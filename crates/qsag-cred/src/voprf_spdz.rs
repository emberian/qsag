//! Threshold oblivious PRF over Shamir sharing with SPDZ authentication:
//! any `t` of `n` servers evaluate, for `2 <= t <= n <= 64`.
//!
//! Any enrolled quorum can evaluate the width-12 Poseidon2 keyed sponge [`plaintext`].
//!
//! # Sharing
//! Server `i` (evaluation point `i + 1`) holds degree-`< t` Shamir shares over
//! Goldilocks of the four key limbs `k`, of a global MAC key `alpha` in the quadratic
//! extension (`|F| > 2^127`), and of `alpha * k`. Any `t` shares are a `t`-of-`t`
//! sharing on those `t` points: an online quorum `S` rescales its `alpha` shares by
//! the Lagrange weights of `S` into additive contributions and runs the dealerless
//! SPDZ preprocessing of `qsag_core::preprocessing` on its own points. No absent
//! server is simulated and the key is never reconstructed.
//!
//! # Enrollment ([`spdz_dkg`], all `n` servers)
//! Every server deals a random key contribution; the sum is the key. The shares are
//! authenticated under `alpha` by `spdz_authenticate_goldilocks_batch_ext2`, which
//! also checks across all `n` servers that values and MACs lie on consistent
//! degree-`< t` polynomials. The public record ([`SpdzPublic`]) commits to every
//! server's share; a restored share file is checked against it.
//!
//! # Evaluation (any `m >= t` servers)
//! 1. [`SpdzSession::begin`]: each server admits and durably burns the counter, then
//!    the quorum establishes fresh oblivious-transfer channels among itself, checks
//!    the stored key shares against their MACs under fresh masks (a corrupted share
//!    aborts here), and generates this session's authenticated tuples: 118 power-7
//!    tuples per item for the S-boxes and 16 Beaver triples per item for client masks.
//!    Each server sends the client its value shares of the mask triples
//!    ([`SpdzGrant`]).
//! 2. [`spdz_blind`]: the client reconstructs each triple `(a, b, c)` and checks
//!    `a * b = c`. A server that shifts `a` must guess `b` (probability `1/p`).
//!    Each input limb is masked twice, with the `a` of two independent triples, and
//!    the two differences `x - a` are published in the request.
//! 3. [`SpdzSession::evaluate`]: the servers form `[x] = [a] + (x - a)` from both
//!    masks and open the difference of the two under a MAC check; it must be zero.
//!    Shifting the client's input therefore needs two independent guesses (`1/p^2`, approximately `2^-128` per shifted limb),
//!    and the opened difference depends only on the shifts, never on `x`. The
//!    permutation runs on authenticated shares; every S-box opens `x + r` for a fresh
//!    tuple. Before anything leaves, all those openings pass one batched MAC check.
//!    Each output limb is then opened twice, masked by two more client masks.
//! 4. [`SpdzClient::finalize`]: all `m` servers must report identical masked outputs
//!    (an honest server reports only MAC-checked values); the two unmaskings of every
//!    limb must agree.
//!
//! # Preprocessing
//! [`SpdzReservoir`] batches preprocessing for a fixed quorum and lends disjoint,
//! single-use sessions. Its exclusive borrow, private vault cursors and absence of
//! clone/serialization prevent issuing the same tuple to two quorums. The legacy
//! [`SpdzSession::begin`] remains a one-shot convenience entry point.
//!
//! Preprocessing generates the full requested batch of `sboxes` power tuples and
//! `triples` Beaver triples in a single dealerless `run_dealerless_pi_pow7_with_alpha`
//! ceremony. The reservoir keeps that ceremony's [`OtMesh`] and the quorum's public
//! interpolation tables, so an online MAC check needs no further base-OT setup. Both
//! belong to the one ordered quorum the reservoir was prepared for; every other
//! quorum, including a reordering or a superset, is refused with [`Error::Context`]
//! and needs a reservoir of its own.
//!
//! A tuple is consumed by advancing a vault cursor before the tuple is read, so no
//! path hands one out twice. A request the session refuses (wrong context, a
//! non-canonical word, two maskings of one limb that disagree) costs that session's
//! reservation and nothing else. A failed authenticated opening discards the whole
//! reservoir: every tuple in it is bound to the same MAC key.
//!
//! [`SpdzSession::into_wire_parties`] completes the in-process offline preprocessing.
//! Each resulting [`SpdzWireParty`] evaluates on its own authenticated mesh endpoint.
//! Independently hosted nodes can start with [`SpdzServer::reserve_wire`] from their
//! own preprocessed shares and use [`SpdzWireParty::serve`] with [`spdz_evaluate_wire`].
//! An abort consumes the reservation. Verification relies on the authenticated roster
//! and enrolled public record.

use alloc::{vec, vec::Vec};
use core::fmt;
use qsag_core::field::goldilocks::{
    Goldilocks, GoldilocksExt2, eval_poly_goldilocks, lagrange_weights_zero_goldilocks,
};
use qsag_core::preprocessing::{
    AuthenticatedPower7Share, GoldilocksBeaverShare, GoldilocksOpeningTables, OtMesh,
    PartyPrivateRng, PreprocessError, PreprocessedPoseidonPartyVault,
    commit_and_open_spdz_goldilocks_batch_quorum_with_mesh, run_dealerless_pi_pow7_with_alpha,
    spdz_authenticate_goldilocks_batch_ext2, spdz_setup_alpha_goldilocks,
};
use qsag_core::sponge::poseidon2::{
    POSEIDON2_HALF_EXTERNAL_ROUNDS, POSEIDON2_INTERNAL_ROUNDS, poseidon2_apply_me,
    poseidon2_apply_mi, poseidon2_const_at,
};
use qsag_core::wipe::{SecretBuffer, SecretWipe, ct_eq_bytes};
use qsag_core::wire_transport::WireTransport;

use qsag_accel::{
    ct::ct_zeroize_bytes,
    goldilocks::GOLDILOCKS_PRIME,
    keccak::{Shake256, cshake256_framed_32 as hash},
    poseidon2::poseidon2_perm12,
};
use qsag_core::wipe::SecretBuffer as Zeroizing;
pub(crate) fn fields(seed: &[u8; 32], domain: &[u8], context: &[u8], n: usize) -> Vec<u64> {
    let mut xof = Shake256::new();
    let key = SecretBuffer(hash(domain, &[seed, context]));
    xof.absorb(&key[..]);
    xof.finalize(0x1f);
    let mut out = Vec::with_capacity(n);
    let mut bytes = SecretBuffer([0u8; 8 * 128]);
    while out.len() < n {
        let count = (n - out.len()).min(128);
        xof.squeeze(&mut bytes[..count * 8]);
        for chunk in bytes[..count * 8].as_chunks::<8>().0 {
            let v = u64::from_le_bytes(*chunk);
            if v < GOLDILOCKS_PRIME {
                out.push(v);
            }
        }
    }
    out
}
pub const MAX_BATCH: usize = 64;
/// Domain limb of the keyed sponge (`"TOPRF1"`), shared by every backend.
pub(crate) const SPONGE_DOMAIN: u64 = 0x544f50524631;
/// Maximum forward step permitted per monotone counter reservation (`counter = u64::MAX` is
/// unconditionally rejected so no single request can exhaust the 64-bit counter space).
pub const MAX_COUNTER_WINDOW: u64 = 64;
/// Default cumulative evaluation item quota per enrolled TOPRF key (`2^20 = 1,048,576` items).
pub const MAX_EVALUATIONS_PER_KEY: u64 = 1 << 20;
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    UnsupportedThreshold,
    Encoding,
    Transport,
    BadDelivery {
        party: usize,
    },
    InconsistentShares,
    Context,
    Counter,
    Quota,
    /// An SPDZ MAC check failed: a share, a MAC or an opened value was altered.
    MacCheck,
    /// Dealerless preprocessing (oblivious transfer, sacrifice or degree check) aborted.
    Preprocessing,
}
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}
impl core::error::Error for Error {}
/// Atomic durable reservation: reject counter <= the stored high-water mark,
/// and enforce the enrolled quota (charged by `items`). Never roll back on abort.
pub trait CounterStore {
    /// Read the durable watermark for this enrolled key and party. Each store
    /// instance must be bound to that same custody identity used by `reserve`.
    /// Read failures must fail closed, never be treated as an empty store.
    fn high_water(&self) -> Result<Option<u64>, Error>;
    fn reserve(
        &mut self,
        key: &[u8; 32],
        party: usize,
        counter: u64,
        items: usize,
    ) -> Result<(), Error>;
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PublicKey {
    commitment: [u8; 32],
}
impl PublicKey {
    /// Import the root obtained from authenticated enrollment, not from an
    /// untrusted evaluation response.
    pub fn from_commitment(commitment: [u8; 32]) -> Self {
        Self { commitment }
    }
    #[cfg(test)]
    pub(crate) fn test_key() -> Self {
        Self {
            commitment: [0; 32],
        }
    }
    pub fn commitment(&self) -> [u8; 32] {
        self.commitment
    }
}
/// Counter admission shared by every backend: reject `u64::MAX` and jumps beyond
/// [`MAX_COUNTER_WINDOW`] before any network round or durable mutation, so one
/// uncorroborated packet cannot exhaust the monotone counter space. The durable
/// watermark is recovered first (also on the first request after a custody
/// reload); local burns are retained even if a faulty store regresses.
pub(crate) fn admit_counter(
    last_counter: &mut Option<u64>,
    store: &dyn CounterStore,
    counter: u64,
) -> Result<(), Error> {
    if counter == u64::MAX {
        return Err(Error::Counter);
    }
    *last_counter = (*last_counter).max(store.high_water()?);
    match *last_counter {
        Some(last) => match counter.checked_sub(last) {
            Some(delta) if (1..=MAX_COUNTER_WINDOW).contains(&delta) => Ok(()),
            _ => Err(Error::Counter),
        },
        None if counter >= MAX_COUNTER_WINDOW => Err(Error::Counter),
        None => Ok(()),
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Context {
    key: [u8; 32],
    session: [u8; 32],
    counter: u64,
    items: usize,
    request: [u8; 32],
}
impl Context {
    pub const fn new(
        key: [u8; 32],
        session: [u8; 32],
        counter: u64,
        items: usize,
        request: [u8; 32],
    ) -> Self {
        Self {
            key,
            session,
            counter,
            items,
            request,
        }
    }
    pub const fn key(&self) -> &[u8; 32] {
        &self.key
    }
    pub const fn session(&self) -> &[u8; 32] {
        &self.session
    }
    pub const fn counter(&self) -> u64 {
        self.counter
    }
    pub const fn items(&self) -> usize {
        self.items
    }
    pub const fn request(&self) -> &[u8; 32] {
        &self.request
    }
    pub(crate) fn digest(&self) -> [u8; 32] {
        hash(
            b"QSAG.TOPRF.REQUEST.CONTEXT.V1",
            &[&self.base_digest(), &self.request],
        )
    }
    pub(crate) fn base_digest(&self) -> [u8; 32] {
        hash(
            b"QSAG.TOPRF.EVAL.V1",
            &[
                &self.key,
                &self.session,
                &self.counter.to_le_bytes(),
                &(self.items as u64).to_le_bytes(),
            ],
        )
    }
}
/// Public binding of one evaluated input inside an [`Evaluation`].
pub(crate) fn input_binding(input: &[u8]) -> [u8; 32] {
    hash(b"QSAG.TOPRF.INPUT.BIND.V1", &[input])
}
pub fn hash_input(input: &[u8]) -> [u64; 4] {
    let seed = Zeroizing(hash(b"QSAG.TOPRF.INPUT.V1", &[input]));
    let values = Zeroizing(fields(&seed, b"QSAG.TOPRF.INPUT.FIELD.V1", b"", 4));
    core::array::from_fn(|i| values[i])
}
/// Reference F, useful for test vectors. Custody never reconstructs this key.
pub fn plaintext(key: &[u64; 4], input: &[u8]) -> [u8; 32] {
    let mut st = Zeroizing([0; 12]);
    let input = Zeroizing(hash_input(input));
    st[..4].copy_from_slice(&input[..]);
    st[4] = 1;
    st[7] = SPONGE_DOMAIN;
    st[8..].copy_from_slice(key);
    poseidon2_perm12(&mut st);
    finish(&st[..4])
}
pub(crate) fn finish(output: &[u64]) -> [u8; 32] {
    let mut bytes = Zeroizing(Vec::with_capacity(output.len() * 8));
    for &v in output {
        bytes.extend_from_slice(&v.to_le_bytes());
    }
    hash(b"QSAG.TOPRF.OUTPUT.V1", &[&bytes[..]])
}
/// Client-side TOPRF outputs. `Debug` names only the public context and the
/// faulty-server evidence; the outputs and receipt tags are wiped on drop.
#[cfg_attr(test, derive(Clone))]
pub struct Evaluation {
    values: Vec<[u8; 32]>,
    pub faulty_servers: Vec<usize>,
    key: [u8; 32],
    input_digests: Vec<[u8; 32]>,
    context: Context,
    receipt_tags: Vec<[u8; 32]>,
}
/// The outputs and receipt tags are secret: equality compares every one of
/// them without data-dependent timing.
impl PartialEq for Evaluation {
    fn eq(&self, other: &Self) -> bool {
        let public = (self.faulty_servers == other.faulty_servers)
            & (self.key == other.key)
            & (self.input_digests == other.input_digests)
            & (self.context == other.context)
            & (self.values.len() == other.values.len())
            & (self.receipt_tags.len() == other.receipt_tags.len());
        let secret = self
            .values
            .iter()
            .zip(&other.values)
            .chain(self.receipt_tags.iter().zip(&other.receipt_tags))
            .fold(true, |acc, (a, b)| acc & qsag_accel::ct::ct_eq_bytes(a, b));
        secret & public
    }
}
impl Eq for Evaluation {}
impl fmt::Debug for Evaluation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Evaluation")
            .field("items", &self.values.len())
            .field("faulty_servers", &self.faulty_servers)
            .field("context", &self.context)
            .field("values", &"<REDACTED>")
            .field("receipt_tags", &"<REDACTED>")
            .finish()
    }
}
impl Drop for Evaluation {
    fn drop(&mut self) {
        for value in self.values.iter_mut().chain(&mut self.receipt_tags) {
            ct_zeroize_bytes(value);
        }
    }
}
/// Issuer-only receipt authentication secret, provisioned independently of the
/// public TOPRF key. Share only with the issuer's authenticated channel adapter.
/// The adapter must authenticate server identities before finalizing outputs.
pub struct IssuanceReceiptKey([u8; 32]);
impl IssuanceReceiptKey {
    /// Import 32 bytes from the issuer's cryptographic key generator or vault.
    pub fn new(secret: [u8; 32]) -> Self {
        Self(secret)
    }
    fn tag(
        &self,
        key_commitment: &[u8; 32],
        context: &Context,
        input: &[u8; 32],
        output: &[u8; 32],
    ) -> [u8; 32] {
        hash(
            b"QSAG.TOPRF.ISSUANCE.RECEIPT.V2",
            &[
                &self.0,
                key_commitment,
                &context.digest(),
                &context.key,
                &context.session,
                &context.counter.to_be_bytes(),
                &(context.items as u64).to_be_bytes(),
                &context.request,
                input,
                output,
            ],
        )
    }
}
impl Drop for IssuanceReceiptKey {
    fn drop(&mut self) {
        ct_zeroize_bytes(&mut self.0);
    }
}
impl Evaluation {
    /// Assemble a client result from a backend's verified outputs.
    pub(crate) fn from_verified(
        values: Vec<[u8; 32]>,
        input_digests: Vec<[u8; 32]>,
        context: Context,
    ) -> Self {
        Self {
            values,
            faulty_servers: Vec::new(),
            key: context.key,
            input_digests,
            context,
            receipt_tags: Vec::new(),
        }
    }
    pub(crate) fn attach_receipts(&mut self, receipt_key: &IssuanceReceiptKey) {
        self.receipt_tags = self
            .input_digests
            .iter()
            .zip(&self.values)
            .map(|(input, output)| receipt_key.tag(&self.key, &self.context, input, output))
            .collect();
    }
    pub fn context(&self) -> &Context {
        &self.context
    }

    /// Authenticate the context, canonical input binding and output before use
    /// as an issuance capability. Plain client finalization is insufficient.
    pub fn authenticated_value_for(
        &self,
        key: &PublicKey,
        input: &[u8],
        receipt_key: &IssuanceReceiptKey,
    ) -> Option<[u8; 32]> {
        if !qsag_accel::ct::ct_eq_bytes(&self.key, &key.commitment)
            || !qsag_accel::ct::ct_eq_bytes(&self.context.key, &key.commitment)
            || self.values.len() != self.input_digests.len()
            || self.receipt_tags.len() != self.input_digests.len()
        {
            return None;
        }
        let digest = input_binding(input);
        let mut found = false;
        let mut matched_output = Zeroizing([0u8; 32]);
        let mut matched_tag = Zeroizing([0u8; 32]);
        for ((cand_digest, cand_out), cand_tag) in self
            .input_digests
            .iter()
            .zip(&self.values)
            .zip(&self.receipt_tags)
        {
            let hit = qsag_accel::ct::ct_eq_bytes(cand_digest, &digest);
            let _ =
                qsag_accel::ct::ct_conditional_assign_bytes(hit, &mut matched_output[..], cand_out);
            let _ =
                qsag_accel::ct::ct_conditional_assign_bytes(hit, &mut matched_tag[..], cand_tag);
            found |= hit;
        }
        if !found {
            return None;
        }
        let expected =
            Zeroizing(receipt_key.tag(&key.commitment, &self.context, &digest, &matched_output));
        if qsag_accel::ct::ct_eq_bytes(&matched_tag[..], &expected[..]) {
            Some(*matched_output)
        } else {
            ct_zeroize_bytes(&mut matched_output[..]);
            None
        }
    }

    /// Authenticate an evaluation capability while additionally pinning the exact
    /// TOPRF [`Context`] (session, counter, item count, and request commitment).
    pub fn authenticated_value_for_context(
        &self,
        key: &PublicKey,
        expected_context: &Context,
        input: &[u8],
        receipt_key: &IssuanceReceiptKey,
    ) -> Option<[u8; 32]> {
        if !qsag_accel::ct::ct_eq_bytes(&self.context.digest(), &expected_context.digest())
            || !qsag_accel::ct::ct_eq_bytes(&self.context.session, &expected_context.session)
            || !qsag_accel::ct::ct_eq_bytes(&self.context.key, &expected_context.key)
            || self.context.counter != expected_context.counter
            || self.context.items != expected_context.items
            || !qsag_accel::ct::ct_eq_bytes(&self.context.request, &expected_context.request)
        {
            return None;
        }
        self.authenticated_value_for(key, input, receipt_key)
    }

    pub fn values(&self) -> &[[u8; 32]] {
        &self.values
    }
    pub fn value_for(&self, key: &PublicKey, input: &[u8]) -> Option<[u8; 32]> {
        if !qsag_accel::ct::ct_eq_bytes(&self.key, &key.commitment)
            || self.values.len() != self.input_digests.len()
        {
            return None;
        }
        let digest = input_binding(input);
        let mut found = false;
        let mut matched_output = Zeroizing([0u8; 32]);
        for (cand_digest, cand_out) in self.input_digests.iter().zip(&self.values) {
            let hit = qsag_accel::ct::ct_eq_bytes(cand_digest, &digest);
            let _ =
                qsag_accel::ct::ct_conditional_assign_bytes(hit, &mut matched_output[..], cand_out);
            found |= hit;
        }
        found.then_some(*matched_output)
    }
}

/// Largest committee. Evaluation points are `1..=n`.
pub const MAX_SPDZ_SERVERS: usize = 64;
/// S-boxes of one width-12 permutation (`2 * 4 * 12 + 22`).
const SBOXES_PER_ITEM: usize = 118;
/// Client mask triples per item: four input and four output limbs, two masks each.
const MASKS_PER_ITEM: usize = 16;
const LANES: usize = 4;
const SERVER_BYTES: usize = 8 + 3 + 32 + 9 + 16 + LANES * 8 + LANES * 16;

fn preprocess_error(error: PreprocessError) -> Error {
    match error {
        PreprocessError::MacCheckFailed { .. } => Error::MacCheck,
        PreprocessError::DegreeCheckFailed { .. } | PreprocessError::ShareCommitMismatch { .. } => {
            Error::InconsistentShares
        }
        _ => Error::Preprocessing,
    }
}

/// Committee shape: privacy threshold `t` and `n` servers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SpdzConfig {
    threshold: usize,
    servers: usize,
}
impl SpdzConfig {
    pub fn new(threshold: usize, servers: usize) -> Result<Self, Error> {
        if threshold < 2 || threshold > servers || servers > MAX_SPDZ_SERVERS {
            return Err(Error::UnsupportedThreshold);
        }
        Ok(Self { threshold, servers })
    }
    pub const fn threshold(&self) -> usize {
        self.threshold
    }
    pub const fn servers(&self) -> usize {
        self.servers
    }
}

/// Public enrollment record. Distribute it over the authenticated enrollment channel.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpdzPublic {
    config: SpdzConfig,
    session: [u8; 32],
    share_digests: Vec<[u8; 32]>,
}
impl SpdzPublic {
    pub const fn config(&self) -> SpdzConfig {
        self.config
    }
    /// The key commitment that [`Context`] and [`Evaluation`] carry.
    pub fn public_key(&self) -> PublicKey {
        let shape = [self.config.threshold as u8, self.config.servers as u8];
        let mut parts: Vec<&[u8]> = vec![&self.session, &shape];
        parts.extend(self.share_digests.iter().map(|d| d.as_slice()));
        PublicKey::from_commitment(hash(b"QSAG.TOPRF.SPDZ.KEY.V1", &parts))
    }
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(42 + 32 * self.share_digests.len());
        out.extend_from_slice(b"QTOPRFP1");
        out.push(self.config.threshold as u8);
        out.push(self.config.servers as u8);
        out.extend_from_slice(&self.session);
        for digest in &self.share_digests {
            out.extend_from_slice(digest);
        }
        out
    }
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        if bytes.len() < 42 || &bytes[..8] != b"QTOPRFP1" {
            return Err(Error::Encoding);
        }
        let config = SpdzConfig::new(bytes[8] as usize, bytes[9] as usize)?;
        if bytes.len() != 42 + 32 * config.servers {
            return Err(Error::Encoding);
        }
        Ok(Self {
            config,
            session: bytes[10..42].try_into().map_err(|_| Error::Encoding)?,
            share_digests: bytes[42..].as_chunks::<32>().0.to_vec(),
        })
    }
}

/// One server's authenticated wire share.
#[derive(Clone, Copy)]
struct Wire {
    val: Goldilocks,
    mac: GoldilocksExt2,
}
impl Wire {
    const ZERO: Self = Self {
        val: Goldilocks::ZERO,
        mac: GoldilocksExt2::ZERO,
    };
    /// A public constant: every Shamir share is the constant itself.
    fn public(value: Goldilocks, alpha: GoldilocksExt2) -> Self {
        Self {
            val: value,
            mac: alpha.mul_base(value),
        }
    }
    fn add(self, rhs: Self) -> Self {
        Self {
            val: self.val + rhs.val,
            mac: self.mac + rhs.mac,
        }
    }
    fn sub(self, rhs: Self) -> Self {
        Self {
            val: self.val - rhs.val,
            mac: self.mac - rhs.mac,
        }
    }
    fn scale(self, k: Goldilocks) -> Self {
        Self {
            val: self.val * k,
            mac: self.mac.mul_base(k),
        }
    }
}
impl SecretWipe for Wire {
    fn secret_wipe(&mut self) {
        self.val.secret_wipe();
        self.mac.secret_wipe();
    }
}

/// One server's long-term custody. Not cloneable; erased on drop.
pub struct SpdzServer {
    party: usize,
    public: SpdzPublic,
    alpha: GoldilocksExt2,
    key: [Wire; LANES],
    last_counter: Option<u64>,
}
impl fmt::Debug for SpdzServer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("SpdzToprfServer(<REDACTED>)")
    }
}
impl Drop for SpdzServer {
    fn drop(&mut self) {
        self.alpha.secret_wipe();
        self.key.secret_wipe();
    }
}

fn share_digest(
    session: &[u8; 32],
    party: usize,
    alpha: GoldilocksExt2,
    key: &[Wire; LANES],
) -> [u8; 32] {
    let mut body = SecretBuffer(Vec::with_capacity(16 + LANES * 24));
    body.extend_from_slice(&alpha.to_be_bytes());
    for wire in key {
        body.extend_from_slice(&wire.val.to_le_bytes());
        body.extend_from_slice(&wire.mac.to_be_bytes());
    }
    hash(
        b"QSAG.TOPRF.SPDZ.SHARE.V1",
        &[session, &[party as u8], &body[..]],
    )
}

impl SpdzServer {
    pub fn party(&self) -> usize {
        self.party
    }
    pub fn public(&self) -> &SpdzPublic {
        &self.public
    }
    pub fn public_key(&self) -> PublicKey {
        self.public.public_key()
    }

    /// This server's shares and local counter. The bytes are secret: store them
    /// encrypted and authenticated, and restore with the same monotone counter store.
    pub fn to_secret_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(SERVER_BYTES);
        out.extend_from_slice(b"QTOPRFS1");
        out.push(self.party as u8);
        out.push(self.public.config.threshold as u8);
        out.push(self.public.config.servers as u8);
        out.extend_from_slice(&self.public_key().commitment());
        out.push(u8::from(self.last_counter.is_some()));
        out.extend_from_slice(&self.last_counter.unwrap_or(0).to_le_bytes());
        out.extend_from_slice(&self.alpha.to_be_bytes());
        for wire in &self.key {
            out.extend_from_slice(&wire.val.to_le_bytes());
        }
        for wire in &self.key {
            out.extend_from_slice(&wire.mac.to_be_bytes());
        }
        out
    }

    /// Restore against the independently pinned enrollment record. The shares must
    /// match the digest that record holds for `expected_party`.
    pub fn from_secret_bytes(
        bytes: &[u8],
        public: &SpdzPublic,
        expected_party: usize,
    ) -> Result<Self, Error> {
        if bytes.len() != SERVER_BYTES || &bytes[..8] != b"QTOPRFS1" {
            return Err(Error::Encoding);
        }
        let party = bytes[8] as usize;
        if party != expected_party
            || party >= public.config.servers
            || bytes[9] as usize != public.config.threshold
            || bytes[10] as usize != public.config.servers
            || !ct_eq_bytes(&bytes[11..43], &public.public_key().commitment())
        {
            return Err(Error::Context);
        }
        let counter = u64::from_le_bytes(bytes[44..52].try_into().map_err(|_| Error::Encoding)?);
        let last_counter = match bytes[43] {
            0 if counter == 0 => None,
            1 if counter != u64::MAX => Some(counter),
            _ => return Err(Error::Encoding),
        };
        let ext = |at: usize| {
            GoldilocksExt2::from_be_bytes_canonical(
                bytes[at..at + 16].try_into().map_err(|_| Error::Encoding)?,
            )
            .map_err(|_| Error::Encoding)
        };
        let alpha = ext(52)?;
        let mut key = SecretBuffer([Wire::ZERO; LANES]);
        for (lane, wire) in key.iter_mut().enumerate() {
            let at = 68 + 8 * lane;
            wire.val = Goldilocks::from_le_bytes_canonical(
                bytes[at..at + 8].try_into().map_err(|_| Error::Encoding)?,
            )
            .map_err(|_| Error::Encoding)?;
            wire.mac = ext(68 + 8 * LANES + 16 * lane)?;
        }
        if !ct_eq_bytes(
            &share_digest(&public.session, party, alpha, &key),
            &public.share_digests[party],
        ) {
            return Err(Error::Context);
        }
        Ok(Self {
            party,
            public: public.clone(),
            alpha,
            key: *key,
            last_counter,
        })
    }
}

fn eval_points(parties: &[usize]) -> Vec<Goldilocks> {
    parties
        .iter()
        .map(|&party| Goldilocks::from_u64_reduced(party as u64 + 1))
        .collect()
}

fn party_rngs(domain: &[u8], context: &[u8; 32], entropy: &[[u8; 32]]) -> Vec<PartyPrivateRng> {
    entropy
        .iter()
        .enumerate()
        .map(|(index, seed)| {
            let derived = SecretBuffer(hash(domain, &[seed, context, &[index as u8]]));
            PartyPrivateRng::from_seed(*derived, domain)
        })
        .collect()
}

/// Dealerless enrollment of all `n` servers. `entropy[i]` is server `i`'s private
/// CSPRNG output; `session` must be fresh for this ceremony.
pub fn spdz_dkg(
    config: SpdzConfig,
    session: [u8; 32],
    entropy: &[[u8; 32]],
) -> Result<Vec<SpdzServer>, Error> {
    let (t, n) = (config.threshold, config.servers);
    if entropy.len() != n {
        return Err(Error::Encoding);
    }
    let sid = hash(
        b"QSAG.TOPRF.SPDZ.DKG.SESSION.V1",
        &[&session, &[t as u8, n as u8]],
    );
    let mut rngs = party_rngs(b"QSAG.TOPRF.SPDZ.DKG.RNG.V1", &sid, entropy);
    let parties: Vec<usize> = (0..n).collect();
    let points = eval_points(&parties);
    let mut mesh = OtMesh::try_establish(sid, &mut rngs).map_err(preprocess_error)?;
    let (alpha_contribs, alpha_shares) =
        spdz_setup_alpha_goldilocks(&sid, t, &points, &mut rngs).map_err(preprocess_error)?;
    let alpha_contribs = SecretBuffer(alpha_contribs);
    let alpha_shares = SecretBuffer(alpha_shares);

    // Every server deals a contribution to each key limb; the key is their sum.
    let mut key_shares = SecretBuffer(vec![vec![Goldilocks::ZERO; LANES]; n]);
    for rng in rngs.iter_mut() {
        for lane in 0..LANES {
            let mut coefficients = SecretBuffer(Vec::with_capacity(t));
            for _ in 0..t {
                coefficients.push(rng.next_goldilocks());
            }
            for (shares, &point) in key_shares.iter_mut().zip(&points) {
                shares[lane] += eval_poly_goldilocks(&coefficients, point);
            }
        }
    }
    let macs = SecretBuffer(
        spdz_authenticate_goldilocks_batch_ext2(
            &sid,
            t,
            &points,
            &mut mesh,
            &alpha_contribs,
            &alpha_shares,
            &key_shares,
            &mut rngs,
        )
        .map_err(preprocess_error)?,
    );

    let mut wires = SecretBuffer(vec![[Wire::ZERO; LANES]; n]);
    for (party, wire) in wires.iter_mut().enumerate() {
        for lane in 0..LANES {
            wire[lane] = Wire {
                val: key_shares[party][lane],
                mac: macs[party][lane],
            };
        }
    }
    let public = SpdzPublic {
        config,
        session,
        share_digests: (0..n)
            .map(|party| share_digest(&session, party, alpha_shares[party], &wires[party]))
            .collect(),
    };
    Ok((0..n)
        .map(|party| SpdzServer {
            party,
            public: public.clone(),
            alpha: alpha_shares[party],
            key: wires[party],
            last_counter: None,
        })
        .collect())
}

fn grant_binding(
    key: &[u8; 32],
    session: &[u8; 32],
    counter: u64,
    items: usize,
    parties: &[usize],
) -> [u8; 32] {
    let quorum: Vec<u8> = parties.iter().map(|&p| p as u8).collect();
    hash(
        b"QSAG.TOPRF.SPDZ.GRANT.V1",
        &[
            key,
            session,
            &counter.to_le_bytes(),
            &(items as u64).to_le_bytes(),
            &quorum,
        ],
    )
}

fn request_digest(binding: &[u8; 32], differences: &[[[u64; 2]; LANES]]) -> [u8; 32] {
    let mut payload = Vec::with_capacity(differences.len() * LANES * 16);
    for item in differences {
        for lane in item {
            for value in lane {
                payload.extend_from_slice(&value.to_le_bytes());
            }
        }
    }
    hash(b"QSAG.TOPRF.SPDZ.REQUEST.V1", &[binding, &payload])
}

/// Index of a client mask triple: `output` selects the pads, `copy` is 0 or 1.
const fn mask_index(item: usize, output: bool, lane: usize, copy: usize) -> usize {
    item * MASKS_PER_ITEM + (output as usize) * 2 * LANES + lane * 2 + copy
}

/// One server's value shares of the session's client mask triples. Private to the
/// client: deliver over that server's authenticated confidential channel.
pub struct SpdzGrant {
    party: usize,
    binding: [u8; 32],
    triples: Vec<[Goldilocks; 3]>,
}
impl SpdzGrant {
    pub fn party(&self) -> usize {
        self.party
    }
}
impl fmt::Debug for SpdzGrant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("SpdzToprfGrant(<REDACTED>)")
    }
}
impl Drop for SpdzGrant {
    fn drop(&mut self) {
        self.triples.secret_wipe();
    }
}

/// The client's public request: identical for every server of the quorum.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpdzRequest {
    context: Context,
    differences: Vec<[[u64; 2]; LANES]>,
}
impl SpdzRequest {
    pub fn context(&self) -> &Context {
        &self.context
    }
}

/// One server's reply: the MAC-checked masked output limbs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpdzOutput {
    party: usize,
    context: Context,
    masked: Vec<[[u64; 2]; LANES]>,
}
impl SpdzOutput {
    pub fn party(&self) -> usize {
        self.party
    }
}

/// Client state between [`spdz_blind`] and [`SpdzClient::finalize`].
pub struct SpdzClient {
    context: Context,
    parties: Vec<usize>,
    input_digests: Vec<[u8; 32]>,
    pads: Vec<[[Goldilocks; 2]; LANES]>,
}
impl fmt::Debug for SpdzClient {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("SpdzToprfClient(<REDACTED>)")
    }
}
impl Drop for SpdzClient {
    fn drop(&mut self) {
        self.pads.secret_wipe();
    }
}

/// Verify the quorum's mask grants and mask `inputs`. `grants` must come from the
/// authenticated channels of at least `t` distinct enrolled servers, all of the
/// session's quorum.
pub fn spdz_blind(
    public: &SpdzPublic,
    inputs: &[&[u8]],
    session: [u8; 32],
    counter: u64,
    grants: &[SpdzGrant],
) -> Result<(SpdzClient, SpdzRequest), Error> {
    let items = inputs.len();
    if items == 0 || items > MAX_BATCH {
        return Err(Error::Quota);
    }
    let parties: Vec<usize> = grants.iter().map(|grant| grant.party).collect();
    if parties.len() < public.config.threshold
        || parties.windows(2).any(|pair| pair[0] >= pair[1])
        || parties.iter().any(|&party| party >= public.config.servers)
    {
        return Err(Error::UnsupportedThreshold);
    }
    let key = public.public_key().commitment();
    let binding = grant_binding(&key, &session, counter, items, &parties);
    if grants.iter().any(|grant| {
        grant.triples.len() != items * MASKS_PER_ITEM || !ct_eq_bytes(&grant.binding, &binding)
    }) {
        return Err(Error::Context);
    }
    let weights =
        lagrange_weights_zero_goldilocks(&eval_points(&parties)).ok_or(Error::Encoding)?;
    let mut masks = SecretBuffer(Vec::with_capacity(items * MASKS_PER_ITEM));
    for index in 0..items * MASKS_PER_ITEM {
        let mut opened = SecretBuffer([Goldilocks::ZERO; 3]);
        for (grant, &weight) in grants.iter().zip(&weights) {
            for (acc, &share) in opened.iter_mut().zip(&grant.triples[index]) {
                *acc += share * weight;
            }
        }
        // With shifts (da, db, dc), acceptance requires
        // da*b + db*a + da*db = dc. For da != 0 this has probability 1/p
        // against an unknown independent honest factor. Input consistency below
        // forces the same shift in both independent masks: 1/p^2 per limb.
        // Honest grants must stay confidential until the corrupt grants are fixed;
        // the authenticated confidential channels in this API are essential.
        if !(opened[0] * opened[1]).ct_eq(opened[2]) {
            return Err(Error::InconsistentShares);
        }
        masks.push(opened[0]);
    }
    let mut differences = Vec::with_capacity(items);
    let mut pads = SecretBuffer(Vec::with_capacity(items));
    for (item, input) in inputs.iter().enumerate() {
        let limbs = SecretBuffer(hash_input(input));
        differences.push(core::array::from_fn(|lane| {
            core::array::from_fn(|copy| {
                (Goldilocks::from_u64_reduced(limbs[lane])
                    - masks[mask_index(item, false, lane, copy)])
                .to_canonical_u64()
            })
        }));
        pads.push(core::array::from_fn(|lane| {
            core::array::from_fn(|copy| masks[mask_index(item, true, lane, copy)])
        }));
    }
    let context = Context::new(
        key,
        session,
        counter,
        items,
        request_digest(&binding, &differences),
    );
    Ok((
        SpdzClient {
            context: context.clone(),
            parties,
            input_digests: inputs.iter().map(|input| input_binding(input)).collect(),
            pads: pads.into_inner(),
        },
        SpdzRequest {
            context,
            differences,
        },
    ))
}

impl SpdzClient {
    /// `outputs` must hold one reply from every server of the quorum, each received
    /// on that server's authenticated channel.
    pub fn finalize(self, outputs: &[SpdzOutput]) -> Result<Evaluation, Error> {
        let reported: Vec<usize> = outputs.iter().map(|output| output.party).collect();
        if reported != self.parties {
            return Err(Error::UnsupportedThreshold);
        }
        let first = &outputs[0];
        if first.masked.len() != self.context.items()
            || outputs
                .iter()
                .any(|output| output.context != self.context || output.masked != first.masked)
        {
            return Err(Error::InconsistentShares);
        }
        let mut values = SecretBuffer(Vec::with_capacity(self.context.items()));
        for (masked, pads) in first.masked.iter().zip(&self.pads) {
            let mut limbs = SecretBuffer([0u64; LANES]);
            for lane in 0..LANES {
                let open = |copy: usize| {
                    Goldilocks::from_canonical(masked[lane][copy])
                        .map(|value| value - pads[lane][copy])
                        .map_err(|_| Error::Encoding)
                };
                let value = open(0)?;
                if !value.ct_eq(open(1)?) {
                    return Err(Error::InconsistentShares);
                }
                limbs[lane] = value.to_canonical_u64();
            }
            values.push(finish(&limbs[..]));
        }
        Ok(Evaluation::from_verified(
            values.into_inner(),
            self.input_digests.clone(),
            self.context.clone(),
        ))
    }

    /// Issuer channel adapter entry point; bind the verified outputs to the issuer receipt key.
    pub fn finalize_for_issuance(
        self,
        outputs: &[SpdzOutput],
        receipt_key: &IssuanceReceiptKey,
    ) -> Result<Evaluation, Error> {
        let mut evaluation = self.finalize(outputs)?;
        evaluation.attach_receipts(receipt_key);
        Ok(evaluation)
    }
}

/// Openings made during the circuit, awaiting the MAC check that precedes release.
struct Pending {
    shares: Vec<Vec<Goldilocks>>,
    macs: Vec<Vec<GoldilocksExt2>>,
}
impl Pending {
    fn with_capacity(quorum: usize, capacity: usize) -> Self {
        Self {
            shares: (0..quorum).map(|_| Vec::with_capacity(capacity)).collect(),
            macs: (0..quorum).map(|_| Vec::with_capacity(capacity)).collect(),
        }
    }
    fn record(&mut self, wires: &[Vec<Wire>]) {
        for ((shares, macs), wires) in self.shares.iter_mut().zip(&mut self.macs).zip(wires) {
            qsag_asm::wipe::secret_vec_reserve(shares, wires.len());
            qsag_asm::wipe::secret_vec_reserve(macs, wires.len());
            shares.extend(wires.iter().map(|wire| wire.val));
            macs.extend(wires.iter().map(|wire| wire.mac));
        }
    }
}
impl Drop for Pending {
    fn drop(&mut self) {
        self.shares.secret_wipe();
        self.macs.secret_wipe();
    }
}

/// The canonical linear layers are `F_p`-linear, so they act on the value and on each
/// extension coordinate of the MAC separately.
fn linear(state: &mut [Wire; 12], external: bool) {
    let mut planes = SecretBuffer([
        core::array::from_fn::<_, 12, _>(|lane| state[lane].val),
        core::array::from_fn::<_, 12, _>(|lane| state[lane].mac.c0),
        core::array::from_fn::<_, 12, _>(|lane| state[lane].mac.c1),
    ]);
    for plane in planes.iter_mut() {
        if external {
            poseidon2_apply_me(plane);
        } else {
            poseidon2_apply_mi(plane);
        }
    }
    for (lane, wire) in state.iter_mut().enumerate() {
        *wire = Wire {
            val: planes[0][lane],
            mac: GoldilocksExt2::new(planes[1][lane], planes[2][lane]),
        };
    }
}

/// The quorum's tuples: `chunks[c][i]` is quorum member `i`'s vault of dealerless run
/// `c`. Every vault burns a range by advancing its cursor before exposing it.
struct TuplePool {
    chunks: Vec<Vec<PreprocessedPoseidonPartyVault>>,
    /// First chunk that may still hold power tuples, and likewise triples.
    pow7_front: usize,
    beaver_front: usize,
}
type Vault = PreprocessedPoseidonPartyVault;

impl TuplePool {
    fn new() -> Self {
        Self {
            chunks: Vec::new(),
            pow7_front: 0,
            beaver_front: 0,
        }
    }

    /// What every member can still supply.
    fn remaining(&self, front: usize, of: fn(&Vault) -> usize) -> usize {
        self.chunks[front.min(self.chunks.len())..]
            .iter()
            .map(|chunk| chunk.iter().map(of).min().unwrap_or(0))
            .sum()
    }
    fn remaining_pow7(&self) -> usize {
        self.remaining(self.pow7_front, Vault::remaining_pow7)
    }
    fn remaining_beaver(&self) -> usize {
        self.remaining(self.beaver_front, Vault::remaining_beaver)
    }

    /// Burn the next `count` tuples of every member; `out[i][k]` is member `i`'s share
    /// of the `k`-th. A shortfall burns what there was and fails.
    fn take<T>(
        chunks: &mut [Vec<Vault>],
        front: &mut usize,
        count: usize,
        remaining: fn(&Vault) -> usize,
        reserve: fn(&mut Vault, usize) -> Result<Vec<T>, PreprocessError>,
        transfer: fn(&mut T) -> T,
    ) -> Result<Vec<Vec<T>>, Error> {
        let members = chunks.first().map_or(0, Vec::len);
        let mut out: Vec<Vec<T>> = (0..members).map(|_| Vec::with_capacity(count)).collect();
        let mut need = count;
        let start = (*front).min(chunks.len());
        for (index, chunk) in chunks.iter_mut().enumerate().skip(start) {
            if need == 0 {
                break;
            }
            let take = need.min(chunk.iter().map(remaining).min().unwrap_or(0));
            if take == 0 {
                *front = index + 1;
                continue;
            }
            for (shares, vault) in out.iter_mut().zip(chunk.iter_mut()) {
                let mut reserved = reserve(vault, take).map_err(preprocess_error)?;
                shares.extend(reserved.iter_mut().map(transfer));
            }
            need -= take;
        }
        if need == 0 {
            Ok(out)
        } else {
            Err(Error::Preprocessing)
        }
    }
    fn take_pow7(&mut self, count: usize) -> Result<Vec<Vec<AuthenticatedPower7Share>>, Error> {
        Self::take(
            &mut self.chunks,
            &mut self.pow7_front,
            count,
            Vault::remaining_pow7,
            Vault::reserve_pow7,
            AuthenticatedPower7Share::take_and_wipe,
        )
    }
    fn take_beaver(&mut self, count: usize) -> Result<Vec<Vec<GoldilocksBeaverShare>>, Error> {
        Self::take(
            &mut self.chunks,
            &mut self.beaver_front,
            count,
            Vault::remaining_beaver,
            Vault::reserve_beaver,
            GoldilocksBeaverShare::take_and_wipe,
        )
    }

    fn poison(&mut self) {
        for vault in self.chunks.iter_mut().flatten() {
            vault.poison_and_wipe();
        }
    }
}

/// Why an evaluation stopped.
enum Refusal {
    /// The request was not acceptable. Every opening made so far passed its MAC check,
    /// so only this session's reservation is spent.
    Request(Error),
    /// An opening or its MAC check failed: a quorum member deviated.
    Quorum(Error),
}
impl From<Error> for Refusal {
    fn from(error: Error) -> Self {
        Self::Quorum(error)
    }
}
impl Refusal {
    fn into_error(self) -> Error {
        match self {
            Self::Request(error) | Self::Quorum(error) => error,
        }
    }
}

/// An online evaluation among one quorum, between tuple generation and release.
pub struct SpdzSession {
    threshold: usize,
    sid: [u8; 32],
    binding: [u8; 32],
    key_commitment: [u8; 32],
    session: [u8; 32],
    counter: u64,
    items: usize,
    parties: Vec<usize>,
    points: Vec<Goldilocks>,
    opening_tables: GoldilocksOpeningTables,
    rngs: Vec<PartyPrivateRng>,
    /// The quorum's degree-`< t` shares of the MAC key.
    alpha: Vec<GoldilocksExt2>,
    mesh: Option<OtMesh>,
    pool: TuplePool,
    key: Vec<[Wire; LANES]>,
    masks: Vec<Vec<Wire>>,
}
impl fmt::Debug for SpdzSession {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("SpdzToprfSession(<REDACTED>)")
    }
}
impl Drop for SpdzSession {
    fn drop(&mut self) {
        self.mesh = None;
        self.alpha.secret_wipe();
        self.key.secret_wipe();
        self.masks.secret_wipe();
    }
}

impl SpdzSession {
    fn alphas(&self) -> SecretBuffer<Vec<GoldilocksExt2>> {
        SecretBuffer(self.alpha.clone())
    }

    /// Open a batch of wires under the SPDZ MAC check, reusing the reservoir's monotone OT mesh.
    fn checked_open(
        &mut self,
        phase: &'static str,
        shares: &[Vec<Goldilocks>],
        macs: &[Vec<GoldilocksExt2>],
    ) -> Result<Vec<Goldilocks>, Error> {
        let mesh = self.mesh.as_mut().ok_or(Error::MacCheck)?;
        commit_and_open_spdz_goldilocks_batch_quorum_with_mesh(
            &self.sid,
            phase,
            self.threshold,
            &self.points,
            shares,
            macs,
            &self.alpha,
            &mut self.rngs,
            Some(mesh),
        )
        .map_err(preprocess_error)
    }

    fn checked_open_wires(
        &mut self,
        phase: &'static str,
        wires: &[Vec<Wire>],
    ) -> Result<Vec<Goldilocks>, Error> {
        let mut pending = Pending::with_capacity(wires.len(), wires.first().map_or(0, Vec::len));
        pending.record(wires);
        self.checked_open(phase, &pending.shares, &pending.macs)
    }

    /// Start an evaluation among `quorum` (ascending party order, at least `t`
    /// servers of one enrollment). `stores[i]` and `entropy[i]` belong to
    /// `quorum[i]`. Every server admits and durably burns `counter` before any
    /// key-dependent step; an aborted session never returns it.
    pub fn begin(
        quorum: &mut [&mut SpdzServer],
        stores: &mut [&mut dyn CounterStore],
        session: [u8; 32],
        counter: u64,
        items: usize,
        entropy: &[[u8; 32]],
    ) -> Result<(Self, Vec<SpdzGrant>), Error> {
        let sboxes = SBOXES_PER_ITEM.checked_mul(items).ok_or(Error::Quota)?;
        Self::begin_with_sboxes(quorum, stores, session, counter, items, entropy, sboxes)
    }

    /// Internal budget override used by malformed-request tests.
    fn begin_with_sboxes(
        quorum: &mut [&mut SpdzServer],
        stores: &mut [&mut dyn CounterStore],
        session: [u8; 32],
        counter: u64,
        items: usize,
        entropy: &[[u8; 32]],
        sboxes: usize,
    ) -> Result<(Self, Vec<SpdzGrant>), Error> {
        // Reserve before preprocessing as well: even failed setup burns the attempt.
        reserve_counters(quorum, stores, counter, items)?;
        let mut pool = SpdzReservoir::prepare_with_sboxes(
            quorum,
            session,
            Some(counter),
            items,
            1,
            entropy,
            sboxes,
        )?;
        let grants = pool.start_reserved(quorum, session, counter, items, sboxes)?;
        Ok((pool.state, grants))
    }

    /// One layer of `x -> x^7` in a single opening round: open `y = x + r` for a
    /// fresh tuple and expand `(y - r)^7` on the authenticated powers of `r`.
    fn sbox(
        &mut self,
        inputs: &[Vec<Wire>],
        pending: &mut Pending,
    ) -> Result<Vec<Vec<Wire>>, Error> {
        let m = inputs.len();
        let count = inputs[0].len();
        let alphas = &self.alpha;
        let tuples = self.pool.take_pow7(count)?;
        let mut masked = SecretBuffer(vec![Vec::with_capacity(count); m]);
        for ((reserved, wires), out) in tuples.iter().zip(inputs).zip(masked.iter_mut()) {
            for (wire, tuple) in wires.iter().zip(reserved) {
                out.push(wire.add(Wire {
                    val: tuple.r_pows[0],
                    mac: tuple.r_macs[0],
                }));
            }
        }
        pending.record(&masked);
        let mut shares = SecretBuffer(vec![Goldilocks::ZERO; m]);
        let mut out = SecretBuffer(vec![Vec::with_capacity(count); m]);
        for gate in 0..count {
            for (share, wires) in shares.iter_mut().zip(masked.iter()) {
                *share = wires[gate].val;
            }
            let y = self
                .opening_tables
                .open(&shares, "toprf_spdz_sbox")
                .map_err(preprocess_error)?;
            for (party, wires) in out.iter_mut().enumerate() {
                wires.push(expand_power7(y, &tuples[party][gate], alphas[party]));
            }
        }
        Ok(out.into_inner())
    }

    fn permute(
        &mut self,
        states: &mut [Vec<[Wire; 12]>],
        pending: &mut Pending,
    ) -> Result<(), Error> {
        for state in states.iter_mut().flatten() {
            linear(state, true);
        }
        let rounds = [
            (0, POSEIDON2_HALF_EXTERNAL_ROUNDS),
            (1, POSEIDON2_INTERNAL_ROUNDS),
            (2, POSEIDON2_HALF_EXTERNAL_ROUNDS),
        ];
        for (tag, count) in rounds {
            let width = if tag == 1 { 1 } else { 12 };
            for round in 0..count {
                let inputs: SecretBuffer<Vec<Vec<Wire>>> = SecretBuffer(
                    states
                        .iter()
                        .zip(self.alpha.iter())
                        .map(|(party, &alpha)| {
                            party
                                .iter()
                                .flat_map(|state| {
                                    (0..width).map(move |lane| {
                                        state[lane].add(Wire::public(
                                            poseidon2_const_at(tag, round, lane as u64),
                                            alpha,
                                        ))
                                    })
                                })
                                .collect()
                        })
                        .collect(),
                );
                let outputs = SecretBuffer(self.sbox(&inputs, pending)?);
                for (party, wires) in states.iter_mut().zip(outputs.iter()) {
                    for (state, chunk) in party.iter_mut().zip(wires.chunks_exact(width)) {
                        state[..width].copy_from_slice(chunk);
                        linear(state, tag != 1);
                    }
                }
            }
        }
        Ok(())
    }

    /// Whether `request` is the one this session's grants were issued for.
    fn check_request(&self, request: &SpdzRequest) -> Result<(), Error> {
        let context = &request.context;
        if ct_eq_bytes(context.key(), &self.key_commitment)
            && context.session() == &self.session
            && context.counter() == self.counter
            && context.items() == self.items
            && request.differences.len() == self.items
            && ct_eq_bytes(
                context.request(),
                &request_digest(&self.binding, &request.differences),
            )
        {
            Ok(())
        } else {
            Err(Error::Context)
        }
    }

    /// Evaluate the client's request and return every server's reply. Nothing is
    /// returned unless every opening of the session passed its MAC check.
    pub fn evaluate(mut self, request: &SpdzRequest) -> Result<Vec<SpdzOutput>, Error> {
        self.evaluate_inner(request).map_err(Refusal::into_error)
    }

    fn evaluate_inner(&mut self, request: &SpdzRequest) -> Result<Vec<SpdzOutput>, Refusal> {
        self.check_request(request).map_err(Refusal::Request)?;
        let context = &request.context;
        let m = self.parties.len();
        let alphas = self.alphas();
        let mut differences = Vec::with_capacity(self.items);
        for item in &request.differences {
            let mut lanes = [[Goldilocks::ZERO; 2]; LANES];
            for (lane, pair) in lanes.iter_mut().zip(item) {
                for (value, &raw) in lane.iter_mut().zip(pair) {
                    *value = Goldilocks::from_canonical(raw)
                        .map_err(|_| Refusal::Request(Error::Encoding))?;
                }
            }
            differences.push(lanes);
        }

        // Both maskings of every input limb must describe the same value.
        let masks = SecretBuffer(core::mem::take(&mut self.masks));
        let input = |party: usize, item: usize, lane: usize, copy: usize| {
            masks[party][mask_index(item, false, lane, copy)]
                .add(Wire::public(differences[item][lane][copy], alphas[party]))
        };
        let bound: SecretBuffer<Vec<Vec<Wire>>> = SecretBuffer(
            (0..m)
                .map(|party| {
                    (0..self.items)
                        .flat_map(|item| (0..LANES).map(move |lane| (item, lane)))
                        .map(|(item, lane)| {
                            input(party, item, lane, 0).sub(input(party, item, lane, 1))
                        })
                        .collect()
                })
                .collect(),
        );
        // The opening is MAC-checked, so a nonzero difference is the request's own: it
        // depends on the two published differences and on nothing secret.
        let opened = self.checked_open_wires("toprf_spdz_input_bind", &bound)?;
        if opened.iter().any(|value| *value != Goldilocks::ZERO) {
            return Err(Refusal::Request(Error::InconsistentShares));
        }

        let mut states: SecretBuffer<Vec<Vec<[Wire; 12]>>> = SecretBuffer(
            (0..m)
                .map(|party| {
                    (0..self.items)
                        .map(|item| {
                            let mut state = [Wire::ZERO; 12];
                            for lane in 0..LANES {
                                state[lane] = input(party, item, lane, 0);
                                state[8 + lane] = self.key[party][lane];
                            }
                            state[4] = Wire::public(Goldilocks::ONE, alphas[party]);
                            state[7] = Wire::public(
                                Goldilocks::from_u64_reduced(crate::voprf::SPONGE_DOMAIN),
                                alphas[party],
                            );
                            state
                        })
                        .collect()
                })
                .collect(),
        );
        let mut pending = Pending::with_capacity(m, self.items * SBOXES_PER_ITEM);
        self.permute(&mut states, &mut pending)?;
        // Every S-box opening is authenticated before any output share is opened.
        let shares = SecretBuffer(core::mem::take(&mut pending.shares));
        let macs = SecretBuffer(core::mem::take(&mut pending.macs));
        drop(SecretBuffer(self.checked_open(
            "toprf_spdz_circuit",
            &shares,
            &macs,
        )?));

        let outputs: SecretBuffer<Vec<Vec<Wire>>> = SecretBuffer(
            (0..m)
                .map(|party| {
                    (0..self.items)
                        .flat_map(|item| {
                            (0..LANES)
                                .flat_map(move |lane| (0..2).map(move |copy| (item, lane, copy)))
                        })
                        .map(|(item, lane, copy)| {
                            states[party][item][lane]
                                .add(masks[party][mask_index(item, true, lane, copy)])
                        })
                        .collect()
                })
                .collect(),
        );
        let opened = self.checked_open_wires("toprf_spdz_output", &outputs)?;
        let masked: Vec<[[u64; 2]; LANES]> = opened
            .chunks_exact(2 * LANES)
            .map(|item| {
                core::array::from_fn(|lane| {
                    core::array::from_fn(|copy| item[2 * lane + copy].to_canonical_u64())
                })
            })
            .collect();
        Ok(self
            .parties
            .iter()
            .map(|&party| SpdzOutput {
                party,
                context: context.clone(),
                masked: masked.clone(),
            })
            .collect())
    }
}

/// A single custodian's one-use reservation for a wire evaluation. Preprocessing
/// and durable counter reservation precede distribution of these private records.
pub struct SpdzWireParty {
    position: usize,
    parties: Vec<usize>,
    context: Context,
    binding: [u8; 32],
    tables: GoldilocksOpeningTables,
    alpha: SecretBuffer<GoldilocksExt2>,
    key: SecretBuffer<[Wire; LANES]>,
    masks: SecretBuffer<Vec<Wire>>,
    powers: Vec<AuthenticatedPower7Share>,
    blinds: SecretBuffer<Vec<[GoldilocksExt2; 3]>>,
    rng: PartyPrivateRng,
}

/// Public parameters agreed by the client and the selected, ascending server roster.
pub struct SpdzWireRound<'a> {
    pub parties: &'a [usize],
    pub session: [u8; 32],
    pub counter: u64,
    pub items: usize,
}

impl SpdzWireRound<'_> {
    fn validate(&self, public: &SpdzPublic, party: usize) -> Result<usize, Error> {
        let parties = self.parties;
        let shape = public.config;
        if parties.len() < shape.threshold
            || parties.windows(2).any(|p| p[0] >= p[1])
            || parties.iter().any(|&p| p >= shape.servers)
        {
            return Err(Error::UnsupportedThreshold);
        }
        if self.items == 0 || self.items > MAX_BATCH {
            return Err(Error::Quota);
        }
        parties.binary_search(&party).map_err(|_| Error::Context)
    }
}

fn take_wire_blinds(
    vault: &mut PreprocessedPoseidonPartyVault,
) -> Result<SecretBuffer<Vec<[GoldilocksExt2; 3]>>, Error> {
    let r = SecretBuffer(vault.mac_alpha_share);
    let u = GoldilocksExt2::new(Goldilocks::ZERO, Goldilocks::ONE);
    Ok(SecretBuffer(
        vault
            .reserve_beaver(3)
            .map_err(preprocess_error)?
            .iter()
            .map(|q| [*r, GoldilocksExt2::new(q.a, q.b), q.a_mac + u * q.b_mac])
            .collect(),
    ))
}

impl SpdzServer {
    /// Start a node using only its enrolled share, local counter store, and its own
    /// two sacrificed preprocessing vaults for this roster. The circuit vault uses
    /// the enrolled MAC key and contains 118 power tuples and 16 client triples per
    /// item. The blinding vault uses a fresh independent MAC key and three triples.
    /// Both vaults are consumed, including on refusal.
    pub fn reserve_wire(
        &mut self,
        round: &SpdzWireRound<'_>,
        store: &mut dyn CounterStore,
        mut circuit: PreprocessedPoseidonPartyVault,
        mut blinding: PreprocessedPoseidonPartyVault,
        rng: PartyPrivateRng,
    ) -> Result<(SpdzWireParty, SpdzGrant), Error> {
        let parties = round.parties;
        let shape = self.public.config;
        let position = round.validate(&self.public, self.party)?;
        let points = eval_points(parties);
        if [&circuit, &blinding]
            .iter()
            .any(|v| v.party_id != position || v.eval_point != points[position])
            || !circuit.mac_alpha_share.ct_eq(self.alpha)
            || blinding.mac_alpha_share.ct_eq(self.alpha)
        {
            return Err(Error::Preprocessing);
        }
        let key = self.public_key().commitment();
        self.burn_wire_counter(round, store)?;
        let binding = grant_binding(&key, &round.session, round.counter, round.items, parties);
        let mut powers = circuit
            .reserve_pow7(round.items * SBOXES_PER_ITEM)
            .map_err(preprocess_error)?;
        powers.reverse();
        let triples = circuit
            .reserve_beaver(round.items * MASKS_PER_ITEM)
            .map_err(preprocess_error)?;
        let grant = SpdzGrant {
            party: self.party,
            binding,
            triples: triples.iter().map(|q| [q.a, q.b, q.c]).collect(),
        };
        let masks = SecretBuffer(
            triples
                .iter()
                .map(|t| Wire {
                    val: t.a,
                    mac: t.a_mac,
                })
                .collect(),
        );
        let party = SpdzWireParty {
            position,
            parties: parties.to_vec(),
            context: Context::new(key, round.session, round.counter, round.items, [0; 32]),
            binding,
            tables: GoldilocksOpeningTables::new(shape.threshold, &points)
                .map_err(preprocess_error)?,
            alpha: SecretBuffer(self.alpha),
            key: SecretBuffer(self.key),
            masks,
            powers,
            blinds: take_wire_blinds(&mut blinding)?,
            rng,
        };
        Ok((party, grant))
    }
}

impl SpdzSession {
    /// Finish private preprocessing and move one independent online state to
    /// each selected custodian, in the grant roster's order.
    pub fn into_wire_parties(mut self) -> Result<Vec<SpdzWireParty>, Error> {
        // The blinding multiplier is a fresh independent extension-field key. A
        // sacrificed triple supplies two random base coordinates and their MACs
        // under this key, hence a sharing of A and of R*A for A=a+u*b.
        let mut vaults = qsag_core::preprocessing::run_dealerless_pi_pow7(
            hash(b"QSAG.TOPRF.WIRE.BLINDS.V1", &[&self.sid]),
            self.threshold,
            &self.points,
            0,
            3,
            0,
            self.mesh.as_mut().ok_or(Error::Preprocessing)?,
            &mut self.rngs,
        )
        .map_err(preprocess_error)?;
        let tuples = self.pool.take_pow7(self.items * SBOXES_PER_ITEM)?;
        let mut parties = Vec::with_capacity(self.parties.len());
        for (position, ((vault, mut powers), rng)) in vaults
            .iter_mut()
            .zip(tuples)
            .zip(core::mem::take(&mut self.rngs))
            .enumerate()
        {
            powers.reverse();
            parties.push(SpdzWireParty {
                position,
                parties: self.parties.clone(),
                context: Context::new(
                    self.key_commitment,
                    self.session,
                    self.counter,
                    self.items,
                    [0; 32],
                ),
                binding: self.binding,
                tables: GoldilocksOpeningTables::new(self.threshold, &self.points)
                    .map_err(preprocess_error)?,
                alpha: SecretBuffer(self.alpha[position]),
                key: SecretBuffer(self.key[position]),
                masks: SecretBuffer(core::mem::take(&mut self.masks[position])),
                powers,
                blinds: take_wire_blinds(vault)?,
                rng,
            });
        }
        Ok(parties)
    }
}

const PREPROCESS_FRAME: u32 = 0x54505001;

impl SpdzWireParty {
    /// Move just this party's one-use preprocessing and grant to its enrolled
    /// host over a dedicated confidential authenticated link. Its long-term
    /// key and MAC-key shares are supplied by the destination's own vault.
    pub fn dispatch(self, grant: SpdzGrant, link: &mut impl WireTransport) -> Result<(), Error> {
        if link.party() != 0
            || link.parties() != 2
            || self.parties.get(self.position) != Some(&grant.party)
            || self.binding != grant.binding
            || self.masks.len() != grant.triples.len()
        {
            return Err(Error::Context);
        }
        let header = hash(
            b"QSAG.TOPRF.WIRE.PREPROCESS.V1",
            &[&self.binding, &[grant.party as u8]],
        );
        let words = self.masks.len() * 5 + self.powers.len() * 21 + self.blinds.len() * 6;
        let mut packet = SecretBuffer(Vec::with_capacity(32 + 8 * words));
        packet.extend_from_slice(&header);
        for (q, m) in grant.triples.iter().zip(self.masks.iter()) {
            if !q[0].ct_eq(m.val) {
                return Err(Error::Context);
            }
            for v in q {
                packet.extend_from_slice(&v.to_be_bytes());
            }
            packet.extend_from_slice(&m.mac.to_be_bytes());
        }
        for p in &self.powers {
            for x in &p.r_pows {
                packet.extend_from_slice(&x.to_be_bytes());
            }
            for x in &p.r_macs {
                packet.extend_from_slice(&x.to_be_bytes());
            }
        }
        for blind in self.blinds.iter().flatten() {
            packet.extend_from_slice(&blind.to_be_bytes());
        }
        link.send_frame(1, PREPROCESS_FRAME, &packet)
            .map_err(|_| Error::Transport)
    }
}

impl SpdzServer {
    /// Receive a one-use batch from the pinned offline preprocessing service,
    /// and reserve its counter in this node's own durable store before returning
    /// the grant. The provider maintains its separate preprocessing reservation.
    pub fn receive_wire(
        &mut self,
        round: &SpdzWireRound<'_>,
        store: &mut dyn CounterStore,
        link: &mut impl WireTransport,
        rng: PartyPrivateRng,
    ) -> Result<(SpdzWireParty, SpdzGrant), Error> {
        let position = round.validate(&self.public, self.party)?;
        if link.party() != 1 || link.parties() != 2 {
            return Err(Error::Context);
        }
        let key = self.public_key().commitment();
        let binding = grant_binding(
            &key,
            &round.session,
            round.counter,
            round.items,
            round.parties,
        );
        let header = hash(
            b"QSAG.TOPRF.WIRE.PREPROCESS.V1",
            &[&binding, &[self.party as u8]],
        );
        let packet = SecretBuffer(
            link.recv_frame(0, PREPROCESS_FRAME)
                .map_err(|_| Error::Transport)?,
        );
        let nm = MASKS_PER_ITEM * round.items;
        let np = SBOXES_PER_ITEM * round.items;
        if !packet.starts_with(&header) || packet.len() != 32 + 8 * (nm * 5 + np * 21 + 18) {
            return Err(Error::Encoding);
        }
        let mut rest = &packet[32..];
        fn take<const N: usize>(rest: &mut &[u8]) -> Result<[u8; N], Error> {
            let (word, tail) = rest.split_first_chunk::<N>().ok_or(Error::Encoding)?;
            *rest = tail;
            Ok(*word)
        }
        fn base(rest: &mut &[u8]) -> Result<Goldilocks, Error> {
            Goldilocks::from_be_bytes_canonical(take(rest)?).map_err(|_| Error::Encoding)
        }
        fn ext(rest: &mut &[u8]) -> Result<GoldilocksExt2, Error> {
            GoldilocksExt2::from_be_bytes_canonical(take(rest)?).map_err(|_| Error::Encoding)
        }
        let mut triples = SecretBuffer(Vec::with_capacity(nm));
        let mut masks = SecretBuffer(Vec::with_capacity(nm));
        for _ in 0..nm {
            let a = base(&mut rest)?;
            triples.push([a, base(&mut rest)?, base(&mut rest)?]);
            masks.push(Wire {
                val: a,
                mac: ext(&mut rest)?,
            });
        }
        let mut powers = Vec::with_capacity(np);
        for _ in 0..np {
            let mut power = AuthenticatedPower7Share {
                r_pows: [Goldilocks::ZERO; 7],
                r_macs: [GoldilocksExt2::ZERO; 7],
                r1_mac: GoldilocksExt2::ZERO,
            };
            for x in &mut power.r_pows {
                *x = base(&mut rest)?;
            }
            for x in &mut power.r_macs {
                *x = ext(&mut rest)?;
            }
            power.r1_mac = power.r_macs[0];
            powers.push(power);
        }
        let mut blinds = SecretBuffer(Vec::with_capacity(3));
        for _ in 0..3 {
            blinds.push([ext(&mut rest)?, ext(&mut rest)?, ext(&mut rest)?]);
        }
        self.burn_wire_counter(round, store)?;
        Ok((
            SpdzWireParty {
                position,
                parties: round.parties.to_vec(),
                context: Context::new(key, round.session, round.counter, round.items, [0; 32]),
                binding,
                tables: GoldilocksOpeningTables::new(
                    self.public.config.threshold,
                    &eval_points(round.parties),
                )
                .map_err(preprocess_error)?,
                alpha: SecretBuffer(self.alpha),
                key: SecretBuffer(self.key),
                masks,
                powers,
                blinds,
                rng,
            },
            SpdzGrant {
                party: self.party,
                binding,
                triples: triples.into_inner(),
            },
        ))
    }

    fn burn_wire_counter(
        &mut self,
        round: &SpdzWireRound<'_>,
        store: &mut dyn CounterStore,
    ) -> Result<(), Error> {
        admit_counter(&mut self.last_counter, store, round.counter)?;
        self.last_counter = Some(round.counter);
        store.reserve(
            &self.public_key().commitment(),
            self.party,
            round.counter,
            round.items,
        )
    }
}

// The client is endpoint zero on each confidential two-party link. Each link's
// authenticated peer is independently associated with its enrolled server ID.
const GRANT_FRAME: u32 = 0x54504701;
const REQUEST_FRAME: u32 = 0x54504702;
const OUTPUT_FRAME: u32 = 0x54504703;

fn field_frame(binding: &[u8; 32], words: impl IntoIterator<Item = u64>) -> SecretBuffer<Vec<u8>> {
    let mut bytes = SecretBuffer(binding.to_vec());
    for word in words {
        qsag_asm::wipe::secret_vec_extend_from_slice(&mut bytes, &word.to_le_bytes());
    }
    bytes
}

fn field_rows<const N: usize>(
    frame: &[u8],
    binding: &[u8; 32],
    count: usize,
) -> Result<SecretBuffer<Vec<[u64; N]>>, Error> {
    if !frame.starts_with(binding) || frame.len() != 32 + count * N * 8 {
        return Err(Error::Encoding);
    }
    let mut words = frame[32..].as_chunks::<8>().0.iter();
    let mut rows = SecretBuffer(Vec::with_capacity(count));
    for _ in 0..count {
        let mut row = SecretBuffer([0; N]);
        for value in row.iter_mut() {
            let raw = u64::from_le_bytes(*words.next().ok_or(Error::Encoding)?);
            *value = Goldilocks::from_canonical(raw)
                .map_err(|_| Error::Encoding)?
                .to_canonical_u64();
        }
        rows.push(*row);
    }
    Ok(rows)
}

impl SpdzWireParty {
    /// Deliver this server's grant to the client, accept its blinded request,
    /// run the authenticated server rounds and return only the checked reply.
    pub fn serve(
        self,
        grant: SpdzGrant,
        peers: &mut impl WireTransport,
        client: &mut impl WireTransport,
    ) -> Result<(), Error> {
        if client.party() != 1
            || client.parties() != 2
            || grant.binding != self.binding
            || self.parties.get(self.position) != Some(&grant.party)
            || grant.triples.len() != self.context.items * MASKS_PER_ITEM
        {
            return Err(Error::Context);
        }
        let frame = field_frame(
            &self.binding,
            grant.triples.iter().flatten().map(|v| v.to_canonical_u64()),
        );
        client
            .send_frame(0, GRANT_FRAME, &frame)
            .map_err(|_| Error::Transport)?;
        drop(frame);
        drop(grant);
        let incoming = SecretBuffer(
            client
                .recv_frame(0, REQUEST_FRAME)
                .map_err(|_| Error::Transport)?,
        );
        let pairs = field_rows::<2>(&incoming, &self.binding, self.context.items * LANES)?;
        let differences: Vec<[[u64; 2]; LANES]> = pairs.as_chunks::<LANES>().0.to_vec();
        let mut context = self.context.clone();
        context.request = request_digest(&self.binding, &differences);
        let reply = self.evaluate(
            peers,
            &SpdzRequest {
                context,
                differences,
            },
        )?;
        let output = field_frame(
            &reply.context.digest(),
            reply.masked.iter().flatten().flatten().copied(),
        );
        client
            .send_frame(0, OUTPUT_FRAME, &output)
            .map_err(|_| Error::Transport)
    }
}

/// Run the client on its own authenticated confidential links to the selected servers.
/// Links are ordered by ascending enrolled party ID. The client holds no server state.
pub fn spdz_evaluate_wire<T: WireTransport>(
    public: &SpdzPublic,
    inputs: &[&[u8]],
    session: [u8; 32],
    counter: u64,
    parties: &[usize],
    links: &mut [T],
) -> Result<Evaluation, Error> {
    let items = inputs.len();
    if items == 0 || items > MAX_BATCH {
        return Err(Error::Quota);
    }
    if parties.len() != links.len()
        || parties.len() < public.config.threshold
        || parties.windows(2).any(|s| s[0] >= s[1])
        || parties.iter().any(|&id| id >= public.config.servers)
        || links.iter().any(|l| l.party() != 0 || l.parties() != 2)
    {
        return Err(Error::UnsupportedThreshold);
    }
    let binding = grant_binding(
        &public.public_key().commitment(),
        &session,
        counter,
        items,
        parties,
    );
    let mut grants = Vec::with_capacity(parties.len());
    for (&party, link) in parties.iter().zip(links.iter_mut()) {
        let frame = SecretBuffer(
            link.recv_frame(1, GRANT_FRAME)
                .map_err(|_| Error::Transport)?,
        );
        let rows = field_rows::<3>(&frame, &binding, items * MASKS_PER_ITEM)?;
        grants.push(SpdzGrant {
            party,
            binding,
            triples: rows
                .iter()
                .map(|row| row.map(Goldilocks::from_u64_reduced))
                .collect(),
        });
    }
    let (client, request) = spdz_blind(public, inputs, session, counter, &grants)?;
    drop(grants);
    let frame = field_frame(
        &binding,
        request.differences.iter().flatten().flatten().copied(),
    );
    for link in links.iter_mut() {
        link.send_frame(1, REQUEST_FRAME, &frame)
            .map_err(|_| Error::Transport)?;
    }
    let mut replies = Vec::with_capacity(parties.len());
    let digest = request.context.digest();
    for (&party, link) in parties.iter().zip(links) {
        let frame = SecretBuffer(
            link.recv_frame(1, OUTPUT_FRAME)
                .map_err(|_| Error::Transport)?,
        );
        let pairs = field_rows::<2>(&frame, &digest, items * LANES)?;
        replies.push(SpdzOutput {
            party,
            context: request.context.clone(),
            masked: pairs.as_chunks::<LANES>().0.to_vec(),
        });
    }
    client.finalize(&replies)
}

impl SpdzWireParty {
    fn open(
        &mut self,
        wire: &mut impl WireTransport,
        tag: u32,
        values: &[Goldilocks],
    ) -> Result<Vec<Goldilocks>, Error> {
        let mut bytes = SecretBuffer(Vec::with_capacity(values.len() * 8));
        for v in values {
            bytes.extend_from_slice(&v.to_canonical_u64().to_le_bytes());
        }
        let rows = SecretBuffer(
            wire.commit_open(tag, &self.binding, self.rng.next_bytes32(), &bytes)
                .map_err(|_| Error::Transport)?,
        );
        if rows.iter().any(|r| r.len() != bytes.len()) {
            return Err(Error::Encoding);
        }
        let mut shares = SecretBuffer(vec![Goldilocks::ZERO; rows.len()]);
        (0..values.len())
            .map(|k| {
                for (slot, row) in shares.iter_mut().zip(rows.iter()) {
                    let raw = row[k * 8..][..8].try_into().map_err(|_| Error::Encoding)?;
                    *slot = Goldilocks::from_canonical(u64::from_le_bytes(raw))
                        .map_err(|_| Error::Encoding)?;
                }
                self.tables
                    .open(&shares, "toprf_wire_open")
                    .map_err(preprocess_error)
            })
            .collect()
    }

    fn authenticate(
        &mut self,
        wire: &mut impl WireTransport,
        tag: u32,
        opened: &[Goldilocks],
        macs: &[GoldilocksExt2],
    ) -> Result<(), Error> {
        let coin = SecretBuffer(self.rng.next_bytes32());
        let coins = wire
            .commit_open(tag, &self.binding, self.rng.next_bytes32(), &coin[..])
            .map_err(|_| Error::Transport)?;
        let fields: Vec<_> = coins.iter().map(Vec::as_slice).collect();
        let mut challenges =
            PartyPrivateRng::from_seed(hash(b"QSAG.TOPRF.WIRE.FOLD.V1", &fields), &self.binding);
        let mut residual = SecretBuffer(GoldilocksExt2::ZERO);
        for (&value, &mac) in opened.iter().zip(macs) {
            *residual += challenges.next_ext2() * (mac - self.alpha.mul_base(value));
        }
        // Open (d+a), then r*(d+a)-c where c=r*a. A failed check reveals only
        // a freshly blinded residual, including when the same custody key is reused.
        let triple = SecretBuffer(self.blinds.pop().ok_or(Error::Preprocessing)?);
        let masked = SecretBuffer(*residual + triple[1]);
        let e = self.open(wire, tag + 1, &[masked.c0, masked.c1])?;
        let product = SecretBuffer(triple[0] * GoldilocksExt2::new(e[0], e[1]) - triple[2]);
        let result = self.open(wire, tag + 2, &[product.c0, product.c1])?;
        if result.iter().all(|v| *v == Goldilocks::ZERO) {
            Ok(())
        } else {
            Err(Error::MacCheck)
        }
    }

    fn checked(
        &mut self,
        wire: &mut impl WireTransport,
        tag: u32,
        wires: &[Wire],
    ) -> Result<Vec<Goldilocks>, Error> {
        let values = SecretBuffer(wires.iter().map(|w| w.val).collect::<Vec<_>>());
        let macs = SecretBuffer(wires.iter().map(|w| w.mac).collect::<Vec<_>>());
        let opened = self.open(wire, tag, &values)?;
        self.authenticate(wire, tag + 1, &opened, &macs)?;
        Ok(opened)
    }

    /// Evaluate on an authenticated, confidential mesh whose endpoint positions
    /// follow the selected roster. Consuming the party burns its one-use material on abort.
    pub fn evaluate(
        mut self,
        wire: &mut impl WireTransport,
        req: &SpdzRequest,
    ) -> Result<SpdzOutput, Error> {
        let context = &req.context;
        if wire.party() != self.position
            || wire.parties() != self.parties.len()
            || context.base_digest() != self.context.base_digest()
            || req.differences.len() != context.items
            || context.request != request_digest(&self.binding, &req.differences)
        {
            return Err(Error::Context);
        }
        let digest = context.digest();
        if wire
            .broadcast(0x54500000, &digest)
            .map_err(|_| Error::Transport)?
            .iter()
            .any(|m| m != &digest)
        {
            return Err(Error::Context);
        }
        let alpha = *self.alpha;
        let mut states = SecretBuffer(Vec::with_capacity(context.items));
        let mut bounds = SecretBuffer(Vec::with_capacity(context.items * LANES));
        for (item, diffs) in req.differences.iter().enumerate() {
            let mut state = [Wire::ZERO; 12];
            for (idx, pair) in diffs.iter().enumerate() {
                let input = |copy: usize| -> Result<Wire, Error> {
                    let public =
                        Goldilocks::from_canonical(pair[copy]).map_err(|_| Error::Encoding)?;
                    Ok(self.masks[mask_index(item, false, idx, copy)]
                        .add(Wire::public(public, alpha)))
                };
                state[idx] = input(0)?;
                bounds.push(state[idx].sub(input(1)?));
                state[8 + idx] = self.key[idx];
            }
            state[4] = Wire::public(Goldilocks::ONE, alpha);
            state[7] = Wire::public(Goldilocks::from_u64_reduced(SPONGE_DOMAIN), alpha);
            linear(&mut state, true);
            states.push(state);
            state.secret_wipe();
        }
        if self
            .checked(wire, 0x54500100, &bounds)?
            .iter()
            .any(|&v| v != Goldilocks::ZERO)
        {
            return Err(Error::InconsistentShares);
        }
        let mut opened_gates = Vec::new();
        let mut gate_macs = SecretBuffer(Vec::new());
        let mut step = 0;
        for (kind, rounds) in [
            (0, POSEIDON2_HALF_EXTERNAL_ROUNDS),
            (1, POSEIDON2_INTERNAL_ROUNDS),
            (2, POSEIDON2_HALF_EXTERNAL_ROUNDS),
        ] {
            let width = if kind == 1 { 1 } else { 12 };
            for round in 0..rounds {
                let mut tuples = Vec::new();
                let mut values = SecretBuffer(Vec::new());
                for state in states.iter() {
                    for (idx, w) in state[..width].iter().enumerate() {
                        let tuple = self.powers.pop().ok_or(Error::Preprocessing)?;
                        let masked = w
                            .add(Wire::public(
                                poseidon2_const_at(kind, round, idx as u64),
                                alpha,
                            ))
                            .add(Wire {
                                val: tuple.r_pows[0],
                                mac: tuple.r_macs[0],
                            });
                        values.push(masked.val);
                        gate_macs.push(masked.mac);
                        tuples.push(tuple);
                    }
                }
                let opened = self.open(wire, 0x54500200 + step, &values)?;
                step += 1;
                for ((state, ys), ts) in states
                    .iter_mut()
                    .zip(opened.chunks_exact(width))
                    .zip(tuples.chunks_exact(width))
                {
                    for ((slot, &y), tuple) in state[..width].iter_mut().zip(ys).zip(ts) {
                        *slot = expand_power7(y, tuple, alpha);
                    }
                    linear(state, kind != 1);
                }
                opened_gates.extend(opened);
            }
        }
        self.authenticate(wire, 0x54500300, &opened_gates, &gate_macs)?;
        let mut outputs = SecretBuffer(Vec::new());
        for (item, state) in states.iter().enumerate() {
            for (idx, v) in state[..LANES].iter().enumerate() {
                for copy in 0..2 {
                    outputs.push(v.add(self.masks[mask_index(item, true, idx, copy)]));
                }
            }
        }
        let opened = self.checked(wire, 0x54500400, &outputs)?;
        let masked = opened
            .chunks_exact(2 * LANES)
            .map(|row| {
                core::array::from_fn(|i| {
                    core::array::from_fn(|j| row[2 * i + j].to_canonical_u64())
                })
            })
            .collect();
        Ok(SpdzOutput {
            party: self.parties[self.position],
            context: context.clone(),
            masked,
        })
    }
}

fn expand_power7(y: Goldilocks, tuple: &AuthenticatedPower7Share, alpha: GoldilocksExt2) -> Wire {
    let coefficients = [7, 21, 35, 35, 21, 7, 1].map(Goldilocks::from_u64_reduced);
    let mut powers = [Goldilocks::ONE; 7];
    for k in (0..6).rev() {
        powers[k] = powers[k + 1] * y;
    }
    let mut result = Wire::public(powers[0] * y, alpha);
    for k in 0..7 {
        let term = Wire {
            val: tuple.r_pows[k],
            mac: tuple.r_macs[k],
        }
        .scale(coefficients[k] * powers[k]);
        result = if k % 2 == 0 {
            result.sub(term)
        } else {
            result.add(term)
        };
    }
    result
}

/// Volatile, fixed-quorum preprocessing reservoir. It cannot be cloned or serialized.
/// Prepare once, then borrow one disjoint reservation per evaluation. Never restore
/// an earlier process snapshot containing a reservoir. A restart discards it and
/// requires fresh entropy and a new batch identifier from every server.
/// This API models all parties in one process, like `SpdzSession`.
pub struct SpdzReservoir {
    state: SpdzSession,
    sessions_remaining: usize,
}

impl SpdzReservoir {
    /// Batch all requested tuples into one OT mesh and one power-tree expansion.
    /// `items` is the total item budget; `sessions` is the maximum number of uses.
    /// Each server must supply fresh private CSPRNG entropy, and `batch` must be
    /// unique for this preparation. Repeating both would recreate spent masks.
    pub fn prepare(
        quorum: &mut [&mut SpdzServer],
        batch: [u8; 32],
        items: usize,
        sessions: usize,
        entropy: &[[u8; 32]],
    ) -> Result<Self, Error> {
        Self::prepare_with_sboxes(
            quorum,
            batch,
            None,
            items,
            sessions,
            entropy,
            items.checked_mul(SBOXES_PER_ITEM).ok_or(Error::Quota)?,
        )
    }

    /// `one_shot` is the counter of the single session a [`SpdzSession::begin`] batch
    /// serves; it separates that batch from every other use of the same `session`.
    fn prepare_with_sboxes(
        quorum: &mut [&mut SpdzServer],
        session: [u8; 32],
        one_shot: Option<u64>,
        items: usize,
        sessions: usize,
        entropy: &[[u8; 32]],
        sboxes: usize,
    ) -> Result<Self, Error> {
        if sessions == 0 || sessions > items {
            return Err(Error::Quota);
        }
        let m = quorum.len();
        let Some(first) = quorum.first() else {
            return Err(Error::UnsupportedThreshold);
        };
        let public = first.public.clone();
        let threshold = public.config.threshold;
        let parties: Vec<usize> = quorum.iter().map(|server| server.party).collect();
        if m < threshold || parties.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(Error::UnsupportedThreshold);
        }
        if entropy.len() != m {
            return Err(Error::Encoding);
        }
        if quorum.iter().any(|server| server.public != public) {
            return Err(Error::Context);
        }
        if items == 0 || items > MAX_BATCH {
            return Err(Error::Quota);
        }
        let key_commitment = public.public_key().commitment();
        let binding = grant_binding(&key_commitment, &session, 0, items, &parties);
        let scope: &[u8] = match &one_shot {
            None => b"reservoir",
            Some(_) => b"one-shot",
        };
        let sid = hash(
            b"QSAG.TOPRF.SPDZ.PREPROCESS.V2",
            &[
                &binding,
                &(sessions as u64).to_le_bytes(),
                scope,
                &one_shot.unwrap_or(0).to_le_bytes(),
            ],
        );
        // Hedge each server's session randomness with its long-term share.
        let hedged: SecretBuffer<Vec<[u8; 32]>> = SecretBuffer(
            quorum
                .iter()
                .zip(entropy)
                .map(|(server, seed)| {
                    let custody = SecretBuffer(server.to_secret_bytes());
                    hash(b"QSAG.TOPRF.SPDZ.ENTROPY.V1", &[seed, &custody[..]])
                })
                .collect(),
        );
        let mut rngs = party_rngs(b"QSAG.TOPRF.SPDZ.PREPROCESS.RNG.V1", &sid, &hedged);
        let points = eval_points(&parties);
        let weights = lagrange_weights_zero_goldilocks(&points).ok_or(Error::Encoding)?;
        // Lagrange-rescaled shares are additive contributions to `alpha` on this quorum.
        let alpha_shares: SecretBuffer<Vec<GoldilocksExt2>> =
            SecretBuffer(quorum.iter().map(|server| server.alpha).collect());
        let alpha_contribs: SecretBuffer<Vec<GoldilocksExt2>> = SecretBuffer(
            alpha_shares
                .iter()
                .zip(&weights)
                .map(|(share, &weight)| share.mul_base(weight))
                .collect(),
        );
        let mesh = OtMesh::try_establish(sid, &mut rngs).map_err(preprocess_error)?;

        let mut this = SpdzSession {
            threshold,
            sid,
            binding,
            key_commitment,
            session,
            counter: 0,
            items,
            parties,
            opening_tables: GoldilocksOpeningTables::new(threshold, &points)
                .map_err(preprocess_error)?,
            points,
            rngs,
            alpha: alpha_shares.to_vec(),
            mesh: Some(mesh),
            pool: TuplePool::new(),
            key: quorum.iter().map(|server| server.key).collect(),
            masks: Vec::new(),
        };

        // Check the stored key shares against their MACs before the long step: each
        // limb is opened under a fresh authenticated mask.
        let check_sid = hash(b"QSAG.TOPRF.SPDZ.KEYCHECK.V1", &[&sid]);
        let mut check = {
            let mesh_ref = this.mesh.as_mut().ok_or(Error::MacCheck)?;
            run_dealerless_pi_pow7_with_alpha(
                check_sid,
                threshold,
                &this.points,
                0,
                LANES,
                0,
                &alpha_contribs,
                &alpha_shares,
                mesh_ref,
                &mut this.rngs,
            )
            .map_err(preprocess_error)?
        };
        let mut blinded = SecretBuffer(vec![Vec::with_capacity(LANES); m]);
        for ((wires, vault), key) in blinded.iter_mut().zip(&mut check).zip(&this.key) {
            let triples = vault.reserve_beaver(LANES).map_err(preprocess_error)?;
            for (limb, triple) in key.iter().zip(triples) {
                wires.push(limb.add(Wire {
                    val: triple.a,
                    mac: triple.a_mac,
                }));
            }
        }
        this.checked_open_wires("toprf_spdz_key_share", &blinded)?;
        drop(check);
        // Each session copies the key shares it checks; none stay with idle tuples.
        this.key.secret_wipe();

        // Single unchunked ceremony: `qsag_core::preprocessing` authenticates in linear
        // `BLOCK = 32` flights without quadratic whole-batch overhead.
        let triples = MASKS_PER_ITEM * items + LANES * sessions;
        let run_sid = hash(b"QSAG.TOPRF.SPDZ.CHUNK.V1", &[&sid, &0u64.to_le_bytes()]);
        let chunk = {
            let mesh_ref = this.mesh.as_mut().ok_or(Error::MacCheck)?;
            run_dealerless_pi_pow7_with_alpha(
                run_sid,
                threshold,
                &this.points,
                sboxes,
                triples,
                0,
                &alpha_contribs,
                &alpha_shares,
                mesh_ref,
                &mut this.rngs,
            )
            .map_err(preprocess_error)?
        };
        this.pool.chunks.push(chunk);
        Ok(Self {
            state: this,
            sessions_remaining: sessions,
        })
    }

    /// Burn a counter and reserve one session. The borrow prevents simultaneous
    /// use, and dropping an abandoned reservation burns its entire tuple budget.
    pub fn begin<'a>(
        &'a mut self,
        quorum: &mut [&mut SpdzServer],
        stores: &mut [&mut dyn CounterStore],
        session: [u8; 32],
        counter: u64,
        items: usize,
    ) -> Result<(SpdzPreparedSession<'a>, Vec<SpdzGrant>), Error> {
        let sboxes = items.checked_mul(SBOXES_PER_ITEM).ok_or(Error::Quota)?;
        self.check_quorum(quorum, items, sboxes)?;
        reserve_counters(quorum, stores, counter, items)?;
        let grants = match self.start_reserved(quorum, session, counter, items, sboxes) {
            Ok(grants) => grants,
            Err(error) => {
                self.poison();
                return Err(error);
            }
        };
        let remaining = self.state.pool.remaining_pow7();
        Ok((
            SpdzPreparedSession {
                pool: self,
                remaining,
                sboxes,
            },
            grants,
        ))
    }

    fn check_quorum(
        &self,
        quorum: &[&mut SpdzServer],
        items: usize,
        sboxes: usize,
    ) -> Result<(), Error> {
        if quorum.len() != self.state.parties.len()
            || quorum.iter().zip(&self.state.parties).any(|(s, &p)| {
                s.party != p || s.public_key().commitment() != self.state.key_commitment
            })
        {
            return Err(Error::Context);
        }
        if items == 0
            || items > MAX_BATCH
            || self.sessions_remaining == 0
            || self.state.pool.remaining_pow7() < sboxes
            || self.state.pool.remaining_beaver() < items * MASKS_PER_ITEM + LANES
        {
            return Err(Error::Quota);
        }
        Ok(())
    }

    fn start_reserved(
        &mut self,
        quorum: &[&mut SpdzServer],
        session: [u8; 32],
        counter: u64,
        items: usize,
        sboxes: usize,
    ) -> Result<Vec<SpdzGrant>, Error> {
        self.check_quorum(quorum, items, sboxes)?;
        self.sessions_remaining -= 1;
        let this = &mut self.state;
        this.session = session;
        this.counter = counter;
        this.items = items;
        this.binding = grant_binding(
            &this.key_commitment,
            &session,
            counter,
            items,
            &this.parties,
        );
        this.sid = hash(b"QSAG.TOPRF.SPDZ.SESSION.V1", &[&this.binding]);
        this.key.secret_wipe();
        this.key = quorum.iter().map(|s| s.key).collect();
        let m = quorum.len();
        let mut blinded = SecretBuffer(vec![Vec::with_capacity(LANES); m]);
        let key_masks = this.pool.take_beaver(LANES)?;
        for ((wires, triples), key) in blinded.iter_mut().zip(&key_masks).zip(&this.key) {
            for (limb, triple) in key.iter().zip(triples) {
                wires.push(limb.add(Wire {
                    val: triple.a,
                    mac: triple.a_mac,
                }));
            }
        }
        this.checked_open_wires("toprf_spdz_key_share", &blinded)?;
        this.masks.secret_wipe();
        this.masks.clear();
        this.masks.reserve(m);
        let mut grants = Vec::with_capacity(m);
        let client_masks = this.pool.take_beaver(MASKS_PER_ITEM * items)?;
        for (index, triples) in client_masks.iter().enumerate() {
            this.masks.push(
                triples
                    .iter()
                    .map(|t| Wire {
                        val: t.a,
                        mac: t.a_mac,
                    })
                    .collect(),
            );
            grants.push(SpdzGrant {
                party: this.parties[index],
                binding: this.binding,
                triples: triples.iter().map(|t| [t.a, t.b, t.c]).collect(),
            });
        }
        Ok(grants)
    }

    fn poison(&mut self) {
        self.state.mesh = None;
        self.state.pool.poison();
        self.state.alpha.secret_wipe();
        self.state.key.secret_wipe();
        self.state.masks.secret_wipe();
        self.state.masks.clear();
    }
}

/// A single-use reservation borrowing its reservoir exclusively.
pub struct SpdzPreparedSession<'a> {
    pool: &'a mut SpdzReservoir,
    remaining: usize,
    sboxes: usize,
}
impl SpdzPreparedSession<'_> {
    /// A refused request spends this reservation only; a failed opening or MAC check
    /// discards the reservoir.
    pub fn evaluate(self, request: &SpdzRequest) -> Result<Vec<SpdzOutput>, Error> {
        let result = self.pool.state.evaluate_inner(request);
        if matches!(result, Err(Refusal::Quorum(_))) {
            self.pool.poison();
        }
        result.map_err(Refusal::into_error)
    }
}
impl Drop for SpdzPreparedSession<'_> {
    fn drop(&mut self) {
        let tuples = &mut self.pool.state.pool;
        let used = self.remaining.saturating_sub(tuples.remaining_pow7());
        let _ = tuples.take_pow7(self.sboxes.saturating_sub(used));
        self.pool.state.key.secret_wipe();
        self.pool.state.masks.secret_wipe();
        self.pool.state.masks.clear();
    }
}

fn reserve_counters(
    quorum: &mut [&mut SpdzServer],
    stores: &mut [&mut dyn CounterStore],
    counter: u64,
    items: usize,
) -> Result<(), Error> {
    let first = quorum.first().ok_or(Error::UnsupportedThreshold)?;
    let cfg = first.public.config;
    if quorum.len() < cfg.threshold
        || quorum.len() > cfg.servers
        || quorum.iter().any(|s| s.party >= cfg.servers)
        || quorum.windows(2).any(|pair| pair[0].party >= pair[1].party)
    {
        return Err(Error::UnsupportedThreshold);
    }
    if stores.len() != quorum.len() {
        return Err(Error::Encoding);
    }
    if items == 0 || items > MAX_BATCH {
        return Err(Error::Quota);
    }
    let public = first.public.clone();
    if quorum.iter().any(|s| s.public != public) {
        return Err(Error::Context);
    }
    let key = public.public_key().commitment();
    // Pre-validate monotone counter admission across ALL servers before mutating `stores[0]`.
    for (server, store) in quorum.iter_mut().zip(stores.iter()) {
        admit_counter(&mut server.last_counter, &**store, counter)?;
    }
    // Ratchet every server's in-memory `last_counter` monotonically even if an I/O failure on
    // `stores[i]` (`i > 0`) aborts partway through durable reservation.
    let mut persist_err = None;
    for (server, store) in quorum.iter_mut().zip(stores.iter_mut()) {
        if persist_err.is_none()
            && let Err(err) = store.reserve(&key, server.party, counter, items)
        {
            persist_err = Some(err);
        }
        server.last_counter = Some(
            server
                .last_counter
                .map_or(counter, |last| last.max(counter)),
        );
    }
    match persist_err {
        Some(err) => Err(err),
        None => Ok(()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::voprf::plaintext;

    struct Store(Option<u64>);
    impl CounterStore for Store {
        fn high_water(&self) -> Result<Option<u64>, Error> {
            Ok(self.0)
        }
        fn reserve(&mut self, _: &[u8; 32], _: usize, counter: u64, _: usize) -> Result<(), Error> {
            if self.0.is_some_and(|last| counter <= last) {
                return Err(Error::Counter);
            }
            self.0 = Some(counter);
            Ok(())
        }
    }

    fn entropy(count: usize, tag: u8) -> Vec<[u8; 32]> {
        (0..count)
            .map(|i| core::array::from_fn(|b| tag ^ (i as u8).wrapping_mul(31) ^ b as u8))
            .collect()
    }

    /// Test-only reconstruction of the key from `t` shares.
    fn reconstruct(servers: &[&SpdzServer]) -> [u64; 4] {
        let parties: Vec<usize> = servers.iter().map(|s| s.party).collect();
        let weights = lagrange_weights_zero_goldilocks(&eval_points(&parties)).unwrap();
        core::array::from_fn(|lane| {
            servers
                .iter()
                .zip(&weights)
                .fold(Goldilocks::ZERO, |acc, (s, &w)| acc + s.key[lane].val * w)
                .to_canonical_u64()
        })
    }

    fn begin(
        quorum: &mut [&mut SpdzServer],
        stores: &mut [Store],
        counter: u64,
        items: usize,
        tag: u8,
    ) -> Result<(SpdzSession, Vec<SpdzGrant>), Error> {
        let seeds = entropy(quorum.len(), tag);
        let mut stores: Vec<&mut dyn CounterStore> = stores
            .iter_mut()
            .map(|s| s as &mut dyn CounterStore)
            .collect();
        SpdzSession::begin(quorum, &mut stores, [9; 32], counter, items, &seeds)
    }

    #[test]
    fn fabricated_evaluation_cannot_authorize_issuance() {
        use crate::blind_vc::*;
        let key = PublicKey::test_key();
        let (req, _) =
            holder_prepare_blind_issuance(42, &[1], key.commitment(), 7, [4; 32], [5; 32]).unwrap();
        let receipt_key = IssuanceReceiptKey::new([99; 32]);
        let mut accumulator = IssuerCredentialAccumulator::new(key.clone(), 7);
        let root = accumulator.root();
        let mut forged = Evaluation {
            values: vec![[8; 32]],
            faulty_servers: Vec::new(),
            key: key.commitment(),
            input_digests: vec![hash(b"QSAG.TOPRF.INPUT.BIND.V1", &[&issuance_input(&req)])],
            context: Context::new(key.commitment(), [7; 32], 0, 1, [6; 32]),
            receipt_tags: Vec::new(),
        };
        for tags in [
            Vec::new(),
            vec![[0; 32]],
            vec![IssuanceReceiptKey::new([1; 32]).tag(
                &forged.key,
                &forged.context,
                &forged.input_digests[0],
                &forged.values[0],
            )],
        ] {
            forged.receipt_tags = tags;
            assert_eq!(
                threshold_issue_blind_vc(&mut accumulator, &req, &[1], &forged, &receipt_key, 42)
                    .unwrap_err(),
                BlindVcError::InvalidOprfEvaluation
            );
            assert_eq!(accumulator.root(), root);
        }
        forged.receipt_tags = vec![receipt_key.tag(
            &forged.key,
            &forged.context,
            &forged.input_digests[0],
            &forged.values[0],
        )];
        assert!(
            forged
                .authenticated_value_for(&key, &issuance_input(&req), &receipt_key)
                .is_some()
        );
        for field in 0..3 {
            let original = [
                forged.context.session,
                forged.input_digests[0],
                forged.values[0],
            ];
            match field {
                0 => forged.context.session[0] ^= 1,
                1 => forged.input_digests[0][0] ^= 1,
                _ => forged.values[0][0] ^= 1,
            }
            assert_eq!(
                threshold_issue_blind_vc(&mut accumulator, &req, &[1], &forged, &receipt_key, 42)
                    .unwrap_err(),
                BlindVcError::InvalidOprfEvaluation
            );
            forged.context.session = original[0];
            forged.input_digests[0] = original[1];
            forged.values[0] = original[2];
        }
        assert_eq!(accumulator.root(), root);
        assert!(
            threshold_issue_blind_vc(&mut accumulator, &req, &[1], &forged, &receipt_key, 42)
                .is_ok()
        );
    }

    #[test]
    fn receipt_authentication_blocks_cross_pk_cross_context_and_duplicate_replay() {
        use crate::blind_vc::*;
        let pk1 = PublicKey::test_key();
        let pk2 = PublicKey {
            commitment: hash(b"QSAG.TOPRF.KEY.V1", &[b"issuer-2"]),
        };
        let receipt_key = IssuanceReceiptKey::new([0x5A; 32]);
        let (req_a, _) =
            holder_prepare_blind_issuance(42, &[10], pk1.commitment(), 7, [0x11; 32], [0x22; 32])
                .unwrap();
        let (req_b_diff_session, _) =
            holder_prepare_blind_issuance(42, &[10], pk1.commitment(), 7, [0x11; 32], [0x33; 32])
                .unwrap();
        let (req_pk2, _) =
            holder_prepare_blind_issuance(42, &[10], pk2.commitment(), 7, [0x11; 32], [0x22; 32])
                .unwrap();

        let ctx_a = Context::new(pk1.commitment(), [0x44; 32], 1, 1, [0x55; 32]);
        let ctx_b = Context::new(pk1.commitment(), [0x66; 32], 1, 1, [0x55; 32]);
        let digest_a = hash(b"QSAG.TOPRF.INPUT.BIND.V1", &[&issuance_input(&req_a)]);
        let val_a = [0x77; 32];
        let eval_a = Evaluation {
            values: vec![val_a],
            faulty_servers: Vec::new(),
            key: pk1.commitment(),
            input_digests: vec![digest_a],
            context: ctx_a.clone(),
            receipt_tags: vec![receipt_key.tag(&pk1.commitment(), &ctx_a, &digest_a, &val_a)],
        };

        // 1. Cross-context replay rejected when caller pins expected TOPRF context.
        assert_eq!(
            eval_a.authenticated_value_for_context(
                &pk1,
                &ctx_a,
                &issuance_input(&req_a),
                &receipt_key,
            ),
            Some(val_a)
        );
        assert_eq!(
            eval_a.authenticated_value_for_context(
                &pk1,
                &ctx_b,
                &issuance_input(&req_a),
                &receipt_key,
            ),
            None
        );

        // 2. Cross-session replay (`req_b_diff_session` with same attribute commit & PK) rejected.
        let mut acc1 = IssuerCredentialAccumulator::new(pk1.clone(), 7);
        assert_eq!(
            threshold_issue_blind_vc(
                &mut acc1,
                &req_b_diff_session,
                &[10],
                &eval_a,
                &receipt_key,
                42,
            )
            .unwrap_err(),
            BlindVcError::InvalidOprfEvaluation
        );

        // 3. Cross-PK replay (`pk1` evaluation transplanted to `pk2` accumulator/request) rejected
        // even if an attacker rewrites the unverified outer `eval.key` and `eval.context.key`!
        let mut acc2 = IssuerCredentialAccumulator::new(pk2.clone(), 7);
        let mut transplanted = eval_a.clone();
        transplanted.key = pk2.commitment();
        transplanted.context.key = pk2.commitment();
        assert_eq!(
            transplanted.authenticated_value_for(&pk2, &issuance_input(&req_a), &receipt_key),
            None
        );
        assert_eq!(
            threshold_issue_blind_vc(&mut acc2, &req_pk2, &[10], &transplanted, &receipt_key, 42,)
                .unwrap_err(),
            BlindVcError::InvalidOprfEvaluation
        );

        // 4. Legitimate issuance succeeds once, then duplicate replay of the same `(req_a, eval_a)`
        // is rejected by the accumulator without mutating the Merkle root.
        assert!(
            threshold_issue_blind_vc(&mut acc1, &req_a, &[10], &eval_a, &receipt_key, 42).is_ok()
        );
        let committed_root = acc1.root();
        assert_eq!(
            threshold_issue_blind_vc(&mut acc1, &req_a, &[10], &eval_a, &receipt_key, 42)
                .unwrap_err(),
            BlindVcError::InvalidOprfEvaluation
        );
        assert_eq!(acc1.root(), committed_root);
    }

    #[test]
    fn evaluation_debug_redacts_outputs_and_receipt_tags() {
        let key = PublicKey::test_key();
        let evaluation = Evaluation {
            values: vec![[0xA7; 32]],
            faulty_servers: vec![3],
            key: key.commitment(),
            input_digests: vec![[0x11; 32]],
            context: Context::new(key.commitment(), [7; 32], 0, 1, [6; 32]),
            receipt_tags: vec![[0xB9; 32]],
        };
        let shown = std::format!("{evaluation:?}");
        assert!(shown.contains("<REDACTED>") && shown.contains("faulty_servers: [3]"));
        // Neither the output nor the tag byte appears in any radix Debug uses.
        for byte in ["167", "a7", "A7", "185", "b9", "B9"] {
            assert!(!shown.contains(byte), "{byte} leaked in {shown}");
        }
    }

    #[test]
    fn committee_shapes() {
        assert!(SpdzConfig::new(2, 2).is_ok());
        assert!(SpdzConfig::new(64, 64).is_ok());
        assert!(SpdzConfig::new(33, 64).is_ok());
        for (t, n) in [(1, 5), (0, 0), (6, 5), (2, 65)] {
            assert_eq!(SpdzConfig::new(t, n), Err(Error::UnsupportedThreshold));
        }
    }

    #[test]
    fn exactly_t_servers_evaluate_and_tampering_is_rejected() {
        let config = SpdzConfig::new(3, 5).unwrap();
        let mut servers = spdz_dkg(config, [1; 32], &entropy(5, 0x11)).unwrap();
        let public = servers[0].public().clone();
        let key = reconstruct(&[&servers[0], &servers[1], &servers[2]]);
        assert_eq!(key, reconstruct(&[&servers[1], &servers[3], &servers[4]]));

        // Custody round trip, and a share that does not match the enrolled record.
        let bytes = servers[4].to_secret_bytes();
        let restored = SpdzServer::from_secret_bytes(&bytes, &public, 4).unwrap();
        assert_eq!(restored.to_secret_bytes(), bytes);
        assert_eq!(
            SpdzServer::from_secret_bytes(&bytes, &public, 3).unwrap_err(),
            Error::Context
        );
        let mut forged = bytes.clone();
        forged[70] ^= 1;
        assert_eq!(
            SpdzServer::from_secret_bytes(&forged, &public, 4).unwrap_err(),
            Error::Context
        );
        assert_eq!(SpdzPublic::from_bytes(&public.to_bytes()).unwrap(), public);

        // Two servers are below the threshold, whichever two.
        let mut stores = [Store(None), Store(None), Store(None)];
        {
            let (a, rest) = servers.split_at_mut(1);
            let mut pair = [&mut a[0], &mut rest[2]];
            assert_eq!(
                begin(&mut pair, &mut stores[..2], 0, 1, 0x20).unwrap_err(),
                Error::UnsupportedThreshold
            );
        }

        // A stored share altered without its MAC aborts before tuple generation.
        let honest = servers[3].key[2];
        servers[3].key[2].val += Goldilocks::ONE;
        {
            let mut it = servers.iter_mut();
            let (s0, _, _, s3, s4) = (
                it.next().unwrap(),
                it.next().unwrap(),
                it.next().unwrap(),
                it.next().unwrap(),
                it.next().unwrap(),
            );
            let mut quorum = [s0, s3, s4];
            assert_eq!(
                begin(&mut quorum, &mut stores, 0, 1, 0x21).unwrap_err(),
                Error::MacCheck
            );
        }
        servers[3].key[2] = honest;
        // The aborted session burned counter 0 at every server it reached.
        assert!(stores.iter().all(|s| s.0 == Some(0)));

        // Servers 0, 3, 4 evaluate; 1 and 2 are absent.
        let inputs: [&[u8]; 1] = [b"correct horse"];
        let (session, mut grants) = {
            let mut it = servers.iter_mut();
            let (s0, _, _, s3, s4) = (
                it.next().unwrap(),
                it.next().unwrap(),
                it.next().unwrap(),
                it.next().unwrap(),
                it.next().unwrap(),
            );
            let mut quorum = [s0, s3, s4];
            assert_eq!(
                begin(&mut quorum, &mut stores, 0, 1, 0x22).unwrap_err(),
                Error::Counter
            );
            begin(&mut quorum, &mut stores, 1, 1, 0x23).unwrap()
        };
        // A server that lies to the client about a mask share is caught by the client.
        let honest = grants[1].triples[5][0];
        grants[1].triples[5][0] += Goldilocks::ONE;
        assert_eq!(
            spdz_blind(&public, &inputs, [9; 32], 1, &grants).unwrap_err(),
            Error::InconsistentShares
        );
        grants[1].triples[5][0] = honest;
        let (client, request) = spdz_blind(&public, &inputs, [9; 32], 1, &grants).unwrap();
        let outputs = session.evaluate(&request).unwrap();

        // Replies that disagree, or a missing reply, are refused.
        let mut altered = outputs.clone();
        altered[2].masked[0][1][0] ^= 1;
        let (probe, _) = spdz_blind(&public, &inputs, [9; 32], 1, &grants).unwrap();
        assert_eq!(
            probe.finalize(&altered).unwrap_err(),
            Error::InconsistentShares
        );
        let (probe, _) = spdz_blind(&public, &inputs, [9; 32], 1, &grants).unwrap();
        assert_eq!(
            probe.finalize(&outputs[..2]).unwrap_err(),
            Error::UnsupportedThreshold
        );

        let evaluation = client.finalize(&outputs).unwrap();
        assert_eq!(evaluation.values(), &[plaintext(&key, inputs[0])]);
        assert_eq!(
            evaluation.value_for(&public.public_key(), inputs[0]),
            Some(plaintext(&key, inputs[0]))
        );
    }

    /// The committee bound, as a measurement: enrollment authenticates the key shares
    /// across all 64 servers over 4032 oblivious-transfer channels (minutes), so it is
    /// run on demand:
    /// `cargo test --release -p qsag-cred --lib sixty_four_servers -- --ignored --nocapture`.
    #[test]
    #[ignore = "minutes of oblivious-transfer setup; run on demand"]
    fn sixty_four_servers_enroll() {
        let started = std::time::Instant::now();
        let config = SpdzConfig::new(8, 64).unwrap();
        let mut servers = spdz_dkg(config, [3; 32], &entropy(64, 0x41)).unwrap();
        std::println!("(8, 64) enrollment: {:?}", started.elapsed());
        let public = servers[0].public().clone();
        let selected = [0, 7, 15, 23, 31, 39, 47, 63];
        let key = reconstruct(&selected.iter().map(|&i| &servers[i]).collect::<Vec<_>>());
        assert_eq!(
            key,
            reconstruct(&servers.iter().take(8).collect::<Vec<_>>())
        );
        for server in &servers {
            SpdzServer::from_secret_bytes(&server.to_secret_bytes(), &public, server.party)
                .unwrap();
        }
        let mut quorum: Vec<_> = servers
            .iter_mut()
            .filter(|s| selected.contains(&s.party))
            .collect();
        let started = std::time::Instant::now();
        let mut pool =
            SpdzReservoir::prepare(&mut quorum, [0x51; 32], 2, 2, &entropy(8, 0x52)).unwrap();
        std::println!(
            "(8, 64) batch preprocessing, two items: {:?}",
            started.elapsed()
        );
        let mut stores: Vec<_> = (0..8).map(|_| Store(None)).collect();
        let inputs: [&[u8]; 1] = [b"64-server end-to-end"];
        for counter in 0..2 {
            let started = std::time::Instant::now();
            let mut store_refs: Vec<&mut dyn CounterStore> = stores
                .iter_mut()
                .map(|s| s as &mut dyn CounterStore)
                .collect();
            let (session, grants) = pool
                .begin(&mut quorum, &mut store_refs, [0x53; 32], counter, 1)
                .unwrap();
            let (client, request) =
                spdz_blind(&public, &inputs, [0x53; 32], counter, &grants).unwrap();
            let outputs = session.evaluate(&request).unwrap();
            let evaluation = client.finalize(&outputs).unwrap();
            assert_eq!(evaluation.values(), &[plaintext(&key, inputs[0])]);
            std::println!(
                "(8, 64) preprocessed online {counter}: {:?}",
                started.elapsed()
            );
        }
    }

    #[test]
    fn wire_parties_match_plaintext_and_abort_on_a_bad_online_key_share() {
        use qsag_core::wire_transport::TransportError;
        use std::sync::mpsc::{Receiver, Sender, channel};
        struct Peer(usize, Sender<(u32, Vec<u8>)>, Receiver<(u32, Vec<u8>)>);
        impl WireTransport for Peer {
            fn party(&self) -> usize {
                self.0
            }
            fn parties(&self) -> usize {
                2
            }
            fn send_frame(
                &mut self,
                to: usize,
                tag: u32,
                data: &[u8],
            ) -> Result<(), TransportError> {
                assert_eq!(to, 1 - self.0);
                self.1
                    .send((tag, data.to_vec()))
                    .map_err(|_| TransportError::Closed { peer: to })
            }
            fn recv_frame(&mut self, from: usize, tag: u32) -> Result<Vec<u8>, TransportError> {
                assert_eq!(from, 1 - self.0);
                let (got, row) = self
                    .2
                    .recv_timeout(std::time::Duration::from_secs(20))
                    .map_err(|_| TransportError::Closed { peer: from })?;
                if got != tag {
                    return Err(TransportError::RoundTagMismatch { expected: tag, got });
                }
                Ok(row)
            }
            fn recv_authenticated_envelope(
                &mut self,
                from: usize,
                tag: u32,
            ) -> Result<Vec<u8>, TransportError> {
                self.recv_frame(from, tag)
            }
        }
        let mut servers = spdz_dkg(
            SpdzConfig::new(2, 3).unwrap(),
            [0x81; 32],
            &entropy(3, 0x82),
        )
        .unwrap();
        let key = reconstruct(&[&servers[0], &servers[2]]);
        let public = servers[0].public().clone();
        let inputs: [&[u8]; 1] = [b"wire evaluation"];
        let mut nodes = [0, 2].map(|id| {
            SpdzServer::from_secret_bytes(&servers[id].to_secret_bytes(), &public, id).unwrap()
        });
        let mut receipts = [Store(None), Store(None)];
        let mut stores = [Store(None), Store(None)];
        for counter in 0..2 {
            let roster = [0, 2];
            let round = SpdzWireRound {
                parties: &roster,
                session: [9; 32],
                counter,
                items: 1,
            };
            let points = eval_points(&roster);
            let alphas = roster.map(|id| servers[id].alpha);
            let weights = lagrange_weights_zero_goldilocks(&points).unwrap();
            let contributions = core::array::from_fn::<_, 2, _>(|i| alphas[i].mul_base(weights[i]));
            let sid = [0x83 + counter as u8; 32];
            let mut rngs = party_rngs(b"wire-test", &sid, &entropy(2, sid[0]));
            let mut mesh = OtMesh::try_establish(sid, &mut rngs).unwrap();
            let circuit = run_dealerless_pi_pow7_with_alpha(
                sid,
                2,
                &points,
                SBOXES_PER_ITEM,
                MASKS_PER_ITEM,
                0,
                &contributions,
                &alphas,
                &mut mesh,
                &mut rngs,
            )
            .unwrap();
            let blinding = qsag_core::preprocessing::run_dealerless_pi_pow7(
                [sid[0] + 2; 32],
                2,
                &points,
                0,
                3,
                0,
                &mut mesh,
                &mut rngs,
            )
            .unwrap();
            // The online servers each take only their own preprocessed material.
            let (parties, grants): (Vec<_>, Vec<_>) = roster
                .into_iter()
                .zip(&mut stores)
                .zip(circuit)
                .zip(blinding)
                .zip(rngs)
                .map(|((((id, store), pool), masks), rng)| {
                    servers[id]
                        .reserve_wire(&round, store, pool, masks, rng)
                        .unwrap()
                })
                .unzip();
            assert!(stores.iter().all(|s| s.0 == Some(counter)));
            let (mut parties, grants): (Vec<_>, Vec<_>) = parties
                .into_iter()
                .zip(grants)
                .zip(nodes.iter_mut().zip(&mut receipts))
                .map(|((party, grant), (node, store))| {
                    let (tx, rx) = channel();
                    let (back, unused) = channel();
                    let mut provider = Peer(0, tx, unused);
                    let mut destination = Peer(1, back, rx);
                    party.dispatch(grant, &mut provider).unwrap();
                    let original =
                        SecretBuffer(destination.recv_frame(0, PREPROCESS_FRAME).unwrap());
                    let rng = || {
                        PartyPrivateRng::from_seed([0x33 + node.party as u8; 32], b"receive-test")
                    };
                    let node_rng = rng();
                    let replay_rng = rng();
                    provider.send_frame(1, PREPROCESS_FRAME, &original).unwrap();
                    let job = node
                        .receive_wire(&round, store, &mut destination, node_rng)
                        .unwrap();
                    provider.send_frame(1, PREPROCESS_FRAME, &original).unwrap();
                    assert!(matches!(
                        node.receive_wire(&round, store, &mut destination, replay_rng),
                        Err(Error::Counter)
                    ));
                    job
                })
                .unzip();
            let (client, request) =
                spdz_blind(&public, &inputs, [9; 32], counter, &grants).unwrap();
            if counter == 1 {
                parties[0].key[2].val += Goldilocks::ONE;
            }
            let (tx0, rx0) = channel();
            let (tx1, rx1) = channel();
            let outputs = std::thread::scope(|scope| {
                let threads = parties
                    .into_iter()
                    .zip([Peer(0, tx0, rx1), Peer(1, tx1, rx0)])
                    .map(|(party, mut endpoint)| {
                        let request = &request;
                        scope.spawn(move || party.evaluate(&mut endpoint, request))
                    })
                    .collect::<Vec<_>>();
                threads
                    .into_iter()
                    .map(|h| h.join().unwrap())
                    .collect::<Vec<_>>()
            });
            if counter == 0 {
                let replies = outputs.into_iter().collect::<Result<Vec<_>, _>>().unwrap();
                assert_eq!(
                    client.finalize(&replies).unwrap().values(),
                    &[plaintext(&key, inputs[0])]
                );
            } else {
                assert!(
                    outputs
                        .iter()
                        .all(|reply| matches!(reply, Err(Error::MacCheck)))
                );
            }
        }
    }

    #[test]
    fn altered_session_state_fails_the_mac_check_before_release() {
        let config = SpdzConfig::new(2, 3).unwrap();
        let mut servers = spdz_dkg(config, [2; 32], &entropy(3, 0x31)).unwrap();
        let public = servers[0].public().clone();
        let inputs: [&[u8]; 1] = [b"input"];
        let mut stores = [Store(None), Store(None)];
        let (mut session, grants) = {
            let (a, rest) = servers.split_at_mut(1);
            let mut quorum = [&mut a[0], &mut rest[1]];
            begin(&mut quorum, &mut stores, 0, 1, 0x32).unwrap()
        };
        let (_, request) = spdz_blind(&public, &inputs, [9; 32], 0, &grants).unwrap();
        // One server uses a different key share inside the session.
        session.key[1][0].val += Goldilocks::ONE;
        assert_eq!(session.evaluate(&request).unwrap_err(), Error::MacCheck);

        // The input checks precede the circuit, so a session without S-box tuples
        // reaches them.
        let (session, grants) = {
            let (a, rest) = servers.split_at_mut(1);
            let mut quorum = [&mut a[0], &mut rest[1]];
            let seeds = entropy(2, 0x33);
            let mut stores: Vec<&mut dyn CounterStore> = stores
                .iter_mut()
                .map(|s| s as &mut dyn CounterStore)
                .collect();
            SpdzSession::begin_with_sboxes(&mut quorum, &mut stores, [9; 32], 1, 1, &seeds, 0)
                .unwrap()
        };
        let (_, honest) = spdz_blind(&public, &inputs, [9; 32], 1, &grants).unwrap();
        // A request altered in transit is not the one the grants were issued for.
        let mut altered = honest.clone();
        altered.differences[0][0][0] ^= 1;
        assert_eq!(session.check_request(&altered).unwrap_err(), Error::Context);
        // A client that masks one limb two different ways is refused before any
        // key-dependent gate.
        altered.context = Context::new(
            *honest.context.key(),
            *honest.context.session(),
            1,
            1,
            request_digest(&session.binding, &altered.differences),
        );
        session.check_request(&altered).unwrap();
        assert_eq!(
            session.evaluate(&altered).unwrap_err(),
            Error::InconsistentShares
        );
    }
    #[test]
    fn reservoir_rejects_replay_wrong_quorum_and_burns_abandonment() {
        let mut servers = spdz_dkg(
            SpdzConfig::new(2, 3).unwrap(),
            [0x61; 32],
            &entropy(3, 0x62),
        )
        .unwrap();
        let public = servers[0].public().clone();
        let key = reconstruct(&[&servers[0], &servers[2]]);
        let mut quorum: Vec<_> = servers.iter_mut().filter(|s| s.party != 1).collect();
        let mut pool =
            SpdzReservoir::prepare(&mut quorum, [0x63; 32], 3, 3, &entropy(2, 0x64)).unwrap();
        let mut stores = [Store(None), Store(None)];
        let mut refs: Vec<&mut dyn CounterStore> = stores
            .iter_mut()
            .map(|s| s as &mut dyn CounterStore)
            .collect();
        quorum.swap(0, 1);
        assert!(matches!(
            pool.begin(&mut quorum, &mut refs, [0x65; 32], 0, 1),
            Err(Error::Context)
        ));
        quorum.swap(0, 1);
        let inputs: [&[u8]; 1] = [b"reservoir"];
        let mut last_grants = None;
        for counter in 0..2 {
            let (session, grants) = pool
                .begin(&mut quorum, &mut refs, [0x65; 32], counter, 1)
                .unwrap();
            if let Some(previous) = last_grants {
                assert_ne!(grants[0].triples, previous);
            }
            last_grants = Some(grants[0].triples.clone());
            let (client, request) =
                spdz_blind(&public, &inputs, [0x65; 32], counter, &grants).unwrap();
            assert_eq!(
                client
                    .finalize(&session.evaluate(&request).unwrap())
                    .unwrap()
                    .values(),
                &[plaintext(&key, inputs[0])]
            );
        }
        assert!(matches!(
            pool.begin(&mut quorum, &mut refs, [0x65; 32], 1, 1),
            Err(Error::Counter)
        ));
        let (abandoned, _) = pool
            .begin(&mut quorum, &mut refs, [0x65; 32], 2, 1)
            .unwrap();
        drop(abandoned);
        assert!(matches!(
            pool.begin(&mut quorum, &mut refs, [0x65; 32], 3, 1),
            Err(Error::Quota)
        ));
    }

    #[test]
    fn each_quorum_of_a_committee_needs_its_own_reservoir_and_computes_the_same_function() {
        let mut servers = spdz_dkg(
            SpdzConfig::new(2, 3).unwrap(),
            [0x91; 32],
            &entropy(3, 0x92),
        )
        .unwrap();
        let public = servers[0].public().clone();
        let key = reconstruct(&[&servers[0], &servers[1]]);
        let mut stores = [Store(None), Store(None), Store(None)];
        let inputs: [&[u8]; 1] = [b"three quorums"];
        let mut counter = 0;
        // Quorums {0, 1}, {1, 2} and {0, 2}: three different sets of evaluation
        // points, hence three different sets of interpolation weights.
        for (round, absent) in [2usize, 0, 1].into_iter().enumerate() {
            let batch = [0x93 + round as u8; 32];
            let mut pool = {
                let mut quorum: Vec<_> = servers.iter_mut().filter(|s| s.party != absent).collect();
                let seeds = entropy(2, 0x96 + round as u8);
                SpdzReservoir::prepare(&mut quorum, batch, 2, 2, &seeds).unwrap()
            };

            // Every other quorum is refused before a counter is burned or a tuple spent.
            let high_water = stores.each_ref().map(|store| store.0);
            for other in (0..4).filter(|&party| party != absent) {
                let mut wrong: Vec<_> = servers.iter_mut().filter(|s| s.party != other).collect();
                let mut refs: Vec<&mut dyn CounterStore> = stores
                    .iter_mut()
                    .enumerate()
                    .filter(|(party, _)| *party != other)
                    .map(|(_, store)| store as &mut dyn CounterStore)
                    .collect();
                assert!(matches!(
                    pool.begin(&mut wrong, &mut refs, batch, counter, 1),
                    Err(Error::Context)
                ));
            }
            assert_eq!(stores.each_ref().map(|store| store.0), high_water);
            assert_eq!(pool.state.pool.remaining_pow7(), 2 * SBOXES_PER_ITEM);

            let mut quorum: Vec<_> = servers.iter_mut().filter(|s| s.party != absent).collect();
            let mut refs: Vec<&mut dyn CounterStore> = stores
                .iter_mut()
                .enumerate()
                .filter(|(party, _)| *party != absent)
                .map(|(_, store)| store as &mut dyn CounterStore)
                .collect();
            for _ in 0..2 {
                let (session, grants) = pool
                    .begin(&mut quorum, &mut refs, batch, counter, 1)
                    .unwrap();
                let (client, request) =
                    spdz_blind(&public, &inputs, batch, counter, &grants).unwrap();
                assert_eq!(
                    client
                        .finalize(&session.evaluate(&request).unwrap())
                        .unwrap()
                        .values(),
                    &[plaintext(&key, inputs[0])]
                );
                counter += 1;
            }
        }
    }

    #[test]
    fn refused_request_spends_one_reservation_and_a_failed_mac_check_the_reservoir() {
        let mut servers = spdz_dkg(
            SpdzConfig::new(2, 3).unwrap(),
            [0x71; 32],
            &entropy(3, 0x72),
        )
        .unwrap();
        let public = servers[0].public().clone();
        let key = reconstruct(&[&servers[0], &servers[1]]);
        let mut quorum: Vec<_> = servers.iter_mut().take(2).collect();
        let mut pool =
            SpdzReservoir::prepare(&mut quorum, [0x73; 32], 5, 5, &entropy(2, 0x74)).unwrap();
        let mut stores = [Store(None), Store(None)];
        let mut refs: Vec<&mut dyn CounterStore> = stores
            .iter_mut()
            .map(|s| s as &mut dyn CounterStore)
            .collect();
        let inputs: [&[u8]; 1] = [b"refusal"];
        let sid = [0x75; 32];

        // A request altered in transit is not the one the grants were issued for.
        let (session, grants) = pool.begin(&mut quorum, &mut refs, sid, 0, 1).unwrap();
        let (_, honest) = spdz_blind(&public, &inputs, sid, 0, &grants).unwrap();
        let mut altered = honest.clone();
        altered.differences[0][0][0] ^= 1;
        assert_eq!(session.evaluate(&altered).unwrap_err(), Error::Context);
        assert!(pool.state.mesh.is_some());

        // One limb masked two different ways, under a digest that matches.
        let (session, grants) = pool.begin(&mut quorum, &mut refs, sid, 1, 1).unwrap();
        let (_, honest) = spdz_blind(&public, &inputs, sid, 1, &grants).unwrap();
        let mut altered = honest.clone();
        altered.differences[0][0][0] ^= 1;
        altered.context = Context::new(
            *honest.context.key(),
            *honest.context.session(),
            1,
            1,
            request_digest(&session.pool.state.binding, &altered.differences),
        );
        assert_eq!(
            session.evaluate(&altered).unwrap_err(),
            Error::InconsistentShares
        );

        assert!(pool.state.mesh.is_some());

        // Each refusal spent its own reservation; the next session is unaffected.
        let (session, grants) = pool.begin(&mut quorum, &mut refs, sid, 2, 1).unwrap();
        let (client, request) = spdz_blind(&public, &inputs, sid, 2, &grants).unwrap();
        assert_eq!(
            client
                .finalize(&session.evaluate(&request).unwrap())
                .unwrap()
                .values(),
            &[plaintext(&key, inputs[0])]
        );
        assert_eq!(pool.state.pool.remaining_pow7(), 2 * SBOXES_PER_ITEM);
        assert!(pool.state.mesh.is_some());

        // A quorum member that deviates fails a MAC check, which spends everything.
        let (session, grants) = pool.begin(&mut quorum, &mut refs, sid, 3, 1).unwrap();
        let (_, request) = spdz_blind(&public, &inputs, sid, 3, &grants).unwrap();
        session.pool.state.key[1][0].val += Goldilocks::ONE;
        assert_eq!(session.evaluate(&request).unwrap_err(), Error::MacCheck);
        assert_eq!(pool.state.pool.remaining_pow7(), 0);
        assert!(pool.state.mesh.is_none());
        assert!(matches!(
            pool.begin(&mut quorum, &mut refs, sid, 4, 1),
            Err(Error::Quota)
        ));
    }

    /// Offline and online cost of a four-item reservoir, as a measurement:
    /// `cargo test --release -p qsag-cred -p qsag-cli --lib reservoir_cost -- --ignored --nocapture`.
    #[test]
    #[ignore = "measurement; run on demand"]
    fn reservoir_cost() {
        for (t, n, m) in [(2, 3, 2), (3, 5, 3), (3, 5, 5)] {
            let config = SpdzConfig::new(t, n).unwrap();
            let mut servers = spdz_dkg(config, [0x81; 32], &entropy(n, 0x82)).unwrap();
            let public = servers[0].public().clone();
            let mut quorum: Vec<_> = servers.iter_mut().take(m).collect();
            let started = std::time::Instant::now();
            let mut pool =
                SpdzReservoir::prepare(&mut quorum, [0x83; 32], 4, 4, &entropy(m, 0x84)).unwrap();
            std::println!(
                "({t}, {n}) quorum {m}: preprocessing four items {:?}",
                started.elapsed()
            );
            let mut stores: Vec<_> = (0..m).map(|_| Store(None)).collect();
            let mut refs: Vec<&mut dyn CounterStore> = stores
                .iter_mut()
                .map(|s| s as &mut dyn CounterStore)
                .collect();
            let inputs: [&[u8]; 1] = [b"cost"];
            for counter in 0..4 {
                let started = std::time::Instant::now();
                let (session, grants) = pool
                    .begin(&mut quorum, &mut refs, [0x85; 32], counter, 1)
                    .unwrap();
                let (client, request) =
                    spdz_blind(&public, &inputs, [0x85; 32], counter, &grants).unwrap();
                let outputs = session.evaluate(&request).unwrap();
                client.finalize(&outputs).unwrap();
                assert!(
                    pool.state.mesh.is_some(),
                    "successful item {counter} lost its OT mesh"
                );
                std::println!(
                    "({t}, {n}) quorum {m}: online evaluation {counter} {:?}",
                    started.elapsed()
                );
            }
        }
    }

    #[test]
    fn partial_store_failure_ratchets_in_memory_counters_and_prevalidates_quorum() {
        struct FailOnReserveStore(Option<u64>);
        impl CounterStore for FailOnReserveStore {
            fn high_water(&self) -> Result<Option<u64>, Error> {
                Ok(self.0)
            }
            fn reserve(&mut self, _: &[u8; 32], _: usize, _: u64, _: usize) -> Result<(), Error> {
                Err(Error::Counter)
            }
        }

        let config = SpdzConfig::new(2, 3).unwrap();
        let mut servers = spdz_dkg(config, [0x91; 32], &entropy(3, 0x92)).unwrap();

        // 1. Pre-validation catches `stores[1]` already at counter `5` BEFORE mutating `stores[0]`!
        {
            let mut quorum: Vec<&mut SpdzServer> = servers.iter_mut().take(2).collect();
            let mut s0 = Store(None);
            let mut s1 = Store(Some(5));
            let mut refs: [&mut dyn CounterStore; 2] = [&mut s0, &mut s1];
            assert_eq!(
                reserve_counters(&mut quorum, &mut refs, 5, 1),
                Err(Error::Counter)
            );
            assert_eq!(s0.0, None);
        }

        // 2. Partial store write failure on `stores[1]` after `stores[0]` persisted counter `6`
        // still ratchets BOTH `servers[0].last_counter` and `servers[1].last_counter` to `Some(6)`!
        {
            let mut quorum: Vec<&mut SpdzServer> = servers.iter_mut().take(2).collect();
            let mut s0 = Store(Some(5));
            let mut s1_fail = FailOnReserveStore(Some(5));
            let mut refs: [&mut dyn CounterStore; 2] = [&mut s0, &mut s1_fail];
            assert_eq!(
                reserve_counters(&mut quorum, &mut refs, 6, 1),
                Err(Error::Counter)
            );
            assert_eq!(s0.0, Some(6));
            assert_eq!(quorum[0].last_counter, Some(6));
            assert_eq!(quorum[1].last_counter, Some(6));

            // Replaying counter `6` against `servers[1]` now fails closed in memory!
            let mut s1_recovered = Store(Some(5));
            let mut refs_retry: [&mut dyn CounterStore; 2] = [&mut s0, &mut s1_recovered];
            assert_eq!(
                reserve_counters(&mut quorum, &mut refs_retry, 6, 1),
                Err(Error::Counter)
            );
            reserve_counters(&mut quorum, &mut refs_retry, 7, 1).unwrap();
            assert_eq!(s0.0, Some(7));
            assert_eq!(s1_recovered.0, Some(7));
        }
    }
}
