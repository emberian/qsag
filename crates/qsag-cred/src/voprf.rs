//! Threshold oblivious PRF with replicated, actively checked arithmetic.
//!
//! # Construction and security boundary
//! The supported configuration is exactly threshold t=2, n=5, with at most
//! t'=1 statically corrupt server. Other configurations are rejected. Private,
//! authenticated point-to-point channels and a consistent authenticated
//! broadcast are required; the transport must separate sessions and phases.
//! This intentionally uses replicated additive sharing instead of Shamir:
//! component i is held by the four servers other than i. Any one server misses
//! one uniform component. Two servers can reconstruct. Multiplication expands
//! into 25 terms. The five diagonal terms are local to their component holders.
//! Each of the 20 ordered cross terms is known to three servers; they send it,
//! masked by a fresh element of a subset seed the recipient does not hold, to
//! the one component holder that cannot compute it. That recipient decodes by
//! majority (for large layers: two vectors and one digest). Masks are bound to
//! the session, counter, layer, gate and pair. See `toprf_engine` for details.
//! With one corrupt party, every decoded term equals the honest term. Induction
//! over the circuit establishes correctness, including under arbitrary local
//! key/input replacement. Output components are likewise majority decoded.
//! Transport omissions may cause abort; guaranteed availability is not claimed.
//!
//! Dealerless setup commits each party's independent seed contributions before
//! delivering them privately to each three/four-member subset. Every recipient
//! checks delivery against the consistent broadcast. The public commitment to
//! all contributions binds the resulting subset seeds and the derived key.
//! No server endpoint receives every subset seed or every key component. Setup aborts
//! on bad delivery. Seed openings must remain on their private subset channels.
//!
//! F(k,x) initializes a width-12 Poseidon2 keyed sponge with four hashed input
//! limbs in the rate, fixed padding/domain limbs, and four key limbs in the
//! capacity. It returns four rate limbs after permutation, hashed with cSHAKE.
//! Security assumes the repository's Poseidon2 instance is a secure keyed
//! sponge, cSHAKE is a quantum-secure PRF/commitment, and private entropy is
//! fresh. This is not a claim of a standardized or independently audited OPRF.
//! With independently uniform sharing coins the underlying sharing privacy is
//! information-theoretic. This implementation expands both client coins and
//! resharing coins with cSHAKE, so the full simulation is computational.
//! A corrupt server can compute every term and mask it is entitled to. Each
//! value it receives is a term masked by a fresh element from the one seed it
//! does not hold, and each output component it holds carries one such mask.
//! Thus its view can be simulated from its input/key shares and public metadata.
//! Unlike the replaced linear map, multiplication of input and key occurs in
//! secret shared nonlinear layers; two chosen basis queries do not expose a
//! linear evaluation oracle. Clients receive only the final output shares.
//!
//! Key binding is honest-majority verifiability against an enrolled DKG root,
//! not a publicly transferable NIZK. An authenticated output must be associated
//! with its actual sender; passing attacker-invented sender identities violates
//! the API's channel contract. Persistent counter reservation precedes all
//! evaluation messages and burns aborted evaluations. Outputs also bind the
//! root of the salted request components, preventing cross-input relabeling.
//! Restore custody only with
//! the same monotonic store. Every batch consumes one counter and quota equal to
//! its item count. Session IDs and counters enter every resharing domain.
use crate::toprf_engine::{self as engine, Wire, fields, hash, majority, subset};
use alloc::{vec, vec::Vec};
use core::fmt;
use qsag_accel::{
    ct::{ct_zeroize_bytes, ct_zeroize_u64s},
    goldilocks::{gl_add, gl_sub},
    poseidon2::poseidon2_perm12,
};
// Owned secret containers are wiped on success, error, and unwinding. Transport
// implementations own messages moved into exchange and must wipe those buffers.
trait Wipe {
    fn wipe(&mut self);
}
impl Wipe for u8 {
    fn wipe(&mut self) {
        *self = 0;
    }
}
impl Wipe for u64 {
    fn wipe(&mut self) {
        *self = 0;
    }
}
impl<T: Wipe, const N: usize> Wipe for [T; N] {
    fn wipe(&mut self) {
        for item in self {
            item.wipe();
        }
    }
}
impl<T: Wipe> Wipe for Vec<T> {
    fn wipe(&mut self) {
        for item in self {
            item.wipe();
        }
    }
}
struct Zeroizing<T: Wipe>(T);
impl<T: Wipe> core::ops::Deref for Zeroizing<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.0
    }
}
impl<T: Wipe> core::ops::DerefMut for Zeroizing<T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.0
    }
}
impl<T: Wipe> Drop for Zeroizing<T> {
    fn drop(&mut self) {
        self.0.wipe();
        core::hint::black_box(&mut self.0);
    }
}

pub const SERVERS: usize = 5;
pub const MAX_BATCH: usize = 64;
/// Maximum forward step permitted per monotone counter reservation (`counter = u64::MAX` is
/// unconditionally rejected so no single request can exhaust the 64-bit counter space).
pub const MAX_COUNTER_WINDOW: u64 = 64;
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    UnsupportedThreshold,
    Encoding,
    Transport,
    BadDelivery { party: usize },
    InconsistentShares,
    Context,
    Counter,
    Quota,
}
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}
impl core::error::Error for Error {}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Config;
impl Config {
    pub fn new(t: usize, n: usize) -> Result<Self, Error> {
        if (t, n) == (2, 5) {
            Ok(Self)
        } else {
            Err(Error::UnsupportedThreshold)
        }
    }
}
/// Implementations must provide confidential authenticated delivery, including
/// local loopback, and consistent authenticated broadcast. Missing peers may
/// return Transport; messages must not cross phases. Sender indices are fixed
/// by enrollment, never supplied by a received payload. Implementations own the
/// outgoing buffers and must wipe private payloads on success and failure.
pub trait Transport {
    fn exchange(
        &mut self,
        phase: [u8; 32],
        outgoing: [Vec<u8>; SERVERS],
    ) -> Result<[Vec<u8>; SERVERS], Error>;
    fn broadcast(&mut self, phase: [u8; 32], message: Vec<u8>)
    -> Result<[Vec<u8>; SERVERS], Error>;
}
/// Atomic durable reservation: reject counter <= the stored high-water mark,
/// and enforce the enrolled quota (charged by `items`). Never roll back on abort.
pub trait CounterStore {
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
pub struct Server {
    party: usize,
    key: PublicKey,
    seeds: [[u8; 32]; 25],
    key_share: [Wire; 4],
    last_counter: Option<u64>,
}
impl fmt::Debug for Server {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("ToprfServer(<REDACTED>)")
    }
}
impl Drop for Server {
    fn drop(&mut self) {
        for s in &mut self.seeds {
            ct_zeroize_bytes(s)
        }
        for s in &mut self.key_share {
            ct_zeroize_u64s(s)
        }
    }
}
/// Independent server setup; `entropy` is private CSPRNG output, not a public
/// ceremony seed. All servers must use the same session and enrolled indices.
pub fn dkg<T: Transport>(
    _: Config,
    party: usize,
    session: [u8; 32],
    entropy: [u8; 32],
    transport: &mut T,
) -> Result<Server, Error> {
    let entropy = Zeroizing(entropy);
    if party >= 5 {
        return Err(Error::Encoding);
    }
    let mut contributions = Zeroizing([[0u8; 32]; 25]);
    let mut commits = Vec::new();
    for i in 0..5 {
        for j in i..5 {
            let s = subset(i, j);
            if party != i && party != j {
                contributions[s] = hash(
                    b"QSAG.TOPRF.DKG.SEED.V1",
                    &[&*entropy, &session, &[party as u8, i as u8, j as u8]],
                );
            }
            commits.extend_from_slice(&hash(
                b"QSAG.TOPRF.DKG.COMMIT.V1",
                &[
                    &session,
                    &[party as u8, i as u8, j as u8],
                    &contributions[s],
                ],
            ));
        }
    }
    let all_commits =
        transport.broadcast(hash(b"QSAG.TOPRF.DKG.COMMITS.V1", &[&session]), commits)?;
    if all_commits.iter().any(|c| c.len() != 15 * 32) {
        return Err(Error::Encoding);
    }
    let mut outgoing = Zeroizing(core::array::from_fn::<_, 5, _>(|_| {
        Vec::with_capacity(15 * 32)
    }));
    for i in 0..5 {
        for j in i..5 {
            if party == i || party == j {
                continue;
            }
            for (recipient, msg) in outgoing.iter_mut().enumerate() {
                if recipient != i && recipient != j {
                    msg.extend_from_slice(&contributions[subset(i, j)]);
                }
            }
        }
    }
    let delivered = Zeroizing(transport.exchange(
        hash(b"QSAG.TOPRF.DKG.DELIVER.V1", &[&session]),
        core::mem::take(&mut *outgoing),
    )?);
    let mut seeds = Zeroizing([[0; 32]; 25]);
    let mut cursors = [0usize; 5];
    let mut ordinal = 0;
    for i in 0..5 {
        for j in i..5 {
            if party != i && party != j {
                let mut joint = Zeroizing(Vec::with_capacity(128));
                for dealer in 0..5 {
                    if dealer == i || dealer == j {
                        continue;
                    }
                    let start = cursors[dealer];
                    cursors[dealer] += 32;
                    let value = delivered[dealer]
                        .get(start..start + 32)
                        .ok_or(Error::BadDelivery { party: dealer })?;
                    let commitment = hash(
                        b"QSAG.TOPRF.DKG.COMMIT.V1",
                        &[&session, &[dealer as u8, i as u8, j as u8], value],
                    );
                    if commitment != all_commits[dealer][ordinal * 32..(ordinal + 1) * 32] {
                        return Err(Error::BadDelivery { party: dealer });
                    }
                    joint.extend_from_slice(value);
                }
                seeds[subset(i, j)] = hash(
                    b"QSAG.TOPRF.DKG.JOINT.V1",
                    &[&session, &[i as u8, j as u8], &joint[..]],
                );
            }
            ordinal += 1;
        }
    }
    let mut binding = Vec::from(session);
    for c in &all_commits {
        binding.extend_from_slice(c)
    }
    let key = PublicKey {
        commitment: hash(b"QSAG.TOPRF.KEY.V1", &[&binding]),
    };
    let mut key_share = Zeroizing([[0; 5]; 4]);
    for i in 0..5 {
        if party != i {
            let component = Zeroizing(fields(
                &seeds[subset(i, i)],
                b"QSAG.TOPRF.KEY.COMPONENT.V1",
                &key.commitment,
                4,
            ));
            for lane in 0..4 {
                key_share[lane][i] = component[lane]
            }
        }
    }
    Ok(Server {
        party,
        key,
        seeds: *seeds,
        key_share: *key_share,
        last_counter: None,
    })
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
    fn digest(&self) -> [u8; 32] {
        hash(
            b"QSAG.TOPRF.REQUEST.CONTEXT.V1",
            &[&self.base_digest(), &self.request],
        )
    }
    fn base_digest(&self) -> [u8; 32] {
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
/// Deliver only to the indexed server on its private client channel.
pub struct Request {
    context: Context,
    party: usize,
    inputs: Vec<[Wire; 4]>,
    salts: [[u8; 32]; 5],
}
fn input_commitment(request: &Request, component: usize) -> [u8; 32] {
    let mut payload = Zeroizing(Vec::with_capacity(request.inputs.len() * 32));
    for input in &request.inputs {
        for lane in input {
            engine::put(&mut payload, lane[component]);
        }
    }
    hash(
        b"QSAG.TOPRF.INPUT.COMMIT.V1",
        &[
            &request.context.base_digest(),
            &[component as u8],
            &request.salts[component],
            &payload[..],
        ],
    )
}
impl fmt::Debug for Request {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("ToprfRequest(<REDACTED>)")
    }
}
impl Drop for Request {
    fn drop(&mut self) {
        for salt in &mut self.salts {
            ct_zeroize_bytes(salt)
        }
        for input in &mut self.inputs {
            for wire in input {
                ct_zeroize_u64s(wire)
            }
        }
    }
}
pub struct Client {
    context: Context,
    input_digests: Vec<[u8; 32]>,
}
pub fn hash_input(input: &[u8]) -> [u64; 4] {
    let seed = hash(b"QSAG.TOPRF.INPUT.V1", &[input]);
    fields(&seed, b"QSAG.TOPRF.INPUT.FIELD.V1", b"", 4)
        .try_into()
        .expect("four limbs")
}
/// Reference F, useful for test vectors. Custody never reconstructs this key.
pub fn plaintext(key: &[u64; 4], input: &[u8]) -> [u8; 32] {
    let mut st = Zeroizing([0; 12]);
    st[..4].copy_from_slice(&hash_input(input));
    st[4] = 1;
    st[7] = 0x544f50524631;
    st[8..].copy_from_slice(key);
    poseidon2_perm12(&mut st);
    finish(&st[..4])
}
fn finish(output: &[u64]) -> [u8; 32] {
    let mut bytes = Zeroizing(Vec::with_capacity(output.len() * 8));
    for &v in output {
        engine::put(&mut bytes, v)
    }
    hash(b"QSAG.TOPRF.OUTPUT.V1", &[&bytes[..]])
}
pub fn blind(
    key: &PublicKey,
    inputs: &[&[u8]],
    session: [u8; 32],
    counter: u64,
    entropy: [u8; 32],
) -> Result<(Client, [Request; 5]), Error> {
    let entropy = Zeroizing(entropy);
    if inputs.is_empty() || inputs.len() > MAX_BATCH {
        return Err(Error::Quota);
    }
    let mut context = Context {
        request: [0; 32],
        key: key.commitment,
        session,
        counter,
        items: inputs.len(),
    };
    let mut requests = core::array::from_fn(|party| Request {
        context: context.clone(),
        party,
        inputs: Vec::new(),
        salts: [[0; 32]; 5],
    });
    let random = Zeroizing(fields(
        &entropy,
        b"QSAG.TOPRF.CLIENT.SHARE.V1",
        &context.digest(),
        inputs.len() * 16,
    ));
    for (party, request) in requests.iter_mut().enumerate() {
        for (component, salt) in request.salts.iter_mut().enumerate() {
            if party != component {
                *salt = hash(
                    b"QSAG.TOPRF.CLIENT.SALT.V1",
                    &[&*entropy, &context.digest(), &[component as u8]],
                );
            }
        }
    }
    for (item, input) in inputs.iter().enumerate() {
        let value = Zeroizing(hash_input(input));
        let mut wires = Zeroizing([[0; 5]; 4]);
        for lane in 0..4 {
            let r = &random[item * 16 + lane * 4..item * 16 + lane * 4 + 4];
            wires[lane][..4].copy_from_slice(r);
            wires[lane][4] = r.iter().fold(value[lane], |a, &b| gl_sub(a, b));
        }
        for (party, req) in requests.iter_mut().enumerate() {
            let mut local = Zeroizing(*wires);
            for wire in local.iter_mut() {
                wire[party] = 0
            }
            req.inputs.push(*local);
        }
    }
    let mut commitments = Vec::new();
    for component in 0..5 {
        let holder = if component == 0 { 1 } else { 0 };
        commitments.extend_from_slice(&input_commitment(&requests[holder], component));
    }
    context.request = hash(b"QSAG.TOPRF.REQUEST.V1", &[&commitments]);
    for request in &mut requests {
        request.context = context.clone();
    }

    Ok((
        Client {
            context,
            input_digests: inputs
                .iter()
                .map(|input| hash(b"QSAG.TOPRF.INPUT.BIND.V1", &[input]))
                .collect(),
        },
        requests,
    ))
}
/// Output arrives over the server's authenticated private channel to the client.
/// Fields are private so callers deserialize exclusively via [`Output::from_wire`] rather than
/// mutating unauthenticated components in memory.
#[derive(Clone, Debug, PartialEq, Eq)]
