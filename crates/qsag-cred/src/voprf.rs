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
// Transport implementations own messages moved into exchange and must wipe them.
use crate::secret_buffer::SecretBuffer as Zeroizing;
#[cfg(test)]
use crate::secret_buffer::Wipe;

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
                    if !qsag_accel::ct::ct_eq_bytes(
                        &commitment,
                        &all_commits[dealer][ordinal * 32..(ordinal + 1) * 32],
                    ) {
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
        inputs: Vec::with_capacity(inputs.len()),
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
#[derive(Clone, PartialEq, Eq)]
pub struct Output {
    context: Context,
    components: Vec<[[u64; 5]; 4]>,
}
impl Drop for Output {
    fn drop(&mut self) {
        for item in &mut self.components {
            for wire in item {
                ct_zeroize_u64s(wire);
            }
        }
    }
}
impl fmt::Debug for Output {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("ToprfOutput(<REDACTED>)")
    }
}
impl Output {
    pub const fn context(&self) -> &Context {
        &self.context
    }
    pub fn components(&self) -> &[[[u64; 5]; 4]] {
        &self.components
    }
}
impl Server {
    pub fn public_key(&self) -> &PublicKey {
        &self.key
    }
    pub fn party(&self) -> usize {
        self.party
    }

    /// Export only this server's ten held subset seeds and local counter.
    /// The returned bytes are secret: encrypt/authenticate them for persistence
    /// and wipe them after use. Restore with the same monotonic CounterStore.
    pub fn to_secret_bytes(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(370);
        bytes.extend_from_slice(b"QTOPRF01");
        bytes.push(self.party as u8);
        bytes.extend_from_slice(&self.key.commitment);
        bytes.push(u8::from(self.last_counter.is_some()));
        bytes.extend_from_slice(&self.last_counter.unwrap_or(0).to_le_bytes());
        for i in 0..SERVERS {
            for j in i..SERVERS {
                if self.party != i && self.party != j {
                    bytes.extend_from_slice(&self.seeds[subset(i, j)]);
                }
            }
        }
        bytes
    }

    /// Restore an authenticated per-party bundle against independently pinned
    /// enrollment metadata. This codec does not authenticate its own input and
    /// cannot replace an encrypted/authenticated storage envelope.
    pub fn from_secret_bytes(
        bytes: &[u8],
        expected_key: &PublicKey,
        expected_party: usize,
    ) -> Result<Self, Error> {
        if bytes.len() != 370 || &bytes[..8] != b"QTOPRF01" {
            return Err(Error::Encoding);
        }
        let party = bytes[8] as usize;
        if party >= SERVERS
            || party != expected_party
            || !qsag_accel::ct::ct_eq_bytes(&bytes[9..41], &expected_key.commitment)
        {
            return Err(Error::Context);
        }
        let counter = u64::from_le_bytes(bytes[42..50].try_into().map_err(|_| Error::Encoding)?);
        let last_counter = match bytes[41] {
            0 if counter == 0 => None,
            1 if counter != u64::MAX => Some(counter),
            _ => return Err(Error::Encoding),
        };
        let mut seeds = Zeroizing([[0; 32]; 25]);
        let mut cursor = 50;
        for i in 0..SERVERS {
            for j in i..SERVERS {
                if party != i && party != j {
                    seeds[subset(i, j)].copy_from_slice(&bytes[cursor..cursor + 32]);
                    cursor += 32;
                }
            }
        }
        let mut key_share = Zeroizing([[0; SERVERS]; 4]);
        for i in 0..SERVERS {
            if party != i {
                let component = Zeroizing(fields(
                    &seeds[subset(i, i)],
                    b"QSAG.TOPRF.KEY.COMPONENT.V1",
                    &expected_key.commitment,
                    4,
                ));
                for lane in 0..4 {
                    key_share[lane][i] = component[lane];
                }
            }
        }
        Ok(Self {
            party,
            key: expected_key.clone(),
            seeds: *seeds,
            key_share: *key_share,
            last_counter,
        })
    }

    pub fn evaluate<T: Transport>(
        &mut self,
        request: Request,
        store: &mut dyn CounterStore,
        transport: &mut T,
    ) -> Result<Output, Error> {
        if request.party != self.party
            || !qsag_accel::ct::ct_eq_bytes(&request.context.key, &self.key.commitment)
            || request.context.items != request.inputs.len()
            || request.inputs.is_empty()
            || request.inputs.len() > MAX_BATCH
        {
            return Err(Error::Context);
        }
        // Reject `u64::MAX` and unbounded counter jumps BEFORE any network broadcast or durable
        // counter mutation so a single uncorroborated `counter = u64::MAX` packet cannot brick
        // the server's monotone high-water mark!
        if request.context.counter == u64::MAX {
            return Err(Error::Counter);
        }
        // Recover before applying the window, including the first request after
        // custody reload. Retain local burns even if a faulty store regresses.
        self.last_counter = self.last_counter.max(store.high_water()?);
        match self.last_counter {
            Some(last) => match request.context.counter.checked_sub(last) {
                Some(delta) if (1..=MAX_COUNTER_WINDOW).contains(&delta) => {}
                _ => return Err(Error::Counter),
            },
            None => {
                if request.context.counter >= MAX_COUNTER_WINDOW {
                    return Err(Error::Counter);
                }
            }
        }
        let context = request.context.digest();
        let agreement =
            transport.broadcast(hash(b"QSAG.TOPRF.START.V1", &[&context]), context.to_vec())?;
        if agreement.iter().filter(|c| c.as_slice() == context).count() < 4 {
            return Err(Error::Context);
        }
        store.reserve(
            &self.key.commitment,
            self.party,
            request.context.counter,
            request.inputs.len(),
        )?;
        self.last_counter = Some(request.context.counter);
        // Bind the client's replicated input before any key-dependent gate.
        // Unanimity among a component's four holders deliberately permits abort:
        // a majority alone could admit inconsistent malicious-client shares.
        let mut commitments = Vec::new();
        for component in 0..5 {
            commitments.extend_from_slice(&input_commitment(&request, component));
        }
        let input_commits =
            transport.broadcast(hash(b"QSAG.TOPRF.INPUT.CHECK.V1", &[&context]), commitments)?;
        let mut verified_commitments = Vec::new();
        for component in 0..5 {
            let mut expected = None;
            for (party, message) in input_commits.iter().enumerate() {
                if party != component {
                    let digest = message
                        .get(component * 32..component * 32 + 32)
                        .ok_or(Error::BadDelivery { party })?;
                    if expected.is_some_and(|e| !qsag_accel::ct::ct_eq_bytes(e, digest)) {
                        return Err(Error::InconsistentShares);
                    }
                    expected = Some(digest);
                }
            }
            verified_commitments.extend_from_slice(expected.ok_or(Error::InconsistentShares)?);
        }
        if !qsag_accel::ct::ct_eq_bytes(
            &hash(b"QSAG.TOPRF.REQUEST.V1", &[&verified_commitments]),
            &request.context.request,
        ) {
            return Err(Error::Context);
        }
        let mut states = Zeroizing(vec![[[0; 5]; 12]; request.inputs.len()]);
        for (st, input) in states.iter_mut().zip(&request.inputs) {
            st[..4].copy_from_slice(input);
            st[8..].copy_from_slice(&self.key_share);
            engine::public(&mut st[4], self.party, 1);
            engine::public(&mut st[7], self.party, 0x544f50524631);
        }
        let result = engine::Engine {
            party: self.party,
            seeds: &self.seeds,
            context,
            layer: 0,
            transport,
        }
        .permute(&mut states);
        result?;
        let components = states
            .iter()
            .map(|st| core::array::from_fn(|lane| st[lane]))
            .collect();
        Ok(Output {
            context: request.context.clone(),
            components,
        })
    }
}
/// Client-side TOPRF outputs. `Debug` names only the public context and the
/// faulty-server evidence; the outputs and receipt tags are wiped on drop.
#[derive(PartialEq, Eq)]
#[cfg_attr(test, derive(Clone))]
pub struct Evaluation {
    values: Vec<[u8; 32]>,
    pub faulty_servers: Vec<usize>,
    key: [u8; 32],
    input_digests: Vec<[u8; 32]>,
    context: Context,
    receipt_tags: Vec<[u8; 32]>,
}
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
        let digest = hash(b"QSAG.TOPRF.INPUT.BIND.V1", &[input]);
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
        let digest = hash(b"QSAG.TOPRF.INPUT.BIND.V1", &[input]);
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
impl Client {
    /// Issuer channel adapter entry point. Never expose the receipt key to a
    /// holder or sign outputs received without authenticated server identities.
    pub fn finalize_for_issuance(
        self,
        outputs: [Option<Output>; 5],
        receipt_key: &IssuanceReceiptKey,
    ) -> Result<Evaluation, Error> {
        let mut evaluation = self.finalize(outputs)?;
        evaluation.receipt_tags = evaluation
            .input_digests
            .iter()
            .zip(&evaluation.values)
            .map(|(input, output)| {
                receipt_key.tag(&evaluation.key, &evaluation.context, input, output)
            })
            .collect();
        Ok(evaluation)
    }
    /// Array indices MUST come from authenticated channel identities. Up to one
    /// bad/missing output is corrected; evidence names a channel, not a public
    /// signature that can be used as a transferable slashing receipt.
    pub fn finalize(self, outputs: [Option<Output>; 5]) -> Result<Evaluation, Error> {
        let mut faulty = Vec::new();
        let mut values = Zeroizing(Vec::with_capacity(self.context.items));
        for item in 0..self.context.items {
            let mut result = Zeroizing([0; 4]);
            for (lane, slot) in result.iter_mut().enumerate() {
                for component in 0..5 {
                    let mut candidates = Zeroizing(Vec::with_capacity(SERVERS - 1));
                    candidates.extend(outputs.iter().enumerate().filter_map(|(party, out)| {
                        let o = out.as_ref()?;
                        if party == component
                            || o.context != self.context
                            || o.components.len() != self.context.items
                        {
                            return None;
                        }
                        let value = o.components[item][lane][component];
                        (value < qsag_accel::goldilocks::GOLDILOCKS_PRIME).then_some((party, value))
                    }));
                    let correct = majority(&candidates, 3)?;
                    *slot = gl_add(*slot, correct);
                    for party in 0..5 {
                        if party != component
                            && !candidates.contains(&(party, correct))
                            && !faulty.contains(&party)
                        {
                            faulty.push(party)
                        }
                    }
                }
            }
            values.push(finish(&result[..]));
        }
        faulty.sort_unstable();
        if faulty.len() > 1 {
            return Err(Error::InconsistentShares);
        }
        Ok(Evaluation {
            values: values.into_inner(),
            faulty_servers: faulty,
            key: self.context.key,
            input_digests: self.input_digests,
            context: self.context,
            receipt_tags: Vec::new(),
        })
    }
}

impl Request {
    /// Canonical private request: 107-byte header, four 32-byte hidden salts,
    /// then 16 canonical 64-bit field limbs per item. No excluded share is sent.
    pub fn to_wire(&self) -> Vec<u8> {
        let mut bytes = Zeroizing(Vec::with_capacity(235 + 128 * self.inputs.len()));
        bytes.extend_from_slice(&self.context.key);
        bytes.extend_from_slice(&self.context.session);
        bytes.extend_from_slice(&self.context.counter.to_le_bytes());
        bytes.extend_from_slice(&(self.context.items as u16).to_le_bytes());
        bytes.push(self.party as u8);
        bytes.extend_from_slice(&self.context.request);
        for (c, salt) in self.salts.iter().enumerate() {
            if c != self.party {
                bytes.extend_from_slice(salt)
            }
        }
        for input in &self.inputs {
            for wire in input {
                for (c, &v) in wire.iter().enumerate() {
                    if c != self.party {
                        engine::put(&mut bytes, v)
                    }
                }
            }
        }
        core::mem::take(&mut *bytes)
    }
    /// The receiving channel must additionally authenticate the client and quota.
    pub fn from_wire(bytes: &[u8]) -> Result<Self, Error> {
        if bytes.len() < 235 {
            return Err(Error::Encoding);
        }
        let key = bytes[..32].try_into().map_err(|_| Error::Encoding)?;
        let session = bytes[32..64].try_into().map_err(|_| Error::Encoding)?;
        let counter = u64::from_le_bytes(bytes[64..72].try_into().map_err(|_| Error::Encoding)?);
        let items =
            u16::from_le_bytes(bytes[72..74].try_into().map_err(|_| Error::Encoding)?) as usize;
        let party = bytes[74] as usize;
        if party >= 5 || items == 0 || items > MAX_BATCH || bytes.len() != 235 + 128 * items {
            return Err(Error::Encoding);
        }
        let mut salts = Zeroizing([[0; 32]; 5]);
        let mut cursor = 107;
        for (c, salt) in salts.iter_mut().enumerate() {
            if c != party {
                salt.copy_from_slice(&bytes[cursor..cursor + 32]);
                cursor += 32;
            }
        }
        let mut inputs = Zeroizing(vec![[[0; 5]; 4]; items]);
        for input in inputs.iter_mut() {
            for wire in input {
                for (c, v) in wire.iter_mut().enumerate() {
                    if c != party {
                        *v = engine::read(bytes, &mut cursor)?
                    }
                }
            }
        }
        Ok(Self {
            context: Context {
                request: bytes[75..107].try_into().map_err(|_| Error::Encoding)?,
                key,
                session,
                counter,
                items,
            },
            party,
            inputs: core::mem::take(&mut *inputs),
            salts: *salts,
        })
    }
}

impl Output {
    /// Canonical authenticated private output, omitting the excluded component.
    pub fn to_wire(&self, party: usize) -> Result<Vec<u8>, Error> {
        if party >= 5
            || self.context.items == 0
            || self.context.items > MAX_BATCH
            || self.components.len() != self.context.items
        {
            return Err(Error::Encoding);
        }
        let mut bytes = Zeroizing(Vec::with_capacity(107 + 128 * self.context.items));
        bytes.extend_from_slice(&self.context.key);
        bytes.extend_from_slice(&self.context.session);
        bytes.extend_from_slice(&self.context.counter.to_le_bytes());
        bytes.extend_from_slice(&(self.context.items as u16).to_le_bytes());
        bytes.push(party as u8);
        bytes.extend_from_slice(&self.context.request);
        for lanes in &self.components {
            for wire in lanes {
                for (c, &v) in wire.iter().enumerate() {
                    if c != party {
                        if v >= qsag_accel::goldilocks::GOLDILOCKS_PRIME {
                            return Err(Error::Encoding);
                        }
                        engine::put(&mut bytes, v)
                    }
                }
            }
        }
        Ok(core::mem::take(&mut *bytes))
    }
    /// `party` is the authenticated sender index from enrollment.
    pub fn from_wire(bytes: &[u8], party: usize) -> Result<Self, Error> {
        if bytes.len() < 107 || party >= 5 || bytes[74] as usize != party {
            return Err(Error::Encoding);
        }
        let key = bytes[..32].try_into().map_err(|_| Error::Encoding)?;
        let session = bytes[32..64].try_into().map_err(|_| Error::Encoding)?;
        let counter = u64::from_le_bytes(bytes[64..72].try_into().map_err(|_| Error::Encoding)?);
        let items =
            u16::from_le_bytes(bytes[72..74].try_into().map_err(|_| Error::Encoding)?) as usize;
        if items == 0 || items > MAX_BATCH || bytes.len() != 107 + 128 * items {
            return Err(Error::Encoding);
        }
        let mut components = Zeroizing(vec![[[0; 5]; 4]; items]);
        let mut cursor = 107;
        for lanes in components.iter_mut() {
            for wire in lanes {
                for (c, v) in wire.iter_mut().enumerate() {
                    if c != party {
                        *v = engine::read(bytes, &mut cursor)?
                    }
                }
            }
        }
        Ok(Self {
            context: Context {
                request: bytes[75..107].try_into().map_err(|_| Error::Encoding)?,
                key,
                session,
                counter,
                items,
            },
            components: core::mem::take(&mut *components),
        })
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn private_wire_rejects_hostile_lengths_and_noncanonical_shares() {
        let context = Context {
            key: [1; 32],
            session: [2; 32],
            request: [3; 32],
            counter: 0,
            items: 1,
        };
        let request = Request {
            context: context.clone(),
            party: 0,
            inputs: vec![[[7; 5]; 4]],
            salts: [[8; 32]; 5],
        };
        let wire = request.to_wire();
        assert_eq!(wire.len(), 235 + 128);
        assert!(Request::from_wire(&wire).is_ok());
        for count in [0, MAX_BATCH as u16 + 1, u16::MAX] {
            let mut malformed = wire.clone();
            malformed[72..74].copy_from_slice(&count.to_le_bytes());
            assert!(Request::from_wire(&malformed).is_err());
        }
        let mut output = Output {
            context,
            components: vec![[[9; 5]; 4]],
        };
        assert!(core::mem::needs_drop::<Output>());
        assert_eq!(std::format!("{output:?}"), "ToprfOutput(<REDACTED>)");
        let wire = output.to_wire(0).unwrap();
        assert_eq!(wire.len(), 107 + 128);
        assert!(Output::from_wire(&wire, 0).is_ok());
        for count in [0, MAX_BATCH as u16 + 1, u16::MAX] {
            let mut malformed = wire.clone();
            malformed[72..74].copy_from_slice(&count.to_le_bytes());
            assert!(Output::from_wire(&malformed, 0).is_err());
        }
        // Reject after some private limbs have already been serialized.
        output.components[0][3][4] = qsag_accel::goldilocks::GOLDILOCKS_PRIME;
        assert_eq!(output.to_wire(0), Err(Error::Encoding));
    }
    use super::*;
    struct AbortTransport;
    impl Transport for AbortTransport {
        fn broadcast(&mut self, _: [u8; 32], _: Vec<u8>) -> Result<[Vec<u8>; 5], Error> {
            Err(Error::Transport)
        }
        fn exchange(&mut self, _: [u8; 32], _: [Vec<u8>; 5]) -> Result<[Vec<u8>; 5], Error> {
            Err(Error::Transport)
        }
    }
    struct Store;
    impl CounterStore for Store {
        fn high_water(&self) -> Result<Option<u64>, Error> {
            Ok(None)
        }
        fn reserve(&mut self, _: &[u8; 32], _: usize, _: u64, _: usize) -> Result<(), Error> {
            Ok(())
        }
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
    fn counter_store_high_water_boundary_and_u64_max_fail_closed() {
        struct FixedWaterStore(Option<u64>);
        impl CounterStore for FixedWaterStore {
            fn high_water(&self) -> Result<Option<u64>, Error> {
                Ok(self.0)
            }
            fn reserve(&mut self, _: &[u8; 32], _: usize, _: u64, _: usize) -> Result<(), Error> {
                Ok(())
            }
        }

        let key = PublicKey::test_key();
        let run_with_water = |water: Option<u64>, last: Option<u64>, counter: u64| -> Error {
            let mut server = Server {
                party: 0,
                key: key.clone(),
                seeds: [[3; 32]; 25],
                key_share: [[4; 5]; 4],
                last_counter: last,
            };
            let (_, requests) = blind(&key, &[b"item"], [9; 32], counter, [10; 32]).unwrap();
            let req = requests.into_iter().next().unwrap();
            let mut store = FixedWaterStore(water);
            server
                .evaluate(req, &mut store, &mut AbortTransport)
                .unwrap_err()
        };

        // `high_water == None` vs `high_water == Some(0)` MUST be strictly distinguished:
        // counter 0 is valid only before any burn (`None`), and rejected once 0 is burned (`Some(0)`).
        assert_eq!(run_with_water(None, None, 0), Error::Transport);
        assert_eq!(
            run_with_water(None, None, MAX_COUNTER_WINDOW - 1),
            Error::Transport
        );
        assert_eq!(
            run_with_water(None, None, MAX_COUNTER_WINDOW),
            Error::Counter
        );

        assert_eq!(run_with_water(Some(0), None, 0), Error::Counter);
        assert_eq!(run_with_water(Some(0), None, 1), Error::Transport);
        assert_eq!(
            run_with_water(Some(0), None, MAX_COUNTER_WINDOW),
            Error::Transport
        );
        assert_eq!(
            run_with_water(Some(0), None, MAX_COUNTER_WINDOW + 1),
            Error::Counter
        );

        // Store regression cannot roll back in-memory `last_counter`.
        assert_eq!(run_with_water(None, Some(0), 0), Error::Counter);
        assert_eq!(run_with_water(Some(3), Some(10), 10), Error::Counter);
        assert_eq!(run_with_water(Some(3), Some(10), 11), Error::Transport);

        // `u64::MAX - 1` and `u64::MAX` high-water marks fail closed on ALL candidate counters
        // without wrapping around to `0` or overflowing window arithmetic.
        for counter in [0, 1, u64::MAX - 2, u64::MAX - 1, u64::MAX] {
            assert_eq!(
                run_with_water(Some(u64::MAX - 1), None, counter),
                Error::Counter
            );
            assert_eq!(
                run_with_water(Some(u64::MAX), None, counter),
                Error::Counter
            );
        }
    }

    #[test]
    fn aborts_drop_secret_owners() {
        assert_eq!(
            dkg(Config, 5, [1; 32], [2; 32], &mut AbortTransport).unwrap_err(),
            Error::Encoding
        );
        assert_eq!(
            dkg(Config, 0, [1; 32], [2; 32], &mut AbortTransport).unwrap_err(),
            Error::Transport
        );
        assert!(matches!(
            blind(&PublicKey::test_key(), &[], [1; 32], 0, [2; 32]),
            Err(Error::Quota)
        ));
        let mut server = Server {
            party: 0,
            key: PublicKey::test_key(),
            seeds: [[3; 32]; 25],
            key_share: [[4; 5]; 4],
            last_counter: None,
        };
        let (_, requests) = blind(&server.key, &[b"input"], [1; 32], 0, [2; 32]).unwrap();
        let request = requests.into_iter().next().unwrap();
        assert_eq!(
            server
                .evaluate(request, &mut Store, &mut AbortTransport)
                .unwrap_err(),
            Error::Transport
        );
    }
    #[test]
    fn delivery_abort_after_partial_joint_and_seed_generation() {
        struct Delivery {
            commits: [Vec<u8>; 5],
            delivered: [Vec<u8>; 5],
        }
        impl Transport for Delivery {
            fn broadcast(&mut self, _: [u8; 32], _: Vec<u8>) -> Result<[Vec<u8>; 5], Error> {
                Ok(self.commits.clone())
            }
            fn exchange(&mut self, _: [u8; 32], _: [Vec<u8>; 5]) -> Result<[Vec<u8>; 5], Error> {
                Ok(self.delivered.clone())
            }
        }
        let session = [1; 32];
        let mut transport = Delivery {
            commits: core::array::from_fn(|_| Vec::new()),
            delivered: core::array::from_fn(|_| Vec::new()),
        };
        for dealer in 0..5 {
            for i in 0..5 {
                for j in i..5 {
                    let value = if dealer != i && dealer != j {
                        hash(
                            b"QSAG.TOPRF.DKG.SEED.V1",
                            &[&[2; 32], &session, &[dealer as u8, i as u8, j as u8]],
                        )
                    } else {
                        [0; 32]
                    };
                    transport.commits[dealer].extend_from_slice(&hash(
                        b"QSAG.TOPRF.DKG.COMMIT.V1",
                        &[&session, &[dealer as u8, i as u8, j as u8], &value],
                    ));
                    if i != 0 && j != 0 && dealer != i && dealer != j {
                        transport.delivered[dealer].extend_from_slice(&value);
                    }
                }
            }
        }
        // First subset completes; a later dealer fails after a partial joint buffer exists.
        transport.delivered[4][32] ^= 1;
        assert_eq!(
            dkg(Config, 0, session, [2; 32], &mut transport).unwrap_err(),
            Error::BadDelivery { party: 4 }
        );
        transport.delivered[4].truncate(32);
        assert_eq!(
            dkg(Config, 0, session, [2; 32], &mut transport).unwrap_err(),
            Error::BadDelivery { party: 4 }
        );
    }

    #[test]
    fn evaluation_aborts_after_secret_state_is_initialized() {
        struct GateAbort {
            step: usize,
            commits: [Vec<u8>; 5],
        }
        impl Transport for GateAbort {
            fn broadcast(&mut self, _: [u8; 32], message: Vec<u8>) -> Result<[Vec<u8>; 5], Error> {
                self.step += 1;
                if self.step == 1 {
                    Ok(core::array::from_fn(|_| message.clone()))
                } else {
                    Ok(self.commits.clone())
                }
            }
            fn exchange(&mut self, _: [u8; 32], _: [Vec<u8>; 5]) -> Result<[Vec<u8>; 5], Error> {
                Err(Error::Transport)
            }
        }
        let mut server = Server {
            party: 0,
            key: PublicKey::test_key(),
            seeds: [[3; 32]; 25],
            key_share: [[4; 5]; 4],
            last_counter: None,
        };
        let (_, requests) = blind(&server.key, &[b"input"], [1; 32], 0, [2; 32]).unwrap();
        let commits = core::array::from_fn(|p| {
            (0..5)
                .flat_map(|c| input_commitment(&requests[p], c))
                .collect()
        });
        let mut transport = GateAbort { step: 0, commits };
        assert_eq!(
            server
                .evaluate(
                    requests.into_iter().next().unwrap(),
                    &mut Store,
                    &mut transport
                )
                .unwrap_err(),
            Error::Transport
        );
        assert_eq!(transport.step, 2);
        assert_eq!(server.last_counter, Some(0));
    }

    #[test]
    fn recursive_wipe_clears_nested_buffers() {
        let mut secret = Zeroizing(vec![[[7u64; 5]; 4]; 2]);
        secret.0.wipe();
        assert!(secret.iter().flatten().flatten().all(|x| *x == 0));
    }

    #[test]
    fn client_view_simulation_and_private_wire() {
        let public = PublicKey::test_key();
        let mut histogram = [[[0usize; 8]; 2]; 5];
        for sample in 0..1024u64 {
            let entropy = hash(b"test coins", &[&sample.to_le_bytes()]);
            for choice in [0usize, 1] {
                let input = if choice == 0 {
                    b"low entropy input A"
                } else {
                    b"low entropy input B"
                };
                let (_, requests) = blind(&public, &[input], [11; 32], sample, entropy).unwrap();
                for (party, request) in requests.iter().enumerate() {
                    assert_eq!(request.salts[party], [0; 32]);
                    assert_eq!(request.inputs[0][0][party], 0);
                    let observed = request.inputs[0][0][if party == 4 { 0 } else { 4 }];
                    histogram[party][choice][(observed & 7) as usize] += 1;
                    let bytes = request.to_wire();
                    assert_eq!(bytes.len(), 363);
                    assert_eq!(Request::from_wire(&bytes).unwrap().to_wire(), bytes);
                    assert!(Request::from_wire(&bytes[..362]).is_err());
                    let mut noncanonical = bytes;
                    noncanonical[235..243]
                        .copy_from_slice(&qsag_accel::goldilocks::GOLDILOCKS_PRIME.to_le_bytes());
                    assert!(Request::from_wire(&noncanonical).is_err());
                }
            }
        }
        // Coarse, deterministic statistical smoke check, not a security proof.
        for hist in histogram {
            for (a, b) in hist[0].iter().zip(hist[1]) {
                assert!(a.abs_diff(b) < 80);
            }
        }
        // For the server missing the residual component, identically coupled
        // coins give exactly the simulator's private shares for two inputs.
        // The public salted commitment is computationally hiding, not identical.
        let (_, a) = blind(&public, &[b"a"], [12; 32], 0, [13; 32]).unwrap();
        let (_, b) = blind(&public, &[b"b"], [12; 32], 0, [13; 32]).unwrap();
        assert_eq!(a[4].inputs, b[4].inputs);
        assert_eq!(a[4].salts, b[4].salts);
        assert_ne!(a[4].context.request, b[4].context.request);
    }
    #[test]
    fn basis_attack_fails_even_given_raw_output_limbs() {
        let evaluate = |input: [u64; 4]| {
            let mut st = [0; 12];
            st[..4].copy_from_slice(&input);
            st[4] = 1;
            st[7] = 0x544f50524631;
            st[8..].copy_from_slice(&[13, 17, 23, 29]);
            poseidon2_perm12(&mut st);
            [st[0], st[1], st[2], st[3]]
        };
        let a = evaluate([1, 0, 0, 0]);
        let b = evaluate([0, 1, 0, 0]);
        for coefficient in 2..66 {
            let target = evaluate([coefficient, 7, 0, 0]);
            let prediction = core::array::from_fn(|i| {
                gl_add(
                    qsag_accel::goldilocks::gl_mul(coefficient, a[i]),
                    qsag_accel::goldilocks::gl_mul(7, b[i]),
                )
            });
            assert_ne!(target, prediction);
        }
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
}
