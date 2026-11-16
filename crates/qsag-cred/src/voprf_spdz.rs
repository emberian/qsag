//! Threshold oblivious PRF over Shamir sharing with SPDZ authentication:
//! any `t` of `n` servers evaluate, for `2 <= t <= n <= 64`.
//!
//! This is the second backend of [`crate::voprf`]. It computes the same function
//! `F(k, x)` (the width-12 Poseidon2 keyed sponge of [`crate::voprf::plaintext`]) and
//! returns the same [`Evaluation`], so issuance code does not care which backend ran.
//! The replicated five-server backend stays as it is; it tolerates one corruption but
//! needs all five servers online during an evaluation, so it gives no availability
//! with a server offline. This backend is the `t`-of-`n` one: any `t` servers
//! evaluate while the other `n - t` are offline. It tolerates `t - 1` corrupt servers
//! among the `t` that are online, which is a dishonest majority, so every value is
//! authenticated and nothing is released before its MAC check.
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
//! # Boundaries
//! Security is with abort; a failed session burns its counter. The protocol functions
//! take every online server's state, like `qsag_core::poseidon2_mpc`: they model
//! honest execution and detect altered shares, MACs and tuples. A networked
//! deployment must send each opened share over authenticated channels with consistent
//! broadcast and feed the received values to the same checks. Verifiability is
//! against the enrolled record, not a public proof. The Poseidon2 keyed sponge and
//! cSHAKE assumptions are those of [`crate::voprf`].

use crate::toprf_engine::hash;
use crate::voprf::{
    Context, CounterStore, Error, Evaluation, IssuanceReceiptKey, MAX_BATCH, PublicKey,
    admit_counter, finish, hash_input, input_binding,
};
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

    /// Issuer channel adapter entry point; see [`crate::voprf::Client::finalize_for_issuance`].
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
    fn take<'a, T>(
        chunks: &'a mut [Vec<Vault>],
        front: &mut usize,
        count: usize,
        remaining: fn(&Vault) -> usize,
        reserve: for<'v> fn(&'v mut Vault, usize) -> Result<&'v [T], PreprocessError>,
    ) -> Result<Vec<Vec<&'a T>>, Error> {
        let members = chunks.first().map_or(0, Vec::len);
        let mut out: Vec<Vec<&'a T>> = (0..members).map(|_| Vec::with_capacity(count)).collect();
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
                shares.extend(reserve(vault, take).map_err(preprocess_error)?);
            }
            need -= take;
        }
        if need == 0 {
            Ok(out)
        } else {
            Err(Error::Preprocessing)
        }
    }
    fn take_pow7(&mut self, count: usize) -> Result<Vec<Vec<&AuthenticatedPower7Share>>, Error> {
        Self::take(
            &mut self.chunks,
            &mut self.pow7_front,
            count,
            Vault::remaining_pow7,
            Vault::reserve_pow7,
        )
    }
    fn take_beaver(&mut self, count: usize) -> Result<Vec<Vec<&GoldilocksBeaverShare>>, Error> {
        Self::take(
            &mut self.chunks,
            &mut self.beaver_front,
            count,
            Vault::remaining_beaver,
            Vault::reserve_beaver,
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
        let binomial = [7u64, 21, 35, 35, 21, 7, 1].map(Goldilocks::from_u64_reduced);
        for gate in 0..count {
            for (share, wires) in shares.iter_mut().zip(masked.iter()) {
                *share = wires[gate].val;
            }
            let y = self
                .opening_tables
                .open(&shares, "toprf_spdz_sbox")
                .map_err(preprocess_error)?;
            // powers[k] = y^(6 - k)
            let mut powers = [Goldilocks::ONE; 7];
            for k in (0..6).rev() {
                powers[k] = powers[k + 1] * y;
            }
            for (party, wires) in out.iter_mut().enumerate() {
                let tuple = tuples[party][gate];
                // (y - r)^7 = y^7 + sum_k (-1)^(k+1) C(7, k+1) y^(6-k) r^(k+1)
                let mut acc = Wire::public(powers[0] * y, alphas[party]);
                for k in 0..7 {
                    let term = Wire {
                        val: tuple.r_pows[k],
                        mac: tuple.r_macs[k],
                    }
                    .scale(binomial[k] * powers[k]);
                    acc = if k % 2 == 0 {
                        acc.sub(term)
                    } else {
                        acc.add(term)
                    };
                }
                wires.push(acc);
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
