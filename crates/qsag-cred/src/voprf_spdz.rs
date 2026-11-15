//! Threshold oblivious PRF over Shamir sharing with SPDZ authentication:
//! any `t` of `n` servers evaluate, for `2 <= t <= n <= 64`.
//!
//! This is the second backend of [`crate::voprf`]. It computes the same function
//! `F(k, x)` (the width-12 Poseidon2 keyed sponge of [`crate::voprf::plaintext`]) and
//! returns the same [`Evaluation`], so issuance code does not care which backend ran.
//! The replicated five-server backend stays as it is; it needs four of five servers
//! online and tolerates one corruption. This backend tolerates `t - 1` corrupt servers
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
//!    `a * b = c`. A server that shifts `a` must guess `b` (probability `2^-64`).
//!    Each input limb is masked twice, with the `a` of two independent triples, and
//!    the two differences `x - a` are published in the request.
//! 3. [`SpdzSession::evaluate`]: the servers form `[x] = [a] + (x - a)` from both
//!    masks and open the difference of the two under a MAC check; it must be zero.
//!    Shifting the client's input therefore needs two independent guesses (`2^-128`),
//!    and the opened difference depends only on the shifts, never on `x`. The
//!    permutation runs on authenticated shares; every S-box opens `x + r` for a fresh
//!    tuple. Before anything leaves, all those openings pass one batched MAC check.
//!    Each output limb is then opened twice, masked by two more client masks.
//! 4. [`SpdzClient::finalize`]: all `m` servers must report identical masked outputs
//!    (an honest server reports only MAC-checked values); the two unmaskings of every
//!    limb must agree.
//!
//! # Why the tuples are generated per session
//! Tuples staged at enrollment would be Shamir-shared among all `n` and usable by any
//! quorum, but two quorums that share no honest server could be handed the same tuple
//! for different inputs. Both open `x + r` at every S-box, the difference reveals
//! `x_1 - x_2` on internal wires, and that recovers the key. A per-server cursor
//! cannot prevent it. Session tuples cost the online quorum the preprocessing time
//! (measured: about 45 s per evaluated item on 24 cores, almost independent of `m`).
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
    OtMesh, PartyPrivateRng, PreprocessError, PreprocessedPoseidonPartyVault,
    commit_and_open_spdz_goldilocks_batch_quorum, open_and_check_degree_goldilocks,
    run_dealerless_pi_pow7_with_alpha, spdz_authenticate_goldilocks_batch_ext2,
    spdz_setup_alpha_goldilocks,
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
        // A shifted mask passes only if the shift was chosen knowing the other factor.
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
    fn new(quorum: usize) -> Self {
        Self {
            shares: vec![Vec::new(); quorum],
            macs: vec![Vec::new(); quorum],
        }
    }
    fn record(&mut self, wires: &[Vec<Wire>]) {
        for ((shares, macs), wires) in self.shares.iter_mut().zip(&mut self.macs).zip(wires) {
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
    rngs: Vec<PartyPrivateRng>,
    vaults: Vec<PreprocessedPoseidonPartyVault>,
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
        self.key.secret_wipe();
        self.masks.secret_wipe();
    }
}

impl SpdzSession {
    fn alphas(&self) -> SecretBuffer<Vec<GoldilocksExt2>> {
        SecretBuffer(
            self.vaults
                .iter()
                .map(|vault| vault.mac_alpha_share)
                .collect(),
        )
    }

    /// Open a batch of wires under the SPDZ MAC check.
    fn checked_open(
        &mut self,
        phase: &'static str,
        shares: &[Vec<Goldilocks>],
        macs: &[Vec<GoldilocksExt2>],
    ) -> Result<Vec<Goldilocks>, Error> {
        let alphas = self.alphas();
        commit_and_open_spdz_goldilocks_batch_quorum(
            &self.sid,
            phase,
            self.threshold,
            &self.points,
            shares,
            macs,
            &alphas,
            &mut self.rngs,
        )
        .map_err(preprocess_error)
    }

    fn checked_open_wires(
        &mut self,
        phase: &'static str,
        wires: &[Vec<Wire>],
    ) -> Result<Vec<Goldilocks>, Error> {
        let mut pending = Pending::new(wires.len());
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
        let sboxes = SBOXES_PER_ITEM * items;
        Self::begin_with_sboxes(quorum, stores, session, counter, items, entropy, sboxes)
    }

    /// [`Self::begin`] with an explicit S-box tuple budget.
    fn begin_with_sboxes(
        quorum: &mut [&mut SpdzServer],
        stores: &mut [&mut dyn CounterStore],
        session: [u8; 32],
        counter: u64,
        items: usize,
        entropy: &[[u8; 32]],
        sboxes: usize,
    ) -> Result<(Self, Vec<SpdzGrant>), Error> {
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
        if stores.len() != m || entropy.len() != m {
            return Err(Error::Encoding);
        }
        if quorum.iter().any(|server| server.public != public) {
            return Err(Error::Context);
        }
        if items == 0 || items > MAX_BATCH {
            return Err(Error::Quota);
        }
        let key_commitment = public.public_key().commitment();
        for (server, store) in quorum.iter_mut().zip(stores.iter()) {
            admit_counter(&mut server.last_counter, &**store, counter)?;
        }
        for (server, store) in quorum.iter_mut().zip(stores.iter_mut()) {
            store.reserve(&key_commitment, server.party, counter, items)?;
            server.last_counter = Some(counter);
        }

        let binding = grant_binding(&key_commitment, &session, counter, items, &parties);
        let sid = hash(b"QSAG.TOPRF.SPDZ.SESSION.V1", &[&binding]);
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
        let mut rngs = party_rngs(b"QSAG.TOPRF.SPDZ.RNG.V1", &sid, &hedged);
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
        let mut mesh = OtMesh::try_establish(sid, &mut rngs).map_err(preprocess_error)?;

        let mut this = Self {
            threshold,
            sid,
            binding,
            key_commitment,
            session,
            counter,
            items,
            parties,
            points,
            rngs,
            vaults: Vec::new(),
            key: quorum.iter().map(|server| server.key).collect(),
            masks: Vec::new(),
        };

        // Check the stored key shares against their MACs before the long step: each
        // limb is opened under a fresh authenticated mask.
        let check_sid = hash(b"QSAG.TOPRF.SPDZ.KEYCHECK.V1", &[&sid]);
        this.vaults = run_dealerless_pi_pow7_with_alpha(
            check_sid,
            threshold,
            &this.points,
            0,
            LANES,
            0,
            &alpha_contribs,
            &alpha_shares,
            &mut mesh,
            &mut this.rngs,
        )
        .map_err(preprocess_error)?;
        let mut blinded = SecretBuffer(vec![Vec::with_capacity(LANES); m]);
        for ((wires, vault), key) in blinded.iter_mut().zip(&mut this.vaults).zip(&this.key) {
            let triples = vault.reserve_beaver(LANES).map_err(preprocess_error)?;
            for (limb, triple) in key.iter().zip(triples) {
                wires.push(limb.add(Wire {
                    val: triple.a,
                    mac: triple.a_mac,
                }));
            }
        }
        this.checked_open_wires("toprf_spdz_key_share", &blinded)?;

        this.vaults = run_dealerless_pi_pow7_with_alpha(
            sid,
            threshold,
            &this.points,
            sboxes,
            MASKS_PER_ITEM * items,
            0,
            &alpha_contribs,
            &alpha_shares,
            &mut mesh,
            &mut this.rngs,
        )
        .map_err(preprocess_error)?;
        let mut grants = Vec::with_capacity(m);
        for (index, vault) in this.vaults.iter_mut().enumerate() {
            let triples = vault
                .reserve_beaver(MASKS_PER_ITEM * items)
                .map_err(preprocess_error)?;
            this.masks.push(
                triples
                    .iter()
                    .map(|triple| Wire {
                        val: triple.a,
                        mac: triple.a_mac,
                    })
                    .collect(),
            );
            grants.push(SpdzGrant {
                party: this.parties[index],
                binding,
                triples: triples
                    .iter()
                    .map(|triple| [triple.a, triple.b, triple.c])
                    .collect(),
            });
        }
        Ok((this, grants))
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
        let alphas = self.alphas();
        let mut tuples = Vec::with_capacity(m);
        let mut masked = SecretBuffer(vec![Vec::with_capacity(count); m]);
        for ((vault, wires), out) in self.vaults.iter_mut().zip(inputs).zip(masked.iter_mut()) {
            let reserved = vault.reserve_pow7(count).map_err(preprocess_error)?;
            for (wire, tuple) in wires.iter().zip(reserved) {
                out.push(wire.add(Wire {
                    val: tuple.r_pows[0],
                    mac: tuple.r_macs[0],
                }));
            }
            tuples.push(reserved);
        }
        pending.record(&masked);
        let mut shares = SecretBuffer(vec![Goldilocks::ZERO; m]);
        let mut out = SecretBuffer(vec![Vec::with_capacity(count); m]);
        let binomial = [7u64, 21, 35, 35, 21, 7, 1].map(Goldilocks::from_u64_reduced);
        for gate in 0..count {
            for (share, wires) in shares.iter_mut().zip(masked.iter()) {
                *share = wires[gate].val;
            }
            let y = open_and_check_degree_goldilocks(
                self.threshold,
                &self.points,
                &shares,
                "toprf_spdz_sbox",
            )
            .map_err(preprocess_error)?;
            // powers[k] = y^(6 - k)
            let mut powers = [Goldilocks::ONE; 7];
            for k in (0..6).rev() {
                powers[k] = powers[k + 1] * y;
            }
            for (party, wires) in out.iter_mut().enumerate() {
                let tuple = &tuples[party][gate];
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
        let alphas = self.alphas();
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
                        .zip(alphas.iter())
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
        self.check_request(request)?;
        let context = &request.context;
        let m = self.parties.len();
        let alphas = self.alphas();
        let mut differences = Vec::with_capacity(self.items);
        for item in &request.differences {
            let mut lanes = [[Goldilocks::ZERO; 2]; LANES];
            for (lane, pair) in lanes.iter_mut().zip(item) {
                for (value, &raw) in lane.iter_mut().zip(pair) {
                    *value = Goldilocks::from_canonical(raw).map_err(|_| Error::Encoding)?;
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
        let opened = self.checked_open_wires("toprf_spdz_input_bind", &bound)?;
        if opened.iter().any(|value| *value != Goldilocks::ZERO) {
            return Err(Error::InconsistentShares);
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
        let mut pending = Pending::new(m);
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
        let config = SpdzConfig::new(3, 64).unwrap();
        let servers = spdz_dkg(config, [3; 32], &entropy(64, 0x41)).unwrap();
        std::println!("(3, 64) enrollment: {:?}", started.elapsed());
        let public = servers[0].public().clone();
        assert_eq!(public.to_bytes().len(), 42 + 32 * 64);
        // Any three shares define the same key, and every share matches the record.
        let key = reconstruct(&[&servers[0], &servers[1], &servers[2]]);
        assert_eq!(key, reconstruct(&[&servers[7], &servers[30], &servers[63]]));
        for server in &servers {
            let bytes = server.to_secret_bytes();
            SpdzServer::from_secret_bytes(&bytes, &public, server.party).unwrap();
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
}
