//! Dealerless root provisioning and child rekey for the linear module.
//!
//! # Model
//!
//! Committee `(t, n)` with `n >= 2t - 1` (enforced by
//! [`crate::seeds::CommitteeConfig`]), at most `t - 1` static malicious
//! corruptions, authenticated consistent broadcast, security with abort. All
//! `n` custodians take part in a rekey. Every message below is a broadcast;
//! the only private messages of the whole construction are in the one-time
//! subset-seed ceremony.
//!
//! # Protocol
//!
//! Shares are degree `t - 1` Shamir shares over `F_q`, `q = 8,380,417`.
//! Pseudorandom sharings come non-interactively from the subset seeds: the
//! share of custodian `i` is `sum over subsets A containing i of
//! PRF(k_A) * f_A(x_i)`, where `f_A` has degree `t - 1`, `f_A(0) = 1`, and
//! vanishes at the points of the custodians outside `A`. Multiplying each
//! term by `x^j`, `1 <= j <= t - 1`, gives pseudorandom degree `2t - 2`
//! sharings of zero.
//!
//! 1. **Hello.** Each custodian broadcasts a fresh nonce and a commitment to
//!    a coin seed. For a root or hardened child it also broadcasts, for every
//!    subset it belongs to, the public image `A*tau_1 + tau_2` of that
//!    subset's short tweak `tau_A = CBD2(PRF(k_A, path))`; all holders of a
//!    subset must publish the same image, and every subset has an honest
//!    holder. The secret tweak is the sum of the subset tweaks and is never
//!    assembled. A non-hardened child adds the public chain-code tweak.
//! 2. **Products.** With the session key (a hash of the whole hello
//!    transcript) the custodians derive fresh MAC-key sharings `alpha_l`
//!    (seven lanes), masks `b_k`, and for every multiplication a pair
//!    `([r]_{t-1}, [r]_{2t-2})`. Each broadcasts `d_i = x_i*y_i + R_i` for
//!    every product; `d` is interpolated and the product share is
//!    `d - r_i`. Products: `alpha_l * s_c` for all 2,048 child coefficients,
//!    `alpha_l * b_k`, and for a child `alpha^parent_l * b'_k`. A corrupt
//!    custodian can add a chosen error to any product, nothing else.
//! 3. **Coin.** The coin seeds are opened; with the product transcript they
//!    define public vectors `chi_k`, `k < 7`, unknown when the errors were
//!    fixed.
//! 4. **Masked opening.** `rho_k = sum_c chi_k[c] * s_c - b_k` is opened by
//!    broadcasting shares, which must lie on one degree `t - 1` polynomial.
//!    The honest shares alone determine that polynomial.
//! 5. **Zero-test commit**, 6. **zero-test open.** Each custodian commits to,
//!    then opens, its shares of
//!    `w_{l,k} = sum_c chi_k[c] * m_{l,c} - m'_{l,k} - rho_k * alpha_l`.
//!    The shares must lie on one degree `t - 1` polynomial that is zero at 0.
//!    For a child the same test runs on the parent's MACs under the parent
//!    key, so the parent sharing is authenticated before the child is released.
//!
//! # Soundness and privacy
//!
//! If any child MAC in lane `l` differs from `alpha_l * s_c` on the sharing
//! defined by the honest custodians, `w_{l,k}(0) = <chi_k, e> - e'_k` with
//! `e != 0` fixed before `chi_k` was sampled, so each of the seven
//! independent tests passes with probability `1/q`: a faulted lane is
//! released with probability at most `q^-7 < 2^-160.99`, and by a union
//! bound over the seven child lanes and seven parent lanes any fault escapes
//! with probability below `2^-157.1`, plus the collision, commitment and PRF
//! advantages against cSHAKE256.
//!
//! An abort reveals nothing: product broadcasts are masked by fresh
//! degree `2t - 2` sharings, `rho_k` by `b_k`, and the opened `w` shares of
//! the honest custodians are a function of `w(0)` (zero, or an error the
//! adversary chose) and the corrupt custodians' own shares. No MAC key is
//! exposed by a failed rekey, so a failed rekey does not retire the family.

use crate::seeds::CustodianSet;
use super::*;
use crate::erase::SecretWords;
use crate::inventory::RekeyFault;
use crate::seeds::CustodianSeeds;
use qsag_accel::ct::ct_eq_bytes;
use qsag_accel::keccak::{Shake256, commit_mpc_broadcast, finalize_cshake256, init_cshake256};

/// Independent sacrifice repetitions per MAC lane: soundness error `q^-7`.
pub const REKEY_SACRIFICE_REPS: usize = 7;
/// Broadcast rounds of one rekey session.
pub const REKEY_BROADCAST_ROUNDS: usize = 6;

const REPS: usize = REKEY_SACRIFICE_REPS;
const COEFFS: usize = MODULE_SECRET_L * MODULE_N;
const CHILD_PRODUCTS: usize = SPDZ_LANES * COEFFS;
const CHECK_PRODUCTS: usize = SPDZ_LANES * REPS;

fn abort<T>(fault: RekeyFault) -> Result<T, HdError> {
    Err(HdError::RekeyAborted(fault))
}

/// Squeeze 192 bits (24 bytes) before constant-time wide reduction mod `q = 8_380_417`,
/// matching `linear_module::sample_uniform_mod_q` and `threshold_eval` so single-draw
/// total-variation and pointwise Rényi bias stay below `q / 2^192 < 2^-169`.
fn field_from_stream(sponge: &mut Shake256) -> u32 {
    let mut bytes = [0u8; 24];
    sponge.squeeze(&mut bytes);
    let value = reduce_wide_mod_q(&bytes);
    ct_zeroize_bytes(&mut bytes);
    value
}

/// `f_A(x) = prod over positions j outside A of (x_j - x) / x_j`.
fn subset_poly_at(xs: &[u32], subset: CustodianSet, x: u32) -> u32 {
    let mut numerator = 1;
    let mut denominator = 1;
    for (j, &xj) in xs.iter().enumerate() {
        if !subset.contains(j) {
            numerator = mod_q_mul(numerator, mod_q_sub(xj, x));
            denominator = mod_q_mul(denominator, xj);
        }
    }
    mod_q_mul(numerator, mod_q_inv_or_zero(denominator))
}

/// Weights `w` with `p(target) = sum_i w_i * p(xs_i)` for `deg p < xs.len()`.
fn lagrange_weights(xs: &[u32], target: u32) -> Vec<u32> {
    xs.iter()
        .enumerate()
        .map(|(i, &xi)| {
            let mut numerator = 1;
            let mut denominator = 1;
            for (j, &xj) in xs.iter().enumerate() {
                if i != j {
                    numerator = mod_q_mul(numerator, mod_q_sub(target, xj));
                    denominator = mod_q_mul(denominator, mod_q_sub(xi, xj));
                }
            }
            mod_q_mul(numerator, mod_q_inv_or_zero(denominator))
        })
        .collect()
}

fn dot(weights: &[u32], values: &[u32]) -> u32 {
    weights
        .iter()
        .zip(values)
        .fold(0, |acc, (&w, &v)| mod_q_add(acc, mod_q_mul(w, v)))
}

/// Opens a broadcast sharing of a fixed degree, rejecting any share set that
/// does not lie on a single polynomial of that degree.
struct OpenPlan {
    basis: usize,
    to_zero: Vec<u32>,
    checks: Vec<Vec<u32>>,
}

impl OpenPlan {
    fn new(xs: &[u32], degree: usize) -> Self {
        let basis = &xs[..degree + 1];
        Self {
            basis: degree + 1,
            to_zero: lagrange_weights(basis, 0),
            checks: xs[degree + 1..]
                .iter()
                .map(|&x| lagrange_weights(basis, x))
                .collect(),
        }
    }

    fn open(&self, shares: &[u32]) -> Result<u32, HdError> {
        let (basis, rest) = shares.split_at(self.basis);
        if rest.len() != self.checks.len() {
            return abort(RekeyFault::MalformedMessage);
        }
        for (weights, &share) in self.checks.iter().zip(rest) {
            if dot(weights, basis) != share {
                return abort(RekeyFault::InconsistentDegree);
            }
        }
        Ok(dot(&self.to_zero, basis))
    }
}

/// Exact 23-bit little-endian packing of canonical field elements.
pub fn pack_field_elements(values: &[u32]) -> Vec<u8> {
    let mut out = alloc::vec![0u8; (values.len() * 23).div_ceil(8)];
    pack_coefficients(values, &mut out);
    out
}

/// Inverse of [`pack_field_elements`]. Rejects a wrong length, a non-canonical
/// residue and nonzero padding bits.
pub fn unpack_field_elements(bytes: &[u8], count: usize) -> Result<Vec<u32>, HdError> {
    let bits = count.checked_mul(23).ok_or(HdError::RekeyAborted(RekeyFault::MalformedMessage))?;
    if bytes.len() != bits.div_ceil(8) {
        return abort(RekeyFault::MalformedMessage);
    }
    let mut values = alloc::vec![0; count];
    unpack_coefficients(bytes, &mut values);
    if values.iter().any(|&v| v >= MODULE_Q)
        || (bits % 8 != 0 && bytes.last().is_some_and(|b| b >> (bits % 8) != 0)) {
        return abort(RekeyFault::MalformedMessage);
    }
    Ok(values)
}

/// Round 1 broadcast.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RekeyHello {
    pub party_id: u16,
    pub nonce: [u8; 32],
    pub coin_commitment: [u8; 32],
    /// `(subset, A*tau_1 + tau_2)` for every subset of the sender; empty for a
    /// non-hardened child, whose tweak is public.
    pub public_shares: Vec<(CustodianSet, [RingPoly; MODULE_K])>,
}

/// Round 2 broadcast: masked degree `2t - 2` product shares.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RekeyProducts {
    pub party_id: u16,
    pub values: Vec<u32>,
}

/// Round 3 broadcast: coin opening.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RekeyCoinOpening {
    pub party_id: u16,
    pub seed: [u8; 32],
    pub salt: [u8; 32],
}

/// Round 4 broadcast: shares of the masked combinations `rho_k`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RekeyMaskedOpening {
    pub party_id: u16,
    pub values: Vec<u32>,
}

/// Round 5 broadcast: commitment to the zero-test shares.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RekeyZeroCommit {
    pub party_id: u16,
    pub digest: [u8; 32],
}

/// Round 6 broadcast: the committed zero-test shares.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RekeyZeroOpening {
    pub party_id: u16,
    pub values: Vec<u32>,
    pub salt: [u8; 32],
}

impl RekeyHello {
    /// Canonical wire encoding; also the bytes bound into the session key.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(68 + self.public_shares.len() * (2 + MODULE_K * 736));
        out.extend_from_slice(&self.party_id.to_be_bytes());
        out.extend_from_slice(&self.nonce);
        out.extend_from_slice(&self.coin_commitment);
        out.extend_from_slice(&(self.public_shares.len() as u16).to_be_bytes());
        for (subset, image) in &self.public_shares {
            out.extend_from_slice(&subset.to_be_bytes());
            for poly in image {
                out.extend_from_slice(&pack_field_elements(&poly.coeffs));
            }
        }
        out
    }
}

fn field_message_bytes(party_id: u16, values: &[u32]) -> Vec<u8> {
    let mut out = party_id.to_be_bytes().to_vec();
    out.extend_from_slice(&pack_field_elements(values));
    out
}

impl RekeyProducts {
    pub fn to_bytes(&self) -> Vec<u8> {
        field_message_bytes(self.party_id, &self.values)
    }
}
impl RekeyMaskedOpening {
    pub fn to_bytes(&self) -> Vec<u8> {
        field_message_bytes(self.party_id, &self.values)
    }
}
impl RekeyZeroOpening {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = field_message_bytes(self.party_id, &self.values);
        out.extend_from_slice(&self.salt);
        out
    }
}
impl RekeyCoinOpening {
    pub const WIRE_BYTES: usize = 66;
}
impl RekeyZeroCommit {
    pub const WIRE_BYTES: usize = 34;
}

fn ordered<T>(
    members: &[(u16, u32)],
    messages: &[T],
    party_id: impl Fn(&T) -> u16,
) -> Result<(), HdError> {
    if messages.len() != members.len()
        || messages
            .iter()
            .zip(members)
            .any(|(message, member)| party_id(message) != member.0)
    {
        return abort(RekeyFault::MalformedMessage);
    }
    Ok(())
}

fn canonical(values: &[u32], count: usize) -> Result<(), HdError> {
    if values.len() != count || values.iter().any(|&v| v >= MODULE_Q) {
        return abort(RekeyFault::MalformedMessage);
    }
    Ok(())
}

struct ParentAuth {
    s: Vec<u32>,
    macs: Vec<u32>,
    alpha: [u32; SPDZ_LANES],
}

impl Drop for ParentAuth {
    fn drop(&mut self) {
        ct_zeroize_u32s(&mut self.s);
        ct_zeroize_u32s(&mut self.macs);
        ct_zeroize_u32s(&mut self.alpha);
    }
}

/// Everything a child inherits from its custodian's parent handle.
struct Lineage {
    seed_a: [u8; 32],
    matrix: Arc<ExpandedHdMatrix>,
    family_id: Option<[u8; 32]>,
    poison_journal: Option<Arc<dyn crate::poison::HdPoisonJournal>>,
    testing_poison_journal: bool,
    poisoned: Arc<AtomicBool>,
    evaluation_queries: Arc<AtomicUsize>,
    #[cfg(feature = "std")]
    budget: Option<Arc<std::sync::Mutex<crate::budget::DurableQueryBudget>>>,
    depth_used: u16,
    max_depth: u16,
}

struct Core {
    party_id: u16,
    position: usize,
    threshold: u16,
    members: Vec<(u16, u32)>,
    request: [u8; 32],
    session: [u8; 32],
    lineage: Lineage,
    parent_t: [RingPoly; MODULE_K],
    /// `Some` once the public key of the result is fixed.
    child_t: Option<[RingPoly; MODULE_K]>,
    public_chain_code: Option<[u8; 32]>,
    chain_code: RedactedSecret<32>,
    chain_code_key: RedactedSecret<32>,
    hardened: bool,
    derivation_index: u32,
    hello: RekeyHello,
    hellos: Vec<RekeyHello>,
    coin_seed: [u8; 32],
    coin_salt: [u8; 32],
    s: Vec<u32>,
    parent: Option<ParentAuth>,
    alpha: [u32; SPDZ_LANES],
    b: Vec<u32>,
    b_parent: Vec<u32>,
    mask_shares: Vec<u32>,
    macs: Vec<u32>,
    products_digest: [u8; 32],
    combined_macs: Vec<u32>,
    combined_parent_macs: Vec<u32>,
    zero_shares: Vec<u32>,
    zero_gates: Option<crate::zero_gate::CommittedZeroGates>,
    zero_salt: [u8; 32],
    zero_commits: Vec<RekeyZeroCommit>,
    complete: bool,
}

impl Drop for Core {
    fn drop(&mut self) {
        if !self.complete && self.parent.is_some() {
            self.lineage.poisoned.store(true, Ordering::Release);
            if let Some(journal) = &self.lineage.poison_journal {
                let _ = journal.poison();
            }
        }
        ct_zeroize_bytes(&mut self.coin_seed);
        ct_zeroize_bytes(&mut self.coin_salt);
        ct_zeroize_bytes(&mut self.zero_salt);
        ct_zeroize_u32s(&mut self.alpha);
        for secret in [
            &mut self.s,
            &mut self.b,
            &mut self.b_parent,
            &mut self.mask_shares,
            &mut self.macs,
            &mut self.combined_macs,
            &mut self.combined_parent_macs,
            &mut self.zero_shares,
        ] {
            ct_zeroize_u32s(secret);
        }
    }
}

impl Core {
    fn xs(&self) -> Vec<u32> {
        self.members.iter().map(|member| member.1).collect()
    }
    fn product_count(&self) -> usize {
        CHILD_PRODUCTS + CHECK_PRODUCTS * if self.parent.is_some() { 2 } else { 1 }
    }
    fn opening_count(&self) -> usize {
        REPS * if self.parent.is_some() { 2 } else { 1 }
    }
    fn zero_count(&self) -> usize {
        CHECK_PRODUCTS * if self.parent.is_some() { 2 } else { 1 }
    }
    fn zero_commitment(&self, party_id: u16, values: &[u32], salt: &[u8; 32]) -> [u8; 32] {
        commit_mpc_broadcast(
            &self.session,
            5,
            party_id,
            &pack_field_elements(values),
            salt,
        )
    }
    fn coin_commitment(
        request: &[u8; 32],
        party_id: u16,
        seed: &[u8; 32],
        salt: &[u8; 32],
    ) -> [u8; 32] {
        commit_mpc_broadcast(request, 1, party_id, seed, salt)
    }
}

pub struct RekeyRound1<'a> {
    seeds: &'a CustodianSeeds,
    derivation: [u8; 32],
    hardened_tweak: bool,
    core: Core,
}
pub struct RekeyRound2(Core);
pub struct RekeyRound3(Core);
pub struct RekeyRound4(Core);
pub struct RekeyRound5(Core);
pub struct RekeyRound6(Core);

struct Request<'p> {
    parent: Option<(&'p LinearModulePartyShare, &'p LinearModuleXPub)>,
    /// Child index, or the account number of a root.
    index: u32,
    hardened: bool,
    root_max_depth: u16,
    root_chain_seed: Option<&'p [u8; 32]>,
    session_id: [u8; 32],
}

impl<'a> RekeyRound1<'a> {
    /// Starts dealerless provisioning of root `account`. Two roots of one
    /// ceremony with different accounts are independent keys; repeating an
    /// account reproduces its key under fresh MAC keys. A hardened root
    /// publishes no chain code. `chain_code_seed` must be an independently generated
    /// 256-bit secret securely provisioned to all custodians. The round transcript
    /// checks agreement on its derived code before any share is released.
    pub fn begin_root(
        seeds: &'a CustodianSeeds,
        account: u32,
        hardened: bool,
        max_depth: u16,
        session_id: [u8; 32],
        private_entropy: [u8; 32],
        chain_code_seed: &'a [u8; 32],
    ) -> Result<(Self, RekeyHello), HdError> {
        if max_depth == 0 || max_depth > MAX_NON_HARDENED_DERIVATION_DEPTH {
            return Err(HdError::InvalidThresholdParameters);
        }
        Self::begin(
            seeds,
            Request {
                parent: None,
                index: account,
                hardened,
                root_max_depth: max_depth,
                root_chain_seed: Some(chain_code_seed),
                session_id,
            },
            private_entropy,
        )
    }

    fn begin(
        seeds: &'a CustodianSeeds,
        request: Request<'_>,
        mut private_entropy: [u8; 32],
    ) -> Result<(Self, RekeyHello), HdError> {
        if !request.hardened && request.index & (1 << 31) != 0 {
            ct_zeroize_bytes(&mut private_entropy);
            return Err(HdError::HardenedDerivationRequired);
        }
        let entropy = RedactedSecret::new(private_entropy);
        ct_zeroize_bytes(&mut private_entropy);
        let config = seeds.config();
        let members = config.members().to_vec();
        let position = seeds.position();
        let party_id = seeds.party_id();
        let own_x = members[position].1;
        let xs: Vec<u32> = members.iter().map(|member| member.1).collect();
        let ceremony = seeds.ceremony_digest();
        let index_bytes = request.index.to_be_bytes();

        let (lineage, parent_t, parent_digest, mut s, parent, parent_cc) = match request.parent {
            None => {
                let seed_a = cshake256_framed_32(
                    b"QSAG.HD.DEALERLESS.SEED_A.V1",
                    &[&ceremony, &index_bytes],
                );
                let root_cc = cshake256_framed_32(
                    b"QSAG.HD.DEALERLESS.ROOT_CC.V2",
                    &[
                        request
                            .root_chain_seed
                            .ok_or(HdError::InvalidThresholdParameters)?,
                        &ceremony,
                        &index_bytes,
                    ],
                );
                (
                    Lineage {
                        seed_a,
                        matrix: Arc::new(ExpandedHdMatrix::new(seed_a)),
                        family_id: None,
                        poison_journal: None,
                        testing_poison_journal: false,
                        poisoned: Arc::new(AtomicBool::new(false)),
                        evaluation_queries: Arc::new(AtomicUsize::new(0)),
                        #[cfg(feature = "std")]
                        budget: None,
                        depth_used: 0,
                        max_depth: request.root_max_depth,
                    },
                    core::array::from_fn(|_| RingPoly::zero()),
                    cshake256_framed_32(b"QSAG.HD.DEALERLESS.ROOT.V1", &[&ceremony, &seed_a]),
                    alloc::vec![0u32; COEFFS],
                    None,
                    RedactedSecret::new(root_cc),
                )
            }
            Some((share, expected)) => {
                share.require_poison_journal()?;
                let valid_scheme = matches!(
                    share.scheme,
                    ShareScheme::Shamir { threshold, eval_point }
                        if threshold == config.threshold() && eval_point == own_x
                );
                if share.is_poisoned()
                    || !valid_scheme
                    || share.party_id != party_id
                    || share.committee != members
                    || expected.seed_a != expected.matrix.seed
                    || share.seed_a != expected.seed_a
                    || share.t_vec != expected.t_vec
                    || share.depth_used != expected.depth_used
                    || share.max_depth != expected.max_depth
                    || expected
                        .chain_code
                        .is_some_and(|cc| share.chain_code.expose() != &cc)
                {
                    return Err(HdError::InvalidThresholdParameters);
                }
                if expected.depth_used >= expected.max_depth {
                    return Err(HdError::DerivationBudgetExceeded {
                        current: expected.depth_used,
                        max: expected.max_depth,
                    });
                }
                if share.hardened && (expected.chain_code.is_some() || !request.hardened) {
                    return Err(HdError::HardenedDerivationRequired);
                }
                if expected.chain_code.is_none() && !request.hardened {
                    return Err(HdError::HardenedDerivationRequired);
                }
                let parent_s: Vec<u32> = share
                    .s_shares
                    .iter()
                    .flat_map(|poly| poly.expose().coeffs)
                    .collect();
                let auth = ParentAuth {
                    s: parent_s.clone(),
                    macs: share
                        .spdz_macs
                        .iter()
                        .flat_map(|lane| lane.iter().flat_map(|poly| poly.expose().coeffs))
                        .collect(),
                    alpha: share.spdz_alpha_shares,
                };
                (
                    Lineage {
                        seed_a: share.seed_a,
                        matrix: Arc::clone(&share.matrix),
                        family_id: Some(share.family_id),
                        poison_journal: share.poison_journal.clone(),
                        testing_poison_journal: share.testing_poison_journal,
                        poisoned: Arc::clone(&share.poisoned),
                        evaluation_queries: Arc::clone(&share.evaluation_queries),
                        #[cfg(feature = "std")]
                        budget: share.budget.clone(),
                        depth_used: share.depth_used + 1,
                        max_depth: share.max_depth,
                    },
                    share.t_vec.clone(),
                    hash_t_vec(&share.seed_a, &share.t_vec),
                    parent_s,
                    Some(auth),
                    RedactedSecret::new(*share.chain_code.expose()),
                )
            }
        };

        let chain_code_key = RedactedSecret::new(match request.parent {
            Some((share, _)) => *share.chain_code_key.expose(),
            None => *request
                .root_chain_seed
                .ok_or(HdError::InvalidThresholdParameters)?,
        });
        let hardened_tweak = request.parent.is_none() || request.hardened;
        let derivation = cshake256_framed_32(
            b"QSAG.HD.TPRF.DERIVATION.V1",
            &[
                &ceremony,
                &config.digest(),
                &[u8::from(request.parent.is_some())],
                &parent_digest,
                &lineage.depth_used.to_be_bytes(),
                &request
                    .parent
                    .map_or(0, |(s, _)| s.derivation_index)
                    .to_be_bytes(),
                &[u8::from(request.hardened)],
                &index_bytes,
            ],
        );

        let mut public_shares = Vec::new();
        let mut child_t = None;
        let (chain_code, public_chain_code) = if hardened_tweak {
            // Replicated threshold PRF: one short tweak for each held subset seed.
            for subset in seeds.held_subsets() {
                let mut tweak_seed = seeds
                    .prf32(subset, b"QSAG.HD.TPRF.TWEAK.V1", &[&derivation])
                    .ok_or(HdError::InvalidThresholdParameters)?;
                let tweak: [RingPoly; MODULE_SECRET_L] = core::array::from_fn(|j| {
                    RingPoly::sample_cbd2_ct(b"QSAG.HD.TPRF.R_POLY.V1", &tweak_seed, j as u32)
                });
                ct_zeroize_bytes(&mut tweak_seed);
                let weight = subset_poly_at(&xs, subset, own_x);
                for (j, poly) in tweak.iter().enumerate() {
                    for (c, &coefficient) in poly.coeffs.iter().enumerate() {
                        let slot = &mut s[j * MODULE_N + c];
                        *slot = mod_q_add(*slot, mod_q_mul(coefficient, weight));
                    }
                }
                public_shares.push((subset, lineage.matrix.relation(&tweak)));
            }
            if request.parent.is_none() {
                let public = (!request.hardened).then_some(*parent_cc.expose());
                (parent_cc, public)
            } else {
                let cc = cshake256_framed_32(
                    b"QSAG.HD.HARDENED_CC.V2",
                    &[
                        chain_code_key.expose(),
                        parent_cc.expose(),
                        &parent_digest,
                        &index_bytes,
                    ],
                );
                (RedactedSecret::new(cc), None)
            }
        } else {
            let (tweak, next_cc) =
                expand_linear_tweak(parent_cc.expose(), &parent_digest, request.index);
            if tweak
                .iter()
                .any(|r| r.centered_l2_norm_sq() > (MODULE_N as u64) * 4)
            {
                return Err(HdError::NormBoundExceeded);
            }
            for (j, poly) in tweak.iter().enumerate() {
                for (c, &coefficient) in poly.coeffs.iter().enumerate() {
                    let slot = &mut s[j * MODULE_N + c];
                    *slot = mod_q_add(*slot, coefficient);
                }
            }
            let delta = lineage.matrix.relation(&tweak);
            child_t = Some(core::array::from_fn(|row| parent_t[row].add(&delta[row])));
            (RedactedSecret::new(next_cc), Some(next_cc))
        };

        let request_digest = cshake256_framed_32(
            b"QSAG.HD.REKEY.REQUEST.V1",
            &[
                &derivation,
                &request.session_id,
                &[u8::from(request.hardened)],
                &cshake256_framed_32(b"QSAG.HD.CHAIN_CODE.COMMIT.V1", &[chain_code.expose()]),
                &lineage.max_depth.to_be_bytes(),
            ],
        );
        // Local randomness also binds this custodian's secret input, so a caller
        // that wrongly repeats `private_entropy` over different parent state
        // still gets a different nonce, and with it a different session key.
        let mut state_bytes: Vec<u8> = s.iter().flat_map(|v| v.to_le_bytes()).collect();
        if let Some(auth) = &parent {
            state_bytes.extend(auth.alpha.iter().flat_map(|v| v.to_le_bytes()));
            state_bytes.extend(auth.macs.iter().flat_map(|v| v.to_le_bytes()));
        }
        let mut state_binding = cshake256_framed_32(b"QSAG.HD.REKEY.STATE.V1", &[&state_bytes]);
        ct_zeroize_bytes(&mut state_bytes);
        let local = RedactedSecret::new(cshake256_framed_32(
            b"QSAG.HD.REKEY.LOCAL.V1",
            &[entropy.expose(), &request_digest, &state_binding],
        ));
        ct_zeroize_bytes(&mut state_binding);
        let secret = |domain: &[u8]| cshake256_framed_32(domain, &[local.expose()]);
        let coin_seed = secret(b"QSAG.HD.REKEY.COIN.V1");
        let coin_salt = secret(b"QSAG.HD.REKEY.COIN_SALT.V1");
        let hello = RekeyHello {
            party_id,
            nonce: secret(b"QSAG.HD.REKEY.NONCE.V1"),
            coin_commitment: Core::coin_commitment(
                &request_digest,
                party_id,
                &coin_seed,
                &coin_salt,
            ),
            public_shares,
        };
        let core = Core {
            party_id,
            position,
            threshold: config.threshold(),
            members,
            request: request_digest,
            chain_code_key,
            hardened: request.hardened,
            derivation_index: request.index | (u32::from(request.hardened) << 31),
            session: [0; 32],
            lineage,
            parent_t,
            child_t,
            public_chain_code,
            chain_code,
            hello: hello.clone(),
            hellos: Vec::new(),
            coin_seed,
            coin_salt,
            s,
            parent,
            alpha: [0; SPDZ_LANES],
            b: Vec::new(),
            b_parent: Vec::new(),
            mask_shares: Vec::new(),
            macs: Vec::new(),
            products_digest: [0; 32],
            combined_macs: Vec::new(),
            combined_parent_macs: Vec::new(),
            zero_shares: Vec::new(),
            zero_gates: None,
            zero_salt: secret(b"QSAG.HD.REKEY.ZERO_SALT.V1"),
            zero_commits: Vec::new(),
            complete: false,
        };
        Ok((
            Self {
                seeds,
                derivation,
                hardened_tweak,
                core,
            },
            hello,
        ))
    }

    /// Round 2. Fixes the session key and the public key of the result from the
    /// complete hello broadcast, then releases the masked product shares.
    pub fn open_products(
        self,
        hellos: &[RekeyHello],
    ) -> Result<(RekeyRound2, RekeyProducts), HdError> {
        let Self {
            seeds,
            derivation,
            hardened_tweak,
            mut core,
        } = self;
        ordered(&core.members, hellos, |hello| hello.party_id)?;
        if hellos[core.position] != core.hello {
            return abort(RekeyFault::MalformedMessage);
        }
        let config = seeds.config();
        if hardened_tweak {
            // Every holder of a subset must publish the same image; the honest
            // holder computed it from the agreed seed.
            let mut child_t = core.parent_t.clone();
            for (position, hello) in hellos.iter().enumerate() {
                let expected = config.subsets_of(position);
                if hello.public_shares.len() != expected.len()
                    || hello
                        .public_shares
                        .iter()
                        .zip(&expected)
                        .any(|(entry, &subset)| {
                            entry.0 != subset
                                || entry
                                    .1
                                    .iter()
                                    .any(|p| p.coeffs.iter().any(|&c| c >= MODULE_Q))
                        })
                {
                    return abort(RekeyFault::MalformedMessage);
                }
            }
            for subset in config.subsets() {
                let mut images = hellos.iter().filter_map(|hello| {
                    hello
                        .public_shares
                        .iter()
                        .find(|entry| entry.0 == subset)
                        .map(|entry| &entry.1)
                });
                let first = images
                    .next()
                    .ok_or(HdError::RekeyAborted(RekeyFault::MalformedMessage))?;
                if images.any(|image| image != first) {
                    return abort(RekeyFault::PublicShareMismatch);
                }
                for (row, poly) in child_t.iter_mut().zip(first) {
                    *row = row.add(poly);
                }
            }
            core.child_t = Some(child_t);
        } else if hellos.iter().any(|hello| !hello.public_shares.is_empty()) {
            return abort(RekeyFault::MalformedMessage);
        }

        let mut transcript = init_cshake256(b"", b"QSAG.HD.REKEY.SESSION.V1");
        transcript.absorb(&core.request);
        for hello in hellos {
            let bytes = hello.to_bytes();
            transcript.absorb(&(bytes.len() as u64).to_le_bytes());
            transcript.absorb(&bytes);
        }
        finalize_cshake256(&mut transcript, true);
        transcript.squeeze(&mut core.session);
        core.hellos = hellos.to_vec();

        // Pseudorandom sharings under the session key.
        let xs = core.xs();
        let own_x = xs[core.position];
        let degree = usize::from(core.threshold) - 1;
        let powers: Vec<u32> = (1..=degree)
            .scan(1u32, |power, _| {
                *power = mod_q_mul(*power, own_x);
                Some(*power)
            })
            .collect();
        let products = core.product_count();
        let has_parent = core.parent.is_some();
        core.b = alloc::vec![0; REPS];
        core.b_parent = alloc::vec![0; if has_parent { REPS } else { 0 }];
        core.mask_shares = alloc::vec![0; products];
        let mut wide_masks = SecretWords(alloc::vec![0u32; products]);
        for subset in seeds.held_subsets() {
            let weight = subset_poly_at(&xs, subset, own_x);
            let stream = |domain: &[u8]| {
                seeds
                    .prf_stream(subset, domain, &[&derivation, &core.session])
                    .ok_or(HdError::InvalidThresholdParameters)
            };
            let mut keys = stream(b"QSAG.HD.REKEY.PRSS.KEYS.V1")?;
            for alpha in &mut core.alpha {
                *alpha = mod_q_add(*alpha, mod_q_mul(field_from_stream(&mut keys), weight));
            }
            for b in core.b.iter_mut().chain(core.b_parent.iter_mut()) {
                *b = mod_q_add(*b, mod_q_mul(field_from_stream(&mut keys), weight));
            }
            let mut masks = stream(b"QSAG.HD.REKEY.PRSS.MASKS.V1")?;
            for (narrow, wide) in core.mask_shares.iter_mut().zip(wide_masks.iter_mut()) {
                let r = field_from_stream(&mut masks);
                let mut high = r;
                for &power in &powers {
                    high = mod_q_add(high, mod_q_mul(field_from_stream(&mut masks), power));
                }
                *narrow = mod_q_add(*narrow, mod_q_mul(r, weight));
                *wide = mod_q_add(*wide, mod_q_mul(high, weight));
            }
        }

        let mut values = Vec::with_capacity(products);
        for &alpha in &core.alpha {
            values.extend(core.s.iter().map(|&s| mod_q_mul(alpha, s)));
        }
        for &alpha in &core.alpha {
            values.extend(core.b.iter().map(|&b| mod_q_mul(alpha, b)));
        }
        if let Some(parent) = &core.parent {
            for &alpha in &parent.alpha {
                values.extend(core.b_parent.iter().map(|&b| mod_q_mul(alpha, b)));
            }
        }
        for (value, mask) in values.iter_mut().zip(wide_masks.iter()) {
            *value = mod_q_add(*value, *mask);
        }
        ct_zeroize_u32s(&mut wide_masks);
        let message = RekeyProducts {
            party_id: core.party_id,
            values,
        };
        Ok((RekeyRound2(core), message))
    }
}

impl RekeyRound2 {
    /// Round 3. Interpolates every product, keeps the degree `t - 1` product
    /// shares, binds the product transcript, and opens this custodian's coin.
    pub fn open_coin(
        self,
        products: &[RekeyProducts],
    ) -> Result<(RekeyRound3, RekeyCoinOpening), HdError> {
        let mut core = self.0;
        ordered(&core.members, products, |message| message.party_id)?;
        let count = core.product_count();
        let mut transcript = init_cshake256(b"", b"QSAG.HD.REKEY.PRODUCTS.V1");
        transcript.absorb(&core.session);
        for message in products {
            canonical(&message.values, count)?;
            transcript.absorb(&message.to_bytes());
        }
        finalize_cshake256(&mut transcript, true);
        transcript.squeeze(&mut core.products_digest);

        let plan = OpenPlan::new(&core.xs(), 2 * (usize::from(core.threshold) - 1));
        let mut column = SecretWords(alloc::vec![0u32; products.len()]);
        let mut macs = SecretWords(Vec::with_capacity(count));
        for (index, &mask) in core.mask_shares.iter().enumerate() {
            for (slot, message) in column.iter_mut().zip(products) {
                *slot = message.values[index];
            }
            macs.push(mod_q_sub(plan.open(&column)?, mask));
        }
        core.macs = core::mem::take(&mut macs.0);
        let opening = RekeyCoinOpening {
            party_id: core.party_id,
            seed: core.coin_seed,
            salt: core.coin_salt,
        };
        Ok((RekeyRound3(core), opening))
    }
}

impl RekeyRound3 {
    /// Round 4. Checks every coin opening, derives the public challenge
    /// vectors, and broadcasts shares of the masked combinations.
    pub fn open_masked(
        self,
        coins: &[RekeyCoinOpening],
    ) -> Result<(RekeyRound4, RekeyMaskedOpening), HdError> {
        let mut core = self.0;
        ordered(&core.members, coins, |coin| coin.party_id)?;
        let mut challenge = init_cshake256(b"", b"QSAG.HD.REKEY.CHALLENGE.V1");
        challenge.absorb(&core.session);
        challenge.absorb(&core.products_digest);
        for (coin, hello) in coins.iter().zip(&core.hellos) {
            let expected =
                Core::coin_commitment(&core.request, coin.party_id, &coin.seed, &coin.salt);
            if !ct_eq_bytes(&expected, &hello.coin_commitment) {
                return abort(RekeyFault::CommitmentMismatch);
            }
            challenge.absorb(&coin.seed);
        }
        finalize_cshake256(&mut challenge, true);

        let lanes = SPDZ_LANES;
        let mut values = alloc::vec![0u32; core.opening_count()];
        core.combined_macs = alloc::vec![0; lanes * REPS];
        core.combined_parent_macs =
            alloc::vec![0; if core.parent.is_some() { lanes * REPS } else { 0 }];
        for k in 0..REPS {
            for c in 0..COEFFS {
                let chi = field_from_stream(&mut challenge);
                values[k] = mod_q_add(values[k], mod_q_mul(chi, core.s[c]));
                for lane in 0..lanes {
                    let slot = &mut core.combined_macs[lane * REPS + k];
                    *slot = mod_q_add(*slot, mod_q_mul(chi, core.macs[lane * COEFFS + c]));
                }
                if let Some(parent) = &core.parent {
                    values[REPS + k] = mod_q_add(values[REPS + k], mod_q_mul(chi, parent.s[c]));
                    for lane in 0..lanes {
                        let slot = &mut core.combined_parent_macs[lane * REPS + k];
                        *slot = mod_q_add(*slot, mod_q_mul(chi, parent.macs[lane * COEFFS + c]));
                    }
                }
            }
            values[k] = mod_q_sub(values[k], core.b[k]);
            if core.parent.is_some() {
                values[REPS + k] = mod_q_sub(values[REPS + k], core.b_parent[k]);
            }
        }
        let message = RekeyMaskedOpening {
            party_id: core.party_id,
            values,
        };
        Ok((RekeyRound4(core), message))
    }
}

impl RekeyRound4 {
    /// Round 5. Opens the masked combinations and commits to the zero-test shares.
    pub fn commit_zero_test(
        self,
        masked: &[RekeyMaskedOpening],
    ) -> Result<(RekeyRound5, RekeyZeroCommit), HdError> {
        let mut core = self.0;
        ordered(&core.members, masked, |message| message.party_id)?;
        let count = core.opening_count();
        for message in masked {
            canonical(&message.values, count)?;
        }
        let plan = OpenPlan::new(&core.xs(), usize::from(core.threshold) - 1);
        let mut column = SecretWords(alloc::vec![0u32; masked.len()]);
        let mut rho = Vec::with_capacity(count);
        for index in 0..count {
            for (slot, message) in column.iter_mut().zip(masked) {
                *slot = message.values[index];
            }
            rho.push(plan.open(&column)?);
        }
        let mut zero_shares = Vec::with_capacity(core.zero_count());
        for lane in 0..SPDZ_LANES {
            for (k, &opened) in rho.iter().take(REPS).enumerate() {
                let check = core.macs[CHILD_PRODUCTS + lane * REPS + k];
                zero_shares.push(mod_q_sub(
                    mod_q_sub(core.combined_macs[lane * REPS + k], check),
                    mod_q_mul(opened, core.alpha[lane]),
                ));
            }
        }
        if let Some(parent) = &core.parent {
            for lane in 0..SPDZ_LANES {
                for k in 0..REPS {
                    let check = core.macs[CHILD_PRODUCTS + CHECK_PRODUCTS + lane * REPS + k];
                    zero_shares.push(mod_q_sub(
                        mod_q_sub(core.combined_parent_macs[lane * REPS + k], check),
                        mod_q_mul(rho[REPS + k], parent.alpha[lane]),
                    ));
                }
            }
        }
        core.zero_shares = zero_shares;
        let plan = OpenPlan::new(&core.xs(), usize::from(core.threshold) - 1);
        let weight = plan.to_zero.get(core.position).copied().unwrap_or(0);
        let mut residuals: Vec<u32> = core
            .zero_shares
            .iter()
            .map(|&v| mod_q_mul(weight, v))
            .collect();
        core.zero_gates = Some(crate::zero_gate::CommittedZeroGates::hold(
            core.session,
            MODULE_Q,
            &mut residuals,
        ));
        let commit = RekeyZeroCommit {
            party_id: core.party_id,
            digest: core.zero_commitment(core.party_id, &core.zero_shares, &core.zero_salt),
        };
        Ok((RekeyRound5(core), commit))
    }
}

impl RekeyRound5 {
    /// Round 6. Freezes the complete commitment set, then releases the shares.
    pub fn open_zero_test(
        self,
        commits: &[RekeyZeroCommit],
    ) -> Result<(RekeyRound6, RekeyZeroOpening), HdError> {
        let mut core = self.0;
        ordered(&core.members, commits, |commit| commit.party_id)?;
        core.zero_commits = commits.to_vec();
        let peers = crate::zero_gate::peer_transcript(
            &core.session,
            core.party_id,
            commits.iter().map(|c| (c.party_id, c.digest)),
        );
        let gates = core.zero_gates.as_mut().ok_or(HdError::MacCheckFailed)?;
        gates.freeze(peers)?;
        gates.open()?;
        if let Some(journal) = &core.lineage.poison_journal {
            journal
                .begin_disclosure(core.session)
                .map_err(|_| HdError::MacCheckFailed)?;
        }
        let opening = RekeyZeroOpening {
            party_id: core.party_id,
            values: core.zero_shares.clone(),
            salt: core.zero_salt,
        };
        Ok((RekeyRound6(core), opening))
    }
}

impl RekeyRound6 {
    /// Public identity for provisioning the mandatory family journal before completion.
    pub fn family_id(&self) -> Result<[u8; 32], HdError> {
        self.0.lineage.family_id.map(Ok).unwrap_or_else(|| {
            self.0
                .child_t
                .as_ref()
                .map(|t| hash_t_vec(&self.0.lineage.seed_a, t))
                .ok_or(HdError::InvalidThresholdParameters)
        })
    }

    /// Releases the authenticated share and its public descriptor only when
    /// every zero-test opens to zero on a consistent degree `t - 1` sharing.
    /// Complete provisioning with a durable journal bound to the resulting family.
    pub fn finish(
        self,
        openings: &[RekeyZeroOpening],
        journal: Arc<dyn crate::poison::HdPoisonJournal>,
    ) -> Result<(LinearModuleXPub, LinearModulePartyShare), HdError> {
        let (public, mut share) = self.finish_inner(openings)?;
        if share.poison_journal.is_none() {
            share.attach_poison_journal(journal)?;
        } else if journal.family_id() != share.family_id || journal.is_poisoned().unwrap_or(true) {
            return Err(HdError::MacCheckFailed);
        }
        share.require_poison_journal()?;
        Ok((public, share))
    }
    /// Explicit nonpersistent completion for pure protocol tests. Absent from builds
    /// without `cfg(test)` or the `testing-ephemeral` feature (regression on
    /// [`DEALER_FREE_PUBLIC_API`]).
    #[cfg(any(test, feature = "testing-ephemeral"))]
    pub fn finish_with_in_memory_poison_journal_for_testing(
        self,
        openings: &[RekeyZeroOpening],
    ) -> Result<(LinearModuleXPub, LinearModulePartyShare), HdError> {
        let (public, share) = self.finish_inner(openings)?;
        Ok((public, share.in_memory_poison_journal_for_testing()))
    }
    fn finish_inner(
        self,
        openings: &[RekeyZeroOpening],
    ) -> Result<(LinearModuleXPub, LinearModulePartyShare), HdError> {
        let mut core = self.0;
        ordered(&core.members, openings, |opening| opening.party_id)?;
        let count = core.zero_count();
        for (opening, commit) in openings.iter().zip(&core.zero_commits) {
            canonical(&opening.values, count)?;
            let expected = core.zero_commitment(opening.party_id, &opening.values, &opening.salt);
            if !ct_eq_bytes(&expected, &commit.digest) {
                return abort(RekeyFault::CommitmentMismatch);
            }
        }
        let plan = OpenPlan::new(&core.xs(), usize::from(core.threshold) - 1);
        let mut column = SecretWords(alloc::vec![0u32; openings.len()]);
        for index in 0..count {
            for (slot, opening) in column.iter_mut().zip(openings) {
                *slot = opening.values[index];
            }
            if plan.open(&column)? != 0 {
                return abort(if index < CHECK_PRODUCTS {
                    RekeyFault::SacrificeNonZero
                } else {
                    RekeyFault::ParentAuthenticationFailed
                });
            }
        }
        let peers = crate::zero_gate::peer_transcript(
            &core.session,
            core.party_id,
            core.zero_commits.iter().map(|c| (c.party_id, c.digest)),
        );
        let peer_sums: Vec<u32> = (0..count)
            .map(|index| {
                openings
                    .iter()
                    .enumerate()
                    .filter(|(position, _)| *position != core.position)
                    .fold(0, |sum, (position, opening)| {
                        mod_q_add(
                            sum,
                            mod_q_mul(
                                plan.to_zero.get(position).copied().unwrap_or(0),
                                opening.values[index],
                            ),
                        )
                    })
            })
            .collect();
        core.zero_gates
            .as_mut()
            .ok_or(HdError::MacCheckFailed)?
            .verify(peers, &peer_sums)?;
        if core
            .lineage
            .poison_journal
            .as_ref()
            .is_some_and(|j| !j.disclosure_active(core.session).unwrap_or(false))
        {
            return Err(HdError::MacCheckFailed);
        }
        if core.lineage.poisoned.load(Ordering::Acquire) {
            return Err(HdError::MacCheckFailed);
        }
        let t_vec = core
            .child_t
            .take()
            .ok_or(HdError::InvalidThresholdParameters)?;
        let lineage = &core.lineage;
        let public = LinearModuleXPub {
            seed_a: lineage.seed_a,
            t_vec: t_vec.clone(),
            chain_code: core.public_chain_code,
            matrix: Arc::clone(&lineage.matrix),
            depth_used: lineage.depth_used,
            max_depth: lineage.max_depth,
        };
        let poly = |values: &[u32]| {
            SecretRingPoly::new(RingPoly {
                coeffs: core::array::from_fn(|c| values[c]),
            })
        };
        let share = LinearModulePartyShare {
            party_id: core.party_id,
            scheme: ShareScheme::Shamir {
                threshold: core.threshold,
                eval_point: core.members[core.position].1,
            },
            seed_a: lineage.seed_a,
            family_id: lineage
                .family_id
                .unwrap_or_else(|| hash_t_vec(&lineage.seed_a, &t_vec)),
            t_vec,
            chain_code: RedactedSecret::new(*core.chain_code.expose()),
            chain_code_key: RedactedSecret::new(*core.chain_code_key.expose()),
            hardened: core.hardened,
            derivation_index: core.derivation_index,
            s_shares: core::array::from_fn(|j| poly(&core.s[j * MODULE_N..])),
            spdz_macs: core::array::from_fn(|lane| {
                core::array::from_fn(|j| poly(&core.macs[lane * COEFFS + j * MODULE_N..]))
            }),
            spdz_alpha_shares: core.alpha,
            committee: core.members.clone(),
            matrix: Arc::clone(&lineage.matrix),
            #[cfg(feature = "std")]
            budget: lineage.budget.clone(),
            poison_journal: lineage.poison_journal.clone(),
            testing_poison_journal: lineage.testing_poison_journal,
            poisoned: Arc::clone(&lineage.poisoned),
            evaluation_queries: Arc::clone(&lineage.evaluation_queries),
            depth_used: lineage.depth_used,
            max_depth: lineage.max_depth,
        };
        if let Some(journal) = &core.lineage.poison_journal {
            journal
                .complete_disclosure(core.session)
                .map_err(|_| HdError::MacCheckFailed)?;
        }
        core.complete = true;
        Ok((public, share))
    }
}

impl LinearModulePartyShare {
    /// Starts the dealerless rekey that derives this custodian's share of child
    /// `child_index` under fresh, independent MAC keys.
    ///
    /// There is no local derivation: the result exists only after all six
    /// broadcast rounds of [`RekeyRound1`] complete with the whole committee,
    /// and the historical one-argument form does not compile.
    /// ```compile_fail
    /// fn legacy(share: &qsag_hd::LinearModulePartyShare) {
    ///     let _ = share.derive_child_share(7);
    /// }
    /// ```
    /// `session_id` names the session and `private_entropy` must be fresh secret
    /// CSPRNG output. A hardened child gets its tweak from the replicated
    /// threshold PRF over the subset seeds and publishes no chain code; the
    /// same path always yields the same child key.
    pub fn derive_child_share<'a>(
        &'a self,
        seeds: &'a CustodianSeeds,
        expected: &LinearModuleXPub,
        child_index: u32,
        hardened: bool,
        session_id: [u8; 32],
        private_entropy: [u8; 32],
    ) -> Result<(RekeyRound1<'a>, RekeyHello), HdError> {
        RekeyRound1::begin(
            seeds,
            Request {
                parent: Some((self, expected)),
                index: child_index,
                hardened,
                root_max_depth: 0,
                root_chain_seed: None,
                session_id,
            },
            private_entropy,
        )
    }

    /// Alias of [`Self::derive_child_share`].
    pub fn derive_child_share_dealerless<'a>(
        &'a self,
        seeds: &'a CustodianSeeds,
        expected: &LinearModuleXPub,
        child_index: u32,
        hardened: bool,
        session_id: [u8; 32],
        private_entropy: [u8; 32],
    ) -> Result<(RekeyRound1<'a>, RekeyHello), HdError> {
        self.derive_child_share(
            seeds,
            expected,
            child_index,
            hardened,
            session_id,
            private_entropy,
        )
    }
}

/// The trusted-dealer fixtures and the reconstruction oracle are not part of
/// any non-test build.
/// ```compile_fail
/// use qsag_hd::linear_module::trusted_dealer_rekey_child;
/// ```
/// ```compile_fail
/// use qsag_hd::linear_module::setup_shamir_linear_module;
/// ```
/// ```compile_fail
/// use qsag_hd::linear_module::reconstruct_for_recovery_or_test;
/// ```
/// ```compile_fail
/// use qsag_hd::linear_module::trusted_dealer_opening_masks;
/// ```
/// Positive control for the four checks above: the module path itself resolves.
/// ```
/// use qsag_hd::linear_module::REKEY_SACRIFICE_REPS;
/// assert_eq!(REKEY_SACRIFICE_REPS, 7);
/// ```
/// The nonpersistent custody shortcuts are absent too, unless the
/// `testing-ephemeral` feature is enabled: no in-memory poison journal, no
/// journal-free completion, no unchecked child-seed reconstruction.
/// ```compile_fail
/// fn bypass(share: qsag_hd::LinearModulePartyShare) -> qsag_hd::LinearModulePartyShare {
///     share.in_memory_poison_journal_for_testing()
/// }
/// ```
/// ```compile_fail
/// fn bypass(round: qsag_hd::linear_module::RekeyRound6) {
///     let _ = round.finish_with_in_memory_poison_journal_for_testing(&[]);
/// }
/// ```
/// ```compile_fail
/// use qsag_hd::recover_child_signing_seed_unchecked;
/// ```
/// ```compile_fail
/// use qsag_hd::inventory::recover_child_signing_seed_unchecked;
/// ```
/// Positive control for the four checks above: the same receivers and paths resolve.
/// ```
/// use qsag_hd::inventory::{enroll_child_signing_seed_quorum, recover_child_signing_seed};
/// fn family(round: &qsag_hd::linear_module::RekeyRound6) {
///     let _ = round.family_id();
/// }
/// fn custody(share: &qsag_hd::LinearModulePartyShare) -> bool { share.is_poisoned() }
/// ```
pub const DEALER_FREE_PUBLIC_API: () = ();

#[cfg(test)]
pub(crate) mod harness {
    use super::*;

    /// One broadcast round as the network carries it. A test may rewrite any
    /// message before delivery.
    pub(crate) enum Stage<'m> {
        Hello(&'m mut Vec<RekeyHello>),
        Products(&'m mut Vec<RekeyProducts>),
        Coins(&'m mut Vec<RekeyCoinOpening>),
        Masked(&'m mut Vec<RekeyMaskedOpening>),
        ZeroCommits(&'m mut Vec<RekeyZeroCommit>),
        ZeroOpenings(&'m mut Vec<RekeyZeroOpening>),
    }

    pub(crate) type Outcome =
        Result<Vec<(LinearModuleXPub, LinearModulePartyShare)>, Vec<Option<HdError>>>;

    type Aborts = Vec<Option<HdError>>;

    fn step<S, T, M>(
        states: Vec<S>,
        advance: impl Fn(S) -> Result<(T, M), HdError>,
    ) -> Result<(Vec<T>, Vec<M>), Aborts> {
        let results: Vec<_> = states.into_iter().map(advance).collect();
        if results.iter().any(Result::is_err) {
            return Err(results.into_iter().map(Result::err).collect());
        }
        Ok(results.into_iter().map(Result::unwrap).unzip())
    }

    /// Runs one session among in-process custodians. Only broadcast messages
    /// cross between them; `tamper` sees each round before delivery.
    pub(crate) fn run(
        seeds: &[CustodianSeeds],
        parents: Option<(&[LinearModulePartyShare], &LinearModuleXPub)>,
        index: u32,
        hardened: bool,
        session_tag: u8,
        tamper: &mut dyn FnMut(Stage<'_>),
    ) -> Outcome {
        let begun: Vec<_> = seeds
            .iter()
            .enumerate()
            .map(|(i, custodian)| {
                let entropy = [session_tag ^ (0x80 + i as u8); 32];
                match parents {
                    None => RekeyRound1::begin_root(
                        custodian,
                        index,
                        hardened,
                        4,
                        [session_tag; 32],
                        entropy,
                        &[0xCC; 32],
                    ),
                    Some((shares, public)) => shares[i].derive_child_share(
                        custodian,
                        public,
                        index,
                        hardened,
                        [session_tag; 32],
                        entropy,
                    ),
                }
            })
            .collect();
        if begun.iter().any(Result::is_err) {
            return Err(begun.into_iter().map(Result::err).collect());
        }
        let (states, mut hellos): (Vec<_>, Vec<_>) = begun.into_iter().map(Result::unwrap).unzip();
        tamper(Stage::Hello(&mut hellos));
        let (states, mut products) = step(states, |s| s.open_products(&hellos))?;
        tamper(Stage::Products(&mut products));
        let (states, mut coins) = step(states, |s| s.open_coin(&products))?;
        tamper(Stage::Coins(&mut coins));
        let (states, mut masked) = step(states, |s| s.open_masked(&coins))?;
        tamper(Stage::Masked(&mut masked));
        let (states, mut commits) = step(states, |s| s.commit_zero_test(&masked))?;
        tamper(Stage::ZeroCommits(&mut commits));
        let (states, mut openings) = step(states, |s| s.open_zero_test(&commits))?;
        tamper(Stage::ZeroOpenings(&mut openings));
        let results: Vec<_> = states
            .into_iter()
            .map(|s| s.finish_with_in_memory_poison_journal_for_testing(&openings))
            .collect();
        if results.iter().any(Result::is_err) {
            return Err(results.into_iter().map(Result::err).collect());
        }
        Ok(results.into_iter().map(Result::unwrap).collect())
    }

    pub(crate) fn honest(
        seeds: &[CustodianSeeds],
        parents: Option<(&[LinearModulePartyShare], &LinearModuleXPub)>,
        index: u32,
        hardened: bool,
        session_tag: u8,
    ) -> (LinearModuleXPub, Vec<LinearModulePartyShare>) {
        let results = run(seeds, parents, index, hardened, session_tag, &mut |_| {})
            .unwrap_or_else(|errors| panic!("honest rekey aborted: {errors:?}"));
        let public = results[0].0.clone();
        assert!(results.iter().all(|(pk, _)| *pk == public));
        (
            public,
            results.into_iter().map(|(_, share)| share).collect(),
        )
    }

    pub(crate) fn committee(t: u16, n: u16) -> crate::seeds::CommitteeConfig {
        let members: Vec<_> = (0..n).map(|i| (i, u32::from(i) + 1)).collect();
        crate::seeds::CommitteeConfig::new(t, &members, [0x5A; 32]).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::harness::*;
    use super::*;
    use crate::seeds::run_seed_ceremony;

    fn all_fail(outcome: Outcome, skip: Option<usize>, fault: RekeyFault) {
        let errors = outcome.expect_err("the faulted session must abort");
        for (i, error) in errors.iter().enumerate() {
            if Some(i) != skip {
                assert_eq!(*error, Some(HdError::RekeyAborted(fault)), "custodian {i}");
            }
        }
    }

    fn alpha(shares: &[LinearModulePartyShare], pk: &LinearModuleXPub) -> [u32; SPDZ_LANES] {
        let weights = quorum_weights(shares, pk).unwrap();
        core::array::from_fn(|lane| {
            shares.iter().zip(&weights).fold(0, |sum, (s, &w)| {
                mod_q_add(sum, mod_q_mul(w, s.spdz_alpha_shares[lane]))
            })
        })
    }

    fn centered_abs(value: u32) -> u32 {
        value.min(MODULE_Q - value)
    }

    #[test]
    fn dealerless_root_and_children_authenticate_under_independent_keys() {
        for (t, n) in [(2u16, 3u16), (3, 5), (2, 5)] {
            let config = committee(t, n);
            let seeds = run_seed_ceremony(&config, 0x10 + n as u8);
            let subsets = config.subsets().len() as u32;
            let (root_pk, root) = honest(&seeds, None, 0, false, 1);
            assert_eq!(root_pk.depth_used, 0);
            assert!(root_pk.chain_code.is_some());
            // The test oracle checks all seven MAC lanes on all 2,048 coefficients
            // and the public relation; two different quorums agree.
            let quorum = usize::from(t);
            let secret = reconstruct_for_recovery_or_test(&root[..quorum], &root_pk).unwrap();
            let other =
                reconstruct_for_recovery_or_test(&root[root.len() - quorum..], &root_pk).unwrap();
            assert_eq!(secret, other);
            // The root secret is the short sum of one CBD2 term per subset.
            assert!(
                secret
                    .iter()
                    .all(|p| p.coeffs.iter().all(|&c| centered_abs(c) <= 2 * subsets))
            );
            assert!(secret.iter().any(|p| p.coeffs.iter().any(|&c| c != 0)));

            // Non-hardened child: equals the watch-only derivation.
            let (child_pk, child) = honest(&seeds, Some((&root, &root_pk)), 7, false, 2);
            assert_eq!(child_pk, root_pk.derive_child(7).unwrap());
            let child_secret =
                reconstruct_for_recovery_or_test(&child[..quorum], &child_pk).unwrap();
            let (tweak, _) = expand_linear_tweak(
                &root_pk.chain_code.unwrap(),
                &hash_t_vec(&root_pk.seed_a, &root_pk.t_vec),
                7,
            );
            for ((child, parent), tweak) in child_secret.iter().zip(&secret).zip(&tweak) {
                assert_eq!(*child, parent.add(tweak));
            }
            // Fresh independent MAC keys in every lane.
            let (a_root, a_child) = (alpha(&root, &root_pk), alpha(&child, &child_pk));
            assert!((0..SPDZ_LANES).all(|lane| a_root[lane] != a_child[lane]));

            // Hardened child: no chain code, deterministic secret, fresh keys on repeat.
            let (hard_pk, hard) = honest(&seeds, Some((&root, &root_pk)), 9, true, 3);
            assert!(hard_pk.chain_code.is_none());
            assert_eq!(
                hard_pk.derive_child(1),
                Err(HdError::HardenedDerivationRequired)
            );
            let (repeat_pk, repeat) = honest(&seeds, Some((&root, &root_pk)), 9, true, 4);
            assert_eq!(repeat_pk, hard_pk);
            assert_ne!(alpha(&hard, &hard_pk), alpha(&repeat, &repeat_pk));
            let hard_secret = reconstruct_for_recovery_or_test(&hard[..quorum], &hard_pk).unwrap();
            assert_eq!(
                hard_secret,
                reconstruct_for_recovery_or_test(&repeat[repeat.len() - quorum..], &repeat_pk)
                    .unwrap()
            );
            // The hardened tweak is short, nonzero, and differs from the public tweak
            // of the same index.
            let (public_tweak, _) = expand_linear_tweak(
                &root_pk.chain_code.unwrap(),
                &hash_t_vec(&root_pk.seed_a, &root_pk.t_vec),
                9,
            );
            for ((hard, parent), public) in hard_secret.iter().zip(&secret).zip(&public_tweak) {
                let delta = hard.sub(parent);
                assert!(delta.coeffs.iter().all(|&c| centered_abs(c) <= 2 * subsets));
                assert_ne!(delta, *public);
                assert_ne!(delta, RingPoly::zero());
            }
            // A grandchild below the hardened child requires hardened derivation.
            assert_eq!(
                hard[0]
                    .derive_child_share(&seeds[0], &hard_pk, 1, false, [9; 32], [9; 32])
                    .err(),
                Some(HdError::HardenedDerivationRequired)
            );
            // Even a coordinator who knows the exact private chain code cannot
            // relabel a hardened share by forging the caller-owned descriptor.
            let mut forged = hard_pk.clone();
            forged.chain_code = Some(*hard[0].chain_code.expose());
            assert_eq!(
                hard[0]
                    .derive_child_share(&seeds[0], &forged, 1, false, [19; 32], [20; 32])
                    .err(),
                Some(HdError::HardenedDerivationRequired)
            );
            let (grand_pk, grand) = honest(&seeds, Some((&hard, &hard_pk)), 1, true, 5);
            assert_eq!(grand_pk.depth_used, 2);
            reconstruct_for_recovery_or_test(&grand[..quorum], &grand_pk).unwrap();
        }
    }

    #[test]
    fn dealerless_masks_open_public_coefficient_through_the_committed_zero_test() {
        let config = committee(2, 3);
        let seeds = run_seed_ceremony(&config, 0x33);
        let (root_pk, root) = honest(&seeds, None, 0, false, 1);
        let (pk, mut shares) = honest(&seeds, Some((&root, &root_pk)), 3, false, 2);
        let projection = AuthorizedHdProjection::PublicRelationCoefficient {
            row: 2,
            coefficient: 41,
        };
        for roster_positions in [[0usize, 1, 2].as_slice(), [0, 2].as_slice()] {
            let roster: Vec<(u16, u32)> = roster_positions
                .iter()
                .map(|&p| config.members()[p])
                .collect();
            let masks: Vec<_> = roster_positions
                .iter()
                .map(|&p| dealerless_opening_mask(&seeds[p], &roster, [6; 32], projection).unwrap())
                .collect();
            let total = masks
                .iter()
                .fold(0, |sum, m| mod_q_add(sum, m.test_value()));
            assert_eq!(total, 0);
            assert!(masks.iter().all(|m| m.test_value() != 0));
            // A mask derived for one projection is refused for another.
            let wrong = AuthorizedHdProjection::PublicRelationCoefficient {
                row: 2,
                coefficient: 42,
            };
            let stray = dealerless_opening_mask(&seeds[0], &roster, [6; 32], wrong).unwrap();
            assert!(matches!(
                HdThresholdEvalRound1Commit::begin(
                    &mut shares[0],
                    &pk,
                    &roster,
                    projection,
                    [6; 32],
                    stray,
                    [1; 32]
                ),
                Err(HdError::InvalidThresholdParameters)
            ));
            let mut active: Vec<&mut LinearModulePartyShare> = Vec::new();
            for (p, share) in shares.iter_mut().enumerate() {
                if roster_positions.contains(&p) {
                    active.push(share);
                }
            }
            let states: Vec<_> = active
                .into_iter()
                .zip(masks)
                .map(|(share, mask)| {
                    HdThresholdEvalRound1Commit::begin(
                        share, &pk, &roster, projection, [6; 32], mask, [2; 32],
                    )
                    .unwrap()
                })
                .collect();
            let commits: Vec<_> = states.iter().map(|s| s.commitment()).collect();
            let mut states: Vec<_> = states
                .into_iter()
                .map(|s| s.freeze(&commits).unwrap())
                .collect();
            let openings: Vec<_> = states.iter().map(|s| s.share_opening()).collect();
            let commits: Vec<_> = states
                .iter_mut()
                .map(|s| s.commit_mac(&openings).unwrap())
                .collect();
            let mut states: Vec<_> = states
                .into_iter()
                .map(|s| s.freeze_mac(&commits).unwrap())
                .collect();
            let mac_openings: Vec<_> = states
                .iter_mut()
                .map(|s| s.mac_opening().unwrap())
                .collect();
            for state in states {
                assert_eq!(state.verify(&mac_openings), Ok(pk.t_vec[2].coeffs[41]));
            }
        }
        // Different sessions give unrelated masks.
        let roster = config.members().to_vec();
        let a = dealerless_opening_mask(&seeds[1], &roster, [6; 32], projection).unwrap();
        let b = dealerless_opening_mask(&seeds[1], &roster, [7; 32], projection).unwrap();
        assert_ne!(a.test_value(), b.test_value());
        // A roster below the threshold or outside the committee is refused.
        assert!(dealerless_opening_mask(&seeds[1], &roster[1..2], [6; 32], projection).is_err());
        assert!(
            dealerless_opening_mask(&seeds[1], &[(1, 2), (9, 9)], [6; 32], projection).is_err()
        );
    }

    #[test]
    fn every_protocol_stage_rejects_a_fault() {
        let config = committee(2, 3);
        let seeds = run_seed_ceremony(&config, 0x44);
        let bump = |v: &mut u32| *v = mod_q_add(*v, 1);

        // Bad multiplication share: an additive error on one child MAC product.
        // With n = 2t - 1 it passes interpolation and only the sacrifice sees it.
        for index in [0, CHILD_PRODUCTS - 1, 3 * COEFFS + 77] {
            let (root_pk, root) = honest(&seeds, None, 0, false, 1);
            let parents = Some((root.as_slice(), &root_pk));
            let outcome = run(&seeds, parents, 5, false, 2, &mut |stage| {
                if let Stage::Products(messages) = stage {
                    bump(&mut messages[1].values[index]);
                }
            });
            all_fail(outcome, None, RekeyFault::SacrificeNonZero);
        }
        // The same error on the sacrifice product itself.
        let (root_pk, root) = honest(&seeds, None, 0, false, 1);
        let parents = Some((root.as_slice(), &root_pk));
        let outcome = run(&seeds, parents, 5, false, 2, &mut |stage| {
            if let Stage::Products(messages) = stage {
                bump(&mut messages[2].values[CHILD_PRODUCTS + 9]);
            }
        });
        all_fail(outcome, None, RekeyFault::SacrificeNonZero);
        // A blind attempt to cancel: error on a MAC product and on all seven of
        // its lane's sacrifice products. Cancelling needs the unopened coin.
        let (root_pk, root) = honest(&seeds, None, 0, false, 1);
        let parents = Some((root.as_slice(), &root_pk));
        let outcome = run(&seeds, parents, 5, false, 2, &mut |stage| {
            if let Stage::Products(messages) = stage {
                bump(&mut messages[0].values[0]);
                for k in 0..REPS {
                    bump(&mut messages[0].values[CHILD_PRODUCTS + k]);
                }
            }
        });
        all_fail(outcome, None, RekeyFault::SacrificeNonZero);
        // An error on the parent-authentication product.
        let (root_pk, root) = honest(&seeds, None, 0, false, 1);
        let parents = Some((root.as_slice(), &root_pk));
        let outcome = run(&seeds, parents, 5, false, 2, &mut |stage| {
            if let Stage::Products(messages) = stage {
                bump(&mut messages[1].values[CHILD_PRODUCTS + CHECK_PRODUCTS]);
            }
        });
        all_fail(outcome, None, RekeyFault::ParentAuthenticationFailed);
        // Non-canonical and truncated product messages.
        let (root_pk, root) = honest(&seeds, None, 0, false, 1);
        let parents = Some((root.as_slice(), &root_pk));
        let outcome = run(&seeds, parents, 5, false, 2, &mut |stage| {
            if let Stage::Products(messages) = stage {
                messages[1].values[4] = MODULE_Q;
            }
        });
        all_fail(outcome, None, RekeyFault::MalformedMessage);
        let (root_pk, root) = honest(&seeds, None, 0, false, 1);
        let parents = Some((root.as_slice(), &root_pk));
        let outcome = run(&seeds, parents, 5, false, 2, &mut |stage| {
            if let Stage::Products(messages) = stage {
                messages[1].values.pop();
            }
        });
        all_fail(outcome, None, RekeyFault::MalformedMessage);

        // Bad coin opening: a different seed than the one committed in round 1.
        let (root_pk, root) = honest(&seeds, None, 0, false, 1);
        let parents = Some((root.as_slice(), &root_pk));
        let outcome = run(&seeds, parents, 5, false, 2, &mut |stage| {
            if let Stage::Coins(coins) = stage {
                coins[2].seed[0] ^= 1;
            }
        });
        all_fail(outcome, None, RekeyFault::CommitmentMismatch);

        // Bad masked opening: one share off the degree t-1 polynomial.
        let (root_pk, root) = honest(&seeds, None, 0, false, 1);
        let parents = Some((root.as_slice(), &root_pk));
        let outcome = run(&seeds, parents, 5, false, 2, &mut |stage| {
            if let Stage::Masked(messages) = stage {
                bump(&mut messages[0].values[3]);
            }
        });
        all_fail(outcome, None, RekeyFault::InconsistentDegree);

        // Bad sacrifice opening: a zero-test share changed after commitment.
        let (root_pk, root) = honest(&seeds, None, 0, false, 1);
        let parents = Some((root.as_slice(), &root_pk));
        let outcome = run(&seeds, parents, 5, false, 2, &mut |stage| {
            if let Stage::ZeroOpenings(openings) = stage {
                bump(&mut openings[1].values[0]);
            }
        });
        all_fail(outcome, None, RekeyFault::CommitmentMismatch);
        // Bad commitment opening: the commitment itself replaced.
        let (root_pk, root) = honest(&seeds, None, 0, false, 1);
        let parents = Some((root.as_slice(), &root_pk));
        let outcome = run(&seeds, parents, 5, false, 2, &mut |stage| {
            if let Stage::ZeroCommits(commits) = stage {
                commits[1].digest[0] ^= 1;
            }
        });
        all_fail(outcome, None, RekeyFault::CommitmentMismatch);
        // A zero-test share changed consistently with a fresh commitment is off
        // the polynomial fixed by the honest custodians.
        let mut session = [0u8; 32];
        let mut forged = None;
        let (root_pk, root) = honest(&seeds, None, 0, false, 1);
        let parents = Some((root.as_slice(), &root_pk));
        let outcome = run(&seeds, parents, 5, false, 2, &mut |stage| match stage {
            Stage::Hello(hellos) => {
                let mut transcript = init_cshake256(b"", b"QSAG.HD.REKEY.SESSION.V1");
                // Recompute the public session key exactly as a custodian does.
                let derivation = cshake256_framed_32(
                    b"QSAG.HD.TPRF.DERIVATION.V1",
                    &[
                        &seeds[0].ceremony_digest(),
                        &config.digest(),
                        &[1],
                        &hash_t_vec(&root_pk.seed_a, &root_pk.t_vec),
                        &1u16.to_be_bytes(),
                        &root[0].derivation_index.to_be_bytes(),
                        &[0],
                        &5u32.to_be_bytes(),
                    ],
                );
                let request = cshake256_framed_32(
                    b"QSAG.HD.REKEY.REQUEST.V1",
                    &[
                        &derivation,
                        &[2; 32],
                        &[0],
                        &cshake256_framed_32(
                            b"QSAG.HD.CHAIN_CODE.COMMIT.V1",
                            &[&root_pk.derive_child(5).unwrap().chain_code.unwrap()],
                        ),
                        &4u16.to_be_bytes(),
                    ],
                );
                transcript.absorb(&request);
                for hello in hellos.iter() {
                    let bytes = hello.to_bytes();
                    transcript.absorb(&(bytes.len() as u64).to_le_bytes());
                    transcript.absorb(&bytes);
                }
                finalize_cshake256(&mut transcript, true);
                transcript.squeeze(&mut session);
            }
            Stage::ZeroCommits(commits) => {
                // The corrupt custodian cannot know its honest share yet in this
                // harness, so it commits to a guess: the all-zero vector.
                let values = alloc::vec![0u32; 2 * CHECK_PRODUCTS];
                commits[1].digest =
                    commit_mpc_broadcast(&session, 5, 1, &pack_field_elements(&values), &[7; 32]);
                forged = Some(values);
            }
            Stage::ZeroOpenings(openings) => {
                openings[1].values = forged.take().unwrap();
                openings[1].salt = [7; 32];
            }
            _ => {}
        });
        // Custodian 1's own state sees the same public transcript and rejects too.
        all_fail(outcome, None, RekeyFault::InconsistentDegree);

        // Equivocation and substitution in round 1.
        let outcome = run(&seeds, None, 1, true, 3, &mut |stage| {
            if let Stage::Hello(hellos) = stage {
                bump(&mut hellos[1].public_shares[0].1[0].coeffs[0]);
            }
        });
        // Custodian 1 sees its own hello altered; the others see holders disagree.
        let errors = outcome.err().unwrap();
        assert_eq!(
            errors[1],
            Some(HdError::RekeyAborted(RekeyFault::MalformedMessage))
        );
        assert_eq!(
            errors[0],
            Some(HdError::RekeyAborted(RekeyFault::PublicShareMismatch))
        );
        assert_eq!(
            errors[2],
            Some(HdError::RekeyAborted(RekeyFault::PublicShareMismatch))
        );
        // Reordered or missing senders.
        let (root_pk, root) = honest(&seeds, None, 0, false, 1);
        let parents = Some((root.as_slice(), &root_pk));
        let outcome = run(&seeds, parents, 5, false, 2, &mut |stage| {
            if let Stage::Hello(hellos) = stage {
                hellos.swap(0, 1);
            }
        });
        all_fail(outcome, None, RekeyFault::MalformedMessage);
        let (root_pk, root) = honest(&seeds, None, 0, false, 1);
        let parents = Some((root.as_slice(), &root_pk));
        let outcome = run(&seeds, parents, 5, false, 2, &mut |stage| {
            if let Stage::Masked(messages) = stage {
                messages.pop();
            }
        });
        all_fail(outcome, None, RekeyFault::MalformedMessage);
        // A public tweak image on a non-hardened rekey is refused.
        let (root_pk, root) = honest(&seeds, None, 0, false, 1);
        let parents = Some((root.as_slice(), &root_pk));
        let outcome = run(&seeds, parents, 5, false, 2, &mut |stage| {
            if let Stage::Hello(hellos) = stage {
                let image = core::array::from_fn(|_| RingPoly::zero());
                hellos[1].public_shares.push((0b011, image));
            }
        });
        all_fail(outcome, None, RekeyFault::MalformedMessage);

        // An aborted child protocol quarantines the parent family.
        assert!(root.iter().all(LinearModulePartyShare::is_poisoned));
        assert!(run(&seeds, parents, 5, false, 6, &mut |_| {}).is_err());
        let (root_pk, root) = honest(&seeds, None, 0, false, 1);
        let (child_pk, child) = honest(&seeds, Some((&root, &root_pk)), 5, false, 6);
        reconstruct_for_recovery_or_test(&child[..2], &child_pk).unwrap();
    }

    #[test]
    fn redundant_committee_rejects_a_bad_product_at_interpolation() {
        // n > 2t - 1: a single wrong point is off the degree 2t-2 polynomial.
        let config = committee(2, 5);
        let seeds = run_seed_ceremony(&config, 0x45);
        let outcome = run(&seeds, None, 0, false, 1, &mut |stage| {
            if let Stage::Products(messages) = stage {
                messages[4].values[11] = mod_q_add(messages[4].values[11], 1);
            }
        });
        all_fail(outcome, None, RekeyFault::InconsistentDegree);
    }

    #[test]
    fn faulted_parent_state_is_caught_before_a_child_is_released() {
        let config = committee(2, 3);
        let seeds = run_seed_ceremony(&config, 0x46);
        let (root_pk, mut root) = honest(&seeds, None, 0, false, 1);
        // One custodian's parent MAC share is wrong: its zero-test share leaves
        // the polynomial defined by the others.
        root[1].spdz_macs[4][2].0.coeffs[9] = mod_q_add(root[1].spdz_macs[4][2].0.coeffs[9], 1);
        let outcome = run(&seeds, Some((&root, &root_pk)), 2, true, 2, &mut |_| {});
        all_fail(outcome, None, RekeyFault::InconsistentDegree);
        assert!(root.iter().all(LinearModulePartyShare::is_poisoned));
        let (root_pk, mut root) = honest(&seeds, None, 0, false, 1);
        // Every custodian holds a consistent sharing of a wrong MAC value.
        for share in &mut root {
            share.spdz_macs[4][2].0.coeffs[9] = mod_q_add(share.spdz_macs[4][2].0.coeffs[9], 1);
        }
        let outcome = run(&seeds, Some((&root, &root_pk)), 2, true, 2, &mut |_| {});
        all_fail(outcome, None, RekeyFault::ParentAuthenticationFailed);
        assert!(root.iter().all(LinearModulePartyShare::is_poisoned));
        let (root_pk, mut root) = honest(&seeds, None, 0, false, 1);
        // A wrong parent secret share is off the degree t-1 polynomial.
        root[2].s_shares[7].0.coeffs[255] = mod_q_add(root[2].s_shares[7].0.coeffs[255], 1);
        let outcome = run(&seeds, Some((&root, &root_pk)), 2, true, 2, &mut |_| {});
        all_fail(outcome, None, RekeyFault::InconsistentDegree);
        assert!(root.iter().all(LinearModulePartyShare::is_poisoned));
        let (root_pk, root) = honest(&seeds, None, 0, false, 1);
        // A poisoned or foreign parent handle cannot start a rekey.
        let (other_pk, _) = honest(&seeds, None, 1, false, 3);
        assert_eq!(
            root[0]
                .derive_child_share(&seeds[0], &other_pk, 2, true, [1; 32], [1; 32])
                .err(),
            Some(HdError::InvalidThresholdParameters)
        );
        assert_eq!(
            root[0]
                .derive_child_share(&seeds[1], &root_pk, 2, true, [1; 32], [1; 32])
                .err(),
            Some(HdError::InvalidThresholdParameters)
        );
        // A newly provisioned test family rekeys successfully.
        honest(&seeds, Some((&root, &root_pk)), 2, true, 4);
    }

    #[test]
    fn coalition_view_is_independent_of_the_missing_subset_seed() {
        // Two worlds that differ only in the seed of the subset excluding
        // custodian 0. Custodian 0 is the whole coalition for t = 2.
        let config = committee(2, 3);
        let missing = CustodianSet::from(0b110);
        let world = |flip: bool| -> Vec<CustodianSeeds> {
            (0..3u16)
                .map(|id| {
                    CustodianSeeds::from_explicit_seeds(&config, id, [0x77; 32], |subset| {
                        let mut seed = [subset.to_be_bytes()[31] ^ 0x3C; 32];
                        if flip && subset == missing {
                            seed[0] ^= 0x80;
                        }
                        seed
                    })
                })
                .collect()
        };
        let mut views = Vec::new();
        let mut secrets = Vec::new();
        for flip in [false, true] {
            let seeds = world(flip);
            assert!(seeds[0].held_subsets().all(|subset| subset != missing));
            let (pk, shares) = honest(&seeds, None, 0, false, 1);
            // Custodian 0's share of the root secret.
            let own: Vec<u32> = shares[0]
                .s_shares
                .iter()
                .flat_map(|p| p.expose().coeffs)
                .collect();
            views.push(own);
            secrets.push((
                reconstruct_for_recovery_or_test(&shares[1..], &pk).unwrap(),
                pk,
            ));
        }
        // Identical coalition share, different secret and public key: the
        // coalition's share and seeds do not determine the secret.
        assert_eq!(views[0], views[1]);
        assert_ne!(secrets[0].0, secrets[1].0);
        assert_ne!(secrets[0].1.t_vec, secrets[1].1.t_vec);
        // The difference is exactly one fresh CBD2 term per polynomial.
        for (a, b) in secrets[0].0.iter().zip(&secrets[1].0) {
            assert!(a.sub(b).coeffs.iter().all(|&c| centered_abs(c) <= 4));
        }
    }

    #[test]
    fn opened_zero_test_shares_are_computable_by_the_coalition() {
        // The round 6 opening adds nothing to a coalition's view: the honest
        // custodians' shares follow from the coalition's own shares and the
        // opened value, here in an honest run and in a faulted run.
        for (t, n) in [(2u16, 3u16), (3, 5)] {
            let config = committee(t, n);
            let seeds = run_seed_ceremony(&config, 0x48);
            let xs: Vec<u32> = config.members().iter().map(|m| m.1).collect();
            let coalition = usize::from(t) - 1;
            for fault in [false, true] {
                let mut captured = Vec::new();
                let outcome = run(&seeds, None, 0, false, 1, &mut |stage| match stage {
                    Stage::Products(messages) if fault => {
                        messages[0].values[5] = mod_q_add(messages[0].values[5], 1);
                    }
                    Stage::ZeroOpenings(openings) => captured = openings.clone(),
                    _ => {}
                });
                assert_eq!(outcome.is_err(), fault);
                let basis = &xs[..coalition + 1];
                let mut nonzero = 0;
                for index in 0..CHECK_PRODUCTS {
                    let all: Vec<u32> = captured.iter().map(|o| o.values[index]).collect();
                    // The opened value w(0), public after the round.
                    let opened = dot(
                        &lagrange_weights(&xs[..usize::from(t)], 0),
                        &all[..usize::from(t)],
                    );
                    nonzero += usize::from(opened != 0);
                    // Interpolate through (0, w(0)) and the coalition's own points.
                    let mut points = alloc::vec![0u32];
                    points.extend_from_slice(&basis[..coalition]);
                    let mut known = alloc::vec![opened];
                    known.extend_from_slice(&all[..coalition]);
                    for honest in coalition..usize::from(n) {
                        let predicted = dot(&lagrange_weights(&points, xs[honest]), &known);
                        assert_eq!(predicted, all[honest]);
                    }
                }
                // Honest run: every test is zero. Faulted run: the faulted lane's
                // seven tests are nonzero (each is zero with probability 1/q).
                assert_eq!(nonzero, if fault { REPS } else { 0 });
            }
        }
    }

    #[test]
    fn field_packing_round_trips_and_rejects_malformed_input() {
        let values: Vec<u32> = (0..1000u32).map(|i| (i * 8_191 + 5) % MODULE_Q).collect();
        let packed = pack_field_elements(&values);
        assert_eq!(packed.len(), 2875);
        assert_eq!(unpack_field_elements(&packed, 1000).unwrap(), values);
        assert!(unpack_field_elements(&packed, 999).is_err());
        assert!(unpack_field_elements(&packed[..2874], 1000).is_err());
        assert!(unpack_field_elements(&[0xFF, 0xFF, 0x7F], 1).is_err());
        // One element leaves one padding bit, which must be zero.
        assert!(unpack_field_elements(&[1, 0, 0x80], 1).is_err());
        assert_eq!(unpack_field_elements(&[1, 0, 0], 1).unwrap(), [1]);
    }

    #[test]
    fn measured_rekey_cost() {
        for (t, n) in [(2u16, 3u16), (2, 5), (3, 5)] {
            let config = committee(t, n);
            let seeds = run_seed_ceremony(&config, 0x49);
            let (root_pk, root) = honest(&seeds, None, 0, false, 1);
            for (label, hardened) in [("non-hardened child", false), ("hardened child", true)] {
                let mut bytes = [0usize; REKEY_BROADCAST_ROUNDS];
                let start = std::time::Instant::now();
                let outcome = run(
                    &seeds,
                    Some((&root, &root_pk)),
                    11,
                    hardened,
                    9,
                    &mut |stage| match stage {
                        Stage::Hello(m) => bytes[0] = m.iter().map(|x| x.to_bytes().len()).sum(),
                        Stage::Products(m) => bytes[1] = m.iter().map(|x| x.to_bytes().len()).sum(),
                        Stage::Coins(m) => bytes[2] = m.len() * RekeyCoinOpening::WIRE_BYTES,
                        Stage::Masked(m) => bytes[3] = m.iter().map(|x| x.to_bytes().len()).sum(),
                        Stage::ZeroCommits(m) => bytes[4] = m.len() * RekeyZeroCommit::WIRE_BYTES,
                        Stage::ZeroOpenings(m) => {
                            bytes[5] = m.iter().map(|x| x.to_bytes().len()).sum();
                        }
                    },
                );
                let elapsed = start.elapsed();
                assert!(outcome.is_ok());
                std::println!(
                    "REKEY ({t},{n}) {label}: rounds={REKEY_BROADCAST_ROUNDS} bytes/round(all custodians)={bytes:?} total={} elapsed={:.3} ms (all {n} custodians, one thread)",
                    bytes.iter().sum::<usize>(),
                    elapsed.as_secs_f64() * 1e3,
                );
            }
        }
    }
}
