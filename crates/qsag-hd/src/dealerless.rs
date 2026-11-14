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

use super::*;
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

fn field_from_stream(sponge: &mut Shake256) -> u32 {
    let mut bytes = [0u8; 12];
    sponge.squeeze(&mut bytes);
    let value = reduce_wide_mod_q(&bytes);
    ct_zeroize_bytes(&mut bytes);
    value
}

/// `f_A(x) = prod over positions j outside A of (x_j - x) / x_j`.
fn subset_poly_at(xs: &[u32], subset: u16, x: u32) -> u32 {
    let mut numerator = 1;
    let mut denominator = 1;
    for (j, &xj) in xs.iter().enumerate() {
        if subset >> j & 1 == 0 {
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
    for (i, &value) in values.iter().enumerate() {
        for bit in 0..23 {
            out[(i * 23 + bit) / 8] |= (((value >> bit) & 1) as u8) << ((i * 23 + bit) % 8);
        }
    }
    out
}

/// Inverse of [`pack_field_elements`]. Rejects a wrong length, a non-canonical
/// residue and nonzero padding bits.
pub fn unpack_field_elements(bytes: &[u8], count: usize) -> Result<Vec<u32>, HdError> {
    if bytes.len() != (count * 23).div_ceil(8) {
        return abort(RekeyFault::MalformedMessage);
    }
    let bit = |index: usize| u32::from((bytes[index / 8] >> (index % 8)) & 1);
    let values: Vec<u32> = (0..count)
        .map(|i| (0..23).fold(0, |acc, b| acc | bit(i * 23 + b) << b))
        .collect();
    if values.iter().any(|&v| v >= MODULE_Q) || (count * 23..bytes.len() * 8).any(|i| bit(i) != 0)
    {
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
    pub public_shares: Vec<(u16, [RingPoly; MODULE_K])>,
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
    #[cfg(feature = "std")]
    poison_journal: Option<Arc<dyn crate::poison::HdPoisonJournal>>,
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
    zero_salt: [u8; 32],
    zero_commits: Vec<RekeyZeroCommit>,
}

impl Drop for Core {
    fn drop(&mut self) {
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
        commit_mpc_broadcast(&self.session, 5, party_id, &pack_field_elements(values), salt)
    }
    fn coin_commitment(request: &[u8; 32], party_id: u16, seed: &[u8; 32], salt: &[u8; 32]) -> [u8; 32] {
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
