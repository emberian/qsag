//! `Π_triple_f2`: dealerless authenticated Boolean Beaver triples for Shamir-SPDZ.
//!
//! Every party contributes XOR shares of `a`, `b` and of the pairwise-OT product `c`. The
//! protocol authenticates those bits, proves `c = a & b` for the whole batch at once, converts
//! raw triples at adaptive arity, then converts the result to degree-`< t` Shamir form:
//!
//! 1. **Authenticated bits.** For each ordered pair (key holder `i`, bit owner `p`) one
//!    KOS-checked correlated OT extension is run whose fixed correlation is the holder's share
//!    `alpha_i` of both MAC-key lanes. Row `k` gives `t_k ^ q_k = x_k * alpha_i`: one unhashed
//!    row per authenticated bit. The correlation is bound to the holder by its base-OT choice
//!    bits, so a holder cannot make a MAC depend on the owner's bit; an owner whose columns are
//!    not monochrome fails the consistency check except by guessing bits of `alpha_i`.
//! 2. **Products.** `b` is the only secret ever used as an OT choice. Hashing the rows of the
//!    owner's `b` bits turns them into random OTs carrying the AND cross terms and, later, the
//!    cross terms of every fold round. A sender that lies in one transfer learns one raw `b` bit
//!    with probability 1/2 and is caught otherwise; this is the leakage the adaptive combine
//!    under a post-hoc bucket permutation is there to absorb.
//! 3. **Recursive inner-product sacrifice.** With public coins `chi_k` fixed after `c` is
//!    authenticated, `c = a & b` for all `k` is the inner-product claim
//!    `<(chi_k a_k), (b_k)> = sum chi_k c_k` over `GF(2)[x]/(x^128 + x^7 + x^2 + x + 1)`. Each
//!    round authenticates the two cross terms, draws a coin `r` and halves the claim
//!    (`a' = a_even + r a_odd`, `b' = r b_even + b_odd`, `c' = h0 + r c + r^2 h1`), ending in a
//!    masked opening of one product. This is the protocol of
//!    `recursive_sacrifice_false_claim_accepting_coins_bound` in
//!    `lean/Qsag/Protocol/Migration/ActiveMigrationZeroTest.lean` up to the fixed index permutation that turns
//!    halves into even/odd positions: a false claim survives `r` rounds on at most a
//!    `2 (r + 1) / 2^128` fraction of coins. Two instances with independent coins run side by
//!    side, so a false batch is accepted with probability at most `(2 (r + 1) / 2^128)^2`.
//!    Cross terms are computed by unchecked OT products; the bound needs only that they are
//!    authenticated before the round coin.
//! 4. **Adaptive combine.** After sacrifice, draw a transcript-bound bucket coin and use
//!    the least `f = combine_arity(n) >= 2` satisfying `n / C(f(n+1), f) <= 2^-40`, where
//!    `n` counts output bits. Discard one full parity bucket per pass. Combine both factors in two
//!    passes when the product backend can leak either factor.
//! 5. **Shamir conversion.** Only after combining, each party deals degree-`< t` shares of
//!    its XOR share and additive MAC share. `spdz_pimac_check_bs_gf256_words` checks the
//!    resulting sharings and their MACs in both lanes. The additive entry point stops before
//!    this dealing step.

#![expect(
    clippy::needless_range_loop,
    reason = "Party, lane and bit indices address several parallel protocol tables"
)]

#[cfg(all(test, not(feature = "std")))]
extern crate std;

mod authentication;
mod combine;
mod sacrifice;
#[cfg(test)]
mod tests;
pub(super) use authentication::authenticate_xor_shared_words;

use super::*;
use crate::preprocessing::ot_ext::{compute_kos_transcript_bind, transpose_cols128_to_rows};
use crate::sponge::keccak::{Cshake256WordStream4, cshake256_static_midstate};
use authentication::{convert_to_shamir_and_check, open_additive_authenticated};
use combine::{Leak, combine_raw, combine_shape};
use sacrifice::{FoldPlan, raw_ceremony, raw_silent_ceremony};

/// Shamir value shares `[party][word]` and Shamir MAC shares `[party][word][lane][bit]`.
pub(super) type ShamirAuthenticatedWords =
    (Vec<Vec<BitslicedGf256x64>>, Vec<Vec<[[Tower128; 64]; 2]>>);

/// Two MAC lanes of one correlated-OT row or of one authenticated value.
type Row = [u128; 2];
type PairRows = ([Vec<u128>; 2], [Vec<u128>; 2]);
type ShamirTamper<'a> =
    dyn FnMut(&mut [Vec<BitslicedGf256x64>], &mut [Vec<[[Tower128; 64]; 2]>]) + 'a;
type ProductTamper<'a> = dyn FnMut(usize, &mut [u64]) + 'a;
type FoldTamper<'a> = dyn FnMut(usize, usize, &mut [[u128; 2]; 2]) + 'a;
type WordTamper<'a> = dyn FnMut(usize, &mut [BitslicedGf256x64], &mut [BitslicedGf256x64]) + 'a;
type MacTamper<'a> = dyn FnMut(usize, &mut [[[Tower128; 64]; 2]]) + 'a;
type ChoiceTamper<'a> = dyn FnMut(usize, usize, &mut u128) + 'a;
type OpeningTamper<'a> = dyn FnMut(usize, &mut [u128]) + 'a;

const ABIT_COL_MID: [u64; 25] = cshake256_static_midstate(b"QSAG.ABIT.COL/v1");
const ABIT_CHI_MID: [u64; 25] = cshake256_static_midstate(b"QSAG.ABIT.CHI/v1");
const SACRIFICE_CHI_MID: [u64; 25] = cshake256_static_midstate(b"QSAG.TRIPLE.F2.CHI/v1");

/// Extra random rows per extension that mask the owner's consistency-check response.
const SACRIFICIAL_ROWS: usize = 256;
/// Below this vector length fold cross terms use fresh chosen-choice products.
const GENERIC_FOLD_LEN: usize = 64;
/// Rate blocks squeezed per hashed row; bounds the number of structured fold rounds.
const MAX_CRH_BLOCKS: usize = 4;
const RATE_WORDS: usize = 17;
#[cfg(any(test, feature = "std"))]
const MAX_WORKERS: usize = 32;
const SHAMIR_BLOCK_WORDS: usize = 64;
/// Pool bits of the disposable mask word of one Shamir conversion check.
const CHECK_MASK_BITS: usize = 512;

#[cfg(any(test, feature = "std"))]
std::thread_local! {
    /// How many sibling parallel regions share the machine with this thread's own regions.
    static WORKER_SHARE: core::cell::Cell<usize> = const { core::cell::Cell::new(1) };
}

fn worker_count() -> usize {
    #[cfg(any(test, feature = "std"))]
    {
        let all = std::thread::available_parallelism()
            .map_or(1, usize::from)
            .min(MAX_WORKERS);
        (PublicDivisor::new(WORKER_SHARE.get()).split(all).0).max(1)
    }
    #[cfg(not(any(test, feature = "std")))]
    {
        1
    }
}

/// Run `f` on every item, across worker threads where the build has them. Items are disjoint
/// and `f` shares only immutable state, so the result does not depend on scheduling.
pub(super) fn par_for_each<T: Send, F: Fn(&mut T) + Sync>(items: &mut [T], f: F) {
    #[cfg(any(test, feature = "std"))]
    {
        let workers = worker_count();
        if workers > 1 && items.len() > 1 {
            let per = PublicDivisor::new(workers).ceil(items.len());
            let f = &f;
            std::thread::scope(|scope| {
                for chunk in items.chunks_mut(per) {
                    scope.spawn(move || chunk.iter_mut().for_each(f));
                }
            });
            return;
        }
    }
    items.iter_mut().for_each(f);
}

/// Like [`par_for_each`] for items that open parallel regions of their own: each item's regions
/// get an equal share of the workers, so the thread count stays that of one region.
fn par_for_each_nested<T: Send, F: Fn(&mut T) + Sync>(items: &mut [T], f: F) {
    #[cfg(any(test, feature = "std"))]
    {
        if worker_count() > 1 && items.len() > 1 {
            let share = WORKER_SHARE.get() * items.len();
            let f = &f;
            std::thread::scope(|scope| {
                for item in items.iter_mut() {
                    scope.spawn(move || {
                        WORKER_SHARE.set(share);
                        f(item);
                    });
                }
            });
            return;
        }
    }
    items.iter_mut().for_each(f);
}

// ---------------------------------------------------------------------------
// GF(2)[x] / (x^128 + x^7 + x^2 + x + 1), bit `j` of a `u128` is the coefficient of `x^j`.
// ---------------------------------------------------------------------------

#[inline]
fn gf_split(x: u128) -> [u64; 2] {
    [x as u64, (x >> 64) as u64]
}

#[inline]
fn gf_join(x: [u64; 2]) -> u128 {
    u128::from(x[0]) | (u128::from(x[1]) << 64)
}

#[inline]
fn gf_mul(a: u128, b: u128) -> u128 {
    let mut acc = [0u64; 2];
    qsag_asm::gf2_128_mul_acc_batch(&mut acc, &[gf_split(a)], &[gf_split(b)]);
    gf_join(acc)
}

fn gf_dot(a: &[u128], b: &[u128]) -> u128 {
    assert_eq!(a.len(), b.len());
    let mut acc = [0u64; 2];
    let mut ta = [[0u64; 2]; 128];
    let mut tb = [[0u64; 2]; 128];
    for (ca, cb) in a.chunks(128).zip(b.chunks(128)) {
        for (i, (x, y)) in ca.iter().zip(cb).enumerate() {
            ta[i] = gf_split(*x);
            tb[i] = gf_split(*y);
        }
        qsag_asm::gf2_128_mul_acc_batch(&mut acc, &ta[..ca.len()], &tb[..ca.len()]);
    }
    qsag_asm::volatile_fill(&mut ta, [0; 2]);
    qsag_asm::volatile_fill(&mut tb, [0; 2]);
    gf_join(acc)
}

#[inline]
fn gf_mul_x(v: u128) -> u128 {
    (v << 1) ^ (0x87 & 0u128.wrapping_sub(v >> 127))
}

/// `dst[i] ^= scalar * src[i]`; constant time in all three operands.
#[inline]
fn gf_scale_xor(dst: &mut [u128], src: &[u128], scalar: u128) {
    if !dst.is_empty() {
        qsag_asm::bitslice::gf2_128_scale_xor(dst, src, scalar);
    }
}

#[inline]
fn bit_mask(bit: u64) -> u128 {
    0u128.wrapping_sub(u128::from(black_box(bit) & 1))
}

#[inline]
fn word_bit(words: &[u64], k: usize) -> u64 {
    (words[k / 64] >> (k % 64)) & 1
}

/// The `x^j` basis, so that `gf_dot(bits_as_rows, POWERS)` recombines 128 authenticated bits.
const POWERS: [u128; 128] = {
    let mut out = [0u128; 128];
    let mut j = 0;
    while j < 128 {
        out[j] = 1u128 << j;
        j += 1;
    }
    out
};

fn stream_words(mid: &[u64; 25], parts: &[&[u8]], out: &mut [u64]) {
    let mut seed = [0u8; 128];
    let mut len = 0usize;
    for part in parts {
        seed[len..len + part.len()].copy_from_slice(part);
        len += part.len();
    }
    Cshake256WordStream4::new(mid, &seed[..len]).fill_words(out);
    wipe_bytes(&mut seed);
}

fn absorb_transcript(transcript: &mut [u8; 32], label: &[u8], data: &[u8]) {
    let prev = *transcript;
    *transcript = cshake256_32_multi_frame(b"QSAG.TRIPLE.F2.TRANSCRIPT/v1", &[&prev, label, data]);
}

fn lane_coins(coin: &[u8; 32]) -> [u128; 2] {
    core::array::from_fn(|lane| u128::from_le_bytes(core::array::from_fn(|i| coin[16 * lane + i])))
}

// ---------------------------------------------------------------------------
// Correlated-OT pool: authenticated bits under each party's MAC-key share.
// ---------------------------------------------------------------------------

struct PairExtension {
    holder: usize,
    owner: usize,
    owner_slices: SecretBuffer<Vec<[[u8; 32]; 4]>>,
    holder_punctured: SecretBuffer<Vec<[[u8; 32]; 4]>>,
    chi_seed: [u8; 32],
    /// `(owner rows, holder rows)`, lane-major.
    rows: Option<Result<PairRows, PreprocessError>>,
}

/// One ceremony's pool of correlated-OT rows. Row `k` of pair (holder `i`, owner `p`) satisfies
/// `owner_row ^ holder_row = rho_p[k] * alpha_i` in both lanes, where `rho_p` are the owner's
/// uniformly random choice bits. A bit `x` is authenticated by publishing `d = x ^ rho_p[k]`.
pub(super) struct DeltaCotPool {
    n: usize,
    rows: usize,
    pair_rows: usize,
    pair_cursor: usize,
    cursor: usize,
    delta: SecretBuffer<Vec<Row>>,
    rho: SecretBuffer<Vec<Vec<u64>>>,
    /// `agg[P][lane][k]`: XOR of `P`'s rows as owner and as holder over all its pairs.
    agg: SecretBuffer<Vec<[Vec<u128>; 2]>>,
    /// `[holder][owner][lane][k]` for `k < pair_rows`.
    owner_rows: SecretBuffer<Vec<Vec<[Vec<u128>; 2]>>>,
    holder_rows: SecretBuffer<Vec<Vec<[Vec<u128>; 2]>>>,
}

/// A pool after its base OTs and before local extension. See [`DeltaCotPool::bootstrap`].
pub(super) struct PoolBoot {
    n: usize,
    rows: usize,
    pair_rows: usize,
    delta: SecretBuffer<Vec<Row>>,
    rho: SecretBuffer<Vec<Vec<u64>>>,
    jobs: Vec<PairExtension>,
}

fn stream_words_pair(
    mid: &[u64; 25],
    parts0: &[&[u8]],
    out0: &mut [u64],
    parts1: &[&[u8]],
    out1: &mut [u64],
) {
    let mut seed0 = [0u8; 128];
    let mut len0 = 0usize;
    for part in parts0 {
        seed0[len0..len0 + part.len()].copy_from_slice(part);
        len0 += part.len();
    }
    let mut seed1 = [0u8; 128];
    let mut len1 = 0usize;
    for part in parts1 {
        seed1[len1..len1 + part.len()].copy_from_slice(part);
        len1 += part.len();
    }
    Cshake256WordStream4::fill_words_pair(mid, &seed0[..len0], out0, &seed1[..len1], out1);
    wipe_bytes(&mut seed0);
    wipe_bytes(&mut seed1);
}

fn extend_pair(
    session_id: &[u8; 32],
    job: &PairExtension,
    rho: &[u64],
    delta: Row,
    rows: usize,
) -> Result<PairRows, PreprocessError> {
    let words = rho.len();
    let payload_words = words - SACRIFICIAL_ROWS / 64;
    debug_assert_eq!(rows, 64 * payload_words);
    let holder_le = (job.holder as u64).to_le_bytes();
    let owner_le = (job.owner as u64).to_le_bytes();

    // SoftSpokenOT (n_C = 256, k = 2) over 128 F_4 slices:
    // Owner expands 4 streams `g0..g3` per slice `j`, locks `u_j = g0 ^ g1 ^ g2 ^ g3 ^ rho`
    // (`128` columns), and forms `t_{0, j} = g2 ^ g3` (lane 0) and `t_{1, j} = g1 ^ g3` (lane 1).
    // Holder expands its 3 non-punctured leaves (`v* = 2 * b0 + b1` zeroed in constant time) and
    // computes `q_{0, j} = g2 ^ g3 ^ (mask(b0) & w_j)` and `q_{1, j} = g1 ^ g3 ^ (mask(b1) & w_j)`.
    let mut t_lo_cols = SecretBuffer(Vec::<Vec<u64>>::with_capacity(128));
    let mut t_hi_cols = SecretBuffer(Vec::<Vec<u64>>::with_capacity(128));
    let mut q_lo_cols = SecretBuffer(Vec::<Vec<u64>>::with_capacity(128));
    let mut q_hi_cols = SecretBuffer(Vec::<Vec<u64>>::with_capacity(128));
    let mut g0 = SecretBuffer(vec![0u64; words]);
    let mut g1 = SecretBuffer(vec![0u64; words]);
    let mut g2 = SecretBuffer(vec![0u64; words]);
    let mut g3 = SecretBuffer(vec![0u64; words]);
    let mut h0 = SecretBuffer(vec![0u64; words]);
    let mut h1 = SecretBuffer(vec![0u64; words]);
    let mut h2 = SecretBuffer(vec![0u64; words]);
    let mut h3 = SecretBuffer(vec![0u64; words]);

    for j in 0..128 {
        let l0_le = ((4 * j) as u64).to_le_bytes();
        let l1_le = ((4 * j + 1) as u64).to_le_bytes();
        let l2_le = ((4 * j + 2) as u64).to_le_bytes();
        let l3_le = ((4 * j + 3) as u64).to_le_bytes();
        let o_slice = &job.owner_slices[j];
        let h_slice = &job.holder_punctured[j];
        stream_words_pair(
            &ABIT_COL_MID,
            &[session_id, &holder_le, &owner_le, &l0_le, &o_slice[0]],
            &mut g0,
            &[session_id, &holder_le, &owner_le, &l1_le, &o_slice[1]],
            &mut g1,
        );
        stream_words_pair(
            &ABIT_COL_MID,
            &[session_id, &holder_le, &owner_le, &l2_le, &o_slice[2]],
            &mut g2,
            &[session_id, &holder_le, &owner_le, &l3_le, &o_slice[3]],
            &mut g3,
        );
        stream_words_pair(
            &ABIT_COL_MID,
            &[session_id, &holder_le, &owner_le, &l0_le, &h_slice[0]],
            &mut h0,
            &[session_id, &holder_le, &owner_le, &l1_le, &h_slice[1]],
            &mut h1,
        );
        stream_words_pair(
            &ABIT_COL_MID,
            &[session_id, &holder_le, &owner_le, &l2_le, &h_slice[2]],
            &mut h2,
            &[session_id, &holder_le, &owner_le, &l3_le, &h_slice[3]],
            &mut h3,
        );

        let b0 = ((black_box(delta[0]) >> j) & 1) as u64;
        let b1 = ((black_box(delta[1]) >> j) & 1) as u64;
        let v_star = ((b0 as u8) << 1) | (b1 as u8);
        for (v, hv) in [&mut *h0, &mut *h1, &mut *h2, &mut *h3]
            .into_iter()
            .enumerate()
        {
            let diff = black_box((v as u8) ^ v_star);
            let is_neq = (((diff | diff.wrapping_neg()) >> 7) & 1) as u64;
            let keep = 0u64.wrapping_sub(is_neq);
            for w in hv.iter_mut() {
                *w &= keep;
            }
        }
        let m0 = 0u64.wrapping_sub(b0);
        let m1 = 0u64.wrapping_sub(b1);

        let mut t_lo = vec![0u64; words];
        let mut t_hi = vec![0u64; words];
        let mut q_lo = vec![0u64; words];
        let mut q_hi = vec![0u64; words];
        for w in 0..words {
            let u_w = g0[w] ^ g1[w] ^ g2[w] ^ g3[w] ^ rho[w];
            let w_corr = u_w ^ h0[w] ^ h1[w] ^ h2[w] ^ h3[w];
            t_lo[w] = g2[w] ^ g3[w];
            t_hi[w] = g1[w] ^ g3[w];
            q_lo[w] = h2[w] ^ h3[w] ^ (m0 & w_corr);
            q_hi[w] = h1[w] ^ h3[w] ^ (m1 & w_corr);
        }
        t_lo_cols.push(t_lo);
        t_hi_cols.push(t_hi);
        q_lo_cols.push(q_lo);
        q_hi_cols.push(q_hi);
    }
    drop((g0, g1, g2, g3, h0, h1, h2, h3));

    // SoftSpokenOT `[X | I_256]` per-column consistency check across all 256 columns individually!
    let mut chi_mask_words = [0u64; 4];
    stream_words(
        &ABIT_CHI_MID,
        &[session_id, &holder_le, &owner_le],
        &mut chi_mask_words,
    );
    let mut check_seed = job.chi_seed;
    for (i, w) in chi_mask_words.iter().enumerate() {
        let b = w.to_le_bytes();
        for k in 0..8 {
            check_seed[8 * i + k] ^= b[k];
        }
    }
    wipe_u64s(&mut chi_mask_words);
    let key = OtExtCheckKey::new(&check_seed, payload_words);
    wipe_bytes32(&mut check_seed);

    let x_hash = key.hash(rho);
    let mut diff = 0u128;
    for j in 0..128 {
        let t0_h = key.hash(&t_lo_cols[j]);
        let q0_h = key.hash(&q_lo_cols[j]);
        let t1_h = key.hash(&t_hi_cols[j]);
        let q1_h = key.hash(&q_hi_cols[j]);
        let m0 = 0u128.wrapping_sub((black_box(delta[0]) >> j) & 1);
        let m1 = 0u128.wrapping_sub((black_box(delta[1]) >> j) & 1);
        for lane in 0..2 {
            diff |= q0_h[lane] ^ t0_h[lane] ^ (m0 & x_hash[lane]);
            diff |= q1_h[lane] ^ t1_h[lane] ^ (m1 & x_hash[lane]);
        }
    }
    if black_box(diff) != 0 {
        drop((t_lo_cols, t_hi_cols, q_lo_cols, q_hi_cols));
        return Err(PreprocessError::KosOtCheckFailed {
            sender_id: job.holder,
            receiver_id: job.owner,
        });
    }

    let t_lanes: [Vec<u128>; 2] = [
        transpose_cols128_to_rows(&t_lo_cols, payload_words),
        transpose_cols128_to_rows(&t_hi_cols, payload_words),
    ];
    let q_lanes: [Vec<u128>; 2] = [
        transpose_cols128_to_rows(&q_lo_cols, payload_words),
        transpose_cols128_to_rows(&q_hi_cols, payload_words),
    ];
    drop((t_lo_cols, t_hi_cols, q_lo_cols, q_hi_cols));
    Ok((t_lanes, q_lanes))
}

impl DeltaCotPool {
    /// Extend `rows` authenticated-bit rows per ordered pair under `alpha_contribs`. The first
    /// `pair_rows` rows keep their per-pair halves for hashed products.
    pub(super) fn establish(
        session_id: &[u8; 32],
        ot_mesh: &mut OtMesh,
        alpha_contribs: &[[Tower128; 2]],
        rows: usize,
        pair_rows: usize,
        party_rngs: &mut [PartyPrivateRng],
    ) -> Result<Self, PreprocessError> {
        let boot = Self::bootstrap(ot_mesh, alpha_contribs, rows, pair_rows, party_rngs)?;
        Self::extend(session_id, boot)
    }

    /// The interactive part of [`Self::establish`] that needs the shared OT mesh: every party's
    /// choice bits `rho`, and per ordered pair the 256 base OTs whose choice bits are the
    /// holder's `alpha_i`. Everything after this is local expansion of what it returns.
    pub(super) fn bootstrap(
        ot_mesh: &mut OtMesh,
        alpha_contribs: &[[Tower128; 2]],
        rows: usize,
        pair_rows: usize,
        party_rngs: &mut [PartyPrivateRng],
    ) -> Result<PoolBoot, PreprocessError> {
        let n = ot_mesh.n;
        let rows = rows.div_ceil(64) * 64;
        let words = (rows + SACRIFICIAL_ROWS) / 64;
        let delta = SecretBuffer(
            alpha_contribs
                .iter()
                .map(|a| [a[0].0, a[1].0])
                .collect::<Vec<Row>>(),
        );
        let mut rho = SecretBuffer(vec![vec![0u64; words]; n]);
        for (p, words_p) in rho.iter_mut().enumerate() {
            for w in words_p.iter_mut() {
                *w = party_rngs[p].next_u64();
            }
        }

        // Pre-draw per-channel RNG inputs in canonical `(holder, owner)` order, then run all
        // `n * (n - 1)` correlated OT channels in parallel across threads.
        struct PairBootstrapJob {
            holder: usize,
            owner: usize,
            choice: [u64; 4],
            sac_words: [u64; 4],
            kos_chi_seed: [u8; 32],
            chi_seed: [u8; 32],
            s_chan: Option<crate::preprocessing::OtExtSenderChannel>,
            r_chan: Option<crate::preprocessing::OtExtReceiverChannel>,
            /// Binding of the batch's wire messages, for the mesh transcript.
            bind: [u8; 32],
            outcome: Option<Result<PairExtension, PreprocessError>>,
        }
        let mut boot_jobs = Vec::with_capacity(n * (n - 1));
        for holder in 0..n {
            let choice = [
                delta[holder][0] as u64,
                (delta[holder][0] >> 64) as u64,
                delta[holder][1] as u64,
                (delta[holder][1] >> 64) as u64,
            ];
            for owner in 0..n {
                if owner == holder {
                    continue;
                }
                let s_chan = ot_mesh
                    .senders
                    .get_mut(owner)
                    .and_then(|row| row.get_mut(holder))
                    .and_then(Option::take)
                    .ok_or(PreprocessError::ChannelPoisoned {
                        sender_id: owner,
                        receiver_id: holder,
                    })?;
                let r_chan = ot_mesh
                    .receivers
                    .get_mut(holder)
                    .and_then(|row| row.get_mut(owner))
                    .and_then(Option::take)
                    .ok_or(PreprocessError::ChannelPoisoned {
                        sender_id: owner,
                        receiver_id: holder,
                    })?;
                let sac_words = [
                    party_rngs[holder].next_u64(),
                    party_rngs[holder].next_u64(),
                    party_rngs[holder].next_u64(),
                    party_rngs[holder].next_u64(),
                ];
                let kos_chi_seed = party_rngs[owner].next_bytes32();
                let chi_seed = party_rngs[holder].next_bytes32();
                boot_jobs.push(PairBootstrapJob {
                    holder,
                    owner,
                    choice,
                    sac_words,
                    kos_chi_seed,
                    chi_seed,
                    s_chan: Some(s_chan),
                    r_chan: Some(r_chan),
                    bind: [0u8; 32],
                    outcome: None,
                });
            }
        }

        par_for_each(&mut boot_jobs, |bjob| {
            let s_chan = bjob.s_chan.as_mut().expect("sender channel taken");
            let r_chan = bjob.r_chan.as_mut().expect("receiver channel taken");
            let bind = &mut bjob.bind;
            let mut run = || -> Result<PairExtension, PreprocessError> {
                let (r_pend, u_msg) =
                    r_chan.round1_send_u_cols_with_sac(&bjob.choice, bjob.sac_words);
                let (s_pend, chal_msg) =
                    s_chan.round2_sample_challenge_with_chi(&u_msg, bjob.kos_chi_seed)?;
                let (proof_msg, recv) = r_chan.round3_prove_and_finish(r_pend, &chal_msg);
                *bind = compute_kos_transcript_bind(
                    &s_pend.u_cols_digest,
                    &s_pend.chi_seed,
                    &proof_msg,
                );
                let send = s_chan.round4_verify_and_finish(s_pend, &proof_msg)?;
                let take = |pad: &[u8; 48]| -> [u8; 32] { core::array::from_fn(|i| pad[i]) };
                let pair_sid = s_chan.session_id;
                let d0 = (bjob.choice[0] as u128) | ((bjob.choice[1] as u128) << 64);
                let d1 = (bjob.choice[2] as u128) | ((bjob.choice[3] as u128) << 64);
                let mut owner_slices = Vec::with_capacity(128);
                let mut holder_punctured = Vec::with_capacity(128);
                for j in 0..128 {
                    let r_seed = take(&send[j].0);
                    let l_seed = take(&send[j].1);
                    let k1_0 = take(&send[128 + j].0);
                    let k1_1 = take(&send[128 + j].1);
                    let (leaves, sib2) = softspoken_f4_slice_setup_receiver(
                        &pair_sid, j, &r_seed, &l_seed, &k1_0, &k1_1,
                    );
                    let sub_known = take(&recv[j]);
                    let k1_known = take(&recv[128 + j]);
                    let b0 = ((d0 >> j) & 1) as u8;
                    let b1 = ((d1 >> j) & 1) as u8;
                    let punc = softspoken_f4_slice_setup_sender_ct(
                        &pair_sid, j, b0, b1, &sub_known, &k1_known, &sib2,
                    );
                    owner_slices.push(leaves);
                    holder_punctured.push(punc);
                }
                Ok(PairExtension {
                    holder: bjob.holder,
                    owner: bjob.owner,
                    owner_slices: SecretBuffer(owner_slices),
                    holder_punctured: SecretBuffer(holder_punctured),
                    chi_seed: bjob.chi_seed,
                    rows: None,
                })
            };
            let res = run();
            crate::wipe::wipe_u64s(&mut bjob.choice);
            crate::wipe::wipe_u64s(&mut bjob.sac_words);
            crate::wipe::wipe_bytes32(&mut bjob.kos_chi_seed);
            bjob.outcome = Some(res);
        });

        // Every channel goes back to the mesh before any failure is reported.
        let mut jobs = Vec::with_capacity(boot_jobs.len());
        let mut failure = None;
        for mut bjob in boot_jobs {
            if let Some(s_chan) = bjob.s_chan.take() {
                ot_mesh.senders[bjob.owner][bjob.holder] = Some(s_chan);
            }
            if let Some(r_chan) = bjob.r_chan.take() {
                ot_mesh.receivers[bjob.holder][bjob.owner] = Some(r_chan);
            }
            ot_mesh.absorb_batch(bjob.owner, bjob.holder, &bjob.bind);
            match bjob.outcome.take() {
                Some(Ok(ext)) => jobs.push(ext),
                Some(Err(err)) => failure = failure.or(Some(err)),
                None => unreachable!("par_for_each populated every job"),
            }
        }
        if let Some(e) = failure {
            return Err(e);
        }
        Ok(PoolBoot {
            n,
            rows,
            pair_rows,
            delta,
            rho,
            jobs,
        })
    }

    /// Local expansion of a bootstrapped pool: the per-pair column PRG, the transpose to rows
    /// and the KOS consistency check. Needs neither the OT mesh nor any party's RNG.
    pub(super) fn extend(session_id: &[u8; 32], boot: PoolBoot) -> Result<Self, PreprocessError> {
        let PoolBoot {
            n,
            rows,
            pair_rows,
            delta,
            rho,
            mut jobs,
        } = boot;
        {
            let (rho_ref, delta_ref) = (&rho, &delta);
            par_for_each(&mut jobs, |job| {
                let extended = extend_pair(
                    session_id,
                    job,
                    &rho_ref[job.owner],
                    delta_ref[job.holder],
                    rows,
                );
                job.rows = Some(extended);
            });
        }

        let mut agg: SecretBuffer<Vec<[Vec<u128>; 2]>> = SecretBuffer(
            (0..n)
                .map(|_| [vec![0u128; rows], vec![0u128; rows]])
                .collect(),
        );
        let mut owner_rows: SecretBuffer<Vec<Vec<[Vec<u128>; 2]>>> = SecretBuffer(
            (0..n)
                .map(|_| (0..n).map(|_| [Vec::new(), Vec::new()]).collect())
                .collect(),
        );
        let mut holder_rows: SecretBuffer<Vec<Vec<[Vec<u128>; 2]>>> = SecretBuffer(
            (0..n)
                .map(|_| (0..n).map(|_| [Vec::new(), Vec::new()]).collect())
                .collect(),
        );
        let mut failure = None;
        for job in &mut jobs {
            match job.rows.take() {
                Some(Ok((mut t_lanes, mut q_lanes))) => {
                    for lane in 0..2 {
                        for (dst, src) in agg[job.owner][lane].iter_mut().zip(&t_lanes[lane]) {
                            *dst ^= *src;
                        }
                        for (dst, src) in agg[job.holder][lane].iter_mut().zip(&q_lanes[lane]) {
                            *dst ^= *src;
                        }
                        wipe_u128s(&mut t_lanes[lane][pair_rows..]);
                        wipe_u128s(&mut q_lanes[lane][pair_rows..]);
                        t_lanes[lane].truncate(pair_rows);
                        q_lanes[lane].truncate(pair_rows);
                    }
                    owner_rows[job.holder][job.owner] = t_lanes;
                    holder_rows[job.holder][job.owner] = q_lanes;
                }
                Some(Err(e)) => failure = failure.or(Some(e)),
                None => failure = failure.or(Some(PreprocessError::PcgInvalidWireSeed)),
            }
        }
        if let Some(e) = failure {
            return Err(e);
        }
        Ok(Self {
            n,
            rows,
            pair_rows,
            pair_cursor: 0,
            cursor: pair_rows,
            delta,
            rho,
            agg,
            owner_rows,
            holder_rows,
        })
    }

    /// Populate a two-lane correlated-OT pool directly from two locally expanded silent
    /// [`crate::pcg_dense::DensePcgExpandedVault`] lanes per party without running interactive
    /// `KosOtExtension`. The first `b_words_prefix[p].len() * 64` bits of `rho[p]` are pinned
    /// to `b_words_prefix[p]` via 1-bit Beaver derandomization against each peer's silent
    /// Subfield-VOLE choice bits.
    pub(super) fn from_silent_pcg_vaults(
        vaults_lane0: &mut [crate::pcg_dense::DensePcgExpandedVault],
        vaults_lane1: &mut [crate::pcg_dense::DensePcgExpandedVault],
        rows: usize,
        pair_rows: usize,
        b_words_prefix: &[Vec<u64>],
        party_rngs: &mut [PartyPrivateRng],
    ) -> Result<Self, PreprocessError> {
        let n = vaults_lane0.len();
        if n < 2 || vaults_lane1.len() != n || b_words_prefix.len() != n || party_rngs.len() != n {
            return Err(PreprocessError::InvalidThreshold { t: n, n });
        }
        for p in 0..n {
            if vaults_lane0[p].party_id != p
                || vaults_lane1[p].party_id != p
                || vaults_lane0[p].num_parties != n
                || vaults_lane1[p].num_parties != n
            {
                return Err(PreprocessError::PcgInvalidWireSeed);
            }
        }
        let words = rows.div_ceil(64);
        let rows = words * 64;
        let prefix_words = b_words_prefix[0].len();
        if prefix_words > words || b_words_prefix.iter().any(|v| v.len() != prefix_words) {
            return Err(PreprocessError::InvalidThreshold { t: n, n });
        }

        let delta = SecretBuffer(
            (0..n)
                .map(|p| [vaults_lane0[p].mac_alpha().0, vaults_lane1[p].mac_alpha().0])
                .collect::<Vec<Row>>(),
        );
        let mut rho = SecretBuffer(vec![vec![0u64; words]; n]);
        for p in 0..n {
            rho[p][..prefix_words].copy_from_slice(&b_words_prefix[p]);
            for w in &mut rho[p][prefix_words..] {
                *w = party_rngs[p].next_u64();
            }
        }

        let mut agg: SecretBuffer<Vec<[Vec<u128>; 2]>> = SecretBuffer(
            (0..n)
                .map(|_| [vec![0u128; rows], vec![0u128; rows]])
                .collect(),
        );
        let mut owner_rows: SecretBuffer<Vec<Vec<[Vec<u128>; 2]>>> = SecretBuffer(
            (0..n)
                .map(|_| (0..n).map(|_| [Vec::new(), Vec::new()]).collect())
                .collect(),
        );
        let mut holder_rows: SecretBuffer<Vec<Vec<[Vec<u128>; 2]>>> = SecretBuffer(
            (0..n)
                .map(|_| (0..n).map(|_| [Vec::new(), Vec::new()]).collect())
                .collect(),
        );

        for holder in 0..n {
            for owner in 0..n {
                if holder == owner {
                    continue;
                }
                let mut t_lanes: [Vec<u128>; 2] =
                    [Vec::with_capacity(rows), Vec::with_capacity(rows)];
                let mut q_lanes: [Vec<u128>; 2] =
                    [Vec::with_capacity(rows), Vec::with_capacity(rows)];
                for (lane, vaults) in [&mut *vaults_lane0, &mut *vaults_lane1]
                    .into_iter()
                    .enumerate()
                {
                    let (mut x_words, mut macs) =
                        vaults[owner].take_subfield_vole_recv_words(holder, words)?;
                    let mut keys = vaults[holder].take_subfield_vole_send_words(owner, words)?;
                    let holder_delta = delta[holder][lane];
                    for k in 0..rows {
                        let diff_bit = word_bit(&rho[owner], k) ^ word_bit(&x_words, k);
                        let t_val = macs[k].0;
                        let q_val = keys[k].0 ^ (bit_mask(diff_bit) & holder_delta);
                        agg[owner][lane][k] ^= t_val;
                        agg[holder][lane][k] ^= q_val;
                        t_lanes[lane].push(t_val);
                        q_lanes[lane].push(q_val);
                    }
                    wipe_u64s(&mut x_words);
                    wipe_tower128(&mut macs);
                    wipe_tower128(&mut keys);
                    wipe_u128s(&mut t_lanes[lane][pair_rows..]);
                    wipe_u128s(&mut q_lanes[lane][pair_rows..]);
                    t_lanes[lane].truncate(pair_rows);
                    q_lanes[lane].truncate(pair_rows);
                }
                owner_rows[holder][owner] = t_lanes;
                holder_rows[holder][owner] = q_lanes;
            }
        }

        Ok(Self {
            n,
            rows,
            pair_rows,
            pair_cursor: 0,
            cursor: pair_rows,
            delta,
            rho,
            agg,
            owner_rows,
            holder_rows,
        })
    }

    fn alloc(&mut self, count: usize) -> Result<usize, PreprocessError> {
        let start = self.cursor;
        if count > self.rows - start {
            return Err(PreprocessError::VaultExhausted {
                kind: "authenticated bit pool",
            });
        }
        self.cursor += count;
        Ok(start)
    }

    /// Rows whose per-pair halves are retained, usable as OT choices in hashed products.
    fn alloc_pair(&mut self, count: usize) -> Result<usize, PreprocessError> {
        let start = self.pair_cursor;
        if count > self.pair_rows - start {
            return Err(PreprocessError::VaultExhausted {
                kind: "authenticated bit pool",
            });
        }
        self.pair_cursor += count;
        Ok(start)
    }

    fn rho_words(&self, party: usize, off: usize, words: usize) -> Vec<u64> {
        debug_assert_eq!(off % 64, 0);
        self.rho[party][off / 64..off / 64 + words].to_vec()
    }

    fn rho_field(&self, party: usize, off: usize) -> u128 {
        debug_assert_eq!(off % 64, 0);
        gf_join([self.rho[party][off / 64], self.rho[party][off / 64 + 1]])
    }

    /// `party`'s additive MAC share of the bit at row `k`, where `d_total` is the XOR of all
    /// owners' published derandomizers for that row (zero for a bit left random).
    #[inline]
    fn mac_bit(&self, party: usize, k: usize, lane: usize, d_total: u64) -> u128 {
        let sel = word_bit(&self.rho[party], k) ^ d_total;
        self.agg[party][lane][k] ^ (bit_mask(sel) & self.delta[party][lane])
    }

    /// Additive MAC shares of `count` bits starting at row `off`, lane-major.
    fn mac_bits(&self, party: usize, off: usize, count: usize, d_total: &[u64]) -> [Vec<u128>; 2] {
        core::array::from_fn(|lane| {
            (0..count)
                .map(|k| self.mac_bit(party, off + k, lane, word_bit(d_total, k)))
                .collect()
        })
    }

    /// Additive MAC share of the field element whose bits sit at rows `off..off + 128`.
    fn mac_field(&self, party: usize, off: usize, d_total: u128) -> Row {
        core::array::from_fn(|lane| {
            let mut rows = [0u128; 128];
            for (j, row) in rows.iter_mut().enumerate() {
                *row = self.mac_bit(party, off + j, lane, ((d_total >> j) & 1) as u64);
            }
            let mac = gf_dot(&rows, &POWERS);
            wipe_u128s(&mut rows);
            mac
        })
    }

    /// Authenticate one additively shared field element: every party publishes the XOR of its
    /// share with 128 fresh pool bits.
    fn authenticate_field(
        &mut self,
        shares: &[u128],
        transcript: &mut [u8; 32],
    ) -> Result<AuthValue, PreprocessError> {
        let off = self.alloc(128)?;
        let mut d_total = 0u128;
        for (p, share) in shares.iter().enumerate() {
            let d = *share ^ self.rho_field(p, off);
            absorb_transcript(transcript, b"field", &d.to_le_bytes());
            d_total ^= d;
        }
        Ok(AuthValue { off, d_total })
    }

    /// A block of 128 OT choices equal to the bits of each owner's `values[p]`.
    fn choose_field(&mut self, values: &[u128]) -> Result<ChoiceBlock, PreprocessError> {
        let off = self.alloc_pair(128)?;
        let d = values
            .iter()
            .enumerate()
            .map(|(p, v)| *v ^ self.rho_field(p, off))
            .collect();
        Ok(ChoiceBlock {
            off,
            d,
            y: SecretBuffer(values.to_vec()),
        })
    }

    /// Reserve the mask word of one Shamir conversion check together with its MAC shares.
    fn take_check_mask(&mut self) -> Result<CheckMask, PreprocessError> {
        let off = self.alloc(CHECK_MASK_BITS)?;
        Ok(CheckMask {
            planes: SecretBuffer(
                (0..self.n)
                    .map(|p| core::array::from_fn(|pl| self.rho[p][off / 64 + pl]))
                    .collect(),
            ),
            // Lane `bit` of the word is the `GF(256)` element with bit `pl` in plane `pl`.
            macs: SecretBuffer(
                (0..self.n)
                    .map(|p| {
                        core::array::from_fn(|lane| {
                            core::array::from_fn(|bit| {
                                let mut acc = Tower128::ZERO;
                                for pl in 0..8 {
                                    let mac = self.mac_bit(p, off + 64 * pl + bit, lane, 0);
                                    acc = acc.add(Tower128(mac).mul_gf256(TowerGf256(1u8 << pl)));
                                }
                                acc.0
                            })
                        })
                    })
                    .collect(),
            ),
        })
    }

    /// What `owner` and `holder` each hold of the pairwise MAC on the 128 choice bits of
    /// `block`: the two differ by `choice * delta_holder` in each lane.
    fn choice_tags(&self, holder: usize, owner: usize, block: &ChoiceBlock) -> (Row, Row) {
        let t = &self.owner_rows[holder][owner];
        let q = &self.holder_rows[holder][owner];
        let range = block.off..block.off + 128;
        (
            core::array::from_fn(|lane| gf_dot(&t[lane][range.clone()], &POWERS)),
            core::array::from_fn(|lane| {
                gf_dot(&q[lane][range.clone()], &POWERS)
                    ^ gf_mul(block.d[owner], self.delta[holder][lane])
            }),
        )
    }

    /// A uniformly random additively shared field element, usable as OT choices and carrying
    /// MAC shares `mac_field(party, off, 0)`.
    fn random_field(&mut self) -> Result<ChoiceBlock, PreprocessError> {
        let off = self.alloc_pair(128)?;
        let y = (0..self.n).map(|p| self.rho_field(p, off)).collect();
        Ok(ChoiceBlock {
            off,
            d: vec![0u128; self.n],
            y: SecretBuffer(y),
        })
    }
}

/// Public handle of an authenticated field element.
#[derive(Clone, Copy)]
struct AuthValue {
    off: usize,
    d_total: u128,
}

/// Every party's share of the mask word of one Shamir conversion check: the word as eight
/// bit planes and the additive MAC share of each of its 64 `GF(256)` lanes.
pub(super) struct CheckMask {
    planes: SecretBuffer<Vec<BitslicedGf256x64>>,
    macs: SecretBuffer<Vec<[[u128; 64]; 2]>>,
}

/// 128 pool rows used as OT choices. `d[p]` is owner `p`'s public derandomizer and `y[p]` its
/// private choice value.
struct ChoiceBlock {
    off: usize,
    d: Vec<u128>,
    y: SecretBuffer<Vec<u128>>,
}
// ---------------------------------------------------------------------------
// Recursive sacrifice.
// ---------------------------------------------------------------------------

/// Deviations a test can inject at each point where a party acts on its own shares.
#[derive(Default)]
pub(super) struct PiTripleF2Faults<'a> {
    /// `(party, c words)`: the party's XOR share of the products, before it is authenticated.
    pub(super) product_shares: Option<&'a mut ProductTamper<'a>>,
    /// `(round, party, [instance][h0, h1])`: the party's cross-term shares of one fold round,
    /// before they are authenticated.
    pub(super) fold_shares: Option<&'a mut FoldTamper<'a>>,
    /// `(round, party, choice)`: what the party feeds a chosen-choice product in place of its
    /// share of the folded `b` entry (`round` is the round count for the base case).
    pub(super) choice_values: Option<&'a mut ChoiceTamper<'a>>,
    /// `(party, packed shares)`: the party's shares of the combine openings, 128 bits a word.
    pub(super) combine_shares: Option<&'a mut OpeningTamper<'a>>,
    /// `(party, a shares, c shares)`: the Shamir value shares of the final triples the party
    /// ends up holding.
    pub(super) shamir_shares: Option<&'a mut WordTamper<'a>>,
    /// `(party, a MAC shares)`: the Shamir MAC shares of the final triples the party ends up
    /// holding.
    pub(super) mac_shares: Option<&'a mut MacTamper<'a>>,
}

impl PiTripleF2Faults<'_> {
    fn acts_on_raw(&self) -> bool {
        self.product_shares.is_some() || self.fold_shares.is_some() || self.choice_values.is_some()
    }
}
// ---------------------------------------------------------------------------
// Raw ceremonies: authenticated bits, products and the sacrifice.
// ---------------------------------------------------------------------------

/// Additively shared authenticated bit triples, indexed `[a, b, c]`: value shares
/// `bits[which][party][word]` and MAC shares `macs[which][party][lane][64 * word + bit]`.
pub(super) struct BitTriples {
    pub(super) bits: [SecretBuffer<Vec<Vec<u64>>>; 3],
    pub(super) macs: [SecretBuffer<Vec<[Vec<u128>; 2]>>; 3],
}

impl BitTriples {
    fn words(&self) -> usize {
        self.bits[0][0].len()
    }
}

/// Private inputs to the final sacrifice opening. Workers return these without
/// publishing sigma; the coordinator checks them on the existing monotone mesh.
struct PendingSacrifice {
    shares: SecretBuffer<Vec<Vec<u128>>>,
    macs: SecretBuffer<Vec<Vec<Row>>>,
}

struct UncheckedRawBatch {
    batch: RawBatch,
    sacrifice: PendingSacrifice,
}

impl UncheckedRawBatch {
    fn check(
        self,
        session_id: &[u8; 32],
        mesh: &mut OtMesh,
        party_rngs: &mut [PartyPrivateRng],
    ) -> Result<RawBatch, PreprocessError> {
        let opened = open_additive_authenticated(
            session_id,
            "pi_triple_f2_sacrifice",
            &self.sacrifice.shares,
            &self.sacrifice.macs,
            &self.batch.delta,
            mesh,
            party_rngs,
        )?;
        for inst in 0..2 {
            if opened[3 * inst + 2] != gf_mul(opened[3 * inst], opened[3 * inst + 1]) {
                return Err(PreprocessError::SacrificeResidualNonZero {
                    phase: "pi_triple_f2",
                });
            }
        }
        let mut batch = self.batch;
        absorb_transcript(
            &mut batch.transcript,
            b"mac-blind",
            &mesh.transcript_digest(),
        );
        Ok(batch)
    }
}

/// One ceremony's raw triples after its sacrifice has accepted.
struct RawBatch {
    triples: BitTriples,
    mask: CheckMask,
    delta: SecretBuffer<Vec<Row>>,
    transcript: [u8; 32],
}

/// Raw ceremonies never exceed this many words, which keeps the fold plan at three rate blocks
/// per hashed row and one ceremony's transient rows and pads near 1 GiB.
const RAW_CEREMONY_WORDS: usize = 3072;

/// Ceremonies run side by side. Each batch bootstraps its ceremonies in order, runs the
/// private work concurrently, then checks final sacrifice openings in order on the shared
/// mesh. A third concurrent ceremony bought under 10% of wall time for 20% more CPU.
const MAX_CONCURRENT_CEREMONIES: usize = 2;

/// Final triples of one combine pool. 8,192 words gives arity 3 (see [`combine::combine_arity`]);
/// smaller pools such as 7,720 words adaptively require arity >= 4. Larger requests are
/// split into pools of this size or more so the raw shares held for one combine stay bounded.
const POOL_WORDS: usize = 8192;

// ---------------------------------------------------------------------------
// The triple protocol.
// ---------------------------------------------------------------------------

fn derive_session(label: &[u8], session_id: &[u8; 32], index: usize) -> [u8; 32] {
    cshake256_32_multi_frame(label, &[session_id, &(index as u64).to_be_bytes()])
}

/// Sizes of the combine pools serving `words` final words: one pool below `2 * POOL_WORDS`,
/// otherwise equal pools of at least `POOL_WORDS`.
fn pool_sizes(words: usize) -> Vec<usize> {
    let pools = (words / POOL_WORDS).max(1);
    let (whole, extra) = PublicDivisor::new(pools).split(words);
    (0..pools).map(|i| whole + usize::from(i < extra)).collect()
}

/// `out_words` final additive triples from one combine pool: as many equal KOS-backed raw
/// ceremonies as the combine needs, all under the MAC key `alpha_contribs`, then the combine.
/// Every ceremony draws from its own substream of each party's RNG, forked in ceremony order,
/// so the result does not depend on scheduling. No ceremony is larger than `ceremony_words`
/// raw words. The hooks of `faults` that act inside a raw ceremony apply to the pool's first
/// ceremony.
fn additive_pool(
    session_id: [u8; 32],
    out_words: usize,
    ceremony_words: usize,
    alpha_contribs: &[[Tower128; 2]],
    ot_mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
    faults: &mut PiTripleF2Faults<'_>,
) -> Result<(BitTriples, CheckMask, [u8; 32]), PreprocessError> {
    struct Ceremony {
        session_id: [u8; 32],
        boot: Option<PoolBoot>,
        rngs: Vec<PartyPrivateRng>,
        raw: Option<Result<UncheckedRawBatch, PreprocessError>>,
    }
    let n = ot_mesh.n;
    let (raw_words, _, _) = combine_shape(out_words, Leak::ChoiceSide);
    let count = PublicDivisor::new(ceremony_words).ceil(raw_words);
    let plan = FoldPlan::new(64 * PublicDivisor::new(count).ceil(raw_words))?;
    let concurrent_ceremonies = (PublicDivisor::new((n * (n - 1)).max(1))
        .split(worker_count())
        .0)
        .clamp(1, MAX_CONCURRENT_CEREMONIES);

    let mut batches = Vec::with_capacity(count);
    let mut first = 0;
    while first < count {
        let mut ceremonies = Vec::with_capacity(concurrent_ceremonies);
        for index in first..count.min(first + concurrent_ceremonies) {
            let boot = DeltaCotPool::bootstrap(
                ot_mesh,
                alpha_contribs,
                plan.pool_rows(),
                plan.pair_rows(),
                party_rngs,
            )?;
            let rngs = party_rngs
                .iter_mut()
                .map(|rng| {
                    PartyPrivateRng::from_seed(
                        rng.next_bytes32(),
                        b"QSAG.TRIPLE.F2.CEREMONY.RNG/v1",
                    )
                })
                .collect();
            ceremonies.push(Ceremony {
                session_id: derive_session(b"QSAG.TRIPLE.F2.CEREMONY/v1", &session_id, index),
                boot: Some(boot),
                rngs,
                raw: None,
            });
        }
        // The pool's first ceremony runs on this thread when it is alone or carries the hooks.
        let inline = usize::from(first == 0 && (count == 1 || faults.acts_on_raw()));
        for ceremony in &mut ceremonies[..inline] {
            let boot = ceremony.boot.take().expect("bootstrapped above");
            ceremony.raw = Some(raw_ceremony(
                ceremony.session_id,
                &plan,
                boot,
                &mut ceremony.rngs,
                faults,
            ));
        }
        {
            let plan = &plan;
            par_for_each_nested(&mut ceremonies[inline..], |ceremony| {
                let boot = ceremony.boot.take().expect("bootstrapped above");
                ceremony.raw = Some(raw_ceremony(
                    ceremony.session_id,
                    plan,
                    boot,
                    &mut ceremony.rngs,
                    &mut PiTripleF2Faults::default(),
                ));
            });
        }
        for ceremony in &mut ceremonies {
            let raw = ceremony.raw.take().expect("every ceremony ran")?;
            batches.push(raw.check(&ceremony.session_id, ot_mesh, &mut ceremony.rngs)?);
        }
        first += ceremonies.len();
    }

    let mut transcript = session_id;
    for batch in &batches {
        absorb_transcript(&mut transcript, b"ceremony", &batch.transcript);
    }
    let views: Vec<&BitTriples> = batches.iter().map(|batch| &batch.triples).collect();
    let combined = combine_raw(
        &session_id,
        Leak::ChoiceSide,
        out_words,
        &views,
        &batches[0].delta,
        &mut transcript,
        ot_mesh,
        party_rngs,
        faults,
    )?;
    let RawBatch { mask, .. } = batches.swap_remove(0);
    Ok((combined, mask, transcript))
}

/// Deal degree-`< t` Shamir shares of final additive triples and their MACs, check them under
/// `Π_MAC` and pack them into vault triples appended to `out[party]`.
#[expect(
    clippy::too_many_arguments,
    reason = "Quorum, key shares, shares and private randomness are separate protocol inputs"
)]
fn shamir_triples(
    session_id: &[u8; 32],
    t: usize,
    eval_points: &[TowerGf256],
    alpha_shamir: &[[Tower128; 2]],
    mask: CheckMask,
    triples: BitTriples,
    transcript: &[u8; 32],
    party_rngs: &mut [PartyPrivateRng],
    faults: &mut PiTripleF2Faults<'_>,
    out: &mut [Vec<KeccakBitTripleShare64>],
) -> Result<(), PreprocessError> {
    let n = eval_points.len();
    let words = triples.words();
    // Laid out `a | b | c`.
    let all_bits = SecretBuffer(
        (0..n)
            .map(|p| {
                [
                    &triples.bits[0][p][..],
                    &triples.bits[1][p][..],
                    &triples.bits[2][p][..],
                ]
                .concat()
            })
            .collect::<Vec<_>>(),
    );
    let all_macs: SecretBuffer<Vec<[Vec<u128>; 2]>> = SecretBuffer(
        (0..n)
            .map(|p| {
                core::array::from_fn(|lane| {
                    [
                        &triples.macs[0][p][lane][..],
                        &triples.macs[1][p][lane][..],
                        &triples.macs[2][p][lane][..],
                    ]
                    .concat()
                })
            })
            .collect(),
    );
    drop(triples);
    let (words_sh, macs_sh) = convert_to_shamir_and_check(
        session_id,
        t,
        eval_points,
        alpha_shamir,
        mask,
        &all_bits,
        &all_macs,
        transcript,
        party_rngs,
        &mut |shares, macs| {
            for p in 0..n {
                if let Some(hook) = faults.shamir_shares.as_mut() {
                    let (a_part, rest) = shares[p].split_at_mut(words);
                    hook(p, a_part, &mut rest[words..]);
                }
                if let Some(hook) = faults.mac_shares.as_mut() {
                    hook(p, &mut macs[p][..words]);
                }
            }
        },
    )?;
    drop((all_bits, all_macs));
    let words_sh = SecretBuffer(words_sh);
    let macs_sh = SecretBuffer(macs_sh);
    for p in 0..n {
        out[p].reserve(words);
        for k in 0..words {
            out[p].push(KeccakBitTripleShare64 {
                a: words_sh[p][k],
                b: words_sh[p][words + k],
                c: words_sh[p][2 * words + k],
                a_mac: macs_sh[p][k],
                b_mac: macs_sh[p][words + k],
                c_mac: macs_sh[p][2 * words + k],
            });
        }
    }
    Ok(())
}

fn vaults_from(
    eval_points: &[TowerGf256],
    alpha_shamir: &[[Tower128; 2]],
    triples: Vec<Vec<KeccakBitTripleShare64>>,
) -> Vec<PreprocessedKeccakPartyVault> {
    triples
        .into_iter()
        .enumerate()
        .map(|(p, triples)| PreprocessedKeccakPartyVault {
            party_id: p,
            eval_point: eval_points[p],
            mac_alpha_lanes: alpha_shamir[p],
            triples,
            cursor: 0,
            poisoned: false,
        })
        .collect()
}

/// Runs `Π_triple_f2` for `num_triples` final words in degree-`< t` Shamir form, and returns
/// with the vaults a digest chaining every broadcast of the run.
#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the public preprocessing API used by other protocol modules"
)]
pub(super) fn run_pi_triple_f2(
    session_id: [u8; 32],
    t: usize,
    eval_points: &[TowerGf256],
    num_triples: usize,
    alpha_contribs: &[[Tower128; 2]],
    alpha_shamir: &[[Tower128; 2]],
    ot_mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
    faults: &mut PiTripleF2Faults<'_>,
) -> Result<(Vec<PreprocessedKeccakPartyVault>, [u8; 32]), PreprocessError> {
    let n = eval_points.len();
    let mut out: Vec<Vec<KeccakBitTripleShare64>> =
        (0..n).map(|_| Vec::with_capacity(num_triples)).collect();
    let mut transcript = session_id;
    for (index, words) in pool_sizes(num_triples).into_iter().enumerate() {
        let pool_sid = derive_session(b"QSAG.TRIPLE.F2.POOL/v1", &session_id, index);
        let (triples, mask, pool_transcript) = additive_pool(
            pool_sid,
            words,
            RAW_CEREMONY_WORDS,
            alpha_contribs,
            ot_mesh,
            party_rngs,
            faults,
        )?;
        absorb_transcript(&mut transcript, b"pool", &pool_transcript);
        shamir_triples(
            &pool_sid,
            t,
            eval_points,
            alpha_shamir,
            mask,
            triples,
            &pool_transcript,
            party_rngs,
            faults,
            &mut out,
        )?;
    }
    Ok((vaults_from(eval_points, alpha_shamir, out), transcript))
}

/// Runs `Π_triple_f2` for `num_words` final words and stops before the Shamir conversion: the
/// parties keep additive (`n`-of-`n`) shares of the bits and of their two-lane MACs under
/// `alpha_contribs`. Returns the triples and a digest chaining every broadcast of the run.
pub(super) fn run_pi_triple_f2_additive(
    session_id: [u8; 32],
    num_words: usize,
    alpha_contribs: &[[Tower128; 2]],
    ot_mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
    faults: &mut PiTripleF2Faults<'_>,
) -> Result<(BitTriples, [u8; 32]), PreprocessError> {
    let n = ot_mesh.n;
    let mut all = BitTriples {
        bits: core::array::from_fn(|_| crate::wipe::secret_vecs_with_capacity(n, num_words)),
        macs: core::array::from_fn(|_| {
            SecretBuffer(
                (0..n)
                    .map(|_| core::array::from_fn(|_| Vec::with_capacity(64 * num_words)))
                    .collect(),
            )
        }),
    };
    let mut transcript = session_id;
    for (index, words) in pool_sizes(num_words).into_iter().enumerate() {
        let pool_sid = derive_session(b"QSAG.TRIPLE.F2.POOL/v1", &session_id, index);
        let (mut triples, _mask, pool_transcript) = additive_pool(
            pool_sid,
            words,
            RAW_CEREMONY_WORDS,
            alpha_contribs,
            ot_mesh,
            party_rngs,
            faults,
        )?;
        absorb_transcript(&mut transcript, b"pool", &pool_transcript);
        for which in 0..3 {
            for p in 0..n {
                all.bits[which][p].append(&mut triples.bits[which][p]);
                for lane in 0..2 {
                    all.macs[which][p][lane].append(&mut triples.macs[which][p][lane]);
                }
            }
        }
    }
    Ok((all, transcript))
}

/// Authenticate, sacrifice, combine and Shamir-convert silent Boolean Beaver triples drawn from
/// locally expanded [`crate::pcg_dense::DensePcgExpandedVault`]s. Blinded MAC checks reuse
/// `mesh` when supplied; standalone materialization establishes one mesh for all checks.
/// The vaults must hold the raw words [`silent_raw_words`] gives for `num_triples`.
#[expect(
    clippy::too_many_arguments,
    reason = "Silent PCG vaults, threshold evaluation points, MAC shares and private RNGs are distinct protocol inputs"
)]
pub(super) fn run_silent_pi_triple_f2(
    session_id: [u8; 32],
    t: usize,
    eval_points: &[TowerGf256],
    num_triples: usize,
    alpha_shamir: &[[Tower128; 2]],
    vaults_lane0: &mut [crate::pcg_dense::DensePcgExpandedVault],
    vaults_lane1: &mut [crate::pcg_dense::DensePcgExpandedVault],
    mesh: Option<&mut OtMesh>,
    party_rngs: &mut [PartyPrivateRng],
    faults: &mut PiTripleF2Faults<'_>,
) -> Result<Vec<PreprocessedKeccakPartyVault>, PreprocessError> {
    let n = eval_points.len();
    let mut owned_mesh;
    let mesh = match mesh {
        Some(mesh) => mesh,
        None => {
            let blind_sid = derive_session(b"QSAG.TRIPLE.F2.SILENT.BLIND/v1", &session_id, 0);
            owned_mesh = OtMesh::establish(blind_sid, party_rngs)?;
            &mut owned_mesh
        }
    };
    let plan = FoldPlan::new(64 * silent_raw_words(num_triples))?;
    let RawBatch {
        triples: raw,
        mask,
        delta,
        mut transcript,
    } = raw_silent_ceremony(
        session_id,
        &plan,
        vaults_lane0,
        vaults_lane1,
        party_rngs,
        faults,
    )?
    .check(&session_id, mesh, party_rngs)?;
    let combined = combine_raw(
        &session_id,
        Leak::BothFactors,
        num_triples,
        &[&raw],
        &delta,
        &mut transcript,
        mesh,
        party_rngs,
        faults,
    )?;
    drop((raw, delta));
    let mut out: Vec<Vec<KeccakBitTripleShare64>> = (0..n).map(|_| Vec::new()).collect();
    shamir_triples(
        &session_id,
        t,
        eval_points,
        alpha_shamir,
        mask,
        combined,
        &transcript,
        party_rngs,
        faults,
        &mut out,
    )?;
    Ok(vaults_from(eval_points, alpha_shamir, out))
}

/// Raw triple words one silent ceremony consumes for `num_triples` final words.
fn silent_raw_words(num_triples: usize) -> usize {
    combine_shape(num_triples, Leak::BothFactors).0
}
