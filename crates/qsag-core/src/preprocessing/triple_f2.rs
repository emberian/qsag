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

use super::*;
use crate::sponge::keccak::{Cshake256WordStream4, cshake256_static_midstate};

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
        (all / WORKER_SHARE.get()).max(1)
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
            let per = items.len().div_ceil(workers);
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
    seeds0: SecretBuffer<Vec<[u8; 32]>>,
    seeds1: SecretBuffer<Vec<[u8; 32]>>,
    chosen: SecretBuffer<Vec<[u8; 32]>>,
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
    let total_rows = 64 * words;
    let holder_le = (job.holder as u64).to_le_bytes();
    let owner_le = (job.owner as u64).to_le_bytes();

    // Owner: `t0`, `t1` columns and the message `u = t0 ^ t1 ^ rho`. Holder: the column of its
    // base-OT choice, plus `u` where that choice bit of `alpha` is set, giving `t0 ^ alpha_m rho`.
    let mut t_cols = SecretBuffer(Vec::<Vec<u64>>::with_capacity(256));
    let mut q_cols = SecretBuffer(Vec::<Vec<u64>>::with_capacity(256));
    let mut t1_a = SecretBuffer(vec![0u64; words]);
    let mut t1_b = SecretBuffer(vec![0u64; words]);
    for pair in 0..128 {
        let col_a = 2 * pair;
        let col_b = col_a + 1;
        let col_a_le = (col_a as u64).to_le_bytes();
        let col_b_le = (col_b as u64).to_le_bytes();
        let mut t0_a = vec![0u64; words];
        let mut t0_b = vec![0u64; words];
        let mut q_a = vec![0u64; words];
        let mut q_b = vec![0u64; words];
        stream_words_pair(
            &ABIT_COL_MID,
            &[
                session_id,
                &holder_le,
                &owner_le,
                &col_a_le,
                &job.seeds0[col_a],
            ],
            &mut t0_a,
            &[
                session_id,
                &holder_le,
                &owner_le,
                &col_a_le,
                &job.seeds1[col_a],
            ],
            &mut t1_a,
        );
        stream_words_pair(
            &ABIT_COL_MID,
            &[
                session_id,
                &holder_le,
                &owner_le,
                &col_b_le,
                &job.seeds0[col_b],
            ],
            &mut t0_b,
            &[
                session_id,
                &holder_le,
                &owner_le,
                &col_b_le,
                &job.seeds1[col_b],
            ],
            &mut t1_b,
        );
        stream_words_pair(
            &ABIT_COL_MID,
            &[
                session_id,
                &holder_le,
                &owner_le,
                &col_a_le,
                &job.chosen[col_a],
            ],
            &mut q_a,
            &[
                session_id,
                &holder_le,
                &owner_le,
                &col_b_le,
                &job.chosen[col_b],
            ],
            &mut q_b,
        );
        let mask_a = 0u64.wrapping_sub(black_box(
            ((delta[col_a / 128] >> (col_a % 128)) & 1) as u64,
        ));
        let mask_b = 0u64.wrapping_sub(black_box(
            ((delta[col_b / 128] >> (col_b % 128)) & 1) as u64,
        ));
        for w in 0..words {
            q_a[w] ^= mask_a & (t0_a[w] ^ t1_a[w] ^ rho[w]);
            q_b[w] ^= mask_b & (t0_b[w] ^ t1_b[w] ^ rho[w]);
        }
        t_cols.push(t0_a);
        t_cols.push(t0_b);
        q_cols.push(q_a);
        q_cols.push(q_b);
    }
    let mut t_lanes: [Vec<u128>; 2] =
        core::array::from_fn(|l| transpose_cols128_to_rows(&t_cols[128 * l..128 * (l + 1)], words));
    let mut q_lanes: [Vec<u128>; 2] =
        core::array::from_fn(|l| transpose_cols128_to_rows(&q_cols[128 * l..128 * (l + 1)], words));
    drop((t_cols, q_cols, t1_a, t1_b));

    // KOS consistency check. The challenge is the holder's fresh randomness, sent only after
    // the owner's `u` columns; the sacrificial rows keep `x_bar` and `t_bar` uniform.
    let mut chi_words = vec![0u64; 2 * total_rows];
    stream_words(
        &ABIT_CHI_MID,
        &[session_id, &holder_le, &owner_le, &job.chi_seed],
        &mut chi_words,
    );
    let chi: Vec<u128> = chi_words
        .as_chunks::<2>()
        .0
        .iter()
        .map(|w| gf_join([w[0], w[1]]))
        .collect();
    let mut x_bar = 0u128;
    for (k, weight) in chi.iter().enumerate() {
        x_bar ^= *weight & bit_mask(word_bit(rho, k));
    }
    let mut consistent = true;
    for lane in 0..2 {
        let t_bar = gf_dot(&t_lanes[lane], &chi);
        let q_bar = gf_dot(&q_lanes[lane], &chi);
        consistent &= black_box(q_bar ^ t_bar ^ gf_mul(x_bar, delta[lane])) == 0;
    }
    for lane in 0..2 {
        wipe_u128s(&mut t_lanes[lane][rows..]);
        wipe_u128s(&mut q_lanes[lane][rows..]);
        t_lanes[lane].truncate(rows);
        q_lanes[lane].truncate(rows);
    }
    if !consistent {
        for lane in 0..2 {
            wipe_u128s(&mut t_lanes[lane]);
            wipe_u128s(&mut q_lanes[lane]);
        }
        return Err(PreprocessError::KosOtCheckFailed {
            sender_id: job.holder,
            receiver_id: job.owner,
        });
    }
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
                Ok(PairExtension {
                    holder: bjob.holder,
                    owner: bjob.owner,
                    seeds0: SecretBuffer(send.iter().map(|pair| take(&pair.0)).collect()),
                    seeds1: SecretBuffer(send.iter().map(|pair| take(&pair.1)).collect()),
                    chosen: SecretBuffer(recv.iter().map(take).collect()),
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
// Correlation-robust hashing of pool rows (eight rows per permutation call).
// ---------------------------------------------------------------------------

/// Rows hashed per `Keccak-f[1600]` call.
const CRH_WIDTH: usize = 8;
type CrhOut = [[u64; RATE_WORDS * MAX_CRH_BLOCKS]; CRH_WIDTH];

fn crh_prefix(session_id: &[u8; 32], holder: usize, owner: usize, domain: u64) -> [u64; 8] {
    let mut prefix = [0u64; 8];
    prefix[0] = u64::from_le_bytes(*b"QSAG.CRH");
    prefix[1] = u64::from_le_bytes(*b".F2.V001");
    for i in 0..4 {
        prefix[2 + i] = u64::from_le_bytes(core::array::from_fn(|b| session_id[8 * i + b]));
    }
    prefix[6] = ((holder as u64) << 32) | owner as u64;
    prefix[7] = domain;
    prefix
}

/// `SHAKE256(prefix || index || row)` for eight rows, `blocks` rate blocks of output each.
/// Every row is still hashed on its own: a correlated-OT row is only usable as a pad after a
/// correlation-robust hash of that row, so the batching is across SIMD lanes and never across
/// rows of one sponge.
fn crh_x8(
    prefix: &[u64; 8],
    index: [u64; CRH_WIDTH],
    rows: &[Row; CRH_WIDTH],
    blocks: usize,
    backend: qsag_asm::SimdBackend,
    out: &mut CrhOut,
) {
    let mut st = qsag_asm::KeccakState8x::default();
    for (w, word) in prefix.iter().enumerate() {
        st.0[w] = [*word; CRH_WIDTH];
    }
    for s in 0..CRH_WIDTH {
        st.0[8][s] = index[s];
        st.0[9][s] = rows[s][0] as u64;
        st.0[10][s] = (rows[s][0] >> 64) as u64;
        st.0[11][s] = rows[s][1] as u64;
        st.0[12][s] = (rows[s][1] >> 64) as u64;
    }
    st.0[13] = [0x1f; CRH_WIDTH];
    st.0[16] = [1u64 << 63; CRH_WIDTH];
    for b in 0..blocks {
        qsag_asm::keccak_f1600_x8_with_backend(&mut st, backend);
        for w in 0..RATE_WORDS {
            for s in 0..CRH_WIDTH {
                out[s][RATE_WORDS * b + w] = st.0[w][s];
            }
        }
    }
    qsag_asm::volatile_fill(&mut st.0, [0u64; CRH_WIDTH]);
}

// ---------------------------------------------------------------------------
// Products.
// ---------------------------------------------------------------------------

/// Shape of the recursive sacrifice for a batch of `nbits` raw bit triples.
struct FoldPlan {
    nbits: usize,
    /// Vector length entering each round.
    lens: Vec<usize>,
    /// Rounds whose cross terms ride on the hashed rows of the raw `b` bits.
    structured: usize,
    crh_blocks: usize,
}

impl FoldPlan {
    fn new(nbits: usize) -> Result<Self, PreprocessError> {
        let mut lens = Vec::new();
        let mut len = nbits;
        while len > 1 {
            lens.push(len);
            len = len.div_ceil(2);
        }
        let needed = lens
            .iter()
            .position(|&l| l <= GENERIC_FOLD_LEN)
            .unwrap_or(lens.len());
        let crh_blocks = (1 + 4 * needed).div_ceil(RATE_WORDS).max(1);
        if crh_blocks > MAX_CRH_BLOCKS {
            return Err(PreprocessError::InvalidThreshold { t: 0, n: 0 });
        }
        let structured = ((RATE_WORDS * crh_blocks - 1) / 4).min(lens.len());
        Ok(Self {
            nbits,
            lens,
            structured,
            crh_blocks,
        })
    }

    fn rounds(&self) -> usize {
        self.lens.len()
    }

    /// Choice blocks of the chosen-choice rounds and of the masked base case (`u`, `v` and the
    /// folded `b`), both instances.
    fn choice_blocks(&self) -> usize {
        let generic: usize = self.lens[self.structured..]
            .iter()
            .map(|l| 2 * (l / 2))
            .sum();
        2 * (generic + 3)
    }

    fn pair_rows(&self) -> usize {
        self.nbits + 128 * self.choice_blocks()
    }

    fn pool_rows(&self) -> usize {
        // `a`, `c`, four authenticated cross terms per round, four base products, the mask word
        // of the Shamir check.
        self.pair_rows() + 2 * self.nbits + 128 * (4 * self.rounds() + 4) + CHECK_MASK_BITS
    }
}

/// Hashed rows of one ordered pair over a range of raw `b` bits: the pad difference of every
/// structured round, the pad sums both sides keep, and the AND shares.
struct PairPads {
    holder: usize,
    owner: usize,
    start: usize,
    len: usize,
    /// `planes[(round * 2 + instance) * len + k]`: sender's `pad0 ^ pad1`, turned in place into
    /// the correction message of that round and wiped once the round has consumed it.
    planes: Vec<u128>,
    /// Rounds whose planes are already wiped.
    spent_rounds: usize,
    /// `[round][instance][parity of the bit's group]`.
    send_sum: SecretBuffer<Vec<[[u128; 2]; 2]>>,
    recv_sum: SecretBuffer<Vec<[[u128; 2]; 2]>>,
    and_send: SecretBuffer<Vec<u64>>,
    and_recv: SecretBuffer<Vec<u64>>,
    round_recv: [[u128; 2]; 2],
}

impl Drop for PairPads {
    fn drop(&mut self) {
        let live = (2 * self.spent_rounds * self.len).min(self.planes.len());
        wipe_u128s(&mut self.planes[live..]);
    }
}

fn hash_pair_pads(
    job: &mut PairPads,
    session_id: &[u8; 32],
    pool: &DeltaCotPool,
    plan: &FoldPlan,
    a_holder: &[u64],
    b_owner: &[u64],
) {
    let prefix = crh_prefix(session_id, job.holder, job.owner, 0);
    let backend = qsag_asm::detect_backend();
    let delta = pool.delta[job.holder];
    let q_rows = &pool.holder_rows[job.holder][job.owner];
    let t_rows = &pool.owner_rows[job.holder][job.owner];
    let rounds = plan.structured;
    let mut o0: CrhOut = [[0u64; RATE_WORDS * MAX_CRH_BLOCKS]; CRH_WIDTH];
    let mut o1: CrhOut = [[0u64; RATE_WORDS * MAX_CRH_BLOCKS]; CRH_WIDTH];
    let mut or: CrhOut = [[0u64; RATE_WORDS * MAX_CRH_BLOCKS]; CRH_WIDTH];
    debug_assert_eq!(job.len % CRH_WIDTH, 0);
    for base in (0..job.len).step_by(CRH_WIDTH) {
        let k0 = job.start + base;
        let index: [u64; CRH_WIDTH] = core::array::from_fn(|s| (k0 + s) as u64);
        let rows0: [Row; CRH_WIDTH] =
            core::array::from_fn(|s| [q_rows[0][k0 + s], q_rows[1][k0 + s]]);
        let rows1: [Row; CRH_WIDTH] =
            core::array::from_fn(|s| [rows0[s][0] ^ delta[0], rows0[s][1] ^ delta[1]]);
        let rows_r: [Row; CRH_WIDTH] =
            core::array::from_fn(|s| [t_rows[0][k0 + s], t_rows[1][k0 + s]]);
        crh_x8(&prefix, index, &rows0, plan.crh_blocks, backend, &mut o0);
        crh_x8(&prefix, index, &rows1, plan.crh_blocks, backend, &mut o1);
        crh_x8(&prefix, index, &rows_r, plan.crh_blocks, backend, &mut or);
        for s in 0..CRH_WIDTH {
            let k = k0 + s;
            let local = base + s;
            // AND cross term: the sender's correction is `pad0 ^ pad1 ^ a`.
            let a_bit = word_bit(a_holder, k);
            let b_bit = word_bit(b_owner, k);
            let pad0 = o0[s][0] & 1;
            let correction = pad0 ^ (o1[s][0] & 1) ^ a_bit;
            job.and_send[local / 64] |= pad0 << (local % 64);
            job.and_recv[local / 64] |= ((or[s][0] & 1) ^ (b_bit & correction)) << (local % 64);
            for round in 0..rounds {
                let parity = (k >> round) & 1;
                for inst in 0..2 {
                    let w = 1 + 4 * round + 2 * inst;
                    let h0 = gf_join([o0[s][w], o0[s][w + 1]]);
                    let h1 = gf_join([o1[s][w], o1[s][w + 1]]);
                    let hr = gf_join([or[s][w], or[s][w + 1]]);
                    job.planes[(round * 2 + inst) * job.len + local] = h0 ^ h1;
                    job.send_sum[round][inst][parity] ^= h0;
                    job.recv_sum[round][inst][parity] ^= hr;
                }
            }
        }
    }
    for buf in [&mut o0, &mut o1, &mut or] {
        qsag_asm::volatile_fill(buf, [0u64; RATE_WORDS * MAX_CRH_BLOCKS]);
    }
}

/// One round of structured cross terms for one pair range. Bit `k` sits in group `k >> round`
/// with public coefficient `tens_b[k mod 2^round]`; the sender's payload for it is that
/// coefficient times its share of the partner group's `a` entry.
fn structured_round_pair(
    job: &mut PairPads,
    round: usize,
    a_vec: &[Vec<Vec<u128>>; 2],
    tens_b: &[Vec<u128>; 2],
    b_owner: &[u64],
) {
    let group = 1usize << round;
    for inst in 0..2 {
        let a_holder = &a_vec[inst][job.holder];
        let lo = (round * 2 + inst) * job.len;
        let plane = &mut job.planes[lo..lo + job.len];
        let mut acc = [0u128; 2];
        for (gi, blk) in plane.chunks_mut(group).enumerate() {
            let g = (job.start >> round) + gi;
            let scalar = a_holder.get(g ^ 1).copied().unwrap_or(0);
            if round == 0 {
                blk[0] ^= scalar;
            } else {
                gf_scale_xor(blk, &tens_b[inst][..blk.len()], scalar);
            }
            let first = job.start + gi * group;
            let mut sum = 0u128;
            for (o, correction) in blk.iter().enumerate() {
                sum ^= *correction & bit_mask(word_bit(b_owner, first + o));
            }
            acc[g & 1] ^= sum;
        }
        wipe_u128s(plane);
        job.round_recv[inst] = acc;
    }
    job.spent_rounds = round + 1;
}

/// One product `x * y` of additively shared field elements, with `y` the choice side.
struct FieldProduct {
    block: usize,
    x: SecretBuffer<Vec<u128>>,
    out: usize,
}

struct PairProducts {
    holder: usize,
    owner: usize,
    /// `[out] -> (holder share, owner share)`.
    shares: Vec<(u128, u128)>,
}

/// Cross terms `x_holder * y_owner` of every product for every ordered pair, accumulated per
/// output slot. The caller adds each party's local `x_p * y_p`.
fn cot_field_products(
    session_id: &[u8; 32],
    pool: &DeltaCotPool,
    domain: &mut u64,
    blocks: &[ChoiceBlock],
    products: &[FieldProduct],
    outs: usize,
) -> Vec<Vec<u128>> {
    let n = pool.n;
    let first_domain = *domain;
    *domain += products.len() as u64;
    let mut jobs = Vec::with_capacity(n * (n - 1));
    for holder in 0..n {
        for owner in 0..n {
            if holder != owner {
                jobs.push(PairProducts {
                    holder,
                    owner,
                    shares: vec![(0u128, 0u128); outs],
                });
            }
        }
    }
    par_for_each(&mut jobs, |job| {
        let backend = qsag_asm::detect_backend();
        let delta = pool.delta[job.holder];
        let q_rows = &pool.holder_rows[job.holder][job.owner];
        let t_rows = &pool.owner_rows[job.holder][job.owner];
        let mut o0: CrhOut = [[0u64; RATE_WORDS * MAX_CRH_BLOCKS]; CRH_WIDTH];
        let mut o1: CrhOut = [[0u64; RATE_WORDS * MAX_CRH_BLOCKS]; CRH_WIDTH];
        let mut or: CrhOut = [[0u64; RATE_WORDS * MAX_CRH_BLOCKS]; CRH_WIDTH];
        for (j, product) in products.iter().enumerate() {
            let block = &blocks[product.block];
            let prefix = crh_prefix(session_id, job.holder, job.owner, first_domain + j as u64);
            let d = block.d[job.owner];
            let y = block.y[job.owner];
            let mut payload = product.x[job.holder];
            let (mut send, mut recv) = (0u128, 0u128);
            for base in (0..128).step_by(CRH_WIDTH) {
                let index: [u64; CRH_WIDTH] =
                    core::array::from_fn(|s| (block.off + base + s) as u64);
                let rows0: [Row; CRH_WIDTH] = core::array::from_fn(|s| {
                    let k = block.off + base + s;
                    let adjust = bit_mask(((d >> (base + s)) & 1) as u64);
                    [
                        q_rows[0][k] ^ (adjust & delta[0]),
                        q_rows[1][k] ^ (adjust & delta[1]),
                    ]
                });
                let rows1: [Row; CRH_WIDTH] =
                    core::array::from_fn(|s| [rows0[s][0] ^ delta[0], rows0[s][1] ^ delta[1]]);
                let rows_r: [Row; CRH_WIDTH] = core::array::from_fn(|s| {
                    let k = block.off + base + s;
                    [t_rows[0][k], t_rows[1][k]]
                });
                crh_x8(&prefix, index, &rows0, 1, backend, &mut o0);
                crh_x8(&prefix, index, &rows1, 1, backend, &mut o1);
                crh_x8(&prefix, index, &rows_r, 1, backend, &mut or);
                for s in 0..CRH_WIDTH {
                    let pad0 = gf_join([o0[s][0], o0[s][1]]);
                    let correction = pad0 ^ gf_join([o1[s][0], o1[s][1]]) ^ payload;
                    let choice = bit_mask(((y >> (base + s)) & 1) as u64);
                    send ^= pad0;
                    recv ^= gf_join([or[s][0], or[s][1]]) ^ (choice & correction);
                    payload = gf_mul_x(payload);
                }
            }
            job.shares[product.out].0 ^= send;
            job.shares[product.out].1 ^= recv;
        }
        for buf in [&mut o0, &mut o1, &mut or] {
            qsag_asm::volatile_fill(buf, [0u64; RATE_WORDS * MAX_CRH_BLOCKS]);
        }
    });
    let mut out = vec![vec![0u128; n]; outs];
    for job in &jobs {
        for (slot, (send, recv)) in job.shares.iter().enumerate() {
            out[slot][job.holder] ^= *send;
            out[slot][job.owner] ^= *recv;
        }
    }
    out
}

// ---------------------------------------------------------------------------
// Additive opening with MAC check.
// ---------------------------------------------------------------------------

#[cfg(test)]
std::thread_local! {
    static ADDITIVE_CHECK_WEIGHTS: core::cell::RefCell<Vec<u128>> = const {
        core::cell::RefCell::new(Vec::new())
    };
    static ADDITIVE_CHECK_OPENINGS: core::cell::RefCell<Vec<Tower128>> = const {
        core::cell::RefCell::new(Vec::new())
    };
}

/// Open additively shared field elements `shares[party][j]` and check their two-lane MACs
/// `macs[party][j]` against the parties' key shares. Commit value shares before opening them,
/// and commit MAC residual shares while keeping them private. Only independently randomized
/// MAC residuals are revealed; a failing residual must never expose a multiple of the key.
#[inline(never)]
fn open_additive_authenticated(
    session_id: &[u8; 32],
    phase: &'static str,
    shares: &[Vec<u128>],
    macs: &[Vec<Row>],
    delta: &[Row],
    mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<u128>, PreprocessError> {
    let n = shares.len();
    let count = shares[0].len();
    let commit = |tag: &[u8], party: usize, words: &[u128], salt: &[u8; 32]| -> [u8; 32] {
        let mut xof = Cshake256Xof::new(b"QSAG.TRIPLE.F2.OPEN.COM/v1");
        xof.absorb(session_id);
        xof.absorb(phase.as_bytes());
        xof.absorb(tag);
        xof.absorb(&(party as u64).to_be_bytes());
        for w in words {
            xof.absorb(&w.to_le_bytes());
        }
        xof.absorb(salt);
        let mut out = [0u8; 32];
        xof.squeeze(&mut out);
        out
    };

    let mut opened = vec![0u128; count];
    let mut salts = Vec::with_capacity(n);
    let mut coms = Vec::with_capacity(n);
    for p in 0..n {
        let salt = party_rngs[p].next_bytes32();
        coms.push(commit(b"value", p, &shares[p], &salt));
        salts.push(salt);
    }
    for p in 0..n {
        if !ct_eq_bytes32(&commit(b"value", p, &shares[p], &salts[p]), &coms[p]) {
            return Err(PreprocessError::ShareCommitMismatch { phase, party_id: p });
        }
        wipe_bytes32(&mut salts[p]);
        for (dst, share) in opened.iter_mut().zip(&shares[p]) {
            *dst ^= *share;
        }
    }

    let mut sigma = SecretBuffer(vec![vec![0u128; 2 * count]; n]);
    coms.clear();
    for p in 0..n {
        for j in 0..count {
            for lane in 0..2 {
                sigma[p][2 * j + lane] = macs[p][j][lane] ^ gf_mul(opened[j], delta[p][lane]);
            }
        }
        salts[p] = party_rngs[p].next_bytes32();
        coms.push(commit(b"sigma", p, &sigma[p], &salts[p]));
    }
    for p in 0..n {
        if !ct_eq_bytes32(&commit(b"sigma", p, &sigma[p], &salts[p]), &coms[p]) {
            return Err(PreprocessError::ShareCommitMismatch { phase, party_id: p });
        }
        wipe_bytes32(&mut salts[p]);
    }
    if count == 0 {
        return Ok(opened);
    }
    // Fix the WHOLE residual vector before drawing any projection coefficient.
    // For a nonzero vector over q = 2^128, a uniform linear projection is zero
    // with probability 1/q. Conditional on a nonzero projection, the existing
    // two-round blinding accepts with probability 1/q^2. Three independent
    // projections therefore accept with probability
    // (1/q + (1 - 1/q)/q^2)^3 < 1/q^2, even for a fault in only ONE MAC lane.
    // No projection is ever reconstructed without a fresh private multiplier.
    let mut binding = Cshake256Xof::new(b"QSAG.TRIPLE.F2.MAC.PROJECTIONS.COM/v1");
    binding.absorb(session_id);
    binding.absorb(phase.as_bytes());
    binding.absorb(&(n as u64).to_be_bytes());
    binding.absorb(&(count as u64).to_be_bytes());
    for commitment in &coms {
        binding.absorb(commitment);
    }
    let mut committed = [0u8; 32];
    binding.squeeze(&mut committed);
    for projection in 0..3u64 {
        let sid = cshake256_32_multi_frame(
            b"QSAG.TRIPLE.F2.MAC.PROJECTION/v1",
            &[session_id, phase.as_bytes(), &projection.to_be_bytes()],
        );
        let coin_binding = cshake256_32_multi_frame(
            b"QSAG.TRIPLE.F2.MAC.PROJECTION.COIN/v1",
            &[&committed, &mesh.transcript_digest()],
        );
        let coin = run_commit_and_open_coin(
            &sid,
            b"PI_TRIPLE_F2_MAC_PROJECTION",
            &coin_binding,
            party_rngs,
        )?;
        for lane in 0..2 {
            let mut xof = Cshake256Xof::new(b"QSAG.TRIPLE.F2.MAC.PROJECTION.COEFF/v1");
            xof.absorb(&coin);
            xof.absorb(&[lane as u8]);
            let weights = (0..count)
                .map(|_| {
                    let mut bytes = [0u8; 16];
                    xof.squeeze(&mut bytes);
                    u128::from_le_bytes(bytes)
                })
                .collect::<Vec<_>>();
            let residual = SecretBuffer(
                sigma
                    .iter()
                    .map(|row| {
                        let values = SecretBuffer(
                            row.as_chunks::<2>()
                                .0
                                .iter()
                                .map(|pair| pair[lane])
                                .collect::<Vec<_>>(),
                        );
                        // Projection uses the MAC's polynomial field. The final coordinate
                        // map into the tower field is XOR-linear and zero-preserving;
                        // its blinding zero test needs no multiplicative isomorphism.
                        Tower128(gf_dot(&weights, &values))
                    })
                    .collect::<Vec<_>>(),
            );
            let blind_sid =
                cshake256_32_multi_frame(b"QSAG.TRIPLE.F2.MAC.BLIND/v1", &[&sid, &[lane as u8]]);
            let blinded = mac_blind::blind_open_tower128(
                &blind_sid,
                phase,
                &residual,
                Some(&mut *mesh),
                party_rngs,
            )?;
            #[cfg(test)]
            {
                ADDITIVE_CHECK_OPENINGS.with(|checks| checks.borrow_mut().push(blinded));
                ADDITIVE_CHECK_WEIGHTS
                    .with(|weights_seen| weights_seen.borrow_mut().push(weights[0]));
            }
            if !blinded.ct_eq(Tower128::ZERO) {
                return Err(PreprocessError::MacCheckFailed {
                    phase,
                    accused_party: None,
                });
            }
        }
    }
    Ok(opened)
}

// ---------------------------------------------------------------------------
// Shamir conversion.
// ---------------------------------------------------------------------------

/// Degree-`< t` shares of a full `GF(256)^64` word.
fn shamir_share_planes(
    t: usize,
    eval_mats: &[PublicGf256Matrix],
    secret: &BitslicedGf256x64,
    rng: &mut PartyPrivateRng,
) -> Vec<BitslicedGf256x64> {
    let mut coeffs: Vec<BitslicedGf256x64> = Vec::with_capacity(t);
    coeffs.push(*secret);
    for _ in 1..t {
        coeffs.push(core::array::from_fn(|_| rng.next_u64()));
    }
    let out = eval_mats
        .iter()
        .map(|mat| {
            let mut acc = [0u64; 8];
            for c in coeffs.iter().rev() {
                acc = bs_gf256_xor(&mat.scale_planes(&acc), c);
            }
            acc
        })
        .collect();
    for c in &mut coeffs {
        wipe_u64s(c);
    }
    out
}

/// Shamir value shares `[party][word]` and Shamir MAC shares `[party][word][lane][bit]`.
pub(super) type ShamirAuthenticatedWords =
    (Vec<Vec<BitslicedGf256x64>>, Vec<Vec<[[Tower128; 64]; 2]>>);

/// Deal degree-`< t` shares of every party's XOR share `bit_words[party][word]` and of its
/// additive MAC share `mac_bits[party][lane][64 * word + bit]`, then run the `Π_MAC`
/// consistency and degree check over all `n` parties. `tamper` sees the dealt shares before
/// the check.
#[expect(
    clippy::too_many_arguments,
    reason = "Quorum, value shares, MAC shares and private randomness are separate protocol inputs"
)]
fn convert_to_shamir_and_check(
    session_id: &[u8; 32],
    t: usize,
    eval_points: &[TowerGf256],
    alpha_shamir: &[[Tower128; 2]],
    mask: CheckMask,
    bit_words: &[Vec<u64>],
    mac_bits: &[[Vec<u128>; 2]],
    transcript: &[u8; 32],
    party_rngs: &mut [PartyPrivateRng],
    tamper: &mut ShamirTamper<'_>,
) -> Result<ShamirAuthenticatedWords, PreprocessError> {
    let n = eval_points.len();
    let num_words = bit_words[0].len();
    let eval_mats: Vec<PublicGf256Matrix> = eval_points
        .iter()
        .map(|&pt| PublicGf256Matrix::from_public_scalar(pt))
        .collect();

    // The disposable mask word of the check is read as 64 `GF(256)` lanes.
    struct Dealer {
        party: usize,
        rng: PartyPrivateRng,
        /// `[receiver][word]`, the mask word last.
        dealt: SecretBuffer<Vec<Vec<BitslicedGf256x64>>>,
        additive: SecretBuffer<Vec<[[u128; 64]; 2]>>,
    }
    let mut dealers: Vec<Dealer> = (0..n)
        .map(|party| Dealer {
            party,
            rng: PartyPrivateRng::from_seed(
                party_rngs[party].next_bytes32(),
                b"QSAG.TRIPLE.F2.DEAL/v1",
            ),
            dealt: SecretBuffer(vec![vec![[0u64; 8]; num_words + 1]; n]),
            additive: SecretBuffer(vec![[[0u128; 64]; 2]; num_words + 1]),
        })
        .collect();
    {
        let mask_ref = &mask;
        let eval_mats_ref = &eval_mats;
        par_for_each(&mut dealers, |dealer| {
            let p = dealer.party;
            for (k, word) in bit_words[p].iter().enumerate() {
                let dealt = SecretBuffer(shamir_share_bits64_gf256_mats(
                    t,
                    eval_mats_ref,
                    *word,
                    &mut dealer.rng,
                ));
                for q in 0..n {
                    dealer.dealt[q][k] = dealt[q];
                }
                for lane in 0..2 {
                    dealer.additive[k][lane]
                        .copy_from_slice(&mac_bits[p][lane][64 * k..64 * k + 64]);
                }
            }
            let dealt = SecretBuffer(shamir_share_planes(
                t,
                eval_mats_ref,
                &mask_ref.planes[p],
                &mut dealer.rng,
            ));
            for q in 0..n {
                dealer.dealt[q][num_words] = dealt[q];
            }
            dealer.additive[num_words] = mask_ref.macs[p];
        });
    }
    let mut words_sh = SecretBuffer(vec![vec![[0u64; 8]; num_words]; n]);
    let mut r_chk_sh = SecretBuffer(vec![[0u64; 8]; n]);
    for dealer in &dealers {
        for q in 0..n {
            for k in 0..num_words {
                bs_gf256_xor_assign(&mut words_sh[q][k], &dealer.dealt[q][k]);
            }
            bs_gf256_xor_assign(&mut r_chk_sh[q], &dealer.dealt[q][num_words]);
        }
    }
    let additive: Vec<SecretBuffer<Vec<[[u128; 64]; 2]>>> = dealers
        .into_iter()
        .map(|mut dealer| SecretBuffer(core::mem::take(&mut dealer.additive.0)))
        .collect();

    // Shamir-share every additive MAC word. Each block of words draws from per-party
    // substreams keyed by the block index, so blocks are independent of scheduling.
    let seeds: SecretBuffer<Vec<[u8; 32]>> =
        SecretBuffer((0..n).map(|p| party_rngs[p].next_bytes32()).collect());
    let mut macs_sh = vec![vec![[[Tower128::ZERO; 64]; 2]; num_words + 1]; n];
    {
        struct MacBlock<'a> {
            index: usize,
            dst: Vec<&'a mut [[[Tower128; 64]; 2]]>,
        }
        let mut iters: Vec<_> = macs_sh
            .iter_mut()
            .map(|v| v.chunks_mut(SHAMIR_BLOCK_WORDS))
            .collect();
        let mut blocks = Vec::new();
        loop {
            let dst: Vec<_> = iters.iter_mut().filter_map(Iterator::next).collect();
            if dst.is_empty() {
                break;
            }
            blocks.push(MacBlock {
                index: blocks.len(),
                dst,
            });
        }
        let additive_ref = &additive;
        let seeds_ref = &seeds;
        let eval_mats_ref = &eval_mats;
        par_for_each(&mut blocks, |block| {
            let first = block.index * SHAMIR_BLOCK_WORDS;
            let block_le = (block.index as u64).to_le_bytes();
            for p in 0..n {
                let mut rng = PartyPrivateRng::from_seed(seeds_ref[p], &block_le);
                for k_off in 0..block.dst[0].len() {
                    for lane in 0..2 {
                        let dealt = SecretBuffer(shamir_share_tower128x64_mats(
                            t,
                            eval_mats_ref,
                            &additive_ref[p][first + k_off][lane],
                            &mut rng,
                        ));
                        for (q, dst_q) in block.dst.iter_mut().enumerate() {
                            let mut unpacked = unpack_bs_gf256x16_to_u128x64(&dealt[q]);
                            for bit in 0..64 {
                                dst_q[k_off][lane][bit] =
                                    dst_q[k_off][lane][bit].add(Tower128(unpacked[bit]));
                            }
                            wipe_u128s(&mut unpacked);
                        }
                    }
                }
            }
        });
    }
    drop((additive, seeds, mask));

    tamper(&mut words_sh, &mut macs_sh);

    let checked = spdz_pimac_check_bs_gf256_words(
        session_id,
        t,
        eval_points,
        alpha_shamir,
        &words_sh,
        &macs_sh,
        &mut r_chk_sh,
        transcript,
        party_rngs,
    );
    for party in &mut macs_sh {
        if let Some(mut chk) = party.pop() {
            wipe_tower128(&mut chk[0]);
            wipe_tower128(&mut chk[1]);
        }
    }
    if let Err(e) = checked {
        for party in &mut macs_sh {
            for word in party.iter_mut() {
                wipe_tower128(&mut word[0]);
                wipe_tower128(&mut word[1]);
            }
        }
        return Err(e);
    }
    Ok((core::mem::take(&mut words_sh.0), macs_sh))
}

/// Authenticate XOR-shared Boolean words under the two-lane SPDZ key and return consistent
/// degree-`< t` Shamir shares of the bits and of their MACs.
#[expect(
    clippy::too_many_arguments,
    reason = "Quorum, key shares, value shares and private randomness are separate protocol inputs"
)]
pub(super) fn authenticate_xor_shared_words(
    session_id: &[u8; 32],
    t: usize,
    eval_points: &[TowerGf256],
    ot_mesh: &mut OtMesh,
    alpha_contribs: &[[Tower128; 2]],
    alpha_shamir: &[[Tower128; 2]],
    bit_words: &[Vec<u64>],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<ShamirAuthenticatedWords, PreprocessError> {
    let n = eval_points.len();
    let num_words = bit_words[0].len();
    let nbits = 64 * num_words;
    let mut pool = DeltaCotPool::establish(
        session_id,
        ot_mesh,
        alpha_contribs,
        nbits + CHECK_MASK_BITS,
        0,
        party_rngs,
    )?;
    let off = pool.alloc(nbits)?;
    let mut transcript = *session_id;
    let mut d_total = vec![0u64; num_words];
    for p in 0..n {
        for (k, word) in bit_words[p].iter().enumerate() {
            let d = *word ^ pool.rho[p][off / 64 + k];
            absorb_transcript(&mut transcript, b"bits", &d.to_le_bytes());
            d_total[k] ^= d;
        }
    }
    let mac_bits: SecretBuffer<Vec<[Vec<u128>; 2]>> = SecretBuffer(
        (0..n)
            .map(|p| pool.mac_bits(p, off, nbits, &d_total))
            .collect(),
    );
    let mask = pool.take_check_mask()?;
    drop(pool);
    convert_to_shamir_and_check(
        session_id,
        t,
        eval_points,
        alpha_shamir,
        mask,
        bit_words,
        &mac_bits,
        &transcript,
        party_rngs,
        &mut |_, _| {},
    )
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

/// Pairwise MAC on one owner's share of the folded `b` vector of one instance under one
/// holder's key: `t[lane][j] ^ q[lane][j] = b_vec[inst][owner][j] * delta_holder[lane]`. The
/// raw `b` bits are pool rows, so these are public linear combinations of rows both sides
/// already hold, and they fold with the same coins as `b_vec`.
struct FoldedTags {
    inst: usize,
    holder: usize,
    owner: usize,
    t: [Vec<u128>; 2],
    q: [Vec<u128>; 2],
}

impl Drop for FoldedTags {
    fn drop(&mut self) {
        for lane in 0..2 {
            wipe_u128s(&mut self.t[lane]);
            wipe_u128s(&mut self.q[lane]);
        }
    }
}

impl FoldedTags {
    /// Tags of the `b` vector after `log2(tens_b[inst].len())` folds of the `nbits` raw bits at
    /// pair rows `off_b..`.
    fn after_structured_rounds(
        pool: &DeltaCotPool,
        off_b: usize,
        nbits: usize,
        tens_b: &[Vec<u128>; 2],
    ) -> Vec<Self> {
        let n = pool.n;
        let mut tags = Vec::with_capacity(2 * n * (n - 1));
        for inst in 0..2 {
            for holder in 0..n {
                for owner in 0..n {
                    if holder != owner {
                        tags.push(Self {
                            inst,
                            holder,
                            owner,
                            t: [Vec::new(), Vec::new()],
                            q: [Vec::new(), Vec::new()],
                        });
                    }
                }
            }
        }
        par_for_each(&mut tags, |tag| {
            let coeffs = &tens_b[tag.inst];
            let fold = |rows: &[Vec<u128>; 2]| -> [Vec<u128>; 2] {
                core::array::from_fn(|lane| {
                    rows[lane][off_b..off_b + nbits]
                        .chunks(coeffs.len())
                        .map(|group| gf_dot(&coeffs[..group.len()], group))
                        .collect()
                })
            };
            tag.t = fold(&pool.owner_rows[tag.holder][tag.owner]);
            tag.q = fold(&pool.holder_rows[tag.holder][tag.owner]);
        });
        tags
    }

    /// `b' = r b_even + b_odd`.
    fn fold(&mut self, r: u128) {
        for side in [&mut self.t, &mut self.q] {
            for lane in side.iter_mut() {
                let (mut even, mut odd) = split_even_odd(lane);
                gf_scale_xor(&mut odd, &even, r);
                wipe_u128s(&mut even);
                wipe_u128s(lane);
                *lane = odd;
            }
        }
    }
}

/// Check that the choices of `block` are every owner's share of entry `entry` of the folded
/// `b` vector of instance `inst`. Each owner sends each holder its side of the pairwise tag
/// difference; the holder's side equals it exactly when the choice is that share, and an owner
/// with another choice has to guess a multiple of the holder's key in both lanes.
fn bind_choice(
    pool: &DeltaCotPool,
    tags: &[FoldedTags],
    inst: usize,
    entry: usize,
    block: &ChoiceBlock,
) -> Result<(), PreprocessError> {
    for tag in tags.iter().filter(|tag| tag.inst == inst) {
        let (owner_tag, holder_tag) = pool.choice_tags(tag.holder, tag.owner, block);
        let mut diff = 0u128;
        for lane in 0..2 {
            diff |= owner_tag[lane] ^ tag.t[lane][entry] ^ holder_tag[lane] ^ tag.q[lane][entry];
        }
        if black_box(diff) != 0 {
            return Err(PreprocessError::MacCheckFailed {
                phase: "pi_triple_f2_choice",
                accused_party: Some(tag.owner),
            });
        }
    }
    Ok(())
}

fn split_even_odd(v: &[u128]) -> (Vec<u128>, Vec<u128>) {
    let half = v.len().div_ceil(2);
    let mut even = Vec::with_capacity(half);
    let mut odd = Vec::with_capacity(half);
    for pair in v.chunks(2) {
        even.push(pair[0]);
        odd.push(pair.get(1).copied().unwrap_or(0));
    }
    (even, odd)
}

/// Prepare the recursive inner-product sacrifice over the authenticated raw bits.
/// The coordinator must check the returned private opening before accepting these triples.
#[expect(
    clippy::too_many_arguments,
    reason = "Shares, MAC shares, pads and randomness of one ceremony are separate protocol inputs"
)]
fn recursive_sacrifice(
    session_id: &[u8; 32],
    plan: &FoldPlan,
    pool: &mut DeltaCotPool,
    off_b: usize,
    pads: &mut [PairPads],
    bits: [&[Vec<u64>]; 3],
    macs: [&[[Vec<u128>; 2]]; 3],
    transcript: &mut [u8; 32],
    party_rngs: &mut [PartyPrivateRng],
    faults: &mut PiTripleF2Faults<'_>,
) -> Result<PendingSacrifice, PreprocessError> {
    let n = pool.n;
    let nbits = plan.nbits;
    let [a_bits, b_bits, c_bits] = bits;
    let [mac_a, mac_b, mac_c] = macs;

    let chi_coin =
        run_commit_and_open_coin(session_id, b"PI_TRIPLE_F2_CHI", transcript, party_rngs)?;
    absorb_transcript(transcript, b"chi", &chi_coin);
    let chi: [Vec<u128>; 2] = core::array::from_fn(|inst| {
        let mut words = vec![0u64; 2 * nbits];
        stream_words(&SACRIFICE_CHI_MID, &[&chi_coin, &[inst as u8]], &mut words);
        words
            .as_chunks::<2>()
            .0
            .iter()
            .map(|w| gf_join([w[0], w[1]]))
            .collect()
    });

    // Claim `<a_vec, b_vec> = c` per instance, as additive shares.
    struct SacrificeInitSlot {
        inst: usize,
        p: usize,
        a: Vec<u128>,
        b: Vec<u128>,
        cv: u128,
        cm: [u128; 2],
    }
    let mut init_slots: Vec<SacrificeInitSlot> = (0..2)
        .flat_map(|inst| {
            (0..n).map(move |p| SacrificeInitSlot {
                inst,
                p,
                a: Vec::new(),
                b: Vec::new(),
                cv: 0,
                cm: [0u128; 2],
            })
        })
        .collect();
    {
        let chi_ref = &chi;
        par_for_each(&mut init_slots, |slot| {
            let inst = slot.inst;
            let p = slot.p;
            slot.a = (0..nbits)
                .map(|k| chi_ref[inst][k] & bit_mask(word_bit(&a_bits[p], k)))
                .collect();
            if inst == 0 {
                slot.b = (0..nbits)
                    .map(|k| u128::from(word_bit(&b_bits[p], k)))
                    .collect();
            }
            let mut cv = 0u128;
            for k in 0..nbits {
                cv ^= chi_ref[inst][k] & bit_mask(word_bit(&c_bits[p], k));
            }
            slot.cv = cv;
            slot.cm = [
                gf_dot(&chi_ref[inst], &mac_c[p][0]),
                gf_dot(&chi_ref[inst], &mac_c[p][1]),
            ];
        });
    }
    let mut a_vec: SecretBuffer<[Vec<Vec<u128>>; 2]> =
        SecretBuffer([vec![Vec::new(); n], vec![Vec::new(); n]]);
    let mut b_vec: SecretBuffer<[Vec<Vec<u128>>; 2]> =
        SecretBuffer([vec![Vec::new(); n], vec![Vec::new(); n]]);
    let mut c_val = SecretBuffer([vec![0u128; n], vec![0u128; n]]);
    let mut c_mac = SecretBuffer([vec![[0u128; 2]; n], vec![[0u128; 2]; n]]);
    for mut slot in init_slots {
        a_vec[slot.inst][slot.p] = core::mem::take(&mut slot.a);
        if slot.inst == 0 {
            let b_copy = slot.b.clone();
            b_vec[0][slot.p] = core::mem::take(&mut slot.b);
            b_vec[1][slot.p] = b_copy;
        }
        c_val[slot.inst][slot.p] = slot.cv;
        c_mac[slot.inst][slot.p] = slot.cm;
        slot.cv = 0;
        slot.cm = [0; 2];
    }
    // Public coefficients of each raw bit in the folded entries.
    let mut tens_a: [Vec<u128>; 2] = [vec![1u128], vec![1u128]];
    let mut tens_b: [Vec<u128>; 2] = [vec![1u128], vec![1u128]];
    let mut product_domain = 1u64;
    // Set at the first chosen-choice product; until then every choice is a raw `b` row.
    let mut tags: Option<Vec<FoldedTags>> = None;

    for round in 0..plan.rounds() {
        let len = plan.lens[round];
        let pairs = len / 2;
        // `h[inst][party] = [h0, h1]` with `h0 = <a_even, b_odd>`, `h1 = <a_odd, b_even>`.
        let mut h = SecretBuffer([vec![[0u128; 2]; n], vec![[0u128; 2]; n]]);
        let mut halves: SecretBuffer<Vec<Vec<[Vec<u128>; 4]>>> = SecretBuffer(vec![
            vec![[Vec::new(), Vec::new(), Vec::new(), Vec::new()]; n],
            vec![[Vec::new(), Vec::new(), Vec::new(), Vec::new()]; n],
        ]);
        {
            struct SplitSlot {
                inst: usize,
                p: usize,
                h_pair: [u128; 2],
                parts: [Vec<u128>; 4],
            }
            let mut split_slots: Vec<SplitSlot> = (0..2)
                .flat_map(|inst| {
                    (0..n).map(move |p| SplitSlot {
                        inst,
                        p,
                        h_pair: [0u128; 2],
                        parts: [Vec::new(), Vec::new(), Vec::new(), Vec::new()],
                    })
                })
                .collect();
            let a_ref = &a_vec.0;
            let b_ref = &b_vec.0;
            par_for_each(&mut split_slots, |slot| {
                let (a_even, a_odd) = split_even_odd(&a_ref[slot.inst][slot.p]);
                let (b_even, b_odd) = split_even_odd(&b_ref[slot.inst][slot.p]);
                slot.h_pair = [
                    gf_dot(&a_even[..pairs], &b_odd[..pairs]),
                    gf_dot(&a_odd[..pairs], &b_even[..pairs]),
                ];
                slot.parts = [a_even, a_odd, b_even, b_odd];
            });
            for mut slot in split_slots {
                h[slot.inst][slot.p] = slot.h_pair;
                slot.h_pair = [0; 2];
                halves[slot.inst][slot.p] = core::mem::take(&mut slot.parts);
            }
        }

        if round < plan.structured {
            let a_ref = &a_vec.0;
            let tens_ref = &tens_b;
            par_for_each(pads, |job| {
                structured_round_pair(job, round, a_ref, tens_ref, &b_bits[job.owner]);
            });
            for job in pads.iter() {
                for inst in 0..2 {
                    // Bits of odd groups pair with even `a` entries (`h0`), and vice versa.
                    for (slot, parity) in [(0usize, 1usize), (1, 0)] {
                        h[inst][job.holder][slot] ^= job.send_sum[round][inst][parity];
                        h[inst][job.owner][slot] ^=
                            job.recv_sum[round][inst][parity] ^ job.round_recv[inst][parity];
                    }
                }
            }
        } else {
            let tags = tags.get_or_insert_with(|| {
                FoldedTags::after_structured_rounds(pool, off_b, nbits, &tens_b)
            });
            let mut blocks = Vec::with_capacity(4 * pairs);
            let mut products = Vec::with_capacity(4 * pairs);
            for inst in 0..2 {
                for i in 0..pairs {
                    for (slot, a_idx, b_idx) in [(0usize, 2 * i, 2 * i + 1), (1, 2 * i + 1, 2 * i)]
                    {
                        let mut y: SecretBuffer<Vec<u128>> =
                            SecretBuffer((0..n).map(|p| b_vec[inst][p][b_idx]).collect());
                        if let Some(hook) = faults.choice_values.as_mut() {
                            for (p, choice) in y.iter_mut().enumerate() {
                                hook(round, p, choice);
                            }
                        }
                        let block = pool.choose_field(&y)?;
                        bind_choice(pool, tags, inst, b_idx, &block)?;
                        products.push(FieldProduct {
                            block: blocks.len(),
                            x: SecretBuffer((0..n).map(|p| a_vec[inst][p][a_idx]).collect()),
                            out: 2 * inst + slot,
                        });
                        blocks.push(block);
                    }
                }
            }
            let cross =
                cot_field_products(session_id, pool, &mut product_domain, &blocks, &products, 4);
            for inst in 0..2 {
                for slot in 0..2 {
                    for p in 0..n {
                        h[inst][p][slot] ^= cross[2 * inst + slot][p];
                    }
                }
            }
        }

        if let Some(hook) = faults.fold_shares.as_mut() {
            for p in 0..n {
                let mut mine = [h[0][p], h[1][p]];
                hook(round, p, &mut mine);
                h[0][p] = mine[0];
                h[1][p] = mine[1];
            }
        }

        // Authenticate both cross terms of both instances, then draw the round coin.
        let mut handles = [[AuthValue { off: 0, d_total: 0 }; 2]; 2];
        for inst in 0..2 {
            for slot in 0..2 {
                let shares: SecretBuffer<Vec<u128>> =
                    SecretBuffer((0..n).map(|p| h[inst][p][slot]).collect());
                handles[inst][slot] = pool.authenticate_field(&shares, transcript)?;
            }
        }
        let coin =
            run_commit_and_open_coin(session_id, b"PI_TRIPLE_F2_FOLD", transcript, party_rngs)?;
        absorb_transcript(transcript, b"fold", &coin);
        let r = lane_coins(&coin);

        for inst in 0..2 {
            let r_sq = gf_mul(r[inst], r[inst]);
            for p in 0..n {
                let [mut a_even, a_odd, b_even, mut b_odd] = core::mem::take(&mut halves[inst][p]);
                gf_scale_xor(&mut a_even, &a_odd, r[inst]);
                gf_scale_xor(&mut b_odd, &b_even, r[inst]);
                wipe_u128s(&mut a_vec[inst][p]);
                wipe_u128s(&mut b_vec[inst][p]);
                a_vec[inst][p] = a_even;
                b_vec[inst][p] = b_odd;
                let (mut a_odd, mut b_even) = (a_odd, b_even);
                wipe_u128s(&mut a_odd);
                wipe_u128s(&mut b_even);

                c_val[inst][p] =
                    h[inst][p][0] ^ gf_mul(r[inst], c_val[inst][p]) ^ gf_mul(r_sq, h[inst][p][1]);
                let mac_h0 = pool.mac_field(p, handles[inst][0].off, handles[inst][0].d_total);
                let mac_h1 = pool.mac_field(p, handles[inst][1].off, handles[inst][1].d_total);
                for lane in 0..2 {
                    c_mac[inst][p][lane] = mac_h0[lane]
                        ^ gf_mul(r[inst], c_mac[inst][p][lane])
                        ^ gf_mul(r_sq, mac_h1[lane]);
                }
            }
            // `a' = a_even + r a_odd`, `b' = r b_even + b_odd`.
            let mut scaled_a = vec![0u128; tens_a[inst].len()];
            gf_scale_xor(&mut scaled_a, &tens_a[inst], r[inst]);
            tens_a[inst].extend_from_slice(&scaled_a);
            let mut scaled_b = vec![0u128; tens_b[inst].len()];
            gf_scale_xor(&mut scaled_b, &tens_b[inst], r[inst]);
            scaled_b.extend_from_slice(&tens_b[inst]);
            tens_b[inst] = scaled_b;
        }
        for tag in tags.iter_mut().flatten() {
            tag.fold(r[tag.inst]);
        }
    }

    // Masked base case on the single remaining pair of each instance:
    // open `a + rb u`, `b + rb v`, `c + rb d1 + rb^2 d2` with `d1 = a v + u b`, `d2 = u v`.
    // The mask `u` of `a` is only ever a payload: `u b` takes the folded `b` as its choice, so
    // no transfer in this protocol has a choice that depends on `a`.
    let tags =
        tags.unwrap_or_else(|| FoldedTags::after_structured_rounds(pool, off_b, nbits, &tens_b));
    let mut blocks = Vec::with_capacity(6);
    let mut products = Vec::with_capacity(6);
    for inst in 0..2 {
        let u = pool.random_field()?;
        let v = pool.random_field()?;
        let mut y: SecretBuffer<Vec<u128>> =
            SecretBuffer((0..n).map(|p| b_vec[inst][p][0]).collect());
        if let Some(hook) = faults.choice_values.as_mut() {
            for (p, choice) in y.iter_mut().enumerate() {
                hook(plan.rounds(), p, choice);
            }
        }
        let b = pool.choose_field(&y)?;
        bind_choice(pool, &tags, inst, 0, &b)?;
        let (v_idx, b_idx) = (blocks.len() + 1, blocks.len() + 2);
        products.push(FieldProduct {
            block: v_idx,
            x: SecretBuffer((0..n).map(|p| a_vec[inst][p][0]).collect()),
            out: 2 * inst,
        });
        products.push(FieldProduct {
            block: b_idx,
            x: SecretBuffer(u.y.to_vec()),
            out: 2 * inst,
        });
        products.push(FieldProduct {
            block: v_idx,
            x: SecretBuffer(u.y.to_vec()),
            out: 2 * inst + 1,
        });
        blocks.push(u);
        blocks.push(v);
        blocks.push(b);
    }
    drop(tags);
    let mut d = SecretBuffer(cot_field_products(
        session_id,
        pool,
        &mut product_domain,
        &blocks,
        &products,
        4,
    ));
    for inst in 0..2 {
        let (u, v) = (&blocks[3 * inst], &blocks[3 * inst + 1]);
        for p in 0..n {
            d[2 * inst][p] ^= gf_mul(a_vec[inst][p][0], v.y[p]) ^ gf_mul(u.y[p], b_vec[inst][p][0]);
            d[2 * inst + 1][p] ^= gf_mul(u.y[p], v.y[p]);
        }
    }
    let mut d_handles = [AuthValue { off: 0, d_total: 0 }; 4];
    for (slot, handle) in d_handles.iter_mut().enumerate() {
        *handle = pool.authenticate_field(&d[slot], transcript)?;
    }
    let base_coin =
        run_commit_and_open_coin(session_id, b"PI_TRIPLE_F2_BASE", transcript, party_rngs)?;
    // A zero base coin would open the unmasked pair; it is replaced by one.
    let rb = lane_coins(&base_coin).map(|c| if c == 0 { 1 } else { c });

    let mut open_shares = SecretBuffer(vec![vec![0u128; 6]; n]);
    let mut open_macs = SecretBuffer(vec![vec![[0u128; 2]; 6]; n]);
    for inst in 0..2 {
        let (u, v) = (&blocks[3 * inst], &blocks[3 * inst + 1]);
        let rb_sq = gf_mul(rb[inst], rb[inst]);
        let weights_a: Vec<u128> = (0..nbits)
            .map(|k| gf_mul(chi[inst][k], tens_a[inst][k]))
            .collect();
        for p in 0..n {
            open_shares[p][3 * inst] = a_vec[inst][p][0] ^ gf_mul(rb[inst], u.y[p]);
            open_shares[p][3 * inst + 1] = b_vec[inst][p][0] ^ gf_mul(rb[inst], v.y[p]);
            open_shares[p][3 * inst + 2] = c_val[inst][p]
                ^ gf_mul(rb[inst], d[2 * inst][p])
                ^ gf_mul(rb_sq, d[2 * inst + 1][p]);
            let mac_u = pool.mac_field(p, u.off, 0);
            let mac_v = pool.mac_field(p, v.off, 0);
            let mac_d1 = pool.mac_field(p, d_handles[2 * inst].off, d_handles[2 * inst].d_total);
            let mac_d2 = pool.mac_field(
                p,
                d_handles[2 * inst + 1].off,
                d_handles[2 * inst + 1].d_total,
            );
            for lane in 0..2 {
                open_macs[p][3 * inst][lane] =
                    gf_dot(&weights_a, &mac_a[p][lane]) ^ gf_mul(rb[inst], mac_u[lane]);
                open_macs[p][3 * inst + 1][lane] =
                    gf_dot(&tens_b[inst][..nbits], &mac_b[p][lane]) ^ gf_mul(rb[inst], mac_v[lane]);
                open_macs[p][3 * inst + 2][lane] = c_mac[inst][p][lane]
                    ^ gf_mul(rb[inst], mac_d1[lane])
                    ^ gf_mul(rb_sq, mac_d2[lane]);
            }
        }
    }
    Ok(PendingSacrifice {
        shares: open_shares,
        macs: open_macs,
    })
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

/// Ceremonies run side by side. Each wave bootstraps its ceremonies in order, runs the
/// private work concurrently, then checks final sacrifice openings in order on the shared
/// mesh. A third concurrent ceremony bought under 10% of wall time for 20% more CPU.
const MAX_CONCURRENT_CEREMONIES: usize = 2;

/// Final triples of one combine pool. 8,192 words gives arity 3 (see [`combine_arity`]);
/// smaller pools such as 7,720 words adaptively require arity >= 4. Larger requests are
/// split into pools of this size or more so the raw shares held for one combine stay bounded.
const POOL_WORDS: usize = 8192;

fn pair_pads(n: usize, nbits: usize, plan: &FoldPlan) -> Vec<PairPads> {
    let unit = (1usize << plan.structured).max(64);
    let ranges_per_pair = ((worker_count() + n * (n - 1) / 2) / (n * (n - 1))).max(1);
    let range_len = nbits.div_ceil(ranges_per_pair).div_ceil(unit) * unit;
    let mut pads = Vec::new();
    for holder in 0..n {
        for owner in 0..n {
            if holder == owner {
                continue;
            }
            for start in (0..nbits).step_by(range_len) {
                let len = range_len.min(nbits - start);
                pads.push(PairPads {
                    holder,
                    owner,
                    start,
                    len,
                    planes: vec![0u128; 2 * plan.structured * len],
                    spent_rounds: 0,
                    send_sum: SecretBuffer(vec![[[0u128; 2]; 2]; plan.structured]),
                    recv_sum: SecretBuffer(vec![[[0u128; 2]; 2]; plan.structured]),
                    and_send: SecretBuffer(vec![0u64; len / 64]),
                    and_recv: SecretBuffer(vec![0u64; len / 64]),
                    round_recv: [[0u128; 2]; 2],
                });
            }
        }
    }
    pads
}

/// One KOS-backed raw ceremony over a bootstrapped pool: `plan.nbits` authenticated raw bit
/// triples and the pending private sacrifice opening, checked by the coordinator.
fn raw_ceremony(
    session_id: [u8; 32],
    plan: &FoldPlan,
    boot: PoolBoot,
    party_rngs: &mut [PartyPrivateRng],
    faults: &mut PiTripleF2Faults<'_>,
) -> Result<UncheckedRawBatch, PreprocessError> {
    let n = boot.n;
    let nbits = plan.nbits;
    let raw_words = nbits / 64;
    let mut pool = DeltaCotPool::extend(&session_id, boot)?;
    let mut transcript = session_id;

    // Raw `a` and `b` are the parties' pool bits themselves; `b` sits in the pair region.
    let off_b = pool.alloc_pair(nbits)?;
    let off_a = pool.alloc(nbits)?;
    let off_c = pool.alloc(nbits)?;
    let a_bits = SecretBuffer(
        (0..n)
            .map(|p| pool.rho_words(p, off_a, raw_words))
            .collect::<Vec<_>>(),
    );
    let b_bits = SecretBuffer(
        (0..n)
            .map(|p| pool.rho_words(p, off_b, raw_words))
            .collect::<Vec<_>>(),
    );

    // Hash every ordered pair's `b` rows once: AND cross terms now, fold pads for later.
    let mut pads = pair_pads(n, nbits, plan);
    {
        let (pool_ref, a_ref, b_ref) = (&pool, &a_bits, &b_bits);
        par_for_each(&mut pads, |job| {
            let (holder, owner) = (job.holder, job.owner);
            hash_pair_pads(
                job,
                &session_id,
                pool_ref,
                plan,
                &a_ref[holder],
                &b_ref[owner],
            );
        });
    }
    let mut c_bits = SecretBuffer(
        (0..n)
            .map(|p| {
                a_bits[p]
                    .iter()
                    .zip(&b_bits[p])
                    .map(|(a, b)| a & b)
                    .collect::<Vec<u64>>()
            })
            .collect::<Vec<_>>(),
    );
    for job in &pads {
        for (i, (send, recv)) in job.and_send.iter().zip(job.and_recv.iter()).enumerate() {
            c_bits[job.holder][job.start / 64 + i] ^= *send;
            c_bits[job.owner][job.start / 64 + i] ^= *recv;
        }
    }
    if let Some(hook) = faults.product_shares.as_mut() {
        for p in 0..n {
            hook(p, &mut c_bits[p]);
        }
    }

    // Authenticate `c`: each party publishes its share XOR the reserved pool bits.
    let mut d_c = vec![0u64; raw_words];
    for p in 0..n {
        for (k, word) in c_bits[p].iter().enumerate() {
            let d = *word ^ pool.rho[p][off_c / 64 + k];
            absorb_transcript(&mut transcript, b"c", &d.to_le_bytes());
            d_c[k] ^= d;
        }
    }
    let zero = vec![0u64; raw_words];
    let macs =
        compute_mac_triples_parallel(&pool, n, nbits, [off_a, off_b, off_c], [&zero, &zero, &d_c]);
    sacrifice_raw(
        &session_id,
        plan,
        pool,
        off_b,
        pads,
        [a_bits, b_bits, c_bits],
        macs,
        transcript,
        party_rngs,
        faults,
    )
}

/// One raw ceremony whose triples and correlated-OT pool come from locally expanded
/// [`crate::pcg_dense::DensePcgExpandedVault`]s instead of `KosOtExtension`.
fn raw_silent_ceremony(
    session_id: [u8; 32],
    plan: &FoldPlan,
    vaults_lane0: &mut [crate::pcg_dense::DensePcgExpandedVault],
    vaults_lane1: &mut [crate::pcg_dense::DensePcgExpandedVault],
    party_rngs: &mut [PartyPrivateRng],
    faults: &mut PiTripleF2Faults<'_>,
) -> Result<UncheckedRawBatch, PreprocessError> {
    let n = vaults_lane0.len();
    let nbits = plan.nbits;
    let raw_words = nbits / 64;

    let mut a_bits = SecretBuffer(vec![vec![0u64; raw_words]; n]);
    let mut b_bits = SecretBuffer(vec![vec![0u64; raw_words]; n]);
    let mut c_bits = SecretBuffer(vec![vec![0u64; raw_words]; n]);
    for p in 0..n {
        for k in 0..raw_words {
            let (aw, bw, cw) = vaults_lane0[p].next_bool_triple_word64()?;
            a_bits[p][k] = aw;
            b_bits[p][k] = bw;
            c_bits[p][k] = cw;
        }
    }
    if let Some(hook) = faults.product_shares.as_mut() {
        for p in 0..n {
            hook(p, &mut c_bits[p]);
        }
    }

    let mut pool = DeltaCotPool::from_silent_pcg_vaults(
        vaults_lane0,
        vaults_lane1,
        plan.pool_rows(),
        plan.pair_rows(),
        &b_bits,
        party_rngs,
    )?;
    let mut transcript = session_id;

    let off_b = pool.alloc_pair(nbits)?;
    let off_a = pool.alloc(nbits)?;
    let off_c = pool.alloc(nbits)?;

    // The structured fold pads ride on the `b` rows. The AND shares hashed alongside are
    // unused: `c` comes from the vault and the sacrifice checks it against `a & b`.
    let mut pads = pair_pads(n, nbits, plan);
    {
        let (pool_ref, a_ref, b_ref) = (&pool, &a_bits, &b_bits);
        par_for_each(&mut pads, |job| {
            let (holder, owner) = (job.holder, job.owner);
            hash_pair_pads(
                job,
                &session_id,
                pool_ref,
                plan,
                &a_ref[holder],
                &b_ref[owner],
            );
        });
    }

    let mut d_a = vec![0u64; raw_words];
    for p in 0..n {
        for (k, word) in a_bits[p].iter().enumerate() {
            let d = *word ^ pool.rho[p][off_a / 64 + k];
            absorb_transcript(&mut transcript, b"a", &d.to_le_bytes());
            d_a[k] ^= d;
        }
    }
    let mut d_c = vec![0u64; raw_words];
    for p in 0..n {
        for (k, word) in c_bits[p].iter().enumerate() {
            let d = *word ^ pool.rho[p][off_c / 64 + k];
            absorb_transcript(&mut transcript, b"c", &d.to_le_bytes());
            d_c[k] ^= d;
        }
    }
    let zero = vec![0u64; raw_words];
    let macs =
        compute_mac_triples_parallel(&pool, n, nbits, [off_a, off_b, off_c], [&d_a, &zero, &d_c]);
    sacrifice_raw(
        &session_id,
        plan,
        pool,
        off_b,
        pads,
        [a_bits, b_bits, c_bits],
        macs,
        transcript,
        party_rngs,
        faults,
    )
}

type RawBits = [SecretBuffer<Vec<Vec<u64>>>; 3];
type RawMacs = [SecretBuffer<Vec<[Vec<u128>; 2]>>; 3];

fn compute_mac_triples_parallel(
    pool: &DeltaCotPool,
    n: usize,
    nbits: usize,
    offs: [usize; 3],
    deltas: [&[u64]; 3],
) -> RawMacs {
    struct MacSlot {
        which: usize,
        p: usize,
        out: [Vec<u128>; 2],
    }
    let mut slots: Vec<MacSlot> = (0..3)
        .flat_map(|which| {
            (0..n).map(move |p| MacSlot {
                which,
                p,
                out: [Vec::new(), Vec::new()],
            })
        })
        .collect();
    par_for_each(&mut slots, |slot| {
        slot.out = pool.mac_bits(slot.p, offs[slot.which], nbits, deltas[slot.which]);
    });
    let mut macs: RawMacs =
        core::array::from_fn(|_| SecretBuffer(vec![[Vec::new(), Vec::new()]; n]));
    for mut slot in slots {
        macs[slot.which][slot.p] = core::mem::take(&mut slot.out);
    }
    macs
}

#[expect(
    clippy::too_many_arguments,
    reason = "Shares, MAC shares, pads and randomness of one ceremony are separate protocol inputs"
)]
fn sacrifice_raw(
    session_id: &[u8; 32],
    plan: &FoldPlan,
    mut pool: DeltaCotPool,
    off_b: usize,
    mut pads: Vec<PairPads>,
    bits: RawBits,
    macs: RawMacs,
    mut transcript: [u8; 32],
    party_rngs: &mut [PartyPrivateRng],
    faults: &mut PiTripleF2Faults<'_>,
) -> Result<UncheckedRawBatch, PreprocessError> {
    let sacrifice = recursive_sacrifice(
        session_id,
        plan,
        &mut pool,
        off_b,
        &mut pads,
        [&bits[0], &bits[1], &bits[2]],
        [&macs[0], &macs[1], &macs[2]],
        &mut transcript,
        party_rngs,
        faults,
    )?;
    drop(pads);
    let mask = pool.take_check_mask()?;
    let delta = SecretBuffer(pool.delta.to_vec());
    Ok(UncheckedRawBatch {
        batch: RawBatch {
            triples: BitTriples { bits, macs },
            mask,
            delta,
            transcript,
        },
        sacrifice,
    })
}

// ---------------------------------------------------------------------------
// Bucket combine.
// ---------------------------------------------------------------------------

/// Statistical security of one combine pass, in bits.
const COMBINE_SECURITY_BITS: u32 = 40;

/// Bucket size of a combine pass that outputs `out_bits` bits: the least `f >= 2` with
/// `out_bits / C(f (out_bits + 1), f) <= 2^-40`.
///
/// **Leakage model.** Before the bucket coin is drawn, a deviating party can make the sacrifice
/// succeed only if linear functionals of its choice over the honest parties' raw bits of one
/// factor take values it guessed: a wrong OT correction on bit `k` is caught unless the
/// receiver's bit is the guess, and one error spread over a set of corrections tests the parity
/// of that set. `j` independent functionals survive with probability `2^-j` and tell the
/// adversary the subspace `L` they span, nothing else, about uniformly random raw bits.
///
/// **Combine.** A public uniform permutation of the raw bit positions, drawn after every such
/// transfer, cuts `f (out_bits + 1)` positions into buckets of `f` and discards the rest,
/// including one whole bucket. An output bit is the XOR of the folded factor over its bucket;
/// nothing else about the folded factor is ever opened. The outputs are uniform in the
/// adversary's view unless some non-zero `l` in `L` is a sum of output functionals, that is,
/// unless the support of `l` is a union of `g >= 1` kept buckets.
///
/// **Bound.** For a fixed support of size `f g` that happens with probability
/// `R(g) = C(n, g) / C(f m, f g)` with `n = out_bits`, `m = n + 1`. `R(n) = R(1) / n`, and for
/// `2 <= g < n`, `C(f m, f g) >= C(m, g)^f` (Vandermonde) gives
/// `R(g) <= C(m, g)^(1 - f) <= (m (m - 1) / 2)^(1 - f) < R(1)` once `n >= 15`. So every `l`
/// is bad with probability at most `R(1) = n / C(f m, f)`, and by a union bound over the
/// `2^j - 1` non-zero elements of `L` the adversary survives and learns anything about the
/// outputs with probability below `2^-j (2^j - 1) R(1) < R(1)`, whatever `j` it chose. The
/// discarded bucket is what rules out the parity of all raw bits, which without it is the
/// parity of all outputs. `combine_arity_meets_its_bound` checks the maximum over `g`
/// numerically.
fn combine_arity(out_bits: usize) -> usize {
    debug_assert!(out_bits >= 64);
    let n = out_bits as u128;
    let target = n << COMBINE_SECURITY_BITS;
    let mut f = 2u128;
    loop {
        // `C(f (n + 1), f)`, exact while it fits; an overflow is above every target.
        let mut binom = Some(1u128);
        for i in 0..f {
            binom = binom
                .and_then(|c| c.checked_mul(f * (n + 1) - i))
                .map(|c| c / (i + 1));
        }
        if binom.is_none_or(|c| c >= target) {
            return f as usize;
        }
        f += 1;
    }
}

/// Raw words a combine pass with bucket size `arity` needs for `out_words` outputs.
fn combine_input_words(out_words: usize, arity: usize) -> usize {
    (arity * (64 * out_words + 1)).div_ceil(64)
}

/// Which raw factors a deviating party can aim a selective failure at.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Leak {
    /// Only `b`. With KOS-backed raw triples every OT choice is a raw `b` row, a share of the
    /// folded `b` that [`bind_choice`] ties to those rows, or the mask `v` of the folded `b`;
    /// `a` and its mask are only ever payloads, and a receiver has no freedom in its choices.
    ChoiceSide,
    /// Both. Raw triples from a PCG are claimed, not computed: a party that misreports its
    /// share of one factor is caught exactly when the other factor's bit is set.
    BothFactors,
}

/// `(raw words, bucket size folding b, bucket size folding a)` for `out_words` final words.
fn combine_shape(out_words: usize, leak: Leak) -> (usize, usize, Option<(usize, usize)>) {
    match leak {
        Leak::ChoiceSide => {
            let fold_b = combine_arity(64 * out_words);
            (combine_input_words(out_words, fold_b), fold_b, None)
        }
        Leak::BothFactors => {
            let fold_a = combine_arity(64 * out_words);
            let mid_words = combine_input_words(out_words, fold_a);
            let fold_b = combine_arity(64 * mid_words);
            (
                combine_input_words(mid_words, fold_b),
                fold_b,
                Some((mid_words, fold_a)),
            )
        }
    }
}

/// Equally sized batches addressed as one array of bit triples.
struct PoolView<'a> {
    batches: &'a [&'a BitTriples],
    batch_bits: usize,
}

impl PoolView<'_> {
    #[inline]
    fn bit(&self, which: usize, party: usize, idx: usize) -> u64 {
        word_bit(
            &self.batches[idx / self.batch_bits].bits[which][party],
            idx % self.batch_bits,
        )
    }

    #[inline]
    fn mac(&self, which: usize, party: usize, lane: usize, idx: usize) -> u128 {
        self.batches[idx / self.batch_bits].macs[which][party][lane][idx % self.batch_bits]
    }
}

/// One pass of the bucket combine. With `fold = 1` an output triple is
/// `(a_0, b_0 ^ .. ^ b_{f-1}, c_0 ^ .. ^ c_{f-1} ^ e_1 b_1 ^ .. ^ e_{f-1} b_{f-1})` over the
/// `f = arity` members of its bucket, where `e_i = a_0 ^ a_i` is opened with a MAC check;
/// `fold = 0` swaps the roles of `a` and `b`. The bucket permutation is drawn here, bound to
/// `transcript`, and every opening is absorbed into it.
#[expect(
    clippy::too_many_arguments,
    reason = "Pool, shape, key shares and private randomness of one pass are separate inputs"
)]
fn combine_pass(
    session_id: &[u8; 32],
    phase: &'static str,
    fold: usize,
    arity: usize,
    out_words: usize,
    batches: &[&BitTriples],
    delta: &[Row],
    transcript: &mut [u8; 32],
    mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
    faults: &mut PiTripleF2Faults<'_>,
) -> Result<BitTriples, PreprocessError> {
    let n = delta.len();
    let keep = 1 - fold;
    let pool = PoolView {
        batches,
        batch_bits: 64 * batches[0].words(),
    };
    let total = pool.batch_bits * batches.len();
    let out_bits = 64 * out_words;
    if batches.iter().any(|b| 64 * b.words() != pool.batch_bits)
        || arity < 2
        || arity * (out_bits + 1) > total
    {
        return Err(PreprocessError::VaultExhausted {
            kind: "raw triples of a combine pool",
        });
    }

    // Every raw share is authenticated and every sacrifice has finished, so no transfer that
    // depends on a raw bit is still to come. Only now is the bucket coin drawn.
    let coin = run_commit_and_open_coin(session_id, phase.as_bytes(), transcript, party_rngs)?;
    absorb_transcript(transcript, b"bucket", &coin);
    let perm = derive_coin_permutation(&coin, phase.as_bytes(), total);
    let member = |bit: usize, i: usize| perm[bit * arity + i] as usize;

    // Openings `e = keep_0 ^ keep_i`, 128 to a field element.
    let opens = out_bits * (arity - 1);
    let elems = opens.div_ceil(128);
    struct PartyOpen {
        party: usize,
        shares: Vec<u128>,
        macs: Vec<Row>,
    }
    let mut parts: Vec<PartyOpen> = (0..n)
        .map(|party| PartyOpen {
            party,
            shares: vec![0u128; elems],
            macs: vec![[0u128; 2]; elems],
        })
        .collect();
    {
        let (pool, member) = (&pool, &member);
        par_for_each(&mut parts, |part| {
            let p = part.party;
            let mut rows = [[0u128; 128]; 2];
            for elem in 0..elems {
                let mut share = 0u128;
                for j in 0..128.min(opens - 128 * elem) {
                    let open = 128 * elem + j;
                    let (bit, i) = (open / (arity - 1), 1 + open % (arity - 1));
                    let (m0, mi) = (member(bit, 0), member(bit, i));
                    share |= u128::from(pool.bit(keep, p, m0) ^ pool.bit(keep, p, mi)) << j;
                    for lane in 0..2 {
                        rows[lane][j] = pool.mac(keep, p, lane, m0) ^ pool.mac(keep, p, lane, mi);
                    }
                }
                part.shares[elem] = share;
                part.macs[elem] = core::array::from_fn(|lane| gf_dot(&rows[lane], &POWERS));
                rows = [[0u128; 128]; 2];
            }
        });
    }
    let mut shares = SecretBuffer(Vec::with_capacity(n));
    let mut macs = SecretBuffer(Vec::with_capacity(n));
    for mut part in parts {
        if let Some(hook) = faults.combine_shares.as_mut() {
            hook(part.party, &mut part.shares);
        }
        shares.push(core::mem::take(&mut part.shares));
        macs.push(core::mem::take(&mut part.macs));
    }
    let opened =
        open_additive_authenticated(session_id, phase, &shares, &macs, delta, mesh, party_rngs)?;
    absorb_transcript(transcript, b"mac-blind", &mesh.transcript_digest());
    drop((shares, macs));
    let opened_bytes: Vec<u8> = opened.iter().flat_map(|e| e.to_le_bytes()).collect();
    absorb_transcript(transcript, b"open", &opened_bytes);
    let opened_bit = |bit: usize, i: usize| {
        let open = bit * (arity - 1) + (i - 1);
        ((opened[open / 128] >> (open % 128)) & 1) as u64
    };

    struct PartyOut {
        party: usize,
        bits: [Vec<u64>; 3],
        macs: [[Vec<u128>; 2]; 3],
    }
    let mut outs: Vec<PartyOut> = (0..n)
        .map(|party| PartyOut {
            party,
            bits: core::array::from_fn(|_| vec![0u64; out_words]),
            macs: core::array::from_fn(|_| core::array::from_fn(|_| vec![0u128; out_bits])),
        })
        .collect();
    {
        let (pool, member, opened_bit) = (&pool, &member, &opened_bit);
        par_for_each(&mut outs, |out| {
            let p = out.party;
            for bit in 0..out_bits {
                let m0 = member(bit, 0);
                let kept = pool.bit(keep, p, m0);
                let mut folded = 0u64;
                let mut product = 0u64;
                let mut folded_mac = [0u128; 2];
                let mut product_mac = [0u128; 2];
                for i in 0..arity {
                    let mi = member(bit, i);
                    let e = if i == 0 { 0 } else { opened_bit(bit, i) };
                    let y = pool.bit(fold, p, mi);
                    folded ^= y;
                    product ^= pool.bit(2, p, mi) ^ (e & y);
                    for lane in 0..2 {
                        let y_mac = pool.mac(fold, p, lane, mi);
                        folded_mac[lane] ^= y_mac;
                        product_mac[lane] ^= pool.mac(2, p, lane, mi) ^ (bit_mask(e) & y_mac);
                    }
                }
                out.bits[keep][bit / 64] |= kept << (bit % 64);
                out.bits[fold][bit / 64] |= folded << (bit % 64);
                out.bits[2][bit / 64] |= product << (bit % 64);
                for lane in 0..2 {
                    out.macs[keep][lane][bit] = pool.mac(keep, p, lane, m0);
                    out.macs[fold][lane][bit] = folded_mac[lane];
                    out.macs[2][lane][bit] = product_mac[lane];
                }
            }
        });
    }
    let mut combined = BitTriples {
        bits: core::array::from_fn(|_| SecretBuffer(Vec::with_capacity(n))),
        macs: core::array::from_fn(|_| SecretBuffer(Vec::with_capacity(n))),
    };
    for mut out in outs {
        for which in 0..3 {
            combined.bits[which].push(core::mem::take(&mut out.bits[which]));
            combined.macs[which].push(core::mem::take(&mut out.macs[which]));
        }
    }
    Ok(combined)
}

/// Combine the raw triples of `batches` into `out_words` final words: fold `b`, and where both
/// factors can leak fold `a` in a second pass under a fresh permutation of the intermediate
/// triples. Each pass is one application of the bound of [`combine_arity`]; in the second, the
/// first pass's openings turn any functional of the raw `a` bits into one of the intermediate
/// `a` bits, fixed before the second coin.
#[expect(
    clippy::too_many_arguments,
    reason = "Pool, shape, key shares and private randomness of one combine are separate inputs"
)]
fn combine_raw(
    session_id: &[u8; 32],
    leak: Leak,
    out_words: usize,
    batches: &[&BitTriples],
    delta: &[Row],
    transcript: &mut [u8; 32],
    mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
    faults: &mut PiTripleF2Faults<'_>,
) -> Result<BitTriples, PreprocessError> {
    let (_, fold_b, second) = combine_shape(out_words, leak);
    let first_words = second.map_or(out_words, |(mid_words, _)| mid_words);
    let first = combine_pass(
        session_id,
        "pi_triple_f2_comb_b",
        1,
        fold_b,
        first_words,
        batches,
        delta,
        transcript,
        mesh,
        party_rngs,
        faults,
    )?;
    let Some((_, fold_a)) = second else {
        return Ok(first);
    };
    combine_pass(
        session_id,
        "pi_triple_f2_comb_a",
        0,
        fold_a,
        out_words,
        &[&first],
        delta,
        transcript,
        mesh,
        party_rngs,
        faults,
    )
}

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
    (0..pools)
        .map(|i| words / pools + usize::from(i < words % pools))
        .collect()
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
    let count = raw_words.div_ceil(ceremony_words);
    let plan = FoldPlan::new(64 * raw_words.div_ceil(count))?;
    let wave = (worker_count() / (n * (n - 1)).max(1)).clamp(1, MAX_CONCURRENT_CEREMONIES);

    let mut batches = Vec::with_capacity(count);
    for first in (0..count).step_by(wave) {
        let mut ceremonies = Vec::with_capacity(wave);
        for index in first..count.min(first + wave) {
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
        bits: core::array::from_fn(|_| SecretBuffer(vec![Vec::with_capacity(num_words); n])),
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn crh_x8_is_one_shake256_per_row() {
        let prefix = crh_prefix(&[0x5a; 32], 2, 1, 7);
        let index: [u64; CRH_WIDTH] = core::array::from_fn(|s| 1000 + 3 * s as u64);
        let rows: [Row; CRH_WIDTH] = core::array::from_fn(|s| {
            let v = 0x0123_4567_89ab_cdef_0f1e_2d3c_4b5a_6978u128.rotate_left(11 * s as u32);
            [v, !v ^ (s as u128)]
        });
        let mut out: CrhOut = [[0u64; RATE_WORDS * MAX_CRH_BLOCKS]; CRH_WIDTH];
        for backend in [qsag_asm::SimdBackend::Portable, qsag_asm::detect_backend()] {
            crh_x8(&prefix, index, &rows, MAX_CRH_BLOCKS, backend, &mut out);
            for s in 0..CRH_WIDTH {
                let mut msg = Vec::new();
                for word in prefix {
                    msg.extend_from_slice(&word.to_le_bytes());
                }
                msg.extend_from_slice(&index[s].to_le_bytes());
                msg.extend_from_slice(&rows[s][0].to_le_bytes());
                msg.extend_from_slice(&rows[s][1].to_le_bytes());
                let want =
                    crate::sponge::keccak::shake256_xof(8 * RATE_WORDS * MAX_CRH_BLOCKS, &msg);
                let got: Vec<u8> = out[s].iter().flat_map(|w| w.to_le_bytes()).collect();
                assert_eq!(got, want, "lane {s}, backend {backend:?}");
            }
        }
    }

    #[test]
    fn additive_share_shift_opens_only_fresh_randomized_residuals() {
        // Keep the portable field circuit out of loop vectorization.
        #[inline(never)]
        fn expected_product(r: Tower128, d: Tower128) -> Tower128 {
            r.mul(d)
        }
        let sid = [0xe1; 32];
        let delta = [[0x1234u128, 0x5678u128], [0x9876u128, 0xabcdu128]];
        let macs = vec![vec![[0u128; 2]]; 2];
        let shifted = vec![vec![1u128], vec![0u128]];
        let total = delta[0][0] ^ delta[1][0];
        let mut seen = alloc::collections::BTreeSet::new();
        let mut seen_randomizers = alloc::collections::BTreeSet::new();
        for honest_tape in 1..=16 {
            // Fixed alpha, shift, corrupt tape and base-OT setup. Only the
            // honest party's fresh private randomness varies between aborts.
            let tapes = [0x91, honest_tape];
            let rngs = || {
                tapes
                    .iter()
                    .map(|&seed| PartyPrivateRng::from_seed([seed; 32], b"additive-abort"))
                    .collect::<Vec<_>>()
            };
            let mut private = rngs();
            let mut setup_rngs: Vec<_> = (0..2)
                .map(|p| PartyPrivateRng::from_seed([0x42 + p; 32], b"fixed-additive-base-ot"))
                .collect();
            let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut setup_rngs);
            let before = mesh.transcript_digest();
            // The retained mesh blinds from its single-use pool. Stage it from the same
            // private tapes and read the joint randomizer the first round will consume.
            mesh.prestage_blinded_checks(1, &mut private).unwrap();
            let staged = mesh.staged_blinding_serials();
            let randomizer = mesh.next_blinding_randomizer().unwrap();
            ADDITIVE_CHECK_OPENINGS.with(|checks| checks.borrow_mut().clear());
            ADDITIVE_CHECK_WEIGHTS.with(|weights| weights.borrow_mut().clear());
            assert!(matches!(
                open_additive_authenticated(
                    &sid,
                    "additive_shift",
                    &shifted,
                    &macs,
                    &delta,
                    &mut mesh,
                    &mut private
                ),
                Err(PreprocessError::MacCheckFailed {
                    phase: "additive_shift",
                    ..
                })
            ));
            let checks = ADDITIVE_CHECK_OPENINGS.with(|checks| checks.borrow().clone());
            let weights = ADDITIVE_CHECK_WEIGHTS.with(|weights| weights.borrow().clone());
            assert_eq!(weights.len(), 1);
            let projected = Tower128(gf_mul(weights[0], total));
            assert_eq!(checks, [expected_product(randomizer, projected)]);
            assert_ne!(checks[0], Tower128::ZERO);
            assert_ne!(checks[0], projected);
            assert_ne!(mesh.transcript_digest(), before);
            // The rejecting round spent exactly the triple whose randomizer was read.
            assert_eq!(mesh.staged_blinding_serials(), staged[..staged.len() - 1]);
            assert!(seen_randomizers.insert(randomizer.0));
            seen.insert(checks[0].0);
        }
        assert_eq!(seen.len(), 16);
        // A fault confined to the second lane is also rejected.
        let mut private: Vec<_> = (0..2)
            .map(|p| PartyPrivateRng::from_seed([0x51 + p; 32], b"additive-second-lane"))
            .collect();
        let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut private);
        let delta = [[0, 19], [0, 23]];
        ADDITIVE_CHECK_OPENINGS.with(|checks| checks.borrow_mut().clear());
        assert!(matches!(
            open_additive_authenticated(
                &sid,
                "additive_second_lane",
                &shifted,
                &macs,
                &delta,
                &mut mesh,
                &mut private
            ),
            Err(PreprocessError::MacCheckFailed { .. })
        ));
        ADDITIVE_CHECK_OPENINGS.with(|checks| {
            assert_eq!(checks.borrow().len(), 2);
            assert_eq!(checks.borrow()[0], Tower128::ZERO);
            assert_ne!(checks.borrow()[1], Tower128::ZERO);
        });
        ADDITIVE_CHECK_OPENINGS.with(|checks| checks.borrow_mut().clear());
        assert_eq!(
            open_additive_authenticated(
                &sid,
                "additive_honest",
                &vec![vec![0]; 2],
                &macs,
                &delta,
                &mut mesh,
                &mut private
            )
            .unwrap(),
            [0]
        );
        // All three projections and BOTH MAC lanes must be checked on success.
        ADDITIVE_CHECK_OPENINGS.with(|checks| assert_eq!(*checks.borrow(), [Tower128::ZERO; 6]));
        // A fault in a late element crosses gf_dot's 128-element chunks.
        let fields = 257;
        let mut shifted = vec![vec![0u128; fields]; 2];
        shifted[0][fields - 1] = 1;
        ADDITIVE_CHECK_OPENINGS.with(|checks| checks.borrow_mut().clear());
        assert!(matches!(
            open_additive_authenticated(
                &sid,
                "additive_late_element",
                &shifted,
                &vec![vec![[0u128; 2]; fields]; 2],
                &delta,
                &mut mesh,
                &mut private
            ),
            Err(PreprocessError::MacCheckFailed { .. })
        ));
        ADDITIVE_CHECK_OPENINGS.with(|checks| {
            assert_eq!(checks.borrow().len(), 2);
            assert_eq!(checks.borrow()[0], Tower128::ZERO);
            assert_ne!(checks.borrow()[1], Tower128::ZERO);
        });
    }

    type TestSetup = (
        [TowerGf256; 3],
        Vec<PartyPrivateRng>,
        OtMesh,
        Vec<[Tower128; 2]>,
        Vec<[Tower128; 2]>,
    );
    fn setup(sid: [u8; 32], tag: &[u8]) -> TestSetup {
        let points = [TowerGf256(1), TowerGf256(2), TowerGf256(3)];
        let mut rngs: Vec<_> = (0..3)
            .map(|p| PartyPrivateRng::from_seed([p + 0x30; 32], tag))
            .collect();
        let mesh = OtMesh::establish_ideal_for_test(sid, &mut rngs);
        let (alpha, shared) = spdz_setup_alpha_gf256(&sid, 2, &points, &mut rngs).unwrap();
        (points, rngs, mesh, alpha, shared)
    }

    /// Opened `(a, b, c)` bits of additive triples, after checking `c = a & b` and both MAC
    /// lanes of every bit against the XOR of the key shares.
    fn open_additive(triples: &BitTriples, alpha: &[[Tower128; 2]]) -> [Vec<u64>; 3] {
        let n = alpha.len();
        let words = triples.words();
        let key: Row = core::array::from_fn(|lane| alpha.iter().fold(0, |k, a| k ^ a[lane].0));
        let opened: [Vec<u64>; 3] = core::array::from_fn(|which| {
            (0..words)
                .map(|w| (0..n).fold(0, |x, p| x ^ triples.bits[which][p][w]))
                .collect()
        });
        for which in 0..3 {
            for lane in 0..2 {
                for k in 0..64 * words {
                    let mac = (0..n).fold(0, |m, p| m ^ triples.macs[which][p][lane][k]);
                    assert_eq!(mac, bit_mask(word_bit(&opened[which], k)) & key[lane]);
                }
            }
        }
        for w in 0..words {
            assert_eq!(opened[2][w], opened[0][w] & opened[1][w]);
        }
        opened
    }

    /// `log2 C(n, k)`. Kept out of line: inlined into the loops of its caller, this sum sends
    /// LLVM's loop vectorizer into minutes of planning.
    #[inline(never)]
    fn log2_binom(n: usize, k: usize) -> f64 {
        let mut acc = 0.0;
        for i in 0..k {
            acc += ((n - i) as f64).log2() - ((i + 1) as f64).log2();
        }
        acc
    }

    /// `log2` of `C(n, g) / C(f (n + 1), f g)`: the chance that a fixed set of `f g` raw
    /// positions is a union of `g` kept buckets.
    #[inline(never)]
    fn log2_union_chance(n: usize, f: usize, g: usize) -> f64 {
        log2_binom(n, g) - log2_binom(f * (n + 1), f * g)
    }

    #[test]
    fn combine_arity_meets_its_bound() {
        // Hand-checked values: the production pool, one raw ceremony's worth, small requests.
        assert_eq!(combine_arity(64 * POOL_WORDS), 3);
        assert_eq!(combine_arity(64 * 7720), 4);
        assert_eq!(combine_arity(64 * 7000), 4);
        assert_eq!(combine_arity(64 * 1015), 4);
        assert_eq!(combine_arity(64 * 100), 4);
        assert_eq!(combine_arity(64 * 4), 6);
        assert_eq!(combine_arity(64), 7);

        for words in [
            1usize, 2, 3, 4, 5, 8, 25, 64, 126, 512, 1015, 7720, 8192, 16383,
        ] {
            let n = core::hint::black_box(64 * words);
            let f = combine_arity(n);
            // The chance is largest for a single bucket, and that is below 2^-40.
            let single = log2_union_chance(n, f, 1);
            assert!(single <= -f64::from(COMBINE_SECURITY_BITS), "{words} words");
            let mut probes: Vec<usize> = (2..=64).collect();
            probes.extend([n / 3, n / 2, n - 2, n - 1, n]);
            for g in probes {
                if (2..=n).contains(&g) {
                    assert!(
                        log2_union_chance(n, f, g) < single,
                        "{words} words, {g} buckets"
                    );
                }
            }
            // One member fewer per bucket would not do.
            if f > 2 {
                let short = log2_union_chance(n, f - 1, 1);
                assert!(short > -f64::from(COMBINE_SECURITY_BITS), "{words} words");
            }
        }
        // The two-pass shape of the silent path at its chunk size.
        assert_eq!(combine_shape(5, Leak::BothFactors), (156, 5, Some((31, 6))));
    }

    /// A pool with a single set raw `b` bit, shared and authenticated by hand.
    fn one_hot_pool(words: usize, hot: usize, delta: &[Row]) -> BitTriples {
        let n = delta.len();
        let mut pool = BitTriples {
            bits: core::array::from_fn(|_| SecretBuffer(vec![vec![0u64; words]; n])),
            macs: core::array::from_fn(|_| {
                SecretBuffer(
                    (0..n)
                        .map(|_| [vec![0u128; 64 * words], vec![0u128; 64 * words]])
                        .collect(),
                )
            }),
        };
        // `a` is all ones, so `c = b`; party 0 holds the values, every party its MAC share.
        for w in 0..words {
            pool.bits[0][0][w] = u64::MAX;
        }
        pool.bits[1][0][hot / 64] = 1 << (hot % 64);
        pool.bits[2][0][hot / 64] = 1 << (hot % 64);
        for p in 0..n {
            for lane in 0..2 {
                pool.macs[0][p][lane].fill(delta[p][lane]);
                pool.macs[1][p][lane][hot] = delta[p][lane];
                pool.macs[2][p][lane][hot] = delta[p][lane];
            }
        }
        pool
    }

    /// The bucket permutation acts on bits, not words: one marked raw bit lands on output bit
    /// offsets unrelated to its own, in either output word, or in the discarded positions, and
    /// the outputs stay valid authenticated triples.
    #[test]
    fn combine_permutes_single_bits_and_keeps_triples_valid() {
        let delta: Vec<Row> = vec![[3, 5], [0x11 << 64, 7 << 100], [9 << 30, 1 << 127]];
        let alpha: Vec<[Tower128; 2]> = delta
            .iter()
            .map(|d| [Tower128(d[0]), Tower128(d[1])])
            .collect();
        let out_words = 2;
        let arity = combine_arity(64 * out_words);
        let raw_words = combine_input_words(out_words, arity);
        let hot = 64 * 3 + 17;
        let (mut landed, mut same_offset, mut dropped) = (0usize, 0usize, 0usize);
        let mut seen = alloc::collections::BTreeSet::new();
        for trial in 0u8..96 {
            let pool = one_hot_pool(raw_words, hot, &delta);
            let mut rngs: Vec<_> = (0..3)
                .map(|p| PartyPrivateRng::from_seed([trial; 32], &[b'c', p]))
                .collect();
            let mut mesh = OtMesh::establish_ideal_for_test([trial; 32], &mut rngs);
            let mut transcript = [trial; 32];
            let out = combine_pass(
                &[0x77; 32],
                "pi_triple_f2_comb_b",
                1,
                arity,
                out_words,
                &[&pool],
                &delta,
                &mut transcript,
                &mut mesh,
                &mut rngs,
                &mut PiTripleF2Faults::default(),
            )
            .unwrap();
            let opened = open_additive(&out, &alpha);
            assert_eq!(opened[0], [u64::MAX; 2]);
            let ones: u32 = opened[1].iter().map(|w| w.count_ones()).sum();
            assert!(ones <= 1);
            if ones == 0 {
                dropped += 1;
                continue;
            }
            let pos = (0..128).find(|k| word_bit(&opened[1], *k) == 1).unwrap();
            landed += 1;
            same_offset += usize::from(pos % 64 == hot % 64);
            seen.insert(pos);
        }
        // 768 of the 832 raw positions are in kept buckets, so about 7 trials in 96 drop the
        // bit; a word-level permutation would keep its offset in all of the others.
        assert!((1..=30).contains(&dropped), "dropped {dropped}");
        assert!(
            same_offset <= 8,
            "offset kept {same_offset} of {landed} times"
        );
        assert!(seen.len() >= 40, "only {} distinct positions", seen.len());
    }

    /// Additive output mode: valid authenticated triples under the additive key shares, the
    /// same for the same seeds, and no word repeated.
    #[test]
    fn additive_triples_are_valid_authenticated_and_deterministic() {
        let run = || {
            let sid = [0xa0; 32];
            let (_, mut rngs, mut mesh, alpha, _) = setup(sid, b"additive");
            let before = mesh.transcript_digest();
            let (triples, transcript) = run_pi_triple_f2_additive(
                sid,
                5,
                &alpha,
                &mut mesh,
                &mut rngs,
                &mut PiTripleF2Faults::default(),
            )
            .unwrap();
            assert_eq!(triples.words(), 5);
            assert_ne!(mesh.transcript_digest(), before);
            (open_additive(&triples, &alpha), transcript)
        };
        let (opened, transcript) = run();
        for w in 0..5 {
            assert!((0..w).all(|v| (opened[0][v], opened[1][v]) != (opened[0][w], opened[1][w])));
        }
        assert_eq!((opened, transcript), run());
    }

    /// Several raw ceremonies, two of them concurrent, feeding one combine pool: every triple
    /// is valid and the result is a function of the seeds alone.
    #[test]
    fn pooled_ceremonies_are_valid_and_independent_of_scheduling() {
        let run = || {
            let sid = [0xc0; 32];
            let (_, mut rngs, mut mesh, alpha, _) = setup(sid, b"pooled-ceremonies");
            // Seven words need 42 raw words: three ceremonies of 14.
            let (triples, _, transcript) = additive_pool(
                sid,
                7,
                16,
                &alpha,
                &mut mesh,
                &mut rngs,
                &mut PiTripleF2Faults::default(),
            )
            .unwrap();
            (open_additive(&triples, &alpha), transcript)
        };
        let first = run();
        assert_eq!(first.0[0].len(), 7);
        assert_eq!(first, run());
    }

    #[test]
    fn shamir_triples_are_boolean_products_of_degree_below_t() {
        let sid = [0xd0; 32];
        let (points, mut rngs, mut mesh, alpha, shared) = setup(sid, b"shamir");
        let (vaults, _) = run_pi_triple_f2(
            sid,
            2,
            &points,
            3,
            &alpha,
            &shared,
            &mut mesh,
            &mut rngs,
            &mut PiTripleF2Faults::default(),
        )
        .unwrap();
        for k in 0..3 {
            let open = |pick: fn(&KeccakBitTripleShare64) -> BitslicedGf256x64| {
                let shares: Vec<_> = vaults.iter().map(|v| pick(&v.triples[k])).collect();
                open_and_check_degree_bs_gf256(2, &points, &shares, "test").unwrap()
            };
            let (a, b, c) = (open(|tr| tr.a), open(|tr| tr.b), open(|tr| tr.c));
            assert_eq!(
                (&a[1..], &b[1..], &c[1..]),
                (&[0u64; 7][..], &[0u64; 7][..], &[0u64; 7][..])
            );
            assert_eq!(c[0], a[0] & b[0]);
        }
    }

    /// Every point where a party acts on its own shares: a wrong product share, a wrong fold
    /// cross term, a chosen-choice product fed something other than the party's share of the
    /// folded `b` (in a fold round and in the base case), a wrong share of a combine opening,
    /// and wrong Shamir value or MAC shares.
    #[test]
    fn rejects_product_fold_choice_opening_mac_and_degree_corruption() {
        for attack in 0..7 {
            let sid = [0xb0 + attack; 32];
            let (points, mut rngs, mut mesh, alpha, shared) = setup(sid, b"corruption");
            let mut product = |p: usize, words: &mut [u64]| {
                if p == 0 {
                    words[0] ^= 1;
                }
            };
            let mut fold = |round: usize, p: usize, terms: &mut [[u128; 2]; 2]| {
                if round == 0 && p == 0 {
                    terms[0][0] ^= 1;
                    terms[1][0] ^= 1;
                }
            };
            let mut seen_generic = None;
            let mut choice_fold = |round: usize, p: usize, choice: &mut u128| {
                let first = *seen_generic.get_or_insert(round);
                if round == first && p == 1 {
                    *choice ^= 1 << 77;
                }
            };
            // The base case reports the round count as its round.
            let base_round = FoldPlan::new(64 * combine_shape(2, Leak::ChoiceSide).0)
                .unwrap()
                .rounds();
            let mut choice_base = |round: usize, p: usize, choice: &mut u128| {
                if round == base_round && p == 2 {
                    *choice ^= 1;
                }
            };
            let mut opening = |p: usize, shares: &mut [u128]| {
                if p == 1 {
                    shares[0] ^= 1 << 5;
                }
            };
            let mut mac = |p: usize, tags: &mut [[[Tower128; 64]; 2]]| {
                if p == 0 {
                    tags[0][0][0].0 ^= 1;
                }
            };
            let mut degree =
                |p: usize, a: &mut [BitslicedGf256x64], _: &mut [BitslicedGf256x64]| {
                    if p == 2 {
                        a[0][0] ^= 1;
                    }
                };
            let mut faults = PiTripleF2Faults::default();
            let phase = match attack {
                0 => {
                    faults.product_shares = Some(&mut product);
                    None
                }
                1 => {
                    faults.fold_shares = Some(&mut fold);
                    None
                }
                2 => {
                    faults.choice_values = Some(&mut choice_fold);
                    Some("pi_triple_f2_choice")
                }
                3 => {
                    faults.choice_values = Some(&mut choice_base);
                    Some("pi_triple_f2_choice")
                }
                4 => {
                    faults.combine_shares = Some(&mut opening);
                    Some("pi_triple_f2_comb_b")
                }
                5 => {
                    faults.mac_shares = Some(&mut mac);
                    None
                }
                _ => {
                    faults.shamir_shares = Some(&mut degree);
                    None
                }
            };
            let err = run_pi_triple_f2(
                sid,
                2,
                &points,
                2,
                &alpha,
                &shared,
                &mut mesh,
                &mut rngs,
                &mut faults,
            )
            .err()
            .unwrap_or_else(|| panic!("accepted attack {attack}"));
            if let Some(phase) = phase {
                assert!(
                    matches!(err, PreprocessError::MacCheckFailed { phase: p, .. } if p == phase),
                    "attack {attack}: {err:?}"
                );
            }
        }
    }
}
