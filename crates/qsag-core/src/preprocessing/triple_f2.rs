//! `Π_triple_f2`: dealerless authenticated Boolean Beaver triples for Shamir-SPDZ.
//!
//! Every party contributes XOR shares of `a`, `b` and of the pairwise-OT product `c`. The
//! protocol authenticates those bits, proves `c = a & b` for the whole batch at once, converts
//! the shares to degree-`< t` Shamir form and combines raw triples `3 -> 1`:
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
//!    with probability 1/2 and is caught otherwise; this is the leakage the `3 -> 1` combine
//!    under a post-hoc bucket permutation is there to absorb.
//! 3. **Recursive inner-product sacrifice.** With public coins `chi_k` fixed after `c` is
//!    authenticated, `c = a & b` for all `k` is the inner-product claim
//!    `<(chi_k a_k), (b_k)> = sum chi_k c_k` over `GF(2)[x]/(x^128 + x^7 + x^2 + x + 1)`. Each
//!    round authenticates the two cross terms, draws a coin `r` and halves the claim
//!    (`a' = a_even + r a_odd`, `b' = r b_even + b_odd`, `c' = h0 + r c + r^2 h1`), ending in a
//!    masked opening of one product. This is the protocol of
//!    `recursive_sacrifice_false_claim_accepting_coins_bound` in
//!    `lean/Qsag/ActiveMigrationZeroTest.lean` up to the fixed index permutation that turns
//!    halves into even/odd positions: a false claim survives `r` rounds on at most a
//!    `2 (r + 1) / 2^128` fraction of coins. Two instances with independent coins run side by
//!    side, so a false batch is accepted with probability at most `(2 (r + 1) / 2^128)^2`.
//!    Cross terms are computed by unchecked OT products; the bound needs only that they are
//!    authenticated before the round coin.
//! 4. **Shamir conversion.** Each party deals degree-`< t` shares of its XOR share and of its
//!    additive MAC share. `spdz_pimac_check_bs_gf256_words` then accepts only degree-`< t`
//!    sharings whose MAC polynomial opens to `alpha * value` in both lanes. A dealt value other
//!    than the authenticated bit would need a MAC on a value the dealer has no MAC for, so the
//!    converted shares are Boolean and equal to the authenticated bits.
//! 5. **Combine.** Only after all of the above is a bucket coin drawn, bound to a digest of the
//!    locked shares; raw triples are combined `3 -> 1` with MAC-checked openings.

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

fn worker_count() -> usize {
    #[cfg(any(test, feature = "std"))]
    {
        std::thread::available_parallelism()
            .map_or(1, usize::from)
            .min(MAX_WORKERS)
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
    let mut t1 = SecretBuffer(vec![0u64; words]);
    for col in 0..256 {
        let col_le = (col as u64).to_le_bytes();
        let mut t0 = vec![0u64; words];
        let mut q = vec![0u64; words];
        stream_words(
            &ABIT_COL_MID,
            &[session_id, &holder_le, &owner_le, &col_le, &job.seeds0[col]],
            &mut t0,
        );
        stream_words(
            &ABIT_COL_MID,
            &[session_id, &holder_le, &owner_le, &col_le, &job.seeds1[col]],
            &mut t1,
        );
        stream_words(
            &ABIT_COL_MID,
            &[session_id, &holder_le, &owner_le, &col_le, &job.chosen[col]],
            &mut q,
        );
        let mask = 0u64.wrapping_sub(black_box(((delta[col / 128] >> (col % 128)) & 1) as u64));
        for w in 0..words {
            q[w] ^= mask & (t0[w] ^ t1[w] ^ rho[w]);
        }
        t_cols.push(t0);
        q_cols.push(q);
    }
    let mut t_lanes: [Vec<u128>; 2] =
        core::array::from_fn(|l| transpose_cols128_to_rows(&t_cols[128 * l..128 * (l + 1)], words));
    let mut q_lanes: [Vec<u128>; 2] =
        core::array::from_fn(|l| transpose_cols128_to_rows(&q_cols[128 * l..128 * (l + 1)], words));
    drop((t_cols, q_cols, t1));

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

        // Base OTs for this ceremony's key: the holder's choice bits are the bits of `alpha_i`.
        let mut jobs = Vec::with_capacity(n * (n - 1));
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
                let (send, recv) =
                    ot_mesh.run_correlated_ot_words(owner, holder, &choice, party_rngs)?;
                let take = |pad: &[u8; 48]| -> [u8; 32] { core::array::from_fn(|i| pad[i]) };
                jobs.push(PairExtension {
                    holder,
                    owner,
                    seeds0: SecretBuffer(send.iter().map(|pair| take(&pair.0)).collect()),
                    seeds1: SecretBuffer(send.iter().map(|pair| take(&pair.1)).collect()),
                    chosen: SecretBuffer(recv.iter().map(take).collect()),
                    chi_seed: party_rngs[holder].next_bytes32(),
                    rows: None,
                });
            }
        }

        let rho_ref = &rho;
        let delta_ref = &delta;
        par_for_each(&mut jobs, |job| {
            job.rows = Some(extend_pair(
                session_id,
                job,
                &rho_ref[job.owner],
                delta_ref[job.holder],
                rows,
            ));
        });

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

/// 128 pool rows used as OT choices. `d[p]` is owner `p`'s public derandomizer and `y[p]` its
/// private choice value.
struct ChoiceBlock {
    off: usize,
    d: Vec<u128>,
    y: SecretBuffer<Vec<u128>>,
}

// ---------------------------------------------------------------------------
// Correlation-robust hashing of pool rows (four rows per permutation call).
// ---------------------------------------------------------------------------

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

/// `SHAKE256(prefix || index || row)` for four rows, `blocks` rate blocks of output each.
fn crh_x4(
    prefix: &[u64; 8],
    index: [u64; 4],
    rows: &[Row; 4],
    blocks: usize,
    backend: qsag_asm::SimdBackend,
    out: &mut [[u64; RATE_WORDS * MAX_CRH_BLOCKS]; 4],
) {
    let mut st = qsag_asm::KeccakState4x::default();
    for (w, word) in prefix.iter().enumerate() {
        st.0[w] = [*word; 4];
    }
    for s in 0..4 {
        st.0[8][s] = index[s];
        st.0[9][s] = rows[s][0] as u64;
        st.0[10][s] = (rows[s][0] >> 64) as u64;
        st.0[11][s] = rows[s][1] as u64;
        st.0[12][s] = (rows[s][1] >> 64) as u64;
    }
    st.0[13] = [0x1f; 4];
    st.0[16] = [1u64 << 63; 4];
    for b in 0..blocks {
        qsag_asm::keccak_f1600_x4_with_backend(&mut st, backend);
        for w in 0..RATE_WORDS {
            for s in 0..4 {
                out[s][RATE_WORDS * b + w] = st.0[w][s];
            }
        }
    }
    qsag_asm::volatile_fill(&mut st.0, [0u64; 4]);
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

    /// Choice blocks of the chosen-choice rounds and of the masked base case, both instances.
    fn choice_blocks(&self) -> usize {
        let generic: usize = self.lens[self.structured..]
            .iter()
            .map(|l| 2 * (l / 2))
            .sum();
        2 * (generic + 2)
    }

    fn pair_rows(&self) -> usize {
        self.nbits + 128 * self.choice_blocks()
    }

    fn pool_rows(&self) -> usize {
        // `a`, `c`, four authenticated cross terms per round, four base products, the check mask.
        self.pair_rows() + 2 * self.nbits + 128 * (4 * self.rounds() + 4) + 512
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
    let mut o0 = [[0u64; RATE_WORDS * MAX_CRH_BLOCKS]; 4];
    let mut o1 = [[0u64; RATE_WORDS * MAX_CRH_BLOCKS]; 4];
    let mut or = [[0u64; RATE_WORDS * MAX_CRH_BLOCKS]; 4];
    for base in (0..job.len).step_by(4) {
        let k0 = job.start + base;
        let index: [u64; 4] = core::array::from_fn(|s| (k0 + s) as u64);
        let rows0: [Row; 4] = core::array::from_fn(|s| [q_rows[0][k0 + s], q_rows[1][k0 + s]]);
        let rows1: [Row; 4] =
            core::array::from_fn(|s| [rows0[s][0] ^ delta[0], rows0[s][1] ^ delta[1]]);
        let rows_r: [Row; 4] = core::array::from_fn(|s| [t_rows[0][k0 + s], t_rows[1][k0 + s]]);
        crh_x4(&prefix, index, &rows0, plan.crh_blocks, backend, &mut o0);
        crh_x4(&prefix, index, &rows1, plan.crh_blocks, backend, &mut o1);
        crh_x4(&prefix, index, &rows_r, plan.crh_blocks, backend, &mut or);
        for s in 0..4 {
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
        let mut o0 = [[0u64; RATE_WORDS * MAX_CRH_BLOCKS]; 4];
        let mut o1 = [[0u64; RATE_WORDS * MAX_CRH_BLOCKS]; 4];
        let mut or = [[0u64; RATE_WORDS * MAX_CRH_BLOCKS]; 4];
        for (j, product) in products.iter().enumerate() {
            let block = &blocks[product.block];
            let prefix = crh_prefix(session_id, job.holder, job.owner, first_domain + j as u64);
            let d = block.d[job.owner];
            let y = block.y[job.owner];
            let mut payload = product.x[job.holder];
            let (mut send, mut recv) = (0u128, 0u128);
            for base in (0..128).step_by(4) {
                let index: [u64; 4] = core::array::from_fn(|s| (block.off + base + s) as u64);
                let rows0: [Row; 4] = core::array::from_fn(|s| {
                    let k = block.off + base + s;
                    let adjust = bit_mask(((d >> (base + s)) & 1) as u64);
                    [
                        q_rows[0][k] ^ (adjust & delta[0]),
                        q_rows[1][k] ^ (adjust & delta[1]),
                    ]
                });
                let rows1: [Row; 4] =
                    core::array::from_fn(|s| [rows0[s][0] ^ delta[0], rows0[s][1] ^ delta[1]]);
                let rows_r: [Row; 4] = core::array::from_fn(|s| {
                    let k = block.off + base + s;
                    [t_rows[0][k], t_rows[1][k]]
                });
                crh_x4(&prefix, index, &rows0, 1, backend, &mut o0);
                crh_x4(&prefix, index, &rows1, 1, backend, &mut o1);
                crh_x4(&prefix, index, &rows_r, 1, backend, &mut or);
                for s in 0..4 {
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

/// Open additively shared field elements `shares[party][j]` and check their two-lane MACs
/// `macs[party][j]` against the parties' key shares. Value shares and MAC-check shares are
/// each committed before any is opened.
fn open_additive_authenticated(
    session_id: &[u8; 32],
    phase: &'static str,
    shares: &[Vec<u128>],
    macs: &[Vec<Row>],
    delta: &[Row],
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
    let mut total = vec![0u128; 2 * count];
    for p in 0..n {
        if !ct_eq_bytes32(&commit(b"sigma", p, &sigma[p], &salts[p]), &coms[p]) {
            return Err(PreprocessError::ShareCommitMismatch { phase, party_id: p });
        }
        wipe_bytes32(&mut salts[p]);
        for (dst, s) in total.iter_mut().zip(&sigma[p]) {
            *dst ^= *s;
        }
    }
    if total.iter().any(|v| *v != 0) {
        return Err(PreprocessError::MacCheckFailed {
            phase,
            accused_party: None,
        });
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
