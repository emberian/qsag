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
                let mut t_lanes: [Vec<u128>; 2] = [Vec::with_capacity(rows), Vec::with_capacity(rows)];
                let mut q_lanes: [Vec<u128>; 2] = [Vec::with_capacity(rows), Vec::with_capacity(rows)];
                for (lane, vaults) in [&mut *vaults_lane0, &mut *vaults_lane1].into_iter().enumerate() {
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
    pool: &mut DeltaCotPool,
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

    // Disposable mask word of the check: 512 pool bits per party, read as 64 `GF(256)` lanes.
    let chk_off = pool.alloc(512)?;
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
        let pool_ref = &*pool;
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
            let mut planes: BitslicedGf256x64 =
                core::array::from_fn(|pl| pool_ref.rho[p][chk_off / 64 + pl]);
            let dealt = SecretBuffer(shamir_share_planes(
                t,
                eval_mats_ref,
                &planes,
                &mut dealer.rng,
            ));
            wipe_u64s(&mut planes);
            for q in 0..n {
                dealer.dealt[q][num_words] = dealt[q];
            }
            for lane in 0..2 {
                for bit in 0..64 {
                    let mut acc = Tower128::ZERO;
                    for pl in 0..8 {
                        let mac = pool_ref.mac_bit(p, chk_off + 64 * pl + bit, lane, 0);
                        acc = acc.add(Tower128(mac).mul_gf256(TowerGf256(1u8 << pl)));
                    }
                    dealer.additive[num_words][lane][bit] = acc.0;
                }
            }
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
    drop((additive, seeds));

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
        nbits + 512,
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
    convert_to_shamir_and_check(
        session_id,
        t,
        eval_points,
        alpha_shamir,
        &mut pool,
        bit_words,
        &mac_bits,
        &transcript,
        party_rngs,
        &mut |_, _| {},
    )
}

// ---------------------------------------------------------------------------
// The triple protocol.
// ---------------------------------------------------------------------------

/// Deviations a test can inject at each point where a party acts on its own shares.
#[derive(Default)]
pub(super) struct PiTripleF2Faults<'a> {
    /// `(party, c words)`: the party's XOR share of the products, before it is authenticated.
    pub(super) product_shares: Option<&'a mut ProductTamper<'a>>,
    /// `(round, party, [instance][h0, h1])`: the party's cross-term shares of one fold round,
    /// before they are authenticated.
    pub(super) fold_shares: Option<&'a mut FoldTamper<'a>>,
    /// `(party, a shares, c shares)`: the Shamir value shares the party ends up holding.
    pub(super) shamir_shares: Option<&'a mut WordTamper<'a>>,
    /// `(party, a MAC shares)`: the Shamir MAC shares the party ends up holding.
    pub(super) mac_shares: Option<&'a mut MacTamper<'a>>,
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

/// The recursive inner-product sacrifice over the authenticated raw bits. Returns `Ok(())` only
/// if both instances' final product openings pass their MAC checks and their product tests.
#[expect(
    clippy::too_many_arguments,
    reason = "Shares, MAC shares, pads and randomness of one ceremony are separate protocol inputs"
)]
fn recursive_sacrifice(
    session_id: &[u8; 32],
    plan: &FoldPlan,
    pool: &mut DeltaCotPool,
    pads: &mut [PairPads],
    bits: [&[Vec<u64>]; 3],
    macs: [&[[Vec<u128>; 2]]; 3],
    transcript: &mut [u8; 32],
    party_rngs: &mut [PartyPrivateRng],
    faults: &mut PiTripleF2Faults<'_>,
) -> Result<(), PreprocessError> {
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
    let mut a_vec: SecretBuffer<[Vec<Vec<u128>>; 2]> = SecretBuffer(core::array::from_fn(|inst| {
        (0..n)
            .map(|p| {
                (0..nbits)
                    .map(|k| chi[inst][k] & bit_mask(word_bit(&a_bits[p], k)))
                    .collect()
            })
            .collect()
    }));
    let mut b_vec: SecretBuffer<[Vec<Vec<u128>>; 2]> = SecretBuffer(core::array::from_fn(|_| {
        (0..n)
            .map(|p| {
                (0..nbits)
                    .map(|k| u128::from(word_bit(&b_bits[p], k)))
                    .collect()
            })
            .collect()
    }));
    let mut c_val = SecretBuffer([vec![0u128; n], vec![0u128; n]]);
    let mut c_mac = SecretBuffer([vec![[0u128; 2]; n], vec![[0u128; 2]; n]]);
    for inst in 0..2 {
        for p in 0..n {
            for k in 0..nbits {
                c_val[inst][p] ^= chi[inst][k] & bit_mask(word_bit(&c_bits[p], k));
            }
            for lane in 0..2 {
                c_mac[inst][p][lane] = gf_dot(&chi[inst], &mac_c[p][lane]);
            }
        }
    }
    // Public coefficients of each raw bit in the folded entries.
    let mut tens_a: [Vec<u128>; 2] = [vec![1u128], vec![1u128]];
    let mut tens_b: [Vec<u128>; 2] = [vec![1u128], vec![1u128]];
    let mut product_domain = 1u64;

    for round in 0..plan.rounds() {
        let len = plan.lens[round];
        let pairs = len / 2;
        // `h[inst][party] = [h0, h1]` with `h0 = <a_even, b_odd>`, `h1 = <a_odd, b_even>`.
        let mut h = SecretBuffer([vec![[0u128; 2]; n], vec![[0u128; 2]; n]]);
        let mut halves: SecretBuffer<Vec<Vec<[Vec<u128>; 4]>>> =
            SecretBuffer(vec![Vec::with_capacity(n), Vec::with_capacity(n)]);
        for inst in 0..2 {
            for p in 0..n {
                let (a_even, a_odd) = split_even_odd(&a_vec[inst][p]);
                let (b_even, b_odd) = split_even_odd(&b_vec[inst][p]);
                h[inst][p][0] = gf_dot(&a_even[..pairs], &b_odd[..pairs]);
                h[inst][p][1] = gf_dot(&a_odd[..pairs], &b_even[..pairs]);
                halves[inst].push([a_even, a_odd, b_even, b_odd]);
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
            let mut blocks = Vec::with_capacity(4 * pairs);
            let mut products = Vec::with_capacity(4 * pairs);
            for inst in 0..2 {
                for i in 0..pairs {
                    for (slot, a_idx, b_idx) in [(0usize, 2 * i, 2 * i + 1), (1, 2 * i + 1, 2 * i)]
                    {
                        let y: SecretBuffer<Vec<u128>> =
                            SecretBuffer((0..n).map(|p| b_vec[inst][p][b_idx]).collect());
                        products.push(FieldProduct {
                            block: blocks.len(),
                            x: SecretBuffer((0..n).map(|p| a_vec[inst][p][a_idx]).collect()),
                            out: 2 * inst + slot,
                        });
                        blocks.push(pool.choose_field(&y)?);
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
    }

    // Masked base case on the single remaining pair of each instance:
    // open `a + rb u`, `b + rb v`, `c + rb d1 + rb^2 d2` with `d1 = a v + u b`, `d2 = u v`.
    let mut blocks = Vec::with_capacity(4);
    let mut products = Vec::with_capacity(6);
    for inst in 0..2 {
        let u = pool.random_field()?;
        let v = pool.random_field()?;
        let (u_idx, v_idx) = (blocks.len(), blocks.len() + 1);
        products.push(FieldProduct {
            block: v_idx,
            x: SecretBuffer((0..n).map(|p| a_vec[inst][p][0]).collect()),
            out: 2 * inst,
        });
        products.push(FieldProduct {
            block: u_idx,
            x: SecretBuffer((0..n).map(|p| b_vec[inst][p][0]).collect()),
            out: 2 * inst,
        });
        products.push(FieldProduct {
            block: v_idx,
            x: SecretBuffer(u.y.to_vec()),
            out: 2 * inst + 1,
        });
        blocks.push(u);
        blocks.push(v);
    }
    let mut d = SecretBuffer(cot_field_products(
        session_id,
        pool,
        &mut product_domain,
        &blocks,
        &products,
        4,
    ));
    for inst in 0..2 {
        let (u, v) = (&blocks[2 * inst], &blocks[2 * inst + 1]);
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
        let (u, v) = (&blocks[2 * inst], &blocks[2 * inst + 1]);
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
    let opened = open_additive_authenticated(
        session_id,
        "pi_triple_f2_sacrifice",
        &open_shares,
        &open_macs,
        &pool.delta,
        party_rngs,
    )?;
    for inst in 0..2 {
        if opened[3 * inst + 2] != gf_mul(opened[3 * inst], opened[3 * inst + 1]) {
            return Err(PreprocessError::SacrificeResidualNonZero {
                phase: "pi_triple_f2",
            });
        }
    }
    Ok(())
}

/// Runs `Π_triple_f2` and also returns the public bucket permutation it used: final triple `k`
/// is combined from raw triples `perm[k]`, `perm[num_triples + k]`, `perm[2 * num_triples + k]`.
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
) -> Result<(Vec<PreprocessedKeccakPartyVault>, Vec<u32>), PreprocessError> {
    let n = eval_points.len();
    let raw_triples = 3 * num_triples;
    let nbits = 64 * raw_triples;
    let plan = FoldPlan::new(nbits)?;
    let mut pool = DeltaCotPool::establish(
        &session_id,
        ot_mesh,
        alpha_contribs,
        plan.pool_rows(),
        plan.pair_rows(),
        party_rngs,
    )?;
    let mut transcript = session_id;

    // Raw `a` and `b` are the parties' pool bits themselves; `b` sits in the pair region.
    let off_b = pool.alloc_pair(nbits)?;
    let off_a = pool.alloc(nbits)?;
    let off_c = pool.alloc(nbits)?;
    let a_bits = SecretBuffer(
        (0..n)
            .map(|p| pool.rho_words(p, off_a, raw_triples))
            .collect::<Vec<_>>(),
    );
    let b_bits = SecretBuffer(
        (0..n)
            .map(|p| pool.rho_words(p, off_b, raw_triples))
            .collect::<Vec<_>>(),
    );

    // Hash every ordered pair's `b` rows once: AND cross terms now, fold pads for later.
    let unit = (1usize << plan.structured).max(64);
    let ranges_per_pair = (worker_count() / (n * (n - 1))).max(1);
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
    {
        let (pool_ref, plan_ref, a_ref, b_ref) = (&pool, &plan, &a_bits, &b_bits);
        par_for_each(&mut pads, |job| {
            let (holder, owner) = (job.holder, job.owner);
            hash_pair_pads(
                job,
                &session_id,
                pool_ref,
                plan_ref,
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
    let mut d_c = vec![0u64; raw_triples];
    for p in 0..n {
        for (k, word) in c_bits[p].iter().enumerate() {
            let d = *word ^ pool.rho[p][off_c / 64 + k];
            absorb_transcript(&mut transcript, b"c", &d.to_le_bytes());
            d_c[k] ^= d;
        }
    }
    let zero = vec![0u64; raw_triples];
    let mac_a: SecretBuffer<Vec<[Vec<u128>; 2]>> = SecretBuffer(
        (0..n)
            .map(|p| pool.mac_bits(p, off_a, nbits, &zero))
            .collect(),
    );
    let mac_b: SecretBuffer<Vec<[Vec<u128>; 2]>> = SecretBuffer(
        (0..n)
            .map(|p| pool.mac_bits(p, off_b, nbits, &zero))
            .collect(),
    );
    let mac_c: SecretBuffer<Vec<[Vec<u128>; 2]>> = SecretBuffer(
        (0..n)
            .map(|p| pool.mac_bits(p, off_c, nbits, &d_c))
            .collect(),
    );

    finish_pi_triple_f2_from_authenticated_raw(
        session_id,
        t,
        eval_points,
        num_triples,
        alpha_shamir,
        pool,
        &plan,
        pads,
        a_bits,
        b_bits,
        c_bits,
        mac_a,
        mac_b,
        mac_c,
        transcript,
        party_rngs,
        faults,
    )
}

/// Authenticate, sacrifice (`< 2^-256` two-instance recursive fold), Shamir-convert, and `3 -> 1`
/// bucket-combine silent Boolean Beaver triples drawn directly from locally expanded
/// [`crate::pcg_dense::DensePcgExpandedVault`]s without running `KosOtExtension`.
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
    party_rngs: &mut [PartyPrivateRng],
    faults: &mut PiTripleF2Faults<'_>,
) -> Result<(Vec<PreprocessedKeccakPartyVault>, Vec<u32>), PreprocessError> {
    let n = eval_points.len();
    let raw_triples = 3 * num_triples;
    let nbits = 64 * raw_triples;
    let plan = FoldPlan::new(nbits)?;

    let mut a_bits = SecretBuffer(vec![vec![0u64; raw_triples]; n]);
    let mut b_bits = SecretBuffer(vec![vec![0u64; raw_triples]; n]);
    let mut c_bits = SecretBuffer(vec![vec![0u64; raw_triples]; n]);
    for p in 0..n {
        for k in 0..raw_triples {
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

    // Prepare structured fold pads on `b` rows (AND shares are discarded because `c_bits` comes
    // directly from the silent `DensePcgExpandedVault`, and `recursive_sacrifice` verifies `c == a & b`).
    let unit = (1usize << plan.structured).max(64);
    let ranges_per_pair = (worker_count() / (n * (n - 1))).max(1);
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
    {
        let (pool_ref, plan_ref, a_ref, b_ref) = (&pool, &plan, &a_bits, &b_bits);
        par_for_each(&mut pads, |job| {
            let (holder, owner) = (job.holder, job.owner);
            hash_pair_pads(
                job,
                &session_id,
                pool_ref,
                plan_ref,
                &a_ref[holder],
                &b_ref[owner],
            );
        });
    }

    let mut d_a = vec![0u64; raw_triples];
    for p in 0..n {
        for (k, word) in a_bits[p].iter().enumerate() {
            let d = *word ^ pool.rho[p][off_a / 64 + k];
            absorb_transcript(&mut transcript, b"a", &d.to_le_bytes());
            d_a[k] ^= d;
        }
    }
    let mut d_c = vec![0u64; raw_triples];
    for p in 0..n {
        for (k, word) in c_bits[p].iter().enumerate() {
            let d = *word ^ pool.rho[p][off_c / 64 + k];
            absorb_transcript(&mut transcript, b"c", &d.to_le_bytes());
            d_c[k] ^= d;
        }
    }
    let zero = vec![0u64; raw_triples];
    let mac_a: SecretBuffer<Vec<[Vec<u128>; 2]>> = SecretBuffer(
        (0..n)
            .map(|p| pool.mac_bits(p, off_a, nbits, &d_a))
            .collect(),
    );
    let mac_b: SecretBuffer<Vec<[Vec<u128>; 2]>> = SecretBuffer(
        (0..n)
            .map(|p| pool.mac_bits(p, off_b, nbits, &zero))
            .collect(),
    );
    let mac_c: SecretBuffer<Vec<[Vec<u128>; 2]>> = SecretBuffer(
        (0..n)
            .map(|p| pool.mac_bits(p, off_c, nbits, &d_c))
            .collect(),
    );

    finish_pi_triple_f2_from_authenticated_raw(
        session_id,
        t,
        eval_points,
        num_triples,
        alpha_shamir,
        pool,
        &plan,
        pads,
        a_bits,
        b_bits,
        c_bits,
        mac_a,
        mac_b,
        mac_c,
        transcript,
        party_rngs,
        faults,
    )
}

#[expect(
    clippy::too_many_arguments,
    reason = "Internal helper sharing sacrifice, Shamir conversion, and 3->1 combiner between KOS and silent PCG pools"
)]
fn finish_pi_triple_f2_from_authenticated_raw(
    session_id: [u8; 32],
    t: usize,
    eval_points: &[TowerGf256],
    num_triples: usize,
    alpha_shamir: &[[Tower128; 2]],
    mut pool: DeltaCotPool,
    plan: &FoldPlan,
    mut pads: Vec<PairPads>,
    a_bits: SecretBuffer<Vec<Vec<u64>>>,
    b_bits: SecretBuffer<Vec<Vec<u64>>>,
    c_bits: SecretBuffer<Vec<Vec<u64>>>,
    mac_a: SecretBuffer<Vec<[Vec<u128>; 2]>>,
    mac_b: SecretBuffer<Vec<[Vec<u128>; 2]>>,
    mac_c: SecretBuffer<Vec<[Vec<u128>; 2]>>,
    mut transcript: [u8; 32],
    party_rngs: &mut [PartyPrivateRng],
    faults: &mut PiTripleF2Faults<'_>,
) -> Result<(Vec<PreprocessedKeccakPartyVault>, Vec<u32>), PreprocessError> {
    let n = eval_points.len();
    let raw_triples = 3 * num_triples;
    recursive_sacrifice(
        &session_id,
        plan,
        &mut pool,
        &mut pads,
        [&a_bits, &b_bits, &c_bits],
        [&mac_a, &mac_b, &mac_c],
        &mut transcript,
        party_rngs,
        faults,
    )?;
    drop(pads);

    // Degree-`< t` Shamir shares of all raw words and MACs, laid out `a | b | c`.
    let all_bits = SecretBuffer(
        (0..n)
            .map(|p| [&a_bits[p][..], &b_bits[p][..], &c_bits[p][..]].concat())
            .collect::<Vec<_>>(),
    );
    let all_macs: SecretBuffer<Vec<[Vec<u128>; 2]>> = SecretBuffer(
        (0..n)
            .map(|p| {
                core::array::from_fn(|lane| {
                    [
                        &mac_a[p][lane][..],
                        &mac_b[p][lane][..],
                        &mac_c[p][lane][..],
                    ]
                    .concat()
                })
            })
            .collect(),
    );
    drop((a_bits, b_bits, c_bits, mac_a, mac_b, mac_c));
    let (words_sh, macs_sh) = convert_to_shamir_and_check(
        &session_id,
        t,
        eval_points,
        alpha_shamir,
        &mut pool,
        &all_bits,
        &all_macs,
        &transcript,
        party_rngs,
        &mut |words, macs| {
            for p in 0..n {
                if let Some(hook) = faults.shamir_shares.as_mut() {
                    let (a_part, rest) = words[p].split_at_mut(raw_triples);
                    hook(p, a_part, &mut rest[raw_triples..]);
                }
                if let Some(hook) = faults.mac_shares.as_mut() {
                    hook(p, &mut macs[p][..raw_triples]);
                }
            }
        },
    )?;
    drop((all_bits, all_macs, pool));

    let mut a_sh = SecretBuffer(words_sh);
    let mut b_sh = SecretBuffer(Vec::with_capacity(n));
    let mut c_sh = SecretBuffer(Vec::with_capacity(n));
    let mut a_mac = SecretBuffer(macs_sh);
    let mut b_mac = SecretBuffer(Vec::with_capacity(n));
    let mut c_mac = SecretBuffer(Vec::with_capacity(n));
    for p in 0..n {
        c_sh.push(a_sh[p].split_off(2 * raw_triples));
        b_sh.push(a_sh[p].split_off(raw_triples));
        c_mac.push(a_mac[p].split_off(2 * raw_triples));
        b_mac.push(a_mac[p].split_off(raw_triples));
    }

    // Bucket assignment for the `3 -> 1` combine. Every raw share is authenticated and the
    // sacrifice has finished, so no party can still deviate on a raw triple or on a transfer
    // that depends on a raw bit. Only now is a joint coin drawn, bound to a digest of the locked
    // shares, and expanded into a uniform permutation of the raw triple indices.
    let lock_digest = pi_triple_f2_lock_digest(
        &session_id,
        raw_triples,
        a_sh.as_slice(),
        b_sh.as_slice(),
        c_sh.as_slice(),
        a_mac.as_slice(),
        b_mac.as_slice(),
        c_mac.as_slice(),
        party_rngs,
    );
    let bucket_coin = run_commit_and_open_coin(
        &session_id,
        b"PI_TRIPLE_F2_BUCKET",
        &lock_digest,
        party_rngs,
    )?;
    let bucket_perm = derive_coin_permutation(&bucket_coin, b"PI_TRIPLE_F2_BUCKET", raw_triples);

    // `3 -> 1` SPDZ-authenticated Beaver combine on both `a` and `b`. All `num_triples` bucket
    // openings `d = b0 ^ b1` and `e = a0 ^ a1 ^ a2` go through two committed `MacCheck` batches.
    let mut final_a = SecretBuffer(vec![vec![[0u64; 8]; num_triples]; n]);
    let mut final_b = SecretBuffer(vec![vec![[0u64; 8]; num_triples]; n]);
    let mut final_c = SecretBuffer(vec![vec![[0u64; 8]; num_triples]; n]);
    let mut final_a_mac = SecretBuffer(vec![vec![[[Tower128::ZERO; 64]; 2]; num_triples]; n]);
    let mut final_b_mac = SecretBuffer(vec![vec![[[Tower128::ZERO; 64]; 2]; num_triples]; n]);
    let mut final_c_mac = SecretBuffer(vec![vec![[[Tower128::ZERO; 64]; 2]; num_triples]; n]);

    let mut d_sh_batch = SecretBuffer(vec![vec![[0u64; 8]; num_triples]; n]);
    let mut d_mac_batch = SecretBuffer(vec![vec![[[Tower128::ZERO; 64]; 2]; num_triples]; n]);
    for k in 0..num_triples {
        let k0 = bucket_perm[k] as usize;
        let k1 = bucket_perm[num_triples + k] as usize;
        for p in 0..n {
            d_sh_batch[p][k] = bs_gf256_xor(&b_sh[p][k0], &b_sh[p][k1]);
            for lane in 0..2 {
                for bit in 0..64 {
                    d_mac_batch[p][k][lane][bit] =
                        b_mac[p][k0][lane][bit].add(b_mac[p][k1][lane][bit]);
                }
            }
        }
    }
    let d_opened = commit_and_open_spdz_bs_gf256_batch_quorum(
        &session_id,
        "pi_triple_f2_comb_d",
        t,
        eval_points,
        d_sh_batch.as_slice(),
        d_mac_batch.as_slice(),
        alpha_shamir,
        party_rngs,
    )?;
    drop((d_sh_batch, d_mac_batch));

    let mut e_sh_batch = SecretBuffer(vec![vec![[0u64; 8]; num_triples]; n]);
    let mut e_mac_batch = SecretBuffer(vec![vec![[[Tower128::ZERO; 64]; 2]; num_triples]; n]);
    for k in 0..num_triples {
        let k0 = bucket_perm[k] as usize;
        let k1 = bucket_perm[num_triples + k] as usize;
        let k2 = bucket_perm[2 * num_triples + k] as usize;
        for p in 0..n {
            let a_mid_p = bs_gf256_xor(&a_sh[p][k0], &a_sh[p][k1]);
            final_a[p][k] = a_mid_p;
            e_sh_batch[p][k] = bs_gf256_xor(&a_mid_p, &a_sh[p][k2]);
            for lane in 0..2 {
                for bit in 0..64 {
                    let a_mid_m = a_mac[p][k0][lane][bit].add(a_mac[p][k1][lane][bit]);
                    final_a_mac[p][k][lane][bit] = a_mid_m;
                    e_mac_batch[p][k][lane][bit] = a_mid_m.add(a_mac[p][k2][lane][bit]);
                }
            }
        }
    }
    let e_opened = commit_and_open_spdz_bs_gf256_batch_quorum(
        &session_id,
        "pi_triple_f2_comb_e",
        t,
        eval_points,
        e_sh_batch.as_slice(),
        e_mac_batch.as_slice(),
        alpha_shamir,
        party_rngs,
    )?;
    drop((e_sh_batch, e_mac_batch));

    for k in 0..num_triples {
        let k0 = bucket_perm[k] as usize;
        let k1 = bucket_perm[num_triples + k] as usize;
        let k2 = bucket_perm[2 * num_triples + k] as usize;
        let d_open = &d_opened[k];
        let e_open = &e_opened[k];

        for p in 0..n {
            let da1 = bs_gf256_mul_planes_ct(d_open, &a_sh[p][k1]);
            let mut c_mid = bs_gf256_xor(&bs_gf256_xor(&c_sh[p][k0], &c_sh[p][k1]), &da1);
            final_b[p][k] = bs_gf256_xor(&b_sh[p][k0], &b_sh[p][k2]);
            let eb2 = bs_gf256_mul_planes_ct(e_open, &b_sh[p][k2]);
            final_c[p][k] = bs_gf256_xor(&bs_gf256_xor(&c_mid, &c_sh[p][k2]), &eb2);
            wipe_u64s(&mut c_mid);

            for bit in 0..64 {
                let d_gf = bs_gf256_extract_lane(d_open, bit);
                let e_gf = bs_gf256_extract_lane(e_open, bit);
                for lane in 0..2 {
                    final_b_mac[p][k][lane][bit] =
                        b_mac[p][k0][lane][bit].add(b_mac[p][k2][lane][bit]);
                    final_c_mac[p][k][lane][bit] = c_mac[p][k0][lane][bit]
                        .add(c_mac[p][k1][lane][bit])
                        .add(a_mac[p][k1][lane][bit].mul_gf256(d_gf))
                        .add(c_mac[p][k2][lane][bit])
                        .add(b_mac[p][k2][lane][bit].mul_gf256(e_gf));
                }
            }
        }
    }
    drop((a_sh, b_sh, c_sh, a_mac, b_mac, c_mac));

    let mut vaults = Vec::with_capacity(n);
    for p in 0..n {
        let mut triples = Vec::with_capacity(num_triples);
        for k in 0..num_triples {
            triples.push(KeccakBitTripleShare64 {
                a: final_a[p][k],
                b: final_b[p][k],
                c: final_c[p][k],
                a_mac: final_a_mac[p][k],
                b_mac: final_b_mac[p][k],
                c_mac: final_c_mac[p][k],
            });
        }
        vaults.push(PreprocessedKeccakPartyVault {
            party_id: p,
            eval_point: eval_points[p],
            mac_alpha_lanes: alpha_shamir[p],
            triples,
            cursor: 0,
            poisoned: false,
        });
    }
    Ok((vaults, bucket_perm))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_product_fold_mac_and_degree_corruption() {
        for attack in 0..4 {
            let sid = [0xb0 + attack; 32];
            let mut rngs: Vec<_> = (0..3)
                .map(|p| PartyPrivateRng::from_seed([p + 1; 32], b"fold-corruption"))
                .collect();
            let points = [TowerGf256(1), TowerGf256(2), TowerGf256(3)];
            let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut rngs);
            let (alpha, shared) = spdz_setup_alpha_gf256(&sid, 2, &points, &mut rngs).unwrap();
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
            match attack {
                0 => faults.product_shares = Some(&mut product),
                1 => faults.fold_shares = Some(&mut fold),
                2 => faults.mac_shares = Some(&mut mac),
                _ => faults.shamir_shares = Some(&mut degree),
            }
            assert!(
                run_pi_triple_f2(
                    sid,
                    2,
                    &points,
                    2,
                    &alpha,
                    &shared,
                    &mut mesh,
                    &mut rngs,
                    &mut faults
                )
                .is_err(),
                "accepted attack {attack}"
            );
        }
    }
}
