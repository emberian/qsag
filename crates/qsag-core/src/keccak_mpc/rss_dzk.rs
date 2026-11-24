use super::*;

// The proof only embeds Boolean values, so it can use the polynomial field
// GF(2)[t]/(t^128 + t^7 + t^2 + t + 1) directly. No conversion of Keccak shares or
// FIPS 205 outputs is involved.
#[derive(Clone, Copy)]
pub(super) struct RssProofField(pub(super) u128);

impl RssProofField {
    pub(super) const ZERO: Self = Self(0);
    pub(super) const ONE: Self = Self(1);

    pub(super) fn add(self, rhs: Self) -> Self {
        Self(self.0 ^ rhs.0)
    }

    pub(super) fn mul(self, rhs: Self) -> Self {
        RssFieldMultiplier::new(rhs).mul(self)
    }

    /// Multiply by the public monomial `t^shift`, `shift < 64`.
    pub(super) fn mul_t_pow(self, shift: u32) -> Self {
        if shift == 0 {
            return self;
        }
        let lo = self.0 << shift;
        // Fewer than 64 overflow bits, so their reduction has degree below 71.
        let hi = self.0 >> (128 - shift);
        Self(lo ^ hi ^ (hi << 1) ^ (hi << 2) ^ (hi << 7))
    }

    /// Inverse of a public nonzero element: `x^(2^128 - 2)`.
    pub(super) fn inv_public(self) -> Self {
        let mut acc = Self::ONE;
        let mut sq = self;
        for _ in 1..128 {
            sq = sq.mul(sq);
            acc = acc.mul(sq);
        }
        acc
    }

    fn from_coin(coin: &[u8; 32]) -> Self {
        let mut bytes = [0u8; 16];
        bytes.copy_from_slice(&coin[..16]);
        Self(u128::from_le_bytes(bytes))
    }

    fn nonzero(self) -> Self {
        if self.0 == 0 { Self::ONE } else { self }
    }

    fn ct_eq(self, rhs: Self) -> bool {
        black_box(self.0 ^ rhs.0) == 0
    }
}

/// Fixed operand in the polynomial field used by the active RSS proof.
/// Share the hardware-dispatched arithmetic with the 256-bit RSS engine.
struct RssFieldMultiplier {
    operand: [u64; 2],
}

impl RssFieldMultiplier {
    #[inline]
    fn new(v: RssProofField) -> Self {
        Self {
            operand: [v.0 as u64, (v.0 >> 64) as u64],
        }
    }

    #[inline]
    fn mul(&self, x: RssProofField) -> RssProofField {
        let mut out = [0; 2];
        qsag_asm::gf2_128_mul_acc_batch(
            &mut out,
            &[[x.0 as u64, (x.0 >> 64) as u64]],
            &[self.operand],
        );
        RssProofField(u128::from(out[0]) | (u128::from(out[1]) << 64))
    }
}

impl crate::wipe::SecretWipe for RssProofField {
    fn secret_wipe(&mut self) {
        self.0 = 0;
        core::hint::black_box(self);
    }
}

fn wipe_rss_proof_field(values: &mut [RssProofField]) {
    qsag_asm::volatile_fill(values, RssProofField::ZERO);
}

/// Word-index bits bound by the packed sumcheck rounds.
pub(super) const RSS_DZK_TENSOR_BITS: usize = 6;
/// Relation words per group, `2^RSS_DZK_TENSOR_BITS`.
pub(super) const RSS_DZK_GROUP_WORDS: usize = 1 << RSS_DZK_TENSOR_BITS;
/// Evaluation points `{0, 1, slope}^RSS_DZK_TENSOR_BITS` per group, `3^RSS_DZK_TENSOR_BITS`.
pub(super) const RSS_DZK_TERNARY: usize = 3usize.pow(RSS_DZK_TENSOR_BITS as u32);
/// Bit lanes (sponge instances) per relation word.
pub(super) const RSS_DZK_LANES: usize = 64;
/// Four-word groups whose subset XORs are tabulated when binding a group.
pub(super) const RSS_DZK_NIBBLES: usize = RSS_DZK_GROUP_WORDS / 4;

/// Expand the `2^r` words of a group indexed by `u` into `3^r` words indexed by
/// `e = sum_l e_l * 3^l`: digit `0` keeps the `u_l = 0` half, digit `1` the `u_l = 1` half,
/// digit `2` their XOR. Works in place: each stage rewrites blocks from the top down, so a
/// block's destination never covers sources that are still unread.
pub(super) fn rss_ternary_expand(src: &[u64], out: &mut [u64; RSS_DZK_TERNARY]) {
    out[..RSS_DZK_GROUP_WORDS].copy_from_slice(&src[..RSS_DZK_GROUP_WORDS]);
    let mut pow3 = 1usize;
    let mut high = RSS_DZK_GROUP_WORDS;
    for _ in 0..RSS_DZK_TENSOR_BITS {
        let half = high / 2;
        for uh in (0..half).rev() {
            let src0 = pow3 * (2 * uh);
            let dst = 3 * pow3 * uh;
            for el in 0..pow3 {
                let x0 = out[src0 + el];
                let x1 = out[src0 + pow3 + el];
                out[dst + el] = x0;
                out[dst + pow3 + el] = x1;
                out[dst + 2 * pow3 + el] = x0 ^ x1;
            }
        }
        pow3 *= 3;
        high = half;
    }
}

/// For each of four columns of 64 secret words `rows[u][c]` and public coefficients `beta_u`,
/// compute the 64 field elements `out[i][c] = sum_u beta_u * bit_i(rows[u][c])`.
/// `pattern[bit][g]` is the public nibble of coefficient bit `bit` over words `4g..4g+4`;
/// only public values index memory. `planes` is caller scratch holding secret bit planes.
pub(super) fn rss_bind_columns(
    rows: &[[u64; 4]; RSS_DZK_GROUP_WORDS],
    pattern: &qsag_asm::XorCombinePattern,
    planes: &mut [[[u64; 4]; 64]; 2],
    out: &mut [[u128; 4]; RSS_DZK_LANES],
) {
    // Plane `k` of half `h` holds coefficient bit `64 h + k` of all 64 lanes of every column.
    qsag_asm::gf2_xor_combine_planes(rows, pattern, planes);
    // Transposed, row `i` of half `h` holds limb `h` of lane `i` of every column.
    let [low, high] = planes;
    qsag_asm::transpose64x256(low);
    qsag_asm::transpose64x256(high);
    for ((out, low), high) in out.iter_mut().zip(low.iter()).zip(high.iter()) {
        for ((value, lo), hi) in out.iter_mut().zip(low).zip(high) {
            *value = u128::from(*lo) | (u128::from(*hi) << 64);
        }
    }
}

/// Public per-pass weights. Relation word `k = 64 * g + u` has weight
/// `nu[g] * prod_{l in bits(u)} mu[l]`, with `nu[g] = prod_{l in bits(g)} nu_bits[l]`.
pub(super) struct RssDzkWeights {
    pub(super) mu: [RssProofField; RSS_DZK_TENSOR_BITS],
    pub(super) nu: Vec<RssProofField>,
}

struct RssDzkCtx<'a> {
    session_id: &'a [u8; 32],
    batch_ctr: u64,
    groups: usize,
    /// Latch of the accumulator under verification.
    poison: &'a RssPoisonLatch,
}

impl RssDzkCtx<'_> {
    fn coin(
        &self,
        label: &[u8],
        pass: usize,
        step: usize,
        party_rngs: &mut [PartyPrivateRng; 3],
    ) -> Result<RssProofField, KeccakMpcError> {
        let mut bind = [0u8; 32];
        bind[0] = pass as u8;
        bind[4..8].copy_from_slice(&(step as u32).to_le_bytes());
        bind[8..16].copy_from_slice(&self.batch_ctr.to_le_bytes());
        bind[16..24].copy_from_slice(&(self.groups as u64).to_le_bytes());
        match run_commit_and_open_coin(self.session_id, label, &bind, party_rngs) {
            Ok(coin) => Ok(RssProofField::from_coin(&coin)),
            Err(e) => self.poison.fail(e.into()),
        }
    }
}

/// Proof tables of one pass: slot shares of the bound `a` (weighted by `t^lane`) and `b`
/// vectors. Wiped on `Drop`.
///
/// The buffers outlive a pass and are reused by the next one. A pass needs about 10 MiB per
/// table at the deferred flush size; allocated fresh, that memory comes back from the kernel
/// unmapped every time and the binding workers fault it in page by page, which costs more
/// than the field arithmetic.
#[derive(Default)]
pub(super) struct RssDzkTables {
    x: [Vec<u128>; 3],
    y: [Vec<u128>; 3],
    /// Leading elements of every table that may be nonzero. All elements behind are zero.
    live: usize,
}

impl RssDzkTables {
    /// Size every table to `len` zero elements and mark them all live for the pass that is
    /// about to fill them. The previous pass must have ended with [`Self::wipe_live`].
    fn begin_pass(&mut self, len: usize) {
        self.wipe_live();
        for table in self.x.iter_mut().chain(&mut self.y) {
            table.resize(len, 0);
        }
        self.live = len;
    }

    /// Zero the live prefix, restoring the all-zero state between passes.
    fn wipe_live(&mut self) {
        for table in self.x.iter_mut().chain(&mut self.y) {
            let live = self.live.min(table.len());
            qsag_asm::volatile_fill(&mut table[..live], 0);
        }
        self.live = 0;
    }
}

impl Drop for RssDzkTables {
    fn drop(&mut self) {
        for s in 0..3 {
            qsag_asm::volatile_fill(&mut self.x[s], 0);
            qsag_asm::volatile_fill(&mut self.y[s], 0);
        }
    }
}

/// Elements per dot-product call in a halving round; bounds a worker's operand scratch at
/// 32 KiB.
const RSS_DZK_FOLD_BLOCK: usize = 1024;
/// Lower-half length from which a halving round is split across threads. Every partial
/// result is combined by XOR, so the split changes no message and no challenge.
#[cfg(feature = "std")]
const RSS_DZK_FOLD_PAR_MIN: usize = 1 << 14;

/// Worker budget of the proof. Queried once: `available_parallelism` reads the scheduler
/// affinity and the cgroup quota files on every call.
#[cfg(feature = "std")]
fn rss_dzk_workers() -> usize {
    static WORKERS: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *WORKERS.get_or_init(|| {
        std::thread::available_parallelism()
            .map_or(1, usize::from)
            .min(16)
    })
}

/// `(lower half, upper half)` of one slot's table in a halving round, equal lengths.
type RssFoldHalves<'a> = (&'a [u128], &'a [u128]);

/// Party `p`'s additive shares of `L = <x_lo, y_hi>` and `R = <x_hi, y_lo>` over one index
/// range, from the slot-`p` and slot-`q = p + 1` halves of that range. Its share of a product
/// `sum x * y` of replicated sharings is `sum x_p * (y_p + y_q) + sum x_q * y_p`; the tables
/// are read where they lie and only the sums `y_p + y_q` go through scratch.
fn rss_fold_cross_dot(
    xp: RssFoldHalves<'_>,
    xq: RssFoldHalves<'_>,
    yp: RssFoldHalves<'_>,
    yq: RssFoldHalves<'_>,
) -> [u128; 2] {
    let dot = qsag_asm::gf2_128_dot;
    fn cut(h: RssFoldHalves<'_>, start: usize, end: usize) -> RssFoldHalves<'_> {
        (&h.0[start..end], &h.1[start..end])
    }
    let mut y_lo = [0u128; RSS_DZK_FOLD_BLOCK];
    let mut y_hi = [0u128; RSS_DZK_FOLD_BLOCK];
    let mut out = [0u128; 2];
    let n = xp.0.len();
    for start in (0..n).step_by(RSS_DZK_FOLD_BLOCK) {
        let end = (start + RSS_DZK_FOLD_BLOCK).min(n);
        let (xp, xq) = (cut(xp, start, end), cut(xq, start, end));
        let (yp, yq) = (cut(yp, start, end), cut(yq, start, end));
        let y_lo = &mut y_lo[..end - start];
        let y_hi = &mut y_hi[..end - start];
        for ((sum, p), q) in y_lo.iter_mut().zip(yp.0).zip(yq.0) {
            *sum = p ^ q;
        }
        for ((sum, p), q) in y_hi.iter_mut().zip(yp.1).zip(yq.1) {
            *sum = p ^ q;
        }
        out[0] ^= dot(xp.0, y_hi) ^ dot(xq.0, yp.1);
        out[1] ^= dot(xp.1, y_lo) ^ dot(xq.1, yp.0);
    }
    let used = n.min(RSS_DZK_FOLD_BLOCK);
    wipe_u128s(&mut y_lo[..used]);
    wipe_u128s(&mut y_hi[..used]);
    out
}

/// All three parties' `(L, R)` shares of one halving round.
pub(super) fn rss_fold_cross_dots<'a>(
    xs: &[RssFoldHalves<'a>; 3],
    ys: &[RssFoldHalves<'a>; 3],
) -> [[u128; 2]; 3] {
    let n = xs[0].0.len();
    let range_dot = |p: usize, start: usize, end: usize| {
        let q = (p + 1) % 3;
        let cut =
            |h: RssFoldHalves<'a>| -> RssFoldHalves<'a> { (&h.0[start..end], &h.1[start..end]) };
        rss_fold_cross_dot(cut(xs[p]), cut(xs[q]), cut(ys[p]), cut(ys[q]))
    };
    #[cfg(feature = "std")]
    if n >= RSS_DZK_FOLD_PAR_MIN {
        let chunk = n.div_ceil(rss_dzk_workers().div_ceil(3));
        let range_dot = &range_dot;
        return std::thread::scope(|scope| {
            let handles: Vec<_> = (0..3)
                .flat_map(|p| (0..n).step_by(chunk).map(move |start| (p, start)))
                .map(|(p, start)| {
                    scope.spawn(move || (p, range_dot(p, start, (start + chunk).min(n))))
                })
                .collect();
            let mut out = [[0u128; 2]; 3];
            for handle in handles {
                let (p, mut part) = handle.join().expect("RSS fold worker failed");
                out[p][0] ^= part[0];
                out[p][1] ^= part[1];
                wipe_u128s(&mut part);
            }
            out
        });
    }
    core::array::from_fn(|p| range_dot(p, 0, n))
}

/// The first `len` elements below and from `upper` of every slot's table.
pub(super) fn rss_fold_halves(
    table: &[Vec<u128>; 3],
    upper: usize,
    len: usize,
) -> [RssFoldHalves<'_>; 3] {
    core::array::from_fn(|s| {
        let (lo, hi) = table[s].split_at(upper);
        (&lo[..len], &hi[..len])
    })
}

/// `lo[i] ^= scale * hi[i]` for each `(lo, hi, scale)` job, with public scales. The folded
/// `hi` is dead afterwards and is wiped by the worker that just read it.
pub(super) fn rss_fold_scale_xor(jobs: &mut [(&mut [u128], &mut [u128], RssProofField)]) {
    let apply = |lo: &mut [u128], hi: &mut [u128], scale: RssProofField| {
        qsag_asm::bitslice::gf2_128_scale_xor(lo, hi, scale.0);
        qsag_asm::volatile_fill(hi, 0);
    };
    #[cfg(feature = "std")]
    if jobs
        .first()
        .is_some_and(|job| job.0.len() >= RSS_DZK_FOLD_PAR_MIN)
    {
        let per_job = rss_dzk_workers().div_ceil(jobs.len());
        let apply = &apply;
        std::thread::scope(|scope| {
            for (lo, hi, scale) in jobs.iter_mut() {
                let chunk = lo.len().div_ceil(per_job);
                let scale = *scale;
                for (lo, hi) in lo.chunks_mut(chunk).zip(hi.chunks_mut(chunk)) {
                    scope.spawn(move || apply(lo, hi, scale));
                }
            }
        });
        return;
    }
    for (lo, hi, scale) in jobs.iter_mut() {
        apply(lo, hi, *scale);
    }
}

/// One halving round of the weighted inner-product argument over tables of blocks of `unit`
/// elements (`x` already carries the per-group public weights `w_g`); `hi_groups` blocks exist
/// in the upper half, which starts at block `half`. The invariant `claim = sum_g <x_g, y_g>` is
/// preserved by `x' = x_lo + gamma * x_hi`, `y' = y_lo + gamma^-1 * y_hi`,
/// `claim' = claim + gamma^-1 * L + gamma * R`, where `L = sum_g <x_lo, y_hi>` and
/// `R = sum_g <x_hi, y_lo>` are sent as masked additive shares before `gamma` is drawn.
#[expect(
    clippy::too_many_arguments,
    reason = "One protocol round: tables, dimensions, claim, randomness and challenge context"
)]
fn rss_dzk_fold_round(
    ctx: &RssDzkCtx<'_>,
    pass: usize,
    step: usize,
    tables: &mut RssDzkTables,
    unit: usize,
    hi_groups: usize,
    half: usize,
    claim: &mut [RssProofField; 3],
    streams: &mut RssProofStreams,
    party_rngs: &mut [PartyPrivateRng; 3],
) -> Result<(), KeccakMpcError> {
    let mut l_msg = SecretBuffer(streams.zero_share());
    let mut r_msg = SecretBuffer(streams.zero_share());
    let RssDzkTables { x, y, live } = tables;
    let len = hi_groups * unit;
    let upper = half * unit;
    {
        // Lane 0 accumulates <x_lo, y_hi>, lane 1 accumulates <x_hi, y_lo>.
        let mut dots = rss_fold_cross_dots(
            &rss_fold_halves(x, upper, len),
            &rss_fold_halves(y, upper, len),
        );
        for p in 0..3 {
            l_msg[p] = l_msg[p].add(RssProofField(dots[p][0]));
            r_msg[p] = r_msg[p].add(RssProofField(dots[p][1]));
        }
        wipe_u128s(dots.as_flattened_mut());
    }

    let gamma = ctx
        .coin(b"RSS_DZK_POLY_FOLD_COIN/v3", pass, step, party_rngs)?
        .nonzero();
    let gamma_inv = gamma.inv_public();
    for s in 0..3 {
        claim[s] = claim[s]
            .add(gamma_inv.mul(l_msg[s]))
            .add(gamma.mul(r_msg[s]));
    }
    let mut jobs: Vec<(&mut [u128], &mut [u128], RssProofField)> = Vec::with_capacity(6);
    for (table, scale) in [(x, gamma), (y, gamma_inv)] {
        for slot in table.iter_mut() {
            let (lo, hi) = slot.split_at_mut(upper);
            jobs.push((&mut lo[..len], &mut hi[..len], scale));
        }
    }
    rss_fold_scale_xor(&mut jobs);
    // Everything from `upper` on was either folded and wiped just now or never written.
    *live = (*live).min(upper);
    Ok(())
}

/// Unreduced sum of products of 64-bit words with 128-bit weights, as accumulated by
/// [`qsag_asm::gf2_64x128_clmul_acc`]: the value is `acc[0] + t^64 * acc[1]`.
type RssWideSum = [u128; 2];

/// Reduce an [`RssWideSum`] (degree below 191) modulo `t^128 + t^7 + t^2 + t + 1`.
fn rss_reduce_wide(sum: RssWideSum) -> u128 {
    let low = sum[0] ^ (sum[1] << 64);
    // Fewer than 64 overflow bits, so their reduction has degree below 71.
    let high = sum[1] >> 64;
    low ^ high ^ (high << 1) ^ (high << 2) ^ (high << 7)
}

/// Per-party additive shares of the packed sumcheck tables for both passes.
///
/// For every group `g` and every point `e in {0, 1, slope}^6`, the 64 words of the group are
/// combined over GF(2) into one word per operand (`a_e`, `b_e`); party `p` forms its share
/// `T = a_e,p & (b_e,p ^ b_e,q) ^ a_e,q & b_e,p` of the 64 products with word operations, and
/// accumulates `sum_g nu[g] * T(t)`, where `T(t)` reads the word as a polynomial of degree
/// below 64. Lane 0 uses the pass-0 weights and lane 1 the pass-1 weights. Nothing here depends
/// on a round challenge, so all six packed rounds read these `729` sums.
pub(super) fn rss_dzk_tensor_tables(
    pending: &RssPendingDzkTriples,
    groups: usize,
    nu_pairs: &[[u128; 2]],
) -> [Vec<[u128; 2]>; 3] {
    #[cfg(feature = "std")]
    if groups >= 128 {
        let chunk = groups.div_ceil(rss_dzk_workers());
        return std::thread::scope(|scope| {
            let handles: Vec<_> = nu_pairs
                .chunks(chunk)
                .enumerate()
                .map(|(i, weights)| {
                    scope.spawn(move || rss_dzk_tensor_tables_range(pending, i * chunk, weights))
                })
                .collect();
            let mut total: [Vec<[u128; 2]>; 3] =
                core::array::from_fn(|_| vec![[0; 2]; RSS_DZK_TERNARY]);
            for handle in handles {
                let mut part = handle.join().expect("RSS tensor worker failed");
                for (dst, src) in total.iter_mut().zip(&mut part) {
                    for (dst, src) in dst.iter_mut().zip(src.iter()) {
                        dst[0] ^= src[0];
                        dst[1] ^= src[1];
                    }
                    qsag_asm::volatile_fill(src, [0; 2]);
                }
            }
            total
        });
    }
    debug_assert_eq!(groups, nu_pairs.len());
    rss_dzk_tensor_tables_range(pending, 0, nu_pairs)
}

pub(super) fn rss_dzk_tensor_tables_range(
    pending: &RssPendingDzkTriples,
    first_group: usize,
    nu_pairs: &[[u128; 2]],
) -> [Vec<[u128; 2]>; 3] {
    // `sums[p][lane][e]`: party `p`'s product-share word of point `e`, times the lane's group
    // weight, summed over the groups. A product word has degree below 64, so it enters by
    // two carryless multiplications and the sum is reduced once per point at the end.
    let mut sums: [[Vec<RssWideSum>; 2]; 3] =
        core::array::from_fn(|_| core::array::from_fn(|_| vec![[0u128; 2]; RSS_DZK_TERNARY]));
    let mut ea = [[0u64; RSS_DZK_TERNARY]; 3];
    let mut eb = [[0u64; RSS_DZK_TERNARY]; 3];
    for (g, nu) in nu_pairs.iter().enumerate() {
        let w0 = (first_group + g) * RSS_DZK_GROUP_WORDS;
        for s in 0..3 {
            rss_ternary_expand(&pending.a[s][w0..], &mut ea[s]);
            rss_ternary_expand(&pending.b[s][w0..], &mut eb[s]);
        }
        // The tensor entries contain the local product terms before resharing.
        // Reuse the expanded left operand once all three shares of a point are read.
        for e in 0..RSS_DZK_TERNARY {
            let share = |words: &[[u64; RSS_DZK_TERNARY]; 3]| qsag_verified::RssShare64 {
                x0: words[0][e],
                x1: words[1][e],
                x2: words[2][e],
            };
            let prod = qsag_verified::rss_and_gate(share(&ea), share(&eb), Default::default());
            [ea[0][e], ea[1][e], ea[2][e]] = [prod.x0, prod.x1, prod.x2];
        }
        for (party_sums, products) in sums.iter_mut().zip(&ea) {
            for (sums, weight) in party_sums.iter_mut().zip(nu) {
                qsag_asm::gf2_64x128_clmul_acc(sums, products, *weight);
            }
        }
    }
    let tabs = core::array::from_fn(|p| {
        let [lane0, lane1] = &sums[p];
        lane0
            .iter()
            .zip(lane1)
            .map(|(a, b)| [rss_reduce_wide(*a), rss_reduce_wide(*b)])
            .collect()
    });
    for sums in sums.iter_mut().flatten() {
        qsag_asm::volatile_fill(sums, [0; 2]);
    }
    for s in 0..3 {
        wipe_u64s(&mut ea[s]);
        wipe_u64s(&mut eb[s]);
    }
    tabs
}

/// Slot shares of the weighted claims `sum_k weight(k) * c_k(t)` for both passes.
pub(super) fn rss_dzk_initial_claims(
    pending: &RssPendingDzkTriples,
    groups: usize,
    weights: &[RssDzkWeights; 2],
    nu_pairs: &[[u128; 2]],
) -> [[RssProofField; 3]; 2] {
    let mut mu_tab = [[RssProofField::ONE; RSS_DZK_GROUP_WORDS]; 2];
    for pass in 0..2 {
        for u in 1..RSS_DZK_GROUP_WORDS {
            mu_tab[pass][u] =
                mu_tab[pass][u & (u - 1)].mul(weights[pass].mu[u.trailing_zeros() as usize]);
        }
    }
    // Slot `s`'s share of both claims: per word offset, the weighted sum over the groups
    // (a 64-bit word times a 128-bit weight, reduced once), then the offset's `mu` weight.
    let slot_claims = |s: usize| -> [RssProofField; 2] {
        let mut sums = [[[0u128; 2]; RSS_DZK_GROUP_WORDS]; 2];
        debug_assert_eq!(pending.c[s].len(), groups * RSS_DZK_GROUP_WORDS);
        let (group_words, _) = pending.c[s].as_chunks::<RSS_DZK_GROUP_WORDS>();
        for (words, nu) in group_words.iter().zip(nu_pairs) {
            for (sums, weight) in sums.iter_mut().zip(nu) {
                qsag_asm::gf2_64x128_clmul_acc(sums, words, *weight);
            }
        }
        let mut part = [RssProofField::ZERO; 2];
        for ((part, sums), mu) in part.iter_mut().zip(&sums).zip(&mu_tab) {
            for (sum, mu) in sums.iter().zip(mu) {
                *part = part.add(mu.mul(RssProofField(rss_reduce_wide(*sum))));
            }
        }
        qsag_asm::volatile_fill(sums.as_flattened_mut(), [0; 2]);
        part
    };
    let mut claims = [[RssProofField::ZERO; 3]; 2];
    let mut add_part = |s: usize, mut part: [RssProofField; 2]| {
        for (claim, share) in claims.iter_mut().zip(part) {
            claim[s] = claim[s].add(share);
        }
        wipe_rss_proof_field(&mut part);
    };
    #[cfg(feature = "std")]
    if groups >= 128 {
        let slot_claims = &slot_claims;
        std::thread::scope(|scope| {
            let handles: Vec<_> = (0..3)
                .map(|s| scope.spawn(move || slot_claims(s)))
                .collect();
            for (s, handle) in handles.into_iter().enumerate() {
                add_part(s, handle.join().expect("RSS claim worker failed"));
            }
        });
        return claims;
    }
    for s in 0..3 {
        add_part(s, slot_claims(s));
    }
    claims
}

/// One complete proof pass. See [`verify_rss_boolean_triples_bbcggi19`].
#[expect(
    clippy::too_many_arguments,
    reason = "One proof pass: relations, weights, claims, randomness and challenge context"
)]
fn rss_dzk_pass(
    ctx: &RssDzkCtx<'_>,
    pass: usize,
    pending: &RssPendingDzkTriples,
    weights: &RssDzkWeights,
    tabs: &[Vec<[u128; 2]>; 3],
    mut claim: [RssProofField; 3],
    tables: &mut RssDzkTables,
    streams: &mut RssProofStreams,
    party_rngs: &mut [PartyPrivateRng; 3],
) -> Result<(), KeccakMpcError> {
    let groups = ctx.groups;
    let tab: [Vec<RssProofField>; 3] =
        core::array::from_fn(|p| tabs[p].iter().map(|v| RssProofField(v[pass])).collect());
    let mut tab = SecretBuffer(tab);
    let mut gammas = [RssProofField::ZERO; RSS_DZK_TENSOR_BITS];
    let mut bound_weight = RssProofField::ONE;
    let mut scratch = SecretBuffer(vec![RssProofField::ZERO; RSS_DZK_TERNARY]);

    // Packed sumcheck over the six low word-index bits. Round `i` treats bit `i` as the
    // variable `X`; its weight is `w_i(X) = 1 + X * (1 + mu_i)` and the round polynomial is
    // `w_i(X) * s(X)` with `s(X) = (1 + X) s(0) + X s(1) + (X + X^2) s_2`.
    for (i, gamma_slot) in gammas.iter_mut().enumerate() {
        let mut s1 = SecretBuffer(streams.zero_share());
        let mut s2 = SecretBuffer(streams.zero_share());
        let len = tab[0].len();
        for p in 0..3 {
            scratch[..len].copy_from_slice(&tab[p]);
            let mut len3 = len / 3;
            for l in (i + 1..RSS_DZK_TENSOR_BITS).rev() {
                for idx in 0..len3 {
                    scratch[idx] = scratch[idx].add(weights.mu[l].mul(scratch[idx + len3]));
                }
                len3 /= 3;
            }
            s1[p] = s1[p].add(scratch[1]);
            s2[p] = s2[p].add(scratch[2]);
        }
        let gamma = ctx.coin(b"RSS_DZK_POLY_SUMCHECK_COIN/v3", pass, i, party_rngs)?;
        let mu = weights.mu[i];
        let w = RssProofField::ONE.add(gamma.mul(RssProofField::ONE.add(mu)));
        let c0 = w.mul(RssProofField::ONE.add(gamma));
        let c1 = w.mul(gamma);
        let c2 = w.mul(gamma.add(gamma.mul(gamma)));
        for p in 0..3 {
            let s0 = claim[p].add(mu.mul(s1[p]));
            claim[p] = c0.mul(s0).add(c1.mul(s1[p])).add(c2.mul(s2[p]));
            let next = len / 3;
            for idx in 0..next {
                tab[p][idx] = c0
                    .mul(tab[p][3 * idx])
                    .add(c1.mul(tab[p][3 * idx + 1]))
                    .add(c2.mul(tab[p][3 * idx + 2]));
            }
            wipe_rss_proof_field(&mut tab[p][next..]);
            tab[p].truncate(next);
        }
        *gamma_slot = gamma;
        bound_weight = bound_weight.mul(w);
    }
    wipe_rss_proof_field(&mut scratch);
    for t in tab.iter_mut() {
        wipe_rss_proof_field(t);
    }

    // Bind the six bits in the relation vectors themselves: element `(g, lane)` of the bound
    // `a` is `sum_u beta(u) * a[64 g + u][lane]` with `beta(u) = prod_i (u_i ? gamma_i : 1 + gamma_i)`.
    let mut beta = [RssProofField::ONE; RSS_DZK_GROUP_WORDS];
    for (i, gamma) in gammas.iter().copied().enumerate() {
        let bit = 1usize << i;
        let one_plus = RssProofField::ONE.add(gamma);
        for u in 0..bit {
            beta[u | bit] = beta[u].mul(gamma);
            beta[u] = beta[u].mul(one_plus);
        }
    }
    let mut pattern = [[0u8; RSS_DZK_NIBBLES]; 128];
    for (bit, nibbles) in pattern.iter_mut().enumerate() {
        for g in 0..RSS_DZK_NIBBLES {
            for d in 0..4 {
                nibbles[g] |= (((beta[4 * g + d].0 >> bit) & 1) as u8) << d;
            }
        }
    }
    let block_weights: Vec<RssProofField> =
        weights.nu.iter().map(|v| bound_weight.mul(*v)).collect();
    tables.begin_pass(groups * RSS_DZK_LANES);
    // Groups are independent linear maps under public coefficients. Partition only
    // this arithmetic and absorb `block_weights[g]` directly into `x`; challenges,
    // proof messages and verification stay in exact sequential order.
    let bind = |s: usize, start: usize, x: &mut [u128], y: &mut [u128]| {
        // Two groups per kernel call: columns `(a, b)` of the first, `(a, b)` of the second.
        let mut rows = [[0u64; 4]; RSS_DZK_GROUP_WORDS];
        let mut planes = [[[0u64; 4]; 64]; 2];
        let mut bound = [[0u128; 4]; RSS_DZK_LANES];
        let mut weighted = [0u128; RSS_DZK_LANES];
        for (pair, (x, y)) in x
            .chunks_mut(2 * RSS_DZK_LANES)
            .zip(y.chunks_mut(2 * RSS_DZK_LANES))
            .enumerate()
        {
            let first = start + 2 * pair;
            let in_pair = x.len() / RSS_DZK_LANES;
            for k in 0..2 {
                if k < in_pair {
                    let offset = (first + k) * RSS_DZK_GROUP_WORDS;
                    let a = &pending.a[s][offset..offset + RSS_DZK_GROUP_WORDS];
                    let b = &pending.b[s][offset..offset + RSS_DZK_GROUP_WORDS];
                    for (row, (a, b)) in rows.iter_mut().zip(a.iter().zip(b)) {
                        row[2 * k] = *a;
                        row[2 * k + 1] = *b;
                    }
                } else {
                    for row in &mut rows {
                        row[2 * k] = 0;
                        row[2 * k + 1] = 0;
                    }
                }
            }
            rss_bind_columns(&rows, &pattern, &mut planes, &mut bound);
            for (k, (x, y)) in x
                .chunks_mut(RSS_DZK_LANES)
                .zip(y.chunks_mut(RSS_DZK_LANES))
                .enumerate()
            {
                for (lane, ((w, y), bound)) in weighted
                    .iter_mut()
                    .zip(y.iter_mut())
                    .zip(&bound)
                    .enumerate()
                {
                    *w = RssProofField(bound[2 * k]).mul_t_pow(lane as u32).0;
                    *y = bound[2 * k + 1];
                }
                // `x` is zero at the start of a pass. Fuse the fixed public
                // group weight over all lanes in one hardware dispatch.
                qsag_asm::bitslice::gf2_128_scale_xor(x, &weighted, block_weights[first + k].0);
            }
        }
        qsag_asm::volatile_fill(&mut rows, [0; 4]);
        qsag_asm::volatile_fill(planes.as_flattened_mut(), [0; 4]);
        qsag_asm::volatile_fill(&mut bound, [0; 4]);
        wipe_u128s(&mut weighted);
    };
    #[cfg(feature = "std")]
    {
        // One scope for all three slots, the worker budget shared between them.
        let workers = rss_dzk_workers()
            .div_ceil(3)
            .min(groups.div_ceil(64))
            .max(1);
        let chunk_groups = groups.div_ceil(workers);
        let bind = &bind;
        std::thread::scope(|scope| {
            for (s, (x, y)) in tables.x.iter_mut().zip(&mut tables.y).enumerate() {
                for (chunk, (x, y)) in x
                    .chunks_mut(chunk_groups * RSS_DZK_LANES)
                    .zip(y.chunks_mut(chunk_groups * RSS_DZK_LANES))
                    .enumerate()
                {
                    scope.spawn(move || bind(s, chunk * chunk_groups, x, y));
                }
            }
        });
    }
    #[cfg(not(feature = "std"))]
    for (s, (x, y)) in tables.x.iter_mut().zip(&mut tables.y).enumerate() {
        bind(s, 0, x, y);
    }

    // Halve the group index, then halve the 64 lanes (`block_weights` already absorbed in `x`).
    let mut step = 0usize;
    let mut size = groups.next_power_of_two();
    let mut cur = groups;
    while size > 1 {
        let half = size / 2;
        let hi_groups = cur.saturating_sub(half);
        rss_dzk_fold_round(
            ctx,
            pass,
            step,
            tables,
            RSS_DZK_LANES,
            hi_groups,
            half,
            &mut claim,
            streams,
            party_rngs,
        )?;
        cur = cur.min(half);
        size = half;
        step += 1;
    }
    let mut half = RSS_DZK_LANES / 2;
    while half >= 1 {
        rss_dzk_fold_round(
            ctx, pass, step, tables, 1, half, half, &mut claim, streams, party_rngs,
        )?;
        half /= 2;
        step += 1;
    }

    // Masked product check of the single remaining relation `x * y == claim`.
    let x: [RssProofField; 3] = core::array::from_fn(|s| RssProofField(tables.x[s][0]));
    let y: [RssProofField; 3] = core::array::from_fn(|s| RssProofField(tables.y[s][0]));
    let (rx_p, rx_s) = streams.draw();
    let (ry_p, ry_s) = streams.draw();
    let mut c0 = SecretBuffer(streams.zero_share());
    let mut c1 = SecretBuffer(streams.zero_share());
    for p in 0..3 {
        let q = (p + 1) % 3;
        c0[p] = c0[p]
            .add(rx_p[p].mul(ry_p[p].add(ry_s[p])))
            .add(rx_s[p].mul(ry_p[p]));
        c1[p] = c1[p]
            .add(rx_p[p].mul(y[p].add(y[q])))
            .add(rx_s[p].mul(y[p]))
            .add(ry_p[p].mul(x[p].add(x[q])))
            .add(ry_s[p].mul(x[p]));
    }
    let tau = ctx.coin(b"RSS_DZK_POLY_BASE_TAU/v3", pass, 0, party_rngs)?;
    let tau_sq = tau.mul(tau);
    let limbs = |v: RssProofField| [v.0 as u64, (v.0 >> 64) as u64];
    let mut open_prim: [Vec<u64>; 3] = [Vec::new(), Vec::new(), Vec::new()];
    let mut open_sec: [Vec<u64>; 3] = [Vec::new(), Vec::new(), Vec::new()];
    for p in 0..3 {
        let q = (p + 1) % 3;
        let pe = |s: usize| c0[s].add(tau.mul(c1[s])).add(tau_sq.mul(claim[s]));
        for v in [
            rx_p[p].add(tau.mul(x[p])),
            ry_p[p].add(tau.mul(y[p])),
            pe(p),
        ] {
            open_prim[p].extend_from_slice(&limbs(v));
        }
        for v in [
            rx_s[p].add(tau.mul(x[q])),
            ry_s[p].add(tau.mul(y[q])),
            pe(q),
        ] {
            open_sec[p].extend_from_slice(&limbs(v));
        }
    }
    let opened = rss_commit_and_open_u64_batch(
        ctx.session_id,
        "rss_dzk_base_eval",
        &open_prim,
        &open_sec,
        party_rngs,
        ctx.poison,
    )?;
    let elem = |i: usize| RssProofField(u128::from(opened[i]) | (u128::from(opened[i + 1]) << 64));
    if !elem(0).mul(elem(2)).ct_eq(elem(4)) {
        return ctx.poison.fail(KeccakMpcError::RssSacrificeFailed);
    }
    Ok(())
}

/// Batch verification of all recorded 2-of-3 RSS Boolean AND relations, in the style of the
/// Boneh–Boyle–Corrigan-Gibbs–Gilboa–Ishai (`CRYPTO 2019`) distributed zero-knowledge proofs:
/// a sumcheck/inner-product compression over $\mathbb{F} = \mathbb{F}_2[t]/(t^{128}+t^7+t^2+t+1)$
/// run jointly on the replicated shares, with every prover message additively masked by a
/// pairwise zero sharing and nothing opened except the final masked product check.
///
/// **Statement.** Relation word `k` carries 64 relations `a_k[i] & b_k[i] == c_k[i]`. With
/// `G` groups of 64 words, `kappa = ceil(log2 G)` and public weights
/// `weight(64 g + u) = prod_{l in bits(g)} nu_l * prod_{l in bits(u)} mu_l`, the proof shows
/// `sum_k weight(k) * sum_i t^i a_k[i] b_k[i] == sum_k weight(k) * c_k(t)`, where `c_k(t)`
/// reads the 64-bit word as a polynomial of degree below 64. The `6 + kappa` weight elements
/// are drawn by a joint commit-then-open coin after all relation shares are fixed.
///
/// **Packing.** A word is never split into 64 field elements on the weighted side: `c_k(t)`
/// and every per-group product word enter through one carryless multiplication by a 128-bit
/// weight. The six low word-index bits are bound by a sumcheck whose round messages are public
/// linear combinations of `3^6` challenge-independent sums of word ANDs
/// ([`rss_dzk_tensor_tables`]). Only then are the relation vectors bound, by GF(2) linear
/// combinations of whole words selected by public coefficient bits, leaving `64 G` field
/// elements per vector for the halving rounds ([`rss_dzk_fold_round`]). No per-relation
/// coefficient is ever stored.
///
/// **Soundness of one pass**, for an adversary controlling one party (so its deviations are
/// additive errors on the masked messages, chosen before the next challenge):
/// 1. Weights. If some relation fails, the error words `e_k(t) = a_k b_k + c_k` are not all
///    zero and `e_k(t) != 0` in the field because its degree is below 64. The weighted error is
///    a nonzero multilinear polynomial in the `6 + kappa` weight elements, so it vanishes with
///    probability at most `(6 + kappa) / 2^128` (Schwartz–Zippel).
/// 2. Packed rounds (6). A false claim stays false unless the challenge is a root of
///    `w_i(X) * D(X)` with `deg D <= 2` and `D != 0`: at most `3 / 2^128` each.
/// 3. Halving rounds (`kappa` over groups, 6 over lanes). The claim error becomes
///    `Delta + gamma^-1 e_L + gamma e_R`; times `gamma` this is a nonzero polynomial of degree
///    at most 2 over the `2^128 - 1` nonzero challenges: at most `2 / (2^128 - 1)` each.
/// 4. Final product check. `x_e * y_e - p_e` is a polynomial of degree 2 in `tau` whose leading
///    coefficient is the remaining claim error: at most `2 / 2^128`.
///
/// One pass therefore accepts a false batch with probability at most
/// `(3 kappa + 38) / (2^128 - 1)`; `kappa <= 58` for any batch that fits in memory, so this is
/// below `2^-120`. Two passes with independent weights and challenges are run and both must
/// accept: the error is below `2^-240`, and in particular below `2^-126`. A Keccak batch has
/// `G = 600`, `kappa = 10`: at most `(68 / (2^128 - 1))^2 < 2^-243`.
///
/// **Privacy.** Round messages are masked by fresh pairwise zero sharings and the only opened
/// values are `r_x + tau x`, `r_y + tau y` and the matching masked product, with `r_x`, `r_y`
/// uniform. An abort reveals nothing beyond the fact that the check failed.
pub(super) fn verify_rss_boolean_triples_bbcggi19(
    session_id: &[u8; 32],
    batch_ctr: u64,
    pending: &mut RssPendingDzkTriples,
    mask: &RssMaskSession,
    party_rngs: &mut [PartyPrivateRng; 3],
) -> Result<(), KeccakMpcError> {
    verify_rss_boolean_triples_seeded(session_id, batch_ctr, pending, mask, party_rngs, None)
}

/// [`verify_rss_boolean_triples_bbcggi19`] with the relation weights of both passes expanded
/// from `weight_seed` instead of from a coin drawn here. The caller must have produced the
/// seed by a commit-then-open coin flip that was bound to every transmitted gate message and
/// opened only after all of them were fixed; the weights are then exactly as unpredictable
/// as the internally drawn ones. Every later round challenge is still a fresh joint coin.
///
/// A failure is permanent for `pending`: its latch is set where the failure is detected,
/// before the relation shares are wiped, and every later call on the same accumulator
/// returns [`KeccakMpcError::Poisoned`], including when it holds no relations. The owner of
/// the accumulator must treat that as the end of the session (see
/// [`RssPendingDzkTriples::is_poisoned`]).
pub(crate) fn verify_rss_boolean_triples_seeded(
    session_id: &[u8; 32],
    batch_ctr: u64,
    pending: &mut RssPendingDzkTriples,
    mask: &RssMaskSession,
    party_rngs: &mut [PartyPrivateRng; 3],
    weight_seed: Option<&[u8; 32]>,
) -> Result<(), KeccakMpcError> {
    if pending.poison.is_set() {
        pending.clear_and_wipe();
        return Err(KeccakMpcError::Poisoned);
    }
    if pending.len_words() == 0 {
        return Ok(());
    }
    pending.pad_to_group();
    let mut tables = core::mem::take(&mut pending.fold_tables);
    let result = rss_dzk_verify_padded(
        session_id,
        batch_ctr,
        pending,
        &mut tables,
        mask,
        party_rngs,
        weight_seed,
    );
    pending.fold_tables = tables;
    if result.is_err() {
        // Every failure site has already latched; this covers any error added later.
        pending.poison.set();
    }
    pending.clear_and_wipe();
    result
}

fn rss_dzk_verify_padded(
    session_id: &[u8; 32],
    batch_ctr: u64,
    pending: &RssPendingDzkTriples,
    tables: &mut RssDzkTables,
    mask: &RssMaskSession,
    party_rngs: &mut [PartyPrivateRng; 3],
    weight_seed: Option<&[u8; 32]>,
) -> Result<(), KeccakMpcError> {
    let groups = pending.len_words() / RSS_DZK_GROUP_WORDS;
    let ctx = RssDzkCtx {
        session_id,
        batch_ctr,
        groups,
        poison: &pending.poison,
    };
    let kappa = groups.next_power_of_two().trailing_zeros() as usize;

    // Joint weight coin, drawn only now that every relation share is fixed.
    let mut bind = [0u8; 32];
    bind[8..16].copy_from_slice(&batch_ctr.to_le_bytes());
    bind[16..24].copy_from_slice(&(groups as u64).to_le_bytes());
    let coin = match weight_seed {
        Some(seed) => *seed,
        None => match run_commit_and_open_coin(
            session_id,
            b"RSS_DZK_POLY_WEIGHT_COIN/v3",
            &bind,
            party_rngs,
        ) {
            Ok(coin) => coin,
            Err(e) => return pending.poison.fail(e.into()),
        },
    };
    let mut xof = Cshake256Xof::new(b"QSAG.RSS.DZK.WEIGHTS.POLY/v3");
    xof.absorb(&coin);
    xof.absorb(&bind);
    let mut next_elem = || {
        let mut bytes = [0u8; 16];
        xof.squeeze(&mut bytes);
        RssProofField(u128::from_le_bytes(bytes))
    };
    let weights: [RssDzkWeights; 2] = core::array::from_fn(|_| {
        let mu = core::array::from_fn(|_| next_elem());
        let nu_bits: Vec<RssProofField> = (0..kappa).map(|_| next_elem()).collect();
        let mut nu = vec![RssProofField::ONE; groups];
        for g in 1..groups {
            nu[g] = nu[g & (g - 1)].mul(nu_bits[g.trailing_zeros() as usize]);
        }
        RssDzkWeights { mu, nu }
    });
    let nu_pairs: Vec<[u128; 2]> = (0..groups)
        .map(|g| [weights[0].nu[g].0, weights[1].nu[g].0])
        .collect();

    let mut claims = rss_dzk_initial_claims(pending, groups, &weights, &nu_pairs);
    let mut tabs = rss_dzk_tensor_tables(pending, groups, &nu_pairs);
    let mut streams = RssProofStreams::new(mask, session_id, batch_ctr);
    let mut result = Ok(());
    for pass in 0..2 {
        result = rss_dzk_pass(
            &ctx,
            pass,
            pending,
            &weights[pass],
            &tabs,
            claims[pass],
            tables,
            &mut streams,
            party_rngs,
        );
        // Success leaves one element per table; an abort leaves whatever the pass reached.
        tables.wipe_live();
        if result.is_err() {
            break;
        }
    }
    for tab in &mut tabs {
        qsag_asm::volatile_fill(tab, [0; 2]);
    }
    for claim in &mut claims {
        wipe_rss_proof_field(claim);
    }
    result
}
