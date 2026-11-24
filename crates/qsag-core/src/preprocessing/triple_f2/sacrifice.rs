//! Correlation-robust row hashing, raw triple generation and recursive sacrifice.

use super::*;

// ---------------------------------------------------------------------------
// Correlation-robust hashing of pool rows (eight rows per permutation call).
// ---------------------------------------------------------------------------

/// Rows hashed per `Keccak-f[1600]` call.
pub(super) const CRH_WIDTH: usize = 8;
pub(super) type CrhOut = [[u64; RATE_WORDS * MAX_CRH_BLOCKS]; CRH_WIDTH];

pub(super) fn crh_prefix(
    session_id: &[u8; 32],
    holder: usize,
    owner: usize,
    domain: u64,
) -> [u64; 8] {
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
pub(super) fn crh_x8(
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
pub(super) struct FoldPlan {
    nbits: usize,
    /// Vector length entering each round.
    lens: Vec<usize>,
    /// Rounds whose cross terms ride on the hashed rows of the raw `b` bits.
    structured: usize,
    crh_blocks: usize,
}

impl FoldPlan {
    pub(super) fn new(nbits: usize) -> Result<Self, PreprocessError> {
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

    pub(super) fn rounds(&self) -> usize {
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

    pub(super) fn pair_rows(&self) -> usize {
        self.nbits + 128 * self.choice_blocks()
    }

    pub(super) fn pool_rows(&self) -> usize {
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
fn pair_pads(n: usize, nbits: usize, plan: &FoldPlan) -> Vec<PairPads> {
    let unit = (1usize << plan.structured).max(64);
    let ranges_per_pair = PublicDivisor::new(n * (n - 1))
        .split(worker_count() + n * (n - 1) / 2)
        .0
        .max(1);
    let range_len = (PublicDivisor::new(ranges_per_pair).ceil(nbits) + unit - 1) & !(unit - 1);
    let mut pads = Vec::new();
    for holder in 0..n {
        for owner in 0..n {
            if holder == owner {
                continue;
            }
            let mut start = 0;
            while start < nbits {
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
                start += len;
            }
        }
    }
    pads
}

/// One KOS-backed raw ceremony over a bootstrapped pool: `plan.nbits` authenticated raw bit
/// triples and the pending private sacrifice opening, checked by the coordinator.
pub(super) fn raw_ceremony(
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
pub(super) fn raw_silent_ceremony(
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
