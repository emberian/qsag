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
