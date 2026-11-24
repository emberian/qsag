//! Committed CRS, base-OT rounds, parity combining and canonical wire messages.

use super::rlwe_poly::{crs_mixed_session_id, rlwe_fo_encrypt_branch, rlwe_ot_decrypt_ct_mask};
use super::rlwe_proof::{bounded_ternary_witness, encode_rlwe_poly_le};
use super::*;

/// Expand the 2-universal systematic Leftover-Hash matrix $E = [I_{256} \mid R_{256 \times 256}] \in \mathbb{F}_2^{256 \times 512}$
/// from the post-Base-OT public combiner coin. Every row `i` is `[u64; 8]` (`512` bits).
fn derive_extractor_matrix_256x512(
    session_id: &[u8; 32],
    ext_sender_id: usize,
    ext_receiver_id: usize,
    combiner_coin: &[u8; 32],
) -> Box<[[u64; RLWE_BASE_OT_WORDS]; OT_EXT_SUBSPACE_BITS]> {
    let mut xof = Cshake256Xof::new(b"QSAG.OT.COMBINER.EXT/v1");
    xof.absorb(session_id);
    xof.absorb(&(ext_sender_id as u64).to_be_bytes());
    xof.absorb(&(ext_receiver_id as u64).to_be_bytes());
    xof.absorb(combiner_coin);
    let mut raw = vec![0u8; OT_EXT_SUBSPACE_BITS * 32];
    xof.squeeze(&mut raw);

    let mut mat = Box::new([[0u64; RLWE_BASE_OT_WORDS]; OT_EXT_SUBSPACE_BITS]);
    for row in 0..OT_EXT_SUBSPACE_BITS {
        mat[row][row / 64] = 1u64 << (row % 64);
        let base = 32 * row;
        for w in 0..4 {
            let o = base + 8 * w;
            mat[row][4 + w] = u64::from_le_bytes([
                raw[o],
                raw[o + 1],
                raw[o + 2],
                raw[o + 3],
                raw[o + 4],
                raw[o + 5],
                raw[o + 6],
                raw[o + 7],
            ]);
        }
    }
    mat
}

/// Depth-2 GGM $\mathbb{F}_4$ (`k = 2`) 3-out-of-4 puncture setup for Receiver on slice `slice_idx`:
/// Given level-1 base-OT seed pair `(r_seed, l_seed)` (Sender holds `r_seed` when `b0 == 0`, `l_seed`
/// when `b0 == 1`) and level-2 base-OT seed pair `(k1_0, k1_1)` (Sender holds `k1_{b1}`), expands
/// the 4 leaf seeds `[s0, s1, s2, s3]` and encrypts the level-2 XOR sibling pair `(ct0, ct1)` so
/// Receiver output of one depth-2 `F_4` GGM slice setup: `(four_leaves, sibling_ciphertexts)`.
pub type F4SliceReceiverSetup = ([[u8; 32]; 4], ([u8; 32], [u8; 32]));

/// Sender recovers `[s_v : v != 2*b0 + b1]` and learns zero information about `s_{2*b0 + b1}`.
#[inline]
pub fn softspoken_f4_slice_setup_receiver(
    session_id: &[u8; 32],
    slice_idx: usize,
    r_seed: &[u8; 32],
    l_seed: &[u8; 32],
    k1_0: &[u8; 32],
    k1_1: &[u8; 32],
) -> F4SliceReceiverSetup {
    let g_row = OT_EXT_SUBSPACE_BITS + slice_idx;
    let p_row = OT_EXT_SUBSPACE_BITS + OT_EXT_F4_SLICES + slice_idx;
    let s0 = combiner_step_hash32(session_id, g_row, 0, 0, 0, &[0u8; 32], l_seed);
    let s1 = combiner_step_hash32(session_id, g_row, 0, 0, 1, &[0u8; 32], l_seed);
    let s2 = combiner_step_hash32(session_id, g_row, 0, 1, 0, &[0u8; 32], r_seed);
    let s3 = combiner_step_hash32(session_id, g_row, 0, 1, 1, &[0u8; 32], r_seed);
    let mut pad0 = combiner_step_hash32(session_id, p_row, 0, 0, 0, &[0u8; 32], k1_0);
    let mut pad1 = combiner_step_hash32(session_id, p_row, 0, 0, 1, &[0u8; 32], k1_1);
    let mut ct0 = [0u8; 32];
    let mut ct1 = [0u8; 32];
    for b in 0..32 {
        ct0[b] = s1[b] ^ s3[b] ^ pad0[b];
        ct1[b] = s0[b] ^ s2[b] ^ pad1[b];
    }
    wipe_bytes32(&mut pad0);
    wipe_bytes32(&mut pad1);
    ([s0, s1, s2, s3], (ct0, ct1))
}

/// Branch-free constant-time Sender recovery of the 3 non-punctured depth-2 GGM leaves for slice
/// `slice_idx`, with punctured slot `v* = 2 * b0 + b1` zeroed.
#[inline]
pub fn softspoken_f4_slice_setup_sender_ct(
    session_id: &[u8; 32],
    slice_idx: usize,
    b0: u8,
    b1: u8,
    sub_known: &[u8; 32],
    k1_known: &[u8; 32],
    ggm_sib2: &([u8; 32], [u8; 32]),
) -> [[u8; 32]; 4] {
    let b0 = black_box(b0) & 1;
    let b1 = black_box(b1) & 1;
    let branch_hi = 1u8 ^ b0;
    let g_row = OT_EXT_SUBSPACE_BITS + slice_idx;
    let p_row = OT_EXT_SUBSPACE_BITS + OT_EXT_F4_SLICES + slice_idx;
    let mut c_even =
        combiner_step_hash32(session_id, g_row, 0, branch_hi, 0, &[0u8; 32], sub_known);
    let mut c_odd = combiner_step_hash32(session_id, g_row, 0, branch_hi, 1, &[0u8; 32], sub_known);
    let mut pad_b1 = combiner_step_hash32(session_id, p_row, 0, 0, b1, &[0u8; 32], k1_known);
    let b1_mask = 0u8.wrapping_sub(b1);
    let mut c_third = [0u8; 32];
    for b in 0..32 {
        let ct_sel = ggm_sib2.0[b] ^ (b1_mask & (ggm_sib2.0[b] ^ ggm_sib2.1[b]));
        let known_sib = c_odd[b] ^ (b1_mask & (c_odd[b] ^ c_even[b]));
        c_third[b] = ct_sel ^ pad_b1[b] ^ known_sib;
    }
    let mut out = [[0u8; 32]; 4];
    for (v, dst) in out.iter_mut().enumerate() {
        let v_hi = ((v >> 1) & 1) as u8;
        let v_lo = (v & 1) as u8;
        let m_other_half = 0u8.wrapping_sub(black_box(v_hi ^ b0));
        let m_third = (!m_other_half) & 0u8.wrapping_sub(black_box(v_lo ^ b1));
        let half_src = if v_lo == 0 { &c_even } else { &c_odd };
        for b in 0..32 {
            dst[b] = (m_other_half & half_src[b]) | (m_third & c_third[b]);
        }
    }
    wipe_bytes32(&mut c_even);
    wipe_bytes32(&mut c_odd);
    wipe_bytes32(&mut pad_b1);
    wipe_bytes32(&mut c_third);
    out
}

/// Zero out the punctured leaf `v* = 2 * b0 + b1` of a 4-leaf slice in strict constant time.
#[inline]
pub fn softspoken_f4_zero_punctured_slot_ct(leaves: &mut [[u8; 32]; 4], b0: u8, b1: u8) {
    let v_star = ((black_box(b0) & 1) << 1) | (black_box(b1) & 1);
    for (v, leaf) in leaves.iter_mut().enumerate() {
        let diff = black_box((v as u8) ^ v_star);
        let is_neq = ((diff | diff.wrapping_neg()) >> 7) & 1;
        let keep = 0u8.wrapping_sub(is_neq);
        for b in leaf.iter_mut() {
            *b &= keep;
        }
    }
}

/// Bulk two-lane BDOZ inner product in the protocol's tower basis.
/// Converts both inputs through the exact field isomorphism before dispatch;
/// backend failures propagate without accepting a partial check.
pub fn batch_bdoz_gf2128_dot(
    backend: &dyn qsag_accel::AcceleratorBackend,
    shares: &[[u128; 2]],
    weights: &[[u128; 2]],
) -> Result<[u128; 2], qsag_accel::AccelError> {
    if shares.len() != weights.len() {
        return Err(qsag_accel::AccelError::LengthMismatch {
            what: "BDOZ weights",
            expected: shares.len(),
            actual: weights.len(),
        });
    }
    let convert = |input: &[[u128; 2]]| {
        let mut converted = SecretBuffer(Vec::with_capacity(input.len()));
        for chunk in input.chunks(32) {
            let mut flat = SecretBuffer([0u128; 64]);
            flat[..chunk.len() * 2].copy_from_slice(chunk.as_flattened());
            qsag_asm::tower128_to_poly128_x64_ct(&mut flat);
            converted.extend((0..chunk.len()).map(|i| (flat[2 * i], flat[2 * i + 1])));
        }
        converted
    };
    let shares = convert(shares);
    let weights = convert(weights);
    let result = SecretBuffer(backend.bdoz_gf2_128_batch_dot(&shares, &weights)?);
    Ok([
        qsag_asm::poly128_to_tower128_ct(result.0.0),
        qsag_asm::poly128_to_tower128_ct(result.0.1),
    ])
}

/// Visit disjoint slots in deterministic index order within each worker.
fn parallel_slots<T: Send, F: Fn(usize, &mut T) + Sync>(slots: &mut [T], f: F) {
    #[cfg(feature = "std")]
    {
        if slots.len() <= 1 {
            for (index, value) in slots.iter_mut().enumerate() {
                f(index, value);
            }
            return;
        }
        let budget = BaseProofWorkers::acquire(slots.len().min(16));
        if budget.count <= 1 {
            for (index, value) in slots.iter_mut().enumerate() {
                f(index, value);
            }
            return;
        }
        let chunk_len = PublicDivisor::new(budget.count).ceil(slots.len()).max(1);
        std::thread::scope(|scope| {
            for (chunk, values) in slots.chunks_mut(chunk_len).enumerate() {
                let f = &f;
                scope.spawn(move || {
                    for (offset, value) in values.iter_mut().enumerate() {
                        f(chunk * chunk_len + offset, value);
                    }
                });
            }
        });
    }
    #[cfg(not(feature = "std"))]
    for (index, value) in slots.iter_mut().enumerate() {
        f(index, value);
    }
}

/// Fast single-block `keccak_f1600` PRF (`0` heap allocations!) for the 4-ciphertext parity combiner.
#[inline]
pub(super) fn combiner_step_hash32(
    session_id: &[u8; 32],
    row_idx: usize,
    step_idx: usize,
    beta: u8,
    gamma: u8,
    label_a: &[u8; 32],
    seed_b: &[u8; 32],
) -> [u8; 32] {
    let mut st = combiner_step_state(session_id, row_idx, step_idx, beta, gamma, label_a, seed_b);
    keccak_f1600(&mut st);
    let mut out = [0u8; 32];
    for i in 0..4 {
        out[8 * i..8 * i + 8].copy_from_slice(&st[i].to_le_bytes());
    }
    wipe_u64s(&mut st);
    out
}

fn combiner_step_state(
    session_id: &[u8; 32],
    row_idx: usize,
    step_idx: usize,
    beta: u8,
    gamma: u8,
    label_a: &[u8; 32],
    seed_b: &[u8; 32],
) -> [u64; 25] {
    let mut st = [0u64; 25];
    st[0] = u64::from_le_bytes(*b"QSAG.OT.");
    st[1] = u64::from_le_bytes(*b"PARCOMB1");
    for i in 0..4 {
        let o = 8 * i;
        st[2 + i] = u64::from_le_bytes(core::array::from_fn(|array_index| {
            (session_id[o..o + 8])[array_index]
        }));
        st[6 + i] = u64::from_le_bytes(core::array::from_fn(|array_index| {
            (label_a[o..o + 8])[array_index]
        }));
        st[10 + i] = u64::from_le_bytes(core::array::from_fn(|array_index| {
            (seed_b[o..o + 8])[array_index]
        }));
    }
    st[14] =
        ((row_idx as u64) << 32) | ((step_idx as u64) << 8) | ((beta as u64) << 1) | (gamma as u64);
    st[15] = 0x1f;
    st[16] = 0x8000_0000_0000_0000;
    st
}

pub(super) fn combiner_step_hash32_x4(
    session_id: &[u8; 32],
    row: usize,
    step: usize,
    labels: &([u8; 32], [u8; 32]),
    seeds: &([u8; 32], [u8; 32]),
) -> [[u8; 32]; 4] {
    let mut states = SecretBuffer(core::array::from_fn::<_, 4, _>(|slot| {
        combiner_step_state(
            session_id,
            row,
            step,
            (slot / 2) as u8,
            (slot % 2) as u8,
            if slot / 2 == 0 { &labels.0 } else { &labels.1 },
            if slot % 2 == 0 { &seeds.0 } else { &seeds.1 },
        )
    }));
    qsag_asm::keccak_f1600_batch(&mut states[..]);
    core::array::from_fn(|slot| core::array::from_fn(|b| states[slot][b / 8].to_le_bytes()[b % 8]))
}

#[inline]
fn ct_select_bytes32_4(table: &[[u8; 32]; 4], secret_idx: u8) -> [u8; 32] {
    let mut out = [0u8; 32];
    for k in 0..4u8 {
        let diff = black_box(secret_idx ^ k);
        let is_zero = 1u8.wrapping_sub(((diff | diff.wrapping_neg()) >> 7) & 1);
        let mask = 0u8.wrapping_sub(is_zero);
        for b in 0..32 {
            out[b] |= table[k as usize][b] & mask;
        }
    }
    out
}

/// Wire message 0a (`OT-Ext Receiver -> OT-Ext Sender`): commitment to CRS coin share before CRS exists.
#[derive(Clone, Copy, Debug)]
pub struct BaseOtCrsCommitMsg {
    pub receiver_crs_commit: [u8; 32],
}

/// Wire message 0b (`OT-Ext Sender -> OT-Ext Receiver`): Sender's CRS coin share.
#[derive(Clone, Copy, Debug)]
pub struct BaseOtCrsShareMsg {
    pub sender_crs_share: [u8; 32],
}

/// Wire message 0c (`OT-Ext Receiver -> OT-Ext Sender`): opening of Receiver's committed CRS coin share.
#[derive(Clone, Copy, Debug)]
pub struct BaseOtCrsOpenMsg {
    pub receiver_crs_share: [u8; 32],
}

/// Isolated CRS Round-0 state for `OT-Ext Receiver` (`!Clone`, wiped on `Drop`).
pub struct BaseOtCrsReceiverRound0 {
    my_crs_share: [u8; 32],
}

impl Drop for BaseOtCrsReceiverRound0 {
    fn drop(&mut self) {
        wipe_bytes32(&mut self.my_crs_share);
    }
}

impl BaseOtCrsReceiverRound0 {
    pub fn commit(
        session_id: [u8; 32],
        ext_sender_id: usize,
        ext_receiver_id: usize,
        receiver_rng: &mut PartyPrivateRng,
    ) -> (Self, BaseOtCrsCommitMsg) {
        let my_crs_share = receiver_rng.next_bytes32();
        let receiver_crs_commit = commit_crs_coin_share(
            &session_id,
            ext_sender_id,
            ext_receiver_id,
            ext_receiver_id,
            &my_crs_share,
        );
        (
            Self { my_crs_share },
            BaseOtCrsCommitMsg {
                receiver_crs_commit,
            },
        )
    }

    pub fn open_and_derive_crs_coin(
        self,
        sender_msg: &BaseOtCrsShareMsg,
    ) -> ([u8; 32], BaseOtCrsOpenMsg) {
        let mut crs_coin = [0u8; 32];
        for (b, crs_coin_b_item) in crs_coin[..32].iter_mut().enumerate() {
            *crs_coin_b_item = self.my_crs_share[b] ^ sender_msg.sender_crs_share[b];
        }
        (
            crs_coin,
            BaseOtCrsOpenMsg {
                receiver_crs_share: self.my_crs_share,
            },
        )
    }
}

/// Isolated CRS Round-0 state for `OT-Ext Sender` (`!Clone`, wiped on `Drop`).
pub struct BaseOtCrsSenderRound0 {
    session_id: [u8; 32],
    ext_sender_id: usize,
    ext_receiver_id: usize,
    peer_crs_commit: [u8; 32],
    my_crs_share: [u8; 32],
}

impl Drop for BaseOtCrsSenderRound0 {
    fn drop(&mut self) {
        wipe_bytes32(&mut self.my_crs_share);
    }
}

impl BaseOtCrsSenderRound0 {
    pub fn respond(
        session_id: [u8; 32],
        ext_sender_id: usize,
        ext_receiver_id: usize,
        commit_msg: &BaseOtCrsCommitMsg,
        sender_rng: &mut PartyPrivateRng,
    ) -> (Self, BaseOtCrsShareMsg) {
        let my_crs_share = sender_rng.next_bytes32();
        (
            Self {
                session_id,
                ext_sender_id,
                ext_receiver_id,
                peer_crs_commit: commit_msg.receiver_crs_commit,
                my_crs_share,
            },
            BaseOtCrsShareMsg {
                sender_crs_share: my_crs_share,
            },
        )
    }

    pub fn verify_and_derive_crs_coin(
        self,
        open_msg: &BaseOtCrsOpenMsg,
    ) -> Result<[u8; 32], PreprocessError> {
        let exp = commit_crs_coin_share(
            &self.session_id,
            self.ext_sender_id,
            self.ext_receiver_id,
            self.ext_receiver_id,
            &open_msg.receiver_crs_share,
        );
        if !ct_eq_bytes32(&exp, &self.peer_crs_commit) {
            return Err(PreprocessError::CoinCommitMismatch {
                party_id: self.ext_receiver_id,
            });
        }
        let mut crs_coin = [0u8; 32];
        for (b, crs_coin_b_item) in crs_coin[..32].iter_mut().enumerate() {
            *crs_coin_b_item = open_msg.receiver_crs_share[b] ^ self.my_crs_share[b];
        }
        Ok(crs_coin)
    }
}

/// Wire message 1 of per-party OT-extension channel setup (`OT-Ext Sender -> OT-Ext Receiver`,
/// containing `512` random-choice Ring-LWE Base-OT requests + OR-Sigma ZKPoKs).
/// Number of 128-slot Multi-CRS Ring-LWE Base-OT blocks (`4 * 128 = 512` OTs, `4` OR-Sigma proofs).
pub const RLWE_BASE_OT_BLOCKS: usize = 4;
/// Number of independent CRS Ring-LWE OT slots packed per short Ring-LWE secret (`128`).
pub const RLWE_BASE_OT_SLOTS_PER_BLOCK: usize = RLWE_BASE_OT_COUNT / RLWE_BASE_OT_BLOCKS;

#[derive(Clone, Debug)]
pub struct BaseOtRound1Msg {
    /// `512` Ring-LWE receiver public keys `pk0[m] = a_m * s_{m / 128} + e_m - b_m * t_m`.
    pub pk0s: Vec<RlwePoly>,
    /// `4` constant-time 13-rep OR-Sigma ZKPoKs on block anchors `(a_{128*blk}, t_{128*blk}, pk0[128*blk])`.
    pub block_poks: Vec<RlweReceiverZkPok>,
}

/// Wire message 2 of per-party OT-extension channel setup (`OT-Ext Receiver -> OT-Ext Sender`,
/// containing `512` FO-encrypted Ring-LWE Base-OT responses + combiner coin commitment).
#[derive(Clone, Debug)]
pub struct BaseOtRound2Msg {
    pub resps: Vec<RlweOtSenderMsg>,
    pub receiver_coin_commit: [u8; 32],
}

/// Wire message 3 (`OT-Ext Sender -> OT-Ext Receiver`: combiner coin share after FO check passes).
#[derive(Clone, Debug)]
pub struct BaseOtRound3Msg {
    pub sender_coin_share: [u8; 32],
}

/// Wire message 4 (`OT-Ext Receiver -> OT-Ext Sender`: opening of committed combiner coin share +
/// 4-ciphertext parity combiner tables folding `512` Base OTs into `256` active-secure Base OTs +
/// `128` depth-2 GGM $\mathbb{F}_4$ sibling ciphertexts).
#[derive(Clone, Debug)]
pub struct BaseOtRound4Msg {
    pub receiver_coin_share: [u8; 32],
    pub parity_tables: Vec<Vec<[[u8; 32]; 4]>>,
    pub ggm_sib2: Vec<([u8; 32], [u8; 32])>,
}

/// Isolated single-party Round-1 state for the OT-Ext Sender (Base-OT Receiver).
pub struct BaseOtExtSenderRound1 {
    session_id: [u8; 32],
    ext_sender_id: usize,
    ext_receiver_id: usize,
    c_tilde_words: [u64; RLWE_BASE_OT_WORDS],
    sec_states: Vec<RlweOtReceiverSecret>,
    cached_crs: Vec<(RlwePolyNtt, RlwePoly)>,
}

impl Drop for BaseOtExtSenderRound1 {
    fn drop(&mut self) {
        wipe_u64s(&mut self.c_tilde_words);
    }
}

/// Isolated single-party Round-2 state for the OT-Ext Receiver (Base-OT Sender).
pub struct BaseOtExtReceiverRound2 {
    session_id: [u8; 32],
    ext_sender_id: usize,
    ext_receiver_id: usize,
    base_seed_pairs: Vec<([u8; 32], [u8; 32])>,
    my_coin_share: [u8; 32],
    combiner_prf_seed: [u8; 32],
}

impl Drop for BaseOtExtReceiverRound2 {
    fn drop(&mut self) {
        for (s0, s1) in &mut self.base_seed_pairs {
            wipe_bytes32(s0);
            wipe_bytes32(s1);
        }
        wipe_bytes32(&mut self.my_coin_share);
        wipe_bytes32(&mut self.combiner_prf_seed);
    }
}

/// Isolated single-party Round-3 state for the OT-Ext Sender after all 384 FO checks pass.
pub struct BaseOtExtSenderRound3 {
    session_id: [u8; 32],
    ext_sender_id: usize,
    ext_receiver_id: usize,
    c_tilde_words: [u64; RLWE_BASE_OT_WORDS],
    base_seeds: Vec<[u8; 32]>,
    peer_coin_commit: [u8; 32],
    my_coin_share: [u8; 32],
}

impl Drop for BaseOtExtSenderRound3 {
    fn drop(&mut self) {
        wipe_u64s(&mut self.c_tilde_words);
        for s in &mut self.base_seeds {
            wipe_bytes32(s);
        }
        wipe_bytes32(&mut self.my_coin_share);
    }
}

fn commit_crs_coin_share(
    session_id: &[u8; 32],
    ext_sender_id: usize,
    ext_receiver_id: usize,
    party_id: usize,
    share: &[u8; 32],
) -> [u8; 32] {
    let s_be = (ext_sender_id as u64).to_be_bytes();
    let r_be = (ext_receiver_id as u64).to_be_bytes();
    let p_be = (party_id as u64).to_be_bytes();
    cshake256_32_multi_frame(
        b"QSAG.OT.CRS.COMMIT/v1",
        &[session_id, &s_be, &r_be, &p_be, share],
    )
}

fn commit_combiner_coin_share(
    session_id: &[u8; 32],
    ext_sender_id: usize,
    ext_receiver_id: usize,
    party_id: usize,
    share: &[u8; 32],
) -> [u8; 32] {
    let s_be = (ext_sender_id as u64).to_be_bytes();
    let r_be = (ext_receiver_id as u64).to_be_bytes();
    let p_be = (party_id as u64).to_be_bytes();
    cshake256_32_multi_frame(
        b"QSAG.OT.COMBINER.COMMIT/v1",
        &[session_id, &s_be, &r_be, &p_be, share],
    )
}

// Bound active worker threads across concurrent mesh bootstraps and nested slot loops.
#[cfg(any(test, feature = "std"))]
static BASE_PROOF_WORKERS: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);
#[cfg(any(test, feature = "std"))]
pub(super) struct BaseProofWorkers {
    count: usize,
    added: usize,
}
#[cfg(any(test, feature = "std"))]
impl BaseProofWorkers {
    pub(super) fn hw_cap() -> usize {
        std::thread::available_parallelism()
            .map_or(1, usize::from)
            .min(32)
    }

    fn acquire(requested: usize) -> Self {
        use core::sync::atomic::Ordering;
        if requested <= 1 {
            return Self { count: 1, added: 0 };
        }
        let cap = Self::hw_cap();
        let mut current = BASE_PROOF_WORKERS.load(Ordering::Relaxed);
        loop {
            let active = current.max(1);
            let avail_extra = cap.saturating_sub(active);
            let extra = (requested - 1).min(avail_extra);
            if extra == 0 {
                return Self { count: 1, added: 0 };
            }
            let added = if current == 0 { extra + 1 } else { extra };
            match BASE_PROOF_WORKERS.compare_exchange_weak(
                current,
                current + added,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                Ok(_) => {
                    return Self {
                        count: 1 + extra,
                        added,
                    };
                }
                Err(value) => current = value,
            }
        }
    }
}
#[cfg(any(test, feature = "std"))]
impl Drop for BaseProofWorkers {
    fn drop(&mut self) {
        if self.added > 0 {
            BASE_PROOF_WORKERS.fetch_sub(self.added, core::sync::atomic::Ordering::Relaxed);
        }
    }
}

#[cfg(any(test, feature = "std"))]
pub(super) struct ActiveMeshWorkerGuard;
#[cfg(any(test, feature = "std"))]
impl ActiveMeshWorkerGuard {
    pub(super) fn enter() -> Self {
        BASE_PROOF_WORKERS.fetch_add(1, core::sync::atomic::Ordering::Relaxed);
        Self
    }
}
#[cfg(any(test, feature = "std"))]
impl Drop for ActiveMeshWorkerGuard {
    fn drop(&mut self) {
        BASE_PROOF_WORKERS.fetch_sub(1, core::sync::atomic::Ordering::Relaxed);
    }
}

impl BaseOtExtSenderRound1 {
    #[expect(
        clippy::type_complexity,
        reason = "Internal packed Base-OT block return tuple bundling secrets, pk0s, proof, and cached CRS"
    )]
    fn build_packed_block(
        crs_coin: &[u8; 32],
        session_id: &[u8; 32],
        ext_sender_id: usize,
        ext_receiver_id: usize,
        blk: usize,
        c_tilde_words: &[u64; RLWE_BASE_OT_WORDS],
        rng: &mut PartyPrivateRng,
    ) -> (
        Vec<RlweOtReceiverSecret>,
        Vec<RlwePoly>,
        RlweReceiverZkPok,
        Vec<(RlwePolyNtt, RlwePoly)>,
    ) {
        let m0 = blk * RLWE_BASE_OT_SLOTS_PER_BLOCK;
        let mixed_sid = crs_mixed_session_id(crs_coin, session_id);
        let (mut s_blk, mut e0) = loop {
            let mut s = RlwePoly::sample_ternary_eta1(rng);
            let mut e = RlwePoly::sample_ternary_eta1(rng);
            if black_box(bounded_ternary_witness(&s, &e)) {
                break (s, e);
            }
            wipe_u16s(&mut s.0);
            wipe_u16s(&mut e.0);
        };
        let mut s_blk_ntt = s_blk.to_ntt();
        let mut crs_pairs = Vec::with_capacity(RLWE_BASE_OT_SLOTS_PER_BLOCK);
        for grp in 0..(RLWE_BASE_OT_SLOTS_PER_BLOCK / 8) {
            let base = (m0 + 8 * grp) as u32;
            let idxs = core::array::from_fn(|k| base + k as u32);
            let a_batch =
                RlwePoly::from_crs_xof_batch8(&mixed_sid, ext_receiver_id, ext_sender_id, idxs, 0);
            let t_batch =
                RlwePoly::from_crs_xof_batch8(&mixed_sid, ext_receiver_id, ext_sender_id, idxs, 1);
            for (a_m, t_m) in a_batch.into_iter().zip(t_batch) {
                crs_pairs.push((a_m.to_ntt(), t_m));
            }
        }
        let (a0_ntt, t0) = &crs_pairs[0];
        let bit0 = ((c_tilde_words[m0 / 64] >> (m0 % 64)) & 1) == 1;
        let rlwe0 = a0_ntt.pointwise_mul_from_ntt(&s_blk_ntt).add(&e0);
        let shifted0 = rlwe0.sub(t0);
        let pk0_0 = RlwePoly::ct_select(bit0, &shifted0, &rlwe0);
        let pok = RlweReceiverZkPok::prove_ct(
            crs_coin,
            session_id,
            ext_receiver_id,
            ext_sender_id,
            m0 as u32,
            a0_ntt,
            t0,
            &pk0_0,
            &s_blk,
            &e0,
            bit0,
            rng,
        );
        wipe_u16s(&mut e0.0);

        let mut secs = Vec::with_capacity(RLWE_BASE_OT_SLOTS_PER_BLOCK);
        let mut pk0s = Vec::with_capacity(RLWE_BASE_OT_SLOTS_PER_BLOCK);
        secs.push(RlweOtReceiverSecret {
            crs_coin: *crs_coin,
            session_id: *session_id,
            sender_id: ext_receiver_id,
            receiver_id: ext_sender_id,
            ot_idx: m0 as u32,
            pk0: pk0_0,
            s_r: s_blk,
            choice_bit: bit0,
        });
        pk0s.push(pk0_0);

        for (slot, (a_ntt_m, t_m)) in crs_pairs.iter().enumerate().skip(1) {
            let m = m0 + slot;
            let bit_m = ((c_tilde_words[m / 64] >> (m % 64)) & 1) == 1;
            let mut e_m = RlwePoly::sample_ternary_eta1(rng);
            let rlwe_m = a_ntt_m.pointwise_mul_from_ntt(&s_blk_ntt).add(&e_m);
            wipe_u16s(&mut e_m.0);
            let shifted_m = rlwe_m.sub(t_m);
            let pk0_m = RlwePoly::ct_select(bit_m, &shifted_m, &rlwe_m);
            secs.push(RlweOtReceiverSecret {
                crs_coin: *crs_coin,
                session_id: *session_id,
                sender_id: ext_receiver_id,
                receiver_id: ext_sender_id,
                ot_idx: m as u32,
                pk0: pk0_m,
                s_r: s_blk,
                choice_bit: bit_m,
            });
            pk0s.push(pk0_m);
        }
        wipe_u16s(&mut s_blk_ntt.0);
        wipe_u16s(&mut s_blk.0);
        (secs, pk0s, pok, crs_pairs)
    }

    /// Step 1 (`OT-Ext Sender` local) bound to a jointly committed CRS coin `crs_coin`.
    pub fn start_with_crs(
        crs_coin: [u8; 32],
        session_id: [u8; 32],
        ext_sender_id: usize,
        ext_receiver_id: usize,
        sender_rng: &mut PartyPrivateRng,
    ) -> (Self, BaseOtRound1Msg) {
        let mut c_tilde_words = [0u64; RLWE_BASE_OT_WORDS];
        for w in &mut c_tilde_words {
            *w = sender_rng.next_u64();
        }
        let mut sec_states = Vec::with_capacity(RLWE_BASE_OT_COUNT);
        let mut pk0s = Vec::with_capacity(RLWE_BASE_OT_COUNT);
        let mut block_poks = Vec::with_capacity(RLWE_BASE_OT_BLOCKS);
        let mut cached_crs = Vec::with_capacity(RLWE_BASE_OT_COUNT);

        #[cfg(any(test, feature = "std"))]
        {
            let mut jobs: Vec<_> = (0..RLWE_BASE_OT_BLOCKS)
                .map(|blk| {
                    (
                        blk,
                        PartyPrivateRng::from_seed(
                            sender_rng.next_bytes32(),
                            b"QSAG.BASE_OT.PROOF/v2",
                        ),
                    )
                })
                .collect();
            let requested = std::thread::available_parallelism()
                .map_or(1, usize::from)
                .min(RLWE_BASE_OT_BLOCKS);
            let budget = BaseProofWorkers::acquire(requested);
            if budget.count <= 1 {
                for (blk, rng) in &mut jobs {
                    let (secs, pks, pok, crs) = Self::build_packed_block(
                        &crs_coin,
                        &session_id,
                        ext_sender_id,
                        ext_receiver_id,
                        *blk,
                        &c_tilde_words,
                        rng,
                    );
                    sec_states.extend(secs);
                    pk0s.extend(pks);
                    block_poks.push(pok);
                    cached_crs.extend(crs);
                }
            } else {
                let chunk_size = PublicDivisor::new(budget.count).ceil(jobs.len());
                let results = std::thread::scope(|scope| {
                    let words = &c_tilde_words;
                    let mut handles = Vec::with_capacity(budget.count);
                    for chunk in jobs.chunks_mut(chunk_size) {
                        handles.push(scope.spawn(move || {
                            chunk
                                .iter_mut()
                                .map(|(blk, rng)| {
                                    Self::build_packed_block(
                                        &crs_coin,
                                        &session_id,
                                        ext_sender_id,
                                        ext_receiver_id,
                                        *blk,
                                        words,
                                        rng,
                                    )
                                })
                                .collect::<Vec<_>>()
                        }));
                    }
                    handles
                        .into_iter()
                        .flat_map(|h| h.join().expect("base proof worker failed"))
                        .collect::<Vec<_>>()
                });
                for (secs, pks, pok, crs) in results {
                    sec_states.extend(secs);
                    pk0s.extend(pks);
                    block_poks.push(pok);
                    cached_crs.extend(crs);
                }
            }
        }
        #[cfg(not(any(test, feature = "std")))]
        for blk in 0..RLWE_BASE_OT_BLOCKS {
            let (secs, pks, pok, crs) = Self::build_packed_block(
                &crs_coin,
                &session_id,
                ext_sender_id,
                ext_receiver_id,
                blk,
                &c_tilde_words,
                sender_rng,
            );
            sec_states.extend(secs);
            pk0s.extend(pks);
            block_poks.push(pok);
            cached_crs.extend(crs);
        }
        (
            Self {
                session_id,
                ext_sender_id,
                ext_receiver_id,
                c_tilde_words,
                sec_states,
                cached_crs,
            },
            BaseOtRound1Msg { pk0s, block_poks },
        )
    }

    /// Step 1 (`OT-Ext Sender` local): sample 384 random Base-OT choice bits $\tilde{\mathbf{c}}$
    /// using ONLY `sender_rng` and emit `BaseOtRound1Msg` (3 packed 128-slot blocks with OR-Sigma ZKPoKs).
    pub fn start(
        session_id: [u8; 32],
        ext_sender_id: usize,
        ext_receiver_id: usize,
        sender_rng: &mut PartyPrivateRng,
    ) -> (Self, BaseOtRound1Msg) {
        Self::start_with_crs(
            [0u8; 32],
            session_id,
            ext_sender_id,
            ext_receiver_id,
            sender_rng,
        )
    }

    /// Step 3 (`OT-Ext Sender` local): verify all 384 Fujisaki–Okamoto re-encryptions in **strict
    /// constant time across all 384 branches** (`0` early-abort index timing leak!) before sampling
    /// or revealing any combiner coin.
    pub fn verify_fo_and_respond_coin(
        mut self,
        msg2: &BaseOtRound2Msg,
        sender_rng: &mut PartyPrivateRng,
    ) -> Result<(BaseOtExtSenderRound3, BaseOtRound3Msg), PreprocessError> {
        if msg2.reqs_len_mismatch(RLWE_BASE_OT_COUNT)
            || msg2.resps.iter().any(|r| {
                !r.u0.is_canonical()
                    || !r.v0.is_canonical()
                    || !r.u1.is_canonical()
                    || !r.v1.is_canonical()
            })
        {
            return Err(PreprocessError::BaseOtFoCheckFailed {
                sender_id: self.ext_receiver_id,
                receiver_id: self.ext_sender_id,
                ot_idx: 0,
            });
        }
        let cached_crs = core::mem::take(&mut self.cached_crs);
        let mut base_seeds = SecretBuffer(vec![[0u8; 32]; RLWE_BASE_OT_COUNT]);
        let mut results = (0..RLWE_BASE_OT_COUNT)
            .map(|_| (SecretBuffer([0u8; 32]), Ok(0u8)))
            .collect::<Vec<_>>();
        parallel_slots(&mut results, |m, result| {
            result.1 = (|| {
                let (a_ntt, t_crs) = &cached_crs[m];
                let (seed_m, ok_m) =
                    rlwe_ot_decrypt_ct_mask(&self.sec_states[m], a_ntt, t_crs, &msg2.resps[m])?;
                *result.0 = seed_m;
                Ok::<_, PreprocessError>(ok_m)
            })();
        });
        drop(cached_crs);
        let mut all_ok = 1u8;
        for (m, result) in results.into_iter().enumerate() {
            let (seed, ok) = result;
            base_seeds[m] = *seed;
            all_ok &= ok?;
        }
        if black_box(all_ok) == 0 {
            return Err(PreprocessError::BaseOtFoCheckFailed {
                sender_id: self.ext_receiver_id,
                receiver_id: self.ext_sender_id,
                ot_idx: 0,
            });
        }
        let my_coin_share = sender_rng.next_bytes32();
        let c_tilde_words = self.c_tilde_words;
        wipe_u64s(&mut self.c_tilde_words);
        let verified_base_seeds = core::mem::take(&mut base_seeds.0);
        Ok((
            BaseOtExtSenderRound3 {
                session_id: self.session_id,
                ext_sender_id: self.ext_sender_id,
                ext_receiver_id: self.ext_receiver_id,
                c_tilde_words,
                base_seeds: verified_base_seeds,
                peer_coin_commit: msg2.receiver_coin_commit,
                my_coin_share,
            },
            BaseOtRound3Msg {
                sender_coin_share: my_coin_share,
            },
        ))
    }

    /// Alias for [`Self::verify_fo_and_respond_coin`].
    #[inline]
    pub fn verify_fo_and_commit_coin(
        self,
        msg2: &BaseOtRound2Msg,
        sender_rng: &mut PartyPrivateRng,
    ) -> Result<(BaseOtExtSenderRound3, BaseOtRound3Msg), PreprocessError> {
        self.verify_fo_and_respond_coin(msg2, sender_rng)
    }
}

impl BaseOtRound2Msg {
    #[inline]
    fn reqs_len_mismatch(&self, expected: usize) -> bool {
        self.resps.len() != expected
    }
}

impl BaseOtExtReceiverRound2 {
    /// Step 2 (`OT-Ext Receiver` local) bound to jointly committed `crs_coin`: verifies all 3
    /// block Receiver OR-Sigma ZKPoKs (`BaseOtReceiverProofFailed` on tamper!) before FO-encrypting
    /// all 384 seed pairs under per-slot `(a_m, t_m)` (`PVW08` lossy-branch security on every slot).
    pub fn respond_with_crs(
        crs_coin: [u8; 32],
        session_id: [u8; 32],
        ext_sender_id: usize,
        ext_receiver_id: usize,
        msg1: &BaseOtRound1Msg,
        receiver_rng: &mut PartyPrivateRng,
    ) -> Result<(Self, BaseOtRound2Msg), PreprocessError> {
        if msg1.pk0s.len() != RLWE_BASE_OT_COUNT || msg1.block_poks.len() != RLWE_BASE_OT_BLOCKS {
            return Err(PreprocessError::BaseOtFoCheckFailed {
                sender_id: ext_receiver_id,
                receiver_id: ext_sender_id,
                ot_idx: 0,
            });
        }
        if msg1.pk0s.iter().any(|p| !p.is_canonical()) {
            return Err(PreprocessError::BaseOtReceiverProofFailed {
                sender_id: ext_receiver_id,
                receiver_id: ext_sender_id,
            });
        }
        let mixed_sid = crs_mixed_session_id(&crs_coin, &session_id);
        let mut proof_valid = [false; RLWE_BASE_OT_BLOCKS];
        parallel_slots(&mut proof_valid, |blk, valid| {
            let m0 = (blk * RLWE_BASE_OT_SLOTS_PER_BLOCK) as u32;
            let a0_ntt =
                RlwePoly::from_crs_xof(&mixed_sid, ext_receiver_id, ext_sender_id, m0, 0).to_ntt();
            let t0 = RlwePoly::from_crs_xof(&mixed_sid, ext_receiver_id, ext_sender_id, m0, 1);
            *valid = msg1.block_poks[blk].verify(
                &crs_coin,
                &session_id,
                ext_receiver_id,
                ext_sender_id,
                m0,
                &a0_ntt,
                &t0,
                &msg1.pk0s[m0 as usize],
            );
        });
        if proof_valid.iter().any(|valid| !valid) {
            return Err(PreprocessError::BaseOtReceiverProofFailed {
                sender_id: ext_receiver_id,
                receiver_id: ext_sender_id,
            });
        }
        // Preserve the RNG schedule independently of worker scheduling.
        let mut seeds = SecretBuffer(
            (0..RLWE_BASE_OT_COUNT)
                .map(|_| {
                    [
                        receiver_rng.next_bytes32(),
                        receiver_rng.next_bytes32(),
                        receiver_rng.next_bytes32(),
                        receiver_rng.next_bytes32(),
                    ]
                })
                .collect::<Vec<_>>(),
        );
        let mut results = (0..RLWE_BASE_OT_COUNT).map(|_| None).collect::<Vec<_>>();
        parallel_slots(
            &mut results.chunks_mut(8).collect::<Vec<_>>(),
            |grp, chunk| {
                let base_m = 8 * grp;
                let idxs = core::array::from_fn(|k| (base_m + k) as u32);
                let a_batch = RlwePoly::from_crs_xof_batch8(
                    &mixed_sid,
                    ext_receiver_id,
                    ext_sender_id,
                    idxs,
                    0,
                );
                let t_batch = RlwePoly::from_crs_xof_batch8(
                    &mixed_sid,
                    ext_receiver_id,
                    ext_sender_id,
                    idxs,
                    1,
                );
                for (k, result) in chunk.iter_mut().enumerate() {
                    let m = base_m + k;
                    let pk0 = &msg1.pk0s[m];
                    let [mut s0, mut s1, mut rho0, mut rho1] = seeds[m];
                    let a_ntt = a_batch[k].to_ntt();
                    let pk1 = pk0.add(&t_batch[k]);
                    let (u0, v0) = rlwe_fo_encrypt_branch(
                        &crs_coin,
                        &session_id,
                        ext_receiver_id,
                        ext_sender_id,
                        m as u32,
                        0,
                        &a_ntt,
                        pk0,
                        &s0,
                        &rho0,
                    );
                    let (u1, v1) = rlwe_fo_encrypt_branch(
                        &crs_coin,
                        &session_id,
                        ext_receiver_id,
                        ext_sender_id,
                        m as u32,
                        1,
                        &a_ntt,
                        &pk1,
                        &s1,
                        &rho1,
                    );
                    wipe_bytes32(&mut rho0);
                    wipe_bytes32(&mut rho1);
                    wipe_bytes32(&mut s0);
                    wipe_bytes32(&mut s1);
                    *result = Some(RlweOtSenderMsg { u0, v0, u1, v1 });
                }
            },
        );
        let mut base_seed_pairs = Vec::with_capacity(RLWE_BASE_OT_COUNT);
        for seed in seeds.iter_mut() {
            base_seed_pairs.push((seed[0], seed[1]));
            for value in seed {
                wipe_bytes32(value);
            }
        }
        let resps = results
            .into_iter()
            .map(|r| r.expect("every slot is evaluated"))
            .collect();
        let my_coin_share = receiver_rng.next_bytes32();
        let combiner_prf_seed = receiver_rng.next_bytes32();
        let receiver_coin_commit = commit_combiner_coin_share(
            &session_id,
            ext_sender_id,
            ext_receiver_id,
            ext_receiver_id,
            &my_coin_share,
        );
        Ok((
            Self {
                session_id,
                ext_sender_id,
                ext_receiver_id,
                base_seed_pairs,
                my_coin_share,
                combiner_prf_seed,
            },
            BaseOtRound2Msg {
                resps,
                receiver_coin_commit,
            },
        ))
    }

    /// Step 2 (`OT-Ext Receiver` local): verify 384 OR-Sigma ZKPoKs and FO-encrypt 384 seed pairs.
    pub fn respond(
        session_id: [u8; 32],
        ext_sender_id: usize,
        ext_receiver_id: usize,
        msg1: &BaseOtRound1Msg,
        receiver_rng: &mut PartyPrivateRng,
    ) -> Result<(Self, BaseOtRound2Msg), PreprocessError> {
        Self::respond_with_crs(
            [0u8; 32],
            session_id,
            ext_sender_id,
            ext_receiver_id,
            msg1,
            receiver_rng,
        )
    }

    /// Step 4 (`OT-Ext Receiver` local): receive Sender's coin share, open Receiver's committed coin
    /// share, fold the `512` Base OTs into `256` active-secure Base OTs via 4-ciphertext parity
    /// combiner tables, construct `128` depth-2 GGM $\mathbb{F}_4$ slices, wipe all raw Base-OT
    /// seeds, and build [`OtExtReceiverChannel`].
    pub fn finalize(mut self, msg3: &BaseOtRound3Msg) -> (OtExtReceiverChannel, BaseOtRound4Msg) {
        let mut combined_coin = [0u8; 32];
        for (b, combined_coin_b_item) in combined_coin[..32].iter_mut().enumerate() {
            *combined_coin_b_item = self.my_coin_share[b] ^ msg3.sender_coin_share[b];
        }
        let extractor = derive_extractor_matrix_256x512(
            &self.session_id,
            self.ext_sender_id,
            self.ext_receiver_id,
            &combined_coin,
        );
        let mut comb_rng =
            PartyPrivateRng::from_seed(self.combiner_prf_seed, b"QSAG.OT.PARCOMB.RNG/v1");
        wipe_bytes32(&mut self.combiner_prf_seed);

        let supports: Vec<Vec<usize>> = extractor
            .iter()
            .map(|bits| {
                (0..RLWE_BASE_OT_COUNT)
                    .filter(|&m| ((bits[m / 64] >> (m % 64)) & 1) == 1)
                    .collect()
            })
            .collect();
        // Draw all masks in the original row/step order before scheduling work.
        let masks = SecretBuffer(
            supports
                .iter()
                .map(|support| {
                    (1..support.len())
                        .map(|_| (comb_rng.next_bytes32(), comb_rng.next_bytes32()))
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>(),
        );
        let mut rows = SecretBuffer(vec![
            (([0u8; 32], [0u8; 32]), Vec::new());
            OT_EXT_SUBSPACE_BITS
        ]);
        parallel_slots(&mut rows[..], |row, output| {
            let support = &supports[row];
            let m0 = support[0];
            let mut cur_l0 = combiner_step_hash32(
                &self.session_id,
                row,
                0,
                0,
                0,
                &[0u8; 32],
                &self.base_seed_pairs[m0].0,
            );
            let mut cur_l1 = combiner_step_hash32(
                &self.session_id,
                row,
                0,
                0,
                1,
                &[0u8; 32],
                &self.base_seed_pairs[m0].1,
            );

            let mut row_tables = Vec::with_capacity(support.len().saturating_sub(1));
            for (step_minus1, &mr) in support.iter().skip(1).enumerate() {
                let step = step_minus1 + 1;
                let (next_l0, next_l1) = masks[row][step_minus1];
                let mut tbl = [[0u8; 32]; 4];
                let pads = SecretBuffer(combiner_step_hash32_x4(
                    &self.session_id,
                    row,
                    step,
                    &(cur_l0, cur_l1),
                    &self.base_seed_pairs[mr],
                ));
                for slot in 0..4 {
                    let target = if (slot / 2) ^ (slot % 2) == 0 {
                        &next_l0
                    } else {
                        &next_l1
                    };
                    for b in 0..32 {
                        tbl[slot][b] = target[b] ^ pads[slot][b];
                    }
                }
                wipe_bytes32(&mut cur_l0);
                wipe_bytes32(&mut cur_l1);
                cur_l0 = next_l0;
                cur_l1 = next_l1;
                row_tables.push(tbl);
            }
            *output = ((cur_l0, cur_l1), row_tables);
        });
        let mut combined_seed_pairs = Box::new([([0u8; 32], [0u8; 32]); OT_EXT_SUBSPACE_BITS]);
        let mut parity_tables = Vec::with_capacity(OT_EXT_SUBSPACE_BITS);
        for (row, (mut pair, tables)) in core::mem::take(&mut rows.0).into_iter().enumerate() {
            combined_seed_pairs[row] = pair;
            wipe_bytes32(&mut pair.0);
            wipe_bytes32(&mut pair.1);
            parity_tables.push(tables);
        }

        let mut slice_seeds = Box::new([[[0u8; 32]; 4]; OT_EXT_F4_SLICES]);
        let mut ggm_sib2 = Vec::with_capacity(OT_EXT_F4_SLICES);
        for j in 0..OT_EXT_F4_SLICES {
            let (r_seed, l_seed) = &combined_seed_pairs[j];
            let (k1_0, k1_1) = &combined_seed_pairs[OT_EXT_F4_SLICES + j];
            let (leaves, sib2) =
                softspoken_f4_slice_setup_receiver(&self.session_id, j, r_seed, l_seed, k1_0, k1_1);
            slice_seeds[j] = leaves;
            ggm_sib2.push(sib2);
        }
        for (s0, s1) in combined_seed_pairs.iter_mut() {
            wipe_bytes32(s0);
            wipe_bytes32(s1);
        }

        for (s0, s1) in &mut self.base_seed_pairs {
            wipe_bytes32(s0);
            wipe_bytes32(s1);
        }
        let msg4 = BaseOtRound4Msg {
            receiver_coin_share: self.my_coin_share,
            parity_tables,
            ggm_sib2,
        };
        (
            OtExtReceiverChannel {
                session_id: self.session_id,
                sender_id: self.ext_sender_id,
                receiver_id: self.ext_receiver_id,
                slice_seeds,
                batch_ctr: 0,
            },
            msg4,
        )
    }
}

impl BaseOtExtSenderRound3 {
    /// Step 5 (`OT-Ext Sender` local): verify Receiver's coin commitment, evaluate all 256 parity
    /// combiner chains in constant time to obtain `delta = E * c_tilde` (`256` bits) and
    /// `128` 3-out-of-4 punctured $\mathbb{F}_4$ GGM slices, wipe `c_tilde_words` and `base_seeds`,
    /// and finalize [`OtExtSenderChannel`].
    pub fn finalize(
        mut self,
        msg4: &BaseOtRound4Msg,
    ) -> Result<OtExtSenderChannel, PreprocessError> {
        let expected_commit = commit_combiner_coin_share(
            &self.session_id,
            self.ext_sender_id,
            self.ext_receiver_id,
            self.ext_receiver_id,
            &msg4.receiver_coin_share,
        );
        if !ct_eq_bytes32(&expected_commit, &self.peer_coin_commit) {
            return Err(PreprocessError::CoinCommitMismatch {
                party_id: self.ext_receiver_id,
            });
        }
        if msg4.parity_tables.len() != OT_EXT_SUBSPACE_BITS
            || msg4.ggm_sib2.len() != OT_EXT_F4_SLICES
        {
            return Err(PreprocessError::KosOtCheckFailed {
                sender_id: self.ext_sender_id,
                receiver_id: self.ext_receiver_id,
            });
        }
        let mut combined_coin = [0u8; 32];
        for (b, combined_coin_b_item) in combined_coin[..32].iter_mut().enumerate() {
            *combined_coin_b_item = msg4.receiver_coin_share[b] ^ self.my_coin_share[b];
        }
        let extractor = derive_extractor_matrix_256x512(
            &self.session_id,
            self.ext_sender_id,
            self.ext_receiver_id,
            &combined_coin,
        );
        let mut delta = [0u128; 2];
        let mut combined_seeds = Box::new([[0u8; 32]; OT_EXT_SUBSPACE_BITS]);

        let supports: Vec<Vec<usize>> = extractor
            .iter()
            .map(|bits| {
                (0..RLWE_BASE_OT_COUNT)
                    .filter(|&m| ((bits[m / 64] >> (m % 64)) & 1) == 1)
                    .collect()
            })
            .collect();
        for (row, support) in supports.iter().enumerate() {
            if msg4.parity_tables[row].len() + 1 != support.len() {
                return Err(PreprocessError::KosOtCheckFailed {
                    sender_id: self.ext_sender_id,
                    receiver_id: self.ext_receiver_id,
                });
            }
        }
        let mut row_bits = [0u8; OT_EXT_SUBSPACE_BITS];
        let mut rows = SecretBuffer(vec![([0u8; 32], 0u8); OT_EXT_SUBSPACE_BITS]);
        parallel_slots(&mut rows[..], |row, output| {
            let support = &supports[row];
            let m0 = support[0];
            let mut acc_bit = ((black_box(self.c_tilde_words[m0 / 64]) >> (m0 % 64)) & 1) as u8;
            let mut cur_label = combiner_step_hash32(
                &self.session_id,
                row,
                0,
                0,
                acc_bit,
                &[0u8; 32],
                &self.base_seeds[m0],
            );

            for (step_minus1, &mr) in support.iter().skip(1).enumerate() {
                let step = step_minus1 + 1;
                let gamma = ((black_box(self.c_tilde_words[mr / 64]) >> (mr % 64)) & 1) as u8;
                let slot = (acc_bit << 1) | gamma;
                let ct_entry = ct_select_bytes32_4(&msg4.parity_tables[row][step_minus1], slot);
                let pad = combiner_step_hash32(
                    &self.session_id,
                    row,
                    step,
                    acc_bit,
                    gamma,
                    &cur_label,
                    &self.base_seeds[mr],
                );
                for b in 0..32 {
                    cur_label[b] = ct_entry[b] ^ pad[b];
                }
                acc_bit ^= gamma;
            }
            *output = (cur_label, acc_bit);
        });
        for row in 0..OT_EXT_SUBSPACE_BITS {
            combined_seeds[row] = rows[row].0;
            row_bits[row] = rows[row].1;
            delta[row / 128] |= (row_bits[row] as u128) << (row % 128);
        }

        let mut punctured_seeds = Box::new([[[0u8; 32]; 4]; OT_EXT_F4_SLICES]);
        for j in 0..OT_EXT_F4_SLICES {
            punctured_seeds[j] = softspoken_f4_slice_setup_sender_ct(
                &self.session_id,
                j,
                row_bits[j],
                row_bits[OT_EXT_F4_SLICES + j],
                &combined_seeds[j],
                &combined_seeds[OT_EXT_F4_SLICES + j],
                &msg4.ggm_sib2[j],
            );
        }
        wipe_bytes(&mut row_bits);
        for s in combined_seeds.iter_mut() {
            wipe_bytes32(s);
        }

        wipe_u64s(&mut self.c_tilde_words);
        for s in &mut self.base_seeds {
            wipe_bytes32(s);
        }
        Ok(OtExtSenderChannel {
            session_id: self.session_id,
            sender_id: self.ext_sender_id,
            receiver_id: self.ext_receiver_id,
            delta,
            punctured_seeds,
            batch_ctr: 0,
            poisoned: alloc::sync::Arc::new(core::sync::atomic::AtomicBool::new(false)),
        })
    }
}
fn encode_rlwe_poly_vec(out: &mut Vec<u8>, poly: &RlwePoly) {
    let mut buf = [0u8; RLWE_N * 2];
    encode_rlwe_poly_le(poly, &mut buf);
    out.extend_from_slice(&buf);
}

fn decode_rlwe_poly_slice(raw: &[u8], pos: &mut usize) -> Option<RlwePoly> {
    let bytes = raw.get(*pos..*pos + RLWE_N * 2)?;
    *pos += RLWE_N * 2;
    let mut coeffs = [0u16; RLWE_N];
    for (i, slot) in coeffs.iter_mut().enumerate() {
        *slot = u16::from_le_bytes([bytes[2 * i], bytes[2 * i + 1]]);
    }
    let poly = RlwePoly(coeffs);
    poly.is_canonical().then_some(poly)
}

fn encode_i16_box_reps(out: &mut Vec<u8>, reps: &[[i16; RLWE_N]; RLWE_ZKPOK_REPS]) {
    for arr in reps {
        for &v in arr {
            out.extend_from_slice(&v.to_le_bytes());
        }
    }
}

fn decode_i16_box_reps(
    raw: &[u8],
    pos: &mut usize,
) -> Option<Box<[[i16; RLWE_N]; RLWE_ZKPOK_REPS]>> {
    let need = RLWE_ZKPOK_REPS * RLWE_N * 2;
    let bytes = raw.get(*pos..*pos + need)?;
    *pos += need;
    let mut out = Box::new([[0i16; RLWE_N]; RLWE_ZKPOK_REPS]);
    let mut off = 0usize;
    for rep in out.iter_mut() {
        for coeff in rep.iter_mut() {
            *coeff = i16::from_le_bytes([bytes[off], bytes[off + 1]]);
            off += 2;
        }
    }
    Some(out)
}

impl BaseOtCrsCommitMsg {
    pub fn to_bytes(&self) -> [u8; 32] {
        self.receiver_crs_commit
    }

    pub fn from_bytes(raw: &[u8]) -> Option<Self> {
        let receiver_crs_commit: [u8; 32] = raw.try_into().ok()?;
        Some(Self {
            receiver_crs_commit,
        })
    }
}

impl BaseOtCrsShareMsg {
    pub fn to_bytes(&self) -> [u8; 32] {
        self.sender_crs_share
    }

    pub fn from_bytes(raw: &[u8]) -> Option<Self> {
        let sender_crs_share: [u8; 32] = raw.try_into().ok()?;
        Some(Self { sender_crs_share })
    }
}

impl BaseOtCrsOpenMsg {
    pub fn to_bytes(&self) -> [u8; 32] {
        self.receiver_crs_share
    }

    pub fn from_bytes(raw: &[u8]) -> Option<Self> {
        let receiver_crs_share: [u8; 32] = raw.try_into().ok()?;
        Some(Self { receiver_crs_share })
    }
}

impl BaseOtRound1Msg {
    /// Canonical byte serialization (`384` canonical `RlwePoly`s + `3` `RlweReceiverZkPok`s).
    pub fn to_bytes(&self) -> Vec<u8> {
        let pok_bytes = RLWE_ZKPOK_REPS * 8 + 4 * RLWE_ZKPOK_REPS * RLWE_N * 2;
        let mut out = Vec::with_capacity(
            8 + self.pk0s.len() * RLWE_N * 2 + self.block_poks.len() * pok_bytes,
        );
        out.extend_from_slice(&(self.pk0s.len() as u32).to_be_bytes());
        out.extend_from_slice(&(self.block_poks.len() as u32).to_be_bytes());
        for pk0 in &self.pk0s {
            encode_rlwe_poly_vec(&mut out, pk0);
        }
        for pok in &self.block_poks {
            for &c in &pok.chal0 {
                out.extend_from_slice(&c.to_le_bytes());
            }
            for &c in &pok.chal1 {
                out.extend_from_slice(&c.to_le_bytes());
            }
            encode_i16_box_reps(&mut out, &pok.z_s0);
            encode_i16_box_reps(&mut out, &pok.z_e0);
            encode_i16_box_reps(&mut out, &pok.z_s1);
            encode_i16_box_reps(&mut out, &pok.z_e1);
        }
        out
    }

    /// Strict canonical decoder rejecting non-canonical lengths or coefficients.
    pub fn from_bytes(raw: &[u8]) -> Option<Self> {
        if raw.len() < 8 {
            return None;
        }
        let pk_len = u32::from_be_bytes(raw[0..4].try_into().ok()?) as usize;
        let pok_len = u32::from_be_bytes(raw[4..8].try_into().ok()?) as usize;
        if pk_len != RLWE_BASE_OT_COUNT || pok_len != RLWE_BASE_OT_BLOCKS {
            return None;
        }
        let mut pos = 8usize;
        validate_frame_count(pk_len, RLWE_N * 2, raw.len() - pos).ok()?;
        let mut pk0s = Vec::with_capacity(pk_len);
        for _ in 0..pk_len {
            pk0s.push(decode_rlwe_poly_slice(raw, &mut pos)?);
        }
        let pok_bytes = RLWE_ZKPOK_REPS * 8 + 4 * RLWE_ZKPOK_REPS * RLWE_N * 2;
        validate_frame_count(pok_len, pok_bytes, raw.len() - pos).ok()?;
        let mut block_poks = Vec::with_capacity(pok_len);
        for _ in 0..pok_len {
            let mut chal0 = [0u32; RLWE_ZKPOK_REPS];
            let mut chal1 = [0u32; RLWE_ZKPOK_REPS];
            for slot in &mut chal0 {
                let b: [u8; 4] = raw.get(pos..pos + 4)?.try_into().ok()?;
                pos += 4;
                *slot = u32::from_le_bytes(b);
            }
            for slot in &mut chal1 {
                let b: [u8; 4] = raw.get(pos..pos + 4)?.try_into().ok()?;
                pos += 4;
                *slot = u32::from_le_bytes(b);
            }
            let z_s0 = decode_i16_box_reps(raw, &mut pos)?;
            let z_e0 = decode_i16_box_reps(raw, &mut pos)?;
            let z_s1 = decode_i16_box_reps(raw, &mut pos)?;
            let z_e1 = decode_i16_box_reps(raw, &mut pos)?;
            block_poks.push(RlweReceiverZkPok {
                chal0,
                chal1,
                z_s0,
                z_e0,
                z_s1,
                z_e1,
            });
        }
        (pos == raw.len()).then_some(Self { pk0s, block_poks })
    }
}

impl BaseOtRound2Msg {
    /// Canonical byte serialization (`384` 4-poly FO responses + 32-byte combiner coin commitment).
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(4 + self.resps.len() * 4 * RLWE_N * 2 + 32);
        out.extend_from_slice(&(self.resps.len() as u32).to_be_bytes());
        for r in &self.resps {
            encode_rlwe_poly_vec(&mut out, &r.u0);
            encode_rlwe_poly_vec(&mut out, &r.v0);
            encode_rlwe_poly_vec(&mut out, &r.u1);
            encode_rlwe_poly_vec(&mut out, &r.v1);
        }
        out.extend_from_slice(&self.receiver_coin_commit);
        out
    }

    /// Strict canonical decoder.
    pub fn from_bytes(raw: &[u8]) -> Option<Self> {
        if raw.len() < 36 {
            return None;
        }
        let count = u32::from_be_bytes(raw[0..4].try_into().ok()?) as usize;
        if count != RLWE_BASE_OT_COUNT {
            return None;
        }
        let mut pos = 4usize;
        validate_frame_count(count, 4 * RLWE_N * 2, raw.len() - pos - 32).ok()?;
        let mut resps = Vec::with_capacity(count);
        for _ in 0..count {
            let u0 = decode_rlwe_poly_slice(raw, &mut pos)?;
            let v0 = decode_rlwe_poly_slice(raw, &mut pos)?;
            let u1 = decode_rlwe_poly_slice(raw, &mut pos)?;
            let v1 = decode_rlwe_poly_slice(raw, &mut pos)?;
            resps.push(RlweOtSenderMsg { u0, v0, u1, v1 });
        }
        let receiver_coin_commit: [u8; 32] = raw.get(pos..pos + 32)?.try_into().ok()?;
        pos += 32;
        (pos == raw.len()).then_some(Self {
            resps,
            receiver_coin_commit,
        })
    }
}

impl BaseOtRound3Msg {
    pub fn to_bytes(&self) -> [u8; 32] {
        self.sender_coin_share
    }

    pub fn from_bytes(raw: &[u8]) -> Option<Self> {
        let sender_coin_share: [u8; 32] = raw.try_into().ok()?;
        Some(Self { sender_coin_share })
    }
}

impl BaseOtRound4Msg {
    /// Canonical byte serialization (`32`-byte coin opening + `256` length-prefixed parity tables +
    /// `128` 64-byte GGM sibling pairs).
    pub fn to_bytes(&self) -> Vec<u8> {
        let entries: usize = self.parity_tables.iter().map(Vec::len).sum();
        let mut out = Vec::with_capacity(
            32 + 2 + self.parity_tables.len() * 2 + entries * 128 + self.ggm_sib2.len() * 64,
        );
        out.extend_from_slice(&self.receiver_coin_share);
        out.extend_from_slice(&(self.parity_tables.len() as u16).to_be_bytes());
        for row in &self.parity_tables {
            out.extend_from_slice(&(row.len() as u16).to_be_bytes());
            for tbl in row {
                for entry in tbl {
                    out.extend_from_slice(entry);
                }
            }
        }
        for (ct0, ct1) in &self.ggm_sib2 {
            out.extend_from_slice(ct0);
            out.extend_from_slice(ct1);
        }
        out
    }

    /// Strict canonical decoder.
    pub fn from_bytes(raw: &[u8]) -> Option<Self> {
        if raw.len() < 34 + OT_EXT_F4_SLICES * 64 {
            return None;
        }
        let receiver_coin_share: [u8; 32] = raw[0..32].try_into().ok()?;
        let rows = u16::from_be_bytes([raw[32], raw[33]]) as usize;
        if rows != OT_EXT_SUBSPACE_BITS {
            return None;
        }
        let mut pos = 34usize;
        let mut parity_tables = Vec::with_capacity(OT_EXT_SUBSPACE_BITS);
        for _ in 0..OT_EXT_SUBSPACE_BITS {
            let len_bytes: [u8; 2] = raw.get(pos..pos + 2)?.try_into().ok()?;
            pos += 2;
            let row_len = u16::from_be_bytes(len_bytes) as usize;
            if row_len > RLWE_BASE_OT_COUNT {
                return None;
            }
            validate_frame_count(row_len, 128, raw.len() - pos).ok()?;
            let mut row = Vec::with_capacity(row_len);
            for _ in 0..row_len {
                let mut tbl = [[0u8; 32]; 4];
                for entry in &mut tbl {
                    entry.copy_from_slice(raw.get(pos..pos + 32)?);
                    pos += 32;
                }
                row.push(tbl);
            }
            parity_tables.push(row);
        }
        if raw.len() - pos != OT_EXT_F4_SLICES * 64 {
            return None;
        }
        let mut ggm_sib2 = Vec::with_capacity(OT_EXT_F4_SLICES);
        for _ in 0..OT_EXT_F4_SLICES {
            let mut ct0 = [0u8; 32];
            let mut ct1 = [0u8; 32];
            ct0.copy_from_slice(raw.get(pos..pos + 32)?);
            pos += 32;
            ct1.copy_from_slice(raw.get(pos..pos + 32)?);
            pos += 32;
            ggm_sib2.push((ct0, ct1));
        }
        (pos == raw.len()).then_some(Self {
            receiver_coin_share,
            parity_tables,
            ggm_sib2,
        })
    }
}
