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
