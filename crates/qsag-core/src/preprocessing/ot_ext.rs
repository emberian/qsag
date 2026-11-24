//! SoftSpokenOT extension channels, KOS consistency checks and the party mesh.

#[cfg(any(test, feature = "std"))]
use super::rlwe_base_ot::{ActiveMeshWorkerGuard, BaseProofWorkers};
use super::*;

/// Established `SoftSpokenOT (n_C = 256, k = 2)` Ring-LWE OT-Extension Sender channel (`!Clone`,
/// wiped on `Drop`). All forks share the poison latch. Each fork owns its seed memory and
/// erases it when observing poison in a mutable protocol operation or on drop.
pub struct OtExtSenderChannel {
    pub session_id: [u8; 32],
    pub sender_id: usize,
    pub receiver_id: usize,
    pub(super) delta: [u128; 2],
    pub(super) punctured_seeds: Box<[[[u8; 32]; 4]; OT_EXT_F4_SLICES]>,
    pub(super) batch_ctr: u64,
    pub(super) poisoned: alloc::sync::Arc<core::sync::atomic::AtomicBool>,
}

impl OtExtSenderChannel {
    /// Whether this channel or any substream sharing its 256-bit `delta` correlation has aborted.
    #[inline]
    pub fn is_poisoned(&self) -> bool {
        self.poisoned.load(core::sync::atomic::Ordering::SeqCst)
    }

    fn wipe_local_secrets(&mut self) {
        wipe_u128s(&mut self.delta);
        for slice in self.punctured_seeds.iter_mut() {
            for s in slice.iter_mut() {
                wipe_bytes32(s);
            }
        }
    }

    fn poison_and_wipe(&mut self) {
        self.poisoned
            .store(true, core::sync::atomic::Ordering::SeqCst);
        self.wipe_local_secrets();
    }

    /// Derive a domain-separated child sender channel over the same 256-bit `delta` correlation
    /// so independent concurrent repetition streams never contend or re-run Ring-LWE Base OT.
    ///
    /// Shares the parent's atomic poison latch so any consistency-check failure on any forked
    /// substream permanently poisons the parent and every sibling substream sharing `delta`.
    pub fn fork_substream(
        &self,
        child_session_id: [u8; 32],
        stream_idx: u64,
    ) -> Result<Self, PreprocessError> {
        if self.is_poisoned() {
            return Err(PreprocessError::ChannelPoisoned {
                sender_id: self.sender_id,
                receiver_id: self.receiver_id,
            });
        }
        let s_be = (self.sender_id as u64).to_be_bytes();
        let r_be = (self.receiver_id as u64).to_be_bytes();
        let idx_be = stream_idx.to_be_bytes();
        let mut punctured_seeds = Box::new([[[0u8; 32]; 4]; OT_EXT_F4_SLICES]);
        for j in 0..OT_EXT_F4_SLICES {
            for v in 0..4usize {
                let leaf_be = ((4 * j + v) as u64).to_be_bytes();
                punctured_seeds[j][v] = cshake256_32_multi_frame(
                    b"QSAG.OT.EXT.FORK/v1",
                    &[
                        &self.session_id,
                        &child_session_id,
                        &s_be,
                        &r_be,
                        &idx_be,
                        &leaf_be,
                        &self.punctured_seeds[j][v],
                    ],
                );
            }
            let b0 = ((black_box(self.delta[0]) >> j) & 1) as u8;
            let b1 = ((black_box(self.delta[1]) >> j) & 1) as u8;
            softspoken_f4_zero_punctured_slot_ct(&mut punctured_seeds[j], b0, b1);
        }
        if self.is_poisoned() {
            for slice in punctured_seeds.iter_mut() {
                for s in slice.iter_mut() {
                    wipe_bytes32(s);
                }
            }
            return Err(PreprocessError::ChannelPoisoned {
                sender_id: self.sender_id,
                receiver_id: self.receiver_id,
            });
        }
        Ok(Self {
            session_id: child_session_id,
            sender_id: self.sender_id,
            receiver_id: self.receiver_id,
            delta: self.delta,
            punctured_seeds,
            batch_ctr: 0,
            poisoned: alloc::sync::Arc::clone(&self.poisoned),
        })
    }
}

impl Drop for OtExtSenderChannel {
    fn drop(&mut self) {
        self.wipe_local_secrets();
    }
}

/// Established `SoftSpokenOT (n_C = 256, k = 2)` Ring-LWE OT-Extension Receiver channel (`!Clone`, wiped on `Drop`).
pub struct OtExtReceiverChannel {
    pub session_id: [u8; 32],
    pub sender_id: usize,
    pub receiver_id: usize,
    pub(super) slice_seeds: Box<[[[u8; 32]; 4]; OT_EXT_F4_SLICES]>,
    pub(super) batch_ctr: u64,
}

impl OtExtReceiverChannel {
    /// Derive the matching domain-separated child receiver channel for [`OtExtSenderChannel::fork_substream`].
    pub fn fork_substream(&self, child_session_id: [u8; 32], stream_idx: u64) -> Self {
        let s_be = (self.sender_id as u64).to_be_bytes();
        let r_be = (self.receiver_id as u64).to_be_bytes();
        let idx_be = stream_idx.to_be_bytes();
        let mut slice_seeds = Box::new([[[0u8; 32]; 4]; OT_EXT_F4_SLICES]);
        for j in 0..OT_EXT_F4_SLICES {
            for v in 0..4usize {
                let leaf_be = ((4 * j + v) as u64).to_be_bytes();
                slice_seeds[j][v] = cshake256_32_multi_frame(
                    b"QSAG.OT.EXT.FORK/v1",
                    &[
                        &self.session_id,
                        &child_session_id,
                        &s_be,
                        &r_be,
                        &idx_be,
                        &leaf_be,
                        &self.slice_seeds[j][v],
                    ],
                );
            }
        }
        Self {
            session_id: child_session_id,
            sender_id: self.sender_id,
            receiver_id: self.receiver_id,
            slice_seeds,
            batch_ctr: 0,
        }
    }
}

impl Drop for OtExtReceiverChannel {
    fn drop(&mut self) {
        for slice in self.slice_seeds.iter_mut() {
            for s in slice.iter_mut() {
                wipe_bytes32(s);
            }
        }
    }
}

/// Execute the full committed-CRS + OR-Sigma ZKPoK + 512-branch FO + 4-ciphertext `512 -> 256`
/// parity combiner + $\mathbb{F}_4$ GGM slice puncture handshake over explicit per-party wire messages.
pub fn try_establish_rlwe_ot_ext_channel(
    session_id: [u8; 32],
    sender_id: usize,
    receiver_id: usize,
    sender_rng: &mut PartyPrivateRng,
    receiver_rng: &mut PartyPrivateRng,
) -> Result<(OtExtSenderChannel, OtExtReceiverChannel), PreprocessError> {
    let (crs_r0, crs_com) =
        BaseOtCrsReceiverRound0::commit(session_id, sender_id, receiver_id, receiver_rng);
    let (crs_s0, crs_sh) =
        BaseOtCrsSenderRound0::respond(session_id, sender_id, receiver_id, &crs_com, sender_rng);
    let (r_crs_coin, crs_open) = crs_r0.open_and_derive_crs_coin(&crs_sh);
    let s_crs_coin = crs_s0.verify_and_derive_crs_coin(&crs_open)?;

    let (s_r1, msg1) = BaseOtExtSenderRound1::start_with_crs(
        s_crs_coin,
        session_id,
        sender_id,
        receiver_id,
        sender_rng,
    );
    let (r_r2, msg2) = BaseOtExtReceiverRound2::respond_with_crs(
        r_crs_coin,
        session_id,
        sender_id,
        receiver_id,
        &msg1,
        receiver_rng,
    )?;
    let (s_r3, msg3) = s_r1.verify_fo_and_respond_coin(&msg2, sender_rng)?;
    let (r_chan, msg4) = r_r2.finalize(&msg3);
    let s_chan = s_r3.finalize(&msg4)?;
    Ok((s_chan, r_chan))
}

/// Ideal base-OT functionality for unit tests of the OT extension and its
/// consumers. Production never compiles this constructor. Base proofs, FO,
/// committed CRS and SoftSpokenOT attacks also have a real default end-to-end regression.
#[cfg(test)]
pub(super) fn establish_ideal_ot_ext_channel_for_test(
    session_id: [u8; 32],
    sender_id: usize,
    receiver_id: usize,
    sender_rng: &mut PartyPrivateRng,
    receiver_rng: &mut PartyPrivateRng,
) -> (OtExtSenderChannel, OtExtReceiverChannel) {
    let delta = [
        u128::from(sender_rng.next_u64()) | (u128::from(sender_rng.next_u64()) << 64),
        u128::from(sender_rng.next_u64()) | (u128::from(sender_rng.next_u64()) << 64),
    ];
    let mut slice_seeds = Box::new([[[0u8; 32]; 4]; OT_EXT_F4_SLICES]);
    let mut punctured_seeds = Box::new([[[0u8; 32]; 4]; OT_EXT_F4_SLICES]);
    for j in 0..OT_EXT_F4_SLICES {
        for v in 0..4usize {
            slice_seeds[j][v] = receiver_rng.next_bytes32();
        }
        punctured_seeds[j] = slice_seeds[j];
        let b0 = ((delta[0] >> j) & 1) as u8;
        let b1 = ((delta[1] >> j) & 1) as u8;
        softspoken_f4_zero_punctured_slot_ct(&mut punctured_seeds[j], b0, b1);
    }
    (
        OtExtSenderChannel {
            session_id,
            sender_id,
            receiver_id,
            delta,
            punctured_seeds,
            batch_ctr: 0,
            poisoned: alloc::sync::Arc::new(core::sync::atomic::AtomicBool::new(false)),
        },
        OtExtReceiverChannel {
            session_id,
            sender_id,
            receiver_id,
            slice_seeds,
            batch_ctr: 0,
        },
    )
}

/// Fallible full-protocol bootstrap; identical in production and test builds.
pub fn establish_rlwe_ot_ext_channel(
    session_id: [u8; 32],
    sender_id: usize,
    receiver_id: usize,
    sender_rng: &mut PartyPrivateRng,
    receiver_rng: &mut PartyPrivateRng,
) -> Result<(OtExtSenderChannel, OtExtReceiverChannel), PreprocessError> {
    try_establish_rlwe_ot_ext_channel(session_id, sender_id, receiver_id, sender_rng, receiver_rng)
}

/// Interactive KOS OT-Extension Message 1 (`OT Receiver -> OT Sender`: locks `128` parity-combined
/// `u_cols` BEFORE Sender samples `chi_seed`!).
#[derive(Clone, Debug)]
pub struct KosOtUColsMsg {
    /// `128` active-secure combined bit-columns of length `padded_words` (`payload_words + 4` sacrificial words = +256 OTs).
    pub u_cols: Vec<Vec<u64>>,
}

/// Interactive KOS OT-Extension Message 2 (`OT Sender -> OT Receiver`: fresh 256-bit random challenge seed!).
#[derive(Clone, Copy, Debug)]
pub struct KosOtChallengeMsg {
    pub chi_seed: [u8; 32],
}

/// Interactive `SoftSpokenOT (n_C = 256, k = 2)` Message 3 (`OT Receiver -> OT Sender`):
/// `[X | I_256]` polynomial-basis $\mathbb{F}_{2^{128}}^2$ hash of the choice vector `x_hash` and
/// all `256` individual column hashes `t_hash` (Roy `CRYPTO 2022` Fig. 9).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OtExtProofMsg {
    pub x_hash: [u128; 2],
    pub t_hash: Box<[[u128; 2]; OT_EXT_SUBSPACE_BITS]>,
}

/// Wire-type alias preserving source compatibility across downstream crates.
pub type KosOtProofMsg = OtExtProofMsg;
impl KosOtUColsMsg {
    /// Canonical byte serialization (`padded_words_be32` + `128 * padded_words` LE `u64`s).
    pub fn to_bytes(&self) -> Vec<u8> {
        let padded_words = self.u_cols.first().map_or(0, Vec::len);
        let mut out = Vec::with_capacity(4 + self.u_cols.len() * padded_words * 8);
        out.extend_from_slice(&(padded_words as u32).to_be_bytes());
        for col in &self.u_cols {
            for &w in col {
                out.extend_from_slice(&w.to_le_bytes());
            }
        }
        out
    }

    /// Strict canonical decoder.
    pub fn from_bytes(raw: &[u8]) -> Option<Self> {
        if raw.len() < 4 {
            return None;
        }
        let padded_words = u32::from_be_bytes(raw[0..4].try_into().ok()?) as usize;
        if padded_words < 4 {
            return None;
        }
        let mut pos = 4usize;
        validate_frame_count(padded_words, 128 * 8, raw.len() - pos).ok()?;
        if raw.len() - pos != 128 * padded_words * 8 {
            return None;
        }
        let mut u_cols = Vec::with_capacity(128);
        for _ in 0..128 {
            let mut col = Vec::with_capacity(padded_words);
            for _ in 0..padded_words {
                let b: [u8; 8] = raw[pos..pos + 8].try_into().ok()?;
                pos += 8;
                col.push(u64::from_le_bytes(b));
            }
            u_cols.push(col);
        }
        Some(Self { u_cols })
    }
}

impl KosOtChallengeMsg {
    pub fn to_bytes(&self) -> [u8; 32] {
        self.chi_seed
    }

    pub fn from_bytes(raw: &[u8]) -> Option<Self> {
        let chi_seed: [u8; 32] = raw.try_into().ok()?;
        Some(Self { chi_seed })
    }
}

impl OtExtProofMsg {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(OT_EXT_PROOF_BYTES);
        out.extend_from_slice(&self.x_hash[0].to_le_bytes());
        out.extend_from_slice(&self.x_hash[1].to_le_bytes());
        for entry in self.t_hash.iter() {
            out.extend_from_slice(&entry[0].to_le_bytes());
            out.extend_from_slice(&entry[1].to_le_bytes());
        }
        out
    }

    pub fn from_bytes(raw: &[u8]) -> Option<Self> {
        if raw.len() != OT_EXT_PROOF_BYTES {
            return None;
        }
        let entry = |i: usize| -> [u128; 2] {
            core::array::from_fn(|lane| {
                let o = 32 * i + 16 * lane;
                u128::from_le_bytes(core::array::from_fn(|b| raw[o + b]))
            })
        };
        Some(Self {
            x_hash: entry(0),
            t_hash: Box::new(core::array::from_fn(|c| entry(c + 1))),
        })
    }
}

/// Polynomial-basis $\mathbb{F}_{2^{128}}^2$ universal linear hash $H = [X \mid I_{256}]$ of
/// Roy (`CRYPTO 2022` / `ePrint 2022/192` Def. 4.1 & Fig. 9).
///
/// Evaluates $P_v(s_\ell) = \bigoplus_{k=0}^{B-1} v_k \cdot s_\ell^{k+1}$ over
/// $\mathbb{F}_2\[z\]/(z^{128} + z^7 + z^2 + z + 1)$ at two independent points $(s_0, s_1)$ and
/// XORs with the 256-bit sacrificial tail `(tail_0, tail_1)`, achieving $\epsilon \le (B / 2^{128})^2$
/// almost-universality (`< 2^{-230}` per frame) and exact one-time-pad hiding of all payload bits.
pub struct OtExtCheckKey {
    payload_words: usize,
    powers: [Vec<u128>; 2],
}

impl OtExtCheckKey {
    pub fn new(chi_seed: &[u8; 32], payload_words: usize) -> Self {
        let blocks = payload_words.div_ceil(2);
        let powers = core::array::from_fn(|lane| {
            let point = u128::from_le_bytes(core::array::from_fn(|i| chi_seed[16 * lane + i]));
            let mut cur = point;
            let mut powers = Vec::with_capacity(blocks);
            for _ in 0..blocks {
                powers.push(cur);
                cur = qsag_asm::gf2_128_dot(
                    core::slice::from_ref(&cur),
                    core::slice::from_ref(&point),
                );
            }
            powers
        });
        Self {
            payload_words,
            powers,
        }
    }

    #[inline]
    pub fn payload_words(&self) -> usize {
        self.payload_words
    }

    /// Hash one bit-column of length `payload_words + 4` `u64` words in constant time.
    pub fn hash(&self, col: &[u64]) -> [u128; 2] {
        let pw = self.payload_words;
        assert_eq!(col.len(), pw + 4);
        let blocks = pw.div_ceil(2);
        let mut packed = SecretBuffer(vec![0u128; blocks]);
        for k in 0..blocks {
            let lo = col[2 * k] as u128;
            let hi = if 2 * k + 1 < pw {
                (col[2 * k + 1] as u128) << 64
            } else {
                0
            };
            packed[k] = lo | hi;
        }
        let tail0 = (col[pw] as u128) | ((col[pw + 1] as u128) << 64);
        let tail1 = (col[pw + 2] as u128) | ((col[pw + 3] as u128) << 64);
        let h0 = if blocks == 0 {
            tail0
        } else {
            qsag_asm::gf2_128_dot(&packed, &self.powers[0]) ^ tail0
        };
        let h1 = if blocks == 0 {
            tail1
        } else {
            qsag_asm::gf2_128_dot(&packed, &self.powers[1]) ^ tail1
        };
        [h0, h1]
    }
}

/// Ephemeral Receiver state awaiting `KosOtChallengeMsg` (`!Clone`, wiped on `Drop`).
pub struct KosOtReceiverPending {
    pub(super) batch_ctr: u64,
    payload_words: usize,
    full_choices: Vec<u64>,
    t_cols: Vec<Vec<u64>>,
    pub(super) u_cols_digest: [u8; 32],
}

impl Drop for KosOtReceiverPending {
    fn drop(&mut self) {
        wipe_u64s(&mut self.full_choices);
        for col in &mut self.t_cols {
            wipe_u64s(col);
        }
    }
}

/// Ephemeral Sender state awaiting `KosOtProofMsg` (`!Clone`, wiped on `Drop`).
pub struct KosOtSenderPending {
    batch_ctr: u64,
    q_rows_lo: Vec<u128>,
    q_rows_hi: Vec<u128>,
    q_hash: Box<[[u128; 2]; OT_EXT_SUBSPACE_BITS]>,
    pub(super) u_cols_digest: [u8; 32],
    pub(super) chi_seed: [u8; 32],
}

impl Drop for KosOtSenderPending {
    fn drop(&mut self) {
        wipe_u128s(&mut self.q_rows_lo);
        wipe_u128s(&mut self.q_rows_hi);
        for h in self.q_hash.iter_mut() {
            wipe_u128s(h);
        }
    }
}

#[inline]
fn expand_prg_columns_8x_u64s(
    session_id: &[u8; 32],
    batch_ctr: u64,
    base_col_idx: usize,
    seeds: [&[u8; 32]; 8],
    num_words: usize,
) -> [Vec<u64>; 8] {
    const OT_EXT_COL_V2_MID: [u64; 25] =
        crate::sponge::keccak::cshake256_static_midstate(b"QSAG.OT.EXT.COL/v2");
    let mut hdrs = SecretBuffer([[0u8; 80]; 8]);
    let b_be = batch_ctr.to_be_bytes();
    for lane in 0..8 {
        hdrs[lane][0..32].copy_from_slice(session_id);
        hdrs[lane][32..40].copy_from_slice(&b_be);
        hdrs[lane][40..48].copy_from_slice(&((base_col_idx + lane) as u64).to_be_bytes());
        hdrs[lane][48..80].copy_from_slice(seeds[lane]);
    }
    let mut out: [Vec<u64>; 8] = core::array::from_fn(|_| vec![0u64; num_words]);
    let [o0, o1, o2, o3, o4, o5, o6, o7] = &mut out;
    let inputs: [&[u8]; 8] = core::array::from_fn(|i| &hdrs[i][..]);
    let mut outs: [&mut [u64]; 8] = [o0, o1, o2, o3, o4, o5, o6, o7];
    crate::sponge::keccak::cshake256_8x_squeeze_u64s(&OT_EXT_COL_V2_MID, inputs, &mut outs);
    out
}

/// Transpose 128 bit-columns of `num_words` `u64`s into `64 * num_words` `u128` rows.
pub(super) fn transpose_cols128_to_rows(cols: &[Vec<u64>], num_words: usize) -> Vec<u128> {
    debug_assert_eq!(cols.len(), 128);
    let total_rows = 64 * num_words;
    let mut rows = vec![0u128; total_rows];
    for w in 0..num_words {
        for half in 0..2 {
            let mut tile: [u64; 64] = core::array::from_fn(|i| cols[64 * half + i][w]);
            for (stage, mask) in [
                0x5555_5555_5555_5555u64,
                0x3333_3333_3333_3333,
                0x0f0f_0f0f_0f0f_0f0f,
                0x00ff_00ff_00ff_00ff,
                0x0000_ffff_0000_ffff,
                0x0000_0000_ffff_ffff,
            ]
            .into_iter()
            .enumerate()
            {
                let shift = 1usize << stage;
                for base in (0..64).step_by(2 * shift) {
                    for offset in 0..shift {
                        let a = base + offset;
                        let b = a + shift;
                        let delta = ((tile[a] >> shift) ^ tile[b]) & mask;
                        tile[a] ^= delta << shift;
                        tile[b] ^= delta;
                    }
                }
            }
            for i in 0..64 {
                rows[64 * w + i] |= (tile[i] as u128) << (64 * half);
            }
            wipe_u64s(&mut tile);
        }
    }
    rows
}

pub(super) fn hash_kos_u_cols(
    session_id: &[u8; 32],
    sender_id: usize,
    receiver_id: usize,
    batch_ctr: u64,
    u_cols: &[Vec<u64>],
) -> [u8; 32] {
    let mut xof = Cshake256Xof::new(b"QSAG.OT.KOS.UCOLS/v2");
    xof.absorb(session_id);
    xof.absorb(&(sender_id as u64).to_be_bytes());
    xof.absorb(&(receiver_id as u64).to_be_bytes());
    xof.absorb(&batch_ctr.to_be_bytes());
    xof.absorb(&(u_cols.len() as u64).to_be_bytes());
    for col in u_cols {
        xof.absorb(&(col.len() as u64).to_be_bytes());
        for &w in col {
            xof.absorb(&w.to_le_bytes());
        }
    }
    let mut out = [0u8; 32];
    xof.squeeze(&mut out);
    out
}

pub(super) fn compute_kos_transcript_bind(
    u_cols_digest: &[u8; 32],
    chi_seed: &[u8; 32],
    proof: &KosOtProofMsg,
) -> [u8; 32] {
    let proof_bytes = proof.to_bytes();
    cshake256_32_multi_frame(
        b"QSAG.OT.KOS.BIND/v2",
        &[u_cols_digest, chi_seed, &proof_bytes],
    )
}

/// Fast 4-way SIMD (`keccak_f1600_x4`) single-block `SHAKE256` transcript-bound correlation-robust
/// hash batch over 256-bit receiver rows `(t_rows_lo[ell], t_rows_hi[ell])` (`128`-bit PQ Grover security).
fn crh_ot_receiver_pads_batch(
    session_id: &[u8; 32],
    transcript_bind: &[u8; 32],
    sender_id: usize,
    receiver_id: usize,
    batch_ctr: u64,
    t_rows_lo: &[u128],
    t_rows_hi: &[u128],
) -> Vec<[u8; 48]> {
    let payload_rows = t_rows_lo.len();
    assert_eq!(payload_rows, t_rows_hi.len());
    let mut pads = vec![[0u8; 48]; payload_rows];
    if payload_rows == 0 {
        return pads;
    }
    assert!(sender_id < 65536 && receiver_id < 65536 && payload_rows <= (u32::MAX as usize));
    let role_prefix = ((sender_id as u64) << 48) | ((receiver_id as u64) << 32);
    let sid_words: [u64; 4] = core::array::from_fn(|i| {
        let o = 8 * i;
        u64::from_le_bytes(core::array::from_fn(|b| session_id[o + b]))
    });
    let bind_words: [u64; 4] = core::array::from_fn(|i| {
        let o = 8 * i;
        u64::from_le_bytes(core::array::from_fn(|b| transcript_bind[o + b]))
    });
    let backend = qsag_asm::detect_backend();

    let eval_range =
        |base_ell: usize, lo_slice: &[u128], hi_slice: &[u128], out_slice: &mut [[u8; 48]]| {
            let w0 = [u64::from_le_bytes(*b"QSAG.CRH"); 4];
            let w1 = [u64::from_le_bytes(*b".OT.V002"); 4];
            let mut st = qsag_asm::KeccakState4x::default();
            for (chunk_idx, ((lo_chunk, hi_chunk), o_chunk)) in lo_slice
                .chunks(4)
                .zip(hi_slice.chunks(4))
                .zip(out_slice.chunks_mut(4))
                .enumerate()
            {
                st.0 = [[0u64; 4]; 25];
                st.0[0] = w0;
                st.0[1] = w1;
                for i in 0..4 {
                    st.0[2 + i] = [sid_words[i]; 4];
                    st.0[6 + i] = [bind_words[i]; 4];
                }
                st.0[11] = [batch_ctr; 4];
                for (slot, (&r_lo, &r_hi)) in lo_chunk.iter().zip(hi_chunk.iter()).enumerate() {
                    let ell = (base_ell + 4 * chunk_idx + slot) as u64;
                    st.0[10][slot] = role_prefix | ell;
                    st.0[12][slot] = r_lo as u64;
                    st.0[13][slot] = (r_lo >> 64) as u64;
                    st.0[14][slot] = r_hi as u64;
                    st.0[15][slot] = (r_hi >> 64) as u64;
                }
                st.0[16] = [0x8000_0000_0000_001f; 4];
                qsag_asm::keccak_f1600_x4_with_backend(&mut st, backend);
                for (slot, dst) in o_chunk.iter_mut().enumerate() {
                    for w in 0..6 {
                        dst[8 * w..8 * w + 8].copy_from_slice(&st.0[w][slot].to_le_bytes());
                    }
                }
            }
            qsag_asm::volatile_fill(&mut st.0, [0u64; 4]);
        };

    #[cfg(any(test, feature = "std"))]
    if payload_rows >= 2048 {
        let workers = std::thread::available_parallelism()
            .map_or(1, usize::from)
            .min(16);
        let chunk_len = PublicDivisor::new(workers).ceil(payload_rows).max(64);
        std::thread::scope(|scope| {
            for (index, o_sub) in pads.chunks_mut(chunk_len).enumerate() {
                let base_ell = index * chunk_len;
                let range = base_ell..base_ell + o_sub.len();
                let (lo_sub, hi_sub) = (&t_rows_lo[range.clone()], &t_rows_hi[range]);
                scope.spawn(move || eval_range(base_ell, lo_sub, hi_sub, o_sub));
            }
        });
        return pads;
    }
    eval_range(0, t_rows_lo, t_rows_hi, &mut pads);
    pads
}

/// Fast 4-way SIMD (`keccak_f1600_x4`) single-block `SHAKE256` transcript-bound correlation-robust
/// hash batch over 256-bit sender row pairs `(q_row, q_row ^ delta)` (`128`-bit PQ Grover security).
#[allow(clippy::too_many_arguments)]
fn crh_ot_sender_pad_pairs_batch(
    session_id: &[u8; 32],
    transcript_bind: &[u8; 32],
    sender_id: usize,
    receiver_id: usize,
    batch_ctr: u64,
    delta: [u128; 2],
    q_rows_lo: &[u128],
    q_rows_hi: &[u128],
) -> Vec<OtPadPair> {
    let payload_rows = q_rows_lo.len();
    assert_eq!(payload_rows, q_rows_hi.len());
    let mut pad_pairs = vec![([0u8; 48], [0u8; 48]); payload_rows];
    if payload_rows == 0 {
        return pad_pairs;
    }
    assert!(sender_id < 65536 && receiver_id < 65536 && payload_rows <= (u32::MAX as usize));
    let role_prefix = ((sender_id as u64) << 48) | ((receiver_id as u64) << 32);
    let sid_words: [u64; 4] = core::array::from_fn(|i| {
        let o = 8 * i;
        u64::from_le_bytes(core::array::from_fn(|b| session_id[o + b]))
    });
    let bind_words: [u64; 4] = core::array::from_fn(|i| {
        let o = 8 * i;
        u64::from_le_bytes(core::array::from_fn(|b| transcript_bind[o + b]))
    });
    let backend = qsag_asm::detect_backend();

    let eval_range =
        |base_ell: usize, lo_slice: &[u128], hi_slice: &[u128], out_slice: &mut [OtPadPair]| {
            let w0 = [u64::from_le_bytes(*b"QSAG.CRH"); 4];
            let w1 = [u64::from_le_bytes(*b".OT.V002"); 4];
            let mut st = qsag_asm::KeccakState4x::default();
            for (pair_idx, ((lo_chunk, hi_chunk), o_chunk)) in lo_slice
                .chunks(2)
                .zip(hi_slice.chunks(2))
                .zip(out_slice.chunks_mut(2))
                .enumerate()
            {
                st.0 = [[0u64; 4]; 25];
                st.0[0] = w0;
                st.0[1] = w1;
                for i in 0..4 {
                    st.0[2 + i] = [sid_words[i]; 4];
                    st.0[6 + i] = [bind_words[i]; 4];
                }
                st.0[11] = [batch_ctr; 4];
                for (sub, (&q_lo, &q_hi)) in lo_chunk.iter().zip(hi_chunk.iter()).enumerate() {
                    let ell = (base_ell + 2 * pair_idx + sub) as u64;
                    let q1_lo = q_lo ^ delta[0];
                    let q1_hi = q_hi ^ delta[1];
                    st.0[10][2 * sub] = role_prefix | ell;
                    st.0[12][2 * sub] = q_lo as u64;
                    st.0[13][2 * sub] = (q_lo >> 64) as u64;
                    st.0[14][2 * sub] = q_hi as u64;
                    st.0[15][2 * sub] = (q_hi >> 64) as u64;
                    st.0[10][2 * sub + 1] = role_prefix | ell;
                    st.0[12][2 * sub + 1] = q1_lo as u64;
                    st.0[13][2 * sub + 1] = (q1_lo >> 64) as u64;
                    st.0[14][2 * sub + 1] = q1_hi as u64;
                    st.0[15][2 * sub + 1] = (q1_hi >> 64) as u64;
                }
                st.0[16] = [0x8000_0000_0000_001f; 4];
                qsag_asm::keccak_f1600_x4_with_backend(&mut st, backend);
                for (sub, (p0, p1)) in o_chunk.iter_mut().enumerate() {
                    for w in 0..6 {
                        p0[8 * w..8 * w + 8].copy_from_slice(&st.0[w][2 * sub].to_le_bytes());
                        p1[8 * w..8 * w + 8].copy_from_slice(&st.0[w][2 * sub + 1].to_le_bytes());
                    }
                }
            }
            qsag_asm::volatile_fill(&mut st.0, [0u64; 4]);
        };

    #[cfg(any(test, feature = "std"))]
    if payload_rows >= 1024 {
        let workers = std::thread::available_parallelism()
            .map_or(1, usize::from)
            .min(16);
        let chunk_len = PublicDivisor::new(workers).ceil(payload_rows).max(64);
        std::thread::scope(|scope| {
            for (index, o_sub) in pad_pairs.chunks_mut(chunk_len).enumerate() {
                let base_ell = index * chunk_len;
                let range = base_ell..base_ell + o_sub.len();
                let (lo_sub, hi_sub) = (&q_rows_lo[range.clone()], &q_rows_hi[range]);
                scope.spawn(move || eval_range(base_ell, lo_sub, hi_sub, o_sub));
            }
        });
        return pad_pairs;
    }
    eval_range(0, q_rows_lo, q_rows_hi, &mut pad_pairs);
    pad_pairs
}

/// Pre-challenge transcript mask XORed with the fresh post-`u_cols` `chi_seed` (`chi_seed ^ mask`
/// is an information-theoretically uniform bijection over $\mathbb{F}_{2^{128}}^2$!).
pub(super) fn derive_ot_ext_check_seed(
    session_id: &[u8; 32],
    sender_id: usize,
    receiver_id: usize,
    batch_ctr: u64,
    u_cols_digest: &[u8; 32],
    chi_seed: &[u8; 32],
) -> [u8; 32] {
    let mut xof = Cshake256Xof::new(b"QSAG.OT.KOS.ICHAL/v2");
    xof.absorb(session_id);
    xof.absorb(&(sender_id as u64).to_be_bytes());
    xof.absorb(&(receiver_id as u64).to_be_bytes());
    xof.absorb(&batch_ctr.to_be_bytes());
    xof.absorb(u_cols_digest);
    let mut mask = [0u8; 32];
    xof.squeeze(&mut mask);
    for (m, &c) in mask.iter_mut().zip(chi_seed.iter()) {
        *m ^= c;
    }
    mask
}

impl OtExtReceiverChannel {
    /// Interactive `SoftSpokenOT (n_C = 256, k = 2)` Step 1 (`OT Receiver -> OT Sender`): append
    /// 256 sacrificial random OTs, expand `128` $\mathbb{F}_4$ GGM slices (`512` streams -> `128`
    /// wire `u_cols` and `256` `t_cols`), lock `KosOtUColsMsg` **before** seeing Sender's `chi_seed`,
    /// and retain `KosOtReceiverPending`.
    pub fn round1_send_u_cols(
        &mut self,
        choice_words: &[u64],
        rng: &mut PartyPrivateRng,
    ) -> (KosOtReceiverPending, KosOtUColsMsg) {
        assert!(
            self.batch_ctr < u64::MAX,
            "OtExtReceiverChannel batch counter exhausted"
        );
        let sac_words = [
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
        ];
        self.round1_send_u_cols_with_sac(choice_words, sac_words)
    }

    pub(crate) fn round1_send_u_cols_with_sac(
        &mut self,
        choice_words: &[u64],
        sac_words: [u64; 4],
    ) -> (KosOtReceiverPending, KosOtUColsMsg) {
        assert!(
            self.batch_ctr < u64::MAX,
            "OtExtReceiverChannel batch counter exhausted"
        );
        let payload_words = choice_words.len();
        let padded_words = payload_words + 4;
        let batch_ctr = self.batch_ctr;
        self.batch_ctr += 1;

        let mut full_choices = Vec::with_capacity(padded_words);
        full_choices.extend_from_slice(choice_words);
        full_choices.extend_from_slice(&sac_words);

        let mut t_lo_cols = vec![Vec::new(); OT_EXT_F4_SLICES];
        let mut t_hi_cols = vec![Vec::new(); OT_EXT_F4_SLICES];
        let mut u_cols = vec![Vec::new(); OT_EXT_F4_SLICES];

        let fill_slice_pair = |sid: &[u8; 32],
                               slices: &[[[u8; 32]; 4]; OT_EXT_F4_SLICES],
                               choices_ref: &[u64],
                               base_j: usize,
                               t_lo_sub: &mut [Vec<u64>],
                               t_hi_sub: &mut [Vec<u64>],
                               u_sub: &mut [Vec<u64>]| {
            let s_refs: [&[u8; 32]; 8] = core::array::from_fn(|k| &slices[base_j + (k / 4)][k % 4]);
            let mut g_batch =
                expand_prg_columns_8x_u64s(sid, batch_ctr, 4 * base_j, s_refs, padded_words);
            for sub in 0..2 {
                let off = 4 * sub;
                let mut t_lo = vec![0u64; padded_words];
                let mut t_hi = vec![0u64; padded_words];
                let mut u = vec![0u64; padded_words];
                for w in 0..padded_words {
                    let g0 = g_batch[off][w];
                    let g1 = g_batch[off + 1][w];
                    let g2 = g_batch[off + 2][w];
                    let g3 = g_batch[off + 3][w];
                    t_lo[w] = g2 ^ g3;
                    t_hi[w] = g1 ^ g3;
                    u[w] = g0 ^ g1 ^ g2 ^ g3 ^ choices_ref[w];
                }
                for l in 0..4 {
                    wipe_u64s(&mut g_batch[off + l]);
                }
                t_lo_sub[sub] = t_lo;
                t_hi_sub[sub] = t_hi;
                u_sub[sub] = u;
            }
        };

        #[cfg(any(test, feature = "std"))]
        if padded_words >= 64 {
            let sid = &self.session_id;
            let slices = &*self.slice_seeds;
            let choices_ref = &full_choices;
            std::thread::scope(|scope| {
                for (c_idx, ((t_lo_sub, t_hi_sub), u_sub)) in t_lo_cols
                    .chunks_mut(16)
                    .zip(t_hi_cols.chunks_mut(16))
                    .zip(u_cols.chunks_mut(16))
                    .enumerate()
                {
                    let base_j = 16 * c_idx;
                    scope.spawn(move || {
                        for pair in 0..8 {
                            let o = 2 * pair;
                            fill_slice_pair(
                                sid,
                                slices,
                                choices_ref,
                                base_j + o,
                                &mut t_lo_sub[o..o + 2],
                                &mut t_hi_sub[o..o + 2],
                                &mut u_sub[o..o + 2],
                            );
                        }
                    });
                }
            });
        } else {
            for pair in 0..(OT_EXT_F4_SLICES / 2) {
                let base_j = 2 * pair;
                fill_slice_pair(
                    &self.session_id,
                    &self.slice_seeds,
                    &full_choices,
                    base_j,
                    &mut t_lo_cols[base_j..base_j + 2],
                    &mut t_hi_cols[base_j..base_j + 2],
                    &mut u_cols[base_j..base_j + 2],
                );
            }
        }
        #[cfg(not(any(test, feature = "std")))]
        for pair in 0..(OT_EXT_F4_SLICES / 2) {
            let base_j = 2 * pair;
            fill_slice_pair(
                &self.session_id,
                &self.slice_seeds,
                &full_choices,
                base_j,
                &mut t_lo_cols[base_j..base_j + 2],
                &mut t_hi_cols[base_j..base_j + 2],
                &mut u_cols[base_j..base_j + 2],
            );
        }

        let mut t_cols = Vec::with_capacity(OT_EXT_SUBSPACE_BITS);
        t_cols.extend(t_lo_cols);
        t_cols.extend(t_hi_cols);

        let u_cols_digest = hash_kos_u_cols(
            &self.session_id,
            self.sender_id,
            self.receiver_id,
            batch_ctr,
            &u_cols,
        );
        (
            KosOtReceiverPending {
                batch_ctr,
                payload_words,
                full_choices,
                t_cols,
                u_cols_digest,
            },
            KosOtUColsMsg { u_cols },
        )
    }

    /// Interactive `SoftSpokenOT (n_C = 256, k = 2)` Step 3 (`OT Receiver -> OT Sender`): evaluate
    /// [`OtExtCheckKey`] (`[X | I_256]`) on `full_choices` and all `256` columns individually, and
    /// derive 256-bit transcript-bound receiver pads.
    pub fn round3_prove_and_finish(
        &self,
        mut pending: KosOtReceiverPending,
        chal: &KosOtChallengeMsg,
    ) -> (KosOtProofMsg, Vec<[u8; 48]>) {
        let mut check_seed = derive_ot_ext_check_seed(
            &self.session_id,
            self.sender_id,
            self.receiver_id,
            pending.batch_ctr,
            &pending.u_cols_digest,
            &chal.chi_seed,
        );
        let key = OtExtCheckKey::new(&check_seed, pending.payload_words);
        wipe_bytes32(&mut check_seed);

        let proof = OtExtProofMsg {
            x_hash: key.hash(&pending.full_choices),
            t_hash: Box::new(core::array::from_fn(|col| key.hash(&pending.t_cols[col]))),
        };
        wipe_u64s(&mut pending.full_choices);

        let bind = compute_kos_transcript_bind(&pending.u_cols_digest, &chal.chi_seed, &proof);
        let mut t_rows_lo =
            transpose_cols128_to_rows(&pending.t_cols[..OT_EXT_F4_SLICES], pending.payload_words);
        let mut t_rows_hi =
            transpose_cols128_to_rows(&pending.t_cols[OT_EXT_F4_SLICES..], pending.payload_words);
        for col in &mut pending.t_cols {
            wipe_u64s(col);
        }
        let pads = crh_ot_receiver_pads_batch(
            &self.session_id,
            &bind,
            self.sender_id,
            self.receiver_id,
            pending.batch_ctr,
            &t_rows_lo,
            &t_rows_hi,
        );
        wipe_u128s(&mut t_rows_lo);
        wipe_u128s(&mut t_rows_hi);
        (proof, pads)
    }
}

impl OtExtSenderChannel {
    /// Interactive `SoftSpokenOT (n_C = 256, k = 2)` Step 2 (`OT Sender -> OT Receiver`): validate
    /// 128-column `KosOtUColsMsg`, expand `256` `q_cols`, and sample a **fresh** 256-bit `chi_seed`
    /// *after* `u_cols` is locked.
    pub fn round2_sample_challenge(
        &mut self,
        u_msg: &KosOtUColsMsg,
        sender_rng: &mut PartyPrivateRng,
    ) -> Result<(KosOtSenderPending, KosOtChallengeMsg), PreprocessError> {
        if self.is_poisoned() {
            self.wipe_local_secrets();
            return Err(PreprocessError::ChannelPoisoned {
                sender_id: self.sender_id,
                receiver_id: self.receiver_id,
            });
        }
        if self.batch_ctr == u64::MAX {
            self.poison_and_wipe();
            return Err(PreprocessError::ChannelPoisoned {
                sender_id: self.sender_id,
                receiver_id: self.receiver_id,
            });
        }
        if u_msg.u_cols.len() != OT_EXT_F4_SLICES {
            self.poison_and_wipe();
            return Err(PreprocessError::KosOtCheckFailed {
                sender_id: self.sender_id,
                receiver_id: self.receiver_id,
            });
        }
        let padded_words = u_msg.u_cols[0].len();
        if padded_words < 4
            || validate_frame_count(padded_words, OT_EXT_F4_SLICES * 8, MAX_FRAME_BUDGET).is_err()
            || u_msg.u_cols.iter().any(|c| c.len() != padded_words)
        {
            self.poison_and_wipe();
            return Err(PreprocessError::KosOtCheckFailed {
                sender_id: self.sender_id,
                receiver_id: self.receiver_id,
            });
        }
        let payload_words = padded_words - 4;
        let batch_ctr = self.batch_ctr;
        self.batch_ctr += 1;
        let chi_seed = sender_rng.next_bytes32();
        self.round2_sample_challenge_with_chi_inner(
            batch_ctr,
            payload_words,
            padded_words,
            u_msg,
            chi_seed,
        )
    }

    pub(crate) fn round2_sample_challenge_with_chi(
        &mut self,
        u_msg: &KosOtUColsMsg,
        chi_seed: [u8; 32],
    ) -> Result<(KosOtSenderPending, KosOtChallengeMsg), PreprocessError> {
        if self.is_poisoned() {
            self.wipe_local_secrets();
            return Err(PreprocessError::ChannelPoisoned {
                sender_id: self.sender_id,
                receiver_id: self.receiver_id,
            });
        }
        if self.batch_ctr == u64::MAX {
            self.poison_and_wipe();
            return Err(PreprocessError::ChannelPoisoned {
                sender_id: self.sender_id,
                receiver_id: self.receiver_id,
            });
        }
        if u_msg.u_cols.len() != OT_EXT_F4_SLICES {
            self.poison_and_wipe();
            return Err(PreprocessError::KosOtCheckFailed {
                sender_id: self.sender_id,
                receiver_id: self.receiver_id,
            });
        }
        let padded_words = u_msg.u_cols[0].len();
        if padded_words < 4
            || validate_frame_count(padded_words, OT_EXT_F4_SLICES * 8, MAX_FRAME_BUDGET).is_err()
            || u_msg.u_cols.iter().any(|c| c.len() != padded_words)
        {
            self.poison_and_wipe();
            return Err(PreprocessError::KosOtCheckFailed {
                sender_id: self.sender_id,
                receiver_id: self.receiver_id,
            });
        }
        let payload_words = padded_words - 4;
        let batch_ctr = self.batch_ctr;
        self.batch_ctr += 1;
        self.round2_sample_challenge_with_chi_inner(
            batch_ctr,
            payload_words,
            padded_words,
            u_msg,
            chi_seed,
        )
    }

    fn round2_sample_challenge_with_chi_inner(
        &mut self,
        batch_ctr: u64,
        payload_words: usize,
        padded_words: usize,
        u_msg: &KosOtUColsMsg,
        chi_seed: [u8; 32],
    ) -> Result<(KosOtSenderPending, KosOtChallengeMsg), PreprocessError> {
        let mut q_lo_cols = vec![Vec::new(); OT_EXT_F4_SLICES];
        let mut q_hi_cols = vec![Vec::new(); OT_EXT_F4_SLICES];

        let fill_q_slice_pair = |sid: &[u8; 32],
                                 slices: &[[[u8; 32]; 4]; OT_EXT_F4_SLICES],
                                 delta: [u128; 2],
                                 u_cols_ref: &[Vec<u64>],
                                 base_j: usize,
                                 q_lo_sub: &mut [Vec<u64>],
                                 q_hi_sub: &mut [Vec<u64>]| {
            let s_refs: [&[u8; 32]; 8] = core::array::from_fn(|k| &slices[base_j + (k / 4)][k % 4]);
            let mut g_batch =
                expand_prg_columns_8x_u64s(sid, batch_ctr, 4 * base_j, s_refs, padded_words);
            for sub in 0..2 {
                let j = base_j + sub;
                let off = 4 * sub;
                let b0 = ((black_box(delta[0]) >> j) & 1) as u64;
                let b1 = ((black_box(delta[1]) >> j) & 1) as u64;
                let v_star = ((b0 as u8) << 1) | (b1 as u8);
                for v in 0..4usize {
                    let diff = black_box((v as u8) ^ v_star);
                    let is_neq = (((diff | diff.wrapping_neg()) >> 7) & 1) as u64;
                    let keep = 0u64.wrapping_sub(is_neq);
                    for gw in &mut g_batch[off + v] {
                        *gw &= keep;
                    }
                }
                let m0 = 0u64.wrapping_sub(b0);
                let m1 = 0u64.wrapping_sub(b1);
                let mut q_lo = vec![0u64; padded_words];
                let mut q_hi = vec![0u64; padded_words];
                let u_j = &u_cols_ref[j];
                for w in 0..padded_words {
                    let g0 = g_batch[off][w];
                    let g1 = g_batch[off + 1][w];
                    let g2 = g_batch[off + 2][w];
                    let g3 = g_batch[off + 3][w];
                    let w_corr = u_j[w] ^ g0 ^ g1 ^ g2 ^ g3;
                    q_lo[w] = g2 ^ g3 ^ (m0 & w_corr);
                    q_hi[w] = g1 ^ g3 ^ (m1 & w_corr);
                }
                for v in 0..4 {
                    wipe_u64s(&mut g_batch[off + v]);
                }
                q_lo_sub[sub] = q_lo;
                q_hi_sub[sub] = q_hi;
            }
        };

        #[cfg(any(test, feature = "std"))]
        if padded_words >= 64 {
            let sid = &self.session_id;
            let slices = &*self.punctured_seeds;
            let delta = self.delta;
            let u_cols_ref = &u_msg.u_cols;
            std::thread::scope(|scope| {
                for (c_idx, (q_lo_sub, q_hi_sub)) in q_lo_cols
                    .chunks_mut(16)
                    .zip(q_hi_cols.chunks_mut(16))
                    .enumerate()
                {
                    let base_j = 16 * c_idx;
                    scope.spawn(move || {
                        for pair in 0..8 {
                            let o = 2 * pair;
                            fill_q_slice_pair(
                                sid,
                                slices,
                                delta,
                                u_cols_ref,
                                base_j + o,
                                &mut q_lo_sub[o..o + 2],
                                &mut q_hi_sub[o..o + 2],
                            );
                        }
                    });
                }
            });
        } else {
            for pair in 0..(OT_EXT_F4_SLICES / 2) {
                let base_j = 2 * pair;
                fill_q_slice_pair(
                    &self.session_id,
                    &self.punctured_seeds,
                    self.delta,
                    &u_msg.u_cols,
                    base_j,
                    &mut q_lo_cols[base_j..base_j + 2],
                    &mut q_hi_cols[base_j..base_j + 2],
                );
            }
        }
        #[cfg(not(any(test, feature = "std")))]
        for pair in 0..(OT_EXT_F4_SLICES / 2) {
            let base_j = 2 * pair;
            fill_q_slice_pair(
                &self.session_id,
                &self.punctured_seeds,
                self.delta,
                &u_msg.u_cols,
                base_j,
                &mut q_lo_cols[base_j..base_j + 2],
                &mut q_hi_cols[base_j..base_j + 2],
            );
        }

        let u_cols_digest = hash_kos_u_cols(
            &self.session_id,
            self.sender_id,
            self.receiver_id,
            batch_ctr,
            &u_msg.u_cols,
        );
        let mut check_seed = derive_ot_ext_check_seed(
            &self.session_id,
            self.sender_id,
            self.receiver_id,
            batch_ctr,
            &u_cols_digest,
            &chi_seed,
        );
        let key = OtExtCheckKey::new(&check_seed, payload_words);
        wipe_bytes32(&mut check_seed);

        let q_hash = Box::new(core::array::from_fn(|col| {
            if col < OT_EXT_F4_SLICES {
                key.hash(&q_lo_cols[col])
            } else {
                key.hash(&q_hi_cols[col - OT_EXT_F4_SLICES])
            }
        }));
        let q_rows_lo = transpose_cols128_to_rows(&q_lo_cols, payload_words);
        let q_rows_hi = transpose_cols128_to_rows(&q_hi_cols, payload_words);
        for col in &mut q_lo_cols {
            wipe_u64s(col);
        }
        for col in &mut q_hi_cols {
            wipe_u64s(col);
        }

        Ok((
            KosOtSenderPending {
                batch_ctr,
                q_rows_lo,
                q_rows_hi,
                q_hash,
                u_cols_digest,
                chi_seed,
            },
            KosOtChallengeMsg { chi_seed },
        ))
    }

    /// Interactive `SoftSpokenOT (n_C = 256, k = 2)` Step 4 (`OT Sender` local): verify all `256`
    /// per-column `[X | I_256]` equations `H(q_c) == t_hash[c] ^ (delta_c & x_hash)` in constant
    /// time. A mismatch poisons the shared latch and erases this sender’s local seeds.
    pub fn round4_verify_and_finish(
        &mut self,
        pending: KosOtSenderPending,
        proof: &KosOtProofMsg,
    ) -> Result<Vec<OtPadPair>, PreprocessError> {
        if self.is_poisoned() {
            self.wipe_local_secrets();
            return Err(PreprocessError::ChannelPoisoned {
                sender_id: self.sender_id,
                receiver_id: self.receiver_id,
            });
        }
        let mut diff = 0u128;
        for col in 0..OT_EXT_SUBSPACE_BITS {
            let d_bit = (black_box(self.delta[col / 128]) >> (col % 128)) & 1;
            let mask = 0u128.wrapping_sub(d_bit);
            for lane in 0..2 {
                diff |= pending.q_hash[col][lane]
                    ^ proof.t_hash[col][lane]
                    ^ (mask & proof.x_hash[lane]);
            }
        }
        if black_box(diff) != 0 {
            self.poison_and_wipe();
            return Err(PreprocessError::KosOtCheckFailed {
                sender_id: self.sender_id,
                receiver_id: self.receiver_id,
            });
        }

        let bind = compute_kos_transcript_bind(&pending.u_cols_digest, &pending.chi_seed, proof);
        let pad_pairs = crh_ot_sender_pad_pairs_batch(
            &self.session_id,
            &bind,
            self.sender_id,
            self.receiver_id,
            pending.batch_ctr,
            self.delta,
            &pending.q_rows_lo,
            &pending.q_rows_hi,
        );
        // A sibling may have failed its consistency check while these pads were derived.
        if self.is_poisoned() {
            let _discard = SecretBuffer(pad_pairs);
            self.wipe_local_secrets();
            return Err(PreprocessError::ChannelPoisoned {
                sender_id: self.sender_id,
                receiver_id: self.receiver_id,
            });
        }
        Ok(pad_pairs)
    }
}

/// Full $n$-party mesh of directional Ring-LWE OT-extension channels (`n * (n - 1)` channels).
pub struct OtMesh {
    pub n: usize,
    pub session_id: [u8; 32],
    pub(super) senders: Vec<Vec<Option<OtExtSenderChannel>>>,
    pub(super) receivers: Vec<Vec<Option<OtExtReceiverChannel>>>,
    /// Chain over every extension batch run on this mesh, in the order they were run.
    pub(super) transcript: [u8; 32],
    /// Pre-staged single-use multiplicative blinding triples for retained-mesh MAC checks.
    pub(super) blind_pool: mac_blind::BlindPool,
}

type OtChannelSetup = fn(
    [u8; 32],
    usize,
    usize,
    &mut PartyPrivateRng,
    &mut PartyPrivateRng,
) -> Result<(OtExtSenderChannel, OtExtReceiverChannel), PreprocessError>;

impl OtMesh {
    /// Run committed CRS + `384` OR-Sigma ZKPoK + FO-checked Ring-LWE Base OTs + 4-ciphertext
    /// `384 -> 128` parity combiner per ordered pair `(i, j)` (`i != j`).
    pub fn try_establish(
        session_id: [u8; 32],
        party_rngs: &mut [PartyPrivateRng],
    ) -> Result<Self, PreprocessError> {
        Self::try_establish_with(session_id, party_rngs, try_establish_rlwe_ot_ext_channel)
    }

    fn try_establish_with(
        session_id: [u8; 32],
        party_rngs: &mut [PartyPrivateRng],
        setup: OtChannelSetup,
    ) -> Result<Self, PreprocessError> {
        let n = party_rngs.len();
        if n < 2 {
            return Err(PreprocessError::InvalidThreshold { t: 2, n });
        }
        let mut senders: Vec<Vec<Option<OtExtSenderChannel>>> =
            (0..n).map(|_| (0..n).map(|_| None).collect()).collect();
        let mut receivers: Vec<Vec<Option<OtExtReceiverChannel>>> =
            (0..n).map(|_| (0..n).map(|_| None).collect()).collect();

        // Each pair gets fresh private substreams before workers start. No RNG
        // or transcript is shared between threads. Limit concurrency so large
        // committees do not allocate one full base-OT handshake per edge at once.
        #[cfg(any(test, feature = "std"))]
        {
            use core::sync::atomic::{AtomicUsize, Ordering};
            use std::sync::Mutex;

            let mut job_slots = Vec::with_capacity(n * (n - 1));
            for i in 0..n {
                for j in 0..n {
                    if i == j {
                        continue;
                    }
                    let sender = PartyPrivateRng::from_seed(
                        party_rngs[i].next_bytes32(),
                        b"QSAG.OT.MESH.SENDER/v1",
                    );
                    let receiver = PartyPrivateRng::from_seed(
                        party_rngs[j].next_bytes32(),
                        b"QSAG.OT.MESH.RECEIVER/v1",
                    );
                    job_slots.push(Mutex::new(Some((i, j, sender, receiver))));
                }
            }
            type OtMeshJobOutcome = (
                usize,
                usize,
                Result<(OtExtSenderChannel, OtExtReceiverChannel), PreprocessError>,
            );
            let total_jobs = job_slots.len();
            let out_slots: Vec<Mutex<Option<OtMeshJobOutcome>>> =
                (0..total_jobs).map(|_| Mutex::new(None)).collect();
            let max_workers = BaseProofWorkers::hw_cap();
            let workers = total_jobs.min(max_workers).max(1);
            let next_idx = AtomicUsize::new(0);
            std::thread::scope(|scope| {
                let job_slots_ref = &job_slots;
                let out_slots_ref = &out_slots;
                let next_ref = &next_idx;
                for _ in 0..workers {
                    scope.spawn(move || {
                        let _guard = ActiveMeshWorkerGuard::enter();
                        loop {
                            let idx = next_ref.fetch_add(1, Ordering::Relaxed);
                            if idx >= total_jobs {
                                break;
                            }
                            let Some((i, j, mut sender, mut receiver)) =
                                job_slots_ref[idx].lock().expect("mesh job slot").take()
                            else {
                                continue;
                            };
                            let res = setup(session_id, i, j, &mut sender, &mut receiver);
                            *out_slots_ref[idx].lock().expect("mesh out slot") = Some((i, j, res));
                        }
                    });
                }
            });
            for slot in out_slots {
                let (i, j, res) = slot
                    .into_inner()
                    .map_err(|_| PreprocessError::PcgInvalidWireSeed)?
                    .ok_or(PreprocessError::PcgInvalidWireSeed)?;
                let (sender, receiver) = res?;
                senders[i][j] = Some(sender);
                receivers[j][i] = Some(receiver);
            }
        }
        #[cfg(not(any(test, feature = "std")))]
        for i in 0..n {
            for j in 0..n {
                if i == j {
                    continue;
                }
                let (s_chan, r_chan) = if i < j {
                    let (left, right) = party_rngs.split_at_mut(j);
                    setup(session_id, i, j, &mut left[i], &mut right[0])?
                } else {
                    let (left, right) = party_rngs.split_at_mut(i);
                    setup(session_id, i, j, &mut right[0], &mut left[j])?
                };
                senders[i][j] = Some(s_chan);
                receivers[j][i] = Some(r_chan);
            }
        }
        Ok(Self {
            n,
            session_id,
            senders,
            receivers,
            transcript: cshake256_32_multi_frame(
                b"QSAG.OT.MESH.TRANSCRIPT/v1",
                &[&session_id, &(n as u64).to_be_bytes()],
            ),
            blind_pool: mac_blind::BlindPool::default(),
        })
    }

    /// Digest chaining, for every correlated-OT extension batch run on this mesh so far, its
    /// direction and the binding of its three wire messages (`u` columns, challenge, proof).
    /// Callers absorb it into their own transcript so later coins depend on all OT traffic.
    pub fn transcript_digest(&self) -> [u8; 32] {
        self.transcript
    }

    pub(crate) fn absorb_batch(&mut self, sender_id: usize, receiver_id: usize, bind: &[u8; 32]) {
        let prev = self.transcript;
        self.transcript = cshake256_32_multi_frame(
            b"QSAG.OT.MESH.TRANSCRIPT/v1",
            &[
                &prev,
                &(sender_id as u64).to_be_bytes(),
                &(receiver_id as u64).to_be_bytes(),
                bind,
            ],
        );
    }

    /// Explicit ideal base OT for fast tests of downstream protocols.
    #[cfg(test)]
    pub(crate) fn establish_ideal_for_test(
        session_id: [u8; 32],
        party_rngs: &mut [PartyPrivateRng],
    ) -> Self {
        Self::try_establish_with(session_id, party_rngs, |sid, i, j, sender, receiver| {
            Ok(establish_ideal_ot_ext_channel_for_test(
                sid, i, j, sender, receiver,
            ))
        })
        .expect("ideal base-OT unit-test mesh")
    }

    /// Fallible real-protocol convenience constructor.
    pub fn establish(
        session_id: [u8; 32],
        party_rngs: &mut [PartyPrivateRng],
    ) -> Result<Self, PreprocessError> {
        Self::try_establish(session_id, party_rngs)
    }

    /// Execute an interactive 3-message KOS correlated OT batch from `sender_id` to `receiver_id`
    /// on `choice_words`, drawing `chi_seed` from `party_rngs[sender_id]` *after* `u_cols` is locked.
    pub fn run_correlated_ot_words(
        &mut self,
        sender_id: usize,
        receiver_id: usize,
        choice_words: &[u64],
        party_rngs: &mut [PartyPrivateRng],
    ) -> Result<OtBatchPads, PreprocessError> {
        if sender_id == receiver_id
            || sender_id >= self.n
            || receiver_id >= self.n
            || party_rngs.len() != self.n
        {
            return Err(PreprocessError::KosOtCheckFailed {
                sender_id,
                receiver_id,
            });
        }
        // Large local preprocessing jobs are split into independently challenged frames.
        // The peer-facing receiver keeps a strict budget even when a vault needs more OTs.
        const WORDS_PER_FRAME: usize = MAX_FRAME_BUDGET / (128 * 8) - 4;
        if choice_words.len() > WORDS_PER_FRAME {
            let (mut send, mut recv) = (OtSendPads(Vec::new()), OtRecvPads(Vec::new()));
            for choices in choice_words.chunks(WORDS_PER_FRAME) {
                let (s, r) =
                    self.run_correlated_ot_words(sender_id, receiver_id, choices, party_rngs)?;
                secret_vec_extend_from_slice(&mut send.0, &s.0);
                secret_vec_extend_from_slice(&mut recv.0, &r.0);
            }
            return Ok((send, recv));
        }
        let (sender_rng, receiver_rng) = if sender_id < receiver_id {
            let (left, right) = party_rngs.split_at_mut(receiver_id);
            (&mut left[sender_id], &mut right[0])
        } else {
            let (left, right) = party_rngs.split_at_mut(sender_id);
            (&mut right[0], &mut left[receiver_id])
        };

        let r_chan = self.receivers[receiver_id][sender_id]
            .as_mut()
            .ok_or(PreprocessError::PcgInvalidWireSeed)?;
        let s_chan = self.senders[sender_id][receiver_id]
            .as_mut()
            .ok_or(PreprocessError::PcgInvalidWireSeed)?;

        let (r_pending, u_msg) = r_chan.round1_send_u_cols(choice_words, receiver_rng);
        let (s_pending, chal_msg) = s_chan.round2_sample_challenge(&u_msg, sender_rng)?;
        let (proof_msg, recv_pads) = r_chan.round3_prove_and_finish(r_pending, &chal_msg);
        let recv_pads = OtRecvPads(recv_pads);
        let bind =
            compute_kos_transcript_bind(&s_pending.u_cols_digest, &s_pending.chi_seed, &proof_msg);
        let send_pads = OtSendPads(s_chan.round4_verify_and_finish(s_pending, &proof_msg)?);
        self.absorb_batch(sender_id, receiver_id, &bind);
        Ok((send_pads, recv_pads))
    }
}
