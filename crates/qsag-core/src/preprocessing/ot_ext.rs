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
