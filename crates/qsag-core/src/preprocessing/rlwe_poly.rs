//! Ring-LWE polynomial arithmetic, NTTs and Fujisaki–Okamoto base transfers.

use super::rlwe_proof::bounded_ternary_witness;
use super::*;

/// Ring dimension $N = 1024$ of $R_q = \mathbb{Z}_{12289}\[X\]/(X^{1024} + 1)$ (`> 200`-bit PQ Core-SVP).
pub const RLWE_N: usize = 1024;

/// Number of random-choice FO-checked Ring-LWE Base OTs combined via `[I_256 | R_{256x256}]`
/// (`512 - 256 = 256` bits of Leftover-Hash-Lemma entropy slack; joint selective-failure advantage $< 2^{-128}$).
pub const RLWE_BASE_OT_COUNT: usize = 512;

/// Number of `u64` words packing `RLWE_BASE_OT_COUNT = 512` choice bits (`8 * 64 = 512`).
pub const RLWE_BASE_OT_WORDS: usize = RLWE_BASE_OT_COUNT / 64;

/// Repetition-code blocklength / secret correlation width $n_C = d_C = 256$ of `SoftSpokenOT (k = 2)`
/// ($\Delta \in \mathbb{F}_2^{256}$: Roy `CRYPTO 2022` Thm 4.5 exact $t = 240$, $2^{-t-1} = 2^{-241}$,
/// and 128-bit post-quantum Grover resistance).
pub const OT_EXT_SUBSPACE_BITS: usize = 256;

/// Number of depth-2 GGM $\mathbb{F}_4$ (`k = 2`) 2-bit small-field VOLE slices (`256 / 2 = 128`),
/// matching the 128-column `u_cols` wire format at $1.00\times$ IKNP bandwidth.
pub const OT_EXT_F4_SLICES: usize = OT_EXT_SUBSPACE_BITS / 2;

/// Number of sacrificial extended OTs appended to every batch (`I_256` hiding block in `[X | I_256]`).
pub const OT_EXT_SACRIFICIAL_OTS: usize = 256;

/// Byte length of [`OtExtProofMsg`] (`32` B `x_hash` + `256 * 32` B per-column `t_hash` = `8,224` B).
pub const OT_EXT_PROOF_BYTES: usize = 32 * (1 + OT_EXT_SUBSPACE_BITS);

/// Prime modulus $q = 12289$ ($q - 1 = 3 \times 2^{12} = 6 \times 2048$, supporting exact 2048-th roots of unity).
pub const RLWE_Q: u16 = 12289;

/// Center $\lfloor q / 2 \rfloor = 6144$ encoding bit `1` (`|e_1 r_c - e_2 s_R + e_3|_∞ <= 2049 < 3072 = floor(q/4)`).
pub const RLWE_HALF_Q: u16 = 6144;

/// Exact branch-free Barrett remainder `p % 12289` for all `p: u32`:
/// `12289 * 2_863_078_533 == 2^45 + 3205`, and `3205 * (u32::MAX / 12289 + 1) < 2_863_078_533`,
/// so `((p as u64 * 2_863_078_533) >> 45)` equals `p / 12289` identically across `[0, u32::MAX]`.
#[inline(always)]
pub(super) const fn rlwe_barrett_rem_u32(p: u32) -> u16 {
    let q = (((p as u64) * 2_863_078_533u64) >> 45) as u32;
    (p - q * (RLWE_Q as u32)) as u16
}

#[inline]
const fn rlwe_reduce_once(x: u32) -> u16 {
    let d = x.wrapping_sub(RLWE_Q as u32);
    (d.wrapping_add((RLWE_Q as u32) & 0u32.wrapping_sub(d >> 31))) as u16
}

#[inline]
const fn rlwe_add(a: u16, b: u16) -> u16 {
    rlwe_reduce_once((a as u32) + (b as u32))
}

#[inline]
const fn rlwe_sub(a: u16, b: u16) -> u16 {
    rlwe_reduce_once((a as u32) + (RLWE_Q as u32) - (b as u32))
}

#[inline(always)]
const fn rlwe_mul(a: u16, b: u16) -> u16 {
    rlwe_barrett_rem_u32((a as u32) * (b as u32))
}

const fn rlwe_pow(mut base: u16, mut exp: u32) -> u16 {
    let mut acc = 1u16;
    while exp > 0 {
        if (exp & 1) == 1 {
            acc = rlwe_mul(acc, base);
        }
        base = rlwe_mul(base, base);
        exp >>= 1;
    }
    acc
}

/// Primitive 2048-th root of unity $\psi_{2048} = 11^6 \bmod 12289$ ($\psi_{2048}^{1024} \equiv -1 \pmod{12289}$).
pub const RLWE_PSI_2048: u16 = {
    let psi = rlwe_pow(11, 6);
    assert!(rlwe_pow(psi, 1024) == RLWE_Q - 1);
    psi
};

/// Multiplicative inverse of $\psi_{2048}$ modulo $12289$.
pub const RLWE_PSI_INV_2048: u16 = rlwe_pow(RLWE_PSI_2048, 2047);

/// Primitive 1024-th root of unity $\omega_{1024} = \psi_{2048}^2 = 11^{12} \bmod 12289$ and its inverse.
pub const RLWE_OMEGA_1024: u16 = rlwe_mul(RLWE_PSI_2048, RLWE_PSI_2048);
pub const RLWE_OMEGA_INV_1024: u16 = rlwe_mul(RLWE_PSI_INV_2048, RLWE_PSI_INV_2048);
pub const RLWE_N_INV: u16 = rlwe_pow(RLWE_N as u16, (RLWE_Q - 2) as u32);

const PSI_POWS: [u16; RLWE_N] = {
    let mut arr = [0u16; RLWE_N];
    let mut cur = 1u16;
    let mut i = 0usize;
    while i < RLWE_N {
        arr[i] = cur;
        cur = rlwe_mul(cur, RLWE_PSI_2048);
        i += 1;
    }
    arr
};

const NTT_INVERSE_SCALES: [u16; RLWE_N] = {
    let mut arr = [0u16; RLWE_N];
    let mut cur = 1u16;
    let mut i = 0usize;
    while i < RLWE_N {
        arr[i] = rlwe_mul(cur, RLWE_N_INV);
        cur = rlwe_mul(cur, RLWE_PSI_INV_2048);
        i += 1;
    }
    arr
};

const OMEGA_POWS: [u16; RLWE_N / 2] = {
    let mut arr = [0u16; RLWE_N / 2];
    let mut cur = 1u16;
    let mut i = 0usize;
    while i < RLWE_N / 2 {
        arr[i] = cur;
        cur = rlwe_mul(cur, RLWE_OMEGA_1024);
        i += 1;
    }
    arr
};

const OMEGA_INV_POWS: [u16; RLWE_N / 2] = {
    let mut arr = [0u16; RLWE_N / 2];
    let mut cur = 1u16;
    let mut i = 0usize;
    while i < RLWE_N / 2 {
        arr[i] = cur;
        cur = rlwe_mul(cur, RLWE_OMEGA_INV_1024);
        i += 1;
    }
    arr
};

/// Constant-time Ring-LWE bit decoder matching `lean/Qsag/Protocol/Threshold/Preprocessing.lean:rlweDecodeBit`
/// (`true` iff `3072 <= z && z < 9216`, `0` secret-dependent branches).
#[inline]
pub fn rlwe_decode_bit_ct(z: u16) -> u8 {
    let z32 = black_box(z as u32);
    // ge_3072 == 1 iff z32 >= 3072 (underflow bit of z32 - 3072 is 0)
    let ge_3072 = 1u32 ^ ((z32.wrapping_sub(3072)) >> 31);
    // lt_9216 == 1 iff z32 < 9216 (underflow bit of z32 - 9216 is 1)
    let lt_9216 = (z32.wrapping_sub(9216)) >> 31;
    (ge_3072 & lt_9216) as u8
}

/// Polynomial in $R_q = \mathbb{Z}_{12289}\[X\]/(X^{1024} + 1)$.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct RlwePoly(pub [u16; RLWE_N]);

/// Pre-transformed negacyclic NTT representation of a public CRS polynomial for fast batch products.
#[derive(Clone, Copy)]
pub struct RlwePolyNtt(pub(super) [u16; RLWE_N]);

impl RlwePolyNtt {
    #[inline]
    pub fn from_ntt(&self) -> RlwePoly {
        let mut c = self.0;
        RlwePoly::ntt_inverse(&mut c);
        for i in 0..RLWE_N {
            c[i] = rlwe_mul(c[i], NTT_INVERSE_SCALES[i]);
        }
        RlwePoly(c)
    }

    #[inline]
    pub(crate) fn pointwise_mul_from_ntt(&self, rhs: &Self) -> RlwePoly {
        let mut c = [0u16; RLWE_N];
        for (dst, (&lhs, &rhs_coeff)) in c.iter_mut().zip(self.0.iter().zip(rhs.0.iter())) {
            *dst = rlwe_mul(lhs, rhs_coeff);
        }
        RlwePoly::ntt_inverse(&mut c);
        for (dst, &scale) in c.iter_mut().zip(NTT_INVERSE_SCALES.iter()) {
            *dst = rlwe_mul(*dst, scale);
        }
        RlwePoly(c)
    }
}

impl fmt::Debug for RlwePoly {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "RlwePoly([{}..])", self.0[0])
    }
}

impl Default for RlwePoly {
    fn default() -> Self {
        Self([0u16; RLWE_N])
    }
}

impl RlwePoly {
    pub const ZERO: Self = Self([0u16; RLWE_N]);

    pub fn add(&self, rhs: &Self) -> Self {
        let mut out = [0u16; RLWE_N];
        for (i, out_i_item) in out[..RLWE_N].iter_mut().enumerate() {
            *out_i_item = rlwe_add(self.0[i], rhs.0[i]);
        }
        Self(out)
    }

    pub fn sub(&self, rhs: &Self) -> Self {
        let mut out = [0u16; RLWE_N];
        for (i, out_i_item) in out[..RLWE_N].iter_mut().enumerate() {
            *out_i_item = rlwe_sub(self.0[i], rhs.0[i]);
        }
        Self(out)
    }

    /// Constant-time full-polynomial equality check across all 1024 coefficients (`0` early exit).
    #[inline]
    pub fn ct_eq(&self, rhs: &Self) -> bool {
        let mut diff = 0u16;
        for i in 0..RLWE_N {
            diff |= black_box(self.0[i]) ^ black_box(rhs.0[i]);
        }
        black_box(diff) == 0
    }

    /// Constant-time polynomial selection (`choice == true` -> `if_true`, else `if_false`).
    pub fn ct_select(choice: bool, if_true: &Self, if_false: &Self) -> Self {
        let mask = 0u16.wrapping_sub(black_box(choice as u16));
        let mut out = [0u16; RLWE_N];
        for (i, out_i_item) in out[..RLWE_N].iter_mut().enumerate() {
            *out_i_item = if_false.0[i] ^ (mask & (if_true.0[i] ^ if_false.0[i]));
        }
        Self(out)
    }

    // Forward Gentleman–Sande DIF leaves evaluations in bit-reversed order.
    // Pointwise products retain that order; inverse Cooley–Tukey DIT consumes
    // it directly. All indices and loop bounds depend only on the public size.
    fn ntt_forward(a: &mut [u16; RLWE_N]) {
        let mut len = RLWE_N;
        while len >= 2 {
            let half = len / 2;
            let step = RLWE_N >> len.trailing_zeros();
            for block in a.chunks_mut(len) {
                let (left, right) = block.split_at_mut(half);
                for (j, (u, v)) in left.iter_mut().zip(right).enumerate() {
                    let sum = rlwe_add(*u, *v);
                    *v = rlwe_mul(rlwe_sub(*u, *v), OMEGA_POWS[j * step]);
                    *u = sum;
                }
            }
            len >>= 1;
        }
    }

    fn ntt_inverse(a: &mut [u16; RLWE_N]) {
        let mut len = 2usize;
        while len <= RLWE_N {
            let half = len / 2;
            let step = RLWE_N >> len.trailing_zeros();
            for block in a.chunks_mut(len) {
                let (left, right) = block.split_at_mut(half);
                for (j, (u, v)) in left.iter_mut().zip(right).enumerate() {
                    let product = rlwe_mul(*v, OMEGA_INV_POWS[j * step]);
                    *v = rlwe_sub(*u, product);
                    *u = rlwe_add(*u, product);
                }
            }
            len <<= 1;
        }
    }

    #[inline]
    pub fn to_ntt(&self) -> RlwePolyNtt {
        let mut a = self.0;
        for i in 0..RLWE_N {
            a[i] = rlwe_mul(a[i], PSI_POWS[i]);
        }
        Self::ntt_forward(&mut a);
        RlwePolyNtt(a)
    }

    #[inline]
    pub fn mul_ntt(&self, lhs_ntt: &RlwePolyNtt) -> Self {
        let mut b = self.0;
        for i in 0..RLWE_N {
            b[i] = rlwe_mul(b[i], PSI_POWS[i]);
        }
        Self::ntt_forward(&mut b);
        let mut c = [0u16; RLWE_N];
        for i in 0..RLWE_N {
            c[i] = rlwe_mul(lhs_ntt.0[i], b[i]);
        }
        Self::ntt_inverse(&mut c);
        for i in 0..RLWE_N {
            c[i] = rlwe_mul(c[i], NTT_INVERSE_SCALES[i]);
        }
        wipe_u16s(&mut b);
        Self(c)
    }

    /// Fast $O(N \log N)$ negacyclic multiplication modulo $(X^{1024} + 1, 12289)$.
    pub fn mul_negacyclic(&self, rhs: &Self) -> Self {
        let mut lhs_ntt = self.to_ntt();
        let out = rhs.mul_ntt(&lhs_ntt);
        wipe_u16s(&mut lhs_ntt.0);
        out
    }

    /// Deterministically derive public CRS polynomial in $R_q$ via rejection sampling (`< 3*q = 36867 < 65536`).
    pub fn from_crs_xof(
        session_id: &[u8; 32],
        sender: usize,
        receiver: usize,
        ot_idx: u32,
        slot: u8,
    ) -> Self {
        let mut xof = Cshake256Xof::new(b"QSAG.OT.RLWE.CRS/v1");
        let mut hdr = [0u8; 53];
        hdr[0..32].copy_from_slice(session_id);
        hdr[32..40].copy_from_slice(&(sender as u64).to_be_bytes());
        hdr[40..48].copy_from_slice(&(receiver as u64).to_be_bytes());
        hdr[48..52].copy_from_slice(&ot_idx.to_be_bytes());
        hdr[52] = slot;
        xof.absorb(&hdr);

        let mut coeffs = [0u16; RLWE_N];
        let mut idx = 0usize;
        let mut initial_buf = [0u8; 28 * 136];
        xof.squeeze(&mut initial_buf);
        #[expect(
            clippy::chunks_exact_to_as_chunks,
            reason = "Keep the workspace Rust 1.85 minimum; slice as_chunks requires a newer compiler"
        )]
        for chunk in initial_buf.chunks_exact(2) {
            if idx == RLWE_N {
                return Self(coeffs);
            }
            let val = u16::from_le_bytes([chunk[0], chunk[1]]);
            if val < 3 * RLWE_Q {
                coeffs[idx] = rlwe_barrett_rem_u32(u32::from(val));
                idx += 1;
            }
        }
        let mut tail_buf = [0u8; 2 * 136];
        while idx < RLWE_N {
            xof.squeeze(&mut tail_buf);
            #[expect(
                clippy::chunks_exact_to_as_chunks,
                reason = "Keep the workspace Rust 1.85 minimum; slice as_chunks requires a newer compiler"
            )]
            for chunk in tail_buf.chunks_exact(2) {
                if idx == RLWE_N {
                    break;
                }
                let val = u16::from_le_bytes([chunk[0], chunk[1]]);
                if val < 3 * RLWE_Q {
                    coeffs[idx] = rlwe_barrett_rem_u32(u32::from(val));
                    idx += 1;
                }
            }
        }
        Self(coeffs)
    }

    /// 8-way SIMD (`KeccakState8x`) CRS polynomial expansion producing bit-for-bit identical
    /// polynomials to 8 calls to [`Self::from_crs_xof`].
    pub(super) fn from_crs_xof_batch8(
        session_id: &[u8; 32],
        sender: usize,
        receiver: usize,
        ot_indices: [u32; 8],
        slot: u8,
    ) -> [Self; 8] {
        const RLWE_CRS_V1_MID: [u64; 25] =
            crate::sponge::keccak::cshake256_static_midstate(b"QSAG.OT.RLWE.CRS/v1");
        const INITIAL_WORDS: usize = 28 * crate::sponge::keccak::SHAKE256_RATE_LANES;

        let mut hdrs = [[0u8; 53]; 8];
        let s_be = (sender as u64).to_be_bytes();
        let r_be = (receiver as u64).to_be_bytes();
        for (lane, hdr) in hdrs.iter_mut().enumerate() {
            hdr[0..32].copy_from_slice(session_id);
            hdr[32..40].copy_from_slice(&s_be);
            hdr[40..48].copy_from_slice(&r_be);
            hdr[48..52].copy_from_slice(&ot_indices[lane].to_be_bytes());
            hdr[52] = slot;
        }
        let inputs: [&[u8]; 8] = core::array::from_fn(|i| &hdrs[i][..]);
        let mut w0 = [0u64; INITIAL_WORDS];
        let mut w1 = [0u64; INITIAL_WORDS];
        let mut w2 = [0u64; INITIAL_WORDS];
        let mut w3 = [0u64; INITIAL_WORDS];
        let mut w4 = [0u64; INITIAL_WORDS];
        let mut w5 = [0u64; INITIAL_WORDS];
        let mut w6 = [0u64; INITIAL_WORDS];
        let mut w7 = [0u64; INITIAL_WORDS];
        {
            let mut outs: [&mut [u64]; 8] = [
                &mut w0, &mut w1, &mut w2, &mut w3, &mut w4, &mut w5, &mut w6, &mut w7,
            ];
            crate::sponge::keccak::cshake256_8x_squeeze_u64s(&RLWE_CRS_V1_MID, inputs, &mut outs);
        }
        let raw_lanes = [&w0, &w1, &w2, &w3, &w4, &w5, &w6, &w7];
        core::array::from_fn(|lane| {
            let mut coeffs = [0u16; RLWE_N];
            let mut idx = 0usize;
            'words: for &word in raw_lanes[lane].iter() {
                for shift in [0u32, 16, 32, 48] {
                    if idx == RLWE_N {
                        break 'words;
                    }
                    let val = ((word >> shift) & 0xFFFF) as u16;
                    if val < 3 * RLWE_Q {
                        coeffs[idx] = rlwe_barrett_rem_u32(u32::from(val));
                        idx += 1;
                    }
                }
            }
            if idx == RLWE_N {
                Self(coeffs)
            } else {
                Self::from_crs_xof(session_id, sender, receiver, ot_indices[lane], slot)
            }
        })
    }

    /// Deterministically expand CRS polynomial `(a_crs` or `t_crs[ot_idx])` bound to `crs_coin`.
    pub fn from_crs_xof_with_coin(
        crs_coin: &[u8; 32],
        session_id: &[u8; 32],
        sender_id: usize,
        receiver_id: usize,
        ot_idx: u32,
        role: u8,
    ) -> Self {
        let mixed_sid = crs_mixed_session_id(crs_coin, session_id);
        Self::from_crs_xof(&mixed_sid, sender_id, receiver_id, ot_idx, role)
    }

    /// Check whether every coefficient lies in canonical `[0, RLWE_Q)`.
    #[inline]
    pub fn is_canonical(&self) -> bool {
        self.0.iter().all(|&c| c < RLWE_Q)
    }

    /// Sample short ternary noise polynomial in $\{-1, 0, +1\}^{1024}$ ($\eta = 1$) in strict
    /// constant time via 2-bit centered binomial `CBD_1` (`a_bit - b_bit`, `0` rejection branches!).
    pub fn sample_ternary_eta1(rng: &mut PartyPrivateRng) -> Self {
        let mut coeffs = [0u16; RLWE_N];
        let mut buf = [0u8; RLWE_N / 4]; // 256 bytes = 1024 * 2 bits
        rng.fill_bytes(&mut buf);
        for byte_idx in 0..(RLWE_N / 4) {
            let b = black_box(buf[byte_idx]);
            for sub in 0..4 {
                let pair = (b >> (2 * sub)) & 0x3;
                let a_bit = (pair & 1) as u16;
                let b_bit = ((pair >> 1) & 1) as u16;
                // a_bit - b_bit in {-1, 0, +1} mod RLWE_Q:
                // if a_bit == 1 && b_bit == 0 -> 1
                // if a_bit == 0 && b_bit == 1 -> RLWE_Q - 1
                // else -> 0
                let pos_mask = 0u16.wrapping_sub(a_bit & (1 - b_bit));
                let neg_mask = 0u16.wrapping_sub((1 - a_bit) & b_bit);
                coeffs[4 * byte_idx + sub] = (1u16 & pos_mask) | ((RLWE_Q - 1) & neg_mask);
            }
        }
        wipe_bytes(&mut buf);
        Self(coeffs)
    }
}

#[inline]
pub(super) fn crs_mixed_session_id(crs_coin: &[u8; 32], session_id: &[u8; 32]) -> [u8; 32] {
    if *crs_coin == [0u8; 32] {
        *session_id
    } else {
        cshake256_32_multi_frame(b"QSAG.OT.RLWE.CRS.COIN/v1", &[session_id, crs_coin])
    }
}
/// First message of active-checked Ring-LWE 1-out-of-2 OT (`Receiver -> Sender`), carrying `pk0`
/// and a constant-time OR-Sigma proof of short witness knowledge [`RlweReceiverZkPok`].
#[derive(Clone, Debug)]
pub struct RlweOtReceiverMsg {
    pub pk0: RlwePoly,
    pub pok: RlweReceiverZkPok,
}

/// Ephemeral receiver state for 1 FO-checked Ring-LWE base OT (`!Clone`, wiped on `Drop`).
pub struct RlweOtReceiverSecret {
    pub(super) crs_coin: [u8; 32],
    pub(super) session_id: [u8; 32],
    pub(super) sender_id: usize,
    pub(super) receiver_id: usize,
    pub(super) ot_idx: u32,
    pub(super) pk0: RlwePoly,
    pub(super) s_r: RlwePoly,
    pub(super) choice_bit: bool,
}

impl fmt::Debug for RlweOtReceiverSecret {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("RlweOtReceiverSecret([REDACTED])")
    }
}

impl Drop for RlweOtReceiverSecret {
    fn drop(&mut self) {
        wipe_u16s(&mut self.s_r.0);
        self.choice_bit = false;
        black_box(&mut self.choice_bit);
    }
}

/// Second message of active-checked Ring-LWE 1-out-of-2 OT (`Sender -> Receiver`).
#[derive(Clone, Debug)]
pub struct RlweOtSenderMsg {
    pub u0: RlwePoly,
    pub v0: RlwePoly,
    pub u1: RlwePoly,
    pub v1: RlwePoly,
}

#[inline]
fn encode_seed64_into_poly(seed: &[u8; 32], rho: &[u8; 32]) -> RlwePoly {
    let mut coeffs = [0u16; RLWE_N];
    for byte_idx in 0..32 {
        let b_s = black_box(seed[byte_idx]);
        let b_r = black_box(rho[byte_idx]);
        for bit in 0..8 {
            let bit_s = ((b_s >> bit) & 1) as u16;
            let bit_r = ((b_r >> bit) & 1) as u16;
            coeffs[8 * byte_idx + bit] = bit_s * RLWE_HALF_Q;
            coeffs[256 + 8 * byte_idx + bit] = bit_r * RLWE_HALF_Q;
        }
    }
    RlwePoly(coeffs)
}

#[inline]
fn decode_seed64_from_poly_ct(noisy: &RlwePoly) -> ([u8; 32], [u8; 32]) {
    let mut seed = [0u8; 32];
    let mut rho = [0u8; 32];
    for byte_idx in 0..32 {
        let mut acc_s = 0u8;
        let mut acc_r = 0u8;
        for bit in 0..8 {
            acc_s |= rlwe_decode_bit_ct(noisy.0[8 * byte_idx + bit]) << bit;
            acc_r |= rlwe_decode_bit_ct(noisy.0[256 + 8 * byte_idx + bit]) << bit;
        }
        seed[byte_idx] = acc_s;
        rho[byte_idx] = acc_r;
    }
    (seed, rho)
}

/// Deterministic Fujisaki–Okamoto branch encryptor: derives `(r_b, e2_b, e3_b)` from
/// `Cshake256("QSAG.OT.RLWE.FO/v1", crs_coin || session_id || sender || receiver || ot_idx || branch || seed || rho)`
/// and encrypts `(seed || rho)` (64 bytes = 512 bits <= 1024 coeffs).
#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the explicit statement, role, witness and randomness bindings in this protocol API"
)]
pub(super) fn rlwe_fo_encrypt_branch(
    crs_coin: &[u8; 32],
    session_id: &[u8; 32],
    sender_id: usize,
    receiver_id: usize,
    ot_idx: u32,
    branch: u8,
    a_ntt: &RlwePolyNtt,
    pk_branch: &RlwePoly,
    seed: &[u8; 32],
    rho: &[u8; 32],
) -> (RlwePoly, RlwePoly) {
    let mut label = [0u8; 120];
    label[0..32].copy_from_slice(crs_coin);
    label[32..64].copy_from_slice(session_id);
    label[64..72].copy_from_slice(&(sender_id as u64).to_be_bytes());
    label[72..80].copy_from_slice(&(receiver_id as u64).to_be_bytes());
    label[80..84].copy_from_slice(&ot_idx.to_be_bytes());
    label[84] = branch;
    label[88..120].copy_from_slice(seed);
    let mut fo_seed = cshake256_32_multi_frame(b"QSAG.OT.RLWE.FO/v2", &[&label, rho]);
    wipe_bytes(&mut label);

    let mut fo_rng = PartyPrivateRng::from_seed(fo_seed, b"QSAG.OT.RLWE.FO.STREAM/v2");
    wipe_bytes32(&mut fo_seed);
    let mut r_b = RlwePoly::sample_ternary_eta1(&mut fo_rng);
    let mut e2_b = RlwePoly::sample_ternary_eta1(&mut fo_rng);
    let mut e3_b = RlwePoly::sample_ternary_eta1(&mut fo_rng);
    let mut m_poly = encode_seed64_into_poly(seed, rho);

    let mut r_b_ntt = r_b.to_ntt();
    let u_b = a_ntt.pointwise_mul_from_ntt(&r_b_ntt).add(&e2_b);
    let v_b = pk_branch.mul_ntt(&r_b_ntt).add(&e3_b).add(&m_poly);

    wipe_u16s(&mut r_b_ntt.0);
    wipe_u16s(&mut r_b.0);
    wipe_u16s(&mut e2_b.0);
    wipe_u16s(&mut e3_b.0);
    wipe_u16s(&mut m_poly.0);
    (u_b, v_b)
}

#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the explicit statement, role, witness and randomness bindings in this protocol API"
)]
fn rlwe_ot_choose_with_crs(
    crs_coin: &[u8; 32],
    session_id: &[u8; 32],
    sender_id: usize,
    receiver_id: usize,
    ot_idx: u32,
    a_ntt: &RlwePolyNtt,
    t_crs: &RlwePoly,
    choice_bit: bool,
    rng: &mut PartyPrivateRng,
) -> (RlweOtReceiverSecret, RlweOtReceiverMsg) {
    let (s_r, mut e1) = loop {
        let mut s = RlwePoly::sample_ternary_eta1(rng);
        let mut e = RlwePoly::sample_ternary_eta1(rng);
        if black_box(bounded_ternary_witness(&s, &e)) {
            break (s, e);
        }
        wipe_u16s(&mut s.0);
        wipe_u16s(&mut e.0);
    };
    let rlwe_sample = s_r.mul_ntt(a_ntt).add(&e1);
    let shifted = rlwe_sample.sub(t_crs);
    let pk0 = RlwePoly::ct_select(choice_bit, &shifted, &rlwe_sample);
    let pok = RlweReceiverZkPok::prove_ct(
        crs_coin,
        session_id,
        sender_id,
        receiver_id,
        ot_idx,
        a_ntt,
        t_crs,
        &pk0,
        &s_r,
        &e1,
        choice_bit,
        rng,
    );
    wipe_u16s(&mut e1.0);
    (
        RlweOtReceiverSecret {
            crs_coin: *crs_coin,
            session_id: *session_id,
            sender_id,
            receiver_id,
            ot_idx,
            pk0,
            s_r,
            choice_bit,
        },
        RlweOtReceiverMsg { pk0, pok },
    )
}

/// Transparent CRS for the standalone base-OT API, bound to its protocol and roles.
fn rlwe_session_crs(session_id: &[u8; 32], sender_id: usize, receiver_id: usize) -> [u8; 32] {
    cshake256_32_multi_frame(
        b"QSAG.OT.RLWE.CRS/v2",
        &[
            session_id,
            &(sender_id as u64).to_be_bytes(),
            &(receiver_id as u64).to_be_bytes(),
            &(RLWE_N as u64).to_be_bytes(),
            &RLWE_Q.to_be_bytes(),
            &(RLWE_ZKPOK_REPS as u64).to_be_bytes(),
        ],
    )
}

/// Receiver Round-1: encode secret `choice_bit` into `pk0 = (a * s_R + e_1) - choice_bit * t_crs`
/// and attach a constant-time OR-Sigma proof [`RlweReceiverZkPok`].
pub fn rlwe_ot_choose(
    session_id: &[u8; 32],
    sender_id: usize,
    receiver_id: usize,
    ot_idx: u32,
    choice_bit: bool,
    rng: &mut PartyPrivateRng,
) -> (RlweOtReceiverSecret, RlweOtReceiverMsg) {
    let zero_coin = rlwe_session_crs(session_id, sender_id, receiver_id);
    let a_ntt =
        RlwePoly::from_crs_xof_with_coin(&zero_coin, session_id, sender_id, receiver_id, ot_idx, 0)
            .to_ntt();
    let t_crs =
        RlwePoly::from_crs_xof_with_coin(&zero_coin, session_id, sender_id, receiver_id, ot_idx, 1);
    rlwe_ot_choose_with_crs(
        &zero_coin,
        session_id,
        sender_id,
        receiver_id,
        ot_idx,
        &a_ntt,
        &t_crs,
        choice_bit,
        rng,
    )
}

#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the explicit statement, role, witness and randomness bindings in this protocol API"
)]
fn try_rlwe_ot_transfer_with_crs(
    crs_coin: &[u8; 32],
    session_id: &[u8; 32],
    sender_id: usize,
    receiver_id: usize,
    ot_idx: u32,
    a_ntt: &RlwePolyNtt,
    t_crs: &RlwePoly,
    req: &RlweOtReceiverMsg,
    seed0: &[u8; 32],
    seed1: &[u8; 32],
    rng: &mut PartyPrivateRng,
) -> Result<RlweOtSenderMsg, PreprocessError> {
    if !req.pok.verify(
        crs_coin,
        session_id,
        sender_id,
        receiver_id,
        ot_idx,
        a_ntt,
        t_crs,
        &req.pk0,
    ) {
        return Err(PreprocessError::BaseOtReceiverProofFailed {
            sender_id,
            receiver_id,
        });
    }
    let pk0 = req.pk0;
    let pk1 = pk0.add(t_crs);
    let mut rho0 = rng.next_bytes32();
    let mut rho1 = rng.next_bytes32();
    let (u0, v0) = rlwe_fo_encrypt_branch(
        crs_coin,
        session_id,
        sender_id,
        receiver_id,
        ot_idx,
        0,
        a_ntt,
        &pk0,
        seed0,
        &rho0,
    );
    let (u1, v1) = rlwe_fo_encrypt_branch(
        crs_coin,
        session_id,
        sender_id,
        receiver_id,
        ot_idx,
        1,
        a_ntt,
        &pk1,
        seed1,
        &rho1,
    );
    wipe_bytes32(&mut rho0);
    wipe_bytes32(&mut rho1);
    Ok(RlweOtSenderMsg { u0, v0, u1, v1 })
}

/// Fallible Sender Round-2: verifies Receiver's OR-Sigma ZKPoK **before** encrypting `(seed0, seed1)`.
#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the explicit statement, role, witness and randomness bindings in this protocol API"
)]
pub fn try_rlwe_ot_transfer(
    session_id: &[u8; 32],
    sender_id: usize,
    receiver_id: usize,
    ot_idx: u32,
    req: &RlweOtReceiverMsg,
    seed0: &[u8; 32],
    seed1: &[u8; 32],
    rng: &mut PartyPrivateRng,
) -> Result<RlweOtSenderMsg, PreprocessError> {
    let zero_coin = rlwe_session_crs(session_id, sender_id, receiver_id);
    let a_ntt =
        RlwePoly::from_crs_xof_with_coin(&zero_coin, session_id, sender_id, receiver_id, ot_idx, 0)
            .to_ntt();
    let t_crs =
        RlwePoly::from_crs_xof_with_coin(&zero_coin, session_id, sender_id, receiver_id, ot_idx, 1);
    try_rlwe_ot_transfer_with_crs(
        &zero_coin,
        session_id,
        sender_id,
        receiver_id,
        ot_idx,
        &a_ntt,
        &t_crs,
        req,
        seed0,
        seed1,
        rng,
    )
}

/// Sender Round-2: verifies Receiver's OR-Sigma ZKPoK and Fujisaki–Okamoto encrypts 64-byte payloads
/// `(seed_b || rho_b)` under `(pk0, pk0 + t_crs)` with worst-case noise $\le 2049 < 3072$ (`0` decryption error).
#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the explicit statement, role, witness and randomness bindings in this protocol API"
)]
pub fn rlwe_ot_transfer(
    session_id: &[u8; 32],
    sender_id: usize,
    receiver_id: usize,
    ot_idx: u32,
    req: &RlweOtReceiverMsg,
    seed0: &[u8; 32],
    seed1: &[u8; 32],
    rng: &mut PartyPrivateRng,
) -> Result<RlweOtSenderMsg, PreprocessError> {
    try_rlwe_ot_transfer(
        session_id,
        sender_id,
        receiver_id,
        ot_idx,
        req,
        seed0,
        seed1,
        rng,
    )
}

pub(super) fn rlwe_ot_decrypt_ct_mask(
    sec: &RlweOtReceiverSecret,
    a_ntt: &RlwePolyNtt,
    t_crs: &RlwePoly,
    resp: &RlweOtSenderMsg,
) -> Result<([u8; 32], u8), PreprocessError> {
    if !resp.u0.is_canonical()
        || !resp.v0.is_canonical()
        || !resp.u1.is_canonical()
        || !resp.v1.is_canonical()
    {
        return Err(PreprocessError::BaseOtFoCheckFailed {
            sender_id: sec.sender_id,
            receiver_id: sec.receiver_id,
            ot_idx: sec.ot_idx,
        });
    }
    let u_c = RlwePoly::ct_select(sec.choice_bit, &resp.u1, &resp.u0);
    let v_c = RlwePoly::ct_select(sec.choice_bit, &resp.v1, &resp.v0);
    let mut prod = u_c.mul_negacyclic(&sec.s_r);
    let mut diff = v_c.sub(&prod);
    let (mut seed_c, mut rho_c) = decode_seed64_from_poly_ct(&diff);
    wipe_u16s(&mut prod.0);
    wipe_u16s(&mut diff.0);

    let pk1 = sec.pk0.add(t_crs);
    let pk_c = RlwePoly::ct_select(sec.choice_bit, &pk1, &sec.pk0);
    let branch = black_box(sec.choice_bit as u8);
    let (u_exp, v_exp) = rlwe_fo_encrypt_branch(
        &sec.crs_coin,
        &sec.session_id,
        sec.sender_id,
        sec.receiver_id,
        sec.ot_idx,
        branch,
        a_ntt,
        &pk_c,
        &seed_c,
        &rho_c,
    );
    wipe_bytes32(&mut rho_c);
    let ok_u = u_exp.ct_eq(&u_c) as u8;
    let ok_v = v_exp.ct_eq(&v_c) as u8;
    let ok = black_box(ok_u & ok_v);
    let keep_mask = 0u8.wrapping_sub(ok);
    for b in &mut seed_c {
        *b &= keep_mask;
    }
    Ok((seed_c, ok))
}

fn rlwe_ot_decrypt_with_crs(
    sec: &RlweOtReceiverSecret,
    a_ntt: &RlwePolyNtt,
    t_crs: &RlwePoly,
    resp: &RlweOtSenderMsg,
) -> Result<[u8; 32], PreprocessError> {
    let (mut seed_c, ok) = rlwe_ot_decrypt_ct_mask(sec, a_ntt, t_crs, resp)?;
    if black_box(ok) == 0 {
        wipe_bytes32(&mut seed_c);
        return Err(PreprocessError::BaseOtFoCheckFailed {
            sender_id: sec.sender_id,
            receiver_id: sec.receiver_id,
            ot_idx: sec.ot_idx,
        });
    }
    Ok(seed_c)
}

/// Receiver Round-3: branchlessly select `(u_c, v_c)`, recover `(seed_c, rho_c)`, and **actively
/// re-encrypt `(u_c, v_c)` from `rho_c`** (`Err(BaseOtFoCheckFailed)` if the Sender deviated!).
pub fn rlwe_ot_decrypt(
    sec: &RlweOtReceiverSecret,
    resp: &RlweOtSenderMsg,
) -> Result<[u8; 32], PreprocessError> {
    let a_ntt = RlwePoly::from_crs_xof_with_coin(
        &sec.crs_coin,
        &sec.session_id,
        sec.sender_id,
        sec.receiver_id,
        sec.ot_idx,
        0,
    )
    .to_ntt();
    let t_crs = RlwePoly::from_crs_xof_with_coin(
        &sec.crs_coin,
        &sec.session_id,
        sec.sender_id,
        sec.receiver_id,
        sec.ot_idx,
        1,
    );
    rlwe_ot_decrypt_with_crs(sec, &a_ntt, &t_crs, resp)
}
