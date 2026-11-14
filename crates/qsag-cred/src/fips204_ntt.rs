//! Exact NIST `FIPS 204` (`ML-DSA-44`, `ML-DSA-65`, `ML-DSA-87`) Ring Arithmetic, NTT, Bit-Packing,
//! `Power2Round`, Division-Free `Decompose`/`MakeHint`/`UseHint`, `SampleInBall`, and Standalone
//! Standard Verifier (`ml_dsa_verify`, FIPS 204 Algorithm 3 / Algorithm 8).

use alloc::vec;
use alloc::vec::Vec;

use qsag_accel::ct::{ct_eq_bytes, ct_lt_u64, ct_select_u64, ct_zeroize_u32s};
use qsag_accel::keccak::{Shake128, Shake256};

/// FIPS 204 prime modulus $q = 8\_380\_417 = 2^{23} - 2^{13} + 1$.
pub const MLDSA_Q: u32 = 8_380_417;
/// Cyclotomic ring degree $N = 256$.
pub const MLDSA_N: usize = 256;
/// Public key dropped low-order bit count $d = 13$.
pub const MLDSA_D: u32 = 13;
/// Primitive 512th root of unity $\zeta = 1753 \bmod q$.
pub const MLDSA_ZETA: u32 = 1753;
/// $256^{-1} \bmod 8\_380\_417 = 8\_347\_681$.
pub const MLDSA_INV_256: u32 = 8_347_681;

#[inline]
pub const fn fq_add(a: u32, b: u32) -> u32 {
    let s = a + b;
    let ge = !ct_lt_u64(s as u64, MLDSA_Q as u64);
    ct_select_u64(ge, s.wrapping_sub(MLDSA_Q) as u64, s as u64) as u32
}

#[inline]
pub const fn fq_sub(a: u32, b: u32) -> u32 {
    let lt = ct_lt_u64(a as u64, b as u64);
    let d = a.wrapping_sub(b);
    ct_select_u64(lt, d.wrapping_add(MLDSA_Q) as u64, d as u64) as u32
}

/// Branchless, division-free Barrett modular multiplication mod $q = 8\_380\_417$:
/// For all $a, b < q$ ($a b < 2^{46}$), with
/// $M_{64} = \lfloor 2^{64} / 8\_380\_417 \rfloor = 2\_201\_154\_512\_929$,
/// $q_{\text{est}} = \lfloor (a b \cdot M_{64}) / 2^{64} \rfloor \in \{\lfloor ab/q \rfloor - 1, \lfloor ab/q \rfloor\}$,
/// so one branchless conditional subtraction of $q$ reduces `ab - q_est * q` into `[0, q)` with
/// zero hardware `div`/`rem` instructions.
#[inline]
pub const fn fq_mul(a: u32, b: u32) -> u32 {
    const BARRETT_M64: u128 = (1u128 << 64) / (MLDSA_Q as u128);
    let prod = (a as u64) * (b as u64);
    let q_est = (((prod as u128) * BARRETT_M64) >> 64) as u64;
    let rem = prod - q_est * (MLDSA_Q as u64);
    let ge = !ct_lt_u64(rem, MLDSA_Q as u64);
    ct_select_u64(ge, rem.wrapping_sub(MLDSA_Q as u64), rem) as u32
}

/// Constant-time Fermat inversion $a^{q - 2} \bmod q$ (`0 -> 0`).
pub const fn fq_inv_or_zero(a: u32) -> u32 {
    let mut base = a;
    let mut exp = MLDSA_Q - 2;
    let mut acc = 1u32;
    while exp > 0 {
        if (exp & 1) == 1 {
            acc = fq_mul(acc, base);
        }
        base = fq_mul(base, base);
        exp >>= 1;
    }
    acc
}

const fn bitrev8(mut x: u8) -> u8 {
    let mut out = 0u8;
    let mut i = 0;
    while i < 8 {
        out = (out << 1) | (x & 1);
        x >>= 1;
        i += 1;
    }
    out
}

const fn fq_pow(mut base: u32, mut exp: u32) -> u32 {
    let mut acc = 1u32;
    while exp > 0 {
        if (exp & 1) == 1 {
            acc = fq_mul(acc, base);
        }
        base = fq_mul(base, base);
        exp >>= 1;
    }
    acc
}

const fn build_fips204_zetas() -> [u32; MLDSA_N] {
    let mut arr = [0u32; MLDSA_N];
    let mut i = 0usize;
    while i < MLDSA_N {
        let rev = bitrev8(i as u8) as u32;
        arr[i] = fq_pow(MLDSA_ZETA, rev);
        i += 1;
    }
    arr
}

/// Exact FIPS 204 Appendix B bit-reversed NTT twiddle table (`ZETAS[i] = 1753^{BitRev_8(i)} mod q`).
pub static FIPS204_ZETAS: [u32; MLDSA_N] = build_fips204_zetas();

/// All three NIST FIPS 204 parameter sets (`ML-DSA-44`, `ML-DSA-65`, `ML-DSA-87`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum MlDsaLevel {
    MlDsa44,
    MlDsa65,
    MlDsa87,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MlDsaParams {
    pub level: MlDsaLevel,
    pub k: usize,
    pub ell: usize,
    pub eta: u32,
    pub tau: usize,
    pub beta: u32,
    pub gamma1: u32,
    pub gamma2: u32,
    pub omega: usize,
    pub c_tilde_bytes: usize,
    pub z_poly_bytes: usize,
    pub w1_poly_bytes: usize,
    pub pk_bytes: usize,
    pub sig_bytes: usize,
}

impl MlDsaLevel {
    pub const fn params(self) -> MlDsaParams {
        match self {
            Self::MlDsa44 => MlDsaParams {
                level: self,
                k: 4,
                ell: 4,
                eta: 2,
                tau: 39,
                beta: 78,
                gamma1: 1 << 17,
                gamma2: (MLDSA_Q - 1) / 88,
                omega: 80,
                c_tilde_bytes: 32,
                z_poly_bytes: 576,  // 256 * 18 / 8
                w1_poly_bytes: 192, // 256 * 6 / 8
                pk_bytes: 32 + 4 * 320,
                sig_bytes: 32 + 4 * 576 + 80 + 4, // 2420 B
            },
            Self::MlDsa65 => MlDsaParams {
                level: self,
                k: 6,
                ell: 5,
                eta: 4,
                tau: 49,
                beta: 196,
                gamma1: 1 << 19,
                gamma2: (MLDSA_Q - 1) / 32,
                omega: 55,
                c_tilde_bytes: 48,
                z_poly_bytes: 640,  // 256 * 20 / 8
                w1_poly_bytes: 128, // 256 * 4 / 8
                pk_bytes: 32 + 6 * 320,
                sig_bytes: 48 + 5 * 640 + 55 + 6, // 3309 B
            },
            Self::MlDsa87 => MlDsaParams {
                level: self,
                k: 8,
                ell: 7,
                eta: 2,
                tau: 60,
                beta: 120,
                gamma1: 1 << 19,
                gamma2: (MLDSA_Q - 1) / 32,
                omega: 75,
                c_tilde_bytes: 64,
                z_poly_bytes: 640,
                w1_poly_bytes: 128,
                pk_bytes: 32 + 8 * 320,
                sig_bytes: 64 + 7 * 640 + 75 + 8, // 4627 B
            },
        }
    }
}

/// Polynomial in $\mathcal{R}_q$ (standard coefficient order or NTT evaluation order).
#[derive(Clone, PartialEq, Eq)]
pub struct Poly256 {
    pub coeffs: [u32; MLDSA_N],
}

impl Default for Poly256 {
    fn default() -> Self {
        Self::zero()
    }
}

impl core::fmt::Debug for Poly256 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "Poly256([256 mod {}])", MLDSA_Q)
    }
}

impl Poly256 {
    pub const fn zero() -> Self {
        Self {
            coeffs: [0u32; MLDSA_N],
        }
    }

    pub fn zeroize(&mut self) {
        ct_zeroize_u32s(&mut self.coeffs);
    }

    pub fn add(&self, rhs: &Self) -> Self {
        let mut out = [0u32; MLDSA_N];
        for (out, (&left, &right)) in out.iter_mut().zip(self.coeffs.iter().zip(&rhs.coeffs)) {
            *out = fq_add(left, right);
        }
        Self { coeffs: out }
    }

    pub fn sub(&self, rhs: &Self) -> Self {
        let mut out = [0u32; MLDSA_N];
        for (out, (&left, &right)) in out.iter_mut().zip(self.coeffs.iter().zip(&rhs.coeffs)) {
            *out = fq_sub(left, right);
        }
        Self { coeffs: out }
    }

    pub fn scale(&self, scalar: u32) -> Self {
        let mut out = [0u32; MLDSA_N];
        for (out, &value) in out.iter_mut().zip(&self.coeffs) {
            *out = fq_mul(value, scalar);
        }
        Self { coeffs: out }
    }

    /// Pointwise multiplication in the NTT domain (`Algorithm 45`).
    pub fn pointwise_mul(&self, rhs: &Self) -> Self {
        let mut out = [0u32; MLDSA_N];
        for (out, (&left, &right)) in out.iter_mut().zip(self.coeffs.iter().zip(&rhs.coeffs)) {
            *out = fq_mul(left, right);
        }
        Self { coeffs: out }
    }

    /// Exact FIPS 204 Algorithm 41 forward `NTT` (Cooley-Tukey in-place, `0` secret branches).
    pub fn ntt(&mut self) {
        let mut m = 0usize;
        let mut len = 128usize;
        while len >= 1 {
            let mut start = 0usize;
            while start < MLDSA_N {
                m += 1;
                let z = FIPS204_ZETAS[m];
                for j in start..(start + len) {
                    let t = fq_mul(z, self.coeffs[j + len]);
                    self.coeffs[j + len] = fq_sub(self.coeffs[j], t);
                    self.coeffs[j] = fq_add(self.coeffs[j], t);
                }
                start += 2 * len;
            }
            len >>= 1;
        }
    }

    /// Exact FIPS 204 Algorithm 42 inverse `NTT^{-1}` (Gentleman-Sande in-place, `0` secret branches).
    pub fn inv_ntt(&mut self) {
        let mut m = 256usize;
        let mut len = 1usize;
        while len < MLDSA_N {
            let mut start = 0usize;
            while start < MLDSA_N {
                m -= 1;
                let z_neg = fq_sub(0, FIPS204_ZETAS[m]);
                for j in start..(start + len) {
                    let t = self.coeffs[j];
                    self.coeffs[j] = fq_add(t, self.coeffs[j + len]);
                    self.coeffs[j + len] = fq_mul(z_neg, fq_sub(t, self.coeffs[j + len]));
                }
                start += 2 * len;
            }
            len <<= 1;
        }
        for slot in &mut self.coeffs {
            *slot = fq_mul(*slot, MLDSA_INV_256);
        }
    }

    /// Exact constant-time centered infinity norm $\|f\|_\infty = \max_j |f_j \bmod^\pm q|$.
    pub fn inf_norm(&self) -> u32 {
        let half_q = (MLDSA_Q / 2) as u64;
        let mut max_v = 0u64;
        for &c in &self.coeffs {
            let c64 = c as u64;
            let gt = ct_lt_u64(half_q, c64);
            let abs_v = ct_select_u64(gt, (MLDSA_Q as u64) - c64, c64);
            let bigger = ct_lt_u64(max_v, abs_v);
            max_v = ct_select_u64(bigger, abs_v, max_v);
        }
        max_v as u32
    }

    /// Unbiased 23-bit FIPS 204 `RejNTTPoly` sampling from `SHAKE128` (`Algorithm 30`).
    pub fn rej_ntt_shake128(rho: &[u8; 32], col_j: u8, row_i: u8) -> Self {
        let mut sp = Shake128::new();
        sp.absorb(rho);
        sp.absorb(&[col_j, row_i]);
        sp.finalize(0x1F);

        let mut coeffs = [0u32; MLDSA_N];
        let mut idx = 0usize;
        let mut buf = [0u8; 168];
        while idx < MLDSA_N {
            sp.squeeze(&mut buf);
            let mut pos = 0usize;
            while pos + 3 <= buf.len() && idx < MLDSA_N {
                let cand =
                    u32::from_le_bytes([buf[pos], buf[pos + 1], buf[pos + 2], 0]) & 0x7F_FFFF;
                pos += 3;
                if cand < MLDSA_Q {
                    coeffs[idx] = cand;
                    idx += 1;
                }
            }
        }
        Self { coeffs }
    }
}

/// FIPS 204 `ExpandA(rho)` (`Algorithm 32`): returns `k x ell` matrix $\hat{\mathbf{A}}$ in NTT domain.
pub fn expand_a_ntt(params: &MlDsaParams, rho: &[u8; 32]) -> Vec<Vec<Poly256>> {
    let mut mat = Vec::with_capacity(params.k);
    for i in 0..params.k {
        let mut row = Vec::with_capacity(params.ell);
        for j in 0..params.ell {
            row.push(Poly256::rej_ntt_shake128(rho, j as u8, i as u8));
        }
        mat.push(row);
    }
    mat
}

/// Multiply NTT matrix $\hat{\mathbf{A}} \in \mathcal{R}_q^{k \times \ell}$ by NTT vector $\hat{\mathbf{v}} \in \mathcal{R}_q^\ell$.
pub fn mat_vec_mul_ntt(mat_ntt: &[Vec<Poly256>], vec_ntt: &[Poly256]) -> Vec<Poly256> {
    let mut out = Vec::with_capacity(mat_ntt.len());
    for row in mat_ntt {
        let mut acc = Poly256::zero();
        for (a_ij, v_j) in row.iter().zip(vec_ntt.iter()) {
            acc = acc.add(&a_ij.pointwise_mul(v_j));
        }
        out.push(acc);
    }
    out
}

/// FIPS 204 `Power2Round(r)` (`Algorithm 35`, $d = 13$): returns `(r1, r0_mod_q)` in constant time.
#[inline]
pub fn power2round(r: u32) -> (u32, u32) {
    let low = r & 0x1FFF;
    let gt_half = ct_lt_u64(4096, low as u64);
    // Centered `r0 in (-4096, 4096]` represented mod `q`:
    let r0_mod_q = ct_select_u64(
        gt_half,
        (MLDSA_Q as u64) - (8192 - (low as u64)),
        low as u64,
    ) as u32;
    let diff = ct_select_u64(gt_half, (r + 8192 - low) as u64, (r - low) as u64) as u32;
    let r1 = diff >> 13;
    (r1, r0_mod_q)
}

/// Division-free, branchless FIPS 204 `Decompose(r)` (`Algorithm 36`):
/// Returns `(r1, r0_signed)` with `r0_signed in [-gamma2, gamma2]` and **0 hardware `div`/`rem`**!
#[inline]
pub fn decompose_ct(r: u32, gamma2: u32) -> (u32, i32) {
    const ALPHA_88: u128 = 2 * ((MLDSA_Q - 1) / 88) as u128;
    const ALPHA_32: u128 = 2 * ((MLDSA_Q - 1) / 32) as u128;
    const M48_88: u128 = (1u128 << 48) / ALPHA_88 + 1;
    const M48_32: u128 = (1u128 << 48) / ALPHA_32 + 1;
    let alpha = 2 * gamma2;
    let m48: u128 = if gamma2 == (MLDSA_Q - 1) / 88 {
        M48_88
    } else {
        M48_32
    };
    let q_quot = (((r as u128) * m48) >> 48) as u32;
    let rem = r - q_quot * alpha; // exact `r % alpha` in `[0, alpha)`!

    let gt_g2 = ct_lt_u64(gamma2 as u64, rem as u64);
    let r0_base = ct_select_u64(gt_g2, (rem as i64 - alpha as i64) as u64, rem as u64) as i32;
    let r_minus_r0 = (r as i32) - r0_base;

    // Corner wrap at `r - r0 == q - 1`: set `r1 = 0, r0 = r0_base - 1`
    let is_top = r_minus_r0 == (MLDSA_Q - 1) as i32;
    let base_r1 = q_quot + (gt_g2 as u32);
    let r1 = ct_select_u64(is_top, 0, base_r1 as u64) as u32;
    let r0 = ct_select_u64(is_top, (r0_base - 1) as u64, r0_base as u64) as i32;
    (r1, r0)
}

#[inline]
pub fn high_bits_ct(r: u32, gamma2: u32) -> u32 {
    decompose_ct(r, gamma2).0
}

#[inline]
pub fn low_bits_abs_ct(r: u32, gamma2: u32) -> u32 {
    let (_, r0) = decompose_ct(r, gamma2);
    let neg = r0 < 0;
    ct_select_u64(neg, (-r0) as u64, r0 as u64) as u32
}

/// FIPS 204 `MakeHint(z, r)` (`Algorithm 39`).
#[inline]
pub fn make_hint_ct(z_mod_q: u32, r_mod_q: u32, gamma2: u32) -> u8 {
    let r1 = high_bits_ct(r_mod_q, gamma2);
    let v1 = high_bits_ct(fq_add(r_mod_q, z_mod_q), gamma2);
    (r1 != v1) as u8
}

/// FIPS 204 `UseHint(h, r)` (`Algorithm 40`).
#[inline]
pub fn use_hint(hint: u8, r_mod_q: u32, gamma2: u32) -> u32 {
    let m = if gamma2 == (MLDSA_Q - 1) / 88 {
        44u32
    } else {
        16u32
    };
    let (r1, r0) = decompose_ct(r_mod_q, gamma2);
    if hint == 0 {
        return r1;
    }
    if r0 > 0 {
        if r1 + 1 == m { 0 } else { r1 + 1 }
    } else if r1 == 0 {
        m - 1
    } else {
        r1 - 1
    }
}

/// FIPS 204 `SampleInBall(c_tilde)` (`Algorithm 29`) on public challenge seed `c_tilde`.
pub fn sample_in_ball(c_tilde: &[u8], tau: usize) -> Poly256 {
    let mut sp = Shake256::new();
    sp.absorb(c_tilde);
    sp.finalize(0x1F);

    let mut sign_bytes = [0u8; 8];
    sp.squeeze(&mut sign_bytes);
    let mut signs = u64::from_le_bytes(sign_bytes);

    let mut coeffs = [0u32; MLDSA_N];
    let mut one_byte = [0u8; 1];
    for i in (MLDSA_N - tau)..MLDSA_N {
        let j = loop {
            sp.squeeze(&mut one_byte);
            let b = one_byte[0] as usize;
            if b <= i {
                break b;
            }
        };
        coeffs[i] = coeffs[j];
        coeffs[j] = if (signs & 1) == 1 { MLDSA_Q - 1 } else { 1 };
        signs >>= 1;
    }
    Poly256 { coeffs }
}

// ============================================================================
// Exact FIPS 204 Bit-Packing (`pkEncode`, `pkDecode`, `w1Encode`, `sigEncode`, `sigDecode`)
// ============================================================================

fn pack_t1_poly(t1: &Poly256, out: &mut [u8]) {
    debug_assert_eq!(out.len(), 320);
    for i in 0..64 {
        let c0 = t1.coeffs[4 * i];
        let c1 = t1.coeffs[4 * i + 1];
        let c2 = t1.coeffs[4 * i + 2];
        let c3 = t1.coeffs[4 * i + 3];
        out[5 * i] = (c0 & 0xFF) as u8;
        out[5 * i + 1] = (((c0 >> 8) & 0x03) | ((c1 & 0x3F) << 2)) as u8;
        out[5 * i + 2] = (((c1 >> 6) & 0x0F) | ((c2 & 0x0F) << 4)) as u8;
        out[5 * i + 3] = (((c2 >> 4) & 0x3F) | ((c3 & 0x03) << 6)) as u8;
        out[5 * i + 4] = ((c3 >> 2) & 0xFF) as u8;
    }
}

fn unpack_t1_poly(bytes: &[u8]) -> Poly256 {
    debug_assert_eq!(bytes.len(), 320);
    let mut coeffs = [0u32; MLDSA_N];
    for i in 0..64 {
        let b0 = bytes[5 * i] as u32;
        let b1 = bytes[5 * i + 1] as u32;
        let b2 = bytes[5 * i + 2] as u32;
        let b3 = bytes[5 * i + 3] as u32;
        let b4 = bytes[5 * i + 4] as u32;
        coeffs[4 * i] = (b0 | (b1 << 8)) & 0x3FF;
        coeffs[4 * i + 1] = ((b1 >> 2) | (b2 << 6)) & 0x3FF;
        coeffs[4 * i + 2] = ((b2 >> 4) | (b3 << 4)) & 0x3FF;
        coeffs[4 * i + 3] = ((b3 >> 6) | (b4 << 2)) & 0x3FF;
    }
    Poly256 { coeffs }
}

/// FIPS 204 `pkEncode(rho, t1)` (`Algorithm 22`).
pub fn pk_encode(params: &MlDsaParams, rho: &[u8; 32], t1: &[Poly256]) -> Vec<u8> {
    assert_eq!(t1.len(), params.k);
    let mut out = vec![0u8; params.pk_bytes];
    out[0..32].copy_from_slice(rho);
    for (i, p) in t1.iter().enumerate() {
        pack_t1_poly(p, &mut out[32 + i * 320..32 + (i + 1) * 320]);
    }
    out
}

/// FIPS 204 `pkDecode(pk)` (`Algorithm 23`).
pub fn pk_decode(params: &MlDsaParams, pk_bytes: &[u8]) -> Option<([u8; 32], Vec<Poly256>)> {
    if pk_bytes.len() != params.pk_bytes {
        return None;
    }
    let mut rho = [0u8; 32];
    rho.copy_from_slice(&pk_bytes[0..32]);
    let mut t1 = Vec::with_capacity(params.k);
    for i in 0..params.k {
        t1.push(unpack_t1_poly(&pk_bytes[32 + i * 320..32 + (i + 1) * 320]));
    }
    Some((rho, t1))
}

/// FIPS 204 `w1Encode(w1)` (`Algorithm 28`).
pub fn w1_encode(params: &MlDsaParams, w1: &[Poly256]) -> Vec<u8> {
    let mut out = vec![0u8; params.k * params.w1_poly_bytes];
    for (p_idx, poly) in w1.iter().enumerate() {
        let dst = &mut out[p_idx * params.w1_poly_bytes..(p_idx + 1) * params.w1_poly_bytes];
        if params.w1_poly_bytes == 192 {
            // 6 bits per coeff (`4` coeffs -> `3` bytes)
            for i in 0..64 {
                let c0 = poly.coeffs[4 * i] & 0x3F;
                let c1 = poly.coeffs[4 * i + 1] & 0x3F;
                let c2 = poly.coeffs[4 * i + 2] & 0x3F;
                let c3 = poly.coeffs[4 * i + 3] & 0x3F;
                dst[3 * i] = (c0 | (c1 << 6)) as u8;
                dst[3 * i + 1] = ((c1 >> 2) | (c2 << 4)) as u8;
                dst[3 * i + 2] = ((c2 >> 4) | (c3 << 2)) as u8;
            }
        } else {
            // 4 bits per coeff (`2` coeffs -> `1` byte)
            for (i, slot) in dst.iter_mut().enumerate().take(128) {
                let c0 = poly.coeffs[2 * i] & 0x0F;
                let c1 = poly.coeffs[2 * i + 1] & 0x0F;
                *slot = (c0 | (c1 << 4)) as u8;
            }
        }
    }
    out
}

fn pack_z_poly(params: &MlDsaParams, z: &Poly256, dst: &mut [u8]) {
    let g1 = params.gamma1 as i32;
    let map_coeff = |c: u32| -> u32 {
        let signed = if c > MLDSA_Q / 2 {
            (c as i32) - (MLDSA_Q as i32)
        } else {
            c as i32
        };
        (g1 - signed) as u32
    };
    if params.z_poly_bytes == 576 {
        // 18 bits per coeff (`4` coeffs -> `9` bytes)
        for i in 0..64 {
            let v0 = map_coeff(z.coeffs[4 * i]) & 0x3_FFFF;
            let v1 = map_coeff(z.coeffs[4 * i + 1]) & 0x3_FFFF;
            let v2 = map_coeff(z.coeffs[4 * i + 2]) & 0x3_FFFF;
            let v3 = map_coeff(z.coeffs[4 * i + 3]) & 0x3_FFFF;
            let acc: u128 =
                (v0 as u128) | ((v1 as u128) << 18) | ((v2 as u128) << 36) | ((v3 as u128) << 54);
            let le = acc.to_le_bytes();
            dst[9 * i..9 * i + 9].copy_from_slice(&le[0..9]);
        }
    } else {
        // 20 bits per coeff (`4` coeffs -> `10` bytes)
        for i in 0..64 {
            let v0 = map_coeff(z.coeffs[4 * i]) & 0xF_FFFF;
            let v1 = map_coeff(z.coeffs[4 * i + 1]) & 0xF_FFFF;
            let v2 = map_coeff(z.coeffs[4 * i + 2]) & 0xF_FFFF;
            let v3 = map_coeff(z.coeffs[4 * i + 3]) & 0xF_FFFF;
            let acc: u128 =
                (v0 as u128) | ((v1 as u128) << 20) | ((v2 as u128) << 40) | ((v3 as u128) << 60);
            let le = acc.to_le_bytes();
            dst[10 * i..10 * i + 10].copy_from_slice(&le[0..10]);
        }
    }
}

fn unpack_z_poly(params: &MlDsaParams, src: &[u8]) -> Poly256 {
    let g1 = params.gamma1 as i32;
    let unmap = |u: u32| -> u32 {
        let signed = g1 - (u as i32);
        ct_select_u64(signed < 0, (signed + MLDSA_Q as i32) as u64, signed as u64) as u32
    };
    let mut coeffs = [0u32; MLDSA_N];
    if params.z_poly_bytes == 576 {
        for i in 0..64 {
            let mut le = [0u8; 16];
            le[0..9].copy_from_slice(&src[9 * i..9 * i + 9]);
            let acc = u128::from_le_bytes(le);
            coeffs[4 * i] = unmap((acc & 0x3_FFFF) as u32);
            coeffs[4 * i + 1] = unmap(((acc >> 18) & 0x3_FFFF) as u32);
            coeffs[4 * i + 2] = unmap(((acc >> 36) & 0x3_FFFF) as u32);
            coeffs[4 * i + 3] = unmap(((acc >> 54) & 0x3_FFFF) as u32);
        }
    } else {
        for i in 0..64 {
            let mut le = [0u8; 16];
            le[0..10].copy_from_slice(&src[10 * i..10 * i + 10]);
            let acc = u128::from_le_bytes(le);
            coeffs[4 * i] = unmap((acc & 0xF_FFFF) as u32);
            coeffs[4 * i + 1] = unmap(((acc >> 20) & 0xF_FFFF) as u32);
            coeffs[4 * i + 2] = unmap(((acc >> 40) & 0xF_FFFF) as u32);
            coeffs[4 * i + 3] = unmap(((acc >> 60) & 0xF_FFFF) as u32);
        }
    }
    Poly256 { coeffs }
}

/// FIPS 204 `sigEncode(c_tilde, z, hints)` (`Algorithm 26`) -> exact `2420` / `3309` / `4627` bytes!
pub fn sig_encode(
    params: &MlDsaParams,
    c_tilde: &[u8],
    z: &[Poly256],
    hints: &[[u8; MLDSA_N]],
) -> Vec<u8> {
    assert_eq!(c_tilde.len(), params.c_tilde_bytes);
    assert_eq!(z.len(), params.ell);
    assert_eq!(hints.len(), params.k);

    let mut out = vec![0u8; params.sig_bytes];
    out[0..params.c_tilde_bytes].copy_from_slice(c_tilde);
    let mut off = params.c_tilde_bytes;
    for poly in z {
        pack_z_poly(params, poly, &mut out[off..off + params.z_poly_bytes]);
        off += params.z_poly_bytes;
    }

    // `HintBitPack` (`Algorithm 20`):
    let hint_buf = &mut out[off..];
    let mut cursor = 0usize;
    for (row_idx, h_row) in hints.iter().enumerate() {
        for (j, &bit) in h_row.iter().enumerate() {
            if bit != 0 {
                hint_buf[cursor] = j as u8;
                cursor += 1;
            }
        }
        hint_buf[params.omega + row_idx] = cursor as u8;
    }
    out
}

/// `(c_tilde, z, hints)` of a decoded signature.
pub type DecodedSignature = (Vec<u8>, Vec<Poly256>, Vec<[u8; MLDSA_N]>);

/// FIPS 204 `sigDecode(sig)` (`Algorithm 27` + strict `HintBitUnpack` `Algorithm 21` validation!).
pub fn sig_decode(params: &MlDsaParams, sig: &[u8]) -> Option<DecodedSignature> {
    if sig.len() != params.sig_bytes {
        return None;
    }
    let c_tilde = sig[0..params.c_tilde_bytes].to_vec();
    let mut off = params.c_tilde_bytes;
    let mut z = Vec::with_capacity(params.ell);
    for _ in 0..params.ell {
        z.push(unpack_z_poly(params, &sig[off..off + params.z_poly_bytes]));
        off += params.z_poly_bytes;
    }

    // Strict `HintBitUnpack` (`Algorithm 21`): rejects unsorted indices, `count > omega`, or nonzero padding!
    let y = &sig[off..];
    let mut hints = vec![[0u8; MLDSA_N]; params.k];
    let mut k_idx = 0usize;
    for (i, h_row) in hints.iter_mut().enumerate() {
        let end = y[params.omega + i] as usize;
        if end < k_idx || end > params.omega {
            return None;
        }
        let mut first = k_idx;
        while first < end {
            if first > k_idx && y[first] <= y[first - 1] {
                return None;
            }
            h_row[y[first] as usize] = 1;
            first += 1;
        }
        k_idx = end;
    }
    for &pad_byte in &y[k_idx..params.omega] {
        if pad_byte != 0 {
            return None;
        }
    }
    Some((c_tilde, z, hints))
}

/// Compute FIPS 204 message representative $\mu = \text{SHAKE256}(\text{tr} \| [0, |\text{ctx}|] \| \text{ctx} \| M, 64)$
/// where $\text{tr} = \text{SHAKE256}(\text{pk}, 64)$.
pub fn compute_fips204_mu(pk_bytes: &[u8], msg: &[u8], ctx: &[u8]) -> Option<[u8; 64]> {
    if ctx.len() > 255 {
        return None;
    }
    let mut tr = [0u8; 64];
    let mut sp_tr = Shake256::new();
    sp_tr.absorb(pk_bytes);
    sp_tr.finalize(0x1F);
    sp_tr.squeeze(&mut tr);

    let mut sp_mu = Shake256::new();
    sp_mu.absorb(&tr);
    sp_mu.absorb(&[0x00, ctx.len() as u8]);
    sp_mu.absorb(ctx);
    sp_mu.absorb(msg);
    sp_mu.finalize(0x1F);
    let mut mu = [0u8; 64];
    sp_mu.squeeze(&mut mu);
    Some(mu)
}

/// Standalone **100% Standard NIST `FIPS 204` `ML-DSA.Verify`** (`Algorithm 3` + `Algorithm 8`)!
/// Accepts standard `(pk_bytes, msg, ctx, sig_bytes)` with zero threshold-specific modifications.
pub fn ml_dsa_verify(
    level: MlDsaLevel,
    pk_bytes: &[u8],
    msg: &[u8],
    ctx: &[u8],
    sig_bytes: &[u8],
) -> bool {
    let params = level.params();
    let Some((rho, t1)) = pk_decode(&params, pk_bytes) else {
        return false;
    };
    let Some((c_tilde, z, hints)) = sig_decode(&params, sig_bytes) else {
        return false;
    };

    // 1. Check `||z||_inf < gamma1 - beta`
    let z_bound = params.gamma1 - params.beta;
    for z_poly in &z {
        if z_poly.inf_norm() >= z_bound {
            return false;
        }
    }

    let Some(mu) = compute_fips204_mu(pk_bytes, msg, ctx) else {
        return false;
    };

    // 2. Expand `A_hat`, `c = SampleInBall(c_tilde)`, `c_hat = NTT(c)`
    let a_hat = expand_a_ntt(&params, &rho);
    let mut c_hat = sample_in_ball(&c_tilde, params.tau);
    c_hat.ntt();

    let mut z_hat = z;
    for p in &mut z_hat {
        p.ntt();
    }
    let az_hat = mat_vec_mul_ntt(&a_hat, &z_hat);

    // 3. Compute `w'_approx = NTT^{-1}(A_hat * z_hat - c_hat * NTT(t1 * 2^d))` and `w'_1 = UseHint(h, w'_approx)`
    let mut w1_prime = Vec::with_capacity(params.k);
    for (row, hint_row) in hints.iter().enumerate() {
        let mut t1_scaled = Poly256::zero();
        for (out, &value) in t1_scaled.coeffs.iter_mut().zip(&t1[row].coeffs) {
            *out = (value << MLDSA_D) % MLDSA_Q;
        }
        t1_scaled.ntt();
        let ct1_hat = c_hat.pointwise_mul(&t1_scaled);
        let mut w_approx = az_hat[row].sub(&ct1_hat);
        w_approx.inv_ntt();

        let mut w1_row = Poly256::zero();
        for ((out, &hint), &value) in w1_row.coeffs.iter_mut().zip(hint_row).zip(&w_approx.coeffs) {
            *out = use_hint(hint, value, params.gamma2);
        }
        w1_prime.push(w1_row);
    }

    // 4. Recompute `c_tilde' = SHAKE256(mu || w1Encode(w'_1), c_tilde_bytes)` and compare in constant time!
    let w1_bytes = w1_encode(&params, &w1_prime);
    let mut sp_c = Shake256::new();
    sp_c.absorb(&mu);
    sp_c.absorb(&w1_bytes);
    sp_c.finalize(0x1F);
    let mut c_prime = vec![0u8; params.c_tilde_bytes];
    sp_c.squeeze(&mut c_prime);

    ct_eq_bytes(&c_tilde, &c_prime)
}

/// Expanded private signing material. Secret polynomials stay in the NTT domain.
pub struct MlDsaSigningKey {
    level: MlDsaLevel,
    rho: [u8; 32],
    key: SecretBytes<32>,
    public_key: Vec<u8>,
    s1: SecretPolys,
    s2: SecretPolys,
    t0: SecretPolys,
}

impl core::fmt::Debug for MlDsaSigningKey {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("MlDsaSigningKey")
            .field("level", &self.level)
            .field("secret", &"<REDACTED>")
            .finish()
    }
}

struct SecretBytes<const N: usize>([u8; N]);
impl<const N: usize> Drop for SecretBytes<N> {
    fn drop(&mut self) {
        qsag_accel::ct::ct_zeroize_bytes(&mut self.0);
    }
}
struct SecretPolys(Vec<Poly256>);
impl Drop for SecretPolys {
    fn drop(&mut self) {
        for p in &mut self.0 {
            p.zeroize();
        }
    }
}
impl Drop for MlDsaSigningKey {
    fn drop(&mut self) {
        qsag_accel::ct::ct_zeroize_bytes(&mut self.key.0);
        for poly in self
            .s1
            .0
            .iter_mut()
            .chain(&mut self.s2.0)
            .chain(&mut self.t0.0)
        {
            poly.zeroize();
        }
    }
}

fn expand_secret_poly(seed: &[u8; 64], nonce: u16, eta: u32) -> Poly256 {
    let mut xof = Shake256::new();
    xof.absorb(seed);
    xof.absorb(&nonce.to_le_bytes());
    xof.finalize(0x1f);
    let mut poly = Poly256::zero();
    let mut filled = 0;
    let mut byte = SecretBytes([0; 1]);
    while filled < MLDSA_N {
        xof.squeeze(&mut byte.0);
        for nibble in [byte.0[0] & 15, byte.0[0] >> 4] {
            let valid = if eta == 2 { nibble < 15 } else { nibble < 9 };
            if valid && filled < MLDSA_N {
                let value = if eta == 2 {
                    nibble as u32 % 5
                } else {
                    nibble as u32
                };
                poly.coeffs[filled] = fq_sub(eta, value);
                filled += 1;
            }
        }
    }
    poly
}

/// Deterministic seeded FIPS 204 key generation. The caller supplies an unpredictable seed.
pub fn ml_dsa_keygen_from_seed(level: MlDsaLevel, seed: &[u8; 32]) -> (Vec<u8>, MlDsaSigningKey) {
    let params = level.params();
    let mut expanded = SecretBytes([0; 128]);
    let mut xof = Shake256::new();
    xof.absorb(seed);
    xof.absorb(&[params.k as u8, params.ell as u8]);
    xof.finalize(0x1f);
    xof.squeeze(&mut expanded.0);
    let mut rho = [0; 32];
    rho.copy_from_slice(&expanded.0[..32]);
    let mut private_seed = SecretBytes([0; 64]);
    private_seed.0.copy_from_slice(&expanded.0[32..96]);
    let mut key = SecretBytes([0; 32]);
    key.0.copy_from_slice(&expanded.0[96..]);
    let mut s1 = SecretPolys(
        (0..params.ell)
            .map(|index| expand_secret_poly(&private_seed.0, index as u16, params.eta))
            .collect(),
    );
    let mut s2 = SecretPolys(
        (0..params.k)
            .map(|index| {
                expand_secret_poly(&private_seed.0, (params.ell + index) as u16, params.eta)
            })
            .collect(),
    );
    for poly in s1.0.iter_mut().chain(&mut s2.0) {
        poly.ntt();
    }
    let matrix = expand_a_ntt(&params, &rho);
    let mut t = SecretPolys(mat_vec_mul_ntt(&matrix, &s1.0));
    let mut t1 = Vec::with_capacity(params.k);
    let mut t0 = SecretPolys(Vec::with_capacity(params.k));
    for (row, error) in t.0.iter_mut().zip(&s2.0) {
        *row = row.add(error);
        row.inv_ntt();
        let mut high = Poly256::zero();
        let mut low = Poly256::zero();
        for ((hi, lo), &value) in high.coeffs.iter_mut().zip(&mut low.coeffs).zip(&row.coeffs) {
            (*hi, *lo) = power2round(value);
        }
        low.ntt();
        t0.0.push(low);
        t1.push(high);
    }
    let public_key = pk_encode(&params, &rho, &t1);
    (
        public_key.clone(),
        MlDsaSigningKey {
            level,
            rho,
            key,
            public_key,
            s1,
            s2,
            t0,
        },
    )
}

/// Test-only: builds a standard signing key from explicit short secrets
/// (coefficient form), exactly as key generation does after sampling.
#[cfg(test)]
pub(crate) fn signing_key_from_secret_for_test(
    level: MlDsaLevel,
    rho: [u8; 32],
    s1: Vec<Poly256>,
    s2: Vec<Poly256>,
) -> (Vec<u8>, MlDsaSigningKey) {
    let params = level.params();
    let mut s1 = SecretPolys(s1);
    let mut s2 = SecretPolys(s2);
    for poly in s1.0.iter_mut().chain(&mut s2.0) {
        poly.ntt();
    }
    let matrix = expand_a_ntt(&params, &rho);
    let mut t = mat_vec_mul_ntt(&matrix, &s1.0);
    let mut t1 = Vec::with_capacity(params.k);
    let mut t0 = SecretPolys(Vec::with_capacity(params.k));
    for (row, error) in t.iter_mut().zip(&s2.0) {
        *row = row.add(error);
        row.inv_ntt();
        let mut high = Poly256::zero();
        let mut low = Poly256::zero();
        for ((hi, lo), &value) in high.coeffs.iter_mut().zip(&mut low.coeffs).zip(&row.coeffs) {
            (*hi, *lo) = power2round(value);
        }
        low.ntt();
        t0.0.push(low);
        t1.push(high);
    }
    let public_key = pk_encode(&params, &rho, &t1);
    (
        public_key.clone(),
        MlDsaSigningKey { level, rho, key: SecretBytes([0x5A; 32]), public_key, s1, s2, t0 },
    )
}

fn expand_signing_mask(params: &MlDsaParams, seed: &[u8; 64], nonce: u16) -> Poly256 {
    let mut xof = Shake256::new();
    xof.absorb(seed);
    xof.absorb(&nonce.to_le_bytes());
    xof.finalize(0x1f);
    let mut bytes = SecretBytes([0; 640]);
    xof.squeeze(&mut bytes.0[..params.z_poly_bytes]);
    unpack_z_poly(params, &bytes.0[..params.z_poly_bytes])
}

/// Deterministic FIPS 204 signing, using the all-zero optional randomness string.
/// Returns `None` for an oversized context or exhausted 16-bit mask counter.
pub fn ml_dsa_sign_deterministic(sk: &MlDsaSigningKey, msg: &[u8], ctx: &[u8]) -> Option<Vec<u8>> {
    let params = sk.level.params();
    let mu = compute_fips204_mu(&sk.public_key, msg, ctx)?;
    let mut mask_seed = SecretBytes([0; 64]);
    let mut xof = Shake256::new();
    xof.absorb(&sk.key.0);
    xof.absorb(&[0; 32]);
    xof.absorb(&mu);
    xof.finalize(0x1f);
    xof.squeeze(&mut mask_seed.0);
    let matrix = expand_a_ntt(&params, &sk.rho);
    let mut nonce = 0u16;
    loop {
        let next = nonce.checked_add(params.ell as u16)?;
        let y = SecretPolys(
            (nonce..next)
                .map(|index| expand_signing_mask(&params, &mask_seed.0, index))
                .collect(),
        );
        nonce = next;
        let mut y_hat = SecretPolys(y.0.clone());
        for poly in &mut y_hat.0 {
            poly.ntt();
        }
        let mut w = SecretPolys(mat_vec_mul_ntt(&matrix, &y_hat.0));
        for poly in &mut w.0 {
            poly.inv_ntt();
        }
        let w1: Vec<Poly256> =
            w.0.iter()
                .map(|p| Poly256 {
                    coeffs: p.coeffs.map(|c| high_bits_ct(c, params.gamma2)),
                })
                .collect();
        let mut challenge = vec![0; params.c_tilde_bytes];
        let mut h = Shake256::new();
        h.absorb(&mu);
        h.absorb(&w1_encode(&params, &w1));
        h.finalize(0x1f);
        h.squeeze(&mut challenge);
        let mut c = sample_in_ball(&challenge, params.tau);
        c.ntt();
        let mut z = SecretPolys(Vec::with_capacity(params.ell));
        let mut reject = false;
        for (mask, secret) in y.0.iter().zip(&sk.s1.0) {
            let mut response = c.pointwise_mul(secret);
            response.inv_ntt();
            response = response.add(mask);
            reject |= response.inf_norm() >= params.gamma1 - params.beta;
            z.0.push(response);
        }
        let mut hints = vec![[0; MLDSA_N]; params.k];
        let mut ones = 0usize;
        for (((row, secret), low), hint_row) in
            w.0.iter().zip(&sk.s2.0).zip(&sk.t0.0).zip(&mut hints)
        {
            let mut cs2 = c.pointwise_mul(secret);
            cs2.inv_ntt();
            let mut ct0 = c.pointwise_mul(low);
            ct0.inv_ntt();
            reject |= ct0.inf_norm() >= params.gamma2;
            for (((&wi, &ei), &ti), hint) in row
                .coeffs
                .iter()
                .zip(&cs2.coeffs)
                .zip(&ct0.coeffs)
                .zip(hint_row)
            {
                let base = fq_sub(wi, ei);
                reject |= low_bits_abs_ct(base, params.gamma2) >= params.gamma2 - params.beta;
                *hint = make_hint_ct(fq_sub(0, ti), fq_add(base, ti), params.gamma2);
                ones += *hint as usize;
            }
            cs2.zeroize();
            ct0.zeroize();
        }
        if !reject && ones <= params.omega {
            return Some(sig_encode(&params, &challenge, &z.0, &hints));
        }
    }
}

#[cfg(test)]
mod signing_tests {
    use super::*;
    #[test]
    fn deterministic_signing_all_levels() {
        for level in [
            MlDsaLevel::MlDsa44,
            MlDsaLevel::MlDsa65,
            MlDsaLevel::MlDsa87,
        ] {
            let (pk, sk) = ml_dsa_keygen_from_seed(level, &[0x61; 32]);
            let sig = ml_dsa_sign_deterministic(&sk, b"message", b"context").unwrap();
            assert!(ml_dsa_verify(level, &pk, b"message", b"context", &sig));
            assert!(!ml_dsa_verify(level, &pk, b"changed", b"context", &sig));
            assert!(!ml_dsa_verify(level, &pk, b"message", b"other", &sig));
            assert_eq!(
                Some(sig),
                ml_dsa_sign_deterministic(&sk, b"message", b"context")
            );
            assert!(ml_dsa_sign_deterministic(&sk, b"message", &[0; 256]).is_none());
        }
    }
}

#[cfg(test)]
mod nist_key_vectors {
    use super::*;
    #[test]
    fn seeded_public_keys_match_nist_acvp() {
        {
            let (pk, _) = ml_dsa_keygen_from_seed(
                MlDsaLevel::MlDsa44,
                &[
                    113, 148, 177, 60, 149, 35, 16, 16, 175, 210, 201, 9, 153, 43, 210, 0, 59, 166,
                    244, 55, 195, 136, 107, 219, 227, 246, 184, 103, 161, 75, 161, 97,
                ],
            );
            let mut xof = Shake256::new();
            xof.absorb(&pk);
            xof.finalize(0x1f);
            let mut digest = [0; 32];
            xof.squeeze(&mut digest);
            assert_eq!(
                digest,
                [
                    13, 179, 34, 53, 148, 161, 252, 232, 219, 72, 200, 241, 121, 54, 17, 161, 127,
                    204, 0, 6, 255, 234, 38, 207, 112, 148, 216, 50, 80, 55, 40, 143
                ]
            );
        }
        {
            let (pk, _) = ml_dsa_keygen_from_seed(
                MlDsaLevel::MlDsa65,
                &[
                    169, 145, 253, 66, 176, 113, 212, 156, 72, 174, 62, 117, 198, 71, 69, 158, 13,
                    170, 209, 225, 186, 53, 106, 4, 128, 25, 18, 211, 41, 75, 207, 248,
                ],
            );
            let mut xof = Shake256::new();
            xof.absorb(&pk);
            xof.finalize(0x1f);
            let mut digest = [0; 32];
            xof.squeeze(&mut digest);
            assert_eq!(
                digest,
                [
                    236, 57, 176, 12, 144, 49, 225, 78, 151, 45, 35, 176, 102, 64, 52, 45, 26, 120,
                    250, 93, 240, 239, 18, 170, 50, 54, 165, 10, 198, 231, 189, 143
                ]
            );
        }
        {
            let (pk, _) = ml_dsa_keygen_from_seed(
                MlDsaLevel::MlDsa87,
                &[
                    161, 111, 91, 7, 150, 112, 62, 45, 26, 1, 64, 163, 92, 191, 54, 239, 171, 231,
                    14, 117, 43, 165, 155, 106, 154, 14, 156, 75, 5, 48, 47, 115,
                ],
            );
            let mut xof = Shake256::new();
            xof.absorb(&pk);
            xof.finalize(0x1f);
            let mut digest = [0; 32];
            xof.squeeze(&mut digest);
            assert_eq!(
                digest,
                [
                    38, 116, 168, 255, 113, 81, 180, 147, 251, 69, 45, 170, 146, 10, 95, 235, 92,
                    229, 232, 215, 6, 119, 115, 92, 5, 67, 174, 194, 187, 22, 28, 7
                ]
            );
        }
    }
}

// NIST ACVP seed-format, deterministic, external pure-message vectors.
#[cfg(test)]
mod nist_signature_vectors {
    use super::*;
    #[test]
    fn signatures_match_nist_acvp() {
        {
            let (_, sk) = ml_dsa_keygen_from_seed(
                MlDsaLevel::MlDsa44,
                &[
                    152, 160, 174, 46, 10, 243, 60, 250, 7, 47, 174, 128, 172, 188, 228, 176, 253,
                    125, 39, 199, 131, 192, 140, 66, 191, 145, 120, 72, 12, 109, 75, 175,
                ],
            );
            let signature = ml_dsa_sign_deterministic(
                &sk,
                &[180],
                &[
                    186, 50, 45, 115, 142, 160, 192, 225, 244, 249, 141, 18, 73, 173, 109, 68, 164,
                    19, 82, 169, 231, 111, 239, 50, 146, 250, 177, 151, 7, 11, 116, 29, 191, 209,
                    235, 7, 235, 148, 87, 8, 168, 94, 131, 3, 205, 136, 225, 213, 196, 208, 219,
                    131, 57, 103, 247, 165, 58, 25, 8,
                ],
            )
            .unwrap();
            let mut xof = Shake256::new();
            xof.absorb(&signature);
            xof.finalize(0x1f);
            let mut digest = [0; 32];
            xof.squeeze(&mut digest);
            assert_eq!(
                digest,
                [
                    217, 11, 108, 209, 48, 20, 215, 31, 234, 88, 23, 51, 172, 22, 14, 55, 215, 203,
                    207, 190, 238, 48, 52, 33, 220, 213, 187, 220, 190, 78, 51, 254
                ]
            );
        }
        {
            let (_, sk) = ml_dsa_keygen_from_seed(
                MlDsaLevel::MlDsa65,
                &[
                    242, 122, 234, 254, 137, 17, 144, 237, 193, 221, 109, 189, 154, 130, 58, 2,
                    150, 28, 90, 8, 62, 238, 114, 200, 185, 32, 167, 183, 20, 91, 148, 91,
                ],
            );
            let signature = ml_dsa_sign_deterministic(
                &sk,
                &[155],
                &[
                    70, 126, 37, 117, 60, 101, 236, 70, 192, 84, 236, 3, 183, 145, 106, 33, 219, 3,
                    139, 211, 34, 175, 231, 242, 237, 185, 27, 73, 39, 190, 229, 188, 59, 235, 90,
                    52, 218, 182, 70, 226, 66, 3, 153, 80, 122, 133, 165, 51, 82, 76, 182, 154,
                    225, 31, 221, 161, 179, 255, 43, 130, 72, 47, 73, 90, 165, 103, 137, 93, 196,
                    188, 109, 145, 157, 109, 243, 0, 80, 154, 242, 24, 60, 100, 121, 113, 24, 139,
                    35, 196, 72, 31, 241, 71, 71, 227, 80, 54, 3, 234, 235, 108, 158, 225, 152,
                    204, 189, 206, 37, 5, 228, 38, 192, 164, 71, 114, 101, 153, 102, 77, 68, 144,
                    211, 39, 63, 93, 136, 43, 96, 194, 115, 215, 38, 17, 62, 58, 139, 161, 253,
                    223, 190, 93, 27, 247, 235, 136, 124, 122, 114, 167, 165, 195, 14, 42, 252, 42,
                    166, 41, 131, 149, 172, 124, 44, 65, 252, 207, 174, 61, 30, 186, 26, 11, 93,
                    116, 119, 64, 187, 122, 80, 194, 242, 53, 167, 140, 3, 112, 167, 213, 79, 93,
                    245, 165, 173, 90, 84, 54, 158, 214, 113, 60, 74, 111, 175, 26, 51, 169, 52,
                    182, 255, 75, 135, 155, 207, 49, 240, 0, 178, 202, 24, 110, 12, 249, 173, 205,
                    213, 77, 181, 145, 42, 118, 140, 66, 22, 32, 243, 227, 53, 89, 86, 27, 222,
                    180, 206, 252, 43, 202, 243, 98,
                ],
            )
            .unwrap();
            let mut xof = Shake256::new();
            xof.absorb(&signature);
            xof.finalize(0x1f);
            let mut digest = [0; 32];
            xof.squeeze(&mut digest);
            assert_eq!(
                digest,
                [
                    121, 156, 73, 178, 43, 102, 14, 153, 44, 252, 131, 109, 236, 132, 211, 68, 43,
                    115, 240, 117, 143, 209, 62, 247, 3, 250, 178, 194, 97, 50, 190, 136
                ]
            );
        }
        {
            let (_, sk) = ml_dsa_keygen_from_seed(
                MlDsaLevel::MlDsa87,
                &[
                    241, 66, 33, 72, 75, 202, 212, 149, 195, 236, 70, 126, 132, 61, 130, 242, 222,
                    95, 60, 109, 83, 185, 71, 171, 84, 220, 96, 41, 68, 8, 139, 238,
                ],
            );
            let signature = ml_dsa_sign_deterministic(
                &sk,
                &[236],
                &[
                    0, 166, 235, 255, 124, 159, 230, 108, 169, 95, 95, 192, 105, 177, 30, 68, 217,
                    39, 173, 205, 103,
                ],
            )
            .unwrap();
            let mut xof = Shake256::new();
            xof.absorb(&signature);
            xof.finalize(0x1f);
            let mut digest = [0; 32];
            xof.squeeze(&mut digest);
            assert_eq!(
                digest,
                [
                    149, 97, 117, 195, 215, 19, 134, 146, 199, 236, 47, 34, 27, 78, 176, 188, 225,
                    38, 48, 56, 195, 136, 165, 126, 133, 61, 8, 222, 22, 112, 86, 56
                ]
            );
        }
    }
}
