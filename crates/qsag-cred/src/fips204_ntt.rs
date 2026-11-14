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
/// $\lceil 2^{46} / 8\_380\_417 \rceil = 8\_396\_807$.
/// Wait: for exact `0`-division over all `a, b < q` (`a*b < 2^{46}`), let
/// $M_{64} = \lfloor 2^{64} / 8\_380\_417 \rfloor = 2\_201\_154\_512\_929$:
/// $q_{\text{est}} = \lfloor (a b \cdot M_{64}) / 2^{64} \rfloor \in \{\lfloor ab/q \rfloor - 1, \lfloor ab/q \rfloor\}$,
/// so 1 branchless conditional subtraction of $q$ reduces `ab - q_est * q` into `[0, q)` with
/// **ZERO hardware `div`/`rem` instructions**!
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
