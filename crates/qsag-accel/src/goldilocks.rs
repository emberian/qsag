//! Canonical constant-time Goldilocks field ($p = 2^{64} - 2^{32} + 1$), quadratic extension
//! $\mathbb{F}_{p^2} = \mathbb{F}_p[u]/(u^2 - 7)$, injective 5-limb 56-bit digest framing,
//! radix-2 NTT, and shifted-coset Reed-Solomon LDE over $\mathbb{F}_{p^2}$.

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

use crate::AccelError;
use crate::ct::{ct_eq_u64, ct_select_u64};

/// Canonical Goldilocks prime $p = 2^{64} - 2^{32} + 1$.
pub const GOLDILOCKS_PRIME: u64 = 0xFFFF_FFFF_0000_0001;
/// Reduction constant $\epsilon = 2^{32} - 1 = 2^{64} - p$.
pub const GOLDILOCKS_EPSILON: u64 = 0xFFFF_FFFF;
/// Multiplicative generator $g = 7$ of $\mathbb{F}_p^\times$ and non-residue for $\mathbb{F}_{p^2}$.
pub const GOLDILOCKS_GENERATOR: u64 = 7;
/// Primitive $2^{32}$-th root of unity $\omega_{2^{32}} = 7^{2^{32} - 1} \bmod p$.
pub const GOLDILOCKS_ROOT_2_32: u64 = 1_753_635_133_440_165_772;
/// Maximum 2-adicity of $\mathbb{F}_p^\times$.
pub const GOLDILOCKS_TWO_ADICITY: u32 = 32;

/// Strictly check `raw < GOLDILOCKS_PRIME` without reducing aliases in $[p, 2^{64})$.
#[inline]
pub const fn gl_is_canonical(raw: u64) -> bool {
    raw < GOLDILOCKS_PRIME
}

/// Branchless canonicalization of any `u64` into $[0, p - 1]$.
#[inline]
pub const fn gl_reduce_u64(x: u64) -> u64 {
    let (diff, borrow) = x.overflowing_sub(GOLDILOCKS_PRIME);
    ct_select_u64(borrow, x, diff)
}

/// Branchless modular addition of canonical inputs `a, b < p`.
#[inline]
pub const fn gl_add(a: u64, b: u64) -> u64 {
    let a_c = gl_reduce_u64(a);
    let b_c = gl_reduce_u64(b);
    let rem_p = GOLDILOCKS_PRIME - b_c;
    let (diff, borrow) = a_c.overflowing_sub(rem_p);
    let plain_sum = a_c.wrapping_add(b_c);
    ct_select_u64(borrow, plain_sum, diff)
}

/// Branchless modular subtraction of canonical inputs `a, b < p`.
#[inline]
pub const fn gl_sub(a: u64, b: u64) -> u64 {
    let a_c = gl_reduce_u64(a);
    let b_c = gl_reduce_u64(b);
    let (diff, borrow) = a_c.overflowing_sub(b_c);
    let adj = (borrow as u64).wrapping_neg() & GOLDILOCKS_PRIME;
    diff.wrapping_add(adj)
}

/// Branchless negation `0 - a mod p`.
#[inline]
pub const fn gl_neg(a: u64) -> u64 {
    gl_sub(0, a)
}

/// Branchless 128-to-64 Goldilocks reduction for arbitrary `u128`.
#[inline]
pub const fn gl_reduce128(x: u128) -> u64 {
    let lo = x as u64;
    let hi = (x >> 64) as u64;
    let hi_lo = hi & GOLDILOCKS_EPSILON;
    let hi_hi = hi >> 32;
    // `hi_lo <= 2^32 - 1` implies `(hi_lo << 32) - hi_lo <= (2^32 - 1)^2 < p`.
    let mid = (hi_lo << 32).wrapping_sub(hi_lo);
    let lo_c = gl_reduce_u64(lo);
    gl_sub(gl_add(lo_c, mid), hi_hi)
}

/// Branchless modular multiplication `a * b mod p`.
#[inline]
pub const fn gl_mul(a: u64, b: u64) -> u64 {
    let a_c = gl_reduce_u64(a);
    let b_c = gl_reduce_u64(b);
    gl_reduce128((a_c as u128) * (b_c as u128))
}

/// Branchless squaring `a^2 mod p`.
#[inline]
pub const fn gl_sq(a: u64) -> u64 {
    gl_mul(a, a)
}

#[inline]
const fn gl_exp_pow2(mut x: u64, mut k: u32) -> u64 {
    while k > 0 {
        x = gl_sq(x);
        k -= 1;
    }
    x
}

/// Constant-time Fermat addition chain $a^{p - 2} \bmod p$ (`0` maps to `0` with zero secret branches).
#[inline]
pub const fn gl_inv_or_zero(a: u64) -> u64 {
    let x = gl_reduce_u64(a);
    let t2 = gl_mul(gl_sq(x), x);
    let t3 = gl_mul(gl_sq(t2), x);
    let t6 = gl_mul(gl_exp_pow2(t3, 3), t3);
    let t12 = gl_mul(gl_exp_pow2(t6, 6), t6);
    let t24 = gl_mul(gl_exp_pow2(t12, 12), t12);
    let t30 = gl_mul(gl_exp_pow2(t24, 6), t6);
    let t31 = gl_mul(gl_sq(t30), x);
    let t32 = gl_mul(gl_sq(t31), x);
    let hi = gl_exp_pow2(t31, 33);
    gl_mul(hi, t32)
}

/// Public-exponent binary exponentiation $a^e \bmod p$.
#[inline]
pub const fn gl_pow_pub(a: u64, mut exp: u64) -> u64 {
    let mut base = gl_reduce_u64(a);
    let mut acc = 1u64;
    while exp > 0 {
        if (exp & 1) == 1 {
            acc = gl_mul(acc, base);
        }
        base = gl_sq(base);
        exp >>= 1;
    }
    acc
}

/// Constant-time binary exponentiation $a^e \bmod p$ for secret 64-bit exponents.
#[inline]
pub const fn gl_pow_ct(a: u64, exp: u64) -> u64 {
    let mut base = gl_reduce_u64(a);
    let mut acc = 1u64;
    let mut bit = 0u32;
    while bit < 64 {
        let prod = gl_mul(acc, base);
        let take = ((exp >> bit) & 1) == 1;
        acc = ct_select_u64(take, prod, acc);
        base = gl_sq(base);
        bit += 1;
    }
    acc
}

// ============================================================================
// Quadratic Extension Field F_{p^2} = F_p[u] / (u^2 - 7)
// ============================================================================

#[inline]
pub const fn ext2_add(a: [u64; 2], b: [u64; 2]) -> [u64; 2] {
    [gl_add(a[0], b[0]), gl_add(a[1], b[1])]
}

#[inline]
pub const fn ext2_sub(a: [u64; 2], b: [u64; 2]) -> [u64; 2] {
    [gl_sub(a[0], b[0]), gl_sub(a[1], b[1])]
}

#[inline]
pub const fn ext2_neg(a: [u64; 2]) -> [u64; 2] {
    [gl_neg(a[0]), gl_neg(a[1])]
}

#[inline]
pub const fn ext2_mul(a: [u64; 2], b: [u64; 2]) -> [u64; 2] {
    let v0 = gl_mul(a[0], b[0]);
    let v1 = gl_mul(a[1], b[1]);
    let nr_v1 = gl_mul(GOLDILOCKS_GENERATOR, v1);
    let c0 = gl_add(v0, nr_v1);
    let c1 = gl_sub(
        gl_mul(gl_add(a[0], a[1]), gl_add(b[0], b[1])),
        gl_add(v0, v1),
    );
    [c0, c1]
}

#[inline]
pub const fn ext2_scale_base(a: [u64; 2], s: u64) -> [u64; 2] {
    [gl_mul(a[0], s), gl_mul(a[1], s)]
}

/// Constant-time norm-based inverse in $\mathbb{F}_{p^2}$ (`[0, 0]` maps to `[0, 0]`).
#[inline]
pub const fn ext2_inv_or_zero(a: [u64; 2]) -> [u64; 2] {
    // Norm(a0 + a1 u) = a0^2 - 7 * a1^2 != 0 for all (a0, a1) != (0, 0) since 7 is non-square.
    let norm = gl_sub(gl_sq(a[0]), gl_mul(GOLDILOCKS_GENERATOR, gl_sq(a[1])));
    let inv_norm = gl_inv_or_zero(norm);
    [gl_mul(a[0], inv_norm), gl_neg(gl_mul(a[1], inv_norm))]
}

#[inline]
pub fn ext2_ct_eq(a: [u64; 2], b: [u64; 2]) -> bool {
    ct_eq_u64(gl_reduce_u64(a[0]), gl_reduce_u64(b[0]))
        && ct_eq_u64(gl_reduce_u64(a[1]), gl_reduce_u64(b[1]))
}

// ============================================================================
// Canonical 5-Limb 56-Bit Injective 32-Byte Digest Packing (Zero Mod-p Alias)
// ============================================================================

/// Pack a 32-byte digest injectively into **5 canonical 56-bit Goldilocks limbs** (`< 2^56 < p`).
///
/// Layout: `digest[0..32] || 0x01 || 0x00 || 0x00` = 35 bytes = `5 * 7` big-endian chunks.
/// Eliminates the `[p, 2^64)` modulo-$p$ aliasing vulnerability completely.
#[inline]
pub const fn pack_bytes32_to_limbs56(digest: &[u8; 32]) -> [u64; 5] {
    let mut marked = [0u8; 35];
    let mut i = 0usize;
    while i < 32 {
        marked[i] = digest[i];
        i += 1;
    }
    marked[32] = 0x01;
    let mut out = [0u64; 5];
    let mut limb = 0usize;
    while limb < 5 {
        let base = limb * 7;
        let mut acc = 0u64;
        let mut j = 0usize;
        while j < 7 {
            acc = (acc << 8) | (marked[base + j] as u64);
            j += 1;
        }
        out[limb] = acc;
        limb += 1;
    }
    out
}

/// Strictly invert [`pack_bytes32_to_limbs56`], rejecting any limb `>= 2^56` or malformed delimiter.
#[inline]
pub const fn unpack_limbs56_to_bytes32(limbs: &[u64; 5]) -> Option<[u8; 32]> {
    let mut marked = [0u8; 35];
    let mut limb = 0usize;
    while limb < 5 {
        let v = limbs[limb];
        if v >= (1u64 << 56) {
            return None;
        }
        let base = limb * 7;
        let mut j = 0usize;
        while j < 7 {
            marked[base + (6 - j)] = ((v >> (8 * j)) & 0xFF) as u8;
            j += 1;
        }
        limb += 1;
    }
    if marked[32] != 0x01 || marked[33] != 0x00 || marked[34] != 0x00 {
        return None;
    }
    let mut out = [0u8; 32];
    let mut i = 0usize;
    while i < 32 {
        out[i] = marked[i];
        i += 1;
    }
    Some(out)
}

/// Pack an arbitrary byte slice into canonical `< 2^56` Goldilocks limbs (`0x01` delimiter + `0x00*`),
/// matching `Qsag.bytesToLimbs56` bit-for-bit.
#[cfg(feature = "alloc")]
pub fn pack_slice_to_limbs56(msg: &[u8]) -> Vec<u64> {
    let rem = (msg.len() + 1) % 7;
    let pad_zeros = if rem == 0 { 0 } else { 7 - rem };
    let total_bytes = msg.len() + 1 + pad_zeros;
    let num_limbs = total_bytes / 7;
    let mut out = Vec::with_capacity(num_limbs);
    for limb_idx in 0..num_limbs {
        let base = limb_idx * 7;
        let mut acc = 0u64;
        for j in 0..7 {
            let pos = base + j;
            let b = if pos < msg.len() {
                msg[pos]
            } else if pos == msg.len() {
                0x01
            } else {
                0x00
            };
            acc = (acc << 8) | (b as u64);
        }
        out.push(acc);
    }
    out
}

// ============================================================================
// Radix-2 Goldilocks NTT & Shifted-Coset Ext2 Reed-Solomon LDE
// ============================================================================

/// Return the primitive $2^{\text{log2\_n}}$-th root of unity in $\mathbb{F}_p^\times$ (`log2_n <= 32`).
#[inline]
pub const fn goldilocks_primitive_root(log2_n: u32) -> Result<u64, AccelError> {
    if log2_n > GOLDILOCKS_TWO_ADICITY {
        return Err(AccelError::DomainTooLarge { log2_len: log2_n });
    }
    let mut w = GOLDILOCKS_ROOT_2_32;
    let mut steps = GOLDILOCKS_TWO_ADICITY - log2_n;
    while steps > 0 {
        w = gl_sq(w);
        steps -= 1;
    }
    Ok(w)
}

/// Validate that `len` is a nonzero power of two no larger than $2^{32}$ and return `log2(len)`.
#[inline]
const fn ntt_log2_len(what: &'static str, len: usize) -> Result<u32, AccelError> {
    if !len.is_power_of_two() {
        return Err(AccelError::NotPowerOfTwo { what, len });
    }
    let log2_len = len.trailing_zeros();
    if log2_len > GOLDILOCKS_TWO_ADICITY {
        return Err(AccelError::DomainTooLarge { log2_len });
    }
    Ok(log2_len)
}

/// Precompute forward twiddle powers `[1, omega, omega^2, ..., omega^{n/2 - 1}]` for a power-of-two `n`.
#[cfg(feature = "alloc")]
pub fn precompute_goldilocks_twiddles(n: usize) -> Result<Vec<u64>, AccelError> {
    let log2_n = ntt_log2_len("twiddle domain", n)?;
    let half = n / 2;
    if half == 0 {
        return Ok(Vec::new());
    }
    let omega = goldilocks_primitive_root(log2_n)?;
    let mut twiddles = Vec::with_capacity(half);
    let mut cur = 1u64;
    for _ in 0..half {
        twiddles.push(cur);
        cur = gl_mul(cur, omega);
    }
    Ok(twiddles)
}

/// Check that public `twiddles` is `[1, omega, ..., omega^{n/2 - 1}]` for a primitive `n`-th root
/// of unity `omega` (the table [`precompute_goldilocks_twiddles`] produces for some root).
///
/// Backends that derive stage roots from a few table entries (the Vulkan kernels read only
/// `twiddles[n >> s]`) agree with [`goldilocks_ntt_cpu`] exactly on tables that pass this check.
/// The table is public, so the scan is variable-time.
pub fn check_goldilocks_twiddles(n: usize, twiddles: &[u64]) -> Result<(), AccelError> {
    ntt_log2_len("NTT buffer", n)?;
    if n == 1 {
        return Ok(());
    }
    if twiddles.len() != n / 2 {
        return Err(AccelError::LengthMismatch {
            what: "NTT twiddles",
            expected: n / 2,
            actual: twiddles.len(),
        });
    }
    let mut bad = gl_reduce_u64(twiddles[0]) ^ 1;
    if n >= 4 {
        let omega = twiddles[1];
        for pair in twiddles.windows(2) {
            bad |= gl_reduce_u64(pair[1]) ^ gl_mul(pair[0], omega);
        }
        // omega^{n/2} == -1 makes the order of omega exactly n.
        bad |= gl_mul(twiddles[n / 2 - 1], omega) ^ (GOLDILOCKS_PRIME - 1);
    }
    if bad != 0 {
        return Err(AccelError::InvalidTwiddles);
    }
    Ok(())
}

#[inline]
fn bit_reverse_permute(buf: &mut [u64]) {
    let n = buf.len();
    if n <= 1 {
        return;
    }
    let shift = usize::BITS - n.trailing_zeros();
    for i in 0..n {
        let rev = i.reverse_bits() >> shift;
        if i < rev {
            buf.swap(i, rev);
        }
    }
}

/// In-place constant-time radix-2 Cooley-Tukey NTT (`inverse == false`) and inverse NTT (`inverse == true`)
/// over canonical Goldilocks field elements.
///
/// `twiddles` MUST contain `[1, omega, omega^2, ..., omega^{n/2 - 1}]` where `omega` is a primitive
/// `n`-th root of unity (`twiddles.len() == buf.len() / 2`).
///
/// All shape checks run before `buf` is modified, so an `Err` leaves `buf` untouched.
pub fn goldilocks_ntt_cpu(
    buf: &mut [u64],
    twiddles: &[u64],
    inverse: bool,
) -> Result<(), AccelError> {
    let n = buf.len();
    ntt_log2_len("NTT buffer", n)?;
    if n > 1 && twiddles.len() != n / 2 {
        return Err(AccelError::LengthMismatch {
            what: "NTT twiddles",
            expected: n / 2,
            actual: twiddles.len(),
        });
    }
    for slot in buf.iter_mut() {
        *slot = gl_reduce_u64(*slot);
    }
    if n == 1 {
        return Ok(());
    }

    bit_reverse_permute(buf);

    let mut len = 2usize;
    while len <= n {
        let half = len / 2;
        let step = n / len;
        let mut start = 0usize;
        while start < n {
            for j in 0..half {
                let tw_idx = j * step;
                let w = if !inverse {
                    gl_reduce_u64(twiddles[tw_idx])
                } else if tw_idx == 0 {
                    1u64
                } else {
                    gl_reduce_u64(twiddles[n / 2 - tw_idx])
                };
                // Note: for inverse, `omega^{-k} = -omega^{n/2 - k}` because `omega^{n/2} = -1`!
                let w_eff = if inverse && tw_idx != 0 { gl_neg(w) } else { w };
                let u = buf[start + j];
                let v = gl_mul(buf[start + j + half], w_eff);
                buf[start + j] = gl_add(u, v);
                buf[start + j + half] = gl_sub(u, v);
            }
            start += len;
        }
        len <<= 1;
    }

    if inverse {
        let inv_n = gl_inv_or_zero(n as u64);
        for slot in buf.iter_mut() {
            *slot = gl_mul(*slot, inv_n);
        }
    }
    Ok(())
}

/// Allocation-free in-place radix-2 NTT (`inverse == false`) / inverse NTT (`inverse == true`)
/// computing stage roots directly from [`goldilocks_primitive_root`] (`0` heap allocations).
pub fn goldilocks_ntt_alloc_free(buf: &mut [u64], inverse: bool) -> Result<(), AccelError> {
    let n = buf.len();
    let log2_n = ntt_log2_len("NTT buffer", n)?;
    for slot in buf.iter_mut() {
        *slot = gl_reduce_u64(*slot);
    }
    if n == 1 {
        return Ok(());
    }
    bit_reverse_permute(buf);

    let mut stage_log2 = 1u32;
    while stage_log2 <= log2_n {
        let len = 1usize << stage_log2;
        let half = len / 2;
        let w_root = goldilocks_primitive_root(stage_log2)?;
        let w_step = if inverse {
            gl_inv_or_zero(w_root)
        } else {
            w_root
        };
        let mut start = 0usize;
        while start < n {
            let mut w = 1u64;
            for j in 0..half {
                let u = buf[start + j];
                let v = gl_mul(buf[start + j + half], w);
                buf[start + j] = gl_add(u, v);
                buf[start + j + half] = gl_sub(u, v);
                w = gl_mul(w, w_step);
            }
            start += len;
        }
        stage_log2 += 1;
    }

    if inverse {
        let inv_n = gl_inv_or_zero(n as u64);
        for slot in buf.iter_mut() {
            *slot = gl_mul(*slot, inv_n);
        }
    }
    Ok(())
}

#[inline]
fn bit_reverse_permute_ext2_coord(out: &mut [[u64; 2]], len: usize, coord: usize) {
    if len <= 1 {
        return;
    }
    let shift = usize::BITS - len.trailing_zeros();
    for i in 0..len {
        let rev = i.reverse_bits() >> shift;
        if i < rev {
            let tmp = out[i][coord];
            out[i][coord] = out[rev][coord];
            out[rev][coord] = tmp;
        }
    }
}

fn ntt_ext2_coord_in_slice(
    out: &mut [[u64; 2]],
    len: usize,
    coord: usize,
    inverse: bool,
) -> Result<(), AccelError> {
    let log2_n = ntt_log2_len("ext2 NTT length", len)?;
    if out.len() < len {
        return Err(AccelError::LengthMismatch {
            what: "ext2 NTT buffer",
            expected: len,
            actual: out.len(),
        });
    }
    for item in out.iter_mut().take(len) {
        item[coord] = gl_reduce_u64(item[coord]);
    }
    if len == 1 {
        return Ok(());
    }
    bit_reverse_permute_ext2_coord(out, len, coord);
    let mut stage_log2 = 1u32;
    while stage_log2 <= log2_n {
        let slen = 1usize << stage_log2;
        let half = slen / 2;
        let w_root = goldilocks_primitive_root(stage_log2)?;
        let w_step = if inverse {
            gl_inv_or_zero(w_root)
        } else {
            w_root
        };
        let mut start = 0usize;
        while start < len {
            let mut w = 1u64;
            for j in 0..half {
                let u = out[start + j][coord];
                let v = gl_mul(out[start + j + half][coord], w);
                out[start + j][coord] = gl_add(u, v);
                out[start + j + half][coord] = gl_sub(u, v);
                w = gl_mul(w, w_step);
            }
            start += slen;
        }
        stage_log2 += 1;
    }
    if inverse {
        let inv_n = gl_inv_or_zero(len as u64);
        for item in out.iter_mut().take(len) {
            item[coord] = gl_mul(item[coord], inv_n);
        }
    }
    Ok(())
}

/// Zero-allocation `#![no_std]` shifted-coset Reed-Solomon Low-Degree Extension (LDE) over $\mathbb{F}_{p^2}$:
/// Given `evals` of length $N = 2^k$ representing polynomial $P(X) \in \mathbb{F}_{p^2}[X]_{< N}$
/// evaluated on $\{1, \omega_N, \dots, \omega_N^{N-1}\}$, computes `out` of length $M = N \cdot \text{blowup}$
/// containing $P(\text{shift} \cdot \omega_M^i)$ for $i \in [0, M)$ directly inside `out`!
pub fn coset_lde_ext2_cpu(
    evals: &[[u64; 2]],
    blowup: usize,
    shift: u64,
    out: &mut [[u64; 2]],
) -> Result<(), AccelError> {
    let n = evals.len();
    ntt_log2_len("LDE evaluation domain", n)?;
    if !blowup.is_power_of_two() {
        return Err(AccelError::NotPowerOfTwo {
            what: "LDE blowup",
            len: blowup,
        });
    }
    let m = n.checked_mul(blowup).ok_or(AccelError::LengthOverflow)?;
    ntt_log2_len("LDE codeword domain", m)?;
    if out.len() != m {
        return Err(AccelError::LengthMismatch {
            what: "LDE output",
            expected: m,
            actual: out.len(),
        });
    }

    for (i, ev) in evals.iter().enumerate() {
        out[i] = [gl_reduce_u64(ev[0]), gl_reduce_u64(ev[1])];
    }
    for slot in out.iter_mut().skip(n) {
        *slot = [0u64, 0u64];
    }

    // 1. Inverse NTT of length N in-place inside `out[0..n]`.
    ntt_ext2_coord_in_slice(out, n, 0, true)?;
    ntt_ext2_coord_in_slice(out, n, 1, true)?;

    // 2. Multiply monomial coefficients c_j by shift^j.
    let shift_c = gl_reduce_u64(shift);
    let mut shift_pow = 1u64;
    for item in out.iter_mut().take(n) {
        item[0] = gl_mul(item[0], shift_pow);
        item[1] = gl_mul(item[1], shift_pow);
        shift_pow = gl_mul(shift_pow, shift_c);
    }

    // 3. Forward NTT of length M = N * blowup across all of `out[0..m]`.
    ntt_ext2_coord_in_slice(out, m, 0, false)?;
    ntt_ext2_coord_in_slice(out, m, 1, false)
}
