//! Canonical constant-time Goldilocks field ($p = 2^{64} - 2^{32} + 1$), quadratic extension
//! $\mathbb{F}_{p^2} = \mathbb{F}_p[u]/(u^2 - 7)$, injective 5-limb 56-bit digest framing,
//! radix-2 NTT, and shifted-coset Reed-Solomon LDE over $\mathbb{F}_{p^2}$.

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

use qsag_asm::portable::{
    goldilocks_add_ct_portable, goldilocks_canonicalize_ct, goldilocks_mul_ct_portable,
    goldilocks_reduce128_ct_portable, goldilocks_sub_ct_portable,
};

use crate::AccelError;
use crate::ct::{ct_eq_u64, ct_select_u64};

// The scalar field lives in `qsag_asm::portable`; this module names it for the kernels here
// and adds inversion, exponentiation, the quadratic extension, and the transforms.

/// Canonical Goldilocks prime $p = 2^{64} - 2^{32} + 1$.
pub const GOLDILOCKS_PRIME: u64 = qsag_asm::GOLDILOCKS_PRIME;
/// Reduction constant $\epsilon = 2^{32} - 1 = 2^{64} - p$.
pub const GOLDILOCKS_EPSILON: u64 = qsag_asm::GOLDILOCKS_EPSILON;
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
    goldilocks_canonicalize_ct(x)
}

/// Branchless modular addition, canonical for every `u64` input pair.
#[inline]
pub const fn gl_add(a: u64, b: u64) -> u64 {
    goldilocks_add_ct_portable(a, b)
}

/// Branchless modular subtraction, canonical for every `u64` input pair.
#[inline]
pub const fn gl_sub(a: u64, b: u64) -> u64 {
    goldilocks_sub_ct_portable(a, b)
}

/// Branchless negation `0 - a mod p`.
#[inline]
pub const fn gl_neg(a: u64) -> u64 {
    gl_sub(0, a)
}

/// Branchless 128-to-64 Goldilocks reduction for arbitrary `u128`.
#[inline]
pub const fn gl_reduce128(x: u128) -> u64 {
    goldilocks_reduce128_ct_portable(x)
}

/// Branchless modular multiplication `a * b mod p`, canonical for every `u64` input pair.
#[inline]
pub const fn gl_mul(a: u64, b: u64) -> u64 {
    goldilocks_mul_ct_portable(a, b)
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
pub(crate) const fn ntt_log2_len(what: &'static str, len: usize) -> Result<u32, AccelError> {
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
fn bit_reverse_permute<T>(buf: &mut [T]) {
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

// Fuse extension coordinates so both share twiddles, bit reversal and thread scheduling.
// No transpose or coefficient-sized scratch allocation is needed.
trait NttValue: Copy + Send {
    fn reduce(&mut self);
    fn scale(&mut self, w: u64);
    fn butterfly(lo: &mut Self, hi: &mut Self, w: u64);
}

impl NttValue for u64 {
    #[inline]
    fn reduce(&mut self) {
        *self = gl_reduce_u64(*self);
    }
    #[inline]
    fn scale(&mut self, w: u64) {
        *self = gl_mul(*self, w);
    }
    #[inline]
    fn butterfly(lo: &mut Self, hi: &mut Self, w: u64) {
        let u = *lo;
        let v = gl_mul(*hi, w);
        *lo = gl_add(u, v);
        *hi = gl_sub(u, v);
    }
}

impl NttValue for [u64; 2] {
    #[inline]
    fn reduce(&mut self) {
        self.iter_mut().for_each(NttValue::reduce);
    }
    #[inline]
    fn scale(&mut self, w: u64) {
        self.iter_mut().for_each(|x| x.scale(w));
    }
    #[inline]
    fn butterfly(lo: &mut Self, hi: &mut Self, w: u64) {
        u64::butterfly(&mut lo[0], &mut hi[0], w);
        u64::butterfly(&mut lo[1], &mut hi[1], w);
    }
}

// Four independent products expose instruction-level/vector parallelism. Powers advance by
// w^4, removing the scalar w *= root dependency between adjacent butterflies.
#[inline]
fn butterflies<T: NttValue>(
    lo: &mut [T],
    hi: &mut [T],
    mut weights: impl FnMut(usize, usize) -> [u64; 4],
) {
    let (lo_blocks, lo_tail) = lo.as_chunks_mut::<4>();
    let (hi_blocks, hi_tail) = hi.as_chunks_mut::<4>();
    for (i, (lo, hi)) in lo_blocks.iter_mut().zip(hi_blocks).enumerate() {
        let w = weights(i * 4, 4);
        for lane in 0..4 {
            T::butterfly(&mut lo[lane], &mut hi[lane], w[lane]);
        }
    }
    if !lo_tail.is_empty() {
        let w = weights(lo_blocks.len() * 4, lo_tail.len());
        for lane in 0..lo_tail.len() {
            T::butterfly(&mut lo_tail[lane], &mut hi_tail[lane], w[lane]);
        }
    }
}

fn ntt_stage<T: NttValue>(
    buf: &mut [T],
    len: usize,
    run: impl Fn(&mut [T], &mut [T], usize) + Sync,
) {
    let half = len / 2;
    #[cfg(feature = "std")]
    {
        let workers = crate::cpu_workers(buf.len(), 32_768);
        if workers > 1 {
            let blocks = buf.len() / len;
            if blocks >= workers {
                // Group early-stage blocks to amortize thread startup.
                let groups = buf.chunks_mut(blocks.div_ceil(workers) * len);
                crate::cpu_drain(workers, groups, |group| {
                    for block in group.chunks_mut(len) {
                        let (lo, hi) = block.split_at_mut(half);
                        run(lo, hi, 0);
                    }
                });
            } else {
                // Split within butterflies too: the final stage has only one block.
                let chunk_len = half.div_ceil(workers / blocks);
                let pieces = buf.chunks_mut(len).flat_map(|block| {
                    let (lo, hi) = block.split_at_mut(half);
                    lo.chunks_mut(chunk_len)
                        .zip(hi.chunks_mut(chunk_len))
                        .enumerate()
                });
                crate::cpu_drain(workers, pieces, |(i, (lo, hi))| run(lo, hi, i * chunk_len));
            }
            return;
        }
    }
    for block in buf.chunks_mut(len) {
        let (lo, hi) = block.split_at_mut(half);
        run(lo, hi, 0);
    }
}

fn normalize_ntt<T: NttValue>(buf: &mut [T], inverse: bool) {
    if inverse {
        let inv_n = gl_inv_or_zero(buf.len() as u64);
        crate::cpu_chunks_mut(buf, 32_768, |_, chunk| {
            chunk.iter_mut().for_each(|x| x.scale(inv_n));
        });
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
    crate::cpu_chunks_mut(buf, 32_768, |_, chunk| {
        chunk.iter_mut().for_each(NttValue::reduce);
    });
    if n == 1 {
        return Ok(());
    }
    bit_reverse_permute(buf);
    for stage in 1..=n.trailing_zeros() {
        let len = 1usize << stage;
        let step = n / len;
        ntt_stage(buf, len, |lo, hi, offset| {
            butterflies(lo, hi, |j, lanes| {
                let mut w = [1; 4];
                for (lane, w) in w.iter_mut().enumerate().take(lanes) {
                    let idx = (offset + j + lane) * step;
                    *w = if inverse && idx != 0 {
                        gl_neg(twiddles[n / 2 - idx])
                    } else {
                        gl_reduce_u64(twiddles[idx])
                    };
                }
                w
            });
        });
    }
    normalize_ntt(buf, inverse);
    Ok(())
}

/// Allocation-free in-place radix-2 NTT (`inverse == false`) / inverse NTT (`inverse == true`)
/// computing stage roots directly from [`goldilocks_primitive_root`]. No transform scratch
/// allocation; large `std` jobs use scoped workers, while `no_std` stays allocation-free.
pub fn goldilocks_ntt_alloc_free(buf: &mut [u64], inverse: bool) -> Result<(), AccelError> {
    ntt_alloc_free(buf, inverse)
}

fn ntt_alloc_free<T: NttValue>(buf: &mut [T], inverse: bool) -> Result<(), AccelError> {
    let log2_n = ntt_log2_len("NTT buffer", buf.len())?;
    crate::cpu_chunks_mut(buf, 32_768, |_, chunk| {
        chunk.iter_mut().for_each(NttValue::reduce);
    });
    bit_reverse_permute(buf);
    for stage in 1..=log2_n {
        let root = goldilocks_primitive_root(stage)?;
        let root = if inverse { gl_inv_or_zero(root) } else { root };
        let root2 = gl_sq(root);
        let initial = [1, root, root2, gl_mul(root2, root)];
        let stride = gl_sq(root2);
        ntt_stage(buf, 1usize << stage, |lo, hi, offset| {
            let mut w = initial;
            if offset != 0 {
                let first = gl_pow_pub(root, offset as u64);
                for x in &mut w {
                    *x = gl_mul(*x, first);
                }
            }
            butterflies(lo, hi, |j, _| {
                if j != 0 {
                    for x in &mut w {
                        *x = gl_mul(*x, stride);
                    }
                }
                w
            });
        });
    }
    normalize_ntt(buf, inverse);
    Ok(())
}

/// Shape contract of a coset LDE job, shared by every backend: power-of-two domain and blowup,
/// a codeword domain inside the two-adic subgroup, and `out_len == domain_len * blowup`.
pub(crate) fn coset_lde_shape(
    domain_len: usize,
    blowup: usize,
    out_len: usize,
) -> Result<(), AccelError> {
    ntt_log2_len("LDE evaluation domain", domain_len)?;
    if !blowup.is_power_of_two() {
        return Err(AccelError::NotPowerOfTwo {
            what: "LDE blowup",
            len: blowup,
        });
    }
    let codeword_len = domain_len
        .checked_mul(blowup)
        .ok_or(AccelError::LengthOverflow)?;
    ntt_log2_len("LDE codeword domain", codeword_len)?;
    if out_len != codeword_len {
        return Err(AccelError::LengthMismatch {
            what: "LDE output",
            expected: codeword_len,
            actual: out_len,
        });
    }
    Ok(())
}

/// Scratch-free (zero-allocation without `std`) shifted-coset Reed-Solomon Low-Degree Extension (LDE) over $\mathbb{F}_{p^2}$:
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
    coset_lde_shape(n, blowup, out.len())?;

    for (i, ev) in evals.iter().enumerate() {
        out[i] = [gl_reduce_u64(ev[0]), gl_reduce_u64(ev[1])];
    }
    for slot in out.iter_mut().skip(n) {
        *slot = [0u64, 0u64];
    }

    // 1. Inverse NTT of length N in-place inside `out[0..n]`.
    ntt_alloc_free(&mut out[..n], true)?;

    // 2. Multiply monomial coefficients c_j by shift^j.
    let shift_c = gl_reduce_u64(shift);
    crate::cpu_chunks_mut(&mut out[..n], 32_768, |offset, chunk| {
        let mut shift_pow = gl_pow_pub(shift_c, offset as u64);
        for item in chunk {
            item.scale(shift_pow);
            shift_pow = gl_mul(shift_pow, shift_c);
        }
    });

    // 3. Forward NTT of length M = N * blowup across all of `out`.
    ntt_alloc_free(out, false)
}

// ============================================================================
// Quartic Extension Field F_{p^4} = F_{p^2}[w] / (w^2 - u) & 4-Byte Kronecker
// ============================================================================

/// Canonical `GoldilocksExt4` identity element `[1, 0, 0, 0]`.
pub const EXT4_ONE: [u64; 4] = [1, 0, 0, 0];
/// Canonical `GoldilocksExt4` zero element `[0, 0, 0, 0]`.
pub const EXT4_ZERO: [u64; 4] = [0, 0, 0, 0];

#[inline]
pub const fn ext4_add(a: [u64; 4], b: [u64; 4]) -> [u64; 4] {
    [
        gl_add(a[0], b[0]),
        gl_add(a[1], b[1]),
        gl_add(a[2], b[2]),
        gl_add(a[3], b[3]),
    ]
}

#[inline]
pub const fn ext4_sub(a: [u64; 4], b: [u64; 4]) -> [u64; 4] {
    [
        gl_sub(a[0], b[0]),
        gl_sub(a[1], b[1]),
        gl_sub(a[2], b[2]),
        gl_sub(a[3], b[3]),
    ]
}

#[inline]
pub const fn ext4_mul(a: [u64; 4], b: [u64; 4]) -> [u64; 4] {
    let v0 = ext2_mul([a[0], a[1]], [b[0], b[1]]);
    let v1 = ext2_mul([a[2], a[3]], [b[2], b[3]]);
    let mid_raw = ext2_mul(
        ext2_add([a[0], a[1]], [a[2], a[3]]),
        ext2_add([b[0], b[1]], [b[2], b[3]]),
    );
    let mid = ext2_sub(ext2_sub(mid_raw, v0), v1);
    [
        gl_add(v0[0], gl_mul(v1[1], GOLDILOCKS_GENERATOR)),
        gl_add(v0[1], v1[0]),
        mid[0],
        mid[1],
    ]
}

#[inline]
pub const fn ext4_pow_pub(mut base: [u64; 4], mut exp: u64) -> [u64; 4] {
    base = [
        gl_reduce_u64(base[0]),
        gl_reduce_u64(base[1]),
        gl_reduce_u64(base[2]),
        gl_reduce_u64(base[3]),
    ];
    let mut acc = EXT4_ONE;
    while exp > 0 {
        if (exp & 1) == 1 {
            acc = ext4_mul(acc, base);
        }
        base = ext4_mul(base, base);
        exp >>= 1;
    }
    acc
}

/// Build a 4-byte (`1,024`-entry = `32 KiB`) multilinear equality Kronecker table over
/// $\mathbb{F}_{p^4}$ supporting up to `32` variables (`num_vars <= 26` in VRAM WHIR).
pub fn eq_kronecker_1024(point: &[[u64; 4]]) -> [[u64; 4]; 1024] {
    let mut out = [EXT4_ZERO; 1024];
    for byte_idx in 0..4usize {
        for k in 0..256usize {
            let mut prod = EXT4_ONE;
            let mut zeroed = false;
            for j in 0..8usize {
                let b = 8 * byte_idx + j;
                let bit = (k >> j) & 1 == 1;
                if b < point.len() {
                    let p = point[b];
                    let term = if bit { p } else { ext4_sub(EXT4_ONE, p) };
                    prod = ext4_mul(prod, term);
                } else if bit {
                    zeroed = true;
                    break;
                }
            }
            out[256 * byte_idx + k] = if zeroed { EXT4_ZERO } else { prod };
        }
    }
    out
}

/// Build a 4-byte (`1,024`-entry = `32 KiB`) multilinear monomial Kronecker table over
/// $\mathbb{F}_{p^4}$ supporting up to `32` variables (`num_vars <= 26` in VRAM WHIR).
pub fn mono_kronecker_1024(point: &[[u64; 4]]) -> [[u64; 4]; 1024] {
    let mut out = [EXT4_ZERO; 1024];
    for byte_idx in 0..4usize {
        for k in 0..256usize {
            let mut prod = EXT4_ONE;
            let mut zeroed = false;
            for j in 0..8usize {
                let b = 8 * byte_idx + j;
                let bit = (k >> j) & 1 == 1;
                if b < point.len() {
                    if bit {
                        prod = ext4_mul(prod, point[b]);
                    }
                } else if bit {
                    zeroed = true;
                    break;
                }
            }
            out[256 * byte_idx + k] = if zeroed { EXT4_ZERO } else { prod };
        }
    }
    out
}

/// Build a 4-byte (`1,024`-entry = `32 KiB`) geometric Kronecker table for `scale * z^i`
/// over $0 \le i < 2^{32}$.
pub fn geometric_kronecker_1024(scale: [u64; 4], z: [u64; 4]) -> [[u64; 4]; 1024] {
    let mut out = [EXT4_ZERO; 1024];
    let z_c = [
        gl_reduce_u64(z[0]),
        gl_reduce_u64(z[1]),
        gl_reduce_u64(z[2]),
        gl_reduce_u64(z[3]),
    ];
    let mut cur = [
        gl_reduce_u64(scale[0]),
        gl_reduce_u64(scale[1]),
        gl_reduce_u64(scale[2]),
        gl_reduce_u64(scale[3]),
    ];
    for slot in &mut out[0..256] {
        *slot = cur;
        cur = ext4_mul(cur, z_c);
    }
    let z_8 = ext4_pow_pub(z_c, 256);
    cur = EXT4_ONE;
    for slot in &mut out[256..512] {
        *slot = cur;
        cur = ext4_mul(cur, z_8);
    }
    let z_16 = ext4_pow_pub(z_8, 256);
    cur = EXT4_ONE;
    for slot in &mut out[512..768] {
        *slot = cur;
        cur = ext4_mul(cur, z_16);
    }
    let z_24 = ext4_pow_pub(z_16, 256);
    cur = EXT4_ONE;
    for slot in &mut out[768..1024] {
        *slot = cur;
        cur = ext4_mul(cur, z_24);
    }
    out
}

/// Build a paired `2 x 1,024` (`2,048`-entry = `64 KiB`) geometric Kronecker table for two OOD points.
pub fn pair_geometric_kronecker_2048(
    s0: [u64; 4],
    z0: [u64; 4],
    s1: [u64; 4],
    z1: [u64; 4],
) -> [[u64; 4]; 2048] {
    let mut out = [EXT4_ZERO; 2048];
    out[0..1024].copy_from_slice(&geometric_kronecker_1024(s0, z0));
    out[1024..2048].copy_from_slice(&geometric_kronecker_1024(s1, z1));
    out
}
