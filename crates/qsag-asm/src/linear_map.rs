//! Tableless byte-block linear maps. Matrices are indexed only by public byte
//! positions; GFNI computes the eight parities without secret-indexed tables.
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
use crate::portable::{POLY_TO_T7_BASIS, T7_TO_POLY_BASIS};

#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
const fn matrices(basis: &[u128; 128]) -> [[u64; 16]; 16] {
    let mut out = [[0; 16]; 16];
    let mut input = 0;
    while input < 16 {
        let mut output = 0;
        while output < 16 {
            let mut bit = 0;
            while bit < 8 {
                let mut row = 0;
                let mut column = 0;
                while column < 8 {
                    row |=
                        (((basis[input * 8 + column] >> (output * 8 + bit)) & 1) as u64) << column;
                    column += 1;
                }
                // GFNI numbers matrix rows in reverse byte order.
                out[input][output] |= row << ((7 - bit) * 8);
                bit += 1;
            }
            output += 1;
        }
        input += 1;
    }
    out
}
#[cfg(target_arch = "x86_64")]
static FORWARD: [[u64; 16]; 16] = matrices(&T7_TO_POLY_BASIS);
#[cfg(target_arch = "x86_64")]
static INVERSE: [[u64; 16]; 16] = matrices(&POLY_TO_T7_BASIS);

#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
const fn convolution_matrices(basis: &[u128; 128]) -> [[u64; 16]; 16] {
    let mut out = matrices(basis);
    let mut i = 0;
    while i < 16 {
        let mut j = 0;
        while j < 16 {
            out[i][j] = out[i][j].reverse_bits();
            j += 1;
        }
        i += 1;
    }
    out
}
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
static CONV_FORWARD: [[u64; 16]; 16] = convolution_matrices(&T7_TO_POLY_BASIS);
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
static CONV_INVERSE: [[u64; 16]; 16] = convolution_matrices(&POLY_TO_T7_BASIS);

pub(crate) fn map(x: u128, inverse: bool) -> u128 {
    #[cfg(target_arch = "x86_64")]
    {
        let caps = crate::probe_capabilities();
        if caps.gfni {
            let matrices = if inverse { &INVERSE } else { &FORWARD };
            if caps.avx512 {
                // SAFETY: GFNI and AVX-512 including OS ZMM state were probed.
                return unsafe { gfni512(x, matrices) };
            }
            // SAFETY: GFNI was probed; SSE2 is baseline x86-64.
            return unsafe { gfni128(x, matrices) };
        }
    }
    #[cfg(target_arch = "x86_64")]
    {
        let caps = crate::probe_capabilities();
        if caps.pclmulqdq && caps.bmi2 {
            // SAFETY: checked carryless multiplication and PEXT support.
            return unsafe {
                if inverse {
                    pclmul_map::<true>(x)
                } else {
                    pclmul_map::<false>(x)
                }
            };
        }
    }
    #[cfg(target_arch = "aarch64")]
    {
        let caps = crate::probe_capabilities();
        if caps.aarch64_neon && caps.aarch64_pmull {
            let _dit = crate::cpuid::ensure_aarch64_dit_enabled();
            // SAFETY: checked NEON and PMULL support.
            return unsafe {
                pmull_map(
                    x,
                    if inverse {
                        &CONV_INVERSE
                    } else {
                        &CONV_FORWARD
                    },
                )
            };
        }
    }
    if inverse {
        crate::portable::poly128_to_tower128_portable(x)
    } else {
        crate::portable::tower128_to_poly128_portable(x)
    }
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "gfni,avx512f,avx512bw")]
unsafe fn gfni512(x: u128, matrices: &[[u64; 16]; 16]) -> u128 {
    use core::arch::x86_64::*;
    let mut lo = _mm512_setzero_si512();
    let mut hi = _mm512_setzero_si512();
    for (byte, matrix) in x.to_le_bytes().iter().zip(matrices) {
        let input = _mm512_set1_epi64(i64::from(*byte));
        // SAFETY: each matrix contains sixteen u64s; loads are unaligned.
        unsafe {
            lo = _mm512_xor_si512(
                lo,
                _mm512_gf2p8affine_epi64_epi8::<0>(
                    input,
                    _mm512_loadu_si512(matrix.as_ptr().cast()),
                ),
            );
            hi = _mm512_xor_si512(
                hi,
                _mm512_gf2p8affine_epi64_epi8::<0>(
                    input,
                    _mm512_loadu_si512(matrix.as_ptr().add(8).cast()),
                ),
            );
        }
    }
    let low = _mm_cvtsi128_si64(_mm512_cvtepi64_epi8(lo)) as u64;
    let high = _mm_cvtsi128_si64(_mm512_cvtepi64_epi8(hi)) as u64;
    u128::from(low) | (u128::from(high) << 64)
}

/// Eight inputs share each GFNI matrix load: every byte in a qword belongs to a
/// different input. The public byte transpose makes all 64 SIMD bytes useful.
#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "gfni,avx512f,avx512bw")]
unsafe fn gfni512x8(values: &mut [u128], matrices: &[[u64; 16]; 16]) {
    use core::arch::x86_64::*;
    let mut columns = [0u64; 16];
    for (i, value) in values.iter().enumerate() {
        for (column, byte) in columns.iter_mut().zip(value.to_le_bytes()) {
            *column |= u64::from(byte) << (8 * i);
        }
    }
    let mut lo = _mm512_setzero_si512();
    let mut hi = _mm512_setzero_si512();
    for (&column, matrix) in columns.iter().zip(matrices) {
        let input = _mm512_set1_epi64(column as i64);
        // SAFETY: each matrix contains sixteen u64s.
        unsafe {
            lo = _mm512_xor_si512(
                lo,
                _mm512_gf2p8affine_epi64_epi8::<0>(
                    input,
                    _mm512_loadu_si512(matrix.as_ptr().cast()),
                ),
            );
            hi = _mm512_xor_si512(
                hi,
                _mm512_gf2p8affine_epi64_epi8::<0>(
                    input,
                    _mm512_loadu_si512(matrix.as_ptr().add(8).cast()),
                ),
            );
        }
    }
    // SAFETY: the sixteen columns hold two full ZMM stores.
    unsafe {
        _mm512_storeu_si512(columns.as_mut_ptr().cast(), lo);
        _mm512_storeu_si512(columns.as_mut_ptr().add(8).cast(), hi);
    }
    for (i, value) in values.iter_mut().enumerate() {
        let bytes: [u8; 16] = core::array::from_fn(|j| (columns[j] >> (8 * i)) as u8);
        *value = u128::from_le_bytes(bytes);
    }
    crate::volatile_fill(&mut columns, 0);
}

pub(crate) fn map_batch(values: &mut [u128], inverse: bool) {
    #[cfg(target_arch = "x86_64")]
    {
        let caps = crate::probe_capabilities();
        if caps.gfni && caps.avx512 {
            for chunk in values.chunks_mut(8) {
                // SAFETY: checked features; the batch accepts one through eight inputs.
                unsafe {
                    gfni512x8(chunk, if inverse { &INVERSE } else { &FORWARD });
                }
            }
            return;
        }
    }
    for value in values {
        *value = map(*value, inverse);
    }
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "gfni")]
unsafe fn gfni128(x: u128, matrices: &[[u64; 16]; 16]) -> u128 {
    use core::arch::x86_64::*;
    let mut out = [0u8; 16];
    for (pair, dst) in out.as_chunks_mut::<2>().0.iter_mut().enumerate() {
        let mut sum = _mm_setzero_si128();
        for (byte, matrix) in x.to_le_bytes().iter().zip(matrices) {
            // SAFETY: each public pair indexes two elements of the matrix.
            let m = unsafe { _mm_loadu_si128(matrix.as_ptr().add(pair * 2).cast()) };
            sum = _mm_xor_si128(
                sum,
                _mm_gf2p8affine_epi64_epi8::<0>(_mm_set1_epi64x(i64::from(*byte)), m),
            );
        }
        dst[0] = _mm_cvtsi128_si64(sum) as u8;
        dst[1] = _mm_cvtsi128_si64(_mm_srli_si128::<8>(sum)) as u8;
    }
    u128::from_le_bytes(out)
}

// For each eight-bit row r, the coefficient of x^7 in x * reverse(r)
// is its parity dot product. Rows spaced eight bits apart do not overlap at
// these coefficient positions, so a single CLMUL computes eight parities.
#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "pclmulqdq,bmi2")]
unsafe fn pclmul_map<const INVERSE: bool>(x: u128) -> u128 {
    let matrices = if INVERSE {
        &CONV_INVERSE
    } else {
        &CONV_FORWARD
    };
    use core::arch::x86_64::*;
    let mut output = [0u8; 16];
    for (byte, matrix) in x.to_le_bytes().iter().zip(matrices) {
        let input = _mm_cvtsi64_si128(i64::from(*byte));
        for (pair, dst) in output.as_chunks_mut::<2>().0.iter_mut().enumerate() {
            // SAFETY: public pair index selects two in-bounds matrix words.
            let rows = unsafe { _mm_loadu_si128(matrix.as_ptr().add(pair * 2).cast()) };
            let low = _mm_cvtsi128_si64(_mm_clmulepi64_si128::<0x00>(input, rows)) as u64;
            let high = _mm_cvtsi128_si64(_mm_clmulepi64_si128::<0x10>(input, rows)) as u64;
            dst[0] ^= _pext_u64(low, 0x8080808080808080) as u8;
            dst[1] ^= _pext_u64(high, 0x8080808080808080) as u8;
        }
    }
    u128::from_le_bytes(output)
}

#[cfg(target_arch = "aarch64")]
#[target_feature(enable = "neon,aes")]
unsafe fn pmull_map(x: u128, matrices: &[[u64; 16]; 16]) -> u128 {
    use core::arch::aarch64::*;
    let mut output = [0u8; 16];
    for (byte, matrix) in x.to_le_bytes().iter().zip(matrices) {
        for (dst, &rows) in output.iter_mut().zip(matrix) {
            let product = vmull_p64(u64::from(*byte), rows) as u64;
            let parities = (product >> 7) & 0x0101010101010101;
            *dst ^= (parities.wrapping_mul(0x0102040810204080) >> 56) as u8;
        }
    }
    u128::from_le_bytes(output)
}

#[cfg(test)]
mod tests {
    #[test]
    fn batches_match_reference_at_every_tail_and_direction() {
        let initial: [u128; 137] = core::array::from_fn(|i| {
            (i as u128 + 1).wrapping_mul(0xfedcba98765432100123456789abcdef)
        });
        for len in 0..=initial.len() {
            let mut actual = initial;
            super::map_batch(&mut actual[..len], false);
            for (&x, &y) in initial[..len].iter().zip(&actual[..len]) {
                assert_eq!(y, crate::portable::tower128_to_poly128_portable(x));
            }
            assert_eq!(actual[len..], initial[len..]);
            super::map_batch(&mut actual[..len], true);
            assert_eq!(actual, initial);
        }
    }
    #[test]
    fn all_basis_vectors_and_dense_inputs_match_reference() {
        for x in (0..128).map(|bit| 1u128 << bit).chain([
            0,
            u128::MAX,
            0x0123456789abcdef_fedcba9876543210,
        ]) {
            let y = super::map(x, false);
            assert_eq!(y, crate::portable::tower128_to_poly128_portable(x));
            assert_eq!(super::map(y, true), x);
            assert_eq!(
                super::map(x, true),
                crate::portable::poly128_to_tower128_portable(x)
            );
            #[cfg(target_arch = "x86_64")]
            if crate::probe_capabilities().pclmulqdq && crate::probe_capabilities().bmi2 {
                // SAFETY: checked features.
                unsafe {
                    assert_eq!(super::pclmul_map::<false>(x), y);
                    assert_eq!(super::pclmul_map::<true>(y), x);
                }
            }
            #[cfg(target_arch = "x86_64")]
            if crate::probe_capabilities().gfni {
                // SAFETY: checked feature support.
                unsafe {
                    assert_eq!(super::gfni128(x, &super::FORWARD), y);
                    assert_eq!(super::gfni128(y, &super::INVERSE), x);
                }
            }
        }
    }
}
