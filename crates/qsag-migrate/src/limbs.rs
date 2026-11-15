//! Constant-time fixed-width integer arithmetic over little-endian `[u64; N]` limbs.
//!
//! Every loop bound is the const limb count, so each instantiation is straight-line code.
//! Data-dependent choices are taken with the mask selectors of `qsag_accel::ct`; no function
//! here branches on or indexes by a limb value.

use qsag_accel::ct::{ct_eq_u64, ct_select_u64};

/// The integer `1`.
#[inline]
pub(crate) const fn one<const N: usize>() -> [u64; N] {
    let mut out = [0u64; N];
    out[0] = 1;
    out
}

/// `a + b mod 2^(64 N)` and the carry out.
#[inline]
pub(crate) fn adc<const N: usize>(a: [u64; N], b: [u64; N]) -> ([u64; N], bool) {
    let mut out = [0u64; N];
    let mut carry = 0u128;
    for i in 0..N {
        let cur = (a[i] as u128) + (b[i] as u128) + carry;
        out[i] = cur as u64;
        carry = cur >> 64;
    }
    (out, carry != 0)
}

/// `a - b mod 2^(64 N)` and the borrow out (`true` iff `a < b`).
#[inline]
pub(crate) fn sbb<const N: usize>(a: [u64; N], b: [u64; N]) -> ([u64; N], bool) {
    let mut out = [0u64; N];
    let mut borrow = 0u64;
    for i in 0..N {
        let (d1, b1) = a[i].overflowing_sub(b[i]);
        let (d2, b2) = d1.overflowing_sub(borrow);
        out[i] = d2;
        borrow = (b1 as u64) | (b2 as u64);
    }
    (out, borrow != 0)
}

/// `a < b` as unsigned integers.
#[inline]
pub(crate) fn lt<const N: usize>(a: [u64; N], b: [u64; N]) -> bool {
    sbb(a, b).1
}

/// `if_true` when `choice`, else `if_false`, selected limb by limb with a mask.
#[inline]
pub(crate) fn ct_select<const N: usize>(
    choice: bool,
    if_true: [u64; N],
    if_false: [u64; N],
) -> [u64; N] {
    let mut out = [0u64; N];
    for i in 0..N {
        out[i] = ct_select_u64(choice, if_true[i], if_false[i]);
    }
    out
}

/// `a == b`, from the OR of all limb differences.
#[inline]
pub(crate) fn ct_eq<const N: usize>(a: [u64; N], b: [u64; N]) -> bool {
    let mut acc = 0u64;
    for i in 0..N {
        acc |= a[i] ^ b[i];
    }
    ct_eq_u64(acc, 0)
}

/// `a == 0`, from the OR of all limbs.
#[inline]
pub(crate) fn is_zero<const N: usize>(a: [u64; N]) -> bool {
    let mut acc = 0u64;
    for &limb in &a {
        acc |= limb;
    }
    ct_eq_u64(acc, 0)
}

/// One conditional subtraction of `m` from `overflow * 2^(64 N) + value`.
///
/// The result is fully reduced whenever that integer is below `2 m`.
#[inline]
pub(crate) fn reduce_once<const N: usize>(
    value: [u64; N],
    overflow: bool,
    m: [u64; N],
) -> [u64; N] {
    let (diff, borrow) = sbb(value, m);
    ct_select(overflow | !borrow, diff, value)
}

/// `a + b mod m` for `a, b < m`.
#[inline]
pub(crate) fn add_mod<const N: usize>(a: [u64; N], b: [u64; N], m: [u64; N]) -> [u64; N] {
    let (sum, carry) = adc(a, b);
    reduce_once(sum, carry, m)
}

/// `a - b mod m` for `a, b < m`: the wrapped difference plus `m` when the subtraction borrowed.
#[inline]
pub(crate) fn sub_mod<const N: usize>(a: [u64; N], b: [u64; N], m: [u64; N]) -> [u64; N] {
    let (diff, borrow) = sbb(a, b);
    let mut out = [0u64; N];
    let mut carry = 0u128;
    for i in 0..N {
        let addend = ct_select_u64(borrow, m[i], 0);
        let cur = (diff[i] as u128) + (addend as u128) + carry;
        out[i] = cur as u64;
        carry = cur >> 64;
    }
    out
}

/// `-a mod m` for `a < m` (`0 -> 0`).
#[inline]
pub(crate) fn neg_mod<const N: usize>(a: [u64; N], m: [u64; N]) -> [u64; N] {
    sub_mod([0u64; N], a, m)
}

/// Decode `B = 8 N` little-endian bytes.
#[inline]
pub(crate) fn from_le_bytes<const N: usize, const B: usize>(bytes: &[u8; B]) -> [u64; N] {
    const { assert!(B == 8 * N) };
    let mut out = [0u64; N];
    for (limb, chunk) in out.iter_mut().zip(bytes.chunks_exact(8)) {
        *limb = u64::from_le_bytes(chunk.try_into().unwrap());
    }
    out
}

/// Encode as `B = 8 N` little-endian bytes.
#[inline]
pub(crate) fn to_le_bytes<const N: usize, const B: usize>(limbs: [u64; N]) -> [u8; B] {
    const { assert!(B == 8 * N) };
    let mut out = [0u8; B];
    for (chunk, limb) in out.chunks_exact_mut(8).zip(limbs) {
        chunk.copy_from_slice(&limb.to_le_bytes());
    }
    out
}

/// Decode `B = 8 N` big-endian bytes (most significant byte first).
#[inline]
pub(crate) fn from_be_bytes<const N: usize, const B: usize>(bytes: &[u8; B]) -> [u64; N] {
    const { assert!(B == 8 * N) };
    let mut out = [0u64; N];
    for (limb, chunk) in out.iter_mut().rev().zip(bytes.chunks_exact(8)) {
        *limb = u64::from_be_bytes(chunk.try_into().unwrap());
    }
    out
}

/// Encode as `B = 8 N` big-endian bytes (most significant byte first).
#[inline]
pub(crate) fn to_be_bytes<const N: usize, const B: usize>(limbs: [u64; N]) -> [u8; B] {
    const { assert!(B == 8 * N) };
    let mut out = [0u8; B];
    for (chunk, limb) in out.chunks_exact_mut(8).zip(limbs.into_iter().rev()) {
        chunk.copy_from_slice(&limb.to_be_bytes());
    }
    out
}

/// CIOS Montgomery product `a * b * 2^(-64 N) mod m`.
///
/// Requires `a, b < m`, `m` odd with its top bit clear, and `inv = -m^{-1} mod 2^64`.
#[inline]
pub(crate) fn mont_mul<const N: usize>(
    a: [u64; N],
    b: [u64; N],
    m: [u64; N],
    inv: u64,
) -> [u64; N] {
    let mut t = [0u64; N];
    // Limb `N` of the running sum, which stays below `2 m` after every outer round.
    let mut t_top = 0u64;
    for &ai in &a {
        let mut carry = 0u128;
        for j in 0..N {
            let cur = (t[j] as u128) + (ai as u128) * (b[j] as u128) + carry;
            t[j] = cur as u64;
            carry = cur >> 64;
        }
        let cur = (t_top as u128) + carry;
        let hi = cur as u64;
        let hi_carry = (cur >> 64) as u64;

        // Add `u * m` so limb 0 cancels, then shift the sum down one limb.
        let u = t[0].wrapping_mul(inv);
        let cur0 = (t[0] as u128) + (u as u128) * (m[0] as u128);
        let mut carry2 = cur0 >> 64;
        for j in 1..N {
            let cur = (t[j] as u128) + (u as u128) * (m[j] as u128) + carry2;
            t[j - 1] = cur as u64;
            carry2 = cur >> 64;
        }
        let cur = (hi as u128) + carry2;
        t[N - 1] = cur as u64;
        t_top = hi_carry.wrapping_add((cur >> 64) as u64);
    }
    reduce_once(t, t_top != 0, m)
}

/// `base^exp mod m` with a fixed square-and-multiply schedule of `64 N` rounds.
///
/// `base < m` is in plain (non-Montgomery) form, as is the result; `r2 = 2^(128 N) mod m`.
/// The schedule reads every bit of `exp` but the round count does not depend on its value.
#[inline]
pub(crate) fn mont_pow<const N: usize>(
    base: [u64; N],
    exp: [u64; N],
    m: [u64; N],
    inv: u64,
    r2: [u64; N],
) -> [u64; N] {
    let mut b_m = mont_mul(base, r2, m, inv);
    let mut acc_m = mont_mul(one(), r2, m, inv);
    for limb in exp {
        for bit in 0..64 {
            let take = ((limb >> bit) & 1) == 1;
            let prod = mont_mul(acc_m, b_m, m, inv);
            acc_m = ct_select(take, prod, acc_m);
            b_m = mont_mul(b_m, b_m, m, inv);
        }
    }
    mont_mul(acc_m, one(), m, inv)
}

#[cfg(test)]
mod tests {
    use alloc::vec::Vec;

    use super::*;
    use crate::{
        bls12_381::{BLS_P, BLS_R},
        pallas::{PALLAS_P, PALLAS_Q},
        scalar::ED_PRIME,
        secp256k1_ct::{SECP_N, SECP_P},
    };

    struct Rng(u64);

    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            z ^ (z >> 31)
        }

        /// Uniform-ish limbs with all-zero and all-one limbs over-represented.
        fn limbs<const N: usize>(&mut self) -> [u64; N] {
            core::array::from_fn(|_| match self.next() % 8 {
                0 => 0,
                1 => u64::MAX,
                _ => self.next(),
            })
        }

        fn below<const N: usize>(&mut self, m: [u64; N]) -> [u64; N] {
            match self.next() % 16 {
                0 => [0; N],
                1 => ref_trim(&ref_sub(&m, &[1])),
                _ => ref_trim(&ref_rem(&self.limbs::<N>(), &m)),
            }
        }
    }

    // Variable-time schoolbook reference on little-endian limb vectors of any length.

    fn ref_cmp(a: &[u64], b: &[u64]) -> core::cmp::Ordering {
        let n = a.len().max(b.len());
        for i in (0..n).rev() {
            let (x, y) = (
                a.get(i).copied().unwrap_or(0),
                b.get(i).copied().unwrap_or(0),
            );
            if x != y {
                return x.cmp(&y);
            }
        }
        core::cmp::Ordering::Equal
    }

    fn ref_add(a: &[u64], b: &[u64]) -> Vec<u64> {
        let n = a.len().max(b.len());
        let mut out = Vec::with_capacity(n + 1);
        let mut carry = 0u128;
        for i in 0..n {
            let cur = a.get(i).copied().unwrap_or(0) as u128
                + b.get(i).copied().unwrap_or(0) as u128
                + carry;
            out.push(cur as u64);
            carry = cur >> 64;
        }
        out.push(carry as u64);
        out
    }

    /// `a - b`, requiring `a >= b`.
    fn ref_sub(a: &[u64], b: &[u64]) -> Vec<u64> {
        assert!(ref_cmp(a, b).is_ge());
        let mut out = Vec::with_capacity(a.len());
        let mut borrow = 0i128;
        for (i, &x) in a.iter().enumerate() {
            let cur = x as i128 - b.get(i).copied().unwrap_or(0) as i128 - borrow;
            out.push(cur as u64);
            borrow = i128::from(cur < 0);
        }
        assert_eq!(borrow, 0);
        out
    }

    fn ref_mul(a: &[u64], b: &[u64]) -> Vec<u64> {
        let mut out = alloc::vec![0u64; a.len() + b.len()];
        for (i, &x) in a.iter().enumerate() {
            let mut carry = 0u128;
            for (j, &y) in b.iter().enumerate() {
                let cur = out[i + j] as u128 + (x as u128) * (y as u128) + carry;
                out[i + j] = cur as u64;
                carry = cur >> 64;
            }
            out[i + b.len()] = carry as u64;
        }
        out
    }

    /// Bitwise long division remainder `a mod m`.
    fn ref_rem(a: &[u64], m: &[u64]) -> Vec<u64> {
        let mut rem = alloc::vec![0u64; m.len()];
        for i in (0..a.len() * 64).rev() {
            let bit = (a[i / 64] >> (i % 64)) & 1;
            rem = ref_add(&rem, &rem);
            rem[0] |= bit;
            if ref_cmp(&rem, m).is_ge() {
                rem = ref_sub(&rem, m);
            }
            rem.truncate(m.len() + 1);
        }
        rem
    }

    fn ref_trim<const N: usize>(a: &[u64]) -> [u64; N] {
        assert!(a.iter().skip(N).all(|&x| x == 0));
        core::array::from_fn(|i| a.get(i).copied().unwrap_or(0))
    }

    fn ref_mul_mod<const N: usize>(a: [u64; N], b: [u64; N], m: [u64; N]) -> [u64; N] {
        ref_trim(&ref_rem(&ref_mul(&a, &b), &m))
    }

    fn wide(x: [u64; 2]) -> u128 {
        (x[0] as u128) | ((x[1] as u128) << 64)
    }

    fn narrow(x: u128) -> [u64; 2] {
        [x as u64, (x >> 64) as u64]
    }

    #[test]
    fn two_limb_ops_match_u128() {
        let mut rng = Rng(1);
        for _ in 0..4000 {
            let (a, b) = (rng.limbs::<2>(), rng.limbs::<2>());
            let (x, y) = (wide(a), wide(b));
            let (sum, carry) = x.overflowing_add(y);
            assert_eq!(adc(a, b), (narrow(sum), carry));
            let (diff, borrow) = x.overflowing_sub(y);
            assert_eq!(sbb(a, b), (narrow(diff), borrow));
            assert_eq!(lt(a, b), x < y);
            assert_eq!(ct_eq(a, b), x == y);
            assert!(ct_eq(a, a));
            assert_eq!(is_zero(a), x == 0);
            assert_eq!(ct_select(true, a, b), a);
            assert_eq!(ct_select(false, a, b), b);

            let m = wide(rng.limbs::<2>()) | 1;
            let (xr, yr) = (x % m, y % m);
            let (ar, br, ml) = (narrow(xr), narrow(yr), narrow(m));
            let sum_mod = if m - xr > yr { xr + yr } else { xr - (m - yr) };
            assert_eq!(add_mod(ar, br, ml), narrow(sum_mod));
            let diff_mod = if xr >= yr { xr - yr } else { xr + (m - yr) };
            assert_eq!(sub_mod(ar, br, ml), narrow(diff_mod));
            assert_eq!(neg_mod(ar, ml), narrow((m - xr) % m));
            assert_eq!(reduce_once(ar, false, ml), ar);
            assert_eq!(reduce_once(ml, false, ml), [0; 2]);
        }
        assert!(is_zero([0u64; 2]));
        assert_eq!(one::<2>(), narrow(1));
    }

    fn check_wide_ops<const N: usize>(seed: u64, moduli: &[[u64; N]]) {
        let mut rng = Rng(seed);
        for _ in 0..300 {
            let (a, b) = (rng.limbs::<N>(), rng.limbs::<N>());
            let (sum, carry) = adc(a, b);
            let expected = ref_add(&a, &b);
            assert_eq!(&sum[..], &expected[..N]);
            assert_eq!(carry, expected[N] == 1);
            let (diff, borrow) = sbb(a, b);
            assert_eq!(borrow, ref_cmp(&a, &b).is_lt());
            assert_eq!(lt(a, b), borrow);
            if borrow {
                assert_eq!(sbb(b, a).0, ref_trim(&ref_sub(&b, &a)));
                assert_eq!(adc(diff, b), (a, true));
            } else {
                assert_eq!(diff, ref_trim(&ref_sub(&a, &b)));
            }
            assert_eq!(ct_eq(a, b), a == b);
            assert_eq!(is_zero(a), a == [0; N]);
            assert_eq!(ct_select(true, a, b), a);
            assert_eq!(ct_select(false, a, b), b);
        }
        for &m in moduli {
            let last = ref_trim(&ref_sub(&m, &[1]));
            assert_eq!(add_mod(last, one(), m), [0; N]);
            assert_eq!(sub_mod([0; N], one(), m), last);
            assert_eq!(neg_mod([0; N], m), [0; N]);
            assert_eq!(neg_mod(one(), m), last);
            assert_eq!(reduce_once(m, false, m), [0; N]);
            assert_eq!(reduce_once(last, false, m), last);
            assert!(lt(last, m) && !lt(m, m));
            for _ in 0..200 {
                let (a, b) = (rng.below(m), rng.below(m));
                assert_eq!(add_mod(a, b, m), ref_trim(&ref_rem(&ref_add(&a, &b), &m)));
                let lifted = ref_sub(&ref_add(&a, &m), &b);
                assert_eq!(sub_mod(a, b, m), ref_trim(&ref_rem(&lifted, &m)));
                assert_eq!(add_mod(neg_mod(a, m), a, m), [0; N]);
            }
        }
    }

    #[test]
    fn four_and_six_limb_ops_match_schoolbook_reference() {
        check_wide_ops::<4>(2, &[PALLAS_P, PALLAS_Q, BLS_R, SECP_P, SECP_N, ED_PRIME]);
        check_wide_ops::<6>(3, &[BLS_P]);
    }

    #[test]
    fn byte_codecs_round_trip_in_both_orders() {
        let mut rng = Rng(4);
        for _ in 0..200 {
            let a = rng.limbs::<4>();
            let le: [u8; 32] = to_le_bytes(a);
            let be: [u8; 32] = to_be_bytes(a);
            for (i, &limb) in a.iter().enumerate() {
                assert_eq!(le[8 * i..8 * i + 8], limb.to_le_bytes());
                assert_eq!(be[32 - 8 * (i + 1)..32 - 8 * i], limb.to_be_bytes());
            }
            let mut reversed = le;
            reversed.reverse();
            assert_eq!(reversed, be);
            assert_eq!(from_le_bytes::<4, 32>(&le), a);
            assert_eq!(from_be_bytes::<4, 32>(&be), a);

            let c = rng.limbs::<6>();
            let le: [u8; 48] = to_le_bytes(c);
            let mut be: [u8; 48] = to_be_bytes(c);
            assert_eq!(from_le_bytes::<6, 48>(&le), c);
            assert_eq!(from_be_bytes::<6, 48>(&be), c);
            be.reverse();
            assert_eq!(be, le);
        }
        let mut one_be = [0u8; 32];
        one_be[31] = 1;
        assert_eq!(from_be_bytes::<4, 32>(&one_be), one());
    }

    /// `-m^{-1} mod 2^64` by Newton iteration.
    fn mont_inv(m0: u64) -> u64 {
        let mut x = 1u64;
        for _ in 0..6 {
            x = x.wrapping_mul(2u64.wrapping_sub(m0.wrapping_mul(x)));
        }
        assert_eq!(m0.wrapping_mul(x), 1);
        x.wrapping_neg()
    }

    fn check_mont<const N: usize>(seed: u64, m: [u64; N]) {
        let inv = mont_inv(m[0]);
        let mut r2_wide = alloc::vec![0u64; 2 * N + 1];
        r2_wide[2 * N] = 1;
        let r2: [u64; N] = ref_trim(&ref_rem(&r2_wide, &m));
        let mul = |a, b| mont_mul(mont_mul(a, b, m, inv), r2, m, inv);
        let last = ref_trim(&ref_sub(&m, &[1]));

        assert_eq!(mul(last, last), one());
        assert_eq!(mul(last, [0; N]), [0; N]);
        let mut rng = Rng(seed);
        for _ in 0..200 {
            let (a, b) = (rng.below(m), rng.below(m));
            assert_eq!(mul(a, b), ref_mul_mod(a, b, m));
            assert_eq!(mul(a, one()), a);
            let a_m = mont_mul(a, r2, m, inv);
            assert!(lt(a_m, m));
            assert_eq!(mont_mul(a_m, one(), m, inv), a);
        }

        let p_minus_2 = ref_trim(&ref_sub(&m, &[2]));
        assert_eq!(mont_pow([0; N], p_minus_2, m, inv, r2), [0; N]);
        assert_eq!(mont_pow(last, [0; N], m, inv, r2), one());
        for _ in 0..4 {
            let a = rng.below(m);
            let a_inv = mont_pow(a, p_minus_2, m, inv, r2);
            assert_eq!(mul(a, a_inv), if a == [0; N] { [0; N] } else { one() });
            let mut cube = [0u64; N];
            cube[0] = 3;
            assert_eq!(mont_pow(a, cube, m, inv, r2), mul(mul(a, a), a));
        }
    }

    #[test]
    fn montgomery_matches_schoolbook_for_pallas_and_bls_moduli() {
        check_mont::<4>(5, PALLAS_P);
        check_mont::<4>(6, PALLAS_Q);
        check_mont::<4>(7, BLS_R);
        check_mont::<6>(8, BLS_P);
    }
}
