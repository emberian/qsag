//! Constant-time comparisons, branchless conditional selection, volatile memory wiping,
//! and redacted secret containers.

use crate::AccelError;
use core::fmt;
use core::hint::black_box;

/// Wipe a mutable byte slice using `write_volatile` + sequential-consistency compiler fence
/// so LTO/dead-store elimination cannot elide secret erasure on drop.
#[inline(never)]
pub fn ct_zeroize_bytes(buf: &mut [u8]) {
    qsag_asm::volatile_fill(buf, 0);
}

/// Wipe a mutable `u32` slice via `write_volatile`.
#[inline(never)]
pub fn ct_zeroize_u32s(buf: &mut [u32]) {
    qsag_asm::volatile_fill(buf, 0);
}

/// Wipe a mutable `i32` slice via `write_volatile`.
#[inline(never)]
pub fn ct_zeroize_i32s(buf: &mut [i32]) {
    qsag_asm::volatile_fill(buf, 0);
}

/// Wipe a mutable `u64` slice via `write_volatile`.
#[inline(never)]
pub fn ct_zeroize_u64s(buf: &mut [u64]) {
    qsag_asm::volatile_fill(buf, 0);
}

/// Wipe a mutable `i64` slice via `write_volatile`.
#[inline(never)]
pub fn ct_zeroize_i64s(buf: &mut [i64]) {
    qsag_asm::volatile_fill(buf, 0);
}

/// Wipe a mutable `u128` slice via `write_volatile`.
#[inline(never)]
pub fn ct_zeroize_u128s(buf: &mut [u128]) {
    qsag_asm::volatile_fill(buf, 0);
}

/// Return all-ones `u64` mask (`u64::MAX`) if `choice`, else `0`.
#[inline]
pub const fn ct_mask_u64(choice: bool) -> u64 {
    (choice as u64).wrapping_neg()
}

/// Return all-ones `u128` mask (`u128::MAX`) if `choice`, else `0`.
#[inline]
pub const fn ct_mask_u128(choice: bool) -> u128 {
    (choice as u128).wrapping_neg()
}

/// Return all-ones `u8` mask (`0xFF`) if `choice`, else `0`.
#[inline]
pub const fn ct_mask_u8(choice: bool) -> u8 {
    (choice as u8).wrapping_neg()
}

/// Expand the low bit of `bit` into an all-ones / all-zero `u64` mask.
#[inline]
pub const fn ct_mask_from_bit_u64(bit: u64) -> u64 {
    (bit & 1).wrapping_neg()
}

/// Truncate a `u64` mask to a `u8` mask (`0xFF` or `0x00`).
#[inline]
pub const fn ct_mask_u64_to_u8(mask: u64) -> u8 {
    (mask & 0xFF) as u8
}

/// Equality mask over `u64`: `u64::MAX` iff `a == b`, else `0`.
///
/// The difference and the resulting mask each pass through a `core::hint::black_box` value
/// barrier so the optimizer cannot rewrite the mask arithmetic into a data-dependent branch.
#[inline]
pub fn ct_eq_mask_u64(a: u64, b: u64) -> u64 {
    let diff = black_box(a ^ b);
    let nonzero_bit = (diff | diff.wrapping_neg()) >> 63;
    black_box(nonzero_bit.wrapping_sub(1))
}

/// Equality mask over `u128`: `u64::MAX` iff `a == b`, else `0`.
#[inline]
pub fn ct_eq_mask_u128(a: u128, b: u128) -> u64 {
    let diff = a ^ b;
    ct_eq_mask_u64((diff as u64) | ((diff >> 64) as u64), 0)
}

/// Equality mask over byte slices: `u64::MAX` iff the slices have equal length and contents.
///
/// Slice lengths are public; only the contents are compared in constant time.
#[inline]
pub fn ct_eq_bytes_mask(a: &[u8], b: &[u8]) -> u64 {
    let len_mask = ct_eq_mask_u64(a.len() as u64, b.len() as u64);
    let mut acc = 0u8;
    for (&x, &y) in a.iter().zip(b.iter()) {
        acc |= x ^ y;
    }
    ct_eq_mask_u64(black_box(acc) as u64, 0) & len_mask
}

/// Strict unsigned less-than mask over `u64`: `u64::MAX` iff `a < b`, else `0`.
#[inline]
pub const fn ct_lt_mask_u64(a: u64, b: u64) -> u64 {
    // Borrow-out of `a - b`, computed from the operands and the wrapped difference.
    let (a, b) = (black_box(a), black_box(b));
    let borrow = ((!a & b) | ((!a | b) & a.wrapping_sub(b))) >> 63;
    black_box(borrow.wrapping_neg())
}

/// Strict unsigned less-than mask over `u128`: `u64::MAX` iff `a < b`, else `0`.
#[inline]
pub const fn ct_lt_mask_u128(a: u128, b: u128) -> u64 {
    let (a, b) = (black_box(a), black_box(b));
    let borrow = ((!a & b) | ((!a | b) & a.wrapping_sub(b))) >> 127;
    black_box((borrow as u64).wrapping_neg())
}

/// Mask-driven selection: `if_true` when `mask == u64::MAX`, `if_false` when `mask == 0`.
#[inline]
pub const fn ct_select_mask_u64(mask: u64, if_true: u64, if_false: u64) -> u64 {
    let m = black_box(mask);
    black_box((if_true & m) | (if_false & !m))
}

/// Mask-driven conditional copy of `src` into `dst` (`mask == 0xFF` copies, `mask == 0x00` keeps).
#[inline]
pub fn ct_conditional_assign_bytes_mask(
    mask: u8,
    dst: &mut [u8],
    src: &[u8],
) -> Result<(), AccelError> {
    if dst.len() != src.len() {
        return Err(AccelError::LengthMismatch {
            what: "ct_conditional_assign_bytes src",
            expected: dst.len(),
            actual: src.len(),
        });
    }
    let m = black_box(mask);
    for (d, &s) in dst.iter_mut().zip(src.iter()) {
        *d = (s & m) | (*d & !m);
    }
    Ok(())
}

/// Equality over `u64`, evaluated through [`ct_eq_mask_u64`].
#[inline]
pub fn ct_eq_u64(a: u64, b: u64) -> bool {
    ct_eq_mask_u64(a, b) & 1 == 1
}

/// Equality over `u128`, evaluated through [`ct_eq_mask_u128`].
#[inline]
pub fn ct_eq_u128(a: u128, b: u128) -> bool {
    ct_eq_mask_u128(a, b) & 1 == 1
}

/// Equality over byte slices, evaluated through [`ct_eq_bytes_mask`]. Returns `false` if lengths differ.
#[inline]
pub fn ct_eq_bytes(a: &[u8], b: &[u8]) -> bool {
    ct_eq_bytes_mask(a, b) & 1 == 1
}

/// Branchless conditional selection: returns `if_true` when `choice` is `true`, else `if_false`.
#[inline]
pub const fn ct_select_u64(choice: bool, if_true: u64, if_false: u64) -> u64 {
    ct_select_mask_u64(ct_mask_u64(choice), if_true, if_false)
}

/// Branchless conditional selection over `u128`.
#[inline]
pub const fn ct_select_u128(choice: bool, if_true: u128, if_false: u128) -> u128 {
    let m = black_box(ct_mask_u128(choice));
    black_box((if_true & m) | (if_false & !m))
}

/// Branchless conditional copy of `src` into `dst` iff `choice == true`.
///
/// Returns [`AccelError::LengthMismatch`] (and leaves `dst` untouched) when the slices differ in length.
#[inline]
pub fn ct_conditional_assign_bytes(
    choice: bool,
    dst: &mut [u8],
    src: &[u8],
) -> Result<(), AccelError> {
    ct_conditional_assign_bytes_mask(ct_mask_u8(choice), dst, src)
}

/// Branchless unsigned strict less-than `a < b` over `u64`.
#[inline]
pub const fn ct_lt_u64(a: u64, b: u64) -> bool {
    ct_lt_mask_u64(a, b) & 1 == 1
}

/// Branchless unsigned less-than-or-equal `a <= b` over `u64`.
#[inline]
pub const fn ct_le_u64(a: u64, b: u64) -> bool {
    ct_lt_mask_u64(b, a) & 1 == 0
}

/// Branchless unsigned strict less-than `a < b` over `u128`.
#[inline]
pub const fn ct_lt_u128(a: u128, b: u128) -> bool {
    ct_lt_mask_u128(a, b) & 1 == 1
}

/// Fixed-size secret byte container with `<REDACTED>` `fmt::Debug`, constant-time equality,
/// and mandatory `write_volatile` zeroization on `Drop`.
pub struct RedactedSecret<const N: usize>([u8; N]);

impl<const N: usize> RedactedSecret<N> {
    #[inline]
    pub const fn new(bytes: [u8; N]) -> Self {
        Self(bytes)
    }

    #[inline]
    pub const fn expose(&self) -> &[u8; N] {
        &self.0
    }

    #[inline]
    pub fn expose_mut(&mut self) -> &mut [u8; N] {
        &mut self.0
    }
}

impl<const N: usize> PartialEq for RedactedSecret<N> {
    fn eq(&self, other: &Self) -> bool {
        ct_eq_bytes(&self.0, &other.0)
    }
}

impl<const N: usize> Eq for RedactedSecret<N> {}

impl<const N: usize> fmt::Debug for RedactedSecret<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("RedactedSecret(<REDACTED>)")
    }
}

impl<const N: usize> Drop for RedactedSecret<N> {
    fn drop(&mut self) {
        ct_zeroize_bytes(&mut self.0);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const EDGE: [u64; 8] = [
        0,
        1,
        2,
        0x7FFF_FFFF_FFFF_FFFF,
        0x8000_0000_0000_0000,
        0x8000_0000_0000_0001,
        u64::MAX - 1,
        u64::MAX,
    ];

    #[test]
    fn masks_agree_with_native_comparisons_on_edge_values() {
        for &a in &EDGE {
            for &b in &EDGE {
                assert_eq!(ct_eq_mask_u64(a, b), if a == b { u64::MAX } else { 0 });
                assert_eq!(ct_lt_mask_u64(a, b), if a < b { u64::MAX } else { 0 });
                assert_eq!(ct_eq_u64(a, b), a == b);
                assert_eq!(ct_lt_u64(a, b), a < b);
                assert_eq!(ct_le_u64(a, b), a <= b);
                let (wa, wb) = ((a as u128) << 64 | b as u128, (b as u128) << 64 | a as u128);
                assert_eq!(ct_eq_mask_u128(wa, wb), if wa == wb { u64::MAX } else { 0 });
                assert_eq!(ct_lt_mask_u128(wa, wb), if wa < wb { u64::MAX } else { 0 });
                assert_eq!(ct_lt_u128(wa, wb), wa < wb);
                assert_eq!(
                    ct_select_mask_u64(ct_eq_mask_u64(a, b), 7, 9),
                    if a == b { 7 } else { 9 }
                );
            }
        }
        assert_eq!(ct_mask_from_bit_u64(1), u64::MAX);
        assert_eq!(ct_mask_from_bit_u64(2), 0);
        assert_eq!(ct_mask_u64_to_u8(u64::MAX), 0xFF);
    }

    #[test]
    fn byte_equality_mask_covers_length_and_single_bit_differences() {
        let a = [0x5Au8; 33];
        let mut b = a;
        assert_eq!(ct_eq_bytes_mask(&a, &b), u64::MAX);
        for i in 0..b.len() {
            b[i] ^= 0x80;
            assert_eq!(ct_eq_bytes_mask(&a, &b), 0);
            b[i] ^= 0x80;
        }
        assert_eq!(ct_eq_bytes_mask(&a, &b[..32]), 0);
        assert!(!ct_eq_bytes(&a[..0], &b[..1]));
        assert!(ct_eq_bytes(&[], &[]));
    }

    #[test]
    fn conditional_assign_rejects_length_mismatch_without_writing() {
        let mut dst = [1u8; 4];
        assert_eq!(
            ct_conditional_assign_bytes(true, &mut dst, &[9u8; 5]),
            Err(AccelError::LengthMismatch {
                what: "ct_conditional_assign_bytes src",
                expected: 4,
                actual: 5,
            })
        );
        assert_eq!(dst, [1u8; 4]);
        ct_conditional_assign_bytes(false, &mut dst, &[9u8; 4]).unwrap();
        assert_eq!(dst, [1u8; 4]);
        ct_conditional_assign_bytes(true, &mut dst, &[9u8; 4]).unwrap();
        assert_eq!(dst, [9u8; 4]);
    }
}
