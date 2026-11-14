//! Secret-memory wiping through the audited assembly crate's safe typed API.
use core::hint::black_box;
use crate::field::goldilocks::{Goldilocks, GoldilocksExt2};
use crate::field::tower::{Tower128, TowerGf256};

#[inline]
fn volatile_zero_slice<T: Copy>(buf: &mut [T], zero: T) {
    qsag_asm::volatile_fill(buf, zero);
}

/// Deterministically overwrite a byte slice with zeros (`core::ptr::write_volatile` + `SeqCst` fence).
#[inline(never)]
pub fn wipe_bytes(buf: &mut [u8]) {
    volatile_zero_slice(buf, 0u8);
}

/// Alias for [`wipe_bytes`] used across `fips205` and `tsw_baggy`.
#[inline(never)]
pub fn wipe_slice(buf: &mut [u8]) {
    volatile_zero_slice(buf, 0u8);
}

/// Deterministically overwrite a fixed 16-byte array with zeros.
#[inline(never)]
pub fn wipe_bytes16(buf: &mut [u8; 16]) {
    volatile_zero_slice(buf.as_mut_slice(), 0u8);
}

/// Deterministically overwrite a fixed 32-byte array with zeros.
#[inline(never)]
pub fn wipe_bytes32(buf: &mut [u8; 32]) {
    volatile_zero_slice(buf.as_mut_slice(), 0u8);
}

/// Deterministically overwrite a `u16` slice with zeros via `write_volatile` + `SeqCst` fence.
#[inline(never)]
pub fn wipe_u16s(buf: &mut [u16]) {
    volatile_zero_slice(buf, 0u16);
}

/// Deterministically overwrite a `u64` slice with zeros via `write_volatile` + `SeqCst` fence.
#[inline(never)]
pub fn wipe_u64s(buf: &mut [u64]) {
    volatile_zero_slice(buf, 0u64);
}

/// Deterministically overwrite a `u128` slice with zeros via `write_volatile` + `SeqCst` fence.
#[inline(never)]
pub fn wipe_u128s(buf: &mut [u128]) {
    volatile_zero_slice(buf, 0u128);
}

/// Deterministically overwrite a `Goldilocks` slice with zeros via `write_volatile` + `SeqCst` fence.
#[inline(never)]
pub fn wipe_goldilocks(buf: &mut [Goldilocks]) {
    volatile_zero_slice(buf, Goldilocks::ZERO);
}

/// Deterministically overwrite a `GoldilocksExt2` slice with zeros via `write_volatile` + `SeqCst` fence.
#[inline(never)]
pub fn wipe_ext2(buf: &mut [GoldilocksExt2]) {
    volatile_zero_slice(buf, GoldilocksExt2::ZERO);
}

/// Deterministically overwrite a `TowerGf256` slice with zeros via `write_volatile` + `SeqCst` fence.
#[inline(never)]
pub fn wipe_gf256_slice(buf: &mut [TowerGf256]) {
    volatile_zero_slice(buf, TowerGf256::ZERO);
}

/// Deterministically overwrite a `Tower128` slice with zeros via `write_volatile` + `SeqCst` fence.
#[inline(never)]
pub fn wipe_tower128_slice(buf: &mut [Tower128]) {
    volatile_zero_slice(buf, Tower128::ZERO);
}

/// Constant-time equality over equal-length byte slices (returns `false` immediately only if
/// public slice lengths differ).
#[inline]
pub fn ct_eq_bytes(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut diff = 0u8;
    for (&x, &y) in a.iter().zip(b.iter()) {
        diff |= x ^ y;
    }
    let diff = black_box(diff);
    (((diff as u16).wrapping_sub(1)) >> 15) == 1
}

/// Constant-time equality over 32-byte arrays.
#[inline]
pub fn ct_eq_bytes32(a: &[u8; 32], b: &[u8; 32]) -> bool {
    ct_eq_bytes(a, b)
}

/// Constant-time equality over `u64` words.
#[inline]
pub fn ct_eq_u64(a: u64, b: u64) -> bool {
    let diff = black_box(a ^ b);
    let folded = (diff | diff.wrapping_neg()) >> 63;
    folded == 0
}

/// Constant-time equality over `u128` words.
#[inline]
pub fn ct_eq_u128(a: u128, b: u128) -> bool {
    let lo = (a ^ b) as u64;
    let hi = ((a ^ b) >> 64) as u64;
    ct_eq_u64(lo | hi, 0)
}

/// Constant-time branchless byte select: returns `if_true` if `choice == true`, else `if_false`.
#[inline]
pub fn ct_select_u8(choice: bool, if_true: u8, if_false: u8) -> u8 {
    let mask = 0u8.wrapping_sub(black_box(choice as u8));
    if_false ^ (mask & (if_true ^ if_false))
}

/// Constant-time branchless `u64` select: returns `if_true` if `choice == true`, else `if_false`.
#[inline]
pub fn ct_select_u64(choice: bool, if_true: u64, if_false: u64) -> u64 {
    let mask = 0u64.wrapping_sub(black_box(choice as u64));
    if_false ^ (mask & (if_true ^ if_false))
}

/// Constant-time branchless `u128` select: returns `if_true` if `choice == true`, else `if_false`.
#[inline]
pub fn ct_select_u128(choice: bool, if_true: u128, if_false: u128) -> u128 {
    let mask = 0u128.wrapping_sub(black_box(choice as u128));
    if_false ^ (mask & (if_true ^ if_false))
}

/// Constant-time 32-byte array select: returns `if_true` if `choice == true`, else `if_false`.
#[inline]
pub fn ct_select_bytes32(choice: bool, if_true: &[u8; 32], if_false: &[u8; 32]) -> [u8; 32] {
    let mask = 0u8.wrapping_sub(black_box(choice as u8));
    let mut out = [0u8; 32];
    for i in 0..32 {
        out[i] = if_false[i] ^ (mask & (if_true[i] ^ if_false[i]));
    }
    out
}

/// Recursive wiping for owned temporary share buffers.
pub(crate) trait SecretWipe { fn secret_wipe(&mut self); }
impl SecretWipe for u8 { fn secret_wipe(&mut self) { qsag_asm::volatile_fill(core::slice::from_mut(self), 0); } }
impl SecretWipe for u128 { fn secret_wipe(&mut self) { qsag_asm::volatile_fill(core::slice::from_mut(self), 0); } }
impl SecretWipe for u64 { fn secret_wipe(&mut self) { qsag_asm::volatile_fill(core::slice::from_mut(self), 0); } }
impl SecretWipe for Tower128 { fn secret_wipe(&mut self) { qsag_asm::volatile_fill(core::slice::from_mut(&mut self.0), 0); } }
impl<T: SecretWipe, const N: usize> SecretWipe for [T; N] {
    fn secret_wipe(&mut self) { for x in self { x.secret_wipe(); } }
}
impl<T: SecretWipe> SecretWipe for alloc::vec::Vec<T> {
    fn secret_wipe(&mut self) { for x in self { x.secret_wipe(); } }
}
/// Wipes the owned buffer on normal and error exits, including unwinding.
pub(crate) struct SecretBuffer<T: SecretWipe>(pub T);
impl<T: SecretWipe> core::ops::Deref for SecretBuffer<T> {
    type Target = T;
    fn deref(&self) -> &T { &self.0 }
}
impl<T: SecretWipe> core::ops::DerefMut for SecretBuffer<T> {
    fn deref_mut(&mut self) -> &mut T { &mut self.0 }
}
impl<T: SecretWipe> Drop for SecretBuffer<T> {
    fn drop(&mut self) { self.0.secret_wipe(); black_box(&mut self.0); }
}

#[cfg(test)]
mod raii_tests {
    use super::*;
    #[test]
    fn secret_buffer_wipes_on_question_mark() {
        struct Probe<'a>(&'a core::cell::Cell<bool>);
        impl SecretWipe for Probe<'_> {
            fn secret_wipe(&mut self) { self.0.set(true); }
        }
        fn fail(wiped: &core::cell::Cell<bool>) -> Result<(), ()> {
            let _guard = SecretBuffer(Probe(wiped));
            Err(())?;
            Ok(())
        }
        let wiped = core::cell::Cell::new(false);
        assert!(fail(&wiped).is_err());
        assert!(wiped.get());
        let mut words = alloc::vec![[u64::MAX; 8]; 3];
        words.secret_wipe();
        assert_eq!(words, alloc::vec![[0; 8]; 3]);
    }
}
