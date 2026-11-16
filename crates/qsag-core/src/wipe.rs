//! Secret-memory wiping through the audited assembly crate's safe typed API.
//!
//! ### The zeroizing wrappers
//! There is one set of them in the workspace. They are defined in `qsag_asm::wipe`, below
//! every other crate, and this module is their path for every crate that depends on
//! `qsag-core` (`no_std` + `alloc`): it re-exports them and implements [`SecretWipe`] for
//! the field types defined here. A crate does not define its own wrapper; it implements
//! [`SecretWipe`] for its own secret types and uses these:
//!
//! | item | use |
//! |---|---|
//! | [`SecretWipe`] | recursive volatile wipe of a value; implemented for integer words, arrays, tuples, `Option`, `Box`, `Vec` and the field types |
//! | [`SecretBuffer`]`<T>` | owner that wipes `T` on return, on `?` and on unwinding |
//! | [`SecretBytes`]`<N>` | `SecretBuffer<[u8; N]>`: keys, seeds and digests on the stack |
//! | [`SecretVec`]`<T>` | `SecretBuffer<Vec<T>>`: heap secrets; grow with `push_wiping` / `extend_wiping` |
//! | [`SecretScratch`]`<T>` | vector whose growth, truncation and consuming iteration all wipe |
//! | [`secret_vec_reserve`], [`secret_vec_push`], [`secret_vec_extend_from_slice`] | wipe-aware growth of a plain `Vec` |
//! | [`secret_vecs_with_capacity`] | per-party secret vectors that really have their capacity |
//!
//! `Vec` growth reached through `DerefMut` of a [`SecretVec`] can reallocate and free the
//! old storage unwiped: size the vector up front or use the wiping methods.
use crate::field::goldilocks::{Goldilocks, GoldilocksExt2};
use crate::field::tower::{Tower128, TowerGf256};
use core::hint::black_box;
use qsag_asm::volatile_fill;

/// Deterministically overwrite a byte slice with zeros (`core::ptr::write_volatile` + `SeqCst` fence).
#[inline(never)]
pub fn wipe_bytes(buf: &mut [u8]) {
    volatile_fill(buf, 0u8);
}

/// Alias for [`wipe_bytes`] used across `fips205` and `tsw_baggy`.
pub use self::wipe_bytes as wipe_slice;

/// Deterministically overwrite a fixed 16-byte array with zeros.
#[inline(never)]
pub fn wipe_bytes16(buf: &mut [u8; 16]) {
    volatile_fill(buf.as_mut_slice(), 0u8);
}

/// Deterministically overwrite a fixed 32-byte array with zeros.
#[inline(never)]
pub fn wipe_bytes32(buf: &mut [u8; 32]) {
    volatile_fill(buf.as_mut_slice(), 0u8);
}

/// Deterministically overwrite a `u16` slice with zeros via `write_volatile` + `SeqCst` fence.
#[inline(never)]
pub fn wipe_u16s(buf: &mut [u16]) {
    volatile_fill(buf, 0u16);
}

/// Deterministically overwrite a `u64` slice with zeros via `write_volatile` + `SeqCst` fence.
#[inline(never)]
pub fn wipe_u64s(buf: &mut [u64]) {
    volatile_fill(buf, 0u64);
}

/// Deterministically overwrite a `u128` slice with zeros via `write_volatile` + `SeqCst` fence.
#[inline(never)]
pub fn wipe_u128s(buf: &mut [u128]) {
    volatile_fill(buf, 0u128);
}

/// Deterministically overwrite a `Goldilocks` slice with zeros via `write_volatile` + `SeqCst` fence.
#[inline(never)]
pub fn wipe_goldilocks(buf: &mut [Goldilocks]) {
    volatile_fill(buf, Goldilocks::ZERO);
}

/// Deterministically overwrite a `GoldilocksExt2` slice with zeros via `write_volatile` + `SeqCst` fence.
#[inline(never)]
pub fn wipe_ext2(buf: &mut [GoldilocksExt2]) {
    volatile_fill(buf, GoldilocksExt2::ZERO);
}

/// Deterministically overwrite a `TowerGf256` slice with zeros via `write_volatile` + `SeqCst` fence.
#[inline(never)]
pub fn wipe_gf256_slice(buf: &mut [TowerGf256]) {
    volatile_fill(buf, TowerGf256::ZERO);
}

/// Deterministically overwrite a `Tower128` slice with zeros via `write_volatile` + `SeqCst` fence.
#[inline(never)]
pub fn wipe_tower128_slice(buf: &mut [Tower128]) {
    volatile_fill(buf, Tower128::ZERO);
}

/// Constant-time equality over byte slices (`false` at once only when the public lengths
/// differ), on the platform kernel of `qsag-asm`.
pub use qsag_asm::ct_eq_bytes;

/// Constant-time equality over 32-byte arrays, on the platform kernel of `qsag-asm`.
pub use qsag_asm::ct_eq_32 as ct_eq_bytes32;

/// Constant-time equality over `u64` and `u128` words.
pub use qsag_accel::ct::{ct_eq_u64, ct_eq_u128};

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

pub use qsag_asm::wipe::{
    SecretBuffer, SecretBytes, SecretIntoIter, SecretScratch, SecretVec, SecretWipe,
    secret_vec_extend_from_slice, secret_vec_push, secret_vec_reserve, wipe,
};

/// `outer` secret vectors, each with room for `capacity` items.
///
/// `vec![Vec::with_capacity(c); n]` does not do this: `vec!` clones the element and a
/// cloned `Vec` has no spare capacity, so all but the last vector reallocate on push and
/// free their old storage unwiped.
pub fn secret_vecs_with_capacity<T: SecretWipe>(
    outer: usize,
    capacity: usize,
) -> SecretVec<alloc::vec::Vec<T>> {
    SecretBuffer(
        (0..outer)
            .map(|_| alloc::vec::Vec::with_capacity(capacity))
            .collect(),
    )
}

impl SecretWipe for TowerGf256 {
    fn secret_wipe(&mut self) {
        volatile_fill(core::slice::from_mut(&mut self.0), 0);
    }
    fn wipe_slice(items: &mut [Self]) {
        volatile_fill(items, TowerGf256::ZERO);
    }
}
impl SecretWipe for Tower128 {
    fn secret_wipe(&mut self) {
        volatile_fill(core::slice::from_mut(&mut self.0), 0);
    }
    fn wipe_slice(items: &mut [Self]) {
        volatile_fill(items, Tower128::ZERO);
    }
}
impl SecretWipe for Goldilocks {
    fn secret_wipe(&mut self) {
        volatile_fill(core::slice::from_mut(&mut self.0), 0);
    }
    fn wipe_slice(items: &mut [Self]) {
        volatile_fill(items, Goldilocks::ZERO);
    }
}
impl SecretWipe for GoldilocksExt2 {
    fn secret_wipe(&mut self) {
        self.c0.secret_wipe();
        self.c1.secret_wipe();
    }
    fn wipe_slice(items: &mut [Self]) {
        volatile_fill(items, GoldilocksExt2::ZERO);
    }
}

#[cfg(test)]
mod ct_tests {
    use super::*;

    #[test]
    fn ct_equalities_agree_with_plain_equality() {
        let base: [u8; 71] = core::array::from_fn(|i| (i as u8).wrapping_mul(0x9d) ^ 0x35);
        for len in 0..=base.len() {
            let a = &base[..len];
            assert!(ct_eq_bytes(a, a));
            assert!(!ct_eq_bytes(a, &base[..len.saturating_sub(1)]) || len == 0);
            for pos in 0..len {
                for bit in [0x01u8, 0x10, 0x80] {
                    let mut b = base;
                    b[pos] ^= bit;
                    assert!(!ct_eq_bytes(a, &b[..len]), "len={len} pos={pos}");
                    assert!(!ct_eq_bytes(&b[..len], a), "len={len} pos={pos}");
                }
            }
        }
        assert!(!ct_eq_bytes(&[], &[0]));

        let x: [u8; 32] = core::array::from_fn(|i| 0xa7 ^ (i as u8).wrapping_mul(0x3b));
        assert!(ct_eq_bytes32(&x, &x));
        for pos in 0..32 {
            for bit in 0..8 {
                let mut y = x;
                y[pos] ^= 1 << bit;
                assert!(!ct_eq_bytes32(&x, &y), "pos={pos} bit={bit}");
            }
        }

        let edge = [0u64, 1, 2, 1 << 32, 1 << 63, u64::MAX - 1, u64::MAX];
        for &p in &edge {
            for &q in &edge {
                assert_eq!(ct_eq_u64(p, q), p == q);
                for &hi in &edge {
                    let (l, r) = (u128::from(p) | (u128::from(hi) << 64), u128::from(q));
                    assert_eq!(ct_eq_u128(l, r), l == r);
                    assert_eq!(ct_eq_u128(l, l ^ (u128::from(q) << 64)), q == 0);
                }
            }
        }
    }
}

#[cfg(test)]
mod raii_tests {
    use super::*;
    #[test]
    fn secret_buffer_wipes_on_question_mark() {
        struct Probe<'a>(&'a core::cell::Cell<bool>);
        impl SecretWipe for Probe<'_> {
            fn secret_wipe(&mut self) {
                self.0.set(true);
            }
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

        let mut grow = alloc::vec::Vec::with_capacity(2);
        secret_vec_push(&mut grow, 0xDEAD_BEEFu64);
        secret_vec_push(&mut grow, 0xCAFE_BABEu64);
        secret_vec_extend_from_slice(&mut grow, &[1u64, 2, 3, 4]);
        assert_eq!(
            grow,
            alloc::vec![0xDEAD_BEEFu64, 0xCAFE_BABEu64, 1, 2, 3, 4]
        );
        grow.secret_wipe();
        assert_eq!(grow, alloc::vec![0u64; 6]);

        let per_party = secret_vecs_with_capacity::<u64>(5, 7);
        assert!(per_party.len() == 5 && per_party.iter().all(|v| v.capacity() >= 7));
        // The trap the helper replaces: only the moved-in last element keeps its capacity.
        assert_eq!(
            alloc::vec![alloc::vec::Vec::<u64>::with_capacity(7); 5][0].capacity(),
            0
        );

        let mut key = SecretBytes::<32>::zeroed();
        key[7] = 9;
        let mut heap: SecretVec<u8> = SecretVec::with_capacity(1);
        heap.push_wiping(1);
        heap.extend_wiping(&key[..]);
        assert_eq!((heap.len(), heap[8]), (33, 9));
        assert_eq!(alloc::format!("{key:?}"), "SecretBuffer([REDACTED])");
        let mut nested = [[TowerGf256(7); 4]; 2];
        nested.secret_wipe();
        assert_eq!(nested, [[TowerGf256::ZERO; 4]; 2]);
    }
}
