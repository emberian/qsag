//! Secret-memory erasure shared by every crate in the workspace.
//!
//! One trait ([`SecretWipe`]), one scope guard ([`SecretBuffer`], with the aliases
//! [`SecretBytes`] and [`SecretVec`]) and one growable scratch buffer
//! ([`SecretScratch`]), all built on [`crate::volatile_fill`]. This crate sits below
//! every other workspace crate: `qsag_core::wipe` re-exports these items and adds the
//! field-element implementations, and crates that do not depend on `qsag-core` import
//! them from here. Protocol crates implement [`SecretWipe`] for their own types and
//! reuse the guards instead of redefining them.
//!
//! What each guard covers:
//! - [`SecretBuffer`] erases its contents when it leaves scope: normal return, `?`,
//!   and unwinding. Around a `Vec` ([`SecretVec`]) it also erases the spare capacity,
//!   so slots vacated by `truncate`/`pop`/`clear` do not survive. A `Vec` method
//!   reached through `DerefMut` can still reallocate and free the old storage
//!   unerased; grow with [`SecretBuffer::push_wiping`] / [`SecretBuffer::extend_wiping`]
//!   or size the vector up front.
//! - [`SecretScratch`] dereferences to a slice, so no reallocating `Vec` method is
//!   reachable at all: growth erases the old allocation, truncation and consuming
//!   iteration erase the vacated slots. Use it for scratch that grows and shrinks.

use crate::volatile_fill;
use core::ops::{Deref, DerefMut};

/// Overwrite `self` with zeros through volatile writes.
pub trait SecretWipe {
    fn secret_wipe(&mut self);

    /// Erase a whole slice. Word types override this with a single volatile fill.
    fn wipe_slice(items: &mut [Self])
    where
        Self: Sized,
    {
        for item in items {
            item.secret_wipe();
        }
    }
}

/// Erase any [`SecretWipe`] value in place, including unsized slices.
#[inline]
pub fn wipe<T: SecretWipe + ?Sized>(secret: &mut T) {
    secret.secret_wipe();
}

macro_rules! wipe_words {
    ($($t:ty),* $(,)?) => { $(
        impl SecretWipe for $t {
            #[inline]
            fn secret_wipe(&mut self) {
                volatile_fill(core::slice::from_mut(self), 0);
            }
            #[inline]
            fn wipe_slice(items: &mut [Self]) {
                volatile_fill(items, 0);
            }
        }
    )* };
}
wipe_words!(
    u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize
);

impl SecretWipe for bool {
    #[inline]
    fn secret_wipe(&mut self) {
        volatile_fill(core::slice::from_mut(self), false);
    }
    #[inline]
    fn wipe_slice(items: &mut [Self]) {
        volatile_fill(items, false);
    }
}

impl<T: SecretWipe> SecretWipe for [T] {
    #[inline]
    fn secret_wipe(&mut self) {
        T::wipe_slice(self);
    }
}

impl<T: SecretWipe, const N: usize> SecretWipe for [T; N] {
    #[inline]
    fn secret_wipe(&mut self) {
        T::wipe_slice(self);
    }
    #[inline]
    fn wipe_slice(items: &mut [Self]) {
        T::wipe_slice(items.as_flattened_mut());
    }
}

impl<T: SecretWipe + ?Sized> SecretWipe for &mut T {
    #[inline]
    fn secret_wipe(&mut self) {
        (**self).secret_wipe();
    }
}

impl<T: SecretWipe> SecretWipe for Option<T> {
    #[inline]
    fn secret_wipe(&mut self) {
        if let Some(inner) = self {
            inner.secret_wipe();
        }
    }
}

macro_rules! wipe_tuples {
    ($(($($name:ident $idx:tt),+)),* $(,)?) => { $(
        impl<$($name: SecretWipe),+> SecretWipe for ($($name,)+) {
            #[inline]
            fn secret_wipe(&mut self) {
                $( self.$idx.secret_wipe(); )+
            }
        }
    )* };
}
wipe_tuples!((A 0, B 1), (A 0, B 1, C 2), (A 0, B 1, C 2, D 3));

/// Zero the bytes between a vector's length and its capacity. They are not live
/// values, but `truncate`, `pop` and `clear` leave former secrets there.
#[cfg(feature = "alloc")]
fn wipe_spare_capacity<T>(v: &mut alloc::vec::Vec<T>) {
    let spare = v.spare_capacity_mut();
    let bytes = core::mem::size_of_val(spare);
    // SAFETY: `spare` is `bytes` writable bytes owned by the vector, and any byte
    // pattern, including zero, is valid for `MaybeUninit<u8>`.
    let raw = unsafe {
        core::slice::from_raw_parts_mut(
            spare.as_mut_ptr().cast::<core::mem::MaybeUninit<u8>>(),
            bytes,
        )
    };
    volatile_fill(raw, core::mem::MaybeUninit::new(0u8));
}

#[cfg(feature = "alloc")]
impl<T: SecretWipe> SecretWipe for alloc::vec::Vec<T> {
    fn secret_wipe(&mut self) {
        T::wipe_slice(self);
        wipe_spare_capacity(self);
    }
}

#[cfg(feature = "alloc")]
impl<T: SecretWipe + ?Sized> SecretWipe for alloc::boxed::Box<T> {
    #[inline]
    fn secret_wipe(&mut self) {
        (**self).secret_wipe();
    }
}

/// Owns a secret and erases it when it leaves scope, on every exit path.
pub struct SecretBuffer<T: SecretWipe>(pub T);

/// Fixed-size secret byte array, for keys, seeds and digests held on the stack.
pub type SecretBytes<const N: usize> = SecretBuffer<[u8; N]>;

/// Heap-allocated secret vector.
#[cfg(feature = "alloc")]
pub type SecretVec<T> = SecretBuffer<alloc::vec::Vec<T>>;

impl<T: SecretWipe> SecretBuffer<T> {
    /// Same as the tuple constructor; usable through the type aliases, which the
    /// tuple constructor is not.
    #[inline]
    pub const fn new(secret: T) -> Self {
        Self(secret)
    }
}

impl<const N: usize> SecretBuffer<[u8; N]> {
    #[inline]
    pub const fn zeroed() -> Self {
        Self([0u8; N])
    }
}

#[cfg(feature = "alloc")]
impl<T: Copy + SecretWipe> SecretBuffer<alloc::vec::Vec<T>> {
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self(alloc::vec::Vec::with_capacity(capacity))
    }
    /// [`secret_vec_push`] on the owned vector.
    #[inline]
    pub fn push_wiping(&mut self, item: T) {
        secret_vec_push(&mut self.0, item);
    }
    /// [`secret_vec_extend_from_slice`] on the owned vector.
    #[inline]
    pub fn extend_wiping(&mut self, slice: &[T]) {
        secret_vec_extend_from_slice(&mut self.0, slice);
    }
}

impl<T: SecretWipe + Default> SecretBuffer<T> {
    /// Release the secret to the caller, who becomes responsible for erasing it.
    ///
    /// The value is moved out and the guard's own storage is then erased byte for
    /// byte, so no placeholder is built, wiped and dropped in its place. Always
    /// inlined, so `self` is not first moved into a separate callee parameter slot
    /// that the wipe below would not reach.
    #[inline(always)]
    pub fn into_inner(self) -> T {
        let mut slot = core::mem::MaybeUninit::new(self);
        // SAFETY: `slot` holds an initialized guard whose only field is the secret.
        // The secret is read out exactly once, and `slot` is never read or dropped
        // as a guard again.
        let secret = unsafe { core::ptr::read(&raw const (*slot.as_ptr()).0) };
        // SAFETY: `slot` is `size_of::<Self>()` writable bytes, and any byte pattern
        // is valid for `MaybeUninit<u8>`.
        let raw = unsafe {
            core::slice::from_raw_parts_mut(
                slot.as_mut_ptr().cast::<core::mem::MaybeUninit<u8>>(),
                core::mem::size_of::<Self>(),
            )
        };
        volatile_fill(raw, core::mem::MaybeUninit::new(0u8));
        secret
    }
}

impl<T: SecretWipe> Deref for SecretBuffer<T> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &T {
        &self.0
    }
}

impl<T: SecretWipe> DerefMut for SecretBuffer<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
        &mut self.0
    }
}

impl<T: SecretWipe> Drop for SecretBuffer<T> {
    fn drop(&mut self) {
        self.0.secret_wipe();
        core::hint::black_box(&mut self.0);
    }
}

impl<T: SecretWipe> core::fmt::Debug for SecretBuffer<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("SecretBuffer([REDACTED])")
    }
}

/// Grow `v` to hold `additional` more items without abandoning an unerased
/// allocation: on reallocation the live items are copied, then the old storage is
/// erased before it is freed.
#[cfg(feature = "alloc")]
pub fn secret_vec_reserve<T: Copy + SecretWipe>(v: &mut alloc::vec::Vec<T>, additional: usize) {
    let needed = v
        .len()
        .checked_add(additional)
        .expect("secret buffer size overflow");
    if needed > v.capacity() {
        let new_cap = needed.max(v.capacity().saturating_mul(2)).max(8);
        let mut next = alloc::vec::Vec::with_capacity(new_cap);
        next.extend_from_slice(v.as_slice());
        v.secret_wipe();
        core::hint::black_box(v.as_mut_slice());
        *v = next;
    }
}

/// `Vec::push` through [`secret_vec_reserve`].
#[cfg(feature = "alloc")]
#[inline]
pub fn secret_vec_push<T: Copy + SecretWipe>(v: &mut alloc::vec::Vec<T>, item: T) {
    secret_vec_reserve(v, 1);
    v.push(item);
}

/// `Vec::extend_from_slice` through [`secret_vec_reserve`].
#[cfg(feature = "alloc")]
#[inline]
pub fn secret_vec_extend_from_slice<T: Copy + SecretWipe>(v: &mut alloc::vec::Vec<T>, slice: &[T]) {
    secret_vec_reserve(v, slice.len());
    v.extend_from_slice(slice);
}

/// Growable secret scratch. Growth erases the old allocation before releasing it;
/// truncation, consuming iteration and drop erase the vacated slots. It dereferences
/// to a slice, so no `Vec` method that could reallocate is reachable.
#[cfg(feature = "alloc")]
pub struct SecretScratch<T: SecretWipe + Copy>(alloc::vec::Vec<T>);

#[cfg(feature = "alloc")]
impl<T: SecretWipe + Copy> SecretScratch<T> {
    #[inline]
    pub const fn new() -> Self {
        Self(alloc::vec::Vec::new())
    }
    #[inline]
    pub fn with_capacity(n: usize) -> Self {
        Self(alloc::vec::Vec::with_capacity(n))
    }
    #[inline]
    pub fn as_slice(&self) -> &[T] {
        &self.0
    }
    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        &mut self.0
    }
    #[inline]
    pub fn capacity(&self) -> usize {
        self.0.capacity()
    }
    pub fn reserve(&mut self, additional: usize) {
        secret_vec_reserve(&mut self.0, additional);
    }
    pub fn push(&mut self, value: T) {
        secret_vec_push(&mut self.0, value);
    }
    pub fn extend_from_slice(&mut self, values: &[T]) {
        secret_vec_extend_from_slice(&mut self.0, values);
    }
    pub fn truncate(&mut self, len: usize) {
        if len < self.0.len() {
            T::wipe_slice(&mut self.0[len..]);
            self.0.truncate(len);
        }
    }
    pub fn clear(&mut self) {
        self.truncate(0);
    }
    pub fn resize(&mut self, len: usize, value: T) {
        if len < self.0.len() {
            self.truncate(len);
        } else {
            self.reserve(len - self.0.len());
            self.0.resize(len, value);
        }
    }
}

#[cfg(feature = "alloc")]
impl<T: SecretWipe + Copy> Default for SecretScratch<T> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(feature = "alloc")]
impl<T: SecretWipe + Copy> Clone for SecretScratch<T> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

#[cfg(feature = "alloc")]
impl<T: SecretWipe + Copy> Drop for SecretScratch<T> {
    fn drop(&mut self) {
        self.0.secret_wipe();
        core::hint::black_box(self.0.as_mut_slice());
    }
}

#[cfg(feature = "alloc")]
impl<T: SecretWipe + Copy> core::fmt::Debug for SecretScratch<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("SecretScratch([REDACTED])")
    }
}

#[cfg(feature = "alloc")]
impl<T: SecretWipe + Copy> Deref for SecretScratch<T> {
    type Target = [T];
    #[inline]
    fn deref(&self) -> &[T] {
        &self.0
    }
}

#[cfg(feature = "alloc")]
impl<T: SecretWipe + Copy> DerefMut for SecretScratch<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut [T] {
        &mut self.0
    }
}

/// Takes ownership of an existing allocation; it is erased like any other.
#[cfg(feature = "alloc")]
impl<T: SecretWipe + Copy> From<alloc::vec::Vec<T>> for SecretScratch<T> {
    fn from(value: alloc::vec::Vec<T>) -> Self {
        Self(value)
    }
}

#[cfg(feature = "alloc")]
impl<T: SecretWipe + Copy> FromIterator<T> for SecretScratch<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let iter = iter.into_iter();
        let mut out = Self::with_capacity(iter.size_hint().0);
        out.extend(iter);
        out
    }
}

#[cfg(feature = "alloc")]
impl<T: SecretWipe + Copy> Extend<T> for SecretScratch<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        let iter = iter.into_iter();
        self.reserve(iter.size_hint().0);
        for value in iter {
            self.push(value);
        }
    }
}

#[cfg(feature = "alloc")]
impl<'a, T: SecretWipe + Copy> IntoIterator for &'a SecretScratch<T> {
    type Item = &'a T;
    type IntoIter = core::slice::Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

#[cfg(feature = "alloc")]
impl<'a, T: SecretWipe + Copy> IntoIterator for &'a mut SecretScratch<T> {
    type Item = &'a mut T;
    type IntoIter = core::slice::IterMut<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter_mut()
    }
}

/// Consuming iterator over a [`SecretScratch`]: each slot is erased as it is yielded,
/// and the remainder when the iterator is dropped.
#[cfg(feature = "alloc")]
pub struct SecretIntoIter<T: SecretWipe + Copy> {
    values: SecretScratch<T>,
    pos: usize,
}

#[cfg(feature = "alloc")]
impl<T: SecretWipe + Copy> Iterator for SecretIntoIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<T> {
        let slot = self.values.get_mut(self.pos)?;
        let value = *slot;
        slot.secret_wipe();
        self.pos += 1;
        Some(value)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        let n = self.values.len() - self.pos;
        (n, Some(n))
    }
}

#[cfg(feature = "alloc")]
impl<T: SecretWipe + Copy> ExactSizeIterator for SecretIntoIter<T> {}

#[cfg(feature = "alloc")]
impl<T: SecretWipe + Copy> IntoIterator for SecretScratch<T> {
    type Item = T;
    type IntoIter = SecretIntoIter<T>;
    fn into_iter(self) -> Self::IntoIter {
        SecretIntoIter {
            values: self,
            pos: 0,
        }
    }
}

#[cfg(all(test, feature = "std"))]
mod tests {
    use super::*;
    use alloc::vec;
    use alloc::vec::Vec;
    use core::cell::Cell;

    /// Counts erasures of slots that still hold a nonzero value.
    #[derive(Clone, Copy)]
    struct Probe<'a> {
        value: u64,
        wiped: &'a Cell<usize>,
    }
    impl SecretWipe for Probe<'_> {
        fn secret_wipe(&mut self) {
            if self.value != 0 {
                self.wiped.set(self.wiped.get() + 1);
            }
            self.value.secret_wipe();
        }
    }

    #[test]
    fn buffer_erases_on_error_return_and_unwind() {
        fn fail(bytes: &mut [u8; 32]) -> Result<(), ()> {
            let _guard = SecretBuffer(bytes);
            Err(())?;
            Ok(())
        }
        let mut bytes = [0x5a; 32];
        assert!(fail(&mut bytes).is_err());
        assert_eq!(bytes, [0; 32]);

        bytes.fill(0x7b);
        let unwound = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _guard = SecretBuffer(&mut bytes);
            panic!("injected failure");
        }));
        assert!(unwound.is_err());
        assert_eq!(bytes, [0; 32]);
    }

    #[test]
    fn aliases_construct_and_grow_without_abandoning_storage() {
        let wiped = Cell::new(0);
        let probe = Probe {
            value: 7,
            wiped: &wiped,
        };
        let mut v: SecretVec<Probe<'_>> = SecretVec::with_capacity(1);
        v.push_wiping(probe);
        v.extend_wiping(&[probe; 8]);
        assert_eq!(wiped.get(), 1, "the outgrown allocation was erased");
        assert_eq!(v.len(), 9);
        drop(v);
        assert_eq!(wiped.get(), 10);

        let mut key = SecretBytes::<32>::zeroed();
        key.fill(0xa5);
        assert_eq!(*SecretBytes::new([1u8; 4]), [1u8; 4]);
        assert_eq!(std::format!("{key:?}"), "SecretBuffer([REDACTED])");
        let released: [u8; 32] = key.into_inner();
        assert_eq!(released, [0xa5; 32]);
    }

    #[test]
    fn into_inner_releases_the_same_allocation_unerased() {
        let mut v: SecretVec<u8> = SecretVec::with_capacity(64);
        v.extend_wiping(&[0xa5; 48]);
        let (base, capacity) = (v.as_ptr(), v.capacity());
        let released: Vec<u8> = v.into_inner();
        assert_eq!((released.as_ptr(), released.capacity()), (base, capacity));
        assert_eq!(released, [0xa5; 48]);

        let boxed = SecretBuffer(vec![7u16; 5].into_boxed_slice());
        let base = boxed.as_ptr();
        let released = boxed.into_inner();
        assert_eq!(released.as_ptr(), base);
        assert_eq!(*released, [7u16; 5]);

        let nested = SecretBuffer((u64::MAX, [3u8; 5], Some(-1i16))).into_inner();
        assert_eq!(nested, (u64::MAX, [3u8; 5], Some(-1i16)));
    }

    #[test]
    fn nested_words_tuples_and_options_are_zeroed() {
        let mut words = vec![[u64::MAX; 8]; 3];
        words.secret_wipe();
        assert_eq!(words, vec![[0; 8]; 3]);

        let mut nested: [[u32; 4]; 2] = [[7; 4]; 2];
        let mut mixed = (u128::MAX, [0xffu8; 5], Some(-1i16), true);
        wipe(&mut nested);
        wipe(&mut mixed);
        assert_eq!(nested, [[0; 4]; 2]);
        assert_eq!(mixed, (0, [0; 5], Some(0), false));

        let mut boxed: alloc::boxed::Box<[u16]> = vec![9u16; 6].into_boxed_slice();
        boxed.secret_wipe();
        assert!(boxed.iter().all(|&x| x == 0));
    }

    #[test]
    fn vec_erasure_reaches_slots_vacated_by_truncate() {
        let mut v = SecretBuffer(vec![0xa5u8; 64]);
        v.truncate(8);
        let base = v.as_ptr();
        v.secret_wipe();
        // SAFETY: the 64-byte allocation is still owned by `v`, and all of it was
        // written by `secret_wipe`.
        let all = unsafe { core::slice::from_raw_parts(base, 64) };
        assert_eq!(all, [0u8; 64]);
    }

    #[test]
    fn secret_scratch_erases_growth_truncation_iteration_and_unwind() {
        let wiped = Cell::new(0);
        let probe = Probe {
            value: 42,
            wiped: &wiped,
        };
        let mut values = SecretScratch::with_capacity(2);
        values.extend([probe; 2]);
        values.reserve(3);
        assert_eq!(wiped.get(), 2, "growth erases the old allocation");
        assert!(values.iter().all(|p| p.value == 42));
        values.resize(4, probe);
        values.truncate(2);
        assert_eq!(wiped.get(), 4, "truncation erases the vacated slots");
        let mut iter = values.into_iter();
        assert_eq!(iter.next().unwrap().value, 42);
        assert_eq!(wiped.get(), 5, "a consumed slot is erased");
        drop(iter);
        assert_eq!(wiped.get(), 6, "an abandoned iterator erases the rest");

        let failed = (|| -> Result<(), ()> {
            let _scratch: SecretScratch<_> = [probe; 3].into_iter().collect();
            Err(())?;
            Ok(())
        })();
        assert!(failed.is_err());
        assert_eq!(wiped.get(), 9);

        let unwound = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _stack = SecretBuffer([probe; 4]);
            let _heap: SecretScratch<_> = [probe; 2].into_iter().collect();
            panic!("injected failure");
        }));
        assert!(unwound.is_err());
        assert_eq!(wiped.get(), 15);
    }

    #[test]
    fn secret_scratch_reuses_its_allocation_and_plain_vec_helpers_agree() {
        let mut fields: SecretScratch<[[u64; 4]; 2]> = vec![[[u64::MAX; 4]; 2]; 64].into();
        let allocation = fields.as_ptr();
        fields.clear();
        fields.extend([[[7; 4]; 2]; 64]);
        assert_eq!(allocation, fields.as_ptr());
        assert_eq!(fields.len(), 64);

        let mut grow: Vec<u64> = Vec::with_capacity(2);
        secret_vec_push(&mut grow, 0xDEAD_BEEF);
        secret_vec_push(&mut grow, 0xCAFE_BABE);
        secret_vec_extend_from_slice(&mut grow, &[1, 2, 3, 4]);
        assert_eq!(grow, [0xDEAD_BEEF, 0xCAFE_BABE, 1, 2, 3, 4]);
        grow.secret_wipe();
        assert_eq!(grow, [0u64; 6]);
    }
}
