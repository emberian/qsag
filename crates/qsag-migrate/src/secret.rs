//! Owned gadget scratch. Growth wipes the old allocation before releasing it;
//! truncation and consuming iteration also wipe vacated slots.
use alloc::vec::Vec;
use core::ops::{Deref, DerefMut};
use qsag_accel::ct::ct_zeroize_u64s;

pub(crate) trait Wipe: Copy {
    fn wipe(&mut self);
    fn wipe_slice(values: &mut [Self]) {
        for x in values {
            x.wipe();
        }
    }
}
impl Wipe for u64 {
    fn wipe(&mut self) {
        ct_zeroize_u64s(core::slice::from_mut(self));
    }
    fn wipe_slice(values: &mut [Self]) {
        ct_zeroize_u64s(values);
    }
}
impl Wipe for u128 {
    fn wipe(&mut self) {
        qsag_asm::volatile_fill(core::slice::from_mut(self), 0);
    }
    fn wipe_slice(values: &mut [Self]) {
        qsag_asm::volatile_fill(values, 0);
    }
}
impl<T: Wipe, const N: usize> Wipe for [T; N] {
    fn wipe(&mut self) {
        T::wipe_slice(self);
    }
    fn wipe_slice(values: &mut [Self]) {
        T::wipe_slice(values.as_flattened_mut());
    }
}
impl<A: Wipe, B: Wipe> Wipe for (A, B) {
    fn wipe(&mut self) {
        self.0.wipe();
        self.1.wipe();
    }
}
#[derive(Clone)]
pub(crate) struct SecretVec<T: Wipe>(Vec<T>);
impl<T: Wipe> Default for SecretVec<T> {
    fn default() -> Self {
        Self::new()
    }
}
impl<T: Wipe> SecretVec<T> {
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        &mut self.0
    }
    pub fn new() -> Self {
        Self(Vec::new())
    }
    pub fn with_capacity(n: usize) -> Self {
        Self(Vec::with_capacity(n))
    }
    pub fn reserve(&mut self, additional: usize) {
        let required = self
            .len()
            .checked_add(additional)
            .expect("scratch size overflow");
        if required > self.0.capacity() {
            let mut next = Self::with_capacity(required.max(self.0.capacity().saturating_mul(2)));
            next.0.extend_from_slice(&self.0);
            core::mem::swap(self, &mut next);
        }
    }
    pub fn push(&mut self, value: T) {
        self.reserve(1);
        self.0.push(value);
    }
    pub fn extend_from_slice(&mut self, values: &[T]) {
        self.reserve(values.len());
        self.0.extend_from_slice(values);
    }
    pub fn truncate(&mut self, len: usize) {
        if len < self.len() {
            T::wipe_slice(&mut self.0[len..]);
        }
        self.0.truncate(len);
    }
    pub fn clear(&mut self) {
        self.truncate(0);
    }
    pub fn resize(&mut self, len: usize, value: T) {
        if len < self.len() {
            self.truncate(len);
        } else {
            self.reserve(len - self.len());
            self.0.resize(len, value);
        }
    }
}
impl<T: Wipe> Drop for SecretVec<T> {
    fn drop(&mut self) {
        T::wipe_slice(&mut self.0);
    }
}
impl<T: Wipe> Deref for SecretVec<T> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        &self.0
    }
}
impl<T: Wipe> DerefMut for SecretVec<T> {
    fn deref_mut(&mut self) -> &mut [T] {
        &mut self.0
    }
}
impl<T: Wipe> From<Vec<T>> for SecretVec<T> {
    fn from(value: Vec<T>) -> Self {
        Self(value)
    }
}
impl<T: Wipe> FromIterator<T> for SecretVec<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let iter = iter.into_iter();
        let mut out = Self::with_capacity(iter.size_hint().0);
        out.extend(iter);
        out
    }
}
impl<T: Wipe> Extend<T> for SecretVec<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        let iter = iter.into_iter();
        self.reserve(iter.size_hint().0);
        for value in iter {
            self.push(value);
        }
    }
}
impl<'a, T: Wipe> IntoIterator for &'a SecretVec<T> {
    type Item = &'a T;
    type IntoIter = core::slice::Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
impl<'a, T: Wipe> IntoIterator for &'a mut SecretVec<T> {
    type Item = &'a mut T;
    type IntoIter = core::slice::IterMut<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}
pub(crate) struct SecretIntoIter<T: Wipe> {
    values: SecretVec<T>,
    pos: usize,
}
impl<T: Wipe> Iterator for SecretIntoIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<T> {
        let slot = self.values.get_mut(self.pos)?;
        let value = *slot;
        slot.wipe();
        self.pos += 1;
        Some(value)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        let n = self.values.len() - self.pos;
        (n, Some(n))
    }
}
impl<T: Wipe> ExactSizeIterator for SecretIntoIter<T> {}
impl<T: Wipe> IntoIterator for SecretVec<T> {
    type Item = T;
    type IntoIter = SecretIntoIter<T>;
    fn into_iter(self) -> Self::IntoIter {
        SecretIntoIter {
            values: self,
            pos: 0,
        }
    }
}

/// Fixed-size stack scratch with the same drop guarantee as heap scratch.
pub(crate) struct Secret<T: Wipe>(pub T);
impl<T: Wipe> Drop for Secret<T> {
    fn drop(&mut self) {
        self.0.wipe();
    }
}
impl<T: Wipe> Deref for Secret<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.0
    }
}
impl<T: Wipe> DerefMut for Secret<T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::cell::Cell;

    #[derive(Clone, Copy)]
    struct Probe<'a> {
        value: u64,
        wiped: &'a Cell<usize>,
    }
    impl Wipe for Probe<'_> {
        fn wipe(&mut self) {
            if self.value != 0 {
                self.wiped.set(self.wiped.get() + 1);
            }
            self.value.wipe();
        }
    }

    #[test]
    fn scratch_wipes_growth_truncation_iteration_and_errors() {
        let wiped = Cell::new(0);
        let probe = Probe {
            value: 42,
            wiped: &wiped,
        };
        let mut values = SecretVec::with_capacity(2);
        values.extend([probe; 2]);
        values.reserve(3);
        assert_eq!(wiped.get(), 2, "old allocation must be wiped on growth");
        assert!(values.iter().all(|p| p.value == 42));
        values.resize(4, probe);
        values.truncate(2);
        assert_eq!(wiped.get(), 4, "truncated slots must be wiped immediately");
        let mut iter = values.into_iter();
        assert_eq!(iter.next().unwrap().value, 42);
        assert_eq!(wiped.get(), 5, "consumed slot must be wiped");
        drop(iter);
        assert_eq!(
            wiped.get(),
            6,
            "abandoned iterator must wipe remaining slots"
        );
        let result = (|| -> Result<(), ()> {
            let _scratch: SecretVec<_> = [probe; 3].into_iter().collect();
            Err(())?;
            Ok(())
        })();
        assert!(result.is_err());
        assert_eq!(wiped.get(), 9);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _stack = Secret([probe; 4]);
            let _heap: SecretVec<_> = [probe; 2].into_iter().collect();
            panic!("scratch unwind test");
        }));
        assert!(result.is_err());
        assert_eq!(wiped.get(), 15);
    }

    #[test]
    fn nested_field_scratch_is_zeroed_and_reusable() {
        let mut fields: SecretVec<[[u64; 4]; 2]> = alloc::vec![[[u64::MAX; 4]; 2]; 64].into();
        <[[u64; 4]; 2]>::wipe_slice(&mut fields);
        assert!(fields.iter().flatten().flatten().all(|&x| x == 0));
        let allocation = fields.as_ptr();
        fields.clear();
        fields.extend([[[7; 4]; 2]; 64]);
        assert_eq!(allocation, fields.as_ptr(), "reuse must not allocate");
        assert_eq!(fields.len(), 64);
    }
}
