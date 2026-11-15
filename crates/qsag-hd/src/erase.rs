//! Safe erasure barriers, retaining the underlying volatile wipe guarantee.
#[inline(never)]
pub(crate) fn ct_zeroize_bytes(secret: &mut [u8]) {
    secret.fill(0);
    core::hint::black_box(&mut *secret);
    qsag_accel::ct::ct_zeroize_bytes(secret);
}

#[inline(never)]
pub(crate) fn ct_zeroize_u32s(secret: &mut [u32]) {
    secret.fill(0);
    core::hint::black_box(&mut *secret);
    qsag_accel::ct::ct_zeroize_u32s(secret);
}

/// Owned temporary seed material, erased on success, early return and unwind.
pub(crate) struct SecretBytes(pub(crate) alloc::vec::Vec<u8>);

impl Drop for SecretBytes {
    fn drop(&mut self) {
        ct_zeroize_bytes(&mut self.0);
    }
}

/// Temporary field words erased before their allocation is released.
pub(crate) struct SecretWords(pub(crate) alloc::vec::Vec<u32>);
impl core::ops::Deref for SecretWords {
    type Target = alloc::vec::Vec<u32>;
    fn deref(&self) -> &Self::Target { &self.0 }
}
impl core::ops::DerefMut for SecretWords {
    fn deref_mut(&mut self) -> &mut Self::Target { &mut self.0 }
}
impl Drop for SecretWords {
    fn drop(&mut self) {
        ct_zeroize_u32s(&mut self.0);
        #[cfg(test)]
        WORD_WIPES.with(|events| {
            if let Some(events) = &mut *events.borrow_mut() {
                events.push((self.0.len(), self.0.iter().all(|v| *v == 0)));
            }
        });
    }
}

#[cfg(test)]
std::thread_local! {
    static WORD_WIPES: std::cell::RefCell<Option<alloc::vec::Vec<(usize, bool)>>> = const { std::cell::RefCell::new(None) };
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn partial_field_buffers_are_erased_on_error() {
        fn fail() -> Result<(), ()> {
            let mut words = SecretWords(alloc::vec::Vec::with_capacity(7));
            words.extend_from_slice(&[11, 12, 13]);
            Err(())?;
            Ok(())
        }
        WORD_WIPES.with(|events| *events.borrow_mut() = Some(alloc::vec::Vec::new()));
        assert!(fail().is_err());
        assert_eq!(WORD_WIPES.with(|events| events.borrow_mut().take().unwrap()), alloc::vec![(3, true)]);
    }
}
