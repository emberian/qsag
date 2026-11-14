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
