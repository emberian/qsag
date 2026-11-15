//! Scope-bound wiping for temporary protocol buffers, including error returns.
use alloc::vec::Vec;
use core::ops::{Deref, DerefMut};

pub(crate) trait Wipe {
    fn wipe(&mut self);
}
impl Wipe for u8 {
    fn wipe(&mut self) {
        qsag_accel::ct::ct_zeroize_bytes(core::slice::from_mut(self));
    }
}
impl Wipe for u32 {
    fn wipe(&mut self) {
        qsag_accel::ct::ct_zeroize_u32s(core::slice::from_mut(self));
    }
}
impl Wipe for u64 {
    fn wipe(&mut self) {
        qsag_accel::ct::ct_zeroize_u64s(core::slice::from_mut(self));
    }
}
impl Wipe for u128 {
    fn wipe(&mut self) {
        let mut limbs = [*self as u64, (*self >> 64) as u64];
        qsag_accel::ct::ct_zeroize_u64s(&mut limbs);
        *self = (limbs[0] as u128) | ((limbs[1] as u128) << 64);
    }
}
impl Wipe for usize {
    fn wipe(&mut self) {
        qsag_asm::volatile_fill(core::slice::from_mut(self), 0);
    }
}
impl<A: Wipe, B: Wipe> Wipe for (A, B) {
    fn wipe(&mut self) {
        self.0.wipe();
        self.1.wipe();
    }
}
impl<T: Wipe, const N: usize> Wipe for [T; N] {
    fn wipe(&mut self) {
        for value in self {
            value.wipe();
        }
    }
}
impl<T: Wipe> Wipe for Vec<T> {
    fn wipe(&mut self) {
        for value in self {
            value.wipe();
        }
    }
}
pub(crate) struct SecretBuffer<T: Wipe>(pub T);
impl<T: Wipe> Drop for SecretBuffer<T> {
    fn drop(&mut self) {
        self.0.wipe();
    }
}
impl<T: Wipe> Deref for SecretBuffer<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.0
    }
}
impl<T: Wipe> DerefMut for SecretBuffer<T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.0
    }
}
impl<T: Wipe + Default> SecretBuffer<T> {
    pub fn into_inner(mut self) -> T {
        core::mem::take(&mut self.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    struct Borrowed<'a>(&'a mut [u8; 32]);
    impl Wipe for Borrowed<'_> {
        fn wipe(&mut self) {
            self.0.wipe();
        }
    }
    #[test]
    fn guard_wipes_before_error_returns_and_unwinding() {
        fn fail(bytes: &mut [u8; 32]) -> Result<(), ()> {
            let _guard = SecretBuffer(Borrowed(bytes));
            Err(())?;
            Ok(())
        }
        let mut bytes = [0x5a; 32];
        assert!(fail(&mut bytes).is_err());
        assert_eq!(bytes, [0; 32]);
        bytes.fill(0x7b);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _guard = SecretBuffer(Borrowed(&mut bytes));
            panic!("injected failure");
        }));
        assert!(result.is_err());
        assert_eq!(bytes, [0; 32]);
    }
}
