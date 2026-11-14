//! Scope-bound wiping for temporary protocol buffers, including error returns.
use alloc::vec::Vec;
use core::ops::{Deref, DerefMut};

pub(crate) trait Wipe { fn wipe(&mut self); }
impl Wipe for u8 { fn wipe(&mut self) { qsag_accel::ct::ct_zeroize_bytes(core::slice::from_mut(self)); } }
impl Wipe for u32 { fn wipe(&mut self) { qsag_accel::ct::ct_zeroize_u32s(core::slice::from_mut(self)); } }
impl Wipe for u64 { fn wipe(&mut self) { qsag_accel::ct::ct_zeroize_u64s(core::slice::from_mut(self)); } }
impl<T: Wipe, const N: usize> Wipe for [T; N] {
    fn wipe(&mut self) { for value in self { value.wipe(); } }
}
impl<T: Wipe> Wipe for Vec<T> {
    fn wipe(&mut self) { for value in self { value.wipe(); } }
}
pub(crate) struct SecretBuffer<T: Wipe>(pub T);
impl<T: Wipe> Drop for SecretBuffer<T> { fn drop(&mut self) { self.0.wipe(); } }
impl<T: Wipe> Deref for SecretBuffer<T> { type Target = T; fn deref(&self) -> &T { &self.0 } }
impl<T: Wipe> DerefMut for SecretBuffer<T> { fn deref_mut(&mut self) -> &mut T { &mut self.0 } }
impl<T: Wipe + Default> SecretBuffer<T> {
    pub fn into_inner(mut self) -> T { core::mem::take(&mut self.0) }
}
