//! Canonical subgroup scalars. Encodings in this module are little endian.
use crate::secp256k1_ct::SECP_N;
use qsag_accel::ct::{ct_select_u64, ct_zeroize_bytes, ct_zeroize_u64s};

/// Domain separator for canonical spending-key migration nullifiers (version 1).
pub const NULLIFIER_DOMAIN: u64 = 0x4d49_475f_4e55_4c31;

pub(crate) const ED_ORDER: [u64; 4] = [
    0x5812_631a_5cf5_d3ed,
    0x14de_f9de_a2f7_9cd6,
    0,
    0x1000_0000_0000_0000,
];
pub(crate) const ED_PRIME: [u64; 4] = [
    0xffff_ffff_ffff_ffed,
    u64::MAX,
    u64::MAX,
    0x7fff_ffff_ffff_ffff,
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ScalarGroup {
    Secp256k1,
    Ed25519,
}
impl ScalarGroup {
    pub(crate) fn order(self) -> [u64; 4] {
        match self {
            Self::Secp256k1 => SECP_N,
            Self::Ed25519 => ED_ORDER,
        }
    }
}

/// A nonzero, reduced spending scalar, with volatile cleanup on drop.
pub struct SpendingScalar {
    pub(crate) bytes: [u8; 32],
    pub(crate) group: ScalarGroup,
}
impl core::fmt::Debug for SpendingScalar {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SpendingScalar")
            .field("group", &self.group)
            .field("bytes", &"<REDACTED>")
            .finish()
    }
}
impl Drop for SpendingScalar {
    fn drop(&mut self) {
        ct_zeroize_bytes(&mut self.bytes);
    }
}
impl SpendingScalar {
    pub fn from_le_bytes(mut bytes: [u8; 32], group: ScalarGroup) -> Option<Self> {
        let limbs = decode(&bytes);
        let valid = less(limbs, group.order()) & (limbs.iter().fold(0, |a, &b| a | b) != 0);
        if valid {
            Some(Self { bytes, group })
        } else {
            ct_zeroize_bytes(&mut bytes);
            None
        }
    }
    pub fn group(&self) -> ScalarGroup {
        self.group
    }
    pub fn as_le_bytes(&self) -> &[u8; 32] {
        &self.bytes
    }

    /// Return the canonical big-endian encoding. The caller owns its cleanup.
    pub fn to_be_bytes(&self) -> [u8; 32] {
        let mut bytes = self.bytes;
        bytes.reverse();
        bytes
    }

    /// Bind a migration nullifier to the spending key, subgroup and replay domain.
    ///
    /// Use the same domain for every destination and every legacy address format
    /// in one migration campaign. Changing the destination must not permit the
    /// same key to migrate twice. Domain allocation and replay tracking belong to
    /// the caller. This helper does not establish ownership of a public key.
    pub fn compute_nullifier(&self, migration_domain: &[u8; 32]) -> [u64; 4] {
        use qsag_accel::goldilocks::pack_bytes32_to_limbs56;
        use qsag_accel::poseidon2::poseidon2_hash_limbs;

        let mut bytes = self.to_be_bytes();
        let mut limbs = pack_bytes32_to_limbs56(&bytes);
        ct_zeroize_bytes(&mut bytes);
        let domain = pack_bytes32_to_limbs56(migration_domain);
        let mut input = [0; 11];
        input[0] = match self.group {
            ScalarGroup::Secp256k1 => 1,
            ScalarGroup::Ed25519 => 2,
        };
        input[1..6].copy_from_slice(&limbs);
        input[6..].copy_from_slice(&domain);
        ct_zeroize_u64s(&mut limbs);
        let nullifier = poseidon2_hash_limbs(NULLIFIER_DOMAIN, &input);
        ct_zeroize_u64s(&mut input);
        nullifier
    }
}

pub(crate) fn decode(bytes: &[u8; 32]) -> [u64; 4] {
    core::array::from_fn(|i| u64::from_le_bytes(bytes[i * 8..i * 8 + 8].try_into().unwrap()))
}
pub(crate) fn encode(limbs: [u64; 4]) -> [u8; 32] {
    let mut out = [0; 32];
    for (chunk, limb) in out.chunks_exact_mut(8).zip(limbs) {
        chunk.copy_from_slice(&limb.to_le_bytes());
    }
    out
}
fn subtract(a: [u64; 4], b: [u64; 4]) -> ([u64; 4], bool) {
    let mut borrow = false;
    let out = core::array::from_fn(|i| {
        let (x, b0) = a[i].overflowing_sub(b[i]);
        let (x, b1) = x.overflowing_sub(u64::from(borrow));
        borrow = b0 | b1;
        x
    });
    (out, borrow)
}
pub(crate) fn less(a: [u64; 4], b: [u64; 4]) -> bool {
    subtract(a, b).1
}
pub(crate) fn add(a: [u64; 4], b: [u64; 4], modulus: [u64; 4]) -> [u64; 4] {
    let mut carry = 0u128;
    let sum = core::array::from_fn(|i| {
        carry += a[i] as u128 + b[i] as u128;
        let limb = carry as u64;
        carry >>= 64;
        limb
    });
    let (diff, borrow) = subtract(sum, modulus);
    core::array::from_fn(|i| ct_select_u64((carry != 0) | !borrow, diff[i], sum[i]))
}
pub(crate) fn sub(a: [u64; 4], b: [u64; 4], modulus: [u64; 4]) -> [u64; 4] {
    let (diff, borrow) = subtract(a, b);
    let mut carry = 0u128;
    core::array::from_fn(|i| {
        carry += diff[i] as u128 + ct_select_u64(borrow, modulus[i], 0) as u128;
        let limb = carry as u64;
        carry >>= 64;
        limb
    })
}
pub(crate) fn reduce(bytes: &[u8; 32], modulus: [u64; 4]) -> [u64; 4] {
    let mut out = [0; 4];
    for &byte in bytes.iter().rev() {
        for bit in (0..8).rev() {
            out = add(out, out, modulus);
            out = add(out, [((byte >> bit) & 1) as u64, 0, 0, 0], modulus);
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn canonical_boundaries_and_wrap() {
        for group in [ScalarGroup::Secp256k1, ScalarGroup::Ed25519] {
            let q = group.order();
            let last = sub(q, [1, 0, 0, 0], q);
            assert_eq!(add(last, [1, 0, 0, 0], q), [0; 4]);
            assert_eq!(sub([0; 4], [1, 0, 0, 0], q), last);
            assert!(SpendingScalar::from_le_bytes(encode(q), group).is_none());
            assert!(SpendingScalar::from_le_bytes([0; 32], group).is_none());
            assert!(SpendingScalar::from_le_bytes(encode(last), group).is_some());
            assert_eq!(reduce(&encode(q), q), [0; 4]);
        }
    }
}
