//! Canonical subgroup scalars. Encodings in this module are little endian.
use crate::{limbs, secp256k1_ct::SECP_N};
use qsag_accel::ct::{ct_zeroize_bytes, ct_zeroize_u64s};

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
        let mut candidate = Self {
            bytes: [0u8; 32],
            group,
        };
        candidate.bytes.copy_from_slice(&bytes);
        ct_zeroize_bytes(&mut bytes);
        let mut value = decode(&candidate.bytes);
        let valid = limbs::lt(value, group.order()) & !limbs::is_zero(value);
        ct_zeroize_u64s(&mut value);
        if valid {
            Some(candidate)
        } else {
            drop(candidate);
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

#[inline]
pub(crate) fn decode(bytes: &[u8; 32]) -> [u64; 4] {
    limbs::from_le_bytes(bytes)
}
#[inline]
pub(crate) fn encode(value: [u64; 4]) -> [u8; 32] {
    limbs::to_le_bytes(value)
}
#[inline]
pub(crate) fn add(a: [u64; 4], b: [u64; 4], modulus: [u64; 4]) -> [u64; 4] {
    limbs::add_mod(a, b, modulus)
}
#[inline]
pub(crate) fn sub(a: [u64; 4], b: [u64; 4], modulus: [u64; 4]) -> [u64; 4] {
    limbs::sub_mod(a, b, modulus)
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
