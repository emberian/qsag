use super::*;

use qsag_agg::zk_hem::v2::field5::Fp5 as Field;

#[derive(Clone, Copy, Default, Eq)]
pub(super) struct Fp5(pub(super) [Goldilocks; 5]);

impl core::fmt::Debug for Fp5 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_tuple("Fp5").field(&"<REDACTED>").finish()
    }
}

impl PartialEq for Fp5 {
    fn eq(&self, other: &Self) -> bool {
        let mut diff = 0u64;
        for (a, b) in self.0.iter().zip(other.0.iter()) {
            diff |= a.to_canonical_u64() ^ b.to_canonical_u64();
        }
        qsag_accel::ct::ct_eq_u64(diff, 0)
    }
}
impl SecretWipe for Fp5 {
    fn secret_wipe(&mut self) {
        self.0.secret_wipe();
    }
}

impl Fp5 {
    pub(super) const ZERO: Self = Self([Goldilocks::ZERO; 5]);
    pub(super) const ONE: Self = Self([
        Goldilocks::ONE,
        Goldilocks::ZERO,
        Goldilocks::ZERO,
        Goldilocks::ZERO,
        Goldilocks::ZERO,
    ]);

    /// Strict lift of five wire limbs: `None` if any limb lies in the alias band `[p, 2^64)`.
    #[inline]
    pub(super) fn from_canonical_limbs(limbs: [u64; 5]) -> Option<Self> {
        let mut out = [Goldilocks::ZERO; 5];
        for (slot, limb) in out.iter_mut().zip(limbs) {
            *slot = Goldilocks::from_canonical(limb).ok()?;
        }
        Some(Self(out))
    }

    /// Branchless lift of limbs that are canonical by construction (rejection-sampled tapes,
    /// already validated wire limbs); the identity on every canonical limb.
    #[inline]
    pub(super) fn from_limbs(limbs: [u64; 5]) -> Self {
        Self(limbs.map(Goldilocks::from_u64_reduced))
    }

    #[inline]
    pub(super) fn to_limbs(self) -> [u64; 5] {
        self.0.map(Goldilocks::to_canonical_u64)
    }

    /// Canonical limbs widened for lazy `u128` accumulation.
    #[inline]
    pub(super) fn to_wide_limbs(self) -> [u128; 5] {
        self.0.map(|limb| limb.to_canonical_u64() as u128)
    }

    #[inline]
    pub(super) fn is_zero(self) -> bool {
        let l = self.to_limbs();
        (l[0] | l[1] | l[2] | l[3] | l[4]) == 0
    }

    pub(super) fn add(self, rhs: Self) -> Self {
        Self((Field::from_limbs(self.0) + Field::from_limbs(rhs.0)).to_limbs())
    }

    pub(super) fn sub(self, rhs: Self) -> Self {
        Self((Field::from_limbs(self.0) - Field::from_limbs(rhs.0)).to_limbs())
    }

    pub(super) fn scale_fp(self, s: u64) -> Self {
        Self(
            Field::from_limbs(self.0)
                .mul_base(Goldilocks::from_u64_reduced(s))
                .to_limbs(),
        )
    }

    pub(super) fn mul(self, rhs: Self) -> Self {
        Self((Field::from_limbs(self.0) * Field::from_limbs(rhs.0)).to_limbs())
    }

    #[inline]
    pub(super) fn to_le_bytes(self) -> [u8; 40] {
        let mut out = [0u8; 40];
        for (chunk, limb) in out.chunks_exact_mut(8).zip(self.0) {
            chunk.copy_from_slice(&limb.to_le_bytes());
        }
        out
    }
}
