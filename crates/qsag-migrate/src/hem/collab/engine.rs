//! Authenticated arithmetic over Goldilocks and its quintic extension `Fp5` for a quorum
//! of custodians.
//!
//! SPDZ over additive shares (Damgard, Pastro, Smart, Zakarias, CRYPTO 2012; the MAC check
//! is the commit-then-open check of SPDZ-2, Damgard et al., ESORICS 2013). A shared value
//! `x` is held as additive shares of `x` and of `alpha_0 x`, `alpha_1 x` for two
//! Goldilocks keys that are themselves additively shared. An extension-field value (`Fp5`)
//! carries the same two base-field keys limb by limb, so multiplying a share by a public
//! extension element is local.
//!
//! * **9-triple Toom-3 `Fp5` Beaver multiplication ([`Engine::mul_ext`]):** Two degree-4
//!   polynomials over `F_p` are evaluated locally at `{0, 1, -1, 2, -2, 3, -3, 4, inf}`,
//!   multiplied in one batched base-field Beaver round (`9` triples per `Fp5` product —
//!   43.75% fewer triples than `Fp4` schoolbook's 16 and 64% fewer than `Fp5` schoolbook's
//!   25), interpolated in `F_p`, and reduced modulo `u^5 - 3`.
//! * **Anti-rollback preprocessing burn before round 1 ([`Engine::new_anchored`]):** Every [`Preprocessing`] tape has a cryptographic
//!   identifier (`tape_id`) bound to its MAC key shares, lengths, and opening material.
//!   Session setup atomically burns `tape_id` (and, with [`Engine::new_anchored`], advances
//!   the hardware/external monotone counter via [`qsag_core::ExternalMonotoneAnchor`])
//!   before round 1 (`0` network messages sent). Persist the expected generation with
//!   the tape snapshot so a rollback remains detectable after a process restart.
//! * Opening a value sends the value shares and queues the MAC shares; [`Engine::check`]
//!   settles the queue (`2 / p^2 < 2^-126`) and checks echo-chain agreement across peers.

#[cfg(test)]
use alloc::vec;
use alloc::vec::Vec;

use qsag_agg::field::{Goldilocks, GoldilocksOps as _};
use qsag_agg::sponge::cshake256_32;
use qsag_agg::zk_hem::SeedStream;
use qsag_agg::zk_hem::v2::field5::Fp5;
use qsag_agg::zk_hem::v2::params::{EXT_BYTES, LIMBS};

use qsag_core::wipe::{SecretBuffer, SecretScratch, SecretWipe};

use super::net::{NetError, Transport};

type F = Goldilocks;
type E = Fp5;

/// Base-field Beaver triples consumed per `Fp5` product via Toom-3 interpolation.
pub const EXT_MUL_TRIPLES: usize = 9;

/// One party's share of an authenticated base-field value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Sb {
    pub v: F,
    pub m: [F; 2],
}

/// One party's share of an authenticated quintic extension-field value (`Fp5`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Sh {
    pub v: E,
    pub m: [E; 2],
}

impl SecretWipe for Sb {
    fn secret_wipe(&mut self) {
        Self::wipe_slice(core::slice::from_mut(self));
    }

    fn wipe_slice(items: &mut [Self]) {
        qsag_asm::volatile_fill(items, Self::ZERO);
    }
}

impl Sb {
    pub const ZERO: Self = Self {
        v: F::ZERO,
        m: [F::ZERO; 2],
    };

    #[inline]
    pub fn scale(self, k: F) -> Self {
        Self {
            v: self.v * k,
            m: [self.m[0] * k, self.m[1] * k],
        }
    }

    /// The share times a public extension element.
    #[inline]
    pub fn scale_ext(self, k: E) -> Sh {
        Sh {
            v: k.mul_base(self.v),
            m: [k.mul_base(self.m[0]), k.mul_base(self.m[1])],
        }
    }

    #[inline]
    pub fn lift(self) -> Sh {
        Sh {
            v: E::from_base(self.v),
            m: [E::from_base(self.m[0]), E::from_base(self.m[1])],
        }
    }
}

impl core::ops::Add for Sb {
    type Output = Self;
    #[inline]
    fn add(self, r: Self) -> Self {
        Self {
            v: self.v + r.v,
            m: [self.m[0] + r.m[0], self.m[1] + r.m[1]],
        }
    }
}

impl core::ops::Sub for Sb {
    type Output = Self;
    #[inline]
    fn sub(self, r: Self) -> Self {
        Self {
            v: self.v - r.v,
            m: [self.m[0] - r.m[0], self.m[1] - r.m[1]],
        }
    }
}

impl core::ops::AddAssign for Sb {
    #[inline]
    fn add_assign(&mut self, r: Self) {
        *self = *self + r;
    }
}

impl SecretWipe for Sh {
    fn secret_wipe(&mut self) {
        Self::wipe_slice(core::slice::from_mut(self));
    }

    fn wipe_slice(items: &mut [Self]) {
        qsag_asm::volatile_fill(items, Self::ZERO);
    }
}

impl Sh {
    pub const ZERO: Self = Self {
        v: E::ZERO,
        m: [E::ZERO; 2],
    };

    #[inline]
    pub fn scale(self, k: E) -> Self {
        Self {
            v: self.v * k,
            m: [self.m[0] * k, self.m[1] * k],
        }
    }

    /// Limb `j` (`0..5`) of the value, as a base-field share.
    #[inline]
    pub fn limb(self, j: usize) -> Sb {
        Sb {
            v: self.v.to_limbs()[j],
            m: [self.m[0].to_limbs()[j], self.m[1].to_limbs()[j]],
        }
    }

    /// Assemble an `Fp5` share from five base-field limb shares.
    #[inline]
    pub fn from_limbs(limbs: [Sb; LIMBS]) -> Self {
        Self {
            v: E::from_limbs(limbs.map(|s| s.v)),
            m: [
                E::from_limbs(limbs.map(|s| s.m[0])),
                E::from_limbs(limbs.map(|s| s.m[1])),
            ],
        }
    }
}

impl core::ops::Add for Sh {
    type Output = Self;
    #[inline]
    fn add(self, r: Self) -> Self {
        Self {
            v: self.v + r.v,
            m: [self.m[0] + r.m[0], self.m[1] + r.m[1]],
        }
    }
}

impl core::ops::Sub for Sh {
    type Output = Self;
    #[inline]
    fn sub(self, r: Self) -> Self {
        Self {
            v: self.v - r.v,
            m: [self.m[0] - r.m[0], self.m[1] - r.m[1]],
        }
    }
}

impl core::ops::AddAssign for Sh {
    #[inline]
    fn add_assign(&mut self, r: Self) {
        *self = *self + r;
    }
}

/// One party's one-use material: its shares of the two MAC keys, of Beaver triples
/// `(a, b, a b)` and of uniform values, all over the base field. Every party consumes
/// its store in the same order. Intentionally non-`Clone`; wiped on `Drop`.
pub struct Preprocessing {
    pub key: [F; 2],
    pub triples: Vec<[Sb; 3]>,
    pub randoms: Vec<Sb>,
}

impl Preprocessing {
    /// Bind both keys, both lengths and every value and MAC, in tape order.
    pub fn tape_id(&self) -> [u8; 32] {
        self.hash_tape(usize::MAX)
    }

    fn hash_tape(&self, limit: usize) -> [u8; 32] {
        use qsag_accel::keccak::{finalize_cshake256, init_cshake256};
        let mut hash = init_cshake256(b"", TAPE_ID_DOMAIN);
        for key in &self.key {
            hash.absorb(&key.to_le_bytes());
        }
        hash.absorb(&(self.triples.len() as u64).to_le_bytes());
        hash.absorb(&(self.randoms.len() as u64).to_le_bytes());
        for share in self.triples.iter().take(limit).flatten().chain(self.randoms.iter().take(limit)) {
            for word in [&share.v, &share.m[0], &share.m[1]] {
                hash.absorb(&word.to_le_bytes());
            }
        }
        finalize_cshake256(&mut hash, true);
        let mut id = [0; 32];
        hash.squeeze(&mut id);
        id
    }
}

impl Drop for Preprocessing {
    fn drop(&mut self) {
        qsag_asm::volatile_fill(&mut self.key, F::ZERO);
        self.triples.secret_wipe();
        self.randoms.secret_wipe();
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MpcError {
    Net(NetError),
    /// A message has the wrong length or a non-canonical field element.
    Malformed {
        from: usize,
    },
    OutOfTriples,
    OutOfRandoms,
    /// The batch MAC check failed: some opened value was wrong.
    MacCheck,
    /// Two parties hold different transcripts of the broadcast messages.
    Equivocation,
    /// A party's opened check value does not match its commitment.
    BadCommitment {
        from: usize,
    },
    /// A preprocessing tape / MAC key share was already burned by an earlier session.
    PreprocessingReused,
    /// The external monotone anti-rollback anchor refused the pre-round-1 burn.
    AntiRollback,
}

impl From<NetError> for MpcError {
    fn from(e: NetError) -> Self {
        Self::Net(e)
    }
}

/// What one party sent and consumed.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Stats {
    /// Payload bytes sent, summed over all peers.
    pub bytes_sent: u64,
    /// Broadcast rounds.
    pub rounds: u64,
    pub triples_used: u64,
    pub randoms_used: u64,
    pub mac_checks: u64,
}

const COIN_DOMAIN: &[u8] = b"QSAG.COLLAB.MAC.COINS/v2";
const COMMIT_DOMAIN: &[u8] = b"QSAG.COLLAB.MAC.COMMIT/v2";
const ECHO_DOMAIN: &[u8] = b"QSAG.COLLAB.ECHO/v2";
#[cfg(any(feature = "std", test))]
const LOCAL_DOMAIN: &[u8] = b"QSAG.COLLAB.LOCAL/v2";
const TAPE_ID_DOMAIN: &[u8] = b"QSAG.COLLAB.TAPE.ID/v1";
#[cfg(feature = "std")]
const TAPE_BURN_DOMAIN: &[u8] = b"QSAG.COLLAB.TAPE.BURN/v1";

#[cfg(feature = "std")]
fn burn_tape_in_process(tape_id: [u8; 32]) -> Result<(), MpcError> {
    use std::collections::BTreeSet;
    use std::sync::{Mutex, OnceLock};
    static BURNED: OnceLock<Mutex<BTreeSet<[u8; 32]>>> = OnceLock::new();
    let mut set = BURNED
        .get_or_init(|| Mutex::new(BTreeSet::new()))
        .lock()
        .map_err(|_| MpcError::AntiRollback)?;
    if !set.insert(tape_id) {
        return Err(MpcError::PreprocessingReused);
    }
    Ok(())
}

/// Check packet size in [`Engine::check`]: `2 * EXT_BYTES` (`sigma`) + `32` (`echo`) + `32` (`nonce`).
const CHECK_OPENING_BYTES: usize = 2 * EXT_BYTES + 32 + 32;

/// One custodian's side of the authenticated computation.
