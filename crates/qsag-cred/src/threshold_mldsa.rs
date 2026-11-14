//! Threshold ML-DSA-44 with standard FIPS 204 public keys and signatures.
//!
//! # Model (read this before deploying)
//!
//! `n <= 5` custodians, a privacy threshold `t >= 2`, and `n >= 2t - 1`.
//! At most `t - 1` custodians are statically and maliciously corrupt. Key
//! generation needs all `n`; **signing needs a quorum of at least `2t - 1`
//! custodians** (three for `t = 2`, five for `t = 3`), so that the corrupt
//! ones are a minority of the quorum. `t` custodians alone cannot sign: the
//! rejection test is a multiparty computation that is only sound with an
//! honest majority. Channels: authenticated confidential pairwise links and
//! authenticated consistent broadcast, through [`MpcTransport`]. Security is
//! with abort. See [`crate::rss_mpc`] for the sharing engine and its bounds.
//!
//! # Key generation
//!
//! No party or dealer ever holds `s1` or `s2`. Every coefficient is produced
//! exactly as FIPS 204 `RejBoundedPoly` produces it for `eta = 2`: a uniform
//! shared nibble is discarded when it equals 15 and otherwise mapped to
//! `2 - (b mod 5)`. The nibble's bits are exclusive-ors of one pseudorandom
//! bit per holder subset, so they are uniform and unknown to any `t - 1`
//! custodians; only the "equals 15" flag is opened. The secret is therefore
//! uniform on `[-2, 2]` per coefficient, held as replicated shares modulo
//! `q`. `t = A*s1 + s2` is computed on shares and opened, and the public key
//! is the standard encoding of `(rho, Power2Round(t).1)`. As in the FIPS 204
//! analysis, `t0` is treated as public. A corrupt custodian can abort after
//! seeing the public key; it cannot move a coefficient outside `[-2, 2]`.
//!
//! # Signing
//!
//! Per attempt, in four phases:
//!
//! 1. The mask `y` is sampled as 18 shared uniform bits per coefficient
//!    (`y = gamma1 - bits`, the `ExpandMask` range). Shared uniform masks
//!    `r < q` with known bits are prepared for the conversions below. The
//!    holders of every subset compare keyed digests of everything they hold:
//!    this fixes every share of `y` (the role of a round-one commitment)
//!    before anything about it is opened.
//! 2. `w = A*y` is computed on shares; `HighBits(w)` is computed by a shared
//!    circuit on `w + r` and only `w1` is opened. The challenge is
//!    `c = SampleInBall(H(mu || w1))`.
//! 3. `z = y + c*s1` and `w - c*s2` exist only as shares. One shared bit
//!    decides both `||z|| < gamma1 - beta` and
//!    `||LowBits(w - c*s2)|| < gamma2 - beta` with `HighBits(w - c*s2) = w1`
//!    (tested as `(w - c*s2 - w1*2*gamma2) mod+- q` lying in the open
//!    interval, which is equivalent). Every multiplication behind that bit
//!    is verified before it is opened; the number of failing coefficients is
//!    multiplied by a random extension-field element, so only "zero or not"
//!    is revealed.
//! 4. Only if the bit is "accept" do the holders open `z`. Each component of
//!    `z` is the one fixed in phase 1 plus `c` times the key component, and
//!    every subset has an honest holder who reports it, so a corrupt signer
//!    cannot substitute a different `y`. The hint is public given `z`, `c`
//!    and `t`. Too many hint bits rejects the attempt after `z` is public;
//!    that pair `(c, z)` already satisfies both secret-dependent checks and
//!    is distributed like part of an ordinary signature.
//!
//! What a rejected attempt reveals: `w1`, uniformly masked values, and the
//! reject bit. `w1` is a function of the fresh mask `y` alone. That the pair
//! (`w1`, reject) carries no usable information about the key is the usual
//! heuristic assumption for Fiat-Shamir-with-aborts protocols that publish
//! the commitment of a rejected attempt; it is not proved here.
//!
//! Nonce safety: every session derives its subset keys from fresh
//! contributions of all holders, bound to the session, the quorum and the
//! message representative, so two sessions never share `y` while one honest
//! holder has fresh entropy. The durable [`NonceBurnPersistence`] reservation
//! is kept as a second line of defence.

use crate::fips204_ntt::{
    MLDSA_D, MLDSA_N, MLDSA_Q, MlDsaLevel, MlDsaParams, Poly256, compute_fips204_mu, expand_a_ntt,
    fq_add, fq_sub, high_bits_ct, mat_vec_mul_ntt, ml_dsa_verify, pk_encode, power2round,
    sample_in_ball, sig_encode, use_hint, w1_encode,
};
use crate::rss_mpc::{
    EXT_DEGREE, Engine, MpcError, MpcStats, MpcTransport, Sh, Structure, less_than_public,
    masked_range_test,
};
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;
use qsag_accel::ct::ct_eq_bytes;
use qsag_accel::keccak::{Shake256, cshake256_framed_32};
use qsag_policy::AuthorizedSignReleaseToken;

/// Maximum custodians.
pub const MAX_THRESHOLD_MLDSA_PARTIES: usize = 5;
/// Attempts per signing session before `RejectionBudgetExhausted`.
pub const DEFAULT_MAX_REJECTION_ATTEMPTS: u32 = 256;

/// Round phase labels reported through [`crate::rss_mpc::RoundInfo::phase`].
pub const PHASE_SETUP: u8 = 0;
pub const PHASE_SIGN_MASKS: u8 = 1;
pub const PHASE_SIGN_HIGH_BITS: u8 = 2;
pub const PHASE_SIGN_REJECTION: u8 = 3;
pub const PHASE_SIGN_RELEASE: u8 = 4;
pub const PHASE_DKG_COIN: u8 = 10;
pub const PHASE_DKG_SAMPLE: u8 = 11;
pub const PHASE_DKG_PUBLIC_KEY: u8 = 12;

const MASK_BITS: usize = 23;
const SPARE_MASKS: usize = 32;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ThresholdMlDsaError {
    /// Only ML-DSA-44 is implemented by the threshold protocol.
    UnsupportedLevel,
    InvalidThresholdParameters {
        threshold: usize,
        num_parties: usize,
    },
    /// Every replicated subset must have an honest holder (`n >= 2t - 1`).
    InsufficientHonestHolderCoverage {
        threshold: usize,
        num_parties: usize,
    },
    DuplicateOrUnknownParty {
        party_id: u16,
    },
    /// Signing needs `2t - 1` custodians.
    QuorumTooSmall {
        have: usize,
        need: usize,
    },
    ContextTooLong,
    NoncePersistenceFailed,
    PolicyTokenDigestMismatch,
    /// Fewer accepted nibbles than coefficients; rerun key generation.
    KeySamplingShortfall,
    /// An opened value was outside the domain its verified circuit allows.
    ProtocolInvariantViolated,
    SignatureVerificationFailed,
    RejectionBudgetExhausted {
        attempts: u32,
    },
    Mpc(MpcError),
}

impl From<MpcError> for ThresholdMlDsaError {
    fn from(error: MpcError) -> Self {
        Self::Mpc(error)
    }
}

impl fmt::Display for ThresholdMlDsaError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}
impl core::error::Error for ThresholdMlDsaError {}

/// Durable reservation of a signing attempt. `reserve` must return `false`
/// if `(party_id, epoch)` or `(party_id, session_id, attempt)` was reserved
/// before for this key, across restarts. Epochs must advance monotonically.
pub trait NonceBurnPersistence {
    fn reserve(&mut self, party_id: u16, epoch: u64, session_id: &[u8; 32], attempt: u32) -> bool;

    /// Durable next unused epoch for this key and party. Unsupported recovery fails closed.
    fn next_epoch(&self, _key_id: &[u8; 32], _party_id: u16) -> Result<u64, ThresholdMlDsaError> {
        Err(ThresholdMlDsaError::NoncePersistenceFailed)
    }
}

/// Key-bound, exclusively locked, crash-atomic attempt ledger. Provision once
/// with `create`; after restart use `open` and recover the signer's epoch.
#[cfg(feature = "std")]
pub struct FsNonceBurnStore {
    record: qsag_asm::durable::LockedRecord,
    key_id: [u8; 32],
    burns: Vec<(u16, u64, [u8; 32], u32)>,
    poisoned: bool,
}

#[cfg(feature = "std")]
impl FsNonceBurnStore {
    pub fn create(path: impl Into<std::path::PathBuf>, key_id: [u8; 32]) -> std::io::Result<Self> {
        let store = Self {
            record: qsag_asm::durable::LockedRecord::create_new(path)?,
            key_id,
            burns: Vec::new(),
            poisoned: false,
        };
        store.record.replace(&store.encode())?;
        Ok(store)
    }

    pub fn open(path: impl Into<std::path::PathBuf>, key_id: [u8; 32]) -> std::io::Result<Self> {
        let record = qsag_asm::durable::LockedRecord::open_existing(path)?;
        let bytes = record.read()?;
        let invalid =
            || std::io::Error::new(std::io::ErrorKind::InvalidData, "invalid nonce ledger");
        if bytes.len() < 56
            || &bytes[..8] != b"QSCBURN1"
            || bytes[8..16] != record.lock_seal()
            || bytes[16..48] != key_id
        {
            return Err(invalid());
        }
        let count = u64::from_le_bytes(bytes[48..56].try_into().map_err(|_| invalid())?);
        if !((bytes.len() - 56).is_multiple_of(46)) || count != ((bytes.len() - 56) / 46) as u64 {
            return Err(invalid());
        }
        let mut store = Self {
            record,
            key_id,
            burns: Vec::new(),
            poisoned: false,
        };
        for row in bytes[56..].as_chunks::<46>().0 {
            let party = u16::from_le_bytes(row[..2].try_into().map_err(|_| invalid())?);
            let epoch = u64::from_le_bytes(row[2..10].try_into().map_err(|_| invalid())?);
            let session = row[10..42].try_into().map_err(|_| invalid())?;
            let attempt = u32::from_le_bytes(row[42..].try_into().map_err(|_| invalid())?);
            if !store.available(party, epoch, &session, attempt) {
                return Err(invalid());
            }
            store.burns.push((party, epoch, session, attempt));
        }
        Ok(store)
    }

    fn encode(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(56 + self.burns.len() * 46);
        bytes.extend_from_slice(b"QSCBURN1");
        bytes.extend_from_slice(&self.record.lock_seal());
        bytes.extend_from_slice(&self.key_id);
        bytes.extend_from_slice(&(self.burns.len() as u64).to_le_bytes());
        for (party, epoch, session, attempt) in &self.burns {
            bytes.extend_from_slice(&party.to_le_bytes());
            bytes.extend_from_slice(&epoch.to_le_bytes());
            bytes.extend_from_slice(session);
            bytes.extend_from_slice(&attempt.to_le_bytes());
        }
        bytes
    }

    fn available(&self, party: u16, epoch: u64, session: &[u8; 32], attempt: u32) -> bool {
        !self.poisoned
            && epoch != u64::MAX
            && !self.burns.iter().any(|(p, e, s, a)| {
                *p == party && (*e >= epoch || (*s == *session && *a == attempt))
            })
    }
}

#[cfg(feature = "std")]
impl NonceBurnPersistence for FsNonceBurnStore {
    fn reserve(&mut self, party_id: u16, epoch: u64, session_id: &[u8; 32], attempt: u32) -> bool {
        if !self.available(party_id, epoch, session_id, attempt) {
            return false;
        }
        self.burns.push((party_id, epoch, *session_id, attempt));
        if self.record.replace(&self.encode()).is_err() {
            self.poisoned = true;
            return false;
        }
        true
    }

    fn next_epoch(&self, key_id: &[u8; 32], party_id: u16) -> Result<u64, ThresholdMlDsaError> {
        if self.poisoned
            || *key_id != self.key_id
            || self
                .record
                .read()
                .map_or(true, |bytes| bytes != self.encode())
        {
            return Err(ThresholdMlDsaError::NoncePersistenceFailed);
        }
        Ok(self
            .burns
            .iter()
            .filter(|(p, _, _, _)| *p == party_id)
            .map(|(_, epoch, _, _)| epoch + 1)
            .max()
            .unwrap_or(0))
    }
}

/// Public parameters of a key-generation ceremony.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ThresholdMlDsaDkgConfig {
    pub level: MlDsaLevel,
    pub threshold: usize,
    /// Distinct custodian identifiers; order does not matter.
    pub party_ids: Vec<u16>,
    pub session_id: [u8; 32],
}

fn sorted_distinct(ids: &[u16]) -> Result<Vec<u16>, ThresholdMlDsaError> {
    let mut sorted = ids.to_vec();
    sorted.sort_unstable();
    if let Some(pair) = sorted.windows(2).find(|w| w[0] == w[1]) {
        return Err(ThresholdMlDsaError::DuplicateOrUnknownParty { party_id: pair[0] });
    }
    Ok(sorted)
}

fn ids_bytes(ids: &[u16]) -> Vec<u8> {
    ids.iter().flat_map(|id| id.to_le_bytes()).collect()
}

fn check_parameters(
    level: MlDsaLevel,
    threshold: usize,
    parties: usize,
) -> Result<(), ThresholdMlDsaError> {
    if level != MlDsaLevel::MlDsa44 {
        return Err(ThresholdMlDsaError::UnsupportedLevel);
    }
    if threshold < 2 || parties > MAX_THRESHOLD_MLDSA_PARTIES || threshold > parties {
        return Err(ThresholdMlDsaError::InvalidThresholdParameters {
            threshold,
            num_parties: parties,
        });
    }
    if parties < 2 * threshold - 1 {
        return Err(ThresholdMlDsaError::InsufficientHonestHolderCoverage {
            threshold,
            num_parties: parties,
        });
    }
    Ok(())
}

impl ThresholdMlDsaDkgConfig {
    /// Checks the configuration and returns the sorted custodian list.
    pub fn validate(&self) -> Result<Vec<u16>, ThresholdMlDsaError> {
        check_parameters(self.level, self.threshold, self.party_ids.len())?;
        sorted_distinct(&self.party_ids)
    }
}

/// Public result of key generation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ThresholdVerificationPack {
    pub level: MlDsaLevel,
    pub threshold: usize,
    /// Sorted custodian identifiers.
    pub party_ids: Vec<u16>,
    pub rho: [u8; 32],
    /// Standard FIPS 204 public key.
    pub pk_bytes: Vec<u8>,
    /// Public `t = A*s1 + s2` in coefficient form (`t0` is public here).
    pub t: Vec<Poly256>,
}

impl ThresholdVerificationPack {
    pub fn issuer_pk_digest(&self) -> [u8; 32] {
        cshake256_framed_32(b"QSAG.VC.ISSUER_PK.V1", &[&self.pk_bytes])
    }

    pub fn policy_signing_key_id(&self) -> [u8; 32] {
        cshake256_framed_32(b"QSAG.POLICY.KEY.V1", &[&self.pk_bytes])
    }

    /// Custodians required in a signing session.
    pub fn signing_quorum(&self) -> usize {
        2 * self.threshold - 1
    }
}

struct SubsetShare {
    /// Holders, as a bitmask over positions in the sorted custodian list.
    holders: u32,
    s1_hat: Vec<Poly256>,
    s2_hat: Vec<Poly256>,
}

impl Drop for SubsetShare {
    fn drop(&mut self) {
        for poly in self.s1_hat.iter_mut().chain(&mut self.s2_hat) {
            poly.zeroize();
        }
    }
}

/// One custodian's key material. Not cloneable; erased on drop.
pub struct ThresholdMlDsaSignerShare {
    party_id: u16,
    pack: ThresholdVerificationPack,
    subsets: Vec<SubsetShare>,
    next_epoch: u64,
}

impl fmt::Debug for ThresholdMlDsaSignerShare {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ThresholdMlDsaSignerShare")
            .field("party_id", &self.party_id)
            .field("secret", &"<REDACTED>")
            .finish()
    }
}

impl ThresholdMlDsaSignerShare {
    /// Recover without rolling back an epoch already advanced in this process.
    pub fn recover_epoch_from_store(
        &mut self,
        store: &dyn NonceBurnPersistence,
    ) -> Result<(), ThresholdMlDsaError> {
        self.next_epoch = self
            .next_epoch
            .max(store.next_epoch(&self.pack.policy_signing_key_id(), self.party_id)?);
        Ok(())
    }

    pub fn party_id(&self) -> u16 {
        self.party_id
    }

    pub fn verification_pack(&self) -> &ThresholdVerificationPack {
        &self.pack
    }

    fn custody_digest(&self) -> [u8; 32] {
        let mut xof = Shake256::new();
        xof.absorb(b"QSAG.TMLDSA.CUSTODY.V1");
        for subset in &self.subsets {
            for poly in subset.s1_hat.iter().chain(&subset.s2_hat) {
                for &c in &poly.coeffs {
                    xof.absorb(&c.to_le_bytes());
                }
            }
        }
        xof.finalize(0x1F);
        let mut out = [0u8; 32];
        xof.squeeze(&mut out);
        out
    }

    /// Test-only access to the additive components this custodian holds.
    #[cfg(test)]
    pub(crate) fn components_for_test(&self) -> Vec<(u32, Vec<Poly256>, Vec<Poly256>)> {
        self.subsets
            .iter()
            .map(|s| (s.holders, s.s1_hat.clone(), s.s2_hat.clone()))
            .collect()
    }
}

fn to_polys(flat: &[u32]) -> Vec<Poly256> {
    flat.as_chunks::<MLDSA_N>()
        .0
        .iter()
        .map(|chunk| Poly256 { coeffs: *chunk })
        .collect()
}

fn flatten(polys: &[Poly256]) -> Vec<u32> {
    polys
        .iter()
        .flat_map(|p| p.coeffs.iter().copied())
        .collect()
}

fn ntt_all(mut polys: Vec<Poly256>) -> Vec<Poly256> {
    for poly in &mut polys {
        poly.ntt();
    }
    polys
}

fn inv_ntt_all(mut polys: Vec<Poly256>) -> Vec<Poly256> {
    for poly in &mut polys {
        poly.inv_ntt();
    }
    polys
}

/// `c * v` for a challenge and a vector, both in NTT form; coefficient output.
fn challenge_times(c_hat: &Poly256, v_hat: &[Poly256]) -> Vec<u32> {
    flatten(&inv_ntt_all(
        v_hat.iter().map(|p| c_hat.pointwise_mul(p)).collect(),
    ))
}

fn require_bits(values: &[u32]) -> Result<(), ThresholdMlDsaError> {
    if values.iter().all(|&v| v <= 1) {
        Ok(())
    } else {
        Err(ThresholdMlDsaError::ProtocolInvariantViolated)
    }
}

/// Sum of `2^i * planes[i]`.
fn compose(planes: &[Sh]) -> Sh {
    let mut acc = planes[0].clone();
    for (i, plane) in planes.iter().enumerate().skip(1) {
        acc = acc.add(&plane.scale(1 << i));
    }
    acc
}

// ---------------------------------------------------------------------------
// Key generation
// ---------------------------------------------------------------------------

/// Runs one custodian's side of dealerless key generation.
///
/// `entropy` must be fresh secret randomness. All `n` custodians must run
/// this with the same `config` over a transport whose party positions follow
/// the ascending order of `config.party_ids`.
