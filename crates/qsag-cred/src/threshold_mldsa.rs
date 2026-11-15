//! Threshold FIPS 204 ML-DSA (`ML-DSA-44`, `ML-DSA-65`, and `ML-DSA-87`) with
//! standard FIPS 204 public keys and signatures and sealed-`w1` abort privacy.
//!
//! # Model (read this before deploying)
//!
//! A key has `n` custodians identified by distinct `u16` IDs, a privacy threshold
//! `t >= 2`, and `n >= 2t - 1`.
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
//! with the exact FIPS 204 `RejBoundedPoly` distribution: for `eta = 2`
//! (`ML-DSA-44` and `ML-DSA-87`), a uniform shared nibble is discarded when it
//! equals 15 and otherwise mapped to `2 - (b mod 5)`; for `eta = 4`
//! (`ML-DSA-65`), a uniform shared nibble is discarded when `b >= 9` and
//! otherwise mapped to `4 - b`. The nibble's bits are exclusive-ors of one
//! pseudorandom bit per holder subset, so they are uniform and unknown to any
//! `t - 1` custodians; only the rejection flag is opened. The secret is
//! therefore uniform on `[-eta, eta]` per coefficient, held as replicated
//! shares modulo `q`. `t = A*s1 + s2` is computed on shares and opened, and the
//! public key is the standard encoding of `(rho, Power2Round(t).1)`. As in the
//! FIPS 204 analysis, `t0` is treated as public. A corrupt custodian can abort
//! after seeing the public key; it cannot move a coefficient outside `[-eta, eta]`.
//!
//! # Signing (Sealed-`w1` Abort-Transcript Zero Knowledge)
//!
//! Naive threshold Fiat-Shamir-with-aborts schemes that open `w1 = HighBits(A*y)`
//! before checking norms leak `(w1, reject)` joint correlations on aborted
//! attempts (particularly when `A` is square, as in `ML-DSA-44`, where `w = A*y`
//! carries zero LWE noise and boundary `w1` bins correlate `y` with `gamma1 - beta`).
//! Here `w1` and `c` remain **100% secret-shared** until every FIPS 204
//! acceptance predicate succeeds:
//!
//! 1. The mask `y` is sampled as `18` (`ML-DSA-44`) or `20` (`ML-DSA-65`/`87`)
//!    shared uniform bits per coefficient (`y = gamma1 - bits`, the exact
//!    `ExpandMask` plateau). Independent uniform masks `r < q` with known bits
//!    are prepared for every masked opening.
//! 2. `w = A*y` is computed on shares; `(w1, w1_bits) = HighBits(w)` is
//!    evaluated by a verified shared circuit on `w + gamma2 - 1 + r` (`gamma2 =
//!    (q - 1) / 88` or `(q - 1) / 32`), and **kept secret-shared**.
//! 3. `w1_bits` are lifted via authenticated `daBits` into binary RSS (`GF(2)^64`
//!    verified in `GF(2^128)`), packed into `w1Encode(w1)`, absorbed with `mu`
//!    into shared `SHAKE256` (`Keccak-f[1600]`), and expanded by a shared
//!    `SampleInBall` circuit into shares of `c`. Next `z = y + c*s1`,
//!    `w - c*s2`, and `c*t0` are evaluated on shares, and one blinded
//!    extension-field check decides all five conditions jointly: `SampleInBall`
//!    completion, `||z||_inf < gamma1 - beta`, `||LowBits(w - c*s2)||_inf <
//!    gamma2 - beta`, `HighBits(w - c*s2) == w1`, `||c*t0||_inf < gamma2`, and
//!    `weight(MakeHint(-c*t0, w - c*s2 + c*t0)) <= omega`.
//! 4. Rejected attempts open **only** one-time-pad masked field/binary shares
//!    and the single blinded abort verdict — **never `w1`, `c`, `z`, or `h`**.
//!    Only after acceptance do the custodians open `(w1, z)` in Phase 4 and
//!    assemble the standard FIPS 204 signature `(c_tilde, z, h)`.
//!
//! Nonce safety: every session derives its subset keys from fresh
//! contributions of all holders, bound to the session, the quorum and the
//! message representative, so two sessions never share `y` while one honest
//! holder has fresh entropy. The durable [`NonceBurnPersistence`] reservation
//! is kept as a second line of defence.

use crate::fips204_ntt::{
    MLDSA_D, MLDSA_N, MLDSA_Q, MlDsaLevel, MlDsaParams, Poly256, compute_fips204_mu, expand_a_ntt,
    fq_add, fq_mul, fq_sub, high_bits_ct, mat_vec_mul_ntt, ml_dsa_verify, pk_encode, power2round,
    sample_in_ball, sig_encode, use_hint, w1_encode,
};
use crate::rss_mpc::{
    BinSh, EXT_DEGREE, Engine, MpcError, MpcStats, MpcTransport, Sh, Structure, less_than_public,
    masked_range_test,
};
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;
use qsag_accel::ct::{ct_eq_bytes, ct_zeroize_bytes};
use qsag_accel::keccak::{KECCAK_RC, Shake256, cshake256_framed_32};
use qsag_policy::AuthorizedSignReleaseToken;
use qsag_verified::{MlDsaBarrierChecks, MlDsaReleaseGate};

/// Enrollment identifier limit. The current RSS backend additionally enforces
/// `rss_mpc::MAX_MPC_PARTIES`; a polynomial-sharing backend is needed above it.
pub const MAX_THRESHOLD_MLDSA_PARTIES: usize = 64;
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
const SPARE_MASKS: usize = 64;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ThresholdMlDsaError {
    /// Parameter set is not one of the supported FIPS 204 ML-DSA levels (`44`, `65`, `87`).
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

/// Key-bound, MAC-authenticated, exclusively locked, crash-atomic attempt ledger.
/// Provision once with [`Self::create`]; after restart use [`Self::open`] or
/// [`Self::open_at_least`] (supplying an externally retained monotonic generation floor)
/// and recover the signer's epoch.
#[cfg(feature = "std")]
pub struct FsNonceBurnStore {
    path: std::path::PathBuf,
    lock_id: [u8; 16],
    record: qsag_asm::durable::LockedRecord,
    key_id: [u8; 32],
    mac_key: qsag_accel::ct::RedactedSecret<32>,
    generation: u64,
    burns: Vec<(u16, u64, [u8; 32], u32)>,
    poisoned: bool,
}

#[cfg(feature = "std")]
fn mldsa_burn_lock_inode(path: &std::path::Path) -> std::io::Result<[u8; 16]> {
    let mut os = path.as_os_str().to_os_string();
    os.push(".lock");
    let meta = std::fs::symlink_metadata(std::path::PathBuf::from(os))?;
    if !meta.is_file() || meta.file_type().is_symlink() {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            "invalid nonce ledger lock sidecar",
        ));
    }
    let mut id = [0u8; 16];
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        id[..8].copy_from_slice(&meta.dev().to_le_bytes());
        id[8..].copy_from_slice(&meta.ino().to_le_bytes());
    }
    Ok(id)
}

#[cfg(feature = "std")]
impl FsNonceBurnStore {
    pub fn create(
        path: impl Into<std::path::PathBuf>,
        key_id: [u8; 32],
        mut storage_mac_key: [u8; 32],
    ) -> std::io::Result<Self> {
        let path = path.into();
        let record = qsag_asm::durable::LockedRecord::create_new(&path)?;
        let lock_id = mldsa_burn_lock_inode(&path)?;
        let mac_key = qsag_accel::ct::RedactedSecret::new(storage_mac_key);
        qsag_accel::ct::ct_zeroize_bytes(&mut storage_mac_key);
        let store = Self {
            path,
            lock_id,
            record,
            key_id,
            mac_key,
            generation: 0,
            burns: Vec::new(),
            poisoned: false,
        };
        store.record.replace(&store.encode())?;
        Ok(store)
    }

    pub fn open(
        path: impl Into<std::path::PathBuf>,
        key_id: [u8; 32],
        storage_mac_key: [u8; 32],
    ) -> std::io::Result<Self> {
        Self::open_at_least(path, key_id, storage_mac_key, 0)
    }

    pub fn open_at_least(
        path: impl Into<std::path::PathBuf>,
        key_id: [u8; 32],
        mut storage_mac_key: [u8; 32],
        min_expected_generation: u64,
    ) -> std::io::Result<Self> {
        let path = path.into();
        let record = qsag_asm::durable::LockedRecord::open_existing(&path)?;
        let lock_id = mldsa_burn_lock_inode(&path)?;
        let mac_key = qsag_accel::ct::RedactedSecret::new(storage_mac_key);
        qsag_accel::ct::ct_zeroize_bytes(&mut storage_mac_key);
        let bytes = record.read()?;
        let invalid =
            || std::io::Error::new(std::io::ErrorKind::InvalidData, "invalid nonce ledger");
        if bytes.len() < 96 {
            return Err(invalid());
        }
        let (body, tag) = bytes.split_at(bytes.len() - 32);
        let expected_tag = cshake256_framed_32(
            b"QSAG.MLDSA.NONCE_BURN.V2",
            &[mac_key.expose(), &lock_id, body],
        );
        if !qsag_accel::ct::ct_eq_bytes(&expected_tag, tag) {
            return Err(invalid());
        }
        if &body[..8] != b"QSCBURN2"
            || body[8..16] != record.lock_seal()
            || !qsag_accel::ct::ct_eq_bytes(&body[16..48], &key_id)
        {
            return Err(invalid());
        }
        let generation = u64::from_le_bytes(body[48..56].try_into().map_err(|_| invalid())?);
        let count = u64::from_le_bytes(body[56..64].try_into().map_err(|_| invalid())?);
        if generation < min_expected_generation
            || !(body.len() - 64).is_multiple_of(46)
            || count != ((body.len() - 64) / 46) as u64
            || generation < count
        {
            return Err(invalid());
        }
        let mut store = Self {
            path,
            lock_id,
            record,
            key_id,
            mac_key,
            generation,
            burns: Vec::new(),
            poisoned: false,
        };
        for row in body[64..].as_chunks::<46>().0 {
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

    pub const fn generation(&self) -> u64 {
        self.generation
    }

    fn encode(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(96 + self.burns.len() * 46);
        bytes.extend_from_slice(b"QSCBURN2");
        bytes.extend_from_slice(&self.record.lock_seal());
        bytes.extend_from_slice(&self.key_id);
        bytes.extend_from_slice(&self.generation.to_le_bytes());
        bytes.extend_from_slice(&(self.burns.len() as u64).to_le_bytes());
        for (party, epoch, session, attempt) in &self.burns {
            bytes.extend_from_slice(&party.to_le_bytes());
            bytes.extend_from_slice(&epoch.to_le_bytes());
            bytes.extend_from_slice(session);
            bytes.extend_from_slice(&attempt.to_le_bytes());
        }
        let tag = cshake256_framed_32(
            b"QSAG.MLDSA.NONCE_BURN.V2",
            &[self.mac_key.expose(), &self.lock_id, &bytes],
        );
        bytes.extend_from_slice(&tag);
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
        if mldsa_burn_lock_inode(&self.path).ok() != Some(self.lock_id) {
            self.poisoned = true;
            return false;
        }
        let Some(next_gen) = self.generation.checked_add(1) else {
            self.poisoned = true;
            return false;
        };
        self.generation = next_gen;
        self.burns.push((party_id, epoch, *session_id, attempt));
        if self.record.replace(&self.encode()).is_err() {
            self.poisoned = true;
            return false;
        }
        true
    }

    fn next_epoch(&self, key_id: &[u8; 32], party_id: u16) -> Result<u64, ThresholdMlDsaError> {
        let expected = self.encode();
        if self.poisoned
            || !qsag_accel::ct::ct_eq_bytes(key_id, &self.key_id)
            || mldsa_burn_lock_inode(&self.path).ok() != Some(self.lock_id)
            || self.record.read().map_or(true, |bytes| {
                !qsag_accel::ct::ct_eq_bytes(&bytes, &expected)
            })
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
    if !matches!(
        level,
        MlDsaLevel::MlDsa44 | MlDsaLevel::MlDsa65 | MlDsaLevel::MlDsa87
    ) {
        return Err(ThresholdMlDsaError::UnsupportedLevel);
    }
    if threshold < 2 || parties > MAX_THRESHOLD_MLDSA_PARTIES || threshold > parties {
        return Err(ThresholdMlDsaError::InvalidThresholdParameters {
            threshold,
            num_parties: parties,
        });
    }
    if threshold > parties.div_ceil(2) {
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
    /// Sorted holder positions in the global custodian list.
    holders: Vec<usize>,
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
    pub(crate) fn components_for_test(&self) -> Vec<(Vec<usize>, Vec<Poly256>, Vec<Poly256>)> {
        self.subsets
            .iter()
            .map(|s| (s.holders.clone(), s.s1_hat.clone(), s.s2_hat.clone()))
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
pub fn threshold_mldsa_dkg_party<T: MpcTransport>(
    config: &ThresholdMlDsaDkgConfig,
    party_id: u16,
    entropy: &[u8; 32],
    net: &mut T,
) -> Result<ThresholdMlDsaSignerShare, ThresholdMlDsaError> {
    let ids = config.validate()?;
    let me = ids
        .iter()
        .position(|&id| id == party_id)
        .ok_or(ThresholdMlDsaError::DuplicateOrUnknownParty { party_id })?;
    let params = config.level.params();
    let structure = Structure::new(ids.len(), config.threshold)?;
    let context = cshake256_framed_32(
        b"QSAG.TMLDSA.DKG.CTX.V1",
        &[
            &config.session_id,
            &ids_bytes(&ids),
            &[config.threshold as u8, params.k as u8, params.ell as u8],
        ],
    );
    let mut engine = Engine::setup(net, structure.clone(), me, &context, entropy)?;

    engine.set_phase(PHASE_DKG_COIN);
    let coin = engine.rand(16)?;
    let coin = engine.open(&[&coin])?;
    let rho = cshake256_framed_32(
        b"QSAG.TMLDSA.DKG.RHO.V1",
        &[
            &context,
            &coin[0]
                .iter()
                .flat_map(|v| v.to_le_bytes())
                .collect::<Vec<u8>>(),
        ],
    );

    engine.set_phase(PHASE_DKG_SAMPLE);
    let need = (params.ell + params.k) * MLDSA_N;
    let secret = if params.eta == 2 {
        let candidates = need + need / 8 + 96;
        let bits = engine.rand_bits(4 * candidates)?;
        let b: Vec<Sh> = (0..4)
            .map(|i| bits.slice(i * candidates, candidates))
            .collect();
        let first = engine.mul(
            &Sh::concat(&[&b[0], &b[1], &b[2]]),
            &Sh::concat(&[&b[1], &b[2], &b[3]]),
        )?;
        let p01 = first.slice(0, candidates);
        let p12 = first.slice(candidates, candidates);
        let p23 = first.slice(2 * candidates, candidates);
        let or12 = b[1].add(&b[2]).sub(&p12);
        let or01 = b[0].add(&b[1]).sub(&p01);
        let second = engine.mul(
            &Sh::concat(&[&b[3], &b[2], &p01]),
            &Sh::concat(&[&or12, &or01, &p23]),
        )?;
        let at_least_10 = second.slice(0, candidates);
        let low_part = second.slice(candidates, candidates);
        let is_15 = second.slice(2 * candidates, candidates);
        let at_least_5 = b[3].add(&low_part).sub(&engine.mul(&b[3], &low_part)?);
        // coefficient = 2 - (nibble mod 5)
        let coefficient = engine
            .public_const(2, candidates)?
            .sub(&compose(&b))
            .add(&at_least_5.add(&at_least_10).scale(5));
        let flags = engine.open(&[&is_15])?;
        require_bits(&flags[0])?;
        let accepted: Vec<usize> = (0..candidates)
            .filter(|&i| flags[0][i] == 0)
            .take(need)
            .collect();
        if accepted.len() < need {
            return Err(ThresholdMlDsaError::KeySamplingShortfall);
        }
        coefficient.gather(&accepted)
    } else if params.eta == 4 {
        // FIPS 204 RejBoundedPoly for eta = 4 (ML-DSA-65): accept nibble b < 9, map to 4 - b.
        // Reject flag: b >= 9 iff b[3] == 1 and (b[0] | b[1] | b[2]) == 1.
        let candidates = (need * 16).div_ceil(9) + 960;
        let bits = engine.rand_bits(4 * candidates)?;
        let b: Vec<Sh> = (0..4)
            .map(|i| bits.slice(i * candidates, candidates))
            .collect();
        let p01 = engine.mul(&b[0], &b[1])?;
        let or01 = b[0].add(&b[1]).sub(&p01);
        let p012 = engine.mul(&or01, &b[2])?;
        let or012 = or01.add(&b[2]).sub(&p012);
        let at_least_9 = engine.mul(&b[3], &or012)?;
        let coefficient = engine.public_const(4, candidates)?.sub(&compose(&b));
        let flags = engine.open(&[&at_least_9])?;
        require_bits(&flags[0])?;
        let accepted: Vec<usize> = (0..candidates)
            .filter(|&i| flags[0][i] == 0)
            .take(need)
            .collect();
        if accepted.len() < need {
            return Err(ThresholdMlDsaError::KeySamplingShortfall);
        }
        coefficient.gather(&accepted)
    } else {
        return Err(ThresholdMlDsaError::UnsupportedLevel);
    };

    let a_hat = expand_a_ntt(&params, &rho);
    let split = params.ell * MLDSA_N;
    let mut t_share = engine.zeros(params.k * MLDSA_N)?;
    let mut subsets = Vec::with_capacity(engine.comps().len());
    for (i, &subset) in engine.comps().iter().enumerate() {
        let s1_hat = ntt_all(to_polys(&secret.c[i][..split]));
        let s2 = to_polys(&secret.c[i][split..]);
        let product = inv_ntt_all(mat_vec_mul_ntt(&a_hat, &s1_hat));
        let t: Vec<Poly256> = product.iter().zip(&s2).map(|(p, e)| p.add(e)).collect();
        t_share.c[i] = flatten(&t);
        subsets.push(SubsetShare {
            holders: structure.subsets[subset].clone(),
            s1_hat,
            s2_hat: ntt_all(s2),
        });
    }

    engine.set_phase(PHASE_DKG_PUBLIC_KEY);
    let t = to_polys(&engine.open(&[&t_share])?[0]);
    let t1: Vec<Poly256> = t
        .iter()
        .map(|poly| {
            let mut high = Poly256::zero();
            for (out, &value) in high.coeffs.iter_mut().zip(&poly.coeffs) {
                *out = power2round(value).0;
            }
            high
        })
        .collect();
    let pk_bytes = pk_encode(&params, &rho, &t1);
    let confirmation = cshake256_framed_32(
        b"QSAG.TMLDSA.DKG.CONFIRM.V1",
        &[
            &context,
            &pk_bytes,
            &flatten(&t)
                .iter()
                .flat_map(|v| v.to_le_bytes())
                .collect::<Vec<u8>>(),
        ],
    );
    engine.confirm(&confirmation)?;

    Ok(ThresholdMlDsaSignerShare {
        party_id,
        pack: ThresholdVerificationPack {
            level: config.level,
            threshold: config.threshold,
            party_ids: ids,
            rho,
            pk_bytes,
            t,
        },
        subsets,
        next_epoch: 0,
    })
}

// ---------------------------------------------------------------------------
// Signing
// ---------------------------------------------------------------------------

/// Public parameters of one signing session.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ThresholdSignSession {
    pub session_id: [u8; 32],
    /// At least `2t - 1` distinct custodians. Transport positions follow the
    /// ascending order of this list.
    pub quorum: Vec<u16>,
}

/// A standard signature and the cost of producing it, for one party.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ThresholdSignOutput {
    pub signature: Vec<u8>,
    pub attempts: u32,
    pub stats: MpcStats,
}

/// `HighBits` of the hidden value `opened - r mod q`, where the hidden value
/// is `w + gamma2 - 1 mod q` and `r < q` is given by its 23 shared bits.
///
/// Supports both FIPS 204 decomposition granularities:
/// - `gamma2 = (q - 1) / 88 = 95_232` (`ML-DSA-44`, `alpha = 2^11 * 93`, `m = 44`),
///   returning `(value, 6 LSB-first bit planes)` with `44 -> 0` wrapped.
/// - `gamma2 = (q - 1) / 32 = 261_888` (`ML-DSA-65` and `ML-DSA-87`,
///   `alpha = 2^9 * 1023`, `m = 16`), returning `(value, 4 LSB-first bit planes)`
///   with `16 -> 0` wrapped modulo `16`.
fn high_bits_circuit_with_bits<T: MpcTransport>(
    engine: &mut Engine<'_, T>,
    opened: &[u32],
    r: &[Sh],
    gamma2: u32,
) -> Result<(Sh, Vec<Sh>), MpcError> {
    let len = opened.len();
    let one = engine.public_const(1, len)?;

    // d = opened - r as a 23-bit two's complement number, with final borrow.
    let mut d: Vec<Sh> = Vec::with_capacity(MASK_BITS);
    let mut borrow: Option<Sh> = None;
    for (i, r_bit) in r.iter().enumerate() {
        let c_bit: Vec<u32> = opened.iter().map(|&c| (c >> i) & 1).collect();
        let not_c: Vec<u32> = c_bit.iter().map(|&bit| 1 - bit).collect();
        let (next, diff) = match &borrow {
            None => {
                let next = r_bit.mul_pub(&not_c);
                let diff = engine.public(&c_bit)?.sub(r_bit).add(&next.scale(2));
                (next, diff)
            }
            Some(b) => {
                let both = engine.mul(r_bit, b)?;
                let next = both
                    .mul_pub(&c_bit)
                    .add(&r_bit.add(b).sub(&both).mul_pub(&not_c));
                let diff = engine.public(&c_bit)?.sub(r_bit).sub(b).add(&next.scale(2));
                (next, diff)
            }
        };
        d.push(diff);
        borrow = Some(next);
    }
    let wrap = borrow.expect("23 bits");

    // x = d + q * wrap modulo 2^23, with q = 2^23 - 2^13 + 1. Bit 0 and the
    // zero bits 1..13 of q ripple a carry; the ten one-bits act as a decrement
    // by wrap - carry.
    let mut carries = Vec::with_capacity(13);
    carries.push(engine.mul(&d[0], &wrap)?);
    for i in 1..13 {
        let next = engine.mul(&d[i], &carries[i - 1])?;
        carries.push(next);
    }

    if gamma2 == (MLDSA_Q - 1) / 88 {
        let mut u: Vec<Sh> = Vec::with_capacity(12);
        u.push(d[11].add(&carries[10]).sub(&carries[11].scale(2)));
        u.push(d[12].add(&carries[11]).sub(&carries[12].scale(2)));
        let mut decrement = wrap.sub(&carries[12]);
        for bit in &d[13..MASK_BITS] {
            let next = engine.mul(&one.sub(bit), &decrement)?;
            u.push(bit.sub(&decrement).add(&next.scale(2)));
            decrement = next;
        }

        // Restoring division of the 12-bit number u by 93. The quotient is below
        // 64, so the top six bits enter the remainder without a subtraction.
        const DIVISOR_93: [u32; 8] = [1, 0, 1, 1, 1, 0, 1, 0];
        let mut remainder: Vec<Sh> = u[6..12].to_vec();
        remainder.push(engine.zeros(len)?);
        let mut quotient: Vec<Sh> = Vec::with_capacity(6);
        for i in (0..6).rev() {
            let mut a: Vec<Sh> = Vec::with_capacity(8);
            a.push(u[i].clone());
            a.append(&mut remainder);
            let mut borrow: Option<Sh> = None;
            let mut difference: Vec<Sh> = Vec::with_capacity(8);
            for (a_bit, &k_bit) in a.iter().zip(&DIVISOR_93) {
                let next = match (&borrow, k_bit) {
                    (None, 0) => None,
                    (None, _) => Some(one.sub(a_bit)),
                    (Some(b), 0) => Some(b.sub(&engine.mul(a_bit, b)?)),
                    (Some(b), _) => Some(one.sub(a_bit).add(&engine.mul(a_bit, b)?)),
                };
                let mut bit = a_bit.sub(&engine.public_const(k_bit, len)?);
                if let Some(b) = &borrow {
                    bit = bit.sub(b);
                }
                if let Some(n) = &next {
                    bit = bit.add(&n.scale(2));
                }
                difference.push(bit);
                borrow = next;
            }
            let at_least = one.sub(&borrow.expect("divisor has a one bit"));
            let deltas: Vec<Sh> = difference
                .iter()
                .zip(&a)
                .take(7)
                .map(|(s, a_bit)| s.sub(a_bit))
                .collect();
            let delta_refs: Vec<&Sh> = deltas.iter().collect();
            let selected = engine.mul(&Sh::concat(&delta_refs), &at_least.repeat(7))?;
            remainder = (0..7)
                .map(|j| a[j].add(&selected.slice(j * len, len)))
                .collect();
            quotient.push(at_least);
        }
        // quotient[0] is bit 5. 44 = 0b101100 is the only reachable value with
        // bits 5, 3 and 2 set.
        let top = engine.mul(&quotient[0], &quotient[2])?;
        let is_44 = engine.mul(&top, &quotient[3])?;
        let bits = vec![
            quotient[5].clone(),
            quotient[4].clone(),
            quotient[3].sub(&is_44),
            quotient[2].sub(&is_44),
            quotient[1].clone(),
            quotient[0].sub(&is_44),
        ];
        let mut value = is_44.scale(MLDSA_Q - 44);
        for (index, bit) in quotient.iter().enumerate() {
            value = value.add(&bit.scale(1 << (5 - index)));
        }
        Ok((value, bits))
    } else {
        debug_assert_eq!(gamma2, (MLDSA_Q - 1) / 32);
        // alpha = 2 * 261_888 = 523_776 = 2^9 * 1023. Extract 14 bits x[9..23].
        let mut u: Vec<Sh> = Vec::with_capacity(14);
        for j in 9..13 {
            u.push(d[j].add(&carries[j - 1]).sub(&carries[j].scale(2)));
        }
        let mut decrement = wrap.sub(&carries[12]);
        for bit in &d[13..MASK_BITS] {
            let next = engine.mul(&one.sub(bit), &decrement)?;
            u.push(bit.sub(&decrement).add(&next.scale(2)));
            decrement = next;
        }

        // Restoring division of 14-bit u <= 16_368 = 16 * 1023 by 10-bit 1023.
        // Quotient is in 0..=16; wrapping 16 -> 0 keeps the low 4 quotient bits.
        const DIVISOR_1023: [u32; 11] = [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0];
        let mut remainder: Vec<Sh> = u[5..14].to_vec();
        remainder.push(engine.zeros(len)?);
        let mut quotient: Vec<Sh> = Vec::with_capacity(5);
        for i in (0..5).rev() {
            let mut a: Vec<Sh> = Vec::with_capacity(11);
            a.push(u[i].clone());
            a.append(&mut remainder);
            let mut borrow: Option<Sh> = None;
            let mut difference: Vec<Sh> = Vec::with_capacity(11);
            for (a_bit, &k_bit) in a.iter().zip(&DIVISOR_1023) {
                let next = match (&borrow, k_bit) {
                    (None, 0) => None,
                    (None, _) => Some(one.sub(a_bit)),
                    (Some(b), 0) => Some(b.sub(&engine.mul(a_bit, b)?)),
                    (Some(b), _) => Some(one.sub(a_bit).add(&engine.mul(a_bit, b)?)),
                };
                let mut bit = a_bit.sub(&engine.public_const(k_bit, len)?);
                if let Some(b) = &borrow {
                    bit = bit.sub(b);
                }
                if let Some(n) = &next {
                    bit = bit.add(&n.scale(2));
                }
                difference.push(bit);
                borrow = next;
            }
            let at_least = one.sub(&borrow.expect("divisor has a one bit"));
            let deltas: Vec<Sh> = difference
                .iter()
                .zip(&a)
                .take(10)
                .map(|(s, a_bit)| s.sub(a_bit))
                .collect();
            let delta_refs: Vec<&Sh> = deltas.iter().collect();
            let selected = engine.mul(&Sh::concat(&delta_refs), &at_least.repeat(10))?;
            remainder = (0..10)
                .map(|j| a[j].add(&selected.slice(j * len, len)))
                .collect();
            quotient.push(at_least);
        }
        let bits = vec![
            quotient[4].clone(),
            quotient[3].clone(),
            quotient[2].clone(),
            quotient[1].clone(),
        ];
        let value = compose(&bits);
        Ok((value, bits))
    }
}

#[cfg(test)]
fn high_bits_circuit<T: MpcTransport>(
    engine: &mut Engine<'_, T>,
    opened: &[u32],
    r: &[Sh],
) -> Result<Sh, MpcError> {
    Ok(high_bits_circuit_with_bits(engine, opened, r, (MLDSA_Q - 1) / 88)?.0)
}

/// 24-round `Keccak-f[1600]` over 25 XOR-shared 64-bit lanes (1 batched `bit_and` per round).
fn mpc_keccak_f1600<T: MpcTransport>(
    engine: &mut Engine<'_, T>,
    state: &mut [BinSh; 25],
) -> Result<(), MpcError> {
    const KECCAK_RHO: [u32; 24] = [
        1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14, 27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44,
    ];
    const KECCAK_PI: [usize; 24] = [
        10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4, 15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1,
    ];

    for &rc in &KECCAK_RC {
        // Theta
        let bc: [BinSh; 5] = core::array::from_fn(|i| {
            state[i]
                .xor(&state[i + 5])
                .xor(&state[i + 10])
                .xor(&state[i + 15])
                .xor(&state[i + 20])
        });
        for i in 0..5 {
            let t = bc[(i + 4) % 5].xor(&bc[(i + 1) % 5].rotl(1));
            state[i] = state[i].xor(&t);
            state[i + 5] = state[i + 5].xor(&t);
            state[i + 10] = state[i + 10].xor(&t);
            state[i + 15] = state[i + 15].xor(&t);
            state[i + 20] = state[i + 20].xor(&t);
        }

        // Rho + Pi
        let mut t = state[1].clone();
        for (&j, &rotation) in KECCAK_PI.iter().zip(&KECCAK_RHO) {
            let next = state[j].clone();
            state[j] = t.rotl(rotation);
            t = next;
        }

        // Chi (batched across all 25 lanes in 1 round)
        let state_refs: [&BinSh; 25] = core::array::from_fn(|idx| &state[idx]);
        let inv_all = engine.not_bin(&BinSh::concat(&state_refs))?;
        let not_state: [BinSh; 25] = core::array::from_fn(|idx| inv_all.slice(idx, 1));
        let mut lhs_refs: Vec<&BinSh> = Vec::with_capacity(25);
        let mut rhs_refs: Vec<&BinSh> = Vec::with_capacity(25);
        for row in (0..25).step_by(5) {
            for i in 0..5 {
                lhs_refs.push(&not_state[row + (i + 1) % 5]);
                rhs_refs.push(&state[row + (i + 2) % 5]);
            }
        }
        let chi_and = engine.bit_and(&BinSh::concat(&lhs_refs), &BinSh::concat(&rhs_refs))?;
        for (idx, lane) in state.iter_mut().enumerate() {
            *lane = lane.xor(&chi_and.slice(idx, 1));
        }

        // Iota
        state[0] = state[0].xor(&engine.public_bin(&[rc])?);
    }
    Ok(())
}

fn place_bit0_256(bit0: &BinSh, idx: usize) -> BinSh {
    let comps = bit0.c.len();
    let mut out = BinSh::zeros(comps, 4);
    let word = idx / 64;
    let shift = idx % 64;
    for i in 0..comps {
        out.c[i][word] = (bit0.c[i][0] & 1) << shift;
    }
    out
}

/// Derives the secret-shared challenge polynomial `c in {-1, 0, 1}^256 subset R_q`
/// and `SampleInBall` shortfall indicator bit directly from `mu` and the secret-shared
/// `w1` bit-planes, keeping `w1`, `c_tilde`, and `c` 100% sealed inside RSS.
fn mpc_derive_challenge<T: MpcTransport>(
    engine: &mut Engine<'_, T>,
    params: &MlDsaParams,
    mu: &[u8; 64],
    w1_bit_planes: &[Sh],
) -> Result<(Sh, Sh), ThresholdMlDsaError> {
    const CAND_BYTES: usize = 232;
    let comps = engine.comps().len();
    let b_width = w1_bit_planes.len();
    let w_len = w1_bit_planes[0].len();
    let total_w1_bits = b_width * w_len;
    let w1_words = total_w1_bits / 64;

    // 1. Lift w1Encode bitstream from F_q to binary RSS via authenticated daBits + F_q XOR.
    let mut flat_w1_bits = engine.zeros(total_w1_bits)?;
    for i in 0..comps {
        for m in 0..w_len {
            for (d, plane) in w1_bit_planes.iter().enumerate().take(b_width) {
                flat_w1_bits.c[i][m * b_width + d] = plane.c[i][m];
            }
        }
    }
    let (r_fq, r_bin) = engine.rand_dabits(total_w1_bits)?;
    let prod_mask = engine.mul(&flat_w1_bits, &r_fq)?;
    let masked_w1_fq = flat_w1_bits.add(&r_fq).sub(&prod_mask.scale(2));
    let opened_w1_bits = engine.open(&[&masked_w1_fq])?.remove(0);
    require_bits(&opened_w1_bits)?;
    let mut pub_w1_words = vec![0u64; w1_words];
    for (pos, &bit) in opened_w1_bits.iter().enumerate() {
        pub_w1_words[pos / 64] |= (bit as u64) << (pos % 64);
    }
    let w1_bin = r_bin.xor(&engine.public_bin(&pub_w1_words)?);

    // 2. Sponge 1: c_tilde = SHAKE256(mu || w1Encode(w1), c_tilde_bytes).
    let mut mu_lanes: Vec<BinSh> = Vec::with_capacity(8);
    for chunk in mu.chunks_exact(8) {
        let mut bytes = [0u8; 8];
        bytes.copy_from_slice(chunk);
        mu_lanes.push(engine.public_bin(&[u64::from_le_bytes(bytes)])?);
    }
    let w1_lanes: Vec<BinSh> = (0..w1_words).map(|w| w1_bin.slice(w, 1)).collect();
    let mut state1: [BinSh; 25] =
        core::array::from_fn(|_| engine.zeros_bin(1).expect("engine active"));
    let mut lane_pos = 0usize;
    for lane in mu_lanes.iter().chain(w1_lanes.iter()) {
        state1[lane_pos] = state1[lane_pos].xor(lane);
        lane_pos += 1;
        if lane_pos == 17 {
            mpc_keccak_f1600(engine, &mut state1)?;
            lane_pos = 0;
        }
    }
    let pad_start = engine.public_bin(&[0x1Fu64])?;
    let pad_end = engine.public_bin(&[0x80u64 << 56])?;
    state1[lane_pos] = state1[lane_pos].xor(&pad_start);
    state1[16] = state1[16].xor(&pad_end);
    mpc_keccak_f1600(engine, &mut state1)?;
    let c_tilde_words = params.c_tilde_bytes / 8;

    // 3. Sponge 2: SampleInBall(c_tilde) over 232 candidate bytes (< 2^-157 shortfall).
    let mut state2: [BinSh; 25] =
        core::array::from_fn(|_| engine.zeros_bin(1).expect("engine active"));
    state2[..c_tilde_words].clone_from_slice(&state1[..c_tilde_words]);
    state2[c_tilde_words] = state2[c_tilde_words].xor(&pad_start);
    state2[16] = state2[16].xor(&pad_end);
    mpc_keccak_f1600(engine, &mut state2)?;
    let sign_word = state2[0].clone();
    let mut cand_lanes: Vec<BinSh> = Vec::with_capacity(29);
    for lane in &state2[1..17] {
        cand_lanes.push(lane.clone());
    }
    mpc_keccak_f1600(engine, &mut state2)?;
    for lane in &state2[0..13] {
        cand_lanes.push(lane.clone());
    }

    // 4. Bit-sliced comparison b_t <= (256 - tau + k) across k = 0..tau for all 232 candidates.
    let tau = params.tau;
    let mask_tau = (1u64 << tau) - 1;
    let raw_b: [BinSh; 8] = core::array::from_fn(|r| {
        let mut out = BinSh::zeros(comps, CAND_BYTES);
        for t in 0..CAND_BYTES {
            let shift = (t % 8) * 8 + r;
            for i in 0..comps {
                out.c[i][t] = (cand_lanes[t / 8].c[i][0] >> shift) & 1;
            }
        }
        out
    });
    let b_bcast: [BinSh; 8] = core::array::from_fn(|r| raw_b[r].broadcast_bit0(mask_tau));
    let not_c_masks: [u64; 8] = core::array::from_fn(|r| {
        let mut c_r = 0u64;
        for k in 0..tau {
            let bound_k = (MLDSA_N - tau + k) as u64;
            c_r |= ((bound_k >> r) & 1) << k;
        }
        (!c_r) & mask_tau
    });
    let mut borrow = b_bcast[0].and_pub(&vec![not_c_masks[0]; CAND_BYTES]);
    for r in 1..8 {
        let prod = engine.bit_and(&b_bcast[r], &borrow)?;
        let xored = b_bcast[r]
            .xor(&borrow)
            .and_pub(&vec![not_c_masks[r]; CAND_BYTES]);
        borrow = prod.xor(&xored);
    }
    let le_mask = engine
        .not_bin(&borrow)?
        .and_pub(&vec![mask_tau; CAND_BYTES]);

    // 5. Sequential SampleInBall cursor over t = 0..232.
    let mut cursor = engine.public_bin(&[1u64])?;
    let mut fires: Vec<BinSh> = Vec::with_capacity(CAND_BYTES);
    for t in 0..CAND_BYTES {
        let fire_t = engine.bit_and(&cursor, &le_mask.slice(t, 1))?;
        cursor = cursor.xor(&fire_t).xor(&fire_t.shl_bits(1));
        fires.push(fire_t);
    }
    let sib_incomplete_bin = engine
        .not_bin(&cursor.shr_bits(tau as u32))?
        .and_pub(&[1u64]);

    // 6. Select j_k = b_{t_k} and tree-decode to 256-bit one-hot masks sel[0..tau].
    let fire_refs: Vec<&BinSh> = fires.iter().collect();
    let fire_all = BinSh::concat(&fire_refs);
    let b_bcast_refs: [&BinSh; 8] = core::array::from_fn(|r| &b_bcast[r]);
    let j_prod_all = engine.bit_and(&BinSh::concat(&b_bcast_refs), &fire_all.repeat(8))?;
    let j_words: [BinSh; 8] = core::array::from_fn(|r| {
        j_prod_all
            .slice(r * CAND_BYTES, CAND_BYTES)
            .xor_reduce_words()
    });
    let j_bits: [BinSh; 8] = core::array::from_fn(|r| {
        let mut out = BinSh::zeros(comps, tau);
        for i in 0..comps {
            let w = j_words[r].c[i][0];
            for k in 0..tau {
                out.c[i][k] = (w >> k) & 1;
            }
        }
        out
    });
    let j_refs: [&BinSh; 8] = core::array::from_fn(|r| &j_bits[r]);
    let nj_all = engine
        .not_bin(&BinSh::concat(&j_refs))?
        .and_pub(&vec![1u64; 8 * tau]);
    let nj_bits: [BinSh; 8] = core::array::from_fn(|r| nj_all.slice(r * tau, tau));

    // Tree decode round 1: 4 pairs of 2-bit groups (16 products of length tau).
    let mut r1_lhs: Vec<&BinSh> = Vec::with_capacity(16);
    let mut r1_rhs: Vec<&BinSh> = Vec::with_capacity(16);
    for p in 0..4 {
        let b0 = [&nj_bits[2 * p], &j_bits[2 * p]];
        let b1 = [&nj_bits[2 * p + 1], &j_bits[2 * p + 1]];
        for &hi_bit in &b1 {
            for &lo_bit in &b0 {
                r1_lhs.push(lo_bit);
                r1_rhs.push(hi_bit);
            }
        }
    }
    let r1_prod = engine.bit_and(&BinSh::concat(&r1_lhs), &BinSh::concat(&r1_rhs))?;
    let g2: [[BinSh; 4]; 4] =
        core::array::from_fn(|p| core::array::from_fn(|v| r1_prod.slice((4 * p + v) * tau, tau)));

    // Tree decode round 2: low nibble and high nibble (32 products of length tau).
    let mut r2_lhs: Vec<&BinSh> = Vec::with_capacity(32);
    let mut r2_rhs: Vec<&BinSh> = Vec::with_capacity(32);
    for hi in 0..4 {
        for lo in 0..4 {
            r2_lhs.push(&g2[0][lo]);
            r2_rhs.push(&g2[1][hi]);
        }
    }
    for hi in 0..4 {
        for lo in 0..4 {
            r2_lhs.push(&g2[2][lo]);
            r2_rhs.push(&g2[3][hi]);
        }
    }
    let r2_prod = engine.bit_and(&BinSh::concat(&r2_lhs), &BinSh::concat(&r2_rhs))?;
    let lo4: [BinSh; 16] = core::array::from_fn(|v| r2_prod.slice(v * tau, tau));
    let hi4: [BinSh; 16] = core::array::from_fn(|v| r2_prod.slice((16 + v) * tau, tau));

    // Tree decode round 3: full byte 0..256 (256 products of length tau).
    let mut r3_lhs: Vec<&BinSh> = Vec::with_capacity(MLDSA_N);
    let mut r3_rhs: Vec<&BinSh> = Vec::with_capacity(MLDSA_N);
    for hi_nibble in &hi4 {
        for lo_nibble in &lo4 {
            r3_lhs.push(lo_nibble);
            r3_rhs.push(hi_nibble);
        }
    }
    let r3_prod = engine.bit_and(&BinSh::concat(&r3_lhs), &BinSh::concat(&r3_rhs))?;
    let mut sel: Vec<BinSh> = (0..tau).map(|_| BinSh::zeros(comps, 4)).collect();
    for v in 0..MLDSA_N {
        let oh_v = r3_prod.slice(v * tau, tau);
        for i in 0..comps {
            for (k, sel_k) in sel.iter_mut().enumerate().take(tau) {
                sel_k.c[i][v / 64] |= (oh_v.c[i][k] & 1) << (v % 64);
            }
        }
    }

    // 7. Fisher-Yates SampleInBall loop over k = 0..tau.
    let mut sign_bcast = BinSh::zeros(comps, 4 * tau);
    for i in 0..comps {
        let sw = sign_word.c[i][0];
        for k in 0..tau {
            let bit = (sw >> k) & 1;
            let mask = 0u64.wrapping_sub(bit);
            for w in 0..4 {
                sign_bcast.c[i][4 * k + w] = mask;
            }
        }
    }
    let sel_refs: Vec<&BinSh> = sel.iter().collect();
    let sign_sel_all = engine.bit_and(&sign_bcast, &BinSh::concat(&sel_refs))?;
    let mut nz = engine.zeros_bin(4)?;
    let mut neg = engine.zeros_bin(4)?;
    for (k, sel_k) in sel.iter().enumerate() {
        let idx_i = MLDSA_N - tau + k;
        let both = engine.bit_and(
            &BinSh::concat(&[&nz, &neg]),
            &BinSh::concat(&[sel_k, sel_k]),
        )?;
        let prod_nz = both.slice(0, 4);
        let prod_neg = both.slice(4, 4);
        let nz_j = prod_nz.bit_parity();
        let neg_j = prod_neg.bit_parity();
        nz = nz
            .xor(&prod_nz)
            .xor(sel_k)
            .xor(&place_bit0_256(&nz_j, idx_i));
        neg = neg
            .xor(&prod_neg)
            .xor(&sign_sel_all.slice(4 * k, 4))
            .xor(&place_bit0_256(&neg_j, idx_i));
    }

    // 8. Reverse daBit conversion of (nz, neg, sib_incomplete) into F_q shares:
    // open_bin verifies every binary gate in GF(2^128) BEFORE c touches s1 or s2.
    let (r2_fq, r2_bin) = engine.rand_dabits(513)?;
    let packed_c = BinSh::concat(&[&nz, &neg, &sib_incomplete_bin]).xor(&r2_bin);
    let opened_c_words = engine.open_bin(&[&packed_c])?.remove(0);
    if opened_c_words[8] > 1 {
        return Err(ThresholdMlDsaError::ProtocolInvariantViolated);
    }
    let mut m_bits = Vec::with_capacity(513);
    for pos in 0..513 {
        m_bits.push(((opened_c_words[pos / 64] >> (pos % 64)) & 1) as u32);
    }
    let m_fq = engine.public(&m_bits)?;
    let lifted = m_fq.add(&r2_fq).sub(&r2_fq.mul_pub(&m_bits).scale(2));
    let nz_fq = lifted.slice(0, MLDSA_N);
    let neg_fq = lifted.slice(MLDSA_N, MLDSA_N);
    let sib_incomplete_fq = lifted.slice(2 * MLDSA_N, 1);
    let c_share = nz_fq.sub(&neg_fq.scale(2));
    Ok((c_share, sib_incomplete_fq))
}

/// Computes `[hb_bits != w1_bits]` in `{0, 1} subset F_q` for `4`-bit or `6`-bit planes.
fn hint_diff_bits<T: MpcTransport>(
    engine: &mut Engine<'_, T>,
    hb_bits: &[Sh],
    w1_bits: &[Sh],
) -> Result<Sh, MpcError> {
    let b_width = hb_bits.len();
    let w_len = hb_bits[0].len();
    let hb_refs: Vec<&Sh> = hb_bits.iter().collect();
    let w1_refs: Vec<&Sh> = w1_bits.iter().collect();
    let prod = engine.mul(&Sh::concat(&hb_refs), &Sh::concat(&w1_refs))?;
    let diff: Vec<Sh> = (0..b_width)
        .map(|d| {
            hb_bits[d]
                .add(&w1_bits[d])
                .sub(&prod.slice(d * w_len, w_len).scale(2))
        })
        .collect();
    if b_width == 4 {
        let p = engine.mul(
            &Sh::concat(&[&diff[0], &diff[2]]),
            &Sh::concat(&[&diff[1], &diff[3]]),
        )?;
        let or01 = diff[0].add(&diff[1]).sub(&p.slice(0, w_len));
        let or23 = diff[2].add(&diff[3]).sub(&p.slice(w_len, w_len));
        let p2 = engine.mul(&or01, &or23)?;
        Ok(or01.add(&or23).sub(&p2))
    } else {
        debug_assert_eq!(b_width, 6);
        let p = engine.mul(
            &Sh::concat(&[&diff[0], &diff[2], &diff[4]]),
            &Sh::concat(&[&diff[1], &diff[3], &diff[5]]),
        )?;
        let or01 = diff[0].add(&diff[1]).sub(&p.slice(0, w_len));
        let or23 = diff[2].add(&diff[3]).sub(&p.slice(w_len, w_len));
        let or45 = diff[4].add(&diff[5]).sub(&p.slice(2 * w_len, w_len));
        let p0123 = engine.mul(&or01, &or23)?;
        let or0123 = or01.add(&or23).sub(&p0123);
        let p_all = engine.mul(&or0123, &or45)?;
        Ok(or0123.add(&or45).sub(&p_all))
    }
}

/// Evaluates all FIPS 204 rejection predicates (`SampleInBall` completion,
/// `||z||_inf < gamma1 - beta`, `||r0||_inf < gamma2 - beta`,
/// `HighBits(w - c*s2) == w1`, `||c*t0||_inf < gamma2`, and
/// `weight(MakeHint(-c*t0, w - c*s2 + c*t0)) <= omega`) without opening `w1`,
/// `c`, `z`, or `h` on rejected attempts.
#[allow(clippy::too_many_arguments)]
fn sealed_rejection_verdict<T: MpcTransport>(
    engine: &mut Engine<'_, T>,
    (z_masked, z_bound): (&Sh, u32),
    (low, low_bound, low_masks): (&Sh, u32, &Sh),
    (ct0_sh, ct0_masks): (&Sh, &Sh),
    (hint_r_sh, hint_r_masks, hint_r_planes): (&Sh, &Sh, &[Sh]),
    (hw_mask, omega): (&Sh, usize),
    range_planes: &[Sh],
    w1_bit_planes: &[Sh],
    sib_incomplete_fq: &Sh,
    gamma2: u32,
) -> Result<Option<(bool, bool, bool)>, MpcError> {
    let z_len = z_masked.len();
    let w_len = low.len();
    let low_masked = low
        .add(&engine.public_const(low_bound - 1, w_len)?)
        .add(low_masks);
    let ct0_masked = ct0_sh
        .add(&engine.public_const(gamma2 - 1, w_len)?)
        .add(ct0_masks);
    let hint_r_masked = hint_r_sh
        .add(&engine.public_const(gamma2 - 1, w_len)?)
        .add(hint_r_masks);
    let batch_masked = Sh::concat(&[z_masked, &low_masked, &ct0_masked, &hint_r_masked]);
    let opened_batch = engine.open(&[&batch_masked])?.remove(0);

    let (_, hb_hint_bits) = high_bits_circuit_with_bits(
        engine,
        &opened_batch[z_len + 2 * w_len..z_len + 3 * w_len],
        hint_r_planes,
        gamma2,
    )?;
    let hint_bits = hint_diff_bits(engine, &hb_hint_bits, w1_bit_planes)?;
    let hint_weight = hint_bits.sum();
    let hw_opened = engine.open(&[&hint_weight.add(hw_mask)])?.remove(0);

    let mut range_opened = Vec::with_capacity(z_len + 2 * w_len + 1);
    range_opened.extend_from_slice(&opened_batch[..z_len + 2 * w_len]);
    range_opened.push(hw_opened[0]);

    let mut widths = vec![2 * z_bound - 1; z_len];
    widths.extend_from_slice(&vec![2 * low_bound - 1; w_len]);
    widths.extend_from_slice(&vec![2 * gamma2 - 1; w_len]);
    widths.push((omega + 1) as u32);

    let inside = masked_range_test(engine, &range_opened, &widths, range_planes)?;
    let outside = engine.public_const(1, z_len + 2 * w_len + 1)?.sub(&inside);
    let z_failures = outside.slice(0, z_len).sum();
    let low_failures = outside.slice(z_len, w_len).sum();
    let ct0_failures = outside.slice(z_len + w_len, w_len).sum();
    let hw_failures = outside.slice(z_len + 2 * w_len, 1);

    let high_opened: Vec<u32> = opened_batch[z_len..z_len + w_len]
        .iter()
        .map(|&v| fq_add(v, gamma2 - low_bound))
        .collect();
    let high_planes: Vec<Sh> = range_planes.iter().map(|p| p.slice(z_len, w_len)).collect();
    let high_inside = masked_range_test(
        engine,
        &high_opened,
        &vec![2 * gamma2 - 1; w_len],
        &high_planes,
    )?;
    let high_failures = engine.public_const(1, w_len)?.sub(&high_inside).sum();

    let aux_failures = ct0_failures.add(&hw_failures).add(sib_incomplete_fq);
    let joint_failures = z_failures
        .add(&low_failures)
        .add(&high_failures)
        .add(&aux_failures);
    let joint_blind = engine.rand(EXT_DEGREE)?;
    let joint = engine.mul(&joint_blind, &joint_failures.repeat(EXT_DEGREE))?;
    if engine.open(&[&joint])?[0].iter().any(|&v| v != 0) {
        return Ok(None);
    }

    let mut bits = [false; 4];
    for (index, failures) in [z_failures, low_failures, high_failures, aux_failures]
        .iter()
        .enumerate()
    {
        let blind = engine.rand(EXT_DEGREE)?;
        let verdict = engine.mul(&blind, &failures.repeat(EXT_DEGREE))?;
        let verdict = engine.open(&[&verdict])?;
        bits[index] = verdict[0].iter().all(|&v| v == 0);
    }
    Ok(Some((bits[0] && bits[3], bits[1], bits[2])))
}

/// First opens only the joint acceptance bit. After acceptance, checks the
/// three predicates independently before releasing their witnesses. A rejected
/// attempt never reveals which predicate failed. The masked coefficient openings
/// are shared by the circuits; no unmasked coefficient is released.
#[cfg(test)]
fn rejection_verdict<T: MpcTransport>(
    engine: &mut Engine<'_, T>,
    (z_masked, z_bound): (&Sh, u32),
    (low, low_bound, low_masks): (&Sh, u32, &Sh),
    planes: &[Sh],
    high_bound: u32,
) -> Result<Option<(bool, bool, bool)>, MpcError> {
    let z_len = z_masked.len();
    let low_len = low.len();
    let low_masked = low
        .add(&engine.public_const(low_bound - 1, low_len)?)
        .add(low_masks);
    let masked = Sh::concat(&[z_masked, &low_masked]);
    let opened = engine.open(&[&masked])?.remove(0);
    let mut widths = vec![2 * z_bound - 1; z_len];
    widths.extend_from_slice(&vec![2 * low_bound - 1; low_len]);
    let inside = masked_range_test(engine, &opened, &widths, planes)?;
    let outside = engine.public_const(1, z_len + low_len)?.sub(&inside);
    let z_failures = outside.slice(0, z_len).sum();
    let low_failures = outside.slice(z_len, low_len).sum();
    // A wider residual interval checks the HighBits relation separately from
    // the stricter rejection norm. Shifting a masked public value by a public
    // constant preserves its mask and does not disclose the residual.
    let high_opened: Vec<u32> = opened[z_len..]
        .iter()
        .map(|&v| fq_add(v, high_bound - low_bound))
        .collect();
    let high_planes: Vec<Sh> = planes.iter().map(|p| p.slice(z_len, low_len)).collect();
    let high_inside = masked_range_test(
        engine,
        &high_opened,
        &vec![2 * high_bound - 1; low_len],
        &high_planes,
    )?;
    let high_failures = engine.public_const(1, low_len)?.sub(&high_inside).sum();
    let joint_failures = z_failures.add(&low_failures).add(&high_failures);
    let joint_blind = engine.rand(EXT_DEGREE)?;
    let joint = engine.mul(&joint_blind, &joint_failures.repeat(EXT_DEGREE))?;
    if engine.open(&[&joint])?[0].iter().any(|&v| v != 0) {
        return Ok(None);
    }
    let mut bits = [false; 3];
    for (index, failures) in [z_failures, low_failures, high_failures].iter().enumerate() {
        let blind = engine.rand(EXT_DEGREE)?;
        let verdict = engine.mul(&blind, &failures.repeat(EXT_DEGREE))?;
        let verdict = engine.open(&[&verdict])?;
        bits[index] = verdict[0].iter().all(|&v| v == 0);
    }
    Ok(Some((bits[0], bits[1], bits[2])))
}

/// Branchless reduction of 128 uniform keystream bits modulo `MLDSA_Q` (`< 2^-103` bias).
#[inline]
fn stream_word_mod_q(block: &[u8; 16]) -> u32 {
    const RADIX_21: u32 = 1 << 21;
    const MASK_21: u128 = (1u128 << 21) - 1;
    let raw = u128::from_le_bytes(*block);
    let mut acc = ((raw >> 105) & MASK_21) as u32;
    let mut shift = 84u32;
    loop {
        let limb = ((raw >> shift) & MASK_21) as u32;
        acc = fq_add(fq_mul(acc, RADIX_21), limb);
        if shift == 0 {
            break;
        }
        shift -= 21;
    }
    acc
}

fn apply_response_stream_cipher(
    response: &mut Sh,
    seal_key: &[u8; 32],
    context: &[u8; 32],
    attempt: u32,
    encrypt: bool,
) {
    let mut xof = Shake256::new();
    xof.absorb(b"QSAG.MLDSA.PENDING_CIPHER.V1");
    xof.absorb(seal_key);
    xof.absorb(context);
    xof.absorb(&attempt.to_be_bytes());
    xof.finalize(0x1f);
    // A bounded batch preserves the exact XOF byte stream, including between
    // components, while avoiding a squeeze call for every coefficient.
    let mut stream = [0u8; 16 * 128];
    for component in &mut response.c {
        for coeffs in component.chunks_mut(128) {
            let bytes = &mut stream[..16 * coeffs.len()];
            xof.squeeze(bytes);
            for (coeff, block) in coeffs.iter_mut().zip(bytes.as_chunks::<16>().0) {
                let mask = stream_word_mod_q(block);
                *coeff = if encrypt { fq_add(*coeff, mask) } else { fq_sub(*coeff, mask) };
            }
        }
    }
    ct_zeroize_bytes(&mut stream);
}

/// Seals the pending `z` shares under a per-attempt XOF stream cipher whose only
/// decryption key is held privately inside `qsag_verified::MlDsaReleaseGate`.
/// Any failed rejection-sampling or commitment barrier wipes the key to `[0u8; 32]`
/// inside `qsag-verified`, rendering `sealed_response` cryptographically unrecoverable.
struct PendingResponse {
    sealed_response: Sh,
    ciphertext_tag: [u8; 32],
    gate: MlDsaReleaseGate,
}

impl PendingResponse {
    fn new_sealed(
        mut response: Sh,
        context: [u8; 32],
        attempt: u32,
        seal_entropy: &[u8; 32],
    ) -> Self {
        let mut seal_key = cshake256_framed_32(
            b"QSAG.MLDSA.SEAL_KEY.V1",
            &[seal_entropy, &context, &attempt.to_be_bytes()],
        );
        apply_response_stream_cipher(&mut response, &seal_key, &context, attempt, true);
        let ciphertext_tag = Self::ciphertext_tag(&response, &context, attempt);
        let gate = MlDsaReleaseGate::new_sealed(context, attempt, seal_key);
        ct_zeroize_bytes(&mut seal_key);
        Self {
            sealed_response: response,
            ciphertext_tag,
            gate,
        }
    }

    fn ciphertext_tag(ciphertext: &Sh, context: &[u8; 32], attempt: u32) -> [u8; 32] {
        let mut sponge = Shake256::new();
        sponge.absorb(b"QSAG.MLDSA.PENDING_CT_TAG.V1");
        sponge.absorb(context);
        sponge.absorb(&attempt.to_be_bytes());
        sponge.absorb(&(ciphertext.c.len() as u64).to_be_bytes());
        for component in &ciphertext.c {
            sponge.absorb(&(component.len() as u64).to_be_bytes());
            for coefficient in component {
                sponge.absorb(&coefficient.to_le_bytes());
            }
        }
        sponge.finalize(0x1f);
        let mut digest = [0; 32];
        sponge.squeeze(&mut digest);
        digest
    }

    fn release(mut self, checks: MlDsaBarrierChecks) -> Result<Sh, ThresholdMlDsaError> {
        let (_, released_key) = self.gate.try_release_z_share(checks);
        let mut seal_key =
            released_key.map_err(|_| ThresholdMlDsaError::ProtocolInvariantViolated)?;
        let expected_tag = Self::ciphertext_tag(
            &self.sealed_response,
            &checks.req_session_id,
            checks.req_attempt,
        );
        if !ct_eq_bytes(&self.ciphertext_tag, &expected_tag) {
            ct_zeroize_bytes(&mut seal_key);
            return Err(ThresholdMlDsaError::ProtocolInvariantViolated);
        }
        apply_response_stream_cipher(
            &mut self.sealed_response,
            &seal_key,
            &checks.req_session_id,
            checks.req_attempt,
            false,
        );
        ct_zeroize_bytes(&mut seal_key);
        Ok(self.sealed_response)
    }
}

struct SessionKey {
    s1_hat: Vec<Vec<Poly256>>,
    s2_hat: Vec<Vec<Poly256>>,
}

impl Drop for SessionKey {
    fn drop(&mut self) {
        for poly in self.s1_hat.iter_mut().chain(&mut self.s2_hat).flatten() {
            poly.zeroize();
        }
    }
}

/// Re-expresses the long-term components over the session's subsets. Each
/// long-term subset is assigned to the first session subset it contains, so
/// every member of that session subset holds it and no communication is
/// needed. A component hidden from a coalition stays hidden.
fn session_key(
    share: &ThresholdMlDsaSignerShare,
    quorum: &[u16],
    structure: &Structure,
    comps: &[usize],
    params: &MlDsaParams,
) -> Result<SessionKey, ThresholdMlDsaError> {
    let mut key = SessionKey {
        s1_hat: vec![vec![Poly256::zero(); params.ell]; comps.len()],
        s2_hat: vec![vec![Poly256::zero(); params.k]; comps.len()],
    };
    for subset in &share.subsets {
        let mut present = Vec::new();
        for (position, id) in quorum.iter().enumerate() {
            let global = share
                .pack
                .party_ids
                .iter()
                .position(|p| p == id)
                .expect("validated quorum");
            if subset.holders.binary_search(&global).is_ok() {
                present.push(position);
            }
        }
        let target = structure
            .subsets
            .iter()
            .position(|holders| holders.iter().all(|p| present.binary_search(p).is_ok()))
            .ok_or(ThresholdMlDsaError::ProtocolInvariantViolated)?;
        if let Some(i) = comps.iter().position(|&c| c == target) {
            for (acc, poly) in key.s1_hat[i].iter_mut().zip(&subset.s1_hat) {
                *acc = acc.add(poly);
            }
            for (acc, poly) in key.s2_hat[i].iter_mut().zip(&subset.s2_hat) {
                *acc = acc.add(poly);
            }
        }
    }
    Ok(key)
}

/// Runs one custodian's side of a signing session and returns a standard
/// FIPS 204 signature.
///
/// `entropy` must be fresh secret randomness for this session. The quorum
/// must contain at least `2t - 1` custodians.
pub fn threshold_sign_mldsa_party<T: MpcTransport>(
    share: &mut ThresholdMlDsaSignerShare,
    session: &ThresholdSignSession,
    msg: &[u8],
    ctx: &[u8],
    entropy: &[u8; 32],
    burn: &mut dyn NonceBurnPersistence,
    net: &mut T,
) -> Result<ThresholdSignOutput, ThresholdMlDsaError> {
    let level = share.pack.level;
    let threshold = share.pack.threshold;
    check_parameters(level, threshold, share.pack.party_ids.len())?;
    let params = level.params();
    let quorum = sorted_distinct(&session.quorum)?;
    if let Some(&unknown) = quorum.iter().find(|id| !share.pack.party_ids.contains(id)) {
        return Err(ThresholdMlDsaError::DuplicateOrUnknownParty { party_id: unknown });
    }
    let me = quorum.iter().position(|&id| id == share.party_id).ok_or(
        ThresholdMlDsaError::DuplicateOrUnknownParty {
            party_id: share.party_id,
        },
    )?;
    if quorum.len() < 2 * threshold - 1 {
        return Err(ThresholdMlDsaError::QuorumTooSmall {
            have: quorum.len(),
            need: 2 * threshold - 1,
        });
    }
    let mu = compute_fips204_mu(&share.pack.pk_bytes, msg, ctx)
        .ok_or(ThresholdMlDsaError::ContextTooLong)?;
    let structure = Structure::new(quorum.len(), threshold)?;
    let context = cshake256_framed_32(
        b"QSAG.TMLDSA.SIGN.CTX.V1",
        &[
            &session.session_id,
            &share.pack.pk_bytes,
            &mu,
            &ids_bytes(&quorum),
            &[threshold as u8],
        ],
    );
    let hedged = cshake256_framed_32(
        b"QSAG.TMLDSA.SIGN.ENTROPY.V1",
        &[entropy, &share.custody_digest(), &context],
    );
    let mut engine = Engine::setup(net, structure.clone(), me, &context, &hedged)?;
    let key = session_key(share, &quorum, &structure, engine.comps(), &params)?;
    let comps = engine.comps().len();

    let a_hat = expand_a_ntt(&params, &share.pack.rho);
    let mut t0_hat = Vec::with_capacity(params.k);
    let mut t1_scaled_hat = Vec::with_capacity(params.k);
    for poly in &share.pack.t {
        let mut low = Poly256::zero();
        let mut high = Poly256::zero();
        for ((lo, hi), &value) in low
            .coeffs
            .iter_mut()
            .zip(&mut high.coeffs)
            .zip(&poly.coeffs)
        {
            let (t1, t0) = power2round(value);
            *lo = t0;
            *hi = (t1 << MLDSA_D) % MLDSA_Q;
        }
        low.ntt();
        high.ntt();
        t0_hat.push(low);
        t1_scaled_hat.push(high);
    }

    let gamma1 = params.gamma1;
    let gamma2 = params.gamma2;
    let alpha = 2 * gamma2;
    let w1_bins = (MLDSA_Q - 1) / alpha;
    let y_bits = (gamma1.trailing_zeros() + 1) as usize;
    let z_len = params.ell * MLDSA_N;
    let w_len = params.k * MLDSA_N;
    let masks_needed = 4 * w_len + z_len + 1;
    let masks = masks_needed + SPARE_MASKS;

    let mut s_hat_sh = engine.zeros(z_len + w_len)?;
    for i in 0..comps {
        let mut flat_s = flatten(&key.s1_hat[i]);
        flat_s.extend_from_slice(&flatten(&key.s2_hat[i]));
        s_hat_sh.c[i] = flat_s;
    }

    for attempt in 0..DEFAULT_MAX_REJECTION_ATTEMPTS {
        let epoch = share.next_epoch;
        share.next_epoch = epoch
            .checked_add(1)
            .ok_or(ThresholdMlDsaError::NoncePersistenceFailed)?;
        if !burn.reserve(share.party_id, epoch, &session.session_id, attempt) {
            return Err(ThresholdMlDsaError::NoncePersistenceFailed);
        }

        // Phase 1: the mask y and the conversion masks.
        engine.set_phase(PHASE_SIGN_MASKS);
        let bits = engine.rand_bits(y_bits * z_len + MASK_BITS * masks)?;
        let y_planes: Vec<Sh> = (0..y_bits).map(|i| bits.slice(i * z_len, z_len)).collect();
        let y = engine.public_const(gamma1, z_len)?.sub(&compose(&y_planes));
        let planes: Vec<Sh> = (0..MASK_BITS)
            .map(|i| bits.slice(y_bits * z_len + i * masks, masks))
            .collect();
        let in_field = less_than_public(&mut engine, &planes, &vec![MLDSA_Q; masks])?;
        let flags = engine.open(&[&in_field])?;
        require_bits(&flags[0])?;
        let usable: Vec<usize> = (0..masks)
            .filter(|&i| flags[0][i] == 1)
            .take(masks_needed)
            .collect();
        if usable.len() < masks_needed {
            continue;
        }
        let mask_values = compose(&planes);
        let (high_idx, rest) = usable.split_at(w_len);
        let (z_idx, rest) = rest.split_at(z_len);
        let (low_idx, rest) = rest.split_at(w_len);
        let (ct0_idx, rest) = rest.split_at(w_len);
        let (hint_r_idx, hw_idx) = rest.split_at(w_len);

        let mut w = engine.zeros(w_len)?;
        for i in 0..comps {
            let y_hat = ntt_all(to_polys(&y.c[i]));
            w.c[i] = flatten(&inv_ntt_all(mat_vec_mul_ntt(&a_hat, &y_hat)));
        }
        let shifted = w.add(&engine.public_const(gamma2 - 1, w_len)?);
        let opened_w = engine.open(&[&shifted.add(&mask_values.gather(high_idx))])?;

        // Phase 2: HighBits(w) — verified in place while keeping w1 secret-shared!
        engine.set_phase(PHASE_SIGN_HIGH_BITS);
        let high_planes: Vec<Sh> = planes.iter().map(|plane| plane.gather(high_idx)).collect();
        let (w1_share, w1_bit_planes) =
            high_bits_circuit_with_bits(&mut engine, &opened_w[0], &high_planes, gamma2)?;
        engine.verify()?;

        // Phase 3: sealed challenge derivation + joint rejection verdict (zero w1 opened on abort).
        engine.set_phase(PHASE_SIGN_REJECTION);
        let (c_share, sib_incomplete_fq) =
            mpc_derive_challenge(&mut engine, &params, &mu, &w1_bit_planes)?;
        let mut c_hat_sh = engine.zeros(MLDSA_N)?;
        let mut ct0_sh = engine.zeros(w_len)?;
        for i in 0..comps {
            let mut c_poly = Poly256 {
                coeffs: core::array::from_fn(|j| c_share.c[i][j]),
            };
            c_poly.ntt();
            ct0_sh.c[i] = challenge_times(&c_poly, &t0_hat);
            c_hat_sh.c[i] = c_poly.coeffs.to_vec();
            c_poly.zeroize();
        }
        let cs_hat_sh = engine.mul(&c_hat_sh.repeat(params.ell + params.k), &s_hat_sh)?;
        let mut cs1_sh = engine.zeros(z_len)?;
        let mut cs2_sh = engine.zeros(w_len)?;
        for i in 0..comps {
            let cs_coeff = flatten(&inv_ntt_all(to_polys(&cs_hat_sh.c[i])));
            cs1_sh.c[i] = cs_coeff[..z_len].to_vec();
            cs2_sh.c[i] = cs_coeff[z_len..].to_vec();
        }

        let z = y.add(&cs1_sh);
        let w_minus_cs2 = w.sub(&cs2_sh);
        let low = w_minus_cs2.sub(&w1_share.scale(alpha));
        let hint_r_sh = w_minus_cs2.add(&ct0_sh);

        let z_bound = gamma1 - params.beta;
        let low_bound = gamma2 - params.beta;
        let range_idx: Vec<usize> = z_idx
            .iter()
            .chain(low_idx)
            .chain(ct0_idx)
            .chain(hw_idx)
            .copied()
            .collect();
        let range_planes: Vec<Sh> = planes
            .iter()
            .map(|plane| plane.gather(&range_idx))
            .collect();
        let hint_r_planes: Vec<Sh> = planes
            .iter()
            .map(|plane| plane.gather(hint_r_idx))
            .collect();
        let z_masked = z
            .add(&engine.public_const(z_bound - 1, z_len)?)
            .add(&mask_values.gather(z_idx));
        let mut seal_entropy = cshake256_framed_32(
            b"QSAG.TMLDSA.SEAL_ENTROPY.V1",
            &[
                &hedged,
                &context,
                &attempt.to_be_bytes(),
                &epoch.to_be_bytes(),
            ],
        );
        let pending = PendingResponse::new_sealed(z, context, attempt, &seal_entropy);
        ct_zeroize_bytes(&mut seal_entropy);
        let low_masks = mask_values.gather(low_idx);
        let ct0_masks = mask_values.gather(ct0_idx);
        let hint_r_masks = mask_values.gather(hint_r_idx);
        let hw_mask = mask_values.gather(hw_idx);

        let checks = sealed_rejection_verdict(
            &mut engine,
            (&z_masked, z_bound),
            (&low, low_bound, &low_masks),
            (&ct0_sh, &ct0_masks),
            (&hint_r_sh, &hint_r_masks, &hint_r_planes),
            (&hw_mask, params.omega),
            &range_planes,
            &w1_bit_planes,
            &sib_incomplete_fq,
            gamma2,
        )?;
        let Some((z_norm_ok, r0_norm_ok, w1_match)) = checks else {
            // Dropping the sealed response wipes it before the next attempt.
            continue;
        };
        let u_com_bound = engine.verify().is_ok();
        let accepted = z_norm_ok && r0_norm_ok && w1_match && u_com_bound;
        let released = pending.release(MlDsaBarrierChecks {
            req_session_id: context,
            req_attempt: attempt,
            z_norm_ok,
            r0_norm_ok,
            w1_match,
            u_com_bound,
        });
        if !accepted {
            // Consume the rejecting gate as well; no response survives retry.
            debug_assert!(released.is_err());
            continue;
        }
        let z = released?;

        // Phase 4: release (w1, z) jointly in one opening round after all barriers pass.
        engine.set_phase(PHASE_SIGN_RELEASE);
        let opened_release = engine.open(&[&w1_share, &z])?;
        let w1 = &opened_release[0];
        if w1.iter().any(|&v| v >= w1_bins) {
            return Err(ThresholdMlDsaError::ProtocolInvariantViolated);
        }
        let w1_polys = to_polys(w1);
        let mut c_tilde = vec![0u8; params.c_tilde_bytes];
        let mut xof = Shake256::new();
        xof.absorb(&mu);
        xof.absorb(&w1_encode(&params, &w1_polys));
        xof.finalize(0x1F);
        xof.squeeze(&mut c_tilde);
        let mut c_hat = sample_in_ball(&c_tilde, params.tau);
        c_hat.ntt();

        let z_public = to_polys(&opened_release[1]);
        if z_public.iter().any(|poly| poly.inf_norm() >= z_bound) {
            return Err(ThresholdMlDsaError::ProtocolInvariantViolated);
        }
        let az_hat = mat_vec_mul_ntt(&a_hat, &ntt_all(z_public.clone()));
        let mut hints = vec![[0u8; MLDSA_N]; params.k];
        let mut weight = 0usize;
        let mut consistent = true;
        for (row, hint_row) in hints.iter_mut().enumerate() {
            let mut approx = az_hat[row].sub(&c_hat.pointwise_mul(&t1_scaled_hat[row]));
            approx.inv_ntt();
            for (j, hint) in hint_row.iter_mut().enumerate() {
                let target = w1_polys[row].coeffs[j];
                *hint = (high_bits_ct(approx.coeffs[j], gamma2) != target) as u8;
                weight += *hint as usize;
                consistent &= use_hint(*hint, approx.coeffs[j], gamma2) == target;
            }
        }
        if !consistent || weight > params.omega {
            return Err(ThresholdMlDsaError::ProtocolInvariantViolated);
        }
        let signature = sig_encode(&params, &c_tilde, &z_public, &hints);
        if !ml_dsa_verify(level, &share.pack.pk_bytes, msg, ctx, &signature) {
            return Err(ThresholdMlDsaError::SignatureVerificationFailed);
        }
        return Ok(ThresholdSignOutput {
            signature,
            attempts: attempt + 1,
            stats: engine.stats(),
        });
    }
    Err(ThresholdMlDsaError::RejectionBudgetExhausted {
        attempts: DEFAULT_MAX_REJECTION_ATTEMPTS,
    })
}

/// A policy release for one signing session.
pub struct ThresholdPolicyGate<'a> {
    pub token: AuthorizedSignReleaseToken,
    pub expected_intent_digest: &'a [u8; 32],
    pub quorum: &'a [u16],
}

/// Policy-gated signing: the session identifier, message, context and quorum
/// must match an [`AuthorizedSignReleaseToken`] minted by the policy layer.
pub fn threshold_sign_mldsa_party_policy_gated<T: MpcTransport>(
    share: &mut ThresholdMlDsaSignerShare,
    gate: ThresholdPolicyGate<'_>,
    msg: &[u8],
    ctx: &[u8],
    entropy: &[u8; 32],
    burn: &mut dyn NonceBurnPersistence,
    net: &mut T,
) -> Result<ThresholdSignOutput, ThresholdMlDsaError> {
    let key_id = share.pack.policy_signing_key_id();
    if !gate.token.matches_signing(&key_id, msg, ctx, gate.quorum)
        || !ct_eq_bytes(gate.token.intent_digest(), gate.expected_intent_digest)
    {
        return Err(ThresholdMlDsaError::PolicyTokenDigestMismatch);
    }
    let session = ThresholdSignSession {
        session_id: *gate.token.session_id(),
        quorum: gate.quorum.to_vec(),
    };
    threshold_sign_mldsa_party(share, &session, msg, ctx, entropy, burn, net)
}

#[cfg(test)]
#[path = "threshold_mldsa_tests.rs"]
mod tests;
