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
//! 3. `z = y + c*s1` and `w - c*s2` exist only as shares. One joint bit
//!    decides both `||z|| < gamma1 - beta` and
//!    `||LowBits(w - c*s2)|| < gamma2 - beta` with `HighBits(w - c*s2) = w1`
//!    (tested as `(w - c*s2 - w1*2*gamma2) mod+- q` lying in the open
//!    interval, which is equivalent). Every multiplication behind that bit
//!    is verified before it is opened; each number of failing coefficients is
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
use qsag_verified::{MlDsaBarrierChecks, MlDsaReleaseGate};

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
    let secret = coefficient.gather(&accepted);

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
            holders: structure.subsets[subset],
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
/// With `x = w + gamma2 - 1 mod q` and `alpha = 2*gamma2 = 2^11 * 93`,
/// `HighBits(w) = floor(x / alpha)`, except that the single value
/// `x = q - 1` (quotient 44) maps to 0.
fn high_bits_circuit<T: MpcTransport>(
    engine: &mut Engine<'_, T>,
    opened: &[u32],
    r: &[Sh],
) -> Result<Sh, MpcError> {
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

    // x = d + q * wrap modulo 2^23, with q = 2^23 - 2^13 + 1. Only bits
    // 11..23 of x are needed. Bit 0 and the zero bits 1..13 of q ripple a
    // carry; the ten one-bits act as a decrement by wrap - carry.
    let mut carries = Vec::with_capacity(13);
    carries.push(engine.mul(&d[0], &wrap)?);
    for i in 1..13 {
        let next = engine.mul(&d[i], &carries[i - 1])?;
        carries.push(next);
    }
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
    const DIVISOR_BITS: [u32; 8] = [1, 0, 1, 1, 1, 0, 1, 0];
    let mut remainder: Vec<Sh> = u[6..12].to_vec();
    remainder.push(engine.zeros(len)?);
    let mut quotient: Vec<Sh> = Vec::with_capacity(6);
    for i in (0..6).rev() {
        let mut a: Vec<Sh> = Vec::with_capacity(8);
        a.push(u[i].clone());
        a.append(&mut remainder);
        let mut borrow: Option<Sh> = None;
        let mut difference: Vec<Sh> = Vec::with_capacity(8);
        for (a_bit, &k_bit) in a.iter().zip(&DIVISOR_BITS) {
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
    let mut value = is_44.scale(MLDSA_Q - 44);
    for (index, bit) in quotient.iter().enumerate() {
        value = value.add(&bit.scale(1 << (5 - index)));
    }
    Ok(value)
}

/// First opens only the joint acceptance bit. After acceptance, checks the
/// three predicates independently before releasing their witnesses. A rejected
/// attempt never reveals which predicate failed. The masked coefficient openings
/// are shared by the circuits; no unmasked coefficient is released.
fn rejection_verdict<T: MpcTransport>(
    engine: &mut Engine<'_, T>,
    (z, z_bound): (&Sh, u32),
    (low, low_bound): (&Sh, u32),
    masks: &Sh,
    planes: &[Sh],
    high_bound: u32,
) -> Result<Option<(bool, bool, bool)>, MpcError> {
    let z_len = z.len();
    let low_len = low.len();
    let shifted = Sh::concat(&[
        &z.add(&engine.public_const(z_bound - 1, z_len)?),
        &low.add(&engine.public_const(low_bound - 1, low_len)?),
    ]);
    let opened = engine.open(&[&shifted.add(masks)])?.remove(0);
    let mut widths = vec![2 * z_bound - 1; z_len];
    widths.extend_from_slice(&vec![2 * low_bound - 1; low_len]);
    let inside = masked_range_test(engine, &opened, &widths, planes)?;
    let outside = engine.public_const(1, z_len + low_len)?.sub(&inside);
    let z_failures = outside.slice(0, z_len).sum();
    let low_failures = outside.slice(z_len, low_len).sum();
    // A wider residual interval checks the HighBits relation separately from
    // the stricter rejection norm. Shifting a masked public value by a public
    // constant preserves its mask and does not disclose the residual.
    let high_opened: Vec<u32> = opened[z_len..].iter()
        .map(|&v| fq_add(v, high_bound - low_bound)).collect();
    let high_planes: Vec<Sh> = planes.iter().map(|p| p.slice(z_len, low_len)).collect();
    let high_inside = masked_range_test(engine, &high_opened, &vec![2 * high_bound - 1; low_len], &high_planes)?;
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

/// Owns the entire pending response while the verified affine gate holds its
/// session capability. A rejected gate drops (and zeroizes) the response; only
/// successful consumption returns shares that the caller can open.
struct PendingResponse {
    response: Sh,
    gate: MlDsaReleaseGate,
}

impl PendingResponse {
    fn new(response: Sh, context: [u8; 32], attempt: u32) -> Self {
        let digest = Self::digest(&response, &context, attempt);
        Self {
            response,
            gate: MlDsaReleaseGate::new_sealed(context, attempt, digest),
        }
    }

    fn digest(response: &Sh, context: &[u8; 32], attempt: u32) -> [u8; 32] {
        let mut sponge = Shake256::new();
        sponge.absorb(b"QSAG.MLDSA.PENDING_RESPONSE.V1");
        sponge.absorb(context);
        sponge.absorb(&attempt.to_be_bytes());
        sponge.absorb(&(response.c.len() as u64).to_be_bytes());
        for component in &response.c {
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

    fn release(self, checks: MlDsaBarrierChecks) -> Result<Sh, ThresholdMlDsaError> {
        let (_, released) = self.gate.try_release_z_share(checks);
        let released = released.map_err(|_| ThresholdMlDsaError::ProtocolInvariantViolated)?;
        let expected = Self::digest(&self.response, &checks.req_session_id, checks.req_attempt);
        if !ct_eq_bytes(&released, &expected) {
            return Err(ThresholdMlDsaError::ProtocolInvariantViolated);
        }
        Ok(self.response)
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
        let mut present = 0u32;
        for (position, id) in quorum.iter().enumerate() {
            let global = share
                .pack
                .party_ids
                .iter()
                .position(|p| p == id)
                .expect("validated quorum");
            if (subset.holders >> global) & 1 == 1 {
                present |= 1 << position;
            }
        }
        let target = structure
            .subsets
            .iter()
            .position(|&mask| mask & present == mask)
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
    let y_bits = (gamma1.trailing_zeros() + 1) as usize;
    let z_len = params.ell * MLDSA_N;
    let w_len = params.k * MLDSA_N;
    let masks_needed = 2 * w_len + z_len;
    let masks = masks_needed + SPARE_MASKS;

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
        let (z_idx, low_idx) = rest.split_at(z_len);

        let mut w = engine.zeros(w_len)?;
        for i in 0..comps {
            let y_hat = ntt_all(to_polys(&y.c[i]));
            w.c[i] = flatten(&inv_ntt_all(mat_vec_mul_ntt(&a_hat, &y_hat)));
        }
        let shifted = w.add(&engine.public_const(gamma2 - 1, w_len)?);
        let opened_w = engine.open(&[&shifted.add(&mask_values.gather(high_idx))])?;

        // Phase 2: HighBits(w).
        engine.set_phase(PHASE_SIGN_HIGH_BITS);
        let high_planes: Vec<Sh> = planes.iter().map(|plane| plane.gather(high_idx)).collect();
        let w1_share = high_bits_circuit(&mut engine, &opened_w[0], &high_planes)?;
        let w1 = engine.open(&[&w1_share])?.remove(0);
        if w1.iter().any(|&v| v >= 44) {
            return Err(ThresholdMlDsaError::ProtocolInvariantViolated);
        }
        let w1_polys = to_polys(&w1);
        let mut c_tilde = vec![0u8; params.c_tilde_bytes];
        let mut xof = Shake256::new();
        xof.absorb(&mu);
        xof.absorb(&w1_encode(&params, &w1_polys));
        xof.finalize(0x1F);
        xof.squeeze(&mut c_tilde);
        let mut c_hat = sample_in_ball(&c_tilde, params.tau);
        c_hat.ntt();
        let ct0 = to_polys(&challenge_times(&c_hat, &t0_hat));
        if ct0.iter().any(|poly| poly.inf_norm() >= gamma2) {
            continue;
        }

        // Phase 3: the joint rejection bit.
        engine.set_phase(PHASE_SIGN_REJECTION);
        let mut z = engine.zeros(z_len)?;
        let mut low = engine.zeros(w_len)?;
        for i in 0..comps {
            let cs1 = crate::secret_buffer::SecretBuffer(challenge_times(&c_hat, &key.s1_hat[i]));
            let cs2 = crate::secret_buffer::SecretBuffer(challenge_times(&c_hat, &key.s2_hat[i]));
            z.c[i] = y.c[i]
                .iter()
                .zip(cs1.iter())
                .map(|(&a, &b)| fq_add(a, b))
                .collect();
            low.c[i] = w.c[i]
                .iter()
                .zip(cs2.iter())
                .map(|(&a, &b)| fq_sub(a, b))
                .collect();
        }
        let w1_alpha: Vec<u32> = w1.iter().map(|&v| v * alpha).collect();
        let low = low.sub(&engine.public(&w1_alpha)?);
        let z_bound = gamma1 - params.beta;
        let low_bound = gamma2 - params.beta;
        let test_idx: Vec<usize> = z_idx.iter().chain(low_idx).copied().collect();
        let test_planes: Vec<Sh> = planes.iter().map(|plane| plane.gather(&test_idx)).collect();
        let pending = PendingResponse::new(z, context, attempt);
        let checks = rejection_verdict(
            &mut engine,
            (&pending.response, z_bound),
            (&low, low_bound),
            &mask_values.gather(&test_idx),
            &test_planes,
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

        // Phase 4: release z.
        engine.set_phase(PHASE_SIGN_RELEASE);
        let z_public = to_polys(&engine.open(&[&z])?[0]);
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
        if !consistent {
            return Err(ThresholdMlDsaError::ProtocolInvariantViolated);
        }
        if weight > params.omega {
            continue;
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
