//! `qsag-policy` Stateful Rolling-Window Velocity Guard, Canonical 128-Byte `TransactionIntent`
//! Codec, and `qsag-addr` Conjunctive Hybrid Signature Domain Framing Check.
//!
//! 1. `StatefulVelocityGuard` (non-`Clone`): maintains `(window_id, spent_units, cap_units,
//!    policy_pin, authority_pin, last_nonce)` with overflow-safe `u128` accumulation enforcing
//!    `sum(approved_amounts) <= cap_units` across arbitrary multi-turn spend traces.
//! 2. `encode_intent_128` / `decode_intent_128`: deterministic, zero-padding-bit canonical
//!    128-byte fixed-layout codec (`P0-10` / `P1-01`).
//! 3. `check_hybrid_domain_framing`: role-separated `QSAG.HYBRID.V2` framing check ensuring
//!    classical and post-quantum legs cannot cross-validate across roles or identity commitments.

use crate::keccak::Shake256Sponge;
use crate::tower::ct_eq_bytes32;

/// Magic 32-bit header word `"QSI1"` (`0x5153_4931`) for canonical 128-byte `TransactionIntent`.
pub const INTENT_V1_MAGIC: u32 = 0x5153_4931;

/// Conjunctive hybrid witness suite code `HybridEd25519MlDsa65` (`0x0501`).
pub const SUITE_HYBRID_ED25519_MLDSA65: u16 = 0x0501;

/// Conjunctive hybrid witness suite code `HybridSecp256k1SlhDsa` (`0x0502`).
pub const SUITE_HYBRID_SECP256K1_SLHDSA: u16 = 0x0502;

/// Maximum representable 128-bit rolling-window velocity counter (`2^128 - 1`).
pub const MAX_VELOCITY_U128: u128 = 0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF;

/// Explicit refusal reasons for `StatefulVelocityGuard`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PolicyAddrError {
    PolicyPinMismatch,
    AuthorityPinMismatch,
    WindowIdMismatch,
    NonMonotonicNonce,
    VelocityArithmeticOverflow,
    VelocityCapExceeded,
    InvalidWindowRotation,
}

/// Spend authorization request against a `StatefulVelocityGuard`.
#[derive(Clone, Copy)]
pub struct VelocitySpendRequest {
    pub window_id: u64,
    pub nonce: u64,
    pub amount_units: u128,
    pub policy_pin: [u8; 32],
    pub authority_pin: [u8; 32],
}

/// Non-`Clone` affine rolling-window velocity guard enforcing overflow-safe `spent_units <= cap_units`,
/// strict nonce monotonicity (`nonce > last_nonce`), and 256-bit policy + authority pin binding.
///
/// External callers cannot reset the authorization state.
/// ```compile_fail,E0616
/// use qsag_verified::StatefulVelocityGuard;
/// let mut guard = StatefulVelocityGuard::new_window(0, 100, [0; 32], [0; 32]);
/// guard.spent_units = 0;
/// ```
pub struct StatefulVelocityGuard {
    window_id: u64,
    spent_units: u128,
    cap_units: u128,
    policy_pin: [u8; 32],
    authority_pin: [u8; 32],
    last_nonce: u64,
}

impl StatefulVelocityGuard {
    /// Read-only state observation.
    pub const fn window_id(&self) -> u64 {
        self.window_id
    }

    /// Read-only state observation.
    pub const fn spent_units(&self) -> u128 {
        self.spent_units
    }

    /// Read-only state observation.
    pub const fn cap_units(&self) -> u128 {
        self.cap_units
    }

    /// Read-only state observation.
    pub const fn policy_pin(&self) -> [u8; 32] {
        self.policy_pin
    }

    /// Read-only state observation.
    pub const fn authority_pin(&self) -> [u8; 32] {
        self.authority_pin
    }

    /// Read-only state observation.
    pub const fn last_nonce(&self) -> u64 {
        self.last_nonce
    }

    /// Initialize a fresh rolling window at `spent_units = 0` and `last_nonce = 0`.
    #[inline]
    pub const fn new_window(
        window_id: u64,
        cap_units: u128,
        policy_pin: [u8; 32],
        authority_pin: [u8; 32],
    ) -> StatefulVelocityGuard {
        StatefulVelocityGuard {
            window_id,
            spent_units: 0,
            cap_units,
            policy_pin,
            authority_pin,
            last_nonce: 0,
        }
    }

    /// Authorize `req.amount_units` within the active window if and only if:
    /// - `policy_pin` and `authority_pin` match in constant time,
    /// - `req.window_id == self.window_id`,
    /// - `req.nonce > self.last_nonce`, and
    /// - `self.spent_units + req.amount_units` does not overflow `u128` and is `<= self.cap_units`.
    ///
    /// Rejected calls leave the guard state untouched.
    pub fn authorize_spend(
        self,
        req: VelocitySpendRequest,
    ) -> (StatefulVelocityGuard, Result<u128, PolicyAddrError>) {
        if !ct_eq_bytes32(&self.policy_pin, &req.policy_pin) {
            return (self, Err(PolicyAddrError::PolicyPinMismatch));
        }
        if !ct_eq_bytes32(&self.authority_pin, &req.authority_pin) {
            return (self, Err(PolicyAddrError::AuthorityPinMismatch));
        }
        if req.window_id != self.window_id {
            return (self, Err(PolicyAddrError::WindowIdMismatch));
        }
        if req.nonce <= self.last_nonce {
            return (self, Err(PolicyAddrError::NonMonotonicNonce));
        }
        if req.amount_units > MAX_VELOCITY_U128 - self.spent_units {
            return (self, Err(PolicyAddrError::VelocityArithmeticOverflow));
        }
        let new_spent = self.spent_units + req.amount_units;
        if new_spent > self.cap_units {
            return (self, Err(PolicyAddrError::VelocityCapExceeded));
        }
        let next = StatefulVelocityGuard {
            window_id: self.window_id,
            spent_units: new_spent,
            cap_units: self.cap_units,
            policy_pin: self.policy_pin,
            authority_pin: self.authority_pin,
            last_nonce: req.nonce,
        };
        (next, Ok(req.amount_units))
    }

    /// Advance strictly forward (`next_window_id > self.window_id`) to a fresh rolling window,
    /// resetting `spent_units = 0` while preserving monotonic `last_nonce` and pins.
    pub fn rotate_window(
        self,
        next_window_id: u64,
        req_policy_pin: [u8; 32],
        req_authority_pin: [u8; 32],
    ) -> (StatefulVelocityGuard, Result<(), PolicyAddrError>) {
        if !ct_eq_bytes32(&self.policy_pin, &req_policy_pin) {
            return (self, Err(PolicyAddrError::PolicyPinMismatch));
        }
        if !ct_eq_bytes32(&self.authority_pin, &req_authority_pin) {
            return (self, Err(PolicyAddrError::AuthorityPinMismatch));
        }
        if next_window_id <= self.window_id {
            return (self, Err(PolicyAddrError::InvalidWindowRotation));
        }
        let next = StatefulVelocityGuard {
            window_id: next_window_id,
            spent_units: 0,
            cap_units: self.cap_units,
            policy_pin: self.policy_pin,
            authority_pin: self.authority_pin,
            last_nonce: self.last_nonce,
        };
        (next, Ok(()))
    }
}

/// Canonical `qsag-addr` address format version (`V1 = 1`, `V2 = 2`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IntentAddressVersion {
    V1,
    V2,
}

impl IntentAddressVersion {
    #[inline]
    pub const fn to_u8(self) -> u8 {
        match self {
            Self::V1 => 1,
            Self::V2 => 2,
        }
    }

    #[inline]
    pub const fn from_u8(v: u8) -> Option<Self> {
        match v {
            1 => Some(Self::V1),
            2 => Some(Self::V2),
            _ => None,
        }
    }
}

/// Canonical `qsag-addr` key identity kind (`SingleKey = 1`, `ThresholdCommittee = 2`, `PolicyBound = 3`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IntentIdentityKind {
    SingleKey,
    ThresholdCommittee,
    PolicyBound,
}

impl IntentIdentityKind {
    #[inline]
    pub const fn to_u8(self) -> u8 {
        match self {
            Self::SingleKey => 1,
            Self::ThresholdCommittee => 2,
            Self::PolicyBound => 3,
        }
    }

    #[inline]
    pub const fn from_u8(v: u8) -> Option<Self> {
        match v {
            1 => Some(Self::SingleKey),
            2 => Some(Self::ThresholdCommittee),
            3 => Some(Self::PolicyBound),
            _ => None,
        }
    }
}

/// Canonical `qsag-addr` witness suite tag (`0x0101`, `0x0201`, `0x0302`, `0x0501`, `0x0502`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IntentSuiteTag {
    JortsPoseidon2,
    SlhDsaShake128f,
    ThresholdMlDsa65,
    HybridEd25519MlDsa65,
    HybridSecp256k1SlhDsa,
}

impl IntentSuiteTag {
    #[inline]
    pub const fn to_u16(self) -> u16 {
        match self {
            Self::JortsPoseidon2 => 0x0101,
            Self::SlhDsaShake128f => 0x0201,
            Self::ThresholdMlDsa65 => 0x0302,
            Self::HybridEd25519MlDsa65 => SUITE_HYBRID_ED25519_MLDSA65,
            Self::HybridSecp256k1SlhDsa => SUITE_HYBRID_SECP256K1_SLHDSA,
        }
    }

    #[inline]
    pub const fn from_u16(v: u16) -> Option<Self> {
        match v {
            0x0101 => Some(Self::JortsPoseidon2),
            0x0201 => Some(Self::SlhDsaShake128f),
            0x0302 => Some(Self::ThresholdMlDsa65),
            0x0501 => Some(Self::HybridEd25519MlDsa65),
            0x0502 => Some(Self::HybridSecp256k1SlhDsa),
            _ => None,
        }
    }
}

/// Canonical deterministic 128-byte `TransactionIntent` payload (`P0-10` / `P1-01`).
/// Every byte in `[0..128)` is canonically constrained with zero unvalidated padding bits:
/// - `bytes[0..4]`   : `INTENT_V1_MAGIC` (`0x5153_4931`, big-endian)
/// - `bytes[4..6]`   : `suite_tag` (`u16` big-endian, validated `IntentSuiteTag`)
/// - `bytes[6]`      : `address_version` (`u8`, validated `IntentAddressVersion`)
/// - `bytes[7]`      : `identity_kind` (`u8`, validated `IntentIdentityKind`)
/// - `bytes[8..16]`  : `chain_id` (`u64` big-endian)
/// - `bytes[16..24]` : `nonce` (`u64` big-endian)
/// - `bytes[24..32]` : `timestamp_secs` (`u64` big-endian)
/// - `bytes[32..48]` : `amount_units` (`u128` big-endian)
/// - `bytes[48..64]` : `rolling_window_spent` (`u128` big-endian)
/// - `bytes[64..96]` : `recipient_commitment` (`[u8; 32]`)
/// - `bytes[96..128]`: `payload_digest` (`[u8; 32]`)
#[derive(Clone, Copy)]
pub struct CanonicalIntent128 {
    pub suite_tag: IntentSuiteTag,
    pub address_version: IntentAddressVersion,
    pub identity_kind: IntentIdentityKind,
    pub chain_id: u64,
    pub nonce: u64,
    pub timestamp_secs: u64,
    pub amount_units: u128,
    pub rolling_window_spent: u128,
    pub recipient_commitment: [u8; 32],
    pub payload_digest: [u8; 32],
}

#[derive(Clone, Copy)]
struct IntentHeaderFields {
    suite_tag: IntentSuiteTag,
    address_version: IntentAddressVersion,
    identity_kind: IntentIdentityKind,
    chain_id: u64,
    nonce: u64,
    timestamp_secs: u64,
}

#[inline]
pub(crate) const fn be_u16_read(b0: u8, b1: u8) -> u16 {
    ((b0 as u16) << 8) | (b1 as u16)
}

#[inline]
pub(crate) const fn be_u32_read(b0: u8, b1: u8, b2: u8, b3: u8) -> u32 {
    ((b0 as u32) << 24) | ((b1 as u32) << 16) | ((b2 as u32) << 8) | (b3 as u32)
}

#[inline]
pub(crate) const fn be_u64_read(
    b0: u8,
    b1: u8,
    b2: u8,
    b3: u8,
    b4: u8,
    b5: u8,
    b6: u8,
    b7: u8,
) -> u64 {
    ((b0 as u64) << 56)
        | ((b1 as u64) << 48)
        | ((b2 as u64) << 40)
        | ((b3 as u64) << 32)
        | ((b4 as u64) << 24)
        | ((b5 as u64) << 16)
        | ((b6 as u64) << 8)
        | (b7 as u64)
}

#[inline]
pub(crate) const fn pack_u128_from_u64_be(hi: u64, lo: u64) -> u128 {
    ((hi as u128) << 64) | (lo as u128)
}

#[inline]
pub(crate) const fn unpack_u128_hi(v: u128) -> u64 {
    ((v >> 64) & 0xFFFF_FFFF_FFFF_FFFF) as u64
}

#[inline]
pub(crate) const fn unpack_u128_lo(v: u128) -> u64 {
    (v & 0xFFFF_FFFF_FFFF_FFFF) as u64
}

pub(crate) const fn encode_intent_header32(intent: &CanonicalIntent128) -> [u8; 32] {
    let m = INTENT_V1_MAGIC;
    let st = intent.suite_tag.to_u16();
    let av = intent.address_version.to_u8();
    let ik = intent.identity_kind.to_u8();
    let cid = intent.chain_id;
    let nc = intent.nonce;
    let ts = intent.timestamp_secs;
    [
        ((m >> 24) & 0xFF) as u8,
        ((m >> 16) & 0xFF) as u8,
        ((m >> 8) & 0xFF) as u8,
        (m & 0xFF) as u8,
        ((st >> 8) & 0xFF) as u8,
        (st & 0xFF) as u8,
        av,
        ik,
        ((cid >> 56) & 0xFF) as u8,
        ((cid >> 48) & 0xFF) as u8,
        ((cid >> 40) & 0xFF) as u8,
        ((cid >> 32) & 0xFF) as u8,
        ((cid >> 24) & 0xFF) as u8,
        ((cid >> 16) & 0xFF) as u8,
        ((cid >> 8) & 0xFF) as u8,
        (cid & 0xFF) as u8,
        ((nc >> 56) & 0xFF) as u8,
        ((nc >> 48) & 0xFF) as u8,
        ((nc >> 40) & 0xFF) as u8,
        ((nc >> 32) & 0xFF) as u8,
        ((nc >> 24) & 0xFF) as u8,
        ((nc >> 16) & 0xFF) as u8,
        ((nc >> 8) & 0xFF) as u8,
        (nc & 0xFF) as u8,
        ((ts >> 56) & 0xFF) as u8,
        ((ts >> 48) & 0xFF) as u8,
        ((ts >> 40) & 0xFF) as u8,
        ((ts >> 32) & 0xFF) as u8,
        ((ts >> 24) & 0xFF) as u8,
        ((ts >> 16) & 0xFF) as u8,
        ((ts >> 8) & 0xFF) as u8,
        (ts & 0xFF) as u8,
    ]
}

const fn decode_intent_header32(b: &[u8; 32]) -> Option<IntentHeaderFields> {
    let magic = be_u32_read(b[0], b[1], b[2], b[3]);
    if magic != INTENT_V1_MAGIC {
        return None;
    }
    let st_raw = be_u16_read(b[4], b[5]);
    let suite_tag = match IntentSuiteTag::from_u16(st_raw) {
        Some(t) => t,
        None => return None,
    };
    let address_version = match IntentAddressVersion::from_u8(b[6]) {
        Some(v) => v,
        None => return None,
    };
    let identity_kind = match IntentIdentityKind::from_u8(b[7]) {
        Some(k) => k,
        None => return None,
    };
    let chain_id = be_u64_read(b[8], b[9], b[10], b[11], b[12], b[13], b[14], b[15]);
    let nonce = be_u64_read(b[16], b[17], b[18], b[19], b[20], b[21], b[22], b[23]);
    let timestamp_secs = be_u64_read(b[24], b[25], b[26], b[27], b[28], b[29], b[30], b[31]);
    Some(IntentHeaderFields {
        suite_tag,
        address_version,
        identity_kind,
        chain_id,
        nonce,
        timestamp_secs,
    })
}

pub(crate) const fn encode_intent_amounts32(amount_units: u128, spent_units: u128) -> [u8; 32] {
    let a_hi = unpack_u128_hi(amount_units);
    let a_lo = unpack_u128_lo(amount_units);
    let s_hi = unpack_u128_hi(spent_units);
    let s_lo = unpack_u128_lo(spent_units);
    [
        ((a_hi >> 56) & 0xFF) as u8,
        ((a_hi >> 48) & 0xFF) as u8,
        ((a_hi >> 40) & 0xFF) as u8,
        ((a_hi >> 32) & 0xFF) as u8,
        ((a_hi >> 24) & 0xFF) as u8,
        ((a_hi >> 16) & 0xFF) as u8,
        ((a_hi >> 8) & 0xFF) as u8,
        (a_hi & 0xFF) as u8,
        ((a_lo >> 56) & 0xFF) as u8,
        ((a_lo >> 48) & 0xFF) as u8,
        ((a_lo >> 40) & 0xFF) as u8,
        ((a_lo >> 32) & 0xFF) as u8,
        ((a_lo >> 24) & 0xFF) as u8,
        ((a_lo >> 16) & 0xFF) as u8,
        ((a_lo >> 8) & 0xFF) as u8,
        (a_lo & 0xFF) as u8,
        ((s_hi >> 56) & 0xFF) as u8,
        ((s_hi >> 48) & 0xFF) as u8,
        ((s_hi >> 40) & 0xFF) as u8,
        ((s_hi >> 32) & 0xFF) as u8,
        ((s_hi >> 24) & 0xFF) as u8,
        ((s_hi >> 16) & 0xFF) as u8,
        ((s_hi >> 8) & 0xFF) as u8,
        (s_hi & 0xFF) as u8,
        ((s_lo >> 56) & 0xFF) as u8,
        ((s_lo >> 48) & 0xFF) as u8,
        ((s_lo >> 40) & 0xFF) as u8,
        ((s_lo >> 32) & 0xFF) as u8,
        ((s_lo >> 24) & 0xFF) as u8,
        ((s_lo >> 16) & 0xFF) as u8,
        ((s_lo >> 8) & 0xFF) as u8,
        (s_lo & 0xFF) as u8,
    ]
}

pub(crate) const fn decode_intent_amounts32(b: &[u8; 32]) -> (u128, u128) {
    let a_hi = be_u64_read(b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]);
    let a_lo = be_u64_read(b[8], b[9], b[10], b[11], b[12], b[13], b[14], b[15]);
    let s_hi = be_u64_read(b[16], b[17], b[18], b[19], b[20], b[21], b[22], b[23]);
    let s_lo = be_u64_read(b[24], b[25], b[26], b[27], b[28], b[29], b[30], b[31]);
    (
        pack_u128_from_u64_be(a_hi, a_lo),
        pack_u128_from_u64_be(s_hi, s_lo),
    )
}

pub(crate) const fn unpack_block32(buf: &[u8; 128], base: usize) -> [u8; 32] {
    [
        buf[base],
        buf[base + 1],
        buf[base + 2],
        buf[base + 3],
        buf[base + 4],
        buf[base + 5],
        buf[base + 6],
        buf[base + 7],
        buf[base + 8],
        buf[base + 9],
        buf[base + 10],
        buf[base + 11],
        buf[base + 12],
        buf[base + 13],
        buf[base + 14],
        buf[base + 15],
        buf[base + 16],
        buf[base + 17],
        buf[base + 18],
        buf[base + 19],
        buf[base + 20],
        buf[base + 21],
        buf[base + 22],
        buf[base + 23],
        buf[base + 24],
        buf[base + 25],
        buf[base + 26],
        buf[base + 27],
        buf[base + 28],
        buf[base + 29],
        buf[base + 30],
        buf[base + 31],
    ]
}

pub(crate) const fn pack_4x32(
    b0: &[u8; 32],
    b1: &[u8; 32],
    b2: &[u8; 32],
    b3: &[u8; 32],
) -> [u8; 128] {
    [
        b0[0], b0[1], b0[2], b0[3], b0[4], b0[5], b0[6], b0[7], b0[8], b0[9], b0[10], b0[11],
        b0[12], b0[13], b0[14], b0[15], b0[16], b0[17], b0[18], b0[19], b0[20], b0[21], b0[22],
        b0[23], b0[24], b0[25], b0[26], b0[27], b0[28], b0[29], b0[30], b0[31], b1[0], b1[1],
        b1[2], b1[3], b1[4], b1[5], b1[6], b1[7], b1[8], b1[9], b1[10], b1[11], b1[12], b1[13],
        b1[14], b1[15], b1[16], b1[17], b1[18], b1[19], b1[20], b1[21], b1[22], b1[23], b1[24],
        b1[25], b1[26], b1[27], b1[28], b1[29], b1[30], b1[31], b2[0], b2[1], b2[2], b2[3], b2[4],
        b2[5], b2[6], b2[7], b2[8], b2[9], b2[10], b2[11], b2[12], b2[13], b2[14], b2[15], b2[16],
        b2[17], b2[18], b2[19], b2[20], b2[21], b2[22], b2[23], b2[24], b2[25], b2[26], b2[27],
        b2[28], b2[29], b2[30], b2[31], b3[0], b3[1], b3[2], b3[3], b3[4], b3[5], b3[6], b3[7],
        b3[8], b3[9], b3[10], b3[11], b3[12], b3[13], b3[14], b3[15], b3[16], b3[17], b3[18],
        b3[19], b3[20], b3[21], b3[22], b3[23], b3[24], b3[25], b3[26], b3[27], b3[28], b3[29],
        b3[30], b3[31],
    ]
}

/// Encode `CanonicalIntent128` deterministically into a fixed 128-byte wire frame.
pub const fn encode_intent_128(intent: &CanonicalIntent128) -> [u8; 128] {
    let b0 = encode_intent_header32(intent);
    let b1 = encode_intent_amounts32(intent.amount_units, intent.rolling_window_spent);
    pack_4x32(
        &b0,
        &b1,
        &intent.recipient_commitment,
        &intent.payload_digest,
    )
}

/// Decode and validate a 128-byte canonical `TransactionIntent` frame (`None` on any non-canonical tag/magic).
pub const fn decode_intent_128(bytes: &[u8; 128]) -> Option<CanonicalIntent128> {
    let b0 = unpack_block32(bytes, 0);
    let b1 = unpack_block32(bytes, 32);
    let recipient_commitment = unpack_block32(bytes, 64);
    let payload_digest = unpack_block32(bytes, 96);
    let hdr = match decode_intent_header32(&b0) {
        Some(h) => h,
        None => return None,
    };
    let (amount_units, rolling_window_spent) = decode_intent_amounts32(&b1);
    Some(CanonicalIntent128 {
        suite_tag: hdr.suite_tag,
        address_version: hdr.address_version,
        identity_kind: hdr.identity_kind,
        chain_id: hdr.chain_id,
        nonce: hdr.nonce,
        timestamp_secs: hdr.timestamp_secs,
        amount_units,
        rolling_window_spent,
        recipient_commitment,
        payload_digest,
    })
}

/// Role separator for `qsag-addr` conjunctive hybrid transcripts (`Classical = 0x01`, `PostQuantum = 0x02`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HybridRoleTag {
    Classical,
    PostQuantum,
}

impl HybridRoleTag {
    #[inline]
    pub const fn to_u8(self) -> u8 {
        match self {
            Self::Classical => 0x01,
            Self::PostQuantum => 0x02,
        }
    }
}

/// Verify `QSAG.HYBRID.V2` 14-byte magic, conjunctive hybrid suite tag (`0x0501` or `0x0502`),
/// strict `Classical` vs `PostQuantum` role separation, and 32-byte `id_commit` equality.
pub fn check_hybrid_domain_framing(
    magic14: &[u8; 14],
    wire_role_byte: u8,
    expected_role: HybridRoleTag,
    suite_code: u16,
    expected_id_commit: &[u8; 32],
    wire_id_commit: &[u8; 32],
) -> bool {
    let diff: u8 = (magic14[0] ^ 0x51)
        | (magic14[1] ^ 0x53)
        | (magic14[2] ^ 0x41)
        | (magic14[3] ^ 0x47)
        | (magic14[4] ^ 0x2E)
        | (magic14[5] ^ 0x48)
        | (magic14[6] ^ 0x59)
        | (magic14[7] ^ 0x42)
        | (magic14[8] ^ 0x52)
        | (magic14[9] ^ 0x49)
        | (magic14[10] ^ 0x44)
        | (magic14[11] ^ 0x2E)
        | (magic14[12] ^ 0x56)
        | (magic14[13] ^ 0x32);
    if diff != 0 {
        return false;
    }
    let suite_valid = if suite_code == SUITE_HYBRID_ED25519_MLDSA65 {
        true
    } else if suite_code == SUITE_HYBRID_SECP256K1_SLHDSA {
        true
    } else {
        false
    };
    if !suite_valid {
        return false;
    }
    if wire_role_byte != expected_role.to_u8() {
        return false;
    }
    ct_eq_bytes32(expected_id_commit, wire_id_commit)
}

/// Compute a role-separated `QSAG.HYBRID.V2` SHAKE256 signing transcript digest (`None` if non-hybrid suite).
pub fn derive_hybrid_transcript_digest(
    role: HybridRoleTag,
    suite_code: u16,
    id_commit: &[u8; 32],
    pk_classical_digest: &[u8; 32],
    pk_pq_digest: &[u8; 32],
    message: &[u8],
) -> Option<[u8; 32]> {
    // Canonical address-envelope suites: secp256k1/ML-DSA-44 and Ed25519/ML-DSA-65.
    let algorithm = if suite_code == 0x0501 { 1u8 }
        else if suite_code == 0x0502 { 2u8 }
        else { return None; };
    let magic: [u8; 14] = *b"QSAG.HYBRID.V2";
    let header: [u8; 7] = [role.to_u8(), (suite_code >> 8) as u8, suite_code as u8,
        0, algorithm, 1, algorithm];
    let len = message.len() as u64;
    let length: [u8; 8] = [(len >> 56) as u8, (len >> 48) as u8,
        (len >> 40) as u8, (len >> 32) as u8, (len >> 24) as u8,
        (len >> 16) as u8, (len >> 8) as u8, len as u8];
    let mut sp = Shake256Sponge::new_shake256();
    sp.absorb(&magic);
    sp.absorb(&header);
    sp.absorb(id_commit);
    sp.absorb(pk_classical_digest);
    sp.absorb(pk_pq_digest);
    sp.absorb(&length);
    sp.absorb(message);
    let mut out = [0u8; 32];
    sp.squeeze(&mut out);
    Some(out)
}

/// Checked cumulative velocity shared by production admission and durable guards.
pub const fn checked_velocity_spend(prior: u128, amount: u128, cap: u128) -> Option<u128> {
    if amount > u128::MAX - prior {
        return None;
    }
    let total = prior + amount;
    if total > cap { None } else { Some(total) }
}
