//! Actively secure outer MPC for general custodian quorums.
//!
//! The selected quorum runs SPDZ over additive shares. Every shared wire
//! carries an information-theoretic MAC under a global key that no proper
//! subset of the quorum knows:
//!
//! * a Boolean wire is one 64-lane word `x` with the MAC `Δ · x(X)` in
//!   `GF(2)[X]/(X^128 + X^7 + X^2 + X + 1)`, where `x(X)` reads the 64 lanes as
//!   the coefficients of a polynomial of degree below 64;
//! * a prime-field wire is one field element per lane with the MAC `α · v`
//!   (two independent keys over Goldilocks).
//!
//! Multiplications use Beaver triples, conversions use doubly authenticated
//! bits, and inputs use authenticated random words; all of it comes from
//! preprocessing that is independent of the witness (`threshold_prep`).
//! Values opened inside the protocol are only *partially* opened: their MAC
//! shares are queued, and the queue is settled by a multiplicatively blinded
//! commit-then-open batch MAC check ([`SpdzEngine::check`]) before any output
//! opening is sent and again before an opened output is returned to the caller.
//! Every local MAC residual `d_j` is multiplied via active KOS15 sender-residual
//! OLE by a fresh joint randomizer `R = Σ r_i` (`w = (Σ r_i)(Σ d_j)`), so an
//! abort reveals only uniform `R · D` and leaks zero bits of any MAC key share.
//! A failed check, a malformed message, an inconsistent broadcast or exhausted
//! preprocessing poisons the engine and atomically wipes all ceremony MAC key
//! shares across concurrent batch workers.
//!
//! Soundness per check: a party that sends a wrong share of any opened value
//! passes with probability below `2^-253` across Boolean (`GF(2^128)`, two
//! independent passes), Goldilocks (`GF(p^2)`, two independent passes), and all
//! large prime fields (`Secp256k1`, `Ed25519`, `Pallas`, `BLS12-381`). Privacy
//! holds against any strict subset of the quorum (and, for Shamir custody,
//! fewer than `t` custodians overall). Abort is not identifiable and not fair.
use crate::{
    circuit::{Domain, ONE, Value, ZERO, lift4},
    outer_mpc::{Core, Envelope, Error, FieldWord, Gadgets, ShareBit, Transport, Word},
    secret::{Secret, SecretVec, Wipe},
};
use alloc::{vec, vec::Vec};
use qsag_accel::{
    ct::{ct_eq_bytes_mask, ct_zeroize_bytes, ct_zeroize_u64s},
    gf2_128::gf2_128_mul,
    goldilocks::{GOLDILOCKS_PRIME, gl_add, gl_mul, gl_sub},
    keccak::{Shake256, cshake256_framed_32, reduce_192_mod_p},
};
use qsag_asm::{GFNI_MAT_POLY_TO_T3, GFNI_MAT_T3_TO_POLY, gf256_shamir_mul};
use qsag_core::field::tower::{TowerGf256, lagrange_weights_zero_gf256};

#[inline]
const fn apply_gfni_mat_ct(x: u8, matrix_qword: u64) -> u8 {
    let mut out = 0u8;
    let mut i = 0u32;
    while i < 8 {
        let row_byte = ((matrix_qword >> (8 * (7 - i))) & 0xFF) as u8;
        let mut p = x & row_byte;
        p ^= p >> 4;
        p ^= p >> 2;
        p = (p ^ (p >> 1)) & 1;
        out |= p << i;
        i += 1;
    }
    out
}

/// Lossless constant-time field isomorphism $\Phi^{-1} : \mathcal{T}_3 \to \mathbb{F}_2[z]/(z^8+z^4+z^3+z+1)$ (`0x11b`).
#[inline]
pub const fn t3_to_poly0x11b_byte_ct(x: u8) -> u8 {
    apply_gfni_mat_ct(x, GFNI_MAT_T3_TO_POLY)
}

/// Lossless constant-time field isomorphism $\Phi : \mathbb{F}_2[z]/(z^8+z^4+z^3+z+1) \to \mathcal{T}_3$ (`TowerGf256`).
#[inline]
pub const fn poly0x11b_to_t3_byte_ct(x: u8) -> u8 {
    apply_gfni_mat_ct(x, GFNI_MAT_POLY_TO_T3)
}

/// Convert a 32-byte share from Wiedemann tower $\mathcal{T}_3$ (`TowerGf256`) to AES `0x11b` polynomial basis in constant time.
#[inline]
pub fn t3_to_poly0x11b_bytes32_ct(share: &[u8; 32]) -> [u8; 32] {
    share.map(t3_to_poly0x11b_byte_ct)
}

/// Convert a 32-byte share from AES `0x11b` polynomial basis to Wiedemann tower $\mathcal{T}_3$ (`TowerGf256`) in constant time.
#[inline]
pub fn poly0x11b_to_t3_bytes32_ct(share: &[u8; 32]) -> [u8; 32] {
    share.map(poly0x11b_to_t3_byte_ct)
}

/// Immutable roster and ordered active quorum. Party identities are zero based;
/// Shamir evaluation points are `TowerGf256((party + 1) as u8)` in the canonical
/// Wiedemann binary tower $\mathcal{T}_3 = \mathbb{F}_{2^8}$ (`qsag-core` / `qsag-quorum`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ThresholdConfig {
    threshold: usize,
    parties: usize,
    quorum: Vec<usize>,
}
impl ThresholdConfig {
    pub fn new(threshold: usize, parties: usize, quorum: Vec<usize>) -> Result<Self, Error> {
        if !(2..=64).contains(&parties)
            || !(2..=parties).contains(&threshold)
            || quorum.len() < threshold
            || quorum.len() > parties
            || quorum.iter().any(|&p| p >= parties)
            || quorum.windows(2).any(|w| w[0] >= w[1])
        {
            return Err(Error::InvalidConfiguration);
        }
        Ok(Self {
            threshold,
            parties,
            quorum,
        })
    }
    pub fn threshold(&self) -> usize {
        self.threshold
    }
    pub fn parties(&self) -> usize {
        self.parties
    }
    pub fn quorum(&self) -> &[usize] {
        &self.quorum
    }
    pub(crate) fn binding(&self) -> Vec<u8> {
        let mut b = vec![self.threshold as u8, self.parties as u8];
        b.extend(self.quorum.iter().map(|&p| p as u8));
        b
    }
    /// Convert a bytewise degree-`(t - 1)` `TowerGf256` ($\mathcal{T}_3$) Shamir share
    /// evaluated at `TowerGf256((party + 1) as u8)` to its additive XOR contribution,
    /// without reconstructing any byte of the witness locally.
    pub fn shamir_contribution(&self, party: usize, share: &[u8; 32]) -> Result<[u8; 32], Error> {
        let pos = self
            .quorum
            .iter()
            .position(|&p| p == party)
            .ok_or(Error::InvalidConfiguration)?;
        let pts: Vec<TowerGf256> = self
            .quorum
            .iter()
            .map(|&p| TowerGf256((p + 1) as u8))
            .collect();
        let weights = lagrange_weights_zero_gf256(&pts).ok_or(Error::InvalidConfiguration)?;
        let weight_vec = [weights[pos].0; 32];
        let mut out = [0u8; 32];
        gf256_shamir_mul(&mut out, share, &weight_vec);
        Ok(out)
    }

    /// Convert a legacy AES-`0x11b` polynomial-basis Shamir share evaluated at
    /// `(party + 1)` in $\mathbb{F}_2[z]/(z^8+z^4+z^3+z+1)$ into its additive XOR
    /// contribution via the lossless `GFNI_MAT_POLY_TO_T3` / `GFNI_MAT_T3_TO_POLY`
    /// field isomorphism onto `TowerGf256`.
    pub fn shamir_contribution_poly0x11b(
        &self,
        party: usize,
        poly_share: &[u8; 32],
    ) -> Result<[u8; 32], Error> {
        let pos = self
            .quorum
            .iter()
            .position(|&p| p == party)
            .ok_or(Error::InvalidConfiguration)?;
        let pts: Vec<TowerGf256> = self
            .quorum
            .iter()
            .map(|&p| TowerGf256(poly0x11b_to_t3_byte_ct((p + 1) as u8)))
            .collect();
        let weights = lagrange_weights_zero_gf256(&pts).ok_or(Error::InvalidConfiguration)?;
        let mut t3_share = poly0x11b_to_t3_bytes32_ct(poly_share);
        let mut scaled_t3 = [0u8; 32];
        gf256_shamir_mul(&mut scaled_t3, &t3_share, &[weights[pos].0; 32]);
        ct_zeroize_bytes(&mut t3_share);
        let out = t3_to_poly0x11b_bytes32_ct(&scaled_t3);
        ct_zeroize_bytes(&mut scaled_t3);
        Ok(out)
    }
}

/// Prime field of a preprocessing request.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ThresholdField {
    Goldilocks,
    Secp256k1,
    Ed25519,
    Pallas,
    Bls12_381,
}
impl ThresholdField {
    pub const ALL: [Self; 5] = [
        Self::Goldilocks,
        Self::Secp256k1,
        Self::Ed25519,
        Self::Pallas,
        Self::Bls12_381,
    ];
    pub(crate) fn domain(self) -> Domain {
        match self {
            Self::Goldilocks => Domain::Gold,
            Self::Secp256k1 => Domain::Secp,
            Self::Ed25519 => Domain::Ed,
            Self::Pallas => Domain::PallasFp,
            Self::Bls12_381 => Domain::BlsFp,
        }
    }
    pub(crate) fn from_domain(d: Domain) -> Self {
        match d {
            Domain::Gold => Self::Goldilocks,
            Domain::Secp => Self::Secp256k1,
            Domain::Ed => Self::Ed25519,
            Domain::PallasFp => Self::Pallas,
            Domain::BlsFp => Self::Bls12_381,
            Domain::Bit => unreachable!("Boolean wires are not field wires"),
        }
    }
    pub(crate) fn index(self) -> usize {
        self as usize
    }
    /// Number of bits in the binary encoding of a field element.
    pub fn width(self) -> usize {
        self.domain().width()
    }
}

// ============================================================================
// MAC arithmetic
// ============================================================================

/// Multiply by `X` in `GF(2)[X]/(X^128 + X^7 + X^2 + X + 1)`.
#[inline(always)]
const fn mul_x(a: u128) -> u128 {
    (a << 1) ^ (0x87 & 0u128.wrapping_sub(a >> 127))
}

/// `sum_k lanes_k · X^k · macs[k]`: the word MAC of the lanes selected by
/// `lanes`, from per-lane MAC shares.
#[inline]
pub(crate) fn pack_macs(macs: &[u128; 64], lanes: u64) -> u128 {
    let mut acc = 0u128;
    for k in (0..64).rev() {
        acc = mul_x(acc) ^ (macs[k] & 0u128.wrapping_sub(((lanes >> k) & 1) as u128));
    }
    acc
}

/// MAC arithmetic of a field. Goldilocks MACs are pairs under two keys held
/// in limbs 0 and 1; the larger fields use one key and the plain field law.
#[inline(always)]
pub(crate) fn mac_add(d: Domain, a: Value, b: Value) -> Value {
    if d == Domain::Gold {
        [gl_add(a[0], b[0]), gl_add(a[1], b[1]), 0, 0, 0, 0]
    } else {
        d.add(a, b)
    }
}
#[inline(always)]
pub(crate) fn mac_sub(d: Domain, a: Value, b: Value) -> Value {
    if d == Domain::Gold {
        [gl_sub(a[0], b[0]), gl_sub(a[1], b[1]), 0, 0, 0, 0]
    } else {
        d.sub(a, b)
    }
}
/// MAC (or MAC key) times a field element.
#[inline(always)]
pub(crate) fn mac_scale(d: Domain, mac: Value, by: Value) -> Value {
    if d == Domain::Gold {
        [gl_mul(mac[0], by[0]), gl_mul(mac[1], by[0]), 0, 0, 0, 0]
    } else {
        d.mul(mac, by)
    }
}
pub(crate) fn mac_canonical(d: Domain, mac: Value) -> bool {
    if d == Domain::Gold {
        d.canonical([mac[0], 0, 0, 0, 0, 0])
            && d.canonical([mac[1], 0, 0, 0, 0, 0])
            && (mac[2] | mac[3] | mac[4] | mac[5]) == 0
    } else {
        d.canonical(mac)
    }
}

// ============================================================================
// Wires and preprocessing material
// ============================================================================

/// One party's share of an authenticated 64-lane Boolean word:
/// `[value share, MAC share low, MAC share high]`.
#[derive(Clone, Copy, Default)]
pub(crate) struct ABit(pub [u64; 3]);
impl ABit {
    #[inline(always)]
    pub(crate) const fn new(share: u64, mac: u128) -> Self {
        Self([share, mac as u64, (mac >> 64) as u64])
    }
    #[inline(always)]
    pub(crate) const fn share(self) -> u64 {
        self.0[0]
    }
    #[inline(always)]
    pub(crate) const fn mac(self) -> u128 {
        (self.0[1] as u128) | ((self.0[2] as u128) << 64)
    }
}
impl core::ops::BitXor for ABit {
    type Output = Self;
    #[inline(always)]
    fn bitxor(self, rhs: Self) -> Self {
        Self([
            self.0[0] ^ rhs.0[0],
            self.0[1] ^ rhs.0[1],
            self.0[2] ^ rhs.0[2],
        ])
    }
}
impl Wipe for ABit {
    fn secret_wipe(&mut self) {
        ct_zeroize_u64s(&mut self.0);
    }
    fn wipe_slice(values: &mut [Self]) {
        qsag_asm::volatile_fill(values, Self::default());
    }
}
impl ShareBit for ABit {}

/// Pre-seeded 128-column active KOS15 correlated-OT material between `self` and
/// one quorum peer, used solely for online sender-residual OLE MAC blinding.
/// Never touches witness wires or `PartyPreprocessing` queues; wiped on `Drop` and `poison()`.
#[derive(Clone)]
pub(crate) struct BlindOtPeer {
    /// Correlation scalar `Δ_{self -> peer}` when `self` acts as online KOS15 OT sender.
    pub(crate) sender_delta: u128,
    /// 128 chosen column seeds `k_col = k_{col, bit_col(sender_delta)}` (`self` = online sender).
    pub(crate) sender_seeds: [[u8; 32]; 128],
    /// 128 column seed pairs `(k_{col, 0}, k_{col, 1})` (`self` = online receiver, `peer` = online sender).
    pub(crate) receiver_seeds: [[[u8; 32]; 2]; 128],
    /// Monotonic expansion counter so every `check()` uses fresh one-time PRG blocks.
    pub(crate) counter: u64,
}
impl BlindOtPeer {
    pub(crate) fn wipe(&mut self) {
        qsag_asm::volatile_fill(core::slice::from_mut(&mut self.sender_delta), 0);
        for s in &mut self.sender_seeds {
            ct_zeroize_bytes(s);
        }
        for pair in &mut self.receiver_seeds {
            ct_zeroize_bytes(&mut pair[0]);
            ct_zeroize_bytes(&mut pair[1]);
        }
        qsag_asm::volatile_fill(core::slice::from_mut(&mut self.counter), 0);
    }

    #[cfg(any(feature = "std", test))]
    pub(crate) fn fork_stream(&self, label: &[u8], stream_id: u64) -> Self {
        let derive = |col: usize, seed: &[u8; 32]| -> [u8; 32] {
            cshake256_framed_32(
                b"QSAG.OUTER.SPDZ.BLIND.FORK.V1",
                &[
                    label,
                    &stream_id.to_le_bytes(),
                    &(col as u64).to_le_bytes(),
                    seed,
                ],
            )
        };
        Self {
            sender_delta: self.sender_delta,
            sender_seeds: core::array::from_fn(|col| derive(col, &self.sender_seeds[col])),
            receiver_seeds: core::array::from_fn(|col| {
                [
                    derive(col, &self.receiver_seeds[col][0]),
                    derive(col, &self.receiver_seeds[col][1]),
                ]
            }),
            counter: 0,
        }
    }
}
impl Drop for BlindOtPeer {
    fn drop(&mut self) {
        self.wipe();
    }
}

/// One party's additive shares of the global MAC keys plus per-peer active-OT
/// blinding seeds. Summed over the quorum they give `Δ` (Boolean), the two
/// Goldilocks keys, and the `Secp256k1`, `Ed25519`, `Pallas`, and `BLS12-381`
/// base-field keys. Erased on drop and on ceremony-wide worker abort.
pub struct MacKeyShare {
    pub boolean: u128,
    /// Indexed by [`ThresholdField`]; Goldilocks uses limbs 0 and 1.
    pub field: [Value; 5],
    pub(crate) blind_ot: Vec<BlindOtPeer>,
}
impl Drop for MacKeyShare {
    fn drop(&mut self) {
        self.wipe();
    }
}
impl MacKeyShare {
    pub(crate) fn wipe(&mut self) {
        qsag_asm::volatile_fill(core::slice::from_mut(&mut self.boolean), 0);
        ct_zeroize_u64s(self.field.as_flattened_mut());
        for peer in &mut self.blind_ot {
            peer.wipe();
        }
        self.blind_ot.clear();
    }

    pub(crate) fn wiped() -> Self {
        Self {
            boolean: 0,
            field: [ZERO; 5],
            blind_ot: Vec::new(),
        }
    }

    #[cfg(test)]
    pub(crate) fn is_wiped(&self) -> bool {
        self.boolean == 0 && self.field == [ZERO; 5] && self.blind_ot.is_empty()
    }

    #[cfg(any(feature = "std", test))]
    pub(crate) fn fork_stream(&self, label: &[u8], stream_id: u64) -> Self {
        Self {
            boolean: self.boolean,
            field: self.field,
            blind_ot: self
                .blind_ot
                .iter()
                .map(|p| p.fork_stream(label, stream_id))
                .collect(),
        }
    }

    fn valid_for(&self, config: &ThresholdConfig) -> bool {
        self.blind_ot.len() == config.quorum.len() - 1
            && ThresholdField::ALL
                .iter()
                .all(|f| mac_canonical(f.domain(), self.field[f.index()]))
    }
}

/// Ceremony-wide atomic poison flag and synchronous cross-worker `MacKeyShare`
/// zeroizer. When any concurrent batch worker aborts, [`QuorumKeyEscrow::poison_all`]
/// sets `cancelled` and volatile-wipes every registered `MacKeyShare` across all
/// threads immediately, before any sibling worker can compute or open another share.
#[cfg(any(feature = "std", test))]
#[derive(Clone, Default)]
pub(crate) struct QuorumKeyEscrow {
    cancelled: std::sync::Arc<core::sync::atomic::AtomicBool>,
    slots: std::sync::Arc<std::sync::Mutex<Vec<std::sync::Arc<std::sync::Mutex<MacKeyShare>>>>>,
}
#[cfg(any(feature = "std", test))]
impl QuorumKeyEscrow {
    pub(crate) fn new(cancelled: std::sync::Arc<core::sync::atomic::AtomicBool>) -> Self {
        Self {
            cancelled,
            slots: std::sync::Arc::new(std::sync::Mutex::new(Vec::new())),
        }
    }

    pub(crate) fn register(&self, keys: MacKeyShare) -> std::sync::Arc<std::sync::Mutex<MacKeyShare>> {
        let slot = std::sync::Arc::new(std::sync::Mutex::new(keys));
        if self.is_poisoned() {
            slot.lock().unwrap_or_else(|e| e.into_inner()).wipe();
        }
        self.slots
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .push(slot.clone());
        slot
    }

    pub(crate) fn is_poisoned(&self) -> bool {
        self.cancelled.load(core::sync::atomic::Ordering::SeqCst)
    }

    pub(crate) fn poison_all(&self) {
        self.cancelled
            .store(true, core::sync::atomic::Ordering::SeqCst);
        let guard = self.slots.lock().unwrap_or_else(|e| e.into_inner());
        for slot in guard.iter() {
            slot.lock().unwrap_or_else(|e| e.into_inner()).wipe();
        }
    }

    #[cfg(test)]
    pub(crate) fn registered_count_and_all_wiped(&self) -> (usize, bool) {
        let guard = self.slots.lock().unwrap_or_else(|e| e.into_inner());
        let all_wiped = guard
            .iter()
            .all(|s| s.lock().unwrap_or_else(|e| e.into_inner()).is_wiped());
        (guard.len(), all_wiped)
    }
}

/// One party's share of 64 authenticated bits: lane `k` of `share` is its XOR
/// share of bit `k`, and `macs[k]` its XOR share of `bit_k · Δ`.
pub struct AuthWord {
    pub share: u64,
    pub macs: [u128; 64],
}
impl Drop for AuthWord {
    fn drop(&mut self) {
        ct_zeroize_u64s(core::slice::from_mut(&mut self.share));
        qsag_asm::volatile_fill(&mut self.macs, 0);
    }
}
impl AuthWord {
    fn bit(&self) -> ABit {
        ABit::new(self.share, pack_macs(&self.macs, u64::MAX))
    }
}

/// One party's share of 64 Boolean Beaver triples `c_k = a_k & b_k`.
pub struct BooleanTriple {
    pub a: AuthWord,
    pub b: AuthWord,
    pub c: AuthWord,
}

/// One party's share of an authenticated field element: `[value, MAC]`.
pub struct FieldShare(pub [Value; 2]);
impl Drop for FieldShare {
    fn drop(&mut self) {
        ct_zeroize_u64s(self.0.as_flattened_mut());
    }
}

/// One party's share of a field Beaver triple `(a, b, a·b)`.
pub struct FieldTriple(pub [FieldShare; 3]);

/// One party's share of 64 doubly authenticated bits: the same uniformly
/// random bits shared as a Boolean word and, lane by lane, as field elements.
pub struct DaBitWord {
    pub bits: AuthWord,
    pub field: [FieldShare; 64],
}

// ============================================================================
// Engine
// ============================================================================

struct PendingField {
    values: SecretVec<Value>,
    macs: SecretVec<Value>,
}

/// Domain descriptor for one online sender-residual OLE MAC blinding instance.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum BlindKind {
    Gf128,
    GoldExt2,
    Prime(Domain),
}

impl BlindKind {
    const TWO_POW_254: Value = [0, 0, 0, 1u64 << 62, 0, 0];
    const TWO_POW_380: Value = [0, 0, 0, 0, 0, 1u64 << 60];

    #[inline]
    fn words_len(self) -> usize {
        match self {
            Self::Gf128 | Self::GoldExt2 => 2,
            Self::Prime(d) => d.limbs_len(),
        }
    }

    /// Number of 64-bit choice words (`L = 64 * choice_words` OT bits) so that
    /// Leftover Hash Lemma statistical distance is `< 2^-128` over `F_self`.
    #[inline]
    fn choice_words(self) -> usize {
        match self {
            Self::Gf128 | Self::GoldExt2 => 6,        // 384 bits >= 128 + 256
            Self::Prime(Domain::BlsFp) => 10,         // 640 bits >= 381 + 259
            Self::Prime(_) => 8,                      // 512 bits >= 256 + 256
        }
    }

    #[inline]
    fn canonical(self, v: Value) -> bool {
        match self {
            Self::Gf128 => (v[2] | v[3] | v[4] | v[5]) == 0,
            Self::GoldExt2 => {
                v[0] < GOLDILOCKS_PRIME
                    && v[1] < GOLDILOCKS_PRIME
                    && (v[2] | v[3] | v[4] | v[5]) == 0
            }
            Self::Prime(d) => d.canonical(v),
        }
    }

    #[inline]
    fn add(self, a: Value, b: Value) -> Value {
        match self {
            Self::Gf128 => [a[0] ^ b[0], a[1] ^ b[1], 0, 0, 0, 0],
            Self::GoldExt2 => [gl_add(a[0], b[0]), gl_add(a[1], b[1]), 0, 0, 0, 0],
            Self::Prime(d) => d.add(a, b),
        }
    }

    #[inline]
    fn sub(self, a: Value, b: Value) -> Value {
        match self {
            Self::Gf128 => [a[0] ^ b[0], a[1] ^ b[1], 0, 0, 0, 0],
            Self::GoldExt2 => [gl_sub(a[0], b[0]), gl_sub(a[1], b[1]), 0, 0, 0, 0],
            Self::Prime(d) => d.sub(a, b),
        }
    }

    #[inline]
    fn neg(self, a: Value) -> Value {
        self.sub(ZERO, a)
    }

    /// Field multiplication in `GF(2^128)`, `GF(p)[u]/(u^2 - 7)` (`7` QNR mod Goldilocks `p`),
    /// or prime base field `F_p`. Every nonzero element is invertible!
    #[inline]
    fn mul(self, a: Value, b: Value) -> Value {
        match self {
            Self::Gf128 => {
                let lhs = (a[0] as u128) | ((a[1] as u128) << 64);
                let rhs = (b[0] as u128) | ((b[1] as u128) << 64);
                let prod = gf2_128_mul(lhs, rhs);
                [prod as u64, (prod >> 64) as u64, 0, 0, 0, 0]
            }
            Self::GoldExt2 => {
                let c0 = gl_add(gl_mul(a[0], b[0]), gl_mul(7, gl_mul(a[1], b[1])));
                let c1 = gl_add(gl_mul(a[0], b[1]), gl_mul(a[1], b[0]));
                [c0, c1, 0, 0, 0, 0]
            }
            Self::Prime(d) => d.mul(a, b),
        }
    }

    /// Constant-time zero-rejection wide XOF sampling (`< 2^-128` statistical distance).
    fn sample_xof(self, xof: &mut Shake256) -> Value {
        match self {
            Self::Gf128 => {
                let mut raw = [0u8; 16];
                xof.squeeze(&mut raw);
                let v0 = u64::from_le_bytes(raw[..8].try_into().unwrap());
                let v1 = u64::from_le_bytes(raw[8..].try_into().unwrap());
                ct_zeroize_bytes(&mut raw);
                [v0, v1, 0, 0, 0, 0]
            }
            Self::GoldExt2 => {
                let mut raw0 = [0u8; 24];
                let mut raw1 = [0u8; 24];
                xof.squeeze(&mut raw0);
                xof.squeeze(&mut raw1);
                let g0 = reduce_192_mod_p(&raw0);
                let g1 = reduce_192_mod_p(&raw1);
                ct_zeroize_bytes(&mut raw0);
                ct_zeroize_bytes(&mut raw1);
                [g0, g1, 0, 0, 0, 0]
            }
            Self::Prime(Domain::BlsFp) => {
                let mut raw = [0u8; 96];
                xof.squeeze(&mut raw);
                let mut lo_b = [0u8; 48];
                let mut hi_b = [0u8; 48];
                lo_b.copy_from_slice(&raw[..48]);
                hi_b.copy_from_slice(&raw[48..]);
                ct_zeroize_bytes(&mut raw);
                lo_b[47] &= 0x0f;
                hi_b[47] &= 0x0f;
                let lo: Value = crate::limbs::from_le_bytes(&lo_b);
                let hi: Value = crate::limbs::from_le_bytes(&hi_b);
                ct_zeroize_bytes(&mut lo_b);
                ct_zeroize_bytes(&mut hi_b);
                Domain::BlsFp.add(lo, Domain::BlsFp.mul(hi, Self::TWO_POW_380))
            }
            Self::Prime(d) => {
                let mut raw = [0u8; 64];
                xof.squeeze(&mut raw);
                let mut lo_b = [0u8; 32];
                let mut hi_b = [0u8; 32];
                lo_b.copy_from_slice(&raw[..32]);
                hi_b.copy_from_slice(&raw[32..]);
                ct_zeroize_bytes(&mut raw);
                lo_b[31] &= 0x3f;
                hi_b[31] &= 0x3f;
                let lo = lift4(crate::limbs::from_le_bytes(&lo_b));
                let hi = lift4(crate::limbs::from_le_bytes(&hi_b));
                ct_zeroize_bytes(&mut lo_b);
                ct_zeroize_bytes(&mut hi_b);
                d.add(lo, d.mul(hi, Self::TWO_POW_254))
            }
        }
    }
}

/// One party's online state. Wires made by one engine may be used by another
/// engine of the same party that holds the same MAC key shares.
pub(crate) struct SpdzEngine<T> {
    pub(crate) config: ThresholdConfig,
    pub(crate) party: usize,
    first: bool,
    peers: Vec<usize>,
    /// Session as given by the caller; batch engines derive theirs from it.
    #[cfg(any(feature = "std", test))]
    root_session: [u8; 32],
    session: [u8; 32],
    link_keys: Vec<[u8; 32]>,
    keys: MacKeyShare,
    #[cfg(any(feature = "std", test))]
    escrow_slot: Option<std::sync::Arc<std::sync::Mutex<MacKeyShare>>>,
    #[cfg(any(feature = "std", test))]
    batch_escrow: Option<QuorumKeyEscrow>,
    ones_mac: u128,
    sequence: u64,
    failed: bool,
    rng: Shake256,
    /// Hash chain over every broadcast payload, in quorum order. Compared
    /// across the quorum at each check, so equivocation is caught there.
    transcript: [u8; 32],
    transcript_dirty: bool,
    pending_bits: SecretVec<u64>,
    pending_bit_macs: SecretVec<u128>,
    pending_fields: [PendingField; 5],
    #[cfg(any(feature = "std", test))]
    pub(crate) batch_cancelled: Option<alloc::sync::Arc<core::sync::atomic::AtomicBool>>,
    #[cfg(test)]
    pub(crate) fault: Option<Fault>,
    pub(crate) transport: T,
}

/// Deviations a corrupt custodian can make, for regression tests. Each one
/// fires once, on the first matching operation.
#[cfg(test)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Fault {
    /// Flip one lane of the local value share of a wire about to be opened.
    FlipOpenedShare { lane: usize },
    /// Send a wrong masked difference in a Boolean Beaver opening.
    BeaverOpening { lane: usize },
    /// Use a wrong local product share after a Boolean Beaver opening.
    BeaverOutput { lane: usize },
    /// Send a wrong masked difference in a field Beaver opening.
    FieldBeaverOpening { lane: usize },
    /// Send a wrong masked bit during a Boolean-to-field conversion.
    ConversionBit { lane: usize },
    /// Send a wrong masked difference during a field-to-Boolean conversion.
    ConversionField { lane: usize },
    /// Contribute a non-uniform word where lane-uniform input is required.
    SplitInput,
    /// Send different opening shares to different peers.
    Equivocate,
    /// Open the correct value share but hold a wrong MAC share for it.
    WrongMac,
}

impl<T> Drop for SpdzEngine<T> {
    fn drop(&mut self) {
        for key in &mut self.link_keys {
            ct_zeroize_bytes(key);
        }
        qsag_asm::volatile_fill(core::slice::from_mut(&mut self.ones_mac), 0);
        ct_zeroize_bytes(&mut self.transcript);
    }
}

fn words32(bytes: &[u8; 32]) -> [u64; 4] {
    core::array::from_fn(|i| u64::from_le_bytes(bytes[8 * i..8 * i + 8].try_into().unwrap()))
}
fn bytes_of(words: &[u64]) -> Vec<u8> {
    words.iter().flat_map(|w| w.to_le_bytes()).collect()
}

impl<T: Transport> SpdzEngine<T> {
    pub(crate) fn new(
        party: usize,
        session: [u8; 32],
        config: ThresholdConfig,
        mut link_keys: Vec<[u8; 32]>,
        keys: MacKeyShare,
        transport: T,
    ) -> Result<Self, Error> {
        if !config.quorum.contains(&party)
            || link_keys.len() != config.quorum.len() - 1
            || !keys.valid_for(&config)
        {
            for key in &mut link_keys {
                ct_zeroize_bytes(key);
            }
            return Err(Error::InvalidConfiguration);
        }
        #[cfg(any(feature = "std", test))]
        let root_session = session;
        let session = cshake256_framed_32(b"QSAG.OUTER.SPDZ.V1", &[&session, &config.binding()]);
        let mut rng = Shake256::new();
        rng.absorb(b"QSAG.OUTER.SPDZ.RNG.V1");
        rng.absorb(&session);
        rng.absorb(&[party as u8]);
        for key in &link_keys {
            rng.absorb(key);
        }
        rng.finalize(0x1f);
        let peers = config
            .quorum
            .iter()
            .copied()
            .filter(|&p| p != party)
            .collect();
        let empty = || PendingField {
            values: SecretVec::new(),
            macs: SecretVec::new(),
        };
        Ok(Self {
            first: party == config.quorum[0],
            ones_mac: gf2_128_mul(keys.boolean, u64::MAX as u128),
            transcript: cshake256_framed_32(b"QSAG.OUTER.SPDZ.TRANSCRIPT.V1", &[&session]),
            config,
            party,
            peers,
            #[cfg(any(feature = "std", test))]
            root_session,
            session,
            link_keys,
            keys,
            #[cfg(any(feature = "std", test))]
            escrow_slot: None,
            #[cfg(any(feature = "std", test))]
            batch_escrow: None,
            sequence: 0,
            failed: false,
            rng,
            transcript_dirty: false,
            pending_bits: SecretVec::new(),
            pending_bit_macs: SecretVec::new(),
            pending_fields: [empty(), empty(), empty(), empty(), empty()],
            #[cfg(any(feature = "std", test))]
            batch_cancelled: None,
            #[cfg(test)]
            fault: None,
            transport,
        })
    }

    /// Move this engine's `MacKeyShare` into a shared [`QuorumKeyEscrow`] so that
    /// an abort in any concurrent batch worker synchronously wipes all workers' keys.
    #[cfg(any(feature = "std", test))]
    pub(crate) fn attach_escrow(&mut self, escrow: &QuorumKeyEscrow) {
        if self.escrow_slot.is_none() {
            let moved = core::mem::replace(&mut self.keys, MacKeyShare::wiped());
            let slot = escrow.register(moved);
            self.escrow_slot = Some(slot);
        }
        self.batch_escrow = Some(escrow.clone());
    }

    #[inline]
    fn is_failed(&mut self) -> bool {
        #[cfg(any(feature = "std", test))]
        if !self.failed
            && self
                .batch_escrow
                .as_ref()
                .is_some_and(QuorumKeyEscrow::is_poisoned)
        {
            Core::poison(self);
        }
        self.failed
    }

    fn boolean_key(&self) -> u128 {
        #[cfg(any(feature = "std", test))]
        if let Some(slot) = &self.escrow_slot {
            return slot.lock().unwrap_or_else(|e| e.into_inner()).boolean;
        }
        self.keys.boolean
    }

    fn field_key(&self, index: usize) -> Value {
        #[cfg(any(feature = "std", test))]
        if let Some(slot) = &self.escrow_slot {
            return slot.lock().unwrap_or_else(|e| e.into_inner()).field[index];
        }
        self.keys.field[index]
    }

    fn with_blind_ot<R>(&mut self, f: impl FnOnce(&mut [BlindOtPeer]) -> R) -> R {
        #[cfg(any(feature = "std", test))]
        if let Some(slot) = &self.escrow_slot {
            let mut guard = slot.lock().unwrap_or_else(|e| e.into_inner());
            return f(&mut guard.blind_ot);
        }
        f(&mut self.keys.blind_ot)
    }

    /// Custody secrets for starting this custodian's batch engines.
    #[cfg(any(feature = "std", test))]
    pub(crate) fn custody(&self) -> ([u8; 32], ThresholdConfig, Vec<[u8; 32]>, MacKeyShare) {
        let forked_keys = if let Some(slot) = &self.escrow_slot {
            slot.lock()
                .unwrap_or_else(|e| e.into_inner())
                .fork_stream(b"SEED", 0)
        } else {
            self.keys.fork_stream(b"SEED", 0)
        };
        (
            self.root_session,
            self.config.clone(),
            self.link_keys.clone(),
            forked_keys,
        )
    }

    /// Hedge local commitment and coin randomness with private ceremony entropy.
    pub(crate) fn mix_entropy(&mut self, entropy: &[u8; 32]) {
        let mut current = [0u8; 32];
        self.rng.squeeze(&mut current);
        let mut next = Shake256::new();
        next.absorb(b"QSAG.OUTER.SPDZ.HEDGE.V1");
        next.absorb(&current);
        next.absorb(entropy);
        next.absorb(&self.session);
        next.finalize(0x1f);
        ct_zeroize_bytes(&mut current);
        self.rng = next;
    }

    fn fail<V>(&mut self, error: Error) -> Result<V, Error> {
        Core::poison(self);
        Err(error)
    }

    fn tag(&self, key: &[u8; 32], sender: usize, recipient: usize, payload: &[u64]) -> [u8; 32] {
        let mut encoded = bytes_of(payload);
        let tag = cshake256_framed_32(
            b"QSAG.OUTER.SPDZ.MAC.V1",
            &[
                key,
                &self.session,
                &(sender as u64).to_le_bytes(),
                &(recipient as u64).to_le_bytes(),
                &self.sequence.to_le_bytes(),
                &encoded,
            ],
        );
        ct_zeroize_bytes(&mut encoded);
        tag
    }

    /// Send `own` to every peer and return all payloads in quorum order (own
    /// included). Any transport or authentication failure poisons the engine.
    fn broadcast(&mut self, own: &[u64]) -> Result<Vec<SecretVec<u64>>, Error> {
        self.send(&vec![own; self.peers.len()], own)
    }

    fn send(&mut self, to_peers: &[&[u64]], own: &[u64]) -> Result<Vec<SecretVec<u64>>, Error> {
        if self.is_failed() {
            return Err(Error::MultiplicationCheck);
        }
        #[cfg(any(feature = "std", test))]
        if self
            .batch_cancelled
            .as_ref()
            .is_some_and(|flag| flag.load(core::sync::atomic::Ordering::SeqCst))
        {
            Core::poison(self);
            return Err(Error::Transport);
        }
        let outgoing = self
            .peers
            .iter()
            .zip(&self.link_keys)
            .zip(to_peers)
            .map(|((&peer, key), payload)| Envelope {
                sender: self.party,
                recipient: peer,
                sequence: self.sequence,
                payload: payload.to_vec(),
                tag: self.tag(key, self.party, peer, payload),
            })
            .collect();
        let incoming = match self.transport.exchange_many(outgoing) {
            Ok(incoming) => incoming,
            Err(error) => return self.fail(error),
        };
        if incoming.len() != self.peers.len() {
            return self.fail(Error::InvalidConfiguration);
        }
        let mut received = Vec::with_capacity(self.peers.len());
        for (i, mut message) in incoming.into_iter().enumerate() {
            let peer = self.peers[i];
            if message.sender != peer
                || message.recipient != self.party
                || message.sequence != self.sequence
                || message.payload.len() != own.len()
                || ct_eq_bytes_mask(
                    &message.tag,
                    &self.tag(&self.link_keys[i], peer, self.party, &message.payload),
                ) != u64::MAX
            {
                return self.fail(Error::Authentication(peer));
            }
            received.push(SecretVec::from(core::mem::take(&mut message.payload)));
        }
        let mine = self
            .config
            .quorum
            .iter()
            .position(|&p| p == self.party)
            .unwrap();
        received.insert(mine, own.iter().copied().collect());
        let mut chain = Shake256::new();
        chain.absorb(b"QSAG.OUTER.SPDZ.CHAIN.V1");
        chain.absorb(&self.transcript);
        chain.absorb(&self.sequence.to_le_bytes());
        for payload in &received {
            let mut bytes = bytes_of(payload);
            chain.absorb(&bytes);
            ct_zeroize_bytes(&mut bytes);
        }
        chain.finalize(0x1f);
        chain.squeeze(&mut self.transcript);
        self.transcript_dirty = true;
        self.sequence = match self.sequence.checked_add(1) {
            Some(next) => next,
            None => return self.fail(Error::InvalidConfiguration),
        };
        Ok(received)
    }

    /// Confidential authenticated pairwise exchange (`to_peers.len() == self.peers.len()`).
    /// Unlike `send`, confidential payloads differ per recipient and are NOT absorbed into
    /// the broadcast `self.transcript`; instead, returns per-edge digests `(out_digests, in_digests)`
    /// bound and symmetry-checked inside the subsequent `commit_then_open` coin round.
    #[allow(clippy::type_complexity)]
    fn send_pairwise(
        &mut self,
        to_peers: &[SecretVec<u64>],
        expected_len: usize,
    ) -> Result<(Vec<[u8; 32]>, Vec<[u8; 32]>, Vec<SecretVec<u64>>), Error> {
        if self.is_failed() {
            return Err(Error::MultiplicationCheck);
        }
        #[cfg(any(feature = "std", test))]
        if self
            .batch_cancelled
            .as_ref()
            .is_some_and(|flag| flag.load(core::sync::atomic::Ordering::SeqCst))
        {
            Core::poison(self);
            return Err(Error::Transport);
        }
        let seq = self.sequence;
        let edge_digest = |session: &[u8; 32], sender: usize, recipient: usize, words: &[u64]| {
            let mut bytes = bytes_of(words);
            let d = cshake256_framed_32(
                b"QSAG.OUTER.SPDZ.PAIRWISE.V1",
                &[
                    session,
                    &seq.to_le_bytes(),
                    &(sender as u64).to_le_bytes(),
                    &(recipient as u64).to_le_bytes(),
                    &bytes,
                ],
            );
            ct_zeroize_bytes(&mut bytes);
            d
        };
        let mut out_digests = Vec::with_capacity(self.peers.len());
        let mut outgoing = Vec::with_capacity(self.peers.len());
        for ((&peer, key), payload) in self.peers.iter().zip(&self.link_keys).zip(to_peers) {
            debug_assert_eq!(payload.len(), expected_len);
            out_digests.push(edge_digest(&self.session, self.party, peer, payload));
            outgoing.push(Envelope {
                sender: self.party,
                recipient: peer,
                sequence: seq,
                payload: payload.to_vec(),
                tag: self.tag(key, self.party, peer, payload),
            });
        }
        let incoming = match self.transport.exchange_many(outgoing) {
            Ok(incoming) => incoming,
            Err(error) => return self.fail(error),
        };
        if incoming.len() != self.peers.len() {
            return self.fail(Error::InvalidConfiguration);
        }
        let mut in_digests = Vec::with_capacity(self.peers.len());
        let mut received = Vec::with_capacity(self.peers.len());
        for (i, mut message) in incoming.into_iter().enumerate() {
            let peer = self.peers[i];
            if message.sender != peer
                || message.recipient != self.party
                || message.sequence != seq
                || message.payload.len() != expected_len
                || ct_eq_bytes_mask(
                    &message.tag,
                    &self.tag(&self.link_keys[i], peer, self.party, &message.payload),
                ) != u64::MAX
            {
                return self.fail(Error::Authentication(peer));
            }
            in_digests.push(edge_digest(&self.session, peer, self.party, &message.payload));
            received.push(SecretVec::from(core::mem::take(&mut message.payload)));
        }
        self.sequence = match self.sequence.checked_add(1) {
            Some(next) => next,
            None => return self.fail(Error::InvalidConfiguration),
        };
        Ok((out_digests, in_digests, received))
    }

    /// Commit-then-open coin round that also cross-checks all `m(m - 1)` directed pairwise
    /// edge digests `(out_digests, in_digests)` across the quorum.
    #[allow(clippy::type_complexity)]
    fn commit_coin_with_edges(
        &mut self,
        label: &[u8],
        edges: &[(&[[u8; 32]], &[[u8; 32]])],
    ) -> Result<Shake256, Error> {
        let peer_count = self.peers.len();
        let mut coin = [0u8; 32];
        self.rng.squeeze(&mut coin);
        let mut payload = Vec::with_capacity(4 + edges.len() * peer_count * 8);
        payload.extend_from_slice(&words32(&coin));
        ct_zeroize_bytes(&mut coin);
        for &(out_d, in_d) in edges {
            for d in out_d.iter().chain(in_d.iter()) {
                payload.extend_from_slice(&words32(d));
            }
        }
        let opened = self.commit_then_open(label, &payload, &[])?;
        let quorum_len = self.config.quorum.len();
        // Verify that for every round `r` and every ordered pair `(pos_a, pos_b)` (`pos_a != pos_b`),
        // `pos_a`'s outgoing digest to `pos_b` equals `pos_b`'s incoming digest from `pos_a`.
        let slot_of = |owner_pos: usize, peer_pos: usize| -> usize {
            if peer_pos < owner_pos {
                peer_pos
            } else {
                peer_pos - 1
            }
        };
        for (round_idx, _) in edges.iter().enumerate() {
            let base = 4 + round_idx * peer_count * 8;
            for pos_a in 0..quorum_len {
                for pos_b in 0..quorum_len {
                    if pos_a == pos_b {
                        continue;
                    }
                    let a_out_off = base + slot_of(pos_a, pos_b) * 4;
                    let b_in_off = base + (peer_count + slot_of(pos_b, pos_a)) * 4;
                    if opened[pos_a][a_out_off..a_out_off + 4]
                        != opened[pos_b][b_in_off..b_in_off + 4]
                    {
                        return self.fail(Error::MultiplicationCheck);
                    }
                }
            }
        }
        let mut xof = Shake256::new();
        xof.absorb(b"QSAG.OUTER.SPDZ.BLIND.COIN.V1");
        xof.absorb(label);
        xof.absorb(&self.session);
        xof.absorb(&self.transcript);
        for row in &opened {
            xof.absorb(&bytes_of(&row[..4]));
        }
        xof.finalize(0x1f);
        Ok(xof)
    }

    /// Hiding and binding commitment of the quorum member at `position` to
    /// `payload` in the current round. Binding the position stops one member
    /// from replaying another's commitment and opening.
    fn commitment(
        &self,
        label: &[u8],
        position: usize,
        payload: &[u64],
        nonce: &[u8; 32],
    ) -> [u64; 4] {
        let mut bytes = bytes_of(payload);
        let digest = cshake256_framed_32(
            b"QSAG.OUTER.SPDZ.COMMIT.V1",
            &[
                label,
                &self.session,
                &self.sequence.to_le_bytes(),
                &[position as u8],
                &bytes,
                nonce,
            ],
        );
        ct_zeroize_bytes(&mut bytes);
        words32(&digest)
    }

    /// Commit to `payload`, then open it; every party's opening is checked
    /// against its commitment. Returns all payloads in quorum order.
    fn commit_then_open(
        &mut self,
        label: &[u8],
        payload: &[u64],
        prefix: &[u64],
    ) -> Result<Vec<SecretVec<u64>>, Error> {
        let mut nonce = [0u8; 32];
        self.rng.squeeze(&mut nonce);
        let mine = self
            .config
            .quorum
            .iter()
            .position(|&p| p == self.party)
            .unwrap();
        let own_commit = self.commitment(label, mine, payload, &nonce);
        let committed_at = self.sequence;
        let mut first: Vec<u64> = prefix.to_vec();
        first.extend_from_slice(&own_commit);
        let commits = self.broadcast(&first)?;
        if commits
            .iter()
            .any(|c| c[..prefix.len()] != first[..prefix.len()])
        {
            return self.fail(Error::MultiplicationCheck);
        }
        let mut opening: SecretVec<u64> = payload.iter().copied().collect();
        opening.extend_from_slice(&words32(&nonce));
        ct_zeroize_bytes(&mut nonce);
        let opened = self.broadcast(&opening)?;
        let now = self.sequence;
        self.sequence = committed_at;
        let mut ok = true;
        for (position, (commit, open)) in commits.iter().zip(&opened).enumerate() {
            let (body, nonce) = open.split_at(payload.len());
            let mut nonce_bytes = [0u8; 32];
            for (chunk, word) in nonce_bytes.chunks_exact_mut(8).zip(nonce) {
                chunk.copy_from_slice(&word.to_le_bytes());
            }
            ok &= commit[prefix.len()..] == self.commitment(label, position, body, &nonce_bytes);
        }
        self.sequence = now;
        if !ok {
            return self.fail(Error::MultiplicationCheck);
        }
        Ok(opened
            .into_iter()
            .map(|open| open[..payload.len()].iter().copied().collect())
            .collect())
    }

    fn field_challenge(xof: &mut Shake256, d: Domain) -> Value {
        loop {
            let mut bytes = [0u8; 48];
            let byte_len = d.limbs_len() * 8;
            xof.squeeze(&mut bytes[..byte_len]);
            let mut value = ZERO;
            for (limb, chunk) in value[..d.limbs_len()]
                .iter_mut()
                .zip(bytes[..byte_len].chunks_exact(8))
            {
                *limb = u64::from_le_bytes(chunk.try_into().unwrap());
            }
            ct_zeroize_bytes(&mut bytes);
            if d == Domain::Ed || d == Domain::PallasFp {
                value[3] &= 0x7fff_ffff_ffff_ffff;
            } else if d == Domain::BlsFp {
                value[5] &= 0x1fff_ffff_ffff_ffff;
            }
            if d.canonical(value) {
                return value;
            }
        }
    }

    /// Multiplicatively blinded batch MAC check (`C4-F1`).
    ///
    /// 1. All parties verify broadcast transcript agreement and open coin shares to fix
    ///    linear-combination challenges `χ`.
    /// 2. Each party computes its local unblinded MAC residuals `d_{p, item}` (never sent!).
    /// 3. Across all peers, parties run active KOS15 correlated-OT extension (`2` independent
    ///    128-bit correlation checks verified BEFORE any residual touches the wire), followed by
    ///    sender-residual OLE (`s_{j->i, l} + y_{j->i, l} = c_{i, l} · d_j`) and Leftover Hash
    ///    Lemma compression (`< 2^-128` statistical distance) into additive shares `w_p` of
    ///    `W = (Σ_i r_i) · (Σ_j d_j)`.
    /// 4. Parties commit-then-open `w_p` (`b"blind_sigma"`) and verify `Σ_p w_p == 0`.
    ///    An abort reveals only uniform `R · D`, leaking zero bits of any MAC key share!
    pub(crate) fn check(&mut self) -> Result<(), Error> {
        if self.is_failed() {
            return Err(Error::MultiplicationCheck);
        }
        if !self.transcript_dirty {
            return Ok(());
        }
        let transcript = words32(&self.transcript);
        let mut coin = [0u8; 32];
        self.rng.squeeze(&mut coin);
        let coins = self.commit_then_open(b"coin", &words32(&coin), &transcript)?;
        ct_zeroize_bytes(&mut coin);
        let mut xof = Shake256::new();
        xof.absorb(b"QSAG.OUTER.SPDZ.CHALLENGE.V1");
        xof.absorb(&self.session);
        xof.absorb(&self.transcript);
        for share in &coins {
            xof.absorb(&bytes_of(share));
        }
        xof.finalize(0x1f);

        // Assemble the deterministic list of active blinding instances and local secret residuals `d_p`.
        let mut kinds: Vec<BlindKind> = Vec::with_capacity(8);
        let mut local_d: SecretVec<Value> = SecretVec::new();

        if !self.pending_bits.is_empty() {
            let count = self.pending_bits.len();
            let bool_key = self.boolean_key();
            let values: SecretVec<u128> = self.pending_bits.iter().map(|&v| v as u128).collect();
            for _inst in 0..2 {
                let mut chi = vec![0u128; count];
                for c in &mut chi {
                    let mut bytes = [0u8; 16];
                    xof.squeeze(&mut bytes);
                    *c = u128::from_le_bytes(bytes);
                }
                let mac_sum = qsag_asm::gf2_128_dot(&chi, &self.pending_bit_macs);
                let value_sum = qsag_asm::gf2_128_dot(&chi, &values);
                let s = mac_sum ^ gf2_128_mul(bool_key, value_sum);
                kinds.push(BlindKind::Gf128);
                local_d.push([s as u64, (s >> 64) as u64, 0, 0, 0, 0]);
            }
            self.pending_bits.clear();
            self.pending_bit_macs.clear();
        }

        for field in ThresholdField::ALL {
            if self.pending_fields[field.index()].values.is_empty() {
                continue;
            }
            let d = field.domain();
            let key = self.field_key(field.index());
            let pending = &mut self.pending_fields[field.index()];
            if d == Domain::Gold {
                for _inst in 0..2 {
                    let mut acc = Secret([0u64; 2]);
                    for lane in 0..2 {
                        let mut total = Secret(ZERO);
                        for (value, mac) in pending.values.iter().zip(pending.macs.iter()) {
                            let chi = Self::field_challenge(&mut xof, d);
                            let m = [mac[lane], 0, 0, 0, 0, 0];
                            let k = [key[lane], 0, 0, 0, 0, 0];
                            let term = d.sub(m, d.mul(k, *value));
                            *total = d.add(*total, d.mul(chi, term));
                        }
                        acc[lane] = total[0];
                    }
                    kinds.push(BlindKind::GoldExt2);
                    local_d.push([acc[0], acc[1], 0, 0, 0, 0]);
                }
            } else {
                let mut total = Secret(ZERO);
                for (value, mac) in pending.values.iter().zip(pending.macs.iter()) {
                    let chi = Self::field_challenge(&mut xof, d);
                    let term = d.sub(*mac, d.mul(key, *value));
                    *total = d.add(*total, d.mul(chi, term));
                }
                kinds.push(BlindKind::Prime(d));
                local_d.push(*total);
            }
            pending.values.clear();
            pending.macs.clear();
        }

        if kinds.is_empty() {
            self.transcript_dirty = false;
            return Ok(());
        }

        // Compute OT row layout: `w_data` 64-bit choice words + `4` KOS15 sacrifice words (`256` bits).
        let mut item_bit_offsets = Vec::with_capacity(kinds.len());
        let mut w_data = 0usize;
        for &kind in &kinds {
            item_bit_offsets.push(w_data * 64);
            w_data += kind.choice_words();
        }
        let w_tot = w_data + 4;
        let peer_count = self.peers.len();

        // Sample disposable uniform choice words `c_own[0..w_tot]` for this check.
        let mut c_own: SecretVec<u64> = SecretVec::with_capacity(w_tot);
        for _ in 0..w_tot {
            let mut b8 = [0u8; 8];
            self.rng.squeeze(&mut b8);
            c_own.push(u64::from_le_bytes(b8));
            ct_zeroize_bytes(&mut b8);
        }

        // Expand per-peer 128-column KOS15 base-OT PRGs at the current one-use `counter`.
        let session = self.session;
        let my_party = self.party;
        let peers_copy = self.peers.clone();
        let expand_col = |sender: usize,
                          recipient: usize,
                          counter: u64,
                          col: usize,
                          seed: &[u8; 32],
                          out: &mut [u64]| {
            let mut prg = Shake256::new();
            prg.absorb(b"QSAG.OUTER.SPDZ.BLIND.PRG.V1");
            prg.absorb(&session);
            prg.absorb(&(sender as u64).to_le_bytes());
            prg.absorb(&(recipient as u64).to_le_bytes());
            prg.absorb(&counter.to_le_bytes());
            prg.absorb(&(col as u64).to_le_bytes());
            prg.absorb(seed);
            prg.finalize(0x1f);
            let mut buf = [0u8; 8];
            for slot in out.iter_mut() {
                prg.squeeze(&mut buf);
                *slot = u64::from_le_bytes(buf);
            }
            ct_zeroize_bytes(&mut buf);
        };

        // For each peer `i`:
        // - As Receiver (`peer[i]` -> `self`): build `u_to_send[i]` (`128 * w_tot` words) and keep `t0_cols[i]`.
        // - As Sender (`self` -> `peer[i]`): expand `k_cols[i]` and copy `sender_deltas[i]`.
        let mut u_to_send: Vec<SecretVec<u64>> = Vec::with_capacity(peer_count);
        let mut t0_cols: Vec<Vec<SecretVec<u64>>> = Vec::with_capacity(peer_count);
        let mut k_cols: Vec<Vec<SecretVec<u64>>> = Vec::with_capacity(peer_count);
        let mut sender_deltas: SecretVec<u128> = SecretVec::with_capacity(peer_count);
        let mut pair_counters: Vec<u64> = Vec::with_capacity(peer_count);

        let ot_ready = self.with_blind_ot(|blind_ot| {
            if blind_ot.len() != peer_count {
                return false;
            }
            for (i, ot) in blind_ot.iter_mut().enumerate() {
                let peer = peers_copy[i];
                let ctr = ot.counter;
                ot.counter = ot.counter.wrapping_add(1);
                pair_counters.push(ctr);
                sender_deltas.push(ot.sender_delta);

                let mut u_flat = SecretVec::with_capacity(128 * w_tot);
                let mut peer_t0 = Vec::with_capacity(128);
                let mut peer_k = Vec::with_capacity(128);
                let mut t1_tmp: SecretVec<u64> = vec![0u64; w_tot].into();
                for col in 0..128 {
                    let mut t0_col: SecretVec<u64> = vec![0u64; w_tot].into();
                    expand_col(peer, my_party, ctr, col, &ot.receiver_seeds[col][0], &mut t0_col);
                    expand_col(peer, my_party, ctr, col, &ot.receiver_seeds[col][1], &mut t1_tmp);
                    for w in 0..w_tot {
                        u_flat.push(t0_col[w] ^ t1_tmp[w] ^ c_own[w]);
                    }
                    peer_t0.push(t0_col);

                    let mut k_col: SecretVec<u64> = vec![0u64; w_tot].into();
                    expand_col(my_party, peer, ctr, col, &ot.sender_seeds[col], &mut k_col);
                    peer_k.push(k_col);
                }
                u_to_send.push(u_flat);
                t0_cols.push(peer_t0);
                k_cols.push(peer_k);
            }
            true
        });
        if !ot_ready {
            return self.fail(Error::MultiplicationCheck);
        }

        // Round P1: Exchange KOS15 column matrices `u_cols` (`128 * w_tot` words per peer).
        let (u_out_digests, u_in_digests, u_received) =
            self.send_pairwise(&u_to_send, 128 * w_tot)?;
        drop(u_to_send);

        // Sender computes `q_cols[i][col][w] = k_cols[i][col][w] ^ (mask(delta_col) & u_in[col][w])`.
        for (i, u_in) in u_received.iter().enumerate() {
            let delta = sender_deltas[i];
            for col in 0..128 {
                let mask = 0u64.wrapping_sub(((delta >> col) & 1) as u64);
                let u_slice = &u_in[col * w_tot..(col + 1) * w_tot];
                for (q_w, &u_w) in k_cols[i][col].iter_mut().zip(u_slice) {
                    *q_w ^= u_w & mask;
                }
            }
        }
        drop(u_received);

        // Round C1: Commit-then-open KOS15 challenge coin bound to all `u_cols` edge digests.
        let mut kos_xof =
            self.commit_coin_with_edges(b"blind_kos_chi", &[(&u_out_digests, &u_in_digests)])?;
        let data_bits = w_data * 64;
        let mut psi = [vec![0u128; data_bits], vec![0u128; data_bits]];
        for pass_psi in &mut psi {
            for slot in pass_psi {
                let mut b16 = [0u8; 16];
                kos_xof.squeeze(&mut b16);
                *slot = u128::from_le_bytes(b16);
            }
        }

        // Helper extracting 128-bit row `b` across 128 column vectors.
        let row128_of = |cols: &[SecretVec<u64>], b: usize| -> u128 {
            let word = b / 64;
            let bit = b % 64;
            let mut lo = 0u64;
            let mut hi = 0u64;
            for col in 0..64 {
                lo |= ((cols[col][word] >> bit) & 1) << col;
                hi |= ((cols[64 + col][word] >> bit) & 1) << col;
            }
            (lo as u128) | ((hi as u128) << 64)
        };
        let c_bit = |c_words: &[u64], b: usize| -> u64 { (c_words[b / 64] >> (b % 64)) & 1 };

        // Round P2: Receiver sends `(x_kos[0..2], t_kos[0..2])` (`8` `u64` words) to each Sender;
        // Sender verifies active KOS15 correlation BEFORE any residual `d_p` touches the wire!
        let mut kos_to_send: Vec<SecretVec<u64>> = Vec::with_capacity(peer_count);
        for peer_t0 in &t0_cols {
            let mut msg = SecretVec::with_capacity(8);
            for (pass, pass_psi) in psi.iter().enumerate() {
                let sac_base = data_bits + pass * 128;
                let c_mask = (c_own[w_data + 2 * pass] as u128)
                    | ((c_own[w_data + 2 * pass + 1] as u128) << 64);
                let mut t_mask = 0u128;
                for l in 0..128 {
                    let row = Secret(row128_of(peer_t0, sac_base + l));
                    t_mask ^= gf2_128_mul(*row, 1u128 << l);
                }
                let mut x_acc = Secret(c_mask);
                let mut t_acc = Secret(t_mask);
                for (b, &psi_val) in pass_psi.iter().enumerate() {
                    let choose = 0u128.wrapping_sub(c_bit(&c_own, b) as u128);
                    *x_acc ^= psi_val & choose;
                    let row = Secret(row128_of(peer_t0, b));
                    *t_acc ^= gf2_128_mul(*row, psi_val);
                }
                msg.push(*x_acc as u64);
                msg.push((*x_acc >> 64) as u64);
                msg.push(*t_acc as u64);
                msg.push((*t_acc >> 64) as u64);
            }
            kos_to_send.push(msg);
        }
        let (kos_out_digests, kos_in_digests, kos_received) =
            self.send_pairwise(&kos_to_send, 8)?;
        drop(kos_to_send);

        let mut kos_ok = u64::MAX;
        for (i, resp) in kos_received.iter().enumerate() {
            let delta = sender_deltas[i];
            let peer_q = &k_cols[i];
            for (pass, pass_psi) in psi.iter().enumerate() {
                let x_in = (resp[4 * pass] as u128) | ((resp[4 * pass + 1] as u128) << 64);
                let t_in = (resp[4 * pass + 2] as u128) | ((resp[4 * pass + 3] as u128) << 64);
                let sac_base = data_bits + pass * 128;
                let mut q_acc = Secret(0u128);
                for l in 0..128 {
                    let row = Secret(row128_of(peer_q, sac_base + l));
                    *q_acc ^= gf2_128_mul(*row, 1u128 << l);
                }
                for (b, &psi_val) in pass_psi.iter().enumerate() {
                    let row = Secret(row128_of(peer_q, b));
                    *q_acc ^= gf2_128_mul(*row, psi_val);
                }
                let rhs = Secret(t_in ^ gf2_128_mul(x_in, delta));
                kos_ok &= ct_eq_bytes_mask(&q_acc.to_le_bytes(), &rhs.to_le_bytes());
            }
        }
        drop(kos_received);
        if kos_ok != u64::MAX {
            return self.fail(Error::MultiplicationCheck);
        }

        // Round P3: Active KOS15 correlation passed! Run sender-residual OLE across all peers:
        // Sender `self` sends `(ct_0, ct_1) = (pad_0 + x, pad_1 + x + d_self)` and stores `s = -x`;
        // Receiver `i` computes `y = ct_c - pad_c = x + c * d_self`, so `s + y = c * d_self`!
        let ro_pad = |kind: BlindKind,
                      sender: usize,
                      recipient: usize,
                      ctr: u64,
                      row_idx: usize,
                      key128: u128|
         -> Value {
            let mut xof_ro = Shake256::new();
            xof_ro.absorb(b"QSAG.OUTER.SPDZ.BLIND.RO.V1");
            xof_ro.absorb(&session);
            xof_ro.absorb(&(sender as u64).to_le_bytes());
            xof_ro.absorb(&(recipient as u64).to_le_bytes());
            xof_ro.absorb(&ctr.to_le_bytes());
            xof_ro.absorb(&(row_idx as u64).to_le_bytes());
            let mut kb = key128.to_le_bytes();
            xof_ro.absorb(&kb);
            ct_zeroize_bytes(&mut kb);
            xof_ro.finalize(0x1f);
            kind.sample_xof(&mut xof_ro)
        };

        let ole_words_per_peer: usize = kinds
            .iter()
            .map(|k| k.choice_words() * 64 * 2 * k.words_len())
            .sum();
        let mut ole_to_send: Vec<SecretVec<u64>> = Vec::with_capacity(peer_count);
        // `sender_shares[peer_idx][item_idx]` holds the `L` additive shares `s = -x` for `self -> peer`.
        let mut sender_shares: Vec<Vec<SecretVec<Value>>> = Vec::with_capacity(peer_count);

        for i in 0..peer_count {
            let peer = peers_copy[i];
            let ctr = pair_counters[i];
            let delta = sender_deltas[i];
            let peer_q = &k_cols[i];
            let mut payload = SecretVec::with_capacity(ole_words_per_peer);
            let mut peer_s = Vec::with_capacity(kinds.len());

            for (item_idx, &kind) in kinds.iter().enumerate() {
                let l_bits = kind.choice_words() * 64;
                let base_b = item_bit_offsets[item_idx];
                let wlen = kind.words_len();
                let d_self = local_d[item_idx];
                let mut s_vec = SecretVec::with_capacity(l_bits);
                for l in 0..l_bits {
                    let b = base_b + l;
                    let q_row = Secret(row128_of(peer_q, b));
                    let q_xor = Secret(*q_row ^ delta);
                    let pad0 = Secret(ro_pad(kind, my_party, peer, ctr, b, *q_row));
                    let pad1 = Secret(ro_pad(kind, my_party, peer, ctr, b, *q_xor));
                    let x_mask = Secret(kind.sample_xof(&mut self.rng));
                    let ct0 = Secret(kind.add(*pad0, *x_mask));
                    let ct1 = Secret(kind.add(*pad1, kind.add(*x_mask, d_self)));
                    payload.extend_from_slice(&ct0[..wlen]);
                    payload.extend_from_slice(&ct1[..wlen]);
                    s_vec.push(kind.neg(*x_mask));
                }
                peer_s.push(s_vec);
            }
            ole_to_send.push(payload);
            sender_shares.push(peer_s);
        }
        drop(k_cols);

        let (ole_out_digests, ole_in_digests, ole_received) =
            self.send_pairwise(&ole_to_send, ole_words_per_peer)?;
        drop(ole_to_send);

        // Decode Receiver shares `y_{peer -> self}` in constant time (selecting `ct_c` by bitmask).
        let mut receiver_shares: Vec<Vec<SecretVec<Value>>> = Vec::with_capacity(peer_count);
        for (i, ct_in) in ole_received.iter().enumerate() {
            let peer = peers_copy[i];
            let ctr = pair_counters[i];
            let peer_t0 = &t0_cols[i];
            let mut cursor = 0usize;
            let mut peer_y = Vec::with_capacity(kinds.len());

            for (item_idx, &kind) in kinds.iter().enumerate() {
                let l_bits = kind.choice_words() * 64;
                let base_b = item_bit_offsets[item_idx];
                let wlen = kind.words_len();
                let mut y_vec = SecretVec::with_capacity(l_bits);
                for l in 0..l_bits {
                    let b = base_b + l;
                    let mut ct0 = ZERO;
                    let mut ct1 = ZERO;
                    ct0[..wlen].copy_from_slice(&ct_in[cursor..cursor + wlen]);
                    ct1[..wlen].copy_from_slice(&ct_in[cursor + wlen..cursor + 2 * wlen]);
                    cursor += 2 * wlen;
                    if !kind.canonical(ct0) || !kind.canonical(ct1) {
                        return self.fail(Error::MultiplicationCheck);
                    }
                    let cb = c_bit(&c_own, b) == 1;
                    let ct_c = Secret(crate::limbs::ct_select(cb, ct1, ct0));
                    let t0_row = Secret(row128_of(peer_t0, b));
                    let pad_c = Secret(ro_pad(kind, peer, my_party, ctr, b, *t0_row));
                    y_vec.push(kind.sub(*ct_c, *pad_c));
                }
                peer_y.push(y_vec);
            }
            receiver_shares.push(peer_y);
        }
        drop(t0_cols);
        drop(ole_received);

        // Round C2: Commit-then-open LHL coin bound to BOTH Round-P2 and Round-P3 edge digests!
        let mut lhl_xof = self.commit_coin_with_edges(
            b"blind_lhl",
            &[
                (&kos_out_digests, &kos_in_digests),
                (&ole_out_digests, &ole_in_digests),
            ],
        )?;

        // Compress via Leftover Hash Lemma into `w_own[item]` (`Σ_p w_p = (Σ r_i)(Σ d_j)`).
        let total_w_words: usize = kinds.iter().map(|k| k.words_len()).sum();
        let mut encoded_w: SecretVec<u64> = SecretVec::with_capacity(total_w_words);

        for (item_idx, &kind) in kinds.iter().enumerate() {
            let l_bits = kind.choice_words() * 64;
            let base_b = item_bit_offsets[item_idx];
            let wlen = kind.words_len();
            let mut g_weights = Vec::with_capacity(l_bits);
            for _ in 0..l_bits {
                g_weights.push(kind.sample_xof(&mut lhl_xof));
            }
            let mut r_own = Secret(ZERO);
            for (l, &g) in g_weights.iter().enumerate() {
                let take = c_bit(&c_own, base_b + l) == 1;
                let term = crate::limbs::ct_select(take, g, ZERO);
                *r_own = kind.add(*r_own, term);
            }
            let mut w_item = Secret(kind.mul(*r_own, local_d[item_idx]));
            for i in 0..peer_count {
                for (l, &g) in g_weights.iter().enumerate() {
                    let sum_sy =
                        Secret(kind.add(sender_shares[i][item_idx][l], receiver_shares[i][item_idx][l]));
                    *w_item = kind.add(*w_item, kind.mul(g, *sum_sy));
                }
            }
            encoded_w.extend_from_slice(&w_item[..wlen]);
        }
        drop(local_d);
        drop(sender_shares);
        drop(receiver_shares);

        // Round C3: Commit-then-open blinded shares `w_p` and verify `Σ_p w_p == 0`!
        let opened_ws = self.commit_then_open(b"blind_sigma", &encoded_w, &[])?;
        let mut cursor = 0usize;
        let mut all_zero = true;
        for &kind in &kinds {
            let wlen = kind.words_len();
            let mut total = ZERO;
            for row in &opened_ws {
                let mut share = ZERO;
                share[..wlen].copy_from_slice(&row[cursor..cursor + wlen]);
                if !kind.canonical(share) {
                    return self.fail(Error::MultiplicationCheck);
                }
                total = kind.add(total, share);
            }
            all_zero &= total == ZERO;
            cursor += wlen;
        }
        if !all_zero {
            return self.fail(Error::MultiplicationCheck);
        }
        self.transcript_dirty = false;
        Ok(())
    }

    /// Reveal Boolean wires to the quorum without checking them yet; their
    /// MAC shares join the queue settled by the next [`Self::check`].
    fn partial_open(&mut self, wires: &[ABit]) -> Result<Vec<u64>, Error> {
        let own: SecretVec<u64> = wires.iter().map(|w| w.share()).collect();
        #[cfg(test)]
        if self.fault == Some(Fault::Equivocate) && !own.is_empty() {
            self.fault = None;
            let mut other = own.clone();
            other[0] ^= 1;
            let mut payloads: Vec<&[u64]> = vec![&own; self.peers.len()];
            payloads[0] = &other;
            return self.finish_partial_open(wires, &payloads, &own);
        }
        let payloads: Vec<&[u64]> = vec![&own; self.peers.len()];
        self.finish_partial_open(wires, &payloads, &own)
    }

    fn finish_partial_open(
        &mut self,
        wires: &[ABit],
        payloads: &[&[u64]],
        own: &[u64],
    ) -> Result<Vec<u64>, Error> {
        let shares = self.send(payloads, own)?;
        let mut out = vec![0u64; wires.len()];
        for share in &shares {
            for (acc, s) in out.iter_mut().zip(share.iter()) {
                *acc ^= s;
            }
        }
        self.pending_bits.extend_from_slice(&out);
        self.pending_bit_macs.extend(wires.iter().map(|w| w.mac()));
        Ok(out)
    }

    fn partial_open_fields(
        &mut self,
        shares: &[[Value; 2]],
        d: Domain,
    ) -> Result<Vec<Value>, Error> {
        let wlen = d.limbs_len();
        let own: SecretVec<u64> = shares
            .iter()
            .flat_map(|s| s[0][..wlen].iter().copied())
            .collect();
        let received = self.broadcast(&own)?;
        let mut out = vec![ZERO; shares.len()];
        for row in &received {
            for (acc, limbs) in out.iter_mut().zip(row.chunks_exact(wlen)) {
                let mut value = ZERO;
                value[..wlen].copy_from_slice(limbs);
                if !d.canonical(value) {
                    return self.fail(Error::InvalidConfiguration);
                }
                *acc = d.add(*acc, value);
            }
        }
        let pending = &mut self.pending_fields[ThresholdField::from_domain(d).index()];
        pending.values.extend_from_slice(&out);
        pending.macs.extend(shares.iter().map(|s| s[1]));
        Ok(out)
    }

    fn public_bit(&self, x: u64) -> ABit {
        let mac = match x {
            0 => 0,
            u64::MAX => self.ones_mac,
            _ => gf2_128_mul(self.boolean_key(), x as u128),
        };
        ABit::new(if self.first { x } else { 0 }, mac)
    }

    fn public_field(&self, value: Value, d: Domain) -> [Value; 2] {
        let key = self.field_key(ThresholdField::from_domain(d).index());
        [
            if self.first { value } else { ZERO },
            mac_scale(d, key, value),
        ]
    }

    fn take<V>(&mut self, taken: Result<Vec<V>, Error>, count: usize) -> Result<Vec<V>, Error> {
        match taken {
            Ok(items) if items.len() == count => Ok(items),
            Ok(_) => self.fail(Error::InvalidConfiguration),
            Err(error) => self.fail(error),
        }
    }

    fn field_share_valid(d: Domain, share: &FieldShare) -> bool {
        d.canonical(share.0[0]) && mac_canonical(d, share.0[1])
    }

    fn input(&mut self, own: &[u64], uniform: bool) -> Result<Word<ABit>, Error> {
        if self.is_failed() {
            return Err(Error::MultiplicationCheck);
        }
        let taken = self.transport.take_auth_words(own.len());
        let masks = self.take(taken, own.len())?;
        // The mask is itself lane-uniform in the uniform case: its single
        // authenticated bit (lane 0) is spread over all lanes, so the masked
        // word reveals nothing and the shared input is uniform by construction.
        let masks: SecretVec<ABit> = masks
            .iter()
            .map(|r| {
                if uniform {
                    ABit::new(
                        0u64.wrapping_sub(r.share & 1),
                        gf2_128_mul(r.macs[0], u64::MAX as u128),
                    )
                } else {
                    r.bit()
                }
            })
            .collect();
        #[allow(unused_mut)]
        let mut masked: SecretVec<u64> = own
            .iter()
            .zip(masks.iter())
            .map(|(&x, r)| x ^ r.share())
            .collect();
        #[cfg(test)]
        if uniform && self.fault == Some(Fault::SplitInput) && !masked.is_empty() {
            self.fault = None;
            masked[0] ^= 1;
        }
        let received = self.broadcast(&masked)?;
        let mut public = vec![0u64; own.len()];
        for (position, row) in received.iter().enumerate() {
            if uniform && row.iter().any(|&w| w != 0 && w != u64::MAX) {
                let culprit = self.config.quorum[position];
                return self.fail(Error::Disagreement(culprit));
            }
            for (acc, w) in public.iter_mut().zip(row.iter()) {
                *acc ^= w;
            }
        }
        Ok(masks
            .iter()
            .zip(public)
            .map(|(&r, e)| r ^ self.public_bit(e))
            .collect())
    }
}

impl<T: Transport> Core for SpdzEngine<T> {
    type Bit = ABit;

    #[inline]
    fn quorum_position(&self) -> (usize, usize) {
        let pos = self
            .config
            .quorum
            .iter()
            .position(|&p| p == self.party)
            .unwrap_or(0);
        (pos, self.config.quorum.len())
    }

    #[inline]
    fn constant(&self, x: u64) -> ABit {
        self.public_bit(x)
    }

    fn share(&mut self, own: &[u64]) -> Result<Word<ABit>, Error> {
        self.input(own, false)
    }

    fn share_masked(&mut self, own: &[u64]) -> Result<Word<ABit>, Error> {
        self.input(own, false)
    }

    fn share_uniform_lanes(&mut self, own: &[u64]) -> Result<Word<ABit>, Error> {
        if own.iter().any(|&w| w != 0 && w != u64::MAX) {
            return Err(Error::InvalidConfiguration);
        }
        self.input(own, true)
    }

    fn fshare_many(
        &mut self,
        own_words: &[SecretVec<Value>],
        d: Domain,
    ) -> Result<Vec<FieldWord>, Error> {
        if self.is_failed() {
            return Err(Error::MultiplicationCheck);
        }
        if own_words.is_empty() {
            return Ok(Vec::new());
        }
        let k = own_words.len();
        let count = k * 64;
        let taken = self
            .transport
            .take_field_randoms(ThresholdField::from_domain(d), count);
        let randoms = self.take(taken, count)?;
        if randoms.iter().any(|r| !Self::field_share_valid(d, r)) {
            return self.fail(Error::InvalidConfiguration);
        }
        let wlen = d.limbs_len();
        let mut masked_flat: SecretVec<u64> = SecretVec::with_capacity(count * wlen);
        let mut rand_iter = randoms.iter();
        for word in own_words {
            if word.len() != 64 {
                return self.fail(Error::InvalidConfiguration);
            }
            for &val in word.iter() {
                if !d.canonical(val) {
                    return self.fail(Error::InvalidConfiguration);
                }
                let r = rand_iter.next().unwrap();
                let diff = Secret(d.sub(val, r.0[0]));
                masked_flat.extend_from_slice(&diff[..wlen]);
            }
        }
        let received = self.broadcast(&masked_flat)?;
        let mut public_sums = vec![ZERO; count];
        for (pos, row) in received.iter().enumerate() {
            for (acc, limbs) in public_sums.iter_mut().zip(row.chunks_exact(wlen)) {
                let mut v = ZERO;
                v[..wlen].copy_from_slice(limbs);
                if !d.canonical(v) {
                    let culprit = self.config.quorum[pos];
                    return self.fail(Error::Disagreement(culprit));
                }
                *acc = d.add(*acc, v);
            }
        }
        let mut out = Vec::with_capacity(k);
        for (r_chunk, pub_chunk) in randoms.chunks_exact(64).zip(public_sums.chunks_exact(64)) {
            let mut fw = FieldWord::with_capacity(64);
            for (r, &p_val) in r_chunk.iter().zip(pub_chunk) {
                let pub_sh = self.public_field(p_val, d);
                fw.push([d.add(r.0[0], pub_sh[0]), mac_add(d, r.0[1], pub_sh[1])]);
            }
            out.push(fw);
        }
        Ok(out)
    }

    fn broadcast_bytes(&mut self, own: &[u8]) -> Result<Vec<Vec<u8>>, Error> {
        self.check()?;
        let word_len = 1 + own.len().div_ceil(8);
        let mut words: SecretVec<u64> = SecretVec::with_capacity(word_len);
        words.push(own.len() as u64);
        for chunk in own.chunks(8) {
            let mut buf = [0u8; 8];
            buf[..chunk.len()].copy_from_slice(chunk);
            words.push(u64::from_le_bytes(buf));
            ct_zeroize_bytes(&mut buf);
        }
        let received = self.broadcast(&words)?;
        let mut out = Vec::with_capacity(received.len());
        for row in &received {
            if row.len() != word_len || row[0] != own.len() as u64 {
                return self.fail(Error::InvalidConfiguration);
            }
            let n = row[0] as usize;
            let mut bytes = Vec::with_capacity(n);
            for &w in &row[1..] {
                let b = w.to_le_bytes();
                let take = (n - bytes.len()).min(8);
                bytes.extend_from_slice(&b[..take]);
            }
            out.push(bytes);
        }
        Ok(out)
    }

    fn and_into(&mut self, pairs: &[(ABit, ABit)], out: &mut Word<ABit>) -> Result<(), Error> {
        out.clear();
        if self.is_failed() {
            return Err(Error::MultiplicationCheck);
        }
        if pairs.is_empty() {
            return Ok(());
        }
        let taken = self.transport.take_boolean_triples(pairs.len());
        let triples = self.take(taken, pairs.len())?;
        let k = pairs.len();
        let mut masked: SecretVec<ABit> = SecretVec::with_capacity(2 * k);
        for (&(x, _), t) in pairs.iter().zip(&triples) {
            masked.push(x ^ t.a.bit());
        }
        for (&(_, y), t) in pairs.iter().zip(&triples) {
            masked.push(y ^ t.b.bit());
        }
        #[cfg(test)]
        if let Some(Fault::BeaverOpening { lane }) = self.fault {
            self.fault = None;
            masked[0].0[0] ^= 1 << (lane & 63);
        }
        let opened = self.partial_open(&masked)?;
        let (d, e) = opened.split_at(k);
        out.reserve(k);
        for ((t, &d), &e) in triples.iter().zip(d).zip(e) {
            let share = t.c.share ^ (d & t.b.share) ^ (e & t.a.share);
            let mac =
                pack_macs(&t.c.macs, u64::MAX) ^ pack_macs(&t.b.macs, d) ^ pack_macs(&t.a.macs, e);
            out.push(ABit::new(share, mac) ^ self.public_bit(d & e));
        }
        #[cfg(test)]
        if let Some(Fault::BeaverOutput { lane }) = self.fault {
            self.fault = None;
            out[0].0[0] ^= 1 << (lane & 63);
        }
        Ok(())
    }

    fn verify_all_pending(&mut self) -> Result<(), Error> {
        self.check()
    }

    fn open(&mut self, bits: &[ABit]) -> Result<Vec<u64>, Error> {
        self.check()?;
        #[cfg(test)]
        if let Some(Fault::FlipOpenedShare { lane }) = self.fault
            && !bits.is_empty()
        {
            self.fault = None;
            let mut forged: SecretVec<ABit> = bits.iter().copied().collect();
            forged[0].0[0] ^= 1 << (lane & 63);
            let opened = self.partial_open(&forged)?;
            self.check()?;
            return Ok(opened);
        }
        #[cfg(test)]
        if self.fault == Some(Fault::WrongMac) && !bits.is_empty() {
            self.fault = None;
            let mut forged: SecretVec<ABit> = bits.iter().copied().collect();
            forged[0].0[1] ^= 1;
            let opened = self.partial_open(&forged)?;
            self.check()?;
            return Ok(opened);
        }
        let opened = self.partial_open(bits)?;
        self.check()?;
        Ok(opened)
    }

    fn open_lanes(&mut self, bits: &[ABit], mask: u64) -> Result<Vec<u64>, Error> {
        if mask == u64::MAX {
            return self.open(bits);
        }
        if self.is_failed() {
            return Err(Error::MultiplicationCheck);
        }
        // Hidden lanes are one-time padded with authenticated random bits.
        let taken = self.transport.take_auth_words(bits.len());
        let pads = self.take(taken, bits.len())?;
        let padded: SecretVec<ABit> = bits
            .iter()
            .zip(&pads)
            .map(|(&b, r)| b ^ ABit::new(r.share & !mask, pack_macs(&r.macs, !mask)))
            .collect();
        let mut opened = self.open(&padded)?;
        for word in &mut opened {
            *word &= mask;
        }
        Ok(opened)
    }

    fn agree(&mut self, root: [u8; 32]) -> Result<(), Error> {
        self.check()?;
        let own = words32(&root);
        let received = self.broadcast(&own)?;
        for (position, row) in received.iter().enumerate() {
            if row[..] != own[..] {
                let culprit = self.config.quorum[position];
                return self.fail(Error::Disagreement(culprit));
            }
        }
        Ok(())
    }

    fn poison(&mut self) {
        self.failed = true;
        self.keys.wipe();
        #[cfg(any(feature = "std", test))]
        {
            if let Some(slot) = &self.escrow_slot {
                slot.lock().unwrap_or_else(|e| e.into_inner()).wipe();
            }
            if let Some(escrow) = &self.batch_escrow {
                escrow.poison_all();
            }
            if let Some(cancelled) = &self.batch_cancelled {
                cancelled.store(true, core::sync::atomic::Ordering::SeqCst);
            }
        }
        qsag_asm::volatile_fill(core::slice::from_mut(&mut self.ones_mac), 0);
        self.pending_bits.clear();
        self.pending_bit_macs.clear();
        for pending in &mut self.pending_fields {
            pending.values.clear();
            pending.macs.clear();
        }
    }

    fn fconstant(&self, value: Value, d: Domain) -> FieldWord {
        vec![self.public_field(value, d); 64].into()
    }

    fn fscale_lanes(&self, a: &FieldWord, by: &[Value], d: Domain) -> FieldWord {
        a.iter()
            .zip(by)
            .map(|(a, by)| [d.mul(a[0], *by), mac_scale(d, a[1], *by)])
            .collect()
    }

    fn fadd(&self, a: &FieldWord, b: &FieldWord, d: Domain) -> FieldWord {
        a.iter()
            .zip(b.iter())
            .map(|(a, b)| {
                let (a, b) = (*a, *b);
                [d.add(a[0], b[0]), mac_add(d, a[1], b[1])]
            })
            .collect()
    }

    fn fsub(&self, a: &FieldWord, b: &FieldWord, d: Domain) -> FieldWord {
        a.iter()
            .zip(b.iter())
            .map(|(a, b)| {
                let (a, b) = (*a, *b);
                [d.sub(a[0], b[0]), mac_sub(d, a[1], b[1])]
            })
            .collect()
    }

    fn fscale(&self, a: &FieldWord, by: Value, d: Domain) -> FieldWord {
        a.iter()
            .map(|a| {
                let a = *a;
                [d.mul(a[0], by), mac_scale(d, a[1], by)]
            })
            .collect()
    }

    fn frandom(&mut self, d: Domain) -> Result<FieldWord, Error> {
        if self.is_failed() {
            return Err(Error::MultiplicationCheck);
        }
        let taken = self
            .transport
            .take_field_randoms(ThresholdField::from_domain(d), 64);
        let randoms = self.take(taken, 64)?;
        if randoms.iter().any(|r| !Self::field_share_valid(d, r)) {
            return self.fail(Error::InvalidConfiguration);
        }
        Ok(randoms.iter().map(|r| r.0).collect())
    }

    fn fmul_many(
        &mut self,
        pairs: &[(&FieldWord, &FieldWord)],
        d: Domain,
    ) -> Result<Vec<FieldWord>, Error> {
        if self.is_failed() {
            return Err(Error::MultiplicationCheck);
        }
        if pairs.is_empty() {
            return Ok(Vec::new());
        }
        let count = pairs.len() * 64;
        let taken = self
            .transport
            .take_field_triples(ThresholdField::from_domain(d), count);
        let triples = self.take(taken, count)?;
        if triples
            .iter()
            .any(|t| t.0.iter().any(|s| !Self::field_share_valid(d, s)))
        {
            return self.fail(Error::InvalidConfiguration);
        }
        let mut masked: SecretVec<[Value; 2]> = SecretVec::with_capacity(2 * count);
        let lanes = || pairs.iter().flat_map(|(a, b)| a.iter().zip(b.iter()));
        for ((x, _), t) in lanes().zip(&triples) {
            let x = *x;
            let a = t.0[0].0;
            masked.push([d.sub(x[0], a[0]), mac_sub(d, x[1], a[1])]);
        }
        for ((_, y), t) in lanes().zip(&triples) {
            let y = *y;
            let b = t.0[1].0;
            masked.push([d.sub(y[0], b[0]), mac_sub(d, y[1], b[1])]);
        }
        #[cfg(test)]
        if let Some(Fault::FieldBeaverOpening { lane }) = self.fault {
            self.fault = None;
            masked[lane & 63][0] = d.add(masked[lane & 63][0], ONE);
        }
        let opened = self.partial_open_fields(&masked, d)?;
        let (delta, epsilon) = opened.split_at(count);
        let products: FieldWord = triples
            .iter()
            .zip(delta)
            .zip(epsilon)
            .map(|((t, &de), &ep)| {
                let [a, b, c] = [t.0[0].0, t.0[1].0, t.0[2].0];
                let constant = self.public_field(d.mul(de, ep), d);
                let share = d.add(
                    d.add(c[0], constant[0]),
                    d.add(d.mul(de, b[0]), d.mul(ep, a[0])),
                );
                let mac = mac_add(
                    d,
                    mac_add(d, c[1], constant[1]),
                    mac_add(d, mac_scale(d, b[1], de), mac_scale(d, a[1], ep)),
                );
                [share, mac]
            })
            .collect();
        Ok(products
            .chunks_exact(64)
            .map(|w| w.iter().copied().collect())
            .collect())
    }

    fn fopen_many(&mut self, words: &[FieldWord], d: Domain) -> Result<Vec<Vec<Value>>, Error> {
        if words.is_empty() {
            return Ok(Vec::new());
        }
        self.check()?;
        let flat: SecretVec<[Value; 2]> = words.iter().flat_map(|w| w.iter().copied()).collect();
        let opened = self.partial_open_fields(&flat, d)?;
        self.check()?;
        Ok(opened.chunks_exact(64).map(|v| v.to_vec()).collect())
    }

    /// `[x]_p = c + (1 − 2c)·[r]_p` for the public masked bit `c = x ⊕ r` of a
    /// doubly authenticated random bit `r`: no multiplication and no input
    /// from any party, so a party cannot substitute a different bit.
    fn lift_bits_many(&mut self, bits: &[ABit], d: Domain) -> Result<Vec<FieldWord>, Error> {
        if self.is_failed() {
            return Err(Error::MultiplicationCheck);
        }
        if bits.is_empty() {
            return Ok(Vec::new());
        }
        let taken = self
            .transport
            .take_dabits(ThresholdField::from_domain(d), bits.len());
        let dabits = self.take(taken, bits.len())?;
        if dabits
            .iter()
            .any(|r| r.field.iter().any(|s| !Self::field_share_valid(d, s)))
        {
            return self.fail(Error::InvalidConfiguration);
        }
        #[allow(unused_mut)]
        let mut masked: SecretVec<ABit> = bits
            .iter()
            .zip(&dabits)
            .map(|(&x, r)| x ^ r.bits.bit())
            .collect();
        #[cfg(test)]
        if let Some(Fault::ConversionBit { lane }) = self.fault {
            self.fault = None;
            masked[0].0[0] ^= 1 << (lane & 63);
        }
        let opened = self.partial_open(&masked)?;
        let one = self.public_field(ONE, d);
        Ok(dabits
            .iter()
            .zip(opened)
            .map(|(r, c)| {
                (0..64)
                    .map(|lane| {
                        let r = r.field[lane].0;
                        if (c >> lane) & 1 == 0 {
                            r
                        } else {
                            [d.sub(one[0], r[0]), mac_sub(d, one[1], r[1])]
                        }
                    })
                    .collect()
            })
            .collect())
    }

    fn bits_to_field_many(
        &mut self,
        words: &[Word<ABit>],
        d: Domain,
    ) -> Result<Vec<FieldWord>, Error> {
        let mut out = Vec::with_capacity(words.len());
        // Each lifted bit holds 64 field lanes; bound the scratch per round.
        let words_per_batch = (1024 / d.width()).max(1);
        for chunk in words.chunks(words_per_batch) {
            let bits: Word<ABit> = chunk.iter().flat_map(|word| word.iter().copied()).collect();
            let lifted = self.lift_bits_many(&bits, d)?;
            let mut offset = 0;
            for word in chunk {
                out.push(self.weighted_sum(&lifted[offset..offset + word.len()], d));
                offset += word.len();
            }
        }
        Ok(out)
    }

    /// Open `v − ρ` for a random `ρ` known bit by bit, then add the public
    /// difference back inside the Boolean circuit. `ρ` is assembled from
    /// doubly authenticated bits, so its field and Boolean forms agree.
    fn field_to_bits_many(
        &mut self,
        words: &[&FieldWord],
        d: Domain,
    ) -> Result<Vec<Word<ABit>>, Error> {
        if words.is_empty() {
            return Ok(Vec::new());
        }
        let width = d.width();
        if matches!(d, Domain::PallasFp | Domain::BlsFp) {
            // Wide zero-rejection daBit mask (`n_lo = width - 1` + `136` high bits,
            // `< 2^-129` statistical distance across all 64 lanes, 0% rejection).
            let n_lo = width - 1;
            let n_hi = 136usize;
            let per_word = n_lo + n_hi;
            let total_dabits = words.len() * per_word;
            let taken = self
                .transport
                .take_dabits(ThresholdField::from_domain(d), total_dabits);
            let dabits = self.take(taken, total_dabits)?;
            if dabits
                .iter()
                .any(|r| r.field.iter().any(|s| !Self::field_share_valid(d, s)))
            {
                return self.fail(Error::InvalidConfiguration);
            }
            let zero_bit = self.public_bit(0);
            let mut lo_words: Vec<Word<ABit>> = Vec::with_capacity(words.len());
            let mut hi_bits: Vec<Word<ABit>> = Vec::with_capacity(words.len());
            let mut rho_field: Vec<FieldWord> = Vec::with_capacity(words.len());
            for chunk in dabits.chunks_exact(per_word) {
                let mut lo_w: Word<ABit> = chunk[..n_lo].iter().map(|r| r.bits.bit()).collect();
                lo_w.push(zero_bit);
                lo_words.push(lo_w);
                hi_bits.push(chunk[n_lo..].iter().map(|r| r.bits.bit()).collect());
                let lifted: Vec<FieldWord> = chunk
                    .iter()
                    .map(|r| r.field.iter().map(|s| s.0).collect())
                    .collect();
                rho_field.push(self.weighted_sum(&lifted, d));
            }
            #[allow(unused_mut)]
            let mut masked: SecretVec<[Value; 2]> = words
                .iter()
                .zip(&rho_field)
                .flat_map(|(v, r)| {
                    v.iter().zip(r.iter()).map(|(v, r)| {
                        let v = *v;
                        [d.sub(v[0], r[0]), mac_sub(d, v[1], r[1])]
                    })
                })
                .collect();
            #[cfg(test)]
            if let Some(Fault::ConversionField { lane }) = self.fault {
                self.fault = None;
                masked[lane & 63][0] = d.add(masked[lane & 63][0], ONE);
            }
            let opened = self.partial_open_fields(&masked, d)?;
            let public: Vec<Word<ABit>> = opened
                .chunks_exact(64)
                .map(|lanes| {
                    (0..width)
                        .map(|bit| {
                            self.public_bit(lanes.iter().enumerate().fold(
                                0,
                                |word, (lane, v)| {
                                    word | (((v[bit / 64] >> (bit % 64)) & 1) << lane)
                                },
                            ))
                        })
                        .collect()
                })
                .collect();

            // Precompute public powers `C_k = 2^{n_lo + k} mod p` (`k = 0..136`) and fold all
            // `138` summands across `words.len()` in an 8-round `field_add_many` tree.
            let mut pow = ONE;
            for _ in 0..n_lo {
                pow = d.add(pow, pow);
            }
            let mut tree: Vec<Vec<Word<ABit>>> = Vec::with_capacity(2 + n_hi);
            tree.push(public);
            tree.push(lo_words);
            for k in 0..n_hi {
                let c_k = pow;
                pow = d.add(pow, pow);
                let term_k: Vec<Word<ABit>> = hi_bits
                    .iter()
                    .map(|hb| {
                        let b_k = hb[k];
                        (0..width)
                            .map(|bit| {
                                if ((c_k[bit / 64] >> (bit % 64)) & 1) != 0 {
                                    b_k
                                } else {
                                    zero_bit
                                }
                            })
                            .collect()
                    })
                    .collect();
                tree.push(term_k);
            }
            while tree.len() > 1 {
                let pairs_count = tree.len() / 2;
                let k_words = words.len();
                let mut lhs = Vec::with_capacity(pairs_count * k_words);
                let mut rhs = Vec::with_capacity(pairs_count * k_words);
                for pair in tree.chunks_exact(2) {
                    lhs.extend(pair[0].iter().cloned());
                    rhs.extend(pair[1].iter().cloned());
                }
                let sums = self.field_add_many(&lhs, &rhs, d)?;
                let mut next: Vec<Vec<Word<ABit>>> = sums
                    .chunks_exact(k_words)
                    .map(|chunk| chunk.to_vec())
                    .collect();
                if tree.len() % 2 == 1 {
                    next.push(tree.pop().unwrap());
                }
                tree = next;
            }
            return Ok(tree.pop().unwrap());
        }
        let mut rho_bits: Vec<Word<ABit>> = Vec::with_capacity(words.len());
        let mut rho_field: Vec<FieldWord> = Vec::with_capacity(words.len());
        for _ in words {
            let (bits, field) = self.random_bits_of_field(d)?;
            rho_bits.push(bits);
            rho_field.push(field);
        }
        #[allow(unused_mut)]
        let mut masked: SecretVec<[Value; 2]> = words
            .iter()
            .zip(&rho_field)
            .flat_map(|(v, r)| {
                v.iter().zip(r.iter()).map(|(v, r)| {
                    let v = *v;
                    [d.sub(v[0], r[0]), mac_sub(d, v[1], r[1])]
                })
            })
            .collect();
        #[cfg(test)]
        if let Some(Fault::ConversionField { lane }) = self.fault {
            self.fault = None;
            masked[lane & 63][0] = d.add(masked[lane & 63][0], ONE);
        }
        let opened = self.partial_open_fields(&masked, d)?;
        let public: Vec<Word<ABit>> = opened
            .chunks_exact(64)
            .map(|lanes| {
                (0..width)
                    .map(|bit| {
                        self.public_bit(lanes.iter().enumerate().fold(0, |word, (lane, v)| {
                            word | (((v[bit / 64] >> (bit % 64)) & 1) << lane)
                        }))
                    })
                    .collect()
            })
            .collect();
        self.field_add_many(&public, &rho_bits, d)
    }
}

impl<T: Transport> SpdzEngine<T> {
    fn weighted_sum(&self, bits: &[FieldWord], d: Domain) -> FieldWord {
        let mut sum: FieldWord = vec![self.public_field(ZERO, d); 64].into();
        let mut weight = ONE;
        for bit in bits {
            sum = self.fadd(&sum, &self.fscale(bit, weight, d), d);
            weight = d.add(weight, weight);
        }
        sum
    }

    /// A uniformly random field word together with its binary encoding.
    ///
    /// The value is `Σ 2^b r_b` over `width` doubly authenticated bits. For
    /// Goldilocks the candidate is rejected (and its acceptance bit opened)
    /// unless it is below the modulus in every lane, so the accepted value is
    /// exactly uniform. For the 255/256-bit fields the excess above the
    /// modulus has probability below `2^-222` per lane and is not sampled out.
    fn random_bits_of_field(&mut self, d: Domain) -> Result<(Word<ABit>, FieldWord), Error> {
        let width = d.width();
        for _ in 0..4 {
            let taken = self
                .transport
                .take_dabits(ThresholdField::from_domain(d), width);
            let dabits = self.take(taken, width)?;
            if dabits
                .iter()
                .any(|r| r.field.iter().any(|s| !Self::field_share_valid(d, s)))
            {
                return self.fail(Error::InvalidConfiguration);
            }
            let bits: Word<ABit> = dabits.iter().map(|r| r.bits.bit()).collect();
            let lifted: Vec<FieldWord> = dabits
                .iter()
                .map(|r| r.field.iter().map(|s| s.0).collect())
                .collect();
            let field = self.weighted_sum(&lifted, d);
            if d != Domain::Gold {
                return Ok((bits, field));
            }
            let below = self.less_than_modulus_many(core::slice::from_ref(&bits), d)?;
            if self.open(&below)?[0] == u64::MAX {
                return Ok((bits, field));
            }
        }
        self.fail(Error::InvalidProof)
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::threshold_prep::FixtureDealer;
    use std::{
        boxed::Box,
        collections::BTreeMap,
        sync::{Arc, Mutex, mpsc},
        time::Duration,
    };

    enum Batch {
        Triples(Vec<Option<Vec<BooleanTriple>>>),
        Words(Vec<Option<Vec<AuthWord>>>),
        FieldTriples(Vec<Option<Vec<FieldTriple>>>),
        FieldRandoms(Vec<Option<Vec<FieldShare>>>),
        DaBits(Vec<Option<Vec<DaBitWord>>>),
    }
    /// Shared fixture: the first quorum member to reach a request generates
    /// the material for everyone; all members must make the same requests.
    struct Supply {
        dealer: FixtureDealer,
        batches: BTreeMap<usize, (std::string::String, Batch)>,
    }
    enum Source {
        Fixture(Arc<Mutex<Supply>>),
        /// Material produced ahead of time by a preprocessing ceremony.
        Stored(Box<crate::threshold_prep::PartyPreprocessing>),
    }
    pub(crate) struct Network {
        position: usize,
        config: ThresholdConfig,
        senders: Vec<mpsc::Sender<Envelope>>,
        incoming: mpsc::Receiver<Envelope>,
        pending: BTreeMap<(u64, usize), Envelope>,
        source: Source,
        round: usize,
    }
    impl Network {
        fn supplied<V>(
            &mut self,
            request: std::string::String,
            make: impl FnOnce(&mut FixtureDealer) -> Batch,
            rows: impl FnOnce(&mut Batch) -> &mut Vec<Option<Vec<V>>>,
            stored: impl FnOnce(&mut crate::threshold_prep::PartyPreprocessing) -> Result<Vec<V>, Error>,
        ) -> Result<Vec<V>, Error> {
            let supply = match &mut self.source {
                Source::Stored(store) => return stored(store),
                Source::Fixture(supply) => supply,
            };
            let mut supply = supply.lock().unwrap();
            if !supply.batches.contains_key(&self.round) {
                let batch = make(&mut supply.dealer);
                supply.batches.insert(self.round, (request.clone(), batch));
            }
            let (expected, batch) = supply.batches.get_mut(&self.round).unwrap();
            assert_eq!(
                *expected, request,
                "quorum members disagree on preprocessing"
            );
            let rows = rows(batch);
            let mine = rows[self.position].take().unwrap();
            if rows.iter().all(Option::is_none) {
                supply.batches.remove(&self.round);
            }
            self.round += 1;
            Ok(mine)
        }
    }
    fn options<V>(rows: Vec<Vec<V>>) -> Vec<Option<Vec<V>>> {
        rows.into_iter().map(Some).collect()
    }
    impl Transport for Network {
        fn exchange_many(&mut self, outgoing: Vec<Envelope>) -> Result<Vec<Envelope>, Error> {
            let sequence = outgoing[0].sequence;
            for envelope in outgoing {
                self.senders[envelope.recipient]
                    .send(envelope)
                    .map_err(|_| Error::Transport)?;
            }
            let mut received = Vec::new();
            for &peer in &self.config.quorum {
                if peer == self.config.quorum[self.position] {
                    continue;
                }
                let key = (sequence, peer);
                while !self.pending.contains_key(&key) {
                    let envelope = self
                        .incoming
                        .recv_timeout(Duration::from_secs(30))
                        .map_err(|_| Error::Transport)?;
                    assert!(
                        self.pending
                            .insert((envelope.sequence, envelope.sender), envelope)
                            .is_none()
                    );
                }
                received.push(self.pending.remove(&key).unwrap());
            }
            Ok(received)
        }
        fn take_boolean_triples(&mut self, count: usize) -> Result<Vec<BooleanTriple>, Error> {
            self.supplied(
                std::format!("triples {count}"),
                |d| Batch::Triples(options(d.boolean_triples(count))),
                |b| match b {
                    Batch::Triples(rows) => rows,
                    _ => unreachable!(),
                },
                |store| store.take_boolean_triples(count),
            )
        }
        fn take_auth_words(&mut self, count: usize) -> Result<Vec<AuthWord>, Error> {
            self.supplied(
                std::format!("words {count}"),
                |d| Batch::Words(options(d.auth_words(count))),
                |b| match b {
                    Batch::Words(rows) => rows,
                    _ => unreachable!(),
                },
                |store| store.take_auth_words(count),
            )
        }
        fn take_field_triples(
            &mut self,
            field: ThresholdField,
            count: usize,
        ) -> Result<Vec<FieldTriple>, Error> {
            self.supplied(
                std::format!("field triples {field:?} {count}"),
                |d| Batch::FieldTriples(options(d.field_triples(field, count))),
                |b| match b {
                    Batch::FieldTriples(rows) => rows,
                    _ => unreachable!(),
                },
                |store| store.take_field_triples(field, count),
            )
        }
        fn take_field_randoms(
            &mut self,
            field: ThresholdField,
            count: usize,
        ) -> Result<Vec<FieldShare>, Error> {
            self.supplied(
                std::format!("field randoms {field:?} {count}"),
                |d| Batch::FieldRandoms(options(d.field_randoms(field, count))),
                |b| match b {
                    Batch::FieldRandoms(rows) => rows,
                    _ => unreachable!(),
                },
                |store| store.take_field_randoms(field, count),
            )
        }
        fn take_dabits(
            &mut self,
            field: ThresholdField,
            count: usize,
        ) -> Result<Vec<DaBitWord>, Error> {
            self.supplied(
                std::format!("dabits {field:?} {count}"),
                |d| Batch::DaBits(options(d.dabits(field, count))),
                |b| match b {
                    Batch::DaBits(rows) => rows,
                    _ => unreachable!(),
                },
                |store| store.take_dabits(field, count),
            )
        }
    }
    pub(crate) fn keys(config: &ThresholdConfig, party: usize) -> Vec<[u8; 32]> {
        config
            .quorum
            .iter()
            .filter(|&&p| p != party)
            .map(|&p| {
                cshake256_framed_32(
                    b"TEST.THRESHOLD.KEY",
                    &[&[party.min(p) as u8, party.max(p) as u8]],
                )
            })
            .collect()
    }
    /// Run `f(party, MAC key share, transport)` on one thread per quorum
    /// member and return the results in quorum order. Preprocessing comes
    /// from the shared deterministic fixture, generated on demand.
    pub(crate) fn run<R: Send, F: Fn(usize, MacKeyShare, Network) -> R + Sync>(
        config: ThresholdConfig,
        f: F,
    ) -> Vec<R> {
        let dealer = FixtureDealer::new(&config, [13; 32]);
        let mac_keys = dealer.mac_key_shares();
        let supply = Arc::new(Mutex::new(Supply {
            dealer,
            batches: BTreeMap::new(),
        }));
        let parties = mac_keys
            .into_iter()
            .map(|keys| (keys, Source::Fixture(supply.clone())))
            .collect();
        run_parties(config, parties, f)
    }

    /// As [`run`], with each member's keys and stored material from a
    /// preprocessing ceremony, in quorum order.
    pub(crate) fn run_stored<R: Send, F: Fn(usize, MacKeyShare, Network) -> R + Sync>(
        config: ThresholdConfig,
        parties: Vec<(MacKeyShare, crate::threshold_prep::PartyPreprocessing)>,
        f: F,
    ) -> Vec<R> {
        let parties = parties
            .into_iter()
            .map(|(keys, store)| (keys, Source::Stored(Box::new(store))))
            .collect();
        run_parties(config, parties, f)
    }

    fn run_parties<R: Send, F: Fn(usize, MacKeyShare, Network) -> R + Sync>(
        config: ThresholdConfig,
        parties: Vec<(MacKeyShare, Source)>,
        f: F,
    ) -> Vec<R> {
        let (senders, receivers): (Vec<_>, Vec<_>) =
            (0..config.parties).map(|_| mpsc::channel()).unzip();
        let mut receivers: Vec<_> = receivers.into_iter().map(Some).collect();
        std::thread::scope(|scope| {
            let handles: Vec<_> = config
                .quorum
                .iter()
                .zip(parties)
                .enumerate()
                .map(|(position, (&party, (keys, source)))| {
                    let network = Network {
                        position,
                        config: config.clone(),
                        senders: senders.clone(),
                        incoming: receivers[party].take().unwrap(),
                        pending: BTreeMap::new(),
                        source,
                        round: 0,
                    };
                    let f = &f;
                    scope.spawn(move || f(party, keys, network))
                })
                .collect();
            handles.into_iter().map(|h| h.join().unwrap()).collect()
        })
    }
    pub(crate) fn engine(
        config: &ThresholdConfig,
        party: usize,
        mac_keys: MacKeyShare,
        network: Network,
    ) -> SpdzEngine<Network> {
        let mut engine = SpdzEngine::new(
            party,
            [9; 32],
            config.clone(),
            keys(config, party),
            mac_keys,
            network,
        )
        .unwrap();
        engine.mix_entropy(&[party as u8; 32]);
        engine
    }
    pub(crate) fn shamir_share(party: usize, threshold: usize, witness: &[u8; 32]) -> [u8; 32] {
        use qsag_core::field::tower::eval_poly_gf256;
        let x = TowerGf256((party + 1) as u8);
        core::array::from_fn(|byte| {
            let coeffs: Vec<TowerGf256> = (0..threshold)
                .map(|degree| {
                    if degree == 0 {
                        TowerGf256(witness[byte])
                    } else {
                        TowerGf256(
                            (byte as u8)
                                .wrapping_mul(31)
                                .wrapping_add(degree as u8)
                                .wrapping_mul(13),
                        )
                    }
                })
                .collect();
            eval_poly_gf256(&coeffs, x).0
        })
    }

    #[test]
    fn tower_gf256_and_poly0x11b_basis_isomorphism_and_shamir_roundtrip() {
        use qsag_asm::portable::gfni_poly_mul_u8;
        // 1. Exhaustively verify over all 256^2 byte pairs that `poly0x11b_to_t3_byte_ct`
        //    and `t3_to_poly0x11b_byte_ct` are exact mutually inverse field isomorphisms
        //    between AES `0x11b` and `qsag-core`'s Wiedemann `TowerGf256` (`T_3`).
        assert_eq!(poly0x11b_to_t3_byte_ct(0), 0);
        assert_eq!(poly0x11b_to_t3_byte_ct(1), 1);
        assert_eq!(t3_to_poly0x11b_byte_ct(0), 0);
        assert_eq!(t3_to_poly0x11b_byte_ct(1), 1);
        for a in 0u8..=255 {
            let ta = poly0x11b_to_t3_byte_ct(a);
            assert_eq!(t3_to_poly0x11b_byte_ct(ta), a);
            for b in [0u8, 1, 2, 3, 0x53, 0xca, 0xff, a] {
                let tb = poly0x11b_to_t3_byte_ct(b);
                assert_eq!(poly0x11b_to_t3_byte_ct(a ^ b), ta ^ tb);
                let prod_poly = gfni_poly_mul_u8(a, b);
                let prod_t3 = TowerGf256(ta).mul(TowerGf256(tb)).0;
                assert_eq!(poly0x11b_to_t3_byte_ct(prod_poly), prod_t3);
                assert_eq!(t3_to_poly0x11b_byte_ct(prod_t3), prod_poly);
            }
        }

        // 2. Roundtrip a 32-byte witness shared in legacy `0x11b` polynomial basis through
        //    `ThresholdConfig::shamir_contribution_poly0x11b` AND via explicit share conversion
        //    onto `TowerGf256`.
        let witness: [u8; 32] = core::array::from_fn(|i| (i as u8).wrapping_mul(37) ^ 0xa5);
        for (t, n, quorum) in [
            (2, 3, vec![0, 2]),
            (3, 5, vec![1, 3, 4]),
            (5, 9, vec![0, 2, 5, 7, 8]),
        ] {
            let cfg = ThresholdConfig::new(t, n, quorum).unwrap();
            let mut recon_poly = [0u8; 32];
            for &p in cfg.quorum() {
                let x = (p + 1) as u8;
                let poly_share: [u8; 32] = core::array::from_fn(|byte| {
                    let mut out = witness[byte];
                    let mut power = x;
                    for deg in 1..t {
                        let coeff = (byte as u8).wrapping_mul(19).wrapping_add(deg as u8 * 7);
                        out ^= gfni_poly_mul_u8(power, coeff);
                        power = gfni_poly_mul_u8(power, x);
                    }
                    out
                });
                let contrib = cfg.shamir_contribution_poly0x11b(p, &poly_share).unwrap();
                for (dst, c) in recon_poly.iter_mut().zip(contrib) {
                    *dst ^= c;
                }
            }
            assert_eq!(recon_poly, witness);
        }
    }

    #[test]
    fn shamir_quorums_cover_every_supported_threshold_and_size() {
        let witness = core::array::from_fn(|i| i as u8 * 7);
        for n in 2..=64 {
            for t in 2..=n {
                // Include nonconsecutive, high party identifiers.
                let quorum: Vec<_> = (n - t..n).collect();
                let cfg = ThresholdConfig::new(t, n, quorum).unwrap();
                let mut reconstructed = [0; 32];
                for &p in cfg.quorum() {
                    let share = shamir_share(p, t, &witness);
                    for (a, b) in reconstructed
                        .iter_mut()
                        .zip(cfg.shamir_contribution(p, &share).unwrap())
                    {
                        *a ^= b;
                    }
                }
                assert_eq!(reconstructed, witness, "{t}-of-{n}");
            }
        }
        let cfg = ThresholdConfig::new(2, 64, vec![0, 31, 63]).unwrap();
        let mut reconstructed = [0; 32];
        for &p in cfg.quorum() {
            for (a, b) in reconstructed.iter_mut().zip(
                cfg.shamir_contribution(p, &shamir_share(p, 2, &witness))
                    .unwrap(),
            ) {
                *a ^= b;
            }
        }
        assert_eq!(reconstructed, witness);
        for (t, n, q) in [
            (1, 3, vec![0, 1]),
            (4, 3, vec![0, 1, 2]),
            (2, 65, vec![0, 1]),
            (2, 3, vec![0]),
            (2, 3, vec![0, 0]),
            (2, 3, vec![1, 0]),
            (2, 3, vec![0, 3]),
        ] {
            assert!(ThresholdConfig::new(t, n, q).is_err());
        }
    }

    #[test]
    fn word_macs_are_linear_and_match_the_global_key() {
        let cfg = ThresholdConfig::new(3, 5, vec![0, 2, 4]).unwrap();
        let mut dealer = FixtureDealer::new(&cfg, [1; 32]);
        let words = dealer.auth_words(8);
        for item in 0..8 {
            let word = words.iter().fold(0, |w, row| w ^ row[item].share);
            for lanes in [u64::MAX, 0, 1, 0x8000_0000_0000_0000, 0xdead_beef_0123_4567] {
                let mac = words
                    .iter()
                    .fold(0, |m, row| m ^ pack_macs(&row[item].macs, lanes));
                assert_eq!(mac, dealer.boolean_mac_of(word & lanes));
            }
        }
        // X^k weights agree with field multiplication by the lane monomial.
        let macs: [u128; 64] = core::array::from_fn(|k| 0x1234_5678_9abc_def0_u128 << k | 1);
        let expected = (0..64).fold(0, |acc, k| acc ^ gf2_128_mul(macs[k], 1u128 << k));
        assert_eq!(pack_macs(&macs, u64::MAX), expected);
    }

    #[test]
    fn authenticated_engines_support_sparse_and_full_rosters() {
        for cfg in [
            ThresholdConfig::new(2, 64, vec![0, 63]).unwrap(),
            ThresholdConfig::new(3, 9, vec![1, 4, 8]).unwrap(),
            ThresholdConfig::new(16, 16, (0..16).collect()).unwrap(),
        ] {
            run(cfg.clone(), |party, mac_keys, network| {
                let mut engine = engine(&cfg, party, mac_keys, network);
                engine.agree([17; 32]).unwrap();
                let contribution = |p: usize, k: u64| k.wrapping_mul(p as u64 + 1);
                let a = engine.share(&[contribution(party, 0xa55a)]).unwrap();
                let b = engine.share(&[contribution(party, 0x81f0)]).unwrap();
                let c = engine.and(&[(a[0], b[0])]).unwrap();
                let total = |k| cfg.quorum.iter().fold(0, |v, &p| v ^ contribution(p, k));
                let mixed = c[0] ^ a[0] ^ engine.constant(0xffff);
                assert_eq!(
                    engine.open(&[c[0], mixed]).unwrap(),
                    vec![
                        total(0xa55a) & total(0x81f0),
                        (total(0xa55a) & total(0x81f0)) ^ total(0xa55a) ^ 0xffff
                    ]
                );
                // Only the selected lanes of a masked opening are revealed.
                let mask = 0x00ff_00ff_0f0f_3333;
                assert_eq!(
                    engine.open_lanes(&[a[0], c[0]], mask).unwrap(),
                    vec![total(0xa55a) & mask, total(0xa55a) & total(0x81f0) & mask]
                );
                let uniform = engine
                    .share_uniform_lanes(&[if party == cfg.quorum[0] { u64::MAX } else { 0 }, 0])
                    .unwrap();
                assert_eq!(engine.open(&uniform).unwrap(), vec![u64::MAX, 0]);
                for d in Domain::ALL_FIELDS {
                    let seven = [7, 0, 0, 0, 0, 0];
                    let a = engine.fconstant(seven, d);
                    let r = engine.frandom(d).unwrap();
                    let ar = engine.fadd(&a, &r, d);
                    let product = engine.fmul(&ar, &ar, d).unwrap();
                    let opened = engine.fopen_many(&[product, r], d).unwrap();
                    for (square, r) in opened[0].iter().zip(&opened[1]) {
                        let sum = d.add(seven, *r);
                        assert_eq!(*square, d.mul(sum, sum));
                    }
                }
                engine.agree([18; 32]).unwrap();
            });
        }
    }

    #[test]
    fn conversions_and_inverse_match_native() {
        let cfg = ThresholdConfig::new(3, 7, vec![1, 3, 6]).unwrap();
        run(cfg.clone(), |party, mac_keys, network| {
            let mut engine = engine(&cfg, party, mac_keys, network);
            for d in Domain::ALL_FIELDS {
                let value = d.sub(d.modulus(), ONE);
                let expected: Vec<Value> = (0..64)
                    .map(|lane| match lane % 3 {
                        0 => value,
                        1 => [17, 0, 0, 0, 0, 0],
                        _ => [lane as u64, 1, 0, 0, 0, 0]
                            .map(|x| if d == Domain::Gold { x & !1 } else { x }),
                    })
                    .map(|v| {
                        if d == Domain::Gold {
                            [v[0], 0, 0, 0, 0, 0]
                        } else {
                            v
                        }
                    })
                    .collect();
                let own: Vec<_> = (0..d.width())
                    .map(|bit| {
                        expected.iter().enumerate().fold(0, |v, (lane, x)| {
                            v | (((x[bit / 64] >> (bit % 64)) & 1) << lane)
                        })
                    })
                    .collect();
                // Three XOR contributions, none of them the value itself.
                let contribution: Vec<_> = own
                    .iter()
                    .enumerate()
                    .map(|(bit, &v)| match party {
                        1 => v ^ (bit as u64).wrapping_mul(0x12345678),
                        3 => (bit as u64).wrapping_mul(0x12345678) ^ 0xabcdef,
                        _ => 0xabcdef,
                    })
                    .collect();
                let bits = engine.share(&contribution).unwrap();
                let field = engine.bits_to_field(&bits, d).unwrap();
                let opened = engine
                    .fopen_many(&[field.iter().copied().collect()], d)
                    .unwrap();
                assert_eq!(opened[0], expected);
                let roundtrip = engine.field_to_bits(&field, d).unwrap();
                assert_eq!(engine.open(&roundtrip).unwrap(), own);
                let inverse = engine.finverse(&field, d).unwrap();
                let product = engine.fmul(&inverse, &field, d).unwrap();
                let encoded = engine.field_to_bits(&product, d).unwrap();
                let opened = engine.open(&encoded).unwrap();
                assert_eq!(opened[0], u64::MAX);
                assert!(opened[1..].iter().all(|&x| x == 0));
            }
        });
    }

    /// One custodian of a 3-of-5 quorum deviates once. Every honest custodian
    /// must abort inside `f` and must not obtain any opened value from it.
    fn cheat<F>(fault: Fault, cheater: usize, f: F)
    where
        F: Fn(&mut SpdzEngine<Network>, usize) -> Result<Vec<u64>, Error> + Sync,
    {
        let cfg = ThresholdConfig::new(3, 5, vec![0, 2, 4]).unwrap();
        // Control: with nobody deviating the same steps succeed and agree.
        let honest = run(cfg.clone(), |party, mac_keys, network| {
            let mut engine = engine(&cfg, party, mac_keys, network);
            let outcome = f(&mut engine, party);
            assert!(!engine.failed);
            outcome
        });
        let reference = honest[0].clone().expect("honest run must succeed");
        assert!(!reference.is_empty());
        assert!(
            honest
                .iter()
                .all(|outcome| outcome.as_ref() == Ok(&reference))
        );
        let outcomes = run(cfg.clone(), |party, mac_keys, network| {
            let mut engine = engine(&cfg, party, mac_keys, network);
            if party == cheater {
                engine.fault = Some(fault);
            }
            let outcome = f(&mut engine, party);
            assert!(
                party != cheater || engine.fault.is_none(),
                "{fault:?} was never injected"
            );
            // A poisoned engine refuses all further work and holds no keys.
            assert!(engine.failed);
            assert!(engine.keys.is_wiped());
            assert_eq!(engine.open(&[]), Err(Error::MultiplicationCheck));
            assert_eq!(engine.agree([0; 32]), Err(Error::MultiplicationCheck));
            assert!(engine.share(&[1]).is_err());
            outcome
        });
        for (position, outcome) in outcomes.iter().enumerate() {
            assert!(
                matches!(
                    outcome,
                    Err(Error::MultiplicationCheck) | Err(Error::Disagreement(_))
                ),
                "{fault:?}: custodian at position {position} got {outcome:?}"
            );
        }
    }

    fn inputs(engine: &mut SpdzEngine<Network>, party: usize) -> Result<(ABit, ABit), Error> {
        let a = engine.share(&[0x0123_4567_89ab_cdef_u64.rotate_left(party as u32)])?;
        let b = engine.share(&[0xfedc_ba98_7654_3210_u64.rotate_left(3 * party as u32)])?;
        Ok((a[0], b[0]))
    }

    #[test]
    fn flipped_wire_share_is_caught_before_the_opening_is_returned() {
        for cheater in [0, 2, 4] {
            for lane in [0, 31, 63] {
                cheat(Fault::FlipOpenedShare { lane }, cheater, |e, party| {
                    let (a, b) = inputs(e, party)?;
                    e.open(&[a ^ b])
                });
            }
        }
    }

    #[test]
    fn lying_in_a_beaver_opening_is_caught_before_the_product_opens() {
        for cheater in [0, 2, 4] {
            for lane in [0, 17, 63] {
                cheat(Fault::BeaverOpening { lane }, cheater, |e, party| {
                    let (a, b) = inputs(e, party)?;
                    let c = e.and(&[(a, b)])?;
                    // The lie is still undetected here; no honest custodian
                    // sends a share of the product before the check runs.
                    e.open(&c)
                });
                cheat(Fault::BeaverOutput { lane }, cheater, |e, party| {
                    let (a, b) = inputs(e, party)?;
                    let c = e.and(&[(a, b)])?;
                    e.open(&c)
                });
            }
        }
    }

    #[test]
    fn lying_in_a_field_beaver_opening_is_caught_in_every_field() {
        for d in Domain::ALL_FIELDS {
            for cheater in [0, 4] {
                cheat(Fault::FieldBeaverOpening { lane: 9 }, cheater, |e, _| {
                    let a = e.frandom(d)?;
                    let b = e.frandom(d)?;
                    let c = e.fmul(&a, &b, d)?;
                    let bits = e.field_to_bits(&c, d)?;
                    e.open(&bits)
                });
            }
        }
    }

    #[test]
    fn forged_conversion_bits_are_caught_in_both_directions() {
        for d in Domain::ALL_FIELDS {
            for cheater in [0, 2] {
                cheat(Fault::ConversionBit { lane: 5 }, cheater, |e, party| {
                    let (a, _) = inputs(e, party)?;
                    let lifted = e.lift_bits_many(&[a], d)?;
                    Ok(e.fopen_many(&lifted, d)?[0].iter().map(|v| v[0]).collect())
                });
                cheat(Fault::ConversionField { lane: 40 }, cheater, |e, _| {
                    let a = e.frandom(d)?;
                    let bits = e.field_to_bits(&a, d)?;
                    e.open(&bits)
                });
            }
        }
    }

    #[test]
    fn split_inputs_wrong_macs_and_equivocation_are_caught() {
        for cheater in [0, 2, 4] {
            cheat(Fault::SplitInput, cheater, |e, _| {
                let w = e.share_uniform_lanes(&[u64::MAX])?;
                e.open(&w)
            });
            cheat(Fault::WrongMac, cheater, |e, party| {
                let (a, b) = inputs(e, party)?;
                e.open(&[a ^ b])
            });
            cheat(Fault::Equivocate, cheater, |e, party| {
                let (a, b) = inputs(e, party)?;
                let c = e.and(&[(a, b)])?;
                e.open(&c)
            });
        }
    }

    #[test]
    fn stored_preprocessing_is_served_in_order_and_exhaustion_fails_closed() {
        use crate::threshold_prep::{Demand, PartyPreprocessing};
        let cfg = ThresholdConfig::new(3, 5, vec![0, 2, 4]).unwrap();
        let mut dealer = FixtureDealer::new(&cfg, [21; 32]);
        let field = ThresholdField::Goldilocks;
        let mut stores: Vec<PartyPreprocessing> =
            (0..3).map(|_| PartyPreprocessing::new()).collect();
        for (store, words) in stores.iter_mut().zip(dealer.auth_words(2)) {
            store.add_auth_words(words);
        }
        for (store, triples) in stores.iter_mut().zip(dealer.boolean_triples(1)) {
            store.add_boolean_triples(triples);
        }
        for (store, dabits) in stores.iter_mut().zip(dealer.dabits(field, 1)) {
            store.add_dabits(field, dabits);
        }
        let mut demand = Demand {
            boolean_triples: 1,
            auth_words: 2,
            ..Demand::default()
        };
        demand.dabits[field.index()] = 1;
        assert!(stores.iter().all(|store| store.remaining() == demand));
        let parties = dealer.mac_key_shares().into_iter().zip(stores).collect();
        run_stored(cfg.clone(), parties, |party, mac_keys, network| {
            let mut engine = engine(&cfg, party, mac_keys, network);
            let (a, b) = inputs(&mut engine, party).unwrap();
            let c = engine.and(&[(a, b)]).unwrap();
            let lifted = engine.lift_bits_many(&c, Domain::Gold).unwrap();
            let total = |k: u64, r: u32| {
                cfg.quorum
                    .iter()
                    .fold(0, |v, &p| v ^ k.rotate_left(r * p as u32))
            };
            let expected = total(0x0123_4567_89ab_cdef, 1) & total(0xfedc_ba98_7654_3210, 3);
            assert_eq!(engine.open(&c).unwrap(), vec![expected]);
            let opened = engine.fopen_many(&lifted, Domain::Gold).unwrap();
            for (lane, value) in opened[0].iter().enumerate() {
                assert_eq!(*value, [(expected >> lane) & 1, 0, 0, 0, 0, 0]);
            }
            // Everything stored has been used exactly once; one more request
            // fails closed, consumes nothing and poisons the engine.
            assert_eq!(
                engine.and(&[(a, b)]).err(),
                Some(Error::MissingPreprocessing)
            );
            assert!(engine.failed);
            assert_eq!(engine.open(&c), Err(Error::MultiplicationCheck));
        });
    }

    #[test]
    fn malformed_rounds_and_invalid_custody_are_rejected() {
        struct Altered;
        impl Transport for Altered {
            fn exchange_many(&mut self, out: Vec<Envelope>) -> Result<Vec<Envelope>, Error> {
                Ok(out
                    .iter()
                    .map(|m| Envelope {
                        sender: m.recipient,
                        recipient: m.sender,
                        sequence: m.sequence,
                        payload: m.payload.clone(),
                        tag: [0; 32],
                    })
                    .collect())
            }
        }
        struct Empty;
        impl Transport for Empty {}
        let cfg = ThresholdConfig::new(2, 64, vec![0, 63]).unwrap();
        let mac_keys = || FixtureDealer::new(&cfg, [3; 32]).mac_key_shares().remove(0);
        let state = |transport| {
            SpdzEngine::new(
                0,
                [9; 32],
                cfg.clone(),
                keys(&cfg, 0),
                mac_keys(),
                transport,
            )
        };
        let mut altered = state(Altered).unwrap();
        assert_eq!(altered.agree([1; 32]), Err(Error::Authentication(63)));
        assert_eq!(altered.agree([1; 32]), Err(Error::MultiplicationCheck));
        let mut empty =
            SpdzEngine::new(0, [9; 32], cfg.clone(), keys(&cfg, 0), mac_keys(), Empty).unwrap();
        assert_eq!(empty.share(&[1]).err(), Some(Error::MissingPreprocessing));
        assert_eq!(empty.open(&[]), Err(Error::MultiplicationCheck));
        let mut empty =
            SpdzEngine::new(0, [9; 32], cfg.clone(), keys(&cfg, 0), mac_keys(), Empty).unwrap();
        assert_eq!(empty.agree([1; 32]), Err(Error::InvalidConfiguration));
        assert_eq!(empty.agree([1; 32]), Err(Error::MultiplicationCheck));
        // Not a quorum member, wrong number of channel keys, non-canonical key share.
        assert!(
            SpdzEngine::new(1, [9; 32], cfg.clone(), keys(&cfg, 0), mac_keys(), Empty).is_err()
        );
        assert!(SpdzEngine::new(0, [9; 32], cfg.clone(), vec![], mac_keys(), Empty).is_err());
        let mut bad = mac_keys();
        bad.field[ThresholdField::Secp256k1.index()] = [u64::MAX; 6];
        assert!(SpdzEngine::new(0, [9; 32], cfg.clone(), keys(&cfg, 0), bad, Empty).is_err());
        assert!(
            crate::CoZkCustodianShare::new_shamir(
                1,
                cfg.clone(),
                [0; 32],
                [0; 32],
                [0; 32],
                keys(&cfg, 0),
                mac_keys(),
            )
            .is_err()
        );
        assert!(
            crate::CoZkCustodianShare::new_shamir(
                0,
                cfg.clone(),
                [0; 32],
                [0; 32],
                [0; 32],
                vec![],
                mac_keys()
            )
            .is_err()
        );
        for parties in [0, 1, 65, usize::MAX] {
            assert!(
                crate::CoZkCustodianShare::new_additive(
                    0,
                    parties,
                    [0; 32],
                    [0; 32],
                    [0; 32],
                    vec![],
                    mac_keys(),
                )
                .is_err()
            );
        }
        assert!(
            crate::CoZkCustodianShare::new_additive(
                63,
                64,
                [0; 32],
                [0; 32],
                [0; 32],
                vec![[1; 32]; 63],
                mac_keys(),
            )
            .is_ok()
        );
    }

    #[test]
    fn repeated_wire_fault_aborts_reveal_uniform_blinded_residuals_and_poison_all_workers() {
        // 1. Spy transport recording every opened broadcast message of party 0 while
        //    cheater party 4 injects a known wire fault (`e = 1`) across 16 repeated
        //    sessions under the SAME global MAC key `Δ`!
        //    In an unblinded SPDZ check (`Σ σ_p = χ_0 · Δ`), ANY SINGLE abort would let
        //    the attacker compute `Δ = χ_0^-1 · Σ σ_p` directly from the final broadcast.
        //    With sender-residual OLE blinding, the final `blind_sigma` opening sums to
        //    `W_k = R_k · (χ_{k,0} · Δ)` for fresh uniform `R_k ∈ GF(2^128)`, so dividing
        //    out `χ_{k,0}` yields independent uniform random elements `R_k · Δ` that
        //    never collide across sessions and never equal `Δ`!
        struct SpyTransport {
            inner: Network,
            recorded: Arc<Mutex<Vec<Vec<u64>>>>,
        }
        impl Transport for SpyTransport {
            fn exchange_many(&mut self, outgoing: Vec<Envelope>) -> Result<Vec<Envelope>, Error> {
                let bcast = (outgoing.len() >= 2 && outgoing[0].payload == outgoing[1].payload)
                    .then(|| outgoing[0].payload.clone());
                let incoming = self.inner.exchange_many(outgoing)?;
                if let Some(payload) = bcast {
                    self.recorded.lock().unwrap().push(payload);
                }
                Ok(incoming)
            }
            fn take_boolean_triples(&mut self, c: usize) -> Result<Vec<BooleanTriple>, Error> {
                self.inner.take_boolean_triples(c)
            }
            fn take_auth_words(&mut self, c: usize) -> Result<Vec<AuthWord>, Error> {
                self.inner.take_auth_words(c)
            }
            fn take_field_triples(
                &mut self,
                f: ThresholdField,
                c: usize,
            ) -> Result<Vec<FieldTriple>, Error> {
                self.inner.take_field_triples(f, c)
            }
            fn take_field_randoms(
                &mut self,
                f: ThresholdField,
                c: usize,
            ) -> Result<Vec<FieldShare>, Error> {
                self.inner.take_field_randoms(f, c)
            }
            fn take_dabits(&mut self, f: ThresholdField, c: usize) -> Result<Vec<DaBitWord>, Error> {
                self.inner.take_dabits(f, c)
            }
        }

        let cfg = ThresholdConfig::new(3, 5, vec![0, 2, 4]).unwrap();
        let master_dealer = FixtureDealer::new(&cfg, [0x77; 32]);
        let true_delta = master_dealer.boolean_mac_of(1);
        assert_ne!(true_delta, 0);
        let base_keys = master_dealer.mac_key_shares();

        let mut observed_w0 = Vec::new();
        for trial in 0..16u64 {
            let supply = Arc::new(Mutex::new(Supply {
                dealer: FixtureDealer::new(&cfg, [0x77; 32]),
                batches: BTreeMap::new(),
            }));
            // Fork fresh OT streams from the SAME underlying `MacKeyShare`s `(Δ, α_f)`.
            let trial_parties: Vec<_> = base_keys
                .iter()
                .map(|k| (k.fork_stream(b"ABORT_TRIAL", trial), Source::Fixture(supply.clone())))
                .collect();
            let spy_msgs: [Arc<Mutex<Vec<Vec<u64>>>>; 3] =
                core::array::from_fn(|_| Arc::new(Mutex::new(Vec::new())));
            let outcomes = run_parties(cfg.clone(), trial_parties, |party, mac_keys, network| {
                let pos = cfg.quorum.iter().position(|&p| p == party).unwrap();
                let spy = SpyTransport {
                    inner: network,
                    recorded: spy_msgs[pos].clone(),
                };
                let mut e = SpdzEngine::new(
                    party,
                    [trial as u8 + 1; 32],
                    cfg.clone(),
                    keys(&cfg, party),
                    mac_keys,
                    spy,
                )
                .unwrap();
                e.mix_entropy(&[(trial as u8).wrapping_mul(17) ^ (party as u8); 32]);
                if party == 4 {
                    e.fault = Some(Fault::FlipOpenedShare { lane: 0 });
                }
                let a = e.share(&[0x55aa_55aa_55aa_55aa])?;
                let res = e.open(&a);
                assert!(e.failed && e.keys.is_wiped());
                res
            });
            assert!(outcomes.iter().all(|o| *o == Err(Error::MultiplicationCheck)));

            // Reconstruct the opened `blind_sigma` XOR sum across all 3 quorum members:
            // the final broadcast payload of each party has `[w_inst0 (2 words), w_inst1 (2 words), nonce (4 words)]`.
            let p0_last = spy_msgs[0].lock().unwrap().last().unwrap().clone();
            let p1_last = spy_msgs[1].lock().unwrap().last().unwrap().clone();
            let p2_last = spy_msgs[2].lock().unwrap().last().unwrap().clone();
            assert_eq!(p0_last.len(), 8);
            let mut sum_inst0 = 0u128;
            let mut sum_inst1 = 0u128;
            for msg in [&p0_last, &p1_last, &p2_last] {
                sum_inst0 ^= (msg[0] as u128) | ((msg[1] as u128) << 64);
                sum_inst1 ^= (msg[2] as u128) | ((msg[3] as u128) << 64);
            }
            assert_ne!(sum_inst0, 0, "blinded residual must be nonzero on wire fault");
            assert_ne!(sum_inst1, 0, "second blinded instance must also be nonzero");
            assert_ne!(sum_inst0, true_delta);
            assert_ne!(sum_inst1, true_delta);
            assert!(!observed_w0.contains(&sum_inst0), "blinded residuals must be fresh uniform per session");
            observed_w0.push(sum_inst0);
        }

        // 2. Concurrent worker poisoning: attach 4 `SpdzEngine`s (root + 3 batch workers)
        //    to one `QuorumKeyEscrow`; when worker 2 aborts, ALL 4 engines' `MacKeyShare`s
        //    are synchronously zeroized in memory immediately!
        let cancelled = Arc::new(core::sync::atomic::AtomicBool::new(false));
        let escrow = QuorumKeyEscrow::new(cancelled.clone());
        let mut workers: Vec<_> = (0..4)
            .map(|w| {
                struct Dummy;
                impl Transport for Dummy {}
                let mut eng = SpdzEngine::new(
                    0,
                    [w as u8; 32],
                    cfg.clone(),
                    keys(&cfg, 0),
                    base_keys[0].fork_stream(b"WORKER", w),
                    Dummy,
                )
                .unwrap();
                eng.attach_escrow(&escrow);
                eng
            })
            .collect();
        assert_eq!(escrow.registered_count_and_all_wiped(), (4, false));
        assert_ne!(workers[0].boolean_key(), 0);
        // Trigger poison on worker 2 alone:
        Core::poison(&mut workers[2]);
        assert!(cancelled.load(core::sync::atomic::Ordering::SeqCst));
        assert_eq!(escrow.registered_count_and_all_wiped(), (4, true));
        for w in &mut workers {
            assert_eq!(w.boolean_key(), 0);
            for f in ThresholdField::ALL {
                assert_eq!(w.field_key(f.index()), ZERO);
            }
            assert_eq!(w.open(&[]), Err(Error::MultiplicationCheck));
        }
    }
}
