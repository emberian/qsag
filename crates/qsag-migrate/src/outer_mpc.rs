//! Replicated mixed-domain evaluation with active 1-of-3 malicious multiplication
//! verification over authenticated confidential pairwise channels.
use crate::circuit::{Domain, Value};
use crate::secret::{Secret, SecretVec, Wipe};
use crate::threshold_mpc::{
    AuthWord, BooleanTriple, DaBitWord, FieldShare, FieldTriple, ThresholdField,
};
use alloc::{boxed::Box, vec, vec::Vec};
use qsag_accel::{
    ct::{ct_eq_bytes_mask, ct_zeroize_bytes, ct_zeroize_u64s},
    goldilocks::{GOLDILOCKS_PRIME as GOLDILOCKS_P, gl_add, gl_mul, gl_sub},
    keccak::{KECCAK_RC, cshake256_framed_32, reduce_192_zero_bias},
};
use qsag_core::sponge::keccak::{Cshake256Xof, SHAKE256_RATE_BYTES, cshake256_static_midstate};
use qsag_asm::{
    BitPlane256, SimdBackend, XorCombinePattern, detect_backend,
    gf2_64x128_clmul_acc_with_backend, gf2_128_dot_with_backend,
    gf2_128_mul_acc_batch_with_backend, gf2_xor_combine_planes_with_backend,
    transpose64x256_with_backend,
};

const MAX_PENDING_BITS: usize = 262_144;
const BIT_TENSOR_BITS: usize = 6;
const BIT_GROUP_WORDS: usize = 1 << BIT_TENSOR_BITS;
const BIT_TERNARY: usize = 729;
const BIT_LANES: usize = 64;
const BIT_NIBBLES: usize = BIT_GROUP_WORDS / 4;
const BIT_FOLD_BLOCK: usize = 1_024;
const MAX_BIT_GROUPS: usize = MAX_PENDING_BITS / BIT_GROUP_WORDS;
const MAX_PENDING_FIELD_WORDS: usize = 1_024;
/// Schwartz-Zippel numerator of one 64-lane packed Boolean check pass per flush:
/// `6 + 1 = 7` for the `6` word-offset weights plus `1` unstructured group weight,
/// `6 * 3 = 18` for the `6` packed ternary sumcheck rounds,
/// `2 * (log2(MAX_BIT_GROUPS) + 6) = 36` for the `12` group + `6` lane halving rounds,
/// and `2` for the randomized base sacrifice (`63` total; two independent passes give
/// `(63 / (2^128 - 1))^2 < 2^-244`, `> 122` bits quantum Grover).
const BIT_CHECK_NUMERATOR: usize = 7
    + 3 * BIT_TENSOR_BITS
    + 2 * (MAX_BIT_GROUPS.ilog2() as usize + BIT_LANES.ilog2() as usize)
    + 2;
/// Numerator of the prime-field check per flush: 1 for the random linear
/// combination, 2 per binary fold over at most `MAX_PENDING_FIELD_WORDS * 64`
/// lane products, and 2 for the base sacrifice.
const FIELD_CHECK_NUMERATOR: usize = 1 + 2 * (MAX_PENDING_FIELD_WORDS * 64).ilog2() as usize + 2;
const _: () = assert!(
    BIT_CHECK_NUMERATOR == 63
        && BIT_CHECK_NUMERATOR * BIT_CHECK_NUMERATOR < 4096
        && FIELD_CHECK_NUMERATOR == 35
        && MAX_BIT_GROUPS.is_power_of_two()
        && (MAX_PENDING_FIELD_WORDS * 64).is_power_of_two()
        && BIT_GROUP_WORDS == 64
        && BIT_TERNARY == 3usize.pow(BIT_TENSOR_BITS as u32)
);
const CONVERT_CHUNK_WORDS: usize = 512;

#[derive(Clone, Copy, Default)]
pub(crate) struct Bit(pub [u64; 2]);
impl core::ops::BitXor for Bit {
    type Output = Self;
    fn bitxor(self, rhs: Self) -> Self {
        Self([self.0[0] ^ rhs.0[0], self.0[1] ^ rhs.0[1]])
    }
}
impl Wipe for Bit {
    fn secret_wipe(&mut self) {
        ct_zeroize_u64s(&mut self.0);
    }
    fn wipe_slice(values: &mut [Self]) {
        qsag_asm::volatile_fill(values, Self::default());
    }
}
impl ShareBit for Bit {}
pub(crate) type Word<B = Bit> = SecretVec<B>;

/// One 64-lane shared Boolean wire of some backend. XOR is the only local gate.
pub(crate) trait ShareBit:
    Copy + Default + Send + Sync + Wipe + core::ops::BitXor<Output = Self>
{
}

/// Primitive operations every outer-MPC backend provides. The replicated
/// 2-of-3 engine and the authenticated general-quorum engine both implement
/// it; [`Gadgets`] and the distributed prover are written against it alone.
///
/// Contract shared by all backends: no value derived from secret wires is
/// returned by `open`, `open_lanes` or `fopen_many`, and `agree` does not
/// succeed, unless every multiplication and conversion performed so far has
/// passed the backend's active-security check. Any failure poisons the engine.
pub(crate) trait Core {
    type Bit: ShareBit;
    /// Public 64-lane constant.
    fn constant(&self, x: u64) -> Self::Bit;
    /// Jointly input words: the shared value is the XOR of all parties' `own`.
    fn share(&mut self, own: &[u64]) -> Result<Word<Self::Bit>, Error>;
    /// As `share`, with every party's contribution forced to be lane-uniform.
    fn share_uniform_lanes(&mut self, own: &[u64]) -> Result<Word<Self::Bit>, Error>;
    fn and_into(
        &mut self,
        pairs: &[(Self::Bit, Self::Bit)],
        out: &mut Word<Self::Bit>,
    ) -> Result<(), Error>;
    fn verify_all_pending(&mut self) -> Result<(), Error>;
    fn open(&mut self, bits: &[Self::Bit]) -> Result<Vec<u64>, Error>;
    /// Open only the lanes selected by `mask`; the other lanes stay hidden
    /// and are returned as zero.
    fn open_lanes(&mut self, bits: &[Self::Bit], mask: u64) -> Result<Vec<u64>, Error>;
    fn agree(&mut self, root: [u8; 32]) -> Result<(), Error>;
    fn poison(&mut self);

    fn fconstant(&self, value: Value, d: Domain) -> FieldWord;
    /// Scale lane `i` by the public `by[i]`.
    fn fscale_lanes(&self, a: &FieldWord, by: &[Value], d: Domain) -> FieldWord;
    fn fadd(&self, a: &FieldWord, b: &FieldWord, d: Domain) -> FieldWord;
    fn fsub(&self, a: &FieldWord, b: &FieldWord, d: Domain) -> FieldWord;
    fn fscale(&self, a: &FieldWord, b: Value, d: Domain) -> FieldWord;
    /// Fresh uniformly random shared field word.
    fn frandom(&mut self, d: Domain) -> Result<FieldWord, Error>;
    fn fmul_many(
        &mut self,
        pairs: &[(&FieldWord, &FieldWord)],
        d: Domain,
    ) -> Result<Vec<FieldWord>, Error>;
    fn fopen_many(&mut self, words: &[FieldWord], d: Domain) -> Result<Vec<Vec<Value>>, Error>;
    fn bits_to_field_many(
        &mut self,
        words: &[Word<Self::Bit>],
        d: Domain,
    ) -> Result<Vec<FieldWord>, Error>;
    fn field_to_bits_many(
        &mut self,
        words: &[&FieldWord],
        d: Domain,
    ) -> Result<Vec<Word<Self::Bit>>, Error>;
    fn lift_bits_many(&mut self, bits: &[Self::Bit], d: Domain)
    -> Result<Vec<FieldWord>, Error>;

    /// Test hook: move a pending field-multiplication fault out of the way
    /// (and back) so regressions can aim it at a chosen phase.
    #[cfg(test)]
    fn take_field_fault(&mut self) -> Option<FaultInjection> {
        None
    }
    #[cfg(test)]
    fn restore_fault(&mut self, _fault: FaultInjection) {}
    #[cfg(test)]
    fn on_public_or_view_open(&self) {}
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    InvalidConfiguration,
    Transport,
    Authentication(usize),
    Disagreement(usize),
    MultiplicationCheck,
    InvalidTape,
    InvalidProof,
    MissingPreprocessing,
}

/// Authenticated envelopes also require confidential delivery. Implementations
/// must deliver each envelope only to its recipient; broadcasting is unsafe.
/// Returned entries are ordered [previous custodian, next custodian].
pub trait Transport: Send {
    /// Maximum concurrently evaluated repetition batches on this custodian.
    /// A zero limit is treated as one. Batches are scheduled in ascending order;
    /// the limit affects resource use only, never repetitions or verification.
    fn max_parallel_batches(&self) -> usize {
        usize::MAX
    }

    /// Optional independent authenticated streams, requested in batch order.
    /// Every custodian must provide all `MIT_REPETITIONS.div_ceil(64)` streams
    /// or none. With the `std` feature these streams allow the independent
    /// repetition batches to run concurrently. Each stream receives a distinct
    /// session/mask domain.
    fn fork(&mut self, _batch: usize) -> Option<Self>
    where
        Self: Sized,
    {
        None
    }

    #[cfg(test)]
    fn audit_transcript(&self) -> Option<(u64, u64)> {
        None
    }
    #[cfg(test)]
    fn audit_candidates(&self, _candidates: Vec<[u8; 32]>) {}
    #[cfg(test)]
    fn audit_private_state(
        &self,
        _party: usize,
        _session: &[u8; 32],
        _witness: &[u8; 32],
        _entropy: &[u8; 32],
        _keys: &[[u8; 32]; 2],
        _statement: &crate::zk_engine::MigrationStatement,
    ) {
    }
    #[cfg(test)]
    fn test_fault_raw(&self) -> Option<[usize; 4]> {
        None
    }
    #[cfg(test)]
    fn on_public_or_view_open(&self) {}
    fn exchange(&mut self, _outgoing: [Envelope; 2]) -> Result<[Envelope; 2], Error> {
        Err(Error::InvalidConfiguration)
    }

    /// General quorum delivery, ordered by the configured quorum with self omitted.
    /// Each envelope must remain confidential to its recipient.
    fn exchange_many(&mut self, _outgoing: Vec<Envelope>) -> Result<Vec<Envelope>, Error> {
        Err(Error::InvalidConfiguration)
    }

    /// General-quorum preprocessing for this stream, consumed in request
    /// order. Every quorum member must serve the same positions of the same
    /// ceremony output under the MAC key shares it gave its
    /// `CoZkCustodianShare`. Material is used once, including across aborts
    /// and forks; a stream that runs dry fails closed. See `threshold_prep`.
    fn take_boolean_triples(&mut self, _count: usize) -> Result<Vec<BooleanTriple>, Error> {
        Err(Error::MissingPreprocessing)
    }
    fn take_auth_words(&mut self, _count: usize) -> Result<Vec<AuthWord>, Error> {
        Err(Error::MissingPreprocessing)
    }
    fn take_field_triples(
        &mut self,
        _field: ThresholdField,
        _count: usize,
    ) -> Result<Vec<FieldTriple>, Error> {
        Err(Error::MissingPreprocessing)
    }
    fn take_field_randoms(
        &mut self,
        _field: ThresholdField,
        _count: usize,
    ) -> Result<Vec<FieldShare>, Error> {
        Err(Error::MissingPreprocessing)
    }
    fn take_dabits(
        &mut self,
        _field: ThresholdField,
        _count: usize,
    ) -> Result<Vec<DaBitWord>, Error> {
        Err(Error::MissingPreprocessing)
    }
}

/// Wire envelope. Authentication binds the session, identities and sequence.
pub struct Envelope {
    pub sender: usize,
    pub recipient: usize,
    pub sequence: u64,
    pub payload: Vec<u64>,
    pub tag: [u8; 32],
}
impl Drop for Envelope {
    fn drop(&mut self) {
        ct_zeroize_u64s(&mut self.payload);
    }
}

/// Word-oriented view of the workspace SHAKE256 sponge: 64-bit words are
/// absorbed and squeezed in little-endian byte order.
#[derive(Clone)]
struct WordSponge136(Cshake256Xof);
impl WordSponge136 {
    fn new() -> Self {
        Self(Cshake256Xof::new_shake256())
    }

    fn from_shake_seed(seed: &[u8; 32]) -> Self {
        let mut s = Self::new();
        s.0.absorb(seed);
        s
    }

    fn absorb_u64(&mut self, word: u64) {
        self.0.absorb(&word.to_le_bytes());
    }

    fn absorb_bytes32(&mut self, bytes: &[u8; 32]) {
        self.0.absorb(bytes);
    }

    fn digest_clone(&self) -> [u8; 32] {
        let mut out = [0u8; 32];
        self.0.clone().squeeze(&mut out);
        out
    }

    fn squeeze_u64s(&mut self, out: &mut [u64]) {
        let mut block = Secret([0u8; SHAKE256_RATE_BYTES]);
        for words in out.chunks_mut(SHAKE256_RATE_BYTES / 8) {
            let bytes = &mut block[..8 * words.len()];
            self.0.squeeze(bytes);
            for (word, chunk) in words.iter_mut().zip(bytes.chunks_exact(8)) {
                *word = u64::from_le_bytes(chunk.try_into().unwrap());
            }
        }
    }

    fn squeeze_u64(&mut self) -> u64 {
        let mut w = [0u64; 1];
        self.squeeze_u64s(&mut w);
        w[0]
    }

    fn squeeze_u128(&mut self) -> u128 {
        let mut w = [0u64; 2];
        self.squeeze_u64s(&mut w);
        (w[0] as u128) | ((w[1] as u128) << 64)
    }

    fn squeeze_nonzero_u128(&mut self) -> u128 {
        loop {
            let v = self.squeeze_u128();
            if v != 0 {
                return v;
            }
        }
    }

    fn squeeze_bytes32(&mut self) -> [u8; 32] {
        let mut words = [0u64; 4];
        self.squeeze_u64s(&mut words);
        let mut out = [0u8; 32];
        for (chunk, &w) in out.chunks_exact_mut(8).zip(&words) {
            chunk.copy_from_slice(&w.to_le_bytes());
        }
        ct_zeroize_u64s(&mut words);
        out
    }
}

/// `cshake256_framed_32("QSAG.OUTER.MESSAGE.V1", [key, session, ..])` with the
/// frame count and the key and session frames already absorbed.
fn build_mac_prefix(key: &[u8; 32], session: &[u8; 32]) -> Cshake256Xof {
    let mut xof = Cshake256Xof::new(b"QSAG.OUTER.MESSAGE.V1");
    xof.absorb(&5u64.to_le_bytes());
    for frame in [key, session] {
        xof.absorb(&32u64.to_le_bytes());
        xof.absorb(frame);
    }
    xof
}

// ============================================================================
// Polynomial-Basis GF(2^128) = GF(2)[x]/(x^128 + x^7 + x^2 + x + 1) & Bitslice
// ============================================================================

type Gf128 = [u64; 2];
type RepGf128 = [Gf128; 2];

#[inline(always)]
const fn u128_to_gf128(v: u128) -> Gf128 {
    [v as u64, (v >> 64) as u64]
}

#[inline(always)]
const fn gf128_to_u128(a: Gf128) -> u128 {
    (a[0] as u128) | ((a[1] as u128) << 64)
}

#[inline(always)]
const fn xor_gf128(a: Gf128, b: Gf128) -> Gf128 {
    [a[0] ^ b[0], a[1] ^ b[1]]
}

/// Branch-free multiplication by `x` in `GF(2)[x]/(x^128 + x^7 + x^2 + x + 1)`.
#[cfg(test)]
#[inline(always)]
const fn poly128_mul_x(c: u128) -> u128 {
    let carry = 0u128.wrapping_sub(c >> 127);
    (c << 1) ^ (carry & 0x87)
}

/// Exact branch-free multiplication by `x^16` in `GF(2)[x]/(x^128 + x^7 + x^2 + x + 1)`.
#[cfg(test)]
#[inline(always)]
const fn poly128_mul_x16(c: u128) -> u128 {
    let h = c >> 112;
    (c << 16) ^ h ^ (h << 1) ^ (h << 2) ^ (h << 7)
}

/// Multiply a `GF(2^128)` element by `x^lane` (`lane < 64`) using strictly
/// compile-time constant immediate shifts (`x^128 = x^7 + x^2 + x + 1`).
#[inline(always)]
fn poly128_mul_x_lane(mut v: u128, lane: usize) -> u128 {
    debug_assert!(lane < BIT_LANES);
    macro_rules! step {
        ($bit:literal) => {
            if (lane & $bit) != 0 {
                let lo = v << $bit;
                let hi = v >> (128 - $bit);
                v = lo ^ hi ^ (hi << 1) ^ (hi << 2) ^ (hi << 7);
            }
        };
    }
    step!(32);
    step!(16);
    step!(8);
    step!(4);
    step!(2);
    step!(1);
    v
}

/// Reduce an unreduced `[low, high]` carryless product (`sum[0] + x^64 * sum[1]`,
/// degree `< 191`) modulo `x^128 + x^7 + x^2 + x + 1`.
#[inline(always)]
const fn reduce_wide_gf128(sum: [u128; 2]) -> u128 {
    let low = sum[0] ^ (sum[1] << 64);
    let high = sum[1] >> 64;
    low ^ high ^ (high << 1) ^ (high << 2) ^ (high << 7)
}

/// Dispatch `GF(2^128)` dot products directly to hardware `VPCLMULQDQ`/`PCLMULQDQ`/`PMULL`.
#[inline(always)]
fn gf128_dot_acc(acc: &mut Gf128, a: &[Gf128], b: &[Gf128], backend: SimdBackend) {
    gf2_128_mul_acc_batch_with_backend(acc, a, b, backend);
}

/// Hardware-accelerated single `GF(2^128)` multiplication via `PCLMULQDQ`/`PMULL`.
#[inline(always)]
fn gf128_mul_hw(a: Gf128, b: Gf128, backend: SimdBackend) -> Gf128 {
    let mut acc = [0u64; 2];
    gf2_128_mul_acc_batch_with_backend(&mut acc, &[a], &[b], backend);
    acc
}

#[inline(always)]
fn gf128_mul_u128(a: u128, b: u128, backend: SimdBackend) -> u128 {
    gf128_to_u128(gf128_mul_hw(u128_to_gf128(a), u128_to_gf128(b), backend))
}

#[inline(always)]
fn gf128_dot_native(a: &[u128], b: &[u128], backend: SimdBackend) -> u128 {
    gf2_128_dot_with_backend(a, b, backend)
}

/// Multiplicative inverse of a public nonzero `GF(2^128)` challenge (`x^(2^128 - 2)`).
#[inline]
fn gf128_inv_public(x: Gf128, backend: SimdBackend) -> Gf128 {
    let mut acc = [1u64, 0u64];
    let mut sq = x;
    for _ in 1..128 {
        sq = gf128_mul_hw(sq, sq, backend);
        acc = gf128_mul_hw(acc, sq, backend);
    }
    acc
}

/// Expand the `64` 64-lane words of one group into `3^6 = 729` words over `{0, 1, 0^1}^6`.
#[inline]
fn ternary_expand_group(src: &[u64; BIT_GROUP_WORDS], out: &mut [u64; BIT_TERNARY]) {
    out[..BIT_GROUP_WORDS].copy_from_slice(src);
    let mut pow3 = 1usize;
    let mut high = BIT_GROUP_WORDS;
    for _ in 0..BIT_TENSOR_BITS {
        let half = high / 2;
        for uh in (0..half).rev() {
            let src0 = pow3 * (2 * uh);
            let dst = 3 * pow3 * uh;
            for el in 0..pow3 {
                let x0 = out[src0 + el];
                let x1 = out[src0 + pow3 + el];
                out[dst + el] = x0;
                out[dst + pow3 + el] = x1;
                out[dst + 2 * pow3 + el] = x0 ^ x1;
            }
        }
        pow3 *= 3;
        high = half;
    }
}

/// Bind `64` rows of four 64-lane words (`[a_0, a_1, b_0, b_1]`) under a public
/// Four-Russians nibble pattern into `64` per-lane `[u128; 4]` tuples.
#[inline]
fn bind_group_columns(
    rows: &[BitPlane256; BIT_GROUP_WORDS],
    pattern: &XorCombinePattern,
    planes: &mut [[BitPlane256; 64]; 2],
    out: &mut [[u128; 4]; BIT_LANES],
    backend: SimdBackend,
) {
    gf2_xor_combine_planes_with_backend(rows, pattern, planes, backend);
    let [low, high] = planes;
    transpose64x256_with_backend(low, backend);
    transpose64x256_with_backend(high, backend);
    for ((dst, lo_row), hi_row) in out.iter_mut().zip(low.iter()).zip(high.iter()) {
        for ((val, &lo), &hi) in dst.iter_mut().zip(lo_row).zip(hi_row) {
            *val = u128::from(lo) | (u128::from(hi) << 64);
        }
    }
}

#[inline]
fn zeroize_gf128_slice(slice: &mut [Gf128]) {
    ct_zeroize_u64s(slice.as_flattened_mut());
}

/// Set `v` to `len` words without ever leaving secret words in freed or
/// truncated storage: a shrink wipes the dropped tail and a growth wipes the old
/// allocation before it is released. Growth past the capacity does not keep the
/// old contents; callers overwrite the whole buffer.
#[cfg(test)]
#[inline]
fn resize_wiped(v: &mut Vec<u64>, len: usize) {
    if len < v.len() {
        ct_zeroize_u64s(&mut v[len..]);
    } else if len > v.capacity() {
        ct_zeroize_u64s(v);
        *v = Vec::with_capacity(len);
    }
    v.resize(len, 0);
}

/// Grow `v` to at least `len` words, wiping any reallocated backing buffer without
/// zeroing and shrinking the reusable high-water tail on smaller calls (`Engine`
/// wipes the entire buffer in `release_verified_scratch` and `Drop`).
#[inline]
fn ensure_scratch_len(v: &mut Vec<u64>, len: usize) {
    if len > v.len() {
        if len > v.capacity() {
            let cap = len.max(2 * v.capacity());
            ct_zeroize_u64s(v);
            *v = Vec::with_capacity(cap);
        }
        v.resize(len, 0);
    }
}

/// `Vec::reserve` that wipes the old allocation when it has to move.
#[inline]
fn reserve_wiped(v: &mut Vec<u64>, additional: usize) {
    let need = v.len() + additional;
    if need > v.capacity() {
        let mut grown = Vec::with_capacity(need.max(2 * v.capacity()));
        grown.extend_from_slice(v);
        ct_zeroize_u64s(v);
        *v = grown;
    }
}

struct ZeroizeRepGf128Vec(Vec<RepGf128>);
impl Drop for ZeroizeRepGf128Vec {
    fn drop(&mut self) {
        for item in &mut self.0 {
            zeroize_gf128_slice(item);
        }
    }
}

struct BitCheckScratch {
    x_tab: [[SecretVec<u128>; 2]; 2],
    y_tab: [[SecretVec<u128>; 2]; 2],
    live: usize,
    y_sum_lo: SecretVec<u128>,
    y_sum_hi: SecretVec<u128>,
    wide_sums: Box<[[[u128; 2]; BIT_TERNARY]; 2]>,
    init_sums: Box<[[[[u128; 2]; BIT_GROUP_WORDS]; 2]; 2]>,
    tab: Box<[[u128; BIT_TERNARY]; 2]>,
    sumcheck_scratch: Box<[u128; BIT_TERNARY]>,
    ea: Box<[[u64; BIT_TERNARY]; 2]>,
    eb: Box<[[u64; BIT_TERNARY]; 2]>,
    prod: Box<[u64; BIT_TERNARY]>,
    c_words: Box<[[u64; BIT_GROUP_WORDS]; 2]>,
    a_words: Box<[[u64; BIT_GROUP_WORDS]; 2]>,
    b_words: Box<[[u64; BIT_GROUP_WORDS]; 2]>,
    rows: Box<[BitPlane256; BIT_GROUP_WORDS]>,
    planes: Box<[[BitPlane256; 64]; 2]>,
    bound: Box<[[u128; 4]; BIT_LANES]>,
    weighted_a: Box<[[u128; BIT_LANES]; 2]>,
    c_claim: [RepGf128; 2],
    a_fin: [RepGf128; 2],
    b_fin: [RepGf128; 2],
    u_mask: [RepGf128; 2],
    v_mask: [RepGf128; 2],
}
impl BitCheckScratch {
    fn new_boxed() -> Box<Self> {
        Box::new(Self {
            x_tab: core::array::from_fn(|_| core::array::from_fn(|_| SecretVec::new())),
            y_tab: core::array::from_fn(|_| core::array::from_fn(|_| SecretVec::new())),
            live: 0,
            y_sum_lo: SecretVec::with_capacity(BIT_FOLD_BLOCK),
            y_sum_hi: SecretVec::with_capacity(BIT_FOLD_BLOCK),
            wide_sums: Box::new([[[0u128; 2]; BIT_TERNARY]; 2]),
            init_sums: Box::new([[[[0u128; 2]; BIT_GROUP_WORDS]; 2]; 2]),
            tab: Box::new([[0u128; BIT_TERNARY]; 2]),
            sumcheck_scratch: Box::new([0u128; BIT_TERNARY]),
            ea: Box::new([[0u64; BIT_TERNARY]; 2]),
            eb: Box::new([[0u64; BIT_TERNARY]; 2]),
            prod: Box::new([0u64; BIT_TERNARY]),
            c_words: Box::new([[0u64; BIT_GROUP_WORDS]; 2]),
            a_words: Box::new([[0u64; BIT_GROUP_WORDS]; 2]),
            b_words: Box::new([[0u64; BIT_GROUP_WORDS]; 2]),
            rows: Box::new([[0u64; 4]; BIT_GROUP_WORDS]),
            planes: Box::new([[[0u64; 4]; 64]; 2]),
            bound: Box::new([[0u128; 4]; BIT_LANES]),
            weighted_a: Box::new([[0u128; BIT_LANES]; 2]),
            c_claim: [[[0u64; 2]; 2]; 2],
            a_fin: [[[0u64; 2]; 2]; 2],
            b_fin: [[[0u64; 2]; 2]; 2],
            u_mask: [[[0u64; 2]; 2]; 2],
            v_mask: [[[0u64; 2]; 2]; 2],
        })
    }

    fn wipe_live_tables(&mut self) {
        for table in self.x_tab.iter_mut().chain(&mut self.y_tab).flatten() {
            let used = self.live.min(table.len());
            qsag_asm::volatile_fill(&mut table[..used], 0);
        }
        self.live = 0;
    }

    fn prepare_tables(&mut self, len: usize) {
        self.wipe_live_tables();
        for table in self.x_tab.iter_mut().chain(&mut self.y_tab).flatten() {
            table.resize(len, 0);
        }
        self.live = len;
        self.y_sum_lo.resize(BIT_FOLD_BLOCK, 0);
        self.y_sum_hi.resize(BIT_FOLD_BLOCK, 0);
    }

    fn wipe_all(&mut self) {
        self.wipe_live_tables();
        for table in self.x_tab.iter_mut().chain(&mut self.y_tab).flatten() {
            table.clear();
        }
        self.y_sum_lo.clear();
        self.y_sum_hi.clear();
        qsag_asm::volatile_fill(self.wide_sums.as_flattened_mut(), [0u128; 2]);
        for t in self.init_sums.iter_mut() {
            qsag_asm::volatile_fill(t.as_flattened_mut(), [0u128; 2]);
        }
        for t in self.tab.iter_mut() {
            qsag_asm::volatile_fill(t, 0);
        }
        qsag_asm::volatile_fill(&mut *self.sumcheck_scratch, 0);
        for s in 0..2 {
            ct_zeroize_u64s(&mut self.ea[s]);
            ct_zeroize_u64s(&mut self.eb[s]);
            ct_zeroize_u64s(&mut self.c_words[s]);
            ct_zeroize_u64s(&mut self.a_words[s]);
            ct_zeroize_u64s(&mut self.b_words[s]);
            qsag_asm::volatile_fill(&mut self.weighted_a[s], 0);
        }
        ct_zeroize_u64s(&mut *self.prod);
        qsag_asm::volatile_fill(&mut *self.rows, [0u64; 4]);
        qsag_asm::volatile_fill(self.planes.as_flattened_mut(), [0u64; 4]);
        qsag_asm::volatile_fill(&mut *self.bound, [0u128; 4]);
        for pair in [
            &mut self.c_claim,
            &mut self.a_fin,
            &mut self.b_fin,
            &mut self.u_mask,
            &mut self.v_mask,
        ] {
            for r in pair {
                zeroize_gf128_slice(r);
            }
        }
    }
}
impl Drop for BitCheckScratch {
    fn drop(&mut self) {
        self.wipe_all();
    }
}

// ============================================================================
// Cubic Goldilocks Extension Field GF(p)[u] / (u^3 - 7), |F| = p^3 > 2^191.99
// ============================================================================

type GoldExt3 = [u64; 3];
type RepGoldExt3 = [GoldExt3; 2];

#[inline]
fn g3_add(a: GoldExt3, b: GoldExt3) -> GoldExt3 {
    [gl_add(a[0], b[0]), gl_add(a[1], b[1]), gl_add(a[2], b[2])]
}

#[inline]
fn g3_sub(a: GoldExt3, b: GoldExt3) -> GoldExt3 {
    [gl_sub(a[0], b[0]), gl_sub(a[1], b[1]), gl_sub(a[2], b[2])]
}

#[inline]
fn g3_mul(a: GoldExt3, b: GoldExt3) -> GoldExt3 {
    let a0b0 = gl_mul(a[0], b[0]);
    let a1b1 = gl_mul(a[1], b[1]);
    let a2b2 = gl_mul(a[2], b[2]);
    let t_0 = gl_add(gl_mul(a[1], b[2]), gl_mul(a[2], b[1]));
    let c0 = gl_add(a0b0, gl_mul(7, t_0));
    let c1 = gl_add(
        gl_add(gl_mul(a[0], b[1]), gl_mul(a[1], b[0])),
        gl_mul(7, a2b2),
    );
    let c2 = gl_add(gl_add(gl_mul(a[0], b[2]), a1b1), gl_mul(a[2], b[0]));
    [c0, c1, c2]
}

#[inline]
fn g3_canonical(a: GoldExt3) -> bool {
    a[0] < GOLDILOCKS_P && a[1] < GOLDILOCKS_P && a[2] < GOLDILOCKS_P
}

#[inline]
fn squeeze_g3_challenge(xof: &mut WordSponge136) -> GoldExt3 {
    let mut words = [0u64; 9];
    xof.squeeze_u64s(&mut words);
    let mut raw = [0u8; 72];
    for (chunk, &w) in raw.chunks_exact_mut(8).zip(&words) {
        chunk.copy_from_slice(&w.to_le_bytes());
    }
    let mut out = [0u64; 3];
    for (dst, slice24) in out.iter_mut().zip(raw.chunks_exact(24)) {
        let mut arr = [0u8; 24];
        arr.copy_from_slice(slice24);
        *dst = reduce_192_zero_bias(&arr);
    }
    out
}

#[inline]
fn squeeze_fp_challenge(xof: &mut WordSponge136, d: Domain) -> Value {
    loop {
        let b = xof.squeeze_bytes32();
        let mut v = crate::scalar::decode(&b);
        if d == Domain::Ed {
            v[3] &= 0x7fff_ffff_ffff_ffff;
        }
        if d.canonical(v) {
            return v;
        }
    }
}

// ============================================================================
// Replicated Mixed-Domain Active Engine
// ============================================================================

/// Replicated additive field shares, with one entry per repetition lane.
pub(crate) type FieldWord = SecretVec<[Value; 2]>;
type PendingFieldTriple = (FieldWord, FieldWord, FieldWord);

#[cfg(test)]
#[derive(Clone, Copy)]
pub(crate) enum FaultInjection {
    BitAnd {
        call_countdown: usize,
        gate: usize,
        lane: usize,
    },
    FieldMul {
        domain: Domain,
        call_countdown: usize,
        lane: usize,
    },
}

#[cfg(test)]
impl FaultInjection {
    pub(crate) fn to_raw(self) -> [usize; 4] {
        match self {
            Self::BitAnd {
                call_countdown,
                gate,
                lane,
            } => [0, call_countdown, gate, lane],
            Self::FieldMul {
                domain,
                call_countdown,
                lane,
            } => {
                let tag = match domain {
                    Domain::Gold => 1,
                    Domain::Secp => 2,
                    Domain::Ed => 3,
                    Domain::Bit => 0,
                };
                [tag, call_countdown, lane, 0]
            }
        }
    }
    fn from_raw([tag, a, b, c]: [usize; 4]) -> Self {
        match tag {
            0 => Self::BitAnd {
                call_countdown: a,
                gate: b,
                lane: c,
            },
            1 => Self::FieldMul {
                domain: Domain::Gold,
                call_countdown: a,
                lane: b,
            },
            2 => Self::FieldMul {
                domain: Domain::Secp,
                call_countdown: a,
                lane: b,
            },
            _ => Self::FieldMul {
                domain: Domain::Ed,
                call_countdown: a,
                lane: b,
            },
        }
    }
}

pub(crate) struct Engine<T> {
    pub party: usize,
    #[cfg(any(feature = "std", test))]
    pub(crate) batch_cancelled: Option<alloc::sync::Arc<core::sync::atomic::AtomicBool>>,
    session: [u8; 32],
    keys: [[u8; 32]; 2],
    mac_prefix: [Cshake256Xof; 2],
    pads: [WordSponge136; 2],
    edge_sponges: [WordSponge136; 2],
    coin_rng: WordSponge136,
    sequence: u64,
    poisoned: bool,
    pending_bits_raw: Vec<u64>,
    pending_secp: Vec<PendingFieldTriple>,
    pending_ed: Vec<PendingFieldTriple>,
    pending_gold: Vec<PendingFieldTriple>,
    scratch_r: Vec<u64>,
    scratch_s: Vec<u64>,
    bit_scratch: Option<Box<BitCheckScratch>>,
    #[cfg(test)]
    pub(crate) fault: Option<FaultInjection>,
    pub transport: T,
}

impl<T> Drop for Engine<T> {
    fn drop(&mut self) {
        for key in &mut self.keys {
            ct_zeroize_bytes(key);
        }
        ct_zeroize_u64s(&mut self.scratch_r);
        ct_zeroize_u64s(&mut self.scratch_s);
        ct_zeroize_u64s(&mut self.pending_bits_raw);
    }
}

impl<T: Transport> Engine<T> {
    pub fn new(
        party: usize,
        session: [u8; 32],
        keys: [[u8; 32]; 2],
        transport: T,
    ) -> Result<Self, Error> {
        if party >= 3 {
            return Err(Error::InvalidConfiguration);
        }
        let mac_prefix = [
            build_mac_prefix(&keys[0], &session),
            build_mac_prefix(&keys[1], &session),
        ];
        let pads = keys.map(|key| {
            let mut seed = cshake256_framed_32(b"QSAG.OUTER.PADS.V1", &[&key, &session]);
            let sp = WordSponge136::from_shake_seed(&seed);
            ct_zeroize_bytes(&mut seed);
            sp
        });
        let prev = (party + 2) % 3;
        let next = (party + 1) % 3;
        let init_edge = |u: usize, v: usize| {
            let mut s = WordSponge136::new();
            s.absorb_u64(0x4544_4745_5f56_3100); // "EDGE_V1"
            s.absorb_bytes32(&session);
            s.absorb_u64((u as u64) | ((v as u64) << 8));
            s
        };
        let edge_sponges = [init_edge(prev, party), init_edge(party, next)];
        let mut coin_seed = cshake256_framed_32(
            b"QSAG.OUTER.COIN.RNG.V1",
            &[&session, &[party as u8], &keys[0], &keys[1]],
        );
        let coin_rng = WordSponge136::from_shake_seed(&coin_seed);
        ct_zeroize_bytes(&mut coin_seed);
        #[cfg(test)]
        let fault = transport.test_fault_raw().map(FaultInjection::from_raw);
        Ok(Self {
            party,
            session,
            keys,
            mac_prefix,
            pads,
            edge_sponges,
            coin_rng,
            sequence: 0,
            poisoned: false,
            #[cfg(any(feature = "std", test))]
            batch_cancelled: None,
            pending_bits_raw: Vec::new(),
            pending_secp: Vec::new(),
            pending_ed: Vec::new(),
            pending_gold: Vec::new(),
            scratch_r: Vec::new(),
            scratch_s: Vec::new(),
            bit_scratch: None,
            #[cfg(test)]
            fault,
            transport,
        })
    }

    /// Session and channel keys, for starting this custodian's batch engines.
    pub(crate) fn custody(&self) -> ([u8; 32], [[u8; 32]; 2]) {
        (self.session, self.keys)
    }

    /// Release evaluation scratch after a repetition batch has passed all
    /// checks. Its engine remains live for authenticated opening rounds.
    #[cfg(any(feature = "std", test))]
    pub(crate) fn release_verified_scratch(&mut self) {
        debug_assert!(self.pending_bits_raw.is_empty());
        debug_assert!(
            self.pending_secp.is_empty()
                && self.pending_ed.is_empty()
                && self.pending_gold.is_empty()
        );
        self.bit_scratch = None;
        for scratch in [
            &mut self.scratch_r,
            &mut self.scratch_s,
            &mut self.pending_bits_raw,
        ] {
            ct_zeroize_u64s(scratch);
            *scratch = Vec::new();
        }
    }

    /// Hedge local coin-flipping randomness with custodian-private ceremony entropy.
    pub fn mix_entropy(&mut self, entropy: &[u8; 32]) {
        let current = self.coin_rng.squeeze_bytes32();
        let mut next_seed = cshake256_framed_32(
            b"QSAG.OUTER.COIN.HEDGE.V1",
            &[&current, entropy, &self.session],
        );
        self.coin_rng = WordSponge136::from_shake_seed(&next_seed);
        ct_zeroize_bytes(&mut next_seed);
    }

    #[inline]
    pub fn constant(&self, x: u64) -> Bit {
        Bit([
            if self.party == 0 { x } else { 0 },
            if (self.party + 1) % 3 == 0 { x } else { 0 },
        ])
    }

    fn tag(
        &self,
        peer: usize,
        sender: usize,
        recipient: usize,
        seq: u64,
        payload: &[u64],
    ) -> [u8; 32] {
        let mut xof = self.mac_prefix[peer].clone();
        xof.absorb(&2u64.to_le_bytes());
        xof.absorb(&[sender as u8, recipient as u8]);
        xof.absorb(&8u64.to_le_bytes());
        xof.absorb(&seq.to_le_bytes());
        xof.absorb(&((payload.len() as u64) * 8).to_le_bytes());
        let mut block = Secret([0u8; 8 * SHAKE256_RATE_BYTES]);
        for words in payload.chunks(SHAKE256_RATE_BYTES) {
            let bytes = &mut block[..8 * words.len()];
            for (chunk, word) in bytes.chunks_exact_mut(8).zip(words) {
                chunk.copy_from_slice(&word.to_le_bytes());
            }
            xof.absorb(bytes);
        }
        let mut out = [0u8; 32];
        xof.squeeze(&mut out);
        out
    }

    fn raw_exchange(&mut self, mut payloads: [Vec<u64>; 2]) -> Result<[SecretVec<u64>; 2], Error> {
        if self.poisoned {
            for payload in &mut payloads {
                ct_zeroize_u64s(payload);
            }
            return Err(Error::MultiplicationCheck);
        }
        #[cfg(any(feature = "std", test))]
        if self
            .batch_cancelled
            .as_ref()
            .is_some_and(|flag| flag.load(core::sync::atomic::Ordering::Relaxed))
        {
            for payload in &mut payloads {
                ct_zeroize_u64s(payload);
            }
            return Err(Error::Transport);
        }
        let peers = [(self.party + 2) % 3, (self.party + 1) % 3];
        let seq = self.sequence;
        let [p0, p1] = payloads;
        let out_tag_0 = self.tag(0, self.party, peers[0], seq, &p0);
        let out_tag_1 = self.tag(1, self.party, peers[1], seq, &p1);
        let outgoing = [
            Envelope {
                tag: out_tag_0,
                sender: self.party,
                recipient: peers[0],
                sequence: seq,
                payload: p0,
            },
            Envelope {
                tag: out_tag_1,
                sender: self.party,
                recipient: peers[1],
                sequence: seq,
                payload: p1,
            },
        ];
        let mut incoming = self.transport.exchange(outgoing)?;
        for (i, message) in incoming.iter().enumerate() {
            let expected = self.tag(i, peers[i], self.party, seq, &message.payload);
            if message.sender != peers[i]
                || message.recipient != self.party
                || message.sequence != seq
                || ct_eq_bytes_mask(&expected, &message.tag) != u64::MAX
            {
                self.poisoned = true;
                return Err(Error::Authentication(peers[i]));
            }
        }
        // Record canonical directed-edge tags: edge 0 is `prev -> self`, edge 1 is `self -> next`.
        self.edge_sponges[0].absorb_u64(seq);
        self.edge_sponges[0].absorb_bytes32(&incoming[0].tag);
        self.edge_sponges[0].absorb_bytes32(&out_tag_0);
        self.edge_sponges[1].absorb_u64(seq);
        self.edge_sponges[1].absorb_bytes32(&out_tag_1);
        self.edge_sponges[1].absorb_bytes32(&incoming[1].tag);

        self.sequence = seq.checked_add(1).ok_or(Error::InvalidConfiguration)?;
        Ok(incoming
            .each_mut()
            .map(|m| SecretVec::from(core::mem::take(&mut m.payload))))
    }

    fn raw_share_owned(
        &mut self,
        own: Vec<u64>,
    ) -> Result<(SecretVec<u64>, SecretVec<u64>), Error> {
        let len = own.len();
        let mut own_copy = SecretVec::with_capacity(len);
        own_copy.extend_from_slice(&own);
        let incoming = match self.raw_exchange([own, Vec::new()]) {
            Ok(incoming) => incoming,
            Err(error) => {
                ct_zeroize_u64s(&mut own_copy);
                return Err(error);
            }
        };
        if incoming[1].len() != len || !incoming[0].is_empty() {
            ct_zeroize_u64s(&mut own_copy);
            self.poisoned = true;
            return Err(Error::InvalidConfiguration);
        }
        let [_, next_share] = incoming;
        Ok((own_copy, next_share))
    }

    pub fn share(&mut self, own: &[u64]) -> Result<Word, Error> {
        let (mut mine, mut next) = self.raw_share_owned(own.to_vec())?;
        let out = mine.iter().zip(&next).map(|(&a, &b)| Bit([a, b])).collect();
        ct_zeroize_u64s(&mut mine);
        ct_zeroize_u64s(&mut next);
        Ok(out)
    }

    /// Share secret bits while enforcing that every custodian supplies uniform
    /// 64-lane masks (`0` or `u64::MAX`), preventing cross-repetition witness splitting.
    pub fn share_uniform_lanes(&mut self, own: &[u64]) -> Result<Word, Error> {
        if own.iter().any(|&w| w != 0 && w != u64::MAX) {
            return Err(Error::InvalidConfiguration);
        }
        let (mut mine, mut next) = self.raw_share_owned(own.to_vec())?;
        if next.iter().any(|&w| w != 0 && w != u64::MAX) {
            ct_zeroize_u64s(&mut mine);
            ct_zeroize_u64s(&mut next);
            self.poisoned = true;
            return Err(Error::Disagreement((self.party + 1) % 3));
        }
        let out = mine.iter().zip(&next).map(|(&a, &b)| Bit([a, b])).collect();
        ct_zeroize_u64s(&mut mine);
        ct_zeroize_u64s(&mut next);
        Ok(out)
    }

    /// Two-round commit-then-open coin-flipping bound to the full three-edge
    /// authenticated transcript up to `self.sequence`.
    fn coin_flip(&mut self, domain: &[u8]) -> Result<[u8; 32], Error> {
        let flip_seq = self.sequence;
        let td_own = [
            self.edge_sponges[0].digest_clone(),
            self.edge_sponges[1].digest_clone(),
        ];
        let mut r_own = self.coin_rng.squeeze_bytes32();
        let session = self.session;
        let commit_for = |party: usize, td: &[[u8; 32]; 2], r: &[u8; 32]| {
            cshake256_framed_32(
                b"QSAG.OUTER.COIN.COMMIT.V1",
                &[
                    &session,
                    &flip_seq.to_le_bytes(),
                    &(party as u64).to_le_bytes(),
                    domain,
                    &td[0],
                    &td[1],
                    r,
                ],
            )
        };
        let c_own = commit_for(self.party, &td_own, &r_own);
        let to_words4 = |b: &[u8; 32]| -> [u64; 4] {
            core::array::from_fn(|i| {
                let mut buf = [0u8; 8];
                buf.copy_from_slice(&b[8 * i..8 * i + 8]);
                u64::from_le_bytes(buf)
            })
        };
        let from_words4 = |w: &[u64]| -> [u8; 32] {
            let mut out = [0u8; 32];
            for (chunk, &val) in out.chunks_exact_mut(8).zip(&w[..4]) {
                chunk.copy_from_slice(&val.to_le_bytes());
            }
            out
        };

        let c_vec = to_words4(&c_own).to_vec();
        let in_commits = self.raw_exchange([c_vec.clone(), c_vec])?;
        if in_commits[0].len() != 4 || in_commits[1].len() != 4 {
            ct_zeroize_bytes(&mut r_own);
            self.poisoned = true;
            return Err(Error::MultiplicationCheck);
        }
        let prev = (self.party + 2) % 3;
        let next = (self.party + 1) % 3;
        let mut commits = [[0u8; 32]; 3];
        commits[self.party] = c_own;
        commits[prev] = from_words4(&in_commits[0]);
        commits[next] = from_words4(&in_commits[1]);

        let mut open_words = Vec::with_capacity(24);
        open_words.extend_from_slice(&to_words4(&r_own));
        open_words.extend_from_slice(&to_words4(&td_own[0]));
        open_words.extend_from_slice(&to_words4(&td_own[1]));
        for c in &commits {
            open_words.extend_from_slice(&to_words4(c));
        }
        let in_opens = self.raw_exchange([open_words.clone(), open_words])?;
        if in_opens[0].len() != 24 || in_opens[1].len() != 24 {
            ct_zeroize_bytes(&mut r_own);
            self.poisoned = true;
            return Err(Error::MultiplicationCheck);
        }

        let mut r_prev = from_words4(&in_opens[0][0..4]);
        let td_prev = [
            from_words4(&in_opens[0][4..8]),
            from_words4(&in_opens[0][8..12]),
        ];
        let mut r_next = from_words4(&in_opens[1][0..4]);
        let td_next = [
            from_words4(&in_opens[1][4..8]),
            from_words4(&in_opens[1][8..12]),
        ];

        // Verify echoed commitments match across all three parties, pairwise edge
        // transcripts match on all three links, and both peer commitments open validly.
        let mut valid_mask = ct_eq_bytes_mask(&td_prev[1], &td_own[0])
            & ct_eq_bytes_mask(&td_next[0], &td_own[1])
            & ct_eq_bytes_mask(&td_prev[0], &td_next[1]);
        for (idx, expected_c) in commits.iter().enumerate() {
            let echo_prev = from_words4(&in_opens[0][12 + 4 * idx..16 + 4 * idx]);
            let echo_next = from_words4(&in_opens[1][12 + 4 * idx..16 + 4 * idx]);
            valid_mask &= ct_eq_bytes_mask(&echo_prev, expected_c);
            valid_mask &= ct_eq_bytes_mask(&echo_next, expected_c);
        }
        let expected_prev = commit_for(prev, &td_prev, &r_prev);
        let expected_next = commit_for(next, &td_next, &r_next);
        valid_mask &= ct_eq_bytes_mask(&expected_prev, &commits[prev]);
        valid_mask &= ct_eq_bytes_mask(&expected_next, &commits[next]);

        if valid_mask != u64::MAX {
            ct_zeroize_bytes(&mut r_own);
            ct_zeroize_bytes(&mut r_prev);
            ct_zeroize_bytes(&mut r_next);
            self.poisoned = true;
            return Err(Error::MultiplicationCheck);
        }

        let mut r_xor = [0u8; 32];
        for (i, dst) in r_xor.iter_mut().enumerate() {
            *dst = r_own[i] ^ r_prev[i] ^ r_next[i];
        }
        let mut edges_by_party = [[0u8; 32]; 3];
        edges_by_party[self.party] = td_own[0];
        edges_by_party[prev] = td_prev[0];
        edges_by_party[next] = td_next[0];

        let out = cshake256_framed_32(
            b"QSAG.OUTER.COIN.DERIVE.V1",
            &[
                &self.session,
                &flip_seq.to_le_bytes(),
                domain,
                &edges_by_party[0],
                &edges_by_party[1],
                &edges_by_party[2],
                &commits[0],
                &commits[1],
                &commits[2],
                &r_xor,
            ],
        );
        ct_zeroize_bytes(&mut r_own);
        ct_zeroize_bytes(&mut r_prev);
        ct_zeroize_bytes(&mut r_next);
        ct_zeroize_bytes(&mut r_xor);
        Ok(out)
    }

    fn open_raw_bits(&mut self, bits: &[Bit]) -> Result<Vec<u64>, Error> {
        let mut own = Vec::with_capacity(bits.len() * 2);
        for b in bits {
            own.push(b.0[0]);
            own.push(b.0[1]);
        }
        let incoming = self.raw_exchange([own.clone(), own])?;
        if incoming.iter().any(|v| v.len() != bits.len() * 2) {
            self.poisoned = true;
            return Err(Error::InvalidConfiguration);
        }
        let mut out = Vec::with_capacity(bits.len());
        for (i, b) in bits.iter().enumerate() {
            if incoming[0][2 * i + 1] != b.0[0] {
                self.poisoned = true;
                return Err(Error::Disagreement((self.party + 2) % 3));
            }
            if incoming[1][2 * i] != b.0[1] || incoming[0][2 * i] != incoming[1][2 * i + 1] {
                self.poisoned = true;
                return Err(Error::Disagreement((self.party + 1) % 3));
            }
            out.push(b.0[0] ^ b.0[1] ^ incoming[0][2 * i]);
        }
        Ok(out)
    }

    fn reshare_gf128_many(&mut self, locals: &[Gf128]) -> Result<Vec<RepGf128>, Error> {
        let total_u64 = locals.len() * 2;
        ensure_scratch_len(&mut self.scratch_r, total_u64);
        ensure_scratch_len(&mut self.scratch_s, total_u64);
        self.pads[0].squeeze_u64s(&mut self.scratch_r[..total_u64]);
        self.pads[1].squeeze_u64s(&mut self.scratch_s[..total_u64]);
        let mut own = Vec::with_capacity(total_u64);
        for (idx, &[w0, w1]) in locals.iter().enumerate() {
            let off = 2 * idx;
            own.push(w0 ^ self.scratch_r[off] ^ self.scratch_s[off]);
            own.push(w1 ^ self.scratch_r[off + 1] ^ self.scratch_s[off + 1]);
        }
        let (mine, next) = self.raw_share_owned(own)?;
        let mut out = Vec::with_capacity(locals.len());
        for idx in 0..locals.len() {
            let off = 2 * idx;
            out.push([[mine[off], mine[off + 1]], [next[off], next[off + 1]]]);
        }
        Ok(out)
    }

    fn prss_gf128(&mut self) -> RepGf128 {
        let mut raw0 = [0u64; 2];
        let mut raw1 = [0u64; 2];
        self.pads[0].squeeze_u64s(&mut raw0);
        self.pads[1].squeeze_u64s(&mut raw1);
        let out = [raw0, raw1];
        ct_zeroize_u64s(&mut raw0);
        ct_zeroize_u64s(&mut raw1);
        out
    }

    fn fold_bit_tables_round(
        &mut self,
        scratch: &mut BitCheckScratch,
        upper: usize,
        len: usize,
        backend: SimdBackend,
    ) -> Result<(), Error> {
        let mut fold_locals = [[0u64; 2]; 4];
        for t in 0..2 {
            let mut l_acc = 0u128;
            let mut r_acc = 0u128;
            for start in (0..len).step_by(BIT_FOLD_BLOCK) {
                let blk = (len - start).min(BIT_FOLD_BLOCK);
                let lo_r = start..start + blk;
                let hi_r = (upper + start)..(upper + start + blk);
                let x0_lo = &scratch.x_tab[t][0][lo_r.clone()];
                let x1_lo = &scratch.x_tab[t][1][lo_r.clone()];
                let x0_hi = &scratch.x_tab[t][0][hi_r.clone()];
                let x1_hi = &scratch.x_tab[t][1][hi_r.clone()];
                let y0_lo = &scratch.y_tab[t][0][lo_r.clone()];
                let y1_lo = &scratch.y_tab[t][1][lo_r];
                let y0_hi = &scratch.y_tab[t][0][hi_r.clone()];
                let y1_hi = &scratch.y_tab[t][1][hi_r];
                let y_lo_sum = &mut scratch.y_sum_lo[..blk];
                let y_hi_sum = &mut scratch.y_sum_hi[..blk];
                for ((dst, &p), &q) in y_lo_sum.iter_mut().zip(y0_lo).zip(y1_lo) {
                    *dst = p ^ q;
                }
                for ((dst, &p), &q) in y_hi_sum.iter_mut().zip(y0_hi).zip(y1_hi) {
                    *dst = p ^ q;
                }
                l_acc ^= gf128_dot_native(x0_lo, y_hi_sum, backend)
                    ^ gf128_dot_native(x1_lo, y0_hi, backend);
                r_acc ^= gf128_dot_native(x0_hi, y_lo_sum, backend)
                    ^ gf128_dot_native(x1_hi, y0_lo, backend);
            }
            fold_locals[2 * t] = u128_to_gf128(l_acc);
            fold_locals[2 * t + 1] = u128_to_gf128(r_acc);
        }
        qsag_asm::volatile_fill(&mut scratch.y_sum_lo[..len.min(BIT_FOLD_BLOCK)], 0);
        qsag_asm::volatile_fill(&mut scratch.y_sum_hi[..len.min(BIT_FOLD_BLOCK)], 0);

        let reshared_res = self.reshare_gf128_many(&fold_locals);
        zeroize_gf128_slice(&mut fold_locals);
        let lr_sh = ZeroizeRepGf128Vec(reshared_res?);

        let seed_rk = self.coin_flip(b"QSAG.OUTER.MULCHECK.BITS.FOLD.V1")?;
        let mut xof_rk = WordSponge136::from_shake_seed(&seed_rk);
        let gamma = [
            u128_to_gf128(xof_rk.squeeze_nonzero_u128()),
            u128_to_gf128(xof_rk.squeeze_nonzero_u128()),
        ];
        let gamma_inv = [
            gf128_inv_public(gamma[0], backend),
            gf128_inv_public(gamma[1], backend),
        ];

        for t in 0..2 {
            let g_u = gf128_to_u128(gamma[t]);
            let gi_u = gf128_to_u128(gamma_inv[t]);
            let scales = [gamma_inv[t], gamma[t]];
            for side in 0..2 {
                let msgs = [lr_sh.0[2 * t][side], lr_sh.0[2 * t + 1][side]];
                gf128_dot_acc(&mut scratch.c_claim[t][side], &scales, &msgs, backend);

                let (x_lo, x_rest) = scratch.x_tab[t][side].split_at_mut(upper);
                let x_hi = &mut x_rest[..len];
                qsag_asm::bitslice::gf2_128_scale_xor_with_backend(
                    &mut x_lo[..len],
                    x_hi,
                    g_u,
                    backend,
                );
                qsag_asm::volatile_fill(x_hi, 0);

                let (y_lo, y_rest) = scratch.y_tab[t][side].split_at_mut(upper);
                let y_hi = &mut y_rest[..len];
                qsag_asm::bitslice::gf2_128_scale_xor_with_backend(
                    &mut y_lo[..len],
                    y_hi,
                    gi_u,
                    backend,
                );
                qsag_asm::volatile_fill(y_hi, 0);
            }
        }
        scratch.live = scratch.live.min(upper);
        Ok(())
    }

    /// Batch-verify up to `MAX_PENDING_BITS` (`262,144`) 64-lane Boolean `AND` triples
    /// (`16,777,216` Boolean gates) over `GF(2^128) = GF(2)[x]/(x^128 + x^7 + x^2 + x + 1)`
    /// via two independent lockstep 64-lane-packed BBCGGI19 proofs:
    /// 1. 64-bit word polynomial embedding `P(w) = sum_{lane=0}^{63} bit_lane(w) * x^lane`
    ///    weighted by `6` word-offset challenges `mu` and `G <= 4,096` group challenges `nu`
    ///    via `gf2_64x128_clmul_acc`,
    /// 2. `6` packed ternary sumcheck rounds (`3^6 = 729` points) binding the `6` word-offset bits,
    /// 3. Four-Russians word binding (`gf2_xor_combine_planes` + `transpose64x256`) into `64 * G`
    ///    field elements total across all 64 lanes,
    /// 4. `ceil(log2 G) + 6 <= 18` halving inner-product rounds over `GF(2^128)^x`, and
    /// 5. Zero-knowledge randomized base-case sacrifice.
    ///
    /// Per-flush false acceptance is `< (BIT_CHECK_NUMERATOR / (2^128 - 1))^2 =
    /// (63 / (2^128 - 1))^2 < 2^-244` (`> 122` bits quantum Grover).
    #[allow(clippy::needless_range_loop)]
    fn verify_pending_bits_slice(&mut self, triples_raw: &[u64]) -> Result<(), Error> {
        debug_assert_eq!(triples_raw.len() % 6, 0);
        let n = triples_raw.len() / 6;
        if n == 0 {
            return Ok(());
        }
        let backend = detect_backend();
        let groups = n.div_ceil(BIT_GROUP_WORDS);
        debug_assert!(groups <= MAX_BIT_GROUPS);

        let seed0 = self.coin_flip(b"QSAG.OUTER.MULCHECK.BITS.INIT.V1")?;
        let mut xof0 = WordSponge136::from_shake_seed(&seed0);
        let mu: [[u128; BIT_TENSOR_BITS]; 2] =
            core::array::from_fn(|_| core::array::from_fn(|_| xof0.squeeze_u128()));
        let nu: [Vec<u128>; 2] =
            core::array::from_fn(|_| (0..groups).map(|_| xof0.squeeze_u128()).collect());

        let mut mu_tab = [[1u128; BIT_GROUP_WORDS]; 2];
        for t in 0..2 {
            for u in 1..BIT_GROUP_WORDS {
                mu_tab[t][u] = gf128_mul_u128(
                    mu_tab[t][u & (u - 1)],
                    mu[t][u.trailing_zeros() as usize],
                    backend,
                );
            }
        }

        // `scratch` implements `Drop` (`wipe_all`), guaranteeing deterministic zeroization
        // on every `Err` early return and when `Engine` drops.
        let mut scratch = self
            .bit_scratch
            .take()
            .unwrap_or_else(BitCheckScratch::new_boxed);
        qsag_asm::volatile_fill(scratch.wide_sums.as_flattened_mut(), [0u128; 2]);
        for t in scratch.init_sums.iter_mut() {
            qsag_asm::volatile_fill(t.as_flattened_mut(), [0u128; 2]);
        }

        // Build packed 729-point ternary product tables and initial weighted claims in one
        // linear pass over `triples_raw` via hardware `64 x 128` carryless MACs.
        for g in 0..groups {
            let start = g * BIT_GROUP_WORDS * 6;
            let end = (start + BIT_GROUP_WORDS * 6).min(triples_raw.len());
            let chunk = &triples_raw[start..end];
            let g_words = chunk.len() / 6;
            for (u, triple) in chunk.chunks_exact(6).enumerate() {
                scratch.a_words[0][u] = triple[0];
                scratch.a_words[1][u] = triple[1];
                scratch.b_words[0][u] = triple[2];
                scratch.b_words[1][u] = triple[3];
                scratch.c_words[0][u] = triple[4];
                scratch.c_words[1][u] = triple[5];
            }
            if g_words < BIT_GROUP_WORDS {
                for s in 0..2 {
                    scratch.a_words[s][g_words..].fill(0);
                    scratch.b_words[s][g_words..].fill(0);
                    scratch.c_words[s][g_words..].fill(0);
                }
            }

            let sp = &mut *scratch;
            ternary_expand_group(&sp.a_words[0], &mut sp.ea[0]);
            ternary_expand_group(&sp.a_words[1], &mut sp.ea[1]);
            ternary_expand_group(&sp.b_words[0], &mut sp.eb[0]);
            ternary_expand_group(&sp.b_words[1], &mut sp.eb[1]);
            for (e, dst) in sp.prod.iter_mut().enumerate() {
                *dst = (sp.ea[0][e] & (sp.eb[0][e] ^ sp.eb[1][e])) ^ (sp.ea[1][e] & sp.eb[0][e]);
            }
            for t in 0..2 {
                let w_nu = nu[t][g];
                gf2_64x128_clmul_acc_with_backend(&mut sp.wide_sums[t], &*sp.prod, w_nu, backend);
                for side in 0..2 {
                    gf2_64x128_clmul_acc_with_backend(
                        &mut sp.init_sums[t][side],
                        &sp.c_words[side],
                        w_nu,
                        backend,
                    );
                }
            }
        }

        for t in 0..2 {
            for (dst, &wide) in scratch.tab[t].iter_mut().zip(&scratch.wide_sums[t]) {
                *dst = reduce_wide_gf128(wide);
            }
            for side in 0..2 {
                let mut acc = 0u128;
                for (u, &wide) in scratch.init_sums[t][side].iter().enumerate() {
                    acc ^= gf128_mul_u128(mu_tab[t][u], reduce_wide_gf128(wide), backend);
                }
                scratch.c_claim[t][side] = u128_to_gf128(acc);
            }
        }
        qsag_asm::volatile_fill(scratch.wide_sums.as_flattened_mut(), [0u128; 2]);
        for t in scratch.init_sums.iter_mut() {
            qsag_asm::volatile_fill(t.as_flattened_mut(), [0u128; 2]);
        }
        for s in 0..2 {
            ct_zeroize_u64s(&mut scratch.ea[s]);
            ct_zeroize_u64s(&mut scratch.eb[s]);
            ct_zeroize_u64s(&mut scratch.c_words[s]);
            ct_zeroize_u64s(&mut scratch.a_words[s]);
            ct_zeroize_u64s(&mut scratch.b_words[s]);
        }
        ct_zeroize_u64s(&mut *scratch.prod);

        // Six packed ternary sumcheck rounds binding the 6 word-offset bits across both passes.
        let mut gammas = [[0u128; BIT_TENSOR_BITS]; 2];
        let mut bound_weight = [1u128; 2];
        let mut len_tab = BIT_TERNARY;
        for i in 0..BIT_TENSOR_BITS {
            let mut sc_locals = [[0u64; 2]; 4];
            for t in 0..2 {
                scratch.sumcheck_scratch[..len_tab].copy_from_slice(&scratch.tab[t][..len_tab]);
                let mut len3 = len_tab / 3;
                for l in (i + 1..BIT_TENSOR_BITS).rev() {
                    let mu_l = mu[t][l];
                    for idx in 0..len3 {
                        let hi_val = scratch.sumcheck_scratch[idx + len3];
                        scratch.sumcheck_scratch[idx] ^= gf128_mul_u128(mu_l, hi_val, backend);
                    }
                    len3 /= 3;
                }
                sc_locals[2 * t] = u128_to_gf128(scratch.sumcheck_scratch[1]);
                sc_locals[2 * t + 1] = u128_to_gf128(scratch.sumcheck_scratch[2]);
            }
            qsag_asm::volatile_fill(&mut scratch.sumcheck_scratch[..len_tab], 0);

            let sc_res = self.reshare_gf128_many(&sc_locals);
            zeroize_gf128_slice(&mut sc_locals);
            let s_sh = ZeroizeRepGf128Vec(sc_res?);

            let seed_sc = self.coin_flip(b"QSAG.OUTER.MULCHECK.BITS.SUMCHECK.V1")?;
            let mut xof_sc = WordSponge136::from_shake_seed(&seed_sc);
            let gamma_round = [xof_sc.squeeze_u128(), xof_sc.squeeze_u128()];

            let next_len = len_tab / 3;
            for t in 0..2 {
                let g = gamma_round[t];
                gammas[t][i] = g;
                let mu_i = mu[t][i];
                let w = 1u128 ^ gf128_mul_u128(g, 1u128 ^ mu_i, backend);
                let c0 = gf128_mul_u128(w, 1u128 ^ g, backend);
                let c1 = gf128_mul_u128(w, g, backend);
                let g_sq = gf128_mul_u128(g, g, backend);
                let c2 = gf128_mul_u128(w, g ^ g_sq, backend);
                bound_weight[t] = gf128_mul_u128(bound_weight[t], w, backend);

                for side in 0..2 {
                    let s1 = gf128_to_u128(s_sh.0[2 * t][side]);
                    let s2 = gf128_to_u128(s_sh.0[2 * t + 1][side]);
                    let s0 = gf128_to_u128(scratch.c_claim[t][side])
                        ^ gf128_mul_u128(mu_i, s1, backend);
                    let next_c = gf128_mul_u128(c0, s0, backend)
                        ^ gf128_mul_u128(c1, s1, backend)
                        ^ gf128_mul_u128(c2, s2, backend);
                    scratch.c_claim[t][side] = u128_to_gf128(next_c);
                }

                for idx in 0..next_len {
                    scratch.tab[t][idx] = gf128_mul_u128(c0, scratch.tab[t][3 * idx], backend)
                        ^ gf128_mul_u128(c1, scratch.tab[t][3 * idx + 1], backend)
                        ^ gf128_mul_u128(c2, scratch.tab[t][3 * idx + 2], backend);
                }
                qsag_asm::volatile_fill(&mut scratch.tab[t][next_len..len_tab], 0);
            }
            len_tab = next_len;
        }
        for t in 0..2 {
            qsag_asm::volatile_fill(&mut scratch.tab[t][..len_tab], 0);
        }

        // Build Four-Russians public nibble patterns and bind all `groups` into `64 * groups`
        // field elements per pass/side.
        let mut patterns = [[[0u8; BIT_NIBBLES]; 128]; 2];
        for t in 0..2 {
            let mut beta = [1u128; BIT_GROUP_WORDS];
            for (i, &g) in gammas[t].iter().enumerate() {
                let bit = 1usize << i;
                let one_plus = 1u128 ^ g;
                for u in 0..bit {
                    beta[u | bit] = gf128_mul_u128(beta[u], g, backend);
                    beta[u] = gf128_mul_u128(beta[u], one_plus, backend);
                }
            }
            for (bit, nibbles) in patterns[t].iter_mut().enumerate() {
                for nib in 0..BIT_NIBBLES {
                    let mut mask = 0u8;
                    for d in 0..4 {
                        mask |= (((beta[4 * nib + d] >> bit) & 1) as u8) << d;
                    }
                    nibbles[nib] = mask;
                }
            }
        }

        scratch.prepare_tables(groups * BIT_LANES);
        for g in 0..groups {
            let start = g * BIT_GROUP_WORDS * 6;
            let end = (start + BIT_GROUP_WORDS * 6).min(triples_raw.len());
            let chunk = &triples_raw[start..end];
            let g_words = chunk.len() / 6;
            for (u, triple) in chunk.chunks_exact(6).enumerate() {
                scratch.rows[u] = [triple[0], triple[1], triple[2], triple[3]];
            }
            if g_words < BIT_GROUP_WORDS {
                scratch.rows[g_words..].fill([0u64; 4]);
            }

            let sp = &mut *scratch;
            let dst_range = (g * BIT_LANES)..((g + 1) * BIT_LANES);
            for t in 0..2 {
                bind_group_columns(
                    &sp.rows,
                    &patterns[t],
                    &mut sp.planes,
                    &mut sp.bound,
                    backend,
                );
                let w_g = gf128_mul_u128(bound_weight[t], nu[t][g], backend);
                for (lane, b_row) in sp.bound.iter().enumerate() {
                    sp.weighted_a[0][lane] = poly128_mul_x_lane(b_row[0], lane);
                    sp.weighted_a[1][lane] = poly128_mul_x_lane(b_row[1], lane);
                    sp.y_tab[t][0][g * BIT_LANES + lane] = b_row[2];
                    sp.y_tab[t][1][g * BIT_LANES + lane] = b_row[3];
                }
                qsag_asm::bitslice::gf2_128_scale_xor_with_backend(
                    &mut sp.x_tab[t][0][dst_range.clone()],
                    &sp.weighted_a[0],
                    w_g,
                    backend,
                );
                qsag_asm::bitslice::gf2_128_scale_xor_with_backend(
                    &mut sp.x_tab[t][1][dst_range.clone()],
                    &sp.weighted_a[1],
                    w_g,
                    backend,
                );
            }
        }
        qsag_asm::volatile_fill(&mut *scratch.rows, [0u64; 4]);
        qsag_asm::volatile_fill(scratch.planes.as_flattened_mut(), [0u64; 4]);
        qsag_asm::volatile_fill(&mut *scratch.bound, [0u128; 4]);
        for s in 0..2 {
            qsag_asm::volatile_fill(&mut scratch.weighted_a[s], 0);
        }

        // Halve over the `groups` dimension, then halve over the `64` lanes.
        let mut size = groups.next_power_of_two();
        let mut cur = groups;
        while size > 1 {
            let half = size / 2;
            let hi_groups = cur - half;
            self.fold_bit_tables_round(
                &mut scratch,
                half * BIT_LANES,
                hi_groups * BIT_LANES,
                backend,
            )?;
            cur = half;
            size = half;
        }
        let mut half_lanes = BIT_LANES / 2;
        while half_lanes >= 1 {
            self.fold_bit_tables_round(&mut scratch, half_lanes, half_lanes, backend)?;
            half_lanes /= 2;
        }

        for t in 0..2 {
            for side in 0..2 {
                scratch.a_fin[t][side] = u128_to_gf128(scratch.x_tab[t][side][0]);
                scratch.b_fin[t][side] = u128_to_gf128(scratch.y_tab[t][side][0]);
            }
        }
        scratch.wipe_live_tables();

        // Zero-knowledge randomized base-case sacrifice on the single remaining relation per pass.
        scratch.u_mask = [self.prss_gf128(), self.prss_gf128()];
        scratch.v_mask = [self.prss_gf128(), self.prss_gf128()];
        let mut base_locals = [[0u64; 2]; 4];
        for t in 0..2 {
            let a0 = scratch.a_fin[t][0];
            let a1 = scratch.a_fin[t][1];
            let b0 = scratch.b_fin[t][0];
            let b1 = scratch.b_fin[t][1];
            let u0 = scratch.u_mask[t][0];
            let u1 = scratch.u_mask[t][1];
            let v0 = scratch.v_mask[t][0];
            let v1 = scratch.v_mask[t][1];
            let v_sum = xor_gf128(v0, v1);
            let b_sum = xor_gf128(b0, b1);

            let mut d1 = [0u64; 2];
            let mut lhs4 = [a0, a1, u0, u1];
            let mut rhs4 = [v_sum, v0, b_sum, b0];
            gf128_dot_acc(&mut d1, &lhs4, &rhs4, backend);
            zeroize_gf128_slice(&mut lhs4);
            zeroize_gf128_slice(&mut rhs4);

            let mut d2 = [0u64; 2];
            let mut lhs2 = [u0, u1];
            let mut rhs2 = [v_sum, v0];
            gf128_dot_acc(&mut d2, &lhs2, &rhs2, backend);
            zeroize_gf128_slice(&mut lhs2);
            zeroize_gf128_slice(&mut rhs2);

            base_locals[2 * t] = d1;
            base_locals[2 * t + 1] = d2;
        }

        let d_res = self.reshare_gf128_many(&base_locals);
        zeroize_gf128_slice(&mut base_locals);
        let d_sh = ZeroizeRepGf128Vec(d_res?);

        let seed_base = self.coin_flip(b"QSAG.OUTER.MULCHECK.BITS.BASE.V1")?;
        let mut xof_base = WordSponge136::from_shake_seed(&seed_base);
        let rb = [
            u128_to_gf128(xof_base.squeeze_nonzero_u128()),
            u128_to_gf128(xof_base.squeeze_nonzero_u128()),
        ];
        let rb_sq = [
            gf128_mul_hw(rb[0], rb[0], backend),
            gf128_mul_hw(rb[1], rb[1], backend),
        ];

        let mut to_open = Word::with_capacity(12);
        for t in 0..2 {
            let pows2 = [rb[t], rb_sq[t]];
            let mut alpha_sh = [[0u64; 2]; 2];
            let mut beta_sh = [[0u64; 2]; 2];
            let mut gamma_sh = [[0u64; 2]; 2];
            for side in 0..2 {
                alpha_sh[side] = xor_gf128(
                    scratch.a_fin[t][side],
                    gf128_mul_hw(scratch.u_mask[t][side], rb[t], backend),
                );
                beta_sh[side] = xor_gf128(
                    scratch.b_fin[t][side],
                    gf128_mul_hw(scratch.v_mask[t][side], rb[t], backend),
                );
                let mut g_val = scratch.c_claim[t][side];
                let d_arr = [d_sh.0[2 * t][side], d_sh.0[2 * t + 1][side]];
                gf128_dot_acc(&mut g_val, &d_arr, &pows2, backend);
                gamma_sh[side] = g_val;
            }
            for item in [&alpha_sh, &beta_sh, &gamma_sh] {
                to_open.push(Bit([item[0][0], item[1][0]]));
                to_open.push(Bit([item[0][1], item[1][1]]));
            }
            zeroize_gf128_slice(&mut alpha_sh);
            zeroize_gf128_slice(&mut beta_sh);
            zeroize_gf128_slice(&mut gamma_sh);
        }
        drop(d_sh);
        for pair in [
            &mut scratch.c_claim,
            &mut scratch.a_fin,
            &mut scratch.b_fin,
            &mut scratch.u_mask,
            &mut scratch.v_mask,
        ] {
            for r in pair {
                zeroize_gf128_slice(r);
            }
        }

        let mut opened = self.open_raw_bits(&to_open).map_err(|err| match err {
            Error::Disagreement(_) => Error::MultiplicationCheck,
            other => other,
        })?;
        drop(to_open);

        let mut diff_acc = 0u64;
        for t in 0..2 {
            let base = t * 6;
            let alpha = [opened[base], opened[base + 1]];
            let beta = [opened[base + 2], opened[base + 3]];
            let gamma = [opened[base + 4], opened[base + 5]];
            let expected = gf128_mul_hw(alpha, beta, backend);
            diff_acc |= (gamma[0] ^ expected[0]) | (gamma[1] ^ expected[1]);
        }
        ct_zeroize_u64s(&mut opened);
        if diff_acc != 0 {
            self.poisoned = true;
            return Err(Error::MultiplicationCheck);
        }
        self.bit_scratch = Some(scratch);
        Ok(())
    }

    fn flush_pending_bits(&mut self) -> Result<(), Error> {
        self.flush_bit_chunks(false)
    }

    // Automatic flushing checks only complete chunks. Openings and conversions
    // always call `flush_pending_bits`, which also checks the retained tail.
    fn flush_bit_chunks(&mut self, retain_tail: bool) -> Result<(), Error> {
        if self.pending_bits_raw.is_empty() {
            return Ok(());
        }
        let mut batch = core::mem::take(&mut self.pending_bits_raw);
        let checked = if retain_tail {
            batch.len() / (MAX_PENDING_BITS * 6) * (MAX_PENDING_BITS * 6)
        } else {
            batch.len()
        };
        for chunk in batch[..checked].chunks(MAX_PENDING_BITS * 6) {
            if let Err(err) = self.verify_pending_bits_slice(chunk) {
                ct_zeroize_u64s(&mut batch);
                return Err(err);
            }
        }
        let remaining = batch.len() - checked;
        batch.copy_within(checked.., 0);
        ct_zeroize_u64s(&mut batch[remaining..]);
        batch.truncate(remaining);
        self.pending_bits_raw = batch;
        Ok(())
    }

    fn reshare_fp_scalars(
        &mut self,
        locals: &[Value],
        d: Domain,
    ) -> Result<SecretVec<[Value; 2]>, Error> {
        let mut own = Vec::with_capacity(locals.len() * 4);
        let mut mine_vals = SecretVec::with_capacity(locals.len());
        for &lv in locals {
            let r0 = Self::field_pad(&mut self.pads[0], d);
            let r1 = Self::field_pad(&mut self.pads[1], d);
            let masked = d.add(lv, d.sub(r0, r1));
            mine_vals.push(masked);
            own.extend_from_slice(&masked);
        }
        let (_, next_raw) = self.raw_share_owned(own)?;
        let mut out = SecretVec::with_capacity(locals.len());
        for (mv, chunk) in mine_vals.into_iter().zip(next_raw.chunks_exact(4)) {
            let nv: Value = [chunk[0], chunk[1], chunk[2], chunk[3]];
            if !d.canonical(nv) {
                self.poisoned = true;
                return Err(Error::MultiplicationCheck);
            }
            out.push([mv, nv]);
        }
        Ok(out)
    }

    fn open_raw_fp_scalars(
        &mut self,
        shares: &[[Value; 2]],
        d: Domain,
    ) -> Result<Vec<Value>, Error> {
        let mut payload = Vec::with_capacity(shares.len() * 8);
        for pair in shares {
            payload.extend_from_slice(&pair[0]);
            payload.extend_from_slice(&pair[1]);
        }
        let received = self.raw_exchange([payload.clone(), payload])?;
        if received.iter().any(|v| v.len() != shares.len() * 8) {
            self.poisoned = true;
            return Err(Error::InvalidConfiguration);
        }
        let mut out = Vec::with_capacity(shares.len());
        for (i, a) in shares.iter().enumerate() {
            let prev: [Value; 2] = core::array::from_fn(|j| {
                let s = &received[0][8 * i + 4 * j..8 * i + 4 * j + 4];
                [s[0], s[1], s[2], s[3]]
            });
            let next: [Value; 2] = core::array::from_fn(|j| {
                let s = &received[1][8 * i + 4 * j..8 * i + 4 * j + 4];
                [s[0], s[1], s[2], s[3]]
            });
            if prev[1] != a[0] {
                self.poisoned = true;
                return Err(Error::Disagreement((self.party + 2) % 3));
            }
            if next[0] != a[1] || prev[0] != next[1] || !d.canonical(prev[0]) {
                self.poisoned = true;
                return Err(Error::Disagreement((self.party + 1) % 3));
            }
            out.push(d.add(d.add(a[0], a[1]), prev[0]));
        }
        Ok(out)
    }

    /// Batch-verify large-prime (`Secp256k1` / `Ed25519`, `p > 2^254.99`) multiplications
    /// via replicated BBCGGI19 inner-product folding + zero-knowledge base-case sacrifice.
    /// Per-flush cheating probability is `<= FIELD_CHECK_NUMERATOR / (p - 1) = 35 / (p - 1)`:
    /// `< 2^-250.87` for `Secp` and `< 2^-249.87` for `Ed`, hence `< 2^-249` for both.
    fn verify_pending_large_prime_slice(
        &mut self,
        triples: &[PendingFieldTriple],
        d: Domain,
    ) -> Result<(), Error> {
        if triples.is_empty() {
            return Ok(());
        }
        let total = triples.len() * 64;
        let seed0 = self.coin_flip(b"QSAG.OUTER.MULCHECK.FP.INIT.V1")?;
        let mut xof0 = WordSponge136::from_shake_seed(&seed0);

        struct FpScratch {
            a_vec: Vec<[Value; 2]>,
            b_vec: Vec<[Value; 2]>,
            cap: usize,
            c_claim: [Value; 2],
            u_sh: [Value; 2],
            v_sh: [Value; 2],
            d_loc: [Value; 2],
        }
        impl Drop for FpScratch {
            fn drop(&mut self) {
                for vec_buf in [&mut self.a_vec, &mut self.b_vec] {
                    if vec_buf.len() < self.cap && vec_buf.capacity() >= self.cap {
                        vec_buf.resize(self.cap, [[0; 4]; 2]);
                    }
                    for pair in vec_buf.iter_mut() {
                        ct_zeroize_u64s(&mut pair[0]);
                        ct_zeroize_u64s(&mut pair[1]);
                    }
                }
                for pair in [
                    &mut self.c_claim,
                    &mut self.u_sh,
                    &mut self.v_sh,
                    &mut self.d_loc,
                ] {
                    ct_zeroize_u64s(&mut pair[0]);
                    ct_zeroize_u64s(&mut pair[1]);
                }
            }
        }

        let mut sc = FpScratch {
            a_vec: Vec::with_capacity(total + 1),
            b_vec: Vec::with_capacity(total + 1),
            cap: total + 1,
            c_claim: [[0; 4]; 2],
            u_sh: [[0; 4]; 2],
            v_sh: [[0; 4]; 2],
            d_loc: [[0; 4]; 2],
        };

        for (x_fw, y_fw, z_fw) in triples {
            for ((x, y), z) in x_fw.iter().zip(y_fw).zip(z_fw) {
                let chi = squeeze_fp_challenge(&mut xof0, d);
                sc.a_vec.push([d.mul(chi, x[0]), d.mul(chi, x[1])]);
                sc.b_vec.push(*y);
                sc.c_claim[0] = d.add(sc.c_claim[0], d.mul(chi, z[0]));
                sc.c_claim[1] = d.add(sc.c_claim[1], d.mul(chi, z[1]));
            }
        }

        let rep_local_mul = |x: &[Value; 2], y: &[Value; 2]| -> Value {
            d.add(d.mul(x[0], d.add(y[0], y[1])), d.mul(x[1], y[0]))
        };

        while sc.a_vec.len() > 1 {
            if sc.a_vec.len() % 2 == 1 {
                sc.a_vec.push([[0; 4]; 2]);
                sc.b_vec.push([[0; 4]; 2]);
            }
            let half = sc.a_vec.len() / 2;
            sc.d_loc = [[0u64; 4]; 2];
            for k in 0..half {
                sc.d_loc[0] = d.add(
                    sc.d_loc[0],
                    rep_local_mul(&sc.a_vec[2 * k], &sc.b_vec[2 * k + 1]),
                );
                sc.d_loc[1] = d.add(
                    sc.d_loc[1],
                    rep_local_mul(&sc.a_vec[2 * k + 1], &sc.b_vec[2 * k]),
                );
            }
            let mut reshared = self.reshare_fp_scalars(&sc.d_loc, d)?;
            let seed_rk = match self.coin_flip(b"QSAG.OUTER.MULCHECK.FP.FOLD.V1") {
                Ok(s) => s,
                Err(e) => {
                    for r in &mut reshared {
                        ct_zeroize_u64s(&mut r[0]);
                        ct_zeroize_u64s(&mut r[1]);
                    }
                    return Err(e);
                }
            };
            let mut xof_rk = WordSponge136::from_shake_seed(&seed_rk);
            let rk = squeeze_fp_challenge(&mut xof_rk, d);
            let rk_sq = d.mul(rk, rk);

            sc.c_claim = [
                d.add(
                    reshared[0][0],
                    d.add(d.mul(rk, sc.c_claim[0]), d.mul(rk_sq, reshared[1][0])),
                ),
                d.add(
                    reshared[0][1],
                    d.add(d.mul(rk, sc.c_claim[1]), d.mul(rk_sq, reshared[1][1])),
                ),
            ];
            for r in &mut reshared {
                ct_zeroize_u64s(&mut r[0]);
                ct_zeroize_u64s(&mut r[1]);
            }
            for k in 0..half {
                let na = [
                    d.add(sc.a_vec[2 * k][0], d.mul(rk, sc.a_vec[2 * k + 1][0])),
                    d.add(sc.a_vec[2 * k][1], d.mul(rk, sc.a_vec[2 * k + 1][1])),
                ];
                let nb = [
                    d.add(d.mul(rk, sc.b_vec[2 * k][0]), sc.b_vec[2 * k + 1][0]),
                    d.add(d.mul(rk, sc.b_vec[2 * k][1]), sc.b_vec[2 * k + 1][1]),
                ];
                sc.a_vec[k] = na;
                sc.b_vec[k] = nb;
            }
            sc.a_vec.truncate(half);
            sc.b_vec.truncate(half);
        }

        let a0 = sc.a_vec[0];
        let b0 = sc.b_vec[0];
        sc.u_sh = [
            Self::field_pad(&mut self.pads[0], d),
            Self::field_pad(&mut self.pads[1], d),
        ];
        sc.v_sh = [
            Self::field_pad(&mut self.pads[0], d),
            Self::field_pad(&mut self.pads[1], d),
        ];
        sc.d_loc = [
            d.add(rep_local_mul(&a0, &sc.v_sh), rep_local_mul(&sc.u_sh, &b0)),
            rep_local_mul(&sc.u_sh, &sc.v_sh),
        ];
        let mut d_sh = self.reshare_fp_scalars(&sc.d_loc, d)?;

        let seed_base = match self.coin_flip(b"QSAG.OUTER.MULCHECK.FP.BASE.V1") {
            Ok(s) => s,
            Err(e) => {
                for r in &mut d_sh {
                    ct_zeroize_u64s(&mut r[0]);
                    ct_zeroize_u64s(&mut r[1]);
                }
                return Err(e);
            }
        };
        let mut xof_base = WordSponge136::from_shake_seed(&seed_base);
        let rb = loop {
            let cand = squeeze_fp_challenge(&mut xof_base, d);
            if cand != [0; 4] {
                break cand;
            }
        };
        let rb_sq = d.mul(rb, rb);

        let alpha_sh = [
            d.add(a0[0], d.mul(rb, sc.u_sh[0])),
            d.add(a0[1], d.mul(rb, sc.u_sh[1])),
        ];
        let beta_sh = [
            d.add(b0[0], d.mul(rb, sc.v_sh[0])),
            d.add(b0[1], d.mul(rb, sc.v_sh[1])),
        ];
        let gamma_sh = [
            d.add(
                sc.c_claim[0],
                d.add(d.mul(rb, d_sh[0][0]), d.mul(rb_sq, d_sh[1][0])),
            ),
            d.add(
                sc.c_claim[1],
                d.add(d.mul(rb, d_sh[0][1]), d.mul(rb_sq, d_sh[1][1])),
            ),
        ];
        for r in &mut d_sh {
            ct_zeroize_u64s(&mut r[0]);
            ct_zeroize_u64s(&mut r[1]);
        }
        let mut to_open = [alpha_sh, beta_sh, gamma_sh];
        let opened_res = self.open_raw_fp_scalars(&to_open, d);
        for item in &mut to_open {
            ct_zeroize_u64s(&mut item[0]);
            ct_zeroize_u64s(&mut item[1]);
        }
        let opened = opened_res.map_err(|err| match err {
            Error::Disagreement(_) => Error::MultiplicationCheck,
            other => other,
        })?;
        if opened[2] != d.mul(opened[0], opened[1]) {
            self.poisoned = true;
            return Err(Error::MultiplicationCheck);
        }
        Ok(())
    }

    fn prss_g3(&mut self) -> RepGoldExt3 {
        let sample = |sp: &mut WordSponge136| -> GoldExt3 {
            core::array::from_fn(|_| {
                loop {
                    let w = sp.squeeze_u64();
                    if w < GOLDILOCKS_P {
                        return w;
                    }
                }
            })
        };
        [sample(&mut self.pads[0]), sample(&mut self.pads[1])]
    }

    fn reshare_g3_many(&mut self, locals: &[GoldExt3]) -> Result<SecretVec<RepGoldExt3>, Error> {
        let mut own = Vec::with_capacity(locals.len() * 3);
        let mut mine_vals = SecretVec::with_capacity(locals.len());
        for &lv in locals {
            let r = self.prss_g3();
            let masked = g3_add(lv, g3_sub(r[0], r[1]));
            mine_vals.push(masked);
            own.extend_from_slice(&masked);
        }
        let (_, next_raw) = self.raw_share_owned(own)?;
        let mut out = SecretVec::with_capacity(locals.len());
        for (mv, chunk) in mine_vals.into_iter().zip(next_raw.chunks_exact(3)) {
            let nv: GoldExt3 = [chunk[0], chunk[1], chunk[2]];
            if !g3_canonical(nv) {
                self.poisoned = true;
                return Err(Error::MultiplicationCheck);
            }
            out.push([mv, nv]);
        }
        Ok(out)
    }

    fn open_raw_g3(&mut self, shares: &[RepGoldExt3]) -> Result<Vec<GoldExt3>, Error> {
        let mut payload = Vec::with_capacity(shares.len() * 6);
        for pair in shares {
            payload.extend_from_slice(&pair[0]);
            payload.extend_from_slice(&pair[1]);
        }
        let received = self.raw_exchange([payload.clone(), payload])?;
        if received.iter().any(|v| v.len() != shares.len() * 6) {
            self.poisoned = true;
            return Err(Error::InvalidConfiguration);
        }
        let mut out = Vec::with_capacity(shares.len());
        for (i, a) in shares.iter().enumerate() {
            let prev: RepGoldExt3 = core::array::from_fn(|j| {
                let s = &received[0][6 * i + 3 * j..6 * i + 3 * j + 3];
                [s[0], s[1], s[2]]
            });
            let next: RepGoldExt3 = core::array::from_fn(|j| {
                let s = &received[1][6 * i + 3 * j..6 * i + 3 * j + 3];
                [s[0], s[1], s[2]]
            });
            if prev[1] != a[0] {
                self.poisoned = true;
                return Err(Error::Disagreement((self.party + 2) % 3));
            }
            if next[0] != a[1] || prev[0] != next[1] || !g3_canonical(prev[0]) {
                self.poisoned = true;
                return Err(Error::Disagreement((self.party + 1) % 3));
            }
            out.push(g3_add(g3_add(a[0], a[1]), prev[0]));
        }
        Ok(out)
    }

    /// Batch-verify Goldilocks (`p = 2^64 - 2^32 + 1`) multiplications lifted into the
    /// irreducible cubic extension `GF(p)[u] / (u^3 - 7)` (`p^3 > 2^191.99`). Per-flush
    /// cheating probability is `<= FIELD_CHECK_NUMERATOR / (p^3 - 1) = 35 / (p^3 - 1)
    /// < 2^-186.87 < 2^-186`.
    fn verify_pending_gold_slice(&mut self, triples: &[PendingFieldTriple]) -> Result<(), Error> {
        if triples.is_empty() {
            return Ok(());
        }
        let total = triples.len() * 64;
        let seed0 = self.coin_flip(b"QSAG.OUTER.MULCHECK.GOLD.INIT.V1")?;
        let mut xof0 = WordSponge136::from_shake_seed(&seed0);

        struct GoldScratch {
            a_vec: Vec<RepGoldExt3>,
            b_vec: Vec<RepGoldExt3>,
            cap: usize,
            c_claim: RepGoldExt3,
            u_sh: RepGoldExt3,
            v_sh: RepGoldExt3,
            d_loc: [GoldExt3; 2],
        }
        impl Drop for GoldScratch {
            fn drop(&mut self) {
                for vec_buf in [&mut self.a_vec, &mut self.b_vec] {
                    if vec_buf.len() < self.cap && vec_buf.capacity() >= self.cap {
                        vec_buf.resize(self.cap, [[0; 3]; 2]);
                    }
                    for pair in vec_buf.iter_mut() {
                        ct_zeroize_u64s(&mut pair[0]);
                        ct_zeroize_u64s(&mut pair[1]);
                    }
                }
                for pair in [
                    &mut self.c_claim,
                    &mut self.u_sh,
                    &mut self.v_sh,
                    &mut self.d_loc,
                ] {
                    ct_zeroize_u64s(&mut pair[0]);
                    ct_zeroize_u64s(&mut pair[1]);
                }
            }
        }

        let mut sc = GoldScratch {
            a_vec: Vec::with_capacity(total + 1),
            b_vec: Vec::with_capacity(total + 1),
            cap: total + 1,
            c_claim: [[0; 3]; 2],
            u_sh: [[0; 3]; 2],
            v_sh: [[0; 3]; 2],
            d_loc: [[0; 3]; 2],
        };

        for (x_fw, y_fw, z_fw) in triples {
            for ((x, y), z) in x_fw.iter().zip(y_fw).zip(z_fw) {
                let chi = squeeze_g3_challenge(&mut xof0);
                let scale_base = |c: GoldExt3, v: u64| -> GoldExt3 {
                    [gl_mul(c[0], v), gl_mul(c[1], v), gl_mul(c[2], v)]
                };
                sc.a_vec
                    .push([scale_base(chi, x[0][0]), scale_base(chi, x[1][0])]);
                sc.b_vec.push([[y[0][0], 0, 0], [y[1][0], 0, 0]]);
                sc.c_claim[0] = g3_add(sc.c_claim[0], scale_base(chi, z[0][0]));
                sc.c_claim[1] = g3_add(sc.c_claim[1], scale_base(chi, z[1][0]));
            }
        }

        let rep_local_mul = |x: &RepGoldExt3, y: &RepGoldExt3| -> GoldExt3 {
            g3_add(g3_mul(x[0], g3_add(y[0], y[1])), g3_mul(x[1], y[0]))
        };

        while sc.a_vec.len() > 1 {
            if sc.a_vec.len() % 2 == 1 {
                sc.a_vec.push([[0; 3]; 2]);
                sc.b_vec.push([[0; 3]; 2]);
            }
            let half = sc.a_vec.len() / 2;
            sc.d_loc = [[0u64; 3]; 2];
            for k in 0..half {
                sc.d_loc[0] = g3_add(
                    sc.d_loc[0],
                    rep_local_mul(&sc.a_vec[2 * k], &sc.b_vec[2 * k + 1]),
                );
                sc.d_loc[1] = g3_add(
                    sc.d_loc[1],
                    rep_local_mul(&sc.a_vec[2 * k + 1], &sc.b_vec[2 * k]),
                );
            }
            let mut reshared = self.reshare_g3_many(&sc.d_loc)?;
            let seed_rk = match self.coin_flip(b"QSAG.OUTER.MULCHECK.GOLD.FOLD.V1") {
                Ok(s) => s,
                Err(e) => {
                    for r in &mut reshared {
                        ct_zeroize_u64s(&mut r[0]);
                        ct_zeroize_u64s(&mut r[1]);
                    }
                    return Err(e);
                }
            };
            let mut xof_rk = WordSponge136::from_shake_seed(&seed_rk);
            let rk = squeeze_g3_challenge(&mut xof_rk);
            let rk_sq = g3_mul(rk, rk);

            sc.c_claim = [
                g3_add(
                    reshared[0][0],
                    g3_add(g3_mul(rk, sc.c_claim[0]), g3_mul(rk_sq, reshared[1][0])),
                ),
                g3_add(
                    reshared[0][1],
                    g3_add(g3_mul(rk, sc.c_claim[1]), g3_mul(rk_sq, reshared[1][1])),
                ),
            ];
            for r in &mut reshared {
                ct_zeroize_u64s(&mut r[0]);
                ct_zeroize_u64s(&mut r[1]);
            }
            for k in 0..half {
                let na = [
                    g3_add(sc.a_vec[2 * k][0], g3_mul(rk, sc.a_vec[2 * k + 1][0])),
                    g3_add(sc.a_vec[2 * k][1], g3_mul(rk, sc.a_vec[2 * k + 1][1])),
                ];
                let nb = [
                    g3_add(g3_mul(rk, sc.b_vec[2 * k][0]), sc.b_vec[2 * k + 1][0]),
                    g3_add(g3_mul(rk, sc.b_vec[2 * k][1]), sc.b_vec[2 * k + 1][1]),
                ];
                sc.a_vec[k] = na;
                sc.b_vec[k] = nb;
            }
            sc.a_vec.truncate(half);
            sc.b_vec.truncate(half);
        }

        let a0 = sc.a_vec[0];
        let b0 = sc.b_vec[0];
        sc.u_sh = self.prss_g3();
        sc.v_sh = self.prss_g3();
        sc.d_loc = [
            g3_add(rep_local_mul(&a0, &sc.v_sh), rep_local_mul(&sc.u_sh, &b0)),
            rep_local_mul(&sc.u_sh, &sc.v_sh),
        ];
        let mut d_sh = self.reshare_g3_many(&sc.d_loc)?;

        let seed_base = match self.coin_flip(b"QSAG.OUTER.MULCHECK.GOLD.BASE.V1") {
            Ok(s) => s,
            Err(e) => {
                for r in &mut d_sh {
                    ct_zeroize_u64s(&mut r[0]);
                    ct_zeroize_u64s(&mut r[1]);
                }
                return Err(e);
            }
        };
        let mut xof_base = WordSponge136::from_shake_seed(&seed_base);
        let rb = loop {
            let cand = squeeze_g3_challenge(&mut xof_base);
            if cand != [0; 3] {
                break cand;
            }
        };
        let rb_sq = g3_mul(rb, rb);

        let alpha_sh = [
            g3_add(a0[0], g3_mul(rb, sc.u_sh[0])),
            g3_add(a0[1], g3_mul(rb, sc.u_sh[1])),
        ];
        let beta_sh = [
            g3_add(b0[0], g3_mul(rb, sc.v_sh[0])),
            g3_add(b0[1], g3_mul(rb, sc.v_sh[1])),
        ];
        let gamma_sh = [
            g3_add(
                sc.c_claim[0],
                g3_add(g3_mul(rb, d_sh[0][0]), g3_mul(rb_sq, d_sh[1][0])),
            ),
            g3_add(
                sc.c_claim[1],
                g3_add(g3_mul(rb, d_sh[0][1]), g3_mul(rb_sq, d_sh[1][1])),
            ),
        ];
        for r in &mut d_sh {
            ct_zeroize_u64s(&mut r[0]);
            ct_zeroize_u64s(&mut r[1]);
        }
        let mut to_open = [alpha_sh, beta_sh, gamma_sh];
        let opened_res = self.open_raw_g3(&to_open);
        for item in &mut to_open {
            ct_zeroize_u64s(&mut item[0]);
            ct_zeroize_u64s(&mut item[1]);
        }
        let opened = opened_res.map_err(|err| match err {
            Error::Disagreement(_) => Error::MultiplicationCheck,
            other => other,
        })?;
        if opened[2] != g3_mul(opened[0], opened[1]) {
            self.poisoned = true;
            return Err(Error::MultiplicationCheck);
        }
        Ok(())
    }

    fn flush_pending_domain(&mut self, d: Domain) -> Result<(), Error> {
        let batch = match d {
            Domain::Secp => core::mem::take(&mut self.pending_secp),
            Domain::Ed => core::mem::take(&mut self.pending_ed),
            Domain::Gold => core::mem::take(&mut self.pending_gold),
            Domain::Bit => return self.flush_pending_bits(),
        };
        if batch.is_empty() {
            return Ok(());
        }
        for chunk in batch.chunks(MAX_PENDING_FIELD_WORDS) {
            let res = if d == Domain::Gold {
                self.verify_pending_gold_slice(chunk)
            } else {
                self.verify_pending_large_prime_slice(chunk, d)
            };
            res?;
        }
        Ok(())
    }

    /// Mandatory pre-open active multiplication verification barrier across all
    /// Boolean and prime-field domains. Zero secret-dependent wire values may open
    /// unless this barrier succeeds.
    pub fn verify_all_pending(&mut self) -> Result<(), Error> {
        if self.poisoned {
            return Err(Error::MultiplicationCheck);
        }
        self.flush_pending_bits()?;
        self.flush_pending_domain(Domain::Secp)?;
        self.flush_pending_domain(Domain::Ed)?;
        self.flush_pending_domain(Domain::Gold)?;
        Ok(())
    }

    fn and_into(&mut self, pairs: &[(Bit, Bit)], out: &mut Word) -> Result<(), Error> {
        if self.poisoned {
            out.clear();
            return Err(Error::MultiplicationCheck);
        }
        let k = pairs.len();
        if k == 0 {
            out.clear();
            return Ok(());
        }
        ensure_scratch_len(&mut self.scratch_r, k);
        ensure_scratch_len(&mut self.scratch_s, k);
        self.pads[0].squeeze_u64s(&mut self.scratch_r[..k]);
        self.pads[1].squeeze_u64s(&mut self.scratch_s[..k]);
        let mut own = Vec::with_capacity(k);
        for ((&(a, b), &r), &s) in pairs
            .iter()
            .zip(&self.scratch_r[..k])
            .zip(&self.scratch_s[..k])
        {
            own.push((a.0[0] & (b.0[0] ^ b.0[1])) ^ (a.0[1] & b.0[0]) ^ r ^ s);
        }
        #[cfg(test)]
        if let Some(FaultInjection::BitAnd {
            ref mut call_countdown,
            gate,
            lane,
        }) = self.fault
        {
            if *call_countdown == 0 {
                let idx = gate.min(own.len() - 1);
                own[idx] ^= 1u64 << (lane & 63);
                self.fault = None;
            } else {
                *call_countdown -= 1;
            }
        }
        let (mine, next) = match self.raw_share_owned(own) {
            Ok(shares) => shares,
            Err(err) => {
                out.clear();
                return Err(err);
            }
        };
        out.resize(k, Bit::default());
        for (dst, (&a, &b)) in out.iter_mut().zip(mine.iter().zip(&next)) {
            *dst = Bit([a, b]);
        }
        let old_raw = self.pending_bits_raw.len();
        reserve_wiped(&mut self.pending_bits_raw, k * 6);
        self.pending_bits_raw.resize(old_raw + k * 6, 0);
        for (dst, (&(a, b), &z)) in self.pending_bits_raw[old_raw..]
            .chunks_exact_mut(6)
            .zip(pairs.iter().zip(out.iter()))
        {
            dst[0] = a.0[0];
            dst[1] = a.0[1];
            dst[2] = b.0[0];
            dst[3] = b.0[1];
            dst[4] = z.0[0];
            dst[5] = z.0[1];
        }
        if self.pending_bits_raw.len() >= MAX_PENDING_BITS * 6 {
            self.flush_bit_chunks(true)?;
        }
        Ok(())
    }

    /// Reconstruct only explicitly public data after verifying all pending
    /// Boolean and prime-field multiplications. Both holders supply every
    /// component; inconsistencies abort before the caller receives any output.
    pub fn open(&mut self, bits: &[Bit]) -> Result<Vec<u64>, Error> {
        self.verify_all_pending()?;
        self.open_raw_bits(bits)
    }

    pub fn agree(&mut self, root: [u8; 32]) -> Result<(), Error> {
        self.verify_all_pending()?;
        let words: Vec<_> = root
            .chunks_exact(8)
            .map(|b| u64::from_le_bytes(b.try_into().unwrap()))
            .collect();
        let received = self.raw_exchange([words.clone(), words.clone()])?;
        for (i, r) in received.iter().enumerate() {
            if &r[..] != words.as_slice() {
                self.poisoned = true;
                return Err(Error::Disagreement(
                    (self.party + if i == 0 { 2 } else { 1 }) % 3,
                ));
            }
        }
        Ok(())
    }

}


impl<T: Transport> Core for Engine<T> {
    type Bit = Bit;
    #[inline]
    fn constant(&self, x: u64) -> Bit {
        Engine::constant(self, x)
    }
    fn share(&mut self, own: &[u64]) -> Result<Word, Error> {
        Engine::share(self, own)
    }
    fn share_uniform_lanes(&mut self, own: &[u64]) -> Result<Word, Error> {
        Engine::share_uniform_lanes(self, own)
    }
    #[inline]
    fn and_into(&mut self, pairs: &[(Bit, Bit)], out: &mut Word) -> Result<(), Error> {
        Engine::and_into(self, pairs, out)
    }
    fn verify_all_pending(&mut self) -> Result<(), Error> {
        Engine::verify_all_pending(self)
    }
    fn open(&mut self, bits: &[Bit]) -> Result<Vec<u64>, Error> {
        Engine::open(self, bits)
    }
    fn open_lanes(&mut self, bits: &[Bit], mask: u64) -> Result<Vec<u64>, Error> {
        // Replicated shares are lane-wise, so hidden lanes are simply withheld.
        let masked: Word = bits
            .iter()
            .map(|b| Bit([b.0[0] & mask, b.0[1] & mask]))
            .collect();
        Engine::open(self, &masked)
    }
    fn agree(&mut self, root: [u8; 32]) -> Result<(), Error> {
        Engine::agree(self, root)
    }
    fn poison(&mut self) {
        self.poisoned = true;
    }
    fn fconstant(&self, value: Value, _d: Domain) -> FieldWord {
        Engine::fconstant(self, value)
    }
    fn fscale_lanes(&self, a: &FieldWord, by: &[Value], d: Domain) -> FieldWord {
        a.iter()
            .zip(by)
            .map(|(a, by)| a.map(|v| d.mul(v, *by)))
            .collect()
    }
    fn fadd(&self, a: &FieldWord, b: &FieldWord, d: Domain) -> FieldWord {
        a.iter()
            .zip(b)
            .map(|(a, b)| core::array::from_fn(|j| d.add(a[j], b[j])))
            .collect()
    }
    fn fsub(&self, a: &FieldWord, b: &FieldWord, d: Domain) -> FieldWord {
        a.iter()
            .zip(b)
            .map(|(a, b)| core::array::from_fn(|j| d.sub(a[j], b[j])))
            .collect()
    }
    fn fscale(&self, a: &FieldWord, b: Value, d: Domain) -> FieldWord {
        a.iter().map(|a| a.map(|v| d.mul(v, b))).collect()
    }
    fn frandom(&mut self, d: Domain) -> Result<FieldWord, Error> {
        Ok(Engine::frandom(self, d))
    }
    fn fmul_many(
        &mut self,
        pairs: &[(&FieldWord, &FieldWord)],
        d: Domain,
    ) -> Result<Vec<FieldWord>, Error> {
        Engine::fmul_many(self, pairs, d)
    }
    fn fopen_many(&mut self, words: &[FieldWord], d: Domain) -> Result<Vec<Vec<Value>>, Error> {
        Engine::fopen_many(self, words, d)
    }
    fn bits_to_field_many(&mut self, words: &[Word], d: Domain) -> Result<Vec<FieldWord>, Error> {
        Engine::bits_to_field_many(self, words, d)
    }
    fn field_to_bits_many(&mut self, words: &[&FieldWord], d: Domain) -> Result<Vec<Word>, Error> {
        Engine::field_to_bits_many(self, words, d)
    }
    fn lift_bits_many(&mut self, bits: &[Bit], d: Domain) -> Result<Vec<FieldWord>, Error> {
        Engine::lift_bits_many(self, bits, d)
    }
    #[cfg(test)]
    fn take_field_fault(&mut self) -> Option<FaultInjection> {
        if matches!(self.fault, Some(FaultInjection::FieldMul { .. })) {
            self.fault.take()
        } else {
            None
        }
    }
    #[cfg(test)]
    fn restore_fault(&mut self, fault: FaultInjection) {
        self.fault = Some(fault);
    }
    #[cfg(test)]
    fn on_public_or_view_open(&self) {
        self.transport.on_public_or_view_open();
    }
}

/// Backend-independent gadgets over any [`Core`] engine.
pub(crate) trait Gadgets: Core {
    fn and(&mut self, pairs: &[(Self::Bit, Self::Bit)]) -> Result<Word<Self::Bit>, Error> {
        let mut out = SecretVec::with_capacity(pairs.len());
        self.and_into(pairs, &mut out)?;
        Ok(out)
    }

    fn number(&self, x: Value, n: usize) -> Word<Self::Bit> {
        (0..n)
            .map(|i| {
                self.constant(if i < 256 && (x[i / 64] >> (i % 64)) & 1 != 0 {
                    u64::MAX
                } else {
                    0
                })
            })
            .collect()
    }

    fn xor(&self, a: &[Self::Bit], b: &[Self::Bit]) -> Word<Self::Bit> {
        a.iter().zip(b).map(|(&a, &b)| a ^ b).collect()
    }

    #[cfg(test)]
    fn select(&mut self, c: Self::Bit, a: &[Self::Bit], b: &[Self::Bit]) -> Result<Word<Self::Bit>, Error> {
        let pairs: SecretVec<_> = a.iter().zip(b).map(|(&a, &b)| (c, a ^ b)).collect();
        Ok(self
            .and(&pairs)?
            .iter()
            .zip(b)
            .map(|(&x, &b)| x ^ b)
            .collect())
    }

    fn select_many(
        &mut self,
        conds: &[Self::Bit],
        a_words: &[Word<Self::Bit>],
        b_words: &[Word<Self::Bit>],
    ) -> Result<Vec<Word<Self::Bit>>, Error> {
        if a_words.is_empty() {
            return Ok(Vec::new());
        }
        let width = a_words[0].len();
        let mut pairs = SecretVec::with_capacity(a_words.len() * width);
        for ((&c, a), b) in conds.iter().zip(a_words).zip(b_words) {
            for (&ai, &bi) in a.iter().zip(b) {
                pairs.push((c, ai ^ bi));
            }
        }
        let prods = self.and(&pairs)?;
        let mut out = Vec::with_capacity(a_words.len());
        for (b, chunk) in b_words.iter().zip(prods.chunks_exact(width)) {
            out.push(chunk.iter().zip(b).map(|(&p, &bi)| p ^ bi).collect());
        }
        Ok(out)
    }

    /// Parallel-prefix binary adder; logarithmic communication depth for single words.
    #[cfg(test)]
    fn add(&mut self, a: &[Self::Bit], b: &[Self::Bit], carry: Self::Bit) -> Result<(Word<Self::Bit>, Self::Bit), Error> {
        let n = a.len();
        let p = self.xor(a, b);
        let mut pp = p.clone();
        let mut g = self.and(
            &a.iter()
                .copied()
                .zip(b.iter().copied())
                .collect::<SecretVec<_>>(),
        )?;
        let mut step = 1;
        while step < n {
            let indices: Vec<_> = (2 * step - 1..n).step_by(2 * step).collect();
            self.prefix_layer(&indices, step, &mut pp, &mut g)?;
            step *= 2;
        }
        step /= 4;
        while step != 0 {
            let indices: Vec<_> = (3 * step - 1..n).step_by(2 * step).collect();
            self.prefix_layer(&indices, step, &mut pp, &mut g)?;
            step /= 2;
        }
        let cs = self.and(&pp.into_iter().map(|p| (p, carry)).collect::<SecretVec<_>>())?;
        for (gi, &csi) in g.iter_mut().zip(&cs) {
            *gi = *gi ^ csi;
        }
        Ok((
            (0..n)
                .map(|i| p[i] ^ if i == 0 { carry } else { g[i - 1] })
                .collect(),
            g[n - 1],
        ))
    }

    #[cfg(test)]
    fn prefix_layer(
        &mut self,
        indices: &[usize],
        step: usize,
        p: &mut [Self::Bit],
        g: &mut [Self::Bit],
    ) -> Result<(), Error> {
        if indices.is_empty() {
            return Ok(());
        }
        let pairs: SecretVec<_> = indices
            .iter()
            .flat_map(|&i| [(p[i], g[i - step]), (p[i], p[i - step])])
            .collect();
        let products = self.and(&pairs)?;
        for (k, &i) in indices.iter().enumerate() {
            g[i] = g[i] ^ products[2 * k];
            p[i] = products[2 * k + 1];
        }
        Ok(())
    }

    /// Vectorized 1-AND-per-bit Boyar-Peralta adder across `K` words in parallel.
    fn add_many(
        &mut self,
        a_words: &[Word<Self::Bit>],
        b_words: &[Word<Self::Bit>],
        carry_mask: u64,
    ) -> Result<(Vec<Word<Self::Bit>>, Word<Self::Bit>), Error> {
        if a_words.is_empty() {
            return Ok((Vec::new(), SecretVec::new()));
        }
        let k = a_words.len();
        let n = a_words[0].len();
        let mut sums: Vec<Word<Self::Bit>> = (0..k).map(|_| SecretVec::with_capacity(n)).collect();
        let mut carries: Word<Self::Bit> = vec![self.constant(carry_mask); k].into();
        let zero = self.constant(0);
        let mut pairs = SecretVec::with_capacity(k);
        pairs.resize(k, (zero, zero));
        let mut prods = SecretVec::with_capacity(k);
        for bit in 0..n {
            for (pair_slot, ((a, b), (&c, sum_w))) in pairs.iter_mut().zip(
                a_words
                    .iter()
                    .zip(b_words)
                    .zip(carries.iter().zip(&mut sums)),
            ) {
                let ai = a[bit];
                let bi = b[bit];
                sum_w.push(ai ^ bi ^ c);
                *pair_slot = (ai ^ c, bi ^ c);
            }
            self.and_into(&pairs, &mut prods)?;
            for (c, &p) in carries.iter_mut().zip(&prods) {
                *c = *c ^ p;
            }
        }
        Ok((sums, carries))
    }

    /// Vectorized addition of `a_words` with a public constant `k_val` (`1` `AND` per bit).
    fn add_public_many(
        &mut self,
        a_words: &[Word<Self::Bit>],
        k_val: Value,
        carry_mask: u64,
        width: usize,
    ) -> Result<(Vec<Word<Self::Bit>>, Word<Self::Bit>), Error> {
        if a_words.is_empty() {
            return Ok((Vec::new(), SecretVec::new()));
        }
        let k = a_words.len();
        let k_bits = self.number(k_val, width);
        let mut sums: Vec<Word<Self::Bit>> = (0..k).map(|_| SecretVec::with_capacity(width)).collect();
        let mut carries: Word<Self::Bit> = vec![self.constant(carry_mask); k].into();
        let zero = self.constant(0);
        let mut pairs = SecretVec::with_capacity(k);
        pairs.resize(k, (zero, zero));
        let mut prods = SecretVec::with_capacity(k);
        for (bit, &kb) in k_bits.iter().enumerate() {
            for (pair_slot, (a, (&c, sum_w))) in
                pairs.iter_mut().zip(a_words.iter().zip(carries.iter().zip(&mut sums)))
            {
                let ai = a[bit];
                sum_w.push(ai ^ kb ^ c);
                *pair_slot = (ai ^ c, kb ^ c);
            }
            self.and_into(&pairs, &mut prods)?;
            for (c, &p) in carries.iter_mut().zip(&prods) {
                *c = *c ^ p;
            }
        }
        Ok((sums, carries))
    }

    /// Check `v < d.modulus()` across `v_words` (`width == d.width()`).
    /// Since `p = 2^n - c`, `v < p <==> v + c < 2^n <==> carry_out_n(v + c) == 0`.
    fn less_than_modulus_many(&mut self, v_words: &[Word<Self::Bit>], d: Domain) -> Result<Word<Self::Bit>, Error> {
        if v_words.is_empty() {
            return Ok(SecretVec::new());
        }
        let (_, carries) = self.add_public_many(v_words, domain_c_const(d), 0, d.width())?;
        let ones = self.constant(u64::MAX);
        Ok(carries.into_iter().map(|ge| ge ^ ones).collect())
    }

    #[cfg(test)]
    fn reduce_once(&mut self, a: &[Self::Bit], d: Domain) -> Result<Word<Self::Bit>, Error> {
        let modulus = self.number(d.modulus(), a.len());
        let not_m: Word<Self::Bit> = modulus
            .iter()
            .map(|&x| x ^ self.constant(u64::MAX))
            .collect();
        let (difference, ge) = self.add(a, &not_m, self.constant(u64::MAX))?;
        Ok(self.select(ge, &difference, a)?[..d.width()]
            .iter()
            .copied()
            .collect())
    }

    #[cfg(test)]
    fn field_add(&mut self, a: &[Self::Bit], b: &[Self::Bit], d: Domain) -> Result<Word<Self::Bit>, Error> {
        if d == Domain::Bit {
            return Ok(self.xor(a, b));
        }
        let (mut s, c) = self.add(a, b, self.constant(0))?;
        s.push(c);
        self.reduce_once(&s, d)
    }

    fn field_add_many(
        &mut self,
        a_words: &[Word<Self::Bit>],
        b_words: &[Word<Self::Bit>],
        d: Domain,
    ) -> Result<Vec<Word<Self::Bit>>, Error> {
        if a_words.is_empty() {
            return Ok(Vec::new());
        }
        if d == Domain::Bit {
            return Ok(a_words
                .iter()
                .zip(b_words)
                .map(|(a, b)| self.xor(a, b))
                .collect());
        }
        let n = d.width();
        let (sums, overflow) = self.add_many(a_words, b_words, 0)?;
        // `0 <= a + b < 2p = 2^(n+1) - 2c`, so `overflow` and `carry_c` are mutually exclusive.
        let (diffs, carry_c) = self.add_public_many(&sums, domain_c_const(d), 0, n)?;
        let ge: Word<Self::Bit> = overflow
            .into_iter()
            .zip(carry_c)
            .map(|(ov, cc)| ov ^ cc)
            .collect();
        self.select_many(&ge, &diffs, &sums)
    }

    #[cfg(test)]
    fn field_sub(&mut self, a: &[Self::Bit], b: &[Self::Bit], d: Domain) -> Result<Word<Self::Bit>, Error> {
        if d == Domain::Bit {
            return Ok(self.xor(a, b));
        }
        let not_b: Word<Self::Bit> = b.iter().map(|&x| x ^ self.constant(u64::MAX)).collect();
        let (difference, no_borrow) = self.add(a, &not_b, self.constant(u64::MAX))?;
        let modulus = self.number(d.modulus(), a.len());
        let (corrected, _) = self.add(&difference, &modulus, self.constant(0))?;
        self.select(no_borrow, &difference, &corrected)
    }

    /// Carry-save tree; all compressors at a level share one network round.
    #[cfg(test)]
    fn sum_rows(&mut self, mut rows: Vec<Word<Self::Bit>>, width: usize) -> Result<Word<Self::Bit>, Error> {
        for r in &mut rows {
            r.resize(width, self.constant(0));
        }
        while rows.len() > 2 {
            let count = rows.len() / 3;
            let pairs: SecretVec<_> = rows
                .chunks_exact(3)
                .flat_map(|r| (0..width).map(move |i| (r[0][i] ^ r[1][i], r[0][i] ^ r[2][i])))
                .collect();
            let products = self.and(&pairs)?;
            let mut next = Vec::with_capacity(count * 2 + 2);
            for (k, r) in rows.chunks_exact(3).enumerate() {
                next.push((0..width).map(|i| r[0][i] ^ r[1][i] ^ r[2][i]).collect());
                let mut carry: Word<Self::Bit> = vec![self.constant(0)].into();
                carry.extend((0..width - 1).map(|i| r[0][i] ^ products[k * width + i]));
                next.push(carry);
            }
            next.extend(rows[count * 3..].iter().cloned());
            rows = next;
        }
        if rows.len() == 1 {
            Ok(rows.remove(0))
        } else {
            Ok(self.add(&rows[0], &rows[1], self.constant(0))?.0)
        }
    }
    #[cfg(test)]
    fn field_mul(&mut self, a: &[Self::Bit], b: &[Self::Bit], d: Domain) -> Result<Word<Self::Bit>, Error> {
        if d == Domain::Bit {
            return self.and(&[(a[0], b[0])]);
        }
        let n = d.width();
        let pairs: SecretVec<_> = (0..n)
            .flat_map(|i| (0..n).map(move |j| (a[i], b[j])))
            .collect();
        let products = self.and(&pairs)?;
        let rows: Vec<_> = (0..n)
            .map(|i| {
                let mut row: Word<Self::Bit> = vec![self.constant(0); i].into();
                row.extend_from_slice(&products[i * n..(i + 1) * n]);
                row
            })
            .collect();
        let wide = self.sum_rows(rows, 2 * n)?;
        self.reduce_wide(wide, d)
    }
    #[cfg(test)]
    fn field_scale(&mut self, a: &[Self::Bit], value: Value, d: Domain) -> Result<Word<Self::Bit>, Error> {
        if d == Domain::Bit {
            return Ok(if value[0] == 0 {
                vec![self.constant(0)].into()
            } else {
                a.iter().copied().collect()
            });
        }
        let mut coefficient = [value[0], value[1], value[2], value[3], 0];
        let mut digits = Vec::new();
        let mut shift = 0;
        while coefficient.iter().any(|&x| x != 0) {
            if coefficient[0] & 1 != 0 {
                let negative = coefficient[0] & 3 == 3;
                digits.push((shift, negative));
                if negative {
                    let mut carry = true;
                    for limb in &mut coefficient {
                        let (v, c) = limb.overflowing_add(u64::from(carry));
                        *limb = v;
                        carry = c;
                    }
                } else {
                    coefficient[0] -= 1;
                }
            }
            for i in 0..4 {
                coefficient[i] = (coefficient[i] >> 1) | (coefficient[i + 1] << 63);
            }
            coefficient[4] >>= 1;
            shift += 1;
        }
        if digits.is_empty() {
            return Ok(vec![self.constant(0); d.width()].into());
        }
        let width = d.width() + digits.last().unwrap().0 + 1;
        let mut correction = 0;
        let mut rows: Vec<_> = digits
            .into_iter()
            .map(|(shift, negative)| {
                let mut row: Word<Self::Bit> = vec![self.constant(0); shift].into();
                row.extend_from_slice(a);
                row.resize(width, self.constant(0));
                if negative {
                    correction += 1;
                    for bit in &mut row {
                        *bit = *bit ^ self.constant(u64::MAX);
                    }
                }
                row
            })
            .collect();
        if correction != 0 {
            rows.push(self.number([correction, 0, 0, 0], width));
        }
        let wide = self.sum_rows(rows, width)?;
        self.reduce_wide(wide, d)
    }
    #[cfg(test)]
    fn reduce_wide(&mut self, mut wide: Word<Self::Bit>, d: Domain) -> Result<Word<Self::Bit>, Error> {
        let n = d.width();
        let c = match d {
            Domain::Ed => 19u64,
            Domain::Secp => 0x1_0000_03d1,
            Domain::Gold => 0xffff_ffff,
            Domain::Bit => unreachable!(),
        };
        let cbits = 64 - c.leading_zeros() as usize;
        while wide.len() > n + 1 {
            let high: Word<Self::Bit> = wide[n..].iter().copied().collect();
            let width = core::cmp::max(n, high.len() + cbits) + 1;
            let mut rows: Vec<Word<Self::Bit>> = vec![wide[..n].iter().copied().collect()];
            for shift in 0..cbits {
                if (c >> shift) & 1 != 0 {
                    let mut r: Word<Self::Bit> = vec![self.constant(0); shift].into();
                    r.extend_from_slice(&high);
                    rows.push(r);
                }
            }
            wide = self.sum_rows(rows, width)?;
        }
        self.reduce_once(&wide, d)
    }

    /// Lockstep 24-round `Keccak-f[1600]` across multiple 1600-bit states (`24` network rounds total).
    fn permutations(&mut self, states: &mut [&mut [Self::Bit]]) -> Result<(), Error> {
        if states.is_empty() {
            return Ok(());
        }
        const RHO: [usize; 24] = [
            1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14, 27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20,
            44,
        ];
        const PI: [usize; 24] = [
            10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4, 15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1,
        ];
        let ones = self.constant(u64::MAX);
        let zero = self.constant(0);
        let total_pairs = states.len() * 1600;
        let mut pairs = SecretVec::with_capacity(total_pairs);
        pairs.resize(total_pairs, (zero, zero));
        let mut prods = SecretVec::with_capacity(total_pairs);
        let mut c_buf = Secret([zero; 320]);
        let mut t_buf = Secret([zero; 64]);
        let mut next_buf = Secret([zero; 64]);

        for rc in KECCAK_RC {
            for (state, state_pairs) in states.iter_mut().zip(pairs.chunks_exact_mut(1600)) {
                for (i, c_slot) in c_buf.iter_mut().enumerate() {
                    let col = i / 64;
                    let z = i % 64;
                    *c_slot = state[col * 64 + z]
                        ^ state[(col + 5) * 64 + z]
                        ^ state[(col + 10) * 64 + z]
                        ^ state[(col + 15) * 64 + z]
                        ^ state[(col + 20) * 64 + z];
                }
                for x in 0..5 {
                    for z in 0..64 {
                        let d_xz = c_buf[((x + 4) % 5) * 64 + z]
                            ^ c_buf[((x + 1) % 5) * 64 + (z + 63) % 64];
                        for y in 0..5 {
                            state[(x + 5 * y) * 64 + z] = state[(x + 5 * y) * 64 + z] ^ d_xz;
                        }
                    }
                }
                t_buf.copy_from_slice(&state[64..128]);
                for (j, r) in PI.into_iter().zip(RHO) {
                    next_buf.copy_from_slice(&state[j * 64..j * 64 + 64]);
                    for z in 0..64 {
                        state[j * 64 + z] = t_buf[(z + 64 - r) % 64];
                    }
                    t_buf.copy_from_slice(&next_buf[..]);
                }
                for (i, slot) in state_pairs.iter_mut().enumerate() {
                    let row = (i / 320) * 320;
                    let x = (i / 64) % 5;
                    let z = i % 64;
                    *slot = (
                        state[row + ((x + 1) % 5) * 64 + z] ^ ones,
                        state[row + ((x + 2) % 5) * 64 + z],
                    );
                }
            }
            self.and_into(&pairs, &mut prods)?;
            for (state, chunk) in states.iter_mut().zip(prods.chunks_exact(1600)) {
                for (s, &v) in state.iter_mut().zip(chunk) {
                    *s = *s ^ v;
                }
                for (i, s) in state[..64].iter_mut().enumerate() {
                    if (rc >> i) & 1 != 0 {
                        *s = *s ^ ones;
                    }
                }
            }
        }
        Ok(())
    }

    fn permutation(&mut self, state: &mut Word<Self::Bit>) -> Result<(), Error> {
        self.permutations(&mut [state.as_mut_slice()])
    }

    fn fmul(&mut self, a: &FieldWord, b: &FieldWord, d: Domain) -> Result<FieldWord, Error> {
        Ok(self.fmul_many(&[(a, b)], d)?.pop().unwrap())
    }


    #[cfg(test)]
    fn bits_to_field(&mut self, v: &[Self::Bit], d: Domain) -> Result<FieldWord, Error> {
        Ok(self
            .bits_to_field_many(&[v.iter().copied().collect()], d)?
            .pop()
            .unwrap())
    }

    #[cfg(test)]
    fn field_to_bits(&mut self, v: &FieldWord, d: Domain) -> Result<Word<Self::Bit>, Error> {
        Ok(self.field_to_bits_many(&[v], d)?.pop().unwrap())
    }

    fn finverse(&mut self, a: &FieldWord, d: Domain) -> Result<FieldWord, Error> {
        // Opening authenticates all pending products first. Only the uniformly
        // masked product is public; the mask and inverse remain shared.
        // Inversion gates require a nonzero operand. Bound retries so malformed
        // zero operands abort instead of hanging a ceremony indefinitely.
        for _ in 0..3 {
            let mask = self.frandom(d)?;
            let product = self.fmul(a, &mask, d)?;
            let opened = self.fopen_many(&[product], d)?;
            if opened[0].contains(&[0; 4]) {
                continue;
            }
            let inverses: Vec<Value> = opened[0].iter().map(|u| d.inverse(*u)).collect();
            return Ok(self.fscale_lanes(&mask, &inverses, d));
        }
        self.poison();
        Err(Error::InvalidProof)
    }
}
impl<E: Core> Gadgets for E {}

fn domain_c_const(d: Domain) -> Value {
    match d {
        Domain::Ed => [19, 0, 0, 0],
        Domain::Secp => [0x1_0000_03d1, 0, 0, 0],
        Domain::Gold => [0xffff_ffff, 0, 0, 0],
        Domain::Bit => [0, 0, 0, 0],
    }
}

pub(crate) struct Sponge<B: ShareBit = Bit> {
    pub(crate) state: Word<B>,
    pub(crate) pos: usize,
}
impl<B: ShareBit> Sponge<B> {
    pub fn new<E: Core<Bit = B>>(e: &E) -> Self {
        Self {
            state: vec![e.constant(0); 1600].into(),
            pos: 0,
        }
    }
    pub fn absorb<E: Core<Bit = B>>(&mut self, e: &mut E, input: &[B]) -> Result<(), Error> {
        for &b in input {
            self.state[self.pos] = self.state[self.pos] ^ b;
            self.pos += 1;
            if self.pos == 1088 {
                e.permutation(&mut self.state)?;
                self.pos = 0;
            }
        }
        Ok(())
    }
    pub fn public<E: Core<Bit = B>>(&mut self, e: &mut E, bytes: &[u8]) -> Result<(), Error> {
        let bits = public_bytes(e, bytes);
        self.absorb(e, &bits)
    }
    pub fn pad_only<E: Core<Bit = B>>(&mut self, e: &E, suffix: u8) {
        for i in 0..8 {
            if (suffix >> i) & 1 != 0 {
                self.state[self.pos + i] = self.state[self.pos + i] ^ e.constant(u64::MAX);
            }
        }
        self.state[1087] = self.state[1087] ^ e.constant(u64::MAX);
        self.pos = 0;
    }
    #[cfg(test)]
    pub fn finalize<E: Core<Bit = B>>(&mut self, e: &mut E, suffix: u8) -> Result<(), Error> {
        self.pad_only(e, suffix);
        e.permutation(&mut self.state)?;
        Ok(())
    }
    #[cfg(test)]
    pub fn squeeze<E: Core<Bit = B>>(
        &mut self,
        e: &mut E,
        count: usize,
    ) -> Result<Word<B>, Error> {
        let mut out = SecretVec::with_capacity(count);
        for _ in 0..count {
            if self.pos == 1088 {
                e.permutation(&mut self.state)?;
                self.pos = 0;
            }
            out.push(self.state[self.pos]);
            self.pos += 1;
        }
        Ok(out)
    }
    /// Initialize a shared `cSHAKE256` sponge from the public permuted customization
    /// block (`0` MPC rounds for it). The customization must fit one rate block.
    pub fn cshake_public<E: Core<Bit = B>>(e: &E, customization: &[u8]) -> Self {
        let mut s = Self::new(e);
        let st = cshake256_static_midstate(customization);
        for (lane_idx, &w) in st.iter().enumerate() {
            for bit in 0..64 {
                s.state[lane_idx * 64 + bit] =
                    e.constant(if (w >> bit) & 1 != 0 { u64::MAX } else { 0 });
            }
        }
        s
    }
    #[cfg(test)]
    pub fn cshake<E: Core<Bit = B>>(e: &mut E, customization: &[u8]) -> Result<Self, Error> {
        Ok(Self::cshake_public(e, customization))
    }
}

/// Squeeze `counts[i]` bits from each `sponges[i]` in lockstep, sharing one
/// `Engine::permutations` batch call per 1088-bit block across all sponges that need more output.
pub(crate) fn squeeze_sponges_lockstep<E: Core>(
    e: &mut E,
    sponges: &mut [Sponge<E::Bit>],
    counts: &[usize],
) -> Result<Vec<Word<E::Bit>>, Error> {
    let mut outs: Vec<Word<E::Bit>> =
        counts.iter().map(|&c| SecretVec::with_capacity(c)).collect();
    loop {
        let mut need_perm = Vec::new();
        for (idx, (sp, &target)) in sponges.iter_mut().zip(counts).enumerate() {
            let rem = target - outs[idx].len();
            if rem == 0 {
                continue;
            }
            if sp.pos < 1088 {
                let take = (1088 - sp.pos).min(rem);
                outs[idx].extend_from_slice(&sp.state[sp.pos..sp.pos + take]);
                sp.pos += take;
            }
            if outs[idx].len() < target && sp.pos == 1088 {
                need_perm.push(idx);
            }
        }
        if need_perm.is_empty() {
            break;
        }
        let mut refs: Vec<&mut [E::Bit]> = Vec::with_capacity(need_perm.len());
        // Split borrows safely across `sponges` in index order.
        let mut cursor = 0usize;
        let mut rest: &mut [Sponge<E::Bit>] = &mut *sponges;
        for &idx in &need_perm {
            let (_, after) = rest.split_at_mut(idx - cursor);
            let (first, tail) = after.split_first_mut().unwrap();
            first.pos = 0;
            refs.push(first.state.as_mut_slice());
            rest = tail;
            cursor = idx + 1;
        }
        e.permutations(&mut refs)?;
    }
    Ok(outs)
}

pub(crate) fn public_bytes<E: Core>(e: &E, bytes: &[u8]) -> Word<E::Bit> {
    bytes
        .iter()
        .flat_map(|b| (0..8).map(move |i| e.constant(if (b >> i) & 1 != 0 { u64::MAX } else { 0 })))
        .collect()
}
pub(crate) fn lane_bytes(words: &[u64], lane: usize) -> Vec<u8> {
    words
        .chunks_exact(8)
        .map(|chunk| {
            chunk
                .iter()
                .enumerate()
                .fold(0, |v, (i, b)| v | (((b >> lane) & 1) as u8) << i)
        })
        .collect()
}
pub(crate) fn encode<B: ShareBit>(out: &mut Word<B>, value: &[B]) {
    out.extend_from_slice(value);
    out.resize(out.len().div_ceil(8) * 8, B::default());
}

impl<T: Transport> Engine<T> {
    pub fn fconstant(&self, value: Value) -> FieldWord {
        vec![
            [
                if self.party == 0 { value } else { [0; 4] },
                if (self.party + 1) % 3 == 0 {
                    value
                } else {
                    [0; 4]
                }
            ];
            64
        ]
        .into()
    }
    fn field_pad(s: &mut WordSponge136, d: Domain) -> Value {
        if d == Domain::Gold {
            loop {
                let w = Secret(s.squeeze_u64());
                if *w < GOLDILOCKS_P {
                    return [*w, 0, 0, 0];
                }
            }
        }
        loop {
            let mut words = Secret([0u64; 4]);
            s.squeeze_u64s(&mut words[..]);
            if d == Domain::Ed {
                words[3] &= 0x7fff_ffff_ffff_ffff;
            }
            if d.canonical(*words) {
                return *words;
            }
        }
    }

    fn frandom(&mut self, d: Domain) -> FieldWord {
        (0..64)
            .map(|_| {
                [
                    Self::field_pad(&mut self.pads[0], d),
                    Self::field_pad(&mut self.pads[1], d),
                ]
            })
            .collect()
    }

    pub fn fmul_many(
        &mut self,
        pairs: &[(&FieldWord, &FieldWord)],
        d: Domain,
    ) -> Result<Vec<FieldWord>, Error> {
        if self.poisoned {
            return Err(Error::MultiplicationCheck);
        }
        if pairs.is_empty() {
            return Ok(Vec::new());
        }
        let k = pairs.len();
        let mut own_flat = Vec::with_capacity(k * 256);
        for (pair_idx, &(a, b)) in pairs.iter().enumerate() {
            #[cfg(test)]
            let inject_lane = match self.fault {
                Some(FaultInjection::FieldMul {
                    domain,
                    ref mut call_countdown,
                    lane,
                }) if domain == d && pair_idx == 0 => {
                    if *call_countdown == 0 {
                        let target_lane = lane & 63;
                        self.fault = None;
                        Some(target_lane)
                    } else {
                        *call_countdown -= 1;
                        None
                    }
                }
                _ => None,
            };
            #[cfg(not(test))]
            let _ = pair_idx;
            for (lane_idx, (al, bl)) in a.iter().zip(b).enumerate() {
                // Only one lane's masks are live: no per-word mask allocation.
                let r = Secret([
                    Self::field_pad(&mut self.pads[0], d),
                    Self::field_pad(&mut self.pads[1], d),
                ]);
                #[cfg(not(test))]
                let _ = lane_idx;
                let prod = Secret(d.add(
                    d.add(d.mul(al[0], d.add(bl[0], bl[1])), d.mul(al[1], bl[0])),
                    d.sub(r[0], r[1]),
                ));
                #[cfg(test)]
                let prod = Secret(if inject_lane == Some(lane_idx) {
                    d.add(*prod, [1, 0, 0, 0])
                } else {
                    *prod
                });
                own_flat.extend_from_slice(&prod[..]);
            }
        }
        let (own_raw, next_raw) = self.raw_share_owned(own_flat)?;
        let mut results = Vec::with_capacity(k);
        for (word_own, word_next) in own_raw.chunks_exact(256).zip(next_raw.chunks_exact(256)) {
            let mut fw = FieldWord::with_capacity(64);
            for (av, b_slice) in word_own.chunks_exact(4).zip(word_next.chunks_exact(4)) {
                let bv: Value = [b_slice[0], b_slice[1], b_slice[2], b_slice[3]];
                if !d.canonical(bv) {
                    self.poisoned = true;
                    return Err(Error::MultiplicationCheck);
                }
                fw.push([[av[0], av[1], av[2], av[3]], bv]);
            }
            results.push(fw);
        }
        let queue = match d {
            Domain::Secp => &mut self.pending_secp,
            Domain::Ed => &mut self.pending_ed,
            Domain::Gold => &mut self.pending_gold,
            Domain::Bit => return Err(Error::InvalidConfiguration),
        };
        for (&(a, b), z) in pairs.iter().zip(&results) {
            queue.push((a.clone(), b.clone(), z.clone()));
        }
        if queue.len() >= MAX_PENDING_FIELD_WORDS {
            self.flush_pending_domain(d)?;
        }
        Ok(results)
    }

    fn fopen_many(&mut self, words: &[FieldWord], d: Domain) -> Result<Vec<Vec<Value>>, Error> {
        if words.is_empty() {
            return Ok(Vec::new());
        }
        self.verify_all_pending()?;
        let k = words.len();
        let mut payload = Vec::with_capacity(k * 512);
        for w in words {
            for pair in w {
                payload.extend_from_slice(&pair[0]);
                payload.extend_from_slice(&pair[1]);
            }
        }
        let received = self.raw_exchange([payload.clone(), payload])?;
        if received.iter().any(|v| v.len() != k * 512) {
            self.poisoned = true;
            return Err(Error::InvalidConfiguration);
        }
        let mut all_out = Vec::with_capacity(k);
        for (w_idx, w) in words.iter().enumerate() {
            let base_w = w_idx * 512;
            let mut out = Vec::with_capacity(64);
            for (lane, a) in w.iter().enumerate() {
                let off = base_w + 8 * lane;
                let prev: [Value; 2] = core::array::from_fn(|j| {
                    let s = &received[0][off + 4 * j..off + 4 * j + 4];
                    [s[0], s[1], s[2], s[3]]
                });
                let next: [Value; 2] = core::array::from_fn(|j| {
                    let s = &received[1][off + 4 * j..off + 4 * j + 4];
                    [s[0], s[1], s[2], s[3]]
                });
                if prev[1] != a[0] {
                    self.poisoned = true;
                    return Err(Error::Disagreement((self.party + 2) % 3));
                }
                if next[0] != a[1] || prev[0] != next[1] || !d.canonical(prev[0]) {
                    self.poisoned = true;
                    return Err(Error::Disagreement((self.party + 1) % 3));
                }
                out.push(d.add(d.add(a[0], a[1]), prev[0]));
            }
            all_out.push(out);
        }
        Ok(all_out)
    }

    fn component_owner_bits(&self, words: &[FieldWord], d: Domain, owner: usize) -> Vec<Word> {
        words
            .iter()
            .map(|a| {
                (0..d.width())
                    .map(|bit| {
                        Bit(core::array::from_fn(|j| {
                            if (self.party + j) % 3 != owner {
                                0
                            } else {
                                a.iter().enumerate().fold(0, |mask, (lane, value)| {
                                    mask | (((value[j][bit / 64] >> (bit % 64)) & 1) << lane)
                                })
                            }
                        }))
                    })
                    .collect()
            })
            .collect()
    }

    /// Binary encoding of additive sharings without reconstructing their sums.
    fn component_bits_many(&mut self, words: &[FieldWord], d: Domain) -> Result<Vec<Word>, Error> {
        let p0 = self.component_owner_bits(words, d, 0);
        let p1 = self.component_owner_bits(words, d, 1);
        let p2 = self.component_owner_bits(words, d, 2);
        let (sum01, carry1) = self.add_many(&p0, &p1, 0)?;
        let (ring_sum, carry2) = self.add_many(&sum01, &p2, 0)?;
        // S = ring_sum + (carry1+carry2)*2^n. Encode k*c with k in
        // {0,1,2}, using mutually exclusive low/high bits of k, then reduce once.
        // ring_sum + 2*c < 2*p for all supported fields, including Goldilocks.
        let pairs: SecretVec<_> = carry1.iter().copied().zip(carry2.iter().copied()).collect();
        let high = self.and(&pairs)?;
        let c = domain_c_const(d)[0];
        let correction: Vec<Word> = carry1
            .iter()
            .zip(&carry2)
            .zip(&high)
            .map(|((&a, &b), &hi)| {
                (0..d.width())
                    .map(|bit| {
                        let mut out = self.constant(0);
                        if bit < 64 && (c >> bit) & 1 != 0 {
                            out = out ^ a ^ b;
                        }
                        if bit < 64 && ((2 * c) >> bit) & 1 != 0 {
                            out = out ^ hi;
                        }
                        out
                    })
                    .collect()
            })
            .collect();
        self.field_add_many(&ring_sum, &correction, d)
    }

    /// Convert using a uniform mask in Z/(2^n), with secret carry correction.
    /// If S = R0+R1+R2 = r+k*2^n and delta = v-r mod 2^n, then
    /// v = S+delta-(k+borrow)*2^n. The three carry bits remain shared.
    /// All pending multiplications are verified before the uniform delta opens.
    pub fn bits_to_field_many(
        &mut self,
        words: &[Word],
        d: Domain,
    ) -> Result<Vec<FieldWord>, Error> {
        let mut out = Vec::with_capacity(words.len());
        for chunk in words.chunks(CONVERT_CHUNK_WORDS) {
            let masks: Vec<FieldWord> = (0..chunk.len())
                .map(|_| {
                    (0..64)
                        .map(|_| {
                            core::array::from_fn(|side| {
                                let mut raw = Secret([0; 4]);
                                self.pads[side].squeeze_u64s(&mut raw[..d.width().div_ceil(64)]);
                                if d == Domain::Ed {
                                    raw[3] &= 0x7fff_ffff_ffff_ffff;
                                }
                                *raw
                            })
                        })
                        .collect()
                })
                .collect();
            out.extend(self.bits_to_field_masked(chunk, masks, d)?);
        }
        Ok(out)
    }

    fn bits_to_field_masked(
        &mut self,
        words: &[Word],
        mut masks: Vec<FieldWord>,
        d: Domain,
    ) -> Result<Vec<FieldWord>, Error> {
        let width = d.width();
        let count = words.len();
        let p0 = self.component_owner_bits(&masks, d, 0);
        let p1 = self.component_owner_bits(&masks, d, 1);
        let p2 = self.component_owner_bits(&masks, d, 2);
        let (sum01, mut carries) = self.add_many(&p0, &p1, 0)?;
        let (ring_mask, carry2) = self.add_many(&sum01, &p2, 0)?;
        carries.extend_from_slice(&carry2);
        let ones = self.constant(u64::MAX);
        let not_mask: Vec<Word> = ring_mask
            .iter()
            .map(|w| w.iter().map(|&b| b ^ ones).collect())
            .collect();
        let (deltas, no_borrow) = self.add_many(words, &not_mask, u64::MAX)?;
        carries.extend(no_borrow.iter().map(|&b| b ^ ones));
        // Each raw component is below 2^n < 2p. This single conditional
        // subtraction canonicalizes it, including the Goldilocks boundary.
        for mask in &mut masks {
            for pair in mask.iter_mut() {
                for value in pair {
                    *value = crate::scalar::sub(*value, d.modulus(), d.modulus());
                }
            }
        }
        let lifted = self.lift_bits_many(&carries, d)?;
        let mut corrected = Vec::with_capacity(count);
        for (i, mask) in masks.iter().enumerate() {
            let k = self.fadd(&lifted[i], &lifted[count + i], d);
            let k_borrow = self.fadd(&k, &lifted[2 * count + i], d);
            let correction = self.fscale(&k_borrow, domain_c_const(d), d);
            corrected.push(self.fsub(mask, &correction, d));
        }
        let mut flat = Word::with_capacity(count * width);
        for delta in &deltas {
            flat.extend_from_slice(delta);
        }
        let opened = self.open(&flat)?;
        for (mask, bits) in corrected.iter_mut().zip(opened.chunks_exact(width)) {
            for (lane, pair) in mask.iter_mut().enumerate() {
                let mut value = [0; 4];
                for (bit, &word) in bits.iter().enumerate() {
                    value[bit / 64] |= ((word >> lane) & 1) << (bit % 64);
                }
                let value = crate::scalar::sub(value, d.modulus(), d.modulus());
                for (side, part) in pair.iter_mut().enumerate() {
                    if (self.party + side) % 3 == 0 {
                        *part = d.add(*part, value);
                    }
                }
            }
        }
        Ok(corrected)
    }

    /// Convert additive to binary sharing by opening only fresh masked differences
    /// after actively verifying all pending Boolean and prime-field multiplications.
    pub fn field_to_bits_many(
        &mut self,
        words: &[&FieldWord],
        d: Domain,
    ) -> Result<Vec<Word>, Error> {
        if words.is_empty() {
            return Ok(Vec::new());
        }
        let mut r_list: Vec<FieldWord> = (0..words.len()).map(|_| self.frandom(d)).collect();
        let deltas: Vec<FieldWord> = words
            .iter()
            .zip(&r_list)
            .map(|(v, r)| self.fsub(v, r, d))
            .collect();
        let opened_list = self.fopen_many(&deltas, d)?;
        drop(deltas);
        for (r_fw, opened) in r_list.iter_mut().zip(&opened_list) {
            for (pair, &val) in r_fw.iter_mut().zip(opened) {
                for (j, part) in pair.iter_mut().enumerate() {
                    if (self.party + j) % 3 == 0 {
                        *part = d.add(*part, val);
                    }
                }
            }
        }
        let mut all_out = Vec::with_capacity(words.len());
        for r_chunk in r_list.chunks(CONVERT_CHUNK_WORDS) {
            all_out.extend(self.component_bits_many(r_chunk, d)?);
        }
        Ok(all_out)
    }

    pub fn lift_bits_many(&mut self, bits: &[Bit], d: Domain) -> Result<Vec<FieldWord>, Error> {
        if bits.is_empty() {
            return Ok(Vec::new());
        }
        let make_owner = |owner: usize| -> Vec<FieldWord> {
            bits.iter()
                .map(|&bit| {
                    (0..64)
                        .map(|lane| {
                            core::array::from_fn(|j| {
                                if (self.party + j) % 3 == owner {
                                    [(bit.0[j] >> lane) & 1, 0, 0, 0]
                                } else {
                                    [0; 4]
                                }
                            })
                        })
                        .collect()
                })
                .collect()
        };
        let p0 = make_owner(0);
        let p1 = make_owner(1);
        let p2 = make_owner(2);
        let pairs01: Vec<_> = p0.iter().zip(&p1).collect();
        let ab01 = self.fmul_many(&pairs01, d)?;
        let firsts: Vec<FieldWord> = p0
            .iter()
            .zip(&p1)
            .zip(&ab01)
            .map(|((a, b), ab)| {
                let sum = self.fadd(a, b, d);
                self.fsub(&sum, &self.fscale(ab, [2, 0, 0, 0], d), d)
            })
            .collect();
        let pairs12: Vec<_> = firsts.iter().zip(&p2).collect();
        let ab12 = self.fmul_many(&pairs12, d)?;
        Ok(firsts
            .iter()
            .zip(&p2)
            .zip(&ab12)
            .map(|((f, c), ab)| {
                let sum = self.fadd(f, c, d);
                self.fsub(&sum, &self.fscale(ab, [2, 0, 0, 0], d), d)
            })
            .collect())
    }

}

#[cfg(test)]
pub(crate) mod tests {

    extern crate std;
    use super::*;
    use qsag_asm::gf2_128_mul_portable;
    use std::sync::{
        Arc,
        atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering},
        mpsc::{self, Receiver, Sender},
    };

    pub struct Network {
        trace: Option<Arc<Trace>>,
        stream: usize,
        children: Vec<Network>,
        sends: [Sender<Envelope>; 2],
        receives: [Receiver<Envelope>; 2],
    }

    struct Trace {
        party_id: AtomicUsize,
        msg_count: AtomicU64,
        word_count: AtomicU64,
        digest: AtomicU64,
        candidates: std::sync::Mutex<Vec<[u8; 32]>>,
        private_view: std::sync::Mutex<Vec<u8>>,
    }
    impl Default for Trace {
        fn default() -> Self {
            Self {
                party_id: AtomicUsize::new(usize::MAX),
                msg_count: AtomicU64::new(0),
                word_count: AtomicU64::new(0),
                digest: AtomicU64::new(0),
                candidates: std::sync::Mutex::new(Vec::new()),
                private_view: std::sync::Mutex::new(Vec::new()),
            }
        }
    }
    pub(crate) struct AuditHandle(Arc<Trace>);
    impl AuditHandle {
        pub fn candidates(&self) -> Vec<[u8; 32]> {
            self.0.candidates.lock().unwrap().clone()
        }
    }
    impl Trace {
        fn new(_party: usize) -> Self {
            Self::default()
        }
        fn record(&self, stream: usize, direction: u8, m: &Envelope) {
            let expected_party = self.party_id.load(Ordering::Acquire);
            assert_ne!(expected_party, usize::MAX);
            assert_eq!(
                expected_party,
                if direction == 0 {
                    m.sender
                } else {
                    m.recipient
                }
            );
            let mut local_digest =
                (stream as u64).rotate_left(7) ^ u64::from(direction) ^ m.sequence;
            for &word in &m.payload {
                local_digest ^= word;
            }
            for &byte in &m.tag {
                local_digest = local_digest.rotate_left(1) ^ u64::from(byte);
            }
            self.msg_count.fetch_add(1, Ordering::Relaxed);
            self.word_count
                .fetch_add(m.payload.len() as u64, Ordering::Relaxed);
            self.digest.fetch_xor(local_digest, Ordering::Relaxed);
        }
        fn stats(&self) -> (u64, u64) {
            (
                self.msg_count.load(Ordering::Acquire),
                self.word_count.load(Ordering::Acquire),
            )
        }
    }
    impl Network {
        fn record(&self, direction: u8, m: &Envelope) {
            if let Some(trace) = &self.trace {
                trace.record(self.stream, direction, m);
            }
        }
    }
    pub(crate) fn parallel_batches() -> usize {
        if std::thread::available_parallelism().is_ok_and(|n| n.get() >= 24) {
            4
        } else if std::thread::available_parallelism().is_ok_and(|n| n.get() >= 21) {
            7
        } else {
            4
        }
    }

    impl Transport for Network {
        // Large test hosts overlap ceremonies, each with three custodians.
        fn max_parallel_batches(&self) -> usize {
            parallel_batches()
        }

        fn audit_transcript(&self) -> Option<(u64, u64)> {
            self.trace.as_ref().map(|t| t.stats())
        }
        fn audit_candidates(&self, candidates: Vec<[u8; 32]>) {
            self.trace
                .as_ref()
                .unwrap()
                .candidates
                .lock()
                .unwrap()
                .extend(candidates);
        }
        fn audit_private_state(
            &self,
            party: usize,
            session: &[u8; 32],
            witness: &[u8; 32],
            entropy: &[u8; 32],
            keys: &[[u8; 32]; 2],
            statement: &crate::zk_engine::MigrationStatement,
        ) {
            if let Some(trace) = &self.trace {
                let mut private = trace.private_view.lock().unwrap();
                assert!(private.is_empty());
                private.push(party as u8);
                for bytes in [session, witness, entropy, &keys[0], &keys[1]] {
                    private.extend_from_slice(bytes);
                }
                private.extend_from_slice(&statement.to_transcript_bytes());
                trace.party_id.store(party, Ordering::Release);
            }
        }
        fn fork(&mut self, _batch: usize) -> Option<Self> {
            if self.children.is_empty() {
                None
            } else {
                Some(self.children.remove(0))
            }
        }
        fn exchange(&mut self, out: [Envelope; 2]) -> Result<[Envelope; 2], Error> {
            for (s, m) in self.sends.iter().zip(out) {
                self.record(0, &m);
                s.send(m).map_err(|_| Error::Transport)?;
            }
            let messages = [
                self.receives[0].recv().map_err(|_| Error::Transport)?,
                self.receives[1].recv().map_err(|_| Error::Transport)?,
            ];
            for m in &messages {
                self.record(1, m);
            }
            Ok(messages)
        }
    }
    pub fn networks() -> [Network; 3] {
        let mut roots = raw_networks();
        for _ in 0..crate::zk_engine::MIT_REPETITIONS.div_ceil(64) {
            for (root, child) in roots.iter_mut().zip(raw_networks()) {
                root.children.push(child);
            }
        }
        roots
    }
    fn raw_networks() -> [Network; 3] {
        let mut sends: Vec<Vec<Option<Sender<Envelope>>>> =
            (0..3).map(|_| (0..2).map(|_| None).collect()).collect();
        let mut receives: Vec<Vec<Option<Receiver<Envelope>>>> =
            (0..3).map(|_| (0..2).map(|_| None).collect()).collect();
        for (p, row) in sends.iter_mut().enumerate() {
            for (i, entry) in row.iter_mut().enumerate() {
                let (s, r) = mpsc::channel();
                *entry = Some(s);
                let peer = (p + if i == 0 { 2 } else { 1 }) % 3;
                receives[peer][1 - i] = Some(r);
            }
        }
        core::array::from_fn(|p| Network {
            trace: None,
            stream: 0,
            children: Vec::new(),
            sends: core::array::from_fn(|i| sends[p][i].take().unwrap()),
            receives: core::array::from_fn(|i| receives[p][i].take().unwrap()),
        })
    }
    pub fn keys(p: usize) -> [[u8; 32]; 2] {
        [[((p + 2) % 3 + 1) as u8; 32], [(p + 1) as u8; 32]]
    }
    pub fn run<F: Fn(usize, Network) + Sync>(f: F) {
        std::thread::scope(|scope| {
            for (p, n) in networks().into_iter().enumerate() {
                let f = &f;
                scope.spawn(move || f(p, n));
            }
        });
    }
    #[test]
    fn masked_inverse_matches_plaintext_and_rejects_zero() {
        run(|party, network| {
            let mut e = Engine::new(party, [0x91; 32], keys(party), network).unwrap();
            for d in [Domain::Gold, Domain::Secp, Domain::Ed] {
                let a = e.frandom(d);
                let clear = e.fopen_many(core::slice::from_ref(&a), d).unwrap();
                let inverse = e.finverse(&a, d).unwrap();
                let actual = e.fopen_many(&[inverse], d).unwrap();
                for (a, b) in clear[0].iter().zip(&actual[0]) {
                    assert_eq!(d.mul(*a, *b), [1, 0, 0, 0]);
                }
            }
            let zero = e.fconstant([0; 4]);
            assert!(matches!(
                e.finverse(&zero, Domain::Secp),
                Err(Error::InvalidProof)
            ));
        });
    }

    pub fn audited_networks() -> [(Network, AuditHandle); 3] {
        let mut networks = networks().map(Some);
        core::array::from_fn(|p| {
            let mut network = networks[p].take().unwrap();
            let trace = Arc::new(Trace::new(p));
            for (batch, child) in network.children.iter_mut().enumerate() {
                child.trace = Some(trace.clone());
                child.stream = batch + 1;
            }
            network.trace = Some(trace.clone());
            (network, AuditHandle(trace))
        })
    }

    pub(crate) fn valid_mac_tag(key: &[u8; 32], session: &[u8; 32], m: &Envelope) -> [u8; 32] {
        let bytes: Vec<u8> = m.payload.iter().flat_map(|w| w.to_le_bytes()).collect();
        cshake256_framed_32(
            b"QSAG.OUTER.MESSAGE.V1",
            &[
                key,
                session,
                &[m.sender as u8, m.recipient as u8],
                &m.sequence.to_le_bytes(),
                &bytes,
            ],
        )
    }

    #[test]
    fn cancelled_batch_sends_no_messages() {
        struct NoExchange;
        impl Transport for NoExchange {
            fn exchange(&mut self, _: [Envelope; 2]) -> Result<[Envelope; 2], Error> {
                panic!("cancelled batch sent a message");
            }
        }
        let mut engine = Engine::new(0, [0x61; 32], keys(0), NoExchange).unwrap();
        engine.batch_cancelled = Some(Arc::new(AtomicBool::new(true)));
        assert!(matches!(engine.share(&[0x1234]), Err(Error::Transport)));
        let wire = engine.constant(1);
        assert_eq!(engine.open(&[wire]), Err(Error::Transport));
        assert_eq!(engine.sequence, 0);
    }

    #[test]
    fn bit_check_vectors_never_reallocate_while_folding() {
        let mut scratch = BitCheckScratch::new_boxed();
        // Growing, shrinking and odd group counts, in one scratch as across flushes.
        let mut peak_ptrs: Option<[*const u128; 8]> = None;
        for groups in [
            1usize,
            3,
            2,
            7,
            33,
            5,
            MAX_BIT_GROUPS,
            33,
            7,
            MAX_BIT_GROUPS,
        ] {
            let needed = groups * BIT_LANES;
            scratch.prepare_tables(needed);
            let sc = &mut *scratch;
            let cur_ptrs: [*const u128; 8] = core::array::from_fn(|idx| {
                if idx < 4 {
                    sc.x_tab[idx / 2][idx % 2].as_ptr()
                } else {
                    let j = idx - 4;
                    sc.y_tab[j / 2][j % 2].as_ptr()
                }
            });
            for table in sc.x_tab.iter_mut().chain(&mut sc.y_tab).flatten() {
                assert_eq!(table.len(), needed);
                let storage = table.as_ptr();
                assert_eq!(storage, table.as_ptr());
            }
            if let Some(expected) = peak_ptrs {
                assert_eq!(cur_ptrs, expected);
            } else if groups == MAX_BIT_GROUPS {
                peak_ptrs = Some(cur_ptrs);
            }
        }
    }

    #[test]
    fn wiped_growth_keeps_pending_words_and_clears_scratch() {
        let mut pending = vec![1u64, 2, 3];
        reserve_wiped(&mut pending, 1_000);
        assert_eq!(pending, [1, 2, 3]);
        assert!(pending.capacity() >= 1_003);

        let mut scratch = vec![7u64; 8];
        resize_wiped(&mut scratch, 2);
        assert_eq!(scratch, [7, 7]);
        resize_wiped(&mut scratch, 4);
        assert_eq!(scratch, [7, 7, 0, 0]);
        let len = scratch.capacity() + 1;
        resize_wiped(&mut scratch, len);
        assert_eq!(scratch.len(), len);
        assert!(scratch.iter().all(|&w| w == 0));
    }

    #[test]
    fn zero_alloc_mac_tag_and_word_sponge_match_reference_across_all_alignments() {
        let session = [0x42u8; 32];
        run(|p, n| {
            let e = Engine::new(p, session, keys(p), n).unwrap();
            if p == 0 {
                for len in 0..=300usize {
                    let payload: Vec<u64> = (0..len)
                        .map(|i| 0x9e37_79b9_7f4a_7c15u64.wrapping_mul(i as u64 + 1))
                        .collect();
                    let seq = 0xfedc_ba98_7654_3210u64.wrapping_add(len as u64);
                    let fast = e.tag(0, 0, 2, seq, &payload);
                    let dummy = Envelope {
                        sender: 0,
                        recipient: 2,
                        sequence: seq,
                        payload,
                        tag: [0; 32],
                    };
                    let reference = valid_mac_tag(&keys(0)[0], &session, &dummy);
                    assert_eq!(fast, reference, "mismatch at payload len {len}");
                }
            }
        });
    }

    #[test]
    fn bitsliced_wiedemann_tower_and_gold_ext3_match_field_axioms() {
        let backend = detect_backend();
        let mut xof = WordSponge136::from_shake_seed(&[0x77; 32]);
        let mut a = [0u64; 128];
        let mut b = [0u64; 128];
        xof.squeeze_u64s(&mut a);
        xof.squeeze_u64s(&mut b);

        // 1. Verify `poly128_mul_x`, `poly128_mul_x16`, `poly128_mul_x_lane`, and `gf128_inv_public`.
        for _ in 0..64 {
            let elem_u = xof.squeeze_nonzero_u128();
            let elem = u128_to_gf128(elem_u);
            assert_eq!(
                u128_to_gf128(poly128_mul_x(elem_u)),
                gf2_128_mul_portable(elem, [2, 0])
            );
            assert_eq!(
                u128_to_gf128(poly128_mul_x16(elem_u)),
                gf2_128_mul_portable(elem, [1u64 << 16, 0])
            );
            let inv = gf128_inv_public(elem, backend);
            assert_eq!(gf2_128_mul_portable(elem, inv), [1, 0]);
            for lane in 0..BIT_LANES {
                assert_eq!(
                    u128_to_gf128(poly128_mul_x_lane(elem_u, lane)),
                    gf2_128_mul_portable(elem, [1u64 << lane, 0]),
                    "poly128_mul_x_lane mismatch at lane {lane}"
                );
            }
        }

        // 2. Verify `ternary_expand_group`, `gf2_64x128_clmul_acc_with_backend`, and `reduce_wide_gf128`.
        let mut scratch = BitCheckScratch::new_boxed();
        let words64: [u64; BIT_GROUP_WORDS] = core::array::from_fn(|u| a[u]);
        ternary_expand_group(&words64, &mut scratch.ea[0]);
        for e in 0..BIT_TERNARY {
            let mut rem = e;
            let mut expected = 0u64;
            let mut valid_digits = [0usize; BIT_TENSOR_BITS];
            for d in &mut valid_digits {
                *d = rem % 3;
                rem /= 3;
            }
            for (u, &w) in words64.iter().enumerate() {
                let mut include = true;
                for (bit, &d) in valid_digits.iter().enumerate() {
                    let b_u = (u >> bit) & 1;
                    if (d == 0 && b_u != 0) || (d == 1 && b_u != 1) {
                        include = false;
                        break;
                    }
                }
                if include {
                    expected ^= w;
                }
            }
            assert_eq!(scratch.ea[0][e], expected, "ternary point {e}");
        }
        let weight = xof.squeeze_u128();
        let mut wide = [[0u128; 2]; BIT_GROUP_WORDS];
        gf2_64x128_clmul_acc_with_backend(&mut wide, &words64, weight, backend);
        for (u, &w) in words64.iter().enumerate() {
            assert_eq!(
                u128_to_gf128(reduce_wide_gf128(wide[u])),
                gf2_128_mul_portable([w, 0], u128_to_gf128(weight)),
                "64x128 clmul reduce mismatch at {u}"
            );
        }

        // 3. Verify `gf128_dot_acc` (`gf2_128_mul_acc_batch_with_backend`) matches `gf2_128_mul_portable`.
        let lanes_a: [Gf128; 64] = core::array::from_fn(|i| [a[2 * i], a[2 * i + 1]]);
        let lanes_b: [Gf128; 64] = core::array::from_fn(|i| [b[2 * i], b[2 * i + 1]]);
        for len in [7usize, 15, 64] {
            let mut acc_fast = [0u64; 2];
            gf128_dot_acc(&mut acc_fast, &lanes_a[..len], &lanes_b[..len], backend);
            let mut acc_ref = [0u64; 2];
            for (&la, &lb) in lanes_a[..len].iter().zip(&lanes_b[..len]) {
                acc_ref = xor_gf128(acc_ref, gf2_128_mul_portable(la, lb));
            }
            assert_eq!(acc_fast, acc_ref, "gf128_dot_acc mismatch at len {len}");
        }

        // 4. Verify `bind_group_columns` matches exact bit-by-bit evaluation across all 64 lanes x 4 columns.
        let beta: [u128; BIT_GROUP_WORDS] = core::array::from_fn(|_| xof.squeeze_u128());
        let mut pattern = [[0u8; BIT_NIBBLES]; 128];
        for (bit, nibbles) in pattern.iter_mut().enumerate() {
            for nib in 0..BIT_NIBBLES {
                for d in 0..4 {
                    nibbles[nib] |= (((beta[4 * nib + d] >> bit) & 1) as u8) << d;
                }
            }
        }
        for u in 0..BIT_GROUP_WORDS {
            scratch.rows[u] = [a[u], b[u], a[64 + u], b[64 + u]];
        }
        bind_group_columns(
            &scratch.rows,
            &pattern,
            &mut scratch.planes,
            &mut scratch.bound,
            backend,
        );
        for lane in 0..BIT_LANES {
            for col in 0..4 {
                let mut expected = 0u128;
                for (row, &beta_u) in scratch.rows.iter().zip(beta.iter()).take(BIT_GROUP_WORDS) {
                    if (row[col] >> lane) & 1 != 0 {
                        expected ^= beta_u;
                    }
                }
                assert_eq!(
                    scratch.bound[lane][col], expected,
                    "bind_group_columns lane {lane} col {col}"
                );
            }
        }

        // 5. Verify `BitCheckScratch::wipe_all` deterministically zeroizes all live buffers.
        scratch.prepare_tables(128);
        scratch.x_tab[0][0][0] = 0xdead_beef_cafe_babe_u128;
        scratch.tab[0][0] = 0x1111_2222_3333_4444_u128;
        scratch.c_claim[0][0] = [0x1234, 0x5678];
        scratch.wipe_all();
        assert!(scratch.x_tab[0][0].is_empty());
        assert_eq!(scratch.live, 0);
        assert_eq!(scratch.tab[0][0], 0);
        assert_eq!(scratch.c_claim[0][0], [0, 0]);
        assert!(scratch.bound.iter().all(|&row| row == [0; 4]));

        // 6. Verify `u^3 - 7` is irreducible over Goldilocks: `3 | (p - 1)` and `7^((p-1)/3) != 1`.
        let exp = (GOLDILOCKS_P - 1) / 3;
        assert_eq!(exp * 3, GOLDILOCKS_P - 1);
        let mut base = 7u64;
        let mut acc = 1u64;
        let mut e_rem = exp;
        while e_rem > 0 {
            if e_rem & 1 != 0 {
                acc = gl_mul(acc, base);
            }
            base = gl_mul(base, base);
            e_rem >>= 1;
        }
        assert_ne!(acc, 1, "7 must be a cubic non-residue mod Goldilocks p");

        // Verify associativity & distributivity of `GoldExt3`.
        let x = squeeze_g3_challenge(&mut xof);
        let y = squeeze_g3_challenge(&mut xof);
        let z = squeeze_g3_challenge(&mut xof);
        assert_eq!(g3_mul(g3_mul(x, y), z), g3_mul(x, g3_mul(y, z)));
        assert_eq!(g3_mul(x, g3_add(y, z)), g3_add(g3_mul(x, y), g3_mul(x, z)));
    }

    #[test]
    fn replicated_arithmetic_and_shared_sponge_match_native() {
        run(|p, n| {
            let mut e = Engine::new(p, [27; 32], keys(p), n).unwrap();
            let secret = e
                .share(&[if p == 0 {
                    0x5555
                } else if p == 1 {
                    0x3333
                } else {
                    0xf0f0
                }])
                .unwrap();
            let square = e.and(&[(secret[0], secret[0])]).unwrap();
            assert_eq!(e.open(&square).unwrap(), vec![0x5555 ^ 0x3333 ^ 0xf0f0]);
            // Exercise both halves of a super-block, partial 16-gate blocks,
            // odd quad folding, and the maximum flush boundary with varied lanes.
            for len in [
                15,
                16,
                17,
                31,
                32,
                33,
                63,
                64,
                65,
                127,
                128,
                129,
                193,
                MAX_PENDING_BITS + 1,
            ] {
                let xs: Vec<_> = (0..len)
                    .map(|i| {
                        (i as u64)
                            .wrapping_mul(0x9e37_79b9_7f4a_7c15)
                            .rotate_left(p as u32 * 7)
                    })
                    .collect();
                let ys: Vec<_> = xs
                    .iter()
                    .map(|x| x.rotate_left(23) ^ 0xa55a_f00f_1234_5678)
                    .collect();
                let x = e.share(&xs).unwrap();
                let y = e.share(&ys).unwrap();
                let pairs: Vec<_> = x.into_iter().zip(y).collect();
                let z = e.and(&pairs).unwrap();
                assert_eq!(e.pending_bits_raw.len(), (len % MAX_PENDING_BITS) * 6);
                let opened = e.open(&z).unwrap();
                assert!(e.pending_bits_raw.is_empty());
                for (i, got) in opened.into_iter().enumerate() {
                    let mut clear_x = 0;
                    let mut clear_y = 0;
                    for party in 0..3 {
                        let x = (i as u64)
                            .wrapping_mul(0x9e37_79b9_7f4a_7c15)
                            .rotate_left(party * 7);
                        clear_x ^= x;
                        clear_y ^= x.rotate_left(23) ^ 0xa55a_f00f_1234_5678;
                    }
                    assert_eq!(got, clear_x & clear_y, "length {len}, gate {i}");
                }
            }
            for d in [Domain::Gold, Domain::Secp, Domain::Ed] {
                let a = d.sub(d.modulus(), [2, 0, 0, 0]);
                let b = [0xfedc_ba98_7654_3211, 0, 0, 0];
                let aa = e.number(a, d.width());
                let bb = e.number(b, d.width());
                let scale = d.sub(d.modulus(), [1, 0, 0, 0]);
                for operation in 0..4 {
                    let out = match operation {
                        0 => e.field_add(&aa, &bb, d),
                        1 => e.field_sub(&aa, &bb, d),
                        2 => e.field_mul(&aa, &bb, d),
                        _ => e.field_scale(&aa, scale, d),
                    }
                    .unwrap();
                    let expected = match operation {
                        0 => d.add(a, b),
                        1 => d.sub(a, b),
                        2 => d.mul(a, b),
                        _ => d.mul(a, scale),
                    };
                    let clear = e.open(&out).unwrap();
                    for (i, &bit) in clear.iter().enumerate() {
                        assert_eq!(
                            bit,
                            if (expected[i / 64] >> (i % 64)) & 1 != 0 {
                                u64::MAX
                            } else {
                                0
                            },
                            "domain {d:?}, operation {operation}, bit {i}"
                        );
                    }
                }
            }
            let mut s = Sponge::cshake(&mut e, b"test").unwrap();
            s.public(&mut e, &1u64.to_le_bytes()).unwrap();
            s.public(&mut e, &3u64.to_le_bytes()).unwrap();
            s.public(&mut e, b"abc").unwrap();
            s.finalize(&mut e, 4).unwrap();
            let hash = s.squeeze(&mut e, 256).unwrap();
            assert_eq!(
                lane_bytes(&e.open(&hash).unwrap(), 0),
                cshake256_framed_32(b"test", &[b"abc"])
            );
        });
    }

    #[test]
    fn arithmetic_matches_native_over_independent_lanes() {
        run(|p, n| {
            let mut e = Engine::new(p, [28; 32], keys(p), n).unwrap();
            for d in [Domain::Gold, Domain::Secp, Domain::Ed] {
                let values: Vec<[Value; 2]> = (0..64u8)
                    .map(|lane| {
                        core::array::from_fn(|side| {
                            let bytes =
                                cshake256_framed_32(b"OUTER.FIELD.TEST", &[&[lane, side as u8]]);
                            let mut value = crate::scalar::decode(&bytes);
                            if d == Domain::Gold {
                                value = [value[0] >> 1, 0, 0, 0];
                            } else {
                                value[3] >>= 2;
                            }
                            value
                        })
                    })
                    .collect();
                let operands: [Word; 2] = core::array::from_fn(|side| {
                    (0..d.width())
                        .map(|bit| {
                            e.constant(values.iter().enumerate().fold(0, |mask, (lane, v)| {
                                mask | (((v[side][bit / 64] >> (bit % 64)) & 1) << lane)
                            }))
                        })
                        .collect()
                });
                for operation in 0..4 {
                    let out = match operation {
                        0 => e.field_add(&operands[0], &operands[1], d),
                        1 => e.field_sub(&operands[0], &operands[1], d),
                        2 => e.field_mul(&operands[0], &operands[1], d),
                        _ => e.field_scale(&operands[0], [27, 0, 0, 0], d),
                    }
                    .unwrap();
                    let clear = e.open(&out).unwrap();
                    for (lane, v) in values.iter().enumerate() {
                        let expected = match operation {
                            0 => d.add(v[0], v[1]),
                            1 => d.sub(v[0], v[1]),
                            2 => d.mul(v[0], v[1]),
                            _ => d.mul(v[0], [27, 0, 0, 0]),
                        };
                        for (bit, &word) in clear.iter().enumerate() {
                            assert_eq!((word >> lane) & 1, (expected[bit / 64] >> (bit % 64)) & 1);
                        }
                    }
                }
            }
        });
    }

    #[test]
    fn ring_mask_conversion_covers_component_boundaries_and_all_carries() {
        run(|party, network| {
            let mut e = Engine::new(party, [0x63; 32], keys(party), network).unwrap();
            for d in [Domain::Gold, Domain::Secp, Domain::Ed] {
                let max = match d {
                    Domain::Gold => [u64::MAX, 0, 0, 0],
                    Domain::Ed => [u64::MAX, u64::MAX, u64::MAX, 0x7fff_ffff_ffff_ffff],
                    _ => [u64::MAX; 4],
                };
                let zero = [0; 4];
                let one = [1, 0, 0, 0];
                let last = crate::scalar::sub(d.modulus(), one, d.modulus());
                let cases = [
                    [zero; 3],
                    [max, one, zero],
                    [zero, max, one],
                    [max; 3],
                    [d.modulus(); 3],
                    [last, d.modulus(), max],
                    [last; 3],
                ];
                let expected: Vec<Value> =
                    (0..64).map(|lane| [zero, one, last][lane % 3]).collect();
                let clear: Vec<_> = (0..d.width())
                    .map(|bit| {
                        if party != 0 {
                            return 0;
                        }
                        expected.iter().enumerate().fold(0, |word, (lane, value)| {
                            word | (((value[bit / 64] >> (bit % 64)) & 1) << lane)
                        })
                    })
                    .collect();
                let input = e.share(&clear).unwrap();
                let words: Vec<_> = cases.iter().map(|_| input.clone()).collect();
                let masks: Vec<FieldWord> = cases
                    .iter()
                    .map(|case| {
                        (0..64)
                            .map(|_| core::array::from_fn(|side| case[(party + side) % 3]))
                            .collect()
                    })
                    .collect();
                let canonical: Vec<FieldWord> = masks
                    .iter()
                    .map(|mask| {
                        mask.iter()
                            .map(|pair| {
                                pair.map(|v| crate::scalar::sub(v, d.modulus(), d.modulus()))
                            })
                            .collect()
                    })
                    .collect();
                for (bits, case) in e
                    .component_bits_many(&canonical, d)
                    .unwrap()
                    .iter()
                    .zip(cases)
                {
                    let sum = case.into_iter().fold(zero, |acc, v| {
                        d.add(acc, crate::scalar::sub(v, d.modulus(), d.modulus()))
                    });
                    let opened = e.open(bits).unwrap();
                    for lane in 0..64 {
                        let mut actual = [0; 4];
                        for (bit, &word) in opened.iter().enumerate() {
                            actual[bit / 64] |= ((word >> lane) & 1) << (bit % 64);
                        }
                        assert_eq!(actual, sum);
                    }
                }
                let converted = e.bits_to_field_masked(&words, masks, d).unwrap();
                for opened in e.fopen_many(&converted, d).unwrap() {
                    assert_eq!(opened, expected);
                }
            }
        });
    }

    #[test]
    fn masked_field_conversions_and_products_match_all_lanes() {
        run(|p, n| {
            let mut e = Engine::new(p, [61; 32], keys(p), n).unwrap();
            for d in [Domain::Gold, Domain::Secp, Domain::Ed] {
                let values: Vec<[Value; 2]> = (0..64u8)
                    .map(|lane| {
                        core::array::from_fn(|side| {
                            let mut value = crate::scalar::decode(&cshake256_framed_32(
                                b"OUTER.CONVERT.TEST",
                                &[&[lane, side as u8]],
                            ));
                            if d == Domain::Gold {
                                value = [value[0] >> 1, 0, 0, 0];
                            } else {
                                value[3] >>= 2;
                            }
                            value
                        })
                    })
                    .collect();
                let bits: [Word; 2] = core::array::from_fn(|side| {
                    (0..d.width())
                        .map(|bit| {
                            e.constant(values.iter().enumerate().fold(0, |v, (lane, x)| {
                                v | (((x[side][bit / 64] >> (bit % 64)) & 1) << lane)
                            }))
                        })
                        .collect()
                });
                let a = e.bits_to_field(&bits[0], d).unwrap();
                let b = e.bits_to_field(&bits[1], d).unwrap();
                let product = e.fmul(&a, &b, d).unwrap();
                let outputs = [
                    e.fadd(&a, &b, d),
                    e.fsub(&a, &b, d),
                    product,
                    e.fscale(&a, [27, 0, 0, 0], d),
                ];
                for (op, output) in outputs.iter().enumerate() {
                    let encoded = e.field_to_bits(output, d).unwrap();
                    let clear = e.open(&encoded).unwrap();
                    for (lane, x) in values.iter().enumerate() {
                        let expected = match op {
                            0 => d.add(x[0], x[1]),
                            1 => d.sub(x[0], x[1]),
                            2 => d.mul(x[0], x[1]),
                            _ => d.mul(x[0], [27, 0, 0, 0]),
                        };
                        for (bit, word) in clear.iter().enumerate() {
                            assert_eq!((word >> lane) & 1, (expected[bit / 64] >> (bit % 64)) & 1);
                        }
                    }
                }
            }
        });
    }

    #[test]
    fn authentication_rejects_altered_envelope() {
        struct Tamper(Network, bool);
        impl Transport for Tamper {
            fn exchange(&mut self, mut out: [Envelope; 2]) -> Result<[Envelope; 2], Error> {
                if self.1 {
                    out[0].tag[0] ^= 1;
                }
                self.0.exchange(out)
            }
        }
        run(|p, n| {
            let mut e = Engine::new(p, [7; 32], keys(p), Tamper(n, p == 0)).unwrap();
            let result = e.share(&[123]);
            if p == 2 {
                assert!(matches!(result, Err(Error::Authentication(0))));
            } else {
                assert!(result.is_ok());
            }
        });
    }

    #[test]
    fn active_one_bit_boolean_and_fault_with_valid_mac_aborts_before_any_wire_opens() {
        struct CorruptBoolReshare {
            inner: Network,
            is_corrupt: bool,
            target_seq: u64,
            key0: [u8; 32],
            session: [u8; 32],
            exchanges_after_check: Arc<AtomicUsize>,
            check_finished: Arc<AtomicBool>,
        }
        impl Transport for CorruptBoolReshare {
            fn exchange(&mut self, mut out: [Envelope; 2]) -> Result<[Envelope; 2], Error> {
                if self.check_finished.load(Ordering::SeqCst) {
                    self.exchanges_after_check.fetch_add(1, Ordering::SeqCst);
                }
                if self.is_corrupt && out[0].sequence == self.target_seq {
                    // Flip exactly 1 bit in lane 37 of gate 19 and sign a valid MAC.
                    out[0].payload[19] ^= 1u64 << 37;
                    out[0].tag = valid_mac_tag(&self.key0, &self.session, &out[0]);
                }
                self.inner.exchange(out)
            }
        }

        for corrupt_p in 0..3 {
            let session = [0x91 + corrupt_p as u8; 32];
            let after_check: [Arc<AtomicUsize>; 3] =
                core::array::from_fn(|_| Arc::new(AtomicUsize::new(0)));
            let flags: [Arc<AtomicBool>; 3] =
                core::array::from_fn(|_| Arc::new(AtomicBool::new(false)));

            run(|p, n| {
                let transport = CorruptBoolReshare {
                    inner: n,
                    is_corrupt: p == corrupt_p,
                    // seq 0 = share(x), seq 1 = share(y), seq 2 = `and` resharing!
                    target_seq: 2,
                    key0: keys(p)[0],
                    session,
                    exchanges_after_check: after_check[p].clone(),
                    check_finished: flags[p].clone(),
                };
                let mut e = Engine::new(p, session, keys(p), transport).unwrap();
                let x = e
                    .share(&vec![0xdead_beef_cafe_babeu64.wrapping_add(p as u64); 33])
                    .unwrap();
                let y = e
                    .share(&vec![
                        0x0123_4567_89ab_cdefu64.wrapping_mul(p as u64 + 3);
                        33
                    ])
                    .unwrap();
                let pairs: Vec<_> = x.iter().copied().zip(y.iter().copied()).collect();
                let z = e.and(&pairs).unwrap();

                // Attempt to open `z`: pre-open check must fail before `open_raw_bits(&z)` runs.
                let res = e.open(&z);
                flags[p].store(true, Ordering::SeqCst);
                if p != corrupt_p {
                    assert_eq!(
                        res,
                        Err(Error::MultiplicationCheck),
                        "honest custodian {p} must abort with MultiplicationCheck when {corrupt_p} cheats"
                    );
                    // Engine is poisoned: subsequent open attempts must fail with 0 network messages.
                    assert_eq!(e.open(&x), Err(Error::MultiplicationCheck));
                    assert_eq!(after_check[p].load(Ordering::SeqCst), 0);
                }
            });
        }
    }

    #[test]
    fn active_one_limb_prime_field_fault_with_valid_mac_aborts_before_a2b_and_b2a_openings() {
        struct CorruptFieldReshare {
            inner: Network,
            is_corrupt: bool,
            corrupted_once: bool,
            domain: Domain,
            key0: [u8; 32],
            session: [u8; 32],
            opened_masked_diff: Arc<AtomicBool>,
        }
        impl Transport for CorruptFieldReshare {
            fn exchange(&mut self, mut out: [Envelope; 2]) -> Result<[Envelope; 2], Error> {
                // `fmul` resharing has 256 `u64`s to peer 0 and 0 `u64`s to peer 1.
                if self.is_corrupt
                    && !self.corrupted_once
                    && out[0].payload.len() == 256
                    && out[1].payload.is_empty()
                {
                    self.corrupted_once = true;
                    // Add 1 modulo `p` to lane 13's share so it remains 100% canonical `< p`
                    // AND carries a valid pairwise MAC!
                    let off = 13 * 4;
                    let cur: Value = out[0].payload[off..off + 4].try_into().unwrap();
                    let bad = self.domain.add(cur, [1, 0, 0, 0]);
                    out[0].payload[off..off + 4].copy_from_slice(&bad);
                    out[0].tag = valid_mac_tag(&self.key0, &self.session, &out[0]);
                }
                // Detect if `fopen_many` (`512` `u64`s to both peers) or `open` of A2B/B2A delta
                // (`d.width() * 2` `u64`s: `128`, `510`, or `512` `u64`s) ever gets transmitted!
                let len0 = out[0].payload.len();
                let len1 = out[1].payload.len();
                let is_conversion_delta_open =
                    len0 == len1 && (len0 == 512 || len0 == 510 || len0 == 128);
                if is_conversion_delta_open {
                    self.opened_masked_diff.store(true, Ordering::SeqCst);
                }
                self.inner.exchange(out)
            }
        }

        for d in [Domain::Gold, Domain::Secp, Domain::Ed] {
            for a2b in [true, false] {
                for corrupt_p in 0..3 {
                    let session = [0xa0 + (corrupt_p as u8) * 7 + u8::from(a2b); 32];
                    let leaked: [Arc<AtomicBool>; 3] =
                        core::array::from_fn(|_| Arc::new(AtomicBool::new(false)));

                    run(|p, n| {
                        let transport = CorruptFieldReshare {
                            inner: n,
                            is_corrupt: p == corrupt_p,
                            corrupted_once: false,
                            domain: d,
                            key0: keys(p)[0],
                            session,
                            opened_masked_diff: leaked[p].clone(),
                        };
                        let mut e = Engine::new(p, session, keys(p), transport).unwrap();
                        let a = e.fconstant([7, 0, 0, 0]);
                        let b = e.fconstant([11, 0, 0, 0]);
                        let bad_prod = e.fmul(&a, &b, d).unwrap();

                        let res = if a2b {
                            // A2B (`field_to_bits`): must abort BEFORE `v - r` (`512` `u64`s) opens!
                            e.field_to_bits(&bad_prod, d).map(|_| ())
                        } else {
                            // B2A (`bits_to_field`): pending `fmul` fault must abort BEFORE `v - r` opens!
                            let dummy_bits = e.number([5, 0, 0, 0], d.width());
                            e.bits_to_field(&dummy_bits, d).map(|_| ())
                        };
                        if p != corrupt_p {
                            assert_eq!(
                                res,
                                Err(Error::MultiplicationCheck),
                                "domain {d:?}, a2b={a2b}, honest {p}, corrupt {corrupt_p}"
                            );
                            assert!(
                                !leaked[p].load(Ordering::SeqCst),
                                "honest custodian {p} must NEVER open masked A2B/B2A delta on failure!"
                            );
                        }
                    });
                }
            }
        }
    }

    #[test]
    fn consistent_share_additive_faults_are_caught_by_bbcggi19_check_with_zero_wire_openings() {
        struct ConsistentFaultTransport {
            inner: Network,
            fault: Option<FaultInjection>,
            wire_opened: Arc<AtomicBool>,
        }
        impl Transport for ConsistentFaultTransport {
            fn test_fault_raw(&self) -> Option<[usize; 4]> {
                self.fault.map(FaultInjection::to_raw)
            }
            fn exchange(&mut self, out: [Envelope; 2]) -> Result<[Envelope; 2], Error> {
                let len0 = out[0].payload.len();
                let len1 = out[1].payload.len();
                // Detect any opening of secret wires (`33 * 2 = 66` u64s) or A2B/B2A deltas (`128`, `510`, `512`).
                if len0 == len1 && matches!(len0, 66 | 128 | 510 | 512) {
                    self.wire_opened.store(true, Ordering::SeqCst);
                }
                self.inner.exchange(out)
            }
        }

        // 1. Consistent 1-bit Boolean `AND` additive fault (`z = (x & y) ^ (1 << 37)`):
        //    All MACs, edge transcripts, and replicated share consistency checks pass;
        //    ONLY the `GF(2^128)` BBCGGI19 algebraic sacrifice check catches this fault!
        for corrupt_p in 0..3 {
            let session = [0xb1 + corrupt_p as u8; 32];
            let leaked: [Arc<AtomicBool>; 3] =
                core::array::from_fn(|_| Arc::new(AtomicBool::new(false)));
            run(|p, n| {
                let transport = ConsistentFaultTransport {
                    inner: n,
                    fault: (p == corrupt_p).then_some(FaultInjection::BitAnd {
                        call_countdown: 0,
                        gate: 19,
                        lane: 37,
                    }),
                    wire_opened: leaked[p].clone(),
                };
                let mut e = Engine::new(p, session, keys(p), transport).unwrap();
                let x = e.share(&vec![0xaaaa_5555_f0f0_0f0fu64; 33]).unwrap();
                let y = e.share(&vec![0x1234_5678_9abc_def0u64; 33]).unwrap();
                let pairs: Vec<_> = x.iter().copied().zip(y.iter().copied()).collect();
                let z = e.and(&pairs).unwrap();
                assert_eq!(e.open(&z), Err(Error::MultiplicationCheck));
                assert!(!leaked[p].load(Ordering::SeqCst));
            });
        }

        // 2. Consistent 1-limb prime-field `fmul` additive fault (`z = x * y + 1 mod p`)
        //    across `Gold` (`GF(p^3)`), `Secp`, and `Ed` before A2B and B2A openings!
        for d in [Domain::Gold, Domain::Secp, Domain::Ed] {
            for a2b in [true, false] {
                for corrupt_p in 0..3 {
                    let session = [0xc0 + (corrupt_p as u8) * 5 + u8::from(a2b); 32];
                    let leaked: [Arc<AtomicBool>; 3] =
                        core::array::from_fn(|_| Arc::new(AtomicBool::new(false)));
                    run(|p, n| {
                        let transport = ConsistentFaultTransport {
                            inner: n,
                            fault: (p == corrupt_p).then_some(FaultInjection::FieldMul {
                                domain: d,
                                call_countdown: 0,
                                lane: 29,
                            }),
                            wire_opened: leaked[p].clone(),
                        };
                        let mut e = Engine::new(p, session, keys(p), transport).unwrap();
                        let a = e.fconstant([13, 0, 0, 0]);
                        let b = e.fconstant([17, 0, 0, 0]);
                        let bad_prod = e.fmul(&a, &b, d).unwrap();
                        let res = if a2b {
                            e.field_to_bits(&bad_prod, d).map(|_| ())
                        } else {
                            let dummy_bits = e.number([9, 0, 0, 0], d.width());
                            e.bits_to_field(&dummy_bits, d).map(|_| ())
                        };
                        assert_eq!(res, Err(Error::MultiplicationCheck));
                        assert!(!leaked[p].load(Ordering::SeqCst));
                    });
                }
            }
        }
    }
}
