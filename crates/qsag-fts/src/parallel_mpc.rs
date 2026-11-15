//! A 48-round bijective x^7 SPN over GF(2^128)^2 with authenticated MPC.
//! The S-box is bijective over GF(2^128): gcd(7, 2^128-1)=1.
//! The chain hash adds Davies-Meyer feedforward; that hash is not claimed bijective.
//! Formal degree 7^48 > 2^134 is not, by itself, a cryptographic security proof.
//! Every masked power opening is included in the committed BDOZ MAC check.

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use qsag_accel::AcceleratorBackend;
use qsag_accel::ct::{ct_eq_bytes, ct_zeroize_bytes, ct_zeroize_u128s};
use qsag_accel::gf2_128::gf2_128_mul;
use qsag_accel::goldilocks::pack_bytes32_to_limbs56;
use qsag_accel::keccak::{commit_mpc_broadcast, cshake256_framed_32, cshake256_framed_xof};
use qsag_accel::poseidon2::poseidon2_hash_limbs;

/// Nonzero MDS diffusion constants in $\mathbb{F}_{2^{128}}$ for 2-lane Davies-Meyer compression.
const GF128_MDS_A: u128 = 0x9E37_79B9_7F4A_7C15_F39C_C060_5CED_C835;
const GF128_MDS_B: u128 = 0xBF58_476D_1CE4_E5B9_94D0_49BB_1331_11EB;

/// Maximum default allocation of single-use authenticated power tuples per party.
pub const DEFAULT_BEAVER_TRIPLE_POOL: usize = 131_072;
const SPN_ROUNDS: usize = 48;

/// Configuration for `ParallelSeededFts`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ParallelSeededParams {
    /// Merkle tree height $h \ge 1$ (`2^h` few-time epoch leaves).
    pub tree_height: usize,
    /// Winternitz chain length $w \ge 2$ (`0..w` positions, `w - 1` hash steps).
    pub winternitz_w: usize,
    /// Number of parallel chains $L$ per epoch leaf.
    pub num_chains: usize,
    /// Constant sum $S = \lfloor L (w - 1) / 2 \rfloor$.
    pub target_sum: usize,
}

impl ParallelSeededParams {
    pub const CUSTODY_H10_W5: Self = Self {
        tree_height: 10,
        winternitz_w: 5,
        num_chains: 68,
        target_sum: 136,
    };

    #[cfg(test)]
    pub const FAST_H4_W5: Self = Self {
        tree_height: 4,
        winternitz_w: 5,
        num_chains: 4,
        target_sum: 8,
    };

    /// Nonlinear communication depth for a batched schedule, including intermediate and output MAC barriers.
    /// Serial local evaluation is not a distributed scheduler. Tree height is absent.
    pub const fn secret_mpc_depth(&self) -> usize {
        SPN_ROUNDS * (1 + self.winternitz_w) + 8
    }

    pub const fn secret_keccak_and_rounds_vs_internal_tree(&self) -> (usize, usize) {
        (
            self.secret_mpc_depth(),
            24 * (self.tree_height * self.winternitz_w + 1),
        )
    }

    pub fn validate(&self) -> Result<(), ParallelSeededError> {
        if !(1..=20).contains(&self.tree_height)
            || !(2..=256).contains(&self.winternitz_w)
            || self.num_chains == 0
            || self.num_chains > 256
            || self.target_sum > 4096
            || self.target_sum == 0
            || self.target_sum >= self.num_chains * (self.winternitz_w - 1)
        {
            return Err(ParallelSeededError::InvalidThresholdParameters);
        }
        // Public DP, saturating at 2^128. Reaching the cap certifies >=128 bits.
        let cap = crate::u384::U384([0, 0, 1, 0, 0, 0]);
        let mut counts = vec![crate::u384::U384::ZERO; self.target_sum + 1];
        counts[0] = crate::u384::U384::ONE;
        for _ in 0..self.num_chains {
            let mut next = vec![crate::u384::U384::ZERO; counts.len()];
            for (sum, slot) in next.iter_mut().enumerate() {
                for digit in 0..self.winternitz_w.min(sum + 1) {
                    let sum = slot.checked_add(counts[sum - digit]).unwrap_or(cap);
                    *slot = if cap.ct_lt(sum) { cap } else { sum };
                }
            }
            counts = next;
        }
        if !cfg!(test) && counts[self.target_sum] != cap {
            return Err(ParallelSeededError::InvalidThresholdParameters);
        }
        Ok(())
    }
}

/// Errors produced by `ParallelSeededFts` threshold keygen, MAC barrier, or verification.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ParallelSeededError {
    InvalidThresholdParameters,
    Poisoned,
    PersistenceFailed,
    EpochOutOfRange,
    EpochUseBudgetExhausted,
    BeaverPreprocessingExhausted,
    GrindingExhausted,
    CommitmentMismatch { party_id: u16 },
    BdozMacCheckFailed,
    InvalidAuthenticationPath,
    SignatureVerificationFailed,
}

/// Public key for `ParallelSeededFts` (`pk_seed` as 4 canonical Goldilocks limbs + 4-limb Poseidon2 Merkle `root`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParallelSeededPublicKey {
    pub params: ParallelSeededParams,
    pub pk_seed_bytes: [u8; 32],
    pub pk_seed_limbs: [u64; 4],
    pub merkle_root: [u64; 4],
}

/// Single-use authenticated powers a^1 through a^7 of one hidden uniform mask.
/// All seven MACs use the original shared key; no MAC is squared locally.
/// Single use, so not `Clone`: a copy would let one mask open twice.
/// ```compile_fail
/// use qsag_fts::parallel_mpc::AuthenticatedPowerShare;
/// fn dup(power: &AuthenticatedPowerShare) -> AuthenticatedPowerShare { power.clone() }
/// ```
pub struct AuthenticatedPowerShare {
    powers: [AuthWire128; 7],
}
impl AuthenticatedPowerShare {
    fn zeroize(&mut self) {
        for wire in &mut self.powers {
            ct_zeroize_u128s(core::slice::from_mut(&mut wire.val_sh));
            ct_zeroize_u128s(&mut wire.mac);
        }
    }
}
/// Historical name retained for callers that store preprocessing allocations.
pub type AuthenticatedBeaverTriple = AuthenticatedPowerShare;

/// Secret field elements wiped when dropped: DKG samples and products, and reconstructed
/// openings that no MAC check has accepted yet.
struct SecretValues(Vec<u128>);
impl Drop for SecretValues {
    fn drop(&mut self) {
        ct_zeroize_u128s(&mut self.0);
    }
}

/// Authenticated share of an $\mathbb{F}_{2^{128}}$ wire (`val_sh`) + 2-lane BDOZ MAC (`mac[0..2]`).
#[derive(Clone)]
struct AuthWire128 {
    val_sh: u128,
    mac: [u128; 2],
}

impl Drop for AuthWire128 {
    fn drop(&mut self) {
        ct_zeroize_u128s(core::slice::from_mut(&mut self.val_sh));
        ct_zeroize_u128s(&mut self.mac);
    }
}
impl Drop for AuthenticatedPowerShare {
    fn drop(&mut self) {
        self.zeroize();
    }
}

/// Storage must atomically persist the increased use count before returning Ok.
/// Bind the log to a key and prevent rollback across process/device recovery.
pub trait LeafBurnPersistence {
    fn burn_epoch_before_sign(
        &mut self,
        key: &[u8; 32],
        party_id: u16,
        epoch: u32,
        use_count: u8,
    ) -> Result<(), ParallelSeededError>;
}

/// Ephemeral testing log only. Never use for persistent custody: it cannot survive a crash.
#[cfg(any(test, feature = "testing-ephemeral"))]
#[derive(Default)]
pub struct InMemoryBurnLog {
    entries: Vec<([u8; 32], u16, u32, u8)>,
}
#[cfg(any(test, feature = "testing-ephemeral"))]
impl LeafBurnPersistence for InMemoryBurnLog {
    fn burn_epoch_before_sign(
        &mut self,
        key: &[u8; 32],
        party_id: u16,
        epoch: u32,
        use_count: u8,
    ) -> Result<(), ParallelSeededError> {
        if let Some(entry) = self
            .entries
            .iter_mut()
            .find(|e| e.0 == *key && e.1 == party_id && e.2 == epoch)
        {
            if use_count != 1 || entry.3 != 0 {
                return Err(ParallelSeededError::PersistenceFailed);
            }
            entry.3 = use_count;
        } else {
            if use_count != 1 {
                return Err(ParallelSeededError::PersistenceFailed);
            }
            self.entries.push((*key, party_id, epoch, use_count));
        }
        Ok(())
    }
}

/// Per-party threshold share for `ParallelSeededFts` (`0` central reconstruction, private pairwise
/// PRG zero-share seeds, authenticated Beaver pool, `<REDACTED>` `Debug`, `write_volatile` `Drop`).
pub struct ParallelSeededPartyShare {
    pub party_id: u16,
    pub params: ParallelSeededParams,
    key_seed: [u8; 32],
    committee: Vec<u16>,
    sk_seed_lanes: [u128; 2],
    sk_seed_macs: [[u128; 2]; 2],
    sk_prf_lanes: [u128; 2],
    sk_prf_macs: [[u128; 2]; 2],
    bdoz_alpha_share: [u128; 2],
    local_salt_seed: [u8; 32],
    pairwise_zero_seeds: Vec<(u16, [u8; 32])>,
    beaver_pool: Vec<AuthenticatedBeaverTriple>,
    beaver_cursor: usize,
    epoch_uses: Vec<u8>,
    poisoned: bool,
    pending_openings: Vec<(u128, AuthWire128)>,
    #[cfg(test)]
    power_fault: bool,
}

impl fmt::Debug for ParallelSeededPartyShare {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ParallelSeededPartyShare")
            .field("party_id", &self.party_id)
            .field("params", &self.params)
            .field("sk_seed_lanes", &"<REDACTED>")
            .field("sk_prf_lanes", &"<REDACTED>")
            .field("bdoz_alpha_share", &"<REDACTED>")
            .field("pairwise_zero_seeds", &"<REDACTED>")
            .finish()
    }
}

impl Drop for ParallelSeededPartyShare {
    fn drop(&mut self) {
        self.erase();
    }
}
impl ParallelSeededPartyShare {
    pub fn is_poisoned(&self) -> bool {
        self.poisoned
    }
    fn poison(&mut self) {
        self.poisoned = true;
        self.clear_pending_openings();
    }
    fn clear_pending_openings(&mut self) {
        // The authenticated wire wipes itself when dropped.
        for (opened, _) in &mut self.pending_openings {
            ct_zeroize_u128s(core::slice::from_mut(opened));
        }
        self.pending_openings.clear();
    }
    fn erase(&mut self) {
        self.clear_pending_openings();
        ct_zeroize_u128s(&mut self.sk_seed_lanes);
        for m in &mut self.sk_seed_macs {
            ct_zeroize_u128s(m);
        }
        ct_zeroize_u128s(&mut self.sk_prf_lanes);
        for m in &mut self.sk_prf_macs {
            ct_zeroize_u128s(m);
        }
        ct_zeroize_u128s(&mut self.bdoz_alpha_share);
        ct_zeroize_bytes(&mut self.local_salt_seed);
        for (_, seed) in &mut self.pairwise_zero_seeds {
            ct_zeroize_bytes(seed);
        }
        for triple in &mut self.beaver_pool {
            triple.zeroize();
        }
        ct_zeroize_bytes(&mut self.epoch_uses);
    }
}

/// Signature produced by the reference runner; nonlinear depth is independent of h.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParallelSeededSignature {
    pub epoch: u32,
    pub randomizer: [u8; 32],
    pub grind_counter: u32,
    /// `L` 32-byte chain intermediates `[X_{ep, 0, a_0}, ..., X_{ep, L-1, a_{L-1}}]`.
    pub chain_nodes: Vec<[u8; 32]>,
    /// Height-`h` Poseidon2 Merkle sibling path from leaf `epoch` to `pk.merkle_root`.
    pub merkle_siblings: Vec<[u64; 4]>,
}

impl ParallelSeededSignature {
    /// Exact wire length for `params`.
    pub const fn encoded_len(params: &ParallelSeededParams) -> usize {
        40 + 32 * params.num_chains + 32 * params.tree_height
    }

    /// Canonical wire form: `epoch (4, BE) || randomizer (32) || grind_counter (4, BE) ||
    /// chain_nodes (32 each) || merkle_siblings (4 little-endian limbs each)`.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out =
            Vec::with_capacity(40 + 32 * (self.chain_nodes.len() + self.merkle_siblings.len()));
        out.extend_from_slice(&self.epoch.to_be_bytes());
        out.extend_from_slice(&self.randomizer);
        out.extend_from_slice(&self.grind_counter.to_be_bytes());
        for node in &self.chain_nodes {
            out.extend_from_slice(node);
        }
        for limb in self.merkle_siblings.iter().flatten() {
            out.extend_from_slice(&limb.to_le_bytes());
        }
        out
    }

    /// Strict decoder: exact length for `params`, an in-range epoch, and canonical field limbs.
    pub fn from_bytes_canonical(
        params: &ParallelSeededParams,
        bytes: &[u8],
    ) -> Result<Self, ParallelSeededError> {
        let malformed = ParallelSeededError::SignatureVerificationFailed;
        if params.validate().is_err() || bytes.len() != Self::encoded_len(params) {
            return Err(malformed);
        }
        let word = |at: usize| {
            u32::from_be_bytes([bytes[at], bytes[at + 1], bytes[at + 2], bytes[at + 3]])
        };
        let epoch = word(0);
        if (epoch as u64) >> params.tree_height != 0 {
            return Err(ParallelSeededError::EpochOutOfRange);
        }
        let mut randomizer = [0u8; 32];
        randomizer.copy_from_slice(&bytes[4..36]);
        let (nodes, siblings) = bytes[40..].split_at(32 * params.num_chains);
        let chain_nodes = nodes.as_chunks::<32>().0.to_vec();
        let mut merkle_siblings = Vec::with_capacity(params.tree_height);
        for sibling in siblings.as_chunks::<32>().0 {
            let mut limbs = [0u64; 4];
            for (limb, raw) in limbs.iter_mut().zip(sibling.as_chunks::<8>().0) {
                *limb = u64::from_le_bytes(*raw);
                if !qsag_accel::goldilocks::gl_is_canonical(*limb) {
                    return Err(malformed);
                }
            }
            merkle_siblings.push(limbs);
        }
        Ok(Self {
            epoch,
            randomizer,
            grind_counter: word(36),
            chain_nodes,
            merkle_siblings,
        })
    }
}

/// Commit-then-open BDOZ 2-lane GF($2^{128}$) MAC barrier message per party.
#[derive(Clone)]
pub struct CommittedMacBarrierShare {
    pub party_id: u16,
    pub commitment: [u8; 32],
    pub tag_diff_lanes: (u128, u128),
    pub salt: [u8; 32],
}

/// Per-party MAC-check phase. No opening is available before all commitments
/// are frozen. Transport must authenticate sender identities and provide a common
/// broadcast view. Dropping an unfinished round permanently invalidates the key.
pub struct MacCommitRound<'a> {
    share: &'a mut ParallelSeededPartyShare,
    session: [u8; 32],
    round: u32,
    quorum: Vec<u16>,
    payload: [u8; 32],
    salt: [u8; 32],
    commitments: Vec<(u16, [u8; 32])>,
    complete: bool,
}

pub struct MacOpenRound<'a>(MacCommitRound<'a>);

impl<'a> MacCommitRound<'a> {
    fn new(
        share: &'a mut ParallelSeededPartyShare,
        session: [u8; 32],
        round: u32,
        quorum: Vec<u16>,
        payload: [u8; 32],
        salt: [u8; 32],
    ) -> Self {
        Self {
            share,
            session,
            round,
            quorum,
            payload,
            salt,
            commitments: Vec::new(),
            complete: false,
        }
    }
    pub fn commitment(&self) -> (u16, [u8; 32]) {
        (
            self.share.party_id,
            commit_mpc_broadcast(
                &self.session,
                self.round,
                self.share.party_id,
                &self.payload,
                &self.salt,
            ),
        )
    }
    pub fn freeze(
        mut self,
        commitments: &[(u16, [u8; 32])],
    ) -> Result<MacOpenRound<'a>, ParallelSeededError> {
        if commitments.len() != self.quorum.len()
            || self.quorum.iter().enumerate().any(|(i, id)| {
                self.quorum[..i].contains(id)
                    || commitments.iter().filter(|c| c.0 == *id).count() != 1
            })
            || !commitments.contains(&self.commitment())
        {
            return Err(ParallelSeededError::BdozMacCheckFailed);
        }
        self.commitments = commitments.to_vec();
        Ok(MacOpenRound(self))
    }
}
impl MacOpenRound<'_> {
    pub fn opening(&self) -> (u16, [u8; 32], [u8; 32]) {
        (self.0.share.party_id, self.0.payload, self.0.salt)
    }
    /// Checks every opening against the frozen commitments and returns the summed
    /// MAC residual lanes. The round counts as complete only when both are zero;
    /// the caller's release gate takes the acceptance decision from the residual.
    pub(crate) fn residual(
        mut self,
        openings: &[(u16, [u8; 32], [u8; 32])],
    ) -> Result<[u128; 2], ParallelSeededError> {
        if openings.len() != self.0.commitments.len() {
            return Err(ParallelSeededError::BdozMacCheckFailed);
        }
        let mut sum = [0u8; 32];
        for (id, commitment) in &self.0.commitments {
            let mut found = openings.iter().filter(|o| o.0 == *id);
            let (_, payload, salt) = found
                .next()
                .ok_or(ParallelSeededError::BdozMacCheckFailed)?;
            if found.next().is_some() {
                return Err(ParallelSeededError::BdozMacCheckFailed);
            }
            let actual = commit_mpc_broadcast(&self.0.session, self.0.round, *id, payload, salt);
            if !ct_eq_bytes(&actual, commitment) {
                return Err(ParallelSeededError::CommitmentMismatch { party_id: *id });
            }
            for (acc, &value) in sum.iter_mut().zip(payload) {
                *acc ^= value;
            }
        }
        self.0.complete = ct_eq_bytes(&sum, &[0; 32]);
        let lanes = bytes32_to_lanes(&sum);
        Ok([lanes.0, lanes.1])
    }
}
impl Drop for MacCommitRound<'_> {
    fn drop(&mut self) {
        ct_zeroize_bytes(&mut self.payload);
        ct_zeroize_bytes(&mut self.salt);
        if !self.complete {
            self.share.poison();
        }
    }
}

#[inline]
fn bytes32_to_lanes(b: &[u8; 32]) -> (u128, u128) {
    (
        u128::from_le_bytes(core::array::from_fn(|i| b[i])),
        u128::from_le_bytes(core::array::from_fn(|i| b[16 + i])),
    )
}

#[inline]
fn lanes_to_bytes32(l0: u128, l1: u128) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[0..16].copy_from_slice(&l0.to_le_bytes());
    out[16..32].copy_from_slice(&l1.to_le_bytes());
    out
}

fn pow7_plain(x: u128) -> u128 {
    let x2 = gf2_128_mul(x, x);
    let x4 = gf2_128_mul(x2, x2);
    gf2_128_mul(gf2_128_mul(x, x2), x4)
}

// V5 changes the compression function deliberately: one domain-separated stream
// commits to both tweaks and the complete round count. V4 constants are not reused.
fn round_constants(c0: u128, c1: u128) -> [(u128, u128); SPN_ROUNDS] {
    let mut stream = [0u8; SPN_ROUNDS * 32];
    cshake256_framed_xof(
        b"QSAG.PSFTS.POW7_ROUNDS.V5",
        &[
            &c0.to_le_bytes(),
            &c1.to_le_bytes(),
            &(SPN_ROUNDS as u32).to_be_bytes(),
        ],
        &mut stream,
    );
    core::array::from_fn(|round| bytes32_to_lanes(&stream.as_chunks::<32>().0[round]))
}

fn algebraic_step_plain(input: (u128, u128), c0: u128, c1: u128) -> (u128, u128) {
    let mut state = input;
    for rc in round_constants(c0, c1) {
        let x = state.0 ^ rc.0;
        let y = state.1 ^ rc.1;
        let x7 = pow7_plain(x);
        let y7 = pow7_plain(y);
        state = (
            x7 ^ gf2_128_mul(y7, GF128_MDS_A),
            y7 ^ gf2_128_mul(x7, GF128_MDS_B),
        );
    }
    (state.0 ^ input.0, state.1 ^ input.1)
}

#[inline]
fn derive_seed_tweak(pk_seed: &[u8; 32], epoch: u32, chain_idx: u16) -> (u128, u128) {
    let ep_be = epoch.to_be_bytes();
    let ch_be = chain_idx.to_be_bytes();
    let raw = cshake256_framed_32(b"QSAG.PSFTS.SEED_TWK.V2", &[pk_seed, &ep_be, &ch_be]);
    bytes32_to_lanes(&raw)
}

#[inline]
fn derive_chain_tweak(pk_seed: &[u8; 32], epoch: u32, chain_idx: u16, step: u8) -> (u128, u128) {
    let ep_be = epoch.to_be_bytes();
    let ch_be = chain_idx.to_be_bytes();
    let st_be = [step];
    let raw = cshake256_framed_32(
        b"QSAG.PSFTS.CHAIN_TWK.V2",
        &[pk_seed, &ep_be, &ch_be, &st_be],
    );
    bytes32_to_lanes(&raw)
}

#[inline]
fn derive_rand_tweak(pk_seed: &[u8; 32], epoch: u32, use_cnt: u8, msg: &[u8]) -> (u128, u128) {
    let ep_be = epoch.to_be_bytes();
    let u_be = [use_cnt];
    let raw = cshake256_framed_32(b"QSAG.PSFTS.RAND_TWK.V2", &[pk_seed, &ep_be, &u_be, msg]);
    bytes32_to_lanes(&raw)
}

#[inline]
#[cfg(any(test, feature = "test-dealer"))]
fn prf_leaf_chain_seed_plain(
    sk_seed_lanes: (u128, u128),
    pk_seed: &[u8; 32],
    epoch: u32,
    chain_idx: u16,
) -> [u8; 32] {
    let (c0, c1) = derive_seed_tweak(pk_seed, epoch, chain_idx);
    let (o0, o1) = algebraic_step_plain(sk_seed_lanes, c0, c1);
    lanes_to_bytes32(o0, o1)
}

#[inline]
pub fn parallel_chain_step(
    pk_seed: &[u8; 32],
    epoch: u32,
    chain_idx: u16,
    step: u8,
    cur: &[u8; 32],
) -> [u8; 32] {
    let (c0, c1) = derive_chain_tweak(pk_seed, epoch, chain_idx, step);
    let (o0, o1) = algebraic_step_plain(bytes32_to_lanes(cur), c0, c1);
    lanes_to_bytes32(o0, o1)
}

/// Compress all `L` chain endpoints of `epoch` into a 4-limb Poseidon2 leaf using canonical
/// 5-limb 56-bit packing per 32-byte endpoint (`0` modulo-$p$ aliasing!) + all 4 `pk_seed` limbs.
fn hash_epoch_endpoints_poseidon2(
    pk_seed_limbs: &[u64; 4],
    epoch: u32,
    endpoints: &[[u8; 32]],
) -> [u64; 4] {
    let mut limbs = Vec::with_capacity(5 + endpoints.len() * 5);
    limbs.extend_from_slice(pk_seed_limbs);
    limbs.push(epoch as u64);
    for ep_end in endpoints {
        limbs.extend_from_slice(&pack_bytes32_to_limbs56(ep_end));
    }
    poseidon2_hash_limbs(0x5053_4654_535F_4C46, &limbs)
}

/// Derive base-`w` chain offsets of length `L` and check whether their sum equals `target_sum`.
fn derive_sum_constrained_offsets(
    params: &ParallelSeededParams,
    pk_seed: &[u8; 32],
    merkle_root: &[u64; 4],
    epoch: u32,
    randomizer: &[u8; 32],
    msg: &[u8],
    counter: u32,
) -> Option<Vec<u8>> {
    let mut root_bytes = [0u8; 32];
    for (i, limb) in merkle_root.iter().enumerate() {
        root_bytes[i * 8..(i + 1) * 8].copy_from_slice(&limb.to_le_bytes());
    }
    let ep_be = epoch.to_be_bytes();
    let ctr_be = counter.to_be_bytes();
    let mut storage = [0u8; 512];
    let stream = storage.get_mut(..params.num_chains.checked_mul(2)?)?;
    cshake256_framed_xof(
        b"QSAG.PSFTS.HMSG.V2",
        &[pk_seed, &root_bytes, &ep_be, randomizer, &ctr_be, msg],
        stream,
    );

    let w = params.winternitz_w as u16;
    let zone = (65536u32 / (w as u32)) * (w as u32);
    let mut out = [0u8; 256];
    let mut sum = 0usize;
    for (dst, chunk) in out.iter_mut().zip(stream.as_chunks::<2>().0.iter()) {
        let v = u16::from_le_bytes([chunk[0], chunk[1]]) as u32;
        if v >= zone {
            return None;
        }
        let digit = (v % (w as u32)) as u8;
        sum += digit as usize;
        *dst = digit;
    }
    if sum == params.target_sum {
        Some(out[..params.num_chains].to_vec())
    } else {
        None
    }
}

/// Linear operations on BDOZ-authenticated $\mathbb{F}_{2^{128}}$ shares (`0` communication, `0` secrets!).
#[inline]
fn auth_xor(x: &AuthWire128, y: &AuthWire128) -> AuthWire128 {
    AuthWire128 {
        val_sh: x.val_sh ^ y.val_sh,
        mac: [x.mac[0] ^ y.mac[0], x.mac[1] ^ y.mac[1]],
    }
}

#[inline]
fn auth_scale_const(x: &AuthWire128, c: u128) -> AuthWire128 {
    AuthWire128 {
        val_sh: gf2_128_mul(x.val_sh, c),
        mac: [gf2_128_mul(x.mac[0], c), gf2_128_mul(x.mac[1], c)],
    }
}

#[inline]
fn auth_add_pub_const(
    party_idx: usize,
    alpha_i: [u128; 2],
    x: &AuthWire128,
    c: u128,
) -> AuthWire128 {
    let val_sh = if party_idx == 0 {
        x.val_sh ^ c
    } else {
        x.val_sh
    };
    AuthWire128 {
        val_sh,
        mac: [
            x.mac[0] ^ gf2_128_mul(alpha_i[0], c),
            x.mac[1] ^ gf2_128_mul(alpha_i[1], c),
        ],
    }
}

/// In characteristic two all binomial coefficients of (a+d)^7 are one.
/// A single masked d=x+a is enough given authenticated a^1,...,a^7.
fn apply_power(
    power: &AuthenticatedPowerShare,
    d: u128,
    alpha: [u128; 2],
    first: bool,
) -> AuthWire128 {
    let mut d_powers = [1u128; 8];
    let mut acc = 1;
    for slot in d_powers.iter_mut().skip(1) {
        acc = gf2_128_mul(acc, d);
        *slot = acc;
    }
    let mut out = AuthWire128 {
        val_sh: if first { d_powers[7] } else { 0 },
        mac: core::array::from_fn(|lane| gf2_128_mul(alpha[lane], d_powers[7])),
    };
    for (index, wire) in power.powers.iter().enumerate() {
        out = auth_xor(&out, &auth_scale_const(wire, d_powers[6 - index]));
    }
    out
}
fn mpc_pow7(
    shares: &mut [ParallelSeededPartyShare],
    x: &[AuthWire128],
) -> Result<Vec<AuthWire128>, ParallelSeededError> {
    let mut d = 0;
    for (sh, xi) in shares.iter().zip(x) {
        if sh.poisoned {
            return Err(ParallelSeededError::Poisoned);
        }
        let power = sh
            .beaver_pool
            .get(sh.beaver_cursor)
            .ok_or(ParallelSeededError::BeaverPreprocessingExhausted)?;
        d ^= xi.val_sh ^ power.powers[0].val_sh;
    }
    #[cfg(test)]
    if let Some(sh) = shares.iter_mut().find(|sh| sh.power_fault) {
        sh.power_fault = false;
        d ^= 1;
    }
    let mut out = Vec::with_capacity(shares.len());
    for (party, (sh, xi)) in shares.iter_mut().zip(x).enumerate() {
        let power = &mut sh.beaver_pool[sh.beaver_cursor];
        sh.pending_openings
            .push((d, auth_xor(xi, &power.powers[0])));
        out.push(apply_power(power, d, sh.bdoz_alpha_share, party == 0));
        power.zeroize();
        sh.beaver_cursor += 1;
    }
    Ok(out)
}

fn mpc_algebraic_step(
    shares: &mut [ParallelSeededPartyShare],
    in0: &[AuthWire128],
    in1: &[AuthWire128],
    c0: u128,
    c1: u128,
) -> Result<(Vec<AuthWire128>, Vec<AuthWire128>), ParallelSeededError> {
    let mut state0 = in0.to_vec();
    let mut state1 = in1.to_vec();
    for rc in round_constants(c0, c1) {
        for (p, ((x, y), sh)) in state0
            .iter_mut()
            .zip(&mut state1)
            .zip(shares.iter())
            .enumerate()
        {
            *x = auth_add_pub_const(p, sh.bdoz_alpha_share, x, rc.0);
            *y = auth_add_pub_const(p, sh.bdoz_alpha_share, y, rc.1);
        }
        let s0 = mpc_pow7(shares, &state0)?;
        let s1 = mpc_pow7(shares, &state1)?;
        for (((x, y), u), v) in state0.iter_mut().zip(&mut state1).zip(&s0).zip(&s1) {
            *x = auth_xor(u, &auth_scale_const(v, GF128_MDS_A));
            *y = auth_xor(v, &auth_scale_const(u, GF128_MDS_B));
        }
    }
    for ((x, y), (u, v)) in state0.iter_mut().zip(&mut state1).zip(in0.iter().zip(in1)) {
        *x = auth_xor(x, u);
        *y = auth_xor(y, v);
    }
    Ok((state0, state1))
}

/// Clears every party's pending masked openings when an opening attempt ends,
/// whether it returned a value, returned an error or unwound.
struct PendingOpeningsGuard<'a>(&'a mut [ParallelSeededPartyShare]);
impl Drop for PendingOpeningsGuard<'_> {
    fn drop(&mut self) {
        for sh in self.0.iter_mut() {
            sh.clear_pending_openings();
        }
    }
}

/// One party's MAC shares for a batch of wires, wiped when dropped.
struct MacSharePairs(Vec<(u128, u128)>);
impl Drop for MacSharePairs {
    fn drop(&mut self) {
        crate::release_gate::wipe_pairs(&mut self.0);
    }
}

/// Complete public tree cache + threshold shares for `ParallelSeededFts`.
///
/// The party shares are driven only through [`Self::threshold_sign`]; a caller cannot
/// take, replace or reorder them.
/// ```compile_fail
/// fn take(setup: &mut qsag_fts::ParallelSeededThresholdSetup) -> Vec<qsag_fts::ParallelSeededPartyShare> {
///     core::mem::take(&mut setup.shares)
/// }
/// ```
/// Positive control: the public key and tree stay public.
/// ```
/// fn public(setup: &qsag_fts::ParallelSeededThresholdSetup) -> (&qsag_fts::ParallelSeededPublicKey, usize) {
///     (&setup.pk, setup.public_tree_layers.len())
/// }
/// ```
pub struct ParallelSeededThresholdSetup {
    pub pk: ParallelSeededPublicKey,
    pub(crate) shares: Vec<ParallelSeededPartyShare>,
    /// Public Merkle tree layers (`layers[0]` has `2^h` leaves, `layers[h][0]` is `merkle_root`)
    /// built in **plaintext** (`Depth = 0` secret rounds!) once leaf endpoints open.
    pub public_tree_layers: Vec<Vec<[u64; 4]>>,
    #[cfg(test)]
    test_fault: Option<(usize, usize, u128)>,
}

impl ParallelSeededThresholdSetup {
    /// Explicit trusted-dealer convenience API for fast tests.
    /// Deployments requiring dealerless setup use `finalize_parallel_seeded_dkg_party`
    /// with a reviewed private-channel and oblivious-product backend.
    #[cfg(any(test, feature = "test-dealer"))]
    pub fn trusted_dealer_keygen<B: AcceleratorBackend>(
        params: ParallelSeededParams,
        num_parties: usize,
        master_entropy: [u8; 32],
        pk_seed_bytes: [u8; 32],
        accel: &B,
    ) -> Result<Self, ParallelSeededError> {
        Self::trusted_dealer_setup_for_testing(
            params,
            num_parties,
            master_entropy,
            pk_seed_bytes,
            accel,
        )
    }

    /// Trusted-dealer test/recovery setup. The dealer knows seeds and MAC keys.
    /// This is not distributed key generation.
    #[cfg(any(test, feature = "test-dealer"))]
    pub fn trusted_dealer_setup_for_testing<B: AcceleratorBackend>(
        params: ParallelSeededParams,
        num_parties: usize,
        master_entropy: [u8; 32],
        pk_seed_bytes: [u8; 32],
        accel: &B,
    ) -> Result<Self, ParallelSeededError> {
        params.validate()?;
        if !(2..=u16::MAX as usize).contains(&num_parties) {
            return Err(ParallelSeededError::InvalidThresholdParameters);
        }

        let mut ent = master_entropy;
        let seed5 = pack_bytes32_to_limbs56(&pk_seed_bytes);
        let pk_seed_limbs = poseidon2_hash_limbs(0x5345_4544_3536_5633, &seed5);

        let mut sk_seed_bytes = cshake256_framed_32(b"QSAG.PSFTS.KG.SK_SEED.V2", &[&ent]);
        let mut sk_prf_bytes = cshake256_framed_32(b"QSAG.PSFTS.KG.SK_PRF.V2", &[&ent]);
        let mut sk_seed = [
            bytes32_to_lanes(&sk_seed_bytes).0,
            bytes32_to_lanes(&sk_seed_bytes).1,
        ];
        let mut sk_prf = [
            bytes32_to_lanes(&sk_prf_bytes).0,
            bytes32_to_lanes(&sk_prf_bytes).1,
        ];

        // Sample party BDOZ MAC key shares `\alpha_i` (`\bigoplus \alpha_i = \alpha`, then erase `\alpha`!).
        let mut alphas = Vec::with_capacity(num_parties);
        let mut alpha_global = [0u128; 2];
        for p_idx in 0..num_parties {
            let p_be = (p_idx as u16).to_be_bytes();
            let raw = cshake256_framed_32(b"QSAG.PSFTS.ALPHA.V2", &[&ent, &p_be]);
            let ai = [
                u128::from_le_bytes(core::array::from_fn(|i| raw[i])),
                u128::from_le_bytes(core::array::from_fn(|i| raw[16 + i])),
            ];
            alpha_global[0] ^= ai[0];
            alpha_global[1] ^= ai[1];
            alphas.push(ai);
        }

        // Helper dealing an authenticated wire `w` across `num_parties` with uniform shares & MACs.
        let deal_auth_wire = |domain: &[u8], tag: u32, mut secret_val: u128| -> Vec<AuthWire128> {
            let t_be = tag.to_be_bytes();
            let mut full_mac = [
                gf2_128_mul(alpha_global[0], secret_val),
                gf2_128_mul(alpha_global[1], secret_val),
            ];
            let mut val_acc = 0u128;
            let mut mac_acc = [0u128; 2];
            let mut res = Vec::with_capacity(num_parties);
            for p in 0..num_parties {
                let p_be = (p as u16).to_be_bytes();
                if p + 1 < num_parties {
                    let mut rv = cshake256_framed_32(domain, &[&ent, &t_be, &p_be, &[0x01]]);
                    let mut rm = cshake256_framed_32(domain, &[&ent, &t_be, &p_be, &[0x02]]);
                    let v = u128::from_le_bytes(core::array::from_fn(|i| rv[i]));
                    let m0 = u128::from_le_bytes(core::array::from_fn(|i| rm[i]));
                    let m1 = u128::from_le_bytes(core::array::from_fn(|i| rm[16 + i]));
                    val_acc ^= v;
                    mac_acc[0] ^= m0;
                    mac_acc[1] ^= m1;
                    res.push(AuthWire128 {
                        val_sh: v,
                        mac: [m0, m1],
                    });
                    ct_zeroize_bytes(&mut rv);
                    ct_zeroize_bytes(&mut rm);
                } else {
                    res.push(AuthWire128 {
                        val_sh: secret_val ^ val_acc,
                        mac: [full_mac[0] ^ mac_acc[0], full_mac[1] ^ mac_acc[1]],
                    });
                }
            }
            ct_zeroize_u128s(&mut full_mac);
            ct_zeroize_u128s(&mut mac_acc);
            ct_zeroize_u128s(core::slice::from_mut(&mut val_acc));
            ct_zeroize_u128s(core::slice::from_mut(&mut secret_val));
            res
        };

        let seed0_sh = deal_auth_wire(b"QSAG.PSFTS.DEAL_S0.V2", 0, sk_seed[0]);
        let seed1_sh = deal_auth_wire(b"QSAG.PSFTS.DEAL_S1.V2", 1, sk_seed[1]);
        let prf0_sh = deal_auth_wire(b"QSAG.PSFTS.DEAL_P0.V2", 2, sk_prf[0]);
        let prf1_sh = deal_auth_wire(b"QSAG.PSFTS.DEAL_P1.V2", 3, sk_prf[1]);

        // Four signing attempts, bounded by the public resource limit.
        let pool_size = (2 * SPN_ROUNDS * (1 + params.num_chains + params.target_sum) * 4)
            .min(DEFAULT_BEAVER_TRIPLE_POOL);
        let mut party_pools: Vec<Vec<AuthenticatedBeaverTriple>> = (0..num_parties)
            .map(|_| Vec::with_capacity(pool_size))
            .collect();
        let mut raw_ab = vec![0u8; pool_size * 32];
        cshake256_framed_xof(b"QSAG.PSFTS.BEAVER_AB.V2", &[&ent], &mut raw_ab);

        for (tr_idx, chunk) in raw_ab.as_chunks::<32>().0.iter().enumerate() {
            let mut a = u128::from_le_bytes(core::array::from_fn(|i| chunk[i]));
            let mut power = a;
            let dealt: [Vec<AuthWire128>; 7] = core::array::from_fn(|index| {
                let shares =
                    deal_auth_wire(b"QSAG.PSFTS.POWER.V4", (tr_idx * 7 + index) as u32, power);
                power = gf2_128_mul(power, a);
                shares
            });
            for (party, pool) in party_pools.iter_mut().enumerate() {
                pool.push(AuthenticatedPowerShare {
                    powers: core::array::from_fn(|index| dealt[index][party].clone()),
                });
            }
            ct_zeroize_u128s(core::slice::from_mut(&mut a));
            ct_zeroize_u128s(core::slice::from_mut(&mut power));
        }
        ct_zeroize_bytes(&mut raw_ab);

        let num_leaves = 1usize << params.tree_height;
        let mut shares = Vec::with_capacity(num_parties);
        for (p_idx, beaver_pool) in party_pools.into_iter().enumerate() {
            let pid_i = p_idx as u16;
            let pi_be = pid_i.to_be_bytes();
            let local_salt_seed = cshake256_framed_32(b"QSAG.PSFTS.SALT_SEED.V2", &[&ent, &pi_be]);

            let mut pairwise_zero_seeds = Vec::with_capacity(num_parties - 1);
            for j_idx in 0..num_parties {
                if j_idx == p_idx {
                    continue;
                }
                let pid_j = j_idx as u16;
                let lo = pid_i.min(pid_j).to_be_bytes();
                let hi = pid_i.max(pid_j).to_be_bytes();
                let z_seed = cshake256_framed_32(b"QSAG.PSFTS.PAIR_ZSEED.V2", &[&ent, &lo, &hi]);
                pairwise_zero_seeds.push((pid_j, z_seed));
            }

            shares.push(ParallelSeededPartyShare {
                party_id: pid_i,
                params,
                key_seed: pk_seed_bytes,
                committee: (0..num_parties).map(|i| i as u16).collect(),
                sk_seed_lanes: [seed0_sh[p_idx].val_sh, seed1_sh[p_idx].val_sh],
                sk_seed_macs: [seed0_sh[p_idx].mac, seed1_sh[p_idx].mac],
                sk_prf_lanes: [prf0_sh[p_idx].val_sh, prf1_sh[p_idx].val_sh],
                sk_prf_macs: [prf0_sh[p_idx].mac, prf1_sh[p_idx].mac],
                bdoz_alpha_share: alphas[p_idx],
                local_salt_seed,
                pairwise_zero_seeds,
                beaver_pool,
                beaver_cursor: 0,
                epoch_uses: vec![0u8; num_leaves],
                poisoned: false,
                pending_openings: Vec::new(),
                #[cfg(test)]
                power_fault: false,
            });
        }

        // Evaluate endpoints per leaf, then build all public Merkle
        // levels in 100% public plaintext (`Depth = 0` secret rounds!).
        let mut leaves = Vec::with_capacity(num_leaves);
        let mut endpoints = vec![[0u8; 32]; params.num_chains];
        for ep in 0..num_leaves {
            for (ch, end_slot) in endpoints.iter_mut().enumerate() {
                let mut v = prf_leaf_chain_seed_plain(
                    (sk_seed[0], sk_seed[1]),
                    &pk_seed_bytes,
                    ep as u32,
                    ch as u16,
                );
                for step in 0..(params.winternitz_w - 1) {
                    v = parallel_chain_step(&pk_seed_bytes, ep as u32, ch as u16, step as u8, &v);
                }
                *end_slot = v;
            }
            leaves.push(hash_epoch_endpoints_poseidon2(
                &pk_seed_limbs,
                ep as u32,
                &endpoints,
            ));
        }

        // Permanently zeroize ALL offline dealing secrets (`sk_seed`, `sk_prf`, `alpha_global`, `ent`)!
        for ep_buf in &mut endpoints {
            ct_zeroize_bytes(ep_buf);
        }
        ct_zeroize_bytes(&mut sk_seed_bytes);
        ct_zeroize_bytes(&mut sk_prf_bytes);
        ct_zeroize_u128s(&mut sk_seed);
        ct_zeroize_u128s(&mut sk_prf);
        ct_zeroize_u128s(&mut alpha_global);
        for a in &mut alphas {
            ct_zeroize_u128s(a);
        }
        ct_zeroize_bytes(&mut ent);

        let mut public_tree_layers = Vec::with_capacity(params.tree_height + 1);
        public_tree_layers.push(leaves);
        for layer in 0..params.tree_height {
            let cur_layer = &public_tree_layers[layer];
            let mut parents = vec![[0u64; 4]; cur_layer.len() / 2];
            accel
                .try_merkle_layer_poseidon2(cur_layer, &pk_seed_limbs, layer as u32, &mut parents)
                .map_err(|_| ParallelSeededError::InvalidAuthenticationPath)?;
            public_tree_layers.push(parents);
        }
        let merkle_root = public_tree_layers[params.tree_height][0];

        Ok(Self {
            pk: ParallelSeededPublicKey {
                params,
                pk_seed_bytes,
                pk_seed_limbs,
                merkle_root,
            },
            shares,
            public_tree_layers,
            #[cfg(test)]
            test_fault: None,
        })
    }

    /// Local reference orchestration. Callers must supply durable burn storage.
    pub fn threshold_sign<B: AcceleratorBackend>(
        &mut self,
        epoch: u32,
        msg: &[u8],
        session_id: [u8; 32],
        persistence: &mut impl LeafBurnPersistence,
        accel: &B,
    ) -> Result<ParallelSeededSignature, ParallelSeededError> {
        self.pk.params.validate()?;
        if self.shares.len() < 2 || self.shares.iter().any(|s| s.poisoned) {
            return Err(ParallelSeededError::Poisoned);
        }
        let result = self.sign_inner(epoch, msg, session_id, persistence, accel);
        if matches!(
            result,
            Err(ParallelSeededError::CommitmentMismatch { .. })
                | Err(ParallelSeededError::BdozMacCheckFailed)
                | Err(ParallelSeededError::PersistenceFailed)
        ) {
            for share in &mut self.shares {
                share.poison();
            }
        }
        result
    }

    #[cfg(test)]
    pub fn threshold_sign_with_fault<B: AcceleratorBackend>(
        &mut self,
        epoch: u32,
        msg: &[u8],
        session_id: [u8; 32],
        fault: Option<(usize, usize, u128)>,
        accel: &B,
    ) -> Result<ParallelSeededSignature, ParallelSeededError> {
        self.test_fault = fault;
        let result = self.threshold_sign(
            epoch,
            msg,
            session_id,
            &mut InMemoryBurnLog::default(),
            accel,
        );
        self.test_fault = None;
        result
    }

    fn sign_inner<B: AcceleratorBackend>(
        &mut self,
        epoch: u32,
        msg: &[u8],
        session_id: [u8; 32],
        persistence: &mut impl LeafBurnPersistence,
        accel: &B,
    ) -> Result<ParallelSeededSignature, ParallelSeededError> {
        let num_leaves = 1usize << self.pk.params.tree_height;
        let ep_usize = epoch as usize;
        if ep_usize >= num_leaves {
            return Err(ParallelSeededError::EpochOutOfRange);
        }
        let needed = 2 * SPN_ROUNDS * (1 + self.pk.params.num_chains + self.pk.params.target_sum);
        for (i, sh) in self.shares.iter().enumerate() {
            if sh.params != self.pk.params
                || sh.epoch_uses.len() != num_leaves
                || self.shares[..i]
                    .iter()
                    .any(|other| other.party_id == sh.party_id)
            {
                return Err(ParallelSeededError::InvalidThresholdParameters);
            }
            if sh.beaver_pool.len().saturating_sub(sh.beaver_cursor) < needed {
                return Err(ParallelSeededError::BeaverPreprocessingExhausted);
            }
        }
        if self.public_tree_layers.len() != self.pk.params.tree_height + 1
            || self
                .public_tree_layers
                .iter()
                .enumerate()
                .any(|(level, nodes)| nodes.len() != num_leaves >> level)
            || self.public_tree_layers.last().map(|nodes| nodes[0]) != Some(self.pk.merkle_root)
        {
            return Err(ParallelSeededError::InvalidAuthenticationPath);
        }
        let msg_epoch_tag = cshake256_framed_32(b"QSAG.FTS.EPOCH.MESSAGE.V1", &[msg]);
        for sh in &mut self.shares {
            let prior = sh.epoch_uses[ep_usize];
            let mut epoch_guard = qsag_verified::FtsEpochGuard::new_unused(
                self.pk.pk_seed_bytes,
                epoch,
                num_leaves as u32,
            );
            if prior > 0 {
                let (consumed, _) =
                    epoch_guard.consume_epoch_once(self.pk.pk_seed_bytes, epoch, [0u8; 32]);
                epoch_guard = consumed;
            }
            let (next_guard, permit) =
                epoch_guard.consume_epoch_once(self.pk.pk_seed_bytes, epoch, msg_epoch_tag);
            let (key, authorized_epoch, _) = permit
                .map_err(|_| ParallelSeededError::EpochUseBudgetExhausted)?
                .into_binding();
            if key != self.pk.pk_seed_bytes || authorized_epoch != epoch {
                return Err(ParallelSeededError::PersistenceFailed);
            }
            let next_uses = next_guard.used();
            persistence.burn_epoch_before_sign(
                &self.pk.pk_seed_bytes,
                sh.party_id,
                authorized_epoch,
                next_uses,
            )?;
            sh.epoch_uses[ep_usize] = next_uses;
        }
        let use_cnt = self.shares[0].epoch_uses[ep_usize];
        if self
            .shares
            .iter()
            .any(|sh| sh.params != self.pk.params || sh.epoch_uses[ep_usize] != use_cnt)
        {
            return Err(ParallelSeededError::PersistenceFailed);
        }
        let mut quorum_bytes = Vec::new();
        for sh in &self.shares {
            quorum_bytes.extend_from_slice(&sh.party_id.to_be_bytes());
        }
        let session_id = cshake256_framed_32(
            b"QSAG.PSFTS.SIGN_CONTEXT.V3",
            &[
                &session_id,
                &self.pk.pk_seed_bytes,
                &epoch.to_be_bytes(),
                &[use_cnt],
                msg,
                &quorum_bytes,
            ],
        );
        let n = self.shares.len();

        // Authenticated evaluation of `randomizer` (`0` sk_prf reconstruction!)
        let prf_in0: Vec<AuthWire128> = self
            .shares
            .iter()
            .map(|sh| AuthWire128 {
                val_sh: sh.sk_prf_lanes[0],
                mac: sh.sk_prf_macs[0],
            })
            .collect();
        let prf_in1: Vec<AuthWire128> = self
            .shares
            .iter()
            .map(|sh| AuthWire128 {
                val_sh: sh.sk_prf_lanes[1],
                mac: sh.sk_prf_macs[1],
            })
            .collect();
        let (rc0, rc1) = derive_rand_tweak(&self.pk.pk_seed_bytes, epoch, use_cnt, msg);
        let (rand_w0, rand_w1) =
            mpc_algebraic_step(&mut self.shares, &prf_in0, &prf_in1, rc0, rc1)?;

        // Committed BDOZ MAC check BEFORE opening `randomizer`!
        let rand_open = self.open_and_verify_bdoz_wires(
            &session_id,
            0x5241_4E44,
            &[rand_w0, rand_w1],
            None,
            None,
            accel,
        )?;
        let randomizer = lanes_to_bytes32(rand_open[0], rand_open[1]);

        // Public grinding (`0` MPC rounds!)
        let mut chosen_ctr = None;
        let mut chosen_offsets = Vec::new();
        for ctr in 0..1_000_000u32 {
            if let Some(offs) = derive_sum_constrained_offsets(
                &self.pk.params,
                &self.pk.pk_seed_bytes,
                &self.pk.merkle_root,
                epoch,
                &randomizer,
                msg,
                ctr,
            ) {
                chosen_ctr = Some(ctr);
                chosen_offsets = offs;
                break;
            }
        }
        let grind_counter = chosen_ctr.ok_or(ParallelSeededError::GrindingExhausted)?;

        // Authenticated evaluation of all `L` parallel chains (`0` sk_seed reconstruction!)
        let seed_in0: Vec<AuthWire128> = (0..n)
            .map(|p| AuthWire128 {
                val_sh: self.shares[p].sk_seed_lanes[0],
                mac: self.shares[p].sk_seed_macs[0],
            })
            .collect();
        let seed_in1: Vec<AuthWire128> = (0..n)
            .map(|p| AuthWire128 {
                val_sh: self.shares[p].sk_seed_lanes[1],
                mac: self.shares[p].sk_seed_macs[1],
            })
            .collect();

        let mut all_auth_wires: Vec<Vec<AuthWire128>> =
            Vec::with_capacity(self.pk.params.num_chains * 2);
        for (ch, &target_a) in chosen_offsets.iter().enumerate() {
            let (sc0, sc1) = derive_seed_tweak(&self.pk.pk_seed_bytes, epoch, ch as u16);
            let (mut cur0, mut cur1) =
                mpc_algebraic_step(&mut self.shares, &seed_in0, &seed_in1, sc0, sc1)?;
            for step in 0..(target_a as usize) {
                let (tc0, tc1) =
                    derive_chain_tweak(&self.pk.pk_seed_bytes, epoch, ch as u16, step as u8);
                let (nxt0, nxt1) = mpc_algebraic_step(&mut self.shares, &cur0, &cur1, tc0, tc1)?;
                cur0 = nxt0;
                cur1 = nxt1;
            }
            all_auth_wires.push(cur0);
            all_auth_wires.push(cur1);
        }

        // Committed BDOZ 2-lane GF(2^128) MAC barrier BEFORE releasing `chain_nodes`!
        let opened_lanes = self.open_and_verify_bdoz_wires(
            &session_id,
            0x4348_4E53,
            &all_auth_wires,
            Some(&chosen_offsets),
            {
                #[cfg(test)]
                {
                    self.test_fault
                }
                #[cfg(not(test))]
                {
                    None
                }
            },
            accel,
        )?;

        let mut chain_nodes = Vec::with_capacity(self.pk.params.num_chains);
        for pair in opened_lanes.as_chunks::<2>().0.iter() {
            chain_nodes.push(lanes_to_bytes32(pair[0], pair[1]));
        }

        // Depth = 0 secret rounds: attach plaintext height-`h` Merkle sibling path!
        let mut merkle_siblings = Vec::with_capacity(self.pk.params.tree_height);
        let mut cur_idx = ep_usize;
        for tree_layer in self
            .public_tree_layers
            .iter()
            .take(self.pk.params.tree_height)
        {
            let sib_idx = cur_idx ^ 1;
            merkle_siblings.push(tree_layer[sib_idx]);
            cur_idx >>= 1;
        }

        let sig = ParallelSeededSignature {
            epoch,
            randomizer,
            grind_counter,
            chain_nodes,
            merkle_siblings,
        };
        verify_parallel_seeded_fts(&self.pk, msg, &sig, accel)?;
        verify_canonical_minimal_grind_counter(&self.pk, msg, &sig)?;
        Ok(sig)
    }

    /// Genuine SPDZ/BDOZ batch MAC verification over `wires`:
    /// 1. Parties broadcast candidate wire shares `val_sh` (fault-injectable for negative testing)
    ///    yielding candidate public values `\tilde{w}_k`.
    /// 2. Each party `i` **strictly locally** folds its authenticated MAC shares `\gamma_i(w_k)` via
    ///    `accel.bdoz_gf2_128_batch_dot`, computes `\sigma_i = \gamma_{\text{folded}, i} \oplus (\alpha_i \odot \tilde{x}) \oplus z_i`
    ///    where `z_i` is derived from **private pairwise PRG seeds** `k_{min(i,j), max(i,j)}`, and
    ///    broadcasts ONLY `commitment_i` in Phase 1!
    /// 3. Phase 2 verifies all commitments FIRST, then checks `\bigoplus_i \sigma_i == (0, 0)`!
    fn open_and_verify_bdoz_wires<B: AcceleratorBackend>(
        &mut self,
        session_id: &[u8; 32],
        round_tag: u32,
        wires: &[Vec<AuthWire128>],
        signature_codeword: Option<&[u8]>,
        injected_fault: Option<(usize, usize, u128)>,
        accel: &B,
    ) -> Result<Vec<u128>, ParallelSeededError> {
        let params = self.pk.params;
        Self::open_and_verify_shares(
            &mut self.shares,
            &params,
            session_id,
            round_tag,
            wires,
            signature_codeword,
            injected_fault,
            accel,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn open_and_verify_shares<B: AcceleratorBackend>(
        shares: &mut [ParallelSeededPartyShare],
        params: &ParallelSeededParams,
        session_id: &[u8; 32],
        round_tag: u32,
        wires: &[Vec<AuthWire128>],
        signature_codeword: Option<&[u8]>,
        injected_fault: Option<(usize, usize, u128)>,
        accel: &B,
    ) -> Result<Vec<u128>, ParallelSeededError> {
        // Declared first, so it is dropped last: every exit below clears the
        // pending openings after the MAC rounds have released their shares.
        let pending_guard = PendingOpeningsGuard(shares);
        let shares = &mut *pending_guard.0;

        let mut combined = Vec::new();
        let pending_count = shares
            .first()
            .ok_or(ParallelSeededError::BdozMacCheckFailed)?
            .pending_openings
            .len();
        if shares
            .iter()
            .any(|s| s.pending_openings.len() != pending_count)
        {
            return Err(ParallelSeededError::BdozMacCheckFailed);
        }
        for index in 0..pending_count {
            let opened = shares[0].pending_openings[index].0;
            combined.push(
                shares
                    .iter()
                    .enumerate()
                    .map(|(party, sh)| {
                        let mut wire = sh.pending_openings[index].1.clone();
                        wire.val_sh = if party == 0 { opened } else { 0 };
                        wire
                    })
                    .collect(),
            );
        }
        if pending_count != 0 {
            // Verify masked intermediate openings before accessing output shares.
            for sh in shares.iter_mut() {
                sh.clear_pending_openings();
            }
            Self::open_and_verify_shares(
                shares,
                params,
                session_id,
                round_tag ^ 0x8000_0000,
                &combined,
                None,
                None,
                accel,
            )?;
        }
        let num_wires = wires.len();
        let n = shares.len();
        let rt_be = round_tag.to_be_bytes();

        // Candidate wire opening (`\tilde{w}_k = \bigoplus_{p=0..n} candidate_val[p][k]`).
        // The buffer owns every encoding of the candidates and wipes them on any exit;
        // the release gate below takes it by move.
        let mut candidates = crate::release_gate::OpenedCandidates::with_capacity(num_wires);
        for (w_idx, w_parties) in wires.iter().enumerate() {
            let mut acc = 0u128;
            for (p_idx, aw) in w_parties.iter().enumerate() {
                let mut v = aw.val_sh;
                if let Some((fp, fw, delta)) = injected_fault
                    && fp == p_idx
                    && fw == w_idx
                {
                    v ^= delta;
                }
                acc ^= v;
            }
            candidates.push(acc);
        }
        let tilde_digest = cshake256_framed_32(
            b"QSAG.PSFTS.TILDE_DIGEST.V2",
            &[session_id, &rt_be, candidates.digest_input()],
        );

        // Public Fiat-Shamir random linear combination weights bound to `(session_id, round_tag, tilde_digest)`!
        let mut weights = Vec::with_capacity(num_wires);
        for w_idx in 0..num_wires {
            let idx_be = (w_idx as u32).to_be_bytes();
            let wr = cshake256_framed_32(
                b"QSAG.PSFTS.MAC_W.V2",
                &[session_id, &rt_be, &tilde_digest, &idx_be],
            );
            let w0 = u128::from_le_bytes(core::array::from_fn(|i| wr[i]));
            let w1 = u128::from_le_bytes(core::array::from_fn(|i| wr[16 + i]));
            weights.push((w0, w1));
        }
        let tilde_x = accel
            .bdoz_gf2_128_batch_dot(candidates.pairs(), &weights)
            .map_err(|_| ParallelSeededError::BdozMacCheckFailed)?;
        candidates.shed_encodings();

        // Phase 1 (Commit ONLY): Every party computes `sigma_i` strictly from its own private struct!
        let quorum: Vec<_> = shares.iter().map(|sh| sh.party_id).collect();
        let mut barriers = Vec::with_capacity(n);
        for (p_idx, sh) in shares.iter_mut().enumerate() {
            let party_gammas = MacSharePairs(
                wires
                    .iter()
                    .map(|w_parties| (w_parties[p_idx].mac[0], w_parties[p_idx].mac[1]))
                    .collect(),
            );
            let folded_gamma = accel
                .bdoz_gf2_128_batch_dot(&party_gammas.0, &weights)
                .map_err(|_| ParallelSeededError::BdozMacCheckFailed)?;
            drop(party_gammas);

            // Private pairwise PRG zero-share `z_i = \bigoplus_{j != i} F(k_{min(i,j), max(i,j)}, sid || rt || tilde_digest)`!
            let mut z0 = 0u128;
            let mut z1 = 0u128;
            for (_, pair_seed) in &sh.pairwise_zero_seeds {
                let prf = cshake256_framed_32(
                    b"QSAG.PSFTS.PAIR_ZERO_PRF.V2",
                    &[pair_seed, session_id, &rt_be, &tilde_digest],
                );
                z0 ^= u128::from_le_bytes(core::array::from_fn(|i| prf[i]));
                z1 ^= u128::from_le_bytes(core::array::from_fn(|i| prf[16 + i]));
            }

            let sigma0 = folded_gamma.0 ^ gf2_128_mul(tilde_x.0, sh.bdoz_alpha_share[0]) ^ z0;
            let sigma1 = folded_gamma.1 ^ gf2_128_mul(tilde_x.1, sh.bdoz_alpha_share[1]) ^ z1;

            let mut payload = [0u8; 32];
            payload[0..16].copy_from_slice(&sigma0.to_le_bytes());
            payload[16..32].copy_from_slice(&sigma1.to_le_bytes());
            let salt = cshake256_framed_32(
                b"QSAG.PSFTS.BAR_SALT.V2",
                &[&sh.local_salt_seed, session_id, &rt_be, &tilde_digest],
            );
            barriers.push(MacCommitRound::new(
                sh,
                *session_id,
                round_tag,
                quorum.clone(),
                payload,
                salt,
            ));
        }
        let commitments: Vec<_> = barriers.iter().map(MacCommitRound::commitment).collect();
        let mut ready = Vec::with_capacity(n);
        for barrier in barriers {
            ready.push(barrier.freeze(&commitments)?);
        }
        let openings: Vec<_> = ready.iter().map(MacOpenRound::opening).collect();
        // Every party computes its residual from the frozen transcript before any
        // gate exists. An error here drops `candidates`, which wipes them.
        let mut residuals = Vec::with_capacity(n);
        for state in ready {
            residuals.push(state.residual(&openings)?);
        }
        // Each party holds the candidates in its own gate. All gates check their
        // residual before the first one releases; one refusal destroys every copy.
        let mut gate = crate::release_gate::QuorumGate::hold(
            params,
            signature_codeword.is_some(),
            *session_id,
            SPN_ROUNDS,
            n,
            candidates,
        );
        gate.verify_all(&residuals)?;
        gate.release(signature_codeword.unwrap_or(&[]))
    }
}

pub(crate) fn verify_canonical_minimal_grind_counter(
    pk: &ParallelSeededPublicKey,
    msg: &[u8],
    sig: &ParallelSeededSignature,
) -> Result<(), ParallelSeededError> {
    for ctr in 0..sig.grind_counter {
        if derive_sum_constrained_offsets(
            &pk.params,
            &pk.pk_seed_bytes,
            &pk.merkle_root,
            sig.epoch,
            &sig.randomizer,
            msg,
            ctr,
        )
        .is_some()
        {
            return Err(ParallelSeededError::SignatureVerificationFailed);
        }
    }
    Ok(())
}

/// Verify a `ParallelSeededSignature` against `pk` and `msg` using `AcceleratorBackend`.
pub fn verify_parallel_seeded_fts<B: AcceleratorBackend>(
    pk: &ParallelSeededPublicKey,
    msg: &[u8],
    sig: &ParallelSeededSignature,
    accel: &B,
) -> Result<(), ParallelSeededError> {
    const GOLDILOCKS_P: u64 = 0xFFFF_FFFF_0000_0001;
    let params = &pk.params;
    params.validate()?;
    if pk.pk_seed_limbs.iter().any(|&x| x >= GOLDILOCKS_P)
        || pk.merkle_root.iter().any(|&x| x >= GOLDILOCKS_P)
        || sig
            .merkle_siblings
            .iter()
            .any(|sib| sib.iter().any(|&x| x >= GOLDILOCKS_P))
    {
        return Err(ParallelSeededError::InvalidAuthenticationPath);
    }
    if pk.pk_seed_limbs
        != poseidon2_hash_limbs(
            0x5345_4544_3536_5633,
            &pack_bytes32_to_limbs56(&pk.pk_seed_bytes),
        )
    {
        return Err(ParallelSeededError::SignatureVerificationFailed);
    }
    if (sig.epoch as usize) >= (1usize << params.tree_height) {
        return Err(ParallelSeededError::EpochOutOfRange);
    }
    if sig.chain_nodes.len() != params.num_chains || sig.merkle_siblings.len() != params.tree_height
    {
        return Err(ParallelSeededError::SignatureVerificationFailed);
    }

    let offsets = derive_sum_constrained_offsets(
        params,
        &pk.pk_seed_bytes,
        &pk.merkle_root,
        sig.epoch,
        &sig.randomizer,
        msg,
        sig.grind_counter,
    )
    .ok_or(ParallelSeededError::SignatureVerificationFailed)?;

    verify_canonical_minimal_grind_counter(pk, msg, sig)?;

    let mut endpoints = Vec::with_capacity(params.num_chains);
    for (ch, (&start_node, &a_pos)) in sig.chain_nodes.iter().zip(offsets.iter()).enumerate() {
        let mut cur = start_node;
        for step in (a_pos as usize)..(params.winternitz_w - 1) {
            cur = parallel_chain_step(&pk.pk_seed_bytes, sig.epoch, ch as u16, step as u8, &cur);
        }
        endpoints.push(cur);
    }

    let mut cur_hash = hash_epoch_endpoints_poseidon2(&pk.pk_seed_limbs, sig.epoch, &endpoints);
    let mut idx = sig.epoch as usize;
    for (layer, &sib) in sig.merkle_siblings.iter().enumerate() {
        let pair = if (idx & 1) == 0 {
            [cur_hash, sib]
        } else {
            [sib, cur_hash]
        };
        let mut out_p = [[0u64; 4]; 1];
        accel
            .try_merkle_layer_poseidon2_at(
                &pair,
                &pk.pk_seed_limbs,
                layer as u32,
                (idx >> 1) as u64,
                &mut out_p,
            )
            .map_err(|_| ParallelSeededError::InvalidAuthenticationPath)?;
        cur_hash = out_p[0];
        idx >>= 1;
    }

    if cur_hash != pk.merkle_root {
        return Err(ParallelSeededError::SignatureVerificationFailed);
    }
    Ok(())
}

impl core::fmt::Display for ParallelSeededError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{self:?}")
    }
}
impl core::error::Error for ParallelSeededError {}

#[path = "sign_session.rs"]
mod sign_session;
pub use sign_session::*;

#[path = "dkg.rs"]
mod dkg;
pub use dkg::*;

#[cfg(test)]
mod power_auth_tests {
    use super::*;
    use qsag_accel::CpuReferenceBackend;
    #[test]
    fn corrupted_masked_opening_poison_is_permanent() {
        let accel = CpuReferenceBackend::new();
        let mut setup = ParallelSeededThresholdSetup::trusted_dealer_setup_for_testing(
            ParallelSeededParams {
                tree_height: 1,
                winternitz_w: 2,
                num_chains: 2,
                target_sum: 1,
            },
            2,
            [71; 32],
            [81; 32],
            &accel,
        )
        .unwrap();
        setup.shares[0].power_fault = true;
        let mut log = InMemoryBurnLog::default();
        assert_eq!(
            setup.threshold_sign(0, b"fault", [1; 32], &mut log, &accel),
            Err(ParallelSeededError::BdozMacCheckFailed)
        );
        assert!(
            setup.shares.iter().all(|s| s.is_poisoned()
                && s.sk_seed_lanes != [0; 2]
                && s.bdoz_alpha_share != [0; 2])
        );
        assert_eq!(
            setup.threshold_sign(1, b"retry", [2; 32], &mut log, &accel),
            Err(ParallelSeededError::Poisoned)
        );
    }
    #[test]
    fn diffusion_is_invertible_and_power_matches_plaintext() {
        assert_ne!(gf2_128_mul(GF128_MDS_A, GF128_MDS_B), 1);
        let accel = CpuReferenceBackend::new();
        let mut setup = ParallelSeededThresholdSetup::trusted_dealer_setup_for_testing(
            ParallelSeededParams {
                tree_height: 1,
                winternitz_w: 2,
                num_chains: 2,
                target_sum: 1,
            },
            2,
            [3; 32],
            [4; 32],
            &accel,
        )
        .unwrap();
        let x: Vec<_> = setup
            .shares
            .iter()
            .map(|s| AuthWire128 {
                val_sh: s.sk_seed_lanes[0],
                mac: s.sk_seed_macs[0],
            })
            .collect();
        let plain = x.iter().fold(0, |acc, x| acc ^ x.val_sh);
        let power = mpc_pow7(&mut setup.shares, &x).unwrap();
        let opened = setup
            .open_and_verify_bdoz_wires(&[5; 32], 1, &[power], None, None, &accel)
            .unwrap();
        assert_eq!(opened[0], pow7_plain(plain));
    }
}

#[cfg(test)]
mod candidate_custody_tests {
    use super::*;
    use crate::release_gate::probe;
    use core::sync::atomic::{AtomicUsize, Ordering};
    use qsag_accel::{
        AccelError, CertifiedKernelPin, CpuReferenceBackend, KernelSlot, KernelTargetArch,
    };

    /// CPU reference backend whose BDOZ fold fails on one chosen call.
    struct FailingFold {
        fail_on_call: usize,
        calls: AtomicUsize,
    }
    impl FailingFold {
        fn new(fail_on_call: usize) -> Self {
            Self {
                fail_on_call,
                calls: AtomicUsize::new(0),
            }
        }
    }
    impl AcceleratorBackend for FailingFold {
        fn target_arch(&self) -> KernelTargetArch {
            CpuReferenceBackend.target_arch()
        }
        fn kernel_pin(&self, slot: KernelSlot) -> CertifiedKernelPin {
            CpuReferenceBackend.kernel_pin(slot)
        }
        fn batch_keccak_f1600(&self, s: &mut [[u64; 25]]) {
            CpuReferenceBackend.batch_keccak_f1600(s);
        }
        fn batch_poseidon2_perm12(&self, s: &mut [[u64; 12]]) {
            CpuReferenceBackend.batch_poseidon2_perm12(s);
        }
        fn goldilocks_ntt_inplace(
            &self,
            b: &mut [u64],
            t: &[u64],
            i: bool,
        ) -> Result<(), AccelError> {
            CpuReferenceBackend.goldilocks_ntt_inplace(b, t, i)
        }
        fn coset_lde_ext2(
            &self,
            e: &[[u64; 2]],
            b: usize,
            s: u64,
            o: &mut [[u64; 2]],
        ) -> Result<(), AccelError> {
            CpuReferenceBackend.coset_lde_ext2(e, b, s, o)
        }
        fn try_merkle_layer_poseidon2_at(
            &self,
            c: &[[u64; 4]],
            p: &[u64; 4],
            l: u32,
            s: u64,
            o: &mut [[u64; 4]],
        ) -> Result<(), AccelError> {
            CpuReferenceBackend.try_merkle_layer_poseidon2_at(c, p, l, s, o)
        }
        fn bdoz_gf2_128_batch_dot(
            &self,
            s: &[(u128, u128)],
            w: &[(u128, u128)],
        ) -> Result<(u128, u128), AccelError> {
            if self.calls.fetch_add(1, Ordering::SeqCst) == self.fail_on_call {
                return Err(AccelError::LengthOverflow);
            }
            CpuReferenceBackend.bdoz_gf2_128_batch_dot(s, w)
        }
    }

    fn setup(parties: usize) -> ParallelSeededThresholdSetup {
        ParallelSeededThresholdSetup::trusted_dealer_setup_for_testing(
            ParallelSeededParams {
                tree_height: 1,
                winternitz_w: 2,
                num_chains: 2,
                target_sum: 1,
            },
            parties,
            [51; 32],
            [52; 32],
            &CpuReferenceBackend,
        )
        .unwrap()
    }
    /// The shared seed lane as one authenticated wire: an opening with no
    /// masked intermediate openings behind it.
    fn seed_wire(setup: &ParallelSeededThresholdSetup) -> Vec<AuthWire128> {
        setup
            .shares
            .iter()
            .map(|s| AuthWire128 {
                val_sh: s.sk_seed_lanes[0],
                mac: s.sk_seed_macs[0],
            })
            .collect()
    }
    fn no_pending(setup: &ParallelSeededThresholdSetup) -> bool {
        setup.shares.iter().all(|s| s.pending_openings.is_empty())
    }

    #[test]
    fn accepted_opening_releases_once_and_wipes_its_working_copies() {
        let mut setup = setup(3);
        let wire = seed_wire(&setup);
        let plain = wire.iter().fold(0, |acc, w| acc ^ w.val_sh);
        probe::reset();
        let opened = setup
            .open_and_verify_bdoz_wires(&[5; 32], 1, &[wire], None, None, &CpuReferenceBackend)
            .unwrap();
        assert_eq!(opened, [plain]);
        let counts = probe::counts();
        assert_eq!((counts.created, counts.wiped, counts.released), (1, 1, 1));
        assert!(setup.shares.iter().all(|s| !s.is_poisoned()));
    }

    #[test]
    fn faulted_candidate_is_wiped_and_never_released() {
        for (parties, faulty_party) in [(2, 0), (2, 1), (3, 0), (3, 2)] {
            let mut setup = setup(parties);
            let wire = seed_wire(&setup);
            probe::reset();
            assert_eq!(
                setup.open_and_verify_bdoz_wires(
                    &[5; 32],
                    1,
                    &[wire],
                    None,
                    Some((faulty_party, 0, 1)),
                    &CpuReferenceBackend,
                ),
                Err(ParallelSeededError::BdozMacCheckFailed)
            );
            // The one candidate buffer was wiped and no party's gate released.
            let counts = probe::counts();
            assert_eq!((counts.created, counts.wiped, counts.released), (1, 1, 0));
            assert!(setup.shares.iter().all(|s| s.is_poisoned()));
            assert!(no_pending(&setup));
        }
    }

    #[test]
    fn accelerator_failure_wipes_candidates_and_clears_pending_openings() {
        // Call 0 folds the candidates; calls 1 and 2 fold each party's MAC shares.
        for fail_on_call in 0..3 {
            let mut setup = setup(2);
            let x = seed_wire(&setup);
            // Leaves one verified-later masked opening pending per party.
            let power = mpc_pow7(&mut setup.shares, &x).unwrap();
            assert!(setup.shares.iter().all(|s| s.pending_openings.len() == 1));
            // The first three folds belong to the pending-opening check; let them pass.
            let accel = FailingFold::new(3 + fail_on_call);
            probe::reset();
            assert_eq!(
                setup.open_and_verify_bdoz_wires(&[5; 32], 1, &[power], None, None, &accel),
                Err(ParallelSeededError::BdozMacCheckFailed)
            );
            assert_eq!(accel.calls.load(Ordering::SeqCst), 4 + fail_on_call);
            // Two buffers: the pending-opening check (released) and the failed output.
            let counts = probe::counts();
            assert_eq!((counts.created, counts.wiped, counts.released), (2, 2, 1));
            assert!(no_pending(&setup));
        }
        // The pending-opening check itself fails: nothing is released at all.
        for fail_on_call in 0..3 {
            let mut setup = setup(2);
            let x = seed_wire(&setup);
            let power = mpc_pow7(&mut setup.shares, &x).unwrap();
            let accel = FailingFold::new(fail_on_call);
            probe::reset();
            assert_eq!(
                setup.open_and_verify_bdoz_wires(&[5; 32], 1, &[power], None, None, &accel),
                Err(ParallelSeededError::BdozMacCheckFailed)
            );
            let counts = probe::counts();
            assert_eq!((counts.created, counts.wiped, counts.released), (1, 1, 0));
            assert!(no_pending(&setup));
        }
    }

    #[test]
    fn mismatched_pending_openings_are_cleared_on_refusal() {
        let mut setup = setup(2);
        let x = seed_wire(&setup);
        let power = mpc_pow7(&mut setup.shares, &x).unwrap();
        // One party recorded an opening its peer did not.
        let extra = setup.shares[1].pending_openings[0].1.clone();
        setup.shares[1].pending_openings.push((9, extra));
        probe::reset();
        assert_eq!(
            setup.open_and_verify_bdoz_wires(
                &[5; 32],
                1,
                &[power],
                None,
                None,
                &CpuReferenceBackend,
            ),
            Err(ParallelSeededError::BdozMacCheckFailed)
        );
        assert!(no_pending(&setup));
        // Refused before any candidate was reconstructed.
        let counts = probe::counts();
        assert_eq!((counts.created, counts.wiped, counts.released), (0, 0, 0));
    }

    #[test]
    fn corrupted_masked_opening_releases_nothing() {
        let mut setup = setup(2);
        let x = seed_wire(&setup);
        setup.shares[0].power_fault = true;
        let power = mpc_pow7(&mut setup.shares, &x).unwrap();
        probe::reset();
        assert_eq!(
            setup.open_and_verify_bdoz_wires(
                &[5; 32],
                1,
                &[power],
                None,
                None,
                &CpuReferenceBackend,
            ),
            Err(ParallelSeededError::BdozMacCheckFailed)
        );
        // Only the pending-opening check ran; the output wire was never opened.
        let counts = probe::counts();
        assert_eq!((counts.created, counts.wiped, counts.released), (1, 1, 0));
        assert!(setup.shares.iter().all(|s| s.is_poisoned()));
        assert!(no_pending(&setup));
    }
}

#[cfg(test)]
mod boundary_tests {
    use super::*;
    use qsag_accel::CpuReferenceBackend;
    struct RejectBurn;
    impl LeafBurnPersistence for RejectBurn {
        fn burn_epoch_before_sign(
            &mut self,
            _: &[u8; 32],
            _: u16,
            _: u32,
            _: u8,
        ) -> Result<(), ParallelSeededError> {
            Err(ParallelSeededError::PersistenceFailed)
        }
    }
    #[test]
    fn burn_failure_precedes_secret_evaluation() {
        let accel = CpuReferenceBackend::new();
        let mut setup = ParallelSeededThresholdSetup::trusted_dealer_setup_for_testing(
            ParallelSeededParams {
                tree_height: 1,
                winternitz_w: 2,
                num_chains: 2,
                target_sum: 1,
            },
            2,
            [11; 32],
            [12; 32],
            &accel,
        )
        .unwrap();
        assert_eq!(
            setup.threshold_sign(0, b"message", [13; 32], &mut RejectBurn, &accel),
            Err(ParallelSeededError::PersistenceFailed)
        );
        assert!(
            setup
                .shares
                .iter()
                .all(|s| s.beaver_cursor == 0 && s.poisoned)
        );
    }
    #[test]
    fn malformed_parameters_are_rejected() {
        let good = ParallelSeededParams::CUSTODY_H10_W5;
        for bad in [
            ParallelSeededParams {
                tree_height: usize::MAX,
                ..good
            },
            ParallelSeededParams {
                num_chains: 0,
                ..good
            },
            ParallelSeededParams {
                winternitz_w: 1,
                ..good
            },
            ParallelSeededParams {
                target_sum: 0,
                ..good
            },
            ParallelSeededParams {
                target_sum: usize::MAX,
                ..good
            },
        ] {
            assert_eq!(
                bad.validate(),
                Err(ParallelSeededError::InvalidThresholdParameters)
            );
        }
    }

    #[test]
    fn noncanonical_goldilocks_limbs_are_rejected_at_verify_entry() {
        const GOLDILOCKS_P: u64 = 0xFFFF_FFFF_0000_0001;
        let accel = CpuReferenceBackend::new();
        let mut setup = ParallelSeededThresholdSetup::trusted_dealer_setup_for_testing(
            ParallelSeededParams {
                tree_height: 1,
                winternitz_w: 2,
                num_chains: 2,
                target_sum: 1,
            },
            2,
            [21; 32],
            [22; 32],
            &accel,
        )
        .unwrap();
        let mut log = InMemoryBurnLog::default();
        let sig = setup
            .threshold_sign(0, b"canonical-check", [23; 32], &mut log, &accel)
            .unwrap();
        verify_parallel_seeded_fts(&setup.pk, b"canonical-check", &sig, &accel).unwrap();

        let mut bad_pk_seed = setup.pk.clone();
        bad_pk_seed.pk_seed_limbs[0] = GOLDILOCKS_P;
        assert_eq!(
            verify_parallel_seeded_fts(&bad_pk_seed, b"canonical-check", &sig, &accel),
            Err(ParallelSeededError::InvalidAuthenticationPath)
        );

        let mut bad_pk_root = setup.pk.clone();
        bad_pk_root.merkle_root[0] = GOLDILOCKS_P;
        assert_eq!(
            verify_parallel_seeded_fts(&bad_pk_root, b"canonical-check", &sig, &accel),
            Err(ParallelSeededError::InvalidAuthenticationPath)
        );

        let mut bad_sig = sig;
        bad_sig.merkle_siblings[0][0] = GOLDILOCKS_P;
        assert_eq!(
            verify_parallel_seeded_fts(&setup.pk, b"canonical-check", &bad_sig, &accel),
            Err(ParallelSeededError::InvalidAuthenticationPath)
        );
    }
}
