//! Fixed-capacity private-policy multisignature as a zk-Hem relation.
//!
//! The only public values are the policy address and a 32-byte message:
//!
//! ```text
//! leaf_i      = sponge12(pk_seed_i || pk_root_i || LEAF)[0..4]
//! node        = sponge12(left || right || NODE || level)[0..4]      (fixed depth, zero padding leaves)
//! policy_root = sponge12(members_root || threshold || ROOT)[0..4]
//! address     = sponge12("QSAG.POLICY/v1" || policy_root)[0..4]
//! ```
//!
//! The relation has `capacity` identical slots. Every slot holds a member public key with
//! its policy path and a `JortsPoseidon2` signature of the message under that key, and the
//! slot's full verification is constrained: the message hash `mu` from the key bytes, the
//! chain digits of `H_msg`, the target digit sum, all 128 chains, the endpoint sponge and
//! the XMSS path up to `pk_root`. A slot also carries a hidden `active` bit. Active slots
//! form a prefix, their member indices strictly increase (so they are distinct members),
//! and `sum(active) - threshold` is a small non-negative number. An inactive slot repeats
//! any valid member signature, so its contents satisfy the same rows and the relation is
//! the same for every threshold, member count and signing subset.
//!
//! Every length in the proof is fixed by `(capacity, depth, regime)` except the number of
//! deduplicated Merkle siblings, which is a function of the Fiat-Shamir query positions.
//! Proofs of one statement under different prover seeds differ in byte length the same way.
//!
//! The row structure depends only on `(capacity, depth)`. The verifier's work is linear in
//! the relation size (it evaluates the row matrices at one point).

use alloc::vec;
use alloc::vec::Vec;

use super::protocol::{self, ZkHemError, ZkHemProof};
use super::relation::{ConstraintSystem, Lc, Shape, poseidon2_perm, sponge12, sponge12_native};
use crate::field::Goldilocks;
use crate::pcs::WhirSecurityRegime;
use crate::sig::{
    AggSigProfile, DOMAIN_H_MSG_STATEFUL, DOMAIN_MERKLE_NODE, DOMAIN_WOTS_PK, DOMAIN_WOTS_STEP,
    JORTS_XMSS_HEIGHT, ValidatorPublicKey, ValidatorSignature, WOTS_CHAINS, WOTS_MAX_STEP,
    WOTS_TARGET_SUM,
};
use crate::sponge::POSEIDON2_CONST_IV;

type F = Goldilocks;
type Digest = [F; 4];

const POLICY_LEAF_TAG: u64 = 0x5153_504C_4541_4631; // "QSPLEAF1"
const POLICY_NODE_TAG: u64 = 0x5153_504E_4F44_4531; // "QSPNODE1"
const POLICY_ROOT_TAG: u64 = 0x5153_5052_4F4F_5431; // "QSPROOT1"
const POLICY_ADDRESS_LABEL: &[u8; 14] = b"QSAG.POLICY/v1";

/// Length of the `QSAG.MU/v2` frame for a 32-byte message, and its 7-byte limbs.
const MU_FRAME_LEN: usize = 79 + 32;
const MU_FRAME_LIMBS: usize = 16;
const MU_MESSAGE_OFFSET: usize = 79;
const MU_FIRST_MESSAGE_LIMB: usize = MU_MESSAGE_OFFSET / 7;
const MU_PUBLIC_LIMBS: usize = MU_FRAME_LIMBS - MU_FIRST_MESSAGE_LIMB;

#[inline]
fn f(x: u64) -> F {
    F::from_u64_reduced(x)
}

fn label_limbs() -> [F; 2] {
    core::array::from_fn(|i| {
        f(POLICY_ADDRESS_LABEL[7 * i..7 * i + 7]
            .iter()
            .fold(0u64, |acc, &b| (acc << 8) | u64::from(b)))
    })
}

fn first4(st: [F; 12]) -> Digest {
    [st[0], st[1], st[2], st[3]]
}

fn first4_lc(st: &[Lc; 12]) -> [Lc; 4] {
    core::array::from_fn(|i| st[i].clone())
}

/// Capacity and policy-tree depth; together they fix the relation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MultisigParams {
    /// Number of signature slots (`N_max`).
    pub capacity: usize,
    /// Depth of the member tree; a policy has at most `2^depth` members.
    pub depth: usize,
}

impl MultisigParams {
    fn valid(self) -> bool {
        (1..=64).contains(&self.capacity) && (1..=20).contains(&self.depth)
    }

    /// Bits of `sum(active) - threshold`.
    fn slack_bits(self) -> usize {
        (usize::BITS - self.capacity.leading_zeros()) as usize
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MultisigError {
    InvalidParams,
    /// Threshold outside `1..=members`, or more members than `2^depth`.
    InvalidPolicy,
    /// Fewer signers than the threshold, more than the capacity, or indices not strictly
    /// increasing.
    InvalidSignerSet,
    /// A signer is not the policy member at its index or its signature does not verify.
    InvalidSignature,
    Proof(ZkHemError),
}

/// A threshold policy over `JortsPoseidon2` public keys.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Policy {
    depth: usize,
    threshold: u32,
    members: Vec<ValidatorPublicKey>,
    /// `levels[0]` are the leaves, `levels[depth]` is the single root.
    levels: Vec<Vec<Digest>>,
}

impl Policy {
    pub fn new(
        members: Vec<ValidatorPublicKey>,
        threshold: u32,
        depth: usize,
    ) -> Result<Self, MultisigError> {
        if !(1..=20).contains(&depth)
            || members.len() > 1usize << depth
            || threshold == 0
            || threshold as usize > members.len()
            || members.iter().any(|pk| pk.profile != AggSigProfile::JortsPoseidon2)
        {
            return Err(MultisigError::InvalidPolicy);
        }
        let mut leaves: Vec<Digest> = members.iter().map(Self::leaf).collect();
        leaves.resize(1usize << depth, [F::ZERO; 4]);
        let mut levels = vec![leaves];
        for level in 0..depth {
            let next = levels[level]
                .chunks(2)
                .map(|pair| Self::node(&pair[0], &pair[1], level))
                .collect();
            levels.push(next);
        }
        Ok(Self {
            depth,
            threshold,
            members,
            levels,
        })
    }

    fn leaf(pk: &ValidatorPublicKey) -> Digest {
        let mut msg = pk.pk_seed.to_vec();
        msg.extend_from_slice(&pk.pk_root);
        msg.push(f(POLICY_LEAF_TAG));
        first4(sponge12_native(&msg))
    }

    fn node(left: &Digest, right: &Digest, level: usize) -> Digest {
        let mut msg = left.to_vec();
        msg.extend_from_slice(right);
        msg.extend_from_slice(&[f(POLICY_NODE_TAG), f(level as u64)]);
        first4(sponge12_native(&msg))
    }

    fn path(&self, index: usize) -> Vec<Digest> {
        (0..self.depth)
            .map(|level| self.levels[level][(index >> level) ^ 1])
            .collect()
    }

    pub fn threshold(&self) -> u32 {
        self.threshold
    }

    pub fn members(&self) -> &[ValidatorPublicKey] {
        &self.members
    }

    /// `Poseidon2("QSAG.POLICY/v1", policy_root)`: the only public handle of the policy.
    pub fn address(&self) -> Digest {
        let mut msg = self.levels[self.depth][0].to_vec();
        msg.extend_from_slice(&[f(u64::from(self.threshold)), f(POLICY_ROOT_TAG)]);
        let policy_root = first4(sponge12_native(&msg));
        let mut msg = label_limbs().to_vec();
        msg.extend_from_slice(&policy_root);
        first4(sponge12_native(&msg))
    }
}

/// One signer: its index in the policy and its signature of the message.
#[derive(Clone, Debug)]
pub struct MultisigSigner {
    pub member_index: usize,
    pub signature: ValidatorSignature,
}

/// The message-dependent part of the `QSAG.MU/v2` frame limbs, as public inputs.
fn message_limbs(message: &[u8; 32]) -> [F; MU_PUBLIC_LIMBS] {
    core::array::from_fn(|j| {
        let limb = MU_FIRST_MESSAGE_LIMB + j;
        f((0..7).fold(0u64, |acc, k| {
            let offset = 7 * limb + k;
            let byte = if (MU_MESSAGE_OFFSET..MU_FRAME_LEN).contains(&offset) {
                u64::from(message[offset - MU_MESSAGE_OFFSET])
            } else {
                0
            };
            (acc << 8) | byte
        }))
    })
}

fn public_inputs(address: &Digest, message: &[u8; 32]) -> Vec<F> {
    let mut out = address.to_vec();
    out.extend_from_slice(&message_limbs(message));
    out
}

/// Assigned contents of one slot.
#[derive(Clone)]
struct Slot {
    active: bool,
    member_index: usize,
    policy_path: Vec<Digest>,
    pk_seed: Digest,
    pk_root: Digest,
    r_rand: Digest,
    leaf_idx: u32,
    tsw_ctr: u32,
    chains: Vec<Digest>,
    xmss_path: Vec<Digest>,
}

impl Slot {
    fn placeholder(depth: usize) -> Self {
        Self {
            active: false,
            member_index: 0,
            policy_path: vec![[F::ZERO; 4]; depth],
            pk_seed: [F::ZERO; 4],
            pk_root: [F::ZERO; 4],
            r_rand: [F::ZERO; 4],
            leaf_idx: 0,
            tsw_ctr: 0,
            chains: vec![[F::ZERO; 4]; WOTS_CHAINS],
            xmss_path: vec![[F::ZERO; 4]; JORTS_XMSS_HEIGHT],
        }
    }
}

// ============================================================================
// Gadgets
// ============================================================================

fn alloc4(cs: &mut ConstraintSystem, v: &Digest) -> [Lc; 4] {
    core::array::from_fn(|i| cs.alloc(v[i]).into())
}

/// `n` fresh Boolean variables holding the low bits of `value`, least significant first.
fn alloc_bits(cs: &mut ConstraintSystem, value: u64, n: usize) -> Vec<Lc> {
    (0..n)
        .map(|t| {
            let bit: Lc = cs.alloc(f((value >> t) & 1)).into();
            cs.enforce_boolean(&bit);
            bit
        })
        .collect()
}

fn pack_bits(bits: &[Lc]) -> Lc {
    let parts: Vec<(F, &Lc)> = bits
        .iter()
        .enumerate()
        .map(|(t, b)| (f(1u64 << t), b))
        .collect();
    Lc::combine(&parts)
}

/// The unique 64-bit decomposition of the canonical representative of `value`: the bits
/// recompose to it, and if the high 32 bits are all ones the low 32 bits are zero
/// (`p = 2^64 - 2^32 + 1`).
fn canonical_bits(cs: &mut ConstraintSystem, value: &Lc) -> Vec<Lc> {
    let bits = alloc_bits(cs, cs.eval(value).to_canonical_u64(), 64);
    cs.enforce_equal(&pack_bits(&bits), value);
    let mut high_ones = bits[32].clone();
    for bit in &bits[33..] {
        high_ones = cs.mul(&high_ones, bit).into();
    }
    cs.enforce_mul(high_ones, pack_bits(&bits[..32]), Lc::zero());
    bits
}

/// Byte `k` (least significant first) of a 64-bit decomposition.
fn byte_of(bits: &[Lc], k: usize) -> Lc {
    pack_bits(&bits[8 * k..8 * k + 8])
}

/// `if bit { on_one } else { on_zero }` on four limbs.
fn select4(cs: &mut ConstraintSystem, bit: &Lc, on_one: &[Lc; 4], on_zero: &[Lc; 4]) -> [Lc; 4] {
    core::array::from_fn(|i| cs.select(bit, &on_one[i], &on_zero[i]))
}

fn enforce_equal4(cs: &mut ConstraintSystem, a: &[Lc; 4], b: &[Lc; 4]) {
    for (x, y) in a.iter().zip(b) {
        cs.enforce_equal(x, y);
    }
}

/// `crate::sig::compute_message_mu` for a 32-byte message: the five 56-bit limbs of
/// `poseidon2_hash32(frame(pk, message))`.
fn mu_gadget(
    cs: &mut ConstraintSystem,
    seed_bits: &[Vec<Lc>; 4],
    root_bits: &[Vec<Lc>; 4],
    message_limbs: &[Lc],
) -> [Lc; 5] {
    // Frame bytes: 3, 10, "QSAG.MU/v2", 65, profile, pk_seed (4 x 8 LE), pk_root (4 x 8 LE),
    // 32, message. The message bytes arrive through the public limbs.
    let mut frame: Vec<Lc> = Vec::with_capacity(MU_FRAME_LEN);
    let constant = |b: u8| Lc::constant(f(u64::from(b)));
    frame.push(constant(3));
    frame.push(constant(10));
    frame.extend(b"QSAG.MU/v2".iter().map(|&b| constant(b)));
    frame.push(constant(65));
    frame.push(constant(AggSigProfile::JortsPoseidon2 as u8));
    for bits in seed_bits.iter().chain(root_bits) {
        frame.extend((0..8).map(|k| byte_of(bits, k)));
    }
    frame.push(constant(32));
    frame.resize(MU_FRAME_LEN, Lc::zero());
    // `poseidon2_hash32`: 7-byte big-endian limbs, a 0x01 byte after the message.
    frame.push(constant(1));
    debug_assert_eq!(frame.len(), 7 * MU_FRAME_LIMBS);
    let limbs: Vec<Lc> = (0..MU_FRAME_LIMBS)
        .map(|j| {
            let parts: Vec<(F, &Lc)> = (0..7)
                .map(|k| (f(1u64 << (8 * (6 - k))), &frame[7 * j + k]))
                .collect();
            let limb = Lc::combine(&parts);
            match j.checked_sub(MU_FIRST_MESSAGE_LIMB) {
                Some(m) => limb.plus(&message_limbs[m]),
                None => limb,
            }
        })
        .collect();

    let mut st: [Lc; 12] = core::array::from_fn(|_| Lc::zero());
    st[8] = Lc::constant(f(8));
    st[9] = Lc::constant(f(4));
    st[10] = Lc::constant(f(32));
    st[11] = Lc::constant(f(POSEIDON2_CONST_IV));
    for block in limbs.chunks(8) {
        for (lane, limb) in st.iter_mut().zip(block) {
            *lane = lane.plus(limb);
        }
        poseidon2_perm(cs, &mut st);
    }
    // Sixteen limbs fill two blocks exactly; the padding block is `[1, 0, .., 0, 2^56]`.
    st[0] = st[0].plus_const(F::ONE);
    st[7] = st[7].plus_const(f(1u64 << 56));
    poseidon2_perm(cs, &mut st);

    // Digest byte `8 i + k` is byte `7 - k` of lane `i` (big-endian words).
    let lane_bits: Vec<Vec<Lc>> = (0..4).map(|i| canonical_bits(cs, &st[i])).collect();
    let digest_byte = |n: usize| byte_of(&lane_bits[n / 8], 7 - n % 8);
    core::array::from_fn(|j| {
        let width = if j < 4 { 7 } else { 4 };
        let bytes: Vec<Lc> = (0..width).map(|b| digest_byte(7 * j + b)).collect();
        let parts: Vec<(F, &Lc)> = bytes
            .iter()
            .enumerate()
            .map(|(b, byte)| (f(1u64 << (8 * b)), byte))
            .collect();
        Lc::combine(&parts)
    })
}

/// `crate::sig::merkle_node_hash` with tree index and layer zero.
fn xmss_node(
    cs: &mut ConstraintSystem,
    seed: &[Lc; 4],
    meta: Lc,
    left: &[Lc; 4],
    right: &[Lc; 4],
) -> [Lc; 4] {
    let mut st: [Lc; 12] = core::array::from_fn(|i| match i {
        0..=3 => seed[i].clone(),
        4..=7 => left[i - 4].clone(),
        8 => Lc::constant(f(DOMAIN_MERKLE_NODE)),
        9 => meta.clone(),
        _ => Lc::zero(),
    });
    poseidon2_perm(cs, &mut st);
    for i in 0..4 {
        st[i] = st[i].plus(&right[i]);
    }
    st[4] = st[4].plus_const(F::ONE);
    st[5] = st[5].plus_const(f(POSEIDON2_CONST_IV));
    poseidon2_perm(cs, &mut st);
    first4_lc(&st)
}

/// Rows of one slot. Returns `(active, member index, members root)`.
fn slot_gadget(
    cs: &mut ConstraintSystem,
    params: MultisigParams,
    slot: &Slot,
    message_limbs: &[Lc],
) -> (Lc, Lc, [Lc; 4]) {
    let active: Lc = cs.alloc(f(u64::from(slot.active))).into();
    cs.enforce_boolean(&active);
    let seed = alloc4(cs, &slot.pk_seed);
    let root = alloc4(cs, &slot.pk_root);

    // Policy membership.
    let mut leaf_msg: Vec<Lc> = seed.to_vec();
    leaf_msg.extend_from_slice(&root);
    leaf_msg.push(Lc::constant(f(POLICY_LEAF_TAG)));
    let mut node = first4_lc(&sponge12(cs, &leaf_msg));
    let index_bits = alloc_bits(cs, slot.member_index as u64, params.depth);
    for (level, bit) in index_bits.iter().enumerate() {
        let sibling = alloc4(cs, &slot.policy_path[level]);
        let left = select4(cs, bit, &sibling, &node);
        let right: [Lc; 4] =
            core::array::from_fn(|i| node[i].plus(&sibling[i]).minus(&left[i]));
        let mut msg: Vec<Lc> = left.to_vec();
        msg.extend_from_slice(&right);
        msg.push(Lc::constant(f(POLICY_NODE_TAG)));
        msg.push(Lc::constant(f(level as u64)));
        node = first4_lc(&sponge12(cs, &msg));
    }
    let members_root = node;

    // Message hash from the key bytes.
    let seed_bits: [Vec<Lc>; 4] = core::array::from_fn(|i| canonical_bits(cs, &seed[i]));
    let root_bits: [Vec<Lc>; 4] = core::array::from_fn(|i| canonical_bits(cs, &root[i]));
    let mu = mu_gadget(cs, &seed_bits, &root_bits, message_limbs);

    // `compute_hmsg_stateful`.
    let leaf_bits = alloc_bits(cs, u64::from(slot.leaf_idx), JORTS_XMSS_HEIGHT);
    let leaf_idx = pack_bits(&leaf_bits);
    let tsw_ctr = pack_bits(&alloc_bits(cs, u64::from(slot.tsw_ctr), 32));
    let r_rand = alloc4(cs, &slot.r_rand);
    let mut st: [Lc; 12] = core::array::from_fn(|i| match i {
        0..=3 => seed[i].clone(),
        4..=7 => root[i - 4].clone(),
        8 => Lc::constant(f(DOMAIN_H_MSG_STATEFUL)),
        9 => leaf_idx.scaled(f(1u64 << 32)).plus(&tsw_ctr),
        10 => mu[4].clone(),
        _ => Lc::constant(f(POSEIDON2_CONST_IV)),
    });
    poseidon2_perm(cs, &mut st);
    for i in 0..4 {
        st[i] = st[i].plus(&r_rand[i]);
        st[4 + i] = st[4 + i].plus(&mu[i]);
    }
    poseidon2_perm(cs, &mut st);
    st[0] = st[0].plus_const(F::ONE);
    poseidon2_perm(cs, &mut st);

    // `extract_wots_digits_checked`: every limb is below `2^63`, digits are bit pairs.
    let mut digit_bits: Vec<(Lc, Lc)> = Vec::with_capacity(WOTS_CHAINS);
    for (limb_idx, limb) in st.iter().take(5).enumerate() {
        let bits = alloc_bits(cs, cs.eval(limb).to_canonical_u64(), 63);
        cs.enforce_equal(&pack_bits(&bits), limb);
        let digits = if limb_idx < 4 { 31 } else { 4 };
        digit_bits.extend((0..digits).map(|i| (bits[2 * i].clone(), bits[2 * i + 1].clone())));
    }
    debug_assert_eq!(digit_bits.len(), WOTS_CHAINS);
    let digit_sum = digit_bits.iter().fold(Lc::zero(), |acc, (b0, b1)| {
        acc.plus(b0).plus(&b1.scaled(F::TWO))
    });
    cs.enforce_zero(digit_sum.plus_const(F::ZERO - f(WOTS_TARGET_SUM as u64)));

    // Chains: step `s` runs iff `s >= digit`.
    let mut sponge: [Lc; 12] = core::array::from_fn(|i| match i {
        0..=3 => seed[i].clone(),
        4 => leaf_idx.clone(),
        7 => Lc::constant(f(WOTS_CHAINS as u64)),
        8 => Lc::constant(f(DOMAIN_WOTS_PK)),
        11 => Lc::constant(f(POSEIDON2_CONST_IV)),
        _ => Lc::zero(),
    });
    poseidon2_perm(cs, &mut sponge);
    let step_tag = Lc::constant(f(DOMAIN_WOTS_STEP));
    let mut endpoints: Vec<[Lc; 4]> = Vec::with_capacity(2);
    for (chain, (b0, b1)) in digit_bits.iter().enumerate() {
        let both: Lc = cs.mul(b0, b1).into();
        // digit > 0, digit > 1, digit > 2.
        let skip = [b0.plus(b1).minus(&both), b1.clone(), both];
        let mut cur = alloc4(cs, &slot.chains[chain]);
        for (step, skip_step) in skip.iter().enumerate().take(WOTS_MAX_STEP) {
            let addr = leaf_idx
                .scaled(f(1u64 << 16))
                .plus_const(f(((chain as u64) << 4) | step as u64));
            let tweak = [step_tag.clone(), addr, Lc::zero(), Lc::zero()];
            let mut st: [Lc; 12] = core::array::from_fn(|i| match i {
                0..=3 => cur[i].clone(),
                4..=7 => seed[i - 4].clone(),
                _ => tweak[i - 8].clone(),
            });
            poseidon2_perm(cs, &mut st);
            // `poseidon2_compress12_ff`: `perm.b0 + in0 + 2 in1 + 4 tweak`.
            let hashed: [Lc; 4] = core::array::from_fn(|i| {
                st[i]
                    .plus(&cur[i])
                    .plus(&seed[i].scaled(F::TWO))
                    .plus(&tweak[i].scaled(f(4)))
            });
            cur = select4(cs, skip_step, &cur, &hashed);
        }
        endpoints.push(cur);
        if endpoints.len() == 2 {
            for i in 0..4 {
                sponge[i] = sponge[i].plus(&endpoints[0][i]);
                sponge[4 + i] = sponge[4 + i].plus(&endpoints[1][i]);
            }
            poseidon2_perm(cs, &mut sponge);
            endpoints.clear();
        }
    }
    sponge[0] = sponge[0].plus_const(F::ONE);
    poseidon2_perm(cs, &mut sponge);

    // XMSS path to `pk_root`.
    let mut node = first4_lc(&sponge);
    for level in 0..JORTS_XMSS_HEIGHT {
        let sibling = alloc4(cs, &slot.xmss_path[level]);
        let parent_idx = pack_bits(&leaf_bits[level + 1..]);
        let meta = parent_idx.plus_const(f(((level as u64) + 1) << 32));
        let left = select4(cs, &leaf_bits[level], &sibling, &node);
        let right: [Lc; 4] =
            core::array::from_fn(|i| node[i].plus(&sibling[i]).minus(&left[i]));
        node = xmss_node(cs, &seed, meta, &left, &right);
    }
    enforce_equal4(cs, &node, &root);

    (active, pack_bits(&index_bits), members_root)
}

fn synthesize(
    params: MultisigParams,
    address: &Digest,
    message: &[u8; 32],
    threshold: u32,
    slots: &[Slot],
) -> (Shape, Vec<F>) {
    assert_eq!(slots.len(), params.capacity);
    let mut cs = ConstraintSystem::new();
    let publics: Vec<Lc> = public_inputs(address, message)
        .into_iter()
        .map(|v| cs.public_input(v).into())
        .collect();
    let (address_lc, message_limbs) = publics.split_at(4);
    let threshold_lc: Lc = cs.alloc(f(u64::from(threshold))).into();

    let mut prev: Option<(Lc, Lc, [Lc; 4])> = None;
    let mut active_sum = Lc::zero();
    let mut members_root = None;
    for slot in slots {
        let (active, index, root) = slot_gadget(&mut cs, params, slot, message_limbs);
        active_sum = active_sum.plus(&active);
        match &prev {
            None => members_root = Some(root.clone()),
            Some((prev_active, prev_index, prev_root)) => {
                enforce_equal4(&mut cs, &root, prev_root);
                // Active slots are a prefix.
                cs.enforce_mul(
                    active.clone(),
                    Lc::constant(F::ONE).minus(prev_active),
                    Lc::zero(),
                );
                // An active slot's member index exceeds the previous slot's.
                let gap = cs.eval(&index).to_canonical_u64() as i128
                    - cs.eval(prev_index).to_canonical_u64() as i128
                    - 1;
                let gap_bits = alloc_bits(&mut cs, gap.max(0) as u64, params.depth);
                cs.enforce_mul(
                    active.clone(),
                    index
                        .minus(prev_index)
                        .plus_const(F::ZERO - F::ONE)
                        .minus(&pack_bits(&gap_bits)),
                    Lc::zero(),
                );
            }
        }
        prev = Some((active, index, root));
    }

    // `sum(active) >= threshold`.
    let slack = cs.eval(&active_sum).to_canonical_u64() as i128 - i128::from(threshold);
    let slack_bits = alloc_bits(&mut cs, slack.max(0) as u64, params.slack_bits());
    cs.enforce_equal(&active_sum.minus(&threshold_lc), &pack_bits(&slack_bits));

    // Address of the policy.
    let Some(members_root) = members_root else {
        unreachable!("capacity is at least one")
    };
    let mut msg: Vec<Lc> = members_root.to_vec();
    msg.push(threshold_lc);
    msg.push(Lc::constant(f(POLICY_ROOT_TAG)));
    let policy_root = first4_lc(&sponge12(&mut cs, &msg));
    let mut msg: Vec<Lc> = label_limbs().map(Lc::constant).to_vec();
    msg.extend_from_slice(&policy_root);
    let computed = first4_lc(&sponge12(&mut cs, &msg));
    for (got, want) in computed.iter().zip(address_lc) {
        cs.enforce_equal(got, want);
    }
    cs.finish()
}

/// The relation for one `(capacity, depth)`, built once and reused by provers and verifiers.
#[derive(Clone, Debug)]
