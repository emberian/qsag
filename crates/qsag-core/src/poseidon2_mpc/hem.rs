use super::*;

// ============================================================================
// `Hem`-Compatible Native `[Goldilocks; 4]` `JortsPoseidon2` SPDZ MPC Engine
// (`w = 4, chains = 128, target_sum = 192, height = 6`, `0` Intermediate A2B)
// ============================================================================

/// Wire profile tag for `Hem`-aggregatable `JortsPoseidon2` (`AggSigProfile::JortsPoseidon2 = 1`).
pub const HEM_JORTS_PROFILE_BYTE: u8 = 1;
/// Number of base-4 `WOTS+C` chains in `Hem` `JortsPoseidon2` (`128`).
pub const HEM_WOTS_CHAINS: usize = 128;
/// Winternitz base `w = 4` (`0..=3` steps per chain).
pub const HEM_WOTS_BASE_W: usize = 4;
/// Maximum step index per chain (`w - 1 = 3`).
pub const HEM_WOTS_MAX_STEP: usize = HEM_WOTS_BASE_W - 1;
/// Exact constant digit sum (`192 = 128 * 1.5`), fixing online & verifier step count to `192`.
pub const HEM_WOTS_TARGET_SUM: usize = 192;
/// Height of the `Hem` `JortsPoseidon2` XMSS tree (`2^6 = 64` leaves).
pub const HEM_JORTS_XMSS_HEIGHT: usize = 6;
/// Number of leaves in the `Hem` `JortsPoseidon2` XMSS tree (`64`).
pub const HEM_JORTS_MAX_LEAVES: usize = 1usize << HEM_JORTS_XMSS_HEIGHT;
/// Canonical serialized byte length of a `HemJortsPublicKey` (`65` bytes).
pub const HEM_JORTS_PK_BYTES: usize = 1 + 32 + 32;
/// Canonical serialized byte length of a `HemJortsSignature` (`4,328` bytes).
pub const HEM_JORTS_SIG_BYTES: usize =
    32 + 4 + 4 + HEM_WOTS_CHAINS * 32 + HEM_JORTS_XMSS_HEIGHT * 32;

/// Domain tags matching `qsag_agg::sig` bit-for-bit.
pub const HEM_DOMAIN_PRF_WOTS: u64 = 0x5153_4147_5750_5246; // "QSAGWPRF"
pub const HEM_DOMAIN_WOTS_STEP: u64 = 0x5153_4147_5753_5450; // "QSAGWSTP"
pub const HEM_DOMAIN_WOTS_PK: u64 = 0x5153_4147_5750_4B31; // "QSAGWPK1"
pub const HEM_DOMAIN_MERKLE_NODE: u64 = 0x5153_4147_4D52_4B4C; // "QSAGMRKL"
pub const HEM_DOMAIN_H_MSG_STATEFUL: u64 = 0x5153_4147_484D_5331; // "QSAGHMS1"
pub const HEM_DOMAIN_PRF_MSG: u64 = 0x5153_4147_5052_464D; // "QSAGPRFM"

/// Domain tags for deterministic 56-bit injective seed expansion and unassigned-leaf commitments.
pub const HEM_DOMAIN_PK_SEED_EXPAND: u64 = 0x5153_4147_4850_4B53; // "QSAGHPKS"
pub const HEM_DOMAIN_SK_SEED_EXPAND: u64 = 0x5153_4147_4853_4B53; // "QSAGHSKS"
pub const HEM_DOMAIN_SK_PRF_EXPAND: u64 = 0x5153_4147_4853_4B50; // "QSAGHSKP"
pub const HEM_DOMAIN_PRF_CHECK: u64 = 0x5153_4147_4850_4348; // "QSAGHPCH"
pub const HEM_DOMAIN_UNASSIGNED_LEAF: u64 = 0x5153_4147_4855_4E41; // "QSAGHUNA"

/// 4-limb algebraic `Goldilocks` digest (`32` canonical little-endian bytes).
pub type HemDigest4 = [Goldilocks; 4];

/// 5-limb 56-bit injective `Goldilocks` packing of a 32-byte digest (`0` mod-`p` collisions).
pub type HemDigest5 = [Goldilocks; 5];

/// Bijectively pack 32 raw bytes into 5 canonical `Goldilocks` limbs (`4 × 56` bits + `1 × 32` bits),
/// matching `qsag_agg::sig::bytes32_to_limbs56` bit-for-bit.
#[inline]
pub fn hem_bytes32_to_limbs56(bytes: &[u8; 32]) -> HemDigest5 {
    let mut out = [Goldilocks::ZERO; 5];
    for i in 0..4 {
        let mut v = 0u64;
        for b in 0..7 {
            v |= (bytes[7 * i + b] as u64) << (8 * b);
        }
        out[i] = Goldilocks::from_u64_reduced(v);
    }
    let last = u32::from_le_bytes([bytes[28], bytes[29], bytes[30], bytes[31]]) as u64;
    out[4] = Goldilocks::from_u64_reduced(last);
    out
}

/// Serialize a `HemDigest4` to 32 canonical little-endian bytes (`qsag_agg::sig::digest4_to_bytes`).
#[inline]
pub fn hem_digest4_to_bytes(d: &HemDigest4) -> [u8; 32] {
    let mut out = [0u8; 32];
    for i in 0..4 {
        out[8 * i..8 * (i + 1)].copy_from_slice(&d[i].to_le_bytes());
    }
    out
}

/// Decode a `HemDigest4` from 32 canonical little-endian bytes (`< p` per limb).
#[inline]
pub fn hem_digest4_from_bytes_canonical(bytes: &[u8; 32]) -> Option<HemDigest4> {
    let mut out = [Goldilocks::ZERO; 4];
    for i in 0..4 {
        let mut limb = [0u8; 8];
        limb.copy_from_slice(&bytes[8 * i..8 * (i + 1)]);
        out[i] = Goldilocks::from_le_bytes_canonical(limb).ok()?;
    }
    Some(out)
}

/// Deterministically derive a canonical `HemDigest4` `pk_seed` from a 32-byte DKG public seed.
#[inline]
pub fn hem_pk_seed_from_bytes32(pk_seed_bytes: &[u8; 32]) -> HemDigest4 {
    let limbs5 = hem_bytes32_to_limbs56(pk_seed_bytes);
    let mut st = [
        limbs5[0],
        limbs5[1],
        limbs5[2],
        limbs5[3],
        limbs5[4],
        Goldilocks::ZERO,
        Goldilocks::ZERO,
        Goldilocks::ZERO,
        Goldilocks::from_u64_reduced(HEM_DOMAIN_PK_SEED_EXPAND),
        Goldilocks::ZERO,
        Goldilocks::ZERO,
        Goldilocks::from_u64_reduced(POSEIDON2_CONST_IV),
    ];
    poseidon2_perm12(&mut st);
    [
        st[0] + limbs5[0],
        st[1] + limbs5[1],
        st[2] + limbs5[2],
        st[3] + limbs5[3],
    ]
}

/// Expand a 32-byte secret seed (`SK.seed` or `SK.prf`) in the clear via the exact same 5-limb
/// 56-bit linear packing + feed-forward `poseidon2_perm12` evaluated inside SPDZ MPC.
pub fn hem_expand_secret_bytes32_clear(
    secret_bytes: &[u8; 32],
    pk_seed: HemDigest4,
    domain_tag: u64,
) -> HemDigest4 {
    let mut limbs5 = hem_bytes32_to_limbs56(secret_bytes);
    let mut st = [
        limbs5[0],
        limbs5[1],
        limbs5[2],
        limbs5[3],
        limbs5[4],
        pk_seed[0],
        pk_seed[1],
        pk_seed[2],
        pk_seed[3],
        Goldilocks::from_u64_reduced(domain_tag),
        Goldilocks::ZERO,
        Goldilocks::from_u64_reduced(POSEIDON2_CONST_IV),
    ];
    poseidon2_perm12(&mut st);
    let out = [
        st[0] + limbs5[0],
        st[1] + limbs5[1],
        st[2] + limbs5[2],
        st[3] + limbs5[3],
    ];
    wipe_goldilocks(&mut limbs5);
    wipe_goldilocks(&mut st);
    out
}

/// Canonical 65-byte `Hem`-compatible `JortsPoseidon2` validator public key
/// (`0x01 || pk_seed_le32 || pk_root_le32`, byte-identical to `qsag_agg::ValidatorPublicKey`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct HemJortsPublicKey {
    pub pk_seed: HemDigest4,
    pub pk_root: HemDigest4,
}

impl HemJortsPublicKey {
    /// Serialize to canonical 65-byte `ValidatorPublicKey` wire format.
    pub fn to_bytes(&self) -> [u8; HEM_JORTS_PK_BYTES] {
        let mut out = [0u8; HEM_JORTS_PK_BYTES];
        out[0] = HEM_JORTS_PROFILE_BYTE;
        out[1..33].copy_from_slice(&hem_digest4_to_bytes(&self.pk_seed));
        out[33..65].copy_from_slice(&hem_digest4_to_bytes(&self.pk_root));
        out
    }

    /// Parse from canonical 65-byte `ValidatorPublicKey` wire format.
    pub fn from_bytes_canonical(bytes: &[u8; HEM_JORTS_PK_BYTES]) -> Option<Self> {
        if bytes[0] != HEM_JORTS_PROFILE_BYTE {
            return None;
        }
        let mut s = [0u8; 32];
        let mut r = [0u8; 32];
        s.copy_from_slice(&bytes[1..33]);
        r.copy_from_slice(&bytes[33..65]);
        Some(Self {
            pk_seed: hem_digest4_from_bytes_canonical(&s)?,
            pk_root: hem_digest4_from_bytes_canonical(&r)?,
        })
    }

    /// Projection to [`PqPublicKey`] used by [`EpochLatchCertificate`] and [`crate::dkg::QuorumEpochLatchCluster`].
    #[inline]
    pub fn latch_pq_public_key(&self, dkg_pk_seed: [u8; 32]) -> PqPublicKey {
        PqPublicKey {
            pk_seed: dkg_pk_seed,
            pk_root: hem_digest4_to_bytes(&self.pk_root),
        }
    }
}

/// Canonical 4,328-byte `Hem`-compatible `JortsPoseidon2` signature, byte-identical to
/// `qsag_agg::ValidatorSignature` (`AggSigProfile::JortsPoseidon2`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HemJortsSignature {
    pub r_rand: HemDigest4,
    pub stateful_leaf_idx: u32,
    pub tsw_ctr: u32,
    pub wots_chains: Vec<HemDigest4>,
    pub merkle_path: Vec<HemDigest4>,
}

impl HemJortsSignature {
    /// Encode to canonical 4,328-byte `qsag_agg::ValidatorSignature` wire format.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(HEM_JORTS_SIG_BYTES);
        out.extend_from_slice(&hem_digest4_to_bytes(&self.r_rand));
        out.extend_from_slice(&self.stateful_leaf_idx.to_le_bytes());
        out.extend_from_slice(&self.tsw_ctr.to_le_bytes());
        for c in &self.wots_chains {
            out.extend_from_slice(&hem_digest4_to_bytes(c));
        }
        for sib in &self.merkle_path {
            out.extend_from_slice(&hem_digest4_to_bytes(sib));
        }
        out
    }

    /// Decode from canonical 4,328-byte `qsag_agg::ValidatorSignature` wire format.
    pub fn from_bytes_canonical(bytes: &[u8]) -> Option<Self> {
        if bytes.len() != HEM_JORTS_SIG_BYTES {
            return None;
        }
        let mut pos = 0usize;
        let read_d4 = |buf: &[u8], p: &mut usize| -> Option<HemDigest4> {
            let slice: &[u8; 32] = buf.get(*p..*p + 32)?.try_into().ok()?;
            *p += 32;
            hem_digest4_from_bytes_canonical(slice)
        };
        let read_u32 = |buf: &[u8], p: &mut usize| -> Option<u32> {
            let slice: &[u8; 4] = buf.get(*p..*p + 4)?.try_into().ok()?;
            *p += 4;
            Some(u32::from_le_bytes(*slice))
        };

        let r_rand = read_d4(bytes, &mut pos)?;
        let stateful_leaf_idx = read_u32(bytes, &mut pos)?;
        if (stateful_leaf_idx as usize) >= HEM_JORTS_MAX_LEAVES {
            return None;
        }
        let tsw_ctr = read_u32(bytes, &mut pos)?;
        let mut wots_chains = Vec::with_capacity(HEM_WOTS_CHAINS);
        for _ in 0..HEM_WOTS_CHAINS {
            wots_chains.push(read_d4(bytes, &mut pos)?);
        }
        let mut merkle_path = Vec::with_capacity(HEM_JORTS_XMSS_HEIGHT);
        for _ in 0..HEM_JORTS_XMSS_HEIGHT {
            merkle_path.push(read_d4(bytes, &mut pos)?);
        }
        if pos != bytes.len() {
            return None;
        }
        Some(Self {
            r_rand,
            stateful_leaf_idx,
            tsw_ctr,
            wots_chains,
            merkle_path,
        })
    }
}

/// Public cached height-6 XMSS leaf table, leaf-0 `WOTS+C` endpoints, and `SK.prf` check digest
/// produced during distributed `HemJortsPoseidon2` key generation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HemJortsCachedTree {
    pub dkg_pk_seed: [u8; 32],
    pub pk: HemJortsPublicKey,
    pub active_leaves: usize,
    pub leaves: Vec<HemDigest4>,
    pub leaf0_endpoints: Vec<HemDigest4>,
    pub prf_check: HemDigest4,
}

impl HemJortsCachedTree {
    /// Verify public structural consistency: `active_leaves in 1..=64`, `leaves.len() == 64`,
    /// `leaf0_endpoints` (`128` chains) sponges directly to `leaves[0]`, `pk.pk_seed` matches
    /// `dkg_pk_seed`, any inactive leaves equal `hem_unassigned_leaf_digest`, and the 64 leaves
    /// Merkle-hash to `pk.pk_root`.
    pub fn verify_consistency(&self) -> bool {
        if self.active_leaves == 0
            || self.active_leaves > HEM_JORTS_MAX_LEAVES
            || self.leaves.len() != HEM_JORTS_MAX_LEAVES
            || self.leaf0_endpoints.len() != HEM_WOTS_CHAINS
        {
            return false;
        }
        if self.pk.pk_seed != hem_pk_seed_from_bytes32(&self.dkg_pk_seed) {
            return false;
        }
        let endpoints0: [HemDigest4; HEM_WOTS_CHAINS] =
            core::array::from_fn(|r| self.leaf0_endpoints[r]);
        if hem_compress_wots_endpoints_sponge(self.pk.pk_seed, 0, 0, 0, &endpoints0)
            != self.leaves[0]
        {
            return false;
        }
        for kp in self.active_leaves..HEM_JORTS_MAX_LEAVES {
            if self.leaves[kp] != hem_unassigned_leaf_digest(self.pk.pk_seed, kp as u32) {
                return false;
            }
        }
        hem_merkle_root_from_leaves(self.pk.pk_seed, &self.leaves) == Some(self.pk.pk_root)
    }
}

/// Algebraic 256-bit Jive/feed-forward compression `H_comp(in0, in1, tweak) -> HemDigest4`,
/// matching `qsag_agg::sponge::poseidon2_compress12_ff` bit-for-bit.
#[inline]
pub fn hem_poseidon2_compress12_ff(
    mut in0: HemDigest4,
    in1: HemDigest4,
    tweak: HemDigest4,
) -> HemDigest4 {
    let mut st = [
        in0[0], in0[1], in0[2], in0[3], in1[0], in1[1], in1[2], in1[3], tweak[0], tweak[1],
        tweak[2], tweak[3],
    ];
    poseidon2_perm12(&mut st);
    let out = [
        st[0] + in0[0] + in1[0] * Goldilocks::TWO + tweak[0] * Goldilocks::from_u64_reduced(4),
        st[1] + in0[1] + in1[1] * Goldilocks::TWO + tweak[1] * Goldilocks::from_u64_reduced(4),
        st[2] + in0[2] + in1[2] * Goldilocks::TWO + tweak[2] * Goldilocks::from_u64_reduced(4),
        st[3] + in0[3] + in1[3] * Goldilocks::TWO + tweak[3] * Goldilocks::from_u64_reduced(4),
    ];
    wipe_goldilocks(&mut st);
    wipe_goldilocks(&mut in0);
    out
}

/// Bijective address packing for `WOTS+C` steps (`qsag_agg::sig::pack_wots_addr_limb`).
#[inline]
pub fn hem_pack_wots_addr_limb(
    layer: u32,
    kp_idx: u32,
    chain_idx: u32,
    step_idx: u32,
) -> Goldilocks {
    debug_assert!(layer < 64 && kp_idx < (1 << 20) && chain_idx < 256 && step_idx < 16);
    let packed = ((layer as u64) << 44)
        | ((kp_idx as u64) << 16)
        | ((chain_idx as u64) << 4)
        | (step_idx as u64);
    Goldilocks::from_u64_reduced(packed)
}

/// Clear single-party `WOTS+C` chain base secret `y^(0)` (`qsag_agg::sig::ValidatorKeypair::wots_base_secret`).
#[inline]
pub fn hem_wots_base_secret_clear(
    sk_seed: HemDigest4,
    pk_seed: HemDigest4,
    layer: u32,
    tree_idx: u64,
    kp_idx: u32,
    chain_idx: u32,
) -> HemDigest4 {
    let tweak = [
        Goldilocks::from_u64_reduced(HEM_DOMAIN_PRF_WOTS),
        hem_pack_wots_addr_limb(layer, kp_idx, chain_idx, 0),
        Goldilocks::from_u64_reduced(tree_idx & 0xFFFF_FFFF),
        Goldilocks::from_u64_reduced(tree_idx >> 32),
    ];
    hem_poseidon2_compress12_ff(sk_seed, pk_seed, tweak)
}

/// Public `WOTS+C` step transition `y^(step + 1) = F(pk_seed, y^(step), adrs)`
/// (`qsag_agg::sig::wots_step_hash_injective`).
#[inline]
pub fn hem_wots_step_hash_injective(
    pk_seed: HemDigest4,
    cur: HemDigest4,
    layer: u32,
    tree_idx: u64,
    kp_idx: u32,
    chain_idx: u32,
    step_idx: u32,
) -> HemDigest4 {
    let tweak = [
        Goldilocks::from_u64_reduced(HEM_DOMAIN_WOTS_STEP),
        hem_pack_wots_addr_limb(layer, kp_idx, chain_idx, step_idx),
        Goldilocks::from_u64_reduced(tree_idx & 0xFFFF_FFFF),
        Goldilocks::from_u64_reduced(tree_idx >> 32),
    ];
    hem_poseidon2_compress12_ff(cur, pk_seed, tweak)
}

/// Compress all 128 `WOTS+C` chain endpoints (`y^(3)`) into a 4-limb `wots_pk` leaf digest,
/// matching `qsag_agg::sig::compress_wots_endpoints_sponge` bit-for-bit.
pub fn hem_compress_wots_endpoints_sponge(
    pk_seed: HemDigest4,
    layer: u32,
    tree_idx: u64,
    kp_idx: u32,
    endpoints: &[HemDigest4; HEM_WOTS_CHAINS],
) -> HemDigest4 {
    let layer_kp = ((layer as u64) << 32) | (kp_idx as u64);
    let mut st = [
        pk_seed[0],
        pk_seed[1],
        pk_seed[2],
        pk_seed[3],
        Goldilocks::from_u64_reduced(layer_kp),
        Goldilocks::from_u64_reduced(tree_idx & 0xFFFF_FFFF),
        Goldilocks::from_u64_reduced(tree_idx >> 32),
        Goldilocks::from_u64_reduced(HEM_WOTS_CHAINS as u64),
        Goldilocks::from_u64_reduced(HEM_DOMAIN_WOTS_PK),
        Goldilocks::ZERO,
        Goldilocks::ZERO,
        Goldilocks::from_u64_reduced(POSEIDON2_CONST_IV),
    ];
    poseidon2_perm12(&mut st);
    for pair_idx in 0..(HEM_WOTS_CHAINS / 2) {
        let e0 = endpoints[2 * pair_idx];
        let e1 = endpoints[2 * pair_idx + 1];
        for i in 0..4 {
            st[i] += e0[i];
            st[4 + i] += e1[i];
        }
        poseidon2_perm12(&mut st);
    }
    st[0] += Goldilocks::ONE;
    poseidon2_perm12(&mut st);
    [st[0], st[1], st[2], st[3]]
}

/// Domain-separated public digest for an unassigned leaf slot (`kp_idx >= active_leaves`),
/// disjoint from `HEM_DOMAIN_WOTS_PK` so no valid `WOTS+C` endpoint vector can collide with it.
#[inline]
pub fn hem_unassigned_leaf_digest(pk_seed: HemDigest4, kp_idx: u32) -> HemDigest4 {
    let tweak = [
        Goldilocks::from_u64_reduced(HEM_DOMAIN_UNASSIGNED_LEAF),
        Goldilocks::from_u64_reduced(kp_idx as u64),
        Goldilocks::ZERO,
        Goldilocks::from_u64_reduced(POSEIDON2_CONST_IV),
    ];
    hem_poseidon2_compress12_ff(pk_seed, pk_seed, tweak)
}

/// 2-block binary Merkle node sponge matching `qsag_agg::sig::merkle_node_hash` (`DOMAIN_MERKLE_NODE`).
#[inline]
pub fn hem_merkle_node_hash(
    pk_seed: HemDigest4,
    layer: u32,
    tree_idx: u64,
    level: u32,
    node_idx: u32,
    left: HemDigest4,
    right: HemDigest4,
) -> HemDigest4 {
    debug_assert!(layer <= 0xFFFE && level <= 0xFFFF);
    let meta0 = ((layer as u64) << 48) | ((level as u64) << 32) | (node_idx as u64);
    let mut st = [
        pk_seed[0],
        pk_seed[1],
        pk_seed[2],
        pk_seed[3],
        left[0],
        left[1],
        left[2],
        left[3],
        Goldilocks::from_u64_reduced(HEM_DOMAIN_MERKLE_NODE),
        Goldilocks::from_u64_reduced(meta0),
        Goldilocks::from_u64_reduced(tree_idx & 0xFFFF_FFFF),
        Goldilocks::from_u64_reduced(tree_idx >> 32),
    ];
    poseidon2_perm12(&mut st);
    for i in 0..4 {
        st[i] += right[i];
    }
    st[4] += Goldilocks::ONE;
    st[5] += Goldilocks::from_u64_reduced(POSEIDON2_CONST_IV);
    poseidon2_perm12(&mut st);
    [st[0], st[1], st[2], st[3]]
}

/// Compute the height-6 XMSS Merkle root from 64 leaf digests.
pub fn hem_merkle_root_from_leaves(
    pk_seed: HemDigest4,
    leaves: &[HemDigest4],
) -> Option<HemDigest4> {
    if leaves.len() != HEM_JORTS_MAX_LEAVES {
        return None;
    }
    let mut cur = leaves.to_vec();
    for lvl in 0..HEM_JORTS_XMSS_HEIGHT {
        let mut next = Vec::with_capacity(cur.len() / 2);
        for p in 0..(cur.len() / 2) {
            next.push(hem_merkle_node_hash(
                pk_seed,
                0,
                0,
                (lvl + 1) as u32,
                p as u32,
                cur[2 * p],
                cur[2 * p + 1],
            ));
        }
        cur = next;
    }
    Some(cur[0])
}

/// Extract the 6-sibling XMSS authentication path and Merkle root for `leaf_idx < 64`.
pub fn hem_merkle_auth_path(
    pk_seed: HemDigest4,
    leaves: &[HemDigest4],
    leaf_idx: usize,
) -> Option<(Vec<HemDigest4>, HemDigest4)> {
    if leaves.len() != HEM_JORTS_MAX_LEAVES || leaf_idx >= HEM_JORTS_MAX_LEAVES {
        return None;
    }
    let mut path = Vec::with_capacity(HEM_JORTS_XMSS_HEIGHT);
    let mut cur = leaves.to_vec();
    let mut idx = leaf_idx;
    for lvl in 0..HEM_JORTS_XMSS_HEIGHT {
        path.push(cur[idx ^ 1]);
        let mut next = Vec::with_capacity(cur.len() / 2);
        for p in 0..(cur.len() / 2) {
            next.push(hem_merkle_node_hash(
                pk_seed,
                0,
                0,
                (lvl + 1) as u32,
                p as u32,
                cur[2 * p],
                cur[2 * p + 1],
            ));
        }
        cur = next;
        idx >>= 1;
    }
    Some((path, cur[0]))
}

/// Compute collision-free 5-limb 56-bit message representative `mu`, matching
/// `qsag_agg::sig::compute_message_mu` bit-for-bit.
#[inline]
pub fn hem_compute_message_mu(pk: &HemJortsPublicKey, msg: &[u8]) -> ([u8; 32], HemDigest5) {
    let pk_bytes = pk.to_bytes();
    let framed = crate::sponge::keccak::encode_multi_frame(&[b"QSAG.MU/v2", &pk_bytes, msg]);
    let h = poseidon2_hash32(&framed);
    (h, hem_bytes32_to_limbs56(&h))
}

/// Clear single-party `r_rand` derivation matching `qsag_agg::sig::ValidatorKeypair::derive_deterministic_r_rand`.
#[inline]
pub fn hem_derive_r_rand_clear(
    sk_prf: HemDigest4,
    pk_seed: HemDigest4,
    mu: HemDigest5,
    epoch: u64,
) -> HemDigest4 {
    let mut st = [
        sk_prf[0],
        sk_prf[1],
        sk_prf[2],
        sk_prf[3],
        pk_seed[0],
        pk_seed[1],
        pk_seed[2],
        pk_seed[3],
        Goldilocks::from_u64_reduced(HEM_DOMAIN_PRF_MSG),
        Goldilocks::from_u64_reduced(epoch),
        mu[4],
        Goldilocks::from_u64_reduced(POSEIDON2_CONST_IV),
    ];
    poseidon2_perm12(&mut st);
    for i in 0..4 {
        st[i] += mu[i];
    }
    poseidon2_perm12(&mut st);
    let out = [st[0], st[1], st[2], st[3]];
    wipe_goldilocks(&mut st);
    out
}

/// Public check digest committing to `sk_prf` (`poseidon2_compress12_ff(sk_prf, pk_seed, [HEM_DOMAIN_PRF_CHECK, 0, 0, IV])`).
#[inline]
pub fn hem_prf_check_digest_clear(sk_prf: HemDigest4, pk_seed: HemDigest4) -> HemDigest4 {
    let tweak = [
        Goldilocks::from_u64_reduced(HEM_DOMAIN_PRF_CHECK),
        Goldilocks::ZERO,
        Goldilocks::ZERO,
        Goldilocks::from_u64_reduced(POSEIDON2_CONST_IV),
    ];
    hem_poseidon2_compress12_ff(sk_prf, pk_seed, tweak)
}

/// Stateful layer-0 randomized message hash `H_msg_stateful` (`qsag_agg::sig::compute_hmsg_stateful`).
pub fn hem_compute_hmsg_stateful(
    pk_seed: HemDigest4,
    pk_root: HemDigest4,
    r_rand: HemDigest4,
    mu: HemDigest5,
    kp_idx: u32,
    tsw_ctr: u32,
) -> HemDigest5 {
    let kp_ctr = ((kp_idx as u64) << 32) | (tsw_ctr as u64);
    let mut st = [
        pk_seed[0],
        pk_seed[1],
        pk_seed[2],
        pk_seed[3],
        pk_root[0],
        pk_root[1],
        pk_root[2],
        pk_root[3],
        Goldilocks::from_u64_reduced(HEM_DOMAIN_H_MSG_STATEFUL),
        Goldilocks::from_u64_reduced(kp_ctr),
        mu[4],
        Goldilocks::from_u64_reduced(POSEIDON2_CONST_IV),
    ];
    poseidon2_perm12(&mut st);
    for i in 0..4 {
        st[i] += r_rand[i];
        st[4 + i] += mu[i];
    }
    poseidon2_perm12(&mut st);
    st[0] += Goldilocks::ONE;
    poseidon2_perm12(&mut st);
    [st[0], st[1], st[2], st[3], st[4]]
}

/// Extract 128 base-4 digits (`256` bits) from `hmsg[0..5]` requiring `< 2^63` per limb
/// (`qsag_agg::sig::extract_wots_digits_checked`).
pub fn hem_extract_wots_digits_checked(hmsg: &HemDigest5) -> Option<[u8; HEM_WOTS_CHAINS]> {
    for limb in hmsg {
        if (limb.to_canonical_u64() >> 63) != 0 {
            return None;
        }
    }
    let mut digits = [0u8; HEM_WOTS_CHAINS];
    for limb_idx in 0..4 {
        let v = hmsg[limb_idx].to_canonical_u64();
        for i in 0..31 {
            digits[31 * limb_idx + i] = ((v >> (2 * i)) & 3) as u8;
        }
    }
    let v4 = hmsg[4].to_canonical_u64();
    for i in 0..4 {
        digits[124 + i] = ((v4 >> (2 * i)) & 3) as u8;
    }
    Some(digits)
}

/// Deterministically grind `tsw_ctr` upward from `0` until `hem_extract_wots_digits_checked`
/// succeeds and the 128 base-4 digits sum to `HEM_WOTS_TARGET_SUM = 192`.
pub fn hem_grind_stateful_tsw_digits(
    pk_seed: HemDigest4,
    pk_root: HemDigest4,
    r_rand: HemDigest4,
    mu: HemDigest5,
    kp_idx: u32,
    max_grind: u32,
) -> Option<(u32, [u8; HEM_WOTS_CHAINS])> {
    let mut ctr = 0u32;
    loop {
        let hmsg = hem_compute_hmsg_stateful(pk_seed, pk_root, r_rand, mu, kp_idx, ctr);
        if let Some(digits) = hem_extract_wots_digits_checked(&hmsg) {
            let sum: usize = digits.iter().map(|&d| d as usize).sum();
            if sum == HEM_WOTS_TARGET_SUM {
                return Some((ctr, digits));
            }
        }
        if ctr >= max_grind {
            return None;
        }
        ctr = ctr.checked_add(1)?;
    }
}

/// Standalone reference verifier matching `qsag_agg::verify_individual_signature`
/// (`AggSigProfile::JortsPoseidon2`) bit-for-bit.
pub fn verify_hem_jorts_signature(
    pk: &HemJortsPublicKey,
    msg: &[u8],
    sig: &HemJortsSignature,
) -> bool {
    let kp_idx = sig.stateful_leaf_idx;
    if (kp_idx as usize) >= HEM_JORTS_MAX_LEAVES
        || sig.wots_chains.len() != HEM_WOTS_CHAINS
        || sig.merkle_path.len() != HEM_JORTS_XMSS_HEIGHT
    {
        return false;
    }
    let (_, mu) = hem_compute_message_mu(pk, msg);
    let hmsg =
        hem_compute_hmsg_stateful(pk.pk_seed, pk.pk_root, sig.r_rand, mu, kp_idx, sig.tsw_ctr);
    let Some(digits) = hem_extract_wots_digits_checked(&hmsg) else {
        return false;
    };
    let sum: usize = digits.iter().map(|&d| d as usize).sum();
    if sum != HEM_WOTS_TARGET_SUM {
        return false;
    }
    let mut endpoints = [[Goldilocks::ZERO; 4]; HEM_WOTS_CHAINS];
    for r in 0..HEM_WOTS_CHAINS {
        let mut cur = sig.wots_chains[r];
        for step in (digits[r] as u32)..(HEM_WOTS_MAX_STEP as u32) {
            cur = hem_wots_step_hash_injective(pk.pk_seed, cur, 0, 0, kp_idx, r as u32, step);
        }
        endpoints[r] = cur;
    }
    let mut node = hem_compress_wots_endpoints_sponge(pk.pk_seed, 0, 0, kp_idx, &endpoints);
    let mut idx = kp_idx;
    for (lvl, &sib) in sig
        .merkle_path
        .iter()
        .enumerate()
        .take(HEM_JORTS_XMSS_HEIGHT)
    {
        let parent_idx = idx >> 1;
        node = if (idx & 1) == 0 {
            hem_merkle_node_hash(pk.pk_seed, 0, 0, (lvl + 1) as u32, parent_idx, node, sib)
        } else {
            hem_merkle_node_hash(pk.pk_seed, 0, 0, (lvl + 1) as u32, parent_idx, sib, node)
        };
        idx = parent_idx;
    }
    node == pk.pk_root
}

/// Exact preprocessing budget `(num_pow7, num_beaver, num_a2b)` for distributed `HemJortsPoseidon2`
/// key generation with `active_leaves` active `WOTS+C` leaves (`0` Beaver triples, `0` A2B masks!).
pub fn required_hem_jorts_keygen_preprocessing_budget(
    active_leaves: usize,
) -> Result<(usize, usize, usize), Poseidon2MpcError> {
    if active_leaves == 0 || active_leaves > HEM_JORTS_MAX_LEAVES {
        return Err(Poseidon2MpcError::InvalidParams);
    }
    let perms = 2 + 1 + active_leaves * HEM_WOTS_CHAINS * HEM_WOTS_BASE_W;
    Ok((perms * POSEIDON2_SBOXES_PER_PERM, 0, 0))
}

/// Exact preprocessing budget `(num_pow7, 0, 0)` for `verify_reshared_hem_jorts_key_mpc`
/// (`7` `poseidon2_perm12`s = `826` `pow7` tuples, `0` Beaver triples, `0` A2B masks).
#[inline]
pub const fn required_hem_jorts_reshare_verify_preprocessing_budget() -> (usize, usize, usize) {
    let perms = 2 + 1 + HEM_WOTS_BASE_W;
    (perms * POSEIDON2_SBOXES_PER_PERM, 0, 0)
}

/// Exact constant preprocessing budget `(num_pow7, 0, 0)` for one `sign_hem_jorts_poseidon2_mpc_cached`
/// or `retry_hem_jorts_poseidon2_mpc_cached` signature (`324` `poseidon2_perm12`s = `38,232` `pow7`
/// tuples, `0` Beaver triples, `0` A2B masks — constant across all messages because `sum(digits) == 192`!).
#[inline]
pub const fn required_hem_jorts_sign_preprocessing_budget_cached() -> (usize, usize, usize) {
    let perms = 2 + 2 + HEM_WOTS_CHAINS + HEM_WOTS_TARGET_SUM;
    (perms * POSEIDON2_SBOXES_PER_PERM, 0, 0)
}
