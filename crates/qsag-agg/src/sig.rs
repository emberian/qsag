//! Post-quantum validator public keys, signatures (`JortsPoseidon2` and `CorduroyPoseidon2`),
//! stateful `EpochLatch` (`[P0-04]`), 5-limb 56-bit collision-free digest packing (`[P1-02]`),
//! 256-bit WOTS+C + deterministic upper-layer/FORS-root signing (`[P0-02]`, `[P0-03]`),
//! canonical `SignerBitmap`, and committee commitments.

use alloc::collections::BTreeSet;
use alloc::vec;
use alloc::vec::Vec;

use crate::field::Goldilocks;
use crate::sponge::{
    POSEIDON2_CONST_IV, cshake256_32, encode_multi_frame, poseidon2_compress12_ff,
    poseidon2_hash32, poseidon2_perm12,
};

/// Number of base-4 `WOTS+C` chains ($\ell_1 = 128 \implies 256$-bit full message security, `[P0-02]`).
pub const WOTS_CHAINS: usize = 128;
/// Winternitz base $w = 4$ (`0..=3` steps per chain).
pub const WOTS_BASE_W: usize = 4;
/// Maximum step index per chain (`w - 1 = 3`).
pub const WOTS_MAX_STEP: usize = WOTS_BASE_W - 1;
/// Target-Sum Winternitz (`TSW`) constant digit sum ($T_{\text{sum}} = 192 = 128 \times 1.5$ exact mean),
/// fixing total verifier WOTS+C steps per layer to $128 \times 3 - 192 = 192$.
pub const WOTS_TARGET_SUM: usize = 192;
/// Exact constant number of verifier `Poseidon2` WOTS+C step transitions per layer (`192`).
pub const WOTS_VERIFIER_STEPS: usize = WOTS_CHAINS * WOTS_MAX_STEP - WOTS_TARGET_SUM;

/// Stateful `JortsPoseidon2` XMSS subtree height (`2^6 = 64` epochs per validator keypair).
pub const JORTS_XMSS_HEIGHT: usize = 6;

/// Stateless `CorduroyPoseidon2` FORS tree count ($k = 32$, `[P0-03]`).
pub const FORS_TREES: usize = 32;
/// Stateless `CorduroyPoseidon2` FORS tree height ($a = 8 \implies k \cdot a = 256$-bit FORS, `[P0-03]`).
pub const FORS_HEIGHT: usize = 8;
/// Stateless `CorduroyPoseidon2` hypertree layers ($d = 16$).
pub const CORDUROY_NUM_LAYERS: usize = 16;
/// Stateless `CorduroyPoseidon2` subtree height per layer ($h' = 4 \implies d \cdot h' = 64$-bit leaf space).
pub const CORDUROY_SUBTREE_HEIGHT: usize = 4;
/// Hard per-key stateless signature budget ($Q_{\max} = 2^{20}$ signatures per `CorduroyPoseidon2` keypair):
/// Over $2^{64}$ hypertree leaves, $\Pr[\exists\text{ leaf hit } \ge 2\text{ times}] < \binom{2^{20}}{2}/2^{64} < 2^{-25}$
/// and $\Pr[\exists\text{ leaf hit } \ge 3\text{ times}] < \binom{2^{20}}{3}/2^{128} < 2^{-69}$, so
/// $(k=32, a=8)$ FORS subset-resilience satisfies $\epsilon_{\text{FORS}}(Q_{\max}) < 2^{-256} + 2^{-25}\cdot 2^{-224} < 2^{-249}$
/// classical ($> 128$-bit post-quantum Grover security with $> 20$ bits of multi-hit safety margin!).
pub const CORDUROY_MAX_STATELESS_SIGS_PER_KEY: u64 = 1u64 << 20;

// Domain tags encoded as Goldilocks constants for algebraic `Poseidon2` tweakable hashing.
pub const DOMAIN_PRF_WOTS: u64 = 0x5153_4147_5750_5246; // "QSAGWPRF"
pub const DOMAIN_WOTS_STEP: u64 = 0x5153_4147_5753_5450; // "QSAGWSTP"
pub const DOMAIN_WOTS_PK: u64 = 0x5153_4147_5750_4B31; // "QSAGWPK1"
pub const DOMAIN_MERKLE_NODE: u64 = 0x5153_4147_4D52_4B4C; // "QSAGMRKL"
pub const DOMAIN_H_MSG_STATEFUL: u64 = 0x5153_4147_484D_5331; // "QSAGHMS1"
pub const DOMAIN_H_MSG_DET_TREE: u64 = 0x5153_4147_4844_5452; // "QSAGHDTR"
pub const DOMAIN_H_MSG_STATELESS: u64 = 0x5153_4147_4853_544C; // "QSAGHSTL"
pub const DOMAIN_PRF_MSG: u64 = 0x5153_4147_5052_464D; // "QSAGPRFM"
pub const DOMAIN_FORS_PRF: u64 = 0x5153_4147_4650_5246; // "QSAGFPRF"
pub const DOMAIN_FORS_LEAF: u64 = 0x5153_4147_464C_4546; // "QSAGFLEF"
pub const DOMAIN_FORS_NODE: u64 = 0x5153_4147_464E_4F44; // "QSAGFNOD"
pub const DOMAIN_FORS_ROOTS: u64 = 0x5153_4147_4652_5453; // "QSAGFRTS"

/// Post-quantum hash-signature profile supported by `qsag-agg`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u8)]
pub enum AggSigProfile {
    /// Stateful `Jorts-Poseidon2` (`256`-bit `WOTS+C` + height-6 XMSS tree, `4,328`B raw signature).
    JortsPoseidon2 = 1,
    /// Stateless `Corduroy-Poseidon2` (`256`-bit `FORS` $k=32,a=8$ + $d=16,h'=4$ `256`-bit `WOTS+C` hypertree, `76,896`B raw signature).
    CorduroyPoseidon2 = 2,
}

impl AggSigProfile {
    pub fn from_u8(b: u8) -> Option<Self> {
        match b {
            1 => Some(Self::JortsPoseidon2),
            2 => Some(Self::CorduroyPoseidon2),
            _ => None,
        }
    }

    /// Exact raw byte length of one serialized individual signature under this profile.
    pub const fn raw_signature_bytes(self) -> usize {
        match self {
            Self::JortsPoseidon2 => {
                // 32B r_rand + 4B tsw_ctr + 4B leaf_idx + 128*32B WOTS + 6*32B XMSS = 4,328 bytes
                32 + 4 + 4 + WOTS_CHAINS * 32 + JORTS_XMSS_HEIGHT * 32
            }
            Self::CorduroyPoseidon2 => {
                // 32B r_rand + 32*(1+8)*32B FORS + 16*(4B tsw_ctr + 128*32B WOTS + 4*32B Merkle) = 76,896 bytes
                32 + FORS_TREES * (1 + FORS_HEIGHT) * 32
                    + CORDUROY_NUM_LAYERS * (4 + WOTS_CHAINS * 32 + CORDUROY_SUBTREE_HEIGHT * 32)
            }
        }
    }
}

/// Errors returned during stateful/stateless signing or batch pre-validation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SigError {
    ProfileMismatch,
    EpochOutOfBounds,
    EpochMonotonicityViolation,
    EpochReuseDifferentMessage,
    WalPersistenceFailed,
    StatelessBudgetExhausted,
    SigningCounterExhausted,
}

/// 4-limb algebraic `Goldilocks` digest (`32` canonical bytes).
pub type Digest4 = [Goldilocks; 4];

/// 5-limb 56-bit injective `Goldilocks` packing of an arbitrary 32-byte digest (`[P1-02]`: `0` mod-`p` collisions!).
pub type Digest5 = [Goldilocks; 5];

/// Bijectively pack 32 raw bytes into 5 canonical `Goldilocks` limbs (`4 × 56` bits + `1 × 32` bits).
#[inline]
pub fn bytes32_to_limbs56(bytes: &[u8; 32]) -> Digest5 {
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

/// Inverse of `bytes32_to_limbs56`, enforcing canonical limb bit-widths (`< 2^56` and `< 2^32`).
#[inline]
pub fn limbs56_to_bytes32_canonical(d: &Digest5) -> Option<[u8; 32]> {
    let mut out = [0u8; 32];
    for i in 0..4 {
        let v = d[i].to_canonical_u64();
        if (v >> 56) != 0 {
            return None;
        }
        let b = v.to_le_bytes();
        out[7 * i..7 * (i + 1)].copy_from_slice(&b[0..7]);
    }
    let v4 = d[4].to_canonical_u64();
    if (v4 >> 32) != 0 {
        return None;
    }
    out[28..32].copy_from_slice(&(v4 as u32).to_le_bytes());
    Some(out)
}

#[inline]
pub fn digest4_to_bytes(d: &Digest4) -> [u8; 32] {
    let mut out = [0u8; 32];
    for i in 0..4 {
        out[8 * i..8 * (i + 1)].copy_from_slice(&d[i].to_le_bytes());
    }
    out
}

#[inline]
pub fn digest4_from_bytes_canonical(bytes: &[u8; 32]) -> Option<Digest4> {
    let mut out = [Goldilocks::ZERO; 4];
    for i in 0..4 {
        let mut limb = [0u8; 8];
        limb.copy_from_slice(&bytes[8 * i..8 * (i + 1)]);
        out[i] = Goldilocks::from_le_bytes_canonical(limb)?;
    }
    Some(out)
}

/// Validator public key (`65` bytes wire: 1B profile + 32B `pk_seed` + 32B `pk_root`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ValidatorPublicKey {
    pub profile: AggSigProfile,
    pub pk_seed: Digest4,
    pub pk_root: Digest4,
}

impl ValidatorPublicKey {
    pub fn to_bytes(&self) -> [u8; 65] {
        let mut out = [0u8; 65];
        out[0] = self.profile as u8;
        out[1..33].copy_from_slice(&digest4_to_bytes(&self.pk_seed));
        out[33..65].copy_from_slice(&digest4_to_bytes(&self.pk_root));
        out
    }

    pub fn from_bytes_canonical(bytes: &[u8; 65]) -> Option<Self> {
        let profile = AggSigProfile::from_u8(bytes[0])?;
        let mut s = [0u8; 32];
        let mut r = [0u8; 32];
        s.copy_from_slice(&bytes[1..33]);
        r.copy_from_slice(&bytes[33..65]);
        Some(Self {
            profile,
            pk_seed: digest4_from_bytes_canonical(&s)?,
            pk_root: digest4_from_bytes_canonical(&r)?,
        })
    }
}

/// FORS tree opening for stateless `CorduroyPoseidon2` ($a = 8$).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ForsOpening {
    pub secret_val: Digest4,
    pub auth_path: [Digest4; FORS_HEIGHT],
}

/// One hypertree layer signature (`WOTS+C` chains + `tsw_ctr` + subtree Merkle path).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HypertreeLayerSig {
    pub tsw_ctr: u32,
    pub wots_chains: Vec<Digest4>,
    pub merkle_path: Vec<Digest4>,
}

/// Individual validator signature (`4,328`B for `JortsPoseidon2`, `76,896`B for `CorduroyPoseidon2`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ValidatorSignature {
    pub profile: AggSigProfile,
    pub r_rand: Digest4,
    /// Stateful `JortsPoseidon2` epoch leaf index (`0` in stateless `CorduroyPoseidon2`, where leaf is XOF-derived!).
    pub stateful_leaf_idx: u32,
    pub fors_openings: Vec<ForsOpening>,
    pub layers: Vec<HypertreeLayerSig>,
}

impl ValidatorSignature {
    /// Decode exactly one signature, rejecting non-canonical field limbs and trailing bytes.
    pub fn from_bytes_canonical(
        profile: AggSigProfile,
        bytes: &[u8],
    ) -> Result<Self, crate::AggError> {
        let bad = crate::AggError::MalformedWireBytes;
        if bytes.len() != profile.raw_signature_bytes() {
            return Err(bad);
        }
        let mut pos = 0;
        fn digest(bytes: &[u8], pos: &mut usize) -> Option<Digest4> {
            let mut out = [Goldilocks::ZERO; 4];
            for limb in &mut out {
                let raw = bytes.get(*pos..*pos + 8)?;
                *limb = Goldilocks::from_canonical_u64(u64::from_le_bytes(raw.try_into().ok()?))?;
                *pos += 8;
            }
            Some(out)
        }
        fn word(bytes: &[u8], pos: &mut usize) -> Option<u32> {
            let out = u32::from_le_bytes(bytes.get(*pos..*pos + 4)?.try_into().ok()?);
            *pos += 4;
            Some(out)
        }
        let r_rand = digest(bytes, &mut pos).ok_or(bad)?;
        let mut stateful_leaf_idx = 0;
        let mut fors_openings = Vec::new();
        let (layers_count, height) = match profile {
            AggSigProfile::JortsPoseidon2 => {
                stateful_leaf_idx = word(bytes, &mut pos).ok_or(bad)?;
                if stateful_leaf_idx >= 1 << JORTS_XMSS_HEIGHT {
                    return Err(bad);
                }
                (1, JORTS_XMSS_HEIGHT)
            }
            AggSigProfile::CorduroyPoseidon2 => {
                for _ in 0..FORS_TREES {
                    let secret_val = digest(bytes, &mut pos).ok_or(bad)?;
                    let mut auth_path = [[Goldilocks::ZERO; 4]; FORS_HEIGHT];
                    for d in &mut auth_path {
                        *d = digest(bytes, &mut pos).ok_or(bad)?;
                    }
                    fors_openings.push(ForsOpening {
                        secret_val,
                        auth_path,
                    });
                }
                (CORDUROY_NUM_LAYERS, CORDUROY_SUBTREE_HEIGHT)
            }
        };
        let mut layers = Vec::with_capacity(layers_count);
        for _ in 0..layers_count {
            let tsw_ctr = word(bytes, &mut pos).ok_or(bad)?;
            let mut wots_chains = Vec::with_capacity(WOTS_CHAINS);
            for _ in 0..WOTS_CHAINS {
                wots_chains.push(digest(bytes, &mut pos).ok_or(bad)?);
            }
            let mut merkle_path = Vec::with_capacity(height);
            for _ in 0..height {
                merkle_path.push(digest(bytes, &mut pos).ok_or(bad)?);
            }
            layers.push(HypertreeLayerSig {
                tsw_ctr,
                wots_chains,
                merkle_path,
            });
        }
        if pos != bytes.len() {
            return Err(bad);
        }
        Ok(Self {
            profile,
            r_rand,
            stateful_leaf_idx,
            fors_openings,
            layers,
        })
    }

    /// Serialize the raw individual signature to canonical bytes.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(self.profile.raw_signature_bytes());
        out.extend_from_slice(&digest4_to_bytes(&self.r_rand));
        if self.profile == AggSigProfile::JortsPoseidon2 {
            out.extend_from_slice(&self.stateful_leaf_idx.to_le_bytes());
        } else {
            for op in &self.fors_openings {
                out.extend_from_slice(&digest4_to_bytes(&op.secret_val));
                for sib in &op.auth_path {
                    out.extend_from_slice(&digest4_to_bytes(sib));
                }
            }
        }
        for layer in &self.layers {
            out.extend_from_slice(&layer.tsw_ctr.to_le_bytes());
            for c in &layer.wots_chains {
                out.extend_from_slice(&digest4_to_bytes(c));
            }
            for sib in &layer.merkle_path {
                out.extend_from_slice(&digest4_to_bytes(sib));
            }
        }
        out
    }
}

// ============================================================================
// Algebraic `Poseidon2` Tweakable Hash & WOTS+C / XMSS / FORS Operations
// ============================================================================

/// Compute collision-free 5-limb 56-bit message representative
/// $\mu = \text{bytes32\_to\_limbs56}(H_{\text{pre}}(\text{pk\_bytes}, \text{msg}))$ (`[P1-02]`).
#[inline]
pub fn compute_message_mu(pk: &ValidatorPublicKey, msg: &[u8]) -> ([u8; 32], Digest5) {
    let pk_bytes = pk.to_bytes();
    if msg.len() < 128 {
        // Zero-allocation stack fast-path matching `encode_multi_frame(&[b"QSAG.MU/v2", &pk_bytes, msg])`:
        let mut buf = [0u8; 207];
        buf[0] = 3;
        buf[1] = 10;
        buf[2..12].copy_from_slice(b"QSAG.MU/v2");
        buf[12] = 65;
        buf[13..78].copy_from_slice(&pk_bytes);
        buf[78] = msg.len() as u8;
        let end = 79 + msg.len();
        buf[79..end].copy_from_slice(msg);
        let h = poseidon2_hash32(&buf[..end]);
        return (h, bytes32_to_limbs56(&h));
    }
    let framed = encode_multi_frame(&[b"QSAG.MU/v2", &pk_bytes, msg]);
    let h = poseidon2_hash32(&framed);
    (h, bytes32_to_limbs56(&h))
}

/// Bijective domain-separated address packing for `WOTS+C` steps (`< 2^62` canonical `Goldilocks` limb):
/// `packed = (layer << 44) | (kp_idx << 16) | (chain_idx << 4) | step_idx`, paired with `DOMAIN_WOTS_STEP`
/// in its own dedicated limb and lossless 64-bit `(tree_lo32, tree_hi32)` in limbs `2..4` (`[P1-04]`).
#[inline]
pub fn pack_wots_addr_limb(layer: u32, kp_idx: u32, chain_idx: u32, step_idx: u32) -> Goldilocks {
    debug_assert!(layer < 64 && kp_idx < (1 << 20) && chain_idx < 256 && step_idx < 16);
    let packed = ((layer as u64) << 44)
        | ((kp_idx as u64) << 16)
        | ((chain_idx as u64) << 4)
        | (step_idx as u64);
    Goldilocks::from_u64_reduced(packed)
}

#[inline]
pub fn wots_step_hash_injective(
    pk_seed: Digest4,
    cur: Digest4,
    layer: u32,
    tree_idx: u64,
    kp_idx: u32,
    chain_idx: u32,
    step_idx: u32,
) -> Digest4 {
    let tweak = [
        Goldilocks::from_u64_reduced(DOMAIN_WOTS_STEP),
        pack_wots_addr_limb(layer, kp_idx, chain_idx, step_idx),
        Goldilocks::from_u64_reduced(tree_idx & 0xFFFF_FFFF),
        Goldilocks::from_u64_reduced(tree_idx >> 32),
    ];
    poseidon2_compress12_ff(cur, pk_seed, tweak)
}

/// Compress all 128 WOTS+C chain endpoints (`128 × 4 = 512` limbs) into a 4-limb `wots_pk`
/// via a 256-bit-capacity (`4` capacity limbs, `8` rate limbs) Width-12 `Poseidon2` sponge (`66` perms):
/// - Init block: `st = perm12([pk_seed[0..4], [layer_kp, tree_lo, tree_hi, 128], [DOMAIN_WOTS_PK, 0, 0, IV]])`
/// - 64 pair blocks (`p = 0..64`): `st[0..4] += ep[2p]; st[4..8] += ep[2p+1]; st = perm12(st)`
/// - Final domain-pad squeeze: `st[0] += 1; st = perm12(st); out = st[0..4]`.
pub fn compress_wots_endpoints_sponge(
    pk_seed: Digest4,
    layer: u32,
    tree_idx: u64,
    kp_idx: u32,
    endpoints: &[Digest4; WOTS_CHAINS],
) -> Digest4 {
    let layer_kp = ((layer as u64) << 32) | (kp_idx as u64);
    let mut st = [
        pk_seed[0],
        pk_seed[1],
        pk_seed[2],
        pk_seed[3],
        Goldilocks::from_u64_reduced(layer_kp),
        Goldilocks::from_u64_reduced(tree_idx & 0xFFFF_FFFF),
        Goldilocks::from_u64_reduced(tree_idx >> 32),
        Goldilocks::from_u64_reduced(WOTS_CHAINS as u64),
        Goldilocks::from_u64_reduced(DOMAIN_WOTS_PK),
        Goldilocks::ZERO,
        Goldilocks::ZERO,
        Goldilocks::from_u64_reduced(POSEIDON2_CONST_IV),
    ];
    poseidon2_perm12(&mut st);
    for pair_idx in 0..(WOTS_CHAINS / 2) {
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

/// Position of a Merkle node: hypertree `layer`, 64-bit `tree_idx`, `level` above the leaves, and
/// `node_idx` within that level.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MerkleNodeAddr {
    pub layer: u32,
    pub tree_idx: u64,
    pub level: u32,
    pub node_idx: u32,
}

/// 2-Block Full-`pk_seed[0..4]` Binary Merkle Node Sponge (`[P1-02]` & `[P1-04]`):
/// Binds ALL 256 bits of `pk_seed`, `layer`, 64-bit `tree_idx`, `level`, `node_idx`, `left`, and `right`!
#[inline]
pub fn merkle_node_hash(
    domain_tag: u64,
    pk_seed: Digest4,
    addr: MerkleNodeAddr,
    left: Digest4,
    right: Digest4,
) -> Digest4 {
    let MerkleNodeAddr {
        layer,
        tree_idx,
        level,
        node_idx,
    } = addr;
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
        Goldilocks::from_u64_reduced(domain_tag),
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

/// Stateful layer-0 randomized message hash `H_msg_stateful(pk_seed, pk_root, r_rand, mu[0..5], kp_idx, tsw_ctr) -> Digest5`:
/// Binds `kp_idx` (`[P0-02]` anti-multi-target) and all 5 injective 56-bit limbs of `mu` (`[P1-02]`),
/// outputting 5 limbs for full 256-bit WOTS+C (`128` base-4 digits)!
pub fn compute_hmsg_stateful(
    pk_seed: Digest4,
    pk_root: Digest4,
    r_rand: Digest4,
    mu: Digest5,
    kp_idx: u32,
    tsw_ctr: u32,
) -> Digest5 {
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
        Goldilocks::from_u64_reduced(DOMAIN_H_MSG_STATEFUL),
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

/// Deterministic `r_rand`-FREE & `mu`-FREE WOTS+C hash for signing `fors_pk` (layer 0 of stateless `Corduroy`)
/// and child `subtree_root` (upper layers `1..d-1`) (`[P0-02]` & `[P0-03]`):
/// Reusing the same `(layer, tree_idx, kp_idx)` on identical `child_or_fors_root` ALWAYS yields the IDENTICAL codeword!
pub fn compute_hmsg_det_tree(
    pk_seed: Digest4,
    pk_root: Digest4,
    layer: u32,
    tree_idx: u64,
    kp_idx: u32,
    tsw_ctr: u32,
    child_or_fors_root: Digest4,
) -> Digest5 {
    let layer_kp = ((layer as u64) << 32) | (kp_idx as u64);
    let mut st = [
        pk_seed[0],
        pk_seed[1],
        pk_seed[2],
        pk_seed[3],
        pk_root[0],
        pk_root[1],
        pk_root[2],
        pk_root[3],
        Goldilocks::from_u64_reduced(DOMAIN_H_MSG_DET_TREE),
        Goldilocks::from_u64_reduced(layer_kp),
        Goldilocks::from_u64_reduced(tree_idx & 0xFFFF_FFFF),
        Goldilocks::from_u64_reduced(tree_idx >> 32),
    ];
    poseidon2_perm12(&mut st);
    for i in 0..4 {
        st[i] += child_or_fors_root[i];
    }
    st[4] += Goldilocks::from_u64_reduced(tsw_ctr as u64);
    st[5] += Goldilocks::ONE;
    poseidon2_perm12(&mut st);
    [st[0], st[1], st[2], st[3], st[4]]
}

/// Extract 128 base-4 digits (`256` full bits!) from `hmsg[0..5]`, strictly requiring `hmsg[0..5] < 2^63`
/// so that $\sum_{i=0}^{30} d_i 4^i + b_{62} 2^{62} \le 2^{63} - 1 < p$ has ZERO modular wrap-around in $\mathbb{F}_p$!
/// Layout: `31` digits from each of `hmsg[0..4]` (`124` digits = `248` bits) + `4` digits from `hmsg[4]` (`8` bits) = `128` digits (`256` bits).
pub fn extract_wots_digits_checked(hmsg: &Digest5) -> Option<[u8; WOTS_CHAINS]> {
    for limb in hmsg {
        if (limb.to_canonical_u64() >> 63) != 0 {
            return None;
        }
    }
    let mut digits = [0u8; WOTS_CHAINS];
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

/// Stateless `CorduroyPoseidon2` XOF `H_msg_stateless(r_rand, pk_seed, pk_root, mu)` (`[P0-03]`):
/// Squeezes **100% disjoint** wrap-around-free `< 2^63` limbs for:
/// - `FORS_TREES = 32` indices of `8` bits (`256` bits total: `7` indices/limb across limbs `0..4` = 28 + `4` indices in limb `4` = 32),
/// - `leaf_global_idx : u64` (`64` bits: low 32 bits from limb `5`, high 32 bits from limb `6`), NEVER attacker-chosen!
pub fn derive_stateless_fors_and_leaf_checked(
    pk_seed: Digest4,
    pk_root: Digest4,
    r_rand: Digest4,
    mu: Digest5,
) -> Option<([usize; FORS_TREES], u64, [Goldilocks; 7])> {
    let mut st = [
        pk_seed[0],
        pk_seed[1],
        pk_seed[2],
        pk_seed[3],
        pk_root[0],
        pk_root[1],
        pk_root[2],
        pk_root[3],
        Goldilocks::from_u64_reduced(DOMAIN_H_MSG_STATELESS),
        mu[4],
        Goldilocks::ZERO,
        Goldilocks::from_u64_reduced(POSEIDON2_CONST_IV),
    ];
    poseidon2_perm12(&mut st);
    for i in 0..4 {
        st[i] += r_rand[i];
        st[4 + i] += mu[i];
    }
    poseidon2_perm12(&mut st);
    let mut sq = [Goldilocks::ZERO; 7];
    sq.copy_from_slice(&st[0..7]);
    for limb in &sq {
        if (limb.to_canonical_u64() >> 63) != 0 {
            return None;
        }
    }
    let mut fors_idxs = [0usize; FORS_TREES];
    for l in 0..4 {
        let v = sq[l].to_canonical_u64();
        for sub in 0..7 {
            fors_idxs[7 * l + sub] = ((v >> (8 * sub)) & 0xFF) as usize;
        }
    }
    let v4 = sq[4].to_canonical_u64();
    for sub in 0..4 {
        fors_idxs[28 + sub] = ((v4 >> (8 * sub)) & 0xFF) as usize;
    }
    let leaf_lo = sq[5].to_canonical_u64() & 0xFFFF_FFFF;
    let leaf_hi = sq[6].to_canonical_u64() & 0xFFFF_FFFF;
    let leaf_global_idx = leaf_lo | (leaf_hi << 32);
    Some((fors_idxs, leaf_global_idx, sq))
}

/// Recover the 256-bit `FORS` public key from `32` height-8 `ForsOpening`s in stateless `CorduroyPoseidon2`.
pub fn recover_fors_pk(
    pk_seed: Digest4,
    leaf_global_idx: u64,
    indices: &[usize; FORS_TREES],
    openings: &[ForsOpening],
) -> Option<Digest4> {
    if openings.len() != FORS_TREES {
        return None;
    }
    let kp_idx = (leaf_global_idx & ((1u64 << CORDUROY_SUBTREE_HEIGHT) - 1)) as u32;
    let tree_idx = leaf_global_idx >> CORDUROY_SUBTREE_HEIGHT;
    let mut roots = [[Goldilocks::ZERO; 4]; FORS_TREES];

    for j in 0..FORS_TREES {
        let idx_j = indices[j];
        if idx_j >= (1 << FORS_HEIGHT) {
            return None;
        }
        let global_fors_leaf = ((j as u64) << FORS_HEIGHT) | (idx_j as u64);
        let leaf_tweak = [
            Goldilocks::from_u64_reduced(DOMAIN_FORS_LEAF),
            Goldilocks::from_u64_reduced(((kp_idx as u64) << 24) | global_fors_leaf),
            Goldilocks::from_u64_reduced(tree_idx & 0xFFFF_FFFF),
            Goldilocks::from_u64_reduced(tree_idx >> 32),
        ];
        let mut node = poseidon2_compress12_ff(openings[j].secret_val, pk_seed, leaf_tweak);
        let mut cur_idx = idx_j as u32;
        for (lvl, &sib) in openings[j].auth_path.iter().enumerate().take(FORS_HEIGHT) {
            let parent_idx = cur_idx >> 1;
            let addr_node = ((j as u32) << (FORS_HEIGHT - 1 - lvl)) + parent_idx;
            node = if (cur_idx & 1) == 0 {
                merkle_node_hash(
                    DOMAIN_FORS_NODE,
                    pk_seed,
                    MerkleNodeAddr {
                        layer: 0,
                        tree_idx,
                        level: (lvl + 1) as u32,
                        node_idx: (kp_idx << 16) | addr_node,
                    },
                    node,
                    sib,
                )
            } else {
                merkle_node_hash(
                    DOMAIN_FORS_NODE,
                    pk_seed,
                    MerkleNodeAddr {
                        layer: 0,
                        tree_idx,
                        level: (lvl + 1) as u32,
                        node_idx: (kp_idx << 16) | addr_node,
                    },
                    sib,
                    node,
                )
            };
            cur_idx = parent_idx;
        }
        roots[j] = node;
    }

    // Compress all 32 FORS roots + `pk_seed` via rate-8 Width-12 `Poseidon2` sponge (`1 + 16 + 1 = 18` perms).
    let mut st = [
        pk_seed[0],
        pk_seed[1],
        pk_seed[2],
        pk_seed[3],
        Goldilocks::from_u64_reduced(kp_idx as u64),
        Goldilocks::from_u64_reduced(tree_idx & 0xFFFF_FFFF),
        Goldilocks::from_u64_reduced(tree_idx >> 32),
        Goldilocks::from_u64_reduced(FORS_TREES as u64),
        Goldilocks::from_u64_reduced(DOMAIN_FORS_ROOTS),
        Goldilocks::ZERO,
        Goldilocks::ZERO,
        Goldilocks::from_u64_reduced(POSEIDON2_CONST_IV),
    ];
    poseidon2_perm12(&mut st);
    for pair in 0..(FORS_TREES / 2) {
        for i in 0..4 {
            st[i] += roots[2 * pair][i];
            st[4 + i] += roots[2 * pair + 1][i];
        }
        poseidon2_perm12(&mut st);
    }
    st[0] += Goldilocks::ONE;
    poseidon2_perm12(&mut st);
    Some([st[0], st[1], st[2], st[3]])
}

/// Standalone reference verifier for a single `ValidatorSignature` (`JortsPoseidon2` or `CorduroyPoseidon2`).
pub fn verify_individual_signature(
    pk: &ValidatorPublicKey,
    msg: &[u8],
    sig: &ValidatorSignature,
) -> bool {
    if pk.profile != sig.profile {
        return false;
    }
    let (_, mu) = compute_message_mu(pk, msg);

    match pk.profile {
        AggSigProfile::JortsPoseidon2 => {
            if !sig.fors_openings.is_empty() || sig.layers.len() != 1 {
                return false;
            }
            let kp_idx = sig.stateful_leaf_idx;
            if (kp_idx as usize) >= (1usize << JORTS_XMSS_HEIGHT) {
                return false;
            }
            let layer_sig = &sig.layers[0];
            if layer_sig.wots_chains.len() != WOTS_CHAINS
                || layer_sig.merkle_path.len() != JORTS_XMSS_HEIGHT
            {
                return false;
            }
            let hmsg = compute_hmsg_stateful(
                pk.pk_seed,
                pk.pk_root,
                sig.r_rand,
                mu,
                kp_idx,
                layer_sig.tsw_ctr,
            );
            let Some(digits) = extract_wots_digits_checked(&hmsg) else {
                return false;
            };
            let sum: usize = digits.iter().map(|&d| d as usize).sum();
            if sum != WOTS_TARGET_SUM {
                return false;
            }
            let mut endpoints = [[Goldilocks::ZERO; 4]; WOTS_CHAINS];
            for r in 0..WOTS_CHAINS {
                let mut cur = layer_sig.wots_chains[r];
                for step in (digits[r] as u32)..(WOTS_MAX_STEP as u32) {
                    cur = wots_step_hash_injective(pk.pk_seed, cur, 0, 0, kp_idx, r as u32, step);
                }
                endpoints[r] = cur;
            }
            let mut node = compress_wots_endpoints_sponge(pk.pk_seed, 0, 0, kp_idx, &endpoints);
            let mut idx = kp_idx;
            for (lvl, &sib) in layer_sig
                .merkle_path
                .iter()
                .enumerate()
                .take(JORTS_XMSS_HEIGHT)
            {
                let parent_idx = idx >> 1;
                node = if (idx & 1) == 0 {
                    merkle_node_hash(
                        DOMAIN_MERKLE_NODE,
                        pk.pk_seed,
                        MerkleNodeAddr {
                            layer: 0,
                            tree_idx: 0,
                            level: (lvl + 1) as u32,
                            node_idx: parent_idx,
                        },
                        node,
                        sib,
                    )
                } else {
                    merkle_node_hash(
                        DOMAIN_MERKLE_NODE,
                        pk.pk_seed,
                        MerkleNodeAddr {
                            layer: 0,
                            tree_idx: 0,
                            level: (lvl + 1) as u32,
                            node_idx: parent_idx,
                        },
                        sib,
                        node,
                    )
                };
                idx = parent_idx;
            }
            node == pk.pk_root
        }
        AggSigProfile::CorduroyPoseidon2 => {
            if sig.stateful_leaf_idx != 0 || sig.layers.len() != CORDUROY_NUM_LAYERS {
                return false;
            }
            let Some((fors_idxs, leaf_global_idx, _)) =
                derive_stateless_fors_and_leaf_checked(pk.pk_seed, pk.pk_root, sig.r_rand, mu)
            else {
                return false;
            };
            let Some(mut cur_root) =
                recover_fors_pk(pk.pk_seed, leaf_global_idx, &fors_idxs, &sig.fors_openings)
            else {
                return false;
            };
            let mut idx_cursor = leaf_global_idx;
            for (layer, lsig) in sig.layers.iter().enumerate() {
                if lsig.wots_chains.len() != WOTS_CHAINS
                    || lsig.merkle_path.len() != CORDUROY_SUBTREE_HEIGHT
                {
                    return false;
                }
                let kp_idx = (idx_cursor & ((1u64 << CORDUROY_SUBTREE_HEIGHT) - 1)) as u32;
                let tree_idx = idx_cursor >> CORDUROY_SUBTREE_HEIGHT;
                let hmsg = compute_hmsg_det_tree(
                    pk.pk_seed,
                    pk.pk_root,
                    layer as u32,
                    tree_idx,
                    kp_idx,
                    lsig.tsw_ctr,
                    cur_root,
                );
                let Some(digits) = extract_wots_digits_checked(&hmsg) else {
                    return false;
                };
                let sum: usize = digits.iter().map(|&d| d as usize).sum();
                if sum != WOTS_TARGET_SUM {
                    return false;
                }
                let mut endpoints = [[Goldilocks::ZERO; 4]; WOTS_CHAINS];
                for r in 0..WOTS_CHAINS {
                    let mut cur = lsig.wots_chains[r];
                    for step in (digits[r] as u32)..(WOTS_MAX_STEP as u32) {
                        cur = wots_step_hash_injective(
                            pk.pk_seed,
                            cur,
                            layer as u32,
                            tree_idx,
                            kp_idx,
                            r as u32,
                            step,
                        );
                    }
                    endpoints[r] = cur;
                }
                let mut node = compress_wots_endpoints_sponge(
                    pk.pk_seed,
                    layer as u32,
                    tree_idx,
                    kp_idx,
                    &endpoints,
                );
                let mut sub_idx = kp_idx;
                for (lvl, &sib) in lsig
                    .merkle_path
                    .iter()
                    .enumerate()
                    .take(CORDUROY_SUBTREE_HEIGHT)
                {
                    let parent_idx = sub_idx >> 1;
                    node = if (sub_idx & 1) == 0 {
                        merkle_node_hash(
                            DOMAIN_MERKLE_NODE,
                            pk.pk_seed,
                            MerkleNodeAddr {
                                layer: layer as u32,
                                tree_idx,
                                level: (lvl + 1) as u32,
                                node_idx: parent_idx,
                            },
                            node,
                            sib,
                        )
                    } else {
                        merkle_node_hash(
                            DOMAIN_MERKLE_NODE,
                            pk.pk_seed,
                            MerkleNodeAddr {
                                layer: layer as u32,
                                tree_idx,
                                level: (lvl + 1) as u32,
                                node_idx: parent_idx,
                            },
                            sib,
                            node,
                        )
                    };
                    sub_idx = parent_idx;
                }
                cur_root = node;
                idx_cursor = tree_idx;
            }
            cur_root == pk.pk_root
        }
    }
}

/// Verify a batch of individual signatures while strictly rejecting duplicate `(pk, stateful_leaf_idx)`
/// pairs in stateful `JortsPoseidon2` (`[P0-04]` anti-replay / anti-equivocation).
pub fn verify_signature_batch(items: &[(ValidatorPublicKey, &[u8], ValidatorSignature)]) -> bool {
    let mut seen_stateful = BTreeSet::new();
    for (pk, msg, sig) in items {
        if pk.profile == AggSigProfile::JortsPoseidon2
            && !seen_stateful.insert((*pk, sig.stateful_leaf_idx))
        {
            return false;
        }
        if !verify_individual_signature(pk, msg, sig) {
            return false;
        }
    }
    true
}

/// Durable write-ahead log (`WAL`) persistence sink for `StatefulEpochLatch` (`[P0-04]`).
///
/// Must atomically persist `(pk_root, next_unused_epoch, epoch, mu_bytes)` to stable storage
/// (`fsync` / NVRAM) **strictly BEFORE** `ValidatorKeypair` computes or releases any WOTS+C chains!
pub trait EpochWalSink {
    /// Recover authenticated state for this key; implementations must reject a wrong key.
    fn recovered_state(&self, pk_root: &[u8; 32]) -> Result<Option<WalEpochState>, SigError>;

    fn persist_latched_epoch(
        &mut self,
        pk_root: &[u8; 32],
        next_unused_epoch: u32,
        latched_epoch: u32,
        mu_bytes: &[u8; 32],
    ) -> Result<(), SigError>;
}

/// Latched signer state recovered from a WAL: `(next_epoch, latched_epoch, latched_mu)`.
pub type WalEpochState = (u32, u32, [u8; 32]);

/// Real `fsync`-backed durable WAL implementation for `std` validator deployments (`[P0-04]`).
#[cfg(feature = "std")]
pub struct FsWalEpochSink {
    record: qsag_asm::durable::LockedRecord,
    mac_key: [u8; 32],
    current: [u8; 112],
}

#[cfg(feature = "std")]
impl Drop for FsWalEpochSink {
    fn drop(&mut self) {
        qsag_asm::volatile_fill(&mut self.mac_key, 0);
    }
}

#[cfg(feature = "std")]
impl FsWalEpochSink {
    const MAGIC: &'static [u8; 8] = b"QSAGWAL3";

    fn tag(key: &[u8; 32], body: &[u8]) -> [u8; 32] {
        cshake256_32(b"QSAG.AGG.WAL.MAC/v3", &encode_multi_frame(&[key, body]))
    }

    /// A missing WAL may be initialized only with a newly created lock sidecar.
    /// Use a distinct secret MAC key for each enrolled signing key and profile.
    pub fn open_or_recover(
        path: impl Into<std::path::PathBuf>,
        expected_pk_root: &[u8; 32],
        mac_key: [u8; 32],
    ) -> Result<(Self, Option<WalEpochState>), SigError> {
        Self::open_internal(path.into(), expected_pk_root, mac_key, false)
    }

    /// Explicit fresh-key enrollment, never recovery after a missing WAL.
    pub fn create_new_for_fresh_key(
        path: impl Into<std::path::PathBuf>,
        expected_pk_root: &[u8; 32],
        mac_key: [u8; 32],
    ) -> Result<(Self, Option<WalEpochState>), SigError> {
        Self::open_internal(path.into(), expected_pk_root, mac_key, true)
    }

    fn open_internal(
        path: std::path::PathBuf,
        expected_pk_root: &[u8; 32],
        mac_key: [u8; 32],
        create: bool,
    ) -> Result<(Self, Option<WalEpochState>), SigError> {
        let record = qsag_asm::durable::LockedRecord::acquire(path)
            .map_err(|_| SigError::WalPersistenceFailed)?;
        if create && !record.is_fresh() {
            return Err(SigError::WalPersistenceFailed);
        }
        let mut current = [0u8; 112];
        match record.read() {
            Ok(_) if create => return Err(SigError::WalPersistenceFailed),
            Ok(bytes) => {
                if bytes.len() != current.len() {
                    return Err(SigError::WalPersistenceFailed);
                }
                current.copy_from_slice(&bytes);
                if &current[..8] != Self::MAGIC
                    || &current[8..40] != expected_pk_root
                    || !qsag_asm::ct_eq_bytes(&Self::tag(&mac_key, &current[..80]), &current[80..])
                {
                    return Err(SigError::WalPersistenceFailed);
                }
            }
            Err(e) if e.kind() == std::io::ErrorKind::NotFound && create && record.is_fresh() => {
                current[..8].copy_from_slice(Self::MAGIC);
                current[8..40].copy_from_slice(expected_pk_root);
                let tag = Self::tag(&mac_key, &current[..80]);
                current[80..].copy_from_slice(&tag);
                record
                    .replace(&current)
                    .map_err(|_| SigError::WalPersistenceFailed)?;
            }
            Err(_) => return Err(SigError::WalPersistenceFailed),
        }
        let next = u32::from_le_bytes(current[40..44].try_into().map_err(|_| SigError::WalPersistenceFailed)?);
        let epoch = u32::from_le_bytes(current[44..48].try_into().map_err(|_| SigError::WalPersistenceFailed)?);
        let mut mu = [0; 32];
        mu.copy_from_slice(&current[48..80]);
        let recovered = if next == 0 {
            if current[44..80].iter().any(|&b| b != 0) {
                return Err(SigError::WalPersistenceFailed);
            }
            None
        } else {
            if epoch.checked_add(1) != Some(next) {
                return Err(SigError::WalPersistenceFailed);
            }
            Some((next, epoch, mu))
        };
        Ok((
            Self {
                record,
                mac_key,
                current,
            },
            recovered,
        ))
    }
}

#[cfg(feature = "std")]
impl EpochWalSink for FsWalEpochSink {
    fn recovered_state(&self, pk_root: &[u8; 32]) -> Result<Option<WalEpochState>, SigError> {
        if &self.current[8..40] != pk_root
            || self
                .record
                .read()
                .map_err(|_| SigError::WalPersistenceFailed)?
                .as_slice()
                != self.current
        {
            return Err(SigError::WalPersistenceFailed);
        }
        let next = u32::from_le_bytes(self.current[40..44].try_into().map_err(|_| SigError::WalPersistenceFailed)?);
        let epoch = u32::from_le_bytes(self.current[44..48].try_into().map_err(|_| SigError::WalPersistenceFailed)?);
        let mu = self.current[48..80].try_into().map_err(|_| SigError::WalPersistenceFailed)?;
        Ok((next != 0).then_some((next, epoch, mu)))
    }

    fn persist_latched_epoch(
        &mut self,
        pk_root: &[u8; 32],
        next: u32,
        epoch: u32,
        mu: &[u8; 32],
    ) -> Result<(), SigError> {
        let old_next = u32::from_le_bytes(self.current[40..44].try_into().map_err(|_| SigError::WalPersistenceFailed)?);
        if &self.current[8..40] != pk_root
            || epoch.checked_add(1) != Some(next)
            || next < old_next
            || (next == old_next
                && (&self.current[48..80] != mu
                    || u32::from_le_bytes(self.current[44..48].try_into().map_err(|_| SigError::WalPersistenceFailed)?) != epoch))
            || self
                .record
                .read()
                .map_err(|_| SigError::WalPersistenceFailed)?
                .as_slice()
                != self.current
        {
            return Err(SigError::WalPersistenceFailed);
        }
        let mut staged = self.current;
        staged[40..44].copy_from_slice(&next.to_le_bytes());
        staged[44..48].copy_from_slice(&epoch.to_le_bytes());
        staged[48..80].copy_from_slice(mu);
        let tag = Self::tag(&self.mac_key, &staged[..80]);
        staged[80..].copy_from_slice(&tag);
        self.record
            .replace(&staged)
            .map_err(|_| SigError::WalPersistenceFailed)?;
        self.current = staged;
        Ok(())
    }
}

/// Monotonic durable reservation counter. Reserve BEFORE computing any signature.
/// The sink must bind reservations to the key and serialize competing writers.
