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
    assert!(
        layer < 64 && kp_idx < (1 << 20) && chain_idx < 256 && step_idx < 16,
        "WOTS+C address coordinate out of injective Goldilocks packing bounds"
    );
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
    assert!(
        layer <= 0xFFFE && level <= 0xFFFF,
        "MerkleNodeAddr (layer, level) out of canonical Goldilocks framing range"
    );
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
    verify_individual_signature_with_mu(pk, mu, sig)
}

/// Verify a single `ValidatorSignature` against a precomputed `mu = H_msg_mu(pk, msg)`.
pub(crate) fn verify_individual_signature_with_mu(
    pk: &ValidatorPublicKey,
    mu: Digest5,
    sig: &ValidatorSignature,
) -> bool {
    if pk.profile != sig.profile {
        return false;
    }

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

#[cfg(feature = "std")]
pub use qsag_core::{ExternalMonotoneAnchor, LedgerCheckpoint};

/// Real `fsync`-backed durable WAL implementation for `std` validator deployments (`[P0-04]`).
#[cfg(feature = "std")]
pub struct FsWalEpochSink {
    record: qsag_asm::durable::LockedRecord,
    mac_key: [u8; 32],
    current: [u8; 112],
    lock_identity: [u8; 24],
    anchor: Option<alloc::boxed::Box<dyn ExternalMonotoneAnchor>>,
}

#[cfg(feature = "std")]
impl Drop for FsWalEpochSink {
    fn drop(&mut self) {
        qsag_asm::volatile_fill(&mut self.mac_key, 0);
    }
}

#[cfg(feature = "std")]
impl FsWalEpochSink {
    const MAGIC: &'static [u8; 8] = b"QSAGWAL4";

    fn tag(key: &[u8; 32], identity: &[u8; 24], body: &[u8]) -> [u8; 32] {
        cshake256_32(
            b"QSAG.AGG.WAL.MAC/v4",
            &encode_multi_frame(&[key, identity, body]),
        )
    }

    /// Recover an existing unanchored WAL; missing or older-format records are rejected.
    /// Lock identity detects sidecar replacement. Whole-filesystem rollback protection
    /// requires [`Self::open_anchored`] and an independently durable anchor.
    /// Use a distinct secret MAC key for each enrolled signing key and profile.
    pub fn open_or_recover(
        path: impl Into<std::path::PathBuf>,
        expected_pk_root: &[u8; 32],
        mac_key: [u8; 32],
    ) -> Result<(Self, Option<WalEpochState>), SigError> {
        Self::open_internal(path.into(), expected_pk_root, mac_key, false, None)
    }

    /// Explicit fresh-key enrollment, never recovery after a missing WAL.
    pub fn create_new_for_fresh_key(
        path: impl Into<std::path::PathBuf>,
        expected_pk_root: &[u8; 32],
        mac_key: [u8; 32],
    ) -> Result<(Self, Option<WalEpochState>), SigError> {
        Self::open_internal(path.into(), expected_pk_root, mac_key, true, None)
    }

    /// Enroll a fresh key with an independent durable rollback anchor.
    pub fn create_anchored(
        path: impl Into<std::path::PathBuf>,
        expected_pk_root: &[u8; 32],
        mac_key: [u8; 32],
        anchor: alloc::boxed::Box<dyn ExternalMonotoneAnchor>,
    ) -> Result<(Self, Option<WalEpochState>), SigError> {
        Self::open_internal(path.into(), expected_pk_root, mac_key, true, Some(anchor))
    }

    /// Recover only if the authenticated WAL is at least as new as its independent anchor.
    pub fn open_anchored(
        path: impl Into<std::path::PathBuf>,
        expected_pk_root: &[u8; 32],
        mac_key: [u8; 32],
        anchor: alloc::boxed::Box<dyn ExternalMonotoneAnchor>,
    ) -> Result<(Self, Option<WalEpochState>), SigError> {
        Self::open_internal(path.into(), expected_pk_root, mac_key, false, Some(anchor))
    }

    fn checkpoint(&self) -> LedgerCheckpoint {
        LedgerCheckpoint {
            generation: u32::from_le_bytes(self.current[40..44].try_into().expect("fixed width"))
                as u64,
            tag: self.current[80..].try_into().expect("fixed width"),
        }
    }

    fn check_identity_and_anchor(&self) -> Result<(), SigError> {
        self.record
            .verify_lock_identity(&self.lock_identity)
            .map_err(|_| SigError::WalPersistenceFailed)?;
        if let Some(anchor) = &self.anchor {
            let expected = self.checkpoint();
            if anchor.load().map_err(|_| SigError::WalPersistenceFailed)? != Some(expected) {
                return Err(SigError::WalPersistenceFailed);
            }
        }
        Ok(())
    }

    fn open_internal(
        path: std::path::PathBuf,
        expected_pk_root: &[u8; 32],
        mac_key: [u8; 32],
        create: bool,
        anchor: Option<alloc::boxed::Box<dyn ExternalMonotoneAnchor>>,
    ) -> Result<(Self, Option<WalEpochState>), SigError> {
        let record = qsag_asm::durable::LockedRecord::acquire(path)
            .map_err(|_| SigError::WalPersistenceFailed)?;
        if create && !record.is_fresh() {
            return Err(SigError::WalPersistenceFailed);
        }
        let magic = if anchor.is_some() {
            b"QSAGWAA4"
        } else {
            Self::MAGIC
        };
        let lock_identity = record.lock_identity_seal();
        if let Some(a) = &anchor {
            let enrolled = a
                .load()
                .map_err(|_| SigError::WalPersistenceFailed)?
                .is_some();
            if enrolled == create {
                return Err(SigError::WalPersistenceFailed);
            }
        }
        let mut current = [0u8; 112];
        match record.read() {
            Ok(_) if create => return Err(SigError::WalPersistenceFailed),
            Ok(bytes) => {
                if bytes.len() != current.len() {
                    return Err(SigError::WalPersistenceFailed);
                }
                current.copy_from_slice(&bytes);
                if &current[..8] != magic
                    || &current[8..40] != expected_pk_root
                    || !qsag_asm::ct_eq_bytes(
                        &Self::tag(&mac_key, &lock_identity, &current[..80]),
                        &current[80..],
                    )
                {
                    return Err(SigError::WalPersistenceFailed);
                }
            }
            Err(e) if e.kind() == std::io::ErrorKind::NotFound && create && record.is_fresh() => {
                current[..8].copy_from_slice(magic);
                current[8..40].copy_from_slice(expected_pk_root);
                let tag = Self::tag(&mac_key, &lock_identity, &current[..80]);
                current[80..].copy_from_slice(&tag);
                record
                    .replace(&current)
                    .map_err(|_| SigError::WalPersistenceFailed)?;
            }
            Err(_) => return Err(SigError::WalPersistenceFailed),
        }
        let next = u32::from_le_bytes(
            current[40..44]
                .try_into()
                .map_err(|_| SigError::WalPersistenceFailed)?,
        );
        let epoch = u32::from_le_bytes(
            current[44..48]
                .try_into()
                .map_err(|_| SigError::WalPersistenceFailed)?,
        );
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
        let sink = Self {
            record,
            mac_key,
            current,
            lock_identity,
            anchor,
        };
        if let Some(anchor) = &sink.anchor {
            let checkpoint = sink.checkpoint();
            if let Some(old) = anchor.load().map_err(|_| SigError::WalPersistenceFailed)?
                && (old.generation > checkpoint.generation
                    || (old.generation == checkpoint.generation && old.tag != checkpoint.tag))
            {
                return Err(SigError::WalPersistenceFailed);
            }
            anchor
                .advance(checkpoint)
                .map_err(|_| SigError::WalPersistenceFailed)?;
        }
        Ok((sink, recovered))
    }
}

#[cfg(feature = "std")]
impl EpochWalSink for FsWalEpochSink {
    fn recovered_state(&self, pk_root: &[u8; 32]) -> Result<Option<WalEpochState>, SigError> {
        self.check_identity_and_anchor()?;
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
        let next = u32::from_le_bytes(
            self.current[40..44]
                .try_into()
                .map_err(|_| SigError::WalPersistenceFailed)?,
        );
        let epoch = u32::from_le_bytes(
            self.current[44..48]
                .try_into()
                .map_err(|_| SigError::WalPersistenceFailed)?,
        );
        let mu = self.current[48..80]
            .try_into()
            .map_err(|_| SigError::WalPersistenceFailed)?;
        Ok((next != 0).then_some((next, epoch, mu)))
    }

    fn persist_latched_epoch(
        &mut self,
        pk_root: &[u8; 32],
        next: u32,
        epoch: u32,
        mu: &[u8; 32],
    ) -> Result<(), SigError> {
        self.check_identity_and_anchor()?;
        let old_next = u32::from_le_bytes(
            self.current[40..44]
                .try_into()
                .map_err(|_| SigError::WalPersistenceFailed)?,
        );
        if &self.current[8..40] != pk_root
            || epoch.checked_add(1) != Some(next)
            || next < old_next
            || (next == old_next
                && (&self.current[48..80] != mu
                    || u32::from_le_bytes(
                        self.current[44..48]
                            .try_into()
                            .map_err(|_| SigError::WalPersistenceFailed)?,
                    ) != epoch))
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
        let tag = Self::tag(&self.mac_key, &self.lock_identity, &staged[..80]);
        staged[80..].copy_from_slice(&tag);
        self.record
            .replace(&staged)
            .map_err(|_| SigError::WalPersistenceFailed)?;
        self.current = staged;
        if let Some(anchor) = &self.anchor {
            anchor
                .advance(self.checkpoint())
                .map_err(|_| SigError::WalPersistenceFailed)?;
        }
        Ok(())
    }
}

/// Monotonic durable reservation counter. Reserve BEFORE computing any signature.
/// The sink must bind reservations to the key and serialize competing writers.
pub trait StatelessBudgetWalSink {
    fn reserve(&mut self, pk_root: &[u8; 32], limit: u64) -> Result<u64, SigError>;
}

/// Durable stateless reservations backed by an authenticated, locked epoch record.
/// Use a dedicated WAL path and MAC key for this signing key's stateless budget.
#[cfg(feature = "std")]
pub struct FsStatelessBudgetWal(FsWalEpochSink);

#[cfg(feature = "std")]
impl FsStatelessBudgetWal {
    pub fn create_new_for_fresh_key(
        path: impl Into<std::path::PathBuf>,
        pk_root: &[u8; 32],
        mac_key: [u8; 32],
    ) -> Result<Self, SigError> {
        Ok(Self(
            FsWalEpochSink::create_new_for_fresh_key(path, pk_root, mac_key)?.0,
        ))
    }
    pub fn open_or_recover(
        path: impl Into<std::path::PathBuf>,
        pk_root: &[u8; 32],
        mac_key: [u8; 32],
    ) -> Result<Self, SigError> {
        Ok(Self(
            FsWalEpochSink::open_or_recover(path, pk_root, mac_key)?.0,
        ))
    }
}

#[cfg(feature = "std")]
impl StatelessBudgetWalSink for FsStatelessBudgetWal {
    fn reserve(&mut self, pk_root: &[u8; 32], limit: u64) -> Result<u64, SigError> {
        let used = self
            .0
            .recovered_state(pk_root)?
            .map_or(0, |s| u64::from(s.0));
        if used >= limit || used >= u64::from(u32::MAX) {
            return Err(SigError::StatelessBudgetExhausted);
        }
        self.0.persist_latched_epoch(
            pk_root,
            (used + 1) as u32,
            used as u32,
            &cshake256_32(b"QSAG.STATELESS.BUDGET/v1", pk_root),
        )?;
        Ok(used + 1)
    }
}

/// Non-cloneable stateful `EpochLatch` (`[P0-04]`): enforces monotonic epoch progression and
/// idempotent crash-retry on `(epoch, mu_bytes)` while strictly forbidding `Clone` fork hazards!
#[derive(Default, PartialEq, Eq)]
pub struct StatefulEpochLatch {
    next_unused_epoch: u32,
    last_latched: Option<(u32, [u8; 32], Digest4)>,
}

impl core::fmt::Debug for StatefulEpochLatch {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("StatefulEpochLatch")
            .field("next_unused_epoch", &self.next_unused_epoch)
            .field("has_latched_epoch", &self.last_latched.is_some())
            .finish()
    }
}

impl StatefulEpochLatch {
    pub const fn new() -> Self {
        Self {
            next_unused_epoch: 0,
            last_latched: None,
        }
    }

    pub fn next_unused_epoch(&self) -> u32 {
        self.next_unused_epoch
    }
}

/// Non-cloneable validator keypair with redacted `Debug`, `Drop` zeroization, integrated
/// `StatefulEpochLatch`, and stateless `CORDUROY_MAX_STATELESS_SIGS_PER_KEY` counter (`[P0-04]`).
pub struct ValidatorKeypair {
    sk_seed: Digest4,
    sk_prf: Digest4,
    pub pk: ValidatorPublicKey,
    top_subtree_leaves: Vec<Digest4>,
    latch: StatefulEpochLatch,
    stateless_sigs_issued: u64,
}

impl core::fmt::Debug for ValidatorKeypair {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("ValidatorKeypair")
            .field("pk", &self.pk)
            .field("sk_seed", &"[REDACTED]")
            .field("sk_prf", &"[REDACTED]")
            .field("next_unused_epoch", &self.latch.next_unused_epoch)
            .field("stateless_sigs_issued", &self.stateless_sigs_issued)
            .finish()
    }
}

impl Drop for ValidatorKeypair {
    fn drop(&mut self) {
        qsag_asm::volatile_fill(&mut self.sk_seed, Goldilocks::ZERO);
        qsag_asm::volatile_fill(&mut self.sk_prf, Goldilocks::ZERO);
        if let Some((_, ref mut mu_b, ref mut r_b)) = self.latch.last_latched {
            qsag_asm::volatile_fill(mu_b, 0);
            qsag_asm::volatile_fill(r_b, Goldilocks::ZERO);
        }
    }
}

impl ValidatorKeypair {
    /// Generate a genuine full-tree `ValidatorKeypair` from `(master_seed, validator_idx)`.
    pub fn keygen_deterministic(
        profile: AggSigProfile,
        master_seed: &[u8; 32],
        validator_idx: u32,
    ) -> Self {
        let idx_bytes = validator_idx.to_le_bytes();
        let mut raw_sk = cshake256_32(
            b"QSAG.KEYGEN.SK/v2",
            &encode_multi_frame(&[master_seed, &idx_bytes]),
        );
        let mut raw_prf = cshake256_32(
            b"QSAG.KEYGEN.PRF/v2",
            &encode_multi_frame(&[master_seed, &idx_bytes]),
        );
        let raw_pub = cshake256_32(
            b"QSAG.KEYGEN.PKSEED/v2",
            &encode_multi_frame(&[master_seed, &idx_bytes]),
        );

        let to_d4 = |b: &[u8; 32]| -> Digest4 {
            let mut d = [Goldilocks::ZERO; 4];
            for i in 0..4 {
                let mut limb = [0u8; 8];
                limb.copy_from_slice(&b[8 * i..8 * (i + 1)]);
                d[i] = Goldilocks::from_u64_reduced(u64::from_le_bytes(limb));
            }
            d
        };
        let sk_seed = to_d4(&raw_sk);
        let sk_prf = to_d4(&raw_prf);
        let pk_seed = to_d4(&raw_pub);
        qsag_asm::volatile_fill(&mut raw_sk, 0);
        qsag_asm::volatile_fill(&mut raw_prf, 0);

        let (top_layer, sub_height) = match profile {
            AggSigProfile::JortsPoseidon2 => (0u32, JORTS_XMSS_HEIGHT),
            AggSigProfile::CorduroyPoseidon2 => {
                ((CORDUROY_NUM_LAYERS - 1) as u32, CORDUROY_SUBTREE_HEIGHT)
            }
        };
        let (top_subtree_leaves, pk_root) =
            Self::build_xmss_subtree(sk_seed, pk_seed, top_layer, 0, sub_height);

        Self {
            sk_seed,
            sk_prf,
            pk: ValidatorPublicKey {
                profile,
                pk_seed,
                pk_root,
            },
            top_subtree_leaves,
            latch: StatefulEpochLatch::new(),
            stateless_sigs_issued: 0,
        }
    }

    #[inline]
    pub fn next_unused_epoch(&self) -> u32 {
        self.latch.next_unused_epoch
    }

    #[inline]
    pub fn stateless_sigs_issued(&self) -> u64 {
        self.stateless_sigs_issued
    }

    /// Restore durable `StatefulEpochLatch` state recovered by `FsWalEpochSink::open_or_recover`.
    pub fn restore_from_wal(
        &mut self,
        next_unused_epoch: u32,
        latched_epoch: u32,
        mu_bytes: [u8; 32],
    ) -> Result<(), SigError> {
        if next_unused_epoch == 0
            || next_unused_epoch < self.latch.next_unused_epoch
            || (next_unused_epoch == self.latch.next_unused_epoch
                && self
                    .latch
                    .last_latched
                    .as_ref()
                    .is_some_and(|(ep, mu, _)| *ep != latched_epoch || *mu != mu_bytes))
            || latched_epoch >= next_unused_epoch
            || (next_unused_epoch as usize) > (1usize << JORTS_XMSS_HEIGHT)
        {
            return Err(SigError::WalPersistenceFailed);
        }
        let mu = bytes32_to_limbs56(&mu_bytes);
        let r = self.derive_deterministic_r_rand(mu, latched_epoch as u64);
        self.latch.next_unused_epoch = next_unused_epoch;
        self.latch.last_latched = Some((latched_epoch, mu_bytes, r));
        Ok(())
    }

    fn build_xmss_subtree(
        sk_seed: Digest4,
        pk_seed: Digest4,
        layer: u32,
        tree_idx: u64,
        sub_height: usize,
    ) -> (Vec<Digest4>, Digest4) {
        let num_leaves = 1usize << sub_height;
        let mut leaves = Vec::with_capacity(num_leaves);
        for kp in 0..num_leaves {
            let mut endpoints = [[Goldilocks::ZERO; 4]; WOTS_CHAINS];
            for (r, endpoint) in endpoints.iter_mut().enumerate().take(WOTS_CHAINS) {
                let mut cur =
                    Self::wots_base_secret(sk_seed, pk_seed, layer, tree_idx, kp as u32, r as u32);
                for step in 0..(WOTS_MAX_STEP as u32) {
                    cur = wots_step_hash_injective(
                        pk_seed, cur, layer, tree_idx, kp as u32, r as u32, step,
                    );
                }
                *endpoint = cur;
                qsag_asm::volatile_fill(&mut cur, Goldilocks::ZERO);
            }
            leaves.push(compress_wots_endpoints_sponge(
                pk_seed, layer, tree_idx, kp as u32, &endpoints,
            ));
        }

        let mut cur_layer = leaves.clone();
        for lvl in 0..sub_height {
            let mut next = Vec::with_capacity(cur_layer.len() / 2);
            for p in 0..(cur_layer.len() / 2) {
                next.push(merkle_node_hash(
                    DOMAIN_MERKLE_NODE,
                    pk_seed,
                    MerkleNodeAddr {
                        layer,
                        tree_idx,
                        level: (lvl + 1) as u32,
                        node_idx: p as u32,
                    },
                    cur_layer[2 * p],
                    cur_layer[2 * p + 1],
                ));
            }
            cur_layer = next;
        }
        (leaves, cur_layer[0])
    }

    #[inline]
    fn wots_base_secret(
        sk_seed: Digest4,
        pk_seed: Digest4,
        layer: u32,
        tree_idx: u64,
        kp_idx: u32,
        chain_idx: u32,
    ) -> Digest4 {
        let tweak = [
            Goldilocks::from_u64_reduced(DOMAIN_PRF_WOTS),
            pack_wots_addr_limb(layer, kp_idx, chain_idx, 0),
            Goldilocks::from_u64_reduced(tree_idx & 0xFFFF_FFFF),
            Goldilocks::from_u64_reduced(tree_idx >> 32),
        ];
        poseidon2_compress12_ff(sk_seed, pk_seed, tweak)
    }

    #[inline]
    fn fors_leaf_secret(&self, tree_idx: u64, kp_idx: u32, global_fors_leaf: u64) -> Digest4 {
        let tweak = [
            Goldilocks::from_u64_reduced(DOMAIN_FORS_PRF),
            Goldilocks::from_u64_reduced(((kp_idx as u64) << 24) | global_fors_leaf),
            Goldilocks::from_u64_reduced(tree_idx & 0xFFFF_FFFF),
            Goldilocks::from_u64_reduced(tree_idx >> 32),
        ];
        poseidon2_compress12_ff(self.sk_seed, self.pk.pk_seed, tweak)
    }

    #[inline]
    fn derive_deterministic_r_rand(&self, mu: Digest5, epoch_or_nonce: u64) -> Digest4 {
        let mut st = [
            self.sk_prf[0],
            self.sk_prf[1],
            self.sk_prf[2],
            self.sk_prf[3],
            self.pk.pk_seed[0],
            self.pk.pk_seed[1],
            self.pk.pk_seed[2],
            self.pk.pk_seed[3],
            Goldilocks::from_u64_reduced(DOMAIN_PRF_MSG),
            Goldilocks::from_u64_reduced(epoch_or_nonce),
            mu[4],
            Goldilocks::from_u64_reduced(POSEIDON2_CONST_IV),
        ];
        poseidon2_perm12(&mut st);
        for i in 0..4 {
            st[i] += mu[i];
        }
        poseidon2_perm12(&mut st);
        let out = [st[0], st[1], st[2], st[3]];
        qsag_asm::volatile_fill(&mut st, Goldilocks::ZERO);
        out
    }

    /// Stateful signing with mandatory `StatefulEpochLatch` (`[P0-04]`):
    /// - Idempotently returns the identical signature if `(epoch, msg)` matches the last latched call,
    /// - Rejects any attempt to sign a different message at an already-latched epoch or out-of-order epoch!
    pub fn sign_stateful(
        &mut self,
        msg: &[u8],
        epoch: u32,
        wal: &mut dyn EpochWalSink,
    ) -> Result<ValidatorSignature, SigError> {
        self.sign_stateful_with_wal(msg, epoch, wal)
    }

    #[cfg(test)]
    pub(crate) fn sign_stateful_for_unit_test(
        &mut self,
        msg: &[u8],
        epoch: u32,
    ) -> Result<ValidatorSignature, SigError> {
        self.sign_stateful_internal(msg, epoch, None)
    }

    /// Load a stateful key and initialize its latch directly from authenticated storage.
    pub fn from_master_seed_with_wal(
        profile: AggSigProfile,
        master_seed: &[u8; 32],
        validator_idx: u32,
        wal: &dyn EpochWalSink,
    ) -> Result<Self, SigError> {
        if profile != AggSigProfile::JortsPoseidon2 {
            return Err(SigError::ProfileMismatch);
        }
        let mut key = Self::keygen_deterministic(profile, master_seed, validator_idx);
        if let Some((next, epoch, mu)) = wal.recovered_state(&digest4_to_bytes(&key.pk.pk_root))? {
            key.restore_from_wal(next, epoch, mu)?;
        }
        Ok(key)
    }

    /// Stateful signing backed by a durable `EpochWalSink` (`FsWalEpochSink` under `std`), ensuring
    /// the advanced epoch is `fsync`ed to stable storage **strictly BEFORE** any WOTS+C chain values
    /// are computed or returned (`[P0-04]`).
    pub fn sign_stateful_with_wal(
        &mut self,
        msg: &[u8],
        epoch: u32,
        wal: &mut dyn EpochWalSink,
    ) -> Result<ValidatorSignature, SigError> {
        if self.pk.profile != AggSigProfile::JortsPoseidon2 {
            return Err(SigError::ProfileMismatch);
        }
        let root = digest4_to_bytes(&self.pk.pk_root);
        if let Some((next, prev, mu)) = wal.recovered_state(&root)? {
            self.restore_from_wal(next, prev, mu)?;
        }
        self.sign_stateful_internal(msg, epoch, Some(wal))
    }

    fn sign_stateful_internal(
        &mut self,
        msg: &[u8],
        epoch: u32,
        wal: Option<&mut dyn EpochWalSink>,
    ) -> Result<ValidatorSignature, SigError> {
        if self.pk.profile != AggSigProfile::JortsPoseidon2 {
            return Err(SigError::ProfileMismatch);
        }
        if (epoch as usize) >= (1usize << JORTS_XMSS_HEIGHT) {
            return Err(SigError::EpochOutOfBounds);
        }
        let (mu_bytes, mu) = compute_message_mu(&self.pk, msg);
        if let Some((prev, prev_mu, _)) = self.latch.last_latched {
            if epoch == prev && prev_mu != mu_bytes {
                return Err(SigError::EpochReuseDifferentMessage);
            }
            if epoch != prev && epoch < self.latch.next_unused_epoch {
                return Err(SigError::EpochMonotonicityViolation);
            }
        }
        if let Some(sink) = wal {
            sink.persist_latched_epoch(
                &digest4_to_bytes(&self.pk.pk_root),
                epoch + 1,
                epoch,
                &mu_bytes,
            )?;
        }
        let r_rand = if let Some((prev_ep, prev_mu, cached_r)) = self.latch.last_latched {
            if epoch == prev_ep {
                if mu_bytes == prev_mu {
                    cached_r
                } else {
                    return Err(SigError::EpochReuseDifferentMessage);
                }
            } else if epoch < self.latch.next_unused_epoch {
                return Err(SigError::EpochMonotonicityViolation);
            } else {
                let next_ep = epoch + 1;
                let r = self.derive_deterministic_r_rand(mu, epoch as u64);
                self.latch.next_unused_epoch = next_ep;
                self.latch.last_latched = Some((epoch, mu_bytes, r));
                r
            }
        } else {
            let next_ep = epoch + 1;
            let r = self.derive_deterministic_r_rand(mu, epoch as u64);
            self.latch.next_unused_epoch = next_ep;
            self.latch.last_latched = Some((epoch, mu_bytes, r));
            r
        };

        let mut tsw_ctr = 0u32;
        let digits = loop {
            let hmsg =
                compute_hmsg_stateful(self.pk.pk_seed, self.pk.pk_root, r_rand, mu, epoch, tsw_ctr);
            if let Some(d) = extract_wots_digits_checked(&hmsg) {
                let s: usize = d.iter().map(|&x| x as usize).sum();
                if s == WOTS_TARGET_SUM {
                    break d;
                }
            }
            tsw_ctr = tsw_ctr
                .checked_add(1)
                .ok_or(SigError::SigningCounterExhausted)?;
        };

        let mut wots_chains = Vec::with_capacity(WOTS_CHAINS);
        for (r, &digit) in digits.iter().enumerate().take(WOTS_CHAINS) {
            let mut cur =
                Self::wots_base_secret(self.sk_seed, self.pk.pk_seed, 0, 0, epoch, r as u32);
            for step in 0..(digit as u32) {
                cur = wots_step_hash_injective(self.pk.pk_seed, cur, 0, 0, epoch, r as u32, step);
            }
            wots_chains.push(cur);
            qsag_asm::volatile_fill(&mut cur, Goldilocks::ZERO);
        }

        let mut merkle_path = Vec::with_capacity(JORTS_XMSS_HEIGHT);
        let mut cur_layer = self.top_subtree_leaves.clone();
        let mut idx = epoch as usize;
        for lvl in 0..JORTS_XMSS_HEIGHT {
            merkle_path.push(cur_layer[idx ^ 1]);
            let mut next = Vec::with_capacity(cur_layer.len() / 2);
            for p in 0..(cur_layer.len() / 2) {
                next.push(merkle_node_hash(
                    DOMAIN_MERKLE_NODE,
                    self.pk.pk_seed,
                    MerkleNodeAddr {
                        layer: 0,
                        tree_idx: 0,
                        level: (lvl + 1) as u32,
                        node_idx: p as u32,
                    },
                    cur_layer[2 * p],
                    cur_layer[2 * p + 1],
                ));
            }
            cur_layer = next;
            idx >>= 1;
        }
        debug_assert_eq!(cur_layer[0], self.pk.pk_root);

        Ok(ValidatorSignature {
            profile: AggSigProfile::JortsPoseidon2,
            r_rand,
            stateful_leaf_idx: epoch,
            fors_openings: Vec::new(),
            layers: vec![HypertreeLayerSig {
                tsw_ctr,
                wots_chains,
                merkle_path,
            }],
        })
    }

    /// Stateless signing for `CorduroyPoseidon2` (`[P0-03]`):
    /// - Enforces `stateless_sigs_issued < CORDUROY_MAX_STATELESS_SIGS_PER_KEY` ($2^{20}$) so $(k=32, a=8)$
    ///   FORS subset-resilience maintains $> 128$-bit post-quantum security against multi-hit collisions,
    /// - Derives `(fors_idxs, leaf_global_idx)` from XOF `H_msg_stateless` over disjoint bit windows,
    /// - Signs static `fors_pk` and upper-layer `child_root`s deterministically WITHOUT `r_rand` or `mu`!
    pub fn sign_stateless(
        &mut self,
        msg: &[u8],
        wal: &mut dyn StatelessBudgetWalSink,
    ) -> Result<ValidatorSignature, SigError> {
        self.sign_stateless_with_wal(msg, wal)
    }

    pub fn sign_stateless_with_wal(
        &mut self,
        msg: &[u8],
        wal: &mut dyn StatelessBudgetWalSink,
    ) -> Result<ValidatorSignature, SigError> {
        if self.pk.profile != AggSigProfile::CorduroyPoseidon2 {
            return Err(SigError::ProfileMismatch);
        }
        let issued = wal.reserve(
            &digest4_to_bytes(&self.pk.pk_root),
            CORDUROY_MAX_STATELESS_SIGS_PER_KEY,
        )?;
        if issued == 0
            || issued <= self.stateless_sigs_issued
            || issued > CORDUROY_MAX_STATELESS_SIGS_PER_KEY
        {
            return Err(SigError::WalPersistenceFailed);
        }
        self.stateless_sigs_issued = issued;
        self.sign_stateless_internal(msg)
    }

    #[cfg(test)]
    pub(crate) fn sign_stateless_for_unit_test(
        &mut self,
        msg: &[u8],
    ) -> Result<ValidatorSignature, SigError> {
        if self.stateless_sigs_issued >= CORDUROY_MAX_STATELESS_SIGS_PER_KEY {
            return Err(SigError::StatelessBudgetExhausted);
        }
        self.stateless_sigs_issued += 1;
        self.sign_stateless_internal(msg)
    }

    fn sign_stateless_internal(&mut self, msg: &[u8]) -> Result<ValidatorSignature, SigError> {
        if self.pk.profile != AggSigProfile::CorduroyPoseidon2 {
            return Err(SigError::ProfileMismatch);
        }
        let (_, mu) = compute_message_mu(&self.pk, msg);

        let mut r_nonce = 0u64;
        let (r_rand, fors_idxs, leaf_global_idx) = loop {
            let r_cand = self.derive_deterministic_r_rand(mu, r_nonce);
            if let Some((f_idxs, leaf_idx, _)) =
                derive_stateless_fors_and_leaf_checked(self.pk.pk_seed, self.pk.pk_root, r_cand, mu)
            {
                break (r_cand, f_idxs, leaf_idx);
            }
            r_nonce += 1;
        };

        let kp0 = (leaf_global_idx & ((1u64 << CORDUROY_SUBTREE_HEIGHT) - 1)) as u32;
        let tree0 = leaf_global_idx >> CORDUROY_SUBTREE_HEIGHT;
        let fors_leaf_cnt = 1usize << FORS_HEIGHT;
        let mut fors_openings = Vec::with_capacity(FORS_TREES);
        let mut fors_roots = [[Goldilocks::ZERO; 4]; FORS_TREES];

        for j in 0..FORS_TREES {
            let mut leaves = Vec::with_capacity(fors_leaf_cnt);
            for l in 0..fors_leaf_cnt {
                let gl = ((j as u64) << FORS_HEIGHT) | (l as u64);
                let mut sec = self.fors_leaf_secret(tree0, kp0, gl);
                let lt = [
                    Goldilocks::from_u64_reduced(DOMAIN_FORS_LEAF),
                    Goldilocks::from_u64_reduced(((kp0 as u64) << 24) | gl),
                    Goldilocks::from_u64_reduced(tree0 & 0xFFFF_FFFF),
                    Goldilocks::from_u64_reduced(tree0 >> 32),
                ];
                leaves.push(poseidon2_compress12_ff(sec, self.pk.pk_seed, lt));
                qsag_asm::volatile_fill(&mut sec, Goldilocks::ZERO);
            }
            let mut auth_path = [[Goldilocks::ZERO; 4]; FORS_HEIGHT];
            let mut cur_layer = leaves;
            let mut cur_idx = fors_idxs[j];
            for (lvl, path_item) in auth_path.iter_mut().enumerate().take(FORS_HEIGHT) {
                *path_item = cur_layer[cur_idx ^ 1];
                let mut next = Vec::with_capacity(cur_layer.len() / 2);
                for p in 0..(cur_layer.len() / 2) {
                    let addr_node = ((j as u32) << (FORS_HEIGHT - 1 - lvl)) + (p as u32);
                    next.push(merkle_node_hash(
                        DOMAIN_FORS_NODE,
                        self.pk.pk_seed,
                        MerkleNodeAddr {
                            layer: 0,
                            tree_idx: tree0,
                            level: (lvl + 1) as u32,
                            node_idx: (kp0 << 16) | addr_node,
                        },
                        cur_layer[2 * p],
                        cur_layer[2 * p + 1],
                    ));
                }
                cur_layer = next;
                cur_idx >>= 1;
            }
            fors_roots[j] = cur_layer[0];
            let chosen_gl = ((j as u64) << FORS_HEIGHT) | (fors_idxs[j] as u64);
            fors_openings.push(ForsOpening {
                secret_val: self.fors_leaf_secret(tree0, kp0, chosen_gl),
                auth_path,
            });
        }

        let mut st = [
            self.pk.pk_seed[0],
            self.pk.pk_seed[1],
            self.pk.pk_seed[2],
            self.pk.pk_seed[3],
            Goldilocks::from_u64_reduced(kp0 as u64),
            Goldilocks::from_u64_reduced(tree0 & 0xFFFF_FFFF),
            Goldilocks::from_u64_reduced(tree0 >> 32),
            Goldilocks::from_u64_reduced(FORS_TREES as u64),
            Goldilocks::from_u64_reduced(DOMAIN_FORS_ROOTS),
            Goldilocks::ZERO,
            Goldilocks::ZERO,
            Goldilocks::from_u64_reduced(POSEIDON2_CONST_IV),
        ];
        poseidon2_perm12(&mut st);
        for pair in 0..(FORS_TREES / 2) {
            for i in 0..4 {
                st[i] += fors_roots[2 * pair][i];
                st[4 + i] += fors_roots[2 * pair + 1][i];
            }
            poseidon2_perm12(&mut st);
        }
        st[0] += Goldilocks::ONE;
        poseidon2_perm12(&mut st);
        let mut cur_root = [st[0], st[1], st[2], st[3]];

        let mut layers = Vec::with_capacity(CORDUROY_NUM_LAYERS);
        let mut idx_cursor = leaf_global_idx;
        for layer in 0..CORDUROY_NUM_LAYERS {
            let kp_idx = (idx_cursor & ((1u64 << CORDUROY_SUBTREE_HEIGHT) - 1)) as u32;
            let tree_idx = idx_cursor >> CORDUROY_SUBTREE_HEIGHT;

            // Deterministic WOTS+C counter strictly from `(pk_seed, pk_root, layer, tree_idx, kp_idx, cur_root)`!
            let mut tsw_ctr = 0u32;
            let digits = loop {
                let hmsg = compute_hmsg_det_tree(
                    self.pk.pk_seed,
                    self.pk.pk_root,
                    layer as u32,
                    tree_idx,
                    kp_idx,
                    tsw_ctr,
                    cur_root,
                );
                if let Some(d) = extract_wots_digits_checked(&hmsg) {
                    let s: usize = d.iter().map(|&x| x as usize).sum();
                    if s == WOTS_TARGET_SUM {
                        break d;
                    }
                }
                tsw_ctr = tsw_ctr
                    .checked_add(1)
                    .ok_or(SigError::SigningCounterExhausted)?;
            };

            let mut wots_chains = Vec::with_capacity(WOTS_CHAINS);
            for (r, &digit) in digits.iter().enumerate().take(WOTS_CHAINS) {
                let mut cur = Self::wots_base_secret(
                    self.sk_seed,
                    self.pk.pk_seed,
                    layer as u32,
                    tree_idx,
                    kp_idx,
                    r as u32,
                );
                for step in 0..(digit as u32) {
                    cur = wots_step_hash_injective(
                        self.pk.pk_seed,
                        cur,
                        layer as u32,
                        tree_idx,
                        kp_idx,
                        r as u32,
                        step,
                    );
                }
                wots_chains.push(cur);
                qsag_asm::volatile_fill(&mut cur, Goldilocks::ZERO);
            }

            let (sub_leaves, next_root) = if layer + 1 == CORDUROY_NUM_LAYERS {
                (self.top_subtree_leaves.clone(), self.pk.pk_root)
            } else {
                Self::build_xmss_subtree(
                    self.sk_seed,
                    self.pk.pk_seed,
                    layer as u32,
                    tree_idx,
                    CORDUROY_SUBTREE_HEIGHT,
                )
            };
            let mut merkle_path = Vec::with_capacity(CORDUROY_SUBTREE_HEIGHT);
            let mut cur_layer = sub_leaves;
            let mut sub_idx = kp_idx as usize;
            for lvl in 0..CORDUROY_SUBTREE_HEIGHT {
                merkle_path.push(cur_layer[sub_idx ^ 1]);
                let mut next = Vec::with_capacity(cur_layer.len() / 2);
                for p in 0..(cur_layer.len() / 2) {
                    next.push(merkle_node_hash(
                        DOMAIN_MERKLE_NODE,
                        self.pk.pk_seed,
                        MerkleNodeAddr {
                            layer: layer as u32,
                            tree_idx,
                            level: (lvl + 1) as u32,
                            node_idx: p as u32,
                        },
                        cur_layer[2 * p],
                        cur_layer[2 * p + 1],
                    ));
                }
                cur_layer = next;
                sub_idx >>= 1;
            }
            debug_assert_eq!(cur_layer[0], next_root);
            cur_root = next_root;
            idx_cursor = tree_idx;

            layers.push(HypertreeLayerSig {
                tsw_ctr,
                wots_chains,
                merkle_path,
            });
        }

        Ok(ValidatorSignature {
            profile: AggSigProfile::CorduroyPoseidon2,
            r_rand,
            stateful_leaf_idx: 0,
            fors_openings,
            layers,
        })
    }
}

// ============================================================================
// Canonical Signer Bitmap & Committee Commitment
// ============================================================================

/// Canonical bitvector over `0..num_validators` tracking participating signers.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SignerBitmap {
    num_validators: u32,
    words: Vec<u64>,
}

impl SignerBitmap {
    pub fn new_empty(num_validators: u32) -> Self {
        let n_words = (num_validators as usize).div_ceil(64);
        Self {
            num_validators,
            words: vec![0u64; n_words],
        }
    }

    pub fn from_active_indices(num_validators: u32, indices: &[usize]) -> Option<Self> {
        let mut bm = Self::new_empty(num_validators);
        for &idx in indices {
            if idx >= num_validators as usize || bm.contains(idx) {
                return None;
            }
            bm.set(idx);
        }
        Some(bm)
    }

    #[inline]
    pub fn num_validators(&self) -> u32 {
        self.num_validators
    }

    #[inline]
    pub fn set(&mut self, idx: usize) {
        assert!(idx < self.num_validators as usize);
        self.words[idx / 64] |= 1u64 << (idx % 64);
    }

    #[inline]
    pub fn contains(&self, idx: usize) -> bool {
        if idx >= self.num_validators as usize {
            return false;
        }
        ((self.words[idx / 64] >> (idx % 64)) & 1) == 1
    }

    #[inline]
    pub fn count_ones(&self) -> usize {
        self.words.iter().map(|w| w.count_ones() as usize).sum()
    }

    /// Lowest active signer index, if any.
    pub fn first_active(&self) -> Option<usize> {
        self.words
            .iter()
            .enumerate()
            .find(|&(_, &w)| w != 0)
            .map(|(wi, &w)| wi * 64 + w.trailing_zeros() as usize)
    }

    pub fn active_indices(&self) -> Vec<usize> {
        let mut out = Vec::with_capacity(self.count_ones());
        for (wi, &word) in self.words.iter().enumerate() {
            let mut w = word;
            while w != 0 {
                let tz = w.trailing_zeros() as usize;
                out.push(wi * 64 + tz);
                w &= w - 1;
            }
        }
        out
    }

    /// Strict disjointness predicate: same committee size AND zero overlapping bits (`A & B == 0`).
    pub fn is_disjoint(&self, other: &Self) -> bool {
        if self.num_validators != other.num_validators || self.words.len() != other.words.len() {
            return false;
        }
        self.words
            .iter()
            .zip(other.words.iter())
            .all(|(&a, &b)| (a & b) == 0)
    }

    /// Disjoint union (`A | B`), returning `None` if committees mismatch or ANY signer bit overlaps.
    pub fn union_disjoint(&self, other: &Self) -> Option<Self> {
        if !self.is_disjoint(other) {
            return None;
        }
        let words = self
            .words
            .iter()
            .zip(other.words.iter())
            .map(|(&a, &b)| a | b)
            .collect();
        Some(Self {
            num_validators: self.num_validators,
            words,
        })
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(4 + 8 * self.words.len());
        out.extend_from_slice(&self.num_validators.to_le_bytes());
        for &w in &self.words {
            out.extend_from_slice(&w.to_le_bytes());
        }
        out
    }

    pub fn from_bytes_canonical(bytes: &[u8]) -> Option<(Self, usize)> {
        if bytes.len() < 4 {
            return None;
        }
        let mut nv = [0u8; 4];
        nv.copy_from_slice(&bytes[0..4]);
        let num_validators = u32::from_le_bytes(nv);
        let n_words = (num_validators as usize).div_ceil(64);
        let need = 4 + 8 * n_words;
        if bytes.len() < need {
            return None;
        }
        let mut words = Vec::with_capacity(n_words);
        for i in 0..n_words {
            let mut wb = [0u8; 8];
            wb.copy_from_slice(&bytes[4 + 8 * i..4 + 8 * (i + 1)]);
            words.push(u64::from_le_bytes(wb));
        }
        let rem = (num_validators as usize) % 64;
        if rem != 0 {
            if let Some(&last) = words.last() {
                if (last >> rem) != 0 {
                    return None;
                }
            }
        }
        Some((
            Self {
                num_validators,
                words,
            },
            need,
        ))
    }
}

/// Message binding mode for an aggregate proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SigningMode<'a> {
    /// Consensus fast-path: all active signers sign the same message `msg`.
    SharedMessage(&'a [u8]),
    /// Multi-statement aggregation: the `k`-th active signer in `bitmap.active_indices()` signs `msgs[k]`.
    PerSignerMessages(&'a [&'a [u8]]),
}

/// Canonical 32-byte domain-separated commitment to the ordered validator committee `pks`.
pub fn compute_committee_root(pks: &[ValidatorPublicKey]) -> [u8; 32] {
    let mut encoded = Vec::with_capacity(4 + 65 * pks.len());
    encoded.extend_from_slice(&(pks.len() as u32).to_le_bytes());
    for pk in pks {
        encoded.extend_from_slice(&pk.to_bytes());
    }
    cshake256_32(b"QSAG.COMMITTEE.ROOT/v2", &encoded)
}

/// Verify that all active validators in `bitmap` have matching `profile` and **pairwise distinct**
/// `(pk_seed, pk_root)` (`[P0-04]` anti-duplicate-validator replay defense).
pub fn validate_unique_active_committee(
    pks: &[ValidatorPublicKey],
    bitmap: &SignerBitmap,
    expected_profile: AggSigProfile,
) -> bool {
    if pks.len() != bitmap.num_validators() as usize {
        return false;
    }
    let active = bitmap.active_indices();
    if active.is_empty() {
        return false;
    }
    let mut seen = BTreeSet::new();
    for &idx in &active {
        let pk = pks[idx];
        if pk.profile != expected_profile {
            return false;
        }
        if !seen.insert((pk.pk_seed, pk.pk_root)) {
            return false;
        }
    }
    true
}

impl core::fmt::Display for SigError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl core::error::Error for SigError {}

#[cfg(test)]
mod persistence_and_encoding_tests {
    use super::*;

    #[test]
    fn signature_canonical_decoding() {
        for profile in [
            AggSigProfile::JortsPoseidon2,
            AggSigProfile::CorduroyPoseidon2,
        ] {
            let bytes = vec![0; profile.raw_signature_bytes()];
            let parsed = ValidatorSignature::from_bytes_canonical(profile, &bytes).unwrap();
            assert_eq!(parsed.to_bytes(), bytes);
            let mut trailing = bytes.clone();
            trailing.push(0);
            assert!(ValidatorSignature::from_bytes_canonical(profile, &trailing).is_err());
            assert!(
                ValidatorSignature::from_bytes_canonical(profile, &bytes[..bytes.len() - 1])
                    .is_err()
            );
            // Every digest limb, including FORS paths and all hypertree layers.
            let mut offsets: Vec<usize> = (0..32).step_by(8).collect();
            let mut pos = 32;
            if profile == AggSigProfile::JortsPoseidon2 {
                pos += 4;
            } else {
                let end = pos + FORS_TREES * (1 + FORS_HEIGHT) * 32;
                offsets.extend((pos..end).step_by(8));
                pos = end;
            }
            let (layers, height) = if profile == AggSigProfile::JortsPoseidon2 {
                (1, JORTS_XMSS_HEIGHT)
            } else {
                (CORDUROY_NUM_LAYERS, CORDUROY_SUBTREE_HEIGHT)
            };
            for _ in 0..layers {
                pos += 4;
                let end = pos + (WOTS_CHAINS + height) * 32;
                offsets.extend((pos..end).step_by(8));
                pos = end;
            }
            assert_eq!(pos, bytes.len());
            for offset in offsets {
                let mut bad = bytes.clone();
                bad[offset..offset + 8]
                    .copy_from_slice(&crate::field::GOLDILOCKS_PRIME.to_le_bytes());
                assert!(ValidatorSignature::from_bytes_canonical(profile, &bad).is_err());
            }
        }
    }

    #[test]
    fn stateful_signing_refuses_failed_wal() {
        struct FailedWal;
        impl EpochWalSink for FailedWal {
            fn recovered_state(&self, _: &[u8; 32]) -> Result<Option<WalEpochState>, SigError> {
                Ok(None)
            }
            fn persist_latched_epoch(
                &mut self,
                _: &[u8; 32],
                _: u32,
                _: u32,
                _: &[u8; 32],
            ) -> Result<(), SigError> {
                Err(SigError::WalPersistenceFailed)
            }
        }
        let mut key =
            ValidatorKeypair::keygen_deterministic(AggSigProfile::JortsPoseidon2, &[15; 32], 0);
        assert_eq!(
            key.sign_stateful(b"must not sign", 0, &mut FailedWal),
            Err(SigError::WalPersistenceFailed)
        );
        assert_eq!(key.next_unused_epoch(), 0);
    }

    #[cfg(feature = "std")]
    #[test]
    fn stateless_signing_reserves_before_release_and_recovers_count() {
        let path = std::env::temp_dir().join(std::format!(
            "qsag_sign_budget_{}_{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let profile = AggSigProfile::CorduroyPoseidon2;
        let mut key = ValidatorKeypair::keygen_deterministic(profile, &[13; 32], 0);
        let root = digest4_to_bytes(&key.pk.pk_root);
        let mut wal =
            FsStatelessBudgetWal::create_new_for_fresh_key(&path, &root, [19; 32]).unwrap();
        let signature = key.sign_stateless(b"persisted", &mut wal).unwrap();
        assert!(verify_individual_signature(
            &key.pk,
            b"persisted",
            &signature
        ));
        assert_eq!(
            ValidatorSignature::from_bytes_canonical(profile, &signature.to_bytes()).unwrap(),
            signature
        );
        assert_eq!(key.stateless_sigs_issued(), 1);
        drop(wal);
        let mut key = ValidatorKeypair::keygen_deterministic(profile, &[13; 32], 0);
        let mut wal = FsStatelessBudgetWal::open_or_recover(&path, &root, [19; 32]).unwrap();
        assert!(key.sign_stateless(b"after restart", &mut wal).is_ok());
        assert_eq!(key.stateless_sigs_issued(), 2);
        struct FailedWal;
        impl StatelessBudgetWalSink for FailedWal {
            fn reserve(&mut self, _: &[u8; 32], _: u64) -> Result<u64, SigError> {
                Err(SigError::WalPersistenceFailed)
            }
        }
        assert_eq!(
            key.sign_stateless(b"must not sign", &mut FailedWal),
            Err(SigError::WalPersistenceFailed)
        );
        assert_eq!(key.stateless_sigs_issued(), 2);
        drop(wal);
        std::fs::remove_file(path).unwrap();
    }

    #[cfg(feature = "std")]
    #[test]
    fn durable_stateless_budget_survives_restart_and_rejects_wrong_key() {
        let path = std::env::temp_dir().join(std::format!(
            "qsag_budget_{}_{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let root = [9; 32];
        {
            let mut wal =
                FsStatelessBudgetWal::create_new_for_fresh_key(&path, &root, [7; 32]).unwrap();
            assert_eq!(wal.reserve(&root, 2), Ok(1));
            assert_eq!(
                wal.reserve(&[8; 32], 2),
                Err(SigError::WalPersistenceFailed)
            );
        }
        {
            let mut wal = FsStatelessBudgetWal::open_or_recover(&path, &root, [7; 32]).unwrap();
            assert_eq!(wal.reserve(&root, 2), Ok(2));
        }
        let mut wal = FsStatelessBudgetWal::open_or_recover(&path, &root, [7; 32]).unwrap();
        assert_eq!(
            wal.reserve(&root, 2),
            Err(SigError::StatelessBudgetExhausted)
        );
        drop(wal);
        std::fs::remove_file(&path).unwrap();
        assert!(FsStatelessBudgetWal::open_or_recover(&path, &root, [7; 32]).is_err());
    }
}
