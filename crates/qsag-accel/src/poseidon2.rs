//! Width-12 canonical Goldilocks `Poseidon2` permutation (`poseidon2_perm12`), stack-streaming
//! sponge (`0` heap reallocation of secret slices!), and full-4-limb `pk_seed` Merkle layer kernel.

use crate::AccelError;
use crate::ct::ct_zeroize_u64s;
use crate::goldilocks::{gl_add, gl_mul, gl_neg, gl_reduce_u64};

/// Domain IV `"POS2_GL1"` (`0x504F_5332_5F47_4C31`), matching `lean/Qsag/Oracle/Poseidon2.lean`.
pub const POSEIDON2_CONST_IV: u64 = 0x504F_5332_5F47_4C31;
/// External half-rounds ($R_F = 8$ total).
pub const POSEIDON2_HALF_EXTERNAL_ROUNDS: u64 = 4;
/// Internal partial rounds ($R_P = 22$).
pub const POSEIDON2_INTERNAL_ROUNDS: u64 = 22;

/// Diagonal of the canonical internal matrix J + diag(-64, 1, 2, ..., 1024).
/// Its characteristic polynomial is Rabin-irreducible over Goldilocks; the tests below
/// check this for the matrix and its first 32 powers, as well as invertibility.
pub const POSEIDON2_INTERNAL_DIAG: [u64; 12] = [
    crate::goldilocks::GOLDILOCKS_PRIME - 64,
    1,
    1 << 1,
    1 << 2,
    1 << 3,
    1 << 4,
    1 << 5,
    1 << 6,
    1 << 7,
    1 << 8,
    1 << 9,
    1 << 10,
];

#[inline]
pub const fn poseidon2_rc_bijection(x: u64) -> u64 {
    let z0 = x.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let z1 = (z0 ^ (z0 >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    let z2 = (z1 ^ (z1 >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z2 ^ (z2 >> 31)
}

#[inline]
pub const fn poseidon2_const_word(tag: u64, round: u64, lane: u64) -> u64 {
    poseidon2_rc_bijection(
        poseidon2_rc_bijection(poseidon2_rc_bijection(POSEIDON2_CONST_IV ^ tag) ^ round) ^ lane,
    )
}

#[inline]
pub const fn poseidon2_const_at(tag: u64, round: u64, lane: u64) -> u64 {
    gl_reduce_u64(poseidon2_const_word(tag, round, lane))
}

#[inline]
pub const fn poseidon2_sbox7(x: u64) -> u64 {
    qsag_asm::portable::goldilocks_pow7_ct_portable(x)
}

#[inline]
const fn poseidon2_apply_m4(b: [u64; 4]) -> [u64; 4] {
    let s = gl_add(gl_add(b[0], b[1]), gl_add(b[2], b[3]));
    [
        gl_add(s, gl_add(b[0], gl_add(b[1], b[1]))),
        gl_add(s, gl_add(b[1], gl_add(b[2], b[2]))),
        gl_add(s, gl_add(b[2], gl_add(b[3], b[3]))),
        gl_add(s, gl_add(b[3], gl_add(b[0], b[0]))),
    ]
}

pub fn poseidon2_apply_me(st: &mut [u64; 12]) {
    // M4 tensor P3: transpose lanes, apply P3 tensor M4, transpose back.
    *st = [
        st[0], st[3], st[6], st[9], st[1], st[4], st[7], st[10], st[2], st[5], st[8], st[11],
    ];
    for x in st.iter_mut() {
        *x = gl_reduce_u64(*x);
    }
    let y0 = poseidon2_apply_m4([st[0], st[1], st[2], st[3]]);
    let y1 = poseidon2_apply_m4([st[4], st[5], st[6], st[7]]);
    let y2 = poseidon2_apply_m4([st[8], st[9], st[10], st[11]]);
    for i in 0..4 {
        let s = gl_add(gl_add(y0[i], y1[i]), y2[i]);
        st[i] = gl_add(y0[i], s);
        st[4 + i] = gl_add(y1[i], s);
        st[8 + i] = gl_add(y2[i], s);
    }
    *st = [
        st[0], st[4], st[8], st[1], st[5], st[9], st[2], st[6], st[10], st[3], st[7], st[11],
    ];
}

pub fn poseidon2_apply_mi(st: &mut [u64; 12]) {
    let mut s = 0u64;
    for &x in st.iter() {
        s = gl_add(s, x);
    }
    st[0] = gl_add(gl_neg(gl_mul(64, st[0])), s);
    st[1] = gl_add(st[1], s);
    let mut d = 2u64;
    for x in st.iter_mut().skip(2) {
        *x = gl_add(gl_mul(d, *x), s);
        d = gl_add(d, d);
    }
}

/// Canonical Width-12 Goldilocks `Poseidon2` permutation (`poseidon2_perm12`), matching
/// `lean/Qsag/Oracle/Poseidon2.lean` bit-for-bit.
pub fn poseidon2_perm12(st: &mut [u64; 12]) {
    poseidon2_apply_me(st);
    for r in 0..POSEIDON2_HALF_EXTERNAL_ROUNDS {
        for (lane, x) in st.iter_mut().enumerate() {
            *x = poseidon2_sbox7(gl_add(*x, poseidon2_const_at(0, r, lane as u64)));
        }
        poseidon2_apply_me(st);
    }
    for r in 0..POSEIDON2_INTERNAL_ROUNDS {
        st[0] = poseidon2_sbox7(gl_add(st[0], poseidon2_const_at(1, r, 0)));
        poseidon2_apply_mi(st);
    }
    for r in 0..POSEIDON2_HALF_EXTERNAL_ROUNDS {
        for (lane, x) in st.iter_mut().enumerate() {
            *x = poseidon2_sbox7(gl_add(*x, poseidon2_const_at(2, r, lane as u64)));
        }
        poseidon2_apply_me(st);
    }
}

/// Canonical rate-6, capacity-6 field sponge used by zk-Hem and BlindVC.
/// Starts at zero and appends a single field `1`, including an extra block at
/// exact rate boundaries. This is distinct from the domain-tagged rate-8 profile
/// [`Poseidon2Sponge`]; their digests are intentionally not interchangeable.
pub fn sponge12_rate6(message: &[u64]) -> [u64; 12] {
    let mut state = [0u64; 12];
    for chunk in message.chunks(6) {
        for (lane, &value) in state.iter_mut().zip(chunk) {
            *lane = gl_add(*lane, gl_reduce_u64(value));
        }
        if chunk.len() < 6 {
            state[chunk.len()] = gl_add(state[chunk.len()], 1);
        }
        poseidon2_perm12(&mut state);
    }
    if message.len().is_multiple_of(6) {
        state[0] = gl_add(state[0], 1);
        poseidon2_perm12(&mut state);
    }
    state
}

/// Stack-allocated zeroizing Width-12 `Poseidon2` sponge (`rate = 8`, `capacity = 4` = 256 bits)
/// with `10*1` multi-rate padding and **zero heap `Vec` allocation**.
pub struct Poseidon2Sponge {
    state: [u64; 12],
    rate_pos: usize,
}

impl Drop for Poseidon2Sponge {
    fn drop(&mut self) {
        ct_zeroize_u64s(&mut self.state);
        self.rate_pos = 0;
    }
}

impl Poseidon2Sponge {
    pub const fn new_with_domain(domain_tag: u64) -> Self {
        let mut state = [0u64; 12];
        state[8] = 8;
        state[9] = 4;
        state[10] = gl_reduce_u64(domain_tag);
        state[11] = gl_reduce_u64(POSEIDON2_CONST_IV);
        Self { state, rate_pos: 0 }
    }

    #[inline]
    pub fn absorb_limb(&mut self, limb: u64) {
        let v = gl_reduce_u64(limb);
        self.state[self.rate_pos] = gl_add(self.state[self.rate_pos], v);
        self.rate_pos += 1;
        if self.rate_pos == 8 {
            poseidon2_perm12(&mut self.state);
            self.rate_pos = 0;
        }
    }

    pub fn absorb_limbs(&mut self, limbs: &[u64]) {
        for &l in limbs {
            self.absorb_limb(l);
        }
    }

    /// Absorb an arbitrary byte slice via injective `< 2^56` 7-byte chunks (`0x01` delimiter)
    /// completely on the stack without allocating or reallocating any `Vec<u8>`.
    pub fn absorb_bytes_framed(&mut self, bytes: &[u8]) {
        self.absorb_limb(bytes.len() as u64);
        let rem = (bytes.len() + 1) % 7;
        let pad_zeros = if rem == 0 { 0 } else { 7 - rem };
        let total = bytes.len() + 1 + pad_zeros;
        let chunks = total / 7;
        for c in 0..chunks {
            let base = c * 7;
            let mut acc = 0u64;
            for j in 0..7 {
                let pos = base + j;
                let b = if pos < bytes.len() {
                    bytes[pos]
                } else if pos == bytes.len() {
                    0x01
                } else {
                    0x00
                };
                acc = (acc << 8) | (b as u64);
            }
            self.absorb_limb(acc);
        }
    }

    /// Apply `10*1` multi-rate sponge padding and squeeze 4 canonical Goldilocks limbs (256-bit capacity).
    pub fn finalize_digest4(mut self) -> [u64; 4] {
        if self.rate_pos == 7 {
            self.state[7] = gl_add(self.state[7], (1u64 << 56) + 1);
        } else {
            self.state[self.rate_pos] = gl_add(self.state[self.rate_pos], 1);
            self.state[7] = gl_add(self.state[7], 1u64 << 56);
        }
        poseidon2_perm12(&mut self.state);
        [self.state[0], self.state[1], self.state[2], self.state[3]]
    }
}

/// Hash a slice of Goldilocks limbs under `domain_tag` to 4 canonical Goldilocks limbs.
pub fn poseidon2_hash_limbs(domain_tag: u64, limbs: &[u64]) -> [u64; 4] {
    let mut sp = Poseidon2Sponge::new_with_domain(domain_tag);
    sp.absorb_limbs(limbs);
    sp.finalize_digest4()
}

/// Hash length-framed byte slices via `Poseidon2` into 4 canonical Goldilocks limbs.
pub fn poseidon2_hash_framed_limbs4(domain_tag: u64, frames: &[&[u8]]) -> [u64; 4] {
    let mut sp = Poseidon2Sponge::new_with_domain(domain_tag);
    sp.absorb_limb(frames.len() as u64);
    for f in frames {
        sp.absorb_bytes_framed(f);
    }
    sp.finalize_digest4()
}

/// Shape contract of a Merkle layer job, shared by every backend: two children per parent and
/// every global parent index `start_parent_idx + i` inside `0..=u32::MAX`.
pub(crate) fn merkle_layer_shape(
    children_len: usize,
    parents_len: usize,
    start_parent_idx: u64,
) -> Result<(), AccelError> {
    let expected_children = parents_len
        .checked_mul(2)
        .ok_or(AccelError::LengthOverflow)?;
    if children_len != expected_children {
        return Err(AccelError::LengthMismatch {
            what: "Merkle layer children",
            expected: expected_children,
            actual: children_len,
        });
    }
    let last_offset = parents_len.saturating_sub(1) as u64;
    match start_parent_idx.checked_add(last_offset) {
        Some(max_parent_idx) if max_parent_idx <= u32::MAX as u64 => Ok(()),
        _ => Err(AccelError::LengthOverflow),
    }
}

/// Position-tweaked batch Poseidon2 Merkle tree compression layer binding **all 4 limbs
/// `pk_seed[0..4]`**, `layer`, and per-node global parent index `start_parent_idx + parent_idx`!
///
/// Batch tree build passes `start_parent_idx = 0`, while 1-node sibling path verification at
/// child index `idx` passes `start_parent_idx = (idx >> 1) as u64`, guaranteeing exact equivalence
/// AND FIPS-205-grade intra-layer node position separation.
///
/// Supported parent indices lie in `0..=u32::MAX` (`<= 2^32 - 1`), over which
/// `0x4C52_5F4E_4F44_4531 + idx < GOLDILOCKS_PRIME` is strictly injective without `u64` or modular
/// wrap; larger indices return [`AccelError::LengthOverflow`].
///
/// # Scope of the position separation
///
/// The capacity lanes are the sums `pk_seed + (domain(layer), layer, node(idx), IV)`, and the
/// weighted output reads those same sums. The node function therefore depends on the key and
/// the position only through them:
///
/// * **One key.** For a fixed `pk_seed` the map `(layer, idx) -> capacity` is injective over
///   `layer, idx <= u32::MAX`. Two positions of one tree never share a function.
/// * **Several keys.** The separation is per key, not per `(key, position)` pair. The keys
///   `pk_seed` and `pk_seed + (0, 0, d, 0)` have the same function at positions `idx` and
///   `idx - d` of one layer, and a layer shift is absorbed the same way by limbs 0 and 1. A
///   party that derives its seed from another key's seed can so reproduce single nodes of
///   that key at shifted positions, for equal children. It cannot reproduce an authentication
///   path up to a root: the shift would have to be the same at every layer while both indices
///   halve, which forces `d = 0`. Two uniform seeds are related this way with probability about
///   `2^-192` per offset.
///
/// A security argument that needs distinct functions for distinct `(key, position)` pairs
/// across adversarially chosen keys does not get them from this layer. The construction is
/// shared bit for bit with `merkle_layer_poseidon2.comp`, `qsag_core::poseidon2_mpc` and the
/// trees already derived from it, so it is pinned here by
/// `merkle_position_separation_is_per_key`.
pub fn merkle_layer_poseidon2_at_cpu(
    children: &[[u64; 4]],
    pk_seed: &[u64; 4],
    layer: u32,
    start_parent_idx: u64,
    out_parents: &mut [[u64; 4]],
) -> Result<(), AccelError> {
    merkle_layer_shape(children.len(), out_parents.len(), start_parent_idx)?;
    let s0 = gl_reduce_u64(pk_seed[0]);
    let s1 = gl_reduce_u64(pk_seed[1]);
    let s2 = gl_reduce_u64(pk_seed[2]);
    let s3 = gl_reduce_u64(pk_seed[3]);

    const MERKLE_DOMAIN_IV: u64 = 0x4D52_4B4C_5F50_3231;
    let tweak = gl_reduce_u64(MERKLE_DOMAIN_IV.wrapping_add((layer as u64) << 32));

    for (parent_idx, parent_out) in out_parents.iter_mut().enumerate() {
        let left = &children[2 * parent_idx];
        let right = &children[2 * parent_idx + 1];
        let l0 = gl_reduce_u64(left[0]);
        let l1 = gl_reduce_u64(left[1]);
        let l2 = gl_reduce_u64(left[2]);
        let l3 = gl_reduce_u64(left[3]);
        let r0 = gl_reduce_u64(right[0]);
        let r1 = gl_reduce_u64(right[1]);
        let r2 = gl_reduce_u64(right[2]);
        let r3 = gl_reduce_u64(right[3]);

        let node_tweak = gl_reduce_u64(
            0x4C52_5F4E_4F44_4531u64.wrapping_add(start_parent_idx.wrapping_add(parent_idx as u64)),
        );

        // Rate lanes 0..8 hold left || right; capacity lanes 8..12 bind ALL FOUR pk_seed[0..4] limbs
        // plus `(layer, start_parent_idx + parent_idx)`!
        let mut st: [u64; 12] = [
            l0,
            l1,
            l2,
            l3,
            r0,
            r1,
            r2,
            r3,
            gl_add(s0, tweak),
            gl_add(s1, layer as u64),
            gl_add(s2, node_tweak),
            gl_add(s3, POSEIDON2_CONST_IV),
        ];
        let tweak4 = [st[8], st[9], st[10], st[11]];
        poseidon2_perm12(&mut st);

        // Weighted Jive binds both children and the full domain/position tweak.
        parent_out[0] = gl_add(
            st[0],
            gl_add(l0, gl_add(gl_mul(2, r0), gl_mul(4, tweak4[0]))),
        );
        parent_out[1] = gl_add(
            st[1],
            gl_add(l1, gl_add(gl_mul(2, r1), gl_mul(4, tweak4[1]))),
        );
        parent_out[2] = gl_add(
            st[2],
            gl_add(l2, gl_add(gl_mul(2, r2), gl_mul(4, tweak4[2]))),
        );
        parent_out[3] = gl_add(
            st[3],
            gl_add(l3, gl_add(gl_mul(2, r3), gl_mul(4, tweak4[3]))),
        );
        ct_zeroize_u64s(&mut st);
    }
    Ok(())
}

/// Canonical 64-bit domain constant for `qsag-agg` two-block binary Merkle nodes (`0x5153_4147_4D52_4B4C`).
pub const POSEIDON2_MERKLE_NODE_DOMAIN: u64 = 0x5153_4147_4D52_4B4C;
/// Canonical 64-bit domain constant for `qsag-agg` FORS binary Merkle nodes (`0x5153_4147_464E_4F44`).
pub const POSEIDON2_FORS_NODE_DOMAIN: u64 = 0x5153_4147_464E_4F44;
/// Canonical domain constant for `Poseidon2` WHIR Canopy per-tree key derivation (`0x5032_434E_534C_5401`).
pub const POSEIDON2_CANOPY_SALT_DOMAIN: u64 = 0x5032_434E_534C_5401;
/// High 32-bit prefix OR-ed with `node_idx: u32` in `Poseidon2` WHIR Canopy internal nodes (`0x5032_4E44_0000_0000`).
pub const POSEIDON2_CANOPY_NODE_HI: u64 = 0x5032_4E44_0000_0000;
/// Canonical domain constant for `Poseidon2` WHIR Canopy root commitment binding (`0x5032_434E_524F_4F54`).
pub const POSEIDON2_CANOPY_ROOT_DOMAIN: u64 = 0x5032_434E_524F_4F54;

/// Tree coordinates for the 2-block full-`pk_seed[0..4]` `Poseidon2` binary Merkle node sponge.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Poseidon2Merkle2BlockAddr {
    /// Hypertree layer (`<= 0xFFFE` so `(layer << 48) | (level << 32) | node_idx < p`).
    pub layer: u32,
    /// 64-bit hypertree / subtree index, split into two injective 32-bit canonical limbs.
    pub tree_idx: u64,
    /// Height level above the leaves (`<= 0xFFFF`).
    pub level: u32,
    /// Starting `node_idx` within `level` (`start_node_idx + out_parents.len() - 1 <= u32::MAX`).
    pub start_node_idx: u64,
}

/// Domain-separated, length-framed Width-12 Rate-8 `Poseidon2` sponge over `Goldilocks` limbs,
/// matching `qsag_agg::sponge::poseidon2_sponge_hash_limbs` bit-for-bit.
pub fn poseidon2_sponge_hash_limbs_with_cap(
    domain_tag: u64,
    init_cap: [u64; 4],
    limbs: &[u64],
) -> [u64; 4] {
    let mut st = [0u64; 12];
    for (dst, &cap) in st[8..].iter_mut().zip(&init_cap) {
        *dst = gl_reduce_u64(cap);
    }
    let absorb = |st: &mut [u64; 12], block: &[u64; 8]| {
        for (lane, &val) in st[..8].iter_mut().zip(block) {
            *lane = crate::goldilocks::gl_reduce128(*lane as u128 + val as u128);
        }
        poseidon2_perm12(st);
    };
    let mut block = [0u64; 8];
    block[0] = gl_reduce_u64(domain_tag);
    block[1] = gl_reduce_u64(limbs.len() as u64);
    let head = limbs.len().min(6);
    for (dst, &limb) in block[2..2 + head].iter_mut().zip(limbs) {
        *dst = gl_reduce_u64(limb);
    }
    absorb(&mut st, &block);
    ct_zeroize_u64s(&mut block);

    let mut pos = head;
    while pos + 8 <= limbs.len() {
        let mut full = [0u64; 8];
        for i in 0..8 {
            full[i] = gl_reduce_u64(limbs[pos + i]);
        }
        absorb(&mut st, &full);
        ct_zeroize_u64s(&mut full);
        pos += 8;
    }
    if pos < limbs.len() {
        let mut tail_blk = [0u64; 8];
        for (dst, &limb) in tail_blk.iter_mut().zip(&limbs[pos..]) {
            *dst = gl_reduce_u64(limb);
        }
        absorb(&mut st, &tail_blk);
        ct_zeroize_u64s(&mut tail_blk);
    }
    let out = [
        gl_reduce_u64(st[0]),
        gl_reduce_u64(st[1]),
        gl_reduce_u64(st[2]),
        gl_reduce_u64(st[3]),
    ];
    ct_zeroize_u64s(&mut st);
    out
}

/// Derive the per-tree capacity key `tree_key` for a `Poseidon2` WHIR Canopy tree, matching
/// `qsag_agg::sponge::poseidon2_canopy_tree_key`.
#[inline]
pub fn poseidon2_canopy_tree_key_cpu(
    stage_idx: u8,
    log_leaves: u8,
    tree_salt: [u64; 4],
) -> [u64; 4] {
    poseidon2_sponge_hash_limbs_with_cap(
        POSEIDON2_CANOPY_SALT_DOMAIN,
        tree_salt,
        &[stage_idx as u64, log_leaves as u64],
    )
}

/// Bind a `Poseidon2` WHIR Canopy tree's top node `nodes[1]` to `(stage_idx, log_leaves, tree_salt)`,
/// matching `qsag_agg::sponge::poseidon2_canopy_root`.
#[inline]
pub fn poseidon2_canopy_root_cpu(
    stage_idx: u8,
    log_leaves: u8,
    tree_salt: [u64; 4],
    top_node: [u64; 4],
) -> [u64; 4] {
    poseidon2_sponge_hash_limbs_with_cap(
        POSEIDON2_CANOPY_ROOT_DOMAIN,
        tree_salt,
        &[
            stage_idx as u64,
            log_leaves as u64,
            gl_reduce_u64(top_node[0]),
            gl_reduce_u64(top_node[1]),
            gl_reduce_u64(top_node[2]),
            gl_reduce_u64(top_node[3]),
        ],
    )
}

/// Validate shape and canonical Goldilocks framing range (`layer <= 0xFFFE`, `level <= 0xFFFF`,
/// `start_node_idx + parents_len - 1 <= u32::MAX`) for a 2-block `Poseidon2` Merkle layer.
pub(crate) fn merkle_layer_2block_shape(
    children_len: usize,
    parents_len: usize,
    addr: Poseidon2Merkle2BlockAddr,
) -> Result<(), AccelError> {
    merkle_layer_shape(children_len, parents_len, addr.start_node_idx)?;
    if addr.layer > 0xFFFE || addr.level > 0xFFFF {
        return Err(AccelError::LengthOverflow);
    }
    Ok(())
}

/// CPU reference for the 2-block full-`pk_seed[0..4]` `Poseidon2` binary Merkle node sponge
/// (`merkle_node_hash` in `qsag-agg`), matching `merkle_layer_poseidon2.comp` (`pc.mode == 1`)
/// bit-for-bit.
pub fn merkle_layer_poseidon2_2block_at_cpu(
    children: &[[u64; 4]],
    domain_tag: u64,
    pk_seed: &[u64; 4],
    addr: Poseidon2Merkle2BlockAddr,
    out_parents: &mut [[u64; 4]],
) -> Result<(), AccelError> {
    merkle_layer_2block_shape(children.len(), out_parents.len(), addr)?;
    let s0 = gl_reduce_u64(pk_seed[0]);
    let s1 = gl_reduce_u64(pk_seed[1]);
    let s2 = gl_reduce_u64(pk_seed[2]);
    let s3 = gl_reduce_u64(pk_seed[3]);
    let dom = gl_reduce_u64(domain_tag);
    let tree_lo = gl_reduce_u64(addr.tree_idx & 0xFFFF_FFFF);
    let tree_hi = gl_reduce_u64(addr.tree_idx >> 32);
    let const_iv = gl_reduce_u64(POSEIDON2_CONST_IV);

    for (parent_idx, parent_out) in out_parents.iter_mut().enumerate() {
        let left = &children[2 * parent_idx];
        let right = &children[2 * parent_idx + 1];
        let node_idx = addr.start_node_idx + (parent_idx as u64);
        let meta0 = ((addr.layer as u64) << 48) | ((addr.level as u64) << 32) | node_idx;

        let mut st: [u64; 12] = [
            s0,
            s1,
            s2,
            s3,
            gl_reduce_u64(left[0]),
            gl_reduce_u64(left[1]),
            gl_reduce_u64(left[2]),
            gl_reduce_u64(left[3]),
            dom,
            gl_reduce_u64(meta0),
            tree_lo,
            tree_hi,
        ];
        poseidon2_perm12(&mut st);

        st[0] = gl_add(st[0], right[0]);
        st[1] = gl_add(st[1], right[1]);
        st[2] = gl_add(st[2], right[2]);
        st[3] = gl_add(st[3], right[3]);
        st[4] = gl_add(st[4], 1);
        st[5] = gl_add(st[5], const_iv);
        poseidon2_perm12(&mut st);

        *parent_out = [st[0], st[1], st[2], st[3]];
        ct_zeroize_u64s(&mut st);
    }
    Ok(())
}

/// CPU reference for `Poseidon2` WHIR Canopy internal node compression (`1` permutation Weighted Jive),
/// binding 1-indexed binary heap `node_idx = start_node_idx + parent_idx` and `tree_key[0..3]`,
/// matching `qsag_agg::sponge::poseidon2_canopy_internal` and `merkle_layer_poseidon2.comp` (`pc.mode == 2`).
pub fn merkle_layer_poseidon2_canopy_at_cpu(
    children: &[[u64; 4]],
    tree_key: &[u64; 4],
    start_node_idx: u64,
    out_parents: &mut [[u64; 4]],
) -> Result<(), AccelError> {
    merkle_layer_shape(children.len(), out_parents.len(), start_node_idx)?;
    let k0 = gl_reduce_u64(tree_key[0]);
    let k1 = gl_reduce_u64(tree_key[1]);
    let k2 = gl_reduce_u64(tree_key[2]);

    for (parent_idx, parent_out) in out_parents.iter_mut().enumerate() {
        let left = &children[2 * parent_idx];
        let right = &children[2 * parent_idx + 1];
        let l0 = gl_reduce_u64(left[0]);
        let l1 = gl_reduce_u64(left[1]);
        let l2 = gl_reduce_u64(left[2]);
        let l3 = gl_reduce_u64(left[3]);
        let r0 = gl_reduce_u64(right[0]);
        let r1 = gl_reduce_u64(right[1]);
        let r2 = gl_reduce_u64(right[2]);
        let r3 = gl_reduce_u64(right[3]);
        let node_idx = (start_node_idx + parent_idx as u64) & 0xFFFF_FFFF;
        let t0 = gl_reduce_u64(POSEIDON2_CANOPY_NODE_HI | node_idx);

        let mut st: [u64; 12] = [l0, l1, l2, l3, r0, r1, r2, r3, t0, k0, k1, k2];
        poseidon2_perm12(&mut st);

        parent_out[0] = gl_add(st[0], gl_add(l0, gl_add(gl_mul(2, r0), gl_mul(4, t0))));
        parent_out[1] = gl_add(st[1], gl_add(l1, gl_add(gl_mul(2, r1), gl_mul(4, k0))));
        parent_out[2] = gl_add(st[2], gl_add(l2, gl_add(gl_mul(2, r2), gl_mul(4, k1))));
        parent_out[3] = gl_add(st[3], gl_add(l3, gl_add(gl_mul(2, r3), gl_mul(4, k2))));
        ct_zeroize_u64s(&mut st);
    }
    Ok(())
}

/// CPU reference for fixed-tweak `Poseidon2` Weighted Jive Merkle compression (`pc.mode == 3`),
/// matching `qsag_agg::zk_hem::recursive_whir::compress` bit-for-bit.
pub fn merkle_layer_poseidon2_fixed_tweak_cpu(
    children: &[[u64; 4]],
    tweak: &[u64; 4],
    out_parents: &mut [[u64; 4]],
) -> Result<(), AccelError> {
    merkle_layer_shape(children.len(), out_parents.len(), 0)?;
    let t0 = gl_reduce_u64(tweak[0]);
    let t1 = gl_reduce_u64(tweak[1]);
    let t2 = gl_reduce_u64(tweak[2]);
    let t3 = gl_reduce_u64(tweak[3]);

    for (parent_idx, parent_out) in out_parents.iter_mut().enumerate() {
        let left = &children[2 * parent_idx];
        let right = &children[2 * parent_idx + 1];
        let l0 = gl_reduce_u64(left[0]);
        let l1 = gl_reduce_u64(left[1]);
        let l2 = gl_reduce_u64(left[2]);
        let l3 = gl_reduce_u64(left[3]);
        let r0 = gl_reduce_u64(right[0]);
        let r1 = gl_reduce_u64(right[1]);
        let r2 = gl_reduce_u64(right[2]);
        let r3 = gl_reduce_u64(right[3]);

        let mut st: [u64; 12] = [l0, l1, l2, l3, r0, r1, r2, r3, t0, t1, t2, t3];
        poseidon2_perm12(&mut st);

        parent_out[0] = gl_add(st[0], gl_add(l0, gl_add(gl_mul(2, r0), gl_mul(4, t0))));
        parent_out[1] = gl_add(st[1], gl_add(l1, gl_add(gl_mul(2, r1), gl_mul(4, t1))));
        parent_out[2] = gl_add(st[2], gl_add(l2, gl_add(gl_mul(2, r2), gl_mul(4, t2))));
        parent_out[3] = gl_add(st[3], gl_add(l3, gl_add(gl_mul(2, r3), gl_mul(4, t3))));
        ct_zeroize_u64s(&mut st);
    }
    Ok(())
}

#[cfg(test)]
mod merkle_tweak_tests {
    use super::*;

    fn node(pk_seed: [u64; 4], layer: u32, idx: u64) -> [u64; 4] {
        let children = [[11, 12, 13, 14], [21, 22, 23, 24]];
        let mut out = [[0u64; 4]];
        merkle_layer_poseidon2_at_cpu(&children, &pk_seed, layer, idx, &mut out).unwrap();
        out[0]
    }

    #[test]
    fn merkle_position_separation_is_per_key() {
        let seed = [0x1111, 0x2222, 0x3333, 0x4444];
        // One key: every position of a grid, including the index bounds, is its own function.
        let mut seen = std::vec::Vec::new();
        for layer in [0, 1, 2, 31, u32::MAX] {
            for idx in [0, 1, 2, 3, 1 << 20, u64::from(u32::MAX)] {
                let digest = node(seed, layer, idx);
                assert!(!seen.contains(&digest), "layer {layer}, index {idx}");
                seen.push(digest);
            }
        }
        // Across keys the tweak is additive: a seed shifted in limb 2 meets the original
        // key at the position shifted back, and limbs 0 and 1 absorb a layer shift.
        let shifted = [seed[0], seed[1], seed[2] + 5, seed[3]];
        assert_eq!(node(shifted, 3, 7), node(seed, 3, 12));
        assert_ne!(node(shifted, 3, 7), node(seed, 3, 7));
        let relayered = [seed[0] + (1 << 32), seed[1] + 1, seed[2], seed[3]];
        assert_eq!(node(relayered, 3, 7), node(seed, 4, 7));
        // No single shift survives two layers of one path: parent indices halve.
        assert_ne!(node(shifted, 4, 3), node(seed, 4, 6));
    }
}

#[cfg(test)]
mod internal_matrix_tests {
    use super::*;
    use crate::goldilocks::{gl_inv_or_zero, gl_sub};

    const T: usize = 12;
    type Mat = [[u64; T]; T];
    type Poly = [u64; T + 1];

    fn matrix_from_diag(diag: &[u64; T]) -> Mat {
        let mut m = [[1u64; T]; T];
        for (i, row) in m.iter_mut().enumerate() {
            row[i] = gl_add(1, diag[i]);
        }
        m
    }

    fn mat_mul(a: &Mat, b: &Mat) -> Mat {
        let mut out = [[0u64; T]; T];
        for i in 0..T {
            for j in 0..T {
                let mut acc = 0u64;
                for (k, b_row) in b.iter().enumerate() {
                    acc = gl_add(acc, gl_mul(a[i][k], b_row[j]));
                }
                out[i][j] = acc;
            }
        }
        out
    }

    fn mat_vec(a: &Mat, v: &[u64; T]) -> [u64; T] {
        core::array::from_fn(|i| {
            let mut acc = 0u64;
            for j in 0..T {
                acc = gl_add(acc, gl_mul(a[i][j], v[j]));
            }
            acc
        })
    }

    fn vec_mat(v: &[u64; T], a: &Mat) -> [u64; T] {
        core::array::from_fn(|j| {
            let mut acc = 0u64;
            for i in 0..T {
                acc = gl_add(acc, gl_mul(v[i], a[i][j]));
            }
            acc
        })
    }

    /// Row-reduce `rows` in place; returns `(rank, determinant)`.
    fn rank_and_det(mut rows: Mat) -> (usize, u64) {
        let mut rank = 0usize;
        let mut det = 1u64;
        for col in 0..T {
            let Some(pivot) = (rank..T).find(|&r| rows[r][col] != 0) else {
                det = 0;
                continue;
            };
            if pivot != rank {
                rows.swap(pivot, rank);
                det = gl_neg(det);
            }
            det = gl_mul(det, rows[rank][col]);
            let pivot_row = rows[rank];
            let inv = gl_inv_or_zero(pivot_row[col]);
            for row in rows.iter_mut().take(T).skip(rank + 1) {
                let factor = gl_mul(row[col], inv);
                if factor != 0 {
                    for (cell, &piv) in row[col..T].iter_mut().zip(&pivot_row[col..T]) {
                        *cell = gl_sub(*cell, gl_mul(factor, piv));
                    }
                }
            }
            rank += 1;
        }
        (rank, det)
    }

    /// Monic characteristic polynomial (coefficients low-to-high) by Faddeev-LeVerrier.
    fn char_poly(a: &Mat) -> Poly {
        let mut c = [0u64; T + 1];
        c[T] = 1;
        let mut m = [[0u64; T]; T];
        for k in 1..=T {
            m = mat_mul(a, &m);
            for (i, row) in m.iter_mut().enumerate() {
                row[i] = gl_add(row[i], c[T - k + 1]);
            }
            let am = mat_mul(a, &m);
            let mut trace = 0u64;
            for (i, row) in am.iter().enumerate() {
                trace = gl_add(trace, row[i]);
            }
            c[T - k] = gl_neg(gl_mul(trace, gl_inv_or_zero(k as u64)));
        }
        c
    }

    fn degree(f: &[u64]) -> Option<usize> {
        f.iter().rposition(|&c| c != 0)
    }

    /// `a * b mod f` for monic `f` of degree `n = f.len() - 1`; `a`, `b` have `n` coefficients.
    fn poly_mul_mod(a: &[u64], b: &[u64], f: &[u64]) -> [u64; T] {
        let n = f.len() - 1;
        let mut wide = [0u64; 2 * T];
        for i in 0..n {
            for j in 0..n {
                wide[i + j] = gl_add(wide[i + j], gl_mul(a[i], b[j]));
            }
        }
        for i in (n..2 * n).rev() {
            let c = wide[i];
            if c != 0 {
                for j in 0..n {
                    wide[i - n + j] = gl_sub(wide[i - n + j], gl_mul(c, f[j]));
                }
                wide[i] = 0;
            }
        }
        let mut out = [0u64; T];
        out[..n].copy_from_slice(&wide[..n]);
        out
    }

    /// `a^p mod f` where `p` is the Goldilocks prime (the Frobenius map on `F_p[x]/(f)`).
    fn frobenius(a: &[u64; T], f: &[u64]) -> [u64; T] {
        let mut result = [0u64; T];
        result[0] = 1;
        let mut base = *a;
        let mut e = crate::goldilocks::GOLDILOCKS_PRIME;
        while e > 0 {
            if e & 1 == 1 {
                result = poly_mul_mod(&result, &base, f);
            }
            base = poly_mul_mod(&base, &base, f);
            e >>= 1;
        }
        result
    }

    /// Monic gcd, returned as `(coefficients, degree)`.
    fn poly_gcd(a: &[u64], b: &[u64]) -> ([u64; T + 1], usize) {
        let mut x = [0u64; T + 1];
        let mut y = [0u64; T + 1];
        x[..a.len()].copy_from_slice(a);
        y[..b.len()].copy_from_slice(b);
        while let Some(dy) = degree(&y) {
            let inv = gl_inv_or_zero(y[dy]);
            while let Some(dx) = degree(&x) {
                if dx < dy {
                    break;
                }
                let c = gl_mul(x[dx], inv);
                for j in 0..=dy {
                    x[dx - dy + j] = gl_sub(x[dx - dy + j], gl_mul(c, y[j]));
                }
            }
            core::mem::swap(&mut x, &mut y);
        }
        let d = degree(&x).expect("gcd of nonzero polynomials");
        let inv = gl_inv_or_zero(x[d]);
        for c in x.iter_mut() {
            *c = gl_mul(*c, inv);
        }
        (x, d)
    }

    /// `x^(p^i) mod f` for `i = 1..=n`, `n = deg f >= 2`.
    fn frobenius_orbit(f: &[u64]) -> [[u64; T]; T] {
        let n = f.len() - 1;
        let mut cur = [0u64; T];
        cur[1] = 1;
        let mut orbit = [[0u64; T]; T];
        for slot in orbit.iter_mut().take(n) {
            cur = frobenius(&cur, f);
            *slot = cur;
        }
        orbit
    }

    /// Rabin irreducibility test for monic `f` of degree `n >= 2`.
    fn is_irreducible(f: &[u64]) -> bool {
        let n = f.len() - 1;
        let orbit = frobenius_orbit(f);
        let mut x = [0u64; T];
        x[1] = 1;
        if orbit[n - 1] != x {
            return false;
        }
        for q in [2usize, 3, 5, 7, 11] {
            if !n.is_multiple_of(q) {
                continue;
            }
            let mut h = orbit[n / q - 1];
            h[1] = gl_sub(h[1], 1);
            if degree(&h[..n]).is_none() || poly_gcd(f, &h[..n]).1 != 0 {
                return false;
            }
        }
        true
    }

    fn krylov_ranks(m: &Mat) -> (usize, usize) {
        let mut e0 = [0u64; T];
        e0[0] = 1;
        let (mut row, mut col) = (e0, e0);
        let mut observe = [[0u64; T]; T];
        let mut control = [[0u64; T]; T];
        for (o, c) in observe.iter_mut().zip(control.iter_mut()) {
            *o = row;
            *c = col;
            row = vec_mat(&row, m);
            col = mat_vec(m, &col);
        }
        (rank_and_det(observe).0, rank_and_det(control).0)
    }

    #[test]
    fn apply_mi_is_all_ones_plus_declared_diagonal() {
        let expected = matrix_from_diag(&POSEIDON2_INTERNAL_DIAG);
        for j in 0..T {
            let mut unit = [0u64; T];
            unit[j] = 1;
            poseidon2_apply_mi(&mut unit);
            for i in 0..T {
                assert_eq!(unit[i], expected[i][j], "column {j}, row {i}");
            }
        }
    }

    #[test]
    fn internal_matrix_determinant_matches_closed_form_and_is_nonzero() {
        let m = matrix_from_diag(&POSEIDON2_INTERNAL_DIAG);
        let (rank, det) = rank_and_det(m);
        assert_eq!(rank, T);
        let mut prod = 1u64;
        let mut inv_sum = 1u64;
        for &v in &POSEIDON2_INTERNAL_DIAG {
            assert_ne!(v, 0);
            prod = gl_mul(prod, v);
            inv_sum = gl_add(inv_sum, gl_inv_or_zero(v));
        }
        assert_ne!(inv_sum, 0);
        assert_eq!(gl_mul(inv_sum, 1024), 3055);
        assert_eq!(det, gl_mul(prod, inv_sum));
        assert_ne!(det, 0);
    }

    #[test]
    fn no_invariant_subspace_avoids_or_contains_the_sbox_lane_for_matrix_powers() {
        let m = matrix_from_diag(&POSEIDON2_INTERNAL_DIAG);
        let mut power = m;
        for k in 1..=64 {
            assert_eq!(krylov_ranks(&power), (T, T), "M_I^{k}");
            power = mat_mul(&power, &m);
        }
    }

    #[test]
    fn characteristic_polynomial_is_irreducible_for_first_32_powers() {
        let m = matrix_from_diag(&POSEIDON2_INTERNAL_DIAG);
        let mut power = m;
        for k in 1..=32 {
            assert!(is_irreducible(&char_poly(&power)), "M_I^{k}");
            power = mat_mul(&power, &m);
        }
    }

    #[test]
    fn irreducibility_test_separates_known_polynomials() {
        // x^2 - 7 is irreducible (7 is a non-residue); x^2 - 4 = (x - 2)(x + 2) is not.
        assert!(is_irreducible(&[gl_neg(7), 0, 1]));
        assert!(!is_irreducible(&[gl_neg(4), 0, 1]));
    }
}

#[cfg(test)]
mod canonical_kat {
    use super::*;
    #[test]
    fn poseidon2_canonical_sequence_kat() {
        let mut st = core::array::from_fn(|i| i as u64);
        poseidon2_perm12(&mut st);
        assert_eq!(
            st,
            [
                13782584570844608145,
                13136387643152332171,
                7171133015474200819,
                7643370872200861694,
                14144755201299840503,
                16470027036684692562,
                1748465969625202405,
                1718729118078964347,
                6141020819996733037,
                16322330185628708898,
                11650380702735067362,
                2734959974607798415
            ]
        );
    }
}
