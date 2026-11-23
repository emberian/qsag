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

// ============================================================================
// Width-24 Goldilocks `Poseidon2-GL-w24` (`rate = 16, capacity = 8`, 7-limb digest)
// ============================================================================

/// State width $w = 24 = 6 \times 4$ lanes (`rate = 16`, `capacity = 8`).
pub const POSEIDON2_GL24_WIDTH: usize = 24;
/// Rate lanes (`0..16`), fitting two 7-limb child digests + 2 tweak limbs (`7 + 7 + 2 = 16`) in 1 call.
pub const POSEIDON2_GL24_RATE: usize = 16;
/// Capacity lanes (`16..24`, $p^8 \approx 2^{512.00}$, `235.3` QROM sponge bits at $t = 2^{88}$).
pub const POSEIDON2_GL24_CAPACITY: usize = 8;
/// Digest output width (`7` canonical Goldilocks limbs = `56` bytes, `171.3` QROM collision bits).
pub const POSEIDON2_GL24_DIGEST_LIMBS: usize = 7;
/// External half-rounds ($R_F = 8 = 4 + 4$).
pub const POSEIDON2_GL24_HALF_EXTERNAL_ROUNDS: usize = 4;
/// GSR-hardened (`ePrint 2026/1692`) internal partial rounds ($R_P = 44$).
pub const POSEIDON2_GL24_INTERNAL_ROUNDS: usize = 44;
/// Total $x^7$ S-boxes per Width-24 permutation (`8 * 24 + 44 = 236`).
pub const POSEIDON2_GL24_SBOX_COUNT: usize =
    2 * POSEIDON2_GL24_HALF_EXTERNAL_ROUNDS * POSEIDON2_GL24_WIDTH + POSEIDON2_GL24_INTERNAL_ROUNDS;
/// Domain IV `"POS2GL24"` (`0x504F_5332_474C_3234`).
pub const POSEIDON2_GL24_IV: u64 = 0x504F_5332_474C_3234;
/// 2-to-1 Merkle compression domain tag `"MRKLGL24"` (`0x4D52_4B4C_474C_3234`).
pub const POSEIDON2_GL24_MERKLE_TAG: u64 = 0x4D52_4B4C_474C_3234;

/// Shift-only diagonal of $M_I = J_{24} + \mathrm{diag}(-2^{23}, 1, 2, 4, \dots, 2^{22})$.
/// Characteristic polynomial is Rabin-irreducible of degree 24 over Goldilocks, with maximal
/// nonzero-sum branch number `25`.
pub const POSEIDON2_GL24_INTERNAL_DIAG: [u64; 24] = [
    crate::goldilocks::GOLDILOCKS_PRIME - (1u64 << 23),
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
    1 << 11,
    1 << 12,
    1 << 13,
    1 << 14,
    1 << 15,
    1 << 16,
    1 << 17,
    1 << 18,
    1 << 19,
    1 << 20,
    1 << 21,
    1 << 22,
];

/// Deterministic 80-bit Poseidon2 Grain-LFSR generator (`field = 1`, `sbox = 0`, `n = 64`,
/// `t = 24`, `R_F = 8`, `R_P = 44`), producing all `236` canonical Goldilocks round constants.
pub const fn poseidon2_gl24_grain_constants() -> [u64; POSEIDON2_GL24_SBOX_COUNT] {
    let mut bits = [0u8; 80];
    let mut pos = 0usize;

    macro_rules! push_be {
        ($val:expr, $width:expr) => {{
            let mut i = $width;
            while i > 0 {
                i -= 1;
                bits[pos] = (($val >> i) & 1) as u8;
                pos += 1;
            }
        }};
    }

    push_be!(1u32, 2);
    push_be!(0u32, 4);
    push_be!(64u32, 12);
    push_be!(24u32, 12);
    push_be!(8u32, 10);
    push_be!(44u32, 10);
    while pos < 80 {
        bits[pos] = 1;
        pos += 1;
    }

    macro_rules! clock {
        () => {{
            let nb = bits[62] ^ bits[51] ^ bits[38] ^ bits[23] ^ bits[13] ^ bits[0];
            let mut j = 0usize;
            while j < 79 {
                bits[j] = bits[j + 1];
                j += 1;
            }
            bits[79] = nb;
            nb
        }};
    }

    let mut warm = 0usize;
    while warm < 160 {
        let _ = clock!();
        warm += 1;
    }

    let mut out = [0u64; POSEIDON2_GL24_SBOX_COUNT];
    let mut idx = 0usize;
    while idx < POSEIDON2_GL24_SBOX_COUNT {
        let elem = loop {
            let mut val = 0u64;
            let mut b = 0usize;
            while b < 64 {
                let b1 = clock!();
                let b2 = clock!();
                if b1 == 1 {
                    val = (val << 1) | (b2 as u64);
                    b += 1;
                }
            }
            if val < crate::goldilocks::GOLDILOCKS_PRIME {
                break val;
            }
        };
        out[idx] = elem;
        idx += 1;
    }
    out
}

/// Precomputed Grain-LFSR round constants for `Poseidon2-GL-w24` (`(R_F, R_P) = (8, 44)`):
/// `[0..96)` initial 4 external rounds, `[96..140)` 44 internal partial rounds, `[140..236)` terminal 4 external rounds.
pub const POSEIDON2_GL24_RC: [u64; 236] = [
    0xD5BF8AE11C92B989, 0x260F9DF9310DFA25, 0x592432578A606550, 0xBBA16923E2A2D02F,
    0x8186E689E4D19FE2, 0x6710500744D40C61, 0x94AB290278034115, 0x09E5E099E84C8CED,
    0x837D929C50E40826, 0xA70DC82E9B01D522, 0x31935D3C3E0F8A5A, 0x43E7EF85F89C6EF6,
    0x2D825D978F0DB37D, 0x10DF4F507965E5D1, 0x2BEFD14E9F68FD6C, 0xCCC326E2586546FC,
    0xDF9019005948354A, 0x9DB550A181AD3921, 0x96F3555B2A083851, 0xB5E8DDBEB0793433,
    0x64C3C22CA9101B42, 0x2CCEBEC54F899583, 0x042880BB620E90E8, 0xDAEAFCA5DC5056CB,
    0xD1D6E1A20F99C0BE, 0x6226660B08A6F1BF, 0xB52C699A069D9692, 0x3A52D12F49152AA8,
    0x191FDA0ACEBAFD70, 0xEC74521FBFBEF34E, 0xCA8858549BB6C38B, 0xD2E0823E1F895C8B,
    0xCE6AF0F65EBA2097, 0x1F7DC7B5D45A7CD2, 0x6C4C19343F84D09E, 0xC6904F7CA68627EC,
    0x61CF36273D3AFD34, 0x5C44CCB71106CE37, 0xA52532EBA89ED18F, 0x60C0AA5F964A4045,
    0x4FE93A8B09BEDE3C, 0xF527DADC07C2C43C, 0x3CC1A0CFE0223264, 0x735865252CB5EF9D,
    0x82D7D081FF9ABF8E, 0x2750D74D59176D65, 0x4F7C1C75FF71C541, 0x7F3400DF32068090,
    0x5B913EF8AF694F26, 0xCBE1569D0A51FD68, 0x2C75D647DDC081FD, 0x96C13E58F3B38A62,
    0x496FD72241D8F3A3, 0xF00B449AFC0B1ADF, 0xFFDF86D47806CC01, 0xE5C5829F9A87DAF1,
    0x23E37341879D515E, 0x40E752E90576C96B, 0xF38C008E636E7766, 0x011BE5EEEF591F11,
    0x35BB0D9AA2395D9C, 0x20F9929BE109EF16, 0x2F47ED98704FF1B3, 0xBD3FEFFCE9168BAC,
    0x9E93E8584169F154, 0xC101CAAA756D6273, 0x5A7304DE0B923DE4, 0x4D733CE9743DDA95,
    0x030AFC51F4773B1A, 0xBE9BEB2814D5F26D, 0x041457EA23A9560E, 0x0D6426EFAB24E9EB,
    0x4C990D19967E6195, 0x609041AC55071D96, 0xC1DEC65DE8603B08, 0xA786C9D7BBECBE0F,
    0x5F917B3FBC155F42, 0x5E2750EE5E630CB1, 0xFA9441D8B670DD72, 0x199581935DE3BBE1,
    0x773E66E3F25FF275, 0x81C6FC6D036C2F79, 0x7A89BEC509557B68, 0xD0CE5771ACE9C477,
    0x82B00C5CF2D9E7CF, 0xCEAB40115DBAFE74, 0x1B6E699BC6CBB141, 0x34DA4D64DFEAE0C4,
    0x5052731A0D6EB36D, 0xBAC21ACB2D51D029, 0xF8BE263FDA6A23E9, 0x8A180FE76B3D6598,
    0xAAAECCE7B5C242F8, 0x9CC2044963F82975, 0xFAAEFD24975B8281, 0x10AC86FC5BCA467F,
    0xAE56D1A26332ADB1, 0x041CDF5D414C8E00, 0x5D1433A3E546B7E3, 0xA7D44D7291E80DF4,
    0x666E2424EDED37DB, 0x30F77A8CE061BB38, 0xE34B90D6822F097B, 0xBBB62D4B35C9690B,
    0xD705F328CD84C560, 0x50D9FE62B0DDB847, 0x207C9F06E6F738AF, 0x3EB0014EDBCE5FF6,
    0x8F670712BD4A7C06, 0x743C54A67F4CB1B0, 0x6AC5F9961E689829, 0x017323ADC7642AD3,
    0x11E26CE992890AC8, 0x7C2C7BEA88F55D71, 0x9031876CD7240FC0, 0x7E8103C164B8BCF0,
    0x241469CC623303EA, 0xFDBFF43E97F5D12D, 0xADCFA466A0FE777E, 0x5B0D89C22C13CB55,
    0x39149BDBC24B61F7, 0x4B3227B21D8AD305, 0xE9CC64CB74054EFE, 0xE331CDDF0C8BBC86,
    0xFEEAD8DF8A753555, 0xEA647E77EA830D4C, 0x09FEE5990DA0DDEA, 0x2D03A2DA7FAE6365,
    0x5701E887DDAE112B, 0x07B8FCB458AB3738, 0x89ACFCE4460CFABA, 0x887BCB83C1E7CA78,
    0x9FFB5BDA660B1D57, 0x255AD1A68673D75A, 0x4185FB0593177EFD, 0x135CC5E6DBEB9CCB,
    0x7C0380AF942806A0, 0x2FA13E5EAB16D370, 0xC319501C58979653, 0xA0286BF5D5C5D17C,
    0x14A12A392E083337, 0xC6E93F876C58E64D, 0x6AF72F6425763436, 0x99D1B5E1DDA2A84E,
    0x731D7B66DBF1908A, 0x5C79E43127E5359C, 0x6C35271BEA1699DA, 0xB28ED7593E646253,
    0x64963DCD50DF6A37, 0xADBA13F2B4CDFDDF, 0xB92C782D580820D7, 0x0C49406D0BF61AF0,
    0x7B64E36C1CE9DF84, 0xDCF480C3320CCF23, 0x4C3D9A4A5826CB07, 0x30C385C667A6D9E1,
    0x9886A00E36B72D1D, 0xB34E65714720198E, 0xB025E90315B2B014, 0xA7C1444587E54DC2,
    0xD73A18E7CDBECA00, 0x4DDF042CA95B8E38, 0x3D01D171320415C8, 0x815E1561637009B5,
    0x5C19D306C0F40819, 0x941240C1EC94BFDA, 0xDA98CF3370DB7009, 0x5419A91CBFC3E19C,
    0x4B16F27EB28FE9C1, 0x0F29D651515358BE, 0x7B3A882F5B6868FE, 0x8CB08C6E7FC80207,
    0x96781F1035EB6496, 0x4D54331E5ABAB73B, 0xC5F7DA04667D0FA1, 0xAB88CDFC63133CA8,
    0x816006C9C1FFECC7, 0xE7223FBD2834D6FB, 0x255FAF450A99E279, 0x7C8D180FFA074DF3,
    0x18759C88B5A4A77B, 0x79FD00FE7F777BAC, 0x435652355C66EA7F, 0x3B6FFC9372478E5B,
    0x30CB2B8695AA63BC, 0xFC41D8C7E2A8C3CF, 0xB997CCD3DA7FEC2B, 0xDC74E2C341716150,
    0xE3BCE7A490863D53, 0x53B06A4A507CAF4C, 0xE1BD9FB50B9CA99B, 0x6F3F00BFED4E8F96,
    0x545F04C63B604F10, 0xBB7F48E5A268E0C9, 0xE81C580FD20BF995, 0xD58C0B9BD1C4D0C1,
    0x40A4B56AB10CDAB8, 0xC8D60A42BAD3C402, 0x64C117840FDC1D45, 0xFA3F3045A92898CD,
    0x5976828B0DADE5AA, 0xD5799E65EEB4B83B, 0x8468B013305DBA4B, 0xF778AD262258648C,
    0xC4C4DEA693460642, 0x260A16EC33184BAC, 0x165C37F648EAE04C, 0xC770334EB4D86222,
    0x34E1409BCF3D2D49, 0x21CED38891C7C5B2, 0x85AE9FAECFC0F77F, 0xDDA99AA0028E5AD7,
    0x92942B704E466454, 0x152E8D42FC9CECE1, 0x20A5C832A26F8E04, 0xC68513EAB138AB5E,
    0x12F64E5C04268504, 0x834D365BCD434547, 0xF83A067EAC681FE3, 0x58A7B388B42B4A86,
    0xFC14EF180DC44036, 0xCCBDC423FA397007, 0x93C151DAE8AE215F, 0xEF1E1257F8F3CA18,
    0x732664212B7022B8, 0x361A2F369AF43085, 0xB33A51623CD46175, 0x5426FDFF93B406BF,
    0xBB5C0ADF3633BF48, 0x1C88E1C43458B977, 0x0D446D3D0E3FFDC6, 0xB9091B410833FB23,
    0x081A8B34A6133C46, 0x9C232A0BBDB6BCAB, 0xAEFACA1D3E76DEB8, 0x4107C3371F3C1A72,
];

/// Shift-only modular scaling $(x \cdot 2^{\text{shift}}) \bmod p$ for `shift <= 23` using `0`
/// multiplications ($2^{64} \equiv 2^{32} - 1 \pmod p$).
#[inline]
pub const fn gl_shl_small(x: u64, shift: u32) -> u64 {
    debug_assert!(shift <= 23);
    let r = gl_reduce_u64(x);
    let z = (r as u128) << shift;
    let z_lo = gl_reduce_u64(z as u64);
    let z_mid = (z >> 64) as u64;
    // Since `z_mid < 2^23`, `(z_mid << 32) - z_mid` is strictly in `[0, 2^55) ⊂ [0, p)`.
    let mid_term = (z_mid << 32).wrapping_sub(z_mid);
    gl_add(z_lo, mid_term)
}

/// Kronecker-swapped Width-24 external diffusion layer $M_E = M_4 \otimes P_6$ (`0` field muls;
/// kills Bariant / Merz–Rodríguez García `ePrint 2026/306` subspace trail skipping).
pub fn poseidon2_gl24_apply_me(st: &mut [u64; 24]) {
    for x in st.iter_mut() {
        *x = gl_reduce_u64(*x);
    }
    let mut y = [[0u64; 4]; 6];
    for c in 0..6 {
        y[c] = poseidon2_apply_m4([st[c], st[6 + c], st[12 + c], st[18 + c]]);
    }
    for g in 0..4 {
        let s = gl_add(
            gl_add(gl_add(y[0][g], y[1][g]), gl_add(y[2][g], y[3][g])),
            gl_add(y[4][g], y[5][g]),
        );
        for c in 0..6 {
            st[6 * g + c] = gl_add(y[c][g], s);
        }
    }
}

/// Shift-only Width-24 internal diffusion layer $M_I = J_{24} + \mathrm{diag}(-2^{23}, 1, 2, \dots, 2^{22})$
/// (`0` field multiplications, Rabin-irreducible degree-24 charpoly over Goldilocks, nonzero-sum branch number `25`).
pub fn poseidon2_gl24_apply_mi(st: &mut [u64; 24]) {
    let mut s = 0u64;
    for &x in st.iter() {
        s = gl_add(s, gl_reduce_u64(x));
    }
    st[0] = gl_add(s, gl_neg(gl_shl_small(st[0], 23)));
    st[1] = gl_add(s, gl_reduce_u64(st[1]));
    for (j, x) in st.iter_mut().enumerate().skip(2) {
        *x = gl_add(s, gl_shl_small(*x, (j - 1) as u32));
    }
}

/// Canonical Width-24 Goldilocks `Poseidon2-GL-w24` permutation (`(R_F, R_P) = (8, 44)`).
pub fn poseidon2_gl24_perm(st: &mut [u64; 24]) {
    poseidon2_gl24_apply_me(st);
    for r in 0..POSEIDON2_GL24_HALF_EXTERNAL_ROUNDS {
        let base = 24 * r;
        for lane in 0..24 {
            st[lane] = poseidon2_sbox7(gl_add(st[lane], POSEIDON2_GL24_RC[base + lane]));
        }
        poseidon2_gl24_apply_me(st);
    }
    for r in 0..POSEIDON2_GL24_INTERNAL_ROUNDS {
        st[0] = poseidon2_sbox7(gl_add(st[0], POSEIDON2_GL24_RC[96 + r]));
        poseidon2_gl24_apply_mi(st);
    }
    for r in 0..POSEIDON2_GL24_HALF_EXTERNAL_ROUNDS {
        let base = 140 + 24 * r;
        for lane in 0..24 {
            st[lane] = poseidon2_sbox7(gl_add(st[lane], POSEIDON2_GL24_RC[base + lane]));
        }
        poseidon2_gl24_apply_me(st);
    }
}

/// 1-call 2-to-1 Merkle compression of two 7-limb (448-bit) digests + 2 tweak limbs (`7 + 7 + 2 = 16`
/// rate limbs) with Jive-weighted feed-forward (`out[i] = perm(st)[i] + left[i] + 2*right[i] + 4*tweak[i]`).
pub fn poseidon2_gl24_compress_merkle(
    left: &[u64; 7],
    right: &[u64; 7],
    tweak: &[u64; 2],
) -> [u64; 7] {
    let mut st = [0u64; 24];
    for i in 0..7 {
        st[i] = gl_reduce_u64(left[i]);
        st[7 + i] = gl_reduce_u64(right[i]);
    }
    st[14] = gl_reduce_u64(tweak[0]);
    st[15] = gl_reduce_u64(tweak[1]);
    st[16] = POSEIDON2_GL24_RATE as u64;
    st[17] = POSEIDON2_GL24_CAPACITY as u64;
    st[18] = POSEIDON2_GL24_DIGEST_LIMBS as u64;
    st[19] = gl_reduce_u64(POSEIDON2_GL24_MERKLE_TAG);
    st[23] = gl_reduce_u64(POSEIDON2_GL24_IV);

    let mut perm = st;
    poseidon2_gl24_perm(&mut perm);

    let mut out = [0u64; 7];
    for i in 0..7 {
        let mut ff = gl_add(st[i], gl_shl_small(st[7 + i], 1));
        if i < 2 {
            ff = gl_add(ff, gl_shl_small(st[14 + i], 2));
        }
        out[i] = gl_add(perm[i], ff);
    }
    ct_zeroize_u64s(&mut st);
    ct_zeroize_u64s(&mut perm);
    out
}

/// Stack-allocated zeroizing Width-24 `Poseidon2-GL-w24` sponge (`rate = 16`, `capacity = 8`,
/// 7-limb = 56-byte digest) with `10*1` multi-rate padding and zero heap allocations.
pub struct Poseidon2Gl24Sponge {
    state: [u64; 24],
    rate_pos: usize,
}

impl Drop for Poseidon2Gl24Sponge {
    fn drop(&mut self) {
        ct_zeroize_u64s(&mut self.state);
        self.rate_pos = 0;
    }
}

impl Poseidon2Gl24Sponge {
    pub const fn new_with_domain(domain_tag: u64) -> Self {
        let mut state = [0u64; 24];
        state[16] = POSEIDON2_GL24_RATE as u64;
        state[17] = POSEIDON2_GL24_CAPACITY as u64;
        state[18] = 56;
        state[19] = gl_reduce_u64(domain_tag);
        state[23] = gl_reduce_u64(POSEIDON2_GL24_IV);
        Self { state, rate_pos: 0 }
    }

    #[inline]
    pub fn absorb_limb(&mut self, limb: u64) {
        let v = gl_reduce_u64(limb);
        self.state[self.rate_pos] = gl_add(self.state[self.rate_pos], v);
        self.rate_pos += 1;
        if self.rate_pos == POSEIDON2_GL24_RATE {
            poseidon2_gl24_perm(&mut self.state);
            self.rate_pos = 0;
        }
    }

    pub fn absorb_limbs(&mut self, limbs: &[u64]) {
        for &l in limbs {
            self.absorb_limb(l);
        }
    }

    /// Absorb an arbitrary byte slice via injective `< 2^56` 7-byte chunks (`0x01` delimiter).
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

    /// Apply `10*1` multi-rate sponge padding (`rate = 16`) and squeeze 7 canonical Goldilocks limbs.
    pub fn finalize_digest7(mut self) -> [u64; 7] {
        if self.rate_pos == 15 {
            self.state[15] = gl_add(self.state[15], (1u64 << 56) + 1);
        } else {
            self.state[self.rate_pos] = gl_add(self.state[self.rate_pos], 1);
            self.state[15] = gl_add(self.state[15], 1u64 << 56);
        }
        poseidon2_gl24_perm(&mut self.state);
        let mut out = [0u64; 7];
        out.copy_from_slice(&self.state[..7]);
        out
    }
}

/// Hash an arbitrary byte message with `Poseidon2-GL-w24` (`rate = 16, cap = 8`) to 56 canonical LE bytes.
pub fn poseidon2_gl24_hash56(domain_tag: u64, msg: &[u8]) -> [u8; 56] {
    let mut sp = Poseidon2Gl24Sponge::new_with_domain(domain_tag);
    sp.absorb_bytes_framed(msg);
    let limbs = sp.finalize_digest7();
    let mut out = [0u8; 56];
    for (i, &limb) in limbs.iter().enumerate() {
        out[8 * i..8 * i + 8].copy_from_slice(&limb.to_le_bytes());
    }
    out
}

#[cfg(test)]
mod poseidon2_gl24_tests {
    use super::*;
    use crate::goldilocks::GOLDILOCKS_PRIME;

    #[test]
    fn grain_constants_match_table_and_are_canonical() {
        let generated = poseidon2_gl24_grain_constants();
        assert_eq!(generated, POSEIDON2_GL24_RC);
        for &c in &POSEIDON2_GL24_RC {
            assert!(c < GOLDILOCKS_PRIME);
        }
    }

    #[test]
    fn shift_helper_matches_field_multiplication() {
        let samples = [
            0u64,
            1,
            2,
            0xDEAD_BEEF_CAFE_BABE,
            0xFFFF_FFFF_0000_0000,
            GOLDILOCKS_PRIME - 1,
            u64::MAX,
        ];
        for &x in &samples {
            for s in 0..=23 {
                assert_eq!(gl_shl_small(x, s), gl_mul(gl_reduce_u64(x), 1u64 << s));
            }
        }
    }

    #[test]
    fn gl24_canonical_sequence_and_merkle_kats() {
        let mut st: [u64; 24] = core::array::from_fn(|i| i as u64);
        poseidon2_gl24_perm(&mut st);
        assert_eq!(
            st,
            [
                9262813872168818283,
                14473920968081642809,
                3132432025506878070,
                739327372316014541,
                13930273445042610257,
                9887230855574303117,
                10411529172945029295,
                2610146355123527807,
                15800955794096892263,
                126337761019280528,
                15741922631823646152,
                12261346758669164007,
                2093389069744887410,
                3165987204040455923,
                14526830091420603371,
                2537012170462392522,
                17818886402825694850,
                14929111493621950133,
                16221575831479706027,
                10965213893411960579,
                16472025002487739980,
                12534132784495569014,
                13110610053613593246,
                5468252370409873572,
            ]
        );

        let mut zero = [0u64; 24];
        poseidon2_gl24_perm(&mut zero);
        assert_eq!(
            &zero[..7],
            &[
                17732809615181082052,
                5992241717688655734,
                5659530038547088535,
                14879928265562365873,
                9090045152854863079,
                17692364117337720896,
                8104590373471715238,
            ]
        );

        let merkle = poseidon2_gl24_compress_merkle(
            &[1, 2, 3, 4, 5, 6, 7],
            &[8, 9, 10, 11, 12, 13, 14],
            &[100, 200],
        );
        assert_eq!(
            merkle,
            [
                1170443848852734659,
                833485916214919520,
                373819593114229865,
                2500389336842599945,
                2668122737528357675,
                15131165148025152836,
                573418327208874869,
            ]
        );
    }

    #[test]
    fn gl24_internal_matrix_rabin_irreducible_and_me_kills_subspace_trails() {
        // Verify matrix-determinant characteristic polynomial of M_I = J_24 + diag(-2^23, 1, 2, ..., 2^22)
        // is monic degree-24 and Rabin-irreducible over Goldilocks (divisors 24/2 = 12 and 24/3 = 8).
        fn poly_mul(a: &[u64], b: &[u64]) -> alloc::vec::Vec<u64> {
            let mut out = alloc::vec![0u64; a.len() + b.len() - 1];
            for (i, &ai) in a.iter().enumerate() {
                for (j, &bj) in b.iter().enumerate() {
                    out[i + j] = gl_add(out[i + j], gl_mul(ai, bj));
                }
            }
            out
        }
        fn poly_sub(a: &[u64], b: &[u64]) -> alloc::vec::Vec<u64> {
            let n = a.len().max(b.len());
            let mut out = alloc::vec![0u64; n];
            for (i, &ai) in a.iter().enumerate() {
                out[i] = ai;
            }
            for (i, &bi) in b.iter().enumerate() {
                out[i] = gl_add(out[i], gl_neg(bi));
            }
            while out.len() > 1 && *out.last().unwrap() == 0 {
                out.pop();
            }
            out
        }
        fn poly_inv(x: u64) -> u64 {
            let mut res = 1u64;
            let mut cur = x;
            let mut e = GOLDILOCKS_PRIME - 2;
            while e > 0 {
                if e & 1 == 1 {
                    res = gl_mul(res, cur);
                }
                cur = gl_mul(cur, cur);
                e >>= 1;
            }
            res
        }
        fn poly_mod(a: &[u64], b: &[u64]) -> alloc::vec::Vec<u64> {
            let mut r = a.to_vec();
            while r.len() >= b.len() && r.iter().any(|&x| x != 0) {
                let lead = *r.last().unwrap();
                if lead != 0 {
                    let coef = gl_mul(lead, poly_inv(*b.last().unwrap()));
                    let shift = r.len() - b.len();
                    for (i, &bi) in b.iter().enumerate() {
                        r[shift + i] = gl_add(r[shift + i], gl_neg(gl_mul(coef, bi)));
                    }
                }
                r.pop();
            }
            while r.len() > 1 && *r.last().unwrap() == 0 {
                r.pop();
            }
            r
        }
        fn poly_gcd(mut a: alloc::vec::Vec<u64>, mut b: alloc::vec::Vec<u64>) -> alloc::vec::Vec<u64> {
            while b.iter().any(|&x| x != 0) {
                let r = poly_mod(&a, &b);
                a = b;
                b = r;
            }
            let inv = poly_inv(*a.last().unwrap());
            for c in &mut a {
                *c = gl_mul(*c, inv);
            }
            a
        }
        fn frob_step(poly: &[u64], modp: &[u64]) -> alloc::vec::Vec<u64> {
            let mut res = alloc::vec![1u64];
            let mut cur = poly_mod(poly, modp);
            let mut e = GOLDILOCKS_PRIME;
            while e > 0 {
                if e & 1 == 1 {
                    res = poly_mod(&poly_mul(&res, &cur), modp);
                }
                cur = poly_mod(&poly_mul(&cur, &cur), modp);
                e >>= 1;
            }
            res
        }

        let mut full_prod = alloc::vec![1u64];
        for &d in &POSEIDON2_GL24_INTERNAL_DIAG {
            full_prod = poly_mul(&full_prod, &[gl_neg(d), 1]);
        }
        let mut charpoly = full_prod;
        for j in 0..24 {
            let mut prod_wo = alloc::vec![1u64];
            for (i, &d) in POSEIDON2_GL24_INTERNAL_DIAG.iter().enumerate() {
                if i != j {
                    prod_wo = poly_mul(&prod_wo, &[gl_neg(d), 1]);
                }
            }
            charpoly = poly_sub(&charpoly, &prod_wo);
        }
        assert_eq!(charpoly.len(), 25);
        assert_eq!(*charpoly.last().unwrap(), 1);

        let x_poly = alloc::vec![0u64, 1];
        let mut cur = x_poly.clone();
        let mut xp8 = alloc::vec![];
        let mut xp12 = alloc::vec![];
        for step in 1..=24 {
            cur = frob_step(&cur, &charpoly);
            if step == 8 {
                xp8 = cur.clone();
            }
            if step == 12 {
                xp12 = cur.clone();
            }
        }
        assert_eq!(cur, x_poly, "X^(p^24) == X mod charpoly");
        assert_eq!(poly_gcd(poly_sub(&xp8, &x_poly), charpoly.clone()), alloc::vec![1]);
        assert_eq!(poly_gcd(poly_sub(&xp12, &x_poly), charpoly), alloc::vec![1]);

        // Verify M_E = M_4 ⊗ P_6 injects every (X, -X) rate-block difference into capacity lanes 16..24!
        for a in 0..4 {
            for b in (a + 1)..4 {
                for lane in 0..4 {
                    let mut st = [0u64; 24];
                    st[4 * a + lane] = 1;
                    st[4 * b + lane] = GOLDILOCKS_PRIME - 1;
                    poseidon2_gl24_apply_me(&mut st);
                    assert!(
                        st[16..24].iter().any(|&c| c != 0),
                        "rate blocks ({a}, {b}) lane {lane} left capacity untouched"
                    );
                }
            }
        }
    }
}
