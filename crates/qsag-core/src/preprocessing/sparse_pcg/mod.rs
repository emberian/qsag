//! Sparse GGM and QC-LPN construction used by the wire and expansion regression tests.

use super::*;
use crate::sponge::keccak::Shake256Xof;

type BooleanMascotProducts = (
    PartyValues<u64>,
    PartyValues<[u128; 64]>,
    PartyValues<[u128; 64]>,
);

/// Pairwise correlated-OT pass of the sparse fixture: Boolean AND shares plus two `Tower128`
/// companion products per bit. Receiver `j` uses fresh choice bits `c_rand` and publishes
/// `diff = v_words[j] ^ c_rand`.
fn pairwise_boolean_and_mascot_companions(
    ot_mesh: &mut OtMesh,
    u_words_per_party: &[Vec<u64>],
    v_words_per_party: &[Vec<u64>],
    at0_per_party: &[Vec<[u128; 64]>],
    at1_per_party: &[Vec<[u128; 64]>],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<BooleanMascotProducts, PreprocessError> {
    let n = ot_mesh.n;
    let num_words = u_words_per_party[0].len();
    let mut w_bool: Vec<Vec<u64>> = (0..n)
        .map(|i| {
            (0..num_words)
                .map(|k| u_words_per_party[i][k] & v_words_per_party[i][k])
                .collect()
        })
        .collect();
    let mut ct0: Vec<Vec<[u128; 64]>> = (0..n)
        .map(|i| {
            (0..num_words)
                .map(|k| {
                    let mut arr = [0u128; 64];
                    let vi = v_words_per_party[i][k];
                    for bit in 0..64 {
                        let mask = 0u128.wrapping_sub(((vi >> bit) & 1) as u128);
                        arr[bit] = at0_per_party[i][k][bit] & mask;
                    }
                    arr
                })
                .collect()
        })
        .collect();
    let mut ct1: Vec<Vec<[u128; 64]>> = (0..n)
        .map(|i| {
            (0..num_words)
                .map(|k| {
                    let mut arr = [0u128; 64];
                    let vi = v_words_per_party[i][k];
                    for bit in 0..64 {
                        let mask = 0u128.wrapping_sub(((vi >> bit) & 1) as u128);
                        arr[bit] = at1_per_party[i][k][bit] & mask;
                    }
                    arr
                })
                .collect()
        })
        .collect();
    if num_words == 0 {
        return Ok((w_bool, ct0, ct1));
    }

    for i in 0..n {
        for j in 0..n {
            if i == j {
                continue;
            }
            let mut c_rand = vec![0u64; num_words];
            for w in &mut c_rand {
                *w = party_rngs[j].next_u64();
            }
            let (send_pads, recv_pads) =
                ot_mesh.run_correlated_ot_words(i, j, &c_rand, party_rngs)?;
            for k in 0..num_words {
                let ui = u_words_per_party[i][k];
                let cr = black_box(c_rand[k]);
                let dw = v_words_per_party[j][k] ^ cr;
                let mut s_ij_bool = 0u64;
                let mut enc_one_bool = 0u64;
                let mut c1_lane0 = [0u128; 64];
                let mut c1_lane1 = [0u128; 64];

                for bit in 0..64 {
                    let (p0, p1) = &send_pads[64 * k + bit];
                    let d_bit = (dw >> bit) & 1;
                    let mask_bit = (p0[32] & 1) as u64;
                    let ui_bit = (ui >> bit) & 1;
                    let c1_b = (mask_bit ^ ui_bit) ^ ((p1[32] & 1) as u64);
                    s_ij_bool |= (mask_bit ^ (ui_bit & d_bit)) << bit;
                    enc_one_bool |= c1_b << bit;

                    let d_mask128 = 0u128.wrapping_sub(d_bit as u128);
                    let p0_l0 = u128::from_le_bytes(core::array::from_fn(|array_index| {
                        (p0[0..16])[array_index]
                    }));
                    let p1_l0 = u128::from_le_bytes(core::array::from_fn(|array_index| {
                        (p1[0..16])[array_index]
                    }));
                    ct0[i][k][bit] ^= p0_l0 ^ (at0_per_party[i][k][bit] & d_mask128);
                    c1_lane0[bit] = p0_l0 ^ at0_per_party[i][k][bit] ^ p1_l0;

                    let p0_l1 = u128::from_le_bytes(core::array::from_fn(|array_index| {
                        (p0[16..32])[array_index]
                    }));
                    let p1_l1 = u128::from_le_bytes(core::array::from_fn(|array_index| {
                        (p1[16..32])[array_index]
                    }));
                    ct1[i][k][bit] ^= p0_l1 ^ (at1_per_party[i][k][bit] & d_mask128);
                    c1_lane1[bit] = p0_l1 ^ at1_per_party[i][k][bit] ^ p1_l1;
                }
                w_bool[i][k] ^= s_ij_bool;

                let mut s_ji_bool = 0u64;
                for bit in 0..64 {
                    let rpad = &recv_pads[64 * k + bit];
                    let cr_bit = (cr >> bit) & 1;
                    let pb = (rpad[32] & 1) as u64;
                    let corr = cr_bit & ((enc_one_bool >> bit) & 1);
                    s_ji_bool |= (pb ^ corr) << bit;

                    let cmask128 = 0u128.wrapping_sub(cr_bit as u128);
                    let rp_l0 = u128::from_le_bytes(core::array::from_fn(|array_index| {
                        (rpad[0..16])[array_index]
                    }));
                    let rp_l1 = u128::from_le_bytes(core::array::from_fn(|array_index| {
                        (rpad[16..32])[array_index]
                    }));
                    ct0[j][k][bit] ^= rp_l0 ^ (cmask128 & c1_lane0[bit]);
                    ct1[j][k][bit] ^= rp_l1 ^ (cmask128 & c1_lane1[bit]);
                }
                w_bool[j][k] ^= s_ji_bool;
            }
            wipe_u64s(&mut c_rand);
        }
    }
    Ok((w_bool, ct0, ct1))
}

pub(super) const PCG_WIRE_MAGIC: &[u8; 8] = b"QSAGPCG1";

/// Sender-side compact seed (`16 B`) for one `SHAKE256` GGM puncturable-PRF tree.
#[derive(Clone)]
pub struct GgmSenderTreeSeed {
    pub root_seed: [u8; 16],
}

impl fmt::Debug for GgmSenderTreeSeed {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("GgmSenderTreeSeed([REDACTED])")
    }
}

impl Drop for GgmSenderTreeSeed {
    fn drop(&mut self) {
        wipe_bytes(&mut self.root_seed);
    }
}

/// Receiver-side punctured `SHAKE256` GGM tree seed for Binary Subfield-VOLE (`depth * 16 + 34` bytes).
#[derive(Clone)]
pub struct GgmReceiverBinaryTreeSeed {
    pub punctured_idx: u16,
    pub copath: Vec<[u8; 16]>,
    /// Masked punctured-leaf 2-lane `Tower128` correlation `(\bigoplus_u key_S[u]) \oplus \Delta`.
    pub punctured_mac_corr: [Tower128; 2],
}

impl fmt::Debug for GgmReceiverBinaryTreeSeed {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("GgmReceiverBinaryTreeSeed([REDACTED])")
    }
}

impl Drop for GgmReceiverBinaryTreeSeed {
    fn drop(&mut self) {
        self.punctured_idx = 0;
        for node in &mut self.copath {
            wipe_bytes(node);
        }
        wipe_u128s(core::slice::from_mut(&mut self.punctured_mac_corr[0].0));
        wipe_u128s(core::slice::from_mut(&mut self.punctured_mac_corr[1].0));
    }
}

/// Receiver-side punctured `SHAKE256` GGM tree seed for `Tower128` VOLE (`depth * 16 + 50` bytes).
#[derive(Clone)]
pub struct GgmReceiverTowerTreeSeed {
    pub punctured_idx: u16,
    pub punctured_beta: Tower128,
    pub copath: Vec<[u8; 16]>,
    /// Masked punctured-leaf 2-lane `Tower128` correlation `key_S[p^*] \oplus (\beta \cdot \Delta)`.
    pub punctured_mac_val: [Tower128; 2],
}

impl fmt::Debug for GgmReceiverTowerTreeSeed {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("GgmReceiverTowerTreeSeed([REDACTED])")
    }
}

impl Drop for GgmReceiverTowerTreeSeed {
    fn drop(&mut self) {
        self.punctured_idx = 0;
        wipe_u128s(core::slice::from_mut(&mut self.punctured_beta.0));
        for node in &mut self.copath {
            wipe_bytes(node);
        }
        wipe_u128s(core::slice::from_mut(&mut self.punctured_mac_val[0].0));
        wipe_u128s(core::slice::from_mut(&mut self.punctured_mac_val[1].0));
    }
}

/// Directional GGM seed material held by `party_id` for a single peer `peer_id != party_id`.
#[derive(Clone)]
pub struct PcgPeerSeedMaterial {
    pub peer_id: u16,
    /// `3 * 4 = 12` binary GGM sender roots (`X`, `Y`, `Z` bundles where `party_id` is MAC verifier).
    pub bin_sender_trees: Vec<GgmSenderTreeSeed>,
    /// `3 * 4 = 12` binary GGM punctured receiver trees (`X`, `Y`, `Z` bundles where `party_id` holds sparse noise).
    pub bin_receiver_trees: Vec<GgmReceiverBinaryTreeSeed>,
    /// `2 * 4 = 8` `Tower128` GGM sender roots (`A0`, `A1` sacrifice companion bundles, fixed `depth = 14`).
    pub tower_sender_trees: Vec<GgmSenderTreeSeed>,
    /// `2 * 4 = 8` `Tower128` GGM punctured receiver trees (`A0`, `A1` companion bundles, fixed `depth = 14`).
    pub tower_receiver_trees: Vec<GgmReceiverTowerTreeSeed>,
}

impl fmt::Debug for PcgPeerSeedMaterial {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PcgPeerSeedMaterial")
            .field("peer_id", &self.peer_id)
            .finish_non_exhaustive()
    }
}

/// Additive 2-lane `Tower128` BDOZ-authenticated scalar share `[x]_p \in \mathcal{T}_7`.
///
/// Global invariant across parties $p \in \{0, \dots, n-1\}$:
/// `macs_for_me[q][lane] \oplus Peer(q).keys_from_me[p][lane] == Peer(q).alpha[lane] * value` (`q != p`),
/// and for `q == p`, `macs_for_me[p][lane] \oplus keys_from_me[p][lane] == alpha[lane] * value`.
#[derive(PartialEq, Eq)]
pub struct PcgAuthTower128Share {
    pub value: Tower128,
    /// `macs[verifier_q][lane]` authenticating `self.value` under party `q`'s MAC key.
    pub macs: Vec<[Tower128; 2]>,
    /// `keys[holder_q][lane]` authenticating party `q`'s share under `self.alpha`.
    pub keys: Vec<[Tower128; 2]>,
}

impl fmt::Debug for PcgAuthTower128Share {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("PcgAuthTower128Share([REDACTED])")
    }
}

impl Drop for PcgAuthTower128Share {
    fn drop(&mut self) {
        wipe_u128s(core::slice::from_mut(&mut self.value.0));
        for row in &mut self.macs {
            wipe_tower128(row);
        }
        for row in &mut self.keys {
            wipe_tower128(row);
        }
    }
}

impl PcgAuthTower128Share {
    pub fn zero(n: usize) -> Self {
        Self {
            value: Tower128::ZERO,
            macs: vec![[Tower128::ZERO; 2]; n],
            keys: vec![[Tower128::ZERO; 2]; n],
        }
    }

    #[inline]
    pub fn xor_assign(&mut self, rhs: &Self) {
        self.value = self.value.add(rhs.value);
        for q in 0..self.macs.len() {
            for lane in 0..2 {
                self.macs[q][lane] = self.macs[q][lane].add(rhs.macs[q][lane]);
                self.keys[q][lane] = self.keys[q][lane].add(rhs.keys[q][lane]);
            }
        }
    }

    #[inline]
    pub fn scale(&self, rho: Tower128) -> Self {
        let n = self.macs.len();
        let mut macs = vec![[Tower128::ZERO; 2]; n];
        let mut keys = vec![[Tower128::ZERO; 2]; n];
        for q in 0..n {
            for lane in 0..2 {
                macs[q][lane] = self.macs[q][lane].mul(rho);
                keys[q][lane] = self.keys[q][lane].mul(rho);
            }
        }
        Self {
            value: self.value.mul(rho),
            macs,
            keys,
        }
    }
}

/// Authenticated 128-bit `Tower128` Beaver triple `([a], [b], [c])` with `c = a * b` in $\mathcal{T}_7$.
#[derive(PartialEq, Eq)]
pub struct PcgAuthTower128TripleShare {
    pub a: PcgAuthTower128Share,
    pub b: PcgAuthTower128Share,
    pub c: PcgAuthTower128Share,
}

impl fmt::Debug for PcgAuthTower128TripleShare {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("PcgAuthTower128TripleShare([REDACTED])")
    }
}

/// Packed 64-bit batch of authenticated Boolean Beaver triples `([a], [b], [c])` (`c = a & b`)
/// with exact per-bit 2-lane `Tower128` BDOZ MACs and keys.
pub struct PcgAuthBoolTripleWord64 {
    pub a_word: u64,
    pub b_word: u64,
    pub c_word: u64,
    /// `[bit][verifier_q][lane]` authenticating `a_word / b_word / c_word` bits.
    pub a_macs: Vec<[[Tower128; 2]; 64]>,
    pub a_keys: Vec<[[Tower128; 2]; 64]>,
    pub b_macs: Vec<[[Tower128; 2]; 64]>,
    pub b_keys: Vec<[[Tower128; 2]; 64]>,
    pub c_macs: Vec<[[Tower128; 2]; 64]>,
    pub c_keys: Vec<[[Tower128; 2]; 64]>,
}

impl fmt::Debug for PcgAuthBoolTripleWord64 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("PcgAuthBoolTripleWord64([REDACTED])")
    }
}

impl Drop for PcgAuthBoolTripleWord64 {
    fn drop(&mut self) {
        wipe_u64s(core::slice::from_mut(&mut self.a_word));
        wipe_u64s(core::slice::from_mut(&mut self.b_word));
        wipe_u64s(core::slice::from_mut(&mut self.c_word));
        for v in &mut self.a_macs {
            for pair in v {
                wipe_tower128(pair);
            }
        }
        for v in &mut self.a_keys {
            for pair in v {
                wipe_tower128(pair);
            }
        }
        for v in &mut self.b_macs {
            for pair in v {
                wipe_tower128(pair);
            }
        }
        for v in &mut self.b_keys {
            for pair in v {
                wipe_tower128(pair);
            }
        }
        for v in &mut self.c_macs {
            for pair in v {
                wipe_tower128(pair);
            }
        }
        for v in &mut self.c_keys {
            for pair in v {
                wipe_tower128(pair);
            }
        }
    }
}

/// Experimental sparse correlation format, not suitable for online masks.
/// Production vault APIs use uniform KOS/MASCOT preprocessing.
/// Compact `< 24 KB` sublinear Silent-OT / `SHAKE256` GGM + QC-LPN Pseudorandom Correlation
/// Generator (`PCG`) seed held by one party.
///
/// Calling [`PcgPartySeed::expand_local`] expands this `< 24 KB` seed **locally with ZERO network I/O**
/// into `65,600` (`> 65,536`) 2-lane `Tower128` BDOZ-authenticated Boolean Beaver triples +
/// `8` authenticated 128-bit `Tower128` Beaver triples + sacrifice companion masks.
pub struct PcgPartySeed {
    session_id: [u8; 32],
    party_id: usize,
    num_parties: usize,
    tree_depth: usize,
    mac_alpha: [Tower128; 2],
    /// Local PRG seed generating diagonal self-MAC masks `keys[p][p]` (`0` wire bloat).
    diag_mask_seed: [u8; 32],
    peers: Vec<PcgPeerSeedMaterial>,
    /// Public 1-bit `Ferret`-style correlation syndrome `\delta_\ell = z_\ell \oplus (x_\ell \wedge y_\ell)` (`8,200 B`).
    delta_words: Vec<u64>,
    /// Pre-authenticated unweighted companion sums `[\bigoplus_\ell \tilde{A}_{L,\ell} \cdot y_\ell]` (`L = 0, 1`).
    tilde_c_sums: [PcgAuthTower128Share; 2],
    /// `8` authenticated 128-bit `Tower128` Beaver triples.
    tower_triples: Vec<PcgAuthTower128TripleShare>,
}

impl fmt::Debug for PcgPartySeed {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PcgPartySeed")
            .field("party_id", &self.party_id)
            .field("num_parties", &self.num_parties)
            .field("tree_depth", &self.tree_depth)
            .finish_non_exhaustive()
    }
}

impl Drop for PcgPartySeed {
    fn drop(&mut self) {
        wipe_u128s(core::slice::from_mut(&mut self.mac_alpha[0].0));
        wipe_u128s(core::slice::from_mut(&mut self.mac_alpha[1].0));
        wipe_bytes(&mut self.diag_mask_seed);
    }
}

/// Locally expanded PCG correlation vault (`65,600` Boolean triples + `8` `Tower128` triples +
/// sacrifice companion masks), produced by [`PcgPartySeed::expand_local`] with **zero** network I/O.
pub struct PcgExpandedPartyVault {
    pub session_id: [u8; 32],
    pub party_id: usize,
    pub num_parties: usize,
    pub mac_alpha: [Tower128; 2],
    pub bool_triple_words: Vec<PcgAuthBoolTripleWord64>,
    pub tower_triples: Vec<PcgAuthTower128TripleShare>,
    /// Sacrifice companion masks `[\tilde{A}_{lane, \ell}] \in \mathcal{T}_7` (`lane = 0, 1`, `\ell = 0..65,600`).
    pub companion_a: [Vec<PcgAuthTower128Share>; 2],
    pub companion_c_sums: [PcgAuthTower128Share; 2],
}

impl fmt::Debug for PcgExpandedPartyVault {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PcgExpandedPartyVault")
            .field("party_id", &self.party_id)
            .field("num_parties", &self.num_parties)
            .finish_non_exhaustive()
    }
}

impl Drop for PcgExpandedPartyVault {
    fn drop(&mut self) {
        wipe_tower128(&mut self.mac_alpha);
    }
}

impl PcgExpandedPartyVault {
    /// Total number of authenticated Boolean Beaver triples in this expanded vault (`65,600`).
    #[inline]
    pub fn num_boolean_triples(&self) -> usize {
        self.bool_triple_words.len() * 64
    }
}

/// Single-block `SHAKE256` (`Keccak-f[1600]`) GGM internal node expansion:
/// expands `node_seed: [u8; 16]` at `(domain_tag, tree_id, level)` into `(left: [u8; 16], right: [u8; 16])`.
#[inline]
fn ggm_expand_node_shake256(
    session_id: &[u8; 32],
    tree_tag: u8,
    level: u8,
    node_seed: &[u8; 16],
) -> ([u8; 16], [u8; 16]) {
    let mut state = [0u64; 25];
    let mut blk = [0u8; 72];
    blk[0..16].copy_from_slice(b"QSAG.PCG.GGM.ND1");
    blk[16..48].copy_from_slice(session_id);
    blk[48] = tree_tag;
    blk[49] = level;
    blk[50..66].copy_from_slice(node_seed);
    blk[66] = 0x1F; // SHAKE256 pad start (`rate = 136` bytes = `17` u64 lanes)
    for w in 0..9 {
        state[w] = u64::from_le_bytes(core::array::from_fn(|array_index| {
            (blk[8 * w..8 * (w + 1)])[array_index]
        }));
    }
    state[16] ^= 0x80u64 << 56;
    keccak_f1600(&mut state);

    let mut left = [0u8; 16];
    let mut right = [0u8; 16];
    left[0..8].copy_from_slice(&state[0].to_le_bytes());
    left[8..16].copy_from_slice(&state[1].to_le_bytes());
    right[0..8].copy_from_slice(&state[2].to_le_bytes());
    right[8..16].copy_from_slice(&state[3].to_le_bytes());
    wipe_bytes(&mut blk);
    wipe_u64s(&mut state);
    (left, right)
}

/// Single-block `SHAKE256` (`Keccak-f[1600]`) GGM leaf expansion:
/// expands `leaf_seed: [u8; 16]` into two 128-bit `Tower128` MAC/key tags `(lane0, lane1)`.
#[inline]
fn ggm_expand_leaf_tags_shake256(
    session_id: &[u8; 32],
    tree_tag: u8,
    leaf_idx: u32,
    leaf_seed: &[u8; 16],
) -> [u128; 2] {
    let mut state = [0u64; 25];
    let mut blk = [0u8; 72];
    blk[0..16].copy_from_slice(b"QSAG.PCG.GGM.LF1");
    blk[16..48].copy_from_slice(session_id);
    blk[48] = tree_tag;
    blk[49..53].copy_from_slice(&leaf_idx.to_le_bytes());
    blk[53..69].copy_from_slice(leaf_seed);
    blk[69] = 0x1F;
    for w in 0..9 {
        state[w] = u64::from_le_bytes(core::array::from_fn(|array_index| {
            (blk[8 * w..8 * (w + 1)])[array_index]
        }));
    }
    state[16] ^= 0x80u64 << 56;
    keccak_f1600(&mut state);

    let lane0 = (state[0] as u128) | ((state[1] as u128) << 64);
    let lane1 = (state[2] as u128) | ((state[3] as u128) << 64);
    wipe_bytes(&mut blk);
    wipe_u64s(&mut state);
    [lane0, lane1]
}

/// Sender full-tree `SHAKE256` GGM evaluation: returns `(leaf_tags: Vec<[u128; 2]>, level_lr_xors: Vec<([u8; 16], [u8; 16])>)`.
fn ggm_eval_sender_full(
    session_id: &[u8; 32],
    tree_tag: u8,
    depth: usize,
    root_seed: &[u8; 16],
) -> SpcotPunctureOutput {
    let mut cur_level = Vec::with_capacity(1);
    cur_level.push(*root_seed);
    let mut level_lr_xors = Vec::with_capacity(depth);

    for lvl in 0..depth {
        let mut next_level = Vec::with_capacity(cur_level.len() * 2);
        let mut l_xor = [0u8; 16];
        let mut r_xor = [0u8; 16];
        for nodes in cur_level.chunks(4) {
            let mut states = [[0u64; 25]; 4];
            for (i, node) in nodes.iter().enumerate() {
                let mut block = [0u8; 72];
                block[..16].copy_from_slice(b"QSAG.PCG.GGM.ND1");
                block[16..48].copy_from_slice(session_id);
                block[48] = tree_tag;
                block[49] = lvl as u8;
                block[50..66].copy_from_slice(node);
                block[66] = 0x1f;
                #[expect(
                    clippy::chunks_exact_to_as_chunks,
                    reason = "Keep the workspace Rust 1.85 minimum; slice as_chunks requires a newer compiler"
                )]
                for (word, bytes) in states[i].iter_mut().zip(block.chunks_exact(8)) {
                    *word = u64::from_le_bytes(core::array::from_fn(|array_index| {
                        (bytes)[array_index]
                    }));
                }
                states[i][16] = 0x80u64 << 56;
                wipe_bytes(&mut block);
            }
            qsag_asm::keccak_f1600_batch(&mut states[..nodes.len()]);
            for state in &mut states[..nodes.len()] {
                let mut left = [0u8; 16];
                let mut right = [0u8; 16];
                left[..8].copy_from_slice(&state[0].to_le_bytes());
                left[8..].copy_from_slice(&state[1].to_le_bytes());
                right[..8].copy_from_slice(&state[2].to_le_bytes());
                right[8..].copy_from_slice(&state[3].to_le_bytes());
                for b in 0..16 {
                    l_xor[b] ^= left[b];
                    r_xor[b] ^= right[b];
                }
                next_level.push(left);
                next_level.push(right);
                wipe_bytes(&mut left);
                wipe_bytes(&mut right);
                wipe_u64s(state);
            }
        }
        for node in &mut cur_level {
            wipe_bytes(node);
        }
        cur_level = next_level;
        level_lr_xors.push((l_xor, r_xor));
    }

    let num_leaves = 1usize << depth;
    let mut leaf_tags = Vec::with_capacity(num_leaves);
    for (u, cur_level_u_item) in cur_level[..num_leaves].iter_mut().enumerate() {
        leaf_tags.push(ggm_expand_leaf_tags_shake256(
            session_id,
            tree_tag,
            u as u32,
            &*cur_level_u_item,
        ));
        wipe_bytes(&mut *cur_level_u_item);
    }
    (leaf_tags, level_lr_xors)
}

/// Receiver punctured-tree `SHAKE256` GGM evaluation from a compressed `depth * 16 B` copath:
/// reconstructs exact leaf tags at every `u != punctured_idx`, and fills `punctured_idx` from the
/// masked correlation so `mac_R[u] ^ key_S[u] == (u == p^*) * target_delta`.
fn ggm_eval_receiver_punctured(
    session_id: &[u8; 32],
    tree_tag: u8,
    depth: usize,
    punctured_idx: usize,
    copath: &[[u8; 16]],
    punctured_mode_sum_or_direct: ([u128; 2], bool),
) -> Vec<[u128; 2]> {
    let mut cur_level = vec![[0u8; 16]; 1];
    let mut missing_prefix = 0usize;

    for (lvl, copath_lvl_item) in copath[..depth].iter().enumerate() {
        let bit = (punctured_idx >> (depth - 1 - lvl)) & 1;
        let mut next_level = vec![[0u8; 16]; cur_level.len() * 2];
        let mut known_xor = [0u8; 16];

        for (idx, node) in cur_level.iter().enumerate() {
            if idx == missing_prefix {
                continue;
            }
            let (left, right) = ggm_expand_node_shake256(session_id, tree_tag, lvl as u8, node);
            if bit == 0 {
                for b in 0..16 {
                    known_xor[b] ^= right[b];
                }
            } else {
                for b in 0..16 {
                    known_xor[b] ^= left[b];
                }
            }
            next_level[2 * idx] = left;
            next_level[2 * idx + 1] = right;
        }

        let mut recovered_sibling = [0u8; 16];
        for b in 0..16 {
            recovered_sibling[b] = (*copath_lvl_item)[b] ^ known_xor[b];
        }
        let sibling_pos = (missing_prefix << 1) | (bit ^ 1);
        next_level[sibling_pos] = recovered_sibling;
        missing_prefix = (missing_prefix << 1) | bit;

        for node in &mut cur_level {
            wipe_bytes(node);
        }
        cur_level = next_level;
    }

    let num_leaves = 1usize << depth;
    let mut leaf_tags = vec![[0u128; 2]; num_leaves];
    let mut partial_xor = [0u128; 2];
    for u in 0..num_leaves {
        if u == punctured_idx {
            continue;
        }
        let tags = ggm_expand_leaf_tags_shake256(session_id, tree_tag, u as u32, &cur_level[u]);
        leaf_tags[u] = tags;
        partial_xor[0] ^= tags[0];
        partial_xor[1] ^= tags[1];
        wipe_bytes(&mut cur_level[u]);
    }

    let (corr, xor_with_partial) = punctured_mode_sum_or_direct;
    if xor_with_partial {
        leaf_tags[punctured_idx] = [corr[0] ^ partial_xor[0], corr[1] ^ partial_xor[1]];
    } else {
        leaf_tags[punctured_idx] = corr;
    }
    leaf_tags
}

/// Deterministic Quasi-Cyclic LPN parity-check / generator schedule (`base`, odd `stride`) derived
/// via `SHAKE256` from `(session_id, bundle_tag)` for `num_words` 64-bit blocks across `4` trees.
struct QcLpnParitySchedule {
    /// Flattened `[word * 12 + tree * 3 + tap] -> (base, odd_stride)` masked to `(1 << depth) - 1`.
    base_and_stride: Vec<(u32, u32)>,
    leaf_mask: usize,
}

impl QcLpnParitySchedule {
    fn derive(session_id: &[u8; 32], bundle_tag: &[u8], depth: usize, num_words: usize) -> Self {
        let leaf_mask = (1usize << depth) - 1;
        let entries = num_words * PCG_TREES_PER_BUNDLE * PCG_TAPS_PER_TREE;
        let mut xof = Shake256Xof::new_shake256();
        xof.absorb(b"QSAG.PCG.QCLPN.SCHED/v1");
        xof.absorb(session_id);
        xof.absorb(bundle_tag);
        xof.absorb(&(depth as u32).to_le_bytes());
        let mut raw = vec![0u8; entries * 4];
        xof.squeeze(&mut raw);

        let mut base_and_stride = Vec::with_capacity(entries);
        for e in 0..entries {
            let b = (u16::from_le_bytes([raw[4 * e], raw[4 * e + 1]]) as usize) & leaf_mask;
            let s =
                ((u16::from_le_bytes([raw[4 * e + 2], raw[4 * e + 3]]) as usize) | 1) & leaf_mask;
            base_and_stride.push((b as u32, s as u32));
        }
        Self {
            base_and_stride,
            leaf_mask,
        }
    }

    /// Compress `4` GGM leaf-tag vectors (`[tree][0..2^depth]`) into `num_words * 64` LPN output
    /// tags AND compute the sparse noise bit-words `H * e` for `punctured_indices: Option<[usize; 4]>`.
    fn compress_binary_bundle(
        &self,
        num_words: usize,
        tree_leaf_tags: &[Vec<[u128; 2]>],
        punctured_indices: Option<[usize; 4]>,
    ) -> (Vec<u64>, Vec<[[u128; 2]; 64]>) {
        let mut bit_words = vec![0u64; num_words];
        let mut out_tags = vec![[[0u128; 2]; 64]; num_words];
        let mask = self.leaf_mask;

        for k in 0..num_words {
            let mut w_bits = 0u64;
            let row_tags = &mut out_tags[k];
            for tree in 0..PCG_TREES_PER_BUNDLE {
                let leaves = &tree_leaf_tags[tree];
                let p_star = punctured_indices.map(|arr| arr[tree]).unwrap_or(usize::MAX);
                for tap in 0..PCG_TAPS_PER_TREE {
                    let (base, stride) = self.base_and_stride
                        [(k * PCG_TREES_PER_BUNDLE + tree) * PCG_TAPS_PER_TREE + tap];
                    let mut col = base as usize;
                    let step = stride as usize;
                    for (bit, row_tags_bit_item) in row_tags[..64].iter_mut().enumerate() {
                        let t = leaves[col];
                        (*row_tags_bit_item)[0] ^= t[0];
                        (*row_tags_bit_item)[1] ^= t[1];
                        if col == p_star {
                            w_bits ^= 1u64 << bit;
                        }
                        col = (col + step) & mask;
                    }
                }
            }
            bit_words[k] = w_bits;
        }
        (bit_words, out_tags)
    }

    /// Compress `4` `Tower128` VOLE GGM trees into `num_words * 64` values + 2-lane tags.
    fn compress_tower_bundle(
        &self,
        num_words: usize,
        tree_leaf_tags: &[Vec<[u128; 2]>],
        punctured: Option<[(usize, Tower128); 4]>,
    ) -> (Vec<Tower128>, Vec<[u128; 2]>) {
        let total = num_words * 64;
        let mut vals = vec![Tower128::ZERO; total];
        let mut tags = vec![[0u128; 2]; total];
        let mask = self.leaf_mask;

        for k in 0..num_words {
            for tree in 0..PCG_TREES_PER_BUNDLE {
                let leaves = &tree_leaf_tags[tree];
                let (p_star, beta) = punctured
                    .map(|arr| arr[tree])
                    .unwrap_or((usize::MAX, Tower128::ZERO));
                for tap in 0..PCG_TAPS_PER_TREE {
                    let (base, stride) = self.base_and_stride
                        [(k * PCG_TREES_PER_BUNDLE + tree) * PCG_TAPS_PER_TREE + tap];
                    let mut col = base as usize;
                    let step = stride as usize;
                    for bit in 0..64 {
                        let idx = 64 * k + bit;
                        let t = leaves[col];
                        tags[idx][0] ^= t[0];
                        tags[idx][1] ^= t[1];
                        if col == p_star {
                            vals[idx] = vals[idx].add(beta);
                        }
                        col = (col + step) & mask;
                    }
                }
            }
        }
        (vals, tags)
    }
}

/// LHL-amplified (`4` uniform `Tower128` OT masks = `512` bits per element -> `< 2^{-192}`
/// selective-failure advantage) 2-lane BDOZ authentication of `vals_per_party[party][k]` via `OtMesh`.
fn authenticate_tower128_batch(
    session_id: &[u8; 32],
    ot_mesh: &mut OtMesh,
    alphas: &[[Tower128; 2]],
    vals_per_party: &[Vec<Tower128>],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<Vec<PcgAuthTower128Share>>, PreprocessError> {
    let n = ot_mesh.n;
    let count = vals_per_party[0].len();
    let mut out: Vec<Vec<PcgAuthTower128Share>> = (0..n)
        .map(|p| {
            (0..count)
                .map(|k| {
                    let mut sh = PcgAuthTower128Share::zero(n);
                    sh.value = vals_per_party[p][k];
                    sh
                })
                .collect()
        })
        .collect();
    if count == 0 {
        return Ok(out);
    }

    let mut r_masks = vec![vec![[Tower128::ZERO; 4]; count]; n];
    let mut choice_words = crate::wipe::secret_vecs_with_capacity(n, 8 * count);
    for j in 0..n {
        #[expect(
            clippy::needless_range_loop,
            reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows"
        )]
        for k in 0..count {
            #[expect(
                clippy::needless_range_loop,
                reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows"
            )]
            for m in 0..4 {
                let r = party_rngs[j].next_tower128();
                r_masks[j][k][m] = r;
                choice_words[j].push(r.0 as u64);
                choice_words[j].push((r.0 >> 64) as u64);
            }
        }
    }

    let mut raw_k = vec![vec![vec![[[Tower128::ZERO; 4]; 2]; count]; n]; n];
    let mut raw_m = vec![vec![vec![[[Tower128::ZERO; 4]; 2]; count]; n]; n];

    for i in 0..n {
        for k in 0..count {
            for (lane, alpha) in alphas[i].iter().enumerate() {
                let m = party_rngs[i].next_tower128();
                out[i][k].keys[i][lane] = m;
                out[i][k].macs[i][lane] = m.add(alpha.mul(vals_per_party[i][k]));
            }
        }
        for j in 0..n {
            if i == j {
                continue;
            }
            let (send_pads, recv_pads) =
                ot_mesh.run_correlated_ot_words(i, j, &choice_words[j], party_rngs)?;
            for k in 0..count {
                for m in 0..4 {
                    let rj_raw = black_box(r_masks[j][k][m].0);
                    let base_off = (4 * k + m) * 128;
                    for lane in 0..2 {
                        let alpha_il = alphas[i][lane];
                        let mut k_sum = Tower128::ZERO;
                        let mut m_sum = Tower128::ZERO;
                        for bit in 0..128 {
                            let (p0, p1) = &send_pads[base_off + bit];
                            let pad0 = Tower128(u128::from_le_bytes(core::array::from_fn(
                                |array_index| (p0[16 * lane..16 * (lane + 1)])[array_index],
                            )));
                            let pad1 = Tower128(u128::from_le_bytes(core::array::from_fn(
                                |array_index| (p1[16 * lane..16 * (lane + 1)])[array_index],
                            )));
                            let mk = party_rngs[i].next_tower128();
                            k_sum = k_sum.add(mk);
                            let basis = Tower128(1u128 << bit);
                            let ct0 = mk.add(pad0);
                            let ct1 = mk.add(alpha_il.mul(basis)).add(pad1);

                            let pad_c = Tower128(u128::from_le_bytes(core::array::from_fn(
                                |array_index| {
                                    (recv_pads[base_off + bit][16 * lane..16 * (lane + 1)])
                                        [array_index]
                                },
                            )));
                            let choice = ((rj_raw >> bit) & 1) == 1;
                            let cmask = 0u128.wrapping_sub(black_box(choice as u128));
                            let sel = Tower128(ct0.0 ^ (cmask & (ct0.0 ^ ct1.0)));
                            m_sum = m_sum.add(sel.add(pad_c));
                        }
                        raw_k[i][j][k][lane][m] = k_sum;
                        raw_m[i][j][k][lane][m] = m_sum;
                    }
                }
            }
        }
    }

    let coin = run_commit_and_open_coin(session_id, b"PCG_AUTH_T128_LHL", session_id, party_rngs)?;
    let mut xof = Cshake256Xof::new(b"QSAG.PCG.AUTH.T128.LHL/v1");
    xof.absorb(&coin);
    let mut g_weights = vec![[Tower128::ONE; 4]; count];
    for g_weights_k_item in g_weights[..count].iter_mut() {
        for m in 1..4 {
            let mut gb = [0u8; 16];
            xof.squeeze(&mut gb);
            (*g_weights_k_item)[m] = Tower128(u128::from_le_bytes(gb) | 1);
        }
    }

    let mut diffs = vec![vec![Tower128::ZERO; count]; n];
    for j in 0..n {
        for k in 0..count {
            let mut r_comb = r_masks[j][k][0];
            for m in 1..4 {
                r_comb = r_comb.add(g_weights[k][m].mul(r_masks[j][k][m]));
            }
            diffs[j][k] = vals_per_party[j][k].add(r_comb);
            wipe_tower128(&mut r_masks[j][k]);
        }
        wipe_u64s(&mut choice_words[j]);
    }

    for i in 0..n {
        for j in 0..n {
            if i == j {
                continue;
            }
            for k in 0..count {
                let d = diffs[j][k];
                for lane in 0..2 {
                    let mut k_comb = raw_k[i][j][k][lane][0];
                    let mut m_comb = raw_m[i][j][k][lane][0];
                    for m in 1..4 {
                        let g = g_weights[k][m];
                        k_comb = k_comb.add(g.mul(raw_k[i][j][k][lane][m]));
                        m_comb = m_comb.add(g.mul(raw_m[i][j][k][lane][m]));
                    }
                    k_comb = k_comb.add(alphas[i][lane].mul(d));
                    out[i][k].keys[j][lane] = k_comb;
                    out[j][k].macs[i][lane] = m_comb;
                    wipe_tower128(&mut raw_k[i][j][k][lane]);
                    wipe_tower128(&mut raw_m[i][j][k][lane]);
                }
            }
        }
    }
    Ok(out)
}

/// Transfer `depth` compressed 16-byte GGM copath siblings from Sender `s` to Receiver `r` via `OtMesh`.
fn transfer_ggm_copath_via_ot(
    ot_mesh: &mut OtMesh,
    s: usize,
    r: usize,
    depth: usize,
    punctured_idx: usize,
    level_lr_xors: &[([u8; 16], [u8; 16])],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<[u8; 16]>, PreprocessError> {
    let mut choice_word = 0u64;
    for lvl in 0..depth {
        let path_bit = (punctured_idx >> (depth - 1 - lvl)) & 1;
        // When `path_bit == 0` (puncture left), Receiver needs `R_xor` (`choice = 1`);
        // when `path_bit == 1` (puncture right), Receiver needs `L_xor` (`choice = 0`).
        let sib_choice = (path_bit ^ 1) as u64;
        choice_word |= sib_choice << lvl;
    }
    let (send_pads, recv_pads) =
        ot_mesh.run_correlated_ot_words(s, r, &[choice_word], party_rngs)?;
    let mut copath = Vec::with_capacity(depth);
    for lvl in 0..depth {
        let (p0, p1) = &send_pads[lvl];
        let mut ct0 = [0u8; 16];
        let mut ct1 = [0u8; 16];
        for b in 0..16 {
            ct0[b] = level_lr_xors[lvl].0[b] ^ p0[b];
            ct1[b] = level_lr_xors[lvl].1[b] ^ p1[b];
        }
        let sib_choice = ((choice_word >> lvl) & 1) == 1;
        let cmask = 0u8.wrapping_sub(black_box(sib_choice as u8));
        let mut out = [0u8; 16];
        for b in 0..16 {
            let sel = ct0[b] ^ (cmask & (ct0[b] ^ ct1[b]));
            out[b] = sel ^ recv_pads[lvl][b];
        }
        copath.push(out);
    }
    wipe_u64s(core::slice::from_mut(&mut choice_word));
    Ok(copath)
}

/// Namespace for sublinear Silent-OT / `SHAKE256` GGM Puncturable-PRF + QC-LPN `PCG` seed setup,
/// zero-I/O local expansion, and 2-lane `Tower128` BDOZ batch MAC sacrifice (`2^{-256}` soundness).
