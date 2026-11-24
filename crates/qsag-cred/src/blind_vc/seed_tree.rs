use super::*;

// ============================================================================
// N=256 GGM Seed Tree & 8-Way SIMD Shake256 Party Tape Engine
// ============================================================================

pub(super) const fn attribute_commitment_gates(slots: usize) -> usize {
    // Explicit padding consumes an additional permutation for exact rate multiples.
    ((slots + 7) / 6 + 1) * (GATES_PER_PERM12 / 3)
}
pub(super) const SD_NUM_PERMS: usize = 1 + VC_ACCUMULATOR_DEPTH; // Merkle path and scope.
pub(super) const SD_MERKLE_MUX_GATES: usize = VC_ACCUMULATOR_DEPTH * (1 + 6); // One Boolean check and six limb swaps per level.
pub(super) const SD_TOTAL_GATES: usize = SD_NUM_PERMS * GATES_PER_PERM12
    + 2 * attribute_commitment_gates(MAX_VC_ATTRS)
    + SD_MERKLE_MUX_GATES;
pub(super) const SD_CHECKED_GATES: usize = SD_TOTAL_GATES + VC_FINAL_OUTPUTS;
pub(super) const SD_GRID_B: usize = 192;
pub(super) const SD_GRID_L: usize = 192;
pub(super) const SD_RPOLY_COEFFS: usize = 2 * SD_GRID_B; // Degrees 0..=2B except B.

const _: () = assert!(SD_GRID_B * SD_GRID_L >= SD_CHECKED_GATES);

pub(super) fn ggm_expand_children(
    parent: &[u8; 32],
    presentation_nonce: &[u8; 32],
    rep: u32,
    depth: u8,
    node_idx: u16,
) -> ([u8; 32], [u8; 32]) {
    let mut msg = [0u8; 92];
    msg[0..20].copy_from_slice(b"QSAG.VC.SD_GGM_NODE1");
    msg[20..52].copy_from_slice(presentation_nonce);
    msg[52..56].copy_from_slice(&rep.to_le_bytes());
    msg[56] = depth;
    msg[57..59].copy_from_slice(&node_idx.to_le_bytes());
    msg[59] = 0;
    msg[60..92].copy_from_slice(parent);

    let mut sp = Shake256::new();
    sp.absorb(&msg);
    sp.finalize(0x1F);
    // Both child seeds are secret; the squeeze buffer is erased on drop.
    let mut children = SecretBuffer([0u8; 64]);
    sp.squeeze(&mut children.0);
    ct_zeroize_bytes(&mut msg);
    (
        core::array::from_fn(|i| children[i]),
        core::array::from_fn(|i| children[32 + i]),
    )
}

pub(super) fn expand_ggm_tree_256_into(
    root_seed: &[u8; 32],
    presentation_nonce: &[u8; 32],
    rep: u32,
    tree: &mut [[u8; 32]],
) {
    debug_assert_eq!(tree.len(), 2 * VC_SD_LIMBO_PARTIES);
    tree[0] = [0u8; 32];
    tree[1] = *root_seed;
    for depth in 0..VC_SD_GGM_DEPTH {
        let level_start = 1usize << depth;
        let level_width = 1usize << depth;
        for idx in 0..level_width {
            let parent_pos = level_start + idx;
            let children = SecretBuffer(ggm_expand_children(
                &tree[parent_pos],
                presentation_nonce,
                rep,
                depth as u8,
                idx as u16,
            ));
            tree[2 * parent_pos] = children.0.0;
            tree[2 * parent_pos + 1] = children.0.1;
        }
    }
}

pub(super) fn extract_ggm_copath(
    tree: &[[u8; 32]],
    hidden_party: u8,
) -> [[u8; 32]; VC_SD_GGM_DEPTH] {
    let leaf_pos = VC_SD_LIMBO_PARTIES + (hidden_party as usize);
    core::array::from_fn(|step| tree[(leaf_pos >> step) ^ 1])
}

pub(super) fn reconstruct_ggm_leaves_256(
    copath: &[[u8; 32]; VC_SD_GGM_DEPTH],
    hidden_party: u8,
    presentation_nonce: &[u8; 32],
    rep: u32,
) -> [[u8; 32]; VC_SD_LIMBO_PARTIES] {
    let mut tree = SecretBuffer([[0u8; 32]; 2 * VC_SD_LIMBO_PARTIES]);
    let mut known = [false; 2 * VC_SD_LIMBO_PARTIES];
    let leaf_pos = VC_SD_LIMBO_PARTIES + (hidden_party as usize);

    for (step, &sib_seed) in copath.iter().enumerate() {
        let sib_pos = (leaf_pos >> step) ^ 1;
        tree.0[sib_pos] = sib_seed;
        known[sib_pos] = true;
    }

    for depth in 1..VC_SD_GGM_DEPTH {
        let level_start = 1usize << depth;
        let level_width = 1usize << depth;
        for idx in 0..level_width {
            let pos = level_start + idx;
            if known[pos] {
                let parent_seed = tree.0[pos];
                let (left, right) = ggm_expand_children(
                    &parent_seed,
                    presentation_nonce,
                    rep,
                    depth as u8,
                    idx as u16,
                );
                tree.0[2 * pos] = left;
                tree.0[2 * pos + 1] = right;
                known[2 * pos] = true;
                known[2 * pos + 1] = true;
            }
        }
    }

    let mut leaves = [[0u8; 32]; VC_SD_LIMBO_PARTIES];
    for p in 0..VC_SD_LIMBO_PARTIES {
        if p != hidden_party as usize {
            debug_assert!(known[VC_SD_LIMBO_PARTIES + p]);
            leaves[p] = tree.0[VC_SD_LIMBO_PARTIES + p];
        }
    }
    leaves
}

/// 8-way parallel `SHAKE256` (`rate = 136` bytes = `17` `u64` words) PRG sponge driven by
/// [`qsag_asm::keccak_f1600_x8`]. Produces bit-for-bit identical output to scalar [`Shake256`]
/// initialized with `domain(24B) || presentation_nonce(32B) || leaf_seed(32B) || (rep_u32 | (party_u32 << 32))(8B)`.
pub(super) struct Shake256PartyBatch8 {
    state: qsag_asm::KeccakState8x,
    word_pos: [usize; 8],
}

impl Drop for Shake256PartyBatch8 {
    fn drop(&mut self) {
        qsag_asm::volatile_fill(&mut self.state.0, [0u64; 8]);
    }
}

pub(super) const PARTY_TAPE_DOMAIN_24: &[u8; 24] = b"QSAG.VC.LIMBO_TAPE.V1\0\0\0";

impl Shake256PartyBatch8 {
    pub(super) fn new(
        presentation_nonce: &[u8; 32],
        rep: u32,
        base_party: usize,
        leaf_seeds: &[[u8; 32]; 8],
    ) -> Self {
        let mut state = qsag_asm::KeccakState8x::default();
        for lane in 0..3 {
            let w = u64::from_le_bytes(
                PARTY_TAPE_DOMAIN_24[lane * 8..(lane + 1) * 8]
                    .try_into()
                    .unwrap(),
            );
            state.0[lane] = [w; 8];
        }
        for lane in 0..4 {
            let w = u64::from_le_bytes(
                presentation_nonce[lane * 8..(lane + 1) * 8]
                    .try_into()
                    .unwrap(),
            );
            state.0[3 + lane] = [w; 8];
        }
        for (inst, leaf_seed) in leaf_seeds.iter().enumerate() {
            for lane in 0..4 {
                let w = u64::from_le_bytes(leaf_seed[lane * 8..(lane + 1) * 8].try_into().unwrap());
                state.0[7 + lane][inst] = w;
            }
            let tag = (rep as u64) | (((base_party + inst) as u64) << 32);
            state.0[11][inst] = tag;
        }
        // 96 bytes absorbed (lanes 0..12); SHAKE256 pad 0x1F at byte 96 (lane 12 LSB)
        // and 0x80 at byte 135 (lane 16 MSB).
        state.0[12] = [0x1Fu64; 8];
        state.0[16] = [0x80u64 << 56; 8];
        qsag_asm::keccak_f1600_x8(&mut state);
        Self {
            state,
            word_pos: [0usize; 8],
        }
    }

    /// Extract the initial 32-byte commitment salt (`lanes 0..4`) for each of the 8 parties.
    pub(super) fn extract_salts_1(&mut self) -> [[u8; 32]; 8] {
        debug_assert_eq!(self.word_pos, [0usize; 8]);
        let mut salts = [[0u8; 32]; 8];
        for (inst, (salt, pos)) in salts.iter_mut().zip(&mut self.word_pos).enumerate() {
            for lane in 0..4 {
                salt[lane * 8..(lane + 1) * 8]
                    .copy_from_slice(&self.state.0[lane][inst].to_le_bytes());
            }
            *pos = 4;
        }
        salts
    }

    /// Squeeze `count` canonical Goldilocks field elements (strict core lift) into each
    /// active lane's destination buffer (`active_mask[inst] == false` skips inactive lanes).
    pub(super) fn squeeze_canonical_gl(
        &mut self,
        active_mask: [bool; 8],
        outs: &mut [Vec<u64>; 8],
        count: usize,
    ) {
        let mut done = [false; 8];
        let mut all_done = true;
        for inst in 0..8 {
            outs[inst].secret_wipe();
            outs[inst].clear();
            if !active_mask[inst] || count == 0 {
                done[inst] = true;
            } else {
                outs[inst].reserve(count);
                all_done = false;
            }
        }
        while !all_done {
            let mut need_perm = false;
            all_done = true;
            for inst in 0..8 {
                if done[inst] {
                    continue;
                }
                while self.word_pos[inst] < 17 {
                    let cand = Goldilocks::from_canonical(self.state.0[self.word_pos[inst]][inst]);
                    self.word_pos[inst] += 1;
                    if let Ok(limb) = cand {
                        outs[inst].push(limb.to_canonical_u64());
                        if outs[inst].len() == count {
                            done[inst] = true;
                            break;
                        }
                    }
                }
                if !done[inst] {
                    all_done = false;
                    need_perm = true;
                }
            }
            if need_perm {
                qsag_asm::keccak_f1600_x8(&mut self.state);
                for (&is_done, pos) in done.iter().zip(&mut self.word_pos) {
                    if !is_done {
                        *pos = 0;
                    }
                }
            }
        }
    }
}

pub(super) fn digest_limbo_aux(delta_w: &[u64], delta_z: &[u64], delta_c: &[u64; 5]) -> [u8; 32] {
    let mut sp = Shake256::new();
    sp.absorb(b"QSAG.VC.LIMBO_AUX.V1");
    sp.absorb(&(delta_w.len() as u32).to_le_bytes());
    for &w in delta_w {
        sp.absorb(&w.to_le_bytes());
    }
    sp.absorb(&(delta_z.len() as u32).to_le_bytes());
    for &z in delta_z {
        sp.absorb(&z.to_le_bytes());
    }
    for &c in delta_c {
        sp.absorb(&c.to_le_bytes());
    }
    sp.finalize(0x1F);
    let mut out = [0u8; 32];
    sp.squeeze(&mut out);
    out
}

pub(super) fn commit_limbo_party_r1(
    presentation_nonce: &[u8; 32],
    rep: u32,
    party: u16,
    leaf_seed: &[u8; 32],
    aux_digest: Option<&[u8; 32]>,
    salt_1: &[u8; 32],
) -> [u8; 32] {
    let mut sp = Shake256::new();
    sp.absorb(b"QSAG.VC.LIMBO_R1_COM.V1");
    sp.absorb(presentation_nonce);
    sp.absorb(&rep.to_le_bytes());
    sp.absorb(&party.to_le_bytes());
    sp.absorb(leaf_seed);
    match aux_digest {
        None => sp.absorb(&[0u8]),
        Some(d) => {
            sp.absorb(&[1u8]);
            sp.absorb(d);
        }
    }
    sp.absorb(salt_1);
    sp.finalize(0x1F);
    let mut out = [0u8; 32];
    sp.squeeze(&mut out);
    out
}

pub(super) fn hash_limbo_party_online(
    presentation_nonce: &[u8; 32],
    rep: u32,
    party: u16,
    alpha_i: &[Fp5; SD_GRID_L],
    beta_i: &[Fp5; SD_GRID_L],
    sigma_i: Fp5,
) -> [u8; 32] {
    let mut sp = Shake256::new();
    sp.absorb(b"QSAG.VC.LIMBO_R2_HASH.V1");
    sp.absorb(presentation_nonce);
    sp.absorb(&rep.to_le_bytes());
    sp.absorb(&party.to_le_bytes());
    let mut raw: [u8; 40];
    for a in alpha_i {
        raw = a.to_le_bytes();
        sp.absorb(&raw);
    }
    for b in beta_i {
        raw = b.to_le_bytes();
        sp.absorb(&raw);
    }
    raw = sigma_i.to_le_bytes();
    sp.absorb(&raw);
    ct_zeroize_bytes(&mut raw);
    sp.finalize(0x1F);
    let mut out = [0u8; 32];
    sp.squeeze(&mut out);
    out
}

pub(super) fn expand_gamma_weights(
    gamma_seed: &[u8; 32],
    rep: u32,
) -> ([Fp5; SD_GRID_B], [Fp5; SD_GRID_L]) {
    let needed = (SD_GRID_B + SD_GRID_L) * 5;
    let limbs = sample_canonical_gl_vec(
        b"QSAG.VC.LIMBO_GAMMA_EXP.V1",
        gamma_seed,
        &rep.to_le_bytes(),
        needed,
    );
    let mut theta = [Fp5::ZERO; SD_GRID_B];
    let mut eta = [Fp5::ZERO; SD_GRID_L];
    for (b, slot) in theta.iter_mut().enumerate() {
        let base = b * 5;
        *slot = Fp5::from_limbs([
            limbs[base],
            limbs[base + 1],
            limbs[base + 2],
            limbs[base + 3],
            limbs[base + 4],
        ]);
    }
    let off = SD_GRID_B * 5;
    for (l, slot) in eta.iter_mut().enumerate() {
        let base = off + l * 5;
        *slot = Fp5::from_limbs([
            limbs[base],
            limbs[base + 1],
            limbs[base + 2],
            limbs[base + 3],
            limbs[base + 4],
        ]);
    }
    (theta, eta)
}

pub(super) fn squeeze_nonzero_eval_points(tr: &mut InterleavedTranscript, tau: usize) -> Vec<Fp5> {
    let mut seed = [0u8; 32];
    tr.squeeze_bytes(b"VC_SD_LIMBO_EVAL_SEED", &mut seed);
    let mut out = Vec::with_capacity(tau);
    let mut counter = 0u64;
    while out.len() < tau {
        let limbs = sample_canonical_gl_vec(
            b"QSAG.VC.LIMBO_EVAL_PT.V1",
            &seed,
            &counter.to_le_bytes(),
            5,
        );
        counter += 1;
        let pt = Fp5::from_limbs([limbs[0], limbs[1], limbs[2], limbs[3], limbs[4]]);
        if !pt.is_zero() {
            out.push(pt);
        }
    }
    ct_zeroize_bytes(&mut seed);
    out
}
