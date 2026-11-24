//! Sparse fixture seed encoding, decoding and local expansion.

use super::*;

fn write_auth_tower128_share(out: &mut Vec<u8>, sh: &PcgAuthTower128Share) {
    out.extend_from_slice(&sh.value.0.to_le_bytes());
    let n = sh.macs.len();
    out.extend_from_slice(&(n as u16).to_le_bytes());
    for q in 0..n {
        out.extend_from_slice(&sh.macs[q][0].0.to_le_bytes());
        out.extend_from_slice(&sh.macs[q][1].0.to_le_bytes());
        out.extend_from_slice(&sh.keys[q][0].0.to_le_bytes());
        out.extend_from_slice(&sh.keys[q][1].0.to_le_bytes());
    }
}

fn read_auth_tower128_share(
    bytes: &[u8],
    cur: &mut usize,
) -> Result<PcgAuthTower128Share, PreprocessError> {
    if *cur + 18 > bytes.len() {
        return Err(PreprocessError::PcgInvalidWireSeed);
    }
    let value = Tower128(u128::from_le_bytes(core::array::from_fn(|array_index| {
        (bytes[*cur..*cur + 16])[array_index]
    })));
    *cur += 16;
    let n = u16::from_le_bytes([bytes[*cur], bytes[*cur + 1]]) as usize;
    *cur += 2;
    validate_frame_count(n, 64, bytes.len() - *cur)?;
    let mut macs = vec![[Tower128::ZERO; 2]; n];
    let mut keys = vec![[Tower128::ZERO; 2]; n];
    for q in 0..n {
        macs[q][0] = Tower128(u128::from_le_bytes(core::array::from_fn(|array_index| {
            (bytes[*cur..*cur + 16])[array_index]
        })));
        *cur += 16;
        macs[q][1] = Tower128(u128::from_le_bytes(core::array::from_fn(|array_index| {
            (bytes[*cur..*cur + 16])[array_index]
        })));
        *cur += 16;
        keys[q][0] = Tower128(u128::from_le_bytes(core::array::from_fn(|array_index| {
            (bytes[*cur..*cur + 16])[array_index]
        })));
        *cur += 16;
        keys[q][1] = Tower128(u128::from_le_bytes(core::array::from_fn(|array_index| {
            (bytes[*cur..*cur + 16])[array_index]
        })));
        *cur += 16;
    }
    Ok(PcgAuthTower128Share { value, macs, keys })
}

impl PcgPartySeed {
    /// Serialize this compact PCG seed to canonical wire bytes (`< 24 KB` for 2–3 parties).
    pub fn to_wire_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(16 * 1024);
        out.extend_from_slice(PCG_WIRE_MAGIC);
        out.extend_from_slice(&self.session_id);
        out.extend_from_slice(&(self.party_id as u16).to_le_bytes());
        out.extend_from_slice(&(self.num_parties as u16).to_le_bytes());
        out.push(self.tree_depth as u8);
        out.extend_from_slice(&self.mac_alpha[0].0.to_le_bytes());
        out.extend_from_slice(&self.mac_alpha[1].0.to_le_bytes());
        out.extend_from_slice(&self.diag_mask_seed);

        out.extend_from_slice(&(self.peers.len() as u16).to_le_bytes());
        for peer in &self.peers {
            out.extend_from_slice(&peer.peer_id.to_le_bytes());
            for st in &peer.bin_sender_trees {
                out.extend_from_slice(&st.root_seed);
            }
            for rt in &peer.bin_receiver_trees {
                out.extend_from_slice(&rt.punctured_idx.to_le_bytes());
                out.extend_from_slice(&rt.punctured_mac_corr[0].0.to_le_bytes());
                out.extend_from_slice(&rt.punctured_mac_corr[1].0.to_le_bytes());
                for node in &rt.copath {
                    out.extend_from_slice(node);
                }
            }
            for st in &peer.tower_sender_trees {
                out.extend_from_slice(&st.root_seed);
            }
            for rt in &peer.tower_receiver_trees {
                out.extend_from_slice(&rt.punctured_idx.to_le_bytes());
                out.extend_from_slice(&rt.punctured_beta.0.to_le_bytes());
                out.extend_from_slice(&rt.punctured_mac_val[0].0.to_le_bytes());
                out.extend_from_slice(&rt.punctured_mac_val[1].0.to_le_bytes());
                for node in &rt.copath {
                    out.extend_from_slice(node);
                }
            }
        }

        out.extend_from_slice(&(self.delta_words.len() as u32).to_le_bytes());
        for &dw in &self.delta_words {
            out.extend_from_slice(&dw.to_le_bytes());
        }
        write_auth_tower128_share(&mut out, &self.tilde_c_sums[0]);
        write_auth_tower128_share(&mut out, &self.tilde_c_sums[1]);
        out.extend_from_slice(&(self.tower_triples.len() as u16).to_le_bytes());
        for tr in &self.tower_triples {
            write_auth_tower128_share(&mut out, &tr.a);
            write_auth_tower128_share(&mut out, &tr.b);
            write_auth_tower128_share(&mut out, &tr.c);
        }
        out
    }

    /// Deserialize a [`PcgPartySeed`] from canonical wire bytes.
    pub fn from_wire_bytes(bytes: &[u8]) -> Result<Self, PreprocessError> {
        if !cfg!(test) {
            return Err(PreprocessError::ExperimentalSparsePcg);
        }
        if bytes.len() > MAX_FRAME_BUDGET || bytes.len() < 111 || &bytes[0..8] != PCG_WIRE_MAGIC {
            return Err(PreprocessError::PcgInvalidWireSeed);
        }
        let mut session_id = [0u8; 32];
        session_id.copy_from_slice(&bytes[8..40]);
        let party_id = u16::from_le_bytes([bytes[40], bytes[41]]) as usize;
        let num_parties = u16::from_le_bytes([bytes[42], bytes[43]]) as usize;
        let tree_depth = bytes[44] as usize;
        if !(PCG_MIN_TREE_DEPTH..=PCG_MAX_TREE_DEPTH).contains(&tree_depth)
            || party_id >= num_parties
            || num_parties < 2
        {
            return Err(PreprocessError::PcgInvalidWireSeed);
        }
        let alpha0 = Tower128(u128::from_le_bytes(core::array::from_fn(|array_index| {
            (bytes[45..61])[array_index]
        })));
        let alpha1 = Tower128(u128::from_le_bytes(core::array::from_fn(|array_index| {
            (bytes[61..77])[array_index]
        })));
        let mut diag_mask_seed = [0u8; 32];
        diag_mask_seed.copy_from_slice(&bytes[77..109]);
        let num_peers = u16::from_le_bytes([bytes[109], bytes[110]]) as usize;
        if num_peers != num_parties - 1 {
            return Err(PreprocessError::PcgInvalidWireSeed);
        }
        let mut cur = 111usize;
        let tower_depth = PCG_MIN_TREE_DEPTH;

        let peer_bytes = 2
            + 3 * PCG_TREES_PER_BUNDLE * (16 + 2 + 32 + 16 * tree_depth)
            + 2 * PCG_TREES_PER_BUNDLE * (16 + 2 + 16 + 32 + 16 * tower_depth);
        validate_frame_count(num_peers, peer_bytes, bytes.len() - cur)?;
        let mut peers = Vec::with_capacity(num_peers);
        for _ in 0..num_peers {
            if cur + 2 > bytes.len() {
                return Err(PreprocessError::PcgInvalidWireSeed);
            }
            let peer_id = u16::from_le_bytes([bytes[cur], bytes[cur + 1]]);
            cur += 2;

            let mut bin_sender_trees = Vec::with_capacity(3 * PCG_TREES_PER_BUNDLE);
            for _ in 0..(3 * PCG_TREES_PER_BUNDLE) {
                if cur + 16 > bytes.len() {
                    return Err(PreprocessError::PcgInvalidWireSeed);
                }
                let mut root_seed = [0u8; 16];
                root_seed.copy_from_slice(&bytes[cur..cur + 16]);
                cur += 16;
                bin_sender_trees.push(GgmSenderTreeSeed { root_seed });
            }

            let mut bin_receiver_trees = Vec::with_capacity(3 * PCG_TREES_PER_BUNDLE);
            for _ in 0..(3 * PCG_TREES_PER_BUNDLE) {
                let need = 2 + 32 + 16 * tree_depth;
                if cur + need > bytes.len() {
                    return Err(PreprocessError::PcgInvalidWireSeed);
                }
                let punctured_idx = u16::from_le_bytes([bytes[cur], bytes[cur + 1]]);
                cur += 2;
                let c0 = Tower128(u128::from_le_bytes(core::array::from_fn(|array_index| {
                    (bytes[cur..cur + 16])[array_index]
                })));
                cur += 16;
                let c1 = Tower128(u128::from_le_bytes(core::array::from_fn(|array_index| {
                    (bytes[cur..cur + 16])[array_index]
                })));
                cur += 16;
                let mut copath = Vec::with_capacity(tree_depth);
                for _ in 0..tree_depth {
                    let mut node = [0u8; 16];
                    node.copy_from_slice(&bytes[cur..cur + 16]);
                    cur += 16;
                    copath.push(node);
                }
                bin_receiver_trees.push(GgmReceiverBinaryTreeSeed {
                    punctured_idx,
                    copath,
                    punctured_mac_corr: [c0, c1],
                });
            }

            let mut tower_sender_trees = Vec::with_capacity(2 * PCG_TREES_PER_BUNDLE);
            for _ in 0..(2 * PCG_TREES_PER_BUNDLE) {
                if cur + 16 > bytes.len() {
                    return Err(PreprocessError::PcgInvalidWireSeed);
                }
                let mut root_seed = [0u8; 16];
                root_seed.copy_from_slice(&bytes[cur..cur + 16]);
                cur += 16;
                tower_sender_trees.push(GgmSenderTreeSeed { root_seed });
            }

            let mut tower_receiver_trees = Vec::with_capacity(2 * PCG_TREES_PER_BUNDLE);
            for _ in 0..(2 * PCG_TREES_PER_BUNDLE) {
                let need = 2 + 16 + 32 + 16 * tower_depth;
                if cur + need > bytes.len() {
                    return Err(PreprocessError::PcgInvalidWireSeed);
                }
                let punctured_idx = u16::from_le_bytes([bytes[cur], bytes[cur + 1]]);
                cur += 2;
                let punctured_beta =
                    Tower128(u128::from_le_bytes(core::array::from_fn(|array_index| {
                        (bytes[cur..cur + 16])[array_index]
                    })));
                cur += 16;
                let m0 = Tower128(u128::from_le_bytes(core::array::from_fn(|array_index| {
                    (bytes[cur..cur + 16])[array_index]
                })));
                cur += 16;
                let m1 = Tower128(u128::from_le_bytes(core::array::from_fn(|array_index| {
                    (bytes[cur..cur + 16])[array_index]
                })));
                cur += 16;
                let mut copath = Vec::with_capacity(tower_depth);
                for _ in 0..tower_depth {
                    let mut node = [0u8; 16];
                    node.copy_from_slice(&bytes[cur..cur + 16]);
                    cur += 16;
                    copath.push(node);
                }
                tower_receiver_trees.push(GgmReceiverTowerTreeSeed {
                    punctured_idx,
                    punctured_beta,
                    copath,
                    punctured_mac_val: [m0, m1],
                });
            }

            peers.push(PcgPeerSeedMaterial {
                peer_id,
                bin_sender_trees,
                bin_receiver_trees,
                tower_sender_trees,
                tower_receiver_trees,
            });
        }

        if cur + 4 > bytes.len() {
            return Err(PreprocessError::PcgInvalidWireSeed);
        }
        let d_len = u32::from_le_bytes(core::array::from_fn(|array_index| {
            (bytes[cur..cur + 4])[array_index]
        })) as usize;
        cur += 4;
        if d_len != PCG_NUM_WORDS || cur + d_len * 8 > bytes.len() {
            return Err(PreprocessError::PcgInvalidWireSeed);
        }
        let mut delta_words = Vec::with_capacity(d_len);
        for _ in 0..d_len {
            delta_words.push(u64::from_le_bytes(core::array::from_fn(|array_index| {
                (bytes[cur..cur + 8])[array_index]
            })));
            cur += 8;
        }
        let csum0 = read_auth_tower128_share(bytes, &mut cur)?;
        let csum1 = read_auth_tower128_share(bytes, &mut cur)?;
        if cur + 2 > bytes.len() {
            return Err(PreprocessError::PcgInvalidWireSeed);
        }
        let num_tow = u16::from_le_bytes([bytes[cur], bytes[cur + 1]]) as usize;
        cur += 2;
        validate_frame_count(num_tow, 3 * 18, bytes.len() - cur)?;
        let mut tower_triples = Vec::with_capacity(num_tow);
        for _ in 0..num_tow {
            let a = read_auth_tower128_share(bytes, &mut cur)?;
            let b = read_auth_tower128_share(bytes, &mut cur)?;
            let c = read_auth_tower128_share(bytes, &mut cur)?;
            tower_triples.push(PcgAuthTower128TripleShare { a, b, c });
        }
        if cur != bytes.len() {
            return Err(PreprocessError::PcgInvalidWireSeed);
        }
        Ok(Self {
            session_id,
            party_id,
            num_parties,
            tree_depth,
            mac_alpha: [alpha0, alpha1],
            diag_mask_seed,
            peers,
            delta_words,
            tilde_c_sums: [csum0, csum1],
            tower_triples,
        })
    }

    /// Expand this `< 24 KB` seed **locally with ZERO network I/O** (consuming the seed) into
    /// `65,600` (`> 65,536`) 2-lane `Tower128` BDOZ-authenticated Boolean Beaver triples +
    /// `8` authenticated 128-bit `Tower128` Beaver triples + sacrifice companion masks.
    pub fn expand_local(mut self) -> PcgExpandedPartyVault {
        let n = self.num_parties;
        let me = self.party_id;
        let tower_depth = PCG_MIN_TREE_DEPTH;

        let sched_x =
            QcLpnParitySchedule::derive(&self.session_id, b"BIN_X", self.tree_depth, PCG_NUM_WORDS);
        let sched_y =
            QcLpnParitySchedule::derive(&self.session_id, b"BIN_Y", self.tree_depth, PCG_NUM_WORDS);
        let sched_z =
            QcLpnParitySchedule::derive(&self.session_id, b"BIN_Z", self.tree_depth, PCG_NUM_WORDS);
        let sched_a0 =
            QcLpnParitySchedule::derive(&self.session_id, b"TOW_A0", tower_depth, PCG_NUM_WORDS);
        let sched_a1 =
            QcLpnParitySchedule::derive(&self.session_id, b"TOW_A1", tower_depth, PCG_NUM_WORDS);

        let mut bool_triple_words: Vec<PcgAuthBoolTripleWord64> = (0..PCG_NUM_WORDS)
            .map(|_| PcgAuthBoolTripleWord64 {
                a_word: 0,
                b_word: 0,
                c_word: 0,
                a_macs: vec![[[Tower128::ZERO; 2]; 64]; n],
                a_keys: vec![[[Tower128::ZERO; 2]; 64]; n],
                b_macs: vec![[[Tower128::ZERO; 2]; 64]; n],
                b_keys: vec![[[Tower128::ZERO; 2]; 64]; n],
                c_macs: vec![[[Tower128::ZERO; 2]; 64]; n],
                c_keys: vec![[[Tower128::ZERO; 2]; 64]; n],
            })
            .collect();

        let num_triples = PCG_NUM_BOOL_TRIPLES;
        let mut companion_a: [Vec<PcgAuthTower128Share>; 2] = [
            (0..num_triples)
                .map(|_| PcgAuthTower128Share::zero(n))
                .collect(),
            (0..num_triples)
                .map(|_| PcgAuthTower128Share::zero(n))
                .collect(),
        ];

        let mut my_bits_populated = false;
        for peer in &self.peers {
            let q = peer.peer_id as usize;

            // 1. Expand `me` as Sender (`keys[q]` authenticating peer `q`'s sparse vector under `me`'s `mac_alpha`)
            let mut s_leaves = Vec::with_capacity(3 * PCG_TREES_PER_BUNDLE);
            for (t_idx, tree) in peer.bin_sender_trees.iter().enumerate() {
                let tree_tag = ((me * 16 + q) as u8)
                    .wrapping_mul(31)
                    .wrapping_add(t_idx as u8);
                let (lt, _) = ggm_eval_sender_full(
                    &self.session_id,
                    tree_tag,
                    self.tree_depth,
                    &tree.root_seed,
                );
                s_leaves.push(lt);
            }
            let (_, kx) = sched_x.compress_binary_bundle(PCG_NUM_WORDS, &s_leaves[0..4], None);
            let (_, ky) = sched_y.compress_binary_bundle(PCG_NUM_WORDS, &s_leaves[4..8], None);
            let (_, kz) = sched_z.compress_binary_bundle(PCG_NUM_WORDS, &s_leaves[8..12], None);
            for k in 0..PCG_NUM_WORDS {
                for bit in 0..64 {
                    for lane in 0..2 {
                        bool_triple_words[k].a_keys[q][bit][lane] = Tower128(kx[k][bit][lane]);
                        bool_triple_words[k].b_keys[q][bit][lane] = Tower128(ky[k][bit][lane]);
                        bool_triple_words[k].c_keys[q][bit][lane] = Tower128(kz[k][bit][lane]);
                    }
                }
            }

            // 2. Expand `me` as Receiver (`macs[q]` authenticating `me`'s sparse vector under peer `q`'s `mac_alpha`)
            let mut r_leaves = Vec::with_capacity(3 * PCG_TREES_PER_BUNDLE);
            let mut p_indices = [0usize; 12];
            for (t_idx, p_indices_t_idx_item) in p_indices[..(3 * PCG_TREES_PER_BUNDLE)]
                .iter_mut()
                .enumerate()
            {
                let rt = &peer.bin_receiver_trees[t_idx];
                let p_star = rt.punctured_idx as usize;
                *p_indices_t_idx_item = p_star;
                let tree_tag = ((q * 16 + me) as u8)
                    .wrapping_mul(31)
                    .wrapping_add(t_idx as u8);
                let lt = ggm_eval_receiver_punctured(
                    &self.session_id,
                    tree_tag,
                    self.tree_depth,
                    p_star,
                    &rt.copath,
                    (
                        [rt.punctured_mac_corr[0].0, rt.punctured_mac_corr[1].0],
                        true,
                    ),
                );
                r_leaves.push(lt);
            }
            let px: [usize; 4] = core::array::from_fn(|array_index| (p_indices[0..4])[array_index]);
            let py: [usize; 4] = core::array::from_fn(|array_index| (p_indices[4..8])[array_index]);
            let pz: [usize; 4] =
                core::array::from_fn(|array_index| (p_indices[8..12])[array_index]);
            let (wx, mx) = sched_x.compress_binary_bundle(PCG_NUM_WORDS, &r_leaves[0..4], Some(px));
            let (wy, my) = sched_y.compress_binary_bundle(PCG_NUM_WORDS, &r_leaves[4..8], Some(py));
            let (wz, mz) =
                sched_z.compress_binary_bundle(PCG_NUM_WORDS, &r_leaves[8..12], Some(pz));

            for k in 0..PCG_NUM_WORDS {
                if !my_bits_populated {
                    bool_triple_words[k].a_word = wx[k];
                    bool_triple_words[k].b_word = wy[k];
                    bool_triple_words[k].c_word = wz[k];
                }
                for bit in 0..64 {
                    for lane in 0..2 {
                        bool_triple_words[k].a_macs[q][bit][lane] = Tower128(mx[k][bit][lane]);
                        bool_triple_words[k].b_macs[q][bit][lane] = Tower128(my[k][bit][lane]);
                        bool_triple_words[k].c_macs[q][bit][lane] = Tower128(mz[k][bit][lane]);
                    }
                }
            }

            // 3. Expand Tower128 companion bundles (`A0`, `A1`) as Sender & Receiver
            let mut ts_leaves = Vec::with_capacity(2 * PCG_TREES_PER_BUNDLE);
            for (t_idx, tree) in peer.tower_sender_trees.iter().enumerate() {
                let tree_tag = 0x80u8
                    .wrapping_add(((me * 16 + q) as u8).wrapping_mul(17))
                    .wrapping_add(t_idx as u8);
                let (lt, _) =
                    ggm_eval_sender_full(&self.session_id, tree_tag, tower_depth, &tree.root_seed);
                ts_leaves.push(lt);
            }
            let (_, tk0) = sched_a0.compress_tower_bundle(PCG_NUM_WORDS, &ts_leaves[0..4], None);
            let (_, tk1) = sched_a1.compress_tower_bundle(PCG_NUM_WORDS, &ts_leaves[4..8], None);

            let mut tr_leaves = Vec::with_capacity(2 * PCG_TREES_PER_BUNDLE);
            let mut tp_info = [(0usize, Tower128::ZERO); 8];
            for (t_idx, tp_info_t_idx_item) in
                tp_info[..(2 * PCG_TREES_PER_BUNDLE)].iter_mut().enumerate()
            {
                let rt = &peer.tower_receiver_trees[t_idx];
                let p_star = rt.punctured_idx as usize;
                *tp_info_t_idx_item = (p_star, rt.punctured_beta);
                let tree_tag = 0x80u8
                    .wrapping_add(((q * 16 + me) as u8).wrapping_mul(17))
                    .wrapping_add(t_idx as u8);
                let lt = ggm_eval_receiver_punctured(
                    &self.session_id,
                    tree_tag,
                    tower_depth,
                    p_star,
                    &rt.copath,
                    (
                        [rt.punctured_mac_val[0].0, rt.punctured_mac_val[1].0],
                        false,
                    ),
                );
                tr_leaves.push(lt);
            }
            let pa0: [(usize, Tower128); 4] =
                core::array::from_fn(|array_index| (tp_info[0..4])[array_index]);
            let pa1: [(usize, Tower128); 4] =
                core::array::from_fn(|array_index| (tp_info[4..8])[array_index]);
            let (tv0, tm0) =
                sched_a0.compress_tower_bundle(PCG_NUM_WORDS, &tr_leaves[0..4], Some(pa0));
            let (tv1, tm1) =
                sched_a1.compress_tower_bundle(PCG_NUM_WORDS, &tr_leaves[4..8], Some(pa1));

            for ell in 0..num_triples {
                if !my_bits_populated {
                    companion_a[0][ell].value = tv0[ell];
                    companion_a[1][ell].value = tv1[ell];
                }
                for lane in 0..2 {
                    companion_a[0][ell].keys[q][lane] = Tower128(tk0[ell][lane]);
                    companion_a[1][ell].keys[q][lane] = Tower128(tk1[ell][lane]);
                    companion_a[0][ell].macs[q][lane] = Tower128(tm0[ell][lane]);
                    companion_a[1][ell].macs[q][lane] = Tower128(tm1[ell][lane]);
                }
            }

            my_bits_populated = true;
        }

        // 4. Populate diagonal self-MACs (`q == me`) from `diag_mask_seed` AND apply public `delta_words`
        // affine shift (`[c_\ell] = [z_\ell] \oplus \delta_\ell`) preserving 2-lane `Tower128` BDOZ MACs!
        let mut diag_rng = PartyPrivateRng::from_seed(self.diag_mask_seed, b"PCG_DIAG");
        for (k, bool_triple_words_k_item) in
            bool_triple_words[..PCG_NUM_WORDS].iter_mut().enumerate()
        {
            let dw = self.delta_words[k];
            if me == 0 {
                bool_triple_words_k_item.c_word ^= dw;
            }
            let aw = bool_triple_words_k_item.a_word;
            let bw = bool_triple_words_k_item.b_word;
            let cw = bool_triple_words_k_item.c_word;

            for bit in 0..64 {
                let a_bit = ((aw >> bit) & 1) == 1;
                let b_bit = ((bw >> bit) & 1) == 1;
                let c_bit = ((cw >> bit) & 1) == 1;
                let d_bit = ((dw >> bit) & 1) == 1;

                for lane in 0..2 {
                    let alpha_l = self.mac_alpha[lane];
                    let ka = diag_rng.next_tower128();
                    let kb = diag_rng.next_tower128();
                    let kc = diag_rng.next_tower128();
                    bool_triple_words_k_item.a_keys[me][bit][lane] = ka;
                    bool_triple_words_k_item.a_macs[me][bit][lane] =
                        if a_bit { ka.add(alpha_l) } else { ka };
                    bool_triple_words_k_item.b_keys[me][bit][lane] = kb;
                    bool_triple_words_k_item.b_macs[me][bit][lane] =
                        if b_bit { kb.add(alpha_l) } else { kb };
                    bool_triple_words_k_item.c_keys[me][bit][lane] = kc;
                    bool_triple_words_k_item.c_macs[me][bit][lane] =
                        if c_bit { kc.add(alpha_l) } else { kc };

                    if me != 0 && d_bit {
                        bool_triple_words_k_item.c_keys[0][bit][lane] =
                            bool_triple_words_k_item.c_keys[0][bit][lane].add(alpha_l);
                    }
                }
            }
        }

        #[expect(
            clippy::needless_range_loop,
            reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows"
        )]
        for sac_lane in 0..2 {
            #[expect(
                clippy::needless_range_loop,
                reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows"
            )]
            for ell in 0..num_triples {
                let v = companion_a[sac_lane][ell].value;
                for lane in 0..2 {
                    let kd = diag_rng.next_tower128();
                    companion_a[sac_lane][ell].keys[me][lane] = kd;
                    companion_a[sac_lane][ell].macs[me][lane] = kd.add(self.mac_alpha[lane].mul(v));
                }
            }
        }

        PcgExpandedPartyVault {
            session_id: self.session_id,
            party_id: me,
            num_parties: n,
            mac_alpha: self.mac_alpha,
            bool_triple_words,
            tower_triples: core::mem::take(&mut self.tower_triples),
            companion_a,
            companion_c_sums: core::mem::replace(
                &mut self.tilde_c_sums,
                core::array::from_fn(|_| PcgAuthTower128Share::zero(0)),
            ),
        }
    }
}
