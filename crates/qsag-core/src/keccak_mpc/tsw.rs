use super::*;

// ============================================================================
// 3. Distributed `Corduroy` / `Baggy` (`Cshake256Suite`) & `DkgCachedSubtrees`
// ============================================================================

/// Public XMSS subtree leaf cache constructed strictly via distributed cut-boundary MPC
/// (`0` `PqSecretKey`, bounded `max_cached_leaves` to prevent exponential memory DoS).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DkgCachedSubtrees {
    pub top_layer: u32,
    pub top_leaves: Vec<[u8; 32]>,
    pub pk: PqPublicKey,
}

impl DkgCachedSubtrees {
    /// Build the top-layer XMSS subtree leaf cache and [`PqPublicKey`] via distributed 2-of-3 RSS
    /// `cSHAKE256` cut-boundary evaluation (`0` `sk: &PqSecretKey` in cleartext!).
    ///
    /// This is key generation for the stateless hash signature: the root computed here from
    /// the shares, together with `params`, is recorded in the three key shares, and
    /// [`sign_stateless_tsw_rss_mpc`] signs only for that root and parameter set. Shares
    /// that are already bound are evaluated again only under the same parameter set (a
    /// different chain length would open interior chain values of the bound key), and the
    /// recomputed root must equal the bound one.
    pub fn build_distributed_rss(
        params: &PqHashParams,
        cluster: &mut RssSlhMpcCluster,
        max_cached_leaves: usize,
    ) -> Result<Self, KeccakMpcError> {
        if !params.is_well_formed() || cluster.keys[0].key_len != 32 {
            return Err(KeccakMpcError::InvalidParameters);
        }
        let n_leaves = 1usize << params.subtree_height;
        if n_leaves > max_cached_leaves {
            return Err(KeccakMpcError::SubtreeCacheCapExceeded {
                requested: n_leaves,
                max_allowed: max_cached_leaves,
            });
        }
        cluster.ensure_live()?;
        let params_digest = tsw_params_digest(params);
        let prior = cluster.tsw_binding()?;
        if prior.is_some_and(|b| !ct_eq_bytes32(&b.params_digest, &params_digest)) {
            return Err(KeccakMpcError::KeyBindingMismatch);
        }
        let top_layer = (params.num_layers - 1) as u32;
        let pk_seed = cluster.keys[0].pk_seed;
        let endpoints = eval_tsw_wots_subtree_rss(params, cluster, &pk_seed, top_layer, 0, None)?;

        let mut top_leaves = Vec::with_capacity(n_leaves);
        for kp in 0..n_leaves {
            let wotspk_adrs = HashAdrs {
                layer: top_layer,
                tree: 0,
                kind: AdrsKind::WotsPk,
                key_pair: kp as u32,
                chain_idx: 0,
                hash_step: 0,
            };
            let ep = &endpoints[kp * params.ell1..(kp + 1) * params.ell1];
            top_leaves.push(th_tweak_tl(Cshake256Suite, &pk_seed, &wotspk_adrs, ep));
        }
        let pk_root = build_tsw_merkle_root(
            Cshake256Suite,
            &pk_seed,
            top_layer,
            0,
            AdrsKind::Tree,
            0,
            params.subtree_height,
            0,
            &top_leaves,
            0,
        )
        .0;
        match prior {
            Some(bound) => {
                if !ct_eq_bytes32(&bound.pk_root, &pk_root) {
                    return Err(KeccakMpcError::KeyBindingMismatch);
                }
            }
            None => {
                for key in &mut cluster.keys {
                    key.tsw_binding = Some(TswKeyBinding {
                        params_digest,
                        pk_root,
                    });
                }
            }
        }
        Ok(Self {
            top_layer,
            top_leaves,
            pk: PqPublicKey { pk_seed, pk_root },
        })
    }
}

#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the existing explicit protocol interface for callers"
)]
fn build_tsw_merkle_root<S: TweakableHashSuite>(
    suite: S,
    pk_seed: &[u8; 32],
    layer: u32,
    tree: u64,
    kind: AdrsKind,
    key_pair: u32,
    height: usize,
    tree_idx_offset: usize,
    leaves: &[[u8; 32]],
    target_idx: usize,
) -> ([u8; 32], Vec<[u8; 32]>) {
    // Same node hash, node addressing and root-first path order as the verifier's
    // `walk_merkle_auth_path`: the public tree must never be rebuilt by a second convention.
    build_merkle_from_leaves_topdown(
        suite,
        pk_seed,
        layer,
        tree,
        kind,
        key_pair,
        leaves,
        height,
        tree_idx_offset >> height,
        target_idx,
    )
}

/// Sponge state after the `Cshake256Suite` customization block, shared by every tweakable-hash
/// role (the role tag travels inside the preimage frame).
pub(crate) const TSW_SUITE_MIDSTATE: [u64; 25] =
    crate::sponge::keccak::cshake256_static_midstate(PQ_CSHAKE_SUITE_CUSTOM);

/// Byte offset of the 32-byte secret argument inside `th_preimage(tag, pk_seed, adrs, [secret])`:
/// field count, three length-prefixed public fields, and the secret's own length prefix.
pub(crate) const fn tsw_secret32_offset(tag_len: usize) -> usize {
    1 + (1 + tag_len) + (1 + 32) + (1 + 32) + 1
}
pub(crate) const TSW_PRF_SECRET_OFFSET: usize = tsw_secret32_offset(TAG_PRF.len());
pub(crate) const TSW_F_SECRET_OFFSET: usize = tsw_secret32_offset(TAG_TH_F.len());

/// Public bytes of the single rate block that the reference suite absorbs for
/// `th_call_secret(role_tag, pk_seed, adrs, [secret32])`: the exact reference preimage with a
/// zeroed secret slot, followed by `cSHAKE256` padding. The shared secret is XORed into the
/// slot at [`tsw_secret32_offset`].
pub(crate) fn tsw_secret32_frame(
    role_tag: &[u8],
    pk_seed: &[u8; 32],
    adrs: &HashAdrs,
) -> [u8; SHAKE256_RATE_BYTES] {
    let (template, offset) = build_single_secret32_template(role_tag, pk_seed, adrs);
    assert_eq!(offset, tsw_secret32_offset(role_tag.len()));
    assert!(template.len() < SHAKE256_RATE_BYTES);
    let mut frame = [0u8; SHAKE256_RATE_BYTES];
    frame[..template.len()].copy_from_slice(&template);
    frame[template.len()] = 0x04;
    frame[SHAKE256_RATE_BYTES - 1] ^= 0x80;
    frame
}

/// Evaluate the reference suite's `th_secret_prf` (`TAG_PRF`) and subsequent `th_chain_f`
/// (`TAG_TH_F`) chain steps in 64-way 2-of-3 RSS (`active_sign = Some((active_kp, &digits))` for signing, `None` for pkgen).
fn eval_tsw_wots_subtree_rss(
    params: &PqHashParams,
    cluster: &mut RssSlhMpcCluster,
    pk_seed: &[u8; 32],
    layer: u32,
    tree: u64,
    active_sign: Option<(usize, &[usize])>,
) -> Result<Vec<[u8; 32]>, KeccakMpcError> {
    let n_leaves = 1usize << params.subtree_height;
    let ell1 = params.ell1;
    let total_chains = n_leaves * ell1;
    let max_steps = params.w - 1;

    // Both roles share the suite customization block; the role tag is the first frame field.
    let prf_midstate = TSW_SUITE_MIDSTATE;
    let tweak_midstate = TSW_SUITE_MIDSTATE;

    let mut cut = RssCutBuffer::new();
    let mut chunk_sizes = Vec::new();

    let mut cursor = 0usize;
    while cursor < total_chains {
        let chunk_len = (total_chains - cursor).min(64);
        let active_mask = batch_active_mask(chunk_len);

        // Block 0 absorbs `cshake_customization_prefix(136 B)` (identical public block across all 64 lanes,
        // precomputed in `prf_midstate`!)
        // Block 1 absorbs `encode_multi_frame(&[pk_seed(32B), adrs(32B), sk_seed(32B)])`:
        // frame = `[3, 32, pk_seed(32), 32, adrs(32), 32, sk_seed(32)]` = `1 + 1 + 32 + 1 + 32 + 1 + 32 = 100 bytes < 136`!
        let mut st_p = SecretBuffer([[0u64; 1600]; 3]);
        let mut st_s = SecretBuffer([[0u64; 1600]; 3]);
        init_rss_state_from_public_midstate(&prf_midstate, active_mask, &mut st_p, &mut st_s);

        let mut targets = [0usize; 64];
        let mut b = 0;
        while b < chunk_len {
            let flat = cursor + b;
            let kp = flat / ell1;
            let ch = flat % ell1;
            targets[b] = match active_sign {
                Some((act_kp, digs)) if kp == act_kp => digs[ch],
                _ => max_steps,
            };
            let adrs = HashAdrs {
                layer,
                tree,
                kind: AdrsKind::WotsPrf,
                key_pair: kp as u32,
                chain_idx: ch as u32,
                hash_step: 0,
            };
            let pub_frame = tsw_secret32_frame(TAG_PRF, pk_seed, &adrs);

            let bit_b = 1u64 << b;
            for byte_idx in 0..SHAKE256_RATE_BYTES {
                let v = pub_frame[byte_idx];
                for bit in 0..8 {
                    if ((v >> bit) & 1) == 1 {
                        st_p[0][8 * byte_idx + bit] ^= bit_b;
                        st_s[2][8 * byte_idx + bit] ^= bit_b;
                    }
                }
            }
            b += 1;
        }
        for p in 0..3 {
            let (sk_p, sk_s) = cluster.keys[p].sk_seed_shares();
            for byte_idx in 0..32 {
                for bit in 0..8 {
                    let mp = 0u64.wrapping_sub(((sk_p[byte_idx] >> bit) & 1) as u64) & active_mask;
                    let ms = 0u64.wrapping_sub(((sk_s[byte_idx] >> bit) & 1) as u64) & active_mask;
                    st_p[p][8 * (TSW_PRF_SECRET_OFFSET + byte_idx) + bit] ^= mp;
                    st_s[p][8 * (TSW_PRF_SECRET_OFFSET + byte_idx) + bit] ^= ms;
                }
            }
        }
        cluster.permute_batch64_deferred(chunk_len, &mut st_p, &mut st_s)?;

        let mut cur_p = SecretBuffer([[0u64; 256]; 3]);
        let mut cur_s = SecretBuffer([[0u64; 256]; 3]);
        for p in 0..3 {
            cur_p[p].copy_from_slice(&st_p[p][..256]);
            cur_s[p].copy_from_slice(&st_s[p][..256]);
            wipe_u64s(&mut st_p[p]);
            wipe_u64s(&mut st_s[p]);
        }

        // Advance `step = 0..max_steps` via `cSHAKE256("QSAG.TH.TWEAK/v1", [3, 32, pk_seed, 32, adrs, 32, cur])`
        for step in 0..max_steps {
            let mut exec_mask = 0u64;
            let mut b = 0;
            while b < chunk_len {
                if step < targets[b] {
                    exec_mask |= 1u64 << b;
                }
                b += 1;
            }
            if exec_mask == 0 {
                continue;
            }
            let mut sp = SecretBuffer([[0u64; 1600]; 3]);
            let mut ss = SecretBuffer([[0u64; 1600]; 3]);
            init_rss_state_from_public_midstate(&tweak_midstate, active_mask, &mut sp, &mut ss);

            for b in 0..chunk_len {
                let flat = cursor + b;
                let kp = flat / ell1;
                let ch = flat % ell1;
                let adrs = HashAdrs {
                    layer,
                    tree,
                    kind: AdrsKind::WotsHash,
                    key_pair: kp as u32,
                    chain_idx: ch as u32,
                    hash_step: step as u32,
                };
                let pub_frame = tsw_secret32_frame(TAG_TH_F, pk_seed, &adrs);

                let bit_b = 1u64 << b;
                for byte_idx in 0..SHAKE256_RATE_BYTES {
                    let v = pub_frame[byte_idx];
                    for bit in 0..8 {
                        if ((v >> bit) & 1) == 1 {
                            sp[0][8 * byte_idx + bit] ^= bit_b;
                            ss[2][8 * byte_idx + bit] ^= bit_b;
                        }
                    }
                }
            }
            for p in 0..3 {
                for bit_idx in 0..256 {
                    sp[p][8 * TSW_F_SECRET_OFFSET + bit_idx] ^= cur_p[p][bit_idx];
                    ss[p][8 * TSW_F_SECRET_OFFSET + bit_idx] ^= cur_s[p][bit_idx];
                }
            }
            if let Err(e) = cluster.permute_batch64_deferred(chunk_len, &mut sp, &mut ss) {
                wipe_rss_states(&mut cur_p, &mut cur_s);
                return Err(e);
            }

            let keep = !exec_mask;
            for p in 0..3 {
                for bit_idx in 0..256 {
                    cur_p[p][bit_idx] = (cur_p[p][bit_idx] & keep) | (sp[p][bit_idx] & exec_mask);
                    cur_s[p][bit_idx] = (cur_s[p][bit_idx] & keep) | (ss[p][bit_idx] & exec_mask);
                }
                wipe_u64s(&mut sp[p]);
                wipe_u64s(&mut ss[p]);
            }
        }

        for p in 0..3 {
            cut.push_party_slices(p, &cur_p[p], &cur_s[p]);
            wipe_u64s(&mut cur_p[p]);
            wipe_u64s(&mut cur_s[p]);
        }
        chunk_sizes.push(chunk_len);
        cursor += chunk_len;
    }

    let (opened_words, _tok) = cluster.flush_verify_and_open_cut("rss_tsw_wots_subtree", &cut)?;

    let mut out = Vec::with_capacity(total_chains);
    let mut off = 0usize;
    for &c_len in &chunk_sizes {
        let slice = &opened_words[off..off + 256];
        for b in 0..c_len {
            let mut node = [0u8; 32];
            for byte_idx in 0..32 {
                let mut v = 0u8;
                for bit in 0..8 {
                    v |= (((slice[8 * byte_idx + bit] >> b) & 1) as u8) << bit;
                }
                node[byte_idx] = v;
            }
            out.push(node);
        }
        off += 256;
    }
    Ok(out)
}

/// Public `opt_rand` input of the randomizer PRF: fixed by the public key, as in FIPS 205
/// deterministic signing where `opt_rand = PK.seed`.
pub(super) fn tsw_rss_opt_rand(pk: &PqPublicKey) -> [u8; 32] {
    cshake256_32(
        b"QSAG.TSW.RSS.OPT_RAND/v1",
        &encode_multi_frame(&[&pk.pk_seed, &pk.pk_root]),
    )
}

/// Sign a message under stateless `Corduroy` / `Baggy` (`Cshake256Suite`) via distributed
/// 2-of-3 RSS cut-boundary MPC (`0` `PqSecretKey` reconstruction!), verifying the assembled
/// signature with [`verify_pq_hash_sig`] before returning!
///
/// The key shares must have been bound by [`DkgCachedSubtrees::build_distributed_rss`];
/// `params` and `pk` are checked against that binding before anything is evaluated, so the
/// FORS indices and WOTS digits are never derived from a root or parameter set the shares
/// were not generated for.
///
/// The randomizer is `R = PRF_msg(SK.prf, opt_rand, mu)` with `opt_rand` fixed by the public
/// key and `mu` the message digest, evaluated on the shared `SK.prf`. It is a function of
/// the key and the message only: a retry in another session, with other party randomness,
/// opens the same `R` and therefore the same FORS instance and indices. An aborting signer
/// gains no second choice of `R` for a message.
pub fn sign_stateless_tsw_rss_mpc(
    params: &PqHashParams,
    cluster: &mut RssSlhMpcCluster,
    pk: &PqPublicKey,
    msg: &[u8],
    max_grind: u32,
) -> Result<PqHashSig, KeccakMpcError> {
    if !params.is_well_formed()
        || params.stateful
        || cluster.keys[0].key_len != 32
        || !ct_eq_bytes(&pk.pk_seed, &cluster.keys[0].pk_seed)
    {
        return Err(KeccakMpcError::InvalidParameters);
    }
    cluster.ensure_live()?;
    let binding = cluster
        .tsw_binding()?
        .ok_or(KeccakMpcError::KeyBindingMismatch)?;
    if !ct_eq_bytes32(&binding.params_digest, &tsw_params_digest(params))
        || !ct_eq_bytes32(&binding.pk_root, &pk.pk_root)
    {
        return Err(KeccakMpcError::KeyBindingMismatch);
    }

    let mu = th_pre_hash(Cshake256Suite, &pk.pk_seed, &pk.pk_root, msg);
    let transcript = encode_multi_frame(&[&cluster.session_id, &mu]);
    for rng in &mut cluster.party_rngs {
        rng.hedge_transcript(&transcript);
    }
    cluster.mask_session.hedge_transcript(&transcript);
    let opt_rand = tsw_rss_opt_rand(pk);
    let (r_blk, _tok_r) = cluster.prf_msg_shared(32, &opt_rand, &mu)?;
    let mut r_rand = [0u8; 32];
    r_rand.copy_from_slice(r_blk.as_slice());

    let (leaf_global_idx, idxs) = derive_stateless_leaf_and_fors_indices(
        Cshake256Suite,
        params,
        &r_rand,
        &pk.pk_seed,
        &pk.pk_root,
        &mu,
    )
    .ok_or(KeccakMpcError::InvalidParameters)?;

    let sub_leaves = 1usize << params.subtree_height;
    let kp0 = (leaf_global_idx % sub_leaves) as u32;
    let tree0 = (leaf_global_idx / sub_leaves) as u64;

    // Evaluate FORS trees in 64-way RSS (`cSHAKE256("QSAG.TH.PRF/v1", ...)` -> `cSHAKE256("QSAG.TH.TWEAK/v1", ...)`)
    let t_leaves = 1usize << params.fors_height;
    let total_fors = params.fors_trees * t_leaves;
    // Both roles share the suite customization block; the role tag is the first frame field.
    let prf_midstate = TSW_SUITE_MIDSTATE;
    let tweak_midstate = TSW_SUITE_MIDSTATE;

    let mut cut = RssCutBuffer::new();
    let mut fors_chunks = Vec::new();

    // First batch: `params.fors_trees` (`<= 64`) revealed FORS `secret_val`s
    {
        let mut st_p = SecretBuffer([[0u64; 1600]; 3]);
        let mut st_s = SecretBuffer([[0u64; 1600]; 3]);
        let mask_k = batch_active_mask(params.fors_trees);
        init_rss_state_from_public_midstate(&prf_midstate, mask_k, &mut st_p, &mut st_s);
        let mut j = 0;
        while j < params.fors_trees {
            let adrs = HashAdrs {
                layer: 0,
                tree: tree0,
                kind: AdrsKind::ForsPrf,
                key_pair: kp0,
                chain_idx: j as u32,
                hash_step: idxs[j] as u32,
            };
            let pub_frame = tsw_secret32_frame(TAG_PRF, &pk.pk_seed, &adrs);
            let bit_b = 1u64 << j;
            for byte_idx in 0..SHAKE256_RATE_BYTES {
                let v = pub_frame[byte_idx];
                for bit in 0..8 {
                    if ((v >> bit) & 1) == 1 {
                        st_p[0][8 * byte_idx + bit] ^= bit_b;
                        st_s[2][8 * byte_idx + bit] ^= bit_b;
                    }
                }
            }
            j += 1;
        }
        for p in 0..3 {
            let (sk_p, sk_s) = cluster.keys[p].sk_seed_shares();
            for byte_idx in 0..32 {
                for bit in 0..8 {
                    let mp = 0u64.wrapping_sub(((sk_p[byte_idx] >> bit) & 1) as u64) & mask_k;
                    let ms = 0u64.wrapping_sub(((sk_s[byte_idx] >> bit) & 1) as u64) & mask_k;
                    st_p[p][8 * (TSW_PRF_SECRET_OFFSET + byte_idx) + bit] ^= mp;
                    st_s[p][8 * (TSW_PRF_SECRET_OFFSET + byte_idx) + bit] ^= ms;
                }
            }
        }
        cluster.permute_batch64_deferred(params.fors_trees, &mut st_p, &mut st_s)?;
        for p in 0..3 {
            cut.push_party_slices(p, &st_p[p][..256], &st_s[p][..256]);
            wipe_u64s(&mut st_p[p]);
            wipe_u64s(&mut st_s[p]);
        }
    }

    // All `total_fors` leaf hashes `T_l(pk_seed, ForsTree_adrs, [secret_val])` (`PRF -> TWEAK` inside MPC!)
    let mut f_cur = 0usize;
    while f_cur < total_fors {
        let c_len = (total_fors - f_cur).min(64);
        let mask_c = batch_active_mask(c_len);
        let mut st_p = SecretBuffer([[0u64; 1600]; 3]);
        let mut st_s = SecretBuffer([[0u64; 1600]; 3]);
        init_rss_state_from_public_midstate(&prf_midstate, mask_c, &mut st_p, &mut st_s);
        for b in 0..c_len {
            let flat = f_cur + b;
            let tree_j = flat / t_leaves;
            let leaf_i = flat % t_leaves;
            let adrs = HashAdrs {
                layer: 0,
                tree: tree0,
                kind: AdrsKind::ForsPrf,
                key_pair: kp0,
                chain_idx: tree_j as u32,
                hash_step: leaf_i as u32,
            };
            let pub_frame = tsw_secret32_frame(TAG_PRF, &pk.pk_seed, &adrs);
            let bit_b = 1u64 << b;
            for byte_idx in 0..SHAKE256_RATE_BYTES {
                let v = pub_frame[byte_idx];
                for bit in 0..8 {
                    if ((v >> bit) & 1) == 1 {
                        st_p[0][8 * byte_idx + bit] ^= bit_b;
                        st_s[2][8 * byte_idx + bit] ^= bit_b;
                    }
                }
            }
        }
        for p in 0..3 {
            let (sk_p, sk_s) = cluster.keys[p].sk_seed_shares();
            for byte_idx in 0..32 {
                for bit in 0..8 {
                    let mp = 0u64.wrapping_sub(((sk_p[byte_idx] >> bit) & 1) as u64) & mask_c;
                    let ms = 0u64.wrapping_sub(((sk_s[byte_idx] >> bit) & 1) as u64) & mask_c;
                    st_p[p][8 * (TSW_PRF_SECRET_OFFSET + byte_idx) + bit] ^= mp;
                    st_s[p][8 * (TSW_PRF_SECRET_OFFSET + byte_idx) + bit] ^= ms;
                }
            }
        }
        cluster.permute_batch64_deferred(c_len, &mut st_p, &mut st_s)?;

        // Hash `secret_val` -> `leaf_hash` via `cSHAKE256("QSAG.TH.TWEAK/v1", [3, 32, pk_seed, 32, leaf_adrs, 32, secret_val])`
        let mut sp = SecretBuffer([[0u64; 1600]; 3]);
        let mut ss = SecretBuffer([[0u64; 1600]; 3]);
        init_rss_state_from_public_midstate(&tweak_midstate, mask_c, &mut sp, &mut ss);
        for b in 0..c_len {
            let flat = f_cur + b;
            let tree_j = flat / t_leaves;
            let leaf_i = flat % t_leaves;
            let leaf_adrs = HashAdrs {
                layer: 0,
                tree: tree0,
                kind: AdrsKind::ForsTree,
                key_pair: kp0,
                chain_idx: tree_j as u32,
                hash_step: leaf_i as u32,
            };
            let pub_frame = tsw_secret32_frame(TAG_TH_F, &pk.pk_seed, &leaf_adrs);
            let bit_b = 1u64 << b;
            for byte_idx in 0..SHAKE256_RATE_BYTES {
                let v = pub_frame[byte_idx];
                for bit in 0..8 {
                    if ((v >> bit) & 1) == 1 {
                        sp[0][8 * byte_idx + bit] ^= bit_b;
                        ss[2][8 * byte_idx + bit] ^= bit_b;
                    }
                }
            }
        }
        for p in 0..3 {
            for bit_idx in 0..256 {
                sp[p][8 * TSW_F_SECRET_OFFSET + bit_idx] ^= st_p[p][bit_idx];
                ss[p][8 * TSW_F_SECRET_OFFSET + bit_idx] ^= st_s[p][bit_idx];
            }
            wipe_u64s(&mut st_p[p]);
            wipe_u64s(&mut st_s[p]);
        }
        cluster.permute_batch64_deferred(c_len, &mut sp, &mut ss)?;
        for p in 0..3 {
            cut.push_party_slices(p, &sp[p][..256], &ss[p][..256]);
            wipe_u64s(&mut sp[p]);
            wipe_u64s(&mut ss[p]);
        }
        fors_chunks.push(c_len);
        f_cur += c_len;
    }

    let (fors_opened, _tok_f) = cluster.flush_verify_and_open_cut("rss_tsw_fors_cut", &cut)?;

    let mut rev_secrets = Vec::with_capacity(params.fors_trees);
    for j in 0..params.fors_trees {
        let mut s_val = [0u8; 32];
        for byte_idx in 0..32 {
            let mut v = 0u8;
            for bit in 0..8 {
                v |= (((fors_opened[8 * byte_idx + bit] >> j) & 1) as u8) << bit;
            }
            s_val[byte_idx] = v;
        }
        rev_secrets.push(s_val);
    }

    let mut flat_fors_leaves = Vec::with_capacity(total_fors);
    let mut f_off = 256usize;
    for &c_len in &fors_chunks {
        let slice = &fors_opened[f_off..f_off + 256];
        for b in 0..c_len {
            let mut l_val = [0u8; 32];
            for byte_idx in 0..32 {
                let mut v = 0u8;
                for bit in 0..8 {
                    v |= (((slice[8 * byte_idx + bit] >> b) & 1) as u8) << bit;
                }
                l_val[byte_idx] = v;
            }
            flat_fors_leaves.push(l_val);
        }
        f_off += 256;
    }

    let mut fors_openings = Vec::with_capacity(params.fors_trees);
    let mut fors_roots = Vec::with_capacity(params.fors_trees);
    for j in 0..params.fors_trees {
        let tree_leaves = &flat_fors_leaves[j * t_leaves..(j + 1) * t_leaves];
        let (root_j, auth_path) = build_tsw_merkle_root(
            Cshake256Suite,
            &pk.pk_seed,
            0,
            tree0,
            AdrsKind::ForsTree,
            kp0,
            params.fors_height,
            j * t_leaves,
            tree_leaves,
            idxs[j],
        );
        // Verify Merkle path matches `walk_merkle_auth_path`
        let check_root = walk_merkle_auth_path(
            Cshake256Suite,
            &pk.pk_seed,
            0,
            tree0,
            AdrsKind::ForsTree,
            kp0,
            params.fors_height,
            j,
            idxs[j],
            tree_leaves[idxs[j]],
            &auth_path,
        )
        .ok_or(KeccakMpcError::PostVerifyFailed)?;
        if !ct_eq_bytes32(&root_j, &check_root) {
            return Err(KeccakMpcError::PostVerifyFailed);
        }
        fors_roots.push(root_j);
        fors_openings.push(ForsTreeOpening {
            secret_val: rev_secrets[j],
            auth_path,
        });
    }
    let mut cur_root =
        crate::tsw_baggy::fors_pk_from_roots(Cshake256Suite, &pk.pk_seed, tree0, kp0, &fors_roots);

    // Evaluate hypertree layers `0..num_layers` with public TSW target-sum grinding (`0` r_rand on internal nodes `[P0-02]`)
    let target_sum = canonical_target_sum(params.w, params.ell1);
    let mut cur_global = leaf_global_idx;
    let mut layer_sigs = Vec::with_capacity(params.num_layers);

    for layer_idx in 0..params.num_layers {
        let kp_idx = cur_global % sub_leaves;
        let tree_idx_nat = cur_global / sub_leaves;
        let tree_idx = tree_idx_nat as u64;
        let layer_u32 = layer_idx as u32;
        let kp_u32 = kp_idx as u32;

        let mut found: Option<(u32, Vec<usize>)> = None;
        for ctr in 0..max_grind {
            let hmsg = th_hash_internal_node(
                Cshake256Suite,
                &pk.pk_seed,
                &pk.pk_root,
                &cur_root,
                layer_u32,
                tree_idx,
                kp_u32,
                ctr,
            );
            if let Some(digs) = extract_base_w_digits_checked(params.w, params.ell1, &hmsg)
                && check_target_sum(params.w, params.ell1, target_sum, &digs)
            {
                found = Some((ctr, digs));
                break;
            }
        }
        let (tsw_ctr, digits) = found.ok_or(KeccakMpcError::GrindExhausted)?;

        let opened_nodes = eval_tsw_wots_subtree_rss(
            params,
            cluster,
            &pk.pk_seed,
            layer_u32,
            tree_idx,
            Some((kp_idx, &digits)),
        )?;
        let wots_chains = opened_nodes[kp_idx * params.ell1..(kp_idx + 1) * params.ell1].to_vec();

        let mut leaves = Vec::with_capacity(sub_leaves);
        for kp in 0..sub_leaves {
            let ep = if kp == kp_idx {
                let mut completed = Vec::with_capacity(params.ell1);
                for ch in 0..params.ell1 {
                    let mut x = wots_chains[ch];
                    for step in digits[ch]..(params.w - 1) {
                        let step_adrs = HashAdrs {
                            layer: layer_u32,
                            tree: tree_idx,
                            kind: AdrsKind::WotsHash,
                            key_pair: kp as u32,
                            chain_idx: ch as u32,
                            hash_step: step as u32,
                        };
                        x = th_chain_f(Cshake256Suite, &pk.pk_seed, &step_adrs, &x);
                    }
                    completed.push(x);
                }
                completed
            } else {
                opened_nodes[kp * params.ell1..(kp + 1) * params.ell1].to_vec()
            };
            let pk_adrs = HashAdrs {
                layer: layer_u32,
                tree: tree_idx,
                kind: AdrsKind::WotsPk,
                key_pair: kp as u32,
                chain_idx: 0,
                hash_step: 0,
            };
            leaves.push(th_tweak_tl(Cshake256Suite, &pk.pk_seed, &pk_adrs, &ep));
        }
        let (next_root, auth_path) = build_tsw_merkle_root(
            Cshake256Suite,
            &pk.pk_seed,
            layer_u32,
            tree_idx,
            AdrsKind::Tree,
            0,
            params.subtree_height,
            0,
            &leaves,
            kp_idx,
        );
        layer_sigs.push(LayerXmssSig {
            tsw_ctr,
            wots_chains,
            auth_path,
        });
        cur_root = next_root;
        cur_global = tree_idx_nat;
    }

    let sig = PqHashSig {
        r_rand,
        msg_tsw_ctr: 0,
        leaf_global_idx,
        fors_openings,
        layer_sigs,
    };
    if !verify_pq_hash_sig(Cshake256Suite, params, pk, msg, &sig) {
        return Err(KeccakMpcError::PostVerifyFailed);
    }
    Ok(sig)
}
