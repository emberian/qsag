use super::*;

/// Evaluate all WOTS+C chains for a batch of `(layer, tree, kp, chain_idx, steps)` targets in MPC:
/// - `steps == 0`: `th_secret_prf` directly produces the cut-boundary `st[0..4]` (`0` A2B needed!);
/// - `steps >= 1`: intermediate unrevealed steps convert `st[0..4]` -> `[bytes32]` via
///   [`eval_spdz_canonical_a2b_state4_batch_to_bytes32`], and ONLY the final step `steps - 1`
///   lands at the cut boundary!
#[expect(
    clippy::too_many_arguments,
    reason = "One MPC phase: transcript context, quorum, public seed, chain targets and per-party state"
)]
fn eval_wots_chains_mpc_cut(
    session_id: &[u8; 32],
    phase: &'static str,
    t: usize,
    quorum_pts: &[Goldilocks],
    pk_seed: &[u8; 32],
    targets: &[(u32, u64, u32, u32, usize)],
    key_shares: &mut [&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<[u8; 32]>, Poseidon2MpcError> {
    let m = quorum_pts.len();
    let count = targets.len();
    if count == 0 {
        return Ok(Vec::new());
    }
    let mut pending = SpdzGoldilocksPendingChecks::new(m);

    // Step 0: derive WOTS secret base `th_secret_prf(TAG_PRF, pk_seed, sk_seed, adrs)` for all targets
    let mut prf_tmpls = Vec::with_capacity(count);
    for &(layer, tree, kp, ch_idx, _) in targets {
        let adrs = HashAdrs {
            layer,
            tree,
            kind: AdrsKind::WotsPrf,
            key_pair: kp,
            chain_idx: ch_idx,
            hash_step: 0,
        };
        prf_tmpls.push(build_single_secret32_template(TAG_PRF, pk_seed, &adrs));
    }
    let mut prf_secrets = secret_vecs_with_capacity(m, count);
    for p in 0..m {
        let seed_w = SecretBuffer(key_seed_wires(key_shares[p]));
        for _ in 0..count {
            secret_vec_push(&mut prf_secrets[p], *seed_w);
        }
    }

    let mut cur_states = SecretBuffer(
        match eval_spdz_poseidon2_hash32_templates(
            t,
            quorum_pts,
            &prf_tmpls,
            &prf_secrets,
            vaults,
            &mut pending,
        ) {
            Ok(s) => s,
            Err(e) => {
                poison_all_on_abort(key_shares, vaults);
                return Err(Poseidon2MpcError::Preprocess(e));
            }
        },
    );

    let max_steps = targets.iter().map(|x| x.4).max().unwrap_or(0);
    for step in 0..max_steps {
        let active: Vec<usize> = (0..count).filter(|&i| step < targets[i].4).collect();
        let mut active_st = secret_vecs_with_capacity(m, active.len());
        for p in 0..m {
            for &i in &active {
                secret_vec_push(&mut active_st[p], cur_states[p][i]);
            }
        }
        let active_bytes = SecretBuffer(
            match eval_spdz_canonical_a2b_state4_batch_to_bytes32(
                t,
                quorum_pts,
                &active_st,
                vaults,
                &mut pending,
            ) {
                Ok(b) => b,
                Err(e) => {
                    poison_all_on_abort(key_shares, vaults);
                    return Err(Poseidon2MpcError::Preprocess(e));
                }
            },
        );

        let mut step_tmpls = Vec::with_capacity(active.len());
        for &i in &active {
            let (layer, tree, kp, ch_idx, _) = targets[i];
            let adrs = HashAdrs {
                layer,
                tree,
                kind: AdrsKind::WotsHash,
                key_pair: kp,
                chain_idx: ch_idx,
                hash_step: step as u32,
            };
            step_tmpls.push(build_single_secret32_template(TAG_TH_F, pk_seed, &adrs));
        }

        let next_st = SecretBuffer(
            match eval_spdz_poseidon2_hash32_templates(
                t,
                quorum_pts,
                &step_tmpls,
                &active_bytes,
                vaults,
                &mut pending,
            ) {
                Ok(s) => s,
                Err(e) => {
                    poison_all_on_abort(key_shares, vaults);
                    return Err(Poseidon2MpcError::Preprocess(e));
                }
            },
        );

        for p in 0..m {
            for (slot, &i) in active.iter().enumerate() {
                cur_states[p][i] = next_st[p][slot];
            }
        }
    }

    let empty_extra = vec![Vec::new(); m];
    let (digests, _) = flush_verify_and_open_cut_states4(
        session_id,
        phase,
        t,
        quorum_pts,
        &cur_states,
        &empty_extra,
        &mut pending,
        key_shares,
        vaults,
        party_rngs,
    )?;
    Ok(digests)
}

/// Evaluate every WOTS+C chain of subtree `(layer, tree)` to full depth in MPC and compress each
/// key pair's endpoints into its public leaf digest.
#[expect(
    clippy::too_many_arguments,
    reason = "One MPC phase: transcript context, parameters, quorum, subtree address and per-party state"
)]
fn compute_subtree_wots_pks_mpc(
    session_id: &[u8; 32],
    phase: &'static str,
    params: &PqHashParams,
    t: usize,
    quorum_pts: &[Goldilocks],
    pk_seed: &[u8; 32],
    layer_u32: u32,
    tree_idx: u64,
    key_shares: &mut [&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<[u8; 32]>, Poseidon2MpcError> {
    let sub_leaves = 1usize << params.subtree_height;
    let steps = params.w - 1;
    let mut targets = Vec::with_capacity(sub_leaves * params.ell1);
    for kp in 0..sub_leaves {
        for r in 0..params.ell1 {
            targets.push((layer_u32, tree_idx, kp as u32, r as u32, steps));
        }
    }
    let endpoints = eval_wots_chains_mpc_cut(
        session_id, phase, t, quorum_pts, pk_seed, &targets, key_shares, vaults, party_rngs,
    )?;
    let mut leaves = Vec::with_capacity(sub_leaves);
    for kp in 0..sub_leaves {
        let slice = &endpoints[kp * params.ell1..(kp + 1) * params.ell1];
        let pk_adrs = HashAdrs {
            layer: layer_u32,
            tree: tree_idx,
            kind: AdrsKind::WotsPk,
            key_pair: kp as u32,
            chain_idx: 0,
            hash_step: 0,
        };
        leaves.push(th_tweak_tl(Poseidon2Suite, pk_seed, &pk_adrs, slice));
    }
    Ok(leaves)
}

/// Count the same padded sponge blocks as the online evaluator, including framing.
fn template_permutations(template: &(Vec<u8>, usize)) -> usize {
    let mut limbs = bytes_to_limbs56(&template.0);
    poseidon2_pad(&mut limbs);
    limbs.len() / 8
}

fn chain_template_permutations() -> (usize, usize) {
    let prf = build_single_secret32_template(TAG_PRF, &[0; 32], &HashAdrs::ZERO);
    let step = build_single_secret32_template(TAG_TH_F, &[0; 32], &HashAdrs::ZERO);
    (template_permutations(&prf), template_permutations(&step))
}

/// Compute exact preprocessing tuple budget `(num_pow7, num_beaver, num_a2b)` required by
/// [`build_distributed_poseidon2_key`].
pub fn required_poseidon2_keygen_preprocessing_budget(
    params: &PqHashParams,
) -> (usize, usize, usize) {
    let sub_leaves = 1usize << params.subtree_height;
    let chains = sub_leaves * params.ell1;
    let steps = params.w.saturating_sub(1);
    let (prf_perms, step_perms) = chain_template_permutations();
    let perms_per_chain = prf_perms + steps * step_perms;
    let num_pow7 = chains * perms_per_chain * POSEIDON2_SBOXES_PER_PERM;
    let num_a2b_hashes = chains * steps;
    (
        num_pow7,
        num_a2b_hashes * POSEIDON2_BEAVER_PER_A2B_HASH32,
        num_a2b_hashes * 4,
    )
}

/// Compute exact preprocessing tuple budget `(num_pow7, num_beaver, num_a2b)` required by one
/// [`sign_jorts_poseidon2_mpc`] or [`sign_stateless_tsw_poseidon2_mpc`] signature.
pub fn required_poseidon2_sign_preprocessing_budget(
    params: &PqHashParams,
) -> (usize, usize, usize) {
    sign_preprocessing_budget(params, false)
}

/// Preprocessing tuple budget `(num_pow7, num_beaver, num_a2b)` sufficient for one signature made
/// with a top-subtree leaf cache ([`sign_jorts_poseidon2_mpc_cached`],
/// [`retry_jorts_poseidon2_mpc_cached`] or [`sign_stateless_tsw_poseidon2_mpc_cached`]
/// with `Some(cache)`).
///
/// It is smaller than [`required_poseidon2_sign_preprocessing_budget`] by exactly one
/// [`required_poseidon2_keygen_preprocessing_budget`]: the top subtree's `2^subtree_height * ell1`
/// full-depth chains are not evaluated.
pub fn required_poseidon2_sign_preprocessing_budget_cached(
    params: &PqHashParams,
) -> (usize, usize, usize) {
    sign_preprocessing_budget(params, true)
}

fn sign_preprocessing_budget(
    params: &PqHashParams,
    top_subtree_cached: bool,
) -> (usize, usize, usize) {
    let sub_leaves = 1usize << params.subtree_height;
    let steps_max = params.w.saturating_sub(1);
    let fors_leaves = if params.stateful {
        0
    } else {
        params.fors_trees * (1usize << params.fors_height)
    };
    // With a top-subtree leaf cache the top layer evaluates only its `ell1` signing chains.
    let mpc_subtrees = params
        .num_layers
        .saturating_sub(usize::from(top_subtree_cached));
    let hypertree_chains =
        params.num_layers * params.ell1 + mpc_subtrees * sub_leaves * params.ell1;
    let (prf_perms, step_perms) = chain_template_permutations();
    let opt_domain = if params.stateful {
        build_stateful_det_opt_domain(0, &[0; 32])
    } else {
        build_stateless_det_opt_domain(&[0; 32])
    };
    let randomizer_perms = template_permutations(&build_prf_msg_template(&opt_domain, &[0; 32]));
    let total_perms = randomizer_perms
        + fors_leaves * (prf_perms + step_perms)
        + hypertree_chains * (prf_perms + steps_max * step_perms);
    let total_a2b_hashes = fors_leaves + hypertree_chains * steps_max;
    (
        total_perms * POSEIDON2_SBOXES_PER_PERM,
        total_a2b_hashes * POSEIDON2_BEAVER_PER_A2B_HASH32,
        total_a2b_hashes * 4,
    )
}

/// Build the distributed `PqPublicKey` (`pk_seed`, `pk_root`) over `Poseidon2Suite` via dishonest-
/// majority SPDZ MPC without ever reconstructing `SK.seed` or `SK.prf`.
pub fn build_distributed_poseidon2_key(
    session_id: [u8; 32],
    params: &PqHashParams,
    t: usize,
    key_shares: &mut [&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<PqPublicKey, Poseidon2MpcError> {
    build_distributed_poseidon2_key_cached(session_id, params, t, key_shares, vaults, party_rngs)
        .map(|cache| cache.pk)
}

/// [`build_distributed_poseidon2_key`], additionally keeping the top subtree's public leaf digests.
///
/// The returned [`DkgCachedSubtrees`] holds the `2^subtree_height` WOTS+C public-key digests of
/// subtree `(layer = num_layers - 1, tree = 0)` together with the public key they hash to. Passing
/// it to the `_cached` signing functions lets a signature skip recomputing that subtree in MPC.
pub fn build_distributed_poseidon2_key_cached(
    session_id: [u8; 32],
    params: &PqHashParams,
    t: usize,
    key_shares: &mut [&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<DkgCachedSubtrees, Poseidon2MpcError> {
    if !params.is_well_formed() {
        return Err(Poseidon2MpcError::InvalidParams);
    }
    let (pk_seed, quorum_pts) = validate_quorum_slices(t, key_shares, vaults, party_rngs)?;
    let first_enrolled = key_shares[0].enrolled_profile;
    for ks in key_shares.iter().skip(1) {
        match (first_enrolled, ks.enrolled_profile) {
            (None, None) => {}
            (Some((p0, k0)), Some((pi, ki)))
                if p0 == pi
                    && ct_eq_bytes32(&k0.pk_seed, &ki.pk_seed)
                    && ct_eq_bytes32(&k0.pk_root, &ki.pk_root) => {}
            _ => return Err(Poseidon2MpcError::KeyProfileMismatch),
        }
    }
    if let Some((ep, _)) = first_enrolled
        && ep != *params
    {
        return Err(Poseidon2MpcError::KeyProfileMismatch);
    }
    let top_layer = (params.num_layers - 1) as u32;
    let top_leaves = compute_subtree_wots_pks_mpc(
        &session_id,
        "pos2_keygen_top_leaves",
        params,
        t,
        &quorum_pts,
        &pk_seed,
        top_layer,
        0,
        key_shares,
        vaults,
        party_rngs,
    )?;
    let (pk_root, _) = build_merkle_from_leaves_topdown(
        Poseidon2Suite,
        &pk_seed,
        top_layer,
        0,
        AdrsKind::Tree,
        0,
        &top_leaves,
        params.subtree_height,
        0,
        0,
    );
    let pk = PqPublicKey { pk_seed, pk_root };
    for ks in key_shares.iter_mut() {
        ks.enroll_key_profile(*params, pk)?;
    }
    Ok(DkgCachedSubtrees {
        top_layer,
        top_leaves,
        pk,
    })
}

/// Check that an optional top-subtree leaf cache belongs to `(params, pk)`.
///
/// The cache is public data from the caller, so it is accepted only if it names the top layer,
/// carries this public key, has `2^subtree_height` leaves, and those leaves hash to `pk_root`.
/// Runs before any epoch is latched or any preprocessing is consumed.
pub(super) fn validate_top_subtree_cache(
    params: &PqHashParams,
    pk: &PqPublicKey,
    cache: Option<&DkgCachedSubtrees>,
) -> Result<(), Poseidon2MpcError> {
    let Some(cache) = cache else {
        return Ok(());
    };
    let top_layer = (params.num_layers - 1) as u32;
    if cache.top_layer != top_layer
        || cache.pk != *pk
        || cache.top_leaves.len() != 1usize << params.subtree_height
    {
        return Err(Poseidon2MpcError::CachedSubtreeMismatch);
    }
    let (root, _) = build_merkle_from_leaves_topdown(
        Poseidon2Suite,
        &pk.pk_seed,
        top_layer,
        0,
        AdrsKind::Tree,
        0,
        &cache.top_leaves,
        params.subtree_height,
        0,
        0,
    );
    if root != pk.pk_root {
        return Err(Poseidon2MpcError::CachedSubtreeMismatch);
    }
    Ok(())
}

#[expect(
    clippy::too_many_arguments,
    reason = "One signature: transcript context, parameters, public key, optional leaf cache, message inputs and per-party state"
)]
fn sign_hypertree_poseidon2_mpc_core(
    session_id: &[u8; 32],
    params: &PqHashParams,
    pk: &PqPublicKey,
    cache: Option<&DkgCachedSubtrees>,
    t: usize,
    quorum_pts: &[Goldilocks],
    mu: &[u8; 32],
    r_rand: [u8; 32],
    leaf_global_idx: usize,
    fors_idxs: Option<&[usize]>,
    max_grind: u32,
    key_shares: &mut [&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<PqHashSig, Poseidon2MpcError> {
    let m = quorum_pts.len();
    let sub_leaves = 1usize << params.subtree_height;
    if cache.is_some_and(|c| c.top_layer as usize != params.num_layers - 1) {
        return Err(Poseidon2MpcError::CachedSubtreeMismatch);
    }

    let (fors_openings, mut cur_root) = if params.stateful {
        (Vec::new(), *mu)
    } else {
        let idxs = fors_idxs.ok_or(Poseidon2MpcError::InvalidParams)?;
        let kp0 = (leaf_global_idx % sub_leaves) as u32;
        let tree0 = (leaf_global_idx / sub_leaves) as u64;
        let fors_leaf_count = 1usize << params.fors_height;
        let total_fors = params.fors_trees * fors_leaf_count;

        let mut pending = SpdzGoldilocksPendingChecks::new(m);
        let mut prf_tmpls = Vec::with_capacity(total_fors);
        let mut f_tmpls = Vec::with_capacity(total_fors);
        for j in 0..params.fors_trees {
            for u in 0..fors_leaf_count {
                let prf_adrs = HashAdrs {
                    layer: 0,
                    tree: tree0,
                    kind: AdrsKind::ForsPrf,
                    key_pair: kp0,
                    chain_idx: j as u32,
                    hash_step: u as u32,
                };
                prf_tmpls.push(build_single_secret32_template(
                    TAG_PRF,
                    &pk.pk_seed,
                    &prf_adrs,
                ));
                let tree_adrs = HashAdrs {
                    layer: 0,
                    tree: tree0,
                    kind: AdrsKind::ForsTree,
                    key_pair: kp0,
                    chain_idx: j as u32,
                    hash_step: u as u32,
                };
                f_tmpls.push(build_single_secret32_template(
                    TAG_TH_F,
                    &pk.pk_seed,
                    &tree_adrs,
                ));
            }
        }
        let mut prf_secs = secret_vecs_with_capacity(m, total_fors);
        for p in 0..m {
            let sw = SecretBuffer(key_seed_wires(key_shares[p]));
            for _ in 0..total_fors {
                secret_vec_push(&mut prf_secs[p], *sw);
            }
        }
        let sec_states = SecretBuffer(
            match eval_spdz_poseidon2_hash32_templates(
                t,
                quorum_pts,
                &prf_tmpls,
                &prf_secs,
                vaults,
                &mut pending,
            ) {
                Ok(s) => s,
                Err(e) => {
                    poison_all_on_abort(key_shares, vaults);
                    return Err(Poseidon2MpcError::Preprocess(e));
                }
            },
        );

        // Convert ALL `total_fors` secret states to canonical byte shares via A2B so unrevealed
        // FORS leaves NEVER open `sec_states`, and open ONLY the `fors_trees` selected `secret_val`s
        // plus the `total_fors` public leaf hashes at the cut boundary!
        let sec_bytes = SecretBuffer(
            match eval_spdz_canonical_a2b_state4_batch_to_bytes32(
                t,
                quorum_pts,
                &sec_states,
                vaults,
                &mut pending,
            ) {
                Ok(b) => b,
                Err(e) => {
                    poison_all_on_abort(key_shares, vaults);
                    return Err(Poseidon2MpcError::Preprocess(e));
                }
            },
        );

        let leaf_states = match eval_spdz_poseidon2_hash32_templates(
            t,
            quorum_pts,
            &f_tmpls,
            &sec_bytes,
            vaults,
            &mut pending,
        ) {
            Ok(s) => s,
            Err(e) => {
                poison_all_on_abort(key_shares, vaults);
                return Err(Poseidon2MpcError::Preprocess(e));
            }
        };

        // Selected `fors_trees` revealed `secret_val` states are also cut-boundary digests!
        let mut cut_states = SecretBuffer(leaf_states);
        for p in 0..m {
            secret_vec_reserve(&mut cut_states[p], params.fors_trees);
            for (j, &idx_j) in idxs.iter().enumerate().take(params.fors_trees) {
                secret_vec_push(
                    &mut cut_states[p],
                    sec_states[p][j * fors_leaf_count + idx_j],
                );
            }
        }
        let empty_extra = vec![Vec::new(); m];
        let (opened_fors, _) = flush_verify_and_open_cut_states4(
            session_id,
            "pos2_fors_cut",
            t,
            quorum_pts,
            &cut_states,
            &empty_extra,
            &mut pending,
            key_shares,
            vaults,
            party_rngs,
        )?;

        let mut openings = Vec::with_capacity(params.fors_trees);
        let mut roots = Vec::with_capacity(params.fors_trees);
        for (j, &idx_j) in idxs.iter().enumerate().take(params.fors_trees) {
            let leaves_j = &opened_fors[j * fors_leaf_count..(j + 1) * fors_leaf_count];
            let revealed_sec = opened_fors[total_fors + j];
            let (root_j, path_j) = build_merkle_from_leaves_topdown(
                Poseidon2Suite,
                &pk.pk_seed,
                0,
                tree0,
                AdrsKind::ForsTree,
                kp0,
                leaves_j,
                params.fors_height,
                j,
                idx_j,
            );
            roots.push(root_j);
            openings.push(ForsTreeOpening {
                secret_val: revealed_sec,
                auth_path: path_j,
            });
        }
        let fors_pk_adrs = HashAdrs {
            layer: 0,
            tree: tree0,
            kind: AdrsKind::ForsRoots,
            key_pair: kp0,
            chain_idx: 0,
            hash_step: 0,
        };
        let fors_pk = th_tweak_tl(Poseidon2Suite, &pk.pk_seed, &fors_pk_adrs, &roots);
        (openings, fors_pk)
    };

    let mut layer_sigs = Vec::with_capacity(params.num_layers);
    let mut cur_global = leaf_global_idx;
    for layer_idx in 0..params.num_layers {
        let kp_idx = cur_global % sub_leaves;
        let tree_idx_nat = cur_global / sub_leaves;
        let tree_idx = tree_idx_nat as u64;
        let layer_u32 = layer_idx as u32;
        let kp_u32 = kp_idx as u32;

        // Public leaves of this layer's subtree, when the caller's cache covers it.
        let cached_leaves: Option<&[[u8; 32]]> = match cache {
            Some(c) if c.top_layer == layer_u32 => {
                if tree_idx != 0 || c.pk != *pk || c.top_leaves.len() != sub_leaves {
                    return Err(Poseidon2MpcError::CachedSubtreeMismatch);
                }
                Some(&c.top_leaves)
            }
            _ => None,
        };

        let (ctr, digits, _) = if params.stateful && layer_idx == 0 {
            grind_tsw_leaf_counter(
                Poseidon2Suite,
                params.w,
                params.ell1,
                params.target_sum(),
                &r_rand,
                &pk.pk_seed,
                &pk.pk_root,
                &cur_root,
                tree_idx,
                kp_u32,
                max_grind,
            )
            .ok_or(Poseidon2MpcError::TswGrindExhausted)?
        } else {
            grind_tsw_internal_counter(
                Poseidon2Suite,
                params.w,
                params.ell1,
                params.target_sum(),
                &pk.pk_seed,
                &pk.pk_root,
                &cur_root,
                layer_u32,
                tree_idx,
                kp_u32,
                max_grind,
            )
            .ok_or(Poseidon2MpcError::TswGrindExhausted)?
        };

        let mut sig_targets = Vec::with_capacity(params.ell1);
        for (r, &dr) in digits.iter().enumerate().take(params.ell1) {
            sig_targets.push((layer_u32, tree_idx, kp_u32, r as u32, dr));
        }
        let wots_chains = eval_wots_chains_mpc_cut(
            session_id,
            "pos2_layer_wots_sig",
            t,
            quorum_pts,
            &pk.pk_seed,
            &sig_targets,
            key_shares,
            vaults,
            party_rngs,
        )?;

        // Sibling leaves are public and static per `(layer, tree)`: a cached subtree needs no MPC
        // beyond the signing chains above.
        let computed_leaves;
        let subtree_leaves = match cached_leaves {
            Some(leaves) => leaves,
            None => {
                computed_leaves = compute_subtree_wots_pks_mpc(
                    session_id,
                    "pos2_layer_subtree_pks",
                    params,
                    t,
                    quorum_pts,
                    &pk.pk_seed,
                    layer_u32,
                    tree_idx,
                    key_shares,
                    vaults,
                    party_rngs,
                )?;
                &computed_leaves[..]
            }
        };
        let (next_root, auth_path) = build_merkle_from_leaves_topdown(
            Poseidon2Suite,
            &pk.pk_seed,
            layer_u32,
            tree_idx,
            AdrsKind::Tree,
            0,
            subtree_leaves,
            params.subtree_height,
            0,
            kp_idx,
        );
        layer_sigs.push(LayerXmssSig {
            tsw_ctr: ctr,
            wots_chains,
            auth_path,
        });
        cur_root = next_root;
        cur_global = tree_idx_nat;
    }

    let sig = PqHashSig {
        r_rand,
        leaf_global_idx,
        msg_tsw_ctr: 0,
        fors_openings,
        layer_sigs,
    };
    Ok(sig)
}

#[expect(
    clippy::too_many_arguments,
    reason = "One MPC phase: transcript context, quorum, PRF inputs and per-party state"
)]
fn eval_prf_msg_mpc_cut(
    session_id: &[u8; 32],
    phase: &'static str,
    t: usize,
    quorum_pts: &[Goldilocks],
    opt_rand: &[u8],
    mu: &[u8; 32],
    key_shares: &mut [&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<[u8; 32], Poseidon2MpcError> {
    let m = quorum_pts.len();
    let mut pending = SpdzGoldilocksPendingChecks::new(m);
    let tmpl = build_prf_msg_template(opt_rand, mu);
    let tmpls = [tmpl];
    let mut prf_secs = secret_vecs_with_capacity(m, 1);
    for p in 0..m {
        let pw = SecretBuffer(key_prf_wires(key_shares[p]));
        secret_vec_push(&mut prf_secs[p], *pw);
    }
    let st4 = SecretBuffer(
        match eval_spdz_poseidon2_hash32_templates(
            t,
            quorum_pts,
            &tmpls,
            &prf_secs,
            vaults,
            &mut pending,
        ) {
            Ok(s) => s,
            Err(e) => {
                poison_all_on_abort(key_shares, vaults);
                return Err(Poseidon2MpcError::Preprocess(e));
            }
        },
    );
    let empty_extra = vec![Vec::new(); m];
    let (digests, _) = flush_verify_and_open_cut_states4(
        session_id,
        phase,
        t,
        quorum_pts,
        &st4,
        &empty_extra,
        &mut pending,
        key_shares,
        vaults,
        party_rngs,
    )?;
    Ok(digests[0])
}

fn validate_enrolled_key_profile(
    params: &PqHashParams,
    pk: &PqPublicKey,
    quorum_pk_seed: &[u8; 32],
    key_shares: &[&mut Poseidon2SpdzAuthenticatedKeyShare],
) -> Result<(), Poseidon2MpcError> {
    if !ct_eq_bytes32(&pk.pk_seed, quorum_pk_seed) {
        return Err(Poseidon2MpcError::PublicSeedMismatch);
    }
    for ks in key_shares {
        let Some((ep, epk)) = ks.enrolled_profile.as_ref() else {
            return Err(Poseidon2MpcError::KeyNotEnrolled);
        };
        if *ep != *params
            || !ct_eq_bytes32(&epk.pk_seed, &pk.pk_seed)
            || !ct_eq_bytes32(&epk.pk_root, &pk.pk_root)
        {
            return Err(Poseidon2MpcError::KeyProfileMismatch);
        }
    }
    Ok(())
}

pub(super) fn resolve_enrolled_latch_authority<'a>(
    key_shares: &'a [&mut Poseidon2SpdzAuthenticatedKeyShare],
) -> Result<Option<&'a EpochLatchAuthorityPublic>, Poseidon2MpcError> {
    let first = key_shares[0].enrolled_latch_authority.as_ref();
    for ks in key_shares.iter().skip(1) {
        if ks.enrolled_latch_authority.as_ref() != first {
            return Err(Poseidon2MpcError::LatchCertificateRejected(
                QuorumLatchError::CertificateCommitteeMismatch,
            ));
        }
    }
    Ok(first)
}

/// Committee-wide latch gate of the stateful signers.
///
/// A one-time leaf may open for one message only, whichever `t` members sign. Local latches
/// enforce that among the members present; two signing sets that overlap only in corrupt members
/// could still each reserve the same epoch for a different message. So local latches are accepted
/// on their own only at full attendance (`signers == n`, where the set is itself a latch quorum:
/// `2n > n + (t - 1)`), and any smaller signing set must present a certificate that a quorum `q`
/// with `2q > n + (t - 1)` reserved exactly this `(key, epoch, mu)` under the committee's pinned
/// [`EpochLatchAuthorityPublic`].
///
/// Reads public values only and changes nothing.
#[expect(
    clippy::too_many_arguments,
    reason = "Latch authorization binds public key, committee threshold, attendance, pinned authority, certificate, epoch and message digest"
)]
pub(super) fn check_committee_latch_authorisation(
    pk: &PqPublicKey,
    t: usize,
    n: usize,
    signers: usize,
    pinned_authority: Option<&EpochLatchAuthorityPublic>,
    latch_cert: Option<&EpochLatchCertificate>,
    epoch: u64,
    mu: &[u8; 32],
) -> Result<(), Poseidon2MpcError> {
    match latch_cert {
        Some(cert) => {
            let binding = epoch_latch_binding(&pk.pk_seed, &pk.pk_root, epoch, mu);
            if let Some(authority) = pinned_authority {
                cert.verify_against(authority, n, t, epoch, &binding)
                    .map_err(Poseidon2MpcError::LatchCertificateRejected)
            } else {
                cert.verify_for(n, t, epoch, &binding)
                    .map_err(Poseidon2MpcError::LatchCertificateRejected)?;
                Err(Poseidon2MpcError::LatchCertificateRejected(
                    QuorumLatchError::CertificateCommitteeMismatch,
                ))
            }
        }
        None if signers == n && latch_quorum_intersects_honestly(signers, n, t) => Ok(()),
        None => Err(Poseidon2MpcError::LatchCertificateRequired {
            signers,
            committee: n,
        }),
    }
}

/// Pick the epoch of a new stateful signature and reserve it in every signer's latch.
///
/// With a certificate the epoch is the certified one; a signer whose latch is behind skips
/// forward to it, and one already holding `(epoch, mu)` in flight keeps it. Without a certificate
/// (full attendance only) the epoch is the next epoch of the latches, which must all agree.
///
/// Every check runs before the first latch moves: a missing or rejected certificate, latches
/// that disagree, a latch already past the epoch or holding it for another digest, and an
/// exhausted key all return with every latch unchanged. The only way to return an error after
/// some latches moved is a durable latch failing to persist in the second pass; the latches
/// before it in the slice then hold `(epoch, mu)`, which is the reservation the gate authorised
/// and is accepted again when the same certificate is presented.
#[expect(
    clippy::too_many_arguments,
    reason = "Epoch reservation checks parameters, public key, threshold, pinned authority, certificate, latches and message digest"
)]
pub(super) fn reserve_authorised_epoch<L: StatefulEpochLatch>(
    params: &PqHashParams,
    pk: &PqPublicKey,
    t: usize,
    n: usize,
    pinned_authority: Option<&EpochLatchAuthorityPublic>,
    latch_cert: Option<&EpochLatchCertificate>,
    latches: &mut [&mut L],
    mu: &[u8; 32],
) -> Result<u64, Poseidon2MpcError> {
    let Some(first) = latches.first() else {
        return Err(Poseidon2MpcError::InvalidQuorum { t, n: 0 });
    };
    let epoch = match latch_cert {
        Some(cert) => cert.epoch(),
        None => first.peek_next_epoch(),
    };
    check_committee_latch_authorisation(
        pk,
        t,
        n,
        latches.len(),
        pinned_authority,
        latch_cert,
        epoch,
        mu,
    )?;
    if latch_cert.is_none() && latches.iter().any(|l| l.peek_next_epoch() != epoch) {
        return Err(Poseidon2MpcError::EpochLatch(
            EpochLatchError::LatchesDisagree,
        ));
    }
    for l in latches.iter() {
        l.check_reserve_epoch_at(epoch, params.max_sigs_log2, mu)?;
    }
    for l in latches.iter_mut() {
        l.reserve_epoch_at(epoch, params.max_sigs_log2, mu)?;
    }
    Ok(epoch)
}

/// Sign a message under stateful `JortsPoseidon2` via dishonest-majority $t$-of-$n$ Shamir SPDZ:
/// - Requires committee-wide latch authorisation for `mu = H_pre(pk_seed, pk_root, msg)`: either
///   all `n` members sign (then `latch_cert` may be `None`), or `latch_cert` certifies that a
///   quorum `q` with `2q > n + (t - 1)` reserved this `(key, epoch, mu)`. Fewer than `n` signers
///   without a certificate get [`Poseidon2MpcError::LatchCertificateRequired`]; a certificate
///   for another committee, key, epoch or message gets
///   [`Poseidon2MpcError::LatchCertificateRejected`]. Both are returned before any latch moves
///   and before any share or preprocessing is used;
/// - Reserves the epoch in EVERY participating party's non-clonable [`StatefulEpochLatch`]
///   BEFORE any secret MPC wire is opened (all latches are checked first, so a latch that cannot
///   take the epoch leaves the others where they were);
/// - Derives `r_rand = PRF_msg(SK.prf, build_stateful_det_opt_domain(epoch, pk_seed), mu)` in SPDZ;
/// - Evaluates the hypertree WOTS+C chains and verifies `verify_pq_hash_sig` before returning.
///
/// Availability is that of the latch quorum: `floor((n + t - 1) / 2) + 1` members must
/// acknowledge every signature, which for `(t, n) = (2, 3)` is all three.
#[expect(
    clippy::too_many_arguments,
    reason = "One signing session: parameters, public key, committee latch certificate, quorum latches, message and per-party state"
)]
pub fn sign_jorts_poseidon2_mpc<L: StatefulEpochLatch>(
    session_id: [u8; 32],
    params: &PqHashParams,
    pk: &PqPublicKey,
    t: usize,
    latch_cert: Option<&EpochLatchCertificate>,
    latches: &mut [&mut L],
    msg: &[u8],
    max_grind: u32,
    key_shares: &mut [&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<(u64, PqHashSig), Poseidon2MpcError> {
    sign_jorts_poseidon2_mpc_cached(
        session_id, params, pk, None, t, latch_cert, latches, msg, max_grind, key_shares, vaults,
        party_rngs,
    )
}

/// [`sign_jorts_poseidon2_mpc`] with an optional top-subtree leaf cache.
///
/// With `Some(cache)` the top layer's Merkle root and authentication path come from
/// `cache.top_leaves`, and MPC evaluates only that layer's `ell1` signing chains. The signature is
/// byte-identical to the uncached one. A cache that does not match `(params, pk)` is rejected with
/// [`Poseidon2MpcError::CachedSubtreeMismatch`] before any epoch is latched.
#[expect(
    clippy::too_many_arguments,
    reason = "One signing session: parameters, public key, optional leaf cache, committee latch certificate, quorum latches, message and per-party state"
)]
pub fn sign_jorts_poseidon2_mpc_cached<L: StatefulEpochLatch>(
    session_id: [u8; 32],
    params: &PqHashParams,
    pk: &PqPublicKey,
    cache: Option<&DkgCachedSubtrees>,
    t: usize,
    latch_cert: Option<&EpochLatchCertificate>,
    latches: &mut [&mut L],
    msg: &[u8],
    max_grind: u32,
    key_shares: &mut [&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<(u64, PqHashSig), Poseidon2MpcError> {
    if !params.is_well_formed() || !params.stateful {
        return Err(Poseidon2MpcError::InvalidParams);
    }
    validate_top_subtree_cache(params, pk, cache)?;
    if latches.len() != key_shares.len() {
        return Err(Poseidon2MpcError::InvalidQuorum {
            t,
            n: latches.len(),
        });
    }
    let (quorum_pk_seed, quorum_pts) = validate_quorum_slices(t, key_shares, vaults, party_rngs)?;
    validate_enrolled_key_profile(params, pk, &quorum_pk_seed, key_shares)?;
    let committee_size = key_shares[0].committee_size;
    let mu = th_pre_hash(Poseidon2Suite, &pk.pk_seed, &pk.pk_root, msg);

    let ep0 = {
        let pinned_authority = resolve_enrolled_latch_authority(key_shares)?;
        reserve_authorised_epoch(
            params,
            pk,
            t,
            committee_size,
            pinned_authority,
            latch_cert,
            latches,
            &mu,
        )?
    };
    let leaf_global_idx = usize::try_from(ep0)
        .map_err(|_| Poseidon2MpcError::EpochLatch(EpochLatchError::Exhausted))?;

    let opt_domain = build_stateful_det_opt_domain(ep0, &pk.pk_seed);
    let r_rand = eval_prf_msg_mpc_cut(
        &session_id,
        "pos2_stateful_r_rand",
        t,
        &quorum_pts,
        &opt_domain,
        &mu,
        key_shares,
        vaults,
        party_rngs,
    )?;

    let sig = sign_hypertree_poseidon2_mpc_core(
        &session_id,
        params,
        pk,
        cache,
        t,
        &quorum_pts,
        &mu,
        r_rand,
        leaf_global_idx,
        None,
        max_grind,
        key_shares,
        vaults,
        party_rngs,
    )?;
    if !verify_pq_hash_sig(Poseidon2Suite, params, pk, msg, &sig) {
        return Err(Poseidon2MpcError::SignatureSelfCheckFailed);
    }
    Ok((ep0, sig))
}

/// Safe crash-recovery retry for stateful `JortsPoseidon2` (`[P0-04]`):
/// - Applies the same committee-wide latch gate as [`sign_jorts_poseidon2_mpc`] to
///   `(epoch, mu)`: full attendance, or a certificate for exactly this key, epoch and message;
/// - Verifies `latch.retry_latched_epoch(epoch, &mu)` across all quorum latches (refusing any
///   unlatched epoch or equivocated message digest); no latch is advanced;
/// - Re-derives the exact deterministic `r_rand` and bit-identical `PqHashSig`.
#[expect(
    clippy::too_many_arguments,
    reason = "One retry session: parameters, public key, committee latch certificate, quorum latches, latched epoch, message and per-party state"
)]
pub fn retry_jorts_poseidon2_mpc<L: StatefulEpochLatch>(
    session_id: [u8; 32],
    params: &PqHashParams,
    pk: &PqPublicKey,
    t: usize,
    latch_cert: Option<&EpochLatchCertificate>,
    latches: &mut [&mut L],
    epoch: u64,
    msg: &[u8],
    max_grind: u32,
    key_shares: &mut [&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<PqHashSig, Poseidon2MpcError> {
    retry_jorts_poseidon2_mpc_cached(
        session_id, params, pk, None, t, latch_cert, latches, epoch, msg, max_grind, key_shares,
        vaults, party_rngs,
    )
}

/// [`retry_jorts_poseidon2_mpc`] with an optional top-subtree leaf cache (same cache
/// rules as [`sign_jorts_poseidon2_mpc_cached`]).
#[expect(
    clippy::too_many_arguments,
    reason = "One retry session: parameters, public key, optional leaf cache, committee latch certificate, quorum latches, latched epoch, message and per-party state"
)]
pub fn retry_jorts_poseidon2_mpc_cached<L: StatefulEpochLatch>(
    session_id: [u8; 32],
    params: &PqHashParams,
    pk: &PqPublicKey,
    cache: Option<&DkgCachedSubtrees>,
    t: usize,
    latch_cert: Option<&EpochLatchCertificate>,
    latches: &mut [&mut L],
    epoch: u64,
    msg: &[u8],
    max_grind: u32,
    key_shares: &mut [&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<PqHashSig, Poseidon2MpcError> {
    if !params.is_well_formed() || !params.stateful {
        return Err(Poseidon2MpcError::InvalidParams);
    }
    validate_top_subtree_cache(params, pk, cache)?;
    if latches.len() != key_shares.len() {
        return Err(Poseidon2MpcError::InvalidQuorum {
            t,
            n: latches.len(),
        });
    }
    let (quorum_pk_seed, quorum_pts) = validate_quorum_slices(t, key_shares, vaults, party_rngs)?;
    validate_enrolled_key_profile(params, pk, &quorum_pk_seed, key_shares)?;
    let committee_size = key_shares[0].committee_size;
    let mu = th_pre_hash(Poseidon2Suite, &pk.pk_seed, &pk.pk_root, msg);

    {
        let pinned_authority = resolve_enrolled_latch_authority(key_shares)?;
        check_committee_latch_authorisation(
            pk,
            t,
            committee_size,
            latches.len(),
            pinned_authority,
            latch_cert,
            epoch,
            &mu,
        )?;
    }
    for l in latches.iter_mut() {
        let ep = l.retry_latched_epoch(epoch, &mu)?;
        if ep != epoch {
            return Err(Poseidon2MpcError::EpochLatch(
                EpochLatchError::EquivocationRefused,
            ));
        }
    }
    let leaf_global_idx = usize::try_from(epoch)
        .map_err(|_| Poseidon2MpcError::EpochLatch(EpochLatchError::Exhausted))?;
    let opt_domain = build_stateful_det_opt_domain(epoch, &pk.pk_seed);
    let r_rand = eval_prf_msg_mpc_cut(
        &session_id,
        "pos2_stateful_retry_r_rand",
        t,
        &quorum_pts,
        &opt_domain,
        &mu,
        key_shares,
        vaults,
        party_rngs,
    )?;

    let sig = sign_hypertree_poseidon2_mpc_core(
        &session_id,
        params,
        pk,
        cache,
        t,
        &quorum_pts,
        &mu,
        r_rand,
        leaf_global_idx,
        None,
        max_grind,
        key_shares,
        vaults,
        party_rngs,
    )?;
    if !verify_pq_hash_sig(Poseidon2Suite, params, pk, msg, &sig) {
        return Err(Poseidon2MpcError::SignatureSelfCheckFailed);
    }
    Ok(sig)
}

/// The stateless signers' randomiser `R = PRF_msg(SK.prf, build_stateless_det_opt_domain(pk_seed), mu)`,
/// evaluated on shares and opened after its MAC check.
///
/// Every input other than the shared `SK.prf` is fixed by the key and the message digest, so no
/// caller, signer or session contributes to `R`: aborting and retrying a session reproduces the
/// same `R` and therefore the same hypertree leaf and FORS instance.
#[expect(
    clippy::too_many_arguments,
    reason = "One MPC phase: transcript context, quorum, public key, message digest and per-party state"
)]
pub(super) fn eval_stateless_r_rand_mpc(
    session_id: &[u8; 32],
    t: usize,
    quorum_pts: &[Goldilocks],
    pk: &PqPublicKey,
    mu: &[u8; 32],
    key_shares: &mut [&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<[u8; 32], Poseidon2MpcError> {
    let transcript = crate::sponge::keccak::encode_multi_frame(&[session_id, mu]);
    for rng in party_rngs.iter_mut() {
        rng.hedge_transcript(&transcript);
    }
    let opt_domain = build_stateless_det_opt_domain(&pk.pk_seed);
    eval_prf_msg_mpc_cut(
        session_id,
        "pos2_stateless_r_rand",
        t,
        quorum_pts,
        &opt_domain,
        mu,
        key_shares,
        vaults,
        party_rngs,
    )
}

/// Sign a message under stateless `Corduroy` / `Baggy` over `Poseidon2Suite` in SPDZ MPC.
///
/// The randomiser `R` is derived under MPC from `SK.prf` and the message digest alone (see
/// [`build_stateless_det_opt_domain`]); there is no randomiser input. Signing the same message
/// again, in any session and with any signing set, yields the same signature.
#[expect(
    clippy::too_many_arguments,
    reason = "One signing session: parameters, public key, message and per-party state"
)]
pub fn sign_stateless_tsw_poseidon2_mpc(
    session_id: [u8; 32],
    params: &PqHashParams,
    pk: &PqPublicKey,
    t: usize,
    msg: &[u8],
    max_grind: u32,
    key_shares: &mut [&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<PqHashSig, Poseidon2MpcError> {
    sign_stateless_tsw_poseidon2_mpc_cached(
        session_id, params, pk, None, t, msg, max_grind, key_shares, vaults, party_rngs,
    )
}

/// [`sign_stateless_tsw_poseidon2_mpc`] with an optional top-subtree leaf cache (same cache rules
/// as [`sign_jorts_poseidon2_mpc_cached`]; rejection happens before any MPC wire opens).
#[expect(
    clippy::too_many_arguments,
    reason = "One signing session: parameters, public key, optional leaf cache, message and per-party state"
)]
pub fn sign_stateless_tsw_poseidon2_mpc_cached(
    session_id: [u8; 32],
    params: &PqHashParams,
    pk: &PqPublicKey,
    cache: Option<&DkgCachedSubtrees>,
    t: usize,
    msg: &[u8],
    max_grind: u32,
    key_shares: &mut [&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<PqHashSig, Poseidon2MpcError> {
    if !params.is_well_formed() || params.stateful {
        return Err(Poseidon2MpcError::InvalidParams);
    }
    validate_top_subtree_cache(params, pk, cache)?;
    let (quorum_pk_seed, quorum_pts) = validate_quorum_slices(t, key_shares, vaults, party_rngs)?;
    validate_enrolled_key_profile(params, pk, &quorum_pk_seed, key_shares)?;
    let mu = th_pre_hash(Poseidon2Suite, &pk.pk_seed, &pk.pk_root, msg);

    let r_rand = eval_stateless_r_rand_mpc(
        &session_id,
        t,
        &quorum_pts,
        pk,
        &mu,
        key_shares,
        vaults,
        party_rngs,
    )?;
    let (leaf_global_idx, fors_idxs) = derive_stateless_leaf_and_fors_indices(
        Poseidon2Suite,
        params,
        &r_rand,
        &pk.pk_seed,
        &pk.pk_root,
        &mu,
    )
    .ok_or(Poseidon2MpcError::InvalidParams)?;

    let sig = sign_hypertree_poseidon2_mpc_core(
        &session_id,
        params,
        pk,
        cache,
        t,
        &quorum_pts,
        &mu,
        r_rand,
        leaf_global_idx,
        Some(&fors_idxs),
        max_grind,
        key_shares,
        vaults,
        party_rngs,
    )?;
    if !verify_pq_hash_sig(Poseidon2Suite, params, pk, msg, &sig) {
        return Err(Poseidon2MpcError::SignatureSelfCheckFailed);
    }
    Ok(sig)
}

impl core::fmt::Display for Poseidon2MpcError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl core::error::Error for Poseidon2MpcError {}
