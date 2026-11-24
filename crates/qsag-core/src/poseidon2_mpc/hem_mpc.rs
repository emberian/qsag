use super::*;

#[inline]
fn pack_secret_bytes32_to_limbs56_auth(bytes32: &[AuthGlWire; 32]) -> [AuthGlWire; 5] {
    let mut out = [AuthGlWire::ZERO; 5];
    for i in 0..4 {
        let mut acc = AuthGlWire::ZERO;
        for b in 0..7 {
            let weight = Goldilocks::from_u64_reduced(1u64 << (8 * b));
            acc = acc.add(bytes32[7 * i + b].scale(weight));
        }
        out[i] = acc;
    }
    let mut acc4 = AuthGlWire::ZERO;
    for b in 0..4 {
        let weight = Goldilocks::from_u64_reduced(1u64 << (8 * b));
        acc4 = acc4.add(bytes32[28 + b].scale(weight));
    }
    out[4] = acc4;
    out
}

type ExpandedHemSecretDigestPair = (Vec<[AuthGlWire; 4]>, Vec<[AuthGlWire; 4]>);

/// Expand `(sk_seed_bytes, sk_prf_bytes)` into `(sk_seed, sk_prf)` native `[AuthGlWire; 4]` shares
/// across the quorum in 1 parallel `eval_spdz_poseidon2_perm12_batch` (`2` perms, `0` A2B!).
fn expand_hem_secret_digests_mpc(
    t: usize,
    quorum_pts: &[Goldilocks],
    pk_seed: HemDigest4,
    key_shares: &[&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    pending: &mut SpdzGoldilocksPendingChecks,
) -> Result<ExpandedHemSecretDigestPair, PreprocessError> {
    let m = quorum_pts.len();
    let mut states = secret_vecs_with_capacity(m, 2);
    let mut seed_low4 = SecretBuffer(vec![[AuthGlWire::ZERO; 4]; m]);
    let mut prf_low4 = SecretBuffer(vec![[AuthGlWire::ZERO; 4]; m]);

    for p in 0..m {
        let alpha_p = vaults[p].mac_alpha_share;
        let sw = SecretBuffer(key_seed_wires(key_shares[p]));
        let pw = SecretBuffer(key_prf_wires(key_shares[p]));
        let ls = SecretBuffer(pack_secret_bytes32_to_limbs56_auth(&sw));
        let lp = SecretBuffer(pack_secret_bytes32_to_limbs56_auth(&pw));
        seed_low4[p] = [ls[0], ls[1], ls[2], ls[3]];
        prf_low4[p] = [lp[0], lp[1], lp[2], lp[3]];

        let pks: [AuthGlWire; 4] =
            core::array::from_fn(|i| AuthGlWire::public_const(pk_seed[i], alpha_p));
        let iv =
            AuthGlWire::public_const(Goldilocks::from_u64_reduced(POSEIDON2_CONST_IV), alpha_p);
        let dom_s = AuthGlWire::public_const(
            Goldilocks::from_u64_reduced(HEM_DOMAIN_SK_SEED_EXPAND),
            alpha_p,
        );
        let dom_p = AuthGlWire::public_const(
            Goldilocks::from_u64_reduced(HEM_DOMAIN_SK_PRF_EXPAND),
            alpha_p,
        );

        secret_vec_push(
            &mut states[p],
            [
                ls[0],
                ls[1],
                ls[2],
                ls[3],
                ls[4],
                pks[0],
                pks[1],
                pks[2],
                pks[3],
                dom_s,
                AuthGlWire::ZERO,
                iv,
            ],
        );
        secret_vec_push(
            &mut states[p],
            [
                lp[0],
                lp[1],
                lp[2],
                lp[3],
                lp[4],
                pks[0],
                pks[1],
                pks[2],
                pks[3],
                dom_p,
                AuthGlWire::ZERO,
                iv,
            ],
        );
    }

    eval_spdz_poseidon2_perm12_batch(t, quorum_pts, &mut states, vaults, pending)?;

    let mut sk_seed_out = SecretBuffer(vec![[AuthGlWire::ZERO; 4]; m]);
    let mut sk_prf_out = SecretBuffer(vec![[AuthGlWire::ZERO; 4]; m]);
    for p in 0..m {
        for i in 0..4 {
            sk_seed_out[p][i] = states[p][0][i].add(seed_low4[p][i]);
            sk_prf_out[p][i] = states[p][1][i].add(prf_low4[p][i]);
        }
    }
    Ok((
        core::mem::take(&mut sk_seed_out.0),
        core::mem::take(&mut sk_prf_out.0),
    ))
}

/// Evaluate a batch of native `[AuthGlWire; 4]` Jive/feed-forward compressions
/// `poseidon2_compress12_ff(in0_secret, pk_seed_public, tweak_public)` in SPDZ (`0` A2B!).
fn eval_spdz_hem_compress12_ff_batch(
    t: usize,
    quorum_pts: &[Goldilocks],
    in0_per_party: &[Vec<[AuthGlWire; 4]>],
    pk_seed: HemDigest4,
    tweaks: &[HemDigest4],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    pending: &mut SpdzGoldilocksPendingChecks,
) -> Result<Vec<Vec<[AuthGlWire; 4]>>, PreprocessError> {
    let m = quorum_pts.len();
    let batch = tweaks.len();
    if batch == 0 {
        return Ok(vec![Vec::new(); m]);
    }
    let mut states = secret_vecs_with_capacity(m, batch);
    for p in 0..m {
        let alpha_p = vaults[p].mac_alpha_share;
        let pks: [AuthGlWire; 4] =
            core::array::from_fn(|i| AuthGlWire::public_const(pk_seed[i], alpha_p));
        for (k, tw) in tweaks.iter().enumerate() {
            let x = in0_per_party[p][k];
            let tw_w: [AuthGlWire; 4] =
                core::array::from_fn(|i| AuthGlWire::public_const(tw[i], alpha_p));
            secret_vec_push(
                &mut states[p],
                [
                    x[0], x[1], x[2], x[3], pks[0], pks[1], pks[2], pks[3], tw_w[0], tw_w[1],
                    tw_w[2], tw_w[3],
                ],
            );
        }
    }

    eval_spdz_poseidon2_perm12_batch(t, quorum_pts, &mut states, vaults, pending)?;

    let mut out = secret_vecs_with_capacity(m, batch);
    for p in 0..m {
        for k in 0..batch {
            let x = in0_per_party[p][k];
            secret_vec_push(
                &mut out[p],
                [
                    states[p][k][0].add(x[0]).add(AuthGlWire::public_const(
                        pk_seed[0] * Goldilocks::TWO
                            + tweaks[k][0] * Goldilocks::from_u64_reduced(4),
                        vaults[p].mac_alpha_share,
                    )),
                    states[p][k][1].add(x[1]).add(AuthGlWire::public_const(
                        pk_seed[1] * Goldilocks::TWO
                            + tweaks[k][1] * Goldilocks::from_u64_reduced(4),
                        vaults[p].mac_alpha_share,
                    )),
                    states[p][k][2].add(x[2]).add(AuthGlWire::public_const(
                        pk_seed[2] * Goldilocks::TWO
                            + tweaks[k][2] * Goldilocks::from_u64_reduced(4),
                        vaults[p].mac_alpha_share,
                    )),
                    states[p][k][3].add(x[3]).add(AuthGlWire::public_const(
                        pk_seed[3] * Goldilocks::TWO
                            + tweaks[k][3] * Goldilocks::from_u64_reduced(4),
                        vaults[p].mac_alpha_share,
                    )),
                ],
            );
        }
    }
    Ok(core::mem::take(&mut out.0))
}

/// Strictly verify ALL queued intermediate SPDZ wires AND open a batch of cut-boundary native
/// `HemDigest4` (`[Goldilocks; 4]`) digests via committed zero-masked `GoldilocksExt2` `MacCheck`.
#[expect(
    clippy::too_many_arguments,
    reason = "Two-stage cut barrier binds session, phase, quorum, cut digests, pending checks and party state"
)]
fn flush_verify_and_open_hem_digests4(
    session_id: &[u8; 32],
    phase: &'static str,
    t: usize,
    quorum_pts: &[Goldilocks],
    cut_digests_per_party: &[Vec<[AuthGlWire; 4]>],
    pending: &mut SpdzGoldilocksPendingChecks,
    key_shares: &mut [&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<HemDigest4>, Poseidon2MpcError> {
    flush_verify_and_open_hem_digests4_with_mesh(
        session_id,
        phase,
        t,
        quorum_pts,
        cut_digests_per_party,
        pending,
        key_shares,
        vaults,
        party_rngs,
        None,
    )
}

#[expect(
    clippy::too_many_arguments,
    reason = "Two-stage cut barrier binds session, phase, quorum, cut digests, pending checks, party state and optional retained OT mesh"
)]
fn flush_verify_and_open_hem_digests4_with_mesh(
    session_id: &[u8; 32],
    phase: &'static str,
    t: usize,
    quorum_pts: &[Goldilocks],
    cut_digests_per_party: &[Vec<[AuthGlWire; 4]>],
    pending: &mut SpdzGoldilocksPendingChecks,
    key_shares: &mut [&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    party_rngs: &mut [PartyPrivateRng],
    mut mesh: Option<&mut OtMesh>,
) -> Result<Vec<HemDigest4>, Poseidon2MpcError> {
    let m = quorum_pts.len();
    let num_digests = cut_digests_per_party[0].len();
    let alpha = SecretBuffer(vaults.iter().map(|v| v.mac_alpha_share).collect::<Vec<_>>());

    let intermediate = commit_and_open_spdz_goldilocks_batch_quorum_with_mesh(
        session_id,
        "hem_pre_cut_intermediate_mac",
        t,
        quorum_pts,
        &pending.shares_per_party,
        &pending.macs_per_party,
        &alpha,
        party_rngs,
        mesh.as_deref_mut(),
    );
    pending.clear_and_wipe();
    match intermediate {
        Ok(mut values) => wipe_goldilocks(&mut values),
        Err(e) => {
            poison_all_on_abort(key_shares, vaults);
            return Err(Poseidon2MpcError::Preprocess(e));
        }
    }

    let total_wires = 4 * num_digests;
    let mut all_sh = secret_vecs_with_capacity(m, total_wires);
    let mut all_mac = secret_vecs_with_capacity(m, total_wires);
    for p in 0..m {
        for st in &cut_digests_per_party[p] {
            for w in st {
                secret_vec_push(&mut all_sh[p], w.val);
                secret_vec_push(&mut all_mac[p], w.mac);
            }
        }
    }

    let opened_res = commit_and_open_spdz_goldilocks_batch_quorum_with_mesh(
        session_id, phase, t, quorum_pts, &all_sh, &all_mac, &alpha, party_rngs, mesh,
    );
    drop(all_sh);
    drop(all_mac);
    drop(alpha);

    let opened = SecretBuffer(match opened_res {
        Ok(v) => v,
        Err(e) => {
            poison_all_on_abort(key_shares, vaults);
            return Err(Poseidon2MpcError::Preprocess(e));
        }
    });

    let mut out = Vec::with_capacity(num_digests);
    for s in 0..num_digests {
        out.push([
            opened[4 * s],
            opened[4 * s + 1],
            opened[4 * s + 2],
            opened[4 * s + 3],
        ]);
    }
    Ok(out)
}

/// Evaluate a batch of `(kp_idx, chain_idx, steps)` targets in native `[Goldilocks; 4]` SPDZ
/// (`0` intermediate A2B conversions!) starting from already-expanded `sk_seed_per_party`.
fn eval_hem_wots_chains_native_spdz(
    t: usize,
    quorum_pts: &[Goldilocks],
    pk_seed: HemDigest4,
    sk_seed_per_party: &[[AuthGlWire; 4]],
    targets: &[(u32, u32, usize)],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    pending: &mut SpdzGoldilocksPendingChecks,
) -> Result<Vec<Vec<[AuthGlWire; 4]>>, PreprocessError> {
    let m = quorum_pts.len();
    let count = targets.len();
    if count == 0 {
        return Ok(vec![Vec::new(); m]);
    }

    let mut base_in = secret_vecs_with_capacity(m, count);
    for p in 0..m {
        for _ in 0..count {
            secret_vec_push(&mut base_in[p], sk_seed_per_party[p]);
        }
    }
    let mut base_tweaks = Vec::with_capacity(count);
    for &(kp_idx, chain_idx, _) in targets {
        base_tweaks.push([
            Goldilocks::from_u64_reduced(HEM_DOMAIN_PRF_WOTS),
            hem_pack_wots_addr_limb(0, kp_idx, chain_idx, 0),
            Goldilocks::ZERO,
            Goldilocks::ZERO,
        ]);
    }
    let mut cur_states = SecretBuffer(eval_spdz_hem_compress12_ff_batch(
        t,
        quorum_pts,
        &base_in,
        pk_seed,
        &base_tweaks,
        vaults,
        pending,
    )?);

    let max_steps = targets.iter().map(|x| x.2).max().unwrap_or(0);
    for step in 0..max_steps {
        let active: Vec<usize> = (0..count).filter(|&i| step < targets[i].2).collect();
        let mut active_in = secret_vecs_with_capacity(m, active.len());
        for p in 0..m {
            for &i in &active {
                secret_vec_push(&mut active_in[p], cur_states[p][i]);
            }
        }
        let mut step_tweaks = Vec::with_capacity(active.len());
        for &i in &active {
            let (kp_idx, chain_idx, _) = targets[i];
            step_tweaks.push([
                Goldilocks::from_u64_reduced(HEM_DOMAIN_WOTS_STEP),
                hem_pack_wots_addr_limb(0, kp_idx, chain_idx, step as u32),
                Goldilocks::ZERO,
                Goldilocks::ZERO,
            ]);
        }
        let next_st = SecretBuffer(eval_spdz_hem_compress12_ff_batch(
            t,
            quorum_pts,
            &active_in,
            pk_seed,
            &step_tweaks,
            vaults,
            pending,
        )?);
        for p in 0..m {
            for (slot, &i) in active.iter().enumerate() {
                cur_states[p][i] = next_st[p][slot];
            }
        }
    }

    Ok(core::mem::take(&mut cur_states.0))
}

/// Derive a [`HemJortsCachedTree`] in the clear from `(dkg_pk_seed, sk_seed_bytes, sk_prf_bytes)`
/// for reference comparison in tests and local custody staging.
pub fn derive_hem_jorts_cached_tree_clear(
    dkg_pk_seed: [u8; 32],
    sk_seed_bytes: &[u8; 32],
    sk_prf_bytes: &[u8; 32],
    active_leaves: usize,
) -> Result<HemJortsCachedTree, Poseidon2MpcError> {
    if active_leaves == 0 || active_leaves > HEM_JORTS_MAX_LEAVES {
        return Err(Poseidon2MpcError::InvalidParams);
    }
    let pk_seed = hem_pk_seed_from_bytes32(&dkg_pk_seed);
    let mut sk_seed =
        hem_expand_secret_bytes32_clear(sk_seed_bytes, pk_seed, HEM_DOMAIN_SK_SEED_EXPAND);
    let mut sk_prf =
        hem_expand_secret_bytes32_clear(sk_prf_bytes, pk_seed, HEM_DOMAIN_SK_PRF_EXPAND);
    let prf_check = hem_prf_check_digest_clear(sk_prf, pk_seed);

    let mut leaves = Vec::with_capacity(HEM_JORTS_MAX_LEAVES);
    let mut leaf0_endpoints = Vec::with_capacity(HEM_WOTS_CHAINS);
    for kp in 0..active_leaves {
        let mut endpoints = [[Goldilocks::ZERO; 4]; HEM_WOTS_CHAINS];
        for (r, ep) in endpoints.iter_mut().enumerate().take(HEM_WOTS_CHAINS) {
            let mut cur = hem_wots_base_secret_clear(sk_seed, pk_seed, 0, 0, kp as u32, r as u32);
            for step in 0..(HEM_WOTS_MAX_STEP as u32) {
                cur = hem_wots_step_hash_injective(pk_seed, cur, 0, 0, kp as u32, r as u32, step);
            }
            *ep = cur;
            wipe_goldilocks(&mut cur);
        }
        if kp == 0 {
            leaf0_endpoints.extend_from_slice(&endpoints);
        }
        leaves.push(hem_compress_wots_endpoints_sponge(
            pk_seed, 0, 0, kp as u32, &endpoints,
        ));
    }
    for kp in active_leaves..HEM_JORTS_MAX_LEAVES {
        leaves.push(hem_unassigned_leaf_digest(pk_seed, kp as u32));
    }
    wipe_goldilocks(&mut sk_seed);
    wipe_goldilocks(&mut sk_prf);

    let pk_root =
        hem_merkle_root_from_leaves(pk_seed, &leaves).ok_or(Poseidon2MpcError::InvalidParams)?;
    Ok(HemJortsCachedTree {
        dkg_pk_seed,
        pk: HemJortsPublicKey { pk_seed, pk_root },
        active_leaves,
        leaves,
        leaf0_endpoints,
        prf_check,
    })
}

/// Build a `Hem`-aggregatable `JortsPoseidon2` public key & height-6 leaf cache in SPDZ MPC with
/// `active_leaves in 1..=64` active `WOTS+C` leaves and domain-separated unassigned leaves above it.
pub fn build_distributed_hem_jorts_key_mpc_with_active_leaves(
    session_id: [u8; 32],
    active_leaves: usize,
    t: usize,
    key_shares: &mut [&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<HemJortsCachedTree, Poseidon2MpcError> {
    if active_leaves == 0 || active_leaves > HEM_JORTS_MAX_LEAVES {
        return Err(Poseidon2MpcError::InvalidParams);
    }
    let (dkg_pk_seed, quorum_pts) = validate_quorum_slices(t, key_shares, vaults, party_rngs)?;
    let pk_seed = hem_pk_seed_from_bytes32(&dkg_pk_seed);
    let m = quorum_pts.len();
    let mut pending = SpdzGoldilocksPendingChecks::new(m);

    let (sk_seed_p, sk_prf_p) = match expand_hem_secret_digests_mpc(
        t,
        &quorum_pts,
        pk_seed,
        key_shares,
        vaults,
        &mut pending,
    ) {
        Ok(pair) => (SecretBuffer(pair.0), SecretBuffer(pair.1)),
        Err(e) => {
            poison_all_on_abort(key_shares, vaults);
            return Err(Poseidon2MpcError::Preprocess(e));
        }
    };

    let prf_in = SecretBuffer((0..m).map(|p| vec![sk_prf_p[p]]).collect::<Vec<_>>());
    let prf_tweak = [[
        Goldilocks::from_u64_reduced(HEM_DOMAIN_PRF_CHECK),
        Goldilocks::ZERO,
        Goldilocks::ZERO,
        Goldilocks::from_u64_reduced(POSEIDON2_CONST_IV),
    ]];
    let prf_chk_p = SecretBuffer(
        match eval_spdz_hem_compress12_ff_batch(
            t,
            &quorum_pts,
            &prf_in,
            pk_seed,
            &prf_tweak,
            vaults,
            &mut pending,
        ) {
            Ok(v) => v,
            Err(e) => {
                poison_all_on_abort(key_shares, vaults);
                return Err(Poseidon2MpcError::Preprocess(e));
            }
        },
    );

    let mut targets = Vec::with_capacity(active_leaves * HEM_WOTS_CHAINS);
    for kp in 0..active_leaves {
        for r in 0..HEM_WOTS_CHAINS {
            targets.push((kp as u32, r as u32, HEM_WOTS_MAX_STEP));
        }
    }
    let mut cut_states = SecretBuffer(
        match eval_hem_wots_chains_native_spdz(
            t,
            &quorum_pts,
            pk_seed,
            &sk_seed_p,
            &targets,
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
        secret_vec_push(&mut cut_states[p], prf_chk_p[p][0]);
    }

    let opened = flush_verify_and_open_hem_digests4(
        &session_id,
        "hem_keygen_endpoints_and_prf",
        t,
        &quorum_pts,
        &cut_states,
        &mut pending,
        key_shares,
        vaults,
        party_rngs,
    )?;

    let prf_check = opened[active_leaves * HEM_WOTS_CHAINS];
    let mut leaves = Vec::with_capacity(HEM_JORTS_MAX_LEAVES);
    let mut leaf0_endpoints = Vec::with_capacity(HEM_WOTS_CHAINS);
    for kp in 0..active_leaves {
        let base = kp * HEM_WOTS_CHAINS;
        let endpoints: [HemDigest4; HEM_WOTS_CHAINS] = core::array::from_fn(|r| opened[base + r]);
        if kp == 0 {
            leaf0_endpoints.extend_from_slice(&endpoints);
        }
        leaves.push(hem_compress_wots_endpoints_sponge(
            pk_seed, 0, 0, kp as u32, &endpoints,
        ));
    }
    for kp in active_leaves..HEM_JORTS_MAX_LEAVES {
        leaves.push(hem_unassigned_leaf_digest(pk_seed, kp as u32));
    }

    let pk_root =
        hem_merkle_root_from_leaves(pk_seed, &leaves).ok_or(Poseidon2MpcError::InvalidParams)?;
    let pk = HemJortsPublicKey { pk_seed, pk_root };
    for ks in key_shares.iter_mut() {
        ks.enroll_hem_key_profile(pk, prf_check)?;
    }

    Ok(HemJortsCachedTree {
        dkg_pk_seed,
        pk,
        active_leaves,
        leaves,
        leaf0_endpoints,
        prf_check,
    })
}

/// Authenticate reshared `(t', n')` SPDZ key shares against an existing [`HemJortsCachedTree`]
/// without reconstructing `SK.seed` or `SK.prf`: first checks `cache.verify_consistency()` (which
/// Merkle-binds `cache.leaf0_endpoints[0]` to `cache.pk.pk_root`), then recomputes
/// `leaf0_endpoints[0]` and `prf_check` in SPDZ MPC (`7` permutations = `798` `pow7` tuples),
/// verifies both match `cache`, and enrolls `(cache.pk, cache.prf_check)` on every share.
