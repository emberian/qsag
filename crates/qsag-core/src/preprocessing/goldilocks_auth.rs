//! Gilboa OLE, Shamir sharing and extension-field MACs over Goldilocks.

use super::*;

/// LHL-amplified (`320` random OT bits -> `64`-bit `Goldilocks` via post-OT 2-universal hash,
/// `< 2^{-129}` selective-failure advantage) + 24-byte unbiased pad (`< 2^{-192}` bias)
/// pairwise Gilboa OLE over `Goldilocks`:
/// computes $n$-party additive shares `w_i` such that $\sum_i w_i = (\sum_i u_i)(\sum_j v_j) \pmod p$
/// (`ole_pairwise_cross_sum_eq_mul`) with **zero** cleartext reconstruction and **zero** secret OT choice bits!
pub fn pairwise_gilboa_ole_goldilocks(
    ot_mesh: &mut OtMesh,
    u_per_party: &[Vec<Goldilocks>],
    v_per_party: &[Vec<Goldilocks>],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<Vec<Goldilocks>>, PreprocessError> {
    // Bound OT pads and LHL scratch independently of the output count.
    // Every block retains a post-OT coin, drawn only after its correlations.
    const BLOCK: usize = 32;
    let n = ot_mesh.n;
    if n == 0 || u_per_party.len() != n || v_per_party.len() != n || party_rngs.len() != n {
        return Err(PreprocessError::InvalidThreshold { t: 1, n });
    }
    let count = u_per_party[0].len();
    if u_per_party
        .iter()
        .chain(v_per_party)
        .any(|row| row.len() != count)
    {
        return Err(PreprocessError::InvalidThreshold { t: 1, n });
    }
    let mut out = crate::wipe::secret_vecs_with_capacity(n, count);
    for start in (0..count).step_by(BLOCK) {
        let end = (start + BLOCK).min(count);
        let u = SecretBuffer(
            u_per_party
                .iter()
                .map(|row| row[start..end].to_vec())
                .collect::<Vec<_>>(),
        );
        let v = SecretBuffer(
            v_per_party
                .iter()
                .map(|row| row[start..end].to_vec())
                .collect::<Vec<_>>(),
        );
        let block = SecretBuffer(pairwise_gilboa_ole_goldilocks_block(
            ot_mesh, &u, &v, party_rngs,
        )?);
        for (dst, src) in out.iter_mut().zip(block.iter()) {
            dst.extend_from_slice(src);
        }
    }
    Ok(out.into_inner())
}

fn pairwise_gilboa_ole_goldilocks_block(
    ot_mesh: &mut OtMesh,
    u_per_party: &[Vec<Goldilocks>],
    v_per_party: &[Vec<Goldilocks>],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<Vec<Goldilocks>>, PreprocessError> {
    let n = ot_mesh.n;
    if n == 0 || u_per_party.len() != n || v_per_party.len() != n || party_rngs.len() != n {
        return Err(PreprocessError::InvalidThreshold { t: 1, n });
    }
    let count = u_per_party[0].len();
    for p in 0..n {
        if u_per_party[p].len() != count || v_per_party[p].len() != count {
            return Err(PreprocessError::InvalidThreshold { t: 1, n });
        }
    }
    if count == 0 {
        return Ok(vec![Vec::new(); n]);
    }

    let mut w_per_party: Vec<Vec<Goldilocks>> = (0..n)
        .map(|i| {
            (0..count)
                .map(|k| u_per_party[i][k] * v_per_party[i][k])
                .collect()
        })
        .collect();

    // 5 random `u64` words (`320` disposable bits = `64` target + `256` LHL min-entropy buffer) per item!
    const WORDS_PER_ITEM: usize = 5;
    let total_words = WORDS_PER_ITEM * count;
    let mut r_words = SecretBuffer(vec![vec![0u64; total_words]; n]);
    for i in 0..n {
        for w in 0..total_words {
            r_words[i][w] = party_rngs[i].next_u64();
        }
    }

    // `raw_sender_sh[j][i][k][s]` (held by Sender `j`) + `raw_recv_sh[j][i][k][s]` (held by Receiver `i`)
    // == `bit_s(r_words[i][5*k..5*k+5]) * v_per_party[j][k]`!
    let mut raw_sender_sh = SecretBuffer(vec![vec![vec![[Goldilocks::ZERO; 320]; count]; n]; n]);
    let mut raw_recv_sh = SecretBuffer(vec![vec![vec![[Goldilocks::ZERO; 320]; count]; n]; n]);

    for i in 0..n {
        for j in 0..n {
            if i == j {
                continue;
            }
            let (send_pads, recv_pads) =
                ot_mesh.run_correlated_ot_words(j, i, &r_words[i], party_rngs)?;
            for k in 0..count {
                let vj = v_per_party[j][k];
                for w_off in 0..WORDS_PER_ITEM {
                    let rw = black_box(r_words[i][WORDS_PER_ITEM * k + w_off]);
                    for bit in 0..64 {
                        let s_idx = 64 * w_off + bit;
                        let ot_idx = 320 * k + s_idx;
                        let (p0, p1) = &send_pads[ot_idx];
                        let pad0 = Goldilocks::from_bytes24_unbiased(&core::array::from_fn(
                            |array_index| (p0[0..24])[array_index],
                        ));
                        let pad1 = Goldilocks::from_bytes24_unbiased(&core::array::from_fn(
                            |array_index| (p1[0..24])[array_index],
                        ));
                        let m_mask = party_rngs[j].next_goldilocks();
                        raw_sender_sh[j][i][k][s_idx] = m_mask;

                        let ct0 = m_mask.const_neg() + pad0;
                        let ct1 = (vj - m_mask) + pad1;

                        let pad_c = Goldilocks::from_bytes24_unbiased(&core::array::from_fn(
                            |array_index| (recv_pads[ot_idx][0..24])[array_index],
                        ));
                        let choice = ((rw >> bit) & 1) == 1;
                        let mask64 = 0u64.wrapping_sub(black_box(choice as u64));
                        let sel_raw = ct0.to_canonical_u64()
                            ^ (mask64 & (ct0.to_canonical_u64() ^ ct1.to_canonical_u64()));
                        let sel = Goldilocks::from_u64_reduced(sel_raw);
                        raw_recv_sh[j][i][k][s_idx] = sel - pad_c;
                    }
                }
            }
        }
    }

    // Post-OT public-coin 2-universal LHL combiner `g[0..320] ∈ F_p^{320}` (`< 2^{-129}` selective-failure advantage!)
    let sid = ot_mesh.session_id;
    let lhl_coin = run_commit_and_open_coin(
        &sid,
        b"GILBOA_GL_LHL_COMBINE",
        &ot_mesh.transcript_digest(),
        party_rngs,
    )?;
    let mut g_xof = Cshake256Xof::new(b"QSAG.GILBOA.GL.LHL_G/v1");
    g_xof.absorb(&lhl_coin);
    let mut g_weights = [Goldilocks::ZERO; 320];
    #[expect(
        clippy::needless_range_loop,
        reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows"
    )]
    for s in 0..320 {
        let mut b24 = [0u8; 24];
        g_xof.squeeze(&mut b24);
        g_weights[s] = Goldilocks::from_bytes24_unbiased(&b24);
    }

    let mut diffs = SecretBuffer(vec![vec![Goldilocks::ZERO; count]; n]);
    for i in 0..n {
        for k in 0..count {
            let mut u_comb = Goldilocks::ZERO;
            for w_off in 0..WORDS_PER_ITEM {
                let rw = black_box(r_words[i][WORDS_PER_ITEM * k + w_off]);
                for bit in 0..64 {
                    let b_mask = 0u64.wrapping_sub((rw >> bit) & 1);
                    let w_val = Goldilocks::from_u64_reduced(
                        b_mask & g_weights[64 * w_off + bit].to_canonical_u64(),
                    );
                    u_comb += w_val;
                }
            }
            diffs[i][k] = u_per_party[i][k] - u_comb;
        }
        wipe_u64s(&mut r_words[i]);
    }

    for i in 0..n {
        for j in 0..n {
            if i == j {
                continue;
            }
            for k in 0..count {
                let mut s_acc = diffs[i][k] * v_per_party[j][k];
                let mut r_acc = Goldilocks::ZERO;
                for s in 0..320 {
                    let gw = g_weights[s];
                    s_acc += gw * raw_sender_sh[j][i][k][s];
                    r_acc += gw * raw_recv_sh[j][i][k][s];
                }
                w_per_party[j][k] += s_acc;
                w_per_party[i][k] += r_acc;
                wipe_goldilocks(&mut raw_sender_sh[j][i][k]);
                wipe_goldilocks(&mut raw_recv_sh[j][i][k]);
            }
        }
    }
    Ok(w_per_party)
}

pub(super) fn shamir_share_goldilocks(
    t: usize,
    eval_points: &[Goldilocks],
    secret: Goldilocks,
    rng: &mut PartyPrivateRng,
) -> Vec<Goldilocks> {
    let mut coeffs = Vec::with_capacity(t);
    coeffs.push(secret);
    for _ in 1..t {
        coeffs.push(rng.next_goldilocks());
    }
    let out = eval_points
        .iter()
        .map(|&pt| eval_poly_goldilocks(&coeffs, pt))
        .collect();
    wipe_goldilocks(&mut coeffs);
    out
}

pub(super) fn shamir_share_ext2(
    t: usize,
    eval_points: &[Goldilocks],
    secret: GoldilocksExt2,
    rng: &mut PartyPrivateRng,
) -> Vec<GoldilocksExt2> {
    let mut coeffs = Vec::with_capacity(t);
    coeffs.push(secret);
    for _ in 1..t {
        coeffs.push(rng.next_ext2());
    }
    let out = eval_points
        .iter()
        .map(|&pt| eval_poly_ext2_at_base(&coeffs, pt))
        .collect();
    wipe_ext2(&mut coeffs);
    out
}

/// Commit-before-open + degree-`< t` interpolation of `GoldilocksExt2` shares across `eval_points[0..n]`.
pub fn commit_and_open_degree_ext2(
    session_id: &[u8; 32],
    phase: &'static str,
    t: usize,
    eval_points: &[Goldilocks],
    shares: &[GoldilocksExt2],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<GoldilocksExt2, PreprocessError> {
    let n = eval_points.len();
    if t == 0 || t > n || shares.len() != n || party_rngs.len() != n {
        return Err(PreprocessError::InvalidThreshold { t, n });
    }
    validate_all_eval_points_goldilocks(eval_points)?;
    let mut salts = SecretBuffer(Vec::with_capacity(n));
    let mut coms = Vec::with_capacity(n);
    for p in 0..n {
        let mut salt = party_rngs[p].next_bytes32();
        let mut pid = (p as u64).to_be_bytes();
        let mut c0_b = shares[p].c0.to_canonical_u64().to_le_bytes();
        let mut c1_b = shares[p].c1.to_canonical_u64().to_le_bytes();
        let com = cshake256_32_multi_frame(
            b"QSAG.SPDZ.EXT2.DEG.COM/v1",
            &[session_id, phase.as_bytes(), &pid, &c0_b, &c1_b, &salt],
        );
        wipe_bytes(&mut pid);
        wipe_bytes(&mut c0_b);
        wipe_bytes(&mut c1_b);
        secret_vec_push(&mut salts, salt);
        wipe_bytes32(&mut salt);
        coms.push(com);
    }
    for p in 0..n {
        let mut pid = (p as u64).to_be_bytes();
        let mut c0_b = shares[p].c0.to_canonical_u64().to_le_bytes();
        let mut c1_b = shares[p].c1.to_canonical_u64().to_le_bytes();
        let exp = cshake256_32_multi_frame(
            b"QSAG.SPDZ.EXT2.DEG.COM/v1",
            &[session_id, phase.as_bytes(), &pid, &c0_b, &c1_b, &salts[p]],
        );
        wipe_bytes(&mut pid);
        wipe_bytes(&mut c0_b);
        wipe_bytes(&mut c1_b);
        wipe_bytes32(&mut salts[p]);
        if !ct_eq_bytes32(&exp, &coms[p]) {
            return Err(PreprocessError::ShareCommitMismatch { phase, party_id: p });
        }
    }
    open_and_check_degree_ext2(t, eval_points, shares, phase)
}

/// Dealerless generation of consistent degree-`< t` Shamir shares of the global `GoldilocksExt2`
/// SPDZ MAC key $\alpha = \sum_{i=0}^{n-1} \alpha^{(i)}$.
pub fn spdz_setup_alpha_goldilocks(
    session_id: &[u8; 32],
    t: usize,
    eval_points: &[Goldilocks],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<(Vec<GoldilocksExt2>, Vec<GoldilocksExt2>), PreprocessError> {
    let n = eval_points.len();
    if t == 0 || t > n || party_rngs.len() != n {
        return Err(PreprocessError::InvalidThreshold { t, n });
    }
    validate_all_eval_points_goldilocks(eval_points)?;

    let mut alpha_contribs = vec![GoldilocksExt2::ZERO; n];
    let mut alpha_shamir = vec![GoldilocksExt2::ZERO; n];
    let mut beta_shamir = SecretBuffer(vec![GoldilocksExt2::ZERO; n]);

    for i in 0..n {
        let a_i = party_rngs[i].next_ext2();
        let b_i = party_rngs[i].next_ext2();
        alpha_contribs[i] = a_i;
        let a_sh = SecretBuffer(shamir_share_ext2(t, eval_points, a_i, &mut party_rngs[i]));
        let b_sh = SecretBuffer(shamir_share_ext2(t, eval_points, b_i, &mut party_rngs[i]));
        for p in 0..n {
            alpha_shamir[p] += a_sh[p];
            beta_shamir[p] += b_sh[p];
        }
    }

    let coin = run_commit_and_open_coin(session_id, b"SPDZ_ALPHA_GL_DEG", session_id, party_rngs)?;
    let eta = GoldilocksExt2::new(
        Goldilocks::from_u128_reduced(
            u128::from_le_bytes(core::array::from_fn(|array_index| {
                (coin[0..16])[array_index]
            })) | 1,
        ),
        Goldilocks::from_u128_reduced(u128::from_le_bytes(core::array::from_fn(|array_index| {
            (coin[16..32])[array_index]
        }))),
    );
    let comb: SecretBuffer<Vec<GoldilocksExt2>> = SecretBuffer(
        (0..n)
            .map(|p| beta_shamir[p] + eta * alpha_shamir[p])
            .collect(),
    );
    let _ = commit_and_open_degree_ext2(
        session_id,
        "spdz_setup_alpha_goldilocks",
        t,
        eval_points,
        comb.as_slice(),
        party_rngs,
    )?;
    {
        // Beta masks the degree opening. Additionally check the dealt constant
        // against the private contributions without publishing any discrepancy.
        let lambdas = lagrange_weights_zero_goldilocks(&eval_points[..t])
            .ok_or(PreprocessError::DuplicateOrZeroEvalPoint)?;
        let residual = SecretBuffer(
            (0..n)
                .map(|p| {
                    let weighted = if p < t {
                        alpha_shamir[p].mul_base(lambdas[p])
                    } else {
                        GoldilocksExt2::ZERO
                    };
                    weighted - alpha_contribs[p]
                })
                .collect::<Vec<_>>(),
        );
        let w = blind_open_ext2(
            session_id,
            "spdz_alpha_gl_consistency",
            &residual,
            None,
            party_rngs,
        )?;
        if !w.ct_eq(GoldilocksExt2::ZERO) {
            return Err(PreprocessError::MacCheckFailed {
                phase: "spdz_alpha_gl_consistency",
                accused_party: None,
            });
        }
    }
    Ok((alpha_contribs, alpha_shamir))
}

/// Dealerless `Π_MAC` over `Goldilocks` Shamir shares, processed in blocks of at most 32
/// values so the full-vector Toeplitz combiner costs linear work in the batch length.
/// Each block receives a separately framed session, fresh 256-bit tail entropy and its own
/// post-correlation coin. Within a block, the combiner covers `total_items + 4` `u64` words
/// and has exact $p^{-\text{total\_items}}$ collision probability, with `< 2^{-129}`
/// selective-failure advantage. Sender `i` inputs only private `alpha_contribs[i]`.
/// Every block checks degree-`< t` consistency across all parties and $\gamma(x) = \alpha x$
/// with the existing `< 2^{-127}` fold/degree bound. The blinded
/// zero test additionally has false acceptance probability `p^{-2}` for a nonzero residual.
/// Batch bounds sum these per-block terms over `ceil(count / 32)` by the union bound.
#[expect(
    clippy::too_many_arguments,
    reason = "Quorum, value shares, MAC shares and private randomness are separate protocol inputs"
)]
pub fn spdz_authenticate_goldilocks_batch_ext2(
    session_id: &[u8; 32],
    t: usize,
    eval_points: &[Goldilocks],
    ot_mesh: &mut OtMesh,
    alpha_contribs: &[GoldilocksExt2],
    alpha_shamir_shares: &[GoldilocksExt2],
    x_shares_per_party: &[Vec<Goldilocks>],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<Vec<GoldilocksExt2>>, PreprocessError> {
    // Each block retains the full tail entropy and its own post-correlation coin.
    // The overall failure bound is the union bound over ceil(count / BLOCK) blocks.
    const BLOCK: usize = 32;
    let n = eval_points.len();
    if t == 0
        || t > n
        || ot_mesh.n != n
        || alpha_contribs.len() != n
        || alpha_shamir_shares.len() != n
        || x_shares_per_party.len() != n
        || party_rngs.len() != n
    {
        return Err(PreprocessError::InvalidThreshold { t, n });
    }
    validate_all_eval_points_goldilocks(eval_points)?;
    let count = x_shares_per_party[0].len();
    if x_shares_per_party.iter().any(|row| row.len() != count) {
        return Err(PreprocessError::InvalidThreshold { t, n });
    }
    let mut out = crate::wipe::secret_vecs_with_capacity(n, count);
    for start in (0..count).step_by(BLOCK) {
        let end = (start + BLOCK).min(count);
        let block_id = cshake256_32_multi_frame(
            b"QSAG.SPDZ.GL.PIMAC.BLOCK/v1",
            &[
                session_id,
                &(start as u64).to_be_bytes(),
                &(count as u64).to_be_bytes(),
            ],
        );
        let values = SecretBuffer(
            x_shares_per_party
                .iter()
                .map(|row| row[start..end].to_vec())
                .collect::<Vec<_>>(),
        );
        let macs = SecretBuffer(spdz_authenticate_goldilocks_batch_ext2_block(
            &block_id,
            t,
            eval_points,
            ot_mesh,
            alpha_contribs,
            alpha_shamir_shares,
            &values,
            party_rngs,
        )?);
        for (dst, src) in out.iter_mut().zip(macs.iter()) {
            dst.extend_from_slice(src);
        }
    }
    Ok(out.into_inner())
}

#[expect(clippy::too_many_arguments, reason = "Separate protocol inputs")]
fn spdz_authenticate_goldilocks_batch_ext2_block(
    session_id: &[u8; 32],
    t: usize,
    eval_points: &[Goldilocks],
    ot_mesh: &mut OtMesh,
    alpha_contribs: &[GoldilocksExt2],
    alpha_shamir_shares: &[GoldilocksExt2],
    x_shares_per_party: &[Vec<Goldilocks>],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<Vec<GoldilocksExt2>>, PreprocessError> {
    let n = eval_points.len();
    if t == 0
        || t > n
        || ot_mesh.n != n
        || alpha_contribs.len() != n
        || alpha_shamir_shares.len() != n
        || x_shares_per_party.len() != n
        || party_rngs.len() != n
    {
        return Err(PreprocessError::InvalidThreshold { t, n });
    }
    validate_all_eval_points_goldilocks(eval_points)?;
    let count = x_shares_per_party[0].len();
    for x_shares_per_party_p_item in x_shares_per_party[..n].iter().skip(1) {
        if (*x_shares_per_party_p_item).len() != count {
            return Err(PreprocessError::InvalidThreshold { t, n });
        }
    }
    if count == 0 {
        return Ok(vec![Vec::new(); n]);
    }

    let lambdas_t = lagrange_weights_zero_goldilocks(&eval_points[..t])
        .ok_or(PreprocessError::DuplicateOrZeroEvalPoint)?;

    // Sample 3 disposable degree-`< t` random Goldilocks wires:
    // - `r_deg`: one-time pad for full `0..n` degree check of `x_shares_per_party`
    // - `r_chk0, r_chk1`: `GoldilocksExt2` one-time pad for the `Π_MAC` linear check `Z`!
    let mut r_extra_sh = SecretBuffer(vec![[Goldilocks::ZERO; 3]; n]);
    for party_rngs_i_item in party_rngs[..n].iter_mut() {
        for slot in 0..3 {
            let ri = (*party_rngs_i_item).next_goldilocks();
            let s_ri = SecretBuffer(shamir_share_goldilocks(
                t,
                eval_points,
                ri,
                &mut *party_rngs_i_item,
            ));
            for p in 0..n {
                r_extra_sh[p][slot] += s_ri[p];
            }
        }
    }

    let total_items = count + 3;
    // Full-vector 2-universal Toeplitz LHL combiner over `total_items` `u64` words + `4` tail `u64` words (`256` bits)!
    let m_words = total_items + 4;
    let m_bits = 64 * m_words;

    let mut u_target = SecretBuffer(vec![vec![Goldilocks::ZERO; total_items]; t]);
    let mut r_words = SecretBuffer(vec![vec![0u64; m_words]; t]);
    for j in 0..t {
        let lj = lambdas_t[j];
        for k in 0..count {
            u_target[j][k] = lj * x_shares_per_party[j][k];
        }
        for slot in 0..3 {
            u_target[j][count + slot] = lj * r_extra_sh[j][slot];
        }
        for w in 0..m_words {
            r_words[j][w] = party_rngs[j].next_u64();
        }
    }

    // Sender `i in 0..n` inputs ONLY private `alpha_contribs[i]`; Receiver `j in 0..t` inputs random `r_words[j]`
    let mut raw_keys = SecretBuffer(vec![vec![vec![GoldilocksExt2::ZERO; m_bits]; t]; n]);
    let mut raw_macs = SecretBuffer(vec![vec![vec![GoldilocksExt2::ZERO; m_bits]; t]; n]);
    let mut ct_xof = Cshake256Xof::new(b"QSAG.SPDZ.GL.PIMAC.CT/v1");
    ct_xof.absorb(session_id);

    for i in 0..n {
        if i < t {
            let ai = alpha_contribs[i];
            for s in 0..m_bits {
                let bit_val = (r_words[i][s / 64] >> (s % 64)) & 1;
                let mask = party_rngs[i].next_ext2();
                raw_keys[i][i][s] = mask;
                raw_macs[i][i][s] = ai.mul_base(Goldilocks::from_u64_reduced(bit_val)) - mask;
            }
        }
        for j in 0..t {
            if i == j {
                continue;
            }
            let ai = alpha_contribs[i];
            let (send_pads, recv_pads) =
                ot_mesh.run_correlated_ot_words(i, j, &r_words[j], party_rngs)?;
            ct_xof.absorb(&(i as u64).to_be_bytes());
            ct_xof.absorb(&(j as u64).to_be_bytes());
            #[inline]
            fn expand_ot_pad48_to_ext2(pad: &[u8; 48]) -> GoldilocksExt2 {
                GoldilocksExt2::new(
                    Goldilocks::from_bytes24_unbiased(&core::array::from_fn(|array_index| {
                        (pad[0..24])[array_index]
                    })),
                    Goldilocks::from_bytes24_unbiased(&core::array::from_fn(|array_index| {
                        (pad[24..48])[array_index]
                    })),
                )
            }

            for s in 0..m_bits {
                let (p0, p1) = &send_pads[s];
                let pad0 = expand_ot_pad48_to_ext2(p0);
                let pad1 = expand_ot_pad48_to_ext2(p1);

                let mask = party_rngs[i].next_ext2();
                raw_keys[i][j][s] = mask;
                let ct0 = pad0 - mask;
                let ct1 = (ai - mask) + pad1;
                let mut ct_frame = [0u8; 32];
                ct_frame[0..8].copy_from_slice(&ct0.c0.to_canonical_u64().to_be_bytes());
                ct_frame[8..16].copy_from_slice(&ct0.c1.to_canonical_u64().to_be_bytes());
                ct_frame[16..24].copy_from_slice(&ct1.c0.to_canonical_u64().to_be_bytes());
                ct_frame[24..32].copy_from_slice(&ct1.c1.to_canonical_u64().to_be_bytes());
                ct_xof.absorb(&ct_frame);

                let pad_c = expand_ot_pad48_to_ext2(&recv_pads[s]);

                let rj_w = black_box(r_words[j][s / 64]);
                let choice = ((rj_w >> (s % 64)) & 1) == 1;
                let cmask = 0u64.wrapping_sub(black_box(choice as u64));
                let sel_c0 = Goldilocks::from_u64_reduced(
                    ct0.c0.to_canonical_u64()
                        ^ (cmask & (ct0.c0.to_canonical_u64() ^ ct1.c0.to_canonical_u64())),
                );
                let sel_c1 = Goldilocks::from_u64_reduced(
                    ct0.c1.to_canonical_u64()
                        ^ (cmask & (ct0.c1.to_canonical_u64() ^ ct1.c1.to_canonical_u64())),
                );
                raw_macs[i][j][s] = GoldilocksExt2::new(sel_c0, sel_c1) - pad_c;
            }
        }
    }
    ct_xof.absorb(&ot_mesh.transcript_digest());
    let mut ct_digest = [0u8; 32];
    ct_xof.squeeze(&mut ct_digest);

    // Post-OT full-vector 2-universal Toeplitz combiner `H[idx, s] = toeplitz_all[idx + s]`
    // over ALL `idx in 0..total_items` and ALL `s in 0..m_bits`:
    // For ANY non-zero bit difference `\Delta r = r - r' \in \{-1, 0, 1\}^{m_bits} \setminus \{0\}`,
    // let `s* = max { s : \Delta r_s != 0 }`. Conditioned on `toeplitz_all[0 .. idx + s*]`,
    // `(H \cdot \Delta r)[idx]` adds `\pm toeplitz_all[idx + s*]`, which is freshly uniform in `F_p`.
    // By the chain rule across `idx = 0 .. total_items - 1`, `Pr_H[H r == H r'] == p^{-total_items}`
    // unconditionally across the entire `m_bits`-bit input vector (`0` block-diagonal blind spots).
    let lhl_coin =
        run_commit_and_open_coin(session_id, b"SPDZ_GL_PIMAC_LHL", &ct_digest, party_rngs)?;
    let mut h_xof = Cshake256Xof::new(b"QSAG.SPDZ.GL.LHL_H/v2");
    h_xof.absorb(&lhl_coin);

    let mut toeplitz_u64 = vec![0u64; total_items + m_bits];
    for slot in &mut toeplitz_u64 {
        let mut b24 = [0u8; 24];
        h_xof.squeeze(&mut b24);
        *slot = Goldilocks::from_bytes24_unbiased(&b24).to_canonical_u64();
    }

    let mut diff_sum = SecretBuffer(vec![Goldilocks::ZERO; total_items]);
    for j in 0..t {
        for idx in 0..total_items {
            let h_row = &toeplitz_u64[idx..idx + m_bits];
            let mut acc_u128 = 0u128;
            for w in 0..m_words {
                let rw = black_box(r_words[j][w]);
                let h_word = &h_row[64 * w..64 * (w + 1)];
                for (b, &h) in h_word.iter().enumerate() {
                    let m = 0u64.wrapping_sub((rw >> b) & 1);
                    acc_u128 += (m & h) as u128;
                }
            }
            let u_comb = Goldilocks::reduce128(acc_u128);
            diff_sum[idx] += u_target[j][idx] - u_comb;
        }
        wipe_goldilocks(&mut u_target[j]);
        wipe_u64s(&mut r_words[j]);
    }
    drop((u_target, r_words));

    // Pre-sum additive OT shares across `j in 0..t` and `i in 0..n` BEFORE `toeplitz_u64` multiplies!
    let mut sum_raw_c0 = SecretBuffer(vec![vec![0u64; m_bits]; n]);
    let mut sum_raw_c1 = SecretBuffer(vec![vec![0u64; m_bits]; n]);
    for p in 0..n {
        for s in 0..m_bits {
            let mut acc = GoldilocksExt2::ZERO;
            for j in 0..t {
                acc += raw_keys[p][j][s];
            }
            if p < t {
                for raw_macs_i_item in raw_macs[..n].iter() {
                    acc += (*raw_macs_i_item)[p][s];
                }
            }
            sum_raw_c0[p][s] = acc.c0.to_canonical_u64();
            sum_raw_c1[p][s] = acc.c1.to_canonical_u64();
        }
    }
    drop((raw_keys, raw_macs));

    // `2^64 == 2^32 - 1 (mod p)` => `2^128 == (2^32 - 1)^2 (mod p)`.
    let two_pow_64_mod_p = Goldilocks::from_u64_reduced((1u64 << 32) - 1);
    let two_pow_128_mod_p = two_pow_64_mod_p * two_pow_64_mod_p;

    let compute_party_taus = |p: usize| -> Vec<GoldilocksExt2> {
        let ap = alpha_contribs[p];
        let sr0 = &sum_raw_c0[p];
        let sr1 = &sum_raw_c1[p];
        let mut taus_p = vec![GoldilocksExt2::ZERO; total_items];
        for idx in 0..total_items {
            let h_row = &toeplitz_u64[idx..idx + m_bits];
            let mut acc0_lo = 0u128;
            let mut acc0_hi = 0u64;
            let mut acc1_lo = 0u128;
            let mut acc1_hi = 0u64;
            for s in 0..m_bits {
                let h = h_row[s] as u128;
                let (n0, ov0) = acc0_lo.overflowing_add((sr0[s] as u128) * h);
                acc0_lo = n0;
                acc0_hi += ov0 as u64;
                let (n1, ov1) = acc1_lo.overflowing_add((sr1[s] as u128) * h);
                acc1_lo = n1;
                acc1_hi += ov1 as u64;
            }
            let comb_c0 = Goldilocks::reduce128(acc0_lo)
                + Goldilocks::from_u64_reduced(acc0_hi) * two_pow_128_mod_p;
            let comb_c1 = Goldilocks::reduce128(acc1_lo)
                + Goldilocks::from_u64_reduced(acc1_hi) * two_pow_128_mod_p;
            taus_p[idx] = ap.mul_base(diff_sum[idx]) + GoldilocksExt2::new(comb_c0, comb_c1);
        }
        taus_p
    };

    #[cfg(feature = "std")]
    let taus_per_party: SecretBuffer<Vec<Vec<GoldilocksExt2>>> = if total_items >= 64 {
        SecretBuffer(std::thread::scope(|s| {
            let handles: Vec<_> = (0..n)
                .map(|p| s.spawn(move || compute_party_taus(p)))
                .collect();
            // Join every handle before propagating an error: otherwise a second
            // unjoined worker panic would make thread::scope panic on exit.
            let joined = handles.into_iter().map(|h| h.join()).collect::<Vec<_>>();
            joined
                .into_iter()
                .map(|result| {
                    result.map_err(|_| PreprocessError::MacCheckFailed {
                        phase: "spdz_gl_toeplitz_worker",
                        accused_party: None,
                    })
                })
                .collect::<Result<Vec<_>, _>>()
        })?)
    } else {
        SecretBuffer((0..n).map(compute_party_taus).collect())
    };
    #[cfg(not(feature = "std"))]
    let taus_per_party: SecretBuffer<Vec<Vec<GoldilocksExt2>>> =
        SecretBuffer((0..n).map(compute_party_taus).collect());

    drop((sum_raw_c0, sum_raw_c1, diff_sum));

    let mut all_macs = SecretBuffer(vec![vec![GoldilocksExt2::ZERO; total_items]; n]);
    for p in 0..n {
        for idx in 0..total_items {
            let sh = SecretBuffer(shamir_share_ext2(
                t,
                eval_points,
                taus_per_party[p][idx],
                &mut party_rngs[p],
            ));
            for q in 0..n {
                all_macs[q][idx] += sh[q];
            }
        }
    }
    drop(taus_per_party);

    // Batch `Π_MAC` consistency + full `0..n` degree check:
    let chk_coin =
        run_commit_and_open_coin(session_id, b"SPDZ_GL_PIMAC_CHK", &lhl_coin, party_rngs)?;
    let mut chk_xof = Cshake256Xof::new(b"QSAG.SPDZ.GL.PIMAC_W/v1");
    chk_xof.absorb(&chk_coin);

    // 1) Degree `< t` check on `x_shares_per_party` across `0..n` masked by `r_extra_sh[..][0]`
    let mut deg_sh: SecretBuffer<Vec<Goldilocks>> =
        SecretBuffer((0..n).map(|p| r_extra_sh[p][0]).collect());
    #[expect(
        clippy::needless_range_loop,
        reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows"
    )]
    for k in 0..count {
        let mut b24 = [0u8; 24];
        chk_xof.squeeze(&mut b24);
        let w = Goldilocks::from_bytes24_unbiased(&b24);
        for p in 0..n {
            deg_sh[p] += w * x_shares_per_party[p][k];
        }
    }
    let _ =
        open_and_check_degree_goldilocks(t, eval_points, deg_sh.as_slice(), "spdz_gl_words_deg")?;
    drop(deg_sh);

    // 2) Fold all wires (`0..count` + `r_extra_sh[0]`) with random `GoldilocksExt2` weights, masked
    //    over `F_{p^2}` by `R_pad = (r_extra_sh[1], r_extra_sh[2])` (`0` bits leaked!)
    let mut z_sh = SecretBuffer(vec![GoldilocksExt2::ZERO; n]);
    let mut z_mac = SecretBuffer(vec![GoldilocksExt2::ZERO; n]);
    let ext_u = GoldilocksExt2::new(Goldilocks::ZERO, Goldilocks::ONE);
    for p in 0..n {
        z_sh[p] = GoldilocksExt2::new(r_extra_sh[p][1], r_extra_sh[p][2]);
        z_mac[p] = all_macs[p][count + 1] + ext_u * all_macs[p][count + 2];
    }
    {
        let mut b48 = [0u8; 48];
        chk_xof.squeeze(&mut b48);
        let chi0 = GoldilocksExt2::new(
            Goldilocks::from_bytes24_unbiased(&core::array::from_fn(|array_index| {
                (b48[0..24])[array_index]
            })),
            Goldilocks::from_bytes24_unbiased(&core::array::from_fn(|array_index| {
                (b48[24..48])[array_index]
            })),
        );
        for p in 0..n {
            z_sh[p] += chi0.mul_base(r_extra_sh[p][0]);
            z_mac[p] += chi0 * all_macs[p][count];
            wipe_goldilocks(&mut r_extra_sh[p]);
        }
    }
    drop(r_extra_sh);
    for k in 0..count {
        let mut b48 = [0u8; 48];
        chk_xof.squeeze(&mut b48);
        let chi = GoldilocksExt2::new(
            Goldilocks::from_bytes24_unbiased(&core::array::from_fn(|array_index| {
                (b48[0..24])[array_index]
            })),
            Goldilocks::from_bytes24_unbiased(&core::array::from_fn(|array_index| {
                (b48[24..48])[array_index]
            })),
        );
        for p in 0..n {
            z_sh[p] += chi.mul_base(x_shares_per_party[p][k]);
            z_mac[p] += chi * all_macs[p][k];
        }
    }

    let z_open = commit_and_open_degree_ext2(
        session_id,
        "spdz_gl_pimac_z",
        t,
        eval_points,
        z_sh.as_slice(),
        party_rngs,
    )?;
    drop(z_sh);

    let d_sh: SecretBuffer<Vec<GoldilocksExt2>> = SecretBuffer(
        (0..n)
            .map(|p| z_mac[p] - z_open * alpha_shamir_shares[p])
            .collect(),
    );
    drop(z_mac);
    let d_zero = blind_open_degree_ext2(
        session_id,
        "spdz_gl_pimac_d",
        t,
        eval_points,
        &d_sh,
        ot_mesh,
        party_rngs,
    )?;
    drop(d_sh);
    if !d_zero.ct_eq(GoldilocksExt2::ZERO) {
        return Err(PreprocessError::MacCheckFailed {
            phase: "spdz_gl_pimac",
            accused_party: None,
        });
    }

    let mut out_macs = Vec::with_capacity(n);
    for p in 0..n {
        let mut v = Vec::with_capacity(count);
        v.extend_from_slice(&all_macs[p][..count]);
        out_macs.push(v);
    }
    Ok(out_macs)
}

/// Batched dishonest-majority commit-before-open + SPDZ `GoldilocksExt2` `MacCheck` over any quorum.
#[expect(
    clippy::too_many_arguments,
    reason = "Quorum, value shares, MAC shares and private randomness are separate protocol inputs"
)]
pub fn commit_and_open_spdz_goldilocks_batch_quorum(
    session_id: &[u8; 32],
    phase: &'static str,
    t: usize,
    quorum_eval_points: &[Goldilocks],
    batch_shares: &[Vec<Goldilocks>],
    batch_macs: &[Vec<GoldilocksExt2>],
    alpha_shares: &[GoldilocksExt2],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<Goldilocks>, PreprocessError> {
    commit_and_open_spdz_goldilocks_batch_quorum_with_mesh(
        session_id,
        phase,
        t,
        quorum_eval_points,
        batch_shares,
        batch_macs,
        alpha_shares,
        party_rngs,
        None,
    )
}

#[expect(
    clippy::too_many_arguments,
    reason = "Reuse ceremony OT channels without changing the public opening API"
)]
pub fn commit_and_open_spdz_goldilocks_batch_quorum_with_mesh(
    session_id: &[u8; 32],
    phase: &'static str,
    t: usize,
    quorum_eval_points: &[Goldilocks],
    batch_shares: &[Vec<Goldilocks>],
    batch_macs: &[Vec<GoldilocksExt2>],
    alpha_shares: &[GoldilocksExt2],
    party_rngs: &mut [PartyPrivateRng],
    mesh: Option<&mut OtMesh>,
) -> Result<Vec<Goldilocks>, PreprocessError> {
    let m = quorum_eval_points.len();
    if t == 0
        || m < t
        || batch_shares.len() != m
        || batch_macs.len() != m
        || alpha_shares.len() != m
        || party_rngs.len() != m
    {
        return Err(PreprocessError::InvalidThreshold { t, n: m });
    }
    let batch_len = batch_shares[0].len();
    for p in 0..m {
        if batch_shares[p].len() != batch_len || batch_macs[p].len() != batch_len {
            return Err(PreprocessError::InvalidThreshold { t, n: m });
        }
    }
    if batch_len == 0 {
        return Ok(Vec::new());
    }
    validate_all_eval_points_goldilocks(quorum_eval_points)?;

    let mut salts = SecretBuffer(Vec::with_capacity(m));
    let mut coms = Vec::with_capacity(m);
    for p in 0..m {
        let mut salt = party_rngs[p].next_bytes32();
        let mut xof = Cshake256Xof::new(b"QSAG.SPDZ.GL.BATCH.OPEN.COM/v1");
        xof.absorb(session_id);
        xof.absorb(&(phase.len() as u64).to_be_bytes());
        xof.absorb(phase.as_bytes());
        xof.absorb(&(p as u64).to_be_bytes());
        xof.absorb(&salt);
        #[expect(
            clippy::needless_range_loop,
            reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows"
        )]
        for w in 0..batch_len {
            let mut b8 = batch_shares[p][w].to_canonical_u64().to_le_bytes();
            xof.absorb(&b8);
            wipe_bytes(&mut b8);
        }
        let mut com = [0u8; 32];
        xof.squeeze(&mut com);
        secret_vec_push(&mut salts, salt);
        wipe_bytes32(&mut salt);
        coms.push(com);
    }
    for p in 0..m {
        let mut xof = Cshake256Xof::new(b"QSAG.SPDZ.GL.BATCH.OPEN.COM/v1");
        xof.absorb(session_id);
        xof.absorb(&(phase.len() as u64).to_be_bytes());
        xof.absorb(phase.as_bytes());
        xof.absorb(&(p as u64).to_be_bytes());
        xof.absorb(&salts[p]);
        #[expect(
            clippy::needless_range_loop,
            reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows"
        )]
        for w in 0..batch_len {
            let mut b8 = batch_shares[p][w].to_canonical_u64().to_le_bytes();
            xof.absorb(&b8);
            wipe_bytes(&mut b8);
        }
        let mut exp = [0u8; 32];
        xof.squeeze(&mut exp);
        wipe_bytes32(&mut salts[p]);
        if !ct_eq_bytes32(&exp, &coms[p]) {
            return Err(PreprocessError::ShareCommitMismatch { phase, party_id: p });
        }
    }
    drop(salts);

    let mut opened = Vec::with_capacity(batch_len);
    let mut dig_xof = Cshake256Xof::new(b"QSAG.SPDZ.GL.BATCH.DIG/v1");
    let mut single_sh = SecretBuffer(vec![Goldilocks::ZERO; m]);
    let opening_tables = GoldilocksOpeningTables::new(t, quorum_eval_points)?;
    #[expect(
        clippy::needless_range_loop,
        reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows"
    )]
    for w in 0..batch_len {
        for p in 0..m {
            single_sh[p] = batch_shares[p][w];
        }
        let sec = opening_tables.open(single_sh.as_slice(), phase)?;
        dig_xof.absorb(&sec.to_canonical_u64().to_le_bytes());
        opened.push(sec);
    }
    drop(single_sh);
    let mut open_digest = [0u8; 32];
    dig_xof.squeeze(&mut open_digest);

    let fold_coin =
        run_commit_and_open_coin(session_id, phase.as_bytes(), &open_digest, party_rngs)?;
    let mut chi_xof = Cshake256Xof::new(b"QSAG.SPDZ.GL.BATCH.CHIS/v1");
    chi_xof.absorb(&fold_coin);

    let mut x_folded = GoldilocksExt2::ZERO;
    let mut m_folded = SecretBuffer(vec![GoldilocksExt2::ZERO; t]);
    for w in 0..batch_len {
        let mut b48 = [0u8; 48];
        chi_xof.squeeze(&mut b48);
        let chi = GoldilocksExt2::new(
            Goldilocks::from_bytes24_unbiased(&core::array::from_fn(|array_index| {
                (b48[0..24])[array_index]
            })),
            Goldilocks::from_bytes24_unbiased(&core::array::from_fn(|array_index| {
                (b48[24..48])[array_index]
            })),
        );
        x_folded += chi.mul_base(opened[w]);
        for q in 0..t {
            m_folded[q] += chi * batch_macs[q][w];
        }
    }

    let lambdas_0 = lagrange_weights_zero_goldilocks(&quorum_eval_points[..t])
        .ok_or(PreprocessError::DuplicateOrZeroEvalPoint)?;
    let additive = SecretBuffer(
        (0..m)
            .map(|p| {
                if p < t {
                    (m_folded[p] - alpha_shares[p] * x_folded).mul_base(lambdas_0[p])
                } else {
                    GoldilocksExt2::ZERO
                }
            })
            .collect::<Vec<_>>(),
    );
    let w = blind_open_ext2(session_id, phase, &additive, mesh, party_rngs)?;
    if !w.ct_eq(GoldilocksExt2::ZERO) {
        return Err(PreprocessError::MacCheckFailed {
            phase,
            accused_party: None,
        });
    }
    Ok(opened)
}
