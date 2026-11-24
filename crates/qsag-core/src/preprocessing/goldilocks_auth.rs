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
