//! Shamir sharing and two-lane SPDZ authentication over the binary tower.

use super::*;

/// Evaluate a `Tower128` polynomial at `Tower128::embed_gf256(x)`.
#[inline]
fn eval_poly_tower128(coeffs: &[Tower128], x: TowerGf256) -> Tower128 {
    let mut acc = Tower128::ZERO;
    for &c in coeffs.iter().rev() {
        acc = acc.mul_gf256(x).add(c);
    }
    acc
}

/// Share a `Tower128` secret at degree `< t` across `eval_points[0..n]`.
#[inline]
pub(super) fn shamir_share_tower128(
    t: usize,
    eval_points: &[TowerGf256],
    secret: Tower128,
    rng: &mut PartyPrivateRng,
) -> Vec<Tower128> {
    let mut coeffs = Vec::with_capacity(t);
    coeffs.push(secret);
    for _ in 1..t {
        coeffs.push(rng.next_tower128());
    }
    let out: Vec<Tower128> = eval_points
        .iter()
        .map(|&pt| eval_poly_tower128(&coeffs, pt))
        .collect();
    wipe_tower128(&mut coeffs);
    out
}

/// Commit-before-open + degree-`< t` interpolation of `Tower128` shares across `eval_points[0..n]`.
pub fn commit_and_open_degree_tower128(
    session_id: &[u8; 32],
    phase: &'static str,
    t: usize,
    eval_points: &[TowerGf256],
    shares: &[Tower128],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Tower128, PreprocessError> {
    let n = eval_points.len();
    if t == 0 || t > n || shares.len() != n || party_rngs.len() != n {
        return Err(PreprocessError::InvalidThreshold { t, n });
    }
    validate_all_eval_points_gf256(eval_points)?;
    let mut salts = Vec::with_capacity(n);
    let mut coms = Vec::with_capacity(n);
    for p in 0..n {
        let salt = party_rngs[p].next_bytes32();
        let pid = (p as u64).to_be_bytes();
        let vb = shares[p].0.to_le_bytes();
        let com = cshake256_32_multi_frame(
            b"QSAG.SPDZ.T128.OPEN.COM/v1",
            &[session_id, phase.as_bytes(), &pid, &vb, &salt],
        );
        salts.push(salt);
        coms.push(com);
    }
    for p in 0..n {
        let pid = (p as u64).to_be_bytes();
        let vb = shares[p].0.to_le_bytes();
        let exp = cshake256_32_multi_frame(
            b"QSAG.SPDZ.T128.OPEN.COM/v1",
            &[session_id, phase.as_bytes(), &pid, &vb, &salts[p]],
        );
        wipe_bytes32(&mut salts[p]);
        if !ct_eq_bytes32(&exp, &coms[p]) {
            return Err(PreprocessError::ShareCommitMismatch { phase, party_id: p });
        }
    }
    let lambdas_0 = lagrange_weights_zero_gf256(&eval_points[..t])
        .ok_or(PreprocessError::DuplicateOrZeroEvalPoint)?;
    let mut secret = Tower128::ZERO;
    for q in 0..t {
        secret = secret.add(shares[q].mul_gf256(lambdas_0[q]));
    }
    for m in t..n {
        let xm = eval_points[m];
        let mut expected = Tower128::ZERO;
        for i in 0..t {
            let mut num = TowerGf256::ONE;
            let mut den = TowerGf256::ONE;
            for j in 0..t {
                if i == j {
                    continue;
                }
                num = num.mul(xm.add(eval_points[j]));
                den = den.mul(eval_points[i].add(eval_points[j]));
            }
            let li = num.mul(den.inv().ok_or(PreprocessError::DuplicateOrZeroEvalPoint)?);
            expected = expected.add(shares[i].mul_gf256(li));
        }
        if !expected.ct_eq(shares[m]) {
            return Err(PreprocessError::DegreeCheckFailed { phase });
        }
    }
    Ok(secret)
}

/// Dealerless generation of consistent degree-`< t` Shamir shares of the global 2-lane `Tower128`
/// SPDZ MAC key $\alpha = \bigoplus_{i=0}^{n-1} \alpha^{(i)}$.
///
/// Returns `(alpha_contribs_per_sender, alpha_shamir_shares_per_party)` after verifying via a
/// random mask polynomial that every party dealt a consistent degree-`< t` polynomial across `0..n`.
pub fn spdz_setup_alpha_gf256(
    session_id: &[u8; 32],
    t: usize,
    eval_points: &[TowerGf256],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<(TowerAlphaShares, TowerAlphaShares), PreprocessError> {
    let n = eval_points.len();
    if t == 0 || t > n || party_rngs.len() != n {
        return Err(PreprocessError::InvalidThreshold { t, n });
    }
    validate_all_eval_points_gf256(eval_points)?;

    let mut alpha_contribs = vec![[Tower128::ZERO; 2]; n];
    let mut alpha_shamir = vec![[Tower128::ZERO; 2]; n];
    let mut beta_shamir = SecretBuffer(vec![[Tower128::ZERO; 2]; n]);

    for i in 0..n {
        for lane in 0..2 {
            let mut a_i = party_rngs[i].next_tower128();
            let mut b_i = party_rngs[i].next_tower128();
            alpha_contribs[i][lane] = a_i;
            let a_sh = SecretBuffer(shamir_share_tower128(
                t,
                eval_points,
                a_i,
                &mut party_rngs[i],
            ));
            let b_sh = SecretBuffer(shamir_share_tower128(
                t,
                eval_points,
                b_i,
                &mut party_rngs[i],
            ));
            wipe_u128s(core::slice::from_mut(&mut a_i.0));
            wipe_u128s(core::slice::from_mut(&mut b_i.0));
            for p in 0..n {
                alpha_shamir[p][lane] = alpha_shamir[p][lane].add(a_sh[p]);
                beta_shamir[p][lane] = beta_shamir[p][lane].add(b_sh[p]);
            }
        }
    }

    let coin =
        run_commit_and_open_coin(session_id, b"SPDZ_ALPHA_GF256_DEG", session_id, party_rngs)?;
    let etas = [
        Tower128(
            u128::from_le_bytes(core::array::from_fn(|array_index| {
                (coin[0..16])[array_index]
            })) | 1,
        ),
        Tower128(
            u128::from_le_bytes(core::array::from_fn(|array_index| {
                (coin[16..32])[array_index]
            })) | 1,
        ),
    ];
    for lane in 0..2 {
        let comb: SecretBuffer<Vec<Tower128>> = SecretBuffer(
            (0..n)
                .map(|p| beta_shamir[p][lane].add(etas[lane].mul(alpha_shamir[p][lane])))
                .collect(),
        );
        let _ = commit_and_open_degree_tower128(
            session_id,
            "spdz_setup_alpha_gf256",
            t,
            eval_points,
            &comb,
            party_rngs,
        )?;
    }
    Ok((alpha_contribs, alpha_shamir))
}

/// Deal and degree-check consistent degree-`< t` Shamir shares of caller-supplied 2-lane
/// `Tower128` SPDZ MAC key contributions `alpha_contribs` (for example, the per-party
/// `mac_alpha()` scalars of two silent [`crate::pcg_dense::DensePcgExpandedVault`] lanes).
pub fn spdz_share_existing_alpha_gf256(
    session_id: &[u8; 32],
    t: usize,
    eval_points: &[TowerGf256],
    alpha_contribs: &[[Tower128; 2]],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<TowerAlphaShares, PreprocessError> {
    let n = eval_points.len();
    if t == 0 || t > n || alpha_contribs.len() != n || party_rngs.len() != n {
        return Err(PreprocessError::InvalidThreshold { t, n });
    }
    validate_all_eval_points_gf256(eval_points)?;

    let mut alpha_shamir = vec![[Tower128::ZERO; 2]; n];
    let mut beta_shamir = SecretBuffer(vec![[Tower128::ZERO; 2]; n]);

    for i in 0..n {
        for lane in 0..2 {
            let a_i = alpha_contribs[i][lane];
            let mut b_i = party_rngs[i].next_tower128();
            let a_sh = SecretBuffer(shamir_share_tower128(
                t,
                eval_points,
                a_i,
                &mut party_rngs[i],
            ));
            let b_sh = SecretBuffer(shamir_share_tower128(
                t,
                eval_points,
                b_i,
                &mut party_rngs[i],
            ));
            wipe_u128s(core::slice::from_mut(&mut b_i.0));
            for p in 0..n {
                alpha_shamir[p][lane] = alpha_shamir[p][lane].add(a_sh[p]);
                beta_shamir[p][lane] = beta_shamir[p][lane].add(b_sh[p]);
            }
        }
    }

    let coin =
        run_commit_and_open_coin(session_id, b"SPDZ_ALPHA_GF256_DEG", session_id, party_rngs)?;
    let etas = [
        Tower128(
            u128::from_le_bytes(core::array::from_fn(|array_index| {
                (coin[0..16])[array_index]
            })) | 1,
        ),
        Tower128(
            u128::from_le_bytes(core::array::from_fn(|array_index| {
                (coin[16..32])[array_index]
            })) | 1,
        ),
    ];
    for lane in 0..2 {
        let comb: SecretBuffer<Vec<Tower128>> = SecretBuffer(
            (0..n)
                .map(|p| beta_shamir[p][lane].add(etas[lane].mul(alpha_shamir[p][lane])))
                .collect(),
        );
        let _ = commit_and_open_degree_tower128(
            session_id,
            "spdz_share_existing_alpha_gf256",
            t,
            eval_points,
            &comb,
            party_rngs,
        )?;
    }
    Ok(alpha_shamir)
}

/// LHL-amplified (`[I | H]` with `32` disposable tail bytes = `256` bits, `< 2^{-129}` selective-failure
/// advantage) pairwise 2-lane `Tower128` BDOZ batch authentication of `count` `TowerGf256` share vectors.
///
/// Sender `i` inputs ONLY its private `alpha_per_party[i]`; Receiver `j` inputs uniform random OT
/// choice bytes and broadcasts derandomized differences after all OTs complete.
pub fn authenticate_gf256_batch_two_lane(
    ot_mesh: &mut OtMesh,
    alpha_per_party: &[[Tower128; 2]],
    x_batch: &[Vec<TowerGf256>],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<(PairwiseTowerMacs, PairwiseTowerMacs), PreprocessError> {
    let n = ot_mesh.n;
    let count = x_batch.len();
    if n == 0 || alpha_per_party.len() != n || party_rngs.len() != n {
        return Err(PreprocessError::InvalidThreshold { t: 1, n });
    }
    for row in x_batch {
        if row.len() != n {
            return Err(PreprocessError::InvalidThreshold { t: 1, n });
        }
    }
    if count == 0 {
        return Ok((vec![vec![Vec::new(); n]; n], vec![vec![Vec::new(); n]; n]));
    }

    let m_raw = count + 32; // 32 extra random GF(256) bytes = 256 bits of LHL min-entropy buffer
    let num_u64 = m_raw.div_ceil(8);

    let mut r_bytes = SecretBuffer(vec![vec![0u8; m_raw]; n]);
    let mut choice_words = SecretBuffer(vec![vec![0u64; num_u64]; n]);
    for j in 0..n {
        party_rngs[j].fill_bytes(&mut r_bytes[j]);
        for s in 0..m_raw {
            choice_words[j][s / 8] |= (r_bytes[j][s] as u64) << (8 * (s % 8));
        }
    }

    let mut raw_macs = SecretBuffer(vec![vec![vec![[Tower128::ZERO; 2]; m_raw]; n]; n]);
    let mut raw_keys = SecretBuffer(vec![vec![vec![[Tower128::ZERO; 2]; m_raw]; n]; n]);

    for i in 0..n {
        for s in 0..m_raw {
            let ri_gf = TowerGf256(r_bytes[i][s]);
            for lane in 0..2 {
                let local_mask = party_rngs[i].next_tower128();
                raw_keys[i][i][s][lane] = local_mask;
                raw_macs[i][i][s][lane] = local_mask.add(alpha_per_party[i][lane].mul_gf256(ri_gf));
            }
        }
        for j in 0..n {
            if i == j {
                continue;
            }
            let (send_pads, recv_pads) =
                ot_mesh.run_correlated_ot_words(i, j, &choice_words[j], party_rngs)?;
            for s in 0..m_raw {
                let rj_byte = black_box(r_bytes[j][s]);
                for lane in 0..2 {
                    let alpha_il = alpha_per_party[i][lane];
                    let mut key_sum = Tower128::ZERO;
                    let mut mac_sum = Tower128::ZERO;
                    for bit in 0..8 {
                        let ot_idx = 8 * s + bit;
                        let (p0, p1) = &send_pads[ot_idx];
                        let pad0 =
                            Tower128(u128::from_le_bytes(core::array::from_fn(|array_index| {
                                (p0[16 * lane..16 * (lane + 1)])[array_index]
                            })));
                        let pad1 =
                            Tower128(u128::from_le_bytes(core::array::from_fn(|array_index| {
                                (p1[16 * lane..16 * (lane + 1)])[array_index]
                            })));
                        let mask_k = party_rngs[i].next_tower128();
                        key_sum = key_sum.add(mask_k);
                        let ct0 = mask_k.add(pad0);
                        let ct1 = mask_k
                            .add(alpha_il.mul_gf256(TowerGf256(1u8 << bit)))
                            .add(pad1);

                        let pad_c =
                            Tower128(u128::from_le_bytes(core::array::from_fn(|array_index| {
                                (recv_pads[ot_idx][16 * lane..16 * (lane + 1)])[array_index]
                            })));
                        let b_choice = ((rj_byte >> bit) & 1) == 1;
                        let c_mask = 0u128.wrapping_sub(black_box(b_choice as u128));
                        let ct_sel = Tower128(ct0.0 ^ (c_mask & (ct0.0 ^ ct1.0)));
                        mac_sum = mac_sum.add(ct_sel.add(pad_c));
                    }
                    raw_keys[i][j][s][lane] = key_sum;
                    raw_macs[i][j][s][lane] = mac_sum;
                }
            }
        }
    }

    // Post-OT systematic universal hash `[I | H]` (`count x (count + 32)`)
    let sid = ot_mesh.session_id;
    let lhl_coin = run_commit_and_open_coin(&sid, b"BDOZ_GF256_LHL_COMBINE", &sid, party_rngs)?;
    let mut h_xof = Cshake256Xof::new(b"QSAG.BDOZ.GF256.LHL_H/v1");
    h_xof.absorb(&lhl_coin);

    let mut h_rows = vec![[0u8; 32]; count];
    for row in &mut h_rows {
        h_xof.squeeze(row);
    }

    // Each party `j` broadcasts derandomized differences `diff[j][idx] = x_batch[idx][j] ^ u_comb[j][idx]`
    let mut diffs = vec![vec![TowerGf256::ZERO; count]; n];
    for j in 0..n {
        for idx in 0..count {
            let mut u_comb = TowerGf256(r_bytes[j][idx]);
            for tl in 0..32 {
                let g = TowerGf256(h_rows[idx][tl]);
                u_comb = u_comb.add(g.mul(TowerGf256(r_bytes[j][count + tl])));
            }
            diffs[j][idx] = x_batch[idx][j].add(u_comb);
        }
        wipe_bytes(&mut r_bytes[j]);
        wipe_u64s(&mut choice_words[j]);
    }

    let mut out_macs = vec![vec![vec![[Tower128::ZERO; 2]; count]; n]; n];
    let mut out_keys = vec![vec![vec![[Tower128::ZERO; 2]; count]; n]; n];
    for i in 0..n {
        for j in 0..n {
            for idx in 0..count {
                let d_gf = diffs[j][idx];
                for lane in 0..2 {
                    let mut m_acc = raw_macs[i][j][idx][lane];
                    let mut k_acc = raw_keys[i][j][idx][lane];
                    for tl in 0..32 {
                        let g_gf = TowerGf256(h_rows[idx][tl]);
                        m_acc = m_acc.add(raw_macs[i][j][count + tl][lane].mul_gf256(g_gf));
                        k_acc = k_acc.add(raw_keys[i][j][count + tl][lane].mul_gf256(g_gf));
                    }
                    k_acc = k_acc.add(alpha_per_party[i][lane].mul_gf256(d_gf));
                    out_macs[i][j][idx][lane] = m_acc;
                    out_keys[i][j][idx][lane] = k_acc;
                }
            }
            for s in 0..m_raw {
                wipe_tower128(&mut raw_macs[i][j][s]);
                wipe_tower128(&mut raw_keys[i][j][s]);
            }
        }
    }

    Ok((out_macs, out_keys))
}

/// Single-vector wrapper around `authenticate_gf256_batch_two_lane` inheriting full LHL `Combine`
/// selective-failure immunity (`< 2^{-129}`).
pub fn authenticate_gf256_shares_two_lane(
    ot_mesh: &mut OtMesh,
    alpha_per_party: &[[Tower128; 2]],
    x_shares: &[TowerGf256],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<TowerMacMatrices, PreprocessError> {
    let batch = alloc::vec![x_shares.to_vec()];
    let (b_macs, b_keys) =
        authenticate_gf256_batch_two_lane(ot_mesh, alpha_per_party, &batch, party_rngs)?;
    let n = ot_mesh.n;
    let mut macs = vec![vec![[Tower128::ZERO; 2]; n]; n];
    let mut keys = vec![vec![[Tower128::ZERO; 2]; n]; n];
    for i in 0..n {
        for j in 0..n {
            macs[i][j] = b_macs[i][j][0];
            keys[i][j] = b_keys[i][j][0];
        }
    }
    Ok((macs, keys))
}

/// Dealerless `Π_MAC` over `BitslicedGf256x64` words: computes degree-`< t` 2-lane `Tower128`
/// SPDZ Shamir MAC shares `macs[party][word_idx][lane][bit]` for every party `0..n` using
/// LHL-amplified OT (`< 2^{-129}` selective-failure advantage) AND verifies across ALL `0..n`
/// parties that both `words_per_party` and `macs` lie on consistent degree-`< t` polynomials with
/// $\gamma_{\text{lane}}(x) = \alpha_{\text{lane}} \cdot x$ ($2^{-256}$ soundness).
#[expect(
    clippy::too_many_arguments,
    reason = "Quorum, value shares, MAC shares and private randomness are separate protocol inputs"
)]
