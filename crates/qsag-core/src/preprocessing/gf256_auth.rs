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
pub fn spdz_authenticate_bs_gf256_words(
    session_id: &[u8; 32],
    t: usize,
    eval_points: &[TowerGf256],
    ot_mesh: &mut OtMesh,
    alpha_contribs: &[[Tower128; 2]],
    alpha_shamir_shares: &[[Tower128; 2]],
    words_per_party: &[Vec<BitslicedGf256x64>],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<Vec<[[Tower128; 64]; 2]>>, PreprocessError> {
    let n = eval_points.len();
    if t == 0
        || t > n
        || ot_mesh.n != n
        || alpha_contribs.len() != n
        || alpha_shamir_shares.len() != n
        || words_per_party.len() != n
        || party_rngs.len() != n
    {
        return Err(PreprocessError::InvalidThreshold { t, n });
    }
    validate_all_eval_points_gf256(eval_points)?;
    let num_words = words_per_party[0].len();
    for words_per_party_p_item in words_per_party[..n].iter().skip(1) {
        if (*words_per_party_p_item).len() != num_words {
            return Err(PreprocessError::InvalidThreshold { t, n });
        }
    }
    if num_words == 0 {
        return Ok(vec![Vec::new(); n]);
    }

    let lambdas_t = lagrange_weights_zero_gf256(&eval_points[..t])
        .ok_or(PreprocessError::DuplicateOrZeroEvalPoint)?;
    let eval_mats: Vec<PublicGf256Matrix> = eval_points
        .iter()
        .map(|&pt| PublicGf256Matrix::from_public_scalar(pt))
        .collect();

    // Sample 1 disposable degree-`< t` random GF(256)^64 mask word `r_chk` (`512` bits of uniform entropy!)
    let mut r_chk_sh = vec![[0u64; 8]; n];
    for party_rngs_i_item in party_rngs[..n].iter_mut() {
        let mut coeffs = Vec::with_capacity(t);
        for _ in 0..t {
            let mut rp = [0u64; 8];
            for pl in &mut rp {
                *pl = (*party_rngs_i_item).next_u64();
            }
            coeffs.push(rp);
        }
        for (p, mat_pt) in eval_mats.iter().enumerate() {
            let mut acc = [0u64; 8];
            for c in coeffs.iter().rev() {
                acc = bs_gf256_xor(&mat_pt.scale_planes(&acc), c);
            }
            bs_gf256_xor_assign(&mut r_chk_sh[p], &acc);
        }
        for c in &mut coeffs {
            wipe_u64s(c);
        }
    }

    let total_w = num_words + 1;
    let total_elems = 64 * total_w;
    let m_raw = total_elems + 32; // +32 bytes = 256-bit LHL buffer
    let num_u64 = m_raw.div_ceil(8);

    let mut u_target = SecretBuffer(vec![vec![TowerGf256::ZERO; total_elems]; t]);
    let mut r_bytes = SecretBuffer(vec![vec![0u8; m_raw]; t]);
    let mut choice_words = SecretBuffer(vec![vec![0u64; num_u64]; t]);
    for j in 0..t {
        let lj = lambdas_t[j];
        for k in 0..num_words {
            for bit in 0..64 {
                u_target[j][64 * k + bit] =
                    lj.mul(bs_gf256_extract_lane(&words_per_party[j][k], bit));
            }
        }
        for bit in 0..64 {
            u_target[j][64 * num_words + bit] = lj.mul(bs_gf256_extract_lane(&r_chk_sh[j], bit));
        }
        party_rngs[j].fill_bytes(&mut r_bytes[j]);
        for s in 0..m_raw {
            choice_words[j][s / 8] |= (r_bytes[j][s] as u64) << (8 * (s % 8));
        }
    }

    // Accumulate additive OT correlation shares directly into `sum_raw[party][slot]` (`O(n * m_raw)`
    // instead of `O(n * t * m_raw)` 4D matrices) before universal-hash `[I | H]` compression.
    let mut sum_raw = vec![vec![[Tower128::ZERO; 2]; m_raw]; n];

    for i in 0..n {
        if i < t {
            for s in 0..m_raw {
                let ri_emb = TowerGf256(r_bytes[i][s]);
                for lane in 0..2 {
                    let local_mask = party_rngs[i].next_tower128();
                    let local_mac = local_mask.add(alpha_contribs[i][lane].mul_gf256(ri_emb));
                    sum_raw[i][s][lane] = sum_raw[i][s][lane].add(local_mask).add(local_mac);
                }
            }
        }
        for j in 0..t {
            if i == j {
                continue;
            }
            let (send_pads, recv_pads) =
                ot_mesh.run_correlated_ot_words(i, j, &choice_words[j], party_rngs)?;
            for s in 0..m_raw {
                let rj_byte = black_box(r_bytes[j][s]);
                for lane in 0..2 {
                    let alpha_il = alpha_contribs[i][lane];
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
                    sum_raw[i][s][lane] = sum_raw[i][s][lane].add(key_sum);
                    sum_raw[j][s][lane] = sum_raw[j][s][lane].add(mac_sum);
                }
            }
        }
    }

    // Post-OT systematic Toeplitz 2-universal hash `[I | T]` (`256^{-total_elems}` collision bound!)
    let lhl_coin = run_commit_and_open_coin(
        session_id,
        b"SPDZ_BS64_LHL_COMBINE",
        &ot_mesh.session_id,
        party_rngs,
    )?;
    let mut h_xof = Cshake256Xof::new(b"QSAG.SPDZ.BS64.LHL_H/v1");
    h_xof.absorb(&lhl_coin);
    let mut toeplitz_h = vec![0u8; total_elems + 32];
    h_xof.squeeze(&mut toeplitz_h);

    let mut diff_sum = SecretBuffer(vec![TowerGf256::ZERO; total_elems]);
    for j in 0..t {
        let mut r_lut = [[0u8; 16]; 64];
        for tl in 0..32 {
            let rt = TowerGf256(r_bytes[j][total_elems + tl]);
            #[expect(
                clippy::needless_range_loop,
                reason = "Each public nibble updates two adjacent lookup rows"
            )]
            for nib in 0..16usize {
                r_lut[2 * tl][nib] = TowerGf256(nib as u8).mul(rt).0;
                r_lut[2 * tl + 1][nib] = TowerGf256((nib as u8) << 4).mul(rt).0;
            }
        }
        for idx in 0..total_elems {
            let mut u_comb = r_bytes[j][idx];
            for tl in 0..32 {
                let hb = toeplitz_h[idx + tl];
                u_comb ^=
                    r_lut[2 * tl][(hb & 0x0F) as usize] ^ r_lut[2 * tl + 1][(hb >> 4) as usize];
            }
            diff_sum[idx] = diff_sum[idx].add(u_target[j][idx].add(TowerGf256(u_comb)));
            u_target[j][idx] = TowerGf256::ZERO;
        }
        for row in &mut r_lut {
            wipe_bytes(row);
        }
        wipe_bytes(&mut r_bytes[j]);
        wipe_u64s(&mut choice_words[j]);
    }

    // Precompute Four-Russians nibble LUTs for `sum_raw[p][total_elems..+32][lane]` (indexed only by public `toeplitz_h`)
    let sum_luts: SecretBuffer<Vec<[[[u128; 16]; 64]; 2]>> = SecretBuffer(
        (0..n)
            .map(|p| {
                core::array::from_fn(|lane| {
                    core::array::from_fn(|slot| {
                        let tl = slot / 2;
                        let hi = (slot % 2) == 1;
                        let base = sum_raw[p][total_elems + tl][lane];
                        core::array::from_fn(|nib| {
                            let sc = if hi { (nib as u8) << 4 } else { nib as u8 };
                            base.mul_gf256(TowerGf256(sc)).0
                        })
                    })
                })
            })
            .collect(),
    );

    let party_work_seeds: SecretBuffer<Vec<[u8; 32]>> =
        SecretBuffer((0..n).map(|p| party_rngs[p].next_bytes32()).collect());

    // Sum additive shares `tau_p[idx][lane]` at each party `p in 0..n` and Shamir-share at degree `< t`
    let mut all_macs = vec![vec![[[Tower128::ZERO; 64]; 2]; total_w]; n];
    const SH_BLK_WORDS: usize = 256;
    let eval_sh_block = |blk_idx: usize, dst_per_party: &mut [&mut [[[Tower128; 64]; 2]]]| {
        let k_start = blk_idx * SH_BLK_WORDS;
        let blk_len = dst_per_party[0].len();
        let blk_le = (blk_idx as u64).to_le_bytes();
        for p in 0..n {
            let mut sub_rng = PartyPrivateRng::from_seed(party_work_seeds[p], &blk_le);
            for k_off in 0..blk_len {
                let k = k_start + k_off;
                for lane in 0..2 {
                    let ap = alpha_contribs[p][lane];
                    let lut = &sum_luts[p][lane];
                    let mut tau_word = [0u128; 64];
                    for (bit, tau_dst) in tau_word.iter_mut().enumerate() {
                        let idx = 64 * k + bit;
                        let mut acc = sum_raw[p][idx][lane].add(ap.mul_gf256(diff_sum[idx])).0;
                        for tl in 0..32 {
                            let hb = toeplitz_h[idx + tl];
                            acc ^= lut[2 * tl][(hb & 0x0F) as usize]
                                ^ lut[2 * tl + 1][(hb >> 4) as usize];
                        }
                        *tau_dst = acc;
                    }
                    let sh_blocks = SecretBuffer(shamir_share_tower128x64_mats(
                        t,
                        &eval_mats,
                        &tau_word,
                        &mut sub_rng,
                    ));
                    wipe_u128s(&mut tau_word);
                    for (q, dst_q) in dst_per_party.iter_mut().enumerate() {
                        let mut unpacked = unpack_bs_gf256x16_to_u128x64(&sh_blocks[q]);
                        for bit in 0..64 {
                            dst_q[k_off][lane][bit] =
                                dst_q[k_off][lane][bit].add(Tower128(unpacked[bit]));
                        }
                        wipe_u128s(&mut unpacked);
                    }
                }
            }
        }
    };

    #[cfg(any(test, feature = "std"))]
    if total_w > SH_BLK_WORDS {
        let mut party_iters: Vec<_> = all_macs
            .iter_mut()
            .map(|v| v.chunks_mut(SH_BLK_WORDS))
            .collect();
        let mut blk_groups: Vec<Vec<&mut [[[Tower128; 64]; 2]]>> = Vec::new();
        loop {
            let mut grp = Vec::with_capacity(n);
            for it in &mut party_iters {
                if let Some(sl) = it.next() {
                    grp.push(sl);
                }
            }
            if grp.is_empty() {
                break;
            }
            blk_groups.push(grp);
        }
        let workers = std::thread::available_parallelism()
            .map_or(1, usize::from)
            .min(16);
        let grp_per_worker = blk_groups.len().div_ceil(workers).max(1);
        std::thread::scope(|scope| {
            for (w_idx, worker_grps) in blk_groups.chunks_mut(grp_per_worker).enumerate() {
                let base_blk = w_idx * grp_per_worker;
                scope.spawn(move || {
                    for (off, grp) in worker_grps.iter_mut().enumerate() {
                        eval_sh_block(base_blk + off, grp.as_mut_slice());
                    }
                });
            }
        });
    } else {
        let mut party_iters: Vec<_> = all_macs
            .iter_mut()
            .map(|v| v.chunks_mut(SH_BLK_WORDS))
            .collect();
        let mut blk_idx = 0usize;
        loop {
            let mut grp = Vec::with_capacity(n);
            for it in &mut party_iters {
                if let Some(sl) = it.next() {
                    grp.push(sl);
                }
            }
            if grp.is_empty() {
                break;
            }
            eval_sh_block(blk_idx, grp.as_mut_slice());
            blk_idx += 1;
        }
    }
    #[cfg(not(any(test, feature = "std")))]
    {
        let mut party_iters: Vec<_> = all_macs
            .iter_mut()
            .map(|v| v.chunks_mut(SH_BLK_WORDS))
            .collect();
        let mut blk_idx = 0usize;
        loop {
            let mut grp = Vec::with_capacity(n);
            for it in &mut party_iters {
                if let Some(sl) = it.next() {
                    grp.push(sl);
                }
            }
            if grp.is_empty() {
                break;
            }
            eval_sh_block(blk_idx, grp.as_mut_slice());
            blk_idx += 1;
        }
    }

    for row in sum_raw.iter_mut() {
        for share in row {
            wipe_tower128(share);
        }
    }
    drop(sum_luts);
    drop(party_work_seeds);
    drop(diff_sum);

    spdz_pimac_check_bs_gf256_words(
        session_id,
        t,
        eval_points,
        alpha_shamir_shares,
        words_per_party,
        &all_macs,
        &mut r_chk_sh,
        &lhl_coin,
        party_rngs,
    )?;

    // Pop the disposable `r_chk` MAC slot and return the verified `num_words` SPDZ MAC shares
    for all_macs_p_item in all_macs[..n].iter_mut() {
        if let Some(mut chk_m) = (*all_macs_p_item).pop() {
            wipe_tower128(&mut chk_m[0]);
            wipe_tower128(&mut chk_m[1]);
        }
    }
    Ok(all_macs)
}

/// Batch `Π_MAC` consistency and full `0..n` degree check of Shamir value shares
/// `words_per_party[p][0..num_words]` against Shamir MAC shares `all_macs[p][0..=num_words]`.
///
/// Slot `num_words` of `all_macs` authenticates the disposable mask word whose value shares are
/// `r_chk_sh`. The check accepts only if both the value shares and the MAC shares lie on
/// degree-`< t` polynomials across all `n` parties and every MAC polynomial opens to
/// `alpha_lane * value` (`2^{-256}` soundness). `transcript` binds the check coin to everything
/// fixed before it; `r_chk_sh` is wiped.
#[expect(
    clippy::too_many_arguments,
    reason = "Quorum, value shares, MAC shares and private randomness are separate protocol inputs"
)]
pub(crate) fn spdz_pimac_check_bs_gf256_words(
    session_id: &[u8; 32],
    t: usize,
    eval_points: &[TowerGf256],
    alpha_shamir_shares: &[[Tower128; 2]],
    words_per_party: &[Vec<BitslicedGf256x64>],
    all_macs: &[Vec<[[Tower128; 64]; 2]>],
    r_chk_sh: &mut [BitslicedGf256x64],
    transcript: &[u8; 32],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<(), PreprocessError> {
    let n = eval_points.len();
    let num_words = words_per_party[0].len();
    const SH_BLK_WORDS: usize = 256;

    // 1) Check degree `< t` of `words_per_party` across `0..n` masked by `r_chk_sh` (`2^{-256}` soundness!)
    let chk_coin =
        run_commit_and_open_coin(session_id, b"SPDZ_BS64_PIMAC_CHK", transcript, party_rngs)?;
    let mut chk_xof = Cshake256Xof::new(b"QSAG.SPDZ.BS64.PIMAC_W/v1");
    chk_xof.absorb(&chk_coin);

    let mut deg_fold_sh = SecretBuffer(r_chk_sh.to_vec());
    #[expect(
        clippy::needless_range_loop,
        reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows"
    )]
    for k in 0..num_words {
        let mut s_byte = [0u8; 1];
        chk_xof.squeeze(&mut s_byte);
        let mat = PublicGf256Matrix::from_public_scalar(TowerGf256(s_byte[0] | 1));
        for p in 0..n {
            mat.scale_xor_into(&mut deg_fold_sh[p], &words_per_party[p][k]);
        }
    }
    // Check lanes `32..64` here while reserving lanes `0..16` and `16..32` strictly as two
    // independent 128-bit one-time pads `(R_0, R_1)` for `(Z_0, Z_1)` below (`0` pad reuse!).
    let mut deg_half_sh = vec![[0u64; 8]; n];
    for p in 0..n {
        for pl in 0..8 {
            deg_half_sh[p][pl] = deg_fold_sh[p][pl] & 0xFFFF_FFFF_0000_0000u64;
        }
    }
    drop(deg_fold_sh);
    let _ =
        open_and_check_degree_bs_gf256(t, eval_points, &deg_half_sh, "spdz_bs_gf256_words_deg")?;

    // 2) Independent 2-lane `Tower128` folding (`2^{-256}` soundness, zero pad reuse across lanes!):
    //    - `R_0` (lanes `0..16` of `r_chk_sh`) masks `Z_0` with identity basis `[I, *; 0, I]`;
    //    - `R_1` (lanes `16..32` of `r_chk_sh`) masks `Z_1` independently;
    //    - Lanes `32..64` of `r_chk_sh` and all `64 * num_words` wires use independent uniform
    //      `GF(2^128)` challenges `(chi_0, chi_1)` (no `| 1` bias!).
    let mut z_sh_lanes = SecretBuffer(vec![vec![Tower128::ZERO; n]; 2]);
    let mut z_mac = SecretBuffer(vec![[Tower128::ZERO; 2]; n]);
    for b_idx in 0..16 {
        let basis = Tower128(1u128 << (8 * b_idx));
        let mut cb0 = [0u8; 16];
        chk_xof.squeeze(&mut cb0);
        let chi0_hi = Tower128(u128::from_le_bytes(cb0));
        for p in 0..n {
            let r_lo = bs_gf256_extract_lane(&r_chk_sh[p], b_idx);
            let r_hi = bs_gf256_extract_lane(&r_chk_sh[p], 16 + b_idx);
            z_sh_lanes[0][p] = z_sh_lanes[0][p]
                .add(basis.mul_gf256(r_lo))
                .add(chi0_hi.mul_gf256(r_hi));
            z_sh_lanes[1][p] = z_sh_lanes[1][p].add(basis.mul_gf256(r_hi));
            z_mac[p][0] = z_mac[p][0]
                .add(basis.mul(all_macs[p][num_words][0][b_idx]))
                .add(chi0_hi.mul(all_macs[p][num_words][0][16 + b_idx]));
            z_mac[p][1] = z_mac[p][1].add(basis.mul(all_macs[p][num_words][1][16 + b_idx]));
        }
    }
    #[expect(
        clippy::needless_range_loop,
        reason = "Coordinate order binds the same lane across all party MAC matrices"
    )]
    for bit in 32..64 {
        let mut cb = [0u8; 32];
        chk_xof.squeeze(&mut cb);
        let chi0 = Tower128(u128::from_le_bytes(core::array::from_fn(|i| cb[i])));
        let chi1 = Tower128(u128::from_le_bytes(core::array::from_fn(|i| cb[16 + i])));
        for p in 0..n {
            let r_byte = bs_gf256_extract_lane(&r_chk_sh[p], bit);
            z_sh_lanes[0][p] = z_sh_lanes[0][p].add(chi0.mul_gf256(r_byte));
            z_sh_lanes[1][p] = z_sh_lanes[1][p].add(chi1.mul_gf256(r_byte));
            z_mac[p][0] = z_mac[p][0].add(chi0.mul(all_macs[p][num_words][0][bit]));
            z_mac[p][1] = z_mac[p][1].add(chi1.mul(all_macs[p][num_words][1][bit]));
        }
    }
    for r_chk_sh_p_item in r_chk_sh[..n].iter_mut() {
        wipe_u64s(&mut *r_chk_sh_p_item);
    }

    let fold_word_range = |blk_start: usize,
                           blk_count: usize|
     -> (Vec<[Tower128; 2]>, Vec<[Tower128; 2]>) {
        let mut local_zsh = vec![[Tower128::ZERO; 2]; n];
        let mut local_zmac = vec![[Tower128::ZERO; 2]; n];
        let mut chi_buf = [0u8; 64 * 32];
        for blk_idx in blk_start..(blk_start + blk_count) {
            let k_start = blk_idx * SH_BLK_WORDS;
            let k_end = (k_start + SH_BLK_WORDS).min(num_words);
            let mut blk_xof = Cshake256Xof::new(b"QSAG.SPDZ.BS64.PIMAC_W_BLK/v1");
            blk_xof.absorb(&chk_coin);
            blk_xof.absorb(&(blk_idx as u64).to_le_bytes());
            for k in k_start..k_end {
                blk_xof.squeeze(&mut chi_buf);
                let lhs: [[u128; 2]; 64] = core::array::from_fn(|bit| {
                    let off = 32 * bit;
                    [
                        u128::from_le_bytes(core::array::from_fn(|b| chi_buf[off + b])),
                        u128::from_le_bytes(core::array::from_fn(|b| chi_buf[off + 16 + b])),
                    ]
                });
                for p in 0..n {
                    for (bit, pair) in lhs.iter().enumerate() {
                        let x_byte = bs_gf256_extract_lane(&words_per_party[p][k], bit);
                        local_zsh[p][0] = local_zsh[p][0].add(Tower128(pair[0]).mul_gf256(x_byte));
                        local_zsh[p][1] = local_zsh[p][1].add(Tower128(pair[1]).mul_gf256(x_byte));
                    }
                    let mut rhs: [[u128; 2]; 64] = core::array::from_fn(|bit| {
                        [all_macs[p][k][0][bit].0, all_macs[p][k][1][bit].0]
                    });
                    let mut folded = qsag_asm::tower128_bdoz_2lane_mac(&lhs, &rhs);
                    local_zmac[p][0] = local_zmac[p][0].add(Tower128(folded[0]));
                    local_zmac[p][1] = local_zmac[p][1].add(Tower128(folded[1]));
                    wipe_u128s(rhs.as_flattened_mut());
                    wipe_u128s(&mut folded);
                }
            }
        }
        wipe_bytes(&mut chi_buf);
        (local_zsh, local_zmac)
    };

    let num_blks = num_words.div_ceil(SH_BLK_WORDS);
    #[cfg(any(test, feature = "std"))]
    if num_blks > 1 {
        let workers = std::thread::available_parallelism()
            .map_or(1, usize::from)
            .min(16);
        let blks_per_worker = num_blks.div_ceil(workers).max(1);
        let partials = std::thread::scope(|scope| {
            let mut handles = Vec::new();
            let mut b0 = 0usize;
            while b0 < num_blks {
                let cnt = (num_blks - b0).min(blks_per_worker);
                handles.push(scope.spawn(move || fold_word_range(b0, cnt)));
                b0 += cnt;
            }
            handles
                .into_iter()
                .map(|h| h.join().expect("spdz pimac fold worker"))
                .collect::<Vec<_>>()
        });
        for (mut l_zsh, mut l_zmac) in partials {
            for p in 0..n {
                z_sh_lanes[0][p] = z_sh_lanes[0][p].add(l_zsh[p][0]);
                z_sh_lanes[1][p] = z_sh_lanes[1][p].add(l_zsh[p][1]);
                z_mac[p][0] = z_mac[p][0].add(l_zmac[p][0]);
                z_mac[p][1] = z_mac[p][1].add(l_zmac[p][1]);
                wipe_tower128(&mut l_zsh[p]);
                wipe_tower128(&mut l_zmac[p]);
            }
        }
    } else if num_blks == 1 {
        let (mut l_zsh, mut l_zmac) = fold_word_range(0, 1);
        for p in 0..n {
            z_sh_lanes[0][p] = z_sh_lanes[0][p].add(l_zsh[p][0]);
            z_sh_lanes[1][p] = z_sh_lanes[1][p].add(l_zsh[p][1]);
            z_mac[p][0] = z_mac[p][0].add(l_zmac[p][0]);
            z_mac[p][1] = z_mac[p][1].add(l_zmac[p][1]);
            wipe_tower128(&mut l_zsh[p]);
            wipe_tower128(&mut l_zmac[p]);
        }
    }
    #[cfg(not(any(test, feature = "std")))]
    if num_blks > 0 {
        let (mut l_zsh, mut l_zmac) = fold_word_range(0, num_blks);
        for p in 0..n {
            z_sh_lanes[0][p] = z_sh_lanes[0][p].add(l_zsh[p][0]);
            z_sh_lanes[1][p] = z_sh_lanes[1][p].add(l_zsh[p][1]);
            z_mac[p][0] = z_mac[p][0].add(l_zmac[p][0]);
            z_mac[p][1] = z_mac[p][1].add(l_zmac[p][1]);
            wipe_tower128(&mut l_zsh[p]);
            wipe_tower128(&mut l_zmac[p]);
        }
    }

    let z_open = [
        commit_and_open_degree_tower128(
            session_id,
            "spdz_bs_gf256_pimac_z0",
            t,
            eval_points,
            &z_sh_lanes[0],
            party_rngs,
        )?,
        commit_and_open_degree_tower128(
            session_id,
            "spdz_bs_gf256_pimac_z1",
            t,
            eval_points,
            &z_sh_lanes[1],
            party_rngs,
        )?,
    ];
    drop(z_sh_lanes);

    let mut blind_mesh = OtMesh::establish(
        cshake256_32_multi_frame(b"QSAG.SPDZ.BS64.PIMAC.BLIND/v1", &[session_id, &chk_coin]),
        party_rngs,
    )?;
    // Open `D_lane(x_p) = [gamma_lane(Z_lane)]_p ^ (Z_lane * [alpha_lane]_p)` across ALL `0..n` parties!
    for (lane, &z_op_l) in z_open.iter().enumerate() {
        let d_sh: SecretBuffer<Vec<Tower128>> = SecretBuffer(
            (0..n)
                .map(|p| z_mac[p][lane].add(z_op_l.mul(alpha_shamir_shares[p][lane])))
                .collect(),
        );
        let d_zero = blind_open_degree_tower128(
            session_id,
            "spdz_bs_gf256_pimac_d",
            t,
            eval_points,
            &d_sh,
            &mut blind_mesh,
            party_rngs,
        )?;
        if !d_zero.ct_eq(Tower128::ZERO) {
            return Err(PreprocessError::MacCheckFailed {
                phase: "spdz_bs_gf256_pimac",
                accused_party: None,
            });
        }
    }
    drop(z_mac);
    Ok(())
}

/// Share a 64-bit Boolean word `word` across `eval_points` as a `BitslicedGf256x64` vector of
/// degree `< t` using `rng` and precomputed `PublicGf256Matrix` evaluation points.
#[inline]
pub(super) fn shamir_share_bits64_gf256_mats(
    t: usize,
    eval_mats: &[PublicGf256Matrix],
    word: u64,
    rng: &mut PartyPrivateRng,
) -> Vec<BitslicedGf256x64> {
    let n = eval_mats.len();
    let mut coeffs: Vec<BitslicedGf256x64> = Vec::with_capacity(t);
    coeffs.push([word, 0, 0, 0, 0, 0, 0, 0]);
    for _ in 1..t {
        let mut rand_plane = [0u64; 8];
        for pl in &mut rand_plane {
            *pl = rng.next_u64();
        }
        coeffs.push(rand_plane);
    }

    let mut out = vec![[0u64; 8]; n];
    for (p, mat_pt) in eval_mats.iter().enumerate() {
        let mut acc = [0u64; 8];
        for c in coeffs.iter().rev() {
            acc = bs_gf256_xor(&mat_pt.scale_planes(&acc), c);
        }
        out[p] = acc;
    }
    for c in &mut coeffs {
        wipe_u64s(c);
    }
    out
}

#[cfg(test)]
pub(super) fn shamir_share_bits64_gf256(
    t: usize,
    eval_points: &[TowerGf256],
    word: u64,
    rng: &mut PartyPrivateRng,
) -> Vec<BitslicedGf256x64> {
    let mats: Vec<PublicGf256Matrix> = eval_points
        .iter()
        .map(|&pt| PublicGf256Matrix::from_public_scalar(pt))
        .collect();
    shamir_share_bits64_gf256_mats(t, &mats, word, rng)
}

#[inline]
fn transpose_64x64_in_place(tile: &mut [u64; 64]) {
    for stage in 0..6 {
        let shift = 1usize << stage;
        let mask = u64::MAX / ((1u64 << shift) + 1);
        for base in (0..64).step_by(2 * shift) {
            for offset in 0..shift {
                let a = base + offset;
                let b = a + shift;
                let delta = ((tile[a] >> shift) ^ tile[b]) & mask;
                tile[a] ^= delta << shift;
                tile[b] ^= delta;
            }
        }
    }
}

#[inline]
pub(super) fn unpack_bs_gf256x16_to_u128x64(blocks: &[BitslicedGf256x64; 16]) -> [u128; 64] {
    let mut lo = [0u64; 64];
    let mut hi = [0u64; 64];
    for byte_idx in 0..8 {
        for pl in 0..8 {
            lo[8 * byte_idx + pl] = blocks[byte_idx][pl];
            hi[8 * byte_idx + pl] = blocks[8 + byte_idx][pl];
        }
    }
    transpose_64x64_in_place(&mut lo);
    transpose_64x64_in_place(&mut hi);
    let out: [u128; 64] = core::array::from_fn(|bit| (lo[bit] as u128) | ((hi[bit] as u128) << 64));
    wipe_u64s(&mut lo);
    wipe_u64s(&mut hi);
    out
}

/// Pack 64 `Tower128` elements (`[u128; 64]`) into 16 bitsliced `TowerGf256` byte blocks
/// (`[BitslicedGf256x64; 16]`) and Shamir-share at degree `< t` over `eval_mats`.
pub(super) fn shamir_share_tower128x64_mats(
    t: usize,
    eval_mats: &[PublicGf256Matrix],
    vals: &[u128; 64],
    rng: &mut PartyPrivateRng,
) -> Vec<[BitslicedGf256x64; 16]> {
    let n = eval_mats.len();
    let mut lo: [u64; 64] = core::array::from_fn(|bit| vals[bit] as u64);
    let mut hi: [u64; 64] = core::array::from_fn(|bit| (vals[bit] >> 64) as u64);
    transpose_64x64_in_place(&mut lo);
    transpose_64x64_in_place(&mut hi);
    let mut const_blocks = [[0u64; 8]; 16];
    for byte_idx in 0..8 {
        for pl in 0..8 {
            const_blocks[byte_idx][pl] = lo[8 * byte_idx + pl];
            const_blocks[8 + byte_idx][pl] = hi[8 * byte_idx + pl];
        }
    }
    wipe_u64s(&mut lo);
    wipe_u64s(&mut hi);

    let mut out = vec![[[0u64; 8]; 16]; n];
    for byte_idx in 0..16 {
        let mut coeffs: Vec<BitslicedGf256x64> = Vec::with_capacity(t);
        coeffs.push(const_blocks[byte_idx]);
        for _ in 1..t {
            let mut rp = [0u64; 8];
            for pl in &mut rp {
                *pl = rng.next_u64();
            }
            coeffs.push(rp);
        }
        for (p, mat_pt) in eval_mats.iter().enumerate() {
            let mut acc = [0u64; 8];
            for c in coeffs.iter().rev() {
                acc = bs_gf256_xor(&mat_pt.scale_planes(&acc), c);
            }
            out[p][byte_idx] = acc;
        }
        for c in &mut coeffs {
            wipe_u64s(c);
        }
    }
    for blk in &mut const_blocks {
        wipe_u64s(blk);
    }
    out
}
