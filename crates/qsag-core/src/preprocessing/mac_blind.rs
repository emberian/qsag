//! Multiplicatively blinded MAC residual openings at every threshold and committee size.
//!
//! These helpers consume additive residuals that remain private throughout multiplication.
//! A fresh joint randomizer is the OLE receiver input; the residual is ALWAYS the sender
//! input. Both OLE backends use disposable random choice tapes and a post-OT entropy
//! amplifier, rather than choice bits of a MAC residual. No authenticated triple or MAC
//! opening is used to bootstrap this multiplication, so there is no circular check.
//!
//! In the ideal OLE hybrid, fixing every corrupt input leaves an honest party's uniform
//! randomizer uniform over the field. For nonzero d, w = r*d is a field permutation:
//! its distribution is independent of d (including alpha), with false acceptance 1/|F|.
//! The concrete OLE adds its documented statistical selective-failure bound; raw Gilboa
//! on residual bits would NOT provide this property. Commit all final shares before any
//! are revealed, preventing a last speaker from cancelling the honest check share.
use super::*;

/// Check every degree syndrome privately before opening the blinded constant.
/// Each constraint uses an independent joint randomizer: opening pointwise
/// products with one common r would expose r through a corrupt party's known share.
pub(super) fn blind_open_degree_ext2(
    session_id: &[u8; 32],
    phase: &'static str,
    t: usize,
    points: &[Goldilocks],
    shares: &[GoldilocksExt2],
    mesh: &mut OtMesh,
    rngs: &mut [PartyPrivateRng],
) -> Result<GoldilocksExt2, PreprocessError> {
    let tables = GoldilocksOpeningTables::new(t, points)?;
    for (offset, row) in tables.extra.iter().enumerate() {
        let residual = SecretBuffer(
            shares
                .iter()
                .enumerate()
                .map(|(p, &d)| {
                    let coefficient = if p < t {
                        -row[p]
                    } else if p == t + offset {
                        Goldilocks::ONE
                    } else {
                        Goldilocks::ZERO
                    };
                    d.mul_base(coefficient)
                })
                .collect::<Vec<_>>(),
        );
        let sid = cshake256_32_multi_frame(
            b"QSAG.SPDZ.BLIND.EXT2.DEG/v1",
            &[session_id, phase.as_bytes(), &(offset as u64).to_be_bytes()],
        );
        let w = blind_open_ext2(&sid, phase, &residual, Some(&mut *mesh), rngs)?;
        if !w.ct_eq(GoldilocksExt2::ZERO) {
            return Err(PreprocessError::DegreeCheckFailed { phase });
        }
    }
    let residual = SecretBuffer(
        shares
            .iter()
            .enumerate()
            .map(|(p, &d)| {
                if p < t {
                    d.mul_base(tables.zero[p])
                } else {
                    GoldilocksExt2::ZERO
                }
            })
            .collect::<Vec<_>>(),
    );
    blind_open_ext2(session_id, phase, &residual, Some(mesh), rngs)
}

pub(super) fn blind_open_degree_tower128(
    session_id: &[u8; 32],
    phase: &'static str,
    t: usize,
    points: &[TowerGf256],
    shares: &[Tower128],
    mesh: &mut OtMesh,
    rngs: &mut [PartyPrivateRng],
) -> Result<Tower128, PreprocessError> {
    let tables = Gf256OpeningTables::new(t, points)?;
    for (offset, row) in tables.extra.iter().enumerate() {
        let residual = SecretBuffer(
            shares
                .iter()
                .enumerate()
                .map(|(p, &d)| {
                    let coefficient = if p < t {
                        row[p]
                    } else if p == t + offset {
                        TowerGf256::ONE
                    } else {
                        TowerGf256::ZERO
                    };
                    d.mul_gf256(coefficient)
                })
                .collect::<Vec<_>>(),
        );
        let sid = cshake256_32_multi_frame(
            b"QSAG.SPDZ.BLIND.T128.DEG/v1",
            &[session_id, phase.as_bytes(), &(offset as u64).to_be_bytes()],
        );
        let w = blind_open_tower128(&sid, phase, &residual, Some(&mut *mesh), rngs)?;
        if !w.ct_eq(Tower128::ZERO) {
            return Err(PreprocessError::DegreeCheckFailed { phase });
        }
    }
    let residual = SecretBuffer(
        shares
            .iter()
            .enumerate()
            .map(|(p, &d)| {
                if p < t {
                    d.mul_gf256(tables.zero[p])
                } else {
                    Tower128::ZERO
                }
            })
            .collect::<Vec<_>>(),
    );
    blind_open_tower128(session_id, phase, &residual, Some(mesh), rngs)
}

fn blinding_mesh(
    session_id: &[u8; 32],
    phase: &'static str,
    party_rngs: &mut [PartyPrivateRng],
) -> Result<OtMesh, PreprocessError> {
    let sid = cshake256_32_multi_frame(b"QSAG.SPDZ.BLIND.OT/v1", &[session_id, phase.as_bytes()]);
    OtMesh::establish(sid, party_rngs)
}

pub(super) fn blind_open_ext2(
    session_id: &[u8; 32],
    phase: &'static str,
    residual: &[GoldilocksExt2],
    mesh: Option<&mut OtMesh>,
    party_rngs: &mut [PartyPrivateRng],
) -> Result<GoldilocksExt2, PreprocessError> {
    let mut owned_mesh;
    let mesh = match mesh {
        Some(mesh) => mesh,
        None => {
            owned_mesh = blinding_mesh(session_id, phase, party_rngs)?;
            &mut owned_mesh
        }
    };
    let n = residual.len();
    // Multiply in the EXTENSION field directly. Splitting into four base-field
    // OLEs would let a malicious peer use inconsistent correlations in the four
    // columns, weakening the extension-field soundness to a base-field event.
    let r = SecretBuffer(
        party_rngs
            .iter_mut()
            .map(PartyPrivateRng::next_ext2)
            .collect::<Vec<_>>(),
    );
    let w = SecretBuffer(ole_blind_ext2(session_id, mesh, &r, residual, party_rngs)?);
    // Represent additive shares as n-of-n Shamir shares using PUBLIC inverse weights.
    let points = (1..=n)
        .map(|p| Goldilocks::from_u64_reduced(p as u64))
        .collect::<Vec<_>>();
    let lambdas = lagrange_weights_zero_goldilocks(&points)
        .ok_or(PreprocessError::DuplicateOrZeroEvalPoint)?;
    let shares = SecretBuffer(
        (0..n)
            .map(|p| w[p].mul_base(lambdas[p].inv()))
            .collect::<Vec<_>>(),
    );
    commit_and_open_degree_ext2(session_id, phase, n, &points, &shares, party_rngs)
}

/// Native-field OLE. The only receiver choices are 640 disposable random bits;
/// neither the residual nor its coordinates ever supply a choice bit. The post-OT
/// hash retains a 384-bit entropy budget after a field-sized error observation
/// and the 128-bit extracted randomizer. Sender errors therefore cannot turn the
/// final opening into probes of residual bits. The public correction derandomizes
/// the extracted mask to the fresh receiver randomizer; it never opens a residual.
fn ole_blind_ext2(
    session_id: &[u8; 32],
    mesh: &mut OtMesh,
    randomizers: &[GoldilocksExt2],
    residuals: &[GoldilocksExt2],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<GoldilocksExt2>, PreprocessError> {
    const WORDS: usize = 10;
    const BITS: usize = 64 * WORDS;
    let n = residuals.len();
    let choices = SecretBuffer(
        party_rngs
            .iter_mut()
            .map(|rng| (0..WORDS).map(|_| rng.next_u64()).collect::<Vec<_>>())
            .collect::<Vec<_>>(),
    );
    let mut raw = SecretBuffer(vec![vec![GoldilocksExt2::ZERO; BITS]; n]);
    let mut bind = Cshake256Xof::new(b"QSAG.SPDZ.BLIND.EXT2.CT/v1");
    for receiver in 0..n {
        for sender in 0..n {
            if sender == receiver {
                continue;
            }
            let (send, recv) =
                mesh.run_correlated_ot_words(sender, receiver, &choices[receiver], party_rngs)?;
            for bit in 0..BITS {
                let decode = |pad: &[u8; 48]| {
                    GoldilocksExt2::new(
                        Goldilocks::from_bytes24_unbiased(&core::array::from_fn(|i| pad[i])),
                        Goldilocks::from_bytes24_unbiased(&core::array::from_fn(|i| pad[24 + i])),
                    )
                };
                let mask = party_rngs[sender].next_ext2();
                let ct0 = decode(&send[bit].0) - mask;
                let ct1 = decode(&send[bit].1) + residuals[sender] - mask;
                bind.absorb(&ct0.to_be_bytes());
                bind.absorb(&ct1.to_be_bytes());
                let choice = (choices[receiver][bit / 64] >> (bit % 64)) & 1;
                let select = 0u64.wrapping_sub(black_box(choice));
                let selected = GoldilocksExt2::new(
                    Goldilocks::from_u64_reduced(
                        ct0.c0.to_canonical_u64()
                            ^ (select & (ct0.c0.to_canonical_u64() ^ ct1.c0.to_canonical_u64())),
                    ),
                    Goldilocks::from_u64_reduced(
                        ct0.c1.to_canonical_u64()
                            ^ (select & (ct0.c1.to_canonical_u64() ^ ct1.c1.to_canonical_u64())),
                    ),
                );
                raw[sender][bit] += mask;
                raw[receiver][bit] += selected - decode(&recv[bit]);
            }
        }
    }
    bind.absorb(&mesh.transcript_digest());
    let mut digest = [0u8; 32];
    bind.squeeze(&mut digest);
    let coin = run_commit_and_open_coin(session_id, b"SPDZ_BLIND_EXT2_LHL", &digest, party_rngs)?;
    let mut xof = Cshake256Xof::new(b"QSAG.SPDZ.BLIND.EXT2.H/v1");
    xof.absorb(&coin);
    let mut extracted = SecretBuffer(vec![GoldilocksExt2::ZERO; n]);
    let mut w = SecretBuffer(vec![GoldilocksExt2::ZERO; n]);
    for bit in 0..BITS {
        let mut bytes = [0u8; 48];
        xof.squeeze(&mut bytes);
        let g = GoldilocksExt2::new(
            Goldilocks::from_bytes24_unbiased(&core::array::from_fn(|i| bytes[i])),
            Goldilocks::from_bytes24_unbiased(&core::array::from_fn(|i| bytes[24 + i])),
        );
        for party in 0..n {
            let select = 0u64.wrapping_sub(black_box((choices[party][bit / 64] >> (bit % 64)) & 1));
            extracted[party] += GoldilocksExt2::new(
                Goldilocks::from_u64_reduced(select & g.c0.to_canonical_u64()),
                Goldilocks::from_u64_reduced(select & g.c1.to_canonical_u64()),
            );
            w[party] += g * raw[party][bit];
        }
    }
    let diffs = SecretBuffer(
        (0..n)
            .map(|p| randomizers[p] - extracted[p])
            .collect::<Vec<_>>(),
    );
    let sum_diff = diffs
        .iter()
        .copied()
        .fold(GoldilocksExt2::ZERO, |a, b| a + b);
    for party in 0..n {
        w[party] += residuals[party] * (randomizers[party] + sum_diff - diffs[party]);
    }
    Ok(w.into_inner())
}

pub(super) fn blind_open_tower128(
    session_id: &[u8; 32],
    phase: &'static str,
    residual: &[Tower128],
    mesh: Option<&mut OtMesh>,
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Tower128, PreprocessError> {
    let mut owned_mesh;
    let mesh = match mesh {
        Some(mesh) => mesh,
        None => {
            owned_mesh = blinding_mesh(session_id, phase, party_rngs)?;
            &mut owned_mesh
        }
    };
    let sender = SecretBuffer(residual.iter().map(|&d| vec![d]).collect::<Vec<_>>());
    let points = (1..=residual.len())
        .map(|p| TowerGf256(p as u8))
        .collect::<Vec<_>>();
    let lambdas =
        lagrange_weights_zero_gf256(&points).ok_or(PreprocessError::DuplicateOrZeroEvalPoint)?;
    // Repeat independently so even a fault confined to ONE MAC lane retains
    // 2^-256 rejection soundness, rather than accepting when one randomizer is zero.
    for _ in 0..2 {
        let receiver = SecretBuffer(
            party_rngs
                .iter_mut()
                .map(|rng| vec![rng.next_tower128()])
                .collect::<Vec<_>>(),
        );
        // Tower OLE's FIRST input is the sender, its SECOND input is the receiver.
        let products = SecretBuffer(pairwise_ole_tower128(
            session_id, mesh, &sender, &receiver, party_rngs,
        )?);
        let shares = SecretBuffer(
            products
                .iter()
                .zip(&lambdas)
                .map(|(w, l)| w[0].mul_gf256(l.inv().expect("nonzero public interpolation weight")))
                .collect::<Vec<_>>(),
        );
        let opened = commit_and_open_degree_tower128(
            session_id,
            phase,
            points.len(),
            &points,
            &shares,
            party_rngs,
        )?;
        if !opened.ct_eq(Tower128::ZERO) {
            return Ok(opened);
        }
    }
    Ok(Tower128::ZERO)
}

/// Entropy-amplified native-field Tower OLE with six independent 128-bit receiver masks.
/// Correlations and ciphertexts are fixed before the field-valued hash coin. The masks
/// supply 128-bit statistical privacy under affine bit errors, up to field-sized
/// MAC-key guessing events; see the module's committed blinding construction.
/// Computes additive shares of `(sum u) * (sum v)` without reconstructing either input.
pub(super) fn pairwise_ole_tower128(
    session_id: &[u8; 32],
    ot_mesh: &mut OtMesh,
    u_per_party: &[Vec<Tower128>],
    v_per_party: &[Vec<Tower128>],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<Vec<Tower128>>, PreprocessError> {
    let n = ot_mesh.n;
    let count = u_per_party[0].len();
    let mut w_per_party: Vec<Vec<Tower128>> = (0..n)
        .map(|i| {
            (0..count)
                .map(|k| u_per_party[i][k].mul(v_per_party[i][k]))
                .collect()
        })
        .collect();
    if count == 0 {
        return Ok(w_per_party);
    }

    // Each party `i` samples `6 * count` uniform `Tower128` OT masks (`12 * count` u64 choice words)
    let mut r_masks = SecretBuffer(vec![vec![[Tower128::ZERO; 6]; count]; n]);
    let mut choice_words = crate::wipe::secret_vecs_with_capacity(n, 12 * count);
    for i in 0..n {
        for k in 0..count {
            for m in 0..6 {
                let r = party_rngs[i].next_tower128();
                r_masks[i][k][m] = r;
                choice_words[i].push(r.0 as u64);
                choice_words[i].push((r.0 >> 64) as u64);
            }
        }
    }

    let mut raw_s = SecretBuffer(vec![vec![vec![[Tower128::ZERO; 6]; count]; n]; n]);
    let mut raw_r = SecretBuffer(vec![vec![vec![[Tower128::ZERO; 6]; count]; n]; n]);
    let mut bind = Cshake256Xof::new(b"QSAG.SPDZ.BLIND.T128.CT/v1");
    for i in 0..n {
        for j in 0..n {
            if i == j {
                continue;
            }
            // Sender `j` inputs `u_j[k]`; Receiver `i` inputs uniform random `r_masks[i][k][0..6]`
            let (send_pads, recv_pads) =
                ot_mesh.run_correlated_ot_words(j, i, &choice_words[i], party_rngs)?;
            for k in 0..count {
                let uj = u_per_party[j][k];
                for m in 0..6 {
                    let rm_raw = black_box(r_masks[i][k][m].0);
                    let mut s_sum = Tower128::ZERO;
                    let mut r_sum = Tower128::ZERO;
                    let base_off = (6 * k + m) * 128;
                    for bit in 0..128 {
                        let (p0, p1) = &send_pads[base_off + bit];
                        let pad0 =
                            Tower128(u128::from_le_bytes(core::array::from_fn(|array_index| {
                                (p0[0..16])[array_index]
                            })));
                        let pad1 =
                            Tower128(u128::from_le_bytes(core::array::from_fn(|array_index| {
                                (p1[0..16])[array_index]
                            })));
                        let mask = party_rngs[j].next_tower128();
                        s_sum = s_sum.add(mask);
                        let basis = Tower128(1u128 << bit);
                        let ct0 = mask.add(pad0);
                        let ct1 = mask.add(uj.mul(basis)).add(pad1);
                        bind.absorb(&ct0.0.to_le_bytes());
                        bind.absorb(&ct1.0.to_le_bytes());

                        let pad_c =
                            Tower128(u128::from_le_bytes(core::array::from_fn(|array_index| {
                                (recv_pads[base_off + bit][0..16])[array_index]
                            })));
                        let choice = ((rm_raw >> bit) & 1) == 1;
                        let cmask = 0u128.wrapping_sub(black_box(choice as u128));
                        let sel = Tower128(ct0.0 ^ (cmask & (ct0.0 ^ ct1.0)));
                        r_sum = r_sum.add(sel.add(pad_c));
                    }
                    raw_s[j][i][k][m] = s_sum;
                    raw_r[j][i][k][m] = r_sum;
                }
            }
        }
    }

    // Post-OT `Π_coin` 2-universal LHL combiner (`768 -> 128` bits) + MASCOT input derandomization
    bind.absorb(&ot_mesh.transcript_digest());
    let mut digest = [0u8; 32];
    bind.squeeze(&mut digest);
    let coin = run_commit_and_open_coin(session_id, b"PCG_OLE_T128_LHL", &digest, party_rngs)?;
    let mut xof = Cshake256Xof::new(b"QSAG.PCG.OLE.T128.LHL/v1");
    xof.absorb(&coin);
    let mut g_weights = vec![[Tower128::ONE; 6]; count];
    for g_weights_k_item in g_weights[..count].iter_mut() {
        for m in 1..6 {
            let mut gb = [0u8; 16];
            xof.squeeze(&mut gb);
            (*g_weights_k_item)[m] = Tower128(u128::from_le_bytes(gb));
        }
    }

    let mut diffs = SecretBuffer(vec![vec![Tower128::ZERO; count]; n]);
    for i in 0..n {
        for k in 0..count {
            let mut r_comb = r_masks[i][k][0];
            for m in 1..6 {
                r_comb = r_comb.add(g_weights[k][m].mul(r_masks[i][k][m]));
            }
            diffs[i][k] = v_per_party[i][k].add(r_comb);
            wipe_tower128(&mut r_masks[i][k]);
        }
        wipe_u64s(&mut choice_words[i]);
    }

    for i in 0..n {
        for j in 0..n {
            if i == j {
                continue;
            }
            for k in 0..count {
                let mut s_comb = raw_s[j][i][k][0];
                let mut r_comb = raw_r[j][i][k][0];
                for m in 1..6 {
                    let g = g_weights[k][m];
                    s_comb = s_comb.add(g.mul(raw_s[j][i][k][m]));
                    r_comb = r_comb.add(g.mul(raw_r[j][i][k][m]));
                }
                // `s_comb + r_comb == u_j * r_comb_i`; add `u_j * (v_i + r_comb_i)` to Sender `j`!
                s_comb = s_comb.add(u_per_party[j][k].mul(diffs[i][k]));
                w_per_party[j][k] = w_per_party[j][k].add(s_comb);
                w_per_party[i][k] = w_per_party[i][k].add(r_comb);
                wipe_tower128(&mut raw_s[j][i][k]);
                wipe_tower128(&mut raw_r[j][i][k]);
            }
        }
    }
    Ok(w_per_party)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rngs(tape: u8) -> Vec<PartyPrivateRng> {
        [tape, 200]
            .into_iter()
            .map(|seed| PartyPrivateRng::from_seed([seed; 32], b"mac-blind-regression"))
            .collect()
    }

    #[test]
    fn unanimous_opening_share_shift_aborts_without_releasing_alpha() {
        let sid = [0x9d; 32];
        let points = [Goldilocks::ONE, Goldilocks::from_u64_reduced(2)];
        let alpha = GoldilocksExt2::new(
            Goldilocks::from_u64_reduced(19),
            Goldilocks::from_u64_reduced(23),
        );
        let x = Goldilocks::from_u64_reduced(41);
        let mut private = rngs(31);
        let alpha_shares = shamir_share_ext2(2, &points, alpha, &mut private[0]);
        let shares = shamir_share_goldilocks(2, &points, x, &mut private[0]);
        let macs = shamir_share_ext2(2, &points, alpha.mul_base(x), &mut private[0]);
        let mut shifted = shares.clone();
        shifted[0] += Goldilocks::ONE;
        assert!(matches!(
            commit_and_open_spdz_goldilocks_quorum(
                &sid,
                "unanimous_shift",
                2,
                &points,
                &shifted,
                &macs,
                &alpha_shares,
                &mut private,
            ),
            Err(PreprocessError::MacCheckFailed { .. })
        ));
        assert_eq!(
            commit_and_open_spdz_goldilocks_quorum(
                &sid,
                "unanimous_honest",
                2,
                &points,
                &shares,
                &macs,
                &alpha_shares,
                &mut private,
            )
            .unwrap(),
            x
        );
    }

    #[test]
    fn degree_consistent_dealer_shift_with_full_redundancy_aborts() {
        let sid = [0x8d; 32];
        let points = (1..=3)
            .map(Goldilocks::from_u64_reduced)
            .collect::<Vec<_>>();
        let mut private = (0..3)
            .map(|p| PartyPrivateRng::from_seed([p + 60; 32], b"dealer-shift"))
            .collect::<Vec<_>>();
        let alpha = GoldilocksExt2::new(
            Goldilocks::from_u64_reduced(19),
            Goldilocks::from_u64_reduced(23),
        );
        let x = Goldilocks::from_u64_reduced(41);
        let keys = shamir_share_ext2(2, &points, alpha, &mut private[0]);
        let macs = shamir_share_ext2(2, &points, alpha.mul_base(x), &mut private[0]);
        let mut shares = shamir_share_goldilocks(2, &points, x, &mut private[0]);
        for share in &mut shares {
            *share += Goldilocks::ONE;
        }
        assert_eq!(
            open_and_check_degree_goldilocks(2, &points, &shares, "dealer_shift").unwrap(),
            x + Goldilocks::ONE
        );
        assert!(matches!(
            commit_and_open_spdz_goldilocks_quorum(
                &sid,
                "dealer_shift",
                2,
                &points,
                &shares,
                &macs,
                &keys,
                &mut private,
            ),
            Err(PreprocessError::MacCheckFailed { .. })
        ));
    }

    #[test]
    fn degree_consistent_three_of_four_shift_aborts() {
        let sid = [0x8e; 32];
        let points = (1..=4)
            .map(Goldilocks::from_u64_reduced)
            .collect::<Vec<_>>();
        let mut private = (0..4)
            .map(|p| PartyPrivateRng::from_seed([p + 70; 32], b"three-of-four"))
            .collect::<Vec<_>>();
        let alpha = GoldilocksExt2::new(
            Goldilocks::from_u64_reduced(19),
            Goldilocks::from_u64_reduced(23),
        );
        let x = Goldilocks::from_u64_reduced(41);
        let keys = shamir_share_ext2(3, &points, alpha, &mut private[0]);
        let macs = shamir_share_ext2(3, &points, alpha.mul_base(x), &mut private[0]);
        let mut shares = shamir_share_goldilocks(3, &points, x, &mut private[0]);
        // The two corrupt points shift by a quadratic that vanishes at both
        // honest points. All four values STILL have degree <3, but x moves by 12.
        for p in 0..2 {
            shares[p] += (points[p] - points[2]) * (points[p] - points[3]);
        }
        assert_eq!(
            open_and_check_degree_goldilocks(3, &points, &shares, "coalition").unwrap(),
            x + Goldilocks::from_u64_reduced(12)
        );
        assert!(matches!(
            commit_and_open_spdz_goldilocks_quorum(
                &sid,
                "three_of_four_shift",
                3,
                &points,
                &shares,
                &macs,
                &keys,
                &mut private,
            ),
            Err(PreprocessError::MacCheckFailed { .. })
        ));
    }

    #[test]
    fn private_degree_checks_reject_mac_tampering_at_an_extra_recipient() {
        let sid = [0x81; 32];
        let mut private = (0..4)
            .map(|p| PartyPrivateRng::from_seed([p + 80; 32], b"private-degree"))
            .collect::<Vec<_>>();
        let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut private);
        let points = (1..=4)
            .map(Goldilocks::from_u64_reduced)
            .collect::<Vec<_>>();
        let mut shares = shamir_share_ext2(3, &points, GoldilocksExt2::ZERO, &mut private[0]);
        assert_eq!(
            blind_open_degree_ext2(
                &sid,
                "private_degree_honest",
                3,
                &points,
                &shares,
                &mut mesh,
                &mut private
            )
            .unwrap(),
            GoldilocksExt2::ZERO
        );
        shares[3] += GoldilocksExt2::ONE;
        assert!(matches!(
            blind_open_degree_ext2(
                &sid,
                "private_degree",
                3,
                &points,
                &shares,
                &mut mesh,
                &mut private
            ),
            Err(PreprocessError::DegreeCheckFailed { .. })
        ));
        let points = (1..=4).map(TowerGf256).collect::<Vec<_>>();
        let mut shares = shamir_share_tower128(3, &points, Tower128::ZERO, &mut private[0]);
        assert_eq!(
            blind_open_degree_tower128(
                &sid,
                "private_degree_honest",
                3,
                &points,
                &shares,
                &mut mesh,
                &mut private
            )
            .unwrap(),
            Tower128::ZERO
        );
        shares[3] = shares[3].add(Tower128::ONE);
        assert!(matches!(
            blind_open_degree_tower128(
                &sid,
                "private_degree",
                3,
                &points,
                &shares,
                &mut mesh,
                &mut private
            ),
            Err(PreprocessError::DegreeCheckFailed { .. })
        ));
    }

    #[test]
    fn unanimous_boolean_share_shift_aborts() {
        let sid = [0x7e; 32];
        let points = [TowerGf256(1), TowerGf256(2)];
        let mats = points
            .iter()
            .map(|&p| PublicGf256Matrix::from_public_scalar(p))
            .collect::<Vec<_>>();
        let alpha = [Tower128(0x123456), Tower128(0x987654)];
        let mut private = rngs(51);
        let mut alpha_shares = vec![[Tower128::ZERO; 2]; 2];
        let mut macs = vec![[[Tower128::ZERO; 64]; 2]; 2];
        for lane in 0..2 {
            let key = shamir_share_tower128(2, &points, alpha[lane], &mut private[0]);
            for p in 0..2 {
                alpha_shares[p][lane] = key[p];
            }
            #[expect(
                clippy::needless_range_loop,
                reason = "Each bit indexes the same lane in both parties' MAC arrays"
            )]
            for bit in 0..64 {
                let mac = shamir_share_tower128(
                    2,
                    &points,
                    alpha[lane].mul_gf256(TowerGf256(((42u64 >> bit) & 1) as u8)),
                    &mut private[0],
                );
                for p in 0..2 {
                    macs[p][lane][bit] = mac[p];
                }
            }
        }
        let mut shares = shamir_share_bits64_gf256_mats(2, &mats, 42, &mut private[0]);
        shares[0][0] ^= 1;
        assert!(matches!(
            commit_and_open_spdz_bs_gf256_quorum(
                &sid,
                "unanimous_boolean_shift",
                2,
                &points,
                &shares,
                &macs,
                &alpha_shares,
                &mut private,
            ),
            Err(PreprocessError::MacCheckFailed { .. })
        ));
    }

    #[test]
    fn repeated_aborts_with_fixed_alpha_open_fresh_field_permutations() {
        let sid = [0x4b; 32];
        let alpha = GoldilocksExt2::new(
            Goldilocks::from_u64_reduced(19),
            Goldilocks::from_u64_reduced(23),
        );
        let d = -alpha.mul_base(Goldilocks::from_u64_reduced(17));
        let residual = [d - GoldilocksExt2::ONE, GoldilocksExt2::ONE];
        let mut seen = Vec::new();
        for tape in 1..=16 {
            let mut private = rngs(tape);
            let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut private);
            let mut reference = rngs(tape);
            let _ = OtMesh::establish_ideal_for_test(sid, &mut reference);
            let r = reference[0].next_ext2() + reference[1].next_ext2();
            let w = blind_open_ext2(
                &sid,
                "fixed_alpha_abort",
                &residual,
                Some(&mut mesh),
                &mut private,
            )
            .unwrap();
            assert_eq!(w, r * d, "OLE must open exactly the blinded residual");
            assert!(!w.ct_eq(GoldilocksExt2::ZERO));
            assert!(!w.ct_eq(d), "raw -delta*alpha residual escaped");
            assert!(!seen.contains(&w), "random tapes reused a check value");
            seen.push(w);
        }
        // Algebraic distribution check, beyond a sampling assertion: multiplication
        // by either nonzero residual is bijective. For a fixed corrupt contribution,
        // the honest randomizer that yields any target w exists and is unique.
        let other = d + GoldilocksExt2::ONE;
        let corrupt_r = GoldilocksExt2::new(Goldilocks::ONE, Goldilocks::from_u64_reduced(7));
        for target in seen {
            for residual in [d, other] {
                let honest_r = target * residual.inv().unwrap() - corrupt_r;
                assert_eq!((honest_r + corrupt_r) * residual, target);
            }
        }
    }

    #[test]
    fn tower_blinding_is_multiplication_with_receiver_randomness() {
        let sid = [0x3c; 32];
        let mut seen = Vec::new();
        for tape in 1..=8 {
            let mut private = rngs(tape);
            let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut private);
            let w = blind_open_tower128(
                &sid,
                "tower_abort",
                &[Tower128(0x1234), Tower128(0x9876)],
                Some(&mut mesh),
                &mut private,
            )
            .unwrap();
            assert_ne!(w, Tower128::ZERO);
            assert!(!seen.contains(&w));
            seen.push(w);
        }
        let mut private = rngs(42);
        let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut private);
        assert_eq!(
            blind_open_tower128(
                &sid,
                "tower_zero",
                &[Tower128(7), Tower128(7)],
                Some(&mut mesh),
                &mut private
            )
            .unwrap(),
            Tower128::ZERO
        );
    }
}
