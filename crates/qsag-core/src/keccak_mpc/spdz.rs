use super::*;

// ============================================================================
// 2. Dishonest-Majority $t$-of-$n$ SPDZ Shamir `Keccak-f[1600]` & `SlhMpcOracles`
// ============================================================================

#[inline]
fn rotate_bs_gf256_lanes_left(w: &BitslicedGf256x64, r: u32) -> BitslicedGf256x64 {
    core::array::from_fn(|pl| w[pl].rotate_left(r))
}

#[inline]
fn rotate_spdz_macs_left(m: &[[Tower128; 64]; 2], r: u32) -> [[Tower128; 64]; 2] {
    let shift = (r as usize) & 63;
    if shift == 0 {
        return *m;
    }
    let mut out = [[Tower128::ZERO; 64]; 2];
    for lane in 0..2 {
        for src in 0..64 {
            out[lane][(src + shift) & 63] = m[lane][src];
        }
    }
    out
}

#[inline]
fn xor_spdz_macs_assign(dst: &mut [[Tower128; 64]; 2], rhs: &[[Tower128; 64]; 2]) {
    for lane in 0..2 {
        for bit in 0..64 {
            dst[lane][bit].0 ^= rhs[lane][bit].0;
        }
    }
}

#[inline]
pub(crate) fn add_public_u64_to_spdz_word(
    pub_word: u64,
    sh: &mut BitslicedGf256x64,
    mac: &mut [[Tower128; 64]; 2],
    alpha_share: &[Tower128; 2],
) {
    // In Shamir over `TowerGf256`, constant polynomial `f(X) = c` evaluates to `c` at every point!
    sh[0] ^= pub_word;
    let mut bit = 0;
    while bit < 64 {
        let mask = 0u128.wrapping_sub(((pub_word >> bit) & 1) as u128);
        mac[0][bit].0 ^= mask & alpha_share[0].0;
        mac[1][bit].0 ^= mask & alpha_share[1].0;
        bit += 1;
    }
}

/// MAC update for a Beaver product, with the 128 coefficients of each tag
/// transposed into planes. Each GF(256) multiply handles all 64 sponge lanes.
pub(super) fn beaver_mac_planes(
    c: &SpdzMacWord,
    b: &SpdzMacWord,
    a: &SpdzMacWord,
    alpha: &[Tower128; 2],
    d: &BitslicedGf256x64,
    e: &BitslicedGf256x64,
    de: &BitslicedGf256x64,
) -> SpdzMacWord {
    // Valid Boolean circuit openings have only plane zero. Public bit masks
    // scale the entire tag directly; retain the field-plane path for arbitrary
    // GF(256) inputs and malformed openings (which the MAC barrier rejects).
    if d[1..].iter().chain(&e[1..]).all(|&plane| plane == 0) {
        return core::array::from_fn(|ml| {
            core::array::from_fn(|i| {
                let dm = 0u128.wrapping_sub(u128::from((d[0] >> i) & 1));
                let em = 0u128.wrapping_sub(u128::from((e[0] >> i) & 1));
                Tower128(
                    c[ml][i].0 ^ (b[ml][i].0 & dm) ^ (a[ml][i].0 & em) ^ (alpha[ml].0 & dm & em),
                )
            })
        });
    }
    let planes = |mac: &SpdzMacWord| {
        SecretBuffer(core::array::from_fn::<_, 64, _>(|i| {
            [
                mac[0][i].0 as u64,
                (mac[0][i].0 >> 64) as u64,
                mac[1][i].0 as u64,
                (mac[1][i].0 >> 64) as u64,
            ]
        }))
    };
    let mut bp = planes(b);
    let mut ap = planes(a);
    qsag_asm::transpose64x256(&mut bp);
    qsag_asm::transpose64x256(&mut ap);
    for col in 0..4 {
        for byte in 0..8 {
            let bb = core::array::from_fn(|bit| bp[8 * byte + bit][col]);
            let aa = core::array::from_fn(|bit| ap[8 * byte + bit][col]);
            let alpha_byte = (alpha[col / 2].0 >> (64 * (col % 2) + 8 * byte)) as u8;
            let alph =
                core::array::from_fn(|bit| 0u64.wrapping_sub(u64::from((alpha_byte >> bit) & 1)));
            let db = bs_gf256_mul_planes_ct(d, &bb);
            let ea = bs_gf256_mul_planes_ct(e, &aa);
            let public = bs_gf256_mul_planes_ct(de, &alph);
            for bit in 0..8 {
                bp[8 * byte + bit][col] = db[bit] ^ ea[bit] ^ public[bit];
            }
        }
    }
    qsag_asm::transpose64x256(&mut bp);
    core::array::from_fn(|ml| {
        core::array::from_fn(|i| {
            Tower128(c[ml][i].0 ^ u128::from(bp[i][2 * ml]) ^ (u128::from(bp[i][2 * ml + 1]) << 64))
        })
    })
}

/// Commit-before-open + full `0..m` Shamir degree-`< t` opening for Beaver masked `(d, e)` words,
/// appending `(opened_word, mac_shares)` to `pending_mac_words` and `pending_mac_tags` for the
/// pre-cut 2-lane `Tower128` SPDZ `MacCheck` barrier (`[P0-08]`).
#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the existing explicit protocol interface for callers"
)]
fn commit_and_open_beaver_de_batch(
    session_id: &[u8; 32],
    round_idx: usize,
    t: usize,
    quorum_pts: &[TowerGf256],
    de_shares: &[Vec<BitslicedGf256x64>],
    de_macs: &[Vec<[[Tower128; 64]; 2]>],
    pending_opened: &mut Vec<BitslicedGf256x64>,
    pending_macs: &mut [Vec<[[Tower128; 64]; 2]>],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<BitslicedGf256x64>, PreprocessError> {
    let m = quorum_pts.len();
    let batch_len = de_shares[0].len();

    let mut salts = Vec::with_capacity(m);
    let mut coms = Vec::with_capacity(m);
    for p in 0..m {
        let salt = party_rngs[p].next_bytes32();
        let mut xof = Cshake256Xof::new(b"QSAG.SPDZ.KECCAK.DE.COM/v1");
        xof.absorb(session_id);
        xof.absorb(&(round_idx as u64).to_be_bytes());
        xof.absorb(&(p as u64).to_be_bytes());
        xof.absorb(&salt);
        let mut w = 0;
        while w < batch_len {
            let mut pl = 0;
            while pl < 8 {
                xof.absorb(&de_shares[p][w][pl].to_le_bytes());
                pl += 1;
            }
            w += 1;
        }
        let mut com = [0u8; 32];
        xof.squeeze(&mut com);
        salts.push(salt);
        coms.push(com);
    }

    for p in 0..m {
        let mut xof = Cshake256Xof::new(b"QSAG.SPDZ.KECCAK.DE.COM/v1");
        xof.absorb(session_id);
        xof.absorb(&(round_idx as u64).to_be_bytes());
        xof.absorb(&(p as u64).to_be_bytes());
        xof.absorb(&salts[p]);
        let mut w = 0;
        while w < batch_len {
            let mut pl = 0;
            while pl < 8 {
                xof.absorb(&de_shares[p][w][pl].to_le_bytes());
                pl += 1;
            }
            w += 1;
        }
        wipe_bytes32(&mut salts[p]);
        let mut exp = [0u8; 32];
        xof.squeeze(&mut exp);
        if !ct_eq_bytes32(&exp, &coms[p]) {
            return Err(PreprocessError::ShareCommitMismatch {
                phase: "spdz_keccak_chi_de",
                party_id: p,
            });
        }
    }

    let mut opened = Vec::with_capacity(batch_len);
    let mut single_sh = SecretBuffer(vec![[0u64; 8]; m]);
    let opening_tables = crate::preprocessing::Gf256OpeningTables::new(t, quorum_pts)?;
    for w in 0..batch_len {
        for p in 0..m {
            single_sh[p] = de_shares[p][w];
            secret_vec_push(&mut pending_macs[p], de_macs[p][w]);
        }
        let val = opening_tables.open_bitsliced(&single_sh, "spdz_keccak_chi_de")?;
        pending_opened.push(val);
        opened.push(val);
    }
    for s in single_sh.iter_mut() {
        wipe_u64s(s);
    }
    Ok(opened)
}

/// Folded 2-lane `Tower128` SPDZ `MacCheck` (`2^{-256}` soundness) verifying all accumulated Beaver
/// openings `pending_opened` **strictly before** any party reveals its cut-boundary output share!
#[expect(
    clippy::too_many_arguments,
    reason = "The authenticated batch and retained OT mesh are separate protocol inputs"
)]
pub(crate) fn verify_pending_spdz_mac_batch_with_mesh(
    session_id: &[u8; 32],
    phase: &'static str,
    t: usize,
    quorum_pts: &[TowerGf256],
    pending_opened: &[BitslicedGf256x64],
    pending_macs: &[Vec<[[Tower128; 64]; 2]>],
    alpha_shares: &[[Tower128; 2]],
    party_rngs: &mut [PartyPrivateRng],
    mut mesh: Option<&mut OtMesh>,
) -> Result<(), PreprocessError> {
    let n = quorum_pts.len();
    if t == 0
        || t > n
        || pending_macs.len() != n
        || alpha_shares.len() != n
        || party_rngs.len() != n
        || pending_macs.iter().any(|m| m.len() != pending_opened.len())
    {
        return Err(PreprocessError::InvalidThreshold { t, n });
    }
    crate::preprocessing::validate_all_eval_points_gf256(quorum_pts)?;
    if pending_opened.is_empty() {
        return Ok(());
    }
    let lambdas_0 = lagrange_weights_zero_gf256(&quorum_pts[..t])
        .ok_or(PreprocessError::DuplicateOrZeroEvalPoint)?;

    let mut dig_xof = Cshake256Xof::new(b"QSAG.SPDZ.KECCAK.PEND.DIG/v1");
    for w in pending_opened {
        let mut pl = 0;
        while pl < 8 {
            dig_xof.absorb(&w[pl].to_le_bytes());
            pl += 1;
        }
    }
    let mut open_digest = [0u8; 32];
    dig_xof.squeeze(&mut open_digest);

    let fold_coin =
        run_commit_and_open_coin(session_id, phase.as_bytes(), &open_digest, party_rngs)?;
    let (x_folded, mut m_folded) =
        crate::preprocessing::fold_spdz_mac_words(&fold_coin, pending_opened, pending_macs, t);

    // Additive masking alone cancels in the aggregate and leaks alpha on abort.
    // Keep residuals private and open only independently multiplicatively blinded lanes.
    let mut verdict = Ok(());
    for lane in 0..2 {
        let residual = SecretBuffer(
            (0..n)
                .map(|q| {
                    if q < t {
                        m_folded[q][lane]
                            .add(alpha_shares[q][lane].mul(x_folded[lane]))
                            .mul_gf256(lambdas_0[q])
                    } else {
                        Tower128::ZERO
                    }
                })
                .collect::<Vec<_>>(),
        );
        let sid = cshake256_32_multi_frame(
            b"QSAG.SPDZ.KECCAK.PEND.MAC.COM/v1",
            &[
                session_id,
                phase.as_bytes(),
                b"blinded-lane",
                &(lane as u64).to_be_bytes(),
                &fold_coin,
            ],
        );
        let opened = crate::preprocessing::blind_open_tower128(
            &sid,
            phase,
            &residual,
            mesh.as_deref_mut(),
            party_rngs,
        );
        verdict = match opened {
            Ok(w) if w.ct_eq(Tower128::ZERO) => Ok(()),
            Ok(_) => Err(PreprocessError::MacCheckFailed {
                phase,
                accused_party: None,
            }),
            Err(e) => Err(e),
        };
        if verdict.is_err() {
            break;
        }
    }
    // Folded MAC shares are wiped on the abort paths too.
    for row in m_folded.iter_mut() {
        wipe_tower128(row);
    }
    verdict
}

/// A vault poisoned by an earlier abort has a zeroed MAC key share, so no MAC relation
/// checked against it means anything. If any vault of the quorum is poisoned, the rest are
/// poisoned too and the call is refused before anything is evaluated or opened.
fn spdz_refuse_poisoned_vaults(
    vaults: &mut [PreprocessedKeccakPartyVault],
) -> Result<(), KeccakMpcError> {
    if vaults.iter().any(|v| v.poisoned) {
        for v in vaults.iter_mut() {
            v.poison_and_wipe();
        }
        return Err(KeccakMpcError::Poisoned);
    }
    Ok(())
}

/// Evaluate one 24-round `Keccak-f[1600]` permutation in dishonest-majority $t$-of-$n$ SPDZ Shamir
/// over `25` intra-sponge 64-bit `BitslicedGf256x64` lanes (`600` `KeccakBitTripleShare64` words!),
/// propagating exact 2-lane `Tower128` SPDZ MAC shares across $\theta, \rho, \pi, \chi, \iota$.
///
/// On ANY commitment/degree failure, poisons and wipes ALL vaults immediately (`[P0-07]`).
#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the existing explicit protocol interface for callers"
)]
pub fn eval_spdz_keccak_f1600_single(
    session_id: &[u8; 32],
    perm_ctr: usize,
    t: usize,
    quorum_pts: &[TowerGf256],
    states_sh: &mut [[BitslicedGf256x64; 25]],
    states_mac: &mut [[[[Tower128; 64]; 2]; 25]],
    vaults: &mut [PreprocessedKeccakPartyVault],
    pending_opened: &mut Vec<BitslicedGf256x64>,
    pending_macs: &mut [Vec<[[Tower128; 64]; 2]>],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<(), KeccakMpcError> {
    let m = quorum_pts.len();
    if t == 0
        || m < t
        || states_sh.len() != m
        || states_mac.len() != m
        || vaults.len() != m
        || pending_macs.len() != m
        || party_rngs.len() != m
    {
        return Err(KeccakMpcError::InvalidParameters);
    }
    validate_all_eval_points_gf256(quorum_pts)?;
    spdz_refuse_poisoned_vaults(vaults)?;

    for (rnd, &rc) in KECCAK_ROUND_CONSTANTS.iter().enumerate() {
        // 1. Theta + Rho + Pi on shares AND 2-lane `Tower128` SPDZ MACs
        let mut b_sh = SecretBuffer(vec![[[0u64; 8]; 25]; m]);
        let mut b_mac = SecretBuffer(vec![[[[Tower128::ZERO; 64]; 2]; 25]; m]);

        for p in 0..m {
            let mut c_sh = [[0u64; 8]; 5];
            let mut c_mac = [[[Tower128::ZERO; 64]; 2]; 5];
            for x in 0..5 {
                for y in 0..5 {
                    bs_gf256_xor_assign(&mut c_sh[x], &states_sh[p][x + 5 * y]);
                    xor_spdz_macs_assign(&mut c_mac[x], &states_mac[p][x + 5 * y]);
                }
            }
            for x in 0..5 {
                let d_sh = bs_gf256_xor(
                    &c_sh[(x + 4) % 5],
                    &rotate_bs_gf256_lanes_left(&c_sh[(x + 1) % 5], 1),
                );
                let mut d_mac = c_mac[(x + 4) % 5];
                let rot_m = rotate_spdz_macs_left(&c_mac[(x + 1) % 5], 1);
                xor_spdz_macs_assign(&mut d_mac, &rot_m);

                for y in 0..5 {
                    bs_gf256_xor_assign(&mut states_sh[p][x + 5 * y], &d_sh);
                    xor_spdz_macs_assign(&mut states_mac[p][x + 5 * y], &d_mac);
                }
            }
            for source in 0..25 {
                let x = source % 5;
                let y = source / 5;
                let target = y + 5 * ((2 * x + 3 * y) % 5);
                let rot = KECCAK_ROTATION_OFFSETS[source];
                b_sh[p][target] = rotate_bs_gf256_lanes_left(&states_sh[p][source], rot);
                b_mac[p][target] = rotate_spdz_macs_left(&states_mac[p][source], rot);
            }
        }

        // 2. Chi: 25 parallel Beaver AND words (`50` masked words opened in 1 round!)
        let mut de_sh = secret_vecs_with_capacity(m, 50);
        let mut de_mac = secret_vecs_with_capacity(m, 50);
        let mut round_triples_a = SecretBuffer(vec![[[0u64; 8]; 25]; m]);
        let mut round_triples_b = SecretBuffer(vec![[[0u64; 8]; 25]; m]);
        let mut round_triples_c = SecretBuffer(vec![[[0u64; 8]; 25]; m]);
        let mut round_mac_a = SecretBuffer(vec![[[[Tower128::ZERO; 64]; 2]; 25]; m]);
        let mut round_mac_b = SecretBuffer(vec![[[[Tower128::ZERO; 64]; 2]; 25]; m]);
        let mut round_mac_c = SecretBuffer(vec![[[[Tower128::ZERO; 64]; 2]; 25]; m]);

        for lane in 0..25 {
            let x = lane % 5;
            let y = lane / 5;
            let u_lane = 5 * y + ((x + 1) % 5);
            let v_lane = 5 * y + ((x + 2) % 5);

            for p in 0..m {
                let alpha_p = vaults[p].mac_alpha_lanes;
                let tr = match vaults[p].pop_triple() {
                    Ok(t_ref) => t_ref,
                    Err(e) => {
                        for v in vaults.iter_mut() {
                            v.poison_and_wipe();
                        }
                        return Err(KeccakMpcError::Preprocess(e));
                    }
                };
                round_triples_a[p][lane] = tr.a;
                round_triples_b[p][lane] = tr.b;
                round_triples_c[p][lane] = tr.c;
                round_mac_a[p][lane] = tr.a_mac;
                round_mac_b[p][lane] = tr.b_mac;
                round_mac_c[p][lane] = tr.c_mac;

                let mut not_u_sh = b_sh[p][u_lane];
                let mut not_u_mac = b_mac[p][u_lane];
                add_public_u64_to_spdz_word(u64::MAX, &mut not_u_sh, &mut not_u_mac, &alpha_p);

                let d_w = bs_gf256_xor(&not_u_sh, &round_triples_a[p][lane]);
                let mut d_m = not_u_mac;
                xor_spdz_macs_assign(&mut d_m, &round_mac_a[p][lane]);

                let e_w = bs_gf256_xor(&b_sh[p][v_lane], &round_triples_b[p][lane]);
                let mut e_m = b_mac[p][v_lane];
                xor_spdz_macs_assign(&mut e_m, &round_mac_b[p][lane]);

                secret_vec_push(&mut de_sh[p], d_w);
                secret_vec_push(&mut de_sh[p], e_w);
                secret_vec_push(&mut de_mac[p], d_m);
                secret_vec_push(&mut de_mac[p], e_m);
            }
        }

        let de_opened = match commit_and_open_beaver_de_batch(
            session_id,
            perm_ctr * 24 + rnd,
            t,
            quorum_pts,
            &de_sh,
            &de_mac,
            pending_opened,
            pending_macs,
            party_rngs,
        ) {
            Ok(v) => v,
            Err(e) => {
                for v in vaults.iter_mut() {
                    v.poison_and_wipe();
                }
                return Err(KeccakMpcError::Preprocess(e));
            }
        };

        for lane in 0..25 {
            let d_pub = &de_opened[2 * lane];
            let e_pub = &de_opened[2 * lane + 1];
            let de_pub = bs_gf256_mul_planes_ct(d_pub, e_pub);

            for p in 0..m {
                let db = bs_gf256_mul_planes_ct(d_pub, &round_triples_b[p][lane]);
                let ea = bs_gf256_mul_planes_ct(e_pub, &round_triples_a[p][lane]);
                // Note: `de_pub` is a public `BitslicedGf256x64` constant (plane 0..7), added identically
                // to every party's Shamir share (`f(X) = de_pub` has degree 0)!
                let mut prod_sh = bs_gf256_xor(&round_triples_c[p][lane], &db);
                bs_gf256_xor_assign(&mut prod_sh, &ea);
                bs_gf256_xor_assign(&mut prod_sh, &de_pub);

                let alpha_p = vaults[p].mac_alpha_lanes;
                let prod_mac = beaver_mac_planes(
                    &round_mac_c[p][lane],
                    &round_mac_b[p][lane],
                    &round_mac_a[p][lane],
                    &alpha_p,
                    d_pub,
                    e_pub,
                    &de_pub,
                );

                states_sh[p][lane] = bs_gf256_xor(&b_sh[p][lane], &prod_sh);
                states_mac[p][lane] = b_mac[p][lane];
                xor_spdz_macs_assign(&mut states_mac[p][lane], &prod_mac);

                wipe_u64s(&mut round_triples_a[p][lane]);
                wipe_u64s(&mut round_triples_b[p][lane]);
                wipe_u64s(&mut round_triples_c[p][lane]);
            }
        }

        // 3. Iota: XOR public round constant `rc` into lane `0`
        for p in 0..m {
            let alpha_p = vaults[p].mac_alpha_lanes;
            add_public_u64_to_spdz_word(rc, &mut states_sh[p][0], &mut states_mac[p][0], &alpha_p);
        }
    }
    Ok(())
}

/// Bit positions of one `Keccak-f[1600]` state in the instance-bitsliced layout.
pub(super) const SPDZ_BATCH_POSITIONS: usize = 1600;

/// Evaluate 64 independent 24-round `Keccak-f[1600]` permutations in dishonest-majority
/// $t$-of-$n$ SPDZ Shamir, bitsliced across sponge instances.
///
/// `states_sh[p][lane * 64 + z]` holds party `p`'s `TowerGf256` Shamir shares of state bit
/// `(lane, z)` for all 64 instances (bit `i` of plane `k` is bit `k` of instance `i`'s share), and
/// `states_mac[p][lane * 64 + z][l][i]` the matching lane-`l` MAC share of instance `i`.
/// - Theta, rho and pi are word XORs and index moves on shares and MAC shares alike.
/// - Chi consumes `1600` 64-way Beaver triple words per round, so one bit of every triple word
///   serves one instance, and opens all `3200` masked words of the round in one
///   commit-then-open step shared by the 64 instances.
/// - Every opened word and its MAC shares are appended to `pending_opened` / `pending_macs`;
///   the caller must pass the batched `MacCheck` before any output share is revealed.
///
/// On ANY commitment/degree failure, poisons and wipes ALL vaults immediately (`[P0-07]`).
#[expect(
    clippy::too_many_arguments,
    reason = "Same explicit protocol interface as the single-instance evaluator"
)]
pub fn eval_spdz_keccak_f1600_batch64(
    session_id: &[u8; 32],
    perm_ctr: usize,
    t: usize,
    quorum_pts: &[TowerGf256],
    states_sh: &mut [Vec<BitslicedGf256x64>],
    states_mac: &mut [Vec<SpdzMacWord>],
    vaults: &mut [PreprocessedKeccakPartyVault],
    pending_opened: &mut Vec<BitslicedGf256x64>,
    pending_macs: &mut [Vec<SpdzMacWord>],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<(), KeccakMpcError> {
    const N: usize = SPDZ_BATCH_POSITIONS;
    const ZERO_MAC: SpdzMacWord = [[Tower128::ZERO; 64]; 2];
    let m = quorum_pts.len();
    if t == 0
        || m < t
        || states_sh.len() != m
        || states_mac.len() != m
        || vaults.len() != m
        || pending_macs.len() != m
        || party_rngs.len() != m
        || states_sh.iter().any(|s| s.len() != N)
        || states_mac.iter().any(|s| s.len() != N)
    {
        return Err(KeccakMpcError::InvalidParameters);
    }
    validate_all_eval_points_gf256(quorum_pts)?;
    spdz_refuse_poisoned_vaults(vaults)?;

    let mut b_sh = SecretBuffer(vec![vec![[0u64; 8]; N]; m]);
    let mut b_mac = SecretBuffer(vec![vec![ZERO_MAC; N]; m]);
    let mut col_sh = SecretBuffer(vec![[0u64; 8]; 320]);
    let mut col_mac = SecretBuffer(vec![ZERO_MAC; 320]);
    let mut d_sh = SecretBuffer(vec![[0u64; 8]; 320]);
    let mut d_mac = SecretBuffer(vec![ZERO_MAC; 320]);
    let mut tr_a = SecretBuffer(vec![vec![[0u64; 8]; N]; m]);
    let mut tr_b = SecretBuffer(vec![vec![[0u64; 8]; N]; m]);
    let mut tr_c = SecretBuffer(vec![vec![[0u64; 8]; N]; m]);
    let mut mac_a = SecretBuffer(vec![vec![ZERO_MAC; N]; m]);
    let mut mac_b = SecretBuffer(vec![vec![ZERO_MAC; N]; m]);
    let mut mac_c = SecretBuffer(vec![vec![ZERO_MAC; N]; m]);
    let mut de_sh = secret_vecs_with_capacity(m, 2 * N);
    let mut de_mac = secret_vecs_with_capacity(m, 2 * N);

    for (rnd, &rc) in KECCAK_ROUND_CONSTANTS.iter().enumerate() {
        // 1. Theta + Rho + Pi on shares and MAC shares: no rotation inside a word, only moves.
        for p in 0..m {
            for x in 0..5 {
                for z in 0..64 {
                    let mut cs = [0u64; 8];
                    let mut cm = ZERO_MAC;
                    for y in 0..5 {
                        let idx = (x + 5 * y) * 64 + z;
                        bs_gf256_xor_assign(&mut cs, &states_sh[p][idx]);
                        xor_spdz_macs_assign(&mut cm, &states_mac[p][idx]);
                    }
                    col_sh[x * 64 + z] = cs;
                    col_mac[x * 64 + z] = cm;
                }
            }
            for x in 0..5 {
                for z in 0..64 {
                    let prev = ((x + 4) % 5) * 64 + z;
                    let next = ((x + 1) % 5) * 64 + ((z + 63) & 63);
                    d_sh[x * 64 + z] = bs_gf256_xor(&col_sh[prev], &col_sh[next]);
                    d_mac[x * 64 + z] = col_mac[prev];
                    xor_spdz_macs_assign(&mut d_mac[x * 64 + z], &col_mac[next]);
                }
            }
            for (source, rot) in KECCAK_ROTATION_OFFSETS.iter().enumerate() {
                let x = source % 5;
                let y = source / 5;
                let target = y + 5 * ((2 * x + 3 * y) % 5);
                let rot = *rot as usize;
                for z in 0..64 {
                    let src_z = (z + 64 - rot) & 63;
                    let src = source * 64 + src_z;
                    let dst = target * 64 + z;
                    b_sh[p][dst] = bs_gf256_xor(&states_sh[p][src], &d_sh[x * 64 + src_z]);
                    b_mac[p][dst] = states_mac[p][src];
                    xor_spdz_macs_assign(&mut b_mac[p][dst], &d_mac[x * 64 + src_z]);
                }
            }
        }

        // 2. Chi: one Beaver triple word per state bit; all masked words open together.
        for p in 0..m {
            de_sh[p].clear();
            de_mac[p].clear();
        }
        for idx in 0..N {
            let lane = idx / 64;
            let z = idx % 64;
            let row = 5 * (lane / 5);
            let u = (row + (lane + 1) % 5) * 64 + z;
            let v = (row + (lane + 2) % 5) * 64 + z;
            for p in 0..m {
                let alpha_p = vaults[p].mac_alpha_lanes;
                let tr = match vaults[p].pop_triple() {
                    Ok(t_ref) => t_ref,
                    Err(e) => {
                        for vault in vaults.iter_mut() {
                            vault.poison_and_wipe();
                        }
                        return Err(KeccakMpcError::Preprocess(e));
                    }
                };
                tr_a[p][idx] = tr.a;
                tr_b[p][idx] = tr.b;
                tr_c[p][idx] = tr.c;
                mac_a[p][idx] = tr.a_mac;
                mac_b[p][idx] = tr.b_mac;
                mac_c[p][idx] = tr.c_mac;

                let mut not_u_sh = b_sh[p][u];
                let mut not_u_mac = b_mac[p][u];
                add_public_u64_to_spdz_word(u64::MAX, &mut not_u_sh, &mut not_u_mac, &alpha_p);

                let mut d_m = not_u_mac;
                xor_spdz_macs_assign(&mut d_m, &mac_a[p][idx]);
                let mut e_m = b_mac[p][v];
                xor_spdz_macs_assign(&mut e_m, &mac_b[p][idx]);
                secret_vec_push(&mut de_sh[p], bs_gf256_xor(&not_u_sh, &tr_a[p][idx]));
                secret_vec_push(&mut de_sh[p], bs_gf256_xor(&b_sh[p][v], &tr_b[p][idx]));
                secret_vec_push(&mut de_mac[p], d_m);
                secret_vec_push(&mut de_mac[p], e_m);
            }
        }

        let de_opened = match commit_and_open_beaver_de_batch(
            session_id,
            perm_ctr * 24 + rnd,
            t,
            quorum_pts,
            &de_sh,
            &de_mac,
            pending_opened,
            pending_macs,
            party_rngs,
        ) {
            Ok(opened) => opened,
            Err(e) => {
                for vault in vaults.iter_mut() {
                    vault.poison_and_wipe();
                }
                return Err(KeccakMpcError::Preprocess(e));
            }
        };

        for idx in 0..N {
            let d_pub = &de_opened[2 * idx];
            let e_pub = &de_opened[2 * idx + 1];
            let de_pub = bs_gf256_mul_planes_ct(d_pub, e_pub);
            for p in 0..m {
                let db = bs_gf256_mul_planes_ct(d_pub, &tr_b[p][idx]);
                let ea = bs_gf256_mul_planes_ct(e_pub, &tr_a[p][idx]);
                // `de_pub` is public, so it enters every party's share (constant polynomial).
                let mut prod_sh = bs_gf256_xor(&tr_c[p][idx], &db);
                bs_gf256_xor_assign(&mut prod_sh, &ea);
                bs_gf256_xor_assign(&mut prod_sh, &de_pub);

                let alpha_p = vaults[p].mac_alpha_lanes;
                let mut out_mac = beaver_mac_planes(
                    &mac_c[p][idx],
                    &mac_b[p][idx],
                    &mac_a[p][idx],
                    &alpha_p,
                    d_pub,
                    e_pub,
                    &de_pub,
                );
                xor_spdz_macs_assign(&mut out_mac, &b_mac[p][idx]);
                states_sh[p][idx] = bs_gf256_xor(&b_sh[p][idx], &prod_sh);
                states_mac[p][idx] = out_mac;
            }
        }

        // 3. Iota: the public round constant enters lane 0 of every instance.
        for p in 0..m {
            let alpha_p = vaults[p].mac_alpha_lanes;
            for z in 0..64 {
                if ((rc >> z) & 1) == 1 {
                    add_public_u64_to_spdz_word(
                        u64::MAX,
                        &mut states_sh[p][z],
                        &mut states_mac[p][z],
                        &alpha_p,
                    );
                }
            }
        }
    }
    for p in 0..m {
        for words in [&mut b_sh[p], &mut tr_a[p], &mut tr_b[p], &mut tr_c[p]] {
            for word in words.iter_mut() {
                wipe_u64s(word);
            }
        }
    }
    Ok(())
}

pub(crate) fn slh_profile_digest_u64x4(params: &Fips205Params) -> [u64; 4] {
    let n_b = (params.n as u64).to_le_bytes();
    let h_b = (params.h as u64).to_le_bytes();
    let d_b = (params.d as u64).to_le_bytes();
    let hp_b = (params.hp as u64).to_le_bytes();
    let a_b = (params.a as u64).to_le_bytes();
    let k_b = (params.k as u64).to_le_bytes();
    let lg_w_b = (params.lg_w as u64).to_le_bytes();
    let m_b = (params.m as u64).to_le_bytes();
    let digest = cshake256_32_multi_frame(
        b"QSAG.FIPS205.PROFILE.V1",
        &[
            params.name.as_bytes(),
            &n_b,
            &h_b,
            &d_b,
            &hp_b,
            &a_b,
            &k_b,
            &lg_w_b,
            &m_b,
        ],
    );
    core::array::from_fn(|i| u64::from_le_bytes(core::array::from_fn(|b| digest[8 * i + b])))
}

#[inline]
fn ct_eq_u64_x4(a: &[u64; 4], b: &[u64; 4]) -> bool {
    let mut ok = 1u8;
    for i in 0..4 {
        ok &= ct_eq_u64(a[i], b[i]) as u8;
    }
    ok == 1
}

/// Lock-free write-once commitment to an enrolled [`Fips205Params`] profile on a share.
pub(super) struct SlhProfileLatch {
    state: AtomicU8,
    digest: [AtomicU64; 4],
}

impl SlhProfileLatch {
    const UNBOUND: u8 = 0;
    const BINDING: u8 = 1;
    const BOUND: u8 = 2;

    pub(super) const fn new() -> Self {
        Self {
            state: AtomicU8::new(Self::UNBOUND),
            digest: [
                AtomicU64::new(0),
                AtomicU64::new(0),
                AtomicU64::new(0),
                AtomicU64::new(0),
            ],
        }
    }

    fn enrolled(&self) -> Result<Option<[u64; 4]>, ()> {
        match self.state.load(Ordering::Acquire) {
            Self::UNBOUND => Ok(None),
            Self::BOUND => Ok(Some([
                self.digest[0].load(Ordering::Acquire),
                self.digest[1].load(Ordering::Acquire),
                self.digest[2].load(Ordering::Acquire),
                self.digest[3].load(Ordering::Acquire),
            ])),
            _ => Err(()),
        }
    }

    fn bind(&self, want: [u64; 4]) -> Result<(), ()> {
        if self
            .state
            .compare_exchange(
                Self::UNBOUND,
                Self::BINDING,
                Ordering::AcqRel,
                Ordering::Acquire,
            )
            .is_ok()
        {
            for (slot, &val) in self.digest.iter().zip(&want) {
                slot.store(val, Ordering::Release);
            }
            self.state.store(Self::BOUND, Ordering::Release);
            return Ok(());
        }
        if let Ok(Some(cur)) = self.enrolled()
            && ct_eq_u64_x4(&cur, &want)
        {
            return Ok(());
        }
        Err(())
    }
}

/// Authenticated SPDZ Shamir representation of `(SK.seed, SK.prf)` packed into four 64-bit words
/// (`[BitslicedGf256x64; 4]` = 32 bytes each) paired with 2-lane `Tower128` SPDZ MAC shares!
pub struct SpdzAuthenticatedKeyShare {
    pub party_id: usize,
    pub eval_point: TowerGf256,
    pub key_len: usize,
    pub pk_seed: [u8; 32],
    pub sk_seed_words: [BitslicedGf256x64; 4],
    pub sk_seed_macs: [[[Tower128; 64]; 2]; 4],
    pub sk_prf_words: [BitslicedGf256x64; 4],
    pub sk_prf_macs: [[[Tower128; 64]; 2]; 4],
    pub(super) slh_profile: SlhProfileLatch,
}

impl fmt::Debug for SpdzAuthenticatedKeyShare {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "SpdzAuthenticatedKeyShare(party={}, n={}, [REDACTED])",
            self.party_id, self.key_len
        )
    }
}

impl SpdzAuthenticatedKeyShare {
    /// The 32-byte scheme identity recorded in this share, if any. The record is the same
    /// write-once latch a FIPS 205 profile occupies, so a share serves one scheme only.
    pub(crate) fn scheme_identity(&self) -> Result<Option<[u8; 32]>, KeccakMpcError> {
        let words = self
            .slh_profile
            .enrolled()
            .map_err(|()| KeccakMpcError::KeyBindingMismatch)?;
        Ok(words.map(|w| {
            let mut out = [0u8; 32];
            for (chunk, word) in out.as_chunks_mut::<8>().0.iter_mut().zip(w) {
                *chunk = word.to_le_bytes();
            }
            out
        }))
    }

    /// Record `identity` once; a share that already carries another value refuses.
    pub(crate) fn bind_scheme_identity(&self, identity: &[u8; 32]) -> Result<(), KeccakMpcError> {
        let words: [u64; 4] =
            core::array::from_fn(|i| u64::from_le_bytes(identity.as_chunks::<8>().0[i]));
        self.slh_profile
            .bind(words)
            .map_err(|()| KeccakMpcError::KeyBindingMismatch)
    }
}

impl Drop for SpdzAuthenticatedKeyShare {
    fn drop(&mut self) {
        for w in 0..4 {
            wipe_u64s(&mut self.sk_seed_words[w]);
            wipe_u64s(&mut self.sk_prf_words[w]);
            for l in 0..2 {
                wipe_tower128(&mut self.sk_seed_macs[w][l]);
                wipe_tower128(&mut self.sk_prf_macs[w][l]);
            }
        }
    }
}

/// Authenticate DKG/reshared `ShamirSeedShare256` `(sk_seed, sk_prf)` shares under the SPDZ global
/// 2-lane `Tower128` MAC key of `vaults` (`alpha_contribs` from `spdz_setup_alpha_gf256`), with zero
/// secret reconstruction!
#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the existing explicit protocol interface for callers"
)]
