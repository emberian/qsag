//! Authenticated Boolean Beaver triples and dealerless Keccak vault generation.

use super::*;

/// One party's isolated 64-way bitsliced Boolean Beaver triple share `([a]_p, [b]_p, [c]_p)`
/// over $\mathcal{T}_3 = \mathbb{F}_{2^8}$ paired with full 2-lane `Tower128` SPDZ Shamir MAC shares
/// (`a_mac, b_mac, c_mac`), wiped on `Drop`.
pub struct KeccakBitTripleShare64 {
    pub a: BitslicedGf256x64,
    pub b: BitslicedGf256x64,
    pub c: BitslicedGf256x64,
    pub a_mac: [[Tower128; 64]; 2],
    pub b_mac: [[Tower128; 64]; 2],
    pub c_mac: [[Tower128; 64]; 2],
}

impl fmt::Debug for KeccakBitTripleShare64 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("KeccakBitTripleShare64([REDACTED])")
    }
}

impl Drop for KeccakBitTripleShare64 {
    fn drop(&mut self) {
        wipe_u64s(&mut self.a);
        wipe_u64s(&mut self.b);
        wipe_u64s(&mut self.c);
        for lane in 0..2 {
            wipe_tower128(&mut self.a_mac[lane]);
            wipe_tower128(&mut self.b_mac[lane]);
            wipe_tower128(&mut self.c_mac[lane]);
        }
    }
}

/// Per-party isolated vault of dealerless-preprocessed `Keccak-f[1600]` Boolean triples and
/// degree-$<t$ Shamir shares of the 2-lane `Tower128` SPDZ MAC keys (`!Clone`, wiped on `Drop`,
/// permanently poisoned and zeroized on any `MacCheck` abort).
pub struct PreprocessedKeccakPartyVault {
    pub party_id: usize,
    pub eval_point: TowerGf256,
    /// Degree-$<t$ Shamir share $[\alpha]_p \in \mathcal{T}_7^2$ of the global 2-lane SPDZ MAC key.
    pub mac_alpha_lanes: [Tower128; 2],
    pub(crate) triples: Vec<KeccakBitTripleShare64>,
    pub(crate) cursor: usize,
    pub poisoned: bool,
}

impl fmt::Debug for PreprocessedKeccakPartyVault {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "PreprocessedKeccakPartyVault(party={}, rem={}, poisoned={})",
            self.party_id,
            self.remaining(),
            self.poisoned
        )
    }
}

impl Drop for PreprocessedKeccakPartyVault {
    fn drop(&mut self) {
        self.poison_and_wipe();
    }
}

impl PreprocessedKeccakPartyVault {
    /// Immediately burn `mac_alpha_lanes` and purge all remaining triples on any `MacCheck` failure!
    pub fn poison_and_wipe(&mut self) {
        self.poisoned = true;
        wipe_tower128(&mut self.mac_alpha_lanes);
        self.triples.clear();
        self.cursor = 0;
    }

    #[inline]
    pub fn remaining(&self) -> usize {
        if self.poisoned {
            0
        } else {
            self.triples.len().saturating_sub(self.cursor)
        }
    }

    #[inline]
    pub fn triples_slice(&self) -> &[KeccakBitTripleShare64] {
        &self.triples
    }

    /// Monotonically burn a disjoint range before exposing its material. All quorums
    /// sharing this vault use the same cursor; abandoned reservations are never reclaimed.
    pub fn reserve_triples(
        &mut self,
        count: usize,
    ) -> Result<&[KeccakBitTripleShare64], PreprocessError> {
        let range = reserve_material(
            &mut self.cursor,
            self.triples.len(),
            count,
            self.poisoned,
            "Keccak triple",
        )?;
        Ok(&self.triples[range])
    }

    #[inline]
    pub fn pop_triple(&mut self) -> Result<&KeccakBitTripleShare64, PreprocessError> {
        Ok(&self.reserve_triples(1)?[0])
    }
}

/// Multiply XOR-shared Boolean words using the production KOS/MASCOT pool.
/// All masked openings carry two-lane GF(2^128) MACs; the pool performs batch
/// companion sacrifice before any triple is used. Full-field n-of-n Shamir
/// shares are converted back by the linear bit-zero projection only at the end.
pub(crate) fn checked_boolean_product(
    session_id: &[u8; 32],
    a: &[Vec<u64>],
    b: &[Vec<u64>],
    mesh: &mut OtMesh,
    rngs: &mut [PartyPrivateRng],
) -> Result<Vec<Vec<u64>>, PreprocessError> {
    checked_boolean_product_with_hook(session_id, a, b, mesh, rngs, |_| {})
}

pub(super) fn checked_boolean_product_with_hook<F: FnMut(&mut [Vec<BitslicedGf256x64>])>(
    session_id: &[u8; 32],
    a: &[Vec<u64>],
    b: &[Vec<u64>],
    mesh: &mut OtMesh,
    rngs: &mut [PartyPrivateRng],
    mut fault: F,
) -> Result<Vec<Vec<u64>>, PreprocessError> {
    let n = a.len();
    if !(2..=255).contains(&n)
        || b.len() != n
        || rngs.len() != n
        || mesh.n != n
        || a.iter().chain(b).any(|v| v.len() != a[0].len())
    {
        return Err(PreprocessError::InvalidThreshold { t: n, n });
    }
    let points: Vec<_> = (1..=n).map(|p| TowerGf256(p as u8)).collect();
    let weights =
        lagrange_weights_zero_gf256(&points).ok_or(PreprocessError::DuplicateOrZeroEvalPoint)?;
    let projection: Vec<_> = weights
        .iter()
        .map(|&w| PublicGf256Matrix::from_public_scalar(w))
        .collect();
    let (mut contributions, mut alpha) = spdz_setup_alpha_gf256(session_id, n, &points, rngs)?;
    let result = (|| {
        let mut out = crate::wipe::SecretBuffer(vec![vec![0; a[0].len()]; n]);
        // One triple ceremony and one input authentication per chunk of words.
        const CHUNK_WORDS: usize = 512;
        for start in (0..a[0].len()).step_by(CHUNK_WORDS) {
            let count = (a[0].len() - start).min(CHUNK_WORDS);
            let sid = cshake256_32_multi_frame(
                b"QSAG.DPCG.ACTIVE.PRODUCT/v1",
                &[session_id, &(start as u64).to_be_bytes()],
            );
            let vaults = run_dealerless_pi_triple_f2_with_alpha(
                sid,
                n,
                &points,
                count,
                &contributions,
                &alpha,
                mesh,
                rngs,
            )?;
            let bits = crate::wipe::SecretBuffer(
                (0..n)
                    .map(|p| {
                        (start..start + count)
                            .flat_map(|k| [a[p][k], b[p][k]])
                            .collect::<Vec<u64>>()
                    })
                    .collect::<Vec<_>>(),
            );
            let (mut inputs, mut macs) = triple_f2::authenticate_xor_shared_words(
                &sid,
                n,
                &points,
                mesh,
                &contributions,
                &alpha,
                &bits,
                rngs,
            )?;
            drop(bits);
            let batch_result: Result<(), PreprocessError> = (|| {
                for p in 0..n {
                    for k in 0..count {
                        let triple = &vaults[p].triples[k];
                        bs_gf256_xor_assign(&mut inputs[p][2 * k], &triple.a);
                        bs_gf256_xor_assign(&mut inputs[p][2 * k + 1], &triple.b);
                        for (word, triple_mac) in macs[p][2 * k..2 * k + 2]
                            .iter_mut()
                            .zip([&triple.a_mac, &triple.b_mac])
                        {
                            for (lane, triple_lane) in word.iter_mut().zip(triple_mac) {
                                for (value, &mask) in lane.iter_mut().zip(triple_lane) {
                                    *value = value.add(mask);
                                }
                            }
                        }
                    }
                }
                fault(&mut inputs);
                let opening = commit_and_open_spdz_bs_gf256_batch_quorum(
                    &sid,
                    "dense_pcg_active_beaver_mask",
                    n,
                    &points,
                    &inputs,
                    &macs,
                    &alpha,
                    rngs,
                );
                for party in &mut macs {
                    for word in party {
                        for lane in word {
                            wipe_tower128(lane);
                        }
                    }
                }
                let opened = opening?;
                for p in 0..n {
                    for k in 0..count {
                        let triple = &vaults[p].triples[k];
                        let d = &opened[2 * k];
                        let e = &opened[2 * k + 1];
                        let mut c = bs_gf256_xor(&triple.c, &bs_gf256_mul_planes_ct(d, &triple.b));
                        bs_gf256_xor_assign(&mut c, &bs_gf256_mul_planes_ct(e, &triple.a));
                        bs_gf256_xor_assign(&mut c, &bs_gf256_mul_planes_ct(d, e));
                        out[p][start + k] = projection[p].scale_planes(&c)[0];
                        wipe_u64s(&mut c);
                    }
                }
                Ok(())
            })();
            for party in &mut inputs {
                for word in party {
                    wipe_u64s(word);
                }
            }
            batch_result?;
        }
        Ok(core::mem::take(&mut out.0))
    })();
    for v in &mut contributions {
        wipe_tower128(v);
    }
    for v in &mut alpha {
        wipe_tower128(v);
    }
    result
}

/// Batch bitsliced `64x` SPDZ committed opening + 2-lane `Tower128` `MacCheck` (`2^{-256}` soundness)
/// across `batch_len` words; every quorum multiplies the private residual by a
/// fresh secret randomizer using OLE before the committed check opening.
#[expect(
    clippy::too_many_arguments,
    reason = "Quorum, value shares, MAC shares and private randomness are separate protocol inputs"
)]
pub fn commit_and_open_spdz_bs_gf256_batch_quorum(
    session_id: &[u8; 32],
    phase: &'static str,
    t: usize,
    quorum_eval_points: &[TowerGf256],
    batch_shares: &[Vec<BitslicedGf256x64>],
    batch_macs: &[Vec<[[Tower128; 64]; 2]>],
    alpha_shares: &[[Tower128; 2]],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<BitslicedGf256x64>, PreprocessError> {
    commit_and_open_spdz_bs_gf256_batch_quorum_with_mesh(
        session_id,
        phase,
        t,
        quorum_eval_points,
        batch_shares,
        batch_macs,
        alpha_shares,
        None,
        party_rngs,
    )
}

/// Variant of [`commit_and_open_spdz_bs_gf256_batch_quorum`] reusing a caller-owned [`OtMesh`].
#[expect(
    clippy::too_many_arguments,
    reason = "Quorum, value shares, MAC shares, optional OT mesh and private randomness are separate protocol inputs"
)]
pub fn commit_and_open_spdz_bs_gf256_batch_quorum_with_mesh(
    session_id: &[u8; 32],
    phase: &'static str,
    t: usize,
    quorum_eval_points: &[TowerGf256],
    batch_shares: &[Vec<BitslicedGf256x64>],
    batch_macs: &[Vec<[[Tower128; 64]; 2]>],
    alpha_shares: &[[Tower128; 2]],
    mesh: Option<&mut OtMesh>,
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<BitslicedGf256x64>, PreprocessError> {
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
    validate_all_eval_points_gf256(quorum_eval_points)?;

    // Round 1: Commit to all `batch_len` words per party before revealing any share
    let mut salts = Vec::with_capacity(m);
    let mut coms = Vec::with_capacity(m);
    for p in 0..m {
        let salt = party_rngs[p].next_bytes32();
        let mut xof = Cshake256Xof::new(b"QSAG.SPDZ.BS64.BATCH.OPEN.COM/v1");
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
            #[expect(
                clippy::needless_range_loop,
                reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows"
            )]
            for pl in 0..8 {
                xof.absorb(&batch_shares[p][w][pl].to_le_bytes());
            }
        }
        let mut com = [0u8; 32];
        xof.squeeze(&mut com);
        salts.push(salt);
        coms.push(com);
    }
    for p in 0..m {
        let mut xof = Cshake256Xof::new(b"QSAG.SPDZ.BS64.BATCH.OPEN.COM/v1");
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
            #[expect(
                clippy::needless_range_loop,
                reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows"
            )]
            for pl in 0..8 {
                xof.absorb(&batch_shares[p][w][pl].to_le_bytes());
            }
        }
        let mut exp = [0u8; 32];
        xof.squeeze(&mut exp);
        wipe_bytes32(&mut salts[p]);
        if !ct_eq_bytes32(&exp, &coms[p]) {
            return Err(PreprocessError::ShareCommitMismatch { phase, party_id: p });
        }
    }

    let lambdas_0 = lagrange_weights_zero_gf256(&quorum_eval_points[..t])
        .ok_or(PreprocessError::DuplicateOrZeroEvalPoint)?;
    let lambda0_mats: Vec<PublicGf256Matrix> = lambdas_0
        .iter()
        .map(|&l| PublicGf256Matrix::from_public_scalar(l))
        .collect();
    let mut extrap_mats: Vec<Vec<PublicGf256Matrix>> = Vec::with_capacity(m - t);
    for r_idx in t..m {
        let xm = quorum_eval_points[r_idx];
        let mut row = Vec::with_capacity(t);
        for i in 0..t {
            let mut num = TowerGf256::ONE;
            let mut den = TowerGf256::ONE;
            for j in 0..t {
                if i == j {
                    continue;
                }
                num = num.mul(xm.add(quorum_eval_points[j]));
                den = den.mul(quorum_eval_points[i].add(quorum_eval_points[j]));
            }
            let li = num.mul(den.inv().ok_or(PreprocessError::DuplicateOrZeroEvalPoint)?);
            row.push(PublicGf256Matrix::from_public_scalar(li));
        }
        extrap_mats.push(row);
    }

    let mut opened = Vec::with_capacity(batch_len);
    let mut dig_xof = Cshake256Xof::new(b"QSAG.SPDZ.BS64.BATCH.DIG/v1");
    for (w, _) in batch_shares[0].iter().enumerate() {
        let mut sec = [0u64; 8];
        for q in 0..t {
            lambda0_mats[q].scale_xor_into(&mut sec, &batch_shares[q][w]);
        }
        for r_idx in t..m {
            let mut expected = [0u64; 8];
            for i in 0..t {
                extrap_mats[r_idx - t][i].scale_xor_into(&mut expected, &batch_shares[i][w]);
            }
            if expected != batch_shares[r_idx][w] {
                return Err(PreprocessError::DegreeCheckFailed { phase });
            }
        }
        #[expect(
            clippy::needless_range_loop,
            reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows"
        )]
        for pl in 0..8 {
            dig_xof.absorb(&sec[pl].to_le_bytes());
        }
        opened.push(sec);
    }
    let mut open_digest = [0u8; 32];
    dig_xof.squeeze(&mut open_digest);

    // Round 2: Public-coin random `Tower128` folding across all `64 * batch_len` opened lanes + ZK `MacCheck`
    let fold_coin =
        run_commit_and_open_coin(session_id, phase.as_bytes(), &open_digest, party_rngs)?;
    let (x_folded, m_folded) = fold_spdz_mac_words(&fold_coin, &opened, batch_macs, t);

    let mut local_mesh = match mesh {
        Some(_) => None,
        None => {
            let sid = cshake256_32_multi_frame(
                b"QSAG.SPDZ.BS64.BLIND.OT/v1",
                &[session_id, phase.as_bytes(), &fold_coin],
            );
            Some(OtMesh::establish(sid, party_rngs)?)
        }
    };
    let active_mesh: &mut OtMesh = match mesh {
        Some(m_ref) => m_ref,
        None => local_mesh
            .as_mut()
            .ok_or(PreprocessError::InvalidThreshold { t, n: m })?,
    };
    for lane in 0..2 {
        let lane_sid = cshake256_32_multi_frame(
            b"QSAG.SPDZ.BS64.BLIND.LANE/v1",
            &[
                session_id,
                phase.as_bytes(),
                &fold_coin,
                &(lane as u64).to_be_bytes(),
            ],
        );
        let additive = SecretBuffer(
            (0..m)
                .map(|p| {
                    if p < t {
                        m_folded[p][lane]
                            .add(x_folded[lane].mul(alpha_shares[p][lane]))
                            .mul_gf256(lambdas_0[p])
                    } else {
                        Tower128::ZERO
                    }
                })
                .collect::<Vec<_>>(),
        );
        let w = blind_open_tower128(
            &lane_sid,
            phase,
            &additive,
            Some(&mut *active_mesh),
            party_rngs,
        )?;
        if !w.ct_eq(Tower128::ZERO) {
            return Err(PreprocessError::MacCheckFailed {
                phase,
                accused_party: None,
            });
        }
    }
    Ok(opened)
}

/// Run dealerless `Π_triple_f2` for `num_triples` authenticated 64-way Boolean triples.
/// Authenticate raw products, recursively sacrifice, then draw transcript-bound bucket coins.
/// The adaptive arity `f` satisfies `n / C(f(n+1), f) <= 2^-40` for `n` output bits;
/// one whole parity bucket is discarded. Combine both factors before Shamir dealing and
/// checking the resulting value/MAC shares. The additive variant stops before Shamir dealing.
pub fn run_dealerless_pi_triple_f2(
    session_id: [u8; 32],
    t: usize,
    eval_points: &[TowerGf256],
    num_triples: usize,
    ot_mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<PreprocessedKeccakPartyVault>, PreprocessError> {
    run_dealerless_pi_triple_f2_with_fault(
        session_id,
        t,
        eval_points,
        num_triples,
        ot_mesh,
        party_rngs,
        |_, _, _| {},
    )
}

/// Fault-injectable entry point for adversarial unit tests of `Π_triple_f2`.
pub fn run_dealerless_pi_triple_f2_with_fault<F>(
    session_id: [u8; 32],
    t: usize,
    eval_points: &[TowerGf256],
    num_triples: usize,
    ot_mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
    fault_hook: F,
) -> Result<Vec<PreprocessedKeccakPartyVault>, PreprocessError>
where
    F: FnMut(usize, &mut [BitslicedGf256x64], &mut [BitslicedGf256x64]),
{
    let n = eval_points.len();
    if t == 0 || t > n || party_rngs.len() != n || ot_mesh.n != n {
        return Err(PreprocessError::InvalidThreshold { t, n });
    }
    validate_all_eval_points_gf256(eval_points)?;

    let (mut alpha_contribs, mut alpha_shamir) =
        spdz_setup_alpha_gf256(&session_id, t, eval_points, party_rngs)?;
    let res = run_dealerless_pi_triple_f2_with_alpha_and_fault(
        session_id,
        t,
        eval_points,
        num_triples,
        &alpha_contribs,
        &alpha_shamir,
        ot_mesh,
        party_rngs,
        fault_hook,
    )
    .map(|(vaults, _transcript)| vaults);
    for ac in &mut alpha_contribs {
        wipe_tower128(ac);
    }
    for ash in &mut alpha_shamir {
        wipe_tower128(ash);
    }
    res
}

/// Run dealerless `Π_triple_f2` bound to an existing session SPDZ MAC key `(alpha_contribs, alpha_shamir)`
/// (used when `SpdzAuthenticatedKeyShare` and `PreprocessedKeccakPartyVault` share a single global $\alpha$).
#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the public preprocessing API used by other protocol modules"
)]
pub fn run_dealerless_pi_triple_f2_with_alpha(
    session_id: [u8; 32],
    t: usize,
    eval_points: &[TowerGf256],
    num_triples: usize,
    alpha_contribs: &[[Tower128; 2]],
    alpha_shamir: &[[Tower128; 2]],
    ot_mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<PreprocessedKeccakPartyVault>, PreprocessError> {
    run_dealerless_pi_triple_f2_with_alpha_and_fault(
        session_id,
        t,
        eval_points,
        num_triples,
        alpha_contribs,
        alpha_shamir,
        ot_mesh,
        party_rngs,
        |_, _, _| {},
    )
    .map(|(vaults, _transcript)| vaults)
}

/// [`run_dealerless_pi_triple_f2`] that also returns the ceremony's transcript digest: a chain
/// over every value the parties broadcast in it (authentication derandomizers, sacrifice coins
/// and cross terms, the bucket coin and the combine openings). A caller running the ceremony
/// inside a larger protocol absorbs it into its own transcript.
pub fn run_dealerless_pi_triple_f2_with_transcript(
    session_id: [u8; 32],
    t: usize,
    eval_points: &[TowerGf256],
    num_triples: usize,
    ot_mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
) -> Result<(Vec<PreprocessedKeccakPartyVault>, [u8; 32]), PreprocessError> {
    let n = eval_points.len();
    if t == 0 || t > n || party_rngs.len() != n || ot_mesh.n != n {
        return Err(PreprocessError::InvalidThreshold { t, n });
    }
    validate_all_eval_points_gf256(eval_points)?;
    let (mut alpha_contribs, mut alpha_shamir) =
        spdz_setup_alpha_gf256(&session_id, t, eval_points, party_rngs)?;
    let res = run_dealerless_pi_triple_f2_with_alpha_and_fault(
        session_id,
        t,
        eval_points,
        num_triples,
        &alpha_contribs,
        &alpha_shamir,
        ot_mesh,
        party_rngs,
        |_, _, _| {},
    );
    for ac in &mut alpha_contribs {
        wipe_tower128(ac);
    }
    for ash in &mut alpha_shamir {
        wipe_tower128(ash);
    }
    res
}

/// One party's additive (`n`-of-`n`) shares of authenticated Boolean Beaver triple words and of
/// their two-lane MACs. Bit `k` of word `w` has MAC shares `*_mac[lane][64 * w + k]`; over all
/// parties they XOR to the bit times the XOR of the parties' `alpha_contribs[.][lane]`, as raw
/// 128-bit vectors. Wiped on [`Drop`].
pub struct AdditiveBoolTripleShares {
    pub party_id: usize,
    pub a: Vec<u64>,
    pub b: Vec<u64>,
    pub c: Vec<u64>,
    pub a_mac: [Vec<u128>; 2],
    pub b_mac: [Vec<u128>; 2],
    pub c_mac: [Vec<u128>; 2],
}

impl Drop for AdditiveBoolTripleShares {
    fn drop(&mut self) {
        for words in [&mut self.a, &mut self.b, &mut self.c] {
            wipe_u64s(words);
        }
        for macs in [&mut self.a_mac, &mut self.b_mac, &mut self.c_mac] {
            for lane in macs {
                wipe_u128s(lane);
            }
        }
    }
}

/// `Π_triple_f2` stopped before its Shamir conversion: `num_words` sacrificed and bucket-combined
/// Boolean Beaver triple words, additively shared among the parties of `ot_mesh` and
/// authenticated under the two-lane key whose additive shares are `alpha_contribs`. This is the
/// form an `n`-of-`n` committee consumes directly; [`run_dealerless_pi_triple_f2_with_alpha`]
/// is the same factory followed by the conversion to degree-`< t` shares.
pub fn run_dealerless_pi_triple_f2_additive(
    session_id: [u8; 32],
    num_words: usize,
    alpha_contribs: &[[Tower128; 2]],
    ot_mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<AdditiveBoolTripleShares>, PreprocessError> {
    run_dealerless_pi_triple_f2_additive_with_fault(
        session_id,
        num_words,
        alpha_contribs,
        ot_mesh,
        party_rngs,
        |_, _| {},
    )
}

/// Fault-injectable entry point for adversarial tests of the additive output mode:
/// `product_fault(party, words)` sees the party's XOR share of the raw products of the first
/// ceremony of every combine pool, before that share is authenticated.
pub fn run_dealerless_pi_triple_f2_additive_with_fault<F>(
    session_id: [u8; 32],
    num_words: usize,
    alpha_contribs: &[[Tower128; 2]],
    ot_mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
    mut product_fault: F,
) -> Result<Vec<AdditiveBoolTripleShares>, PreprocessError>
where
    F: FnMut(usize, &mut [u64]),
{
    let n = ot_mesh.n;
    if n < 2 || party_rngs.len() != n || alpha_contribs.len() != n {
        return Err(PreprocessError::InvalidThreshold { t: n, n });
    }
    let take_macs =
        |macs: &mut [Vec<u128>; 2]| core::array::from_fn(|l| core::mem::take(&mut macs[l]));
    if num_words == 0 {
        return Ok((0..n)
            .map(|party_id| AdditiveBoolTripleShares {
                party_id,
                a: Vec::new(),
                b: Vec::new(),
                c: Vec::new(),
                a_mac: [Vec::new(), Vec::new()],
                b_mac: [Vec::new(), Vec::new()],
                c_mac: [Vec::new(), Vec::new()],
            })
            .collect());
    }
    let (mut triples, _transcript) = triple_f2::run_pi_triple_f2_additive(
        session_id,
        num_words,
        alpha_contribs,
        ot_mesh,
        party_rngs,
        &mut triple_f2::PiTripleF2Faults {
            product_shares: Some(&mut product_fault),
            ..Default::default()
        },
    )?;
    Ok((0..n)
        .map(|p| AdditiveBoolTripleShares {
            party_id: p,
            a: core::mem::take(&mut triples.bits[0][p]),
            b: core::mem::take(&mut triples.bits[1][p]),
            c: core::mem::take(&mut triples.bits[2][p]),
            a_mac: take_macs(&mut triples.macs[0][p]),
            b_mac: take_macs(&mut triples.macs[1][p]),
            c_mac: take_macs(&mut triples.macs[2][p]),
        })
        .collect())
}

/// Unbiased Fisher–Yates permutation of `0..len`, expanded from the public coin `coin` under
/// `domain`.
///
/// Position `i` (from `len - 1` down to `1`) is swapped with an index drawn uniformly from
/// `0..=i`. Each draw takes 64 XOF bits, masks them to the smallest power of two above `i`
/// and is repeated until the value is at most `i`, so no residue class is favoured (a draw is
/// rejected with probability below 1/2).
pub(crate) fn derive_coin_permutation(coin: &[u8; 32], domain: &[u8], len: usize) -> Vec<u32> {
    assert!(
        len <= u32::MAX as usize,
        "permutation length exceeds u32 range"
    );
    let mut xof = Cshake256Xof::new(b"QSAG.COIN.PERMUTATION/v1");
    xof.absorb(&(domain.len() as u64).to_le_bytes());
    xof.absorb(domain);
    xof.absorb(&(len as u64).to_le_bytes());
    xof.absorb(coin);

    let mut perm: Vec<u32> = (0..len as u32).collect();
    for i in (1..len).rev() {
        let bound = i as u64;
        let mask = u64::MAX >> bound.leading_zeros();
        let j = loop {
            let mut buf = [0u8; 8];
            xof.squeeze(&mut buf);
            let draw = u64::from_le_bytes(buf) & mask;
            if draw <= bound {
                break draw as usize;
            }
        };
        perm.swap(i, j);
    }
    perm
}

/// Runs `Π_triple_f2` and also returns its transcript digest. `fault_hook` sees every party's
/// Shamir shares of the final `a` and `c` words before the `Π_MAC` check.
#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the public preprocessing API used by other protocol modules"
)]
pub(super) fn run_dealerless_pi_triple_f2_with_alpha_and_fault<F>(
    session_id: [u8; 32],
    t: usize,
    eval_points: &[TowerGf256],
    num_triples: usize,
    alpha_contribs: &[[Tower128; 2]],
    alpha_shamir: &[[Tower128; 2]],
    ot_mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
    mut fault_hook: F,
) -> Result<(Vec<PreprocessedKeccakPartyVault>, [u8; 32]), PreprocessError>
where
    F: FnMut(usize, &mut [BitslicedGf256x64], &mut [BitslicedGf256x64]),
{
    let n = eval_points.len();
    if t == 0
        || t > n
        || party_rngs.len() != n
        || ot_mesh.n != n
        || alpha_contribs.len() != n
        || alpha_shamir.len() != n
    {
        return Err(PreprocessError::InvalidThreshold { t, n });
    }
    validate_all_eval_points_gf256(eval_points)?;

    if num_triples == 0 {
        let mut vaults = Vec::with_capacity(n);
        for p in 0..n {
            vaults.push(PreprocessedKeccakPartyVault {
                party_id: p,
                eval_point: eval_points[p],
                mac_alpha_lanes: alpha_shamir[p],
                triples: Vec::new(),
                cursor: 0,
                poisoned: false,
            });
        }
        return Ok((vaults, session_id));
    }
    triple_f2::run_pi_triple_f2(
        session_id,
        t,
        eval_points,
        num_triples,
        alpha_contribs,
        alpha_shamir,
        ot_mesh,
        party_rngs,
        &mut triple_f2::PiTripleF2Faults {
            shamir_shares: Some(&mut fault_hook),
            ..Default::default()
        },
    )
}
