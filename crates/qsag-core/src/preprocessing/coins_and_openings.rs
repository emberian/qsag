//! Commit-and-open public coins, degree checks and quorum openings.

use super::*;

/// Local single-party state for a separated two-round `Π_coin` ceremony.
///
/// Holds only one party's private 32-byte share and commitment; zeroizes the share on [`Drop`].
/// Distributed callers exchange `commitment` across all `n` parties before calling
/// [`PartyCoinCommitState::open_share`] and [`verify_and_combine_coin_openings`], which combines
/// **only the verified supplied wire openings** (never reading remote private shares).
pub struct PartyCoinCommitState {
    party_id: usize,
    share: [u8; 32],
    commitment: [u8; 32],
}

impl Drop for PartyCoinCommitState {
    fn drop(&mut self) {
        wipe_bytes32(&mut self.share);
    }
}

impl PartyCoinCommitState {
    /// Sample a fresh 32-byte coin share from `rng` and compute its `QSAG.COIN.COMMIT/v1` digest.
    pub fn commit(
        party_id: usize,
        session_id: &[u8; 32],
        phase_label: &[u8],
        transcript_digest: &[u8; 32],
        rng: &mut PartyPrivateRng,
    ) -> Self {
        let share = rng.next_bytes32();
        let pid = (party_id as u64).to_be_bytes();
        let commitment = cshake256_32_multi_frame(
            b"QSAG.COIN.COMMIT/v1",
            &[session_id, phase_label, transcript_digest, &pid, &share],
        );
        Self {
            party_id,
            share,
            commitment,
        }
    }

    /// Public commitment broadcast in Round 1.
    #[inline]
    pub fn commitment(&self) -> [u8; 32] {
        self.commitment
    }

    /// Party index bound into the Round-1 commitment frame.
    #[inline]
    pub fn party_id(&self) -> usize {
        self.party_id
    }

    /// Release this party's Round-2 opening after locking all `n` Round-1 peer commitments.
    /// Consumes `self` (wiping the stored share via `Drop`) and returns the 32-byte opening.
    pub fn open_share(self, locked_commitments: &[[u8; 32]]) -> Result<[u8; 32], PreprocessError> {
        if self.party_id >= locked_commitments.len()
            || !ct_eq_bytes32(&locked_commitments[self.party_id], &self.commitment)
        {
            return Err(PreprocessError::CoinCommitMismatch {
                party_id: self.party_id,
            });
        }
        Ok(self.share)
    }
}

/// Verify all `n` Round-2 wire `openings` against `locked_commitments` and derive the 32-byte
/// `QSAG.COIN.DERIVE/v1` public coin exclusively from the **verified supplied `openings`**.
pub fn verify_and_combine_coin_openings(
    session_id: &[u8; 32],
    phase_label: &[u8],
    transcript_digest: &[u8; 32],
    locked_commitments: &[[u8; 32]],
    openings: &[[u8; 32]],
) -> Result<[u8; 32], PreprocessError> {
    if locked_commitments.is_empty() || locked_commitments.len() != openings.len() {
        return Err(PreprocessError::CoinCommitMismatch {
            party_id: locked_commitments.len().min(openings.len()),
        });
    }
    let mut combined = [0u8; 32];
    for (p, (commit, opened)) in locked_commitments.iter().zip(openings.iter()).enumerate() {
        let pid = (p as u64).to_be_bytes();
        let recomputed = cshake256_32_multi_frame(
            b"QSAG.COIN.COMMIT/v1",
            &[session_id, phase_label, transcript_digest, &pid, opened],
        );
        if !ct_eq_bytes32(&recomputed, commit) {
            wipe_bytes32(&mut combined);
            return Err(PreprocessError::CoinCommitMismatch { party_id: p });
        }
        for (dst, &src) in combined.iter_mut().zip(opened.iter()) {
            *dst ^= src;
        }
    }
    let out = cshake256_32_multi_frame(
        b"QSAG.COIN.DERIVE/v1",
        &[session_id, phase_label, transcript_digest, &combined],
    );
    wipe_bytes32(&mut combined);
    Ok(out)
}

/// In-process coordinator coin-toss helper (`Π_coin`): every party commits `cSHAKE256` to a
/// private 32-byte share before any opening is checked, then verifies all commitments and derives
/// `QSAG.COIN.DERIVE/v1`. For separated-participant wire ceremonies, use [`PartyCoinCommitState`]
/// and [`verify_and_combine_coin_openings`].
pub fn run_commit_and_open_coin(
    session_id: &[u8; 32],
    phase_label: &[u8],
    transcript_digest: &[u8; 32],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<[u8; 32], PreprocessError> {
    run_commit_and_open_coin_with_hook(
        session_id,
        phase_label,
        transcript_digest,
        party_rngs,
        |_, _| {},
    )
}

/// Same as [`run_commit_and_open_coin`], with an adversarial fault-injection hook on opened shares
/// for unit-testing `CoinCommitMismatch` detection.
///
/// Note: `ProductionCoinReduction.lean` models this exact in-process two-pass helper semantics
/// (verifying hook-mutated openings against Round-1 commitments and XORing the locked `shares`
/// vector; separated wire participants instead combine verified wire openings via
/// [`verify_and_combine_coin_openings`]).
pub fn run_commit_and_open_coin_with_hook<F>(
    session_id: &[u8; 32],
    phase_label: &[u8],
    transcript_digest: &[u8; 32],
    party_rngs: &mut [PartyPrivateRng],
    mut corrupt_opening: F,
) -> Result<[u8; 32], PreprocessError>
where
    F: FnMut(usize, &mut [u8; 32]),
{
    let n = party_rngs.len();
    let mut shares = Vec::with_capacity(n);
    let mut commits = Vec::with_capacity(n);
    for (p, rng) in party_rngs.iter_mut().enumerate() {
        let r_p = rng.next_bytes32();
        let pid = (p as u64).to_be_bytes();
        let com = cshake256_32_multi_frame(
            b"QSAG.COIN.COMMIT/v1",
            &[session_id, phase_label, transcript_digest, &pid, &r_p],
        );
        shares.push(r_p);
        commits.push(com);
    }

    // Broadcast openings (after all commitments are locked)
    let mut combined = [0u8; 32];
    for p in 0..n {
        let mut opened = shares[p];
        corrupt_opening(p, &mut opened);
        let pid = (p as u64).to_be_bytes();
        let recomputed = cshake256_32_multi_frame(
            b"QSAG.COIN.COMMIT/v1",
            &[session_id, phase_label, transcript_digest, &pid, &opened],
        );
        wipe_bytes32(&mut opened);
        if !ct_eq_bytes32(&recomputed, &commits[p]) {
            for s in &mut shares {
                wipe_bytes32(s);
            }
            wipe_bytes32(&mut combined);
            return Err(PreprocessError::CoinCommitMismatch { party_id: p });
        }
        for b in 0..32 {
            combined[b] ^= shares[p][b];
        }
    }
    for s in &mut shares {
        wipe_bytes32(s);
    }
    let out = cshake256_32_multi_frame(
        b"QSAG.COIN.DERIVE/v1",
        &[session_id, phase_label, transcript_digest, &combined],
    );
    wipe_bytes32(&mut combined);
    Ok(out)
}

// ============================================================================
// 4. Full-Vector `eval_points[0..n]` Degree Verifiers & Committed SPDZ `MacCheck`
// ============================================================================

/// Validate that ALL `n` evaluation points in `eval_points[0..n]` are non-zero and pairwise
/// distinct (prevents `eval_points[m] == 0` for `m >= t` from leaking `f(0)`!).
pub fn validate_all_eval_points_gf256(eval_points: &[TowerGf256]) -> Result<(), PreprocessError> {
    if eval_points.is_empty() {
        return Ok(());
    }
    if eval_points.len() > u8::MAX as usize {
        return Err(PreprocessError::DuplicateOrZeroEvalPoint);
    }
    let points: Vec<_> = eval_points
        .iter()
        .map(|p| qsag_verified::Gf256(p.0))
        .collect();
    if qsag_verified::shamir_validate_points_gf256(&points) {
        Ok(())
    } else {
        Err(PreprocessError::DuplicateOrZeroEvalPoint)
    }
}

/// Validate that ALL `n` `Goldilocks` evaluation points in `eval_points[0..n]` are canonical,
/// non-zero mod $p$, and pairwise distinct.
pub fn validate_all_eval_points_goldilocks(
    eval_points: &[Goldilocks],
) -> Result<(), PreprocessError> {
    for i in 0..eval_points.len() {
        if eval_points[i].to_canonical_u64() == 0 {
            return Err(PreprocessError::DuplicateOrZeroEvalPoint);
        }
        for j in (i + 1)..eval_points.len() {
            if eval_points[i] == eval_points[j] {
                return Err(PreprocessError::DuplicateOrZeroEvalPoint);
            }
        }
    }
    Ok(())
}

/// Public interpolation tables for one ordered quorum and threshold.
/// Denominators use Montgomery batch inversion (one field inverse).
pub struct GoldilocksOpeningTables {
    t: usize,
    n: usize,
    pub(super) zero: Vec<Goldilocks>,
    pub(super) extra: Vec<Vec<Goldilocks>>,
}
impl GoldilocksOpeningTables {
    pub fn new(t: usize, points: &[Goldilocks]) -> Result<Self, PreprocessError> {
        let n = points.len();
        if t == 0 || t > n {
            return Err(PreprocessError::InvalidThreshold { t, n });
        }
        validate_all_eval_points_goldilocks(points)?;
        let mut denominators = vec![Goldilocks::ONE; t];
        let mut prefix = vec![Goldilocks::ONE; t];
        let mut product = Goldilocks::ONE;
        for i in 0..t {
            for j in 0..t {
                if i != j {
                    denominators[i] = denominators[i].const_mul(points[i].const_sub(points[j]));
                }
            }
            prefix[i] = product;
            product = product.const_mul(denominators[i]);
        }
        let mut inverse = product
            .checked_inv()
            .ok_or(PreprocessError::DuplicateOrZeroEvalPoint)?;
        for i in (0..t).rev() {
            let original = denominators[i];
            denominators[i] = inverse.const_mul(prefix[i]);
            inverse = inverse.const_mul(original);
        }
        let row = |x: Goldilocks| -> Vec<Goldilocks> {
            (0..t)
                .map(|i| {
                    let mut value = denominators[i];
                    for (j, point) in points[..t].iter().enumerate() {
                        if i != j {
                            value = value.const_mul(x.const_sub(*point));
                        }
                    }
                    value
                })
                .collect()
        };
        Ok(Self {
            t,
            n,
            zero: row(Goldilocks::ZERO),
            extra: points[t..].iter().map(|&x| row(x)).collect(),
        })
    }
    pub fn open(
        &self,
        shares: &[Goldilocks],
        phase: &'static str,
    ) -> Result<Goldilocks, PreprocessError> {
        if shares.len() != self.n {
            return Err(PreprocessError::DegreeCheckFailed { phase });
        }
        let dot = |row: &[Goldilocks]| {
            row.iter()
                .zip(&shares[..self.t])
                .fold(Goldilocks::ZERO, |acc, (&a, &b)| {
                    acc.const_add(a.const_mul(b))
                })
        };
        for (row, &actual) in self.extra.iter().zip(&shares[self.t..]) {
            if dot(row) != actual {
                return Err(PreprocessError::DegreeCheckFailed { phase });
            }
        }
        Ok(dot(&self.zero))
    }
}
pub struct Gf256OpeningTables {
    t: usize,
    n: usize,
    pub(super) zero: Vec<TowerGf256>,
    pub(super) extra: Vec<Vec<TowerGf256>>,
}
impl Gf256OpeningTables {
    pub fn new(t: usize, points: &[TowerGf256]) -> Result<Self, PreprocessError> {
        let n = points.len();
        if t == 0 || t > n {
            return Err(PreprocessError::InvalidThreshold { t, n });
        }
        validate_all_eval_points_gf256(points)?;
        let mut denominators = vec![TowerGf256::ONE; t];
        let mut prefix = vec![TowerGf256::ONE; t];
        let mut product = TowerGf256::ONE;
        for i in 0..t {
            for j in 0..t {
                if i != j {
                    denominators[i] = denominators[i].mul(points[i].add(points[j]));
                }
            }
            prefix[i] = product;
            product = product.mul(denominators[i]);
        }
        let mut inverse = product
            .inv()
            .ok_or(PreprocessError::DuplicateOrZeroEvalPoint)?;
        for i in (0..t).rev() {
            let original = denominators[i];
            denominators[i] = inverse.mul(prefix[i]);
            inverse = inverse.mul(original);
        }
        let row = |x: TowerGf256| -> Vec<TowerGf256> {
            (0..t)
                .map(|i| {
                    let mut value = denominators[i];
                    for (j, point) in points[..t].iter().enumerate() {
                        if i != j {
                            value = value.mul(x.add(*point));
                        }
                    }
                    value
                })
                .collect()
        };
        Ok(Self {
            t,
            n,
            zero: row(TowerGf256::ZERO),
            extra: points[t..].iter().map(|&x| row(x)).collect(),
        })
    }
    pub fn open(
        &self,
        shares: &[TowerGf256],
        phase: &'static str,
    ) -> Result<TowerGf256, PreprocessError> {
        if shares.len() != self.n {
            return Err(PreprocessError::DegreeCheckFailed { phase });
        }
        let dot = |row: &[TowerGf256]| {
            row.iter()
                .zip(&shares[..self.t])
                .fold(TowerGf256::ZERO, |acc, (&a, &b)| acc.add(a.mul(b)))
        };
        for (row, &actual) in self.extra.iter().zip(&shares[self.t..]) {
            if dot(row) != actual {
                return Err(PreprocessError::DegreeCheckFailed { phase });
            }
        }
        Ok(dot(&self.zero))
    }
}
impl Gf256OpeningTables {
    pub fn open_bitsliced(
        &self,
        shares: &[BitslicedGf256x64],
        phase: &'static str,
    ) -> Result<BitslicedGf256x64, PreprocessError> {
        if shares.len() != self.n {
            return Err(PreprocessError::DegreeCheckFailed { phase });
        }
        let dot = |row: &[TowerGf256]| {
            let mut out = [0; 8];
            for (&a, b) in row.iter().zip(&shares[..self.t]) {
                PublicGf256Matrix::from_public_scalar(a).scale_xor_into(&mut out, b);
            }
            out
        };
        for (row, actual) in self.extra.iter().zip(&shares[self.t..]) {
            if dot(row) != *actual {
                return Err(PreprocessError::DegreeCheckFailed { phase });
            }
        }
        Ok(dot(&self.zero))
    }
}

/// Interpolate the unique degree `< t` polynomial through `(pts[0..t], vals[0..t])` at `x = 0` AND
/// verify that ALL `eval_points[0..n]` are valid and `vals[t..n]` lie on that exact polynomial!
pub fn open_and_check_degree_gf256(
    t: usize,
    eval_points: &[TowerGf256],
    shares: &[TowerGf256],
    phase: &'static str,
) -> Result<TowerGf256, PreprocessError> {
    let n = eval_points.len();
    if t == 0 || t > n || shares.len() != n {
        return Err(PreprocessError::DegreeCheckFailed { phase });
    }
    validate_all_eval_points_gf256(eval_points)?;
    let points: Vec<_> = eval_points[..t]
        .iter()
        .map(|p| qsag_verified::Gf256(p.0))
        .collect();
    let mut values: Vec<_> = shares[..t]
        .iter()
        .map(|p| qsag_verified::Gf256(p.0))
        .collect();
    let secret = qsag_verified::shamir_lagrange_at_zero_gf256(&points, &values);
    qsag_asm::volatile_fill(&mut values, qsag_verified::Gf256(0));
    let secret = TowerGf256(secret.ok_or(PreprocessError::DuplicateOrZeroEvalPoint)?.0);
    for m in t..n {
        let xm = eval_points[m];
        let mut expected = TowerGf256::ZERO;
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
            expected = expected.add(li.mul(shares[i]));
        }
        if expected != shares[m] {
            return Err(PreprocessError::DegreeCheckFailed { phase });
        }
    }
    Ok(secret)
}

/// Bitsliced `64x` version of [`open_and_check_degree_gf256`] using [`PublicGf256Matrix`].
pub fn open_and_check_degree_bs_gf256(
    t: usize,
    eval_points: &[TowerGf256],
    shares: &[BitslicedGf256x64],
    phase: &'static str,
) -> Result<BitslicedGf256x64, PreprocessError> {
    let n = eval_points.len();
    if t == 0 || t > n || shares.len() != n {
        return Err(PreprocessError::DegreeCheckFailed { phase });
    }
    validate_all_eval_points_gf256(eval_points)?;
    let lambdas_0 = lagrange_weights_zero_gf256(&eval_points[..t])
        .ok_or(PreprocessError::DuplicateOrZeroEvalPoint)?;
    let mut secret = [0u64; 8];
    for q in 0..t {
        let mat = PublicGf256Matrix::from_public_scalar(lambdas_0[q]);
        mat.scale_xor_into(&mut secret, &shares[q]);
    }
    for m in t..n {
        let xm = eval_points[m];
        let mut expected = [0u64; 8];
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
            let mat = PublicGf256Matrix::from_public_scalar(li);
            mat.scale_xor_into(&mut expected, &shares[i]);
        }
        if expected != shares[m] {
            return Err(PreprocessError::DegreeCheckFailed { phase });
        }
    }
    Ok(secret)
}

/// Fold both independent MAC lanes in polynomial basis. Challenges are expanded
/// from a post-commitment coin by the four-way word stream; basis conversion is
/// performed once per bounded block, and each tag vector uses the batched dot kernel.
/// Returns tower-basis sums for the existing zero-masked committed sigma protocol.
pub(crate) fn fold_spdz_mac_words(
    coin: &[u8; 32],
    opened: &[BitslicedGf256x64],
    macs: &[Vec<[[Tower128; 64]; 2]>],
    t: usize,
) -> ([Tower128; 2], SecretBuffer<Vec<[Tower128; 2]>>) {
    use crate::sponge::keccak::{Cshake256WordStream4, cshake256_static_midstate};
    const MID: [u64; 25] = cshake256_static_midstate(b"QSAG.SPDZ.MAC.WORD_CHI/v2");
    const BLOCK: usize = 16;
    let mut stream = Cshake256WordStream4::new(&MID, coin);
    let mut raw = vec![0u64; BLOCK * 64 * 4];
    let mut chi = vec![0u128; BLOCK * 64];
    let mut values = vec![0u128; BLOCK * 64];
    let mut tags = SecretBuffer(vec![0u128; BLOCK * 64]);
    let mut x = [0u128; 2];
    let mut sums = SecretBuffer(vec![[0u128; 2]; t]);
    for (block, words) in opened.chunks(BLOCK).enumerate() {
        let len = words.len() * 64;
        stream.fill_words(&mut raw[..4 * len]);
        for (w, word) in words.iter().enumerate() {
            for bit in 0..64 {
                values[64 * w + bit] = Tower128::embed_gf256(bs_gf256_extract_lane(word, bit)).0;
            }
        }
        qsag_asm::tower128_to_poly128_batch_ct(&mut values[..len]);
        for lane in 0..2 {
            for (i, dst) in chi[..len].iter_mut().enumerate() {
                *dst = u128::from(raw[4 * i + 2 * lane])
                    | (u128::from(raw[4 * i + 2 * lane + 1]) << 64);
            }
            x[lane] ^= qsag_asm::gf2_128_dot(&values[..len], &chi[..len]);
            for q in 0..t {
                for w in 0..words.len() {
                    for bit in 0..64 {
                        tags[64 * w + bit] = macs[q][block * BLOCK + w][lane][bit].0;
                    }
                }
                qsag_asm::tower128_to_poly128_batch_ct(&mut tags[..len]);
                sums[q][lane] ^= qsag_asm::gf2_128_dot(&tags[..len], &chi[..len]);
            }
        }
    }
    qsag_asm::poly128_to_tower128_batch_ct(&mut x);
    qsag_asm::poly128_to_tower128_batch_ct(sums.as_flattened_mut());
    let result = SecretBuffer(
        sums.iter()
            .map(|v| [Tower128(v[0]), Tower128(v[1])])
            .collect(),
    );
    ([Tower128(x[0]), Tower128(x[1])], result)
}

/// Interpolate degree `< t` polynomial over `Goldilocks` at `0` AND verify `eval_points[0..n]` + `shares[t..n]`.
pub fn open_and_check_degree_goldilocks(
    t: usize,
    eval_points: &[Goldilocks],
    shares: &[Goldilocks],
    phase: &'static str,
) -> Result<Goldilocks, PreprocessError> {
    if t == 0 || t > eval_points.len() || shares.len() != eval_points.len() {
        return Err(PreprocessError::DegreeCheckFailed { phase });
    }
    if t == eval_points.len() {
        // No extra degree witnesses. Interpolate once without building an opening table.
        let points: Vec<_> = eval_points
            .iter()
            .map(|x| qsag_verified::Goldilocks(x.to_canonical_u64()))
            .collect();
        let mut values: Vec<_> = shares
            .iter()
            .map(|x| qsag_verified::Goldilocks(x.to_canonical_u64()))
            .collect();
        let result = qsag_verified::shamir_lagrange_at_zero_goldilocks(&points, &values);
        qsag_asm::volatile_fill(&mut values, qsag_verified::Goldilocks(0));
        return result
            .map(|x| Goldilocks::from_u64_reduced(x.0))
            .ok_or(PreprocessError::DuplicateOrZeroEvalPoint);
    }
    GoldilocksOpeningTables::new(t, eval_points)?.open(shares, phase)
}

/// Interpolate degree `< t` polynomial over `GoldilocksExt2` at `0` AND verify `shares[t..n]`.
pub fn open_and_check_degree_ext2(
    t: usize,
    eval_points: &[Goldilocks],
    shares: &[GoldilocksExt2],
    phase: &'static str,
) -> Result<GoldilocksExt2, PreprocessError> {
    let c0_shares: Vec<Goldilocks> = shares.iter().map(|s| s.c0).collect();
    let c1_shares: Vec<Goldilocks> = shares.iter().map(|s| s.c1).collect();
    let s0 = open_and_check_degree_goldilocks(t, eval_points, &c0_shares, phase)?;
    let s1 = open_and_check_degree_goldilocks(t, eval_points, &c1_shares, phase)?;
    Ok(GoldilocksExt2::new(s0, s1))
}

/// Batch bitsliced `64x` SPDZ committed opening + 2-lane `Tower128` `MacCheck` (`2^{-256}` soundness).
#[expect(
    clippy::too_many_arguments,
    reason = "Quorum, value shares, MAC shares and private randomness are separate protocol inputs"
)]
pub fn commit_and_open_spdz_bs_gf256_quorum(
    session_id: &[u8; 32],
    phase: &'static str,
    t: usize,
    quorum_eval_points: &[TowerGf256],
    shares: &[BitslicedGf256x64],
    mac_shares: &[[[Tower128; 64]; 2]],
    alpha_shares: &[[Tower128; 2]],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<BitslicedGf256x64, PreprocessError> {
    let values = SecretBuffer(shares.iter().map(|&x| vec![x]).collect::<Vec<_>>());
    let macs = SecretBuffer(mac_shares.iter().map(|&x| vec![x]).collect::<Vec<_>>());
    commit_and_open_spdz_bs_gf256_batch_quorum(
        session_id,
        phase,
        t,
        quorum_eval_points,
        &values,
        &macs,
        alpha_shares,
        party_rngs,
    )
    .map(|opened| opened[0])
}

/// Dishonest-majority commit-before-open + SPDZ `GoldilocksExt2` `MacCheck` over any quorum.
#[expect(
    clippy::too_many_arguments,
    reason = "Quorum, value shares, MAC shares and private randomness are separate protocol inputs"
)]
pub fn commit_and_open_spdz_goldilocks_quorum(
    session_id: &[u8; 32],
    phase: &'static str,
    t: usize,
    quorum_eval_points: &[Goldilocks],
    shares: &[Goldilocks],
    mac_shares: &[GoldilocksExt2],
    alpha_shares: &[GoldilocksExt2],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Goldilocks, PreprocessError> {
    let values = SecretBuffer(shares.iter().map(|&x| vec![x]).collect::<Vec<_>>());
    let macs = SecretBuffer(mac_shares.iter().map(|&x| vec![x]).collect::<Vec<_>>());
    commit_and_open_spdz_goldilocks_batch_quorum(
        session_id,
        phase,
        t,
        quorum_eval_points,
        &values,
        &macs,
        alpha_shares,
        party_rngs,
    )
    .map(|opened| opened[0])
}

/// Dishonest-majority commit-before-open + SPDZ `GoldilocksExt2` `MacCheck` for an extension wire.
#[expect(
    clippy::too_many_arguments,
    reason = "Quorum, value shares, MAC shares and private randomness are separate protocol inputs"
)]
pub fn commit_and_open_spdz_ext2_quorum(
    session_id: &[u8; 32],
    phase: &'static str,
    t: usize,
    quorum_eval_points: &[Goldilocks],
    shares: &[GoldilocksExt2],
    mac_shares: &[GoldilocksExt2],
    alpha_shares: &[GoldilocksExt2],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<GoldilocksExt2, PreprocessError> {
    let m = quorum_eval_points.len();
    if t == 0
        || m < t
        || shares.len() != m
        || mac_shares.len() != m
        || alpha_shares.len() != m
        || party_rngs.len() != m
    {
        return Err(PreprocessError::InvalidThreshold { t, n: m });
    }
    let mut salts = Vec::with_capacity(m);
    let mut coms = Vec::with_capacity(m);
    for p in 0..m {
        let salt = party_rngs[p].next_bytes32();
        let pid = (p as u64).to_be_bytes();
        let c0_b = shares[p].c0.to_canonical_u64().to_le_bytes();
        let c1_b = shares[p].c1.to_canonical_u64().to_le_bytes();
        let com = cshake256_32_multi_frame(
            b"QSAG.SPDZ.EXT2.OPEN.COM/v1",
            &[session_id, phase.as_bytes(), &pid, &c0_b, &c1_b, &salt],
        );
        salts.push(salt);
        coms.push(com);
    }
    for p in 0..m {
        let pid = (p as u64).to_be_bytes();
        let c0_b = shares[p].c0.to_canonical_u64().to_le_bytes();
        let c1_b = shares[p].c1.to_canonical_u64().to_le_bytes();
        let exp = cshake256_32_multi_frame(
            b"QSAG.SPDZ.EXT2.OPEN.COM/v1",
            &[session_id, phase.as_bytes(), &pid, &c0_b, &c1_b, &salts[p]],
        );
        wipe_bytes32(&mut salts[p]);
        if !ct_eq_bytes32(&exp, &coms[p]) {
            return Err(PreprocessError::ShareCommitMismatch { phase, party_id: p });
        }
    }

    let x_cand = open_and_check_degree_ext2(t, quorum_eval_points, shares, phase)?;
    let lambdas_0 = lagrange_weights_zero_goldilocks(&quorum_eval_points[..t])
        .ok_or(PreprocessError::DuplicateOrZeroEvalPoint)?;

    let additive = SecretBuffer(
        (0..m)
            .map(|p| {
                if p < t {
                    (mac_shares[p] - alpha_shares[p] * x_cand).mul_base(lambdas_0[p])
                } else {
                    GoldilocksExt2::ZERO
                }
            })
            .collect::<Vec<_>>(),
    );
    let w = blind_open_ext2(session_id, phase, &additive, None, party_rngs)?;
    if !w.ct_eq(GoldilocksExt2::ZERO) {
        return Err(PreprocessError::MacCheckFailed {
            phase,
            accused_party: None,
        });
    }
    Ok(x_cand)
}
