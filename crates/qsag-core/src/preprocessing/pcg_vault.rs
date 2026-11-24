//! Materialization of authenticated Keccak vaults from silent PCG correlations.

use super::*;

/// Validated tree depth for the experimental compact correlation format.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PcgTreeDepth {
    Depth14,
    Depth15,
    Depth16,
}
impl TryFrom<usize> for PcgTreeDepth {
    type Error = PreprocessError;
    fn try_from(depth: usize) -> Result<Self, Self::Error> {
        match depth {
            14 => Ok(Self::Depth14),
            15 => Ok(Self::Depth15),
            16 => Ok(Self::Depth16),
            _ => Err(PreprocessError::PcgDepthOutOfRange { depth }),
        }
    }
}

/// Minimum supported `SHAKE256` GGM puncturable-PRF tree depth (`2^14 = 16,384` leaves/tree).
pub const PCG_MIN_TREE_DEPTH: usize = 14;
/// Default `SHAKE256` GGM puncturable-PRF tree depth (`2^15 = 32,768` leaves/tree).
pub const PCG_DEFAULT_TREE_DEPTH: usize = 15;
/// Maximum supported `SHAKE256` GGM puncturable-PRF tree depth (`2^16 = 65,536` leaves/tree).
pub const PCG_MAX_TREE_DEPTH: usize = 16;

/// Number of packed 64-bit Boolean Beaver triple batches expanded per PCG seed (`1,025 * 64 = 65,600 > 65,536`).
pub const PCG_NUM_WORDS: usize = 1025;
/// Total authenticated Boolean Beaver triples expanded locally from one `< 24 KB` PCG seed (`65,600`).
pub const PCG_NUM_BOOL_TRIPLES: usize = PCG_NUM_WORDS * 64;
/// Number of full 128-bit `Tower128` Beaver triples bundled alongside the `65,600` Boolean triples.
pub const PCG_NUM_TOWER_TRIPLES: usize = 8;
/// Regular LPN noise weight (number of independent punctured GGM trees per primal/dual LPN bundle).
pub const PCG_TREES_PER_BUNDLE: usize = 4;
/// Number of Quasi-Cyclic LPN parity taps per tree block (`4 * 3 = 12`-regular LPN code).
pub const PCG_TAPS_PER_TREE: usize = 3;
/// Hard ceiling on serialized `PcgPartySeed` wire size (`24,576` bytes = `24 KB`).
pub const PCG_MAX_SEED_WIRE_BYTES: usize = 24 * 1024;
/// Compatibility entry point using uniform KOS/MASCOT preprocessing.
/// Compact sparse PCG correlations are not suitable as online Beaver masks.
pub fn run_dealerless_pcg_keccak_vaults(
    session_id: [u8; 32],
    t: usize,
    eval_points: &[TowerGf256],
    tree_depth: usize,
    num_triples_words: usize,
    ot_mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<PreprocessedKeccakPartyVault>, PreprocessError> {
    let n = eval_points.len();
    if t == 0 || t > n || n < 2 || num_triples_words > PCG_NUM_WORDS - 10 || party_rngs.len() != n {
        return Err(PreprocessError::InvalidThreshold { t, n });
    }
    validate_all_eval_points_gf256(eval_points)?;

    PcgTreeDepth::try_from(tree_depth)?;
    run_dealerless_pi_triple_f2(
        session_id,
        t,
        eval_points,
        num_triples_words,
        ot_mesh,
        party_rngs,
    )
}

/// Generate uniform authenticated masks under an existing MAC key. The factory splits the
/// request into raw ceremonies and combine pools itself; the returned vault owns all of them
/// and this API is not a streaming source.
#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the public preprocessing API used by other protocol modules"
)]
pub fn run_dealerless_pcg_keccak_vaults_with_alpha(
    session_id: [u8; 32],
    t: usize,
    eval_points: &[TowerGf256],
    tree_depth: usize,
    num_triples_words: usize,
    alpha_contribs: &[[Tower128; 2]],
    alpha_shamir: &[[Tower128; 2]],
    ot_mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<PreprocessedKeccakPartyVault>, PreprocessError> {
    let n = eval_points.len();
    if t == 0
        || t > n
        || n < 2
        || party_rngs.len() != n
        || alpha_contribs.len() != n
        || alpha_shamir.len() != n
    {
        return Err(PreprocessError::InvalidThreshold { t, n });
    }
    validate_all_eval_points_gf256(eval_points)?;
    PcgTreeDepth::try_from(tree_depth)?;

    if ot_mesh.n != n {
        return Err(PreprocessError::InvalidThreshold { t, n });
    }
    run_dealerless_pi_triple_f2_with_alpha(
        session_id,
        t,
        eval_points,
        num_triples_words,
        alpha_contribs,
        alpha_shamir,
        ot_mesh,
        party_rngs,
    )
}

/// Maximum 64-bit `KeccakBitTripleShare64` words materialized from a single pair of expanded
/// [`crate::pcg_dense::DensePcgExpandedVault`]s. A party can aim a selective failure at either
/// factor of a claimed PCG triple, so both are folded: 5 words (`320` triples) take two combine
/// passes of bucket sizes 5 and 6, that is 156 raw words, and `58,368 <= 65,536` Subfield-VOLE
/// rows including sacrifice and Shamir-check overhead. Six words no longer fit one vault.
pub const SILENT_PCG_KECCAK_CHUNK_WORDS: usize = 5;

/// Convert two locally expanded [`crate::pcg_dense::DensePcgExpandedVault`] lanes per party
/// directly into authenticated threshold Shamir-SPDZ [`PreprocessedKeccakPartyVault`]s.
/// Triple generation uses the silent vaults; additive MAC openings share one fresh OT mesh
/// for this standalone materialization.
///
/// Consumes silent Boolean Beaver triples from `vaults_lane0` and silent Subfield-VOLEs from
/// `(vaults_lane0, vaults_lane1)`, executes the two-instance recursive inner-product sacrifice
/// (`< 2^-256` false-batch soundness), combines raw triples under two post-sacrifice public
/// bit permutations (one folding `b`, one folding `a`, `2^-40` each) and verifies the Shamir
/// conversion of the result under `Π_MAC`. `num_triples` is at most
/// [`SILENT_PCG_KECCAK_CHUNK_WORDS`].
pub fn materialize_silent_pcg_keccak_vaults(
    session_id: [u8; 32],
    t: usize,
    eval_points: &[TowerGf256],
    num_triples: usize,
    vaults_lane0: &mut [crate::pcg_dense::DensePcgExpandedVault],
    vaults_lane1: &mut [crate::pcg_dense::DensePcgExpandedVault],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<PreprocessedKeccakPartyVault>, PreprocessError> {
    let n = eval_points.len();
    if t == 0
        || t > n
        || n < 2
        || vaults_lane0.len() != n
        || vaults_lane1.len() != n
        || party_rngs.len() != n
    {
        return Err(PreprocessError::InvalidThreshold { t, n });
    }
    validate_all_eval_points_gf256(eval_points)?;

    let mut alpha_contribs: Vec<[Tower128; 2]> = (0..n)
        .map(|p| [vaults_lane0[p].mac_alpha(), vaults_lane1[p].mac_alpha()])
        .collect();
    let mut alpha_shamir =
        spdz_share_existing_alpha_gf256(&session_id, t, eval_points, &alpha_contribs, party_rngs)?;
    let res = materialize_silent_pcg_keccak_vaults_with_alpha(
        session_id,
        t,
        eval_points,
        num_triples,
        &alpha_shamir,
        vaults_lane0,
        vaults_lane1,
        party_rngs,
    );
    for ac in &mut alpha_contribs {
        wipe_tower128(ac);
    }
    for ash in &mut alpha_shamir {
        wipe_tower128(ash);
    }
    res
}

/// Same as [`materialize_silent_pcg_keccak_vaults`], using pre-dealt Shamir MAC key shares
/// `alpha_shamir` matching `[vaults_lane0[p].mac_alpha(), vaults_lane1[p].mac_alpha()]`.
#[expect(
    clippy::too_many_arguments,
    reason = "Vault lanes, threshold evaluation points, Shamir MAC keys, and RNGs are separate protocol inputs"
)]
pub fn materialize_silent_pcg_keccak_vaults_with_alpha(
    session_id: [u8; 32],
    t: usize,
    eval_points: &[TowerGf256],
    num_triples: usize,
    alpha_shamir: &[[Tower128; 2]],
    vaults_lane0: &mut [crate::pcg_dense::DensePcgExpandedVault],
    vaults_lane1: &mut [crate::pcg_dense::DensePcgExpandedVault],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<PreprocessedKeccakPartyVault>, PreprocessError> {
    materialize_silent_pcg_keccak_vaults_on_mesh(
        session_id,
        t,
        eval_points,
        num_triples,
        alpha_shamir,
        vaults_lane0,
        vaults_lane1,
        None,
        party_rngs,
    )
}

#[expect(
    clippy::too_many_arguments,
    reason = "Silent vaults and an optional existing OT mesh are distinct inputs"
)]
fn materialize_silent_pcg_keccak_vaults_on_mesh(
    session_id: [u8; 32],
    t: usize,
    eval_points: &[TowerGf256],
    num_triples: usize,
    alpha_shamir: &[[Tower128; 2]],
    vaults_lane0: &mut [crate::pcg_dense::DensePcgExpandedVault],
    vaults_lane1: &mut [crate::pcg_dense::DensePcgExpandedVault],
    mesh: Option<&mut OtMesh>,
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<PreprocessedKeccakPartyVault>, PreprocessError> {
    let n = eval_points.len();
    if t == 0
        || t > n
        || n < 2
        || alpha_shamir.len() != n
        || vaults_lane0.len() != n
        || vaults_lane1.len() != n
        || party_rngs.len() != n
    {
        return Err(PreprocessError::InvalidThreshold { t, n });
    }
    validate_all_eval_points_gf256(eval_points)?;
    if num_triples > SILENT_PCG_KECCAK_CHUNK_WORDS {
        return Err(PreprocessError::VaultExhausted {
            kind: "silent PCG Keccak chunk",
        });
    }
    if num_triples == 0 {
        return Ok((0..n)
            .map(|p| PreprocessedKeccakPartyVault {
                party_id: p,
                eval_point: eval_points[p],
                mac_alpha_lanes: alpha_shamir[p],
                triples: Vec::new(),
                cursor: 0,
                poisoned: false,
            })
            .collect());
    }
    triple_f2::run_silent_pi_triple_f2(
        session_id,
        t,
        eval_points,
        num_triples,
        alpha_shamir,
        vaults_lane0,
        vaults_lane1,
        mesh,
        party_rngs,
        &mut triple_f2::PiTripleF2Faults::default(),
    )
}

/// Burn and locally expand two compact [`crate::pcg_dense::DensePcgPartySeed`] lanes per party
/// against `burn_tracker`, then materialize authenticated [`PreprocessedKeccakPartyVault`]s
/// with OT traffic confined to blinded MAC checks.
#[expect(
    clippy::too_many_arguments,
    reason = "Two seed lanes, burn tracker, threshold points and RNGs are distinct ceremony inputs"
)]
pub fn expand_and_materialize_silent_pcg_keccak_vaults<
    T: crate::pcg_dense::SeedBurnTracker + ?Sized,
>(
    session_id: [u8; 32],
    t: usize,
    eval_points: &[TowerGf256],
    num_triples: usize,
    seeds_lane0: Vec<crate::pcg_dense::DensePcgPartySeed>,
    seeds_lane1: Vec<crate::pcg_dense::DensePcgPartySeed>,
    burn_tracker: &mut T,
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<PreprocessedKeccakPartyVault>, PreprocessError> {
    let n = eval_points.len();
    if seeds_lane0.len() != n || seeds_lane1.len() != n {
        return Err(PreprocessError::InvalidThreshold { t, n });
    }
    let mut vaults0 = Vec::with_capacity(n);
    for seed in seeds_lane0 {
        vaults0.push(seed.expand_local(burn_tracker)?);
    }
    let mut vaults1 = Vec::with_capacity(n);
    for seed in seeds_lane1 {
        vaults1.push(seed.expand_local(burn_tracker)?);
    }
    materialize_silent_pcg_keccak_vaults(
        session_id,
        t,
        eval_points,
        num_triples,
        &mut vaults0,
        &mut vaults1,
        party_rngs,
    )
}

/// End-to-end silent `pcg_dense` preprocessing entrypoint: establishes compact expand-accumulate
/// dual-LPN [`crate::pcg_dense::DensePcgPartySeed`]s at `tree_depth`, burns and expands them locally
/// via `burn_tracker`, and materializes `num_triples_words` authenticated Shamir-SPDZ
/// [`PreprocessedKeccakPartyVault`]s without interactive KOS/MASCOT triple loops.
#[expect(
    clippy::too_many_arguments,
    reason = "Session, threshold parameters, tree depth, burn tracker, OT mesh and RNGs are distinct ceremony inputs"
)]
pub fn run_silent_pcg_keccak_vaults<T: crate::pcg_dense::SeedBurnTracker + ?Sized>(
    session_id: [u8; 32],
    t: usize,
    eval_points: &[TowerGf256],
    tree_depth: crate::pcg_dense::PcgTreeDepth,
    num_triples_words: usize,
    burn_tracker: &mut T,
    ot_mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<PreprocessedKeccakPartyVault>, PreprocessError> {
    let n = eval_points.len();
    if t == 0 || t > n || n < 2 || party_rngs.len() != n || ot_mesh.n != n {
        return Err(PreprocessError::InvalidThreshold { t, n });
    }
    validate_all_eval_points_gf256(eval_points)?;

    let (mut raw_contribs, _) = spdz_setup_alpha_gf256(&session_id, t, eval_points, party_rngs)?;
    for contrib in &mut raw_contribs {
        contrib[0].0 |= 1;
        contrib[1].0 |= 1;
    }
    let mut alpha_shamir =
        spdz_share_existing_alpha_gf256(&session_id, t, eval_points, &raw_contribs, party_rngs)?;
    let res = run_silent_pcg_keccak_vaults_with_alpha(
        session_id,
        t,
        eval_points,
        tree_depth,
        num_triples_words,
        &raw_contribs,
        &alpha_shamir,
        burn_tracker,
        ot_mesh,
        party_rngs,
    );
    for ac in &mut raw_contribs {
        wipe_tower128(ac);
    }
    for ash in &mut alpha_shamir {
        wipe_tower128(ash);
    }
    res
}

/// Same as [`run_silent_pcg_keccak_vaults`], bound to an existing 2-lane session SPDZ MAC key
/// `(alpha_contribs, alpha_shamir)` where every `alpha_contribs[p][lane]` has `LSB == 1`.
#[expect(
    clippy::too_many_arguments,
    reason = "Session, threshold parameters, tree depth, MAC keys, burn tracker, OT mesh and RNGs are distinct ceremony inputs"
)]
pub fn run_silent_pcg_keccak_vaults_with_alpha<T: crate::pcg_dense::SeedBurnTracker + ?Sized>(
    session_id: [u8; 32],
    t: usize,
    eval_points: &[TowerGf256],
    tree_depth: crate::pcg_dense::PcgTreeDepth,
    num_triples_words: usize,
    alpha_contribs: &[[Tower128; 2]],
    alpha_shamir: &[[Tower128; 2]],
    burn_tracker: &mut T,
    ot_mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<PreprocessedKeccakPartyVault>, PreprocessError> {
    let n = eval_points.len();
    if t == 0
        || t > n
        || n < 2
        || alpha_contribs.len() != n
        || alpha_shamir.len() != n
        || party_rngs.len() != n
        || ot_mesh.n != n
    {
        return Err(PreprocessError::InvalidThreshold { t, n });
    }
    validate_all_eval_points_gf256(eval_points)?;

    let alphas_lane0: SecretBuffer<Vec<Tower128>> =
        SecretBuffer((0..n).map(|p| alpha_contribs[p][0]).collect());
    let alphas_lane1: SecretBuffer<Vec<Tower128>> =
        SecretBuffer((0..n).map(|p| alpha_contribs[p][1]).collect());

    let mut acc_triples: Vec<Vec<KeccakBitTripleShare64>> = (0..n)
        .map(|_| Vec::with_capacity(num_triples_words))
        .collect();
    let mut chunk_idx = 0u64;
    let mut remaining = num_triples_words;

    while remaining > 0 {
        let take = remaining.min(SILENT_PCG_KECCAK_CHUNK_WORDS);
        let sid_lane0 = cshake256_32_multi_frame(
            b"QSAG.DPCG.SILENT.CHUNK/v1",
            &[&session_id, &chunk_idx.to_be_bytes(), &[0u8]],
        );
        let sid_lane1 = cshake256_32_multi_frame(
            b"QSAG.DPCG.SILENT.CHUNK/v1",
            &[&session_id, &chunk_idx.to_be_bytes(), &[1u8]],
        );
        let sid_mat = cshake256_32_multi_frame(
            b"QSAG.DPCG.SILENT.CHUNK/v1",
            &[&session_id, &chunk_idx.to_be_bytes(), &[2u8]],
        );
        chunk_idx += 1;

        let seeds0 = crate::pcg_dense::setup_dense_pcg_seeds_with_alphas(
            sid_lane0,
            tree_depth,
            &alphas_lane0,
            ot_mesh,
            party_rngs,
        )?;
        let seeds1 = crate::pcg_dense::setup_dense_pcg_seeds_with_alphas(
            sid_lane1,
            tree_depth,
            &alphas_lane1,
            ot_mesh,
            party_rngs,
        )?;
        let mut vaults0 = Vec::with_capacity(n);
        for seed in seeds0 {
            vaults0.push(seed.expand_local(burn_tracker)?);
        }
        let mut vaults1 = Vec::with_capacity(n);
        for seed in seeds1 {
            vaults1.push(seed.expand_local(burn_tracker)?);
        }
        let chunk_vaults = materialize_silent_pcg_keccak_vaults_on_mesh(
            sid_mat,
            t,
            eval_points,
            take,
            alpha_shamir,
            &mut vaults0,
            &mut vaults1,
            Some(&mut *ot_mesh),
            party_rngs,
        )?;
        for p in 0..n {
            // Keep the source entries initialized so their destructors erase the old allocation.
            acc_triples[p].extend(
                chunk_vaults[p]
                    .triples
                    .iter()
                    .map(|q| KeccakBitTripleShare64 {
                        a: q.a,
                        b: q.b,
                        c: q.c,
                        a_mac: q.a_mac,
                        b_mac: q.b_mac,
                        c_mac: q.c_mac,
                    }),
            );
        }
        remaining -= take;
    }

    Ok((0..n)
        .map(|p| PreprocessedKeccakPartyVault {
            party_id: p,
            eval_point: eval_points[p],
            mac_alpha_lanes: alpha_shamir[p],
            triples: core::mem::take(&mut acc_triples[p]),
            cursor: 0,
            poisoned: false,
        })
        .collect())
}
