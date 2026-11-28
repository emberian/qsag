//! Threshold proving: the `zk-Hem v2` prover run by a quorum of custodians on a
//! secret-shared assignment (`QuinticGoldilocks`, `Fp5`).
//!
//! * [`net`]: authenticated, encrypted message transport between custodians.
//! * [`engine`]: MAC-authenticated additive sharing over Goldilocks & `Fp5` (SPDZ, with
//!   9-triple Toom-3 `Fp5` Beaver multiplication and pre-round-1 anti-rollback burn).
//! * [`custody`]: from `(k, n)` Shamir or XOR custody shares of a secret to authenticated
//!   shares of its bits.
//! * [`prep`]: the dealerless ceremony that produces [`engine::Preprocessing`].
//! * [`witgen`]: from shares of the secret's bits to shares of the whole assignment.
//! * [`prover`]: one custodian's side of the `zk-Hem v2` split proof, [`prover::prove_party`].
//! * [`prove_ownership_party`] / [`prove_ownership_party_anchored`]: end-to-end from a
//!   custody share to a [`ZkHemV2SplitProof`] (`QSAGZKS2`).
//! * [`verify_threshold_ownership`]: the verifier for threshold ownership statements.

mod over_wire;
pub use over_wire::*;
mod tape;

pub mod column_digest;
pub mod custody;
pub mod engine;
pub mod net;
pub mod prep;
pub mod prover;
#[cfg(any(test, feature = "testing-ephemeral"))]
pub mod ring_lpn;
pub mod witgen;

use alloc::vec::Vec;

use qsag_agg::field::Goldilocks;
use qsag_agg::zk_hem::v2::params::Profile;
use qsag_agg::zk_hem::v2::protocol::{ZkHemV2SplitProof, verify_split};

use super::relations::{
    OwnershipStatement, ownership_auxiliary_inputs, ownership_definitions, ownership_shape,
    ownership_transcript,
};
#[cfg(feature = "std")]
use engine::Preprocessing;
use engine::{Engine, MpcError, Stats};
use net::Transport;

/// Why a custodian's [`prove_ownership_party`] produced no proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ThresholdError {
    /// Session anti-rollback or preprocessing burn failed before round 1.
    Mpc(MpcError),
    Prep(prep::PrepError),
    Verification,
    /// The statement is malformed, or the custody input does not fit it.
    Statement,
    Input(custody::InputError),
    Witness(witgen::WitgenError),
    Prove(prover::ProveError),
}

/// The stages of [`prove_ownership_party`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Stage {
    /// Custody shares to authenticated shares of the secret's bits.
    Input,
    /// Shares of the secret's bits to shares of the assignment.
    Witness,
    /// The `zk-Hem v2` split proof.
    Proof,
}

/// What one custodian brings to [`prove_ownership_party`].
#[derive(Clone, Copy, Debug)]
pub struct CustodyInput<'a> {
    pub xor_share: &'a [u8],
    pub path: &'a [u32],
    pub merkle_root: Option<&'a [u8; 32]>,
}

impl<'a> CustodyInput<'a> {
    /// A share of a secret whose statement has no hidden path and no script tree.
    pub fn secret(xor_share: &'a [u8]) -> Self {
        Self {
            xor_share,
            path: &[],
            merkle_root: None,
        }
    }
}

/// Triples and uniform values one custodian consumes in [`prove_ownership_party`], by
/// stage, for a secret of `secret_bytes` bytes. `None` for a malformed statement or quorum size.
pub fn ownership_demand(
    statement: &OwnershipStatement,
    profile: Profile,
    parties: usize,
    secret_bytes: usize,
) -> Option<[(Stage, usize, usize); 3]> {
    if !(2..=qsag_agg::zk_hem::v2::pcs::MAX_STAGE0_SHARES).contains(&parties) {
        return None;
    }
    let (shape, defs) = ownership_definitions(statement)?;
    let input = custody::input_demand(parties, secret_bytes);
    let witness = witgen::demand(&shape, &defs).ok()?;
    let proof = prover::prover_demand(&shape, profile)?;
    Some([
        (Stage::Input, input.0, input.1),
        (Stage::Witness, witness.triples, witness.randoms),
        (Stage::Proof, proof.0, proof.1),
    ])
}

/// Construct an anchored [`Engine`] (burning `(session, prep.tape_id())` into `anchor`
/// before round 1 with the generation recorded alongside the tape) and run
/// [`prove_ownership_party`].
#[cfg(feature = "std")]
#[allow(clippy::too_many_arguments)]
pub fn prove_ownership_party_anchored<T: Transport>(
    net: T,
    prep: Preprocessing,
    session: &[u8; 32],
    local_seed: &[u8; 32],
    anchor: &dyn qsag_core::ExternalMonotoneAnchor,
    expected_prev_gen: Option<u64>,
    statement: &OwnershipStatement,
    profile: Profile,
    input: CustodyInput<'_>,
) -> Result<ZkHemV2SplitProof, ThresholdError> {
    let mut e = Engine::new_anchored(net, prep, session, local_seed, anchor, expected_prev_gen)
        .map_err(ThresholdError::Mpc)?;
    prove_ownership_party(&mut e, statement, profile, input)
}

/// One custodian's side of a threshold proof of `statement`. No custodian holds the
/// secret, any variable of the assignment that depends on it, or any share of another
/// custodian at any point.
pub fn prove_ownership_party<T: Transport>(
    e: &mut Engine<T>,
    statement: &OwnershipStatement,
    profile: Profile,
    input: CustodyInput<'_>,
) -> Result<ZkHemV2SplitProof, ThresholdError> {
    prove_ownership_party_observed(e, statement, profile, input, &mut |_, _| {})
}

/// [`prove_ownership_party`], reporting the engine's counters after each stage.
pub fn prove_ownership_party_observed<T: Transport>(
    e: &mut Engine<T>,
    statement: &OwnershipStatement,
    profile: Profile,
    input: CustodyInput<'_>,
    after: &mut dyn FnMut(Stage, Stats),
) -> Result<ZkHemV2SplitProof, ThresholdError> {
    let (shape, defs) = ownership_definitions(statement).ok_or(ThresholdError::Statement)?;
    let public_inputs = statement.public_inputs().ok_or(ThresholdError::Statement)?;
    let auxiliary = ownership_auxiliary_inputs(
        statement,
        input.xor_share.len(),
        input.path,
        input.merkle_root,
    )
    .ok_or(ThresholdError::Statement)?;
    let widths = witgen::input_bits(&defs);
    let fits = widths.len() == 1 + auxiliary.len()
        && widths[0] >= 8 * input.xor_share.len()
        && widths[1..]
            .iter()
            .zip(&auxiliary)
            .all(|(&w, a)| w == a.len());
    if !fits {
        return Err(ThresholdError::Statement);
    }
    let mut secret = qsag_core::wipe::SecretBuffer(
        custody::input_secret_bits(e, input.xor_share).map_err(ThresholdError::Input)?,
    );
    after(Stage::Input, e.stats);
    let padding = widths[0] - secret.len();
    qsag_core::wipe::secret_vec_reserve(&mut secret, padding);
    secret.resize(widths[0], e.public(Goldilocks::ZERO));
    let mut inputs = qsag_core::wipe::SecretBuffer(Vec::with_capacity(widths.len()));
    inputs.push(secret.into_inner());
    for bits in &auxiliary {
        inputs.push(
            bits.iter()
                .map(|&b| e.public(Goldilocks::from_u64_reduced(u64::from(b))))
                .collect(),
        );
    }
    let z = witgen::generate(e, &shape, &defs, &public_inputs, &inputs)
        .map_err(ThresholdError::Witness)?;
    after(Stage::Witness, e.stats);
    let proof = prover::prove_party(
        e,
        &shape,
        &public_inputs,
        &ownership_transcript(statement, profile),
        profile,
        z,
    )
    .map_err(ThresholdError::Prove)?;
    after(Stage::Proof, e.stats);
    Ok(proof)
}

/// Verify a threshold `zk-Hem v2` split proof of an ownership statement under `profile`.
pub fn verify_threshold_ownership(
    statement: &OwnershipStatement,
    profile: Profile,
    proof: &ZkHemV2SplitProof,
) -> bool {
    if proof.profile != profile {
        return false;
    }
    let (Some(shape), Some(public_inputs)) =
        (ownership_shape(statement), statement.public_inputs())
    else {
        return false;
    };
    verify_split(
        &shape,
        &public_inputs,
        &ownership_transcript(statement, profile),
        profile,
        proof,
    )
}

#[cfg(test)]
mod tests {
    use alloc::vec;
    use alloc::vec::Vec;
    use core::ops::{Add, Sub};

    use qsag_agg::field::{Goldilocks, encode_rs_coset_goldilocks, intt_goldilocks};
    use qsag_agg::pcs::hypercube_to_monomial_coeffs;
    use qsag_agg::zk_hem::SeedStream;
    use qsag_agg::zk_hem::v2::field5::Fp5;
    use qsag_agg::zk_hem::v2::protocol::layout_of;

    type E = Fp5;
    type F = Goldilocks;

    fn coins(tag: u8) -> SeedStream {
        SeedStream::new(b"QSAG.COLLAB.TEST.COINS/v2", &[tag; 32])
    }

    fn share_additive<T>(values: &[T], parties: usize, mut coin: impl FnMut() -> T) -> Vec<Vec<T>>
    where
        T: Copy + Sub<Output = T>,
    {
        assert!(parties >= 2);
        let mut shares: Vec<Vec<T>> = (0..parties)
            .map(|_| Vec::with_capacity(values.len()))
            .collect();
        for &value in values {
            let mut rest = value;
            for share in &mut shares[1..] {
                let r = coin();
                share.push(r);
                rest = rest - r;
            }
            shares[0].push(rest);
        }
        shares
    }

    fn reconstruct<T>(shares: &[Vec<T>]) -> Vec<T>
    where
        T: Copy + Add<Output = T>,
    {
        let mut out = shares[0].clone();
        for share in &shares[1..] {
            assert_eq!(share.len(), out.len());
            for (acc, &s) in out.iter_mut().zip(share) {
                *acc = *acc + s;
            }
        }
        out
    }

    fn codeword_share(table_share: &[F], blowup: usize) -> Vec<F> {
        encode_rs_coset_goldilocks(&hypercube_to_monomial_coeffs(table_share), blowup)
    }

    #[test]
    fn encoding_and_reduced_masking_commute_with_additive_sharing() {
        let mut s = coins(50);
        for (log_cells, parties, blowup) in [(4usize, 2usize, 4usize), (7, 3, 4), (9, 5, 16)] {
            let cells = 1usize << log_cells;
            let table: Vec<F> = (0..cells).map(|_| s.next_base()).collect();
            let shares = share_additive(&table, parties, || s.next_base());
            let share_words: Vec<Vec<F>> =
                shares.iter().map(|sh| codeword_share(sh, blowup)).collect();
            let word = codeword_share(&table, blowup);
            assert_eq!(word.len(), cells * blowup);
            assert_eq!(reconstruct(&share_words), word);
            assert!(share_words.iter().all(|w| w != &word));

            // Reduced Stage-0 masked polynomial `g = P_s + beta_R * R`: additive across custodians.
            let p_s: Vec<E> = (0..cells).map(|_| s.next_fp5()).collect();
            let p_shares = share_additive(&p_s, parties, || s.next_fp5());
            let r_shares: Vec<Vec<E>> = (0..parties)
                .map(|_| (0..cells + 2).map(|_| s.next_fp5()).collect())
                .collect();
            let r_sum = reconstruct(&r_shares);
            let beta_r = s.next_fp5();
            let g_shares: Vec<Vec<E>> = (0..parties)
                .map(|p| {
                    (0..cells + 2)
                        .map(|i| {
                            p_shares[p].get(i).copied().unwrap_or(E::ZERO) + beta_r * r_shares[p][i]
                        })
                        .collect()
                })
                .collect();
            let expected: Vec<E> = (0..cells + 2)
                .map(|i| p_s.get(i).copied().unwrap_or(E::ZERO) + beta_r * r_sum[i])
                .collect();
            assert_eq!(reconstruct(&g_shares), expected);
        }
    }

    fn decode(word: &[F], cells: usize) -> Vec<F> {
        let mut coeffs = word.to_vec();
        intt_goldilocks(&mut coeffs);
        assert!(coeffs[cells..].iter().all(|&c| c == F::ZERO));
        coeffs.truncate(cells);
        let shift_inv = F::NON_RESIDUE.inv();
        let mut power = F::ONE;
        for c in &mut coeffs {
            *c *= power;
            power *= shift_inv;
        }
        for b in 0..cells.trailing_zeros() {
            for idx in 0..cells {
                if (idx >> b) & 1 == 1 {
                    let lower = coeffs[idx ^ (1 << b)];
                    coeffs[idx] += lower;
                }
            }
        }
        coeffs
    }

    #[test]
    fn a_complete_stage0_codeword_reveals_the_table_whatever_the_blinders() {
        let (shape, assignment) = super::prover::tests::small_relation(5);
        let layout = layout_of(&shape).unwrap();
        let st0 = layout.schedule.stages[0];
        let cells = 1usize << layout.log_cells;
        let opened = (st0.num_queries.min((cells * st0.blowup) >> st0.step_vars)
            + qsag_agg::zk_hem::v2::params::LIMBS * qsag_agg::zk_hem::v2::params::MASK_POINTS)
            << st0.step_vars;
        assert_eq!(layout.blind_cells, opened);
        assert!(layout.blind_cells < cells * st0.blowup);

        let mut s = coins(60);
        let mut table = vec![F::ZERO; cells];
        table[..assignment.len()].copy_from_slice(&assignment);
        for slot in &mut table[cells - layout.blind_cells..] {
            *slot = s.next_base();
        }
        let word = codeword_share(&table, st0.blowup);
        assert_eq!(decode(&word, cells), table);

        let shares = share_additive(&table, 3, || s.next_base());
        for share in &shares {
            let recovered = decode(&codeword_share(share, st0.blowup), cells);
            assert_eq!(&recovered, share);
            assert_ne!(recovered[..assignment.len()], assignment[..]);
        }
    }

    #[test]
    #[ignore = "measurement"]
    fn measure_threshold_ownership() {
        use super::custody::tests::shamir;
        use super::custody::xor_share_from_shamir;
        use super::engine::Dealer;
        use super::engine::tests::run_parties;
        use super::witgen::tests::{derived_cases, reference_cases};
        use super::*;
        let profile = Profile::default();
        let only = std::env::var("COLLAB_MEASURE_ONLY").ok();
        let mut cases: Vec<_> = reference_cases()
            .into_iter()
            .map(|(st, _, secret)| (st, secret, Vec::new(), None))
            .collect();
        cases.extend(
            derived_cases()
                .into_iter()
                .map(|(st, _, secret, path, root)| (st, secret, path, root)),
        );
        for (parties, case) in [(3usize, 0usize), (3, 1), (5, 0), (3, 2), (3, 3)] {
            let (st, secret, path, root) = cases[case].clone();
            let label = std::format!("{:?} {:?} N={parties}", st.lock, st.source);
            if only.as_ref().is_some_and(|o| !label.contains(o.as_str())) {
                continue;
            }
            let shares = shamir(&secret, parties, parties + 2, 9);
            let quorum: Vec<usize> = (0..parties + 2).filter(|&p| p != 1).take(parties).collect();
            let stages = ownership_demand(&st, profile, parties, secret.len()).unwrap();
            let triples: usize = stages.iter().map(|s| s.1).sum();
            let randoms: usize = stages.iter().map(|s| s.2).sum();
            let preps = Dealer::new(parties, &[3 + case as u8; 32]).preprocessing(triples, randoms);
            let t = std::time::Instant::now();
            let out = run_parties(preps, |mut e| {
                let me = quorum[e.me()];
                let xor = xor_share_from_shamir(&quorum, me, &shares[me]).unwrap();
                let mut marks = Vec::new();
                let start = std::time::Instant::now();
                let proof = prove_ownership_party_observed(
                    &mut e,
                    &st,
                    profile,
                    CustodyInput {
                        xor_share: &xor,
                        path: &path,
                        merkle_root: root.as_ref(),
                    },
                    &mut |stage, stats| marks.push((stage, stats, start.elapsed().as_secs_f64())),
                );
                assert_eq!(e.remaining(), (0, 0), "demand is exact");
                (proof, marks)
            });
            let total_s = t.elapsed().as_secs_f64();
            let proof = out[0].0.clone().unwrap();
            assert!(out.iter().all(|(p, _)| p.as_ref() == Ok(&proof)));
            let bytes = proof.to_bytes();
            let t = std::time::Instant::now();
            assert!(verify_threshold_ownership(&st, profile, &proof));
            let verify_s = t.elapsed().as_secs_f64();
            let mut other = st.clone();
            other.epoch += 1;
            assert!(!verify_threshold_ownership(&other, profile, &proof));
            let all_sent: u64 = out
                .iter()
                .map(|(_, marks)| marks.last().unwrap().1.bytes_sent)
                .sum();
            std::println!(
                "{label}: proof={} bytes all_parties_sent={all_sent} wall={total_s:.1}s verify={verify_s:.2}s",
                bytes.len()
            );
            let mut before = (Stats::default(), 0.0);
            for ((stage, stats, at), demand) in out[0].1.iter().zip(&stages) {
                std::println!(
                    "  {stage:?}: triples={} randoms={} sent={} bytes rounds={} mac_checks={} time={:.1}s",
                    stats.triples_used - before.0.triples_used,
                    stats.randoms_used - before.0.randoms_used,
                    stats.bytes_sent - before.0.bytes_sent,
                    stats.rounds - before.0.rounds,
                    stats.mac_checks - before.0.mac_checks,
                    at - before.1,
                );
                assert_eq!(
                    (stats.triples_used - before.0.triples_used) as usize,
                    demand.1
                );
                assert_eq!(
                    (stats.randoms_used - before.0.randoms_used) as usize,
                    demand.2
                );
                before = (*stats, *at);
            }
        }
    }
}
