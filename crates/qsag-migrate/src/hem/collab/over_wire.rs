//! Dealerless preprocessing and proving on the same transport.
use super::*;
use prep::PrepDemand;
use qsag_accel::keccak::cshake256_framed_32;
use qsag_agg::zk_hem::relation::Shape;
use qsag_core::{preprocessing::PartyPrivateRng, wipe::SecretBuffer};

/// The exact total tape length for each custodian.
pub fn ownership_prep_demand(
    statement: &OwnershipStatement,
    profile: Profile,
    parties: usize,
    secret_bytes: usize,
) -> Result<PrepDemand, ThresholdError> {
    ownership_demand(statement, profile, parties, secret_bytes)
        .ok_or(ThresholdError::Statement)?
        .into_iter()
        .try_fold(PrepDemand::default(), |d, (_, t, r)| {
            Ok(PrepDemand {
                triples: d.triples.checked_add(t).ok_or(ThresholdError::Statement)?,
                randoms: d.randoms.checked_add(r).ok_or(ThresholdError::Statement)?,
            })
        })
}

/// The common ceremony session is public. Each custodian hedges its private randomness
/// against that session and its own roster position.
pub fn prepare_party<T: Transport>(
    net: &mut T,
    session: &[u8; 32],
    local_seed: &[u8; 32],
    demand: &PrepDemand,
) -> Result<engine::Preprocessing, ThresholdError> {
    let sid = cshake256_framed_32(b"QSAG.COLLAB.PREP.SESSION/v1", &[session]);
    let seed = SecretBuffer(cshake256_framed_32(
        b"QSAG.COLLAB.PREP.PARTY/v1",
        &[local_seed, &sid, &(net.me() as u64).to_le_bytes()],
    ));
    let mut rng = PartyPrivateRng::from_seed(*seed, &sid);
    prep::run_party_preprocessing(sid, demand, net, &mut rng).map_err(ThresholdError::Prep)
}

fn prepare_ownership<T: Transport>(
    net: &mut T,
    session: &[u8; 32],
    local_seed: &[u8; 32],
    statement: &OwnershipStatement,
    profile: Profile,
    input: CustodyInput<'_>,
) -> Result<engine::Preprocessing, ThresholdError> {
    ownership_auxiliary_inputs(
        statement,
        input.xor_share.len(),
        input.path,
        input.merkle_root,
    )
    .ok_or(ThresholdError::Statement)?;
    let demand = ownership_prep_demand(statement, profile, net.parties(), input.xor_share.len())?;
    prepare_party(net, session, local_seed, &demand)
}

/// Prepare fresh material and prove with a private, independently sampled local seed.
pub fn prove_ownership_party_over_wire<T: Transport>(
    mut net: T,
    session: &[u8; 32],
    local_seed: &[u8; 32],
    statement: &OwnershipStatement,
    profile: Profile,
    input: CustodyInput<'_>,
) -> Result<ZkHemV2SplitProof, ThresholdError> {
    let prep = prepare_ownership(&mut net, session, local_seed, statement, profile, input)?;
    let mut e =
        Engine::new_ephemeral(net, prep, session, local_seed).map_err(ThresholdError::Mpc)?;
    checked_ownership(&mut e, statement, profile, input)
}

/// Prepare fresh material and durably burn it before the online proof.
#[cfg(feature = "std")]
#[allow(clippy::too_many_arguments)]
pub fn prove_ownership_party_over_wire_anchored<T: Transport>(
    mut net: T,
    session: &[u8; 32],
    local_seed: &[u8; 32],
    anchor: &dyn qsag_core::ExternalMonotoneAnchor,
    expected_prev_gen: Option<u64>,
    statement: &OwnershipStatement,
    profile: Profile,
    input: CustodyInput<'_>,
) -> Result<ZkHemV2SplitProof, ThresholdError> {
    let prep = prepare_ownership(&mut net, session, local_seed, statement, profile, input)?;
    let mut e = Engine::new_anchored(net, prep, session, local_seed, anchor, expected_prev_gen)
        .map_err(ThresholdError::Mpc)?;
    checked_ownership(&mut e, statement, profile, input)
}

/// Produce the split proof and verify the complete ownership statement locally.
pub fn checked_ownership<T: Transport>(
    engine: &mut Engine<T>,
    statement: &OwnershipStatement,
    profile: Profile,
    input: CustodyInput<'_>,
) -> Result<ZkHemV2SplitProof, ThresholdError> {
    let proof = prove_ownership_party(engine, statement, profile, input)?;
    verify_threshold_ownership(statement, profile, &proof)
        .then_some(proof)
        .ok_or(ThresholdError::Verification)
}

/// Prove a relation whose full assignment is held by custodian zero. All other
/// custodians pass `None` and learn only the public inputs and the proof.
#[allow(clippy::too_many_arguments)]
pub fn prove_relation_party_over_wire<T: Transport>(
    mut net: T,
    session: &[u8; 32],
    local_seed: &[u8; 32],
    shape: &Shape,
    public_inputs: &[Goldilocks],
    transcript_binding: &[u8],
    profile: Profile,
    assignment: Option<&[Goldilocks]>,
) -> Result<ZkHemV2SplitProof, ThresholdError> {
    if assignment.is_some() != (net.me() == 0)
        || assignment.is_some_and(|v| v.len() != shape.num_vars)
        || public_inputs.len() != shape.num_public
        || !(2..=qsag_agg::zk_hem::v2::pcs::MAX_STAGE0_SHARES).contains(&net.parties())
    {
        return Err(ThresholdError::Statement);
    }
    let (triples, randoms) =
        prover::prover_demand(shape, profile).ok_or(ThresholdError::Statement)?;
    let demand = PrepDemand {
        triples,
        randoms: randoms
            .checked_add(shape.num_vars)
            .and_then(|r| r.checked_add(qsag_agg::zk_hem::v2::params::LIMBS))
            .ok_or(ThresholdError::Statement)?,
    };
    let prep = prepare_party(&mut net, session, local_seed, &demand)?;
    let mut e =
        Engine::new_ephemeral(net, prep, session, local_seed).map_err(ThresholdError::Mpc)?;
    let z = e
        .input(0, assignment, shape.num_vars)
        .map_err(ThresholdError::Mpc)?;
    let proof = prover::prove_party(&mut e, shape, public_inputs, transcript_binding, profile, z)
        .map_err(ThresholdError::Prove)?;
    verify_split(shape, public_inputs, transcript_binding, profile, &proof)
        .then_some(proof)
        .ok_or(ThresholdError::Verification)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hem::collab::net::connect_tcp_stream_mesh;
    use std::net::{SocketAddr, TcpListener};
    use std::time::Duration;

    fn addrs(n: usize) -> Vec<SocketAddr> {
        let listeners: Vec<_> = (0..n)
            .map(|_| TcpListener::bind("127.0.0.1:0").unwrap())
            .collect();
        listeners.iter().map(|l| l.local_addr().unwrap()).collect()
    }

    #[test]
    fn tcp_custodians_preprocess_and_prove() {
        let addresses = addrs(3);
        let (shape, assignment) = prover::tests::small_relation(5);
        let publics = &assignment[1..=shape.num_public];
        let proofs = std::thread::scope(|s| {
            let jobs: Vec<_> = (0..3)
                .map(|me| {
                    let (shape, addresses) = (&shape, &addresses);
                    let mine = (me == 0).then_some(assignment.as_slice());
                    s.spawn(move || {
                        let keys = (0..3).map(|p| [(me + p + 1) as u8; 32]).collect();
                        let net = connect_tcp_stream_mesh(
                            [18; 32],
                            [19; 32],
                            me,
                            addresses,
                            keys,
                            [me as u8 + 20; 32],
                            Duration::from_secs(180),
                        )
                        .unwrap();
                        prove_relation_party_over_wire(
                            net,
                            &[19; 32],
                            &[me as u8 + 23; 32],
                            shape,
                            publics,
                            b"tcp relation",
                            Profile::default(),
                            mine,
                        )
                        .unwrap()
                    })
                })
                .collect();
            jobs.into_iter()
                .map(|j| j.join().unwrap())
                .collect::<Vec<_>>()
        });
        assert!(proofs.windows(2).all(|p| p[0] == p[1]));
        assert!(verify_split(
            &shape,
            publics,
            b"tcp relation",
            Profile::default(),
            &proofs[0]
        ));
    }

    /// #tooth Modifying one dealerless MAC share forces every honest engine to abort.
    #[test]
    fn altered_dealerless_mac_is_rejected() {
        use crate::hem::collab::net::channel_mesh;
        use qsag_core::preprocessing::PartyPrivateRng;
        let session = [109; 32];
        std::thread::scope(|scope| {
            for (me, mut net) in channel_mesh(session, 2).into_iter().enumerate() {
                scope.spawn(move || {
                    let seed = [71 + me as u8; 32];
                    let mut rng = PartyPrivateRng::from_seed(seed, &session);
                    let mut tape = prep::run_party_preprocessing(
                        session,
                        &PrepDemand {
                            triples: 0,
                            randoms: 1,
                        },
                        &mut net,
                        &mut rng,
                    )
                    .unwrap();
                    if me == 1 {
                        tape.randoms[0].m[0] += Goldilocks::ONE;
                    }
                    let mut engine = Engine::new_ephemeral(net, tape, &session, &seed).unwrap();
                    let value = engine.random().unwrap();
                    engine.open(&[value]).unwrap();
                    assert_eq!(engine.check(), Err(MpcError::MacCheck));
                });
            }
        });
    }

    /// #tooth A differently provisioned link never yields a usable mesh.
    #[test]
    fn tcp_handshake_rejects_wrong_pairwise_psk() {
        let addresses = addrs(2);
        std::thread::scope(|s| {
            let a = s.spawn(|| {
                connect_tcp_stream_mesh(
                    [1; 32],
                    [2; 32],
                    0,
                    &addresses,
                    alloc::vec![[3;32];2],
                    [4; 32],
                    Duration::from_secs(5),
                )
                .is_err()
            });
            assert!(
                connect_tcp_stream_mesh(
                    [1; 32],
                    [2; 32],
                    1,
                    &addresses,
                    alloc::vec![[5;32];2],
                    [6; 32],
                    Duration::from_secs(5)
                )
                .is_err()
            );
            assert!(a.join().unwrap());
        });
    }
}
