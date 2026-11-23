//! Dealerless enrollment for an arbitrary binary MSP. Every endpoint samples its own
//! additive contribution to every column (the first column is the PRF key). Each
//! owner receives only its matrix projections. Two independent masked codewords
//! tie those private rows to the very same authenticated columns used by Poseidon2.

#![forbid(unsafe_code)]
use super::*;

#[cfg(test)]
std::thread_local! {
    pub(super) static CORRUPT_ROW: core::cell::Cell<bool> = const { core::cell::Cell::new(false) };
}

const ROWS: u32 = 0x0508_0000;
const CHECK_COMMIT: u32 = ROWS + 1;
const CHECK_OPEN: u32 = ROWS + 2;

pub struct DealerlessPersonalReleaseDkg<W: DurableWal> {
    pub party: PersonalReleaseParty<W>,
    pub pk_seed: HemDigest4,
    pub commitment: HemDigest4,
}

/// Run at each custodian, with its independently provisioned latch/link keys and
/// private RNG. The ceremony id is single-use within the deployment and key epoch.
/// A dishonest endpoint can abort. All successful honest endpoints agree on the
/// same key. An MSP granting a singleton access is ineligible for split custody.
#[allow(clippy::too_many_arguments)]
pub fn run_dealerless_personal_release_dkg_over_wire<
    W: DurableWal,
    T: WireTransport,
    J: PoisonJournal,
>(
    deployment_id: [u8; 32],
    ceremony_id: [u8; 32],
    latch: PersonalBeltLatch<W>,
    program: MonotoneSpanProgram,
    pk_seed: HemDigest4,
    transport: T,
    rng: &mut PartyPrivateRng,
    journal: &mut J,
) -> Result<DealerlessPersonalReleaseDkg<W>, PersonalReleaseError> {
    let participants = latch.system().participants();
    let roster: Vec<_> = participants.iter().copied().collect();
    if roster.len() < 2
        || transport.parties() != roster.len()
        || roster.get(transport.party()) != Some(&latch.party())
        || program
            .row_owners()
            .iter()
            .any(|p| !participants.contains(p))
        || program.solve_reconstruction_weights(participants).is_none()
        || roster.iter().any(|p| {
            program
                .solve_reconstruction_weights(&PartySet::from([*p]))
                .is_some()
        })
    {
        return Err(PersonalReleaseError::ContextMismatch);
    }
    let seed_bytes = pk_seed.map(|v| v.to_be_bytes());
    let sid = h32(
        b"QSAG.PERSONAL.MSP.DKG/v1",
        &[
            &deployment_id,
            &ceremony_id,
            &latch.system().policy_digest(latch.key_epoch_context()),
            &span_program_digest(&program),
            seed_bytes.as_flattened(),
        ],
    );
    let mut keys = SecretBuffer(Vec::with_capacity(roster.len()));
    for &p in &roster {
        keys.push(if p == latch.party() {
            [0; 32]
        } else {
            latch
                .derive_wire_link_key(&sid, p)
                .ok_or(PersonalReleaseError::ContextMismatch)?
        });
    }
    journal
        .reserve_session(&sid)
        .map_err(|_| PersonalReleaseError::SessionPoisoned)?;
    let mut wire = MacSealedWireChannel::new_encrypted(
        transport,
        deployment_id,
        sid,
        core::mem::take(&mut keys.0),
    )?;
    let res = enroll(&program, &roster, sid, &pk_seed, &mut wire, rng);
    let (rows, commitment) = res.inspect_err(|_| {
        let _ = journal.mark_poisoned(&sid);
        send_abort_all(&mut wire);
    })?;
    let input = PersonalMspInput::new(latch.party(), program, rows)
        .map_err(|_| PersonalReleaseError::ContextMismatch)?;
    let mut party = PersonalReleaseParty::new(deployment_id, latch, input)?;
    party.enrolled_key = Some((pk_seed, commitment));
    Ok(DealerlessPersonalReleaseDkg {
        party,
        pk_seed,
        commitment,
    })
}

type Rows = SecretBuffer<Vec<HemDigest4>>;

fn enroll<T: WireTransport>(
    program: &MonotoneSpanProgram,
    roster: &[u16],
    sid: [u8; 32],
    pk_seed: &HemDigest4,
    wire: &mut MacSealedWireChannel<T>,
    rng: &mut PartyPrivateRng,
) -> Result<(Rows, HemDigest4), PersonalReleaseError> {
    let me = wire.party();
    let mut ot = PartyOtEndpoint::establish_over_wire(sid, roster, wire, rng)?;
    let alpha = SecretBuffer(rng.next_ext2());
    let width = 4 * program.num_cols();
    // Three independent column vectors X, B, C (four lanes per column).
    let columns = SecretBuffer(
        (0..3 * width)
            .map(|_| rng.next_goldilocks())
            .collect::<Vec<_>>(),
    );
    let auth = authenticate_goldilocks_batch_over_wire(
        wire, &mut ot, roster, &sid, *alpha, &columns, rng,
    )?;
    // Freeze all three rows at every honest owner before anyone reveals a coin share.
    let local_count = program
        .row_owners()
        .iter()
        .filter(|&&owner| owner == roster[me])
        .count();
    let mut received = SecretBuffer(Vec::with_capacity(local_count));
    for (row, &owner) in program.matrix_rows().iter().zip(program.row_owners()) {
        let peer = roster
            .binary_search(&owner)
            .map_err(|_| PersonalReleaseError::ContextMismatch)?;
        let mut local = SecretBuffer([Goldilocks::ZERO; 12]);
        for batch in 0..3 {
            for (col, _) in row.iter().enumerate().filter(|(_, v)| **v == 1) {
                for lane in 0..4 {
                    local[4 * batch + lane] += columns[batch * width + 4 * col + lane];
                }
            }
        }
        if peer == me {
            for sender in 0..roster.len() {
                if sender == me {
                    continue;
                }
                let bytes = recv_wire(wire, roster, sender, ROWS)?;
                if bytes.len() != 96 {
                    return Err(PersonalReleaseError::LaneRosterMismatch);
                }
                for (dst, raw) in local.iter_mut().zip(bytes.as_chunks::<8>().0) {
                    *dst += decode_gl_be(raw).ok_or(PersonalReleaseError::LaneRosterMismatch)?;
                }
            }
            received.push(*local);
        } else {
            #[cfg(test)]
            if CORRUPT_ROW.with(|flag| flag.replace(false)) {
                local[0] += Goldilocks::ONE;
            }
            let bytes = SecretBuffer(local.map(|v| v.to_be_bytes()));
            wire.send_frame(peer, ROWS, bytes.as_flattened())?;
        }
    }

    let coin = joint_coin_over_wire(wire, roster, &sid, b"dkg-row-check", &sid, true, rng)?;
    let mut xof = Cshake256Xof::new(b"QSAG.MSP.ROW.CHALLENGES/v1");
    xof.absorb(&coin);
    let challenges: [Goldilocks; 2] = core::array::from_fn(|_| {
        let mut b = [0; 24];
        xof.squeeze(&mut b);
        Goldilocks::from_bytes24_unbiased(&b)
    });
    let input = |i: usize| LocalAuthWire {
        val: columns[i],
        mac: auth[i],
    };
    let mut masks = SecretBuffer(Vec::with_capacity(2 * width));
    for (j, &challenge) in challenges.iter().enumerate() {
        for i in 0..width {
            masks.push(input(i).scale(challenge).add(input((j + 1) * width + i)));
        }
    }
    let opened = commit_open_and_check_goldilocks_over_wire(
        wire,
        &mut ot,
        roster,
        &sid,
        "dkg-masked-columns",
        CHECK_COMMIT,
        CHECK_OPEN,
        &masks,
        *alpha,
        rng,
    )?;
    let mut rows = SecretBuffer(Vec::with_capacity(received.len()));
    let mut rows_ok = 1u8;
    for (matrix, values) in program
        .matrix_rows()
        .iter()
        .zip(program.row_owners())
        .filter_map(|(r, p)| (*p == roster[me]).then_some(r))
        .zip(received.iter())
    {
        for (j, &challenge) in challenges.iter().enumerate() {
            for lane in 0..4 {
                let expected = matrix
                    .iter()
                    .enumerate()
                    .filter(|(_, v)| **v == 1)
                    .fold(Goldilocks::ZERO, |s, (col, _)| {
                        s + opened[j * width + 4 * col + lane]
                    });
                let rhs = values[lane] * challenge + values[4 * (j + 1) + lane];
                rows_ok &= u8::from(core::hint::black_box(expected.ct_eq(rhs)));
            }
        }
        rows.push([values[0], values[1], values[2], values[3]]);
    }
    if rows_ok == 0 {
        return Err(PersonalReleaseError::CommitmentMismatch);
    }
    let root = SecretBuffer(core::array::from_fn(input));
    let digest = authenticated_prf_check(
        wire,
        &mut ot,
        roster,
        h32(b"dkg/prf-check", &[&sid]),
        pk_seed,
        alpha,
        root,
        rng,
    )?;
    Ok((rows, digest))
}
