//! Genuine dealerless ceremony drivers for `qsag-cli` and its runnable examples.
use std::collections::BTreeMap;
use std::sync::mpsc::{self, Receiver, Sender};
use std::thread;

use qsag_accel::keccak::cshake256_framed_32;
use qsag_core::preprocessing::{PartyPrivateRng, try_establish_rlwe_ot_ext_channel};
use qsag_core::wipe::SecretBuffer;
use qsag_policy::ot::{AuthenticatedOtWire, CommittedCorrelatedOt, CommittedOtMessage};
use qsag_policy::{
    PolicyGuardDkgRound1, PolicySignerGuardShare, PolicyViolation,
    finalize_distributed_policy_guard,
};

fn fresh_entropy() -> Result<[u8; 32], PolicyViolation> {
    let mut rng = PartyPrivateRng::from_os_rng(b"QSAG.CLI.CEREMONY.ENTROPY.V1")
        .map_err(|_| PolicyViolation::BarrierBdozMacFailed)?;
    let mut entropy = [0; 32];
    rng.fill_bytes(&mut entropy);
    Ok(entropy)
}

/// Channels are allocated by the coordinator and moved exclusively to their endpoints.
/// Only public OT protocol messages and encrypted alternatives cross these channels.
struct LocalOtWire {
    tx: BTreeMap<u16, Sender<([u8; 32], CommittedOtMessage)>>,
    rx: BTreeMap<u16, Receiver<([u8; 32], CommittedOtMessage)>>,
}

impl AuthenticatedOtWire for LocalOtWire {
    fn send(
        &mut self,
        peer: u16,
        context: [u8; 32],
        message: CommittedOtMessage,
    ) -> Result<(), PolicyViolation> {
        self.tx
            .get(&peer)
            .ok_or(PolicyViolation::IntentBindingMismatch)?
            .send((context, message))
            .map_err(|_| PolicyViolation::BarrierBdozMacFailed)
    }

    fn receive(
        &mut self,
        peer: u16,
        context: [u8; 32],
    ) -> Result<CommittedOtMessage, PolicyViolation> {
        let (actual, message) = self
            .rx
            .get(&peer)
            .ok_or(PolicyViolation::IntentBindingMismatch)?
            .recv_timeout(std::time::Duration::from_secs(120))
            .map_err(|_| PolicyViolation::BarrierBdozMacFailed)?;
        if actual != context {
            return Err(PolicyViolation::BarrierBdozMacFailed);
        }
        Ok(message)
    }
}

/// Bootstrap real, direction-specific base OT using independently sampled local entropy.
/// The session binds the roster; party handles never receive another party's RNG or pads.
fn ot_endpoints(
    parties: &[u16],
    session: [u8; 32],
) -> Result<Vec<CommittedCorrelatedOt<LocalOtWire>>, PolicyViolation> {
    if parties.len() < 2 || parties.windows(2).any(|w| w[0] >= w[1]) {
        return Err(PolicyViolation::IntentBindingMismatch);
    }
    let mut wires: Vec<_> = parties
        .iter()
        .map(|_| LocalOtWire {
            tx: BTreeMap::new(),
            rx: BTreeMap::new(),
        })
        .collect();
    let n = parties.len();
    let mut senders: Vec<Vec<_>> = (0..n).map(|_| (0..n).map(|_| None).collect()).collect();
    let mut receivers: Vec<Vec<_>> = (0..n).map(|_| (0..n).map(|_| None).collect()).collect();
    for (i, &sender) in parties.iter().enumerate() {
        for (j, &receiver) in parties.iter().enumerate() {
            if i == j {
                continue;
            }
            let mut srng = PartyPrivateRng::from_os_rng(b"QSAG.CLI.OT.SENDER.V1")
                .map_err(|_| PolicyViolation::BarrierBdozMacFailed)?;
            let mut rrng = PartyPrivateRng::from_os_rng(b"QSAG.CLI.OT.RECEIVER.V1")
                .map_err(|_| PolicyViolation::BarrierBdozMacFailed)?;
            let (s, r) = try_establish_rlwe_ot_ext_channel(
                session,
                usize::from(sender),
                usize::from(receiver),
                &mut srng,
                &mut rrng,
            )
            .map_err(|_| PolicyViolation::BarrierBdozMacFailed)?;
            senders[i][j] = Some(s);
            receivers[j][i] = Some(r);
            let (tx, rx) = mpsc::channel();
            wires[i].tx.insert(receiver, tx);
            wires[j].rx.insert(sender, rx);
        }
    }
    let mut result = Vec::with_capacity(n);
    for (i, wire) in wires.into_iter().enumerate() {
        let mut peers = Vec::with_capacity(n - 1);
        for (j, &peer) in parties.iter().enumerate() {
            if i == j {
                continue;
            }
            peers.push((
                peer,
                senders[i][j]
                    .take()
                    .ok_or(PolicyViolation::IntentBindingMismatch)?,
                receivers[i][j]
                    .take()
                    .ok_or(PolicyViolation::IntentBindingMismatch)?,
            ));
        }
        let entropy = fresh_entropy().map_err(|_| PolicyViolation::BarrierBdozMacFailed)?;
        result.push(CommittedCorrelatedOt::new(
            parties[i], peers, entropy, wire,
        )?);
    }
    Ok(result)
}

/// Independent private seeds for one local policy enrollment.
pub fn fresh_guard_seeds<const N: usize>() -> std::io::Result<SecretBuffer<[[u8; 32]; N]>> {
    let mut seeds = SecretBuffer([[0; 32]; N]);
    for seed in seeds.iter_mut() {
        qsag_accel::fill_os_random(seed)?;
    }
    Ok(seeds)
}

/// Provision `PolicySignerGuardShare`s via the 3-round distributed `PolicyGuardDkgRound1`
/// ceremony (`PolicyGuardDkgRound1::new` -> `round2_open_seeds` -> `finalize_distributed_policy_guard`)
/// without any `test-dealer` dependency.
pub fn provision_distributed_policy_guards_with_capacity(
    ceremony_seed: [u8; 32],
    entropies: &[[u8; 32]],
    parties: &[u16],
    slots: usize,
) -> Result<Vec<PolicySignerGuardShare>, PolicyViolation> {
    let setup_id = cshake256_framed_32(b"QSAG.CLI.POLICY.DKG.SETUP.V1", &[&ceremony_seed]);
    if entropies.len() != parties.len() {
        return Err(PolicyViolation::IntentBindingMismatch);
    }
    let mut round1_states = Vec::with_capacity(parties.len());
    let mut commits = Vec::new();
    for (&id, &entropy) in parties.iter().zip(entropies) {
        let (st, msgs) =
            PolicyGuardDkgRound1::new_with_capacity(id, parties, setup_id, entropy, slots)?;
        round1_states.push((id, st));
        commits.extend(msgs);
    }

    let mut round2_states = Vec::with_capacity(parties.len());
    let mut opens = Vec::new();
    for (id, st) in round1_states {
        let incoming: Vec<_> = commits
            .iter()
            .filter(|c| c.recipient == id)
            .cloned()
            .collect();
        let (st2, msgs) = st.round2_open_seeds(&incoming)?;
        round2_states.push((id, st2));
        opens.extend(msgs);
    }

    let n = parties.len();
    let endpoints =
        ot_endpoints(parties, setup_id).map_err(|_| PolicyViolation::BarrierBdozMacFailed)?;

    let opens_ref = &opens;
    thread::scope(|scope| {
        let handles: Vec<_> = round2_states
            .into_iter()
            .zip(endpoints)
            .map(|((id, st2), mut ot)| {
                scope.spawn(move || {
                    let incoming: Vec<_> = opens_ref
                        .iter()
                        .filter(|o| o.recipient == id)
                        .cloned()
                        .collect();
                    finalize_distributed_policy_guard(st2, &incoming, &mut ot)
                })
            })
            .collect();

        let mut out = Vec::with_capacity(n);
        for h in handles {
            let guard = h
                .join()
                .map_err(|_| PolicyViolation::BarrierBdozMacFailed)??;
            out.push(guard);
        }
        Ok(out)
    })
}
