//! Production RLWE/KOS/Gilboa DKG benchmark; argument: power count, tree height.
//! Times preprocessing plus activation, not public leaf evaluation.
use std::collections::BTreeMap;
use std::sync::mpsc::{self, Receiver, Sender};
use std::thread;

use qsag_core::preprocessing::{PartyPrivateRng, try_establish_rlwe_ot_ext_channel};
use qsag_fts::ot::{AuthenticatedOtWire, CommittedCorrelatedOt, CommittedOtMessage};
use qsag_fts::{
    ParallelSeededDkgConfig, ParallelSeededDkgReservoir, ParallelSeededDkgRound1State,
    ParallelSeededError, ParallelSeededGilboaProducts, ParallelSeededParams,
    finalize_parallel_seeded_dkg_party,
};

fn fresh_entropy() -> Result<[u8; 32], ParallelSeededError> {
    let mut rng = PartyPrivateRng::from_os_rng(b"QSAG.CLI.CEREMONY.ENTROPY.V1")
        .map_err(|_| ParallelSeededError::BdozMacCheckFailed)?;
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
    ) -> Result<(), ParallelSeededError> {
        self.tx
            .get(&peer)
            .ok_or(ParallelSeededError::InvalidThresholdParameters)?
            .send((context, message))
            .map_err(|_| ParallelSeededError::BdozMacCheckFailed)
    }

    fn receive(
        &mut self,
        peer: u16,
        context: [u8; 32],
    ) -> Result<CommittedOtMessage, ParallelSeededError> {
        let (actual, message) = self
            .rx
            .get(&peer)
            .ok_or(ParallelSeededError::InvalidThresholdParameters)?
            .recv_timeout(std::time::Duration::from_secs(120))
            .map_err(|_| ParallelSeededError::BdozMacCheckFailed)?;
        if actual != context {
            return Err(ParallelSeededError::BdozMacCheckFailed);
        }
        Ok(message)
    }
}

/// Bootstrap real, direction-specific base OT using independently sampled local entropy.
/// The session binds the roster; party handles never receive another party's RNG or pads.
fn ot_endpoints(
    parties: &[u16],
    session: [u8; 32],
) -> Result<Vec<CommittedCorrelatedOt<LocalOtWire>>, ParallelSeededError> {
    if parties.len() < 2 || parties.windows(2).any(|w| w[0] >= w[1]) {
        return Err(ParallelSeededError::InvalidThresholdParameters);
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
                .map_err(|_| ParallelSeededError::BdozMacCheckFailed)?;
            let mut rrng = PartyPrivateRng::from_os_rng(b"QSAG.CLI.OT.RECEIVER.V1")
                .map_err(|_| ParallelSeededError::BdozMacCheckFailed)?;
            let (s, r) = try_establish_rlwe_ot_ext_channel(
                session,
                usize::from(sender),
                usize::from(receiver),
                &mut srng,
                &mut rrng,
            )
            .map_err(|_| ParallelSeededError::BdozMacCheckFailed)?;
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
                    .ok_or(ParallelSeededError::InvalidThresholdParameters)?,
                receivers[i][j]
                    .take()
                    .ok_or(ParallelSeededError::InvalidThresholdParameters)?,
            ));
        }
        let entropy = fresh_entropy().map_err(|_| ParallelSeededError::BdozMacCheckFailed)?;
        result.push(CommittedCorrelatedOt::new(
            parties[i], peers, entropy, wire,
        )?);
    }
    Ok(result)
}

fn main() {
    let count: usize = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "32".into())
        .parse()
        .unwrap();
    let height: usize = std::env::args()
        .nth(2)
        .unwrap_or_else(|| "3".into())
        .parse()
        .unwrap();
    let refills: usize = std::env::args()
        .nth(3)
        .unwrap_or_else(|| "0".into())
        .parse()
        .unwrap();
    let started = std::time::Instant::now();
    let roster = vec![0, 1, 2];
    let params = ParallelSeededParams {
        tree_height: height,
        ..ParallelSeededParams::CUSTODY_H10_W5
    };
    let config = ParallelSeededDkgConfig {
        params,
        roster: roster.clone(),
        session: [91; 32],
        power_count: count,
        beaver_count: 0,
    };
    let mut states: Vec<_> = roster
        .iter()
        .map(|&id| {
            ParallelSeededDkgRound1State::begin(config.clone(), id, fresh_entropy().unwrap())
                .unwrap()
        })
        .collect();
    let commits: Vec<_> = states.iter().map(|s| s.commitment()).collect();
    let opens: Vec<_> = states
        .iter_mut()
        .map(|s| s.open(&commits).unwrap())
        .collect();
    let mut inboxes: Vec<Vec<_>> = (0..3).map(|_| Vec::new()).collect();
    for state in &mut states {
        for p in state.private_packages().unwrap() {
            inboxes[p.recipient as usize].push(p);
        }
    }
    let backends: Vec<_> = ot_endpoints(&roster, [91; 32])
        .unwrap()
        .into_iter()
        .enumerate()
        .map(|(id, ot)| ParallelSeededGilboaProducts::new(id as u16, fresh_entropy().unwrap(), ot))
        .collect();
    eprintln!(
        "base_ot_seconds={:.6} powers={count} height={height}",
        started.elapsed().as_secs_f64()
    );
    let product_start = std::time::Instant::now();
    let mut pending: Vec<_> = thread::scope(|scope| {
        let handles: Vec<_> = states
            .into_iter()
            .zip(inboxes)
            .zip(backends)
            .map(|((state, packages), mut backend)| {
                let opens = &opens;
                scope.spawn(move || {
                    finalize_parallel_seeded_dkg_party(state, opens, packages, &mut backend)
                        .unwrap()
                })
            })
            .collect();
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });
    eprintln!(
        "products_seconds={:.6}",
        product_start.elapsed().as_secs_f64()
    );
    let commits: Vec<_> = pending.iter().map(|p| p.check_commitment()).collect();
    let coins: Vec<_> = pending
        .iter_mut()
        .map(|p| p.reveal_check_coin(&commits).unwrap())
        .collect();
    let masked: Vec<_> = pending
        .iter_mut()
        .map(|p| p.masked_shares(&coins).unwrap())
        .collect();
    let commits: Vec<_> = pending
        .iter_mut()
        .map(|p| p.tag_commitment(&masked).unwrap())
        .collect();
    let tags: Vec<_> = pending
        .iter_mut()
        .map(|p| p.open_tags(&commits).unwrap())
        .collect();
    let outputs: Vec<_> = pending
        .into_iter()
        .map(|p| p.activate(&tags).unwrap())
        .collect();
    let elapsed = started.elapsed().as_secs_f64();
    println!(
        "activated_parties={} powers={} height={} seconds={:.6} powers_per_second={:.3} projected_leaf_ms={:.3}",
        outputs.len(),
        count,
        height,
        elapsed,
        count as f64 / elapsed,
        elapsed * 52320.0 / count as f64 * 1000.0
    );
    if refills == 0 {
        return;
    }
    let mut reservoirs: Vec<_> = outputs
        .into_iter()
        .map(|o| ParallelSeededDkgReservoir::new(o).unwrap())
        .collect();
    for generation in 0..refills {
        let start = std::time::Instant::now();
        let mut states: Vec<_> = reservoirs
            .into_iter()
            .map(|r| {
                r.into_refill([92; 32], count, 0, fresh_entropy().unwrap())
                    .unwrap()
            })
            .collect();
        let commits: Vec<_> = states.iter().map(|s| s.commitment()).collect();
        let opens: Vec<_> = states
            .iter_mut()
            .map(|s| s.open(&commits).unwrap())
            .collect();
        let mut inboxes: Vec<Vec<_>> = (0..3).map(|_| Vec::new()).collect();
        for state in &mut states {
            for p in state.private_packages().unwrap() {
                inboxes[p.recipient as usize].push(p);
            }
        }
        // Fresh base-OT channels for each measured refill; include that cost.
        let backends: Vec<_> = ot_endpoints(&roster, [93; 32])
            .unwrap()
            .into_iter()
            .enumerate()
            .map(|(id, ot)| {
                ParallelSeededGilboaProducts::new(id as u16, fresh_entropy().unwrap(), ot)
            })
            .collect();
        let mut pending: Vec<_> = thread::scope(|scope| {
            let handles: Vec<_> = states
                .into_iter()
                .zip(inboxes)
                .zip(backends)
                .map(|((state, packages), mut backend)| {
                    let opens = &opens;
                    scope.spawn(move || state.finalize(opens, packages, &mut backend).unwrap())
                })
                .collect();
            handles.into_iter().map(|h| h.join().unwrap()).collect()
        });
        let commits: Vec<_> = pending.iter().map(|p| p.check_commitment()).collect();
        let coins: Vec<_> = pending
            .iter_mut()
            .map(|p| p.reveal_check_coin(&commits).unwrap())
            .collect();
        let masked: Vec<_> = pending
            .iter_mut()
            .map(|p| p.masked_shares(&coins).unwrap())
            .collect();
        let commits: Vec<_> = pending
            .iter_mut()
            .map(|p| p.tag_commitment(&masked).unwrap())
            .collect();
        let tags: Vec<_> = pending
            .iter_mut()
            .map(|p| p.open_tags(&commits).unwrap())
            .collect();
        reservoirs = pending
            .into_iter()
            .map(|p| p.activate(&tags).unwrap())
            .collect();
        println!(
            "refill={} height={} powers={} seconds={:.6}",
            generation + 1,
            height,
            count,
            start.elapsed().as_secs_f64()
        );
    }
}
