//! Genuine dealerless ceremony drivers for `qsag-cli` and its runnable examples.
//!
//! Replaces `trusted_dealer_setup_for_testing` in default builds so `qsag-cli` ships
//! with zero `test-dealer` feature dependencies while remaining deterministic from explicit
//! ceremony seeds when restoring durable checkpoints or running known-answer checks.

use std::collections::BTreeMap;
use std::sync::mpsc::{self, Receiver, Sender};
use std::thread;

use qsag_accel::ct::ct_zeroize_bytes;
use qsag_accel::keccak::cshake256_framed_32;
use qsag_core::preprocessing::{PartyPrivateRng, try_establish_rlwe_ot_ext_channel};
use qsag_fts::ot::{AuthenticatedOtWire, CommittedCorrelatedOt, CommittedOtMessage};
use qsag_fts::{
    LeafBurnPersistence, ParallelSeededDkgConfig, ParallelSeededDkgOutput,
    ParallelSeededDkgRound1State, ParallelSeededDkgSharePackage, ParallelSeededError,
    ParallelSeededGilboaProducts, ParallelSeededMerkleLayers, ParallelSeededParams,
    ParallelSeededPublicKey, ParallelSeededSignRequest, ParallelSeededSignResult,
    ParallelSeededSignSession, ParallelSeededSignature, assemble_parallel_seeded_public_key,
    finalize_parallel_seeded_dkg_party,
};
use qsag_policy::{
    PolicyGuardDkgRound1, PolicySignerGuardShare, PolicyViolation,
    finalize_distributed_policy_guard,
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

/// Provision `PolicySignerGuardShare`s via the 3-round distributed `PolicyGuardDkgRound1`
/// ceremony (`PolicyGuardDkgRound1::new` -> `round2_open_seeds` -> `finalize_distributed_policy_guard`)
/// without any `test-dealer` dependency.
pub fn provision_distributed_policy_guards(
    ceremony_seed: [u8; 32],
    parties: &[u16],
) -> Result<Vec<PolicySignerGuardShare>, PolicyViolation> {
    provision_distributed_policy_guards_with_capacity(
        ceremony_seed,
        parties,
        qsag_policy::BDOZ_PREPROC_SLOTS,
    )
}

pub fn provision_distributed_policy_guards_with_capacity(
    mut ceremony_seed: [u8; 32],
    parties: &[u16],
    slots: usize,
) -> Result<Vec<PolicySignerGuardShare>, PolicyViolation> {
    let setup_id = cshake256_framed_32(b"QSAG.CLI.POLICY.DKG.SETUP.V1", &[&ceremony_seed]);
    let mut entropies = Vec::with_capacity(parties.len());
    for &id in parties {
        entropies.push(cshake256_framed_32(
            b"QSAG.CLI.POLICY.DKG.PARTY_ENTROPY.V1",
            &[&ceremony_seed, &id.to_be_bytes()],
        ));
    }
    ct_zeroize_bytes(&mut ceremony_seed);

    let mut round1_states = Vec::with_capacity(parties.len());
    let mut commits = Vec::new();
    for (&id, entropy) in parties.iter().zip(entropies) {
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

/// Dealerless `ParallelSeededFts` threshold ceremony + distributed `ParallelSeededSignSession` driver.
pub struct DealerlessThresholdFtsSetup {
    pub pk: ParallelSeededPublicKey,
    pub public_tree_layers: ParallelSeededMerkleLayers,
    /// Activated DKG outputs. Each key share stays inside its output and is reached only through
    /// `ParallelSeededDkgOutput::share_mut`.
    outputs: Vec<ParallelSeededDkgOutput>,
    roster: Vec<u16>,
}

impl DealerlessThresholdFtsSetup {
    /// Compute the deterministic authenticated power-tuple budget required for `params`:
    /// `2^h` leaf preparations plus `2^h` epoch signatures. The underlying single-tree
    /// protocol still materializes these tuples; callers must budget memory accordingly.
    pub fn required_power_count(
        params: &ParallelSeededParams,
    ) -> Result<usize, ParallelSeededError> {
        params.validate()?;
        let leaves = 1usize
            .checked_shl(params.tree_height as u32)
            .ok_or(ParallelSeededError::InvalidThresholdParameters)?;
        let per_leaf = 2 * 48 * params.num_chains * params.winternitz_w;
        let per_sign = 2 * 48 * (1 + params.num_chains + params.target_sum);
        let total = leaves
            .checked_mul(per_leaf.saturating_add(per_sign))
            .ok_or(ParallelSeededError::InvalidThresholdParameters)?;
        if total == 0 {
            return Err(ParallelSeededError::InvalidThresholdParameters);
        }
        Ok(total)
    }

    /// Execute the full dealerless `ParallelSeededDkgRound1State` -> `finalize_parallel_seeded_dkg_party`
    /// -> 5-round BDOZ `activate` ceremony, followed by distributed `begin_leaf_preparation` (or verified
    /// cached Merkle layers when resuming an existing vault).
    pub fn run_ceremony(
        params: ParallelSeededParams,
        parties: usize,
        mut ceremony_seed: [u8; 32],
        cached_tree: Option<(ParallelSeededPublicKey, ParallelSeededMerkleLayers)>,
    ) -> Result<Self, ParallelSeededError> {
        if parties < 2 || parties > usize::from(u16::MAX) {
            ct_zeroize_bytes(&mut ceremony_seed);
            return Err(ParallelSeededError::InvalidThresholdParameters);
        }
        let power_count = match Self::required_power_count(&params) {
            Ok(c) => c,
            Err(e) => {
                ct_zeroize_bytes(&mut ceremony_seed);
                return Err(e);
            }
        };
        let roster: Vec<u16> = (0..parties as u16).collect();
        let dkg_session = cshake256_framed_32(b"QSAG.CLI.FTS.DKG.SESSION.V1", &[&ceremony_seed]);

        let config = ParallelSeededDkgConfig {
            params,
            roster: roster.clone(),
            session: dkg_session,
            power_count,
            beaver_count: 0,
        };

        let mut states = Vec::with_capacity(parties);
        for &id in &roster {
            let party_entropy = cshake256_framed_32(
                b"QSAG.CLI.FTS.DKG.PARTY_ENTROPY.V1",
                &[&ceremony_seed, &id.to_be_bytes()],
            );
            states.push(ParallelSeededDkgRound1State::begin(
                config.clone(),
                id,
                party_entropy,
            )?);
        }
        ct_zeroize_bytes(&mut ceremony_seed);

        let commits: Vec<_> = states
            .iter()
            .map(ParallelSeededDkgRound1State::commitment)
            .collect();
        let mut openings = Vec::with_capacity(parties);
        for st in &mut states {
            openings.push(st.open(&commits)?);
        }

        let mut inboxes: Vec<Vec<ParallelSeededDkgSharePackage>> =
            (0..parties).map(|_| Vec::new()).collect();
        for st in &mut states {
            for pkg in st.private_packages()? {
                let idx = usize::from(pkg.recipient);
                if idx >= parties {
                    return Err(ParallelSeededError::InvalidThresholdParameters);
                }
                inboxes[idx].push(pkg);
            }
        }

        let backends = ot_endpoints(&roster, dkg_session)?
            .into_iter()
            .zip(&roster)
            .map(|(ot, &id)| {
                let entropy =
                    fresh_entropy().map_err(|_| ParallelSeededError::BdozMacCheckFailed)?;
                Ok(ParallelSeededGilboaProducts::new(id, entropy, ot))
            })
            .collect::<Result<Vec<_>, ParallelSeededError>>()?;

        let openings_ref = &openings;
        let mut pending = thread::scope(|scope| -> Result<Vec<_>, ParallelSeededError> {
            let handles: Vec<_> = states
                .into_iter()
                .zip(inboxes)
                .zip(backends)
                .map(|((st, pkgs), mut backend)| {
                    scope.spawn(move || {
                        finalize_parallel_seeded_dkg_party(st, openings_ref, pkgs, &mut backend)
                    })
                })
                .collect();
            let mut res = Vec::with_capacity(parties);
            for h in handles {
                let item = h
                    .join()
                    .map_err(|_| ParallelSeededError::BdozMacCheckFailed)??;
                res.push(item);
            }
            Ok(res)
        })?;

        // 5-round BDOZ consistency barrier before releasing any party share
        let check_commits: Vec<_> = pending.iter().map(|p| p.check_commitment()).collect();
        let mut coins = Vec::with_capacity(parties);
        for p in &mut pending {
            coins.push(p.reveal_check_coin(&check_commits)?);
        }
        let coins_ref = &coins;
        let masked = thread::scope(|scope| -> Result<Vec<_>, ParallelSeededError> {
            let handles: Vec<_> = pending
                .iter_mut()
                .map(|p| scope.spawn(move || p.masked_shares(coins_ref)))
                .collect();
            let mut res = Vec::with_capacity(parties);
            for h in handles {
                res.push(
                    h.join()
                        .map_err(|_| ParallelSeededError::BdozMacCheckFailed)??,
                );
            }
            Ok(res)
        })?;
        let masked_ref = &masked;
        let tag_commits = thread::scope(|scope| -> Result<Vec<_>, ParallelSeededError> {
            let handles: Vec<_> = pending
                .iter_mut()
                .map(|p| scope.spawn(move || p.tag_commitment(masked_ref)))
                .collect();
            let mut res = Vec::with_capacity(parties);
            for h in handles {
                res.push(
                    h.join()
                        .map_err(|_| ParallelSeededError::BdozMacCheckFailed)??,
                );
            }
            Ok(res)
        })?;
        let mut tags = Vec::with_capacity(parties);
        for p in &mut pending {
            tags.push(p.open_tags(&tag_commits)?);
        }
        let tags_ref = &tags;
        let mut outputs: Vec<ParallelSeededDkgOutput> =
            thread::scope(|scope| -> Result<Vec<_>, ParallelSeededError> {
                let handles: Vec<_> = pending
                    .into_iter()
                    .map(|p| scope.spawn(move || p.activate(tags_ref)))
                    .collect();
                let mut res = Vec::with_capacity(parties);
                for h in handles {
                    res.push(
                        h.join()
                            .map_err(|_| ParallelSeededError::BdozMacCheckFailed)??,
                    );
                }
                Ok(res)
            })?;

        let pk_seed_bytes = outputs[0].pk_seed_bytes;
        // This driver never consumes the DKG's output Beaver triples: drop (and so wipe) them
        // here, where the outputs were previously consumed for their shares.
        for out in &mut outputs {
            out.beaver_triples.clear();
        }

        let (pk, public_tree_layers) = if let Some((cached_pk, cached_layers)) = cached_tree {
            if cached_pk.pk_seed_bytes != pk_seed_bytes || cached_layers.is_empty() {
                return Err(ParallelSeededError::InvalidAuthenticationPath);
            }
            let (rebuilt_pk, rebuilt_layers) =
                assemble_parallel_seeded_public_key(params, pk_seed_bytes, &cached_layers[0])?;
            if rebuilt_pk != cached_pk || rebuilt_layers != cached_layers {
                return Err(ParallelSeededError::InvalidAuthenticationPath);
            }
            (rebuilt_pk, rebuilt_layers)
        } else {
            let num_leaves = 1u32 << params.tree_height;
            let mut leaves = Vec::with_capacity(num_leaves as usize);
            for epoch in 0..num_leaves {
                let leaf_sid = cshake256_framed_32(
                    b"QSAG.CLI.FTS.LEAF_PREP.V1",
                    &[&dkg_session, &epoch.to_be_bytes()],
                );
                let mut sessions = Vec::with_capacity(parties);
                for out in &mut outputs {
                    sessions.push(ParallelSeededSignSession::begin_leaf_preparation(
                        out.share_mut(),
                        epoch,
                        leaf_sid,
                        &roster,
                    )?);
                }
                match drive_sign_sessions(&mut sessions)? {
                    ParallelSeededSignResult::Leaf {
                        epoch: actual,
                        digest,
                    } if actual == epoch => leaves.push(digest),
                    _ => return Err(ParallelSeededError::SignatureVerificationFailed),
                }
            }
            assemble_parallel_seeded_public_key(params, pk_seed_bytes, &leaves)?
        };

        Ok(Self {
            pk,
            public_tree_layers,
            outputs,
            roster,
        })
    }

    /// Sign `msg` at one-time `epoch` across all `ParallelSeededSignSession`s in lockstep,
    /// burning `epoch` in `persistence` for every party prior to opening any share.
    pub fn threshold_sign<P: LeafBurnPersistence>(
        &mut self,
        epoch: u32,
        msg: &[u8],
        session_id: [u8; 32],
        persistence: &mut P,
    ) -> Result<ParallelSeededSignature, ParallelSeededError> {
        let num_leaves = 1u32
            .checked_shl(self.pk.params.tree_height as u32)
            .ok_or(ParallelSeededError::InvalidThresholdParameters)?;
        if epoch >= num_leaves {
            return Err(ParallelSeededError::EpochOutOfRange);
        }
        let siblings: Vec<[u64; 4]> = (0..self.pk.params.tree_height)
            .map(|lvl| self.public_tree_layers[lvl][((epoch as usize) >> lvl) ^ 1])
            .collect();

        let req = ParallelSeededSignRequest {
            pk: &self.pk,
            epoch,
            msg,
            session_id,
            roster: &self.roster,
            siblings: &siblings,
        };

        let mut sessions = Vec::with_capacity(self.outputs.len());
        for out in &mut self.outputs {
            sessions.push(ParallelSeededSignSession::begin(
                out.share_mut(),
                &req,
                persistence,
            )?);
        }
        match drive_sign_sessions(&mut sessions)? {
            ParallelSeededSignResult::Signature(sig) => Ok(sig),
            _ => Err(ParallelSeededError::SignatureVerificationFailed),
        }
    }
}

fn drive_sign_sessions(
    sessions: &mut [ParallelSeededSignSession<'_>],
) -> Result<ParallelSeededSignResult, ParallelSeededError> {
    for _ in 0..2048 {
        if let Some(res) = sessions[0].result() {
            let res_cloned = res.clone();
            if sessions.iter().all(|s| s.result() == Some(&res_cloned)) {
                return Ok(res_cloned);
            }
            return Err(ParallelSeededError::SignatureVerificationFailed);
        }
        let mut outbound = Vec::with_capacity(sessions.len());
        for s in sessions.iter() {
            outbound.push(s.outbound()?);
        }
        for s in sessions.iter_mut() {
            s.advance(&outbound)?;
        }
    }
    Err(ParallelSeededError::GrindingExhausted)
}

#[cfg(test)]
mod tests {
    use super::*;
    use qsag_fts::ParallelSeededDkgProducts;
    use qsag_policy::PolicyAuthenticatedOt;

    #[test]
    fn power_budget_accepts_production_single_tree_height() {
        // Guard against reintroducing the old height-four CLI cap. This checks
        // the budget only: it does not pretend an eager single tree is a hypertree.
        assert!(
            DealerlessThresholdFtsSetup::required_power_count(
                &ParallelSeededParams::CUSTODY_H10_W5,
            )
            .is_ok()
        );
    }

    #[test]
    fn production_ot_policy_exchange_and_gilboa_product() {
        let endpoints = ot_endpoints(&[0, 1], [41; 32]).unwrap();
        let outputs = thread::scope(|scope| {
            let jobs: Vec<_> = endpoints
                .into_iter()
                .enumerate()
                .map(|(id, mut ot)| {
                    scope.spawn(move || {
                        let alternatives: Vec<_> = (0..65u128)
                            .map(|i| [1000 * id as u128 + i, 1000 * id as u128 + i + 100])
                            .collect();
                        let choices: Vec<_> = (0..65).map(|i| i % 2 != 0).collect();
                        let selected = ot
                            .exchange(
                                id as u16,
                                (1 - id) as u16,
                                [42; 32],
                                &alternatives,
                                &choices,
                            )
                            .unwrap();
                        for (i, value) in selected.iter().enumerate() {
                            assert_eq!(
                                *value,
                                1000 * (1 - id) as u128
                                    + i as u128
                                    + if choices[i] { 100 } else { 0 }
                            );
                        }
                        let mut products = ParallelSeededGilboaProducts::new(
                            id as u16,
                            fresh_entropy().unwrap(),
                            ot,
                        );
                        let operands: Vec<_> = (0..35u128).map(|i| i + 7 + id as u128).collect();
                        let result = products.product_shares([43; 32], 0, 1, &operands).unwrap();
                        assert!(products.product_shares([43; 32], 0, 1, &operands).is_err());
                        result
                    })
                })
                .collect();
            jobs.into_iter()
                .map(|j| j.join().unwrap())
                .collect::<Vec<_>>()
        });
        for (i, (left, right)) in outputs[0].iter().zip(&outputs[1]).enumerate() {
            assert_eq!(
                left ^ right,
                qsag_accel::gf2_128::gf2_128_mul(i as u128 + 7, i as u128 + 8)
            );
        }
    }
}
