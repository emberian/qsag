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
     DEFAULT_BEAVER_TRIPLE_POOL, LeafBurnPersistence, ParallelSeededDkgConfig,
    ParallelSeededDkgOutput, ParallelSeededDkgRefillUnverified, ParallelSeededDkgReservoir,
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

/// Dealerless `ParallelSeededFts` threshold ceremony + bounded `ParallelSeededDkgReservoir`
/// persistence/refill + distributed `ParallelSeededSignSession` driver.
pub struct DealerlessThresholdFtsSetup {
    pub pk: ParallelSeededPublicKey,
    pub public_tree_layers: ParallelSeededMerkleLayers,
    /// Activated per-custodian reservoirs. Each key share stays inside its reservoir and is
    /// reached only through `ParallelSeededDkgReservoir::share_mut`.
    reservoirs: Vec<ParallelSeededDkgReservoir>,
    roster: Vec<u16>,
}

fn refill_reservoirs(
    reservoirs: &mut Vec<ParallelSeededDkgReservoir>,
    session: [u8; 32],
    power_count: usize,
) -> Result<(), ParallelSeededError> {
    let parties = reservoirs.len();
    if parties < 2 || power_count == 0 || power_count > DEFAULT_BEAVER_TRIPLE_POOL {
        return Err(ParallelSeededError::InvalidThresholdParameters);
    }
    let roster = reservoirs[0].committee().to_vec();
    let old = core::mem::take(reservoirs);
    let mut states = Vec::with_capacity(parties);
    for res in old {
        let ent = fresh_entropy()?;
        states.push(res.into_refill(session, power_count, 0, ent)?);
    }

    let commits: Vec<_> = states.iter().map(|s| s.commitment()).collect();
    let mut openings = Vec::with_capacity(parties);
    for st in &mut states {
        openings.push(st.open(&commits)?);
    }

    let mut inboxes: Vec<Vec<ParallelSeededDkgSharePackage>> =
        (0..parties).map(|_| Vec::new()).collect();
    for st in &mut states {
        for pkg in st.private_packages()? {
            let pos = roster
                .binary_search(&pkg.recipient)
                .map_err(|_| ParallelSeededError::InvalidThresholdParameters)?;
            inboxes[pos].push(pkg);
        }
    }

    let ot_sid = cshake256_framed_32(
        b"QSAG.CLI.FTS.REFILL.OT.V1",
        &[&session, &(power_count as u64).to_be_bytes()],
    );
    let backends = ot_endpoints(&roster, ot_sid)?
        .into_iter()
        .zip(&roster)
        .map(|(ot, &id)| {
            let entropy = fresh_entropy().map_err(|_| ParallelSeededError::BdozMacCheckFailed)?;
            Ok(ParallelSeededGilboaProducts::new(id, entropy, ot))
        })
        .collect::<Result<Vec<_>, ParallelSeededError>>()?;

    let openings_ref = &openings;
    let mut pending: Vec<ParallelSeededDkgRefillUnverified> =
        thread::scope(|scope| -> Result<Vec<_>, ParallelSeededError> {
            let handles: Vec<_> = states
                .into_iter()
                .zip(inboxes)
                .zip(backends)
                .map(|((st, pkgs), mut backend)| {
                    scope.spawn(move || st.finalize(openings_ref, pkgs, &mut backend))
                })
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
    let mut activated: Vec<ParallelSeededDkgReservoir> =
        thread::scope(|scope| -> Result<Vec<_>, ParallelSeededError> {
            let handles: Vec<_> = pending
                .into_iter()
                .map(|p| scope.spawn(move || p.activate(tags_ref)))
                .collect();
            let mut res = Vec::with_capacity(parties);
            for h in handles {
                let mut r = h
                    .join()
                    .map_err(|_| ParallelSeededError::BdozMacCheckFailed)??;
                let _ = r.take_beaver_triples();
                res.push(r);
            }
            Ok(res)
        })?;
    *reservoirs = core::mem::take(&mut activated);
    Ok(())
}

impl DealerlessThresholdFtsSetup {
    /// Compute the total power-tuple work across `2^h` leaf preparations plus `2^h` signatures.
    /// Streaming [`ParallelSeededDkgReservoir`] refills cap each DKG/refill flight to
    /// [`DEFAULT_BEAVER_TRIPLE_POOL`] (`131_072`) tuples regardless of tree height.
    pub fn required_power_count(
        params: &ParallelSeededParams,
    ) -> Result<usize, ParallelSeededError> {
        params.validate()?;
        let leaves = 1usize
            .checked_shl(params.tree_height as u32)
            .ok_or(ParallelSeededError::InvalidThresholdParameters)?;
        let per_leaf = params.leaf_preparation_power_count();
        let per_sign = params.signing_power_count();
        let total = leaves
            .checked_mul(per_leaf.saturating_add(per_sign))
            .ok_or(ParallelSeededError::InvalidThresholdParameters)?;
        if total == 0 {
            return Err(ParallelSeededError::InvalidThresholdParameters);
        }
        Ok(total)
    }

    fn bounded_initial_power_budget(
        params: &ParallelSeededParams,
        has_cached_tree: bool,
    ) -> Result<usize, ParallelSeededError> {
        params.validate()?;
        let per_leaf = params.leaf_preparation_power_count();
        let per_sign = params.signing_power_count();
        if per_leaf == 0
            || per_sign == 0
            || per_leaf > DEFAULT_BEAVER_TRIPLE_POOL
            || per_sign > DEFAULT_BEAVER_TRIPLE_POOL
        {
            return Err(ParallelSeededError::InvalidThresholdParameters);
        }
        if has_cached_tree {
            return Ok(per_sign);
        }
        let num_leaves = 1usize
            .checked_shl(params.tree_height as u32)
            .ok_or(ParallelSeededError::InvalidThresholdParameters)?;
        let max_leaves_per_batch = (DEFAULT_BEAVER_TRIPLE_POOL / per_leaf).max(1);
        let initial_leaves = num_leaves.min(max_leaves_per_batch);
        let leaf_budget = initial_leaves
            .checked_mul(per_leaf)
            .ok_or(ParallelSeededError::InvalidThresholdParameters)?;
        if initial_leaves == num_leaves
            && let Some(with_sign) = leaf_budget.checked_add(per_sign)
            && with_sign <= DEFAULT_BEAVER_TRIPLE_POOL
        {
            return Ok(with_sign);
        }
        Ok(leaf_budget)
    }

    /// Execute the bounded dealerless `ParallelSeededDkgRound1State` -> `finalize_parallel_seeded_dkg_party`
    /// -> 5-round BDOZ `activate` ceremony, streaming leaf-preparation refills (`into_refill`)
    /// across arbitrary tree heights and pre-populating one signing batch in each custodian's
    /// [`ParallelSeededDkgReservoir`].
    pub fn run_ceremony(
        params: ParallelSeededParams,
        parties: usize,
        mut ceremony_seed: [u8; 32],
        cached_tree: Option<(ParallelSeededPublicKey, ParallelSeededMerkleLayers)>,
    ) -> Result<Self, ParallelSeededError> {
        if parties < 2 || parties > 255 {
            ct_zeroize_bytes(&mut ceremony_seed);
            return Err(ParallelSeededError::InvalidThresholdParameters);
        }
        let power_count = match Self::bounded_initial_power_budget(&params, cached_tree.is_some()) {
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
        let outputs: Vec<ParallelSeededDkgOutput> =
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
        let mut reservoirs = Vec::with_capacity(parties);
        for mut out in outputs {
            out.beaver_triples.clear();
            reservoirs.push(ParallelSeededDkgReservoir::new(out)?);
        }

        let per_leaf = params.leaf_preparation_power_count();
        let per_sign = params.signing_power_count();
        let max_leaves_per_batch = (DEFAULT_BEAVER_TRIPLE_POOL / per_leaf).max(1);

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
            let num_leaves = 1usize << params.tree_height;
            let mut leaves = Vec::with_capacity(num_leaves);
            for ep_idx in 0..num_leaves {
                if reservoirs.iter().any(|r| r.remaining_powers() < per_leaf) {
                    let rem_leaves = num_leaves - ep_idx;
                    let batch_leaves = rem_leaves.min(max_leaves_per_batch);
                    let leaf_budget = batch_leaves
                        .checked_mul(per_leaf)
                        .ok_or(ParallelSeededError::InvalidThresholdParameters)?;
                    let batch_powers = if batch_leaves == rem_leaves
                        && let Some(with_sign) = leaf_budget.checked_add(per_sign)
                        && with_sign <= DEFAULT_BEAVER_TRIPLE_POOL
                    {
                        with_sign
                    } else {
                        leaf_budget
                    };
                    let refill_sid = cshake256_framed_32(
                        b"QSAG.CLI.FTS.LEAF_REFILL.V1",
                        &[&dkg_session, &(ep_idx as u32).to_be_bytes()],
                    );
                    refill_reservoirs(&mut reservoirs, refill_sid, batch_powers)?;
                }
                let epoch = ep_idx as u32;
                let leaf_sid = cshake256_framed_32(
                    b"QSAG.CLI.FTS.LEAF_PREP.V1",
                    &[&dkg_session, &epoch.to_be_bytes()],
                );
                let mut sessions = Vec::with_capacity(parties);
                for res in &mut reservoirs {
                    sessions.push(ParallelSeededSignSession::begin_leaf_preparation(
                        res.share_mut(),
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
            // Pre-populate at least one full signing power batch so the first `qsag sign`
            // executes directly from persisted reservoirs with zero DKG / zero OT!
            if reservoirs.iter().any(|r| r.remaining_powers() < per_sign) {
                let topup_sid =
                    cshake256_framed_32(b"QSAG.CLI.FTS.SIGN_TOPUP.V1", &[&dkg_session]);
                refill_reservoirs(&mut reservoirs, topup_sid, per_sign)?;
            }
            assemble_parallel_seeded_public_key(params, pk_seed_bytes, &leaves)?
        };

        Ok(Self {
            pk,
            public_tree_layers,
            reservoirs,
            roster,
        })
    }

    /// Serialize every custodian's activated [`ParallelSeededDkgReservoir`] (`QSFTSRS1`)
    /// along with the shared monotonic reservoir generation.
    pub fn serialize_reservoirs(
        &self,
    ) -> Result<(u64, Vec<qsag_core::wipe::SecretVec<u8>>), ParallelSeededError> {
        let generation = self
            .reservoirs
            .first()
            .ok_or(ParallelSeededError::InvalidThresholdParameters)?
            .generation();
        let mut blobs = Vec::with_capacity(self.reservoirs.len());
        for r in &self.reservoirs {
            if r.generation() != generation {
                return Err(ParallelSeededError::InvalidThresholdParameters);
            }
            blobs.push(r.to_secret_bytes()?);
        }
        Ok((generation, blobs))
    }

    /// Rehydrate a [`DealerlessThresholdFtsSetup`] directly from persisted per-custodian
    /// [`ParallelSeededDkgReservoir`] bytes (`0` re-DKG!).
    pub fn from_persisted_reservoirs<B: AsRef<[u8]>>(
        pk: ParallelSeededPublicKey,
        public_tree_layers: ParallelSeededMerkleLayers,
        expected_generation: u64,
        blobs: &[B],
    ) -> Result<Self, ParallelSeededError> {
        pk.params.validate()?;
        if blobs.len() < 2 || blobs.len() > 255 {
            return Err(ParallelSeededError::InvalidThresholdParameters);
        }
        let (rebuilt_pk, rebuilt_layers) = assemble_parallel_seeded_public_key(
            pk.params,
            pk.pk_seed_bytes,
            public_tree_layers
                .first()
                .ok_or(ParallelSeededError::InvalidAuthenticationPath)?,
        )?;
        if rebuilt_pk != pk || rebuilt_layers != public_tree_layers {
            return Err(ParallelSeededError::InvalidAuthenticationPath);
        }
        let mut reservoirs = Vec::with_capacity(blobs.len());
        let mut roster = Vec::with_capacity(blobs.len());
        for raw in blobs {
            let r = ParallelSeededDkgReservoir::from_secret_bytes(raw.as_ref())?;
            if r.pk_seed_bytes() != pk.pk_seed_bytes
                || r.params() != pk.params
                || r.generation() != expected_generation
            {
                return Err(ParallelSeededError::InvalidThresholdParameters);
            }
            roster.push(r.party_id());
            reservoirs.push(r);
        }
        if !roster.windows(2).all(|w| w[0] < w[1])
            || reservoirs.iter().any(|r| r.committee() != roster.as_slice())
        {
            return Err(ParallelSeededError::InvalidThresholdParameters);
        }
        Ok(Self {
            pk,
            public_tree_layers,
            reservoirs,
            roster,
        })
    }

    /// Sign `msg` at one-time `epoch` across all `ParallelSeededSignSession`s in lockstep,
    /// burning `epoch` in `persistence` for every party prior to opening any share and
    /// automatically running a bounded `into_refill` if the persisted pool is depleted.
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
        let per_sign = self.pk.params.signing_power_count();
        if self
            .reservoirs
            .iter()
            .any(|r| r.remaining_powers() < per_sign)
        {
            let refill_sid = cshake256_framed_32(
                b"QSAG.CLI.FTS.SIGN_REFILL.V1",
                &[&session_id, &self.pk.pk_seed_bytes, &epoch.to_be_bytes()],
            );
            refill_reservoirs(&mut self.reservoirs, refill_sid, per_sign)?;
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

        let mut sessions = Vec::with_capacity(self.reservoirs.len());
        for res in &mut self.reservoirs {
            sessions.push(ParallelSeededSignSession::begin(
                res.share_mut(),
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
        let init = DealerlessThresholdFtsSetup::bounded_initial_power_budget(
            &ParallelSeededParams::CUSTODY_H10_W5,
            false,
        )
        .unwrap();
        assert!(init <= DEFAULT_BEAVER_TRIPLE_POOL);
    }

    #[test]
    fn reservoir_persistence_signs_without_redkg_and_refills_cleanly() {
        let params = ParallelSeededParams {
            tree_height: 1,
            ..ParallelSeededParams::CUSTODY_H10_W5
        };
        let setup = DealerlessThresholdFtsSetup::run_ceremony(params, 2, [0x37; 32], None).unwrap();
        let pk = setup.pk.clone();
        let layers = setup.public_tree_layers.clone();
        let (gen0, blobs0) = setup.serialize_reservoirs().unwrap();
        drop(setup);

        // Stale or wrong generation must be rejected.
        assert!(
            DealerlessThresholdFtsSetup::from_persisted_reservoirs(
                pk.clone(),
                layers.clone(),
                gen0 + 1,
                &blobs0,
            )
            .is_err()
        );

        // Epoch 0 signs directly from the persisted reservoirs with 0 DKG!
        let mut restored0 = DealerlessThresholdFtsSetup::from_persisted_reservoirs(
            pk.clone(),
            layers.clone(),
            gen0,
            &blobs0,
        )
        .unwrap();
        struct MemLatch(std::collections::BTreeSet<(u16, u32)>);
        impl LeafBurnPersistence for MemLatch {
            fn burn_epoch_before_sign(
                &mut self,
                _key: &[u8; 32],
                party_id: u16,
                epoch: u32,
                use_count: u8,
            ) -> Result<(), ParallelSeededError> {
                if use_count != 1 || !self.0.insert((party_id, epoch)) {
                    return Err(ParallelSeededError::PersistenceFailed);
                }
                Ok(())
            }
        }
        let mut latch = MemLatch(std::collections::BTreeSet::new());
        let sig0 = restored0
            .threshold_sign(0, b"first-persisted-sign", [0xAA; 32], &mut latch)
            .unwrap();
        qsag_fts::verify_parallel_seeded_fts(
            &pk,
            b"first-persisted-sign",
            &sig0,
            &qsag_accel::CpuReferenceBackend::new(),
        )
        .unwrap();
        let (gen1, blobs1) = restored0.serialize_reservoirs().unwrap();
        assert_eq!(gen1, gen0, "first sign consumed pre-populated reservoir without DKG");
        drop(restored0);

        // Epoch 1 triggers automatic bounded `into_refill` because reservoir powers were spent.
        let mut restored1 = DealerlessThresholdFtsSetup::from_persisted_reservoirs(
            pk.clone(),
            layers,
            gen1,
            &blobs1,
        )
        .unwrap();
        let sig1 = restored1
            .threshold_sign(1, b"second-refill-sign", [0xBB; 32], &mut latch)
            .unwrap();
        qsag_fts::verify_parallel_seeded_fts(
            &pk,
            b"second-refill-sign",
            &sig1,
            &qsag_accel::CpuReferenceBackend::new(),
        )
        .unwrap();
        let (gen2, _) = restored1.serialize_reservoirs().unwrap();
        assert_eq!(gen2, gen1 + 1, "second sign automatically refilled reservoir");
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
