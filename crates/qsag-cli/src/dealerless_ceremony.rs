//! Genuine dealerless ceremony drivers for `qsag-cli` and its runnable examples.
//!
//! Replaces `trusted_dealer_setup_for_testing` in default builds so `qsag-cli` ships
//! with zero `test-dealer` feature dependencies while remaining deterministic from explicit
//! ceremony seeds when restoring durable checkpoints or running known-answer checks.

use std::collections::BTreeSet;
use std::sync::mpsc::{self, Receiver, Sender};
use std::thread;

use qsag_accel::ct::{ct_zeroize_bytes, ct_zeroize_u128s};
use qsag_accel::gf2_128::gf2_128_mul;
use qsag_accel::keccak::{cshake256_framed_32, cshake256_framed_xof};
use qsag_fts::{
    LeafBurnPersistence, ParallelSeededDkgConfig, ParallelSeededDkgOutput,
    ParallelSeededDkgProducts, ParallelSeededDkgRound1State, ParallelSeededDkgSharePackage,
    ParallelSeededError, ParallelSeededMerkleLayers, ParallelSeededParams,
    ParallelSeededPartyShare, ParallelSeededPublicKey, ParallelSeededSignRequest,
    ParallelSeededSignResult, ParallelSeededSignSession, ParallelSeededSignature,
    assemble_parallel_seeded_public_key, finalize_parallel_seeded_dkg_party,
};
use qsag_policy::{
    PolicyAuthenticatedOt, PolicyGuardDkgRound1, PolicySignerGuardShare, PolicyViolation,
    finalize_distributed_policy_guard,
};

struct ZeroizePairs(Vec<[u128; 2]>);

impl Drop for ZeroizePairs {
    fn drop(&mut self) {
        for pair in &mut self.0 {
            ct_zeroize_u128s(pair);
        }
    }
}

struct ZeroizeU128s(Vec<u128>);

impl Drop for ZeroizeU128s {
    fn drop(&mut self) {
        ct_zeroize_u128s(&mut self.0);
    }
}

struct PolicyOtFrame {
    sender: u16,
    recipient: u16,
    domain: [u8; 32],
    alternatives: ZeroizePairs,
}

struct ScopedPolicyOt {
    party_id: u16,
    tx: Vec<(u16, Sender<PolicyOtFrame>)>,
    rx: Vec<(u16, Receiver<PolicyOtFrame>)>,
    seen: BTreeSet<(u16, [u8; 32])>,
}

impl PolicyAuthenticatedOt for ScopedPolicyOt {
    fn exchange(
        &mut self,
        local_party: u16,
        peer: u16,
        domain: [u8; 32],
        alternatives: &[[u128; 2]],
        choices: &[bool],
    ) -> Result<Vec<u128>, PolicyViolation> {
        if local_party != self.party_id
            || local_party == peer
            || alternatives.len() != choices.len()
            || !self.seen.insert((peer, domain))
        {
            return Err(PolicyViolation::IntentBindingMismatch);
        }
        let tx = self
            .tx
            .iter()
            .find(|(id, _)| *id == peer)
            .map(|(_, ch)| ch)
            .ok_or(PolicyViolation::IntentBindingMismatch)?;
        let rx = self
            .rx
            .iter()
            .find(|(id, _)| *id == peer)
            .map(|(_, ch)| ch)
            .ok_or(PolicyViolation::IntentBindingMismatch)?;

        let outbound = PolicyOtFrame {
            sender: local_party,
            recipient: peer,
            domain,
            alternatives: ZeroizePairs(alternatives.to_vec()),
        };

        let incoming = if local_party < peer {
            tx.send(outbound)
                .map_err(|_| PolicyViolation::BarrierBdozMacFailed)?;
            rx.recv()
                .map_err(|_| PolicyViolation::BarrierBdozMacFailed)?
        } else {
            let inc = rx
                .recv()
                .map_err(|_| PolicyViolation::BarrierBdozMacFailed)?;
            tx.send(outbound)
                .map_err(|_| PolicyViolation::BarrierBdozMacFailed)?;
            inc
        };

        if incoming.sender != peer
            || incoming.recipient != local_party
            || incoming.domain != domain
            || incoming.alternatives.0.len() != choices.len()
        {
            return Err(PolicyViolation::IntentBindingMismatch);
        }
        let selected: Vec<u128> = incoming
            .alternatives
            .0
            .iter()
            .zip(choices.iter())
            .map(|(pair, &bit)| pair[usize::from(bit)])
            .collect();
        drop(incoming);
        Ok(selected)
    }
}

/// Provision `PolicySignerGuardShare`s via the 3-round distributed `PolicyGuardDkgRound1`
/// ceremony (`PolicyGuardDkgRound1::new` -> `round2_open_seeds` -> `finalize_distributed_policy_guard`)
/// without any `test-dealer` dependency.
pub fn provision_distributed_policy_guards(
    mut ceremony_seed: [u8; 32],
    parties: &[u16],
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
    for (&id, entropy) in parties.iter().zip(entropies.into_iter()) {
        let (st, msgs) = PolicyGuardDkgRound1::new(id, parties, setup_id, entropy)?;
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
    let mut tx_grid: Vec<Vec<(u16, Sender<PolicyOtFrame>)>> =
        (0..n).map(|_| Vec::with_capacity(n.saturating_sub(1))).collect();
    let mut rx_grid: Vec<Vec<(u16, Receiver<PolicyOtFrame>)>> =
        (0..n).map(|_| Vec::with_capacity(n.saturating_sub(1))).collect();
    for i in 0..n {
        for j in 0..n {
            if i == j {
                continue;
            }
            let (tx, rx) = mpsc::channel();
            tx_grid[i].push((parties[j], tx));
            rx_grid[j].push((parties[i], rx));
        }
    }

    let opens_ref = &opens;
    thread::scope(|scope| {
        let handles: Vec<_> = round2_states
            .into_iter()
            .zip(tx_grid)
            .zip(rx_grid)
            .map(|(((id, st2), tx), rx)| {
                scope.spawn(move || {
                    let incoming: Vec<_> = opens_ref
                        .iter()
                        .filter(|o| o.recipient == id)
                        .cloned()
                        .collect();
                    let mut ot = ScopedPolicyOt {
                        party_id: id,
                        tx,
                        rx,
                        seen: BTreeSet::new(),
                    };
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

struct MaskedProductPacket {
    context: [u8; 32],
    values: ZeroizeU128s,
}

struct PairwiseBeaverProductChannel {
    party_id: u16,
    pad_secret: [u8; 32],
    tx: Vec<Option<Sender<MaskedProductPacket>>>,
    rx: Vec<Option<Receiver<MaskedProductPacket>>>,
    seen: BTreeSet<(u16, u16, [u8; 32])>,
}

impl Drop for PairwiseBeaverProductChannel {
    fn drop(&mut self) {
        ct_zeroize_bytes(&mut self.pad_secret);
    }
}

impl PairwiseBeaverProductChannel {
    fn send_packet(
        &self,
        peer: u16,
        context: [u8; 32],
        values: Vec<u128>,
    ) -> Result<(), ParallelSeededError> {
        let sender = self
            .tx
            .get(usize::from(peer))
            .and_then(Option::as_ref)
            .ok_or(ParallelSeededError::InvalidThresholdParameters)?;
        sender
            .send(MaskedProductPacket {
                context,
                values: ZeroizeU128s(values),
            })
            .map_err(|_| ParallelSeededError::BdozMacCheckFailed)
    }

    fn recv_packet(
        &self,
        peer: u16,
        expected_context: [u8; 32],
        expected_len: usize,
    ) -> Result<ZeroizeU128s, ParallelSeededError> {
        let receiver = self
            .rx
            .get(usize::from(peer))
            .and_then(Option::as_ref)
            .ok_or(ParallelSeededError::InvalidThresholdParameters)?;
        let pkt = receiver
            .recv()
            .map_err(|_| ParallelSeededError::BdozMacCheckFailed)?;
        if pkt.context != expected_context || pkt.values.0.len() != expected_len {
            return Err(ParallelSeededError::BdozMacCheckFailed);
        }
        Ok(pkt.values)
    }
}

impl ParallelSeededDkgProducts for PairwiseBeaverProductChannel {
    fn party_id(&self) -> u16 {
        self.party_id
    }

    fn product_shares(
        &mut self,
        context: [u8; 32],
        sender: u16,
        receiver: u16,
        operand: &[u128],
    ) -> Result<Vec<u128>, ParallelSeededError> {
        if sender == receiver {
            return Err(ParallelSeededError::InvalidThresholdParameters);
        }
        if self.party_id != sender && self.party_id != receiver {
            if !operand.is_empty() {
                return Err(ParallelSeededError::InvalidThresholdParameters);
            }
            return Ok(Vec::new());
        }
        if !self.seen.insert((sender, receiver, context)) {
            return Err(ParallelSeededError::BdozMacCheckFailed);
        }
        let count = operand.len();
        if count == 0 {
            return Ok(Vec::new());
        }

        // Derive correlated Beaver triples `(a_i, b_i, c_i = a_i * b_i)` isolated to `(sender, receiver, context)`
        // so only one-time-masked `x_i ^ a_i` and `y_i ^ b_i` ever cross the party channel, followed by the
        // 5-round BDOZ consistency check in `ParallelSeededDkgUnverifiedOutput::activate`.
        let mut raw = vec![0u8; count * 48];
        cshake256_framed_xof(
            b"QSAG.CLI.DKG.BEAVER.CORR.V1",
            &[
                &self.pad_secret,
                &context,
                &sender.to_be_bytes(),
                &receiver.to_be_bytes(),
                &(count as u64).to_be_bytes(),
            ],
            &mut raw,
        );

        let mut my_mask = ZeroizeU128s(Vec::with_capacity(count));
        let mut my_pad = ZeroizeU128s(Vec::with_capacity(count));
        for chunk in raw.chunks_exact(48) {
            let mut a_bytes = [0u8; 16];
            let mut b_bytes = [0u8; 16];
            let mut r_bytes = [0u8; 16];
            a_bytes.copy_from_slice(&chunk[..16]);
            b_bytes.copy_from_slice(&chunk[16..32]);
            r_bytes.copy_from_slice(&chunk[32..48]);
            let a = u128::from_le_bytes(a_bytes);
            let b = u128::from_le_bytes(b_bytes);
            let r = u128::from_le_bytes(r_bytes);
            if self.party_id == sender {
                my_mask.0.push(a);
                my_pad.0.push(r);
            } else {
                my_mask.0.push(b);
                my_pad.0.push(gf2_128_mul(a, b) ^ r);
            }
        }
        ct_zeroize_bytes(&mut raw);

        let peer = if self.party_id == sender {
            receiver
        } else {
            sender
        };
        let masked_local: Vec<u128> = operand
            .iter()
            .zip(my_mask.0.iter())
            .map(|(&x, &m)| x ^ m)
            .collect();

        let masked_remote = if self.party_id < peer {
            self.send_packet(peer, context, masked_local)?;
            self.recv_packet(peer, context, count)?
        } else {
            let inc = self.recv_packet(peer, context, count)?;
            self.send_packet(peer, context, masked_local)?;
            inc
        };

        let mut out = Vec::with_capacity(count);
        for i in 0..count {
            let factor = if self.party_id == sender {
                operand[i]
            } else {
                my_mask.0[i]
            };
            out.push(my_pad.0[i] ^ gf2_128_mul(factor, masked_remote.0[i]));
        }
        Ok(out)
    }
}

/// Dealerless `ParallelSeededFts` threshold ceremony + distributed `ParallelSeededSignSession` driver.
pub struct DealerlessThresholdFtsSetup {
    pub pk: ParallelSeededPublicKey,
    pub public_tree_layers: ParallelSeededMerkleLayers,
    shares: Vec<ParallelSeededPartyShare>,
    roster: Vec<u16>,
}

impl DealerlessThresholdFtsSetup {
    /// Compute the deterministic authenticated power-tuple budget required for `params`:
    /// `2^h` leaf preparations plus `2^h` epoch signatures (`<= 1_048_576` for `tree_height <= 4`).
    pub fn required_power_count(params: &ParallelSeededParams) -> Result<usize, ParallelSeededError> {
        params.validate()?;
        if params.tree_height > 4 {
            return Err(ParallelSeededError::InvalidThresholdParameters);
        }
        let leaves = 1usize << params.tree_height;
        let per_leaf = 2 * 48 * params.num_chains * params.winternitz_w;
        let per_sign = 2 * 48 * (1 + params.num_chains + params.target_sum);
        let total = leaves
            .checked_mul(per_leaf.saturating_add(per_sign))
            .ok_or(ParallelSeededError::InvalidThresholdParameters)?;
        if total == 0 || total > 1_048_576 {
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
        if !(2..=16).contains(&parties) {
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
        let beaver_corr_secret =
            cshake256_framed_32(b"QSAG.CLI.FTS.DKG.BEAVER_CORR.V1", &[&ceremony_seed]);

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

        let mut tx_grid: Vec<Vec<Option<Sender<MaskedProductPacket>>>> =
            (0..parties).map(|_| (0..parties).map(|_| None).collect()).collect();
        let mut rx_grid: Vec<Vec<Option<Receiver<MaskedProductPacket>>>> =
            (0..parties).map(|_| (0..parties).map(|_| None).collect()).collect();
        for s in 0..parties {
            for r in 0..parties {
                if s == r {
                    continue;
                }
                let (tx, rx) = mpsc::channel();
                tx_grid[s][r] = Some(tx);
                rx_grid[r][s] = Some(rx);
            }
        }

        let backends: Vec<PairwiseBeaverProductChannel> = tx_grid
            .into_iter()
            .zip(rx_grid)
            .enumerate()
            .map(|(id, (tx, rx))| PairwiseBeaverProductChannel {
                party_id: id as u16,
                pad_secret: beaver_corr_secret,
                tx,
                rx,
                seen: BTreeSet::new(),
            })
            .collect();

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
        let mut masked = Vec::with_capacity(parties);
        for p in &mut pending {
            masked.push(p.masked_shares(&coins)?);
        }
        let mut tag_commits = Vec::with_capacity(parties);
        for p in &mut pending {
            tag_commits.push(p.tag_commitment(&masked)?);
        }
        let mut tags = Vec::with_capacity(parties);
        for p in &mut pending {
            tags.push(p.open_tags(&tag_commits)?);
        }
        let mut outputs: Vec<ParallelSeededDkgOutput> = Vec::with_capacity(parties);
        for p in pending {
            outputs.push(p.activate(&tags)?);
        }

        let pk_seed_bytes = outputs[0].pk_seed_bytes;
        let mut shares: Vec<ParallelSeededPartyShare> =
            outputs.into_iter().map(|o| o.share).collect();

        let (pk, public_tree_layers) = if let Some((cached_pk, cached_layers)) = cached_tree {
            if cached_pk.pk_seed_bytes != pk_seed_bytes || cached_layers.is_empty() {
                return Err(ParallelSeededError::InvalidAuthenticationPath);
            }
            let (rebuilt_pk, rebuilt_layers) = assemble_parallel_seeded_public_key(
                params,
                pk_seed_bytes,
                &cached_layers[0],
            )?;
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
                for sh in &mut shares {
                    sessions.push(ParallelSeededSignSession::begin_leaf_preparation(
                        sh, epoch, leaf_sid, &roster,
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
            shares,
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

        let mut sessions = Vec::with_capacity(self.shares.len());
        for sh in &mut self.shares {
            sessions.push(ParallelSeededSignSession::begin(sh, &req, persistence)?);
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
