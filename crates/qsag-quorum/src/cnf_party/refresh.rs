//! Each dealer additively shares two zero masks and an independent zero-sum blind.
//! All holders bind their replica views before the joint field challenge. Opening
//! a blinded linear combination checks the aggregate mask without disclosing it.
#![forbid(unsafe_code)]
use super::*;

const DEAL: u32 = 0x0413_0000;
const COMMIT: u32 = 0x0418_0000;
const PREPARED: u32 = 0x0415_0000;
const CHECK: u32 = 0x0414_0000;
const ROW: usize = 112; // seed mask, PRF mask, field blind, fresh PRSS contribution

impl<T: WireTransport, J: PoisonJournal> IsolatedCnfParty<T, J> {
    /// Return refreshed custody bytes for a subsequent session. All dealers contribute
    /// private entropy, and only the holders of a slot receive its components.
    pub fn refresh_share(
        &mut self,
        share: &CnfRssKeyShare256,
    ) -> Result<CnfRssKeyShare256, CnfPartyError> {
        self.guarded(|p| p.refresh_inner(share))
    }

    /// A refresh may be installed once every custodian has durably prepared its bytes.
    pub fn confirm_refresh_prepared(&mut self) -> Result<(), CnfPartyError> {
        if self.is_poisoned() {
            return Err(CnfPartyError::Poisoned);
        }
        for peer in self.topo.peers() {
            self.transport.send_frame(peer, PREPARED, &self.session)?;
        }
        for peer in self.topo.peers() {
            let msg = self.recv(peer, PREPARED, 32)?;
            if !ct_eq_bytes(&msg, &self.session) {
                return Err(CnfPartyError::ConsistencyMismatch { peer });
            }
        }
        Ok(())
    }

    fn refresh_inner(
        &mut self,
        share: &CnfRssKeyShare256,
    ) -> Result<CnfRssKeyShare256, CnfPartyError> {
        if share.party_id != self.topo.me
            || share.slot_indices() != self.topo.held
            || share.key_len != self.key_len
            || share.scheme_identity() != self.scheme_identity
            || share.slh_profile_digest() != self.slh_profile_digest
            || share.pk_seed != self.pk_seed
            || share.config().parties() != self.topo.n
            || share.config().total_slots() != self.topo.subsets.len()
        {
            return Err(CnfPartyError::InvalidParameters);
        }
        self.barrier_inner()?;
        let slots = self.topo.subsets.len();
        let mut deal = SecretBuffer(vec![[0u8; ROW]; slots]);
        let (last, others) = deal
            .split_last_mut()
            .ok_or(CnfPartyError::InvalidParameters)?;
        for row in others {
            self.rng.fill(row);
            for (sum, byte) in last[..80].iter_mut().zip(row) {
                *sum ^= *byte;
            }
        }
        self.rng.fill(&mut last[80..]);
        #[cfg(test)]
        if self.fault == Some(Fault::NonzeroRefreshMask) {
            deal[0][0] ^= 1;
        }
        let commitment = |session: &[u8; 32], from: usize, to: usize, opening: &[u8]| {
            h32(
                b"QSAG.QUORUM.REFRESH.COMMIT/v1",
                &[session, &[from as u8, to as u8], opening],
            )
        };
        let mut outgoing = Vec::with_capacity(self.topo.n - 1);
        for peer in self.topo.peers() {
            let mut payload = SecretBuffer(Vec::with_capacity(self.topo.held.len() * ROW));
            for (s, row) in deal.iter().enumerate() {
                if self.topo.holds(peer, s) {
                    payload.extend_from_slice(row);
                }
            }
            let digest = commitment(&self.session, self.topo.me, peer, &payload);
            self.transport.send_frame(peer, COMMIT, &digest)?;
            outgoing.push(payload);
        }
        let mut commitments = vec![[0u8; 32]; self.topo.n];
        for peer in self.topo.peers() {
            commitments[peer].copy_from_slice(&self.recv(peer, COMMIT, 32)?);
        }
        for (peer, payload) in self.topo.peers().zip(outgoing) {
            self.transport.send_frame(peer, DEAL, &payload)?;
        }
        let mut rows = SecretBuffer(vec![[0u8; ROW]; self.topo.held.len()]);
        for (l, &s) in self.topo.held.iter().enumerate() {
            rows[l] = deal[s];
        }
        drop(deal);
        for peer in self.topo.peers() {
            let raw = SecretBuffer(self.recv(peer, DEAL, rows.len() * ROW)?);
            if !ct_eq_bytes32(
                &commitments[peer],
                &commitment(&self.session, peer, self.topo.me, &raw),
            ) {
                return Err(CnfPartyError::OpeningRejected { party: peer });
            }
            for (dst, src) in rows.iter_mut().flatten().zip(raw.iter()) {
                *dst ^= *src;
            }
        }
        for (l, row) in rows.iter().enumerate() {
            let (seed, prf, prss) = share
                .held_slot(self.topo.held[l])
                .ok_or(CnfPartyError::InvalidParameters)?;
            if !(ct_eq_bytes32(seed, &self.key_shares[l]) & ct_eq_bytes32(prf, &self.prf_shares[l]))
            {
                return Err(CnfPartyError::InvalidParameters);
            }
            absorb_framed(&mut self.transcripts[l], prss);
            absorb_framed(&mut self.transcripts[l], row);
        }
        self.exchange_consistency(2)?;
        let coin = self.joint_coin()?;
        self.exchange_consistency(3)?;
        let challenge = u128::from_le_bytes(
            coin.first_chunk::<16>()
                .copied()
                .ok_or(CnfPartyError::InvalidParameters)?,
        );
        let checks: Vec<_> = rows
            .iter()
            .map(|row| {
                // Evaluate a degree-four polynomial. Its constant coefficient is
                // the one-time blind. A nonzero sum passes with probability <= 4/2^128.
                let result = row[..80].as_chunks::<16>().0.iter().fold(0, |acc, block| {
                    gf_mul(acc, challenge) ^ u128::from_le_bytes(*block)
                });
                result.to_le_bytes().to_vec()
            })
            .collect();
        if !ct_eq_bytes(&self.open_shares(CHECK, &checks)?, &[0; 16]) {
            return Err(CnfPartyError::MultiplicationCheckFailed);
        }

        // Replace only the three component arrays in the canonical QSCNFK01
        // encoding, preserving even custom SLH profile locks and pairwise PRFs.
        let mut raw = share.to_secret_bytes();
        let count = rows.len();
        let offset = 80 + 2 * count;
        for (l, row) in rows.iter().enumerate() {
            for i in 0..self.key_len {
                raw[offset + 32 * l + i] ^= row[i];
                raw[offset + 32 * (count + l) + i] ^= row[32 + i];
            }
            raw[offset + 32 * (2 * count + l)..offset + 32 * (2 * count + l + 1)]
                .copy_from_slice(&row[80..]);
        }
        CnfRssKeyShare256::from_secret_bytes(&raw).map_err(|_| CnfPartyError::InvalidParameters)
    }
}
