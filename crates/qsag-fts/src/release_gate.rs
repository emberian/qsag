//! Custody of opened wire candidates between the value opening and the MAC check.
//!
//! Signature chain endpoints of the 68-chain `w = 5`, `S = 136` shape are held
//! inside `qsag_verified::FtsDeferredMacSession`: the verified state machine
//! decides whether the MAC residual is zero, whether all 48 rounds ran and whether
//! the codeword is a valid constant-sum word, and only then yields the endpoints.
//! Every other opening (the randomizer, public-leaf endpoints, other parameter
//! shapes) has no codeword at release time and uses the same hold, verify, release
//! order with a consuming verified opening guard.
//!
//! [`OpenedCandidates`] owns the candidates from the moment they are reconstructed
//! and wipes every encoding of them when it is dropped, so an error before the gate
//! exists leaves nothing behind. [`QuorumGate`] takes that buffer by move and holds
//! one [`OutputGate`] per party; nothing is released until every party's residual
//! has been accepted.
use alloc::vec::Vec;
use alloc::boxed::Box;
use qsag_verified::{ConsumingOpeningGuard2Lane, OpeningReleasePermit};
use qsag_accel::ct::{ct_zeroize_bytes, ct_zeroize_u128s};
use qsag_verified::fts_spn_guard::{
    FtsDeferredMacSession, WOTS_CS_BASE_W, WOTS_CS_CHAINS, WOTS_CS_TARGET_SUM,
};

use crate::parallel_mpc::{ParallelSeededError, ParallelSeededParams};

pub(crate) fn wipe_pairs(pairs: &mut [(u128, u128)]) {
    for (lo, hi) in pairs {
        ct_zeroize_u128s(core::slice::from_mut(lo));
        ct_zeroize_u128s(core::slice::from_mut(hi));
    }
}

/// Counts candidate buffers on the current thread, so a test can assert that a
/// failed opening wiped every buffer it created and released none.
#[cfg(test)]
pub(crate) mod probe {
    extern crate std;
    use core::cell::Cell;

    std::thread_local! {
        static CREATED: Cell<usize> = const { Cell::new(0) };
        static WIPED: Cell<usize> = const { Cell::new(0) };
        static RELEASED: Cell<usize> = const { Cell::new(0) };
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub(crate) struct Counts {
        pub(crate) created: usize,
        pub(crate) wiped: usize,
        pub(crate) released: usize,
    }

    pub(crate) fn reset() {
        CREATED.with(|c| c.set(0));
        WIPED.with(|c| c.set(0));
        RELEASED.with(|c| c.set(0));
    }
    pub(crate) fn counts() -> Counts {
        Counts {
            created: CREATED.with(Cell::get),
            wiped: WIPED.with(Cell::get),
            released: RELEASED.with(Cell::get),
        }
    }
    pub(super) fn created() {
        CREATED.with(|c| c.set(c.get() + 1));
    }
    pub(super) fn wiped() {
        WIPED.with(|c| c.set(c.get() + 1));
    }
    pub(super) fn released() {
        RELEASED.with(|c| c.set(c.get() + 1));
    }
}

/// Reconstructed wire candidates that no MAC check has accepted yet, in the three
/// encodings the check needs: the values, their byte string for the transcript
/// digest, and the `(v, v)` pairs for the two-lane weighted fold.
pub(crate) struct OpenedCandidates {
    values: Vec<u128>,
    digest_input: Vec<u8>,
    pairs: Vec<(u128, u128)>,
}

impl OpenedCandidates {
    /// The capacity is exact, so pushing `wires` candidates never reallocates and
    /// leaves no unwiped copy behind.
    pub(crate) fn with_capacity(wires: usize) -> Self {
        #[cfg(test)]
        probe::created();
        Self {
            values: Vec::with_capacity(wires),
            digest_input: Vec::with_capacity(wires.saturating_mul(16)),
            pairs: Vec::with_capacity(wires),
        }
    }

    pub(crate) fn push(&mut self, value: u128) {
        self.values.push(value);
        self.digest_input.extend_from_slice(&value.to_le_bytes());
        self.pairs.push((value, value));
    }

    pub(crate) fn digest_input(&self) -> &[u8] {
        &self.digest_input
    }

    pub(crate) fn pairs(&self) -> &[(u128, u128)] {
        &self.pairs
    }

    /// Wipes the digest and fold encodings once both have been consumed.
    pub(crate) fn shed_encodings(&mut self) {
        ct_zeroize_bytes(&mut self.digest_input);
        self.digest_input.clear();
        wipe_pairs(&mut self.pairs);
        self.pairs.clear();
    }

    fn wipe(&mut self) {
        ct_zeroize_u128s(&mut self.values);
        ct_zeroize_bytes(&mut self.digest_input);
        wipe_pairs(&mut self.pairs);
    }
}

impl Drop for OpenedCandidates {
    fn drop(&mut self) {
        self.wipe();
        #[cfg(test)]
        {
            assert!(self.values.iter().all(|&v| v == 0));
            assert!(self.digest_input.iter().all(|&b| b == 0));
            assert!(self.pairs.iter().all(|&p| p == (0, 0)));
            probe::wiped();
        }
    }
}

enum Held {
    Verified(Vec<FtsDeferredMacSession>),
    Bound {
        values: Vec<u128>,
        binding: [u8; 32],
        guard: Option<Box<ConsumingOpeningGuard2Lane>>,
        permit: Option<OpeningReleasePermit>,
    },
}

pub(crate) struct OutputGate {
    session: [u8; 32],
    held: Held,
}

fn verified_shape(params: &ParallelSeededParams) -> bool {
    params.winternitz_w == usize::from(WOTS_CS_BASE_W)
        && params.num_chains == WOTS_CS_CHAINS
        && params.target_sum as u64 == WOTS_CS_TARGET_SUM
}

fn candidate_binding(values: &[u128]) -> [u8; 32] {
    let mut sponge = qsag_accel::keccak::Shake256::new();
    sponge.absorb(b"QSAG.FTS.CANDIDATE_BINDING.V1");
    sponge.absorb(&(values.len() as u64).to_be_bytes());
    for value in values { sponge.absorb(&value.to_le_bytes()); }
    sponge.finalize(0x1f);
    let mut digest = [0; 32];
    sponge.squeeze(&mut digest);
    digest
}

impl OutputGate {
    /// Takes ownership of the candidates. `spn_rounds` is the number of rounds the
    /// final chain step actually ran.
    pub(crate) fn hold(
        params: &ParallelSeededParams,
        signature_chains: bool,
        session: [u8; 32],
        spn_rounds: usize,
        mut values: Vec<u128>,
    ) -> Self {
        let held = if signature_chains
            && verified_shape(params)
            && values.len() == 2 * WOTS_CS_CHAINS
        {
            let rounds = u8::try_from(spn_rounds).unwrap_or(0);
            let sessions = values
                .as_chunks::<2>()
                .0
                .iter()
                .map(|pair| {
                    FtsDeferredMacSession::new_spn48_evaluated(session, rounds, pair[0], pair[1])
                })
                .collect();
            ct_zeroize_u128s(&mut values);
            Held::Verified(sessions)
        } else {
            let binding = candidate_binding(&values);
            Held::Bound {
                guard: Some(Box::new(ConsumingOpeningGuard2Lane::new(session, 0, binding,
                    u64::from(spn_rounds == 48 && !values.is_empty())))),
                values, binding, permit: None,
            }
        };
        Self { session, held }
    }

    fn wipe(&mut self) {
        match &mut self.held {
            Held::Verified(sessions) => {
                // A mismatched request drives each session into verified quarantine,
                // which zeroes its candidate wires.
                let mismatched = self.session.map(|byte| !byte);
                for session in core::mem::take(sessions) {
                    let (next, _) = session.verify_intermediate_mac(mismatched, 1, 1);
                    sessions.push(next);
                }
                core::hint::black_box(sessions);
            }
            Held::Bound { values, guard, permit, .. } => {
                ct_zeroize_u128s(values);
                values.clear();
                *guard = None;
                *permit = None;
            }
        }
    }

    /// Single use. A nonzero residual destroys the candidates.
    pub(crate) fn verify_mac(&mut self, residual: [u128; 2]) -> Result<(), ParallelSeededError> {
        let request = self.session;
        let accepted = match &mut self.held {
            Held::Verified(sessions) => {
                let mut accepted = !sessions.is_empty();
                for session in core::mem::take(sessions) {
                    let (next, result) =
                        session.verify_intermediate_mac(request, residual[0], residual[1]);
                    accepted &= result.is_ok();
                    sessions.push(next);
                }
                accepted
            }
            Held::Bound { values, binding, guard, permit } => {
                if let Some(gate) = guard.take() {
                    let gate = (*gate).absorb_opening(binding, &candidate_binding(values), residual);
                    let (_, granted) = gate.verify_once(&request, 0, binding);
                    *permit = granted;
                    permit.is_some()
                } else { false }
            }
        };
        if !accepted {
            self.wipe();
            return Err(ParallelSeededError::BdozMacCheckFailed);
        }
        Ok(())
    }

    /// Yields the candidates once, after an accepted MAC check. `digits` is the
    /// codeword the signature endpoints answer.
    pub(crate) fn release(&mut self, digits: &[u8]) -> Result<Vec<u128>, ParallelSeededError> {
        let request = self.session;
        let released = match &mut self.held {
            Held::Verified(sessions) => {
                let mut out = Vec::with_capacity(2 * sessions.len());
                let mut accepted = !sessions.is_empty();
                for session in core::mem::take(sessions) {
                    let (next, result) = session.release_spn_output(request, digits);
                    match result {
                        Ok((lo, hi)) => out.extend_from_slice(&[lo, hi]),
                        Err(_) => accepted = false,
                    }
                    sessions.push(next);
                }
                if accepted {
                    Some(out)
                } else {
                    ct_zeroize_u128s(&mut out);
                    None
                }
            }
            Held::Bound { values, binding, permit, .. } => {
                match permit.take() {
                    Some(grant) if grant.session_id() == request && grant.round_id() == 0
                        && grant.openings() == 1 && candidate_binding(values) == *binding =>
                        Some(core::mem::take(values)),
                    _ => None,
                }
            }
        };
        match released {
            Some(values) => Ok(values),
            None => {
                self.wipe();
                Err(ParallelSeededError::BdozMacCheckFailed)
            }
        }
    }
}

#[cfg(test)]
impl OutputGate {
    pub(crate) fn is_verified(&self) -> bool {
        matches!(self.held, Held::Verified(_))
    }
}

impl Drop for OutputGate {
    fn drop(&mut self) {
        self.wipe();
    }
}

#[cfg(test)]
impl OutputGate {
    fn is_destroyed(&self) -> bool {
        match &self.held {
            Held::Verified(sessions) => sessions.iter().all(|s| s.is_quarantined()),
            Held::Bound { values, permit, .. } => values.is_empty() && permit.is_none(),
        }
    }
}

/// One [`OutputGate`] per party over the same candidates. A refusal by any party
/// destroys every party's copy, and no copy is released before every party has
/// accepted its own residual.
pub(crate) struct QuorumGate {
    gates: Vec<OutputGate>,
}

impl QuorumGate {
    /// Consumes the candidates: each party's gate receives its own copy and the
    /// source buffer is wiped before this returns.
    pub(crate) fn hold(
        params: &ParallelSeededParams,
        signature_chains: bool,
        session: [u8; 32],
        spn_rounds: usize,
        parties: usize,
        candidates: OpenedCandidates,
    ) -> Self {
        let gates = (0..parties)
            .map(|_| {
                OutputGate::hold(
                    params,
                    signature_chains,
                    session,
                    spn_rounds,
                    candidates.values.clone(),
                )
            })
            .collect();
        drop(candidates);
        Self { gates }
    }

    fn wipe(&mut self) {
        for gate in &mut self.gates {
            gate.wipe();
        }
    }

    /// `residuals[i]` is the residual party `i` computed from the frozen transcript.
    /// Every party's check runs; one refusal destroys all copies.
    pub(crate) fn verify_all(
        &mut self,
        residuals: &[[u128; 2]],
    ) -> Result<(), ParallelSeededError> {
        let mut accepted = !self.gates.is_empty() && residuals.len() == self.gates.len();
        if accepted {
            for (gate, residual) in self.gates.iter_mut().zip(residuals) {
                accepted &= gate.verify_mac(*residual).is_ok();
            }
        }
        if !accepted {
            self.wipe();
            return Err(ParallelSeededError::BdozMacCheckFailed);
        }
        Ok(())
    }

    /// Yields the candidates once, after [`Self::verify_all`] accepted, and only if
    /// every party's gate releases the same values.
    pub(crate) fn release(&mut self, digits: &[u8]) -> Result<Vec<u128>, ParallelSeededError> {
        let mut accepted = !self.gates.is_empty();
        let mut agreed: Option<Vec<u128>> = None;
        for gate in &mut self.gates {
            match gate.release(digits) {
                Ok(mut values) => match &agreed {
                    None => agreed = Some(values),
                    Some(first) => {
                        accepted &= *first == values;
                        ct_zeroize_u128s(&mut values);
                    }
                },
                Err(_) => accepted = false,
            }
        }
        match agreed {
            Some(values) if accepted => {
                #[cfg(test)]
                probe::released();
                Ok(values)
            }
            other => {
                if let Some(mut values) = other {
                    ct_zeroize_u128s(&mut values);
                }
                self.wipe();
                Err(ParallelSeededError::BdozMacCheckFailed)
            }
        }
    }
}

#[cfg(test)]
impl QuorumGate {
    pub(crate) fn all_destroyed(&self) -> bool {
        self.gates.iter().all(OutputGate::is_destroyed)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;

    const CUSTODY: ParallelSeededParams = ParallelSeededParams::CUSTODY_H10_W5;

    fn codeword() -> Vec<u8> {
        vec![2; WOTS_CS_CHAINS]
    }
    fn candidates() -> Vec<u128> {
        (1..=2 * WOTS_CS_CHAINS as u128).collect()
    }
    fn custody_gate(rounds: usize) -> OutputGate {
        let gate = OutputGate::hold(&CUSTODY, true, [7; 32], rounds, candidates());
        assert!(matches!(gate.held, Held::Verified(_)));
        gate
    }

    #[test]
    fn custody_endpoints_release_only_after_a_zero_residual_and_a_valid_codeword() {
        let mut gate = custody_gate(48);
        gate.verify_mac([0, 0]).unwrap();
        assert_eq!(gate.release(&codeword()).unwrap(), candidates());
        // Released once.
        assert!(gate.release(&codeword()).is_err());
    }

    #[test]
    fn custody_endpoints_are_destroyed_by_every_refusal() {
        // No MAC check.
        assert!(custody_gate(48).release(&codeword()).is_err());
        // Either residual lane nonzero.
        for residual in [[1, 0], [0, 1]] {
            let mut gate = custody_gate(48);
            assert_eq!(
                gate.verify_mac(residual),
                Err(ParallelSeededError::BdozMacCheckFailed)
            );
            assert!(gate.verify_mac([0, 0]).is_err());
            assert!(gate.release(&codeword()).is_err());
        }
        // A chain step that did not run all 48 rounds.
        for rounds in [0, 47, 49, 304] {
            assert!(custody_gate(rounds).verify_mac([0, 0]).is_err());
        }
        // MAC check replayed.
        let mut gate = custody_gate(48);
        gate.verify_mac([0, 0]).unwrap();
        assert!(gate.verify_mac([0, 0]).is_err());
        assert!(gate.release(&codeword()).is_err());
        // Codewords off the constant-sum layer, out of range or of the wrong length.
        let mut high = codeword();
        high[0] = 3;
        let mut wide = codeword();
        wide[0] = 5;
        wide[1] = 0;
        wide[2] = 1;
        for digits in [high, wide, vec![2; WOTS_CS_CHAINS - 1], Vec::new()] {
            let mut gate = custody_gate(48);
            gate.verify_mac([0, 0]).unwrap();
            assert!(gate.release(&digits).is_err());
            assert!(gate.release(&codeword()).is_err());
        }
    }

    #[test]
    fn other_openings_keep_the_same_order() {
        for (params, chains, values) in [
            (CUSTODY, false, vec![3u128, 4]),
            (ParallelSeededParams::FAST_H4_W5, true, vec![3u128; 8]),
        ] {
            let hold = || {
                let gate = OutputGate::hold(&params, chains, [7; 32], 48, values.clone());
                assert!(matches!(gate.held, Held::Bound { .. }));
                gate
            };
            assert!(hold().release(&[]).is_err());
            let mut gate = hold();
            assert!(gate.verify_mac([0, 1]).is_err());
            assert!(gate.verify_mac([0, 0]).is_err());
            assert!(gate.release(&[]).is_err());
            let mut gate = hold();
            gate.verify_mac([0, 0]).unwrap();
            assert!(gate.verify_mac([0, 0]).is_err());
            let mut gate = hold();
            gate.verify_mac([0, 0]).unwrap();
            assert_eq!(gate.release(&[]).unwrap(), values);
            assert!(gate.release(&[]).is_err());
        }
    }

    fn opened(values: &[u128]) -> OpenedCandidates {
        let mut candidates = OpenedCandidates::with_capacity(values.len());
        for &value in values {
            candidates.push(value);
        }
        candidates
    }

    /// The custody shape (verified sessions) and a shape held locally.
    fn quorum_shapes() -> [(ParallelSeededParams, bool, Vec<u128>, Vec<u8>); 2] {
        [
            (CUSTODY, true, candidates(), codeword()),
            (CUSTODY, false, vec![3u128, 4], Vec::new()),
        ]
    }

    #[test]
    fn opened_candidates_wipe_every_encoding() {
        let mut held = opened(&[u128::MAX, 7, 1 << 100]);
        assert_eq!(held.values, [u128::MAX, 7, 1 << 100]);
        assert_eq!(held.digest_input().len(), 48);
        assert_eq!(held.pairs()[1], (7, 7));

        held.shed_encodings();
        assert!(held.digest_input().is_empty() && held.pairs().is_empty());
        assert_eq!(held.values, [u128::MAX, 7, 1 << 100]);

        let mut held = opened(&[u128::MAX, 7, 1 << 100]);
        held.wipe();
        assert_eq!(held.values, [0; 3]);
        assert_eq!(held.digest_input(), [0u8; 48]);
        assert_eq!(held.pairs(), [(0, 0); 3]);
    }

    #[test]
    fn dropping_unreleased_candidates_wipes_them() {
        probe::reset();
        drop(opened(&[5, 6]));
        // The gate consumes the buffer, so it is wiped before any check runs.
        let gate = QuorumGate::hold(&CUSTODY, false, [7; 32], 48, 3, opened(&[5, 6]));
        assert_eq!(
            probe::counts(),
            probe::Counts {
                created: 2,
                wiped: 2,
                released: 0
            }
        );
        drop(gate);
        assert_eq!(probe::counts().released, 0);
    }

    #[test]
    fn quorum_releases_only_after_every_party_accepts() {
        for (params, chains, values, digits) in quorum_shapes() {
            probe::reset();
            let mut gate = QuorumGate::hold(&params, chains, [7; 32], 48, 3, opened(&values));
            assert_eq!(gate.gates.len(), 3);
            assert_eq!(gate.gates[0].is_verified(), chains);
            gate.verify_all(&[[0, 0]; 3]).unwrap();
            assert_eq!(gate.release(&digits).unwrap(), values);
            assert_eq!(probe::counts().released, 1);
            // Released once.
            assert!(gate.release(&digits).is_err());
            assert!(gate.all_destroyed());
        }
    }

    #[test]
    fn one_refusing_party_destroys_every_copy() {
        let refusals: [&[[u128; 2]]; 6] = [
            // The refusing party is first, in the middle, or last.
            &[[1, 0], [0, 0], [0, 0]],
            &[[0, 0], [0, 1], [0, 0]],
            &[[0, 0], [0, 0], [1, 1]],
            // A residual is missing or surplus.
            &[[0, 0], [0, 0]],
            &[[0, 0]; 4],
            &[],
        ];
        for (params, chains, values, digits) in quorum_shapes() {
            for residuals in refusals {
                probe::reset();
                let mut gate = QuorumGate::hold(&params, chains, [7; 32], 48, 3, opened(&values));
                assert_eq!(
                    gate.verify_all(residuals),
                    Err(ParallelSeededError::BdozMacCheckFailed)
                );
                assert!(gate.all_destroyed());
                // The parties whose own residual was zero release nothing either.
                assert!(gate.release(&digits).is_err());
                assert!(gate.verify_all(&[[0, 0]; 3]).is_err());
                assert!(gate.release(&digits).is_err());
                assert!(gate.all_destroyed());
                let counts = probe::counts();
                assert_eq!((counts.created, counts.wiped, counts.released), (1, 1, 0));
            }
        }
    }

    #[test]
    fn quorum_refuses_without_a_check_without_parties_and_on_a_bad_codeword() {
        for (params, chains, values, digits) in quorum_shapes() {
            probe::reset();
            // No MAC check.
            let mut gate = QuorumGate::hold(&params, chains, [7; 32], 48, 2, opened(&values));
            assert!(gate.release(&digits).is_err());
            assert!(gate.all_destroyed());
            // No party.
            let mut gate = QuorumGate::hold(&params, chains, [7; 32], 48, 0, opened(&values));
            assert!(gate.verify_all(&[]).is_err());
            assert!(gate.release(&digits).is_err());
            assert_eq!(probe::counts().released, 0);
        }
        // Every party accepted the MAC check, then the codeword is refused.
        probe::reset();
        let mut gate = QuorumGate::hold(&CUSTODY, true, [7; 32], 48, 2, opened(&candidates()));
        gate.verify_all(&[[0, 0]; 2]).unwrap();
        let mut high = codeword();
        high[0] = 3;
        assert_eq!(
            gate.release(&high),
            Err(ParallelSeededError::BdozMacCheckFailed)
        );
        assert!(gate.all_destroyed());
        assert!(gate.release(&codeword()).is_err());
        // A chain step that did not run all 48 rounds.
        let mut gate = QuorumGate::hold(&CUSTODY, true, [7; 32], 47, 2, opened(&candidates()));
        assert!(gate.verify_all(&[[0, 0]; 2]).is_err());
        assert!(gate.all_destroyed());
        assert_eq!(probe::counts().released, 0);
    }
}
