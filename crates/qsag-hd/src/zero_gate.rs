//! Committed zero-test release gate backed by `qsag_verified::HdCommittedZeroTest`.
//!
//! One verified gate holds each lane's local residual. The "peer" of a gate is the
//! aggregate of every other roster member: its commitment is the digest of their
//! frozen commitment transcript and its residual is the modular sum of their
//! openings. The verified state machine therefore decides the three properties the
//! protocol needs: no local residual leaves before the peer transcript is frozen,
//! the opened transcript is the frozen one, and every lane sums to zero.
use crate::HdError;
use qsag_asm::wipe::wipe;
use alloc::vec::Vec;
use qsag_accel::keccak::cshake256_framed_32;
use qsag_verified::HdCommittedZeroTest;

pub(crate) struct CommittedZeroGates {
    session: [u8; 32],
    modulus: u32,
    gates: Vec<HdCommittedZeroTest>,
    opened: Option<Vec<u32>>,
}

/// Digest of the other members' commitments, in the order the caller froze them.
pub(crate) fn peer_transcript(
    session: &[u8; 32],
    own_party: u16,
    commitments: impl Iterator<Item = (u16, [u8; 32])>,
) -> [u8; 32] {
    let mut bytes = Vec::new();
    for (party, digest) in commitments.filter(|(party, _)| *party != own_party) {
        bytes.extend_from_slice(&party.to_be_bytes());
        bytes.extend_from_slice(&digest);
    }
    cshake256_framed_32(
        b"QSAG.HD.ZERO_TEST.PEER_TRANSCRIPT.V1",
        &[session, &own_party.to_be_bytes(), &bytes],
    )
}

impl CommittedZeroGates {
    /// Moves the residuals into verified gates and wipes the caller's copy.
    pub(crate) fn hold(session: [u8; 32], modulus: u32, residuals: &mut [u32]) -> Self {
        let gates = residuals
            .iter()
            .map(|&residual| {
                HdCommittedZeroTest::new_awaiting_peer_commit(session, residual, modulus)
            })
            .collect();
        wipe(residuals);
        Self {
            session,
            modulus,
            gates,
            opened: None,
        }
    }

    fn step<T>(
        &mut self,
        mut transition: impl FnMut(
            HdCommittedZeroTest,
        ) -> (
            HdCommittedZeroTest,
            Result<T, qsag_verified::CredHdGuardError>,
        ),
    ) -> Result<Vec<T>, HdError> {
        let mut outputs = Vec::with_capacity(self.gates.len());
        let mut failed = self.gates.is_empty();
        for gate in core::mem::take(&mut self.gates) {
            let (next, result) = transition(gate);
            match result {
                Ok(output) => outputs.push(output),
                Err(_) => failed = true,
            }
            self.gates.push(next);
        }
        if failed {
            self.quarantine();
            return Err(HdError::MacCheckFailed);
        }
        Ok(outputs)
    }

    /// Drives every gate into the verified quarantine state, which zeroes its residual.
    fn quarantine(&mut self) {
        let mismatched = self.session.map(|byte| !byte);
        for gate in core::mem::take(&mut self.gates) {
            let (next, _) = gate.open_local_residual(mismatched);
            self.gates.push(next);
        }
        if let Some(opened) = &mut self.opened {
            wipe(opened);
        }
        self.opened = None;
    }

    pub(crate) fn freeze(&mut self, peers: [u8; 32]) -> Result<(), HdError> {
        let session = self.session;
        self.step(|gate| gate.freeze_peer_commitment(session, peers))
            .map(|_| ())
    }

    /// The local residuals. Refused until the peer transcript is frozen.
    pub(crate) fn open(&mut self) -> Result<&[u32], HdError> {
        if self.opened.is_none() {
            let session = self.session;
            self.opened = Some(self.step(|gate| gate.open_local_residual(session))?);
        }
        self.opened.as_deref().ok_or(HdError::MacCheckFailed)
    }

    /// Accepts only the frozen peer transcript with every lane summing to zero.
    pub(crate) fn verify(&mut self, peers: [u8; 32], peer_sums: &[u32]) -> Result<(), HdError> {
        if peer_sums.len() != self.gates.len() || peer_sums.iter().any(|&sum| sum >= self.modulus) {
            self.quarantine();
            return Err(HdError::MacCheckFailed);
        }
        let session = self.session;
        let mut lane = 0;
        self.step(|gate| {
            let sum = peer_sums[lane];
            lane += 1;
            gate.verify_peer_opening(session, peers, sum)
        })
        .map(|_| ())
    }
}

impl Drop for CommittedZeroGates {
    fn drop(&mut self) {
        self.quarantine();
        core::hint::black_box(&mut self.gates);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const Q: u32 = crate::MODULE_Q;

    #[test]
    fn residual_is_withheld_until_the_peer_transcript_is_frozen() {
        let mut gates = CommittedZeroGates::hold([1; 32], Q, &mut [5, 6]);
        assert_eq!(gates.open().err(), Some(HdError::MacCheckFailed));
        // The refusal is terminal and the residuals are gone.
        assert_eq!(gates.freeze([2; 32]), Err(HdError::MacCheckFailed));
        assert_eq!(gates.open().err(), Some(HdError::MacCheckFailed));
    }

    #[test]
    fn accepts_exactly_the_frozen_transcript_and_zero_sums() {
        let run = |peers: [u8; 32], sums: [u32; 2]| {
            let mut residuals = [5, 0];
            let mut gates = CommittedZeroGates::hold([1; 32], Q, &mut residuals);
            assert_eq!(residuals, [0, 0]);
            gates.freeze([2; 32]).unwrap();
            assert_eq!(gates.open().unwrap(), [5, 0]);
            assert_eq!(gates.open().unwrap(), [5, 0]);
            gates.verify(peers, &sums)
        };
        assert_eq!(run([2; 32], [Q - 5, 0]), Ok(()));
        assert_eq!(run([3; 32], [Q - 5, 0]), Err(HdError::MacCheckFailed));
        assert_eq!(run([2; 32], [Q - 4, 0]), Err(HdError::MacCheckFailed));
        assert_eq!(run([2; 32], [Q - 5, 1]), Err(HdError::MacCheckFailed));
        assert_eq!(run([2; 32], [Q - 5, Q]), Err(HdError::MacCheckFailed));
    }

    #[test]
    fn verification_requires_the_local_opening_and_is_single_use() {
        let mut gates = CommittedZeroGates::hold([1; 32], Q, &mut [0]);
        gates.freeze([2; 32]).unwrap();
        assert_eq!(gates.verify([2; 32], &[0]), Err(HdError::MacCheckFailed));
        let mut gates = CommittedZeroGates::hold([1; 32], Q, &mut [0]);
        gates.freeze([2; 32]).unwrap();
        gates.open().unwrap();
        assert_eq!(gates.verify([2; 32], &[0]), Ok(()));
        assert_eq!(gates.verify([2; 32], &[0]), Err(HdError::MacCheckFailed));
    }

    #[test]
    fn peer_transcript_excludes_self_and_binds_order_and_owner() {
        let all = [(1u16, [1u8; 32]), (2, [2; 32]), (3, [3; 32])];
        let base = peer_transcript(&[9; 32], 2, all.into_iter());
        let without_self = [(1u16, [1u8; 32]), (3, [3; 32])];
        assert_eq!(base, peer_transcript(&[9; 32], 2, without_self.into_iter()));
        let swapped = [(3u16, [3u8; 32]), (1, [1; 32])];
        assert_ne!(base, peer_transcript(&[9; 32], 2, swapped.into_iter()));
        assert_ne!(base, peer_transcript(&[9; 32], 1, all.into_iter()));
        assert_ne!(base, peer_transcript(&[8; 32], 2, all.into_iter()));
    }
}
