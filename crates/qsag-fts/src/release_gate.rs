//! Custody of opened wire candidates between the value opening and the MAC check.
//!
//! Signature chain endpoints of the 68-chain `w = 5`, `S = 136` shape are held
//! inside `qsag_verified::FtsDeferredMacSession`: the verified state machine
//! decides whether the MAC residual is zero, whether all 48 rounds ran and whether
//! the codeword is a valid constant-sum word, and only then yields the endpoints.
//! Every other opening (the randomizer, public-leaf endpoints, other parameter
//! shapes) has no codeword at release time and uses the same hold, verify, release
//! order with a local zero check.
use alloc::vec::Vec;
use qsag_accel::ct::ct_zeroize_u128s;
use qsag_verified::fts_spn_guard::{
    FtsDeferredMacSession, WOTS_CS_BASE_W, WOTS_CS_CHAINS, WOTS_CS_TARGET_SUM,
};

use crate::parallel_mpc::{ParallelSeededError, ParallelSeededParams};

enum Held {
    Verified(Vec<FtsDeferredMacSession>),
    Local { values: Vec<u128>, mac_verified: bool },
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
            Held::Local {
                values,
                mac_verified: false,
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
            Held::Local {
                values,
                mac_verified,
            } => {
                ct_zeroize_u128s(values);
                values.clear();
                *mac_verified = false;
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
            Held::Local {
                values,
                mac_verified,
            } => {
                *mac_verified = !*mac_verified && !values.is_empty() && residual == [0, 0];
                *mac_verified
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
            Held::Local {
                values,
                mac_verified,
            } => {
                if *mac_verified {
                    *mac_verified = false;
                    Some(core::mem::take(values))
                } else {
                    None
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
                assert!(matches!(gate.held, Held::Local { .. }));
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
}
