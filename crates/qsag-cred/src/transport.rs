//! Canonical authentication envelopes for evidence from untrusted transports.
use crate::fips204_ntt::{MlDsaLevel, ml_dsa_verify};
use alloc::vec::Vec;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SignedRoundMessage {
    pub signature: Vec<u8>,
}

/// Canonical framing shared by senders and public evidence verification.
pub fn round_message(
    protocol: &[u8],
    session: &[u8; 32],
    attempt: u32,
    quorum: &[u16],
    party: u16,
    round: u8,
    payload: &[u8],
) -> Vec<u8> {
    let mut ids = quorum.to_vec();
    ids.sort_unstable();
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&(protocol.len() as u64).to_le_bytes());
    bytes.extend_from_slice(protocol);
    bytes.extend_from_slice(session);
    bytes.extend_from_slice(&attempt.to_le_bytes());
    bytes.extend_from_slice(&(ids.len() as u64).to_le_bytes());
    for id in ids {
        bytes.extend_from_slice(&id.to_le_bytes());
    }
    bytes.extend_from_slice(&party.to_le_bytes());
    bytes.push(round);
    bytes.extend_from_slice(&(payload.len() as u64).to_le_bytes());
    bytes.extend_from_slice(payload);
    bytes
}

pub fn verify_transport_message(
    keys: &[(u16, Vec<u8>)],
    party: u16,
    bytes: &[u8],
    signed: &SignedRoundMessage,
) -> bool {
    let mut matches = keys.iter().filter(|(id, _)| *id == party);
    let Some((_, pk)) = matches.next() else {
        return false;
    };
    let level = match pk.len() {
        1312 => MlDsaLevel::MlDsa44,
        1952 => MlDsaLevel::MlDsa65,
        2592 => MlDsaLevel::MlDsa87,
        _ => return false,
    };
    matches.next().is_none()
        && ml_dsa_verify(level, pk, bytes, b"QSAG.TRANSPORT.V1", &signed.signature)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fips204_ntt::{ml_dsa_keygen_from_seed, ml_dsa_sign_deterministic};

    #[test]
    fn all_fips_levels_authenticate_the_same_envelope() {
        let message = round_message(b"test", &[3; 32], 0, &[1, 2, 3], 2, 1, b"payload");
        for level in [
            MlDsaLevel::MlDsa44,
            MlDsaLevel::MlDsa65,
            MlDsaLevel::MlDsa87,
        ] {
            let (pk, sk) = ml_dsa_keygen_from_seed(level, &[7; 32]);
            let signed = SignedRoundMessage {
                signature: ml_dsa_sign_deterministic(&sk, &message, b"QSAG.TRANSPORT.V1").unwrap(),
            };
            let keys = [(2, pk.clone())];
            assert!(verify_transport_message(&keys, 2, &message, &signed));
            assert!(!verify_transport_message(&keys, 1, &message, &signed));
            assert!(!verify_transport_message(&keys, 2, b"modified", &signed));
            assert!(!verify_transport_message(
                &[(2, pk.clone()), (2, pk.clone())],
                2,
                &message,
                &signed
            ));
            assert!(!verify_transport_message(
                &[(2, pk[..pk.len() - 1].to_vec())],
                2,
                &message,
                &signed
            ));
        }
    }
}
