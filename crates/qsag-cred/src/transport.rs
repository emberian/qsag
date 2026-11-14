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
    matches.next().is_none()
        && ml_dsa_verify(
            MlDsaLevel::MlDsa44,
            pk,
            bytes,
            b"QSAG.TRANSPORT.V1",
            &signed.signature,
        )
}
