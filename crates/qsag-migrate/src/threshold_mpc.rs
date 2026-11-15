//! General custodian quorums, separate from the three virtual ZKBoo views.
//!
//! This backend uses additive online sharing and one-use trusted-dealer Beaver
//! triples. Online additive privacy requires at least one honest participant;
//! Shamir custody additionally requires fewer than `t` colluding custodians.
//! It does NOT provide the RSS backend's active-security
//! guarantee. Pairwise authentication detects transport corruption, not malicious
//! computation. Preprocessing must be independent of witnesses, never reused,
//! delivered confidentially, and erased by the dealer before online execution.
use crate::{
    circuit::{Domain, Value},
    outer_mpc::{Bit, Engine, Envelope, Error, FieldWord, Transport, Word},
    secret::{Secret, SecretVec},
};
use alloc::{vec, vec::Vec};
use qsag_accel::{
    ct::{ct_eq_bytes_mask, ct_zeroize_bytes, ct_zeroize_u64s},
    keccak::{Shake256, cshake256_framed_32},
};

/// Immutable roster and ordered active quorum. Party identities are zero based;
/// Shamir evaluation points are `party + 1` in the AES GF(256) polynomial basis.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ThresholdConfig {
    threshold: usize,
    parties: usize,
    quorum: Vec<usize>,
}
impl ThresholdConfig {
    pub fn new(threshold: usize, parties: usize, quorum: Vec<usize>) -> Result<Self, Error> {
        if !(2..=64).contains(&parties)
            || !(2..=parties).contains(&threshold)
            || quorum.len() < threshold
            || quorum.len() > parties
            || quorum.iter().any(|&p| p >= parties)
            || quorum.windows(2).any(|w| w[0] >= w[1])
        {
            return Err(Error::InvalidConfiguration);
        }
        Ok(Self {
            threshold,
            parties,
            quorum,
        })
    }
    pub fn threshold(&self) -> usize {
        self.threshold
    }
    pub fn parties(&self) -> usize {
        self.parties
    }
    pub fn quorum(&self) -> &[usize] {
        &self.quorum
    }
    pub(crate) fn binding(&self) -> Vec<u8> {
        let mut b = vec![self.threshold as u8, self.parties as u8];
        b.extend(self.quorum.iter().map(|&p| p as u8));
        b
    }
    /// Convert a bytewise degree-(t-1) Shamir share to its XOR contribution,
    /// without reconstructing any byte of the witness locally.
    pub fn shamir_contribution(&self, party: usize, share: &[u8; 32]) -> Result<[u8; 32], Error> {
        if !self.quorum.contains(&party) {
            return Err(Error::InvalidConfiguration);
        }
        let x = (party + 1) as u8;
        let mut weight = 1;
        for &peer in &self.quorum {
            if peer != party {
                let y = (peer + 1) as u8;
                weight = gf_mul(weight, gf_mul(y, gf_pow(x ^ y, 254)));
            }
        }
        Ok(share.map(|b| gf_mul(b, weight)))
    }
}
fn gf_mul(mut a: u8, mut b: u8) -> u8 {
    let mut out = 0;
    for _ in 0..8 {
        out ^= a & 0u8.wrapping_sub(b & 1);
        a = (a << 1) ^ (0x1b & 0u8.wrapping_sub(a >> 7));
        b >>= 1;
    }
    out
}
fn gf_pow(mut a: u8, mut n: u8) -> u8 {
    let mut out = 1;
    while n != 0 {
        if n & 1 != 0 {
            out = gf_mul(out, a);
        }
        a = gf_mul(a, a);
        n >>= 1;
    }
    out
}

/// Field identifier for preprocessing requests; independent of private circuit types.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ThresholdField {
    Goldilocks,
    Secp256k1,
    Ed25519,
}
impl ThresholdField {
    fn domain(self) -> Domain {
        match self {
            Self::Goldilocks => Domain::Gold,
            Self::Secp256k1 => Domain::Secp,
            Self::Ed25519 => Domain::Ed,
        }
    }
    pub(crate) fn from_domain(d: Domain) -> Self {
        match d {
            Domain::Gold => Self::Goldilocks,
            Domain::Secp => Self::Secp256k1,
            Domain::Ed => Self::Ed25519,
            Domain::Bit => unreachable!(),
        }
    }
}
/// One party's one-use XOR shares of 64 independent Boolean triples `(a,b,a&b)`.
/// The type is intentionally neither Clone nor Copy.
pub struct BooleanTriple(pub [u64; 3]);
impl Drop for BooleanTriple {
    fn drop(&mut self) {
        ct_zeroize_u64s(&mut self.0);
    }
}
/// One party's one-use additive shares of a field triple `(a,b,a*b)`.
pub struct FieldTriple(pub [[u64; 4]; 3]);
impl Drop for FieldTriple {
    fn drop(&mut self) {
        ct_zeroize_u64s(self.0.as_flattened_mut());
    }
}

/// Offline trusted preprocessing generator. Construct once with fresh secret
/// entropy; consume batches in the same order at all quorum members. Never give
/// this object or its entropy to an online custodian. Recreating it with the same
/// entropy/session reuses triples and destroys privacy.
