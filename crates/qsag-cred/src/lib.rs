#![no_std]
#![forbid(unsafe_code)]
#![allow(clippy::chunks_exact_to_as_chunks)]
//! Post-Quantum Threshold Credentials, 2-Round Verifiable Lattice OPRF (`PiVoprf`),
//! Blind Threshold Verifiable Credentials + Unlinkable Selective Disclosure (`PiBlindVc`),
//! and Dealerless Standard-Verifier `FIPS 204` Threshold `ML-DSA` (`ThresholdMlDsa`).
extern crate alloc;
#[cfg(any(test, feature = "std"))]
extern crate std;
pub mod blind_vc;
pub mod fips204_ntt;
pub mod rss_mpc;
pub mod threshold_mldsa;
pub mod threshold_mldsa_shamir;
mod toprf_engine;
pub mod voprf;
pub mod voprf_spdz;
pub use fips204_ntt::{
    MLDSA_D, MLDSA_N, MLDSA_Q, MlDsaLevel, MlDsaParams, MlDsaSigningKey, Poly256,
    ml_dsa_keygen_from_seed, ml_dsa_sign_deterministic, ml_dsa_verify, pk_decode, pk_encode,
    sig_decode, sig_encode,
};
pub use rss_mpc::{
    MpcError, MpcStats, MpcTransport, MpcTransportError, RoundInbox, RoundInfo, RoundKind,
};
#[cfg(feature = "std")]
pub use threshold_mldsa::FsNonceBurnStore;
pub use threshold_mldsa::{
    DEFAULT_MAX_REJECTION_ATTEMPTS, MAX_THRESHOLD_MLDSA_PARTIES, NonceBurnPersistence,
    ThresholdMlDsaDkgConfig, ThresholdMlDsaError, ThresholdMlDsaSignerShare, ThresholdPolicyGate,
    ThresholdSignOutput, ThresholdSignSession, ThresholdVerificationPack,
    threshold_mldsa_dkg_party, threshold_sign_mldsa_party, threshold_sign_mldsa_party_policy_gated,
};
pub use threshold_mldsa_shamir::threshold_mldsa_shamir_expand_party;
