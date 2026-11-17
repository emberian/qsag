#![no_std]
#![forbid(unsafe_code)]
#![allow(clippy::chunks_exact_to_as_chunks)]
//! Threshold cryptographic building blocks and accumulator-based credentials.
//!
//! [`voprf`] evaluates a custom symmetric Poseidon2/cSHAKE PRF using actively
//! checked replicated sharing (five online servers, privacy against one corrupt
//! server). [`voprf_spdz`] evaluates the same function with Shamir/SPDZ shares.
//! Neither is a lattice OPRF or a publicly transferable proof of PRF evaluation:
//! verifiability relies on authenticated server responses and the enrolled key
//! record. The SPDZ API handles all online states together; its authenticated
//! network deployment is not implemented here.
//!
//! [`blind_vc`] enrolls issuer-approved attribute commitments in an issuer-managed
//! Merkle accumulator. Issuance discloses the attributes and commitment to the
//! issuer while hiding the holder blind. Presentations prove selective disclosure
//! and membership against an issuer-signed root, which verifiers must authenticate
//! and apply an epoch policy to. Verification consumes a challenge from the verifier's
//! [`presentation_challenge`] ledger, so a captured presentation is accepted once.
//! There is no independent publicly verifiable
//! signature on each credential. Fresh presentation entropy avoids an intentional
//! stable pseudonym; attributes and application metadata may still link holders.
//!
//! The crate also implements standard-verifier FIPS 204 ML-DSA and dealerless
//! threshold ML-DSA. These are separate from the symmetric OPRF construction.
extern crate alloc;
#[cfg(any(test, feature = "std"))]
extern crate std;
pub mod blind_vc;
pub mod fips204_ntt;
pub mod presentation_challenge;
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
