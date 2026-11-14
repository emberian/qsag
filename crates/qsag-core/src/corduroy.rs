//! `Corduroy`: the algebraic Poseidon2 hypertree custody scheme.
//!
//! `Corduroy` is the stateless target-sum Winternitz hypertree of [`crate::tsw_baggy`]
//! instantiated with the Poseidon2 tweakable hash and the
//! [`PqHashParams::CORDUROY_CUSTODY_128`] geometry, signed by the authenticated-share
//! Poseidon2 engine of [`crate::poseidon2_mpc`]. This module gives that scheme its suite
//! name; it adds no new cryptography and leaves the Poseidon2 permutation, its round
//! constants and its S-box untouched.

use crate::tsw_baggy::{
    PqHashParams, PqHashSig, PqPublicKey, PqSecretKey, Poseidon2Suite, derive_public_key,
    verify_pq_hash_sig,
};

pub use crate::poseidon2_mpc::{
    build_distributed_poseidon2_key as corduroy_keygen_mpc,
    build_distributed_poseidon2_key_cached as corduroy_keygen_mpc_cached,
    sign_stateless_tsw_poseidon2_mpc as sign_corduroy_mpc,
    sign_stateless_tsw_poseidon2_mpc_cached as sign_corduroy_mpc_cached,
};

/// Marker for the suite.
#[derive(Clone, Copy, Debug)]
pub struct Corduroy;

/// Parameter, key and signature types of the suite.
pub type CorduroyParams = PqHashParams;
pub type CorduroyPublicKey = PqPublicKey;
pub type CorduroySig = PqHashSig;

impl Corduroy {
    /// The custody parameter set.
    pub const PARAMS: CorduroyParams = PqHashParams::CORDUROY_CUSTODY_128;

    /// Verify a signature under `params` (use [`Self::PARAMS`] in production).
    pub fn verify(
        params: &CorduroyParams,
        pk: &CorduroyPublicKey,
        msg: &[u8],
        sig: &CorduroySig,
    ) -> bool {
        !params.stateful && verify_pq_hash_sig(Poseidon2Suite, params, pk, msg, sig)
    }

    /// Single-party reference public key (tests and known-answer comparisons).
    pub fn reference_public_key(params: &CorduroyParams, sk: &PqSecretKey) -> CorduroyPublicKey {
        derive_public_key(Poseidon2Suite, params, sk)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tsw_baggy::eval_single_sign_stateless;

    #[test]
    fn corduroy_parameters_are_the_custody_preset_and_verify_reference_signatures() {
        const { assert!(Corduroy::PARAMS.is_well_formed() && !Corduroy::PARAMS.stateful) };
        assert_eq!((Corduroy::PARAMS.w, Corduroy::PARAMS.ell1), (4, 128));

        // A compact geometry keeps the reference signer fast; the hash suite is the real one.
        let params = PqHashParams::COMPACT_GOLDEN;
        let sk = PqSecretKey {
            sk_seed: [0x11; 32],
            sk_prf: [0x22; 32],
            pk_seed: [0x33; 32],
        };
        let pk = Corduroy::reference_public_key(&params, &sk);
        let sig = eval_single_sign_stateless(Poseidon2Suite, &params, &sk, &pk, b"m", &[7u8; 32], 1 << 20)
            .expect("reference signature");
        assert!(Corduroy::verify(&params, &pk, b"m", &sig));
        assert!(!Corduroy::verify(&params, &pk, b"n", &sig));
        // A stateful parameter set is not a Corduroy parameter set.
        assert!(!Corduroy::verify(&PqHashParams::COMPACT_JORTS, &pk, b"m", &sig));
    }
}
