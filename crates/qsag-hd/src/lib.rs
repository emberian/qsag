#![no_std]
#![forbid(unsafe_code)]
//! Hardened SLH-DSA signature-key inventories and linear-module custody with
//! dealerless provisioning.
//!
//! Roots, child rekeys, MAC keys, opening masks and inventory child seeds are
//! produced by the custodians themselves from a one-time subset-seed ceremony
//! ([`seeds`]). The supported model is an honest-majority committee
//! (`n >= 2t - 1`, at most `t - 1` static malicious corruptions) with
//! authenticated confidential channels and consistent broadcast, and security
//! with abort; other committees are rejected. See `STATUS.md` for what is and is
//! not established.

extern crate alloc;
#[cfg(any(test, feature = "std"))]
extern crate std;
#[cfg(feature = "std")]
pub mod budget;
pub mod poison;
pub use poison::PoisonJournal;

mod erase;
pub mod inventory;
pub mod linear_module;
pub mod seeds;
mod zero_gate;

#[cfg(any(test, feature = "testing-ephemeral"))]
pub use inventory::recover_child_signing_seed_unchecked;
pub use inventory::{
    HdError, InventoryChildProof, InventoryMasterPublicKey, InventoryPartyShareVault, RekeyFault,
    WatchOnlyInventoryTable, commit_inventory_public_keys, derive_inventory_vault,
    enroll_child_signing_seed_quorum, inventory_child_public_key, recover_child_signing_seed,
    verify_inventory_child_proof,
};
pub use linear_module::{
    AuthorizedHdProjection, DEFAULT_MAX_DERIVATION_DEPTH, LinearModulePartyShare, LinearModuleXPub,
    MAX_NON_HARDENED_DERIVATION_DEPTH, MODULE_K, MODULE_L, MODULE_MAC_LANES, MODULE_N, MODULE_Q,
    MODULE_SECRET_L, OpeningMask, REKEY_BROADCAST_ROUNDS, REKEY_SACRIFICE_REPS, RekeyRound1,
    RingPoly, SecretRingPoly, ShareScheme, dealerless_opening_mask, expand_matrix_a,
    max_cbd2_linf_norm_after_depth, validate_shamir_eval_points,
};
pub use seeds::{
    CommitteeConfig, CustodianSeeds, CustodianSet, MAX_CUSTODIANS, MAX_SUBSET_SEEDS,
    SeedCeremonyRound1, SeedConfirmation, SeedContributionCommit, SeedPrivateDelivery,
};

#[cfg(test)]
mod tests {
    use alloc::format;
    use alloc::vec::Vec;
    use qsag_accel::CpuReferenceBackend;

    use super::*;
    use crate::linear_module::harness::{committee, honest};
    use crate::seeds::run_seed_ceremony;

    #[test]
    fn test_pi_hd_commit_inventory_zero_online_round_watch_only_and_isolation() {
        let accel = CpuReferenceBackend::new();
        let config = committee(2, 3);
        let seeds = run_seed_ceremony(&config, 0x31);
        let vaults: Vec<_> = seeds
            .iter()
            .map(|custodian| derive_inventory_vault(custodian, [0x42u8; 32], 16).unwrap())
            .collect();
        assert!(format!("{:?}", vaults[0]).contains("<REDACTED>"));
        let enrollment: Vec<&InventoryPartyShareVault> = vaults.iter().collect();
        assert_eq!(
            recover_child_signing_seed(&config, &[&vaults[0], &vaults[1]], 0, None).err(),
            Some(HdError::InvalidSignatureKey)
        );
        let pubkeys: Vec<[u8; 32]> = (0..16)
            .map(|idx| {
                enroll_child_signing_seed_quorum(&config, &enrollment, idx)
                    .unwrap()
                    .1
            })
            .collect();
        let table = commit_inventory_public_keys([0x42u8; 32], pubkeys, &accel).unwrap();
        assert_eq!(table.master_pk.master_root_pk.len(), 32);

        for child_idx in [0u32, 5, 15] {
            let (addr, proof) = table.derive_watch_only_child(child_idx, "qsp").unwrap();
            verify_inventory_child_proof(&table.master_pk, &proof, &addr, &accel).unwrap();
            // A different quorum recovers the seed of exactly the enrolled key.
            recover_child_signing_seed(
                &config,
                &[&vaults[1], &vaults[2]],
                child_idx,
                Some(&proof.child_pk),
            )
            .unwrap();
        }
    }

    #[test]
    fn test_pi_hd_linear_module_dealerless_derivation_mac_and_depth_cap() {
        assert_eq!(
            validate_shamir_eval_points(&[1, 2, 0, 4]),
            Err(HdError::DuplicateOrZeroEvalPoint)
        );
        assert_eq!(
            validate_shamir_eval_points(&[1, 2, 3, 2]),
            Err(HdError::DuplicateOrZeroEvalPoint)
        );

        let config = committee(3, 5);
        let seeds = run_seed_ceremony(&config, 0x55);
        let (xpub_root, shares_root) = honest(&seeds, None, 0, false, 1);
        assert_eq!(xpub_root.max_depth, 4);
        assert!(format!("{:?}", shares_root[0]).contains("<REDACTED>"));

        // Compare watch-only derivation with dealerless rekeys down to the depth cap.
        let mut cur_xpub = xpub_root;
        let mut cur_shares = shares_root;
        for (tag, step_idx) in [7u32, 42, 99, 3].into_iter().enumerate() {
            let expected = cur_xpub.derive_child(step_idx).unwrap();
            (cur_xpub, cur_shares) = honest(
                &seeds,
                Some((&cur_shares, &cur_xpub)),
                step_idx,
                false,
                tag as u8 + 2,
            );
            assert_eq!(cur_xpub, expected);
        }
        assert_eq!(cur_xpub.depth_used, 4);

        // Two distinct 3-of-5 quorums hold the same authenticated child secret,
        // which satisfies A*s1 + s2 = t.
        let s_a =
            linear_module::reconstruct_shamir_and_verify_key_relation(&cur_shares[..3], &cur_xpub)
                .unwrap();
        let s_b =
            linear_module::reconstruct_shamir_and_verify_key_relation(&cur_shares[2..], &cur_xpub)
                .unwrap();
        assert_eq!(s_a, s_b);

        // Depth bounds hold for the watch-only and the custodian side.
        assert_eq!(
            cur_xpub.derive_child(100),
            Err(HdError::DerivationBudgetExceeded { current: 4, max: 4 })
        );
        assert_eq!(
            cur_shares[0]
                .derive_child_share(&seeds[0], &cur_xpub, 100, false, [1; 32], [2; 32])
                .err(),
            Some(HdError::DerivationBudgetExceeded { current: 4, max: 4 })
        );
    }
}
