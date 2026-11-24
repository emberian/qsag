#![no_std]
#![forbid(unsafe_code)]
//! Committed SLH-DSA key inventories with distributed subset-seed provisioning.
extern crate alloc;
#[cfg(any(test, feature = "std"))]
extern crate std;
#[cfg(feature = "std")]
pub mod budget;
pub mod poison;
pub use poison::PoisonJournal;

pub mod inventory;
pub mod seeds;

#[cfg(any(test, feature = "testing-ephemeral"))]
pub use inventory::recover_child_signing_seed_unchecked;
pub use inventory::{
    HdError, InventoryChildProof, InventoryMasterPublicKey, InventoryPartyShareVault, RekeyFault,
    WatchOnlyInventoryTable, commit_inventory_public_keys, derive_inventory_vault,
    derive_rss_child_share_2of3, enroll_child_signing_seed_quorum, inventory_child_public_key,
    recover_child_signing_seed, verify_inventory_child_proof,
};
#[cfg(feature = "std")]
pub use inventory::{derive_rss_child_share_2of3_budgeted, recover_child_signing_seed_budgeted};
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
    use crate::seeds::run_seed_ceremony;

    #[test]
    fn partial_field_buffers_are_erased_on_error() {
        use core::cell::Cell;
        use qsag_asm::wipe::{SecretBuffer, SecretWipe};
        struct Probe<'a>(u32, &'a Cell<usize>);
        impl SecretWipe for Probe<'_> {
            fn secret_wipe(&mut self) {
                self.0 = 0;
                self.1.set(self.1.get() + 1);
            }
        }
        fn fail(erased: &Cell<usize>) -> Result<(), ()> {
            let mut words = SecretBuffer(Vec::with_capacity(7));
            words.extend([11, 12, 13].map(|value| Probe(value, erased)));
            Err(())?;
            Ok(())
        }
        let erased = Cell::new(0);
        assert!(fail(&erased).is_err());
        assert_eq!(erased.get(), 3);
    }

    #[test]
    fn test_pi_hd_commit_inventory_zero_online_round_watch_only_and_isolation() {
        let accel = CpuReferenceBackend::new();
        let config = CommitteeConfig::new(2, &[(0, 1), (1, 2), (2, 3)], [0x5a; 32]).unwrap();
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
}
