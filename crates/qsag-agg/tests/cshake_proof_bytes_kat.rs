//! Deterministic proof-bytes KAT for `[DKT26]` `< 2^{-128}` QROM Quintic `Fp5` proofs:
//! - Public [`HemQuinticProof`] (`QSAGHQM2`) under both `TurboShake400` and `Poseidon2Gl24`.
//! - Committed-mask zero-knowledge [`ZkHemV2Proof`] (`QSAGZKH2`) under deterministic seed material.
#![cfg(feature = "std")]

use qsag_agg::sig::{EpochWalSink, SigError, WalEpochState};
use qsag_agg::sponge::cshake256_32;
use qsag_agg::zk_hem::relation::{ConstraintSystem, Lc};
use qsag_agg::zk_hem::v2::params::Profile as ZkHemV2Profile;
use qsag_agg::zk_hem::v2::protocol::{prove as prove_v2, verify as verify_v2};
use qsag_agg::{
    AggSigProfile, Goldilocks, HemQuinticProfile, HemQuinticProof, SignerBitmap, SigningMode,
    ValidatorKeypair, prove_hem_quintic_128, verify_hem_quintic_128,
};

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn digest(bytes: &[u8]) -> String {
    hex(&cshake256_32(b"QSAG.TEST.PROOF_BYTES_KAT", bytes))
}

#[derive(Default)]
struct MemoryWal(Option<WalEpochState>);

impl EpochWalSink for MemoryWal {
    fn recovered_state(&self, _pk_root: &[u8; 32]) -> Result<Option<WalEpochState>, SigError> {
        Ok(self.0)
    }

    fn persist_latched_epoch(
        &mut self,
        _pk_root: &[u8; 32],
        next_unused_epoch: u32,
        latched_epoch: u32,
        mu_bytes: &[u8; 32],
    ) -> Result<(), SigError> {
        self.0 = Some((next_unused_epoch, latched_epoch, *mu_bytes));
        Ok(())
    }
}

#[test]
fn hem_quintic_proof_bytes_are_deterministic_and_canonical() {
    let mut keys: Vec<ValidatorKeypair> = (0..4)
        .map(|idx| {
            ValidatorKeypair::keygen_deterministic(AggSigProfile::JortsPoseidon2, &[11; 32], idx)
        })
        .collect();
    let pks: Vec<_> = keys.iter().map(|kp| kp.pk).collect();
    let message = b"kat-aggregate-message";
    let bitmap = SignerBitmap::from_active_indices(4, &[0, 2, 3]).unwrap();
    let sigs: Vec<_> = [0usize, 2, 3]
        .into_iter()
        .map(|idx| {
            let mut wal = MemoryWal::default();
            keys[idx].sign_stateful(message, 0, &mut wal).unwrap()
        })
        .collect();
    let mode = SigningMode::SharedMessage(message);

    for profile in [
        HemQuinticProfile::TurboShake400,
        HemQuinticProfile::Poseidon2Gl24,
    ] {
        let p_a = prove_hem_quintic_128(profile, &pks, &bitmap, &mode, &sigs).unwrap();
        let p_b = prove_hem_quintic_128(profile, &pks, &bitmap, &mode, &sigs).unwrap();
        let bytes_a = p_a.to_bytes();
        let bytes_b = p_b.to_bytes();
        assert_eq!(bytes_a, bytes_b, "HemQuinticProof must be 100% deterministic");
        assert_eq!(&bytes_a[..8], b"QSAGHQM2");
        let decoded = HemQuinticProof::from_bytes(&bytes_a).unwrap();
        assert!(verify_hem_quintic_128(&pks, &mode, &decoded));
        println!(
            "KAT quintic profile={profile:?} len={} digest={}",
            bytes_a.len(),
            digest(&bytes_a)
        );
    }
}

#[test]
fn zkhem_v2_cshake_and_turboshake_proof_bytes_are_deterministic() {
    let f = Goldilocks::from_u64_reduced;
    let mut cs = ConstraintSystem::new();
    let pub_out: Lc = cs.public_input(f(42)).into();
    let a: Lc = cs.alloc(f(6)).into();
    let b: Lc = cs.alloc(f(7)).into();
    let prod: Lc = cs.mul(&a, &b).into();
    cs.enforce_equal(&prod, &pub_out);
    let _ = qsag_agg::zk_hem::relation::sponge12(&mut cs, &[pub_out, prod]);
    let (shape, assignment) = cs.finish_v2();

    for profile in [
        ZkHemV2Profile::CshakeJohnson400,
        ZkHemV2Profile::TurboShakeJohnson400,
    ] {
        let p1 = prove_v2(
            &shape,
            assignment.clone(),
            b"KAT.ZKHEM.V2",
            profile,
            &[0x3C; 32],
        )
        .unwrap();
        let p2 = prove_v2(
            &shape,
            assignment.clone(),
            b"KAT.ZKHEM.V2",
            profile,
            &[0x3C; 32],
        )
        .unwrap();
        let b1 = p1.to_bytes();
        let b2 = p2.to_bytes();
        assert_eq!(b1, b2);
        assert_eq!(&b1[..8], b"QSAGZKH2");
        assert!(verify_v2(&shape, &[f(42)], b"KAT.ZKHEM.V2", profile, &p1));
    }
}
