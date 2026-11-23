// SPDX-License-Identifier: Apache-2.0 OR MIT
#![no_main]

//! Coverage-guided untrusted wire-decoder & verifier fuzzer for Quintic `Fp5` public
//! signature aggregation (`HemQuinticProof` `QSAGHQM2`, `ValidatorPublicKey`, `ValidatorSignature`,
//! `SignerBitmap`, and `HierarchicalHemAggregate` `QSAGHEM\x04`).

use std::sync::OnceLock;

use libfuzzer_sys::fuzz_target;
use qsag_agg::{
    AggSigProfile, EpochWalSink, HIERARCHICAL_HEM_WIRE_MAGIC, HemQuinticProfile, HemQuinticProof,
    HierarchicalHemAggregate, PreparedPolicyRegistry, ShardHemPolicy, ShardHemWitness, SigError,
    SignerBitmap, SigningMode, ValidatorKeypair, ValidatorPublicKey, ValidatorSignature,
    hierarchical_hem_message, prove_hem_quintic_128, prove_hierarchical_hem_prepared,
    verify_hem_quintic_128, verify_hierarchical_hem_prepared, verify_individual_signature,
};

type EpochReceipt = (u32, u32, [u8; 32]);

#[derive(Default)]
struct MemEpochWal {
    state: Option<([u8; 32], EpochReceipt)>,
}

impl EpochWalSink for MemEpochWal {
    fn recovered_state(&self, pk_root: &[u8; 32]) -> Result<Option<EpochReceipt>, SigError> {
        match &self.state {
            None => Ok(None),
            Some((root, st)) if root == pk_root => Ok(Some(*st)),
            Some(_) => Err(SigError::WalPersistenceFailed),
        }
    }

    fn persist_latched_epoch(
        &mut self,
        pk_root: &[u8; 32],
        next_unused_epoch: u32,
        latched_epoch: u32,
        mu_bytes: &[u8; 32],
    ) -> Result<(), SigError> {
        if let Some((root, _)) = &self.state
            && root != pk_root
        {
            return Err(SigError::WalPersistenceFailed);
        }
        self.state = Some((*pk_root, (next_unused_epoch, latched_epoch, *mu_bytes)));
        Ok(())
    }
}

struct AggFixtures {
    pks: Vec<ValidatorPublicKey>,
    msg: &'static [u8],
    turbo_wire: Vec<u8>,
    gl24_wire: Vec<u8>,
    prepared: PreparedPolicyRegistry,
    hier_wire: Vec<u8>,
}

fn fixtures() -> &'static AggFixtures {
    static FX: OnceLock<AggFixtures> = OnceLock::new();
    FX.get_or_init(|| {
        let mut kp0 =
            ValidatorKeypair::keygen_deterministic(AggSigProfile::JortsPoseidon2, &[11; 32], 0);
        let mut kp1 =
            ValidatorKeypair::keygen_deterministic(AggSigProfile::JortsPoseidon2, &[12; 32], 1);
        let pks = vec![kp0.pk, kp1.pk];
        let msg: &'static [u8] = b"fuzz-whir-agg-quintic-v2";
        let mut wal0 = MemEpochWal::default();
        let mut wal1 = MemEpochWal::default();
        let sig0 = kp0.sign_stateful(msg, 0, &mut wal0).unwrap();
        let sig1 = kp1.sign_stateful(msg, 0, &mut wal1).unwrap();
        let bm = SignerBitmap::from_active_indices(2, &[0, 1]).unwrap();
        let mode = SigningMode::SharedMessage(msg);

        let turbo_wire = prove_hem_quintic_128(
            HemQuinticProfile::TurboShake400,
            &pks,
            &bm,
            &mode,
            &[sig0.clone(), sig1.clone()],
        )
        .unwrap()
        .to_bytes();
        let gl24_wire = prove_hem_quintic_128(
            HemQuinticProfile::Poseidon2Gl24,
            &pks,
            &bm,
            &mode,
            &[sig0, sig1],
        )
        .unwrap()
        .to_bytes();

        let policies = vec![ShardHemPolicy {
            shard_id: 1,
            custodian_cluster: [0xA1; 32],
            quorum_keys: pks.clone(),
            minimum_quorums: 1,
        }];
        let prepared = PreparedPolicyRegistry::new(policies.clone()).unwrap();
        let reg_msg =
            hierarchical_hem_message(&prepared.policy_registry_root(), &policies[0], 5, msg);
        let sig_h = kp0.sign_stateful(&reg_msg, 1, &mut wal0).unwrap();
        let bm_h = SignerBitmap::from_active_indices(2, &[0]).unwrap();
        let sigs_h = [sig_h];
        let hier_wire = prove_hierarchical_hem_prepared(
            &prepared,
            &[ShardHemWitness {
                bitmap: &bm_h,
                signatures: &sigs_h,
            }],
            5,
            msg,
            1,
            HemQuinticProfile::TurboShake400,
        )
        .unwrap()
        .to_bytes();

        AggFixtures {
            pks,
            msg,
            turbo_wire,
            gl24_wire,
            prepared,
            hier_wire,
        }
    })
}

fn with_prefix(prefix: &[u8], body: &[u8]) -> Vec<u8> {
    let mut v = Vec::with_capacity(prefix.len() + body.len());
    v.extend_from_slice(prefix);
    v.extend_from_slice(body);
    v
}

fuzz_target!(init: {
    fixtures();
}, |data: &[u8]| {
    let fx = fixtures();
    let Some((&sel, rest)) = data.split_first() else {
        return;
    };

    // 1. `SignerBitmap`, `ValidatorPublicKey`, and `ValidatorSignature` canonical decoders
    if let Some((bm, used)) = SignerBitmap::from_bytes_canonical(rest) {
        assert_eq!(bm.to_bytes(), rest[..used]);
    }
    if let Ok(arr) = <&[u8; 65]>::try_from(rest)
        && let Some(pk) = ValidatorPublicKey::from_bytes_canonical(arr)
    {
        assert_eq!(&pk.to_bytes(), arr);
    }
    for prof in [
        AggSigProfile::JortsPoseidon2,
        AggSigProfile::CorduroyPoseidon2,
    ] {
        if let Ok(sig) = ValidatorSignature::from_bytes_canonical(prof, rest) {
            assert_eq!(sig.to_bytes(), rest);
            let _ = verify_individual_signature(&fx.pks[0], fx.msg, &sig);
        }
    }

    // 2. `HemQuinticProof` (`QSAGHQM2`) raw + magic-prefixed + differential mutation
    let mode = SigningMode::SharedMessage(fx.msg);
    for cand in [rest.to_vec(), with_prefix(b"QSAGHQM2", rest)] {
        if let Some(proof) = HemQuinticProof::from_bytes(&cand) {
            assert_eq!(proof.to_bytes(), cand);
            let _ = verify_hem_quintic_128(&fx.pks, &mode, &proof);
        }
    }

    let base = if sel & 1 == 0 {
        &fx.turbo_wire
    } else {
        &fx.gl24_wire
    };
    let mut mutated = base.clone();
    for edit in rest.chunks_exact(5).take(6) {
        let idx = (u32::from_le_bytes([edit[0], edit[1], edit[2], edit[3]]) as usize)
            % mutated.len();
        mutated[idx] ^= edit[4];
    }
    if mutated != *base
        && let Some(dec) = HemQuinticProof::from_bytes(&mutated)
    {
        assert_eq!(dec.to_bytes(), mutated);
        assert!(!verify_hem_quintic_128(&fx.pks, &mode, &dec));
    }

    // 3. `HierarchicalHemAggregate` (`QSAGHEM\x04`) wire decoder + verifier
    for cand in [
        rest.to_vec(),
        with_prefix(HIERARCHICAL_HEM_WIRE_MAGIC, rest),
    ] {
        if let Ok(agg) = HierarchicalHemAggregate::from_bytes_canonical(&cand) {
            assert_eq!(agg.to_bytes(), cand);
            let _ = verify_hierarchical_hem_prepared(
                &fx.prepared,
                5,
                fx.msg,
                1,
                HemQuinticProfile::TurboShake400,
                &agg,
            );
        }
    }
    if sel & 2 == 0 {
        let mut h_mut = fx.hier_wire.clone();
        for edit in rest.chunks_exact(5).take(6) {
            let idx = (u32::from_le_bytes([edit[0], edit[1], edit[2], edit[3]]) as usize)
                % h_mut.len();
            h_mut[idx] ^= edit[4];
        }
        if h_mut != fx.hier_wire
            && let Ok(agg) = HierarchicalHemAggregate::from_bytes_canonical(&h_mut)
        {
            assert_eq!(agg.to_bytes(), h_mut);
            assert!(!verify_hierarchical_hem_prepared(
                &fx.prepared,
                5,
                fx.msg,
                1,
                HemQuinticProfile::TurboShake400,
                &agg,
            ));
        }
    }
});
