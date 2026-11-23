// SPDX-License-Identifier: Apache-2.0 OR MIT
#![no_main]

//! Coverage-guided adversarial wire-decoder, canonical roundtrip, and soundness fuzzer for
//! `ZkHemV2Proof::from_bytes` (`QSAGZKH2`) + `v2::verify` and `ZkHemV2SplitProof::from_bytes`
//! (`QSAGZKS2`) + `v2::verify_split`, across shapes WITH and WITHOUT LogUp lookup tables.

use std::sync::OnceLock;

use libfuzzer_sys::fuzz_target;
use qsag_agg::field::Goldilocks;
use qsag_agg::zk_hem::relation::{ConstraintSystem, Lc, Shape, sponge12};
use qsag_agg::zk_hem::v2::params::Profile;
use qsag_agg::zk_hem::v2::protocol::{
    self as v2, MAGIC as ZKH2_MAGIC, MAGIC_SPLIT as ZKS2_MAGIC, ZkHemV2Proof, ZkHemV2SplitProof,
};

struct V2Fixtures {
    plain_shape: Shape,
    plain_pub: [Goldilocks; 1],
    plain_wire: Vec<u8>,
    lookup_shape: Shape,
    lookup_pub: [Goldilocks; 1],
    lookup_wire: Vec<u8>,
}

const STMT: &[u8] = b"fuzz-zkhem-v2-icd";

fn fixtures() -> &'static V2Fixtures {
    static FX: OnceLock<V2Fixtures> = OnceLock::new();
    FX.get_or_init(|| {
        let f = Goldilocks::from_u64_reduced;

        // 1. Plain v2 relation (`log_rows >= 5`)
        let mut cs = ConstraintSystem::new();
        let p: Lc = cs.public_input(f(19)).into();
        let w: Lc = cs.alloc(f(1)).into();
        cs.enforce_boolean(&w);
        let st = sponge12(&mut cs, &[p, w]);
        let _ = cs.mul(&st[0], &st[1]);
        let (plain_shape, plain_z) = cs.finish_v2();
        let plain_proof = v2::prove(
            &plain_shape,
            plain_z,
            STMT,
            Profile::TurboShakeJohnson400,
            &[0x31; 32],
        )
        .expect("plain v2 proof");
        assert!(v2::verify(
            &plain_shape,
            &[f(19)],
            STMT,
            Profile::TurboShakeJohnson400,
            &plain_proof
        ));

        // 2. LogUp-enabled v2 relation (`enforce_byte` lookup table)
        let mut cs_lk = ConstraintSystem::new();
        let p_lk: Lc = cs_lk.public_input(f(42)).into();
        for i in 0..8u64 {
            let cell: Lc = cs_lk.alloc(f(10 + i)).into();
            cs_lk.enforce_byte(&cell);
        }
        let st_lk = sponge12(&mut cs_lk, &[p_lk]);
        let _ = cs_lk.mul(&st_lk[0], &st_lk[1]);
        let (lookup_shape, lookup_z) = cs_lk.finish_v2();
        let lookup_proof = v2::prove(
            &lookup_shape,
            lookup_z,
            STMT,
            Profile::TurboShakeJohnson400,
            &[0x72; 32],
        )
        .expect("lookup v2 proof");
        assert!(v2::verify(
            &lookup_shape,
            &[f(42)],
            STMT,
            Profile::TurboShakeJohnson400,
            &lookup_proof
        ));

        V2Fixtures {
            plain_shape,
            plain_pub: [f(19)],
            plain_wire: plain_proof.to_bytes(),
            lookup_shape,
            lookup_pub: [f(42)],
            lookup_wire: lookup_proof.to_bytes(),
        }
    })
}

fn prefix_with(magic: &[u8; 8], rest: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(8 + rest.len());
    out.extend_from_slice(magic);
    out.extend_from_slice(rest);
    out
}

fuzz_target!(init: {
    fixtures();
}, |data: &[u8]| {
    let fx = fixtures();
    let Some((&sel, rest)) = data.split_first() else {
        return;
    };
    let profile = if sel & 1 == 0 {
        Profile::TurboShakeJohnson400
    } else {
        Profile::CshakeJohnson400
    };

    // 1. Untrusted wire decoding on both plain and LogUp shapes (`QSAGZKH2` & `QSAGZKS2`)
    for (shape, pub_in) in [
        (&fx.plain_shape, &fx.plain_pub[..]),
        (&fx.lookup_shape, &fx.lookup_pub[..]),
    ] {
        for cand in [rest.to_vec(), prefix_with(&ZKH2_MAGIC, rest)] {
            if let Some(proof) = ZkHemV2Proof::from_bytes(&cand, shape) {
                assert_eq!(proof.to_bytes(), cand);
                let _ = v2::verify(shape, pub_in, STMT, profile, &proof);
            }
        }
        for cand in [rest.to_vec(), prefix_with(&ZKS2_MAGIC, rest)] {
            if let Some(split_proof) = ZkHemV2SplitProof::from_bytes(&cand, shape) {
                assert_eq!(split_proof.to_bytes(), cand);
                let _ = v2::verify_split(shape, pub_in, STMT, profile, &split_proof);
            }
        }
    }

    // 2. Seeded mutation of valid single-prover proofs (plain & LogUp) AND synthetic split-header lift
    if sel & 2 == 0 {
        let (shape, pub_in, base) = if sel & 4 == 0 {
            (&fx.plain_shape, &fx.plain_pub[..], &fx.plain_wire)
        } else {
            (&fx.lookup_shape, &fx.lookup_pub[..], &fx.lookup_wire)
        };
        let mut mutated = base.clone();
        for edit in rest.chunks_exact(5).take(8) {
            let idx = (u32::from_le_bytes([edit[0], edit[1], edit[2], edit[3]]) as usize)
                % mutated.len();
            mutated[idx] ^= edit[4];
        }
        if mutated != *base
            && let Some(proof) = ZkHemV2Proof::from_bytes(&mutated, shape)
        {
            assert_eq!(proof.to_bytes(), mutated);
            assert!(
                !v2::verify(shape, pub_in, STMT, Profile::TurboShakeJohnson400, &proof),
                "mutated ZkHemV2Proof forged verification"
            );
        }

        // Also lift single-prover body into a 1-committer `QSAGZKS2` candidate and mutate it
        if sel & 4 == 0 && base.len() > 10 {
            let mut split_cand = Vec::with_capacity(base.len() + 1);
            split_cand.extend_from_slice(&ZKS2_MAGIC);
            split_cand.push(base[8]);
            split_cand.push(base[9]);
            split_cand.push(1u8); // committers = 1
            split_cand.extend_from_slice(&base[10..]);
            for edit in rest.chunks_exact(5).take(4) {
                let idx = (u32::from_le_bytes([edit[0], edit[1], edit[2], edit[3]]) as usize)
                    % split_cand.len();
                split_cand[idx] ^= edit[4];
            }
            if let Some(sp) = ZkHemV2SplitProof::from_bytes(&split_cand, shape) {
                assert_eq!(sp.to_bytes(), split_cand);
                let _ = v2::verify_split(shape, pub_in, STMT, Profile::TurboShakeJohnson400, &sp);
            }
        }
    }
});
