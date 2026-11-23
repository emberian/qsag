// SPDX-License-Identifier: Apache-2.0 OR MIT
#![no_main]

//! Coverage-guided fuzzer for `zk_hem::relation` (`ConstraintSystem` / `Shape` R1CS + LogUp) and
//! `zk_hem::v2` (`ZkHemV2Proof` `QSAGZKH2` & `ZkHemV2SplitProof` `QSAGZKS2` canonical wire codecs).

use std::sync::OnceLock;

use libfuzzer_sys::fuzz_target;
use qsag_agg::Goldilocks;
use qsag_agg::zk_hem::relation::{ConstraintSystem, Lc, Shape, sponge12};
use qsag_agg::zk_hem::v2::params::Profile;
use qsag_agg::zk_hem::v2::protocol::{
    ZkHemV2Proof, ZkHemV2SplitProof, prove, verify, verify_split,
};

struct HologramFixtures {
    shape: Shape,
    pub_in: [Goldilocks; 1],
    proof_wire: Vec<u8>,
}

fn fixtures() -> &'static HologramFixtures {
    static FX: OnceLock<HologramFixtures> = OnceLock::new();
    FX.get_or_init(|| {
        let f = Goldilocks::from_u64_reduced;
        let mut cs = ConstraintSystem::new();
        let p0: Lc = cs.public_input(f(91)).into();
        let w0: Lc = cs.alloc(f(1)).into();
        cs.enforce_boolean(&w0);
        let b0: Lc = cs.alloc(f(0x5A)).into();
        cs.enforce_byte(&b0);
        let st = sponge12(&mut cs, &[p0, w0, b0]);
        let _ = cs.mul(&st[0], &st[1]);
        let (shape, assignment) = cs.finish_v2();
        let pub_in = [f(91)];
        let proof = prove(
            &shape,
            assignment,
            b"fuzz-hologram-v2",
            Profile::TurboShakeJohnson400,
            &[0x42; 32],
        )
        .unwrap();
        HologramFixtures {
            shape,
            pub_in,
            proof_wire: proof.to_bytes(),
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

    // 1. `ZkHemV2Proof` (`QSAGZKH2`) and `ZkHemV2SplitProof` (`QSAGZKS2`) canonical decoders
    for cand in [rest.to_vec(), with_prefix(b"QSAGZKH2\x11\x10", rest)] {
        if let Some(p) = ZkHemV2Proof::from_bytes(&cand, &fx.shape) {
            assert_eq!(p.to_bytes(), cand);
            let _ = verify(
                &fx.shape,
                &fx.pub_in,
                b"fuzz-hologram-v2",
                Profile::TurboShakeJohnson400,
                &p,
            );
        }
    }
    for cand in [rest.to_vec(), with_prefix(b"QSAGZKS2\x11\x10\x01", rest)] {
        if let Some(sp) = ZkHemV2SplitProof::from_bytes(&cand, &fx.shape) {
            assert_eq!(sp.to_bytes(), cand);
            let _ = verify_split(
                &fx.shape,
                &fx.pub_in,
                b"fuzz-hologram-v2",
                Profile::TurboShakeJohnson400,
                &sp,
            );
        }
    }

    // 2. Seeded mutation over real `ZkHemV2Proof`
    if sel & 1 == 0 {
        let mut mutated = fx.proof_wire.clone();
        for edit in rest.chunks_exact(5).take(6) {
            let idx = (u32::from_le_bytes([edit[0], edit[1], edit[2], edit[3]]) as usize)
                % mutated.len();
            mutated[idx] ^= edit[4];
        }
        if mutated != fx.proof_wire
            && let Some(dec) = ZkHemV2Proof::from_bytes(&mutated, &fx.shape)
        {
            assert_eq!(dec.to_bytes(), mutated);
            assert!(!verify(
                &fx.shape,
                &fx.pub_in,
                b"fuzz-hologram-v2",
                Profile::TurboShakeJohnson400,
                &dec,
            ));
        }
    }
});
