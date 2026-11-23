// SPDX-License-Identifier: Apache-2.0 OR MIT
#![no_main]

//! Coverage-guided adversarial wire-decoder, canonical bijection, and R1CS/WHIR verifier fuzzer
//! for `[DKT26]` `< 2^{-128}` QROM `FixedPathWhirW24::from_bytes_canonical` (`QSAGIW24`) and
//! `SuccinctIvcProof::from_bytes_canonical` (`QSAGIVC1\x00` + `verify_ivc_tree`).

use std::sync::OnceLock;

use libfuzzer_sys::fuzz_target;
use qsag_agg::field::Goldilocks;
use qsag_agg::zk_hem::v2::field5::Fp5;
use qsag_agg::{
    FixedPathWhirW24, IvcStepConfig, IvcSubtreeStatement, IvcTableCommitment, SuccinctIvcProof,
    verify_ivc_tree,
};

struct IvcW24Fixtures {
    cfg16: IvcStepConfig,
    context: [Goldilocks; 3],
    nonce16: [Goldilocks; 4],
    root16: [Goldilocks; 7],
    point16: Vec<Fp5>,
    value16: Fp5,
    opening16_wire: Vec<u8>,
    stmt: IvcSubtreeStatement,
}

fn fixtures() -> &'static IvcW24Fixtures {
    static FX: OnceLock<IvcW24Fixtures> = OnceLock::new();
    FX.get_or_init(|| {
        let f = Goldilocks::from_u64_reduced;
        let cfg16 = IvcStepConfig::dkt26(16).expect("dkt26 16");
        let table: Vec<Goldilocks> = (0..(1usize << 16))
            .map(|i| f((i as u64).wrapping_mul(17).wrapping_add(3)))
            .collect();
        let com = IvcTableCommitment::commit(&cfg16, &table, &[0x5A; 32]).expect("commit w24");
        let context = [f(11), f(22), f(33)];
        let point16: Vec<Fp5> = (0..16).map(|i| Fp5::from_u64((i + 5) as u64)).collect();
        let (value16, opening16) = com.open(&context, &point16).expect("open w24");
        assert!(opening16.verify(&cfg16, &context, com.nonce(), com.root(), &point16, value16));
        let opening16_wire = opening16.to_bytes();
        let decoded =
            FixedPathWhirW24::from_bytes_canonical(&cfg16, &opening16_wire).expect("roundtrip");
        assert_eq!(decoded, opening16);

        IvcW24Fixtures {
            cfg16,
            context,
            nonce16: com.nonce(),
            root16: com.root(),
            point16,
            value16,
            opening16_wire,
            stmt: IvcSubtreeStatement {
                policy_registry_root: [0x33; 32],
                shard_lo: 0,
                shard_hi: 2,
                total_quorums: 2,
                message_digest: [0x77; 32],
            },
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

    // 1. `FixedPathWhirW24::from_bytes_canonical` at `dkt26(16)`
    for cand in [rest.to_vec(), with_prefix(b"QSAGIW24", rest)] {
        if let Some(op) = FixedPathWhirW24::from_bytes_canonical(&fx.cfg16, &cand) {
            assert_eq!(op.to_bytes(), cand);
            let _ = op.verify(
                &fx.cfg16,
                &fx.context,
                fx.nonce16,
                fx.root16,
                &fx.point16,
                fx.value16,
            );
        }
    }

    // 2. `SuccinctIvcProof` canonical decoder (`QSAGIVC1\x00` only; non-zero tag rejected)
    for cand in [
        rest.to_vec(),
        with_prefix(b"QSAGIVC1\x01", rest),
        with_prefix(b"QSAGIVC1\x00", rest),
    ] {
        if cand.len() >= 9 && &cand[..8] == b"QSAGIVC1" && cand[8] != 0 {
            assert!(SuccinctIvcProof::from_bytes_canonical(&cand).is_none());
        }
        if let Some(prod_proof) = SuccinctIvcProof::from_bytes_canonical(&cand) {
            assert_eq!(prod_proof.to_bytes(), cand);
            let _ = verify_ivc_tree(&fx.stmt, &prod_proof);
        }
    }

    // 3. Seeded differential mutation over real `FixedPathWhirW24` opening
    if sel & 1 == 0 {
        let mut mutated = fx.opening16_wire.clone();
        for edit in rest.chunks_exact(5).take(8) {
            let idx = (u32::from_le_bytes([edit[0], edit[1], edit[2], edit[3]]) as usize)
                % mutated.len();
            mutated[idx] ^= edit[4];
        }
        if mutated != fx.opening16_wire
            && let Some(op) = FixedPathWhirW24::from_bytes_canonical(&fx.cfg16, &mutated)
        {
            assert_eq!(op.to_bytes(), mutated);
            assert!(
                !op.verify(
                    &fx.cfg16,
                    &fx.context,
                    fx.nonce16,
                    fx.root16,
                    &fx.point16,
                    fx.value16
                ),
                "mutated FixedPathWhirW24 forged verification"
            );
        }
    }
});
