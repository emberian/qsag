// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Head-to-head release timing benchmark comparing `qsag-core::fips205` (`SLH-DSA-SHAKE`)
//! and `qsag-cred::fips204_ntt` (`ML-DSA-44`, `ML-DSA-65`, `ML-DSA-87`) against upstream
//! `fips205` (`v0.4`) and `fips204` (`v0.4`) crates.

use std::hint::black_box;
use std::time::Instant;

use fips204::traits::{
    KeyGen as Fips204KeyGen, SerDes as Fips204SerDes, Signer as Fips204Signer,
    Verifier as Fips204Verifier,
};
use fips204::{ml_dsa_44, ml_dsa_65, ml_dsa_87};
use fips205::traits::{
    KeyGen as Fips205KeyGen, SerDes as Fips205SerDes, Signer as Fips205Signer,
    Verifier as Fips205Verifier,
};
use fips205::{
    slh_dsa_shake_128f, slh_dsa_shake_128s, slh_dsa_shake_192f, slh_dsa_shake_256f,
    slh_dsa_shake_256s,
};
use qsag_asm::{detect_backend, mldsa_inv_ntt, mldsa_ntt, mldsa_ntt_with_backend, SimdBackend};
use qsag_core::fips205::{Fips205Params, slh_keygen_internal, slh_sign, slh_verify};
use qsag_cred::fips204_ntt::expand_a_ntt;
use qsag_cred::{MLDSA_N, MLDSA_Q, MlDsaLevel, Poly256, ml_dsa_keygen_from_seed, ml_dsa_sign_deterministic, ml_dsa_verify};

fn measure_us(warmup: usize, iters: usize, mut f: impl FnMut()) -> (f64, f64) {
    for _ in 0..warmup {
        f();
    }
    let mut samples = Vec::with_capacity(iters);
    for _ in 0..iters {
        let t0 = Instant::now();
        f();
        samples.push(t0.elapsed().as_nanos() as f64 / 1_000.0);
    }
    samples.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let median = samples[samples.len() / 2];
    let mean = samples.iter().sum::<f64>() / (samples.len() as f64);
    (median, mean)
}

macro_rules! bench_slh_dsa {
    ($label:expr, $params:expr, $up_mod:ident, $n:literal, $kg_iters:expr, $sign_iters:expr, $ver_iters:expr) => {{
        let params = $params;
        let sk_seed = [0x11u8; $n];
        let sk_prf = [0x22u8; $n];
        let pk_seed = [0x33u8; $n];
        let msg = b"nist-fips-205-simd-benchmark-payload-bytes";
        let ctx = b"bench-ctx";

        let (q_sk, q_pk) =
            slh_keygen_internal(&params, &sk_seed, &sk_prf, &pk_seed).expect("qsag keygen");
        let (u_pk, u_sk) = $up_mod::KG::keygen_with_seeds(&sk_seed, &sk_prf, &pk_seed);
        assert_eq!(q_pk.to_bytes().as_slice(), u_pk.clone().into_bytes().as_slice());

        let q_sig = slh_sign(&params, msg, ctx, &q_sk, None).expect("qsag sign");
        let u_sig = u_sk.try_sign(msg, ctx, false).expect("upstream sign");
        assert_eq!(q_sig.as_slice(), u_sig.as_slice());
        assert!(slh_verify(&params, msg, &q_sig, ctx, &q_pk));
        assert!(u_pk.verify(msg, &u_sig, ctx));

        let kg_warm = ($kg_iters / 4).max(1);
        let (q_kg_med, _) = measure_us(kg_warm, $kg_iters, || {
            let res = slh_keygen_internal(
                black_box(&params),
                black_box(&sk_seed),
                black_box(&sk_prf),
                black_box(&pk_seed),
            )
            .unwrap();
            black_box(res);
        });
        let (u_kg_med, _) = measure_us(kg_warm, $kg_iters, || {
            let res = $up_mod::KG::keygen_with_seeds(
                black_box(&sk_seed),
                black_box(&sk_prf),
                black_box(&pk_seed),
            );
            black_box(res);
        });

        let sign_warm = ($sign_iters / 4).max(1);
        let (q_sg_med, _) = measure_us(sign_warm, $sign_iters, || {
            let sig = slh_sign(
                black_box(&params),
                black_box(msg),
                black_box(ctx),
                black_box(&q_sk),
                None,
            )
            .unwrap();
            black_box(sig);
        });
        let (u_sg_med, _) = measure_us(sign_warm, $sign_iters, || {
            let sig = u_sk
                .try_sign(black_box(msg), black_box(ctx), black_box(false))
                .unwrap();
            black_box(sig);
        });

        let ver_warm = ($ver_iters / 4).max(2);
        let (q_vr_med, _) = measure_us(ver_warm, $ver_iters, || {
            let ok = slh_verify(
                black_box(&params),
                black_box(msg),
                black_box(&q_sig),
                black_box(ctx),
                black_box(&q_pk),
            );
            assert!(black_box(ok));
        });
        let (u_vr_med, _) = measure_us(ver_warm, $ver_iters, || {
            let ok = u_pk.verify(black_box(msg), black_box(&u_sig), black_box(ctx));
            assert!(black_box(ok));
        });

        println!(
            "| {:<20} | KeyGen | {:>10.1} us | {:>10.1} us | {:>6.2}x |",
            $label,
            q_kg_med,
            u_kg_med,
            u_kg_med / q_kg_med
        );
        println!(
            "| {:<20} | Sign   | {:>10.1} us | {:>10.1} us | {:>6.2}x |",
            $label,
            q_sg_med,
            u_sg_med,
            u_sg_med / q_sg_med
        );
        println!(
            "| {:<20} | Verify | {:>10.1} us | {:>10.1} us | {:>6.2}x |",
            $label,
            q_vr_med,
            u_vr_med,
            u_vr_med / q_vr_med
        );
    }};
}

macro_rules! bench_ml_dsa {
    ($label:expr, $level:expr, $up_mod:ident, $iters:expr) => {{
        let level = $level;
        let params = level.params();
        let xi = [0x42u8; 32];
        let rho = [0x7Au8; 32];
        let msg = b"nist-fips-204-simd-benchmark-payload-bytes";
        let ctx = b"bench-ctx";

        let (q_pk_bytes, q_sk) = ml_dsa_keygen_from_seed(level, &xi);
        let (u_pk, u_sk) = $up_mod::KG::keygen_from_seed(&xi);
        let u_pk_bytes = u_pk.clone().into_bytes();
        assert_eq!(q_pk_bytes.as_slice(), u_pk_bytes.as_slice());

        let q_sig = ml_dsa_sign_deterministic(&q_sk, msg, ctx).expect("qsag sign");
        let u_sig = u_sk
            .try_sign_with_seed(&[0u8; 32], msg, ctx)
            .expect("upstream sign");
        assert_eq!(q_sig.as_slice(), u_sig.as_slice());
        assert!(ml_dsa_verify(level, &q_pk_bytes, msg, ctx, &q_sig));
        assert!(u_pk.verify(msg, &u_sig, ctx));

        let warm = ($iters / 4).max(10);
        let (q_ea_med, _) = measure_us(warm, $iters, || {
            let mat = expand_a_ntt(black_box(&params), black_box(&rho));
            black_box(mat);
        });

        let (q_kg_med, _) = measure_us(warm, $iters, || {
            let res = ml_dsa_keygen_from_seed(black_box(level), black_box(&xi));
            black_box(res);
        });
        let (u_kg_med, _) = measure_us(warm, $iters, || {
            let res = $up_mod::KG::keygen_from_seed(black_box(&xi));
            black_box(res);
        });

        let (q_sg_med, _) = measure_us(warm, $iters, || {
            let sig = ml_dsa_sign_deterministic(black_box(&q_sk), black_box(msg), black_box(ctx))
                .unwrap();
            black_box(sig);
        });
        let (u_sg_med, _) = measure_us(warm, $iters, || {
            let sig = u_sk
                .try_sign_with_seed(black_box(&[0u8; 32]), black_box(msg), black_box(ctx))
                .unwrap();
            black_box(sig);
        });

        // Wire-bytes verification (`pkDecode` + `ExpandA` + `Verify`, matching FIPS 204 Alg 8):
        let (q_vr_wire_med, _) = measure_us(warm, $iters, || {
            let ok = ml_dsa_verify(
                black_box(level),
                black_box(&q_pk_bytes),
                black_box(msg),
                black_box(ctx),
                black_box(&q_sig),
            );
            assert!(black_box(ok));
        });
        let (u_vr_wire_med, _) = measure_us(warm, $iters, || {
            let pk_parsed = $up_mod::PublicKey::try_from_bytes(black_box(u_pk_bytes)).unwrap();
            let ok = pk_parsed.verify(black_box(msg), black_box(&u_sig), black_box(ctx));
            assert!(black_box(ok));
        });
        let (u_vr_cached_med, _) = measure_us(warm, $iters, || {
            let ok = u_pk.verify(black_box(msg), black_box(&u_sig), black_box(ctx));
            assert!(black_box(ok));
        });

        println!(
            "| {:<12} | ExpandA      | {:>8.2} us | {:>11} | {:>7} |",
            $label, q_ea_med, "-", "-"
        );
        println!(
            "| {:<12} | KeyGen       | {:>8.2} us | {:>8.2} us | {:>6.2}x |",
            $label,
            q_kg_med,
            u_kg_med,
            u_kg_med / q_kg_med
        );
        println!(
            "| {:<12} | Sign (det)   | {:>8.2} us | {:>8.2} us | {:>6.2}x |",
            $label,
            q_sg_med,
            u_sg_med,
            u_sg_med / q_sg_med
        );
        println!(
            "| {:<12} | Verify(wire) | {:>8.2} us | {:>8.2} us | {:>6.2}x |",
            $label,
            q_vr_wire_med,
            u_vr_wire_med,
            u_vr_wire_med / q_vr_wire_med
        );
        println!(
            "| {:<12} | Verify(pre)  | {:>8.2} us | {:>8.2} us | {:>6.2}x |",
            $label,
            q_vr_wire_med,
            u_vr_cached_med,
            u_vr_cached_med / q_vr_wire_med
        );
    }};
}

fn main() {
    println!("Detected SIMD backend: {:?}", detect_backend());
    println!();
    println!("=== NIST FIPS 205 (SLH-DSA-SHAKE): QSAG vs Upstream `fips205` (v0.4) ===");
    println!("| Parameter Set        | Op     |       QSAG    |   Upstream    | Speedup |");
    println!("|----------------------|--------|---------------|---------------|---------|");
    bench_slh_dsa!(
        "SLH-DSA-SHAKE-128f",
        Fips205Params::SLH_DSA_SHAKE_128F,
        slh_dsa_shake_128f,
        16,
        40,
        20,
        100
    );
    bench_slh_dsa!(
        "SLH-DSA-SHAKE-192f",
        Fips205Params::SLH_DSA_SHAKE_192F,
        slh_dsa_shake_192f,
        24,
        30,
        12,
        60
    );
    bench_slh_dsa!(
        "SLH-DSA-SHAKE-256f",
        Fips205Params::SLH_DSA_SHAKE_256F,
        slh_dsa_shake_256f,
        32,
        16,
        8,
        50
    );
    bench_slh_dsa!(
        "SLH-DSA-SHAKE-128s",
        Fips205Params::SLH_DSA_SHAKE_128S,
        slh_dsa_shake_128s,
        16,
        5,
        3,
        100
    );
    bench_slh_dsa!(
        "SLH-DSA-SHAKE-256s",
        Fips205Params::SLH_DSA_SHAKE_256S,
        slh_dsa_shake_256s,
        32,
        3,
        2,
        80
    );

    println!();
    println!("=== NIST FIPS 204 (ML-DSA): QSAG vs Upstream `fips204` (v0.4) ===");
    println!("| Level        | Op           |     QSAG    |  Upstream   | Speedup |");
    println!("|--------------|--------------|-------------|-------------|---------|");
    bench_ml_dsa!("ML-DSA-44", MlDsaLevel::MlDsa44, ml_dsa_44, 500);
    bench_ml_dsa!("ML-DSA-65", MlDsaLevel::MlDsa65, ml_dsa_65, 500);
    bench_ml_dsa!("ML-DSA-87", MlDsaLevel::MlDsa87, ml_dsa_87, 500);

    println!();
    println!("=== ML-DSA 256-Point NTT / InvNTT Microbenchmark (1000 calls per sample) ===");
    let mut poly = [0u32; MLDSA_N];
    for (i, slot) in poly.iter_mut().enumerate() {
        *slot = ((i as u32) * 31_337) % MLDSA_Q;
    }
    let mut poly_ref = Poly256 { coeffs: poly };
    let (ntt_disp_us, _) = measure_us(20, 100, || {
        for _ in 0..1000 {
            mldsa_ntt(black_box(&mut poly));
        }
    });
    let (inv_disp_us, _) = measure_us(20, 100, || {
        for _ in 0..1000 {
            mldsa_inv_ntt(black_box(&mut poly));
        }
    });
    let (ntt_port_us, _) = measure_us(20, 100, || {
        for _ in 0..1000 {
            mldsa_ntt_with_backend(black_box(&mut poly), SimdBackend::Portable);
        }
    });
    let (ntt_scalar_us, _) = measure_us(10, 50, || {
        for _ in 0..1000 {
            poly_ref.ntt_scalar_ref();
            black_box(&poly_ref);
        }
    });
    println!(
        "NTT (dispatched SIMD): {:.3} ns/call | InvNTT (dispatched SIMD): {:.3} ns/call | Portable Seiler: {:.3} ns/call | Scalar Barrett ref: {:.3} ns/call ({:.2}x)",
        ntt_disp_us,
        inv_disp_us,
        ntt_port_us,
        ntt_scalar_us,
        ntt_scalar_us / ntt_disp_us
    );
}
