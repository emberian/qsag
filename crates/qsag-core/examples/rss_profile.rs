//! Linux release benchmark, using public test fixtures, with reference parity checks.
//! Build with `CARGO_PROFILE_RELEASE_DEBUG=2 cargo build --release -p qsag-core
//! --example rss_profile`, then run `target/release/examples/rss_profile 128f`.
//! Modes: `128f`, `128s`, or `batch` (64 verified Keccak permutations).
//! Add `--sign-only` to use the reference public key and exclude threshold keygen;
//! reference keygen/sign timings are printed separately from threshold timings.
//! For bounded runs, prefix the command with
//! `SWARM_MEM_MAX=12G timeout --kill-after=10s 600s`.
use qsag_core::fips205::{
    Fips205Params, slh_keygen_internal, slh_keygen_mpc, slh_sign, slh_sign_mpc, slh_verify,
};
use qsag_core::keccak_mpc::{
    RssSlhMpcCluster, eval_rss_keccak_f1600_batch64, run_dealerless_rss_dkg_2of3,
};
use qsag_core::preprocessing::PartyPrivateRng;
use std::time::Instant;

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_else(|| "128f".into());
    let sid = [0x51; 32];
    let mut rngs =
        core::array::from_fn(|p| PartyPrivateRng::from_seed([0x20 + p as u8; 32], b"rss-profile"));
    let start = Instant::now();
    let (keys, _) = run_dealerless_rss_dkg_2of3(sid, 16, &mut rngs).unwrap();
    eprintln!("dkg_seconds={:.6}", start.elapsed().as_secs_f64());
    if mode == "batch" {
        let mut primary = [[0u64; 1600]; 3];
        let mut secondary = primary;
        let start = Instant::now();
        eval_rss_keccak_f1600_batch64(&sid, 0, 64, &mut primary, &mut secondary, &keys, &mut rngs)
            .unwrap();
        eprintln!(
            "batch64_verified_seconds={:.6}",
            start.elapsed().as_secs_f64()
        );
        return;
    }
    let params = match mode.as_str() {
        "128f" => Fips205Params::SLH_DSA_SHAKE_128F,
        "128s" => Fips205Params::SLH_DSA_SHAKE_128S,
        _ => panic!("expected 128f, 128s, or batch"),
    };
    let pk_seed = keys[0].pk_seed[..16].to_vec();
    // Reproduce public benchmark RNG inputs; custody shares expose no raw getters.
    let mut seed = [0u8; 16];
    let mut prf = [0u8; 16];
    for mut fixture_rng in core::array::from_fn::<_, 3, _>(|p| {
        PartyPrivateRng::from_seed([0x20 + p as u8; 32], b"rss-profile")
    }) {
        let _ = fixture_rng.next_bytes32();
        let _ = fixture_rng.next_bytes32();
        let mut contribution = [0u8; 16];
        fixture_rng.fill_bytes(&mut contribution);
        for (dst, src) in seed.iter_mut().zip(contribution) {
            *dst ^= src;
        }
        fixture_rng.fill_bytes(&mut contribution);
        for (dst, src) in prf.iter_mut().zip(contribution) {
            *dst ^= src;
        }
    }
    let start = Instant::now();
    let (reference_sk, reference_pk) = slh_keygen_internal(&params, &seed, &prf, &pk_seed).unwrap();
    eprintln!(
        "profile={mode} reference_keygen_seconds={:.6}",
        start.elapsed().as_secs_f64()
    );
    let start = Instant::now();
    let reference_sig = slh_sign(&params, b"benchmark", b"", &reference_sk, None).unwrap();
    eprintln!(
        "profile={mode} reference_sign_seconds={:.6}",
        start.elapsed().as_secs_f64()
    );
    let mut cluster = RssSlhMpcCluster::new(sid, keys, rngs).unwrap();
    let start = Instant::now();
    let pk = if std::env::args().any(|arg| arg == "--sign-only") {
        eprintln!("using reference public key; threshold keygen excluded");
        reference_pk
    } else {
        let pk = slh_keygen_mpc(&params, &mut cluster, &pk_seed).unwrap();
        eprintln!(
            "profile={mode} keygen_seconds={:.6}",
            start.elapsed().as_secs_f64()
        );
        assert_eq!(pk, reference_pk);
        pk
    };
    let start = Instant::now();
    let sig = slh_sign_mpc(&params, &mut cluster, b"benchmark", b"", &pk, None).unwrap();
    eprintln!(
        "profile={mode} sign_seconds={:.6} signature_bytes={}",
        start.elapsed().as_secs_f64(),
        sig.len()
    );
    assert_eq!(sig, reference_sig);
    assert!(slh_verify(&params, b"benchmark", &sig, b"", &pk));
    let mut bad = sig;
    bad[0] ^= 1;
    assert!(!slh_verify(&params, b"benchmark", &bad, b"", &pk));
}
