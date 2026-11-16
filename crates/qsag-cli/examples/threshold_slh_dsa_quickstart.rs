#![deny(clippy::unwrap_used, clippy::expect_used)]
//! Threshold FIPS 205 SLH-DSA-SHAKE-128f: 2-of-3 RSS, and optionally 3-of-5 CNF-RSS.
//!
//! Run: `cargo run --release -p qsag-cli --example threshold_slh_dsa_quickstart --locked`
//!
//! The default run is the 2-of-3 workflow (a few seconds): dealerless key
//! generation, a full 17,088-byte signature, stock verification, tampered-message
//! rejection, and an RFC 9814 SPKI roundtrip.
//!
//! Pass `-- --cnf-rss-3of5` to also run the same workflow for a 3-of-5 quorum that
//! changes its online members between keygen and signing. That stage takes about
//! eight minutes: it evaluates all 22 hypertree layers over projected CNF-RSS
//! correlations. CNF-RSS currently uses a trusted coordinator holding all shares;
//! the stage does not demonstrate privacy against that coordinator or isolated
//! custodians.
//!
//! Fixed seeds are reproducible demonstration inputs, never deployment entropy.

use qsag_core::cnf_rss::{
    CnfRssConfig, CnfRssProjectedEngine, StreamingCnfRssSource, run_dealerless_cnf_rss_dkg,
};
use qsag_core::fips205::{Fips205Params, SlhPublicKey, slh_keygen_mpc, slh_sign_mpc, slh_verify};
use qsag_core::keccak_mpc::{RssSlhMpcCluster, run_dealerless_rss_dkg_2of3};
use qsag_core::preprocessing::PartyPrivateRng;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cnf_rss = match std::env::args().nth(1).as_deref() {
        None => false,
        Some("--cnf-rss-3of5") => true,
        Some(other) => {
            return Err(format!("unknown argument {other:?}; expected --cnf-rss-3of5").into());
        }
    };
    let started = std::time::Instant::now();
    run_rss_example()?;
    if cnf_rss {
        run_cnf_example()?;
    } else {
        println!(
            "\n(3-of-5 CNF-RSS stage skipped; rerun with `-- --cnf-rss-3of5`, about 8 minutes)"
        );
    }
    println!("Total: {:?}", started.elapsed());
    Ok(())
}

fn run_rss_example() -> Result<(), Box<dyn std::error::Error>> {
    let started = std::time::Instant::now();
    println!("=== Stage 1: Full NIST SLH-DSA-SHAKE-128f (2-of-3 RSS MPC) ===");
    let params = Fips205Params::SLH_DSA_SHAKE_128F;
    let msg = b"Transfer 250,000 units from treasury vault #7";
    let ctx = b"qsag:treasury:v1";

    let mut rss_dkg_rngs = [
        PartyPrivateRng::from_seed([0x11; 32], b"example.rss.dkg.p0"),
        PartyPrivateRng::from_seed([0x22; 32], b"example.rss.dkg.p1"),
        PartyPrivateRng::from_seed([0x33; 32], b"example.rss.dkg.p2"),
    ];
    let (rss_keys, pk_seed_full) =
        run_dealerless_rss_dkg_2of3([0xA0; 32], params.n, &mut rss_dkg_rngs)?;

    let rss_sign_rngs = [
        PartyPrivateRng::from_seed([0x44; 32], b"example.rss.sign.p0"),
        PartyPrivateRng::from_seed([0x55; 32], b"example.rss.sign.p1"),
        PartyPrivateRng::from_seed([0x66; 32], b"example.rss.sign.p2"),
    ];
    let mut rss_cluster = RssSlhMpcCluster::new([0xA1; 32], rss_keys, rss_sign_rngs)?;

    eprintln!("RSS DKG: {:?}", started.elapsed());
    let pk = slh_keygen_mpc(&params, &mut rss_cluster, &pk_seed_full[..params.n])?;
    eprintln!("RSS root: {:?}", started.elapsed());
    let sig = slh_sign_mpc(&params, &mut rss_cluster, msg, ctx, &pk, None)?;

    assert_eq!(sig.len(), params.sig_bytes()); // 17,088 bytes
    assert!(
        slh_verify(&params, msg, &sig, ctx, &pk),
        "stock FIPS 205 verifier must accept threshold signature"
    );
    assert!(
        !slh_verify(&params, b"tampered payload", &sig, ctx, &pk),
        "tampered message must be rejected"
    );

    let spki_der = pk.to_spki_der(&params)?;
    let (decoded_params, decoded_pk) = SlhPublicKey::from_spki_der(&spki_der)?;
    assert_eq!(decoded_params, params);
    assert_eq!(decoded_pk, pk);
    println!(
        "  [ok] SLH-DSA-SHAKE-128f pk={} B (SPKI={} B), sig={} B verified by stock slh_verify",
        pk.to_bytes().len(),
        spki_der.len(),
        sig.len(),
    );

    eprintln!("Stage 1 elapsed: {:?}", started.elapsed());
    Ok(())
}

fn demo_rngs(count: usize, seed: u8) -> Vec<PartyPrivateRng> {
    (0..count)
        .map(|i| PartyPrivateRng::from_seed([seed + i as u8; 32], b"example.cnf-rss"))
        .collect()
}

fn run_cnf_example() -> Result<(), Box<dyn std::error::Error>> {
    let started = std::time::Instant::now();
    println!(
        "\n=== Stage 2: Full NIST SLH-DSA-SHAKE-128f (3-of-5 CNF-RSS coordinator prototype) ==="
    );
    let params = Fips205Params::SLH_DSA_SHAKE_128F;
    let config = CnfRssConfig::new(3, 5)?;
    let (mut shares, pk_seed) =
        run_dealerless_cnf_rss_dkg([0xC1; 32], &config, params.n, &mut demo_rngs(5, 0x80))?;
    let pk = {
        let session = [0xC2; 32];
        let mut source = StreamingCnfRssSource::establish(session, &config, &shares, &[0, 1, 2])?;
        let [s0, s1, s2, _, _] = shares.as_mut_slice() else {
            return Err(std::io::Error::other("expected five custodian shares").into());
        };
        let mut rngs = demo_rngs(3, 0x90);
        let mut engine =
            CnfRssProjectedEngine::new(session, vec![s0, s1, s2], &mut rngs, &mut source)?;
        slh_keygen_mpc(&params, &mut engine, &pk_seed[..params.n])?
    };
    for share in &mut shares {
        share.bind_slh_params(&params, &pk_seed[..params.n])?;
    }
    eprintln!("CNF-RSS DKG + root: {:?}", started.elapsed());
    let msg = b"Transfer 250,000 units from treasury vault #7";
    let ctx = b"qsag:treasury:v1";
    let sig = {
        // Only custodians 0, 3, and 4 participate in this signing engine.
        let session = [0xC3; 32];
        let mut source = StreamingCnfRssSource::establish(session, &config, &shares, &[0, 3, 4])?;
        let [s0, _, _, s3, s4] = shares.as_mut_slice() else {
            return Err(std::io::Error::other("expected five custodian shares").into());
        };
        let mut rngs = demo_rngs(3, 0xA0);
        let mut engine =
            CnfRssProjectedEngine::new(session, vec![s0, s3, s4], &mut rngs, &mut source)?;
        slh_sign_mpc(&params, &mut engine, msg, ctx, &pk, None)?
    };
    assert_eq!(sig.len(), params.sig_bytes());
    assert!(slh_verify(&params, msg, &sig, ctx, &pk));
    assert!(!slh_verify(&params, b"tampered payload", &sig, ctx, &pk));
    let spki = pk.to_spki_der(&params)?;
    assert_eq!(SlhPublicKey::from_spki_der(&spki)?, (params, pk));
    println!(
        "  [ok] 3-of-5 quorum {{0,3,4}}: {} B signature, {} B SPKI",
        sig.len(),
        spki.len()
    );
    eprintln!("Stage 2 elapsed: {:?}", started.elapsed());
    Ok(())
}
