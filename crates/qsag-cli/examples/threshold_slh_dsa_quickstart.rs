#![deny(clippy::unwrap_used, clippy::expect_used)]
//! Threshold FIPS 205 SLH-DSA-SHAKE-128f: 2-of-3 RSS, and optionally 3-of-5 zero-coordinator CNF.
//!
//! Run: `cargo run --release -p qsag-cli --example threshold_slh_dsa_quickstart --locked`
//!
//! The default run is the 2-of-3 workflow (a few seconds): dealerless key
//! generation, a full 17,088-byte signature, stock verification, tampered-message
//! rejection, and an RFC 9814 SPKI roundtrip.
//!
//! Pass `-- --cnf-rss-3of5` to also run the zero-coordinator 3-of-5 [`IsolatedCnfParty`]
//! ceremony over encrypted `MacSealedWireChannel` endpoints (`f = 2` corruptions tolerated;
//! each custodian runs in its own isolated thread and holds only its own CNF slot shares).
//!
//! Fixed seeds are reproducible demonstration inputs, never deployment entropy.

use std::time::Duration;

use qsag_core::cnf_rss::{CnfRssConfig, run_dealerless_cnf_rss_dkg};
use qsag_core::fips205::{Fips205Params, SlhPublicKey, slh_keygen_mpc, slh_sign_mpc, slh_verify};
use qsag_core::keccak_mpc::{RssSlhMpcCluster, run_dealerless_rss_dkg_2of3};
use qsag_core::preprocessing::PartyPrivateRng;
use qsag_quorum::cnf_party::{CnfPartyKeys, IsolatedCnfParty, run_isolated_cnf_ceremony};
use qsag_quorum::party_node::{NodeError, PoisonJournal};
use qsag_quorum::wire_channel::InMemoryWireMesh;

#[derive(Default)]
struct DemoPoisonJournal {
    reserved: Vec<[u8; 32]>,
    poisoned: Vec<[u8; 32]>,
}

impl PoisonJournal for DemoPoisonJournal {
    fn reserve_session(&mut self, session_id: &[u8; 32]) -> Result<(), NodeError> {
        if self.reserved.contains(session_id) || self.poisoned.contains(session_id) {
            return Err(NodeError::Journal);
        }
        self.reserved.push(*session_id);
        Ok(())
    }

    fn mark_poisoned(&mut self, session_id: &[u8; 32]) -> Result<(), NodeError> {
        if !self.poisoned.contains(session_id) {
            self.poisoned.push(*session_id);
        }
        Ok(())
    }

    fn is_poisoned(&self, session_id: &[u8; 32]) -> bool {
        self.poisoned.contains(session_id)
    }
}

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
            "\n(3-of-5 isolated CNF stage skipped; rerun with `-- --cnf-rss-3of5`)"
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
        .map(|i| PartyPrivateRng::from_seed([seed.wrapping_add(i as u8); 32], b"example.cnf-rss"))
        .collect()
}

fn run_cnf_example() -> Result<(), Box<dyn std::error::Error>> {
    let started = std::time::Instant::now();
    println!(
        "\n=== Stage 2: Full NIST SLH-DSA-SHAKE-128f (3-of-5 IsolatedCnfParty zero-coordinator MPC) ==="
    );
    let params = Fips205Params::SLH_DSA_SHAKE_128F;
    let config = CnfRssConfig::new(3, 5)?;
    let (shares, pk_seed) =
        run_dealerless_cnf_rss_dkg([0xC1; 32], &config, params.n, &mut demo_rngs(5, 0x80))?;
    let mut keys: Vec<CnfPartyKeys> = shares
        .iter()
        .map(CnfPartyKeys::from_custody)
        .collect::<Result<_, _>>()
        .map_err(|e| format!("loading CNF custodian keys failed: {e:?}"))?;

    let kg_session = [0xC2; 32];
    let (kg_endpoints, _) = InMemoryWireMesh::connect(5, kg_session);
    let kg_parties = kg_endpoints
        .into_iter()
        .zip(&keys)
        .enumerate()
        .map(|(p, (mut ep, key))| {
            ep.set_timeout(Duration::from_secs(600));
            IsolatedCnfParty::new(
                key,
                ep,
                kg_session,
                &[0x90u8.wrapping_add(p as u8); 32],
                DemoPoisonJournal::default(),
            )
            .map_err(|e| format!("constructing keygen party {p} failed: {e:?}"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let pks = run_isolated_cnf_ceremony(kg_parties, |_, party| party.slh_keygen(&params));
    let pk = pks
        .into_iter()
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .next()
        .ok_or("missing keygen output")?;

    for key in &mut keys {
        key.bind_slh_params(&params, &pk_seed[..params.n])
            .map_err(|e| format!("binding SLH parameters failed: {e:?}"))?;
    }
    eprintln!("Isolated CNF DKG + root: {:?}", started.elapsed());

    let msg = b"Transfer 250,000 units from treasury vault #7";
    let ctx = b"qsag:treasury:v1";
    let sign_session = [0xC3; 32];
    let (sign_endpoints, _) = InMemoryWireMesh::connect(5, sign_session);
    let sign_parties = sign_endpoints
        .into_iter()
        .zip(&keys)
        .enumerate()
        .map(|(p, (mut ep, key))| {
            ep.set_timeout(Duration::from_secs(600));
            IsolatedCnfParty::new(
                key,
                ep,
                sign_session,
                &[0xA0u8.wrapping_add(p as u8); 32],
                DemoPoisonJournal::default(),
            )
            .map_err(|e| format!("constructing signing party {p} failed: {e:?}"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let sigs = run_isolated_cnf_ceremony(sign_parties, |_, party| {
        party.slh_sign(&params, msg, ctx, &pk, None)
    });
    let sig_vec = sigs.into_iter().collect::<Result<Vec<_>, _>>()?;
    let sig = sig_vec
        .first()
        .ok_or("missing signing output")?
        .clone();
    for peer_sig in &sig_vec[1..] {
        assert_eq!(peer_sig, &sig);
    }

    assert_eq!(sig.len(), params.sig_bytes());
    assert!(slh_verify(&params, msg, &sig, ctx, &pk));
    assert!(!slh_verify(&params, b"tampered payload", &sig, ctx, &pk));
    let spki = pk.to_spki_der(&params)?;
    assert_eq!(SlhPublicKey::from_spki_der(&spki)?, (params, pk));
    println!(
        "  [ok] 3-of-5 IsolatedCnfParty ceremony: {} B signature, {} B SPKI",
        sig.len(),
        spki.len()
    );
    eprintln!("Stage 2 elapsed: {:?}", started.elapsed());
    Ok(())
}
