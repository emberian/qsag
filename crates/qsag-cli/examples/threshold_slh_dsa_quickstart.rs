#![deny(clippy::unwrap_used, clippy::expect_used)]
//! Quickstart: Threshold NIST FIPS 205 `SLH-DSA-SHAKE-128f` Signing, Verification & Dynamic Reshare.
//!
//! Run (from workspace root once placed in `crates/qsag-cli/examples/`):
//! ```bash
//! cargo run --release -p qsag-cli --example threshold_slh_dsa_quickstart
//! ```
//!
//! Fixed seeds below are for this reproducible demonstration only, never deployment.
//! Full Ring-LWE bootstrap and SPDZ root checks can be expensive.
//!
//! Demonstrates three end-to-end threshold hash-signature workflows using `qsag-core`:
//! 1. **Full NIST `SLH-DSA-SHAKE-128f` (`17,088 B`) Threshold Sign & Stock Verify (`2-of-3` RSS):**
//!    Dealerless 2-of-3 RSS DKG (`run_dealerless_rss_dkg_2of3`), distributed MPC root keygen
//!    (`slh_keygen_mpc`), distributed pure FIPS 205 threshold signing (`slh_sign_mpc`), stock
//!    unmodified `slh_verify`, and RFC 9814 SPKI DER public-key roundtrip (`50 B`).
//! 2. **Dishonest-Majority `(3, 4)` Shamir DKG + SPDZ Authenticated `PRF_msg` Oracle:**
//!    2-round commit-then-open `TowerGf256` DKG (`run_dealerless_dkg_seed32_gf256`), 2-lane
//!    `Tower128` SPDZ MAC setup, KOS/MASCOT Boolean triple preprocessing (`600` 64-bit words),
//!    and `SpdzSlhMpcCluster::eval_prf_msg_mpc` (`SlhMpcOracles`).
//! 3. **Dynamic Quorum Redistribution `(3, 4) -> (4, 6)` (`Π_reshare`):**
//!    Authorized 3-party quorum reshares `(sk_seed, sk_prf)` directly to a disjoint 6-party
//!    committee (`run_dealerless_reshare_seed32_gf256_with_mesh_root`), volatile-wiping all old shares in place
//!    (`!share.is_valid()`) while preserving bit-identical `PRF_msg` output `R` under the new
//!    4-of-6 quorum with zero secret reconstruction.

use qsag_core::dkg::{
    DkgError, ShamirSeedShare256, run_dealerless_dkg_seed32_gf256,
    run_dealerless_reshare_seed32_gf256_with_mesh_root,
};
use qsag_core::field::tower::TowerGf256;
use qsag_core::fips205::{
    Fips205Params, SlhMpcOracles, SlhPublicKey, format_pure_m_prime, slh_keygen_mpc, slh_sign_mpc,
    slh_verify,
};
use qsag_core::keccak_mpc::{
    RssSlhMpcCluster, SpdzSlhMpcCluster, authenticate_dkg_seed_shares_for_spdz,
    run_dealerless_rss_dkg_2of3,
};
use qsag_core::preprocessing::{
    OtMesh, PCG_DEFAULT_TREE_DEPTH, PartyPrivateRng, run_dealerless_pcg_keccak_vaults_with_alpha,
    spdz_setup_alpha_gf256,
};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let started = std::time::Instant::now();
    let mut last_lap = started;
    let mut lap = |label: &str| {
        let now = std::time::Instant::now();
        eprintln!("  [{label}] {:?}", now - last_lap);
        last_lap = now;
    };
    // The RSS demonstration is independent of the Shamir committees. Run both
    // workflows concurrently; the total below includes joining the RSS result.
    std::thread::scope(|scope| -> Result<(), Box<dyn std::error::Error>> {
        let rss = scope.spawn(|| run_rss_example().map_err(|e| e.to_string()));
        let params = Fips205Params::SLH_DSA_SHAKE_128F;
        let msg = b"Transfer 250,000 QSAG from treasury vault #7";
        let ctx = b"qsag:treasury:v1";
        let stage2_started = std::time::Instant::now();
        println!("\n=== Stage 2: Dishonest-Majority (3, 4) Shamir DKG + SPDZ MPC ===");
        let (old_t, old_n) = (3usize, 4usize);
        let old_pts: Vec<TowerGf256> = (1..=old_n as u8).map(TowerGf256).collect();
        let mut old_rngs: Vec<PartyPrivateRng> = (0..old_n)
            .map(|i| PartyPrivateRng::from_seed([0x70 + i as u8; 32], b"example.spdz.old"))
            .collect();
        let mut old_mesh = OtMesh::try_establish([0xB0; 32], &mut old_rngs)?;
        eprintln!("Old committee bootstrap: {:?}", started.elapsed());
        lap("old mesh");

        // 2-round dealerless Shamir DKG over GF(2^8) with SPDZ Booleanity check for (sk_seed, sk_prf).
        let (mut sk_seed_old, shared_pk_seed32) = run_dealerless_dkg_seed32_gf256(
            [0xB1; 32],
            old_t,
            &old_pts,
            &mut old_mesh,
            &mut old_rngs,
        )?;
        let (mut sk_prf_old, _) = run_dealerless_dkg_seed32_gf256(
            [0xB2; 32],
            old_t,
            &old_pts,
            &mut old_mesh,
            &mut old_rngs,
        )?;
        lap("two seed DKGs");

        // Authenticate DKG shares under a fresh 2-lane Tower128 SPDZ MAC key and request
        // exactly 600 Boolean triple words for one PRF permutation. The compatibility
        // entrypoint currently uses KOS/MASCOT with full active sacrifice checks.
        let (alpha_c, alpha_sh) =
            spdz_setup_alpha_gf256(&[0xB3; 32], old_t, &old_pts, &mut old_rngs)?;
        let auth_keys_old = authenticate_dkg_seed_shares_for_spdz(
            &[0xB4; 32],
            old_t,
            &old_pts,
            params.n,
            shared_pk_seed32,
            &sk_seed_old,
            &sk_prf_old,
            &alpha_c,
            &alpha_sh,
            &mut old_mesh,
            &mut old_rngs,
        )?;
        lap("MAC key + key-share authentication");
        let mut vaults_old = run_dealerless_pcg_keccak_vaults_with_alpha(
            [0xB5; 32],
            old_t,
            &old_pts,
            PCG_DEFAULT_TREE_DEPTH,
            600,
            &alpha_c,
            &alpha_sh,
            &mut old_mesh,
            &mut old_rngs,
        )?;
        lap("600-word triple vault (3, 4)");

        // Signer quorum {0, 1, 2} evaluates R = PRF_msg([SK.prf], opt_rand, M') with pre-cut MacCheck.
        let m_prime = format_pure_m_prime(msg, ctx)?;
        let opt_rand = &shared_pk_seed32[..params.n];
        let r_before = {
            let mut spdz_old = SpdzSlhMpcCluster::new(
                [0xB6; 32],
                old_t,
                &auth_keys_old[..old_t],
                &mut vaults_old[..old_t],
                &mut old_rngs[..old_t],
            )?;
            let (r_block, _mac_tok) = spdz_old.eval_prf_msg_mpc(params.n, opt_rand, &m_prime)?;
            r_block
        };
        println!(
            "  [ok] (3, 4) SPDZ quorum {{0,1,2}} evaluated 16-byte PRF_msg R = {:02x?}",
            &r_before.as_slice()[..8]
        );

        eprintln!("Stage 2 elapsed: {:?}", stage2_started.elapsed());
        lap("PRF_msg under SPDZ");
        let stage3_started = std::time::Instant::now();
        println!("\n=== Stage 3: Dynamic Reshare (3, 4) -> (4, 6) & Old-Share Wipe ===");
        let (new_t, new_n) = (4usize, 6usize);
        let new_pts: Vec<TowerGf256> = (11..11 + new_n as u8).map(TowerGf256).collect();
        let old_quorum = [0usize, 2, 3]; // Authorized 3-party subset of old committee
        let mut quorum_rngs: Vec<PartyPrivateRng> = (0..old_t)
            .map(|i| PartyPrivateRng::from_seed([0x90 + i as u8; 32], b"example.reshare.old"))
            .collect();
        let mut new_rngs: Vec<PartyPrivateRng> = (0..new_n)
            .map(|i| PartyPrivateRng::from_seed([0xC0 + i as u8; 32], b"example.reshare.new"))
            .collect();
        let mut new_mesh = OtMesh::try_establish([0xD0; 32], &mut new_rngs)?;
        eprintln!("New committee bootstrap: {:?}", started.elapsed());
        lap("new mesh");

        // Enroll both 256-bit seed commitments before redistribution. Each commitment
        // evaluates a secret-keyed 32-byte SPDZ MPC PRF under full dishonest-majority
        // MAC authentication without reconstructing either seed.
        let seed_root = custody_root(
            &sk_seed_old,
            old_t,
            &old_pts,
            shared_pk_seed32,
            0xE0,
            &mut old_mesh,
        )?;
        let prf_root = custody_root(
            &sk_prf_old,
            old_t,
            &old_pts,
            shared_pk_seed32,
            0xE1,
            &mut old_mesh,
        )?;
        lap("two custody roots (3, 4)");
        let sk_seed_new = run_dealerless_reshare_seed32_gf256_with_mesh_root(
            [0xD1; 32],
            old_t,
            &old_quorum,
            &mut sk_seed_old,
            new_t,
            &new_pts,
            &mut new_mesh,
            &mut quorum_rngs,
            &mut new_rngs,
            &seed_root,
            |shares, root_mesh| {
                custody_root(shares, new_t, &new_pts, shared_pk_seed32, 0xE2, root_mesh)
                    .map_err(|_| DkgError::PublicRootMismatch)
            },
        )?;
        let sk_prf_new = run_dealerless_reshare_seed32_gf256_with_mesh_root(
            [0xD2; 32],
            old_t,
            &old_quorum,
            &mut sk_prf_old,
            new_t,
            &new_pts,
            &mut new_mesh,
            &mut quorum_rngs,
            &mut new_rngs,
            &prf_root,
            |shares, root_mesh| {
                custody_root(shares, new_t, &new_pts, shared_pk_seed32, 0xE3, root_mesh)
                    .map_err(|_| DkgError::PublicRootMismatch)
            },
        )?;

        // Every old committee share is volatile-wiped and permanently invalidated!
        lap("two reshares with (4, 6) custody roots");
        assert!(sk_seed_old.iter().all(|s| !s.is_valid()));
        assert!(sk_prf_old.iter().all(|s| !s.is_valid()));
        assert!(sk_seed_new.iter().all(|s| s.is_valid()));

        // Verify the new (4, 6) committee evaluates the exact same secret-keyed R = PRF_msg(...)!
        let (alpha_c2, alpha_sh2) =
            spdz_setup_alpha_gf256(&[0xD3; 32], new_t, &new_pts, &mut new_rngs)?;
        let auth_keys_new = authenticate_dkg_seed_shares_for_spdz(
            &[0xD4; 32],
            new_t,
            &new_pts,
            params.n,
            shared_pk_seed32,
            &sk_seed_new,
            &sk_prf_new,
            &alpha_c2,
            &alpha_sh2,
            &mut new_mesh,
            &mut new_rngs,
        )?;
        lap("MAC key + key-share authentication");
        let mut vaults_new = run_dealerless_pcg_keccak_vaults_with_alpha(
            [0xD5; 32],
            new_t,
            &new_pts,
            PCG_DEFAULT_TREE_DEPTH,
            600,
            &alpha_c2,
            &alpha_sh2,
            &mut new_mesh,
            &mut new_rngs,
        )?;
        lap("600-word triple vault (4, 6)");

        let r_after = {
            let mut spdz_new = SpdzSlhMpcCluster::new(
                [0xD6; 32],
                new_t,
                &auth_keys_new[1..1 + new_t], // 4-party quorum {1, 2, 3, 4}
                &mut vaults_new[1..1 + new_t],
                &mut new_rngs[1..1 + new_t],
            )?;
            let (r_block, _mac_tok) = spdz_new.eval_prf_msg_mpc(params.n, opt_rand, &m_prime)?;
            r_block
        };
        assert_eq!(
            r_before.as_slice(),
            r_after.as_slice(),
            "reshared (4, 6) quorum must preserve exact secret key without reconstruction"
        );
        println!(
            "  [ok] (3, 4) -> (4, 6) reshare wiped all 4 old shares and matched R bit-for-bit!"
        );
        lap("PRF_msg under SPDZ");
        eprintln!("Stage 3 elapsed: {:?}", stage3_started.elapsed());
        rss.join()
            .map_err(|_| std::io::Error::other("RSS worker panicked"))?
            .map_err(std::io::Error::other)?;
        eprintln!("Total: {:?}", started.elapsed());
        Ok(())
    })
}

fn run_rss_example() -> Result<(), Box<dyn std::error::Error>> {
    let started = std::time::Instant::now();
    println!("=== Stage 1: Full NIST SLH-DSA-SHAKE-128f (2-of-3 RSS MPC) ===");
    let params = Fips205Params::SLH_DSA_SHAKE_128F;
    let msg = b"Transfer 250,000 QSAG from treasury vault #7";
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

/// Recompute a 256-bit public custody commitment over all 32 bytes of `shares` without
/// reconstructing the seed. Independent sessions and fresh OS entropy isolate these check
/// ceremonies; existing OT channels advance their batch counters so base OTs never repeat.
fn custody_root(
    shares: &[ShamirSeedShare256],
    threshold: usize,
    points: &[TowerGf256],
    pk_seed: [u8; 32],
    label: u8,
    mesh: &mut OtMesh,
) -> Result<[u8; 32], Box<dyn std::error::Error>> {
    let started = std::time::Instant::now();
    let mut rngs = (0..points.len())
        .map(|_| PartyPrivateRng::from_os_rng(b"example.custody.root"))
        .collect::<Result<Vec<_>, _>>()?;
    let (alpha, alpha_shares) = spdz_setup_alpha_gf256(&[label; 32], threshold, points, &mut rngs)?;
    // Bind all 32 bytes (`256` bits) of `shares` under 2-lane `Tower128` SPDZ MACs and evaluate
    // `SHAKE256(seed_32 || pk_seed_32 || "QSAG.SLH.CUSTODY.ROOT/v1")[..32]` inside MPC.
    let keys = authenticate_dkg_seed_shares_for_spdz(
        &[label; 32],
        threshold,
        points,
        32,
        pk_seed,
        shares,
        shares,
        &alpha,
        &alpha_shares,
        mesh,
        &mut rngs,
    )?;
    let authenticated = started.elapsed();
    // One `Keccak-f[1600]` permutation consumes `600` 64-way Boolean triple words.
    let mut vaults = run_dealerless_pcg_keccak_vaults_with_alpha(
        [label; 32],
        threshold,
        points,
        PCG_DEFAULT_TREE_DEPTH,
        600,
        &alpha,
        &alpha_shares,
        mesh,
        &mut rngs,
    )?;
    let preprocessed = started.elapsed();
    let mut cluster = SpdzSlhMpcCluster::new(
        [label; 32],
        threshold,
        &keys[..threshold],
        &mut vaults[..threshold],
        &mut rngs[..threshold],
    )?;
    let (blk, _mac_tok) = cluster.eval_prf_msg_mpc(32, &pk_seed, b"QSAG.SLH.CUSTODY.ROOT/v1")?;
    eprintln!(
        "    custody root: authenticate {:?}, triples {:?}, evaluate {:?}",
        authenticated,
        preprocessed - authenticated,
        started.elapsed() - preprocessed
    );
    let mut root = [0u8; 32];
    root.copy_from_slice(blk.as_slice());
    Ok(root)
}
