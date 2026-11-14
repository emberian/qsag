//! Release timing report for the pure-hash threshold suite.
//!
//! Run with `cargo run --release -p qsag-core --example pants_bench`. Pass `--skip-slh` to
//! leave out the (slow) `SLH-DSA-SHAKE-128f` row.
//!
//! What the numbers are:
//! * `one-process` is measured wall time of all three parties simulated on one thread.
//! * `per-party est.` is two thirds of that: a party does the share-local work of two of the
//!   three slots. It is an estimate, not a measurement on separate hosts.
//! * Hops and bytes are counted by the engine ([`qsag_core::rss256::WireStats`]).
//! * `LAN` / `WAN` are a model, not a network run:
//!   `hops * one-way delay + bytes / bandwidth + per-party est.` with 0.25 ms one-way and
//!   10 Gbit/s for LAN, 20 ms one-way (40 ms round trip) and 1 Gbit/s for WAN.
use qsag_core::baggy::{
    BaggyParams, MemoryFirstSigned, WaistbandCache, baggy_keygen_mpc, baggy_sign_mpc, baggy_verify,
};
use qsag_core::belt_latch::MemoryWal;
use qsag_core::fips205::{Fips205Params, slh_keygen_internal, slh_sign, slh_sign_mpc, slh_verify};
use qsag_core::jorts::{JortsParams, JortsSigner, jorts_keygen_mpc, jorts_verify};
use qsag_core::keccak_mpc::{RssSlhMpcCluster, run_dealerless_rss_dkg_2of3};
use qsag_core::preprocessing::PartyPrivateRng;
use qsag_core::rss256::{AndMode, Rss256Engine, WireStats};
use std::time::Instant;

fn rngs(tag: u8) -> [PartyPrivateRng; 3] {
    core::array::from_fn(|p| PartyPrivateRng::from_seed([tag + p as u8; 32], b"pants-bench"))
}

fn engine(tag: u8) -> Rss256Engine {
    let sid = [tag; 32];
    let mut r = rngs(tag);
    let (keys, _) = run_dealerless_rss_dkg_2of3(sid, 32, &mut r).unwrap();
    Rss256Engine::new(sid, keys, r).unwrap()
}

fn delta(after: WireStats, before: WireStats) -> WireStats {
    WireStats {
        perm_levels: after.perm_levels - before.perm_levels,
        lane_perms: after.lane_perms - before.lane_perms,
        and_bytes: after.and_bytes - before.and_bytes,
        checks: after.checks - before.checks,
        cut_checks: after.cut_checks - before.cut_checks,
        check_hops: after.check_hops - before.check_hops,
        check_bytes: after.check_bytes - before.check_bytes,
        open_rounds: after.open_rounds - before.open_rounds,
        open_bytes: after.open_bytes - before.open_bytes,
        staged_lane_perms: after.staged_lane_perms - before.staged_lane_perms,
        staged_bytes: after.staged_bytes - before.staged_bytes,
        staged_state_bytes: after.staged_state_bytes - before.staged_state_bytes,
    }
}

/// Modelled latency in milliseconds for `hops` message hops and `bytes` sent per party.
fn model_ms(hops: u64, bytes: u64, cpu_ms: f64, one_way_ms: f64, gbit: f64) -> f64 {
    hops as f64 * one_way_ms + (bytes as f64 * 8.0) / (gbit * 1e6) + cpu_ms
}

fn row(name: &str, wall_s: f64, hops: u64, bytes: u64, lane_perms: u64, note: &str) {
    let wall_ms = wall_s * 1e3;
    let party_ms = wall_ms * 2.0 / 3.0;
    println!(
        "{name:<34} | one-process {wall_ms:>9.1} ms | per-party est. {party_ms:>9.1} ms | \
         lane-perms {lane_perms:>7} | hops {hops:>4} | wire/party {bytes:>11} B | \
         LAN {:>9.1} ms | WAN {:>10.1} ms | {note}",
        model_ms(hops, bytes, party_ms, 0.25, 10.0),
        model_ms(hops, bytes, party_ms, 20.0, 1.0),
    );
}

fn engine_row(name: &str, wall_s: f64, d: WireStats, note: &str) {
    row(
        name,
        wall_s,
        d.online_hops(),
        d.online_bytes(),
        d.lane_perms,
        note,
    );
}

fn main() {
    let skip_slh = std::env::args().any(|a| a == "--skip-slh");
    println!("backend: {:?}", qsag_asm::detect_backend());

    // ---- Engine microbenchmark -------------------------------------------------------
    {
        use qsag_core::rss256::SharedState256;
        let mut e = engine(0x10);
        let mid = [0u64; 25];
        let frames = vec![[0x5Au8; 136]; 256];
        let t = Instant::now();
        let reps = 8;
        for _ in 0..reps {
            let mut st = SharedState256::from_public_frames(&mid, &frames).unwrap();
            e.permute(&mut st, 256).unwrap();
        }
        let wave_ms = t.elapsed().as_secs_f64() * 1e3 / reps as f64;
        let t = Instant::now();
        e.check().unwrap();
        let check_ms = t.elapsed().as_secs_f64() * 1e3;
        println!(
            "engine: 256-lane permutation {wave_ms:.2} ms one-process ({:.1} us per lane-perm); \
             barrier over {reps} such waves {check_ms:.1} ms",
            wave_ms * 1e3 / 256.0
        );
    }

    // ---- BaggySha3 -------------------------------------------------------------------
    let params = BaggyParams::SHA3_128F;
    let msg = b"pants bench message";
    {
        let mut e = engine(0x20);
        let mut none = WaistbandCache::disabled();
        let t = Instant::now();
        let mut ledger = MemoryFirstSigned::new();
        let (pk, binding) = baggy_keygen_mpc(&mut e, &params, &mut none).unwrap();
        println!(
            "BaggySha3 keygen (top subtree): {:.1} ms one-process",
            t.elapsed().as_secs_f64() * 1e3
        );

        let before = e.stats();
        let t = Instant::now();
        let sig =
            baggy_sign_mpc(&mut e, &params, &pk, &binding, &mut none, &mut ledger, msg).unwrap();
        let wall = t.elapsed().as_secs_f64();
        assert!(baggy_verify(&params, &pk, msg, &sig));
        engine_row(
            "BaggySha3 128f, no Waistband (1B)",
            wall,
            delta(e.stats(), before),
            &format!("sig {} B", params.sig_bytes()),
        );

        for top in [2usize, 3] {
            let mut cache = WaistbandCache::new(top, 1 << 16);
            let before = e.stats();
            let t = Instant::now();
            cache
                .precompute(&mut e, &params, &pk, &binding, &mut ledger)
                .unwrap();
            let pre = t.elapsed().as_secs_f64();
            let pre_stats = delta(e.stats(), before);
            println!(
                "Waistband precompute, top {top} layers: {:.1} ms one-process, {} lane-perms, \
                 {} signatures cached (offline)",
                pre * 1e3,
                pre_stats.lane_perms,
                cache.sig_entries()
            );
            let before = e.stats();
            let t = Instant::now();
            let cached =
                baggy_sign_mpc(&mut e, &params, &pk, &binding, &mut cache, &mut ledger, msg)
                    .unwrap();
            let wall = t.elapsed().as_secs_f64();
            assert_eq!(cached, sig);
            engine_row(
                &format!("BaggySha3 128f, Waistband L={top} (1B)"),
                wall,
                delta(e.stats(), before),
                &format!(
                    "{} of {} layers online",
                    params.num_layers - top,
                    params.num_layers
                ),
            );
        }

        // Mode 1A with the largest cache: stage a single-use bank, then sign.
        let mut cache = WaistbandCache::new(3, 1 << 16);
        cache
            .precompute(&mut e, &params, &pk, &binding, &mut ledger)
            .unwrap();
        // 2 randomiser waves, then the chain lanes of the 13 uncached layers and the FORS
        // lanes over the PRF level and the first F level, and the chain lanes over two more
        // levels.
        let chain_lanes =
            (params.num_layers - 3) * (1usize << params.subtree_height) * params.wots.chains;
        let fors_lanes = params.signed_fors_trees() << params.fors_height;
        let waves =
            2 + 2 * (chain_lanes + fors_lanes).div_ceil(256) + 2 * chain_lanes.div_ceil(256);
        let before = e.stats();
        let t = Instant::now();
        e.stage_beaver_bank(waves).unwrap();
        let stage = t.elapsed().as_secs_f64();
        let staged = delta(e.stats(), before);
        println!(
            "Mode 1A bank for one signature: {waves} waves staged in {:.1} ms one-process, \
             {} B offline wire/party, {} B of triples held per party",
            stage * 1e3,
            staged.staged_bytes,
            staged.staged_state_bytes
        );
        e.set_mode(AndMode::BeaverBank).unwrap();
        let before = e.stats();
        let t = Instant::now();
        let banked =
            baggy_sign_mpc(&mut e, &params, &pk, &binding, &mut cache, &mut ledger, msg).unwrap();
        let wall = t.elapsed().as_secs_f64();
        assert_eq!(banked, sig);
        engine_row(
            "BaggySha3 128f, Waistband L=3 (1A)",
            wall,
            delta(e.stats(), before),
            &format!("bank left: {} planes", e.bank().remaining_planes()),
        );
    }

    // ---- JortsSha3 -------------------------------------------------------------------
    {
        let height = 6;
        let jp = JortsParams::with_height(height);
        let mut e = engine(0x30);
        let before = e.stats();
        let t = Instant::now();
        let key = jorts_keygen_mpc(&mut e, &jp).unwrap();
        let keygen = t.elapsed().as_secs_f64();
        let kd = delta(e.stats(), before);
        let per_lane_perm = keygen / kd.lane_perms as f64;
        println!(
            "JortsSha3 keygen h={height}: {:.1} ms one-process for {} lane-perms; at that rate \
             h=20 needs {:.1} hours one-process (extrapolated, not run)",
            keygen * 1e3,
            kd.lane_perms,
            per_lane_perm * (jp.wots.chains as f64 * 4.0 * (1u64 << 20) as f64) / 3600.0
        );
        let pk = key.pk;
        let wals = [MemoryWal::new(), MemoryWal::new(), MemoryWal::new()];
        let mut signer = JortsSigner::new(jp, key, wals, e.keys()).unwrap();

        let runs = 8u64;
        let before = e.stats();
        let t = Instant::now();
        for epoch in 0..runs {
            let sig = signer.sign_mode3a(&mut e, epoch, msg).unwrap();
            assert!(jorts_verify(&jp, &pk, msg, &sig));
        }
        let wall = t.elapsed().as_secs_f64() / runs as f64;
        let mut d = delta(e.stats(), before);
        for v in [
            &mut d.perm_levels,
            &mut d.lane_perms,
            &mut d.and_bytes,
            &mut d.check_hops,
            &mut d.check_bytes,
            &mut d.open_rounds,
            &mut d.open_bytes,
        ] {
            *v /= runs;
        }
        engine_row(
            "JortsSha3 Mode 3A (leaf sweep)",
            wall,
            d,
            &format!(
                "mean of {runs}; sig {} B at h=20",
                JortsParams::SHA3_H20.sig_bytes()
            ),
        );

        // Mode 3A over a pre-staged triple bank (Mode 1A gates): four waves per signature.
        let runs_bank = 4u64;
        e.stage_beaver_bank(4 * runs_bank as usize).unwrap();
        e.set_mode(AndMode::BeaverBank).unwrap();
        let before = e.stats();
        let t = Instant::now();
        let mut used = 0u64;
        for i in 0..runs_bank {
            let sig = signer.sign_mode3a(&mut e, runs + i, msg).unwrap();
            assert!(jorts_verify(&jp, &pk, msg, &sig));
            used += 1;
        }
        let wall = t.elapsed().as_secs_f64() / used as f64;
        let mut d = delta(e.stats(), before);
        for v in [
            &mut d.perm_levels,
            &mut d.lane_perms,
            &mut d.and_bytes,
            &mut d.check_hops,
            &mut d.check_bytes,
            &mut d.open_rounds,
            &mut d.open_bytes,
        ] {
            *v /= used;
        }
        engine_row(
            "JortsSha3 Mode 3A + staged bank (1A)",
            wall,
            d,
            &format!("mean of {used}; a leaf whose deepest digit is below 3 leaves triples unused"),
        );
        // Leftover triples are discarded with the engine mode switch below.
        let runs = runs + runs_bank;
        e.set_mode(AndMode::InlineCnf).unwrap();

        let window = 16usize;
        let before = e.stats();
        let t = Instant::now();
        signer.stage_window(&mut e, runs, window).unwrap();
        let stage = t.elapsed().as_secs_f64();
        println!(
            "JortsSha3 Mode 3B window of {window} leaves staged in {:.1} ms one-process \
             ({} lane-perms, background)",
            stage * 1e3,
            delta(e.stats(), before).lane_perms
        );
        let before = e.stats();
        let t = Instant::now();
        for i in 0..window as u64 {
            let sig = signer.sign_mode3b(&mut e, runs + i, msg).unwrap();
            assert!(jorts_verify(&jp, &pk, msg, &sig));
        }
        let wall = t.elapsed().as_secs_f64() / window as f64;
        let mut d = delta(e.stats(), before);
        for v in [
            &mut d.check_hops,
            &mut d.check_bytes,
            &mut d.open_rounds,
            &mut d.open_bytes,
        ] {
            *v /= window as u64;
        }
        engine_row(
            "JortsSha3 Mode 3B (rolling window)",
            wall,
            d,
            &format!("mean of {window}; includes the public digit grind"),
        );
    }

    // ---- SLH-DSA-SHAKE-128f on the 64-lane engine -----------------------------------
    if !skip_slh {
        let sid = [0x51; 32];
        let mut r = rngs(0x40);
        let (keys, _) = run_dealerless_rss_dkg_2of3(sid, 16, &mut r).unwrap();
        let p = Fips205Params::SLH_DSA_SHAKE_128F;
        let pk_seed = keys[0].pk_seed[..16].to_vec();
        // Reproduce public benchmark RNG inputs; custody shares expose no raw getters.
        let mut seed = [0u8; 16];
        let mut prf = [0u8; 16];
        for mut fixture_rng in rngs(0x40) {
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
        let (ref_sk, ref_pk) = slh_keygen_internal(&p, &seed, &prf, &pk_seed).unwrap();
        let mut cluster = RssSlhMpcCluster::new(sid, keys, r).unwrap();
        let t = Instant::now();
        let sig = slh_sign_mpc(&p, &mut cluster, msg, b"", &ref_pk, None).unwrap();
        let wall = t.elapsed().as_secs_f64();
        assert_eq!(sig, slh_sign(&p, msg, b"", &ref_sk, None).unwrap());
        assert!(slh_verify(&p, msg, &sig, b"", &ref_pk));
        let lane_perms = cluster.lane_permutations();
        // This engine does not count hops. The dependency depth of FIPS 205 128f signing
        // is two PRF_msg permutations plus a 16-permutation WOTS chain (w = 16), so 432
        // gate rounds is a lower bound; its per-batch proofs add more.
        row(
            "SLH-DSA-SHAKE-128f (64-lane, 1B)",
            wall,
            24 * 18,
            4800 * lane_perms,
            lane_perms,
            "sig 17088 B; exact FIPS 205 KAT parity; hops are a lower bound, proof traffic not counted",
        );
    }
}
