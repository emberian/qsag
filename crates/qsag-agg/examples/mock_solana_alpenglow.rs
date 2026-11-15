//! Solana Alpenglow (`Rotor` + `Votor`) Consensus Benchmark (`N = 1,500` Stake-Weighted Validators).
//!
//! Benchmarks single-key validator notarization/finalization voting and `Hem` finality-checkpoint
//! compression across realistic Solana Alpenglow consensus parameters (zero threshold-DVT cosplay):
//! 1. **Section 1 — `Rotor` / `Votor` Notarization & Finalization Vote Matrix (`N = 1,500`)**:
//!    - `80%` stake (`1,200` votes): 1-round fast finalization (`150.0 ms` slot budget).
//!    - `60%` stake (`900` votes): 2-round slow finalization (`400.0 ms` slot budget).
//!    - Side-by-side comparison of sub-MTU `FrontierSumFts::Compact514` (`514 B`, 1 QUIC packet) &
//!      `Compact770` (`770 B`, 1 QUIC packet, 2-use), full-width `FrontierSumFts::Full256Bit`
//!      (`2,338 B`, `PQ128`), `JortsPoseidon2` (`4,328 B`, `PQ128` `Hem`-aggregatable), and
//!      reference `FIPS 204 ML-DSA-44` (`2,420 B`, NIST Cat-2).
//! 2. **Section 2 — `Hem` Succinct Finality Certificate Compression (`BciksJohnsonQrom128`)**:
//!    - Full-density `K = 128` single shard (`max_shard_signers(JortsPoseidon2) = 128`),
//!    - Multi-shard `HierarchicalHemAggregate` & jointly-batched `HemAggregatedProof` (`4 x 128 = 512`
//!      default; `1,200`-validator full fast-finality committee via `QSAG_ALPENGLOW_FULL_COMMITTEE=1`),
//!    - Unconditional Johnson-radius QROM (`BciksJohnsonQrom128`) only; refuted capacity-proximity
//!      conjectures (`[CS25]`, `[KKH26]`) are purged.

use std::time::Instant;

use qsag_accel::CpuReferenceBackend;
use qsag_agg::{
    AggSigProfile, DEFAULT_MAX_SHARD_SIGNERS_JORTS, EpochWalSink, HemAggConfig,
    HierarchicalHemAggregate, PreparedPolicyRegistry, ShardHemPolicy, ShardHemWitness, SigError,
    SignerBitmap, SigningMode, SuccinctHierarchicalHemAggregate, ValidatorKeypair,
    ValidatorPublicKey, ValidatorSignature, WhirSecurityRegime, aggregate_signatures_with_config,
    compress_verified_hierarchical_hem, compute_policy_registry_root, hierarchical_hem_message,
    prove_hierarchical_hem, verify_aggregate_with_regime, verify_hierarchical_hem,
    verify_hierarchical_hem_prepared, verify_individual_signature,
    verify_succinct_hierarchical_hem, with_worker_limit,
};
use qsag_fts::{
    FrontierDpTable, FrontierFtsError, FrontierFtsProfile, FrontierFtsPublicKey,
    FrontierFtsSignature, FrontierFtsSigningKey, FsWalFtsEpochLatch, FtsEpochWal,
    verify_frontier_fts,
};

const ALPENGLOW_VALIDATORS: usize = 1_500;
const FAST_QUORUM_80PCT: usize = 1_200; // 80% 1-round fast finalization
const SLOW_QUORUM_60PCT: usize = 900; // 60% 2-round slow finalization
const FAST_BUDGET_MS: f64 = 150.0;
const SLOW_BUDGET_MS: f64 = 400.0;

/// Votor vote metadata + QUIC short-header / AEAD tag (`slot + block_id + validator_id + flags + AEAD`).
const VOTOR_HEADER_BYTES: usize = 96;
/// RFC 9000 §14.1 minimum QUIC UDP payload ceiling (`1,200 B`).
const QUIC_PAYLOAD_MTU_BYTES: usize = 1_200;
/// FIPS 204 ML-DSA-44 reference sizes (`sig = 2,420 B`, `pk = 1,312 B`).
const ML_DSA_44_SIG_BYTES: usize = 2_420;
const ML_DSA_44_PK_BYTES: usize = 1_312;

/// Nominal 4.0 GHz reference clock for cycle estimation & Solana Agave/Firedancer CU calibration
/// (`Ed25519` precompile = `2,280 CU` at ~`35 us` single-core -> ~`65 CU/us`).
const NOMINAL_GHZ: f64 = 4.0;
const SOLANA_CU_PER_US: f64 = 65.0;

#[derive(Default)]
struct MemFtsWal {
    key: Option<[u8; 32]>,
    uses: u8,
}

impl FtsEpochWal for MemFtsWal {
    fn uses_completed(&self, wal_key: &[u8; 32]) -> Result<u8, FrontierFtsError> {
        match &self.key {
            None => Ok(0),
            Some(k) if k == wal_key => Ok(self.uses),
            Some(_) => Err(FrontierFtsError::PersistenceFailed),
        }
    }

    fn reserve_use(&mut self, wal_key: &[u8; 32], next: u8) -> Result<(), FrontierFtsError> {
        if let Some(k) = &self.key
            && k != wal_key
        {
            return Err(FrontierFtsError::PersistenceFailed);
        }
        if next <= self.uses {
            return Err(FrontierFtsError::UseBudgetExhausted);
        }
        self.key = Some(*wal_key);
        self.uses = next;
        Ok(())
    }
}

type EpochReceipt = (u32, u32, [u8; 32]);

#[derive(Default)]
struct MemEpochWal {
    state: Option<([u8; 32], EpochReceipt)>,
}

impl EpochWalSink for MemEpochWal {
    fn recovered_state(
        &self,
        pk_root: &[u8; 32],
    ) -> Result<Option<(u32, u32, [u8; 32])>, SigError> {
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

fn seed32(tag: u8, idx: u32) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[0] = tag;
    out[1..5].copy_from_slice(&idx.to_le_bytes());
    for (i, b) in out[5..].iter_mut().enumerate() {
        *b = tag
            .wrapping_mul(37)
            .wrapping_add((idx as u8).wrapping_mul(13))
            .wrapping_add(i as u8);
    }
    out
}

fn votor_vote_payload(validator_idx: usize) -> [u8; 72] {
    let mut msg = [0u8; 72];
    msg[0..32].copy_from_slice(b"solana.alpenglow.votor.notarize.");
    msg[32..40].copy_from_slice(&42_000_000u64.to_le_bytes());
    msg[40..44].copy_from_slice(&(validator_idx as u32).to_le_bytes());
    msg[44..72].copy_from_slice(b"blk_9f8e7d6c5b4a3210fedcba98");
    msg
}

fn percentile_sorted(sorted: &[f64], num: usize, den: usize) -> f64 {
    if sorted.is_empty() {
        return 0.0;
    }
    let idx = ((sorted.len() - 1) * num).div_ceil(den);
    sorted[idx.min(sorted.len() - 1)]
}

fn peak_rss_mib() -> Option<f64> {
    let status = std::fs::read_to_string("/proc/self/status").ok()?;
    for line in status.lines() {
        if let Some(rest) = line.strip_prefix("VmHWM:") {
            let kib: f64 = rest.split_whitespace().next()?.parse().ok()?;
            return Some(kib / 1024.0);
        }
    }
    None
}

#[inline]
const fn quic_packets_for_sig(sig_bytes: usize) -> usize {
    (sig_bytes + VOTOR_HEADER_BYTES).div_ceil(QUIC_PAYLOAD_MTU_BYTES)
}

#[inline]
fn ingress_mb(num_votes: usize, sig_bytes: usize) -> f64 {
    (num_votes * (sig_bytes + VOTOR_HEADER_BYTES)) as f64 / 1_000_000.0
}

struct VoteBenchRow {
    name: &'static str,
    security_note: &'static str,
    sig_bytes: usize,
    pk_bytes: usize,
    quic_pkts: usize,
    warm_sign_us: f64,
    warm_fsync_sign_us: Option<f64>,
    verify_1core_us: f64,
    batch900_p50_ms: f64,
    batch900_p99_ms: f64,
    batch1200_p50_ms: f64,
    batch1200_p99_ms: f64,
}

type SignedFtsEntry = (FrontierFtsPublicKey, Vec<([u8; 72], FrontierFtsSignature)>);

fn bench_fts_rotor_profile(
    name: &'static str,
    security_note: &'static str,
    profile: FrontierFtsProfile,
    full_distinct_trees: bool,
    workers: usize,
    batch_iters: usize,
) -> VoteBenchRow {
    let dp = FrontierDpTable::build(profile);
    let max_uses = profile.params().max_safe_uses as usize;
    // Generate genuinely distinct cryptographic votes across `N = 1,500` validator indices while
    // dropping secret chain caches immediately so peak RSS stays < 80 MiB.
    let base_trees = if full_distinct_trees {
        ALPENGLOW_VALIDATORS.div_ceil(max_uses)
    } else {
        match profile {
            FrontierFtsProfile::Full256Bit => ALPENGLOW_VALIDATORS,
            FrontierFtsProfile::Compact514 => 384,
            FrontierFtsProfile::Compact770 => 256,
            _ => 256,
        }
    };

    let chunk = base_trees.div_ceil(workers);
    let pool: Vec<SignedFtsEntry> = std::thread::scope(|scope| {
        let dp_ref = &dp;
        let handles: Vec<_> = (0..workers)
            .filter_map(|w_idx| {
                let start = w_idx * chunk;
                (start < base_trees).then(|| {
                    let end = (start + chunk).min(base_trees);
                    scope.spawn(move || {
                        let accel = CpuReferenceBackend::new();
                        let mut out = Vec::with_capacity(end - start);
                        for t_idx in start..end {
                            let u = t_idx as u32;
                            let sk = FrontierFtsSigningKey::keygen(
                                profile,
                                seed32(0xA1, u),
                                seed32(0xB2, u),
                                seed32(0xC3, u),
                                true,
                                &accel,
                            );
                            let mut sk = sk
                                .attach_wal(Box::new(MemFtsWal::default()))
                                .expect("attach in-memory FTS WAL");
                            let pk = sk.pk.clone();
                            let mut signed = Vec::with_capacity(max_uses);
                            for use_slot in 0..max_uses {
                                let v_idx = t_idx * max_uses + use_slot;
                                let msg = votor_vote_payload(v_idx);
                                let sig = sk
                                    .sign(
                                        dp_ref,
                                        &msg,
                                        &seed32(0xD4u8.wrapping_add(use_slot as u8), u),
                                    )
                                    .expect("FTS slot vote sign");
                                signed.push((msg, sig));
                            }
                            drop(sk);
                            out.push((pk, signed));
                        }
                        out
                    })
                })
            })
            .collect();
        handles
            .into_iter()
            .map(|h| h.join().expect("FTS setup worker panicked"))
            .collect::<Vec<_>>()
            .into_iter()
            .flatten()
            .collect()
    });

    let mut votes: Vec<(FrontierFtsPublicKey, [u8; 72], FrontierFtsSignature)> =
        Vec::with_capacity(ALPENGLOW_VALIDATORS);
    for v_idx in 0..ALPENGLOW_VALIDATORS {
        let (pk, signed) = &pool[v_idx % pool.len()];
        let (msg, sig) = &signed[(v_idx / pool.len()) % signed.len()];
        votes.push((pk.clone(), *msg, sig.clone()));
    }
    let sig_bytes = votes[0].2.to_bytes(profile).len();
    assert_eq!(sig_bytes, profile.signature_bytes());
    let pk_bytes = 32 + votes[0].0.root.len();

    // Measure warm cached-tree signing latency (pure compute + real `FsWalFtsEpochLatch` journal).
    let accel = CpuReferenceBackend::new();
    let warm_msg = votor_vote_payload(99_999);
    let mut sign_samples_us = Vec::with_capacity(9);
    for sample_idx in 0..9u32 {
        let sk = FrontierFtsSigningKey::keygen(
            profile,
            seed32(0xE1, 9_000 + sample_idx),
            seed32(0xE2, 9_000 + sample_idx),
            seed32(0xE3, 9_000 + sample_idx),
            true,
            &accel,
        )
        .attach_wal(Box::new(MemFtsWal::default()))
        .expect("attach warm WAL");
        let mut sk = sk;
        let t0 = Instant::now();
        let sig = sk
            .sign(&dp, &warm_msg, &seed32(0xE4, 9_000 + sample_idx))
            .expect("warm FTS sign");
        sign_samples_us.push(t0.elapsed().as_secs_f64() * 1_000_000.0);
        verify_frontier_fts(&sk.pk, &dp, &warm_msg, &sig).expect("warm FTS vote must verify");
    }
    sign_samples_us.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let warm_sign_us = sign_samples_us[sign_samples_us.len() / 2];

    let run_id = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("system clock")
        .as_nanos();
    let wal_dir = std::env::temp_dir().join(format!(
        "qsag-alpenglow-fts-{}-{run_id}",
        std::process::id()
    ));
    std::fs::create_dir(&wal_dir).expect("create temp FTS journal dir");
    let fs_sk = FrontierFtsSigningKey::keygen(
        profile,
        seed32(0xF1, 77),
        seed32(0xF2, 77),
        seed32(0xF3, 77),
        true,
        &accel,
    );
    let fs_wal = FsWalFtsEpochLatch::create(
        wal_dir.join("validator.wal"),
        fs_sk.wal_key(),
        seed32(0xF4, 77),
    )
    .expect("create durable FTS WAL");
    let mut fs_sk = fs_sk
        .attach_wal(Box::new(fs_wal))
        .expect("attach durable FTS WAL");
    let t_fs = Instant::now();
    let fs_sig = fs_sk
        .sign(&dp, &warm_msg, &seed32(0xF5, 77))
        .expect("durable FTS sign");
    let fsync_us = t_fs.elapsed().as_secs_f64() * 1_000_000.0;
    verify_frontier_fts(&fs_sk.pk, &dp, &warm_msg, &fs_sig).expect("durable FTS vote verifies");
    drop(fs_sk);
    std::fs::remove_dir_all(&wal_dir).expect("cleanup temp FTS journal dir");

    // Single-core per-vote verification latency across 256 votes.
    let single_count = 256.min(votes.len());
    let t_1c = Instant::now();
    for (pk, msg, sig) in &votes[..single_count] {
        verify_frontier_fts(pk, &dp, msg, sig).expect("single-core FTS vote verify");
    }
    let verify_1core_us = (t_1c.elapsed().as_secs_f64() * 1_000_000.0) / (single_count as f64);

    // Multi-core parallel batch verification for 900 (60% slow path) & 1,200 (80% fast path) votes.
    let measure_batch = |count: usize| -> (f64, f64) {
        let slice = &votes[..count];
        let per_worker = count.div_ceil(workers);
        let mut samples = Vec::with_capacity(batch_iters);
        for _ in 0..batch_iters {
            let t0 = Instant::now();
            std::thread::scope(|scope| {
                let dp_ref = &dp;
                for batch in slice.chunks(per_worker) {
                    scope.spawn(move || {
                        for (pk, msg, sig) in batch {
                            verify_frontier_fts(pk, dp_ref, msg, sig)
                                .expect("parallel FTS notarization vote must verify");
                        }
                    });
                }
            });
            samples.push(t0.elapsed().as_secs_f64() * 1_000.0);
        }
        samples.sort_by(|a, b| a.partial_cmp(b).unwrap());
        (
            percentile_sorted(&samples, 50, 100),
            percentile_sorted(&samples, 99, 100),
        )
    };
    let (batch900_p50_ms, batch900_p99_ms) = measure_batch(SLOW_QUORUM_60PCT);
    let (batch1200_p50_ms, batch1200_p99_ms) = measure_batch(FAST_QUORUM_80PCT);

    VoteBenchRow {
        name,
        security_note,
        sig_bytes,
        pk_bytes,
        quic_pkts: quic_packets_for_sig(sig_bytes),
        warm_sign_us,
        warm_fsync_sign_us: Some(fsync_us),
        verify_1core_us,
        batch900_p50_ms,
        batch900_p99_ms,
        batch1200_p50_ms,
        batch1200_p99_ms,
    }
}

fn build_jorts_committee_and_bench_rotor(
    committee_keys: usize,
    workers: usize,
    batch_iters: usize,
) -> (Vec<(ValidatorKeypair, MemEpochWal)>, VoteBenchRow) {
    let master_seed = seed32(0x99, 42);
    let chunk = committee_keys.div_ceil(workers);
    let mut validators: Vec<(ValidatorKeypair, MemEpochWal)> = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..workers)
            .filter_map(|w_idx| {
                let start = w_idx * chunk;
                (start < committee_keys).then(|| {
                    let end = (start + chunk).min(committee_keys);
                    scope.spawn(move || {
                        let mut out = Vec::with_capacity(end - start);
                        for idx in start..end {
                            let kp = ValidatorKeypair::keygen_deterministic(
                                AggSigProfile::JortsPoseidon2,
                                &master_seed,
                                idx as u32,
                            );
                            out.push((kp, MemEpochWal::default()));
                        }
                        out
                    })
                })
            })
            .collect();
        handles
            .into_iter()
            .map(|h| h.join().expect("Jorts keygen worker panicked"))
            .collect::<Vec<_>>()
            .into_iter()
            .flatten()
            .collect()
    });

    // Sign `ALPENGLOW_VALIDATORS = 1,500` distinct slot votes across distinct XMSS leaves (`0..3`).
    type SignedJortsEntry = (ValidatorPublicKey, Vec<([u8; 72], ValidatorSignature)>);
    let epochs_needed = ALPENGLOW_VALIDATORS.div_ceil(validators.len());
    let signed_per_validator: Vec<SignedJortsEntry> = std::thread::scope(|scope| {
        let per_worker = validators.len().div_ceil(workers);
        let handles: Vec<_> = validators
            .chunks_mut(per_worker)
            .enumerate()
            .map(|(c_idx, sub)| {
                let base = c_idx * per_worker;
                scope.spawn(move || {
                    let mut out = Vec::with_capacity(sub.len());
                    for (local_i, (kp, wal)) in sub.iter_mut().enumerate() {
                        let val_i = base + local_i;
                        let mut slot_sigs = Vec::with_capacity(epochs_needed);
                        for ep in 0..epochs_needed {
                            let vote_idx = ep * committee_keys + val_i;
                            let msg = votor_vote_payload(vote_idx);
                            let sig = kp
                                .sign_stateful(&msg, ep as u32, wal)
                                .expect("Jorts Votor vote sign");
                            slot_sigs.push((msg, sig));
                        }
                        out.push((kp.pk, slot_sigs));
                    }
                    out
                })
            })
            .collect();
        handles
            .into_iter()
            .map(|h| h.join().expect("Jorts vote sign panicked"))
            .collect::<Vec<_>>()
            .into_iter()
            .flatten()
            .collect()
    });

    let mut votes: Vec<(ValidatorPublicKey, [u8; 72], ValidatorSignature)> =
        Vec::with_capacity(ALPENGLOW_VALIDATORS);
    for v_idx in 0..ALPENGLOW_VALIDATORS {
        let k_idx = v_idx % signed_per_validator.len();
        let ep_idx = v_idx / signed_per_validator.len();
        let (pk, list) = &signed_per_validator[k_idx];
        let (msg, sig) = &list[ep_idx];
        votes.push((*pk, *msg, sig.clone()));
    }

    // Warm single-validator stateful sign latency at epoch `epochs_needed`.
    let warm_epoch = epochs_needed as u32;
    let mut sign_samples_us = Vec::with_capacity(9);
    for (i, (kp, wal)) in validators.iter_mut().take(9).enumerate() {
        let msg = votor_vote_payload(50_000 + i);
        let t0 = Instant::now();
        let sig = kp
            .sign_stateful(&msg, warm_epoch, wal)
            .expect("warm Jorts sign");
        sign_samples_us.push(t0.elapsed().as_secs_f64() * 1_000_000.0);
        assert!(verify_individual_signature(&kp.pk, &msg, &sig));
    }
    sign_samples_us.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let warm_sign_us = sign_samples_us[sign_samples_us.len() / 2];

    let single_count = 256.min(votes.len());
    let t_1c = Instant::now();
    for (pk, msg, sig) in &votes[..single_count] {
        assert!(verify_individual_signature(pk, msg, sig));
    }
    let verify_1core_us = (t_1c.elapsed().as_secs_f64() * 1_000_000.0) / (single_count as f64);

    let measure_batch = |count: usize| -> (f64, f64) {
        let slice = &votes[..count];
        let per_worker = count.div_ceil(workers);
        let mut samples = Vec::with_capacity(batch_iters);
        for _ in 0..batch_iters {
            let t0 = Instant::now();
            std::thread::scope(|scope| {
                for batch in slice.chunks(per_worker) {
                    scope.spawn(move || {
                        for (pk, msg, sig) in batch {
                            assert!(verify_individual_signature(pk, msg, sig));
                        }
                    });
                }
            });
            samples.push(t0.elapsed().as_secs_f64() * 1_000.0);
        }
        samples.sort_by(|a, b| a.partial_cmp(b).unwrap());
        (
            percentile_sorted(&samples, 50, 100),
            percentile_sorted(&samples, 99, 100),
        )
    };
    let (batch900_p50_ms, batch900_p99_ms) = measure_batch(SLOW_QUORUM_60PCT);
    let (batch1200_p50_ms, batch1200_p99_ms) = measure_batch(FAST_QUORUM_80PCT);

    let sig_bytes = AggSigProfile::JortsPoseidon2.raw_signature_bytes();
    let row = VoteBenchRow {
        name: "JortsPoseidon2",
        security_note: "PQ128 (32B Poseidon2, 64-ep XMSS, Hem-agg)",
        sig_bytes,
        pk_bytes: 64,
        quic_pkts: quic_packets_for_sig(sig_bytes),
        warm_sign_us,
        warm_fsync_sign_us: None,
        verify_1core_us,
        batch900_p50_ms,
        batch900_p99_ms,
        batch1200_p50_ms,
        batch1200_p99_ms,
    };
    (validators, row)
}

fn print_section1_rotor_votor_matrix(rows: &[VoteBenchRow]) {
    println!(
        "\n[Section 1] `Rotor` / `Votor` Notarization & Finalization Vote Matrix (N = {ALPENGLOW_VALIDATORS} Validators)"
    );
    println!(
        "  Budgets : 80% 1-round fast finalization = {FAST_QUORUM_80PCT} votes / {FAST_BUDGET_MS:.0} ms | 60% 2-round slow finalization = {SLOW_QUORUM_60PCT} votes / {SLOW_BUDGET_MS:.0} ms"
    );
    println!(
        "  Framing : +{VOTOR_HEADER_BYTES} B Votor/QUIC header, {QUIC_PAYLOAD_MTU_BYTES} B RFC 9000 UDP payload (`ceil((sig + {VOTOR_HEADER_BYTES}) / {QUIC_PAYLOAD_MTU_BYTES})`)"
    );
    println!(
        "  {:<20} {:>7} {:>6} {:>8} {:>9} {:>9} {:>9} {:>10} {:>10} {:>11} {:>9}",
        "Profile",
        "Sig(B)",
        "PK(B)",
        "QUIC_Pkt",
        "In_900MB",
        "In_1200MB",
        "In_1500MB",
        "Sign(us)",
        "Ver1C(us)",
        "EstCyc@4GHz",
        "Solana_CU"
    );
    println!("  {}", "-".repeat(120));
    for r in rows {
        let est_cycles = r.verify_1core_us * 1_000.0 * NOMINAL_GHZ;
        let est_cu = r.verify_1core_us * SOLANA_CU_PER_US;
        println!(
            "  {:<20} {:>7} {:>6} {:>8} {:>9.3} {:>9.3} {:>9.3} {:>10.1} {:>10.1} {:>11.0} {:>9.0}",
            r.name,
            r.sig_bytes,
            r.pk_bytes,
            r.quic_pkts,
            ingress_mb(SLOW_QUORUM_60PCT, r.sig_bytes),
            ingress_mb(FAST_QUORUM_80PCT, r.sig_bytes),
            ingress_mb(ALPENGLOW_VALIDATORS, r.sig_bytes),
            r.warm_sign_us,
            r.verify_1core_us,
            est_cycles,
            est_cu,
        );
    }
    println!(
        "  {:<20} {:>7} {:>6} {:>8} {:>9.3} {:>9.3} {:>9.3} {:>10} {:>10} {:>11} {:>9}",
        "ML-DSA-44 (ref)",
        ML_DSA_44_SIG_BYTES,
        ML_DSA_44_PK_BYTES,
        quic_packets_for_sig(ML_DSA_44_SIG_BYTES),
        ingress_mb(SLOW_QUORUM_60PCT, ML_DSA_44_SIG_BYTES),
        ingress_mb(FAST_QUORUM_80PCT, ML_DSA_44_SIG_BYTES),
        ingress_mb(ALPENGLOW_VALIDATORS, ML_DSA_44_SIG_BYTES),
        "ref(FIPS)",
        "ref(FIPS)",
        "ref(Cat-2)",
        "non-agg",
    );

    println!("\n  Parallel Multi-Core Batch Verification vs Alpenglow Consensus Budgets:");
    println!(
        "  {:<20} {:>12} {:>12} {:>14} {:>12} {:>12} {:>14}  Security / Epoch Tree Envelope",
        "Profile",
        "900_p50(ms)",
        "900_p99(ms)",
        "400ms_Headrm",
        "1200_p50(ms)",
        "1200_p99(ms)",
        "150ms_Headrm",
    );
    println!("  {}", "-".repeat(138));
    for r in rows {
        let h400 = SLOW_BUDGET_MS / r.batch900_p50_ms.max(0.001);
        let h150 = FAST_BUDGET_MS / r.batch1200_p50_ms.max(0.001);
        println!(
            "  {:<20} {:>12.2} {:>12.2} {:>13.1}x {:>12.2} {:>12.2} {:>13.1}x  {}",
            r.name,
            r.batch900_p50_ms,
            r.batch900_p99_ms,
            h400,
            r.batch1200_p50_ms,
            r.batch1200_p99_ms,
            h150,
            r.security_note,
        );
        if let Some(fs_us) = r.warm_fsync_sign_us {
            println!(
                "    └─ durable `FsWalFtsEpochLatch` sign (incl. OS journal sync) = {fs_us:.1} us"
            );
        }
    }
    println!(
        "  Note: `Full256Bit` (`2,338 B`) fits in 2 UDP datagrams when header <= 62 B (`2,400 B`) or on 1,232 B IPv6 UDP payloads,"
    );
    println!(
        "        whereas `ML-DSA-44` (`2,420 B`) exceeds `2 x 1,200 B` even before headers (always 3 RFC 9000 initial QUIC datagrams)."
    );
}

fn bench_section2_hem_finality_compression(
    validators: &mut [(ValidatorKeypair, MemEpochWal)],
    checkpoint_epoch: u32,
    workers: usize,
    verify_iters: usize,
    full_committee: bool,
) {
    let regime = WhirSecurityRegime::BciksJohnsonQrom128;
    let shard_cap = DEFAULT_MAX_SHARD_SIGNERS_JORTS;
    assert_eq!(shard_cap, 128);
    let jorts_raw_b = AggSigProfile::JortsPoseidon2.raw_signature_bytes();

    println!(
        "\n[Section 2] `Hem` Succinct Finality Certificate Compression (`JortsPoseidon2`, `{regime:?}`)"
    );
    println!(
        "  Security Regime: `BciksJohnsonQrom128` — unconditional BCIKS20 Johnson-radius QROM (`ceil(512/log2(B)) + 2` queries + 16-bit PoW)."
    );
    println!(
        "  Soundness Note : Conjectural capacity-proximity regimes were refuted in `[CS25]`/`[KKH26]` and are completely removed."
    );

    // 2A. Single full-density shard (`K = 128`, `max_shard_signers(JortsPoseidon2) = 128`).
    let msg_single = b"solana.alpenglow.finality.checkpoint.slot.42000000.single_shard";
    let single_k = shard_cap;
    let mut single_pks = Vec::with_capacity(single_k);
    let mut single_sigs = Vec::with_capacity(single_k);
    for (kp, wal) in validators.iter_mut().take(single_k) {
        let sig = kp
            .sign_stateful(msg_single, checkpoint_epoch, wal)
            .expect("sign K=128 checkpoint");
        single_pks.push(kp.pk);
        single_sigs.push(sig);
    }
    let single_active: Vec<usize> = (0..single_k).collect();
    let single_bm =
        SignerBitmap::from_active_indices(single_k as u32, &single_active).expect("bitmap");
    let mut single_cfg = HemAggConfig::default_for(AggSigProfile::JortsPoseidon2, seed32(0xAA, 7));
    single_cfg.regime = regime;

    let t_prove_single = Instant::now();
    let single_proof = aggregate_signatures_with_config(
        &single_pks,
        &single_bm,
        &SigningMode::SharedMessage(msg_single),
        &single_sigs,
        &single_cfg,
    )
    .expect("K=128 Hem checkpoint proof");
    let single_prove_ms = t_prove_single.elapsed().as_secs_f64() * 1_000.0;
    let single_wire = single_proof.to_bytes();

    let measure_agg_verify = |max_w: Option<usize>| -> (f64, f64) {
        let mut samples = Vec::with_capacity(verify_iters);
        for _ in 0..verify_iters {
            let t0 = Instant::now();
            let ok = match max_w {
                Some(w) => with_worker_limit(w, || {
                    verify_aggregate_with_regime(
                        &single_pks,
                        &SigningMode::SharedMessage(msg_single),
                        &single_proof,
                        regime,
                    )
                }),
                None => verify_aggregate_with_regime(
                    &single_pks,
                    &SigningMode::SharedMessage(msg_single),
                    &single_proof,
                    regime,
                ),
            };
            assert!(ok, "K=128 Hem checkpoint must verify");
            samples.push(t0.elapsed().as_secs_f64() * 1_000.0);
        }
        samples.sort_by(|a, b| a.partial_cmp(b).unwrap());
        (
            percentile_sorted(&samples, 50, 100),
            percentile_sorted(&samples, 99, 100),
        )
    };
    let (single_all_p50, single_all_p99) = measure_agg_verify(None);
    let (single_1c_p50, single_1c_p99) = measure_agg_verify(Some(1));

    // 2B. Jointly-witnessed multi-shard `HemAggregatedProof` (`max_shards_per_batch = 10` -> ONE
    //     joint WHIR PCS opening!) AND regional 2-layer `HierarchicalHemAggregate`.
    let target_signers = if full_committee {
        FAST_QUORUM_80PCT
    } else {
        std::env::var("QSAG_ALPENGLOW_SHARDS")
            .ok()
            .and_then(|s| s.parse::<usize>().ok())
            .filter(|&n| n > 0)
            .map(|n| (n * shard_cap).min(validators.len()))
            .unwrap_or(4 * shard_cap)
    };
    assert!(target_signers <= validators.len());

    let msg_joint = b"solana.alpenglow.finality.checkpoint.slot.42000000.joint_committee";
    let joint_epoch = checkpoint_epoch + 1;
    let per_worker = target_signers.div_ceil(workers);
    let joint_pairs: Vec<(ValidatorPublicKey, ValidatorSignature)> = std::thread::scope(|scope| {
        let handles: Vec<_> = validators[..target_signers]
            .chunks_mut(per_worker)
            .map(|sub| {
                scope.spawn(move || {
                    sub.iter_mut()
                        .map(|(kp, wal)| {
                            let sig = kp
                                .sign_stateful(msg_joint, joint_epoch, wal)
                                .expect("joint committee checkpoint sign");
                            (kp.pk, sig)
                        })
                        .collect::<Vec<_>>()
                })
            })
            .collect();
        handles
            .into_iter()
            .map(|h| h.join().expect("joint sign worker panicked"))
            .collect::<Vec<_>>()
            .into_iter()
            .flatten()
            .collect()
    });
    let joint_pks: Vec<ValidatorPublicKey> = joint_pairs.iter().map(|(pk, _)| *pk).collect();
    let joint_sigs: Vec<ValidatorSignature> = joint_pairs.into_iter().map(|(_, s)| s).collect();
    let joint_active: Vec<usize> = (0..target_signers).collect();
    let joint_bm =
        SignerBitmap::from_active_indices(target_signers as u32, &joint_active).expect("bitmap");

    let mut joint_cfg = HemAggConfig::default_for(AggSigProfile::JortsPoseidon2, seed32(0xBB, 11));
    joint_cfg.regime = regime;
    joint_cfg.max_signers_per_shard = shard_cap;
    joint_cfg.max_shards_per_batch = 16; // Jointly witness full 128-signer shards under one WHIR opening!

    let t_prove_joint = Instant::now();
    let joint_proof = aggregate_signatures_with_config(
        &joint_pks,
        &joint_bm,
        &SigningMode::SharedMessage(msg_joint),
        &joint_sigs,
        &joint_cfg,
    )
    .expect("joint multi-shard Hem proof");
    let joint_prove_ms = t_prove_joint.elapsed().as_secs_f64() * 1_000.0;
    let joint_wire = joint_proof.to_bytes();

    let measure_joint_verify = |max_w: Option<usize>| -> (f64, f64) {
        let mut samples = Vec::with_capacity(verify_iters);
        for _ in 0..verify_iters {
            let t0 = Instant::now();
            let ok = match max_w {
                Some(w) => with_worker_limit(w, || {
                    verify_aggregate_with_regime(
                        &joint_pks,
                        &SigningMode::SharedMessage(msg_joint),
                        &joint_proof,
                        regime,
                    )
                }),
                None => verify_aggregate_with_regime(
                    &joint_pks,
                    &SigningMode::SharedMessage(msg_joint),
                    &joint_proof,
                    regime,
                ),
            };
            assert!(ok, "joint committee Hem proof must verify");
            samples.push(t0.elapsed().as_secs_f64() * 1_000.0);
        }
        samples.sort_by(|a, b| a.partial_cmp(b).unwrap());
        (
            percentile_sorted(&samples, 50, 100),
            percentile_sorted(&samples, 99, 100),
        )
    };
    let (joint_all_p50, joint_all_p99) = measure_joint_verify(None);
    let (joint_1c_p50, joint_1c_p99) = measure_joint_verify(Some(1));

    // 2C. Regional 2-Layer `HierarchicalHemAggregate` over disjoint validator shards.
    let hier_epoch = (checkpoint_epoch + 2) as u64;
    let hier_msg = b"solana.alpenglow.finality.hierarchical.slot.42000000";
    let shard_slices: Vec<(usize, usize)> = (0..target_signers.div_ceil(shard_cap))
        .map(|s| {
            let lo = s * shard_cap;
            let hi = (lo + shard_cap).min(target_signers);
            (lo, hi)
        })
        .collect();
    let policies: Vec<ShardHemPolicy> = shard_slices
        .iter()
        .enumerate()
        .map(|(s_idx, &(lo, hi))| ShardHemPolicy {
            shard_id: (s_idx as u64 + 1) * 10,
            custodian_cluster: seed32(0x61, s_idx as u32),
            quorum_keys: validators[lo..hi].iter().map(|(kp, _)| kp.pk).collect(),
            minimum_quorums: (hi - lo) * 3 / 4,
        })
        .collect();
    let registry_root = compute_policy_registry_root(&policies);

    let mut signed_hier: Vec<(SignerBitmap, Vec<ValidatorSignature>)> =
        Vec::with_capacity(policies.len());
    for (policy, &(lo, hi)) in policies.iter().zip(&shard_slices) {
        let region_msg = hierarchical_hem_message(&registry_root, policy, hier_epoch, hier_msg);
        let len = hi - lo;
        let active: Vec<usize> = (0..len).collect();
        let bm = SignerBitmap::from_active_indices(len as u32, &active).expect("shard bitmap");
        let sigs: Vec<ValidatorSignature> = validators[lo..hi]
            .iter_mut()
            .map(|(kp, wal)| {
                kp.sign_stateful(&region_msg, hier_epoch as u32, wal)
                    .expect("hierarchical shard sign")
            })
            .collect();
        signed_hier.push((bm, sigs));
    }
    let hier_witnesses: Vec<ShardHemWitness<'_>> = signed_hier
        .iter()
        .map(|(bm, sigs)| ShardHemWitness {
            bitmap: bm,
            signatures: sigs.as_slice(),
        })
        .collect();
    let min_global: usize = policies.iter().map(|p| p.minimum_quorums).sum();
    let mut hier_cfg = HemAggConfig::default_for(AggSigProfile::JortsPoseidon2, seed32(0xCC, 19));
    hier_cfg.regime = regime;

    let t_prove_hier = Instant::now();
    let hier_agg = prove_hierarchical_hem(
        &policies,
        &hier_witnesses,
        hier_epoch,
        hier_msg,
        min_global,
        &hier_cfg,
    )
    .expect("Alpenglow 2-layer hierarchical Hem");
    let hier_prove_ms = t_prove_hier.elapsed().as_secs_f64() * 1_000.0;
    let hier_wire = hier_agg.to_bytes();
    let hier_decoded =
        HierarchicalHemAggregate::from_bytes_canonical(&hier_wire).expect("canonical decode");
    let prepared_hier =
        PreparedPolicyRegistry::new(policies.clone()).expect("valid Alpenglow policy registry");
    assert!(verify_hierarchical_hem(
        &policies,
        hier_epoch,
        hier_msg,
        min_global,
        regime,
        &hier_decoded,
    ));

    let measure_hier_verify = |max_w: Option<usize>| -> (f64, f64) {
        let mut samples = Vec::with_capacity(verify_iters);
        for _ in 0..verify_iters {
            let t0 = Instant::now();
            let ok = match max_w {
                Some(w) => with_worker_limit(w, || {
                    verify_hierarchical_hem_prepared(
                        &prepared_hier,
                        hier_epoch,
                        hier_msg,
                        min_global,
                        regime,
                        &hier_decoded,
                    )
                }),
                None => verify_hierarchical_hem_prepared(
                    &prepared_hier,
                    hier_epoch,
                    hier_msg,
                    min_global,
                    regime,
                    &hier_decoded,
                ),
            };
            assert!(ok, "Alpenglow hierarchical Hem must verify");
            samples.push(t0.elapsed().as_secs_f64() * 1_000.0);
        }
        samples.sort_by(|a, b| a.partial_cmp(b).unwrap());
        (
            percentile_sorted(&samples, 50, 100),
            percentile_sorted(&samples, 99, 100),
        )
    };
    let (hier_all_p50, hier_all_p99) = measure_hier_verify(None);
    let (hier_1c_p50, hier_1c_p99) = measure_hier_verify(Some(1));

    // 2D. Succinct Outer Commitment-Chain Compression (`SuccinctHierarchicalHemAggregate`):
    //     compresses M regional shard proofs into 1 outer `BciksJohnsonQrom128` WHIR proof!
    let t_prove_succ = Instant::now();
    let succ_agg = compress_verified_hierarchical_hem(
        &policies,
        hier_epoch,
        hier_msg,
        min_global,
        &hier_decoded,
        hier_cfg.blinding_seed,
    )
    .expect("Alpenglow succinct outer Hem compression");
    let succ_prove_ms = t_prove_succ.elapsed().as_secs_f64() * 1_000.0;
    let succ_wire = succ_agg.to_bytes();
    let succ_decoded = SuccinctHierarchicalHemAggregate::from_bytes_canonical(&succ_wire)
        .expect("canonical succinct decode");

    let measure_succ_verify = |max_w: Option<usize>| -> (f64, f64) {
        let mut samples = Vec::with_capacity(verify_iters);
        for _ in 0..verify_iters {
            let t0 = Instant::now();
            let ok = match max_w {
                Some(w) => with_worker_limit(w, || {
                    verify_succinct_hierarchical_hem(
                        &policies,
                        hier_epoch,
                        hier_msg,
                        min_global,
                        &succ_decoded,
                    )
                }),
                None => verify_succinct_hierarchical_hem(
                    &policies,
                    hier_epoch,
                    hier_msg,
                    min_global,
                    &succ_decoded,
                ),
            };
            assert!(ok, "Alpenglow succinct outer Hem must verify");
            samples.push(t0.elapsed().as_secs_f64() * 1_000.0);
        }
        samples.sort_by(|a, b| a.partial_cmp(b).unwrap());
        (
            percentile_sorted(&samples, 50, 100),
            percentile_sorted(&samples, 99, 100),
        )
    };
    let (succ_all_p50, succ_all_p99) = measure_succ_verify(None);
    let (succ_1c_p50, succ_1c_p99) = measure_succ_verify(Some(1));
    let rss_str = peak_rss_mib()
        .map(|m| format!("{m:.1} MiB"))
        .unwrap_or_else(|| "n/a".to_string());

    println!(
        "\n  Live Prover & Verifier Measurements (`BciksJohnsonQrom128`, peak_rss = {rss_str}):"
    );
    println!(
        "  {:<32} {:>7} {:>10} {:>10} {:>10} {:>9} {:>9} {:>10} {:>11} {:>11}",
        "Certificate Topology",
        "Signers",
        "RawJortsKB",
        "RawMLDSAKB",
        "HemWireKiB",
        "vs_Jorts",
        "vs_MLDSA",
        "Prove(ms)",
        "VerAll p50/99",
        "Ver1C p50/99"
    );
    println!("  {}", "-".repeat(134));

    for (label, k, wire_len, p_ms, all_50, all_99, c1_50, c1_99) in [
        (
            "Single Full Shard (1x128)",
            single_k,
            single_wire.len(),
            single_prove_ms,
            single_all_p50,
            single_all_p99,
            single_1c_p50,
            single_1c_p99,
        ),
        (
            "Jointly-Batched WHIR Cert",
            target_signers,
            joint_wire.len(),
            joint_prove_ms,
            joint_all_p50,
            joint_all_p99,
            joint_1c_p50,
            joint_1c_p99,
        ),
        (
            "Regional 2-Layer Hierarchical",
            target_signers,
            hier_wire.len(),
            hier_prove_ms,
            hier_all_p50,
            hier_all_p99,
            hier_1c_p50,
            hier_1c_p99,
        ),
        (
            "Succinct Outer Recursive Hem",
            target_signers,
            succ_wire.len(),
            succ_prove_ms,
            succ_all_p50,
            succ_all_p99,
            succ_1c_p50,
            succ_1c_p99,
        ),
    ] {
        let raw_jorts = k * jorts_raw_b;
        let raw_mldsa = k * ML_DSA_44_SIG_BYTES;
        println!(
            "  {:<32} {:>7} {:>10.1} {:>10.1} {:>10.1} {:>8.2}x {:>8.2}x {:>10.2} {:>5.2}/{:<5.2} {:>5.2}/{:<5.2}",
            label,
            k,
            raw_jorts as f64 / 1024.0,
            raw_mldsa as f64 / 1024.0,
            wire_len as f64 / 1024.0,
            raw_jorts as f64 / wire_len as f64,
            raw_mldsa as f64 / wire_len as f64,
            p_ms,
            all_50,
            all_99,
            c1_50,
            c1_99,
        );
    }

    // Exact wire-size projection for 60% (`900` = `7x128 + 4`) and 80% (`1,200` = `9x128 + 48`)
    // jointly-witnessed Alpenglow finality certificates derived from the measured per-extra-shard
    // affine witness delta (`row_sumcheck_polys + col_evals + 2 Ext4 point claims` = `6,688 B/shard`).
    let num_joint_shards = target_signers.div_ceil(shard_cap);
    let per_extra_shard_b = if num_joint_shards > 1 {
        (joint_wire.len() - single_wire.len()) / (num_joint_shards - 1)
    } else {
        6_688
    };
    println!(
        "\n  Alpenglow Committee Certificate Wire Accounting (`BciksJohnsonQrom128` Jointly-Batched WHIR):"
    );
    for (q_label, k_signers, full_shards, tail_signers) in [
        (
            "60% Slow Finality (2-round)",
            SLOW_QUORUM_60PCT,
            7usize,
            4usize,
        ),
        (
            "80% Fast Finality (1-round)",
            FAST_QUORUM_80PCT,
            9usize,
            48usize,
        ),
    ] {
        // Full 128-signer shards share 1 WHIR opening; non-matching tail shard adds 1 merge leaf.
        let full_batch_b = single_wire.len() + (full_shards - 1) * per_extra_shard_b;
        let est_cert_b = if full_committee && k_signers == FAST_QUORUM_80PCT {
            joint_wire.len()
        } else if tail_signers == 0 {
            full_batch_b
        } else {
            // Tail shard (`nv = 20` or `22`) is strictly <= `single_wire.len()`.
            full_batch_b + single_wire.len() - 41
        };
        let raw_jorts = k_signers * jorts_raw_b;
        let raw_mldsa = k_signers * ML_DSA_44_SIG_BYTES;
        println!(
            "    - {q_label} (K={k_signers}, {full_shards}x128 + {tail_signers}): raw_Jorts = {:.1} KiB | raw_ML-DSA-44 = {:.1} KiB | Hem_cert <= {:.1} KiB ({:.2}x vs Jorts, {:.2}x vs ML-DSA-44)",
            raw_jorts as f64 / 1024.0,
            raw_mldsa as f64 / 1024.0,
            est_cert_b as f64 / 1024.0,
            raw_jorts as f64 / est_cert_b as f64,
            raw_mldsa as f64 / est_cert_b as f64,
        );
    }
}

fn main() {
    let workers = std::thread::available_parallelism()
        .map(usize::from)
        .unwrap_or(1);
    let full_committee = std::env::var("QSAG_ALPENGLOW_FULL_COMMITTEE")
        .ok()
        .is_some_and(|v| v == "1" || v.eq_ignore_ascii_case("true"));
    let batch_iters = std::env::var("QSAG_ALPENGLOW_ITERS")
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .filter(|&n| n > 0)
        .unwrap_or(15);
    let verify_iters = std::env::var("QSAG_VERIFY_ITERS")
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .filter(|&n| n > 0)
        .unwrap_or(9);

    println!(
        "=========================================================================================="
    );
    println!(
        " QSAG x Solana Alpenglow (`Rotor` + `Votor`, N={ALPENGLOW_VALIDATORS} Validators, threads={workers})"
    );
    println!(
        "=========================================================================================="
    );

    let row_514 = bench_fts_rotor_profile(
        "Frontier::Compact514",
        "128b classical / 64b Grover (16B node, 1-use h=14, fits 1 QUIC pkt)",
        FrontierFtsProfile::Compact514,
        full_committee,
        workers,
        batch_iters,
    );
    let row_770 = bench_fts_rotor_profile(
        "Frontier::Compact770",
        "128b classical / 64b Grover (16B node, 2-use h=15, fits 1 QUIC pkt)",
        FrontierFtsProfile::Compact770,
        full_committee,
        workers,
        batch_iters,
    );
    let row_256 = bench_fts_rotor_profile(
        "Frontier::Full256Bit",
        "PQ128: 256b classical / 128b Grover (32B node, 1-use h=8, < ML-DSA-44)",
        FrontierFtsProfile::Full256Bit,
        true,
        workers,
        batch_iters,
    );

    let jorts_committee_keys = if full_committee {
        FAST_QUORUM_80PCT
    } else {
        512
    };
    let (mut jorts_validators, row_jorts) =
        build_jorts_committee_and_bench_rotor(jorts_committee_keys, workers, batch_iters);

    print_section1_rotor_votor_matrix(&[row_514, row_770, row_256, row_jorts]);

    let next_checkpoint_epoch = (ALPENGLOW_VALIDATORS.div_ceil(jorts_validators.len()) + 1) as u32;
    bench_section2_hem_finality_compression(
        &mut jorts_validators,
        next_checkpoint_epoch,
        workers,
        verify_iters,
        full_committee,
    );

    #[cfg(feature = "vulkan")]
    if let Some((submissions, receipts, fallbacks)) = qsag_agg::vulkan_execution_counts() {
        println!(
            "\nVulkan totals: submissions={submissions} accepted_v5_receipts={receipts} cpu_fallbacks={fallbacks}"
        );
    }
}
