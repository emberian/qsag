//! Ethereum Beam Chain (`4.0 s` Slot) Consensus Aggregation & Optional `3f + 1` DVT Benchmark.
//!
//! Separates the orthogonal layers of post-quantum Ethereum Beam Chain engineering and then
//! composes them into a full-network slot:
//! 1. **Section 1 — Consensus Attestation Subnet Aggregation & `< 8.0 ms` Block Verification**:
//!    - Regional attestation subnets (`4 x 128 = 512` full-density `JortsPoseidon2` validators,
//!      `4 x 32 = 128` `JortsPoseidon2` validators, and mixed `JortsPoseidon2` + stateless
//!      `CorduroyPoseidon2` hypertree subnets) proved under unconditional `BciksJohnsonQrom128`
//!      (refuted capacity-proximity conjectures `[CS25]`/`[KKH26]` are purged).
//!    - Reports per-subnet ingress (`KiB` & `KiB/s`), `HierarchicalHemAggregate` wire size &
//!      compression vs raw PQ / `ML-DSA-44`, exact EVM calldata gas (`16 gas/nonzero` EIP-2028 +
//!      `40 gas/nonzero` EIP-7623 floor), per-subnet aggregator & 4-subnet joint prover latency vs
//!      the `4,000 ms` Beam slot, and multi-core & 1-core block verification (`p50`, `p99`, `min`)
//!      against the **`< 8.0 ms` Beam Chain client verification target**.
//!    - Builds the compact hierarchy commitment and checks it against
//!      `VerifiedHierarchicalHemEvidence` from a full child verification.
//! 2. **Section 2 — Optional Institutional Validator DVT Feeder (`QS-B BftShamirJorts`, `n >= 3f + 1`)**:
//!    - Consensus aggregation (`Hem`) operates over independent validator public keys; threshold
//!      custody is purely an optional per-validator Obol/SSV-style DVT layer protecting a single
//!      validator's signing key across operator nodes with `0 B` extra on-chain overhead.
//!    - Benchmarks `IsolatedQuorumParty` (`QS-B BftShamirJorts`) at real Ethereum DVT cluster sizes:
//!      **`3-of-4` (`n = 4, f = 1, t = 3, q = 3`)** and **`5-of-7` (`n = 7, f = 2, t = 3, q = 5`)**.
//! 3. **Section 3 — Full-Network Slot Critical Path (`M x 128` attesters, `M = 16, 64` by default)**:
//!    - `M` genuinely distinct 128-validator subnets (distinct keys, shard ids and custodian
//!      clusters under one policy registry), each signing its registry-pinned subnet statement.
//!    - Measures the per-subnet aggregator prove (one 128-key shard, warm), the single-host joint
//!      prove of all `M` shards, the hierarchy's wire bytes and calldata gas, and multi-core /
//!      1-core verification of all `M` child proofs (the proposer's check and a first-time
//!      client's check alike).
//!    - The compact commitment (`compress_hierarchical_hem_evidence`) is built and checked against
//!      `VerifiedHierarchicalHemEvidence`, off the authorization path: its outer proof certifies
//!      the summary hash chain, not the child proofs, so it does not replace the hierarchy for a
//!      verifier without evidence.
//!    - Measures attester signing through the durable `FsWalEpochSink` (file record + `fsync`)
//!      next to an in-memory WAL; the WAL directory (`QSAG_WAL_DIR`, default the system temp dir)
//!      is reported with its filesystem type, since a `tmpfs` directory does not measure media.
//!    - Prints the end-to-end `4,000 ms` slot budget: measured phases from this host, network
//!      phases from an explicit model (`QSAG_BEAM_PROPOSAL_MS`, `QSAG_BEAM_GOSSIP_HOP_MS`,
//!      `QSAG_BEAM_PROPOSER_MBPS`, `QSAG_BEAM_CLIENT_MBPS`).
//!    - `QSAG_BEAM_SUBNETS=16,64,128` selects the subnet counts (`0` skips the section);
//!      `QSAG_BEAM_JOINT_WORKERS=n` bounds CPU workers; `QSAG_PROVER_JOBS` (default1) bounds active batches.

use std::path::{Path, PathBuf};
use std::time::Instant;

use qsag_agg::{
    AggSigProfile, EpochWalSink, FsWalEpochSink, HemAggConfig, HierarchicalHemAggregate,
    PreparedPolicyRegistry, ShardHemPolicy, ShardHemWitness, SigError, SignerBitmap, SigningMode,
    StatelessBudgetWalSink, SuccinctHierarchicalHemAggregate, ValidatorKeypair, ValidatorSignature,
    WhirSecurityRegime, aggregate_signatures_with_config, check_hierarchical_hem_commitment,
    compress_hierarchical_hem_evidence, compute_policy_registry_root, hierarchical_hem_message,
    prove_hierarchical_hem_prepared, verify_hierarchical_hem,
    verify_hierarchical_hem_evidence_prepared, verify_hierarchical_hem_prepared,
    verify_succinct_hierarchical_hem_prepared, with_worker_limit,
};
use qsag_core::belt_latch::{BeltLatchRecord, BeltLatchState, DurableWal, WalError};
use qsag_quorum::party_node::IsolatedQuorumParty;
use qsag_quorum::quorum_jorts::{
    QuorumConfig, ShamirCustodian, quorum_jorts_verify, stage_bft_shamir,
};
use qsag_quorum::wire_channel::InMemoryWireMesh;

const BEAM_SLOT_SECONDS: f64 = 4.0;
const BEAM_SLOT_BUDGET_MS: f64 = 4_000.0;
const BEAM_VERIFY_TARGET_MS: f64 = 8.0;
const ML_DSA_44_SIG_BYTES: usize = 2_420;
const SUBNET_SIZE: usize = 128;
/// Two-thirds supermajority of a full 128-validator subnet (`ceil(2 * 128 / 3)`).
const SUBNET_MIN_QUORUM: usize = (2 * SUBNET_SIZE).div_ceil(3);

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

#[derive(Default)]
struct MemStatelessWal {
    used: u64,
}

impl StatelessBudgetWalSink for MemStatelessWal {
    fn reserve(&mut self, _pk_root: &[u8; 32], limit: u64) -> Result<u64, SigError> {
        if self.used >= limit {
            return Err(SigError::StatelessBudgetExhausted);
        }
        self.used += 1;
        Ok(self.used)
    }
}

#[derive(Clone, Debug, Default)]
struct MemBeltWal {
    stored: Option<Vec<u8>>,
}

impl DurableWal for MemBeltWal {
    fn authorize_open(&self, _record: &BeltLatchRecord) -> Result<(), WalError> {
        Ok(())
    }

    fn sync_persist(&mut self, state: &BeltLatchState) -> Result<(), WalError> {
        self.stored = Some(state.to_bytes());
        Ok(())
    }

    fn load(&self) -> Result<Option<BeltLatchState>, WalError> {
        match &self.stored {
            None => Ok(None),
            Some(raw) => BeltLatchState::from_bytes(raw)
                .map(Some)
                .ok_or(WalError::Corrupt),
        }
    }
}

fn seed32(tag: u8, id: u64) -> [u8; 32] {
    let mut s = [0u8; 32];
    s[0] = tag;
    s[1..9].copy_from_slice(&id.to_le_bytes());
    for (i, b) in s[9..].iter_mut().enumerate() {
        *b = tag
            .wrapping_mul(53)
            .wrapping_add(id as u8)
            .wrapping_add(i as u8);
    }
    s
}

fn percentile_sorted(sorted: &[f64], num: usize, den: usize) -> f64 {
    if sorted.is_empty() {
        return 0.0;
    }
    let idx = ((sorted.len() - 1) * num).div_ceil(den);
    sorted[idx.min(sorted.len() - 1)]
}

/// Exact EVM calldata gas accounting:
/// - Standard EIP-2028 calldata cost: `16 gas/nonzero byte + 4 gas/zero byte`.
/// - EIP-7623 (Pectra/Beam calldata floor): `40 gas/nonzero byte + 10 gas/zero byte`.
fn evm_calldata_gas(bytes: &[u8]) -> (u64, u64) {
    let zero_bytes = bytes.iter().filter(|&&b| b == 0).count() as u64;
    let nonzero_bytes = (bytes.len() as u64) - zero_bytes;
    let standard_eip2028 = nonzero_bytes * 16 + zero_bytes * 4;
    let floor_eip7623 = nonzero_bytes * 40 + zero_bytes * 10;
    (standard_eip2028, floor_eip7623)
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

type ValidatorKeypairVec = Vec<ValidatorKeypair>;

fn run_beam_hierarchy_bench(
    label: &str,
    subnet_specs: &[(u64, AggSigProfile, usize, usize)],
    workers: usize,
    verify_iters: usize,
) {
    if let Ok(only) = std::env::var("QSAG_BEAM_ONLY")
        && !label.contains(&only)
    {
        return;
    }

    let regime = WhirSecurityRegime::BciksJohnsonQrom128;
    let epoch_floor = 0u64;
    let beacon_root_msg = b"ethereum.beam.slot.128000.head_root.0x4a7b8c9d0e1f2a3b4c5d6e7f8091a2b3";

    // Parallelize keygen across all available CPU cores (not merely 1 thread per subnet).
    let t_setup = Instant::now();
    let flat_jobs: Vec<(usize, u64, AggSigProfile, u32)> = subnet_specs
        .iter()
        .enumerate()
        .flat_map(|(s_idx, &(shard_id, profile, committee_len, _))| {
            (0..committee_len as u32).map(move |idx| (s_idx, shard_id, profile, idx))
        })
        .collect();
    let job_chunk = flat_jobs.len().div_ceil(workers);
    let generated: Vec<(usize, ValidatorKeypair)> = std::thread::scope(|scope| {
        let handles: Vec<_> = flat_jobs
            .chunks(job_chunk)
            .map(|sub| {
                scope.spawn(move || {
                    sub.iter()
                        .map(|&(s_idx, shard_id, profile, idx)| {
                            let kp = ValidatorKeypair::keygen_deterministic(
                                profile,
                                &seed32(0x31, shard_id),
                                idx,
                            );
                            (s_idx, kp)
                        })
                        .collect::<Vec<_>>()
                })
            })
            .collect();
        handles
            .into_iter()
            .map(|h| h.join().expect("Beam keygen worker panicked"))
            .collect::<Vec<_>>()
            .into_iter()
            .flatten()
            .collect()
    });

    let mut subnet_keypairs: Vec<ValidatorKeypairVec> = subnet_specs
        .iter()
        .map(|&(_, _, len, _)| Vec::with_capacity(len))
        .collect();
    for (s_idx, kp) in generated {
        subnet_keypairs[s_idx].push(kp);
    }

    let policies: Vec<ShardHemPolicy> = subnet_specs
        .iter()
        .zip(&subnet_keypairs)
        .map(|(&(shard_id, _, _, min_quorum), kps)| ShardHemPolicy {
            shard_id,
            custodian_cluster: seed32(0x52, shard_id),
            quorum_keys: kps.iter().map(|kp| kp.pk).collect(),
            minimum_quorums: min_quorum,
        })
        .collect();
    let registry_root = compute_policy_registry_root(&policies);

    // Parallelize validator signing across all cores.
    let mut flat_sign_tasks: Vec<(usize, Vec<u8>, ValidatorKeypair)> =
        Vec::with_capacity(flat_jobs.len());
    for (s_idx, kps) in subnet_keypairs.into_iter().enumerate() {
        let region_msg = hierarchical_hem_message(
            &registry_root,
            &policies[s_idx],
            epoch_floor,
            beacon_root_msg,
        );
        for kp in kps {
            flat_sign_tasks.push((s_idx, region_msg.clone(), kp));
        }
    }
    let sign_chunk = flat_sign_tasks.len().div_ceil(workers);
    let signed_flat: Vec<(usize, ValidatorSignature)> = std::thread::scope(|scope| {
        let handles: Vec<_> = flat_sign_tasks
            .chunks_mut(sign_chunk)
            .map(|sub| {
                scope.spawn(move || {
                    sub.iter_mut()
                        .map(|(s_idx, region_msg, kp)| {
                            let sig = match kp.pk.profile {
                                AggSigProfile::JortsPoseidon2 => {
                                    let mut wal = MemEpochWal::default();
                                    kp.sign_stateful(region_msg, epoch_floor as u32, &mut wal)
                                        .expect("Jorts subnet sign")
                                }
                                AggSigProfile::CorduroyPoseidon2 => {
                                    let mut wal = MemStatelessWal::default();
                                    kp.sign_stateless(region_msg, &mut wal)
                                        .expect("Corduroy subnet sign")
                                }
                            };
                            (*s_idx, sig)
                        })
                        .collect::<Vec<_>>()
                })
            })
            .collect();
        handles
            .into_iter()
            .map(|h| h.join().expect("Beam sign worker panicked"))
            .collect::<Vec<_>>()
            .into_iter()
            .flatten()
            .collect()
    });

    let mut sigs_by_subnet: Vec<Vec<ValidatorSignature>> = subnet_specs
        .iter()
        .map(|&(_, _, len, _)| Vec::with_capacity(len))
        .collect();
    for (s_idx, sig) in signed_flat {
        sigs_by_subnet[s_idx].push(sig);
    }
    let signed_subnets: Vec<(SignerBitmap, Vec<ValidatorSignature>)> = sigs_by_subnet
        .into_iter()
        .map(|sigs| {
            let indices: Vec<usize> = (0..sigs.len()).collect();
            let bm =
                SignerBitmap::from_active_indices(sigs.len() as u32, &indices).expect("bitmap");
            (bm, sigs)
        })
        .collect();
    let setup_ms = t_setup.elapsed().as_secs_f64() * 1_000.0;

    // 1. Measure realistic single-subnet P2P aggregator latency (each Beam attestation subnet has
    //    its own dedicated aggregator node proving 1 subnet within the 4,000 ms slot). Use the
    //    heaviest subnet in mixed topologies (`CorduroyPoseidon2` if present, else subnet 0).
    let rep_idx = policies
        .iter()
        .position(|p| p.quorum_keys[0].profile == AggSigProfile::CorduroyPoseidon2)
        .unwrap_or(0);
    let rep_policy = &policies[rep_idx];
    let rep_region_msg =
        hierarchical_hem_message(&registry_root, rep_policy, epoch_floor, beacon_root_msg);
    let mut sub_cfg = HemAggConfig::default_for(
        rep_policy.quorum_keys[0].profile,
        seed32(0x71, rep_idx as u64),
    );
    sub_cfg.regime = regime;
    let t_sub_prove = Instant::now();
    let _rep_subnet_proof = aggregate_signatures_with_config(
        &rep_policy.quorum_keys,
        &signed_subnets[rep_idx].0,
        &SigningMode::SharedMessage(&rep_region_msg),
        &signed_subnets[rep_idx].1,
        &sub_cfg,
    )
    .expect("single-subnet Beam aggregator proof");
    let single_subnet_prove_ms = t_sub_prove.elapsed().as_secs_f64() * 1_000.0;

    // 2. Measure 4-subnet joint hierarchical proving on one host (`prove_hierarchical_hem`).
    let witnesses: Vec<ShardHemWitness<'_>> = signed_subnets
        .iter()
        .map(|(bitmap, sigs)| ShardHemWitness {
            bitmap,
            signatures: sigs.as_slice(),
        })
        .collect();
    let min_global: usize = policies.iter().map(|p| p.minimum_quorums).sum();
    let mut cfg = HemAggConfig::default_for(AggSigProfile::JortsPoseidon2, seed32(0x73, 99));
    cfg.regime = regime;

    let prepared_registry =
        PreparedPolicyRegistry::new(policies.clone()).expect("valid epoch policy registry");
    let t_prove = Instant::now();
    let agg = prove_hierarchical_hem_prepared(
        &prepared_registry,
        &witnesses,
        epoch_floor,
        beacon_root_msg,
        min_global,
        &cfg,
    )
    .expect("2-layer Beam Chain hierarchical Hem aggregation");
    let joint_prove_ms = t_prove.elapsed().as_secs_f64() * 1_000.0;

    let wire = agg.to_bytes();
    let decoded =
        HierarchicalHemAggregate::from_bytes_canonical(&wire).expect("canonical wire roundtrip");
    assert_eq!(decoded, agg);

    // 3. Measure block proposer / client verification: BOTH multi-core (`std::thread::scope`)
    //    AND single-core (`with_worker_limit(1, ...)`) against epoch-prepared committee roots
    //    (`PreparedPolicyRegistry`), plus cold uncached committee-registry verification.
    assert!(verify_hierarchical_hem(
        &policies,
        epoch_floor,
        beacon_root_msg,
        min_global,
        regime,
        &decoded,
    ));
    assert!(verify_hierarchical_hem_prepared(
        &prepared_registry,
        epoch_floor,
        beacon_root_msg,
        min_global,
        regime,
        &decoded,
    ));

    let measure_verify = |max_w: Option<usize>, prepared: bool| -> (f64, f64, f64) {
        let mut samples = Vec::with_capacity(verify_iters);
        for _ in 0..verify_iters {
            let t0 = Instant::now();
            let call = || {
                if prepared {
                    verify_hierarchical_hem_prepared(
                        &prepared_registry,
                        epoch_floor,
                        beacon_root_msg,
                        min_global,
                        regime,
                        &decoded,
                    )
                } else {
                    verify_hierarchical_hem(
                        &policies,
                        epoch_floor,
                        beacon_root_msg,
                        min_global,
                        regime,
                        &decoded,
                    )
                }
            };
            let ok = match max_w {
                Some(w) => with_worker_limit(w, call),
                None => call(),
            };
            assert!(ok);
            samples.push(t0.elapsed().as_secs_f64() * 1_000.0);
        }
        samples.sort_by(|a, b| a.partial_cmp(b).unwrap());
        (
            samples[0],
            percentile_sorted(&samples, 50, 100),
            percentile_sorted(&samples, 99, 100),
        )
    };
    let (all_min_ms, all_p50_ms, all_p99_ms) = measure_verify(None, true);
    let (_cold_min_ms, cold_p50_ms, _cold_p99_ms) = measure_verify(None, false);
    let (c1_min_ms, c1_p50_ms, c1_p99_ms) = measure_verify(Some(1), true);

    // 4. Measure the compact hierarchy commitment (`SuccinctHierarchicalHemAggregate`). Its outer
    //    proof covers the summary hash chain only; authorizing the quorum still needs evidence
    //    from a full child verification, so the compact object is checked against that evidence.
    let evidence = verify_hierarchical_hem_evidence_prepared(
        &prepared_registry,
        epoch_floor,
        beacon_root_msg,
        min_global,
        regime,
        &decoded,
    )
    .expect("child proofs verify into evidence");
    let t_succ_prove = Instant::now();
    let succinct = compress_hierarchical_hem_evidence(&evidence, cfg.blinding_seed)
        .expect("outer succinct Beam Chain compression");
    let succinct_compress_ms = t_succ_prove.elapsed().as_secs_f64() * 1_000.0;
    let succinct_wire = succinct.to_bytes();
    let succinct_decoded = SuccinctHierarchicalHemAggregate::from_bytes_canonical(&succinct_wire)
        .expect("canonical succinct wire roundtrip");
    assert_eq!(succinct_decoded, succinct);
    let mut succ_samples = Vec::with_capacity(verify_iters);
    for _ in 0..verify_iters {
        let t0 = Instant::now();
        assert!(verify_succinct_hierarchical_hem_prepared(
            &prepared_registry,
            epoch_floor,
            beacon_root_msg,
            min_global,
            regime,
            &succinct_decoded,
            &evidence,
        ));
        succ_samples.push(t0.elapsed().as_secs_f64() * 1_000.0);
    }
    succ_samples.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let succ_p50_ms = percentile_sorted(&succ_samples, 50, 100);
    let succ_min_ms = succ_samples[0];

    // Bandwidth & EVM calldata gas metrics.
    let total_signers = decoded
        .checked_total_quorums()
        .expect("checked_total_quorums");
    let raw_subnet_bytes: Vec<usize> = subnet_specs
        .iter()
        .map(|&(_, prof, count, _)| count * prof.raw_signature_bytes())
        .collect();
    let total_raw_pq_bytes: usize = raw_subnet_bytes.iter().sum();
    let max_subnet_raw_bytes = raw_subnet_bytes.iter().copied().max().unwrap_or(0);
    let total_raw_mldsa_bytes = total_signers * ML_DSA_44_SIG_BYTES;
    let (gas_eip2028, gas_eip7623_floor) = evm_calldata_gas(&wire);

    println!(
        "\n  [{label}] subnets={} | total_validators={total_signers} | min_quorum={min_global} | regime={regime:?}",
        policies.len()
    );
    println!(
        "    Ingress   : max_subnet_raw = {:.1} KiB ({:.1} KiB/s @ 4s slot) | total_raw_PQ = {:.1} KiB | eq_raw_ML-DSA-44 = {:.1} KiB",
        max_subnet_raw_bytes as f64 / 1024.0,
        (max_subnet_raw_bytes as f64 / 1024.0) / BEAM_SLOT_SECONDS,
        total_raw_pq_bytes as f64 / 1024.0,
        total_raw_mldsa_bytes as f64 / 1024.0,
    );
    println!(
        "    Cert Wire : {} B ({:.1} KiB) | compression = {:.2}x vs raw PQ, {:.2}x vs ML-DSA-44 | EVM calldata = {} gas (EIP-2028) / {} gas (EIP-7623 floor)",
        wire.len(),
        wire.len() as f64 / 1024.0,
        total_raw_pq_bytes as f64 / wire.len() as f64,
        total_raw_mldsa_bytes as f64 / wire.len() as f64,
        gas_eip2028,
        gas_eip7623_floor,
    );
    println!(
        "    Compact   : {} B ({:.1} KiB) commitment to the verified hierarchy (not a standalone certificate) | build = {succinct_compress_ms:.1} ms | check vs evidence p50 = {succ_p50_ms:.2} ms (min = {succ_min_ms:.2} ms)",
        succinct_wire.len(),
        succinct_wire.len() as f64 / 1024.0,
    );
    println!(
        "    Prover    : subnet_aggregator = {single_subnet_prove_ms:.2} ms ({:.1}x under 4000 ms slot) | 4-subnet_joint_host = {joint_prove_ms:.2} ms | setup = {setup_ms:.1} ms",
        BEAM_SLOT_BUDGET_MS / single_subnet_prove_ms.max(0.001),
    );
    println!(
        "    Verify    : multi-core p50 = {all_p50_ms:.2} ms, p99 = {all_p99_ms:.2} ms, min = {all_min_ms:.2} ms (cold_registry p50 = {cold_p50_ms:.2} ms | target < {BEAM_VERIFY_TARGET_MS:.1} ms: {}) | 1-core p50 = {c1_p50_ms:.2} ms, p99 = {c1_p99_ms:.2} ms, min = {c1_min_ms:.2} ms",
        if all_p50_ms < BEAM_VERIFY_TARGET_MS {
            "MET"
        } else {
            "MISSED"
        },
    );
}

struct DvtBenchResult {
    label: &'static str,
    n: usize,
    f: usize,
    t: usize,
    q: usize,
    sign_p50_us: f64,
    sign_p99_us: f64,
    verify_us: f64,
    mesh_bytes_per_slot: u64,
    sig_wire_bytes: usize,
}

fn run_qsb_dvt_cluster_bench(
    label: &'static str,
    cfg: QuorumConfig,
    online: &[usize],
    openers: &[usize],
) -> DvtBenchResult {
    let rounds = 8u64;
    let height = 4u8; // 16 leaves per staged test subtree
    let staged =
        stage_bft_shamir(cfg, height, &seed32(0x84, cfg.parties() as u64)).expect("stage QS-B DVT");
    let pk = *staged.tree.public_key();
    let tree = staged.tree.clone();

    let (endpoints, stats) =
        InMemoryWireMesh::connect(cfg.parties(), seed32(0x95, cfg.parties() as u64));
    let mut endpoints_opt: Vec<Option<_>> = endpoints.into_iter().map(Some).collect();
    let mut party_slots: Vec<Option<_>> = staged
        .parties
        .into_iter()
        .map(|mat| {
            let p = mat.party;
            let ep = endpoints_opt[p].take().expect("unique endpoint");
            let cust = ShamirCustodian::new(cfg, tree.clone(), mat, MemBeltWal::default())
                .expect("build ShamirCustodian");
            Some(IsolatedQuorumParty::new(cust, ep).expect("build IsolatedQuorumParty"))
        })
        .collect();

    let mut active_nodes: Vec<_> = online
        .iter()
        .map(|&p| party_slots[p].take().expect("online custodian"))
        .collect();

    let mut sign_samples_us = Vec::with_capacity(rounds as usize);
    let mut last_sig = None;

    for leaf in 0..rounds {
        let mut msg = Vec::from(&b"ethereum.beam.dvt.attestation.slot."[..]);
        msg.extend_from_slice(&(128_000 + leaf).to_le_bytes());
        let msg_ref = msg.as_slice();

        let t_sign = Instant::now();
        let outcomes: Vec<_> = std::thread::scope(|scope| {
            let handles: Vec<_> = active_nodes
                .iter_mut()
                .map(|node| {
                    scope.spawn(move || {
                        node.sign(online, openers, leaf, msg_ref)
                            .expect("QS-B BftShamirJorts isolated DVT sign")
                    })
                })
                .collect();
            handles
                .into_iter()
                .map(|h| h.join().expect("DVT custodian thread panicked"))
                .collect()
        });
        sign_samples_us.push(t_sign.elapsed().as_secs_f64() * 1_000_000.0);

        for out in &outcomes {
            assert_eq!(out.certified_by, online.len());
            assert!(out.blamed.is_empty());
            assert_eq!(out.signature, outcomes[0].signature);
        }
        assert!(quorum_jorts_verify(&pk, msg_ref, &outcomes[0].signature));
        last_sig = Some(outcomes.into_iter().next().unwrap().signature);
    }

    sign_samples_us.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let sig = last_sig.expect("at least one DVT signature");
    let mut last_msg = Vec::from(&b"ethereum.beam.dvt.attestation.slot."[..]);
    last_msg.extend_from_slice(&(128_000 + rounds - 1).to_le_bytes());
    let t_ver = Instant::now();
    for _ in 0..100 {
        assert!(quorum_jorts_verify(&pk, &last_msg, &sig));
    }
    let verify_us = (t_ver.elapsed().as_secs_f64() * 1_000_000.0) / 100.0;

    DvtBenchResult {
        label,
        n: cfg.parties(),
        f: cfg.max_faults(),
        t: cfg.threshold(),
        q: cfg.quorum(),
        sign_p50_us: percentile_sorted(&sign_samples_us, 50, 100),
        sign_p99_us: percentile_sorted(&sign_samples_us, 99, 100),
        verify_us,
        mesh_bytes_per_slot: stats.total_bytes() / rounds,
        sig_wire_bytes: sig.wire_bytes(),
    }
}

fn env_f64(name: &str, default: f64) -> f64 {
    std::env::var(name)
        .ok()
        .and_then(|v| v.parse::<f64>().ok())
        .filter(|v| v.is_finite() && *v >= 0.0)
        .unwrap_or(default)
}

fn backend_label() -> &'static str {
    #[cfg(feature = "vulkan")]
    if std::env::var("QSAG_ACCEL").as_deref() == Ok("vulkan") {
        return "Vulkan";
    }
    "CPU"
}

/// Filesystem type of the mount holding `path` (longest `/proc/self/mounts` prefix), if known.
fn mount_fstype(path: &Path) -> Option<String> {
    let canon = std::fs::canonicalize(path).ok()?;
    let mounts = std::fs::read_to_string("/proc/self/mounts").ok()?;
    let mut best: Option<(usize, String)> = None;
    for line in mounts.lines() {
        let mut fields = line.split_whitespace();
        let (Some(_src), Some(mnt), Some(fstype)) = (fields.next(), fields.next(), fields.next())
        else {
            continue;
        };
        let mnt = mnt.replace("\\040", " ");
        if canon.starts_with(&mnt) && best.as_ref().is_none_or(|(len, _)| mnt.len() > *len) {
            best = Some((mnt.len(), fstype.to_string()));
        }
    }
    best.map(|(_, t)| t)
}

fn wal_root_dir() -> PathBuf {
    std::env::var_os("QSAG_WAL_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir)
}

struct DurableSignStats {
    mem_p50_us: f64,
    mem_p99_us: f64,
    fs_p50_us: f64,
    fs_p99_us: f64,
    dir: PathBuf,
    fstype: String,
}

/// Attester signing latency through an in-memory WAL and through the durable `FsWalEpochSink`
/// (locked file record, `fsync` before the signature is released), on fresh keys each.
fn measure_durable_attester_sign(samples: usize, workers: usize) -> DurableSignStats {
    let master = seed32(0x3D, 0xD0);
    let keys: Vec<ValidatorKeypair> = std::thread::scope(|scope| {
        let per = (2 * samples).div_ceil(workers).max(1);
        let handles: Vec<_> = (0..2 * samples)
            .collect::<Vec<_>>()
            .chunks(per)
            .map(|idxs| {
                let idxs = idxs.to_vec();
                scope.spawn(move || {
                    idxs.into_iter()
                        .map(|i| {
                            ValidatorKeypair::keygen_deterministic(
                                AggSigProfile::JortsPoseidon2,
                                &master,
                                i as u32,
                            )
                        })
                        .collect::<Vec<_>>()
                })
            })
            .collect();
        handles
            .into_iter()
            .flat_map(|h| h.join().expect("durable-sign keygen worker panicked"))
            .collect()
    });
    let msg = b"ethereum.beam.slot.128000.attestation.durable";
    let mut keys = keys.into_iter();

    let mut mem_us = Vec::with_capacity(samples);
    for _ in 0..samples {
        let mut kp = keys.next().expect("mem-WAL key");
        let mut wal = MemEpochWal::default();
        let t0 = Instant::now();
        kp.sign_stateful(msg, 0, &mut wal).expect("mem-WAL sign");
        mem_us.push(t0.elapsed().as_secs_f64() * 1_000_000.0);
    }

    let run_id = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("system clock")
        .as_nanos();
    let dir = wal_root_dir().join(format!("qsag-beam-wal-{}-{run_id}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create durable WAL dir");
    let fstype = mount_fstype(&dir).unwrap_or_else(|| "unknown".to_string());
    let mut fs_us = Vec::with_capacity(samples);
    for (i, mut kp) in keys.enumerate() {
        let pk_root: [u8; 32] = kp.pk.to_bytes()[33..65].try_into().expect("32-byte root");
        let (mut sink, recovered) = FsWalEpochSink::create_new_for_fresh_key(
            dir.join(format!("attester-{i}.wal")),
            &pk_root,
            seed32(0x3E, i as u64),
        )
        .expect("create durable epoch WAL");
        assert!(recovered.is_none());
        let t0 = Instant::now();
        let sig = kp
            .sign_stateful_with_wal(msg, 0, &mut sink)
            .expect("durable-WAL sign");
        fs_us.push(t0.elapsed().as_secs_f64() * 1_000_000.0);
        assert!(qsag_agg::verify_individual_signature(&kp.pk, msg, &sig));
    }
    std::fs::remove_dir_all(&dir).expect("remove durable WAL dir");

    mem_us.sort_by(|a, b| a.partial_cmp(b).unwrap());
    fs_us.sort_by(|a, b| a.partial_cmp(b).unwrap());
    DurableSignStats {
        mem_p50_us: percentile_sorted(&mem_us, 50, 100),
        mem_p99_us: percentile_sorted(&mem_us, 99, 100),
        fs_p50_us: percentile_sorted(&fs_us, 50, 100),
        fs_p99_us: percentile_sorted(&fs_us, 99, 100),
        dir: wal_root_dir(),
        fstype,
    }
}

struct NetworkSlotResult {
    subnets: usize,
    validators: usize,
    joint_host_ms: f64,
    joint_workers: usize,
    hierarchy_bytes: usize,
    shard_gossip_bytes: usize,
    gas_eip2028: u64,
    gas_eip7623: u64,
    verify_all_p50_ms: f64,
    verify_all_p99_ms: f64,
    verify_1c_p50_ms: f64,
    verify_1c_p99_ms: f64,
    evidence_ms: f64,
    compact_build_ms: f64,
    compact_bytes: usize,
    compact_check_p50_ms: f64,
    commitment_only_p50_ms: f64,
}

/// One `M`-subnet slot: sign the registry-pinned statements at `epoch`, prove all `M` shards on
/// this host, and verify every child proof (multi-core and 1-core) as a proposer or first-time
/// client must. The compact commitment is built and checked as well, off the authorization path.
fn run_network_slot(
    subnet_keys: &mut [Vec<(ValidatorKeypair, MemEpochWal)>],
    epoch: u64,
    workers: usize,
    verify_iters: usize,
) -> NetworkSlotResult {
    let subnets = subnet_keys.len();
    let beacon_root_msg = b"ethereum.beam.slot.128000.head_root.full_network";
    let policies: Vec<ShardHemPolicy> = subnet_keys
        .iter()
        .enumerate()
        .map(|(s, keys)| {
            let shard_id = 1_000 + s as u64;
            ShardHemPolicy {
                shard_id,
                custodian_cluster: seed32(0x53, shard_id),
                quorum_keys: keys.iter().map(|(kp, _)| kp.pk).collect(),
                minimum_quorums: SUBNET_MIN_QUORUM,
            }
        })
        .collect();
    let registry_root = compute_policy_registry_root(&policies);
    let region_msgs: Vec<Vec<u8>> = policies
        .iter()
        .map(|p| hierarchical_hem_message(&registry_root, p, epoch, beacon_root_msg))
        .collect();

    let mut flat: Vec<(usize, &mut (ValidatorKeypair, MemEpochWal))> = subnet_keys
        .iter_mut()
        .enumerate()
        .flat_map(|(s, keys)| keys.iter_mut().map(move |k| (s, k)))
        .collect();
    let per = flat.len().div_ceil(workers).max(1);
    let msgs_ref = &region_msgs;
    let signed: Vec<(usize, ValidatorSignature)> = std::thread::scope(|scope| {
        let handles: Vec<_> = flat
            .chunks_mut(per)
            .map(|chunk| {
                scope.spawn(move || {
                    chunk
                        .iter_mut()
                        .map(|(s, (kp, wal))| {
                            let sig = kp
                                .sign_stateful(&msgs_ref[*s], epoch as u32, wal)
                                .expect("full-network subnet sign");
                            (*s, sig)
                        })
                        .collect::<Vec<_>>()
                })
            })
            .collect();
        handles
            .into_iter()
            .flat_map(|h| h.join().expect("full-network sign worker panicked"))
            .collect()
    });
    let mut sigs_by_subnet: Vec<Vec<ValidatorSignature>> = (0..subnets)
        .map(|_| Vec::with_capacity(SUBNET_SIZE))
        .collect();
    for (s, sig) in signed {
        sigs_by_subnet[s].push(sig);
    }
    let active: Vec<usize> = (0..SUBNET_SIZE).collect();
    let bitmap = SignerBitmap::from_active_indices(SUBNET_SIZE as u32, &active).expect("bitmap");
    let witnesses: Vec<ShardHemWitness<'_>> = sigs_by_subnet
        .iter()
        .map(|sigs| ShardHemWitness {
            bitmap: &bitmap,
            signatures: sigs.as_slice(),
        })
        .collect();
    let min_global = SUBNET_MIN_QUORUM * subnets;
    let mut cfg = HemAggConfig::default_for(AggSigProfile::JortsPoseidon2, seed32(0x74, epoch));
    cfg.regime = WhirSecurityRegime::BciksJohnsonQrom128;

    // Arithmetic workers and concurrent trace allocations are separate budgets:
    // QSAG_BEAM_JOINT_WORKERS bounds CPU workers; QSAG_PROVER_JOBS (default1)
    // bounds active heavy batches before allocation, retaining intra-proof parallelism.
    let joint_workers = std::env::var("QSAG_BEAM_JOINT_WORKERS")
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .filter(|&n| n > 0)
        .unwrap_or(workers);
    let prepared = PreparedPolicyRegistry::new(policies.clone()).expect("valid registry");
    let t_joint = Instant::now();
    let agg = with_worker_limit(joint_workers, || {
        prove_hierarchical_hem_prepared(
            &prepared,
            &witnesses,
            epoch,
            beacon_root_msg,
            min_global,
            &cfg,
        )
    })
    .expect("full-network hierarchical Hem");
    let joint_host_ms = t_joint.elapsed().as_secs_f64() * 1_000.0;
    let wire = agg.to_bytes();
    drop(agg);
    let decoded = HierarchicalHemAggregate::from_bytes_canonical(&wire).expect("canonical decode");
    // Everything after the 76-byte registry header is the gossiped shard batches.
    let shard_gossip_bytes = wire.len() - 76;

    let (gas_eip2028, gas_eip7623) = evm_calldata_gas(&wire);

    // Full verification of every child proof against the epoch-prepared registry: this is the
    // work a proposer does before including the hierarchy and a client does on first receipt.
    let measure_full = |max_w: Option<usize>| -> (f64, f64) {
        let mut samples = Vec::with_capacity(verify_iters + 1);
        for _ in 0..=verify_iters {
            let t0 = Instant::now();
            let call = || {
                verify_hierarchical_hem_prepared(
                    &prepared,
                    epoch,
                    beacon_root_msg,
                    min_global,
                    cfg.regime,
                    &decoded,
                )
            };
            let ok = match max_w {
                Some(w) => with_worker_limit(w, call),
                None => call(),
            };
            assert!(ok, "full-network hierarchy must verify");
            samples.push(t0.elapsed().as_secs_f64() * 1_000.0);
        }
        // The first call warms caches and thread pools.
        samples.remove(0);
        samples.sort_by(|a, b| a.partial_cmp(b).unwrap());
        (
            percentile_sorted(&samples, 50, 100),
            percentile_sorted(&samples, 99, 100),
        )
    };
    let (verify_all_p50_ms, verify_all_p99_ms) = measure_full(None);
    let (verify_1c_p50_ms, verify_1c_p99_ms) = measure_full(Some(1));

    // Fresh evidence for the compact commitment using cached registry roots.
    let t_ev = Instant::now();
    let evidence = verify_hierarchical_hem_evidence_prepared(
        &prepared,
        epoch,
        beacon_root_msg,
        min_global,
        cfg.regime,
        &decoded,
    )
    .expect("child proofs verify into evidence");
    let evidence_ms = t_ev.elapsed().as_secs_f64() * 1_000.0;

    let t_comp = Instant::now();
    let compact = compress_hierarchical_hem_evidence(&evidence, cfg.blinding_seed)
        .expect("full-network compact commitment");
    let compact_build_ms = t_comp.elapsed().as_secs_f64() * 1_000.0;
    let compact_wire = compact.to_bytes();
    let compact_decoded = SuccinctHierarchicalHemAggregate::from_bytes_canonical(&compact_wire)
        .expect("canonical compact decode");
    assert_eq!(compact_decoded, compact);
    assert_eq!(
        compact_decoded.checked_total_quorums(),
        Some(subnets * SUBNET_SIZE)
    );
    let median_ms = |f: &dyn Fn() -> bool| -> f64 {
        let mut samples = Vec::with_capacity(verify_iters);
        for _ in 0..verify_iters {
            let t0 = Instant::now();
            assert!(f(), "compact commitment check must pass");
            samples.push(t0.elapsed().as_secs_f64() * 1_000.0);
        }
        samples.sort_by(|a, b| a.partial_cmp(b).unwrap());
        percentile_sorted(&samples, 50, 100)
    };
    let compact_check_p50_ms = median_ms(&|| {
        verify_succinct_hierarchical_hem_prepared(
            &prepared,
            epoch,
            beacon_root_msg,
            min_global,
            cfg.regime,
            &compact_decoded,
            &evidence,
        )
    });
    let commitment_only_p50_ms = median_ms(&|| {
        check_hierarchical_hem_commitment(
            &policies,
            epoch,
            beacon_root_msg,
            min_global,
            &compact_decoded,
        )
    });

    NetworkSlotResult {
        subnets,
        validators: subnets * SUBNET_SIZE,
        joint_host_ms,
        joint_workers,
        hierarchy_bytes: wire.len(),
        shard_gossip_bytes,
        gas_eip2028,
        gas_eip7623,
        verify_all_p50_ms,
        verify_all_p99_ms,
        verify_1c_p50_ms,
        verify_1c_p99_ms,
        evidence_ms,
        compact_build_ms,
        compact_bytes: compact_wire.len(),
        compact_check_p50_ms,
        commitment_only_p50_ms,
    }
}

/// Warm latency of one subnet aggregator proving one full 128-key shard (1 warm-up + 3 timed).
fn measure_subnet_aggregator(keys: &mut [(ValidatorKeypair, MemEpochWal)]) -> (f64, f64) {
    let msg = b"ethereum.beam.slot.127999.subnet_aggregator.calibration";
    let pks: Vec<_> = keys.iter().map(|(kp, _)| kp.pk).collect();
    let sigs: Vec<ValidatorSignature> = keys
        .iter_mut()
        .map(|(kp, wal)| kp.sign_stateful(msg, 0, wal).expect("calibration sign"))
        .collect();
    let active: Vec<usize> = (0..pks.len()).collect();
    let bitmap = SignerBitmap::from_active_indices(pks.len() as u32, &active).expect("bitmap");
    let mut cfg = HemAggConfig::default_for(AggSigProfile::JortsPoseidon2, seed32(0x75, 0));
    cfg.regime = WhirSecurityRegime::BciksJohnsonQrom128;
    let mut samples = Vec::with_capacity(4);
    for _ in 0..4 {
        let t0 = Instant::now();
        aggregate_signatures_with_config(
            &pks,
            &bitmap,
            &SigningMode::SharedMessage(msg),
            &sigs,
            &cfg,
        )
        .expect("subnet aggregator proof");
        samples.push(t0.elapsed().as_secs_f64() * 1_000.0);
    }
    let cold = samples[0];
    let mut warm = samples[1..].to_vec();
    warm.sort_by(|a, b| a.partial_cmp(b).unwrap());
    (cold, percentile_sorted(&warm, 50, 100))
}

fn run_full_network_section(workers: usize, verify_iters: usize) {
    let mut subnet_counts: Vec<usize> = std::env::var("QSAG_BEAM_SUBNETS")
        .unwrap_or_else(|_| "16,64".to_string())
        .split(',')
        .filter_map(|s| s.trim().parse::<usize>().ok())
        .filter(|&m| m > 0)
        .collect();
    if let Ok(only) = std::env::var("QSAG_BEAM_ONLY") {
        subnet_counts.retain(|m| format!("Beam-Network-{m}x{SUBNET_SIZE}").contains(&only));
    }
    subnet_counts.sort_unstable();
    subnet_counts.dedup();
    let Some(&max_subnets) = subnet_counts.last() else {
        return;
    };

    let proposal_ms = env_f64("QSAG_BEAM_PROPOSAL_MS", 500.0);
    let hop_ms = env_f64("QSAG_BEAM_GOSSIP_HOP_MS", 180.0);
    let proposer_mbps = env_f64("QSAG_BEAM_PROPOSER_MBPS", 1_000.0).max(1.0);
    let client_mbps = env_f64("QSAG_BEAM_CLIENT_MBPS", 100.0).max(1.0);
    let backend = backend_label();

    println!(
        "\n------------------------------------------------------------------------------------------"
    );
    println!(
        "[Section 3] Full-Network Slot Critical Path (M x {SUBNET_SIZE} attesters, M = {subnet_counts:?}, backend = {backend})"
    );
    println!(
        "  Each subnet: 128 distinct `JortsPoseidon2` keys, quorum >= {SUBNET_MIN_QUORUM}/128, full participation; one registry per M."
    );

    let t_keygen = Instant::now();
    let total_keys = max_subnets * SUBNET_SIZE;
    let per = total_keys.div_ceil(workers).max(1);
    let flat_keys: Vec<ValidatorKeypair> = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..total_keys)
            .collect::<Vec<_>>()
            .chunks(per)
            .map(|idxs| {
                let idxs = idxs.to_vec();
                scope.spawn(move || {
                    idxs.into_iter()
                        .map(|i| {
                            let shard_id = 1_000 + (i / SUBNET_SIZE) as u64;
                            ValidatorKeypair::keygen_deterministic(
                                AggSigProfile::JortsPoseidon2,
                                &seed32(0x33, shard_id),
                                (i % SUBNET_SIZE) as u32,
                            )
                        })
                        .collect::<Vec<_>>()
                })
            })
            .collect();
        handles
            .into_iter()
            .flat_map(|h| h.join().expect("full-network keygen worker panicked"))
            .collect()
    });
    let mut subnet_keys: Vec<Vec<(ValidatorKeypair, MemEpochWal)>> = (0..max_subnets)
        .map(|_| Vec::with_capacity(SUBNET_SIZE))
        .collect();
    for (i, kp) in flat_keys.into_iter().enumerate() {
        subnet_keys[i / SUBNET_SIZE].push((kp, MemEpochWal::default()));
    }
    let keygen_ms = t_keygen.elapsed().as_secs_f64() * 1_000.0;
    println!(
        "  Keygen    : {total_keys} distinct validator keys in {keygen_ms:.0} ms ({workers} threads)"
    );

    let durable = measure_durable_attester_sign(16, workers);
    println!(
        "  Attester  : sign p50/p99 = {:.1}/{:.1} us (in-memory WAL) | {:.1}/{:.1} us (durable `FsWalEpochSink`, fsync) | WAL dir {} [{}]",
        durable.mem_p50_us,
        durable.mem_p99_us,
        durable.fs_p50_us,
        durable.fs_p99_us,
        durable.dir.display(),
        durable.fstype,
    );
    if durable.fstype == "tmpfs" || durable.fstype == "ramfs" {
        println!(
            "              WAL dir is memory-backed: fsync here is not a media latency; set QSAG_WAL_DIR to a disk."
        );
    }

    // Calibration signs at epoch 0; slot runs use epochs 1.. so every XMSS leaf is used once.
    let (agg_cold_ms, agg_warm_ms) = measure_subnet_aggregator(&mut subnet_keys[0]);
    println!(
        "  Aggregator: one 128-key subnet shard prove = {agg_warm_ms:.1} ms warm p50 (cold first call {agg_cold_ms:.1} ms)"
    );

    let mut results = Vec::with_capacity(subnet_counts.len());
    for (run, &m) in subnet_counts.iter().enumerate() {
        let r = run_network_slot(&mut subnet_keys[..m], 1 + run as u64, workers, verify_iters);
        println!(
            "\n  [Beam-Network-{m}x{SUBNET_SIZE}] validators={} | joint_host_prove = {:.0} ms ({} workers) | shard gossip to proposer = {:.1} KiB ({:.1} KiB/shard)",
            r.validators,
            r.joint_host_ms,
            r.joint_workers,
            r.shard_gossip_bytes as f64 / 1024.0,
            r.shard_gossip_bytes as f64 / 1024.0 / m as f64,
        );
        println!(
            "    Hierarchy : {} B ({:.1} KiB) = what a first-time verifier must receive | calldata {} gas (EIP-2028) / {} gas (EIP-7623 floor)",
            r.hierarchy_bytes,
            r.hierarchy_bytes as f64 / 1024.0,
            r.gas_eip2028,
            r.gas_eip7623,
        );
        println!(
            "    Verify    : all {m} child proofs, prepared registry: multi-core p50/p99 = {:.2}/{:.2} ms | 1-core p50/p99 = {:.2}/{:.2} ms | target < {BEAM_VERIFY_TARGET_MS:.1} ms: {}",
            r.verify_all_p50_ms,
            r.verify_all_p99_ms,
            r.verify_1c_p50_ms,
            r.verify_1c_p99_ms,
            if r.verify_1c_p50_ms < BEAM_VERIFY_TARGET_MS {
                "MET on 1 core"
            } else if r.verify_all_p50_ms < BEAM_VERIFY_TARGET_MS {
                "MET multi-core only"
            } else {
                "MISSED"
            },
        );
        println!(
            "    Compact   : {} B ({:.1} KiB) commitment, reuse-only build {:.1} ms; checked against evidence in {:.2} ms (fresh evidence with prepared registry: {:.1} ms)",
            r.compact_bytes,
            r.compact_bytes as f64 / 1024.0,
            r.compact_build_ms,
            r.compact_check_p50_ms,
            r.evidence_ms,
        );
        println!(
            "                fresh-evidence + build pipeline: {:.2} ms; cached evidence eliminates a second child verification.",
            r.evidence_ms + r.compact_build_ms
        );
        println!(
            "                commitment relation alone: {:.2} ms. It certifies the summary hash chain, not the child proofs or signatures.",
            r.commitment_only_p50_ms,
        );
        results.push(r);
    }

    println!(
        "\n  End-to-end {BEAM_SLOT_BUDGET_MS:.0} ms slot critical path (measured = this host, {backend}; model = assumed network input):"
    );
    print!("  {:<56} {:>8}", "Phase", "Source");
    for r in &results {
        print!(" {:>12}", format!("M={} (ms)", r.subnets));
    }
    println!();
    println!("  {}", "-".repeat(66 + 13 * results.len()));
    let ingress_ms =
        |r: &NetworkSlotResult| r.shard_gossip_bytes as f64 * 8.0 / (proposer_mbps * 1_000.0);
    let client_dl_ms =
        |r: &NetworkSlotResult| r.hierarchy_bytes as f64 * 8.0 / (client_mbps * 1_000.0);
    type PhaseRow<'a> = (
        String,
        &'static str,
        Box<dyn Fn(&NetworkSlotResult) -> f64 + 'a>,
    );
    let rows: Vec<PhaseRow<'_>> = vec![
        (
            "Block proposal + execution".to_string(),
            "model",
            Box::new(|_| proposal_ms),
        ),
        (
            "Attester durable sign (FsWalEpochSink fsync, p50)".to_string(),
            "measured",
            Box::new(|_| durable.fs_p50_us / 1_000.0),
        ),
        (
            "Gossipsub subnet hop".to_string(),
            "model",
            Box::new(|_| hop_ms),
        ),
        (
            format!("Per-subnet aggregator prove (1 x 128, {backend}, warm)"),
            "measured",
            Box::new(|_| agg_warm_ms),
        ),
        (
            "Global aggregation topic hop".to_string(),
            "model",
            Box::new(|_| hop_ms),
        ),
        (
            format!("Proposer ingress of M shard proofs @ {proposer_mbps:.0} Mbps"),
            "model",
            Box::new(ingress_ms),
        ),
        (
            "Proposer verifies all M child proofs (multi-core p50)".to_string(),
            "measured",
            Box::new(|r| r.verify_all_p50_ms),
        ),
        (
            "Block gossip hop".to_string(),
            "model",
            Box::new(|_| hop_ms),
        ),
        (
            format!("Client receives the hierarchy @ {client_mbps:.0} Mbps"),
            "model",
            Box::new(client_dl_ms),
        ),
        (
            "Client verifies all M child proofs (multi-core p50)".to_string(),
            "measured",
            Box::new(|r| r.verify_all_p50_ms),
        ),
    ];
    let mut totals = vec![0.0f64; results.len()];
    for (label, source, f) in &rows {
        print!("  {label:<56} {source:>8}");
        for (i, r) in results.iter().enumerate() {
            let v = f(r);
            totals[i] += v;
            print!(" {v:>12.1}");
        }
        println!();
    }
    println!("  {}", "-".repeat(66 + 13 * results.len()));
    print!("  {:<56} {:>8}", "Total slot wall-clock", "");
    for t in &totals {
        print!(" {t:>12.1}");
    }
    println!();
    print!("  {:<56} {:>8}", "Remaining margin in 4,000 ms slot", "");
    for t in &totals {
        print!(" {:>12.1}", BEAM_SLOT_BUDGET_MS - t);
    }
    println!();
    print!(
        "  {:<56} {:>8}",
        "Single-host contrast: joint prove of all M shards", ""
    );
    for r in &results {
        print!(" {:>12.1}", r.joint_host_ms);
    }
    println!();
    print!("  {:<56} {:>8}", "Off path: compact commitment build", "");
    for r in &results {
        print!(" {:>12.1}", r.compact_build_ms);
    }
    println!();
}

fn run_dvt_section() {
    println!(
        "\n------------------------------------------------------------------------------------------"
    );
    println!(
        "[Section 2] Optional Institutional Validator DVT Feeder (`QS-B BftShamirJorts`, `n >= 3f + 1`)"
    );
    println!(
        "  \"Consensus aggregation (`Hem`) operates over independent validator public keys; threshold custody"
    );
    println!(
        "   is purely an optional per-validator DVT layer (Obol/SSV-style) protecting a single validator's"
    );
    println!("   signing key across operator nodes with `0` extra on-chain bytes.\"");

    let cfg_3_of_4 =
        QuorumConfig::new(3, 4, 1).expect("3-of-4 BFT Shamir config (n=4,f=1,t=3,q=3)");
    assert_eq!(cfg_3_of_4.quorum(), 3);
    let dvt_3_of_4 =
        run_qsb_dvt_cluster_bench("Obol/SSV 3-of-4 (f=1)", cfg_3_of_4, &[0, 1, 2], &[0, 1, 2]);

    let cfg_5_of_7 =
        QuorumConfig::new(3, 7, 2).expect("5-of-7 BFT Shamir config (n=7,f=2,t=3,q=5)");
    assert_eq!(cfg_5_of_7.quorum(), 5);
    let dvt_5_of_7 = run_qsb_dvt_cluster_bench(
        "Obol/SSV 5-of-7 (f=2)",
        cfg_5_of_7,
        &[0, 1, 2, 3, 4],
        &[0, 1, 2],
    );

    println!(
        "\n  {:<24} {:>15} {:>12} {:>12} {:>11} {:>14} {:>12} {:>14}",
        "DVT Cluster Profile",
        "Params(n,f,t,q)",
        "Sign_p50(us)",
        "Sign_p99(us)",
        "Verify(us)",
        "OffChainMesh/s",
        "SigWire(B)",
        "OnChainExtra"
    );
    println!("  {}", "-".repeat(124));
    for d in [dvt_3_of_4, dvt_5_of_7] {
        println!(
            "  {:<24} {:>15} {:>12.1} {:>12.1} {:>11.1} {:>12} B {:>12} {:>14}",
            d.label,
            format!("({},{},{},{})", d.n, d.f, d.t, d.q),
            d.sign_p50_us,
            d.sign_p99_us,
            d.verify_us,
            d.mesh_bytes_per_slot,
            d.sig_wire_bytes,
            "0 B (0.0%)",
        );
    }
}

fn main() {
    let workers = std::thread::available_parallelism()
        .map(usize::from)
        .unwrap_or(1);
    let verify_iters = std::env::var("QSAG_VERIFY_ITERS")
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .filter(|&n| n > 0)
        .unwrap_or(9);

    println!(
        "=========================================================================================="
    );
    println!(
        " QSAG x Ethereum Beam Chain (`4.0 s` Slot, `BciksJohnsonQrom128`, threads={workers})"
    );
    println!(
        "=========================================================================================="
    );
    println!(
        "[Section 1] Consensus Attestation Subnet Aggregation & `< 8.0 ms` Block Verification"
    );
    println!(
        "  Security Regime: `BciksJohnsonQrom128` (unconditional Johnson coding bound; refuted capacity conjectures `[CS25]`/`[KKH26]` purged)."
    );

    // Scenario A: Full-density 4 x 128 = 512 JortsPoseidon2 validators across 4 attestation subnets.
    let jorts_full_subnets = [
        (10, AggSigProfile::JortsPoseidon2, 128, 96),
        (20, AggSigProfile::JortsPoseidon2, 128, 96),
        (30, AggSigProfile::JortsPoseidon2, 128, 96),
        (40, AggSigProfile::JortsPoseidon2, 128, 96),
    ];
    run_beam_hierarchy_bench(
        "Beam-Jorts-4x128-Johnson-Qrom128",
        &jorts_full_subnets,
        workers,
        verify_iters,
    );

    // Scenario B: Medium-density 4 x 32 = 128 JortsPoseidon2 validators across 4 attestation subnets.
    let jorts_32_subnets = [
        (11, AggSigProfile::JortsPoseidon2, 32, 24),
        (21, AggSigProfile::JortsPoseidon2, 32, 24),
        (31, AggSigProfile::JortsPoseidon2, 32, 24),
        (41, AggSigProfile::JortsPoseidon2, 32, 24),
    ];
    run_beam_hierarchy_bench(
        "Beam-Jorts-4x32-Johnson-Qrom128",
        &jorts_32_subnets,
        workers,
        verify_iters,
    );

    // Scenario C: Mixed Stateful (`JortsPoseidon2`) + Stateless Hypertree (`CorduroyPoseidon2`) subnets.
    let mixed_subnets = [
        (100, AggSigProfile::JortsPoseidon2, 32, 22),
        (200, AggSigProfile::JortsPoseidon2, 32, 22),
        (300, AggSigProfile::CorduroyPoseidon2, 4, 3),
        (400, AggSigProfile::CorduroyPoseidon2, 4, 3),
    ];
    run_beam_hierarchy_bench(
        "Beam-Mixed-Jorts+Corduroy-Johnson-Qrom128",
        &mixed_subnets,
        workers,
        verify_iters,
    );

    if std::env::var("QSAG_BEAM_ONLY").is_err() {
        run_dvt_section();
    }
    run_full_network_section(workers, verify_iters);

    if let Some(rss) = peak_rss_mib() {
        println!("\n  Process peak RSS (`VmHWM`): {rss:.1} MiB");
    }
    #[cfg(feature = "vulkan")]
    if let Some((submissions, receipts, fallbacks)) = qsag_agg::vulkan_execution_counts() {
        println!(
            "  Vulkan totals: submissions={submissions} accepted_v5_receipts={receipts} cpu_fallbacks={fallbacks}"
        );
    }
}
