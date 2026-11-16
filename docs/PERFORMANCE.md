# Measured performance and scaling demos

This record distinguishes three workloads: full signature shards, a hierarchy of separately verified shards, and recursive split proofs. They have different wire formats and verification costs. The million-validator schedules in [QUORUM_AND_CONSENSUS_SCALING.md](QUORUM_AND_CONSENSUS_SCALING.md) are analytical projections, not runs of those networks.

## Full signature shards on GPU — 2026-11-16

Intel Core i9-12900 (22 workers) with Radeon RX 6750 XT (12 GiB, RADV), on the shared `hbox` build host. `JortsPoseidon2`, all signers active, one shared message, one shard, default `BciksJohnsonQrom128` (tag 4). These are complete aggregates, including canonical serialization roundtrip and successful verification. Proving excludes key generation/signing; verification is the median of three checks. These recorded release builds used **LTO off and 16 codegen units**.

| Signers | Prove | Verify, all workers | Verify, one worker | Serialized bytes | Keygen + signing |
| --- | ---: | ---: | ---: | ---: | ---: |
| 256 | 2.82 s | 5.59 ms | 7.68 ms | 480,342 | 0.8 s |
| 512 | 5.10 s | 4.25 ms | 10.54 ms | 556,830 | 1.5 s |

[Recorded output and proof digests](performance-data/2026-11-16-gpu-shards.txt). Earlier 128-signer measurements are 1.33–1.56 s GPU, 2.94–3.67 s CPU, 445,566 bytes, and 3.0 ms verification (6.2 ms with one worker); see [paper §7](../paper/qsag.typ). Those earlier runs and the newer rows above are separate observations, not a controlled scaling curve.

Reproduce the newer rows on a supported Vulkan host with the pinned toolchain:

```sh
for n in 256 512; do
  QSAG_ACCEL=vulkan QSAG_BENCH_N=$n QSAG_BENCH_SHARD=$n \
    QSAG_BENCH_BATCH=1 QSAG_BENCH_REGIME=4 \
    CARGO_PROFILE_RELEASE_LTO=off CARGO_PROFILE_RELEASE_CODEGEN_UNITS=16 \
    cargo test --locked --release -p qsag-agg --features vulkan --lib \
      bench_consensus_scale -- --ignored --nocapture
done
```

The harness is [`bench_consensus_scale`](../crates/qsag-agg/src/lib.rs). `QSAG_BENCH_N` can exceed the shard size to measure a flat multi-shard aggregate; its bytes and verification then grow with shard count. The Vulkan backend accelerates eligible work; enabling it does not move every prover operation onto the GPU.

## Distinct-validator hierarchy demos — 2026-11-14

The [Beam example](../crates/qsag-agg/examples/mock_ethereum_beam.rs) generated distinct keys, signed subnet statements, built all shard proofs, and verified every child against a prepared registry. Runs used the same i9-12900 / RX 6750 XT host with 22 workers and a 12 GiB process-group cap. Other jobs shared the host. Each subnet contained 128 validators with full participation.

| Validators | Shards | Single-host prove, all shards | Full hierarchy | Full verify, multi-core p50 | Full verify, one-core p50 |
| --- | ---: | ---: | ---: | ---: | ---: |
| 2,048 | 16 | 22.6 s | 6,973.9 KiB | 42.57 ms | 207.39 ms |
| 8,192 | 64 | 99.2 s | 27,889.6 KiB | 109.34 ms | 786.81 ms |
| 16,384 | 128 | 181.9 s | 55,779.1 KiB | 107.63 ms | 1,233.10 ms |

[Recorded output](performance-data/2026-11-14-beam-hierarchy.txt). Warm per-subnet proving was 1.26–1.46 s; the single-host column measures doing **all** subnets on one machine. All three Vulkan runs reported zero CPU fallbacks. The nonmonotone multi-core verification times reflect separate, contended runs.

These are historical implementation measurements: the run used the live aggregation/FTS sources with `qsag-core` and `qsag-quorum` overlaid from commit `6264e1b` in the remote checkout while their replacements were being integrated. The exact aggregate source tree was not pinned to one commit. Later optimizations and wire changes mean these are evidence of exercised scale, not benchmarks of today's exact checkout.

The compact hierarchy commitment printed by this example requires previously verified child evidence. It does **not** replace the full hierarchy for a new verifier. The table counts the full hierarchy. Network hops and transfers in the example's slot-budget table are model inputs; these runs were single-host cryptographic workloads, not a deployed consensus network. Full verification at these sizes exceeded the example's 8 ms target.

Run the current harness:

```sh
QSAG_ACCEL=vulkan QSAG_BEAM_SUBNETS=16,64,128 QSAG_PROVER_JOBS=1 \
  cargo run --locked --release -p qsag-agg --features vulkan \
    --example mock_ethereum_beam
```

The [Alpenglow example](../crates/qsag-agg/examples/mock_solana_alpenglow.rs) separately exercises a 1,200-vote finality committee from a 1,500-validator set, vote packet sizes, batched verification, durable signing, and finality aggregation. Its live `Compact1122` votes and Hem's `JortsPoseidon2` checkpoint signatures are distinct formats.

## Contractive split recursion — 2026-11-16

The current [`SplitSubtreeAggregate` regression](../crates/qsag-agg/src/recursive/split.rs) proves real signature leaves, merges them, roundtrips the wire encoding, verifies the root against a roster root, and rejects tampered ledger edges and folded openings. Recorded CPU release runs on `hbox`:

| Depth | Shards per leaf | Active signers | Root circuit rows | Root prove | Full verification | Total wire bytes | Folded openings |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 2 | 1 | 2 | 1,048,576 | 60.14 s | 42.02 ms | 2,342,406 | 1 |
| 3 | 1 | 4 | 524,288 | 103.87 s | 77.55 ms | 4,149,614 | 2 |
| 2 | 2 | 4 | 1,048,576 | 118.52 s | 45.93 ms | 2,392,782 | 1 |

[Recorded output](performance-data/2026-11-16-split-recursion.txt). Each shard has two registered keys and one active signer. This is a recursion-depth and correctness demonstration on small signer fixtures. The circuit contracts above the leaf: one-shard leaves have 2,097,152 rows; depth-2 internal nodes have 1,048,576; the depth-3 root has 524,288. Root proving includes the deferred-opening fold but excludes earlier leaf/internal proofs and setup. Setup plus construction through root verification took 147.86 s and 294.50 s for the first two rows. The combined depth-2/depth-3 process peaked at 9.36 GiB RSS; the wrapper/fan-in-2 test process peaked at 14.76 GiB.

Leaves and intermediate proofs use bounded-query tag 7; the root uses bounded-query TurboSHAKE tag 10. These are different security profiles from the default tag-4 shard benchmarks. There is one folded WHIR opening per level below the root. The serialized object also contains a ledger; the opening count alone is **not** a constant-size proof claim. Total bytes above include that ledger and all folded openings, rather than just the roughly 1.1 MB root proof.

```sh
cargo test --locked --release -p qsag-agg --lib \
  split_depth_two_and_three_succinct_folded_openings_and_tamper_rejection -- --nocapture
cargo test --locked --release -p qsag-agg --lib \
  split_legacy_leaf_wrapper_and_two_shard_per_leaf_under_memory_cap -- --nocapture
```

## Million-validator projections

The [scaling model](QUORUM_AND_CONSENSUS_SCALING.md) explores an arity-2/4/8/16 hologram-merge topology with one GPU per node. At 1,048,576 validators it projects a 321 KiB root and 4.28 s critical-path proving, excluding inter-node transfers. Merge times and root-opening sizes are fitted/modelled. These are not measurements of the split-recursion format above, nor an end-to-end million-validator proof. The model is useful for choosing shard sizes and fan-in; the measured hierarchy and recursive runs show the implementation costs that still have to converge.

```sh
python3 scripts/quorum_and_consensus_scaling.py --self-test
```
