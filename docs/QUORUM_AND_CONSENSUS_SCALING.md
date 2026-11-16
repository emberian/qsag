# QSAG quorum custody and consensus scaling

Engineering assessment, recalibrated 2026-11-15 on measured release runs of the current prover. The tables below separate three kinds of number: **measured** (one recorded run on named hardware), **exact** (arithmetic on wire formats), and **projection** (arithmetic on measured constants outside the size at which they were measured). Projections are labelled in their table titles.

## Executive finding

QSAG addresses two independent problems. Hem aggregates signatures from independently controlled validator keys; threshold custody distributes control of one signing key. A validator fleet does not need threshold custody to use Hem, and a custody committee does not replace a validator set: one key shared among custodians is still one vote.

What the current code establishes, per 128-signer Jorts shard (24 PCS variables, default `BciksJohnsonQrom128` regime): a **445,566-byte** proof, **3.67 s** to prove on an Intel Core i9-12900, **1.56 s** on an AMD Radeon RX 6750 XT (RADV NAVI22), and **3.00 ms** to verify on all workers (**6.21 ms** on one core). Shards are independent, so a validator set is proved in parallel, one prover per 128 validators, and verified at 6.21 core-milliseconds per shard.

What it does not establish:

- **Constant-size certificates.** Across shards the certificate is still the shard proofs themselves: 7.1 MB at 2,048 validators and 28.5 MB at 8,192. Verification time is small; bytes are the binding cost.
- **Signature recursion.** `prove_succinct_shard_whir_merge` proves, in one parent circuit, that up to 16 child WHIR *openings* verify. It does not execute a shard's row sumcheck or AIR check, so it does not certify signatures. `verify_succinct_shard_whir_merge` therefore requires `VerifiedHierarchicalHemEvidence`, which is obtained only by verifying every shard proof.
- **A merge of real shard openings.** The merge is measured on 4,096-cell child oracles (12 variables), not on 24-variable shard commitments, and under the bounded-query Poseidon2 regime (tag 8), not the default regime. Parent proofs are not merged again in the current code. Every merge-tree row below is a projection.
- **A sub-slot Solana path through Hem.** Hem does not aggregate the single-packet `Compact1122` votes; it aggregates `JortsPoseidon2` or `CorduroyPoseidon2` signatures. On Solana it is an asynchronous checkpoint over a second signature, and at 1,000–1,500 validators its proofs are larger than the votes.

## Reproduction and interpretation

Run from the repository root:

```sh
python3 scripts/quorum_and_consensus_scaling.py --self-test
python3 scripts/quorum_and_consensus_scaling.py --write-tables
python3 scripts/quorum_and_consensus_scaling.py -o ./scaling-report.txt
```

The model uses only the Python standard library and runs no build, prover, GPU or network code. `--write-tables` regenerates the marked block below. `--self-test` checks the arithmetic identities, the merge-tree shapes, the ratios quoted in this prose, a set of source-drift guards (shard size, merge fan-in, the benchmark's child size and regime, packet constants), and byte equality of the generated block. It does not certify prose, cryptography, or the measurements themselves. `--link-mbps` and `--merge-arity` change the transfer and tree columns of a report written with `-o`; the checked-in tables use the defaults (100 Mbps, k = 4).

Bytes are decimal; MB is 10^6 bytes; GiB is binary. Bandwidth figures count one delivered copy, not network-wide gossip.

## Calibration

All aggregation measurements are single release runs (thin LTO, one codegen unit) with 22 worker threads on an Intel Core i9-12900 (Alder Lake); GPU runs use an AMD Radeon RX 6750 XT (RADV NAVI22) through Vulkan with the Poseidon2 Canopy and WHIR opening work left on the CPU. They are rounded observations, not distributions: there is no p99.

**Shard.** `bench_consensus_scale` with 128 `JortsPoseidon2` signers in one shard (`DEFAULT_SHARD_PCS_NUM_VARS = 24`), all signing one message. Under the default regime (wire tag 4, cSHAKE256 Canopy trees, no bound on oracle queries) repeated CPU runs gave 3.67–3.73 s to prove, 2.7–3.0 ms to verify on all workers and 6.2–6.4 ms on one core; GPU runs gave 1.56–1.57 s. The same proof bytes (and proof digest) come out of the CPU and GPU provers. Under the Poseidon2-12 Canopy regime (tag 7, a 128-bit profile only for at most 2^38 oracle queries) the proof is 360,702 bytes; its 7.24 s prove time was recorded before the latest row-sumcheck speedup and has no GPU measurement, so the model does not use it for timing.

**Opening merge.** `two_child_multistage_release_benchmark` and `four_child_multistage_compression_benchmark` merge the fixed-path WHIR openings of two or four **4,096-cell** oracles under regime tag 8 (Poseidon2-12, no proof of work, 128-bit profile only for Q + 1 ≤ 2^40). Two children: 1.00 s to prove, 123 ms to verify, a 302,547-byte parent against 527,872 bytes of child openings (0.57×). Four children: 1.88 s, 246 ms, 339,643 bytes against 1,055,744 (0.32×). A four-child merge fills 4,133,722 of 4,194,304 padded rows. A 24-variable shard opening has more folding stages and Merkle paths about twice as deep, so its merge relation is larger; that cost has not been measured.

**Votes.** 1,200 `Compact1122` signatures verify in 1.23 s on one core with SIMD multibuffering and in 158–187 ms on eight threads (earlier measurement, unchanged code path).

## Model equations

1. **Exact.** Raw payload is `N × signature_bytes`. A Jorts signer occupies 512 trace rows of 256 columns, so a 24-variable shard holds `2^24 / (512 × 256) = 128` signers and its base witness is 128 MiB. The hierarchy wrapper is `76 + Σ(124 + child_proof_bytes)` (`to_bytes` in [recursive.rs](../crates/qsag-agg/src/recursive.rs)).
2. **Repeated measured shard.** `ceil(N/128)` shards, each charged the measured proof bytes and times; a partial last shard is charged in full. Proving is charged once per shard and can run on as many provers as there are shards; "ideal" prover counts are `ceil(total_work / deadline)` and assume perfect distribution. Direct verification is charged 6.21 core-ms per shard. Several shards can also be proved as one joint batch with a shared opening, which is smaller than the sum of separate proofs; the model does not use it because the prover must then hold every witness.
3. **Merge-tree projection.** A k-ary tree over `S` shards has `ceil(log_k S)` levels and `Σ ceil(S / k^i)` merge provers. Pipelined latency is one shard proof plus one merge per level; each level is charged the time measured for 4,096-cell children. This is a lower bound in two ways: real shard openings are larger, and a second level requires merging parent proofs, which the current relation does not do (it would have to verify the parent's own sumchecks, not only its opening).

<!-- BEGIN GENERATED SCALING TABLES -->

### Measured: one 128-signer Jorts shard (24 variables)

| Regime | Tag | Proof B | CPU prove s | GPU prove s | Verify ms (all workers) | Verify ms (1 core) |
| --- | --- | --- | --- | --- | --- | --- |
| BciksJohnsonQrom128 (cSHAKE256 Canopy, default) | 4 | 445,566 | 3.67 | 1.56 | 3.00 | 6.21 |
| Poseidon2Cdhz25JohnsonQrom128 (Poseidon2-12 Canopy, Q <= 2^38) | 7 | 360,702 | 7.24 | not measured | 6.84 | 13.21 |

### Measured: fixed-path WHIR opening merge (4,096-cell children, tag 8)

| Children | Prove s | Verify ms | Parent B | Children B | Parent / children |
| --- | --- | --- | --- | --- | --- |
| 2 | 1.00 | 123.00 | 302,547 | 527,872 | 0.57 |
| 4 | 1.88 | 246.00 | 339,643 | 1,055,744 | 0.32 |

### Exact: raw signature payload and Hem base trace

| Signers | Compact1122 B | ML-DSA-44 B | Jorts B | Shards | Jorts base trace GiB |
| --- | --- | --- | --- | --- | --- |
| 1,000 | 1,122,000 | 2,420,000 | 4,328,000 | 8 | 0.98 |
| 1,200 | 1,346,400 | 2,904,000 | 5,193,600 | 10 | 1.17 |
| 1,500 | 1,683,000 | 3,630,000 | 6,492,000 | 12 | 1.46 |
| 2,048 | 2,297,856 | 4,956,160 | 8,863,744 | 16 | 2.00 |
| 8,192 | 9,191,424 | 19,824,640 | 35,454,976 | 64 | 8.00 |
| 131,072 | 147,062,784 | 317,194,240 | 567,279,616 | 1,024 | 128.00 |
| 1,048,576 | 1,176,502,272 | 2,537,553,920 | 4,538,236,928 | 8,192 | 1,024.00 |

### Solana / Alpenglow live vote path (400 ms slot, Compact1122)

| Votes | Datagram B | Ingress B / recipient | Mbps over 400 ms | 1-core SIMD verify ms | Cores to verify inside the slot (ideal) |
| --- | --- | --- | --- | --- | --- |
| 1,000 | 1,218 | 1,218,000 | 24.36 | 1,025.00 | 3 |
| 1,200 | 1,218 | 1,461,600 | 29.23 | 1,230.00 | 4 |
| 1,500 | 1,218 | 1,827,000 | 36.54 | 1,537.50 | 4 |

### Solana / Alpenglow asynchronous checkpoint (full shard proofs retained)

| Signers | Shards | Hierarchy B | Raw Jorts / hierarchy | Raw Compact1122 / hierarchy | CPU prove s (one host, serial) | GPU prove s (one GPU, serial) | Verify core-ms |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 1,000 | 8 | 3,565,596 | 1.21 | 0.31 | 29.36 | 12.48 | 49.68 |
| 1,200 | 10 | 4,456,976 | 1.17 | 0.30 | 36.70 | 15.60 | 62.10 |
| 1,500 | 12 | 5,348,356 | 1.21 | 0.31 | 44.04 | 18.72 | 74.52 |

### Lean-Ethereum / Beam subnets (4 s slot, direct verification of every shard)

| Validators | Subnets of 128 | Hierarchy B | Transfer s at 100 Mbps | GPU prove s (parallel, per subnet) | CPU prove s (parallel, per subnet) | Total GPU-s | Verify ms (serial, all workers) | Verify core-ms |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 2,048 | 16 | 7,131,116 | 0.57 | 1.56 | 3.67 | 24.96 | 48.00 | 99.36 |
| 8,192 | 64 | 28,524,236 | 2.28 | 1.56 | 3.67 | 99.84 | 192.00 | 397.44 |

### Projection: pipelined k=4 opening-merge tree (per-level cost from 4,096-cell children)

| Validators | Shards | Tree depth | Merge provers | Pipelined s (GPU shards) | Pipelined s (CPU shards) | Total merge prover-s | Root opening proof B | Signer bitmap B |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 2,048 | 16 | 2 | 5 | 5.31 | 7.42 | 9.38 | 339,643 | 256 |
| 8,192 | 64 | 3 | 21 | 7.19 | 9.30 | 39.40 | 339,643 | 1,024 |
| 131,072 | 1,024 | 5 | 341 | 10.94 | 13.05 | 639.72 | 339,643 | 16,384 |
| 1,048,576 | 8,192 | 7 | 2,731 | 14.69 | 16.80 | 5,123.36 | 339,643 | 131,072 |

### Epoch / finality scale (12 s slots, 384 s epochs)

| Validators | Shards | Sum of shard proofs B | Total GPU-s | GPUs to prove in 12 s (ideal) | GPUs to prove in 384 s (ideal) | Direct verify core-s | Evidence transfer s at 100 Mbps |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 131,072 | 1,024 | 456,259,584 | 1,597.44 | 134 | 5 | 6.36 | 36.50 |
| 1,048,576 | 8,192 | 3,650,076,672 | 12,779.52 | 1,065 | 34 | 50.87 | 292.01 |

### Trace geometry and verifier chain work

| Profile | w | Chains | Target sum | Verifier chain steps | Rows/signer | Signers per 24-variable shard |
| --- | --- | --- | --- | --- | --- | --- |
| Hem Jorts | 4 | 128 | 192 | 192 | 512 | 128 |
| Hem Corduroy (per WOTS layer) | 4 | 128 | 192 | 192 | 8,192 | 8 |
| Custody base-16 (per WOTS layer) | 16 | 64 | 480 | 480 | not Hem | not Hem |

### WHIR query schedules

| log2 blowup | Tag 4 (default) | Tags 5, 7 | Tags 6, 8 |
| --- | --- | --- | --- |
| 2 | 258 | 202 | 216 |
| 4 | 130 | 102 | 109 |
| 6 | 88 | 70 | 74 |
| 8 | 66 | 52 | 56 |

<!-- END GENERATED SCALING TABLES -->

## Solana / Alpenglow: 1,000–1,500 validators, 400 ms slots

Treat the validator counts as sizing cases, not a quorum derivation: Alpenglow's rules use stake. Anza's roughly 150 ms median finality estimate excludes computation ([design introduction](https://www.anza.xyz/blog/alpenglow-a-new-consensus-for-solana)).

**Live path.** A vote is one `Compact1122` signature (1,122 bytes, 32-byte hash nodes, single use) plus a 96-byte header: 1,218 bytes, which fits the 1,232-byte payload of a minimum-MTU IPv6 packet (Solana's `PACKET_DATA_SIZE`) but not the 1,200-byte RFC 9000 floor. The ingress table gives one recipient's vote traffic; at 1,500 votes it is 36.5 Mbps averaged over a 400 ms slot. Verification is the tighter constraint: about 1.03 ms per vote on one core, so 1,500 votes need four cores inside a slot, and the 150 ms fast path needs the eight-thread figure or better. Each vote key signs once, and the signer burns the key in a synced journal before releasing the signature.

**Checkpoint path.** Hem cannot compress those votes: its circuit verifies Poseidon2 signatures, and `Compact1122` is a Keccak scheme. An aggregate certificate needs each validator to also sign the checkpoint with a `JortsPoseidon2` key (4,328 bytes). At these sizes the certificate does not save bytes against the votes: twelve shard proofs for 1,500 signers are 5.35 MB, against 1.68 MB of raw `Compact1122` votes and 6.49 MB of raw Jorts signatures. What it buys is verification: 75 core-milliseconds for 1,500 signers instead of 1.5 core-seconds, by a verifier that never sees the signatures. Proving takes 44 s on one CPU host or 19 s on one GPU, serially, so it runs behind finality as an archival, bridge or light-client proof, or on twelve provers in parallel.

A 3-of-5 QS-A loopback signing result near 0.56 ms excludes offline staging, durable `fsync` and WAN delivery. It is a local online-path figure, not a committee SLA.

## Lean-Ethereum / Beam: 2,048 and 8,192 validators per 4 s slot

Use the four-second slot and 128-validator subnets as deployment assumptions, not claims about a settled specification. Sixteen subnets cover 2,048 validators and sixty-four cover 8,192.

**Proving.** Subnets prove in parallel, so the critical path is one shard: 1.56 s on a GPU, 3.67 s on a CPU. The CPU figure leaves about 1% of a four-second slot (the Beam harness measured 3.97 s warm for the same shard), so a CPU-only subnet aggregator is not a safe design point. One host proving all sixteen subnets itself does not fit either: the harness measured 5.67 s for the sixteen-subnet slot.

**Direct verification.** Verifying every shard proof costs `64 × 3.00 ms ≈ 192 ms` run one after another on all workers, or 397 core-milliseconds spread over cores (25 ms on sixteen cores, ideally). This path needs no recursion and certifies the signatures. Its cost is bytes: 7.1 MB per slot at 2,048 validators and 28.5 MB at 8,192, which is 0.57 s and 2.28 s of a 100 Mbps link. At 8,192 validators dissemination, not proving or verification, is what does not fit a four-second slot.

**What the opening merge changes, and what it does not.** Three objects must be kept apart.

| Object | Checked inside a proof | Checked by the verifier outside it | Authorizes a quorum |
| --- | --- | --- | --- |
| Shard proof (`ShardBatchProof`) | Signature verification of every signer: row sumcheck, AIR, WHIR opening | Public keys, bitmap, message | Yes |
| Compact hierarchy (`SuccinctHierarchicalHemAggregate`) | A Poseidon2 commitment chain over shard summaries | Registry, epoch, message, threshold | Only with `VerifiedHierarchicalHemEvidence` |
| Opening merge (`SuccinctShardWhirAggregate`) | The fixed-path WHIR opening of each child's evaluation claim, bound to its shard header, through the one-table public Hem relation | Registry, per-shard quorum minimum, global quorum sum | Only with `VerifiedHierarchicalHemEvidence` of the same regime |

`VerifiedHierarchicalHemEvidence` is produced by verifying each shard's full proof for the same registry, epoch, message and threshold. So today the merge is a compact statement about openings that an authorizing verifier can use only after it, or a party it trusts, has verified the shard proofs. It reduces what must be re-sent to parties that already trust that evidence. It does not reduce what a trustless verifier must download.

Full in-circuit shard recursion would add the missing half: the parent relation would also run each shard's row sumcheck and AIR evaluation at the opened point, with shards committed in fixed-path mode, so that the parent proof alone certified the signatures. The root would then be one proof plus the signer bitmap, and the per-slot bytes at 8,192 validators would fall from 28.5 MB to a few hundred kilobytes. That relation does not exist yet, and its prover cost is unknown.

**Projection.** If each level of a k = 4 tree cost what the measured four-child merge costs, sixteen subnets would need two levels (1.56 + 2 × 1.88 = 5.3 s) and sixty-four would need three (7.2 s). Neither fits one four-second slot, so the tree would be pipelined across slots, and a single merge of all sixteen children (the relation's maximum fan-in) is unmeasured. Read these rows as the floor for a design that still has to be built.

## Epoch and finality-gadget scale: 131,072 and 1,048,576 validators

At this scale per-slot aggregation of every validator is not the design point; the question is what an epoch-level finality proof costs.

- **Proving is parallel and affordable in aggregate.** 1,024 shards are 1,597 GPU-seconds; 8,192 shards are 12,780 GPU-seconds. With one GPU per shard the shard layer still takes 1.56 s. Finishing inside one 384 s epoch needs at least 5 and 34 GPUs respectively; inside one 12 s slot, 134 and 1,065.
- **Direct verification is cheap in time and expensive in bytes.** Verifying every shard proof is 6.4 and 50.9 core-seconds, but the evidence is 456 MB and 3.65 GB: 37 s and 292 s of a 100 Mbps link. A million-validator certificate made of shard proofs is not something a light client downloads.
- **A merge tree would be about 11 to 15 seconds deep.** 1,024 shards form a depth-5 tree and 8,192 a depth-7 tree at k = 4 (the last two levels of the larger tree are partly filled). At the measured per-level cost the pipelined latency is 10.9 s and 14.7 s with GPU shard proving (13.1 s and 16.8 s with CPU shards), using 341 and 2,731 merge provers and 640 and 5,123 prover-seconds of merge work. That is about one 12 s slot of latency and well inside a 384 s epoch, and the root would be one 339,643-byte opening proof plus a signer bitmap of 16 KB or 131 KB.

The last bullet is a projection with three unmet preconditions, restated because the numbers are attractive: the per-level cost was measured on 4,096-cell children, not 24-variable shard openings; merging parent proofs is not implemented; and a tree of opening merges would still certify openings rather than signatures. Until shard-AIR recursion exists, an epoch-scale deployment budgets bytes and verification as sums over shard proofs, or samples committees.

Even a succinct proof does not make participation data constant-size. A bitmap grows with the validator set, and replacing it with a commitment means proving the stake-weight rule in-circuit and deciding how slashing recovers signer identities.

## Custody is orthogonal to aggregation

| Deployment | What the signer controls | What the verifier sees | Current boundary |
| --- | --- | --- | --- |
| Independent validator fleet | One secret key per validator | Hem proof over independent public keys and messages | Supported for the two algebraic Hem profiles; threshold sharing is unnecessary |
| Threshold validator custody | A single validator key distributed among custodians | One signature under that validator's key | Threshold count need not add signature wire bytes; setup, policy and transcript traffic remain off chain |
| Threshold FIPS 205 custody | Shares of a standard SLH-DSA secret key | Standard SLH-DSA signature | Stock verification is distinct from Hem's current algebraic signature verifier |
| Threshold algebraic custody feeding Hem | Shares producing exactly the selected Hem profile's signature | Hem proof over validator keys | `hem_quorum.rs` implements the matching Jorts adapter and lifecycle; separated-party refinement and complete deployment composition remain open |

Hem is neither threshold-only nor a universal signature SNARK. [Its profile enum and verifier](../crates/qsag-agg/src/sig.rs) accept JortsPoseidon2 and CorduroyPoseidon2. These cover individual WOTS+C and FORS-based signature verification. They are not FIPS 205 SLH-DSA wire formats. Generic SHAKE/SHA2 SLH-DSA aggregation would need its own trace and performance evidence. The statement “single standard FIPS 205 / Hem-aggregatable signature” must therefore be read as two separate possible outputs, not as an established interchangeable format.

“Zero on-chain threshold overhead” refers narrowly to signature representation under one public key, compared with the corresponding single-owner signature. Registry/policy commitments, threshold custody governance and any on-chain audit requirements can still add data. Active-malicious custody depends on the selected protocol's corruption threshold, authenticated channels, preprocessing and abort behavior; it does not mean availability against arbitrary malicious custodians. State exhaustion, quorum switching, offline staging and rollback-resistant leaf reservations are operational costs, not optional details.

Current Jorts aggregation keys have a height-six tree and thus a short finite leaf lifetime; deployment at consensus cadence needs authenticated key rotation or a different geometry and new measurements. Corduroy trades stateful one-time-leaf discipline for much larger signatures/traces and its own enforced usage budget. A privacy-oriented application must also account for signer bitmaps and message/registry commitments: aggregation by itself does not provide anonymity or hide participation.

## Comparing signature aggregation systems

A signature scheme, an aggregation proof system and a consensus protocol occupy different layers, and throughput comparisons must fix the complete task and parameter set.

| Comparison axis | QSAG Hem / custody | Fair comparison requirement |
| --- | --- | --- |
| Signature task | Stateful Jorts or stateless Corduroy; independent keys | Match security level, message entropy, key lifetime, statefulness, signer count and key/message bytes |
| Proof backend | Degree-eight sumcheck, GoldilocksExt4, WHIR with affine Reed–Solomon folds, Johnson-radius query counts | Match proven versus conjectured proximity assumptions, query budget and Fiat–Shamir threat model |
| Composition | Shared opening inside a batch; full child proofs across batches; opening-only merge | Compare real recursive proof output against real concatenated output, public inputs included |
| Performance | Single recorded runs on the hardware named above | Same threads and memory, release flags, security regime, cold or warm state, serialized bytes, p50 and p99 |
| GPU | Whole-prover runs with the AIR, sumcheck and NTT stages on the device and Canopy hashing on the CPU | Whole prover including transfers, launches and CPU residual work |
| Custody | Dedicated threshold protocols, preprocessing and durable state | Custody is an additional capability; it does not accelerate a proof backend |

There is no matched competitor benchmark in this report, so it makes **no numerical throughput or proof-size superiority claim**.

The [CWYZ26 affine-combiner result](https://arxiv.org/abs/2611.15128) improves the field-size dependence of Reed–Solomon proximity gaps. In this repository the Johnson query formula yields the generated schedule. That is a soundness and parameter choice, not a speedup, and the paper records which parts of the Johnson analysis and the multi-round QROM extraction are not mechanized.

Fixing the digit sum removes checksum chains and fixes verifier chain work; it does not remove digest decoding, counter grinding, endpoint compression or Merkle authentication.

## Work that would change the answer

1. Commit shards in fixed-path mode and measure the opening merge on real 24-variable shard openings, at fan-in 4 and 16.
2. Put the shard's row sumcheck and AIR evaluation into the parent relation, so that a parent proof certifies signatures and `VerifiedHierarchicalHemEvidence` is no longer needed. Measure its prover.
3. Make parent proofs mergeable, then measure a tree end to end across slots, including transfer.
4. Measure tail latency: every figure here is a single run or a small range.
5. Measure custody on authenticated WAN links with offline inventory depletion, active faults and durable reservation latency included.
6. Exercise protocol-level stake weighting, duplicate-signer rejection, stale-epoch rejection, equivocation accountability and key rotation. The arithmetic model does not infer these from signature validity.

These are obligations attached to this analysis, not claims that the work is done.
