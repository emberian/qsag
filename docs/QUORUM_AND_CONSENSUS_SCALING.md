# QSAG quorum custody and consensus scaling

Engineering assessment, reconciled 2026-11-14. The numerical tables retain the older affine-v6 calibration and explicit deployment hypotheses; they are not current prover benchmarks. Habr24 rows are historical: those regimes and wire tags are now rejected. The current default is Johnson QROM. No new hardware benchmark was run for this documentation update.

## Executive finding

QSAG addresses two independent problems: Hem aggregates signatures from independently controlled validator keys, while threshold custody distributes control of each signing key. A validator fleet does not need threshold custody to use Hem. Conversely, a custody committee does not replace a consensus validator set: distributing one key among custodians still yields one validator vote.

The implementation does **not yet establish the requested 150 ms end-to-end consensus path, sub-millisecond Hem verification, or constant-size two-level recursive proof**. The older affine v6 measurements are seconds of proving and tens of milliseconds of verification at a small batch size; newer GPU and prepared-verifier implementations are not represented by that calibration. The hierarchy in `recursive.rs` verifies every regional proof and commits to their contents. The compact outer proof checks only the public commitment chain; authorization requires `VerifiedHierarchicalHemEvidence` obtained by checking the real children and bound to the same registry, epoch, message, threshold, regime and child digests. The useful engineering destination is larger jointly witnessed batches, bounded-memory parallel proving, and eventually a genuine recursive verifier circuit. Calling concatenation recursion would conceal the dominant scaling cost.

## Reproduction and interpretation

Run from the repository root:

```sh
python3 scripts/quorum_and_consensus_scaling.py --self-test
python3 scripts/quorum_and_consensus_scaling.py --self-test -o ./scaling-report.json
```

The second command writes the summary and numerical tables to `./scaling-report.json`. The model uses only the Python standard library; self-test performs bounded arithmetic and small source/document reads, with no build, network, GPU initialization, or prover execution. `--write-tables` regenerates the marked block below. Self-test checks exact equality of every generated table, independent arithmetic identities, invalid-input boundaries, and selected source drift guards. It does not certify prose, cryptography, or the accuracy of historical benchmark measurements.

Use `--help` for sensitivity parameters. For example, `--proof-bytes 500000 --verify-ms 25 --gpu-fraction 0.5 --gpu-kernel-speedup 4` changes hypothetical batch costs without changing the checked-in report. No hardware speedup is inferred from a GPU's marketing FLOPS. Bytes are decimal B; MB means decimal million bytes. GiB is binary. Durations are explicitly labelled. All bandwidth totals count one delivered copy, not network-wide gossip traffic.

## Evidence and model equations

The calibration is the affine v6 `bench_affine_regimes`, K=8, Intel Core i9-12900, as recorded in an earlier paper snapshot. The [current paper source](../paper/qsag.typ) may use newer results; this model retains its named calibration constants. Habr24 capacity-proximity regimes have since been retired; their rows are historical calibration only. The Johnson schedule avoids that capacity claim, but its integration still needs the CWYZ decomposition and concrete checker reduction. Neither label resolves the paper's outstanding multi-round QROM Fiat–Shamir extraction or trace-to-verifier linkage obligations. Old pre-v6 numbers are deliberately excluded from the model. The reported decimals are rounded observations, not distributions or p99 estimates; no raw benchmark artifact was available in the inspected report.

There are three distinct quantitative layers:

1. **Exact arithmetic from specified inputs:** raw payload is `N × signature_bytes`; base trace storage is `N × rows_per_signer × 256 × 8`. The PCS bound is on the flattened polynomial: under the default 24-variable shard (`DEFAULT_SHARD_PCS_NUM_VARS`), `2^24 / (rows_per_signer × 256)` signers per shard, not `2^24` signature-verification rows. Hence a default Jorts shard has 128 signers and its base witness alone occupies 128 MiB. The PCS itself admits 28 variables (`MAX_PCS_NUM_VARS`), so an explicitly configured shard can hold 16 times as many signers at 16 times the memory. The allowed 16-polynomial batch can hold 2,048 Jorts signers and needs 2 GiB of base witnesses alone. PCS extension buffers, Merkle trees, scratch space and parallel copies increase peak RSS substantially. The default code uses two shards per batch; the hypothetical table requires an explicit larger batch configuration.
2. **Repeated measured-job envelope:** `ceil(N/8)` independent jobs, each charged the reported K=8 Johnson bytes and time. The final partial job is charged a full job. This is a conservative scheduling/billing convention, not a proof-size upper bound for production committees: statement bitmaps, larger registries and key validation change costs. Sum-of-standalone-proof bytes are labelled as such, not exact serialized merge bytes. This baseline exhibits why blindly repeating small batches does not yield compression.
3. **Large-batch hypothesis:** each batch up to the configured capacity is assigned a total proof-size budget and verification time. Defaults are illustrative round numbers, **not predictions fitted from K=8**. Every proof budget must include committee-sized bitmaps and public-statement encoding. Reference proving work is `N/8 × 4.90 s`, a linear-work extrapolation with unknown large-batch error; no claim is made that FFT, Merkle or sumcheck scaling stays exactly linear. A CPU improvement divides this entire reference-host work by a user-supplied relative speedup. Because the reference code already uses bounded parallel workers, this factor must not be interpreted as a core count or another free division by the reference machine's cores.

For a region containing `j` hypothetical independent batch proofs of `P` bytes, merging gives `jP − 40(j−1)` bytes: remove repeated 41-byte top-level headers and add one byte per branch. This equation requires that `P` already describes each leaf against the same full regional registry. The hierarchy serialization then gives exactly `76 + Σ(124 + regional_proof_bytes)`. Those framing constants come from `to_bytes` in [lib.rs](../crates/qsag-agg/src/lib.rs) and [recursive.rs](../crates/qsag-agg/src/recursive.rs). The resulting numerical root sizes are conditional on the hypothetical child sizes, not exact predictions of real proof output. They include the existing hierarchy wrapper, even for the single-region Solana sizing row. An ordinary non-hierarchical aggregate can omit that wrapper.

GPU sensitivity uses Amdahl's law: `T_gpu = T_reference × ((1−f) + f/s) + overhead` per batch, where `f` is the accelerable share of **whole-prover wall time**, `s` the acceleration of that share, and overhead includes transfers, launches, synchronization and receipt processing. The table sums batches serially on one hypothetical GPU. CPU and GPU columns are alternatives against the same reference, not compounded improvements. At the default fractions, the nonaccelerated work alone remains a substantial fraction of the total. Required reference-host equivalents are ideal throughput lower bounds `ceil(reference_work/deadline)`, assuming perfect distribution; they do not prove deadline latency, schedulability or sufficient memory.

<!-- BEGIN GENERATED SCALING TABLES -->

### Reported calibration (not rerun here)

| Profile / regime | K | Proof B | Prove ms | Verify ms |
| --- | --- | --- | --- | --- |
| Jorts / Habr24 | 8 | 161,112 | 4,300 | 13.550 |
| Jorts / Johnson | 8 | 291,352 | 4,900 | 26.690 |
| Corduroy / Habr24 | 8 | 240,014 | 49,200 | 18.880 |
| Corduroy / Johnson | 8 | 446,254 | 48,840 | 35.330 |

### Raw signatures and trace storage

| Signers | ML-DSA-44 B | Jorts B | Corduroy B | Jorts base trace GiB |
| --- | --- | --- | --- | --- |
| 1,000 | 2,420,000 | 4,328,000 | 76,896,000 | 0.977 |
| 1,500 | 3,630,000 | 6,492,000 | 115,344,000 | 1.465 |
| 8,192 | 19,824,640 | 35,454,976 | 629,932,032 | 8.000 |
| 131,072 | 317,194,240 | 567,279,616 | 10,078,912,512 | 128.000 |
| 1,048,576 | 2,537,553,920 | 4,538,236,928 | 80,631,300,096 | 1,024.000 |

### Repeated K=8 Johnson calibration: payload/work envelope

| Signers | K=8 jobs | Sum standalone proof B | Reference-host work s | Serial verify ms |
| --- | --- | --- | --- | --- |
| 1,000 | 125 | 36,419,000 | 612.500 | 3,336.250 |
| 8,192 | 1,024 | 298,344,448 | 5,017.600 | 27,330.560 |
| 131,072 | 16,384 | 4,773,511,168 | 80,281.600 | 437,288.960 |
| 1,048,576 | 131,072 | 38,188,089,344 | 642,252.800 | 3,498,311.680 |

### Hypothetical Jorts batch parameters

| Batch cap | Proof B/batch | Verify ms/batch | CPU relative speedup | GPU fraction | GPU kernel speedup | GPU overhead ms/batch |
| --- | --- | --- | --- | --- | --- | --- |
| 2,048 | 1,000,000 | 50.000 | 4.000 | 0.800 | 10.000 | 2.000 |

### Hypothetical hierarchy bandwidth (one copy, four-second slot)

| Signers | Regions | Batch proofs | Root B | Root B/s | ML-DSA/raw to root ratio | Serial verify ms |
| --- | --- | --- | --- | --- | --- | --- |
| 1,000 | 1 | 1 | 1,000,200 | 250,050.000 | 2.420 | 50.000 |
| 8,192 | 1 | 4 | 4,000,080 | 1,000,020.000 | 4.956 | 200.000 |
| 131,072 | 16 | 64 | 64,000,140 | 16,000,035.000 | 4.956 | 3,200.000 |
| 1,048,576 | 128 | 512 | 512,000,588 | 128,000,147.000 | 4.956 | 25,600.000 |

### Hypothetical aggregation latency and capacity requirements

| Signers | Batches | Reference work s | Faster CPU s | GPU scenario s | Required speedup to deadline | Ideal reference-host equivalents |
| --- | --- | --- | --- | --- | --- | --- |
| 1,000 | 1 | 612.500 | 153.125 | 171.502 | 4,083.333 | 4,084 |
| 8,192 | 4 | 5,017.600 | 1,254.400 | 1,404.936 | 1,254.400 | 1,255 |

### Trace geometry and verifier chain work

| Profile | w | Chains | Target sum | Verifier chain steps | Rows/signer | Max signers/shard |
| --- | --- | --- | --- | --- | --- | --- |
| Hem Jorts | 4 | 128 | 192 | 192 | 512 | 128 |
| Hem Corduroy (per WOTS layer) | 4 | 128 | 192 | 192 | 8,192 | 8 |
| Custody base-16 (per WOTS layer) | 16 | 64 | 480 | 480 | not Hem | not Hem |

### Johnson QROM query schedule

| log2 blowup | Queries |
| --- | --- |
| 2 | 258 |
| 4 | 130 |
| 6 | 88 |
| 8 | 66 |

<!-- END GENERATED SCALING TABLES -->

## For Solana / @toly: what fits a finality budget?

Treat 1,500 validators and 1,000 signatures as the requested sizing case, not a consensus quorum derivation. Alpenglow's rules use stake, not equal-weight validator counts. Votor governs voting/finalization, while Rotor concerns dissemination. Anza's original approximately 150 ms median estimate explicitly excluded computation; it is not an available 150 ms proving allowance on top of network delay. The original one-round and two-round paths are protocol alternatives, not a guarantee that every finalization uses the same number of certificates. ([Anza design introduction](https://www.anza.xyz/blog/alpenglow-a-new-consensus-for-solana))

The requested ML-DSA-44 baseline is 2,420,000 B for a thousand signatures. This is a comparison of signature payloads under different signing schemes: Hem currently cannot compress ML-DSA-44 signatures. The relevant Hem input alternatives are Jorts WOTS+C/XMSS or Corduroy FORS/WOTS+C hypertrees. Even after aggregation, those individual signatures still travel from validators to aggregators. Proof compression reduces downstream certificate traffic; it does not eliminate signature ingress. Blockspace savings apply only if the protocol actually stores those signatures or certificates on chain; off-chain votes do not automatically consume that blockspace.

The hypothetical large-batch row expresses a conditional compression benefit against raw ML-DSA, but the repeated measured-job baseline expands that payload dramatically. A claim of succinct bandwidth at this scale therefore requires a real large-batch proof measurement. Its amortization comes from shared WHIR openings within one jointly witnessed batch; independent completed proofs cannot acquire that benefit merely by merging.

The critical path is `vote collection + custody online path + leaf proving + merge/transport + final verification`. Multiply relevant certificate work by the actual number of vote phases and recipients; do not equate a per-certificate number with total network traffic. A 3-of-5 QS-A loopback online result near 0.56 ms excludes offline staging, durable `fsync`, WAN delivery and production ceremony costs. It supports a narrow local online result, not a sub-millisecond global committee SLA. Full FIPS 205 dishonest-majority signing is a separate, much more expensive path in the paper.

The Johnson reference verifier already exceeds a sub-millisecond target for one small proof. Increasing the number of independent proofs adds work. Multicore verification can reduce latency across leaves, but public-input hashing, registry checks, scheduling and memory remain. The table's ideal capacity counts allocate the *entire* finality target to proving, making them optimistic lower bounds. Meeting the real deadline requires tighter budgets and tail-latency measurements, or moving aggregation off the immediate finality path with an explicit protocol design for delayed certification.

## For Ethereum / @VitalikButerin: subnet and root accounting

Use the requested four-second slot and 8,192-validator subnet as deployment assumptions, not claims about a settled Ethereum specification. The larger populations comprise 16 and 128 such regions. Subnets may work in parallel, so the leaf latency critical path is approximately the slowest subnet, while total system work multiplies by the number of subnets. The generated hierarchy table reports final certificate bytes per slot and bytes per second for a recipient of the whole certificate. Each subnet aggregator additionally ingests its own raw signatures; raw ingress per second is the appropriate raw table entry divided by the slot duration. Retransmissions, redundant aggregators, messages, keys, eligibility proofs and gossip fanout are excluded.

A root aggregator receives the regional proofs whose sum remains present in the root object. Root merge is serialization/hash/policy work plus any required verification, **not another succinct proving pass**. Serial verifier work is the sum of batch verification times; parallel lower bounds divide independent leaf work by available capacity but retain root and registry overhead. No measurement here establishes root hashing/serialization time or p99 verify latency. A 32-byte root commitment is useful for binding and transport identification, but a verifier still needs the child evidence and independently trusted registry.

For hypothetical genuine two-level recursion, the accounting would instead be `T_slot ≥ max(T_leaf) + T_recursive_prove + transport + T_recursive_verify`, with root bytes equal to the new recursive proof plus public statement/participation data. Those three recursive costs are **unknown**, not zero and not equal to a single K=8 Hem proof. The circuit must verify child transcript challenges, regimes, Merkle/WHIR openings, sumchecks, statement/registry binding and non-overlapping signer sets. It must also bind stake weights and sufficient participation. A commitment without these checks does not establish quorum. This is the main missing component for a bounded root-verification cost as the validator count grows.

Even a recursively succinct cryptographic proof does not automatically make explicit participation data constant-size. A bitmap grows with the committee; hiding it behind a commitment requires proving the weight/quorum rule and specifying how accountability and slashing recover signer identities. Individual public keys remain necessary at leaf verification, and registry updates/key rotation must be authenticated.

## For Zcash / @zooko: custody is orthogonal to aggregation

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

A signature implementation, an aggregation virtual machine, and proof-system components occupy different layers. Throughput comparisons must specify the complete task and parameter set. A research direction or recursive capability is not evidence of measured deployment performance.

| Comparison axis | QSAG Hem / custody | Fair comparison requirement |
| --- | --- | --- |
| Signature task | Stateful Jorts or stateless Corduroy; independent keys supported | Match security, message entropy, key lifetime, statefulness, signer count and key/message bytes |
| Proof backend | Degree-eight sumcheck, GoldilocksExt4, WHIR, affine RS folds | Match proven/conjectural proximity assumptions, query budget and Fiat–Shamir threat model |
| Composition | Shared openings within a batch; child-proof retention across batches | Compare actual recursive proof output against actual concatenated output, including public inputs |
| Performance | Paper-reported small-batch host measurements | Same CPU threads/RAM, release flags, security regime, cold/warm state, serialized bytes and p50/p99 |
| GPU | Persistent prover arena, GPU AIR/sumcheck and WHIR paths exist; older tables do not calibrate them | Measure the current whole prover with transfer, launches, receipts and CPU residual work |
| Custody | Dedicated threshold protocols, preprocessing and durable state | Treat custody as an additional capability; it does not itself accelerate a proof backend |

There is no matched competitor benchmark in this report, so it makes **no numerical throughput or proof-size superiority claim**. A reproducible comparison should record immutable commits for both stacks and raw machine-readable runs at each requested population, separating key generation, signing, aggregation and verification. This is a concrete missing measurement, not a reason to substitute an unrelated microbenchmark.

The [CWYZ26 affine-combiner result](https://arxiv.org/abs/2611.15128) improves the field-size dependence of Reed–Solomon proximity gaps. In this repository, the Johnson QROM query formula yields the generated schedule. That is a soundness/parameter choice, not an empirical GPU speedup. The paper separately records incomplete full Johnson mechanization and multi-round QROM extraction; larger challenge fields and query counts alone do not discharge those obligations.

The small-coefficient `M_4` external Poseidon2 matrix can be implemented with additions and doubling rather than general field multiplication. The inspected CPU code expresses multiplication by the constant two; the algebra permits replacing it with doubling. Calling this “zero-mul Poseidon2” would be misleading: nonlinear `x^7` S-boxes and other layers still require multiplication, and no end-to-end runtime reduction follows without measurement. See [core Poseidon2](../crates/qsag-core/src/sponge/poseidon2.rs), [accelerator implementation](../crates/qsag-accel/src/poseidon2.rs), and [Vulkan shader](../crates/qsag-accel/shaders/poseidon2_perm12.comp).

Likewise, `z=2, S=480` is not the current Hem trace parameter set. The inspected [custody parameter code](../crates/qsag-core/src/tsw_baggy.rs) supports the base-sixteen target-sum profile in the generated geometry table; Hem uses base four. If `z` denotes pinned zero trailing digits, the paper explicitly distinguishes its full-digest profile from such encodings: narrowing the accepted digest space changes security accounting. If `z` denotes another construction's parameter, that construction must be specified before assigning trace savings. Fixed sum removes checksum chains and fixes verifier chain work, but does not remove digest decoding, counter grinding, endpoint compression, Merkle authentication or FORS work. Trace compactness must be measured for the exact accepted signature language.

## GPU and deployment work that would change the answer

The RX 6750 XT RDNA2 Vulkan path now includes a persistent prover arena, AIR/sumcheck and WHIR integration in `acceleration.rs`, `arithmetize.rs` and `pcs.rs`, as well as a [hardware benchmark entry point](../crates/qsag-accel/examples/rdna2_vulkan_bench.rs), [backend](../crates/qsag-accel/src/vulkan.rs), and shader kernels. The older kernel-only calibration below is not a measurement of that integrated path. The GPU table is therefore a sensitivity analysis only. Kernel receipt checking and CPU revalidation must be included where enabled; accelerating Poseidon2 alone may leave Keccak commitments, extension arithmetic, sumcheck, NTTs and memory traffic dominant.

The next useful gates are:

1. Measure joint batches at the actual shard/batch geometries, including full regional registry bitmaps, serialization and peak memory. Record CPU topology, worker count, regime and raw proof sizes. Keep historical measurements separately versioned.
2. Profile full-prover fractions before offloading; then run the integrated prover on the named GPU with identical statements and security settings. Report both compute time and complete wall time. Verify output independently on CPU.
3. Measure custody on authenticated WAN links with offline inventory depletion, active faults and durable reservation latency included. Validate the custody-to-Hem signature adapter rather than assuming profile compatibility.
4. Implement and benchmark a genuine recursive verifier relation if constant-size root certification is required. Until then, budget root bandwidth and verification as sums over child proofs.
5. Exercise protocol-level quorum weight, duplicate signer rejection, stale epoch rejection, equivocation accountability, key rotation and tail latency. The arithmetic model deliberately does not infer these consensus properties from signature validity.

These are engineering obligations attached to this analysis, not claims that work has already been completed. They preserve the distinction between an achievable local custody fast path, a succinct jointly witnessed signature batch, and a scalable network finality protocol.
