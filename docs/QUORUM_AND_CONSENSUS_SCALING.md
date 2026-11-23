# QSAG quorum custody and consensus scaling

A public committee proof authenticates a signer bitmap and message against validator keys. A regional hierarchy carries the child proofs needed to verify its quorum. A binary IVC root carries one fixed-size proof for a contiguous power-of-two run of shards. These formats answer different bandwidth questions.

## Reading the sizes

- **Public committee.** The two `QSAGHQM2` lengths below come from the same deterministic Jorts fixture with active indices 0, 2 and 3. The test pins the serialized length and SHA-256 digest. Both Canopies use Quintic `Fp5` challenges and the same Stage-0 query schedule. Other signer sets can produce different openings. [Sparse wire vectors](../crates/qsag-agg/src/hem_quintic/tests.rs)
- **Regional hierarchy.** `QSAGHEM\x04` binds each region's policy, message, epoch and quorum. A `PreparedPolicyRegistry` caches the policies and committee roots and exposes a 32 B registry root. Full hierarchy verification checks the attached regional proofs. [Hierarchy and registry](../crates/qsag-agg/src/recursive.rs)
- **Binary IVC.** The public `IvcSubtreeStatement` binds the IVC registry root, message digest, half-open shard interval and total quorums. At every binary depth from 1 through 16 the canonical [DKT26] `SuccinctIvcProof` occupies 639,673 B, exclusive of the statement. A full tree has $2^d$ leaves and $2^d-1$ merges. Transfer time counts proof bits divided by link rate and excludes framing, network latency and computation. [Tree API](../crates/qsag-agg/src/zk_hem/recursive_ivc.rs) · [Root codec](../crates/qsag-agg/src/zk_hem/recursive_ivc/wire.rs)
- **Consensus traffic.** Alpenglow exercises a 64-vote FTS batch and a separate two-region Jorts finality workload. The payload totals count raw signatures before aggregation and exclude headers. [Alpenglow example](../crates/qsag-agg/examples/mock_solana_alpenglow.rs)

For larger validator sets, the payload comparison assumes full participation. A height-20 Jorts signature carries 128 chain nodes and 20 authentication nodes. A hypothetical 96 B aggregate signature with one participation bit per registered validator fits a 1,232 B payload through 9,088 validators. These columns count bytes only.

<!-- BEGIN GENERATED SCALING TABLES -->

### Sparse HemQuintic128 wire vectors (`QSAGHQM2`)

| Canopy | Digest bytes | Encoded bytes, 3 of 4 active |
| --- | --- | --- |
| TurboShake400 | 50 | 360,391 |
| Poseidon2Gl24 | 56 | 381,661 |

### [DKT26] packed-fiber schedules

| log₂ cells | Stage-0 fiber queries |
| --- | --- |
| 16–23 | 267 |
| 24–28 | 266 |

### Binary IVC (`QSAGIVC1`)

| Binary depth | Leaf shards | Internal merges | Root bytes | Root transfer at 100 Mbit/s (ms) |
| --- | --- | --- | --- | --- |
| 1 | 2 | 1 | 639,673 | 51.17 |
| 2 | 4 | 3 | 639,673 | 51.17 |
| 3 | 8 | 7 | 639,673 | 51.17 |
| 4 | 16 | 15 | 639,673 | 51.17 |
| 8 | 256 | 255 | 639,673 | 51.17 |
| 12 | 4,096 | 4,095 | 639,673 | 51.17 |
| 16 | 65,536 | 65,535 | 639,673 | 51.17 |

### Signature payloads in the Alpenglow example

| Workload | Signatures | Bytes per signature | Raw signature bytes |
| --- | --- | --- | --- |
| Votor Compact1122 | 64 | 1,122 | 71,808 |
| Jorts finality, 2 regions × 32 | 64 | 4,328 | 276,992 |

### Validator-set payload arithmetic

| Validators | Raw Jorts signatures at height 20 (MiB) | 96 B signature + bitmap (B) |
| --- | --- | --- |
| 1,500 | 6.83 | 284 |
| 9,088 | 41.39 | 1,232 |
| 10,000 | 45.55 | 1,346 |
| 100,000 | 455.47 | 12,596 |
| 1,048,576 | 4,776.00 | 131,168 |

### Synthesized Verifier Hardware (`QSAG-NI v2`, measured)

| Target and configuration | Mapped area or FPGA resources | Routed clock |
| --- | --- | --- |
| IHP SG13G2, autonomous | 709.61 kGE | — |
| Sky130 HD, autonomous | 784.54 kGE | — |
| ECP5-85F, compact | 23,576 LUT4 | 33.62 MHz |
| ECP5-85F, full rate | 35,153 LUT4 | 29.86 MHz |
| `CL_QSAG_F2`, VU47P wrapper | 314,047 LUT1–6, 290 DSP48E2, 315 RAMB36E2 | — |

<!-- END GENERATED SCALING TABLES -->

The ASIC figures are mapped standard-cell area with autonomous verification and the 32 KiB ROM. The four SRAM banks are black boxes. ECP5 clocks are final routed estimates for the named timing wrappers. The F2 row counts resources for the complete mapped custom-logic wrapper. [ASIC synthesis](../hardware/asic/synth/RESULTS.md) · [ECP5 routing](../hardware/fpga/RESULTS.md) · [F2 synthesis](../hardware/aws_f2/README.md)

## Custody and aggregation

A threshold committee can produce one validator signature under a shared key. Its internal share count affects signing work, while the aggregate sees one validator key. For a symmetric stateful latch quorum, safety requires $2q>n+f$ so that any two certifying quorums intersect outside the fault set.

## Reproduce

```sh
python3 scripts/quorum_and_consensus_scaling.py --write-tables
python3 scripts/quorum_and_consensus_scaling.py --self-test
python3 scripts/quorum_and_consensus_scaling.py --ivc --link-mbps 1000
```

Release workloads and timing columns are in the [performance guide](PERFORMANCE.md).
