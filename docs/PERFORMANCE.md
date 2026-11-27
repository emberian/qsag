# HemQuintic128 (`QSAGHQM2`) & Regional Hierarchy (`QSAGHEM\x04`) — Canonical Release Profile (`codegen-units = 1`)

Run the workloads below from the repository root on the Linux x86_64 reference server (`AMD EPYC-Milan`, 16 cores / 32 threads) with the pinned toolchain and the workspace release profile. Cargo sets `opt-level = 3`, `lto = "thin"` and `codegen-units = 1`. Use these settings without environment overrides so the benchmark keeps the code-generation configuration used for the release constant-time screen. That screen applies to the audited binaries and kernels. [Cargo profile](../Cargo.toml) · [Constant-time evidence](SECURITY_AND_CT_PROOFS.md#constant-time-screen-of-the-current-release-archives)

## Reference x86_64 server measurements

Measured on `2026-11-23` on `AMD EPYC-Milan` (16 cores / 32 hardware threads, `Linux 6.12.107 x86_64`, `rustc 1.99.1 (58cf8f9c3 2026-10-13)`, canonical workspace `--release` profile `opt-level = 3`, `lto = "thin"`, `codegen-units = 1`, `16 GiB` memory cap, shared multi-tenant host load average `~22–29`). The CLI reports proof size and elapsed prove/verify time for eight signatures on one message (`4.40 s` prove = `4,400 ms`). The Beam harness measures the first subnet separately, then proves and verifies the full hierarchy against a prepared registry (`3-of-4 BftShamirJorts` DVT signing ran in `2.44 ms`, `4,172 B`). Its timings exclude key generation and signing.

| Public committee (`TurboShake400`) | Active / registered | Raw signatures (B) | Proof (B) | Prove (ms) | Verify (ms) |
| --- | ---: | ---: | ---: | ---: | ---: |
| Jorts, shared message | 8 / 8 | 34,624 | 392,971 | 4,400 | 19.49 |

| Beam workload (`TurboShake400`) | Shards | Signers | Hierarchy wire (B) | vs ML-DSA-44 (×) | Subnet 0 prove (ms) | Joint prove (ms) | Verify, all workers (ms) | Verify, one worker (ms) | Gas (EIP-2028) | Gas (EIP-7623) |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 4 × 32 Jorts | 4 | 128 | 2,072,874 | 0.15 | 15,384.3 | 60,995.1 | 32.42 | 69.00 | 33,037,260 | 82,593,150 |
| 16 Jorts + 2 Corduroy | 2 | 18 | 978,020 | 0.04 | 9,383.4 | 23,870.8 | 21.58 | 34.52 | 15,590,564 | 38,976,410 |

```sh
cargo run --locked --release -p qsag-cli --example succinct_k_to_1_aggregation -- --signers 8
cargo run --locked --release -p qsag-agg --example mock_ethereum_beam
```

The 32 B registry root identifies the prepared policies. The `wire` column counts the full encoded hierarchy, including the child evidence checked by a fresh verifier. [CLI fixture](../crates/qsag-cli/examples/succinct_k_to_1_aggregation.rs) · [Beam measurements](../crates/qsag-agg/examples/mock_ethereum_beam.rs)

## Binary IVC (`QSAGIVC1`)

The production codec fixes `SuccinctIvcProof::encoded_len()` at 639,673 B. The first test below checks this size and prints the circuit census. The second exercises the canonical parser's length and tag checks. The opt-in third test builds and verifies trees through depth three with a smaller diagnostic schedule. Its elapsed times apply only to that schedule. [Recursive IVC tests](../crates/qsag-agg/src/zk_hem/recursive_ivc/tests.rs)

```sh
cargo test --locked --release -p qsag-agg --lib zk_hem::recursive_ivc::tests::two_child_step_census -- --exact --nocapture
cargo test --locked --release -p qsag-agg --lib zk_hem::recursive_ivc::tests::tooth_succinct_ivc_proof_rejects_nonzero_profile_tag_and_wrong_length -- --exact
cargo test --locked --release -p qsag-agg --lib zk_hem::recursive_ivc::tests::recursive_tree_depths -- --exact --ignored --nocapture
```

The [scaling report](QUORUM_AND_CONSENSUS_SCALING.md) gives sparse committee vectors, binary-tree sizes and measured synthesis results.

## Radeon RX 6750 XT proof and kernel timings

The 2026-11-27 Vulkan measurements below preceded the integration of the wide seed stream and the current recursive committee relation. The release prover ran on an Intel Core i9-12900 with an AMD Radeon RX 6750 XT (RADV NAVI22, Mesa 24.2.8, Vulkan 1.3.289), Linux 6.11.0-29-generic and rustc 1.99.1. Both paths used the same inputs and prover coins under a 12 GiB host memory limit. Each GPU proof matched the CPU serialization byte for byte and passed the ordinary verifier. The explicit Vulkan paths recorded zero CPU fallbacks. A subsequent release check with the integrated seed stream reproduced identical CPU and GPU bytes for both public profiles, both zero-knowledge profiles and the 639,673-byte recursive root. The recursive proof verified with zero CPU fallbacks.

Proof time includes host arithmetic, transfers and GPU execution. Key generation, signing, device initialization, serialization comparison and verification were outside the timers. The zk-Hem v2 and IVC shapes were prepared in advance. The HemQuintic and zk-Hem v2 rows give the median wall time for each backend across three trials. The IVC row is one full CPU/GPU pair. Speedup is CPU time divided by GPU time.

| Prover and workload | Hash profile | Proof (B) | CPU (ms) | CPU + RX 6750 XT (ms) | Speedup |
| --- | --- | ---: | ---: | ---: | ---: |
| HemQuintic128, 1 Jorts signer | TurboShake400 | 308,531 | 362.849131 | 297.952538 | 1.22× |
| HemQuintic128, 1 Jorts signer | Poseidon2Gl24 | 321,381 | 839.314469 | 383.345850 | 2.19× |
| HemQuintic128, 8 Jorts signers | TurboShake400 | 390,171 | 2,362.787596 | 2,047.012092 | 1.15× |
| HemQuintic128, 8 Jorts signers | Poseidon2Gl24 | 416,205 | 3,395.274132 | 2,155.440756 | 1.58× |
| zk-Hem v2, 1,024 S-box/product pairs | CshakeJohnson400 | 263,544 | 137.599934 | 135.137503 | 1.02× |
| zk-Hem v2, 1,024 S-box/product pairs | TurboShakeJohnson400 | 261,994 | 124.619629 | 124.845565 | 1.00× |
| zk-Hem v2, 16,384 S-box/product pairs | CshakeJohnson400 | 263,874 | 184.800014 | 209.302548 | 0.88× |
| zk-Hem v2, 16,384 S-box/product pairs | TurboShakeJohnson400 | 265,374 | 160.168216 | 177.703715 | 0.90× |
| Recursive IVC, two Jorts committees | Poseidon2Gl24 | 639,673 | 124,729.711327 | 107,235.098220 | 1.16× |

HemQuintic uses a shared message. The v2 relation chains a seventh-power S-box and a multiplication at each step. Its parity test also covers a lookup helper commitment, forward/inverse quintic NTT and three CWYZ fiber folds checked against the scalar oracle. The IVC measurement uses the production DKT26 schedule at 2²³ cells and a 639,673-byte root proof. [HemQuintic workloads](../crates/qsag-agg/src/hem_quintic/tests.rs) · [v2 workloads](../crates/qsag-agg/src/zk_hem/v2/protocol.rs) · [IVC workload](../crates/qsag-agg/src/zk_hem/recursive_ivc/tests.rs)

The standalone benchmark timed one invocation per backend. The five active kernels below matched their CPU references. The proof paths and planted-fault audit also exercise five quintic and Canopy kernels. RADV reported 32-thread subgroups, zero scratch and zero spilled registers across the ten pipelines. Each planted mutation caused a hardware mismatch and a rejected pin. [Kernel benchmark](../crates/qsag-accel/examples/rdna2_vulkan_bench.rs) · [Planted-fault audit](../crates/qsag-accel/tests/vulkan_planted_fault_audit.rs)

| Kernel and workload | CPU (ms) | RX 6750 XT (ms) | Speedup |
| --- | ---: | ---: | ---: |
| Poseidon2-12, 262,144 permutations | 1,111.49 | 14.20 | 78.27× |
| Keccak-f[1600], 262,144 permutations | 34.56 | 18.43 | 1.88× |
| Goldilocks NTT, 2²⁰ points | 34.84 | 8.10 | 4.30× |
| Poseidon2-12 Merkle tree, 2²⁰ leaves | 4,466.55 | 41.78 | 106.91× |
| BDOZ GF(2¹²⁸) dot product, 262,144 pairs | 0.88 | 6.32 | 0.14× |

With the `vulkan` feature, create an audited backend with `VulkanSpirvBackend::try_new_audited()` and call `fp5_session()` on it. Pass the session to `prove_hem_quintic_128_with_vulkan`, `zk_hem::v2::protocol::prove_with_vulkan` or `IvcTreeStepRelation::prove_with_vulkan`. All five limb transforms share one upload and download, and a Canopy stays in device memory from its leaves through the top node. The new push-constant blocks occupy 32–64 bytes. [Vulkan session API](../crates/qsag-accel/src/vulkan/fp5.rs)

```sh
mkdir -p target/vulkan-tmp
export TMPDIR="$PWD/target/vulkan-tmp"
cargo test --release -p qsag-agg --features vulkan --lib vulkan_wire_parity -- --ignored --nocapture --test-threads=1
cargo test --release -p qsag-accel --all-features --test vulkan_planted_fault_audit -- --nocapture
cargo run --release -p qsag-accel --features vulkan --example rdna2_vulkan_bench
```
