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
cargo run --locked --release -p qsag-cli --example succinct_k_to_1_aggregation
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
