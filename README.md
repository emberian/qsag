<img src="assets/qsag-mascot.png" alt="qsag mascot" width="120" align="right" />

# qsag

**Post-quantum threshold signing and signature aggregation for wallets, custodians, and validators.** Split control of a signing key among custodians, change which quorum signs without changing the public key, and compress signatures from independent validators into hash-based proofs. Rust, with Lean 4 proofs at the protocol, extracted-MIR, and assembly layers; CPU and Vulkan provers; synthesizable verifier and custody hardware.

Two ideas do most of the work. **Cut-the-Hash** runs only the secret parts of a hash-based signature inside MPC, then builds its public Merkle layers in the clear. **Hem** proves that a batch of signatures verifies, using Goldilocks-field sumcheck and WHIR polynomial commitments, with recursive merges for larger sets. Neither needs elliptic-curve pairings or a trusted setup.

**Measured:** 128 signatures aggregated in **1.33–1.56 s on a Radeon RX 6750 XT**, verified in **3.0 ms**, with a **435 KiB proof**. Full GPU shards now reach **512 signers in 5.10 s**. Hierarchy demos have exercised **16,384 distinct validator keys**; contractive binary recursion has run through **depth 3**. These are different workloads, detailed below.

[Results and demos](#performance-and-scaling) · [How it works](#how-it-works) · [Try it](#quickstart) · [Paper](paper/qsag.typ) · [Assurance boundaries](ASSURANCE.md)

Research prototype; no external audit. The proofs cover named components and models, with open obligations in the deployed end-to-end security composition. `qsag` supplies the signing layer; applications supply their consensus and settlement rules.

## Performance and scaling

Recorded release runs, with settings and selected raw output in [the benchmark record](docs/PERFORMANCE.md). GPU measurements use an RX 6750 XT (12 GiB, RADV); the newer 256/512-signer runs use an i9-12900 host, 22 workers, LTO off, and 16 codegen units. Proving excludes key generation and signing.

| Full Hem shard, default tag 4 | Prove, GPU | Prove, CPU | Verify, multi-core / one worker | Serialized proof |
| --- | ---: | ---: | ---: | ---: |
| 128 signers | 1.33–1.56 s | 2.94–3.67 s | 3.0 / 6.2 ms | 445,566 B |
| 256 signers | **2.82 s** | 5.68 s | 5.59 / 7.68 ms | 480,342 B |
| 512 signers | **5.10 s** | 11.08 s | 4.25 / 10.54 ms | 556,830 B |

CPU prove timings are earlier i9-12900 / Ryzen 9 9950X runs. The newer rows' verify timings come from their GPU-prover host. These are separate measurements on shared machines, not a controlled CPU/GPU speedup comparison.

**Measured validator-set scaling.** The Beam harness generated distinct validator keys and proved and verified all subnet signatures on one i9-12900 + RX 6750 XT. These November 14 runs use the hierarchy format: a new verifier receives and checks every shard proof.

| Validators | 128-signer shards | Prove all shards, one host | Full verification, multi-core p50 | Full hierarchy |
| --- | ---: | ---: | ---: | ---: |
| 2,048 | 16 | 22.6 s | 42.57 ms | 6.81 MiB |
| 8,192 | 64 | 99.2 s | 109.34 ms | 27.24 MiB |
| 16,384 | 128 | 181.9 s | 107.63 ms | 54.47 MiB |

Warm per-subnet proving was 1.26–1.46 s, with zero reported GPU fallbacks. The [run record](docs/PERFORMANCE.md#distinct-validator-hierarchy-demos--2026-11-14) includes the historical source configuration, single-core timings, and network-model boundary. The example's compact summary commitment needs already-verified child evidence; it is not a standalone signature certificate.

**Measured recursive depth.** The newer split construction verifies child sumchecks in-circuit and folds deferred PCS claims into one WHIR opening per level below the root. Real signature fixtures passed depth-2 and depth-3 proving, root verification, wire roundtrips, and tamper rejection. The internal circuit shrinks from **1,048,576 to 524,288 rows**. In the November 16 CPU run, complete depth-2/depth-3 objects were **2.34 / 4.15 MB**, verifying in **42.02 / 77.55 ms**. These fixtures have **2 / 4 active signers**, use bounded-query tags 7/10, and measure recursion rather than validator population. [Timings, total wire sizes, and commands](docs/PERFORMANCE.md#contractive-split-recursion--2026-11-16).

**Projected million-validator scaling.** The separate [hologram merge model (fan-in up to 16)](docs/QUORUM_AND_CONSENSUS_SCALING.md) explores up to 1,048,576 validators: approximately **321 KiB** and **4.28 s critical-path proving**, with one GPU per tree node and no inter-node transfer time. Merge timings and root-opening sizes are modelled. This is a target for the recursive pipeline, not a measured million-validator run or the wire size of today's split proofs.

Other measured operations ([paper §7](paper/qsag.typ)):

| Operation | Result |
| --- | --- |
| Prepared Jorts threshold signature, 2-of-3 | 1.0 ms in memory; 81 ms over a simulated WAN |
| QS-A 2-of-3 / QS-B 3-of-7, encrypted channels and synced journal | 4.37 / 5.21 ms |
| Isolated CNF, one 256-hash Keccak wave, 2-of-3 / 3-of-5 | 39.5 / 96.2 ms; 1.8 / 5.9 MiB traffic |
| Pooled blinded MAC check, 3 parties | 31 µs online; 4.04 ms amortized offline refill |
| Compact1122, verify 1,200 votes | 1.23 s on one core; 158–187 ms on eight threads |
| zk-Hem credential, 32 attributes, tag 7 | 0.28 s prove; 19.6 ms one-core verify; 239,507 B |
| SpongeMacaroon, three caveats | 161 B; 1.8 µs verify |

## How it works

### Threshold signing: keep only the secret hashes in MPC

A hash-based signature publishes most of the digests its signer computes. Cut-the-Hash evaluates four classes of secret operation under MPC, checks the custodians' contributions, opens the boundary digests, and computes the public tree above them normally. Secret computation is at most 16 hashes deep for SLH-DSA and 4 for the native formats, independent of tree height.

For **SLH-DSA (FIPS 205)**, the result is byte-identical to a single signer's output with the same key and randomness, so existing verifiers work unchanged. A bitsliced 2-of-3 engine supplies the fast path; isolated per-custodian CNF parties support honest-majority thresholds including 3-of-5. An authenticated MPC engine supports dishonest-majority configurations with abort. A separate protocol threshold-signs **ML-DSA-44/65/87 (FIPS 204)**.

The native hash-based formats trade signature size, state, and proving cost:

| Format | Purpose | Signature size |
| --- | --- | --- |
| **Baggy** | Stateless signing; cached public upper layers, pruned few-time tree | At most 71,654 B |
| **Jorts** / **JortsPoseidon2** | Stateful, one online round after preprocessing; Poseidon2 variant feeds Hem | 4,328–4,776 B |
| **Compact1122** | Single-use live votes; SIMD batch verification | 1,122 B; 1,218 B with the demo's 96-byte header |

### Quorum switching: share a key without reusing a leaf

Stateful signatures require each one-time leaf to be spent at most once, even across partitions, crashes, and snapshots. **BeltLatch** logs and syncs `(leaf, intent)` before releasing a share. External TPM, hypervisor, or disjoint-device anchors detect rollback beyond the journal's own failure model.

**QS-A** assigns disjoint leaf spaces to signing committees. **QS-B** requires a certificate that a quorum logged the same leaf and message before release. Safety requires every pair of certifying quorums to intersect outside each tolerated fault set ($2q > n + f$ for symmetric quorums). Weighted, threshold-tree, and asymmetric quorum systems use the same release machinery. Public equivocation evidence supports applications that slash a signer for signing two messages at one leaf.

### Hem: prove signature verification, then merge proofs

Hem starts from public `JortsPoseidon2` signatures. It encodes their verification over the 64-bit Goldilocks field and its quartic extension, checks the trace with LogUp-GKR sumcheck, and commits multilinear witnesses using affine-combiner WHIR. The query schedules use the proven Johnson radius; retired capacity-proximity profiles are rejected.

The default tag-4 profile uses cSHAKE256 and a 16-bit proof of work; tag 9 uses TurboSHAKE256 for the outer commitment hash. Explicit opt-in profiles use bounded-query salted-Merkle accounting. [Security parameters and composition boundaries](docs/SECURITY_AND_CT_PROOFS.md#hem-profile-and-qrom-accounting) matter when comparing proof sizes and timings.

Above a shard, the implementation has full in-circuit hologram merges and **contractive split recursion**. Split nodes verify child sumchecks, bind deferred PCS claims into an accumulator root, and fold homogeneous claims at each level. The native verifier checks the root proof, claim ledger, and folded openings against a **32-byte roster root**. Ordered, nonoverlapping shard-index intervals prevent double-counting within a tree; roster enrollment must enforce validator-key uniqueness across shards. [Implementation](crates/qsag-agg/src/recursive/split.rs) · [affine protocol](crates/qsag-agg/AFFINE_PROTOCOL.md).

Threshold custody and aggregation compose: a custodian committee produces one validator signature; Hem aggregates signatures from many independent validator keys. Custody adds no signature bytes to the aggregate.

## Quickstart

The workspace pins Rust `1.99.1` and has zero `crates.io` runtime dependencies.

```sh
# Known-answer tests and supported formats.
cargo run --release -p qsag-cli -- kat
cargo run --release -p qsag-cli -- info

# Generate an SLH-DSA key, sign a file, verify it.
umask 077 && D=$(mktemp -d /tmp/qsag.XXXXXX) && printf 'hello\n' > "$D/msg"
cargo run --release -p qsag-cli -- keygen --scheme slh-dsa-shake-128f \
  --secret-out "$D/sk.json" --public-out "$D/pk.json"
cargo run --release -p qsag-cli -- sign --secret "$D/sk.json" --in "$D/msg" --out "$D/sig.json"
cargo run --release -p qsag-cli -- verify --public "$D/pk.json" --in "$D/msg" --sig "$D/sig.json"
```

Runnable integration and scaling examples:

```sh
cargo run --release -p qsag-cli --example threshold_slh_dsa_quickstart
cargo run --release -p qsag-cli --example succinct_k_to_1_aggregation
cargo run --release -p qsag-agg --example mock_solana_alpenglow
cargo run --release -p qsag-agg --example mock_ethereum_beam

# Explicit Vulkan shard benchmark; CPU is available without the feature/env setting.
QSAG_ACCEL=vulkan QSAG_BENCH_N=512 QSAG_BENCH_SHARD=512 \
  cargo test --release -p qsag-agg --features vulkan --lib \
    bench_consensus_scale -- --ignored --nocapture
```

The consensus examples are single-host protocol harnesses with explicit network models. [Benchmark commands](docs/PERFORMANCE.md) specify the measured configurations. Stateful CLI vaults require `--anchor-dir <dir>` on a disjoint device, `--anchor-tpm-nv <index>`, or `--anchor-vmgenid`; use `--ephemeral-unanchored` for disposable test keys.

## Wallets, migration, and capabilities

The same custody machinery supports the rest of a wallet's signing lifecycle:

| Component | What it provides |
| --- | --- |
| `qsag-hd`, `qsag-addr` | Dealerless module-lattice key hierarchies, committed watch-only inventories, Bech32m PQ addresses, and hybrid keys |
| `qsag-migrate` | Local and threshold zero-knowledge ownership proofs for secp256k1, Ed25519, Pallas, and BLS12-381, bound to a PQ address—even when the chain has only seen a public-key hash |
| `qsag-policy` | Stateful velocity, allowlist, and window rules checked before custodians release shares |
| `SpongeMacaroon`, `PqBiscuit` | Offline attenuation using a keyed sponge chain or a public-key-verifiable one-time-signature chain; third-party discharges for macaroons |
| `qsag-cred`, zk-Hem | Threshold ML-DSA, threshold oblivious PRFs, selective-disclosure credentials, private multisignatures, and delegated capability presentations |

A migration proof establishes ownership; the receiving chain or application must implement the settlement rule. [Migration security](crates/qsag-migrate/SECURITY.md).

## Verification and hardware

Lean 4 covers protocol models, compiler-extracted Rust functions, and decoded assembly routines. The proof library forbids `sorry`, custom axioms, `native_decide`, and `Classical.choice`; selected top-level and MIR theorems are replayed across six independent kernels. The [extraction coverage map](aeneas/qsag-verified/extraction-coverage.md) identifies which extracted functions sit on production paths. Differential tests compare executable Lean models and Rust against independent implementations.

This is component-level assurance. Whole-binary Rust refinement, full deployed WHIR/QROM composition, and a complete zk-Hem simulator remain open. [ASSURANCE.md](ASSURANCE.md) states the theorem premises, trusted base, and current boundaries; [proof architecture](docs/PROOF_ARCHITECTURE.md) and [MIR verification](docs/AENEAS_VERIFICATION.md) map the code to the proofs.

Two hardware projects exercise the same primitives:

- **QSAG-NI:** synthesizable verifier coprocessor, ASIC and FPGA flows, simulation, and formal-equivalence checks. [ASIC results](hardware/asic/synth/RESULTS.md) · [FPGA results](hardware/fpga/RESULTS.md).
- **Dregg-180:** 180 nm, 5 V physical custody enclave with capability checks, tamper response, PUF/fuzzy extraction, and NFC circuitry. [Design and physical implementation status](hardware/gf180mcu/README.md).

Synthesis, simulation, and placement results are distinct from fabricated-silicon measurements. Timing closure and physical signoff are tracked in the hardware directories.

## Repository map

Library crates use `no_std` + `alloc`; OS storage, anchors, and transports use `std`.

| Crates / directory | Contents |
| --- | --- |
| `qsag-core`, `qsag-quorum`, `qsag-fts` | Hash-based signatures, MPC engines, quorum switching, durable leaf allocation, few-time votes |
| `qsag-agg`, `qsag-accel`, `qsag-asm` | Hem, recursive and zero-knowledge relations, Vulkan compute, SIMD and certified assembly kernels |
| `qsag-hd`, `qsag-addr`, `qsag-policy`, `qsag-cred`, `qsag-migrate` | Wallet and application protocols above |
| `qsag-cli` | CLI and end-to-end examples |
| `lean/`, `aeneas/`, `validation/` | Protocol proofs, extracted Rust proofs, differential validation |
| `hardware/` | ASIC, FPGA, and custody-enclave implementations |

[Paper](paper/qsag.typ) · [Measured performance](docs/PERFORMANCE.md) · [Scaling model](docs/QUORUM_AND_CONSENSUS_SCALING.md) · [Security and constant-time proofs](docs/SECURITY_AND_CT_PROOFS.md)

## License

Authored by ember arlynx (`<ember@lunar.town>`). Licensed under either [Apache-2.0](LICENSE-APACHE) or [MIT](LICENSE-MIT), at your option.
