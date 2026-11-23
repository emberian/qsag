<img src="assets/qsag-mascot.png" alt="qsag mascot" width="120" align="right" />

# qsag

**Post-quantum threshold signing, signature aggregation and key migration.** QSAG lets custodians share a signing key, change the quorum that can use it and compress committee signatures into a publicly verifiable proof.

**Cut-the-Hash** evaluates four secret hash-oracle families inside MPC and builds the public Merkle layers in the clear. **Hem** proves signature verification with sumcheck and Johnson-radius WHIR over the quintic Goldilocks field. A regional verifier can check each committee against a prepared policy registry. A verifier of a contiguous binary tree of Jorts shards can check a single **639,673 B** recursive proof.

[Results and demos](#performance-and-scaling) · [How it works](#how-it-works) · [Try it](#quickstart) · [Paper](paper/qsag.typ) · [Assurance boundaries](ASSURANCE.md)

Research prototype; no external audit. [ASSURANCE.md](ASSURANCE.md) states exact theorem scopes, QROM regimes, hardware signoff status, and the trusted computing base. `qsag` supplies the signing, aggregation, and custody layer; applications supply their consensus and settlement rules.

## Performance and scaling

| Proof | Input and profile | Serialized size |
| --- | --- | ---: |
| Public `QSAGHQM2` | Four keys, three active, `HemQuinticProfile::TurboShake400` | 360,391 B |
| Public `QSAGHQM2` | Same keys, bitmap and message, `HemQuinticProfile::Poseidon2Gl24` | 381,661 B |
| Recursive `QSAGIVC1` | Contiguous Jorts shards, fixed `[DKT26]` relation, tag `0x00` | 639,673 B |

The public sizes are pinned wire vectors. A `HierarchicalHemAggregate` includes one public proof per region, so its wire size grows with the sum of the shard sizes. For binary IVC, adding a level doubles the leaf count while preserving the root length. The current IVC leaf relation admits up to two signers per shard. Lean proves a depth-16 straight-line extraction bound (65,536 shards, up to $2^{64}$ quantum queries) for its three-stage margin schedule. The Rust root uses a separate $2^{23}$-cell schedule. [Public wire vectors](crates/qsag-agg/src/hem_quintic/tests.rs) · [Recursive proof implementation](crates/qsag-agg/src/zk_hem/recursive_ivc/)

Selected signing and verification measurements from [paper §7](paper/qsag.typ).

| Operation | Result |
| --- | --- |
| Prepared Jorts threshold signature, 2-of-3 | 1.0 ms in memory; 81 ms over a simulated WAN |
| QS-A 2-of-3 / QS-B 3-of-7, encrypted channels and synced journal | 4.37 / 5.21 ms |
| Isolated CNF, one 256-hash Keccak wave, 2-of-3 / 3-of-5 | 39.5 / 96.2 ms; 1.8 / 5.9 MiB traffic |
| Pooled blinded MAC check (`OtMesh`, active Beaver sacrifice), 3 parties | 31 µs online; 4.04 ms amortized offline refill |
| Compact1122, verify 1,200 votes | 1.23 s on one core; 158–187 ms on eight threads |
| SpongeMacaroon, three caveats | 161 B; 1.8 µs verify |

## How it works

### Threshold signing: keep only the secret hashes in MPC

Cut-the-Hash evaluates four secret oracle families under MPC, checks the custodians' contributions, opens the boundary digests, and computes the public tree above them in the clear. Secret computation is at most 16 hashes deep for SLH-DSA and 4 for the native formats, independent of tree height.

For **SLH-DSA (FIPS 205)**, the output is byte-identical to a single signer's signature on matched key and randomness. Three engines serve it: a 256-lane bitsliced 2-of-3 engine, isolated per-custodian CNF parties (`IsolatedCnfParty`) for honest-majority thresholds ($2(t-1) < n$) over deployment-bound encrypted wire channels, and an authenticated SPDZ engine (`SoftSpokenOT` + active-sacrifice `OtMesh`) for dishonest majorities. A separate dealerless protocol threshold-signs **ML-DSA-44/65/87 (FIPS 204)**.

| Format | Purpose | Signature size |
| --- | --- | --- |
| **Baggy** | Stateless signing; cached public upper layers, pruned PORS+FP few-time tree | At most 71,654 B |
| **Jorts** / **JortsPoseidon2** | Stateful, one online round after preprocessing; Poseidon2 variant feeds Hem | 4,328–4,776 B |
| **Compact1122** | Single-use live votes; SIMD batch verification | 1,122 B; 1,218 B with 96-byte header |

### Quorum switching: share a key without reusing a leaf

**BeltLatch** logs and syncs `(leaf, intent)` on two separate 4,096-byte high-water-mark pages before releasing a share, backed by external TPM 2.0 NV counters (`--anchor-tpm-nv`), disjoint-device mounts (`--anchor-dir`), and hypervisor `VMGENID` fork guards (`--anchor-vmgenid`). **QS-A** assigns disjoint leaf spaces to committees; **QS-B** and **3-of-5 / 4-of-5 CommitteeHandoffJorts** certify leaves under symmetric, weighted, tree-composed, or Cachin–Tackmann $B^3$ asymmetric quorum intersection (including dealerless wire MSP enrollment).

### Hem aggregation and zero knowledge

All three proof formats use $\mathbb F_{p^5} = \mathbb F_p[X]/(X^5-3)$ with $p=2^{64}-2^{32}+1$.

- **Public committees.** `prove_hem_quintic_128` and `verify_hem_quintic_128` use 50-byte TurboSHAKE256 or seven-limb Poseidon2-GL-w24 Canopy digests. All 138 non-S-box trace columns are pinned to canonical zero on inactive slots. `prove_hierarchical_hem_prepared` and `verify_hierarchical_hem_prepared` compose the proofs against a `PreparedPolicyRegistry` (`QSAGHEM\x04`).
- **Private statements.** zk-Hem v2 uses fresh Stage-0 tree nonces and leaf salts, with joint masking for LogUp lookups. Its single-prover and split-share encodings are `QSAGZKH2` and `QSAGZKS2`. The public and hiding schedule certificates bound QROM error below $2^{-128}$ for all 13 table sizes from $2^{16}$ to $2^{28}$ cells at $Q\le 2^{64}$.
- **Recursive roots.** `prove_ivc_tree` and `verify_ivc_tree` use `IvcTreeStepRelation` to check two child WHIR openings and fold their public-matrix claims with a degree-two sumcheck. [Binary IVC](crates/qsag-agg/src/zk_hem/recursive_ivc.rs)

## Quickstart

The workspace pins Rust `1.99.1` and has zero `crates.io` runtime dependencies.

```sh
# Known-answer tests and supported formats.
cargo run --release -p qsag-cli -- kat
cargo run --release -p qsag-cli -- info

# Generate an SLH-DSA key, sign a file, verify it.
umask 077 && D=$(mktemp -d /tmp/qsag.XXXXXX) && printf 'hello\n' > "$D/msg"
cargo run --release -p qsag-cli -- keygen --scheme slh-dsa-shake-128f \
  --secret-out "$D/sk.json" --public-out "$D/pk.json" --ephemeral-unanchored
cargo run --release -p qsag-cli -- sign --secret "$D/sk.json" --in "$D/msg" \
  --out "$D/sig.json" --ephemeral-unanchored
cargo run --release -p qsag-cli -- verify --public "$D/pk.json" --in "$D/msg" --sig "$D/sig.json"

# 128-bit QROM quintic public aggregation (--hem-profile quintic-turbo | quintic-gl24):
cargo run --release -p qsag-cli --example succinct_k_to_1_aggregation
cargo run --release -p qsag-cli --example threshold_slh_dsa_quickstart
```

## Wallets, migration, and capabilities

| Component | What it provides |
| --- | --- |
| `qsag-hd`, `qsag-addr` | Dealerless module-lattice key hierarchies, committed watch-only inventories, Bech32m PQ addresses, and hybrid keys |
| `qsag-migrate` | Local `QSAGZKH2` and collaborative `QSAGZKS2` ownership proofs across 19 CLI kinds, including Bitcoin/Taproot/Ethereum secp256k1, Solana Ed25519, BLS12-381 and Zcash NU7 Sapling, Orchard, ZIP-2005 Ironwood and ZIP-2007 Transparent. `hem::collab::Engine::new_anchored` burns `tape_id()` against an `ExternalMonotoneAnchor` before round 1 and uses nine-triple Toom-3 multiplication over `Fp5`. |
| `qsag-policy` | Stateful velocity, allowlist, and window rules checked before custodians release shares |
| `SpongeMacaroon`, `PqBiscuit`, `QSAGCAU1` | Keyed-sponge macaroons, offline one-time-signature biscuits, and unlinkable zero-knowledge capability presentations |
| `qsag-cred` | Threshold ML-DSA and Poseidon2 OPRFs. Blind credential issuance uses 438 repetitions of three-party Goldilocks MPC-in-the-head. Selective disclosure and private multisignatures use zk-Hem v2. |

## Verification and hardware

Across the three Lean 4.35 packages, the audits accept **148,052 declarations**, including **78,465 theorems in 401 modules**. Six kernels accept the challenge exports for each package (326 theorems, 35 definitions, 18/18 runs). The two Aeneas packages connect Rust MIR to the specification, including all 54 extracted quintic WHIR definitions. The implementation checks include 317 cross-language vectors, 319 rejected mutations and 18/18 detected compiled clause-drop mutants. [Assurance evidence](ASSURANCE.md)

- **QSAG-NI v2.** The autonomous verifier consumes serialized `QSAGZKH2` and `QSAGHQM2` proofs. Its mapped logic uses 709.61 kGE on IHP SG13G2 and 784.54 kGE on Sky130 HD, excluding SRAM. All eight Lattice ECP5-85F bitstreams meet routed timing, including the compact and full-rate cores at 33.62 and 29.86 MHz against 20 MHz targets. [ASIC results](hardware/asic/synth/RESULTS.md) · [FPGA results](hardware/fpga/RESULTS.md)
- **ASS2-0P5 / Dregg-64.** The 64-bit GF180MCU-D 5 V custody enclave targets the 56-pad wafer.space `SLOT_0P5X0P5`. Two-ring hardware W^X reserves peripheral access for the immutable 4 KiB resident ROM and runs owner-signed SRAM applets behind a hardware fence. [Programming guide](hardware/ass2/PROGRAMMING_GUIDE.md)
- **CL_QSAG_F2.** The AWS F2 HDK wrapper integrates two verifier engines and three isolated custody vats in 314,047 LUT1–6, 290 DSP48E2 and 315 RAMB36E2. Rust-to-Verilator cosimulation covers autonomous proof verification and a 32,768-cycle reset scrub. AFI deployment requires AWS-supported replacements for customer DNA_PORT and SYSMON identity and entropy sources. [F2 shell and deployment boundary](hardware/aws_f2/README.md)

Superseded hardware prototypes and non-manufacturable academic PDK runs are archived in [`history/`](history/README.md).

## Repository map

| Crates / directory | Contents |
| --- | --- |
| `qsag-core`, `qsag-quorum`, `qsag-fts` | Hash-based signatures, MPC engines, quorum switching, hardware anchors, few-time votes |
| `qsag-agg`, `qsag-accel`, `qsag-asm` | Hem / `HemQuintic128` / `zk-Hem v2` / `QSAGIVC1`, Vulkan & AWS F2 backends, SIMD & certified assembly kernels |
| `qsag-hd`, `qsag-addr`, `qsag-policy`, `qsag-cred`, `qsag-migrate`, `qsag-ass2` | Wallet, capability, credential, 19-kind migration, and `ASS2-0P5` enclave host SDK |
| `qsag-cli` | CLI (`qsag`, synced bijectively to `dregg-sig`) and runnable examples |
| `lean/`, `aeneas/`, `validation/` | Protocol proofs, MIR extractions, six-kernel replay and differential validation |
| `hardware/` | Verifier ASIC and FPGA implementations, the ASS2 enclave and carrier, and the AWS F2 shell |

[Paper](paper/qsag.typ) · [Assurance boundaries](ASSURANCE.md) · [Hardware assurance matrix](docs/MIL_STD_ASSURANCE_MATRIX.md) · [Security and constant-time proofs](docs/SECURITY_AND_CT_PROOFS.md)

## License

Authored by ember arlynx (`<ember@lunar.town>`). Licensed under either [Apache-2.0](LICENSE-APACHE) or [MIT](LICENSE-MIT), at your option.
