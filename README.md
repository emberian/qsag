<img src="assets/qsag-mascot.png" alt="qsag mascot" width="120" align="right" />

# qsag

**Post-quantum threshold signing, succinct WHIR signature aggregation, multi-ecosystem key migration, and verified custody/verifier silicon.** Split control of a signing key among custodians, switch quorums without changing the public key, and compress validator signatures into hash-based proofs—backed by a 331-module constructive Lean 4.35 library (replayed across six independent kernels), `#![no_std]` zero-dependency Rust (bijectively synced with `dregg-sig`), a Vulkan GPU prover, and ASIC/FPGA/AWS-F2 hardware.

Two ideas do most of the work. **Cut-the-Hash** evaluates only the four secret oracle families of a hash-based signature inside MPC, then builds the public Merkle layers in the clear. **Hem** proves that a batch of signatures verifies using Goldilocks-field sumcheck and Johnson-radius WHIR polynomial commitments (`[CWYZ26]`, `[DKT26]`), with constant-verifier-state recursive merges (`SuccinctSubtreeAggregate`, contractive `SplitSubtreeAggregate`, and depth-independent `QSAGIVC1`). Neither uses elliptic-curve pairings or a trusted setup.

**Measured:** 128 signatures aggregated in **1.33–1.56 s on a Radeon RX 6750 XT**, verified in **3.0 ms** (`445,566 B` default `Ext4` tag 4; **`362,391 B` / `381,045 B` in the 128-bit QROM quintic public profile `QSAGHQM2`**). Full GPU shards reach **512 signers in 5.10 s**. Hierarchy demos have exercised **16,384 distinct validator keys**; contractive split recursion and constant-byte-size `QSAGIVC1` (`26,185 B` diagnostic / `639,673 B` `[DKT26]` root at every depth) have run through **depth 3 (`8` shards)**.

[Results and demos](#performance-and-scaling) · [How it works](#how-it-works) · [Try it](#quickstart) · [Paper](paper/qsag.typ) · [Assurance boundaries](ASSURANCE.md)

Research prototype; no external audit. [ASSURANCE.md](ASSURANCE.md) states exact theorem scopes, QROM regimes, hardware signoff status, and the trusted computing base. `qsag` supplies the signing, aggregation, and custody layer; applications supply their consensus and settlement rules.

## Performance and scaling

Recorded release runs, with settings and raw output in [the benchmark record](docs/PERFORMANCE.md). GPU measurements use an RX 6750 XT (12 GiB, RADV). Proving excludes key generation and signing.

| Full Hem shard, default tag 4 | Prove, GPU | Prove, CPU | Verify, multi-core / one worker | Serialized proof |
| --- | ---: | ---: | ---: | ---: |
| 128 signers | 1.33–1.56 s | 2.94–3.67 s | 3.0 / 6.2 ms | 445,566 B |
| 256 signers | **2.82 s** | 5.68 s | 5.59 / 7.68 ms | 480,342 B |
| 512 signers | **5.10 s** | 11.08 s | 4.25 / 10.54 ms | 556,830 B |

**Measured validator-set scaling.** The Beam harness generated distinct validator keys and proved and verified all subnet signatures on one i9-12900 + RX 6750 XT:

| Validators | 128-signer shards | Prove all shards, one host | Full verification, multi-core p50 | Full hierarchy |
| --- | ---: | ---: | ---: | ---: |
| 2,048 | 16 | 22.6 s | 42.57 ms | 6.81 MiB |
| 8,192 | 64 | 99.2 s | 109.34 ms | 27.24 MiB |
| 16,384 | 128 | 181.9 s | 107.63 ms | 54.47 MiB |

**Measured recursive depth.**
- **Depth-independent `QSAGIVC1` (`crates/qsag-agg/src/recursive_ivc/`):** Folds binary subtrees over `Poseidon2-GL-w24` and $\mathbb{F}_{p^5}$ into a single root proof whose byte length is strictly constant in depth (**`26,185 B`** identically across depths `1, 2, 3` / `2, 4, 8` shards; **`639,673 B`** fixed `[DKT26]` $2^{23}$-cell production format).
- **Contractive split recursion (`SplitSubtreeAggregate`):** Verifies child sumchecks in-circuit (`1,048,576` to `524,288` rows) and folds deferred PCS claims into one WHIR opening per level (`2.34 / 4.15 MB`, verifying in `42.02 / 77.55 ms` at depths 2 and 3).
- **Projected million-validator scaling:** The [hologram merge model (fan-in up to 16)](docs/QUORUM_AND_CONSENSUS_SCALING.md) projects 1,048,576 validators at **~321 KiB** and **4.28 s critical-path proving** with one GPU per tree node.

Other measured operations ([paper §7](paper/qsag.typ)):

| Operation | Result |
| --- | --- |
| Prepared Jorts threshold signature, 2-of-3 | 1.0 ms in memory; 81 ms over a simulated WAN |
| QS-A 2-of-3 / QS-B 3-of-7, encrypted channels and synced journal | 4.37 / 5.21 ms |
| Isolated CNF, one 256-hash Keccak wave, 2-of-3 / 3-of-5 | 39.5 / 96.2 ms; 1.8 / 5.9 MiB traffic |
| Pooled blinded MAC check (`OtMesh`, active Beaver sacrifice), 3 parties | 31 µs online; 4.04 ms amortized offline refill |
| Compact1122, verify 1,200 votes | 1.23 s on one core; 158–187 ms on eight threads |
| Public `HemQuintic128` (`QSAGHQM2`, `< 2^-128` QROM at $Q \le 2^{64}$) | 362,391 B (`TurboShake400`) / 381,045 B (`Poseidon2-GL-w24`) |
| zk-Hem credential, 32 attributes, tag 7 | 0.28 s prove; 19.6 ms one-core verify; 239,507 B |
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

### Hem: prove signature verification, then merge proofs

Hem encodes `JortsPoseidon2` and `CorduroyPoseidon2` verification over the Goldilocks field, checks the trace with sumcheck, and commits multilinear witnesses using Johnson-radius affine-combiner WHIR:
- **128-bit QROM quintic profiles (`HemQuintic128` `QSAGHQM2` & `zk-Hem v2` `QSAGZKH2`):** Over $\mathbb{F}_{p^5}$ with 400-bit `TurboSHAKE256` or 448-bit `Poseidon2-GL-w24` commitments and `[DKT26]` query schedules, sustaining `< 2^{-128}` QROM soundness error across all 13 schedules ($2^{16}..2^{28}$ cells) through $Q \le 2^{64}$ quantum queries.
- **Legacy `Ext4` regimes (`WhirSecurityRegime` tags `4–10`):** 256-bit commitments (`127` bits classical / `81` bits composed QROM due to 256-bit digest collision terms; see [ASSURANCE.md](ASSURANCE.md)).
- **Subtree recursion:** `QSAGIVC1` (`prove_ivc_tree` / `verify_ivc_tree`), `SuccinctSubtreeAggregate`, and `SplitSubtreeAggregate` compress arbitrary-depth validator trees against a 32-byte roster root, with straight-line multi-depth QROM knowledge extraction mechanized in Lean.

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
| `qsag-migrate` | Local and hardware-anchored collaborative MPC proofs (`zk-Hem v2` Toom-3 $\mathbb{F}_{p^5}$) across 19 CLI kinds: Bitcoin/Ethereum `secp256k1`, Solana `Ed25519`, Zcash NU7 (`Sapling`, `Orchard`, `Ironwood` ZIP-2005, `Transparent` ZIP-2007), and `BLS12-381` withdrawal keys |
| `qsag-policy` | Stateful velocity, allowlist, and window rules checked before custodians release shares |
| `SpongeMacaroon`, `PqBiscuit`, `QSAGCAU1` | Keyed-sponge macaroons, offline one-time-signature biscuits, and unlinkable zero-knowledge capability presentations |
| `qsag-cred` | Threshold ML-DSA, threshold Poseidon2 OPRFs, one-time verifier-ledger `BlindVC` credentials, and private multisignatures |

## Verification and hardware

- **Constructive Lean 4.35 Cathedral (`lean/Qsag/`, `aeneas/`):** `331` `Qsag` modules (`496,915` lines, `136,585` audited declarations, `73,117` theorems, `0` rejected, axioms strictly `⊆ {propext, Quot.sound}`, `0` `Classical.choice`, `0` `sorry`, `0` `import all`), welded to `aeneas/lean` (`6,890` decls) and `aeneas/lean-whir` (`1,911` decls, `37/37` WHIR functions), `28` `.rlib` assembly kernels (`ELF ≃ Math ≃ MIR`), and universal `poseidon2_perm12.spv` equivalence. **`312` challenge theorems and `32` definitions pass all 6 independent replay kernels** (`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda_bin`, `con-leche`, `con-ron`).
- **Three live hardware targets (`hardware/`, historical prototypes archived in [`history/`](history/README.md)):**
  - **QSAG-NI v2 (`hardware/asic/`, `hardware/fpga/`):** Stateful `zk-Hem v2` + `QSAGSTA1` verifier coprocessor (`258,104`-byte live proof verified over streaming hardware port, `194/194` faults caught, `105+` Z3/Bitwuzla miters, `Obend` Lean 4, manufacturable `IHP SG13G2` / `Sky130` characterization, Lattice `ECP5-85F` bitstreams).
  - **ASS2-0P5 / Dregg-64 (`hardware/ass2/`, `crates/qsag-ass2/`):** 64-bit `GF180MCU-D` 5 V capability enclave targeting the `SLOT_0P5X0P5` (`56`-pad) shuttle slot (`512`-RO disjoint-pair `144`-bit `BCH(63,36,5)` PUF, PQ owner `I-ROM` bootstrap, `0.60 ns` async latch wipe, KiCad 8 carrier PCB).
  - **CL_QSAG_F2 (`hardware/aws_f2/`, `qsag_accel::aws_f2`):** AWS EC2 F2 (`VU47P`, HDK 2.3.5) custom logic shell integrating 2 `QSAG-NI v2` engines and 3 isolated `ASS2` enclaves (`2.52%` `LUT6`, `3.21%` `DSP48E2`, `14.83%` `RAMB36E2`).

## Repository map

| Crates / directory | Contents |
| --- | --- |
| `qsag-core`, `qsag-quorum`, `qsag-fts` | Hash-based signatures, MPC engines, quorum switching, hardware anchors, few-time votes |
| `qsag-agg`, `qsag-accel`, `qsag-asm` | Hem / `HemQuintic128` / `zk-Hem v2` / `QSAGIVC1`, Vulkan & AWS F2 backends, SIMD & certified assembly kernels |
| `qsag-hd`, `qsag-addr`, `qsag-policy`, `qsag-cred`, `qsag-migrate`, `qsag-ass2` | Wallet, capability, credential, 19-kind migration, and `ASS2-0P5` enclave host SDK |
| `qsag-cli` | CLI (`qsag`, synced bijectively to `dregg-sig`) and runnable examples |
| `lean/`, `aeneas/`, `validation/` | 331-module Lean 4.35 proofs, MIR extractions, 6-kernel comparator, 86 differential suites |
| `hardware/`, `history/` | `asic/` (`QSAG-NI v2`), `fpga/` (`ECP5-85F`), `ass2/` (`ASS2-0P5` + PCB), `aws_f2/` (`VU47P`); retired `Dregg-180` & academic PDK runs in `history/` |

[Paper](paper/qsag.typ) · [Assurance boundaries](ASSURANCE.md) · [Measured performance](docs/PERFORMANCE.md) · [Scaling model](docs/QUORUM_AND_CONSENSUS_SCALING.md) · [Security and constant-time proofs](docs/SECURITY_AND_CT_PROOFS.md)

## License

Authored by ember arlynx (`<ember@lunar.town>`). Licensed under either [Apache-2.0](LICENSE-APACHE) or [MIT](LICENSE-MIT), at your option.
