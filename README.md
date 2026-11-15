<p align="center">
  <img src="assets/qsag-mascot.png" alt="QSAG Mascot" width="200" />
</p>

<h1 align="center">qsag</h1>

Post-quantum threshold signing, key derivation, and non-interactive signature aggregation in Rust and Lean 4.

`qsag` sits beneath wallets, custodians, and validators where elliptic-curve systems use **`FROST`**, **`BLS` aggregation**, and **`BIP-32`**. It is not a consensus engine. Core libraries are `no_std + alloc` with zero external `crates.io` runtime dependencies.

## Core Constructions

### 1. Threshold Hash Signing & Quorum Switching

Evaluating stock `SLH-DSA` in MPC hashes thousands of sequential `w = 16` chains per signature. Stateful trees (`XMSS`) remove the hypertree, provided two signing subsets never reuse a leaf: under $f$ Byzantine custodians, any latch quorum $2q \le n + f$ admits a split-view fork and key recovery.

- **FIPS 205 `SLH-DSA` & FIPS 204 `ML-DSA-44/65/87`:** Stock-verifier-compatible threshold signing via 3-party `RSS` or active `BDOZ`/`SPDZ` (Ring-LWE OT + Dual-LPN PCG).
- **`Baggy` (stateless):** Pure-`Keccak` hypertrees (`w = 4` bitsliced `WOTS+C`, $\mathbb{F}_{2^{128}}$ `[BGIN19]` multiplication checks, top-$L$ internal-node signature cache). Zero rollback state.
- **`Jorts` (stateful, 1 online round):** Pre-steps `WOTS+C` chains offline; avoids $(t, n)$ leaf reuse via $\binom{n}{t}$ committee subtrees (**`QS-A`**) or a $2q > n + f$ BFT monotonic latch (**`QS-B`**, `BeltLatch`).
- **`Compact1122` (few-time):** `1,122 B` pure-`Keccak` signatures (`w = 96`) fitting a single `1,232 B` QUIC/UDP packet for sub-second validator votes.
- **Wallets & Migration:** Module-lattice blind HD derivation (`qsag-hd`), `BDOZ` spend-limit guards (`qsag-policy`), threshold `Poseidon2` VOPRF / `BlindVC` (`qsag-cred`), and 3-party co-ZK ownership proofs for `secp256k1`, `Ed25519`, `Pallas`, and `BLS12-381` (`qsag-migrate`).

### 2. `Hem`: Non-Interactive WHIR Aggregation

`Hem` (`qsag-agg`) arithmetizes $K$ `Poseidon2` hash-tree signatures (`JortsPoseidon2` or stateless `Corduroy`) in a 256-column degree-3 AIR and proves the batch with **WHIR** (`[ACFY25]`) over $\mathbb{F}_p[v]/(v^4 - 7)$ ($p = 2^{64} - 2^{32} + 1$) and Steiner-deduplicated Merkle multiproofs. Soundness stays inside the proved Johnson / `[CWYZ26]` bound; capacity conjectures are disabled. Proving runs on `AVX-512` / `NEON` CPUs and Vulkan 1.3 `Wave32` GPUs with bit-identical transcripts.

## Benchmarks

Release measurements on Zen 5 (`AVX-512`), `RX 6750 XT` (`Vulkan 1.3`), and `EPYC` ([methodology](paper/qsag.typ)):

| Workload | Setup | Latency / Throughput | Size |
| --- | --- | --- | --- |
| **`QS-A` 3-of-5 sign** | Loopback TCP / NVMe `fsync` | **`0.56 ms`** compute / **`4.37 ms`** durable | `1.85 KB` wire, `4,328 B` sig |
| **`QS-B` 3-of-7 BFT sign** | `BeltLatch` ($q = 5$), NVMe `fsync` | **`5.21 ms`** durable | `4,328 B` sig |
| **`BaggySha3` sign** | 256-lane bitsliced `Keccak` | **`17–35 ms`** | Stateless |
| **`cSHAKE256` Merkle batch** | Zen 5 1-core, 8-way `AVX-512` | **`111.2 ns`/node** (`2.66 GB/s` leaf) | `4.0–5.7×` scalar |
| **Alpenglow vote verify** | `1,200` `Compact1122` votes (`8` threads) | **`158–187 ms`** (`1.23 s` 1T) | `1,122 B` / vote |
| **Beam subnet aggregate** | `K = 32` / `K = 128` on `1× RX 6750 XT` | **`322 ms`** / **`1.26 s`** prove; **`3.3–7.0 ms`** verify | `613 MiB` host RSS |

## Constructive Cryptanalysis

Formal verification is used in the design loop across four layers:

1. **Lean 4.35 Proofs (`lean/Qsag/`):** `0 sorry`, `0 Classical.choice` (axioms `{propext, Quot.sound}`). Constructive extractors for `[CWYZ26]` correlated agreement, QROM reductions, `BeltLatch` safety, and crash-WAL recovery, paired with `#tooth_pair` counterexamples when guards are removed.
2. **Rust MIR Extraction (`aeneas/`):** Core arithmetic, sponges, `WOTS+C`, `BDOZ` MACs, and custody guards extracted via Charon + Aeneas (`0 FunsExternal`).
3. **ISA & GPU Noninterference:** Decoded `x86_64`, `AArch64`, and `SPIR-V 1.5` binaries checked for constant-time control flow, coalesced addressing, `Wave32` divergence freedom, and LDS bank-conflict freedom.
4. **Differential Oracles (`validation/`):** `lake exe spec-oracle` and property tests cross-checked byte-for-byte against 17 upstream Rust crates and `x86_64` co-simulation.

## Crates

| Crate | Role |
| --- | --- |
| `qsag-core` | Threshold `SLH-DSA`, `Baggy`, `Jorts`, `Corduroy`, `RSS`/`SPDZ`, RLWE OT, Dual-LPN PCG |
| `qsag-quorum` | $(t, n)$ `QS-A` / `QS-B` quorum switching, `BeltLatch`, AEAD channels |
| `qsag-agg` | `Hem` `GoldilocksExt4` WHIR prover/verifier and Merkle-Canopy multiproofs |
| `qsag-fts` | `Compact1122` and `ParallelSeededFts` few-time signatures + SIMD batch verify |
| `qsag-asm` | `x86_64` (`AVX2`/`AVX-512`/`VPCLMULQDQ`/`GFNI`) and `AArch64` (`NEON`/`PMULL`/`SHA3`) kernels |
| `qsag-accel` | Portable CPU reference and Linux Vulkan 1.3 `Wave32` GPU `ProverArena` |
| `qsag-hd` | Dealerless module-lattice blind HD key derivation |
| `qsag-policy` | Authenticated `BDOZ` spend/rate-limit guards |
| `qsag-addr` | Bech32m addresses and hybrid key envelopes |
| `qsag-cred` | Threshold `ML-DSA-44/65/87`, `Poseidon2` VOPRF, and `BlindVC` |
| `qsag-migrate` | 3-party co-ZK key migration (`secp256k1`, `Ed25519`, `Pallas`, `BLS12-381`) |
| `qsag-cli` | CLI (`keygen`, `sign`, `verify`, `addr`, `aggregate`, `verify-agg`, `kat`) and examples |

## Quickstart

```bash
umask 077 && D=$(mktemp -d /tmp/qsag.XXXXXX) && printf 'hello\n' > "$D/msg"

cargo run --release -p qsag-cli -- kat
cargo run --release -p qsag-cli -- keygen --scheme slh-dsa-shake-128f \
  --secret-out "$D/sk.json" --public-out "$D/pk.json"
cargo run --release -p qsag-cli -- sign   --secret "$D/sk.json" --in "$D/msg" --out "$D/sig.json"
cargo run --release -p qsag-cli -- verify --public "$D/pk.json" --in "$D/msg" --sig "$D/sig.json"

cargo run --release -p qsag-agg --example mock_solana_alpenglow
cargo run --release -p qsag-agg --example mock_ethereum_beam
```

## Documentation & License

- **Paper:** [paper/qsag.typ](paper/qsag.typ) · **Assurance & TCB:** [ASSURANCE.md](ASSURANCE.md) · **Scaling:** [docs/QUORUM_AND_CONSENSUS_SCALING.md](docs/QUORUM_AND_CONSENSUS_SCALING.md) · **Status:** [PROJECT.md](PROJECT.md)
- Dual-licensed under [Apache-2.0](LICENSE-APACHE) or [MIT](LICENSE-MIT).
