<p align="center">
  <img src="assets/qsag-mascot.png" alt="QSAG Mascot" width="220" />
</p>

<h1 align="center">qsag — Quorum-Switching AGgregation / Quantum Succinct AGgregation</h1>

`qsag` is a post-quantum signing, threshold custody, key-derivation, and non-interactive signature-aggregation library written in Rust, paired with constructive cryptanalytic and refinement proofs in Lean 4.

It is **not** a consensus state machine; it provides the cryptographic layer that wallets, threshold custodians, and consensus validators use where elliptic-curve stacks deploy **`FROST` / MPC-ECDSA**, **`BLS` signature aggregation**, **`BIP-32` HD derivation**, and **legacy key migration** today:

1. **Threshold Signing & Custodian Quorum Switching (`qsag-core`, `qsag-quorum`, `qsag-cred`):** Multi-party evaluation of standard **NIST FIPS 205 (`SLH-DSA-SHAKE`)** and **FIPS 204 (`ML-DSA-44/65/87`)** producing stock-verifier-compatible signatures, alongside faster hash-based constructions (**`Baggy`** stateless hypertrees and **`Jorts`** stateful hypertrees) engineered for low-latency MPC and safe rotation across $(t, n)$ custodian subsets.
2. **Non-Interactive Signature Aggregation (`qsag-agg`, `qsag-fts`):** **`Hem`**, a rate-escalating **WHIR** IOP over the quartic Goldilocks extension $\mathbb{F}_p[v]/(v^4 - 7)$ ($|\mathbb{F}_{p^4}| \approx 2^{256}$) with Steiner-deduplicated Merkle-Canopy multiproofs that compresses $K$ post-quantum hash signatures into a single succinct proof, paired with single-datagram (`1,122 B`) few-time validator vote signatures (**`FrontierSumFts`**).
3. **Custody Policy, Blind HD Wallets & Zero-Knowledge Key Migration (`qsag-hd`, `qsag-policy`, `qsag-migrate`, `qsag-addr`):** Dealerless module-lattice blind hierarchical key derivation, authenticated MPC spend/rate-limit policy guards, Bech32m hybrid identity envelopes, threshold Poseidon2 VOPRF / `BlindVC` credentials, and 3-custodian co-ZK ownership proofs migrating existing `secp256k1` (Bitcoin/Taproot/EVM), `Ed25519` (Solana), `Pallas` (Zcash Orchard), and `BLS12-381` (Ethereum Beacon) keys without reconstructing the classical secret key.

---

## Constructions Overview

### 1. Threshold Hash & Lattice Custody (and Why "Quorum Switching" Matters)

Evaluating stock `SLH-DSA` inside MPC is expensive because every signature executes thousands of sequential `Keccak-f[1600]` rounds across `w = 16` Winternitz chains, `FORS` trees, and $d$ hypertree layers. Moving to stateful hash trees (`XMSS` / `LMS`) removes the hypertree overhead, **but** introduces a fundamental distributed-systems hazard: if custodian subset $\{A, B, C\}$ signs at leaf $i$ and subset $\{C, D, E\}$ signs next without global coordination, the state forks and reuses a one-time `WOTS` key—allowing trivial forgery. Whenever the latch quorum $q$ satisfies $2q \le n + f$ under $f$ Byzantine custodians, split-view leaf reuse is provably unavoidable.

`qsag` addresses both regimes:

- **Standard FIPS 205 `SLH-DSA` & FIPS 204 `ML-DSA-44/65/87`:** Evaluated in MPC via 3-party CNF replicated secret sharing (`RSS`) for small honest-majority committees, or active Shamir / `BDOZ`-`SPDZ` backed by Ring-LWE base OT (`24 × 11`-bit monomial challenges, joint `Q192` Gaussian rejection) and Dual-LPN pseudorandom correlation generators (`PCG`).
- **`Baggy` (Stateless Pure-Hash Custody):** Retains full statelessness (zero leaf-counter rollback hazard) while cutting MPC depth via `w = 4`, 128-chain constant-sum `WOTS+C`, 256-lane bitsliced `Keccak-f[1600]`, carry-less $\mathbb{F}_{2^{128}}$ `[BGIN19]` distributed zero-knowledge multiplication checks, and **`Waistband`**—a cache of static top-$L$ internal child-root `WOTS` signatures that never caches message-binding leaves.
- **`Jorts` & `QuorumJorts` (Stateful Pure-Hash Custody with Two Quorum-Switching Escapes):** Pre-steps `WOTS+C` chains offline so online signing requires a single round (`1.85 KB` wire, `4,328 B` signature), with two proven escapes to the $(t, n)$ quorum-switching impossibility:
  - **`QS-A` (`CommitteePartitionedJorts`):** Partitions the hypertree into $\binom{n}{t}$ disjoint committee subtrees (`10` subtrees for `3-of-5`) with $t$-of-$t$ additive leaf sharing inside each active committee—supporting `f = 2` corruptions and `2` offline custodians with `~0.56 ms` online compute, at the cost of public leaf indices identifying which committee signed.
  - **`QS-B` (`BftShamirJorts`):** Shares a single global tree gated by a $2q > n + f$ BFT monotonic leaf latch (**`BeltLatch`**; Availability + Safety for $n \ge 3f + 1$, e.g., $n = 7, f = 2, q = 5$) and MAC-free self-verifying pre-stepped Shamir `WOTS+C` (`H^{3 - d_i}(y_i) = \text{pk}_i`).
- **`FrontierSumFts` (`Compact1122`):** Few-time pure-hash signatures (`w = 96` constant-sum chains, `1,122 B` total) sized to fit inside a single `1,232 B` QUIC/UDP packet with multi-message SIMD batch verification.

### 2. `Hem`: Non-Interactive Signature Aggregation via GoldilocksExt4 WHIR

To aggregate validator or committee signatures non-interactively without lattices or pairings, `Hem` (`qsag-agg`) arithmetizes verification of algebraic `Poseidon2` hash-tree signatures (`JortsPoseidon2` and stateless `Corduroy`) into a 256-column degree-3 AIR and proves batch validity with rate-escalating **WHIR** (`[ACFY25]`) over $\mathbb{F}_p^4 = \mathbb{F}_p[v]/(v^4 - 7)$ ($p = 2^{64} - 2^{32} + 1$) and Steiner-deduplicated **`CanopyMultiProof`** Merkle commitments:

- **Proved Johnson / `[CWYZ26]` Proximity Regime:** Capacity-proximity conjectures (`Habr24`) are disabled and rejected on the wire; `Hem` operates strictly within the Guruswami–Sudan Johnson bound (`q = (258, 130, 88, 66)` queries with 16-bit batch/fold/query PoW under `BciksJohnsonQrom128`).
- **Hardware Acceleration (`qsag-asm`, `qsag-accel`):** CPU paths dispatch to `x86_64` `AVX-512` / `AVX2` + `VPCLMULQDQ` + `GFNI` (including 8-way ZMM `cSHAKE256` Canopy/WHIR hashing) and `AArch64` `NEON` + `PMULL` + `FEAT_SHA3`. On Linux/Vulkan 1.3 (`Wave32`), a persistent VRAM `ProverArena` executes fused Radix-8 Mobius transforms, `Ext4` coset LDEs, Canopy Merkle hashing, 256-column AIR row sumchecks, and WHIR folding on the GPU with bit-exact deterministic parity against the CPU prover.

---

## Performance & Consensus-Scale Benchmarks

Measurements below come from release builds on AMD Zen 5 (`Ryzen AI 9 HX PRO 370`, `AVX-512`), `i9-12900` + `AMD Radeon RX 6750 XT` (`Mesa RADV`, Vulkan 1.3 `Wave32`), and `EPYC` hosts (see [paper/qsag.typ](paper/qsag.typ) and [docs/QUORUM_AND_CONSENSUS_SCALING.md](docs/QUORUM_AND_CONSENSUS_SCALING.md) for full methodology and hardware tables):

| Operation / Workload | Configuration | Latency / Throughput | Size / Memory |
| --- | --- | --- | --- |
| **`QS-A` 3-of-5 stateful threshold sign** | Loopback TCP (`2` custodians offline) / ext4 NVMe `fsync` | **`0.56 ms`** compute / **`4.37 ms`** durable | `1.85 KB` MPC wire, `4,328 B` sig |
| **`QS-B` 3-of-7 BFT stateful threshold sign** | Certified `BeltLatch` ($q = 5$), ext4 NVMe `fsync` | **`5.21 ms`** durable | `4,328 B` sig |
| **`BaggySha3` stateless threshold sign** | 256-lane bitsliced Keccak + `CLMUL` `[BGIN19]` DZK | **`~17–35 ms`** (`~8–15×` vs MPC `SLH-DSA`) | Stateless (`0` rollback state) |
| **Canopy / WHIR `cSHAKE256` batch (`qsag-asm`)** | Zen 5 single-core 8-way `AVX-512` (`69 B` node / `2 KB` leaf) | **`111.2 ns`/node** (`2.66 GB/s` leaf) | `4.0–5.7×` over scalar |
| **GPU `Poseidon2` Merkle tree (`2^{20}` leaves)** | `RX 6750 XT` Vulkan `Wave32` | **`38.77 ms`** (`204.6×` scalar ref) | Keyed SPIR-V 1.5 receipt |
| **Solana Alpenglow vote scale (`N = 1,500`)** | `Compact1122` votes (`1,218 B` framed $\le 1,232\text{ B}$ QUIC MTU), `1,200`-vote quorum | **`158–187 ms`** batch verify (`8` threads; `1.23 s` 1T) | `1,122 B` / vote (`1` UDP packet) |
| **Ethereum Beam subnet (`K = 32` / `K = 128`)** | `BciksJohnsonQrom128` WHIR on `1× RX 6750 XT` GPU | **`321.7 ms`** (`K=32`) / **`1.26–1.34 s`** (`K=128`) prove; **`3.3–7.0 ms`** verify | **`613 MiB`** host RSS (`15.8×` < CPU) |
| **Multi-subnet Beam slot (`2,048–16,384` keys)** | `M = 16..128` subnets × `128` `JortsPoseidon2` keys | `~1.3 s` per subnet GPU; `42–109 ms` multi-core full verify | `3.1–3.2 GiB` peak RSS *(see note)* |

*Multi-subnet scaling note:* `Hem` shard proofs are succinct within each `128`-validator subnet; across $M$ subnets, the outer hierarchical wrapper commits to a `Poseidon2` summary chain while full verification still transmits and checks the $M$ constituent shard proofs (`~436 KiB`/shard under `BciksJohnsonQrom128`), as `cSHAKE256` Merkle verification is not yet arithmetized inside an outer recursive WHIR circuit.

---

## Constructive Cryptanalysis & Formalization Approach

Threshold MPC protocols, stateful anti-rollback latches, and multi-round Fiat–Shamir IOPs fail in subtle ways when analyzed only on paper. `qsag` treats formal verification as **constructive cryptanalysis** across four connected layers:

1. **Constructive Protocol, Coding-Theory & QROM Proofs (`lean/Qsag/`, Lean 4.35):**
   - Strictly **`0 sorry` and `0 Classical.choice`** (kernel axioms restricted to `{propext, Quot.sound}`). Witness extractors, bivariate/trivariate Guruswami–Sudan and cylinder-sliced `[CWYZ26]` correlated-agreement bounds (`Cwyz26JohnsonCertificate`), binary-tower to polynomial-basis $\mathbb{F}_{2^{128}}$ isomorphisms, `BeltLatch` $2q > n + f$ quorum safety, POSIX crash-WAL models, and game-hopping reductions compute explicit `Type`-valued witnesses rather than non-constructive existence proofs.
   - Paired with executable counterexample witnesses (`#tooth_pair`) demonstrating that dropping protocol guards (such as $2q > n + f$, domain framing, external rollback anchors, or norm checks) yields concrete attacks.
2. **Compiler-Extracted Safe-Rust MIR (`aeneas/qsag-verified`, `aeneas/qsag-whir-verified`):**
   - Core arithmetic, sponges, `WOTS+C`, `BDOZ` MACs, `BeltLatch`, and custody release guards are extracted from Rust MIR to Lean via **Charon + Aeneas** (`0 FunsExternal`) and linked directly by workspace crates.
3. **Machine-Code & SIMT Noninterference (`ConstantTimeIsa`, `ElfBinaryVerify`, `SpirvSimtGpuEquiv`):**
   - Decoded `x86_64` (`AVX2` / `PCLMULQDQ` / `VPCLMULQDQ`) and `AArch64` (`NEON` / `PMULL` / `FEAT_SHA3`) assembly kernels and `SPIR-V 1.5` compute shaders are checked against secret-independent control-flow, memory-address, `DOIT`/`FEAT_DIT` operand-timing, and scratch-zeroization contracts.
4. **"Verify Your Code, Test Your Specs" (`validation/`, `spec-oracle`, `isa-cosim`):**
   - Executable Lean reference specifications (`lake exe spec-oracle`) and property-based differential test suites cross-check `qsag` byte-for-byte against 17 independent upstream Rust implementations (`fips205`, `ml-dsa`, `sha3`, `k256`, `curve25519-dalek`, `pasta_curves`, `blstrs`), mutation-injected transcripts, and hardware `x86_64` instruction co-simulation.

---

## Workspace Map

The core Rust workspace contains 12 crates (`no_std` + `alloc` for core libraries; `std` for host storage, networking, Vulkan FFI, and CLI) with zero external `crates.io` runtime dependencies, plus 2 Aeneas-extracted crates and an out-of-workspace differential validation suite:

| Crate | Path | Purpose |
| --- | --- | --- |
| `qsag-core` | `crates/qsag-core` | Threshold `SLH-DSA`, `Baggy`, `Jorts`, `Corduroy`, `RSS`/`SPDZ`, RLWE OT, Dual-LPN `PCG`, DKG/reshare |
| `qsag-quorum` | `crates/qsag-quorum` | Generalized $(t, n)$ `QS-A` / `QS-B` quorum switching, `Hem` threshold custody, AEAD wire channels |
| `qsag-agg` | `crates/qsag-agg` | `Hem` `GoldilocksExt4` WHIR aggregation, `CanopyMultiProof`, hierarchical shard merging |
| `qsag-fts` | `crates/qsag-fts` | `FrontierSumFts` (`Compact1122`) and `ParallelSeededFts` few-time signatures + SIMD batch verify |
| `qsag-asm` | `crates/qsag-asm` | Audited `x86_64` (`AVX2`/`AVX-512`/`VPCLMULQDQ`/`GFNI`) and `AArch64` (`NEON`/`PMULL`/`SHA3`) kernels |
| `qsag-accel` | `crates/qsag-accel` | Portable CPU reference and Linux Vulkan 1.3 `Wave32` GPU `ProverArena` with keyed receipts |
| `qsag-hd` | `crates/qsag-hd` | Dealerless module-lattice blind HD key derivation and watch-only projections |
| `qsag-policy` | `crates/qsag-policy` | Authenticated rolling-window `BDOZ` spend/rate-limit custody guards and durable checkpoints |
| `qsag-addr` | `crates/qsag-addr` | Bech32m `QsagAddress` and canonical `HybridPinnedEnvelope` codecs |
| `qsag-cred` | `crates/qsag-cred` | Threshold `ML-DSA-44/65/87`, `2-of-5` `Poseidon2` VOPRF, and `Quantum128` `BlindVC` |
| `qsag-migrate` | `crates/qsag-migrate` | 3-custodian co-ZK legacy key ownership migration (`secp256k1`, `Ed25519`, `Pallas`, `BLS12-381`) |
| `qsag-cli` | `crates/qsag-cli` | Command-line tool (`keygen`, `sign`, `verify`, `addr`, `aggregate`, `verify-agg`, `kat`) and examples |
| `qsag-verified` | `aeneas/qsag-verified` | Charon/Aeneas-extracted arithmetic, sponge, and custody-guard crate |
| `qsag-whir-verified` | `aeneas/qsag-whir-verified` | Charon/Aeneas-extracted WHIR folding and query-check core |

---

## Quickstart

```bash
umask 077
QSAG_DEMO_DIR=$(mktemp -d /tmp/qsag-demo.XXXXXX)
printf 'qsag quickstart\n' > "$QSAG_DEMO_DIR/msg.bin"

# Built-in KAT suite and single-signer / address workflow
cargo run --release -p qsag-cli -- info
cargo run --release -p qsag-cli -- kat
cargo run --release -p qsag-cli -- keygen --scheme slh-dsa-shake-128f \
  --secret-out "$QSAG_DEMO_DIR/secret.json" --public-out "$QSAG_DEMO_DIR/public.json"
cargo run --release -p qsag-cli -- sign \
  --secret "$QSAG_DEMO_DIR/secret.json" --in "$QSAG_DEMO_DIR/msg.bin" --out "$QSAG_DEMO_DIR/sig.json"
cargo run --release -p qsag-cli -- verify \
  --public "$QSAG_DEMO_DIR/public.json" --in "$QSAG_DEMO_DIR/msg.bin" --sig "$QSAG_DEMO_DIR/sig.json"
cargo run --release -p qsag-cli -- addr encode --public "$QSAG_DEMO_DIR/public.json"

# Protocol & consensus-scale examples
cargo run --release -p qsag-cli --example slh_dsa_quickstart
cargo run --release -p qsag-cli --example succinct_k_to_1_aggregation
cargo run --release -p qsag-cli --example few_time_signatures
cargo run --release -p qsag-cli --example pq_address_and_policy
cargo run --release -p qsag-cli --example dealerless_dkg_consistency_check
cargo run --release -p qsag-agg --example mock_solana_alpenglow
cargo run --release -p qsag-agg --example mock_ethereum_beam
```

---

## Further Reading

- **Technical Paper:** [paper/qsag.typ](paper/qsag.typ) — full protocol specifications, security reductions, `[CWYZ26]` / QROM analysis, and hardware benchmarks.
- **Threat Models & TCB Boundaries:** [ASSURANCE.md](ASSURANCE.md) and [docs/SECURITY_AND_CT_PROOFS.md](docs/SECURITY_AND_CT_PROOFS.md).
- **Engineering & Verification Ledger:** [PROJECT.md](PROJECT.md) and [docs/CONVERGENCE_STATUS.md](docs/CONVERGENCE_STATUS.md) — detailed theorem-to-code status, scoped integration checks, and open refinement items.
- **Consensus Scaling Analysis:** [docs/QUORUM_AND_CONSENSUS_SCALING.md](docs/QUORUM_AND_CONSENSUS_SCALING.md).

## License

Dual-licensed under Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE)) or MIT ([LICENSE-MIT](LICENSE-MIT)) at your option.
