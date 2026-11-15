<p align="center">
  <img src="assets/qsag-mascot.png" alt="QSAG Mascot" width="240" />
</p>

The recorded 2026-11-14 compiled-kernel freshness gate passed: fresh Rust 1.99.1 release archives matched all **19 x86-64 and 9 AArch64 certified assembly kernels**, with zero changed, missing or unpinned kernels. The corresponding Lean certificate checks pass. This covers the named kernel bytes and their explicit ISA contracts; complete linked-program certification remains separate.

**Recorded snapshot, not the working tree.** A recorded 2026-11-14 run of the integrated main-library axiom audit checked 59,257 declarations (28,744 kernel theorem declarations) across 57 modules with 0 rejected axioms, including private and compiler-generated declarations and 277 pure assurance-infrastructure declarations (131 compile-time tactic declarations excluded). The extracted-MIR/custody audit checked 5,318 declarations / 2,093 theorems / 44 modules and the WHIR audit 1,558 / 718 / 7, both with 0 rejected; sandboxed six-kernel replay passed 107 main theorems and 65 MIR theorems plus 17 definitions. Those runs describe the source bytes pinned in [CONVERGENCE_SOURCE.json](docs/CONVERGENCE_SOURCE.json). The library has since gained modules and most pinned files have changed, so these figures are history: they count checked definitions and premises of that snapshot and are neither a check of the present tree nor a statement of production refinement. `python3 scripts/check_evidence_freshness.py` reports which recorded gates and later scoped checks still match the current bytes; the latest results are under [current integration checks](docs/CONVERGENCE_STATUS.md#current-integration-checks).

<h1 align="center">qsag — Quorum-Switching AGgregation / Quantum Succinct AGgregation</h1>

`qsag` is a post-quantum threshold signing, aggregation, and custody stack: NIST **FIPS 205 SLH-DSA-SHAKE** and **FIPS 204 ML-DSA-44/65/87** alongside the custom **Pants** pure-hash and algebraic suite. It combines Rust implementations with Lean protocol proofs, compiler-extracted MIR proofs, scoped machine-code verification, and executable specification tests.

The **14-package Rust project** has **0 external crates.io dependencies**: 12 root workspace packages and two separately rooted extraction crates, `aeneas/qsag-verified` and `aeneas/qsag-whir-verified`. Libraries support `no_std` with `alloc`; host adapters and the CLI require `std`. Production core, policy and quorum use `qsag-verified`; aggregation uses `qsag-whir-verified`. Platform unsafe code lives in `qsag-asm` and the Linux/std raw Vulkan FFI in `qsag-accel`. Rust 1.99.1 (pinned toolchain) / Edition 2024; Lean 4.35.

**Research preview:** implementations and proof coverage are evolving. A proved model, a passing benchmark, and an integrated deployment guarantee are different results. See [the exact theorem map](docs/SECURITY_AND_CT_PROOFS.md#current-parameter-and-theorem-map) and [PROJECT.md](PROJECT.md) for status and [ASSURANCE.md](ASSURANCE.md) for assumptions and remaining integration work.

## The Pants suite

- **Baggy** (`BaggySha3` / `BaggyPoseidon2`): a stateless signing construction with a hypertree design, TSW, and **Waistband**, a static Top-$L$ internal child-root WOTS cache. It never caches message-binding leaves. The pure-hash path uses 256-lane bitsliced Keccak and `PCLMULQDQ` / `VPCLMULQDQ` / `PMULL` $GF(2^{128})$ BGIN19 DZK, with 256-bit digest `WOTS+C` (`w=4, chains=128, target_sum=192`). “Unlimited lifetime” means no stateful leaf-exhaustion counter; concrete security still depends on a finite query/signature budget and the chosen parameters. MPC preprocessing and custody resources retain their own persistence requirements.
- **Jorts** and **QuorumJorts**: explicitly stateful threshold signing guarded by crash-WAL and **BeltLatch**. Certified global allocation requires $2q > n+f$ and, for the BFT availability regime, $q \le n-f$ (feasible with safety when $n \ge 3f+1$). Reported Mode 3B 2-of-3 measurements are approximately **1.0 ms local compute / 81 ms simulated WAN**, not durable deployment latency. `qsag-quorum` exposes two distinct generalized $(t,n)$ modes:
  - **QS-A — `CommitteePartitionedJorts`**: $\binom{n}{t}$ disjoint committee subtrees. A 3-of-5 committee can sign with two parties offline; the reported loopback TCP measurement is approximately **0.56 ms**. Safety with abort permits $f=2$ corruptions, but malicious online signers can withhold their shares. This is **committee-revealing partitioned custody**: public leaf ranges identify the committee. It trades committee anonymity for $t$-of-$t$ online signing when $2f>t$.
  - **QS-B — `BftShamirJorts`**: one global tree, certified BeltLatch, and MAC-free self-verifying pre-stepped Shamir `WOTS+C`. Leaf allocation is quorum-independent; signing threshold $t$ and latch quorum $q$ are separate requirements. For example, $n=7,f=2,q=5$ satisfies the latch condition. “MAC-free” describes the WOTS share verification, not the latch/channel layer.
- **Corduroy**: the algebraic `Poseidon2` stateless threshold custody hypertree.
- **Hem** (`qsag-agg`): non-interactive $K$-to-$1$ succinct signature aggregation and binary-tree proof merging over **GoldilocksExt4**, $\mathbb{F}_p[v]/(v^4-7)$, where $p=2^{64}-2^{32}+1$ and $p^4>2^{255.99}$. It uses EUROCRYPT 2025 rate-escalating **WHIR** and Steiner-deduplicated **CanopyMultiProof** Merkle-Canopy commitments. The default `BciksJohnsonQrom128` query schedule is $q=(258,130,88,66)$; `BciksJohnsonClassical128` remains available in lower-level APIs. Capacity-proximity regimes, including Habr24, are retired and their wire tags are rejected. Johnson query accounting does not close the remaining CWYZ decomposition and concrete WHIR soundness proof. The aggregate verifier enforces a mandatory **128-bit QROM Grover search floor for query accounting**. This is not a total Fiat–Shamir/QROM security proof: field errors, commitment binding, list sizes, adaptive reduction losses, and composition still matter. Merge trees verify constituent proofs and signer disjointness. The compact hierarchy proves a public commitment chain; its authorization API additionally requires locally verified child evidence. It does not prove the child-verifier relation inside the outer proof.

The surrounding stack covers `FrontierSumFts` / `ParallelSeededFts`, secret-keyed dealerless PQ HD wallets, `Bech32m` addresses and `HybridPinnedEnvelope`, authenticated rolling-window BDOZ custody guards, threshold `ML-DSA-44/65/87`, 2-of-5 `Poseidon2` TOPRF, six-limb `Quantum128` BlindVC, three-party co-ZK migration from `secp256k1` / `Taproot` / `Ed25519` plus standalone 438-repetition ZKBoo migration for `Pallas` (`Orchard` / `RedPallas`) and `BLS12-381` (`G1`), and accelerator backends.

Threshold Hem-compatible Jorts signing, refresh and reshare now have implementations in `qsag-quorum::hem_quorum`. The seed-SPDZ lifecycle takes private RNGs from each party; an in-process coordinator still does not establish separated custody. See the [construction obligations](PROJECT.md#construction-proof-obligations) for the remaining implementation-to-ideal-functionality work.

The exact parameter and theorem map is in [the security proof guide](docs/SECURITY_AND_CT_PROOFS.md#current-parameter-and-theorem-map). RLWE uses **24 × 11-bit signed monomials** (264 joint bits; nominal generic-search exponents 264 classical / 132 quantum), with a joint Gaussian rejection parameter approximately 40. These figures are not an instantiated quantum-active OT theorem. Migration uses **438 repetitions**. Johnson queries are **(258,130,88,66)** with +2 slack, 16-bit `QSAG.PCS.POW2/v1` work and `maxQueryCap = 512`.

The RX 6750 XT backend executes six Vulkan kernels. A 2026-11-14 raw RADV run measured **38.77 ms** for a 2^20-leaf Poseidon2 Merkle tree (**204.6×** its CPU reference) and **27.38 ms** for 262,144 Poseidon2-12 permutations (**78.1×**). These are the integrated run’s paired timings; see [the measurement ledger](PROJECT.md#c-06-publication-evidence-and-follow-up). Kernel speedups do not measure full Hem proving.

## Signature bytes and deployment boundaries

For FIPS 205 SLH-DSA-SHAKE, Baggy, Jorts 2-of-3, and QS-B, the threshold/reference equality claim concerns **successfully evaluated signature bytes for the same key, leaf/message, parameters, and matched hedging seed/randomizer**: these equal the canonical single-signer output (statistical distance **0** under that matched-input coupling). This does not assert equality of independently chosen entropy, leaf-selection, retry, or adversarially abort-conditioned output distributions. Production refinement coverage is tracked in [ASSURANCE.md](ASSURANCE.md). QS-A only has a same-committee-leaf-schedule reference; it cannot promise committee anonymity.

FIPS 205 and FIPS 204 outputs are standard-verifier compatible. ML-DSA compatibility does not by itself establish perfect output-distribution equality, and its shared rejection protocol has additional assumptions. Custom Pants formats are not NIST signature formats.

RAM and loopback benchmarks exercise protocol computation; simulated WAN adds a network model. Deployment additionally needs durable reservations before useful share release, authenticated **confidential** channels, consistent broadcast where required, recovery, and a trusted policy time/epoch authority. MAC framing alone supplies no confidentiality. A local cluster holding all shares is a demonstration, not separated custody.

## Which Crate Should I Use?

| Goal | Crate | Current entrypoints |
| --- | --- | --- |
| FIPS 205, Baggy, Jorts, Corduroy, DKG/reshare | `qsag-core` | `fips205::{slh_sign_mpc, slh_verify}`, `keccak_mpc::RssSlhMpcCluster`, `baggy::{BaggySha3, BaggyPoseidon2}`, `jorts::JortsSigner`, `corduroy::Corduroy` |
| Generalized quorum switching | `qsag-quorum` | `quorum_jorts::{CommitteePartitionedJorts, BftShamirJorts}`, `party_node`, `wire_channel` |
| Hem aggregation and merging | `qsag-agg` | `aggregate_signatures`, `merge_aggregates`, `verify_aggregate`, `WhirSecurityRegime`, `CanopyMultiProof` |
| SIMD, carryless arithmetic, timing tests | `qsag-asm` | `keccak_f1600_x4`, `keccak_chi_mpc_row256`, `bitslice`, `cpuid` |
| Few-time signatures | `qsag-fts` | `FrontierFtsSigningKey`, `verify_frontier_fts`, `ParallelSeededSignSession` |
| Dealerless HD wallets | `qsag-hd` | `CustodianSeeds`, `InventoryPartyShareVault`, `LinearModuleXPub`, `AuthorizedHdProjection` |
| Addresses and hybrid binding | `qsag-addr` | `QsagAddress`, `HybridPinnedEnvelope` |
| Custody authorization | `qsag-policy` | `TransactionPolicy`, `PolicySignerGuardShare`, `AuthorizedSignReleaseToken` |
| Legacy ownership migration | `qsag-migrate` | `LegacyOwnershipWitness`, `CoZkCustodianShare`, `co_zk_mpc`, `verify_migration_proof` |
| Credentials and threshold ML-DSA | `qsag-cred` | `threshold_mldsa`, `voprf`, `blind_vc` |
| Batch execution and keyed receipts | `qsag-accel` | `AcceleratorBackend`, `VulkanSpirvBackend`, `CpuReferenceBackend`, `BackendAttestationKey`, `VerifiedKernelDigestRegistry::verify_keyed_receipt` |
| Command-line workflows | `qsag-cli` | `info`, `kat`, `keygen`, `sign`, `verify`, `addr`, `aggregate`, `verify-agg`, `policy-demo` |
| Extracted safe-Rust specifications | `qsag-verified` | `aeneas/qsag-verified` → `QsagVerified.Funs` → `QsagMirProofs` |

## Workspace Crate Map

| Crate | Path | Role / runtime |
| --- | --- | --- |
| `qsag-core` | `crates/qsag-core` | Threshold signatures, preprocessing, custody; `no_std`, optional `std` |
| `qsag-quorum` | `crates/qsag-quorum` | QS-A / QS-B, party nodes and transport; `no_std`, optional `std` |
| `qsag-agg` | `crates/qsag-agg` | Hem Ext4 WHIR, Canopy and merge trees; `no_std`, optional `std` |
| `qsag-asm` | `crates/qsag-asm` | Audited platform SIMD/assembly boundary; `no_std`, optional `std` |
| `qsag-fts` | `crates/qsag-fts` | FrontierSumFts and ParallelSeededFts; `no_std` |
| `qsag-hd` | `crates/qsag-hd` | Secret-keyed dealerless HD custody; `no_std` |
| `qsag-addr` | `crates/qsag-addr` | Bech32m and pinned hybrid identities; `no_std` |
| `qsag-policy` | `crates/qsag-policy` | Authenticated BDOZ policy release; `no_std` |
| `qsag-migrate` | `crates/qsag-migrate` | Active three-party co-ZK ownership migration; `no_std` |
| `qsag-cred` | `crates/qsag-cred` | ML-DSA-44/65/87, TOPRF, six-limb BlindVC; `no_std` |
| `qsag-accel` | `crates/qsag-accel` | CPU reference, Linux/std Vulkan and keyed receipts; portable `no_std` core |
| `qsag-cli` | `crates/qsag-cli` | CLI and examples; `std` binary |
| `qsag-verified` | `aeneas/qsag-verified` | Separate extraction workspace; `no_std` |
| `qsag-whir-verified` | `aeneas/qsag-whir-verified` | Separate extraction workspace, called by Hem |

Optional `std` features provide WAL storage and Linux Vulkan execution. Fresh extraction and complete release-path mediation are tracked separately from the existing Cargo linkage.

## Quickstart: CLI & Runnable Examples

Run from the repository root on Linux with the pinned Rust 1.99.1 toolchain (`rust-version = "1.99.1"`) and `/dev/urandom`. The temporary directory is new on each run because key/signature outputs refuse accidental overwrites. These are demonstration keys.

```bash
umask 077
QSAG_DEMO_DIR=$(mktemp -d /tmp/qsag-demo.XXXXXX)
printf 'qsag quickstart\n' > /tmp/qsag-msg.bin
cargo run --release -p qsag-cli -- info
cargo run --release -p qsag-cli -- kat
cargo run --release -p qsag-cli -- keygen --scheme slh-dsa-shake-128f --secret-out "$QSAG_DEMO_DIR/secret.json" --public-out "$QSAG_DEMO_DIR/public.json"
cargo run --release -p qsag-cli -- sign --secret "$QSAG_DEMO_DIR/secret.json" --in /tmp/qsag-msg.bin --out "$QSAG_DEMO_DIR/signature.json"
cargo run --release -p qsag-cli -- verify --public "$QSAG_DEMO_DIR/public.json" --in /tmp/qsag-msg.bin --sig "$QSAG_DEMO_DIR/signature.json"
cargo run --release -p qsag-cli -- addr encode --public "$QSAG_DEMO_DIR/public.json"
```

The CLI stores versioned JSON key/signature envelopes and reads message bytes from `--in`. Every subcommand accepts `--help`. This CLI sequence passed the isolated Linux check, including all 43 built-in KATs.

### Installed end-to-end examples

Examples use fixed demonstration seeds or in-process custodians. The full threshold example includes RSS signing, SPDZ preprocessing, and dynamic reshare with public-root checks. In the bounded Linux documentation check, it completed RSS signing and stock verification, then timed out after 600 seconds during SPDZ preprocessing (exit 124). It is included below for completeness, but is not a passing bounded quickstart. The integrated run also exceeded the stricter 25-second target (exit 124). Profiling identifies per-bit authenticated triple preprocessing as the dominant cost; meeting that target requires a protocol-level preprocessing redesign.

```bash
cargo run --release -p qsag-cli --example slh_dsa_quickstart
cargo run --release -p qsag-cli --example threshold_slh_dsa_quickstart
cargo run --release -p qsag-cli --example succinct_k_to_1_aggregation
cargo run --release -p qsag-cli --example pq_address_and_policy
cargo run --release -p qsag-cli --example few_time_signatures
cargo run --release -p qsag-cli --example dealerless_dkg_consistency_check
cargo run --release -p qsag-cli --example custom_accel_backend
```

All six examples other than `threshold_slh_dsa_quickstart` exited 0 in the bounded Linux check. See [PROJECT.md](PROJECT.md#documentation-quickstart-validation) for the full result.

## Assurance: verify your code, test your specs

| Pillar | Machine-checked surface | Integration boundary |
| --- | --- | --- |
| Protocol, UC, storage and QROM spine | `lean/Qsag/*.lean`: Goldilocks / GoldilocksExt4, binary towers, Keccak / Poseidon2, hypertrees, Baggy / Waistband / Jorts / BeltLatch, UC simulation, Hem / Canopy; `PosixCrashWal.lean` models POSIX crash/NVMe and `OpenDescriptionId` flock ownership; `ConcreteSecurityBudget.lean` supplies square-root-free unitary BBBV97/O2H and fiber-cardinality reductions | Theorems hold for their definitions and premises. Concrete profile instantiation, runtime event refinement must instantiate the multi-ledger crash/interleaving theorem in `CeremonyAtomicityAndAbort.lean`. |
| Compiler-extracted Rust MIR | Charon + Aeneas, `aeneas/qsag-verified` → `QsagMirProofs`: field/tower arithmetic, sponges, WOTS+C, BDOZ, BeltLatch, Waistband and poison-latch guards; extraction discipline: `0 FunsExternal`, `0 Classical.choice` | Fresh extraction and proof coverage must match the exact source. Guard proofs do not mediate every production release unless secret ownership and caller paths enforce that boundary. |
| CPU bytes and GPU models | `ConstantTimeIsa.lean`, `ElfBinaryVerify.lean`: decoded x86_64 AVX2/PCLMULQDQ/VPCLMULQDQ and aarch64 SHA3/PMULL, taint noninterference, scratch zero-on-exit and mutation witnesses; five SydTV loop refinements, decoded SIMD fixtures, and SPIR-V codec/race/leakage models | LNSym / x86lean / ELFSage grounding, linked ThinLTO coverage and physical semantics validation are active integration work. DOIT / PSTATE.DIT assumptions and caller/compiler leakage remain explicit. |
| Executable ground-truth gates | Native `lake exe spec-oracle` Rust ↔ Lean differential and clause-drop mutation fuzzing; native x86_64 `lake exe isa-cosim` (virtualized Linux host); `ct_dudect`; six-kernel `comparator --paranoid` CI challenge replay | Executables and CI challenge configuration exist; complete required-gate linkage to fresh extraction and exact release bytes is still being integrated. Finite tests can refute a spec; they do not prove it universally correct. |

The constructive proof policy is **0 sorry, 0 Classical.choice**, with permitted axioms `{propext, Quot.sound}`. Reported checked proofs and configured six-kernel challenges are scoped evidence, not a claim that every concurrent source edit has passed every gate. This documentation quickstart check does not rerun the formal assurance suite.

## Documentation

- [PROJECT.md](PROJECT.md): implementation status and remaining work.
- [ASSURANCE.md](ASSURANCE.md): threat models, checked surfaces and trusted boundaries.
- [Aeneas verification](docs/AENEAS_VERIFICATION.md): extraction and proof interface.
- [Constant-time assembly](docs/CONSTANT_TIME_ASM.md): ISA models and empirical timing.
- [Binary verification](docs/BINARY_RLIB_VERIFICATION.md): ELF fixtures and artifact binding.
- [Security and CT proofs](docs/SECURITY_AND_CT_PROOFS.md): protocol invariants and specification tests.
- [Migration threat model](crates/qsag-migrate/SECURITY.md): crate-specific assumptions; consult live source for profile changes.
- [Consensus scaling](docs/QUORUM_AND_CONSENSUS_SCALING.md): measured small batches, mock applications and conditional capacity models.
- [Technical paper source](paper/qsag.typ): construction details; the status documents govern current integration claims.

## License

Licensed under either of Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE)) or MIT license ([LICENSE-MIT](LICENSE-MIT)) at your option.
