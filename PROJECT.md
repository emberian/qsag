# qsag engineering status

The integrated main-library axiom audit checks **59,257 declarations, including 28,744 kernel theorem declarations, across 57 modules**, with **0 rejected axioms**. This includes private and compiler-generated declarations and 277 pure assurance-infrastructure declarations; 131 compile-time tactic declarations are excluded. Counts describe the checked definitions and premises, not complete production refinement. The combined extracted-MIR and custody audit checks **5,318 declarations / 2,093 theorems / 44 contributing modules**; the WHIR audit checks **1,558 / 718 / 7**. Both report **0 rejected axioms**. Sandboxed six-kernel challenge replay passes 107 main theorems and 65 MIR theorems plus 17 definitions.

**qsag — Quorum-Switching AGgregation / Quantum Succinct AGgregation**

This ledger distinguishes implemented mechanisms from integrated assurance. The project has 14 Rust packages with zero external crates.io dependencies: 12 root workspace packages plus `aeneas/qsag-verified` and `aeneas/qsag-whir-verified` extraction workspaces. Libraries support `no_std`; the CLI and host adapters require `std`. See the [README crate map](README.md#workspace-crate-map) for paths and public entrypoints.

## Implemented capabilities

| Surface | Present implementation | Boundary |
| --- | --- | --- |
| `qsag-core` FIPS 205 | All six SLH-DSA-SHAKE parameter sets, RSS/SPDZ threshold evaluation, DKG, refresh and reshare | Matched-input signature equality and standard verification do not establish abort-conditioned distribution equality or full production UC refinement. |
| Baggy / Waistband | Stateless hypertree + TSW, static Top-L child-root WOTS cache, 256-lane Keccak, carryless BGIN19 DZK, 256-bit digest WOTS+C (`w=4`, 128 chains, target sum 192) | No message-binding leaf cache. Stateless signing does not make MPC preprocessing or custody resource accounting rollback-free. Concrete security has finite query budgets. |
| Jorts / BeltLatch | Stateful 2-of-3 signing, staged Mode 3B, crash-WAL and certified latch machinery | Reported ~1.0 ms local / ~81 ms simulated WAN excludes a complete durable authenticated deployment. Global latch safety requires `2q > n+f`; BFT availability requires `q <= n-f` (feasible together when `n >= 3f+1`). |
| `qsag-quorum` QS-A | `CommitteePartitionedJorts`: disjoint committee subtrees, t-of-t online signing; reported 3-of-5 ~0.56 ms loopback TCP with two offline | Committee-revealing partitioned custody. Up to f=2 corruptions is a safety-with-abort claim; corrupt online parties may prevent completion. |
| `qsag-quorum` QS-B | `BftShamirJorts`: global tree, certified BeltLatch, self-verifying pre-stepped Shamir WOTS+C | Quorum-independent leaf allocation; signing t and latch q are distinct. MAC-free WOTS checks do not remove authenticated latch/channel requirements. |
| Corduroy | Algebraic Poseidon2 stateless threshold custody hypertree | Custom construction; full production/proof composition remains under review. |
| `qsag-agg` Hem | GoldilocksExt4 WHIR, CanopyMultiProof Steiner deduplication, K-to-1 aggregation and binary-tree merging | Default `Habr24Qrom128` q=(128,64,43,32); `BciksJohnsonQrom128` q=(258,130,88,66). Mandatory QROM Grover query floor is implemented; total QROM reduction and exact-profile proof linkage remain separate. |
| `qsag-asm` | x86_64 AVX2/GFNI/PCLMULQDQ/VPCLMULQDQ and aarch64 SHA3/PMULL, runtime dispatch, timing harness | Kernel-scoped ISA and fixture evidence; no whole-process constant-time claim. |
| `qsag-fts` | FrontierSumFts and ParallelSeededFts, active DKG/sacrifice and durable burn guards | Respect per-profile use limits; the Full256Bit profile permits one safe use. OT setup and complete workflows need their own runtime checks. |
| `qsag-hd` | Secret-keyed dealerless HD custody, watch-only inventories, authorized module projections and child-MAC rekey | Honest-majority setup and authenticated confidential channels; inventory enrollment can reconstruct selected batch child seeds, not parent/subset seeds. |
| `qsag-addr` | Bech32m QsagAddress and canonical HybridPinnedEnvelope | Bind suite, identity role, HRP and pinned key; address parsing alone is not ownership proof. |
| `qsag-policy` | Authenticated rolling-window BDOZ custody guard, nonce/spend state and durable checkpoints | Real-time caps require a trusted clock/epoch authority and durable reservation before release. |
| `qsag-cred` | Threshold ML-DSA-44, 2-of-5 Poseidon2 TOPRF, six-limb BlindVC with 438-repetition Quantum128 default | ML-DSA active quorum is 2t-1; rejection transcript privacy remains heuristic. Quantum128 is a profile, not an unconditional end-to-end security theorem. |
| `qsag-migrate` | Three-custodian co-ZK ownership migration for secp256k1/Taproot/Ed25519; mandatory active pre-open Boolean and prime-field multiplication checks | Live ZKBoo default is 438 repetitions. Large-prime / cubic-Goldilocks active checks have per-flush bounds <2^-249 / <2^-186 respectively; full FS/QROM extraction and production privacy refinement remain open. |
| `qsag-accel` | AcceleratorBackend, CPU reference and six Linux/std Vulkan kernels, keyed cSHAKE256 receipts | A keyed receipt authenticates a computation report; it is not hardware remote attestation. |
| `qsag-cli` | File-based keygen/sign/verify, addresses, aggregation, policy demo, KATs and seven examples | Local demos are not distributed deployment; README commands are checked separately from formal assurance. |
| `qsag-verified` | Charon/Aeneas MIR extraction and QsagMirProofs over arithmetic, sponges and custody guards | Separate workspace; live core/policy/quorum dependency. Fresh extraction and complete release mediation remain obligations. |
| `qsag-whir-verified` | Extracted WHIR arithmetic called by aggregation | Fresh extraction and protocol-level composition remain release checks. |

## Assurance architecture and remaining integration

The constructive proof discipline is **0 sorry / 0 Classical.choice**, permitted axioms `{propext, Quot.sound}`; MIR extraction also requires **0 FunsExternal**. These are scoped proof/extraction requirements, not a declaration that every live edit has passed the complete release gate.

1. **Protocol, UC, storage and QROM:** `lean/Qsag` covers field/tower and sponge algebra, hypertrees, Baggy/Waistband/Jorts/BeltLatch, UC simulation, Hem Ext4 WHIR and Canopy. `PosixCrashWal.lean` now models POSIX/NVMe crashes and `OpenDescriptionId` flock ownership. `ConcreteSecurityBudget.lean` contains square-root-free unitary BBBV97/O2H mechanics and fiber-cardinality reductions. Remaining work binds concrete runtime profiles and shared ceremony events to these models.
2. **Extracted MIR:** Charon/Aeneas connects `aeneas/qsag-verified` to `QsagMirProofs`, including WOTS+C, BDOZ, BeltLatch, Waistband and poison-latch guards. Guard correctness does not prove that unextracted callers cannot bypass the guard or splice contexts. Production ownership, release construction, scheduler refinement and fresh generated-body comparison remain integration obligations.
3. **Grounded ISA and ELF64:** `ConstantTimeIsa.lean` and `ElfBinaryVerify.lean` provide scoped taint, scratch-zeroization, decoding and mutation witnesses. LNSym / x86lean / ELFSage grounding, linked ThinLTO artifact coverage, runtime DOIT / PSTATE.DIT binding and caller-frame leakage are active work, not blanket closure.
4. **Verify your code, test your specs:** native `lake exe spec-oracle`, Rust↔Lean differential/clause-drop fuzzing, physical x86_64 `lake exe isa-cosim`, `ct_dudect` and six-kernel `comparator --paranoid` CI challenges complement proofs. Existing executables and challenge configuration must become one required dependency graph tied to exact source, extraction, security profile and release binary.

## Outstanding acceptance obligations

| Obligation | Acceptance evidence still needed |
| --- | --- |
| Per-scheme output laws | Production refinement of reference signers with matched coins, first-valid-counter selection, exhaustion/retry behavior and explicit adversarial abort. QS-A anonymity is excluded by construction. |
| Hem total security | One profile consumed by the concrete verifier and proof, with list/field/hash/union terms and an applicable multi-round QROM reduction; no squaring errors without corresponding independent checks. |
| RLWE preprocessing | Pairwise unit differences and short relaxed extraction are proved. Resolve the 143-bit challenge budget and instantiate quantum-active OT/FS security; current rejection parameter is approximately 24. |
| Complete mediation | Secret ownership, bound output objects, non-reusable leases, poison propagation and durable release receipts across every useful network output. |
| Crash/concurrency composition | Instantiate the existing multi-ledger crash/interleaving theorem against all runtime event paths, persistence contracts and rollback anchors. |
| Transport and policy | Authenticated confidential channels, consistent broadcast, reconnect replay protection and authoritative policy epoch advancement. RAM/loopback timings do not establish these. |
| Artifact linkage | Fresh extraction, both proof-workspace audits, complete theorem/import coverage, linked binary and dispatch closure, native hardware checks and required CI dependencies. |

[ASSURANCE.md](ASSURANCE.md) states the threat models and TCB; [security proof guide](docs/SECURITY_AND_CT_PROOFS.md) maps the claims to source modules. Integrated checks and remaining failures are tracked below and in the convergence record.

## Documentation quickstart validation

The isolated Linux check executed the README CLI commands with a 12 GiB memory
cap and a 600-second timeout per Cargo invocation. `info`, `kat` (43 passed,
0 failed), keygen, sign, verify, address encoding and `slh_dsa_quickstart` exited 0.
`threshold_slh_dsa_quickstart` completed RSS signing and stock verification, then
exited 124 at the time limit during Shamir DKG/SPDZ preprocessing. Its full
reshare workflow is therefore not validated by this run. Completing that example
within the bound requires implementation work outside the documentation-only scope.

The other five examples also exited 0: Hem aggregation/merge, address/policy,
few-time signatures (including restart/reuse rejection), DKG consistency/fault
rejection, and the custom accelerator backend. Overall: **12 of 13 Cargo commands
passed**, plus all three shell setup commands; the full threshold example was
the sole timeout. No Rust or Lean source was changed for this check. The isolated
build output was removed after validation.


## C-06 publication evidence and follow-up

Documentation owner: Astra. Reconciled 2026-11-14 against the live source and the claims blueprint. Parameter truth is centralized in [the security proof guide](docs/SECURITY_AND_CT_PROOFS.md#current-parameter-and-theorem-map). Production Cargo linkage is present for both extraction crates. Named advances include signed-monomial extraction, GS interpolation/factor/list algebra, adaptive unitary query bounds, multi-ledger crash/interleaving safety, multi-turn guard reachability, real-spec field/Keccak bridges, arbitrary BDOZ batches, five SydTV looping kernels and decoded SIMD fixtures. Fresh proof closure and exact release artifacts remain integration checks.

The integrated 2026-11-14 RX 6750 XT / RADV NAVI22 run uses Vulkan 1.3.289, RADV 24.2.8, one warmed sample per workload and `CpuReferenceBackend`. Timed GPU calls include submission and host transfers. All six outputs were bit-exact; the keyed receipt verified; 13 submissions were recorded. All pipelines reported Wave32, zero scratch, and zero VGPR/SGPR spills. Raw-log SHA-256: `9b128cfaa2e5904e5121732d8a79ecd1f99ce01f369b732aa39104e08a6d4fe8`.

| Workload | GPU ms | CPU reference ms | Paired ratio |
| --- | ---: | ---: | ---: |
| Poseidon2-12, 262,144 permutations | 27.38 | 2138.08 | 78.1× |
| Keccak-f[1600], 262,144 permutations | 29.67 | 104.30 | 3.5× |
| Goldilocks NTT, 2^20 | 21.40 | 246.24 | 11.5× |
| CosetLdeExt2, 2^18 → 2^20 | 15.96 | 819.54 | 51.4× |
| Poseidon2 Merkle, 2^20 leaves | 38.77 | 7930.78 | 204.6× |
| BDOZ GF(2^128) dot, 262,144 pairs | 6.25 | 68.90 | 11.0× |

These are single shared-host samples, not distributions or whole-prover measurements. Historical reports, including Merkle 19.03 ms / 432.1× and Poseidon2 12.50 ms / 173.0×, do not describe this run. The tested path explicitly selects RADV; unaudited Wave64 is rejected by the audited constructor and every BDOZ call.

`quorum_threaded_bench.rs` implements `ConfidentialWireChannel<TcpEndpoint>` Encrypt-then-MAC AEAD with real filesystem WAL/poison/seed-ledger fsync paths. The requested ext4 figures (QS-A 2-of-3 **4.37 ms**, QS-B 3-of-7 **5.21 ms**) are reported measurements whose raw execution record was not recovered here. Existing ~1.0 ms Jorts / ~0.56 ms QS-A RAM/loopback measurements remain separately scoped; offline staging, WAN latency and durable operations cannot be inferred from them.

The integrated mock runs exited 0. Alpenglow's 64-signer Habr24Qrom128 checkpoint took 4097.03 ms to prove and 8.36 ms to verify (227,470 bytes). Beam's 4×32 classical workload took 5699.04 / 45.14 ms (445,436 bytes). Its 4×32 Jorts Habr24Qrom128 workload took 5859.42 ms to prove and a 75.42 ms median to verify (864,124 bytes); the mixed 72-validator workload took 5049.91 / 76.56 ms (886,856 bytes). Beam's 8 ms verification target was missed in every regime, and proving missed 4 seconds in every regime. Successful execution does not mean those timing targets passed.

The [consensus scaling analysis](docs/QUORUM_AND_CONSENSUS_SCALING.md) distinguishes the Alpenglow and Beam mock workloads from live integrations. Hierarchical Hem retains child evidence and binds registry, epoch, quorum and disjointness. The mocks establish neither 150 ms finality nor a measured <8 ms Beam verifier or million-validator recursive proof.

Remaining C-06 publication inputs: recover the historical GPU and durable-quorum raw records; bind source-changing proof claims to the final integrated build/axiom/import/replay artifacts; remeasure end-to-end Hem on GPU. These are evidence tasks, not permission barriers. The requested bimodal M≈1.08 claim is superseded by the inspected live Gaussian rejection parameter M≈24; the two migration active-field errors must remain separate from generic Grover accounting.

The post-convergence run explicitly enabled and passed the production base-OT roundtrip/replay test. Dense-PCG depth-14/15 checks also passed; the full-height FIPS 205 threshold/KAT/distributed-TSW soak passed in 42.99 seconds. The three-party MASCOT soak did not finish within its 900-second bound (exit 124); it is not a passing result. These test results do not close the unvalidated dense-code security assumption.

Final post-convergence workspace acceptance: 608 tests passed, zero failed and 12 ignored across 33 suites; formatting, no-default-feature checking and clippy with warnings denied pass. The ignored three-party MASCOT soak was separately attempted and timed out; ignored tests are not silently counted as successes.

## Compiled-kernel freshness and SIMD verification

Codex, 2026-11-14: fresh Rust 1.99.1 release archives pass the current
kernel-byte freshness gate for 19/19 x86-64 and 9/9 AArch64 assembly symbols,
with zero changed, removed or unpinned symbols. The five separate SIMD proof
fixtures also match. The requested certificate modules and `ElfFixtureVerify`
build successfully; the fault/speculation audit checks 1,534 declarations with
zero rejected axioms. One-byte mutation and forged-provenance controls reject.

Strict compiled-code audits pass 92 x86-64 and 65 AArch64 crypto symbols,
including public dispatch wrappers. The broader assembly audit also passes
Linux ELF, Windows COFF and Apple Mach-O checks. Eight mandatory-feature SIMD
differential tests pass on Zen 5 hardware and Intel SDE; QEMU 10 and 11 fail the
AVX-512 capability probe and are not counted as successful execution. CI now
requires the new SIMD symbols and runs the verified SDE fallback.

Remaining integration evidence: the separate linked ThinLTO CLI audit did not
run because its attempted build hit two type errors in `poseidon2_mpc.rs`.
Concurrent source edits have since corrected those expressions; a fresh linked
build and audit still need to establish that gate. A whole-library Lean policy
check also reported missing aggregate imports for seven newly added modules:
`CodingTheory.BivariateFactorSplit`, `CodingTheory.BivariateGauss`,
`CodingTheory.JohnsonSetSystem`, `CodingTheory.PersistentPairsBound`,
`PrattPrimalityCert`, `Rss256TernaryRound`, and `Rss256TwoPassProductProof`.
These are separate from the passing scoped certificate build. The exact source
hashes and all successful and failed attempts are retained in the external
verification record; this entry does not claim workspace-wide CI acceptance.
