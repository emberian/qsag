# qsag engineering status

**qsag — Quorum-Switching AGgregation / Quantum Succinct AGgregation**

This ledger distinguishes implemented mechanisms from integrated assurance. The project has 13 crates with zero external crates.io dependencies: 12 root workspace packages plus the separate `aeneas/qsag-verified` extraction workspace. Libraries support `no_std`; the CLI and host adapters require `std`. See the [README crate map](README.md#workspace-crate-map) for paths and public entrypoints.

## Implemented capabilities

| Surface | Present implementation | Boundary |
| --- | --- | --- |
| `qsag-core` FIPS 205 | All six SLH-DSA-SHAKE parameter sets, RSS/SPDZ threshold evaluation, DKG, refresh and reshare | Matched-input signature equality and standard verification do not establish abort-conditioned distribution equality or full production UC refinement. |
| Baggy / Waistband | Stateless hypertree + TSW, static Top-L child-root WOTS cache, 256-lane Keccak, carryless BGIN19 DZK, full 256-bit WOTS+C (`w=4`, 128 chains, target sum 192) | No message-binding leaf cache. Stateless signing does not make MPC preprocessing or custody resource accounting rollback-free. Concrete security has finite query budgets. |
| Jorts / BeltLatch | Stateful 2-of-3 signing, staged Mode 3B, crash-WAL and certified latch machinery | Reported ~1.0 ms local / ~81 ms simulated WAN excludes a complete durable authenticated deployment. Global latch safety requires `2q > n+f`; BFT availability requires `n >= 3f+1`. |
| `qsag-quorum` QS-A | `CommitteePartitionedJorts`: disjoint committee subtrees, t-of-t online signing; reported 3-of-5 ~0.56 ms loopback TCP with two offline | Committee-revealing partitioned custody. Up to f=2 corruptions is a safety-with-abort claim; corrupt online parties may prevent completion. |
| `qsag-quorum` QS-B | `BftShamirJorts`: global tree, certified BeltLatch, self-verifying pre-stepped Shamir WOTS+C | Quorum-independent leaf allocation; signing t and latch q are distinct. MAC-free WOTS checks do not remove authenticated latch/channel requirements. |
| Corduroy | Algebraic Poseidon2 stateless threshold custody hypertree | Custom construction; full production/proof composition remains under review. |
| `qsag-agg` Hem | GoldilocksExt4 WHIR, CanopyMultiProof Steiner deduplication, K-to-1 aggregation and binary-tree merging | Default `Habr24Qrom128` q=(128,64,43,32); `BciksJohnsonQrom128` q=(257,129,87,65). Mandatory QROM Grover query floor is implemented; total QROM reduction and exact-profile proof linkage remain separate. |
| `qsag-asm` | x86_64 AVX2/GFNI/PCLMULQDQ/VPCLMULQDQ and aarch64 SHA3/PMULL, runtime dispatch, timing harness | Kernel-scoped ISA and fixture evidence; no whole-process constant-time claim. |
| `qsag-fts` | FrontierSumFts and ParallelSeededFts, active DKG/sacrifice and durable burn guards | Respect per-profile use limits; the Full256Bit profile permits one safe use. OT setup and complete workflows need their own runtime checks. |
| `qsag-hd` | Secret-keyed dealerless HD custody, watch-only inventories, authorized module projections and child-MAC rekey | Honest-majority setup and authenticated confidential channels; inventory enrollment can reconstruct selected batch child seeds, not parent/subset seeds. |
| `qsag-addr` | Bech32m QsagAddress and canonical HybridPinnedEnvelope | Bind suite, identity role, HRP and pinned key; address parsing alone is not ownership proof. |
| `qsag-policy` | Authenticated rolling-window BDOZ custody guard, nonce/spend state and durable checkpoints | Real-time caps require a trusted clock/epoch authority and durable reservation before release. |
| `qsag-cred` | Threshold ML-DSA-44, 2-of-5 Poseidon2 TOPRF, six-limb BlindVC with 438-repetition Quantum128 default | ML-DSA active quorum is 2t-1; rejection transcript privacy remains heuristic. Quantum128 is a profile, not an unconditional end-to-end security theorem. |
| `qsag-migrate` | Three-custodian co-ZK ownership migration for secp256k1/Taproot/Ed25519; mandatory active pre-open Boolean and prime-field multiplication checks | Live ZKBoo default remains 219 repetitions. Active multiplication checks are implemented; full FS/QROM extraction, stronger profile integration and conditional privacy bridges remain open. |
| `qsag-accel` | AcceleratorBackend, CPU reference execution, keyed cSHAKE256 receipts | A keyed receipt authenticates a computation report; it is not hardware remote attestation. |
| `qsag-cli` | File-based keygen/sign/verify, addresses, aggregation, policy demo, KATs and seven examples | Local demos are not distributed deployment; README commands are checked separately from formal assurance. |
| `qsag-verified` | Charon/Aeneas MIR extraction and QsagMirProofs over arithmetic, sponges and custody guards | Separate workspace. Direct production linkage, fresh extraction and complete secret-release mediation are active work. |

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
| RLWE preprocessing | Extraction for the actual signed-monomial ring challenges, including exceptional differences and norm bounds; widening challenge entropy alone is insufficient. |
| Complete mediation | Secret ownership, bound output objects, non-reusable leases, poison propagation and durable release receipts across every useful network output. |
| Crash/concurrency composition | One ceremony resource authority or sound monotone multi-ledger protocol; no reuse under every crash prefix and interleaving. Per-file atomicity does not prove ceremony atomicity. |
| Transport and policy | Authenticated confidential channels, consistent broadcast, reconnect replay protection and authoritative policy epoch advancement. RAM/loopback timings do not establish these. |
| Artifact linkage | Fresh extraction, both proof-workspace audits, complete theorem/import coverage, linked binary and dispatch closure, native hardware checks and required CI dependencies. |

[ASSURANCE.md](ASSURANCE.md) states the threat models and TCB; [security proof guide](docs/SECURITY_AND_CT_PROOFS.md) maps the claims to source modules. No formal suite was rerun merely to update this ledger.

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
