# Convergence and construction acceptance

Current source reconciliation: 2026-11-14.

## Current construction status

The current runtime defaults to Johnson QROM; capacity-proximity tags reject. RLWE now uses 24×11-bit signed-monomial challenges and joint Q192 Gaussian rejection with M≈40. ML-DSA-44/65/87 are enabled. Earlier profile values and measurements below describe their recorded source snapshots.

The compact Hem authorization API now requires locally verified child evidence bound to the exact context and proof digests. Its outer AIR is still a public commitment chain, so genuine recursive child verification remains open. Hem quorum lifecycle APIs now require private per-party RNGs; public session IDs are context, never key-generation entropy. These are source changes with targeted validation tracked separately from the old workspace acceptance.

The [construction proof ledger](../PROJECT.md#construction-proof-obligations) governs current open work: actual ideal-functionality refinement, CWYZ decomposition, arbitrary-batch/multistage RBR soundness, coherent-query extraction, actual hash attack reductions, production sampler hypotheses and retry/abort privacy. A passing axiom census cannot discharge those semantic premises.

The scoped Lean 4.35 check of `QromExtractionBoundary.lean` passed, including five constructively audited theorems about measured-query branch masses, response/Merkle consistency, locality and recording disturbance. This is a measured-query interface, with coherent-execution extraction still a separate instantiation task.

The later named-kernel freshness run passed 19/19 x86-64 and 9/9 AArch64 kernels and certificate checks; it supersedes the historical ELF failure below. Linked-program coverage remains separate.

## Recorded earlier integration snapshot

The remaining sections preserve the earlier 2026-11-14 source snapshot and its acceptance records. Their PASS/FAIL labels and counts are historical, not a fresh validation of the current tree. Subsequent changes and unresolved obligations above take precedence.

This was the integrated acceptance snapshot. A successful build is distinct from production refinement, cryptographic composition, artifact freshness, and performance acceptance. The release is not certified while the open entries below remain.

## Earlier audit gap disposition

| Gap | Integrated work | Outstanding acceptance |
| --- | --- | --- |
| C-01: Corduroy/Hem/QROM | AIR imported; pointwise row/boundary/shift equivalences; guarded opcode next-state construction with rejection and non-Idle inhabitedness gates; formal list/query accounting | Active-slot completeness; native signature witness extraction; the 256-column/14-column layout bridge; applicable Johnson-radius soundness and quantum commitment extraction. |
| C-02a: protocol challenge | Repaired theorem roster and independent challenge statements | Sandboxed six-kernel replay passes all 107 configured main theorems. |
| C-02b/c: foundation | Nested FIPS signature shapes; injective canonical threshold authorization encoding; strict inhabited/tooth registrations; downstream caller repairs | Full implementation-to-spec refinement is distinct from these checks. |
| C-02d: MIR challenge | Keccak, ADRS, WOTS steps, sponge byte/rollover, session-bound consuming BDOZ handle; independent challenge helper modules retain exposure semantics | Full sponge absorb/framing equivalence and production adoption of the consuming handle remain separate. |
| C-03: active MPC | Production HashSigs refinements, coin framing, custody/Jorts bridge repairs | Private M-gate Round-2 stream; reduction of `advCoinHide`; active `RealProtocolExec` and Shamir signer composition. |
| C-04a: custody linkage | FTS, credentials and HD link the extracted crate and call their release gates; workspace tests pass, and the CI formatting gate is repaired | Prove complete mediation for raw secret ownership, output construction and the concurrent production scheduler. |
| C-04b: coverage/CI | All top-level protocol modules included in the library and audit imports, including recovered ELF and AIR modules; private-environment audit executables; source-policy CI; linked-binary instruction screen | Current assembly fixtures fail freshness. Whole linked-binary leakage/dispatch coverage remains open. Both configured challenge replays now pass all six kernels in the sandbox. |
| C-05a: Rust/model divergence | Persistent fault-cache and ceremony context fields landed; production-model fault/crash theorems repaired | End-to-end trace refinement, codec roundtrips, dirty-cache process restart and append-crash composition remain open. |
| C-05b: core/PCG | Seed/ownership/DKG fixes and policy-gated multi-layer Corduroy test landed; RSS folding parallelized | Full threshold quickstart exceeds 25 seconds. Integrate dense-PCG-backed triple vaults with renewed uniformity, sacrifice and caller refinement proofs; preserve the present soundness checks until that work is validated. |
| C-05c: CLI and legacy KAT | Persistence changes, canonical KAT target and workspace validation landed | Retain crash/restart coverage when changing journal formats or reservation order. |
| C-06: publication truth | Current GPU and mock-chain measurements replace unbound headlines; historical certificates explicitly scoped | Full Hem GPU acceleration and historic durable-quorum measurements need their own evidence; no whole-system QROM or production-equivalence claim follows from local theorems. |

## Additional carried obligations

- Production curve and sacrifice refinements; full-presentation privacy, seed/FS and concurrent composition reductions.
- POSIX/Rust syscall-order refinement, whole-directory crash behavior, codec roundtrips, and append-host nontruncation/external-anchor composition. Crash-safe modeled transitions do not prove that every live caller follows them.
- At this snapshot the RLWE rejection parameter was approximately 24 (current joint parameter: approximately 40). The proposed bimodal sampler does not preserve the extraction argument and is not an accepted replacement.
- Runtime shader functional equivalence to the modeled SPIR-V subset remains open. Bit-exact GPU comparisons and telemetry are separate evidence.
- At this snapshot the binary differed from the historical certificate fixtures in all 16 x86 kernels and one of seven AArch64 kernels; five new kernels lack full historical-certificate coverage. Refresh code, decoder coverage, contracts, invariants and byte-pinned functional proofs together.
- Both mock-chain programs return success, but Beam's 8 ms verification target is missed in all measured regimes. All final measured regimes also miss the 4-second proving target.

The strict live-spec differential run passes 1,952/1,952 vectors with zero mismatches, 500 modeled WAL schedules, 500 Rust latch schedules, 500 quorum checks, 700 certificate cases, 1,100 field metamorphic checks, 100 RSS/party-subset metamorphic checks and 64 ledger cases. All 13 production-source mutations are detected. The crash adapter reconstructs durable contents on restart and discards the pending test-only fault flag; it does not establish POSIX crash refinement. Post-convergence findings are dispositioned below. None of these obligations is a permission barrier or delegated back to the user.

The four-layer bridge now separates its model/simulation core from concrete trace witnesses behind the existing `Qsag.MirSpecBridge` entry point. The core passes its warning-free build. The concrete witness integration and full-library census now pass: 59,257 declarations, 28,744 kernel theorem declarations, 57 modules, zero rejected axioms. The compile-time census checks 58,980 declarations in 56 proof modules and 277 pure assurance-infrastructure declarations; 131 compile-time tactic declarations are excluded. The accepted two-turn witness remains in the public entry module. Shared digest and ML-DSA parameter modules remove cross-module name collisions.

The integrated MIR build, including custody, passes `--wfail`; its combined runtime census reports 5,318 declarations, 2,093 theorems, 44 contributing modules and zero rejected axioms. The separate custody compile-time census checks 77 declarations. WHIR passes its build and runtime census: 1,558 declarations, 718 theorems, seven modules, zero rejected axioms. Both intentional challenge libraries build without errors.

Sandboxed challenge replay passes on the Linux primary host: 107 main theorems; 65 MIR theorems and 17 definitions. The MIR package uses `scripts/run_mir_comparator.py` to copy its local main-library dependency inside an isolated package snapshot; only the copied Lake dependency paths change, and the default bubblewrap sandbox stays enabled. CI uses this runner for the MIR job. No unsandboxed result is used for this acceptance record.

## Post-convergence adversarial review disposition

Three independent Fable review shards inspected Lean/gates, Rust/custody/GPU, and publications/CI. Their reports were retained outside the public repository; this table records the actionable conclusions, including unresolved work. A clarified scope is not a repaired implementation.

| Review items | Disposition |
| --- | --- |
| Lean F1–F3; Rust D3–D4/I3 | Corrected bridge and production-guard claims. **Open implementation work:** session-fresh Round-2 keys and replay rejection; transcript/signature safety predicates; separated-party refinement; ML-DSA independently checked evidence; persistent verified policy state. |
| Lean F4/F10 | Explicitly scoped bridge/ELF additions and custody welds as audit-only, outside the challenge roster. The witness asserts existence; hidden concrete definitions are not an exported reduction API. Registration and expanded replay remain open. |
| Lean F5; publication F5 | Both sandboxed comparator runs finished successfully after the reviewers' evidence snapshots. Final log inventory supersedes the interrupted intermediate logs. WHIR remains audit-only. |
| Lean F6/F9; publication F6/F12 | Runtime censuses now execute in CI; the Lean disk manifest walk is recursive; source lexer handles quoted characters; executable substitution attributes are rejected in the proof library; WHIR disk coverage is checked. |
| Lean F7 | The trait-dictionary elaborator now rejects self-reference except the ignored Eq marker argument. The project-written prelude is explicitly identified as trusted semantics. Prelude unification and explicit Rust enum discriminant support remain open; present extraction uses implicit discriminants. |
| Lean F8; publication F1/F2/F3/F11 | Historical ELF provenance is explicit in primary publications, stale identifiers are corrected, README links the reproducible paper source, tables and MIR status are synchronized. |
| Rust D1 | Production poison journals require an external monotone anchor. Truncation, crash-before-anchor-advance, and lineage regressions pass. Deployment still needs a real anchor outside the disk rollback domain. |
| Rust D2 | Candidate values, digest/fold copies and MAC-share buffers have wipe-on-drop ownership. All party checks precede release; fault and accelerator-error regressions pass. This is not a whole-process erasure proof. |
| Rust D5/D7/D9 | Obsolete sparse PCG is restricted to tests; volatile MemoryWal requires the explicit test feature; unused plaintext degree-check APIs are removed. The live compatibility entrypoint still uses KOS/MASCOT. |
| Rust D6/D8 | GPU staging error cleanup, audited secret-slot enforcement, visible fallback counts and SPIR-V 1.5 receipt identity pass the physical RADV hardware tests and six-kernel benchmark. Receipt domain changes invalidate old receipts. Device-loss limits remain explicit. |
| Rust I1/I2; E1/E3/E4 | Ceremony contexts still need live callers; dense PCG is standalone; the production base-OT and full-height FIPS threshold/KAT/TSW soaks pass, depth-14/15 dense-PCG checks pass, but the three-party MASCOT soak timed out at 900 seconds. Boolean migration bound and tape-abort liveness caveats are stated. File-backed benchmark fixtures exclude external anchor cost. |
| Rust E2 | Embedded shaders are regenerated with glslangValidator 14.3.0 and compared without modifying them; all six match. GPU ratios use the scalar reference, not a tuned CPU baseline. The default Wave64 driver was directly refused; RADV passes. |
| Publication F4/F8 | Linked screens require every assembly kernel and report Rust namespace coverage; callers can require specific namespaces. Whole linked Rust coverage remains open. Freshness CI compares kernel bytes; object hashes remain provenance evidence. |
| Publication F7 | Rust toolchain is pinned; strict quickstart acceptance uses 25 seconds. Quickstart and fixture freshness remain visible failing gates. Hosted CI has not run on this unpushed tree; no run URL is claimed. |
| Publication F9 | Fresh extraction is rerun and recorded with exact source/prelude/generated-file and extractor-binary digests; CI checks those bindings. This establishes recorded freshness, not compiler correctness. |
| Publication F10/F13/F14 | Differential runner supports hosts without the resource wrapper and reports per-witness Lean coverage (8/13); fixed-seed and 25,600-trace timing-test scope are explicit. Ignored production soaks are not counted as passes. |

The remaining C-01/C-03/C-04/C-05 security, performance, whole-system refinement and fresh machine-code certificate obligations above are still release blockers. They have not been converted into passed gates by documentation edits.

## Executed acceptance gates

| Gate | Result and scope |
| --- | --- |
| Main Lean warning-free targets and runtime census | PASS; 59,257 / 28,744 / 57, zero rejected. Recursive disk coverage includes infrastructure. |
| MIR/custody and WHIR | PASS; 5,318 / 2,093 / 44 and 1,558 / 718 / 7, zero rejected. Fresh extraction and exact provenance bindings pass for both packages. |
| Main and MIR challenge replay | Both configured rosters pass all six kernels in the default sandbox again after the rake. |
| Rust workspace | PASS: formatting, workspace no-default-feature check, clippy with warnings denied, and release tests: 608 passed, zero failed, 12 ignored across 33 suites. |
| GPU | Physical RX 6750 XT/RADV: all six outputs bit-exact, keyed receipt accepted, 13 submissions, zero CPU fallbacks. New error-path and audit-enforcement tests pass. Default Wave64 driver is refused. |
| Cross-KAT / ISA / SIMD / SydTV | 277 cross-KAT vectors and 279 negative result/count probes; 7,184 ISA vectors / 7,753 instructions; 512 SIMD batches per primitive; both SydTV architecture cuts and negative controls pass. ISA host is virtualized. |
| Strict differential suite | 1,952 vectors and 5,416 total checks, zero mismatches; all 13 clause-drop mutants detected (eight Lean-cross-checked). |
| Production soaks | Base OT and full-height FIPS threshold/KAT/TSW pass; dense-PCG depth-14/15 checks pass. Three-party MASCOT times out at 900 seconds (exit 124). |
| Quickstart | FAIL: the 25-second bound expires. No performance pass is claimed. |
| ELF freshness | FAIL: 0/16 x86 and 6/7 AArch64 historical kernels match; five live kernels lack certificates. Instruction screens are separate from this failure. |
| Mock-chain timings | Programs pass; Beam verification misses 8 ms in all regimes, and proving misses 4 seconds in all final measured regimes. |
| Publication | Paper and poster compile with no warnings/errors; 13 and four pages, visually inspected. |

The GPU receipt domain changed to V4 and the architecture tag now states SPIR-V 1.5. Earlier receipt pins are historical. The final single-sample GPU log is identified by SHA-256 `9b128cfaa2e5904e5121732d8a79ecd1f99ce01f369b732aa39104e08a6d4fe8`; its paired scalar-reference timings are reproduced in PROJECT.md and both publications.

The machine-readable acceptance record is [CONVERGENCE_EVIDENCE.json](CONVERGENCE_EVIDENCE.json); [CONVERGENCE_SOURCE.json](CONVERGENCE_SOURCE.json) pins the 350 source/control files checked on the primary host. The canonical sorted JSON source-map digest is `88a549fff899dc481c07bcbc91c114d8b3b529b1df9744efe8d3a1ca15868612`. Both build hosts had the same 172-file Rust source fingerprint, `3b104d9e2183809a6bafcb5383c135badbc2eff656e97bb63d7883fbf0b83562`.

Cleanup completed after evidence retention: both designated warm main-library caches reproduce the final census. Temporary convergence and deputy checkouts are removed; the recorded source tree was committed unsigned and was not pushed. This does not describe subsequent working-tree changes.
