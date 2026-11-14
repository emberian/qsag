# MIR verification and canonical weld status

Updated 2026-11-14. Statements delivered, how they were checked, and what is still open.

## Layout

- `aeneas/qsag-verified`: the `no_std`, dependency-free Rust crate. `extract.sh` runs its tests
  (including differential tests against `crates/qsag-core`), Charon, Aeneas, and Lake.
- `QsagVerified/Funs.lean`, `Types.lean`: generated; never edited by hand.
- `QsagVerified/Proofs/*.lean`: proofs about the generated functions.
- `QsagSpecWeld`: welds of extracted primitives to the `Qsag` specifications of the same
  primitives (`RealSpecFieldWeld`, `RealSpecTowerWeld`, `RealSpecHashWeld`,
  `RealSpecKeccakWeld`). Imports only primitive `Qsag` modules.
- `QsagCustodyWeld`: welds whose statements mention protocol specifications
  (`AuthenticatedBeltAndRealSpecWeld`, `RealSpecBeltWeld`, `RealSpecGuardBoundary`). Needs
  `Qsag.MirSpecBridge` and `Qsag.JortsBeltLatchAndQuorumSwitching` to build.
- `AuditMirAxioms`: axiom census (`propext`, `Quot.sound` only) over every declaration of the
  extraction, the proofs and `QsagSpecWeld`, with required-theorem anchors and a negative
  control. `QsagCustodyWeld` runs the same census over its three modules.

## Delivered

Fields.
- Goldilocks add/sub/mul/inverse refine `Qsag.Goldilocks`; `goldilocks_inverse_mul_eq_one`
  gives `a * a⁻¹ = 1` in MIR for every nonzero residue, and `goldilocks_inv_none_iff_zero`
  pins the `Option` behaviour.
- Binary towers: `gf256_mul_refines_qsag`, `tower128_mul_refines_qsag`,
  `tower256_mul_refines_qsag` and the three addition welds identify every extracted tower
  operation with `Qsag.towerMul` / `Qsag.towerAdd` at levels 3, 7 and 8. The wide levels come
  from one level-generic Karatsuba step. `tower128_mul_eq_zero_iff`: the extracted product has
  no zero divisors.

Hashing.
- The comparator now checks the full Keccak zero-state vector (lane 0
  `0xF1258F7940E1DDE7`), universal permutation refinement, exact big-endian ADRS layout,
  and every WOTS chain step against iteration of the extracted F with successive addresses.
  Specification definitions are explicitly pinned in `comparator.json`.
- `SpongeConformance`: each squeeze step writes the exact little-endian rate byte;
  rate-boundary steps apply canonical `Qsag.keccakF1600` and reset the offset. These laws
  apply to SHAKE and cSHAKE states. They do not establish absorb/padding/framing equivalence.
- One Keccak round and the 24-round permutation refine `Qsag.keccakF1600` on every state.
- The 128-chain base-4 WOTS+C digit check equals `Qsag.checkTargetSum 4 128 192`.

Guards (multi-turn, arbitrary request sequences including refusals).
- `BdozConsumption`: the extracted one-shot opening API terminates on all inputs, clears
  keys on every attempt, rejects every subsequent use, and accepts only the provisioned
  session/round after actual MAC verification. Rust tests cover successful-use replay,
  context mismatches, tag/MAC tampering, empty batches, and retries following rejection.
- The comparator includes exact arbitrary-length BDOZ batch acceptance and canonical
  Tower128 multiplication, including its zero-product characterization.
- `BeltLatchKernel.lean`: the transition kernel of production `BeltLatch::bind`, with the
  durable write as an input. `belt_latch_bind_eq` (total, closed form);
  `belt_latch_epoch_binding_unique` (two accepted binds of one epoch carry the same digest,
  salt and digits, and the later is a replay); `belt_latch_fresh_epochs_increase`;
  `belt_latch_poison_absorbing`; `belt_latch_failed_persist_binds_nothing`;
  `belt_latch_recover_then_replay`. `tests/parity_qsag_core.rs` drives the kernel and
  production `BeltLatch<MemoryWal>` with the same requests.
- `BeltAckProvenance.lean`: every certified grant of the authenticated quorum guard has at
  least `q` distinct enrolled custodians with earlier accepted MAC-valid acknowledgments;
  two grants share more than `f` of them. `inhabited_belt_one_fault_multi_epoch` is the
  `n=3, t=2, f=1, q=3` two-epoch witness.
- `MultiTurnMediationAndReachability.lean`: `bdoz_generated_loop_fold` and
  `bdoz_verify_arbitrary_batch` give exact acceptance of the BDOZ verifier for batches of any
  length; `bdoz_successful_trace_checks_every_batch` lifts it to traces.
- `PolicyAndAddr.lean`: `checked_velocity_spend_spec`, the helper production admission calls.
- `CallerContracts.lean`: what unextracted callers must establish for ML-DSA, FTS and RSS
  releases, and a concrete RSS execution showing those contracts are not derivable from the
  guard alone.

## Gates

Run on the Linux build host with `CARGO_BUILD_JOBS=4 SWARM_MEM_MAX=8G timeout --kill-after=10s 600s`:

    lake build --wfail QsagVerified QsagSpecWeld AuditMirAxioms QsagMirProofs

Integrated result on 2026-11-14: warning-free QsagVerified, QsagSpecWeld,
QsagCustodyWeld, AuditMirAxioms and QsagMirProofs build. Runtime census:
5,318 declarations, 2,093 theorems, 44 contributing modules, zero rejected.
The primitive compile-time census is 5,244 declarations. Both extraction crates'
Rust tests pass (24 tests). Both extraction pipelines were rerun successfully after the review. Exact source,
prelude and generated-output digests plus extractor binary hashes are recorded in
the extraction-provenance manifests; CI checks them without rebuilding.

The challenge builds with intentional statement placeholders. On the Linux primary host,
`python3 ../../scripts/run_mir_comparator.py` passed all 65 theorem obligations
and 17 definitions in the default sandbox with all six kernels. The runner
bundles the local Lean dependency inside a disposable package snapshot.


## Custody work, 2026-11-14 — partial, not convergence closure

Implemented on hbox in `the isolated Linux build directory`:

- Quorum isolated RSS traffic MAC keys are derived from provisioning keys and the
  reserved session ID. The regression checks peer agreement and cross-session MAC
  replay refusal. This does not establish the separate private M-gate Round-2 stream.
- `SharedWindowSpendLedger` retains the extracted `StatefulVelocityGuard` across
  approvals and rotations. Its generation supplies monotone request nonces; the
  authenticated, policy-bound, rollback-checked recovery boundary reconstructs the
  guard with the retained cap and spent amount. Release requires its acceptance.
  Rotation, recovery, cumulative spend and direct over-cap refusal regressions pass.
  Signer-local guards still reconstruct temporary verified guards and remain open.
- `sponge_absorb_byte` proves the exact input-byte write and full-rate transition to
  the canonical Keccak permutation. Arbitrary multi-block SHAKE/cSHAKE framing
  equivalence remains open; the existing totality theorem is not that equivalence.

Validation: the requested six-package no-default-feature check and clippy command
exit successfully; the release suite has 241 passed, zero failed or ignored.
The parity-test mirror emits four pre-existing `testing-ephemeral` cfg warnings.
The warning-free MIR targets and runtime census pass: 5,320 declarations, 2,095
 theorem declarations, 44 modules, zero rejected axioms. Extraction provenance
still passes for all 22 bound files; no extracted Rust source or generated MIR
changed. The 65 theorem / 17 definition comparator roster is unchanged.

Sandboxed replay was attempted but blocked before kernel execution:
`bwrap: setting up uid map: Permission denied`. hbox has
`kernel.apparmor_restrict_unprivileged_userns = 1`; no host security setting was
changed and no unsandboxed fallback was used. `scan_badwords.py` is absent on both
hosts; the repository CI scanner `scripts/check_lean_policy.py` passes 136 files
with exposure limit 12. Commands/logs and fingerprints are in the prior verification logs.

The "still outstanding" list that closed this section on its first writing is superseded by
the next section.

## Custody continuation, 2026-11-14 (second pass)

What each item below establishes and what it does not.

Sponge absorb and padding (`QsagVerified/Proofs/SpongeFraming.lean`).
- `load_le_u64_refines`, `xor_rate_block_refines`: the extracted lane load and rate-block XOR
  are `Qsag.loadLe64` / `Qsag.xorRate136` on every state and block.
- `SpongeAbsorbed sp msg` (existential-free reading: `SpongeAbsorbed.canonical`).
  `sponge_absorb_refines`: `absorb` appends its whole argument, for any length and any buffer
  fill; `sponge_absorb_all_refines`: the result depends only on the concatenation, not on the
  split into calls.
- `sponge_finalize_refines`: `finalize` leaves `Qsag.absorbPadded (Qsag.padForRate msg suffix)`
  for the sponge's own suffix, including the 135-pending-byte case where suffix and `0x80`
  share a byte. `shake256_absorb_pad_refines` and `shake256_xof_from_extracted_state` compose
  these from `new_shake256`: `Qsag.shake256Xof` squeezes from exactly the extracted state.
- `cshake256_absorb_pad_refines`: the same for cSHAKE256, for a sponge that has absorbed
  `Qsag.customizationPrefix` and carries suffix `0x04`.
- Open: that `new_cshake256` establishes that hypothesis (the `left_encode` loops, `bytepad`
  zero fill and prefix flush), and identification of squeezed bytes with
  `Qsag.squeezeXofAux` (only the per-byte and rollover laws of `SpongeConformance` exist).
  So `shake256_32` / `cshake256_32` are not yet equated with `Qsag.shake256Xof 32` /
  `Qsag.cshake256Xof 32` as byte strings.

Consuming opening guard (`qsag-verified/src/opening_guard.rs`, extracted;
`QsagVerified/Proofs/ConsumingOpening.lean`, `CustodyMediation.lean`).
- `ConsumingOpeningGuard2Lane` is bound to a session, round and transcript binding, folds
  openings (commitment digest, recomputed digest, two GF(2^128) lanes under XOR) and decides
  once. `OpeningReleasePermit` has private fields and no other constructor. The decision uses
  addition only, so it is independent of the multiplication basis; this is why it fits the
  polynomial-basis production protocol where the Tower128 handle did not.
- `opening_verify_once_eq` (total closed form), `opening_verify_once_single_consumption`,
  `opening_round_permit_sound` / `_complete` / `_refused` for construction, any sequence of
  `absorb_opening` calls and one `verify_once`, `opening_round_single_release`.
  `sigma_release_iff` and `plane_open_release_iff` state the two production call shapes.
- Production: `qsag-policy` mints `AuthorizedSignReleaseToken` only through
  `AuthorizedSignReleaseToken::mint`, which takes the permit of `release_sigma_round`, in both
  the in-process barrier and the per-party phase machine. `qsag-quorum` reconstructs opened
  lanes only in `reconstruct_opened`, which takes the permit of the opening round.
- Not proved: that production constructs its outputs only from the permit (Rust privacy and
  move semantics), and the commitment recomputation, which stays in production code and is
  compared by the guard. The Tower128 `BdozOpeningGuard2Lane` remains unused by production.
  `RssOpenPermit` in `pants_and_quorum_guards.rs` is still `Copy` with a public field.

Signer-local verified velocity state (`qsag-policy`).
- `PolicySignerGuardShare` retains one extracted `StatefulVelocityGuard` across approvals and
  window rotations; approvals commit through `authorize_spend` with a monotone request nonce.
  The guard is pinned to the policy cap on first use; a cap change or a restore rebuilds it by
  replaying the recorded spend through the verified transition. Checkpoints are format V4 and
  carry the request nonce and pinned cap; restore rebuilds the guard before mutating the
  ledger. `policy_velocity_guard_multiturn_cap_sound` covers every such trace.
- V3 checkpoints are not readable by this version.

Raw-secret surfaces (`qsag-fts`, `qsag-cred`, `qsag-hd`): sealed fields, removed raw-share
accessors and `Clone`, redacted `Debug`, wiping drops, and test-only gating of the in-memory
poison journal and unchecked child-seed recovery, each pinned by a `compile_fail` doctest or
unit test. Left open: `ParallelSeededDkgOutput.beaver_triples` / `pk_seed_bytes` stay public
(a `qsag-cli` example reads them); a no-`std` `qsag-hd` build can no longer finish a rekey,
because its only completion path was the in-memory journal; `BlindVerifiableCredential` stays
publicly constructible and its `Debug` prints `issuance_token`.

Validation on hbox (the prior verification logs): `cargo check --no-default-features` and
`cargo clippy --all-targets -- -D warnings` over `qsag-verified` and the five custody crates
exit 0 (the four `testing-ephemeral` cfg warnings of the parity-test mirror remain);
`cargo check --workspace --all-targets` exits 0; `cargo test --release` over the six
packages: 274 passed, 0 failed, 0 ignored; `qsag-policy --features std`: 23 passed.
`lake build --wfail QsagVerified QsagSpecWeld QsagCustodyWeld AuditMirAxioms QsagMirProofs`
succeeds; compile-time census 5,497 declarations, custody weld 85, runtime census 5,579
declarations, 2,263 theorems, 47 modules, zero rejected. Extraction was rerun with the pinned
Charon/Aeneas binaries; the diff to the generated files is additive and provenance passes for
23 bound files. On bb2, `python3 scripts/run_mir_comparator.py` passed in the default sandbox
with all six kernels; the 65 theorem / 17 definition roster, `QsagVerifiedChallenge.lean` and
`comparator.json` are unchanged.

Still open for C-02d / C-04a: the two sponge items above; a proof of the concurrent
production scheduler; the separate private M-gate Round-2 stream; and the remaining public
surfaces listed above. No convergence row is marked closed by this work.
