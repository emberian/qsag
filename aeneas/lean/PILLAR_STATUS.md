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
Rust tests pass (24 tests). Both extraction pipelines were rerun successfully after the rake. Exact source,
prelude and generated-output digests plus extractor binary hashes are recorded in
the extraction-provenance manifests; CI checks them without rebuilding.

The challenge builds with intentional statement placeholders. On the Linux primary host,
`python3 ../../scripts/run_mir_comparator.py` passed all 65 theorem obligations
and 17 definitions in the default sandbox with all six kernels. The runner
bundles the local Lean dependency inside a disposable package snapshot.


## Wave-4 custody work, 2026-11-14 — partial, not convergence closure

Implemented on hbox in `/home/hbox/qsag-w4-mir`:

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
with exposure limit 12. Commands/logs and fingerprints are in `wave4-evidence/`.

Still outstanding: production consuming-BDOZ adoption; persistent signer-local
verified state; complete raw-secret/output mediation across the five crates;
concurrent-scheduler refinement; and full multi-block sponge/framing equivalence.
The verified BDOZ handle uses Wiedemann tower multiplication and per-wire masked
commitments; policy uses polynomial-basis GF(2^128) and aggregate sigma commitments.
Adoption requires a proved representation/protocol bridge or an extracted handle
matching that production protocol, not casting the existing u128 values into Tower128.
No C-02d, C-04a, or Fable disposition is marked closed by this work.
