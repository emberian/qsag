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
  control. `QsagCustodyWeld` runs the same census over its four modules.

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
  apply to SHAKE and cSHAKE states. Absorb and padding are established in `SpongeFraming`; the cSHAKE constructor boundary is listed below.
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
- `RealSpecGuardBoundary.lean`: `StatefulVelocityGuard::authorize_spend`,
  `MlDsaReleaseGate::try_release_z_share` and `BeltLatchKernel::bind` are total and compute
  exactly `Qsag.mirVelocityMachine`, `Qsag.mirMlDsaReleaseMachine` and
  `Qsag.mirBeltLatchKernelMachine` (`MirSpecBridgeCore` §6A-§6C) through field-for-field
  abstractions (`velocity_extracted_step_refines`, `mlDsa_extracted_step_refines`,
  `beltLatch_extracted_step_refines`, each a lockstep `ForwardSim`).
  `extractedVelocity_multiTurn_cap_and_monotonic_nonce`, `extractedMlDsa_at_most_one_release`
  and `extractedBeltLatch_equivocation_free` are the `Qsag` multi-turn theorems restated on
  extracted traces. The velocity guard does not refine the burned-nonce policy model as a whole
  machine (`tooth_velocity_used_nonce_model_is_not_monotone_nonce`).
- `CallerContracts.lean`: what unextracted callers must establish for ML-DSA, FTS and RSS
  releases, and a concrete RSS execution showing those contracts are not derivable from the
  guard alone.

## Custody implementation and verification, 2026-11-14

- ML-DSA binds the actual response coefficients to its consuming release gate, checks
  distinct predicates, and validates the returned digest before release. Rejected attempts
  reveal only the joint failure bit. Credential debug output redacts issuance tokens.
- Policy approvals retain verified velocity state. A replay window retains all 256 admitted
  random identifiers without lexicographic eviction; exhaustion requires authenticated window
  rotation. Signer checkpoints use format V5. Generation fences latch persistence failures.
- Directory monotone anchors use two authenticated, fsynced slots. Custody wrappers use
  anchored ceremony recovery and recover the maximum committed/reserved burn cursor.
  FTS WALs and HD query budgets provide anchored and minimum-checkpoint recovery APIs.
  The anchor directory must live in an independent rollback domain; this is not hardware
  monotonic storage or protection against snapshots containing both anchor and journal.
- HD poison journals fail closed during disclosure and after I/O failures. Caller-injected
  journals support no-std rekey completion. Committed rekey zero tests, FTS epoch permits,
  and canonical grind verification are connected to production paths.
- RSS and FTS permits have private fields and move-only consumption. Same-epoch quorum
  authorization refuses a second grant. Hybrid transcript bytes match both production
  hybrid suites in differential tests. Secret buffers and polynomial drops wipe on errors.
- Extraction emits ordinary public sections and exposes only four scalar aliases in Types.
  The axiom census includes Aeneas and custody modules. The comparator preserves the original
  65 theorem and 17 definition entries and adds custody release and SHAKE byte-equality checks.

## Sponge boundary

`shake256_32_refines` proves byte equality with `Qsag.shake256Xof 32` for arbitrary input.
`sponge_squeeze_prefix` identifies every written byte of a complete short squeeze;
`sponge_squeeze32_refines` identifies those bytes with `Qsag.squeezeXofAux 32`.
`cshake256_32_refines_of_prefix` composes the same output proof with cSHAKE absorb/padding.
Its constructor premise remains open: `new_cshake256` must establish `customizationPrefix`,
including `left_encode`, zero filling and the prefix flush. Unconditional cSHAKE equality
is not claimed. Rust bit-length encoding now widens to u128 instead of saturating u64.

## Sponge phase discipline

`Shake256Sponge::absorb` asserts that squeezing has not begun, as production
`Cshake256Xof::absorb` does. The extracted definition opens with `massert (¬ self.squeezing)`:
`shake256_absorb_after_squeezing_fails` proves that a late absorb returns
`.fail .assertionFailure` for every input, and `shake256_absorb_ok_iff_absorbing` that a
successful absorb implies the absorbing phase. Earlier extractions returned the state
unchanged. `finalize` and `squeeze` stay idempotent and resumable after squeezing begins
(`shake256_finalize_after_squeezing`). No function of the crate absorbs after squeezing; the
only production use of the type is `new_cshake256(..).state` in `qsag-cred`.

## Legacy and separately implemented code

- `threshold::derive_jorts_legacy_v1_det_r_rand` (domain tag `QSAG.JORTSV1.DET`) is a legacy
  v1 model. Production derives the stateful randomizer in
  `qsag_core::tsw_baggy::derive_stateful_r_rand` as `PRF_msg` under `QSAG.PQ.BAGGYSIG.DET/v1`;
  the outputs differ and no production crate calls the legacy function. It has no theorem
  and serves only as the deterministic fixture of the `EpochLatch` retry tests. The
  `EpochLatch` theorems treat `r_rand` as opaque bytes and hold for either derivation.
- `aeneas/qsag-verified/extraction-coverage.{json,md}` (from
  `scripts/gen_extraction_coverage.py`, `--check` fails when stale) classifies every `pub fn`
  of the crate: called from `crates/**`, reached from such a function, related to production
  only through a Lean weld to a shared `Qsag` specification, proved but not welded, used by
  tests only, or unreferenced. Goldilocks and tower arithmetic are in the weld-only class:
  production has its own implementations, tied to these by the specification welds and the
  differential parity tests, not by a call.

## Validation and remaining work

Linux release tests: 301 passed across the standalone verified crate and five custody crates;
the separately invoked production OT bootstrap test also passed. No-default-feature checks
and strict no-dependency, all-target clippy checks pass. Primitive MIR targets build with
warnings treated as errors. The full custody/audit build is blocked by errors in the current
sibling-owned `Qsag.RssSlhFullSecurity` dependency (unresolved `G` identifiers).
A full zero-rejected-axiom census is therefore not certified for this snapshot.

The final repository source-policy scan passes: no forbidden proof escapes, with exposure
limit 12. Earlier sibling documentation-reference failures have been corrected.
The comparator passes 71 theorem and 25 definition checks through all six kernels. The
import-all primitive census, including logical Aeneas support declarations, checks 6,415 declarations
with zero rejected axioms. Compile-time elaborators and their generated implementation
helpers are reported outside the logical census; emitted terms and their transitive proof
dependencies are checked. The extraction manifest binds current source/output hashes and
explicitly records the blocked full pipeline. Do not substitute this primitive census for
the blocked full custody census.

Still open: the cSHAKE constructor proof; concurrent production scheduler refinement;
the private M-gate Round-2 stream; and workspace-wide adoption of anchored recovery APIs.
Production output mediation relies on Rust privacy and move semantics plus verified guard
transitions, not an extraction of the complete asynchronous scheduler. Public DKG containers
remain for existing callers; their secret element fields are opaque and their drops wipe.
