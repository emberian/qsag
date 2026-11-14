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

Result on 2026-11-14 against a fresh Charon/Aeneas extraction of the current Rust source:
successful; `AuditMirAxioms` 5,244 declarations and `QsagSpecWeld` 129 declarations, none
rejected. `cargo test` in `qsag-verified`: all suites pass, parity 5/5.
`QsagVerifiedChallenge` builds with only its intentional statement placeholders.
`check_audit_coverage.py` covers all 43 proof modules. The runtime census is available as
`lake build audit-mir-axioms` followed by `.lake/build/bin/audit-mir-axioms`; the runtime
census also checked 5,244 declarations with zero rejected axioms.
`lake comparator --paranoid --inadvisably-no-sandbox` passed all 65 theorem obligations
and 17 pinned definitions, including Lean's default and paranoid kernels and all four
external checkers. The sandboxed invocation could not start because the verification host
disallows user-namespace mapping; the completed comparison used the isolated checkout.

`QsagCustodyWeld` was not rebuilt on that date: `Qsag.MaliciousSecurity` and
`Qsag.AdvancedMpcAndCreds`, which its `Qsag` imports depend on, did not compile in the
working tree. `BeltAckProvenance`, which `RealSpecBeltWeld` imports, changed since those three
modules last compiled (one proof repaired, statements unchanged).

Constructive proof conventions:
- `by_cases` on a proposition with no `Decidable` instance silently uses `Classical.choice`;
  generated enums have no `DecidableEq`, so case on the constructor instead.
- `omega` uses `Classical.choice` when an implication is among the hypotheses; `clear` it.
- `Nat.and_two_pow_sub_one_eq_mod` and `Nat.testBit_two_pow_sub_one` depend on
  `Classical.choice`; `RealSpecTowerWeld` carries a constructive replacement.
- In a `module` file, `simp only [bind_eq_result_bind, result_bind_ok]` on
  `checked_velocity_spend` exhausted 12 GB; `bind_ok_step` with `change` does not.

## Open

1. Streaming `Shake256Sponge`: absorb/pad/squeeze byte equivalence with the canonical sponge,
   across rate boundaries, and cSHAKE framing. The permutation weld does not give this.
2. Production arithmetic: `crates/qsag-core/src/field` implements Goldilocks and the towers
   separately from the verified crate. The parity tests compare them on samples; no theorem
   covers the production code until it calls the verified functions.
3. `BeltLatch` beyond `bind`: echo construction and verification (`verify_peer_echoes`), the
   log's own MAC and checkpoint, and the relation between the local quorum guard and the
   three-party network. Production `BeltLatch` does not yet call the kernel.
4. RSS session registry and caller adoption of the BDOZ opening handle:
   `RssCutGateSession::new_round1_committed` takes no prior state. The legacy BDOZ burn-on-abort
   API permits successful-opening replay; both counterexamples remain valid for those APIs.
   `BdozOpeningGuard2Lane` now consumes every attempt, binds the session and round, and clears
   both key lanes. Its constructor still requires caller-provisioned fresh keys and masks;
   it is not a persistent session registry and production callers must explicitly adopt it.
5. `EpochLatch` and `StatefulVelocityGuard` have no canonical simulation; the velocity mismatch
   is a proved counterexample (`RealSpecGuardBoundary`).
6. KoalaBear is not in the verified crate.
