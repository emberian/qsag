# MIR verification and canonical weld status

Updated 2026-11-14 by the MIR pillar deputy. This records the delivered statements and
remaining work, rather than treating the entire pillar as complete.

## Delivered

- `BeltAckProvenance.lean`: per-bit complete mediation of the real authenticated
  `VerifiedBeltQuorumGuard.step`; chronological `BeltRun` executions include rejected calls.
  `belt_grant_authenticated_history` produces a duplicate-free set of at least `q`
  custodians below `n`, each with an earlier accepted MAC-valid ack at exactly the grant's
  epoch and message, after the pre-state was bound to that pair.
- `belt_two_grants_authenticated_intersection`: more than `f` common distinct custodians,
  with accepted authenticated evidence in each grant's own history, even across epochs.
  Enrollment is invariant. `belt_ack_seen_provisioned` attaches nonzero and uniquely
  enrolled key witnesses under `BeltProvisionedKeys`; no key secrecy or MAC unforgeability
  is inferred from successful verification alone.
- `belt_new_validated_provenance_init` discharges the empty-bitmap, quorum-configuration,
  and count/range invariants from the actual constructor. `belt_trace_to_run` connects
  the existing arbitrary-action reachability relation to the chronological history API.
- `RealSpecTowerWeld.lean`: every extracted GF(256) multiplication refines both
  `Qsag.mulExec 3` and the abstract `Qsag.towerMul 3` under canonical unpacking.
- `RealSpecHashWeld.lean`: the extracted 128-chain base-4 WOTS+C checker equals
  `Qsag.checkTargetSum 4 128 192` on its extracted digits, including length/range validity.
  A zero-digest rejection witness distinguishes acceptance from totality.
- `RealSpecKeccakWeld.lean`: one full extracted Keccak round and all 24 rounds refine
  `Qsag.roundS` and `Qsag.keccakF1600`. The array round-trip theorem extends the result
  to every extracted input array. The symbolic round is connected to MIR by individual
  bind equalities; it is not an assumed replacement for the generated function.
- `RealSpecBeltWeld.lean`: extracted grants refine the canonical Jorts `CustodiansMask`
  cardinality and intersection algebra, with the authenticated history attached to members.
- `CallerContracts.lean`: separate ML-DSA norm/commitment obligations, FTS round-count and
  residual obligations, and RSS residual obligations appear in multi-turn release theorems.
- Existing Goldilocks welds remain in the default weld. `QsagMirProofs` exports the new
  interfaces and the previous multi-turn reachability interface. Every proof source has
  an explicit import-all audit gate, checked by `check_audit_coverage.py`.

## Build and axiom gates

All Lean compilation was performed on `bb2`, in the isolated `qsag-pillar-mir` checkout, with
`SWARM_MEM_MAX=12G timeout --kill-after=10s 600s swarm-build lake build --wfail`.
The wrapper enforces the memory cap. No RAM-backed scratch directory was used.

The default build includes `QsagSpecWeld`. On the verified snapshot:

- Default build: 76 jobs, successful.
- `AuditMirAxioms`: 4,825 declarations, zero rejected.
- `QsagSpecWeld`: 81 declarations, zero rejected.
- Axiom allowlist: `propext`, `Quot.sound` only; negative controls remain active.
- Import coverage: 39 proof source modules, zero missing gates.

The census found and removed two imported nonconstructive dependencies during development:
`BitVec.setWidth_setWidth` in the GF(256) simplification and `List.nodup_range` in the
64-slot signer proof. The former is excluded from that simplification; the latter is
replaced with a direct kernel-checked finite proof. The axiom policy itself was not relaxed.

## Separate RSS gate

`AuthenticatedBeltAndRealSpecWeld.lean` still imports `Qsag.MirSpecBridge`, which imports
`Qsag.ThresholdMlDsaAndToprf`. It has its own `QsagRssSpecWeld` target and census under the
same axiom policy. It is not imported by the default targets while that upstream import
cone fails. This is a build-dependency separation, not a successful final RSS audit.

The earlier remote snapshot failed at `ThresholdMlDsaAndToprf.lean:10794:53`.
Sibling-owned spec files were not modified to bypass this failure. When the upstream
module is repaired, build `lake build --wfail QsagRssSpecWeld`, then integrate that root
into the default gate if its dependency cone is to be mandatory.

## Remaining proof work

1. Extend the canonical field weld beyond GF(256) to the wider tower kernels. Existing
   within-package arithmetic proofs remain, but are not new cross-package welds.
2. Weld the streaming `Shake256Sponge` absorb/squeeze/padding state to the canonical sponge.
   The full permutation weld does not establish the streaming sponge refinement.
3. Construct canonical guard simulations for `EpochLatch` and `StatefulVelocityGuard`.
   Existing model designs differ; the new work does not assert their equivalence.
4. Relate the local authenticated quorum guard to the full Jorts network state machine
   through an appropriate environment/composition relation. The certificate-mask weld is
   not a whole-machine `ForwardSim` to the different `BeltLatch` transition system.
5. Extend semantic caller contracts to HD residual derivation, the legacy poison latch's
   `check_ok`, and the unauthenticated core's WAL flag. Policy pins require trusted
   provisioning; BDOZ operands must be connected to the external wire transcript.
6. Complete the separate RSS dependency build and its census before claiming one green
   default audit over every proof module, including the old RSS/MirSpecBridge weld.

None of these results establishes linkage to a production binary or fresh extraction
parity. Generated `Funs.lean`/`Types.lean`, challenge files, and sibling crate/spec sources
were not edited by this work.
