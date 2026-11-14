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
- `RealSpecGuardBoundary.lean`: a concrete cross-package witness shows the monotone-nonce
  MIR guard rejecting nonce 1 from last nonce 2 while the canonical used-nonce-list model
  with burned list `[2]` accepts it. The simple field-for-field mapping cannot support
  matching rejection behavior.
- `CallerContracts.lean`: separate ML-DSA norm/commitment obligations, FTS round-count and
  residual obligations, and RSS residual obligations appear in multi-turn release theorems.
- Existing Goldilocks welds remain in the default weld. `QsagMirProofs` exports the new
  interfaces and the previous multi-turn reachability interface. Every proof source has
  an explicit import-all audit gate, checked by `check_audit_coverage.py`.

## Build and axiom gates

All Lean compilation was performed on the designated Linux build host in an isolated checkout, with
`SWARM_MEM_MAX=12G timeout --kill-after=10s 600s swarm-build lake build --wfail`.
The wrapper enforces the memory cap. No RAM-backed scratch directory was used.

The default build includes `QsagSpecWeld`. On the verified snapshot:

- Default build: 86 jobs, successful.
- `AuditMirAxioms`: 4,892 declarations, zero rejected.
- `QsagSpecWeld`: 151 declarations, zero rejected.
- Axiom allowlist: `propext`, `Quot.sound` only; negative controls remain active.
- Import coverage: 40 proof source modules, zero missing gates.

The census found and removed two imported nonconstructive dependencies during development:
`BitVec.setWidth_setWidth` in the GF(256) simplification and `List.nodup_range` in the
64-slot signer proof. The former is excluded from that simplification; the latter is
replaced with a direct kernel-checked finite proof. The axiom policy itself was not relaxed.

## Full RSS integration

The earlier snapshot failed in the sibling-owned `ThresholdMlDsaAndToprf` module.
The final upstream snapshot compiles that module and `MirSpecBridge`. The existing
RSS `ForwardSim` weld is therefore back in `QsagSpecWeld`, `QsagMirProofs`, and the
mandatory import-all `AuditMirAxioms` census. The temporary separate gate was removed;
no proof module is relegated to an optional audit target.

## Remaining proof work

1. Extend the canonical field weld beyond GF(256) to the wider tower kernels. Existing
   within-package arithmetic proofs remain, but are not new cross-package welds.
2. Weld the streaming `Shake256Sponge` absorb/squeeze/padding state to the canonical sponge.
   The full permutation weld does not establish the streaming sponge refinement.
3. Construct canonical guard simulations for `EpochLatch` and `StatefulVelocityGuard`.
   The velocity rejection mismatch is now a proved counterexample; an environment contract
   or a canonical specification change is needed for that particular mapping.
4. Relate the local authenticated quorum guard to the full Jorts network state machine
   through an appropriate environment/composition relation. The certificate-mask weld is
   not a whole-machine `ForwardSim` to the different `BeltLatch` transition system.
5. Extend semantic caller contracts to HD residual derivation, the legacy poison latch's
   `check_ok`, and the unauthenticated core's WAL flag. Policy pins require trusted
   provisioning; BDOZ operands must be connected to the external wire transcript.

None of these results establishes linkage to a production binary or fresh extraction
parity. Generated `Funs.lean`/`Types.lean`, challenge files, and sibling crate/spec sources
were not edited by this work.
