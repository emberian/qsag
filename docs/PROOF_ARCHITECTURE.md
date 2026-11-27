# QSAG proof architecture

The three Lean packages answer different questions. The protocol library defines games and machines. The custody and WHIR packages translate Rust MIR to Lean and prove properties of the generated functions. The archive proofs start from decoded instruction fixtures. The exact audit counts, comparator rosters and replay results are recorded together. [Assurance evidence](../ASSURANCE.md#formal-evidence)

## Following a claim

1. Start at the relevant ideal machine. Its input ports, accepted outputs and error transition determine the observable contract. [Specifications](../lean/Qsag/Spec)
2. Read the declaration in the domain’s top-level module, including its parameters. A `Spec.Refines` witness relates steps of two machines. A `Spec.GameBound` compares a particular game probability with a rational number. A `RatBound.lt` conclusion alone is an arithmetic comparison. [Top-level modules](../lean/Qsag/Top)
3. Follow imports to the implementation boundary. A proof about a Lean model reaches an extracted Rust function when a theorem actually relates the model to the generated function. The corresponding statement for an ISA kernel names the decoded program and its preconditions. [Custody MIR proofs](../aeneas/lean/QsagVerified/Proofs) · [WHIR MIR proofs](../aeneas/lean-whir/QsagWhirVerified) · [ISA inventory](BINARY_RLIB_VERIFICATION.md)
4. Check what the kernel replay selected. The main challenge imports solution modules and reproduces selected statements. The six pinned main definitions and the selected theorem statements are enumerated in the manifest. [Main comparator](../lean/comparator.json)

## Protocol contracts

**Signing.** The latched-machine simulation preserves signed outputs and constrains epoch reuse. The execution-level EUF-CMA reductions quantify over the signing experiment and bounds for its primitives. The suffix `_of_primitive_bounds` identifies that premise. Hash-oracle idealization and numerical substitution are distinct steps. [Signing](../lean/Qsag/Top/Signing.lean) · [Production parameters and bounds](../lean/Qsag/Protocol/Signing/ProductionJortsBaggyBounds.lean)

**Custody.** Fresh signing uses an inclusive epoch window. A retry can replay a matching WAL entry. Public authenticated acknowledgements omit the Shamir share. The reconstruction model reads the share through a private input and models corruption separately. The concrete velocity, belt and ML-DSA transitions have lockstep simulations from Aeneas functions. In particular, `extractedVelocity_approved_nonces_nodup` transfers the monotone model’s invariant to extracted traces. The instruction model executes decoded x86-64 equality and zeroization routines and specifies the coordinator in Lean. The composition takes signature compatibility and an initial-state relation as premises. Its nonce-set policy has a different admission rule. [Ideal custody](../lean/Qsag/Spec/IdealCustody.lean) · [Public and private inputs](../lean/Qsag/Custody/DistributedAuthRun.lean) · [Extracted guard boundary](../aeneas/lean/QsagVerified/Proofs/RealSpecGuardBoundary.lean)

**Credentials.** The ideal machine authenticates commands by port, stores time separately for each verifier and checks challenge expiry against that stored time. A verifier can advance its clock between issuance and presentation. The Shamir-SPDZ model proves honest arithmetic and the alternatives for a false release. Its MAC-forgery experiment assumes valid setup and a fixed value distribution across the secret keys. End-to-end service refinement requires a concrete implementation of the authenticated credential interface. [Ideal credentials](../lean/Qsag/Spec/IdealCred.lean) · [SPDZ arithmetic](../lean/Qsag/Protocol/Credentials/ToprfSpdzArithmeticRefinement.lean) · [Service interface](../lean/Qsag/Top/Credentials.lean)

**Migration.** Conservation and nullifier uniqueness hold for the ideal ledger. Read the settlement refinement with its wire decoder, ownership relation and collision alternative. The concrete elliptic-curve witness uses `secp7Mod43` with subgroup order 31. Production settlement statements carrying `PrimeOrderGroup` require the curve group laws. The prime-modulus certificates discharge only primality. [Migration](../lean/Qsag/Top/Migration.lean)

**Aggregation.** The challenge field has five Goldilocks coefficients in the power basis modulo $X^5-3$. For all thirteen production sizes, the schedule arithmetic computes a bound below $2^{-128}$ under the advertised query cap. The one-stage 64-point and three-stage 256-point examples inhabit `WhirScheduleCert` for their own environments. The deployed reduction takes its round certificate as an argument. The packed sampler reads positions after five 400-bit field slices. Every packed query position is zero with a 400-bit seed. At that width the original five-independent-point charge permits zero bad seeds at the first out-of-domain round. The seeded reduction instead charges a single effective point and still requires its own round certificate. For the full 10,544-bit challenge, separate theorems bound all-position hits at each stage and first-stage out-of-domain collisions. [Field](../lean/Qsag/Math/QuinticExt5.lean) · [Reduced certificates and position sampler](../lean/Qsag/Protocol/Aggregation/QuinticMultiStageWhir.lean) · [Deployed round obligations](../lean/Qsag/Protocol/Aggregation/ZkHemV2ComposedZkAndCerts.lean)

**Recursion.** Inductive extraction authenticates the quorums it returns. A fixed depth-two root and both children verify, the parent matrix claims stitch, and modifications to the root, an opening or a child boundary are rejected. The positive four-leaf execution uses different proof data and a different fixture oracle. The executable regression checks the collision flag, root verification and extraction of leaves 0 through 3 on the 1,057-entry recording. Its theorem assumes Boolean success. A kernel derivation of that premise remains open. [Fixed depth-two proof](../lean/Qsag/Protocol/Aggregation/ConcreteIvcDepth2Cert.lean) · [Recursive extractor](../lean/Qsag/Protocol/Aggregation/MultiDepthRecursiveQromExtractor.lean)

**Compiled instructions.** Whole-kernel functional proofs cover 26 of the 28 archive symbols under their stated input preconditions. The original scalar group covers 12. The AVX2 and NEON transpose functions still lack whole-kernel functional proofs. The trace theorems cover 19 x86-64 and nine AArch64 symbols. The x86 composition fixes a public initial state. Applying the trace results to physical timing requires the platform contract. The archive digests are external freshness checks. A linked application also needs evidence for its relocations and code bytes. The GFNI and PCLMUL cross-checks against extracted MIR fix the block count at one. [Per-symbol table](BINARY_RLIB_VERIFICATION.md) · [Functional proofs](../lean/Qsag/Machine/ElfFunctionalEquiv.lean) · [Trace contracts](../lean/Qsag/Machine/PlatformContractInstances.lean)

## Reusable proof infrastructure

| Module | Role |
| --- | --- |
| `Spec/Refines` | Defines machines, successful and rejected transitions, observations and trace refinement. Inspect which internal events the observation map hides. |
| `Exec/RefinesBridges` | Lifts party-machine simulations into the common machine interface. Error-synchronizing refinement can carry a burned epoch across a rejected signing attempt. |
| `Exec/GuardedMachineSim` | Combines a guard, a successful update and a rejected transition. The simulation proves agreement of guards and preservation of the state relation. |
| `Oracle/SpecRatBridges` | Relates the rational representations used by the finite-game and protocol bounds. |
| `QsagVerified/Proofs/MirWpKit` | Gives weakest-precondition rules for the generated Aeneas result monad and checked scalar operations. |
| `Machine/PlatformContractInstances` | Instantiates instruction-trace and timing contracts for the decoded fixtures. Timing on physical hardware requires the platform assumptions. |

## Reproduction

Run the policy, proof coverage, provenance and hygiene gates at the repository root. The policy gate checks that protocol modules are reachable from the top-level imports. Each runtime census checks declaration ownership and axiom dependencies. The paranoid comparators then check the selected exports using six kernels.

```sh
python3 scripts/check_lean_policy.py
python3 aeneas/lean/check_audit_coverage.py
python3 scripts/check_extraction_provenance.py
python3 scripts/gen_extraction_coverage.py --check
python3 scripts/check_repo_hygiene.py
(cd lean && lake build --wfail && lake exe audit-axioms && lake comparator --paranoid)
(cd aeneas/lean && lake build --wfail && lake exe audit-mir-axioms && python3 ../../scripts/run_mir_comparator.py)
(cd aeneas/lean-whir && lake build --wfail && lake exe audit-whir-mir-axioms && COMPARATOR_BWRAP="$PWD/comparator-bwrap.py" lake comparator --paranoid)
```
