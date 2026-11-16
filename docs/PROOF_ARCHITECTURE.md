# QSAG Proof Architecture Guide

This document is an auditor-first guide to the `Qsag` Lean 4.35 library under `lean/Qsag/`. The library separates the **specification trust boundary** (`Qsag/Spec/`), **shared mathematics** (`Qsag/Math/`), **mechanism proofs by domain** (`Qsag/Coding/`, `Qsag/Oracle/`, `Qsag/Protocol/`, `Qsag/Custody/`, `Qsag/Exec/`, `Qsag/Machine/`), **composed subsystem statements** (`Qsag/Top/`), and **executed checks** (`Qsag/Tests/`). Section 2 is the directory map; every count in it was taken from the files on disk with the command printed there.

What a `Top/` theorem establishes is exactly its Lean statement. Several of them are conditional, or are equalities and arithmetic evaluations rather than security reductions; Section 6 says which, in the words of the modules themselves.

---

## 1. Five-Minute Auditor Entry Map

A reviewer reads **`Qsag/Spec/`** to learn *what* is specified and **`Qsag/Top/`** to read the composed statements, then lets the Lean kernel and the axiom audit check *how* each proof is discharged.

1. **Specification trust boundary (`lean/Qsag/Spec/`, 14 modules).**
   - No `import all`, no custom `axiom`, no `sorry`, no `native_decide` / `bv_decide`; the permitted axioms are `propext` and `Quot.sound` (no `Classical.choice`).
   - Defines rational bounds (`Qsag.RatBound` in `Spec/Bounds.lean`, `Qsag.Spec.RatBound` in `Spec/Primitives.lean`), injective and framed codecs (`FixedCodec`, `FramedCodec`), state machines and trace refinement (`Machine`, `Refines` written `M₁ ⊑ M₂`, `LockstepSim`, `DataRefines`, `ObsRefines`), packages and game bounds (`Pkg`, `Within`, `FinGame`, `GameBound`), hardness predicates and platform contracts (`Spec/Assumptions.lean`), and the five ideal machines (`idealSignMachine`, `idealCustodyMachine`, `idealAggregateMachine`, `idealCredMachine`, `idealMigrateMachine`).
2. **Shared mathematics (`lean/Qsag/Math/`).**
   - One definition of each field and ring, with explicit `RingIso` / `FieldIso` isomorphisms between the representations used by different mechanisms (`Math/PolyRing.lean`, `Math/QuarticExt4.lean`, `Math/Gf2Pow128.lean`, `Protocol/Aggregation/FieldTransport.lean`).
3. **Composed statements (`lean/Qsag/Top/`, 9 modules).**
   - `Top.Foundations`, `Top.ProbPkgGames`, `Top.Signing`, `Top.Custody`, `Top.Aggregation`, `Top.Credentials`, `Top.Migration`, `Top.ClosedProtocolReductions` and `Top.SecurityBounds`. The former `Apex` roster module no longer exists: the comparator roster `lean/comparator.json` (challenge module `QsagChallenge`, solution module `Qsag`) names 127 theorems, all of them `Qsag.Top.*` declarations in these nine modules.

```mermaid
flowchart TD
    TopSec["Top.SecurityBounds<br/>(two-clause summary; re-exports platform contracts)"]
    TopClosed["Top.ClosedProtocolReductions"]
    TopDom["Top.Aggregation, Top.Signing, Top.Custody,<br/>Top.Credentials, Top.Migration"]
    TopBase["Top.Foundations, Top.ProbPkgGames"]

    Mech["Exec, Machine<br/>Protocol/{Signing, Aggregation, Threshold, Credentials, Migration}, Custody<br/>Coding, Oracle"]
    Math["Qsag/Math"]
    Spec["Qsag/Spec"]

    TopSec --> TopDom
    TopDom & TopClosed & TopBase --> Mech
    Mech --> Math
    Mech --> Spec
    Math --> Spec
```

---

## 2. Directory Map (`lean/Qsag/`)

Every library module lives in exactly one directory, and the module name follows the path
(`lean/Qsag/Custody/SeparatedCustody.lean` is `Qsag.Custody.SeparatedCustody`). Declaration
namespaces are independent of the path (for example `Qsag.Custody.payload_injective`,
`Qsag.Aggregation.GoldilocksExt4`). No `.lean` file sits directly under `lean/Qsag/`.

Base names are unique except for three pairs, which must be cited with their directory:
`Aggregation.lean` (`Protocol/Aggregation/`, `Top/`), `Algebra.lean` (`Spec/`, `Math/`) and
`PlatformContractInstances.lean` (`Exec/`, `Machine/`).

| Directory | Modules | Lines | Contents |
| :--- | ---: | ---: | :--- |
| `Tactic/` | 3 | 1,540 | `AssuranceKit` (`#verify_constructive`, `#verify_inhabited`, `#tooth`, `#tooth_pair`), `AuditRegistry`, `Prelude`. |
| `Spec/` | 14 | 15,987 | Specification trust boundary (Section 3). |
| `Math/` | 18 | 26,792 | `Algebra`, `PolyRing` (`RingIso` / `FieldIso`), `CoeffPoly`, `Counting`, `Goldilocks`, `GoldilocksBase`, `QuarticExt4`, `Gf2Pow128`, `HasseHensel`, `Primality`, `EllipticCurves`, `Lattices`, `CyclotomicRlwe`, `MlDsaField`, `MlDsaNtt`, `CommitteeMasks`, `ConstructiveAmplitudeRing`, `TapRowParityBias`. |
| `Math/Tactic/` | 2 | 867 | `CommRing`, `MaskBijection`. |
| `Coding/` | 7 | 12,367 | `ReedSolomon`, `Resultant`, `GuruswamiSudan`, `AffineProximity`, `Cwyz26`, `WelchBerlekampDecoder`, `WhirProfiles`. |
| `Oracle/` | 15 | 26,707 | `Keccak`, `Poseidon2`, `Sponge`, `ByteFraming`, `Spn`, `FiatShamir`, `Qrom`, `SpecRatBridges`, `BlockCompressedOracle`, `PrefixMerkleExtraction`, `FrozenChallengeGame`, `ProbPkgBridge`, `ConstructiveQuantumHilbert`, `TwoWayQipmCompression`, `TwoWayQipmSwapAverage`. |
| `Protocol/Signing/` | 11 | 29,399 | `HashSigs`, `HypertreeEufCma`, `Fips205`, `SignatureOutputAndCacheLaws`, `FrontierCompact1122AndCorduroySecurity`, `HybridAddrPolicyAndFullPresetSecurity`, `PorsFpSecurity`, `PreprocessingSeedSeparation`, `ProdCollision`, `ProdHashReductions`, `ExecEufCmaClosedGame`. |
| `Protocol/Aggregation/` | 22 | 63,772 | `Aggregation`, `SuccinctAggregationIop`, `CorduroyAndHemAirCompleteness`, `HemOpening`, `HemRbrSoundness`, `HemMultistageCascadeRbr`, `HemHighCapSlicedBudget`, `HemCommitteeBoundary`, `Cwyz26JohnsonCertificate`, `Cwyz26EqualDegreeAndMultiFold`, `ConcreteSecurityBudget`, `MultiRoundFsQrom`, `QromSaltedMerkleStateRestoration`, `ClosedFsQromCompile`, `ClosedWhirSchedule`, `Poseidon2AlgebraicAndRecursiveHem`, `RecursivePoseidon2WhirSoundness`, `FieldTransport`, `UcGames`, `ComposedQsAgAndMergeSecurity`, `CrossProtocolAndDualOracleComposition`, `ZkHem`. |
| `Protocol/Threshold/` | 19 | 58,091 | `ThresholdMpc`, `Preprocessing`, `LatticePreprocessingFull`, `RlweExtraction`, `DensePcgTaps`, `MaliciousSecurity`, `MacBlind`, `SacrificeFreezeSample`, `Rss256TernaryRound`, `Rss256TwoPassProductProof`, `BaggyAndRss256Security`, `RssSlhFullSecurity`, `IdealTsig`, `ThresholdApproval`, `ThresholdMlDsaSecurity`, `ThresholdMlDsaAndToprf`, `MlDsa44Parameters`, `ProductionCoinReduction`, `ParametricThresholdAndUnlinkableQsa`. |
| `Protocol/Credentials/` | 5 | 11,634 | `AdvancedMpcAndCreds`, `BlindVcQromSecurity`, `BlindVcCollisionFinder`, `RepetitionCutAndChoose`, `ToprfMachine`. |
| `Protocol/Migration/` | 3 | 10,344 | `ActiveMigrationZeroTest`, `HdToprfAndMigrationSecurity`, `PallasAndBlsMigration`. |
| `Custody/` | 7 | 26,555 | `CustodySuiteFull`, `SeparatedCustody`, `JortsBeltLatchAndQuorumSwitching`, `ShamirThresholdCustodyRefinement`, `DistributedThresholdCustodyRefinement`, `MacaroonAttenuation`, `VolatileCoupon`. |
| `Exec/` | 45 | 40,874 | Execution models (Section 5): `SimulationSpine`, `RefinesBridges`, `GuardedMachineSim`, `InteractiveUcEngine` and the `Interactive*` contracts, `ThresholdIdealService`, `ThresholdIdealDurableService`, the `RssParticipant*` and `RssSigning*` machines, `RssProductionProfile`, `PosixCrashWal`, `TwoSlotHwmBase`, `TwoSlotHwmCrashModel`, `CeremonyAtomicityAndAbort`, `SeparatedCustodyResource`, `SeparatedCustodyUc`, `WhirKernels`, `SpecOracle`, and `PlatformContractInstances` (storage). |
| `Exec/Tactic/` | 1 | 638 | `SimulationKit`. |
| `Machine/` | 44 | 56,493 | Compiled code and extracted MIR: `ConstantTimeIsa`, the `X86*`, `Arm64*` and `Isa*` instruction models, `Elf64Headers`, `Elf64Parse`, `ElfParse`, `ElfBytes`, `ArParse`, `ElfVerify`, `ElfFixtures`, `ElfFixtureVerify`, `ElfInvCerts`, `ElfFunctionalEquiv`, `McRefine`, `McSymbols`, `SydTv`, `ClmulSimd`, `Gf128ClmulLoopAgreement`, `FaultAndSpeculativeSafety`, `IsaCosim`, `SpirvSimt`, `SpirvFixtures`, `MirSpecBridgeCore`, `MirSpecBridge`, `MirSpecBridgeWitnesses`, and `PlatformContractInstances` (SIMT and timing). |
| `Machine/Tactic/` | 1 | 29 | `KernelRfl`. |
| `Top/` | 9 | 10,170 | Composed statements (Section 6). |
| `Tests/` | 43 | 17,130 | Executed instances, `#eval` checks and mutation teeth (`*Teeth`, `*Checks`, `*Run`, `*Tests`, `CompositionInstances`, `GuardedMachineSimInstance`, `MathAndCoding`, `OracleAndQrom`, `EquationExports`). |
| **Total** | **269** | **409,389** | |

The counts are the output of this command on the working tree at commit `0644c9e` plus the
uncommitted changes present on 2026-11-16; module counts were stable across the session in which this table was written, while line
counts moved by hundreds of lines within minutes as other work landed. Treat the line figures
as a snapshot and re-run the command:

```bash
python3 - <<'EOF'
import os, collections
d = collections.defaultdict(lambda: [0, 0])
for dp, _, fn in os.walk('lean/Qsag'):
    for f in fn:
        if f.endswith('.lean'):
            k = os.path.relpath(dp, 'lean/Qsag')
            d[k][0] += 1
            d[k][1] += sum(1 for _ in open(os.path.join(dp, f), 'rb'))
for k in sorted(d): print(k, *d[k])
print(sum(v[0] for v in d.values()), sum(v[1] for v in d.values()))
EOF
```

**Layering.** `scripts/check_lean_policy.py` enforces a rank on the directories (`LAYER_RANK`):

```
Tactic(0) < Spec(1) < Math(2) < {Coding, Oracle}(3) < Protocol(4) < Custody(5) < Exec(6) < Machine(7) < Top(8) < Tests(9)
```

A module may import its own directory and any directory of strictly lower rank; `Coding` and
`Oracle` are peers and do not import each other. The same script requires every library module
to be reachable from `Qsag/Top/` and rejects `import all` anywhere inside `lean/Qsag/`
(`rg -l '^(public |private )?import all' lean/Qsag` prints nothing). `Tests/` is a sink: no
module outside `Tests/` imports one. `public meta import Lean` occurs only in the four `Tactic`
directories.

`lean/Qsag.lean` (the umbrella, 269 imports) and `lean/AuditAxioms.lean` (the axiom gate) list
every module on disk. Both rosters are regenerated with `python3 lean/tools/gen_rosters.py`;
`scripts/check_lean_policy.py` and the `AuditAxioms` disk-inventory check reject an unregistered
file. Declaration totals are whatever the `AuditAxioms` gate and the `audit-axioms` executable
report on a fresh build (Section 7); both must report 0 rejected declarations.

---

## 3. Specification Trust Boundary (`lean/Qsag/Spec/`)

Every module in `lean/Qsag/Spec/` is a Lean 4.35 `module` with a `public section`, at most 12 `@[expose]` attributes and no `import all`.

| Module | Lines | What it defines | Representative theorems |
| :--- | ---: | :--- | :--- |
| `Spec/Algebra.lean` | 139 | `CommRingOps`, `LawfulCommRing` and the field classes used by every algebraic module. | (class definitions) |
| `Spec/Bounds.lean` | 350 | `Qsag.RatBound` (`num / den`, `0 < den`), `atLeastBits`, `strictlyMoreThanBits`, `exceedsBitBudget`, `QueryBudget`, `standardPq128Budget`. | `RatBound.le_trans`, `RatBound.add_le_add`, `RatBound.mul_le_mul`, `atLeastBits_add_union_loss`, `atLeastBits_sumList_union_loss`, `atLeastBits_scale_session_loss` |
| `Spec/Encoding.lean` | 509 | `encodeNatLeBytes`, `be` / `ofBE`, `FixedCodec`, `frameBytes` / `unframeBytes`, `concatFramed`, `domainFrame`, `taggedFixed`. | `FixedCodec.encode_injective`, `FixedCodec.prefix_injective`, `frameBytes_injective`, `prefix_free_injective`, `taggedFixed_ne_of_ne` |
| `Spec/Primitives.lean` | 396 | `Qsag.Spec.RatBound` with `atLeastBits`, `strictlyMoreThanBits`, `exceedsBitBudget`; `FramedCodec`; `DomainTag`; the conversions `RatBound.toBudget` / `RatBound.ofBudget` to `Qsag.RatBound`. | `RatBound.ofBudget_toBudget`, `RatBound.toBudget_ofBudget`, `RatBound.ofBudget_le_iff`, `RatBound.ofBudget_atLeastBits_iff`, `FramedCodec.encode_injective`, `DomainTag.disjoint` |
| `Spec/Parameters.lean` | 861 | Deployed parameter profiles: `pq128StatelessProfile`, `corduroyCustody128Profile`, `baggySha3_128fProfile`, `slhDsaShake128fProfile`, `pq128StatefulEpochProfile`, `hemGoldilocksExt4Profile`, `pqCredentialProfile`, `densePcgV3Profile`, `CustodyQuorumProfile`. | `pq128StatelessProfile_wellFormed`, `pq128StatefulEpochProfile_wellFormed`, `hemGoldilocksExt4Profile_basePrime_eq`, `pqCredentialProfile_soundness_params`, `pqCredentialProfile_rust_parity`, `CustodyQuorumProfile.honest_quorum_intersection` |
| `Spec/Refines.lean` | 506 | `Machine S I O`, `Machine.Reachable`, `Machine.AdmitsTrace`, `Refines` (`⊑`), `LockstepSim`, `ObsRefines`, `DataRefines` (interface-abstracting simulation through `projectTrace`), `PartyMachine`, `StepOutcome`, `ExecMode`, `LeakageContract`. | `Refines.refl`, `Refines.trans`, `Refines.preserve_admitsTrace`, `Refines.preserve_trace_safety`, `DataRefines.preserve_admitsTrace`, `DataRefines.reachable_rel` |
| `Spec/GameBound.lean` | 586 | `Iface`, `Code`, `Within` (query-counted code), `Pkg` (`Pkg.link`, `Pkg.par`), `FinGame`, `AdvDist`, `GameBound`. | `adv_refl`, `adv_symm`, `adv_triangle`, `adv_hybrid`, `adv_until_bad`, `event_le_reduction_win`, `event_le_two_reductions`, `event_le_three_reductions` |
| `Spec/Assumptions.lean` | 5,253 | Hardness predicates over explicit games (`SmDtTcrHard`, `SmDtPreHard`, `ItsrHard`, `PrfHard`, `DecisionRlweHard`, with `ModuleSisHard` and `RegularDualLpnHard`); `HashCollision`, `SecondPreimage`; platform contracts `PosixFsyncContract`, `AuthenticatedChannelContract`, `KeyErasureContract`, `DitHardwareContract`, `SimtWorkgroupContract` / `WellFormedSimtContract`. | `FramedCodec.collisionOfDigestEq_sound`, `SmDtTcrHard.mono`, `smDtTcrHard_constHash_refuted`, `prfHard_emptyOutput_refuted`, `moduleSisHard_noRows_refuted`, `hashSig_forger_bound` |
| `Spec/IdealSign.lean` | 1,800 | `SigScheme`, `IdealSignState`, `idealSignMachine`, `latchedSignerMachine`, `idealSignCorruptibleMachine`, `EufCmaForgery`, `SufCmaForgery`. | `idealSignMachine_reachable_inv`, `idealSignMachine_trace_epochs_increasing`, `idealSignMachine_failed_sign_burns_epoch`, `idealSignMachine_eufCmaForgery_iff`, `latchedSigner_trace_safe` |
| `Spec/IdealCustody.lean` | 1,567 | `CustodyIntent`, `CustodyApproval`, `CustodyLedger`, `custodyLedgerSign`, `IdealCustodyState`, `idealCustodyMachine`, `AsymmetricQuorumSystem`. | `idealCustody_reachable_safeInv`, `idealCustody_reachable_spend_accounting`, `idealCustody_reachable_release_honestly_approved`, `idealCustodyStep_wal_retry_and_conflict`, `abqs_belt_latch_unique_msg` |
| `Spec/IdealAggregate.lean` | 1,012 | `AggregateStatement`, `ValidAggregateWitness`, `mergeWitnessMaps`, `ValidBreak`, `TranscriptBreak`, `AggregateSoundnessOutcome`, `StraightLineExtractor`, `AggregateExtractorSound`, `idealAggregateMachine`. | `mergeWitnessMaps_valid`, `AggregateSoundnessOutcome.signer_trichotomy`, `AggregateExtractorSound.failure_bound`, `acceptAll_not_extractorSound`, `tooth_unsound_verifier_breaks_idealAggregate` |
| `Spec/IdealCred.lean` | 2,159 | `CredPort`, `CredCommand`, `IdealCredConfig`, `IdealCredState`, `credExec`, `idealCredMachine`. | `idealCredMachine_issuance_authenticated`, `idealCredMachine_presentation_sound`, `idealCredMachine_presentation_provenance`, `idealCredMachine_rejects_foreign_issue`, `idealCred_trace_corruption_monotone` |
| `Spec/IdealMigrate.lean` | 810 | `EnrolledSnapshot`, `MigrationClaim`, `LegacyOwnershipScheme`, `IdealMigrateState`, `idealMigrateMachine`. | `idealMigrateMachine_reachable_inv`, `idealMigrateMachine_trace_no_double_claim`, `idealMigrateMachine_trace_minted_le_enrolled`, `idealMigrateMachine_trace_nullifier_fresh` |
| `Spec/Sessions.lean` | 39 | `AbortReason`, `SessionOutcome`, `SessionScheduleReq`: wire data shared by the threshold-signing sessions. | (data only) |

The hardness predicates of `Spec/Assumptions.lean` are meaningful only for adversary classes
that exclude exhaustive search; the `*_refuted` theorems in that module show each predicate is
false for a degenerate primitive, so a hypothesis of that shape is not vacuous.

---

## 4. Canonical Models and the Bridges Between Them

The library contains several isomorphic representations of rationals, extension fields and binary fields, each introduced where it was most convenient. Each family is tied together by proved conversions.

### 4.1 Rational bound carriers
- `Qsag.RatBound` (`Spec/Bounds.lean`) $\leftrightarrow$ `Qsag.Spec.RatBound` (`Spec/Primitives.lean`) via `RatBound.toBudget` / `RatBound.ofBudget` (`RatBound.ofBudget_toBudget`, `RatBound.toBudget_ofBudget`, `RatBound.ofBudget_le_iff`, `RatBound.ofBudget_atLeastBits_iff`). The two carriers are isomorphic and both remain in use; `Top/SecurityBounds.lean` and `Top/ClosedProtocolReductions.lean` state their bounds through `Spec.RatBound.ofBudget`.
- `UcGames.ratLe` (`Nat × Nat`, `Protocol/Aggregation/UcGames.lean`) $\leftrightarrow$ `Spec.RatBound` in `Oracle/SpecRatBridges.lean` (`le_iff_ucRatLe`).
- `ExactRat` (`Math/Lattices.lean`) $\to$ `Spec.RatBound` via `clampExactRat` in `Oracle/SpecRatBridges.lean`.

### 4.2 Quartic Goldilocks $\mathbb{F}_{p^4}$
`Math/QuarticExt4.lean` defines `QuarticGoldilocks` ($\mathbb{F}_p[X]/(X^4 - 7)$, $p = 2^{64} - 2^{32} + 1$) with its field laws. `Protocol/Aggregation/FieldTransport.lean` relates it to the other carriers by explicit ring isomorphisms:
- `ringIsoQuarticToSuccinct : RingIso QuarticGoldilocks GoldilocksExt4`
- `ringIsoQuarticToAgg : RingIso QuarticGoldilocks Aggregation.GoldilocksExt4`
- `ringIsoQuarticToCertified`, onto the carrier of the Johnson certificate
- `RingIso.map_evalCoeffs`, `RingIso.map_nodup`, `RingIso.filter_roots_length`: polynomial evaluation, distinctness and root counts transport across an isomorphism, which carries the Reed–Solomon proximity statements from one carrier to another.

`RingIso`, `FieldIso`, `RingIso.symm`, `RingIso.trans` and `RingIso.toFieldIso` are defined once in `Math/PolyRing.lean`.

### 4.3 Binary field $\mathbb{F}_{2^{128}}$
`Math/Gf2Pow128.lean` defines the Wiedemann tower (`TowerElem`, `towerMul`), proves it a field, and relates it to the GHASH/CLMUL polynomial basis $\mathbb{F}_2[z]/(z^{128}+z^7+z^2+z+1)$ by `psiTower128ToPoly` / `polyToTower128` (`psiTower128ToPoly_field_isomorphism`, `ringIsoTower128ToPoly`). `Machine/Gf128ClmulLoopAgreement.lean` carries the same multiplication down to the Rust shift-and-reduce loop and the `PCLMULQDQ` / `VPCLMULQDQ` / `PMULL` reductions (`gf2_128_mul_bv_eq_rustGf128Mul`, `gf128FieldMul_eq_rustGf128Mul`).

### 4.4 Machines
`Spec/Refines.lean` is the single machine and refinement vocabulary. `Exec/RefinesBridges.lean` (Section 5.1) maps the older execution-layer shapes (`PartyMachine`, `ForwardSim`, `InteractiveService`) into it, so that the `Top/` statements about custody, signing and credentials are all `Spec.Refines` or `Spec.DataRefines` statements.

---

## 5. Simulation and Refinement Infrastructure

These modules add no security statement of their own. They are the proof kit the `Top/` refinements are built from.

### 5.1 `Exec/RefinesBridges.lean` (1,156 lines)
Morphisms between `Spec.Refines` and the execution layer:
- §1: `Qsag.PartyMachine` / `Qsag.ForwardSim` to and from `Spec.Machine` / `Spec.Refines`.
- §2: `NetworkRefines`, the horizontal `N`-party rushing-network product refinement.
- §3: bidirectional morphisms with `InteractiveService` (stateful feedback composition, `PrefixEquivalent`).
- §5: **`ErrSyncDataRefines`** and `IndexedSim`. `ErrSyncDataRefines C A visIn visOut` generalizes `Spec.DataRefines`: a rejected concrete step either *stutters* (`errVis c inp = none`, the abstract state stays) or *synchronizes* (`errVis c inp = some j`, the abstract machine also rejects `j` and moves to `A.errStep a j`). This keeps error-burned state, such as an epoch counter consumed by a failed signing attempt, in lockstep on both sides. Proved: `ErrSyncDataRefines.lift_validTrace`, `ErrSyncDataRefines.preserve_admitsTrace`, `ErrSyncDataRefines.reachable_rel`, `ErrSyncDataRefines.preserve_trace_safety`, the embeddings of `DataRefines` and `Refines` into it, the converse `ErrSyncDataRefines.toRefines`, and `ErrSyncDataRefines.postcompose`. `Machine/MirSpecBridgeCore.lean` uses it for the belt-latch signer at the exact 64-epoch jump window.
- §6: `NetworkChannelSim`, the anti-replay authenticated transport combinator.

### 5.2 `Exec/GuardedMachineSim.lean` (648 lines)
The custody and signing guards of `Machine/MirSpecBridgeCore.lean` share one shape: a Boolean guard over `(state, input)`, a state update and output on success, a rejection otherwise. `GuardedMachine` states that shape once.
- `GuardedMachine.Models`: an existing `PartyMachine` computes a given guarded machine (`GuardedMachine.models_ofOutcome`, `GuardedMachine.models_ofOption`), with `trace_induction`, `trace_invariant` and `at_most_one_accept` for a latching guard.
- **`GuardedMachineSim`**: guard agreement, update and rejection preservation and output equality between two guarded machines; `toForwardSim`, `lift_trace`, `trace_safety`, and `GuardedMachine.forwardSimTo` for an abstract machine that is not guarded.
- Combinators, each with its simulation lifting:
  - **`GuardedMachine.zoom`** / `GuardedMachineSim.zoom`: run a guarded machine on a component of a larger state through a lawful `Lens` (`Lens.fst`, `Lens.snd`, `Lens.comp`); `GuardedMachine.zoom_frame_trace` is the frame property.
  - **`GuardedMachine.seq`** / `GuardedMachineSim.seq`: sequential conjunction of two guards on one state (`GuardedMachine.seq_guard_true_iff`, `GuardedMachine.seq_trace_invariant`).
  - **`GuardedMachine.prod`** / `GuardedMachineSim.prod`: product of two guarded machines on a product state (`GuardedMachine.prod_fst_validTrace`, `GuardedMachine.prod_snd_validTrace`).
  - `GuardedMachine.comapIn`: reindexing of the input alphabet.
- `Tests/GuardedMachineSimInstance.lean` composes the four guard instances of `Machine/MirSpecBridgeCore.lean` (`mirVelocityGuard`, `mirBeltLatchKernelGuard`, `mirMlDsaReleaseGuard`, `mirRssCutGuard`) through `zoom`, `comapIn`, `prod` and `seq`.

### 5.3 `Exec/Tactic/SimulationKit.lean` (638 lines)
Proof automation in the `Qsag.Tactic.AssuranceKit` namespace:
- `by compose_forward_sim` / `by compose_refines`: goal-directed search chaining `ForwardSim.refl` / `ForwardSim.trans` / `LockstepSim.toForwardSim` and `Spec.Refines.refl` / `Spec.Refines.trans` / `Spec.LockstepSim.toRefines`.
- `by mir_sim_step`: a bounded structural splitter over `Option` and `Except`.
- `DataRefinement` with `Rel1`, `Rel2` and container relations, connecting `List UInt8`, `Nat`, `BitVec` and `Digest256` specifications to `ByteArray`, `UInt64`, `UInt32` and length-indexed byte slices.
- `LawfulFramedCodec`, `FramedField`, `framePair_inj`, `frameList_inj` and `by frame_prefix_inj` for multi-field byte-framing injectivity.

### 5.4 `aeneas/lean/QsagVerified/Proofs/MirWpKit.lean` (263 lines)
The corresponding kit on the extracted-MIR side, outside `lean/Qsag/`: `Result.wp` (total) and `Result.wlp` (fail-closed) weakest preconditions over the Aeneas `Result` monad; step rules `wp_ok`, `wp_fail_elim`, `wp_let`, `wp_ite`, `wp_mono`, `wlp_of_wp`; checked-arithmetic rules `wp_uscalar_add`, `wp_uscalar_sub`, `wp_uscalar_mul`; the relational combinators `MirRel1` / `MirRel2` (`MirRel1.comp_bind`); the tactics `mir_wp` and `mir_sim_step`; and one worked instance with its tooth (`mirCheckedDeltaCheck_wp_spec`, `tooth_mirCheckedDeltaCheck_exceeds_cap_fails`). See [AENEAS_VERIFICATION.md](AENEAS_VERIFICATION.md).

### 5.5 Platform contract instances
`Spec/Assumptions.lean` states the platform contracts abstractly. Two modules of the same base name instantiate them and are re-exported by `Top/SecurityBounds.lean`; no clause of the summary theorem there consumes a platform contract.

**`Exec/PlatformContractInstances.lean` (860 lines), storage.** Builds the `FsyncStorageModel` induced by the three-tier `PosixFsState` machine of `Exec/PosixCrashWal.lean` and proves `walModel_contract : PosixFsyncContract (walModel ly)`, with `walModel_noRollback`, `walModel_anchorMonotone`, `walModel_anchorWitnessesDurable`, `walModel_commit_appends_to_visible_log` and `walModel_committed_survives`. `walModel_commit_not_exactly_one_record` shows why the contract allows pending records before the committed one: a rename that precedes a directory sync is flushed by the next directory sync.

**`Machine/PlatformContractInstances.lean` (1,241 lines), SIMT and data-independent timing.**
- §1 `simtEpochContract`: the `SimtWorkgroupContract` of one barrier epoch of a SPIR-V kernel under the Wave32 semantics of `Machine/SpirvSimt.lean`, read off the observation trace. Well-formedness is checked for the two barrier epochs of the two-wave reduction kernel (`twoWaveReduction_epochs_wellFormed`, `twoWaveReduction_write_race_free`); the barrier-free concatenation is not well formed and is schedule dependent (`twoWaveNoBarrier_not_wellFormed`, `twoWaveNoBarrier_schedule_dependent`).
- §2 `faial_disjointStorageBindings`: an access protocol satisfying `FaialMapRaceFree` has disjoint storage bindings.
- §3 **`nttStageAddressModel`: an empty-trace boundary.** This is an address-formula model of one fused stage of `goldilocks_ntt.comp` (256 invocations, 8 Wave32 subgroups), *not* a contract derived from the shader. The Machine layer has no instruction stream for that shader, so `blockTrace` is `[]` for every invocation (uniform control flow holds trivially and says nothing about the shader) and the access sets are written by hand from `productionButterflyIndex` and `productionLdsIndex`; the read set is set equal to the write set by assumption. The one fact proved, `nttStageAddressModel_disjointStorageBindings`, is that those formulas assign no LDS cell to two invocations in each of the nine fused stages. That the shader accesses exactly these cells is not proved.
- §4 `armDitContract`, `x86DitContract`: `DitHardwareContract` instances whose observation is the leakage trace of `execArmProg` / `execX86Prog` on a checker-accepted kernel entry (`arm_kernel_sequence_leakage_data_independent`, `x86_kernel_sequence_leakage_data_independent`), with teeth `tooth_arm_umulh_leaks_without_dit_mode` and `tooth_x86_unrestricted_programs_have_no_dit_contract`.
- §5 **28 compiled `.rlib` symbol contracts.** `elfX86DitContract`, `elfArm64DitContract`, `rlibX86CtEntry` and `rlibArm64CtEntry` connect `Spec.DitHardwareContract` to the `qsag-asm` fixtures of `Machine/ElfVerify.lean` and `Machine/ElfFixtureVerify.lean`: the 19 `x86_64` symbols of `currentX86SymbolContracts` and the 9 `aarch64` symbols of `currentAarch64SymbolContracts`. Proved: `currentX86SymbolContracts_all_wf`, `currentAarch64SymbolContracts_all_wf`, `rlibX86CtEntry_binds_rlib_archive`, `rlibArm64CtEntry_binds_rlib_archive`, `rlib_x86_all19_dit_trace_data_independent`, `rlib_aarch64_all9_dit_trace_data_independent`, and the mutation teeth `tooth_rlib_x86_gfni_missing_vzeroupper_rejected` and `tooth_rlib_aarch64_pmull_missing_neon_wipe_rejected`. These are statements about the decoded fixture bytes under the modeled leakage semantics; see [CONSTANT_TIME_ASM.md](CONSTANT_TIME_ASM.md) for what that model does not cover.

---

## 6. Composed Statements (`lean/Qsag/Top/`)

No `Top/` module contains `import all`. Each subsection names the main declarations and states the limits the module's own header states.

### 6.1 `Top/Foundations.lean` (177 lines)
Instantiates results stated for an arbitrary field, answer width or amplitude ring at the deployed parameters.
- `goldilocks_welch_berlekamp_decoder`, `goldilocks_welch_berlekamp_eq_spec_decoder`: over Goldilocks the Welch–Berlekamp decoder is sound for every word, complete inside the unique-decoding radius, equal there to the specification list decoder, and costs at most $2(n+2)^3+5(n+2)^2$ field operations.
- `block256_fourier_database_support`: for 256-bit oracle answers, the Fourier database component with more than `t` nonzero blocks vanishes after `t` queries.
- `block256_prefix_merkle_extraction_bound`: at most $(d+Q_2+Q_1)(3Q_1+1)/2^{256}$ of oracles make an accepted Merkle opening differ from the one extracted from the Phase-1 log. This is a classical query bound.
- `weighted_compression_ideal_permutation_margin`: preimage and collision probabilities at most $2^{-128}$ for $Q \le 2^{56}$ two-way queries against a lazily sampled permutation of the $p^{12}$ states. The bound is about the lazily sampled permutation, not about `poseidon2Perm12`.
- `two_way_transposition_average_o2h`, `cliffordT_measure_reprogram_rbr_step` (amplitudes in $\mathbb{Q}(\sqrt2, i)$), `threshold_three_projection_mac_blind_bound`.

### 6.2 `Top/ProbPkgGames.lean` (240 lines)
The keyed random-oracle hiding game of `Oracle/Qrom.lean` as probabilistic packages (`Oracle/ProbPkgBridge.lean`): `keyedRomReal`, `keyedRomIdeal`, `keyedRom_hiding_advBoundedOn` (advantage at most `Q / cardB`), `keyedRom_hiding_multiSession` and `keyedRom_hiding_multiSession_gameBound` (`K · Q / cardB` over `K` independently keyed sessions), and the same for the hidden production coin share (`productionCoin_hiding_advBoundedOn`, `productionCoin_hiding_multiSession`, single-session bound $Q/2^{256}$).
*Limits:* `baseO` and `secretFn` are fixed functions; distinguishers are classical and deterministic; the factor `K` is from the hybrid argument and is not tight; replacing the oracle by concrete cSHAKE and relating the game to the signing transcript are not part of these statements.

### 6.3 `Top/Aggregation.lean` (1,202 lines)
- **`aggExt4_cwyz26_fold_and_point_reduction`**: the `[CWYZ26]` Johnson-regime sliced fold decomposition (`Cwyz26JohnsonCertificate`, `Coding/Cwyz26.lean`), point-reduction soundness and zero-oracle verifier acceptance on `Aggregation.GoldilocksExt4`.
- **`deployed_hem_stage_budget_and_aggExt4_transport`**: transports the deployed stage tables through the quartic-field isomorphism of `FieldTransport` and evaluates the round-by-round and Don–Fehr–Majenz budget formulas.
- **`qrom_hem_opening_and_invalid_coordinate_chain`**: measured batch Merkle opening extraction and the compressed Fourier-register support invariant (`Oracle/Qrom.lean`, `HemOpening`).
- **`aggregate_merge_and_simt_gpu_noninterference`**: `Spec.mergeWitnessMaps_valid`, merge-tree quorum weight (`ComposedQsAgAndMergeSecurity`) and decoded SPIR-V SIMT noninterference (`Machine/SpirvSimt.lean`).
- **`multifold_salted_qrom_and_committee_boundary_chain`**: multifold stage budgets (`Cwyz26EqualDegreeAndMultiFold`), the salted-Merkle `nv = 24` budget (`QromSaltedMerkleStateRestoration`) and the committee opening-batch boundary with the merged quorum reduction (`HemCommitteeBoundary`, `ComposedQsAgAndMergeSecurity`).
- **`aggregate_extractor_sound_quorum_reduction`, `aggregate_extractor_sound_quorum_bound`**: for an aggregate verifier satisfying `Spec.AggregateExtractorSound` with error `ε`, the probability of an accepted aggregate naming an active validator with neither a transcript collision, nor a verifying extracted signature, nor quorum participation is at most `ε`. Runs whose extractor output is a verifying signature of a non-participating validator are not bounded here: that is single-signature unforgeability.
- **`xmssStepOpAggregate_straightLine_extractorSound`, `xmssStepOpAggregate_dataRefines_ideal`**: instantiates the contract with a `Spec.StraightLineExtractor` on the non-transparent 256-column `StepOp` AIR committee verifier and lifts it to `Spec.DataRefines` against `Spec.idealAggregateMachine`. Succinct WHIR/Canopy compilation factors through `Top/ClosedProtocolReductions.lean`.
- The rest of the module restates component results under `Qsag.Top` names for the comparator roster (field laws, framing injectivity, `whir_bciksJohnsonQrom128_total_error_bound`, the `sbox7` WHIR chain, `tooth_whir_*` rejections).

### 6.4 `Top/Signing.lean` (841 lines)
- **`production_euf_cma_gameBound`**: through `Spec.event_le_three_reductions`, the forger's winning probability is at most the sum of the probabilities of three extractor events on the same run (`ProdCollision`). It does not reduce those events to hardness experiments; `Top/ClosedProtocolReductions.lean` does that for the executable game.
- **`waistbandCache_refines_stateless`, `waistbandCache_preserves_multiturn_traces`**: the upper-hypertree cache (`SignatureOutputAndCacheLaws`) as a `Spec.Refines` witness.
- **`sponge_and_spn_poly_basis_composition`**: encoding separation of the `cSHAKE256` customization tags (`Oracle/Sponge.lean`) with polynomial-basis SPN chain evaluation (`Oracle/Spn.lean`, `Math/Gf2Pow128.lean`). The separation is a statement about absorbed block sequences, not a sponge or ideal-permutation security reduction.
- **`isa_zeroize_and_ret_ct_composition`, `isa_zeroize_ret_and_hardware_ct`**: translation validation of `ct_memzero` (`Machine/SydTv.lean`) with stack-return noninterference (`ConstantTimeIsa`, `ElfFunctionalEquiv`, `FaultAndSpeculativeSafety`).
- **`adaptive_within_and_compact1122_signing_chain`**, **`public_spn_qrom_differential_walsh_and_isa_cosim`**: query-budget, frontier-profile and SPN bound compositions (`ProdHashReductions`, `FrontierCompact1122AndCorduroySecurity`, `ProductionCoinReduction`, `IsaCosim`).
- **`productionSigScheme`, `productionLatchedSigner_refines_idealSign`, `productionLatchedSigner_trace_safe`**: the epoch-latched production signer refines `Spec.idealSignMachine`. Every emitted signature verifies under the derived public key, epochs are strictly increasing in stateful mode, and a failed signing consumes its epoch.
- Roster restatements: `hypertree_euf_cma_advantage_bound`, `production_euf_cma_advantage_bound`, the `threshold_sig_*` matched-input equalities, and the compiled-fixture results `currentX86_rlib_every_symbol_three_way_ni_sound`, `currentAarch64_rlib_every_symbol_three_way_ni_sound` and the `current_*_mc_refines` family.

### 6.5 `Top/Custody.lean` (4,694 lines)
- **`mirPolicy_refines_specPolicy`, `elf_to_idealTsig_refines`, `elf_to_idealTsig_trace_inclusion`**: `Spec.Refines.trans` composition of the `ELF → MIR → Protocol → IdealTsig` hierarchy (`MirSpecBridgeCore`, `MirSpecBridge`); `elf_to_idealCustody_dataRefines` and `elf_to_idealCustody_trace_inclusion` continue it through `fourLayerCustodyMachine`.
- **`rssSharedRelease_refines_reference`, `thresholdServiceShared_refines_ideal`, `thresholdDurableShared_refines_ideal`: equalities, not distributed simulations.** The module proves `rssSharedReleaseMachine_eq_reference`, `thresholdServiceShared_eq_ideal` and `thresholdDurableShared_eq_ideal`: in each pair the two machines are the same function. The `*_refines_*` witnesses are `Spec.Refines.refl` transported along those equalities and carry no more content than the equality. They say nothing about distributed shares, a network, or multiple parties, and `rssSharedRelease_preserves_traces` is the corresponding trivial trace inclusion.
- **`separated_custody_provenance_and_release_chain`**, **`threshold_durable_feedback_and_resource_burn_chain`**: authenticated quorum submission, spend caps, provenance and durable burn (`SeparatedCustody`, `SeparatedCustodyUc`, `SeparatedCustodyResource`, `ThresholdIdealDurableService`).
- **`posix_wal_commit_and_anchor_rollback_fence`, `posix_atomic_commit_and_two_slot_rollback_fence`, `posix_fsync_contract_wal_commit_and_anchor_fence`, `posixWalHost_wal_commit_and_anchor_fence`**: `replaceAtomic` with external monotone anchor coherence (`PosixCrashWal`, `TwoSlotHwmCrashModel`, `Exec/PlatformContractInstances.lean`) and fail-closed whole-device rollback (`CeremonyAtomicityAndAbort`).
- **`seqSessionChannel_contract`, `authenticated_channel_prevents_custody_replay`**: a sequence-numbered session channel satisfies `Spec.AuthenticatedChannelContract`.
- **`rss_participant_network_gate_and_signing_execution_chain`, `gate_batches_and_quorum_switching_disjointness`**: the `RssParticipant*` and `RssSigning*` execution chain and quorum-switching leaf disjointness (`JortsBeltLatchAndQuorumSwitching`).
- **`certCustodyMachine`, `certCustody_unsafe_release_le_forgery`, `macCustody_unsafe_release_le_key_guess`**: a certificate-pool coordinator with adaptive corruption; on traces without a forgery event it is simulated by `Spec.idealCustodyMachine`, and `Pr[unsafe release] ≤ Pr[forgery event]`.
- **`sepCustodyMachine`, `separatedCustody_refines_idealCustody_of`**: the real coordinator `Custody.submitRecorded` with production signing and adaptive corruption, related to `Spec.idealCustodyMachine` on runs satisfying the hypothesis `SeparatedCustodyRunAssumptions`. **`separatedCustody_dataRefines_idealCustody`** is the unconditional statement for `sepCustodyGuardedMachine`, whose step hardcodes the monotone leaf watermark and forgery-freedom (`sepForged = []`) into its guard and emits the output of an abstract `oracleSign` parameter. **`separatedCustody_forgery_wins_eufCma`, `separatedCustody_forgery_eufCma_gameBound`** turn a forgery event into an EUF-CMA win. The ELF, MIR, `IdealTsig`, RSS and WAL machines of the earlier items are not connected to `Spec.idealCustodyMachine` by these theorems.
- **`distributedCustody_refines_idealCustody`, `distributedCustody_trace_inclusion_and_safety`**: distributed `(t, n)` Shamir custody (`DistCustody.distMachine`: custodians, network buffer, adaptive corruption, coordinator ledger) refines `Spec.idealCustodyMachine` for its own `deploymentId`; `shamirCustodian_refines_mediationVault`, `shamir_custody_network_non_equivocation`.
- Roster restatements: BDOZ MAC soundness, the `ucSimulatorTsig_*` bounds, the `rss3_*` TOPRF facts, `uc_production_threshold_forgery_transfer`.

### 6.6 `Top/Credentials.lean` (1,220 lines)
- **`pcg_dual_lpn_bias_in_spec_ratBound`**, **`rlwe_preprocessing_and_sis_boundary_chain`**, **`threshold_mldsa_hvzk_sacrifice_and_prss_chain`**, **`threshold_mldsa_frozen_sacrifice_sign_step_soundness`**: lattice, dual-LPN and threshold ML-DSA bounds (`Math/Lattices.lean`, `DensePcgTaps`, `LatticePreprocessingFull`, `RlweExtraction`, `ThresholdMlDsaSecurity`, `ThresholdMlDsaAndToprf`, `SacrificeFreezeSample`).
- **`blindVc_cut_and_choose_gameBound`, `blindVc_concrete_fp5_qrom_opening_soundness`**: the `PiBlindVc` cut-and-choose count over the concrete quintic field and the QROM opening-round bound (`RepetitionCutAndChoose`, `BlindVcCollisionFinder`).
- **`CredentialImplementation`, `toprfCredentialImplementation`, `piToprfCredMachine_dataRefines_ideal`**: the refinement obligation against `Spec.idealCredMachine`, inhabited by `piToprfCredService` (`Protocol/Credentials/ToprfMachine.lean`) with the state abstraction `Rel c a := c.abs = a`. `toprfCredentialImplementation_non_identity_state` shows the abstraction is not the identity, and `piToprfCredService_reservoir_never_resets` that the SPDZ reservoir is monotone across accepted and rejected steps. The service is a Lean protocol machine; it is not extracted from, or proved equal to, the Rust `voprf_spdz.rs` implementation.
- **`unauthenticatedCredService_not_implementation`**: an unauthenticated service does not inhabit the obligation.
- **`credPort_authenticated_by_channel_contract`**, with `tooth_open_relay_spoofs_issuer_credPort`: ties `Spec.CredPort` caller labels to `Spec.AuthenticatedChannelContract`.

### 6.7 `Top/Migration.lean` (1,320 lines)
- **`legacy_curve_primality_extraction_and_ideal_migration_chain`**: Pocklington–Pratt certificates for the `secp256k1` primes (`Math/Primality.lean`, `Math/EllipticCurves.lean`), ZKBoo and `RedPallas` extraction (`PallasAndBlsMigration`) and `Spec.idealMigrateMachine`.
- **`active_migration_ceremony_qrom_and_gf2pow128_chain`**: the 438-repetition ceremony bound for the `D0_BITS = 16` packing, QROM scaling arithmetic and $\mathbb{F}_{2^{128}}$ multiplication equivalence (`ActiveMigrationZeroTest`, `HdToprfAndMigrationSecurity`, `Math/Gf2Pow128.lean`).
- **`migration_bit_check_staged_count_numerator_63`**: at the `outer_mpc.rs` stage list an adaptive prover from a false claim is accepted on at most $63/(2^{128}-1)$ of the coin space. As stated in `Top/`, the soundness of the stages ahead of the halving rounds is the hypothesis `StagesSound`; `Protocol/Migration/ActiveMigrationZeroTest.lean` discharges it for the Rust stage list (`rustBitCheckStages_sound`, `rust_bit_check_63_concrete_accepting_coins_bound`).
- **`dlogOwnershipScheme`, `dlogOwnership_accepted_claim_has_unique_scalar`, `tooth_dlogOwnership_rejects_destination_swap`**: a destination-bound discrete-log instance of `Spec.LegacyOwnershipScheme`.
- **`rawSettlementMachine`, `rawSettlement_dataRefines_idealMigrate`, `rawSettlement_trace_simulated`, `dlogSettlement_dataRefines_idealMigrate`**: the settlement registry over raw submissions refines `Spec.idealMigrateMachine` through `SettlementWire.decode`, given `SettlementCircuitSound`; `dlogSettlement_circuitSound` supplies it for the discrete-log scheme.

### 6.8 `Top/ClosedProtocolReductions.lean` (334 lines)
Statements in `Spec.GameBound` form, each one implication from an execution of the verifier to explicit reduction events.
- **`whir_exec_closed_qrom_soundness`**: for a statement outside the language and any `Q`-query Fiat–Shamir adversary, `Pr[execWhirVerify accepts] ≤ scheduleQromError sched Q + Pr[the collision finder outputs a Merkle-hash collision]`, given a `ClosedWhir.WhirScheduleCert` for the schedule. `whirCollisionReduction_validBreak` shows the finder's output is a collision of the byte hash; that both inputs are recorded prover queries (`Spec.TranscriptBreak`) is not stated.
- **`singleStageExactWhir_closed_qrom_soundness`, `singleStageExactWhir_nonvacuity`**: discharges the certificate unconditionally for a non-empty one-stage schedule whose verifier accepts honest proofs and rejects false statements.
- **`deployed_whir_exec_closed_qrom_128`: conditional.** For the four-stage `nv = 24` `deployedSched` at $Q \le 2^{40}$ the theorem takes `ClosedWhir.WhirScheduleCert env deployedSched w` as an open hypothesis; no such certificate is constructed. In addition `deployedStages` uses the profile input `whirAffineStageSimpleNum`, which is not yet bridged from the proved sliced MCA counts.
- **`jorts_baggy_closed_euf_cma_keyed_target_bound`**: `Pr[ExecEufCmaGame wins] ≤ εI + prodPathTargetCount · εT + prodPreCandidateCount · εP`, where the three `ε` bound games played by explicit adversaries that receive the public key and the hash and signing oracles only; `jorts_baggy_closed_euf_cma_same_trace_classification` partitions the winning coins. `jorts_baggy_closed_euf_cma_prf_keygen_hop` and `jorts_baggy_closed_euf_cma_spec_assumptions_bound` connect the game to `Spec.PrfHard`, `Spec.ItsrHard`, `Spec.SmDtTcrHard` and `Spec.SmDtPreHard`; `concrete_exec_euf_cma_spec_assumptions_witness` inhabits those hypotheses at a concrete point with bound `6 / 256 < 1`, which shows they are satisfiable and nothing about deployed parameters.

### 6.9 `Top/SecurityBounds.lean` (142 lines)
**`qsag_unified_concrete_security_summary`** has two clauses, and the module header states exactly what they are:
- **Clause I, facts with no cryptographic hypothesis:** (1) the production tap-row parity bias lies strictly between $2^{-118}$ and $2^{-117}$ (`Math/TapRowParityBias.lean`); (2) the arithmetic inequality $8(q+1)^2 \cdot 2^{438} \cdot 2^{128} \le 3^{438}$ for $q+1 \le 2^{56}$; (3) trace inclusion of `rssSharedReleaseMachine` in `rssReferenceReleaseMachine` and `PrefixEquivalent` of the shared and ideal durable threshold services, which by Section 6.5 are consequences of machine equalities.
- **Clause II, arithmetic on bound formulas:** the 12-entry portfolio roster and the RLWE OR-sigma and HEM `nv = 24` QROM compiler bound *formulas* evaluate to at most $2^{-128}$ within the stated query ceilings. These are evaluations of closed-form expressions. The theorem takes no hardness or oracle-model hypothesis and does not show that any protocol's adversarial advantage is bounded by them.

The EUF-CMA event bound, the `[CWYZ26]` stage budget and the waistband-cache refinement are separate theorems and are not conjuncts of the summary. **`securityBounds_sharp_query_ceiling_sensitivity`** gives `exceedsBitBudget 128` witnesses just past the ceilings.

---

## 7. Independent Verification Commands

Run the Lean 4.35 build and the axiom audit from the `lean/` directory with warnings as errors
(`--wfail`). A cold build of the whole library takes well over ten minutes and several tens of
gigabytes of memory, so run it on a Linux host with a memory limit in place and one build per
tree at a time; Lake resumes from the modules already built if a build is interrupted.

```bash
# 1. Build every library module, the axiom gate, and the audit binary with zero warnings:
lake build --wfail Qsag AuditAxioms audit-axioms

# 2. Re-run the dependency census from the compiled .olean files: every declaration of every
#    Qsag module must depend only on {propext, Quot.sound}:
.lake/build/bin/audit-axioms

# 3. Source policy (from the repository root): forbidden tokens (sorry, axiom, native_decide,
#    bv_decide, Classical.choice, ...), LAW-M1 (<= 12 @[expose] per file), LAW-M2, docstring
#    citations, roster completeness of Qsag.lean and AuditAxioms.lean, the directory layering,
#    reachability from Top, and absence of `import all` in lean/Qsag:
python3 scripts/check_lean_policy.py
```
