module
public import Qsag.Protocol.Migration.ClosedIdealMigrateConnection
public import Qsag.Protocol.Aggregation.PublicHemQuintic128
public import Qsag.Protocol.Aggregation.ZkHemV2ComposedZkAndCerts
public import Qsag.Protocol.Aggregation.ZkHemV2PackedFiberCerts
public import Qsag.Protocol.Aggregation.SuccinctWhirExtractorAndIdealAggregate
public import Qsag.Protocol.Aggregation.MultiDepthRecursiveQromExtractor
public import Qsag.Protocol.Aggregation.RecursiveIvcPublicRowQrom
public import Qsag.Protocol.Aggregation.ConcreteIvcDepth2Cert
public import Qsag.Machine.SpirvPoseidon2UniversalEntry
public import Qsag.Protocol.Aggregation.HemMultistageCascadeRbr
public import Qsag.Protocol.Aggregation.RecursivePoseidon2WhirSoundness
public import Qsag.Protocol.Aggregation.HemInterpolation
public import Qsag.Protocol.Aggregation.ZkHemV2
/-
# Qsag.Top.Aggregation — End-to-End Composed Succinct Aggregation Soundness and Extraction

Top-level composition module (zero `import all`) connecting the coding-theoretic proximity-gap
proofs (`Coding/Cwyz26JohnsonCertificate`, `Coding/Cwyz26DeployedStages`), the
round-by-round `HEM`/`WHIR` verifier and point-reduction bridges (`HemVerifierAcceptance`,
`HemPointReductionSoundness`, `HemFoldDecompositionBridge`, `HemSlicedFoldBudget`), the classical
and coherent Fourier QROM Merkle-opening extractors (`QromBatchMerkleExtraction`,
`HemExtractedOpeningBridge`, `QromCoherentMerkleBridge`, `QromFourierSupport`), the hierarchical
shard merge-tree and quorum reduction (`ComposedQsAgAndMergeSecurity`, `Spec/IdealAggregate`),
and SIMT GPU constant-time kernel
execution (`SpirvSimt`).

Section 6 connects the ideal knowledge-soundness contract `Spec.AggregateExtractorSound` to the
quorum layer of `ComposedQsAgAndMergeSecurity`. For an aggregate verifier over native signatures
that satisfies the contract with error `ε` and an extractor of a class `ℰ`, against every oracle
prover the probability of an accepted aggregate over the custody roster that names an active
validator for which there is neither a collision of the oracle among the prover's queries
(`Spec.TranscriptBreak`), nor a verifying signature in the extractor's output for that validator,
nor quorum participation, is at most `ε`. Runs whose extractor output is a verifying signature
of a non-participating validator are not bounded here: that is single-signature unforgeability.
Section 6b constructs a concrete,
non-vacuous `Spec.AggregateExtractorSound` instance (`stepOp256Aggregate_extractorSound`) over
`Spec.StraightLineExtractor` and a `Spec.DataRefines` simulation (`stepOp256Aggregate_dataRefines_ideal`,
`stepOp256Aggregate_preserve_admitsTrace`)
against `Spec.idealAggregateMachine` for the deterministic 256-column `StepOp` AIR committee
execution table (`verifyStepOp256Aggregate`, extracting native signatures from trace columns via
`stepOp256TableOk_xmss_extract`). Succinct Merkle-root-and-opening Fiat–Shamir WHIR compilation
factors through `Qsag.Top.ClosedProtocolReductions`.
-/

public import Qsag.Spec.Primitives
public import Qsag.Spec.Parameters
public import Qsag.Spec.Assumptions
public import Qsag.Spec.IdealAggregate
public import Qsag.Math.Poseidon2Gl24
public import Qsag.Machine.PlatformContractInstances
public import Qsag.Math.QuinticExt5
public import Qsag.Protocol.Aggregation.Cwyz26JohnsonCertificate
public import Qsag.Coding.Cwyz26
public import Qsag.Protocol.Aggregation.Cwyz26EqualDegreeAndMultiFold
public import Qsag.Protocol.Aggregation.CorduroyAndHemAirCompleteness
public import Qsag.Protocol.Aggregation.Poseidon2AlgebraicAndRecursiveHem
public import Qsag.Protocol.Aggregation.CrossProtocolAndDualOracleComposition
public import Qsag.Protocol.Aggregation.HemOpening
public import Qsag.Protocol.Aggregation.HemRbrSoundness
public import Qsag.Oracle.Qrom
public import Qsag.Protocol.Aggregation.QromSaltedMerkleStateRestoration
public import Qsag.Protocol.Aggregation.ComposedQsAgAndMergeSecurity
public import Qsag.Machine.SpirvPoseidon2Audit
public import Qsag.Machine.SpirvSimt
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Top

set_option autoImplicit false

/-! ## 6. `Spec.AggregateExtractorSound` for the Native Verifier and the Quorum Layer -/

/-- **Accepted aggregate, per validator (one run).** For an aggregate verifier `verifyAgg`
    over individual signatures checked by `verifyAggNativeSig geom`, an oracle `H` and a prover
    with query budget `q`: on a run whose statement lists the enrolled custody keys, where
    `verifyAgg` accepts and the prover does not win the knowledge-soundness game
    (`Spec.aggregateFailure … = false`), every active validator `v` satisfies one of:
    1. two different recorded queries of the prover collide under `H` (`Spec.TranscriptBreak`),
    2. the extractor's output for `v` on this run is a native signature that verifies under
       `v`'s key on the statement's message although the quorum of `v` did not participate,
    3. the quorum of `v` participated. -/
theorem aggregate_extractor_sound_quorum_reduction
    {Proof : Type} {nVal : Nat}
    (geom : Qsag.AggSigGeometry) (custody : Fin nVal → Qsag.Composed.Custody)
    (verifyAgg : (Qsag.Spec.Bytes → Qsag.Spec.Bytes) →
      Qsag.Spec.AggregateStatement Qsag.AggValidatorPk nVal → Proof → Bool)
    (extract : List (Qsag.Spec.Bytes × Qsag.Spec.Bytes) →
      Qsag.Spec.AggregateStatement Qsag.AggValidatorPk nVal → Proof →
      Fin nVal → Option Qsag.AggNativeSignature)
    (H : Qsag.Spec.Bytes → Qsag.Spec.Bytes) (q : Nat)
    (prover : Qsag.Spec.Code Qsag.Spec.byteOracleIface
      (Qsag.Spec.AggregateStatement Qsag.AggValidatorPk nVal × Proof))
    (hRoster : ∀ v : Fin nVal,
      (Qsag.Spec.aggregateRun H q prover).1.1.roster v = (custody v).state.pk)
    (hAcc : verifyAgg H (Qsag.Spec.aggregateRun H q prover).1.1
      (Qsag.Spec.aggregateRun H q prover).1.2 = true)
    (hLose : Qsag.Spec.aggregateFailure (Qsag.verifyAggNativeSig geom) verifyAgg extract H
      (Qsag.Spec.aggregateRun H q prover) = false)
    (v : Fin nVal)
    (hActive : (Qsag.Spec.aggregateRun H q prover).1.1.bitmap.getLsbD v.val = true) :
    (∃ b : Qsag.Spec.AggregateBreak,
      Qsag.Spec.TranscriptBreak H (Qsag.Spec.aggregateRun H q prover).2 b) ∨
    (∃ sig : Qsag.AggNativeSignature,
      extract (Qsag.Spec.aggregateRun H q prover).2 (Qsag.Spec.aggregateRun H q prover).1.1
        (Qsag.Spec.aggregateRun H q prover).1.2 v = some sig ∧
      Qsag.verifyAggNativeSig geom (custody v).state.pk
        (Qsag.Spec.aggregateRun H q prover).1.1.message sig = true ∧
      Qsag.Composed.quorumParticipated (custody v)
        (Qsag.Spec.aggregateRun H q prover).1.1.message = false) ∨
    Qsag.Composed.quorumParticipated (custody v)
      (Qsag.Spec.aggregateRun H q prover).1.1.message = true := by
  have h := (Qsag.Spec.aggregateFailure_false_outcome (Qsag.verifyAggNativeSig geom) verifyAgg
    extract H q prover hLose hAcc).signer_trichotomy
    (fun u => Qsag.Composed.quorumParticipated (custody u)
      (Qsag.Spec.aggregateRun H q prover).1.1.message) v hActive
  rcases h with hB | ⟨sig, hEx, hSig, hNo⟩ | hYes
  · exact .inl hB
  · refine .inr (.inl ⟨sig, hEx, ?_, hNo⟩)
    rw [← hRoster v]
    exact hSig
  · exact .inr (.inr hYes)

/-- **Quorum soundness bound.** Let `verifyAgg` with extractor `extract` of the class `ℰ`
    satisfy `Spec.AggregateExtractorSound` for the oracle family `oracle`, query budget `q` and
    error `ε`. For every prover on the adversary coordinate of a coin split, any event
    contained in

    * the statement lists the enrolled custody keys and `verifyAgg` accepts, and
    * some active validator `v` has no transcript collision, its quorum did not participate,
      and the extractor's output for `v` on the run is not a signature verifying under its key

    has probability at most `ε`. The event concerns the signature the extractor produced from
    the run, so it is not emptied by the existence of verifying signatures.

    This is not unforgeability of the aggregate: a run whose extractor output is a verifying
    signature of a non-participating validator is outside the event, and bounding such runs is
    single-signature unforgeability, which is not used here. The statement has content for a
    class `ℰ` such as `Spec.StraightLineExtractor`; with the unrestricted class the contract
    can hold for a verifier that checks nothing
    (`Spec.acceptAll_alwaysValid_unrestricted_extractorSound`).

    Open obligation: the contract `C` for the deployed verifier, i.e. an extractor of the class
    reading only the prover's oracle transcript, the statement and the proof, and the bound
    `ε`. -/
theorem aggregate_extractor_sound_quorum_bound
    {Proof : Type} {nVal nC n nA : Nat}
    (geom : Qsag.AggSigGeometry) (custody : Fin nVal → Qsag.Composed.Custody)
    (verifyAgg : (Qsag.Spec.Bytes → Qsag.Spec.Bytes) →
      Qsag.Spec.AggregateStatement Qsag.AggValidatorPk nVal → Proof → Bool)
    (extract : List (Qsag.Spec.Bytes × Qsag.Spec.Bytes) →
      Qsag.Spec.AggregateStatement Qsag.AggValidatorPk nVal → Proof →
      Fin nVal → Option Qsag.AggNativeSignature)
    (oracle : Fin nC → Qsag.Spec.Bytes → Qsag.Spec.Bytes) (q : Nat) (ε : Qsag.Spec.RatBound)
    {ℰ : (List (Qsag.Spec.Bytes × Qsag.Spec.Bytes) →
      Qsag.Spec.AggregateStatement Qsag.AggValidatorPk nVal → Proof →
      Fin nVal → Option Qsag.AggNativeSignature) → Prop}
    (C : Qsag.Spec.AggregateExtractorSound ℰ (Qsag.verifyAggNativeSig geom) verifyAgg extract
      oracle q ε)
    (hPos : 0 < n) (π : Qsag.Spec.CoinSplit n nC nA)
    (prover : Fin nA → Qsag.Spec.Code Qsag.Spec.byteOracleIface
      (Qsag.Spec.AggregateStatement Qsag.AggValidatorPk nVal × Proof))
    (fail : Fin n → Bool)
    (hFail : ∀ ω : Fin n, fail ω = true →
      (∀ v : Fin nVal,
        (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).1.1.roster v =
          (custody v).state.pk) ∧
      verifyAgg (oracle (π.chal ω))
        (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).1.1
        (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).1.2 = true ∧
      ∃ v : Fin nVal,
        (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q
          (prover (π.advc ω))).1.1.bitmap.getLsbD v.val = true ∧
        ¬ ((∃ b : Qsag.Spec.AggregateBreak,
            Qsag.Spec.TranscriptBreak (oracle (π.chal ω))
              (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).2 b) ∨
          (∃ sig : Qsag.AggNativeSignature,
            extract (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).2
              (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).1.1
              (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).1.2 v =
                some sig ∧
            Qsag.verifyAggNativeSig geom (custody v).state.pk
              (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q
                (prover (π.advc ω))).1.1.message sig = true ∧
            Qsag.Composed.quorumParticipated (custody v)
              (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q
                (prover (π.advc ω))).1.1.message = false) ∨
          Qsag.Composed.quorumParticipated (custody v)
            (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q
              (prover (π.advc ω))).1.1.message = true)) :
    Qsag.Spec.GameBound (Qsag.Spec.FinGame.mk hPos fail).winProb ε :=
  C.failure_bound hPos π prover fail (fun ω hF => by
    obtain ⟨hRoster, hAcc, v, hActive, hNone⟩ := hFail ω hF
    refine ⟨hAcc, fun hOut => hNone ?_⟩
    rcases hOut.signer_trichotomy
      (fun u => Qsag.Composed.quorumParticipated (custody u)
        (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).1.1.message)
      v hActive with hB | ⟨sig, hEx, hSig, hNo⟩ | hYes
    · exact .inl hB
    · refine .inr (.inl ⟨sig, hEx, ?_, hNo⟩)
      rw [← hRoster v]
      exact hSig
    · exact .inr (.inr hYes))

/-- **Extraction bound for an injective oracle.** If every oracle of the family is injective,
    no transcript collision exists, and the contract bounds the probability that the verifier
    accepts while the extracted witness map is not a valid individual signature for every
    active validator. -/
theorem aggregate_extractor_sound_valid_witness_of_injective
    {Proof : Type} {nVal nC n nA : Nat}
    (geom : Qsag.AggSigGeometry)
    (verifyAgg : (Qsag.Spec.Bytes → Qsag.Spec.Bytes) →
      Qsag.Spec.AggregateStatement Qsag.AggValidatorPk nVal → Proof → Bool)
    (extract : List (Qsag.Spec.Bytes × Qsag.Spec.Bytes) →
      Qsag.Spec.AggregateStatement Qsag.AggValidatorPk nVal → Proof →
      Fin nVal → Option Qsag.AggNativeSignature)
    (oracle : Fin nC → Qsag.Spec.Bytes → Qsag.Spec.Bytes) (q : Nat) (ε : Qsag.Spec.RatBound)
    {ℰ : (List (Qsag.Spec.Bytes × Qsag.Spec.Bytes) →
      Qsag.Spec.AggregateStatement Qsag.AggValidatorPk nVal → Proof →
      Fin nVal → Option Qsag.AggNativeSignature) → Prop}
    (C : Qsag.Spec.AggregateExtractorSound ℰ (Qsag.verifyAggNativeSig geom) verifyAgg extract
      oracle q ε)
    (hInj : ∀ (c : Fin nC) (a b : Qsag.Spec.Bytes), oracle c a = oracle c b → a = b)
    (hPos : 0 < n) (π : Qsag.Spec.CoinSplit n nC nA)
    (prover : Fin nA → Qsag.Spec.Code Qsag.Spec.byteOracleIface
      (Qsag.Spec.AggregateStatement Qsag.AggValidatorPk nVal × Proof))
    (fail : Fin n → Bool)
    (hFail : ∀ ω : Fin n, fail ω = true →
      verifyAgg (oracle (π.chal ω))
        (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).1.1
        (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).1.2 = true ∧
      ¬ Qsag.Spec.ValidAggregateWitness (Qsag.verifyAggNativeSig geom)
        (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).1.1
        (extract (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).2
          (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).1.1
          (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).1.2)) :
    Qsag.Spec.GameBound (Qsag.Spec.FinGame.mk hPos fail).winProb ε :=
  C.failure_bound hPos π prover fail (fun ω hF =>
    ⟨(hFail ω hF).1, fun hOut =>
      (hFail ω hF).2 (hOut.witness_of_injective (hInj (π.chal ω)))⟩)

#verify_constructive Qsag.Top.aggregate_extractor_sound_quorum_reduction
  Qsag.Top.aggregate_extractor_sound_quorum_bound
  Qsag.Top.aggregate_extractor_sound_valid_witness_of_injective

/-! ## 6b. Concrete `Spec.AggregateExtractorSound` & `Spec.DataRefines` for the 256-Column `StepOp` AIR Committee Verifier -/

/-- Non-transparent 256-column `StepOp` execution trace proof for a validator committee: the
    proof carries trace rows (`StepOpRow`), not native signature records, and signatures are
    reconstructed from auxiliary trace registers via `stepXmssSig`. -/
abbrev StepOp256AggregateProof := List Qsag.StepOpRow

/-- Public slot vector derived from an `AggregateStatement` for `stepOp256TableOk`. -/
def stepOp256CommitteeSlots {nVal : Nat}
    (stmt : Qsag.Spec.AggregateStatement Qsag.AggValidatorPk nVal) : List Qsag.StepOpSlot :=
  (List.finRange nVal).map fun i =>
    if stmt.bitmap.getLsbD i.val then
      some (stmt.roster i, Qsag.computeMessageMu (stmt.roster i) stmt.message)
    else
      none

/-- Deterministic 256-column `StepOp` AIR committee aggregate verifier over `.xmssPoseidon2`. -/
def verifyStepOp256Aggregate {nVal : Nat} (_H : Qsag.Spec.Bytes → Qsag.Spec.Bytes)
    (stmt : Qsag.Spec.AggregateStatement Qsag.AggValidatorPk nVal)
    (rows : StepOp256AggregateProof) : Bool :=
  decide (0 < nVal) &&
  (List.finRange nVal).all (fun i =>
    !stmt.bitmap.getLsbD i.val || ((stmt.roster i).profile == .xmssPoseidon2)) &&
  Qsag.stepOp256TableOk .xmssPoseidon2 (stepOp256CommitteeSlots stmt) rows

/-- Proof-carried candidate list reconstructed slot-by-slot from the `StepOp` execution table. -/
def stepOp256ProofSigs (nVal : Nat) (rows : StepOp256AggregateProof) :
    List Qsag.AggNativeSignature :=
  (List.finRange nVal).map fun i =>
    Qsag.stepXmssSig (Qsag.stepOpSlotRow .xmssPoseidon2 rows i.val)

/-- Straight-line extractor reading slot `i` of the `StepOp` execution table. -/
def extractStepOp256Aggregate {nVal : Nat}
    (_log : List (Qsag.Spec.Bytes × Qsag.Spec.Bytes))
    (_stmt : Qsag.Spec.AggregateStatement Qsag.AggValidatorPk nVal)
    (rows : StepOp256AggregateProof) (i : Fin nVal) : Option Qsag.AggNativeSignature :=
  some (Qsag.stepXmssSig (Qsag.stepOpSlotRow .xmssPoseidon2 rows i.val))

theorem extractStepOp256Aggregate_straightLine {nVal : Nat} :
    Qsag.Spec.StraightLineExtractor (PK := Qsag.AggValidatorPk)
      (fun _ => none) (stepOp256ProofSigs nVal) (extractStepOp256Aggregate (nVal := nVal)) :=
  Qsag.Spec.StraightLineExtractor.of_proofSigs _ _ _ (fun _ _ rows i sig hs => by
    have hEq : Qsag.stepXmssSig (Qsag.stepOpSlotRow .xmssPoseidon2 rows i.val) = sig :=
      Option.some.inj hs
    exact List.mem_map.mpr ⟨i, List.mem_finRange i, hEq⟩)

private theorem finRange_getElem? (n k : Nat) (hk : k < n) :
    (List.finRange n)[k]? = some ⟨k, hk⟩ := by
  have hLen : (List.finRange n).length = n := List.length_finRange
  have hk' : k < (List.finRange n).length := by rw [hLen]; exact hk
  rw [List.getElem?_eq_getElem hk', List.getElem_finRange]
  rfl

private theorem stepOp256CommitteeSlots_getElem? {nVal : Nat}
    (stmt : Qsag.Spec.AggregateStatement Qsag.AggValidatorPk nVal)
    (k : Nat) (hk : k < nVal) :
    (stepOp256CommitteeSlots stmt)[k]? =
      some (if stmt.bitmap.getLsbD k then
        some (stmt.roster ⟨k, hk⟩, Qsag.computeMessageMu (stmt.roster ⟨k, hk⟩) stmt.message)
      else none) := by
  unfold stepOp256CommitteeSlots
  rw [List.getElem?_map, finRange_getElem? nVal k hk]
  rfl

/-- Every active validator in an accepted `verifyStepOp256Aggregate` table yields a valid
    native XMSS-Poseidon2 signature via `extractStepOp256Aggregate`. -/
theorem verifyStepOp256Aggregate_validWitness {nVal : Nat}
    (H : Qsag.Spec.Bytes → Qsag.Spec.Bytes)
    (log : List (Qsag.Spec.Bytes × Qsag.Spec.Bytes))
    (stmt : Qsag.Spec.AggregateStatement Qsag.AggValidatorPk nVal)
    (rows : StepOp256AggregateProof)
    (hAcc : verifyStepOp256Aggregate H stmt rows = true) :
    Qsag.Spec.ValidAggregateWitness (Qsag.verifyAggNativeSig Qsag.xmssPoseidon2Geom)
      stmt (extractStepOp256Aggregate log stmt rows) := by
  unfold verifyStepOp256Aggregate at hAcc
  rw [Bool.and_eq_true, Bool.and_eq_true] at hAcc
  obtain ⟨⟨_, hProfAll⟩, hTable⟩ := hAcc
  refine Qsag.Spec.ValidAggregateWitness.intro (fun i hAct => ?_)
  refine ⟨Qsag.stepXmssSig (Qsag.stepOpSlotRow .xmssPoseidon2 rows i.val), rfl, ?_⟩
  have hProfMem := List.all_eq_true.mp hProfAll i (List.mem_finRange i)
  rw [hAct] at hProfMem
  simp only [Bool.not_true, Bool.false_or, beq_iff_eq] at hProfMem
  have hSlot : (stepOp256CommitteeSlots stmt)[i.val]? =
      some (some (stmt.roster i, Qsag.computeMessageMu (stmt.roster i) stmt.message)) := by
    rw [stepOp256CommitteeSlots_getElem? stmt i.val i.isLt]
    have hFinEq : (⟨i.val, i.isLt⟩ : Fin nVal) = i := Fin.ext rfl
    rw [hFinEq, hAct]
    simp only [↓reduceIte]
  exact Qsag.stepOp256TableOk_xmss_extract (stepOp256CommitteeSlots stmt) rows i.val
    (stmt.roster i, Qsag.computeMessageMu (stmt.roster i) stmt.message) stmt.message
    hTable hSlot hProfMem rfl

/-- **Concrete `Spec.AggregateExtractorSound` Instance (`stepOp256Aggregate_extractorSound`)**:
    Certifies the 256-column `StepOp` AIR committee aggregate verifier (`verifyStepOp256Aggregate`)
    with `extractStepOp256Aggregate` in `Spec.StraightLineExtractor` at zero extraction failure
    error (`Spec.RatBound.zero`). -/
theorem stepOp256Aggregate_extractorSound {nVal nC : Nat}
    (oracle : Fin nC → Qsag.Spec.Bytes → Qsag.Spec.Bytes) (q : Nat) :
    Qsag.Spec.AggregateExtractorSound
      (Qsag.Spec.StraightLineExtractor (fun _ => none) (stepOp256ProofSigs nVal))
      (Qsag.verifyAggNativeSig Qsag.xmssPoseidon2Geom)
      (verifyStepOp256Aggregate (nVal := nVal))
      (extractStepOp256Aggregate (nVal := nVal))
      oracle q Qsag.Spec.RatBound.zero :=
  Qsag.Spec.AggregateExtractorSound.of_deterministic _ _ _ _
    extractStepOp256Aggregate_straightLine oracle q
    (fun H log stmt rows _ hAcc =>
      Qsag.Spec.AggregateSoundnessOutcome.of_witness
        (verifyStepOp256Aggregate_validWitness H log stmt rows hAcc))

/-- **`Spec.DataRefines` Simulation Against `Spec.idealAggregateMachine`
    (`stepOp256Aggregate_dataRefines_ideal`)**:
    Every trace accepted by `Spec.rawAggregateVerifierMachine verifyStepOp256Aggregate`
    is simulated step-for-step by `Spec.idealAggregateMachine (verifyAggNativeSig xmssPoseidon2Geom)`. -/
def stepOp256Aggregate_dataRefines_ideal {nVal : Nat}
    (H : Qsag.Spec.Bytes → Qsag.Spec.Bytes) :
    Qsag.Spec.DataRefines
      (Qsag.Spec.rawAggregateVerifierMachine (verifyStepOp256Aggregate (nVal := nVal)) H)
      (Qsag.Spec.idealAggregateMachine (Qsag.verifyAggNativeSig Qsag.xmssPoseidon2Geom))
      (Qsag.Spec.verifiedAggregateVisIn (extractStepOp256Aggregate (nVal := nVal)))
      id :=
  Qsag.Spec.unconditionalAggregate_dataRefines_ideal
    (Qsag.verifyAggNativeSig Qsag.xmssPoseidon2Geom)
    (verifyStepOp256Aggregate (nVal := nVal))
    (extractStepOp256Aggregate (nVal := nVal)) H
    (fun stmt rows log hAcc => verifyStepOp256Aggregate_validWitness H log stmt rows hAcc)

/-- Multi-turn trace inclusion from `rawAggregateVerifierMachine verifyStepOp256Aggregate`
    into `idealAggregateMachine` via `stepOp256Aggregate_dataRefines_ideal`. -/
theorem stepOp256Aggregate_preserve_admitsTrace {nVal : Nat}
    (H : Qsag.Spec.Bytes → Qsag.Spec.Bytes)
    {trace : List (Qsag.Spec.AggregateSubmission Qsag.AggValidatorPk StepOp256AggregateProof nVal × Unit)}
    (hAdmits : (Qsag.Spec.rawAggregateVerifierMachine (verifyStepOp256Aggregate (nVal := nVal)) H).AdmitsTrace
      trace) :
    (Qsag.Spec.idealAggregateMachine (Qsag.verifyAggNativeSig Qsag.xmssPoseidon2Geom)).AdmitsTrace
      (Qsag.Spec.projectTrace
        (Qsag.Spec.verifiedAggregateVisIn (extractStepOp256Aggregate (nVal := nVal))) id trace) :=
  (stepOp256Aggregate_dataRefines_ideal H).preserve_admitsTrace hAdmits

/-- **End-to-End Quorum Bound Specialized to `verifyStepOp256Aggregate`
    (`stepOp256Aggregate_quorum_bound`)**:
    Discharges `C : Spec.AggregateExtractorSound` in `aggregate_extractor_sound_quorum_bound`
    unconditionally via `stepOp256Aggregate_extractorSound`. -/
theorem stepOp256Aggregate_quorum_bound {nVal nC n nA : Nat}
    (custody : Fin nVal → Qsag.Composed.Custody)
    (oracle : Fin nC → Qsag.Spec.Bytes → Qsag.Spec.Bytes) (q : Nat)
    (hPos : 0 < n) (π : Qsag.Spec.CoinSplit n nC nA)
    (prover : Fin nA → Qsag.Spec.Code Qsag.Spec.byteOracleIface
      (Qsag.Spec.AggregateStatement Qsag.AggValidatorPk nVal × StepOp256AggregateProof))
    (fail : Fin n → Bool)
    (hFail : ∀ ω : Fin n, fail ω = true →
      (∀ v : Fin nVal,
        (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).1.1.roster v =
          (custody v).state.pk) ∧
      verifyStepOp256Aggregate (oracle (π.chal ω))
        (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).1.1
        (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).1.2 = true ∧
      ∃ v : Fin nVal,
        (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q
          (prover (π.advc ω))).1.1.bitmap.getLsbD v.val = true ∧
        ¬ ((∃ b : Qsag.Spec.AggregateBreak,
            Qsag.Spec.TranscriptBreak (oracle (π.chal ω))
              (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).2 b) ∨
          (∃ sig : Qsag.AggNativeSignature,
            extractStepOp256Aggregate
              (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).2
              (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).1.1
              (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).1.2 v =
                some sig ∧
            Qsag.verifyAggNativeSig Qsag.xmssPoseidon2Geom (custody v).state.pk
              (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q
                (prover (π.advc ω))).1.1.message sig = true ∧
            Qsag.Composed.quorumParticipated (custody v)
              (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q
                (prover (π.advc ω))).1.1.message = false) ∨
          Qsag.Composed.quorumParticipated (custody v)
            (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q
              (prover (π.advc ω))).1.1.message = true)) :
    Qsag.Spec.GameBound (Qsag.Spec.FinGame.mk hPos fail).winProb Qsag.Spec.RatBound.zero :=
  aggregate_extractor_sound_quorum_bound Qsag.xmssPoseidon2Geom custody
    verifyStepOp256Aggregate extractStepOp256Aggregate oracle q Qsag.Spec.RatBound.zero
    (stepOp256Aggregate_extractorSound oracle q) hPos π prover fail hFail

/-- **Completeness of `verifyStepOp256Aggregate` on Valid Native Committee Signatures
    (`verifyStepOp256Aggregate_complete`)**:
    Any non-empty committee statement whose active validators hold valid `.xmssPoseidon2`
    signatures produces an accepted 256-column `StepOp` table via `stepXmssSlotsRows`. -/
theorem verifyStepOp256Aggregate_complete {nVal : Nat} (hn : 0 < nVal)
    (H : Qsag.Spec.Bytes → Qsag.Spec.Bytes)
    (stmt : Qsag.Spec.AggregateStatement Qsag.AggValidatorPk nVal)
    (sig : Fin nVal → Qsag.AggNativeSignature)
    (dflt : Qsag.AggNativeSignature)
    (hValid : ∀ i : Fin nVal, stmt.bitmap.getLsbD i.val = true →
      Qsag.verifyAggNativeSig Qsag.xmssPoseidon2Geom (stmt.roster i) stmt.message (sig i) = true) :
    verifyStepOp256Aggregate H stmt
      (Qsag.stepXmssSlotsRows (stepOp256CommitteeSlots stmt) (fun _ => stmt.message)
        (fun k => if hk : k < nVal then sig ⟨k, hk⟩ else dflt)) = true := by
  unfold verifyStepOp256Aggregate
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨decide_eq_true hn, ?_⟩, ?_⟩
  · refine List.all_eq_true.mpr (fun i _ => ?_)
    cases hAct : stmt.bitmap.getLsbD i.val
    · rfl
    · simp only [Bool.not_true, Bool.false_or, beq_iff_eq]
      exact Qsag.stepXmssNative_profile (stmt.roster i) stmt.message (sig i) (hValid i hAct)
  · have hSlotsLen : (stepOp256CommitteeSlots stmt).length = nVal := by
      unfold stepOp256CommitteeSlots
      rw [List.length_map, List.length_finRange]
    refine Qsag.stepXmssSlotsRows_of_verify (stepOp256CommitteeSlots stmt)
      (fun _ => stmt.message)
      (fun k => if hk : k < nVal then sig ⟨k, hk⟩ else dflt)
      (by rw [hSlotsLen]; exact hn) (fun k pub hSlot => ?_)
    have hkSlots : k < (stepOp256CommitteeSlots stmt).length :=
      (List.getElem?_eq_some_iff.mp hSlot).1
    have hk : k < nVal := by rwa [hSlotsLen] at hkSlots
    rw [stepOp256CommitteeSlots_getElem? stmt k hk] at hSlot
    let idx : Fin nVal := ⟨k, hk⟩
    cases hAct : stmt.bitmap.getLsbD k
    · rw [hAct] at hSlot; cases hSlot
    · rw [hAct] at hSlot
      simp only [↓reduceIte, Option.some.injEq] at hSlot
      subst hSlot
      refine ⟨rfl, ?_⟩
      rw [dite_eq_left hk]
      exact hValid idx hAct

/-- Unconditional inhabitedness witness: `verifyStepOp256Aggregate` accepts a concrete 512-row
    committee table and inhabits `stepOp256Aggregate_extractorSound`. -/
theorem inhabited_stepOp256Aggregate_accepts :
    ∃ (oracle : Fin 1 → Qsag.Spec.Bytes → Qsag.Spec.Bytes) (q : Nat)
      (stmt : Qsag.Spec.AggregateStatement Qsag.AggValidatorPk 1)
      (rows : StepOp256AggregateProof),
      verifyStepOp256Aggregate (oracle ⟨0, by decide⟩) stmt rows = true ∧
      Qsag.Spec.AggregateExtractorSound
        (Qsag.Spec.StraightLineExtractor (fun _ => none) (stepOp256ProofSigs 1))
        (Qsag.verifyAggNativeSig Qsag.xmssPoseidon2Geom)
        (verifyStepOp256Aggregate (nVal := 1))
        (extractStepOp256Aggregate (nVal := 1))
        oracle q Qsag.Spec.RatBound.zero := by
  let pk0 : Qsag.AggValidatorPk := ⟨.xmssPoseidon2, Qsag.auditPkSeed, Qsag.auditPkSeed⟩
  let stmt : Qsag.Spec.AggregateStatement Qsag.AggValidatorPk 1 := ⟨fun _ => pk0, 0#1, Qsag.auditMsg⟩
  let rows : StepOp256AggregateProof :=
    List.replicate (1 * Qsag.stepOpRowsPerSigner .xmssPoseidon2) Qsag.stepInactiveRow
  refine ⟨fun _ b => b, 0, stmt, rows, ?_, stepOp256Aggregate_extractorSound _ 0⟩
  unfold verifyStepOp256Aggregate
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨by decide, by decide⟩, ?_⟩
  have hSlots : stepOp256CommitteeSlots stmt = List.replicate 1 none := by
    have hFin1 : List.finRange 1 = [⟨0, by decide⟩] := by decide
    have hBit0 : (0#1 : BitVec 1).getLsbD 0 = false := by decide
    unfold stepOp256CommitteeSlots
    rw [hFin1]
    dsimp only [List.map, stmt]
    rw [hBit0]
    rfl
  rw [hSlots]
  exact Qsag.stepInactiveCommittee_table .xmssPoseidon2 1 (by decide)

/-- `#tooth`: `verifyStepOp256Aggregate` rejects an empty trace `[]` on any non-empty committee. -/
theorem tooth_stepOp256Aggregate_rejects_empty_rows
    (H : Qsag.Spec.Bytes → Qsag.Spec.Bytes)
    (stmt : Qsag.Spec.AggregateStatement Qsag.AggValidatorPk 1) :
    ¬ (verifyStepOp256Aggregate H stmt [] = true) := by
  intro hAcc
  unfold verifyStepOp256Aggregate at hAcc
  rw [Bool.and_eq_true] at hAcc
  have hLen := ((Qsag.stepOp256TableOk_iff_rows .xmssPoseidon2
    (stepOp256CommitteeSlots stmt) []).mp hAcc.2).2.1
  have hSlotsLen : (stepOp256CommitteeSlots stmt).length = 1 := rfl
  rw [hSlotsLen, Qsag.stepOpRowsPerSigner.public_eqs.1] at hLen
  exact absurd hLen (by decide)

#verify_constructive
  Qsag.Top.extractStepOp256Aggregate_straightLine
  Qsag.Top.verifyStepOp256Aggregate_validWitness
  Qsag.Top.stepOp256Aggregate_extractorSound
  Qsag.Top.stepOp256Aggregate_preserve_admitsTrace
  Qsag.Top.stepOp256Aggregate_quorum_bound
  Qsag.Top.verifyStepOp256Aggregate_complete
  Qsag.Top.inhabited_stepOp256Aggregate_accepts
  Qsag.Top.tooth_stepOp256Aggregate_rejects_empty_rows

#verify_inhabited Qsag.Top.verifyStepOp256Aggregate_validWitness Qsag.Top.inhabited_stepOp256Aggregate_accepts
#tooth_pair Qsag.Top.stepOp256Aggregate_extractorSound vs Qsag.Top.tooth_stepOp256Aggregate_rejects_empty_rows

open Qsag

open CommRingOps
open Qsag.Aggregation

-- BEGIN COMPARATOR ROSTER

theorem goldilocksReduce128Spec_sound {lo hi : Nat}
    (hLo : lo < 2 ^ 64) (hHi : hi < 2 ^ 64) :
    goldilocksReduce128Spec lo hi < goldilocksPrime ∧
    goldilocksReduce128Spec lo hi = (lo + 2 ^ 64 * hi) % goldilocksPrime :=
  _root_.Qsag.goldilocksReduce128Spec_sound hLo hHi

theorem Goldilocks_mul_inv_cancel {a : Goldilocks} (ha : a ≠ Goldilocks.zero) :
    CommRingOps.mul a (Goldilocks.inv a) = CommRingOps.one :=
  _root_.Qsag.Goldilocks.mul_inv_cancel ha

theorem towerMul_cancel_left (k : Nat) (a b c : TowerElem k)
    (ha : a ≠ towerZero k) (h : towerMul k a b = towerMul k a c) : b = c :=
  _root_.Qsag.towerMul_cancel_left k a b c ha h

theorem ghashDiff_roots_bound (bs₁ bs₂ : List Tower128) (L : Nat) (keys : List Tower128)
    (h₁ : bs₁.length ≤ L) (h₂ : bs₂.length ≤ L) (hnd : keys.Nodup)
    (hne : ∃ H, ghashPoly H bs₁ ≠ ghashPoly H bs₂)
    (heq : ∀ H ∈ keys, ghashPoly H bs₁ = ghashPoly H bs₂) : keys.length ≤ L :=
  _root_.Qsag.ghashDiff_roots_bound bs₁ bs₂ L keys h₁ h₂ hnd hne heq

theorem packTowerLenBlock_injective {a₁ c₁ a₂ c₂ : UInt64}
    (h : packTowerLenBlock a₁ c₁ = packTowerLenBlock a₂ c₂) : a₁ = a₂ ∧ c₁ = c₂ :=
  _root_.Qsag.packTowerLenBlock_injective h

theorem be_injective {w n m : Nat} (hn : n < 256 ^ w) (hm : m < 256 ^ w)
    (h : be w n = be w m) : n = m :=
  _root_.Qsag.be_injective hn hm h

theorem encodeMultiFrame_injective {xs ys : List (List UInt8)}
    (h : encodeMultiFrame xs = encodeMultiFrame ys) : xs = ys :=
  _root_.Qsag.encodeMultiFrame_injective h

theorem chiWordBit_eq_keccakChiBit (w0 w1 w2 : UInt64) (i : Nat) (hi : i < 64) :
    (w0 ^^^ ((~~~w1) &&& w2)).toBitVec.getLsbD i =
      keccakChiBit (w0.toBitVec.getLsbD i) (w1.toBitVec.getLsbD i) (w2.toBitVec.getLsbD i) :=
  _root_.Qsag.chiWordBit_eq_keccakChiBit w0 w1 w2 i hi

theorem cshake256Xof_empty_eq_shake256Xof (outLen : Nat) (input : List UInt8) :
    cshake256Xof outLen [] input = shake256Xof outLen input :=
  _root_.Qsag.cshake256Xof_empty_eq_shake256Xof outLen input

theorem poseidon2Perm12Inv_left_inv (st : Poseidon2State12) :
    poseidon2Perm12Inv (poseidon2Perm12 st) = st :=
  _root_.Qsag.poseidon2Perm12Inv_left_inv st

theorem poseidon2Perm12Inv_right_inv (st : Poseidon2State12) :
    poseidon2Perm12 (poseidon2Perm12Inv st) = st :=
  _root_.Qsag.poseidon2Perm12Inv_right_inv st

theorem bytesToLimbs56_injective {m₁ m₂ : List UInt8}
    (h : bytesToLimbs56 m₁ = bytesToLimbs56 m₂) : m₁ = m₂ :=
  _root_.Qsag.bytesToLimbs56_injective h

theorem popcount_union_disjoint_eq_add :
    ∀ (b1 b2 : SignerBitmapSpec),
      b1.length = b2.length →
      bitmapDisjointSpec b1 b2 = true →
      bitmapPopcountSpec (bitmapUnionSpec b1 b2) =
        bitmapPopcountSpec b1 + bitmapPopcountSpec b2 :=
  _root_.Qsag.popcount_union_disjoint_eq_add

theorem whir_query_miss_bound {α : Type} (bad : α → Bool) (dom : List α) (q dn dd : Nat)
    (hfar : dn * dom.length ≤ dd * countGood bad dom) :
    ((aggDistinctTuples q dom).filter (fun t => t.all (fun x => !bad x))).length * dd ^ q ≤
      (dd - dn) ^ q * (aggDistinctTuples q dom).length :=
  _root_.Qsag.whir_query_miss_bound bad dom q dn dd hfar

theorem validProductionJortsBatch_item_forgery_break (params : PqHashParams)
    (items : List JortsBatchItem) (hValid : ValidProductionJortsBatch params items = true)
    (item : JortsBatchItem) (hItem : item ∈ items)
    (sk : PqSecretKey) (queries : List ProdSigningQuery)
    (hPk : item.validatorPk = derivePublicKey poseidon2Suite params sk)
    (hw : params.w = 4 ∨ params.w = 16)
    (hOneTime : ∀ q, q ∈ queries → ∀ q', q' ∈ queries → q.epoch = q'.epoch → q = q')
    (hFresh : ∀ e ∈ productionSigningLog poseidon2Suite params sk queries, e.1 ≠ item.message) :
    ProdSmTcrBreak poseidon2Suite params sk (productionSigningLog poseidon2Suite params sk queries) ∨
    ProdPreimageBreak poseidon2Suite params sk (productionSigningLog poseidon2Suite params sk queries)
      item.message item.signature :=
  _root_.Qsag.validProductionJortsBatch_item_forgery_break params items hValid item hItem
    sk queries hPk hw hOneTime hFresh

theorem stepOp256TableOk_xmss_extract (slots : List StepOpSlot) (rows : List StepOpRow)
    (k : Nat) (pub : AggValidatorPk × Digest5) (msg : List UInt8)
    (hTable : stepOp256TableOk .xmssPoseidon2 slots rows = true)
    (hSlot : slots[k]? = some (some pub))
    (hProf : pub.1.profile = .xmssPoseidon2)
    (hMu : pub.2 = computeMessageMu pub.1 msg) :
    verifyAggNativeSig xmssPoseidon2Geom pub.1 msg
      (stepXmssSig (stepOpSlotRow .xmssPoseidon2 rows k)) = true :=
  _root_.Qsag.stepOp256TableOk_xmss_extract slots rows k pub msg hTable hSlot hProf hMu

theorem stepOp256TableOk_corduroy_extract (slots : List StepOpSlot) (rows : List StepOpRow)
    (k : Nat) (pub : AggValidatorPk × Digest5) (msg : List UInt8)
    (hTable : stepOp256TableOk .corduroyPoseidon2 slots rows = true)
    (hSlot : slots[k]? = some (some pub))
    (hProf : pub.1.profile = .corduroyPoseidon2)
    (hMu : pub.2 = computeMessageMu pub.1 msg) :
    verifyAggNativeSig corduroyPoseidon2Geom pub.1 msg
      (stepCordSig (stepOpSlotRow .corduroyPoseidon2 rows k)) = true :=
  _root_.Qsag.stepOp256TableOk_corduroy_extract slots rows k pub msg hTable hSlot hProf hMu

theorem stepXmssRows_roundTrip (pk : AggValidatorPk) (msg : List UInt8) (sig : AggNativeSignature)
    (h : verifyAggNativeSig xmssPoseidon2Geom pk msg sig = true) :
    verifyAggNativeSig xmssPoseidon2Geom pk msg
      (stepXmssSig (stepOpSlotRow .xmssPoseidon2 (stepXmssRows pk (computeMessageMu pk msg) sig) 0)) = true :=
  _root_.Qsag.stepXmssRows_roundTrip pk msg sig h

theorem quinticWhirFold2_evalCoeffs (x α : QuinticGoldilocks) (P : List QuinticGoldilocks)
    (hx : x ≠ zero) :
    SuccinctWhirAgg.quinticWhirFold2 x α (RoundPoly.evalCoeffs P x)
      (RoundPoly.evalCoeffs P (neg x)) =
      RoundPoly.evalCoeffs (SuccinctWhirAgg.foldPolyCoeffs α P) (mul x x) :=
  _root_.Qsag.SuccinctWhirAgg.quinticWhirFold2_evalCoeffs x α P hx

theorem packedQuinticWhir_geometry (n : Nat) (lo : 16 ≤ n) (hi : n ≤ 28) :
    let ss := (ZkHemV2Packed.packedProdSched n).stages
    3 ≤ ss.length ∧ ss.length ≤ 4 ∧ ss.all (fun st =>
      decide (0 < st.foldK ∧ st.logDomain + st.foldK ≤ 32 ∧ 0 < st.queryCount ∧
        st.queryCount ≤ 267 ∧ 0 < st.oodCount ∧ st.oodCount ≤ 5)) = true :=
  _root_.Qsag.SuccinctWhirAgg.packedQuinticWhir_geometry n lo hi

theorem zkHemV2MultiStage_geometry :
    SuccinctWhirAgg.zkHemV2MultiStageSched.numRounds = 9 ∧
    SuccinctWhirAgg.zkHemV2MultiStageSched.johnsonOk = true ∧
    ([0, 1, 2, 3].map (SuccinctWhirAgg.domainLog SuccinctWhirAgg.zkHemV2MultiStageSched.stages)) =
      [8, 7, 6, 5] :=
  _root_.Qsag.SuccinctWhirAgg.zkHemV2MultiStage_geometry

theorem measuredSuccinctWhirAggregate_refines_idealAggregate {nVal n : Nat}
    (logCells : Nat) (profile : AggSigProfile) (fr : SuccinctWhirAgg.SuccinctWhirByteFraming)
    (nodeDecode : Spec.Bytes → Option (Nat × Nat × Spec.Bytes × Spec.Bytes))
    (slotC : SuccinctWhirAgg.SlotLeafTableCodec)
    (hPos : 0 < n) (H : Fin n → Spec.Bytes → Spec.Bytes) (Q : Nat)
    (prover : Fin n → Spec.Code Spec.byteOracleIface
      (Spec.AggregateStatement AggValidatorPk nVal × SuccinctWhirAgg.SuccinctWhirAggregateProof)) :
    let extract := SuccinctWhirAgg.extractSuccinctWhirAggregate (nVal := nVal) profile fr nodeDecode slotC
    let single := verifyAggNativeSig (SuccinctWhirAgg.profileGeom profile)
    let verify := SuccinctWhirAgg.verifySuccinctWhirAggregate (nVal := nVal) logCells profile fr
    let games := SuccinctWhirAgg.measuredSlotGames logCells profile fr nodeDecode slotC hPos H Q prover
    Spec.GameBound (Spec.aggregateRefinementGame hPos single verify extract Q H prover).winProb
      (Spec.RatBound.add games.1.winProb games.2.winProb) :=
  _root_.Qsag.SuccinctWhirAgg.measuredSuccinctWhirAggregate_refines_idealAggregate
    logCells profile fr nodeDecode slotC hPos H Q prover

theorem succinctWhirAggregate_extractorSound {nVal nC : Nat}
    (logCells : Nat) (profile : AggSigProfile) (prof : ZkHemV2Packed.WhirCommitmentProfile)
    (hLo : 16 ≤ logCells) (hHi : logCells ≤ 28)
    (fr : SuccinctWhirAgg.SuccinctWhirByteFraming)
    (nodeDecode : Spec.Bytes → Option (Nat × Nat × Spec.Bytes × Spec.Bytes))
    (slotC : SuccinctWhirAgg.SlotLeafTableCodec)
    (oracle : Fin nC → Spec.Bytes → Spec.Bytes) (Q : Nat) (hQ : Q ≤ 2 ^ 64)
    (hSlots : SuccinctWhirAgg.PackedSlotGameBounds (nVal := nVal) logCells profile prof fr
      nodeDecode slotC oracle Q) :
    let ε := SuccinctWhirAgg.toSpecRatBound
      (RatBound.add (ZkHemV2Packed.packedProdQromError logCells Q)
        (ZkHemV2Packed.merkleProfileQromBound prof Q))
    Spec.AggregateExtractorSound
      (Spec.StraightLineExtractor (SuccinctWhirAgg.decodeSlotLeafSig slotC)
        SuccinctWhirAgg.succinctWhirProofSigs)
      (verifyAggNativeSig (SuccinctWhirAgg.profileGeom profile))
      (SuccinctWhirAgg.verifySuccinctWhirAggregate (nVal := nVal) logCells profile fr)
      (SuccinctWhirAgg.extractSuccinctWhirAggregate (nVal := nVal) profile fr nodeDecode slotC)
      oracle Q ε ∧
    ε.num * 2 ^ 128 < 1 * ε.den :=
  _root_.Qsag.SuccinctWhirAgg.succinctWhirAggregate_extractorSound
    logCells profile prof hLo hHi fr nodeDecode slotC oracle Q hQ hSlots

theorem tooth_omitted_stage0_queries_or_ood_accepts_bogus_table {nC : Nat} (hPos : 0 < nC)
    (logCells : Nat) (hLo : 16 ≤ logCells) (hHi : logCells ≤ 28) (profile : AggSigProfile)
    (fr : SuccinctWhirAgg.SuccinctWhirByteFraming) (slotC : SuccinctWhirAgg.SlotLeafTableCodec)
    (tag : ∀ bs, slotC.decode (0 :: bs) = none)
    (extract : List (Spec.Bytes × Spec.Bytes) → Spec.AggregateStatement AggValidatorPk 1 →
      SuccinctWhirAgg.SuccinctWhirAggregateProof → Fin 1 → Option AggNativeSignature)
    (oracle : Fin nC → Spec.Bytes → Spec.Bytes)
    (width : ∀ c bs, (oracle c bs).length = SuccinctWhirAgg.packedChallengeBits / 8)
    (answer : ∀ c bs, slotC.decode (oracle c bs) = none) (Q : Nat) (hQ : 1 ≤ Q)
    {ε : Spec.RatBound} (hε : ε.num < ε.den) :
    ¬ Spec.AggregateExtractorSound
      (Spec.StraightLineExtractor (SuccinctWhirAgg.decodeSlotLeafSig slotC)
        SuccinctWhirAgg.succinctWhirProofSigs)
      (verifyAggNativeSig (SuccinctWhirAgg.profileGeom profile))
      (SuccinctWhirAgg.verifySuccinctWhirOmitQueriesAndOod logCells profile fr)
      extract oracle Q ε :=
  _root_.Qsag.SuccinctWhirAgg.tooth_omitted_stage0_queries_or_ood_accepts_bogus_table
    hPos logCells hLo hHi profile fr slotC tag extract oracle width answer Q hQ hε

theorem ivcRootProof_byteSize_independent_of_depth {params : MultiDepthQrom.IvcWhirParams}
    (d₁ d₂ : Nat)
    (r₁ : MultiDepthQrom.SuccinctIvcRootProof params d₁)
    (r₂ : MultiDepthQrom.SuccinctIvcRootProof params d₂)
    (h₁ : r₁.rootProof.wellFormed = true) (h₂ : r₂.rootProof.wellFormed = true) :
    MultiDepthQrom.encodedByteLen r₁.rootProof = params.openingByteLen ∧
    MultiDepthQrom.encodedByteLen r₂.rootProof = params.openingByteLen ∧
    MultiDepthQrom.encodedByteLen r₁.rootProof = MultiDepthQrom.encodedByteLen r₂.rootProof :=
  _root_.Qsag.MultiDepthQrom.ivcRootProof_byteSize_independent_of_depth d₁ d₂ r₁ r₂ h₁ h₂

theorem extractMultiDepthQrom_inductive_sound {nVal : Nat}
    (env : MultiDepthQrom.IvcExtractionContext nVal)
    (hDep : SuccinctWhirAgg.IsDeployedAggProfile env.profile)
    (H : Spec.Bytes → Spec.Bytes) (T : MultiDepthQrom.QromQueryTranscript)
    (hNoColl : MultiDepthQrom.hasQueryCollision T = false)
    (d : Nat) (stmt : MultiDepthQrom.IvcTreeStatement)
    (pi : MultiDepthQrom.FixedShapeWhirProof env.cfg.params)
    (hVer : MultiDepthQrom.verifyConcreteIvcRoot env.profile env.cfg H d stmt pi = true) :
    (∃ shards : List (MultiDepthQrom.ExtractedLeafShard nVal),
      MultiDepthQrom.extractMultiDepthQrom env H d T stmt pi = some shards ∧
      shards.length = 2 ^ d ∧
      shards.map MultiDepthQrom.ExtractedLeafShard.shardId = List.range' stmt.lo (2 ^ d) ∧
      (shards.map MultiDepthQrom.ExtractedLeafShard.quorumCount).sum = stmt.totalQuorums ∧
      ∀ shard ∈ shards,
        MultiDepthQrom.ValidQuorumSignatures env.profile H stmt.policyRegistryRoot stmt.message shard) ∨
    (∃ (nodeIdx : Nat) (lvl : Nat) (sNode : MultiDepthQrom.IvcTreeStatement)
        (piNode : MultiDepthQrom.FixedShapeWhirProof env.cfg.params),
      nodeIdx < MultiDepthQrom.treeNodeCount d ∧ lvl ≤ d ∧
      MultiDepthQrom.treeNodeAt env H T d stmt pi nodeIdx = some (lvl, sNode, piNode) ∧
      MultiDepthQrom.concreteIvcStepBad env H T lvl sNode piNode = true) :=
  _root_.Qsag.MultiDepthQrom.extractMultiDepthQrom_inductive_sound
    env hDep H T hNoColl d stmt pi hVer

theorem multidepth_recursive_refines_idealAggregate {nVal : Nat}
    (env : MultiDepthQrom.IvcExtractionContext nVal)
    (hDep : SuccinctWhirAgg.IsDeployedAggProfile env.profile)
    (H : Spec.Bytes → Spec.Bytes) (d : Nat)
    (T : MultiDepthQrom.QromQueryTranscript) (stmt : MultiDepthQrom.IvcTreeStatement)
    (rootProof : MultiDepthQrom.FixedShapeWhirProof env.cfg.params)
    (shards : List (MultiDepthQrom.ExtractedLeafShard nVal))
    (hEx : MultiDepthQrom.extractMultiDepthQrom env H d T stmt rootProof = some shards) :
    (∀ sh ∈ shards,
      Spec.ValidAggregateWitness (verifyAggNativeSig (SuccinctWhirAgg.profileGeom env.profile))
        sh.stmt (fun i => some (SuccinctWhirAgg.extractSlotNativeSig env.profile sh.rows i.val))) ∧
    (Spec.idealAggregateMachine
      (verifyAggNativeSig (SuccinctWhirAgg.profileGeom env.profile))).ValidTrace []
      (shards.map (fun sh =>
        ((sh.stmt, fun i => some (SuccinctWhirAgg.extractSlotNativeSig env.profile sh.rows i.val)), ())))
      (shards.map MultiDepthQrom.ExtractedLeafShard.stmt) :=
  _root_.Qsag.MultiDepthQrom.multidepth_recursive_refines_idealAggregate
    env hDep H d T stmt rootProof shards hEx

theorem multidepth_recursive_budget_lt_128
    (prof : ZkHemV2Packed.WhirCommitmentProfile) {d Q : Nat} (hd : d ≤ 16) (hQ : Q ≤ 2 ^ 64) :
    RatBound.lt
      (RatBound.add
        (RatBound.scale (MultiDepthQrom.treeNodeCount d)
          (ClosedWhir.scheduleQromError ZkHemV2Packed.zkHemV2RecursiveMarginSched Q))
        (ZkHemV2Packed.merkleProfileQromBound prof Q))
      (RatBound.invPow2 128) :=
  _root_.Qsag.MultiDepthQrom.multidepth_recursive_budget_lt_128 prof hd hQ

theorem realDepth2AcceptsAndExtracts_of_check
    (checked : MultiDepthQrom.realDepth2AcceptsAndExtracts = true) :
    ∃ shards,
      MultiDepthQrom.realDepth2Run =
        some (MultiDepthQrom.realDepth2Stmt, MultiDepthQrom.realDepth2IvcProof,
          MultiDepthQrom.realDepth2Transcript) ∧
      MultiDepthQrom.hasQueryCollision MultiDepthQrom.realDepth2Transcript = false ∧
      MultiDepthQrom.verifyConcreteIvcRoot MultiDepthQrom.realDepth2Env.profile
        MultiDepthQrom.realDepth2Env.cfg MultiDepthQrom.ivcFastXof56
        2 MultiDepthQrom.realDepth2Stmt MultiDepthQrom.realDepth2IvcProof = true ∧
      MultiDepthQrom.extractMultiDepthQrom MultiDepthQrom.realDepth2Env MultiDepthQrom.ivcFastXof56
        2 MultiDepthQrom.realDepth2Transcript MultiDepthQrom.realDepth2Stmt
        MultiDepthQrom.realDepth2IvcProof = some shards ∧
      shards.length = 4 ∧
      shards.map MultiDepthQrom.ExtractedLeafShard.shardId = [0, 1, 2, 3] ∧
      (shards.map MultiDepthQrom.ExtractedLeafShard.quorumCount).sum = 4 ∧
      ∀ sh ∈ shards,
        MultiDepthQrom.ValidQuorumSignatures MultiDepthQrom.realDepth2Env.profile
          MultiDepthQrom.ivcFastXof56 MultiDepthQrom.realDepth2Stmt.policyRegistryRoot
          MultiDepthQrom.realDepth2Stmt.message sh :=
  _root_.Qsag.MultiDepthQrom.realDepth2AcceptsAndExtracts_of_check checked

theorem depth2_concrete_ivc_root_accepts :
    MultiDepthQrom.verifyConcreteIvcRoot MultiDepthQrom.Depth2Cert.fastEnv.profile
      MultiDepthQrom.Depth2Cert.fastEnv.cfg MultiDepthQrom.Depth2Cert.natXof56
      2 MultiDepthQrom.Depth2Cert.rootStmt MultiDepthQrom.Depth2Cert.rootPi = true :=
  _root_.Qsag.MultiDepthQrom.Depth2Cert.fast_root_accepts

theorem depth2_concrete_ivc_root_flip_rejected :
    ¬ (MultiDepthQrom.verifyConcreteIvcRoot MultiDepthQrom.Depth2Cert.fastEnv.profile
      MultiDepthQrom.Depth2Cert.fastEnv.cfg MultiDepthQrom.Depth2Cert.natXof56
      2 MultiDepthQrom.Depth2Cert.rootStmt
      (MultiDepthQrom.flipRootCoefficient MultiDepthQrom.Depth2Cert.rootPi) = true) :=
  _root_.Qsag.MultiDepthQrom.Depth2Cert.fast_root_flip

theorem depth2_concrete_ivc_ood_flip_rejected :
    ¬ (MultiDepthQrom.verifyConcreteIvcRoot MultiDepthQrom.Depth2Cert.fastEnv.profile
      MultiDepthQrom.Depth2Cert.fastEnv.cfg MultiDepthQrom.Depth2Cert.natXof56
      2 MultiDepthQrom.Depth2Cert.rootStmt
      (MultiDepthQrom.flipSecondStageOod MultiDepthQrom.Depth2Cert.rootPi) = true) :=
  _root_.Qsag.MultiDepthQrom.Depth2Cert.fast_ood_flip

theorem depth2_concrete_ivc_parent_stitch_accepts :
    MultiDepthQrom.parentStitchCheck MultiDepthQrom.Depth2Cert.fastEnv
      MultiDepthQrom.Depth2Cert.natXof56 1 MultiDepthQrom.Depth2Cert.rootStmt
      MultiDepthQrom.Depth2Cert.leftStmt MultiDepthQrom.Depth2Cert.rightStmt
      MultiDepthQrom.Depth2Cert.leftPi MultiDepthQrom.Depth2Cert.rightPi
      MultiDepthQrom.Depth2Cert.rootPi MultiDepthQrom.Depth2Cert.rootFold = true :=
  _root_.Qsag.MultiDepthQrom.Depth2Cert.fast_stitch

theorem depth2_concrete_ivc_child_boundary_flip_rejected :
    ¬ (MultiDepthQrom.parentStitchCheck MultiDepthQrom.Depth2Cert.fastEnv
      MultiDepthQrom.Depth2Cert.natXof56 1 MultiDepthQrom.Depth2Cert.rootStmt
      { MultiDepthQrom.Depth2Cert.leftStmt with hi := MultiDepthQrom.Depth2Cert.leftStmt.hi ^^^ 1 }
      MultiDepthQrom.Depth2Cert.rightStmt MultiDepthQrom.Depth2Cert.leftPi
      MultiDepthQrom.Depth2Cert.rightPi MultiDepthQrom.Depth2Cert.rootPi
      MultiDepthQrom.Depth2Cert.rootFold = true) :=
  _root_.Qsag.MultiDepthQrom.Depth2Cert.fast_child_boundary_flip

theorem recursiveIvc_spineBudget_lt_128 {d Q : Nat} (hd : d ≤ 64) (hq : Q ≤ 2 ^ 64) :
    RatBound.lt (RecursiveIvcPublicRowQrom.spineBudget d Q) (RatBound.invPow2 128) :=
  _root_.Qsag.RecursiveIvcPublicRowQrom.spineBudget_lt_128 hd hq

theorem recursiveIvc_tree_public_sumchecks_qrom {d cardX anc Q : Nat}
    (hd : d ≤ 20) (hq : Q ≤ 2 ^ 64)
    (A : Fin (MultiDepthQrom.treeNodeCount d) → QuantumAdv cardX 320 anc Q)
    (codec : Fin (MultiDepthQrom.treeNodeCount d) →
      ClosedFs.FsCodec RecursiveIvcPublicRowQrom.PublicMessage 95 cardX)
    (claims : Fin (MultiDepthQrom.treeNodeCount d) → RecursiveIvcPublicRowQrom.RoundClaims)
    (hg : ∀ i pre m, pre.length < 95 →
      ((claims i).honest pre m).length ≤ RecursiveIvcPublicRowQrom.roundDegree pre.length + 1) :
    RatBound.lt
      (RatBound.sumList ((List.finRange (MultiDepthQrom.treeNodeCount d)).map
        fun i => RecursiveIvcPublicRowQrom.publicFsMass (A i) (codec i) (claims i)))
      (RatBound.invPow2 160) :=
  _root_.Qsag.RecursiveIvcPublicRowQrom.tree_public_sumchecks_qrom hd hq A codec claims hg

theorem recursiveIvc_overclaimed_spine_euf_cma_forgery {n : Nat}
    (env : MultiDepthQrom.IvcExtractionContext n)
    (H : MultiDepthQrom.IvcAlgebra.RO) (T : MultiDepthQrom.QromQueryTranscript)
    (dep : SuccinctWhirAgg.IsDeployedAggProfile env.profile)
    (hc : MultiDepthQrom.hasQueryCollision T = false)
    (d : Nat) (s : MultiDepthQrom.IvcTreeStatement)
    (p : RecursiveIvcPublicRowQrom.ProofAt env)
    (custody : Nat → Fin n → Composed.Custody)
    (over : RecursiveIvcPublicRowQrom.rangeCap
      (RecursiveIvcPublicRowQrom.honestShardParticipated custody s.message) s.lo (2 ^ d) <
      s.totalQuorums)
    (accept : MultiDepthQrom.verifyConcreteIvcRoot env.profile env.cfg H d s p = true) :
    let cap := RecursiveIvcPublicRowQrom.honestShardParticipated custody s.message
    RecursiveIvcPublicRowQrom.LocatedBad env H T d
      (RecursiveIvcPublicRowQrom.overclaimedSpineNodeAt env H T d s p cap) ∨
      ∃ sh, RecursiveIvcPublicRowQrom.extractOverclaimedSpine env H T d s p cap = some sh ∧
        s.lo ≤ sh.shardId ∧ sh.shardId < s.lo + 2 ^ d ∧ cap sh.shardId < sh.quorumCount ∧
        MultiDepthQrom.ValidQuorumSignatures env.profile H s.policyRegistryRoot s.message sh ∧
        ((∀ v, sh.stmt.roster v = (custody sh.shardId v).state.pk) →
          ∃ v, sh.stmt.bitmap.getLsbD v.val = true ∧
            Composed.QuorumForgery (SuccinctWhirAgg.profileGeom env.profile)
              (custody sh.shardId v) s.message) :=
  _root_.Qsag.RecursiveIvcPublicRowQrom.overclaimed_spine_euf_cma_forgery
    env H T dep hc d s p custody over accept

theorem recursiveIvc_unabsorbed_public_row_sumcheck_forges
    (r falseClaim honestEval : QuinticGoldilocks)
    (hr : CommRingOps.mul r (CommRingOps.sub r CommRingOps.one) ≠ CommRingOps.zero) :
    ∃ c0 c2 : QuinticGoldilocks,
      CommRingOps.add
        (MultiDepthQrom.IvcAlgebra.evalCoeffs
          (RecursiveIvcPublicRowQrom.quadratic falseClaim c0 c2) CommRingOps.zero)
        (MultiDepthQrom.IvcAlgebra.evalCoeffs
          (RecursiveIvcPublicRowQrom.quadratic falseClaim c0 c2) CommRingOps.one) = falseClaim ∧
      MultiDepthQrom.IvcAlgebra.evalCoeffs
        (RecursiveIvcPublicRowQrom.quadratic falseClaim c0 c2) r = honestEval :=
  _root_.Qsag.RecursiveIvcPublicRowQrom.tooth_unabsorbed_public_row_sumcheck_forges_claim
    r falseClaim honestEval hr

open Aggregation in
theorem publicHemQuintic_budget_lt_128 (profile : PublicHemQuintic128)
    (logCells qOracle : Nat) (hLo : 16 ≤ logCells) (hHi : logCells ≤ 28)
    (hQ : qOracle ≤ 2^64) :
    RatBound.lt (publicHemError profile logCells qOracle) ⟨1, 2^128, by decide⟩ :=
  _root_.Qsag.Aggregation.publicHemQuintic_budget_lt_128 profile logCells qOracle hLo hHi hQ

open ZkHemV2Packed ClosedWhir in
theorem zkHemV2_packed_all13_budget_lt_128
    (prof : WhirCommitmentProfile) (logCells Q : Nat)
    (hLo : 16 ≤ logCells) (hHi : logCells ≤ 28) (hQ : Q ≤ 2 ^ 64) :
    RatBound.lt
      (RatBound.add (packedProdQromError logCells Q) (merkleProfileQromBound prof Q))
      (RatBound.invPow2 128) :=
  _root_.Qsag.ZkHemV2Packed.zkHemV2_packed_all13_budget_lt_128 prof logCells Q hLo hHi hQ

open ClosedWhir ZkHemV2Cert SuccinctWhirAgg in
theorem packed_first_ood_positive_mass (n : Nat) (lo : 16 ≤ n) (hi : n ≤ 28)
    (st : WhirStage) (first : (zkHemV2ProdSched n).stages.head? = some st)
    (shift : QuinticGoldilocks) (nz : shift ≠ CommRingOps.zero) (seed : Fin (2^packedChallengeBits)) :
    ∃ word : QuinticGoldilocks → QuinticGoldilocks,
      let ps := gsDecodeList st.degBound st.agree (ZkHemV2.fiberRoots st.logDomain shift) word
      let bad := qsum (2^packedChallengeBits) fun c => if packedOodCollision ps c.val then 1 else 0
      0 < bad ∧ RatBound.lt ⟨bad,2^packedChallengeBits,Nat.two_pow_pos _⟩ (RatBound.invPow2 277) :=
  _root_.Qsag.SuccinctWhirAgg.packed_first_ood_positive_mass n lo hi st first shift nz seed

open Spv Spv.Universal in
theorem spirv_poseidon2_perm12_entry_universal (s : Poseidon2State12) :
    decode poseidon2Perm12SpvWords = some p2 ∧
    poseidonEntryStores p2 (fun i => (s.toList.map (·.val)).getD i 0) =
      some (expectedStores ((poseidon2Perm12 s).toList.map (·.val))) :=
  _root_.Qsag.Spv.Universal.spirv_poseidon2_perm12_entry_universal s

theorem rlib_x86_all19_dit_trace_data_independent
    (tr₁ tr₂ : List ((Fin 19 × Nat) × Qsag.X86State))
    (hSched : tr₁.map Prod.fst = tr₂.map Prod.fst) :
    tr₁.map (fun call => elfX86Leakage Spec.ExecMode.constantTimeSafe
        (rlibX86CtEntry call.1.1 call.1.2) call.2) =
      tr₂.map (fun call => elfX86Leakage Spec.ExecMode.constantTimeSafe
        (rlibX86CtEntry call.1.1 call.1.2) call.2) :=
  _root_.Qsag.rlib_x86_all19_dit_trace_data_independent tr₁ tr₂ hSched

theorem rlib_aarch64_all9_dit_trace_data_independent
    (tr₁ tr₂ : List ((Fin 9 × Nat × Arm64State) × Arm64State))
    (hSched : tr₁.map Prod.fst = tr₂.map Prod.fst) :
    tr₁.map (fun call => elfArm64Leakage Spec.ExecMode.constantTimeSafe
        (rlibArm64CtEntry call.1.1 call.1.2.1 call.1.2.2) call.2) =
      tr₂.map (fun call => elfArm64Leakage Spec.ExecMode.constantTimeSafe
        (rlibArm64CtEntry call.1.1 call.1.2.1 call.1.2.2) call.2) :=
  _root_.Qsag.rlib_aarch64_all9_dit_trace_data_independent tr₁ tr₂ hSched

open RecursiveIvcPublicRowQrom MultiDepthQrom ZkHemV2Packed ClosedWhir in
theorem depth16Schedule_tree_lt_128 {d Q : Nat} (hd : d ≤ 16) (hq : Q ≤ 2^64) :
    RatBound.lt (RatBound.add (RatBound.scale (treeNodeCount d)
      (RatBound.add (sumcheckBudget Q) (depth16WhirError Q)))
      (merkleProfileQromBound .poseidon2Gl24 Q)) (RatBound.invPow2 128) :=
  _root_.Qsag.RecursiveIvcPublicRowQrom.depth16Schedule_tree_lt_128 hd hq

-- END COMPARATOR ROSTER

abbrev recursiveIvcSpineBudgetLt128 := @RecursiveIvcPublicRowQrom.spineBudget_lt_128
abbrev recursiveIvcExtractLeafAlongSpineSound := @RecursiveIvcPublicRowQrom.extractLeafAlongSpine_sound
abbrev recursiveIvcOverclaimedSpineEufCmaForgery := @RecursiveIvcPublicRowQrom.overclaimed_spine_euf_cma_forgery
abbrev recursiveIvcSpineQromExtractorSound := @RecursiveIvcPublicRowQrom.multidepth_spine_qrom_extractor_sound
abbrev recursiveIvcTreePublicSumchecksQrom := @RecursiveIvcPublicRowQrom.tree_public_sumchecks_qrom
abbrev recursiveIvcDepth20BudgetInterval := RecursiveIvcPublicRowQrom.depth20_budget_interval
abbrev recursiveIvcPublicSumchecksQrom := @RecursiveIvcPublicRowQrom.public_sumchecks_qrom
abbrev recursiveIvcPublicRoundBadChallenges := @RecursiveIvcPublicRowQrom.public_round_bad_challenges
abbrev recursiveIvcQuadraticBadChallenges := @RecursiveIvcPublicRowQrom.quadratic_bad_challenges
abbrev recursiveIvcTreeBudgetLt128 := @RecursiveIvcPublicRowQrom.treeBudget_lt_128
abbrev recursiveIvcExtractOutsideNodeFailures := @RecursiveIvcPublicRowQrom.extract_outside_node_failures
abbrev tooth_unabsorbed_public_row_sumcheck_forges_claim :=
  @RecursiveIvcPublicRowQrom.tooth_unabsorbed_public_row_sumcheck_forges_claim
abbrev tooth_dkt26_tree_budget_exceeds_target :=
  RecursiveIvcPublicRowQrom.tooth_dkt26_tree_budget_exceeds_target

#tooth_pair RecursiveIvcPublicRowQrom.quadratic_bad_challenges vs
  RecursiveIvcPublicRowQrom.tooth_unabsorbed_public_row_sumcheck_forges_claim

end Qsag.Top
end
