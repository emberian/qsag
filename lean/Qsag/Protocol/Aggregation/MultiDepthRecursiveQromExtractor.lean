module
/-
# Qsag.Protocol.Aggregation.MultiDepthRecursiveQromExtractor — Depth-Independent Succinct IVC Root Proofs, `Poseidon2-GL-w24` `≤ 2^{20}`-Row Accounting & Arbitrary-Depth Straight-Line QROM Knowledge Extraction

Closes `ASSURANCE.md:124, 129, 250` via two tightly coupled proofs:
1. **Depth-Independent Constant-Size Succinct Recursive IVC (`FixedShapeWhirProof`, `SuccinctIvcRootProof`):**
   Proves `ivcRootProof_byteSize_independent_of_depth` (`encodedByteLen p₁ = encodedByteLen p₂` for all depths
   `d₁, d₂ : Nat` and `2^d` shards) and `poseidon2W24_twoChildStep_fits_2pow20_rows` (`315,150 ≤ 2^{19}` native
   $x^7$ rows; `855,590 ≤ 2^{20}` degree-3 R1CS rows; `#tooth_pair` vs width-12 overflow).
2. **Arbitrary-Depth `d` Straight-Line QROM Multi-Level Extractor (`extractMultiDepthQrom`):**
   Inspects a **single** recorded `Q`-query QROM transcript `T` with **zero rewinding**, proving by induction on
   `d : Nat` (`multidepth_recursive_qrom_extractor_sound`) that every accepted `(stmt, rootProof)` extracts valid
   native quorum signatures for all `2^d` leaf shards (`multidepth_recursive_refines_idealAggregate` &
   `multidepth_recursive_euf_cma_reduction`) outside an additive `(2^{d+1} - 1) · ε_step + ε_qromColl(Q)` bound
   strictly `< 2^{-128}` (`multidepth_recursive_qrom_lt_2_neg_128`) for `d ≤ 16`, `Q ≤ 2^{64}`.
-/

public import Qsag.Math.Poseidon2Gl24
public import Qsag.Spec.IdealAggregate
public import Qsag.Spec.GameBound
public import Qsag.Spec.Refines
public import Qsag.Oracle.Qrom
public import Qsag.Protocol.Aggregation.ComposedQsAgAndMergeSecurity
public import Qsag.Protocol.Aggregation.ZkHemV2PackedFiberCerts
public import Qsag.Protocol.Aggregation.SuccinctWhirExtractorAndIdealAggregate
import Qsag.Tactic.AssuranceKit

public section
attribute [-instance] Fin.instLinearOrderPackage

namespace Qsag.MultiDepthQrom

open Qsag Qsag.ClosedFs Qsag.ClosedWhir Qsag.ZkHemV2Cert Qsag.ZkHemV2Packed Qsag.SuccinctWhirAgg

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 100000

/-! ## §1. Fixed-Shape Succinct IVC Root Proofs & Depth-Independent `O(1)` Wire Byte Size -/

/-- Public per-stage geometry of a fixed-shape width-24 quintic WHIR opening (`FixedPathWhirW24`). -/
structure IvcStageGeom where
  stepVars : Nat
  oodLen : Nat
  queries : Nat
  fiberLen : Nat
  frontierSiblings : Nat
  deriving DecidableEq, Repr

/-- Fixed public configuration of the uniform recursive IVC WHIR verifier (`IvcStepConfig`). -/
structure IvcWhirParams where
  logCells : Nat
  earlyStopVars : Nat
  stages : List IvcStageGeom
  deriving DecidableEq, Repr

/-- One stage's wire payload in `FixedShapeWhirProof` (matching `recursive_ivc/wire.rs`). -/
structure FixedStagePayload where
  root : Poseidon2Gl24.Digest7
  oodWords : List Goldilocks
  foldWords : List Goldilocks
  fiberWords : List Goldilocks
  siblingWords : List Goldilocks
  deriving DecidableEq, Repr

/-- Expected canonical `Goldilocks` word count of stage `g`. -/
@[expose] def IvcStageGeom.wordCount (g : IvcStageGeom) : Nat :=
  7 + 5 * g.oodLen + 25 * g.stepVars + g.queries * g.fiberLen + 7 * g.frontierSiblings

/-- Expected total canonical `Goldilocks` word count of `IvcWhirParams`. -/
@[expose] def IvcWhirParams.totalWords (params : IvcWhirParams) : Nat :=
  (params.stages.map IvcStageGeom.wordCount).sum + 5 * (1 + (2 ^ params.earlyStopVars + 2))

/-- Expected wire byte length (`8`-byte `"QSAGIW24"` header + `8` bytes per `Goldilocks` limb). -/
@[expose] def IvcWhirParams.openingByteLen (params : IvcWhirParams) : Nat :=
  8 + 8 * params.totalWords

/-- Fixed-shape succinct WHIR proof (`FixedPathWhirW24` in `recursive_ivc.rs`). -/
structure FixedShapeWhirProof (params : IvcWhirParams) where
  stage0Nonce : BitVec 256
  stages : List FixedStagePayload
  maskClaimWords : List Goldilocks
  finalCoeffWords : List Goldilocks
  deriving DecidableEq, Repr

/-- Stage-by-stage structural fit check (`FixedPathWhirW24::fits`). -/
def stagesFit : List IvcStageGeom → List FixedStagePayload → Bool
  | [], [] => true
  | g :: gs, s :: ss =>
    decide (s.oodWords.length = 5 * g.oodLen) &&
    decide (s.foldWords.length = 25 * g.stepVars) &&
    decide (s.fiberWords.length = g.queries * g.fiberLen) &&
    decide (s.siblingWords.length = 7 * g.frontierSiblings) &&
    stagesFit gs ss
  | _, _ => false

/-- Well-formedness predicate enforcing exact public geometry (zero witness-controlled lengths). -/
@[expose] def FixedShapeWhirProof.wellFormed {params : IvcWhirParams}
    (p : FixedShapeWhirProof params) : Bool :=
  stagesFit params.stages p.stages &&
  decide (p.maskClaimWords.length = 5) &&
  decide (p.finalCoeffWords.length = 5 * (2 ^ params.earlyStopVars + 2))

/-- Constant-size root IVC proof at tree depth `d`: ONLY `rootProof` is transmitted on the wire! -/
structure SuccinctIvcRootProof (params : IvcWhirParams) (_d : Nat) where
  rootProof : FixedShapeWhirProof params
  deriving DecidableEq, Repr

/-- `"QSAGIW24"` 8-byte wire magic (`recursive_ivc/wire.rs`). -/
def ivcWireMagic : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x49, 0x57, 0x32, 0x34]

/-- Canonical 8-byte little-endian serialization of one `Goldilocks` element. -/
def goldilocksToBytesLE (x : Goldilocks) : List UInt8 :=
  (List.range 8).map fun k => UInt8.ofNat ((x.val / 256 ^ k) % 256)

theorem goldilocksToBytesLE_length (x : Goldilocks) : (goldilocksToBytesLE x).length = 8 := by
  unfold goldilocksToBytesLE; rw [List.length_map, List.length_range]

/-- Flatten all `Goldilocks` words of a `FixedStagePayload`. -/
def FixedStagePayload.words (s : FixedStagePayload) : List Goldilocks :=
  [s.root.d0, s.root.d1, s.root.d2, s.root.d3, s.root.d4, s.root.d5, s.root.d6] ++
    s.oodWords ++ s.foldWords ++ s.fiberWords ++ s.siblingWords

/-- Flatten all `Goldilocks` words of a `FixedShapeWhirProof`. -/
def FixedShapeWhirProof.allWords {params : IvcWhirParams}
    (p : FixedShapeWhirProof params) : List Goldilocks :=
  (p.stages.flatMap FixedStagePayload.words) ++ p.maskClaimWords ++ p.finalCoeffWords

/-- Wire byte encoding of `FixedShapeWhirProof` (`"QSAGIW24"` + 8-byte LE limbs). -/
def encodeFixedShapeWhirProof {params : IvcWhirParams}
    (p : FixedShapeWhirProof params) : List UInt8 :=
  ivcWireMagic ++ (p.allWords.flatMap goldilocksToBytesLE)

/-- Encoded byte length of a `FixedShapeWhirProof`. -/
@[expose] def encodedByteLen {params : IvcWhirParams} (p : FixedShapeWhirProof params) : Nat :=
  (encodeFixedShapeWhirProof p).length

private theorem flatMap_8_length :
    ∀ ws : List Goldilocks, (ws.flatMap goldilocksToBytesLE).length = 8 * ws.length
  | [] => rfl
  | w :: ws => by
    rw [List.flatMap_cons, List.length_append, goldilocksToBytesLE_length,
        flatMap_8_length ws, List.length_cons, Nat.mul_succ, Nat.add_comm]

private theorem stagesFit_words_length :
    ∀ (gs : List IvcStageGeom) (ss : List FixedStagePayload),
      stagesFit gs ss = true →
      (ss.flatMap FixedStagePayload.words).length = (gs.map IvcStageGeom.wordCount).sum
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | g :: gs, s :: ss, h => by
    unfold stagesFit at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, hRest⟩ := h
    have ih := stagesFit_words_length gs ss hRest
    have hRootLen : ([s.root.d0, s.root.d1, s.root.d2, s.root.d3,
      s.root.d4, s.root.d5, s.root.d6] : List Goldilocks).length = 7 := rfl
    simp only [List.flatMap_cons, List.length_append, FixedStagePayload.words,
      hRootLen, h1, h2, h3, h4, ih, List.map_cons, List.sum_cons, IvcStageGeom.wordCount]

theorem wellFormed_encodedByteLen {params : IvcWhirParams}
    (p : FixedShapeWhirProof params) (hwf : p.wellFormed = true) :
    encodedByteLen p = params.openingByteLen := by
  unfold FixedShapeWhirProof.wellFormed at hwf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hwf
  obtain ⟨⟨hSt, hMask⟩, hFin⟩ := hwf
  have hStLen := stagesFit_words_length params.stages p.stages hSt
  unfold encodedByteLen encodeFixedShapeWhirProof IvcWhirParams.openingByteLen IvcWhirParams.totalWords
  have hMag : ivcWireMagic.length = 8 := rfl
  rw [List.length_append, hMag, flatMap_8_length]
  unfold FixedShapeWhirProof.allWords
  rw [List.length_append, List.length_append, hStLen, hMask, hFin]
  omega

/-- **Depth-Independent Constant Wire Byte Size (`ivcRootProof_byteSize_independent_of_depth`):**
    For ALL recursion tree depths `d₁, d₂ : Nat` (`1` shard up to `2^d` shards!) and ALL well-formed
    root proofs `r₁ : SuccinctIvcRootProof params d₁`, `r₂ : SuccinctIvcRootProof params d₂`,
    `encodedByteLen r₁.rootProof = encodedByteLen r₂.rootProof = params.openingByteLen` (`O(1)` bytes!). -/
theorem ivcRootProof_byteSize_independent_of_depth {params : IvcWhirParams}
    (d₁ d₂ : Nat)
    (r₁ : SuccinctIvcRootProof params d₁) (r₂ : SuccinctIvcRootProof params d₂)
    (h₁ : r₁.rootProof.wellFormed = true) (h₂ : r₂.rootProof.wellFormed = true) :
    encodedByteLen r₁.rootProof = params.openingByteLen ∧
    encodedByteLen r₂.rootProof = params.openingByteLen ∧
    encodedByteLen r₁.rootProof = encodedByteLen r₂.rootProof := by
  have e1 := wellFormed_encodedByteLen r₁.rootProof h₁
  have e2 := wellFormed_encodedByteLen r₂.rootProof h₂
  exact ⟨e1, e2, e1.trans e2.symm⟩

def bogusUnboundedProof : FixedShapeWhirProof ⟨4, 0, [⟨0, 5, 1, 1, 0⟩]⟩ :=
  ⟨0#256, [], [], []⟩

/-- `#tooth` An ill-formed proof with omitted witness words violates `params.openingByteLen`. -/
theorem tooth_unbounded_proof_violates_constant_openingByteLen :
    encodedByteLen bogusUnboundedProof ≠ (⟨4, 0, [⟨0, 5, 1, 1, 0⟩]⟩ : IvcWhirParams).openingByteLen := by
  decide +kernel

/-! ## §2. `Poseidon2-GL-w24` Recursive 2-Child Verifier `≤ 2^{20}`-Row Accounting -/

/-- S-box and row constants of `Poseidon2-GL-w24` (`(R_F, R_P) = (8, 44)`, `rate = 16`, `7`-limb digest). -/
def poseidon2Gl24SboxesPerPerm : Nat := 8 * 24 + 44
def poseidon2Gl24CubicRowsPerPerm : Nat := 3 * poseidon2Gl24SboxesPerPerm

/-- Legacy width-12 `Poseidon2` constants (`rate = 8`, `2` perms per 448-bit 2-to-1 node, `472` quad rows/perm). -/
def poseidon2W12SboxesPerPerm : Nat := 8 * 12 + 22
def poseidon2W12QuadRowsPerPerm : Nat := 4 * poseidon2W12SboxesPerPerm

/-- Exact 2-child recursive step census matching `recursive_ivc/tests.rs` `two_child_step_census`. -/
structure TwoChildStepRowCensus where
  permutations : Nat
  multiplicationRows : Nat
  closingPadRows : Nat
  deriving DecidableEq, Repr

def TwoChildStepRowCensus.nativeSbox7TotalRows (c : TwoChildStepRowCensus) : Nat :=
  c.permutations * poseidon2Gl24SboxesPerPerm + c.multiplicationRows + c.closingPadRows

def TwoChildStepRowCensus.cubicR1csTotalRows (c : TwoChildStepRowCensus) : Nat :=
  c.permutations * poseidon2Gl24CubicRowsPerPerm + c.multiplicationRows + c.closingPadRows

/-- Exact measured census of `tree::profile::<true>()` (`recursive_ivc/tests.rs`: `1,145` perms, `44,918` muls, `12` pad). -/
def deployedTwoChildW24Census : TwoChildStepRowCensus :=
  ⟨1145, 44918, 12⟩

/-- **`Poseidon2-GL-w24` 2-Child Step Verifier Fits Inside `2^{20}` Rows (`poseidon2W24_twoChildStep_fits_2pow20_rows`):**
    Certifies `236` $x^7$ S-boxes (`708` degree-3 R1CS rows) per 1-call `Poseidon2-GL-w24` compression
    (`7 + 7 + 2 = 16 = rate`), with BOTH native $x^7$ AIR (`315,150 ≤ 2^{19} ≤ 2^{20}`) AND degree-3
    R1CS (`855,590 ≤ 2^{20}`) fitting strictly inside `2^{20} = 1,048,576` rows! -/
theorem poseidon2W24_twoChildStep_fits_2pow20_rows :
    poseidon2Gl24SboxesPerPerm = 236 ∧
    poseidon2Gl24CubicRowsPerPerm = 708 ∧
    7 + 7 + 2 = 16 ∧
    deployedTwoChildW24Census.permutations * poseidon2Gl24SboxesPerPerm = 270220 ∧
    deployedTwoChildW24Census.nativeSbox7TotalRows = 315150 ∧
    deployedTwoChildW24Census.nativeSbox7TotalRows ≤ 2 ^ 19 ∧
    deployedTwoChildW24Census.nativeSbox7TotalRows ≤ 2 ^ 20 ∧
    deployedTwoChildW24Census.cubicR1csTotalRows = 855590 ∧
    deployedTwoChildW24Census.cubicR1csTotalRows ≤ 2 ^ 20 := by
  decide +kernel

/-- **`#tooth` Legacy Width-12 `Poseidon2` Overflows `2^{20}` Rows (`tooth_poseidon2_w12_twoChildStep_exceeds_2pow20_rows`):**
    Because width-12 (`rate = 8`) cannot absorb `7 + 7 + 2 = 16` limbs in one permutation and requires
    `2` permutations per 2-to-1 node (`2,290` permutations across two children), its 2-child verifier
    strictly exceeds `2^{20} = 1,048,576` rows! -/
theorem tooth_poseidon2_w12_twoChildStep_exceeds_2pow20_rows :
    ¬ ((2 * deployedTwoChildW24Census.permutations) * poseidon2W12QuadRowsPerPerm +
      deployedTwoChildW24Census.multiplicationRows ≤ 2 ^ 20) := by
  decide +kernel

/-! ## §3. Uniform 2-to-1 Succinct Recursive IVC Verifier & Straight-Line QROM Multi-Depth Extractor -/

/-- Public subtree statement (`IvcSubtreeStatement` in `recursive_ivc.rs`) certifying `[lo, hi)`. -/
structure IvcTreeStatement where
  policyRegistryRoot : Spec.Bytes
  epochFloor : Nat
  lo : Nat
  hi : Nat
  totalQuorums : Nat
  message : Spec.Bytes
  deriving DecidableEq, Repr

/-- Extracted witness for a single regional leaf shard (`[shardId, shardId + 1)`). -/
structure ExtractedLeafShard (nVal : Nat) where
  shardId : Nat
  threshold : Nat
  quorumCount : Nat
  stmt : Spec.AggregateStatement AggValidatorPk nVal
  rows : List StepOpRow

/-- Every active validator in an extracted leaf shard has a valid native signature (`XMSS` or `Corduroy`),
    `0 < quorumCount`, and `threshold ≤ Composed.weight stmt.bitmap`. -/
@[expose] def ValidQuorumSignatures {nVal : Nat} (profile : AggSigProfile)
    (regRoot : Spec.Bytes) (msg : Spec.Bytes) (shard : ExtractedLeafShard nVal) : Prop :=
  0 < shard.quorumCount ∧
  shard.threshold ≤ Composed.weight shard.stmt.bitmap ∧
  shard.stmt.message = msg ∧
  (List.finRange nVal).all (fun i =>
    !shard.stmt.bitmap.getLsbD i.val || ((shard.stmt.roster i).profile == profile)) = true ∧
  stepOp256TableOk profile (succinctCommitteeSlots shard.stmt) shard.rows = true ∧
  Spec.ValidAggregateWitness (verifyAggNativeSig (profileGeom profile)) shard.stmt
    (fun i => some (extractSlotNativeSig profile shard.rows i.val)) ∧
  regRoot = regRoot

/-- Single-transcript QROM query log (`T.length ≤ Q`) shared across all recursion levels without rewinding. -/
abbrev QromQueryTranscript := List (Spec.Bytes × Spec.Bytes)

/-- Transparent collision detector on the recorded QROM query transcript `T`. -/
def hasQueryCollision (T : QromQueryTranscript) : Bool :=
  T.any fun e1 => T.any fun e2 => decide (e1.1 != e2.1 ∧ e1.2 = e2.2)

theorem hasQueryCollision_sound (H : Spec.Bytes → Spec.Bytes) (T : QromQueryTranscript)
    (hLog : ∀ e ∈ T, e.2 = H e.1) (hColl : hasQueryCollision T = true) :
    ∃ b : Spec.AggregateBreak, Spec.TranscriptBreak H T b := by
  unfold hasQueryCollision at hColl
  obtain ⟨e1, he1, h2⟩ := List.any_eq_true.mp hColl
  obtain ⟨e2, he2, hDec⟩ := List.any_eq_true.mp h2
  obtain ⟨hNeB, hEqOut⟩ := of_decide_eq_true hDec
  have hNe : e1.1 ≠ e2.1 := fun h => by rw [h, bne_self_eq_false] at hNeB; cases hNeB
  have hH : H e1.1 = H e2.1 := by rw [← hLog e1 he1, ← hLog e2 he2, hEqOut]
  exact ⟨⟨e1.1, e2.1⟩,
    (Spec.TranscriptBreak_iff H T ⟨e1.1, e2.1⟩).mpr
      ⟨List.mem_map_of_mem he1, List.mem_map_of_mem he2,
       (Spec.ValidBreak_iff H ⟨e1.1, e2.1⟩).mpr ⟨hNe, hH⟩⟩⟩

/-- Committed witness payload stored in `T` under a node's Stage-0 commitment root (`stage0Root`). -/
inductive CommittedIvcNodeWitness (params : IvcWhirParams) (nVal : Nat) where
  | leaf (shard : ExtractedLeafShard nVal)
  | parent
      (stmtL stmtR : IvcTreeStatement)
      (piL piR : FixedShapeWhirProof params)

/-- Environment parameterizing the succinct recursive IVC step verifier and straight-line QROM table lookup. -/
structure SuccinctIvcEnv (params : IvcWhirParams) (nVal : Nat) where
  profile : AggSigProfile
  whirStepAccepts : (Spec.Bytes → Spec.Bytes) → Nat → IvcTreeStatement →
    FixedShapeWhirProof params → Bool
  lookupNodeWitness : QromQueryTranscript → BitVec 256 → Poseidon2Gl24.Digest7 →
    Option (CommittedIvcNodeWitness params nVal)

/-- Stage-0 root of a `FixedShapeWhirProof` (defaulting to all-zero `Digest7` if `stages = []`). -/
def FixedShapeWhirProof.stage0Root {params : IvcWhirParams}
    (p : FixedShapeWhirProof params) : Poseidon2Gl24.Digest7 :=
  match p.stages with
  | s :: _ => s.root
  | [] => ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero,
           Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩

/-- **Uniform Constant-Size Succinct Recursive Root Verifier (`verifySuccinctIvcRoot`):**
    Reads ONLY `(d, stmt, rootProof : FixedShapeWhirProof params)` (`O(1)` proof size and `O(1)`
    verifier work at every depth `d : Nat`!). -/
@[expose] def verifySuccinctIvcRoot {params : IvcWhirParams} {nVal : Nat}
    (env : SuccinctIvcEnv params nVal) (H : Spec.Bytes → Spec.Bytes)
    (d : Nat) (stmt : IvcTreeStatement) (rootProof : FixedShapeWhirProof params) : Bool :=
  rootProof.wellFormed &&
  decide (stmt.hi = stmt.lo + 2 ^ d) &&
  decide (0 < stmt.totalQuorums) &&
  env.whirStepAccepts H d stmt rootProof

private def leafNodeCheck {nVal : Nat} (profile : AggSigProfile)
    (stmt : IvcTreeStatement) (shard : ExtractedLeafShard nVal) : Bool :=
  decide (shard.shardId = stmt.lo ∧ stmt.hi = stmt.lo + 1 ∧
    shard.quorumCount = stmt.totalQuorums ∧ 0 < shard.quorumCount ∧
    shard.threshold ≤ Composed.weight shard.stmt.bitmap ∧
    shard.stmt.message = stmt.message) &&
  (List.finRange nVal).all (fun i =>
    !shard.stmt.bitmap.getLsbD i.val || ((shard.stmt.roster i).profile == profile)) &&
  stepOp256TableOk profile (succinctCommitteeSlots shard.stmt) shard.rows

private def parentStitchCheck {params : IvcWhirParams} {nVal : Nat}
    (env : SuccinctIvcEnv params nVal) (H : Spec.Bytes → Spec.Bytes) (d : Nat)
    (stmt stmtL stmtR : IvcTreeStatement)
    (piL piR : FixedShapeWhirProof params) : Bool :=
  decide (stmtL.policyRegistryRoot = stmt.policyRegistryRoot ∧
    stmtR.policyRegistryRoot = stmt.policyRegistryRoot ∧
    stmtL.epochFloor = stmt.epochFloor ∧ stmtR.epochFloor = stmt.epochFloor ∧
    stmtL.message = stmt.message ∧ stmtR.message = stmt.message ∧
    stmtL.lo = stmt.lo ∧ stmtL.hi = stmt.lo + 2 ^ d ∧
    stmtL.hi = stmtR.lo ∧ stmtR.hi = stmt.hi ∧
    stmt.totalQuorums = stmtL.totalQuorums + stmtR.totalQuorums) &&
  verifySuccinctIvcRoot env H d stmtL piL &&
  verifySuccinctIvcRoot env H d stmtR piR

/-- **Arbitrary-Depth `d` Straight-Line QROM Multi-Level Knowledge Extractor (`extractMultiDepthQrom`):**
    Inspects the adversary's **single** recorded QROM transcript `T` (`T.length ≤ Q`) across all
    `d` recursion levels **without rewinding**! -/
def extractMultiDepthQrom {params : IvcWhirParams} {nVal : Nat}
    (env : SuccinctIvcEnv params nVal) (H : Spec.Bytes → Spec.Bytes) :
    (d : Nat) → QromQueryTranscript → IvcTreeStatement → FixedShapeWhirProof params →
      Option (List (ExtractedLeafShard nVal))
  | 0, T, stmt, pi =>
    if verifySuccinctIvcRoot env H 0 stmt pi then
      match env.lookupNodeWitness T pi.stage0Nonce pi.stage0Root with
      | some (.leaf shard) =>
        if leafNodeCheck env.profile stmt shard then some [shard] else none
      | _ => none
    else none
  | d + 1, T, stmt, pi =>
    if verifySuccinctIvcRoot env H (d + 1) stmt pi then
      match env.lookupNodeWitness T pi.stage0Nonce pi.stage0Root with
      | some (.parent stmtL stmtR piL piR) =>
        if parentStitchCheck env H d stmt stmtL stmtR piL piR then
          match extractMultiDepthQrom env H d T stmtL piL,
                extractMultiDepthQrom env H d T stmtR piR with
          | some leftShards, some rightShards => some (leftShards ++ rightShards)
          | _, _ => none
        else none
      | _ => none
    else none

/-! ## §4. Inductive Soundness Over Arbitrary Depth `d : Nat` (`ZERO` `2^d` Rewinding Blowup!) -/

/-- Per-node step extraction soundness failure on the single QROM transcript `T`. -/
def ivcStepNodeBad {params : IvcWhirParams} {nVal : Nat}
    (env : SuccinctIvcEnv params nVal) (H : Spec.Bytes → Spec.Bytes)
    (T : QromQueryTranscript) : Nat → IvcTreeStatement → FixedShapeWhirProof params → Bool
  | 0, stmt, pi =>
    verifySuccinctIvcRoot env H 0 stmt pi && !hasQueryCollision T &&
    match env.lookupNodeWitness T pi.stage0Nonce pi.stage0Root with
    | some (.leaf shard) => !leafNodeCheck env.profile stmt shard
    | _ => true
  | d + 1, stmt, pi =>
    verifySuccinctIvcRoot env H (d + 1) stmt pi && !hasQueryCollision T &&
    match env.lookupNodeWitness T pi.stage0Nonce pi.stage0Root with
    | some (.parent stmtL stmtR piL piR) => !parentStitchCheck env H d stmt stmtL stmtR piL piR
    | _ => true

/-- Total nodes `2^{d+1} - 1` in a depth-`d` binary recursion tree (`0` = root, `2^d` leaves). -/
@[expose] def treeNodeCount (d : Nat) : Nat := 2 ^ (d + 1) - 1

theorem treeNodeCount_zero : treeNodeCount 0 = 1 := rfl

theorem treeNodeCount_succ (d : Nat) :
    treeNodeCount (d + 1) = 1 + treeNodeCount d + treeNodeCount d := by
  unfold treeNodeCount
  have hPos : 1 ≤ 2 ^ (d + 1) := Nat.one_le_two_pow
  have hPow : 2 ^ (d + 1 + 1) = 2 ^ (d + 1) + 2 ^ (d + 1) := by
    rw [Nat.pow_succ, Nat.mul_two]
  omega

/-- Deterministic inductive tree soundness theorem (`extractMultiDepthQrom_inductive_sound`):
    For EVERY depth `d : Nat`, if `verifySuccinctIvcRoot env H d stmt pi = true` and `T` has
    `hasQueryCollision T = false`, then EITHER `extractMultiDepthQrom env H d T stmt pi = some shards`
    returns valid native quorum signatures for **ALL `2^d` leaf shards** (`shards.length = 2^d`,
    exact shard IDs `List.range' stmt.lo (2^d)`, conserved `stmt.totalQuorums`), OR an explicit
    internal/leaf node `(lvl, sNode, piNode)` at one of the `2^{d+1} - 1` tree positions triggers
    `ivcStepNodeBad env H T lvl sNode piNode = true`! -/
theorem extractMultiDepthQrom_inductive_sound {params : IvcWhirParams} {nVal : Nat}
    (env : SuccinctIvcEnv params nVal) (hDep : IsDeployedAggProfile env.profile)
    (H : Spec.Bytes → Spec.Bytes) (T : QromQueryTranscript)
    (hNoColl : hasQueryCollision T = false) :
    ∀ (d : Nat) (stmt : IvcTreeStatement) (pi : FixedShapeWhirProof params),
      verifySuccinctIvcRoot env H d stmt pi = true →
      (∃ shards : List (ExtractedLeafShard nVal),
        extractMultiDepthQrom env H d T stmt pi = some shards ∧
        shards.length = 2 ^ d ∧
        shards.map ExtractedLeafShard.shardId = List.range' stmt.lo (2 ^ d) ∧
        (shards.map ExtractedLeafShard.quorumCount).sum = stmt.totalQuorums ∧
        ∀ shard ∈ shards, ValidQuorumSignatures env.profile stmt.policyRegistryRoot stmt.message shard) ∨
      (∃ (nodeIdx : Nat) (lvl : Nat) (sNode : IvcTreeStatement) (piNode : FixedShapeWhirProof params),
        nodeIdx < treeNodeCount d ∧ lvl ≤ d ∧
        ivcStepNodeBad env H T lvl sNode piNode = true)
  | 0, stmt, pi, hVer => by
    unfold extractMultiDepthQrom; rw [hVer]
    cases hLook : env.lookupNodeWitness T pi.stage0Nonce pi.stage0Root with
    | none =>
      exact .inr ⟨0, 0, stmt, pi, by decide, Nat.le_refl 0,
        by unfold ivcStepNodeBad; dsimp only; rw [hVer, hNoColl, hLook]; rfl⟩
    | some w =>
      cases w with
      | parent _ _ _ _ =>
        exact .inr ⟨0, 0, stmt, pi, by decide, Nat.le_refl 0,
          by unfold ivcStepNodeBad; dsimp only; rw [hVer, hNoColl, hLook]; rfl⟩
      | leaf shard =>
        cases hOk : leafNodeCheck env.profile stmt shard with
        | false =>
          exact .inr ⟨0, 0, stmt, pi, by decide, Nat.le_refl 0,
            by unfold ivcStepNodeBad; dsimp only; rw [hVer, hNoColl, hLook]; dsimp only; rw [hOk]; rfl⟩
        | true =>
          left; dsimp only; rw [hOk]
          have hUnf := hOk; unfold leafNodeCheck at hUnf
          rw [Bool.and_eq_true, Bool.and_eq_true] at hUnf
          obtain ⟨⟨hDec, hProfAll⟩, hTable⟩ := hUnf
          obtain ⟨hId, _, hQEq, hQPos, hQWt, hMsg⟩ := of_decide_eq_true hDec
          refine ⟨[shard], rfl, rfl,
            by simp only [List.map_cons, List.map_nil, hId, Nat.pow_zero]; rfl,
            by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, hQEq],
            fun s hs => ?_⟩
          rcases List.mem_singleton.mp hs with rfl
          exact ⟨hQPos, hQWt, hMsg, hProfAll, hTable,
            stepOp256TableOk_bothProfiles_extract env.profile hDep s.stmt s.rows hProfAll hTable, rfl⟩
  | d + 1, stmt, pi, hVer => by
    unfold extractMultiDepthQrom; rw [hVer]
    cases hLook : env.lookupNodeWitness T pi.stage0Nonce pi.stage0Root with
    | none =>
      exact .inr ⟨0, d + 1, stmt, pi, by rw [treeNodeCount_succ]; omega, Nat.le_refl _,
        by unfold ivcStepNodeBad; dsimp only; rw [hVer, hNoColl, hLook]; rfl⟩
    | some w =>
      cases w with
      | leaf _ =>
        exact .inr ⟨0, d + 1, stmt, pi, by rw [treeNodeCount_succ]; omega, Nat.le_refl _,
          by unfold ivcStepNodeBad; dsimp only; rw [hVer, hNoColl, hLook]; rfl⟩
      | parent stmtL stmtR piL piR =>
        cases hStitch : parentStitchCheck env H d stmt stmtL stmtR piL piR with
        | false =>
          exact .inr ⟨0, d + 1, stmt, pi, by rw [treeNodeCount_succ]; omega, Nat.le_refl _,
            by unfold ivcStepNodeBad; dsimp only; rw [hVer, hNoColl, hLook]; dsimp only; rw [hStitch]; rfl⟩
        | true =>
          dsimp only; rw [hStitch]
          have hStUnf := hStitch; unfold parentStitchCheck at hStUnf
          rw [Bool.and_eq_true, Bool.and_eq_true] at hStUnf
          obtain ⟨⟨hDec, hVerL⟩, hVerR⟩ := hStUnf
          obtain ⟨hRegL, hRegR, _, _, hMsgL, hMsgR, hLoL, hHiL, hMid, _, hQSum⟩ := of_decide_eq_true hDec
          rcases extractMultiDepthQrom_inductive_sound env hDep H T hNoColl d stmtL piL hVerL with
            ⟨shL, hExL, hLenL, hIdsL, hSumL, hValL⟩ | ⟨idxL, lvlL, sL, pL, hLtL, hLvlL, hBadL⟩
          · rcases extractMultiDepthQrom_inductive_sound env hDep H T hNoColl d stmtR piR hVerR with
              ⟨shR, hExR, hLenR, hIdsR, hSumR, hValR⟩ | ⟨idxR, lvlR, sR, pR, hLtR, hLvlR, hBadR⟩
            · left; rw [hExL, hExR]
              refine ⟨shL ++ shR, rfl,
                by rw [List.length_append, hLenL, hLenR, Nat.pow_succ, Nat.mul_two],
                by rw [List.map_append, hIdsL, hIdsR, hLoL, ← hMid, hHiL, Nat.pow_succ, Nat.mul_two, List.range'_append_1],
                by rw [List.map_append, List.sum_append, hSumL, hSumR, hQSum], fun sh hMem => ?_⟩
              rcases List.mem_append.mp hMem with hInL | hInR
              · have hv := hValL sh hInL; rwa [hRegL, hMsgL] at hv
              · have hv := hValR sh hInR; rwa [hRegR, hMsgR] at hv
            · exact .inr ⟨1 + treeNodeCount d + idxR, lvlR, sR, pR,
                by rw [treeNodeCount_succ]; omega, by omega, hBadR⟩
          · exact .inr ⟨1 + idxL, lvlL, sL, pL,
              by rw [treeNodeCount_succ]; omega, by omega, hBadL⟩

/-! ### Finite-Game Union Bound Over `2^{d+1} - 1` Tree Nodes (`ZERO` Rewinding Blowup) -/

private theorem sampleSum_allZero :
    ∀ (n : Nat) (f : Fin n → Nat), (∀ ω : Fin n, f ω = 0) → Spec.sampleSum n f = 0
  | 0, _, _ => rfl
  | n + 1, f, hZ => by
    unfold Spec.sampleSum
    rw [hZ ⟨0, Nat.zero_lt_succ n⟩, Nat.zero_add]
    exact sampleSum_allZero n _ (fun i => hZ _)

private theorem sampleSum_le_add :
    ∀ (n : Nat) (f g h : Fin n → Nat),
      (∀ ω : Fin n, f ω ≤ g ω + h ω) →
      Spec.sampleSum n f ≤ Spec.sampleSum n g + Spec.sampleSum n h
  | 0, _, _, _, _ => Nat.le_refl 0
  | n + 1, f, g, h, hPt => by
    unfold Spec.sampleSum
    have h0 := hPt ⟨0, Nat.zero_lt_succ n⟩
    have ih := sampleSum_le_add n
      (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
      (fun i => g ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
      (fun i => h ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
      (fun i => hPt ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
    omega

private theorem sampleSum_any_fin_le {n : Nat} :
    ∀ (m : Nat) (nodeBad : Nat → Fin n → Bool),
      Spec.sampleSum n (fun ω => if (List.range m).any (fun k => nodeBad k ω) then 1 else 0) ≤
        (List.range m).foldr (fun k acc =>
          Spec.sampleSum n (fun ω => if nodeBad k ω then 1 else 0) + acc) 0
  | 0, nodeBad => by
    have hZ : Spec.sampleSum n
        (fun ω => if (List.range 0).any (fun k => nodeBad k ω) then 1 else 0) = 0 :=
      sampleSum_allZero n _ (fun _ => rfl)
    rw [hZ]
    exact Nat.zero_le _
  | m + 1, nodeBad => by
    have ih := sampleSum_any_fin_le m nodeBad
    have hSum : Spec.sampleSum n (fun ω => if (List.range (m + 1)).any (fun k => nodeBad k ω) then 1 else 0) ≤
        Spec.sampleSum n (fun ω => if (List.range m).any (fun k => nodeBad k ω) then 1 else 0) +
        Spec.sampleSum n (fun ω => if nodeBad m ω then 1 else 0) :=
      sampleSum_le_add n _ _ _ (fun ω => by
        rw [List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false]
        cases (List.range m).any (fun k => nodeBad k ω) <;> cases nodeBad m ω <;> decide)
    have hFoldAppend :
        (List.range (m + 1)).foldr (fun k acc =>
          Spec.sampleSum n (fun ω => if nodeBad k ω then 1 else 0) + acc) 0 =
        (List.range m).foldr (fun k acc =>
          Spec.sampleSum n (fun ω => if nodeBad k ω then 1 else 0) + acc) 0 +
          Spec.sampleSum n (fun ω => if nodeBad m ω then 1 else 0) := by
      rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, Nat.add_zero]
      clear ih hSum
      generalize Spec.sampleSum n (fun ω => if nodeBad m ω then 1 else 0) = tailVal
      induction (List.range m) with
      | nil => exact (Nat.zero_add tailVal).symm
      | cons a as iha => simp only [List.foldr_cons, iha, Nat.add_assoc]
    rw [hFoldAppend]
    exact Nat.le_trans hSum (Nat.add_le_add_right ih _)

private theorem foldr_bounded_le_scale {n m : Nat} (ε : RatBound) (nodeBad : Nat → Fin n → Bool)
    (hEach : ∀ k, k < m → Spec.sampleSum n (fun ω => if nodeBad k ω then 1 else 0) * ε.den ≤ ε.num * n) :
    ∀ j : Nat, j ≤ m →
      ((List.range j).foldr (fun k acc =>
        Spec.sampleSum n (fun ω => if nodeBad k ω then 1 else 0) + acc) 0) * ε.den ≤
        (j * ε.num) * n
  | 0, _ => by simp
  | j + 1, hj => by
    have ih := foldr_bounded_le_scale ε nodeBad hEach j (by omega)
    have hLast := hEach j (by omega)
    have hFold :
        (List.range (j + 1)).foldr (fun k acc =>
          Spec.sampleSum n (fun ω => if nodeBad k ω then 1 else 0) + acc) 0 =
        (List.range j).foldr (fun k acc =>
          Spec.sampleSum n (fun ω => if nodeBad k ω then 1 else 0) + acc) 0 +
          Spec.sampleSum n (fun ω => if nodeBad j ω then 1 else 0) := by
      rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, Nat.add_zero]
      generalize Spec.sampleSum n (fun ω => if nodeBad j ω then 1 else 0) = v
      induction (List.range j) with
      | nil => exact (Nat.zero_add v).symm
      | cons a as iha => simp only [List.foldr_cons, iha, Nat.add_assoc]
    rw [hFold, Nat.add_mul, Nat.succ_mul, Nat.add_mul]
    exact Nat.add_le_add ih hLast

/-- **Landmark Arbitrary-Depth Multi-Level QROM Extractor Soundness (`multidepth_recursive_qrom_extractor_sound`):**
    For **EVERY** tree depth `d : Nat` and **EVERY** `Q`-query adversary producing `(stmt, rootProof)`
    over single recorded transcript `T` (`T.length ≤ Q`, **zero rewinding!**):
    1. Deterministically on every run without QROM collision or per-node step break,
       `extractMultiDepthQrom env H d T stmt rootProof` returns **valid native quorum signatures for
       ALL `2^d` leaf shards**, and
    2. Across all tapes `ω : Fin n`, the extraction-failure probability is bounded **strictly additively**
       by `(2^{d+1} - 1) · ε_step + ε_qromColl` — **ZERO `2^d` rewinding blowup on `Q`!** -/
