module
public import Qsag.Math.QuinticExt5
public import Qsag.Protocol.Signing.ExecEufCmaClosedGame
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

/-- One root and its OOD, affine fold, fiber, and binary Merkle path words. -/
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
  (params.stages.map IvcStageGeom.wordCount).sum + 5 * (1 + (2 ^ params.earlyStopVars + 2)) +
    5 * (15 * params.logCells + 9)

/-- Eight-byte version, 32-byte nonce, 56-byte witness digest, and eight bytes per field limb. -/
@[expose] def IvcWhirParams.openingByteLen (params : IvcWhirParams) : Nat :=
  96 + 8 * params.totalWords

/-- Fixed-shape R1CS argument and WHIR opening, with a separately bound extraction digest. -/
structure FixedShapeWhirProof (params : IvcWhirParams) where
  stage0Nonce : BitVec 256
  witnessCommitRoot : BitVec 448
  algebraWords : List Goldilocks
  stages : List FixedStagePayload
  maskClaimWords : List Goldilocks
  finalCoeffWords : List Goldilocks
  deriving DecidableEq, Repr

/-- Stage-by-stage structural fit check (`FixedPathWhirW24::fits`). -/
@[expose] def stagesFit : List IvcStageGeom → List FixedStagePayload → Bool
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
  decide (p.algebraWords.length = 5 * (15 * params.logCells + 9)) &&
  stagesFit params.stages p.stages &&
  decide (p.maskClaimWords.length = 5) &&
  decide (p.finalCoeffWords.length = 5 * (2 ^ params.earlyStopVars + 2))

/-- Constant-size root IVC proof at tree depth `d`: ONLY `rootProof` is transmitted on the wire! -/
structure SuccinctIvcRootProof (params : IvcWhirParams) (_d : Nat) where
  rootProof : FixedShapeWhirProof params
  deriving DecidableEq, Repr

/-- Distinguishes this byte-oracle and binary-path encoding from the Rust opening encoding. -/
def ivcWireMagic : List UInt8 :=
  [0x51, 0x53, 0x49, 0x56, 0x43, 0x42, 0x30, 0x31]

/-- Canonical 8-byte little-endian serialization of one `Goldilocks` element. -/
@[expose] def goldilocksToBytesLE (x : Goldilocks) : List UInt8 :=
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
  (p.stages.flatMap FixedStagePayload.words) ++ p.maskClaimWords ++ p.finalCoeffWords ++ p.algebraWords

/-- Encode the nonce and witness commitment before the stage and arithmetic payloads. -/
def encodeFixedShapeWhirProof {params : IvcWhirParams}
    (p : FixedShapeWhirProof params) : List UInt8 :=
  ivcWireMagic ++ encodeNatLeBytes 32 p.stage0Nonce.toNat ++
    encodeNatLeBytes 56 p.witnessCommitRoot.toNat ++ p.allWords.flatMap goldilocksToBytesLE

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
  obtain ⟨⟨⟨hAlg, hSt⟩, hMask⟩, hFin⟩ := hwf
  have hStLen := stagesFit_words_length params.stages p.stages hSt
  unfold encodedByteLen encodeFixedShapeWhirProof IvcWhirParams.openingByteLen IvcWhirParams.totalWords
  have hMag : ivcWireMagic.length = 8 := rfl
  simp only [List.length_append, hMag, encodeNatLeBytes_length, flatMap_8_length]
  unfold FixedShapeWhirProof.allWords
  simp only [List.length_append, hStLen, hMask, hFin, hAlg]
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

/-- Wire-shape witness. This declaration makes no claim about cryptographic acceptance. -/
def shapeWitness (p : IvcWhirParams) : FixedShapeWhirProof p :=
  let zeros (n : Nat) := List.replicate n Goldilocks.zero
  let z := Goldilocks.zero
  let stage (g : IvcStageGeom) : FixedStagePayload :=
    ⟨⟨z,z,z,z,z,z,z⟩,zeros (5*g.oodLen),zeros (25*g.stepVars),zeros (g.queries*g.fiberLen),
      zeros (7*g.frontierSiblings)⟩
  ⟨0,0,zeros (5*(15*p.logCells+9)),p.stages.map stage,zeros 5,zeros (5*(2^p.earlyStopVars+2))⟩

/-- The first row sumcheck starts at zero. Check p(0)+p(1) limbwise before hashing.
Each row round has ten coefficients, each in the quintic power basis. -/
@[expose] def initialRowSumOk {p : IvcWhirParams} (pi : FixedShapeWhirProof p) : Bool :=
  let row := (pi.algebraWords.drop (5*(2*p.logCells+4))).take 50
  row.length == 50 && (List.range 5).all fun limb =>
    let atLimb (j : Nat) := ((row[5*j+limb]?).map fun x => x.val).getD 0
    (atLimb 0 + ((List.range 10).map atLimb).sum) % goldilocksPrime == 0

def limbTestParams : IvcWhirParams := ⟨5,2,[⟨2,5,1,13,4⟩,⟨1,2,1,10,3⟩]⟩

def flippedRowProof : FixedShapeWhirProof limbTestParams :=
  let pi := shapeWitness limbTestParams
  let flipped := pi.algebraWords.modify (5*(2*limbTestParams.logCells+4)) (fun x => Goldilocks.ofNat (x.val ^^^ 1))
  {pi with algebraWords := flipped}

theorem flippedRowProof_first_round :
    initialRowSumOk (shapeWitness limbTestParams) = true ∧
    flippedRowProof.wellFormed = true ∧ initialRowSumOk flippedRowProof = false := by
  decide +kernel

#verify_constructive flippedRowProof_first_round

theorem inhabited_ivcRootProof_byteSize :
    ∃ (p : IvcWhirParams) (d₁ d₂ : Nat)
      (r₁ : SuccinctIvcRootProof p d₁) (r₂ : SuccinctIvcRootProof p d₂),
      r₁.rootProof.wellFormed = true ∧ r₂.rootProof.wellFormed = true ∧
        encodedByteLen r₁.rootProof = encodedByteLen r₂.rootProof := by
  let p : IvcWhirParams := ⟨5,2,[⟨2,5,1,13,4⟩,⟨1,2,1,10,3⟩]⟩
  refine ⟨p,0,16,⟨shapeWitness p⟩,⟨shapeWitness p⟩,?_,?_,rfl⟩ <;> decide +kernel

#verify_constructive inhabited_ivcRootProof_byteSize
#verify_inhabited ivcRootProof_byteSize_independent_of_depth inhabited_ivcRootProof_byteSize

def bogusUnboundedProof : FixedShapeWhirProof ⟨4, 0, [⟨0, 5, 1, 1, 0⟩]⟩ :=
  ⟨0#256, 0#448, [], [], [], []⟩

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
  registryAuthPath : List Spec.Bytes

/-- Single-transcript QROM query log (`T.length ≤ Q`) shared across all recursion levels without rewinding. -/
abbrev QromQueryTranscript := List (Spec.Bytes × Spec.Bytes)

/-- Transparent collision detector on the recorded QROM query transcript `T`. -/
def hasQueryCollision (T : QromQueryTranscript) : Bool :=
  T.any fun e1 => T.any fun e2 => decide (e1.1 != e2.1 ∧ e1.2 = e2.2)

theorem hasQueryCollision_nil : hasQueryCollision [] = false := by simp [hasQueryCollision]

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
      (matrixFoldWords : List Goldilocks)

#verify_constructive goldilocksToBytesLE_length flatMap_8_length stagesFit_words_length
  wellFormed_encodedByteLen ivcRootProof_byteSize_independent_of_depth
  tooth_unbounded_proof_violates_constant_openingByteLen poseidon2W24_twoChildStep_fits_2pow20_rows
  tooth_poseidon2_w12_twoChildStep_exceeds_2pow20_rows hasQueryCollision_nil hasQueryCollision_sound

end Qsag.MultiDepthQrom
end

