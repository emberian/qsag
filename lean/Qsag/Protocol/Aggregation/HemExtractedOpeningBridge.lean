module
/-
# Executable opening substitution for the Hem transcript checker

A decoder is a deterministic function of the public output and authenticated opening
values. Replacing these values by the online extractor changes an accepting check only
on the batched extraction-failure event. The measured bound is consumed directly;
there is no supplied Merkle cover. The decoder is an explicit interface, not a claim
that Rust transcript bytes or Fiat–Shamir challenges have been refined here.
-/
public import Qsag.Oracle.QromBatchMerkleExtraction
public import Qsag.Protocol.Aggregation.HemVerifierAcceptance
import all Qsag.Oracle.QromBatchMerkleExtraction
import all Qsag.Oracle.QromMeasuredMerkleExtraction
import all Qsag.Oracle.QromMeasuredQueryExperiment
import all Qsag.Protocol.Aggregation.HemVerifierAcceptance
import all Qsag.Oracle.MultiRoundFsQrom

public section
namespace Qsag
set_option autoImplicit false

abbrev MerkleOpeningValue (w : Nat) := BitVec w × List (BitVec w)

def claimedOpeningValues {cardX w : Nat} (slots : List (MerkleOpeningSlot cardX w))
    (x : Fin cardX) : List (Option (MerkleOpeningValue w)) :=
  slots.map (fun s => some ((s.readout x).leaf, (s.readout x).path))

def extractedOpeningValues {cardX w : Nat} (L : MerkleAddressLayout cardX w)
    (slots : List (MerkleOpeningSlot cardX w)) (H : Fin cardX → BitVec w)
    (xs : List (Fin cardX)) (x : Fin cardX) : List (Option (MerkleOpeningValue w)) :=
  slots.map (fun s => extractOnlineMerkleOpening (s.readout x).rt (merkleRecords L H xs)
    s.level (s.readout x).path.length (s.readout x).idx)

/-- Actual path and range checks, required before the decoder consumes claimed values. -/
def verifyOpeningBatch {cardX w : Nat} (L : MerkleAddressLayout cardX w)
    (slots : List (MerkleOpeningSlot cardX w)) (H : Fin cardX → BitVec w) (x : Fin cardX) : Bool :=
  slots.all (fun s => merkleOpeningShape L s.depth (s.readout x) &&
    decide (merkleRootFromPath (L.hash H) s.level (s.readout x).idx
      (s.readout x).leaf (s.readout x).path = (s.readout x).rt))

/-- Deterministic substitution: every checked opening is recovered outside failure. -/
theorem extractedOpeningValues_eq_claimed {cardX w : Nat} (L : MerkleAddressLayout cardX w)
    (slots : List (MerkleOpeningSlot cardX w)) (H : Fin cardX → BitVec w)
    (xs : List (Fin cardX)) (x : Fin cardX)
    (hv : verifyOpeningBatch L slots H x = true)
    (hf : batchMerkleFailure L slots H xs x = false) :
    extractedOpeningValues L slots H xs x = claimedOpeningValues slots x := by
  unfold extractedOpeningValues claimedOpeningValues
  apply List.map_congr_left
  intro s hs
  have hv' := List.all_eq_true.mp hv s hs
  have hf' : measuredMerkleFailure L s.level s.depth s.readout H xs x = false := by
    have hn : ¬ measuredMerkleFailure L s.level s.depth s.readout H xs x = true := by
      intro he
      have ha : batchMerkleFailure L slots H xs x = true := List.any_eq_true.mpr ⟨s, hs, he⟩
      rw [hf] at ha
      exact Bool.noConfusion ha
    exact Bool.eq_false_iff.mpr hn
  unfold measuredMerkleFailure at hf'
  rw [hv'] at hf'
  simpa only [Bool.true_and, Bool.not_eq_false', decide_eq_true_eq] using hf'

/-- The authenticated checker adapter. The decoder receives `some (leaf,path)` for each
    submitted opening; extractor failures remain `none` in the replacement run. -/
def verifyHemOpeningBatch {cardX w : Nat} (L : MerkleAddressLayout cardX w)
    (slots : List (MerkleOpeningSlot cardX w))
    (inst : HemWhirInstance QuarticGoldilocks)
    (decode : Fin cardX → List (Option (MerkleOpeningValue w)) →
      List (HemTranscriptRound QuarticGoldilocks))
    (H : Fin cardX → BitVec w) (x : Fin cardX) : Bool :=
  verifyOpeningBatch L slots H x && verifyHemAffineWhir inst (decode x (claimedOpeningValues slots x))

/-- Acceptance loss under replacing authenticated openings by extracted values. This
    conclusion quantifies any quantum adversary in the *measured* experiment. -/
theorem measured_hem_opening_substitution_bound {cardX w cardAnc Q : Nat}
    (A : QuantumAdv cardX w cardAnc Q) (L : MerkleAddressLayout cardX w)
    (slots : List (MerkleOpeningSlot cardX w))
    (hLevels : ∀ s ∈ slots, s.level + s.depth ≤ L.levels)
    (inst : HemWhirInstance QuarticGoldilocks)
    (decode : Fin cardX → List (Option (MerkleOpeningValue w)) →
      List (HemTranscriptRound QuarticGoldilocks)) :
    2 ^ w * measuredEventMass A (fun H xs x =>
      verifyHemOpeningBatch L slots inst decode H x &&
      !verifyHemAffineWhir inst (decode x (extractedOpeningValues L slots H xs x))) ≤
      batchMerkleCost Q slots * quantumExperimentTotal A := by
  apply Nat.le_trans (Nat.mul_le_mul_left (2 ^ w) (measuredEventMass_mono A _
    (batchMerkleFailure L slots) ?_))
  · exact measured_batch_merkle_extraction_failure_bound A L slots hLevels
  · intro H xs x h
    by_cases hf : batchMerkleFailure L slots H xs x = true
    · exact hf
    · have he := extractedOpeningValues_eq_claimed L slots H xs x
        ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp h).1).1 (Bool.eq_false_iff.mpr hf)
      rw [he] at h
      have hv := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp h).1).2
      have hn := ((Bool.and_eq_true _ _).mp h).2
      rw [hv] at hn
      exact Bool.noConfusion hn

/-- Direct quantitative consumer: the checked acceptance mass is bounded by acceptance
    on extracted data plus the derived Merkle budget. Bounding the first term still needs
    transcript/challenge sampling and the algebraic reduction. -/
theorem measured_hem_acceptance_from_extracted {cardX w cardAnc Q : Nat}
    (A : QuantumAdv cardX w cardAnc Q) (L : MerkleAddressLayout cardX w)
    (slots : List (MerkleOpeningSlot cardX w))
    (hLevels : ∀ s ∈ slots, s.level + s.depth ≤ L.levels)
    (inst : HemWhirInstance QuarticGoldilocks)
    (decode : Fin cardX → List (Option (MerkleOpeningValue w)) →
      List (HemTranscriptRound QuarticGoldilocks)) :
    2 ^ w * measuredEventMass A (fun H _ x => verifyHemOpeningBatch L slots inst decode H x) ≤
      2 ^ w * measuredEventMass A (fun H xs x =>
        verifyHemAffineWhir inst (decode x (extractedOpeningValues L slots H xs x))) +
      batchMerkleCost Q slots * quantumExperimentTotal A := by
  let acc := fun H (_ : List (Fin cardX)) x => verifyHemOpeningBatch L slots inst decode H x
  let ext := fun H xs x =>
    verifyHemAffineWhir inst (decode x (extractedOpeningValues L slots H xs x))
  let loss := fun H xs x => acc H xs x && !ext H xs x
  have hMono : measuredEventMass A acc ≤
      measuredEventMass A (fun H xs x => ext H xs x || loss H xs x) := by
    apply measuredEventMass_mono
    intro H xs x ha
    dsimp only [loss]
    rw [ha]
    cases ext H xs x <;> rfl
  have hUnion := measuredEventMass_union_le A ext loss
  have hBound := measured_hem_opening_substitution_bound A L slots hLevels inst decode
  have hSum := Nat.mul_le_mul_left (2 ^ w) (Nat.le_trans hMono hUnion)
  rw [Nat.mul_add] at hSum
  exact Nat.le_trans hSum (Nat.add_le_add_left hBound _)

/-- Actual coherent-run acceptance loss for adversaries whose query addresses are
    classical. Arbitrary quantum local computation is permitted by `hC`. -/
theorem classical_hem_opening_substitution_bound {cardX w cardAnc Q : Nat}
    (A : QuantumAdv cardX w cardAnc Q)
    (addr : (Fin cardX → BitVec w) → Nat → Fin cardX) (hC : ClassicalQueryAddresses A addr)
    (L : MerkleAddressLayout cardX w) (slots : List (MerkleOpeningSlot cardX w))
    (hLevels : ∀ s ∈ slots, s.level + s.depth ≤ L.levels)
    (inst : HemWhirInstance QuarticGoldilocks)
    (decode : Fin cardX → List (Option (MerkleOpeningValue w)) →
      List (HemTranscriptRound QuarticGoldilocks)) :
    2 ^ w * uniformOracleSum w cardX (fun H => QVec.queryMassOn (fun x =>
      verifyHemOpeningBatch L slots inst decode H x &&
      !verifyHemAffineWhir inst
        (decode x (extractedOpeningValues L slots H (classicalQueryLog addr H Q) x)))
      (runQuantumAdv A H)) ≤ batchMerkleCost Q slots * quantumExperimentTotal A := by
  rw [← measuredEventMass_classical A addr hC (fun H xs x =>
    verifyHemOpeningBatch L slots inst decode H x &&
    !verifyHemAffineWhir inst (decode x (extractedOpeningValues L slots H xs x)))]
  exact measured_hem_opening_substitution_bound A L slots hLevels inst decode

/-- The residual event has actual algebraic content for arbitrary batch arities and
    arbitrary stage tails: an invalid original coordinate and an accepted combined
    polynomial occur in the transcript decoded from the extracted opening values. -/
theorem hem_extracted_invalid_coordinate {cardX w : Nat}
    (L : MerkleAddressLayout cardX w) (slots : List (MerkleOpeningSlot cardX w))
    (inst : HemWhirInstance QuarticGoldilocks)
    (decode : Fin cardX → List (Option (MerkleOpeningValue w)) →
      List (HemTranscriptRound QuarticGoldilocks))
    (H : Fin cardX → BitVec w) (xs : List (Fin cardX)) (x : Fin cardX)
    (shifts : List QuarticGoldilocks) (weights : List (QuarticGoldilocks × QuarticGoldilocks))
    (decoded : List (List QuarticGoldilocks)) (rest : List (HemTranscriptRound QuarticGoldilocks))
    (hDom : inst.initDomainPts.Nodup) (hEnough : inst.initDegBound + 1 ≤ inst.initMinAgree)
    (hInvalid : ¬ HemStatementValid inst)
    (hAccept : verifyHemOpeningBatch L slots inst decode H x = true)
    (hNoFailure : batchMerkleFailure L slots H xs x = false)
    (hTranscript : decode x (extractedOpeningValues L slots H xs x) =
      .cascade shifts weights decoded :: rest) :
    ∃ i, i < inst.batchOracles.length ∧
      (∀ G : List QuarticGoldilocks,
        polyWitnessValid inst.initDomainPts inst.initMinAgree inst.initDegBound
          (inst.batchOracles.getD i (fun _ => CommRingOps.zero)) inst.initKernel
          (inst.batchClaims.getD i CommRingOps.zero) G = false) ∧
      ∃ P ∈ decoded, polyWitnessValid inst.initDomainPts inst.initMinAgree
        (inst.initDegBound + 1) (evalCascadeOracle inst.initDomainPts inst.batchOracles weights)
        inst.initKernel (evalCascadeClaim inst.batchClaims shifts weights) P = true := by
  have hParts := (Bool.and_eq_true _ _).mp hAccept
  have hEq := extractedOpeningValues_eq_claimed L slots H xs x hParts.1 hNoFailure
  have hCheck := hParts.2
  rw [← hEq, hTranscript] at hCheck
  exact verifyHemAffineWhir_invalid_coordinate inst shifts weights decoded rest
    hDom hEnough hInvalid hCheck

#verify_constructive
  Qsag.extractedOpeningValues_eq_claimed
  Qsag.measured_hem_opening_substitution_bound
  Qsag.measured_hem_acceptance_from_extracted
  Qsag.classical_hem_opening_substitution_bound
  Qsag.hem_extracted_invalid_coordinate
end Qsag
end
