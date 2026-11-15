module
/- Executed, nonconstant decoder consuming openings and the actual Hem checker. -/
public import Qsag.Protocol.Aggregation.HemExtractedOpeningBridge
public import Qsag.Tests.QromMeasuredMerkleExtractionTests
import all Qsag.Protocol.Aggregation.HemExtractedOpeningBridge
import all Qsag.Oracle.QromBatchMerkleExtraction
import all Qsag.Tests.QromMeasuredMerkleExtractionTests
import all Qsag.Oracle.QromMeasuredMerkleExtraction
import all Qsag.Oracle.QromMeasuredQueryExperiment
import all Qsag.Protocol.Aggregation.HemVerifierAcceptance
import all Qsag.Oracle.MultiRoundFsQrom

public section
namespace Qsag
set_option autoImplicit false

def toyOpeningSlots : List (MerkleOpeningSlot 4 1) := [⟨0, 1, toyOpening⟩]

def toyHemDecode (_ : Fin 4) (values : List (Option (MerkleOpeningValue 1))) :
    List (HemTranscriptRound QuarticGoldilocks) :=
  if values = [some (0#1, [1#1])] then
    [.cascade [CommRingOps.zero] [(CommRingOps.zero, CommRingOps.one)] [[]], .finalQuery []]
  else []

def toyHemInstance : HemWhirInstance QuarticGoldilocks :=
  hemZeroOracleClaimInstance [CommRingOps.zero, CommRingOps.one] 0 2 []

/-- The decoder consumes extracted data: a missing opening rejects; the exact claimed
    opening accepts an invalid statement. The measured extraction loss is 0 for the query
    at the actual compression address, and 8/16 for the other address. -/
theorem toy_hem_substitution_execution :
    let honest := toyQueryAdv ⟨1, by decide⟩ (by decide)
    let guesser := toyQueryAdv ⟨0, by decide⟩ (by decide)
    verifyHemAffineWhir toyHemInstance (toyHemDecode ⟨0, by decide⟩ [none]) = false ∧
    verifyHemAffineWhir toyHemInstance
      (toyHemDecode ⟨0, by decide⟩ (claimedOpeningValues toyOpeningSlots ⟨0, by decide⟩)) = true ∧
    measuredEventMass honest (fun H _ x =>
      verifyHemOpeningBatch toyMerkleLayout toyOpeningSlots toyHemInstance toyHemDecode H x) = 8 ∧
    measuredEventMass honest (fun H xs x =>
      verifyHemOpeningBatch toyMerkleLayout toyOpeningSlots toyHemInstance toyHemDecode H x &&
      !verifyHemAffineWhir toyHemInstance
        (toyHemDecode x (extractedOpeningValues toyMerkleLayout toyOpeningSlots H xs x))) = 0 ∧
    measuredEventMass guesser (fun H xs x =>
      verifyHemOpeningBatch toyMerkleLayout toyOpeningSlots toyHemInstance toyHemDecode H x &&
      !verifyHemAffineWhir toyHemInstance
        (toyHemDecode x (extractedOpeningValues toyMerkleLayout toyOpeningSlots H xs x))) = 8 := by
  decide +kernel

/-- Repeating an opening preserves the failure event, while the conservative union budget
    doubles. This checks real multi-slot evaluation without claiming collision independence. -/
theorem toy_batch_duplicate_execution :
    let guesser := toyQueryAdv ⟨0, by decide⟩ (by decide)
    measuredEventMass guesser (batchMerkleFailure toyMerkleLayout (toyOpeningSlots ++ toyOpeningSlots)) = 8 ∧
    batchMerkleCost 1 (toyOpeningSlots ++ toyOpeningSlots) = 8 := by
  decide +kernel

theorem toyHemInstance_invalid : ¬ HemStatementValid toyHemInstance :=
  hemZeroOracleClaimInstance_invalid _ 0 2 [] (by decide) (by decide)

/-- The universal replacement theorem has a concrete decoder and inhabited adversary. -/
theorem toy_hem_substitution_bound_instance :
    let guesser := toyQueryAdv ⟨0, by decide⟩ (by decide)
    2 ^ 1 * measuredEventMass guesser (fun H xs x =>
      verifyHemOpeningBatch toyMerkleLayout toyOpeningSlots toyHemInstance toyHemDecode H x &&
      !verifyHemAffineWhir toyHemInstance
        (toyHemDecode x (extractedOpeningValues toyMerkleLayout toyOpeningSlots H xs x))) ≤
      batchMerkleCost 1 toyOpeningSlots * quantumExperimentTotal guesser := by
  exact measured_hem_opening_substitution_bound _ _ _
    (by intro s hs; simp only [toyOpeningSlots, List.mem_cons, List.not_mem_nil, or_false] at hs
        subst s; decide) _ _

#verify_constructive
  Qsag.toy_hem_substitution_execution
  Qsag.toy_batch_duplicate_execution
  Qsag.toy_hem_substitution_bound_instance
  Qsag.toyHemInstance_invalid
end Qsag
end
