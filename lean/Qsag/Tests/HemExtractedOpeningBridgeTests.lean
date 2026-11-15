module
public import Qsag.Protocol.Aggregation.QromSaltedMerkleStateRestoration
/- Executed, nonconstant decoder consuming openings and the actual Hem checker. -/
public import Qsag.Protocol.Aggregation.HemExtractedOpeningBridge
public import Qsag.Tests.OracleAndQrom
import all Qsag.Protocol.Aggregation.HemExtractedOpeningBridge
import all Qsag.Protocol.Aggregation.QromSaltedMerkleStateRestoration
import all Qsag.Oracle.Qrom
import all Qsag.Tests.OracleAndQrom
import all Qsag.Protocol.Aggregation.HemVerifierAcceptance
import all Qsag.Protocol.Aggregation.MultiRoundFsQrom

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

public section
namespace Qsag
/-- Explicit unsalted (`cardSalt = 1`) 4-address finite Canopy instance showing why omitting
    per-commitment salts enables a 0-online-query collision attack under 2 bits of offline advice. -/
def unsaltedFourAddressCanopy : SaltedCanopyLayout 1 4 1 where
  encode := fun _ _ _ u v =>
    ⟨u.toNat * 2 + v.toNat, by
      have hu := u.isLt
      have hv := v.isLt
      omega⟩
  decode := fun x =>
    some (0, 0, 0, BitVec.ofNat 1 (x.1 / 2), BitVec.ofNat 1 (x.1 % 2))
  levels := 1
  nodes := 1
  decode_sound := by
    intro x s l n u v h
    injection h with hEq
    rcases hEq with ⟨_, _, _, rfl, rfl⟩
    apply Fin.ext
    dsimp
    have hx := x.isLt
    have h1 : (BitVec.ofNat 1 (x.1 / 2)).toNat = x.1 / 2 := by
      rw [BitVec.toNat_ofNat]; omega
    have h2 : (BitVec.ofNat 1 (x.1 % 2)).toNat = x.1 % 2 := by
      rw [BitVec.toNat_ofNat]; omega
    rw [h1, h2]
    omega
  decode_encode := by
    intro s l n u v hl hn
    have hs : s = 0 := Fin.ext (by omega)
    have hl0 : l = 0 := by omega
    have hn0 : n = 0 := by omega
    subst hs hl0 hn0
    dsimp
    have hu := u.isLt
    have hv := v.isLt
    have hU : BitVec.ofNat 1 ((u.toNat * 2 + v.toNat) / 2) = u := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat]; omega
    have hV : BitVec.ofNat 1 ((u.toNat * 2 + v.toNat) % 2) = v := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat]; omega
    rw [hU, hV]

/-- `#tooth`: without fresh salting (`cardSalt = 1`), 2 bits of offline advice find an explicit
    oracle collision in 0 online queries on 100% (`8 / 8`) of 1-bit 3-address oracles. -/
theorem tooth_unsalted_canopy_preprocessed_collision :
    ∃ (A : PreprocessingGame.ClassicalAdvice 3 1 1 2 0 (Fin 3 × Fin 3)),
      PreprocessingGame.adviceWinCount A
        (fun H _ pair => PreprocessingGame.collisionWin H pair) = (2 ^ 1) ^ 3 ∧
      (∀ H : Fin 3 → BitVec 1, (A.run H 0).2 = 0) ∧
      unsaltedFourAddressCanopy.levels = 1 :=
  ⟨PreprocessingGame.storedCollision, PreprocessingGame.storedCollision_count,
   fun _ => rfl, rfl⟩


#tooth_pair saltedCanopy_fresh_salt_preprocessed_bound vs tooth_unsalted_canopy_preprocessed_collision
end Qsag
end
