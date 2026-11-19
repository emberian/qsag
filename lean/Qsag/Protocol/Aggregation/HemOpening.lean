module
public import Qsag.Protocol.Aggregation.HemRbrSoundness
public import Qsag.Oracle.Qrom
public import Qsag.Coding.Cwyz26
public import Qsag.Math.Tactic.CommRing
public import Qsag.Tactic.AssuranceKit
import Qsag.Protocol.Aggregation.MultiRoundFsQrom
import Qsag.Protocol.Aggregation.ConcreteSecurityBudget
import Qsag.Coding.GuruswamiSudan
import Qsag.Coding.ReedSolomon
import Qsag.Math.Counting
import Qsag.Math.CoeffPoly
import Qsag.Math.PolyRing
import Qsag.Math.QuarticExt4
import Qsag.Math.Goldilocks
import Qsag.Math.Primality

/-
# Acceptance facts about the concrete Hem transcript checker

These results inspect `verifyHemAffineWhir`; they do not assume an acceptance cover.
The malformed-batch regression records why the oracle/claim arity check is necessary.
The zero-oracle family below gives a concrete false-statement case in which acceptance
forces a linear challenge collision. This is not a proof for arbitrary Hem statements,
nor a refinement of the Rust Fiat–Shamir transcript parser.
-/

public section
namespace Qsag
set_option autoImplicit false

/-- An accepted cascade has matching batch arities and an actual polynomial witness from
    its candidate list. No semantic event cover is supplied as a hypothesis. -/
theorem verifyHemAffineWhir_cascade_witness {F : Type} [CommRingOps F] [DecidableEq F]
    (inst : HemWhirInstance F) (shifts : List F) (weights : List (F × F))
    (decoded : List (List F)) (rest : List (HemTranscriptRound F))
    (h : verifyHemAffineWhir inst (.cascade shifts weights decoded :: rest) = true) :
    inst.batchClaims.length = inst.batchOracles.length ∧
    shifts.length = inst.batchClaims.length ∧ weights.length = inst.batchClaims.length ∧
    ∃ P ∈ decoded, polyWitnessValid inst.initDomainPts inst.initMinAgree
      (inst.initDegBound + 1) (evalCascadeOracle inst.initDomainPts inst.batchOracles weights)
      inst.initKernel (evalCascadeClaim inst.batchClaims shifts weights) P = true := by
  obtain ⟨hArity, hShifts, hWeights, P, hMem, hP⟩ :=
    verifyHemAffineWhir_incremented_cascade_witness inst shifts weights decoded rest h
  refine ⟨hArity, hShifts, hWeights, P, hMem, ?_⟩
  rw [polyWitnessValid_def] at hP ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hP ⊢
  exact ⟨⟨hP.1.1, Nat.le_trans (hemNextMinAgree_mono _ _) hP.1.2⟩, hP.2⟩

/-- From an accepted transcript for an invalid batch, extract both an invalid input
    coordinate and the accepted combined polynomial. This is the concrete starting event
    for a cascade counting argument; no probability or event-cover hypothesis is assumed. -/
theorem verifyHemAffineWhir_invalid_coordinate
    (inst : HemWhirInstance QuarticGoldilocks)
    (shifts : List QuarticGoldilocks) (weights : List (QuarticGoldilocks × QuarticGoldilocks))
    (decoded : List (List QuarticGoldilocks)) (rest : List (HemTranscriptRound QuarticGoldilocks))
    (hDom : inst.initDomainPts.Nodup) (hEnough : inst.initDegBound + 1 ≤ inst.initMinAgree)
    (hInvalid : ¬ HemStatementValid inst)
    (hAccept : verifyHemAffineWhir inst (.cascade shifts weights decoded :: rest) = true) :
    ∃ i, i < inst.batchOracles.length ∧
      (∀ G : List QuarticGoldilocks,
        polyWitnessValid inst.initDomainPts inst.initMinAgree inst.initDegBound
          (inst.batchOracles.getD i (fun _ => CommRingOps.zero)) inst.initKernel
          (inst.batchClaims.getD i CommRingOps.zero) G = false) ∧
      ∃ P ∈ decoded, polyWitnessValid inst.initDomainPts inst.initMinAgree
        (inst.initDegBound + 1) (evalCascadeOracle inst.initDomainPts inst.batchOracles weights)
        inst.initKernel (evalCascadeClaim inst.batchClaims shifts weights) P = true := by
  obtain ⟨hArity, _, _, hP⟩ := verifyHemAffineWhir_cascade_witness _ _ _ _ _ hAccept
  have hShape : 1 ≤ inst.batchOracles.length ∧ inst.batchOracles.length ≤ 16 := by
    simp only [verifyHemAffineWhir, Bool.and_eq_true, decide_eq_true_eq] at hAccept
    exact ⟨hAccept.1.1.1.1, hAccept.1.1.1.2.1⟩
  have hBatch : ¬ HemBatchValid inst.initDomainPts inst.initMinAgree inst.initDegBound
      inst.initKernel inst.batchOracles inst.batchClaims :=
    fun hb => hInvalid ((HemStatementValid_iff _).mpr ⟨hShape, hb⟩)
  obtain ⟨i, hi, hBad⟩ := exists_invalid_batch_coordinate inst.initDomainPts
    inst.initMinAgree inst.initDegBound inst.initKernel hDom hEnough
    inst.batchOracles inst.batchClaims hArity.symm hBatch
  exact ⟨i, hi, hBad, hP⟩

/-- A single zero oracle carrying the false constant functional claim `1`. The stage list
    is arbitrary: acceptance must already pass the initial cascade witness check. -/
def hemZeroOracleClaimInstance {F : Type} [CommRingOps F]
    (dom : List F) (degree agree : Nat) (stages : List (HemWhirStageSpec F)) :
    HemWhirInstance F :=
  { batchOracles := [fun _ => CommRingOps.zero]
    batchClaims := [CommRingOps.one]
    initDomainPts := dom
    initDegBound := degree
    initMinAgree := agree
    initKernel := [CommRingOps.one]
    stages := stages }

/-- Enough agreement with the zero oracle forces the entire bounded-degree polynomial to
    vanish, hence forces every linear-functional claim to be zero. -/
theorem polyWitnessValid_zeroOracle_claim {F : Type} [LawfulField F] [DecidableEq F]
    (dom : List F) (degree agree : Nat) (kernel P : List F) (claim : F)
    (hDom : dom.Nodup) (hEnough : degree + 1 ≤ agree)
    (h : polyWitnessValid dom agree degree (fun _ => CommRingOps.zero) kernel claim P = true) :
    claim = CommRingOps.zero := by
  simp only [polyWitnessValid_def, Bool.and_eq_true, decide_eq_true_eq] at h
  have hCount : hemCosetAgreeCount dom (fun _ => (CommRingOps.zero : F)) P =
      (dom.filter (fun z => decide (RoundPoly.evalCoeffs P z = CommRingOps.zero))).length := by
    rw [hemCosetAgreeCount_def, ← qsum_get_filter_length]
    apply qsum_congr
    intro idx
    by_cases hz : RoundPoly.evalCoeffs P (dom.get idx) = CommRingOps.zero
    · simp only [hz, decide_true, ↓reduceIte]
    · have hn : (CommRingOps.zero : F) ≠ RoundPoly.evalCoeffs P (dom.get idx) :=
        fun he => hz he.symm
      simp only [hz, hn, decide_false, Bool.false_eq_true, ↓reduceIte]
  have hTrim : trimPoly P = trimPoly ([] : List F) :=
    trimPoly_eq_of_agree_on_nodup h.1.1 (Nat.zero_le (degree + 1))
      (List.Pairwise.filter _ hDom)
      (Nat.le_trans hEnough (hCount ▸ h.1.2))
      (fun z hz => of_decide_eq_true (List.mem_filter.mp hz).2)
  have hZero : ringDot P kernel = CommRingOps.zero := by
    rw [← ringDot_trimPoly_eq, hTrim, trimPoly_nil_eq]
    exact ringDot_nil_left kernel
  exact h.2.symm.trans hZero

theorem hemZeroOracleClaimInstance_invalid {F : Type} [LawfulField F] [DecidableEq F]
    (dom : List F) (degree agree : Nat) (stages : List (HemWhirStageSpec F))
    (hDom : dom.Nodup) (hEnough : degree + 1 ≤ agree) :
    ¬ HemStatementValid (hemZeroOracleClaimInstance dom degree agree stages) := by
  intro hValid
  obtain ⟨_, hBatch⟩ := (HemStatementValid_iff _).mp hValid
  obtain ⟨⟨P, hP⟩, _⟩ := (HemBatchValid_cons_cons_iff dom agree degree [CommRingOps.one]
    (fun _ => CommRingOps.zero) [] CommRingOps.one []).mp hBatch
  have h := polyWitnessValid_zeroOracle_claim dom degree agree [CommRingOps.one]
    P CommRingOps.one hDom hEnough hP
  exact LawfulField.one_ne_zero h

/-- For this false-statement family, actual checker acceptance forces a concrete linear
    challenge collision. The shifted claim `s` is fixed before `(α,β)` is sampled. -/
theorem verifyHemZeroOracle_implies_linear_collision {F : Type} [LawfulField F] [DecidableEq F]
    (dom : List F) (degree agree : Nat) (stages : List (HemWhirStageSpec F))
    (s α β : F) (decoded : List (List F)) (rest : List (HemTranscriptRound F))
    (hDom : dom.Nodup) (hEnough : degree + 2 ≤ agree)
    (h : verifyHemAffineWhir (hemZeroOracleClaimInstance dom degree agree stages)
      (.cascade [s] [(α, β)] decoded :: rest) = true) :
    CommRingOps.add α (CommRingOps.mul β s) = CommRingOps.zero := by
  obtain ⟨_, _, _, P, _, hP⟩ := verifyHemAffineWhir_cascade_witness _ _ _ _ _ h
  have hOracle : evalCascadeOracle dom [fun _ => (CommRingOps.zero : F)] [(α, β)] =
      fun _ => CommRingOps.zero := by
    funext i
    simp only [evalCascadeOracle_cons, evalCascadeOracle_nil, LawfulCommRing.mul_zero,
      LawfulCommRing.add_zero]
  change polyWitnessValid dom agree (degree + 1)
    (evalCascadeOracle dom [fun _ => CommRingOps.zero] [(α, β)]) [CommRingOps.one]
    (evalCascadeClaim [CommRingOps.one] [s] [(α, β)]) P = true at hP
  rw [hOracle] at hP
  have hc := polyWitnessValid_zeroOracle_claim dom (degree + 1) agree [CommRingOps.one]
    P _ hDom hEnough hP
  simpa only [evalCascadeClaim_cons, evalCascadeClaim_nil, LawfulCommRing.mul_one,
    LawfulCommRing.add_zero] using hc

/-- Deterministic acceptance-to-event conversion yields a finite challenge count even when
    the rest of the transcript is chosen adaptively after the challenge. Only `s` is fixed. -/
theorem verifyHemZeroOracle_accepted_pairs_le {F : Type} [LawfulField F] [DecidableEq F]
    (dom S : List F) (degree agree : Nat) (stages : List (HemWhirStageSpec F)) (s : F)
    (decoded : F × F → List (List F)) (rest : F × F → List (HemTranscriptRound F))
    (hDom : dom.Nodup) (hS : S.Nodup) (hEnough : degree + 2 ≤ agree) :
    ((prodPool S).filter (fun p =>
      verifyHemAffineWhir (hemZeroOracleClaimInstance dom degree agree stages)
        (.cascade [s] [p] (decoded p) :: rest p))).length ≤ S.length := by
  let accept := fun p : F × F =>
    verifyHemAffineWhir (hemZeroOracleClaimInstance dom degree agree stages)
      (.cascade [s] [p] (decoded p) :: rest p)
  let collision := fun p : F × F =>
    decide (CommRingOps.add p.1 (CommRingOps.mul p.2 s) = CommRingOps.zero)
  have hImp : ∀ p, accept p = true → collision p = true := by
    intro p hp
    exact decide_eq_true (verifyHemZeroOracle_implies_linear_collision dom degree agree stages
      s p.1 p.2 (decoded p) (rest p) hDom hEnough hp)
  have hLe : ∀ xs : List (F × F), (xs.filter accept).length ≤ (xs.filter collision).length := by
    intro xs
    induction xs with
    | nil => exact Nat.le_refl 0
    | cons p ps ih =>
      cases ha : accept p <;> cases hc : collision p <;>
        simp only [List.filter_cons, ha, hc, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      · exact ih
      · omega
      · have h := hImp p ha
        rw [hc] at h
        exact Bool.noConfusion h
      · omega
  have hBound := absorbed_linear_claim_bad_pairs_le_card S hS
    CommRingOps.zero CommRingOps.one s (Or.inr LawfulField.one_ne_zero)
  simp only [LawfulCommRing.mul_one, LawfulCommRing.zero_add] at hBound
  exact Nat.le_trans (hLe (prodPool S)) hBound

/-- The degree/agreement inequality used by the zero-oracle case holds at each deployed
    nv=24 row. This checks numerical applicability, not a refinement of those rows to Rust. -/
theorem hemZeroOracle_nv24_degree_agreement :
    ∀ w ∈ whirAffineStageWitnesses 24 true, w.d + 2 ≤ w.A := by
  have h : (whirAffineStageWitnesses 24 true).all (fun w => decide (w.d + 2 ≤ w.A)) = true := by
    rw [whirAffineStageWitnesses_qrom_eq_deployed.2]
    decide
  intro w hw
  exact of_decide_eq_true ((List.all_eq_true.mp h) w hw)

#verify_constructive
  Qsag.verifyHemAffineWhir_cascade_witness
  Qsag.verifyHemAffineWhir_invalid_coordinate
  Qsag.polyWitnessValid_zeroOracle_claim
  Qsag.hemZeroOracleClaimInstance_invalid
  Qsag.verifyHemZeroOracle_implies_linear_collision
  Qsag.verifyHemZeroOracle_accepted_pairs_le
  Qsag.hemZeroOracle_nv24_degree_agreement

end Qsag

/-
# Executable opening substitution for the Hem transcript checker

A decoder is a deterministic function of the public output and authenticated opening
values. Replacing these values by the online extractor changes an accepting check only
on the batched extraction-failure event. The measured bound is consumed directly;
there is no supplied Merkle cover. The decoder is an explicit interface, not a claim
that Rust transcript bytes or Fiat–Shamir challenges have been refined here.
-/

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
      have ha : batchMerkleFailure L slots H xs x = true := by
        rw [batchMerkleFailure_def]
        exact List.any_eq_true.mpr ⟨s, hs, he⟩
      rw [hf] at ha
      exact Bool.noConfusion ha
    exact Bool.eq_false_iff.mpr hn
  rw [measuredMerkleFailure_def] at hf'
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

#export_eqns claimedOpeningValues verifyOpeningBatch verifyHemOpeningBatch
end Qsag
end

/-
# Supported sliced fold counts and their quantitative boundary

The sliced decomposition proof is consumed by the claim-carrying binary fold theorem.
A fixed-theta specialization uses the actual equal-degree claim update, but exposes the
remaining invalid-mixture premise; it is not the three-challenge Theorem 5.1 lift.
The numerical stage profiles below concern one binary fold at each final-stage geometry.
They are never substituted into the multistage/QROM acceptance theorem.
-/

public section
namespace Qsag
set_option autoImplicit false

/-- Direct claim-carrying consumer of the proved sliced incidence count. The additional
    list-product term is explicit and is not replaced by the smaller paper constant. -/
theorem sliced_claimFold_bad_pairs_bound
    (D S kernel : List QuarticGoldilocks) (d A B m Dy : Nat)
    (f g : QuarticGoldilocks → QuarticGoldilocks) (e_f e_g s_g : QuarticGoldilocks)
    (hD : D.Nodup) (hS : S.Nodup) (hdA : d + 2 ≤ A)
    (hParams : slicedParamsOk D.length (d + 1) (A + 1) B m Dy = true)
    (hInvalidG : ∀ G : List QuarticGoldilocks, G.length ≤ d + 1 →
      A ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs G z = g z))).length →
      ringDot G kernel ≠ e_g)
    (L : List (Fin (prodPool S).length)) (hNd : L.Nodup)
    (hFlip : ∀ ch ∈ L, ¬¬ ∃ P : List QuarticGoldilocks,
      affineMcaAccepts D S (d + 1) (A + 1) (f, g) ch.1 P = true ∧
      ringDot P kernel = CommRingOps.add e_f
        (CommRingOps.add (CommRingOps.mul ((prodPool S).get ch).1 e_g)
          (CommRingOps.mul ((prodPool S).get ch).2 s_g))) :
    L.length ≤ Dy + slicedRest D.length (d + 1) (A + 1) B (m * (A + 1) - Dy) Dy S.length +
      (gsDecodeList (d + 1) A D f).length * (gsDecodeList d A D g).length * S.length := by
  exact claimFold_bad_pairs_bound D S kernel d A _ f g e_f e_g s_g hD hS hdA
    (slicedParamsOk_sound D.length (d + 1) (A + 1) B m Dy hParams D S hD hS rfl)
    hInvalidG L hNd hFlip

/-- Fixed-theta component of the actual `g + (alpha + beta X)(f + theta g)` combiner.
    `hInvalidMix` is a real remaining obligation: invalid input claims alone do not imply
    it for every theta. Counting its exceptional theta values and handling intermediate
    geometries is required before claiming the full equal-degree lift. -/
theorem sliced_equal_degree_fixed_theta_bound
    (D S kernel : List QuarticGoldilocks) (d A B m Dy : Nat)
    (f g : QuarticGoldilocks → QuarticGoldilocks) (e_f e_g c_f c_g θ : QuarticGoldilocks)
    (hD : D.Nodup) (hS : S.Nodup) (hdA : d + 2 ≤ A)
    (hParams : slicedParamsOk D.length (d + 1) (A + 1) B m Dy = true)
    (hInvalidMix : ∀ G : List QuarticGoldilocks, G.length ≤ d + 1 →
      A ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs G z =
        CommRingOps.add (f z) (CommRingOps.mul θ (g z))))).length →
      ringDot G kernel ≠ CommRingOps.add e_f (CommRingOps.mul θ e_g))
    (L : List (Fin (prodPool S).length)) (hNd : L.Nodup)
    (hFlip : ∀ ch ∈ L, ¬¬ ∃ P : List QuarticGoldilocks,
      affineMcaAccepts D S (d + 1) (A + 1)
        (g, fun z => CommRingOps.add (f z) (CommRingOps.mul θ (g z))) ch.1 P = true ∧
      ringDot P kernel = hemFoldClaimUpdate e_f e_g c_f c_g θ
        ((prodPool S).get ch).1 ((prodPool S).get ch).2) :
    L.length ≤ Dy + slicedRest D.length (d + 1) (A + 1) B (m * (A + 1) - Dy) Dy S.length +
      (gsDecodeList (d + 1) A D g).length *
        (gsDecodeList d A D (fun z => CommRingOps.add (f z) (CommRingOps.mul θ (g z)))).length *
        S.length :=
  sliced_claimFold_bad_pairs_bound D S kernel d A B m Dy g
    (fun z => CommRingOps.add (f z) (CommRingOps.mul θ (g z))) e_g
    (CommRingOps.add e_f (CommRingOps.mul θ e_g))
    (CommRingOps.add c_f (CommRingOps.mul θ c_g)) hD hS hdA hParams hInvalidMix L hNd
    (fun ch hch => by
      have h := hFlip ch hch
      rw [hemFoldClaimUpdate_def] at h
      exact h)

/-- Count divided by the actual challenge-pair cardinality. This is a binary decomposition
    budget, without the claim-list term or any three-challenge/multi-fold lift. -/
def slicedBinaryStageBound (g : HemStageGeom) (r : Nat × Nat × Nat × Nat × Nat)
    (w : Nat × Nat × Nat × Nat) : RatBound :=
  ⟨slicedStageCount goldilocksExt4Card g r w, goldilocksExt4Card * goldilocksExt4Card,
    Nat.mul_pos goldilocksExt4Card_pos goldilocksExt4Card_pos⟩

/-- Pure arithmetic: a 184-bit input tolerates this explicit DFM query budget. It does not
    assert that DFM applies to any particular protocol execution. -/
theorem dfm184_budget_at_2pow27 (b : RatBound) (hb : atLeastBits 184 b)
    (Q : Nat) (hQ : Q + 1 ≤ 2 ^ 27) : atLeastBits 128 (dfmRoundScale Q b) := by
  have hScale : (2 * Q + 1) ^ 2 ≤ 2 ^ 56 := by
    have hbase : 2 * Q + 1 ≤ 2 ^ 28 := by omega
    exact Nat.le_trans (Nat.pow_le_pow_left hbase 2) (by decide)
  change (2 * Q + 1) ^ 2 * b.num * 2 ^ 128 ≤ b.den
  have h := Nat.mul_le_mul_right (b.num * 2 ^ 128) hScale
  have he : 2 ^ 56 * (b.num * 2 ^ 128) = b.num * 2 ^ 184 := by
    calc 2 ^ 56 * (b.num * 2 ^ 128) = b.num * (2 ^ 56 * 2 ^ 128) := Nat.mul_left_comm _ _ _
         _ = b.num * 2 ^ 184 := by rw [show 2 ^ 56 * 2 ^ 128 = 2 ^ 184 from by decide]
  rw [Nat.mul_assoc]
  have hb' : 2 ^ 56 * (b.num * 2 ^ 128) ≤ b.den := by
    rw [he]
    exact hb
  exact Nat.le_trans h hb'

/-- Every non-exhaustive canonical row supplies an actual proved binary decomposition
    count and a 184-bit rational budget. DFM scaling remains an explicitly arithmetic
    conclusion at Q+1 <= 2^27, not an assertion of a QROM experiment reduction. -/
theorem sliced_stage_supported_budget (nv : Nat) (h2 : 2 ≤ nv) (h24 : nv ≤ 24)
    (g : HemStageGeom) (hg : g ∈ hemStageGeoms nv)
    (hne : hemJohnsonQromStageExhaustive g = false) :
    ∃ (r : Nat × Nat × Nat × Nat × Nat) (w : Nat × Nat × Nat × Nat),
      hemJohnsonQromTableRow nv g.stageIdx = some r ∧ slicedStageRow nv g.stageIdx = some w ∧
      (∀ D S : List QuarticGoldilocks, D.Nodup → S.Nodup → D.length = g.n →
        AffineFoldDecompBound D S g.d r.2.2.1 (slicedStageCount S.length g r w)) ∧
      atLeastBits 184 (slicedBinaryStageBound g r w) ∧
      (∀ Q : Nat, Q + 1 ≤ 2 ^ 27 → atLeastBits 128 (dfmRoundScale Q (slicedBinaryStageBound g r w))) := by
  obtain ⟨r, w, hr, hw, hd, hb, hbits⟩ := sliced_stage_decomp_bound nv h2 h24 g hg hne
  have hb184 : atLeastBits 184 (slicedBinaryStageBound g r w) := by
    show slicedStageCount goldilocksExt4Card g r w * 2 ^ 184 ≤
      goldilocksExt4Card * goldilocksExt4Card
    rw [goldilocksExt4Card_def]
    exact Nat.le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hbits)) hb
  exact ⟨r, w, hr, hw, hd, hb184, fun Q hQ => dfm184_budget_at_2pow27 _ hb184 Q hQ⟩

/-- Total diagnostic accessor. Missing/exhaustive rows get no soundness credit. -/
def slicedBinaryStageProfile (nv : Nat) (g : HemStageGeom) : RatBound :=
  match hemJohnsonQromTableRow nv g.stageIdx, slicedStageRow nv g.stageIdx with
  | some r, some w => slicedBinaryStageBound g r w
  | _, _ => RatBound.one

/-- The Q+1 convention matters: the universal 184-bit guarantee fails at Q=2^27,
    although particular table rows can be stronger than that universal floor. -/
theorem tooth_dfm184_query_boundary :
    let b : RatBound := ⟨1, 2 ^ 184, by decide⟩
    atLeastBits 128 (dfmRoundScale (2 ^ 27 - 1) b) ∧
    ¬ atLeastBits 128 (dfmRoundScale (2 ^ 27) b) := by
  decide +kernel

#verify_constructive
  Qsag.sliced_claimFold_bad_pairs_bound
  Qsag.sliced_equal_degree_fixed_theta_bound
  Qsag.dfm184_budget_at_2pow27
  Qsag.sliced_stage_supported_budget
  Qsag.tooth_dfm184_query_boundary
/-- Public numerical interface, avoiding unfolding the full field cardinality in clients. -/
theorem slicedBinaryStageBound_bits_iff (bits : Nat) (g : HemStageGeom)
    (r : Nat × Nat × Nat × Nat × Nat) (w : Nat × Nat × Nat × Nat) :
    atLeastBits bits (slicedBinaryStageBound g r w) ↔
      slicedStageCount goldilocksExt4Card g r w * 2 ^ bits ≤
        goldilocksExt4Card * goldilocksExt4Card := Iff.rfl

/-- The executable parameter certificate implies decomposition for an arbitrary
stage geometry, without a table lookup or a cap on the variable count. -/
theorem sliced_stage_checked_decomposition (g : HemStageGeom)
    (r : Nat × Nat × Nat × Nat × Nat) (w : Nat × Nat × Nat × Nat)
    (hParams : slicedParamsOk g.n g.d r.2.2.1 w.2.2.1 r.2.2.2.1 r.2.2.2.2 = true)
    (D S : List QuarticGoldilocks) (hD : D.Nodup) (hS : S.Nodup) (hLen : D.length = g.n) :
    AffineFoldDecompBound D S g.d r.2.2.1 (slicedStageCount S.length g r w) := by
  rw [slicedStageCount_def]
  exact slicedParamsOk_sound g.n g.d r.2.2.1 w.2.2.1 r.2.2.2.1 r.2.2.2.2 hParams D S hD hS hLen

#verify_constructive slicedBinaryStageBound_bits_iff sliced_stage_checked_decomposition

end Qsag
end

/-
# Coherent observable bridge to the authenticated Hem checker

For bit-output ideal hashes the actual authenticated checker has identical event mass
in the decoded Fourier runtime and the original coherent experiment, up to the explicit
normalization. This is NOT the measured-log extraction bound: no address log is manufactured.
-/

public section
namespace Qsag
set_option autoImplicit false

/-- Direct consumer: the real path/shape/root and Hem checks on arbitrary coherent outputs.
    The bit-output width is explicit; the deployed 256-bit layout is not instantiated here. -/
theorem coherent_hem_authenticated_event_eq {n cardAnc Q : Nat}
    (A : QuantumAdv n 1 cardAnc Q) (L : MerkleAddressLayout n 1)
    (slots : List (MerkleOpeningSlot n 1)) (inst : HemWhirInstance QuarticGoldilocks)
    (decode : Fin n → List (Option (MerkleOpeningValue 1)) → List (HemTranscriptRound QuarticGoldilocks)) :
    coherentTableEventMass (verifyHemOpeningBatch L slots inst decode)
      (fourierOracleState (fourierAdvStateAt A Q (Nat.le_refl Q))) =
      4 ^ (n * Q + n) * uniformOracleSum 1 n (fun H =>
        QVec.queryMassOn (verifyHemOpeningBatch L slots inst decode H) (runQuantumAdv A H)) :=
  fourierAdv_event_eq A (verifyHemOpeningBatch L slots inst decode)

/-- The same event transformation applies to each standalone authenticated opening batch. -/
theorem coherent_merkle_batch_event_eq {n cardAnc Q : Nat}
    (A : QuantumAdv n 1 cardAnc Q) (L : MerkleAddressLayout n 1)
    (slots : List (MerkleOpeningSlot n 1)) :
    coherentTableEventMass (verifyOpeningBatch L slots)
      (fourierOracleState (fourierAdvStateAt A Q (Nat.le_refl Q))) =
      4 ^ (n * Q + n) * uniformOracleSum 1 n (fun H =>
        QVec.queryMassOn (verifyOpeningBatch L slots H) (runQuantumAdv A H)) :=
  fourierAdv_event_eq A (verifyOpeningBatch L slots)

/-- Both numerator and denominator undergo the same scale; this is an actual normalized
    experiment identity, not solely an amplitude identity. -/
theorem coherent_decoded_total_mass {n cardAnc Q : Nat} (A : QuantumAdv n 1 cardAnc Q) :
    coherentTableEventMass (fun _ _ => true)
      (fourierOracleState (fourierAdvStateAt A Q (Nat.le_refl Q))) =
      4 ^ (n * Q + n) * quantumExperimentTotal A := by
  rw [fourierAdv_event_eq]
  have he : ∀ H : Fin n → BitVec 1,
      QVec.queryMassOn (fun _ => true) (runQuantumAdv A H) =
        prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init := by
    intro H
    rw [← runQuantumAdv_normSq A H, QVec.queryMassOn_def, QVec.stateNormSq_def]
    exact qsum_congr (fun _ => rfl)
  rw [uniformOracleSum_congr 1 n _ _ he, uniformOracleSum_const, quantumExperimentTotal_def]

/-! A word oracle uses n*w independent truth-table bits and a w-bit answer
register. Walsh acts on every truth-table bit, while the controlled query XORs
an entire word. No measurement or classical address log is introduced. -/
abbrev CoherentWordState (n w cardAnc : Nat) := OracleBitTable (n * w) → QVec n w cardAnc

def wordTableOracle {n w : Nat} (h : OracleBitTable (n * w)) : Fin n → BitVec w :=
  fun x => BitVec.ofNat w (qsum w (fun b => if
    (tableBitOracle (n * w) h ⟨x.val * w + b.val, by
      have hb := b.isLt
      have hx := Nat.mul_le_mul_right w x.isLt
      rw [Nat.succ_mul] at hx
      omega⟩).getLsbD 0 then 2 ^ b.val else 0))

def wordFourier {n w cardAnc : Nat} (ψ : CoherentWordState n w cardAnc) :
    CoherentWordState n w cardAnc :=
  fun d x y a => oracleWalsh (n * w) (fun h => ψ h x y a) d

def wordDouble {n w cardAnc : Nat} (k : Nat) (ψ : CoherentWordState n w cardAnc) :
    CoherentWordState n w cardAnc := fun h => qvecDoublePow k (ψ h)

theorem wordFourier_square {n w cardAnc : Nat} (ψ : CoherentWordState n w cardAnc) :
    wordFourier (wordFourier ψ) = wordDouble (n * w) ψ := by
  funext h x y a
  unfold wordFourier wordDouble
  simp only [qvecDoublePow_def]
  exact oracleWalsh_square (n * w) _ h

theorem wordFourier_double {n w cardAnc : Nat} (k : Nat) (ψ : CoherentWordState n w cardAnc) :
    wordFourier (wordDouble k ψ) = wordDouble k (wordFourier ψ) := by
  funext h x y a
  unfold wordFourier wordDouble
  simp only [qvecDoublePow_def]
  exact oracleWalsh_doublePow (n * w) k _ h

def wordOracleStep {n w cardAnc : Nat} (U : ScaledUnitary n w cardAnc)
    (ψ : CoherentWordState n w cardAnc) : CoherentWordState n w cardAnc :=
  fun h => U.apply (oracleXor (wordTableOracle h) (ψ h))

def wordFourierStep {n w cardAnc : Nat} (U : ScaledUnitary n w cardAnc)
    (ψ : CoherentWordState n w cardAnc) : CoherentWordState n w cardAnc :=
  wordFourier (wordOracleStep U (wordFourier ψ))

/-- Operational Fourier execution: each step conjugates the full-word query. -/
def wordFourierStateAt {n w cardAnc Q : Nat} (A : QuantumAdv n w cardAnc Q) :
    (t : Nat) → t ≤ Q → CoherentWordState n w cardAnc
  | 0, _ => wordFourier (fun _ => A.init)
  | t + 1, ht => wordFourierStep (A.steps ⟨t, ht⟩)
      (wordFourierStateAt A t (Nat.le_of_succ_le ht))

theorem wordOracleStep_double {n w cardAnc : Nat} (U : ScaledUnitary n w cardAnc)
    (k : Nat) (ψ : CoherentWordState n w cardAnc) :
    wordOracleStep U (wordDouble k ψ) = wordDouble k (wordOracleStep U ψ) := by
  funext h
  have hx : oracleXor (wordTableOracle h) (qvecDoublePow k (ψ h)) =
      qvecDoublePow k (oracleXor (wordTableOracle h) (ψ h)) := by
    simp only [oracleXor_def, qvecDoublePow_def]
  show (U.apply (oracleXor (wordTableOracle h) (qvecDoublePow k (ψ h)))) =
    qvecDoublePow k (U.apply (oracleXor (wordTableOracle h) (ψ h)))
  rw [hx]
  exact U.map_doublePow k _

theorem wordDouble_add {n w cardAnc : Nat} (k l : Nat) (ψ : CoherentWordState n w cardAnc) :
    wordDouble k (wordDouble l ψ) = wordDouble (k + l) ψ := by
  funext h x y a
  unfold wordDouble
  simp only [qvecDoublePow_def]
  exact gaussDoublePow_add k l _

theorem wordDouble_zero {n w cardAnc : Nat} (ψ : CoherentWordState n w cardAnc) :
    wordDouble 0 ψ = ψ := by
  funext h x y a
  unfold wordDouble
  simp only [qvecDoublePow_def, gaussDoublePow_base]

theorem wordFourierStateAt_eq {n w cardAnc Q : Nat} (A : QuantumAdv n w cardAnc Q) :
    ∀ t (ht : t ≤ Q), wordFourierStateAt A t ht =
      wordDouble (n * w * t) (wordFourier (fun h => advStateAt A (wordTableOracle h) t ht))
  | 0, _ => by
    simp only [wordFourierStateAt, advStateAt_zero, Nat.mul_zero, wordDouble_zero]
  | t + 1, ht => by
    simp only [wordFourierStateAt, wordFourierStep, wordFourierStateAt_eq,
      wordFourier_double, wordFourier_square, wordDouble_add,
      wordOracleStep_double, Nat.mul_succ]
    have hs : (wordOracleStep (A.steps ⟨t, ht⟩) fun h =>
        advStateAt A (wordTableOracle h) t (Nat.le_of_succ_le ht)) =
        fun h => advStateAt A (wordTableOracle h) (t + 1) ht := by
      funext h
      rw [advStateAt_succ]
      rfl
    rw [hs]

/-- Decoding preserves all correlations between the full-width oracle and output. -/
theorem wordFourierStateAt_decode {n w cardAnc Q : Nat} (A : QuantumAdv n w cardAnc Q) :
    wordFourier (wordFourierStateAt A Q (Nat.le_refl Q)) =
      wordDouble (n * w * Q + n * w) (fun h => runQuantumAdv A (wordTableOracle h)) := by
  rw [wordFourierStateAt_eq, wordFourier_double, wordFourier_square, wordDouble_add]
  simp only [runQuantumAdv_def]

def wordCoherentEventMass {n w cardAnc : Nat}
    (event : (Fin n → BitVec w) → Fin n → Bool) (ψ : CoherentWordState n w cardAnc) : Nat :=
  oracleTableSum (n * w) (fun h => QVec.queryMassOn (event (wordTableOracle h)) (ψ h))

/-- Tensor-product word-register bridge. Both sides enumerate the same n*w
independent uniform truth-table bits. In particular w=256 is supported. -/
theorem coherent_word_hem_authenticated_event_eq {n w cardAnc Q : Nat}
    (A : QuantumAdv n w cardAnc Q) (L : MerkleAddressLayout n w)
    (slots : List (MerkleOpeningSlot n w)) (inst : HemWhirInstance QuarticGoldilocks)
    (decode : Fin n → List (Option (MerkleOpeningValue w)) → List (HemTranscriptRound QuarticGoldilocks)) :
    wordCoherentEventMass (verifyHemOpeningBatch L slots inst decode)
      (wordFourier (wordFourierStateAt A Q (Nat.le_refl Q))) =
      4 ^ (n * w * Q + n * w) * oracleTableSum (n * w) (fun h =>
        QVec.queryMassOn (verifyHemOpeningBatch L slots inst decode (wordTableOracle h))
          (runQuantumAdv A (wordTableOracle h))) := by
  rw [wordFourierStateAt_decode]
  unfold wordCoherentEventMass wordDouble
  simp only [queryMassOn_doublePow]
  exact oracleTableSum_mul _ _ _

#verify_constructive wordFourier_square wordFourierStateAt_eq wordFourierStateAt_decode
  coherent_word_hem_authenticated_event_eq

#verify_constructive
  Qsag.coherent_hem_authenticated_event_eq
  Qsag.coherent_merkle_batch_event_eq
  Qsag.coherent_decoded_total_mass
end Qsag
end

/-
# Qsag.Protocol.Aggregation.HemMultistageRbrAndSaltedQrom — Equal-Degree `θ`-Mixing Lift, Multi-Batch `verifyHemAffineWhir` Bridge & Compressed-Oracle Salted-Merkle QROM Budget

Constructive Lean 4.35 theorems closing three structural gaps across `HemSlicedFoldBudget`,
`HemWhirRbrSoundness`, `HemVerifierAcceptance`, and `HemExtractedOpeningBridge`
(zero custom axioms, purely constructive extractors):

1. **Equal-Degree `θ`-Exception Bound & Full Three-Challenge `(θ, α, β)` Lift
   (`equal_degree_bad_theta_bound`, `equal_degree_three_challenge_bound`)**:
   - Eliminates the unproved `hInvalidMix` premise in `HemSlicedFoldBudget.sliced_equal_degree_fixed_theta_bound`
     (witnessed necessary by `tooth_equal_degree_invalid_mixture`).
   - Observes that `f(z) + θ g(z) = f(z) + (θ + 0 · z) g(z)` is the `β = 0` slice of `prodPool S`
     when `0 ∈ S`. Any `AffineFoldDecompBound D S (d + 1) A badTheta` combined with degree collapse
     `F_sub := polySubVar H (polyScaleVar θ G_poly)` (`length ≤ d + 1`) bounds the exceptional
     `θ ∈ S` violating `hInvalidMix` by `badTheta + |gsDecodeList d (A - 1) D f| · |gsDecodeList d (A - 1) D g|`
     under symmetric input invalidity (`(f, e_f)` invalid or `(g, e_g)` invalid).
   - Composes with `claimFold_bad_pairs_bound` over all `(θ, (α, β)) ∈ S × prodPool S` (`|S|^3` triples).

2. **Arbitrary-Batch (`1 ≤ m ≤ 16`) Multi-Stage `verifyHemAffineWhir` & Extracted-Opening Bridge
   (`arbitrary_batch_cascade_fiber_bound`, `hem_multistage_extracted_acceptance_and_witness`)**:
   - Generalizes the `m = 1` cascade argument in `HemWhirRbrSoundness`: for any batch arity `m ≥ 1`
     with an invalid coordinate `i₀ < m`, conditioning on any fixed assignment of the `m - 1`
     remaining weight pairs reduces the `i₀`-th slice to `claimFold_bad_pairs_bound` with identical
     error density `(badMca + listF · listG · |S|) / |S|^2`.
   - Composes `HemExtractedOpeningBridge.measured_hem_acceptance_from_extracted` with
     `HemVerifierAcceptance.verifyHemAffineWhir_invalid_coordinate` and `hemAffineWhirStateFunction`
     over arbitrary batch sizes `1 ≤ m ≤ 16` and arbitrary multi-stage `inst.stages`.

3. **State-Restoration & `[CDHZ25]` PoW-Adjusted Salted-Merkle QROM Budgets
   (`cdhz_sliced_stage_clears_128bits_at_2pow50`, `cdhzPqsrPow16_clears_128bits_at_2pow40`)**:
   - Separates linear state-restoration scaling `(Q + 1) · numRounds · b` (`[BCS16; CMS19; CY24]`,
     clearing `128` bits across all `nv ∈ [2, 24]` non-exhaustive sliced stages up to `Q ≤ 2^50`)
     from `[CDHZ25, Thm 6.9]` quadratic Grover post-quantum state restoration combined with the
     deployed `WHIR_FOLD_POW_BITS = 16` joint `(PoW × Challenge)` reduction
     (`23 (Q + 1 + numRounds)^2 · b / 2^16`), clearing `128` bits universally up to
     `Q + 1 + numRounds ≤ 2^33` on `184`-bit stages and up to `Q + 1 + numRounds ≤ 2^40` on all
     `≥ 197`-bit stages alongside the `256`-bit salted-Merkle compressed-oracle collision tail.
-/


public section
namespace Qsag

set_option autoImplicit false
set_option exponentiation.threshold 2048
set_option maxRecDepth 65536

/-! ### Recursive child-WHIR dimensions

The flat tables above remain exact compatibility data. A recursive parent partitions its
Boolean cube into children by fixing `nv - min nv childCap` coordinates. The cap is a
parameter, so dimensions through 30 do not require pretending that a flat nv=24 row
certifies a larger domain. These are child geometry/proximity results; the recursive
verifier must additionally bind children and account for all their failure events.
-/

def hemRecursiveChildVars (nv childCap : Nat) : Nat := min nv childCap

def hemRecursiveSplitDepth (nv childCap : Nat) : Nat := nv - hemRecursiveChildVars nv childCap

def hemRecursiveChildCount (nv childCap : Nat) : Nat := 2 ^ hemRecursiveSplitDepth nv childCap

def hemRecursiveStageGeoms (nv childCap : Nat) : List HemStageGeom :=
  hemStageGeoms (hemRecursiveChildVars nv childCap)

def whirRecursiveAffineStageWitnesses (nv childCap : Nat) (isQrom : Bool) : List WhirAffineWitness :=
  whirAffineStageWitnesses (hemRecursiveChildVars nv childCap) isQrom

theorem hemRecursiveChildVars_bounds (nv childCap : Nat)
    (h2 : 2 ≤ nv) (hc2 : 2 ≤ childCap) (hc24 : childCap ≤ 24) :
    2 ≤ hemRecursiveChildVars nv childCap ∧ hemRecursiveChildVars nv childCap ≤ 24 := by
  exact ⟨Nat.le_min.mpr ⟨h2, hc2⟩, Nat.le_trans (Nat.min_le_right nv childCap) hc24⟩

/-- The partition preserves the full parent cube, including parents with nv > 24. -/
theorem hemRecursive_capacity (nv childCap : Nat) :
    hemRecursiveChildCount nv childCap * 2 ^ hemRecursiveChildVars nv childCap = 2 ^ nv := by
  unfold hemRecursiveChildCount hemRecursiveSplitDepth hemRecursiveChildVars
  rw [← Nat.pow_add, Nat.sub_add_cancel (Nat.min_le_left nv childCap)]

/-- Existing flat callers use exactly one child and the unchanged witness list. -/
theorem hemRecursive_flat_compat (nv childCap : Nat) (h : nv ≤ childCap) (qrom : Bool) :
    hemRecursiveChildCount nv childCap = 1 ∧
    hemRecursiveStageGeoms nv childCap = hemStageGeoms nv ∧
    whirRecursiveAffineStageWitnesses nv childCap qrom = whirAffineStageWitnesses nv qrom := by
  unfold hemRecursiveChildCount hemRecursiveSplitDepth hemRecursiveStageGeoms
    whirRecursiveAffineStageWitnesses hemRecursiveChildVars
  rw [Nat.min_eq_left h, Nat.sub_self, Nat.pow_zero]
  exact ⟨rfl, rfl, rfl⟩

/-- Parametric child geometry and QROM coverage, without a cap on parent dimension. -/
theorem hem_recursive_qrom_witnesses_cover_every_child_stage
    (nv childCap : Nat) (h2 : 2 ≤ nv) (hc2 : 2 ≤ childCap) (hc24 : childCap ≤ 24) :
    hemStageGeometryValid (hemRecursiveChildVars nv childCap) = true ∧
    ∀ g ∈ hemRecursiveStageGeoms nv childCap,
      hemJohnsonQromStageCovered (goldilocksPrime ^ 4) (hemRecursiveChildVars nv childCap) g = true := by
  obtain ⟨hlo, hhi⟩ := hemRecursiveChildVars_bounds nv childCap h2 hc2 hc24
  exact ⟨(hemStageGeometry_valid_and_under_query_cap _ hlo hhi).1,
    hem_johnson_qrom_witnesses_cover_every_canonical_stage.1 _ hlo hhi⟩

theorem hem_recursive_gs_deployed_degree_lt_agreement
    (nv childCap : Nat) (h2 : 2 ≤ nv) (hc2 : 2 ≤ childCap) (hc24 : childCap ≤ 24)
    (w : WhirAffineWitness) (hw : w ∈ whirRecursiveAffineStageWitnesses nv childCap true) :
    w.d < w.A := by
  obtain ⟨hlo, hhi⟩ := hemRecursiveChildVars_bounds nv childCap h2 hc2 hc24
  exact hem_gs_deployed_degree_lt_agreement _ hlo hhi w hw

/-- With the existing 24-variable child profile, parents through 30 need at most 64
    children. This is an arithmetic capacity bound, not a validator-to-row size estimate. -/
theorem hem_recursive_nv30_capacity (nv : Nat) (h30 : nv ≤ 30) :
    hemRecursiveChildCount nv 24 ≤ 64 ∧
    hemRecursiveChildCount nv 24 * 2 ^ hemRecursiveChildVars nv 24 = 2 ^ nv := by
  refine ⟨?_, hemRecursive_capacity nv 24⟩
  have hd : hemRecursiveSplitDepth nv 24 ≤ 6 := by
    unfold hemRecursiveSplitDepth hemRecursiveChildVars
    omega
  exact Nat.le_trans (Nat.pow_le_pow_right (by decide) hd) (by decide)

/-- `#tooth`: dropping the recursive fanout silently loses 63 of the 64 children. -/
theorem tooth_recursive_nv30_needs_all_children :
    ∃ children : Nat, children = 64 ∧ hemRecursiveChildCount 30 24 = children ∧
    hemRecursiveChildVars 30 24 = 24 ∧
    hemRecursiveChildCount 30 24 * 2 ^ hemRecursiveChildVars 30 24 = 2 ^ 30 ∧
    2 ^ hemRecursiveChildVars 30 24 < 2 ^ 30 := by
  exact ⟨64, by decide⟩

#tooth_pair hemRecursive_capacity vs tooth_recursive_nv30_needs_all_children
#verify_constructive hemRecursive_capacity
#verify_constructive hemRecursive_flat_compat
#verify_constructive hem_recursive_qrom_witnesses_cover_every_child_stage
#verify_constructive hem_recursive_gs_deployed_degree_lt_agreement
#verify_constructive hem_recursive_nv30_capacity

/-! ## §1. Equal-Degree `θ`-Exception Bound & Three-Challenge `(θ, α, β)` Lift -/

/-- Constructive index witness for membership in a `DecidableEq` list. -/
def findListMemIdx {α : Type} [DecidableEq α] (x : α) :
    (ys : List α) → x ∈ ys → { i : Fin ys.length // ys.get i = x }
  | [], h => nomatch h
  | y :: ys, h =>
    if hEq : x = y then
      ⟨⟨0, Nat.zero_lt_succ _⟩, hEq.symm⟩
    else
      have hTail : x ∈ ys := by
        rcases List.mem_cons.mp h with rfl | hm
        · exact False.elim (hEq rfl)
        · exact hm
      let sub := findListMemIdx x ys hTail
      ⟨⟨sub.1.1 + 1, Nat.succ_lt_succ sub.1.2⟩, sub.2⟩

private theorem filter_any_le_mul_one {α β : Type} (items : List α) (pred : α → β → Bool)
    (xs : List β) (hEach : ∀ a ∈ items, (xs.filter (pred a)).length ≤ 1) :
    (xs.filter (fun x => items.any (fun a => pred a x))).length ≤ items.length := by
  have h := filter_any_length_le_mul items pred xs 1 hEach
  rw [Nat.mul_one] at h
  exact h

private theorem linear_theta_fin_le_one {F : Type} [LawfulField F] [DecidableEq F]
    (S : List F) (hS : S.Nodup) (Δ_f Δ_g : F)
    (hNz : Δ_f ≠ CommRingOps.zero ∨ Δ_g ≠ CommRingOps.zero)
    (L : List (Fin S.length)) (hNd : L.Nodup) :
    (L.filter (fun iθ =>
      decide (CommRingOps.add Δ_f (CommRingOps.mul (S.get iθ) Δ_g) = CommRingOps.zero))).length ≤ 1 := by
  generalize hFilt : L.filter (fun iθ =>
    decide (CommRingOps.add Δ_f (CommRingOps.mul (S.get iθ) Δ_g) = CommRingOps.zero)) = fl
  have hFlNd : fl.Nodup := hFilt ▸ List.Pairwise.filter _ hNd
  rcases fl with _ | ⟨i₁, _ | ⟨i₂, _⟩⟩
  · exact Nat.zero_le 1
  · exact Nat.le_refl 1
  · exfalso
    have hMem₁ : i₁ ∈ L.filter (fun iθ =>
        decide (CommRingOps.add Δ_f (CommRingOps.mul (S.get iθ) Δ_g) = CommRingOps.zero)) := by
      rw [hFilt]; exact .head _
    have hMem₂ : i₂ ∈ L.filter (fun iθ =>
        decide (CommRingOps.add Δ_f (CommRingOps.mul (S.get iθ) Δ_g) = CommRingOps.zero)) := by
      rw [hFilt]; exact .tail _ (.head _)
    have e₁ : CommRingOps.add Δ_f (CommRingOps.mul (S.get i₁) Δ_g) = CommRingOps.zero :=
      of_decide_eq_true (List.mem_filter.mp hMem₁).2
    have e₂ : CommRingOps.add Δ_f (CommRingOps.mul (S.get i₂) Δ_g) = CommRingOps.zero :=
      of_decide_eq_true (List.mem_filter.mp hMem₂).2
    have hDiffId : CommRingOps.mul (CommRingOps.sub (S.get i₁) (S.get i₂)) Δ_g =
        CommRingOps.sub
          (CommRingOps.add Δ_f (CommRingOps.mul (S.get i₁) Δ_g))
          (CommRingOps.add Δ_f (CommRingOps.mul (S.get i₂) Δ_g)) := by
      constructive_ring
    have hProd0 : CommRingOps.mul (CommRingOps.sub (S.get i₁) (S.get i₂)) Δ_g = CommRingOps.zero := by
      rw [hDiffId, e₁, e₂, LawfulCommRing.sub_self]
    rcases LawfulField.mul_eq_zero hProd0 with hSub0 | hg0
    · have hIdxEq : i₁ = i₂ := nodup_get_inj hS (LawfulCommRing.sub_eq_zero_iff.mp hSub0)
      exact (List.pairwise_cons.mp hFlNd).1 i₂ (.head _) hIdxEq
    · rw [hg0, LawfulCommRing.mul_zero, LawfulCommRing.add_zero] at e₁
      rcases hNz with hfNe | hgNe
      · exact hfNe e₁
      · exact hgNe hg0

/-- **Equal-Degree `θ`-Mixing Exception Bound (`equal_degree_bad_theta_bound`)**:
    Suppose `0 ∈ S`, `D.Nodup`, `S.Nodup`, `d + 3 ≤ A ≤ D.length`, and `AffineFoldDecompBound D S (d + 1) A badTheta`.
    Whenever EITHER `(f, e_f)` OR `(g, e_g)` has no degree-`≤ d` witness at agreement `≥ A - 1` on `D`,
    at most `badTheta + |gsDecodeList d (A - 1) D f| · |gsDecodeList d (A - 1) D g|` indices `iθ ∈ Fin S.length`
    admit a degree-`≤ d` witness `H` (`H.length ≤ d + 1`) at agreement `≥ A` for `(f + θ g, e_f + θ e_g)`. -/
theorem equal_degree_bad_theta_bound
    (D S kernel : List QuarticGoldilocks) (d A badTheta : Nat)
    (f g : QuarticGoldilocks → QuarticGoldilocks) (e_f e_g : QuarticGoldilocks)
    (hD : D.Nodup) (hS : S.Nodup) (hZeroS : (CommRingOps.zero : QuarticGoldilocks) ∈ S)
    (hdA : d + 3 ≤ A) (hAD : A ≤ D.length)
    (hDecompTheta : AffineFoldDecompBound D S (d + 1) A badTheta)
    (hInvalidFG :
      (∀ Fp : List QuarticGoldilocks, Fp.length ≤ d + 1 →
        A - 1 ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs Fp z = f z))).length →
        ringDot Fp kernel ≠ e_f) ∨
      (∀ Gp : List QuarticGoldilocks, Gp.length ≤ d + 1 →
        A - 1 ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs Gp z = g z))).length →
        ringDot Gp kernel ≠ e_g))
    (L_θ : List (Fin S.length)) (hNd : L_θ.Nodup)
    (hBadθ : ∀ iθ ∈ L_θ, ¬¬ ∃ H : List QuarticGoldilocks,
      H.length ≤ d + 1 ∧
      A ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs H z =
        CommRingOps.add (f z) (CommRingOps.mul (S.get iθ) (g z))))).length ∧
      ringDot H kernel = CommRingOps.add e_f (CommRingOps.mul (S.get iθ) e_g)) :
    L_θ.length ≤ badTheta +
      (gsDecodeList d (A - 1) D f).length * (gsDecodeList d (A - 1) D g).length := by
  let candF := gsDecodeList d (A - 1) D f
  let candG := gsDecodeList d (A - 1) D g
  let pairsFG := candF.flatMap (fun pF => candG.map (fun pG => (pF, pG)))
  have hPairsLen : pairsFG.length = candF.length * candG.length := by
    dsimp only [pairsFG]
    induction candF with
    | nil => simp
    | cons _ rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons, ih]
      rw [Nat.succ_mul, Nat.add_comm]
  let matchTheta : GsUniPoly QuarticGoldilocks × GsUniPoly QuarticGoldilocks → Fin S.length → Bool :=
    fun fg iθ =>
      decide (CommRingOps.add (ringDot fg.1.val kernel)
        (CommRingOps.mul (S.get iθ) (ringDot fg.2.val kernel)) =
        CommRingOps.add e_f (CommRingOps.mul (S.get iθ) e_g))
  let anyMatch : Fin S.length → Bool := fun iθ => pairsFG.any (fun fg => matchTheta fg iθ)
  have hSplit := length_filter_add_not anyMatch L_θ
  have hMatchLe : (L_θ.filter anyMatch).length ≤ pairsFG.length := by
    refine filter_any_le_mul_one pairsFG matchTheta L_θ ?_
    intro fg hfg
    rcases List.mem_flatMap.mp hfg with ⟨pF, hpFMem, hInG⟩
    rcases List.mem_map.mp hInG with ⟨pG, hpGMem, rfl⟩
    have hpFProps := (mem_gsDecodeList_iff f hD (by omega) pF).mp hpFMem
    have hpGProps := (mem_gsDecodeList_iff g hD (by omega) pG).mp hpGMem
    let Δ_f := CommRingOps.sub (ringDot pF.val kernel) e_f
    let Δ_g := CommRingOps.sub (ringDot pG.val kernel) e_g
    have hNz : Δ_f ≠ CommRingOps.zero ∨ Δ_g ≠ CommRingOps.zero := by
      rcases hInvalidFG with invF | invG
      · exact .inl (fun h0 => invF pF.val hpFProps.1 hpFProps.2 (LawfulCommRing.sub_eq_zero_iff.mp h0))
      · exact .inr (fun h0 => invG pG.val hpGProps.1 hpGProps.2 (LawfulCommRing.sub_eq_zero_iff.mp h0))
    have hEqFilt : L_θ.filter (matchTheta (pF, pG)) =
        L_θ.filter (fun iθ => decide (CommRingOps.add Δ_f (CommRingOps.mul (S.get iθ) Δ_g) = CommRingOps.zero)) := by
      apply congrArg (fun q => List.filter q L_θ)
      funext iθ
      dsimp only [matchTheta, Δ_f, Δ_g]
      if hEq : CommRingOps.add (ringDot pF.val kernel)
          (CommRingOps.mul (S.get iθ) (ringDot pG.val kernel)) =
          CommRingOps.add e_f (CommRingOps.mul (S.get iθ) e_g) then
        have h0 : CommRingOps.add (CommRingOps.sub (ringDot pF.val kernel) e_f)
            (CommRingOps.mul (S.get iθ) (CommRingOps.sub (ringDot pG.val kernel) e_g)) = CommRingOps.zero := by
          have hId : CommRingOps.add (CommRingOps.sub (ringDot pF.val kernel) e_f)
              (CommRingOps.mul (S.get iθ) (CommRingOps.sub (ringDot pG.val kernel) e_g)) =
            CommRingOps.sub
              (CommRingOps.add (ringDot pF.val kernel) (CommRingOps.mul (S.get iθ) (ringDot pG.val kernel)))
              (CommRingOps.add e_f (CommRingOps.mul (S.get iθ) e_g)) := by constructive_ring
          rw [hId, hEq, LawfulCommRing.sub_self]
        rw [decide_eq_true hEq, decide_eq_true h0]
      else
        have hNe0 : CommRingOps.add (CommRingOps.sub (ringDot pF.val kernel) e_f)
            (CommRingOps.mul (S.get iθ) (CommRingOps.sub (ringDot pG.val kernel) e_g)) ≠ CommRingOps.zero := by
          intro h0
          apply hEq
          have hId : CommRingOps.sub
              (CommRingOps.add (ringDot pF.val kernel) (CommRingOps.mul (S.get iθ) (ringDot pG.val kernel)))
              (CommRingOps.add e_f (CommRingOps.mul (S.get iθ) e_g)) =
            CommRingOps.add (CommRingOps.sub (ringDot pF.val kernel) e_f)
              (CommRingOps.mul (S.get iθ) (CommRingOps.sub (ringDot pG.val kernel) e_g)) := by constructive_ring
          exact LawfulCommRing.sub_eq_zero_iff.mp (hId.trans h0)
        rw [decide_eq_false hEq, decide_eq_false hNe0]
    rw [hEqFilt]
    exact linear_theta_fin_le_one S hS Δ_f Δ_g hNz L_θ hNd
  -- Embed non-matching `iθ` into `prodPool S` via `iθ ↦ (S.get iθ, 0)`:
  let embedZero : (iθ : Fin S.length) → { ch : Fin (prodPool S).length //
      (prodPool S).get ch = (S.get iθ, CommRingOps.zero) } :=
    fun iθ => findListMemIdx (S.get iθ, CommRingOps.zero) (prodPool S)
      (mem_prodPool_iff.mpr ⟨list_get_mem S iθ, hZeroS⟩)
  let L_non := L_θ.filter (fun iθ => !anyMatch iθ)
  let L_pool := L_non.map (fun iθ => (embedZero iθ).1)
  have hPoolNd : L_pool.Nodup := by
    refine List.Pairwise.map _ ?_ (List.Pairwise.filter _ hNd)
    intro i₁ i₂ hNe hEqIdx
    have hPairEq : (S.get i₁, (CommRingOps.zero : QuarticGoldilocks)) = (S.get i₂, CommRingOps.zero) :=
      (embedZero i₁).2.symm.trans ((congrArg (prodPool S).get hEqIdx).trans (embedZero i₂).2)
    exact hNe (nodup_get_inj hS (Prod.mk.inj hPairEq).1)
  have hNonLe : L_pool.length ≤ badTheta := by
    refine hDecompTheta (f, g) L_pool hPoolNd ?_
    intro ch hch hNo
    rcases List.mem_map.mp hch with ⟨iθ, hiθNon, rfl⟩
    rcases List.mem_filter.mp hiθNon with ⟨hiθL, hNotAny⟩
    have hChEq : (prodPool S).get (embedZero iθ).1 = (S.get iθ, CommRingOps.zero) := (embedZero iθ).2
    refine hBadθ iθ hiθL ?_
    rintro ⟨H, hHLen, hHAg, hHDot⟩
    refine hNo ⟨H, ?_, ?_⟩
    · unfold affineMcaAccepts
      rw [list_getD_eq_get (prodPool S) _ (embedZero iθ).1, hChEq]
      have hPredEq : (fun z => decide (RoundPoly.evalCoeffs H z =
          CommRingOps.add (f z) (CommRingOps.mul
            (CommRingOps.add (S.get iθ) (CommRingOps.mul CommRingOps.zero z)) (g z)))) =
          (fun z => decide (RoundPoly.evalCoeffs H z =
            CommRingOps.add (f z) (CommRingOps.mul (S.get iθ) (g z)))) := by
        funext z
        rw [LawfulCommRing.zero_mul, LawfulCommRing.add_zero]
      rw [hPredEq]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨(embedZero iθ).1.2, Nat.le_trans hHLen (Nat.le_succ _)⟩, hHAg⟩
    · rintro ⟨F_poly, G_poly, ⟨hFLen, hGLen, hJoint⟩, hTrimEq⟩
      rw [hChEq] at hTrimEq
      -- Degree collapse: `F_sub := H - θ * G_poly` has length `≤ d + 1` and agrees everywhere with `F_poly`!
      let F_sub := polySubVar H (polyScaleVar (S.get iθ) G_poly)
      have hScaleLen : (polyScaleVar (S.get iθ) G_poly).length ≤ d + 1 := by
        rw [polyScaleVar_length]; exact hGLen
      have hFsubLen : F_sub.length ≤ d + 1 := polySubVar_length_le H _ (d + 1) hHLen hScaleLen
      have hAgreeAll : ∀ z ∈ D, RoundPoly.evalCoeffs F_poly z = RoundPoly.evalCoeffs F_sub z := by
        intro z _
        have hEvH : RoundPoly.evalCoeffs H z =
            CommRingOps.add (RoundPoly.evalCoeffs F_poly z)
              (CommRingOps.mul (S.get iθ) (RoundPoly.evalCoeffs G_poly z)) := by
          rw [← evalCoeffs_trimPoly z H, hTrimEq, evalCoeffs_trimPoly,
              evalCoeffs_polyAddVar, evalCoeffs_polyAddVar,
              evalCoeffs_polyScaleVar, evalCoeffs_polyScaleVar,
              LawfulCommRing.zero_mul, LawfulCommRing.add_zero]
        dsimp only [F_sub]
        rw [evalCoeffs_polySubVar, evalCoeffs_polyScaleVar, hEvH]
        constructive_ring
      have hTrimFEq : trimPoly F_poly = trimPoly F_sub :=
        trimPoly_eq_of_agree_on_nodup (d := d + 1) hFLen
          (Nat.le_trans hFsubLen (Nat.le_succ _)) hD (by omega) hAgreeAll
      let pF : GsUniPoly QuarticGoldilocks := GsUniPoly.ofCoeffs F_poly
      let pG : GsUniPoly QuarticGoldilocks := GsUniPoly.ofCoeffs G_poly
      have hpFLen : pF.val.length ≤ d + 1 := by
        change (trimPoly F_poly).length ≤ d + 1
        rw [hTrimFEq]
        exact Nat.le_trans (trimPoly_length_le F_sub) hFsubLen
      have hJointF : A - 1 ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs pF.val z = f z))).length := by
        refine Nat.le_trans hJoint (nodup_length_le_of_subset (List.Pairwise.filter _ hD) ?_)
        intro z hz
        rcases List.mem_filter.mp hz with ⟨hzD, hB⟩
        refine List.mem_filter.mpr ⟨hzD, decide_eq_true ?_⟩
        change RoundPoly.evalCoeffs (trimPoly F_poly) z = f z
        rw [evalCoeffs_trimPoly]
        exact of_decide_eq_true ((Bool.and_eq_true _ _).mp hB).1
      have hJointG : A - 1 ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs pG.val z = g z))).length := by
        refine Nat.le_trans hJoint (nodup_length_le_of_subset (List.Pairwise.filter _ hD) ?_)
        intro z hz
        rcases List.mem_filter.mp hz with ⟨hzD, hB⟩
        refine List.mem_filter.mpr ⟨hzD, decide_eq_true ?_⟩
        change RoundPoly.evalCoeffs (trimPoly G_poly) z = g z
        rw [evalCoeffs_trimPoly]
        exact of_decide_eq_true ((Bool.and_eq_true _ _).mp hB).2
      have hpFMem : pF ∈ candF :=
        (mem_gsDecodeList_iff f hD (by omega) pF).mpr ⟨hpFLen, hJointF⟩
      have hpGMem : pG ∈ candG :=
        (mem_gsDecodeList_iff g hD (by omega) pG).mpr
          ⟨Nat.le_trans (trimPoly_length_le G_poly) hGLen, hJointG⟩
      have hZeroScale : polyScaleVar (CommRingOps.zero : QuarticGoldilocks) (shiftPoly G_poly) =
          (shiftPoly G_poly).map (fun _ => CommRingOps.zero) := by
        rw [polyScaleVar_def]
        apply List.map_congr_left
        intro a _; exact LawfulCommRing.zero_mul a
      have hDotZero : ringDot (polyScaleVar (CommRingOps.zero : QuarticGoldilocks) (shiftPoly G_poly)) kernel =
          CommRingOps.zero := by
        rw [ringDot_polyScaleVar, LawfulCommRing.zero_mul]
      have hDotEq : CommRingOps.add (ringDot pF.val kernel)
          (CommRingOps.mul (S.get iθ) (ringDot pG.val kernel)) =
          CommRingOps.add e_f (CommRingOps.mul (S.get iθ) e_g) := by
        change CommRingOps.add (ringDot (trimPoly F_poly) kernel)
            (CommRingOps.mul (S.get iθ) (ringDot (trimPoly G_poly) kernel)) = _
        rw [ringDot_trimPoly_eq, ringDot_trimPoly_eq]
        have hDT := congrArg (fun u => ringDot u kernel) hTrimEq
        rw [ringDot_trimPoly_eq, ringDot_trimPoly_eq,
            ringDot_polyAddVar, ringDot_polyAddVar,
            ringDot_polyScaleVar, hDotZero, LawfulCommRing.add_zero] at hDT
        exact hDT.symm.trans hHDot
      have hMemP : (pF, pG) ∈ pairsFG :=
        List.mem_flatMap.mpr ⟨pF, hpFMem, List.mem_map.mpr ⟨pG, hpGMem, rfl⟩⟩
      have hAnyTrue : anyMatch iθ = true :=
        List.any_eq_true.mpr ⟨(pF, pG), hMemP, decide_eq_true hDotEq⟩
      rw [hAnyTrue] at hNotAny
      exact absurd hNotAny (by decide)
  have hLenPool : L_pool.length = L_non.length := List.length_map _
  rw [hLenPool] at hNonLe
  rw [hPairsLen] at hMatchLe
  dsimp only [candF, candG, L_non] at hMatchLe hNonLe
  omega

private theorem nodup_map_snd_filter_fst {α β : Type} [DecidableEq α] (a : α) :
    ∀ (xs : List (α × β)), xs.Nodup →
      ((xs.filter (fun p => decide (p.1 = a))).map Prod.snd).Nodup
  | [], _ => .nil
  | (x, y) :: tl, hNd => by
    obtain ⟨hNotIn, hTlNd⟩ := List.pairwise_cons.mp hNd
    if hx : x = a then
      simp only [List.filter_cons, decide_eq_true hx, ↓reduceIte, List.map_cons]
      refine List.pairwise_cons.mpr ⟨?_, nodup_map_snd_filter_fst a tl hTlNd⟩
      intro y' hy' hEqY
      rcases List.mem_map.mp hy' with ⟨⟨x', y''⟩, hMemF, hSnd⟩
      dsimp only at hSnd
      rcases List.mem_filter.mp hMemF with ⟨hMemTl, hDecX⟩
      have hxEq : x' = x := (of_decide_eq_true hDecX).trans hx.symm
      have hyEq : y'' = y := hSnd.trans hEqY.symm
      rw [hxEq, hyEq] at hMemTl
      exact hNotIn (x, y) hMemTl rfl
    else
      simp only [List.filter_cons, decide_eq_false hx, Bool.false_eq_true, ↓reduceIte]
      exact nodup_map_snd_filter_fst a tl hTlNd

/-- **Full Three-Challenge `(θ, α, β)` Equal-Degree Lift (`equal_degree_three_challenge_bound`)**:
    Eliminates `hInvalidMix` entirely by uniting `equal_degree_bad_theta_bound` (for `θ ∈ S`) with
    `claimFold_bad_pairs_bound` (for `(α, β) ∈ prodPool S` on every non-exceptional `θ`). -/
theorem equal_degree_three_challenge_bound
    (D S kernel : List QuarticGoldilocks) (d A badTheta badAlphaBeta maxMixList : Nat)
    (f g : QuarticGoldilocks → QuarticGoldilocks) (e_f e_g c_f c_g : QuarticGoldilocks)
    (hD : D.Nodup) (hS : S.Nodup) (hZeroS : (CommRingOps.zero : QuarticGoldilocks) ∈ S)
    (hdA : d + 3 ≤ A) (hAD : A ≤ D.length)
    (hDecompTheta : AffineFoldDecompBound D S (d + 1) A badTheta)
    (hDecompAB : AffineFoldDecompBound D S (d + 1) (A + 1) badAlphaBeta)
    (hMixList : ∀ θ : QuarticGoldilocks,
      (gsDecodeList d A D (fun z => CommRingOps.add (f z) (CommRingOps.mul θ (g z)))).length ≤ maxMixList)
    (hInvalidFG :
      (∀ Fp : List QuarticGoldilocks, Fp.length ≤ d + 1 →
        A - 1 ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs Fp z = f z))).length →
        ringDot Fp kernel ≠ e_f) ∨
      (∀ Gp : List QuarticGoldilocks, Gp.length ≤ d + 1 →
        A - 1 ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs Gp z = g z))).length →
        ringDot Gp kernel ≠ e_g))
    (triples : List (Fin S.length × Fin (prodPool S).length)) (hNd : triples.Nodup)
    (hFlip : ∀ tr ∈ triples, ¬¬ ∃ P : List QuarticGoldilocks,
      affineMcaAccepts D S (d + 1) (A + 1)
        (g, fun z => CommRingOps.add (f z) (CommRingOps.mul (S.get tr.1) (g z))) tr.2.1 P = true ∧
      ringDot P kernel = hemFoldClaimUpdate e_f e_g c_f c_g (S.get tr.1)
        ((prodPool S).get tr.2).1 ((prodPool S).get tr.2).2) :
    triples.length ≤
      (badTheta + (gsDecodeList d (A - 1) D f).length * (gsDecodeList d (A - 1) D g).length) *
        (prodPool S).length +
      S.length * (badAlphaBeta + (gsDecodeList (d + 1) A D g).length * maxMixList * S.length) := by
  let isExcTheta : Fin S.length → Bool := fun iθ =>
    let θ := S.get iθ
    let mixWord := fun z => CommRingOps.add (f z) (CommRingOps.mul θ (g z))
    (gsDecodeList d A D mixWord).any (fun pH =>
      decide (ringDot pH.val kernel = CommRingOps.add e_f (CommRingOps.mul θ e_g)))
  let excThetas := (List.finRange S.length).filter isExcTheta
  have hExcBound : excThetas.length ≤
      badTheta + (gsDecodeList d (A - 1) D f).length * (gsDecodeList d (A - 1) D g).length := by
    refine equal_degree_bad_theta_bound D S kernel d A badTheta f g e_f e_g
      hD hS hZeroS hdA hAD hDecompTheta hInvalidFG excThetas
      (List.Pairwise.filter _ (List.nodup_finRange S.length)) ?_
    intro iθ hiθ hNo
    have hAny : isExcTheta iθ = true := (List.mem_filter.mp hiθ).2
    rcases List.any_eq_true.mp hAny with ⟨pH, hpHMem, hpHDot⟩
    have hpHProps := (mem_gsDecodeList_iff _ hD (by omega) pH).mp hpHMem
    exact hNo ⟨pH.val, hpHProps.1, hpHProps.2, of_decide_eq_true hpHDot⟩
  have hSplit := length_filter_add_not (fun tr => isExcTheta tr.1) triples
  have hExcTriples : (triples.filter (fun tr => isExcTheta tr.1)).length ≤
      excThetas.length * (prodPool S).length := by
    let allPool := List.finRange (prodPool S).length
    let box := excThetas.flatMap (fun iθ => allPool.map (fun ch => (iθ, ch)))
    have hBoxLen : box.length = excThetas.length * (prodPool S).length := by
      dsimp only [box]
      have hAP : allPool.length = (prodPool S).length := List.length_finRange
      induction excThetas with
      | nil => simp
      | cons _ tl ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons, ih, hAP]
        rw [Nat.succ_mul, Nat.add_comm]
    rw [← hBoxLen]
    refine nodup_length_le_of_subset (List.Pairwise.filter _ hNd) ?_
    intro tr htr
    rcases List.mem_filter.mp htr with ⟨_, hEx⟩
    exact List.mem_flatMap.mpr ⟨tr.1, List.mem_filter.mpr ⟨List.mem_finRange tr.1, hEx⟩,
      List.mem_map.mpr ⟨tr.2, List.mem_finRange tr.2, rfl⟩⟩
  let goodTriples := triples.filter (fun tr => !isExcTheta tr.1)
  have hGoodPerTheta : ∀ iθ : Fin S.length,
      (goodTriples.filter (fun tr => decide (tr.1 = iθ))).length ≤
        badAlphaBeta + (gsDecodeList (d + 1) A D g).length * maxMixList * S.length := by
    intro iθ
    cases hIsEx : isExcTheta iθ
    · let θ := S.get iθ
      let mixWord := fun z => CommRingOps.add (f z) (CommRingOps.mul θ (g z))
      have hInvMix : ∀ G : List QuarticGoldilocks, G.length ≤ d + 1 →
          A ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs G z = mixWord z))).length →
          ringDot G kernel ≠ CommRingOps.add e_f (CommRingOps.mul θ e_g) := by
        intro G hGLen hGAg hGDot
        let pG : GsUniPoly QuarticGoldilocks := GsUniPoly.ofCoeffs G
        have hpGAg : A ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs pG.val z = mixWord z))).length := by
          have hEqF : D.filter (fun z => decide (RoundPoly.evalCoeffs pG.val z = mixWord z)) =
              D.filter (fun z => decide (RoundPoly.evalCoeffs G z = mixWord z)) :=
            congrArg (fun q => List.filter q D) (funext fun z => by
              show decide (RoundPoly.evalCoeffs (trimPoly G) z = mixWord z) = _
              rw [evalCoeffs_trimPoly])
          rw [hEqF]; exact hGAg
        have hpGMem : pG ∈ gsDecodeList d A D mixWord :=
          (mem_gsDecodeList_iff mixWord hD (by omega) pG).mpr
            ⟨Nat.le_trans (trimPoly_length_le G) hGLen, hpGAg⟩
        have hpGDot : ringDot pG.val kernel = CommRingOps.add e_f (CommRingOps.mul θ e_g) := by
          change ringDot (trimPoly G) kernel = _
          rw [ringDot_trimPoly_eq]; exact hGDot
        have hExTrue : isExcTheta iθ = true :=
          List.any_eq_true.mpr ⟨pG, hpGMem, decide_eq_true hpGDot⟩
        rw [hExTrue] at hIsEx
        exact Bool.noConfusion hIsEx
      let slice := (goodTriples.filter (fun tr => decide (tr.1 = iθ))).map Prod.snd
      have hSliceNd : slice.Nodup :=
        nodup_map_snd_filter_fst iθ goodTriples (List.Pairwise.filter _ hNd)
      have hSliceBound := claimFold_bad_pairs_bound D S kernel d A badAlphaBeta
        g mixWord e_g (CommRingOps.add e_f (CommRingOps.mul θ e_g))
        (CommRingOps.add c_f (CommRingOps.mul θ c_g))
        hD hS (Nat.le_of_succ_le hdA) hDecompAB hInvMix slice hSliceNd
        (fun ch hch hNo => by
          rcases List.mem_map.mp hch with ⟨tr, htrF, rfl⟩
          rcases List.mem_filter.mp htrF with ⟨htrGood, hTr1⟩
          have hTrMem : tr ∈ triples := (List.mem_filter.mp htrGood).1
          have hEq1 : tr.1 = iθ := of_decide_eq_true hTr1
          refine hFlip tr hTrMem (fun ⟨P, hPAcc, hPDot⟩ => hNo ⟨P, ?_, ?_⟩)
          · rw [hEq1] at hPAcc; exact hPAcc
          · rw [hEq1] at hPDot; rw [hPDot, hemFoldClaimUpdate_def])
      have hLenEq : slice.length = (goodTriples.filter (fun tr => decide (tr.1 = iθ))).length :=
        List.length_map _
      rw [hLenEq] at hSliceBound
      have hMixLe := hMixList θ
      have hTermLe : (gsDecodeList (d + 1) A D g).length * (gsDecodeList d A D mixWord).length * S.length ≤
          (gsDecodeList (d + 1) A D g).length * maxMixList * S.length :=
        Nat.mul_le_mul_right S.length (Nat.mul_le_mul_left _ hMixLe)
      exact Nat.le_trans hSliceBound (Nat.add_le_add_left hTermLe badAlphaBeta)
    · have hEmpty : goodTriples.filter (fun tr => decide (tr.1 = iθ)) = [] := by
        have hAux : ∀ xs : List (Fin S.length × Fin (prodPool S).length),
            (∀ t ∈ xs, !isExcTheta t.1 = true) →
            xs.filter (fun tr => decide (tr.1 = iθ)) = [] := by
          intro xs hAll; induction xs with
          | nil => rfl
          | cons hd tl ih =>
            have hHd := hAll hd (.head tl)
            if hE : hd.1 = iθ then
              rw [hE, hIsEx] at hHd; cases hHd
            else
              simp only [List.filter_cons, decide_eq_false hE, Bool.false_eq_true, ↓reduceIte]
              exact ih (fun u hu => hAll u (.tail hd hu))
        exact hAux goodTriples (fun t ht => (List.mem_filter.mp ht).2)
      rw [hEmpty]; exact Nat.zero_le _
  have hGoodCover : goodTriples =
      goodTriples.filter (fun tr => (List.finRange S.length).any (fun iθ => decide (tr.1 = iθ))) := by
    have hAllTrue : ∀ xs : List (Fin S.length × Fin (prodPool S).length),
        xs = xs.filter (fun tr => (List.finRange S.length).any (fun iθ => decide (tr.1 = iθ))) := by
      intro xs; induction xs with
      | nil => rfl
      | cons hd tl ih =>
        have hAny : (List.finRange S.length).any (fun iθ => decide (hd.1 = iθ)) = true :=
          List.any_eq_true.mpr ⟨hd.1, List.mem_finRange hd.1, decide_eq_true rfl⟩
        simp only [List.filter_cons, hAny, ↓reduceIte]
        exact congrArg (hd :: ·) ih
    exact hAllTrue goodTriples
  have hGoodTotal : goodTriples.length ≤
      S.length * (badAlphaBeta + (gsDecodeList (d + 1) A D g).length * maxMixList * S.length) := by
    have hF := filter_any_length_le_mul (List.finRange S.length)
      (fun iθ (tr : Fin S.length × Fin (prodPool S).length) => decide (tr.1 = iθ))
      goodTriples
      (badAlphaBeta + (gsDecodeList (d + 1) A D g).length * maxMixList * S.length)
      (fun iθ _ => hGoodPerTheta iθ)
    rw [← hGoodCover, List.length_finRange] at hF
    exact hF
  have hExcProd : (triples.filter (fun tr => isExcTheta tr.1)).length ≤
      (badTheta + (gsDecodeList d (A - 1) D f).length * (gsDecodeList d (A - 1) D g).length) *
        (prodPool S).length :=
    Nat.le_trans hExcTriples (Nat.mul_le_mul_right (prodPool S).length hExcBound)
  dsimp only [goodTriples] at hGoodTotal
  omega

/-- Specialization of `equal_degree_three_challenge_bound` to `slicedParamsOk` certificates at
    agreement thresholds `A` (for the `θ`-exception slice) and `A + 1` (for the `(α, β)` fold). -/
theorem sliced_equal_degree_theta_slice_challenge_bound
    (D S kernel : List QuarticGoldilocks)
    (d A B₀ m₀ Dy₀ B₁ m₁ Dy₁ maxMixList : Nat)
    (f g : QuarticGoldilocks → QuarticGoldilocks) (e_f e_g c_f c_g : QuarticGoldilocks)
    (hD : D.Nodup) (hS : S.Nodup) (hZeroS : (CommRingOps.zero : QuarticGoldilocks) ∈ S)
    (hdA : d + 3 ≤ A) (hAD : A ≤ D.length)
    (hParamsTheta : slicedParamsOk D.length (d + 1) A B₀ m₀ Dy₀ = true)
    (hParamsAB : slicedParamsOk D.length (d + 1) (A + 1) B₁ m₁ Dy₁ = true)
    (hMixList : ∀ θ : QuarticGoldilocks,
      (gsDecodeList d A D (fun z => CommRingOps.add (f z) (CommRingOps.mul θ (g z)))).length ≤ maxMixList)
    (hInvalidFG :
      (∀ Fp : List QuarticGoldilocks, Fp.length ≤ d + 1 →
        A - 1 ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs Fp z = f z))).length →
        ringDot Fp kernel ≠ e_f) ∨
      (∀ Gp : List QuarticGoldilocks, Gp.length ≤ d + 1 →
        A - 1 ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs Gp z = g z))).length →
        ringDot Gp kernel ≠ e_g))
    (triples : List (Fin S.length × Fin (prodPool S).length)) (hNd : triples.Nodup)
    (hFlip : ∀ tr ∈ triples, ¬¬ ∃ P : List QuarticGoldilocks,
      affineMcaAccepts D S (d + 1) (A + 1)
        (g, fun z => CommRingOps.add (f z) (CommRingOps.mul (S.get tr.1) (g z))) tr.2.1 P = true ∧
      ringDot P kernel = hemFoldClaimUpdate e_f e_g c_f c_g (S.get tr.1)
        ((prodPool S).get tr.2).1 ((prodPool S).get tr.2).2) :
    let badTheta := Dy₀ + slicedRest D.length (d + 1) A B₀ (m₀ * A - Dy₀) Dy₀ S.length
    let badAB := Dy₁ + slicedRest D.length (d + 1) (A + 1) B₁ (m₁ * (A + 1) - Dy₁) Dy₁ S.length
    triples.length ≤
      (badTheta + (gsDecodeList d (A - 1) D f).length * (gsDecodeList d (A - 1) D g).length) *
        (prodPool S).length +
      S.length * (badAB + (gsDecodeList (d + 1) A D g).length * maxMixList * S.length) :=
  equal_degree_three_challenge_bound D S kernel d A _ _ maxMixList f g e_f e_g c_f c_g
    hD hS hZeroS hdA hAD
    (slicedParamsOk_sound D.length (d + 1) A B₀ m₀ Dy₀ hParamsTheta D S hD hS rfl)
    (slicedParamsOk_sound D.length (d + 1) (A + 1) B₁ m₁ Dy₁ hParamsAB D S hD hS rfl)
    hMixList hInvalidFG triples hNd hFlip

/-! ## §2. Arbitrary-Batch (`1 ≤ m ≤ 16`) Multi-Stage `verifyHemAffineWhir` & Extracted-Opening Bridge -/

private theorem evalCascadeClaim_set_split :
    ∀ (es shifts : List QuarticGoldilocks)
      (ws : List (QuarticGoldilocks × QuarticGoldilocks))
      (i : Nat) (p : QuarticGoldilocks × QuarticGoldilocks),
      i < es.length → es.length = shifts.length → shifts.length = ws.length →
      evalCascadeClaim es shifts (ws.set i p) =
        CommRingOps.add
          (evalCascadeClaim es shifts (ws.set i (CommRingOps.zero, CommRingOps.zero)))
          (CommRingOps.add
            (CommRingOps.mul p.1 (es.getD i CommRingOps.zero))
            (CommRingOps.mul p.2 (shifts.getD i CommRingOps.zero)))
  | [], _, _, _, _, hi, _, _ => nomatch hi
  | _ :: _, [], _, _, _, _, hES, _ => nomatch hES
  | _ :: _, _ :: _, [], _, _, _, _, hSW => nomatch hSW
  | e :: es, s :: shifts, _ :: ws, 0, (α, β), _, _, _ => by
    simp only [List.set_cons_zero, evalCascadeClaim_cons, List.getD, List.getElem?_cons_zero, Option.getD_some]
    constructive_ring
  | e :: es, s :: shifts, w :: ws, i + 1, p, hi, hES, hSW => by
    rcases w with ⟨α₀, β₀⟩
    have ih := evalCascadeClaim_set_split es shifts ws i p
      (Nat.lt_of_succ_lt_succ hi) (Nat.succ.inj hES) (Nat.succ.inj hSW)
    simp only [List.set_cons_succ, evalCascadeClaim_cons, List.getD, List.getElem?_cons_succ] at ih ⊢
    rw [ih]
    constructive_ring

private theorem evalCascadeOracle_set_split (domPts : List QuarticGoldilocks) :
    ∀ (os : List (Nat → QuarticGoldilocks))
      (ws : List (QuarticGoldilocks × QuarticGoldilocks))
      (i idx : Nat) (p : QuarticGoldilocks × QuarticGoldilocks),
      i < os.length → os.length = ws.length →
      evalCascadeOracle domPts os (ws.set i p) idx =
        CommRingOps.add
          (evalCascadeOracle domPts os (ws.set i (CommRingOps.zero, CommRingOps.zero)) idx)
          (CommRingOps.mul
            (CommRingOps.add p.1 (CommRingOps.mul p.2 (domPts.getD idx CommRingOps.zero)))
            ((os.getD i (fun _ => CommRingOps.zero)) idx))
  | [], _, _, _, _, hi, _ => nomatch hi
  | _ :: _, [], _, _, _, _, hOW => nomatch hOW
  | O :: os, _ :: ws, 0, idx, (α, β), _, _ => by
    simp only [List.set_cons_zero, evalCascadeOracle_cons, List.getD, List.getElem?_cons_zero, Option.getD_some]
    constructive_ring
  | O :: os, w :: ws, i + 1, idx, p, hi, hOW => by
    rcases w with ⟨α₀, β₀⟩
    have ih := evalCascadeOracle_set_split domPts os ws i idx p
      (Nat.lt_of_succ_lt_succ hi) (Nat.succ.inj hOW)
    simp only [List.set_cons_succ, evalCascadeOracle_cons]
    have hGet : (O :: os).getD (i + 1) (fun _ => CommRingOps.zero) =
        os.getD i (fun _ => CommRingOps.zero) := by
      simp only [List.getD, List.getElem?_cons_succ]
    rw [ih, hGet]
    constructive_ring

private theorem lookupDomOracle_evalCascadeOracle_set
    (domPts : List QuarticGoldilocks) (hDom : domPts.Nodup)
    (os : List (Nat → QuarticGoldilocks))
    (ws : List (QuarticGoldilocks × QuarticGoldilocks))
    (i : Nat) (p : QuarticGoldilocks × QuarticGoldilocks)
    (hi : i < os.length) (hOW : os.length = ws.length)
    (z : QuarticGoldilocks) (hz : z ∈ domPts) :
    lookupDomOracle domPts (evalCascadeOracle domPts os (ws.set i p)) z =
      CommRingOps.add
        (lookupDomOracle domPts
          (evalCascadeOracle domPts os (ws.set i (CommRingOps.zero, CommRingOps.zero))) z)
        (CommRingOps.mul
          (CommRingOps.add p.1 (CommRingOps.mul p.2 z))
          (lookupDomOracle domPts (os.getD i (fun _ => CommRingOps.zero)) z)) := by
  let ⟨idx, hIdxEq⟩ := findListMemIdx z domPts hz
  rw [← hIdxEq,
      lookupDomOracle_get domPts _ hDom idx,
      lookupDomOracle_get domPts _ hDom idx,
      lookupDomOracle_get domPts _ hDom idx,
      evalCascadeOracle_set_split domPts os ws i idx.1 p hi hOW,
      list_getD_eq_get domPts CommRingOps.zero idx]

/-- **Arbitrary-Batch (`1 ≤ m ≤ 16`), Multi-Stage `verifyHemAffineWhir` Cascade Fiber Bound
    (`arbitrary_batch_cascade_fiber_bound`)**:
    For ANY `inst : HemWhirInstance QuarticGoldilocks` with `1 ≤ m ≤ 16` batch oracles, ANY stage
    schedule `inst.stages`, `inst.initDomainPts.Nodup`, `inst.initDegBound + 3 ≤ inst.initMinAgree`,
    and `¬ HemStatementValid { inst with initMinAgree := inst.initMinAgree - 1 }` (accounting for
    the legacy, weaker input premise; the verifier now increments agreement at `.cascade`), constructively extracts an
    invalid coordinate `i₀ < m` such that for ANY fixed `m - 1` sibling weights (`baseWeights`) and
    ANY adaptive continuation `(decoded, rest)`, at most `badMca + listRest · listTarget · |S|`
    challenge pairs `ch ∈ L` pass `verifyHemAffineWhir`. -/
theorem arbitrary_batch_cascade_fiber_bound
    (inst : HemWhirInstance QuarticGoldilocks)
    (S : List QuarticGoldilocks) (badMca : Nat)
    (shifts : List QuarticGoldilocks)
    (baseWeights : List (QuarticGoldilocks × QuarticGoldilocks))
    (hShape : 1 ≤ inst.batchOracles.length ∧ inst.batchOracles.length ≤ 16)
    (hArity : inst.batchClaims.length = inst.batchOracles.length)
    (hShifts : shifts.length = inst.batchClaims.length)
    (hWeights : baseWeights.length = inst.batchClaims.length)
    (hDom : inst.initDomainPts.Nodup) (hS : S.Nodup)
    (hEnough : inst.initDegBound + 3 ≤ inst.initMinAgree)
    (hDecomp : AffineFoldDecompBound inst.initDomainPts S
      (inst.initDegBound + 1) inst.initMinAgree badMca)
    (hInvalid : ¬ HemStatementValid { inst with initMinAgree := inst.initMinAgree - 1 }) :
    ∃ i₀ : Nat, i₀ < inst.batchOracles.length ∧
      ∀ (decoded : QuarticGoldilocks × QuarticGoldilocks → List (List QuarticGoldilocks))
        (rest : QuarticGoldilocks × QuarticGoldilocks → List (HemTranscriptRound QuarticGoldilocks))
        (L : List (Fin (prodPool S).length)),
        L.Nodup →
        (∀ ch ∈ L, verifyHemAffineWhir inst
          (.cascade shifts (baseWeights.set i₀ ((prodPool S).get ch))
            (decoded ((prodPool S).get ch)) :: rest ((prodPool S).get ch)) = true) →
        L.length ≤ badMca +
          (gsDecodeList (inst.initDegBound + 1) (inst.initMinAgree - 1) inst.initDomainPts
            (lookupDomOracle inst.initDomainPts
              (evalCascadeOracle inst.initDomainPts inst.batchOracles
                (baseWeights.set i₀ (CommRingOps.zero, CommRingOps.zero))))).length *
          (gsDecodeList inst.initDegBound (inst.initMinAgree - 1) inst.initDomainPts
            (lookupDomOracle inst.initDomainPts
              (inst.batchOracles.getD i₀ (fun _ => CommRingOps.zero)))).length *
          S.length := by
  have hNotBatch : ¬ HemBatchValid inst.initDomainPts (inst.initMinAgree - 1) inst.initDegBound
      inst.initKernel inst.batchOracles inst.batchClaims :=
    fun hb => hInvalid ((HemStatementValid_iff _).mpr ⟨hShape, hb⟩)
  obtain ⟨i₀, hi₀Lt, hi₀Inv⟩ := exists_invalid_batch_coordinate inst.initDomainPts
    (inst.initMinAgree - 1) inst.initDegBound inst.initKernel hDom (by omega)
    inst.batchOracles inst.batchClaims hArity.symm hNotBatch
  refine ⟨i₀, hi₀Lt, ?_⟩
  intro decoded rest L hNd hAcc
  let domPts := inst.initDomainPts
  let d₀ := inst.initDegBound
  let A₀ := inst.initMinAgree
  have hA : (A₀ - 1) + 1 = A₀ := by omega
  have hOW : inst.batchOracles.length = baseWeights.length := hArity.symm.trans hWeights.symm
  have hi₀Claims : i₀ < inst.batchClaims.length := hArity.symm ▸ hi₀Lt
  let restOracle := evalCascadeOracle domPts inst.batchOracles
    (baseWeights.set i₀ (CommRingOps.zero, CommRingOps.zero))
  let fWord := lookupDomOracle domPts restOracle
  let O_target := inst.batchOracles.getD i₀ (fun _ => CommRingOps.zero)
  let gWord := lookupDomOracle domPts O_target
  let e_f := evalCascadeClaim inst.batchClaims shifts
    (baseWeights.set i₀ (CommRingOps.zero, CommRingOps.zero))
  let e_g := inst.batchClaims.getD i₀ CommRingOps.zero
  let s_g := shifts.getD i₀ CommRingOps.zero
  have hInvalidG : ∀ G : List QuarticGoldilocks, G.length ≤ d₀ + 1 →
      A₀ - 1 ≤ (domPts.filter (fun z => decide (RoundPoly.evalCoeffs G z = gWord z))).length →
      ringDot G inst.initKernel ≠ e_g := by
    intro G hGLen hGAg hGDot
    have hVal : polyWitnessValid domPts (A₀ - 1) d₀ O_target inst.initKernel e_g G = true := by
      rw [polyWitnessValid_def, hemCosetAgreeCount_eq_filter_lookup domPts O_target G hDom]
      dsimp only [gWord] at hGAg
      rw [decide_eq_true hGLen, decide_eq_true hGAg, decide_eq_true hGDot]
      rfl
    rw [hi₀Inv G] at hVal
    exact Bool.noConfusion hVal
  have hDecompPrev : AffineFoldDecompBound domPts S (d₀ + 1) ((A₀ - 1) + 1) badMca :=
    hA.symm ▸ hDecomp
  refine claimFold_bad_pairs_bound domPts S inst.initKernel d₀ (A₀ - 1) badMca
    fWord gWord e_f e_g s_g hDom hS (by omega) hDecompPrev hInvalidG L hNd ?_
  intro ch hch hNo
  obtain ⟨_, _, _, P, _, hPV⟩ :=
    verifyHemAffineWhir_cascade_witness inst shifts
      (baseWeights.set i₀ ((prodPool S).get ch))
      (decoded ((prodPool S).get ch)) (rest ((prodPool S).get ch)) (hAcc ch hch)
  rw [polyWitnessValid_def] at hPV
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hPV
  rcases hPV with ⟨⟨hPLen, hPAg⟩, hPDot⟩
  rw [hemCosetAgreeCount_eq_filter_lookup domPts _ P hDom] at hPAg
  refine hNo ⟨P, ?_, ?_⟩
  · unfold affineMcaAccepts
    rw [list_getD_eq_get (prodPool S) _ ch, hA]
    dsimp only [domPts, d₀, A₀, fWord, gWord, restOracle, O_target] at hPLen hPAg ⊢
    have hEqFilt : inst.initDomainPts.filter (fun z =>
        decide (RoundPoly.evalCoeffs P z =
          CommRingOps.add
            (lookupDomOracle inst.initDomainPts
              (evalCascadeOracle inst.initDomainPts inst.batchOracles
                (baseWeights.set i₀ (CommRingOps.zero, CommRingOps.zero))) z)
            (CommRingOps.mul (CommRingOps.add ((prodPool S).get ch).1
              (CommRingOps.mul ((prodPool S).get ch).2 z))
              (lookupDomOracle inst.initDomainPts
                (inst.batchOracles.getD i₀ (fun _ => CommRingOps.zero)) z)))) =
        inst.initDomainPts.filter (fun z =>
          decide (RoundPoly.evalCoeffs P z =
            lookupDomOracle inst.initDomainPts
              (evalCascadeOracle inst.initDomainPts inst.batchOracles
                (baseWeights.set i₀ ((prodPool S).get ch))) z)) := by
      have hMemCongr : ∀ xs : List QuarticGoldilocks, (∀ z ∈ xs, z ∈ inst.initDomainPts) →
          xs.filter (fun z =>
            decide (RoundPoly.evalCoeffs P z =
              CommRingOps.add
                (lookupDomOracle inst.initDomainPts
                  (evalCascadeOracle inst.initDomainPts inst.batchOracles
                    (baseWeights.set i₀ (CommRingOps.zero, CommRingOps.zero))) z)
                (CommRingOps.mul (CommRingOps.add ((prodPool S).get ch).1
                  (CommRingOps.mul ((prodPool S).get ch).2 z))
                  (lookupDomOracle inst.initDomainPts
                    (inst.batchOracles.getD i₀ (fun _ => CommRingOps.zero)) z)))) =
          xs.filter (fun z =>
            decide (RoundPoly.evalCoeffs P z =
              lookupDomOracle inst.initDomainPts
                (evalCascadeOracle inst.initDomainPts inst.batchOracles
                  (baseWeights.set i₀ ((prodPool S).get ch))) z)) := by
        intro xs hSub; induction xs with
        | nil => rfl
        | cons z zs ih =>
          have hValEq := lookupDomOracle_evalCascadeOracle_set inst.initDomainPts hDom
            inst.batchOracles baseWeights i₀ ((prodPool S).get ch)
            hi₀Lt hOW z (hSub z (.head zs))
          simp only [List.filter_cons, hValEq, ih (fun y hy => hSub y (.tail z hy))]
      exact hMemCongr inst.initDomainPts (fun _ h => h)
    rw [hEqFilt, decide_eq_true ch.2, decide_eq_true hPLen, decide_eq_true hPAg]
    rfl
  · rw [hPDot, evalCascadeClaim_set_split inst.batchClaims shifts baseWeights
      i₀ ((prodPool S).get ch) hi₀Claims hShifts.symm (hShifts.trans hWeights.symm)]

/-- Strengthened cascade fiber bound: the input is invalid at its actual agreement
    threshold. The non-exhaustive slack premise makes the transition exactly A + 1,
    so no stronger invalidity assumption at A - 1 is needed. -/
theorem arbitrary_batch_incremented_cascade_fiber_bound
    (inst : HemWhirInstance QuarticGoldilocks)
    (S : List QuarticGoldilocks) (badMca : Nat)
    (shifts : List QuarticGoldilocks)
    (baseWeights : List (QuarticGoldilocks × QuarticGoldilocks))
    (hShape : 1 ≤ inst.batchOracles.length ∧ inst.batchOracles.length ≤ 16)
    (hArity : inst.batchClaims.length = inst.batchOracles.length)
    (hShifts : shifts.length = inst.batchClaims.length)
    (hWeights : baseWeights.length = inst.batchClaims.length)
    (hDom : inst.initDomainPts.Nodup) (hS : S.Nodup)
    (hEnough : inst.initDegBound + 2 ≤ inst.initMinAgree)
    (hSlack : inst.initMinAgree < inst.initDomainPts.length)
    (hDecomp : AffineFoldDecompBound inst.initDomainPts S
      (inst.initDegBound + 1) (inst.initMinAgree + 1) badMca)
    (hInvalid : ¬ HemStatementValid inst) :
    ∃ i₀ : Nat, i₀ < inst.batchOracles.length ∧
      ∀ (decoded : QuarticGoldilocks × QuarticGoldilocks → List (List QuarticGoldilocks))
        (rest : QuarticGoldilocks × QuarticGoldilocks → List (HemTranscriptRound QuarticGoldilocks))
        (L : List (Fin (prodPool S).length)),
        L.Nodup →
        (∀ ch ∈ L, verifyHemAffineWhir inst
          (.cascade shifts (baseWeights.set i₀ ((prodPool S).get ch))
            (decoded ((prodPool S).get ch)) :: rest ((prodPool S).get ch)) = true) →
        L.length ≤ badMca +
          (gsDecodeList (inst.initDegBound + 1) inst.initMinAgree inst.initDomainPts
            (lookupDomOracle inst.initDomainPts
              (evalCascadeOracle inst.initDomainPts inst.batchOracles
                (baseWeights.set i₀ (CommRingOps.zero, CommRingOps.zero))))).length *
          (gsDecodeList inst.initDegBound inst.initMinAgree inst.initDomainPts
            (lookupDomOracle inst.initDomainPts
              (inst.batchOracles.getD i₀ (fun _ => CommRingOps.zero)))).length *
          S.length := by
  have hNotBatch : ¬ HemBatchValid inst.initDomainPts inst.initMinAgree inst.initDegBound
      inst.initKernel inst.batchOracles inst.batchClaims :=
    fun hb => hInvalid ((HemStatementValid_iff _).mpr ⟨hShape, hb⟩)
  obtain ⟨i₀, hi₀Lt, hi₀Inv⟩ := exists_invalid_batch_coordinate inst.initDomainPts
    inst.initMinAgree inst.initDegBound inst.initKernel hDom (by omega)
    inst.batchOracles inst.batchClaims hArity.symm hNotBatch
  refine ⟨i₀, hi₀Lt, ?_⟩
  intro decoded rest L hNd hAcc
  let domPts := inst.initDomainPts
  let d₀ := inst.initDegBound
  let A₀ := inst.initMinAgree
  have hOW : inst.batchOracles.length = baseWeights.length := hArity.symm.trans hWeights.symm
  have hi₀Claims : i₀ < inst.batchClaims.length := hArity.symm ▸ hi₀Lt
  let restOracle := evalCascadeOracle domPts inst.batchOracles
    (baseWeights.set i₀ (CommRingOps.zero, CommRingOps.zero))
  let fWord := lookupDomOracle domPts restOracle
  let O_target := inst.batchOracles.getD i₀ (fun _ => CommRingOps.zero)
  let gWord := lookupDomOracle domPts O_target
  let e_f := evalCascadeClaim inst.batchClaims shifts
    (baseWeights.set i₀ (CommRingOps.zero, CommRingOps.zero))
  let e_g := inst.batchClaims.getD i₀ CommRingOps.zero
  let s_g := shifts.getD i₀ CommRingOps.zero
  have hInvalidG : ∀ G : List QuarticGoldilocks, G.length ≤ d₀ + 1 →
      A₀ ≤ (domPts.filter (fun z => decide (RoundPoly.evalCoeffs G z = gWord z))).length →
      ringDot G inst.initKernel ≠ e_g := by
    intro G hGLen hGAg hGDot
    have hVal : polyWitnessValid domPts A₀ d₀ O_target inst.initKernel e_g G = true := by
      rw [polyWitnessValid_def, hemCosetAgreeCount_eq_filter_lookup domPts O_target G hDom]
      dsimp only [gWord] at hGAg
      rw [decide_eq_true hGLen, decide_eq_true hGAg, decide_eq_true hGDot]
      rfl
    rw [hi₀Inv G] at hVal
    exact Bool.noConfusion hVal
  have hDecompPrev : AffineFoldDecompBound domPts S (d₀ + 1) (A₀ + 1) badMca :=
    hDecomp
  refine claimFold_bad_pairs_bound domPts S inst.initKernel d₀ A₀ badMca
    fWord gWord e_f e_g s_g hDom hS (by omega) hDecompPrev hInvalidG L hNd ?_
  intro ch hch hNo
  obtain ⟨_, _, _, P, _, hPV⟩ :=
    verifyHemAffineWhir_incremented_cascade_witness inst shifts
      (baseWeights.set i₀ ((prodPool S).get ch))
      (decoded ((prodPool S).get ch)) (rest ((prodPool S).get ch)) (hAcc ch hch)
  rw [hemNextMinAgree_increments _ _ hSlack] at hPV
  rw [polyWitnessValid_def] at hPV
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hPV
  rcases hPV with ⟨⟨hPLen, hPAg⟩, hPDot⟩
  rw [hemCosetAgreeCount_eq_filter_lookup domPts _ P hDom] at hPAg
  refine hNo ⟨P, ?_, ?_⟩
  · unfold affineMcaAccepts
    rw [list_getD_eq_get (prodPool S) _ ch]
    dsimp only [domPts, d₀, A₀, fWord, gWord, restOracle, O_target] at hPLen hPAg ⊢
    have hEqFilt : inst.initDomainPts.filter (fun z =>
        decide (RoundPoly.evalCoeffs P z =
          CommRingOps.add
            (lookupDomOracle inst.initDomainPts
              (evalCascadeOracle inst.initDomainPts inst.batchOracles
                (baseWeights.set i₀ (CommRingOps.zero, CommRingOps.zero))) z)
            (CommRingOps.mul (CommRingOps.add ((prodPool S).get ch).1
              (CommRingOps.mul ((prodPool S).get ch).2 z))
              (lookupDomOracle inst.initDomainPts
                (inst.batchOracles.getD i₀ (fun _ => CommRingOps.zero)) z)))) =
        inst.initDomainPts.filter (fun z =>
          decide (RoundPoly.evalCoeffs P z =
            lookupDomOracle inst.initDomainPts
              (evalCascadeOracle inst.initDomainPts inst.batchOracles
                (baseWeights.set i₀ ((prodPool S).get ch))) z)) := by
      have hMemCongr : ∀ xs : List QuarticGoldilocks, (∀ z ∈ xs, z ∈ inst.initDomainPts) →
          xs.filter (fun z =>
            decide (RoundPoly.evalCoeffs P z =
              CommRingOps.add
                (lookupDomOracle inst.initDomainPts
                  (evalCascadeOracle inst.initDomainPts inst.batchOracles
                    (baseWeights.set i₀ (CommRingOps.zero, CommRingOps.zero))) z)
                (CommRingOps.mul (CommRingOps.add ((prodPool S).get ch).1
                  (CommRingOps.mul ((prodPool S).get ch).2 z))
                  (lookupDomOracle inst.initDomainPts
                    (inst.batchOracles.getD i₀ (fun _ => CommRingOps.zero)) z)))) =
          xs.filter (fun z =>
            decide (RoundPoly.evalCoeffs P z =
              lookupDomOracle inst.initDomainPts
                (evalCascadeOracle inst.initDomainPts inst.batchOracles
                  (baseWeights.set i₀ ((prodPool S).get ch))) z)) := by
        intro xs hSub; induction xs with
        | nil => rfl
        | cons z zs ih =>
          have hValEq := lookupDomOracle_evalCascadeOracle_set inst.initDomainPts hDom
            inst.batchOracles baseWeights i₀ ((prodPool S).get ch)
            hi₀Lt hOW z (hSub z (.head zs))
          simp only [List.filter_cons, hValEq, ih (fun y hy => hSub y (.tail z hy))]
      exact hMemCongr inst.initDomainPts (fun _ h => h)
    rw [hEqFilt, decide_eq_true ch.2, decide_eq_true hPLen, decide_eq_true hPAg]
    rfl
  · rw [hPDot, evalCascadeClaim_set_split inst.batchClaims shifts baseWeights
      i₀ ((prodPool S).get ch) hi₀Claims hShifts.symm (hShifts.trans hWeights.symm)]

/-- **Multi-Stage Authenticated Opening Substitution + Cascade Fiber Bridge
    (`hem_multistage_extracted_acceptance_and_fiber_bound`)**:
    Composes `HemExtractedOpeningBridge.measured_hem_acceptance_from_extracted` (bounding
    authenticated `verifyHemOpeningBatch` acceptance by extracted-opening `verifyHemAffineWhir`
    acceptance plus `batchMerkleCost Q slots`) with `arbitrary_batch_cascade_fiber_bound` over
    arbitrary `1 ≤ m ≤ 16` batch arities and arbitrary `inst.stages`. -/
theorem hem_multistage_extracted_acceptance_and_fiber_bound
    {cardX w cardAnc Q : Nat}
    (A : QuantumAdv cardX w cardAnc Q) (L_merkle : MerkleAddressLayout cardX w)
    (slots : List (MerkleOpeningSlot cardX w))
    (hLevels : ∀ s ∈ slots, s.level + s.depth ≤ L_merkle.levels)
    (inst : HemWhirInstance QuarticGoldilocks)
    (decode : Fin cardX → List (Option (MerkleOpeningValue w)) →
      List (HemTranscriptRound QuarticGoldilocks))
    (S : List QuarticGoldilocks) (badMca : Nat)
    (shifts : List QuarticGoldilocks)
    (baseWeights : List (QuarticGoldilocks × QuarticGoldilocks))
    (hShape : 1 ≤ inst.batchOracles.length ∧ inst.batchOracles.length ≤ 16)
    (hArity : inst.batchClaims.length = inst.batchOracles.length)
    (hShifts : shifts.length = inst.batchClaims.length)
    (hWeights : baseWeights.length = inst.batchClaims.length)
    (hDom : inst.initDomainPts.Nodup) (hS : S.Nodup)
    (hEnough : inst.initDegBound + 3 ≤ inst.initMinAgree)
    (hDecomp : AffineFoldDecompBound inst.initDomainPts S
      (inst.initDegBound + 1) inst.initMinAgree badMca)
    (hInvalid : ¬ HemStatementValid { inst with initMinAgree := inst.initMinAgree - 1 }) :
    (2 ^ w * measuredEventMass A (fun H _ x => verifyHemOpeningBatch L_merkle slots inst decode H x) ≤
      2 ^ w * measuredEventMass A (fun H xs x =>
        verifyHemAffineWhir inst (decode x (extractedOpeningValues L_merkle slots H xs x))) +
      batchMerkleCost Q slots * quantumExperimentTotal A) ∧
    ∃ i₀ : Nat, i₀ < inst.batchOracles.length ∧
      ∀ (decoded : QuarticGoldilocks × QuarticGoldilocks → List (List QuarticGoldilocks))
        (rest : QuarticGoldilocks × QuarticGoldilocks → List (HemTranscriptRound QuarticGoldilocks))
        (L_ch : List (Fin (prodPool S).length)),
        L_ch.Nodup →
        (∀ ch ∈ L_ch, verifyHemAffineWhir inst
          (.cascade shifts (baseWeights.set i₀ ((prodPool S).get ch))
            (decoded ((prodPool S).get ch)) :: rest ((prodPool S).get ch)) = true) →
        L_ch.length ≤ badMca +
          (gsDecodeList (inst.initDegBound + 1) (inst.initMinAgree - 1) inst.initDomainPts
            (lookupDomOracle inst.initDomainPts
              (evalCascadeOracle inst.initDomainPts inst.batchOracles
                (baseWeights.set i₀ (CommRingOps.zero, CommRingOps.zero))))).length *
          (gsDecodeList inst.initDegBound (inst.initMinAgree - 1) inst.initDomainPts
            (lookupDomOracle inst.initDomainPts
              (inst.batchOracles.getD i₀ (fun _ => CommRingOps.zero)))).length *
          S.length :=
  ⟨measured_hem_acceptance_from_extracted A L_merkle slots hLevels inst decode,
   arbitrary_batch_cascade_fiber_bound inst S badMca shifts baseWeights
     hShape hArity hShifts hWeights hDom hS hEnough hDecomp hInvalid⟩

/-! ## §3. State-Restoration & `[CDHZ25]` PoW-Adjusted Salted-Merkle QROM Budgets -/

/-- Linear state-restoration Fiat–Shamir scaling `(Q + 1) · numRounds · b` (`[BCS16; CMS19; CY24]`). -/
def cdhzStateRestorationScale (Q numRounds : Nat) (b : RatBound) : RatBound :=
  ⟨(Q + 1) * numRounds * b.num, b.den, b.h_pos⟩

/-- Quadratic QROM post-quantum state-restoration scaling (`[CDHZ25, Thm 6.9]`, `8 e < 23`)
    combined with joint `powBits`-bit Fiat–Shamir grinding (`WHIR_FOLD_POW_BITS = 16`). -/
def cdhzPqsrPowScale (Q numRounds powBits : Nat) (b : RatBound) : RatBound :=
  ⟨23 * (Q + 1 + numRounds) ^ 2 * b.num, b.den * 2 ^ powBits,
   Nat.mul_pos b.h_pos (Nat.pow_pos (by decide))⟩

/-- Compressed-oracle 256-bit salted-Merkle extraction / collision tail `16 (Q + 1)^2 / 2^256`. -/
def cdhzSaltedMerkleCollisionBound (Q : Nat) : RatBound :=
  ⟨16 * (Q + 1) ^ 2, 2 ^ 256, Nat.pow_pos (by decide)⟩

/-- Under `[CDHZ25, Thm 6.9]` quadratic PQSR + `WHIR_FOLD_POW_BITS = 16` joint PoW, any `184`-bit
    sliced stage clears `128` bits up to `Q + 1 + numRounds ≤ 2^33`, and any `197`-bit stage clears
    `128` bits up to `Q + 1 + numRounds ≤ 2^40`. -/
theorem cdhzPqsrPow16_clears_128bits (b : RatBound) (Q numRounds : Nat) :
    (atLeastBits 184 b → Q + 1 + numRounds ≤ 2 ^ 33 →
      atLeastBits 128 (cdhzPqsrPowScale Q numRounds 16 b)) ∧
    (atLeastBits 197 b → Q + 1 + numRounds ≤ 2 ^ 40 →
      atLeastBits 128 (cdhzPqsrPowScale Q numRounds 16 b)) := by
  refine ⟨fun hb184 hQ33 => ?_, fun hb197 hQ40 => ?_⟩
  · change 23 * (Q + 1 + numRounds) ^ 2 * b.num * 2 ^ 128 ≤ b.den * 2 ^ 16
    have hCoeff : 23 * (Q + 1 + numRounds) ^ 2 ≤ 2 ^ 72 :=
      Nat.le_trans (Nat.mul_le_mul_left 23 (Nat.pow_le_pow_left hQ33 2)) (by decide)
    have h1 := Nat.mul_le_mul_right (b.num * 2 ^ 128) hCoeff
    rw [Nat.mul_assoc]
    refine Nat.le_trans h1 ?_
    have hPow : 2 ^ 72 * (b.num * 2 ^ 128) = (b.num * 2 ^ 184) * 2 ^ 16 := by
      calc 2 ^ 72 * (b.num * 2 ^ 128) = b.num * (2 ^ 72 * 2 ^ 128) := Nat.mul_left_comm _ _ _
           _ = b.num * (2 ^ 184 * 2 ^ 16) := by
               rw [show 2 ^ 72 * 2 ^ 128 = 2 ^ 184 * 2 ^ 16 from by decide]
           _ = (b.num * 2 ^ 184) * 2 ^ 16 := (Nat.mul_assoc _ _ _).symm
    rw [hPow]
    exact Nat.mul_le_mul_right (2 ^ 16) hb184
  · change 23 * (Q + 1 + numRounds) ^ 2 * b.num * 2 ^ 128 ≤ b.den * 2 ^ 16
    have hCoeff : 23 * (Q + 1 + numRounds) ^ 2 ≤ 2 ^ 85 :=
      Nat.le_trans (Nat.mul_le_mul_left 23 (Nat.pow_le_pow_left hQ40 2)) (by decide)
    have h1 := Nat.mul_le_mul_right (b.num * 2 ^ 128) hCoeff
    rw [Nat.mul_assoc]
    refine Nat.le_trans h1 ?_
    have hPow : 2 ^ 85 * (b.num * 2 ^ 128) = (b.num * 2 ^ 197) * 2 ^ 16 := by
      calc 2 ^ 85 * (b.num * 2 ^ 128) = b.num * (2 ^ 85 * 2 ^ 128) := Nat.mul_left_comm _ _ _
           _ = b.num * (2 ^ 197 * 2 ^ 16) := by
               rw [show 2 ^ 85 * 2 ^ 128 = 2 ^ 197 * 2 ^ 16 from by decide]
           _ = (b.num * 2 ^ 197) * 2 ^ 16 := (Nat.mul_assoc _ _ _).symm
    rw [hPow]
    exact Nat.mul_le_mul_right (2 ^ 16) hb197

/-- Pure arithmetic: any `184`-bit per-round soundness bound clears `128` bits under
    state-restoration Fiat–Shamir scaling up to `Q ≤ 2^50` and `numRounds ≤ 63`
    (`(2^50 + 1) · 63 ≤ 2^56` and `2^56 · 2^128 = 2^184`). -/
theorem cdhz184_budget_at_2pow50 (b : RatBound) (hb : atLeastBits 184 b)
    (Q numRounds : Nat) (hQ : Q ≤ 2 ^ 50) (hRounds : numRounds ≤ 63) :
    atLeastBits 128 (cdhzStateRestorationScale Q numRounds b) := by
  have hScale : (Q + 1) * numRounds ≤ 2 ^ 56 := by
    have h1 : (Q + 1) * numRounds ≤ (2 ^ 50 + 1) * 63 :=
      Nat.mul_le_mul (Nat.succ_le_succ hQ) hRounds
    exact Nat.le_trans h1 (by decide)
  change (Q + 1) * numRounds * b.num * 2 ^ 128 ≤ b.den
  have hMul := Nat.mul_le_mul_right (b.num * 2 ^ 128) hScale
  rw [Nat.mul_assoc]
  refine Nat.le_trans hMul ?_
  have hPow : 2 ^ 56 * (b.num * 2 ^ 128) = b.num * 2 ^ 184 := by
    calc 2 ^ 56 * (b.num * 2 ^ 128) = b.num * (2 ^ 56 * 2 ^ 128) := Nat.mul_left_comm _ _ _
         _ = b.num * 2 ^ 184 := by rw [show 2 ^ 56 * 2 ^ 128 = 2 ^ 184 from by decide]
  rw [hPow]
  exact hb

/-- Compressed-oracle 256-bit salted-Merkle collision tail clears `128` bits for all `Q ≤ 2^50`
    (in fact with `> 20` bits to spare since `16 (2^50 + 1)^2 < 2^105 ≤ 2^128`). -/
theorem cdhzSaltedMerkle_clears_128bits_at_2pow50 (Q : Nat) (hQ : Q ≤ 2 ^ 50) :
    atLeastBits 128 (cdhzSaltedMerkleCollisionBound Q) := by
  change 16 * (Q + 1) ^ 2 * 2 ^ 128 ≤ 2 ^ 256
  have hBase : Q + 1 ≤ 2 ^ 51 := by omega
  have hSq : (Q + 1) ^ 2 ≤ (2 ^ 51) ^ 2 := Nat.pow_le_pow_left hBase 2
  have hMul : 16 * (Q + 1) ^ 2 * 2 ^ 128 ≤ 16 * (2 ^ 51) ^ 2 * 2 ^ 128 :=
    Nat.mul_le_mul_right (2 ^ 128) (Nat.mul_le_mul_left 16 hSq)
  exact Nat.le_trans hMul (by decide)

/-- **All Non-Exhaustive Canonical Sliced Stages (`nv ∈ [2, 24]`) Clear `128`-Bit Security at `Q ≤ 2^50`
    Under State-Restoration + Salted-Merkle QROM Scaling (`cdhz_sliced_stage_clears_128bits_at_2pow50`)**:
    Without waiting on `[CWYZ26]` Claim 4.8's multi-sheet space-curve constant, every already-proved
    `sliced_stage_supported_budget` row (`≥ 184` bits) clears `atLeastBits 128` at `Q ≤ 2^50` and
    `numRounds ≤ 63`, together with the `256`-bit salted-Merkle compressed-oracle tail. -/
theorem cdhz_sliced_stage_clears_128bits_at_2pow50
    (nv : Nat) (h2 : 2 ≤ nv) (h24 : nv ≤ 24)
    (g : HemStageGeom) (hg : g ∈ hemStageGeoms nv)
    (hne : hemJohnsonQromStageExhaustive g = false) :
    ∃ (r : Nat × Nat × Nat × Nat × Nat) (w : Nat × Nat × Nat × Nat),
      hemJohnsonQromTableRow nv g.stageIdx = some r ∧
      slicedStageRow nv g.stageIdx = some w ∧
      (∀ D S : List QuarticGoldilocks, D.Nodup → S.Nodup → D.length = g.n →
        AffineFoldDecompBound D S g.d r.2.2.1 (slicedStageCount S.length g r w)) ∧
      (∀ Q numRounds : Nat, Q ≤ 2 ^ 50 → numRounds ≤ 63 →
        atLeastBits 128 (cdhzStateRestorationScale Q numRounds (slicedBinaryStageBound g r w)) ∧
        atLeastBits 128 (cdhzSaltedMerkleCollisionBound Q)) := by
  obtain ⟨r, w, hr, hw, hd, hb184, _⟩ := sliced_stage_supported_budget nv h2 h24 g hg hne
  exact ⟨r, w, hr, hw, hd, fun Q numRounds hQ hR =>
    ⟨cdhz184_budget_at_2pow50 _ hb184 Q numRounds hQ hR,
     cdhzSaltedMerkle_clears_128bits_at_2pow50 Q hQ⟩⟩

/-- The 128-bit sliced-stage result for every child of a recursive WHIR parent.
    `nv` is unrestricted (in particular nv ≤ 30); the flat child cap is configurable.
    The query and round budgets apply to this stage. A whole recursive proof must charge
    all children in its total round budget or separately union-bound their failures. -/
theorem cdhz_recursive_sliced_stage_clears_128bits_at_2pow50
    (nv childCap : Nat) (h2 : 2 ≤ nv) (hc2 : 2 ≤ childCap) (hc24 : childCap ≤ 24)
    (g : HemStageGeom) (hg : g ∈ hemRecursiveStageGeoms nv childCap)
    (hne : hemJohnsonQromStageExhaustive g = false) :
    ∃ (r : Nat × Nat × Nat × Nat × Nat) (w : Nat × Nat × Nat × Nat),
      hemJohnsonQromTableRow (hemRecursiveChildVars nv childCap) g.stageIdx = some r ∧
      slicedStageRow (hemRecursiveChildVars nv childCap) g.stageIdx = some w ∧
      (∀ D S : List QuarticGoldilocks, D.Nodup → S.Nodup → D.length = g.n →
        AffineFoldDecompBound D S g.d r.2.2.1 (slicedStageCount S.length g r w)) ∧
      (∀ Q numRounds : Nat, Q ≤ 2 ^ 50 → numRounds ≤ 63 →
        atLeastBits 128 (cdhzStateRestorationScale Q numRounds (slicedBinaryStageBound g r w)) ∧
        atLeastBits 128 (cdhzSaltedMerkleCollisionBound Q)) := by
  obtain ⟨hlo, hhi⟩ := hemRecursiveChildVars_bounds nv childCap h2 hc2 hc24
  exact cdhz_sliced_stage_clears_128bits_at_2pow50 _ hlo hhi g hg hne

/-- Charging every child explicitly costs up to six additional bits when nv ≤ 30
    and childCap = 24. A 184-bit binary-stage bound then tolerates Q ≤ 2^44 with
    at most 63 rounds per child. This is the arithmetic union-budget component only. -/
theorem cdhz184_recursive_budget_at_2pow44
    (nv : Nat) (h30 : nv ≤ 30) (b : RatBound) (hb : atLeastBits 184 b)
    (Q roundsPerChild : Nat) (hQ : Q ≤ 2 ^ 44) (hRounds : roundsPerChild ≤ 63) :
    atLeastBits 128 (cdhzStateRestorationScale Q
      (hemRecursiveChildCount nv 24 * roundsPerChild) b) := by
  have hCount := (hem_recursive_nv30_capacity nv h30).1
  have hScale : (Q + 1) * (hemRecursiveChildCount nv 24 * roundsPerChild) ≤ 2 ^ 56 :=
    Nat.le_trans (Nat.mul_le_mul (Nat.succ_le_succ hQ) (Nat.mul_le_mul hCount hRounds)) (by decide)
  change (Q + 1) * (hemRecursiveChildCount nv 24 * roundsPerChild) * b.num * 2 ^ 128 ≤ b.den
  have hMul := Nat.mul_le_mul_right (b.num * 2 ^ 128) hScale
  rw [Nat.mul_assoc]
  refine Nat.le_trans hMul ?_
  have hPow : 2 ^ 56 * (b.num * 2 ^ 128) = b.num * 2 ^ 184 := by
    calc 2 ^ 56 * (b.num * 2 ^ 128) = b.num * (2 ^ 56 * 2 ^ 128) := Nat.mul_left_comm _ _ _
         _ = b.num * 2 ^ 184 := by rw [show 2 ^ 56 * 2 ^ 128 = 2 ^ 184 from by decide]
  rw [hPow]
  exact hb

/-- All children are charged in the nv ≤ 30 bound; the flat sliced theorem is reused
    only at the actual child dimension. Commitment/binding and recursive composition
    remain the responsibility of the consuming verifier. -/
theorem cdhz_recursive_sliced_stage_clears_128bits_at_2pow44
    (nv : Nat) (h2 : 2 ≤ nv) (h30 : nv ≤ 30)
    (g : HemStageGeom) (hg : g ∈ hemRecursiveStageGeoms nv 24)
    (hne : hemJohnsonQromStageExhaustive g = false) :
    ∃ (r : Nat × Nat × Nat × Nat × Nat) (w : Nat × Nat × Nat × Nat),
      hemJohnsonQromTableRow (hemRecursiveChildVars nv 24) g.stageIdx = some r ∧
      slicedStageRow (hemRecursiveChildVars nv 24) g.stageIdx = some w ∧
      (∀ D S : List QuarticGoldilocks, D.Nodup → S.Nodup → D.length = g.n →
        AffineFoldDecompBound D S g.d r.2.2.1 (slicedStageCount S.length g r w)) ∧
      (∀ Q roundsPerChild : Nat, Q ≤ 2 ^ 44 → roundsPerChild ≤ 63 →
        atLeastBits 128 (cdhzStateRestorationScale Q
          (hemRecursiveChildCount nv 24 * roundsPerChild) (slicedBinaryStageBound g r w))) := by
  obtain ⟨hlo, hhi⟩ := hemRecursiveChildVars_bounds nv 24 h2 (by decide) (by decide)
  obtain ⟨r, w, hr, hw, hd, hb, _⟩ := sliced_stage_supported_budget _ hlo hhi g hg hne
  exact ⟨r, w, hr, hw, hd, fun Q rounds hQ hR =>
    cdhz184_recursive_budget_at_2pow44 nv h30 _ hb Q rounds hQ hR⟩

/-- `#tooth`: the per-child Q ≤ 2^50 guarantee cannot silently be reused for 64
    children at 63 rounds each and the universal 184-bit input floor. -/
theorem tooth_recursive_fanout_requires_budget :
    ¬ atLeastBits 128 (cdhzStateRestorationScale (2 ^ 50)
      (hemRecursiveChildCount 30 24 * 63) ⟨1, 2 ^ 184, by decide⟩) := by
  decide +kernel

#tooth_pair cdhz184_recursive_budget_at_2pow44 vs tooth_recursive_fanout_requires_budget
#verify_constructive cdhz_recursive_sliced_stage_clears_128bits_at_2pow44

#verify_constructive
  Qsag.equal_degree_bad_theta_bound
  Qsag.equal_degree_three_challenge_bound
  Qsag.sliced_equal_degree_theta_slice_challenge_bound
  Qsag.arbitrary_batch_cascade_fiber_bound
  Qsag.arbitrary_batch_incremented_cascade_fiber_bound
  Qsag.hem_multistage_extracted_acceptance_and_fiber_bound
  Qsag.cdhzPqsrPow16_clears_128bits
  Qsag.cdhz184_budget_at_2pow50
  Qsag.cdhzSaltedMerkle_clears_128bits_at_2pow50
  Qsag.cdhz_sliced_stage_clears_128bits_at_2pow50
  Qsag.cdhz_recursive_sliced_stage_clears_128bits_at_2pow50

/-! ### Exports for lane agg-whir-cert -/

theorem slicedBinaryStageBound_num (g : HemStageGeom) (r : Nat × Nat × Nat × Nat × Nat)
    (w : Nat × Nat × Nat × Nat) :
    (slicedBinaryStageBound g r w).num = slicedStageCount goldilocksExt4Card g r w := by rfl

theorem slicedBinaryStageBound_den (g : HemStageGeom) (r : Nat × Nat × Nat × Nat × Nat)
    (w : Nat × Nat × Nat × Nat) :
    (slicedBinaryStageBound g r w).den = goldilocksExt4Card * goldilocksExt4Card := by rfl
-- (end exports for lane agg-whir-cert)

/-! ## Executed fixtures and teeth (audited and paired in `Tests/HemExtractedOpeningBridgeTests`)

These unfold this module's definitions (`hemZeroOracleClaimInstance`, `claimedOpeningValues`,
`extractedOpeningValues`, `verifyHemOpeningBatch`, the stage profiles). Values of definitions sealed in
lower modules are cited from the certificates proved there: the toy Merkle game in `Oracle/Qrom`, the Hem
checker in `MultiRoundFsQrom`. -/

def toyHemDecode (_ : Fin 4) (values : List (Option (MerkleOpeningValue 1))) :
    List (HemTranscriptRound QuarticGoldilocks) :=
  if values = [some (0#1, [1#1])] then
    [.cascade [CommRingOps.zero] [(CommRingOps.zero, CommRingOps.one)] [[]], .finalQuery []]
  else []

def toyHemInstance : HemWhirInstance QuarticGoldilocks :=
  hemZeroOracleClaimInstance [CommRingOps.zero, CommRingOps.one] 0 2 []

private theorem toyHemInstance_accepts_claimed :
    verifyHemAffineWhir toyHemInstance
      [.cascade [CommRingOps.zero] [(CommRingOps.zero, CommRingOps.one)] [[]], .finalQuery []] = true :=
  verifyHemAffineWhir_zeroOracleClaim_dom01_kat.1

private theorem toyClaimedOpeningValues (x : Fin 4) :
    claimedOpeningValues toyOpeningSlots x = [some (0#1, [1#1])] := by
  rw [toyOpeningSlots_eq]
  show [some ((toyOpening x).leaf, (toyOpening x).path)] = _
  rw [toyOpening_eq]

private theorem toyHemDecode_claimed (x : Fin 4) :
    toyHemDecode x [some (0#1, [1#1])] =
      [.cascade [CommRingOps.zero] [(CommRingOps.zero, CommRingOps.one)] [[]], .finalQuery []] := by
  simp only [toyHemDecode, ↓reduceIte]

private theorem toyHemDecode_other (x : Fin 4) (values : List (Option (MerkleOpeningValue 1)))
    (h : ¬ values = [some (0#1, [1#1])]) : toyHemDecode x values = [] := by
  simp only [toyHemDecode, h, ↓reduceIte]

private theorem toy_event_accept (H : Fin 4 → BitVec 1) (x : Fin 4) :
    verifyHemOpeningBatch toyMerkleLayout toyOpeningSlots toyHemInstance toyHemDecode H x =
      toyAccepted H x := by
  have hV : verifyOpeningBatch toyMerkleLayout toyOpeningSlots H x = toyAccepted H x := by
    rw [toyOpeningSlots_eq, toyAccepted_eq]
    simp only [verifyOpeningBatch, List.all_cons, List.all_nil, Bool.and_true, toyOpening_shape,
      Bool.true_and]
  unfold verifyHemOpeningBatch
  rw [hV, toyClaimedOpeningValues, toyHemDecode_claimed, toyHemInstance_accepts_claimed, Bool.and_true]

private theorem toy_event_fail (H : Fin 4 → BitVec 1) (xs : List (Fin 4)) (x : Fin 4) :
    (verifyHemOpeningBatch toyMerkleLayout toyOpeningSlots toyHemInstance toyHemDecode H x &&
      !verifyHemAffineWhir toyHemInstance
        (toyHemDecode x (extractedOpeningValues toyMerkleLayout toyOpeningSlots H xs x))) =
      measuredMerkleFailure toyMerkleLayout 0 1 toyOpening H xs x := by
  have hE : extractedOpeningValues toyMerkleLayout toyOpeningSlots H xs x =
      [extractOnlineMerkleOpening (toyOpening x).rt (merkleRecords toyMerkleLayout H xs) 0
        (toyOpening x).path.length (toyOpening x).idx] := by
    rw [toyOpeningSlots_eq]; rfl
  have hLp : ((toyOpening x).leaf, (toyOpening x).path) = ((0#1 : BitVec 1), [(1#1 : BitVec 1)]) := by
    rw [toyOpening_eq]
  rw [toy_event_accept, measuredMerkleFailure_def, toyOpening_shape, Bool.true_and, ← toyAccepted_eq,
    hE]
  cases hd : decide (extractOnlineMerkleOpening (toyOpening x).rt (merkleRecords toyMerkleLayout H xs) 0
      (toyOpening x).path.length (toyOpening x).idx = some ((toyOpening x).leaf, (toyOpening x).path))
  · have he := of_decide_eq_false hd
    rw [toyHemDecode_other x _ (fun h => he ((List.cons.inj h).1.trans (congrArg some hLp.symm)))]
    rfl
  · have he := of_decide_eq_true hd
    rw [he, hLp, toyHemDecode_claimed, toyHemInstance_accepts_claimed]

/-- The decoder consumes extracted data: a missing opening rejects; the exact claimed
    opening accepts an invalid statement. The measured extraction loss is 0 for the query
    at the actual compression address, and 8/16 for the other address. -/
theorem toy_hem_substitution_execution :
    let honest := toyQueryAdv ⟨1, by decide⟩ (toyBasisInit_stateNormSq_pos _)
    let guesser := toyQueryAdv ⟨0, by decide⟩ (toyBasisInit_stateNormSq_pos _)
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
  intro honest guesser
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [toyHemDecode_other _ _ (by decide)]
    rfl
  · rw [toyClaimedOpeningValues, toyHemDecode_claimed]
    exact toyHemInstance_accepts_claimed
  · exact (congrArg (measuredEventMass honest)
      (funext fun H => funext fun _ => funext fun x => toy_event_accept H x)).trans
        toy_measured_merkle_event_masses.1
  · exact (congrArg (measuredEventMass honest)
      (funext fun H => funext fun xs => funext fun x => toy_event_fail H xs x)).trans
        toy_measured_merkle_event_masses.2.1
  · exact (congrArg (measuredEventMass guesser)
      (funext fun H => funext fun xs => funext fun x => toy_event_fail H xs x)).trans
        toy_measured_merkle_event_masses.2.2

/-- Actual authenticated Hem decoder consumer, on the earlier nonconstant one-bit layout. -/
theorem coherent_hem_decoder_execution :
    let honest := toyQueryAdv ⟨1, by decide⟩ (toyBasisInit_stateNormSq_pos _)
    coherentTableEventMass
      (verifyHemOpeningBatch toyMerkleLayout toyOpeningSlots toyHemInstance toyHemDecode)
      (fourierOracleState (fourierAdvStateAt honest 1 (Nat.le_refl 1))) = 524288 := by
  intro honest
  rw [coherent_hem_authenticated_event_eq]
  have hEv : (fun H : Fin 4 → BitVec 1 =>
      QVec.queryMassOn
        (verifyHemOpeningBatch toyMerkleLayout toyOpeningSlots toyHemInstance toyHemDecode H)
        (runQuantumAdv honest H)) =
      fun H => QVec.queryMassOn (toyAccepted H) (runQuantumAdv honest H) :=
    funext fun H => congrArg (fun e => QVec.queryMassOn e (runQuantumAdv honest H))
      (funext fun x => toy_event_accept H x)
  rw [hEv, toy_coherent_accept_mass]

#verify_constructive Qsag.coherent_hem_decoder_execution

theorem toyHemInstance_invalid : ¬ HemStatementValid toyHemInstance :=
  hemZeroOracleClaimInstance_invalid _ 0 2 [] (by decide) (by decide)

/-- The universal replacement theorem has a concrete decoder and inhabited adversary. -/
theorem toy_hem_substitution_bound_instance :
    let guesser := toyQueryAdv ⟨0, by decide⟩ (toyBasisInit_stateNormSq_pos _)
    2 ^ 1 * measuredEventMass guesser (fun H xs x =>
      verifyHemOpeningBatch toyMerkleLayout toyOpeningSlots toyHemInstance toyHemDecode H x &&
      !verifyHemAffineWhir toyHemInstance
        (toyHemDecode x (extractedOpeningValues toyMerkleLayout toyOpeningSlots H xs x))) ≤
      batchMerkleCost 1 toyOpeningSlots * quantumExperimentTotal guesser := by
  exact measured_hem_opening_substitution_bound _ _ _
    (by intro s hs; rw [toyOpeningSlots_eq] at hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        subst s; rw [toyMerkleLayout_levels]; decide) _ _

/-- The concrete bound has both accepting and rejecting challenges on an invalid instance:
    exactly two of the four pairs survive. This tests more than an empty attack schedule. -/
theorem hemZeroOracle_acceptance_nontrivial :
    let D : List QuarticGoldilocks := [CommRingOps.zero, CommRingOps.one]
    let inst := hemZeroOracleClaimInstance D 0 2 []
    ¬ HemStatementValid inst ∧
    ((prodPool D).filter (fun p => verifyHemAffineWhir inst
      [.cascade [CommRingOps.zero] [p] [[]], .finalQuery []])).length = 2 ∧
    2 < (prodPool D).length := by
  refine ⟨hemZeroOracleClaimInstance_invalid _ 0 2 [] (by decide) (by decide), ?_, ?_⟩
  · exact verifyHemAffineWhir_zeroOracleClaim_dom01_kat.2
  · rw [prodPool_length]
    decide

private theorem slicedBinaryStageProfile_nv24_stage0 :
    slicedBinaryStageProfile 24 ((hemStageGeoms 24).get ⟨0, by decide⟩) =
      slicedBinaryStageBound ((hemStageGeoms 24).get ⟨0, by decide⟩)
        (24, 0, 527170, 64, 27164) (24, 0, 524291, 185) := by
  unfold slicedBinaryStageProfile
  rw [hemJohnsonQrom_nv24_stage0_rows.2.1, hemJohnsonQrom_nv24_stage0_rows.2.2]

/-- The actual proved nv24 stage-0 expression cannot replace the much smaller paper input.
    Nor does widening commitment digests repair this DFM-scaled arithmetic term. These
    are counterexamples about bounds, not attacks achieving their upper bounds. -/
theorem tooth_sliced_nv24_profile_margin :
    let g := (hemStageGeoms 24).get ⟨0, by decide⟩
    let b := slicedBinaryStageProfile 24 g
    atLeastBits 185 b ∧ ¬ atLeastBits 186 b ∧ ¬ atLeastBits 244 b ∧
    ¬ atLeastBits 128 (dfmRoundScale (2 ^ 28) b) ∧
    ¬ atLeastBits 128 (dfmRoundScale (2 ^ 40) b) ∧
    ¬ atLeastBits 128 (dfmRoundScale (2 ^ 56) b) ∧
    ¬ RatBound.le b (whirAffineEqualDegreeCommitFoldBound
      ((whirAffineStageWitnesses 24 true).get ⟨0, whirAffineStageWitnesses_nv24_qrom_pos⟩)) := by
  -- The table rows are sealed in `Coding/Cwyz26`; their lookups are certified there.
  intro g b
  rw [show b = _ from slicedBinaryStageProfile_nv24_stage0, whirAffineStageWitnesses_nv24_qrom_head]
  simp only [atLeastBits, dfmRoundScale, RatBound.le, whirAffineEqualDegreeCommitFoldBound,
    slicedBinaryStageBound_num, slicedBinaryStageBound_den, goldilocksExt4Card_def]
  decide +kernel

/-- **DFM vs State-Restoration Scaling Contrast at `Q = 2^50` (`tooth_dfmRoundScale_fails_128bits_at_2pow50`)**:
    On `nv = 24` stage `0`, `cdhzStateRestorationScale (2^50) 32 b` and `cdhzSaltedMerkleCollisionBound (2^50)`
    both clear `128` bits, whereas naive `[DFM20]` `dfmRoundScale (2^50) b` fails `128` bits. -/
theorem tooth_dfmRoundScale_fails_128bits_at_2pow50 :
    ∃ g : HemStageGeom, g ∈ hemStageGeoms 24 ∧
      atLeastBits 128 (cdhzStateRestorationScale (2 ^ 50) 32 (slicedBinaryStageProfile 24 g)) ∧
      atLeastBits 128 (cdhzSaltedMerkleCollisionBound (2 ^ 50)) ∧
      ¬ atLeastBits 128 (dfmRoundScale (2 ^ 50) (slicedBinaryStageProfile 24 g)) :=
  ⟨(hemStageGeoms 24).get ⟨0, by decide⟩, list_get_mem (hemStageGeoms 24) ⟨0, by decide⟩,
   by
    rw [slicedBinaryStageProfile_nv24_stage0]
    simp only [atLeastBits, cdhzStateRestorationScale, slicedBinaryStageBound_num,
      slicedBinaryStageBound_den, goldilocksExt4Card_def]
    decide +kernel,
   by decide +kernel,
   by
    rw [slicedBinaryStageProfile_nv24_stage0]
    simp only [atLeastBits, dfmRoundScale]
    decide +kernel⟩

private def witEqDegDom : List QuarticGoldilocks := [qgNat 0, qgNat 1, qgNat 2, qgNat 3]

private theorem witEqDegDom_eq : witEqDegDom = toothDeg1Dom := toothDeg1Dom_eq.symm

private theorem witEqDegDom_nodup : witEqDegDom.Nodup := by
  rw [witEqDegDom_eq]; exact toothDeg1Dom_fixture_facts.1

private theorem witEqDegDom_zero_mem : (CommRingOps.zero : QuarticGoldilocks) ∈ witEqDegDom := by
  rw [witEqDegDom_eq]; exact toothDeg1Dom_fixture_facts.2.1

private theorem witEqDegDecomp3 :
    AffineFoldDecompBound witEqDegDom witEqDegDom 1 3 16 := by
  intro _ L hNd _
  have hLen : (prodPool witEqDegDom).length = 16 := by rw [prodPool_length]; decide
  rw [← hLen]
  exact Nat.le_trans (nodup_length_le_of_subset hNd (fun ch _ => List.mem_finRange ch))
    (Nat.le_of_eq List.length_finRange)

private theorem witEqDegDecomp4 :
    AffineFoldDecompBound witEqDegDom witEqDegDom 1 4 16 := by
  intro _ L hNd _
  have hLen : (prodPool witEqDegDom).length = 16 := by rw [prodPool_length]; decide
  rw [← hLen]
  exact Nat.le_trans (nodup_length_le_of_subset hNd (fun ch _ => List.mem_finRange ch))
    (Nat.le_of_eq List.length_finRange)

private theorem witEqDegMixList :
    ∀ θ : QuarticGoldilocks,
      (gsDecodeList 0 3 witEqDegDom
        (fun _ => CommRingOps.add (qgNat 0) (CommRingOps.mul θ (qgNat 0)))).length ≤ 1 := by
  intro θ
  have hZero : (fun _ : QuarticGoldilocks => CommRingOps.add (qgNat 0) (CommRingOps.mul θ (qgNat 0))) =
      (fun _ => CommRingOps.zero) := by
    funext _; rw [qgNat_zero, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  rw [hZero]
  exact gsDecodeList_zeroOracle_length_le_one witEqDegDom 0 3 witEqDegDom_nodup (by decide)

private theorem witEqDegInvalid :
    (∀ Fp : List QuarticGoldilocks, Fp.length ≤ 1 →
      2 ≤ (witEqDegDom.filter (fun z => decide (RoundPoly.evalCoeffs Fp z = qgNat 0))).length →
      ringDot Fp [qgNat 1] ≠ qgNat 1) ∨
    (∀ Gp : List QuarticGoldilocks, Gp.length ≤ 1 →
      2 ≤ (witEqDegDom.filter (fun z => decide (RoundPoly.evalCoeffs Gp z = qgNat 0))).length →
      ringDot Gp [qgNat 1] ≠ qgNat 0) := by
  refine .inl (fun Fp hLen hAg hDot => ?_)
  rcases Fp with _ | ⟨c, _ | _⟩
  · change CommRingOps.zero = qgNat 1 at hDot
    rw [qgNat_one] at hDot
    exact (by decide : (CommRingOps.zero : QuarticGoldilocks) ≠ CommRingOps.one) hDot
  · have hOne : qgNat 1 = CommRingOps.one := qgNat_one
    have hc1 : c = CommRingOps.one := by
      rw [hOne] at hDot
      simpa only [ringDot_cons_cons, ringDot_nil_left, ringDot_nil_right, LawfulCommRing.mul_one, LawfulCommRing.add_zero] using hDot
    subst hc1
    rw [witEqDegDom_eq] at hAg
    exact absurd hAg toothDeg1Dom_fixture_facts.2.2
  · simp only [List.length_cons] at hLen
    omega

theorem witness_equal_degree_three_challenge_bound :
    ∃ (D S kernel : List QuarticGoldilocks) (d A badTheta badAB maxMix : Nat)
      (f g : QuarticGoldilocks → QuarticGoldilocks) (e_f e_g c_f c_g : QuarticGoldilocks)
      (triples : List (Fin S.length × Fin (prodPool S).length)),
      D.Nodup ∧ S.Nodup ∧ (CommRingOps.zero : QuarticGoldilocks) ∈ S ∧
      d + 3 ≤ A ∧ A ≤ D.length ∧
      AffineFoldDecompBound D S (d + 1) A badTheta ∧
      AffineFoldDecompBound D S (d + 1) (A + 1) badAB ∧
      (∀ θ : QuarticGoldilocks,
        (gsDecodeList d A D (fun z => CommRingOps.add (f z) (CommRingOps.mul θ (g z)))).length ≤ maxMix) ∧
      ((∀ Fp : List QuarticGoldilocks, Fp.length ≤ d + 1 →
          A - 1 ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs Fp z = f z))).length →
          ringDot Fp kernel ≠ e_f) ∨
       (∀ Gp : List QuarticGoldilocks, Gp.length ≤ d + 1 →
          A - 1 ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs Gp z = g z))).length →
          ringDot Gp kernel ≠ e_g)) ∧
      triples.Nodup ∧
      (∀ tr ∈ triples, ¬¬ ∃ P : List QuarticGoldilocks,
        affineMcaAccepts D S (d + 1) (A + 1)
          (g, fun z => CommRingOps.add (f z) (CommRingOps.mul (S.get tr.1) (g z))) tr.2.1 P = true ∧
        ringDot P kernel = hemFoldClaimUpdate e_f e_g c_f c_g (S.get tr.1)
          ((prodPool S).get tr.2).1 ((prodPool S).get tr.2).2) :=
  ⟨witEqDegDom, witEqDegDom, [qgNat 1], 0, 3, 16, 16, 1,
   (fun _ => qgNat 0), (fun _ => qgNat 0), qgNat 1, qgNat 0, qgNat 0, qgNat 0, [],
   witEqDegDom_nodup, witEqDegDom_nodup, witEqDegDom_zero_mem, by decide, by decide,
   witEqDegDecomp3, witEqDegDecomp4, witEqDegMixList, witEqDegInvalid, .nil, fun _ h => nomatch h⟩

private def witCascInst : HemWhirInstance QuarticGoldilocks :=
  hemZeroOracleClaimInstance witEqDegDom 0 3 []

private theorem witCascInstInvalidPrev :
    ¬ HemStatementValid { witCascInst with initMinAgree := witCascInst.initMinAgree - 1 } :=
  hemZeroOracleClaimInstance_invalid witEqDegDom 0 2 [] witEqDegDom_nodup (by decide)

theorem witness_arbitrary_batch_cascade_fiber_bound :
    ∃ (inst : HemWhirInstance QuarticGoldilocks)
      (S : List QuarticGoldilocks) (badMca : Nat)
      (shifts : List QuarticGoldilocks)
      (baseWeights : List (QuarticGoldilocks × QuarticGoldilocks)),
      (1 ≤ inst.batchOracles.length ∧ inst.batchOracles.length ≤ 16) ∧
      inst.batchClaims.length = inst.batchOracles.length ∧
      shifts.length = inst.batchClaims.length ∧
      baseWeights.length = inst.batchClaims.length ∧
      inst.initDomainPts.Nodup ∧ S.Nodup ∧
      inst.initDegBound + 3 ≤ inst.initMinAgree ∧
      AffineFoldDecompBound inst.initDomainPts S (inst.initDegBound + 1) inst.initMinAgree badMca ∧
      ¬ HemStatementValid { inst with initMinAgree := inst.initMinAgree - 1 } :=
  ⟨witCascInst, witEqDegDom, 16, [qgNat 0], [(qgNat 0, qgNat 0)],
   by decide, rfl, rfl, rfl, witEqDegDom_nodup, witEqDegDom_nodup, by decide,
   witEqDegDecomp3, witCascInstInvalidPrev⟩

private def witStage24 : HemStageGeom := (hemStageGeoms 24).get ⟨0, by decide⟩

theorem witness_cdhz_sliced_stage_clears_128bits_at_2pow50 :
    ∃ (nv : Nat) (g : HemStageGeom),
      2 ≤ nv ∧ nv ≤ 24 ∧ g ∈ hemStageGeoms nv ∧ hemJohnsonQromStageExhaustive g = false :=
  ⟨24, witStage24, by decide, by decide, list_get_mem (hemStageGeoms 24) ⟨0, by decide⟩,
    hemJohnsonQrom_nv24_stage0_rows.1⟩

theorem inhabited_recursive_nv30_sliced_stage :
    ∃ (nv childCap : Nat) (g : HemStageGeom),
      nv = 30 ∧ childCap = 24 ∧ 2 ≤ nv ∧ 2 ≤ childCap ∧ childCap ≤ 24 ∧
      g ∈ hemRecursiveStageGeoms nv childCap ∧ hemJohnsonQromStageExhaustive g = false := by
  refine ⟨30, 24, witStage24, rfl, rfl, by decide, by decide, by decide, ?_, ?_⟩
  · exact list_get_mem (hemStageGeoms 24) ⟨0, by decide⟩
  · exact hemJohnsonQrom_nv24_stage0_rows.1

#verify_constructive
  Qsag.toy_hem_substitution_execution
  Qsag.tooth_sliced_nv24_profile_margin
  Qsag.tooth_dfmRoundScale_fails_128bits_at_2pow50
  Qsag.witness_equal_degree_three_challenge_bound
  Qsag.witness_arbitrary_batch_cascade_fiber_bound
  Qsag.witness_cdhz_sliced_stage_clears_128bits_at_2pow50
  Qsag.inhabited_recursive_nv30_sliced_stage
  Qsag.toy_hem_substitution_bound_instance
  Qsag.toyHemInstance_invalid
  Qsag.hemZeroOracle_acceptance_nontrivial
#verify_inhabited cdhz_recursive_sliced_stage_clears_128bits_at_2pow50 witness_cdhz_sliced_stage_clears_128bits_at_2pow50
#verify_inhabited Qsag.equal_degree_three_challenge_bound Qsag.witness_equal_degree_three_challenge_bound
#verify_inhabited Qsag.arbitrary_batch_cascade_fiber_bound Qsag.witness_arbitrary_batch_cascade_fiber_bound
#verify_inhabited Qsag.cdhz_sliced_stage_clears_128bits_at_2pow50 Qsag.witness_cdhz_sliced_stage_clears_128bits_at_2pow50

end Qsag
end
