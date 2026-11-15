module
/-
# Acceptance facts about the concrete Hem transcript checker

These results inspect `verifyHemAffineWhir`; they do not assume an acceptance cover.
The malformed-batch regression records why the oracle/claim arity check is necessary.
The zero-oracle family below gives a concrete false-statement case in which acceptance
forces a linear challenge collision. This is not a proof for arbitrary Hem statements,
nor a refinement of the Rust Fiat–Shamir transcript parser.
-/
public import Qsag.Protocol.Aggregation.HemWhirRbrSoundness
import all Qsag.Protocol.Aggregation.HemWhirRbrSoundness
import all Qsag.Oracle.MultiRoundFsQrom

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
  simp only [verifyHemAffineWhir, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.2.2, h.1.1.2, h.1.2, List.any_eq_true.mp h.2.1⟩

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
    fun hb => hInvalid ⟨hShape, hb⟩
  obtain ⟨i, _, hi, hBad⟩ := findInvalidBatchIdx_complete inst.initDomainPts
    inst.initMinAgree inst.initDegBound inst.initKernel hDom hEnough
    inst.batchOracles inst.batchClaims hArity.symm hBatch
  exact ⟨i, hi, hBad, hP⟩

/-- The former checker, retained only as the mutation under test: it forgets to compare
    the number of batch claims to the number of batch oracles. -/
def verifyHemMissingBatchArity {F : Type} [CommRingOps F] [DecidableEq F]
    (inst : HemWhirInstance F) (tr : List (HemTranscriptRound F)) : Bool :=
  match tr with
  | .cascade shifts weights decoded :: rest =>
    decide (1 ≤ inst.batchOracles.length ∧ inst.batchOracles.length ≤ 16) &&
    decide (shifts.length = inst.batchClaims.length) &&
    decide (weights.length = inst.batchClaims.length) &&
    decoded.any (fun P => polyWitnessValid inst.initDomainPts inst.initMinAgree
      (inst.initDegBound + 1) (evalCascadeOracle inst.initDomainPts inst.batchOracles weights)
      inst.initKernel (evalCascadeClaim inst.batchClaims shifts weights) P) &&
    verifyHemStages (evalCascadeOracle inst.initDomainPts inst.batchOracles weights)
      inst.initDomainPts (inst.initDegBound + 1) inst.initMinAgree inst.initKernel
      (evalCascadeClaim inst.batchClaims shifts weights) inst.stages rest
  | _ => false

def hemMissingClaimInstance : HemWhirInstance QuarticGoldilocks :=
  { batchOracles := [fun _ => CommRingOps.one]
    batchClaims := []
    initDomainPts := [CommRingOps.zero, CommRingOps.one]
    initDegBound := 0
    initMinAgree := 2
    initKernel := [CommRingOps.one]
    stages := [] }

/-- The old checker accepted an invalid statement by dropping its only oracle. The repaired
    checker rejects exactly the same transcript, even though its polynomial checks succeed. -/
theorem tooth_missing_batch_claim_erases_oracle :
    ¬ HemStatementValid hemMissingClaimInstance ∧
    verifyHemMissingBatchArity hemMissingClaimInstance
      [.cascade [] [] [[]], .finalQuery []] = true ∧
    verifyHemAffineWhir hemMissingClaimInstance
      [.cascade [] [] [[]], .finalQuery []] = false := by
  exact ⟨fun h => h.2, by decide, by decide⟩

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
  simp only [polyWitnessValid, Bool.and_eq_true, decide_eq_true_eq] at h
  have hCount : hemCosetAgreeCount dom (fun _ => (CommRingOps.zero : F)) P =
      (dom.filter (fun z => decide (RoundPoly.evalCoeffs P z = CommRingOps.zero))).length := by
    unfold hemCosetAgreeCount
    rw [← qsum_get_filter_eq]
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
    rw [← ringDot_trimPoly_eq, hTrim]
    rfl
  exact h.2.symm.trans hZero

theorem hemZeroOracleClaimInstance_invalid {F : Type} [LawfulField F] [DecidableEq F]
    (dom : List F) (degree agree : Nat) (stages : List (HemWhirStageSpec F))
    (hDom : dom.Nodup) (hEnough : degree + 1 ≤ agree) :
    ¬ HemStatementValid (hemZeroOracleClaimInstance dom degree agree stages) := by
  rintro ⟨_, ⟨P, hP⟩, _⟩
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
    simp only [evalCascadeOracle, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  change polyWitnessValid dom agree (degree + 1)
    (evalCascadeOracle dom [fun _ => CommRingOps.zero] [(α, β)]) [CommRingOps.one]
    (evalCascadeClaim [CommRingOps.one] [s] [(α, β)]) P = true at hP
  rw [hOracle] at hP
  have hc := polyWitnessValid_zeroOracle_claim dom (degree + 1) agree [CommRingOps.one]
    P _ hDom hEnough hP
  simpa only [evalCascadeClaim, LawfulCommRing.mul_one, LawfulCommRing.add_zero] using hc

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

/-- A full checker transcript need not satisfy the extra agreement check in the restricted
    cascade IOP. This prevents using its one-way acceptance bridge as a converse. -/
def hemCoreAgreementBoundaryInstance : HemWhirInstance QuarticGoldilocks :=
  { batchOracles := [fun i => if i = 1 then CommRingOps.one else CommRingOps.zero]
    batchClaims := [CommRingOps.one]
    initDomainPts := [CommRingOps.zero, CommRingOps.one,
      CommRingOps.add CommRingOps.one CommRingOps.one]
    initDegBound := 0
    initMinAgree := 2
    initKernel := [CommRingOps.zero, CommRingOps.one]
    stages := [] }

theorem tooth_core_agreement_is_stronger_than_checker :
    let S : List QuarticGoldilocks := [CommRingOps.zero, CommRingOps.one]
    let tr : List (HemIopMsg QuarticGoldilocks × Nat) :=
      [(.msgCascade [CommRingOps.zero], 2),
       (.msgFinal [CommRingOps.zero, CommRingOps.one], 0)]
    verifyHemAffineWhir hemCoreAgreementBoundaryInstance (assembleHemCoreTranscript S tr) = true ∧
    verifyHemCoreIop S hemCoreAgreementBoundaryInstance.initDomainPts 0 2
      hemCoreAgreementBoundaryInstance tr = false := by decide

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
  · decide
  · decide

/-- The degree/agreement inequality used by the zero-oracle case holds at each deployed
    nv=24 row. This checks numerical applicability, not a refinement of those rows to Rust. -/
theorem hemZeroOracle_nv24_degree_agreement :
    ∀ w ∈ whirAffineStageWitnesses 24 true, w.d + 2 ≤ w.A := by
  have h : (whirAffineStageWitnesses 24 true).all (fun w => decide (w.d + 2 ≤ w.A)) = true := by
    decide +kernel
  intro w hw
  exact of_decide_eq_true ((List.all_eq_true.mp h) w hw)

#verify_constructive
  Qsag.verifyHemAffineWhir_cascade_witness
  Qsag.verifyHemAffineWhir_invalid_coordinate
  Qsag.tooth_missing_batch_claim_erases_oracle
  Qsag.polyWitnessValid_zeroOracle_claim
  Qsag.hemZeroOracleClaimInstance_invalid
  Qsag.verifyHemZeroOracle_implies_linear_collision
  Qsag.verifyHemZeroOracle_accepted_pairs_le
  Qsag.tooth_core_agreement_is_stronger_than_checker
  Qsag.hemZeroOracle_acceptance_nontrivial
  Qsag.hemZeroOracle_nv24_degree_agreement

end Qsag
