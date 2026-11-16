module
import all Qsag.Math.GoldilocksBase
/-
Teeth and acceptance witnesses for the multi-stage Hem cascade IOP
(`Qsag.Protocol.Aggregation.HemMultistageCascadeRbr`), on the 64 → 32 → 16 point witness chain.

* `tooth_dropped_stage_fold_check_accepts_false_claim`: the verifier with the `commit` step's
  fold-consistency check removed (`hemFoldCommitStepUnchecked`, every other step unchanged)
  accepts the false statement `hemFoldFalseInst` for EVERY choice of the five challenges. The
  cheating prover sends zero wires and commits, at each stage, the constant table equal to the
  running claim.
* `real_verifier_rejects_dropped_check_attack`: the real verifier rejects the same attack.
* `honest_two_stage_transcript_accepted`: on a true statement the honest prover, folding its
  polynomial with `affineCombine` and sending the `affine.rs::prove_fold` wires, is accepted, so
  the verifier of the sound theorem is satisfiable through both fold stages.
-/
public import Qsag.Protocol.Aggregation.HemMultistageCascadeRbr
import all Qsag.Protocol.Aggregation.HemMultistageCascadeRbr
import all Qsag.Protocol.Aggregation.HemRbrSoundness
import all Qsag.Protocol.Aggregation.Cwyz26EqualDegreeAndMultiFold
import all Qsag.Protocol.Aggregation.MultiRoundFsQrom
import all Qsag.Protocol.Aggregation.ConcreteSecurityBudget
import all Qsag.Coding.Cwyz26
import all Qsag.Math.Goldilocks

public section
namespace Qsag
namespace HemMultistageCascadeTeeth

set_option autoImplicit false

/-! ## The mutant: `commit` without the fold-consistency check -/

/-- MUTANT `commit` step: accepts any stage table, without comparing it with the virtual fold
    of the previous oracle. -/
def hemFoldCommitStepUnchecked (s : HemFoldIopState) (m : HemFoldIopMsg) : HemFoldIopState :=
  match s, m with
  | .cur dom deg agree _ kernel claim, .commit table =>
    .cur dom deg agree (tableToOracle table) kernel claim
  | _, _ => .invalid

/-- MUTANT verifier: `hemMultistageVerify` with `hemFoldCommitStepUnchecked` in place of
    `hemFoldCommitStep`. -/
def hemMultistageVerifyNoFoldCheck (S domPts : List QuarticGoldilocks) (d₀ A₀ : Nat)
    (stages : List (HemWhirStageSpec QuarticGoldilocks))
    (inst : HemWhirInstance QuarticGoldilocks) (tr : List (HemFoldIopMsg × Nat)) : Bool :=
  hemFoldStateAccepted
    (hemMultistageRunWith hemFoldCommitStepUnchecked S domPts d₀ A₀ stages inst tr)

private theorem hemFoldCommitStepUnchecked_cur (dom : List QuarticGoldilocks) (deg agree : Nat)
    (oracle : Nat → QuarticGoldilocks) (kernel : List QuarticGoldilocks)
    (claim : QuarticGoldilocks) (table : List QuarticGoldilocks) :
    hemFoldCommitStepUnchecked (.cur dom deg agree oracle kernel claim) (.commit table) =
      .cur dom deg agree (tableToOracle table) kernel claim := by rfl

/-! ## The attack -/

/-- Claim after the cascade round on `hemFoldFalseInst` with absorbed shift `0`. -/
def attackClaim0 (c₀ : Nat) : QuarticGoldilocks :=
  evalCascadeClaim [CommRingOps.one] [CommRingOps.zero]
    [(prodPool hemFoldDom64).getD c₀ (CommRingOps.zero, CommRingOps.zero)]

/-- Claim after one fold with all five wires zero, challenge indices `cPhi` and `cTriple`. -/
def attackNextClaim (claim : QuarticGoldilocks) (cPhi cTriple : Nat) : QuarticGoldilocks :=
  hemFoldClaimUpdate
    (CommRingOps.add CommRingOps.zero
      (CommRingOps.mul (hemFoldDom64.getD cPhi CommRingOps.zero) CommRingOps.zero))
    (CommRingOps.add CommRingOps.zero
      (CommRingOps.mul (hemFoldDom64.getD cPhi CommRingOps.zero)
        (CommRingOps.sub claim CommRingOps.zero)))
    CommRingOps.zero CommRingOps.zero
    ((threePool hemFoldDom64 hemFoldDom64).getD cTriple
      (CommRingOps.zero, CommRingOps.zero, CommRingOps.zero)).1
    ((threePool hemFoldDom64 hemFoldDom64).getD cTriple
      (CommRingOps.zero, CommRingOps.zero, CommRingOps.zero)).2.1
    ((threePool hemFoldDom64 hemFoldDom64).getD cTriple
      (CommRingOps.zero, CommRingOps.zero, CommRingOps.zero)).2.2

/-- The cheating transcript for challenge indices `(c₀, c₁, c₂, c₃, c₄)`: zero wires, and at
    each `commit` the constant table equal to the running claim. Each message depends only on
    earlier challenges. -/
def attackTranscript (c₀ c₁ c₂ c₃ c₄ : Nat) : List (HemFoldIopMsg × Nat) :=
  [(.cascade [CommRingOps.zero], c₀),
   (.cross CommRingOps.zero CommRingOps.zero CommRingOps.zero, c₁),
   (.shift CommRingOps.zero CommRingOps.zero, c₂),
   (.commit (List.replicate hemFoldDom32.length (attackNextClaim (attackClaim0 c₀) c₁ c₂)), 0),
   (.cross CommRingOps.zero CommRingOps.zero CommRingOps.zero, c₃),
   (.shift CommRingOps.zero CommRingOps.zero, c₄),
   (.commit (List.replicate hemFoldDom16.length
      (attackNextClaim (attackNextClaim (attackClaim0 c₀) c₁ c₂) c₃ c₄)), 0),
   (.final [attackNextClaim (attackNextClaim (attackClaim0 c₀) c₁ c₂) c₃ c₄], 0)]

/-- A constant table and the constant polynomial pass the final check for any claim, as soon as
    the kernel is `[1, 0]`. -/
private theorem constTable_final_valid (dom : List QuarticGoldilocks) (deg agree : Nat)
    (k₀ c : QuarticGoldilocks) (hk : k₀ = CommRingOps.one) (hAg : agree ≤ dom.length) :
    polyWitnessValid dom agree deg (tableToOracle (List.replicate dom.length c))
      [k₀, CommRingOps.zero] c [c] = true := by
  subst hk
  have hLen : [c].length ≤ deg + 1 := Nat.succ_le_succ (Nat.zero_le deg)
  have hCount : hemCosetAgreeCount dom (tableToOracle (List.replicate dom.length c)) [c] =
      dom.length := by
    unfold hemCosetAgreeCount
    have hF : (fun idx : Fin dom.length =>
        if tableToOracle (List.replicate dom.length c) idx.1 =
          RoundPoly.evalCoeffs [c] (dom.get idx) then 1 else 0) = fun _ => 1 :=
      funext (fun idx => by
        have h1 : tableToOracle (List.replicate dom.length c) idx.1 = c := by
          unfold tableToOracle
          rw [List.getD_eq_getElem?_getD, List.getElem?_replicate_of_lt idx.2]
          rfl
        have h2 : RoundPoly.evalCoeffs [c] (dom.get idx) = c := by
          show CommRingOps.add c (CommRingOps.mul (dom.get idx) CommRingOps.zero) = c
          rw [LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
        rw [h1, h2]
        exact ite_true_eq _ _ rfl)
    rw [hF, qsum_const, Nat.mul_one]
  have hDot : ringDot [c] [CommRingOps.one, CommRingOps.zero] = c := by
    show CommRingOps.add (CommRingOps.mul c CommRingOps.one) CommRingOps.zero = c
    rw [LawfulCommRing.mul_one, LawfulCommRing.add_zero]
  unfold polyWitnessValid
  rw [decide_eq_true hLen, hCount, decide_eq_true hAg, decide_eq_true hDot]
  rfl

private theorem kernelFold_pair_parity (φ a b : QuarticGoldilocks) :
    (hemKernelFold φ [a, b]).length % 2 = 0 := by
  have h : (hemKernelFold φ [a, b]).length = 2 := by rfl
  rw [h]

/-- The mutant verifier accepts the attack on the false statement for every challenge. -/
theorem dropped_fold_check_accepts_every_challenge (c₀ c₁ c₂ c₃ c₄ : Nat) :
    hemMultistageVerifyNoFoldCheck hemFoldDom64 hemFoldDom64 0 43 hemFoldWitnessStages
      hemFoldFalseInst (attackTranscript c₀ c₁ c₂ c₃ c₄) = true := by
  have hRun : hemMultistageRunWith hemFoldCommitStepUnchecked hemFoldDom64 hemFoldDom64 0 43
      hemFoldWitnessStages hemFoldFalseInst (attackTranscript c₀ c₁ c₂ c₃ c₄) = .accepted := by
    show hemFoldFinalStep
      (hemFoldCommitStepUnchecked
        (hemFoldShiftStep hemFoldDom64 hemFoldWitnessStage1.domainPts hemFoldWitnessStage2
          (hemFoldCrossStep hemFoldDom64 hemFoldWitnessStage1.domainPts
            hemFoldWitnessStage1.degBound hemFoldWitnessStage1.minAgree hemFoldWitnessStage2
            (hemFoldCommitStepUnchecked
              (hemFoldShiftStep hemFoldDom64 hemFoldDom64 hemFoldWitnessStage1
                (hemFoldCrossStep hemFoldDom64 hemFoldDom64 (0 + 1) (43 + 1)
                  hemFoldWitnessStage1
                  (hemFoldCascadeStep hemFoldDom64 hemFoldDom64 0 43 hemFoldWitnessStages
                    hemFoldFalseInst .init (.cascade [CommRingOps.zero]) c₀)
                  (.cross CommRingOps.zero CommRingOps.zero CommRingOps.zero) c₁)
                (.shift CommRingOps.zero CommRingOps.zero) c₂)
              (.commit (List.replicate hemFoldDom32.length
                (attackNextClaim (attackClaim0 c₀) c₁ c₂))))
            (.cross CommRingOps.zero CommRingOps.zero CommRingOps.zero) c₃)
          (.shift CommRingOps.zero CommRingOps.zero) c₄)
        (.commit (List.replicate hemFoldDom16.length
          (attackNextClaim (attackNextClaim (attackClaim0 c₀) c₁ c₂) c₃ c₄))))
      (.final [attackNextClaim (attackNextClaim (attackClaim0 c₀) c₁ c₂) c₃ c₄]) = .accepted
    rw [hemFoldCascadeStep_init hemFoldDom64 hemFoldDom64 0 43 hemFoldWitnessStages
      hemFoldFalseInst CommRingOps.zero c₀ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩]
    rw [hemFoldCrossStep_cur hemFoldDom64 hemFoldDom64 (0 + 1) (43 + 1) hemFoldWitnessStage1 _
      hemFoldFalseInst.initKernel _ _ _ _ c₁ (by rfl)]
    rw [hemFoldShiftStep_mid, hemFoldCommitStepUnchecked_cur]
    rw [hemFoldCrossStep_cur hemFoldDom64 hemFoldWitnessStage1.domainPts
      hemFoldWitnessStage1.degBound hemFoldWitnessStage1.minAgree hemFoldWitnessStage2 _ _ _ _ _ _
      c₃ (show (hemKernelFold (hemFoldDom64.getD c₁ CommRingOps.zero)
          hemFoldFalseInst.initKernel).length % 2 = 0 from
        kernelFold_pair_parity (hemFoldDom64.getD c₁ CommRingOps.zero) CommRingOps.one
          CommRingOps.zero)]
    rw [hemFoldShiftStep_mid, hemFoldCommitStepUnchecked_cur]
    exact hemFoldFinalStep_cur _ _ _ _ _ _ _
      (constTable_final_valid hemFoldDom16 1 16
        (CommRingOps.add
          (CommRingOps.add CommRingOps.one
            (CommRingOps.mul (hemFoldDom64.getD c₁ CommRingOps.zero) CommRingOps.zero))
          (CommRingOps.mul (hemFoldDom64.getD c₃ CommRingOps.zero) CommRingOps.zero))
        (attackNextClaim (attackNextClaim (attackClaim0 c₀) c₁ c₂) c₃ c₄)
        (by rw [LawfulCommRing.mul_zero, LawfulCommRing.mul_zero, LawfulCommRing.add_zero,
          LawfulCommRing.add_zero])
        (by decide))
  show hemFoldStateAccepted (hemMultistageRunWith hemFoldCommitStepUnchecked hemFoldDom64
    hemFoldDom64 0 43 hemFoldWitnessStages hemFoldFalseInst
    (attackTranscript c₀ c₁ c₂ c₃ c₄)) = true
  rw [hRun]
  rfl

/-- `#tooth`: dropping the `commit` step's fold-consistency check breaks soundness. The
    statement `hemFoldFalseInst` is false, and the mutant verifier accepts the attack for every
    choice of the five challenges. -/
theorem tooth_dropped_stage_fold_check_accepts_false_claim :
    ¬ (HemStatementValid hemFoldFalseInst ∨
      ∃ c₀ c₁ c₂ c₃ c₄ : Nat,
        ¬ (hemMultistageVerifyNoFoldCheck hemFoldDom64 hemFoldDom64 0 43 hemFoldWitnessStages
          hemFoldFalseInst (attackTranscript c₀ c₁ c₂ c₃ c₄) = true)) := by
  rintro (hValid | ⟨c₀, c₁, c₂, c₃, c₄, hReject⟩)
  · exact hemFoldFalseInst_invalid hValid
  · exact hReject (dropped_fold_check_accepts_every_challenge c₀ c₁ c₂ c₃ c₄)

set_option maxRecDepth 100000 in
/-- The real verifier rejects the same attack (challenge indices `0`): the committed constant
    table `2` differs from the virtual fold of the zero oracle. -/
theorem real_verifier_rejects_dropped_check_attack :
    ¬ (hemMultistageVerify hemFoldDom64 hemFoldDom64 0 43 hemFoldWitnessStages
      hemFoldFalseInst (attackTranscript 0 0 0 0 0) = true) := by
  unfold hemMultistageVerify hemMultistageRun
  simp only [attackTranscript, hemFoldWitnessStages,
    hemMultistageRunWith.public_eqs, hemFoldRunStagesWith.public_eqs,
    hemFoldCascadeStep.public_eqs, hemFoldCrossStep.public_eqs, hemFoldShiftStep.public_eqs,
    hemFoldCommitStep.public_eqs, hemFoldGuard.public_eqs,
    hemTableMatchesOracle.public_eqs, hemVirtualFoldOracle_def,
    evalCascadeOracle_nil, evalCascadeOracle_cons,
    evalCascadeClaim_nil, evalCascadeClaim_cons, attackNextClaim, attackClaim0,
    LawfulCommRing.mul_zero, LawfulCommRing.add_zero, LawfulCommRing.sub_self,
    hemFoldDom64, hemFoldDom32, hemFoldDom16, hemFoldDomain, hemBitRevExponents,
    prodPool_eq, threePool, hemFoldClaimUpdate_def,
    List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append, 
    List.length_map, 
    
    tableToOracle,
    hemFoldFalseInst, hemFoldWitnessStage1, hemFoldWitnessStage2,
    List.length_cons, List.length_nil, Nat.reduceMod, Nat.reduceAdd, Nat.reduceSub,
    decide_true, and_self]
  decide +kernel

/-! ## An honest accepted run through both fold stages -/

/-- A true statement on the witness chain: the constant polynomial `1`, claim `⟨[1], [1, 0]⟩`. -/
def honestInst : HemWhirInstance QuarticGoldilocks :=
  { batchOracles := [fun idx =>
      RoundPoly.evalCoeffs [CommRingOps.one] (hemFoldDom64.getD idx CommRingOps.zero)]
    batchClaims := [ringDot [CommRingOps.one] [CommRingOps.one, CommRingOps.zero]]
    initDomainPts := hemFoldDom64
    initDegBound := 0
    initMinAgree := 43
    initKernel := [CommRingOps.one, CommRingOps.zero]
    stages := hemFoldWitnessStages }

/-- Honest cross wires `(⟨cE, kE⟩, ⟨cE, kO⟩, ⟨cO, kE⟩)` of `affine.rs::prove_fold_in_place`. -/
def honestCross (c k : List QuarticGoldilocks) : HemFoldIopMsg :=
  .cross (ringDot (splitEvenOdd c).1 (splitEvenOdd k).1)
    (ringDot (splitEvenOdd c).1 (splitEvenOdd k).2)
    (ringDot (splitEvenOdd c).2 (splitEvenOdd k).1)

/-- Honest shift wires `(⟨X cE, k'⟩, ⟨X cO, k'⟩)` against the folded kernel. -/
def honestShift (c k' : List QuarticGoldilocks) : HemFoldIopMsg :=
  .shift (ringDot (shiftPoly (splitEvenOdd c).1) k') (ringDot (shiftPoly (splitEvenOdd c).2) k')

/-- Honest folded coefficients `cO + (α + β X)(cE + θ cO)` (`fold_coeffs`). -/
def honestFold (S : List QuarticGoldilocks) (cTriple : Nat) (c : List QuarticGoldilocks) :
    List QuarticGoldilocks :=
  affineCombine
    ((threePool S S).getD cTriple (CommRingOps.zero, CommRingOps.zero, CommRingOps.zero)).1
    ((threePool S S).getD cTriple (CommRingOps.zero, CommRingOps.zero, CommRingOps.zero)).2.1
    ((threePool S S).getD cTriple (CommRingOps.zero, CommRingOps.zero, CommRingOps.zero)).2.2
    (splitEvenOdd c).1 (splitEvenOdd c).2

/-- The honest transcript for challenge indices `(5, 3, 77, 9, 1000)`. -/
def honestTranscript : List (HemFoldIopMsg × Nat) :=
  let S := hemFoldDom64
  let k₀ : List QuarticGoldilocks := [CommRingOps.one, CommRingOps.zero]
  let p₀ := evalCascadePolySum [[CommRingOps.one]]
    [(prodPool S).getD 5 (CommRingOps.zero, CommRingOps.zero)]
  let k₁ := hemKernelFold (S.getD 3 CommRingOps.zero) k₀
  let p₁ := honestFold S 77 p₀
  let k₂ := hemKernelFold (S.getD 9 CommRingOps.zero) k₁
  let p₂ := honestFold S 1000 p₁
  [(.cascade [ringDot (shiftPoly [CommRingOps.one]) k₀], 5),
   (honestCross p₀ k₀, 3),
   (honestShift p₀ k₁, 77),
   (.commit (hemFoldDom32.map (RoundPoly.evalCoeffs p₁)), 0),
   (honestCross p₁ k₁, 9),
   (honestShift p₁ k₂, 1000),
   (.commit (hemFoldDom16.map (RoundPoly.evalCoeffs p₂)), 0),
   (.final p₂, 0)]

set_option maxRecDepth 100000 in
/-- The honest statement is true. -/
theorem honestInst_valid : HemStatementValid honestInst :=
  ⟨by decide, ⟨[CommRingOps.one], by decide +kernel⟩, True.intro⟩

private theorem cascadePair (a b : QuarticGoldilocks) :
    evalCascadePolySum [[CommRingOps.one]] [(a,b)] = [a,b] := by
  simp only [evalCascadePolySum, polyScaleVar_def, shiftPoly_eq, List.map_cons, List.map_nil,
    polyAddVar, rawAddCoeffs, LawfulCommRing.mul_one, LawfulCommRing.mul_zero,
    LawfulCommRing.add_zero]

private theorem cascadePair' (p : QuarticGoldilocks × QuarticGoldilocks) :
    evalCascadePolySum [[CommRingOps.one]] [p] = [p.1, p.2] := by
  cases p with | mk a b => exact cascadePair a b

private theorem crossPair (a b : QuarticGoldilocks) :
    honestCross [a,b] [CommRingOps.one, CommRingOps.zero] = .cross a CommRingOps.zero b := by
  simp only [honestCross, splitEvenOdd, ringDot_cons_cons, ringDot_nil_right, LawfulCommRing.mul_one,
    LawfulCommRing.mul_zero, LawfulCommRing.add_zero]

private theorem shiftPair (a b : QuarticGoldilocks) :
    honestShift [a,b] [CommRingOps.one, CommRingOps.zero] = .shift CommRingOps.zero CommRingOps.zero := by
  simp only [honestShift, splitEvenOdd, shiftPoly_eq, ringDot_cons_cons, ringDot_nil_right,
    LawfulCommRing.zero_mul, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]

private theorem foldPair (S : List QuarticGoldilocks) (c : Nat) (a b : QuarticGoldilocks) :
    let t := (threePool S S).getD c (CommRingOps.zero, CommRingOps.zero, CommRingOps.zero)
    honestFold S c [a,b] = [linearNextA a b t.1 t.2.1, linearNextB a b t.1 t.2.2] := by
  simp only [honestFold, splitEvenOdd, affineCombine_def, polyScaleVar_def, shiftPoly_eq,
    List.map_cons, List.map_nil, polyAddVar, rawAddCoeffs, linearNextA, linearNextB,
    LawfulCommRing.mul_zero, LawfulCommRing.add_zero]

private theorem mapPair (D : List QuarticGoldilocks) (a b : QuarticGoldilocks) :
    D.map (RoundPoly.evalCoeffs [a,b]) = linearTable D a b := by
  apply List.map_congr_left
  intro x _
  simp only [RoundPoly.evalCoeffs_cons, RoundPoly.evalCoeffs_nil,
    LawfulCommRing.mul_zero, LawfulCommRing.add_zero,  ]
  rw [LawfulCommRing.mul_comm x b]

private theorem honestTranscript_linear :
    let p := (prodPool hemFoldDom64).getD 5 (CommRingOps.zero, CommRingOps.zero)
    let t₁ := (threePool hemFoldDom64 hemFoldDom64).getD 77
      (CommRingOps.zero, CommRingOps.zero, CommRingOps.zero)
    let t₂ := (threePool hemFoldDom64 hemFoldDom64).getD 1000
      (CommRingOps.zero, CommRingOps.zero, CommRingOps.zero)
    let a₁ := linearNextA p.1 p.2 t₁.1 t₁.2.1
    let b₁ := linearNextB p.1 p.2 t₁.1 t₁.2.2
    let a₂ := linearNextA a₁ b₁ t₂.1 t₂.2.1
    let b₂ := linearNextB a₁ b₁ t₂.1 t₂.2.2
    honestTranscript =
      [(.cascade [CommRingOps.zero], 5), (.cross p.1 CommRingOps.zero p.2, 3),
       (.shift CommRingOps.zero CommRingOps.zero, 77), (.commit (linearTable hemFoldDom32 a₁ b₁), 0),
       (.cross a₁ CommRingOps.zero b₁, 9), (.shift CommRingOps.zero CommRingOps.zero, 1000),
       (.commit (linearTable hemFoldDom16 a₂ b₂), 0), (.final [a₂,b₂], 0)] := by
  simp only [honestTranscript, cascadePair', foldPair, crossPair, shiftPair,
    hemKernelFold_pair, mapPair, shiftPoly_eq, ringDot_cons_cons, ringDot_nil_right, LawfulCommRing.zero_mul,
    LawfulCommRing.mul_zero, LawfulCommRing.add_zero]

/-- The actual honest transcript traverses both stages; the proof uses the algebraic
fold identity and the certified antipodal geometry, without evaluating field inverses. -/
theorem honest_two_stage_transcript_accepted :
    hemMultistageVerify hemFoldDom64 hemFoldDom64 0 43 hemFoldWitnessStages honestInst
      honestTranscript = true := by
  let p := (prodPool hemFoldDom64).getD 5 (CommRingOps.zero, CommRingOps.zero)
  let t₁ := (threePool hemFoldDom64 hemFoldDom64).getD 77
    (CommRingOps.zero, CommRingOps.zero, CommRingOps.zero)
  let t₂ := (threePool hemFoldDom64 hemFoldDom64).getD 1000
    (CommRingOps.zero, CommRingOps.zero, CommRingOps.zero)
  let a₁ := linearNextA p.1 p.2 t₁.1 t₁.2.1
  let b₁ := linearNextB p.1 p.2 t₁.1 t₁.2.2
  let a₂ := linearNextA a₁ b₁ t₂.1 t₂.2.1
  let b₂ := linearNextB a₁ b₁ t₂.1 t₂.2.2
  have hO : ∀ i, i < hemFoldDom64.length →
      evalCascadeOracle hemFoldDom64 honestInst.batchOracles [p] i =
        linearOracle hemFoldDom64 p.1 p.2 i := by
    intro i _
    simp only [honestInst, evalCascadeOracle_cons, evalCascadeOracle_nil,
      RoundPoly.evalCoeffs_cons, RoundPoly.evalCoeffs_nil, linearOracle,
      LawfulCommRing.mul_zero, LawfulCommRing.add_zero, LawfulCommRing.mul_one]
  have hO₁ : ∀ i, i < hemFoldDom32.length →
      tableToOracle (linearTable hemFoldDom32 a₁ b₁) i = linearOracle hemFoldDom32 a₁ b₁ i :=
    fun i hi => linearTable_toOracle _ _ _ _ hi
  unfold hemMultistageVerify hemMultistageRun
  rw [honestTranscript_linear]
  simp only [hemFoldWitnessStages, hemMultistageRunWith.public_eqs, hemFoldRunStagesWith.public_eqs]
  rw [hemFoldCascadeStep_init hemFoldDom64 hemFoldDom64 0 43
    [hemFoldWitnessStage1, hemFoldWitnessStage2] honestInst CommRingOps.zero 5
    ⟨rfl, rfl, rfl, rfl, rfl, by simp only [honestInst, hemFoldWitnessStages]⟩]
  have hc : evalCascadeClaim honestInst.batchClaims [CommRingOps.zero] [p] = p.1 := by
    simp only [honestInst, ringDot_cons_cons, ringDot_nil_left, evalCascadeClaim_cons, evalCascadeClaim_nil,
      LawfulCommRing.mul_one, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  rw [hc, show honestInst.initKernel = [CommRingOps.one, CommRingOps.zero] from rfl]
  have h₁ := linearStage_complete hemFoldDom64 _ _
    (hemFoldStageGeom_antipodal hemFoldWitnessGeom1) rfl 44 _ p.1 p.2 hO 3 77
  have h₂ := linearStage_complete hemFoldDom64 _ _
    (hemFoldStageGeom_antipodal hemFoldWitnessGeom2) rfl 28 _ a₁ b₁ hO₁ 9 1000
  simp only [hemFoldWitnessStage1] at h₁
  simp only [hemFoldWitnessStage2] at h₂
  simp only [hemFoldWitnessStage1, hemFoldWitnessStage2]
  rw [h₁, h₂]
  rw [hemFoldFinalStep_cur _ _ _ _ _ _ _
    (linearTable_final_valid hemFoldDom16 a₂ b₂ 16 (by decide +kernel))]
  rfl

/-! ## Explicit budgets of the witness IOP -/

set_option maxRecDepth 100000 in
/-- `(badCard, challengeCard)` of the eight rounds of the witness IOP (cascade; cross, shift,
    commit for each of the two stages; final). Every round flips on a strict minority of its
    challenges, and one pass over all rounds has error `2080/4096 + 2/64 + 55808/262144 < 1`. -/
theorem witness_round_budgets :
    (hemMultistageSpecs hemFoldDom64 hemFoldDom64_pos hemFoldDom64 0 43 2016 1
        hemFoldWitnessStages (hemWelchBerlekampBudget hemFoldDom64) hemFoldWitnessCert).map
        (fun sp => (sp.bad, sp.chalCard)) =
      [(2080, 4096), (1, 64), (39936, 262144), (0, 1), (1, 64), (15872, 262144), (0, 1),
        (0, 1)] := by
  rw [hemMultistageSpecs_budgets]
  simp only [hemFoldWitnessStages, hemFoldStageRoundBudgets, prodPool_length, threePool_length]
  decide +kernel

#tooth_pair Qsag.hemMultistage_state_restoration_soundness vs
  Qsag.HemMultistageCascadeTeeth.tooth_dropped_stage_fold_check_accepts_false_claim

#verify_constructive
  Qsag.HemMultistageCascadeTeeth.dropped_fold_check_accepts_every_challenge
  Qsag.HemMultistageCascadeTeeth.tooth_dropped_stage_fold_check_accepts_false_claim
  Qsag.HemMultistageCascadeTeeth.real_verifier_rejects_dropped_check_attack
  Qsag.HemMultistageCascadeTeeth.honestInst_valid
  Qsag.HemMultistageCascadeTeeth.honest_two_stage_transcript_accepted
  Qsag.HemMultistageCascadeTeeth.witness_round_budgets

end HemMultistageCascadeTeeth
end Qsag
