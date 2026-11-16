module
public import Qsag.Math.GoldilocksBase
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
public import Qsag.Protocol.Aggregation.HemRbrSoundness
public import Qsag.Protocol.Aggregation.Cwyz26EqualDegreeAndMultiFold
public import Qsag.Protocol.Aggregation.MultiRoundFsQrom
public import Qsag.Protocol.Aggregation.ConcreteSecurityBudget
public import Qsag.Coding.Cwyz26
public import Qsag.Math.Goldilocks

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
    rw [hemCosetAgreeCount_def]
    have hF : (fun idx : Fin dom.length =>
        if tableToOracle (List.replicate dom.length c) idx.1 =
          RoundPoly.evalCoeffs [c] (dom.get idx) then 1 else 0) = fun _ => 1 :=
      funext (fun idx => by
        have h1 : tableToOracle (List.replicate dom.length c) idx.1 = c := by
          rw [tableToOracle_apply, List.getD_eq_getElem?_getD, List.getElem?_replicate_of_lt idx.2]
          rfl
        have h2 : RoundPoly.evalCoeffs [c] (dom.get idx) = c := by
          show CommRingOps.add c (CommRingOps.mul (dom.get idx) CommRingOps.zero) = c
          rw [LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
        rw [h1, h2]
        exact ite_true_eq _ _ rfl)
    rw [hF, qsum_const, Nat.mul_one]
  have hDot : ringDot [c] [CommRingOps.one, CommRingOps.zero] = c := by
    rw [ringDot_cons_cons, ringDot_nil_left, LawfulCommRing.mul_one, LawfulCommRing.add_zero]
  rw [polyWitnessValid_def, decide_eq_true hLen, hCount, decide_eq_true hAg, decide_eq_true hDot]
  rfl

/-- Shape of the false instance, with its stage list spelled out. -/
private theorem falseInst_shape :
    hemFoldFalseInst.batchOracles.length = 1 ∧ hemFoldFalseInst.batchClaims.length = 1 ∧
      hemFoldFalseInst.initDomainPts = hemFoldDom64 ∧ hemFoldFalseInst.initDegBound = 0 ∧
      hemFoldFalseInst.initMinAgree = 43 ∧
      hemFoldFalseInst.stages = [hemFoldWitnessStage1, hemFoldWitnessStage2] := by
  rw [hemFoldFalseInst.public_eqs, hemFoldWitnessStages.public_eqs]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem falseInst_kernel :
    hemFoldFalseInst.initKernel = [CommRingOps.one, CommRingOps.zero] := by
  rw [hemFoldFalseInst.public_eqs]

private theorem falseInst_oracles :
    hemFoldFalseInst.batchOracles = [fun _ => CommRingOps.zero] := by
  rw [hemFoldFalseInst.public_eqs]

private theorem falseInst_claims : hemFoldFalseInst.batchClaims = [CommRingOps.one] := by
  rw [hemFoldFalseInst.public_eqs]

/-- The virtual fold of the zero oracle is the zero oracle. -/
private theorem virtualFold_zeroOracle (θ α β : QuarticGoldilocks)
    (D E : List QuarticGoldilocks) (O : Nat → QuarticGoldilocks)
    (hO : ∀ i, O i = CommRingOps.zero) (i : Nat) :
    hemVirtualFoldOracle θ α β D E O i = CommRingOps.zero := by
  rw [hemVirtualFoldOracle_def]
  simp only [hO, LawfulCommRing.sub_self, LawfulCommRing.add_zero, LawfulCommRing.mul_zero]

/-- The mutant verifier accepts the attack on the false statement for every challenge. -/
theorem dropped_fold_check_accepts_every_challenge (c₀ c₁ c₂ c₃ c₄ : Nat) :
    hemMultistageVerifyNoFoldCheck hemFoldDom64 hemFoldDom64 0 43 hemFoldWitnessStages
      hemFoldFalseInst (attackTranscript c₀ c₁ c₂ c₃ c₄) = true := by
  have hRun : hemMultistageRunWith hemFoldCommitStepUnchecked hemFoldDom64 hemFoldDom64 0 43
      hemFoldWitnessStages hemFoldFalseInst (attackTranscript c₀ c₁ c₂ c₃ c₄) = .accepted := by
    simp only [attackTranscript, hemFoldWitnessStages.public_eqs,
      hemMultistageRunWith.public_eqs, hemFoldRunStagesWith.public_eqs]
    rw [hemFoldCascadeStep_init hemFoldDom64 hemFoldDom64 0 43
      [hemFoldWitnessStage1, hemFoldWitnessStage2] hemFoldFalseInst CommRingOps.zero c₀
      falseInst_shape, falseInst_kernel, falseInst_claims]
    rw [hemFoldCrossStep_cur hemFoldDom64 hemFoldDom64 (0 + 1) (43 + 1) hemFoldWitnessStage1 _
      [CommRingOps.one, CommRingOps.zero] _ _ _ _ c₁ (by rfl)]
    rw [hemFoldShiftStep_mid, hemFoldCommitStepUnchecked_cur, hemKernelFold_pair]
    rw [hemFoldCrossStep_cur hemFoldDom64 hemFoldWitnessStage1.domainPts
      hemFoldWitnessStage1.degBound hemFoldWitnessStage1.minAgree hemFoldWitnessStage2 _
      [CommRingOps.one, CommRingOps.zero] _ _ _ _ c₃ (by rfl)]
    rw [hemFoldShiftStep_mid, hemFoldCommitStepUnchecked_cur, hemKernelFold_pair]
    simp only [hemFoldWitnessStage2.public_eqs]
    exact hemFoldFinalStep_cur _ _ _ _ _ _ _
      (constTable_final_valid hemFoldDom16 1 16 CommRingOps.one _ rfl (by decide))
  show hemFoldStateAccepted (hemMultistageRunWith hemFoldCommitStepUnchecked hemFoldDom64
    hemFoldDom64 0 43 hemFoldWitnessStages hemFoldFalseInst
    (attackTranscript c₀ c₁ c₂ c₃ c₄)) = true
  rw [hRun]
  exact hemFoldStateAccepted_accepted

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
  intro hAcc
  rw [hemMultistageVerify.public_eqs, hemMultistageRun.public_eqs] at hAcc
  simp only [attackTranscript, hemFoldWitnessStages.public_eqs,
    hemMultistageRunWith.public_eqs, hemFoldRunStagesWith.public_eqs] at hAcc
  rw [hemFoldCascadeStep_init hemFoldDom64 hemFoldDom64 0 43
    [hemFoldWitnessStage1, hemFoldWitnessStage2] hemFoldFalseInst CommRingOps.zero 0
    falseInst_shape, falseInst_kernel] at hAcc
  rw [hemFoldCrossStep_cur hemFoldDom64 hemFoldDom64 (0 + 1) (43 + 1) hemFoldWitnessStage1 _
    [CommRingOps.one, CommRingOps.zero] _ _ _ _ 0 (by rfl), hemFoldShiftStep_mid] at hAcc
  rw [hemFoldCommitStep_cur_reject] at hAcc
  · rw [hemFoldCrossStep_invalid, hemFoldShiftStep_invalid, hemFoldCommitStep_invalid,
      hemFoldFinalStep_invalid, hemFoldStateAccepted_invalid] at hAcc
    exact Bool.false_ne_true hAcc
  · apply Bool.eq_false_iff.mpr
    intro hTable
    rw [hemTableMatchesOracle.public_eqs] at hTable
    have hPos : 0 < hemFoldWitnessStage1.domainPts.length := by
      rw [hemFoldWitnessStage1.public_eqs, hemFoldDom32.public_eqs]
      decide +kernel
    have h0 := of_decide_eq_true (List.all_eq_true.mp hTable 0 (List.mem_range.mpr hPos))
    rw [tableToOracle_apply, virtualFold_zeroOracle _ _ _ _ _ _
      (fun i => by
        rw [falseInst_oracles, evalCascadeOracle_cons, evalCascadeOracle_nil,
          LawfulCommRing.mul_zero, LawfulCommRing.add_zero])] at h0
    revert h0
    simp only [attackNextClaim, attackClaim0, hemFoldClaimUpdate_def, evalCascadeClaim_cons,
      evalCascadeClaim_nil, prodPool_eq, threePool.public_eqs, hemFoldDom32.public_eqs]
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
theorem honestInst_valid : HemStatementValid honestInst := by
  rw [HemStatementValid_iff]
  refine ⟨by decide, ?_⟩
  show HemBatchValid hemFoldDom64 43 0 [CommRingOps.one, CommRingOps.zero]
    [fun idx => RoundPoly.evalCoeffs [CommRingOps.one] (hemFoldDom64.getD idx CommRingOps.zero)]
    [ringDot [CommRingOps.one] [CommRingOps.one, CommRingOps.zero]]
  rw [HemBatchValid_cons_cons_iff]
  refine ⟨⟨[CommRingOps.one], ?_⟩, HemBatchValid_nil_nil _ _ _ _⟩
  rw [polyWitnessValid_def, hemCosetAgreeCount_def, ringDot_cons_cons, ringDot_nil_left]
  decide +kernel

private theorem cascadePair (a b : QuarticGoldilocks) :
    evalCascadePolySum [[CommRingOps.one]] [(a,b)] = [a,b] := by
  simp only [evalCascadePolySum.public_eqs, polyScaleVar_def, shiftPoly_eq, List.map_cons, List.map_nil,
    polyAddVar, rawAddCoeffs, LawfulCommRing.mul_one, LawfulCommRing.mul_zero,
    LawfulCommRing.add_zero]

private theorem cascadePair' (p : QuarticGoldilocks × QuarticGoldilocks) :
    evalCascadePolySum [[CommRingOps.one]] [p] = [p.1, p.2] := by
  cases p with | mk a b => exact cascadePair a b

private theorem crossPair (a b : QuarticGoldilocks) :
    honestCross [a,b] [CommRingOps.one, CommRingOps.zero] = .cross a CommRingOps.zero b := by
  simp only [honestCross, splitEvenOdd.public_eqs, ringDot_cons_cons, ringDot_nil_right, LawfulCommRing.mul_one,
    LawfulCommRing.mul_zero, LawfulCommRing.add_zero]

private theorem shiftPair (a b : QuarticGoldilocks) :
    honestShift [a,b] [CommRingOps.one, CommRingOps.zero] = .shift CommRingOps.zero CommRingOps.zero := by
  simp only [honestShift, splitEvenOdd.public_eqs, shiftPoly_eq, ringDot_cons_cons, ringDot_nil_right,
    LawfulCommRing.zero_mul, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]

private theorem foldPair (S : List QuarticGoldilocks) (c : Nat) (a b : QuarticGoldilocks) :
    let t := (threePool S S).getD c (CommRingOps.zero, CommRingOps.zero, CommRingOps.zero)
    honestFold S c [a,b] = [linearNextA a b t.1 t.2.1, linearNextB a b t.1 t.2.2] := by
  simp only [honestFold, splitEvenOdd.public_eqs, affineCombine_def, polyScaleVar_def, shiftPoly_eq,
    List.map_cons, List.map_nil, polyAddVar, rawAddCoeffs, linearNextA.public_eqs, linearNextB.public_eqs,
    LawfulCommRing.mul_zero, LawfulCommRing.add_zero]

private theorem mapPair (D : List QuarticGoldilocks) (a b : QuarticGoldilocks) :
    D.map (RoundPoly.evalCoeffs [a,b]) = linearTable D a b := by
  rw [linearTable.public_eqs]
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
      RoundPoly.evalCoeffs_cons, RoundPoly.evalCoeffs_nil, linearOracle.public_eqs,
      LawfulCommRing.mul_zero, LawfulCommRing.add_zero, LawfulCommRing.mul_one]
  have hO₁ : ∀ i, i < hemFoldDom32.length →
      tableToOracle (linearTable hemFoldDom32 a₁ b₁) i = linearOracle hemFoldDom32 a₁ b₁ i :=
    fun i hi => by
      rw [linearTable.public_eqs]
      exact linearTable_toOracle _ _ _ _ hi
  rw [hemMultistageVerify.public_eqs, hemMultistageRun.public_eqs]
  rw [honestTranscript_linear]
  simp only [hemFoldWitnessStages.public_eqs, hemMultistageRunWith.public_eqs,
    hemFoldRunStagesWith.public_eqs]
  rw [hemFoldCascadeStep_init hemFoldDom64 hemFoldDom64 0 43
    [hemFoldWitnessStage1, hemFoldWitnessStage2] honestInst CommRingOps.zero 5
    ⟨rfl, rfl, rfl, rfl, rfl, by simp only [honestInst, hemFoldWitnessStages.public_eqs]⟩]
  have hc : evalCascadeClaim honestInst.batchClaims [CommRingOps.zero] [p] = p.1 := by
    simp only [honestInst, ringDot_cons_cons, ringDot_nil_left, evalCascadeClaim_cons, evalCascadeClaim_nil,
      LawfulCommRing.mul_one, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  rw [hc, show honestInst.initKernel = [CommRingOps.one, CommRingOps.zero] from rfl]
  have h₁ := linearStage_complete hemFoldDom64 _ _
    (hemFoldStageGeom_antipodal hemFoldWitnessGeom1)
    (by rw [hemFoldWitnessStage1.public_eqs]) 44 _ p.1 p.2 hO 3 77
  have h₂ := linearStage_complete hemFoldDom64 _ _
    (hemFoldStageGeom_antipodal hemFoldWitnessGeom2)
    (by rw [hemFoldWitnessStage2.public_eqs]) 28 _ a₁ b₁ hO₁ 9 1000
  simp only [hemFoldWitnessStage1.public_eqs] at h₁
  simp only [hemFoldWitnessStage2.public_eqs] at h₂
  simp only [hemFoldWitnessStage1.public_eqs, hemFoldWitnessStage2.public_eqs]
  rw [h₁, h₂]
  rw [hemFoldFinalStep_cur _ _ _ _ _ _ _
    (linearTable_final_valid hemFoldDom16 a₂ b₂ 16 (by decide +kernel))]
  exact hemFoldStateAccepted_accepted

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
  simp only [hemFoldWitnessStages.public_eqs, hemFoldStageRoundBudgets.public_eqs,
    hemWelchBerlekampBudget.public_eqs, hemFoldWitnessStage1.public_eqs,
    hemFoldWitnessStage2.public_eqs, hemFoldDom32.public_eqs, prodPool_length, threePool_length]
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
