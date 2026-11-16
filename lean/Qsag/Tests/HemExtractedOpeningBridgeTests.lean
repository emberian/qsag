module
import all Qsag.Math.GoldilocksBase
public import Qsag.Protocol.Aggregation.QromSaltedMerkleStateRestoration
/- Executed, nonconstant decoder consuming openings and the actual Hem checker. -/
public import Qsag.Protocol.Aggregation.HemOpening
public import Qsag.Tests.OracleAndQrom
import all Qsag.Protocol.Aggregation.HemOpening
import all Qsag.Protocol.Aggregation.QromSaltedMerkleStateRestoration
import all Qsag.Oracle.Qrom
import all Qsag.Tests.OracleAndQrom
import all Qsag.Protocol.Aggregation.MultiRoundFsQrom
import all Qsag.Protocol.Aggregation.HemRbrSoundness
import all Qsag.Protocol.Aggregation.ConcreteSecurityBudget
import all Qsag.Coding.Cwyz26
import all Qsag.Coding.GuruswamiSudan
import all Qsag.Coding.ReedSolomon
import all Qsag.Math.Counting
import all Qsag.Math.CoeffPoly
import all Qsag.Math.PolyRing
import all Qsag.Math.QuarticExt4
import all Qsag.Math.Goldilocks
import all Qsag.Math.Primality

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

/-
Fixtures, teeth and inhabitation witnesses of `Protocol/Aggregation/HemOpening.lean`. Each one
evaluates the concrete Hem checker, the Guruswami–Sudan decoder or the deployed tables over
`QuarticGoldilocks` in the kernel, so it needs the bodies of those definitions.
-/

public section
namespace Qsag
set_option autoImplicit false
set_option exponentiation.threshold 2048
set_option maxRecDepth 65536

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

/-- Regression for the old unincremented checker: the restricted cascade IOP
    already required the stronger agreement threshold now enforced by the full checker. -/
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
    mutantVerifyHemAffineWhirUnincremented hemCoreAgreementBoundaryInstance
      (assembleHemCoreTranscript S tr) = true ∧
    verifyHemAffineWhir hemCoreAgreementBoundaryInstance (assembleHemCoreTranscript S tr) = false ∧
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

#verify_constructive
  Qsag.tooth_missing_batch_claim_erases_oracle
  Qsag.tooth_core_agreement_is_stronger_than_checker
  Qsag.hemZeroOracle_acceptance_nontrivial

/-- The fixed-theta invalid-mixture premise cannot be dropped: two identical zero words
    with false claim one have a valid zero claim after theta=-1 mixing. This is a witness
    to the need for a theta-exception argument, not a counterexample to a bounded lift. -/
theorem tooth_equal_degree_invalid_mixture :
    let D : List QuarticGoldilocks := [CommRingOps.zero, CommRingOps.one]
    (∀ P : List QuarticGoldilocks,
      polyWitnessValid D 2 0 (fun _ => CommRingOps.zero) [CommRingOps.one] CommRingOps.one P = false) ∧
    polyWitnessValid D 2 0
      (fun _ => CommRingOps.add CommRingOps.zero
        (CommRingOps.mul (CommRingOps.sub CommRingOps.zero CommRingOps.one) CommRingOps.zero))
      [CommRingOps.one]
      (CommRingOps.add CommRingOps.one
        (CommRingOps.mul (CommRingOps.sub CommRingOps.zero CommRingOps.one) CommRingOps.one)) [] = true := by
  refine ⟨?_, by decide⟩
  intro P
  cases hv : polyWitnessValid [CommRingOps.zero, CommRingOps.one] 2 0
      (fun _ => (CommRingOps.zero : QuarticGoldilocks)) [CommRingOps.one] CommRingOps.one P with
  | false => rfl
  | true =>
    have h0 := polyWitnessValid_zeroOracle_claim [CommRingOps.zero, CommRingOps.one] 0 2
      [CommRingOps.one] P CommRingOps.one (by decide) (by decide) hv
    exact False.elim ((by decide : (CommRingOps.one : QuarticGoldilocks) ≠ CommRingOps.zero) h0)

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
      ((whirAffineStageWitnesses 24 true).get ⟨0, by decide⟩)) := by
  decide +kernel

#verify_constructive
  Qsag.tooth_equal_degree_invalid_mixture
  Qsag.tooth_sliced_nv24_profile_margin

/-- Concrete inhabited failure fragment at the deployed digest width. The
opening has a nonzero leaf and sibling, verifies its root, and is absent from
the pre-challenge table. This is the same predicate used by committee refusal. -/
theorem batchMerkleFailure_inhabited_256 {cardX : Nat}
    (L : MerkleAddressLayout cardX 256) (hLevels : 1 ≤ L.levels) (hNodes : 0 < L.nodes) :
    ∃ (slot : MerkleOpeningSlot cardX 256) (H : Fin cardX → BitVec 256) (out : Fin cardX),
      slot.level + slot.depth ≤ L.levels ∧ batchMerkleFailure L [slot] H [] out = true := by
  let slot : MerkleOpeningSlot cardX 256 :=
    ⟨0, 1, fun _ => ⟨0#256, 0, 1#256, [2#256]⟩⟩
  refine ⟨slot, fun _ => 0#256, L.encode 0 0 1#256 2#256, hLevels, ?_⟩
  simp [batchMerkleFailure, measuredMerkleFailure, merkleOpeningShape,
    merkleRootFromPath, MerkleAddressLayout.hash, merkleRecords,
    extractOnlineMerkleOpening, findFirst, slot, hNodes]

#verify_constructive batchMerkleFailure_inhabited_256

def qgNat : Nat → QuarticGoldilocks
  | 0 => CommRingOps.zero
  | n + 1 => CommRingOps.add (qgNat n) CommRingOps.one

def toothDeg1Dom : List QuarticGoldilocks :=
  [qgNat 0, qgNat 1, qgNat 2, qgNat 3]

def toothDeg1Pool : List QuarticGoldilocks :=
  [qgNat 0, qgNat 1, CommRingOps.sub CommRingOps.zero CommRingOps.one]

/-- **Equal-Degree `θ`-Exception Necessity Counterexample (`tooth_equal_degree_drop_theta_exception_unsound`)**:
    Let `D = [0, 1, 2, 3]`, `S = [0, 1, -1]`, `d = 0, A = 3`, `f(z) = z`, `g(z) = z`, and all claims `0`.
    Neither `(f, 0)` nor `(g, 0)` admits any degree-`≤ 0` witness at agreement `≥ A - 1 = 2`
    (`gsDecodeList 0 2 D id = []`). Yet at `θ = -1` (`iθ = 2`), `f + θ g = 0` and **all**
    `|prodPool S| = 9 = |S|^2` pairs `(α, β)` accept `P(X) = X` (`deg 1 ≤ d + 1`), proving that
    the `(badTheta + ...) · |prodPool S|` term in `equal_degree_three_challenge_bound` cannot be omitted. -/
theorem tooth_equal_degree_drop_theta_exception_unsound :
    ∃ iθ : Fin toothDeg1Pool.length,
      (gsDecodeList 0 2 toothDeg1Dom (fun z => z)).length = 0 ∧
      (∀ Fp : List QuarticGoldilocks, Fp.length ≤ 1 →
        2 ≤ (toothDeg1Dom.filter (fun z => decide (RoundPoly.evalCoeffs Fp z = z))).length → False) ∧
      (prodPool toothDeg1Pool).length = 9 ∧
      ∀ ch : Fin (prodPool toothDeg1Pool).length,
        affineMcaAccepts toothDeg1Dom toothDeg1Pool 1 4
          ((fun z => z),
           fun z => CommRingOps.add z (CommRingOps.mul (toothDeg1Pool.get iθ) z))
          ch.1 [qgNat 0, qgNat 1] = true ∧
        ringDot [qgNat 0, qgNat 1] [qgNat 1] =
          hemFoldClaimUpdate (qgNat 0) (qgNat 0) (qgNat 0) (qgNat 0)
            (toothDeg1Pool.get iθ)
            ((prodPool toothDeg1Pool).get ch).1 ((prodPool toothDeg1Pool).get ch).2 := by
  have hEmpty : gsDecodeList 0 2 toothDeg1Dom (fun z => z) = [] := by decide +kernel
  have hD : toothDeg1Dom.Nodup := by decide +kernel
  refine ⟨⟨2, by decide⟩, by rw [hEmpty]; rfl, ?_, by decide +kernel, by decide +kernel⟩
  intro Fp hLen hAg
  let pF : GsUniPoly QuarticGoldilocks := GsUniPoly.ofCoeffs Fp
  have hpAg : 2 ≤ (toothDeg1Dom.filter (fun z => decide (RoundPoly.evalCoeffs pF.val z = z))).length := by
    have hEq : toothDeg1Dom.filter (fun z => decide (RoundPoly.evalCoeffs pF.val z = z)) =
        toothDeg1Dom.filter (fun z => decide (RoundPoly.evalCoeffs Fp z = z)) :=
      congrArg (fun q => List.filter q toothDeg1Dom) (funext fun z => by
        show decide (RoundPoly.evalCoeffs (trimPoly Fp) z = z) = _
        rw [evalCoeffs_trimPoly])
    rw [hEq]; exact hAg
  have hpMem : pF ∈ gsDecodeList 0 2 toothDeg1Dom (fun z => z) :=
    (mem_gsDecodeList_iff (fun z => z) hD (by decide) pF).mpr
      ⟨Nat.le_trans (trimPoly_length_le Fp) hLen, hpAg⟩
  rw [hEmpty] at hpMem
  cases hpMem

/-- **Unincremented Cascade Agreement Counterexample
    (`tooth_verifyHemAffineWhir_unincremented_agree_accepts_all`)**:
    In `mutantVerifyHemAffineWhirUnincremented`, `.cascade` checks `polyWitnessValid` at
    `inst.initMinAgree` (`A₀`) rather than `A₀ + 1`. At `domPts = [0, 1, 2]`, `d₀ = 0`, `A₀ = 2`,
    the oracle `0 ↦ 1, _ ↦ 0` with claim `1` violates `HemStatementValid inst` at `A₀ = 2`, yet
    has an `(A₀ - 1) = 1`-agreeing witness `G = [1]` and therefore passes the deliberately stale verifier
    via `P(z) = α - α z` on **every** `(α, β) ∈ prodPool S` (`100%` acceptance)!
    This proves that the `initMinAgree - 1` premise in `arbitrary_batch_cascade_fiber_bound`
    cannot be weakened to `¬ HemStatementValid inst` without the agreement increment now enforced by `verifyHemAffineWhir`. -/
def toothUnincCascadeInst : HemWhirInstance QuarticGoldilocks :=
  { batchOracles := [fun idx => if idx = 0 then qgNat 1 else qgNat 0]
    batchClaims := [qgNat 1]
    initDomainPts := [qgNat 0, qgNat 1, qgNat 2]
    initDegBound := 0
    initMinAgree := 2
    initKernel := [qgNat 1]
    stages := [] }

theorem tooth_verifyHemAffineWhir_unincremented_agree_accepts_all :
    ∃ inst : HemWhirInstance QuarticGoldilocks,
      ¬ HemStatementValid inst ∧
      HemStatementValid { inst with initMinAgree := 1 } ∧
      ∀ ch : Fin (prodPool toothDeg1Pool).length,
        let p := (prodPool toothDeg1Pool).get ch
        let P : List QuarticGoldilocks := [p.1, CommRingOps.sub CommRingOps.zero p.1]
        mutantVerifyHemAffineWhirUnincremented inst
          [.cascade [qgNat 0] [p] [P], .finalQuery P] = true := by
  refine ⟨toothUnincCascadeInst, ?_, ⟨by decide, ⟨[qgNat 1], by decide +kernel⟩, trivial⟩, by decide +kernel⟩
  rintro ⟨_, ⟨G, hG⟩, _⟩
  unfold polyWitnessValid toothUnincCascadeInst at hG
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hG
  rcases hG with ⟨⟨hGLen, hGAg⟩, hGDot⟩
  rcases G with _ | ⟨c, _ | _⟩
  · change CommRingOps.zero = qgNat 1 at hGDot
    exact (by decide : CommRingOps.zero ≠ qgNat 1) hGDot
  · have hOne : qgNat 1 = CommRingOps.one := by decide
    have hc1 : c = CommRingOps.one := by
      rw [hOne] at hGDot
      simpa only [ringDot_cons_cons, ringDot_nil_left, ringDot_nil_right, LawfulCommRing.mul_one, LawfulCommRing.add_zero] using hGDot
    subst hc1
    exact absurd hGAg (by decide +kernel)
  · simp only [List.length_cons] at hGLen
    omega

/-- The repaired verifier rejects the old attack at a nonzero challenge; the zero
    challenge still legitimately belongs to the bad-challenge set. -/
theorem tooth_incremented_cascade_rejects_old_attack :
    ∃ P : List QuarticGoldilocks,
    mutantVerifyHemAffineWhirUnincremented toothUnincCascadeInst
      [.cascade [qgNat 0] [(qgNat 1, qgNat 0)] [P], .finalQuery P] = true ∧
    verifyHemAffineWhir toothUnincCascadeInst
      [.cascade [qgNat 0] [(qgNat 1, qgNat 0)] [P], .finalQuery P] = false := by
  refine ⟨[qgNat 1, CommRingOps.sub (qgNat 0) (qgNat 1)], ?_⟩
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
   by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ## §4. Non-Vacuity Inhabitedness Witnesses & Assurance Gates -/

private def witEqDegDom : List QuarticGoldilocks := [qgNat 0, qgNat 1, qgNat 2, qgNat 3]

private theorem witEqDegDecomp3 :
    AffineFoldDecompBound witEqDegDom witEqDegDom 1 3 16 := by
  intro _ L hNd _
  have hLen : (prodPool witEqDegDom).length = 16 := by decide +kernel
  rw [← hLen]
  exact nodup_length_le_of_subset hNd (fun ch _ => List.mem_finRange ch)

private theorem witEqDegDecomp4 :
    AffineFoldDecompBound witEqDegDom witEqDegDom 1 4 16 := by
  intro _ L hNd _
  have hLen : (prodPool witEqDegDom).length = 16 := by decide +kernel
  rw [← hLen]
  exact nodup_length_le_of_subset hNd (fun ch _ => List.mem_finRange ch)

private theorem witEqDegMixList :
    ∀ θ : QuarticGoldilocks,
      (gsDecodeList 0 3 witEqDegDom
        (fun _ => CommRingOps.add (qgNat 0) (CommRingOps.mul θ (qgNat 0)))).length ≤ 1 := by
  intro θ
  have hZero : (fun _ : QuarticGoldilocks => CommRingOps.add (qgNat 0) (CommRingOps.mul θ (qgNat 0))) =
      (fun _ => CommRingOps.zero) := by
    funext _; dsimp only [qgNat]; rw [LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  rw [hZero]
  exact gsDecodeList_zero_length_le_one witEqDegDom 0 3 (by decide +kernel) (by decide)

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
    exact (by decide : CommRingOps.zero ≠ qgNat 1) hDot
  · have hOne : qgNat 1 = CommRingOps.one := by decide
    have hc1 : c = CommRingOps.one := by
      rw [hOne] at hDot
      simpa only [ringDot_cons_cons, ringDot_nil_left, ringDot_nil_right, LawfulCommRing.mul_one, LawfulCommRing.add_zero] using hDot
    subst hc1
    exact absurd hAg (by decide +kernel)
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
   by decide +kernel, by decide +kernel, by decide, by decide, by decide,
   witEqDegDecomp3, witEqDegDecomp4, witEqDegMixList, witEqDegInvalid, .nil, fun _ h => nomatch h⟩

private def witCascInst : HemWhirInstance QuarticGoldilocks :=
  hemZeroOracleClaimInstance witEqDegDom 0 3 []

private theorem witCascInstInvalidPrev :
    ¬ HemStatementValid { witCascInst with initMinAgree := witCascInst.initMinAgree - 1 } :=
  hemZeroOracleClaimInstance_invalid witEqDegDom 0 2 [] (by decide +kernel) (by decide)

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
   by decide, rfl, rfl, rfl, by decide +kernel, by decide +kernel, by decide,
   witEqDegDecomp3, witCascInstInvalidPrev⟩

private def witStage24 : HemStageGeom := (hemStageGeoms 24).get ⟨0, by decide⟩

theorem witness_cdhz_sliced_stage_clears_128bits_at_2pow50 :
    ∃ (nv : Nat) (g : HemStageGeom),
      2 ≤ nv ∧ nv ≤ 24 ∧ g ∈ hemStageGeoms nv ∧ hemJohnsonQromStageExhaustive g = false :=
  ⟨24, witStage24, by decide, by decide, list_get_mem (hemStageGeoms 24) ⟨0, by decide⟩, by decide +kernel⟩

#tooth_pair Qsag.hemNextMinAgree_increments vs Qsag.tooth_incremented_cascade_rejects_old_attack
theorem inhabited_recursive_nv30_sliced_stage :
    ∃ (nv childCap : Nat) (g : HemStageGeom),
      nv = 30 ∧ childCap = 24 ∧ 2 ≤ nv ∧ 2 ≤ childCap ∧ childCap ≤ 24 ∧
      g ∈ hemRecursiveStageGeoms nv childCap ∧ hemJohnsonQromStageExhaustive g = false := by
  refine ⟨30, 24, witStage24, rfl, rfl, by decide, by decide, by decide, ?_, ?_⟩
  · exact list_get_mem (hemStageGeoms 24) ⟨0, by decide⟩
  · decide +kernel

#verify_inhabited cdhz_recursive_sliced_stage_clears_128bits_at_2pow50 witness_cdhz_sliced_stage_clears_128bits_at_2pow50

#tooth_pair Qsag.equal_degree_three_challenge_bound Qsag.tooth_equal_degree_drop_theta_exception_unsound
#tooth_pair Qsag.arbitrary_batch_cascade_fiber_bound Qsag.tooth_verifyHemAffineWhir_unincremented_agree_accepts_all
#tooth_pair Qsag.arbitrary_batch_incremented_cascade_fiber_bound Qsag.tooth_verifyHemAffineWhir_unincremented_agree_accepts_all
#tooth_pair Qsag.cdhz_sliced_stage_clears_128bits_at_2pow50 Qsag.tooth_dfmRoundScale_fails_128bits_at_2pow50

#verify_inhabited Qsag.equal_degree_three_challenge_bound Qsag.witness_equal_degree_three_challenge_bound
#verify_inhabited Qsag.arbitrary_batch_cascade_fiber_bound Qsag.witness_arbitrary_batch_cascade_fiber_bound
#verify_inhabited Qsag.cdhz_sliced_stage_clears_128bits_at_2pow50 Qsag.witness_cdhz_sliced_stage_clears_128bits_at_2pow50

#verify_constructive
  Qsag.tooth_equal_degree_drop_theta_exception_unsound
  Qsag.tooth_verifyHemAffineWhir_unincremented_agree_accepts_all
  Qsag.tooth_dfmRoundScale_fails_128bits_at_2pow50

end Qsag
end
