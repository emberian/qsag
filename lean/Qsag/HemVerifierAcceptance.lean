module
/-
# Acceptance facts about the concrete Hem transcript checker

These results inspect `verifyHemAffineWhir`; they do not assume an acceptance cover.
The malformed-batch regression records why the oracle/claim arity check is necessary.
The zero-oracle family below gives a concrete false-statement case in which acceptance
forces a linear challenge collision. This is not a proof for arbitrary Hem statements,
nor a refinement of the Rust Fiat–Shamir transcript parser.
-/
public import Qsag.HemWhirRbrSoundness
import all Qsag.HemWhirRbrSoundness
import all Qsag.MultiRoundFsQrom

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

/-- The former checker, retained only as the mutation under test: it forgets to compare
    the number of batch claims to the number of batch oracles. -/
private def verifyHemMissingBatchArity {F : Type} [CommRingOps F] [DecidableEq F]
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

private def missingClaimInstance : HemWhirInstance QuarticGoldilocks :=
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
    ¬ HemStatementValid missingClaimInstance ∧
    verifyHemMissingBatchArity missingClaimInstance
      [.cascade [] [] [[]], .finalQuery []] = true ∧
    verifyHemAffineWhir missingClaimInstance
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

end Qsag
