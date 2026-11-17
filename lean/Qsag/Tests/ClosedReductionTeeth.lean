module
/-
# Qsag.Tests.ClosedReductionTeeth — mutation teeth for `Qsag.Top.ClosedProtocolReductions`

* `inhabited_whir_exec_closed_qrom_soundness_hypotheses`: the hypotheses of
  `Top.whir_exec_closed_qrom_soundness` are jointly satisfiable at a schedule with one stage
  (`ClosedWhir.sampledQueryCert`), with a statement outside the language.
* `tooth_sampled_query_cert_state_not_constantly_false`,
  `tooth_sampled_query_zero_flip_claim_is_false`: that certificate's verifier accepts an honest
  transcript, and accepts the false statement on one challenge, so neither "always rejects" nor
  "never errs" holds for it.
* Pairs with the negative controls proved in `Qsag.Protocol.Aggregation.ClosedWhirSchedule`
  (they evaluate that module's definitions, so they are proved there): list sizes dropped from
  the deployed stages, a stage beyond the Johnson radius, the stage-free schedule.
* `tooth_lying_opening_yields_collision`: under a leaf hash that only keeps the parity, an
  accepted opening of `5` against a committed `7` makes `findCollision` return a witness;
  `inhabited_honest_opening_no_collision`: the honest opening returns none. These two evaluate
  `ClosedFs.findCollision`, whose body is not exported by `ClosedFsQromCompile`.
* The epoch-latch tooth lives in `Qsag.Tests.ClosedEufCmaTeeth`.
-/

public import Qsag.Top.ClosedProtocolReductions
public import Qsag.Protocol.Aggregation.ClosedWhirSchedule
public import Qsag.Protocol.Aggregation.ClosedFsQromCompile
public import Qsag.Protocol.Aggregation.QromSaltedMerkleStateRestoration
public import Qsag.Protocol.Aggregation.MultiRoundFsQrom
public import Qsag.Protocol.Aggregation.ConcreteSecurityBudget
public import Qsag.Coding.Cwyz26
public import Qsag.Protocol.Aggregation.HemOpening
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.ClosedReductionTeeth

open Qsag Qsag.ClosedWhir Qsag.ClosedFs

set_option autoImplicit false
set_option exponentiation.threshold 100000

-- `parityLeafSetup`, `tooth_lying_opening_yields_collision` and `inhabited_honest_opening_no_collision`
-- are proved in `Protocol/Aggregation/ClosedFsQromCompile` (they execute `findCollision`, sealed here).

#verify_constructive Qsag.ClosedReductionTeeth.tooth_lying_opening_yields_collision
#verify_constructive Qsag.ClosedReductionTeeth.inhabited_honest_opening_no_collision

/-! ### The constructed `WhirScheduleCert` -/

/-- **Inhabitedness of the hypotheses of `Top.whir_exec_closed_qrom_soundness`** at a schedule
    with a stage: an environment, a schedule passing the Johnson check, a certificate, and a
    statement outside the language. Only the Merkle setup, the codec and the adversary are left
    to the caller. -/
theorem inhabited_whir_exec_closed_qrom_soundness_hypotheses :
    ∃ (env : WhirEnv Goldilocks) (sched : WhirVerifierSchedule)
      (_ : WhirScheduleCert env sched 2) (x : WhirStmt Goldilocks),
      sched.stages.length = 1 ∧ sched.johnsonOk = true ∧ ¬ whirInLang env sched x :=
  ⟨sampledQueryEnv, sampledQuerySched, sampledQueryCert,
    ⟨[Goldilocks.one, Goldilocks.one, Goldilocks.one, Goldilocks.one], Goldilocks.zero⟩,
    sampledQuerySched_shape.1, sampledQuerySched_shape.2.1, sampledQuery_false_not_inLang⟩

/-- `#tooth` The constructed certificate is not the all-rejecting one: its verifier accepts the
    honest transcript, so "the state function is constantly false" is refuted for it. -/
theorem tooth_sampled_query_cert_state_not_constantly_false :
    ¬ (∀ (x : WhirStmt Goldilocks) (tr : List (WhirMsg Goldilocks × Nat)),
        sampledQueryCert.cert.state x tr = false) := by
  intro h
  have hAcc := sampledQueryCert.cert.accept _ _ sampledQuery_honest_accepts.1
  rw [h] at hAcc
  exact Bool.false_ne_true hAcc

/-- `#tooth` Soundness of the one-stage verifier is not perfect: the false statement is accepted
    on a query challenge, so a certificate claiming zero flips in the query round would be
    wrong. -/
theorem tooth_sampled_query_zero_flip_claim_is_false :
    ¬ (∀ (m0 m1 : WhirMsg Goldilocks) (c0 c1 : Nat),
        (whirOracleIop sampledQueryEnv sampledQuerySched 2).verify
          ⟨[Goldilocks.one, Goldilocks.one, Goldilocks.one, Goldilocks.one], Goldilocks.zero⟩
          [(m0, c0), (m1, c1)] = false) := by
  intro h
  have hAcc := sampledQuery_false_statement_accepted_once.1
  rw [h] at hAcc
  exact Bool.false_ne_true hAcc

#verify_constructive Qsag.ClosedReductionTeeth.inhabited_whir_exec_closed_qrom_soundness_hypotheses
#verify_constructive Qsag.ClosedReductionTeeth.tooth_sampled_query_cert_state_not_constantly_false
#verify_constructive Qsag.ClosedReductionTeeth.tooth_sampled_query_zero_flip_claim_is_false

#tooth_pair Qsag.Top.sampledQueryWhir_closed_qrom_soundness vs
  Qsag.ClosedReductionTeeth.tooth_sampled_query_cert_state_not_constantly_false
#tooth_pair Qsag.ClosedWhir.sampledQuery_query_round_flips vs
  Qsag.ClosedReductionTeeth.tooth_sampled_query_zero_flip_claim_is_false
#tooth_pair Qsag.Top.whir_exec_closed_qrom_soundness vs
  Qsag.ClosedWhir.tooth_empty_schedule_rejects
#tooth_pair Qsag.Top.deployed_whir_exec_closed_qrom_128 vs
  Qsag.ClosedWhir.tooth_omitting_list_size_lowers_every_fold_bound
#tooth_pair Qsag.ClosedFs.openings_agree vs
  Qsag.ClosedReductionTeeth.tooth_lying_opening_yields_collision

end Qsag.ClosedReductionTeeth
end
