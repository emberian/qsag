module
/-
# Qsag.Tests.ClosedReductionTeeth — mutation teeth for `Qsag.Top.ClosedProtocolReductions`

* `tooth_omitting_list_size_factor_underestimates_error`: the deployed schedule with every
  list size set to `1` has a strictly smaller `scheduleQromError`, and
  `tooth_omitting_list_size_fails_johnson_check`: that schedule is rejected by `johnsonOk`.
* `tooth_beyond_johnson_radius_invalidates_certificate`: the first deployed stage with its
  agreement lowered to `n / 2` (`A² ≤ n·d`) fails `johnsonOk` for every slack and list size.
* `tooth_lying_opening_yields_collision`: under a leaf hash that only keeps the parity, an
  accepted opening of `5` against a committed `7` makes `findCollision` return a witness;
  `inhabited_honest_opening_no_collision`: the honest opening returns none.
* The epoch-latch tooth lives in `Qsag.Tests.ClosedEufCmaTeeth`.
-/

public import Qsag.Top.ClosedProtocolReductions
public import Qsag.Tests.ClosedEufCmaTeeth
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

open Qsag.ClosedWhir Qsag.ClosedFs

set_option autoImplicit false
set_option exponentiation.threshold 100000

def dropListSize (s : WhirStage) : WhirStage := { s with listSize := 1 }

/-- The deployed schedule with the Johnson list-size multipliers omitted. -/
def deployedNoList : WhirVerifierSchedule :=
  ⟨24, goldilocksExt4Card, goldilocksExt4Card_pos, deployedStages.map dropListSize⟩

theorem tooth_omitting_list_size_factor_underestimates_error :
    ¬ (RatBound.le (scheduleQromError deployedSched (2 ^ 40))
        (scheduleQromError deployedNoList (2 ^ 40))) := by
  unfold RatBound.le
  decide +kernel

theorem tooth_omitting_list_size_fails_johnson_check :
    ¬ (deployedNoList.johnsonOk = true) := by
  decide +kernel

/-- First deployed stage with agreement `n / 2`, any slack `e / E` and any list size `L`. -/
def beyondRadiusStage (e E L : Nat) : WhirStage :=
  { foldK := 6, logDomain := 20, logInvRate := 2, oodCount := 2, queryCount := 216,
    degBound := 262146, agree := 524288, etaNum := e, etaDen := E, listSize := L,
    sumcheckDeg := 3, mcaNum := 0 }

theorem tooth_beyond_johnson_radius_invalidates_certificate (e E L : Nat) :
    ¬ ((beyondRadiusStage e E L).johnsonOk = true) := by
  have h : (beyondRadiusStage e E L).johnsonOk = false :=
    WhirStage.johnsonOk_false_of_beyond_radius _ (by
      show (524288 : Nat) * 524288 ≤ 2 ^ 20 * 262146
      decide +kernel)
  rw [h]
  exact Bool.false_ne_true

/-- Node hash keeping the left child, leaf hash keeping the parity of the value. -/
def parityLeafSetup : MerkleSetup Nat Nat := ⟨fun _ _ a _ => a, fun _ _ v => v % 2⟩

theorem tooth_lying_opening_yields_collision :
    ¬ (findCollision parityLeafSetup (fun _ => 0) (fun _ _ => 7) [(0, 0)] [(5, [])] = none) := by
  decide +kernel

theorem inhabited_honest_opening_no_collision :
    findCollision parityLeafSetup (fun _ => 0) (fun _ _ => 7) [(0, 0)] [(7, [])] = none := by
  decide +kernel

#verify_constructive Qsag.ClosedReductionTeeth.tooth_omitting_list_size_factor_underestimates_error
#verify_constructive Qsag.ClosedReductionTeeth.tooth_omitting_list_size_fails_johnson_check
#verify_constructive Qsag.ClosedReductionTeeth.tooth_beyond_johnson_radius_invalidates_certificate
#verify_constructive Qsag.ClosedReductionTeeth.tooth_lying_opening_yields_collision
#verify_constructive Qsag.ClosedReductionTeeth.inhabited_honest_opening_no_collision

#tooth_pair Qsag.ClosedWhir.deployedSched_error_at_2pow40 vs
  Qsag.ClosedReductionTeeth.tooth_omitting_list_size_factor_underestimates_error
#tooth_pair Qsag.ClosedWhir.deployedSched_johnsonOk vs
  Qsag.ClosedReductionTeeth.tooth_omitting_list_size_fails_johnson_check
#tooth_pair Qsag.ClosedWhir.deployedSched_johnsonOk vs
  Qsag.ClosedReductionTeeth.tooth_beyond_johnson_radius_invalidates_certificate
#tooth_pair Qsag.ClosedFs.openings_agree vs
  Qsag.ClosedReductionTeeth.tooth_lying_opening_yields_collision

end Qsag.ClosedReductionTeeth
end

public section
namespace Qsag.ClosedWhir
open Qsag.ClosedFs
variable {F : Type} [Qsag.LawfulField F] [DecidableEq F]
/-- The certificate type is inhabited at the stage-free schedule, whose verifier rejects. -/
def emptyScheduleCert (env : WhirEnv F) (nv q : Nat) (hq : 0 < q) (w : Nat) :
    WhirScheduleCert env ⟨nv, q, hq, []⟩ w where
  cert :=
    { state := fun _ _ => false
      bad := fun r => Fin.elim0 r
      init := fun _ _ => rfl
      accept := fun x tr h => by
        have hv : (decide (tr.length = 0) &&
            whirVerdict env ⟨nv, q, hq, []⟩ x.claim
              (tr.map (fun mc => ((⟨mc.1.poly, mc.1.answers⟩ : WhirPub F), mc.2)))
              ((whirQueries env ⟨nv, q, hq, []⟩
                (tr.map (fun mc => ((⟨mc.1.poly, mc.1.answers⟩ : WhirPub F), mc.2)))).map
                (fun qq => whirTable ⟨nv, q, hq, []⟩ x (tr.map (fun mc => mc.1)) qq.1 qq.2))) =
            true := h
        rw [Bool.and_eq_true] at hv
        have hLen : tr = [] := List.eq_nil_of_length_eq_zero (of_decide_eq_true hv.1)
        rw [hLen] at hv
        exact absurd hv.2 Bool.false_ne_true
      flip := fun _ _ r _ _ _ _ => Fin.elim0 r }
  covers := fun r => Fin.elim0 r

/-- A stage-free certificate supplies no accepting transcript; it is only a negative control. -/
theorem tooth_empty_schedule_rejects (env : WhirEnv F) (nv q w : Nat) (hq : 0 < q)
    (x : WhirStmt F) (tr : List (WhirMsg F × Nat)) :
    (whirOracleIop env ⟨nv, q, hq, []⟩ w).verify x tr = false := by
  cases h : (whirOracleIop env ⟨nv, q, hq, []⟩ w).verify x tr
  · rfl
  · have bad := (emptyScheduleCert env nv q hq w).cert.accept x tr h
    exact False.elim (Bool.false_ne_true bad)

#verify_constructive Qsag.ClosedWhir.tooth_empty_schedule_rejects
#tooth_pair Qsag.ClosedWhir.whir_exec_closed_qrom_soundness vs
  Qsag.ClosedWhir.tooth_empty_schedule_rejects
end Qsag.ClosedWhir
end
