module
/- Executed finite preprocessing attacks, including a chronology counterexample.
All arithmetic is kernel-reduced; these are classical experiments, not QAI security. -/
public import Qsag.QromPreprocessingGame
import all Qsag.QromPreprocessingGame
import all Qsag.MultiRoundFsQrom
import all Qsag.ConcreteSecurityBudget

public section
namespace Qsag.PreprocessingGame
set_option autoImplicit false

/-- With advice fixed independently of H, each chosen pair collides on 4 of 8 oracles. -/
theorem fixedAdvice_collision_count (a : BitVec 2) :
    fixedAdviceWinCount storedCollision.online (fun H _ pair => collisionWin H pair) a = 4 := by
  cases a with | ofFin a =>
  revert a
  decide +kernel

/-- A witness that the oracle-dependent preprocessing really changes the experiment:
8 successes with two bits of advice versus 4 for every fixed advice, and zero online calls. -/
theorem storedCollision_execution :
    adviceWinCount storedCollision (fun H _ pair => collisionWin H pair) = 8 ∧
    fixedAdviceWinCount storedCollision.online (fun H _ pair => collisionWin H pair) 0 = 4 ∧
    ∀ H : Fin 3 → BitVec 1, (storedCollision.run H 0).2 = 0 := by
  refine ⟨storedCollision_count, fixedAdvice_collision_count 0, ?_⟩
  intro H
  rfl

/-- Two disjoint three-address slices of the same six-address oracle. -/
def saltSlice (H : Fin 6 → BitVec 1) (s : Fin 2) : Fin 3 → BitVec 1 :=
  fun x => H ⟨s.val * 3 + x.val, by have := s.isLt; have := x.isLt; omega⟩

/-- A single stored entry for salt zero, created without knowing the challenge salt. -/
def oneSaltTable (H : Fin 6 → BitVec 1) : List (Fin 2 × (Fin 3 × Fin 3)) :=
  [(0, storedCollisionPair (storedCollisionAdvice (saltSlice H 0)))]

/-- The same one-entry capacity used after learning the challenge: intentionally NOT
an instance of the chronology in ClassicalAdvice, because preprocessing receives s. -/
def challengeAwareTable (H : Fin 6 → BitVec 1) (s : Fin 2) :
    List (Fin 2 × (Fin 3 × Fin 3)) :=
  [(s, storedCollisionPair (storedCollisionAdvice (saltSlice H s)))]

/-- Fresh uniform salt: exactly 64 successful oracle/salt pairs out of 64*2.
The entry-count bound is attained. Challenge-dependent preprocessing: 128/128 despite
still storing just one entry. Thus moving salt disclosure before preprocessing invalidates
applying the fixed-table entries/K bound to the whole two-stage experiment. -/
theorem freshSalt_chronology_execution :
    uniformOracleSum 1 6 (fun H => qsum 2
      (tableWin (fun s pair => collisionWin (saltSlice H s) pair) (oneSaltTable H))) = 64 ∧
    uniformOracleSum 1 6 (fun H => qsum 2 (fun s =>
      tableWin (fun t pair => collisionWin (saltSlice H t) pair) (challengeAwareTable H s) s)) = 128 ∧
    (2 ^ 1) ^ 6 * 2 = 128 := by
  decide +kernel

/-- Reuses the general proved theorem, not only an executed enumeration. -/
theorem oneSaltTable_bound :
    uniformOracleSum 1 6 (fun H => qsum 2
      (tableWin (fun s pair => collisionWin (saltSlice H s) pair) (oneSaltTable H))) ≤ 64 := by
  exact freshSalt_preprocessed_table_bound oneSaltTable
    (fun H s pair => collisionWin (saltSlice H s) pair) 1 (fun _ => Nat.le_refl 1)

/-- Actual adaptive online queries are charged, even when an address is repeated. -/
def twiceQuery (x : Fin 3) : Program (Fin 3) (BitVec 1) (BitVec 1) 2 :=
  .query x fun _ => .query x fun y => .done y

theorem twiceQuery_execution (H : Fin 3 → BitVec 1) (x : Fin 3) :
    (twiceQuery x).run H = (H x, 2) := by
  unfold twiceQuery Program.run
  rfl

#verify_constructive
  Qsag.PreprocessingGame.fixedAdvice_collision_count
  Qsag.PreprocessingGame.storedCollision_execution
  Qsag.PreprocessingGame.freshSalt_chronology_execution
  Qsag.PreprocessingGame.oneSaltTable_bound
  Qsag.PreprocessingGame.twiceQuery_execution
end Qsag.PreprocessingGame
end
