module
/-
# Qsag.Spec.IdealMigrate — Ideal Post-Quantum Ownership Migration Specification

Layer-0 ideal specification for migrating legacy elliptic-curve accounts (`secp256k1`, `Pallas`,
`BLS12-381`) to post-quantum custody keys via zero-knowledge ownership proofs:
1. Nullifier uniqueness (`spentNullifiers` prevents replay / double-migration of any legacy key),
2. Ownership soundness (`ValidLegacyOwnership`: a claim executes only when backed by a valid
   secret witness for the legacy public key or rerandomized verification key), and
3. Monotone conservation of migrated value (`totalMigrated ≤ poolCap`).
-/

public import Qsag.Spec.Primitives
public import Qsag.Spec.Refines
public import Qsag.Spec.GameBound
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Spec

set_option autoImplicit false

/-- Public migration claim binding a deterministic nullifier, target post-quantum public key,
    and migrated value. -/
structure MigrationClaim where
  nullifier : Digest256
  pqDestinationPk : Bytes
  amount : Nat
  deriving DecidableEq, Repr

/-- Persistent state of the ideal post-quantum migration registry. -/
structure IdealMigrateState where
  poolCap : Nat
  totalMigrated : Nat
  spentNullifiers : List Digest256
  settledClaims : List MigrationClaim

@[expose] def IdealMigrateState.init (poolCap : Nat) : IdealMigrateState :=
  { poolCap := poolCap
    totalMigrated := 0
    spentNullifiers := []
    settledClaims := [] }

/-- Reactive `Machine` for `IdealMigrate`: accepts `(claim, witnessValid)` iff `witnessValid = true`,
    `claim.nullifier ∉ spentNullifiers`, and `totalMigrated + claim.amount ≤ poolCap`. -/
@[expose] def idealMigrateMachine (poolCap₀ : Nat) :
    Machine IdealMigrateState (MigrationClaim × Bool) MigrationClaim where
  Init st := st = IdealMigrateState.init poolCap₀
  step st inp :=
    let (claim, witnessValid) := inp
    if !witnessValid ||
       decide (claim.nullifier ∈ st.spentNullifiers) ||
       !decide (st.totalMigrated + claim.amount ≤ st.poolCap) then
      none
    else
      some ({ st with
              totalMigrated := st.totalMigrated + claim.amount
              spentNullifiers := claim.nullifier :: st.spentNullifiers
              settledClaims := claim :: st.settledClaims },
            claim)
  errStep st _ := st

/-- Core invariant of `IdealMigrateState`: no duplicate nullifiers (`spentNullifiers.Nodup`),
    `spentNullifiers` equals `(settledClaims.map MigrationClaim.nullifier)`, and `totalMigrated ≤ poolCap`. -/
def IdealMigrateState.Inv (poolCap₀ : Nat) (st : IdealMigrateState) : Prop :=
  st.poolCap = poolCap₀ ∧
  st.totalMigrated ≤ poolCap₀ ∧
  st.spentNullifiers = st.settledClaims.map MigrationClaim.nullifier ∧
  st.spentNullifiers.Nodup

theorem IdealMigrateState.init_inv (poolCap₀ : Nat) :
    (IdealMigrateState.init poolCap₀).Inv poolCap₀ :=
  ⟨rfl, Nat.zero_le _, rfl, .nil⟩

theorem idealMigrateMachine_step_preserves_inv {poolCap₀ : Nat}
    {st st' : IdealMigrateState} {claim out : MigrationClaim} {wv : Bool}
    (hInv : st.Inv poolCap₀)
    (hStep : (idealMigrateMachine poolCap₀).step st (claim, wv) = some (st', out)) :
    st'.Inv poolCap₀ ∧ wv = true ∧ out = claim := by
  rcases hInv with ⟨hCapEq, _, hMapEq, hNd⟩
  unfold idealMigrateMachine at hStep
  dsimp only at hStep
  cases hGate : (!wv || decide (claim.nullifier ∈ st.spentNullifiers) ||
      !decide (st.totalMigrated + claim.amount ≤ st.poolCap))
  · simp only [hGate, Bool.false_eq_true, ↓reduceIte] at hStep
    injection hStep with hPair
    injection hPair with hSt hOut
    subst hSt
    rcases Bool.or_eq_false_iff.mp hGate with ⟨hL, hCapDec⟩
    rcases Bool.or_eq_false_iff.mp hL with ⟨hWv, hNullDec⟩
    have hWvTrue : wv = true := by
      cases wv
      · cases hWv
      · rfl
    have hNotMem : claim.nullifier ∉ st.spentNullifiers := of_decide_eq_false hNullDec
    have hCapOk : st.totalMigrated + claim.amount ≤ st.poolCap := by
      cases hDec : decide (st.totalMigrated + claim.amount ≤ st.poolCap)
      · rw [hDec] at hCapDec; cases hCapDec
      · exact of_decide_eq_true hDec
    refine ⟨⟨hCapEq, hCapEq ▸ hCapOk, congrArg (claim.nullifier :: ·) hMapEq,
      .cons (fun x hx hEq => hNotMem (hEq ▸ hx)) hNd⟩, hWvTrue, hOut.symm⟩
  · simp only [hGate, ↓reduceIte] at hStep

theorem idealMigrateMachine_trace_preserves_inv {poolCap₀ : Nat} :
    ∀ {s₀ s_final : IdealMigrateState} {tr : List ((MigrationClaim × Bool) × MigrationClaim)},
      s₀.Inv poolCap₀ →
      (idealMigrateMachine poolCap₀).ValidTrace s₀ tr s_final →
      s_final.Inv poolCap₀
  | _, _, _, hInv, .nil _ => hInv
  | _, _, _, hInv, .accept hStep hRest =>
    idealMigrateMachine_trace_preserves_inv
      (idealMigrateMachine_step_preserves_inv hInv hStep).1 hRest
  | _, _, _, hInv, .reject _ _ hRest =>
    idealMigrateMachine_trace_preserves_inv hInv hRest

/-- Every reachable state of `idealMigrateMachine` enforces strict nullifier uniqueness and pool-cap conservation! -/
theorem idealMigrateMachine_reachable_inv (poolCap₀ : Nat) {st : IdealMigrateState}
    (hReach : (idealMigrateMachine poolCap₀).Reachable st) :
    st.Inv poolCap₀ := by
  rcases hReach with ⟨s₀, tr, hInit, hTrace⟩
  rw [hInit] at hTrace
  exact idealMigrateMachine_trace_preserves_inv (IdealMigrateState.init_inv poolCap₀) hTrace

#verify_constructive
  Qsag.Spec.IdealMigrateState.init_inv
  Qsag.Spec.idealMigrateMachine_step_preserves_inv
  Qsag.Spec.idealMigrateMachine_trace_preserves_inv
  Qsag.Spec.idealMigrateMachine_reachable_inv

end Qsag.Spec
end
