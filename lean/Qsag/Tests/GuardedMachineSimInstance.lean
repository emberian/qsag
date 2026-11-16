module
public import Qsag.Machine.MirSpecBridgeCore
import Qsag.Tactic.AssuranceKit
/-! Exercise the actual guard-kit instance in the canonical machine owner. There are no
copied velocity structures or step functions in this test module. -/
public section
namespace Qsag.Tests.GuardedMachineSimInstance
open Qsag
set_option autoImplicit false
def VelocityTraceSafe (g₀ : MirStatefulVelocityGuard)
    (tr : List (MirVelocitySpendRequest × BitVec 128)) (gF : MirStatefulVelocityGuard) : Prop :=
  let totalApproved := (tr.map (fun p => p.2.toNat)).foldr (· + ·) 0
  gF.spent_units.toNat = g₀.spent_units.toNat + totalApproved ∧
  gF.spent_units.toNat ≤ g₀.cap_units.toNat ∧
  totalApproved ≤ g₀.cap_units.toNat - g₀.spent_units.toNat ∧
  (∀ p ∈ tr, g₀.last_nonce.toNat < p.1.nonce.toNat ∧ p.1.window_id = g₀.window_id ∧
    p.1.policy_pin = g₀.policy_pin ∧ p.1.authority_pin = g₀.authority_pin) ∧
  tr.Pairwise (fun a b => a.1.nonce.toNat < b.1.nonce.toNat)

theorem mirVelocity_multiTurn_cap_and_monotonic_nonce
    {g₀ gF : MirStatefulVelocityGuard} {tr : List (MirVelocitySpendRequest × BitVec 128)}
    (hCap₀ : g₀.spent_units.toNat ≤ g₀.cap_units.toNat)
    (hTr : mirVelocityMachine.ValidTrace g₀ tr gF) : VelocityTraceSafe g₀ tr gF :=
  Qsag.mirVelocity_multiTurn_cap_and_monotonic_nonce hCap₀ hTr

theorem tooth_mirVelocity_nonMonotonic_nonce_rejected (g : MirStatefulVelocityGuard)
    (req : MirVelocitySpendRequest) (hBad : req.nonce.toNat ≤ g.last_nonce.toNat) :
    mirVelocityMachine.step g req = none :=
  Qsag.tooth_mirVelocity_nonMonotonic_nonce_rejected g req (.inl hBad)

theorem inhabited_mirVelocity_trace : ∃ (g₀ gF : MirStatefulVelocityGuard)
    (tr : List (MirVelocitySpendRequest × BitVec 128)),
    g₀.spent_units.toNat ≤ g₀.cap_units.toNat ∧ mirVelocityMachine.ValidTrace g₀ tr gF := by
  obtain ⟨g₀, gF, tr, hCap, hTrace, _⟩ := Qsag.inhabited_mirVelocity_two_turn_trace
  exact ⟨g₀, gF, tr, hCap, hTrace⟩

#verify_constructive mirVelocity_multiTurn_cap_and_monotonic_nonce
#verify_inhabited mirVelocity_multiTurn_cap_and_monotonic_nonce inhabited_mirVelocity_trace
#tooth_pair mirVelocity_multiTurn_cap_and_monotonic_nonce vs tooth_mirVelocity_nonMonotonic_nonce_rejected
end Qsag.Tests.GuardedMachineSimInstance
end
