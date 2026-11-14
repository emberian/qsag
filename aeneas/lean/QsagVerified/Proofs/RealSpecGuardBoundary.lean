module
import all QsagVerified.Funs
public import QsagVerified.Proofs.PolicyAndAddr
public import Qsag.MirSpecBridge
import all Qsag.MirSpecBridgeCore

public section
namespace qsag_verified.proofs
open Aeneas Aeneas.Std Result
open qsag_verified

/-- These states agree on the window, cap, spend, pins and the last accepted nonce.
Nevertheless the extracted monotone-nonce guard and the canonical used-nonce-list
model disagree on a previously unused lower nonce. A field-for-field whole-machine
simulation must not be claimed for this mapping. -/
theorem tooth_velocity_used_nonce_model_is_not_monotone_nonce :
    let pin := Array.repeat 32#usize 0#u8
    let st : policy_and_addr.StatefulVelocityGuard :=
      ⟨0#u64, 1#u128, 10#u128, pin, pin, 2#u64⟩
    let req : policy_and_addr.VelocitySpendRequest :=
      ⟨0#u64, 1#u64, 1#u128, pin, pin⟩
    let spec : Qsag.MirPolicyGuardState :=
      { windowId := 0, velocityWindowCap := 10, accumulatedSpend := 1,
        burnedNonces := [2], pinnedPolicyDigest := List.replicate 32 0,
        pinnedAuthorityDigest := List.replicate 32 0, allowedRecipients := [[]], perTxCap := 10 }
    let inp : Qsag.MirTxIntent :=
      { recipient := [], amountUnits := 1, windowId := 0,
        policyDigest := List.replicate 32 0, authorityDigest := List.replicate 32 0, nonce := 1 }
    policy_and_addr.StatefulVelocityGuard.authorize_spend st req =
      .ok (st, .Err .NonMonotonicNonce) ∧
    (Qsag.mirPolicyStep spec inp).isSome = true := by
  dsimp only
  constructor
  · simp [policy_and_addr.StatefulVelocityGuard.authorize_spend, ct_eq_bytes32_spec,
      bind_eq_result_bind, result_bind_ok]
    intro h
    exact False.elim ((by decide : ¬ ((2#u64).val < (1#u64).val)) h)
  · rw [Qsag.mirPolicyStep.eq_def]
    simp [Qsag.u64MemBool.eq_def]
end qsag_verified.proofs
