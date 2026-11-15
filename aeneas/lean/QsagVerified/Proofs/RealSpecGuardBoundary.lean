module
import all QsagVerified.Funs
public import QsagVerified.Proofs.PolicyAndAddr
import all QsagVerified.Proofs.PolicyAndAddr
public import QsagVerified.Proofs.CredAndHdGuards
import all QsagVerified.Proofs.CredAndHdGuards
public import QsagVerified.Proofs.RealSpecFieldWeld
public import Qsag.MirSpecBridge
import all Qsag.MirSpecBridgeCore

/-!
# Guard welds for the velocity guard and the ML-DSA release gate

`Qsag.MirSpecBridgeCore` §6A and §6B state the velocity guard (`MirStatefulVelocityGuard`) and the
threshold ML-DSA release gate (`MirMlDsaReleaseGate`) over `UInt64`, `BitVec 128` and byte lists.
This module proves that the Aeneas extraction of `policy_and_addr.rs` and `cred_and_hd_guards.rs`
computes exactly those machines:

* `velocity_extracted_step_refines` / `extractedVelocity_forwardSim_mirVelocity`:
  `StatefulVelocityGuard::authorize_spend` never panics, and accepts, rejects and updates its
  state exactly as `Qsag.mirVelocityMachine` does on the abstracted state and request. The
  `u128` overflow test `amount > MAX - spent` and the spec's `spent + amount < 2^128` agree.
* `mlDsa_extracted_step_refines` / `extractedMlDsa_forwardSim_mirMlDsa`: the same for
  `MlDsaReleaseGate::try_release_z_share` against `Qsag.mirMlDsaReleaseMachine`.
* `extractedVelocity_multiTurn_cap_and_monotonic_nonce` and
  `extractedMlDsa_at_most_one_release` carry the multi-turn `Qsag` theorems onto every trace of
  the extracted code.

The velocity guard does **not** refine the burned-nonce policy model `Qsag.MirPolicyGuardState`
as a whole machine: `tooth_velocity_used_nonce_model_is_not_monotone_nonce` exhibits a lower,
never-used nonce that the extraction rejects and the policy model accepts. `Qsag` relates the two
only on accepted steps (`mirVelocityAdapted_step_refines_mirPolicyGuard`).
-/

public section
namespace qsag_verified.proofs
open Aeneas Aeneas.Std Result
open qsag_verified

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

attribute [local simp] UScalar.val

/-! ## Scalar and byte abstractions -/

private theorem arrayU8ToBytes_inj {n : Std.Usize} (a b : Std.Array Std.U8 n) :
    arrayU8ToBytes a = arrayU8ToBytes b ↔ a = b :=
  ⟨arrayU8ToBytes_injective, congrArg arrayU8ToBytes⟩

private theorem arrayU8ToBytes_length32 (a : Std.Array Std.U8 32#usize) :
    (arrayU8ToBytes a).length = 32 := by
  rw [arrayU8ToBytes_length]; rfl

private theorem arrayU8ToBytes_zero32 :
    arrayU8ToBytes (Array.repeat 32#usize 0#u8) = List.replicate 32 0 := rfl

private theorem u64Abs_inj (a b : Std.U64) :
    UInt64.ofBitVec a.bv = UInt64.ofBitVec b.bv ↔ a = b :=
  ⟨fun h => UScalar.ext (congrArg UInt64.toBitVec h), fun h => by rw [h]⟩

private theorem u32Abs_inj (a b : Std.U32) :
    UInt32.ofBitVec a.bv = UInt32.ofBitVec b.bv ↔ a = b :=
  ⟨fun h => UScalar.ext (congrArg UInt32.toBitVec h), fun h => by rw [h]⟩

/-! ## §6A. `StatefulVelocityGuard::authorize_spend` against `Qsag.mirVelocityMachine` -/

/-- State abstraction, field for field. -/
def velocityGuardAbs (g : policy_and_addr.StatefulVelocityGuard) : Qsag.MirStatefulVelocityGuard :=
  { window_id := UInt64.ofBitVec g.window_id.bv
    spent_units := g.spent_units.bv
    cap_units := g.cap_units.bv
    policy_pin := arrayU8ToBytes g.policy_pin
    authority_pin := arrayU8ToBytes g.authority_pin
    last_nonce := UInt64.ofBitVec g.last_nonce.bv }

/-- Request abstraction, field for field. -/
def velocityReqAbs (r : policy_and_addr.VelocitySpendRequest) : Qsag.MirVelocitySpendRequest :=
  { window_id := UInt64.ofBitVec r.window_id.bv
    nonce := UInt64.ofBitVec r.nonce.bv
    amount_units := r.amount_units.bv
    policy_pin := arrayU8ToBytes r.policy_pin
    authority_pin := arrayU8ToBytes r.authority_pin }

/-- `authorize_spend` returns normally on every input, with the result `velocitySpendStep`
    (`PolicyAndAddr.lean`) describes. -/
private theorem velocity_authorize_spend_exact (g : policy_and_addr.StatefulVelocityGuard)
    (r : policy_and_addr.VelocitySpendRequest) :
    match velocitySpendStep g r with
    | some (g', o) => policy_and_addr.StatefulVelocityGuard.authorize_spend g r = .ok (g', .Ok o)
    | none => ∃ e, policy_and_addr.StatefulVelocityGuard.authorize_spend g r = .ok (g, .Err e) := by
  unfold policy_and_addr.StatefulVelocityGuard.authorize_spend velocitySpendStep
  rw [ct_eq_bytes32_spec, ct_eq_bytes32_spec]
  by_cases hp : g.policy_pin = r.policy_pin
  swap
  · simp [hp, bind_eq_result_bind, result_bind_ok]
  by_cases ha : g.authority_pin = r.authority_pin
  swap
  · simp [hp, ha, bind_eq_result_bind, result_bind_ok]
  by_cases hw : r.window_id = g.window_id
  swap
  · have hne : (r.window_id != g.window_id) = true := bne_iff_ne.mpr hw
    simp [hp, ha, hw, hne, bind_eq_result_bind, result_bind_ok]
  by_cases hle_n : r.nonce <= g.last_nonce
  · have hnlt : ¬ g.last_nonce.val < r.nonce.val :=
      Nat.not_lt_of_ge ((UScalar.le_iff_val _ _).mp hle_n)
    simp only [UScalar.val] at hnlt
    simp [hp, ha, hw, hle_n, hnlt, bind_eq_result_bind, result_bind_ok]
  have hlt_n : g.last_nonce.val < r.nonce.val :=
    Nat.lt_of_not_ge fun h => hle_n ((UScalar.le_iff_val _ _).mpr h)
  obtain ⟨rem, hrem, hrem_val⟩ := max_velocity_sub_spec g.spent_units
  have hmax := u128_val_le_max g.spent_units
  have hcapmax := u128_val_le_max g.cap_units
  simp only [decide_eq_true hp, decide_eq_true ha, decide_eq_true hw, decide_eq_true hlt_n,
    hw, bne_self_eq_false, Bool.false_eq_true, hle_n, ↓reduceIte, Bool.true_and,
    bind_eq_result_bind, result_bind_ok]
  rw [hrem, result_bind_ok]
  by_cases hov : r.amount_units > rem
  · have hgt : rem.val < r.amount_units.val := (UScalar.lt_iff_val _ _).mp hov
    have hnc : ¬ (g.spent_units.val + r.amount_units.val ≤ g.cap_units.val) := by omega
    simp only [UScalar.val] at hnc
    simp [hov, hnc]
  have hamt_le : r.amount_units.val ≤ rem.val :=
    Nat.le_of_not_gt fun h => hov ((UScalar.lt_iff_val _ _).mpr h)
  have hsum_lt : g.spent_units.val + r.amount_units.val < 2 ^ 128 := by
    have : (2 : Nat) ^ 128 = 340282366920938463463374607431768211455 + 1 := rfl
    omega
  let new_spent : Std.U128 := ⟨g.spent_units.bv + r.amount_units.bv⟩
  have hadd : (g.spent_units + r.amount_units : Result Std.U128) = .ok new_spent := by
    simp only [hAdd_uscalar_eq, hsum_lt, ↓reduceIte]; rfl
  have hnew_val : new_spent.val = g.spent_units.val + r.amount_units.val := by
    change (g.spent_units.bv + r.amount_units.bv).toNat = _
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt hsum_lt]
  simp only [hov, ↓reduceIte]
  rw [hadd, result_bind_ok]
  by_cases hcap : new_spent > g.cap_units
  · have hnc : ¬ (g.spent_units.val + r.amount_units.val ≤ g.cap_units.val) := by
      rw [← hnew_val]; exact Nat.not_le_of_gt ((UScalar.lt_iff_val _ _).mp hcap)
    simp only [UScalar.val] at hnc
    simp [hcap, hnc]
  · have hc : g.spent_units.val + r.amount_units.val ≤ g.cap_units.val := by
      rw [← hnew_val]; exact Nat.le_of_not_gt fun h => hcap ((UScalar.lt_iff_val _ _).mpr h)
    simp only [UScalar.val] at hc
    simp [hcap, hc]
    rfl

/-- `velocitySpendStep` and `Qsag.mirVelocityAuthorizeSpend` agree through the abstraction. -/
private theorem velocitySpendStep_abs (g : policy_and_addr.StatefulVelocityGuard)
    (r : policy_and_addr.VelocitySpendRequest) :
    Qsag.mirVelocityAuthorizeSpend (velocityGuardAbs g) (velocityReqAbs r) =
      match velocitySpendStep g r with
      | some (g', o) => .ok (velocityGuardAbs g') o.bv
      | none => .err (velocityGuardAbs g) () := by
  have hcapmax := u128_val_le_max g.cap_units
  simp only [UScalar.val] at hcapmax
  unfold Qsag.mirVelocityAuthorizeSpend velocitySpendStep
  by_cases hp : g.policy_pin = r.policy_pin
  swap
  · have : arrayU8ToBytes r.policy_pin ≠ arrayU8ToBytes g.policy_pin :=
      fun h => hp (arrayU8ToBytes_injective h).symm
    simp [velocityGuardAbs, velocityReqAbs, hp, this]
  by_cases ha : g.authority_pin = r.authority_pin
  swap
  · have : arrayU8ToBytes r.authority_pin ≠ arrayU8ToBytes g.authority_pin :=
      fun h => ha (arrayU8ToBytes_injective h).symm
    simp [velocityGuardAbs, velocityReqAbs, hp, ha, this]
  by_cases hw : r.window_id = g.window_id
  swap
  · have : UInt64.ofBitVec r.window_id.bv ≠ UInt64.ofBitVec g.window_id.bv :=
      fun h => hw ((u64Abs_inj _ _).mp h)
    simp [velocityGuardAbs, velocityReqAbs, arrayU8ToBytes_length32, hp, ha, hw, this]
  by_cases hn : g.last_nonce.bv.toNat < r.nonce.bv.toNat
  swap
  · simp [velocityGuardAbs, velocityReqAbs, arrayU8ToBytes_length32, hp, ha, hw, hn]
  by_cases hc : g.spent_units.bv.toNat + r.amount_units.bv.toNat ≤ g.cap_units.bv.toNat
  swap
  · simp [velocityGuardAbs, velocityReqAbs, arrayU8ToBytes_length32, hp, ha, hw, hn, hc]
  have hov : g.spent_units.bv.toNat + r.amount_units.bv.toNat < 2 ^ 128 := by
    have : (2 : Nat) ^ 128 = 340282366920938463463374607431768211455 + 1 := rfl
    omega
  simp [velocityGuardAbs, velocityReqAbs, arrayU8ToBytes_length32, hp, ha, hw, hn, hc, hov]
  exact (BitVec.add_def _ _).symm

/-- **Exact step characterisation.** For every state and request the extracted
    `authorize_spend` returns normally and its result is the step of `Qsag.mirVelocityMachine`
    on the abstracted state and request. -/
theorem velocity_extracted_step_refines :
    ExtractedStepRefines policy_and_addr.StatefulVelocityGuard.authorize_spend
      (fun o : Std.U128 => o.bv) Qsag.mirVelocityMachine velocityGuardAbs velocityReqAbs := by
  intro g r
  have hx := velocity_authorize_spend_exact g r
  have hab := velocitySpendStep_abs g r
  dsimp only [Qsag.mirVelocityMachine, Qsag.PartyMachine.ofOutcome]
  revert hx hab
  cases velocitySpendStep g r with
  | none =>
    intro hx hab
    obtain ⟨e, he⟩ := hx
    rw [he, hab]
    exact ⟨rfl, rfl⟩
  | some p =>
    rcases p with ⟨g', o⟩
    intro hx hab
    rw [hx, hab]

/-- The extracted velocity guard as a `Qsag.PartyMachine`. -/
def extractedVelocityMachine :
    Qsag.PartyMachine policy_and_addr.StatefulVelocityGuard policy_and_addr.VelocitySpendRequest
      (BitVec 128) :=
  extractedPartyMachine policy_and_addr.StatefulVelocityGuard.authorize_spend (fun o => o.bv)

/-- **Weld.** The extracted `authorize_spend` forward-simulates `Qsag.mirVelocityMachine` in
    lockstep through `velocityGuardAbs`. -/
def extractedVelocity_forwardSim_mirVelocity :
    Qsag.ForwardSim extractedVelocityMachine
      (comapInputs Qsag.mirVelocityMachine velocityReqAbs) :=
  velocity_extracted_step_refines.forwardSim

/-- Every multi-turn trace of the extracted velocity guard keeps the `Qsag` cap and nonce
    discipline (`Qsag.mirVelocity_multiTurn_cap_and_monotonic_nonce`): the final spend is the
    initial spend plus the approved amounts and stays within the cap, every approved request is
    pinned to the initial window and pins with a nonce above the initial one, and approved
    nonces strictly increase. -/
theorem extractedVelocity_multiTurn_cap_and_monotonic_nonce
    {g₀ gF : policy_and_addr.StatefulVelocityGuard}
    {tr : List (policy_and_addr.VelocitySpendRequest × BitVec 128)}
    (hCap₀ : g₀.spent_units.val ≤ g₀.cap_units.val)
    (hTr : extractedVelocityMachine.ValidTrace g₀ tr gF) :
    gF.spent_units.val = g₀.spent_units.val + (tr.map (fun p => p.2.toNat)).foldr (· + ·) 0 ∧
    gF.spent_units.val ≤ g₀.cap_units.val ∧
    (∀ p ∈ tr, g₀.last_nonce.val < p.1.nonce.val ∧
      p.1.window_id = g₀.window_id ∧
      p.1.policy_pin = g₀.policy_pin ∧
      p.1.authority_pin = g₀.authority_pin) ∧
    tr.Pairwise (fun a b => a.1.nonce.val < b.1.nonce.val) := by
  obtain ⟨aF, hA, hRel⟩ := extractedVelocity_forwardSim_mirVelocity.lift_validTrace
    (a₀ := velocityGuardAbs g₀) rfl hTr
  change aF = velocityGuardAbs gF at hRel
  subst hRel
  obtain ⟨hSum, hLe, _, hAll, hPair⟩ :=
    Qsag.mirVelocity_multiTurn_cap_and_monotonic_nonce (by exact hCap₀) (comapInputs_validTrace hA)
  simp only [List.map_map, Function.comp_def] at hSum
  refine ⟨hSum, hLe, fun p hp => ?_, ?_⟩
  · obtain ⟨hn, hw, hpp, hap⟩ := hAll _ (List.mem_map_of_mem (f := fun p => (velocityReqAbs p.1, p.2)) hp)
    exact ⟨hn, (u64Abs_inj _ _).mp hw, arrayU8ToBytes_injective hpp, arrayU8ToBytes_injective hap⟩
  · exact List.pairwise_map.mp hPair

/-! ## §6B. `MlDsaReleaseGate::try_release_z_share` against `Qsag.mirMlDsaReleaseMachine` -/

/-- State abstraction, field for field. -/
def mlDsaGateAbs (g : cred_and_hd_guards.MlDsaReleaseGate) : Qsag.MirMlDsaReleaseGate :=
  { session_id := arrayU8ToBytes g.session_id
    attempt := UInt32.ofBitVec g.attempt.bv
    z_share_masked := arrayU8ToBytes g.z_share_masked
    released := g.released
    aborted := g.aborted }

/-- Barrier-check abstraction, field for field. -/
def mlDsaChecksAbs (c : cred_and_hd_guards.MlDsaBarrierChecks) : Qsag.MirMlDsaBarrierChecks :=
  { req_session_id := arrayU8ToBytes c.req_session_id
    req_attempt := UInt32.ofBitVec c.req_attempt.bv
    z_norm_ok := c.z_norm_ok
    r0_norm_ok := c.r0_norm_ok
    w1_match := c.w1_match
    u_com_bound := c.u_com_bound }

/-- `mlDsaGateMealy` (`CredAndHdGuards.lean`) and `Qsag.mirMlDsaTryReleaseZShare` agree through
    the abstraction, including the wiped post-state of a rejection. -/
private theorem mlDsaGate_abs (g : cred_and_hd_guards.MlDsaReleaseGate)
    (c : cred_and_hd_guards.MlDsaBarrierChecks) :
    Qsag.mirMlDsaTryReleaseZShare (mlDsaGateAbs g) (mlDsaChecksAbs c) =
      if mlDsaBarrierPassBool g c then
        .ok (mlDsaGateAbs { g with z_share_masked := Array.repeat 32#usize 0#u8, released := true })
          (arrayU8ToBytes g.z_share_masked)
      else .err (mlDsaGateAbs (mlDsaGateMealy.errStep g c)) () := by
  unfold Qsag.mirMlDsaTryReleaseZShare mlDsaBarrierPassBool
  simp only [mlDsaGateMealy, mlDsaGateAbs, mlDsaChecksAbs, Qsag.abortMirMlDsaGate,
    arrayU8ToBytes_zero32]
  cases ha : g.aborted <;> cases hr : g.released <;> simp only [Bool.or_true, Bool.or_false,
    Bool.not_true, Bool.not_false, Bool.false_and, Bool.true_and, ↓reduceIte, Bool.false_eq_true]
  by_cases hs : g.session_id = c.req_session_id
  swap
  · have : arrayU8ToBytes c.req_session_id ≠ arrayU8ToBytes g.session_id :=
      fun h => hs (arrayU8ToBytes_injective h).symm
    simp [hs, this]
  by_cases hat : g.attempt = c.req_attempt
  swap
  · have : UInt32.ofBitVec g.attempt.bv ≠ UInt32.ofBitVec c.req_attempt.bv :=
      fun h => hat ((u32Abs_inj _ _).mp h)
    simp [arrayU8ToBytes_length32, hs, hat, this]
  cases c.z_norm_ok <;> cases c.r0_norm_ok <;> cases c.w1_match <;> cases c.u_com_bound <;>
    simp [arrayU8ToBytes_length32, hs, hat]

/-- **Exact step characterisation.** For every gate state and barrier-check record the extracted
    `try_release_z_share` returns normally and its result is the step of
    `Qsag.mirMlDsaReleaseMachine` on the abstracted state and checks. -/
theorem mlDsa_extracted_step_refines :
    ExtractedStepRefines cred_and_hd_guards.MlDsaReleaseGate.try_release_z_share
      (fun z : Array Std.U8 32#usize => arrayU8ToBytes z) Qsag.mirMlDsaReleaseMachine
      mlDsaGateAbs mlDsaChecksAbs := by
  intro g c
  obtain ⟨hPass, hFail⟩ := mldsa_gate_try_release_exact g c
  have hab := mlDsaGate_abs g c
  dsimp only [Qsag.mirMlDsaReleaseMachine, Qsag.PartyMachine.ofOutcome]
  cases hb : mlDsaBarrierPassBool g c
  · obtain ⟨e, he⟩ := hFail hb
    rw [hb] at hab
    simp only [Bool.false_eq_true, ↓reduceIte] at hab
    rw [he, hab]
    exact ⟨rfl, rfl⟩
  · rw [hb] at hab
    simp only [↓reduceIte] at hab
    rw [hPass hb, hab]

/-- The extracted ML-DSA release gate as a `Qsag.PartyMachine`. -/
def extractedMlDsaMachine :
    Qsag.PartyMachine cred_and_hd_guards.MlDsaReleaseGate cred_and_hd_guards.MlDsaBarrierChecks
      (List UInt8) :=
  extractedPartyMachine cred_and_hd_guards.MlDsaReleaseGate.try_release_z_share
    (fun z => arrayU8ToBytes z)

/-- **Weld.** The extracted `try_release_z_share` forward-simulates
    `Qsag.mirMlDsaReleaseMachine` in lockstep through `mlDsaGateAbs`. -/
def extractedMlDsa_forwardSim_mirMlDsa :
    Qsag.ForwardSim extractedMlDsaMachine
      (comapInputs Qsag.mirMlDsaReleaseMachine mlDsaChecksAbs) :=
  mlDsa_extracted_step_refines.forwardSim

/-- From any gate state, every trace of the extracted release gate releases at most one share,
    and only on checks naming the gate's own session and attempt with all four barrier flags set
    (`Qsag.mirMlDsa_every_step_wipes_share_and_at_most_one_release`). -/
theorem extractedMlDsa_at_most_one_release
    {g₀ gF : cred_and_hd_guards.MlDsaReleaseGate}
    {tr : List (cred_and_hd_guards.MlDsaBarrierChecks × List UInt8)}
    (hTr : extractedMlDsaMachine.ValidTrace g₀ tr gF) :
    tr.length ≤ 1 ∧
    ∀ p ∈ tr, p.1.req_session_id = g₀.session_id ∧ p.1.req_attempt = g₀.attempt ∧
      p.1.z_norm_ok = true ∧ p.1.r0_norm_ok = true ∧
      p.1.w1_match = true ∧ p.1.u_com_bound = true := by
  obtain ⟨aF, hA, _⟩ := extractedMlDsa_forwardSim_mirMlDsa.lift_validTrace
    (a₀ := mlDsaGateAbs g₀) rfl hTr
  obtain ⟨hLen, hAll, _⟩ :=
    Qsag.mirMlDsa_every_step_wipes_share_and_at_most_one_release (comapInputs_validTrace hA)
  refine ⟨by simpa using hLen, fun p hp => ?_⟩
  obtain ⟨hs, hat, hz, hr0, hw1, hu⟩ :=
    hAll _ (List.mem_map_of_mem (f := fun p => (mlDsaChecksAbs p.1, p.2)) hp)
  exact ⟨arrayU8ToBytes_injective hs, (u32Abs_inj _ _).mp hat, hz, hr0, hw1, hu⟩

/-! ## The burned-nonce policy model is not the extracted guard -/

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

/-- `#tooth` for the velocity weld: a replayed nonce is refused by the extracted guard and by the
    spec machine on the abstracted request. -/
theorem tooth_extractedVelocity_replayed_nonce_rejected
    (g : policy_and_addr.StatefulVelocityGuard) (r : policy_and_addr.VelocitySpendRequest)
    (hReplay : r.nonce.val ≤ g.last_nonce.val) :
    extractedVelocityMachine.step g r = none ∧
    Qsag.mirVelocityMachine.step (velocityGuardAbs g) (velocityReqAbs r) = none :=
  have hSpec : Qsag.mirVelocityMachine.step (velocityGuardAbs g) (velocityReqAbs r) = none :=
    Qsag.tooth_mirVelocity_nonMonotonic_nonce_rejected _ _ (.inl (by simpa [velocityGuardAbs,
      velocityReqAbs] using hReplay))
  ⟨by
    have h := velocity_extracted_step_refines g r
    dsimp only [extractedVelocityMachine, extractedPartyMachine]
    revert h
    generalize policy_and_addr.StatefulVelocityGuard.authorize_spend g r = res
    rcases res with ⟨g', o | e⟩ | _ | _
    · intro h; dsimp only at h; rw [hSpec] at h; cases h
    all_goals intro _; rfl, hSpec⟩

end qsag_verified.proofs
