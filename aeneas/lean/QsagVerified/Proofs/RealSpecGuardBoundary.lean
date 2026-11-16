module
import all QsagVerified.Funs
public import QsagVerified.Proofs.PolicyAndAddr
import all QsagVerified.Proofs.PolicyAndAddr
public import QsagVerified.Proofs.CredAndHdGuards
import all QsagVerified.Proofs.CredAndHdGuards
public import QsagVerified.Proofs.RealSpecFieldWeld
public import QsagVerified.Proofs.BeltLatchKernel
import all QsagVerified.Proofs.BeltLatchKernel
public import Qsag.Machine.MirSpecBridge
import all Qsag.Machine.MirSpecBridgeCore
import Qsag.Tactic.AssuranceKit

/-!
# Guard welds for the velocity guard, the ML-DSA release gate and the belt-latch kernel

`Qsag.MirSpecBridgeCore` §6A-§6C state the velocity guard (`MirStatefulVelocityGuard`), the
threshold ML-DSA release gate (`MirMlDsaReleaseGate`) and the belt-latch kernel
(`MirBeltLatchKernel`) over `UInt64`, `BitVec 128` and byte lists. This module proves that the
Aeneas extraction of `policy_and_addr.rs`, `cred_and_hd_guards.rs` and `belt_latch_kernel.rs`
computes exactly those machines. Each weld is an `ExtractedStepRefines` statement (the extracted
function never panics, and its accept/reject decision, output and post-state are the spec's on
the field-for-field abstraction), hence a lockstep `ForwardSim`:

* `velocity_extracted_step_refines`: `StatefulVelocityGuard::authorize_spend` against
  `Qsag.mirVelocityMachine`. The `u128` overflow test `amount > MAX - spent` and the spec's
  `spent + amount < 2^128` agree.
* `mlDsa_extracted_step_refines`: `MlDsaReleaseGate::try_release_z_share` against
  `Qsag.mirMlDsaReleaseMachine`, including the wiped, aborted post-state of every refusal.
* `beltLatch_extracted_step_refines`: `BeltLatchKernel::bind` against
  `Qsag.mirBeltLatchKernelMachine`, including the poisoned post-state of a failed persist.

`extractedVelocity_multiTurn_cap_and_monotonic_nonce`, `extractedMlDsa_at_most_one_release` and
`extractedBeltLatch_equivocation_free` are the multi-turn `Qsag` theorems restated on every trace
of the extracted code; each is paired with a trace-level `#tooth` and an inhabitedness witness.

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

private theorem arrayU8ToBytes_length32 (a : Std.Array Std.U8 32#usize) :
    (arrayU8ToBytes a).length = 32 := by
  rw [arrayU8ToBytes_length]; rfl

private theorem u64Abs_inj (a b : Std.U64) :
    UInt64.ofBitVec a.bv = UInt64.ofBitVec b.bv ↔ a = b :=
  ⟨fun h => UScalar.ext (congrArg UInt64.toBitVec h), fun h => by rw [h]⟩

private theorem u32Abs_inj (a b : Std.U32) :
    UInt32.ofBitVec a.bv = UInt32.ofBitVec b.bv ↔ a = b :=
  ⟨fun h => UScalar.ext (congrArg UInt32.toBitVec h), fun h => by rw [h]⟩

private theorem u8Abs_inj (a b : Std.U8) :
    UInt8.ofBitVec a.bv = UInt8.ofBitVec b.bv ↔ a = b :=
  ⟨fun h => UScalar.ext (congrArg UInt8.toBitVec h), fun h => by rw [h]⟩

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
  case neg =>
    simp [hp, bind_eq_result_bind, result_bind_ok]
  by_cases ha : g.authority_pin = r.authority_pin
  case neg =>
    simp [hp, ha, bind_eq_result_bind, result_bind_ok]
  by_cases hw : r.window_id = g.window_id
  case neg =>
    have hne : (r.window_id != g.window_id) = true := bne_iff_ne.mpr hw
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
  simp only [decide_eq_true hp, decide_eq_true ha, decide_eq_true hlt_n,
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
  case neg =>
    have : arrayU8ToBytes r.policy_pin ≠ arrayU8ToBytes g.policy_pin :=
      fun h => hp (arrayU8ToBytes_injective h).symm
    simp [velocityGuardAbs, velocityReqAbs, hp, this]
  by_cases ha : g.authority_pin = r.authority_pin
  case neg =>
    have : arrayU8ToBytes r.authority_pin ≠ arrayU8ToBytes g.authority_pin :=
      fun h => ha (arrayU8ToBytes_injective h).symm
    simp [velocityGuardAbs, velocityReqAbs, hp, ha, this]
  by_cases hw : r.window_id = g.window_id
  case neg =>
    have : UInt64.ofBitVec r.window_id.bv ≠ UInt64.ofBitVec g.window_id.bv :=
      fun h => hw ((u64Abs_inj _ _).mp h)
    simp [velocityGuardAbs, velocityReqAbs, arrayU8ToBytes_length32, hp, ha, hw, this]
  by_cases hn : g.last_nonce.bv.toNat < r.nonce.bv.toNat
  case neg =>
    simp [velocityGuardAbs, velocityReqAbs, arrayU8ToBytes_length32, hp, ha, hw, hn]
  by_cases hc : g.spent_units.bv.toNat + r.amount_units.bv.toNat ≤ g.cap_units.bv.toNat
  case neg =>
    simp [velocityGuardAbs, velocityReqAbs, arrayU8ToBytes_length32, hp, ha, hw, hn, hc]
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
  · exact (List.pairwise_map.mp hPair).imp fun h => by simpa [velocityReqAbs] using h

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
  rcases g with ⟨sid, att, z, rel, ab⟩
  rcases c with ⟨csid, catt, zn, r0, w1, uc⟩
  unfold Qsag.mirMlDsaTryReleaseZShare mlDsaBarrierPassBool
  simp only [mlDsaGateMealy, mlDsaGateAbs, mlDsaChecksAbs, Qsag.abortMirMlDsaGate]
  cases ab <;> cases rel <;> simp only [Bool.or_true, Bool.or_false,
    Bool.not_true, Bool.not_false, Bool.false_and, Bool.true_and, ↓reduceIte, Bool.false_eq_true]
  all_goals try rfl
  by_cases hs : sid = csid
  case neg =>
    have : arrayU8ToBytes csid ≠ arrayU8ToBytes sid :=
      fun h => hs (arrayU8ToBytes_injective h).symm
    simp [hs, this]
    rfl
  by_cases hat : att = catt
  case neg =>
    have : UInt32.ofBitVec att.bv ≠ UInt32.ofBitVec catt.bv :=
      fun h => hat ((u32Abs_inj _ _).mp h)
    simp [arrayU8ToBytes_length32, hs, hat, this]
    rfl
  subst hs hat
  cases zn <;> cases r0 <;> cases w1 <;> cases uc <;> simp [arrayU8ToBytes_length32] <;> rfl

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
    (`Qsag.mirMlDsa_at_most_one_release_through_barrier`). -/
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
    Qsag.mirMlDsa_at_most_one_release_through_barrier (comapInputs_validTrace hA)
  refine ⟨by simpa using hLen, fun p hp => ?_⟩
  obtain ⟨hs, hat, hz, hr0, hw1, hu⟩ :=
    hAll _ (List.mem_map_of_mem (f := fun p => (mlDsaChecksAbs p.1, p.2)) hp)
  exact ⟨arrayU8ToBytes_injective hs, (u32Abs_inj _ _).mp hat, hz, hr0, hw1, hu⟩

/-! ## §6C. `BeltLatchKernel::bind` against `Qsag.mirBeltLatchKernelMachine` -/

section BeltLatch
open belt_latch_kernel

/-- Digit-vector abstraction, field for field. -/
def beltDigitsAbs (d : BeltLatchDigits) : Qsag.MirBeltLatchDigits :=
  { len := UInt8.ofBitVec d.len.bv
    row0 := arrayU8ToBytes d.row0
    row1 := arrayU8ToBytes d.row1
    row2 := arrayU8ToBytes d.row2
    row3 := arrayU8ToBytes d.row3 }

/-- Record abstraction, field for field. -/
def beltRecordAbs (r : BeltLatchKernelRecord) : Qsag.MirBeltLatchKernelRecord :=
  { epoch := UInt64.ofBitVec r.epoch.bv
    msg_digest := arrayU8ToBytes r.msg_digest
    retry_salt := arrayU8ToBytes r.retry_salt
    digits := beltDigitsAbs r.digits }

/-- Kernel-state abstraction, field for field. -/
def beltKernelAbs (k : BeltLatchKernel) : Qsag.MirBeltLatchKernel :=
  { capacity_limit := UInt64.ofBitVec k.capacity_limit.bv
    next_epoch := UInt64.ofBitVec k.next_epoch.bv
    has_in_flight := k.has_in_flight
    in_flight := beltRecordAbs k.in_flight
    wal_poisoned := k.wal_poisoned }

/-- Request abstraction, field for field. -/
def beltReqAbs (r : BeltLatchBindRequest) : Qsag.MirBeltLatchBindRequest :=
  { epoch := UInt64.ofBitVec r.epoch.bv
    msg_digest := arrayU8ToBytes r.msg_digest
    retry_salt := arrayU8ToBytes r.retry_salt
    digits := beltDigitsAbs r.digits
    persist_ok := r.persist_ok }

/-- Outcome abstraction, constructor for constructor. -/
def beltOutcomeAbs : BeltLatchBindOutcome → Qsag.MirBeltLatchBindOutcome
  | .Fresh => .Fresh
  | .Replay => .Replay

private theorem beltDigitsAbs_inj (a b : BeltLatchDigits) :
    beltDigitsAbs a = beltDigitsAbs b ↔ a = b := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  rcases a with ⟨l, r0, r1, r2, r3⟩
  rcases b with ⟨l', r0', r1', r2', r3'⟩
  simp only [beltDigitsAbs, Qsag.MirBeltLatchDigits.mk.injEq] at h
  obtain ⟨hl, h0, h1, h2, h3⟩ := h
  rw [(u8Abs_inj _ _).mp hl, arrayU8ToBytes_injective h0, arrayU8ToBytes_injective h1,
    arrayU8ToBytes_injective h2, arrayU8ToBytes_injective h3]

private theorem u64_succ_abs (a : Std.U64) :
    UInt64.ofBitVec (a.bv + (1#u64).bv) = UInt64.ofNat (a.bv.toNat + 1) := by
  rw [BitVec.add_def]; rfl

/-- `beltLatchBindPure` (`BeltLatchKernel.lean`) and `Qsag.mirBeltLatchKernelBind` agree
    through the abstraction, including the poisoned post-state of a failed persist. -/
private theorem beltLatchBindPure_abs (s : BeltLatchKernel) (r : BeltLatchBindRequest) :
    Qsag.mirBeltLatchKernelBind (beltKernelAbs s) (beltReqAbs r) =
      match beltLatchBindPure s r with
      | (s', .Ok o) => .ok (beltKernelAbs s') (beltOutcomeAbs o)
      | (s', .Err _) => .err (beltKernelAbs s') () := by
  have hepoch : (beltRecordAbs s.in_flight).epoch = (beltReqAbs r).epoch ↔
      s.in_flight.epoch = r.epoch := u64Abs_inj _ _
  have hdig : (beltRecordAbs s.in_flight).digits = (beltReqAbs r).digits ↔
      s.in_flight.digits = r.digits := beltDigitsAbs_inj _ _
  have hmsg : (beltRecordAbs s.in_flight).msg_digest = (beltReqAbs r).msg_digest ↔
      s.in_flight.msg_digest = r.msg_digest :=
    ⟨arrayU8ToBytes_injective, fun h => congrArg arrayU8ToBytes h⟩
  have hsalt : (beltRecordAbs s.in_flight).retry_salt = (beltReqAbs r).retry_salt ↔
      s.in_flight.retry_salt = r.retry_salt :=
    ⟨arrayU8ToBytes_injective, fun h => congrArg arrayU8ToBytes h⟩
  unfold Qsag.mirBeltLatchKernelBind beltLatchBindPure
  cases hp : s.wal_poisoned
  case true => simp [beltKernelAbs, hp]
  have hp' : (beltKernelAbs s).wal_poisoned = false := hp
  simp only [hp', Bool.false_eq_true, ↓reduceIte]
  by_cases hin : s.has_in_flight = true ∧ s.in_flight.epoch = r.epoch
  · obtain ⟨hh, he⟩ := hin
    have hhit : ((beltKernelAbs s).has_in_flight &&
        decide ((beltKernelAbs s).in_flight.epoch = (beltReqAbs r).epoch)) = true := by
      simp only [beltKernelAbs, hh, Bool.true_and, decide_eq_true_eq]; exact hepoch.mpr he
    simp only [hhit, ↓reduceIte, hh, he, and_self]
    simp only [beltKernelAbs] at hmsg hsalt ⊢
    have hdM : decide ((beltRecordAbs s.in_flight).digits = (beltReqAbs r).digits) =
        beltLatchDigitsEqB s.in_flight.digits r.digits := by
      cases hB : beltLatchDigitsEqB s.in_flight.digits r.digits
      · exact decide_eq_false fun h => by
          rw [(beltLatchDigitsEqB_iff _ _).mpr (hdig.mp h)] at hB; cases hB
      · exact decide_eq_true (hdig.mpr ((beltLatchDigitsEqB_iff _ _).mp hB))
    by_cases hm : s.in_flight.msg_digest = r.msg_digest
    case neg => simp [hm, hmsg]
    by_cases hs : s.in_flight.retry_salt = r.retry_salt
    case neg => simp [hm, hs, hmsg, hsalt]
    cases hdB : beltLatchDigitsEqB s.in_flight.digits r.digits
    · simp [hm, hs, hmsg, hsalt]
      exact hdM.trans hdB
    · simp [hm, hs, hmsg, hsalt, beltOutcomeAbs]
      exact hdM.trans hdB
  · have hmiss : ((beltKernelAbs s).has_in_flight &&
        decide ((beltKernelAbs s).in_flight.epoch = (beltReqAbs r).epoch)) = false := by
      cases hh : s.has_in_flight
      · simp [beltKernelAbs, hh]
      · have he : ¬ s.in_flight.epoch = r.epoch := fun he => hin ⟨hh, he⟩
        simp only [beltKernelAbs, hh, Bool.true_and, decide_eq_false_iff_not]
        exact fun h => he (hepoch.mp h)
    simp only [hmiss, Bool.false_eq_true, ↓reduceIte, hin]
    unfold beltLatchFreshPure
    have hjump : Qsag.mirBeltMaxEpochJump = 64 := rfl
    simp only [beltKernelAbs, beltReqAbs, UInt64.toNat_ofBitVec, hjump]
    by_cases h1 : r.epoch.bv.toNat < s.next_epoch.bv.toNat
    · simp [h1]
    by_cases h2 : s.capacity_limit.bv.toNat ≤ r.epoch.bv.toNat
    · simp [h1, h2]
    by_cases h3 : 64 < r.epoch.bv.toNat - s.next_epoch.bv.toNat
    · simp [h1, h2, h3]
    cases r.persist_ok
    · simp [h1, h2, h3]
    · simp [h1, h2, h3, beltOutcomeAbs, beltRecordAbs, beltLatchRecordOf, hp]

/-- **Exact step characterisation.** For every kernel state and request the extracted
    `BeltLatchKernel::bind` returns normally and its result is the step of
    `Qsag.mirBeltLatchKernelMachine` on the abstracted state and request. -/
theorem beltLatch_extracted_step_refines :
    ExtractedStepRefines BeltLatchKernel.bind beltOutcomeAbs Qsag.mirBeltLatchKernelMachine
      beltKernelAbs beltReqAbs := by
  intro s r
  have hab := beltLatchBindPure_abs s r
  rw [belt_latch_bind_eq]
  dsimp only [Qsag.mirBeltLatchKernelMachine, Qsag.PartyMachine.ofOutcome]
  revert hab
  rcases beltLatchBindPure s r with ⟨s', o | e⟩
  · intro hab; dsimp only at hab ⊢; rw [hab]
  · intro hab; dsimp only at hab ⊢; rw [hab]; exact ⟨rfl, rfl⟩

/-- The extracted belt-latch kernel as a `Qsag.PartyMachine`. -/
def extractedBeltLatchMachine :
    Qsag.PartyMachine BeltLatchKernel BeltLatchBindRequest Qsag.MirBeltLatchBindOutcome :=
  extractedPartyMachine BeltLatchKernel.bind beltOutcomeAbs

/-- **Weld.** The extracted `BeltLatchKernel::bind` forward-simulates
    `Qsag.mirBeltLatchKernelMachine` in lockstep through `beltKernelAbs`. -/
def extractedBeltLatch_forwardSim_mirBeltLatchKernel :
    Qsag.ForwardSim extractedBeltLatchMachine
      (comapInputs Qsag.mirBeltLatchKernelMachine beltReqAbs) :=
  beltLatch_extracted_step_refines.forwardSim

/-- Every trace of the extracted kernel from a well-formed state stays well formed, binds only
    epochs below the capacity limit, and never accepts two different records for one epoch
    (`Qsag.mirBeltLatchKernel_equivocation_free`). -/
theorem extractedBeltLatch_equivocation_free
    {k₀ kF : BeltLatchKernel}
    {tr : List (BeltLatchBindRequest × Qsag.MirBeltLatchBindOutcome)}
    (hWf₀ : k₀.next_epoch.val ≤ k₀.capacity_limit.val ∧
      (k₀.has_in_flight = true → k₀.in_flight.epoch.val < k₀.next_epoch.val))
    (hTr : extractedBeltLatchMachine.ValidTrace k₀ tr kF) :
    (kF.next_epoch.val ≤ kF.capacity_limit.val ∧
      (kF.has_in_flight = true → kF.in_flight.epoch.val < kF.next_epoch.val)) ∧
    (∀ p ∈ tr, p.1.epoch.val < k₀.capacity_limit.val) ∧
    tr.Pairwise (fun a b => a.1.epoch = b.1.epoch →
      a.1.msg_digest = b.1.msg_digest ∧ a.1.retry_salt = b.1.retry_salt ∧
        a.1.digits = b.1.digits) := by
  obtain ⟨aF, hA, hRel⟩ := extractedBeltLatch_forwardSim_mirBeltLatchKernel.lift_validTrace
    (a₀ := beltKernelAbs k₀) rfl hTr
  change aF = beltKernelAbs kF at hRel
  subst hRel
  obtain ⟨hWfF, hCap, hPair⟩ :=
    Qsag.mirBeltLatchKernel_equivocation_free (by exact hWf₀)
      (comapInputs_validTrace hA)
  refine ⟨hWfF, fun p hp => hCap (beltReqAbs p.1, p.2)
      (List.mem_map_of_mem (f := fun p => (beltReqAbs p.1, p.2)) hp),
    (List.pairwise_map.mp hPair).imp fun h he => ?_⟩
  obtain ⟨hm, hs, hd⟩ := h (congrArg (fun e : Std.U64 => UInt64.ofBitVec e.bv) he)
  exact ⟨arrayU8ToBytes_injective hm, arrayU8ToBytes_injective hs, (beltDigitsAbs_inj _ _).mp hd⟩

/-- `#tooth` for the belt-latch weld: a poisoned kernel accepts nothing, on any trace. -/
theorem tooth_extractedBeltLatch_poisoned_accepts_nothing
    {k kF : BeltLatchKernel} {r : BeltLatchBindRequest} {o : Qsag.MirBeltLatchBindOutcome}
    {rest : List (BeltLatchBindRequest × Qsag.MirBeltLatchBindOutcome)}
    (hP : k.wal_poisoned = true) :
    ¬ extractedBeltLatchMachine.ValidTrace k ((r, o) :: rest) kF := by
  suffices ∀ {s sF tr}, extractedBeltLatchMachine.ValidTrace s tr sF → s.wal_poisoned = true →
      tr ≠ [] → False from fun h => this h hP (List.cons_ne_nil _ _)
  intro s sF tr hT
  induction hT with
  | nil => intro _ h; exact h rfl
  | @accept s' _ _ inp _ _ hStep _ _ =>
    intro hs _
    have h := belt_latch_poisoned_step s' inp hs
    simp only [extractedBeltLatchMachine, extractedPartyMachine, h] at hStep
    cases hStep
  | @reject s' _ inp _ _ _ ih =>
    intro hs hne
    have h := belt_latch_poisoned_step s' inp hs
    refine ih ?_ hne
    simp only [extractedBeltLatchMachine, extractedPartyMachine, h]
    exact hs

/-- A fresh bind followed by its replay, from a well-formed empty kernel. -/
theorem inhabited_extractedBeltLatch_fresh_and_replay :
    ∃ (k₀ kF : BeltLatchKernel) (tr : List (BeltLatchBindRequest × Qsag.MirBeltLatchBindOutcome)),
      (k₀.next_epoch.val ≤ k₀.capacity_limit.val ∧
        (k₀.has_in_flight = true → k₀.in_flight.epoch.val < k₀.next_epoch.val)) ∧
      extractedBeltLatchMachine.ValidTrace k₀ tr kF ∧
      tr.map Prod.snd = [.Fresh, .Replay] := by
  let z := Array.repeat 32#usize 0#u8
  let d : BeltLatchDigits := ⟨0#u8, z, z, z, z⟩
  let k₀ : BeltLatchKernel := ⟨8#u64, 0#u64, false, ⟨0#u64, z, z, d⟩, false⟩
  let r : BeltLatchBindRequest := ⟨0#u64, Array.repeat 32#usize 0xA5#u8, z, d, true⟩
  let k₁ : BeltLatchKernel :=
    { k₀ with next_epoch := ⟨r.epoch.bv + (1#u64).bv⟩, has_in_flight := true,
              in_flight := beltLatchRecordOf r }
  have hb1 := belt_latch_fresh_accepts k₀ r rfl (fun h => Bool.false_ne_true h.1)
    (by decide) (by decide) (by decide) rfl
  have hb2 := belt_latch_replay_accepts k₁ r rfl rfl rfl
  have h1 : extractedBeltLatchMachine.step k₀ r = some (k₁, .Fresh) := by
    dsimp only [extractedBeltLatchMachine, extractedPartyMachine]; rw [hb1]; rfl
  have h2 : extractedBeltLatchMachine.step k₁ r = some (k₁, .Replay) := by
    dsimp only [extractedBeltLatchMachine, extractedPartyMachine]; rw [hb2]; rfl
  exact ⟨k₀, k₁, [(r, .Fresh), (r, .Replay)], ⟨by decide, fun h => by cases h⟩,
    .accept h1 (.accept h2 (.nil k₁)), rfl⟩

end BeltLatch

#tooth_pair qsag_verified.proofs.extractedBeltLatch_equivocation_free vs
  qsag_verified.proofs.tooth_extractedBeltLatch_poisoned_accepts_nothing
#verify_inhabited qsag_verified.proofs.extractedBeltLatch_equivocation_free
  qsag_verified.proofs.inhabited_extractedBeltLatch_fresh_and_replay

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
  · rw [Qsag.mirPolicyStep.eq_def]
    simp [Qsag.u64MemBool.eq_def]

private theorem extractedVelocity_replay_step_none
    (g : policy_and_addr.StatefulVelocityGuard) (r : policy_and_addr.VelocitySpendRequest)
    (hReplay : r.nonce.val ≤ g.last_nonce.val) :
    extractedVelocityMachine.step g r = none :=
  velocity_extracted_step_refines.step_none
    (Qsag.tooth_mirVelocity_nonMonotonic_nonce_rejected _ _
      (.inl (by simpa [velocityGuardAbs, velocityReqAbs] using hReplay)))

/-- A rejected spend leaves the extracted guard unchanged. -/
private theorem extractedVelocity_errStep_eq {g : policy_and_addr.StatefulVelocityGuard}
    {r : policy_and_addr.VelocitySpendRequest} (h : extractedVelocityMachine.step g r = none) :
    extractedVelocityMachine.errStep g r = g := by
  have hx := velocity_authorize_spend_exact g r
  dsimp only [extractedVelocityMachine, extractedPartyMachine] at h ⊢
  revert hx
  cases velocitySpendStep g r with
  | none => rintro ⟨e, he⟩; rw [he]
  | some p => rcases p with ⟨g', o⟩; intro hx; rw [hx] at h; cases h

/-- `#tooth` for the velocity weld: no trace of the extracted guard from `g` records, as its first
    approved spend, a request whose nonce does not exceed `g.last_nonce`. -/
theorem tooth_extractedVelocity_replayed_nonce_never_approved
    {g gF : policy_and_addr.StatefulVelocityGuard} {r : policy_and_addr.VelocitySpendRequest}
    {out : BitVec 128} {rest : List (policy_and_addr.VelocitySpendRequest × BitVec 128)}
    (hReplay : r.nonce.val ≤ g.last_nonce.val) :
    ¬ extractedVelocityMachine.ValidTrace g ((r, out) :: rest) gF := by
  suffices ∀ {s sF tr}, extractedVelocityMachine.ValidTrace s tr sF → s = g →
      tr = (r, out) :: rest → False from fun h => this h rfl rfl
  intro s sF tr hT
  induction hT with
  | nil => intro _ h; cases h
  | accept hStep _ _ =>
    intro hs ht
    subst hs
    simp only [List.cons.injEq, Prod.mk.injEq] at ht
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := ht
    rw [extractedVelocity_replay_step_none _ _ hReplay] at hStep
    cases hStep
  | reject _ hNone _ ih =>
    intro hs ht
    subst hs
    exact ih (extractedVelocity_errStep_eq hNone) ht

/-- Two accepted spends of the extracted guard in one window. -/
theorem inhabited_extractedVelocity_two_turn_trace :
    ∃ (g₀ gF : policy_and_addr.StatefulVelocityGuard)
      (tr : List (policy_and_addr.VelocitySpendRequest × BitVec 128)),
      g₀.spent_units.val ≤ g₀.cap_units.val ∧
      extractedVelocityMachine.ValidTrace g₀ tr gF ∧
      tr.length = 2 := by
  let pin := Array.repeat 32#usize 0#u8
  let g₀ : policy_and_addr.StatefulVelocityGuard := ⟨7#u64, 0#u128, 100#u128, pin, pin, 0#u64⟩
  let r₁ : policy_and_addr.VelocitySpendRequest := ⟨7#u64, 1#u64, 40#u128, pin, pin⟩
  let r₂ : policy_and_addr.VelocitySpendRequest := ⟨7#u64, 2#u64, 55#u128, pin, pin⟩
  let g₁ : policy_and_addr.StatefulVelocityGuard :=
    { g₀ with spent_units := ⟨g₀.spent_units.bv + r₁.amount_units.bv⟩, last_nonce := r₁.nonce }
  let g₂ : policy_and_addr.StatefulVelocityGuard :=
    { g₁ with spent_units := ⟨g₁.spent_units.bv + r₂.amount_units.bv⟩, last_nonce := r₂.nonce }
  have step (g g' : policy_and_addr.StatefulVelocityGuard) (r : policy_and_addr.VelocitySpendRequest)
      (o : Std.U128) (hs : velocitySpendStep g r = some (g', o)) :
      extractedVelocityMachine.step g r = some (g', o.bv) := by
    have hx := velocity_authorize_spend_exact g r
    rw [hs] at hx
    dsimp only [extractedVelocityMachine, extractedPartyMachine]
    rw [hx]
  have h1 := step g₀ g₁ r₁ 40#u128 (by
    unfold velocitySpendStep; split
    · rfl
    · rename_i h; exact absurd (by decide) h)
  have h2 := step g₁ g₂ r₂ 55#u128 (by
    unfold velocitySpendStep; split
    · rfl
    · rename_i h; exact absurd (by decide) h)
  exact ⟨g₀, g₂, [(r₁, (40#u128).bv), (r₂, (55#u128).bv)], by decide,
    .accept h1 (.accept h2 (.nil g₂)), rfl⟩

#tooth_pair qsag_verified.proofs.extractedVelocity_multiTurn_cap_and_monotonic_nonce vs
  qsag_verified.proofs.tooth_extractedVelocity_replayed_nonce_never_approved
#verify_inhabited qsag_verified.proofs.extractedVelocity_multiTurn_cap_and_monotonic_nonce
  qsag_verified.proofs.inhabited_extractedVelocity_two_turn_trace

private theorem extractedMlDsa_failed_barrier_step_none
    (g : cred_and_hd_guards.MlDsaReleaseGate) (c : cred_and_hd_guards.MlDsaBarrierChecks)
    (hFail : (c.z_norm_ok && c.r0_norm_ok && c.w1_match && c.u_com_bound) = false) :
    extractedMlDsaMachine.step g c = none :=
  mlDsa_extracted_step_refines.step_none
    (Qsag.mirMlDsa_failed_barrier_aborts_and_zeros_share_full _ _ hFail).1

/-- `#tooth` for the ML-DSA weld: from any state, no trace of the extracted gate records a
    release whose barrier checks have a flag clear. -/
theorem tooth_extractedMlDsa_failed_barrier_never_released
    {g gF : cred_and_hd_guards.MlDsaReleaseGate} {c : cred_and_hd_guards.MlDsaBarrierChecks}
    {out : List UInt8} {rest : List (cred_and_hd_guards.MlDsaBarrierChecks × List UInt8)}
    (hFail : (c.z_norm_ok && c.r0_norm_ok && c.w1_match && c.u_com_bound) = false) :
    ¬ extractedMlDsaMachine.ValidTrace g ((c, out) :: rest) gF := by
  suffices ∀ {s sF tr}, extractedMlDsaMachine.ValidTrace s tr sF →
      tr = (c, out) :: rest → False from fun h => this h rfl
  intro s sF tr hT
  induction hT with
  | nil => intro h; cases h
  | @accept s' _ _ _ _ _ hStep _ _ =>
    intro ht
    simp only [List.cons.injEq, Prod.mk.injEq] at ht
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := ht
    rw [extractedMlDsa_failed_barrier_step_none _ _ hFail] at hStep
    cases hStep
  | reject _ _ _ ih => exact ih

/-- One honest release of the extracted gate. -/
theorem inhabited_extractedMlDsa_honest_release :
    ∃ (g₀ gF : cred_and_hd_guards.MlDsaReleaseGate)
      (tr : List (cred_and_hd_guards.MlDsaBarrierChecks × List UInt8)),
      extractedMlDsaMachine.ValidTrace g₀ tr gF ∧ tr.length = 1 := by
  let sid := Array.repeat 32#usize 0xA5#u8
  let z := Array.repeat 32#usize 0x5A#u8
  let g₀ : cred_and_hd_guards.MlDsaReleaseGate := ⟨sid, 3#u32, z, false, false⟩
  let c : cred_and_hd_guards.MlDsaBarrierChecks := ⟨sid, 3#u32, true, true, true, true⟩
  let g₁ : cred_and_hd_guards.MlDsaReleaseGate :=
    { g₀ with z_share_masked := Array.repeat 32#usize 0#u8, released := true }
  have h1 : extractedMlDsaMachine.step g₀ c = some (g₁, arrayU8ToBytes z) := by
    have hx := (mldsa_gate_try_release_exact g₀ c).1 (by decide)
    dsimp only [extractedMlDsaMachine, extractedPartyMachine]
    rw [hx]
  exact ⟨g₀, g₁, [(c, arrayU8ToBytes z)], .accept h1 (.nil g₁), rfl⟩

#tooth_pair qsag_verified.proofs.extractedMlDsa_at_most_one_release vs
  qsag_verified.proofs.tooth_extractedMlDsa_failed_barrier_never_released
#verify_inhabited qsag_verified.proofs.extractedMlDsa_at_most_one_release
  qsag_verified.proofs.inhabited_extractedMlDsa_honest_release

end qsag_verified.proofs
