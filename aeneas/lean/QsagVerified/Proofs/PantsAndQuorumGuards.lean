module

public import QsagVerified.Proofs.Common
public import QsagVerified.Proofs.MirRefinementKit
public import QsagVerified.Proofs.Wots
public import QsagVerified.Proofs.FtsSpnGuard
public import QsagVerified.Proofs.Sponge

public section

namespace qsag_verified.proofs

open Aeneas Aeneas.Std Result ControlFlow Error
open qsag_verified

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

attribute [-simp] BitVec.getLsbD_eq_getElem
attribute [local simp] UScalar.val UScalarTy.numBits

private theorem map_id_pair_pants {α β : Type} :
    ∀ (xs : List (α × β)), xs.map (fun p => (id p.1, id p.2)) = xs
  | [] => rfl
  | (_, _) :: rest => congrArg (_ :: ·) (map_id_pair_pants rest)

private theorem u32_cast_u64_val (x : Std.U32) :
    (UScalar.cast .U64 x).val = x.val := by
  have hx : x.val < 2 ^ 32 := x.bv.isLt
  have hx64 : x.val < 2 ^ 64 := Nat.lt_of_lt_of_le hx (by decide)
  change (x.bv.setWidth 64).toNat = x.bv.toNat
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx64]

private theorem acceptedPairsRel_nil_eq {I_s O_s I_m O_m : Type}
    {InRel : I_s → I_m → Prop} {OutRel : O_s → O_m → Prop}
    {xs : List (I_m × O_m)}
    (h : AcceptedPairsRel InRel OutRel [] xs) : xs = [] := by
  cases hxs : xs with
  | nil => rfl
  | cons _ _ => rw [hxs] at h; cases h

private theorem u8_cast_u32_val (x : Std.U8) :
    (UScalar.cast .U32 x).val = x.val := by
  have hx : x.val < 2 ^ 8 := x.bv.isLt
  have hx32 : x.val < 2 ^ 32 := Nat.lt_of_lt_of_le hx (by decide)
  change (x.bv.setWidth 32).toNat = x.bv.toNat
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx32]

private theorem u64_max_val : core.num.U64.MAX.val = 2 ^ 64 - 1 :=
  BitVec.toNat_allOnes

private theorem u64_val_le_max (x : Std.U64) : x.val ≤ core.num.U64.MAX.val := by
  rw [u64_max_val]
  exact Nat.le_pred_of_lt x.bv.isLt

private theorem u64_lt_max_of_ne {x : Std.U64} (hne : x ≠ core.num.U64.MAX) :
    x.val < core.num.U64.MAX.val :=
  Nat.lt_of_le_of_ne (u64_val_le_max x) fun hv => hne (UScalar.eq_of_val_eq hv)

private theorem u64_add_one_lt64_of_ne_max {x : Std.U64} (hne : x ≠ core.num.U64.MAX) :
    x.val + 1 < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (Nat.succ_le_of_lt (u64_lt_max_of_ne hne)) core.num.U64.MAX.bv.isLt

/-! ## 1. `VerifiedBeltQuorumGuard` (`2 * q > n + f` BFT Quorum-Switching + Bounded Jump + Poison) -/

/-- Mathematical BFT quorum-switching predicate validated by `validate_belt_quorum_config`:
    - non-empty committee `0 < n`,
    - corruption bound strictly below reconstruction threshold `f < t`,
    - signing quorum at least threshold `t ≤ q ≤ n`,
    - Byzantine intersection `n + f < 2 * q` (any two `q`-quorums share `≥ f + 1` parties),
    - global-liveness availability `q + f ≤ n` whenever `global_liveness_mode = true`. -/
@[expose]
def ValidBeltQuorumConfigProp
    (n t f q : Std.U32) (global_liveness_mode : Bool) : Prop :=
  0 < n.val ∧
  f.val < t.val ∧
  t.val ≤ q.val ∧
  q.val ≤ n.val ∧
  n.val + f.val < 2 * q.val ∧
  (global_liveness_mode = true → q.val + f.val ≤ n.val)

abbrev validBeltQuorumConfigBool
    (n t f q : Std.U32) (global_liveness_mode : Bool) : Bool :=
  decide (0 < n.val) &&
  decide (f.val < t.val) &&
  decide (t.val ≤ q.val) &&
  decide (q.val ≤ n.val) &&
  decide (n.val + f.val < 2 * q.val) &&
  (!global_liveness_mode || decide (q.val + f.val ≤ n.val))

private theorem validBeltQuorumConfigBool_iff
    (n t f q : Std.U32) (gl : Bool) :
    validBeltQuorumConfigBool n t f q gl = true ↔
      ValidBeltQuorumConfigProp n t f q gl := by
  dsimp only [validBeltQuorumConfigBool, ValidBeltQuorumConfigProp]
  cases gl <;> simp [and_assoc]

theorem validate_belt_quorum_config_eq
    (n t f q : Std.U32) (require_global_liveness : Bool) :
    pants_and_quorum_guards.validate_belt_quorum_config n t f q require_global_liveness =
      .ok (validBeltQuorumConfigBool n t f q require_global_liveness) := by
  unfold pants_and_quorum_guards.validate_belt_quorum_config
  by_cases hn0 : n = 0#u32
  · subst hn0
    simp [validBeltQuorumConfigBool]
  · have hn_pos : 0 < n.val :=
      Nat.pos_of_ne_zero fun h => hn0 (UScalar.eq_of_val_eq h)
    by_cases hft : f >= t
    · have hge_ft : t.val ≤ f.val := (UScalar.le_iff_val _ _).mp hft
      have hnlt_ft : ¬ f.val < t.val := Nat.not_lt_of_ge hge_ft
      simp [hn0, hft, validBeltQuorumConfigBool, hn_pos, hnlt_ft]
    · have hlt_ft : f.val < t.val :=
        Nat.lt_of_not_ge fun h => hft ((UScalar.le_iff_val _ _).mpr h)
      by_cases htq : t > q
      · have hgt_tq : q.val < t.val := (UScalar.lt_iff_val _ _).mp htq
        have hnle_tq : ¬ t.val ≤ q.val := Nat.not_le_of_gt hgt_tq
        simp [hn0, hft, htq, validBeltQuorumConfigBool, hn_pos, hlt_ft, hnle_tq]
      · have hle_tq : t.val ≤ q.val :=
          Nat.le_of_not_gt fun h => htq ((UScalar.lt_iff_val _ _).mpr h)
        by_cases hqn : q > n
        · have hgt_qn : n.val < q.val := (UScalar.lt_iff_val _ _).mp hqn
          have hnle_qn : ¬ q.val ≤ n.val := Nat.not_le_of_gt hgt_qn
          simp [hn0, hft, htq, hqn, validBeltQuorumConfigBool, hn_pos, hlt_ft, hle_tq, hnle_qn]
        · have hle_qn : q.val ≤ n.val :=
            Nat.le_of_not_gt fun h => hqn ((UScalar.lt_iff_val _ _).mpr h)
          let q64 := UScalar.cast .U64 q
          let n64 := UScalar.cast .U64 n
          let f64 := UScalar.cast .U64 f
          have hq64 : q64.val = q.val := u32_cast_u64_val q
          have hn64 : n64.val = n.val := u32_cast_u64_val n
          have hf64 : f64.val = f.val := u32_cast_u64_val f
          have hq_lt : q.val < 2 ^ 32 := q.bv.isLt
          have hn_lt : n.val < 2 ^ 32 := n.bv.isLt
          have hf_lt : f.val < 2 ^ 32 := f.bv.isLt
          have h2q_bound : q64.val + q64.val < 2 ^ 64 := by
            rw [hq64]
            exact Nat.lt_trans (Nat.add_lt_add hq_lt hq_lt) (by decide)
          have hnf_bound : n64.val + f64.val < 2 ^ 64 := by
            rw [hn64, hf64]
            exact Nat.lt_trans (Nat.add_lt_add hn_lt hf_lt) (by decide)
          let two_q : Std.U64 := ⟨q64.bv + q64.bv⟩
          have hadd_2q : (q64 + q64 : Result Std.U64) = .ok two_q := by
            simp only [hAdd_uscalar_eq, h2q_bound, ite_true]; rfl
          have hv_2q : two_q.val = 2 * q.val := by
            change (q64.bv + q64.bv).toNat = 2 * q.val
            rw [BitVec.toNat_add, Nat.mod_eq_of_lt h2q_bound, hq64, Nat.two_mul]
          let n_plus_f : Std.U64 := ⟨n64.bv + f64.bv⟩
          have hadd_nf : (n64 + f64 : Result Std.U64) = .ok n_plus_f := by
            simp only [hAdd_uscalar_eq, hnf_bound, ite_true]; rfl
          have hv_nf : n_plus_f.val = n.val + f.val := by
            change (n64.bv + f64.bv).toNat = n.val + f.val
            rw [BitVec.toNat_add, Nat.mod_eq_of_lt hnf_bound, hn64, hf64]
          simp only [hn0, hft, htq, hqn, ite_false, lift_eq_ok, bind_eq_result_bind, result_bind_ok]
          rw [hadd_2q, result_bind_ok, hadd_nf, result_bind_ok]
          by_cases h2q_le : two_q <= n_plus_f
          · have hle_val : 2 * q.val ≤ n.val + f.val := by
              rw [← hv_2q, ← hv_nf]; exact (UScalar.le_iff_val _ _).mp h2q_le
            have hnlt_2q : ¬ (n.val + f.val < 2 * q.val) := Nat.not_lt_of_ge hle_val
            simp [h2q_le, validBeltQuorumConfigBool, hn_pos, hlt_ft, hle_tq, hle_qn, hnlt_2q]
          · have hlt_2q : n.val + f.val < 2 * q.val := by
              rw [← hv_2q, ← hv_nf]
              exact Nat.lt_of_not_ge fun h => h2q_le ((UScalar.le_iff_val _ _).mpr h)
            simp only [h2q_le, ite_false]
            cases require_global_liveness with
            | false =>
              simp [validBeltQuorumConfigBool, hn_pos, hlt_ft, hle_tq, hle_qn, hlt_2q]
            | true =>
              have hfn : f.val ≤ n.val :=
                Nat.le_trans (Nat.le_of_lt hlt_ft) (Nat.le_trans hle_tq hle_qn)
              let nmf : Std.U32 := ⟨n.bv - f.bv⟩
              have hsub_nf : (n - f : Result Std.U32) = .ok nmf := by
                simp only [hSub_uscalar_eq, hfn, ite_true]; rfl
              have hv_nmf : nmf.val = n.val - f.val :=
                BitVec.toNat_sub_of_le (BitVec.le_def.mpr hfn)
              simp only [ite_true, hsub_nf, result_bind_ok]
              by_cases hq_gt : q > nmf
              · have hgt_val : n.val - f.val < q.val := by
                  rw [← hv_nmf]; exact (UScalar.lt_iff_val _ _).mp hq_gt
                have hnle_gl : ¬ (q.val + f.val ≤ n.val) := by
                  intro hle_gl
                  have h1 : q.val ≤ n.val - f.val := Nat.le_sub_of_add_le hle_gl
                  exact Nat.not_lt_of_ge h1 hgt_val
                simp [hq_gt, validBeltQuorumConfigBool, hn_pos, hlt_ft, hle_tq, hle_qn, hlt_2q, hnle_gl]
              · have hle_sub : q.val ≤ n.val - f.val := by
                  rw [← hv_nmf]
                  exact Nat.le_of_not_gt fun h => hq_gt ((UScalar.lt_iff_val _ _).mpr h)
                have hle_gl : q.val + f.val ≤ n.val := by
                  have h1 := Nat.add_le_add_right hle_sub f.val
                  rwa [Nat.sub_add_cancel hfn] at h1
                simp [hq_gt, validBeltQuorumConfigBool, hn_pos, hlt_ft, hle_tq, hle_qn, hlt_2q, hle_gl]

theorem validate_belt_quorum_config_spec
    (n t f q : Std.U32) (require_global_liveness : Bool) :
    ∃ b, pants_and_quorum_guards.validate_belt_quorum_config n t f q require_global_liveness = .ok b ∧
      (b = true ↔ ValidBeltQuorumConfigProp n t f q require_global_liveness) :=
  ⟨validBeltQuorumConfigBool n t f q require_global_liveness,
    validate_belt_quorum_config_eq n t f q require_global_liveness,
    validBeltQuorumConfigBool_iff n t f q require_global_liveness⟩

abbrev isBeltPhasePoisoned : pants_and_quorum_guards.BeltQuorumPhase → Bool
  | .Poisoned => true
  | _ => false

abbrev purePoisonBelt
    (st : pants_and_quorum_guards.BeltQuorumCore) :
    pants_and_quorum_guards.BeltQuorumCore :=
  { st with
    phase := .Poisoned
    ack_count := 0#u32
    poisoned := true }

abbrev beltGuardCorrupt
    (st : pants_and_quorum_guards.BeltQuorumCore) : Bool :=
  st.poisoned ||
  isBeltPhasePoisoned st.phase ||
  !validBeltQuorumConfigBool st.n st.t st.f st.q st.global_liveness_mode ||
  (st.has_bound_epoch && decide (st.next_epoch.val ≤ st.bound_epoch.val))

/-- Pure Mealy specification of `VerifiedBeltQuorumGuard::step`, capturing both accepted
    quorum-switching transitions and irreversible poison latching on WAL failure or
    conflicting `(epoch, msg_tag)` equivocation. -/
@[expose]
def beltQuorumMealy :
    MealySpec
      pants_and_quorum_guards.BeltQuorumCore
      pants_and_quorum_guards.BeltQuorumCoreInput
      pants_and_quorum_guards.BeltQuorumCoreOutput where
  step st inp :=
    if beltGuardCorrupt st then none
    else
      match inp with
      | .ProposeOrRetryEpoch ep tag walOk =>
        if !walOk then none
        else if st.has_bound_epoch && decide (ep = st.bound_epoch) then
          if decide (st.bound_msg_tag = tag) then
            some (st, .EpochBound)
          else none
        else if decide (ep.val < st.next_epoch.val) then none
        else if decide (st.max_jump_window.val < ep.val - st.next_epoch.val) then none
        else if decide (ep = core.num.U64.MAX) then none
        else
          let nextEp : Std.U64 := ⟨ep.bv + (1#u64).bv⟩
          some ({ st with
            next_epoch := nextEp
            phase := .EpochBoundPendingQuorum
            has_bound_epoch := true
            bound_epoch := ep
            bound_msg_tag := tag
            ack_count := 0#u32 }, .EpochBound)
      | .RecordCustodianAck ackEp ackTag =>
        if !st.has_bound_epoch then none
        else if decide (ackEp ≠ st.bound_epoch) then none
        else if !decide (st.bound_msg_tag = ackTag) then none
        else if decide (st.n.val ≤ st.ack_count.val) then none
        else
          let nextAcks : Std.U32 := ⟨st.ack_count.bv + (1#u32).bv⟩
          some ({ st with ack_count := nextAcks }, .AckRecorded nextAcks)
      | .AuthorizeShares reqEp reqTag =>
        if !st.has_bound_epoch then none
        else if decide (reqEp ≠ st.bound_epoch) then none
        else if !decide (st.bound_msg_tag = reqTag) then none
        else if decide (st.ack_count.val < st.q.val) then none
        else
          some ({ st with phase := .SharesAuthorized },
            .SharesAuthorized {
              authorized_epoch := st.bound_epoch
              msg_tag := st.bound_msg_tag
              certified_acks := st.ack_count })
  errStep st inp :=
    if beltGuardCorrupt st then purePoisonBelt st
    else
      match inp with
      | .ProposeOrRetryEpoch ep tag walOk =>
        if !walOk then purePoisonBelt st
        else if st.has_bound_epoch && decide (ep = st.bound_epoch) then
          if decide (st.bound_msg_tag = tag) then st else purePoisonBelt st
        else if decide (ep.val < st.next_epoch.val) then purePoisonBelt st
        else st
      | .RecordCustodianAck ackEp ackTag =>
        if !st.has_bound_epoch then st
        else if decide (ackEp ≠ st.bound_epoch) then st
        else if !decide (st.bound_msg_tag = ackTag) then purePoisonBelt st
        else st
      | .AuthorizeShares reqEp reqTag =>
        if !st.has_bound_epoch then st
        else if decide (reqEp ≠ st.bound_epoch) then st
        else if !decide (st.bound_msg_tag = reqTag) then purePoisonBelt st
        else st

private theorem belt_propose_step_sim
    (s : pants_and_quorum_guards.BeltQuorumCore)
    (ep : Std.U64) (tag : Array Std.U8 32#usize) (walOk : Bool) :
    (∀ m' u,
      pants_and_quorum_guards.BeltQuorumCore.propose_or_retry_epoch s ep tag walOk =
        .ok (m', .Ok u) →
      beltQuorumMealy.step s (.ProposeOrRetryEpoch ep tag walOk) = some (m', .EpochBound)) ∧
    (∀ m' e,
      pants_and_quorum_guards.BeltQuorumCore.propose_or_retry_epoch s ep tag walOk =
        .ok (m', .Err e) →
      beltQuorumMealy.step s (.ProposeOrRetryEpoch ep tag walOk) = none ∧
      beltQuorumMealy.errStep s (.ProposeOrRetryEpoch ep tag walOk) = m') := by
  rcases s with ⟨n, t, f, q, gl, next_ep, max_jmp, phase, has_bound, bound_ep, bound_tag,
    ack_cnt, poisoned⟩
  unfold pants_and_quorum_guards.BeltQuorumCore.propose_or_retry_epoch
  unfold pants_and_quorum_guards.poison_belt_guard
  simp only [beltQuorumMealy, beltGuardCorrupt, purePoisonBelt]
  cases poisoned
  · cases phase
    case Poisoned =>
      simp [isBeltPhasePoisoned, bind_eq_result_bind, result_bind_ok]
    all_goals
      simp only [isBeltPhasePoisoned, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
        validate_belt_quorum_config_eq, bind_eq_result_bind, result_bind_ok]
      cases validBeltQuorumConfigBool n t f q gl
      · simp
      · simp only [Bool.not_true, Bool.false_or, ↓reduceIte]
        cases has_bound
        · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
          cases walOk
          · simp
          · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            by_cases hlt : ep < next_ep
            · have hlt_v : ep.val < next_ep.val := (UScalar.lt_iff_val _ _).mp hlt
              simp [hlt, hlt_v]
            · have hge_v : next_ep.val ≤ ep.val :=
                Nat.le_of_not_gt fun h => hlt ((UScalar.lt_iff_val _ _).mpr h)
              have hnlt_v : ¬ (ep.val < next_ep.val) := Nat.not_lt_of_ge hge_v
              obtain ⟨hsub, hv_sub⟩ := u64_sub_ok hge_v
              simp only [hlt, hnlt_v, decide_false, Bool.false_eq_true, ↓reduceIte,
                hsub, result_bind_ok]
              by_cases hjmp : (⟨ep.bv - next_ep.bv⟩ : Std.U64) > max_jmp
              · have hjmp_v : max_jmp.val < ep.val - next_ep.val := by
                  rw [← hv_sub]; exact (UScalar.lt_iff_val _ _).mp hjmp
                simp [hjmp, hjmp_v]
              · have hle_jmp : ep.val - next_ep.val ≤ max_jmp.val := by
                  rw [← hv_sub]
                  exact Nat.le_of_not_gt fun h => hjmp ((UScalar.lt_iff_val _ _).mpr h)
                have hnjmp_v : ¬ (max_jmp.val < ep.val - next_ep.val) :=
                  Nat.not_lt_of_ge hle_jmp
                simp only [hjmp, hnjmp_v, decide_false, Bool.false_eq_true, ↓reduceIte]
                by_cases hmax : ep = core.num.U64.MAX
                · simp [hmax]
                · have hadd_ok : (ep + 1#u64 : Result Std.U64) = .ok ⟨ep.bv + (1#u64).bv⟩ := by
                    have hb64 : ep.val + (1#u64).val < 2 ^ 64 := u64_add_one_lt64_of_ne_max hmax
                    simp only [hAdd_uscalar_eq, hb64, ite_true]
                  simp [hmax, hadd_ok, result_bind_ok]
        · simp only [Bool.true_and, ↓reduceIte]
          by_cases hcor : bound_ep >= next_ep
          · have hcor_v : next_ep.val ≤ bound_ep.val := (UScalar.le_iff_val _ _).mp hcor
            simp [hcor, hcor_v]
          · have hn_cor : ¬ (next_ep.val ≤ bound_ep.val) :=
              fun h => hcor ((UScalar.le_iff_val _ _).mpr h)
            simp only [hcor, hn_cor, decide_false, Bool.false_eq_true, ↓reduceIte]
            cases walOk
            · simp
            · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              by_cases hep_eq : ep = bound_ep
              · simp only [hep_eq, decide_true, ↓reduceIte, ct_eq_bytes32_spec,
                  result_bind_ok]
                by_cases htag : bound_tag = tag <;> simp [htag]
              · simp only [hep_eq, decide_false, Bool.false_eq_true, ↓reduceIte]
                by_cases hlt : ep < next_ep
                · have hlt_v : ep.val < next_ep.val := (UScalar.lt_iff_val _ _).mp hlt
                  simp [hlt, hlt_v]
                · have hge_v : next_ep.val ≤ ep.val :=
                    Nat.le_of_not_gt fun h => hlt ((UScalar.lt_iff_val _ _).mpr h)
                
                  have hnlt_v : ¬ (ep.val < next_ep.val) := Nat.not_lt_of_ge hge_v
                  obtain ⟨hsub, hv_sub⟩ := u64_sub_ok hge_v
                  simp only [hlt, hnlt_v, decide_false, Bool.false_eq_true, ↓reduceIte,
                    hsub, result_bind_ok]
                  by_cases hjmp : (⟨ep.bv - next_ep.bv⟩ : Std.U64) > max_jmp
                  · have hjmp_v : max_jmp.val < ep.val - next_ep.val := by
                      rw [← hv_sub]; exact (UScalar.lt_iff_val _ _).mp hjmp
                    simp [hjmp, hjmp_v]
                  · have hle_jmp : ep.val - next_ep.val ≤ max_jmp.val := by
                      rw [← hv_sub]
                      exact Nat.le_of_not_gt fun h => hjmp ((UScalar.lt_iff_val _ _).mpr h)
                  
                    have hnjmp_v : ¬ (max_jmp.val < ep.val - next_ep.val) :=
                      Nat.not_lt_of_ge hle_jmp
                    simp only [hjmp, hnjmp_v, decide_false, Bool.false_eq_true, ↓reduceIte]
                    by_cases hmax : ep = core.num.U64.MAX
                    · simp [hmax]
                    · have hadd_ok : (ep + 1#u64 : Result Std.U64) = .ok ⟨ep.bv + (1#u64).bv⟩ := by
                        have hb64 : ep.val + (1#u64).val < 2 ^ 64 := u64_add_one_lt64_of_ne_max hmax
                        simp only [hAdd_uscalar_eq, hb64, ite_true]
                      simp [hmax, hadd_ok, result_bind_ok]
  · simp [bind_eq_result_bind, result_bind_ok]

private theorem belt_ack_step_sim
    (s : pants_and_quorum_guards.BeltQuorumCore)
    (ackEp : Std.U64) (ackTag : Array Std.U8 32#usize) :
    (∀ m' c,
      pants_and_quorum_guards.BeltQuorumCore.record_custodian_ack s ackEp ackTag =
        .ok (m', .Ok c) →
      beltQuorumMealy.step s (.RecordCustodianAck ackEp ackTag) = some (m', .AckRecorded c)) ∧
    (∀ m' e,
      pants_and_quorum_guards.BeltQuorumCore.record_custodian_ack s ackEp ackTag =
        .ok (m', .Err e) →
      beltQuorumMealy.step s (.RecordCustodianAck ackEp ackTag) = none ∧
      beltQuorumMealy.errStep s (.RecordCustodianAck ackEp ackTag) = m') := by
  rcases s with ⟨n, t, f, q, gl, next_ep, max_jmp, phase, has_bound, bound_ep, bound_tag,
    ack_cnt, poisoned⟩
  unfold pants_and_quorum_guards.BeltQuorumCore.record_custodian_ack
  unfold pants_and_quorum_guards.poison_belt_guard
  simp only [beltQuorumMealy, beltGuardCorrupt, purePoisonBelt]
  cases poisoned
  · cases phase
    case Poisoned =>
      simp [isBeltPhasePoisoned, bind_eq_result_bind, result_bind_ok]
    all_goals
      simp only [isBeltPhasePoisoned, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
        validate_belt_quorum_config_eq, bind_eq_result_bind, result_bind_ok]
      cases validBeltQuorumConfigBool n t f q gl
      · simp
      · simp only [Bool.not_true, Bool.false_or, ↓reduceIte]
        cases has_bound
        · simp
        · simp only [Bool.true_and, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          by_cases hcor : bound_ep >= next_ep
          · have hcor_v : next_ep.val ≤ bound_ep.val := (UScalar.le_iff_val _ _).mp hcor
            simp [hcor, hcor_v]
          · have hn_cor : ¬ (next_ep.val ≤ bound_ep.val) :=
              fun h => hcor ((UScalar.le_iff_val _ _).mpr h)
            simp only [hcor, hn_cor, decide_false, Bool.false_eq_true, ↓reduceIte]
            by_cases hep : ackEp = bound_ep
            · simp only [hep, bne_self_eq_false, Bool.false_eq_true, ne_eq, not_true_eq_false,
                decide_false, ↓reduceIte, ct_eq_bytes32_spec, result_bind_ok]
              by_cases htag : bound_tag = ackTag
              · simp only [htag, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                by_cases hack_ge : ack_cnt >= n
                · have hge_v : n.val ≤ ack_cnt.val := (UScalar.le_iff_val _ _).mp hack_ge
                  simp [hack_ge, hge_v]
                · have hlt_v : ack_cnt.val < n.val :=
                    Nat.lt_of_not_ge fun h => hack_ge ((UScalar.le_iff_val _ _).mpr h)
                  have hnle_v : ¬ (n.val ≤ ack_cnt.val) := Nat.not_le_of_gt hlt_v
                  have hadd_ok :
                      (ack_cnt + 1#u32 : Result Std.U32) =
                        .ok ⟨ack_cnt.bv + (1#u32).bv⟩ := by
                    have hb32 : ack_cnt.val + (1#u32).val < 2 ^ 32 :=
                      Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hlt_v) n.bv.isLt
                    simp only [hAdd_uscalar_eq, hb32, ite_true]
                  simp [hack_ge, hnle_v, hadd_ok, result_bind_ok]
              · simp [htag]
            · have hne : (ackEp != bound_ep) = true := bne_iff_ne.mpr hep
              simp [hep, hne]
  · simp [bind_eq_result_bind, result_bind_ok]

private theorem belt_auth_step_sim
    (s : pants_and_quorum_guards.BeltQuorumCore)
    (reqEp : Std.U64) (reqTag : Array Std.U8 32#usize) :
    (∀ m' g,
      pants_and_quorum_guards.BeltQuorumCore.authorize_shares s reqEp reqTag =
        .ok (m', .Ok g) →
      beltQuorumMealy.step s (.AuthorizeShares reqEp reqTag) = some (m', .SharesAuthorized g)) ∧
    (∀ m' e,
      pants_and_quorum_guards.BeltQuorumCore.authorize_shares s reqEp reqTag =
        .ok (m', .Err e) →
      beltQuorumMealy.step s (.AuthorizeShares reqEp reqTag) = none ∧
      beltQuorumMealy.errStep s (.AuthorizeShares reqEp reqTag) = m') := by
  rcases s with ⟨n, t, f, q, gl, next_ep, max_jmp, phase, has_bound, bound_ep, bound_tag,
    ack_cnt, poisoned⟩
  unfold pants_and_quorum_guards.BeltQuorumCore.authorize_shares
  unfold pants_and_quorum_guards.poison_belt_guard
  simp only [beltQuorumMealy, beltGuardCorrupt, purePoisonBelt]
  cases poisoned
  · cases phase
    case Poisoned =>
      simp [isBeltPhasePoisoned, bind_eq_result_bind, result_bind_ok]
    all_goals
      simp only [isBeltPhasePoisoned, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
        validate_belt_quorum_config_eq, bind_eq_result_bind, result_bind_ok]
      cases validBeltQuorumConfigBool n t f q gl
      · simp
      · simp only [Bool.not_true, Bool.false_or, ↓reduceIte]
        cases has_bound
        · simp
        · simp only [Bool.true_and, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          by_cases hcor : bound_ep >= next_ep
          · have hcor_v : next_ep.val ≤ bound_ep.val := (UScalar.le_iff_val _ _).mp hcor
            simp [hcor, hcor_v]
          · have hn_cor : ¬ (next_ep.val ≤ bound_ep.val) :=
              fun h => hcor ((UScalar.le_iff_val _ _).mpr h)
            simp only [hcor, hn_cor, decide_false, Bool.false_eq_true, ↓reduceIte]
            by_cases hep : reqEp = bound_ep
            · simp only [hep, bne_self_eq_false, Bool.false_eq_true, ne_eq, not_true_eq_false,
                decide_false, ↓reduceIte, ct_eq_bytes32_spec, result_bind_ok]
              by_cases htag : bound_tag = reqTag
              · simp only [htag, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                by_cases hlt_q : ack_cnt < q
                · have hlt_v : ack_cnt.val < q.val := (UScalar.lt_iff_val _ _).mp hlt_q
                  simp [hlt_q, hlt_v]
                · have hnlt_v : ¬ (ack_cnt.val < q.val) :=
                    fun h => hlt_q ((UScalar.lt_iff_val _ _).mpr h)
                  simp [hlt_q, hnlt_v]
              · simp [htag]
            · have hne : (reqEp != bound_ep) = true := bne_iff_ne.mpr hep
              simp [hep, hne]
  · simp [bind_eq_result_bind, result_bind_ok]

/-- Constructive single-step `MirStepSim` simulation from extracted Rust MIR
    `VerifiedBeltQuorumGuard::step` to `beltQuorumMealy` (`0 Classical.choice`). -/
theorem belt_quorum_step_sim :
    MirStepSim beltQuorumMealy
      (adaptStateResult pants_and_quorum_guards.BeltQuorumCore.step)
      Eq (fun a b => a = id b) (fun a b => a = id b) where
  ok_sim {s m m' i_s i_m o_m} hSt hIn hStep := by
    subst m; dsimp only [id] at hIn; subst i_s
    dsimp only [adaptStateResult] at hStep
    unfold pants_and_quorum_guards.BeltQuorumCore.step at hStep
    cases i_m with
    | ProposeOrRetryEpoch ep tag walOk =>
      dsimp only at hStep
      cases hf : pants_and_quorum_guards.BeltQuorumCore.propose_or_retry_epoch s ep tag walOk with
      | fail err => rw [hf] at hStep; cases hStep
      | div => rw [hf] at hStep; cases hStep
      | ok pair =>
        rcases pair with ⟨nx, res⟩
        simp only [hf, bind_eq_result_bind, result_bind_ok] at hStep
        cases res with
        | Err e => cases hStep
        | Ok u =>
          injection hStep with hAcc
          cases hAcc
          have hSim := (belt_propose_step_sim s ep tag walOk).1 _ _ hf
          rw [hSim]
          exact ⟨rfl, rfl⟩
    | RecordCustodianAck ackEp ackTag =>
      dsimp only at hStep
      cases hf : pants_and_quorum_guards.BeltQuorumCore.record_custodian_ack s ackEp ackTag with
      | fail err => rw [hf] at hStep; cases hStep
      | div => rw [hf] at hStep; cases hStep
      | ok pair =>
        rcases pair with ⟨nx, res⟩
        simp only [hf, bind_eq_result_bind, result_bind_ok] at hStep
        cases res with
        | Err e => cases hStep
        | Ok c =>
          injection hStep with hAcc
          cases hAcc
          have hSim := (belt_ack_step_sim s ackEp ackTag).1 _ _ hf
          rw [hSim]
          exact ⟨rfl, rfl⟩
    | AuthorizeShares reqEp reqTag =>
      dsimp only at hStep
      cases hf : pants_and_quorum_guards.BeltQuorumCore.authorize_shares s reqEp reqTag with
      | fail err => rw [hf] at hStep; cases hStep
      | div => rw [hf] at hStep; cases hStep
      | ok pair =>
        rcases pair with ⟨nx, res⟩
        simp only [hf, bind_eq_result_bind, result_bind_ok] at hStep
        cases res with
        | Err e => cases hStep
        | Ok g =>
          injection hStep with hAcc
          cases hAcc
          have hSim := (belt_auth_step_sim s reqEp reqTag).1 _ _ hf
          rw [hSim]
          exact ⟨rfl, rfl⟩
  err_preserves {s m m' i_s i_m e} hSt hIn hStep := by
    subst m; dsimp only [id] at hIn; subst i_s
    dsimp only [adaptStateResult] at hStep
    unfold pants_and_quorum_guards.BeltQuorumCore.step at hStep
    cases i_m with
    | ProposeOrRetryEpoch ep tag walOk =>
      dsimp only at hStep
      cases hf : pants_and_quorum_guards.BeltQuorumCore.propose_or_retry_epoch s ep tag walOk with
      | fail err => rw [hf] at hStep; cases hStep
      | div => rw [hf] at hStep; cases hStep
      | ok pair =>
        rcases pair with ⟨nx, res⟩
        simp only [hf, bind_eq_result_bind, result_bind_ok] at hStep
        cases res with
        | Ok u => cases hStep
        | Err _ =>
          injection hStep with hRej
          cases hRej
          exact (belt_propose_step_sim s ep tag walOk).2 _ _ hf
    | RecordCustodianAck ackEp ackTag =>
      dsimp only at hStep
      cases hf : pants_and_quorum_guards.BeltQuorumCore.record_custodian_ack s ackEp ackTag with
      | fail err => rw [hf] at hStep; cases hStep
      | div => rw [hf] at hStep; cases hStep
      | ok pair =>
        rcases pair with ⟨nx, res⟩
        simp only [hf, bind_eq_result_bind, result_bind_ok] at hStep
        cases res with
        | Ok c => cases hStep
        | Err _ =>
          injection hStep with hRej
          cases hRej
          exact (belt_ack_step_sim s ackEp ackTag).2 _ _ hf
    | AuthorizeShares reqEp reqTag =>
      dsimp only at hStep
      cases hf : pants_and_quorum_guards.BeltQuorumCore.authorize_shares s reqEp reqTag with
      | fail err => rw [hf] at hStep; cases hStep
      | div => rw [hf] at hStep; cases hStep
      | ok pair =>
        rcases pair with ⟨nx, res⟩
        simp only [hf, bind_eq_result_bind, result_bind_ok] at hStep
        cases res with
        | Ok g => cases hStep
        | Err _ =>
          injection hStep with hRej
          cases hRej
          exact (belt_auth_step_sim s reqEp reqTag).2 _ _ hf

private theorem belt_poisoned_trace_nil_and_sticky
    {st s_f : pants_and_quorum_guards.BeltQuorumCore}
    {pairs : List (pants_and_quorum_guards.BeltQuorumCoreInput ×
      pants_and_quorum_guards.BeltQuorumCoreOutput)}
    (hPois : st.poisoned = true)
    (hTr : beltQuorumMealy.ValidTrace st pairs s_f) :
    pairs = [] ∧ s_f.poisoned = true := by
  induction hTr with
  | nil _ => exact ⟨rfl, hPois⟩
  | @accept sa _ _ inp _ _ hStep _ _ =>
    simp only [beltQuorumMealy, beltGuardCorrupt] at hStep
    rw [hPois] at hStep
    simp at hStep
  | @reject sa _ inp _ hNone _ ih =>
    simp only [beltQuorumMealy, beltGuardCorrupt, purePoisonBelt] at ih
    rw [hPois] at ih
    simp only [Bool.true_or, ↓reduceIte] at ih
    exact ih trivial

/-- Once `VerifiedBeltQuorumGuard` has `poisoned = true`, NO subsequent safe-Rust call sequence
    can ever emit an accepted output or clear `poisoned`. -/
theorem belt_poisoned_blocks_all_future_mir
    (st0 st_final : pants_and_quorum_guards.BeltQuorumCore)
    (turns : List (MirTurn pants_and_quorum_guards.BeltQuorumCoreInput
      pants_and_quorum_guards.BeltQuorumCoreOutput
      pants_and_quorum_guards.PantsGuardError))
    (hPois : st0.poisoned = true)
    (hTr : MirTrace (adaptStateResult pants_and_quorum_guards.BeltQuorumCore.step)
      st0 turns st_final) :
    mirAcceptedPairs turns = [] ∧ st_final.poisoned = true := by
  have hInputs :=
    (show InputsMatchTurns (fun a b => a = id b) (turns.map (fun t => id t.input)) turns from by
      clear hTr
      induction turns with
      | nil => exact .nil
      | cons _ rest ih => exact .cons rfl ih)
  obtain ⟨hVal, hRelF, hPairs⟩ := belt_quorum_step_sim.lift_runInputs rfl hTr hInputs
  obtain ⟨hNil, hPoisF⟩ := belt_poisoned_trace_nil_and_sticky hPois hVal
  subst hRelF
  rw [hNil] at hPairs
  exact ⟨acceptedPairsRel_nil_eq hPairs, hPoisF⟩

private def BeltStateInv
    (n t f q : Std.U32) (gl : Bool) (floor : Nat)
    (st : pants_and_quorum_guards.BeltQuorumCore) : Prop :=
  st.n = n ∧ st.t = t ∧ st.f = f ∧ st.q = q ∧ st.global_liveness_mode = gl ∧
  validBeltQuorumConfigBool n t f q gl = true ∧
  floor ≤ st.next_epoch.val ∧
  st.ack_count.val ≤ n.val ∧
  (st.has_bound_epoch = true →
    floor ≤ st.bound_epoch.val ∧ st.bound_epoch.val < st.next_epoch.val) ∧
  (st.poisoned = false → isBeltPhasePoisoned st.phase = false)

private theorem belt_step_ok_properties
    {n t f q : Std.U32} {gl : Bool} {floor : Nat}
    {s s' : pants_and_quorum_guards.BeltQuorumCore}
    {inp : pants_and_quorum_guards.BeltQuorumCoreInput}
    {out : pants_and_quorum_guards.BeltQuorumCoreOutput}
    (hInv : BeltStateInv n t f q gl floor s)
    (hStep : beltQuorumMealy.step s inp = some (s', out)) :
    s.poisoned = false ∧
    s'.poisoned = false ∧
    BeltStateInv n t f q gl floor s' ∧
    (∀ g, out = .SharesAuthorized g →
      s.has_bound_epoch = true ∧
      s'.has_bound_epoch = true ∧
      s'.bound_epoch = s.bound_epoch ∧
      s'.bound_msg_tag = s.bound_msg_tag ∧
      s'.next_epoch = s.next_epoch ∧
      g.authorized_epoch = s.bound_epoch ∧
      g.msg_tag = s.bound_msg_tag ∧
      q.val ≤ g.certified_acks.val ∧
      g.certified_acks.val ≤ n.val ∧
      floor ≤ g.authorized_epoch.val) ∧
    (∀ ep tag walOk, inp = .ProposeOrRetryEpoch ep tag walOk →
      walOk = true ∧
      ((s.has_bound_epoch = true ∧ ep = s.bound_epoch ∧ tag = s.bound_msg_tag ∧ s' = s) ∨
       (s.next_epoch.val ≤ ep.val ∧
        ep.val ≤ s.next_epoch.val + s.max_jump_window.val ∧
        s'.has_bound_epoch = true ∧
        s'.bound_epoch = ep ∧
        s'.bound_msg_tag = tag ∧
        s'.next_epoch.val = ep.val + 1))) ∧
    ((s.has_bound_epoch = true →
      (s'.has_bound_epoch = true ∧
       s'.bound_epoch = s.bound_epoch ∧
       s'.bound_msg_tag = s.bound_msg_tag ∧
       s'.next_epoch = s.next_epoch) ∨
      BeltStateInv n t f q gl s.next_epoch.val s')) := by
  rcases hInv with ⟨hn, ht, hf, hq, hgl, hcfg, hfl_next, hack_le, hbound_inv, hph_inv⟩
  simp only [beltQuorumMealy, beltGuardCorrupt] at hStep
  rcases (by cases s.poisoned <;> simp : s.poisoned = false ∨ s.poisoned = true) with hp | hp
  · have hph_ok := hph_inv hp
    have hcfg_s : validBeltQuorumConfigBool s.n s.t s.f s.q s.global_liveness_mode = true := by
      rw [hn, ht, hf, hq, hgl]; exact hcfg
    have hcor_false : (s.has_bound_epoch && decide (s.next_epoch.val ≤ s.bound_epoch.val)) = false := by
      cases hhb : s.has_bound_epoch
      · rfl
      · simp only [Bool.true_and, decide_eq_false_iff_not]
        exact Nat.not_le_of_gt (hbound_inv hhb).2
    rw [hp, hph_ok, hcfg_s, hcor_false] at hStep
    simp only [Bool.false_or, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hStep
    cases inp with
    | ProposeOrRetryEpoch ep tag walOk =>
      dsimp only at hStep
      rcases (by cases walOk <;> simp : walOk = false ∨ walOk = true) with hwal | hwal
      · rw [hwal] at hStep; simp at hStep
      · rw [hwal] at hStep
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hStep
        by_cases hretry : (s.has_bound_epoch && decide (ep = s.bound_epoch)) = true
        · rw [hretry] at hStep
          simp only [↓reduceIte] at hStep
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hretry
          by_cases htag : s.bound_msg_tag = tag
          · have htd : decide (s.bound_msg_tag = tag) = true := decide_eq_true htag
            rw [htd] at hStep
            simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hStep
            rcases hStep with ⟨hs', hout⟩
            have hs_eq := hs'.symm; have ho_eq := hout.symm
            subst hs_eq; subst ho_eq
            refine ⟨hp, hp,
              ⟨hn, ht, hf, hq, hgl, hcfg, hfl_next, hack_le, hbound_inv, hph_inv⟩,
              (fun _ hg => nomatch hg),
              ?_,
              (fun _ => Or.inl ⟨hretry.1, rfl, rfl, rfl⟩)⟩
            intro ep' tag' wal' hinp
            injection hinp with hep' htag' hwal'
            subst hep'; subst htag'; subst hwal'
            exact ⟨hwal, Or.inl ⟨hretry.1, hretry.2, htag.symm, rfl⟩⟩
          · simp [htag] at hStep
        · simp only [Bool.not_eq_true] at hretry
          rw [hretry] at hStep
          simp only [Bool.false_eq_true, ↓reduceIte] at hStep
          by_cases hlt : ep.val < s.next_epoch.val
          · simp [hlt] at hStep
          · have hge_next : s.next_epoch.val ≤ ep.val := Nat.le_of_not_gt hlt
            simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte] at hStep
            by_cases hjmp : s.max_jump_window.val < ep.val - s.next_epoch.val
            · simp [hjmp] at hStep
            · have hle_jmp : ep.val - s.next_epoch.val ≤ s.max_jump_window.val :=
                Nat.le_of_not_gt hjmp
              have hep_le_win : ep.val ≤ s.next_epoch.val + s.max_jump_window.val := by
                have h1 := Nat.add_le_add_left hle_jmp s.next_epoch.val
                rwa [Nat.add_comm s.next_epoch.val, Nat.sub_add_cancel hge_next] at h1
              simp only [hjmp, decide_false, Bool.false_eq_true, ↓reduceIte] at hStep
              by_cases hmax : ep = core.num.U64.MAX
              · simp [hmax] at hStep
              · simp only [hmax, decide_false, Bool.false_eq_true, ↓reduceIte,
                  Option.some.injEq, Prod.mk.injEq] at hStep
                rcases hStep with ⟨hs', hout⟩
                have hs_eq := hs'.symm; have ho_eq := hout.symm
                subst hs_eq; subst ho_eq
                have hb64 : ep.val + 1 < 2 ^ 64 := u64_add_one_lt64_of_ne_max hmax
                have hv_next : (⟨ep.bv + (1#u64).bv⟩ : Std.U64).val = ep.val + 1 := by
                  change (ep.bv + (1#u64).bv).toNat = ep.val + 1
                  rw [BitVec.toNat_add]
                  exact Nat.mod_eq_of_lt hb64
                have hfl_ep : floor ≤ ep.val := Nat.le_trans hfl_next hge_next
                have hfl_next' : floor ≤ (⟨ep.bv + (1#u64).bv⟩ : Std.U64).val := by
                  rw [hv_next]; exact Nat.le_trans hfl_ep (Nat.le_succ _)
                refine ⟨hp, rfl, ?_, (fun _ hg => nomatch hg), ?_, ?_⟩
                · exact ⟨hn, ht, hf, hq, hgl, hcfg, hfl_next', Nat.zero_le _,
                    (fun _ => ⟨hfl_ep, by dsimp only; rw [hv_next]; exact Nat.lt_succ_self _⟩),
                    (fun _ => rfl)⟩
                · intro ep' tag' wal' hinp
                  injection hinp with hep' htag' hwal'
                  subst hep'; subst htag'; subst hwal'
                  exact ⟨hwal, Or.inr ⟨hge_next, hep_le_win, rfl, rfl, rfl, hv_next⟩⟩
                · intro _
                  right
                  exact ⟨hn, ht, hf, hq, hgl, hcfg,
                    (by dsimp only; rw [hv_next]; exact Nat.le_trans hge_next (Nat.le_succ _)),
                    Nat.zero_le _,
                    (fun _ => ⟨hge_next, by dsimp only; rw [hv_next]; exact Nat.lt_succ_self _⟩),
                    (fun _ => rfl)⟩
    | RecordCustodianAck ackEp ackTag =>
      dsimp only at hStep
      rcases (by cases s.has_bound_epoch <;> simp :
          s.has_bound_epoch = false ∨ s.has_bound_epoch = true) with hhb | hhb
      · rw [hhb] at hStep; simp at hStep
      · rw [hhb] at hStep
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hStep
        by_cases hep : ackEp = s.bound_epoch
        · simp only [hep, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
            ↓reduceIte] at hStep
          by_cases htag : s.bound_msg_tag = ackTag
          · have htd : decide (s.bound_msg_tag = ackTag) = true := decide_eq_true htag
            rw [htd] at hStep
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hStep
            by_cases hack_ge : s.n.val ≤ s.ack_count.val
            · simp [hack_ge] at hStep
            · have hlt_ack : s.ack_count.val < s.n.val := Nat.lt_of_not_ge hack_ge
              simp only [hack_ge, decide_false, Bool.false_eq_true, ↓reduceIte,
                Option.some.injEq, Prod.mk.injEq] at hStep
              rcases hStep with ⟨hs', hout⟩
              have hs_eq := hs'.symm; have ho_eq := hout.symm
              subst hs_eq; subst ho_eq
              have hb32 : s.ack_count.val + 1 < 2 ^ 32 :=
                Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hlt_ack) s.n.bv.isLt
              have hv_ack : (⟨s.ack_count.bv + (1#u32).bv⟩ : Std.U32).val = s.ack_count.val + 1 := by
                change (s.ack_count.bv + (1#u32).bv).toNat = s.ack_count.val + 1
                rw [BitVec.toNat_add]
                exact Nat.mod_eq_of_lt hb32
              have hack_le' : (⟨s.ack_count.bv + (1#u32).bv⟩ : Std.U32).val ≤ n.val := by
                rw [hv_ack, ← hn]; exact Nat.succ_le_of_lt hlt_ack
              refine ⟨hp, rfl, ?_, (fun _ hg => nomatch hg), (fun _ _ _ hinp => nomatch hinp),
                (fun _ => Or.inl ⟨rfl, rfl, rfl, rfl⟩)⟩
              exact ⟨hn, ht, hf, hq, hgl, hcfg, hfl_next, hack_le',
                (fun _ => hbound_inv hhb), (fun _ => hph_ok)⟩
          · simp [htag] at hStep
        · simp [hep] at hStep
    | AuthorizeShares reqEp reqTag =>
      dsimp only at hStep
      rcases (by cases s.has_bound_epoch <;> simp :
          s.has_bound_epoch = false ∨ s.has_bound_epoch = true) with hhb | hhb
      · rw [hhb] at hStep; simp at hStep
      · rw [hhb] at hStep
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hStep
        by_cases hep : reqEp = s.bound_epoch
        · simp only [hep, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
            ↓reduceIte] at hStep
          by_cases htag : s.bound_msg_tag = reqTag
          · have htd : decide (s.bound_msg_tag = reqTag) = true := decide_eq_true htag
            rw [htd] at hStep
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hStep
            by_cases hlt_q : s.ack_count.val < s.q.val
            · simp [hlt_q] at hStep
            · have hge_q : q.val ≤ s.ack_count.val := by
                rw [← hq]; exact Nat.le_of_not_gt hlt_q
              simp only [hlt_q, decide_false, Bool.false_eq_true, ↓reduceIte,
                Option.some.injEq, Prod.mk.injEq] at hStep
              rcases hStep with ⟨hs', hout⟩
              have hs_eq := hs'.symm; have ho_eq := hout.symm
              subst hs_eq; subst ho_eq
              refine ⟨hp, rfl, ?_, ?_, (fun _ _ _ hinp => nomatch hinp),
                (fun _ => Or.inl ⟨rfl, rfl, rfl, rfl⟩)⟩
              · exact ⟨hn, ht, hf, hq, hgl, hcfg, hfl_next, hack_le,
                  (fun _ => hbound_inv hhb), (fun _ => rfl)⟩
              · intro g hg
                injection hg with hg_eq
                subst hg_eq
                exact ⟨hhb, rfl, rfl, rfl, rfl, rfl, rfl, hge_q, hack_le, (hbound_inv hhb).1⟩
          · simp [htag] at hStep
        · simp [hep] at hStep
  · rw [hp] at hStep; simp at hStep

private theorem belt_errStep_dichotomy
    {n t f q : Std.U32} {gl : Bool} {floor : Nat}
    {s : pants_and_quorum_guards.BeltQuorumCore}
    {inp : pants_and_quorum_guards.BeltQuorumCoreInput}
    (_hInv : BeltStateInv n t f q gl floor s) :
    (beltQuorumMealy.errStep s inp).poisoned = true ∨
      beltQuorumMealy.errStep s inp = s := by
  dsimp only [beltQuorumMealy, purePoisonBelt]
  cases beltGuardCorrupt s
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases inp with
    | ProposeOrRetryEpoch ep tag walOk =>
      dsimp only
      cases walOk
      · exact Or.inl rfl
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        cases s.has_bound_epoch && decide (ep = s.bound_epoch)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases decide (ep.val < s.next_epoch.val)
          · exact Or.inr rfl
          · exact Or.inl rfl
        · simp only [↓reduceIte]
          cases decide (s.bound_msg_tag = tag)
          · exact Or.inl rfl
          · exact Or.inr rfl
    | RecordCustodianAck ackEp ackTag =>
      dsimp only
      cases s.has_bound_epoch
      · exact Or.inr rfl
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        cases decide (ackEp ≠ s.bound_epoch)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases decide (s.bound_msg_tag = ackTag)
          · exact Or.inl rfl
          · exact Or.inr rfl
        · exact Or.inr rfl
    | AuthorizeShares reqEp reqTag =>
      dsimp only
      cases s.has_bound_epoch
      · exact Or.inr rfl
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        cases decide (reqEp ≠ s.bound_epoch)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases decide (s.bound_msg_tag = reqTag)
          · exact Or.inl rfl
          · exact Or.inr rfl
        · exact Or.inr rfl
  · exact Or.inl rfl

private theorem belt_grants_above_floor
    {n t f q : Std.U32} {gl : Bool} {floor : Nat}
    {st s_f : pants_and_quorum_guards.BeltQuorumCore}
    {pairs : List (pants_and_quorum_guards.BeltQuorumCoreInput ×
      pants_and_quorum_guards.BeltQuorumCoreOutput)}
    (hInv : BeltStateInv n t f q gl floor st)
    (hTr : beltQuorumMealy.ValidTrace st pairs s_f) :
    ∀ p ∈ pairs, ∀ g, p.2 = .SharesAuthorized g →
      q.val ≤ g.certified_acks.val ∧
      g.certified_acks.val ≤ n.val ∧
      floor ≤ g.authorized_epoch.val := by
  induction hTr generalizing floor with
  | nil _ =>
    intro _ hm; exact False.elim (List.not_mem_nil hm)
  | @accept sa sb _ inp out rest hStep _ ih =>
    obtain ⟨_, _, hInvB, hGrant, _, _⟩ := belt_step_ok_properties hInv hStep
    intro p hp g hg
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hTailMem
    · obtain ⟨_, _, _, _, _, _, _, hq_le, hn_le, hfl_le⟩ := hGrant g hg
      exact ⟨hq_le, hn_le, hfl_le⟩
    · exact ih hInvB p hTailMem g hg
  | @reject sa _ inp _ _ hTail ih =>
    rcases belt_errStep_dichotomy hInv (inp := inp) with hPois | hSame
    · obtain ⟨hNil, _⟩ := belt_poisoned_trace_nil_and_sticky hPois hTail
      subst hNil
      intro _ hm; exact False.elim (List.not_mem_nil hm)
    · rw [hSame] at ih
      exact ih hInv

private theorem belt_future_grants_same_or_ge_next
    {n t f q : Std.U32} {gl : Bool} {floor : Nat}
    {st s_f : pants_and_quorum_guards.BeltQuorumCore}
    {pairs : List (pants_and_quorum_guards.BeltQuorumCoreInput ×
      pants_and_quorum_guards.BeltQuorumCoreOutput)}
    (hInv : BeltStateInv n t f q gl floor st)
    (hBound : st.has_bound_epoch = true)
    (hTr : beltQuorumMealy.ValidTrace st pairs s_f) :
    ∀ p ∈ pairs, ∀ g, p.2 = .SharesAuthorized g →
      (g.authorized_epoch = st.bound_epoch ∧ g.msg_tag = st.bound_msg_tag) ∨
      st.next_epoch.val ≤ g.authorized_epoch.val := by
  induction hTr with
  | nil _ =>
    intro _ hm; exact False.elim (List.not_mem_nil hm)
  | @accept sa sb _ inp out rest hStep hTail ih =>
    obtain ⟨_, _, hInvB, hGrant, _, hAdv⟩ := belt_step_ok_properties hInv hStep
    intro p hp g hg
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hTailMem
    · obtain ⟨_, _, _, _, _, hep, htag, _, _, _⟩ := hGrant g hg
      exact Or.inl ⟨hep, htag⟩
    · rcases hAdv hBound with ⟨hBoundB, hEpB, hTagB, hNextB⟩ | hInvNext
      · rcases ih hInvB hBoundB p hTailMem g hg with ⟨h1, h2⟩ | hGe
        · rw [hEpB] at h1; rw [hTagB] at h2
          exact Or.inl ⟨h1, h2⟩
        · rw [hNextB] at hGe
          exact Or.inr hGe
      · exact Or.inr (belt_grants_above_floor hInvNext hTail p hTailMem g hg).2.2
  | @reject sa _ inp _ _ hTail ih =>
    rcases belt_errStep_dichotomy hInv (inp := inp) with hPois | hSame
    · obtain ⟨hNil, _⟩ := belt_poisoned_trace_nil_and_sticky hPois hTail
      subst hNil
      intro _ hm; exact False.elim (List.not_mem_nil hm)
    · rw [hSame] at ih
      exact ih hInv hBound

private theorem belt_validTrace_non_equivocation
    {n t f q : Std.U32} {gl : Bool} {floor : Nat}
    {st s_f : pants_and_quorum_guards.BeltQuorumCore}
    {pairs : List (pants_and_quorum_guards.BeltQuorumCoreInput ×
      pants_and_quorum_guards.BeltQuorumCoreOutput)}
    (hInv : BeltStateInv n t f q gl floor st)
    (hTr : beltQuorumMealy.ValidTrace st pairs s_f) :
    (∀ p ∈ pairs, ∀ ep tag walOk, p.1 = .ProposeOrRetryEpoch ep tag walOk → walOk = true) ∧
    (∀ p1 ∈ pairs, ∀ p2 ∈ pairs, ∀ g1 g2,
      p1.2 = .SharesAuthorized g1 →
      p2.2 = .SharesAuthorized g2 →
      g1.authorized_epoch = g2.authorized_epoch →
      g1.msg_tag = g2.msg_tag) := by
  induction hTr with
  | nil _ =>
    exact ⟨fun _ hm => False.elim (List.not_mem_nil hm),
      fun _ hm => False.elim (List.not_mem_nil hm)⟩
  | @accept sa sb _ inp out rest hStep hTail ih =>
    obtain ⟨_, _, hInvB, hGrant, hProp, _⟩ := belt_step_ok_properties hInv hStep
    obtain ⟨hWalTail, hNoEqvTail⟩ := ih hInvB
    refine ⟨?_, ?_⟩
    · intro p hp ep tag walOk hinp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hMem
      · exact (hProp ep tag walOk hinp).1
      · exact hWalTail p hMem ep tag walOk hinp
    · intro p1 hp1 p2 hp2 g1 g2 hg1 hg2 hep_eq
      simp only [List.mem_cons] at hp1 hp2
      rcases hp1 with rfl | hm1 <;> rcases hp2 with rfl | hm2
      · rw [hg1] at hg2; injection hg2 with hge; rw [hge]
      · obtain ⟨_, hBoundB, hEpB, hTagB, hNextB, hep1, htag1, _, _, _⟩ := hGrant g1 hg1
        have hlt_next : sa.bound_epoch.val < sa.next_epoch.val :=
          (hInv.2.2.2.2.2.2.2.2.1 (hGrant g1 hg1).1).2
        rcases belt_future_grants_same_or_ge_next hInvB hBoundB hTail p2 hm2 g2 hg2 with
          ⟨_, htag2⟩ | hGe
        · rw [htag1, htag2, hTagB]
        · rw [hNextB, ← hep_eq, hep1] at hGe
          exact False.elim (Nat.not_lt_of_ge hGe hlt_next)
      · obtain ⟨_, hBoundB, hEpB, hTagB, hNextB, hep2, htag2, _, _, _⟩ := hGrant g2 hg2
        have hlt_next : sa.bound_epoch.val < sa.next_epoch.val :=
          (hInv.2.2.2.2.2.2.2.2.1 (hGrant g2 hg2).1).2
        rcases belt_future_grants_same_or_ge_next hInvB hBoundB hTail p1 hm1 g1 hg1 with
          ⟨_, htag1⟩ | hGe
        · rw [htag1, htag2, hTagB]
        · rw [hNextB, hep_eq, hep2] at hGe
          exact False.elim (Nat.not_lt_of_ge hGe hlt_next)
      · exact hNoEqvTail p1 hm1 p2 hm2 g1 g2 hg1 hg2 hep_eq
  | @reject sa _ inp _ _ hTail ih =>
    rcases belt_errStep_dichotomy hInv (inp := inp) with hPois | hSame
    · obtain ⟨hNil, _⟩ := belt_poisoned_trace_nil_and_sticky hPois hTail
      subst hNil
      exact ⟨fun _ hm => False.elim (List.not_mem_nil hm),
        fun _ hm => False.elim (List.not_mem_nil hm)⟩
    · rw [hSame] at ih
      exact ih hInv

/-- **Master Multi-Turn Soundness & Non-Equivocation Theorem for `VerifiedBeltQuorumGuard`:**
    Across ANY arbitrary sequence of safe-Rust `step` calls starting from a validated guard
    `VerifiedBeltQuorumGuard::new_validated`:
    1. `ValidBeltQuorumConfigProp` holds (`2 * q > n + f`, `0 < n`, `f < t ≤ q ≤ n`, and
       `q + f ≤ n` in global-liveness mode);
    2. Every `SharesAuthorized` grant has `q ≤ certified_acks ≤ n` and `initial_next_epoch ≤ authorized_epoch`;
    3. Every accepted `ProposeOrRetryEpoch` had `wal_sync_ok = true`;
    4. **Global Non-Equivocation:** no two `SharesAuthorized` grants anywhere in the multi-turn
       trace ever authorize distinct `msg_tag`s at the same `authorized_epoch`. -/
theorem belt_quorum_guard_multiturn_sound
    (n t f q : Std.U32) (require_global_liveness : Bool)
    (initial_next_epoch max_jump_window : Std.U64)
    (st0 st_final : pants_and_quorum_guards.BeltQuorumCore)
    (turns : List (MirTurn pants_and_quorum_guards.BeltQuorumCoreInput
      pants_and_quorum_guards.BeltQuorumCoreOutput
      pants_and_quorum_guards.PantsGuardError))
    (hNew : pants_and_quorum_guards.BeltQuorumCore.new_validated
      n t f q require_global_liveness initial_next_epoch max_jump_window = .ok (.Ok st0))
    (hTrace : MirTrace (adaptStateResult pants_and_quorum_guards.BeltQuorumCore.step)
      st0 turns st_final) :
    ValidBeltQuorumConfigProp n t f q require_global_liveness ∧
    (∀ p ∈ mirAcceptedPairs turns, ∀ ep tag walOk,
      p.1 = .ProposeOrRetryEpoch ep tag walOk → walOk = true) ∧
    (∀ p ∈ mirAcceptedPairs turns, ∀ g,
      p.2 = .SharesAuthorized g →
        q.val ≤ g.certified_acks.val ∧
        g.certified_acks.val ≤ n.val ∧
        initial_next_epoch.val ≤ g.authorized_epoch.val) ∧
    (∀ p1 ∈ mirAcceptedPairs turns, ∀ p2 ∈ mirAcceptedPairs turns, ∀ g1 g2,
      p1.2 = .SharesAuthorized g1 →
      p2.2 = .SharesAuthorized g2 →
      g1.authorized_epoch = g2.authorized_epoch →
      g1.msg_tag = g2.msg_tag) := by
  unfold pants_and_quorum_guards.BeltQuorumCore.new_validated at hNew
  rw [validate_belt_quorum_config_eq] at hNew
  simp only [bind_eq_result_bind, result_bind_ok] at hNew
  cases hcfg : validBeltQuorumConfigBool n t f q require_global_liveness
  · rw [hcfg] at hNew; simp at hNew
  · rw [hcfg] at hNew
    simp only [↓reduceIte, Result.ok.injEq, core.result.Result.Ok.injEq] at hNew
    have hProp : ValidBeltQuorumConfigProp n t f q require_global_liveness :=
      (validBeltQuorumConfigBool_iff n t f q require_global_liveness).mp hcfg
    have hInitInv : BeltStateInv n t f q require_global_liveness initial_next_epoch.val st0 := by
      rw [← hNew]
      exact ⟨rfl, rfl, rfl, rfl, rfl, hcfg, Nat.le_refl _,
        show 0 ≤ n.val from Nat.zero_le _,
        fun h => Bool.noConfusion h, fun _ => rfl⟩
    obtain ⟨hSafe, _⟩ :=
      belt_quorum_step_sim.lift_trace_safety_abs
        (Safe := fun pairs =>
          (∀ p ∈ pairs, ∀ ep tag walOk,
            p.1 = .ProposeOrRetryEpoch ep tag walOk → walOk = true) ∧
          (∀ p ∈ pairs, ∀ g,
            p.2 = .SharesAuthorized g →
              q.val ≤ g.certified_acks.val ∧
              g.certified_acks.val ≤ n.val ∧
              initial_next_epoch.val ≤ g.authorized_epoch.val) ∧
          (∀ p1 ∈ pairs, ∀ p2 ∈ pairs, ∀ g1 g2,
            p1.2 = .SharesAuthorized g1 →
            p2.2 = .SharesAuthorized g2 →
            g1.authorized_epoch = g2.authorized_epoch →
            g1.msg_tag = g2.msg_tag))
        (fun hVal =>
          let hNeqv := belt_validTrace_non_equivocation hInitInv hVal
          ⟨hNeqv.1, belt_grants_above_floor hInitInv hVal, hNeqv.2⟩)
        rfl
        hTrace
    rw [map_id_pair_pants] at hSafe
    exact ⟨hProp, hSafe.1, hSafe.2.1, hSafe.2.2⟩

/-- Direct single-step bounded epoch-jump theorem on extracted MIR `propose_or_retry_epoch`:
    every accepted proposal either idempotently retries `(bound_epoch, bound_msg_tag)` or
    satisfies `next_epoch ≤ proposed_epoch ≤ next_epoch + max_jump_window`. -/
theorem belt_propose_bounded_jump_spec
    (st st' : pants_and_quorum_guards.BeltQuorumCore)
    (ep : Std.U64) (tag : Array Std.U8 32#usize) (walOk : Bool)
    (hOk : pants_and_quorum_guards.BeltQuorumCore.propose_or_retry_epoch
      st ep tag walOk = .ok (st', .Ok ())) :
    walOk = true ∧
    ValidBeltQuorumConfigProp st.n st.t st.f st.q st.global_liveness_mode ∧
    st.poisoned = false ∧
    ((st.has_bound_epoch = true ∧ ep = st.bound_epoch ∧ tag = st.bound_msg_tag ∧ st' = st) ∨
     (st.next_epoch.val ≤ ep.val ∧
      ep.val ≤ st.next_epoch.val + st.max_jump_window.val ∧
      st'.bound_epoch = ep ∧
      st'.bound_msg_tag = tag ∧
      st'.next_epoch.val = ep.val + 1)) := by
  have hSim := (belt_propose_step_sim st ep tag walOk).1 st' () hOk
  simp only [beltQuorumMealy, beltGuardCorrupt] at hSim
  cases hp : st.poisoned
  · cases hph : isBeltPhasePoisoned st.phase
    · cases hcfg : validBeltQuorumConfigBool st.n st.t st.f st.q st.global_liveness_mode
      · rw [hp, hph, hcfg] at hSim; simp at hSim
      · have hProp :=
          (validBeltQuorumConfigBool_iff st.n st.t st.f st.q st.global_liveness_mode).mp hcfg
        cases hcor : (st.has_bound_epoch && decide (st.next_epoch.val ≤ st.bound_epoch.val))
        · rw [hp, hph, hcfg, hcor] at hSim
          simp only [Bool.false_or, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hSim
          cases hwal : walOk
          · rw [hwal] at hSim; simp at hSim
          · rw [hwal] at hSim
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hSim
            by_cases hretry : (st.has_bound_epoch && decide (ep = st.bound_epoch)) = true
            · rw [hretry] at hSim
              simp only [↓reduceIte] at hSim
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hretry
              by_cases htag : st.bound_msg_tag = tag
              · simp only [htag, decide_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hSim
                exact ⟨rfl, hProp, rfl, Or.inl ⟨hretry.1, hretry.2, htag.symm, hSim.1.symm⟩⟩
              · simp [htag] at hSim
            · simp only [Bool.not_eq_true] at hretry
              rw [hretry] at hSim
              simp only [Bool.false_eq_true, ↓reduceIte] at hSim
              by_cases hlt : ep.val < st.next_epoch.val
              · simp [hlt] at hSim
              · have hge_next : st.next_epoch.val ≤ ep.val := Nat.le_of_not_gt hlt
                simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte] at hSim
                by_cases hjmp : st.max_jump_window.val < ep.val - st.next_epoch.val
                · simp [hjmp] at hSim
                · have hle_jmp : ep.val - st.next_epoch.val ≤ st.max_jump_window.val :=
                    Nat.le_of_not_gt hjmp
                  have hep_le_win : ep.val ≤ st.next_epoch.val + st.max_jump_window.val := by
                    have h1 := Nat.add_le_add_left hle_jmp st.next_epoch.val
                    rwa [Nat.add_comm st.next_epoch.val, Nat.sub_add_cancel hge_next] at h1
                  simp only [hjmp, decide_false, Bool.false_eq_true, ↓reduceIte] at hSim
                  by_cases hmax : ep = core.num.U64.MAX
                  · simp [hmax] at hSim
                  · simp only [hmax, decide_false, Bool.false_eq_true, ↓reduceIte,
                      Option.some.injEq, Prod.mk.injEq] at hSim
                    rcases hSim with ⟨hst', _⟩
                    subst hst'
                    have hb64 : ep.val + 1 < 2 ^ 64 := u64_add_one_lt64_of_ne_max hmax
                    have hv_next : (⟨ep.bv + (1#u64).bv⟩ : Std.U64).val = ep.val + 1 := by
                      change (ep.bv + (1#u64).bv).toNat = ep.val + 1
                      rw [BitVec.toNat_add]
                      exact Nat.mod_eq_of_lt hb64
                    exact ⟨rfl, hProp, rfl, Or.inr ⟨hge_next, hep_le_win, rfl, rfl, hv_next⟩⟩
        · rw [hp, hph, hcfg, hcor] at hSim; simp at hSim
    · rw [hp, hph] at hSim; simp at hSim
  · rw [hp] at hSim; simp at hSim

/-! ## 2. `VerifiedWotsC256Guard` (256-Bit `WOTS+C` `w = 4, chains = 128, target_sum = 192`) -/

/-- Pure mathematical base-4 digit `chainIdx ∈ 0..128` (`0..=3`) extracted from big-endian
    2-bit pairs of `digest[chainIdx / 4]`. -/
@[expose]
def pureWotsC256Digit (digest : Array Std.U8 32#usize) (chainIdx : Nat) : Nat :=
  let b := (digest.val.getD (chainIdx / 4) 0#u8).val
  (b / (2 ^ (6 - 2 * (chainIdx % 4)))) % 4

/-- All 128 base-4 digits (`0..=3`) of a 32-byte `WOTS+C` digest. -/
@[expose]
def pureWotsC256Digits (digest : Array Std.U8 32#usize) : List Nat :=
  (List.range 128).map (pureWotsC256Digit digest)

private theorem u8_and_3_val (x : Std.U8) : (x &&& 3#u8).val = x.val % 4 := by
  change (x.bv &&& (3#u8).bv).toNat = x.bv.toNat % 4
  rw [BitVec.toNat_and]
  exact and_mask_eq_mod _ 2

private theorem u8_shr_and_3_val (b : Std.U8) (s : Std.I32) (k : Nat)
    (hs : (b >>> s : Result Std.U8) = .ok ⟨b.bv >>> k⟩) :
    ∃ d, (do let i2 ← b >>> s; ok (i2 &&& 3#u8)) = Result.ok d ∧
      d.val = (b.val / (2 ^ k)) % 4 ∧ d.val < 4 := by
  refine ⟨⟨b.bv >>> k⟩ &&& 3#u8, ?_, ?_, ?_⟩
  · simp [hs, bind_eq_result_bind, result_bind_ok]
  · rw [u8_and_3_val]
    change (b.bv >>> k).toNat % 4 = _
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  · rw [u8_and_3_val]
    exact Nat.mod_lt _ (by decide)

/-- Functional specification of `wotsc256_extract_digit` for every chain `chain_idx < 128`. -/
theorem wotsc256_extract_digit_spec
    (digest : Array Std.U8 32#usize) (chain_idx : Std.Usize)
    (hlt : chain_idx.val < 128) :
    ∃ d, pants_and_quorum_guards.wotsc256_extract_digit digest chain_idx = .ok d ∧
      d.val = pureWotsC256Digit digest chain_idx.val ∧
      d.val < 4 := by
  unfold pants_and_quorum_guards.wotsc256_extract_digit
  let qIdx : Std.Usize := ⟨chain_idx.bv / (4#usize).bv⟩
  have hdiv : (chain_idx / 4#usize : Result Std.Usize) = .ok qIdx := rfl
  have hv_q : qIdx.val = chain_idx.val / 4 := BitVec.toNat_udiv
  have hq_lt : qIdx.val < 32 := by
    rw [hv_q]
    exact (Nat.div_lt_iff_lt_mul (by decide)).mpr hlt
  have hget : Array.index_usize digest qIdx = .ok (digest.val.getD (chain_idx.val / 4) 0#u8) := by
    have h1 := array_index_getD digest qIdx 0#u8 hq_lt
    rwa [hv_q] at h1
  let rIdx : Std.Usize := ⟨chain_idx.bv % (4#usize).bv⟩
  have hmod : (chain_idx % 4#usize : Result Std.Usize) = .ok rIdx := rfl
  have hv_r : rIdx.val = chain_idx.val % 4 := BitVec.toNat_umod
  simp only [hdiv, hget, hmod, bind_eq_result_bind, result_bind_ok]
  let b := digest.val.getD (chain_idx.val / 4) 0#u8
  have hrem_lt : chain_idx.val % 4 < 4 := Nat.mod_lt _ (by decide)
  rw [hv_r]
  dsimp only [pureWotsC256Digit]
  match hrem : chain_idx.val % 4, hrem_lt with
  | 0, _ =>
    exact u8_shr_and_3_val b 6#i32 6 rfl
  | 1, _ =>
    exact u8_shr_and_3_val b 4#i32 4 rfl
  | 2, _ =>
    exact u8_shr_and_3_val b 2#i32 2 rfl
  | 3, _ =>
    refine ⟨b &&& 3#u8, rfl, ?_, ?_⟩
    · rw [u8_and_3_val, show 6 - 2 * 3 = 0 from rfl, Nat.pow_zero, Nat.div_one]
    · rw [u8_and_3_val]; exact Nat.mod_lt _ (by decide)
  | k + 4, hk =>
    exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 4 k) hk)

private theorem list_range_map_sum_eq_natPrefixSum (f : Nat → Nat) :
    ∀ n : Nat, ((List.range n).map f).sum = natPrefixSum f n
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append]
    simp [natPrefixSum, list_range_map_sum_eq_natPrefixSum f n]

theorem pureWotsC256Digits_sum_eq_prefix (digest : Array Std.U8 32#usize) :
    (pureWotsC256Digits digest).sum = natPrefixSum (pureWotsC256Digit digest) 128 :=
  list_range_map_sum_eq_natPrefixSum (pureWotsC256Digit digest) 128

private def wotsVerifyInv (digest : Array Std.U8 32#usize) (rem : Nat)
    (st : Std.U32 × Std.Usize) : Prop :=
  st.2.val + rem = 128 ∧
  st.1.val = natPrefixSum (pureWotsC256Digit digest) st.2.val ∧
  st.1.val ≤ 3 * st.2.val

private theorem wotsc256_verify_sum_fuel (digest : Array Std.U8 32#usize) :
    ∃ b, loopFuel 129
      (fun (sum1, i1) =>
        pants_and_quorum_guards.verified_wotsc256_verify_sum_loop.body digest sum1 i1)
      (0#u32, 0#usize) = .ok b ∧
      b = decide (natPrefixSum (pureWotsC256Digit digest) 128 = 192) := by
  apply loopFuel_total_rank
    (body := fun (sum1, i1) =>
      pants_and_quorum_guards.verified_wotsc256_verify_sum_loop.body digest sum1 i1)
    (P := wotsVerifyInv digest)
    (Q := fun b => b = decide (natPrefixSum (pureWotsC256Digit digest) 128 = 192))
    (n := 128) (x := (0#u32, 0#usize))
  · rintro ⟨sum, idx⟩ ⟨hidx0, hsum_eq, _⟩
    have hidx128 : idx.val = 128 := by simpa using hidx0
    have hnlt : ¬ (idx < pants_and_quorum_guards.WOTSC256_CHAINS) := by
      unfold pants_and_quorum_guards.WOTSC256_CHAINS
      intro h
      have hv := (UScalar.lt_iff_val _ _).mp h
      rw [hidx128] at hv
      exact Nat.lt_irrefl 128 hv
    refine ⟨decide (sum = pants_and_quorum_guards.WOTSC256_TARGET_SUM), ?_, ?_⟩
    · unfold pants_and_quorum_guards.verified_wotsc256_verify_sum_loop.body
      simp only [hnlt, ite_false]
    · unfold pants_and_quorum_guards.WOTSC256_TARGET_SUM
      apply decide_eq_decide.mpr
      rw [hidx128] at hsum_eq
      exact ⟨fun h => hsum_eq.symm.trans (congrArg UScalar.val h),
        fun h => UScalar.eq_of_val_eq (hsum_eq.trans h)⟩
  · intro rem ⟨sum, idx⟩ ⟨hrem, hsum_eq, hsum_bound⟩
    dsimp only at hrem hsum_eq hsum_bound
    have hlt_val : idx.val < 128 := by
      have h1 : idx.val < idx.val + (rem + 1) := Nat.lt_add_of_pos_right (Nat.succ_pos rem)
      rwa [hrem] at h1
    have hlt_u : idx < pants_and_quorum_guards.WOTSC256_CHAINS := by
      unfold pants_and_quorum_guards.WOTSC256_CHAINS
      exact (UScalar.lt_iff_val _ _).mpr hlt_val
    obtain ⟨d8, hd8, hv_d8, hlt_d8⟩ := wotsc256_extract_digit_spec digest idx hlt_val
    have hle_d8 : d8.val ≤ 3 := Nat.le_of_lt_succ hlt_d8
    let d32 := UScalar.cast .U32 d8
    have hv_d32 : d32.val = d8.val := u8_cast_u32_val d8
    have hd_le_max : d32.val ≤ (4294967295#u32).val := by
      rw [hv_d32]; exact Nat.le_trans hle_d8 (by decide)
    let cap : Std.U32 := ⟨(4294967295#u32).bv - d32.bv⟩
    have hsub : (4294967295#u32 - d32 : Result Std.U32) = .ok cap := by
      simp only [hSub_uscalar_eq, hd_le_max, ite_true]; rfl
    have hv_cap : cap.val = 4294967295 - d8.val := by
      change ((4294967295#u32).bv - d32.bv).toNat = _
      rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hd_le_max)]
      change 4294967295 - d32.val = _
      rw [hv_d32]
    have hsum_le_381 : sum.val ≤ 381 :=
      Nat.le_trans hsum_bound (Nat.mul_le_mul_left 3 (Nat.le_of_lt_succ hlt_val))
    have hcap_ge : 381 ≤ cap.val := by
      rw [hv_cap]
      have : 4294967295 - 3 ≤ 4294967295 - d8.val := Nat.sub_le_sub_left hle_d8 4294967295
      exact Nat.le_trans (by decide) this
    have hnot_gt : ¬ (sum > cap) := fun hgt =>
      Nat.not_lt_of_ge (Nat.le_trans hsum_le_381 hcap_ge) ((UScalar.lt_iff_val _ _).mp hgt)
    have hsum_lt32 : sum.val + d32.val < 2 ^ 32 := by
      rw [hv_d32]
      exact Nat.lt_of_le_of_lt (Nat.add_le_add hsum_le_381 hle_d8) (by decide)
    let sum' : Std.U32 := ⟨sum.bv + d32.bv⟩
    have hadd_s : (sum + d32 : Result Std.U32) = .ok sum' := by
      simp only [hAdd_uscalar_eq, hsum_lt32, ite_true]; rfl
    have hv_sum' : sum'.val = sum.val + d8.val := by
      change (sum.bv + d32.bv).toNat = _
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt hsum_lt32, hv_d32]
    have hidx_lt64 : idx.val + (1#usize).val < 2 ^ 64 :=
      Nat.lt_trans (Nat.succ_lt_succ hlt_val) (by decide)
    let idx' : Std.Usize := ⟨idx.bv + (1#usize).bv⟩
    have hadd_i : (idx + 1#usize : Result Std.Usize) = .ok idx' := by
      simp only [hAdd_uscalar_eq, hidx_lt64, ite_true]; rfl
    have hv_idx' : idx'.val = idx.val + 1 := by
      change (idx.bv + (1#usize).bv).toNat = _
      rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt hidx_lt64
    refine ⟨(sum', idx'), ?_, ?_⟩
    · unfold pants_and_quorum_guards.verified_wotsc256_verify_sum_loop.body
      simp only [hlt_u, ite_true, hd8, lift_eq_ok, bind_eq_result_bind, result_bind_ok]
      rw [hsub, result_bind_ok]
      simp only [hnot_gt, ite_false]
      rw [show UScalar.cast .U32 d8 = d32 from rfl, hadd_s, result_bind_ok, hadd_i, result_bind_ok]
    · refine ⟨?_, ?_, ?_⟩
      · rw [hv_idx', Nat.add_right_comm]; exact hrem
      · rw [hv_sum', hv_idx', hsum_eq, hv_d8]; rfl
      · rw [hv_sum', hv_idx', Nat.mul_add, Nat.mul_one]
        exact Nat.add_le_add hsum_bound hle_d8
  · exact ⟨rfl, rfl, Nat.zero_le 0⟩

/-- **Exact Functional Equivalence for `verified_wotsc256_verify_sum`:**
    The extracted Rust MIR loop always terminates without arithmetic failure and returns `true`
    iff the 128 base-4 digits of `digest` sum to `192`. -/
theorem verified_wotsc256_verify_sum_eq (digest : Array Std.U8 32#usize) :
    pants_and_quorum_guards.verified_wotsc256_verify_sum digest =
      .ok (decide (natPrefixSum (pureWotsC256Digit digest) 128 = 192)) := by
  unfold pants_and_quorum_guards.verified_wotsc256_verify_sum
  unfold pants_and_quorum_guards.verified_wotsc256_verify_sum_loop
  obtain ⟨b, hb, hbeq⟩ := wotsc256_verify_sum_fuel digest
  rw [hbeq] at hb
  exact loop_ok_of_loopFuel (fuel := 129) (usize_lt_loopMaxFuel 128#usize) hb

theorem verified_wotsc256_verify_sum_spec (digest : Array Std.U8 32#usize) :
    ∃ b, pants_and_quorum_guards.verified_wotsc256_verify_sum digest = .ok b ∧
      (b = true ↔ (pureWotsC256Digits digest).sum = 192) := by
  refine ⟨decide (natPrefixSum (pureWotsC256Digit digest) 128 = 192),
    verified_wotsc256_verify_sum_eq digest, ?_⟩
  rw [pureWotsC256Digits_sum_eq_prefix]
  exact decide_eq_true_iff

private def wotsExtractInv (digest : Array Std.U8 32#usize) (rem : Nat)
    (st : Array Std.U8 128#usize × Std.Usize) : Prop :=
  st.2.val + rem = 128 ∧
  ∀ k < st.2.val, (st.1.val.getD k 0#u8).val = pureWotsC256Digit digest k

private theorem list_getD_set_eq {α : Type} :
    ∀ (xs : List α) (i : Nat) (v d : α), i < xs.length → (xs.set i v).getD i d = v
  | [], _, _, _, hi => False.elim (Nat.not_lt_zero _ hi)
  | _ :: _, 0, _, _, _ => rfl
  | _ :: tl, i + 1, v, d, hi => list_getD_set_eq tl i v d (Nat.lt_of_succ_lt_succ hi)

private theorem list_getD_set_ne {α : Type} :
    ∀ (xs : List α) (i k : Nat) (v d : α), k < xs.length → i ≠ k →
      (xs.set i v).getD k d = xs.getD k d
  | [], _, _, _, _, hk, _ => False.elim (Nat.not_lt_zero _ hk)
  | _ :: _, 0, 0, _, _, _, hne => False.elim (hne rfl)
  | _ :: _, 0, _ + 1, _, _, _, _ => rfl
  | _ :: _, _ + 1, 0, _, _, _, _ => rfl
  | _ :: tl, i + 1, k + 1, v, d, hk, hne =>
    list_getD_set_ne tl i k v d (Nat.lt_of_succ_lt_succ hk)
      (fun h => hne (congrArg Nat.succ h))

private theorem wotsc256_extract_digits_fuel (digest : Array Std.U8 32#usize) :
    ∃ arr, loopFuel 129
      (fun (digits1, i1) =>
        pants_and_quorum_guards.verified_wotsc256_extract_digits_loop.body digest digits1 i1)
      (Array.repeat 128#usize 0#u8, 0#usize) = .ok arr ∧
      (∀ k < 128, (arr.val.getD k 0#u8).val = pureWotsC256Digit digest k) := by
  apply loopFuel_total_rank
    (body := fun (digits1, i1) =>
      pants_and_quorum_guards.verified_wotsc256_extract_digits_loop.body digest digits1 i1)
    (P := wotsExtractInv digest)
    (Q := fun arr => ∀ k < 128, (arr.val.getD k 0#u8).val = pureWotsC256Digit digest k)
    (n := 128) (x := (Array.repeat 128#usize 0#u8, 0#usize))
  · rintro ⟨arr, idx⟩ ⟨hidx0, hpre⟩
    have hidx128 : idx.val = 128 := by simpa using hidx0
    have hnlt : ¬ (idx < pants_and_quorum_guards.WOTSC256_CHAINS) := by
      unfold pants_and_quorum_guards.WOTSC256_CHAINS
      intro h
      have hv := (UScalar.lt_iff_val _ _).mp h
      rw [hidx128] at hv
      exact Nat.lt_irrefl 128 hv
    refine ⟨arr, ?_, ?_⟩
    · unfold pants_and_quorum_guards.verified_wotsc256_extract_digits_loop.body
      simp [hnlt]
    · rw [hidx128] at hpre; exact hpre
  · intro rem ⟨arr, idx⟩ ⟨hrem, hpre⟩
    dsimp only at hrem hpre
    have hlt_val : idx.val < 128 := by
      have h1 : idx.val < idx.val + (rem + 1) := Nat.lt_add_of_pos_right (Nat.succ_pos rem)
      rwa [hrem] at h1
    have hlt_u : idx < pants_and_quorum_guards.WOTSC256_CHAINS := by
      unfold pants_and_quorum_guards.WOTSC256_CHAINS
      exact (UScalar.lt_iff_val _ _).mpr hlt_val
    obtain ⟨d8, hd8, hv_d8, _⟩ := wotsc256_extract_digit_spec digest idx hlt_val
    have harr_len : idx.val < arr.val.length := by rw [arr.property]; exact hlt_val
    let arr' : Array Std.U8 128#usize :=
      ⟨arr.val.set idx.val d8, by rw [List.length_set]; exact arr.property⟩
    have hupd : Array.update arr idx d8 = .ok arr' := by
      unfold Array.update
      exact dite_eq_left_of_eq_true (eq_true harr_len)
    have hidx_lt64 : idx.val + (1#usize).val < 2 ^ 64 :=
      Nat.lt_trans (Nat.succ_lt_succ hlt_val) (by decide)
    let idx' : Std.Usize := ⟨idx.bv + (1#usize).bv⟩
    have hadd_i : (idx + 1#usize : Result Std.Usize) = .ok idx' := by
      simp only [hAdd_uscalar_eq, hidx_lt64, ite_true]; rfl
    have hv_idx' : idx'.val = idx.val + 1 := by
      change (idx.bv + (1#usize).bv).toNat = _
      rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt hidx_lt64
    refine ⟨(arr', idx'), ?_, ?_⟩
    · unfold pants_and_quorum_guards.verified_wotsc256_extract_digits_loop.body
      simp only [hlt_u, ite_true, hd8, hupd, hadd_i, bind_eq_result_bind, result_bind_ok]
    · refine ⟨by rw [hv_idx', Nat.add_right_comm]; exact hrem, ?_⟩
      intro k hk
      rw [hv_idx'] at hk
      by_cases hkeq : idx.val = k
      · subst hkeq
        change ((arr.val.set idx.val d8).getD idx.val 0#u8).val = _
        rw [list_getD_set_eq arr.val idx.val d8 0#u8 harr_len]
        exact hv_d8
      · have hk_lt : k < idx.val :=
          Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hk) (Ne.symm hkeq)
        have hk_len : k < arr.val.length := Nat.lt_trans hk_lt harr_len
        change ((arr.val.set idx.val d8).getD k 0#u8).val = _
        rw [list_getD_set_ne arr.val idx.val k d8 0#u8 hk_len hkeq]
        exact hpre k hk_lt
  · exact ⟨rfl, fun _ hk => False.elim (Nat.not_lt_zero _ hk)⟩

theorem verified_wotsc256_extract_digits_spec (digest : Array Std.U8 32#usize) :
    ∃ arr, pants_and_quorum_guards.verified_wotsc256_extract_digits digest = .ok arr ∧
      (∀ k < 128,
        (arr.val.getD k 0#u8).val = pureWotsC256Digit digest k ∧
        (arr.val.getD k 0#u8).val < 4) := by
  unfold pants_and_quorum_guards.verified_wotsc256_extract_digits
  unfold pants_and_quorum_guards.verified_wotsc256_extract_digits_loop
  obtain ⟨arr, harr, hval⟩ := wotsc256_extract_digits_fuel digest
  refine ⟨arr, loop_ok_of_loopFuel (fuel := 129) (usize_lt_loopMaxFuel 128#usize) harr, ?_⟩
  intro k hk
  refine ⟨hval k hk, ?_⟩
  rw [hval k hk]
  dsimp only [pureWotsC256Digit]
  exact Nat.mod_lt _ (by decide)

private theorem u8DigitsNatSum_take_eq_prefix (xs : List Std.U8) (f : Nat → Nat)
    (hlen : 128 ≤ xs.length)
    (hget : ∀ k < 128, (xs.getD k 0#u8).val = f k) :
    ∀ n ≤ 128, u8DigitsNatSum (xs.take n) = natPrefixSum f n
  | 0, _ => rfl
  | n + 1, hn => by
    have hn_lt_len : n < xs.length := Nat.lt_of_lt_of_le hn hlen
    rw [List.take_add_one, List.getElem?_eq_getElem hn_lt_len]
    dsimp only [Option.toList]
    have hsum_app : ∀ (ys : List Std.U8) (x : Std.U8),
        u8DigitsNatSum (ys ++ [x]) = u8DigitsNatSum ys + x.val := by
      intro ys x
      induction ys with
      | nil => simp [u8DigitsNatSum]
      | cons y rest ih => simp [u8DigitsNatSum, ih, Nat.add_assoc]
    rw [hsum_app, u8DigitsNatSum_take_eq_prefix xs f hlen hget n (Nat.le_of_lt hn),
      List.getElem_eq_getD 0#u8, hget n hn]
    rfl

/-- Specification of `VerifiedWotsC256Guard::from_digest_verified`: succeeds iff the 128
    base-4 digits of `digest` sum to `192`, sealing `digits` with `u8DigitsNatSum = 192`. -/
theorem wotsc256_guard_from_digest_spec (digest : Array Std.U8 32#usize) :
    (natPrefixSum (pureWotsC256Digit digest) 128 = 192 →
      ∃ g, pants_and_quorum_guards.VerifiedWotsC256Guard.from_digest_verified digest =
        .ok (.Ok g) ∧
        g.validated_digest = digest ∧
        g.verified_sum = 192#u32 ∧
        u8DigitsNatSum g.digits.val = 192 ∧
        (∀ k < 128,
          (g.digits.val.getD k 0#u8).val = pureWotsC256Digit digest k ∧
          (g.digits.val.getD k 0#u8).val < 4)) ∧
    (natPrefixSum (pureWotsC256Digit digest) 128 ≠ 192 →
      pants_and_quorum_guards.VerifiedWotsC256Guard.from_digest_verified digest =
        .ok (.Err .InvalidWotsC256TargetSum)) := by
  unfold pants_and_quorum_guards.VerifiedWotsC256Guard.from_digest_verified
  unfold pants_and_quorum_guards.WOTSC256_TARGET_SUM
  rw [verified_wotsc256_verify_sum_eq]
  simp only [bind_eq_result_bind, result_bind_ok]
  constructor
  · intro hsum
    simp only [hsum, decide_true, ↓reduceIte]
    obtain ⟨arr, harr, hdigits⟩ := verified_wotsc256_extract_digits_spec digest
    rw [harr, result_bind_ok]
    refine ⟨_, rfl, rfl, rfl, ?_, hdigits⟩
    have hlen128 : arr.val.length = 128 := arr.property
    have htake : arr.val.take 128 = arr.val := List.take_of_length_le (Nat.le_of_eq hlen128)
    rw [← htake]
    rw [u8DigitsNatSum_take_eq_prefix arr.val (pureWotsC256Digit digest)
      (Nat.le_of_eq hlen128.symm) (fun k hk => (hdigits k hk).1) 128 (Nat.le_refl 128)]
    exact hsum
  · intro hne
    simp [hne]

private def findStrictGt128 : List Std.U8 → List Std.U8 → Option Nat
  | [], _ => none
  | _, [] => none
  | x :: xs, y :: ys =>
    if y.val < x.val then some 0
    else (findStrictGt128 xs ys).map Nat.succ

private theorem findStrictGt128_some :
    ∀ {xs ys : List Std.U8} {idx : Nat},
      findStrictGt128 xs ys = some idx →
      ys.length = xs.length →
      idx < xs.length ∧ (ys.getD idx 0#u8).val < (xs.getD idx 0#u8).val
  | [], _, _, h, _ => by cases h
  | _ :: _, [], _, h, _ => by cases h
  | x :: xs, y :: ys, idx, h, hlen => by
    dsimp only [findStrictGt128] at h
    by_cases hlt : y.val < x.val
    · simp only [hlt, ↓reduceIte] at h
      injection h with h0; subst h0
      exact ⟨Nat.zero_lt_succ _, by simpa [List.getD] using hlt⟩
    · simp only [hlt, ↓reduceIte] at h
      cases hrec : findStrictGt128 xs ys with
      | none => rw [hrec] at h; cases h
      | some k =>
        rw [hrec] at h
        simp only [Option.map, Option.some.injEq] at h
        subst h
        obtain ⟨hk, hval⟩ := findStrictGt128_some hrec (Nat.succ.inj hlen)
        exact ⟨Nat.succ_lt_succ hk, by simpa [List.getD] using hval⟩

private theorem findStrictGt128_none :
    ∀ {xs ys : List Std.U8},
      findStrictGt128 xs ys = none →
      ys.length = xs.length →
      u8DigitsNatSum xs ≤ u8DigitsNatSum ys ∧
      (u8DigitsNatSum xs = u8DigitsNatSum ys → xs = ys)
  | [], [], _, _ => ⟨Nat.le_refl 0, fun _ => rfl⟩
  | [], _ :: _, _, hlen => by cases hlen
  | _ :: _, [], _, hlen => by cases hlen
  | x :: xs, y :: ys, hnone, hlen => by
    dsimp only [findStrictGt128] at hnone
    by_cases hlt : y.val < x.val
    · simp only [hlt, ↓reduceIte] at hnone; cases hnone
    · simp only [hlt, ↓reduceIte] at hnone
      have hxy : x.val ≤ y.val := Nat.le_of_not_gt hlt
      cases hrec : findStrictGt128 xs ys with
      | some _ => rw [hrec] at hnone; cases hnone
      | none =>
        obtain ⟨hle_tail, heq_tail⟩ := findStrictGt128_none hrec (Nat.succ.inj hlen)
        dsimp only [u8DigitsNatSum]
        refine ⟨Nat.add_le_add hxy hle_tail, ?_⟩
        intro hsum_eq
        have hx_eq_y : x.val = y.val := by
          by_cases hne : x.val = y.val
          · exact hne
          · have hstrict : x.val < y.val := Nat.lt_of_le_of_ne hxy hne
            have hstrict_sum : x.val + u8DigitsNatSum xs < y.val + u8DigitsNatSum ys :=
              Nat.add_lt_add_of_lt_of_le hstrict hle_tail
            exact False.elim (Nat.ne_of_lt hstrict_sum hsum_eq)
        have htail_eq : u8DigitsNatSum xs = u8DigitsNatSum ys := by
          rw [hx_eq_y] at hsum_eq; exact Nat.add_left_cancel hsum_eq
        rw [UScalar.eq_of_val_eq hx_eq_y, heq_tail htail_eq]

/-- Constructive (`0 Classical.choice`) constant-sum incomparability for two distinct
    `VerifiedWotsC256Guard` codewords: neither 128-digit vector componentwise dominates the other. -/
theorem wotsc256_128_sum192_incomparable_mir
    (d1 d2 : Array Std.U8 32#usize)
    (g1 g2 : pants_and_quorum_guards.VerifiedWotsC256Guard)
    (hg1 : pants_and_quorum_guards.VerifiedWotsC256Guard.from_digest_verified d1 = .ok (.Ok g1))
    (hg2 : pants_and_quorum_guards.VerifiedWotsC256Guard.from_digest_verified d2 = .ok (.Ok g2))
    (hne : g1.digits ≠ g2.digits) :
    (∃ i < 128, (g2.digits.val.getD i 0#u8).val < (g1.digits.val.getD i 0#u8).val) ∧
    (∃ j < 128, (g1.digits.val.getD j 0#u8).val < (g2.digits.val.getD j 0#u8).val) := by
  have hs1 : natPrefixSum (pureWotsC256Digit d1) 128 = 192 := by
    by_cases h : natPrefixSum (pureWotsC256Digit d1) 128 = 192
    · exact h
    · have herr := (wotsc256_guard_from_digest_spec d1).2 h
      rw [herr] at hg1; cases hg1
  have hs2 : natPrefixSum (pureWotsC256Digit d2) 128 = 192 := by
    by_cases h : natPrefixSum (pureWotsC256Digit d2) 128 = 192
    · exact h
    · have herr := (wotsc256_guard_from_digest_spec d2).2 h
      rw [herr] at hg2; cases hg2
  obtain ⟨g1', hg1', _, _, hsum1, _⟩ := (wotsc256_guard_from_digest_spec d1).1 hs1
  obtain ⟨g2', hg2', _, _, hsum2, _⟩ := (wotsc256_guard_from_digest_spec d2).1 hs2
  rw [hg1'] at hg1; injection hg1 with h1; injection h1 with h1'; subst h1'
  rw [hg2'] at hg2; injection hg2 with h2; injection h2 with h2'; subst h2'
  have hlen1 : g1'.digits.val.length = 128 := g1'.digits.property
  have hlen2 : g2'.digits.val.length = 128 := g2'.digits.property
  constructor
  · cases hgt12 : findStrictGt128 g1'.digits.val g2'.digits.val with
    | none =>
      obtain ⟨_, heq⟩ := findStrictGt128_none hgt12 (hlen2.trans hlen1.symm)
      exact False.elim (hne (Std.Array.ext (heq (hsum1.trans hsum2.symm))))
    | some i =>
      obtain ⟨hi, hlt⟩ := findStrictGt128_some hgt12 (hlen2.trans hlen1.symm)
      rw [hlen1] at hi; exact ⟨i, hi, hlt⟩
  · cases hgt21 : findStrictGt128 g2'.digits.val g1'.digits.val with
    | none =>
      obtain ⟨_, heq⟩ := findStrictGt128_none hgt21 (hlen1.trans hlen2.symm)
      exact False.elim (hne (Std.Array.ext (heq (hsum2.trans hsum1.symm)).symm))
    | some j =>
      obtain ⟨hj, hlt⟩ := findStrictGt128_some hgt21 (hlen1.trans hlen2.symm)
      rw [hlen2] at hj; exact ⟨j, hj, hlt⟩

/-! ## 3. `VerifiedRssPoisonLatch` (Sticky Terminal Verification-Failure Latch) -/

abbrev purePoisonRss : pants_and_quorum_guards.VerifiedRssPoisonLatch :=
  { pending_relations := 0#u64, unverified := true, poisoned := true }

/-- Pure Mealy specification of `VerifiedRssPoisonLatch::step`:
    any failed check (`RecordCheckResult false`) or relation-counter overflow irreversibly
    sets `poisoned = true` BEFORE clearing `pending_relations = 0`. -/
@[expose]
def rssPoisonMealy :
    MealySpec
      pants_and_quorum_guards.VerifiedRssPoisonLatch
      pants_and_quorum_guards.RssLatchStepInput
      pants_and_quorum_guards.RssLatchStepOutput where
  step st inp :=
    if st.poisoned then none
    else
      match inp with
      | .StageRelations count =>
        if decide (count = 0#u64) then none
        else if decide (st.pending_relations.val + count.val ≤ core.num.U64.MAX.val) then
          let nextP : Std.U64 := ⟨st.pending_relations.bv + count.bv⟩
          some ({ pending_relations := nextP, unverified := true, poisoned := false },
            .RelationsStaged nextP)
        else none
      | .RecordCheckResult checkOk =>
        if checkOk then
          some ({ pending_relations := 0#u64, unverified := false, poisoned := false },
            .CheckVerified)
        else none
      | .AuthorizeOpen =>
        if !st.unverified && decide (st.pending_relations = 0#u64) then
          some (st, .OpenAuthorized { verified_clean := true })
        else none
  errStep st inp :=
    if st.poisoned then purePoisonRss
    else
      match inp with
      | .StageRelations count =>
        if decide (count = 0#u64) then st else purePoisonRss
      | .RecordCheckResult _ => purePoisonRss
      | .AuthorizeOpen => st

/-- Constructive single-step `MirStepSim` simulation from extracted Rust MIR
    `VerifiedRssPoisonLatch::step` to `rssPoisonMealy` (`0 Classical.choice`). -/
theorem rss_poison_latch_step_sim :
    MirStepSim rssPoisonMealy
      (adaptStateResult pants_and_quorum_guards.VerifiedRssPoisonLatch.step)
      Eq (fun a b => a = id b) (fun a b => a = id b) where
  ok_sim {s m m' i_s i_m o_m} hSt hIn hStep := by
    subst m; dsimp only [id] at hIn; subst i_s
    rcases s with ⟨pend, unv, pois⟩
    dsimp only [adaptStateResult] at hStep
    unfold pants_and_quorum_guards.VerifiedRssPoisonLatch.step at hStep
    dsimp only [rssPoisonMealy, purePoisonRss]
    cases pois
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases i_m with
      | StageRelations count =>
        dsimp only at hStep ⊢
        unfold pants_and_quorum_guards.VerifiedRssPoisonLatch.stage_relations at hStep
        unfold pants_and_quorum_guards.poison_rss_latch at hStep
        simp only [Bool.false_eq_true, ↓reduceIte] at hStep
        by_cases hc0 : count = 0#u64
        · simp only [hc0, ↓reduceIte, bind_eq_result_bind, result_bind_ok] at hStep
          cases hStep
        · simp only [hc0, decide_false, Bool.false_eq_true, ↓reduceIte,
            bind_eq_result_bind] at hStep ⊢
          have hp_le_max : pend.val ≤ core.num.U64.MAX.val := u64_val_le_max pend
          let cap : Std.U64 := ⟨core.num.U64.MAX.bv - pend.bv⟩
          have hsub : (core.num.U64.MAX - pend : Result Std.U64) = .ok cap := by
            simp only [hSub_uscalar_eq, hp_le_max, ite_true]; rfl
          have hv_cap : cap.val = core.num.U64.MAX.val - pend.val := by
            change (core.num.U64.MAX.bv - pend.bv).toNat = _
            exact BitVec.toNat_sub_of_le (BitVec.le_def.mpr hp_le_max)
          rw [hsub, result_bind_ok] at hStep
          by_cases hov : count > cap
          · simp only [hov, ↓reduceIte, result_bind_ok] at hStep
            cases hStep
          · have hle_cap : count.val ≤ cap.val :=
              Nat.le_of_not_gt fun h => hov ((UScalar.lt_iff_val _ _).mpr h)
            have hsum_le : pend.val + count.val ≤ core.num.U64.MAX.val := by
              rw [hv_cap] at hle_cap
              have h1 := Nat.add_le_add_left hle_cap pend.val
              rwa [Nat.add_sub_of_le hp_le_max] at h1
            have hsum_lt64 : pend.val + count.val < 2 ^ 64 :=
              Nat.lt_of_le_of_lt hsum_le core.num.U64.MAX.bv.isLt
            have hadd_ok : (pend + count : Result Std.U64) = .ok ⟨pend.bv + count.bv⟩ := by
              simp only [hAdd_uscalar_eq, hsum_lt64, ite_true]
            simp only [hov, ↓reduceIte] at hStep
            rw [hadd_ok, result_bind_ok, result_bind_ok, result_bind_ok] at hStep
            dsimp only at hStep
            injection hStep with hAcc
            injection hAcc with hm' ho
            rw [decide_eq_true hsum_le]
            simp only [↓reduceIte]
            exact ⟨hm', ho⟩
      | RecordCheckResult checkOk =>
        dsimp only at hStep ⊢
        unfold pants_and_quorum_guards.VerifiedRssPoisonLatch.record_check_result at hStep
        unfold pants_and_quorum_guards.poison_rss_latch at hStep
        cases checkOk
        · simp only [Bool.false_eq_true, ↓reduceIte,
            bind_eq_result_bind, result_bind_ok] at hStep
          cases hStep
        · simp only [Bool.false_eq_true, ↓reduceIte,
            bind_eq_result_bind, result_bind_ok] at hStep ⊢
          injection hStep with hAcc
          injection hAcc with hm' ho
          exact ⟨hm', ho⟩
      | AuthorizeOpen =>
        dsimp only at hStep ⊢
        unfold pants_and_quorum_guards.VerifiedRssPoisonLatch.authorize_open at hStep
        unfold pants_and_quorum_guards.poison_rss_latch at hStep
        cases unv
        · by_cases hp0 : pend = 0#u64
          · simp only [hp0, bne_self_eq_false, Bool.false_eq_true,
              Bool.not_false, decide_true, Bool.and_self, ↓reduceIte,
              bind_eq_result_bind, result_bind_ok] at hStep ⊢
            injection hStep with hAcc
            injection hAcc with hm' ho
            exact ⟨hm', ho⟩
          · have hne : (pend != 0#u64) = true := bne_iff_ne.mpr hp0
            simp only [hne, ↓reduceIte,
              bind_eq_result_bind, result_bind_ok] at hStep
            cases hStep
        · simp only [Bool.false_eq_true, ↓reduceIte,
            bind_eq_result_bind, result_bind_ok] at hStep
          cases hStep
    · cases i_m
      · dsimp only [pants_and_quorum_guards.VerifiedRssPoisonLatch.stage_relations,
          pants_and_quorum_guards.poison_rss_latch] at hStep
        simp only [↓reduceIte, bind_eq_result_bind, result_bind_ok] at hStep
        cases hStep
      · dsimp only [pants_and_quorum_guards.VerifiedRssPoisonLatch.record_check_result,
          pants_and_quorum_guards.poison_rss_latch] at hStep
        simp only [↓reduceIte, bind_eq_result_bind, result_bind_ok] at hStep
        cases hStep
      · dsimp only [pants_and_quorum_guards.VerifiedRssPoisonLatch.authorize_open,
          pants_and_quorum_guards.poison_rss_latch] at hStep
        simp only [↓reduceIte, bind_eq_result_bind, result_bind_ok] at hStep
        cases hStep
  err_preserves {s m m' i_s i_m e} hSt hIn hStep := by
    subst m; dsimp only [id] at hIn; subst i_s
    rcases s with ⟨pend, unv, pois⟩
    dsimp only [adaptStateResult] at hStep
    unfold pants_and_quorum_guards.VerifiedRssPoisonLatch.step at hStep
    dsimp only [rssPoisonMealy, purePoisonRss]
    cases pois
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases i_m with
      | StageRelations count =>
        dsimp only at hStep ⊢
        unfold pants_and_quorum_guards.VerifiedRssPoisonLatch.stage_relations at hStep
        unfold pants_and_quorum_guards.poison_rss_latch at hStep
        simp only [Bool.false_eq_true, ↓reduceIte] at hStep
        by_cases hc0 : count = 0#u64
        · simp only [hc0, decide_true, ↓reduceIte, bind_eq_result_bind, result_bind_ok] at hStep ⊢
          injection hStep with hRej
          injection hRej with hm' _
          exact ⟨trivial, hm'⟩
        · simp only [hc0, decide_false, Bool.false_eq_true, ↓reduceIte,
            bind_eq_result_bind] at hStep ⊢
          have hp_le_max : pend.val ≤ core.num.U64.MAX.val := u64_val_le_max pend
          let cap : Std.U64 := ⟨core.num.U64.MAX.bv - pend.bv⟩
          have hsub : (core.num.U64.MAX - pend : Result Std.U64) = .ok cap := by
            simp only [hSub_uscalar_eq, hp_le_max, ite_true]; rfl
          have hv_cap : cap.val = core.num.U64.MAX.val - pend.val := by
            change (core.num.U64.MAX.bv - pend.bv).toNat = _
            exact BitVec.toNat_sub_of_le (BitVec.le_def.mpr hp_le_max)
          rw [hsub, result_bind_ok] at hStep
          by_cases hov : count > cap
          · have hgt : cap.val < count.val := (UScalar.lt_iff_val _ _).mp hov
            have hnle_sum : ¬ (pend.val + count.val ≤ core.num.U64.MAX.val) := by
              intro hle_sum
              have hle_c : count.val ≤ core.num.U64.MAX.val - pend.val :=
                Nat.le_sub_of_add_le (by rwa [Nat.add_comm] at hle_sum)
              rw [← hv_cap] at hle_c
              exact Nat.not_lt_of_ge hle_c hgt
            simp only [hov, ↓reduceIte, result_bind_ok] at hStep
            injection hStep with hRej
            injection hRej with hm' _
            rw [decide_eq_false hnle_sum]
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact ⟨trivial, hm'⟩
          · have hle_cap : count.val ≤ cap.val :=
              Nat.le_of_not_gt fun h => hov ((UScalar.lt_iff_val _ _).mpr h)
            have hsum_le : pend.val + count.val ≤ core.num.U64.MAX.val := by
              rw [hv_cap] at hle_cap
              have h1 := Nat.add_le_add_left hle_cap pend.val
              rwa [Nat.add_sub_of_le hp_le_max] at h1
            have hsum_lt64 : pend.val + count.val < 2 ^ 64 :=
              Nat.lt_of_le_of_lt hsum_le core.num.U64.MAX.bv.isLt
            have hadd_ok : (pend + count : Result Std.U64) = .ok ⟨pend.bv + count.bv⟩ := by
              simp only [hAdd_uscalar_eq, hsum_lt64, ite_true]
            simp only [hov, ↓reduceIte] at hStep
            rw [hadd_ok, result_bind_ok, result_bind_ok, result_bind_ok] at hStep
            cases hStep
      | RecordCheckResult checkOk =>
        dsimp only at hStep ⊢
        unfold pants_and_quorum_guards.VerifiedRssPoisonLatch.record_check_result at hStep
        unfold pants_and_quorum_guards.poison_rss_latch at hStep
        cases checkOk
        · simp only [Bool.false_eq_true, ↓reduceIte,
            bind_eq_result_bind, result_bind_ok] at hStep ⊢
          injection hStep with hRej
          injection hRej with hm' _
          exact ⟨trivial, hm'⟩
        · simp only [Bool.false_eq_true, ↓reduceIte,
            bind_eq_result_bind, result_bind_ok] at hStep
          cases hStep
      | AuthorizeOpen =>
        dsimp only at hStep ⊢
        unfold pants_and_quorum_guards.VerifiedRssPoisonLatch.authorize_open at hStep
        unfold pants_and_quorum_guards.poison_rss_latch at hStep
        cases unv
        · by_cases hp0 : pend = 0#u64
          · simp only [hp0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
              bind_eq_result_bind, result_bind_ok] at hStep
            cases hStep
          · have hne : (pend != 0#u64) = true := bne_iff_ne.mpr hp0
            simp only [hne, Bool.false_eq_true, Bool.not_false,
              decide_eq_false hp0, Bool.and_false, ↓reduceIte,
              bind_eq_result_bind, result_bind_ok] at hStep ⊢
            injection hStep with hRej
            injection hRej with hm' _
            exact ⟨trivial, hm'⟩
        · simp only [Bool.false_eq_true, Bool.not_true, Bool.false_and,
            ↓reduceIte, bind_eq_result_bind, result_bind_ok] at hStep ⊢
          injection hStep with hRej
          injection hRej with hm' _
          exact ⟨trivial, hm'⟩
    · simp only [↓reduceIte]
      cases i_m
      · dsimp only [pants_and_quorum_guards.VerifiedRssPoisonLatch.stage_relations,
          pants_and_quorum_guards.poison_rss_latch] at hStep
        simp only [↓reduceIte, bind_eq_result_bind, result_bind_ok] at hStep
        injection hStep with hRej
        injection hRej with hm' _
        exact ⟨trivial, hm'⟩
      · dsimp only [pants_and_quorum_guards.VerifiedRssPoisonLatch.record_check_result,
          pants_and_quorum_guards.poison_rss_latch] at hStep
        simp only [↓reduceIte, bind_eq_result_bind, result_bind_ok] at hStep
        injection hStep with hRej
        injection hRej with hm' _
        exact ⟨trivial, hm'⟩
      · dsimp only [pants_and_quorum_guards.VerifiedRssPoisonLatch.authorize_open,
          pants_and_quorum_guards.poison_rss_latch] at hStep
        simp only [↓reduceIte, bind_eq_result_bind, result_bind_ok] at hStep
        injection hStep with hRej
        injection hRej with hm' _
        exact ⟨trivial, hm'⟩

private theorem rss_poisoned_trace_nil_and_sticky
    {st s_f : pants_and_quorum_guards.VerifiedRssPoisonLatch}
    {pairs : List (pants_and_quorum_guards.RssLatchStepInput ×
      pants_and_quorum_guards.RssLatchStepOutput)}
    (hPois : st.poisoned = true)
    (hTr : rssPoisonMealy.ValidTrace st pairs s_f) :
    pairs = [] ∧ s_f.poisoned = true := by
  induction hTr with
  | nil _ => exact ⟨rfl, hPois⟩
  | @accept sa _ _ _ _ _ hStep _ _ =>
    dsimp only [rssPoisonMealy] at hStep
    rw [hPois] at hStep; cases hStep
  | @reject sa _ _ _ _ _ ih =>
    dsimp only [rssPoisonMealy, purePoisonRss] at ih
    rw [hPois] at ih
    simp only [↓reduceIte] at ih
    exact ih trivial

/-- **Sticky Terminal Verification-Failure Theorem (`rss_poison_latch_failed_check_permanently_blocks_open_mir`):**
    Once `VerifiedRssPoisonLatch::record_check_result(st0, false)` runs, `poisoned` is latched
    `true` BEFORE clearing `pending_relations = 0`, and **NO subsequent call sequence**
    (including calling `RecordCheckResult true` on `pending_relations == 0`!) can EVER emit
    any accepted transition or return `Ok` from `authorize_open()`. -/
theorem rss_poison_latch_failed_check_permanently_blocks_open_mir
    (st0 st1 st_final : pants_and_quorum_guards.VerifiedRssPoisonLatch)
    (res1 : core.result.Result Unit pants_and_quorum_guards.PantsGuardError)
    (turns : List (MirTurn pants_and_quorum_guards.RssLatchStepInput
      pants_and_quorum_guards.RssLatchStepOutput
      pants_and_quorum_guards.PantsGuardError))
    (hFail : pants_and_quorum_guards.VerifiedRssPoisonLatch.record_check_result st0 false =
      .ok (st1, res1))
    (hTrace : MirTrace (adaptStateResult pants_and_quorum_guards.VerifiedRssPoisonLatch.step)
      st1 turns st_final) :
    st1.poisoned = true ∧
    st1.pending_relations = 0#u64 ∧
    st_final.poisoned = true ∧
    mirAcceptedPairs turns = [] ∧
    pants_and_quorum_guards.VerifiedRssPoisonLatch.authorize_open st_final =
      .ok ({ pending_relations := 0#u64, unverified := true, poisoned := true },
        .Err .RssEnginePoisoned) := by
  have hSt1 : st1 = { pending_relations := 0#u64, unverified := true, poisoned := true } := by
    unfold pants_and_quorum_guards.VerifiedRssPoisonLatch.record_check_result at hFail
    unfold pants_and_quorum_guards.poison_rss_latch at hFail
    cases hp0 : st0.poisoned <;>
    simp [hp0, bind_eq_result_bind, result_bind_ok] at hFail <;>
    exact hFail.1.symm
  have hPois1 : st1.poisoned = true := by rw [hSt1]
  have hPend1 : st1.pending_relations = 0#u64 := by rw [hSt1]
  have hInputs :=
    (show InputsMatchTurns (fun a b => a = id b) (turns.map (fun t => id t.input)) turns from by
      clear hTrace
      induction turns with
      | nil => exact .nil
      | cons _ rest ih => exact .cons rfl ih)
  obtain ⟨hVal, hRelF, hPairs⟩ := rss_poison_latch_step_sim.lift_runInputs rfl hTrace hInputs
  obtain ⟨hNil, hPoisF⟩ := rss_poisoned_trace_nil_and_sticky hPois1 hVal
  subst hRelF
  rw [hNil] at hPairs
  refine ⟨hPois1, hPend1, hPoisF, acceptedPairsRel_nil_eq hPairs, ?_⟩
  unfold pants_and_quorum_guards.VerifiedRssPoisonLatch.authorize_open
  unfold pants_and_quorum_guards.poison_rss_latch
  rw [hPoisF]
  simp only [↓reduceIte, bind_eq_result_bind, result_bind_ok]

private theorem rss_clean_validTrace_sound
    {st s_f : pants_and_quorum_guards.VerifiedRssPoisonLatch}
    {pairs : List (pants_and_quorum_guards.RssLatchStepInput ×
      pants_and_quorum_guards.RssLatchStepOutput)}
    (hTr : rssPoisonMealy.ValidTrace st pairs s_f) :
    (∀ p ∈ pairs, ∀ perm, p.2 = .OpenAuthorized perm → perm.verified_clean = true) ∧
    (∀ pre suf perm,
      pairs = pre ++ (.AuthorizeOpen, .OpenAuthorized perm) :: suf →
      (st.unverified = false ∧ st.pending_relations = 0#u64 ∧
        ∀ q ∈ pre, ∀ c n, q ≠ (.StageRelations c, .RelationsStaged n)) ∨
      ∃ pre1 pre2, pre = pre1 ++ (.RecordCheckResult true, .CheckVerified) :: pre2 ∧
        ∀ q ∈ pre2, ∀ c n, q ≠ (.StageRelations c, .RelationsStaged n)) := by
  induction hTr with
  | nil _ =>
    refine ⟨fun _ hm => False.elim (List.not_mem_nil hm), ?_⟩
    intro pre _ _ heq
    cases pre <;> cases heq
  | @accept sa sb _ inp out rest hStep _ ih =>
    dsimp only [rssPoisonMealy] at hStep
    cases hp : sa.poisoned
    · rw [hp] at hStep
      simp only [Bool.false_eq_true, ↓reduceIte] at hStep
      cases inp with
      | StageRelations count =>
        dsimp only at hStep
        by_cases hc0 : count = 0#u64
        · simp only [hc0, decide_true, ↓reduceIte] at hStep; cases hStep
        · simp only [hc0, decide_false, Bool.false_eq_true, ↓reduceIte] at hStep
          by_cases hle : sa.pending_relations.val + count.val ≤ core.num.U64.MAX.val
          · simp only [hle, decide_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hStep
            rcases hStep with ⟨hsb, hout⟩
            subst hsb; subst hout
            obtain ⟨hPermTail, hBarrierTail⟩ := ih
            refine ⟨?_, ?_⟩
            · intro p hmem perm hperm
              simp only [List.mem_cons] at hmem
              rcases hmem with rfl | hm
              · cases hperm
              · exact hPermTail p hm perm hperm
            · intro pre suf perm heq
              cases pre with
              | nil => cases heq
              | cons hd tl =>
                injection heq with hhd htl
                rcases hBarrierTail tl suf perm htl with ⟨hu_f, _, _⟩ | ⟨p1, p2, hp_eq, hno_stg⟩
                · cases hu_f
                · exact Or.inr ⟨hd :: p1, p2, by rw [hp_eq]; rfl, hno_stg⟩
          · rw [decide_eq_false hle] at hStep
            simp only [Bool.false_eq_true, ↓reduceIte] at hStep; cases hStep
      | RecordCheckResult checkOk =>
        dsimp only at hStep
        cases checkOk with
        | false => simp only [Bool.false_eq_true, ↓reduceIte] at hStep; cases hStep
        | true =>
          simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hStep
          rcases hStep with ⟨hsb, hout⟩
          subst hsb; subst hout
          obtain ⟨hPermTail, hBarrierTail⟩ := ih
          refine ⟨?_, ?_⟩
          · intro p hmem perm hperm
            simp only [List.mem_cons] at hmem
            rcases hmem with rfl | hm
            · cases hperm
            · exact hPermTail p hm perm hperm
          · intro pre suf perm heq
            cases pre with
            | nil => cases heq
            | cons hd tl =>
              injection heq with hhd htl
              subst hhd
              rcases hBarrierTail tl suf perm htl with ⟨_, _, hno_stg0⟩ | ⟨p1, p2, hp_eq, hno_stg⟩
              · exact Or.inr ⟨[], tl, rfl, hno_stg0⟩
              · exact Or.inr ⟨(.RecordCheckResult true, .CheckVerified) :: p1, p2,
                  by rw [hp_eq]; rfl, hno_stg⟩
      | AuthorizeOpen =>
        dsimp only at hStep
        cases hu : sa.unverified
        · by_cases hp0 : sa.pending_relations = 0#u64
          · simp only [hu, Bool.not_false, hp0, decide_true, Bool.and_self, ↓reduceIte,
              Option.some.injEq, Prod.mk.injEq] at hStep
            rcases hStep with ⟨hsb, hout⟩
            subst hsb; subst hout
            obtain ⟨hPermTail, hBarrierTail⟩ := ih
            refine ⟨?_, ?_⟩
            · intro p hmem perm hperm
              simp only [List.mem_cons] at hmem
              rcases hmem with rfl | hm
              · injection hperm with hp_eq; subst hp_eq; rfl
              · exact hPermTail p hm perm hperm
            · intro pre suf perm heq
              cases pre with
              | nil =>
                exact Or.inl ⟨rfl, hp0, fun _ hm => False.elim (List.not_mem_nil hm)⟩
              | cons hd tl =>
                injection heq with hhd htl
                subst hhd
                rcases hBarrierTail tl suf perm htl with ⟨_, _, hno_stg0⟩ | ⟨p1, p2, hp_eq, hno_stg⟩
                · refine Or.inl ⟨rfl, hp0, ?_⟩
                  intro q hq c n
                  simp only [List.mem_cons] at hq
                  rcases hq with rfl | hq_tl
                  · intro hbad; cases hbad
                  · exact hno_stg0 q hq_tl c n
                · exact Or.inr ⟨(.AuthorizeOpen, .OpenAuthorized { verified_clean := true }) :: p1,
                    p2, by rw [hp_eq]; rfl, hno_stg⟩
          · simp only [hu, Bool.not_false, decide_eq_false hp0, Bool.and_false,
              Bool.false_eq_true, ↓reduceIte] at hStep
            cases hStep
        · simp only [hu, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hStep
          cases hStep
    · rw [hp] at hStep; cases hStep
  | @reject sa _ inp _ _ hTail ih =>
    dsimp only [rssPoisonMealy, purePoisonRss] at hTail
    cases hp : sa.poisoned
    · rw [hp] at hTail
      simp only [Bool.false_eq_true, ↓reduceIte] at hTail
      cases inp with
      | StageRelations count =>
        dsimp only at hTail
        by_cases hc0 : count = 0#u64
        · have hErr : rssPoisonMealy.errStep sa (.StageRelations count) = sa := by
            dsimp only [rssPoisonMealy]; simp only [hp, Bool.false_eq_true, hc0, decide_true, ↓reduceIte]
          rw [hErr] at ih
          exact ih
        · simp only [hc0, decide_false, Bool.false_eq_true, ↓reduceIte] at hTail
          obtain ⟨hNil, _⟩ := rss_poisoned_trace_nil_and_sticky rfl hTail
          subst hNil
          exact ⟨fun _ hm => False.elim (List.not_mem_nil hm),
            fun pre _ _ heq => by cases pre <;> cases heq⟩
      | RecordCheckResult _ =>
        dsimp only at hTail
        obtain ⟨hNil, _⟩ := rss_poisoned_trace_nil_and_sticky rfl hTail
        subst hNil
        exact ⟨fun _ hm => False.elim (List.not_mem_nil hm),
          fun pre _ _ heq => by cases pre <;> cases heq⟩
      | AuthorizeOpen =>
        have hErr : rssPoisonMealy.errStep sa .AuthorizeOpen = sa := by
          dsimp only [rssPoisonMealy]; simp only [hp, Bool.false_eq_true, ↓reduceIte]
        rw [hErr] at ih
        exact ih
    · rw [hp] at hTail
      simp only [↓reduceIte] at hTail
      obtain ⟨hNil, _⟩ := rss_poisoned_trace_nil_and_sticky rfl hTail
      subst hNil
      exact ⟨fun _ hm => False.elim (List.not_mem_nil hm),
        fun pre _ _ heq => by cases pre <;> cases heq⟩

/-- **Multi-Turn Verification-Barrier Soundness for `VerifiedRssPoisonLatch`:**
    Starting from `new_clean`, across ANY multi-turn `MirTrace`:
    1. Every `OpenAuthorized` permit has `verified_clean = true`;
    2. Whenever `AuthorizeOpen` succeeds after any `StageRelations` batch, a `RecordCheckResult true`
       barrier MUST have succeeded after the most recent `StageRelations` batch (and zero failed
       checks occurred anywhere earlier in the trace). -/
theorem rss_poison_latch_multiturn_sound
    (st0 st_final : pants_and_quorum_guards.VerifiedRssPoisonLatch)
    (turns : List (MirTurn pants_and_quorum_guards.RssLatchStepInput
      pants_and_quorum_guards.RssLatchStepOutput
      pants_and_quorum_guards.PantsGuardError))
    (hNew : pants_and_quorum_guards.VerifiedRssPoisonLatch.new_clean = .ok st0)
    (hTrace : MirTrace (adaptStateResult pants_and_quorum_guards.VerifiedRssPoisonLatch.step)
      st0 turns st_final) :
    st0.poisoned = false ∧
    (∀ p ∈ mirAcceptedPairs turns, ∀ perm,
      p.2 = .OpenAuthorized perm → perm.verified_clean = true) ∧
    (∀ pre suf perm,
      mirAcceptedPairs turns = pre ++ (.AuthorizeOpen, .OpenAuthorized perm) :: suf →
      (∀ q ∈ pre, ∀ c n, q ≠ (.StageRelations c, .RelationsStaged n)) ∨
      ∃ pre1 pre2, pre = pre1 ++ (.RecordCheckResult true, .CheckVerified) :: pre2 ∧
        ∀ q ∈ pre2, ∀ c n, q ≠ (.StageRelations c, .RelationsStaged n)) := by
  unfold pants_and_quorum_guards.VerifiedRssPoisonLatch.new_clean at hNew
  simp only [Result.ok.injEq] at hNew
  have hPois0 : st0.poisoned = false := by rw [← hNew]
  obtain ⟨hSafe, _⟩ :=
    rss_poison_latch_step_sim.lift_trace_safety_abs
      (Safe := fun pairs =>
        (∀ p ∈ pairs, ∀ perm, p.2 = .OpenAuthorized perm → perm.verified_clean = true) ∧
        (∀ pre suf perm,
          pairs = pre ++ (.AuthorizeOpen, .OpenAuthorized perm) :: suf →
          (∀ q ∈ pre, ∀ c n, q ≠ (.StageRelations c, .RelationsStaged n)) ∨
          ∃ pre1 pre2, pre = pre1 ++ (.RecordCheckResult true, .CheckVerified) :: pre2 ∧
            ∀ q ∈ pre2, ∀ c n, q ≠ (.StageRelations c, .RelationsStaged n)))
      (fun hVal => by
        obtain ⟨h1, h2⟩ := rss_clean_validTrace_sound hVal
        refine ⟨h1, ?_⟩
        intro pre suf perm heq
        rcases h2 pre suf perm heq with ⟨_, _, hno⟩ | hok
        · exact Or.inl hno
        · exact Or.inr hok)
      rfl
      hTrace
  rw [map_id_pair_pants] at hSafe
  exact ⟨hPois0, hSafe⟩

/-! ## 4. `VerifiedWaistbandRootGuard` (Static Ancestor Child-Root & First-Signed Guard) -/

/-- Pure Mealy specification of `VerifiedWaistbandRootGuard::authorize_ancestor_derivation`:
    requires exact coordinate `(layer, tree, kp)`, `(cache_pk_tag == key_pk_tag)`,
    `(cache_params_tag == key_params_tag)`, `(recomputed_child_root == expected_static_child_root)`,
    and durable first-signed `locked_ancestor_codeword_tag` consistency; any mismatch fails closed
    and permanently sets `poisoned = true`. -/
@[expose]
def waistbandRootMealy :
    MealySpec
      pants_and_quorum_guards.VerifiedWaistbandRootGuard
      pants_and_quorum_guards.WaistbandDerivationRequest
      pants_and_quorum_guards.WaistbandAncestorPermit where
  step st req :=
    if st.poisoned then none
    else if decide (req.req_layer = st.ancestor_layer) &&
        decide (req.req_tree = st.ancestor_tree) &&
        decide (req.req_kp = st.ancestor_kp) &&
        decide (req.cache_pk_tag = st.key_pk_tag) &&
        decide (req.cache_params_tag = st.key_params_tag) &&
        decide (req.recomputed_child_root = st.expected_static_child_root) &&
        (!st.has_locked_codeword ||
          decide (req.candidate_ancestor_codeword_tag = st.locked_ancestor_codeword_tag)) then
      some ({ st with
        has_locked_codeword := true
        locked_ancestor_codeword_tag := req.candidate_ancestor_codeword_tag },
        { layer := st.ancestor_layer
          tree := st.ancestor_tree
          kp := st.ancestor_kp
          verified_child_root := st.expected_static_child_root
          authorized_codeword_tag := req.candidate_ancestor_codeword_tag })
    else none
  errStep st _ := { st with poisoned := true }

private abbrev waistbandInnerPassBool
    (st : pants_and_quorum_guards.VerifiedWaistbandRootGuard)
    (req : pants_and_quorum_guards.WaistbandDerivationRequest) : Bool :=
  decide (req.req_layer = st.ancestor_layer) &&
  decide (req.req_tree = st.ancestor_tree) &&
  decide (req.req_kp = st.ancestor_kp) &&
  decide (req.cache_pk_tag = st.key_pk_tag) &&
  decide (req.cache_params_tag = st.key_params_tag) &&
  decide (req.recomputed_child_root = st.expected_static_child_root) &&
  (!st.has_locked_codeword ||
    decide (req.candidate_ancestor_codeword_tag = st.locked_ancestor_codeword_tag))

private theorem waistband_authorize_exact
    (st : pants_and_quorum_guards.VerifiedWaistbandRootGuard)
    (req : pants_and_quorum_guards.WaistbandDerivationRequest) :
    (st.poisoned = false ∧ waistbandInnerPassBool st req = true →
      pants_and_quorum_guards.VerifiedWaistbandRootGuard.authorize_ancestor_derivation st req =
        .ok ({ st with
          has_locked_codeword := true
          locked_ancestor_codeword_tag := req.candidate_ancestor_codeword_tag },
          .Ok {
            layer := st.ancestor_layer
            tree := st.ancestor_tree
            kp := st.ancestor_kp
            verified_child_root := st.expected_static_child_root
            authorized_codeword_tag := req.candidate_ancestor_codeword_tag })) ∧
    (st.poisoned = true ∨ waistbandInnerPassBool st req = false →
      ∃ e,
        pants_and_quorum_guards.VerifiedWaistbandRootGuard.authorize_ancestor_derivation st req =
          .ok ({ st with poisoned := true }, .Err e)) := by
  rcases st with ⟨key_pk, key_par, anc_lay, anc_tr, anc_kp, exp_root, has_lk, lk_cw, poisoned⟩
  unfold pants_and_quorum_guards.VerifiedWaistbandRootGuard.authorize_ancestor_derivation
  unfold pants_and_quorum_guards.poison_waistband_guard
  dsimp only [waistbandInnerPassBool]
  cases poisoned
  · simp only [Bool.false_eq_true, ↓reduceIte, false_or, true_and]
    by_cases hlay : req.req_layer = anc_lay
    · simp only [hlay, bne_self_eq_false, Bool.false_eq_true, decide_true, Bool.true_and, ↓reduceIte]
      by_cases htr : req.req_tree = anc_tr
      · simp only [htr, bne_self_eq_false, Bool.false_eq_true, decide_true, Bool.true_and, ↓reduceIte]
        by_cases hkp : req.req_kp = anc_kp
        · simp only [hkp, bne_self_eq_false, Bool.false_eq_true, decide_true, Bool.true_and, ↓reduceIte]
          rw [bind_eq_result_bind, ct_eq_bytes32_spec, result_bind_ok]
          by_cases hpk : req.cache_pk_tag = key_pk
          · have hpk_d : decide (req.cache_pk_tag = key_pk) = true := decide_eq_true hpk
            rw [hpk_d]
            simp only [Bool.true_and, ↓reduceIte]
            rw [bind_eq_result_bind, ct_eq_bytes32_spec, result_bind_ok]
            by_cases hpar : req.cache_params_tag = key_par
            · have hpar_d : decide (req.cache_params_tag = key_par) = true := decide_eq_true hpar
              rw [hpar_d]
              simp only [Bool.true_and, ↓reduceIte]
              rw [bind_eq_result_bind, ct_eq_bytes32_spec, result_bind_ok]
              by_cases hrt : req.recomputed_child_root = exp_root
              · have hrt_d : decide (req.recomputed_child_root = exp_root) = true := decide_eq_true hrt
                rw [hrt_d]
                simp only [Bool.true_and, ↓reduceIte]
                cases has_lk
                · simp only [Bool.not_false, Bool.true_or, Bool.false_eq_true, ↓reduceIte]
                  exact ⟨fun _ => trivial, Bool.noConfusion⟩
                · simp only [Bool.not_true, Bool.false_or, ↓reduceIte]
                  rw [bind_eq_result_bind, ct_eq_bytes32_spec, result_bind_ok]
                  by_cases hcw : req.candidate_ancestor_codeword_tag = lk_cw
                  · have hcw_d : decide (req.candidate_ancestor_codeword_tag = lk_cw) = true :=
                      decide_eq_true hcw
                    rw [hcw_d]
                    simp only [↓reduceIte]
                    exact ⟨fun _ => trivial, Bool.noConfusion⟩
                  · have hcw_d : decide (req.candidate_ancestor_codeword_tag = lk_cw) = false :=
                      decide_eq_false hcw
                    rw [hcw_d]
                    simp only [Bool.false_eq_true, ↓reduceIte, bind_eq_result_bind, result_bind_ok]
                    exact ⟨False.elim, fun _ => ⟨_, rfl⟩⟩
              · have hrt_d : decide (req.recomputed_child_root = exp_root) = false :=
                  decide_eq_false hrt
                rw [hrt_d]
                simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, bind_eq_result_bind,
                  result_bind_ok]
                exact ⟨False.elim, fun _ => ⟨_, rfl⟩⟩
            · have hpar_d : decide (req.cache_params_tag = key_par) = false := decide_eq_false hpar
              rw [hpar_d]
              simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, bind_eq_result_bind,
                result_bind_ok]
              exact ⟨False.elim, fun _ => ⟨_, rfl⟩⟩
          · have hpk_d : decide (req.cache_pk_tag = key_pk) = false := decide_eq_false hpk
            rw [hpk_d]
            simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, bind_eq_result_bind,
              result_bind_ok]
            exact ⟨False.elim, fun _ => ⟨_, rfl⟩⟩
        · have hne : (req.req_kp != anc_kp) = true := bne_iff_ne.mpr hkp
          have hd : decide (req.req_kp = anc_kp) = false := decide_eq_false hkp
          rw [hne, hd]
          simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, bind_eq_result_bind, result_bind_ok]
          exact ⟨False.elim, fun _ => ⟨_, rfl⟩⟩
      · have hne : (req.req_tree != anc_tr) = true := bne_iff_ne.mpr htr
        have hd : decide (req.req_tree = anc_tr) = false := decide_eq_false htr
        rw [hne, hd]
        simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, bind_eq_result_bind, result_bind_ok]
        exact ⟨False.elim, fun _ => ⟨_, rfl⟩⟩
    · have hne : (req.req_layer != anc_lay) = true := bne_iff_ne.mpr hlay
      have hd : decide (req.req_layer = anc_lay) = false := decide_eq_false hlay
      rw [hne, hd]
      simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, bind_eq_result_bind, result_bind_ok]
      exact ⟨False.elim, fun _ => ⟨_, rfl⟩⟩
  · simp only [↓reduceIte, Bool.true_eq_false, false_and, true_or, bind_eq_result_bind, result_bind_ok]
    exact ⟨False.elim, fun _ => ⟨_, rfl⟩⟩

/-- Constructive single-step `MirStepSim` simulation from extracted Rust MIR
    `VerifiedWaistbandRootGuard::authorize_ancestor_derivation` to `waistbandRootMealy`. -/
theorem waistband_root_guard_step_sim :
    MirStepSim waistbandRootMealy
      (adaptStateResult pants_and_quorum_guards.VerifiedWaistbandRootGuard.authorize_ancestor_derivation)
      Eq (fun a b => a = id b) (fun a b => a = id b) where
  ok_sim {s m m' i_s i_m o_m} hSt hIn hStep := by
    subst m; dsimp only [id] at hIn; subst i_s
    dsimp only [adaptStateResult] at hStep
    obtain ⟨hPass, hFail⟩ := waistband_authorize_exact s i_m
    dsimp only [waistbandRootMealy]
    rcases (by cases s.poisoned <;> simp : s.poisoned = false ∨ s.poisoned = true) with hp | hp
    · by_cases hb : waistbandInnerPassBool s i_m = true
      · have hok := hPass ⟨hp, hb⟩
        rw [hok, result_bind_ok] at hStep
        injection hStep with hAcc
        cases hAcc
        dsimp only [waistbandInnerPassBool] at hb
        rw [hp, hb]
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact ⟨trivial, rfl⟩
      · simp only [Bool.not_eq_true] at hb
        obtain ⟨err, herr⟩ := hFail (Or.inr hb)
        rw [herr, result_bind_ok] at hStep
        cases hStep
    · obtain ⟨err, herr⟩ := hFail (Or.inl hp)
      rw [herr, result_bind_ok] at hStep
      cases hStep
  err_preserves {s m m' i_s i_m e} hSt hIn hStep := by
    subst m; dsimp only [id] at hIn; subst i_s
    dsimp only [adaptStateResult] at hStep
    obtain ⟨hPass, hFail⟩ := waistband_authorize_exact s i_m
    dsimp only [waistbandRootMealy]
    rcases (by cases s.poisoned <;> simp : s.poisoned = false ∨ s.poisoned = true) with hp | hp
    · by_cases hb : waistbandInnerPassBool s i_m = true
      · have hok := hPass ⟨hp, hb⟩
        rw [hok, result_bind_ok] at hStep
        cases hStep
      · simp only [Bool.not_eq_true] at hb
        obtain ⟨err, herr⟩ := hFail (Or.inr hb)
        rw [herr, result_bind_ok] at hStep
        injection hStep with hRej
        injection hRej with hm' _
        dsimp only [waistbandInnerPassBool] at hb
        rw [hp, hb]
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact ⟨trivial, hm'⟩
    · obtain ⟨err, herr⟩ := hFail (Or.inl hp)
      rw [herr, result_bind_ok] at hStep
      injection hStep with hRej
      injection hRej with hm' _
      rw [hp]
      simp only [↓reduceIte]
      exact ⟨trivial, hm'⟩

private theorem waistband_poisoned_nil
    {st s_f : pants_and_quorum_guards.VerifiedWaistbandRootGuard}
    {pairs : List (pants_and_quorum_guards.WaistbandDerivationRequest ×
      pants_and_quorum_guards.WaistbandAncestorPermit)}
    (hPois : st.poisoned = true)
    (hTr : waistbandRootMealy.ValidTrace st pairs s_f) :
    pairs = [] ∧ s_f.poisoned = true := by
  induction hTr with
  | nil _ => exact ⟨rfl, hPois⟩
  | @accept sa _ _ _ _ _ hStep _ _ =>
    dsimp only [waistbandRootMealy] at hStep
    rw [hPois] at hStep; cases hStep
  | @reject sa _ _ _ _ _ ih =>
    dsimp only [waistbandRootMealy] at ih
    exact ih rfl

private theorem waistband_locked_trace_sound
    {pkTag paramsTag childRoot lockedCw : Array Std.U8 32#usize}
    {layer : Std.U32} {tree : Std.U64} {kp : Std.U32}
    {st s_f : pants_and_quorum_guards.VerifiedWaistbandRootGuard}
    {pairs : List (pants_and_quorum_guards.WaistbandDerivationRequest ×
      pants_and_quorum_guards.WaistbandAncestorPermit)}
    (hSt : st.key_pk_tag = pkTag ∧ st.key_params_tag = paramsTag ∧
      st.ancestor_layer = layer ∧ st.ancestor_tree = tree ∧ st.ancestor_kp = kp ∧
      st.expected_static_child_root = childRoot ∧
      st.has_locked_codeword = true ∧ st.locked_ancestor_codeword_tag = lockedCw)
    (hTr : waistbandRootMealy.ValidTrace st pairs s_f) :
    ∀ p ∈ pairs,
      p.1.req_layer = layer ∧
      p.1.req_tree = tree ∧
      p.1.req_kp = kp ∧
      p.1.cache_pk_tag = pkTag ∧
      p.1.cache_params_tag = paramsTag ∧
      p.1.recomputed_child_root = childRoot ∧
      p.1.candidate_ancestor_codeword_tag = lockedCw ∧
      p.2 = {
        layer := layer
        tree := tree
        kp := kp
        verified_child_root := childRoot
        authorized_codeword_tag := lockedCw } := by
  induction hTr with
  | nil _ =>
    intro _ hm; exact False.elim (List.not_mem_nil hm)
  | @accept sa sb _ req out rest hStep _ ih =>
    rcases hSt with ⟨hpk, hpar, hlay, htr, hkp, hrt, hlk, hcw⟩
    dsimp only [waistbandRootMealy] at hStep
    cases hp : sa.poisoned
    · rw [hp, hpk, hpar, hlay, htr, hkp, hrt, hlk, hcw] at hStep
      simp only [Bool.false_eq_true, Bool.not_true, Bool.false_or, ↓reduceIte] at hStep
      by_cases hcond :
          (decide (req.req_layer = layer) &&
           decide (req.req_tree = tree) &&
           decide (req.req_kp = kp) &&
           decide (req.cache_pk_tag = pkTag) &&
           decide (req.cache_params_tag = paramsTag) &&
           decide (req.recomputed_child_root = childRoot) &&
           decide (req.candidate_ancestor_codeword_tag = lockedCw)) = true
      · rw [hcond] at hStep
        simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hStep
        rcases hStep with ⟨hsb, hout⟩
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        rcases hcond with ⟨⟨⟨⟨⟨⟨rlay, rtr⟩, rkp⟩, rpk⟩, rpar⟩, rrt⟩, rcw⟩
        subst hsb; subst hout
        intro p hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with rfl | hm
        · exact ⟨rlay, rtr, rkp, rpk, rpar, rrt, rcw,
            by rw [rcw]⟩
        · exact ih ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rcw⟩ p hm
      · simp only [Bool.not_eq_true] at hcond
        rw [hcond] at hStep; cases hStep
    · rw [hp] at hStep; cases hStep
  | @reject sa _ _ _ _ hTail _ =>
    obtain ⟨hNil, _⟩ := waistband_poisoned_nil rfl hTail
    subst hNil
    intro _ hm; exact False.elim (List.not_mem_nil hm)

/-- **Master Multi-Turn Soundness Theorem for `VerifiedWaistbandRootGuard`:**
    Starting from `new_enrolled`, across ANY multi-turn `MirTrace`:
    1. Mismatched `cache_pk_tag`, mismatched `cache_params_tag`, mismatched coordinate
       `(layer, tree, kp)`, or corrupted intermediate `recomputed_child_root` NEVER yields
       an `Ok` permit (every accepted request matches all enrolled tags and `expected_static_child_root`);
    2. **First-Signed Codeword Uniqueness:** all accepted permits across the entire trace
       authorize the exact same `authorized_codeword_tag` (equivocating on a second ancestor
       codeword fails closed and poisons the guard). -/
theorem waistband_root_guard_multiturn_sound
    (pkTag paramsTag expectedChildRoot : Array Std.U8 32#usize)
    (layer : Std.U32) (tree : Std.U64) (kp : Std.U32)
    (st0 st_final : pants_and_quorum_guards.VerifiedWaistbandRootGuard)
    (turns : List (MirTurn pants_and_quorum_guards.WaistbandDerivationRequest
      pants_and_quorum_guards.WaistbandAncestorPermit
      pants_and_quorum_guards.PantsGuardError))
    (hNew : pants_and_quorum_guards.VerifiedWaistbandRootGuard.new_enrolled
      pkTag paramsTag layer tree kp expectedChildRoot = .ok st0)
    (hTrace : MirTrace
      (adaptStateResult pants_and_quorum_guards.VerifiedWaistbandRootGuard.authorize_ancestor_derivation)
      st0 turns st_final) :
    (∀ p ∈ mirAcceptedPairs turns,
      p.1.req_layer = layer ∧
      p.1.req_tree = tree ∧
      p.1.req_kp = kp ∧
      p.1.cache_pk_tag = pkTag ∧
      p.1.cache_params_tag = paramsTag ∧
      p.1.recomputed_child_root = expectedChildRoot ∧
      p.2.verified_child_root = expectedChildRoot ∧
      p.2.authorized_codeword_tag = p.1.candidate_ancestor_codeword_tag) ∧
    (∀ p1 ∈ mirAcceptedPairs turns, ∀ p2 ∈ mirAcceptedPairs turns,
      p1.2.authorized_codeword_tag = p2.2.authorized_codeword_tag) := by
  unfold pants_and_quorum_guards.VerifiedWaistbandRootGuard.new_enrolled at hNew
  simp only [Result.ok.injEq] at hNew
  obtain ⟨hSafe, _⟩ :=
    waistband_root_guard_step_sim.lift_trace_safety_abs
      (Safe := fun pairs =>
        (∀ p ∈ pairs,
          p.1.req_layer = layer ∧
          p.1.req_tree = tree ∧
          p.1.req_kp = kp ∧
          p.1.cache_pk_tag = pkTag ∧
          p.1.cache_params_tag = paramsTag ∧
          p.1.recomputed_child_root = expectedChildRoot ∧
          p.2.verified_child_root = expectedChildRoot ∧
          p.2.authorized_codeword_tag = p.1.candidate_ancestor_codeword_tag) ∧
        (∀ p1 ∈ pairs, ∀ p2 ∈ pairs,
          p1.2.authorized_codeword_tag = p2.2.authorized_codeword_tag))
      (fun {pairs s_f} hVal => by
        generalize hs0 : st0 = s_init at hVal
        rw [← hNew] at hs0
        cases hVal with
        | nil _ =>
          exact ⟨fun _ hm => False.elim (List.not_mem_nil hm),
            fun _ hm => False.elim (List.not_mem_nil hm)⟩
        | @accept sa sb _ req out rest hStep hTail =>
          subst hs0
          dsimp only [waistbandRootMealy] at hStep
          simp only [Bool.false_eq_true, Bool.not_false, Bool.true_or, Bool.and_true,
            ↓reduceIte] at hStep
          by_cases hcond :
              (decide (req.req_layer = layer) &&
               decide (req.req_tree = tree) &&
               decide (req.req_kp = kp) &&
               decide (req.cache_pk_tag = pkTag) &&
               decide (req.cache_params_tag = paramsTag) &&
               decide (req.recomputed_child_root = expectedChildRoot)) = true
          · rw [hcond] at hStep
            simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hStep
            rcases hStep with ⟨hsb, hout⟩
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
            rcases hcond with ⟨⟨⟨⟨⟨rlay, rtr⟩, rkp⟩, rpk⟩, rpar⟩, rrt⟩
            subst hsb; subst hout
            have hTailProps := waistband_locked_trace_sound
              ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hTail
            have hAllCw : ∀ p ∈ (req, {
                layer := layer, tree := tree, kp := kp,
                verified_child_root := expectedChildRoot,
                authorized_codeword_tag := req.candidate_ancestor_codeword_tag
              }) :: rest,
                p.2.authorized_codeword_tag = req.candidate_ancestor_codeword_tag := by
              intro p hp
              simp only [List.mem_cons] at hp
              rcases hp with rfl | hm
              · rfl
              · rw [(hTailProps p hm).2.2.2.2.2.2.2]
            refine ⟨?_, ?_⟩
            · intro p hp
              simp only [List.mem_cons] at hp
              rcases hp with rfl | hm
              · exact ⟨rlay, rtr, rkp, rpk, rpar, rrt, rfl, rfl⟩
              · obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ := hTailProps p hm
                rw [t8]
                exact ⟨t1, t2, t3, t4, t5, t6, rfl, t7.symm⟩
            · intro p1 hp1 p2 hp2
              rw [hAllCw p1 hp1, hAllCw p2 hp2]
          · simp only [Bool.not_eq_true] at hcond
            rw [hcond] at hStep; cases hStep
        | @reject sa _ _ _ _ hTail =>
          subst hs0
          obtain ⟨hNil, _⟩ := waistband_poisoned_nil rfl hTail
          subst hNil
          exact ⟨fun _ hm => False.elim (List.not_mem_nil hm),
            fun _ hm => False.elim (List.not_mem_nil hm)⟩)
      rfl
      hTrace
  rw [map_id_pair_pants] at hSafe
  exact hSafe

/-- Direct fail-closed refusal theorem for `VerifiedWaistbandRootGuard`: any mismatch in
    `cache_pk_tag`, `cache_params_tag`, `recomputed_child_root`, or coordinate `(layer, tree, kp)`
    immediately refuses derivation and latches `poisoned = true`. -/
theorem waistband_mismatch_fails_closed_mir
    (st : pants_and_quorum_guards.VerifiedWaistbandRootGuard)
    (req : pants_and_quorum_guards.WaistbandDerivationRequest)
    (hMismatch :
      req.cache_pk_tag ≠ st.key_pk_tag ∨
      req.cache_params_tag ≠ st.key_params_tag ∨
      req.recomputed_child_root ≠ st.expected_static_child_root ∨
      req.req_layer ≠ st.ancestor_layer ∨
      req.req_tree ≠ st.ancestor_tree ∨
      req.req_kp ≠ st.ancestor_kp) :
    ∃ e, pants_and_quorum_guards.VerifiedWaistbandRootGuard.authorize_ancestor_derivation st req =
      .ok ({ st with poisoned := true }, .Err e) := by
  apply (waistband_authorize_exact st req).2
  right
  dsimp only [waistbandInnerPassBool]
  rcases hMismatch with h | h | h | h | h | h
  · rw [decide_eq_false h]; simp only [Bool.and_false, Bool.false_and]
  · rw [decide_eq_false h]; simp only [Bool.and_false, Bool.false_and]
  · rw [decide_eq_false h]; simp only [Bool.and_false, Bool.false_and]
  · rw [decide_eq_false h]; simp only [Bool.false_and]
  · rw [decide_eq_false h]; simp only [Bool.and_false, Bool.false_and]
  · rw [decide_eq_false h]; simp only [Bool.and_false, Bool.false_and]

/-! ## 5. `#tooth` Mutation-Sensitivity & Non-Vacuity Witnesses (`0 Classical.choice`) -/

/-- `#tooth` witness 1: Under-threshold `q = 2` for `(n=5, t=3, f=2)` (`2*q = 4 ≤ 7`) and
    global-liveness-violating `q = 4 > n - f = 3` are BOTH rejected, while BFT-safe
    `(n=7, t=3, f=2, q=5, global_liveness=true)` (`2*q = 10 > 9` and `q = 5 ≤ 7 - 2`) is accepted. -/
theorem tooth_belt_under_threshold_quorum_rejected :
    pants_and_quorum_guards.validate_belt_quorum_config 5#u32 3#u32 2#u32 2#u32 false = .ok false ∧
    pants_and_quorum_guards.validate_belt_quorum_config 5#u32 3#u32 2#u32 4#u32 true = .ok false ∧
    pants_and_quorum_guards.validate_belt_quorum_config 7#u32 3#u32 2#u32 5#u32 true = .ok true := by
  simp only [validate_belt_quorum_config_eq]
  refine ⟨congrArg Result.ok (by decide), congrArg Result.ok (by decide),
    congrArg Result.ok (by decide)⟩

/-- `#tooth` witness 2: WAL sync failure (`wal_sync_ok = false`) and conflicting `(epoch, msg_tag)`
    equivocation permanently latch `poisoned = true` and reject subsequent valid calls. -/
private theorem array_repeat32_val (c : Std.U8) :
    (Array.repeat 32#usize c).val = List.replicate 32 c := rfl

private theorem array_repeat32_ne {x y : Std.U8} (hne : x ≠ y) :
    Array.repeat 32#usize x ≠ Array.repeat 32#usize y := by
  intro h
  have hval : List.replicate 32 x = List.replicate 32 y := by
    rw [← array_repeat32_val x, ← array_repeat32_val y, h]
  exact hne (congrArg (fun l => l.getD 0 0#u8) hval)

private theorem list_getD_replicate_u8 (c d : Std.U8) :
    ∀ (n i : Nat), i < n → (List.replicate n c).getD i d = c
  | 0, _, hi => False.elim (Nat.not_lt_zero _ hi)
  | _ + 1, 0, _ => rfl
  | n + 1, i + 1, hi => list_getD_replicate_u8 c d n i (Nat.lt_of_succ_lt_succ hi)

private theorem pureWotsC256Digit_repeat32 (c : Std.U8) (k : Nat) (hk : k < 128) :
    pureWotsC256Digit (Array.repeat 32#usize c) k =
      (c.val / (2 ^ (6 - 2 * (k % 4)))) % 4 := by
  have hq : k / 4 < 32 := (Nat.div_lt_iff_lt_mul (by decide)).mpr hk
  unfold pureWotsC256Digit
  rw [array_repeat32_val, list_getD_replicate_u8 c 0#u8 32 (k / 4) hq]

private theorem natPrefixSum_repeat32_quads (c : Std.U8) :
    ∀ m, m ≤ 32 →
      natPrefixSum (pureWotsC256Digit (Array.repeat 32#usize c)) (4 * m) =
        m * ((c.val / 64) % 4 + (c.val / 16) % 4 + (c.val / 4) % 4 + c.val % 4)
  | 0, _ => (Nat.zero_mul _).symm
  | m + 1, hm => by
    have h4le : 4 * m + 4 ≤ 128 := by
      rw [← Nat.mul_succ]
      exact Nat.mul_le_mul_left 4 hm
    have hk0 : 4 * m < 128 :=
      Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 4)) h4le
    have hk1 : 4 * m + 1 < 128 :=
      Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by decide : 1 < 4) (4 * m)) h4le
    have hk2 : 4 * m + 2 < 128 :=
      Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by decide : 2 < 4) (4 * m)) h4le
    have hk3 : 4 * m + 3 < 128 :=
      Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by decide : 3 < 4) (4 * m)) h4le
    have hr0 : (4 * m) % 4 = 0 := Nat.mul_mod_right 4 m
    have hr1 : (4 * m + 1) % 4 = 1 := by rw [Nat.add_comm, Nat.add_mul_mod_self_left]
    have hr2 : (4 * m + 2) % 4 = 2 := by rw [Nat.add_comm, Nat.add_mul_mod_self_left]
    have hr3 : (4 * m + 3) % 4 = 3 := by rw [Nat.add_comm, Nat.add_mul_mod_self_left]
    rw [Nat.mul_succ 4 m]
    dsimp only [natPrefixSum]
    rw [natPrefixSum_repeat32_quads c m (Nat.le_of_lt hm),
      pureWotsC256Digit_repeat32 c (4 * m) hk0,
      pureWotsC256Digit_repeat32 c (4 * m + 1) hk1,
      pureWotsC256Digit_repeat32 c (4 * m + 2) hk2,
      pureWotsC256Digit_repeat32 c (4 * m + 3) hk3,
      hr0, hr1, hr2, hr3]
    change m * ((c.val / 64) % 4 + (c.val / 16) % 4 + (c.val / 4) % 4 + c.val % 4) +
        (c.val / 64) % 4 + (c.val / 16) % 4 + (c.val / 4) % 4 + (c.val / 1) % 4 =
      (m + 1) * ((c.val / 64) % 4 + (c.val / 16) % 4 + (c.val / 4) % 4 + c.val % 4)
    rw [Nat.div_one, Nat.succ_mul]
    simp only [Nat.add_assoc]

theorem tooth_belt_wal_and_conflict_poison :
    let tagA := Array.repeat 32#usize 0x41#u8
    let tagB := Array.repeat 32#usize 0x42#u8
    (∃ st0 st1 st2,
      pants_and_quorum_guards.BeltQuorumCore.new_validated
        3#u32 2#u32 1#u32 3#u32 false 10#u64 4#u64 = .ok (.Ok st0) ∧
      pants_and_quorum_guards.BeltQuorumCore.propose_or_retry_epoch
        st0 10#u64 tagA false = .ok (st1, .Err .BeltWalSyncFailed) ∧
      st1.poisoned = true ∧
      pants_and_quorum_guards.BeltQuorumCore.propose_or_retry_epoch
        st1 10#u64 tagA true = .ok (st2, .Err .BeltGuardPoisoned)) ∧
    (∃ st0 st1 st2,
      pants_and_quorum_guards.BeltQuorumCore.new_validated
        3#u32 2#u32 1#u32 3#u32 false 10#u64 4#u64 = .ok (.Ok st0) ∧
      pants_and_quorum_guards.BeltQuorumCore.propose_or_retry_epoch
        st0 10#u64 tagA true = .ok (st1, .Ok ()) ∧
      pants_and_quorum_guards.BeltQuorumCore.propose_or_retry_epoch
        st1 10#u64 tagB true = .ok (st2, .Err .ConflictingEpochMsgTag) ∧
      st2.poisoned = true) := by
  dsimp only
  let zero32 := Array.repeat 32#usize 0#u8
  let tagA := Array.repeat 32#usize 0x41#u8
  let tagB := Array.repeat 32#usize 0x42#u8
  let st0 : pants_and_quorum_guards.BeltQuorumCore := {
    n := 3#u32, t := 2#u32, f := 1#u32, q := 3#u32,
    global_liveness_mode := false, next_epoch := 10#u64, max_jump_window := 4#u64,
    phase := .Idle, has_bound_epoch := false, bound_epoch := 0#u64,
    bound_msg_tag := zero32, ack_count := 0#u32, poisoned := false
  }
  let stPois0 : pants_and_quorum_guards.BeltQuorumCore :=
    { st0 with phase := .Poisoned, ack_count := 0#u32, poisoned := true }
  let stBound : pants_and_quorum_guards.BeltQuorumCore := {
    n := 3#u32, t := 2#u32, f := 1#u32, q := 3#u32,
    global_liveness_mode := false, next_epoch := 11#u64, max_jump_window := 4#u64,
    phase := .EpochBoundPendingQuorum, has_bound_epoch := true, bound_epoch := 10#u64,
    bound_msg_tag := tagA, ack_count := 0#u32, poisoned := false
  }
  let stPoisB : pants_and_quorum_guards.BeltQuorumCore :=
    { stBound with phase := .Poisoned, ack_count := 0#u32, poisoned := true }
  have hNew : pants_and_quorum_guards.BeltQuorumCore.new_validated
      3#u32 2#u32 1#u32 3#u32 false 10#u64 4#u64 = .ok (.Ok st0) := by
    unfold pants_and_quorum_guards.BeltQuorumCore.new_validated
    rw [validate_belt_quorum_config_eq]; rfl
  constructor
  · refine ⟨st0, stPois0, stPois0, hNew, ?_, rfl, ?_⟩
    · unfold pants_and_quorum_guards.BeltQuorumCore.propose_or_retry_epoch
      unfold pants_and_quorum_guards.poison_belt_guard
      dsimp only [st0, stPois0]
      rw [validate_belt_quorum_config_eq]; rfl
    · unfold pants_and_quorum_guards.BeltQuorumCore.propose_or_retry_epoch
      unfold pants_and_quorum_guards.poison_belt_guard
      rfl
  · refine ⟨st0, stBound, stPoisB, hNew, ?_, ?_, rfl⟩
    · unfold pants_and_quorum_guards.BeltQuorumCore.propose_or_retry_epoch
      dsimp only [st0, stBound]
      rw [validate_belt_quorum_config_eq]
      have hne10 : ¬ (10#u64 = core.num.U64.MAX) := by
        intro h; have hv : (10#u64).val = 2 ^ 64 - 1 := by rw [h, u64_max_val]
        exact absurd hv (by decide)
      simp only [Bool.false_eq_true, ↓reduceIte, bind_eq_result_bind, result_bind_ok,
        (by decide : ¬ (10#u64 < 10#u64)), hSub_uscalar_eq, Nat.le_refl,
        (by decide : ¬ ((⟨(10#u64).bv - (10#u64).bv⟩ : Std.U64) > 4#u64)),
        hne10, hAdd_uscalar_eq, (by decide : (10#u64).val + (1#u64).val < 2 ^ 64)]
      rfl
    · unfold pants_and_quorum_guards.BeltQuorumCore.propose_or_retry_epoch
      unfold pants_and_quorum_guards.poison_belt_guard
      dsimp only [stBound, stPoisB, tagA, tagB]
      rw [validate_belt_quorum_config_eq]
      simp only [Bool.false_eq_true, (by decide : ¬ (10#u64 ≥ 11#u64)), ↓reduceIte,
        bind_eq_result_bind, result_bind_ok]
      rw [ct_eq_bytes32_spec, result_bind_ok, decide_eq_false (array_repeat32_ne (by decide))]
      rfl

/-- Inhabitedness witness for `belt_quorum_guard_multiturn_sound`: a complete 5-turn `MirTrace`
    binding epoch `12` via bounded jump `10 → 12`, recording 3 custodian acks, and reaching
    `SharesAuthorized`. -/
theorem inhabited_belt_quorum_trace :
    ∃ st0 stF turns grant,
      pants_and_quorum_guards.BeltQuorumCore.new_validated
        3#u32 2#u32 1#u32 3#u32 false 10#u64 4#u64 = .ok (.Ok st0) ∧
      MirTrace (adaptStateResult pants_and_quorum_guards.BeltQuorumCore.step)
        st0 turns stF ∧
      (.AuthorizeShares 12#u64 (Array.repeat 32#usize 0x41#u8), .SharesAuthorized grant) ∈
        mirAcceptedPairs turns ∧
      grant.authorized_epoch = 12#u64 ∧
      grant.certified_acks = 3#u32 := by
  let tag := Array.repeat 32#usize 0x41#u8
  let st0 : pants_and_quorum_guards.BeltQuorumCore := {
    n := 3#u32, t := 2#u32, f := 1#u32, q := 3#u32,
    global_liveness_mode := false, next_epoch := 10#u64, max_jump_window := 4#u64,
    phase := .Idle, has_bound_epoch := false, bound_epoch := 0#u64,
    bound_msg_tag := Array.repeat 32#usize 0#u8, ack_count := 0#u32, poisoned := false
  }
  let st1 : pants_and_quorum_guards.BeltQuorumCore := {
    n := 3#u32, t := 2#u32, f := 1#u32, q := 3#u32,
    global_liveness_mode := false, next_epoch := 13#u64, max_jump_window := 4#u64,
    phase := .EpochBoundPendingQuorum, has_bound_epoch := true, bound_epoch := 12#u64,
    bound_msg_tag := tag, ack_count := 0#u32, poisoned := false
  }
  let st2 := { st1 with ack_count := 1#u32 }
  let st3 := { st1 with ack_count := 2#u32 }
  let st4 := { st1 with ack_count := 3#u32 }
  let st5 := { st4 with phase := .SharesAuthorized }
  let grant : pants_and_quorum_guards.BeltAuthorizationGrant :=
    { authorized_epoch := 12#u64, msg_tag := tag, certified_acks := 3#u32 }
  have hNew : pants_and_quorum_guards.BeltQuorumCore.new_validated
      3#u32 2#u32 1#u32 3#u32 false 10#u64 4#u64 = .ok (.Ok st0) := by
    unfold pants_and_quorum_guards.BeltQuorumCore.new_validated
    rw [validate_belt_quorum_config_eq]; rfl
  have htag_eq : tower.ct_eq_bytes32 tag tag = .ok true := by
    rw [ct_eq_bytes32_spec, decide_eq_true rfl]
  have hs1 : adaptStateResult pants_and_quorum_guards.BeltQuorumCore.step
      st0 (.ProposeOrRetryEpoch 12#u64 tag true) = .ok (.accepted st1 .EpochBound) := by
    have hne12 : ¬ (12#u64 = core.num.U64.MAX) := by
      intro h; have hv : (12#u64).val = 2 ^ 64 - 1 := by rw [h, u64_max_val]
      exact absurd hv (by decide)
    unfold adaptStateResult pants_and_quorum_guards.BeltQuorumCore.step
      pants_and_quorum_guards.BeltQuorumCore.propose_or_retry_epoch
    dsimp only [st0, st1]
    rw [validate_belt_quorum_config_eq]
    simp only [Bool.false_eq_true, ↓reduceIte, bind_eq_result_bind, result_bind_ok,
      (by decide : ¬ (12#u64 < 10#u64)), hSub_uscalar_eq,
      (by decide : (10#u64).val ≤ (12#u64).val),
      (by decide : ¬ ((⟨(12#u64).bv - (10#u64).bv⟩ : Std.U64) > 4#u64)),
      hne12, hAdd_uscalar_eq, (by decide : (12#u64).val + (1#u64).val < 2 ^ 64)]
    rfl
  have hs2 : adaptStateResult pants_and_quorum_guards.BeltQuorumCore.step
      st1 (.RecordCustodianAck 12#u64 tag) = .ok (.accepted st2 (.AckRecorded 1#u32)) := by
    unfold adaptStateResult pants_and_quorum_guards.BeltQuorumCore.step
      pants_and_quorum_guards.BeltQuorumCore.record_custodian_ack
    dsimp only [st1, st2]
    rw [validate_belt_quorum_config_eq]
    simp only [Bool.false_eq_true, ↓reduceIte, bind_eq_result_bind, result_bind_ok,
      (by decide : ¬ (12#u64 ≥ 13#u64)), bne_self_eq_false, htag_eq,
      (by decide : ¬ (0#u32 ≥ 3#u32)), hAdd_uscalar_eq,
      (by decide : (0#u32).val + (1#u32).val < 2 ^ 32)]
    rfl
  have hs3 : adaptStateResult pants_and_quorum_guards.BeltQuorumCore.step
      st2 (.RecordCustodianAck 12#u64 tag) = .ok (.accepted st3 (.AckRecorded 2#u32)) := by
    unfold adaptStateResult pants_and_quorum_guards.BeltQuorumCore.step
      pants_and_quorum_guards.BeltQuorumCore.record_custodian_ack
    dsimp only [st1, st2, st3]
    rw [validate_belt_quorum_config_eq]
    simp only [Bool.false_eq_true, ↓reduceIte, bind_eq_result_bind, result_bind_ok,
      (by decide : ¬ (12#u64 ≥ 13#u64)), bne_self_eq_false, htag_eq,
      (by decide : ¬ (1#u32 ≥ 3#u32)), hAdd_uscalar_eq,
      (by decide : (1#u32).val + (1#u32).val < 2 ^ 32)]
    rfl
  have hs4 : adaptStateResult pants_and_quorum_guards.BeltQuorumCore.step
      st3 (.RecordCustodianAck 12#u64 tag) = .ok (.accepted st4 (.AckRecorded 3#u32)) := by
    unfold adaptStateResult pants_and_quorum_guards.BeltQuorumCore.step
      pants_and_quorum_guards.BeltQuorumCore.record_custodian_ack
    dsimp only [st1, st3, st4]
    rw [validate_belt_quorum_config_eq]
    simp only [Bool.false_eq_true, ↓reduceIte, bind_eq_result_bind, result_bind_ok,
      (by decide : ¬ (12#u64 ≥ 13#u64)), bne_self_eq_false, htag_eq,
      (by decide : ¬ (2#u32 ≥ 3#u32)), hAdd_uscalar_eq,
      (by decide : (2#u32).val + (1#u32).val < 2 ^ 32)]
    rfl
  have hs5 : adaptStateResult pants_and_quorum_guards.BeltQuorumCore.step
      st4 (.AuthorizeShares 12#u64 tag) = .ok (.accepted st5 (.SharesAuthorized grant)) := by
    unfold adaptStateResult pants_and_quorum_guards.BeltQuorumCore.step
      pants_and_quorum_guards.BeltQuorumCore.authorize_shares
    dsimp only [st1, st4, st5, grant]
    rw [validate_belt_quorum_config_eq]
    simp only [Bool.false_eq_true, ↓reduceIte, bind_eq_result_bind, result_bind_ok,
      (by decide : ¬ (12#u64 ≥ 13#u64)), bne_self_eq_false, htag_eq,
      (by decide : ¬ (3#u32 < 3#u32))]
    rfl
  refine ⟨st0, st5, _, grant, hNew,
    .accept hs1 (.accept hs2 (.accept hs3 (.accept hs4 (.accept hs5 (.nil st5))))),
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self)))), rfl, rfl⟩

/-- `#tooth` & non-vacuity witness 3 (`WOTS+C` 256-bit `w=4, v=128, S=192`):
    `[0x99; 32]` (`[2,1,2,1]` per byte → `6 * 32 = 192`) is accepted by extracted MIR
    `verified_wotsc256_verify_sum`, while `[0x00; 32]` (`S = 0`) and `[0xFF; 32]` (`S = 384`)
    are both rejected. -/
theorem tooth_wotsc256_wrong_sum_rejected_and_inhabited :
    pants_and_quorum_guards.verified_wotsc256_verify_sum (Array.repeat 32#usize 0x99#u8) =
      .ok true ∧
    pants_and_quorum_guards.verified_wotsc256_verify_sum (Array.repeat 32#usize 0x00#u8) =
      .ok false ∧
    pants_and_quorum_guards.verified_wotsc256_verify_sum (Array.repeat 32#usize 0xFF#u8) =
      .ok false := by
  rw [verified_wotsc256_verify_sum_eq, verified_wotsc256_verify_sum_eq,
    verified_wotsc256_verify_sum_eq]
  have h128 : ∀ c : Std.U8,
      natPrefixSum (pureWotsC256Digit (Array.repeat 32#usize c)) 128 =
        32 * ((c.val / 64) % 4 + (c.val / 16) % 4 + (c.val / 4) % 4 + c.val % 4) :=
    fun c => natPrefixSum_repeat32_quads c 32 (Nat.le_refl 32)
  refine ⟨congrArg Result.ok ?_, congrArg Result.ok ?_, congrArg Result.ok ?_⟩ <;>
    (rw [h128]; decide)

/-- `#tooth` witness 4 (`VerifiedRssPoisonLatch`): after `stage_relations(64)` and a failed
    check `record_check_result(false)` (which clears `pending_relations = 0` AFTER setting
    `poisoned = true`), BOTH a subsequent `record_check_result(true)` AND `authorize_open()`
    are rejected with `RssEnginePoisoned`. -/
theorem tooth_rss_failed_check_then_true_check_blocks_open :
    ∃ st0 st1 st2 st3 st4,
      pants_and_quorum_guards.VerifiedRssPoisonLatch.new_clean = .ok st0 ∧
      pants_and_quorum_guards.VerifiedRssPoisonLatch.stage_relations st0 64#u64 =
        .ok (st1, .Ok 64#u64) ∧
      pants_and_quorum_guards.VerifiedRssPoisonLatch.record_check_result st1 false =
        .ok (st2, .Err .RssVerificationCheckFailed) ∧
      st2.pending_relations = 0#u64 ∧
      st2.poisoned = true ∧
      pants_and_quorum_guards.VerifiedRssPoisonLatch.record_check_result st2 true =
        .ok (st3, .Err .RssEnginePoisoned) ∧
      pants_and_quorum_guards.VerifiedRssPoisonLatch.authorize_open st3 =
        .ok (st4, .Err .RssEnginePoisoned) := by
  let st0 : pants_and_quorum_guards.VerifiedRssPoisonLatch :=
    { pending_relations := 0#u64, unverified := false, poisoned := false }
  let st1 : pants_and_quorum_guards.VerifiedRssPoisonLatch :=
    { pending_relations := 64#u64, unverified := true, poisoned := false }
  let stPois : pants_and_quorum_guards.VerifiedRssPoisonLatch :=
    { pending_relations := 0#u64, unverified := true, poisoned := true }
  have hStage : pants_and_quorum_guards.VerifiedRssPoisonLatch.stage_relations st0 64#u64 =
      .ok (st1, .Ok 64#u64) := by
    have hsub0 : (core.num.U64.MAX - 0#u64 : Result Std.U64) = .ok core.num.U64.MAX := by
      have hle0 : (0#u64).val ≤ core.num.U64.MAX.val := Nat.zero_le _
      simp only [hSub_uscalar_eq, hle0, ite_true]
      apply congrArg Result.ok
      exact UScalar.eq_of_val_eq (by
        change (core.num.U64.MAX.bv - (0#u64).bv).toNat = _
        rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle0)]
        exact Nat.sub_zero _)
    have hgt64 : ¬ (64#u64 > core.num.U64.MAX) :=
      fun h => Nat.not_lt_of_ge (u64_val_le_max 64#u64) ((UScalar.lt_iff_val _ _).mp h)
    unfold pants_and_quorum_guards.VerifiedRssPoisonLatch.stage_relations
    dsimp only [st0, st1]
    simp only [Bool.false_eq_true, (by decide : ¬ (64#u64 = 0#u64)), ↓reduceIte, bind_eq_result_bind]
    rw [hsub0, result_bind_ok]
    simp only [hgt64, ↓reduceIte, hAdd_uscalar_eq,
      (by decide : (0#u64).val + (64#u64).val < 2 ^ 64), result_bind_ok]
    rfl
  exact ⟨st0, st1, stPois, stPois, stPois, rfl, hStage, rfl, rfl, rfl, rfl, rfl⟩

/-- Inhabitedness witness for `VerifiedRssPoisonLatch`: clean `stage_relations(32) →
    record_check_result(true) → authorize_open()` multi-turn `MirTrace` succeeds. -/
theorem inhabited_rss_poison_latch_trace :
    ∃ st0 stF turns,
      pants_and_quorum_guards.VerifiedRssPoisonLatch.new_clean = .ok st0 ∧
      MirTrace (adaptStateResult pants_and_quorum_guards.VerifiedRssPoisonLatch.step)
        st0 turns stF ∧
      (.AuthorizeOpen, .OpenAuthorized { verified_clean := true }) ∈ mirAcceptedPairs turns := by
  let st0 : pants_and_quorum_guards.VerifiedRssPoisonLatch :=
    { pending_relations := 0#u64, unverified := false, poisoned := false }
  let st1 : pants_and_quorum_guards.VerifiedRssPoisonLatch :=
    { pending_relations := 32#u64, unverified := true, poisoned := false }
  have hs1 : adaptStateResult pants_and_quorum_guards.VerifiedRssPoisonLatch.step
      st0 (.StageRelations 32#u64) = .ok (.accepted st1 (.RelationsStaged 32#u64)) := by
    have hsub0 : (core.num.U64.MAX - 0#u64 : Result Std.U64) = .ok core.num.U64.MAX := by
      have hle0 : (0#u64).val ≤ core.num.U64.MAX.val := Nat.zero_le _
      simp only [hSub_uscalar_eq, hle0, ite_true]
      apply congrArg Result.ok
      exact UScalar.eq_of_val_eq (by
        change (core.num.U64.MAX.bv - (0#u64).bv).toNat = _
        rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle0)]
        exact Nat.sub_zero _)
    have hgt32 : ¬ (32#u64 > core.num.U64.MAX) :=
      fun h => Nat.not_lt_of_ge (u64_val_le_max 32#u64) ((UScalar.lt_iff_val _ _).mp h)
    unfold adaptStateResult pants_and_quorum_guards.VerifiedRssPoisonLatch.step
      pants_and_quorum_guards.VerifiedRssPoisonLatch.stage_relations
    dsimp only [st0, st1]
    simp only [Bool.false_eq_true, (by decide : ¬ (32#u64 = 0#u64)), ↓reduceIte, bind_eq_result_bind]
    rw [hsub0, result_bind_ok]
    simp only [hgt32, ↓reduceIte, hAdd_uscalar_eq,
      (by decide : (0#u64).val + (32#u64).val < 2 ^ 64), result_bind_ok]
    rfl
  have hs2 : adaptStateResult pants_and_quorum_guards.VerifiedRssPoisonLatch.step
      st1 (.RecordCheckResult true) = .ok (.accepted st0 .CheckVerified) := by
    rfl
  have hs3 : adaptStateResult pants_and_quorum_guards.VerifiedRssPoisonLatch.step
      st0 .AuthorizeOpen = .ok (.accepted st0 (.OpenAuthorized { verified_clean := true })) := by
    unfold adaptStateResult pants_and_quorum_guards.VerifiedRssPoisonLatch.step
      pants_and_quorum_guards.VerifiedRssPoisonLatch.authorize_open
    dsimp only [st0]
    simp only [Bool.false_eq_true, bne_self_eq_false, ↓reduceIte, bind_eq_result_bind, result_bind_ok]
  exact ⟨st0, st0, _, rfl, .accept hs1 (.accept hs2 (.accept hs3 (.nil st0))),
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))⟩

/-- `#tooth` & non-vacuity witness 5 (`VerifiedWaistbandRootGuard`):
    (a) corrupted intermediate `recomputed_child_root` fails closed with `WaistbandChildRootMismatch`,
    (b) honest ancestor derivation succeeds and locks the first codeword, and
    (c) attempting a second distinct ancestor codeword fails closed with `WaistbandCodewordEquivocation`. -/
theorem tooth_waistband_corrupted_root_and_second_codeword_fail_closed :
    let pk := Array.repeat 32#usize 0x11#u8
    let params := Array.repeat 32#usize 0x22#u8
    let goodRoot := Array.repeat 32#usize 0x33#u8
    let badRoot := Array.repeat 32#usize 0xFF#u8
    let cw1 := Array.repeat 32#usize 0x44#u8
    let cw2 := Array.repeat 32#usize 0x55#u8
    (∃ st0 stBad,
      pants_and_quorum_guards.VerifiedWaistbandRootGuard.new_enrolled
        pk params 3#u32 77#u64 5#u32 goodRoot = .ok st0 ∧
      pants_and_quorum_guards.VerifiedWaistbandRootGuard.authorize_ancestor_derivation st0
        { req_layer := 3#u32, req_tree := 77#u64, req_kp := 5#u32,
          cache_pk_tag := pk, cache_params_tag := params,
          recomputed_child_root := badRoot, candidate_ancestor_codeword_tag := cw1 } =
        .ok (stBad, .Err .WaistbandChildRootMismatch) ∧
      stBad.poisoned = true) ∧
    (∃ st0 st1 st2 permit,
      pants_and_quorum_guards.VerifiedWaistbandRootGuard.new_enrolled
        pk params 3#u32 77#u64 5#u32 goodRoot = .ok st0 ∧
      pants_and_quorum_guards.VerifiedWaistbandRootGuard.authorize_ancestor_derivation st0
        { req_layer := 3#u32, req_tree := 77#u64, req_kp := 5#u32,
          cache_pk_tag := pk, cache_params_tag := params,
          recomputed_child_root := goodRoot, candidate_ancestor_codeword_tag := cw1 } =
        .ok (st1, .Ok permit) ∧
      permit.verified_child_root = goodRoot ∧
      pants_and_quorum_guards.VerifiedWaistbandRootGuard.authorize_ancestor_derivation st1
        { req_layer := 3#u32, req_tree := 77#u64, req_kp := 5#u32,
          cache_pk_tag := pk, cache_params_tag := params,
          recomputed_child_root := goodRoot, candidate_ancestor_codeword_tag := cw2 } =
        .ok (st2, .Err .WaistbandCodewordEquivocation) ∧
      st2.poisoned = true) := by
  dsimp only
  let pk := Array.repeat 32#usize 0x11#u8
  let params := Array.repeat 32#usize 0x22#u8
  let goodRoot := Array.repeat 32#usize 0x33#u8
  let badRoot := Array.repeat 32#usize 0xFF#u8
  let cw1 := Array.repeat 32#usize 0x44#u8
  let cw2 := Array.repeat 32#usize 0x55#u8
  let st0 : pants_and_quorum_guards.VerifiedWaistbandRootGuard := {
    key_pk_tag := pk, key_params_tag := params,
    ancestor_layer := 3#u32, ancestor_tree := 77#u64, ancestor_kp := 5#u32,
    expected_static_child_root := goodRoot,
    has_locked_codeword := false,
    locked_ancestor_codeword_tag := Array.repeat 32#usize 0#u8,
    poisoned := false
  }
  let stBad := { st0 with poisoned := true }
  let st1 := { st0 with has_locked_codeword := true, locked_ancestor_codeword_tag := cw1 }
  let st2 := { st1 with poisoned := true }
  let permit : pants_and_quorum_guards.WaistbandAncestorPermit := {
    layer := 3#u32, tree := 77#u64, kp := 5#u32,
    verified_child_root := goodRoot, authorized_codeword_tag := cw1
  }
  have hpk_eq : ∀ c, tower.ct_eq_bytes32 (Array.repeat 32#usize c) (Array.repeat 32#usize c) = .ok true :=
    fun _ => by rw [ct_eq_bytes32_spec, decide_eq_true rfl]
  have hbad_ne : tower.ct_eq_bytes32 (Array.repeat 32#usize 0xFF#u8) (Array.repeat 32#usize 0x33#u8) = .ok false := by
    rw [ct_eq_bytes32_spec, decide_eq_false (array_repeat32_ne (by decide))]
  have hcw_ne : tower.ct_eq_bytes32 (Array.repeat 32#usize 0x55#u8) (Array.repeat 32#usize 0x44#u8) = .ok false := by
    rw [ct_eq_bytes32_spec, decide_eq_false (array_repeat32_ne (by decide))]
  constructor
  · refine ⟨st0, stBad, rfl, ?_, rfl⟩
    unfold pants_and_quorum_guards.VerifiedWaistbandRootGuard.authorize_ancestor_derivation
    unfold pants_and_quorum_guards.poison_waistband_guard
    dsimp only [st0, stBad, pk, params, goodRoot, badRoot, cw1]
    simp only [Bool.false_eq_true, bne_self_eq_false, ↓reduceIte,
      hpk_eq, hbad_ne, bind_eq_result_bind, result_bind_ok]
  · refine ⟨st0, st1, st2, permit, rfl, ?_, rfl, ?_, rfl⟩
    · unfold pants_and_quorum_guards.VerifiedWaistbandRootGuard.authorize_ancestor_derivation
      dsimp only [st0, st1, permit, pk, params, goodRoot, cw1]
      simp only [Bool.false_eq_true, bne_self_eq_false, ↓reduceIte,
        hpk_eq, bind_eq_result_bind, result_bind_ok]
    · unfold pants_and_quorum_guards.VerifiedWaistbandRootGuard.authorize_ancestor_derivation
      unfold pants_and_quorum_guards.poison_waistband_guard
      dsimp only [st0, st1, st2, pk, params, goodRoot, cw1, cw2]
      simp only [Bool.false_eq_true, bne_self_eq_false, ↓reduceIte,
        hpk_eq, hcw_ne, bind_eq_result_bind, result_bind_ok]


/-! ## Authenticated public Belt boundary
The preceding Belt transition lemmas concern the now-private `BeltQuorumCore`.
The public Rust API verifies per-custodian tags before entering that core.
These lemmas are about that newly extracted boundary, not a caller-provided MAC flag. -/

/-- Population count is specified independently as the number of set bit positions. -/
@[expose]
def BeltAckCountInvariant (st : authenticated_belt.VerifiedBeltQuorumGuard) : Prop :=
  st.inner.ack_count.val = (List.range 64).countP (fun i => st.ack_bitmap.bv.getLsbD i)

theorem authenticated_belt_initial_count_invariant
    (n t f q : Std.U32) (gl : Bool) (epoch window : Std.U64)
    (commit wal : Array Std.U8 32#usize) (keys : Array (Array Std.U8 32#usize) 64#usize)
    (st : authenticated_belt.VerifiedBeltQuorumGuard)
    (h : authenticated_belt.VerifiedBeltQuorumGuard.new_validated n t f q gl epoch window commit keys wal =
      .ok (core.result.Result.Ok st)) : BeltAckCountInvariant st := by
  by_cases hn : n > 64#u32
  · simp [authenticated_belt.VerifiedBeltQuorumGuard.new_validated, hn] at h
  · by_cases hv : validBeltQuorumConfigBool n t f q gl = true
    · simp [authenticated_belt.VerifiedBeltQuorumGuard.new_validated, hn,
        pants_and_quorum_guards.BeltQuorumCore.new_validated,
        validate_belt_quorum_config_eq, hv] at h
      cases h
      change (0#u32).val = (List.range 64).countP (fun i => (0#u64).bv.getLsbD i)
      decide
    · simp [authenticated_belt.VerifiedBeltQuorumGuard.new_validated, hn,
        pants_and_quorum_guards.BeltQuorumCore.new_validated,
        validate_belt_quorum_config_eq, hv] at h

theorem authenticated_belt_forged_tag_fails_closed
    (st : authenticated_belt.VerifiedBeltQuorumGuard)
    (epoch : Std.U64) (msg key expected forged : Array Std.U8 32#usize) (id : Std.U8)
    (hin : ¬ UScalar.cast .Usize id >= UScalar.cast .Usize st.inner.n)
    (h64 : ¬ id >= 64#u8)
    (hkey : Array.index_usize st.custodian_keys (UScalar.cast .Usize id) = .ok key)
    (htag : authenticated_belt.custodian_ack_tag key st.guard_key_commit epoch msg id = .ok expected)
    (hforged : expected ≠ forged) :
    authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack st epoch msg id forged =
      .ok (st, core.result.Result.Err authenticated_belt.BeltAuthError.InvalidCustodianTag) := by
  change ¬ (UScalar.cast .Usize st.inner.n).bv.toNat ≤ (UScalar.cast .Usize id).bv.toNat at hin
  simp [authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack,
    pants_and_quorum_guards.BeltQuorumCore.impl.n, hin, h64, hkey, htag,
    ct_eq_bytes32_spec, hforged]

theorem authenticated_belt_duplicate_ack_unchanged
    (st : authenticated_belt.VerifiedBeltQuorumGuard)
    (epoch : Std.U64) (msg key tag : Array Std.U8 32#usize) (id : Std.U8) (bit : Std.U64)
    (hin : ¬ UScalar.cast .Usize id >= UScalar.cast .Usize st.inner.n)
    (h64 : ¬ id >= 64#u8)
    (hkey : Array.index_usize st.custodian_keys (UScalar.cast .Usize id) = .ok key)
    (htag : authenticated_belt.custodian_ack_tag key st.guard_key_commit epoch msg id = .ok tag)
    (hp : st.inner.poisoned = false) (hb : st.inner.has_bound_epoch = true)
    (he : epoch = st.inner.bound_epoch) (hm : msg = st.inner.bound_msg_tag)
    (hbit : (1#u64 <<< id : Result Std.U64) = .ok bit)
    (hused : st.ack_bitmap &&& bit ≠ 0#u64) :
    authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack st epoch msg id tag =
      .ok (st, core.result.Result.Ok st.inner.ack_count) := by
  change ¬ (UScalar.cast .Usize st.inner.n).bv.toNat ≤ (UScalar.cast .Usize id).bv.toNat at hin
  subst epoch
  subst msg
  simp [authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack,
    pants_and_quorum_guards.BeltQuorumCore.impl.n,
    pants_and_quorum_guards.BeltQuorumCore.is_poisoned,
    pants_and_quorum_guards.BeltQuorumCore.impl.has_bound_epoch,
    pants_and_quorum_guards.BeltQuorumCore.impl.bound_epoch,
    pants_and_quorum_guards.BeltQuorumCore.impl.bound_msg_tag,
    pants_and_quorum_guards.BeltQuorumCore.impl.ack_count,
    hin, h64, hkey, htag, ct_eq_bytes32_spec, hp, hb, hbit, hused]

/-- Execute the actual MIR acknowledgment entrypoint repeatedly, retaining even rejected states. -/
@[expose]
def repeatCustodianAck (epoch : Std.U64) (msg tag : Array Std.U8 32#usize) (id : Std.U8) :
    Nat → authenticated_belt.VerifiedBeltQuorumGuard → Result authenticated_belt.VerifiedBeltQuorumGuard
  | 0, st => .ok st
  | n + 1, st => do
      let (next, _) ← authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack st epoch msg id tag
      repeatCustodianAck epoch msg tag id n next

theorem tooth_duplicate_custodian_cannot_reach_quorum
    (st : authenticated_belt.VerifiedBeltQuorumGuard)
    (epoch : Std.U64) (msg key tag : Array Std.U8 32#usize) (id : Std.U8) (bit : Std.U64)
    (hin : ¬ UScalar.cast .Usize id >= UScalar.cast .Usize st.inner.n)
    (h64 : ¬ id >= 64#u8)
    (hkey : Array.index_usize st.custodian_keys (UScalar.cast .Usize id) = .ok key)
    (htag : authenticated_belt.custodian_ack_tag key st.guard_key_commit epoch msg id = .ok tag)
    (hp : st.inner.poisoned = false) (hb : st.inner.has_bound_epoch = true)
    (he : epoch = st.inner.bound_epoch) (hm : msg = st.inner.bound_msg_tag)
    (hbit : (1#u64 <<< id : Result Std.U64) = .ok bit)
    (hused : st.ack_bitmap &&& bit ≠ 0#u64)
    (hone : st.inner.ack_count.val = 1) (hq : 2 ≤ st.inner.q.val) (calls : Nat) :
    repeatCustodianAck epoch msg tag id calls st = .ok st ∧ st.inner.ack_count.val < st.inner.q.val := by
  constructor
  · have hstep := authenticated_belt_duplicate_ack_unchanged st epoch msg key tag id bit
      hin h64 hkey htag hp hb he hm hbit hused
    induction calls with
    | zero => rfl
    | succ n ih => simp only [repeatCustodianAck, hstep, bind_eq_result_bind, result_bind_ok, ih]
  · omega

set_option maxHeartbeats 200000

private theorem result_bind_ok_iff {α β : Type} (x : Result α) (f : α → Result β) (b : β) :
    Result.bind x f = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [Result.bind]

private theorem result_bind_fail {α β : Type} (e : Error) (f : α → Result β) :
    Result.bind (.fail e) f = .fail e := rfl

private theorem result_bind_div {α β : Type} (f : α → Result β) :
    Result.bind .div f = .div := rfl

/-- Enrollment material is immutable at the authenticated boundary. -/
@[expose]
def BeltEnrollmentUnchanged (st st' : authenticated_belt.VerifiedBeltQuorumGuard) : Prop :=
  st'.guard_key_commit = st.guard_key_commit ∧
  st'.custodian_keys = st.custodian_keys ∧ st'.wal_key = st.wal_key

private theorem belt_propose_enrollment_unchanged
    (st st' : authenticated_belt.VerifiedBeltQuorumGuard)
    (ep : Std.U64) (msg digest tag : Array Std.U8 32#usize)
    (r : core.result.Result Unit authenticated_belt.BeltAuthError)
    (h : authenticated_belt.VerifiedBeltQuorumGuard.propose_or_retry_epoch st ep msg digest tag =
      .ok (st', r)) : BeltEnrollmentUnchanged st st' := by
  unfold authenticated_belt.VerifiedBeltQuorumGuard.propose_or_retry_epoch at h
  simp only [bind_eq_result_bind, result_bind_ok,
    pants_and_quorum_guards.BeltQuorumCore.impl.has_bound_epoch,
    pants_and_quorum_guards.BeltQuorumCore.impl.bound_epoch,
    pants_and_quorum_guards.BeltQuorumCore.is_poisoned] at h
  repeat (any_goals first
    | simp only [result_bind_ok_iff, reduceCtorEq, ↓reduceIte] at h
    | (obtain ⟨v, hv, h⟩ : ∃ v, _ ∧ _ := h)
    | (split at h))
  all_goals cases h <;> exact ⟨rfl, rfl, rfl⟩

private theorem belt_ack_enrollment_unchanged
    (st st' : authenticated_belt.VerifiedBeltQuorumGuard)
    (ep : Std.U64) (msg tag : Array Std.U8 32#usize) (id : Std.U8)
    (r : core.result.Result Std.U32 authenticated_belt.BeltAuthError)
    (h : authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack st ep msg id tag =
      .ok (st', r)) : BeltEnrollmentUnchanged st st' := by
  unfold authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack at h
  simp only [bind_eq_result_bind, result_bind_ok, lift,
    pants_and_quorum_guards.BeltQuorumCore.impl.n,
    pants_and_quorum_guards.BeltQuorumCore.impl.has_bound_epoch,
    pants_and_quorum_guards.BeltQuorumCore.impl.bound_epoch,
    pants_and_quorum_guards.BeltQuorumCore.impl.bound_msg_tag,
    pants_and_quorum_guards.BeltQuorumCore.impl.ack_count,
    pants_and_quorum_guards.BeltQuorumCore.is_poisoned] at h
  repeat (any_goals first
    | simp only [result_bind_ok_iff] at h
    | (obtain ⟨v, hv, h⟩ : ∃ v, _ ∧ _ := h)
    | (split at h))
  all_goals cases h <;> exact ⟨rfl, rfl, rfl⟩

private theorem belt_authorize_enrollment_unchanged
    (st st' : authenticated_belt.VerifiedBeltQuorumGuard)
    (ep : Std.U64) (msg : Array Std.U8 32#usize)
    (r : core.result.Result pants_and_quorum_guards.BeltAuthorizationGrant authenticated_belt.BeltAuthError)
    (h : authenticated_belt.VerifiedBeltQuorumGuard.authorize_shares st ep msg =
      .ok (st', r)) : BeltEnrollmentUnchanged st st' := by
  unfold authenticated_belt.VerifiedBeltQuorumGuard.authorize_shares at h
  simp only [bind_eq_result_bind, result_bind_ok,
    pants_and_quorum_guards.BeltQuorumCore.is_poisoned] at h
  repeat (any_goals first
    | simp only [result_bind_ok_iff] at h
    | (obtain ⟨v, hv, h⟩ : ∃ v, _ ∧ _ := h)
    | (split at h))
  all_goals cases h <;> exact ⟨rfl, rfl, rfl⟩

 theorem authenticated_belt_step_enrollment_unchanged
    (st st' : authenticated_belt.VerifiedBeltQuorumGuard)
    (inp : authenticated_belt.BeltQuorumStepInput)
    (r : core.result.Result authenticated_belt.BeltQuorumStepOutput authenticated_belt.BeltAuthError)
    (h : authenticated_belt.VerifiedBeltQuorumGuard.step st inp = .ok (st', r)) :
    BeltEnrollmentUnchanged st st' := by
  cases inp with
  | ProposeOrRetryEpoch ep msg digest tag =>
    unfold authenticated_belt.VerifiedBeltQuorumGuard.step at h
    cases he : authenticated_belt.VerifiedBeltQuorumGuard.propose_or_retry_epoch st ep msg digest tag with
    | fail e => simp [he, bind_eq_result_bind, Result.bind] at h
    | div => simp [he, bind_eq_result_bind, Result.bind] at h
    | ok v =>
      rcases v with ⟨next, res⟩
      have hk := belt_propose_enrollment_unchanged st next ep msg digest tag res he
      cases res <;> simp [he, bind_eq_result_bind, Result.bind] at h <;> rcases h with ⟨rfl, rfl⟩ <;> exact hk
  | RecordCustodianAck ep msg id tag =>
    unfold authenticated_belt.VerifiedBeltQuorumGuard.step at h
    cases he : authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack st ep msg id tag with
    | fail e => simp [he, bind_eq_result_bind, Result.bind] at h
    | div => simp [he, bind_eq_result_bind, Result.bind] at h
    | ok v =>
      rcases v with ⟨next, res⟩
      have hk := belt_ack_enrollment_unchanged st next ep msg tag id res he
      cases res <;> simp [he, bind_eq_result_bind, Result.bind] at h <;> rcases h with ⟨rfl, rfl⟩ <;> exact hk
  | AuthorizeShares ep msg =>
    unfold authenticated_belt.VerifiedBeltQuorumGuard.step at h
    cases he : authenticated_belt.VerifiedBeltQuorumGuard.authorize_shares st ep msg with
    | fail e => simp [he, bind_eq_result_bind, Result.bind] at h
    | div => simp [he, bind_eq_result_bind, Result.bind] at h
    | ok v =>
      rcases v with ⟨next, res⟩
      have hk := belt_authorize_enrollment_unchanged st next ep msg res he
      cases res <;> simp [he, bind_eq_result_bind, Result.bind] at h <;> rcases h with ⟨rfl, rfl⟩ <;> exact hk

private theorem belt_authorize_count_shape
    (st next : pants_and_quorum_guards.BeltQuorumCore)
    (ep : Std.U64) (msg : Array Std.U8 32#usize)
    (r : core.result.Result pants_and_quorum_guards.BeltAuthorizationGrant pants_and_quorum_guards.PantsGuardError)
    (h : pants_and_quorum_guards.BeltQuorumCore.authorize_shares st ep msg = .ok (next, r)) :
    next.ack_count = if next.poisoned then 0#u32 else st.ack_count := by
  unfold pants_and_quorum_guards.BeltQuorumCore.authorize_shares
    pants_and_quorum_guards.poison_belt_guard at h
  cases hp : st.poisoned <;> cases hphase : st.phase <;>
    simp only [hp, hphase, bind_eq_result_bind, result_bind_ok, validate_belt_quorum_config_eq,
      ct_eq_bytes32_spec, Bool.false_eq_true, ↓reduceIte] at h
  repeat (any_goals first
    | simp_all only [Bool.false_eq_true, ↓reduceIte]
    | (split at h))
  all_goals cases h <;> simp_all only [Bool.false_eq_true, ↓reduceIte]

theorem authenticated_belt_authorize_preserves_count
    (st st' : authenticated_belt.VerifiedBeltQuorumGuard)
    (ep : Std.U64) (msg : Array Std.U8 32#usize)
    (r : core.result.Result pants_and_quorum_guards.BeltAuthorizationGrant authenticated_belt.BeltAuthError)
    (h : authenticated_belt.VerifiedBeltQuorumGuard.authorize_shares st ep msg = .ok (st', r))
    (hi : BeltAckCountInvariant st) : BeltAckCountInvariant st' := by
  unfold authenticated_belt.VerifiedBeltQuorumGuard.authorize_shares at h
  cases hc : pants_and_quorum_guards.BeltQuorumCore.authorize_shares st.inner ep msg with
  | fail e => simp [hc, bind_eq_result_bind, Result.bind] at h
  | div => simp [hc, bind_eq_result_bind, Result.bind] at h
  | ok v =>
    rcases v with ⟨next, res⟩
    have hn := belt_authorize_count_shape st.inner next ep msg res hc
    cases hb : next.poisoned <;> cases res <;>
      simp only [hc, bind_eq_result_bind, result_bind_ok,
        pants_and_quorum_guards.BeltQuorumCore.is_poisoned, hb,
        Bool.false_eq_true, ↓reduceIte] at h <;> cases h
    all_goals simp only [hb, Bool.false_eq_true, ↓reduceIte] at hn
    all_goals unfold BeltAckCountInvariant
    all_goals rw [hn]
    all_goals first | exact hi | (change (0#u32).val = (List.range 64).countP (fun i => (0#u64).bv.getLsbD i); decide)

/-- The trust assumption applies exactly to the enrolled committee slots. -/
@[expose]
def BeltProvisionedKeys (n : Std.U32)
    (keys : Array (Array Std.U8 32#usize) 64#usize) : Prop :=
  (∀ (i : Std.U8) key, i.val < n.val →
    Array.index_usize keys (UScalar.cast .Usize i) = .ok key →
    key ≠ Array.repeat 32#usize 0#u8) ∧
  (∀ (i j : Std.U8) ki kj, i.val < n.val → j.val < n.val →
    Array.index_usize keys (UScalar.cast .Usize i) = .ok ki →
    Array.index_usize keys (UScalar.cast .Usize j) = .ok kj →
    ki = kj → i = j)

theorem authenticated_belt_step_preserves_provisioned_keys
    (n : Std.U32) (st st' : authenticated_belt.VerifiedBeltQuorumGuard)
    (inp : authenticated_belt.BeltQuorumStepInput)
    (r : core.result.Result authenticated_belt.BeltQuorumStepOutput authenticated_belt.BeltAuthError)
    (h : authenticated_belt.VerifiedBeltQuorumGuard.step st inp = .ok (st', r))
    (hk : BeltProvisionedKeys n st.custodian_keys) : BeltProvisionedKeys n st'.custodian_keys := by
  rw [(authenticated_belt_step_enrollment_unchanged st st' inp r h).2.1]
  exact hk

/-- The tag computation terminates for all keys, including the public all-zero key. -/
theorem custodian_ack_tag_total
    (key commit msg : Array Std.U8 32#usize) (epoch : Std.U64) (id : Std.U8) :
    ∃ tag, authenticated_belt.custodian_ack_tag key commit epoch msg id = .ok tag := by
  let domain := Array.make 16#usize [81#u8, 83#u8, 65#u8, 71#u8, 46#u8, 66#u8,
    69#u8, 76#u8, 84#u8, 46#u8, 65#u8, 67#u8, 75#u8, 46#u8, 118#u8, 49#u8]
  let sp : keccak.Shake256Sponge := {
    state := Array.repeat 25#usize 0#u64, buf := Array.repeat 136#usize 0#u8,
    buf_len := 0#usize, suffix := 31#u8, squeezing := false, squeeze_offset := 0#usize }
  have hepoch : ∃ bytes, authenticated_belt.encode_epoch epoch = .ok bytes := by
    exact ⟨_, rfl⟩
  obtain ⟨bytes, hepoch⟩ := hepoch
  obtain ⟨s1, h1, hn1, hb1⟩ := sponge_absorb_short sp domain.to_slice rfl (by decide)
  have hl (a : Array Std.U8 32#usize) : a.to_slice.val.length = 32 := a.property
  obtain ⟨s2, h2, hn2, hb2⟩ := sponge_absorb_short s1 key.to_slice hn1
    (by rw [hb1, hl]; decide)
  obtain ⟨s3, h3, hn3, hb3⟩ := sponge_absorb_short s2 commit.to_slice hn2
    (by rw [hb2, hb1, hl, hl]; decide)
  obtain ⟨s4, h4, hn4, hb4⟩ := sponge_absorb_short s3 bytes.to_slice hn3
    (by rw [hb3, hb2, hb1, hl, hl]; change 16 + 32 + 32 + bytes.val.length < 136;
        rw [bytes.property]; decide)
  obtain ⟨s5, h5, hn5, hb5⟩ := sponge_absorb_short s4 msg.to_slice hn4
    (by rw [hb4, hb3, hb2, hb1, hl, hl, hl];
        change 16 + 32 + 32 + bytes.val.length + 32 < 136; rw [bytes.property]; decide)
  obtain ⟨s6, h6, hn6, hb6⟩ := sponge_absorb_short s5 (Array.make 1#usize [id]).to_slice hn5
    (by rw [hb5, hb4, hb3, hb2, hb1, hl, hl, hl];
        change 16 + 32 + 32 + bytes.val.length + 32 + 1 < 136; rw [bytes.property]; decide)
  obtain ⟨out, hout⟩ := sponge_squeeze_short s6 (Array.repeat 32#usize 0#u8).to_slice
    32 (by decide) hn6
    (by rw [hb6, hb5, hb4, hb3, hb2, hb1, hl, hl, hl];
        change 16 + 32 + 32 + bytes.val.length + 32 + 1 < 136; rw [bytes.property]; decide)
    (by decide)
  refine ⟨Array.from_slice (Array.repeat 32#usize 0#u8) out.2, ?_⟩
  unfold authenticated_belt.custodian_ack_tag
  simp only [keccak.Shake256Sponge.new_shake256, bind_eq_result_bind, result_bind_ok,
    lift, hepoch, Array.to_slice_mut]
  rw [h1]
  simp only [result_bind_ok, h2, h3, h4, h5, h6, hout]

theorem authenticated_belt_accepted_proposal_receipt
    (st st' : authenticated_belt.VerifiedBeltQuorumGuard)
    (ep : Std.U64) (msg digest tag : Array Std.U8 32#usize)
    (h : authenticated_belt.VerifiedBeltQuorumGuard.propose_or_retry_epoch st ep msg digest tag =
      .ok (st', .Ok ())) :
    authenticated_belt.wal_receipt_tag st.wal_key st.guard_key_commit ep msg digest = .ok tag := by
  unfold authenticated_belt.VerifiedBeltQuorumGuard.propose_or_retry_epoch at h
  cases hw : authenticated_belt.wal_receipt_tag st.wal_key st.guard_key_commit ep msg digest with
  | fail e => simp [hw, bind_eq_result_bind, Result.bind] at h
  | div => simp [hw, bind_eq_result_bind, Result.bind] at h
  | ok expected =>
    by_cases heq : expected = tag
    · exact congrArg Result.ok heq
    · simp only [hw, bind_eq_result_bind, result_bind_ok, ct_eq_bytes32_spec,
        heq, decide_false, Bool.false_eq_true, ↓reduceIte,
        pants_and_quorum_guards.BeltQuorumCore.impl.has_bound_epoch,
        pants_and_quorum_guards.BeltQuorumCore.impl.bound_epoch,
        pants_and_quorum_guards.BeltQuorumCore.is_poisoned] at h
      repeat (any_goals first
        | simp only [result_bind_ok_iff] at h
        | (obtain ⟨v, hv, h⟩ : ∃ v, _ ∧ _ := h)
        | (split at h))
      all_goals cases h

/-- A public all-zero slot key admits a publicly computable accepted tag.
This is an inhabited counterexample to treating tag validity as secret-key provisioning. -/
theorem authenticated_belt_zero_key_accepts_public_tag :
    let zero := Array.repeat 32#usize 0#u8
    let st : authenticated_belt.VerifiedBeltQuorumGuard := {
      inner := {
        n := 3#u32, t := 2#u32, f := 0#u32, q := 2#u32,
        global_liveness_mode := false, next_epoch := 1#u64, max_jump_window := 1#u64,
        phase := .EpochBoundPendingQuorum, has_bound_epoch := true,
        bound_epoch := 0#u64, bound_msg_tag := zero, ack_count := 1#u32, poisoned := false },
      guard_key_commit := zero, custodian_keys := Array.repeat 64#usize zero,
      wal_key := zero, ack_bitmap := 1#u64 }
    ∃ tag,
      Array.index_usize st.custodian_keys (UScalar.cast .Usize 0#u8) = .ok zero ∧
      authenticated_belt.custodian_ack_tag zero zero 0#u64 zero 0#u8 = .ok tag ∧
      authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack st 0#u64 zero 0#u8 tag =
        .ok (st, .Ok 1#u32) := by
  dsimp only
  obtain ⟨tag, htag⟩ := custodian_ack_tag_total
    (Array.repeat 32#usize 0#u8) (Array.repeat 32#usize 0#u8)
    (Array.repeat 32#usize 0#u8) 0#u64 0#u8
  refine ⟨tag, rfl, htag, ?_⟩
  exact authenticated_belt_duplicate_ack_unchanged _ _ _ _ _ _ 1#u64
    (by decide) (by decide) rfl htag rfl rfl rfl rfl rfl (by decide)

theorem authenticated_belt_accepted_ack_tag
    (st st' : authenticated_belt.VerifiedBeltQuorumGuard)
    (ep : Std.U64) (msg tag : Array Std.U8 32#usize) (id : Std.U8) (count : Std.U32)
    (h : authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack st ep msg id tag =
      .ok (st', .Ok count)) :
    id.val < st.inner.n.val ∧ id.val < 64 ∧
    ∃ key, Array.index_usize st.custodian_keys (UScalar.cast .Usize id) = .ok key ∧
      authenticated_belt.custodian_ack_tag key st.guard_key_commit ep msg id = .ok tag := by
  unfold authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack at h
  simp only [bind_eq_result_bind, result_bind_ok, lift,
    pants_and_quorum_guards.BeltQuorumCore.impl.n] at h
  split at h
  · cases h
  · rename_i hin
    split at h
    · cases h
    · rename_i h64
      cases hk : Array.index_usize st.custodian_keys (UScalar.cast .Usize id) with
      | fail e => simp only [hk, result_bind_fail, reduceCtorEq] at h
      | div => simp only [hk, result_bind_div, reduceCtorEq] at h
      | ok key =>
        simp only [hk, result_bind_ok] at h
        cases ht : authenticated_belt.custodian_ack_tag key st.guard_key_commit ep msg id with
        | fail e => simp only [ht, result_bind_fail, reduceCtorEq] at h
        | div => simp only [ht, result_bind_div, reduceCtorEq] at h
        | ok expected =>
          simp only [ht, result_bind_ok, ct_eq_bytes32_spec] at h
          by_cases heq : expected = tag
          · have hc8 : (UScalar.cast .Usize id).val = id.val := by
              change (id.bv.setWidth 64).toNat = id.bv.toNat
              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt
                (Nat.lt_of_lt_of_le id.bv.isLt (by decide : 2^8 ≤ 2^64))]
            have hc32 : (UScalar.cast .Usize st.inner.n).val = st.inner.n.val := by
              change (st.inner.n.bv.setWidth 64).toNat = st.inner.n.bv.toNat
              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt
                (Nat.lt_of_lt_of_le st.inner.n.bv.isLt (by decide : 2^32 ≤ 2^64))]
            change ¬ (UScalar.cast .Usize st.inner.n).val ≤ (UScalar.cast .Usize id).val at hin
            rw [hc8, hc32] at hin
            change ¬ 64 ≤ id.val at h64
            exact ⟨Nat.lt_of_not_ge hin, Nat.lt_of_not_ge h64, key, rfl, heq ▸ ht⟩
          · simp only [heq, decide_false, Bool.false_eq_true, ↓reduceIte] at h
            cases h

private theorem belt_propose_count_shape
    (st next : pants_and_quorum_guards.BeltQuorumCore)
    (ep : Std.U64) (msg : Array Std.U8 32#usize) (valid : Bool)
    (r : core.result.Result Unit pants_and_quorum_guards.PantsGuardError)
    (h : pants_and_quorum_guards.BeltQuorumCore.propose_or_retry_epoch st ep msg valid = .ok (next, r)) :
    next.ack_count = if next.poisoned then 0#u32
      else if st.has_bound_epoch && decide (st.bound_epoch = ep) then st.ack_count
      else match r with | .Ok _ => 0#u32 | .Err _ => st.ack_count := by
  rw [show decide (st.bound_epoch = ep) = decide (ep = st.bound_epoch) by simp only [eq_comm]]
  cases r with
  | Ok u =>
    have hs := (belt_propose_step_sim st ep msg valid).1 next u h
    dsimp only at ⊢
    clear h
    dsimp only [beltQuorumMealy] at hs
    repeat (any_goals first
      | (split at hs)
      | simp only [reduceCtorEq] at hs)
    all_goals cases hs
    all_goals simp_all [beltGuardCorrupt]
  | Err e =>
    have hs := (belt_propose_step_sim st ep msg valid).2 next e h |>.2
    dsimp only at ⊢
    clear h
    dsimp only [beltQuorumMealy] at hs
    repeat (any_goals split at hs)
    all_goals subst next
    all_goals simp_all [beltGuardCorrupt]

theorem authenticated_belt_propose_preserves_count
    (st st' : authenticated_belt.VerifiedBeltQuorumGuard)
    (ep : Std.U64) (msg digest tag : Array Std.U8 32#usize)
    (r : core.result.Result Unit authenticated_belt.BeltAuthError)
    (h : authenticated_belt.VerifiedBeltQuorumGuard.propose_or_retry_epoch st ep msg digest tag = .ok (st', r))
    (hi : BeltAckCountInvariant st) : BeltAckCountInvariant st' := by
  unfold authenticated_belt.VerifiedBeltQuorumGuard.propose_or_retry_epoch at h
  cases hw : authenticated_belt.wal_receipt_tag st.wal_key st.guard_key_commit ep msg digest with
  | fail e => simp [hw, bind_eq_result_bind, Result.bind] at h
  | div => simp [hw, bind_eq_result_bind, Result.bind] at h
  | ok expected =>
    cases hc : pants_and_quorum_guards.BeltQuorumCore.propose_or_retry_epoch
        st.inner ep msg (decide (expected = tag)) with
    | fail e =>
      cases hb : st.inner.has_bound_epoch <;> by_cases he : st.inner.bound_epoch = ep <;>
        simp [hw, ct_eq_bytes32_spec, hb, he, hc, bind_eq_result_bind, Result.bind,
          pants_and_quorum_guards.BeltQuorumCore.impl.has_bound_epoch,
          pants_and_quorum_guards.BeltQuorumCore.impl.bound_epoch] at h
    | div =>
      cases hb : st.inner.has_bound_epoch <;> by_cases he : st.inner.bound_epoch = ep <;>
        simp [hw, ct_eq_bytes32_spec, hb, he, hc, bind_eq_result_bind, Result.bind,
          pants_and_quorum_guards.BeltQuorumCore.impl.has_bound_epoch,
          pants_and_quorum_guards.BeltQuorumCore.impl.bound_epoch] at h
    | ok v =>
      rcases v with ⟨next, res⟩
      have hn := belt_propose_count_shape st.inner next ep msg (decide (expected = tag)) res hc
      cases hb : st.inner.has_bound_epoch <;> by_cases he : st.inner.bound_epoch = ep <;>
        cases hp : next.poisoned <;> cases res <;> by_cases ht : expected = tag
      all_goals simp only [ht, decide_true, decide_false] at hc
      all_goals simp only [hw, ct_eq_bytes32_spec, hc, bind_eq_result_bind, result_bind_ok,
        pants_and_quorum_guards.BeltQuorumCore.impl.has_bound_epoch,
        pants_and_quorum_guards.BeltQuorumCore.impl.bound_epoch,
        pants_and_quorum_guards.BeltQuorumCore.is_poisoned, hb, he, hp, ht,
        decide_true, decide_false, Bool.false_eq_true, ↓reduceIte] at h
      all_goals cases h
      all_goals simp only [hb, he, hp, Bool.false_and, Bool.true_and, decide_true,
        decide_false, Bool.false_eq_true, ↓reduceIte] at hn
      all_goals unfold BeltAckCountInvariant
      all_goals rw [hn]
      all_goals first | exact hi | (change (0#u32).val = (List.range 64).countP (fun i => (0#u64).bv.getLsbD i); decide)

/-- Proposal projection pins the core Boolean to the extracted WAL MAC comparison. -/
theorem authenticated_belt_propose_core_projection
    (st st' : authenticated_belt.VerifiedBeltQuorumGuard)
    (ep : Std.U64) (msg digest tag : Array Std.U8 32#usize)
    (r : core.result.Result Unit authenticated_belt.BeltAuthError)
    (h : authenticated_belt.VerifiedBeltQuorumGuard.propose_or_retry_epoch st ep msg digest tag =
      .ok (st', r)) :
    ∃ expected cr,
      authenticated_belt.wal_receipt_tag st.wal_key st.guard_key_commit ep msg digest = .ok expected ∧
      pants_and_quorum_guards.BeltQuorumCore.propose_or_retry_epoch st.inner ep msg
        (decide (expected = tag)) = .ok (st'.inner, cr) := by
  unfold authenticated_belt.VerifiedBeltQuorumGuard.propose_or_retry_epoch at h
  simp only [bind_eq_result_bind, result_bind_ok, ct_eq_bytes32_spec,
    pants_and_quorum_guards.BeltQuorumCore.impl.has_bound_epoch,
    pants_and_quorum_guards.BeltQuorumCore.impl.bound_epoch,
    pants_and_quorum_guards.BeltQuorumCore.is_poisoned] at h
  repeat (any_goals first
    | simp only [result_bind_ok_iff, reduceCtorEq, ↓reduceIte] at h
    | (obtain ⟨v, hv, h⟩ : ∃ v, _ ∧ _ := h)
    | (split at h))
  all_goals cases h
  all_goals exact ⟨_, v.2, by assumption, hv⟩

/-- Authentication failures and duplicate acknowledgments stutter; other acks enter the core. -/
theorem authenticated_belt_ack_core_projection
    (st st' : authenticated_belt.VerifiedBeltQuorumGuard)
    (ep : Std.U64) (msg tag : Array Std.U8 32#usize) (id : Std.U8)
    (r : core.result.Result Std.U32 authenticated_belt.BeltAuthError)
    (h : authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack st ep msg id tag =
      .ok (st', r)) :
    st' = st ∨ ∃ cr, pants_and_quorum_guards.BeltQuorumCore.record_custodian_ack
      st.inner ep msg = .ok (st'.inner, cr) := by
  unfold authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack at h
  simp only [bind_eq_result_bind, result_bind_ok, lift,
    pants_and_quorum_guards.BeltQuorumCore.impl.n,
    pants_and_quorum_guards.BeltQuorumCore.impl.has_bound_epoch,
    pants_and_quorum_guards.BeltQuorumCore.impl.bound_epoch,
    pants_and_quorum_guards.BeltQuorumCore.impl.bound_msg_tag,
    pants_and_quorum_guards.BeltQuorumCore.impl.ack_count,
    pants_and_quorum_guards.BeltQuorumCore.is_poisoned] at h
  repeat (any_goals first
    | simp only [result_bind_ok_iff] at h
    | (obtain ⟨v, hv, h⟩ : ∃ v, _ ∧ _ := h)
    | (split at h))
  all_goals cases h
  all_goals first | exact Or.inl rfl | (apply Or.inr; exact ⟨_, by assumption⟩)

theorem authenticated_belt_authorize_core_projection
    (st st' : authenticated_belt.VerifiedBeltQuorumGuard)
    (ep : Std.U64) (msg : Array Std.U8 32#usize)
    (r : core.result.Result pants_and_quorum_guards.BeltAuthorizationGrant authenticated_belt.BeltAuthError)
    (h : authenticated_belt.VerifiedBeltQuorumGuard.authorize_shares st ep msg = .ok (st', r)) :
    ∃ cr, pants_and_quorum_guards.BeltQuorumCore.authorize_shares st.inner ep msg = .ok (st'.inner, cr) := by
  unfold authenticated_belt.VerifiedBeltQuorumGuard.authorize_shares at h
  simp only [bind_eq_result_bind, result_bind_ok,
    pants_and_quorum_guards.BeltQuorumCore.is_poisoned] at h
  repeat (any_goals first
    | simp only [result_bind_ok_iff] at h
    | (obtain ⟨v, hv, h⟩ : ∃ v, _ ∧ _ := h)
    | (split at h))
  all_goals cases h
  all_goals exact ⟨_, by assumption⟩

theorem authenticated_belt_trace_enrollment_unchanged
    {st st_final : authenticated_belt.VerifiedBeltQuorumGuard}
    {turns : List (MirTurn authenticated_belt.BeltQuorumStepInput
      authenticated_belt.BeltQuorumStepOutput authenticated_belt.BeltAuthError)}
    (htrace : MirTrace (adaptStateResult authenticated_belt.VerifiedBeltQuorumGuard.step)
      st turns st_final) : BeltEnrollmentUnchanged st st_final := by
  induction htrace with
  | nil _ => exact ⟨rfl, rfl, rfl⟩
  | @accept m m' mf inp out rest hstep htail ih =>
    simp only [adaptStateResult, result_bind_ok_iff] at hstep
    obtain ⟨⟨next, res⟩, hr, ho⟩ := hstep
    cases res <;> cases ho
    have hk := authenticated_belt_step_enrollment_unchanged m next inp _ hr
    exact ⟨ih.1.trans hk.1, ih.2.1.trans hk.2.1, ih.2.2.trans hk.2.2⟩
  | @reject m m' mf inp err rest hstep htail ih =>
    simp only [adaptStateResult, result_bind_ok_iff] at hstep
    obtain ⟨⟨next, res⟩, hr, ho⟩ := hstep
    cases res <;> cases ho
    have hk := authenticated_belt_step_enrollment_unchanged m next inp _ hr
    exact ⟨ih.1.trans hk.1, ih.2.1.trans hk.2.1, ih.2.2.trans hk.2.2⟩

theorem authenticated_belt_trace_preserves_provisioned_keys
    (n : Std.U32) {st st_final : authenticated_belt.VerifiedBeltQuorumGuard}
    {turns : List (MirTurn authenticated_belt.BeltQuorumStepInput
      authenticated_belt.BeltQuorumStepOutput authenticated_belt.BeltAuthError)}
    (htrace : MirTrace (adaptStateResult authenticated_belt.VerifiedBeltQuorumGuard.step)
      st turns st_final)
    (hk : BeltProvisionedKeys n st.custodian_keys) : BeltProvisionedKeys n st_final.custodian_keys := by
  rw [(authenticated_belt_trace_enrollment_unchanged htrace).2.1]
  exact hk

private theorem belt_countP_disjoint (xs : List Nat) (f g : Nat → Bool)
    (hd : ∀ i ∈ xs, (f i && g i) = false) :
    xs.countP (fun i => f i || g i) = xs.countP f + xs.countP g := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have ha := hd a (by simp)
    have ht := ih (fun i hi => hd i (List.mem_cons_of_mem a hi))
    cases hf : f a <;> cases hg : g a <;>
      simp_all <;> omega

private theorem belt_single_bit (id : Nat) (hid : id < 64) (i : Nat) :
    ((1 : BitVec 64) <<< id).getLsbD i = decide (i = id) := by
  have hone : (1 : BitVec 64).getLsbD (i - id) = decide (i - id = 0) :=
    BitVec.getLsbD_one
  apply Bool.eq_iff_iff.mpr
  simp only [BitVec.getLsbD_shiftLeft, hone, Bool.and_eq_true,
    not_decide_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨_, hge⟩, hz⟩
    exact Nat.le_antisymm (Nat.le_of_sub_eq_zero hz) (Nat.le_of_not_gt hge)
  · intro he
    subst i
    exact ⟨⟨hid, Nat.lt_irrefl id⟩, Nat.sub_self id⟩

private theorem belt_bitmap_insert_count
    (bitmap : Std.U64) (id : Nat) (hid : id < 64)
    (hfresh : bitmap.bv &&& ((1 : BitVec 64) <<< id) = 0) :
    (List.range 64).countP (fun i => (bitmap.bv ||| ((1 : BitVec 64) <<< id)).getLsbD i) =
      (List.range 64).countP (fun i => bitmap.bv.getLsbD i) + 1 := by
  have hd (i : Nat) (_hi : i ∈ List.range 64) :
      (bitmap.bv.getLsbD i && ((1 : BitVec 64) <<< id).getLsbD i) = false := by
    rw [← BitVec.getLsbD_and, hfresh]
    exact BitVec.getLsbD_zero
  simp only [BitVec.getLsbD_or]
  rw [belt_countP_disjoint _ _ _ hd]
  have hcount : (List.range 64).countP (fun i => ((1 : BitVec 64) <<< id).getLsbD i) = 1 := by
    simp only [belt_single_bit id hid]
    change (List.range 64).count id = 1
    exact List.Nodup.count_of_mem (by decide)
      ((by decide : ∀ i : Fin 64, i.val ∈ List.range 64) ⟨id, hid⟩)
  rw [hcount]

/-- Authentication of an input against immutable enrollment material. This asserts MAC
validity, not that the provisioned slot key is secret or nonzero. -/
@[expose]
def BeltAuthenticatedInput (commit wal : Array Std.U8 32#usize)
    (keys : Array (Array Std.U8 32#usize) 64#usize) : authenticated_belt.BeltQuorumStepInput → Prop
  | .ProposeOrRetryEpoch ep msg digest tag =>
    authenticated_belt.wal_receipt_tag wal commit ep msg digest = .ok tag
  | .RecordCustodianAck ep msg id tag => id.val < 64 ∧
    ∃ key, Array.index_usize keys (UScalar.cast .Usize id) = .ok key ∧
      authenticated_belt.custodian_ack_tag key commit ep msg id = .ok tag
  | .AuthorizeShares _ _ => True

theorem authenticated_belt_step_accepted_input
    (st st' : authenticated_belt.VerifiedBeltQuorumGuard)
    (inp : authenticated_belt.BeltQuorumStepInput) (out : authenticated_belt.BeltQuorumStepOutput)
    (h : authenticated_belt.VerifiedBeltQuorumGuard.step st inp = .ok (st', .Ok out)) :
    BeltAuthenticatedInput st.guard_key_commit st.wal_key st.custodian_keys inp := by
  cases inp with
  | ProposeOrRetryEpoch ep msg digest tag =>
    unfold authenticated_belt.VerifiedBeltQuorumGuard.step at h
    cases he : authenticated_belt.VerifiedBeltQuorumGuard.propose_or_retry_epoch st ep msg digest tag with
    | fail e => simp [he, bind_eq_result_bind, Result.bind] at h
    | div => simp [he, bind_eq_result_bind, Result.bind] at h
    | ok v =>
      rcases v with ⟨next, res⟩
      cases res with
      | Err e => simp [he, bind_eq_result_bind, Result.bind] at h
      | Ok u =>
        cases u
        exact authenticated_belt_accepted_proposal_receipt st next ep msg digest tag he
  | RecordCustodianAck ep msg id tag =>
    unfold authenticated_belt.VerifiedBeltQuorumGuard.step at h
    cases he : authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack st ep msg id tag with
    | fail e => simp [he, bind_eq_result_bind, Result.bind] at h
    | div => simp [he, bind_eq_result_bind, Result.bind] at h
    | ok v =>
      rcases v with ⟨next, res⟩
      cases res with
      | Err e => simp [he, bind_eq_result_bind, Result.bind] at h
      | Ok count =>
        exact (authenticated_belt_accepted_ack_tag st next ep msg tag id count he).2
  | AuthorizeShares _ _ => trivial

/-- Every accepted proposal and acknowledgment in the actual multi-turn wrapper trace
has a valid MAC under the initial enrollment material, including after rejected turns. -/
theorem authenticated_belt_trace_mac_valid
    {st st_final : authenticated_belt.VerifiedBeltQuorumGuard}
    {turns : List (MirTurn authenticated_belt.BeltQuorumStepInput
      authenticated_belt.BeltQuorumStepOutput authenticated_belt.BeltAuthError)}
    (htrace : MirTrace (adaptStateResult authenticated_belt.VerifiedBeltQuorumGuard.step)
      st turns st_final) :
    ∀ p ∈ mirAcceptedPairs turns,
      BeltAuthenticatedInput st.guard_key_commit st.wal_key st.custodian_keys p.1 := by
  induction htrace with
  | nil _ => intro p hp; exact False.elim (List.not_mem_nil hp)
  | @accept m m' mf inp out rest hstep htail ih =>
    simp only [adaptStateResult, result_bind_ok_iff] at hstep
    obtain ⟨⟨next, res⟩, hr, ho⟩ := hstep
    cases res <;> cases ho
    have hk := authenticated_belt_step_enrollment_unchanged m next inp _ hr
    intro p hp
    simp only [mirAcceptedPairs, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact authenticated_belt_step_accepted_input m next inp out hr
    · have ht := ih p hp
      rw [hk.1, hk.2.1, hk.2.2] at ht
      exact ht
  | @reject m m' mf inp err rest hstep htail ih =>
    simp only [adaptStateResult, result_bind_ok_iff] at hstep
    obtain ⟨⟨next, res⟩, hr, ho⟩ := hstep
    cases res <;> cases ho
    have hk := authenticated_belt_step_enrollment_unchanged m next inp _ hr
    intro p hp
    have ht := ih p hp
    rw [hk.1, hk.2.1, hk.2.2] at ht
    exact ht

private theorem belt_ack_success_shape
    (st next : pants_and_quorum_guards.BeltQuorumCore) (ep : Std.U64)
    (msg : Array Std.U8 32#usize) (c : Std.U32)
    (h : pants_and_quorum_guards.BeltQuorumCore.record_custodian_ack st ep msg = .ok (next, .Ok c)) :
    next.poisoned = false ∧ msg = st.bound_msg_tag ∧ next.ack_count.val = st.ack_count.val + 1 := by
  have hs := (belt_ack_step_sim st ep msg).1 next c h
  clear h
  have hn := st.n.bv.isLt
  dsimp only [beltQuorumMealy] at hs
  repeat (any_goals first | (split at hs) | simp only [reduceCtorEq] at hs)
  all_goals cases hs
  all_goals simp_all [beltGuardCorrupt, BitVec.toNat_add]
  all_goals omega

private theorem belt_ack_error_shape
    (st next : pants_and_quorum_guards.BeltQuorumCore) (ep : Std.U64)
    (msg : Array Std.U8 32#usize) (e : pants_and_quorum_guards.PantsGuardError)
    (h : pants_and_quorum_guards.BeltQuorumCore.record_custodian_ack st ep msg = .ok (next, .Err e)) :
    next = st ∨ next = purePoisonBelt st := by
  have hs := (belt_ack_step_sim st ep msg).2 next e h |>.2
  dsimp only [beltQuorumMealy] at hs
  repeat (any_goals split at hs)
  all_goals subst next
  all_goals first | exact Or.inl rfl | exact Or.inr rfl

private theorem belt_ack_mismatch_poison
    (st next : pants_and_quorum_guards.BeltQuorumCore) (ep : Std.U64)
    (msg : Array Std.U8 32#usize)
    (r : core.result.Result Std.U32 pants_and_quorum_guards.PantsGuardError)
    (hb : st.has_bound_epoch = true) (he : ep = st.bound_epoch) (hm : msg ≠ st.bound_msg_tag)
    (h : pants_and_quorum_guards.BeltQuorumCore.record_custodian_ack st ep msg = .ok (next, r)) :
    next = purePoisonBelt st := by
  cases r with
  | Ok c => exact False.elim (hm (belt_ack_success_shape st next ep msg c h).2.1)
  | Err e =>
    have hs := (belt_ack_step_sim st ep msg).2 next e h |>.2
    simpa [beltQuorumMealy, hb, he, Ne.symm hm] using hs.symm

theorem authenticated_belt_ack_preserves_count
    (st st' : authenticated_belt.VerifiedBeltQuorumGuard)
    (ep : Std.U64) (msg tag : Array Std.U8 32#usize) (id : Std.U8)
    (r : core.result.Result Std.U32 authenticated_belt.BeltAuthError)
    (h : authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack st ep msg id tag = .ok (st', r))
    (hi : BeltAckCountInvariant st) : BeltAckCountInvariant st' := by
  by_cases h64 : id >= 64#u8
  · simp [authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack,
      pants_and_quorum_guards.BeltQuorumCore.impl.n, h64] at h
    rcases h with ⟨rfl, rfl⟩
    exact hi
  · have hid : id.val < 64 := Nat.lt_of_not_ge h64
    let bit : Std.U64 := ⟨(1 : BitVec 64) <<< id.val⟩
    have hshift : (1#u64 <<< id : Result Std.U64) = .ok bit := by
      change (if id.val < 64 then .ok bit else .fail .integerOverflow : Result Std.U64) = .ok bit
      simp only [hid, ↓reduceIte]
    cases hc : pants_and_quorum_guards.BeltQuorumCore.record_custodian_ack st.inner ep msg with
    | fail e =>
      unfold authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack at h
      simp only [bind_eq_result_bind, result_bind_ok, lift, ct_eq_bytes32_spec,
        pants_and_quorum_guards.BeltQuorumCore.impl.n,
        pants_and_quorum_guards.BeltQuorumCore.impl.has_bound_epoch,
        pants_and_quorum_guards.BeltQuorumCore.impl.bound_epoch,
        pants_and_quorum_guards.BeltQuorumCore.impl.bound_msg_tag,
        pants_and_quorum_guards.BeltQuorumCore.impl.ack_count,
        pants_and_quorum_guards.BeltQuorumCore.is_poisoned,
        h64, hshift, hc] at h
      repeat (any_goals first
        | simp only [result_bind_ok_iff, result_bind_fail, reduceCtorEq, ↓reduceIte] at h
        | (obtain ⟨v, hv, h⟩ : ∃ v, _ ∧ _ := h)
        | (split at h))
      all_goals cases h
      all_goals exact hi
    | div =>
      unfold authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack at h
      simp only [bind_eq_result_bind, result_bind_ok, lift, ct_eq_bytes32_spec,
        pants_and_quorum_guards.BeltQuorumCore.impl.n,
        pants_and_quorum_guards.BeltQuorumCore.impl.has_bound_epoch,
        pants_and_quorum_guards.BeltQuorumCore.impl.bound_epoch,
        pants_and_quorum_guards.BeltQuorumCore.impl.bound_msg_tag,
        pants_and_quorum_guards.BeltQuorumCore.impl.ack_count,
        pants_and_quorum_guards.BeltQuorumCore.is_poisoned,
        h64, hshift, hc] at h
      repeat (any_goals first
        | simp only [result_bind_ok_iff, result_bind_div, reduceCtorEq, ↓reduceIte] at h
        | (obtain ⟨v, hv, h⟩ : ∃ v, _ ∧ _ := h)
        | (split at h))
      all_goals cases h
      all_goals exact hi
    | ok v =>
      rcases v with ⟨next, res⟩
      cases res with
      | Ok c =>
        obtain ⟨hp, hm, hn⟩ := belt_ack_success_shape st.inner next ep msg c hc
        have hmdec : decide (msg = st.inner.bound_msg_tag) = true := decide_eq_true hm
        by_cases hfresh : st.ack_bitmap &&& bit = 0#u64
        · have hused : (st.ack_bitmap &&& bit != 0#u64) = false := by simp [hfresh]
          have hpop := belt_bitmap_insert_count st.ack_bitmap id.val hid (congrArg UScalar.bv hfresh)
          unfold authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack at h
          simp only [bind_eq_result_bind, result_bind_ok, lift, ct_eq_bytes32_spec,
            pants_and_quorum_guards.BeltQuorumCore.impl.n,
            pants_and_quorum_guards.BeltQuorumCore.impl.has_bound_epoch,
            pants_and_quorum_guards.BeltQuorumCore.impl.bound_epoch,
            pants_and_quorum_guards.BeltQuorumCore.impl.bound_msg_tag,
            pants_and_quorum_guards.BeltQuorumCore.impl.ack_count,
            pants_and_quorum_guards.BeltQuorumCore.is_poisoned,
            h64, hshift, hc, hmdec, hused] at h
          repeat (any_goals first
            | simp only [result_bind_ok_iff, reduceCtorEq, ↓reduceIte] at h
            | (obtain ⟨v, hv, h⟩ : ∃ v, _ ∧ _ := h)
            | (split at h))
          all_goals cases h
          all_goals first | exact hi | (change next.ack_count.val = (List.range 64).countP (fun i => (st.ack_bitmap.bv ||| ((1 : BitVec 64) <<< id.val)).getLsbD i); rw [hn, hpop]; exact congrArg (· + 1) hi)
        · have hused : (st.ack_bitmap &&& bit != 0#u64) = true := by simp [hfresh]
          unfold authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack at h
          simp only [bind_eq_result_bind, result_bind_ok, lift, ct_eq_bytes32_spec,
            pants_and_quorum_guards.BeltQuorumCore.impl.n,
            pants_and_quorum_guards.BeltQuorumCore.impl.has_bound_epoch,
            pants_and_quorum_guards.BeltQuorumCore.impl.bound_epoch,
            pants_and_quorum_guards.BeltQuorumCore.impl.bound_msg_tag,
            pants_and_quorum_guards.BeltQuorumCore.impl.ack_count,
            pants_and_quorum_guards.BeltQuorumCore.is_poisoned,
            h64, hshift, hc, hmdec, hused] at h
          repeat (any_goals first
            | simp only [result_bind_ok_iff, ↓reduceIte] at h
            | (obtain ⟨v, hv, h⟩ : ∃ v, _ ∧ _ := h)
            | (split at h))
          all_goals cases h
          all_goals exact hi
      | Err e =>
        rcases belt_ack_error_shape st.inner next ep msg e hc with hn | hn
        · subst next
          by_cases hp : st.inner.poisoned = true <;>
            by_cases hb : st.inner.has_bound_epoch = true <;>
            by_cases he : ep = st.inner.bound_epoch <;>
            by_cases hm : msg = st.inner.bound_msg_tag
          all_goals try
            have hbad := belt_ack_mismatch_poison st.inner st.inner ep msg (.Err e) hb he hm hc
            exact False.elim (hp (congrArg pants_and_quorum_guards.BeltQuorumCore.poisoned hbad))
          all_goals try simp only [he, hm] at hc
          all_goals
            unfold authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack at h
            simp only [bind_eq_result_bind, result_bind_ok, lift, ct_eq_bytes32_spec,
              pants_and_quorum_guards.BeltQuorumCore.impl.n,
              pants_and_quorum_guards.BeltQuorumCore.impl.has_bound_epoch,
              pants_and_quorum_guards.BeltQuorumCore.impl.bound_epoch,
              pants_and_quorum_guards.BeltQuorumCore.impl.bound_msg_tag,
              pants_and_quorum_guards.BeltQuorumCore.impl.ack_count,
              pants_and_quorum_guards.BeltQuorumCore.is_poisoned,
              h64, hshift, hc, hp, hb, he, hm, bne_iff_ne] at h
            repeat (any_goals first
              | simp only [result_bind_ok_iff, reduceCtorEq, ↓reduceIte] at h
              | (obtain ⟨v, hv, h⟩ : ∃ v, _ ∧ _ := h)
              | (split at h))
            all_goals cases h
          all_goals first | exact hi | (simp_all only [decide_true, not_true_eq_false])
        · subst next
          unfold authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack at h
          simp only [bind_eq_result_bind, result_bind_ok, lift, ct_eq_bytes32_spec,
            pants_and_quorum_guards.BeltQuorumCore.impl.n,
            pants_and_quorum_guards.BeltQuorumCore.impl.has_bound_epoch,
            pants_and_quorum_guards.BeltQuorumCore.impl.bound_epoch,
            pants_and_quorum_guards.BeltQuorumCore.impl.bound_msg_tag,
            pants_and_quorum_guards.BeltQuorumCore.impl.ack_count,
            pants_and_quorum_guards.BeltQuorumCore.is_poisoned,
            h64, hshift, hc] at h
          repeat (any_goals first
            | simp only [result_bind_ok_iff, ↓reduceIte] at h
            | (obtain ⟨v, hv, h⟩ : ∃ v, _ ∧ _ := h)
            | (split at h))
          all_goals cases h
          all_goals first | exact hi | (change (0#u32).val = (List.range 64).countP (fun i => (0#u64).bv.getLsbD i); decide)

theorem authenticated_belt_step_preserves_count
    (st st' : authenticated_belt.VerifiedBeltQuorumGuard)
    (inp : authenticated_belt.BeltQuorumStepInput)
    (r : core.result.Result authenticated_belt.BeltQuorumStepOutput authenticated_belt.BeltAuthError)
    (h : authenticated_belt.VerifiedBeltQuorumGuard.step st inp = .ok (st', r))
    (hi : BeltAckCountInvariant st) : BeltAckCountInvariant st' := by
  cases inp with
  | ProposeOrRetryEpoch ep msg digest tag =>
    unfold authenticated_belt.VerifiedBeltQuorumGuard.step at h
    cases he : authenticated_belt.VerifiedBeltQuorumGuard.propose_or_retry_epoch st ep msg digest tag with
    | fail e => simp [he, bind_eq_result_bind, Result.bind] at h
    | div => simp [he, bind_eq_result_bind, Result.bind] at h
    | ok v =>
      rcases v with ⟨next, res⟩
      have hk := authenticated_belt_propose_preserves_count st next ep msg digest tag res he hi
      cases res <;> simp [he, bind_eq_result_bind, Result.bind] at h <;> rcases h with ⟨rfl, rfl⟩ <;> exact hk
  | RecordCustodianAck ep msg id tag =>
    unfold authenticated_belt.VerifiedBeltQuorumGuard.step at h
    cases he : authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack st ep msg id tag with
    | fail e => simp [he, bind_eq_result_bind, Result.bind] at h
    | div => simp [he, bind_eq_result_bind, Result.bind] at h
    | ok v =>
      rcases v with ⟨next, res⟩
      have hk := authenticated_belt_ack_preserves_count st next ep msg tag id res he hi
      cases res <;> simp [he, bind_eq_result_bind, Result.bind] at h <;> rcases h with ⟨rfl, rfl⟩ <;> exact hk
  | AuthorizeShares ep msg =>
    unfold authenticated_belt.VerifiedBeltQuorumGuard.step at h
    cases he : authenticated_belt.VerifiedBeltQuorumGuard.authorize_shares st ep msg with
    | fail e => simp [he, bind_eq_result_bind, Result.bind] at h
    | div => simp [he, bind_eq_result_bind, Result.bind] at h
    | ok v =>
      rcases v with ⟨next, res⟩
      have hk := authenticated_belt_authorize_preserves_count st next ep msg res he hi
      cases res <;> simp [he, bind_eq_result_bind, Result.bind] at h <;> rcases h with ⟨rfl, rfl⟩ <;> exact hk

theorem authenticated_belt_trace_preserves_count
    {st st_final : authenticated_belt.VerifiedBeltQuorumGuard}
    {turns : List (MirTurn authenticated_belt.BeltQuorumStepInput
      authenticated_belt.BeltQuorumStepOutput authenticated_belt.BeltAuthError)}
    (htrace : MirTrace (adaptStateResult authenticated_belt.VerifiedBeltQuorumGuard.step)
      st turns st_final) (hi : BeltAckCountInvariant st) : BeltAckCountInvariant st_final := by
  induction htrace with
  | nil _ => exact hi
  | @accept m m' mf inp out rest hstep htail ih =>
    simp only [adaptStateResult, result_bind_ok_iff] at hstep
    obtain ⟨⟨next, res⟩, hr, ho⟩ := hstep
    cases res <;> cases ho
    exact ih (authenticated_belt_step_preserves_count m next inp _ hr hi)
  | @reject m m' mf inp err rest hstep htail ih =>
    simp only [adaptStateResult, result_bind_ok_iff] at hstep
    obtain ⟨⟨next, res⟩, hr, ho⟩ := hstep
    cases res <;> cases ho
    exact ih (authenticated_belt_step_preserves_count m next inp _ hr hi)

private theorem belt_propose_core_trace
    (st next : pants_and_quorum_guards.BeltQuorumCore) (ep : Std.U64)
    (msg : Array Std.U8 32#usize) (valid : Bool)
    (r : core.result.Result Unit pants_and_quorum_guards.PantsGuardError)
    (h : pants_and_quorum_guards.BeltQuorumCore.propose_or_retry_epoch st ep msg valid = .ok (next, r)) :
    ∃ pairs, beltQuorumMealy.ValidTrace st pairs next := by
  cases r with
  | Ok v =>
    exact ⟨[(.ProposeOrRetryEpoch ep msg valid, .EpochBound)],
      .accept ((belt_propose_step_sim st ep msg valid).1 next v h) (.nil next)⟩
  | Err e =>
    obtain ⟨hs, he⟩ := (belt_propose_step_sim st ep msg valid).2 next e h
    exact ⟨[], .reject (.ProposeOrRetryEpoch ep msg valid) hs (by rw [he]; exact .nil next)⟩

private theorem belt_ack_core_trace
    (st next : pants_and_quorum_guards.BeltQuorumCore) (ep : Std.U64)
    (msg : Array Std.U8 32#usize)
    (r : core.result.Result Std.U32 pants_and_quorum_guards.PantsGuardError)
    (h : pants_and_quorum_guards.BeltQuorumCore.record_custodian_ack st ep msg = .ok (next, r)) :
    ∃ pairs, beltQuorumMealy.ValidTrace st pairs next := by
  cases r with
  | Ok v =>
    exact ⟨[(.RecordCustodianAck ep msg, .AckRecorded v)],
      .accept ((belt_ack_step_sim st ep msg).1 next v h) (.nil next)⟩
  | Err e =>
    obtain ⟨hs, he⟩ := (belt_ack_step_sim st ep msg).2 next e h
    exact ⟨[], .reject (.RecordCustodianAck ep msg) hs (by rw [he]; exact .nil next)⟩

private theorem belt_authorize_core_trace
    (st next : pants_and_quorum_guards.BeltQuorumCore) (ep : Std.U64)
    (msg : Array Std.U8 32#usize)
    (r : core.result.Result pants_and_quorum_guards.BeltAuthorizationGrant pants_and_quorum_guards.PantsGuardError)
    (h : pants_and_quorum_guards.BeltQuorumCore.authorize_shares st ep msg = .ok (next, r)) :
    ∃ pairs, beltQuorumMealy.ValidTrace st pairs next := by
  cases r with
  | Ok v =>
    exact ⟨[(.AuthorizeShares ep msg, .SharesAuthorized v)],
      .accept ((belt_auth_step_sim st ep msg).1 next v h) (.nil next)⟩
  | Err e =>
    obtain ⟨hs, he⟩ := (belt_auth_step_sim st ep msg).2 next e h
    exact ⟨[], .reject (.AuthorizeShares ep msg) hs (by rw [he]; exact .nil next)⟩

private theorem authenticated_belt_authorized_grant_core
    (st st' : authenticated_belt.VerifiedBeltQuorumGuard)
    (ep : Std.U64) (msg : Array Std.U8 32#usize)
    (grant : pants_and_quorum_guards.BeltAuthorizationGrant)
    (h : authenticated_belt.VerifiedBeltQuorumGuard.authorize_shares st ep msg = .ok (st', .Ok grant)) :
    pants_and_quorum_guards.BeltQuorumCore.authorize_shares st.inner ep msg = .ok (st'.inner, .Ok grant) := by
  unfold authenticated_belt.VerifiedBeltQuorumGuard.authorize_shares at h
  cases hc : pants_and_quorum_guards.BeltQuorumCore.authorize_shares st.inner ep msg with
  | fail e => simp [hc, bind_eq_result_bind, Result.bind] at h
  | div => simp [hc, bind_eq_result_bind, Result.bind] at h
  | ok v =>
    rcases v with ⟨next, res⟩
    cases res <;> cases hp : next.poisoned <;>
      simp only [hc, bind_eq_result_bind, result_bind_ok,
        pants_and_quorum_guards.BeltQuorumCore.is_poisoned, hp,
        Bool.false_eq_true, ↓reduceIte] at h <;> cases h
    all_goals rfl

private theorem authenticated_belt_step_core_trace
    (st st' : authenticated_belt.VerifiedBeltQuorumGuard)
    (inp : authenticated_belt.BeltQuorumStepInput)
    (r : core.result.Result authenticated_belt.BeltQuorumStepOutput authenticated_belt.BeltAuthError)
    (h : authenticated_belt.VerifiedBeltQuorumGuard.step st inp = .ok (st', r)) :
    ∃ pairs, beltQuorumMealy.ValidTrace st.inner pairs st'.inner ∧
      ∀ g, r = .Ok (.SharesAuthorized g) → ∃ p ∈ pairs, p.2 = .SharesAuthorized g := by
  cases inp with
  | ProposeOrRetryEpoch ep msg digest tag =>
    unfold authenticated_belt.VerifiedBeltQuorumGuard.step at h
    cases he : authenticated_belt.VerifiedBeltQuorumGuard.propose_or_retry_epoch st ep msg digest tag with
    | fail e => simp [he, bind_eq_result_bind, Result.bind] at h
    | div => simp [he, bind_eq_result_bind, Result.bind] at h
    | ok v =>
      rcases v with ⟨next, res⟩
      obtain ⟨expected, cr, _, hc⟩ := authenticated_belt_propose_core_projection st next ep msg digest tag res he
      obtain ⟨pairs, ht⟩ := belt_propose_core_trace st.inner next.inner ep msg (decide (expected = tag)) cr hc
      cases res <;> simp [he, bind_eq_result_bind, Result.bind] at h <;> rcases h with ⟨rfl, rfl⟩
      all_goals exact ⟨pairs, ht, fun g hg => by cases hg⟩
  | RecordCustodianAck ep msg id tag =>
    unfold authenticated_belt.VerifiedBeltQuorumGuard.step at h
    cases he : authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack st ep msg id tag with
    | fail e => simp [he, bind_eq_result_bind, Result.bind] at h
    | div => simp [he, bind_eq_result_bind, Result.bind] at h
    | ok v =>
      rcases v with ⟨next, res⟩
      have ht : ∃ pairs, beltQuorumMealy.ValidTrace st.inner pairs next.inner := by
        rcases authenticated_belt_ack_core_projection st next ep msg tag id res he with hn | ⟨cr, hc⟩
        · subst next; exact ⟨[], .nil _⟩
        · exact belt_ack_core_trace st.inner next.inner ep msg cr hc
      obtain ⟨pairs, ht⟩ := ht
      cases res <;> simp [he, bind_eq_result_bind, Result.bind] at h <;> rcases h with ⟨rfl, rfl⟩
      all_goals exact ⟨pairs, ht, fun g hg => by cases hg⟩
  | AuthorizeShares ep msg =>
    unfold authenticated_belt.VerifiedBeltQuorumGuard.step at h
    cases he : authenticated_belt.VerifiedBeltQuorumGuard.authorize_shares st ep msg with
    | fail e => simp [he, bind_eq_result_bind, Result.bind] at h
    | div => simp [he, bind_eq_result_bind, Result.bind] at h
    | ok v =>
      rcases v with ⟨next, res⟩
      cases res with
      | Ok grant =>
        simp [he, bind_eq_result_bind, Result.bind] at h
        rcases h with ⟨rfl, rfl⟩
        have hc := authenticated_belt_authorized_grant_core st next ep msg grant he
        refine ⟨[(.AuthorizeShares ep msg, .SharesAuthorized grant)],
          .accept ((belt_auth_step_sim st.inner ep msg).1 next.inner grant hc) (.nil _), ?_⟩
        intro g hg
        cases hg
        exact ⟨_, List.mem_cons_self, rfl⟩
      | Err e =>
        simp [he, bind_eq_result_bind, Result.bind] at h
        rcases h with ⟨rfl, rfl⟩
        obtain ⟨cr, hc⟩ := authenticated_belt_authorize_core_projection st next ep msg (.Err e) he
        obtain ⟨pairs, ht⟩ := belt_authorize_core_trace st.inner next.inner ep msg cr hc
        exact ⟨pairs, ht, fun g hg => by cases hg⟩

private theorem belt_core_trace_append
    {s m f : pants_and_quorum_guards.BeltQuorumCore}
    {xs ys : List (pants_and_quorum_guards.BeltQuorumCoreInput × pants_and_quorum_guards.BeltQuorumCoreOutput)}
    (hx : beltQuorumMealy.ValidTrace s xs m) (hy : beltQuorumMealy.ValidTrace m ys f) :
    beltQuorumMealy.ValidTrace s (xs ++ ys) f := by
  induction hx with
  | nil _ => exact hy
  | accept h _ ih => exact .accept h (ih hy)
  | reject inp h _ ih => exact .reject inp h (ih hy)

/-- The authenticated trace has a core execution covering every released grant.
Duplicate acknowledgments and early authentication errors contribute no core turns. -/
theorem authenticated_belt_trace_core_projection
    {st st_final : authenticated_belt.VerifiedBeltQuorumGuard}
    {turns : List (MirTurn authenticated_belt.BeltQuorumStepInput
      authenticated_belt.BeltQuorumStepOutput authenticated_belt.BeltAuthError)}
    (htrace : MirTrace (adaptStateResult authenticated_belt.VerifiedBeltQuorumGuard.step)
      st turns st_final) :
    ∃ pairs, beltQuorumMealy.ValidTrace st.inner pairs st_final.inner ∧
      ∀ p ∈ mirAcceptedPairs turns, ∀ g, p.2 = .SharesAuthorized g →
        ∃ cp ∈ pairs, cp.2 = .SharesAuthorized g := by
  induction htrace with
  | nil _ => exact ⟨[], .nil _, fun p hp => False.elim (List.not_mem_nil hp)⟩
  | @accept m m' mf inp out rest hstep htail ih =>
    simp only [adaptStateResult, result_bind_ok_iff] at hstep
    obtain ⟨⟨next, res⟩, hr, ho⟩ := hstep
    cases res <;> cases ho
    obtain ⟨xs, hx, hcov⟩ := authenticated_belt_step_core_trace m next inp _ hr
    obtain ⟨ys, hy, hrest⟩ := ih
    refine ⟨xs ++ ys, belt_core_trace_append hx hy, ?_⟩
    intro p hp g hg
    simp only [mirAcceptedPairs, List.mem_cons] at hp
    rcases hp with rfl | hp
    · obtain ⟨cp, hc, he⟩ := hcov g (congrArg core.result.Result.Ok hg)
      exact ⟨cp, List.mem_append_left ys hc, he⟩
    · obtain ⟨cp, hc, he⟩ := hrest p hp g hg
      exact ⟨cp, List.mem_append_right xs hc, he⟩
  | @reject m m' mf inp err rest hstep htail ih =>
    simp only [adaptStateResult, result_bind_ok_iff] at hstep
    obtain ⟨⟨next, res⟩, hr, ho⟩ := hstep
    cases res <;> cases ho
    obtain ⟨xs, hx, _⟩ := authenticated_belt_step_core_trace m next inp _ hr
    obtain ⟨ys, hy, hrest⟩ := ih
    refine ⟨xs ++ ys, belt_core_trace_append hx hy, ?_⟩
    intro p hp g hg
    obtain ⟨cp, hc, he⟩ := hrest p hp g hg
    exact ⟨cp, List.mem_append_right xs hc, he⟩

private theorem belt_core_trace_committee
    {st final : pants_and_quorum_guards.BeltQuorumCore}
    {pairs : List (pants_and_quorum_guards.BeltQuorumCoreInput × pants_and_quorum_guards.BeltQuorumCoreOutput)}
    (ht : beltQuorumMealy.ValidTrace st pairs final) : final.n = st.n := by
  induction ht with
  | nil _ => rfl
  | @accept st next final inp out rest hs ht ih =>
    have hn : next.n = st.n := by
      cases inp <;> dsimp only [beltQuorumMealy] at hs
      repeat (any_goals first | (split at hs) | simp only [reduceCtorEq] at hs)
      all_goals cases hs <;> rfl
    exact ih.trans hn
  | @reject st final inp rest hs ht ih =>
    have hn : (beltQuorumMealy.errStep st inp).n = st.n := by
      cases inp <;> dsimp only [beltQuorumMealy]
      repeat (any_goals split)
      all_goals rfl
    exact ih.trans hn

theorem authenticated_belt_step_committee_unchanged
    (st st' : authenticated_belt.VerifiedBeltQuorumGuard)
    (inp : authenticated_belt.BeltQuorumStepInput)
    (r : core.result.Result authenticated_belt.BeltQuorumStepOutput authenticated_belt.BeltAuthError)
    (h : authenticated_belt.VerifiedBeltQuorumGuard.step st inp = .ok (st', r)) : st'.inner.n = st.inner.n := by
  obtain ⟨_, ht, _⟩ := authenticated_belt_step_core_trace st st' inp r h
  exact belt_core_trace_committee ht

private theorem authenticated_belt_step_ack_range
    (st st' : authenticated_belt.VerifiedBeltQuorumGuard)
    (ep : Std.U64) (msg tag : Array Std.U8 32#usize) (id : Std.U8)
    (out : authenticated_belt.BeltQuorumStepOutput)
    (h : authenticated_belt.VerifiedBeltQuorumGuard.step st (.RecordCustodianAck ep msg id tag) = .ok (st', .Ok out)) :
    id.val < st.inner.n.val := by
  unfold authenticated_belt.VerifiedBeltQuorumGuard.step at h
  cases he : authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack st ep msg id tag with
  | fail e => simp [he, bind_eq_result_bind, Result.bind] at h
  | div => simp [he, bind_eq_result_bind, Result.bind] at h
  | ok v =>
    rcases v with ⟨next, res⟩
    cases res with
    | Err e => simp [he, bind_eq_result_bind, Result.bind] at h
    | Ok count => exact (authenticated_belt_accepted_ack_tag st next ep msg tag id count he).1

theorem authenticated_belt_trace_ack_range
    {st st_final : authenticated_belt.VerifiedBeltQuorumGuard}
    {turns : List (MirTurn authenticated_belt.BeltQuorumStepInput
      authenticated_belt.BeltQuorumStepOutput authenticated_belt.BeltAuthError)}
    (htrace : MirTrace (adaptStateResult authenticated_belt.VerifiedBeltQuorumGuard.step)
      st turns st_final) :
    ∀ p ∈ mirAcceptedPairs turns, ∀ ep msg id tag,
      p.1 = .RecordCustodianAck ep msg id tag → id.val < st.inner.n.val := by
  induction htrace with
  | nil _ => intro p hp; exact False.elim (List.not_mem_nil hp)
  | @accept m m' mf inp out rest hstep htail ih =>
    simp only [adaptStateResult, result_bind_ok_iff] at hstep
    obtain ⟨⟨next, res⟩, hr, ho⟩ := hstep
    cases res <;> cases ho
    have hn := authenticated_belt_step_committee_unchanged m next inp _ hr
    intro p hp ep msg id tag hin
    simp only [mirAcceptedPairs, List.mem_cons] at hp
    rcases hp with rfl | hp
    · cases hin
      exact authenticated_belt_step_ack_range m next ep msg tag id out hr
    · rw [← hn]
      exact ih p hp ep msg id tag hin
  | @reject m m' mf inp err rest hstep htail ih =>
    simp only [adaptStateResult, result_bind_ok_iff] at hstep
    obtain ⟨⟨next, res⟩, hr, ho⟩ := hstep
    cases res <;> cases ho
    have hn := authenticated_belt_step_committee_unchanged m next inp _ hr
    intro p hp ep msg id tag hin
    rw [← hn]
    exact ih p hp ep msg id tag hin

private theorem authenticated_belt_new_facts
    (n t f q : Std.U32) (gl : Bool) (epoch window : Std.U64)
    (commit wal : Array Std.U8 32#usize) (keys : Array (Array Std.U8 32#usize) 64#usize)
    (st : authenticated_belt.VerifiedBeltQuorumGuard)
    (h : authenticated_belt.VerifiedBeltQuorumGuard.new_validated n t f q gl epoch window commit keys wal =
      .ok (.Ok st)) :
    ValidBeltQuorumConfigProp n t f q gl ∧ n.val ≤ 64 ∧
    BeltStateInv n t f q gl epoch.val st.inner ∧
    st.guard_key_commit = commit ∧ st.custodian_keys = keys ∧ st.wal_key = wal := by
  by_cases hn : n > 64#u32
  · simp [authenticated_belt.VerifiedBeltQuorumGuard.new_validated, hn] at h
  · by_cases hv : validBeltQuorumConfigBool n t f q gl = true
    · simp [authenticated_belt.VerifiedBeltQuorumGuard.new_validated, hn,
        pants_and_quorum_guards.BeltQuorumCore.new_validated,
        validate_belt_quorum_config_eq, hv] at h
      cases h
      refine ⟨(validBeltQuorumConfigBool_iff n t f q gl).mp hv,
        Nat.le_of_not_gt hn, ?_, rfl, rfl, rfl⟩
      exact ⟨rfl, rfl, rfl, rfl, rfl, hv, Nat.le_refl _, Nat.zero_le _,
        fun h => Bool.noConfusion h, fun _ => rfl⟩
    · simp [authenticated_belt.VerifiedBeltQuorumGuard.new_validated, hn,
        pants_and_quorum_guards.BeltQuorumCore.new_validated,
        validate_belt_quorum_config_eq, hv] at h

/-- Authenticated multi-turn soundness, including rejected state transitions and duplicate
acknowledgments. The cardinality invariant counts distinct bitmap positions; this theorem
alone does not yet locate the historical acknowledgment turns backing each grant. -/
theorem authenticated_belt_quorum_guard_multiturn_sound
    (n t f q : Std.U32) (gl : Bool) (initial_next_epoch max_jump_window : Std.U64)
    (commit wal : Array Std.U8 32#usize) (keys : Array (Array Std.U8 32#usize) 64#usize)
    (st0 st_final : authenticated_belt.VerifiedBeltQuorumGuard)
    (turns : List (MirTurn authenticated_belt.BeltQuorumStepInput
      authenticated_belt.BeltQuorumStepOutput authenticated_belt.BeltAuthError))
    (hnew : authenticated_belt.VerifiedBeltQuorumGuard.new_validated n t f q gl
      initial_next_epoch max_jump_window commit keys wal = .ok (.Ok st0))
    (htrace : MirTrace (adaptStateResult authenticated_belt.VerifiedBeltQuorumGuard.step)
      st0 turns st_final) :
    ValidBeltQuorumConfigProp n t f q gl ∧ n.val ≤ 64 ∧
    (∀ p ∈ mirAcceptedPairs turns, ∀ ep msg digest tag,
      p.1 = .ProposeOrRetryEpoch ep msg digest tag →
      authenticated_belt.wal_receipt_tag wal commit ep msg digest = .ok tag) ∧
    (∀ p ∈ mirAcceptedPairs turns, ∀ ep msg id tag,
      p.1 = .RecordCustodianAck ep msg id tag →
      id.val < n.val ∧ id.val < 64 ∧
      ∃ key, Array.index_usize keys (UScalar.cast .Usize id) = .ok key ∧
        authenticated_belt.custodian_ack_tag key commit ep msg id = .ok tag) ∧
    (∀ p ∈ mirAcceptedPairs turns, ∀ g, p.2 = .SharesAuthorized g →
      q.val ≤ g.certified_acks.val ∧ g.certified_acks.val ≤ n.val ∧
      initial_next_epoch.val ≤ g.authorized_epoch.val) ∧
    (∀ p1 ∈ mirAcceptedPairs turns, ∀ p2 ∈ mirAcceptedPairs turns, ∀ g1 g2,
      p1.2 = .SharesAuthorized g1 → p2.2 = .SharesAuthorized g2 →
      g1.authorized_epoch = g2.authorized_epoch → g1.msg_tag = g2.msg_tag) ∧
    BeltAckCountInvariant st_final := by
  obtain ⟨hcfg, hn, hinv, hcommit, hkeys, hwal⟩ :=
    authenticated_belt_new_facts n t f q gl initial_next_epoch max_jump_window commit wal keys st0 hnew
  obtain ⟨pairs, ht, hcover⟩ := authenticated_belt_trace_core_projection htrace
  have hgrant := belt_grants_above_floor hinv ht
  have hneq := (belt_validTrace_non_equivocation hinv ht).2
  have hmac := authenticated_belt_trace_mac_valid htrace
  rw [hcommit, hkeys, hwal] at hmac
  have hrange := authenticated_belt_trace_ack_range htrace
  rw [hinv.1] at hrange
  refine ⟨hcfg, hn, ?_, ?_, ?_, ?_,
    authenticated_belt_trace_preserves_count htrace
      (authenticated_belt_initial_count_invariant n t f q gl initial_next_epoch max_jump_window
        commit wal keys st0 hnew)⟩
  · intro p hp ep msg digest tag hi
    have hm := hmac p hp
    rw [hi] at hm
    exact hm
  · intro p hp ep msg id tag hi
    have hm := hmac p hp
    rw [hi] at hm
    exact ⟨hrange p hp ep msg id tag hi, hm⟩
  · intro p hp g hg
    obtain ⟨cp, hcp, hc⟩ := hcover p hp g hg
    exact hgrant cp hcp g hc
  · intro p1 hp1 p2 hp2 g1 g2 hg1 hg2 hep
    obtain ⟨cp1, hcp1, hc1⟩ := hcover p1 hp1 g1 hg1
    obtain ⟨cp2, hcp2, hc2⟩ := hcover p2 hp2 g2 hg2
    exact hneq cp1 hcp1 cp2 hcp2 g1 g2 hc1 hc2 hep

/-- Explicit enrollment trust strengthens actual accepted acknowledgments to nonzero,
pairwise-distinct slot keys. Historical grant backing is a separate obligation. -/
theorem authenticated_belt_provisioned_trace_ack_keys
    (n t f q : Std.U32) (gl : Bool) (initial_next_epoch max_jump_window : Std.U64)
    (commit wal : Array Std.U8 32#usize) (keys : Array (Array Std.U8 32#usize) 64#usize)
    (st0 st_final : authenticated_belt.VerifiedBeltQuorumGuard)
    (turns : List (MirTurn authenticated_belt.BeltQuorumStepInput
      authenticated_belt.BeltQuorumStepOutput authenticated_belt.BeltAuthError))
    (hnew : authenticated_belt.VerifiedBeltQuorumGuard.new_validated n t f q gl
      initial_next_epoch max_jump_window commit keys wal = .ok (.Ok st0))
    (htrace : MirTrace (adaptStateResult authenticated_belt.VerifiedBeltQuorumGuard.step)
      st0 turns st_final) (hkeys : BeltProvisionedKeys n keys) :
    (∀ p ∈ mirAcceptedPairs turns, ∀ ep msg id tag,
      p.1 = .RecordCustodianAck ep msg id tag →
      ∃ key, Array.index_usize keys (UScalar.cast .Usize id) = .ok key ∧
        authenticated_belt.custodian_ack_tag key commit ep msg id = .ok tag ∧
        key ≠ Array.repeat 32#usize 0#u8) ∧
    (∀ p1 ∈ mirAcceptedPairs turns, ∀ p2 ∈ mirAcceptedPairs turns,
      ∀ ep1 msg1 id1 tag1 ep2 msg2 id2 tag2,
      p1.1 = .RecordCustodianAck ep1 msg1 id1 tag1 →
      p2.1 = .RecordCustodianAck ep2 msg2 id2 tag2 → id1 ≠ id2 →
      ∃ key1 key2,
        Array.index_usize keys (UScalar.cast .Usize id1) = .ok key1 ∧
        Array.index_usize keys (UScalar.cast .Usize id2) = .ok key2 ∧
        authenticated_belt.custodian_ack_tag key1 commit ep1 msg1 id1 = .ok tag1 ∧
        authenticated_belt.custodian_ack_tag key2 commit ep2 msg2 id2 = .ok tag2 ∧
        key1 ≠ Array.repeat 32#usize 0#u8 ∧ key2 ≠ Array.repeat 32#usize 0#u8 ∧ key1 ≠ key2) := by
  obtain ⟨_, _, _, hacks, _, _, _⟩ := authenticated_belt_quorum_guard_multiturn_sound
    n t f q gl initial_next_epoch max_jump_window commit wal keys st0 st_final turns hnew htrace
  constructor
  · intro p hp ep msg id tag hi
    obtain ⟨hn, _, key, hk, ht⟩ := hacks p hp ep msg id tag hi
    exact ⟨key, hk, ht, hkeys.1 id key hn hk⟩
  · intro p1 hp1 p2 hp2 ep1 msg1 id1 tag1 ep2 msg2 id2 tag2 hi1 hi2 hne
    obtain ⟨hn1, _, key1, hk1, ht1⟩ := hacks p1 hp1 ep1 msg1 id1 tag1 hi1
    obtain ⟨hn2, _, key2, hk2, ht2⟩ := hacks p2 hp2 ep2 msg2 id2 tag2 hi2
    exact ⟨key1, key2, hk1, hk2, ht1, ht2,
      hkeys.1 id1 key1 hn1 hk1, hkeys.1 id2 key2 hn2 hk2,
      fun he => hne (hkeys.2 id1 id2 key1 key2 hn1 hn2 hk1 hk2 he)⟩

private theorem authenticated_belt_ack_core_projection_strict
    (st st' : authenticated_belt.VerifiedBeltQuorumGuard)
    (ep : Std.U64) (msg tag : Array Std.U8 32#usize) (id : Std.U8)
    (r : core.result.Result Std.U32 authenticated_belt.BeltAuthError)
    (h : authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack st ep msg id tag =
      .ok (st', r)) :
    (st' = st ∧ ((∃ e, r = .Err e) ∨ r = .Ok st.inner.ack_count)) ∨ ∃ cr, pants_and_quorum_guards.BeltQuorumCore.record_custodian_ack
      st.inner ep msg = .ok (st'.inner, cr) := by
  unfold authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack at h
  simp only [bind_eq_result_bind, result_bind_ok, lift,
    pants_and_quorum_guards.BeltQuorumCore.impl.n,
    pants_and_quorum_guards.BeltQuorumCore.impl.has_bound_epoch,
    pants_and_quorum_guards.BeltQuorumCore.impl.bound_epoch,
    pants_and_quorum_guards.BeltQuorumCore.impl.bound_msg_tag,
    pants_and_quorum_guards.BeltQuorumCore.impl.ack_count,
    pants_and_quorum_guards.BeltQuorumCore.is_poisoned] at h
  repeat (any_goals first
    | simp only [result_bind_ok_iff] at h
    | (obtain ⟨v, hv, h⟩ : ∃ v, _ ∧ _ := h)
    | (split at h))
  all_goals cases h
  all_goals first
    | (apply Or.inr; exact ⟨_, by assumption⟩)
    | (apply Or.inl; refine ⟨rfl, ?_⟩; first | exact Or.inl ⟨_, rfl⟩ | exact Or.inr rfl)

/-- The named core input corresponding to a wrapper call. Proposal receipt validity is
computed by the extracted WAL tag function, rather than supplied as an independent flag. -/
@[expose]
def BeltCoreInputFor (st : authenticated_belt.VerifiedBeltQuorumGuard)
    (inp : authenticated_belt.BeltQuorumStepInput)
    (ci : pants_and_quorum_guards.BeltQuorumCoreInput) : Prop :=
  match inp with
  | .ProposeOrRetryEpoch ep msg digest tag =>
    ∃ expected, authenticated_belt.wal_receipt_tag st.wal_key st.guard_key_commit ep msg digest = .ok expected ∧
      ci = .ProposeOrRetryEpoch ep msg (decide (expected = tag))
  | .RecordCustodianAck ep msg _ _ => ci = .RecordCustodianAck ep msg
  | .AuthorizeShares ep msg => ci = .AuthorizeShares ep msg

theorem authenticated_belt_step_core_projection
    (st st' : authenticated_belt.VerifiedBeltQuorumGuard)
    (inp : authenticated_belt.BeltQuorumStepInput)
    (r : core.result.Result authenticated_belt.BeltQuorumStepOutput authenticated_belt.BeltAuthError)
    (h : authenticated_belt.VerifiedBeltQuorumGuard.step st inp = .ok (st', r)) :
    BeltEnrollmentUnchanged st st' ∧
    ((st' = st ∧ ((∃ e, r = .Err e) ∨ r = .Ok (.AckRecorded st.inner.ack_count))) ∨
      ∃ ci cr, BeltCoreInputFor st inp ci ∧
        pants_and_quorum_guards.BeltQuorumCore.step st.inner ci = .ok (st'.inner, cr)) := by
  refine ⟨authenticated_belt_step_enrollment_unchanged st st' inp r h, ?_⟩
  cases inp with
  | ProposeOrRetryEpoch ep msg digest tag =>
    unfold authenticated_belt.VerifiedBeltQuorumGuard.step at h
    cases he : authenticated_belt.VerifiedBeltQuorumGuard.propose_or_retry_epoch st ep msg digest tag with
    | fail e => simp [he, bind_eq_result_bind, Result.bind] at h
    | div => simp [he, bind_eq_result_bind, Result.bind] at h
    | ok v =>
      rcases v with ⟨next, res⟩
      obtain ⟨expected, cr, hw, hc⟩ := authenticated_belt_propose_core_projection st next ep msg digest tag res he
      have hcore : ∃ out, pants_and_quorum_guards.BeltQuorumCore.step st.inner
          (.ProposeOrRetryEpoch ep msg (decide (expected = tag))) = .ok (next.inner, out) := by
        cases cr <;> exact ⟨_, by simp only [pants_and_quorum_guards.BeltQuorumCore.step, hc,
          bind_eq_result_bind, result_bind_ok]; rfl⟩
      obtain ⟨out, hout⟩ := hcore
      cases res <;> simp [he, bind_eq_result_bind, Result.bind] at h <;> rcases h with ⟨rfl, rfl⟩
      all_goals exact Or.inr ⟨_, out, ⟨expected, hw, rfl⟩, hout⟩
  | AuthorizeShares ep msg =>
    unfold authenticated_belt.VerifiedBeltQuorumGuard.step at h
    cases he : authenticated_belt.VerifiedBeltQuorumGuard.authorize_shares st ep msg with
    | fail e => simp [he, bind_eq_result_bind, Result.bind] at h
    | div => simp [he, bind_eq_result_bind, Result.bind] at h
    | ok v =>
      rcases v with ⟨next, res⟩
      obtain ⟨cr, hc⟩ := authenticated_belt_authorize_core_projection st next ep msg res he
      have hcore : ∃ out, pants_and_quorum_guards.BeltQuorumCore.step st.inner
          (.AuthorizeShares ep msg) = .ok (next.inner, out) := by
        cases cr <;> exact ⟨_, by simp only [pants_and_quorum_guards.BeltQuorumCore.step, hc,
          bind_eq_result_bind, result_bind_ok]; rfl⟩
      obtain ⟨out, hout⟩ := hcore
      cases res <;> simp [he, bind_eq_result_bind, Result.bind] at h <;> rcases h with ⟨rfl, rfl⟩
      all_goals exact Or.inr ⟨_, out, rfl, hout⟩
  | RecordCustodianAck ep msg id tag =>
    unfold authenticated_belt.VerifiedBeltQuorumGuard.step at h
    cases he : authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack st ep msg id tag with
    | fail e => simp [he, bind_eq_result_bind, Result.bind] at h
    | div => simp [he, bind_eq_result_bind, Result.bind] at h
    | ok v =>
      rcases v with ⟨next, res⟩
      rcases authenticated_belt_ack_core_projection_strict st next ep msg tag id res he with
        ⟨hn, hdup⟩ | ⟨cr, hc⟩
      · subst next
        cases res with
        | Err e =>
          simp [he, bind_eq_result_bind, Result.bind] at h
          rcases h with ⟨rfl, rfl⟩
          exact Or.inl ⟨rfl, Or.inl ⟨e, rfl⟩⟩
        | Ok c =>
          rcases hdup with ⟨e, heq⟩ | heq
          · cases heq
          · cases heq
            simp [he, bind_eq_result_bind, Result.bind] at h
            rcases h with ⟨rfl, rfl⟩
            exact Or.inl ⟨rfl, Or.inr rfl⟩
      · have hcore : ∃ out, pants_and_quorum_guards.BeltQuorumCore.step st.inner
            (.RecordCustodianAck ep msg) = .ok (next.inner, out) := by
          cases cr <;> exact ⟨_, by simp only [pants_and_quorum_guards.BeltQuorumCore.step, hc,
            bind_eq_result_bind, result_bind_ok]; rfl⟩
        obtain ⟨out, hout⟩ := hcore
        cases res <;> simp [he, bind_eq_result_bind, Result.bind] at h <;> rcases h with ⟨rfl, rfl⟩
        all_goals exact Or.inr ⟨_, out, rfl, hout⟩

end qsag_verified.proofs
