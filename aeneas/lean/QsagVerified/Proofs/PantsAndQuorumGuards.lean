module

public import QsagVerified.Proofs.Common
public import QsagVerified.Proofs.MirRefinementKit
public import QsagVerified.Proofs.Wots
public import QsagVerified.Proofs.FtsSpnGuard

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
