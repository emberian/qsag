module

public import QsagVerified.Proofs.Common
public import QsagVerified.Proofs.MirRefinementKit
public import QsagVerified.Proofs.Goldilocks

public section

namespace qsag_verified.proofs

open Aeneas Aeneas.Std Result ControlFlow Error
open qsag_verified

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

attribute [-simp] BitVec.getLsbD_eq_getElem
attribute [local simp] UScalar.val UScalarTy.numBits

private theorem map_id_pair {α β : Type} :
    ∀ (xs : List (α × β)), xs.map (fun p => (id p.1, id p.2)) = xs
  | [] => rfl
  | (_, _) :: rest => congrArg (_ :: ·) (map_id_pair rest)

/-! ## 1. ML-DSA-44 Eta-2 Nibble Rejection Sampler & Norm Bounds -/

theorem mldsa44_eta2_nibble_uniform_spec (nibble : Std.U8) :
    (15 ≤ nibble.val → cred_and_hd_guards.mldsa44_sample_eta2_nibble_mod_q nibble = .ok none) ∧
    (nibble.val < 15 →
      ∃ out : Std.U32,
        cred_and_hd_guards.mldsa44_sample_eta2_nibble_mod_q nibble = .ok (some out) ∧
        out.val = (8380417 + 2 - nibble.val % 5) % 8380417 ∧
        (out = 2#u32 ∨ out = 1#u32 ∨ out = 0#u32 ∨ out = 8380416#u32 ∨ out = 8380415#u32)) := by
  constructor
  · intro hge
    have hge_u8 : nibble >= 15#u8 := (UScalar.le_iff_val _ _).mpr hge
    unfold cred_and_hd_guards.mldsa44_sample_eta2_nibble_mod_q
    simp [hge_u8]
  · intro hlt
    unfold cred_and_hd_guards.mldsa44_sample_eta2_nibble_mod_q cred_and_hd_guards.MLDSA_Q
    match h : nibble.val, hlt with
    | 0, _ =>
      have hn : nibble = 0#u8 := UScalar.eq_of_val_eq h
      subst hn; refine ⟨2#u32, by decide, by decide, Or.inl rfl⟩
    | 1, _ =>
      have hn : nibble = 1#u8 := UScalar.eq_of_val_eq h
      subst hn; refine ⟨1#u32, by decide, by decide, Or.inr (Or.inl rfl)⟩
    | 2, _ =>
      have hn : nibble = 2#u8 := UScalar.eq_of_val_eq h
      subst hn; refine ⟨0#u32, by decide, by decide, Or.inr (Or.inr (Or.inl rfl))⟩
    | 3, _ =>
      have hn : nibble = 3#u8 := UScalar.eq_of_val_eq h
      subst hn; refine ⟨8380416#u32, by decide, by decide, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
    | 4, _ =>
      have hn : nibble = 4#u8 := UScalar.eq_of_val_eq h
      subst hn; refine ⟨8380415#u32, by decide, by decide, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩
    | 5, _ =>
      have hn : nibble = 5#u8 := UScalar.eq_of_val_eq h
      subst hn; refine ⟨2#u32, by decide, by decide, Or.inl rfl⟩
    | 6, _ =>
      have hn : nibble = 6#u8 := UScalar.eq_of_val_eq h
      subst hn; refine ⟨1#u32, by decide, by decide, Or.inr (Or.inl rfl)⟩
    | 7, _ =>
      have hn : nibble = 7#u8 := UScalar.eq_of_val_eq h
      subst hn; refine ⟨0#u32, by decide, by decide, Or.inr (Or.inr (Or.inl rfl))⟩
    | 8, _ =>
      have hn : nibble = 8#u8 := UScalar.eq_of_val_eq h
      subst hn; refine ⟨8380416#u32, by decide, by decide, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
    | 9, _ =>
      have hn : nibble = 9#u8 := UScalar.eq_of_val_eq h
      subst hn; refine ⟨8380415#u32, by decide, by decide, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩
    | 10, _ =>
      have hn : nibble = 10#u8 := UScalar.eq_of_val_eq h
      subst hn; refine ⟨2#u32, by decide, by decide, Or.inl rfl⟩
    | 11, _ =>
      have hn : nibble = 11#u8 := UScalar.eq_of_val_eq h
      subst hn; refine ⟨1#u32, by decide, by decide, Or.inr (Or.inl rfl)⟩
    | 12, _ =>
      have hn : nibble = 12#u8 := UScalar.eq_of_val_eq h
      subst hn; refine ⟨0#u32, by decide, by decide, Or.inr (Or.inr (Or.inl rfl))⟩
    | 13, _ =>
      have hn : nibble = 13#u8 := UScalar.eq_of_val_eq h
      subst hn; refine ⟨8380416#u32, by decide, by decide, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
    | 14, _ =>
      have hn : nibble = 14#u8 := UScalar.eq_of_val_eq h
      subst hn; refine ⟨8380415#u32, by decide, by decide, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩
    | k + 15, hk =>
      exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 15 k) hk)

theorem check_mldsa44_norm_bounds_spec (z_inf r0_inf : Std.U32) :
    cred_and_hd_guards.check_mldsa44_norm_bounds z_inf r0_inf =
      .ok (decide (z_inf.val < 130994), decide (r0_inf.val < 95154)) := by
  unfold cred_and_hd_guards.check_mldsa44_norm_bounds
    cred_and_hd_guards.MLDSA44_Z_NORM_BOUND
    cred_and_hd_guards.MLDSA44_R0_NORM_BOUND
  by_cases hz : z_inf < 130994#u32 <;> by_cases hr : r0_inf < 95154#u32
  · have hzv : z_inf.val < 130994 := (UScalar.lt_iff_val _ _).mp hz
    have hrv : r0_inf.val < 95154 := (UScalar.lt_iff_val _ _).mp hr
    simp [hz, hr, hzv, hrv]
  · have hzv : z_inf.val < 130994 := (UScalar.lt_iff_val _ _).mp hz
    have hrv : ¬ r0_inf.val < 95154 := fun h => hr ((UScalar.lt_iff_val _ _).mpr h)
    simp [hz, hr, hzv, hrv]
  · have hzv : ¬ z_inf.val < 130994 := fun h => hz ((UScalar.lt_iff_val _ _).mpr h)
    have hrv : r0_inf.val < 95154 := (UScalar.lt_iff_val _ _).mp hr
    simp [hz, hr, hzv, hrv]
  · have hzv : ¬ z_inf.val < 130994 := fun h => hz ((UScalar.lt_iff_val _ _).mpr h)
    have hrv : ¬ r0_inf.val < 95154 := fun h => hr ((UScalar.lt_iff_val _ _).mpr h)
    simp [hz, hr, hzv, hrv]

theorem check_mldsa65_norm_bounds_spec (z_inf r0_inf : Std.U32) :
    cred_and_hd_guards.check_mldsa65_norm_bounds z_inf r0_inf =
      .ok (decide (z_inf.val < 524092), decide (r0_inf.val < 261692)) := by
  unfold cred_and_hd_guards.check_mldsa65_norm_bounds
    cred_and_hd_guards.MLDSA65_Z_NORM_BOUND
    cred_and_hd_guards.MLDSA65_R0_NORM_BOUND
  by_cases hz : z_inf < 524092#u32 <;> by_cases hr : r0_inf < 261692#u32
  · have hzv : z_inf.val < 524092 := (UScalar.lt_iff_val _ _).mp hz
    have hrv : r0_inf.val < 261692 := (UScalar.lt_iff_val _ _).mp hr
    simp [hz, hr, hzv, hrv]
  · have hzv : z_inf.val < 524092 := (UScalar.lt_iff_val _ _).mp hz
    have hrv : ¬ r0_inf.val < 261692 := fun h => hr ((UScalar.lt_iff_val _ _).mpr h)
    simp [hz, hr, hzv, hrv]
  · have hzv : ¬ z_inf.val < 524092 := fun h => hz ((UScalar.lt_iff_val _ _).mpr h)
    have hrv : r0_inf.val < 261692 := (UScalar.lt_iff_val _ _).mp hr
    simp [hz, hr, hzv, hrv]
  · have hzv : ¬ z_inf.val < 524092 := fun h => hz ((UScalar.lt_iff_val _ _).mpr h)
    have hrv : ¬ r0_inf.val < 261692 := fun h => hr ((UScalar.lt_iff_val _ _).mpr h)
    simp [hz, hr, hzv, hrv]

/-! ## 2. Threshold ML-DSA Rejection-Sampling Release Gate (1-Step & Multi-Turn MIR) -/

@[expose]
def mlDsaBarrierPassBool (st : cred_and_hd_guards.MlDsaReleaseGate)
    (c : cred_and_hd_guards.MlDsaBarrierChecks) : Bool :=
  (!st.aborted) && (!st.released) &&
  decide (st.session_id = c.req_session_id) &&
  decide (st.attempt = c.req_attempt) &&
  c.z_norm_ok && c.r0_norm_ok && c.w1_match && c.u_com_bound

@[expose]
def mlDsaGateMealy :
    MealySpec cred_and_hd_guards.MlDsaReleaseGate
      cred_and_hd_guards.MlDsaBarrierChecks (Array Std.U8 32#usize) where
  step st c :=
    if mlDsaBarrierPassBool st c then
      some ({ st with z_share_masked := Array.repeat 32#usize 0#u8, released := true },
        st.z_share_masked)
    else
      none
  errStep st _ :=
    { session_id := st.session_id
      attempt := st.attempt
      z_share_masked := Array.repeat 32#usize 0#u8
      released := false
      aborted := true }

private theorem mldsa_gate_try_release_exact (st : cred_and_hd_guards.MlDsaReleaseGate)
    (c : cred_and_hd_guards.MlDsaBarrierChecks) :
    (mlDsaBarrierPassBool st c = true →
      cred_and_hd_guards.MlDsaReleaseGate.try_release_z_share st c =
        .ok ({ st with z_share_masked := Array.repeat 32#usize 0#u8, released := true },
          .Ok st.z_share_masked)) ∧
    (mlDsaBarrierPassBool st c = false →
      ∃ err, cred_and_hd_guards.MlDsaReleaseGate.try_release_z_share st c =
        .ok (mlDsaGateMealy.errStep st c, .Err err)) := by
  unfold cred_and_hd_guards.MlDsaReleaseGate.try_release_z_share
    cred_and_hd_guards.abort_mldsa_gate mlDsaBarrierPassBool mlDsaGateMealy
  rw [ct_eq_bytes32_spec]
  cases ha : st.aborted <;> cases hr : st.released
  · by_cases hsid : st.session_id = c.req_session_id
    · by_cases hatt : st.attempt = c.req_attempt
      · cases hz : c.z_norm_ok <;> cases hr0 : c.r0_norm_ok <;>
          cases hw1 : c.w1_match <;> cases hu : c.u_com_bound <;>
          simp [hsid, hatt, bind_eq_result_bind, result_bind_ok]
      · have hne : (st.attempt != c.req_attempt) = true := by simp [hatt]
        simp [hsid, hatt, hne, bind_eq_result_bind, result_bind_ok]
    · simp [hsid, bind_eq_result_bind, result_bind_ok]
  · simp [bind_eq_result_bind, result_bind_ok]
  · simp [bind_eq_result_bind, result_bind_ok]
  · simp [bind_eq_result_bind, result_bind_ok]

theorem mldsa_gate_step_sim :
    MirStepSim mlDsaGateMealy
      (adaptStateResult cred_and_hd_guards.MlDsaReleaseGate.try_release_z_share)
      Eq (fun a b => a = id b) (fun a b => a = id b) where
  ok_sim {s m m' i_s i_m o_m} hSt hIn hStep := by
    subst m; dsimp only [id] at hIn; subst i_s
    dsimp only [adaptStateResult] at hStep ⊢
    obtain ⟨hPass, hFail⟩ := mldsa_gate_try_release_exact s i_m
    cases hb : mlDsaBarrierPassBool s i_m
    · obtain ⟨err, herr⟩ := hFail hb
      rw [herr] at hStep
      cases hStep
    · have hok := hPass hb
      rw [hok] at hStep
      simp only [Result.bind] at hStep
      injection hStep with hAcc
      cases hAcc
      dsimp only [mlDsaGateMealy]
      rw [hb]
      exact ⟨rfl, rfl⟩
  err_preserves {s m m' i_s i_m e} hSt hIn hStep := by
    subst m; dsimp only [id] at hIn; subst i_s
    dsimp only [adaptStateResult] at hStep ⊢
    obtain ⟨hPass, hFail⟩ := mldsa_gate_try_release_exact s i_m
    cases hb : mlDsaBarrierPassBool s i_m
    · obtain ⟨err, herr⟩ := hFail hb
      rw [herr] at hStep
      simp only [Result.bind] at hStep
      injection hStep with hRej
      cases hRej
      dsimp only [mlDsaGateMealy]
      rw [hb]
      exact ⟨rfl, rfl⟩
    · have hok := hPass hb
      rw [hok] at hStep
      cases hStep

private theorem mldsa_done_no_more_accepts
    {s s_f : cred_and_hd_guards.MlDsaReleaseGate}
    {trace : List (cred_and_hd_guards.MlDsaBarrierChecks × Array Std.U8 32#usize)}
    (hDone : s.aborted = true ∨ s.released = true)
    (hTr : mlDsaGateMealy.ValidTrace s trace s_f) :
    trace = [] := by
  induction hTr with
  | nil _ => rfl
  | @accept st st' _ inp out _ hStep _ _ =>
    dsimp only [mlDsaGateMealy] at hStep
    cases hb : mlDsaBarrierPassBool st inp
    · rw [hb] at hStep; cases hStep
    · unfold mlDsaBarrierPassBool at hb
      rcases hDone with hab | hrel
      · simp [hab] at hb
      · simp [hrel] at hb
  | reject _ _ _ ih =>
    exact ih (Or.inl rfl)

private theorem mldsa_sealed_spec_trace_safe
    (sid : Array Std.U8 32#usize) (attempt : Std.U32) (z_masked : Array Std.U8 32#usize)
    {trace : List (cred_and_hd_guards.MlDsaBarrierChecks × Array Std.U8 32#usize)}
    {s_f : cred_and_hd_guards.MlDsaReleaseGate}
    (hTr : mlDsaGateMealy.ValidTrace
      { session_id := sid, attempt := attempt, z_share_masked := z_masked,
        released := false, aborted := false }
      trace s_f) :
    trace.length ≤ 1 ∧
    ∀ p ∈ trace,
      p.1.req_session_id = sid ∧ p.1.req_attempt = attempt ∧
      p.1.z_norm_ok = true ∧ p.1.r0_norm_ok = true ∧
      p.1.w1_match = true ∧ p.1.u_com_bound = true ∧
      p.2 = z_masked := by
  generalize hs0 :
    ({ session_id := sid, attempt := attempt, z_share_masked := z_masked,
       released := false, aborted := false } : cred_and_hd_guards.MlDsaReleaseGate) = s0 at hTr
  induction hTr with
  | nil _ =>
    exact ⟨Nat.zero_le 1, fun _ hm => False.elim (List.not_mem_nil hm)⟩
  | @accept st st' _ inp out rest hStep hTail _ =>
    subst hs0
    dsimp only [mlDsaGateMealy] at hStep
    cases hb : mlDsaBarrierPassBool
      { session_id := sid, attempt := attempt, z_share_masked := z_masked,
        released := false, aborted := false } inp
    · rw [hb] at hStep; cases hStep
    · rw [hb] at hStep
      simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hStep
      rcases hStep with ⟨hst', hout⟩
      subst hst'; subst hout
      have hRestNil : rest = [] := mldsa_done_no_more_accepts (Or.inr rfl) hTail
      subst hRestNil
      unfold mlDsaBarrierPassBool at hb
      simp only [Bool.not_false, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq] at hb
      rcases hb with ⟨⟨⟨⟨⟨hsid, hatt⟩, hz⟩, hr0⟩, hw1⟩, hu⟩
      refine ⟨Nat.le_refl 1, ?_⟩
      intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      exact ⟨hsid.symm, hatt.symm, hz, hr0, hw1, hu, rfl⟩
  | reject _ _ hTail _ =>
    subst hs0
    have hRestNil : _ = [] := mldsa_done_no_more_accepts (Or.inl rfl) hTail
    rw [hRestNil]
    exact ⟨Nat.zero_le 1, fun _ hm => False.elim (List.not_mem_nil hm)⟩

theorem mldsa_gate_blocks_z_on_rejection_mir
    (sid : Array Std.U8 32#usize) (attempt : Std.U32) (z_masked : Array Std.U8 32#usize)
    (st0 st_final : cred_and_hd_guards.MlDsaReleaseGate)
    (turns : List (MirTurn cred_and_hd_guards.MlDsaBarrierChecks
      (Array Std.U8 32#usize) cred_and_hd_guards.CredHdGuardError))
    (hnew : cred_and_hd_guards.MlDsaReleaseGate.new_sealed sid attempt z_masked = .ok st0)
    (htrace : MirTrace (adaptStateResult cred_and_hd_guards.MlDsaReleaseGate.try_release_z_share)
      st0 turns st_final) :
    (∀ st c,
      (!(c.z_norm_ok && c.r0_norm_ok && c.w1_match && c.u_com_bound)) = true →
      ∃ err, cred_and_hd_guards.MlDsaReleaseGate.try_release_z_share st c =
        .ok ({ session_id := st.session_id, attempt := st.attempt,
               z_share_masked := Array.repeat 32#usize 0#u8,
               released := false, aborted := true }, .Err err)) ∧
    ((mirAcceptedPairs turns).length ≤ 1 ∧
      ∀ p ∈ mirAcceptedPairs turns,
        p.1.req_session_id = sid ∧ p.1.req_attempt = attempt ∧
        p.1.z_norm_ok = true ∧ p.1.r0_norm_ok = true ∧
        p.1.w1_match = true ∧ p.1.u_com_bound = true ∧
        p.2 = z_masked) := by
  constructor
  · intro st c hReject
    obtain ⟨_, hFail⟩ := mldsa_gate_try_release_exact st c
    apply hFail
    unfold mlDsaBarrierPassBool
    cases hz : c.z_norm_ok <;> cases hr0 : c.r0_norm_ok <;>
      cases hw1 : c.w1_match <;> cases hu : c.u_com_bound
    all_goals simp_all
  · unfold cred_and_hd_guards.MlDsaReleaseGate.new_sealed at hnew
    injection hnew with hst0
    obtain ⟨hSafe, _⟩ :=
      mldsa_gate_step_sim.lift_trace_safety_abs
        (Safe := fun pairs =>
          pairs.length ≤ 1 ∧
          ∀ p ∈ pairs,
            p.1.req_session_id = sid ∧ p.1.req_attempt = attempt ∧
            p.1.z_norm_ok = true ∧ p.1.r0_norm_ok = true ∧
            p.1.w1_match = true ∧ p.1.u_com_bound = true ∧
            p.2 = z_masked)
        (mldsa_sealed_spec_trace_safe sid attempt z_masked)
        hst0
        htrace
    rw [map_id_pair] at hSafe
    exact hSafe

/-! ## 3. 2-of-3 Goldilocks Majority Decoder (Fault Correction & Soundness) -/

private theorem ite_of_dec {α : Type} (P : Prop) [Decidable P] (a b : α) :
    (if P then a else b) = if decide P then a else b := by
  by_cases h : P <;> simp [h]

theorem toprf_majority_corrects_any_single_fault_mir :
    (∀ v : Std.U64, v.val < GoldilocksP →
      cred_and_hd_guards.toprf_majority_of_3_goldilocks v v v = .ok (some (v, none))) ∧
    (∀ v bad : Std.U64, v.val < GoldilocksP → bad ≠ v →
      cred_and_hd_guards.toprf_majority_of_3_goldilocks bad v v = .ok (some (v, some 0#u8)) ∧
      cred_and_hd_guards.toprf_majority_of_3_goldilocks v bad v = .ok (some (v, some 1#u8)) ∧
      cred_and_hd_guards.toprf_majority_of_3_goldilocks v v bad = .ok (some (v, some 2#u8))) ∧
    (∀ s0 s1 s2 out : Std.U64, ∀ cheater : Option Std.U8,
      cred_and_hd_guards.toprf_majority_of_3_goldilocks s0 s1 s2 = .ok (some (out, cheater)) →
      out.val < GoldilocksP ∧ ((s0 = out ∧ s1 = out) ∨ (s0 = out ∧ s2 = out) ∨ (s1 = out ∧ s2 = out))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    unfold cred_and_hd_guards.toprf_majority_of_3_goldilocks goldilocks.GOLDILOCKS_PRIME
    have hlt : v < 18446744069414584321#u64 := (UScalar.lt_iff_val _ _).mpr hv
    simp [hlt, bind_eq_result_bind, result_bind_ok]
  · intro v bad hv hne
    unfold cred_and_hd_guards.toprf_majority_of_3_goldilocks goldilocks.GOLDILOCKS_PRIME
    have hlt : v < 18446744069414584321#u64 := (UScalar.lt_iff_val _ _).mpr hv
    have hne' : v ≠ bad := fun h => hne h.symm
    by_cases hb : bad < 18446744069414584321#u64
    · simp [hlt, hb, hne, hne', bind_eq_result_bind, result_bind_ok]
    · simp [hlt, hb, hne, hne', bind_eq_result_bind, result_bind_ok]
  · intro s0 s1 s2 out cheater hok
    unfold cred_and_hd_guards.toprf_majority_of_3_goldilocks goldilocks.GOLDILOCKS_PRIME at hok
    simp only [ite_of_dec (s0 = s1), ite_of_dec (s0 = s2), ite_of_dec (s1 = s2)] at hok
    by_cases hc0 : s0 < 18446744069414584321#u64 <;>
      by_cases hc1 : s1 < 18446744069414584321#u64 <;>
      by_cases hc2 : s2 < 18446744069414584321#u64 <;>
      cases hb01 : decide (s0 = s1) <;>
      cases hb02 : decide (s0 = s2) <;>
      cases hb12 : decide (s1 = s2)
    all_goals
      simp only [hc0, hc1, hc2, hb01, hb02, hb12, Bool.false_eq_true, ↓reduceIte,
        bind_eq_result_bind, result_bind_ok, Result.ok.injEq,
        Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hok
    all_goals
      rcases hok with ⟨rfl, _⟩
      first
      | exact ⟨(UScalar.lt_iff_val _ _).mp hc0, Or.inl ⟨rfl, (of_decide_eq_true hb01).symm⟩⟩
      | exact ⟨(UScalar.lt_iff_val _ _).mp hc0, Or.inr (Or.inl ⟨rfl, (of_decide_eq_true hb02).symm⟩)⟩
      | exact ⟨(UScalar.lt_iff_val _ _).mp hc1, Or.inr (Or.inr ⟨rfl, (of_decide_eq_true hb12).symm⟩)⟩

/-! ## 4. Committed Zero-Test Gate (Multi-Turn Order & Quarantine Safety) -/

inductive HdZeroStepInput where
  | freezePeer (req_session_id : Array Std.U8 32#usize) (peer_commitment : Array Std.U8 32#usize)
  | openLocal (req_session_id : Array Std.U8 32#usize)
  | verifyPeer (req_session_id : Array Std.U8 32#usize)
      (recomputed_peer_commitment : Array Std.U8 32#usize) (peer_residual : Std.U32)
  deriving DecidableEq

inductive HdZeroStepOutput where
  | peerFrozen
  | localOpened (residual : Std.U32)
  | zeroVerified
  deriving DecidableEq

@[expose]
def mirHdZeroStep (st : cred_and_hd_guards.HdCommittedZeroTest) (inp : HdZeroStepInput) :
    Result (cred_and_hd_guards.HdCommittedZeroTest ×
      core.result.Result HdZeroStepOutput cred_and_hd_guards.CredHdGuardError) :=
  match inp with
  | .freezePeer req_sid peer_comm =>
    Result.bind (cred_and_hd_guards.HdCommittedZeroTest.freeze_peer_commitment st req_sid peer_comm)
      fun (st', res) =>
        match res with
        | .Ok () => .ok (st', .Ok .peerFrozen)
        | .Err e => .ok (st', .Err e)
  | .openLocal req_sid =>
    Result.bind (cred_and_hd_guards.HdCommittedZeroTest.open_local_residual st req_sid)
      fun (st', res) =>
        match res with
        | .Ok r => .ok (st', .Ok (.localOpened r))
        | .Err e => .ok (st', .Err e)
  | .verifyPeer req_sid recomputed_comm peer_res =>
    Result.bind (cred_and_hd_guards.HdCommittedZeroTest.verify_peer_opening
        st req_sid recomputed_comm peer_res)
      fun (st', res) =>
        match res with
        | .Ok () => .ok (st', .Ok .zeroVerified)
        | .Err e => .ok (st', .Err e)

@[expose]
def hdZeroMealy :
    MealySpec cred_and_hd_guards.HdCommittedZeroTest HdZeroStepInput HdZeroStepOutput where
  step st inp :=
    if st.family_quarantined then none
    else
      match inp with
      | .freezePeer req_sid peer_comm =>
        if decide (st.session_id = req_sid) then
          match st.phase with
          | .AwaitPeerCommitment =>
            some ({ st with phase := .PeerCommitmentFrozen, frozen_peer_commitment := peer_comm },
              .peerFrozen)
          | _ => none
        else none
      | .openLocal req_sid =>
        if decide (st.session_id = req_sid) then
          match st.phase with
          | .PeerCommitmentFrozen =>
            some ({ st with phase := .LocalResidualOpened }, .localOpened st.local_residual)
          | _ => none
        else none
      | .verifyPeer req_sid recomputed_comm peer_res =>
        if decide (st.session_id = req_sid) then
          match st.phase with
          | .LocalResidualOpened =>
            if decide (st.frozen_peer_commitment = recomputed_comm) &&
               decide (st.modulus_q ≠ 0#u32) &&
               decide (st.local_residual < st.modulus_q) &&
               decide (peer_res < st.modulus_q) &&
               decide ((st.local_residual.val + peer_res.val) % st.modulus_q.val = 0) then
              some ({ st with phase := .VerifiedZero, local_residual := 0#u32 }, .zeroVerified)
            else none
          | _ => none
        else none
  errStep st _ :=
    { session_id := st.session_id
      phase := .FamilyQuarantined
      frozen_peer_commitment := st.frozen_peer_commitment
      local_residual := 0#u32
      modulus_q := st.modulus_q
      family_quarantined := true }

private theorem u32_cast_u64_val (x : Std.U32) :
    (UScalar.cast .U64 x).val = x.val := by
  have hx : x.val < 2 ^ 32 := x.bv.isLt
  change (x.bv.setWidth 64).toNat = x.bv.toNat
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans hx (by decide))]

private theorem hd_verify_peer_arith_step
    (local_res peer_res q : Std.U32)
    (hq0 : q ≠ 0#u32)
    (_hl : local_res < q)
    (_hp : peer_res < q) :
    ∃ sum rem : Std.U64,
      (UScalar.cast .U64 local_res + UScalar.cast .U64 peer_res : Result Std.U64) = .ok sum ∧
      (sum % UScalar.cast .U64 q : Result Std.U64) = .ok rem ∧
      ((rem != 0#u64) = true ↔ (local_res.val + peer_res.val) % q.val ≠ 0) := by
  have hl_lt : local_res.val < 2 ^ 32 := local_res.bv.isLt
  have hp_lt : peer_res.val < 2 ^ 32 := peer_res.bv.isLt
  have hsum_bound : (UScalar.cast .U64 local_res).val + (UScalar.cast .U64 peer_res).val < 2 ^ 64 := by
    rw [u32_cast_u64_val, u32_cast_u64_val]
    exact Nat.lt_trans (Nat.add_lt_add hl_lt hp_lt) (by decide)
  obtain ⟨sum, hsum, vsum⟩ := checked_add_val (UScalar.cast .U64 local_res) (UScalar.cast .U64 peer_res) hsum_bound
  rw [u32_cast_u64_val, u32_cast_u64_val] at vsum
  let q64 := UScalar.cast .U64 q
  have vq64 : q64.val = q.val := u32_cast_u64_val q
  have hq_nz : q64.val ≠ 0 := by
    rw [vq64]
    intro hz
    exact hq0 (UScalar.eq_of_val_eq hz)
  let rem : Std.U64 := ⟨sum.bv % q64.bv⟩
  have hmod : (sum % q64 : Result Std.U64) = .ok rem := by
    rw [hMod_uscalar_eq]
    simp [hq_nz, rem]
  have vrem : rem.val = (local_res.val + peer_res.val) % q.val := by
    change (sum.bv % q64.bv).toNat = _
    rw [BitVec.toNat_umod]
    change sum.val % q64.val = _
    rw [vsum, vq64]
  refine ⟨sum, rem, hsum, hmod, ?_⟩
  constructor
  · intro hne heq
    have hr0 : rem = 0#u64 := UScalar.eq_of_val_eq (vrem.trans heq)
    rw [hr0] at hne
    simp at hne
  · intro hne
    have hr_ne : rem ≠ 0#u64 := fun h => hne (vrem.symm.trans (congrArg UScalar.val h))
    simp [hr_ne]

