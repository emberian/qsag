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

/-- Every rejected turn in the actual trace wipes the share and seals its suffix. -/
theorem mldsa_rejected_turn_wipes_and_seals
    {st st_final : cred_and_hd_guards.MlDsaReleaseGate}
    {turns : List (MirTurn cred_and_hd_guards.MlDsaBarrierChecks
      (Array Std.U8 32#usize) cred_and_hd_guards.CredHdGuardError)}
    (htrace : MirTrace (adaptStateResult cred_and_hd_guards.MlDsaReleaseGate.try_release_z_share)
      st turns st_final) :
    ∀ pre c err post, turns = pre ++ .rejected c err :: post →
      ∃ before after,
        MirTrace (adaptStateResult cred_and_hd_guards.MlDsaReleaseGate.try_release_z_share)
          st pre before ∧
        adaptStateResult cred_and_hd_guards.MlDsaReleaseGate.try_release_z_share before c =
          .ok (.rejected after err) ∧
        after.aborted = true ∧ after.z_share_masked = Array.repeat 32#usize 0#u8 ∧
        MirTrace (adaptStateResult cred_and_hd_guards.MlDsaReleaseGate.try_release_z_share)
          after post st_final ∧ mirAcceptedPairs post = [] := by
  induction htrace with
  | nil _ =>
    intro pre c err post heq
    cases pre <;> simp at heq
  | @accept m m' mf inp out rest hstep htail ih =>
    intro pre c err post heq
    cases pre with
    | nil => simp at heq
    | cons turn pre =>
      simp only [List.cons_append, List.cons.injEq] at heq
      obtain ⟨before, after, hp, hs, ha, hz, ht, hn⟩ := ih pre c err post heq.2
      exact ⟨before, after, heq.1 ▸ MirTrace.accept hstep hp, hs, ha, hz, ht, hn⟩
  | @reject m m' mf inp e rest hstep htail ih =>
    intro pre c err post heq
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, MirTurn.rejected.injEq] at heq
      rcases heq with ⟨⟨rfl, rfl⟩, rfl⟩
      obtain ⟨_, hrel⟩ := mldsa_gate_step_sim.err_preserves (s := m) rfl rfl hstep
      subst m'
      obtain ⟨hspec, _⟩ := mldsa_gate_step_sim.lift_trace_safety_abs
        (Safe := fun pairs => pairs = [])
        (fun ht => mldsa_done_no_more_accepts (Or.inl rfl) ht) rfl htail
      rw [map_id_pair] at hspec
      exact ⟨m, _, .nil m, hstep, rfl, rfl, htail, hspec⟩
    | cons turn pre =>
      simp only [List.cons_append, List.cons.injEq] at heq
      obtain ⟨before, after, hp, hs, ha, hz, ht, hn⟩ := ih pre c err post heq.2
      exact ⟨before, after, heq.1 ▸ MirTrace.reject hstep hp, hs, ha, hz, ht, hn⟩

theorem mldsa_gate_blocks_z_on_rejection_mir
    (sid : Array Std.U8 32#usize) (attempt : Std.U32) (z_masked : Array Std.U8 32#usize)
    (st0 st_final : cred_and_hd_guards.MlDsaReleaseGate)
    (turns : List (MirTurn cred_and_hd_guards.MlDsaBarrierChecks
      (Array Std.U8 32#usize) cred_and_hd_guards.CredHdGuardError))
    (hnew : cred_and_hd_guards.MlDsaReleaseGate.new_sealed sid attempt z_masked = .ok st0)
    (htrace : MirTrace (adaptStateResult cred_and_hd_guards.MlDsaReleaseGate.try_release_z_share)
      st0 turns st_final) :
    (∀ pre c err post, turns = pre ++ .rejected c err :: post →
      ∃ before after,
        MirTrace (adaptStateResult cred_and_hd_guards.MlDsaReleaseGate.try_release_z_share)
          st0 pre before ∧
        adaptStateResult cred_and_hd_guards.MlDsaReleaseGate.try_release_z_share before c =
          .ok (.rejected after err) ∧
        after.aborted = true ∧ after.z_share_masked = Array.repeat 32#usize 0#u8 ∧
        MirTrace (adaptStateResult cred_and_hd_guards.MlDsaReleaseGate.try_release_z_share)
          after post st_final ∧ mirAcceptedPairs post = []) ∧
    ((mirAcceptedPairs turns).length ≤ 1 ∧
      ∀ p ∈ mirAcceptedPairs turns,
        p.1.req_session_id = sid ∧ p.1.req_attempt = attempt ∧
        p.1.z_norm_ok = true ∧ p.1.r0_norm_ok = true ∧
        p.1.w1_match = true ∧ p.1.u_com_bound = true ∧
        p.2 = z_masked) := by
  constructor
  · exact mldsa_rejected_turn_wipes_and_seals htrace
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

theorem hd_zero_step_sim :
    MirStepSim hdZeroMealy (adaptStateResult mirHdZeroStep)
      Eq (fun a b => a = id b) (fun a b => a = id b) where
  ok_sim {s m m' i_s i_m o_m} hSt hIn hStep := by
    subst m; dsimp only [id] at hIn; subst i_s
    dsimp only [adaptStateResult, mirHdZeroStep] at hStep ⊢
    cases hq : s.family_quarantined
    · cases i_m with
      | freezePeer req_sid peer_comm =>
        dsimp only at hStep ⊢
        unfold cred_and_hd_guards.HdCommittedZeroTest.freeze_peer_commitment
          cred_and_hd_guards.quarantine_hd_family at hStep
        rw [hq, ct_eq_bytes32_spec] at hStep
        dsimp only [hdZeroMealy]
        rw [hq]
        by_cases hsid : s.session_id = req_sid
        · cases hp : s.phase <;>
            simp [hsid, hp, bind_eq_result_bind, result_bind_ok] at hStep ⊢
          rcases hStep with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl⟩
        · simp [hsid, bind_eq_result_bind, result_bind_ok] at hStep
      | openLocal req_sid =>
        dsimp only at hStep ⊢
        unfold cred_and_hd_guards.HdCommittedZeroTest.open_local_residual
          cred_and_hd_guards.quarantine_hd_family at hStep
        rw [hq, ct_eq_bytes32_spec] at hStep
        dsimp only [hdZeroMealy]
        rw [hq]
        by_cases hsid : s.session_id = req_sid
        · cases hp : s.phase <;>
            simp [hsid, hp, bind_eq_result_bind, result_bind_ok] at hStep ⊢
          rcases hStep with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl⟩
        · simp [hsid, bind_eq_result_bind, result_bind_ok] at hStep
      | verifyPeer req_sid recomputed_comm peer_res =>
        dsimp only at hStep ⊢
        unfold cred_and_hd_guards.HdCommittedZeroTest.verify_peer_opening
          cred_and_hd_guards.quarantine_hd_family at hStep
        rw [hq, ct_eq_bytes32_spec] at hStep
        dsimp only [hdZeroMealy]
        rw [hq]
        by_cases hsid : s.session_id = req_sid
        · cases hp : s.phase
          · simp [hsid, hp, bind_eq_result_bind, result_bind_ok] at hStep
          · simp [hsid, hp, bind_eq_result_bind, result_bind_ok] at hStep
          · rw [ct_eq_bytes32_spec] at hStep
            by_cases hcomm : s.frozen_peer_commitment = recomputed_comm
            · by_cases hq0 : s.modulus_q = 0#u32
              · simp [hsid, hp, hcomm, hq0, bind_eq_result_bind, result_bind_ok] at hStep
              · by_cases hlge : s.local_residual >= s.modulus_q
                · simp [hsid, hp, hcomm, hq0, hlge, bind_eq_result_bind, result_bind_ok] at hStep
                · by_cases hpge : peer_res >= s.modulus_q
                  · simp [hsid, hp, hcomm, hq0, hlge, hpge, bind_eq_result_bind, result_bind_ok] at hStep
                  · have hllt : s.local_residual < s.modulus_q := by
                      apply (UScalar.lt_iff_val _ _).mpr
                      exact Nat.lt_of_not_ge fun h => hlge ((UScalar.le_iff_val _ _).mpr h)
                    have hplt : peer_res < s.modulus_q := by
                      apply (UScalar.lt_iff_val _ _).mpr
                      exact Nat.lt_of_not_ge fun h => hpge ((UScalar.le_iff_val _ _).mpr h)
                    obtain ⟨sum, rem, hsum, hmod, hrem_iff⟩ :=
                      hd_verify_peer_arith_step s.local_residual peer_res s.modulus_q hq0 hllt hplt
                    simp only [Bool.false_eq_true, hsid, hp, hcomm, hq0, hlge, hpge, decide_true,
                      ↓reduceIte, bind_eq_result_bind, result_bind_ok, lift_eq_ok, hsum, hmod] at hStep
                    cases hrem : (rem != 0#u64)
                    · rw [hrem] at hStep
                      simp [Result.bind] at hStep
                      rcases hStep with ⟨rfl, rfl⟩
                      have hz : (s.local_residual.val + peer_res.val) % s.modulus_q.val = 0 := by
                        by_cases hzv : (s.local_residual.val + peer_res.val) % s.modulus_q.val = 0
                        · exact hzv
                        · have htrue := hrem_iff.mpr hzv
                          rw [hrem] at htrue; cases htrue
                      simp [hsid, hcomm, hq0, hllt, hplt, hz]
                    · rw [hrem] at hStep
                      simp [Result.bind] at hStep
            · simp [hsid, hp, hcomm, bind_eq_result_bind, result_bind_ok] at hStep
          · simp [hsid, hp, bind_eq_result_bind, result_bind_ok] at hStep
          · simp [hsid, hp, bind_eq_result_bind, result_bind_ok] at hStep
        · simp [hsid, bind_eq_result_bind, result_bind_ok] at hStep
    · cases i_m <;>
        simp [cred_and_hd_guards.HdCommittedZeroTest.freeze_peer_commitment,
          cred_and_hd_guards.HdCommittedZeroTest.open_local_residual,
          cred_and_hd_guards.HdCommittedZeroTest.verify_peer_opening,
          cred_and_hd_guards.quarantine_hd_family, hq,
          bind_eq_result_bind, result_bind_ok] at hStep
  err_preserves {s m m' i_s i_m e} hSt hIn hStep := by
    subst m; dsimp only [id] at hIn; subst i_s
    dsimp only [adaptStateResult, mirHdZeroStep] at hStep ⊢
    cases hq : s.family_quarantined
    · cases i_m with
      | freezePeer req_sid peer_comm =>
        dsimp only at hStep ⊢
        unfold cred_and_hd_guards.HdCommittedZeroTest.freeze_peer_commitment
          cred_and_hd_guards.quarantine_hd_family at hStep
        rw [hq, ct_eq_bytes32_spec] at hStep
        dsimp only [hdZeroMealy]
        rw [hq]
        by_cases hsid : s.session_id = req_sid
        · cases hp : s.phase <;>
            simp [hsid, hp, bind_eq_result_bind, result_bind_ok] at hStep ⊢ <;>
            exact hStep.1
        · simp [hsid, bind_eq_result_bind, result_bind_ok] at hStep ⊢
          exact hStep.1
      | openLocal req_sid =>
        dsimp only at hStep ⊢
        unfold cred_and_hd_guards.HdCommittedZeroTest.open_local_residual
          cred_and_hd_guards.quarantine_hd_family at hStep
        rw [hq, ct_eq_bytes32_spec] at hStep
        dsimp only [hdZeroMealy]
        rw [hq]
        by_cases hsid : s.session_id = req_sid
        · cases hp : s.phase <;>
            simp [hsid, hp, bind_eq_result_bind, result_bind_ok] at hStep ⊢ <;>
            exact hStep.1
        · simp [hsid, bind_eq_result_bind, result_bind_ok] at hStep ⊢
          exact hStep.1
      | verifyPeer req_sid recomputed_comm peer_res =>
        dsimp only at hStep ⊢
        unfold cred_and_hd_guards.HdCommittedZeroTest.verify_peer_opening
          cred_and_hd_guards.quarantine_hd_family at hStep
        rw [hq, ct_eq_bytes32_spec] at hStep
        dsimp only [hdZeroMealy]
        rw [hq]
        by_cases hsid : s.session_id = req_sid
        · cases hp : s.phase
          · simp [hsid, hp, bind_eq_result_bind, result_bind_ok] at hStep ⊢
            exact hStep.1
          · simp [hsid, hp, bind_eq_result_bind, result_bind_ok] at hStep ⊢
            exact hStep.1
          · rw [ct_eq_bytes32_spec] at hStep
            by_cases hcomm : s.frozen_peer_commitment = recomputed_comm
            · by_cases hq0 : s.modulus_q = 0#u32
              · simp [hsid, hp, hcomm, hq0, bind_eq_result_bind, result_bind_ok] at hStep ⊢
                exact hStep.1
              · by_cases hlge : s.local_residual >= s.modulus_q
                · have hnlt : ¬ s.local_residual < s.modulus_q := by
                    intro hlt
                    exact Nat.not_lt_of_ge ((UScalar.le_iff_val _ _).mp hlge)
                      ((UScalar.lt_iff_val _ _).mp hlt)
                  simp [hsid, hp, hcomm, hq0, hlge, hnlt, bind_eq_result_bind, result_bind_ok] at hStep ⊢
                  exact hStep.1
                · by_cases hpge : peer_res >= s.modulus_q
                  · have hnlt : ¬ peer_res < s.modulus_q := by
                      intro hlt
                      exact Nat.not_lt_of_ge ((UScalar.le_iff_val _ _).mp hpge)
                        ((UScalar.lt_iff_val _ _).mp hlt)
                    simp [hsid, hp, hcomm, hq0, hlge, hpge, hnlt, bind_eq_result_bind, result_bind_ok] at hStep ⊢
                    exact hStep.1
                  · have hllt : s.local_residual < s.modulus_q := by
                      apply (UScalar.lt_iff_val _ _).mpr
                      exact Nat.lt_of_not_ge fun h => hlge ((UScalar.le_iff_val _ _).mpr h)
                    have hplt : peer_res < s.modulus_q := by
                      apply (UScalar.lt_iff_val _ _).mpr
                      exact Nat.lt_of_not_ge fun h => hpge ((UScalar.le_iff_val _ _).mpr h)
                    obtain ⟨sum, rem, hsum, hmod, hrem_iff⟩ :=
                      hd_verify_peer_arith_step s.local_residual peer_res s.modulus_q hq0 hllt hplt
                    simp only [Bool.false_eq_true, hsid, hp, hcomm, hq0, hlge, hpge, decide_true,
                      ↓reduceIte, bind_eq_result_bind, result_bind_ok, lift_eq_ok, hsum, hmod] at hStep
                    cases hrem : (rem != 0#u64)
                    · rw [hrem] at hStep
                      simp [Result.bind] at hStep
                    · rw [hrem] at hStep
                      simp [Result.bind] at hStep
                      have hnz : (s.local_residual.val + peer_res.val) % s.modulus_q.val ≠ 0 :=
                        hrem_iff.mp hrem
                      simp [hsid, hcomm, hq0, hllt, hplt, hnz]
                      exact hStep.1
            · simp [hsid, hp, hcomm, bind_eq_result_bind, result_bind_ok] at hStep ⊢
              exact hStep.1
          · simp [hsid, hp, bind_eq_result_bind, result_bind_ok] at hStep ⊢
            exact hStep.1
          · simp [hsid, hp, bind_eq_result_bind, result_bind_ok] at hStep ⊢
            exact hStep.1
        · simp [hsid, bind_eq_result_bind, result_bind_ok] at hStep ⊢
          exact hStep.1
    · cases i_m <;>
        simp [cred_and_hd_guards.HdCommittedZeroTest.freeze_peer_commitment,
          cred_and_hd_guards.HdCommittedZeroTest.open_local_residual,
          cred_and_hd_guards.HdCommittedZeroTest.verify_peer_opening,
          cred_and_hd_guards.quarantine_hd_family, hq, hdZeroMealy,
          bind_eq_result_bind, result_bind_ok] at hStep ⊢ <;>
        exact hStep.1

@[expose]
def hdTraceSafe (sid : Array Std.U8 32#usize) (local_res q : Std.U32)
    (pairs : List (HdZeroStepInput × HdZeroStepOutput)) : Prop :=
  pairs = [] ∨
  (∃ comm, pairs = [(.freezePeer sid comm, .peerFrozen)]) ∨
  (∃ comm, pairs = [(.freezePeer sid comm, .peerFrozen),
                    (.openLocal sid, .localOpened local_res)]) ∨
  (∃ comm peer_res,
    0 < q.val ∧ local_res.val < q.val ∧ peer_res.val < q.val ∧
    (local_res.val + peer_res.val) % q.val = 0 ∧
    pairs = [(.freezePeer sid comm, .peerFrozen),
             (.openLocal sid, .localOpened local_res),
             (.verifyPeer sid comm peer_res, .zeroVerified)])

private theorem hd_quarantined_full_trace_nil
    {st s_f : cred_and_hd_guards.HdCommittedZeroTest}
    {pairs : List (HdZeroStepInput × HdZeroStepOutput)}
    (hq : st.family_quarantined = true)
    (hp : st.phase = .FamilyQuarantined)
    (hr : st.local_residual = 0#u32)
    (hTr : hdZeroMealy.ValidTrace st pairs s_f) :
    pairs = [] ∧ s_f.family_quarantined = true ∧
      s_f.phase = .FamilyQuarantined ∧ s_f.local_residual = 0#u32 := by
  induction hTr with
  | nil _ => exact ⟨rfl, hq, hp, hr⟩
  | @accept sa _ _ _ _ _ hStepA _ _ =>
    dsimp only [hdZeroMealy] at hStepA
    rw [hq] at hStepA; cases hStepA
  | reject _ _ _ ih =>
    exact ih rfl rfl rfl

private theorem hd_verified_zero_trace_nil
    {st s_f : cred_and_hd_guards.HdCommittedZeroTest}
    {pairs : List (HdZeroStepInput × HdZeroStepOutput)}
    (hp : st.phase = .VerifiedZero)
    (hTr : hdZeroMealy.ValidTrace st pairs s_f) :
    pairs = [] := by
  induction hTr with
  | nil _ => rfl
  | @accept sa _ _ inp _ _ hStep _ _ =>
    dsimp only [hdZeroMealy] at hStep
    cases hq : sa.family_quarantined
    · rw [hq] at hStep
      cases inp <;> simp [hp] at hStep
    · rw [hq] at hStep; cases hStep
  | reject _ _ hTail _ =>
    exact (hd_quarantined_full_trace_nil rfl rfl rfl hTail).1

private theorem hd_phase2_trace_shape
    (sid comm : Array Std.U8 32#usize) (local_res q : Std.U32)
    (_hq0 : 0 < q.val) (_hloc : local_res.val < q.val)
    {pairs : List (HdZeroStepInput × HdZeroStepOutput)}
    {s_f : cred_and_hd_guards.HdCommittedZeroTest}
    (hTr : hdZeroMealy.ValidTrace
      { session_id := sid, phase := .LocalResidualOpened,
        frozen_peer_commitment := comm, local_residual := local_res,
        modulus_q := q, family_quarantined := false }
      pairs s_f) :
    pairs = [] ∨
    ∃ peer_res, peer_res.val < q.val ∧ (local_res.val + peer_res.val) % q.val = 0 ∧
      pairs = [(.verifyPeer sid comm peer_res, .zeroVerified)] := by
  generalize hs2 :
    ({ session_id := sid, phase := .LocalResidualOpened,
       frozen_peer_commitment := comm, local_residual := local_res,
       modulus_q := q, family_quarantined := false } : cred_and_hd_guards.HdCommittedZeroTest) = s2 at hTr
  induction hTr with
  | nil _ => exact Or.inl rfl
  | @accept sa sb _ inp out rest hStep hTail _ =>
    subst hs2
    dsimp only [hdZeroMealy] at hStep
    cases inp with
    | freezePeer req_sid peer_comm =>
      simp at hStep
    | openLocal req_sid =>
      simp at hStep
    | verifyPeer req_sid recomputed_comm peer_res =>
      by_cases hsid : sid = req_sid
      · subst hsid
        simp only [Bool.false_eq_true, decide_true, ↓reduceIte] at hStep
        cases hcond :
          (decide (comm = recomputed_comm) && decide (q ≠ 0#u32) &&
           decide (local_res < q) && decide (peer_res < q) &&
           decide ((local_res.val + peer_res.val) % q.val = 0))
        · rw [hcond] at hStep; cases hStep
        · rw [hcond] at hStep
          simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hStep
          rcases hStep with ⟨hsb, hout⟩
          subst hsb; subst hout
          have hRest : rest = [] := hd_verified_zero_trace_nil rfl hTail
          subst hRest
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
          rcases hcond with ⟨⟨⟨⟨hcomm, _⟩, _⟩, hp_lt⟩, hsum⟩
          subst hcomm
          exact Or.inr ⟨peer_res, (UScalar.lt_iff_val _ _).mp hp_lt, hsum, rfl⟩
      · simp [hsid] at hStep
  | reject _ _ hTail _ =>
    subst hs2
    exact Or.inl (hd_quarantined_full_trace_nil rfl rfl rfl hTail).1

private theorem hd_phase1_trace_shape
    (sid comm : Array Std.U8 32#usize) (local_res q : Std.U32)
    (hq0 : 0 < q.val) (hloc : local_res.val < q.val)
    {pairs : List (HdZeroStepInput × HdZeroStepOutput)}
    {s_f : cred_and_hd_guards.HdCommittedZeroTest}
    (hTr : hdZeroMealy.ValidTrace
      { session_id := sid, phase := .PeerCommitmentFrozen,
        frozen_peer_commitment := comm, local_residual := local_res,
        modulus_q := q, family_quarantined := false }
      pairs s_f) :
    pairs = [] ∨
    pairs = [(.openLocal sid, .localOpened local_res)] ∨
    ∃ peer_res, peer_res.val < q.val ∧ (local_res.val + peer_res.val) % q.val = 0 ∧
      pairs = [(.openLocal sid, .localOpened local_res),
               (.verifyPeer sid comm peer_res, .zeroVerified)] := by
  generalize hs1 :
    ({ session_id := sid, phase := .PeerCommitmentFrozen,
       frozen_peer_commitment := comm, local_residual := local_res,
       modulus_q := q, family_quarantined := false } : cred_and_hd_guards.HdCommittedZeroTest) = s1 at hTr
  induction hTr with
  | nil _ => exact Or.inl rfl
  | @accept sa sb _ inp out rest hStep hTail _ =>
    subst hs1
    dsimp only [hdZeroMealy] at hStep
    cases inp with
    | freezePeer _ _ => simp at hStep
    | verifyPeer _ _ _ => simp at hStep
    | openLocal req_sid =>
      by_cases hsid : sid = req_sid
      · subst hsid
        simp only [Bool.false_eq_true, decide_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hStep
        rcases hStep with ⟨hsb, hout⟩
        subst hsb; subst hout
        rcases hd_phase2_trace_shape sid comm local_res q hq0 hloc hTail with hNil | ⟨pr, hpr, hsum, hRest⟩
        · subst hNil; exact Or.inr (Or.inl rfl)
        · subst hRest; exact Or.inr (Or.inr ⟨pr, hpr, hsum, rfl⟩)
      · simp [hsid] at hStep
  | reject _ _ hTail _ =>
    subst hs1
    exact Or.inl (hd_quarantined_full_trace_nil rfl rfl rfl hTail).1

private theorem hd_init_spec_trace_safe
    (sid : Array Std.U8 32#usize) (local_res q : Std.U32)
    (st0 s_f : cred_and_hd_guards.HdCommittedZeroTest)
    (hnew : cred_and_hd_guards.HdCommittedZeroTest.new_awaiting_peer_commit sid local_res q = .ok st0)
    {pairs : List (HdZeroStepInput × HdZeroStepOutput)}
    (hTr : hdZeroMealy.ValidTrace st0 pairs s_f) :
    hdTraceSafe sid local_res q pairs := by
  unfold cred_and_hd_guards.HdCommittedZeroTest.new_awaiting_peer_commit
    cred_and_hd_guards.quarantine_hd_family at hnew
  by_cases hq0 : q = 0#u32
  · simp only [hq0, ↓reduceIte, Result.ok.injEq] at hnew
    subst hnew
    exact Or.inl (hd_quarantined_full_trace_nil rfl rfl rfl hTr).1
  · by_cases hlge : local_res >= q
    · simp only [hq0, hlge, ↓reduceIte, Result.ok.injEq] at hnew
      subst hnew
      exact Or.inl (hd_quarantined_full_trace_nil rfl rfl rfl hTr).1
    · simp only [hq0, hlge, ↓reduceIte, Result.ok.injEq] at hnew
      have hq_pos : 0 < q.val := by
        cases hv : q.val with
        | zero => exact False.elim (hq0 (UScalar.eq_of_val_eq hv))
        | succ k => exact Nat.zero_lt_succ k
      have hloc_lt : local_res.val < q.val :=
        Nat.lt_of_not_ge fun h => hlge ((UScalar.le_iff_val _ _).mpr h)
      generalize hs0 : st0 = s_init at hTr
      rw [← hnew] at hs0
      induction hTr with
      | nil _ => exact Or.inl rfl
      | @accept sa sb _ inp out rest hStep hTail _ =>
        subst hs0
        dsimp only [hdZeroMealy] at hStep
        cases inp with
        | openLocal _ => simp at hStep
        | verifyPeer _ _ _ => simp at hStep
        | freezePeer req_sid comm =>
          by_cases hsid : sid = req_sid
          · subst hsid
            simp only [Bool.false_eq_true, decide_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hStep
            rcases hStep with ⟨hsb, hout⟩
            subst hsb; subst hout
            rcases hd_phase1_trace_shape sid comm local_res q hq_pos hloc_lt hTail with
              hNil | hOpen | ⟨pr, hpr, hsum, hVer⟩
            · subst hNil; exact Or.inr (Or.inl ⟨comm, rfl⟩)
            · subst hOpen; exact Or.inr (Or.inr (Or.inl ⟨comm, rfl⟩))
            · subst hVer
              exact Or.inr (Or.inr (Or.inr ⟨comm, pr, hq_pos, hloc_lt, hpr, hsum, rfl⟩))
          · simp [hsid] at hStep
      | reject _ _ hTail _ =>
        subst hs0
        exact Or.inl (hd_quarantined_full_trace_nil rfl rfl rfl hTail).1

private theorem hd_mir_quarantine_irreversible
    {st st_f : cred_and_hd_guards.HdCommittedZeroTest}
    {turns : List (MirTurn HdZeroStepInput HdZeroStepOutput cred_and_hd_guards.CredHdGuardError)}
    (hq : st.family_quarantined = true ∧ st.phase = .FamilyQuarantined ∧ st.local_residual = 0#u32)
    (hTr : MirTrace (adaptStateResult mirHdZeroStep) st turns st_f) :
    st_f.family_quarantined = true ∧ st_f.phase = .FamilyQuarantined ∧
      st_f.local_residual = 0#u32 ∧ mirAcceptedPairs turns = [] := by
  induction hTr with
  | nil _ => exact ⟨hq.1, hq.2.1, hq.2.2, rfl⟩
  | @accept m m' _ inp out _ hStep _ _ =>
    have hSim := hd_zero_step_sim.ok_sim (s := m) rfl rfl hStep
    dsimp only [hdZeroMealy] at hSim
    rw [hq.1] at hSim
    exact False.elim hSim
  | @reject m m' _ inp err _ hStep _ ih =>
    obtain ⟨_, hRel⟩ := hd_zero_step_sim.err_preserves (s := m) rfl rfl hStep
    subst hRel
    exact ih ⟨rfl, rfl, rfl⟩

private theorem hd_mir_any_rejection_quarantines
    {st st_f : cred_and_hd_guards.HdCommittedZeroTest}
    {turns : List (MirTurn HdZeroStepInput HdZeroStepOutput cred_and_hd_guards.CredHdGuardError)}
    (hTr : MirTrace (adaptStateResult mirHdZeroStep) st turns st_f)
    (hHasRej : ∃ inp err, MirTurn.rejected inp err ∈ turns) :
    st_f.family_quarantined = true ∧ st_f.phase = .FamilyQuarantined ∧
      st_f.local_residual = 0#u32 := by
  induction hTr with
  | nil _ =>
    rcases hHasRej with ⟨_, _, hm⟩
    exact False.elim (List.not_mem_nil hm)
  | accept _ _ ih =>
    rcases hHasRej with ⟨inp, err, hm⟩
    simp only [List.mem_cons, reduceCtorEq, false_or] at hm
    exact ih ⟨inp, err, hm⟩
  | @reject m m' _ _ _ _ hStep hTail _ =>
    obtain ⟨_, hRel⟩ := hd_zero_step_sim.err_preserves (s := m) rfl rfl hStep
    subst hRel
    obtain ⟨h1, h2, h3, _⟩ := hd_mir_quarantine_irreversible ⟨rfl, rfl, rfl⟩ hTail
    exact ⟨h1, h2, h3⟩

theorem hd_zero_test_quarantine_mir
    (sid : Array Std.U8 32#usize) (local_res q : Std.U32)
    (st0 st_final : cred_and_hd_guards.HdCommittedZeroTest)
    (turns : List (MirTurn HdZeroStepInput HdZeroStepOutput cred_and_hd_guards.CredHdGuardError))
    (hnew : cred_and_hd_guards.HdCommittedZeroTest.new_awaiting_peer_commit sid local_res q = .ok st0)
    (htrace : MirTrace (adaptStateResult mirHdZeroStep) st0 turns st_final) :
    hdTraceSafe sid local_res q (mirAcceptedPairs turns) ∧
    ((∃ inp err, MirTurn.rejected inp err ∈ turns) →
      st_final.family_quarantined = true ∧
      st_final.phase = .FamilyQuarantined ∧
      st_final.local_residual = 0#u32) := by
  constructor
  · obtain ⟨hSafe, _⟩ :=
      hd_zero_step_sim.lift_trace_safety_abs
        (Safe := hdTraceSafe sid local_res q)
        (fun hVal => hd_init_spec_trace_safe sid local_res q st0 _ hnew hVal)
        rfl
        htrace
    rw [map_id_pair] at hSafe
    exact hSafe
  · exact hd_mir_any_rejection_quarantines htrace

/-! ## 5. Concrete `#tooth` Refusal Witnesses -/

theorem tooth_mldsa_r0_norm_fail_blocks_z :
    let sid := Array.repeat 32#usize 0x11#u8
    let secret := Array.repeat 32#usize 0x77#u8
    let checks : cred_and_hd_guards.MlDsaBarrierChecks :=
      { req_session_id := sid, req_attempt := 0#u32,
        z_norm_ok := true, r0_norm_ok := false, w1_match := true, u_com_bound := true }
    (cred_and_hd_guards.MlDsaReleaseGate.new_sealed sid 0#u32 secret >>= fun g =>
      cred_and_hd_guards.MlDsaReleaseGate.try_release_z_share g checks) =
      .ok ({ session_id := sid, attempt := 0#u32,
             z_share_masked := Array.repeat 32#usize 0#u8,
             released := false, aborted := true },
           .Err .RejectionSamplingBarrierFailed) := by
  have hsid : tower.ct_eq_bytes32 (Array.repeat 32#usize 0x11#u8)
      (Array.repeat 32#usize 0x11#u8) = .ok true := by
    rw [ct_eq_bytes32_spec]; rfl
  simp [cred_and_hd_guards.MlDsaReleaseGate.new_sealed,
    cred_and_hd_guards.MlDsaReleaseGate.try_release_z_share,
    cred_and_hd_guards.abort_mldsa_gate, hsid,
    bind_eq_result_bind, result_bind_ok]

theorem tooth_toprf_noncanonical_unanimous_rejected :
    cred_and_hd_guards.toprf_majority_of_3_goldilocks
      18446744069414584321#u64 18446744069414584321#u64 18446744069414584321#u64 =
      .ok none := by
  unfold cred_and_hd_guards.toprf_majority_of_3_goldilocks goldilocks.GOLDILOCKS_PRIME
  decide

theorem tooth_hd_premature_open_quarantined :
    let sid := Array.repeat 32#usize 0x22#u8
    (cred_and_hd_guards.HdCommittedZeroTest.new_awaiting_peer_commit sid 5#u32 17#u32 >>= fun st =>
      cred_and_hd_guards.HdCommittedZeroTest.open_local_residual st sid) =
      .ok ({ session_id := sid, phase := .FamilyQuarantined,
             frozen_peer_commitment := Array.repeat 32#usize 0#u8,
             local_residual := 0#u32, modulus_q := 17#u32, family_quarantined := true },
           .Err .InvalidHdPhaseTransition) := by
  have hsid : tower.ct_eq_bytes32 (Array.repeat 32#usize 0x22#u8)
      (Array.repeat 32#usize 0x22#u8) = .ok true := by
    rw [ct_eq_bytes32_spec]; rfl
  have hq : ¬ (17#u32 = 0#u32) := by decide
  have hl : ¬ (5#u32 >= 17#u32) := by decide
  simp [cred_and_hd_guards.HdCommittedZeroTest.new_awaiting_peer_commit,
    cred_and_hd_guards.HdCommittedZeroTest.open_local_residual,
    cred_and_hd_guards.quarantine_hd_family, hsid, hq, hl,
    bind_eq_result_bind, result_bind_ok]

theorem tooth_hd_nonzero_sum_quarantined :
    let sid := Array.repeat 32#usize 0x33#u8
    let comm := Array.repeat 32#usize 0xAA#u8
    let st2 : cred_and_hd_guards.HdCommittedZeroTest :=
      { session_id := sid, phase := .LocalResidualOpened,
        frozen_peer_commitment := comm, local_residual := 5#u32,
        modulus_q := 17#u32, family_quarantined := false }
    cred_and_hd_guards.HdCommittedZeroTest.verify_peer_opening st2 sid comm 6#u32 =
      .ok ({ session_id := sid, phase := .FamilyQuarantined,
             frozen_peer_commitment := comm,
             local_residual := 0#u32, modulus_q := 17#u32, family_quarantined := true },
           .Err .HdZeroTestMismatchQuarantined) := by
  have hsid : tower.ct_eq_bytes32 (Array.repeat 32#usize 0x33#u8)
      (Array.repeat 32#usize 0x33#u8) = .ok true := by
    rw [ct_eq_bytes32_spec]; rfl
  have hcomm : tower.ct_eq_bytes32 (Array.repeat 32#usize 0xAA#u8)
      (Array.repeat 32#usize 0xAA#u8) = .ok true := by
    rw [ct_eq_bytes32_spec]; rfl
  have hq : ¬ (17#u32 = 0#u32) := by decide
  have hl : ¬ (5#u32 >= 17#u32) := by decide
  have hp : ¬ (6#u32 >= 17#u32) := by decide
  obtain ⟨sum, rem, hsum, hmod, hrem_iff⟩ :=
    hd_verify_peer_arith_step 5#u32 6#u32 17#u32 hq (by decide) (by decide)
  have hrem : (rem != 0#u64) = true := hrem_iff.mpr (by decide)
  unfold cred_and_hd_guards.HdCommittedZeroTest.verify_peer_opening
    cred_and_hd_guards.quarantine_hd_family
  simp only [Bool.false_eq_true, hsid, hcomm, hq, hl, hp, ↓reduceIte,
    bind_eq_result_bind, result_bind_ok, lift_eq_ok, hsum, hmod, hrem]

end qsag_verified.proofs
