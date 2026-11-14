module
import all QsagVerified.Funs

public import QsagVerified.Proofs.Common
public import QsagVerified.Proofs.MirRefinementKit
public import QsagVerified.Proofs.Sponge

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

/-! ## 1. Round-1 Mask Commitment Totality -/

theorem compute_rss_mask_commitment_total
    (session_id : Array Std.U8 32#usize) (party_id : Std.U8)
    (mask_bytes salt_nonce : Array Std.U8 32#usize) :
    ∃ comm, rss_cut_session.compute_rss_mask_commitment session_id party_id mask_bytes salt_nonce =
      .ok comm := by
  let sp0 : keccak.Shake256Sponge :=
    ⟨Std.Array.repeat 25#usize 0#u64, Std.Array.repeat 136#usize 0#u8,
      0#usize, 31#u8, false, 0#usize⟩
  have hnew : keccak.Shake256Sponge.new_shake256 = .ok sp0 := rfl
  let dom : Std.Array Std.U8 16#usize := Array.make 16#usize [
    81#u8, 83#u8, 65#u8, 71#u8, 46#u8, 82#u8, 83#u8, 83#u8, 67#u8, 85#u8,
    84#u8, 46#u8, 77#u8, 83#u8, 75#u8, 49#u8]
  let pid_arr : Std.Array Std.U8 1#usize := Array.make 1#usize [party_id]
  have hd : (Std.Array.to_slice dom).val.length = 16 := dom.property
  have hs : (Std.Array.to_slice session_id).val.length = 32 := session_id.property
  have hp : (Std.Array.to_slice pid_arr).val.length = 1 := pid_arr.property
  have hm : (Std.Array.to_slice mask_bytes).val.length = 32 := mask_bytes.property
  have hn : (Std.Array.to_slice salt_nonce).val.length = 32 := salt_nonce.property
  obtain ⟨sp1, hsp1, hn1, hv1⟩ := sponge_absorb_short sp0 (Std.Array.to_slice dom) rfl
    (by change 0 + _ < 136; rw [hd]; decide)
  have hv1' : sp1.buf_len.val = 16 := by
    simpa only [hd, show sp0.buf_len.val = 0 from rfl, Nat.zero_add] using hv1
  obtain ⟨sp2, hsp2, hn2, hv2⟩ := sponge_absorb_short sp1 (Std.Array.to_slice session_id) hn1
    (by rw [hv1', hs]; decide)
  have hv2' : sp2.buf_len.val = 48 := by simpa only [hv1', hs] using hv2
  obtain ⟨sp3, hsp3, hn3, hv3⟩ := sponge_absorb_short sp2 (Std.Array.to_slice pid_arr) hn2
    (by rw [hv2', hp]; decide)
  have hv3' : sp3.buf_len.val = 49 := by simpa only [hv2', hp] using hv3
  obtain ⟨sp4, hsp4, hn4, hv4⟩ := sponge_absorb_short sp3 (Std.Array.to_slice mask_bytes) hn3
    (by rw [hv3', hm]; decide)
  have hv4' : sp4.buf_len.val = 81 := by simpa only [hv3', hm] using hv4
  obtain ⟨sp5, hsp5, hn5, hv5⟩ := sponge_absorb_short sp4 (Std.Array.to_slice salt_nonce) hn4
    (by rw [hv4', hn]; decide)
  have hv5' : sp5.buf_len.val = 113 := by simpa only [hv4', hn] using hv5
  let out : Std.Array Std.U8 32#usize := Std.Array.repeat 32#usize 0#u8
  obtain ⟨result, hresult⟩ := sponge_squeeze_short sp5 (Std.Array.to_slice_mut out).1 32
    (by decide) hn5 (by rw [hv5']; decide) rfl
  unfold rss_cut_session.compute_rss_mask_commitment
  simp only [hnew, bind_eq_result_bind, result_bind_ok, lift_eq_ok]
  rw [hsp1, result_bind_ok, hsp2, result_bind_ok, hsp3, result_bind_ok,
    hsp4, result_bind_ok, hsp5, result_bind_ok, hresult, result_bind_ok]
  exact ⟨_, rfl⟩

/-! ## 2. Pure 4-Phase Mealy Spec & 1-Step MIR Simulation (`MirStepSim`) -/

@[expose]
def rssCutMealy :
    MealySpec rss_cut_session.RssCutGateSession
      rss_cut_session.RssCutStepInput rss_cut_session.RssCutStepOutput where
  step st inp :=
    if st.poisoned then none
    else
      match inp with
      | .AdvanceRound2Chi req_sid recomputed_comm chi_cut =>
        if decide (st.session_id = req_sid) then
          match st.phase with
          | .Round1MaskCommitted =>
            if decide (st.mask_commitment = recomputed_comm) then
              some ({ st with
                      phase := .Round2ChiEvaluated
                      candidate_cut_bytes := chi_cut
                      consistency_verified := false },
                    .Round2Ready)
            else none
          | _ => none
        else none
      | .AdvanceRound3VerifyConsistency req_sid lo hi dzk =>
        if decide (st.session_id = req_sid) then
          match st.phase with
          | .Round2ChiEvaluated =>
            if decide (lo = 0#u128) && decide (hi = 0#u128) && decide (dzk = 0#u64) then
              some ({ st with
                      phase := .Round3ConsistencyVerified
                      consistency_verified := true },
                    .Round3Verified)
            else none
          | _ => none
        else none
      | .OpenVerifiedCut req_sid =>
        if decide (st.session_id = req_sid) then
          match st.phase with
          | .Round3ConsistencyVerified =>
            if st.consistency_verified then
              some ({ st with
                      phase := .CutOpened
                      candidate_cut_bytes := Array.repeat 32#usize 0#u8 },
                    .CutReleased st.candidate_cut_bytes)
            else none
          | _ => none
        else none
  errStep st _ :=
    { session_id := st.session_id
      phase := .Poisoned
      mask_commitment := st.mask_commitment
      candidate_cut_bytes := Array.repeat 32#usize 0#u8
      consistency_verified := false
      poisoned := true }

theorem rss_cut_step_sim :
    MirStepSim rssCutMealy (adaptStateResult rss_cut_session.RssCutGateSession.step)
      Eq (fun a b => a = id b) (fun a b => a = id b) where
  ok_sim {s m m' i_s i_m o_m} hSt hIn hStep := by
    subst m; dsimp only [id] at hIn; subst i_s
    dsimp only [adaptStateResult, rss_cut_session.RssCutGateSession.step] at hStep ⊢
    cases hp_flag : s.poisoned
    · cases i_m with
      | AdvanceRound2Chi req_sid recomputed_comm chi_cut =>
        dsimp only at hStep ⊢
        unfold rss_cut_session.RssCutGateSession.advance_round2_chi
          rss_cut_session.poison_rss_cut_session at hStep
        rw [hp_flag, ct_eq_bytes32_spec] at hStep
        dsimp only [rssCutMealy]
        rw [hp_flag]
        by_cases hsid : s.session_id = req_sid
        · cases hph : s.phase
          · rw [ct_eq_bytes32_spec] at hStep
            by_cases hmc : s.mask_commitment = recomputed_comm
            · simp [hsid, hph, hmc, bind_eq_result_bind, result_bind_ok] at hStep ⊢
              rcases hStep with ⟨rfl, rfl⟩
              exact ⟨rfl, rfl⟩
            · simp [hsid, hph, hmc, bind_eq_result_bind, result_bind_ok] at hStep
          · simp [hsid, hph, bind_eq_result_bind, result_bind_ok] at hStep
          · simp [hsid, hph, bind_eq_result_bind, result_bind_ok] at hStep
          · simp [hsid, hph, bind_eq_result_bind, result_bind_ok] at hStep
          · simp [hsid, hph, bind_eq_result_bind, result_bind_ok] at hStep
        · simp [hsid, bind_eq_result_bind, result_bind_ok] at hStep
      | AdvanceRound3VerifyConsistency req_sid lo hi dzk =>
        dsimp only at hStep ⊢
        unfold rss_cut_session.RssCutGateSession.advance_round3_verify_consistency
          rss_cut_session.poison_rss_cut_session at hStep
        rw [hp_flag, ct_eq_bytes32_spec] at hStep
        dsimp only [rssCutMealy]
        rw [hp_flag]
        by_cases hsid : s.session_id = req_sid
        · cases hph : s.phase
          · simp [hsid, hph, bind_eq_result_bind, result_bind_ok] at hStep
          · by_cases hlo : lo = 0#u128
            · by_cases hhi : hi = 0#u128
              · by_cases hdzk : dzk = 0#u64
                · simp [hsid, hph, hlo, hhi, hdzk, bind_eq_result_bind, result_bind_ok] at hStep ⊢
                  rcases hStep with ⟨rfl, rfl⟩
                  exact ⟨rfl, rfl⟩
                · have hne : (dzk != 0#u64) = true := by simp [hdzk]
                  simp [hsid, hph, hlo, hhi, hne, bind_eq_result_bind, result_bind_ok] at hStep
              · have hne : (hi != 0#u128) = true := by simp [hhi]
                simp [hsid, hph, hlo, hne, bind_eq_result_bind, result_bind_ok] at hStep
            · have hne : (lo != 0#u128) = true := by simp [hlo]
              simp [hsid, hph, hne, bind_eq_result_bind, result_bind_ok] at hStep
          · simp [hsid, hph, bind_eq_result_bind, result_bind_ok] at hStep
          · simp [hsid, hph, bind_eq_result_bind, result_bind_ok] at hStep
          · simp [hsid, hph, bind_eq_result_bind, result_bind_ok] at hStep
        · simp [hsid, bind_eq_result_bind, result_bind_ok] at hStep
      | OpenVerifiedCut req_sid =>
        dsimp only at hStep ⊢
        unfold rss_cut_session.RssCutGateSession.open_verified_cut
          rss_cut_session.poison_rss_cut_session at hStep
        rw [hp_flag, ct_eq_bytes32_spec] at hStep
        dsimp only [rssCutMealy]
        rw [hp_flag]
        by_cases hsid : s.session_id = req_sid
        · cases hph : s.phase
          · simp [hsid, hph, bind_eq_result_bind, result_bind_ok] at hStep
          · simp [hsid, hph, bind_eq_result_bind, result_bind_ok] at hStep
          · cases hcv : s.consistency_verified
            · simp [hsid, hph, hcv, bind_eq_result_bind, result_bind_ok] at hStep
            · simp [hsid, hph, hcv, bind_eq_result_bind, result_bind_ok] at hStep ⊢
              rcases hStep with ⟨rfl, rfl⟩
              exact ⟨rfl, rfl⟩
          · simp [hsid, hph, bind_eq_result_bind, result_bind_ok] at hStep
          · simp [hsid, hph, bind_eq_result_bind, result_bind_ok] at hStep
        · simp [hsid, bind_eq_result_bind, result_bind_ok] at hStep
    · cases i_m <;>
        simp [rss_cut_session.RssCutGateSession.advance_round2_chi,
          rss_cut_session.RssCutGateSession.advance_round3_verify_consistency,
          rss_cut_session.RssCutGateSession.open_verified_cut,
          rss_cut_session.poison_rss_cut_session, hp_flag,
          bind_eq_result_bind, result_bind_ok] at hStep
  err_preserves {s m m' i_s i_m e} hSt hIn hStep := by
    subst m; dsimp only [id] at hIn; subst i_s
    dsimp only [adaptStateResult, rss_cut_session.RssCutGateSession.step] at hStep ⊢
    cases hp_flag : s.poisoned
    · cases i_m with
      | AdvanceRound2Chi req_sid recomputed_comm chi_cut =>
        dsimp only at hStep ⊢
        unfold rss_cut_session.RssCutGateSession.advance_round2_chi
          rss_cut_session.poison_rss_cut_session at hStep
        rw [hp_flag, ct_eq_bytes32_spec] at hStep
        dsimp only [rssCutMealy]
        rw [hp_flag]
        by_cases hsid : s.session_id = req_sid
        · cases hph : s.phase
          · rw [ct_eq_bytes32_spec] at hStep
            by_cases hmc : s.mask_commitment = recomputed_comm
            · simp [hsid, hph, hmc, bind_eq_result_bind, result_bind_ok] at hStep
            · simp [hsid, hph, hmc, bind_eq_result_bind, result_bind_ok] at hStep ⊢
              exact hStep.1
          · simp [hsid, hph, bind_eq_result_bind, result_bind_ok] at hStep ⊢
            exact hStep.1
          · simp [hsid, hph, bind_eq_result_bind, result_bind_ok] at hStep ⊢
            exact hStep.1
          · simp [hsid, hph, bind_eq_result_bind, result_bind_ok] at hStep ⊢
            exact hStep.1
          · simp [hsid, hph, bind_eq_result_bind, result_bind_ok] at hStep ⊢
            exact hStep.1
        · simp [hsid, bind_eq_result_bind, result_bind_ok] at hStep ⊢
          exact hStep.1
      | AdvanceRound3VerifyConsistency req_sid lo hi dzk =>
        dsimp only at hStep ⊢
        unfold rss_cut_session.RssCutGateSession.advance_round3_verify_consistency
          rss_cut_session.poison_rss_cut_session at hStep
        rw [hp_flag, ct_eq_bytes32_spec] at hStep
        dsimp only [rssCutMealy]
        rw [hp_flag]
        by_cases hsid : s.session_id = req_sid
        · cases hph : s.phase
          · simp [hsid, hph, bind_eq_result_bind, result_bind_ok] at hStep ⊢
            exact hStep.1
          · by_cases hlo : lo = 0#u128
            · by_cases hhi : hi = 0#u128
              · by_cases hdzk : dzk = 0#u64
                · simp [hsid, hph, hlo, hhi, hdzk, bind_eq_result_bind, result_bind_ok] at hStep
                · have hne : (dzk != 0#u64) = true := by simp [hdzk]
                  simp [hsid, hph, hlo, hhi, hdzk, hne, bind_eq_result_bind, result_bind_ok] at hStep ⊢
                  exact hStep.1
              · have hne : (hi != 0#u128) = true := by simp [hhi]
                simp [hsid, hph, hlo, hhi, hne, bind_eq_result_bind, result_bind_ok] at hStep ⊢
                exact hStep.1
            · have hne : (lo != 0#u128) = true := by simp [hlo]
              simp [hsid, hph, hlo, hne, bind_eq_result_bind, result_bind_ok] at hStep ⊢
              exact hStep.1
          · simp [hsid, hph, bind_eq_result_bind, result_bind_ok] at hStep ⊢
            exact hStep.1
          · simp [hsid, hph, bind_eq_result_bind, result_bind_ok] at hStep ⊢
            exact hStep.1
          · simp [hsid, hph, bind_eq_result_bind, result_bind_ok] at hStep ⊢
            exact hStep.1
        · simp [hsid, bind_eq_result_bind, result_bind_ok] at hStep ⊢
          exact hStep.1
      | OpenVerifiedCut req_sid =>
        dsimp only at hStep ⊢
        unfold rss_cut_session.RssCutGateSession.open_verified_cut
          rss_cut_session.poison_rss_cut_session at hStep
        rw [hp_flag, ct_eq_bytes32_spec] at hStep
        dsimp only [rssCutMealy]
        rw [hp_flag]
        by_cases hsid : s.session_id = req_sid
        · cases hph : s.phase
          · simp [hsid, hph, bind_eq_result_bind, result_bind_ok] at hStep ⊢
            exact hStep.1
          · simp [hsid, hph, bind_eq_result_bind, result_bind_ok] at hStep ⊢
            exact hStep.1
          · cases hcv : s.consistency_verified
            · simp [hsid, hph, hcv, bind_eq_result_bind, result_bind_ok] at hStep ⊢
              exact hStep.1
            · simp [hsid, hph, hcv, bind_eq_result_bind, result_bind_ok] at hStep
          · simp [hsid, hph, bind_eq_result_bind, result_bind_ok] at hStep ⊢
            exact hStep.1
          · simp [hsid, hph, bind_eq_result_bind, result_bind_ok] at hStep ⊢
            exact hStep.1
        · simp [hsid, bind_eq_result_bind, result_bind_ok] at hStep ⊢
          exact hStep.1
    · cases i_m <;>
        simp [rss_cut_session.RssCutGateSession.advance_round2_chi,
          rss_cut_session.RssCutGateSession.advance_round3_verify_consistency,
          rss_cut_session.RssCutGateSession.open_verified_cut,
          rss_cut_session.poison_rss_cut_session, hp_flag, rssCutMealy,
          bind_eq_result_bind, result_bind_ok] at hStep ⊢ <;>
        exact hStep.1

/-! ## 3. Multi-Turn Anti-DFA Cut Release & Quarantine Invariant -/

@[expose]
def rssCutTraceSafe (sid mask_comm : Array Std.U8 32#usize)
    (pairs : List (rss_cut_session.RssCutStepInput × rss_cut_session.RssCutStepOutput)) : Prop :=
  pairs = [] ∨
  (∃ cut, pairs = [(.AdvanceRound2Chi sid mask_comm cut, .Round2Ready)]) ∨
  (∃ cut, pairs = [(.AdvanceRound2Chi sid mask_comm cut, .Round2Ready),
                   (.AdvanceRound3VerifyConsistency sid 0#u128 0#u128 0#u64, .Round3Verified)]) ∨
  (∃ cut, pairs = [(.AdvanceRound2Chi sid mask_comm cut, .Round2Ready),
                   (.AdvanceRound3VerifyConsistency sid 0#u128 0#u128 0#u64, .Round3Verified),
                   (.OpenVerifiedCut sid, .CutReleased cut)])

private theorem rss_poisoned_trace_nil
    {st s_f : rss_cut_session.RssCutGateSession}
    {pairs : List (rss_cut_session.RssCutStepInput × rss_cut_session.RssCutStepOutput)}
    (hp : st.poisoned = true)
    (hTr : rssCutMealy.ValidTrace st pairs s_f) :
    pairs = [] := by
  induction hTr with
  | nil _ => rfl
  | @accept sa _ _ _ _ _ hStep _ _ =>
    dsimp only [rssCutMealy] at hStep
    rw [hp] at hStep; cases hStep
  | reject _ _ _ ih =>
    exact ih rfl

private theorem rss_opened_trace_nil
    {st s_f : rss_cut_session.RssCutGateSession}
    {pairs : List (rss_cut_session.RssCutStepInput × rss_cut_session.RssCutStepOutput)}
    (hph : st.phase = .CutOpened)
    (hTr : rssCutMealy.ValidTrace st pairs s_f) :
    pairs = [] := by
  induction hTr with
  | nil _ => rfl
  | @accept sa _ _ inp _ _ hStep _ _ =>
    dsimp only [rssCutMealy] at hStep
    cases hp : sa.poisoned
    · rw [hp] at hStep
      cases inp <;> simp [hph] at hStep
    · rw [hp] at hStep; cases hStep
  | reject _ _ hTail _ =>
    exact rss_poisoned_trace_nil rfl hTail

private theorem rss_round3_trace_shape
    (sid mask_comm cut : Array Std.U8 32#usize)
    {pairs : List (rss_cut_session.RssCutStepInput × rss_cut_session.RssCutStepOutput)}
    {s_f : rss_cut_session.RssCutGateSession}
    (hTr : rssCutMealy.ValidTrace
      { session_id := sid, phase := .Round3ConsistencyVerified,
        mask_commitment := mask_comm, candidate_cut_bytes := cut,
        consistency_verified := true, poisoned := false }
      pairs s_f) :
    pairs = [] ∨ pairs = [(.OpenVerifiedCut sid, .CutReleased cut)] := by
  generalize hs3 :
    ({ session_id := sid, phase := .Round3ConsistencyVerified,
       mask_commitment := mask_comm, candidate_cut_bytes := cut,
       consistency_verified := true, poisoned := false } : rss_cut_session.RssCutGateSession) = s3 at hTr
  induction hTr with
  | nil _ => exact Or.inl rfl
  | @accept sa sb _ inp out rest hStep hTail _ =>
    subst hs3
    dsimp only [rssCutMealy] at hStep
    cases inp with
    | AdvanceRound2Chi _ _ _ => simp at hStep
    | AdvanceRound3VerifyConsistency _ _ _ _ => simp at hStep
    | OpenVerifiedCut req_sid =>
      by_cases hsid : sid = req_sid
      · subst hsid
        simp only [Bool.false_eq_true, decide_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hStep
        rcases hStep with ⟨hsb, hout⟩
        subst hsb; subst hout
        have hRest : rest = [] := rss_opened_trace_nil rfl hTail
        subst hRest
        exact Or.inr rfl
      · simp [hsid] at hStep
  | reject _ _ hTail _ =>
    subst hs3
    exact Or.inl (rss_poisoned_trace_nil rfl hTail)

private theorem rss_round2_trace_shape
    (sid mask_comm cut : Array Std.U8 32#usize)
    {pairs : List (rss_cut_session.RssCutStepInput × rss_cut_session.RssCutStepOutput)}
    {s_f : rss_cut_session.RssCutGateSession}
    (hTr : rssCutMealy.ValidTrace
      { session_id := sid, phase := .Round2ChiEvaluated,
        mask_commitment := mask_comm, candidate_cut_bytes := cut,
        consistency_verified := false, poisoned := false }
      pairs s_f) :
    pairs = [] ∨
    pairs = [(.AdvanceRound3VerifyConsistency sid 0#u128 0#u128 0#u64, .Round3Verified)] ∨
    pairs = [(.AdvanceRound3VerifyConsistency sid 0#u128 0#u128 0#u64, .Round3Verified),
             (.OpenVerifiedCut sid, .CutReleased cut)] := by
  generalize hs2 :
    ({ session_id := sid, phase := .Round2ChiEvaluated,
       mask_commitment := mask_comm, candidate_cut_bytes := cut,
       consistency_verified := false, poisoned := false } : rss_cut_session.RssCutGateSession) = s2 at hTr
  induction hTr with
  | nil _ => exact Or.inl rfl
  | @accept sa sb _ inp out rest hStep hTail _ =>
    subst hs2
    dsimp only [rssCutMealy] at hStep
    cases inp with
    | AdvanceRound2Chi _ _ _ => simp at hStep
    | OpenVerifiedCut _ => simp at hStep
    | AdvanceRound3VerifyConsistency req_sid lo hi dzk =>
      by_cases hsid : sid = req_sid
      · subst hsid
        simp only [Bool.false_eq_true, decide_true, ↓reduceIte] at hStep
        cases hz : (decide (lo = 0#u128) && decide (hi = 0#u128) && decide (dzk = 0#u64))
        · rw [hz] at hStep; cases hStep
        · rw [hz] at hStep
          simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hStep
          rcases hStep with ⟨hsb, hout⟩
          subst hsb; subst hout
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hz
          rcases hz with ⟨⟨rfl, rfl⟩, rfl⟩
          rcases rss_round3_trace_shape sid mask_comm cut hTail with hNil | hOpen
          · subst hNil; exact Or.inr (Or.inl rfl)
          · subst hOpen; exact Or.inr (Or.inr rfl)
      · simp [hsid] at hStep
  | reject _ _ hTail _ =>
    subst hs2
    exact Or.inl (rss_poisoned_trace_nil rfl hTail)

private theorem rss_round1_spec_trace_safe
    (sid mask_comm : Array Std.U8 32#usize)
    {pairs : List (rss_cut_session.RssCutStepInput × rss_cut_session.RssCutStepOutput)}
    {s_f : rss_cut_session.RssCutGateSession}
    (hTr : rssCutMealy.ValidTrace
      { session_id := sid, phase := .Round1MaskCommitted,
        mask_commitment := mask_comm,
        candidate_cut_bytes := Array.repeat 32#usize 0#u8,
        consistency_verified := false, poisoned := false }
      pairs s_f) :
    rssCutTraceSafe sid mask_comm pairs := by
  generalize hs1 :
    ({ session_id := sid, phase := .Round1MaskCommitted,
       mask_commitment := mask_comm,
       candidate_cut_bytes := Array.repeat 32#usize 0#u8,
       consistency_verified := false, poisoned := false } : rss_cut_session.RssCutGateSession) = s1 at hTr
  induction hTr with
  | nil _ => exact Or.inl rfl
  | @accept sa sb _ inp out rest hStep hTail _ =>
    subst hs1
    dsimp only [rssCutMealy] at hStep
    cases inp with
    | AdvanceRound3VerifyConsistency _ _ _ _ => simp at hStep
    | OpenVerifiedCut _ => simp at hStep
    | AdvanceRound2Chi req_sid recomputed_comm cut =>
      by_cases hsid : sid = req_sid
      · subst hsid
        by_cases hmc : mask_comm = recomputed_comm
        · subst hmc
          simp only [Bool.false_eq_true, decide_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hStep
          rcases hStep with ⟨hsb, hout⟩
          subst hsb; subst hout
          rcases rss_round2_trace_shape sid mask_comm cut hTail with hNil | hR3 | hOpen
          · subst hNil; exact Or.inr (Or.inl ⟨cut, rfl⟩)
          · subst hR3; exact Or.inr (Or.inr (Or.inl ⟨cut, rfl⟩))
          · subst hOpen; exact Or.inr (Or.inr (Or.inr ⟨cut, rfl⟩))
        · simp [hmc] at hStep
      · simp [hsid] at hStep
  | reject _ _ hTail _ =>
    subst hs1
    exact Or.inl (rss_poisoned_trace_nil rfl hTail)

private theorem rss_mir_poison_irreversible
    {st st_f : rss_cut_session.RssCutGateSession}
    {turns : List (MirTurn rss_cut_session.RssCutStepInput
      rss_cut_session.RssCutStepOutput rss_cut_session.RssCutError)}
    (hp : st.poisoned = true ∧ st.phase = .Poisoned ∧
          st.candidate_cut_bytes = Array.repeat 32#usize 0#u8)
    (hTr : MirTrace (adaptStateResult rss_cut_session.RssCutGateSession.step) st turns st_f) :
    st_f.poisoned = true ∧ st_f.phase = .Poisoned ∧
      st_f.candidate_cut_bytes = Array.repeat 32#usize 0#u8 := by
  induction hTr with
  | nil _ => exact hp
  | @accept m _ _ _ _ _ hStep _ _ =>
    have hSim := rss_cut_step_sim.ok_sim (s := m) rfl rfl hStep
    dsimp only [rssCutMealy] at hSim
    rw [hp.1] at hSim
    exact False.elim hSim
  | @reject m _ _ _ _ _ hStep _ ih =>
    obtain ⟨_, hRel⟩ := rss_cut_step_sim.err_preserves (s := m) rfl rfl hStep
    subst hRel
    exact ih ⟨rfl, rfl, rfl⟩

private theorem rss_mir_any_rejection_poisons
    {st st_f : rss_cut_session.RssCutGateSession}
    {turns : List (MirTurn rss_cut_session.RssCutStepInput
      rss_cut_session.RssCutStepOutput rss_cut_session.RssCutError)}
    (hTr : MirTrace (adaptStateResult rss_cut_session.RssCutGateSession.step) st turns st_f)
    (hHasRej : ∃ inp err, MirTurn.rejected inp err ∈ turns) :
    st_f.poisoned = true ∧ st_f.phase = .Poisoned ∧
      st_f.candidate_cut_bytes = Array.repeat 32#usize 0#u8 := by
  induction hTr with
  | nil _ =>
    rcases hHasRej with ⟨_, _, hm⟩
    exact False.elim (List.not_mem_nil hm)
  | accept _ _ ih =>
    rcases hHasRej with ⟨inp, err, hm⟩
    simp only [List.mem_cons, reduceCtorEq, false_or] at hm
    exact ih ⟨inp, err, hm⟩
  | @reject m _ _ _ _ _ hStep hTail _ =>
    obtain ⟨_, hRel⟩ := rss_cut_step_sim.err_preserves (s := m) rfl rfl hStep
    subst hRel
    exact rss_mir_poison_irreversible ⟨rfl, rfl, rfl⟩ hTail

theorem rss_cut_session_never_releases_unverified_cut
    (sid mask_comm : Array Std.U8 32#usize)
    (st0 st_final : rss_cut_session.RssCutGateSession)
    (turns : List (MirTurn rss_cut_session.RssCutStepInput
      rss_cut_session.RssCutStepOutput rss_cut_session.RssCutError))
    (hnew : rss_cut_session.RssCutGateSession.new_round1_committed sid mask_comm = .ok st0)
    (htrace : MirTrace (adaptStateResult rss_cut_session.RssCutGateSession.step) st0 turns st_final) :
    rssCutTraceSafe sid mask_comm (mirAcceptedPairs turns) ∧
    (∀ inp cut, (inp, .CutReleased cut) ∈ mirAcceptedPairs turns →
      inp = .OpenVerifiedCut sid ∧
      (.AdvanceRound2Chi sid mask_comm cut, .Round2Ready) ∈ mirAcceptedPairs turns ∧
      (.AdvanceRound3VerifyConsistency sid 0#u128 0#u128 0#u64, .Round3Verified) ∈
        mirAcceptedPairs turns) ∧
    ((∃ inp err, MirTurn.rejected inp err ∈ turns) →
      st_final.poisoned = true ∧ st_final.phase = .Poisoned ∧
      st_final.candidate_cut_bytes = Array.repeat 32#usize 0#u8) := by
  unfold rss_cut_session.RssCutGateSession.new_round1_committed at hnew
  injection hnew with hst0
  obtain ⟨hSafeRaw, _⟩ :=
    rss_cut_step_sim.lift_trace_safety_abs
      (Safe := rssCutTraceSafe sid mask_comm)
      (rss_round1_spec_trace_safe sid mask_comm)
      hst0
      htrace
  have hSafe : rssCutTraceSafe sid mask_comm (mirAcceptedPairs turns) := by
    rw [map_id_pair] at hSafeRaw
    exact hSafeRaw
  refine ⟨hSafe, ?_, rss_mir_any_rejection_poisons htrace⟩
  intro inp cut hMem
  rcases hSafe with hNil | ⟨c, h1⟩ | ⟨c, h2⟩ | ⟨c, h3⟩
  · rw [hNil] at hMem; exact False.elim (List.not_mem_nil hMem)
  · rw [h1] at hMem; simp at hMem
  · rw [h2] at hMem; simp at hMem
  · rw [h3] at hMem ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false, false_or, Prod.mk.injEq,
      rss_cut_session.RssCutStepOutput.CutReleased.injEq, reduceCtorEq, and_false] at hMem
    rcases hMem with ⟨rfl, rfl⟩
    exact ⟨rfl, by simp, by simp⟩

/-! ## 4. Concrete `#tooth` Refusal Witnesses -/

theorem tooth_rss_cut_skip_round3_poisoned :
    let sid := Array.repeat 32#usize 0x41#u8
    let mcomm := Array.repeat 32#usize 0x42#u8
    let cut := Array.repeat 32#usize 0x99#u8
    (rss_cut_session.RssCutGateSession.new_round1_committed sid mcomm >>= fun s1 =>
      rss_cut_session.RssCutGateSession.advance_round2_chi s1 sid mcomm cut >>= fun (s2, _) =>
        rss_cut_session.RssCutGateSession.open_verified_cut s2 sid) =
      .ok ({ session_id := sid, phase := .Poisoned, mask_commitment := mcomm,
             candidate_cut_bytes := Array.repeat 32#usize 0#u8,
             consistency_verified := false, poisoned := true },
           .Err .InvalidPhaseTransition) := by
  have hsid : tower.ct_eq_bytes32 (Array.repeat 32#usize 0x41#u8)
      (Array.repeat 32#usize 0x41#u8) = .ok true := by
    rw [ct_eq_bytes32_spec]; rfl
  have hmcomm : tower.ct_eq_bytes32 (Array.repeat 32#usize 0x42#u8)
      (Array.repeat 32#usize 0x42#u8) = .ok true := by
    rw [ct_eq_bytes32_spec]; rfl
  simp [rss_cut_session.RssCutGateSession.new_round1_committed,
    rss_cut_session.RssCutGateSession.advance_round2_chi,
    rss_cut_session.RssCutGateSession.open_verified_cut,
    rss_cut_session.poison_rss_cut_session, hsid, hmcomm,
    bind_eq_result_bind, result_bind_ok]

theorem tooth_rss_cut_nonzero_mac_poisoned :
    let sid := Array.repeat 32#usize 0x51#u8
    let mcomm := Array.repeat 32#usize 0x52#u8
    let cut := Array.repeat 32#usize 0x88#u8
    (rss_cut_session.RssCutGateSession.new_round1_committed sid mcomm >>= fun s1 =>
      rss_cut_session.RssCutGateSession.advance_round2_chi s1 sid mcomm cut >>= fun (s2, _) =>
        rss_cut_session.RssCutGateSession.advance_round3_verify_consistency
          s2 sid 1#u128 0#u128 0#u64) =
      .ok ({ session_id := sid, phase := .Poisoned, mask_commitment := mcomm,
             candidate_cut_bytes := Array.repeat 32#usize 0#u8,
             consistency_verified := false, poisoned := true },
           .Err .ConsistencyCheckFailed) := by
  have hsid : tower.ct_eq_bytes32 (Array.repeat 32#usize 0x51#u8)
      (Array.repeat 32#usize 0x51#u8) = .ok true := by
    rw [ct_eq_bytes32_spec]; rfl
  have hmcomm : tower.ct_eq_bytes32 (Array.repeat 32#usize 0x52#u8)
      (Array.repeat 32#usize 0x52#u8) = .ok true := by
    rw [ct_eq_bytes32_spec]; rfl
  have hnz : (1#u128 != 0#u128) = true := bne_iff_ne.mpr (by decide)
  simp [rss_cut_session.RssCutGateSession.new_round1_committed,
    rss_cut_session.RssCutGateSession.advance_round2_chi,
    rss_cut_session.RssCutGateSession.advance_round3_verify_consistency,
    rss_cut_session.poison_rss_cut_session, hsid, hmcomm, hnz,
    bind_eq_result_bind, result_bind_ok]

theorem tooth_rss_cut_replay_open_poisoned :
    let sid := Array.repeat 32#usize 0x61#u8
    let mcomm := Array.repeat 32#usize 0x62#u8
    let cut := Array.repeat 32#usize 0x77#u8
    let st_opened : rss_cut_session.RssCutGateSession :=
      { session_id := sid, phase := .CutOpened, mask_commitment := mcomm,
        candidate_cut_bytes := Array.repeat 32#usize 0#u8,
        consistency_verified := true, poisoned := false }
    (rss_cut_session.RssCutGateSession.new_round1_committed sid mcomm >>= fun s1 =>
      rss_cut_session.RssCutGateSession.advance_round2_chi s1 sid mcomm cut >>= fun (s2, _) =>
      rss_cut_session.RssCutGateSession.advance_round3_verify_consistency
        s2 sid 0#u128 0#u128 0#u64 >>= fun (s3, _) =>
      rss_cut_session.RssCutGateSession.open_verified_cut s3 sid) =
        .ok (st_opened, .Ok cut) ∧
    rss_cut_session.RssCutGateSession.open_verified_cut st_opened sid =
      .ok ({ session_id := sid, phase := .Poisoned, mask_commitment := mcomm,
             candidate_cut_bytes := Array.repeat 32#usize 0#u8,
             consistency_verified := false, poisoned := true },
           .Err .InvalidPhaseTransition) := by
  have hsid : tower.ct_eq_bytes32 (Array.repeat 32#usize 0x61#u8)
      (Array.repeat 32#usize 0x61#u8) = .ok true := by
    rw [ct_eq_bytes32_spec]; rfl
  have hmcomm : tower.ct_eq_bytes32 (Array.repeat 32#usize 0x62#u8)
      (Array.repeat 32#usize 0x62#u8) = .ok true := by
    rw [ct_eq_bytes32_spec]; rfl
  constructor <;>
    simp [rss_cut_session.RssCutGateSession.new_round1_committed,
      rss_cut_session.RssCutGateSession.advance_round2_chi,
      rss_cut_session.RssCutGateSession.advance_round3_verify_consistency,
      rss_cut_session.RssCutGateSession.open_verified_cut,
      rss_cut_session.poison_rss_cut_session, hsid, hmcomm,
      bind_eq_result_bind, result_bind_ok]

end qsag_verified.proofs
