module

public import QsagVerified.Proofs.Common
public import QsagVerified.Proofs.MirRefinementKit

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

/-! ## 1. 1-Use Epoch Leaf Guard (`fts_guard_at_most_one_sig_per_epoch`) -/

structure FtsEpochConsumeReq where
  req_key_id : Array Std.U8 32#usize
  req_epoch : Std.U32
  msg_digest : Array Std.U8 32#usize
  deriving DecidableEq

@[expose]
def mirFtsEpochStep (st : fts_spn_guard.FtsEpochGuard) (req : FtsEpochConsumeReq) :
    Result (fts_spn_guard.FtsEpochGuard ×
      core.result.Result fts_spn_guard.FtsEpochPermit fts_spn_guard.FtsGuardError) :=
  fts_spn_guard.FtsEpochGuard.consume_epoch_once st req.req_key_id req.req_epoch req.msg_digest

@[expose]
def ftsEpochMealy :
    MealySpec fts_spn_guard.FtsEpochGuard FtsEpochConsumeReq fts_spn_guard.FtsEpochPermit where
  step st req :=
    if st.poisoned then none
    else if decide (st.key_id = req.req_key_id) then
      if decide (req.req_epoch = st.epoch) then
        if decide (st.epoch < st.max_epochs) && decide (st.used = 0#u8) then
          some ({ st with used := 1#u8 },
            { key_id := st.key_id, authorized_epoch := st.epoch, msg_digest := req.msg_digest })
        else none
      else none
    else none
  errStep st req :=
    if st.poisoned then st
    else if decide (st.key_id = req.req_key_id) then
      if decide (req.req_epoch = st.epoch) then
        { st with poisoned := true }
      else st
    else st

theorem fts_epoch_step_sim :
    MirStepSim ftsEpochMealy (adaptStateResult mirFtsEpochStep)
      Eq (fun a b => a = id b) (fun a b => a = id b) where
  ok_sim {s m m' i_s i_m o_m} hSt hIn hStep := by
    subst m; dsimp only [id] at hIn; subst i_s
    dsimp only [adaptStateResult, mirFtsEpochStep] at hStep ⊢
    unfold fts_spn_guard.FtsEpochGuard.consume_epoch_once at hStep
    dsimp only [ftsEpochMealy]
    cases hp : s.poisoned
    · rw [hp, ct_eq_bytes32_spec] at hStep
      by_cases hkid : s.key_id = i_m.req_key_id
      · by_cases hep : i_m.req_epoch = s.epoch
        · by_cases hge : s.epoch >= s.max_epochs
          · simp [hkid, hep, hge, bind_eq_result_bind, result_bind_ok] at hStep
          · have hlt : s.epoch < s.max_epochs := by
              apply (UScalar.lt_iff_val _ _).mpr
              exact Nat.lt_of_not_ge fun h => hge ((UScalar.le_iff_val _ _).mpr h)
            by_cases hused : s.used = 0#u8
            · simp [hkid, hep, hge, hlt, hused, bind_eq_result_bind, result_bind_ok] at hStep ⊢
              rcases hStep with ⟨rfl, rfl⟩
              exact ⟨rfl, rfl⟩
            · have hne : (s.used != 0#u8) = true := by simp [hused]
              simp [hkid, hep, hge, hne, bind_eq_result_bind, result_bind_ok] at hStep
        · have hne : (i_m.req_epoch != s.epoch) = true := by simp [hep]
          simp [hkid, hne, bind_eq_result_bind, result_bind_ok] at hStep
      · simp [hkid, bind_eq_result_bind, result_bind_ok] at hStep
    · simp [hp, result_bind_ok] at hStep
  err_preserves {s m m' i_s i_m e} hSt hIn hStep := by
    subst m; dsimp only [id] at hIn; subst i_s
    dsimp only [adaptStateResult, mirFtsEpochStep] at hStep ⊢
    unfold fts_spn_guard.FtsEpochGuard.consume_epoch_once at hStep
    dsimp only [ftsEpochMealy]
    cases hp : s.poisoned
    · rw [hp, ct_eq_bytes32_spec] at hStep
      by_cases hkid : s.key_id = i_m.req_key_id
      · by_cases hep : i_m.req_epoch = s.epoch
        · by_cases hge : s.epoch >= s.max_epochs
          · have hnlt : ¬ s.epoch < s.max_epochs := fun hlt =>
              Nat.not_lt_of_ge ((UScalar.le_iff_val _ _).mp hge)
                ((UScalar.lt_iff_val _ _).mp hlt)
            simp [hkid, hep, hge, hnlt, bind_eq_result_bind, result_bind_ok] at hStep ⊢
            exact hStep.1
          · by_cases hused : s.used = 0#u8
            · simp [hkid, hep, hge, hused, bind_eq_result_bind, result_bind_ok] at hStep
            · have hne : (s.used != 0#u8) = true := by simp [hused]
              simp [hkid, hep, hge, hused, hne, bind_eq_result_bind, result_bind_ok] at hStep ⊢
              exact hStep.1
        · have hne : (i_m.req_epoch != s.epoch) = true := by simp [hep]
          simp [hkid, hep, hne, bind_eq_result_bind, result_bind_ok] at hStep ⊢
          exact hStep.1
      · simp [hkid, bind_eq_result_bind, result_bind_ok] at hStep ⊢
        exact hStep.1
    · simp [hp, result_bind_ok] at hStep ⊢
      exact hStep.1

private theorem fts_epoch_exhausted_nil
    {st s_f : fts_spn_guard.FtsEpochGuard}
    {pairs : List (FtsEpochConsumeReq × fts_spn_guard.FtsEpochPermit)}
    (hEx : st.poisoned = true ∨ st.used ≠ 0#u8)
    (hTr : ftsEpochMealy.ValidTrace st pairs s_f) :
    pairs = [] := by
  induction hTr with
  | nil _ => rfl
  | @accept sa _ _ req _ _ hStep _ _ =>
    dsimp only [ftsEpochMealy] at hStep
    rcases hEx with hp | hu
    · rw [hp] at hStep; cases hStep
    · cases hp : sa.poisoned
      · rw [hp] at hStep
        by_cases hkid : sa.key_id = req.req_key_id
        · by_cases hep : req.req_epoch = sa.epoch
          · simp [hkid, hep, hu] at hStep
          · simp [hkid, hep] at hStep
        · simp [hkid] at hStep
      · rw [hp] at hStep; cases hStep
  | @reject sa _ req _ _ _ ih =>
    dsimp only [ftsEpochMealy] at ih
    cases hp : sa.poisoned
    · rw [hp] at ih
      by_cases hkid : sa.key_id = req.req_key_id
      · by_cases hep : req.req_epoch = sa.epoch
        · simp only [Bool.false_eq_true, decide_eq_true hkid, decide_eq_true hep, ↓reduceIte] at ih
          exact ih (Or.inl trivial)
        · simp only [Bool.false_eq_true, decide_eq_true hkid, decide_eq_false hep, ↓reduceIte] at ih
          exact ih hEx
      · simp only [Bool.false_eq_true, decide_eq_false hkid, ↓reduceIte] at ih
        exact ih hEx
    · rw [hp] at ih
      simp only [↓reduceIte] at ih
      exact ih (Or.inl hp)

private theorem fts_epoch_unused_spec_safe
    (key_id : Array Std.U8 32#usize) (epoch max_epochs : Std.U32)
    (st0 s_f : fts_spn_guard.FtsEpochGuard)
    (hnew : fts_spn_guard.FtsEpochGuard.new_unused key_id epoch max_epochs = .ok st0)
    {pairs : List (FtsEpochConsumeReq × fts_spn_guard.FtsEpochPermit)}
    (hTr : ftsEpochMealy.ValidTrace st0 pairs s_f) :
    pairs.length ≤ 1 ∧
    (max_epochs.val ≤ epoch.val → pairs = []) ∧
    ∀ p ∈ pairs,
      p.1.req_key_id = key_id ∧
      p.1.req_epoch = epoch ∧
      epoch.val < max_epochs.val ∧
      p.2 = { key_id := key_id, authorized_epoch := epoch, msg_digest := p.1.msg_digest } := by
  unfold fts_spn_guard.FtsEpochGuard.new_unused at hnew
  by_cases hge : epoch >= max_epochs
  · simp only [hge, ↓reduceIte, Result.ok.injEq] at hnew
    subst hnew
    have hNil : pairs = [] := fts_epoch_exhausted_nil (Or.inl rfl) hTr
    subst hNil
    exact ⟨Nat.zero_le 1, fun _ => rfl, fun _ hm => False.elim (List.not_mem_nil hm)⟩
  · simp only [hge, ↓reduceIte, Result.ok.injEq] at hnew
    have hlt_val : epoch.val < max_epochs.val :=
      Nat.lt_of_not_ge fun h => hge ((UScalar.le_iff_val _ _).mpr h)
    have hlt_u32 : epoch < max_epochs := (UScalar.lt_iff_val _ _).mpr hlt_val
    generalize hs0 : st0 = s_init at hTr
    rw [← hnew] at hs0
    induction hTr with
    | nil _ =>
      exact ⟨Nat.zero_le 1,
        fun hbad => False.elim (Nat.not_lt_of_ge hbad hlt_val),
        fun _ hm => False.elim (List.not_mem_nil hm)⟩
    | @accept sa sb _ req out rest hStep hTail _ =>
      subst hs0
      dsimp only [ftsEpochMealy] at hStep
      by_cases hkid : key_id = req.req_key_id
      · by_cases hep : req.req_epoch = epoch
        · simp only [Bool.false_eq_true, hkid, hep, hlt_u32, decide_true, Bool.true_and,
            ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hStep
          rcases hStep with ⟨hsb, hout⟩
          subst hsb; subst hout
          have hRest : rest = [] :=
            fts_epoch_exhausted_nil (Or.inr (show (1#u8 : Std.U8) ≠ 0#u8 from by decide)) hTail
          subst hRest
          refine ⟨Nat.le_refl 1,
            fun hbad => False.elim (Nat.not_lt_of_ge hbad hlt_val), ?_⟩
          intro p hp
          simp only [List.mem_singleton] at hp
          subst hp
          exact ⟨hkid.symm, hep, hlt_val, by simp [hkid]⟩
        · simp [hkid, hep] at hStep
      · simp [hkid] at hStep
    | reject req _ hTail ih =>
      subst hs0
      dsimp only [ftsEpochMealy] at hTail ih
      by_cases hkid : key_id = req.req_key_id
      · by_cases hep : req.req_epoch = epoch
        · simp only [Bool.false_eq_true, decide_eq_true hkid, decide_eq_true hep, ↓reduceIte] at hTail
          have hNil := fts_epoch_exhausted_nil (Or.inl rfl) hTail
          subst hNil
          exact ⟨Nat.zero_le 1,
            fun hbad => False.elim (Nat.not_lt_of_ge hbad hlt_val),
            fun _ hm => False.elim (List.not_mem_nil hm)⟩
        · simp only [Bool.false_eq_true, decide_eq_true hkid, decide_eq_false hep, ↓reduceIte] at ih
          exact ih trivial
      · simp only [Bool.false_eq_true, decide_eq_false hkid, ↓reduceIte] at ih
        exact ih trivial

theorem fts_guard_at_most_one_sig_per_epoch
    (key_id : Array Std.U8 32#usize) (epoch max_epochs : Std.U32)
    (st0 st_final : fts_spn_guard.FtsEpochGuard)
    (turns : List (MirTurn FtsEpochConsumeReq
      fts_spn_guard.FtsEpochPermit fts_spn_guard.FtsGuardError))
    (hnew : fts_spn_guard.FtsEpochGuard.new_unused key_id epoch max_epochs = .ok st0)
    (htrace : MirTrace (adaptStateResult mirFtsEpochStep) st0 turns st_final) :
    (mirAcceptedPairs turns).length ≤ 1 ∧
    (max_epochs.val ≤ epoch.val → mirAcceptedPairs turns = []) ∧
    ∀ p ∈ mirAcceptedPairs turns,
      p.1.req_key_id = key_id ∧
      p.1.req_epoch = epoch ∧
      epoch.val < max_epochs.val ∧
      p.2 = { key_id := key_id, authorized_epoch := epoch, msg_digest := p.1.msg_digest } := by
  obtain ⟨hSafe, _⟩ :=
    fts_epoch_step_sim.lift_trace_safety_abs
      (Safe := fun pairs =>
        pairs.length ≤ 1 ∧
        (max_epochs.val ≤ epoch.val → pairs = []) ∧
        ∀ p ∈ pairs,
          p.1.req_key_id = key_id ∧
          p.1.req_epoch = epoch ∧
          epoch.val < max_epochs.val ∧
          p.2 = { key_id := key_id, authorized_epoch := epoch, msg_digest := p.1.msg_digest })
      (fun hVal => fts_epoch_unused_spec_safe key_id epoch max_epochs st0 _ hnew hVal)
      rfl
      htrace
  rw [map_id_pair] at hSafe
  exact hSafe

/-! ## 2. 68-Chain Base-5 Constant-Sum `S = 136` Verifier & Constructive Incomparability -/

@[expose]
def u8DigitsNatSum : List Std.U8 → Nat
  | [] => 0
  | d :: ds => d.val + u8DigitsNatSum ds

private theorem wots_cs_sum_fuel (digits : Slice Std.U8)
    (suffix : List Std.U8) (idx : Std.Usize) (sum : Std.U64)
    (hs : digits.val.drop idx.val = suffix) :
    ∃ b, loopFuel (suffix.length + 1)
      (fun (s, i) => fts_spn_guard.wots_cs_verify_68_w5_sum136_loop.body digits s i)
      (sum, idx) = .ok b ∧
      (b = true ↔ (∀ d ∈ suffix, d.val < 5) ∧ sum.val + u8DigitsNatSum suffix = 136) := by
  induction suffix generalizing idx sum with
  | nil =>
    have hlen := congrArg List.length hs
    simp only [List.length_drop, List.length_nil] at hlen
    have hn : ¬ idx < Slice.len digits := by
      intro h
      have := (UScalar.lt_iff_val _ _).mp h
      rw [Slice.len_val] at this
      exact Nat.not_lt_of_ge (Nat.le_of_sub_eq_zero hlen) this
    refine ⟨decide (sum = 136#u64), ?_, ?_⟩
    · simp only [List.length_nil, Nat.zero_add, loopFuel_succ,
        fts_spn_guard.wots_cs_verify_68_w5_sum136_loop.body,
        fts_spn_guard.WOTS_CS_TARGET_SUM, hn, ite_false,
        bind_eq_result_bind, result_bind_ok]
    · simp only [decide_eq_true_eq, List.not_mem_nil, false_implies, implies_true,
        u8DigitsNatSum, Nat.add_zero, true_and]
      exact ⟨fun h => congrArg UScalar.val h, fun h => UScalar.eq_of_val_eq h⟩
  | cons d ds ih =>
    have hlen := congrArg List.length hs
    simp only [List.length_drop, List.length_cons] at hlen
    have hidx : idx.val < digits.val.length :=
      Nat.lt_of_sub_pos (hlen ▸ Nat.zero_lt_succ ds.length)
    have hlt : idx < Slice.len digits := (UScalar.lt_iff_val _ _).mpr (by simpa using hidx)
    have hd : digits.val[idx.val]'hidx = d := by
      have hhead := congrArg List.head? hs
      simpa only [List.head?_drop, List.getElem?_eq_getElem hidx, List.head?_cons,
        Option.some.injEq] using hhead
    have hget : Slice.index_usize digits idx = .ok d := by
      simp only [Slice.index_usize, dite_eq_left hidx, hd]
    rw [List.length_cons, loopFuel_succ]
    dsimp only
    by_cases hbad : d >= 5#u8
    · have hstep : fts_spn_guard.wots_cs_verify_68_w5_sum136_loop.body digits sum idx =
          .ok (.done false) := by
        unfold fts_spn_guard.wots_cs_verify_68_w5_sum136_loop.body fts_spn_guard.WOTS_CS_BASE_W
        simp only [hlt, ite_true, hget, hbad, bind_eq_result_bind, result_bind_ok]
      rw [hstep, result_bind_ok]
      refine ⟨false, rfl, ?_⟩
      have hge : 5 ≤ d.val := (UScalar.le_iff_val _ _).mp hbad
      simp only [Bool.false_eq_true, false_iff]
      intro h
      exact Nat.not_lt_of_ge hge (h.1 d (by simp))
    · have hdw : d.val < 5 :=
        Nat.lt_of_not_ge fun h => hbad ((UScalar.le_iff_val _ _).mpr h)
      let d64 := UScalar.cast .U64 d
      have hd64 : d64.val = d.val := by
        change (d.bv.setWidth 64).toNat = d.bv.toNat
        rw [BitVec.toNat_setWidth]
        have hb8 : d.bv.toNat < 2 ^ 8 := d.bv.isLt
        exact Nat.mod_eq_of_lt (Nat.lt_trans hb8 (by decide))
      have hb : d64.val ≤ 18446744073709551615 := by
        have h := d.bv.isLt
        change d.val < 2 ^ 8 at h
        rw [hd64]
        exact Nat.le_trans (Nat.le_of_lt h) (by decide)
      let capacity : Std.U64 := ⟨core.num.U64.MAX.bv - d64.bv⟩
      have hsub : (core.num.U64.MAX - d64 : Result Std.U64) = .ok capacity := by
        have hb' : d64.val ≤ core.num.U64.MAX.val := hb
        simp only [hSub_uscalar_eq, hb', ite_true]
        rfl
      have hcap : capacity.val = 18446744073709551615 - d.val := by
        change (core.num.U64.MAX.bv - d64.bv).toNat = _
        rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hb)]
        change 18446744073709551615 - d64.val = _
        rw [hd64]
      by_cases hov : sum > capacity
      · have hstep : fts_spn_guard.wots_cs_verify_68_w5_sum136_loop.body digits sum idx =
            .ok (.done false) := by
          unfold fts_spn_guard.wots_cs_verify_68_w5_sum136_loop.body fts_spn_guard.WOTS_CS_BASE_W
          simp only [hlt, ite_true, hget, hbad, ite_false, lift_eq_ok,
            bind_eq_result_bind, result_bind_ok]
          rw [hsub, result_bind_ok]
          simp only [hov, ite_true]
        rw [hstep, result_bind_ok]
        refine ⟨false, rfl, ?_⟩
        have hgt := (UScalar.lt_iff_val _ _).mp hov
        simp only [Bool.false_eq_true, false_iff]
        intro h
        simp only [u8DigitsNatSum] at h
        have hlarge : 18446744073709551615 < sum.val + d.val := by
          rw [hcap] at hgt
          have := Nat.add_lt_add_right hgt d.val
          rw [Nat.sub_add_cancel (by simpa only [hd64] using hb)] at this
          exact this
        have htotal : 18446744073709551615 < 136 := by
          rw [← h.2, ← Nat.add_assoc]
          exact Nat.lt_of_lt_of_le hlarge (Nat.le_add_right _ _)
        exact absurd htotal (by decide)
      · have hsum : sum.val + d64.val < 2 ^ 64 := by
          have hle : sum.val ≤ capacity.val :=
            Nat.le_of_not_gt fun h => hov ((UScalar.lt_iff_val _ _).mpr h)
          rw [hd64]
          have hbound := Nat.add_le_add_right hle d.val
          rw [hcap, Nat.sub_add_cancel (by simpa only [hd64] using hb)] at hbound
          exact Nat.lt_succ_of_le hbound
        let sum' : Std.U64 := ⟨sum.bv + d64.bv⟩
        have hadd : (sum + d64 : Result Std.U64) = .ok sum' := by
          simp only [hAdd_uscalar_eq, hsum, ite_true]
          rfl
        have hsum' : sum'.val = sum.val + d.val := by
          change (sum.bv + d64.bv).toNat = _
          rw [BitVec.toNat_add, Nat.mod_eq_of_lt hsum, hd64]
        let idx' : Std.Usize := ⟨idx.bv + (1#usize).bv⟩
        have hbound : idx.val + 1 < 2 ^ 64 := by
          have h : (Slice.len digits).val < 2 ^ 64 := (Slice.len digits).bv.isLt
          rw [Slice.len_val] at h
          exact Nat.lt_of_le_of_lt hidx h
        have hinc : (idx + 1#usize : Result Std.Usize) = .ok idx' := by
          simp [hAdd_uscalar_eq, hbound, idx']
        have hidx' : idx'.val = idx.val + 1 := by
          change (idx.bv + (1#usize).bv).toNat = _
          rw [BitVec.toNat_add]
          exact Nat.mod_eq_of_lt hbound
        have hs' : digits.val.drop idx'.val = ds := by
          rw [hidx', ← List.drop_drop, hs]
          rfl
        have hstep : fts_spn_guard.wots_cs_verify_68_w5_sum136_loop.body digits sum idx =
            .ok (.cont (sum', idx')) := by
          unfold fts_spn_guard.wots_cs_verify_68_w5_sum136_loop.body fts_spn_guard.WOTS_CS_BASE_W
          simp only [hlt, ite_true, hget, hbad, ite_false, lift_eq_ok,
            bind_eq_result_bind, result_bind_ok]
          rw [hsub, result_bind_ok]
          simp only [hov, ite_false]
          rw [hadd, result_bind_ok, hinc, result_bind_ok]
        obtain ⟨b, hb_loop, he⟩ := ih idx' sum' hs'
        rw [hstep, result_bind_ok]
        refine ⟨b, hb_loop, ?_⟩
        rw [he]
        simp only [List.mem_cons, forall_eq_or_imp, hdw, true_and, u8DigitsNatSum, hsum',
          Nat.add_assoc]

theorem wots_cs_verify_68_w5_sum136_spec (digits : Slice Std.U8) :
    ∃ b, fts_spn_guard.wots_cs_verify_68_w5_sum136 digits = .ok b ∧
      (b = true ↔ digits.val.length = 68 ∧
        (∀ d ∈ digits.val, d.val < 5) ∧ u8DigitsNatSum digits.val = 136) := by
  unfold fts_spn_guard.wots_cs_verify_68_w5_sum136 fts_spn_guard.WOTS_CS_CHAINS
  by_cases he : Slice.len digits = 68#usize
  · have helen : digits.val.length = 68 := by
      rw [← Slice.len_val, he]; rfl
    simp only [he, bne_self_eq_false, Bool.false_eq_true, ite_false]
    obtain ⟨b, hb, hiff⟩ := wots_cs_sum_fuel digits digits.val 0#usize 0#u64 List.drop_zero
    refine ⟨b, ?_, ?_⟩
    · unfold fts_spn_guard.wots_cs_verify_68_w5_sum136_loop
      apply loop_ok_of_loopFuel (fuel := digits.val.length + 1)
      · simpa only [Slice.len_val] using usize_lt_loopMaxFuel (Slice.len digits)
      · exact hb
    · rw [hiff]
      simp only [helen, true_and, show (0#u64).val = 0 from rfl, Nat.zero_add]
  · have hnelen : digits.val.length ≠ 68 := by
      intro h
      exact he (UScalar.eq_of_val_eq (by rw [Slice.len_val, h]; rfl))
    have hne : (Slice.len digits != 68#usize) = true := bne_iff_ne.mpr he
    simp only [hne, ↓reduceIte]
    exact ⟨false, rfl, by simp [hnelen]⟩

theorem wots_cs_verify_68_array_spec (digits : Array Std.U8 68#usize) :
    ∃ b, fts_spn_guard.wots_cs_verify_68_array digits = .ok b ∧
      (b = true ↔ (∀ d ∈ digits.val, d.val < 5) ∧ u8DigitsNatSum digits.val = 136) := by
  unfold fts_spn_guard.wots_cs_verify_68_array
  simp only [bind_eq_result_bind, lift_eq_ok, result_bind_ok]
  obtain ⟨b, hb, hiff⟩ := wots_cs_verify_68_w5_sum136_spec (Array.to_slice digits)
  refine ⟨b, hb, ?_⟩
  have hlen : (Array.to_slice digits).val.length = 68 := digits.property
  have hval : (Array.to_slice digits).val = digits.val := rfl
  rw [hiff, hval]
  exact ⟨fun h => h.2, fun h => ⟨digits.property, h⟩⟩

private def findStrictGt : List Std.U8 → List Std.U8 → Option Nat
  | [], _ => none
  | _, [] => none
  | x :: xs, y :: ys =>
    if y.val < x.val then some 0
    else (findStrictGt xs ys).map Nat.succ

private theorem findStrictGt_some :
    ∀ {xs ys : List Std.U8} {idx : Nat},
      findStrictGt xs ys = some idx →
      ys.length = xs.length →
      idx < xs.length ∧ (ys.getD idx 0#u8).val < (xs.getD idx 0#u8).val
  | [], _, _, h, _ => by cases h
  | _ :: _, [], _, h, _ => by cases h
  | x :: xs, y :: ys, idx, h, hlen => by
    dsimp only [findStrictGt] at h
    by_cases hlt : y.val < x.val
    · simp only [hlt, ↓reduceIte] at h
      injection h with h0
      subst h0
      refine ⟨Nat.zero_lt_succ _, ?_⟩
      simpa [List.getD] using hlt
    · simp only [hlt, ↓reduceIte] at h
      cases hrec : findStrictGt xs ys with
      | none =>
        rw [hrec] at h; cases h
      | some k =>
        rw [hrec] at h
        simp only [Option.map, Option.some.injEq] at h
        subst h
        obtain ⟨hk, hval⟩ := findStrictGt_some hrec (Nat.succ.inj hlen)
        refine ⟨Nat.succ_lt_succ hk, ?_⟩
        simpa [List.getD] using hval

private theorem findStrictGt_none :
    ∀ {xs ys : List Std.U8},
      findStrictGt xs ys = none →
      ys.length = xs.length →
      u8DigitsNatSum xs ≤ u8DigitsNatSum ys ∧
      (u8DigitsNatSum xs = u8DigitsNatSum ys → xs = ys)
  | [], [], _, _ => ⟨Nat.le_refl 0, fun _ => rfl⟩
  | [], _ :: _, _, hlen => by cases hlen
  | _ :: _, [], _, hlen => by cases hlen
  | x :: xs, y :: ys, hnone, hlen => by
    dsimp only [findStrictGt] at hnone
    by_cases hlt : y.val < x.val
    · simp only [hlt, ↓reduceIte] at hnone; cases hnone
    · simp only [hlt, ↓reduceIte] at hnone
      have hxy : x.val ≤ y.val := Nat.le_of_not_gt hlt
      cases hrec : findStrictGt xs ys with
      | some _ =>
        rw [hrec] at hnone; cases hnone
      | none =>
        obtain ⟨hle_tail, heq_tail⟩ := findStrictGt_none hrec (Nat.succ.inj hlen)
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
          rw [hx_eq_y] at hsum_eq
          exact Nat.add_left_cancel hsum_eq
        rw [UScalar.eq_of_val_eq hx_eq_y, heq_tail htail_eq]

