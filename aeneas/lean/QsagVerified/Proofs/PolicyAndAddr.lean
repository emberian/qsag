module

public import QsagVerified.Proofs.Common
public import QsagVerified.Proofs.Adrs
public import QsagVerified.Proofs.MirRefinementKit
public import QsagVerified.Proofs.Sponge

public section

/-!
# `PolicyAndAddr`: MIR Multi-Turn Velocity Cap Soundness, Canonical 128-Byte Intent Bijection & Hybrid Framing

Mechanizes multi-turn safety and canonical wire bijectivity directly over the
Charon + Aeneas extracted Rust MIR of `qsag_verified::policy_and_addr`
(`0` axioms beyond `{propext, Quot.sound}`, `0 Classical.choice`, `0` unproved holes):

1. **`policy_velocity_guard_multiturn_cap_sound` & `velocity_spend_step_sim`:**
   Lifts `StatefulVelocityGuard::authorize_spend` onto `MirRefinementKit` (`MealySpec.ofPure`)
   and proves across arbitrary `N`-turn `MirTrace` executions that:
   - `u128AmountsNatSum ((mirAcceptedPairs turns).map Prod.snd) = st_final.spent_units.val`
   - `u128AmountsNatSum ((mirAcceptedPairs turns).map Prod.snd) ≤ cap_units.val`
   - Accepted nonces are strictly positive and strictly increasing (`List.Pairwise (· < ·)`)
   - Every accepted request is cryptographically pinned to `(window_id, policy_pin, authority_pin)`
2. **`rotate_window_resets_spent_monotone_spec`:**
   Proves `StatefulVelocityGuard::rotate_window` enforces pin equality and strict
   window monotonicity (`window_id < next_window_id`) before resetting `spent_units := 0`.
3. **`intent_codec_roundtrip_injective_mir`:**
   Proves total 128-byte encode/decode roundtrip, converse canonicality
   (`decode b = some i → encode i = b`), and full `encode_intent_128` injectivity (`P0-10`/`P1-01`).
4. **`check_hybrid_domain_framing_spec`, `hybrid_domain_framing_role_disjoint_mir`,
   `derive_hybrid_transcript_digest_total`:**
   Proves exact constant-time `"QSAG.HYBRID.V2"` framing semantics, disjointness between
   `Classical` and `PostQuantum` leg signatures, and total SHAKE256 transcript derivation.
5. **Concrete `#tooth` Refusal Witnesses:**
   `tooth_policy_cap_exceeded_rejected`, `tooth_policy_u128_overflow_rejected`,
   `tooth_intent_bad_magic_rejected`, `tooth_hybrid_role_confusion_rejected`.
-/

namespace qsag_verified.proofs

open Aeneas Aeneas.Std Result ControlFlow Error
open qsag_verified

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

attribute [-simp] BitVec.getLsbD_eq_getElem BitVec.setWidth_ofNat_of_le
attribute [local simp] UScalar.val UScalarTy.numBits

/-! ## 1. `StatefulVelocityGuard` Multi-Turn Cap Soundness & Window Rotation -/

@[expose]
def u128AmountsNatSum : List Std.U128 → Nat
  | [] => 0
  | x :: xs => x.val + u128AmountsNatSum xs

@[expose]
def velocitySpendStep (st : policy_and_addr.StatefulVelocityGuard)
    (req : policy_and_addr.VelocitySpendRequest) :
    Option (policy_and_addr.StatefulVelocityGuard × Std.U128) :=
  if decide (st.policy_pin = req.policy_pin) &&
     decide (st.authority_pin = req.authority_pin) &&
     decide (req.window_id = st.window_id) &&
     decide (st.last_nonce.val < req.nonce.val) &&
     decide (st.spent_units.val + req.amount_units.val ≤ st.cap_units.val) then
    some ({ st with
            spent_units := ⟨st.spent_units.bv + req.amount_units.bv⟩
            last_nonce := req.nonce },
          req.amount_units)
  else none

@[expose]
def velocitySpendMealy :
    MealySpec policy_and_addr.StatefulVelocityGuard
      policy_and_addr.VelocitySpendRequest Std.U128 :=
  MealySpec.ofPure velocitySpendStep

private theorem u128_val_le_max (x : Std.U128) :
    x.val ≤ 340282366920938463463374607431768211455 := by
  have hlt : x.val < 340282366920938463463374607431768211455 + 1 := x.bv.isLt
  exact Nat.le_of_lt_succ hlt

private theorem max_velocity_sub_spec (spent : Std.U128) :
    ∃ rem : Std.U128,
      (policy_and_addr.MAX_VELOCITY_U128 - spent : Result Std.U128) = .ok rem ∧
      rem.val = 340282366920938463463374607431768211455 - spent.val := by
  have hb : spent.val ≤ 340282366920938463463374607431768211455 := u128_val_le_max spent
  let rem : Std.U128 :=
    ⟨(340282366920938463463374607431768211455#u128).bv - spent.bv⟩
  refine ⟨rem, ?_, ?_⟩
  · unfold policy_and_addr.MAX_VELOCITY_U128
    have hb' : spent.val ≤ (340282366920938463463374607431768211455#u128).val := hb
    simp only [hSub_uscalar_eq, hb', ↓reduceIte]
    rfl
  · change ((340282366920938463463374607431768211455#u128).bv - spent.bv).toNat = _
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hb)]
    rfl

theorem velocity_spend_step_sim :
    MirStepSim velocitySpendMealy
      (adaptStateResult policy_and_addr.StatefulVelocityGuard.authorize_spend)
      Eq (fun a b => a = id b) (fun a b => a = id b) where
  ok_sim {s m m' i_s i_m o_m} hSt hIn hStep := by
    subst m; dsimp only [id] at hIn; subst i_s
    dsimp only [adaptStateResult, velocitySpendMealy, MealySpec.ofPure,
      velocitySpendStep] at hStep ⊢
    unfold policy_and_addr.StatefulVelocityGuard.authorize_spend at hStep
    rw [ct_eq_bytes32_spec, ct_eq_bytes32_spec] at hStep
    by_cases hp : s.policy_pin = i_m.policy_pin
    · by_cases ha : s.authority_pin = i_m.authority_pin
      · by_cases hw : i_m.window_id = s.window_id
        · by_cases hle_n : i_m.nonce <= s.last_nonce
          · simp [hp, ha, hw, hle_n, bind_eq_result_bind, result_bind_ok] at hStep
          · have hlt_n : s.last_nonce.val < i_m.nonce.val :=
              Nat.lt_of_not_ge fun h => hle_n ((UScalar.le_iff_val _ _).mpr h)
            obtain ⟨rem, hrem, hrem_val⟩ := max_velocity_sub_spec s.spent_units
            simp only [decide_eq_true hp, decide_eq_true ha, hw, bne_self_eq_false,
              Bool.false_eq_true, hle_n, ↓reduceIte, bind_eq_result_bind,
              result_bind_ok] at hStep
            rw [hrem, result_bind_ok] at hStep
            by_cases hov : i_m.amount_units > rem
            · simp [hov, Result.bind] at hStep
            · have hamt_le : i_m.amount_units.val ≤ rem.val :=
                Nat.le_of_not_gt fun h => hov ((UScalar.lt_iff_val _ _).mpr h)
              have hsum_le_max :
                  s.spent_units.val + i_m.amount_units.val ≤
                    340282366920938463463374607431768211455 := by
                have h1 := Nat.add_le_add_right hamt_le s.spent_units.val
                rw [hrem_val,
                  Nat.sub_add_cancel (u128_val_le_max s.spent_units),
                  Nat.add_comm] at h1
                exact h1
              have hsum_lt : s.spent_units.val + i_m.amount_units.val < 2 ^ 128 :=
                Nat.lt_succ_of_le hsum_le_max
              let new_spent : Std.U128 := ⟨s.spent_units.bv + i_m.amount_units.bv⟩
              have hadd : (s.spent_units + i_m.amount_units : Result Std.U128) = .ok new_spent := by
                simp only [hAdd_uscalar_eq, hsum_lt, ↓reduceIte]; rfl
              have hnew_val : new_spent.val = s.spent_units.val + i_m.amount_units.val := by
                change (s.spent_units.bv + i_m.amount_units.bv).toNat = _
                rw [BitVec.toNat_add, Nat.mod_eq_of_lt hsum_lt]
              simp only [hov, ↓reduceIte] at hStep
              rw [hadd, result_bind_ok] at hStep
              by_cases hcap : new_spent > s.cap_units
              · simp [hcap, Result.bind] at hStep
              · have hle_cap : s.spent_units.val + i_m.amount_units.val ≤ s.cap_units.val := by
                  rw [← hnew_val]
                  exact Nat.le_of_not_gt fun h => hcap ((UScalar.lt_iff_val _ _).mpr h)
                simp only [hcap, ↓reduceIte, Result.bind, Result.ok.injEq,
                  MirOutcome.accepted.injEq] at hStep
                rcases hStep with ⟨rfl, rfl⟩
                simp only [decide_eq_true hp, decide_eq_true ha, decide_eq_true hw,
                  decide_eq_true hlt_n, decide_eq_true hle_cap, Bool.and_self, ↓reduceIte]
                exact ⟨rfl, rfl⟩
        · have hne : (i_m.window_id != s.window_id) = true := bne_iff_ne.mpr hw
          simp [hp, ha, hne, bind_eq_result_bind, result_bind_ok] at hStep
      · simp [hp, ha, bind_eq_result_bind, result_bind_ok] at hStep
    · simp [hp, bind_eq_result_bind, result_bind_ok] at hStep
  err_preserves {s m m' i_s i_m e} hSt hIn hStep := by
    subst m; dsimp only [id] at hIn; subst i_s
    dsimp only [adaptStateResult, velocitySpendMealy, MealySpec.ofPure,
      velocitySpendStep] at hStep ⊢
    unfold policy_and_addr.StatefulVelocityGuard.authorize_spend at hStep
    rw [ct_eq_bytes32_spec, ct_eq_bytes32_spec] at hStep
    by_cases hp : s.policy_pin = i_m.policy_pin
    · by_cases ha : s.authority_pin = i_m.authority_pin
      · by_cases hw : i_m.window_id = s.window_id
        · by_cases hle_n : i_m.nonce <= s.last_nonce
          · have hnlt_n : ¬ s.last_nonce.val < i_m.nonce.val :=
              Nat.not_lt_of_ge ((UScalar.le_iff_val _ _).mp hle_n)
            simp [hp, ha, hw, hle_n, hnlt_n, bind_eq_result_bind, result_bind_ok] at hStep ⊢
            exact hStep.1
          · obtain ⟨rem, hrem, hrem_val⟩ := max_velocity_sub_spec s.spent_units
            simp only [decide_eq_true hp, decide_eq_true ha, hw, bne_self_eq_false,
              Bool.false_eq_true, hle_n, ↓reduceIte, bind_eq_result_bind,
              result_bind_ok] at hStep
            rw [hrem, result_bind_ok] at hStep
            by_cases hov : i_m.amount_units > rem
            · have hgt : rem.val < i_m.amount_units.val := (UScalar.lt_iff_val _ _).mp hov
              have hover_cap : ¬ (s.spent_units.val + i_m.amount_units.val ≤ s.cap_units.val) := by
                intro hle
                have hlarge : 340282366920938463463374607431768211455 <
                    s.spent_units.val + i_m.amount_units.val := by
                  have h1 := Nat.add_lt_add_left hgt s.spent_units.val
                  rw [hrem_val, Nat.add_comm,
                    Nat.sub_add_cancel (u128_val_le_max s.spent_units)] at h1
                  exact h1
                exact Nat.not_lt_of_ge
                  (Nat.le_trans hle (u128_val_le_max s.cap_units)) hlarge
              simp only [hov, ↓reduceIte, Result.bind, Result.ok.injEq,
                MirOutcome.rejected.injEq] at hStep
              simp only [decide_eq_false hover_cap, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
              exact ⟨trivial, hStep.1⟩
            · have hamt_le : i_m.amount_units.val ≤ rem.val :=
                Nat.le_of_not_gt fun h => hov ((UScalar.lt_iff_val _ _).mpr h)
              have hsum_le_max :
                  s.spent_units.val + i_m.amount_units.val ≤
                    340282366920938463463374607431768211455 := by
                have h1 := Nat.add_le_add_right hamt_le s.spent_units.val
                rw [hrem_val,
                  Nat.sub_add_cancel (u128_val_le_max s.spent_units),
                  Nat.add_comm] at h1
                exact h1
              have hsum_lt : s.spent_units.val + i_m.amount_units.val < 2 ^ 128 :=
                Nat.lt_succ_of_le hsum_le_max
              let new_spent : Std.U128 := ⟨s.spent_units.bv + i_m.amount_units.bv⟩
              have hadd : (s.spent_units + i_m.amount_units : Result Std.U128) = .ok new_spent := by
                simp only [hAdd_uscalar_eq, hsum_lt, ↓reduceIte]; rfl
              have hnew_val : new_spent.val = s.spent_units.val + i_m.amount_units.val := by
                change (s.spent_units.bv + i_m.amount_units.bv).toNat = _
                rw [BitVec.toNat_add, Nat.mod_eq_of_lt hsum_lt]
              simp only [hov, ↓reduceIte] at hStep
              rw [hadd, result_bind_ok] at hStep
              by_cases hcap : new_spent > s.cap_units
              · have hnle_cap : ¬ (s.spent_units.val + i_m.amount_units.val ≤ s.cap_units.val) := by
                  rw [← hnew_val]
                  exact Nat.not_le_of_gt ((UScalar.lt_iff_val _ _).mp hcap)
                simp only [hcap, ↓reduceIte, Result.bind, Result.ok.injEq,
                  MirOutcome.rejected.injEq] at hStep
                simp only [decide_eq_false hnle_cap, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
                exact ⟨trivial, hStep.1⟩
              · simp [hcap, Result.bind] at hStep
        · have hne : (i_m.window_id != s.window_id) = true := bne_iff_ne.mpr hw
          simp [hp, ha, hw, hne, bind_eq_result_bind, result_bind_ok] at hStep ⊢
          exact hStep.1
      · simp [hp, ha, bind_eq_result_bind, result_bind_ok] at hStep ⊢
        exact hStep.1
    · simp [hp, bind_eq_result_bind, result_bind_ok] at hStep ⊢
      exact hStep.1

private theorem velocity_mir_trace_invariant
    {st st_f : policy_and_addr.StatefulVelocityGuard}
    {turns : List (MirTurn policy_and_addr.VelocitySpendRequest
      Std.U128 policy_and_addr.PolicyAddrError)}
    (hInitLe : st.spent_units.val ≤ st.cap_units.val)
    (hTr : MirTrace (adaptStateResult policy_and_addr.StatefulVelocityGuard.authorize_spend)
      st turns st_f) :
    st.spent_units.val + u128AmountsNatSum ((mirAcceptedPairs turns).map Prod.snd) =
      st_f.spent_units.val ∧
    st_f.spent_units.val ≤ st.cap_units.val ∧
    st_f.window_id = st.window_id ∧
    st_f.cap_units = st.cap_units ∧
    st_f.policy_pin = st.policy_pin ∧
    st_f.authority_pin = st.authority_pin ∧
    st.last_nonce.val ≤ st_f.last_nonce.val ∧
    ((mirAcceptedPairs turns).map (fun p => p.1.nonce.val)).Pairwise (· < ·) ∧
    ∀ p ∈ mirAcceptedPairs turns,
      st.last_nonce.val < p.1.nonce.val ∧
      p.1.window_id = st.window_id ∧
      p.1.policy_pin = st.policy_pin ∧
      p.1.authority_pin = st.authority_pin ∧
      p.2 = p.1.amount_units := by
  induction hTr with
  | nil m =>
    exact ⟨Nat.add_zero _, hInitLe, rfl, rfl, rfl, rfl, Nat.le_refl _,
      List.Pairwise.nil, fun _ hm => False.elim (List.not_mem_nil hm)⟩
  | @accept m m' m_final req out rest hStep _ ih =>
    have hSim := velocity_spend_step_sim.ok_sim (s := m) rfl rfl hStep
    dsimp only [velocitySpendMealy, MealySpec.ofPure, velocitySpendStep, id] at hSim
    cases hcond :
        (decide (m.policy_pin = req.policy_pin) &&
         decide (m.authority_pin = req.authority_pin) &&
         decide (req.window_id = m.window_id) &&
         decide (m.last_nonce.val < req.nonce.val) &&
         decide (m.spent_units.val + req.amount_units.val ≤ m.cap_units.val))
    · rw [hcond] at hSim; exact False.elim hSim
    · rw [hcond] at hSim
      rcases hSim with ⟨hm', hout⟩
      subst hm'; subst hout
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      rcases hcond with ⟨⟨⟨⟨hp, ha⟩, hw⟩, hnonce⟩, hcap_le⟩
      have hsum_lt : m.spent_units.val + req.amount_units.val < 2 ^ 128 :=
        Nat.lt_of_le_of_lt hcap_le m.cap_units.bv.isLt
      have hnew_val :
          (⟨m.spent_units.bv + req.amount_units.bv⟩ : Std.U128).val =
            m.spent_units.val + req.amount_units.val := by
        change (m.spent_units.bv + req.amount_units.bv).toNat = _
        rw [BitVec.toNat_add, Nat.mod_eq_of_lt hsum_lt]
      have hNextLe :
          (⟨m.spent_units.bv + req.amount_units.bv⟩ : Std.U128).val ≤ m.cap_units.val := by
        rw [hnew_val]; exact hcap_le
      obtain ⟨hSumTail, hLeTail, hWid, hCap, hPol, hAuth, hNonceLe, hPairTail, hMemTail⟩ :=
        ih hNextLe
      dsimp only [mirAcceptedPairs, List.map, u128AmountsNatSum]
      refine ⟨?_, hLeTail, hWid, hCap, hPol, hAuth,
        Nat.le_trans (Nat.le_of_lt hnonce) hNonceLe, ?_, ?_⟩
      · rw [← Nat.add_assoc, ← hnew_val]
        exact hSumTail
      · refine List.Pairwise.cons ?_ hPairTail
        intro n hn
        obtain ⟨q, hq_mem, rfl⟩ := List.mem_map.mp hn
        exact (hMemTail q hq_mem).1
      · intro p hp_mem
        simp only [List.mem_cons] at hp_mem
        rcases hp_mem with rfl | hp_tail
        · exact ⟨hnonce, hw, hp.symm, ha.symm, rfl⟩
        · obtain ⟨hn_gt, hq_w, hq_p, hq_a, hq_o⟩ := hMemTail p hp_tail
          exact ⟨Nat.lt_trans hnonce hn_gt, hq_w, hq_p, hq_a, hq_o⟩
  | @reject m m' m_final req err rest hStep _ ih =>
    obtain ⟨_, hm'⟩ := velocity_spend_step_sim.err_preserves (s := m) rfl rfl hStep
    dsimp only [velocitySpendMealy, MealySpec.ofPure] at hm'
    subst hm'
    exact ih hInitLe

theorem policy_velocity_guard_multiturn_cap_sound
    (wid : Std.U64) (cap : Std.U128)
    (policy_pin authority_pin : Array Std.U8 32#usize)
    (st0 st_final : policy_and_addr.StatefulVelocityGuard)
    (turns : List (MirTurn policy_and_addr.VelocitySpendRequest
      Std.U128 policy_and_addr.PolicyAddrError))
    (hnew : policy_and_addr.StatefulVelocityGuard.new_window
      wid cap policy_pin authority_pin = .ok st0)
    (htrace : MirTrace (adaptStateResult policy_and_addr.StatefulVelocityGuard.authorize_spend)
      st0 turns st_final) :
    u128AmountsNatSum ((mirAcceptedPairs turns).map Prod.snd) = st_final.spent_units.val ∧
    u128AmountsNatSum ((mirAcceptedPairs turns).map Prod.snd) ≤ cap.val ∧
    st_final.spent_units.val ≤ cap.val ∧
    st_final.window_id = wid ∧
    st_final.cap_units = cap ∧
    st_final.policy_pin = policy_pin ∧
    st_final.authority_pin = authority_pin ∧
    ((mirAcceptedPairs turns).map (fun p => p.1.nonce.val)).Pairwise (· < ·) ∧
    ∀ p ∈ mirAcceptedPairs turns,
      0 < p.1.nonce.val ∧
      p.1.window_id = wid ∧
      p.1.policy_pin = policy_pin ∧
      p.1.authority_pin = authority_pin ∧
      p.2 = p.1.amount_units := by
  unfold policy_and_addr.StatefulVelocityGuard.new_window at hnew
  injection hnew with hst0
  subst hst0
  obtain ⟨hSum, hLe, hWid, hCap, hPol, hAuth, _, hPair, hMem⟩ :=
    velocity_mir_trace_invariant (hTr := htrace) (show (0#u128).val ≤ cap.val from Nat.zero_le cap.val)
  have hSum0 :
      u128AmountsNatSum ((mirAcceptedPairs turns).map Prod.snd) = st_final.spent_units.val := by
    simpa only [show (0#u128).val = 0 from rfl, Nat.zero_add] using hSum
  exact ⟨hSum0, hSum0 ▸ hLe, hLe, hWid, hCap, hPol, hAuth, hPair, hMem⟩

theorem rotate_window_resets_spent_monotone_spec
    (st : policy_and_addr.StatefulVelocityGuard) (next_wid : Std.U64)
    (req_p req_a : Array Std.U8 32#usize) :
    ∃ st' res,
      policy_and_addr.StatefulVelocityGuard.rotate_window st next_wid req_p req_a =
        .ok (st', res) ∧
      (res = .Ok () ↔
        st.policy_pin = req_p ∧ st.authority_pin = req_a ∧ st.window_id.val < next_wid.val) ∧
      (res = .Ok () →
        st' = { st with window_id := next_wid, spent_units := 0#u128 }) ∧
      (∀ e, res = .Err e → st' = st) := by
  unfold policy_and_addr.StatefulVelocityGuard.rotate_window
  rw [ct_eq_bytes32_spec, ct_eq_bytes32_spec]
  by_cases hp : st.policy_pin = req_p
  · by_cases ha : st.authority_pin = req_a
    · by_cases hle : next_wid <= st.window_id
      · have hnlt : ¬ st.window_id.val < next_wid.val :=
          Nat.not_lt_of_ge ((UScalar.le_iff_val _ _).mp hle)
        simp only [decide_eq_true hp, decide_eq_true ha, hle, ↓reduceIte,
          bind_eq_result_bind, result_bind_ok]
        refine ⟨st, .Err .InvalidWindowRotation, rfl, ?_, ?_, fun _ _ => rfl⟩
        · simp [hnlt]
        · intro h; cases h
      · have hlt : st.window_id.val < next_wid.val :=
          Nat.lt_of_not_ge fun h => hle ((UScalar.le_iff_val _ _).mpr h)
        simp only [decide_eq_true hp, decide_eq_true ha, hle, ↓reduceIte,
          bind_eq_result_bind, result_bind_ok]
        refine ⟨{ st with window_id := next_wid, spent_units := 0#u128 },
          .Ok (), rfl, ?_, fun _ => rfl, ?_⟩
        · simp [hp, ha, hlt]
        · intro _ h; cases h
    · simp only [decide_eq_true hp, decide_eq_false ha, Bool.false_eq_true, ↓reduceIte,
        bind_eq_result_bind, result_bind_ok]
      refine ⟨st, .Err .AuthorityPinMismatch, rfl, ?_, ?_, fun _ _ => rfl⟩
      · simp [ha]
      · intro h; cases h
  · simp only [decide_eq_false hp, Bool.false_eq_true, ↓reduceIte,
      bind_eq_result_bind, result_bind_ok]
    refine ⟨st, .Err .PolicyPinMismatch, rfl, ?_, ?_, fun _ _ => rfl⟩
    · simp [hp]
    · intro h; cases h

/-! ## 2. Canonical 128-Byte `TransactionIntent` Codec Roundtrip & Injectivity -/

private theorem byte8_and_allOnes (x : BitVec 8) : x &&& BitVec.allOnes 8 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and]
  have hm : (BitVec.allOnes 8).getLsbD i = true := by
    match i, hi with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl
    | n + 8, hi => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 8 n) hi)
  rw [hm, Bool.and_true]

private def intentByte16 (v : Std.U16) (shift : Nat) : Std.U8 :=
  UScalar.cast .U8 ((⟨v.bv >>> shift⟩ : Std.U16) &&& 255#u16)

private theorem be_u16_read_roundtrip (v : Std.U16) :
    policy_and_addr.be_u16_read (intentByte16 v 8) (intentByte16 v 0) = .ok v := by
  change Result.ok (⟨((UScalar.cast .U16 (intentByte16 v 8)).bv <<< 8) |||
    (UScalar.cast .U16 (intentByte16 v 0)).bv⟩ : Std.U16) = .ok v
  apply congrArg Result.ok
  apply UScalar.ext
  simp only [intentByte16, UScalar.cast, UScalar.bv_and, BitVec.setWidth_and]
  change (((v.bv >>> 8).setWidth 8 &&& BitVec.allOnes 8).setWidth 16 <<< 8) |||
    (((v.bv >>> 0).setWidth 8 &&& BitVec.allOnes 8).setWidth 16) = v.bv
  simp only [byte8_and_allOnes]
  have hcat : (v.bv >>> 8).setWidth 8 ++ (v.bv >>> 0).setWidth 8 = v.bv := by
    simp only [BitVec.setWidth_ushiftRight_eq_extractLsb]
    rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
    simp
  calc
    _ = ((v.bv >>> 8).setWidth 8 ++ (v.bv >>> 0).setWidth 8).setWidth 16 := by
      rw [BitVec.setWidth_append_eq_shiftLeft_setWidth_or]
    _ = v.bv := by rw [hcat]; rfl

private theorem be_u32_read_roundtrip (v : Std.U32) :
    policy_and_addr.be_u32_read
      (adrsByte32 v 24) (adrsByte32 v 16) (adrsByte32 v 8) (adrsByte32 v 0) = .ok v := by
  change Result.ok (⟨((UScalar.cast .U32 (adrsByte32 v 24)).bv <<< 24) |||
    ((UScalar.cast .U32 (adrsByte32 v 16)).bv <<< 16) |||
    ((UScalar.cast .U32 (adrsByte32 v 8)).bv <<< 8) |||
    (UScalar.cast .U32 (adrsByte32 v 0)).bv⟩ : Std.U32) = .ok v
  apply congrArg Result.ok
  apply UScalar.ext
  simp only [adrsByte32, UScalar.cast, UScalar.bv_and, BitVec.setWidth_and]
  change (((v.bv >>> 24).setWidth 8 &&& BitVec.allOnes 8).setWidth 32 <<< 24) |||
    (((v.bv >>> 16).setWidth 8 &&& BitVec.allOnes 8).setWidth 32 <<< 16) |||
    (((v.bv >>> 8).setWidth 8 &&& BitVec.allOnes 8).setWidth 32 <<< 8) |||
    (((v.bv >>> 0).setWidth 8 &&& BitVec.allOnes 8).setWidth 32) = v.bv
  simp only [byte8_and_allOnes]
  have hcat :
      (v.bv >>> 24).setWidth 8 ++ (v.bv >>> 16).setWidth 8 ++
      (v.bv >>> 8).setWidth 8 ++ (v.bv >>> 0).setWidth 8 = v.bv := by
    simp only [BitVec.setWidth_ushiftRight_eq_extractLsb]
    rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
    rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
    rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
    simp
  calc
    _ = ((v.bv >>> 24).setWidth 8 ++ (v.bv >>> 16).setWidth 8 ++
         (v.bv >>> 8).setWidth 8 ++ (v.bv >>> 0).setWidth 8).setWidth 32 := by
      rw [BitVec.setWidth_append_eq_shiftLeft_setWidth_or
        (b := (v.bv >>> 24).setWidth 8 ++ (v.bv >>> 16).setWidth 8 ++ (v.bv >>> 8).setWidth 8)
        (b' := (v.bv >>> 0).setWidth 8)]
      rw [BitVec.setWidth_append_eq_shiftLeft_setWidth_or
        (b := (v.bv >>> 24).setWidth 8 ++ (v.bv >>> 16).setWidth 8)
        (b' := (v.bv >>> 8).setWidth 8)]
      rw [BitVec.setWidth_append_eq_shiftLeft_setWidth_or
        (b := (v.bv >>> 24).setWidth 8) (b' := (v.bv >>> 16).setWidth 8)]
      simp only [BitVec.shiftLeft_or_distrib, ← BitVec.shiftLeft_add, Nat.reduceAdd]
    _ = v.bv := by rw [hcat]; rfl

set_option maxHeartbeats 400000 in
private theorem be_u64_read_roundtrip (v : Std.U64) :
    policy_and_addr.be_u64_read
      (adrsByte64 v 56) (adrsByte64 v 48) (adrsByte64 v 40) (adrsByte64 v 32)
      (adrsByte64 v 24) (adrsByte64 v 16) (adrsByte64 v 8) (adrsByte64 v 0) = .ok v := by
  change Result.ok (⟨((UScalar.cast .U64 (adrsByte64 v 56)).bv <<< 56) |||
    ((UScalar.cast .U64 (adrsByte64 v 48)).bv <<< 48) |||
    ((UScalar.cast .U64 (adrsByte64 v 40)).bv <<< 40) |||
    ((UScalar.cast .U64 (adrsByte64 v 32)).bv <<< 32) |||
    ((UScalar.cast .U64 (adrsByte64 v 24)).bv <<< 24) |||
    ((UScalar.cast .U64 (adrsByte64 v 16)).bv <<< 16) |||
    ((UScalar.cast .U64 (adrsByte64 v 8)).bv <<< 8) |||
    (UScalar.cast .U64 (adrsByte64 v 0)).bv⟩ : Std.U64) = .ok v
  apply congrArg Result.ok
  apply UScalar.ext
  simp only [adrsByte64, UScalar.cast, UScalar.bv_and, BitVec.setWidth_and]
  change (((v.bv >>> 56).setWidth 8 &&& BitVec.allOnes 8).setWidth 64 <<< 56) |||
    (((v.bv >>> 48).setWidth 8 &&& BitVec.allOnes 8).setWidth 64 <<< 48) |||
    (((v.bv >>> 40).setWidth 8 &&& BitVec.allOnes 8).setWidth 64 <<< 40) |||
    (((v.bv >>> 32).setWidth 8 &&& BitVec.allOnes 8).setWidth 64 <<< 32) |||
    (((v.bv >>> 24).setWidth 8 &&& BitVec.allOnes 8).setWidth 64 <<< 24) |||
    (((v.bv >>> 16).setWidth 8 &&& BitVec.allOnes 8).setWidth 64 <<< 16) |||
    (((v.bv >>> 8).setWidth 8 &&& BitVec.allOnes 8).setWidth 64 <<< 8) |||
    (((v.bv >>> 0).setWidth 8 &&& BitVec.allOnes 8).setWidth 64) = v.bv
  simp only [byte8_and_allOnes]
  have hcat :
      (v.bv >>> 56).setWidth 8 ++ (v.bv >>> 48).setWidth 8 ++
      (v.bv >>> 40).setWidth 8 ++ (v.bv >>> 32).setWidth 8 ++
      (v.bv >>> 24).setWidth 8 ++ (v.bv >>> 16).setWidth 8 ++
      (v.bv >>> 8).setWidth 8 ++ (v.bv >>> 0).setWidth 8 = v.bv := by
    simp only [BitVec.setWidth_ushiftRight_eq_extractLsb]
    rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
    rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
    rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
    rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
    rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
    rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
    rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
    simp
  calc
    _ = ((v.bv >>> 56).setWidth 8 ++ (v.bv >>> 48).setWidth 8 ++
         (v.bv >>> 40).setWidth 8 ++ (v.bv >>> 32).setWidth 8 ++
         (v.bv >>> 24).setWidth 8 ++ (v.bv >>> 16).setWidth 8 ++
         (v.bv >>> 8).setWidth 8 ++ (v.bv >>> 0).setWidth 8).setWidth 64 := by
      rw [BitVec.setWidth_append_eq_shiftLeft_setWidth_or
        (b := (v.bv >>> 56).setWidth 8 ++ (v.bv >>> 48).setWidth 8 ++
              (v.bv >>> 40).setWidth 8 ++ (v.bv >>> 32).setWidth 8 ++
              (v.bv >>> 24).setWidth 8 ++ (v.bv >>> 16).setWidth 8 ++ (v.bv >>> 8).setWidth 8)
        (b' := (v.bv >>> 0).setWidth 8)]
      rw [BitVec.setWidth_append_eq_shiftLeft_setWidth_or
        (b := (v.bv >>> 56).setWidth 8 ++ (v.bv >>> 48).setWidth 8 ++
              (v.bv >>> 40).setWidth 8 ++ (v.bv >>> 32).setWidth 8 ++
              (v.bv >>> 24).setWidth 8 ++ (v.bv >>> 16).setWidth 8)
        (b' := (v.bv >>> 8).setWidth 8)]
      rw [BitVec.setWidth_append_eq_shiftLeft_setWidth_or
        (b := (v.bv >>> 56).setWidth 8 ++ (v.bv >>> 48).setWidth 8 ++
              (v.bv >>> 40).setWidth 8 ++ (v.bv >>> 32).setWidth 8 ++ (v.bv >>> 24).setWidth 8)
        (b' := (v.bv >>> 16).setWidth 8)]
      rw [BitVec.setWidth_append_eq_shiftLeft_setWidth_or
        (b := (v.bv >>> 56).setWidth 8 ++ (v.bv >>> 48).setWidth 8 ++
              (v.bv >>> 40).setWidth 8 ++ (v.bv >>> 32).setWidth 8)
        (b' := (v.bv >>> 24).setWidth 8)]
      rw [BitVec.setWidth_append_eq_shiftLeft_setWidth_or
        (b := (v.bv >>> 56).setWidth 8 ++ (v.bv >>> 48).setWidth 8 ++ (v.bv >>> 40).setWidth 8)
        (b' := (v.bv >>> 32).setWidth 8)]
      rw [BitVec.setWidth_append_eq_shiftLeft_setWidth_or
        (b := (v.bv >>> 56).setWidth 8 ++ (v.bv >>> 48).setWidth 8)
        (b' := (v.bv >>> 40).setWidth 8)]
      rw [BitVec.setWidth_append_eq_shiftLeft_setWidth_or
        (b := (v.bv >>> 56).setWidth 8) (b' := (v.bv >>> 48).setWidth 8)]
      simp only [BitVec.shiftLeft_or_distrib, ← BitVec.shiftLeft_add, Nat.reduceAdd]
    _ = v.bv := by rw [hcat]; rfl

private def read16 (b0 b1 : Std.U8) : Std.U16 :=
  ⟨((UScalar.cast .U16 b0).bv <<< 8) ||| (UScalar.cast .U16 b1).bv⟩

private theorem read16_eq (b0 b1 : Std.U8) :
    policy_and_addr.be_u16_read b0 b1 = .ok (read16 b0 b1) := rfl

private theorem read16_byte0 (b0 b1 : Std.U8) :
    intentByte16 (read16 b0 b1) 8 = b0 := by
  apply UScalar.ext; apply BitVec.eq_of_getLsbD_eq; intro j hj; change j < 8 at hj
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp [intentByte16, read16, UScalar.cast, UScalar.bv_and,
      BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  | j + 8, hj => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 8 j) hj)

private theorem read16_byte1 (b0 b1 : Std.U8) :
    intentByte16 (read16 b0 b1) 0 = b1 := by
  apply UScalar.ext; apply BitVec.eq_of_getLsbD_eq; intro j hj; change j < 8 at hj
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp [intentByte16, read16, UScalar.cast, UScalar.bv_and, BitVec.getLsbD_and]
  | j + 8, hj => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 8 j) hj)

private def read32p (b0 b1 b2 b3 : Std.U8) : Std.U32 :=
  ⟨((UScalar.cast .U32 b0).bv <<< 24) ||| ((UScalar.cast .U32 b1).bv <<< 16) |||
   ((UScalar.cast .U32 b2).bv <<< 8) ||| (UScalar.cast .U32 b3).bv⟩

private theorem read32p_eq (b0 b1 b2 b3 : Std.U8) :
    policy_and_addr.be_u32_read b0 b1 b2 b3 = .ok (read32p b0 b1 b2 b3) := rfl

private theorem read32p_byte0 (b0 b1 b2 b3 : Std.U8) :
    adrsByte32 (read32p b0 b1 b2 b3) 24 = b0 := by
  apply UScalar.ext; apply BitVec.eq_of_getLsbD_eq; intro j hj; change j < 8 at hj
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp [adrsByte32, read32p, UScalar.cast, UScalar.bv_and,
      BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  | j + 8, hj => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 8 j) hj)

private theorem read32p_byte1 (b0 b1 b2 b3 : Std.U8) :
    adrsByte32 (read32p b0 b1 b2 b3) 16 = b1 := by
  apply UScalar.ext; apply BitVec.eq_of_getLsbD_eq; intro j hj; change j < 8 at hj
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp [adrsByte32, read32p, UScalar.cast, UScalar.bv_and,
      BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  | j + 8, hj => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 8 j) hj)

private theorem read32p_byte2 (b0 b1 b2 b3 : Std.U8) :
    adrsByte32 (read32p b0 b1 b2 b3) 8 = b2 := by
  apply UScalar.ext; apply BitVec.eq_of_getLsbD_eq; intro j hj; change j < 8 at hj
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp [adrsByte32, read32p, UScalar.cast, UScalar.bv_and,
      BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  | j + 8, hj => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 8 j) hj)

private theorem read32p_byte3 (b0 b1 b2 b3 : Std.U8) :
    adrsByte32 (read32p b0 b1 b2 b3) 0 = b3 := by
  apply UScalar.ext; apply BitVec.eq_of_getLsbD_eq; intro j hj; change j < 8 at hj
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp [adrsByte32, read32p, UScalar.cast, UScalar.bv_and, BitVec.getLsbD_and]
  | j + 8, hj => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 8 j) hj)

private def read64p (b0 b1 b2 b3 b4 b5 b6 b7 : Std.U8) : Std.U64 :=
  ⟨((UScalar.cast .U64 b0).bv <<< 56) ||| ((UScalar.cast .U64 b1).bv <<< 48) |||
   ((UScalar.cast .U64 b2).bv <<< 40) ||| ((UScalar.cast .U64 b3).bv <<< 32) |||
   ((UScalar.cast .U64 b4).bv <<< 24) ||| ((UScalar.cast .U64 b5).bv <<< 16) |||
   ((UScalar.cast .U64 b6).bv <<< 8) ||| (UScalar.cast .U64 b7).bv⟩

private theorem read64p_eq (b0 b1 b2 b3 b4 b5 b6 b7 : Std.U8) :
    policy_and_addr.be_u64_read b0 b1 b2 b3 b4 b5 b6 b7 =
      .ok (read64p b0 b1 b2 b3 b4 b5 b6 b7) := rfl

private theorem read64p_byte0 (b0 b1 b2 b3 b4 b5 b6 b7 : Std.U8) :
    adrsByte64 (read64p b0 b1 b2 b3 b4 b5 b6 b7) 56 = b0 := by
  apply UScalar.ext; apply BitVec.eq_of_getLsbD_eq; intro j hj; change j < 8 at hj
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp [adrsByte64, read64p, UScalar.cast, UScalar.bv_and,
      BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  | j + 8, hj => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 8 j) hj)

private theorem read64p_byte1 (b0 b1 b2 b3 b4 b5 b6 b7 : Std.U8) :
    adrsByte64 (read64p b0 b1 b2 b3 b4 b5 b6 b7) 48 = b1 := by
  apply UScalar.ext; apply BitVec.eq_of_getLsbD_eq; intro j hj; change j < 8 at hj
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp [adrsByte64, read64p, UScalar.cast, UScalar.bv_and,
      BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  | j + 8, hj => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 8 j) hj)

private theorem read64p_byte2 (b0 b1 b2 b3 b4 b5 b6 b7 : Std.U8) :
    adrsByte64 (read64p b0 b1 b2 b3 b4 b5 b6 b7) 40 = b2 := by
  apply UScalar.ext; apply BitVec.eq_of_getLsbD_eq; intro j hj; change j < 8 at hj
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp [adrsByte64, read64p, UScalar.cast, UScalar.bv_and,
      BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  | j + 8, hj => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 8 j) hj)

private theorem read64p_byte3 (b0 b1 b2 b3 b4 b5 b6 b7 : Std.U8) :
    adrsByte64 (read64p b0 b1 b2 b3 b4 b5 b6 b7) 32 = b3 := by
  apply UScalar.ext; apply BitVec.eq_of_getLsbD_eq; intro j hj; change j < 8 at hj
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp [adrsByte64, read64p, UScalar.cast, UScalar.bv_and,
      BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  | j + 8, hj => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 8 j) hj)

private theorem read64p_byte4 (b0 b1 b2 b3 b4 b5 b6 b7 : Std.U8) :
    adrsByte64 (read64p b0 b1 b2 b3 b4 b5 b6 b7) 24 = b4 := by
  apply UScalar.ext; apply BitVec.eq_of_getLsbD_eq; intro j hj; change j < 8 at hj
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp [adrsByte64, read64p, UScalar.cast, UScalar.bv_and,
      BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  | j + 8, hj => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 8 j) hj)

private theorem read64p_byte5 (b0 b1 b2 b3 b4 b5 b6 b7 : Std.U8) :
    adrsByte64 (read64p b0 b1 b2 b3 b4 b5 b6 b7) 16 = b5 := by
  apply UScalar.ext; apply BitVec.eq_of_getLsbD_eq; intro j hj; change j < 8 at hj
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp [adrsByte64, read64p, UScalar.cast, UScalar.bv_and,
      BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  | j + 8, hj => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 8 j) hj)

private theorem read64p_byte6 (b0 b1 b2 b3 b4 b5 b6 b7 : Std.U8) :
    adrsByte64 (read64p b0 b1 b2 b3 b4 b5 b6 b7) 8 = b6 := by
  apply UScalar.ext; apply BitVec.eq_of_getLsbD_eq; intro j hj; change j < 8 at hj
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp [adrsByte64, read64p, UScalar.cast, UScalar.bv_and,
      BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  | j + 8, hj => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 8 j) hj)

private theorem read64p_byte7 (b0 b1 b2 b3 b4 b5 b6 b7 : Std.U8) :
    adrsByte64 (read64p b0 b1 b2 b3 b4 b5 b6 b7) 0 = b7 := by
  apply UScalar.ext; apply BitVec.eq_of_getLsbD_eq; intro j hj; change j < 8 at hj
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp [adrsByte64, read64p, UScalar.cast, UScalar.bv_and, BitVec.getLsbD_and]
  | j + 8, hj => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 8 j) hj)

private def u128Hi (v : Std.U128) : Std.U64 :=
  UScalar.cast .U64 ((⟨v.bv >>> 64⟩ : Std.U128) &&& 18446744073709551615#u128)

private def u128Lo (v : Std.U128) : Std.U64 :=
  UScalar.cast .U64 (v &&& 18446744073709551615#u128)

private def packU128 (hi lo : Std.U64) : Std.U128 :=
  ⟨((UScalar.cast .U128 hi).bv <<< 64) ||| (UScalar.cast .U128 lo).bv⟩

private theorem unpack_u128_hi_eq (v : Std.U128) :
    policy_and_addr.unpack_u128_hi v = .ok (u128Hi v) := rfl

private theorem unpack_u128_lo_eq (v : Std.U128) :
    policy_and_addr.unpack_u128_lo v = .ok (u128Lo v) := rfl

private theorem pack_u128_eq (hi lo : Std.U64) :
    policy_and_addr.pack_u128_from_u64_be hi lo = .ok (packU128 hi lo) := rfl

private theorem u64_and_mask_bv (x : Std.U128) :
    (UScalar.cast .U64 (x &&& 18446744073709551615#u128)).bv = x.bv.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  have hlt : (x &&& 18446744073709551615#u128).val < 2 ^ 64 := by
    rw [u128_and_mask64_val]
    exact Nat.mod_lt _ (by decide)
  have hval := u128_cast_u64_val_of_lt _ hlt
  rw [u128_and_mask64_val] at hval
  exact hval.trans (BitVec.toNat_setWidth 64 x.bv).symm

private theorem pack_u128_roundtrip (v : Std.U128) :
    policy_and_addr.pack_u128_from_u64_be (u128Hi v) (u128Lo v) = .ok v := by
  rw [pack_u128_eq]
  apply congrArg Result.ok
  apply UScalar.ext
  have hhi : (u128Hi v).bv = (v.bv >>> 64).setWidth 64 := u64_and_mask_bv ⟨v.bv >>> 64⟩
  have hlo : (u128Lo v).bv = (v.bv >>> 0).setWidth 64 := by
    rw [u128Lo, u64_and_mask_bv, BitVec.ushiftRight_zero]
  change ((u128Hi v).bv.setWidth 128 <<< 64) ||| (u128Lo v).bv.setWidth 128 = v.bv
  rw [hhi, hlo]
  have hcat : (v.bv >>> 64).setWidth 64 ++ (v.bv >>> 0).setWidth 64 = v.bv := by
    simp only [BitVec.setWidth_ushiftRight_eq_extractLsb]
    rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
    simp
  calc
    _ = ((v.bv >>> 64).setWidth 64 ++ (v.bv >>> 0).setWidth 64).setWidth 128 := by
      rw [BitVec.setWidth_append_eq_shiftLeft_setWidth_or]
    _ = v.bv := by rw [hcat]; rfl

private theorem u128Hi_pack (hi lo : Std.U64) :
    u128Hi (packU128 hi lo) = hi := by
  apply UScalar.ext
  rw [u128Hi, u64_and_mask_bv]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change j < 64 at hj
  have hlt128 : 64 + j < 128 := Nat.add_lt_add_left hj 64
  have hnlt64 : ¬ (64 + j < 64) := Nat.not_lt_of_ge (Nat.le_add_right 64 j)
  have hsub : 64 + j - 64 = j := Nat.add_sub_cancel_left 64 j
  have hj128 : j < 128 := Nat.lt_trans hj (by decide)
  simp [packU128, UScalar.cast, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, hj, hlt128, hnlt64, hsub, hj128]

private theorem u128Lo_pack (hi lo : Std.U64) :
    u128Lo (packU128 hi lo) = lo := by
  apply UScalar.ext
  rw [u128Lo, u64_and_mask_bv]
  apply BitVec.eq_of_getLsbD_eq
  intro j _
  simp [packU128, UScalar.cast]

private def intentSuiteWord : policy_and_addr.IntentSuiteTag → Std.U16
  | .JortsPoseidon2 => 257#u16
  | .SlhDsaShake128f => 513#u16
  | .ThresholdMlDsa65 => 770#u16
  | .HybridEd25519MlDsa65 => 1281#u16
  | .HybridSecp256k1SlhDsa => 1282#u16

private theorem intentSuite_encode (t : policy_and_addr.IntentSuiteTag) :
    policy_and_addr.IntentSuiteTag.to_u16 t = .ok (intentSuiteWord t) := by
  unfold policy_and_addr.IntentSuiteTag.to_u16
    policy_and_addr.SUITE_HYBRID_ED25519_MLDSA65
    policy_and_addr.SUITE_HYBRID_SECP256K1_SLHDSA
  cases t <;> rfl

private theorem intentSuite_decode (t : policy_and_addr.IntentSuiteTag) :
    policy_and_addr.IntentSuiteTag.from_u16 (intentSuiteWord t) = .ok (some t) := by
  cases t <;> rfl

private theorem intentSuite_converse (raw : Std.U16) (t : policy_and_addr.IntentSuiteTag)
    (h : policy_and_addr.IntentSuiteTag.from_u16 raw = .ok (some t)) :
    intentSuiteWord t = raw := by
  unfold policy_and_addr.IntentSuiteTag.from_u16 at h
  split at h <;> cases h <;> rfl

private def intentAddrVerByte : policy_and_addr.IntentAddressVersion → Std.U8
  | .V1 => 1#u8
  | .V2 => 2#u8

private theorem intentAddrVer_encode (v : policy_and_addr.IntentAddressVersion) :
    policy_and_addr.IntentAddressVersion.to_u8 v = .ok (intentAddrVerByte v) := by
  cases v <;> rfl

private theorem intentAddrVer_decode (v : policy_and_addr.IntentAddressVersion) :
    policy_and_addr.IntentAddressVersion.from_u8 (intentAddrVerByte v) = .ok (some v) := by
  cases v <;> rfl

private theorem intentAddrVer_converse (raw : Std.U8) (v : policy_and_addr.IntentAddressVersion)
    (h : policy_and_addr.IntentAddressVersion.from_u8 raw = .ok (some v)) :
    intentAddrVerByte v = raw := by
  unfold policy_and_addr.IntentAddressVersion.from_u8 at h
  split at h <;> cases h <;> rfl

private def intentIdKindByte : policy_and_addr.IntentIdentityKind → Std.U8
  | .SingleKey => 1#u8
  | .ThresholdCommittee => 2#u8
  | .PolicyBound => 3#u8

private theorem intentIdKind_encode (k : policy_and_addr.IntentIdentityKind) :
    policy_and_addr.IntentIdentityKind.to_u8 k = .ok (intentIdKindByte k) := by
  cases k <;> rfl

private theorem intentIdKind_decode (k : policy_and_addr.IntentIdentityKind) :
    policy_and_addr.IntentIdentityKind.from_u8 (intentIdKindByte k) = .ok (some k) := by
  cases k <;> rfl

private theorem intentIdKind_converse (raw : Std.U8) (k : policy_and_addr.IntentIdentityKind)
    (h : policy_and_addr.IntentIdentityKind.from_u8 raw = .ok (some k)) :
    intentIdKindByte k = raw := by
  unfold policy_and_addr.IntentIdentityKind.from_u8 at h
  split at h <;> cases h <;> rfl

private def intentHeader32Bytes (hdr : policy_and_addr.IntentHeaderFields) :
    Std.Array Std.U8 32#usize :=
  Std.Array.make 32#usize [
    adrsByte32 1364412721#u32 24, adrsByte32 1364412721#u32 16,
    adrsByte32 1364412721#u32 8, adrsByte32 1364412721#u32 0,
    intentByte16 (intentSuiteWord hdr.suite_tag) 8,
    intentByte16 (intentSuiteWord hdr.suite_tag) 0,
    intentAddrVerByte hdr.address_version,
    intentIdKindByte hdr.identity_kind,
    adrsByte64 hdr.chain_id 56, adrsByte64 hdr.chain_id 48,
    adrsByte64 hdr.chain_id 40, adrsByte64 hdr.chain_id 32,
    adrsByte64 hdr.chain_id 24, adrsByte64 hdr.chain_id 16,
    adrsByte64 hdr.chain_id 8, adrsByte64 hdr.chain_id 0,
    adrsByte64 hdr.nonce 56, adrsByte64 hdr.nonce 48,
    adrsByte64 hdr.nonce 40, adrsByte64 hdr.nonce 32,
    adrsByte64 hdr.nonce 24, adrsByte64 hdr.nonce 16,
    adrsByte64 hdr.nonce 8, adrsByte64 hdr.nonce 0,
    adrsByte64 hdr.timestamp_secs 56, adrsByte64 hdr.timestamp_secs 48,
    adrsByte64 hdr.timestamp_secs 40, adrsByte64 hdr.timestamp_secs 32,
    adrsByte64 hdr.timestamp_secs 24, adrsByte64 hdr.timestamp_secs 16,
    adrsByte64 hdr.timestamp_secs 8, adrsByte64 hdr.timestamp_secs 0]

private def intentToHeader (intent : policy_and_addr.CanonicalIntent128) :
    policy_and_addr.IntentHeaderFields :=
  { suite_tag := intent.suite_tag
    address_version := intent.address_version
    identity_kind := intent.identity_kind
    chain_id := intent.chain_id
    nonce := intent.nonce
    timestamp_secs := intent.timestamp_secs }

private theorem encode_intent_header32_eq (intent : policy_and_addr.CanonicalIntent128) :
    policy_and_addr.encode_intent_header32 intent =
      .ok (intentHeader32Bytes (intentToHeader intent)) := by
  unfold policy_and_addr.encode_intent_header32 policy_and_addr.INTENT_V1_MAGIC
  rw [intentSuite_encode, intentAddrVer_encode, intentIdKind_encode]
  rfl

private theorem decode_intent_header32_roundtrip
    (hdr : policy_and_addr.IntentHeaderFields) :
    policy_and_addr.decode_intent_header32 (intentHeader32Bytes hdr) = .ok (some hdr) := by
  unfold policy_and_addr.decode_intent_header32 policy_and_addr.INTENT_V1_MAGIC
  simp [intentHeader32Bytes, Std.Array.make, Std.Array.index_usize,
    be_u16_read_roundtrip, be_u32_read_roundtrip, be_u64_read_roundtrip,
    intentSuite_decode, intentAddrVer_decode, intentIdKind_decode]

private theorem decode_intent_header32_converse
    (b : Std.Array Std.U8 32#usize) (hdr : policy_and_addr.IntentHeaderFields)
    (h : policy_and_addr.decode_intent_header32 b = .ok (some hdr)) :
    intentHeader32Bytes hdr = b := by
  have index (i : Std.Usize) (hi : i.val < 32) :
      Std.Array.index_usize b i = .ok (b.val.getD i.val 0#u8) :=
    array_index_getD b i 0#u8 hi
  unfold policy_and_addr.decode_intent_header32 policy_and_addr.INTENT_V1_MAGIC at h
  simp (disch := decide) only [index, bind_eq_result_bind, result_bind_ok,
    read16_eq, read32p_eq, read64p_eq] at h
  simp only [UScalar.val, UScalarTy.numBits, BitVec.toNat_ofNat,
    Nat.reducePow, Nat.reduceMod] at h
  let magic := read32p (b.val.getD 0 0#u8) (b.val.getD 1 0#u8)
    (b.val.getD 2 0#u8) (b.val.getD 3 0#u8)
  by_cases hmag : magic = 1364412721#u32
  · simp only [show read32p (b.val.getD 0 0#u8) (b.val.getD 1 0#u8)
      (b.val.getD 2 0#u8) (b.val.getD 3 0#u8) = magic from rfl,
      hmag, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
    let st_raw := read16 (b.val.getD 4 0#u8) (b.val.getD 5 0#u8)
    rw [show read16 (b.val.getD 4 0#u8) (b.val.getD 5 0#u8) = st_raw from rfl] at h
    cases hst : policy_and_addr.IntentSuiteTag.from_u16 st_raw with
    | fail _ => rw [hst] at h; cases h
    | div => rw [hst] at h; cases h
    | ok ost =>
      rw [hst, result_bind_ok] at h
      cases ost with
      | none => cases h
      | some t =>
        change (Result.bind (policy_and_addr.IntentAddressVersion.from_u8 (b.val.getD 6 0#u8)) _) =
          .ok (some hdr) at h
        cases hav : policy_and_addr.IntentAddressVersion.from_u8 (b.val.getD 6 0#u8) with
        | fail _ => rw [hav] at h; cases h
        | div => rw [hav] at h; cases h
        | ok oav =>
          rw [hav, result_bind_ok] at h
          cases oav with
          | none => cases h
          | some v =>
            change (Result.bind (policy_and_addr.IntentIdentityKind.from_u8 (b.val.getD 7 0#u8)) _) =
              .ok (some hdr) at h
            cases hik : policy_and_addr.IntentIdentityKind.from_u8 (b.val.getD 7 0#u8) with
            | fail _ => rw [hik] at h; cases h
            | div => rw [hik] at h; cases h
            | ok oik =>
              rw [hik, result_bind_ok] at h
              cases oik with
              | none => cases h
              | some k =>
                injection h with hsome
                injection hsome with hhdr
                subst hhdr
                have hst_eq := intentSuite_converse st_raw t hst
                have hav_eq := intentAddrVer_converse _ v hav
                have hik_eq := intentIdKind_converse _ k hik
                apply Std.Array.ext
                apply List.ext_getElem
                  (by simp only [intentHeader32Bytes, Std.Array.make,
                        List.length_cons, List.length_nil]
                      exact b.property.symm)
                intro i hi hj
                rw [List.getElem_eq_getD 0#u8, List.getElem_eq_getD 0#u8]
                have bound : i < 32 := by rw [b.property] at hj; exact hj
                simp only [intentHeader32Bytes, ← hmag, hst_eq, hav_eq, hik_eq]
                dsimp only [magic, st_raw]
                match i, bound with
                | 0, _ => exact read32p_byte0 _ _ _ _
                | 1, _ => exact read32p_byte1 _ _ _ _
                | 2, _ => exact read32p_byte2 _ _ _ _
                | 3, _ => exact read32p_byte3 _ _ _ _
                | 4, _ => exact read16_byte0 _ _
                | 5, _ => exact read16_byte1 _ _
                | 6, _ => rfl
                | 7, _ => rfl
                | 8, _ => exact read64p_byte0 _ _ _ _ _ _ _ _
                | 9, _ => exact read64p_byte1 _ _ _ _ _ _ _ _
                | 10, _ => exact read64p_byte2 _ _ _ _ _ _ _ _
                | 11, _ => exact read64p_byte3 _ _ _ _ _ _ _ _
                | 12, _ => exact read64p_byte4 _ _ _ _ _ _ _ _
                | 13, _ => exact read64p_byte5 _ _ _ _ _ _ _ _
                | 14, _ => exact read64p_byte6 _ _ _ _ _ _ _ _
                | 15, _ => exact read64p_byte7 _ _ _ _ _ _ _ _
                | 16, _ => exact read64p_byte0 _ _ _ _ _ _ _ _
                | 17, _ => exact read64p_byte1 _ _ _ _ _ _ _ _
                | 18, _ => exact read64p_byte2 _ _ _ _ _ _ _ _
                | 19, _ => exact read64p_byte3 _ _ _ _ _ _ _ _
                | 20, _ => exact read64p_byte4 _ _ _ _ _ _ _ _
                | 21, _ => exact read64p_byte5 _ _ _ _ _ _ _ _
                | 22, _ => exact read64p_byte6 _ _ _ _ _ _ _ _
                | 23, _ => exact read64p_byte7 _ _ _ _ _ _ _ _
                | 24, _ => exact read64p_byte0 _ _ _ _ _ _ _ _
                | 25, _ => exact read64p_byte1 _ _ _ _ _ _ _ _
                | 26, _ => exact read64p_byte2 _ _ _ _ _ _ _ _
                | 27, _ => exact read64p_byte3 _ _ _ _ _ _ _ _
                | 28, _ => exact read64p_byte4 _ _ _ _ _ _ _ _
                | 29, _ => exact read64p_byte5 _ _ _ _ _ _ _ _
                | 30, _ => exact read64p_byte6 _ _ _ _ _ _ _ _
                | 31, _ => exact read64p_byte7 _ _ _ _ _ _ _ _
                | i + 32, hi => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 32 i) hi)
  · have hne : (magic != 1364412721#u32) = true := bne_iff_ne.mpr hmag
    simp only [show read32p (b.val.getD 0 0#u8) (b.val.getD 1 0#u8)
      (b.val.getD 2 0#u8) (b.val.getD 3 0#u8) = magic from rfl,
      hne, ↓reduceIte, Result.ok.injEq] at h
    cases h

private def intentAmounts32Bytes (amount spent : Std.U128) : Std.Array Std.U8 32#usize :=
  Std.Array.make 32#usize [
    adrsByte64 (u128Hi amount) 56, adrsByte64 (u128Hi amount) 48,
    adrsByte64 (u128Hi amount) 40, adrsByte64 (u128Hi amount) 32,
    adrsByte64 (u128Hi amount) 24, adrsByte64 (u128Hi amount) 16,
    adrsByte64 (u128Hi amount) 8, adrsByte64 (u128Hi amount) 0,
    adrsByte64 (u128Lo amount) 56, adrsByte64 (u128Lo amount) 48,
    adrsByte64 (u128Lo amount) 40, adrsByte64 (u128Lo amount) 32,
    adrsByte64 (u128Lo amount) 24, adrsByte64 (u128Lo amount) 16,
    adrsByte64 (u128Lo amount) 8, adrsByte64 (u128Lo amount) 0,
    adrsByte64 (u128Hi spent) 56, adrsByte64 (u128Hi spent) 48,
    adrsByte64 (u128Hi spent) 40, adrsByte64 (u128Hi spent) 32,
    adrsByte64 (u128Hi spent) 24, adrsByte64 (u128Hi spent) 16,
    adrsByte64 (u128Hi spent) 8, adrsByte64 (u128Hi spent) 0,
    adrsByte64 (u128Lo spent) 56, adrsByte64 (u128Lo spent) 48,
    adrsByte64 (u128Lo spent) 40, adrsByte64 (u128Lo spent) 32,
    adrsByte64 (u128Lo spent) 24, adrsByte64 (u128Lo spent) 16,
    adrsByte64 (u128Lo spent) 8, adrsByte64 (u128Lo spent) 0]

private theorem encode_intent_amounts32_eq (amount spent : Std.U128) :
    policy_and_addr.encode_intent_amounts32 amount spent =
      .ok (intentAmounts32Bytes amount spent) := rfl

private theorem decode_intent_amounts32_roundtrip (amount spent : Std.U128) :
    policy_and_addr.decode_intent_amounts32 (intentAmounts32Bytes amount spent) =
      .ok (amount, spent) := by
  unfold policy_and_addr.decode_intent_amounts32
  simp [intentAmounts32Bytes, Std.Array.make, Std.Array.index_usize,
    be_u64_read_roundtrip, pack_u128_roundtrip]

private theorem decode_intent_amounts32_converse
    (b : Std.Array Std.U8 32#usize) (amount spent : Std.U128)
    (h : policy_and_addr.decode_intent_amounts32 b = .ok (amount, spent)) :
    intentAmounts32Bytes amount spent = b := by
  have index (i : Std.Usize) (hi : i.val < 32) :
      Std.Array.index_usize b i = .ok (b.val.getD i.val 0#u8) :=
    array_index_getD b i 0#u8 hi
  unfold policy_and_addr.decode_intent_amounts32 at h
  simp (disch := decide) only [index, bind_eq_result_bind, result_bind_ok,
    read64p_eq, pack_u128_eq, Result.ok.injEq, Prod.mk.injEq] at h
  simp only [UScalar.val, UScalarTy.numBits, BitVec.toNat_ofNat,
    Nat.reducePow, Nat.reduceMod] at h
  rcases h with ⟨rfl, rfl⟩
  apply Std.Array.ext
  apply List.ext_getElem
    (by simp only [intentAmounts32Bytes, Std.Array.make,
          List.length_cons, List.length_nil]
        exact b.property.symm)
  intro i hi hj
  rw [List.getElem_eq_getD 0#u8, List.getElem_eq_getD 0#u8]
  have bound : i < 32 := by rw [b.property] at hj; exact hj
  simp only [intentAmounts32Bytes, u128Hi_pack, u128Lo_pack]
  match i, bound with
  | 0, _ => exact read64p_byte0 _ _ _ _ _ _ _ _
  | 1, _ => exact read64p_byte1 _ _ _ _ _ _ _ _
  | 2, _ => exact read64p_byte2 _ _ _ _ _ _ _ _
  | 3, _ => exact read64p_byte3 _ _ _ _ _ _ _ _
  | 4, _ => exact read64p_byte4 _ _ _ _ _ _ _ _
  | 5, _ => exact read64p_byte5 _ _ _ _ _ _ _ _
  | 6, _ => exact read64p_byte6 _ _ _ _ _ _ _ _
  | 7, _ => exact read64p_byte7 _ _ _ _ _ _ _ _
  | 8, _ => exact read64p_byte0 _ _ _ _ _ _ _ _
  | 9, _ => exact read64p_byte1 _ _ _ _ _ _ _ _
  | 10, _ => exact read64p_byte2 _ _ _ _ _ _ _ _
  | 11, _ => exact read64p_byte3 _ _ _ _ _ _ _ _
  | 12, _ => exact read64p_byte4 _ _ _ _ _ _ _ _
  | 13, _ => exact read64p_byte5 _ _ _ _ _ _ _ _
  | 14, _ => exact read64p_byte6 _ _ _ _ _ _ _ _
  | 15, _ => exact read64p_byte7 _ _ _ _ _ _ _ _
  | 16, _ => exact read64p_byte0 _ _ _ _ _ _ _ _
  | 17, _ => exact read64p_byte1 _ _ _ _ _ _ _ _
  | 18, _ => exact read64p_byte2 _ _ _ _ _ _ _ _
  | 19, _ => exact read64p_byte3 _ _ _ _ _ _ _ _
  | 20, _ => exact read64p_byte4 _ _ _ _ _ _ _ _
  | 21, _ => exact read64p_byte5 _ _ _ _ _ _ _ _
  | 22, _ => exact read64p_byte6 _ _ _ _ _ _ _ _
  | 23, _ => exact read64p_byte7 _ _ _ _ _ _ _ _
  | 24, _ => exact read64p_byte0 _ _ _ _ _ _ _ _
  | 25, _ => exact read64p_byte1 _ _ _ _ _ _ _ _
  | 26, _ => exact read64p_byte2 _ _ _ _ _ _ _ _
  | 27, _ => exact read64p_byte3 _ _ _ _ _ _ _ _
  | 28, _ => exact read64p_byte4 _ _ _ _ _ _ _ _
  | 29, _ => exact read64p_byte5 _ _ _ _ _ _ _ _
  | 30, _ => exact read64p_byte6 _ _ _ _ _ _ _ _
  | 31, _ => exact read64p_byte7 _ _ _ _ _ _ _ _
  | i + 32, hi => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 32 i) hi)

private theorem range_map_getD_eq {n : Nat} (xs : List Std.U8) (hlen : xs.length = n) :
    (List.range n).map (fun k => xs.getD k 0#u8) = xs := by
  apply List.ext_getElem (by rw [List.length_map, List.length_range, hlen])
  intro i h1 h2
  rw [List.getElem_map, List.getElem_range, List.getElem_eq_getD 0#u8]

private def sliceBlock32 (buf : Std.Array Std.U8 128#usize) (base : Nat) :
    Std.Array Std.U8 32#usize :=
  ⟨(List.range 32).map (fun k => buf.val.getD (base + k) 0#u8), by
    rw [List.length_map, List.length_range]; rfl⟩

private def pack4x32Pure (b0 b1 b2 b3 : Std.Array Std.U8 32#usize) :
    Std.Array Std.U8 128#usize :=
  ⟨(List.range 32).map (fun k => b0.val.getD k 0#u8) ++
   (List.range 32).map (fun k => b1.val.getD k 0#u8) ++
   (List.range 32).map (fun k => b2.val.getD k 0#u8) ++
   (List.range 32).map (fun k => b3.val.getD k 0#u8), by
    simp [List.length_append, List.length_map, List.length_range]⟩

set_option maxHeartbeats 800000 in
private theorem pack_4x32_eq (b0 b1 b2 b3 : Std.Array Std.U8 32#usize) :
    policy_and_addr.pack_4x32 b0 b1 b2 b3 = .ok (pack4x32Pure b0 b1 b2 b3) := by
  have idx (xs : Std.Array Std.U8 32#usize) (i : Std.Usize) (hi : i.val < 32) :
      Std.Array.index_usize xs i = .ok (xs.val.getD i.val 0#u8) :=
    array_index_getD xs i 0#u8 hi
  unfold policy_and_addr.pack_4x32
  simp (disch := decide) only [idx, bind_eq_result_bind, result_bind_ok]
  apply congrArg Result.ok
  apply Std.Array.ext
  rfl

private theorem pack4x32Pure_val (b0 b1 b2 b3 : Std.Array Std.U8 32#usize) :
    (pack4x32Pure b0 b1 b2 b3).val = b0.val ++ b1.val ++ b2.val ++ b3.val := by
  dsimp only [pack4x32Pure]
  rw [range_map_getD_eq b0.val (show b0.val.length = 32 from b0.property),
      range_map_getD_eq b1.val (show b1.val.length = 32 from b1.property),
      range_map_getD_eq b2.val (show b2.val.length = 32 from b2.property),
      range_map_getD_eq b3.val (show b3.val.length = 32 from b3.property)]

private theorem usize_add_ok (base off : Std.Usize) (h : base.val + off.val < 2 ^ 64) :
    (base + off : Result Std.Usize) = .ok ⟨base.bv + off.bv⟩ := by
  simp only [hAdd_uscalar_eq, h, ↓reduceIte]

set_option maxHeartbeats 800000 in
private theorem unpack_block32_eq (buf : Std.Array Std.U8 128#usize)
    (base : Std.Usize) (hbase : base.val + 32 ≤ 128) :
    policy_and_addr.unpack_block32 buf base = .ok (sliceBlock32 buf base.val) := by
  have idx0 : Std.Array.index_usize buf base = .ok (buf.val.getD base.val 0#u8) :=
    array_index_getD buf base 0#u8
      (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide)) hbase)
  have hadd (off : Std.Usize) (hoff : off.val < 32) :
      (base + off : Result Std.Usize) = .ok ⟨base.bv + off.bv⟩ :=
    usize_add_ok base off
      (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hoff base.val)
        (Nat.le_trans hbase (by decide)))
  have idx_off (off : Std.Usize) (hoff : off.val < 32) :
      Std.Array.index_usize buf ⟨base.bv + off.bv⟩ =
        .ok (buf.val.getD (base.val + off.val) 0#u8) := by
    have hv : (⟨base.bv + off.bv⟩ : Std.Usize).val = base.val + off.val := by
      change (base.bv + off.bv).toNat = base.val + off.val
      rw [BitVec.toNat_add]
      exact Nat.mod_eq_of_lt
        (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hoff base.val)
          (Nat.le_trans hbase (by decide)))
    have hlt : (⟨base.bv + off.bv⟩ : Std.Usize).val < 128 := by
      rw [hv]
      exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hoff base.val) hbase
    rw [array_index_getD buf ⟨base.bv + off.bv⟩ 0#u8 hlt, hv]
  unfold policy_and_addr.unpack_block32
  simp (disch := decide) only [hadd, idx0, idx_off, bind_eq_result_bind, result_bind_ok]
  apply congrArg Result.ok
  apply Std.Array.ext
  dsimp only [sliceBlock32, Std.Array.make, List.range, List.range.loop, List.map]
  simp only [Nat.add_zero, UScalar.val, UScalarTy.numBits, BitVec.toNat_ofNat,
    Nat.reducePow, Nat.reduceMod]

private theorem sliceBlock32_getElem (buf : Std.Array Std.U8 128#usize) (base i : Nat)
    (hi : i < (sliceBlock32 buf base).val.length) :
    (sliceBlock32 buf base).val[i]'hi = buf.val.getD (base + i) 0#u8 := by
  unfold sliceBlock32 at hi ⊢
  dsimp only at hi ⊢
  rw [List.getElem_map, List.getElem_range]

private theorem sliceBlock32_pack_0 (b0 b1 b2 b3 : Std.Array Std.U8 32#usize) :
    sliceBlock32 (pack4x32Pure b0 b1 b2 b3) 0 = b0 := by
  apply Std.Array.ext
  apply List.ext_getElem (by rw [(sliceBlock32 _ 0).property, b0.property])
  intro i hi hj
  have hi32 : i < 32 := by rw [b0.property] at hj; exact hj
  have hl0 : b0.val.length = 32 := b0.property
  have hl1 : b1.val.length = 32 := b1.property
  have hl2 : b2.val.length = 32 := b2.property
  rw [sliceBlock32_getElem, Nat.zero_add, pack4x32Pure_val]
  have h1 : i < (b0.val ++ b1.val ++ b2.val).length := by
    rw [List.length_append, List.length_append, hl0, hl1, hl2]
    exact Nat.lt_trans hi32 (by decide)
  have h2 : i < (b0.val ++ b1.val).length := by
    rw [List.length_append, hl0, hl1]
    exact Nat.lt_trans hi32 (by decide)
  have hbound : i < (b0.val ++ b1.val ++ b2.val ++ b3.val).length := by
    rw [List.length_append]; exact Nat.lt_of_lt_of_le h1 (Nat.le_add_right _ _)
  rw [← List.getElem_eq_getD 0#u8 (h := hbound), List.getElem_append_left h1,
      List.getElem_append_left h2, List.getElem_append_left hj]

private theorem sliceBlock32_pack_32 (b0 b1 b2 b3 : Std.Array Std.U8 32#usize) :
    sliceBlock32 (pack4x32Pure b0 b1 b2 b3) 32 = b1 := by
  apply Std.Array.ext
  apply List.ext_getElem (by rw [(sliceBlock32 _ 32).property, b1.property])
  intro i hi hj
  have hi32 : i < 32 := by rw [b1.property] at hj; exact hj
  have hl0 : b0.val.length = 32 := b0.property
  have hl1 : b1.val.length = 32 := b1.property
  have hl2 : b2.val.length = 32 := b2.property
  rw [sliceBlock32_getElem, pack4x32Pure_val]
  have h1 : 32 + i < (b0.val ++ b1.val ++ b2.val).length := by
    rw [List.length_append, List.length_append, hl0, hl1, hl2]
    exact Nat.lt_trans (Nat.add_lt_add_left hi32 32) (by decide)
  have h2 : 32 + i < (b0.val ++ b1.val).length := by
    rw [List.length_append, hl0, hl1]
    exact Nat.add_lt_add_left hi32 32
  have hge0 : b0.val.length ≤ 32 + i := by rw [hl0]; exact Nat.le_add_right 32 i
  have hsub : 32 + i - b0.val.length = i := by rw [hl0]; exact Nat.add_sub_cancel_left 32 i
  have hbound : 32 + i < (b0.val ++ b1.val ++ b2.val ++ b3.val).length := by
    rw [List.length_append]; exact Nat.lt_of_lt_of_le h1 (Nat.le_add_right _ _)
  rw [← List.getElem_eq_getD 0#u8 (h := hbound),
      List.getElem_append_left h1, List.getElem_append_left h2,
      List.getElem_append_right hge0]
  simp only [hsub]

private theorem sliceBlock32_pack_64 (b0 b1 b2 b3 : Std.Array Std.U8 32#usize) :
    sliceBlock32 (pack4x32Pure b0 b1 b2 b3) 64 = b2 := by
  apply Std.Array.ext
  apply List.ext_getElem (by rw [(sliceBlock32 _ 64).property, b2.property])
  intro i hi hj
  have hi32 : i < 32 := by rw [b2.property] at hj; exact hj
  have hl0 : b0.val.length = 32 := b0.property
  have hl1 : b1.val.length = 32 := b1.property
  have hl2 : b2.val.length = 32 := b2.property
  rw [sliceBlock32_getElem, pack4x32Pure_val]
  have hlen01 : (b0.val ++ b1.val).length = 64 := by
    rw [List.length_append, hl0, hl1]
  have h1 : 64 + i < (b0.val ++ b1.val ++ b2.val).length := by
    rw [List.length_append, hlen01, hl2]
    exact Nat.add_lt_add_left hi32 64
  have hge01 : (b0.val ++ b1.val).length ≤ 64 + i := by
    rw [hlen01]; exact Nat.le_add_right 64 i
  have hsub : 64 + i - (b0.val ++ b1.val).length = i := by
    rw [hlen01]; exact Nat.add_sub_cancel_left 64 i
  have hbound : 64 + i < (b0.val ++ b1.val ++ b2.val ++ b3.val).length := by
    rw [List.length_append]; exact Nat.lt_of_lt_of_le h1 (Nat.le_add_right _ _)
  rw [← List.getElem_eq_getD 0#u8 (h := hbound),
      List.getElem_append_left h1, List.getElem_append_right hge01]
  simp only [hsub]

private theorem sliceBlock32_pack_96 (b0 b1 b2 b3 : Std.Array Std.U8 32#usize) :
    sliceBlock32 (pack4x32Pure b0 b1 b2 b3) 96 = b3 := by
  apply Std.Array.ext
  apply List.ext_getElem (by rw [(sliceBlock32 _ 96).property, b3.property])
  intro i hi hj
  have hi32 : i < 32 := by rw [b3.property] at hj; exact hj
  have hl0 : b0.val.length = 32 := b0.property
  have hl1 : b1.val.length = 32 := b1.property
  have hl2 : b2.val.length = 32 := b2.property
  have hl3 : b3.val.length = 32 := b3.property
  rw [sliceBlock32_getElem, pack4x32Pure_val]
  have hlen012 : (b0.val ++ b1.val ++ b2.val).length = 96 := by
    rw [List.length_append, List.length_append, hl0, hl1, hl2]
  have hbound : 96 + i < (b0.val ++ b1.val ++ b2.val ++ b3.val).length := by
    rw [List.length_append, hlen012, hl3]
    exact Nat.add_lt_add_left hi32 96
  have hge012 : (b0.val ++ b1.val ++ b2.val).length ≤ 96 + i := by
    rw [hlen012]; exact Nat.le_add_right 96 i
  have hsub : 96 + i - (b0.val ++ b1.val ++ b2.val).length = i := by
    rw [hlen012]; exact Nat.add_sub_cancel_left 96 i
  rw [← List.getElem_eq_getD 0#u8 (h := hbound), List.getElem_append_right hge012]
  simp only [hsub]

private theorem pack4x32_sliceBlocks_eq (buf : Std.Array Std.U8 128#usize) :
    pack4x32Pure
      (sliceBlock32 buf 0) (sliceBlock32 buf 32)
      (sliceBlock32 buf 64) (sliceBlock32 buf 96) = buf := by
  apply Std.Array.ext
  rw [pack4x32Pure_val]
  apply List.ext_getElem
  · simp [(sliceBlock32 buf 0).property, (sliceBlock32 buf 32).property,
      (sliceBlock32 buf 64).property, (sliceBlock32 buf 96).property, buf.property]
  intro i h1 h2
  have hi128 : i < 128 := by rw [buf.property] at h2; exact h2
  have hl0 : (sliceBlock32 buf 0).val.length = 32 := (sliceBlock32 buf 0).property
  have hl1 : (sliceBlock32 buf 32).val.length = 32 := (sliceBlock32 buf 32).property
  have hl2 : (sliceBlock32 buf 64).val.length = 32 := (sliceBlock32 buf 64).property
  have hl01 : ((sliceBlock32 buf 0).val ++ (sliceBlock32 buf 32).val).length = 64 := by
    rw [List.length_append, hl0, hl1]
  have hl012 :
      ((sliceBlock32 buf 0).val ++ (sliceBlock32 buf 32).val ++
       (sliceBlock32 buf 64).val).length = 96 := by
    rw [List.length_append, hl01, hl2]
  by_cases h96 : i < 96
  · have hlt012 :
        i < ((sliceBlock32 buf 0).val ++ (sliceBlock32 buf 32).val ++
             (sliceBlock32 buf 64).val).length := by rw [hl012]; exact h96
    rw [List.getElem_append_left hlt012]
    by_cases h64 : i < 64
    · have hlt01 : i < ((sliceBlock32 buf 0).val ++ (sliceBlock32 buf 32).val).length := by
        rw [hl01]; exact h64
      rw [List.getElem_append_left hlt01]
      by_cases h32 : i < 32
      · have hlt0 : i < (sliceBlock32 buf 0).val.length := by rw [hl0]; exact h32
        rw [List.getElem_append_left hlt0, sliceBlock32_getElem, Nat.zero_add,
            List.getElem_eq_getD 0#u8]
      · have hge0 : (sliceBlock32 buf 0).val.length ≤ i := by
          rw [hl0]; exact Nat.le_of_not_gt h32
        rw [List.getElem_append_right hge0, sliceBlock32_getElem, hl0,
            Nat.add_sub_of_le (Nat.le_of_not_gt h32), List.getElem_eq_getD 0#u8]
    · have hge01 : ((sliceBlock32 buf 0).val ++ (sliceBlock32 buf 32).val).length ≤ i := by
        rw [hl01]; exact Nat.le_of_not_gt h64
      rw [List.getElem_append_right hge01, sliceBlock32_getElem, hl01,
          Nat.add_sub_of_le (Nat.le_of_not_gt h64), List.getElem_eq_getD 0#u8]
  · have hge012 :
        ((sliceBlock32 buf 0).val ++ (sliceBlock32 buf 32).val ++
         (sliceBlock32 buf 64).val).length ≤ i := by
      rw [hl012]; exact Nat.le_of_not_gt h96
    rw [List.getElem_append_right hge012, sliceBlock32_getElem, hl012,
        Nat.add_sub_of_le (Nat.le_of_not_gt h96), List.getElem_eq_getD 0#u8]

private theorem encode_intent_128_roundtrip
    (intent : policy_and_addr.CanonicalIntent128) :
    ∃ bytes,
      policy_and_addr.encode_intent_128 intent = .ok bytes ∧
      policy_and_addr.decode_intent_128 bytes = .ok (some intent) := by
  let b0 := intentHeader32Bytes (intentToHeader intent)
  let b1 := intentAmounts32Bytes intent.amount_units intent.rolling_window_spent
  let bytes := pack4x32Pure b0 b1 intent.recipient_commitment intent.payload_digest
  refine ⟨bytes, ?_, ?_⟩
  · unfold policy_and_addr.encode_intent_128
    simp only [bind_eq_result_bind]
    rw [encode_intent_header32_eq, result_bind_ok,
        encode_intent_amounts32_eq, result_bind_ok, pack_4x32_eq]
  · unfold policy_and_addr.decode_intent_128
    simp only [bind_eq_result_bind]
    rw [unpack_block32_eq bytes 0#usize (by decide), result_bind_ok,
        unpack_block32_eq bytes 32#usize (by decide), result_bind_ok,
        unpack_block32_eq bytes 64#usize (by decide), result_bind_ok,
        unpack_block32_eq bytes 96#usize (by decide), result_bind_ok]
    have h0 : (0#usize).val = 0 := rfl
    have h32 : (32#usize).val = 32 := rfl
    have h64 : (64#usize).val = 64 := rfl
    have h96 : (96#usize).val = 96 := rfl
    rw [h0, h32, h64, h96,
        sliceBlock32_pack_0, sliceBlock32_pack_32, sliceBlock32_pack_64, sliceBlock32_pack_96,
        decode_intent_header32_roundtrip, result_bind_ok]
    dsimp only
    rw [decode_intent_amounts32_roundtrip, result_bind_ok]
    cases intent; rfl

private theorem decode_intent_128_converse
    (bytes : Std.Array Std.U8 128#usize)
    (intent : policy_and_addr.CanonicalIntent128)
    (h : policy_and_addr.decode_intent_128 bytes = .ok (some intent)) :
    policy_and_addr.encode_intent_128 intent = .ok bytes := by
  unfold policy_and_addr.decode_intent_128 at h
  simp only [bind_eq_result_bind] at h
  rw [unpack_block32_eq bytes 0#usize (by decide), result_bind_ok,
      unpack_block32_eq bytes 32#usize (by decide), result_bind_ok,
      unpack_block32_eq bytes 64#usize (by decide), result_bind_ok,
      unpack_block32_eq bytes 96#usize (by decide), result_bind_ok] at h
  have h0 : (0#usize).val = 0 := rfl
  have h32 : (32#usize).val = 32 := rfl
  have h64 : (64#usize).val = 64 := rfl
  have h96 : (96#usize).val = 96 := rfl
  rw [h0, h32, h64, h96] at h
  cases hhdr : policy_and_addr.decode_intent_header32 (sliceBlock32 bytes 0) with
  | fail _ => rw [hhdr] at h; cases h
  | div => rw [hhdr] at h; cases h
  | ok ohdr =>
    rw [hhdr, result_bind_ok] at h
    cases ohdr with
    | none => cases h
    | some hdr =>
      dsimp only at h
      cases hamt : policy_and_addr.decode_intent_amounts32 (sliceBlock32 bytes 32) with
      | fail _ => rw [hamt] at h; cases h
      | div => rw [hamt] at h; cases h
      | ok pair =>
        rcases pair with ⟨amt, spent⟩
        rw [hamt, result_bind_ok] at h
        simp only [Result.ok.injEq, Option.some.injEq] at h
        subst intent
        unfold policy_and_addr.encode_intent_128
        simp only [bind_eq_result_bind]
        rw [encode_intent_header32_eq, result_bind_ok,
            encode_intent_amounts32_eq, result_bind_ok, pack_4x32_eq]
        apply congrArg Result.ok
        have hhdr_eq : intentToHeader
            { suite_tag := hdr.suite_tag, address_version := hdr.address_version,
              identity_kind := hdr.identity_kind, chain_id := hdr.chain_id,
              nonce := hdr.nonce, timestamp_secs := hdr.timestamp_secs,
              amount_units := amt, rolling_window_spent := spent,
              recipient_commitment := sliceBlock32 bytes 64,
              payload_digest := sliceBlock32 bytes 96 } = hdr := by
          cases hdr; rfl
        rw [hhdr_eq,
            decode_intent_header32_converse _ hdr hhdr,
            decode_intent_amounts32_converse _ amt spent hamt]
        exact pack4x32_sliceBlocks_eq bytes

