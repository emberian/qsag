module
import all QsagVerified.Funs

public import QsagVerified.Proofs.Common
public import QsagVerified.Proofs.Adrs
public import QsagVerified.Proofs.MirRefinementKit
public import QsagVerified.Proofs.Sponge
import all QsagVerified.Proofs.SpongeFraming

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
3. **`intent_codec_roundtrip_injective_mir`, `intent_suite_tag_wire_words`,
   `intent_identity_kind_wire_bytes`, `intent_admits_identity_kind_spec`:**
   The suite and identity-kind tags carry the canonical `qsag-addr` wire words
   (`MlDsa65 = 0x0102`, `SlhDsa128f = 0x0202`, `JortsPoseidon2 = 0x0214`,
   `HybridSecp256k1MlDsa44 = 0x0501`, `HybridEd25519MlDsa65 = 0x0502`; kinds `1`, `2`, `3`).
   `encode_intent_128` is total and injective; `decode_intent_128` reads an encoded frame
   back exactly when the identity kind is the one the suite mandates
   (`intentSuiteExpectedKind`) and refuses it otherwise; and every decoded frame re-encodes
   to the same bytes and has a valid `(suite, kind)` pair (`P0-10`/`P1-01`).
4. **`check_hybrid_domain_framing_spec`, `hybrid_domain_framing_role_disjoint_mir`,
   `derive_hybrid_transcript_digest_total`:**
   Proves exact constant-time `"QSAG.HYBRID.V2"` framing semantics, disjointness between
   `Classical` and `PostQuantum` leg signatures, and total SHAKE256 transcript derivation.
5. **Concrete `#tooth` Refusal Witnesses:**
   `tooth_policy_cap_exceeded_rejected`, `tooth_policy_u128_overflow_rejected`,
   `tooth_intent_bad_magic_rejected`, `tooth_intent_retired_suite_words_rejected`,
   `tooth_intent_hybrid_suite_single_kind_rejected`, `tooth_hybrid_role_confusion_rejected`.
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
  | .MlDsa65 => 258#u16
  | .SlhDsa128f => 514#u16
  | .JortsPoseidon2 => 532#u16
  | .HybridSecp256k1MlDsa44 => 1281#u16
  | .HybridEd25519MlDsa65 => 1282#u16

private theorem intentSuite_encode (t : policy_and_addr.IntentSuiteTag) :
    policy_and_addr.IntentSuiteTag.to_u16 t = .ok (intentSuiteWord t) := by
  unfold policy_and_addr.IntentSuiteTag.to_u16
    policy_and_addr.SUITE_HYBRID_SECP256K1_MLDSA44
    policy_and_addr.SUITE_HYBRID_ED25519_MLDSA65
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
  | .SingleOrThreshold => 1#u8
  | .HybridConjunctive => 2#u8
  | .ScriptPredicate => 3#u8

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

/-- The suite tags of the verified intent namespace carry the canonical `qsag-addr`
`WitnessSuiteTag` wire words (`0x0102`, `0x0202`, `0x0214`, `0x0501`, `0x0502`), and
`from_u16` never fails and accepts a word exactly when it is the word of the tag it returns. -/
theorem intent_suite_tag_wire_words :
    policy_and_addr.IntentSuiteTag.to_u16 .MlDsa65 = .ok 258#u16 ∧
    policy_and_addr.IntentSuiteTag.to_u16 .SlhDsa128f = .ok 514#u16 ∧
    policy_and_addr.IntentSuiteTag.to_u16 .JortsPoseidon2 = .ok 532#u16 ∧
    policy_and_addr.IntentSuiteTag.to_u16 .HybridSecp256k1MlDsa44 = .ok 1281#u16 ∧
    policy_and_addr.IntentSuiteTag.to_u16 .HybridEd25519MlDsa65 = .ok 1282#u16 ∧
    (∀ (raw : Std.U16) (t : policy_and_addr.IntentSuiteTag),
      policy_and_addr.IntentSuiteTag.from_u16 raw = .ok (some t) ↔
        policy_and_addr.IntentSuiteTag.to_u16 t = .ok raw) ∧
    (∀ raw : Std.U16, ∃ o, policy_and_addr.IntentSuiteTag.from_u16 raw = .ok o) := by
  refine ⟨intentSuite_encode .MlDsa65, intentSuite_encode .SlhDsa128f,
    intentSuite_encode .JortsPoseidon2, intentSuite_encode .HybridSecp256k1MlDsa44,
    intentSuite_encode .HybridEd25519MlDsa65, ?_, ?_⟩
  · intro raw t
    constructor
    · intro h
      rw [intentSuite_encode, intentSuite_converse raw t h]
    · intro h
      rw [intentSuite_encode] at h
      injection h with h
      rw [← h]
      exact intentSuite_decode t
  · intro raw
    unfold policy_and_addr.IntentSuiteTag.from_u16
    split <;> exact ⟨_, rfl⟩

/-- The identity kinds carry the canonical `qsag-addr` `KeyIdentityKind` wire bytes
(`SingleOrThreshold = 1`, `HybridConjunctive = 2`, `ScriptPredicate = 3`). -/
theorem intent_identity_kind_wire_bytes :
    policy_and_addr.IntentIdentityKind.to_u8 .SingleOrThreshold = .ok 1#u8 ∧
    policy_and_addr.IntentIdentityKind.to_u8 .HybridConjunctive = .ok 2#u8 ∧
    policy_and_addr.IntentIdentityKind.to_u8 .ScriptPredicate = .ok 3#u8 ∧
    (∀ (raw : Std.U8) (k : policy_and_addr.IntentIdentityKind),
      policy_and_addr.IntentIdentityKind.from_u8 raw = .ok (some k) ↔
        policy_and_addr.IntentIdentityKind.to_u8 k = .ok raw) ∧
    (∀ raw : Std.U8, ∃ o, policy_and_addr.IntentIdentityKind.from_u8 raw = .ok o) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · intro raw k
    constructor
    · intro h
      rw [intentIdKind_encode, intentIdKind_converse raw k h]
    · intro h
      rw [intentIdKind_encode] at h
      injection h with h
      rw [← h]
      exact intentIdKind_decode k
  · intro raw
    unfold policy_and_addr.IntentIdentityKind.from_u8
    split <;> exact ⟨_, rfl⟩

/-- The identity kind each admitted suite mandates: `qsag-addr`'s
`WitnessSuiteTag::expected_identity_kind` on the five suites of this namespace. -/
@[expose]
def intentSuiteExpectedKind :
    policy_and_addr.IntentSuiteTag → policy_and_addr.IntentIdentityKind
  | .MlDsa65 => .SingleOrThreshold
  | .SlhDsa128f => .SingleOrThreshold
  | .JortsPoseidon2 => .SingleOrThreshold
  | .HybridSecp256k1MlDsa44 => .HybridConjunctive
  | .HybridEd25519MlDsa65 => .HybridConjunctive

theorem intent_expected_identity_kind_spec (t : policy_and_addr.IntentSuiteTag) :
    policy_and_addr.IntentSuiteTag.expected_identity_kind t =
      .ok (intentSuiteExpectedKind t) := by
  cases t <;> rfl

/-- `admits_identity_kind` never fails and returns `true` exactly for the mandated kind. -/
theorem intent_admits_identity_kind_spec
    (t : policy_and_addr.IntentSuiteTag) (k : policy_and_addr.IntentIdentityKind) :
    ∃ b, policy_and_addr.IntentSuiteTag.admits_identity_kind t k = .ok b ∧
      (b = true ↔ k = intentSuiteExpectedKind t) := by
  cases t <;> cases k <;> refine ⟨_, rfl, ?_⟩ <;>
    first
      | exact ⟨fun _ => rfl, fun _ => rfl⟩
      | exact ⟨fun h => absurd h (by decide), fun h => nomatch h⟩

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

private theorem encode_intent_128_eq (intent : policy_and_addr.CanonicalIntent128) :
    policy_and_addr.encode_intent_128 intent =
      .ok (pack4x32Pure (intentHeader32Bytes (intentToHeader intent))
        (intentAmounts32Bytes intent.amount_units intent.rolling_window_spent)
        intent.recipient_commitment intent.payload_digest) := by
  unfold policy_and_addr.encode_intent_128
  simp only [bind_eq_result_bind]
  rw [encode_intent_header32_eq, result_bind_ok,
      encode_intent_amounts32_eq, result_bind_ok, pack_4x32_eq]

/-- The decoder on an encoded frame: the intent itself when the pairing check passes,
`none` when it does not. -/
private theorem decode_encoded_intent_128
    (intent : policy_and_addr.CanonicalIntent128) (b : Bool)
    (hb : policy_and_addr.IntentSuiteTag.admits_identity_kind
      intent.suite_tag intent.identity_kind = .ok b) :
    policy_and_addr.decode_intent_128
      (pack4x32Pure (intentHeader32Bytes (intentToHeader intent))
        (intentAmounts32Bytes intent.amount_units intent.rolling_window_spent)
        intent.recipient_commitment intent.payload_digest) =
      .ok (if b = true then some intent else none) := by
  unfold policy_and_addr.decode_intent_128
  simp only [bind_eq_result_bind]
  rw [unpack_block32_eq _ 0#usize (by decide), result_bind_ok,
      unpack_block32_eq _ 32#usize (by decide), result_bind_ok,
      unpack_block32_eq _ 64#usize (by decide), result_bind_ok,
      unpack_block32_eq _ 96#usize (by decide), result_bind_ok]
  have h0 : (0#usize).val = 0 := rfl
  have h32 : (32#usize).val = 32 := rfl
  have h64 : (64#usize).val = 64 := rfl
  have h96 : (96#usize).val = 96 := rfl
  rw [h0, h32, h64, h96,
      sliceBlock32_pack_0, sliceBlock32_pack_32, sliceBlock32_pack_64, sliceBlock32_pack_96,
      decode_intent_header32_roundtrip, result_bind_ok]
  dsimp only
  have hb' : policy_and_addr.IntentSuiteTag.admits_identity_kind
      (intentToHeader intent).suite_tag (intentToHeader intent).identity_kind = .ok b := hb
  rw [hb', result_bind_ok]
  cases b with
  | false => rfl
  | true =>
    rw [decode_intent_amounts32_roundtrip, result_bind_ok]
    cases intent; rfl

private theorem decode_intent_128_converse
    (bytes : Std.Array Std.U8 128#usize)
    (intent : policy_and_addr.CanonicalIntent128)
    (h : policy_and_addr.decode_intent_128 bytes = .ok (some intent)) :
    policy_and_addr.encode_intent_128 intent = .ok bytes ∧
      intent.identity_kind = intentSuiteExpectedKind intent.suite_tag := by
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
      obtain ⟨b, hb, hpair⟩ :=
        intent_admits_identity_kind_spec hdr.suite_tag hdr.identity_kind
      rw [hb, result_bind_ok] at h
      cases b with
      | false => cases h
      | true =>
        have hkind : hdr.identity_kind = intentSuiteExpectedKind hdr.suite_tag := hpair.mp rfl
        simp only [↓reduceIte] at h
        cases hamt : policy_and_addr.decode_intent_amounts32 (sliceBlock32 bytes 32) with
        | fail _ => rw [hamt] at h; cases h
        | div => rw [hamt] at h; cases h
        | ok pair =>
          rcases pair with ⟨amt, spent⟩
          rw [hamt, result_bind_ok] at h
          simp only [Result.ok.injEq, Option.some.injEq] at h
          subst intent
          refine ⟨?_, hkind⟩
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

private theorem encode_intent_128_injective
    (i1 i2 : policy_and_addr.CanonicalIntent128) (bytes : Array Std.U8 128#usize)
    (he1 : policy_and_addr.encode_intent_128 i1 = .ok bytes)
    (he2 : policy_and_addr.encode_intent_128 i2 = .ok bytes) : i1 = i2 := by
  rw [encode_intent_128_eq] at he1 he2
  injection he1 with he1
  injection he2 with he2
  have hpk := he1.trans he2.symm
  have hh := congrArg (fun b => sliceBlock32 b 0) hpk
  have ha := congrArg (fun b => sliceBlock32 b 32) hpk
  have hr := congrArg (fun b => sliceBlock32 b 64) hpk
  have hp := congrArg (fun b => sliceBlock32 b 96) hpk
  rw [sliceBlock32_pack_0, sliceBlock32_pack_0] at hh
  rw [sliceBlock32_pack_32, sliceBlock32_pack_32] at ha
  rw [sliceBlock32_pack_64, sliceBlock32_pack_64] at hr
  rw [sliceBlock32_pack_96, sliceBlock32_pack_96] at hp
  have hhdr : intentToHeader i2 = intentToHeader i1 := by
    have h1 := decode_intent_header32_roundtrip (intentToHeader i1)
    rw [hh, decode_intent_header32_roundtrip] at h1
    injection h1 with h1
    injection h1
  have hamt : (i2.amount_units, i2.rolling_window_spent) =
      (i1.amount_units, i1.rolling_window_spent) := by
    have h1 := decode_intent_amounts32_roundtrip i1.amount_units i1.rolling_window_spent
    rw [ha, decode_intent_amounts32_roundtrip] at h1
    injection h1
  have hs : i2.suite_tag = i1.suite_tag := congrArg (fun h => h.suite_tag) hhdr
  have hv : i2.address_version = i1.address_version :=
    congrArg (fun h => h.address_version) hhdr
  have hk : i2.identity_kind = i1.identity_kind := congrArg (fun h => h.identity_kind) hhdr
  have hc : i2.chain_id = i1.chain_id := congrArg (fun h => h.chain_id) hhdr
  have hn : i2.nonce = i1.nonce := congrArg (fun h => h.nonce) hhdr
  have ht : i2.timestamp_secs = i1.timestamp_secs := congrArg (fun h => h.timestamp_secs) hhdr
  have hau : i2.amount_units = i1.amount_units := congrArg Prod.fst hamt
  have hsp : i2.rolling_window_spent = i1.rolling_window_spent := congrArg Prod.snd hamt
  cases i1
  cases i2
  dsimp only at hs hv hk hc hn ht hau hsp hr hp
  subst hs hv hk hc hn ht hau hsp hr hp
  rfl

/-- The 128-byte intent codec. (1) `encode_intent_128` is total, and `decode_intent_128`
reads the encoded frame back when the identity kind is the one the suite mandates and
refuses it otherwise. (2) Every frame the decoder accepts is the encoding of what it
returns, and what it returns has a valid `(suite, kind)` pair. (3) The encoding is
injective on all intents. -/
theorem intent_codec_roundtrip_injective_mir :
    (∀ intent : policy_and_addr.CanonicalIntent128,
      ∃ bytes : Array Std.U8 128#usize,
        policy_and_addr.encode_intent_128 intent = .ok bytes ∧
        (intent.identity_kind = intentSuiteExpectedKind intent.suite_tag →
          policy_and_addr.decode_intent_128 bytes = .ok (some intent)) ∧
        (intent.identity_kind ≠ intentSuiteExpectedKind intent.suite_tag →
          policy_and_addr.decode_intent_128 bytes = .ok none)) ∧
    (∀ (bytes : Array Std.U8 128#usize) (intent : policy_and_addr.CanonicalIntent128),
      policy_and_addr.decode_intent_128 bytes = .ok (some intent) →
      policy_and_addr.encode_intent_128 intent = .ok bytes ∧
        intent.identity_kind = intentSuiteExpectedKind intent.suite_tag) ∧
    (∀ (i1 i2 : policy_and_addr.CanonicalIntent128) (bytes : Array Std.U8 128#usize),
      policy_and_addr.encode_intent_128 i1 = .ok bytes →
      policy_and_addr.encode_intent_128 i2 = .ok bytes →
      i1 = i2) := by
  refine ⟨?_, decode_intent_128_converse, encode_intent_128_injective⟩
  intro intent
  obtain ⟨b, hb, hpair⟩ :=
    intent_admits_identity_kind_spec intent.suite_tag intent.identity_kind
  refine ⟨_, encode_intent_128_eq intent, ?_, ?_⟩
  · intro hvalid
    rw [decode_encoded_intent_128 intent b hb, hpair.mpr hvalid]
    rfl
  · intro hinvalid
    rw [decode_encoded_intent_128 intent b hb]
    cases b with
    | false => rfl
    | true => exact absurd (hpair.mp rfl) hinvalid

/-- A frame `decode_intent_128` accepts carries a `(suite, kind)` pair the canonical
`qsag-addr` `WitnessSuiteTag::validate_identity_kind` accepts: a hybrid suite with
`HybridConjunctive`, any other admitted suite with `SingleOrThreshold`. In particular no
decoded intent has kind `ScriptPredicate`. -/
theorem decode_intent_128_pairing_valid
    (bytes : Array Std.U8 128#usize) (intent : policy_and_addr.CanonicalIntent128)
    (h : policy_and_addr.decode_intent_128 bytes = .ok (some intent)) :
    intent.identity_kind = intentSuiteExpectedKind intent.suite_tag ∧
    intent.identity_kind ≠ .ScriptPredicate := by
  have hkind := (decode_intent_128_converse bytes intent h).2
  refine ⟨hkind, ?_⟩
  rw [hkind]
  cases intent.suite_tag <;> exact fun h => nomatch h

/-! ## 3. Hybrid Domain Framing & SHAKE256 Transcript Derivation -/

@[expose]
def hybridDomainMagic14 : Array Std.U8 14#usize :=
  Array.make 14#usize [
    81#u8, 83#u8, 65#u8, 71#u8, 46#u8, 72#u8, 89#u8, 66#u8,
    82#u8, 73#u8, 68#u8, 46#u8, 86#u8, 50#u8]

@[expose]
def hybridRoleByte : policy_and_addr.HybridRoleTag → Std.U8
  | .Classical => 1#u8
  | .PostQuantum => 2#u8

private theorem hybridRole_to_u8_eq (r : policy_and_addr.HybridRoleTag) :
    policy_and_addr.HybridRoleTag.to_u8 r = .ok (hybridRoleByte r) := by
  cases r <;> rfl

private theorem u8_or_eq_zero_iff (a b : Std.U8) :
    a ||| b = 0#u8 ↔ a = 0#u8 ∧ b = 0#u8 := by
  constructor
  · intro h
    obtain ⟨ha, hb⟩ := BitVec.or_eq_zero_iff.mp (congrArg UScalar.bv h)
    exact ⟨UScalar.ext ha, UScalar.ext hb⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem check_hybrid_domain_framing_spec
    (magic14 : Array Std.U8 14#usize) (wire_role_byte : Std.U8)
    (expected_role : policy_and_addr.HybridRoleTag) (suite_code : Std.U16)
    (expected_id_commit wire_id_commit : Array Std.U8 32#usize) :
    policy_and_addr.check_hybrid_domain_framing
      magic14 wire_role_byte expected_role suite_code expected_id_commit wire_id_commit =
    .ok (decide (magic14 = hybridDomainMagic14 ∧
      (suite_code = 1281#u16 ∨ suite_code = 1282#u16) ∧
      wire_role_byte = hybridRoleByte expected_role ∧
      expected_id_commit = wire_id_commit)) := by
  have index (i : Std.Usize) (hi : i.val < 14) :
      Std.Array.index_usize magic14 i = .ok (magic14.val.getD i.val 0#u8) :=
    array_index_getD magic14 i 0#u8 hi
  unfold policy_and_addr.check_hybrid_domain_framing
    policy_and_addr.SUITE_HYBRID_SECP256K1_MLDSA44
    policy_and_addr.SUITE_HYBRID_ED25519_MLDSA65
  apply bind_ok_step (index 0#usize (by decide)); apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (index 1#usize (by decide)); apply bind_ok_step (lift_eq_ok _); apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (index 2#usize (by decide)); apply bind_ok_step (lift_eq_ok _); apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (index 3#usize (by decide)); apply bind_ok_step (lift_eq_ok _); apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (index 4#usize (by decide)); apply bind_ok_step (lift_eq_ok _); apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (index 5#usize (by decide)); apply bind_ok_step (lift_eq_ok _); apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (index 6#usize (by decide)); apply bind_ok_step (lift_eq_ok _); apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (index 7#usize (by decide)); apply bind_ok_step (lift_eq_ok _); apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (index 8#usize (by decide)); apply bind_ok_step (lift_eq_ok _); apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (index 9#usize (by decide)); apply bind_ok_step (lift_eq_ok _); apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (index 10#usize (by decide)); apply bind_ok_step (lift_eq_ok _); apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (index 11#usize (by decide)); apply bind_ok_step (lift_eq_ok _); apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (index 12#usize (by decide)); apply bind_ok_step (lift_eq_ok _); apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (index 13#usize (by decide)); apply bind_ok_step (lift_eq_ok _); apply bind_ok_step (lift_eq_ok _)
  simp only [UScalar.val, UScalarTy.numBits, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  let diff : Std.U8 :=
    (((((((((((((magic14.val.getD 0 0#u8 ^^^ 81#u8) ||| (magic14.val.getD 1 0#u8 ^^^ 83#u8)) |||
      (magic14.val.getD 2 0#u8 ^^^ 65#u8)) ||| (magic14.val.getD 3 0#u8 ^^^ 71#u8)) |||
      (magic14.val.getD 4 0#u8 ^^^ 46#u8)) ||| (magic14.val.getD 5 0#u8 ^^^ 72#u8)) |||
      (magic14.val.getD 6 0#u8 ^^^ 89#u8)) ||| (magic14.val.getD 7 0#u8 ^^^ 66#u8)) |||
      (magic14.val.getD 8 0#u8 ^^^ 82#u8)) ||| (magic14.val.getD 9 0#u8 ^^^ 73#u8)) |||
      (magic14.val.getD 10 0#u8 ^^^ 68#u8)) ||| (magic14.val.getD 11 0#u8 ^^^ 46#u8)) |||
      (magic14.val.getD 12 0#u8 ^^^ 86#u8)) ||| (magic14.val.getD 13 0#u8 ^^^ 50#u8)
  have hdiff_iff : diff = 0#u8 ↔ magic14 = hybridDomainMagic14 := by
    dsimp only [diff]
    repeat rw [u8_or_eq_zero_iff]
    repeat rw [u8_xor_zero_iff]
    constructor
    · intro h
      apply Std.Array.ext
      apply List.ext_getElem (by rw [magic14.property, hybridDomainMagic14.property])
      intro i ha _
      rw [List.getElem_eq_getD 0#u8, List.getElem_eq_getD 0#u8]
      have hi : i < 14 := by rw [magic14.property] at ha; exact ha
      rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩
      dsimp only [hybridDomainMagic14, Std.Array.make]
      match i, hi with
      | 0, _ => exact h0 | 1, _ => exact h1 | 2, _ => exact h2 | 3, _ => exact h3
      | 4, _ => exact h4 | 5, _ => exact h5 | 6, _ => exact h6 | 7, _ => exact h7
      | 8, _ => exact h8 | 9, _ => exact h9 | 10, _ => exact h10 | 11, _ => exact h11
      | 12, _ => exact h12 | 13, _ => exact h13
      | i + 14, hi => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 14 i) hi)
    · rintro rfl
      exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩
  by_cases hd : diff = 0#u8
  · have hmag : magic14 = hybridDomainMagic14 := hdiff_iff.mp hd
    change (if diff != 0#u8 then _ else _) = _
    rw [hd, bne_self_eq_false]
    simp only [Bool.false_eq_true, ↓reduceIte, bind_eq_result_bind]
    rw [hybridRole_to_u8_eq, ct_eq_bytes32_spec]
    by_cases hs1 : suite_code = 1281#u16
    · subst hs1
      by_cases hr : wire_role_byte = hybridRoleByte expected_role
      · simp [hmag, hr, result_bind_ok]
      · simp [hmag, hr, result_bind_ok]
    · by_cases hs2 : suite_code = 1282#u16
      · subst hs2
        by_cases hr : wire_role_byte = hybridRoleByte expected_role
        · simp [hs1, hmag, hr, result_bind_ok]
        · simp [hs1, hmag, hr, result_bind_ok]
      · simp [hs1, hs2, hmag, result_bind_ok]
  · have hnmag : magic14 ≠ hybridDomainMagic14 := fun hm => hd (hdiff_iff.mpr hm)
    change (if diff != 0#u8 then _ else _) = _
    have hne : (diff != 0#u8) = true := bne_iff_ne.mpr hd
    rw [hne]
    simp [hnmag]

theorem hybrid_domain_framing_role_disjoint_mir
    (magic14 : Array Std.U8 14#usize) (wire_role_byte : Std.U8)
    (suite_code : Std.U16) (expected_id_commit wire_id_commit : Array Std.U8 32#usize)
    (hClassical :
      policy_and_addr.check_hybrid_domain_framing
        magic14 wire_role_byte .Classical suite_code expected_id_commit wire_id_commit =
      .ok true) :
    policy_and_addr.check_hybrid_domain_framing
      magic14 wire_role_byte .PostQuantum suite_code expected_id_commit wire_id_commit =
    .ok false := by
  rw [check_hybrid_domain_framing_spec] at hClassical ⊢
  injection hClassical with hdec
  obtain ⟨_, _, hrole, _⟩ := of_decide_eq_true hdec
  apply congrArg Result.ok
  apply decide_eq_false
  intro ⟨_, _, hrole_pq, _⟩
  rw [hrole] at hrole_pq
  cases hrole_pq

private theorem hybrid_hash_total (d0 d1 d2 d3 d4 d5 d6 : Slice Std.U8) :
    ∃ digest, (do
      let sp ← keccak.Shake256Sponge.new_shake256
      let sp ← keccak.Shake256Sponge.absorb sp d0
      let sp ← keccak.Shake256Sponge.absorb sp d1
      let sp ← keccak.Shake256Sponge.absorb sp d2
      let sp ← keccak.Shake256Sponge.absorb sp d3
      let sp ← keccak.Shake256Sponge.absorb sp d4
      let sp ← keccak.Shake256Sponge.absorb sp d5
      let sp ← keccak.Shake256Sponge.absorb sp d6
      let out := Array.repeat 32#usize 0#u8
      let (dst, back) ← lift (Array.to_slice_mut out)
      let (_, dst) ← keccak.Shake256Sponge.squeeze sp dst
      ok (some (back dst))) = .ok (some digest) := by
  obtain ⟨s0, h0, inv0, _⟩ := sponge_new_shake256_absorbed
  obtain ⟨s1, h1, inv1, _⟩ := sponge_absorb_refines s0 d0 _ inv0
  obtain ⟨s2, h2, inv2, _⟩ := sponge_absorb_refines s1 d1 _ inv1
  obtain ⟨s3, h3, inv3, _⟩ := sponge_absorb_refines s2 d2 _ inv2
  obtain ⟨s4, h4, inv4, _⟩ := sponge_absorb_refines s3 d3 _ inv3
  obtain ⟨s5, h5, inv5, _⟩ := sponge_absorb_refines s4 d4 _ inv4
  obtain ⟨s6, h6, inv6, _⟩ := sponge_absorb_refines s5 d5 _ inv5
  obtain ⟨s7, h7, inv7, _⟩ := sponge_absorb_refines s6 d6 _ inv6
  have hc := inv7.canonical
  obtain ⟨result, hr⟩ := sponge_squeeze_short s7
    (Array.to_slice_mut (Array.repeat 32#usize 0#u8)).1 32 (by decide) hc.1
    (by rw [hc.2.1]; exact Nat.mod_lt _ (by decide)) rfl
  refine ⟨(Array.to_slice_mut (Array.repeat 32#usize 0#u8)).2 result.2, ?_⟩
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, hr,
    bind_eq_result_bind, result_bind_ok, lift_eq_ok]

theorem derive_hybrid_transcript_digest_total
    (role : policy_and_addr.HybridRoleTag) (suite_code : Std.U16)
    (id_commit pk_classical_digest pk_pq_digest : Array Std.U8 32#usize)
    (message : Slice Std.U8) :
    (suite_code = 1281#u16 ∨ suite_code = 1282#u16 →
      ∃ digest, policy_and_addr.derive_hybrid_transcript_digest
        role suite_code id_commit pk_classical_digest pk_pq_digest message = .ok (some digest)) ∧
    (suite_code ≠ 1281#u16 ∧ suite_code ≠ 1282#u16 →
      policy_and_addr.derive_hybrid_transcript_digest
        role suite_code id_commit pk_classical_digest pk_pq_digest message = .ok none) := by
  have headerShift (x : Std.U16) : (x >>> 8#i32 : Result Std.U16) = .ok ⟨x.bv >>> 8⟩ := rfl
  have sh56 (x : Std.U64) : (x >>> 56#i32 : Result Std.U64) = .ok ⟨x.bv >>> 56⟩ := rfl
  have sh48 (x : Std.U64) : (x >>> 48#i32 : Result Std.U64) = .ok ⟨x.bv >>> 48⟩ := rfl
  have sh40 (x : Std.U64) : (x >>> 40#i32 : Result Std.U64) = .ok ⟨x.bv >>> 40⟩ := rfl
  have sh32 (x : Std.U64) : (x >>> 32#i32 : Result Std.U64) = .ok ⟨x.bv >>> 32⟩ := rfl
  have sh24 (x : Std.U64) : (x >>> 24#i32 : Result Std.U64) = .ok ⟨x.bv >>> 24⟩ := rfl
  have sh16 (x : Std.U64) : (x >>> 16#i32 : Result Std.U64) = .ok ⟨x.bv >>> 16⟩ := rfl
  have sh8 (x : Std.U64) : (x >>> 8#i32 : Result Std.U64) = .ok ⟨x.bv >>> 8⟩ := rfl
  constructor
  · intro valid
    rcases valid with h | h <;> subst suite_code <;>
      simp only [policy_and_addr.derive_hybrid_transcript_digest, ↓reduceIte,
        hybridRole_to_u8_eq, headerShift, sh16, sh56, sh48, sh40, sh32, sh24, sh8,
        bind_eq_result_bind, result_bind_ok, lift_eq_ok] <;>
      exact hybrid_hash_total _ _ _ _ _ _ _
  · rintro ⟨h1, h2⟩
    simp only [policy_and_addr.derive_hybrid_transcript_digest, h1, h2, ↓reduceIte]

/-! ## 4. Concrete `#tooth` Refusal Witnesses -/

theorem tooth_policy_cap_exceeded_rejected :
    let pin := Array.repeat 32#usize 0x55#u8
    let req1 : policy_and_addr.VelocitySpendRequest :=
      { window_id := 7#u64, nonce := 1#u64, amount_units := 60#u128,
        policy_pin := pin, authority_pin := pin }
    let req2 : policy_and_addr.VelocitySpendRequest :=
      { window_id := 7#u64, nonce := 2#u64, amount_units := 50#u128,
        policy_pin := pin, authority_pin := pin }
    (policy_and_addr.StatefulVelocityGuard.new_window 7#u64 100#u128 pin pin >>= fun g0 =>
      policy_and_addr.StatefulVelocityGuard.authorize_spend g0 req1 >>= fun (g1, _) =>
        policy_and_addr.StatefulVelocityGuard.authorize_spend g1 req2) =
    .ok ({ window_id := 7#u64, spent_units := 60#u128, cap_units := 100#u128,
           policy_pin := pin, authority_pin := pin, last_nonce := 1#u64 },
         .Err .VelocityCapExceeded) := by
  dsimp only
  have hpin : tower.ct_eq_bytes32 (Array.repeat 32#usize 0x55#u8)
      (Array.repeat 32#usize 0x55#u8) = .ok true := by
    rw [ct_eq_bytes32_spec]; rfl
  obtain ⟨rem0, hrem0, hrem0_val⟩ := max_velocity_sub_spec 0#u128
  obtain ⟨rem60, hrem60, hrem60_val⟩ := max_velocity_sub_spec 60#u128
  have hnle1 : ¬ (1#u64 <= 0#u64) := by decide
  have hnle2 : ¬ (2#u64 <= 1#u64) := by decide
  have hov1 : ¬ (60#u128 > rem0) := by
    intro h
    have hv := (UScalar.lt_iff_val _ _).mp h
    rw [hrem0_val] at hv
    exact absurd hv (by decide)
  have hov2 : ¬ (50#u128 > rem60) := by
    intro h
    have hv := (UScalar.lt_iff_val _ _).mp h
    rw [hrem60_val] at hv
    exact absurd hv (by decide)
  have hadd1 : (0#u128 + 60#u128 : Result Std.U128) = .ok 60#u128 := by
    simp [hAdd_uscalar_eq]
  have hadd2 : (60#u128 + 50#u128 : Result Std.U128) = .ok 110#u128 := by
    simp [hAdd_uscalar_eq]
  have hcap1 : ¬ (60#u128 > 100#u128) := by decide
  have hcap2 : (110#u128 > 100#u128) := by decide
  unfold policy_and_addr.StatefulVelocityGuard.new_window
    policy_and_addr.StatefulVelocityGuard.authorize_spend
  simp only [hpin, bne_self_eq_false, Bool.false_eq_true, hnle1, ↓reduceIte,
    bind_eq_result_bind, result_bind_ok]
  rw [hrem0, result_bind_ok]
  simp only [hov1, ↓reduceIte]
  rw [hadd1, result_bind_ok]
  simp only [hcap1, ↓reduceIte, result_bind_ok, hpin, bne_self_eq_false, Bool.false_eq_true, hnle2]
  rw [hrem60, result_bind_ok]
  simp only [hov2, ↓reduceIte]
  rw [hadd2, result_bind_ok]
  simp only [hcap2, ↓reduceIte]

theorem tooth_policy_u128_overflow_rejected :
    let pin := Array.repeat 32#usize 0x66#u8
    let max_u128 := 340282366920938463463374607431768211455#u128
    let req1 : policy_and_addr.VelocitySpendRequest :=
      { window_id := 9#u64, nonce := 1#u64, amount_units := max_u128,
        policy_pin := pin, authority_pin := pin }
    let req2 : policy_and_addr.VelocitySpendRequest :=
      { window_id := 9#u64, nonce := 2#u64, amount_units := 1#u128,
        policy_pin := pin, authority_pin := pin }
    (policy_and_addr.StatefulVelocityGuard.new_window 9#u64 max_u128 pin pin >>= fun g0 =>
      policy_and_addr.StatefulVelocityGuard.authorize_spend g0 req1 >>= fun (g1, _) =>
        policy_and_addr.StatefulVelocityGuard.authorize_spend g1 req2) =
    .ok ({ window_id := 9#u64, spent_units := max_u128, cap_units := max_u128,
           policy_pin := pin, authority_pin := pin, last_nonce := 1#u64 },
         .Err .VelocityArithmeticOverflow) := by
  dsimp only
  have hpin : tower.ct_eq_bytes32 (Array.repeat 32#usize 0x66#u8)
      (Array.repeat 32#usize 0x66#u8) = .ok true := by
    rw [ct_eq_bytes32_spec]; rfl
  obtain ⟨rem0, hrem0, hrem0_val⟩ := max_velocity_sub_spec 0#u128
  obtain ⟨rem_max, hrem_max, hrem_max_val⟩ :=
    max_velocity_sub_spec 340282366920938463463374607431768211455#u128
  have hnle1 : ¬ (1#u64 <= 0#u64) := by decide
  have hnle2 : ¬ (2#u64 <= 1#u64) := by decide
  have hov1 : ¬ (340282366920938463463374607431768211455#u128 > rem0) := by
    intro h
    have hv := (UScalar.lt_iff_val _ _).mp h
    rw [hrem0_val] at hv
    exact absurd hv (by decide)
  have hadd1 :
      (0#u128 + 340282366920938463463374607431768211455#u128 : Result Std.U128) =
        .ok 340282366920938463463374607431768211455#u128 := by
    simp [hAdd_uscalar_eq]
  have hcap1 :
      ¬ (340282366920938463463374607431768211455#u128 >
          340282366920938463463374607431768211455#u128) := by decide
  have hov2 : (1#u128 > rem_max) := by
    apply (UScalar.lt_iff_val _ _).mpr
    rw [hrem_max_val]
    decide
  unfold policy_and_addr.StatefulVelocityGuard.new_window
    policy_and_addr.StatefulVelocityGuard.authorize_spend
  simp only [hpin, bne_self_eq_false, Bool.false_eq_true, hnle1, ↓reduceIte,
    bind_eq_result_bind, result_bind_ok]
  rw [hrem0, result_bind_ok]
  simp only [hov1, ↓reduceIte]
  rw [hadd1, result_bind_ok]
  simp only [hcap1, ↓reduceIte, result_bind_ok, hpin, bne_self_eq_false, Bool.false_eq_true, hnle2]
  rw [hrem_max, result_bind_ok]
  simp only [hov2, ↓reduceIte]

theorem tooth_intent_bad_magic_rejected :
    policy_and_addr.decode_intent_128 (Array.repeat 128#usize 0#u8) = .ok none := by
  let z := Array.repeat 128#usize 0#u8
  unfold policy_and_addr.decode_intent_128
  simp only [bind_eq_result_bind]
  rw [unpack_block32_eq z 0#usize (by decide), result_bind_ok,
      unpack_block32_eq z 32#usize (by decide), result_bind_ok,
      unpack_block32_eq z 64#usize (by decide), result_bind_ok,
      unpack_block32_eq z 96#usize (by decide), result_bind_ok]
  have hhdr : policy_and_addr.decode_intent_header32 (sliceBlock32 z (0#usize).val) = .ok none := by
    have index (i : Std.Usize) (hi : i.val < 32) :
        Std.Array.index_usize (sliceBlock32 z (0#usize).val) i =
          .ok ((sliceBlock32 z (0#usize).val).val.getD i.val 0#u8) :=
      array_index_getD (sliceBlock32 z (0#usize).val) i 0#u8 hi
    unfold policy_and_addr.decode_intent_header32 policy_and_addr.INTENT_V1_MAGIC
    simp (disch := decide) only [index, bind_eq_result_bind, result_bind_ok,
      read16_eq, read32p_eq, read64p_eq]
    have hb0 : (sliceBlock32 z (0#usize).val).val.getD (0#usize).val 0#u8 = 0#u8 := rfl
    have hb1 : (sliceBlock32 z (0#usize).val).val.getD (1#usize).val 0#u8 = 0#u8 := rfl
    have hb2 : (sliceBlock32 z (0#usize).val).val.getD (2#usize).val 0#u8 = 0#u8 := rfl
    have hb3 : (sliceBlock32 z (0#usize).val).val.getD (3#usize).val 0#u8 = 0#u8 := rfl
    rw [hb0, hb1, hb2, hb3]
    have hr0 : read32p 0#u8 0#u8 0#u8 0#u8 = 0#u32 := by
      apply UScalar.ext
      simp [read32p, UScalar.cast]
    have h0ne : (0#u32 : Std.U32) ≠ 1364412721#u32 := by
      intro h
      have hv : (0#u32 : Std.U32).val = (1364412721#u32 : Std.U32).val := congrArg UScalar.val h
      exact absurd hv (by decide)
    have hne : (0#u32 != 1364412721#u32) = true := bne_iff_ne.mpr h0ne
    rw [hr0, hne]
    rfl
  rw [hhdr, result_bind_ok]

/-- The three words the verified namespace used before it adopted the canonical tags
(`0x0101`, `0x0201`, `0x0302`) are refused. -/
theorem tooth_intent_retired_suite_words_rejected :
    policy_and_addr.IntentSuiteTag.from_u16 257#u16 = .ok none ∧
    policy_and_addr.IntentSuiteTag.from_u16 513#u16 = .ok none ∧
    policy_and_addr.IntentSuiteTag.from_u16 770#u16 = .ok none :=
  ⟨rfl, rfl, rfl⟩

/-- A hybrid suite paired with a single-key identity kind encodes, and the decoder refuses
the frame. -/
theorem tooth_intent_hybrid_suite_single_kind_rejected :
    let z := Array.repeat 32#usize 0#u8
    let intent : policy_and_addr.CanonicalIntent128 :=
      { suite_tag := .HybridEd25519MlDsa65, address_version := .V2,
        identity_kind := .SingleOrThreshold, chain_id := 7#u64, nonce := 9#u64,
        timestamp_secs := 11#u64, amount_units := 13#u128, rolling_window_spent := 17#u128,
        recipient_commitment := z, payload_digest := z }
    ∃ bytes, policy_and_addr.encode_intent_128 intent = .ok bytes ∧
      policy_and_addr.decode_intent_128 bytes = .ok none := by
  intro z intent
  obtain ⟨bytes, henc, _, hrefuse⟩ := intent_codec_roundtrip_injective_mir.1 intent
  exact ⟨bytes, henc, hrefuse (fun h => nomatch h)⟩

theorem tooth_hybrid_role_confusion_rejected :
    let idc := Array.repeat 32#usize 0x77#u8
    policy_and_addr.check_hybrid_domain_framing
      hybridDomainMagic14 1#u8 .PostQuantum 1281#u16 idc idc = .ok false := by
  dsimp only
  rw [check_hybrid_domain_framing_spec]
  apply congrArg Result.ok
  apply decide_eq_false
  intro ⟨_, _, hrole, _⟩
  cases hrole

/-! ## Shared checked velocity helper -/

/-- `checked_velocity_spend` never panics and returns the exact cumulative total precisely
when it fits under the cap; otherwise it returns `none`. The total is the integer sum, with
no wrap-around. Production admission (`qsag-policy`) calls this function. -/
theorem checked_velocity_spend_spec (prior amount cap : Std.U128) :
    policy_and_addr.checked_velocity_spend prior amount cap =
        .ok (if prior.val + amount.val ≤ cap.val then
          some (⟨prior.bv + amount.bv⟩ : Std.U128) else none) ∧
      (prior.val + amount.val ≤ cap.val →
        (⟨prior.bv + amount.bv⟩ : Std.U128).val = prior.val + amount.val) := by
  have hmax : core.num.U128.MAX.val = 2 ^ 128 - 1 := BitVec.toNat_allOnes
  have hp : prior.val < 2 ^ 128 := prior.bv.isLt
  have hc : cap.val < 2 ^ 128 := cap.bv.isLt
  have hle : prior.val ≤ core.num.U128.MAX.val := by rw [hmax]; omega
  have hsubv : (⟨core.num.U128.MAX.bv - prior.bv⟩ : Std.U128).val = 2 ^ 128 - 1 - prior.val := by
    rw [← hmax]
    exact BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle)
  have hsum : prior.val + amount.val < 2 ^ 128 →
      (⟨prior.bv + amount.bv⟩ : Std.U128).val = prior.val + amount.val := fun h =>
    (BitVec.toNat_add _ _).trans (Nat.mod_eq_of_lt h)
  have hfit : prior.val + amount.val ≤ cap.val → prior.val + amount.val < 2 ^ 128 :=
    fun h => Nat.lt_of_le_of_lt h hc
  refine ⟨?_, fun h => hsum (hfit h)⟩
  clear hfit
  have hsub : (core.num.U128.MAX - prior : Result Std.U128) =
      .ok ⟨core.num.U128.MAX.bv - prior.bv⟩ := by
    rw [hSub_uscalar_eq, ite_eq_left_of_eq_true _ _ (eq_true hle)]
  unfold policy_and_addr.checked_velocity_spend
  refine bind_ok_step hsub ?_
  change (if amount > (⟨core.num.U128.MAX.bv - prior.bv⟩ : Std.U128) then _ else _) = _
  by_cases hov : amount > (⟨core.num.U128.MAX.bv - prior.bv⟩ : Std.U128)
  · have hv := (UScalar.lt_iff_val _ _).mp hov
    rw [hsubv] at hv
    have hnle : ¬ prior.val + amount.val ≤ cap.val := by clear hsum; omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true hov), ite_eq_right_of_eq_false _ _ (eq_false hnle)]
  · have hv : ¬ 2 ^ 128 - 1 - prior.val < amount.val := by
      rw [← hsubv]
      exact fun h => hov ((UScalar.lt_iff_val _ _).mpr h)
    have hlt : prior.val + amount.val < 2 ^ 128 := by clear hsum; omega
    have hadd : (prior + amount : Result Std.U128) = .ok ⟨prior.bv + amount.bv⟩ := by
      rw [hAdd_uscalar_eq]
      exact ite_eq_left_of_eq_true _ _ (eq_true hlt)
    rw [ite_eq_right_of_eq_false _ _ (eq_false hov)]
    refine bind_ok_step hadd ?_
    change (if (⟨prior.bv + amount.bv⟩ : Std.U128) > cap then _ else _) = _
    by_cases hcap : prior.val + amount.val ≤ cap.val
    · have hng : ¬ (⟨prior.bv + amount.bv⟩ : Std.U128) > cap := by
        intro h
        have h := (UScalar.lt_iff_val _ _).mp h
        rw [hsum hlt] at h
        exact Nat.not_lt_of_le hcap h
      rw [ite_eq_right_of_eq_false _ _ (eq_false hng), ite_eq_left_of_eq_true _ _ (eq_true hcap)]
    · have hg : (⟨prior.bv + amount.bv⟩ : Std.U128) > cap := by
        apply (UScalar.lt_iff_val _ _).mpr
        rw [hsum hlt]
        exact Nat.lt_of_not_le hcap
      rw [ite_eq_left_of_eq_true _ _ (eq_true hg), ite_eq_right_of_eq_false _ _ (eq_false hcap)]

/-- `#tooth`: the cap is enforced exactly. Spending nothing is allowed at the cap and
refused above it, and a spend that would exceed the cap by one unit is refused. -/
theorem tooth_checked_velocity_spend_cap (prior amount cap : Std.U128) :
    (prior.val + amount.val = cap.val →
        policy_and_addr.checked_velocity_spend prior amount cap =
          .ok (some ⟨prior.bv + amount.bv⟩)) ∧
      (prior.val + amount.val = cap.val + 1 →
        policy_and_addr.checked_velocity_spend prior amount cap = .ok none) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [(checked_velocity_spend_spec prior amount cap).1,
      ite_eq_left_of_eq_true _ _ (eq_true (Nat.le_of_eq h))]
  · rw [(checked_velocity_spend_spec prior amount cap).1,
      ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

end qsag_verified.proofs

