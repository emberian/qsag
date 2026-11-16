module
import all QsagVerified.Funs

public import QsagVerified.Proofs.Common
public import QsagVerified.Proofs.MirRefinementKit
public import QsagVerified.Proofs.Sponge
public import QsagVerified.Proofs.PolicyAndAddr
public import QsagVerified.Proofs.RssCutSession
public import QsagVerified.Proofs.TowerBdoz
public import QsagVerified.Proofs.PantsAndQuorumGuards

public section

/-!
# Multi-turn mediation and reachability over the extracted MIR

The single-guard proofs elsewhere in this directory stop at one of three boundaries:
the authenticated belt wrapper (`authenticated_belt::VerifiedBeltQuorumGuard`) has only
one-call lemmas, the velocity guard trace never rotates its window, and the cut session
is studied one session at a time. This module closes those three boundaries with trace
relations whose every step is a call of the extracted function itself.

* `VelocityTraceReachable` (sections 1, 11): interleaved `authorize_spend` and
  `rotate_window` calls. `velocity_multiwindow_cap_conservation`: per-window spend,
  summed in `Nat`, never exceeds the cap; window ids never go back; accepted nonces
  strictly increase across rotations.
* `BdozBurnTrace` (sections 2, 11): repeated `verify_mac_2lane_with_burn` calls.
  `bdoz_burn_trace_never_unburns`: a rejection is never followed by an acceptance.
* `RssMultiSessionTrace` (section 3): a table of `RssCutGateSession`s driven by `step`.
  `rss_multisession_sticky_poison_absorbency`: a session that rejected once never
  releases a cut; `rss_multisession_release_at_most_once`. The relation carries the
  driver's re-initialisation policy as a parameter, and
  `tooth_rss_reinit_resets_poison_and_releases` refutes the mutant policy.
* `BeltTraceReachable` (sections 4 to 10): calls of `VerifiedBeltQuorumGuard::step`.
  `belt_step_outcome` is the complete-mediation characterization of one call;
  `belt_trace_fork_free_and_epoch_monotone` is the multi-turn theorem: certificate
  epochs never decrease, a repeated epoch repeats the message, every certificate has
  at least `q` distinct in-range signers, and two certificates share more than `f`
  signers. `belt_step_total` and `belt_trace_exists` show the trace relation covers
  every call sequence; `inhabited_belt_trace_three_certificates` and
  `tooth_belt_ack_without_signer_dedup_forges_quorum` are the witness and the
  mutation counterexample.

Authorization consumes the bound epoch's grant state. Repeated requests are refused;
the existing monotonicity theorem remains valid for this stricter transition.
-/

namespace qsag_verified.proofs

open Aeneas Aeneas.Std Result ControlFlow Error
open qsag_verified

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

attribute [-simp] BitVec.getLsbD_eq_getElem

/-! ## 0. From one MIR call to one Mealy step -/

/-- An accepted call of a `(state, Result)`-returning MIR function is an accepted step of
    any Mealy specification it simulates. -/
theorem mirSim_ok_step_eq {S I O E : Type} {spec : MealySpec S I O}
    {f : S → I → Result (S × core.result.Result O E)}
    (sim : MirStepSim spec (adaptStateResult f) Eq (fun a b => a = id b) (fun a b => a = id b))
    {s s' : S} {i : I} {o : O} (h : f s i = .ok (s', .Ok o)) :
    spec.step s i = some (s', o) := by
  have hStep : adaptStateResult f s i = .ok (.accepted s' o) := by
    unfold adaptStateResult; rw [h]; rfl
  have hs := sim.ok_sim (s := s) (i_s := i) rfl rfl hStep
  cases hm : spec.step s i with
  | none => rw [hm] at hs; exact False.elim hs
  | some p =>
    rw [hm] at hs
    obtain ⟨s1, o1⟩ := p
    obtain ⟨h1, h2⟩ := hs
    subst h1; subst h2; rfl

/-- A rejected call is a refused step, and the returned state is the specification's
    error successor. -/
theorem mirSim_err_step_eq {S I O E : Type} {spec : MealySpec S I O}
    {f : S → I → Result (S × core.result.Result O E)}
    (sim : MirStepSim spec (adaptStateResult f) Eq (fun a b => a = id b) (fun a b => a = id b))
    {s s' : S} {i : I} {e : E} (h : f s i = .ok (s', .Err e)) :
    spec.step s i = none ∧ s' = spec.errStep s i := by
  have hStep : adaptStateResult f s i = .ok (.rejected s' e) := by
    unfold adaptStateResult; rw [h]; rfl
  obtain ⟨hn, hr⟩ := sim.err_preserves (s := s) (i_s := i) rfl rfl hStep
  exact ⟨hn, hr.symm⟩

/-! ## 1. Velocity guard: spend and rotation interleaved -/

/-- One caller-visible call on a `StatefulVelocityGuard`. -/
inductive VelocityAction where
  | spend (req : policy_and_addr.VelocitySpendRequest)
  | rotate (next_window_id : Std.U64) (policy_pin authority_pin : Array Std.U8 32#usize)

/-- Executions of `authorize_spend` and `rotate_window` in any order. The third index
    lists the accepted spend requests, oldest first. -/
inductive VelocityTraceReachable :
    policy_and_addr.StatefulVelocityGuard → List VelocityAction →
    List policy_and_addr.VelocitySpendRequest →
    policy_and_addr.StatefulVelocityGuard → Prop where
  | nil (st : policy_and_addr.StatefulVelocityGuard) : VelocityTraceReachable st [] [] st
  | spend_ok {st st' stF : policy_and_addr.StatefulVelocityGuard}
      {req : policy_and_addr.VelocitySpendRequest} {amt : Std.U128}
      {acts : List VelocityAction} {acc : List policy_and_addr.VelocitySpendRequest} :
      policy_and_addr.StatefulVelocityGuard.authorize_spend st req = .ok (st', .Ok amt) →
      VelocityTraceReachable st' acts acc stF →
      VelocityTraceReachable st (.spend req :: acts) (req :: acc) stF
  | spend_err {st st' stF : policy_and_addr.StatefulVelocityGuard}
      {req : policy_and_addr.VelocitySpendRequest} {e : policy_and_addr.PolicyAddrError}
      {acts : List VelocityAction} {acc : List policy_and_addr.VelocitySpendRequest} :
      policy_and_addr.StatefulVelocityGuard.authorize_spend st req = .ok (st', .Err e) →
      VelocityTraceReachable st' acts acc stF →
      VelocityTraceReachable st (.spend req :: acts) acc stF
  | rotate_ok {st st' stF : policy_and_addr.StatefulVelocityGuard}
      {w : Std.U64} {p a : Array Std.U8 32#usize}
      {acts : List VelocityAction} {acc : List policy_and_addr.VelocitySpendRequest} :
      policy_and_addr.StatefulVelocityGuard.rotate_window st w p a = .ok (st', .Ok ()) →
      VelocityTraceReachable st' acts acc stF →
      VelocityTraceReachable st (.rotate w p a :: acts) acc stF
  | rotate_err {st st' stF : policy_and_addr.StatefulVelocityGuard}
      {w : Std.U64} {p a : Array Std.U8 32#usize} {e : policy_and_addr.PolicyAddrError}
      {acts : List VelocityAction} {acc : List policy_and_addr.VelocitySpendRequest} :
      policy_and_addr.StatefulVelocityGuard.rotate_window st w p a = .ok (st', .Err e) →
      VelocityTraceReachable st' acts acc stF →
      VelocityTraceReachable st (.rotate w p a :: acts) acc stF

/-- Units authorized inside window `w`, summed in `Nat` (so no modular wraparound). -/
@[expose]
def windowSpendNat (w : Std.U64) : List policy_and_addr.VelocitySpendRequest → Nat
  | [] => 0
  | r :: rs => (if r.window_id = w then r.amount_units.val else 0) + windowSpendNat w rs

theorem windowSpendNat_eq_zero_of_forall_ne (w : Std.U64) :
    ∀ (acc : List policy_and_addr.VelocitySpendRequest),
      (∀ r ∈ acc, r.window_id ≠ w) → windowSpendNat w acc = 0
  | [], _ => rfl
  | r :: rs, h => by
    have h1 : r.window_id ≠ w := h r List.mem_cons_self
    have h2 := windowSpendNat_eq_zero_of_forall_ne w rs
      (fun x hx => h x (List.mem_cons_of_mem _ hx))
    show (if r.window_id = w then r.amount_units.val else 0) + windowSpendNat w rs = 0
    rw [ite_eq_right h1, h2]

theorem velocity_spend_ok_inv
    {st st' : policy_and_addr.StatefulVelocityGuard}
    {req : policy_and_addr.VelocitySpendRequest} {amt : Std.U128}
    (h : policy_and_addr.StatefulVelocityGuard.authorize_spend st req = .ok (st', .Ok amt)) :
    req.window_id = st.window_id ∧
    st.last_nonce.val < req.nonce.val ∧
    st.policy_pin = req.policy_pin ∧
    st.authority_pin = req.authority_pin ∧
    st.spent_units.val + req.amount_units.val ≤ st.cap_units.val ∧
    st'.spent_units.val = st.spent_units.val + req.amount_units.val ∧
    st'.window_id = st.window_id ∧
    st'.cap_units = st.cap_units ∧
    st'.last_nonce = req.nonce ∧
    amt = req.amount_units := by
  have hSim := mirSim_ok_step_eq velocity_spend_step_sim h
  dsimp only [velocitySpendMealy, MealySpec.ofPure, velocitySpendStep] at hSim
  cases hcond :
      (decide (st.policy_pin = req.policy_pin) &&
       decide (st.authority_pin = req.authority_pin) &&
       decide (req.window_id = st.window_id) &&
       decide (st.last_nonce.val < req.nonce.val) &&
       decide (st.spent_units.val + req.amount_units.val ≤ st.cap_units.val))
  · rw [hcond] at hSim; cases hSim
  · rw [hcond] at hSim
    injection hSim with hSim
    injection hSim with hm' hout
    subst hm'; subst hout
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
    rcases hcond with ⟨⟨⟨⟨hp, ha⟩, hw⟩, hnonce⟩, hcap_le⟩
    have hsum_lt : st.spent_units.val + req.amount_units.val < 2 ^ 128 :=
      Nat.lt_of_le_of_lt hcap_le st.cap_units.bv.isLt
    have hnew_val :
        (⟨st.spent_units.bv + req.amount_units.bv⟩ : Std.U128).val =
          st.spent_units.val + req.amount_units.val := by
      change (st.spent_units.bv + req.amount_units.bv).toNat = _
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt hsum_lt]
    exact ⟨hw, hnonce, hp, ha, hcap_le, hnew_val, rfl, rfl, rfl, rfl⟩

theorem velocity_spend_err_inv
    {st st' : policy_and_addr.StatefulVelocityGuard}
    {req : policy_and_addr.VelocitySpendRequest} {e : policy_and_addr.PolicyAddrError}
    (h : policy_and_addr.StatefulVelocityGuard.authorize_spend st req = .ok (st', .Err e)) :
    st' = st :=
  (mirSim_err_step_eq velocity_spend_step_sim h).2

theorem velocity_rotate_ok_inv
    {st st' : policy_and_addr.StatefulVelocityGuard} {w : Std.U64}
    {p a : Array Std.U8 32#usize}
    (h : policy_and_addr.StatefulVelocityGuard.rotate_window st w p a = .ok (st', .Ok ())) :
    st.window_id.val < w.val ∧
    st' = { st with window_id := w, spent_units := 0#u128 } := by
  obtain ⟨st2, res2, heq, hiff, hok, _⟩ := rotate_window_resets_spent_monotone_spec st w p a
  rw [heq] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok.inj h)
  exact ⟨(hiff.mp rfl).2.2, hok rfl⟩

theorem velocity_rotate_err_inv
    {st st' : policy_and_addr.StatefulVelocityGuard} {w : Std.U64}
    {p a : Array Std.U8 32#usize} {e : policy_and_addr.PolicyAddrError}
    (h : policy_and_addr.StatefulVelocityGuard.rotate_window st w p a = .ok (st', .Err e)) :
    st' = st := by
  obtain ⟨st2, res2, heq, _, _, herr⟩ := rotate_window_resets_spent_monotone_spec st w p a
  rw [heq] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok.inj h)
  exact herr e rfl

/-- Nonces are burned for good: along any trace, rotations included, every accepted
    nonce is above the guard's `last_nonce` at the start of the trace, and accepted
    nonces strictly increase. A nonce at or below `last_nonce` is never accepted in
    any suffix. -/
theorem velocity_trace_nonce_burn
    {st stF : policy_and_addr.StatefulVelocityGuard} {acts : List VelocityAction}
    {acc : List policy_and_addr.VelocitySpendRequest}
    (hTr : VelocityTraceReachable st acts acc stF) :
    st.last_nonce.val ≤ stF.last_nonce.val ∧
    (∀ r ∈ acc, st.last_nonce.val < r.nonce.val) ∧
    (acc.map (fun r => r.nonce.val)).Pairwise (· < ·) := by
  induction hTr with
  | nil st =>
    exact ⟨Nat.le_refl _, fun _ hm => False.elim (List.not_mem_nil hm), List.Pairwise.nil⟩
  | @spend_ok st st' stF req amt acts acc h _ ih =>
    obtain ⟨_, hnonce, _, _, _, _, _, _, hln, _⟩ := velocity_spend_ok_inv h
    rw [hln] at ih
    obtain ⟨hle, hmem, hpw⟩ := ih
    refine ⟨Nat.le_trans (Nat.le_of_lt hnonce) hle, ?_, ?_⟩
    · intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hnonce
      · exact Nat.lt_trans hnonce (hmem r hr)
    · refine List.Pairwise.cons ?_ hpw
      intro n hn
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hn
      exact hmem r hr
  | @spend_err st st' stF req e acts acc h _ ih =>
    have hst := velocity_spend_err_inv h
    subst hst; exact ih
  | @rotate_ok st st' stF w p a acts acc h _ ih =>
    obtain ⟨_, hst⟩ := velocity_rotate_ok_inv h
    have hln : st'.last_nonce = st.last_nonce := by rw [hst]
    rw [hln] at ih; exact ih
  | @rotate_err st st' stF w p a e acts acc h _ ih =>
    have hst := velocity_rotate_err_inv h
    subst hst; exact ih

/-- Window-budget invariant of an arbitrary spend/rotate trace. -/
theorem velocity_trace_window_budget
    {st stF : policy_and_addr.StatefulVelocityGuard} {acts : List VelocityAction}
    {acc : List policy_and_addr.VelocitySpendRequest}
    (hTr : VelocityTraceReachable st acts acc stF)
    (hInit : st.spent_units.val ≤ st.cap_units.val) :
    stF.cap_units = st.cap_units ∧
    stF.spent_units.val ≤ st.cap_units.val ∧
    st.window_id.val ≤ stF.window_id.val ∧
    (∀ r ∈ acc, st.window_id.val ≤ r.window_id.val) ∧
    st.spent_units.val + windowSpendNat st.window_id acc ≤ st.cap_units.val ∧
    (∀ w : Std.U64, st.window_id.val < w.val → windowSpendNat w acc ≤ st.cap_units.val) ∧
    (acc.map (fun r => r.window_id.val)).Pairwise (· ≤ ·) := by
  induction hTr with
  | nil st =>
    exact ⟨rfl, hInit, Nat.le_refl _, fun _ hm => False.elim (List.not_mem_nil hm),
      hInit, fun _ _ => Nat.zero_le _, List.Pairwise.nil⟩
  | @spend_ok st st' stF req amt acts acc h _ ih =>
    obtain ⟨hw, _, _, _, hcap_le, hsp, hwid, hcap, _, _⟩ := velocity_spend_ok_inv h
    have hInit' : st'.spent_units.val ≤ st'.cap_units.val := by
      rw [hsp, hcap]; exact hcap_le
    obtain ⟨ihcap, ihsp, ihw, ihmem, ihsum, ihfut, ihpw⟩ := ih hInit'
    rw [hcap] at ihcap ihsp ihsum ihfut
    rw [hwid] at ihw ihmem ihsum ihfut
    rw [hsp] at ihsum
    refine ⟨ihcap, ihsp, ihw, ?_, ?_, ?_, ?_⟩
    · intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · rw [hw]; exact Nat.le_refl _
      · exact ihmem r hr
    · show st.spent_units.val +
          ((if req.window_id = st.window_id then req.amount_units.val else 0) +
            windowSpendNat st.window_id acc) ≤ st.cap_units.val
      rw [ite_eq_left hw]; omega
    · intro w hlt
      show (if req.window_id = w then req.amount_units.val else 0) +
          windowSpendNat w acc ≤ st.cap_units.val
      have hne : req.window_id ≠ w := by
        intro he; rw [hw] at he; rw [he] at hlt; exact Nat.lt_irrefl _ hlt
      rw [ite_eq_right hne, Nat.zero_add]; exact ihfut w hlt
    · refine List.Pairwise.cons ?_ ihpw
      intro n hn
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hn
      show req.window_id.val ≤ r.window_id.val
      rw [hw]; exact ihmem r hr
  | @spend_err st st' stF req e acts acc h _ ih =>
    have hst := velocity_spend_err_inv h
    subst hst; exact ih hInit
  | @rotate_ok st st' stF w p a acts acc h _ ih =>
    obtain ⟨hlt, hst⟩ := velocity_rotate_ok_inv h
    have hwid : st'.window_id = w := by rw [hst]
    have hsp : st'.spent_units.val = 0 := by rw [hst]; rfl
    have hcap : st'.cap_units = st.cap_units := by rw [hst]
    have hInit' : st'.spent_units.val ≤ st'.cap_units.val := by
      rw [hsp]; exact Nat.zero_le _
    obtain ⟨ihcap, ihsp, ihw, ihmem, ihsum, ihfut, ihpw⟩ := ih hInit'
    rw [hcap] at ihcap ihsp ihsum ihfut
    rw [hwid] at ihw ihmem ihsum ihfut
    rw [hsp, Nat.zero_add] at ihsum
    refine ⟨ihcap, ihsp, Nat.le_trans (Nat.le_of_lt hlt) ihw,
      fun r hr => Nat.le_trans (Nat.le_of_lt hlt) (ihmem r hr), ?_, ?_, ihpw⟩
    · have hzero : windowSpendNat st.window_id acc = 0 :=
        windowSpendNat_eq_zero_of_forall_ne _ _ (fun r hr he => by
          have hge := ihmem r hr
          rw [he] at hge
          exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt hge))
      rw [hzero, Nat.add_zero]; exact hInit
    · intro w' hlt'
      rcases Nat.lt_trichotomy w'.val w.val with hlt2 | heq | hgt
      · have hzero : windowSpendNat w' acc = 0 :=
          windowSpendNat_eq_zero_of_forall_ne _ _ (fun r hr he => by
            have hge := ihmem r hr
            rw [he] at hge
            exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt2 hge))
        rw [hzero]; exact Nat.zero_le _
      · have hww : w' = w := UScalar.eq_of_val_eq heq
        rw [hww]; exact ihsum
      · exact ihfut w' hgt
  | @rotate_err st st' stF w p a e acts acc h _ ih =>
    have hst := velocity_rotate_err_inv h
    subst hst; exact ih hInit

/-- **Rolling-window cap conservation across rotations.** From `new_window`, after any
    interleaving of `authorize_spend` and `rotate_window` calls (accepted or refused):
    for every window id the units authorized in that window, summed in `Nat`, are at
    most `cap`; accepted spends appear in non-decreasing window order, so a closed
    window is never credited again; and accepted nonces strictly increase. -/
theorem velocity_multiwindow_cap_conservation
    (wid : Std.U64) (cap : Std.U128) (policy_pin authority_pin : Array Std.U8 32#usize)
    (st0 stF : policy_and_addr.StatefulVelocityGuard)
    (acts : List VelocityAction) (acc : List policy_and_addr.VelocitySpendRequest)
    (hnew : policy_and_addr.StatefulVelocityGuard.new_window
      wid cap policy_pin authority_pin = .ok st0)
    (hTr : VelocityTraceReachable st0 acts acc stF) :
    (∀ w : Std.U64, windowSpendNat w acc ≤ cap.val) ∧
    (acc.map (fun r => r.window_id.val)).Pairwise (· ≤ ·) ∧
    (acc.map (fun r => r.nonce.val)).Pairwise (· < ·) ∧
    stF.cap_units = cap ∧
    stF.spent_units.val ≤ cap.val ∧
    wid.val ≤ stF.window_id.val := by
  unfold policy_and_addr.StatefulVelocityGuard.new_window at hnew
  injection hnew with hst0
  subst hst0
  obtain ⟨hcap, hsp, hw, hmem, hsum, hfut, hpw⟩ :=
    velocity_trace_window_budget hTr (show (0#u128).val ≤ cap.val from Nat.zero_le cap.val)
  obtain ⟨_, _, hnonce⟩ := velocity_trace_nonce_burn hTr
  have hmem' : ∀ r ∈ acc, wid.val ≤ r.window_id.val := hmem
  have hsum' : 0 + windowSpendNat wid acc ≤ cap.val := hsum
  have hfut' : ∀ w : Std.U64, wid.val < w.val → windowSpendNat w acc ≤ cap.val := hfut
  refine ⟨?_, hpw, hnonce, hcap, hsp, hw⟩
  intro w
  rcases Nat.lt_trichotomy w.val wid.val with hlt | heq | hgt
  · have hzero : windowSpendNat w acc = 0 :=
      windowSpendNat_eq_zero_of_forall_ne _ _ (fun r hr he => by
        have hge := hmem' r hr
        rw [he] at hge
        exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt hge))
    rw [hzero]; exact Nat.zero_le _
  · have hww : w = wid := UScalar.eq_of_val_eq heq
    rw [hww]; omega
  · exact hfut' w hgt

/-! ## 2. BDOZ verifier session: the burn latch across calls -/

/-- Repeated `verify_mac_2lane_with_burn` calls on one verifier session, with the
    returned verdicts oldest first. -/
inductive BdozBurnTrace :
    tower.BdozVerifierSession2Lane →
    List (tower.BdozCommittedBatchOpening2Lane × Slice tower.BdozWireOpening2Lane) →
    List Bool → tower.BdozVerifierSession2Lane → Prop where
  | nil (s : tower.BdozVerifierSession2Lane) : BdozBurnTrace s [] [] s
  | call {s s' sF : tower.BdozVerifierSession2Lane}
      {batch : tower.BdozCommittedBatchOpening2Lane}
      {openings : Slice tower.BdozWireOpening2Lane} {b : Bool}
      {calls : List (tower.BdozCommittedBatchOpening2Lane × Slice tower.BdozWireOpening2Lane)}
      {verdicts : List Bool} :
      tower.verify_mac_2lane_with_burn s batch openings = .ok (s', b) →
      BdozBurnTrace s' calls verdicts sF →
      BdozBurnTrace s ((batch, openings) :: calls) (b :: verdicts) sF

theorem bdoz_burn_step_inv
    {s s' : tower.BdozVerifierSession2Lane}
    {batch : tower.BdozCommittedBatchOpening2Lane}
    {openings : Slice tower.BdozWireOpening2Lane} {b : Bool}
    (h : tower.verify_mac_2lane_with_burn s batch openings = .ok (s', b)) :
    (b = true → s.burned = false ∧ s' = s) ∧
    (b = false → s'.burned = true ∧
      s'.alpha_lanes = Array.make 2#usize [0#u128, 0#u128]) := by
  refine ⟨?_, ?_⟩
  · intro hb
    subst hb
    unfold tower.verify_mac_2lane_with_burn at h
    by_cases hbr : s.burned = true
    · simp [hbr] at h
    · simp [hbr, Bind.bind, Result.bind] at h
      cases hmac : tower.verify_mac_2lane s.alpha_lanes batch openings with
      | fail e => simp [hmac] at h
      | div => simp [hmac] at h
      | ok ok1 =>
        simp [hmac] at h
        cases ok1 with
        | false => simp at h
        | true =>
          simp at h
          exact ⟨by simpa using hbr, h.symm⟩
  · intro hb
    subst hb
    exact (verify_mac_2lane_burn_irreversible s batch openings).2 s' h

/-- A burned session never accepts again, whatever is submitted afterwards. -/
theorem bdoz_burn_trace_absorbing
    {s sF : tower.BdozVerifierSession2Lane}
    {calls : List (tower.BdozCommittedBatchOpening2Lane × Slice tower.BdozWireOpening2Lane)}
    {verdicts : List Bool}
    (hTr : BdozBurnTrace s calls verdicts sF) (hb : s.burned = true) :
    (∀ b ∈ verdicts, b = false) ∧ sF.burned = true := by
  induction hTr with
  | nil s => exact ⟨fun _ hm => False.elim (List.not_mem_nil hm), hb⟩
  | @call s s' sF batch openings b calls verdicts h _ ih =>
    obtain ⟨hT, hF⟩ := bdoz_burn_step_inv h
    cases b with
    | true =>
      have hnb := (hT rfl).1
      rw [hb] at hnb; cases hnb
    | false =>
      obtain ⟨ihv, ihb⟩ := ih (hF rfl).1
      refine ⟨?_, ihb⟩
      intro b hm
      rcases List.mem_cons.mp hm with rfl | hm
      · rfl
      · exact ihv b hm

/-- **Tag-burn conservation.** Along any call trace: a rejection is never followed by
    an acceptance; if every verdict is an acceptance the session is untouched; and
    after any rejection the session ends burned. -/
theorem bdoz_burn_trace_never_unburns
    {s sF : tower.BdozVerifierSession2Lane}
    {calls : List (tower.BdozCommittedBatchOpening2Lane × Slice tower.BdozWireOpening2Lane)}
    {verdicts : List Bool}
    (hTr : BdozBurnTrace s calls verdicts sF) :
    verdicts.Pairwise (fun earlier later => earlier = false → later = false) ∧
    ((∀ b ∈ verdicts, b = true) → sF = s) ∧
    ((∃ b ∈ verdicts, b = false) → sF.burned = true) := by
  induction hTr with
  | nil s =>
    exact ⟨List.Pairwise.nil, fun _ => rfl,
      fun ⟨_, hm, _⟩ => False.elim (List.not_mem_nil hm)⟩
  | @call s s' sF batch openings b calls verdicts h hTail ih =>
    obtain ⟨hT, hF⟩ := bdoz_burn_step_inv h
    obtain ⟨ihpw, ihall, ihex⟩ := ih
    refine ⟨List.Pairwise.cons ?_ ihpw, ?_, ?_⟩
    · intro later hm hb
      exact (bdoz_burn_trace_absorbing hTail (hF hb).1).1 later hm
    · intro hall
      have hbt : b = true := hall b List.mem_cons_self
      have hs := (hT hbt).2
      have htail := ihall (fun x hx => hall x (List.mem_cons_of_mem _ hx))
      rw [htail, hs]
    · rintro ⟨x, hm, hx⟩
      rcases List.mem_cons.mp hm with rfl | hm
      · exact (bdoz_burn_trace_absorbing hTail (hF hx).1).2
      · exact ihex ⟨x, hm, hx⟩

/-! ## 3. Cut sessions: a table of sessions and the poison latch -/

/-- Caller-side session table, keyed by session id. The table is the driver's state;
    every transition applied to an entry is the extracted `RssCutGateSession::step`. -/
abbrev RssSessionTable := Array Std.U8 32#usize → Option rss_cut_session.RssCutGateSession

@[expose]
def RssSessionTable.set (tbl : RssSessionTable) (sid : Array Std.U8 32#usize)
    (s : rss_cut_session.RssCutGateSession) : RssSessionTable :=
  fun k => if k = sid then some s else tbl k

theorem RssSessionTable.set_same (tbl : RssSessionTable) (sid : Array Std.U8 32#usize)
    (s : rss_cut_session.RssCutGateSession) : (tbl.set sid s) sid = some s :=
  ite_eq_left rfl

theorem RssSessionTable.set_other (tbl : RssSessionTable) {sid k : Array Std.U8 32#usize}
    (s : rss_cut_session.RssCutGateSession) (h : k ≠ sid) : (tbl.set sid s) k = tbl k :=
  ite_eq_right h

inductive RssSessionEvent where
  | init (sid mask_commitment : Array Std.U8 32#usize)
  | call (sid : Array Std.U8 32#usize) (input : rss_cut_session.RssCutStepInput)

/-- Interleaved executions of many cut sessions. The third index lists released cuts as
    `(session id, cut)`, oldest first. `allowReinit` is the driver policy for an `init`
    on a session id that already has an entry: `false` refuses it and keeps the entry,
    `true` overwrites the entry with a fresh `new_round1_committed` session. -/
inductive RssMultiSessionTrace (allowReinit : Bool) :
    RssSessionTable → List RssSessionEvent →
    List (Array Std.U8 32#usize × Array Std.U8 32#usize) → RssSessionTable → Prop where
  | nil (tbl : RssSessionTable) : RssMultiSessionTrace allowReinit tbl [] [] tbl
  | init_fresh {tbl tblF : RssSessionTable} {sid mask : Array Std.U8 32#usize}
      {s : rss_cut_session.RssCutGateSession} {evs : List RssSessionEvent}
      {rel : List (Array Std.U8 32#usize × Array Std.U8 32#usize)} :
      tbl sid = none →
      rss_cut_session.RssCutGateSession.new_round1_committed sid mask = .ok s →
      RssMultiSessionTrace allowReinit (tbl.set sid s) evs rel tblF →
      RssMultiSessionTrace allowReinit tbl (.init sid mask :: evs) rel tblF
  | init_refused {tbl tblF : RssSessionTable} {sid mask : Array Std.U8 32#usize}
      {old : rss_cut_session.RssCutGateSession} {evs : List RssSessionEvent}
      {rel : List (Array Std.U8 32#usize × Array Std.U8 32#usize)} :
      allowReinit = false →
      tbl sid = some old →
      RssMultiSessionTrace allowReinit tbl evs rel tblF →
      RssMultiSessionTrace allowReinit tbl (.init sid mask :: evs) rel tblF
  | init_overwrite {tbl tblF : RssSessionTable} {sid mask : Array Std.U8 32#usize}
      {old s : rss_cut_session.RssCutGateSession} {evs : List RssSessionEvent}
      {rel : List (Array Std.U8 32#usize × Array Std.U8 32#usize)} :
      allowReinit = true →
      tbl sid = some old →
      rss_cut_session.RssCutGateSession.new_round1_committed sid mask = .ok s →
      RssMultiSessionTrace allowReinit (tbl.set sid s) evs rel tblF →
      RssMultiSessionTrace allowReinit tbl (.init sid mask :: evs) rel tblF
  | released {tbl tblF : RssSessionTable} {sid cut : Array Std.U8 32#usize}
      {s s' : rss_cut_session.RssCutGateSession} {inp : rss_cut_session.RssCutStepInput}
      {evs : List RssSessionEvent}
      {rel : List (Array Std.U8 32#usize × Array Std.U8 32#usize)} :
      tbl sid = some s →
      rss_cut_session.RssCutGateSession.step s inp = .ok (s', .Ok (.CutReleased cut)) →
      RssMultiSessionTrace allowReinit (tbl.set sid s') evs rel tblF →
      RssMultiSessionTrace allowReinit tbl (.call sid inp :: evs) ((sid, cut) :: rel) tblF
  | progressed {tbl tblF : RssSessionTable} {sid : Array Std.U8 32#usize}
      {s s' : rss_cut_session.RssCutGateSession} {inp : rss_cut_session.RssCutStepInput}
      {o : rss_cut_session.RssCutStepOutput} {evs : List RssSessionEvent}
      {rel : List (Array Std.U8 32#usize × Array Std.U8 32#usize)} :
      tbl sid = some s →
      rss_cut_session.RssCutGateSession.step s inp = .ok (s', .Ok o) →
      (∀ cut, o ≠ .CutReleased cut) →
      RssMultiSessionTrace allowReinit (tbl.set sid s') evs rel tblF →
      RssMultiSessionTrace allowReinit tbl (.call sid inp :: evs) rel tblF
  | failed {tbl tblF : RssSessionTable} {sid : Array Std.U8 32#usize}
      {s s' : rss_cut_session.RssCutGateSession} {inp : rss_cut_session.RssCutStepInput}
      {e : rss_cut_session.RssCutError} {evs : List RssSessionEvent}
      {rel : List (Array Std.U8 32#usize × Array Std.U8 32#usize)} :
      tbl sid = some s →
      rss_cut_session.RssCutGateSession.step s inp = .ok (s', .Err e) →
      RssMultiSessionTrace allowReinit (tbl.set sid s') evs rel tblF →
      RssMultiSessionTrace allowReinit tbl (.call sid inp :: evs) rel tblF
  | unknown {tbl tblF : RssSessionTable} {sid : Array Std.U8 32#usize}
      {inp : rss_cut_session.RssCutStepInput} {evs : List RssSessionEvent}
      {rel : List (Array Std.U8 32#usize × Array Std.U8 32#usize)} :
      tbl sid = none →
      RssMultiSessionTrace allowReinit tbl evs rel tblF →
      RssMultiSessionTrace allowReinit tbl (.call sid inp :: evs) rel tblF

/-- A session that can no longer release: poisoned, or its one cut already opened. -/
@[expose]
def RssSealed (s : rss_cut_session.RssCutGateSession) : Prop :=
  s.poisoned = true ∨ s.phase = .CutOpened

theorem rss_sealed_mealy_none (s : rss_cut_session.RssCutGateSession)
    (inp : rss_cut_session.RssCutStepInput) (hs : RssSealed s) :
    rssCutMealy.step s inp = none := by
  rcases hs with hp | hph
  · simp [rssCutMealy, hp]
  · cases inp <;> simp [rssCutMealy, hph]

/-- Every call on a sealed session is rejected and leaves it poisoned. -/
theorem rss_sealed_step
    {s s' : rss_cut_session.RssCutGateSession} {inp : rss_cut_session.RssCutStepInput}
    {res : core.result.Result rss_cut_session.RssCutStepOutput rss_cut_session.RssCutError}
    (hs : RssSealed s)
    (h : rss_cut_session.RssCutGateSession.step s inp = .ok (s', res)) :
    (∃ e, res = .Err e) ∧ s'.poisoned = true := by
  cases res with
  | Ok o =>
    have hm := mirSim_ok_step_eq rss_cut_step_sim h
    rw [rss_sealed_mealy_none s inp hs] at hm
    cases hm
  | Err e =>
    obtain ⟨_, hs'⟩ := mirSim_err_step_eq rss_cut_step_sim h
    exact ⟨⟨e, rfl⟩, by rw [hs']; rfl⟩

/-- Any rejected call poisons the session, whatever the reason for the rejection. -/
theorem rss_step_err_poisons
    {s s' : rss_cut_session.RssCutGateSession} {inp : rss_cut_session.RssCutStepInput}
    {e : rss_cut_session.RssCutError}
    (h : rss_cut_session.RssCutGateSession.step s inp = .ok (s', .Err e)) :
    s'.poisoned = true := by
  obtain ⟨_, hs'⟩ := mirSim_err_step_eq rss_cut_step_sim h
  rw [hs']; rfl

/-- Complete mediation of the release: a `CutReleased` output only comes out of an
    unpoisoned session in `Round3ConsistencyVerified` with the consistency flag set, it
    is the stored candidate, and the session moves to `CutOpened`. -/
theorem rss_step_release_inv
    {s s' : rss_cut_session.RssCutGateSession} {inp : rss_cut_session.RssCutStepInput}
    {cut : Array Std.U8 32#usize}
    (h : rss_cut_session.RssCutGateSession.step s inp = .ok (s', .Ok (.CutReleased cut))) :
    s'.phase = .CutOpened ∧ s.poisoned = false ∧
    s.phase = .Round3ConsistencyVerified ∧ s.consistency_verified = true ∧
    cut = s.candidate_cut_bytes := by
  have hm := mirSim_ok_step_eq rss_cut_step_sim h
  have hp : s.poisoned = false := by
    cases hp : s.poisoned
    · rfl
    · simp [rssCutMealy, hp] at hm
  cases inp with
  | AdvanceRound2Chi a b c =>
    exfalso
    by_cases h1 : s.session_id = a <;> by_cases h2 : s.mask_commitment = b <;>
      cases hph : s.phase <;> simp [rssCutMealy, hp, hph, h1, h2] at hm
  | AdvanceRound3VerifyConsistency a lo hi dzk =>
    exfalso
    by_cases h1 : s.session_id = a <;> by_cases h2 : lo = 0#u128 <;>
      by_cases h3 : hi = 0#u128 <;> by_cases h4 : dzk = 0#u64 <;>
      cases hph : s.phase <;> simp [rssCutMealy, hp, hph, h1, h2, h3, h4] at hm
  | OpenVerifiedCut req =>
    by_cases h1 : s.session_id = req
    · cases hph : s.phase with
      | Round3ConsistencyVerified =>
        cases hcv : s.consistency_verified with
        | false => simp [rssCutMealy, hp, hph, h1, hcv] at hm
        | true =>
          have hf : rssCutMealy.step s (.OpenVerifiedCut req) =
              some ({ s with phase := .CutOpened,
                             candidate_cut_bytes := Array.repeat 32#usize 0#u8 },
                    .CutReleased s.candidate_cut_bytes) := by
            simp [rssCutMealy, hp, hph, h1, hcv]
          rw [hf] at hm
          injection hm with hm
          injection hm with ha hb
          injection hb with hc
          subst ha; subst hc
          exact ⟨rfl, hp, rfl, rfl, rfl⟩
      | _ => simp [rssCutMealy, hp, hph, h1] at hm
    · simp [rssCutMealy, hp, h1] at hm

/-- On a poisoned session every entry point answers `SessionPoisoned`. -/
theorem rss_poisoned_step_exact (s : rss_cut_session.RssCutGateSession)
    (inp : rss_cut_session.RssCutStepInput) (hp : s.poisoned = true) :
    rss_cut_session.RssCutGateSession.step s inp =
      .ok ({ session_id := s.session_id, phase := .Poisoned,
             mask_commitment := s.mask_commitment,
             candidate_cut_bytes := Array.repeat 32#usize 0#u8,
             consistency_verified := false, poisoned := true },
           .Err .SessionPoisoned) := by
  cases inp <;>
    simp [rss_cut_session.RssCutGateSession.step,
      rss_cut_session.RssCutGateSession.advance_round2_chi,
      rss_cut_session.RssCutGateSession.advance_round3_verify_consistency,
      rss_cut_session.RssCutGateSession.open_verified_cut,
      rss_cut_session.poison_rss_cut_session, hp]

/-- A sealed session stays sealed and releases nothing, across any interleaving with
    other sessions, as long as the driver refuses re-initialisation. -/
theorem rss_multisession_sealed_absorbing
    {tbl tblF : RssSessionTable} {evs : List RssSessionEvent}
    {rel : List (Array Std.U8 32#usize × Array Std.U8 32#usize)}
    (hTr : RssMultiSessionTrace false tbl evs rel tblF)
    {sid : Array Std.U8 32#usize} {s : rss_cut_session.RssCutGateSession}
    (hs : tbl sid = some s) (hsealed : RssSealed s) :
    (∀ cut, (sid, cut) ∉ rel) ∧ ∃ sF, tblF sid = some sF ∧ RssSealed sF := by
  induction hTr generalizing s with
  | nil tbl => exact ⟨fun _ hm => False.elim (List.not_mem_nil hm), s, hs, hsealed⟩
  | @init_fresh tbl tblF sid' mask s0 evs rel hnone _ _ ih =>
    have hne : sid ≠ sid' := by
      intro he; rw [he, hnone] at hs; cases hs
    exact ih (by rw [RssSessionTable.set_other _ _ hne]; exact hs) hsealed
  | @init_refused tbl tblF sid' mask old evs rel _ _ _ ih => exact ih hs hsealed
  | @init_overwrite tbl tblF sid' mask old s0 evs rel hflag _ _ _ _ => cases hflag
  | @released tbl tblF sid' cut s1 s1' inp evs rel hs1 hstep _ ih =>
    by_cases he : sid = sid'
    · subst he
      rw [hs] at hs1
      injection hs1 with hs1
      subst hs1
      obtain ⟨⟨e, he⟩, _⟩ := rss_sealed_step hsealed hstep
      cases he
    · obtain ⟨ihrel, ihF⟩ :=
        ih (by rw [RssSessionTable.set_other _ _ he]; exact hs) hsealed
      refine ⟨?_, ihF⟩
      intro c hm
      rcases List.mem_cons.mp hm with heq | hm
      · injection heq with h1 _
        exact he h1
      · exact ihrel c hm
  | @progressed tbl tblF sid' s1 s1' inp o evs rel hs1 hstep _ _ ih =>
    by_cases he : sid = sid'
    · subst he
      rw [hs] at hs1
      injection hs1 with hs1
      subst hs1
      obtain ⟨⟨e, he⟩, _⟩ := rss_sealed_step hsealed hstep
      cases he
    · exact ih (by rw [RssSessionTable.set_other _ _ he]; exact hs) hsealed
  | @failed tbl tblF sid' s1 s1' inp e evs rel hs1 hstep _ ih =>
    by_cases he : sid = sid'
    · subst he
      exact ih (RssSessionTable.set_same _ _ _) (Or.inl (rss_step_err_poisons hstep))
    · exact ih (by rw [RssSessionTable.set_other _ _ he]; exact hs) hsealed
  | @unknown tbl tblF sid' inp evs rel _ _ ih => exact ih hs hsealed

/-- **Sticky poison absorbency.** If a call on session `sid` is rejected, then in every
    continuation of the trace (any events, on any sessions) no cut is ever released
    for `sid`, and `sid` ends sealed. -/
theorem rss_multisession_sticky_poison_absorbency
    {tbl tblF : RssSessionTable} {sid : Array Std.U8 32#usize}
    {s s' : rss_cut_session.RssCutGateSession} {inp : rss_cut_session.RssCutStepInput}
    {e : rss_cut_session.RssCutError} {evs : List RssSessionEvent}
    {rel : List (Array Std.U8 32#usize × Array Std.U8 32#usize)}
    (hs : tbl sid = some s)
    (hstep : rss_cut_session.RssCutGateSession.step s inp = .ok (s', .Err e))
    (hTr : RssMultiSessionTrace false tbl (.call sid inp :: evs) rel tblF) :
    (∀ cut, (sid, cut) ∉ rel) ∧ ∃ sF, tblF sid = some sF ∧ RssSealed sF := by
  cases hTr with
  | released hs1 hstep1 _ =>
    rw [hs] at hs1
    injection hs1 with hs1
    subst hs1
    rw [hstep] at hstep1
    injection hstep1 with hstep1
    injection hstep1 with _ hres
    cases hres
  | progressed hs1 hstep1 _ _ =>
    rw [hs] at hs1
    injection hs1 with hs1
    subst hs1
    rw [hstep] at hstep1
    injection hstep1 with hstep1
    injection hstep1 with _ hres
    cases hres
  | failed hs1 hstep1 hTail =>
    rw [hs] at hs1
    injection hs1 with hs1
    subst hs1
    exact rss_multisession_sealed_absorbing hTail (RssSessionTable.set_same _ _ _)
      (Or.inl (rss_step_err_poisons hstep1))
  | unknown hnone _ => rw [hs] at hnone; cases hnone

/-- Each session id releases at most one cut over the whole trace. -/
theorem rss_multisession_release_at_most_once
    {tbl tblF : RssSessionTable} {evs : List RssSessionEvent}
    {rel : List (Array Std.U8 32#usize × Array Std.U8 32#usize)}
    (hTr : RssMultiSessionTrace false tbl evs rel tblF) :
    (rel.map Prod.fst).Pairwise (· ≠ ·) := by
  induction hTr with
  | nil tbl => exact List.Pairwise.nil
  | init_fresh _ _ _ ih => exact ih
  | init_refused _ _ _ ih => exact ih
  | init_overwrite hflag _ _ _ _ => cases hflag
  | @released tbl tblF sid cut s1 s1' inp evs rel hs1 hstep hTail ih =>
    refine List.Pairwise.cons ?_ ih
    intro sid2 hm heq
    obtain ⟨p, hp, hfst⟩ := List.mem_map.mp hm
    obtain ⟨sidp, cutp⟩ := p
    have hsealed : RssSealed s1' := Or.inr (rss_step_release_inv hstep).1
    have hno := (rss_multisession_sealed_absorbing hTail
      (RssSessionTable.set_same _ _ _) hsealed).1 cutp
    have hsame : sidp = sid := hfst.trans heq.symm
    rw [hsame] at hp
    exact hno hp
  | progressed _ _ _ _ ih => exact ih
  | failed _ _ _ ih => exact ih
  | unknown _ _ ih => exact ih

theorem rss_step_round2_accepts (s : rss_cut_session.RssCutGateSession)
    (cut : Array Std.U8 32#usize)
    (hp : s.poisoned = false) (hph : s.phase = .Round1MaskCommitted) :
    rss_cut_session.RssCutGateSession.step s
        (.AdvanceRound2Chi s.session_id s.mask_commitment cut) =
      .ok ({ s with phase := .Round2ChiEvaluated, candidate_cut_bytes := cut,
                    consistency_verified := false }, .Ok .Round2Ready) := by
  simp [rss_cut_session.RssCutGateSession.step,
    rss_cut_session.RssCutGateSession.advance_round2_chi, ct_eq_bytes32_spec, hp, hph]

theorem rss_step_round3_accepts (s : rss_cut_session.RssCutGateSession)
    (hp : s.poisoned = false) (hph : s.phase = .Round2ChiEvaluated) :
    rss_cut_session.RssCutGateSession.step s
        (.AdvanceRound3VerifyConsistency s.session_id 0#u128 0#u128 0#u64) =
      .ok ({ s with phase := .Round3ConsistencyVerified, consistency_verified := true },
           .Ok .Round3Verified) := by
  simp [rss_cut_session.RssCutGateSession.step,
    rss_cut_session.RssCutGateSession.advance_round3_verify_consistency,
    ct_eq_bytes32_spec, hp, hph]

theorem rss_step_round3_rejects_nonzero_residual (s : rss_cut_session.RssCutGateSession)
    (lo hi : Std.U128) (dzk : Std.U64)
    (hp : s.poisoned = false) (hph : s.phase = .Round2ChiEvaluated) (hnz : lo ≠ 0#u128) :
    rss_cut_session.RssCutGateSession.step s
        (.AdvanceRound3VerifyConsistency s.session_id lo hi dzk) =
      .ok ({ session_id := s.session_id, phase := .Poisoned,
             mask_commitment := s.mask_commitment,
             candidate_cut_bytes := Array.repeat 32#usize 0#u8,
             consistency_verified := false, poisoned := true },
           .Err .ConsistencyCheckFailed) := by
  simp [rss_cut_session.RssCutGateSession.step,
    rss_cut_session.RssCutGateSession.advance_round3_verify_consistency,
    rss_cut_session.poison_rss_cut_session, ct_eq_bytes32_spec, hp, hph, hnz]

theorem rss_step_open_accepts (s : rss_cut_session.RssCutGateSession)
    (hp : s.poisoned = false) (hph : s.phase = .Round3ConsistencyVerified)
    (hcv : s.consistency_verified = true) :
    rss_cut_session.RssCutGateSession.step s (.OpenVerifiedCut s.session_id) =
      .ok ({ s with phase := .CutOpened,
                    candidate_cut_bytes := Array.repeat 32#usize 0#u8 },
           .Ok (.CutReleased s.candidate_cut_bytes)) := by
  simp [rss_cut_session.RssCutGateSession.step,
    rss_cut_session.RssCutGateSession.open_verified_cut, ct_eq_bytes32_spec, hp, hph, hcv]

/-- Two honest sessions interleaved both release, and the driver refusing a duplicate
    `init` does not disturb either. -/
theorem rss_multisession_two_sessions_release
    (A B mA mB cutA cutB : Array Std.U8 32#usize) (hne : A ≠ B) :
    ∃ (evs : List RssSessionEvent) (tblF : RssSessionTable),
      RssMultiSessionTrace false (fun _ => none) evs [(A, cutA), (B, cutB)] tblF ∧
      evs.length = 9 := by
  have hA {tbl : RssSessionTable} {x y : rss_cut_session.RssCutGateSession} :
      ((tbl.set A x).set B y) A = some x :=
    (RssSessionTable.set_other _ _ hne).trans (RssSessionTable.set_same _ _ _)
  have hB {tbl : RssSessionTable} {x y : rss_cut_session.RssCutGateSession} :
      ((tbl.set B x).set A y) B = some x :=
    (RssSessionTable.set_other _ _ (Ne.symm hne)).trans (RssSessionTable.set_same _ _ _)
  exact ⟨_, _,
    RssMultiSessionTrace.init_fresh (tbl := fun _ => none) (sid := A) (mask := mA) rfl rfl
    (RssMultiSessionTrace.init_fresh (sid := B) (mask := mB)
      (RssSessionTable.set_other _ _ (Ne.symm hne)) rfl
    (RssMultiSessionTrace.init_refused (sid := A) (mask := mB) rfl hA
    (RssMultiSessionTrace.progressed (sid := A) hA
      (rss_step_round2_accepts _ cutA rfl rfl) (fun c hc => by cases hc)
    (RssMultiSessionTrace.progressed (sid := B) hB
      (rss_step_round2_accepts _ cutB rfl rfl) (fun c hc => by cases hc)
    (RssMultiSessionTrace.progressed (sid := A) hA
      (rss_step_round3_accepts _ rfl rfl) (fun c hc => by cases hc)
    (RssMultiSessionTrace.progressed (sid := B) hB
      (rss_step_round3_accepts _ rfl rfl) (fun c hc => by cases hc)
    (RssMultiSessionTrace.released (sid := A) hA
      (rss_step_open_accepts _ rfl rfl rfl)
    (RssMultiSessionTrace.released (sid := B) hB
      (rss_step_open_accepts _ rfl rfl rfl)
    (RssMultiSessionTrace.nil _))))))))), rfl⟩

/-- Inhabitedness of the multi-session relation and of the hypotheses of
    `rss_multisession_release_at_most_once` with two released cuts. -/
theorem inhabited_rss_multisession_trace :
    ∃ (evs : List RssSessionEvent)
      (rel : List (Array Std.U8 32#usize × Array Std.U8 32#usize)) (tblF : RssSessionTable),
      RssMultiSessionTrace false (fun _ => none) evs rel tblF ∧ rel.length = 2 := by
  have hne : (Array.repeat 32#usize 0x41#u8 : Array Std.U8 32#usize) ≠
      Array.repeat 32#usize 0x42#u8 := by decide
  obtain ⟨evs, tblF, hTr, _⟩ := rss_multisession_two_sessions_release
    (Array.repeat 32#usize 0x41#u8) (Array.repeat 32#usize 0x42#u8)
    (Array.repeat 32#usize 0x51#u8) (Array.repeat 32#usize 0x52#u8)
    (Array.repeat 32#usize 0xA1#u8) (Array.repeat 32#usize 0xB2#u8) hne
  exact ⟨evs, _, tblF, hTr, rfl⟩

/-- `#tooth`: the re-initialisation policy is load-bearing. With `allowReinit := true`
    the hypotheses of `rss_multisession_sticky_poison_absorbency` hold (a session entry,
    a rejected consistency check that poisons it, a continuation trace) and the
    conclusion fails: after the driver overwrites the poisoned entry, the same session
    id releases a cut. `new_round1_committed` has no memory of the poisoned session, so
    the refusal has to live in the driver. -/
theorem tooth_rss_reinit_resets_poison_and_releases
    (A m cut1 cut2 : Array Std.U8 32#usize) :
    ∃ (tbl tblF : RssSessionTable) (s s' : rss_cut_session.RssCutGateSession)
      (inp : rss_cut_session.RssCutStepInput) (e : rss_cut_session.RssCutError)
      (evs : List RssSessionEvent),
      tbl A = some s ∧
      rss_cut_session.RssCutGateSession.step s inp = .ok (s', .Err e) ∧
      s'.poisoned = true ∧
      RssMultiSessionTrace true tbl (.call A inp :: evs) [(A, cut2)] tblF := by
  let s1 : rss_cut_session.RssCutGateSession :=
    { session_id := A, phase := .Round2ChiEvaluated, mask_commitment := m,
      candidate_cut_bytes := cut1, consistency_verified := false, poisoned := false }
  have hrej := rss_step_round3_rejects_nonzero_residual s1 1#u128 0#u128 0#u64 rfl rfl
    (by decide)
  exact ⟨RssSessionTable.set (fun _ => none) A s1, _, s1, _, _, _, _,
    RssSessionTable.set_same _ _ _, hrej, rfl,
    RssMultiSessionTrace.failed (RssSessionTable.set_same _ _ _) hrej
    (RssMultiSessionTrace.init_overwrite (sid := A) (mask := m) rfl
      (RssSessionTable.set_same _ _ _) rfl
    (RssMultiSessionTrace.progressed (sid := A) (RssSessionTable.set_same _ _ _)
      (rss_step_round2_accepts _ cut2 rfl rfl) (fun c hc => by cases hc)
    (RssMultiSessionTrace.progressed (sid := A) (RssSessionTable.set_same _ _ _)
      (rss_step_round3_accepts _ rfl rfl) (fun c hc => by cases hc)
    (RssMultiSessionTrace.released (sid := A) (RssSessionTable.set_same _ _ _)
      (rss_step_open_accepts _ rfl rfl rfl)
    (RssMultiSessionTrace.nil _)))))⟩

/-! ## 4. Authenticated belt guard: pure core of each call -/

theorem u64_val_succ_lt_of_ne_max {x : Std.U64} (hne : x ≠ core.num.U64.MAX) :
    x.val + 1 < 2 ^ 64 := by
  have hlt : x.val < 2 ^ 64 := x.bv.isLt
  have hmax : core.num.U64.MAX.val = 2 ^ 64 - 1 := BitVec.toNat_allOnes
  have hne' : x.val ≠ 2 ^ 64 - 1 :=
    fun hv => hne (UScalar.eq_of_val_eq (hv.trans hmax.symm))
  omega

/-- What the corruption test of the pure belt specification rules out. -/
theorem belt_not_corrupt_facts {s : pants_and_quorum_guards.BeltQuorumCore}
    (h : beltGuardCorrupt s = false) :
    s.poisoned = false ∧
    isBeltPhasePoisoned s.phase = false ∧
    validBeltQuorumConfigBool s.n s.t s.f s.q s.global_liveness_mode = true ∧
    (s.has_bound_epoch = true → s.bound_epoch.val < s.next_epoch.val) := by
  cases hp : s.poisoned <;> cases hph : isBeltPhasePoisoned s.phase <;>
    cases hv : validBeltQuorumConfigBool s.n s.t s.f s.q s.global_liveness_mode <;>
    cases hb : s.has_bound_epoch <;>
    simp [beltGuardCorrupt, hp, hph, hv, hb] at h ⊢ <;> omega

theorem belt_mealy_propose_inv
    {s s' : pants_and_quorum_guards.BeltQuorumCore} {ep : Std.U64}
    {tag : Array Std.U8 32#usize} {walOk : Bool}
    {o : pants_and_quorum_guards.BeltQuorumCoreOutput}
    (h : beltQuorumMealy.step s (.ProposeOrRetryEpoch ep tag walOk) = some (s', o)) :
    beltGuardCorrupt s = false ∧ walOk = true ∧ o = .EpochBound ∧
    ((s.has_bound_epoch = true ∧ ep = s.bound_epoch ∧ s.bound_msg_tag = tag ∧ s' = s) ∨
     (¬ (s.has_bound_epoch = true ∧ ep = s.bound_epoch) ∧
      s.next_epoch.val ≤ ep.val ∧
      ep.val - s.next_epoch.val ≤ s.max_jump_window.val ∧
      ep.val + 1 < 2 ^ 64 ∧
      s' = { s with next_epoch := ⟨ep.bv + (1#u64).bv⟩,
                    phase := .EpochBoundPendingQuorum,
                    has_bound_epoch := true,
                    bound_epoch := ep,
                    bound_msg_tag := tag,
                    ack_count := 0#u32 })) := by
  have h2 := h
  dsimp only [beltQuorumMealy] at h2
  cases hc : beltGuardCorrupt s with
  | true => rw [hc] at h2; simp at h2
  | false =>
    rw [hc] at h2
    simp only [Bool.false_eq_true, ↓reduceIte] at h2
    cases walOk with
    | false => simp at h2
    | true =>
      by_cases hr : s.has_bound_epoch = true ∧ ep = s.bound_epoch
      · by_cases ht : s.bound_msg_tag = tag
        · have hf : beltQuorumMealy.step s (.ProposeOrRetryEpoch ep tag true) =
              some (s, .EpochBound) := by
            dsimp only [beltQuorumMealy]; rw [hc]; simp [hr.1, hr.2, ht]
          rw [hf] at h
          injection h with h
          injection h with h1 h2
          exact ⟨rfl, rfl, h2.symm, Or.inl ⟨hr.1, hr.2, ht, h1.symm⟩⟩
        · simp [hr.1, hr.2, ht] at h2
      · have hr' : (s.has_bound_epoch && decide (ep = s.bound_epoch)) = false := by
          cases hb : s.has_bound_epoch with
          | false => rfl
          | true =>
            have hne : ¬ ep = s.bound_epoch := fun he => hr ⟨hb, he⟩
            simp [hne]
        rw [hr'] at h2
        by_cases hlt : ep.val < s.next_epoch.val
        · simp [hlt] at h2
        · by_cases hw : s.max_jump_window.val < ep.val - s.next_epoch.val
          · simp [hlt, hw] at h2
          · by_cases hmax : ep = core.num.U64.MAX
            · simp [hmax] at h2
            · have hf : beltQuorumMealy.step s (.ProposeOrRetryEpoch ep tag true) =
                  some ({ s with next_epoch := ⟨ep.bv + (1#u64).bv⟩,
                                 phase := .EpochBoundPendingQuorum,
                                 has_bound_epoch := true,
                                 bound_epoch := ep,
                                 bound_msg_tag := tag,
                                 ack_count := 0#u32 }, .EpochBound) := by
                dsimp only [beltQuorumMealy]; rw [hc, hr']; simp [hlt, hw, hmax]
              rw [hf] at h
              injection h with h
              injection h with h1 h2
              exact ⟨rfl, rfl, h2.symm, Or.inr ⟨hr, Nat.le_of_not_lt hlt,
                Nat.le_of_not_lt hw, u64_val_succ_lt_of_ne_max hmax, h1.symm⟩⟩

theorem belt_mealy_ack_inv
    {s s' : pants_and_quorum_guards.BeltQuorumCore} {ackEp : Std.U64}
    {ackTag : Array Std.U8 32#usize}
    {o : pants_and_quorum_guards.BeltQuorumCoreOutput}
    (h : beltQuorumMealy.step s (.RecordCustodianAck ackEp ackTag) = some (s', o)) :
    beltGuardCorrupt s = false ∧ s.has_bound_epoch = true ∧ ackEp = s.bound_epoch ∧
    s.bound_msg_tag = ackTag ∧ s.ack_count.val < s.n.val ∧
    s' = { s with ack_count := ⟨s.ack_count.bv + (1#u32).bv⟩ } ∧
    o = .AckRecorded ⟨s.ack_count.bv + (1#u32).bv⟩ := by
  have h2 := h
  dsimp only [beltQuorumMealy] at h2
  cases hc : beltGuardCorrupt s with
  | true => rw [hc] at h2; simp at h2
  | false =>
    rw [hc] at h2
    simp only [Bool.false_eq_true, ↓reduceIte] at h2
    by_cases hb : s.has_bound_epoch = true
    · by_cases he : ackEp = s.bound_epoch
      · by_cases ht : s.bound_msg_tag = ackTag
        · by_cases hn : s.n.val ≤ s.ack_count.val
          · simp [hb, he, ht, hn] at h2
          · have hf : beltQuorumMealy.step s (.RecordCustodianAck ackEp ackTag) =
                some ({ s with ack_count := ⟨s.ack_count.bv + (1#u32).bv⟩ },
                      .AckRecorded ⟨s.ack_count.bv + (1#u32).bv⟩) := by
              dsimp only [beltQuorumMealy]; rw [hc]; simp [hb, he, ht, hn]
            rw [hf] at h
            injection h with h
            injection h with h1 h2
            exact ⟨rfl, hb, he, ht, Nat.lt_of_not_le hn, h1.symm, h2.symm⟩
        · simp [hb, he, ht] at h2
      · simp [hb, he] at h2
    · simp [hb] at h2

theorem belt_mealy_authorize_inv
    {s s' : pants_and_quorum_guards.BeltQuorumCore} {reqEp : Std.U64}
    {reqTag : Array Std.U8 32#usize}
    {o : pants_and_quorum_guards.BeltQuorumCoreOutput}
    (h : beltQuorumMealy.step s (.AuthorizeShares reqEp reqTag) = some (s', o)) :
    beltGuardCorrupt s = false ∧ s.has_bound_epoch = true ∧ reqEp = s.bound_epoch ∧
    s.bound_msg_tag = reqTag ∧ s.q.val ≤ s.ack_count.val ∧
    s' = { s with phase := .SharesAuthorized } ∧
    o = .SharesAuthorized { _private := (), authorized_epoch := s.bound_epoch,
                            msg_tag := s.bound_msg_tag,
                            certified_acks := s.ack_count } := by
  have h2 := h
  dsimp only [beltQuorumMealy] at h2
  cases hc : beltGuardCorrupt s with
  | true => rw [hc] at h2; simp at h2
  | false =>
    rw [hc] at h2
    simp only [Bool.false_eq_true, ↓reduceIte] at h2
    by_cases hb : s.has_bound_epoch = true
    · by_cases he : reqEp = s.bound_epoch
      · by_cases ht : s.bound_msg_tag = reqTag
        · by_cases hq : s.ack_count.val < s.q.val
          · simp [hb, he, ht, hq] at h2
          · have hphase : s.phase ≠ .SharesAuthorized := by
              intro hp
              simp [hb, he, ht, hq, hp] at h2
            have hf : beltQuorumMealy.step s (.AuthorizeShares reqEp reqTag) =
                some ({ s with phase := .SharesAuthorized },
                      .SharesAuthorized { _private := (), authorized_epoch := s.bound_epoch,
                                          msg_tag := s.bound_msg_tag,
                                          certified_acks := s.ack_count }) := by
              dsimp only [beltQuorumMealy]; rw [hc]
              cases hp : s.phase <;> simp_all
            rw [hf] at h
            injection h with h
            injection h with h1 h2
            exact ⟨rfl, hb, he, ht, Nat.le_of_not_lt hq, h1.symm, h2.symm⟩
        · simp [hb, he, ht] at h2
      · simp [hb, he] at h2
    · simp [hb] at h2

/-- A refused step either leaves an uncorrupted core exactly as it was, or poisons it. -/
theorem belt_mealy_errStep_cases (s : pants_and_quorum_guards.BeltQuorumCore)
    (inp : pants_and_quorum_guards.BeltQuorumCoreInput) :
    (beltQuorumMealy.errStep s inp = s ∧ beltGuardCorrupt s = false) ∨
    beltQuorumMealy.errStep s inp = purePoisonBelt s := by
  dsimp only [beltQuorumMealy]
  cases beltGuardCorrupt s
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases inp with
    | ProposeOrRetryEpoch ep tag walOk =>
      dsimp only
      cases walOk
      · exact Or.inr rfl
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        cases s.has_bound_epoch && decide (ep = s.bound_epoch)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases decide (ep.val < s.next_epoch.val)
          · exact Or.inl ⟨rfl, trivial⟩
          · exact Or.inr rfl
        · simp only [↓reduceIte]
          cases decide (s.bound_msg_tag = tag)
          · exact Or.inr rfl
          · exact Or.inl ⟨rfl, trivial⟩
    | RecordCustodianAck ackEp ackTag =>
      dsimp only
      cases s.has_bound_epoch
      · exact Or.inl ⟨rfl, trivial⟩
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        cases decide (ackEp ≠ s.bound_epoch)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases decide (s.bound_msg_tag = ackTag)
          · exact Or.inr rfl
          · exact Or.inl ⟨rfl, trivial⟩
        · exact Or.inl ⟨rfl, trivial⟩
    | AuthorizeShares reqEp reqTag =>
      dsimp only
      cases s.has_bound_epoch
      · exact Or.inl ⟨rfl, trivial⟩
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        cases decide (reqEp ≠ s.bound_epoch)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases decide (s.bound_msg_tag = reqTag)
          · exact Or.inr rfl
          · exact Or.inl ⟨rfl, trivial⟩
        · exact Or.inl ⟨rfl, trivial⟩
  · exact Or.inr rfl

theorem belt_core_propose_ok_mealy
    {s s' : pants_and_quorum_guards.BeltQuorumCore} {ep : Std.U64}
    {tag : Array Std.U8 32#usize} {walOk : Bool} {u : Unit}
    (h : pants_and_quorum_guards.BeltQuorumCore.propose_or_retry_epoch s ep tag walOk =
      .ok (s', .Ok u)) :
    beltQuorumMealy.step s (.ProposeOrRetryEpoch ep tag walOk) = some (s', .EpochBound) := by
  have hstep : pants_and_quorum_guards.BeltQuorumCore.step s
      (.ProposeOrRetryEpoch ep tag walOk) = .ok (s', .Ok .EpochBound) := by
    unfold pants_and_quorum_guards.BeltQuorumCore.step
    simp only [h, bind_eq_result_bind, result_bind_ok]
  exact mirSim_ok_step_eq belt_quorum_step_sim hstep

theorem belt_core_propose_err_mealy
    {s s' : pants_and_quorum_guards.BeltQuorumCore} {ep : Std.U64}
    {tag : Array Std.U8 32#usize} {walOk : Bool}
    {e : pants_and_quorum_guards.PantsGuardError}
    (h : pants_and_quorum_guards.BeltQuorumCore.propose_or_retry_epoch s ep tag walOk =
      .ok (s', .Err e)) :
    beltQuorumMealy.step s (.ProposeOrRetryEpoch ep tag walOk) = none ∧
    s' = beltQuorumMealy.errStep s (.ProposeOrRetryEpoch ep tag walOk) := by
  have hstep : pants_and_quorum_guards.BeltQuorumCore.step s
      (.ProposeOrRetryEpoch ep tag walOk) = .ok (s', .Err e) := by
    unfold pants_and_quorum_guards.BeltQuorumCore.step
    simp only [h, bind_eq_result_bind, result_bind_ok]
  exact mirSim_err_step_eq belt_quorum_step_sim hstep

theorem belt_core_ack_ok_mealy
    {s s' : pants_and_quorum_guards.BeltQuorumCore} {ep : Std.U64}
    {tag : Array Std.U8 32#usize} {k : Std.U32}
    (h : pants_and_quorum_guards.BeltQuorumCore.record_custodian_ack s ep tag =
      .ok (s', .Ok k)) :
    beltQuorumMealy.step s (.RecordCustodianAck ep tag) = some (s', .AckRecorded k) := by
  have hstep : pants_and_quorum_guards.BeltQuorumCore.step s
      (.RecordCustodianAck ep tag) = .ok (s', .Ok (.AckRecorded k)) := by
    unfold pants_and_quorum_guards.BeltQuorumCore.step
    simp only [h, bind_eq_result_bind, result_bind_ok]
  exact mirSim_ok_step_eq belt_quorum_step_sim hstep

theorem belt_core_ack_err_mealy
    {s s' : pants_and_quorum_guards.BeltQuorumCore} {ep : Std.U64}
    {tag : Array Std.U8 32#usize} {e : pants_and_quorum_guards.PantsGuardError}
    (h : pants_and_quorum_guards.BeltQuorumCore.record_custodian_ack s ep tag =
      .ok (s', .Err e)) :
    beltQuorumMealy.step s (.RecordCustodianAck ep tag) = none ∧
    s' = beltQuorumMealy.errStep s (.RecordCustodianAck ep tag) := by
  have hstep : pants_and_quorum_guards.BeltQuorumCore.step s
      (.RecordCustodianAck ep tag) = .ok (s', .Err e) := by
    unfold pants_and_quorum_guards.BeltQuorumCore.step
    simp only [h, bind_eq_result_bind, result_bind_ok]
  exact mirSim_err_step_eq belt_quorum_step_sim hstep

theorem belt_core_authorize_ok_mealy
    {s s' : pants_and_quorum_guards.BeltQuorumCore} {ep : Std.U64}
    {tag : Array Std.U8 32#usize} {g : pants_and_quorum_guards.BeltAuthorizationGrant}
    (h : pants_and_quorum_guards.BeltQuorumCore.authorize_shares s ep tag =
      .ok (s', .Ok g)) :
    beltQuorumMealy.step s (.AuthorizeShares ep tag) = some (s', .SharesAuthorized g) := by
  have hstep : pants_and_quorum_guards.BeltQuorumCore.step s
      (.AuthorizeShares ep tag) = .ok (s', .Ok (.SharesAuthorized g)) := by
    unfold pants_and_quorum_guards.BeltQuorumCore.step
    simp only [h, bind_eq_result_bind, result_bind_ok]
  exact mirSim_ok_step_eq belt_quorum_step_sim hstep

theorem belt_core_authorize_err_mealy
    {s s' : pants_and_quorum_guards.BeltQuorumCore} {ep : Std.U64}
    {tag : Array Std.U8 32#usize} {e : pants_and_quorum_guards.PantsGuardError}
    (h : pants_and_quorum_guards.BeltQuorumCore.authorize_shares s ep tag =
      .ok (s', .Err e)) :
    beltQuorumMealy.step s (.AuthorizeShares ep tag) = none ∧
    s' = beltQuorumMealy.errStep s (.AuthorizeShares ep tag) := by
  have hstep : pants_and_quorum_guards.BeltQuorumCore.step s
      (.AuthorizeShares ep tag) = .ok (s', .Err e) := by
    unfold pants_and_quorum_guards.BeltQuorumCore.step
    simp only [h, bind_eq_result_bind, result_bind_ok]
  exact mirSim_err_step_eq belt_quorum_step_sim hstep

/-! ## 5. Authenticated belt guard: one call of the wrapper -/

theorem uscalar_cast_val_eq {src : UScalarTy} (dst : UScalarTy) (x : UScalar src)
    (h : x.val < 2 ^ dst.numBits) : (UScalar.cast dst x).val = x.val := by
  change (x.bv.setWidth dst.numBits).toNat = x.bv.toNat
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt h]

theorem u64_succ_val {x : Std.U64} (h : x.val + 1 < 2 ^ 64) :
    (⟨x.bv + (1#u64).bv⟩ : Std.U64).val = x.val + 1 :=
  (BitVec.toNat_add _ _).trans (Nat.mod_eq_of_lt h)

theorem u32_succ_val {x : Std.U32} (h : x.val + 1 < 2 ^ 32) :
    (⟨x.bv + (1#u32).bv⟩ : Std.U32).val = x.val + 1 :=
  (BitVec.toNat_add _ _).trans (Nat.mod_eq_of_lt h)

/-- Bit of custodian `id` in the acknowledgment bitmap, as the wrapper computes it. -/
@[expose]
def beltCustodianBit (id : Std.U8) : Std.U64 := ⟨(1#u64).bv <<< id.val⟩

theorem belt_zero_getLsbD (i : Nat) : (0#u64 : Std.U64).bv.getLsbD i = false :=
  BitVec.getLsbD_zero

theorem beltCustodianBit_getLsbD (id : Std.U8) (hk : id.val < 64) (i : Nat) :
    (beltCustodianBit id).bv.getLsbD i = decide (id.val = i) := by
  show ((1#u64 : Std.U64).bv <<< id.val).getLsbD i = decide (id.val = i)
  rw [BitVec.getLsbD_shiftLeft]
  have h1 : (1#u64 : Std.U64).bv.getLsbD (i - id.val) = decide (0 = i - id.val) := by
    show ((2 : Nat) ^ 0).testBit (i - id.val) = decide (0 = i - id.val)
    exact Nat.testBit_two_pow
  rw [h1]
  by_cases hi : i < 64
  · by_cases hlt : i < id.val
    · have hne : ¬ id.val = i := by omega
      rw [decide_eq_true hi, decide_eq_true hlt, decide_eq_false hne]
      rfl
    · by_cases he : id.val = i
      · have hz : 0 = i - id.val := by omega
        rw [decide_eq_true hi, decide_eq_false hlt, decide_eq_true hz, decide_eq_true he]
        rfl
      · have hz : ¬ 0 = i - id.val := by omega
        rw [decide_eq_true hi, decide_eq_false hlt, decide_eq_false hz, decide_eq_false he]
        rfl
  · have hne : ¬ id.val = i := by omega
    rw [decide_eq_false hi, decide_eq_false hne]
    rfl

theorem beltCustodianBit_and_eq_zero {bm : Std.U64} {id : Std.U8} (hk : id.val < 64)
    (h : bm &&& beltCustodianBit id = 0#u64) : bm.bv.getLsbD id.val = false := by
  have h1 : (bm.bv &&& (beltCustodianBit id).bv).getLsbD id.val =
      (0#u64).bv.getLsbD id.val :=
    congrArg (fun x : Std.U64 => x.bv.getLsbD id.val) h
  rw [BitVec.getLsbD_and, beltCustodianBit_getLsbD id hk, belt_zero_getLsbD,
    decide_eq_true rfl, Bool.and_true] at h1
  exact h1

/-- What a caller observes from one `step`. -/
inductive BeltObs where
  | rejected
  | epochBound
  | ackRecorded
  | granted (g : pants_and_quorum_guards.BeltAuthorizationGrant)

@[expose]
def beltObsOf :
    core.result.Result authenticated_belt.BeltQuorumStepOutput
      authenticated_belt.BeltAuthError → BeltObs
  | .Ok .EpochBound => .epochBound
  | .Ok (.AckRecorded _) => .ackRecorded
  | .Ok (.SharesAuthorized g) => .granted g
  | .Err _ => .rejected

/-- Complete mediation of `VerifiedBeltQuorumGuard::step`: the seven ways a returned
    state can relate to the state before the call. Nothing in it mentions the MAC or
    WAL tags, so it holds whatever the tag functions compute. -/
inductive BeltStepOutcome (st st' : authenticated_belt.VerifiedBeltQuorumGuard) :
    BeltObs → Prop where
  | rejected_unchanged : st' = st → BeltStepOutcome st st' .rejected
  | rejected_poisoned :
      st'.inner = purePoisonBelt st.inner → st'.ack_bitmap = 0#u64 →
      BeltStepOutcome st st' .rejected
  | retried : st' = st → BeltStepOutcome st st' .epochBound
  | bound (ep : Std.U64) (msg : Array Std.U8 32#usize) :
      beltGuardCorrupt st.inner = false →
      ¬ (st.inner.has_bound_epoch = true ∧ ep = st.inner.bound_epoch) →
      st.inner.next_epoch.val ≤ ep.val →
      ep.val + 1 < 2 ^ 64 →
      st' = { st with
              inner := { st.inner with
                         next_epoch := ⟨ep.bv + (1#u64).bv⟩,
                         phase := .EpochBoundPendingQuorum,
                         has_bound_epoch := true,
                         bound_epoch := ep,
                         bound_msg_tag := msg,
                         ack_count := 0#u32 },
              ack_bitmap := 0#u64 } →
      BeltStepOutcome st st' .epochBound
  | duplicate : st' = st → BeltStepOutcome st st' .ackRecorded
  | acked (id : Std.U8) :
      beltGuardCorrupt st.inner = false →
      st.inner.has_bound_epoch = true →
      id.val < st.inner.n.val →
      id.val < 64 →
      st.ack_bitmap.bv.getLsbD id.val = false →
      st.inner.ack_count.val < st.inner.n.val →
      st' = { st with
              inner := { st.inner with
                         ack_count := ⟨st.inner.ack_count.bv + (1#u32).bv⟩ },
              ack_bitmap := st.ack_bitmap ||| beltCustodianBit id } →
      BeltStepOutcome st st' .ackRecorded
  | granted :
      beltGuardCorrupt st.inner = false →
      st.inner.has_bound_epoch = true →
      st.inner.q.val ≤ st.inner.ack_count.val →
      st' = { st with inner := { st.inner with phase := .SharesAuthorized } } →
      BeltStepOutcome st st'
        (.granted { _private := (), authorized_epoch := st.inner.bound_epoch,
                    msg_tag := st.inner.bound_msg_tag,
                    certified_acks := st.inner.ack_count })

@[expose]
def beltObsOfPropose : core.result.Result Unit authenticated_belt.BeltAuthError → BeltObs
  | .Ok _ => .epochBound
  | .Err _ => .rejected

@[expose]
def beltObsOfAck : core.result.Result Std.U32 authenticated_belt.BeltAuthError → BeltObs
  | .Ok _ => .ackRecorded
  | .Err _ => .rejected

@[expose]
def beltObsOfAuthorize :
    core.result.Result pants_and_quorum_guards.BeltAuthorizationGrant
      authenticated_belt.BeltAuthError → BeltObs
  | .Ok g => .granted g
  | .Err _ => .rejected

def authProposeBitmap (st : authenticated_belt.VerifiedBeltQuorumGuard) (ep : Std.U64)
    (inner : pants_and_quorum_guards.BeltQuorumCore)
    (cr : core.result.Result Unit pants_and_quorum_guards.PantsGuardError) : Std.U64 :=
  if inner.poisoned then 0#u64
  else if st.inner.has_bound_epoch && decide (st.inner.bound_epoch = ep) then st.ack_bitmap
  else
    match cr with
    | .Ok _ => 0#u64
    | .Err _ => st.ack_bitmap

def authProposeResult (valid : Bool)
    (cr : core.result.Result Unit pants_and_quorum_guards.PantsGuardError) :
    core.result.Result Unit authenticated_belt.BeltAuthError :=
  if valid then
    match cr with
    | .Ok _ => .Ok ()
    | .Err e => .Err (.Core e)
  else .Err .InvalidWalReceipt

set_option linter.unusedSimpArgs false in
/-- The wrapper's `propose_or_retry_epoch` is the core call under some WAL-validity
    bit, followed by a bitmap update that depends only on the core's answer. -/
theorem auth_belt_propose_peel
    {st st' : authenticated_belt.VerifiedBeltQuorumGuard} {ep : Std.U64}
    {msg rd rt : Array Std.U8 32#usize}
    {r : core.result.Result Unit authenticated_belt.BeltAuthError}
    (h : authenticated_belt.VerifiedBeltQuorumGuard.propose_or_retry_epoch st ep msg rd rt =
      .ok (st', r)) :
    ∃ (valid : Bool) (inner : pants_and_quorum_guards.BeltQuorumCore)
      (cr : core.result.Result Unit pants_and_quorum_guards.PantsGuardError),
      pants_and_quorum_guards.BeltQuorumCore.propose_or_retry_epoch st.inner ep msg valid =
        .ok (inner, cr) ∧
      st' = { st with inner := inner, ack_bitmap := authProposeBitmap st ep inner cr } ∧
      r = authProposeResult valid cr := by
  unfold authenticated_belt.VerifiedBeltQuorumGuard.propose_or_retry_epoch at h
  cases hw : authenticated_belt.wal_receipt_tag st.wal_key st.guard_key_commit ep msg rd with
  | fail e => rw [hw] at h; cases h
  | div => rw [hw] at h; cases h
  | ok expected =>
    rw [hw] at h
    simp only [bind_eq_result_bind, result_bind_ok, ct_eq_bytes32_spec,
      pants_and_quorum_guards.BeltQuorumCore.impl.has_bound_epoch,
      pants_and_quorum_guards.BeltQuorumCore.impl.bound_epoch,
      pants_and_quorum_guards.BeltQuorumCore.is_poisoned] at h
    generalize decide (expected = rt) = valid at h
    cases hcore : pants_and_quorum_guards.BeltQuorumCore.propose_or_retry_epoch
        st.inner ep msg valid with
    | fail e =>
      rw [hcore] at h
      cases hbb : st.inner.has_bound_epoch <;>
        by_cases he : st.inner.bound_epoch = ep <;> (simp [hbb, he] at h; cases h)
    | div =>
      rw [hcore] at h
      cases hbb : st.inner.has_bound_epoch <;>
        by_cases he : st.inner.bound_epoch = ep <;> (simp [hbb, he] at h; cases h)
    | ok p =>
      rcases p with ⟨inner, cr⟩
      rw [hcore] at h
      refine ⟨valid, inner, cr, hcore, ?_⟩
      cases cr <;> cases hpz : inner.poisoned <;> cases hbb : st.inner.has_bound_epoch <;>
        by_cases he : st.inner.bound_epoch = ep <;> cases valid <;>
        (simp [hpz, hbb, he] at h
         obtain ⟨rfl, rfl⟩ := h
         simp [authProposeBitmap, authProposeResult, hpz, hbb, he])

theorem auth_belt_propose_outcome
    {st st' : authenticated_belt.VerifiedBeltQuorumGuard} {ep : Std.U64}
    {msg rd rt : Array Std.U8 32#usize}
    {r : core.result.Result Unit authenticated_belt.BeltAuthError}
    (h : authenticated_belt.VerifiedBeltQuorumGuard.propose_or_retry_epoch st ep msg rd rt =
      .ok (st', r)) :
    BeltStepOutcome st st' (beltObsOfPropose r) := by
  obtain ⟨valid, inner, cr, hcore, hst, hr⟩ := auth_belt_propose_peel h
  subst hst; subst hr
  cases cr with
  | Ok u =>
    obtain ⟨hc, hval, _, hcase⟩ := belt_mealy_propose_inv (belt_core_propose_ok_mealy hcore)
    subst hval
    have hp := (belt_not_corrupt_facts hc).1
    rcases hcase with ⟨hb, he, _, hin⟩ | ⟨hnr, hge, _, hlt, hin⟩
    · subst hin
      have hbm : authProposeBitmap st ep st.inner (.Ok u) = st.ack_bitmap := by
        simp [authProposeBitmap, hp, hb, he]
      rw [hbm]
      exact .retried rfl
    · have hpi : inner.poisoned = false := by rw [hin]; exact hp
      have hsame : (st.inner.has_bound_epoch && decide (st.inner.bound_epoch = ep)) = false := by
        cases hb : st.inner.has_bound_epoch with
        | false => rfl
        | true =>
          have hne : ¬ st.inner.bound_epoch = ep := fun he => hnr ⟨hb, he.symm⟩
          simp [hne]
      have hbm : authProposeBitmap st ep inner (.Ok u) = 0#u64 := by
        simp [authProposeBitmap, hpi, hsame]
      rw [hbm]
      exact .bound ep msg hc hnr hge hlt (by rw [hin])
  | Err e =>
    obtain ⟨_, hin⟩ := belt_core_propose_err_mealy hcore
    have hres : ∃ e', authProposeResult valid (.Err e) = .Err e' := by
      cases valid <;> exact ⟨_, rfl⟩
    obtain ⟨e', he'⟩ := hres
    rw [he']
    rcases belt_mealy_errStep_cases st.inner (.ProposeOrRetryEpoch ep msg valid) with
      ⟨hsame, hc⟩ | hpois
    · rw [hsame] at hin
      subst hin
      have hp := (belt_not_corrupt_facts hc).1
      have hbm : authProposeBitmap st ep st.inner (.Err e) = st.ack_bitmap := by
        simp [authProposeBitmap, hp]
      rw [hbm]
      exact .rejected_unchanged rfl
    · rw [hpois] at hin
      have hbm : authProposeBitmap st ep inner (.Err e) = 0#u64 := by
        simp [authProposeBitmap, hin]
      rw [hbm]
      exact .rejected_poisoned hin rfl

theorem belt_mealy_errStep_ack_mismatch (s : pants_and_quorum_guards.BeltQuorumCore)
    (ep : Std.U64) (tag : Array Std.U8 32#usize)
    (hb : s.has_bound_epoch = true) (he : ep = s.bound_epoch) (hne : s.bound_msg_tag ≠ tag) :
    beltQuorumMealy.errStep s (.RecordCustodianAck ep tag) = purePoisonBelt s := by
  dsimp only [beltQuorumMealy]
  cases beltGuardCorrupt s
  · simp only [Bool.false_eq_true, ↓reduceIte]
    simp [hb, he, hne]
  · rfl

theorem auth_belt_ack_outcome
    {st st' : authenticated_belt.VerifiedBeltQuorumGuard} {ep : Std.U64}
    {msg tag : Array Std.U8 32#usize} {id : Std.U8}
    {r : core.result.Result Std.U32 authenticated_belt.BeltAuthError}
    (h : authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack st ep msg id tag =
      .ok (st', r)) :
    BeltStepOutcome st st' (beltObsOfAck r) := by
  unfold authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack at h
  simp only [pants_and_quorum_guards.BeltQuorumCore.impl.n,
    pants_and_quorum_guards.BeltQuorumCore.is_poisoned,
    pants_and_quorum_guards.BeltQuorumCore.impl.has_bound_epoch,
    pants_and_quorum_guards.BeltQuorumCore.impl.bound_epoch,
    pants_and_quorum_guards.BeltQuorumCore.impl.bound_msg_tag,
    pants_and_quorum_guards.BeltQuorumCore.impl.ack_count,
    ct_eq_bytes32_spec, hShlU_uscalar_eq,
    bind_eq_result_bind, result_bind_ok, lift_eq_ok] at h
  split at h
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok.inj h)
    exact .rejected_unchanged rfl
  · rename_i hin
    split at h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok.inj h)
      exact .rejected_unchanged rfl
    · cases hkey : Array.index_usize st.custodian_keys (UScalar.cast .Usize id) with
      | fail e => rw [hkey] at h; cases h
      | div => rw [hkey] at h; cases h
      | ok key =>
        rw [hkey] at h
        simp only [result_bind_ok] at h
        cases htag : authenticated_belt.custodian_ack_tag key st.guard_key_commit ep msg id with
        | fail e => rw [htag] at h; cases h
        | div => rw [htag] at h; cases h
        | ok expected =>
          rw [htag] at h
          simp only [result_bind_ok] at h
          split at h
          · split at h
            · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok.inj h)
              exact .rejected_unchanged rfl
            · split at h
              · rename_i hb
                split at h
                · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok.inj h)
                  exact .rejected_unchanged rfl
                · rename_i hne
                  have he : ep = st.inner.bound_epoch :=
                    Decidable.byContradiction (fun hx => hne (bne_iff_ne.mpr hx))
                  split at h
                  · split at h
                    · rename_i hlt
                      simp only [result_bind_ok] at h
                      split at h
                      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok.inj h)
                        exact .duplicate rfl
                      · rename_i hused
                        have hz : st.ack_bitmap &&& beltCustodianBit id = 0#u64 :=
                          Decidable.byContradiction (fun hx => hused (bne_iff_ne.mpr hx))
                        cases hcore : pants_and_quorum_guards.BeltQuorumCore.record_custodian_ack
                            st.inner ep msg with
                        | fail e => rw [hcore] at h; cases h
                        | div => rw [hcore] at h; cases h
                        | ok p =>
                          rcases p with ⟨inner, cr⟩
                          rw [hcore] at h
                          cases cr with
                          | Ok k =>
                            simp only [result_bind_ok] at h
                            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok.inj h)
                            obtain ⟨hc, _, _, _, hcnt, hin2, _⟩ :=
                              belt_mealy_ack_inv (belt_core_ack_ok_mealy hcore)
                            have hidn : id.val < st.inner.n.val := by
                              have hc1 : (UScalar.cast .Usize id).val = id.val :=
                                uscalar_cast_val_eq .Usize id
                                  (Nat.lt_of_lt_of_le id.bv.isLt (by decide))
                              have hc2 : (UScalar.cast .Usize st.inner.n).val = st.inner.n.val :=
                                uscalar_cast_val_eq .Usize st.inner.n
                                  (Nat.lt_of_lt_of_le st.inner.n.bv.isLt (by decide))
                              have hnle : ¬ (UScalar.cast .Usize st.inner.n).val ≤
                                  (UScalar.cast .Usize id).val :=
                                fun hle => hin ((UScalar.le_iff_val _ _).mpr hle)
                              omega
                            exact .acked id hc hb hidn hlt
                              (beltCustodianBit_and_eq_zero hlt hz) hcnt (by rw [hin2]; rfl)
                          | Err e =>
                            simp only [result_bind_ok] at h
                            obtain ⟨_, hin2⟩ := belt_core_ack_err_mealy hcore
                            rcases belt_mealy_errStep_cases st.inner
                                (.RecordCustodianAck ep msg) with ⟨hsame, hc⟩ | hpois
                            · rw [hsame] at hin2
                              subst hin2
                              have hp := (belt_not_corrupt_facts hc).1
                              simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
                              obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok.inj h)
                              exact .rejected_unchanged rfl
                            · rw [hpois] at hin2
                              subst hin2
                              simp only [purePoisonBelt, ↓reduceIte] at h
                              obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok.inj h)
                              exact .rejected_poisoned rfl rfl
                    · cases h
                  · rename_i hm
                    have hmne : st.inner.bound_msg_tag ≠ msg :=
                      fun heq => hm (decide_eq_true heq.symm)
                    cases hcore : pants_and_quorum_guards.BeltQuorumCore.record_custodian_ack
                        st.inner ep msg with
                    | fail e => rw [hcore] at h; cases h
                    | div => rw [hcore] at h; cases h
                    | ok p =>
                      rcases p with ⟨inner, cr⟩
                      rw [hcore] at h
                      cases cr with
                      | Ok k =>
                        obtain ⟨_, _, _, htagEq, _⟩ :=
                          belt_mealy_ack_inv (belt_core_ack_ok_mealy hcore)
                        exact absurd htagEq hmne
                      | Err e =>
                        simp only [result_bind_ok] at h
                        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok.inj h)
                        obtain ⟨_, hin2⟩ := belt_core_ack_err_mealy hcore
                        exact .rejected_poisoned
                          (hin2.trans (belt_mealy_errStep_ack_mismatch _ _ _ hb he hmne)) rfl
              · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok.inj h)
                exact .rejected_unchanged rfl
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok.inj h)
            exact .rejected_unchanged rfl

theorem auth_belt_authorize_outcome
    {st st' : authenticated_belt.VerifiedBeltQuorumGuard} {ep : Std.U64}
    {msg : Array Std.U8 32#usize}
    {r : core.result.Result pants_and_quorum_guards.BeltAuthorizationGrant
      authenticated_belt.BeltAuthError}
    (h : authenticated_belt.VerifiedBeltQuorumGuard.authorize_shares st ep msg = .ok (st', r)) :
    BeltStepOutcome st st' (beltObsOfAuthorize r) := by
  unfold authenticated_belt.VerifiedBeltQuorumGuard.authorize_shares at h
  cases hcore : pants_and_quorum_guards.BeltQuorumCore.authorize_shares st.inner ep msg with
  | fail e => rw [hcore] at h; cases h
  | div => rw [hcore] at h; cases h
  | ok p =>
    rcases p with ⟨inner, cr⟩
    rw [hcore] at h
    cases cr with
    | Ok g =>
      obtain ⟨hc, hb, _, _, hq, hin, hg⟩ :=
        belt_mealy_authorize_inv (belt_core_authorize_ok_mealy hcore)
      have hp := (belt_not_corrupt_facts hc).1
      subst hin
      injection hg with hg
      subst hg
      simp only [bind_eq_result_bind, result_bind_ok,
        pants_and_quorum_guards.BeltQuorumCore.is_poisoned, hp, Bool.false_eq_true,
        ↓reduceIte] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok.inj h)
      exact .granted hc hb hq (by simp [hp])
    | Err e =>
      obtain ⟨_, hin⟩ := belt_core_authorize_err_mealy hcore
      rcases belt_mealy_errStep_cases st.inner (.AuthorizeShares ep msg) with
        ⟨hsame, hc⟩ | hpois
      · rw [hsame] at hin
        subst hin
        have hp := (belt_not_corrupt_facts hc).1
        simp only [bind_eq_result_bind, result_bind_ok,
          pants_and_quorum_guards.BeltQuorumCore.is_poisoned, hp, Bool.false_eq_true,
          ↓reduceIte] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok.inj h)
        exact .rejected_unchanged rfl
      · rw [hpois] at hin
        subst hin
        simp only [bind_eq_result_bind, result_bind_ok,
          pants_and_quorum_guards.BeltQuorumCore.is_poisoned, purePoisonBelt,
          ↓reduceIte] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok.inj h)
        exact .rejected_poisoned rfl rfl

/-- **Complete mediation of the authenticated belt guard.** Every returned call of the
    extracted `step` is one of the `BeltStepOutcome` cases. -/
theorem belt_step_outcome
    {st st' : authenticated_belt.VerifiedBeltQuorumGuard}
    {a : authenticated_belt.BeltQuorumStepInput}
    {res : core.result.Result authenticated_belt.BeltQuorumStepOutput
      authenticated_belt.BeltAuthError}
    (h : authenticated_belt.VerifiedBeltQuorumGuard.step st a = .ok (st', res)) :
    BeltStepOutcome st st' (beltObsOf res) := by
  unfold authenticated_belt.VerifiedBeltQuorumGuard.step at h
  cases a with
  | ProposeOrRetryEpoch ep msg rd rt =>
    dsimp only at h
    cases hf : authenticated_belt.VerifiedBeltQuorumGuard.propose_or_retry_epoch
        st ep msg rd rt with
    | fail e => rw [hf] at h; cases h
    | div => rw [hf] at h; cases h
    | ok p =>
      rcases p with ⟨nx, r⟩
      rw [hf] at h
      have ho := auth_belt_propose_outcome hf
      cases r <;>
        (simp only [bind_eq_result_bind, result_bind_ok] at h
         obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok.inj h)
         exact ho)
  | RecordCustodianAck ep msg id tag =>
    dsimp only at h
    cases hf : authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack
        st ep msg id tag with
    | fail e => rw [hf] at h; cases h
    | div => rw [hf] at h; cases h
    | ok p =>
      rcases p with ⟨nx, r⟩
      rw [hf] at h
      have ho := auth_belt_ack_outcome hf
      cases r <;>
        (simp only [bind_eq_result_bind, result_bind_ok] at h
         obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok.inj h)
         exact ho)
  | AuthorizeShares ep msg =>
    dsimp only at h
    cases hf : authenticated_belt.VerifiedBeltQuorumGuard.authorize_shares st ep msg with
    | fail e => rw [hf] at h; cases h
    | div => rw [hf] at h; cases h
    | ok p =>
      rcases p with ⟨nx, r⟩
      rw [hf] at h
      have ho := auth_belt_authorize_outcome hf
      cases r <;>
        (simp only [bind_eq_result_bind, result_bind_ok] at h
         obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok.inj h)
         exact ho)

/-! ## 6. Signer sets: counting distinct custodians -/

/-- Number of custodians whose bit is set in a 64-bit acknowledgment bitmap. -/
@[expose]
def beltPopcount (bm : Std.U64) : Nat :=
  (List.range 64).countP (fun i => bm.bv.getLsbD i)

theorem beltAckCountInvariant_iff (st : authenticated_belt.VerifiedBeltQuorumGuard) :
    BeltAckCountInvariant st ↔ st.inner.ack_count.val = beltPopcount st.ack_bitmap :=
  Iff.rfl

theorem belt_zero_count_popcount : (0#u32 : Std.U32).val = beltPopcount 0#u64 := by decide

theorem countP_range_or_single (f : Nat → Bool) (k : Nat) (hf : f k = false) :
    ∀ n, k < n →
      (List.range n).countP (fun i => f i || decide (k = i)) =
        (List.range n).countP f + 1 := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro hk
    rw [List.range_succ, List.countP_append, List.countP_append]
    by_cases hkn : k < n
    · have hne : ¬ k = n := by omega
      rw [ih hkn]
      cases hfn : f n <;> simp [hfn, hne] <;> omega
    · have hkeq : k = n := by omega
      subst hkeq
      have hsame : (List.range k).countP (fun i => f i || decide (k = i)) =
          (List.range k).countP f := by
        apply List.countP_congr
        intro x hx
        have hxk : ¬ k = x := by
          have := List.mem_range.mp hx
          omega
        simp [hxk]
      rw [hsame]
      simp [hf]

theorem countP_inter_union (p q : Nat → Bool) (l : List Nat) :
    l.countP p + l.countP q =
      l.countP (fun i => p i && q i) + l.countP (fun i => p i || q i) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.countP_cons]
    cases p a <;> cases q a <;> simp <;> omega

theorem countP_range_le_of_bounded (r : Nat → Bool) (n : Nat)
    (hr : ∀ i, r i = true → i < n) :
    ∀ m, (List.range m).countP r ≤ n ∧ (List.range m).countP r ≤ m := by
  intro m
  induction m with
  | zero => exact ⟨Nat.zero_le _, Nat.le_refl _⟩
  | succ m ih =>
    rw [List.range_succ, List.countP_append]
    cases hrm : r m with
    | false =>
      have h0 : [m].countP r = 0 := by
        rw [List.countP_cons, hrm]; rfl
      rw [h0]
      exact ⟨ih.1, Nat.le_succ_of_le ih.2⟩
    | true =>
      have hmn := hr m hrm
      have h1 : [m].countP r = 1 := by
        rw [List.countP_cons, hrm]; rfl
      rw [h1]
      exact ⟨Nat.lt_of_le_of_lt ih.2 hmn, Nat.succ_le_succ ih.2⟩

theorem beltPopcount_or_bit (bm : Std.U64) (id : Std.U8) (hk : id.val < 64)
    (hf : bm.bv.getLsbD id.val = false) :
    beltPopcount (bm ||| beltCustodianBit id) = beltPopcount bm + 1 := by
  unfold beltPopcount
  have hfun : (fun i => (bm ||| beltCustodianBit id).bv.getLsbD i) =
      (fun i => bm.bv.getLsbD i || decide (id.val = i)) := by
    funext i
    show (bm.bv ||| (beltCustodianBit id).bv).getLsbD i = _
    rw [BitVec.getLsbD_or, beltCustodianBit_getLsbD id hk]
  rw [hfun]
  exact countP_range_or_single (fun i => bm.bv.getLsbD i) id.val hf 64 hk

theorem belt_or_bit_getLsbD_true {bm : Std.U64} {id : Std.U8} (hk : id.val < 64) {i : Nat}
    (h : (bm ||| beltCustodianBit id).bv.getLsbD i = true) :
    bm.bv.getLsbD i = true ∨ i = id.val := by
  have h1 : (bm.bv ||| (beltCustodianBit id).bv).getLsbD i = true := h
  rw [BitVec.getLsbD_or, beltCustodianBit_getLsbD id hk] at h1
  cases hb : bm.bv.getLsbD i with
  | true => exact Or.inl rfl
  | false =>
    rw [hb, Bool.false_or] at h1
    exact Or.inr (of_decide_eq_true h1).symm

/-- Two signer sets drawn from `n` custodians overlap in at least
    `|a| + |b| - n` custodians. -/
theorem beltPopcount_inter_ge (a b : Std.U64) (n : Nat)
    (ha : ∀ i, a.bv.getLsbD i = true → i < n) (hb : ∀ i, b.bv.getLsbD i = true → i < n) :
    beltPopcount a + beltPopcount b ≤ beltPopcount (a &&& b) + n := by
  have hie : beltPopcount a + beltPopcount b =
      (List.range 64).countP (fun i => a.bv.getLsbD i && b.bv.getLsbD i) +
      (List.range 64).countP (fun i => a.bv.getLsbD i || b.bv.getLsbD i) :=
    countP_inter_union _ _ _
  have hun : (List.range 64).countP (fun i => a.bv.getLsbD i || b.bv.getLsbD i) ≤ n :=
    (countP_range_le_of_bounded (fun i => a.bv.getLsbD i || b.bv.getLsbD i) n (by
      intro i hi
      cases hai : a.bv.getLsbD i with
      | true => exact ha i hai
      | false =>
        rw [hai, Bool.false_or] at hi
        exact hb i hi) 64).1
  have hand : beltPopcount (a &&& b) =
      (List.range 64).countP (fun i => a.bv.getLsbD i && b.bv.getLsbD i) := by
    show (List.range 64).countP (fun i => (a.bv &&& b.bv).getLsbD i) = _
    congr 1
    funext i
    exact BitVec.getLsbD_and
  omega

/-! ## 7. Authenticated belt guard: traces, fork-freedom, quorum intersection -/

/-- Signer-set invariant of the authenticated guard: the core's acknowledgment counter
    is the number of set bitmap bits, and only custodians below `n` are ever set. -/
@[expose]
def BeltGuardInv (n q : Std.U32) (st : authenticated_belt.VerifiedBeltQuorumGuard) : Prop :=
  st.inner.n = n ∧ st.inner.q = q ∧
  st.inner.ack_count.val = beltPopcount st.ack_bitmap ∧
  (∀ i, st.ack_bitmap.bv.getLsbD i = true → i < n.val)

/-- Every call preserves the signer-set invariant, whether it was accepted, refused
    without effect, or refused with poisoning. -/
theorem belt_outcome_preserves_inv {n q : Std.U32}
    {st st' : authenticated_belt.VerifiedBeltQuorumGuard} {obs : BeltObs}
    (hinv : BeltGuardInv n q st) (ho : BeltStepOutcome st st' obs) :
    BeltGuardInv n q st' := by
  obtain ⟨hn, hq, hcnt, hbits⟩ := hinv
  cases ho with
  | rejected_unchanged h => subst h; exact ⟨hn, hq, hcnt, hbits⟩
  | rejected_poisoned h1 h2 =>
    have e1 : st'.inner.ack_count = 0#u32 :=
      congrArg pants_and_quorum_guards.BeltQuorumCore.ack_count h1
    have e2 : st'.inner.n = st.inner.n :=
      (congrArg pants_and_quorum_guards.BeltQuorumCore.n h1).trans rfl
    have e3 : st'.inner.q = st.inner.q :=
      (congrArg pants_and_quorum_guards.BeltQuorumCore.q h1).trans rfl
    refine ⟨e2.trans hn, e3.trans hq, ?_, ?_⟩
    · rw [e1, h2]; exact belt_zero_count_popcount
    · intro i hi
      rw [h2, belt_zero_getLsbD] at hi
      cases hi
  | retried h => subst h; exact ⟨hn, hq, hcnt, hbits⟩
  | bound ep msg hc hnr hge hlt h =>
    subst h
    refine ⟨hn, hq, belt_zero_count_popcount, ?_⟩
    intro i hi
    have hi' : (0#u64 : Std.U64).bv.getLsbD i = true := hi
    rw [belt_zero_getLsbD] at hi'
    cases hi'
  | duplicate h => subst h; exact ⟨hn, hq, hcnt, hbits⟩
  | acked id hc hb hidn h64 hbit hcount h =>
    subst h
    refine ⟨hn, hq, ?_, ?_⟩
    · show (⟨st.inner.ack_count.bv + (1#u32).bv⟩ : Std.U32).val =
        beltPopcount (st.ack_bitmap ||| beltCustodianBit id)
      have h2 : st.inner.n.val < 2 ^ 32 := st.inner.n.bv.isLt
      have hlt32 : st.inner.ack_count.val + 1 < 2 ^ 32 := by omega
      rw [u32_succ_val hlt32, beltPopcount_or_bit _ _ h64 hbit, hcnt]
    · intro i hi
      rcases belt_or_bit_getLsbD_true h64 hi with h1 | h1
      · exact hbits i h1
      · rw [h1, ← hn]; exact hidn
  | granted hc hb hq' h => subst h; exact ⟨hn, hq, hcnt, hbits⟩

/-- How one call moves the epoch binding: it keeps `(bound_epoch, bound_msg_tag,
    next_epoch)`, or it binds a fresh epoch at or above the previous `next_epoch`. -/
theorem belt_outcome_binding
    {st st' : authenticated_belt.VerifiedBeltQuorumGuard} {obs : BeltObs}
    (ho : BeltStepOutcome st st' obs) :
    (st'.inner.has_bound_epoch = st.inner.has_bound_epoch ∧
      st'.inner.bound_epoch = st.inner.bound_epoch ∧
      st'.inner.bound_msg_tag = st.inner.bound_msg_tag ∧
      st'.inner.next_epoch = st.inner.next_epoch) ∨
    (st'.inner.has_bound_epoch = true ∧
      st.inner.next_epoch.val ≤ st'.inner.bound_epoch.val ∧
      st'.inner.bound_epoch.val < st'.inner.next_epoch.val) := by
  cases ho with
  | rejected_unchanged h => subst h; exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
  | rejected_poisoned h1 h2 => rw [h1]; exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
  | retried h => subst h; exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
  | bound ep msg hc hnr hge hlt h =>
    subst h
    refine Or.inr ⟨rfl, hge, ?_⟩
    show ep.val < (⟨ep.bv + (1#u64).bv⟩ : Std.U64).val
    rw [u64_succ_val hlt]
    exact Nat.lt_succ_self _
  | duplicate h => subst h; exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
  | acked id hc hb hidn h64 hbit hcount h => subst h; exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
  | granted hc hb hq h => subst h; exact Or.inl ⟨rfl, rfl, rfl, rfl⟩

theorem belt_outcome_granted_inv
    {st st' : authenticated_belt.VerifiedBeltQuorumGuard}
    {g : pants_and_quorum_guards.BeltAuthorizationGrant}
    (ho : BeltStepOutcome st st' (.granted g)) :
    beltGuardCorrupt st.inner = false ∧
    st.inner.has_bound_epoch = true ∧
    g.authorized_epoch = st.inner.bound_epoch ∧
    g.msg_tag = st.inner.bound_msg_tag ∧
    g.certified_acks = st.inner.ack_count ∧
    st.inner.q.val ≤ st.inner.ack_count.val ∧
    st'.ack_bitmap = st.ack_bitmap := by
  cases ho with
  | granted hc hb hq h => subst h; exact ⟨hc, hb, rfl, rfl, rfl, hq, rfl⟩

/-- A quorum certificate as a caller sees it: the grant returned by `step`, together
    with the signer bitmap the guard held when it issued the grant. -/
structure BeltCert where
  grant : pants_and_quorum_guards.BeltAuthorizationGrant
  signers : Std.U64

abbrev BeltAction := authenticated_belt.BeltQuorumStepInput

/-- Executions of `VerifiedBeltQuorumGuard::step` on arbitrary inputs: epoch proposals
    and retries, acknowledgments in any order and with any repetition, authorization
    requests, replays, and refused calls. The third index lists the certificates
    issued, oldest first. -/
inductive BeltTraceReachable :
    authenticated_belt.VerifiedBeltQuorumGuard → List BeltAction → List BeltCert →
    authenticated_belt.VerifiedBeltQuorumGuard → Prop where
  | nil (st : authenticated_belt.VerifiedBeltQuorumGuard) : BeltTraceReachable st [] [] st
  | bound {st st' stF : authenticated_belt.VerifiedBeltQuorumGuard} {a : BeltAction}
      {acts : List BeltAction} {certs : List BeltCert} :
      authenticated_belt.VerifiedBeltQuorumGuard.step st a = .ok (st', .Ok .EpochBound) →
      BeltTraceReachable st' acts certs stF →
      BeltTraceReachable st (a :: acts) certs stF
  | acked {st st' stF : authenticated_belt.VerifiedBeltQuorumGuard} {a : BeltAction}
      {acts : List BeltAction} {certs : List BeltCert} {k : Std.U32} :
      authenticated_belt.VerifiedBeltQuorumGuard.step st a = .ok (st', .Ok (.AckRecorded k)) →
      BeltTraceReachable st' acts certs stF →
      BeltTraceReachable st (a :: acts) certs stF
  | certified {st st' stF : authenticated_belt.VerifiedBeltQuorumGuard} {a : BeltAction}
      {acts : List BeltAction} {certs : List BeltCert}
      {g : pants_and_quorum_guards.BeltAuthorizationGrant} :
      authenticated_belt.VerifiedBeltQuorumGuard.step st a =
        .ok (st', .Ok (.SharesAuthorized g)) →
      BeltTraceReachable st' acts certs stF →
      BeltTraceReachable st (a :: acts) (⟨g, st'.ack_bitmap⟩ :: certs) stF
  | failed {st st' stF : authenticated_belt.VerifiedBeltQuorumGuard} {a : BeltAction}
      {acts : List BeltAction} {certs : List BeltCert}
      {e : authenticated_belt.BeltAuthError} :
      authenticated_belt.VerifiedBeltQuorumGuard.step st a = .ok (st', .Err e) →
      BeltTraceReachable st' acts certs stF →
      BeltTraceReachable st (a :: acts) certs stF

/-- A refused call leaves the guard exactly as it was, or poisons the core and clears
    the signer bitmap. It never advances an epoch and never adds a signer. -/
theorem belt_failed_call_unchanged_or_poisoned
    {st st' : authenticated_belt.VerifiedBeltQuorumGuard} {a : BeltAction}
    {e : authenticated_belt.BeltAuthError}
    (h : authenticated_belt.VerifiedBeltQuorumGuard.step st a = .ok (st', .Err e)) :
    st' = st ∨ (st'.inner = purePoisonBelt st.inner ∧ st'.ack_bitmap = 0#u64) := by
  have ho : BeltStepOutcome st st' .rejected := belt_step_outcome h
  cases ho with
  | rejected_unchanged h1 => exact Or.inl h1
  | rejected_poisoned h1 h2 => exact Or.inr ⟨h1, h2⟩

/-- Where a certificate can sit relative to a guard state: it certifies the state's
    current binding, or its epoch is at or above the state's `next_epoch`. -/
@[expose]
def BeltCertAhead (st : authenticated_belt.VerifiedBeltQuorumGuard) (c : BeltCert) : Prop :=
  (st.inner.has_bound_epoch = true ∧
    c.grant.authorized_epoch = st.inner.bound_epoch ∧
    c.grant.msg_tag = st.inner.bound_msg_tag) ∨
  st.inner.next_epoch.val ≤ c.grant.authorized_epoch.val

theorem belt_cert_ahead_transfer
    {st st' : authenticated_belt.VerifiedBeltQuorumGuard} {obs : BeltObs}
    (ho : BeltStepOutcome st st' obs) {c : BeltCert} (h : BeltCertAhead st' c) :
    BeltCertAhead st c := by
  rcases belt_outcome_binding ho with ⟨hb, he, ht, hn⟩ | ⟨hb, hge, hlt⟩
  · rcases h with ⟨h1, h2, h3⟩ | h4
    · exact Or.inl ⟨hb.symm.trans h1, h2.trans he, h3.trans ht⟩
    · rw [hn] at h4
      exact Or.inr h4
  · rcases h with ⟨h1, h2, h3⟩ | h4
    · refine Or.inr ?_
      rw [h2]
      exact hge
    · exact Or.inr (by omega)

theorem belt_trace_certs_ahead
    {st stF : authenticated_belt.VerifiedBeltQuorumGuard} {acts : List BeltAction}
    {certs : List BeltCert} (hTr : BeltTraceReachable st acts certs stF) :
    ∀ c ∈ certs, BeltCertAhead st c := by
  induction hTr with
  | nil st => intro c hc; exact False.elim (List.not_mem_nil hc)
  | bound h _ ih =>
    intro c hc
    exact belt_cert_ahead_transfer (belt_step_outcome h) (ih c hc)
  | acked h _ ih =>
    intro c hc
    exact belt_cert_ahead_transfer (belt_step_outcome h) (ih c hc)
  | @certified st st' stF a acts certs g h _ ih =>
    intro c hc
    have ho : BeltStepOutcome st st' (.granted g) := belt_step_outcome h
    rcases List.mem_cons.mp hc with rfl | hc
    · obtain ⟨_, hb, hep, htag, _⟩ := belt_outcome_granted_inv ho
      exact Or.inl ⟨hb, hep, htag⟩
    · exact belt_cert_ahead_transfer ho (ih c hc)
  | failed h _ ih =>
    intro c hc
    exact belt_cert_ahead_transfer (belt_step_outcome h) (ih c hc)

/-- **Epoch monotonicity and fork-freedom along a trace.** For certificates in issue
    order, a later certificate has a strictly larger epoch, or it has the same epoch
    and the same message. From any starting state. -/
theorem belt_trace_certs_monotone
    {st stF : authenticated_belt.VerifiedBeltQuorumGuard} {acts : List BeltAction}
    {certs : List BeltCert} (hTr : BeltTraceReachable st acts certs stF) :
    certs.Pairwise (fun c1 c2 =>
      c1.grant.authorized_epoch.val < c2.grant.authorized_epoch.val ∨
      (c1.grant.authorized_epoch = c2.grant.authorized_epoch ∧
        c1.grant.msg_tag = c2.grant.msg_tag)) := by
  induction hTr with
  | nil st => exact List.Pairwise.nil
  | bound _ _ ih => exact ih
  | acked _ _ ih => exact ih
  | @certified st st' stF a acts certs g h hTail ih =>
    refine List.Pairwise.cons ?_ ih
    intro c2 hc2
    have ho : BeltStepOutcome st st' (.granted g) := belt_step_outcome h
    obtain ⟨hc, hb, hep, htag, _⟩ := belt_outcome_granted_inv ho
    have hlt := (belt_not_corrupt_facts hc).2.2.2 hb
    rcases belt_cert_ahead_transfer ho (belt_trace_certs_ahead hTail c2 hc2) with
      ⟨_, h2, h3⟩ | h4
    · exact Or.inr ⟨hep.trans h2.symm, htag.trans h3.symm⟩
    · refine Or.inl ?_
      show g.authorized_epoch.val < c2.grant.authorized_epoch.val
      rw [hep]
      omega
  | failed _ _ ih => exact ih

theorem pairwise_mem_cases {α : Type} {R : α → α → Prop} :
    ∀ {l : List α}, l.Pairwise R → ∀ a ∈ l, ∀ b ∈ l, a = b ∨ R a b ∨ R b a
  | [], _, a, ha, _, _ => (List.not_mem_nil ha).elim
  | x :: xs, h, a, ha, b, hb => by
    obtain ⟨hx, hxs⟩ := List.pairwise_cons.mp h
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (hx b hb'))
    · exact Or.inr (Or.inr (hx a ha'))
    · exact pairwise_mem_cases hxs a ha' b hb'

/-- **No fork at an epoch.** Two certificates of one trace with the same epoch certify
    the same message, in whatever order and however many calls apart they were issued. -/
theorem belt_trace_same_epoch_same_message
    {st stF : authenticated_belt.VerifiedBeltQuorumGuard} {acts : List BeltAction}
    {certs : List BeltCert} (hTr : BeltTraceReachable st acts certs stF) :
    ∀ c1 ∈ certs, ∀ c2 ∈ certs,
      c1.grant.authorized_epoch = c2.grant.authorized_epoch →
      c1.grant.msg_tag = c2.grant.msg_tag := by
  intro c1 h1 c2 h2 heq
  have hval : c1.grant.authorized_epoch.val = c2.grant.authorized_epoch.val := by rw [heq]
  rcases pairwise_mem_cases (belt_trace_certs_monotone hTr) c1 h1 c2 h2 with
    rfl | hlt | hlt
  · rfl
  · rcases hlt with hlt | ⟨_, hm⟩
    · omega
    · exact hm
  · rcases hlt with hlt | ⟨_, hm⟩
    · omega
    · exact hm.symm

/-- Every certificate of a trace is backed by its signer bitmap: `certified_acks` is the
    number of set bits, that number is at least `q`, and every signer is below `n`.
    The invariant holds again at the end of the trace. -/
theorem belt_trace_certs_quorum {n q : Std.U32}
    {st stF : authenticated_belt.VerifiedBeltQuorumGuard} {acts : List BeltAction}
    {certs : List BeltCert} (hTr : BeltTraceReachable st acts certs stF)
    (hinv : BeltGuardInv n q st) :
    (∀ c ∈ certs,
      c.grant.certified_acks.val = beltPopcount c.signers ∧
      q.val ≤ beltPopcount c.signers ∧
      (∀ i, c.signers.bv.getLsbD i = true → i < n.val)) ∧
    BeltGuardInv n q stF := by
  induction hTr with
  | nil st => exact ⟨fun _ hc => False.elim (List.not_mem_nil hc), hinv⟩
  | bound h _ ih => exact ih (belt_outcome_preserves_inv hinv (belt_step_outcome h))
  | acked h _ ih => exact ih (belt_outcome_preserves_inv hinv (belt_step_outcome h))
  | @certified st st' stF a acts certs g h _ ih =>
    have ho : BeltStepOutcome st st' (.granted g) := belt_step_outcome h
    obtain ⟨ihc, ihF⟩ := ih (belt_outcome_preserves_inv hinv ho)
    obtain ⟨_, _, _, _, hca, hq, hbm⟩ := belt_outcome_granted_inv ho
    obtain ⟨hn, hqq, hcnt, hbits⟩ := hinv
    refine ⟨?_, ihF⟩
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · refine ⟨?_, ?_, ?_⟩
      · show g.certified_acks.val = beltPopcount st'.ack_bitmap
        rw [hca, hbm]
        exact hcnt
      · show q.val ≤ beltPopcount st'.ack_bitmap
        rw [hbm, ← hcnt, ← hqq]
        exact hq
      · intro i hi
        have hi' : st'.ack_bitmap.bv.getLsbD i = true := hi
        rw [hbm] at hi'
        exact hbits i hi'
    · exact ihc c hc
  | failed h _ ih => exact ih (belt_outcome_preserves_inv hinv (belt_step_outcome h))

/-- **Quorum intersection.** Under `n + f < 2 * q`, two signer sets of at least `q`
    custodians below `n` share more than `f` custodians. -/
theorem belt_quorum_intersection {n f q : Std.U32} {s1 s2 : Std.U64}
    (hcfg : n.val + f.val < 2 * q.val)
    (h1 : q.val ≤ beltPopcount s1) (hb1 : ∀ i, s1.bv.getLsbD i = true → i < n.val)
    (h2 : q.val ≤ beltPopcount s2) (hb2 : ∀ i, s2.bv.getLsbD i = true → i < n.val) :
    f.val < beltPopcount (s1 &&& s2) := by
  have := beltPopcount_inter_ge s1 s2 n.val hb1 hb2
  omega

/-- What a successful `new_validated` establishes. -/
theorem auth_belt_new_validated_inv
    {n t f q : Std.U32} {gl : Bool} {e0 window : Std.U64}
    {commit wal : Array Std.U8 32#usize} {keys : Array (Array Std.U8 32#usize) 64#usize}
    {st0 : authenticated_belt.VerifiedBeltQuorumGuard}
    (h : authenticated_belt.VerifiedBeltQuorumGuard.new_validated
      n t f q gl e0 window commit keys wal = .ok (.Ok st0)) :
    ValidBeltQuorumConfigProp n t f q gl ∧
    n.val ≤ 64 ∧
    st0.inner.n = n ∧ st0.inner.q = q ∧
    st0.inner.has_bound_epoch = false ∧
    st0.inner.next_epoch = e0 ∧
    st0.inner.poisoned = false ∧
    st0.inner.ack_count = 0#u32 ∧
    st0.ack_bitmap = 0#u64 := by
  by_cases hn : n > 64#u32
  · simp [authenticated_belt.VerifiedBeltQuorumGuard.new_validated, hn] at h
  · by_cases hv : validBeltQuorumConfigBool n t f q gl = true
    · simp [authenticated_belt.VerifiedBeltQuorumGuard.new_validated, hn,
        pants_and_quorum_guards.BeltQuorumCore.new_validated,
        validate_belt_quorum_config_eq, hv] at h
      cases h
      refine ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · obtain ⟨b, hb, hiff⟩ := validate_belt_quorum_config_spec n t f q gl
        rw [validate_belt_quorum_config_eq] at hb
        injection hb with hb
        exact hiff.mp (hb.symm.trans hv)
      · exact Nat.le_of_not_lt
          (fun (hlt : (64#u32 : Std.U32).val < n.val) => hn ((UScalar.lt_iff_val _ _).mpr hlt))
    · simp [authenticated_belt.VerifiedBeltQuorumGuard.new_validated, hn,
        pants_and_quorum_guards.BeltQuorumCore.new_validated,
        validate_belt_quorum_config_eq, hv] at h

/-- **Unbounded multi-turn fork-freedom of the authenticated belt guard.** From a guard
    created by `new_validated`, after any sequence of `step` calls on any inputs:
    * the configuration satisfies `n + f < 2 * q`;
    * certificate epochs never decrease in issue order, and a repeated epoch repeats
      the message;
    * every certificate's epoch is at least the initial `next_epoch`, its
      `certified_acks` is the number of distinct custodians in its signer bitmap, that
      number is at least `q`, and every signer is below `n`;
    * any two certificates share more than `f` signers;
    * the signer-set invariant holds in the final state. -/
theorem belt_trace_fork_free_and_epoch_monotone
    (n t f q : Std.U32) (gl : Bool) (e0 window : Std.U64)
    (commit wal : Array Std.U8 32#usize) (keys : Array (Array Std.U8 32#usize) 64#usize)
    (st0 stF : authenticated_belt.VerifiedBeltQuorumGuard)
    (acts : List BeltAction) (certs : List BeltCert)
    (hnew : authenticated_belt.VerifiedBeltQuorumGuard.new_validated
      n t f q gl e0 window commit keys wal = .ok (.Ok st0))
    (hTr : BeltTraceReachable st0 acts certs stF) :
    n.val + f.val < 2 * q.val ∧
    certs.Pairwise (fun c1 c2 =>
      c1.grant.authorized_epoch.val < c2.grant.authorized_epoch.val ∨
      (c1.grant.authorized_epoch = c2.grant.authorized_epoch ∧
        c1.grant.msg_tag = c2.grant.msg_tag)) ∧
    (∀ c ∈ certs,
      e0.val ≤ c.grant.authorized_epoch.val ∧
      c.grant.certified_acks.val = beltPopcount c.signers ∧
      q.val ≤ beltPopcount c.signers ∧
      (∀ i, c.signers.bv.getLsbD i = true → i < n.val)) ∧
    (∀ c1 ∈ certs, ∀ c2 ∈ certs, f.val < beltPopcount (c1.signers &&& c2.signers)) ∧
    BeltGuardInv n q stF := by
  obtain ⟨hProp, _, hn, hq, hb0, hne0, _, hc0, hbm0⟩ := auth_belt_new_validated_inv hnew
  have hcfg : n.val + f.val < 2 * q.val := by
    unfold ValidBeltQuorumConfigProp at hProp
    exact hProp.2.2.2.2.1
  have hinv0 : BeltGuardInv n q st0 := by
    refine ⟨hn, hq, ?_, ?_⟩
    · rw [hc0, hbm0]; exact belt_zero_count_popcount
    · intro i hi
      rw [hbm0, belt_zero_getLsbD] at hi
      cases hi
  obtain ⟨hquorum, hinvF⟩ := belt_trace_certs_quorum hTr hinv0
  refine ⟨hcfg, belt_trace_certs_monotone hTr, ?_, ?_, hinvF⟩
  · intro c hc
    refine ⟨?_, hquorum c hc⟩
    rcases belt_trace_certs_ahead hTr c hc with ⟨hb, _, _⟩ | hge
    · rw [hb0] at hb; cases hb
    · rw [hne0] at hge; exact hge
  · intro c1 hc1 c2 hc2
    exact belt_quorum_intersection hcfg (hquorum c1 hc1).2.1 (hquorum c1 hc1).2.2
      (hquorum c2 hc2).2.1 (hquorum c2 hc2).2.2

/-- **Poison is absorbing for the authenticated guard.** From a poisoned core, no call
    sequence yields a certificate and the core stays poisoned. -/
theorem belt_poisoned_trace_no_certs
    {st stF : authenticated_belt.VerifiedBeltQuorumGuard} {acts : List BeltAction}
    {certs : List BeltCert} (hTr : BeltTraceReachable st acts certs stF)
    (hp : st.inner.poisoned = true) :
    certs = [] ∧ stF.inner.poisoned = true := by
  have hstep : ∀ {s s' : authenticated_belt.VerifiedBeltQuorumGuard} {obs : BeltObs},
      s.inner.poisoned = true → BeltStepOutcome s s' obs →
      s'.inner.poisoned = true ∧ ∀ g, obs ≠ .granted g := by
    intro s s' obs hps ho
    have hcor : ∀ (hc : beltGuardCorrupt s.inner = false), False := by
      intro hc
      have := (belt_not_corrupt_facts hc).1
      rw [hps] at this
      cases this
    cases ho with
    | rejected_unchanged h => subst h; exact ⟨hps, fun g hg => by cases hg⟩
    | rejected_poisoned h1 h2 =>
      exact ⟨by rw [h1], fun g hg => by cases hg⟩
    | retried h => subst h; exact ⟨hps, fun g hg => by cases hg⟩
    | bound ep msg hc _ _ _ _ => exact (hcor hc).elim
    | duplicate h => subst h; exact ⟨hps, fun g hg => by cases hg⟩
    | acked id hc _ _ _ _ _ _ => exact (hcor hc).elim
    | granted hc _ _ _ => exact (hcor hc).elim
  induction hTr with
  | nil st => exact ⟨rfl, hp⟩
  | bound h _ ih => exact ih (hstep hp (belt_step_outcome h)).1
  | acked h _ ih => exact ih (hstep hp (belt_step_outcome h)).1
  | @certified st st' stF a acts certs g h _ ih =>
    have ho : BeltStepOutcome st st' (.granted g) := belt_step_outcome h
    exact absurd rfl ((hstep hp ho).2 g)
  | failed h _ ih => exact ih (hstep hp (belt_step_outcome h)).1

/-! ## 8. Totality: the guard never aborts -/

/-- `Shake256Sponge::absorb` returns on every input slice, across any number of rate
    blocks. -/
theorem sponge_absorb_total (sp : keccak.Shake256Sponge) (data : Slice Std.U8)
    (hn : sp.squeezing = false) (hbuf : sp.buf_len.val < 136) :
    ∃ out, keccak.Shake256Sponge.absorb sp data = .ok out ∧
      out.squeezing = false ∧ out.buf_len.val < 136 := by
  let body := fun (a, buf, i, pos) => keccak.Shake256Sponge.absorb_loop.body data a buf i pos
  let P := fun (n : Nat) (x : Std.Array Std.U64 25#usize × Std.Array Std.U8 136#usize ×
      Std.Usize × Std.Usize) =>
    x.2.2.2.val + n = data.val.length ∧ x.2.2.1.val < 136
  let Q := fun (x : Std.Array Std.U64 25#usize × Std.Array Std.U8 136#usize × Std.Usize) =>
    x.2.2.val < 136
  have hz : ∀ x, P 0 x → ∃ y, body x = .ok (.done y) ∧ Q y := by
    rintro ⟨a, buf, i, pos⟩ ⟨hp, hi⟩
    have he : ¬ pos < Slice.len data := by
      change ¬ pos.val < (Slice.len data).val
      rw [Slice.len_val]
      change pos.val + 0 = data.val.length at hp
      rw [← hp, Nat.add_zero]
      exact Nat.lt_irrefl _
    exact ⟨(a, buf, i),
      by simp only [body, keccak.Shake256Sponge.absorb_loop.body, he, ite_false], hi⟩
  have step : ∀ n x, P (n + 1) x → ∃ x', body x = .ok (.cont x') ∧ P n x' := by
    rintro n ⟨a, buf, i, pos⟩ ⟨hp, hib⟩
    change pos.val + (n + 1) = data.val.length at hp
    change i.val < 136 at hib
    have hpos : pos < Slice.len data := by
      change pos.val < (Slice.len data).val
      rw [Slice.len_val]
      exact rank_lt hp
    have hilt : i < keccak.SHAKE256_RATE_BYTES := by
      unfold keccak.SHAKE256_RATE_BYTES
      exact hib
    obtain ⟨v, hv⟩ := slice_index_total data pos (rank_lt hp)
    obtain ⟨buf', hbuf'⟩ := array_update_total buf i v hib
    obtain ⟨i', hi', vi'⟩ := checked_add_val i 1#usize
      (by change i.val + 1 < 2 ^ 64; exact Nat.lt_trans (Nat.succ_lt_succ hib) (by decide))
    obtain ⟨pos', hp', vp'⟩ := checked_add_val pos 1#usize (by
      change pos.val + 1 < 2 ^ 64
      exact Nat.lt_of_le_of_lt (rank_succ_le hp)
        (by simpa only [← Slice.len_val] using (Slice.len data).bv.isLt))
    change i'.val = i.val + 1 at vi'
    change pos'.val = pos.val + 1 at vp'
    by_cases he : i' = keccak.SHAKE256_RATE_BYTES
    · obtain ⟨a', ha'⟩ := xor_rate_block_total a buf'
      obtain ⟨a'', ha''⟩ := keccak_f1600_total a'
      refine ⟨(a'', buf', 0#usize, pos'), ?_, ?_⟩
      · simp only [body, keccak.Shake256Sponge.absorb_loop.body, hpos, hilt, ite_true,
          hv, hbuf', hi', hp', he, ha', ha'', bind_eq_result_bind, result_bind_ok]
      · constructor
        · change pos'.val + n = data.val.length
          rw [vp']; exact rank_next hp
        · show (0#usize : Std.Usize).val < 136
          decide
    · have hsmall : i'.val < 136 := by
        have hne : i'.val ≠ 136 := by
          intro hv136
          apply he
          apply UScalar.eq_of_val_eq
          rw [hv136, keccak.SHAKE256_RATE_BYTES]
          rfl
        omega
      refine ⟨(a, buf', i', pos'), ?_, ?_⟩
      · simp only [body, keccak.Shake256Sponge.absorb_loop.body, hpos, hilt, ite_true,
          hv, hbuf', hi', hp', he, ite_false, bind_eq_result_bind, result_bind_ok]
      · constructor
        · change pos'.val + n = data.val.length
          rw [vp']; exact rank_next hp
        · exact hsmall
  obtain ⟨⟨a, buf, i⟩, hloop, hi⟩ := loopFuel_total_rank body P Q hz step data.val.length
    (sp.state, sp.buf, sp.buf_len, 0#usize) ⟨Nat.zero_add _, hbuf⟩
  have hactual : keccak.Shake256Sponge.absorb_loop sp.state sp.buf sp.buf_len data 0#usize =
      .ok (a, buf, i) := by
    unfold keccak.Shake256Sponge.absorb_loop
    apply loop_ok_of_loopFuel (fuel := data.val.length + 1)
    · simpa only [Slice.len_val] using usize_lt_loopMaxFuel (Slice.len data)
    · exact hloop
  refine ⟨{ sp with state := a, buf := buf, buf_len := i }, ?_, hn, hi⟩
  simp only [keccak.Shake256Sponge.absorb, massert_not_of_eq_false hn,
    hactual, bind_eq_result_bind, result_bind_ok]

theorem u64_shr_i32_total (x : Std.U64) (s : Std.I32)
    (h : (!s.bv.msb && decide (s.bv.toNat < UScalarTy.U64.numBits)) = true) :
    ∃ y, (x >>> s : Result Std.U64) = .ok y :=
  ⟨⟨x.bv >>> s.bv.toNat⟩, by rw [hShrI_uscalar_eq, ite_eq_left h]⟩

theorem belt_encode_epoch_total (epoch : Std.U64) :
    ∃ a, authenticated_belt.encode_epoch epoch = .ok a := by
  obtain ⟨i1, h1⟩ := u64_shr_i32_total epoch 8#i32 (by decide)
  obtain ⟨i3, h3⟩ := u64_shr_i32_total epoch 16#i32 (by decide)
  obtain ⟨i5, h5⟩ := u64_shr_i32_total epoch 24#i32 (by decide)
  obtain ⟨i7, h7⟩ := u64_shr_i32_total epoch 32#i32 (by decide)
  obtain ⟨i9, h9⟩ := u64_shr_i32_total epoch 40#i32 (by decide)
  obtain ⟨i11, h11⟩ := u64_shr_i32_total epoch 48#i32 (by decide)
  obtain ⟨i13, h13⟩ := u64_shr_i32_total epoch 56#i32 (by decide)
  unfold authenticated_belt.encode_epoch
  simp only [h1, h3, h5, h7, h9, h11, h13, bind_eq_result_bind, result_bind_ok, lift_eq_ok]
  exact ⟨_, rfl⟩

/-- Six-part domain-separated SHAKE256 tag, the common shape of the custodian
    acknowledgment tag and the WAL receipt tag. -/
theorem belt_sponge_six_absorb_squeeze_total
    (d0 : Slice Std.U8) (d1 d2 d3 d4 d5 : Slice Std.U8) :
    ∃ out : Std.Array Std.U8 32#usize,
      (do
        let sponge ← keccak.Shake256Sponge.new_shake256
        let sponge1 ← keccak.Shake256Sponge.absorb sponge d0
        let sponge2 ← keccak.Shake256Sponge.absorb sponge1 d1
        let sponge3 ← keccak.Shake256Sponge.absorb sponge2 d2
        let sponge4 ← keccak.Shake256Sponge.absorb sponge3 d3
        let sponge5 ← keccak.Shake256Sponge.absorb sponge4 d4
        let sponge6 ← keccak.Shake256Sponge.absorb sponge5 d5
        let (_, s7) ← keccak.Shake256Sponge.squeeze sponge6
          (Std.Array.to_slice_mut (Std.Array.repeat 32#usize 0#u8)).1
        ok ((Std.Array.to_slice_mut (Std.Array.repeat 32#usize 0#u8)).2 s7)) = .ok out := by
  let sp0 : keccak.Shake256Sponge :=
    ⟨Std.Array.repeat 25#usize 0#u64, Std.Array.repeat 136#usize 0#u8,
      0#usize, 31#u8, false, 0#usize⟩
  have hnew : keccak.Shake256Sponge.new_shake256 = .ok sp0 := rfl
  obtain ⟨sp1, hsp1, hn1, hv1⟩ := sponge_absorb_total sp0 d0 rfl (by decide)
  obtain ⟨sp2, hsp2, hn2, hv2⟩ := sponge_absorb_total sp1 d1 hn1 hv1
  obtain ⟨sp3, hsp3, hn3, hv3⟩ := sponge_absorb_total sp2 d2 hn2 hv2
  obtain ⟨sp4, hsp4, hn4, hv4⟩ := sponge_absorb_total sp3 d3 hn3 hv3
  obtain ⟨sp5, hsp5, hn5, hv5⟩ := sponge_absorb_total sp4 d4 hn4 hv4
  obtain ⟨sp6, hsp6, hn6, hv6⟩ := sponge_absorb_total sp5 d5 hn5 hv5
  obtain ⟨result, hresult⟩ := sponge_squeeze_short sp6
    (Std.Array.to_slice_mut (Std.Array.repeat 32#usize 0#u8)).1 32
    (by decide) hn6 hv6 rfl
  simp only [hnew, bind_eq_result_bind, result_bind_ok]
  rw [hsp1, result_bind_ok, hsp2, result_bind_ok, hsp3, result_bind_ok,
    hsp4, result_bind_ok, hsp5, result_bind_ok, hsp6, result_bind_ok, hresult, result_bind_ok]
  exact ⟨_, rfl⟩

theorem belt_custodian_ack_tag_total (key commit : Array Std.U8 32#usize) (epoch : Std.U64)
    (msg : Array Std.U8 32#usize) (id : Std.U8) :
    ∃ tag, authenticated_belt.custodian_ack_tag key commit epoch msg id = .ok tag := by
  obtain ⟨a, ha⟩ := belt_encode_epoch_total epoch
  obtain ⟨out, hout⟩ := belt_sponge_six_absorb_squeeze_total
    (Array.to_slice (Array.make 16#usize [
      81#u8, 83#u8, 65#u8, 71#u8, 46#u8, 66#u8, 69#u8, 76#u8, 84#u8, 46#u8,
      65#u8, 67#u8, 75#u8, 46#u8, 118#u8, 49#u8 ]))
    (Array.to_slice key) (Array.to_slice commit) (Array.to_slice a) (Array.to_slice msg)
    (Array.to_slice (Array.make 1#usize [ id ]))
  refine ⟨out, ?_⟩
  unfold authenticated_belt.custodian_ack_tag
  simp only [ha, bind_eq_result_bind, result_bind_ok, lift_eq_ok] at hout ⊢
  exact hout

theorem belt_wal_receipt_tag_total (key commit : Array Std.U8 32#usize) (epoch : Std.U64)
    (msg receipt_digest : Array Std.U8 32#usize) :
    ∃ tag, authenticated_belt.wal_receipt_tag key commit epoch msg receipt_digest = .ok tag := by
  obtain ⟨a, ha⟩ := belt_encode_epoch_total epoch
  obtain ⟨out, hout⟩ := belt_sponge_six_absorb_squeeze_total
    (Array.to_slice (Array.make 16#usize [
      81#u8, 83#u8, 65#u8, 71#u8, 46#u8, 66#u8, 69#u8, 76#u8, 84#u8, 46#u8,
      87#u8, 65#u8, 76#u8, 46#u8, 118#u8, 49#u8 ]))
    (Array.to_slice key) (Array.to_slice commit) (Array.to_slice a) (Array.to_slice msg)
    (Array.to_slice receipt_digest)
  refine ⟨out, ?_⟩
  unfold authenticated_belt.wal_receipt_tag
  simp only [ha, bind_eq_result_bind, result_bind_ok, lift_eq_ok] at hout ⊢
  exact hout

/-- `BeltQuorumCore::record_custodian_ack` returns on every state and input: its one
    checked addition is guarded by `ack_count < n`. -/
theorem belt_core_ack_total (s : pants_and_quorum_guards.BeltQuorumCore) (ep : Std.U64)
    (tag : Array Std.U8 32#usize) :
    ∃ p, pants_and_quorum_guards.BeltQuorumCore.record_custodian_ack s ep tag = .ok p := by
  unfold pants_and_quorum_guards.BeltQuorumCore.record_custodian_ack
  rw [validate_belt_quorum_config_eq]
  simp only [pants_and_quorum_guards.poison_belt_guard, ct_eq_bytes32_spec,
    bind_eq_result_bind, result_bind_ok]
  by_cases hge : s.ack_count >= s.n
  · cases s.phase <;> simp only [eq_true hge, Bool.false_eq_true, ↓reduceIte] <;>
      (repeat' (first | split | simp only [result_bind_ok])) <;>
      exact ⟨_, rfl⟩
  · have hlt : s.ack_count.val < s.n.val :=
      Nat.lt_of_not_le (fun h => hge ((UScalar.le_iff_val _ _).mpr h))
    have hn : s.n.val < 2 ^ 32 := s.n.bv.isLt
    obtain ⟨c, hc, _⟩ := checked_add_val s.ack_count 1#u32
      (by show s.ack_count.val + 1 < 2 ^ 32; omega)
    cases s.phase <;>
      simp only [eq_false hge, hc, result_bind_ok, Bool.false_eq_true, ↓reduceIte] <;>
      (repeat' (first | split | simp only [result_bind_ok])) <;>
      exact ⟨_, rfl⟩

theorem belt_core_authorize_total (s : pants_and_quorum_guards.BeltQuorumCore) (ep : Std.U64)
    (tag : Array Std.U8 32#usize) :
    ∃ p, pants_and_quorum_guards.BeltQuorumCore.authorize_shares s ep tag = .ok p := by
  unfold pants_and_quorum_guards.BeltQuorumCore.authorize_shares
  rw [validate_belt_quorum_config_eq]
  simp only [pants_and_quorum_guards.poison_belt_guard, ct_eq_bytes32_spec,
    bind_eq_result_bind, result_bind_ok]
  cases s.phase <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
    (repeat' (first | split | simp only [result_bind_ok])) <;>
    exact ⟨_, rfl⟩

/-- `BeltQuorumCore::propose_or_retry_epoch` returns on every state and input: the
    checked subtraction is guarded by `next_epoch ≤ proposed_epoch` and the checked
    increment by `proposed_epoch ≠ u64::MAX`. -/
theorem belt_core_propose_total (s : pants_and_quorum_guards.BeltQuorumCore) (ep : Std.U64)
    (tag : Array Std.U8 32#usize) (walOk : Bool) :
    ∃ p, pants_and_quorum_guards.BeltQuorumCore.propose_or_retry_epoch s ep tag walOk =
      .ok p := by
  unfold pants_and_quorum_guards.BeltQuorumCore.propose_or_retry_epoch
  rw [validate_belt_quorum_config_eq]
  simp only [pants_and_quorum_guards.poison_belt_guard, ct_eq_bytes32_spec,
    bind_eq_result_bind, result_bind_ok]
  by_cases hlt : ep < s.next_epoch
  · cases s.phase <;> cases s.poisoned <;>
      cases validBeltQuorumConfigBool s.n s.t s.f s.q s.global_liveness_mode <;>
      cases s.has_bound_epoch <;> cases walOk <;>
      (try simp only [eq_true hlt, Bool.false_eq_true, ↓reduceIte]) <;>
      (repeat' (first | split | simp only [result_bind_ok])) <;>
      exact ⟨_, rfl⟩
  · have hge : s.next_epoch.val ≤ ep.val :=
      Nat.le_of_not_lt (fun h => hlt ((UScalar.lt_iff_val _ _).mpr h))
    have hsub : (ep - s.next_epoch : Result Std.U64) = .ok ⟨ep.bv - s.next_epoch.bv⟩ := by
      rw [hSub_uscalar_eq, ite_eq_left hge]
    by_cases hmax : ep = core.num.U64.MAX
    · cases s.phase <;> cases s.poisoned <;>
        cases validBeltQuorumConfigBool s.n s.t s.f s.q s.global_liveness_mode <;>
        cases s.has_bound_epoch <;> cases walOk <;>
        (try simp only [eq_false hlt, hsub, eq_true hmax, result_bind_ok,
          Bool.false_eq_true, ↓reduceIte]) <;>
        (repeat' (first | split | simp only [result_bind_ok])) <;>
        exact ⟨_, rfl⟩
    · obtain ⟨c, hc, _⟩ := checked_add_val ep 1#u64
        (by show ep.val + 1 < 2 ^ 64; exact u64_val_succ_lt_of_ne_max hmax)
      cases s.phase <;> cases s.poisoned <;>
        cases validBeltQuorumConfigBool s.n s.t s.f s.q s.global_liveness_mode <;>
        cases s.has_bound_epoch <;> cases walOk <;>
        (try simp only [eq_false hlt, hsub, eq_false hmax, hc, result_bind_ok,
          Bool.false_eq_true, ↓reduceIte]) <;>
        (repeat' (first | split | simp only [result_bind_ok])) <;>
        exact ⟨_, rfl⟩

/-! ## 9. Completeness: accepted paths, total `step`, and inhabited traces -/

theorem belt_not_corrupt_of_facts {s : pants_and_quorum_guards.BeltQuorumCore}
    (hp : s.poisoned = false) (hph : isBeltPhasePoisoned s.phase = false)
    (hv : validBeltQuorumConfigBool s.n s.t s.f s.q s.global_liveness_mode = true)
    (hb : s.has_bound_epoch = true → s.bound_epoch.val < s.next_epoch.val) :
    beltGuardCorrupt s = false := by
  cases hbb : s.has_bound_epoch with
  | false => simp [beltGuardCorrupt, hp, hph, hv, hbb]
  | true =>
    have hlt := hb hbb
    have hd : decide (s.next_epoch.val ≤ s.bound_epoch.val) = false :=
      decide_eq_false (Nat.not_le.mpr hlt)
    simp [beltGuardCorrupt, hp, hph, hv, hbb, hd]

/-- Core state right after binding a fresh epoch. -/
abbrev beltFreshCore (s : pants_and_quorum_guards.BeltQuorumCore) (e : Std.U64)
    (msg : Array Std.U8 32#usize) : pants_and_quorum_guards.BeltQuorumCore :=
  { s with next_epoch := ⟨e.bv + (1#u64).bv⟩,
           phase := .EpochBoundPendingQuorum,
           has_bound_epoch := true,
           bound_epoch := e,
           bound_msg_tag := msg,
           ack_count := 0#u32 }

abbrev beltAfterPropose (st : authenticated_belt.VerifiedBeltQuorumGuard) (e : Std.U64)
    (msg : Array Std.U8 32#usize) : authenticated_belt.VerifiedBeltQuorumGuard :=
  { st with inner := beltFreshCore st.inner e msg, ack_bitmap := 0#u64 }

abbrev beltAfterAck (st : authenticated_belt.VerifiedBeltQuorumGuard) (id : Std.U8) :
    authenticated_belt.VerifiedBeltQuorumGuard :=
  { st with
    inner := { st.inner with ack_count := ⟨st.inner.ack_count.bv + (1#u32).bv⟩ },
    ack_bitmap := st.ack_bitmap ||| beltCustodianBit id }

abbrev beltAfterGrant (st : authenticated_belt.VerifiedBeltQuorumGuard) :
    authenticated_belt.VerifiedBeltQuorumGuard :=
  { st with inner := { st.inner with phase := .SharesAuthorized } }

theorem belt_not_corrupt_fresh {s : pants_and_quorum_guards.BeltQuorumCore} {e : Std.U64}
    (msg : Array Std.U8 32#usize) (hc : beltGuardCorrupt s = false)
    (hlt : e.val + 1 < 2 ^ 64) : beltGuardCorrupt (beltFreshCore s e msg) = false := by
  obtain ⟨hp, _, hv, _⟩ := belt_not_corrupt_facts hc
  refine belt_not_corrupt_of_facts hp rfl hv (fun _ => ?_)
  show e.val < (⟨e.bv + (1#u64).bv⟩ : Std.U64).val
  rw [u64_succ_val hlt]
  exact Nat.lt_succ_self _

theorem belt_not_corrupt_set_ack_count {s : pants_and_quorum_guards.BeltQuorumCore}
    (c : Std.U32) (hc : beltGuardCorrupt s = false) :
    beltGuardCorrupt { s with ack_count := c } = false := by
  obtain ⟨hp, hph, hv, hb⟩ := belt_not_corrupt_facts hc
  exact belt_not_corrupt_of_facts hp hph hv hb

theorem belt_mealy_propose_fresh {s : pants_and_quorum_guards.BeltQuorumCore} {e : Std.U64}
    (msg : Array Std.U8 32#usize) (hc : beltGuardCorrupt s = false)
    (hnr : ¬ (s.has_bound_epoch = true ∧ e = s.bound_epoch))
    (hge : s.next_epoch.val ≤ e.val)
    (hwin : e.val - s.next_epoch.val ≤ s.max_jump_window.val)
    (hmax : e ≠ core.num.U64.MAX) :
    beltQuorumMealy.step s (.ProposeOrRetryEpoch e msg true) =
      some (beltFreshCore s e msg, .EpochBound) := by
  have hr' : (s.has_bound_epoch && decide (e = s.bound_epoch)) = false := by
    cases hb : s.has_bound_epoch with
    | false => rfl
    | true =>
      have hne : ¬ e = s.bound_epoch := fun he => hnr ⟨hb, he⟩
      simp [hne]
  have hlt : ¬ e.val < s.next_epoch.val := Nat.not_lt.mpr hge
  have hw : ¬ s.max_jump_window.val < e.val - s.next_epoch.val := Nat.not_lt.mpr hwin
  dsimp only [beltQuorumMealy]
  rw [hc, hr']
  simp [hlt, hw, hmax]

theorem belt_mealy_ack_fresh {s : pants_and_quorum_guards.BeltQuorumCore}
    (hc : beltGuardCorrupt s = false) (hb : s.has_bound_epoch = true)
    (hcnt : s.ack_count.val < s.n.val) :
    beltQuorumMealy.step s (.RecordCustodianAck s.bound_epoch s.bound_msg_tag) =
      some ({ s with ack_count := ⟨s.ack_count.bv + (1#u32).bv⟩ },
            .AckRecorded ⟨s.ack_count.bv + (1#u32).bv⟩) := by
  have hn : ¬ s.n.val ≤ s.ack_count.val := Nat.not_le.mpr hcnt
  dsimp only [beltQuorumMealy]
  rw [hc]
  simp [hb, hn]

theorem belt_mealy_authorize_granted {s : pants_and_quorum_guards.BeltQuorumCore}
    (hc : beltGuardCorrupt s = false) (hb : s.has_bound_epoch = true)
    (hq : s.q.val ≤ s.ack_count.val) (hphase : s.phase ≠ .SharesAuthorized) :
    beltQuorumMealy.step s (.AuthorizeShares s.bound_epoch s.bound_msg_tag) =
      some ({ s with phase := .SharesAuthorized },
            .SharesAuthorized { _private := (), authorized_epoch := s.bound_epoch,
                                msg_tag := s.bound_msg_tag,
                                certified_acks := s.ack_count }) := by
  have hnq : ¬ s.ack_count.val < s.q.val := Nat.not_lt.mpr hq
  dsimp only [beltQuorumMealy]
  rw [hc]
  cases hp : s.phase <;> simp_all

/-- Every accepting step of the pure belt specification is realised by the extracted
    `propose_or_retry_epoch` (the converse of the simulation, obtained from totality). -/
theorem belt_core_propose_of_mealy
    {s s' : pants_and_quorum_guards.BeltQuorumCore} {ep : Std.U64}
    {tag : Array Std.U8 32#usize} {walOk : Bool}
    {o : pants_and_quorum_guards.BeltQuorumCoreOutput}
    (hm : beltQuorumMealy.step s (.ProposeOrRetryEpoch ep tag walOk) = some (s', o)) :
    pants_and_quorum_guards.BeltQuorumCore.propose_or_retry_epoch s ep tag walOk =
      .ok (s', .Ok ()) := by
  obtain ⟨⟨s2, r⟩, hcore⟩ := belt_core_propose_total s ep tag walOk
  cases r with
  | Ok u =>
    have h2 := belt_core_propose_ok_mealy hcore
    rw [hm] at h2
    injection h2 with h2
    injection h2 with h3 _
    rw [hcore, h3]
  | Err e =>
    have h2 := (belt_core_propose_err_mealy hcore).1
    rw [hm] at h2
    cases h2

theorem belt_core_ack_of_mealy
    {s s' : pants_and_quorum_guards.BeltQuorumCore} {ep : Std.U64}
    {tag : Array Std.U8 32#usize} {k : Std.U32}
    (hm : beltQuorumMealy.step s (.RecordCustodianAck ep tag) = some (s', .AckRecorded k)) :
    pants_and_quorum_guards.BeltQuorumCore.record_custodian_ack s ep tag =
      .ok (s', .Ok k) := by
  obtain ⟨⟨s2, r⟩, hcore⟩ := belt_core_ack_total s ep tag
  cases r with
  | Ok k2 =>
    have h2 := belt_core_ack_ok_mealy hcore
    rw [hm] at h2
    injection h2 with h2
    injection h2 with h3 h4
    injection h4 with h5
    rw [hcore, h3, h5]
  | Err e =>
    have h2 := (belt_core_ack_err_mealy hcore).1
    rw [hm] at h2
    cases h2

theorem belt_core_authorize_of_mealy
    {s s' : pants_and_quorum_guards.BeltQuorumCore} {ep : Std.U64}
    {tag : Array Std.U8 32#usize} {g : pants_and_quorum_guards.BeltAuthorizationGrant}
    (hm : beltQuorumMealy.step s (.AuthorizeShares ep tag) = some (s', .SharesAuthorized g)) :
    pants_and_quorum_guards.BeltQuorumCore.authorize_shares s ep tag =
      .ok (s', .Ok g) := by
  obtain ⟨⟨s2, r⟩, hcore⟩ := belt_core_authorize_total s ep tag
  cases r with
  | Ok g2 =>
    have h2 := belt_core_authorize_ok_mealy hcore
    rw [hm] at h2
    injection h2 with h2
    injection h2 with h3 h4
    injection h4 with h5
    rw [hcore, h3, h5]
  | Err e =>
    have h2 := (belt_core_authorize_err_mealy hcore).1
    rw [hm] at h2
    cases h2

theorem auth_belt_propose_total (st : authenticated_belt.VerifiedBeltQuorumGuard)
    (ep : Std.U64) (msg rd rt : Array Std.U8 32#usize) :
    ∃ p, authenticated_belt.VerifiedBeltQuorumGuard.propose_or_retry_epoch st ep msg rd rt =
      .ok p := by
  obtain ⟨expected, hw⟩ :=
    belt_wal_receipt_tag_total st.wal_key st.guard_key_commit ep msg rd
  obtain ⟨⟨inner, cr⟩, hcore⟩ :=
    belt_core_propose_total st.inner ep msg (decide (expected = rt))
  unfold authenticated_belt.VerifiedBeltQuorumGuard.propose_or_retry_epoch
  rw [hw]
  simp only [bind_eq_result_bind, result_bind_ok, ct_eq_bytes32_spec,
    pants_and_quorum_guards.BeltQuorumCore.impl.has_bound_epoch,
    pants_and_quorum_guards.BeltQuorumCore.impl.bound_epoch,
    pants_and_quorum_guards.BeltQuorumCore.is_poisoned]
  rw [hcore]
  cases cr <;> (repeat' (first | split | simp only [result_bind_ok])) <;> exact ⟨_, rfl⟩

theorem auth_belt_ack_total (st : authenticated_belt.VerifiedBeltQuorumGuard)
    (ep : Std.U64) (msg : Array Std.U8 32#usize) (id : Std.U8)
    (tag : Array Std.U8 32#usize) :
    ∃ p, authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack st ep msg id tag =
      .ok p := by
  unfold authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack
  simp only [pants_and_quorum_guards.BeltQuorumCore.impl.n,
    pants_and_quorum_guards.BeltQuorumCore.is_poisoned,
    pants_and_quorum_guards.BeltQuorumCore.impl.has_bound_epoch,
    pants_and_quorum_guards.BeltQuorumCore.impl.bound_epoch,
    pants_and_quorum_guards.BeltQuorumCore.impl.bound_msg_tag,
    pants_and_quorum_guards.BeltQuorumCore.impl.ack_count,
    ct_eq_bytes32_spec, bind_eq_result_bind, result_bind_ok, lift_eq_ok]
  by_cases hin : UScalar.cast .Usize id >= UScalar.cast .Usize st.inner.n
  · rw [ite_eq_left hin]; exact ⟨_, rfl⟩
  · rw [ite_eq_right hin]
    by_cases h64 : id >= 64#u8
    · rw [ite_eq_left h64]; exact ⟨_, rfl⟩
    · rw [ite_eq_right h64]
      have hid : id.val < 64 :=
        Nat.lt_of_not_le
          (fun (h : (64#u8 : Std.U8).val ≤ id.val) => h64 ((UScalar.le_iff_val _ _).mpr h))
      have hcast : (UScalar.cast .Usize id).val = id.val :=
        uscalar_cast_val_eq .Usize id (Nat.lt_of_lt_of_le id.bv.isLt (by decide))
      obtain ⟨key, hkey⟩ := array_index_total st.custodian_keys (UScalar.cast .Usize id)
        (by rw [hcast]; exact hid)
      obtain ⟨expected, htag⟩ :=
        belt_custodian_ack_tag_total key st.guard_key_commit ep msg id
      obtain ⟨⟨inner, cr⟩, hcore⟩ := belt_core_ack_total st.inner ep msg
      have hshl : (1#u64 <<< id : Result Std.U64) = .ok (beltCustodianBit id) :=
        (hShlU_uscalar_eq (1#u64) id).trans (ite_eq_left hid)
      rw [hkey]
      simp only [result_bind_ok]
      rw [htag]
      simp only [result_bind_ok, hshl, hcore]
      cases cr <;> (repeat' (first | split | simp only [result_bind_ok])) <;> exact ⟨_, rfl⟩

theorem auth_belt_authorize_total (st : authenticated_belt.VerifiedBeltQuorumGuard)
    (ep : Std.U64) (msg : Array Std.U8 32#usize) :
    ∃ p, authenticated_belt.VerifiedBeltQuorumGuard.authorize_shares st ep msg = .ok p := by
  obtain ⟨⟨inner, cr⟩, hcore⟩ := belt_core_authorize_total st.inner ep msg
  unfold authenticated_belt.VerifiedBeltQuorumGuard.authorize_shares
  rw [hcore]
  simp only [bind_eq_result_bind, result_bind_ok,
    pants_and_quorum_guards.BeltQuorumCore.is_poisoned]
  cases cr <;> (repeat' (first | split | simp only [result_bind_ok])) <;> exact ⟨_, rfl⟩

/-- **The guard never aborts.** `VerifiedBeltQuorumGuard::step` returns a state and a
    verdict on every state and every input: no arithmetic overflow, no out-of-bounds
    index, no divergence. -/
theorem belt_step_total (st : authenticated_belt.VerifiedBeltQuorumGuard) (a : BeltAction) :
    ∃ st' res, authenticated_belt.VerifiedBeltQuorumGuard.step st a = .ok (st', res) := by
  unfold authenticated_belt.VerifiedBeltQuorumGuard.step
  cases a with
  | ProposeOrRetryEpoch ep msg rd rt =>
    dsimp only
    obtain ⟨⟨nx, r⟩, hf⟩ := auth_belt_propose_total st ep msg rd rt
    rw [hf]
    cases r <;> exact ⟨_, _, rfl⟩
  | RecordCustodianAck ep msg id tag =>
    dsimp only
    obtain ⟨⟨nx, r⟩, hf⟩ := auth_belt_ack_total st ep msg id tag
    rw [hf]
    cases r <;> exact ⟨_, _, rfl⟩
  | AuthorizeShares ep msg =>
    dsimp only
    obtain ⟨⟨nx, r⟩, hf⟩ := auth_belt_authorize_total st ep msg
    rw [hf]
    cases r <;> exact ⟨_, _, rfl⟩

/-- **`BeltTraceReachable` does not narrow the adversary.** Every list of actions, from
    every state, has a trace; the safety theorems therefore speak about all call
    sequences, not about the ones that happen to return. -/
theorem belt_trace_exists :
    ∀ (acts : List BeltAction) (st : authenticated_belt.VerifiedBeltQuorumGuard),
      ∃ certs stF, BeltTraceReachable st acts certs stF
  | [], st => ⟨[], st, .nil st⟩
  | a :: acts, st => by
    obtain ⟨st', res, h⟩ := belt_step_total st a
    obtain ⟨certs, stF, hTr⟩ := belt_trace_exists acts st'
    cases res with
    | Ok o =>
      cases o with
      | EpochBound => exact ⟨_, _, .bound h hTr⟩
      | AckRecorded k => exact ⟨_, _, .acked h hTr⟩
      | SharesAuthorized g => exact ⟨_, _, .certified h hTr⟩
    | Err e => exact ⟨_, _, .failed h hTr⟩

theorem BeltTraceReachable.append
    {st st1 st2 : authenticated_belt.VerifiedBeltQuorumGuard}
    {a1 a2 : List BeltAction} {c1 c2 : List BeltCert}
    (h1 : BeltTraceReachable st a1 c1 st1) (h2 : BeltTraceReachable st1 a2 c2 st2) :
    BeltTraceReachable st (a1 ++ a2) (c1 ++ c2) st2 := by
  induction h1 with
  | nil st => exact h2
  | bound h _ ih => exact .bound h (ih h2)
  | acked h _ ih => exact .acked h (ih h2)
  | certified h _ ih => exact .certified h (ih h2)
  | failed h _ ih => exact .failed h (ih h2)

theorem beltCustodianBit_and_eq_zero_of {bm : Std.U64} {id : Std.U8} (hk : id.val < 64)
    (h : bm.bv.getLsbD id.val = false) : bm &&& beltCustodianBit id = 0#u64 := by
  apply UScalar.ext
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  show (bm.bv &&& (beltCustodianBit id).bv).getLsbD i = (0#64).getLsbD i
  rw [BitVec.getLsbD_and, beltCustodianBit_getLsbD id hk, BitVec.getLsbD_zero]
  by_cases hik : id.val = i
  · rw [← hik, h]; rfl
  · rw [decide_eq_false hik, Bool.and_false]

/-- A fresh in-window proposal carrying the WAL receipt tag the guard computes binds the
    epoch and clears the signer bitmap. -/
theorem belt_step_propose_fresh (st : authenticated_belt.VerifiedBeltQuorumGuard)
    (e : Std.U64) (msg rd rt : Array Std.U8 32#usize)
    (hwal : authenticated_belt.wal_receipt_tag st.wal_key st.guard_key_commit e msg rd = .ok rt)
    (hc : beltGuardCorrupt st.inner = false)
    (hnr : ¬ (st.inner.has_bound_epoch = true ∧ e = st.inner.bound_epoch))
    (hge : st.inner.next_epoch.val ≤ e.val)
    (hwin : e.val - st.inner.next_epoch.val ≤ st.inner.max_jump_window.val)
    (hmax : e ≠ core.num.U64.MAX) :
    authenticated_belt.VerifiedBeltQuorumGuard.step st (.ProposeOrRetryEpoch e msg rd rt) =
      .ok (beltAfterPropose st e msg, .Ok .EpochBound) := by
  have hcore := belt_core_propose_of_mealy (belt_mealy_propose_fresh msg hc hnr hge hwin hmax)
  have hp := (belt_not_corrupt_facts hc).1
  have hvalid : decide (rt = rt) = true := decide_eq_true rfl
  unfold authenticated_belt.VerifiedBeltQuorumGuard.step
  dsimp only
  unfold authenticated_belt.VerifiedBeltQuorumGuard.propose_or_retry_epoch
  rw [hwal]
  simp only [bind_eq_result_bind, result_bind_ok]
  rw [ct_eq_bytes32_spec, hvalid]
  simp only [result_bind_ok,
    pants_and_quorum_guards.BeltQuorumCore.impl.has_bound_epoch,
    pants_and_quorum_guards.BeltQuorumCore.impl.bound_epoch,
    pants_and_quorum_guards.BeltQuorumCore.is_poisoned, hcore]
  (repeat' (first | split | simp only [result_bind_ok])) <;>
    first
      | rfl
      | exact absurd ⟨by assumption, by (apply Eq.symm; assumption)⟩ hnr
      | (exfalso; simp_all)

/-- A first acknowledgment by an in-range custodian with the tag the guard computes is
    recorded: the counter grows by one and exactly that custodian's bit is set. -/
theorem belt_step_ack_fresh (st : authenticated_belt.VerifiedBeltQuorumGuard)
    (ep : Std.U64) (msg : Array Std.U8 32#usize) (id : Std.U8)
    (tag key : Array Std.U8 32#usize)
    (hid : id.val < st.inner.n.val) (h64 : id.val < 64)
    (hkey : Array.index_usize st.custodian_keys (UScalar.cast .Usize id) = .ok key)
    (htag : authenticated_belt.custodian_ack_tag key st.guard_key_commit ep msg id = .ok tag)
    (hc : beltGuardCorrupt st.inner = false) (hb : st.inner.has_bound_epoch = true)
    (he : ep = st.inner.bound_epoch) (hm : msg = st.inner.bound_msg_tag)
    (hbit : st.ack_bitmap.bv.getLsbD id.val = false)
    (hcnt : st.inner.ack_count.val < st.inner.n.val) :
    authenticated_belt.VerifiedBeltQuorumGuard.step st (.RecordCustodianAck ep msg id tag) =
      .ok (beltAfterAck st id,
           .Ok (.AckRecorded ⟨st.inner.ack_count.bv + (1#u32).bv⟩)) := by
  subst he; subst hm
  have hcore := belt_core_ack_of_mealy (belt_mealy_ack_fresh hc hb hcnt)
  have hp := (belt_not_corrupt_facts hc).1
  have hc1 : (UScalar.cast .Usize id).val = id.val :=
    uscalar_cast_val_eq .Usize id (Nat.lt_of_lt_of_le id.bv.isLt (by decide))
  have hc2 : (UScalar.cast .Usize st.inner.n).val = st.inner.n.val :=
    uscalar_cast_val_eq .Usize st.inner.n (Nat.lt_of_lt_of_le st.inner.n.bv.isLt (by decide))
  have hin : ¬ UScalar.cast .Usize id >= UScalar.cast .Usize st.inner.n := by
    intro hx
    have hle := (UScalar.le_iff_val _ _).mp hx
    omega
  have h64' : ¬ id >= 64#u8 := by
    intro hx
    have hle : (64#u8 : Std.U8).val ≤ id.val := (UScalar.le_iff_val _ _).mp hx
    have h64v : (64#u8 : Std.U8).val = 64 := rfl
    omega
  have hshl : (1#u64 <<< id : Result Std.U64) = .ok (beltCustodianBit id) :=
    (hShlU_uscalar_eq (1#u64) id).trans (ite_eq_left h64)
  have hz := beltCustodianBit_and_eq_zero_of h64 hbit
  unfold authenticated_belt.VerifiedBeltQuorumGuard.step
  dsimp only
  unfold authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack
  simp only [pants_and_quorum_guards.BeltQuorumCore.impl.n,
    pants_and_quorum_guards.BeltQuorumCore.is_poisoned,
    pants_and_quorum_guards.BeltQuorumCore.impl.has_bound_epoch,
    pants_and_quorum_guards.BeltQuorumCore.impl.bound_epoch,
    pants_and_quorum_guards.BeltQuorumCore.impl.bound_msg_tag,
    pants_and_quorum_guards.BeltQuorumCore.impl.ack_count,
    ct_eq_bytes32_spec, bind_eq_result_bind, result_bind_ok, lift_eq_ok]
  rw [ite_eq_right hin, ite_eq_right h64', hkey]
  simp only [result_bind_ok]
  rw [htag]
  simp only [result_bind_ok, hshl, hcore]
  (repeat' (first | split | simp only [result_bind_ok])) <;>
    first
      | rfl
      | (exfalso; simp_all)

/-- With at least `q` acknowledgments recorded for the bound epoch, authorization is
    granted for exactly that epoch and message. -/
theorem belt_step_authorize_granted (st : authenticated_belt.VerifiedBeltQuorumGuard)
    (hc : beltGuardCorrupt st.inner = false) (hb : st.inner.has_bound_epoch = true)
    (hq : st.inner.q.val ≤ st.inner.ack_count.val)
    (hphase : st.inner.phase ≠ .SharesAuthorized) :
    authenticated_belt.VerifiedBeltQuorumGuard.step st
        (.AuthorizeShares st.inner.bound_epoch st.inner.bound_msg_tag) =
      .ok (beltAfterGrant st,
           .Ok (.SharesAuthorized { _private := (), authorized_epoch := st.inner.bound_epoch,
                                    msg_tag := st.inner.bound_msg_tag,
                                    certified_acks := st.inner.ack_count })) := by
  have hcore := belt_core_authorize_of_mealy (belt_mealy_authorize_granted hc hb hq hphase)
  have hp := (belt_not_corrupt_facts hc).1
  unfold authenticated_belt.VerifiedBeltQuorumGuard.step
  dsimp only
  unfold authenticated_belt.VerifiedBeltQuorumGuard.authorize_shares
  rw [hcore]
  simp only [bind_eq_result_bind, result_bind_ok,
    pants_and_quorum_guards.BeltQuorumCore.is_poisoned]
  (repeat' (first | split | simp only [result_bind_ok])) <;>
    first
      | rfl
      | (exfalso; simp_all)

/-- **Completeness of a two-custodian round.** From any uncorrupted guard whose quorum
    is at most two, a fresh in-window epoch proposed with the guard's own WAL receipt
    tag and acknowledged by two distinct in-range custodians with the guard's own
    acknowledgment tags is certified, with exactly those two signers. -/
theorem belt_two_custodian_round_certifies
    (st : authenticated_belt.VerifiedBeltQuorumGuard) (e : Std.U64)
    (msg rd rt tagA tagB keyA keyB : Array Std.U8 32#usize) (a b : Std.U8)
    (hc : beltGuardCorrupt st.inner = false)
    (hq : st.inner.q.val ≤ 2)
    (hnr : ¬ (st.inner.has_bound_epoch = true ∧ e = st.inner.bound_epoch))
    (hge : st.inner.next_epoch.val ≤ e.val)
    (hwin : e.val - st.inner.next_epoch.val ≤ st.inner.max_jump_window.val)
    (hmax : e ≠ core.num.U64.MAX)
    (ha : a.val < st.inner.n.val) (hb : b.val < st.inner.n.val) (hab : a.val ≠ b.val)
    (ha64 : a.val < 64) (hb64 : b.val < 64)
    (hwal : authenticated_belt.wal_receipt_tag st.wal_key st.guard_key_commit e msg rd = .ok rt)
    (hkA : Array.index_usize st.custodian_keys (UScalar.cast .Usize a) = .ok keyA)
    (htA : authenticated_belt.custodian_ack_tag keyA st.guard_key_commit e msg a = .ok tagA)
    (hkB : Array.index_usize st.custodian_keys (UScalar.cast .Usize b) = .ok keyB)
    (htB : authenticated_belt.custodian_ack_tag keyB st.guard_key_commit e msg b = .ok tagB) :
    BeltTraceReachable st
      [.ProposeOrRetryEpoch e msg rd rt, .RecordCustodianAck e msg a tagA,
       .RecordCustodianAck e msg b tagB, .AuthorizeShares e msg]
      [⟨{ _private := (), authorized_epoch := e, msg_tag := msg, certified_acks := 2#u32 },
        (0#u64 ||| beltCustodianBit a) ||| beltCustodianBit b⟩]
      (beltAfterGrant (beltAfterAck (beltAfterAck (beltAfterPropose st e msg) a) b)) := by
  have hlt := u64_val_succ_lt_of_ne_max hmax
  have hc1 : beltGuardCorrupt (beltAfterPropose st e msg).inner = false :=
    belt_not_corrupt_fresh msg hc hlt
  have hc2 : beltGuardCorrupt (beltAfterAck (beltAfterPropose st e msg) a).inner = false :=
    belt_not_corrupt_set_ack_count _ hc1
  have hc3 : beltGuardCorrupt
      (beltAfterAck (beltAfterAck (beltAfterPropose st e msg) a) b).inner = false :=
    belt_not_corrupt_set_ack_count _ hc2
  have hcnt0 : (beltAfterPropose st e msg).inner.ack_count.val <
      (beltAfterPropose st e msg).inner.n.val := by
    show (0 : Nat) < st.inner.n.val
    omega
  have hcnt1 : (beltAfterAck (beltAfterPropose st e msg) a).inner.ack_count.val <
      (beltAfterAck (beltAfterPropose st e msg) a).inner.n.val := by
    show (1 : Nat) < st.inner.n.val
    omega
  have hbitB : (beltAfterAck (beltAfterPropose st e msg) a).ack_bitmap.bv.getLsbD b.val =
      false := by
    show ((0#u64 : Std.U64).bv ||| (beltCustodianBit a).bv).getLsbD b.val = false
    rw [BitVec.getLsbD_or, belt_zero_getLsbD, beltCustodianBit_getLsbD a ha64]
    simp [hab]
  have hq3 : (beltAfterAck (beltAfterAck (beltAfterPropose st e msg) a) b).inner.q.val ≤
      (beltAfterAck (beltAfterAck (beltAfterPropose st e msg) a) b).inner.ack_count.val := by
    show st.inner.q.val ≤ 2
    exact hq
  refine .bound (belt_step_propose_fresh st e msg rd rt hwal hc hnr hge hwin hmax) ?_
  refine .acked (belt_step_ack_fresh (beltAfterPropose st e msg) e msg a tagA keyA
    ha ha64 hkA htA hc1 rfl rfl rfl (belt_zero_getLsbD _) hcnt0) ?_
  refine .acked (belt_step_ack_fresh (beltAfterAck (beltAfterPropose st e msg) a) e msg b
    tagB keyB hb hb64 hkB htB hc2 rfl rfl rfl hbitB hcnt1) ?_
  refine .certified (belt_step_authorize_granted
    (beltAfterAck (beltAfterAck (beltAfterPropose st e msg) a) b) hc3 rfl hq3 (by intro h; cases h)) ?_
  exact .nil _

/-- State after one certified two-custodian round. -/
abbrev beltRoundEnd (st : authenticated_belt.VerifiedBeltQuorumGuard) (e : Std.U64)
    (msg : Array Std.U8 32#usize) (a b : Std.U8) :
    authenticated_belt.VerifiedBeltQuorumGuard :=
  beltAfterGrant (beltAfterAck (beltAfterAck (beltAfterPropose st e msg) a) b)

/-- **Liveness of a two-custodian round.** Inputs that make the round succeed always
    exist: the tag functions are total, so the guard is never vacuously safe for
    parties that can compute its tags. -/
theorem belt_two_custodian_round_exists
    (st : authenticated_belt.VerifiedBeltQuorumGuard) (e : Std.U64)
    (msg : Array Std.U8 32#usize) (a b : Std.U8)
    (hc : beltGuardCorrupt st.inner = false)
    (hq : st.inner.q.val ≤ 2)
    (hnr : ¬ (st.inner.has_bound_epoch = true ∧ e = st.inner.bound_epoch))
    (hge : st.inner.next_epoch.val ≤ e.val)
    (hwin : e.val - st.inner.next_epoch.val ≤ st.inner.max_jump_window.val)
    (hmax : e ≠ core.num.U64.MAX)
    (ha : a.val < st.inner.n.val) (hb : b.val < st.inner.n.val) (hab : a.val ≠ b.val)
    (ha64 : a.val < 64) (hb64 : b.val < 64) :
    ∃ acts : List BeltAction, acts.length = 4 ∧
      BeltTraceReachable st acts
        [⟨{ _private := (), authorized_epoch := e, msg_tag := msg, certified_acks := 2#u32 },
          (0#u64 ||| beltCustodianBit a) ||| beltCustodianBit b⟩]
        (beltRoundEnd st e msg a b) := by
  obtain ⟨rt, hwal⟩ := belt_wal_receipt_tag_total st.wal_key st.guard_key_commit e msg msg
  have hca : (UScalar.cast .Usize a).val = a.val :=
    uscalar_cast_val_eq .Usize a (Nat.lt_of_lt_of_le a.bv.isLt (by decide))
  have hcb : (UScalar.cast .Usize b).val = b.val :=
    uscalar_cast_val_eq .Usize b (Nat.lt_of_lt_of_le b.bv.isLt (by decide))
  obtain ⟨keyA, hkA⟩ := array_index_total st.custodian_keys (UScalar.cast .Usize a)
    (by rw [hca]; exact ha64)
  obtain ⟨keyB, hkB⟩ := array_index_total st.custodian_keys (UScalar.cast .Usize b)
    (by rw [hcb]; exact hb64)
  obtain ⟨tagA, htA⟩ := belt_custodian_ack_tag_total keyA st.guard_key_commit e msg a
  obtain ⟨tagB, htB⟩ := belt_custodian_ack_tag_total keyB st.guard_key_commit e msg b
  exact ⟨_, rfl, belt_two_custodian_round_certifies st e msg msg rt tagA tagB keyA keyB a b
    hc hq hnr hge hwin hmax ha hb hab ha64 hb64 hwal hkA htA hkB htB⟩

/-! ## 10. Inhabited multi-turn witnesses and mutation teeth -/

abbrev beltWitnessBytes : Array Std.U8 32#usize := Array.repeat 32#usize 0#u8

abbrev beltWitnessKeys : Array (Array Std.U8 32#usize) 64#usize :=
  Array.repeat 64#usize beltWitnessBytes

/-- The guard `new_validated` builds for `n = 3, t = 2, f = 0, q = 2`, first epoch 10. -/
abbrev beltWitnessState0 : authenticated_belt.VerifiedBeltQuorumGuard :=
  { inner :=
      { n := 3#u32, t := 2#u32, f := 0#u32, q := 2#u32, global_liveness_mode := false,
        next_epoch := 10#u64, max_jump_window := 4#u64, phase := .Idle,
        has_bound_epoch := false, bound_epoch := 0#u64, bound_msg_tag := beltWitnessBytes,
        ack_count := 0#u32, poisoned := false },
    guard_key_commit := beltWitnessBytes,
    custodian_keys := beltWitnessKeys,
    wal_key := beltWitnessBytes,
    ack_bitmap := 0#u64 }

/-- **Inhabitedness of the multi-turn theorems.** A guard built by `new_validated`
    runs a twelve-call trace that certifies epochs 10, 11 and 12 with the custodian
    pairs `{0, 1}`, `{1, 2}` and `{0, 2}`. The hypotheses of
    `belt_trace_fork_free_and_epoch_monotone` are therefore satisfiable with three
    certificates, and its conclusions are not vacuous. -/
theorem inhabited_belt_trace_three_certificates :
    ∃ (stF : authenticated_belt.VerifiedBeltQuorumGuard) (acts : List BeltAction)
      (certs : List BeltCert),
      authenticated_belt.VerifiedBeltQuorumGuard.new_validated
        3#u32 2#u32 0#u32 2#u32 false 10#u64 4#u64
        beltWitnessBytes beltWitnessKeys beltWitnessBytes = .ok (.Ok beltWitnessState0) ∧
      BeltTraceReachable beltWitnessState0 acts certs stF ∧
      certs.length ≥ 3 ∧
      certs.map (fun c => c.grant.authorized_epoch.val) = [10, 11, 12] ∧
      certs.map (fun c => beltPopcount c.signers) = [2, 2, 2] := by
  have hnew : authenticated_belt.VerifiedBeltQuorumGuard.new_validated
      3#u32 2#u32 0#u32 2#u32 false 10#u64 4#u64
      beltWitnessBytes beltWitnessKeys beltWitnessBytes = .ok (.Ok beltWitnessState0) := by
    unfold authenticated_belt.VerifiedBeltQuorumGuard.new_validated
      pants_and_quorum_guards.BeltQuorumCore.new_validated
    rw [validate_belt_quorum_config_eq]
    rfl
  obtain ⟨acts1, _, h1⟩ := belt_two_custodian_round_exists beltWitnessState0 10#u64
    beltWitnessBytes 0#u8 1#u8 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨acts2, _, h2⟩ := belt_two_custodian_round_exists
    (beltRoundEnd beltWitnessState0 10#u64 beltWitnessBytes 0#u8 1#u8) 11#u64
    beltWitnessBytes 1#u8 2#u8 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨acts3, _, h3⟩ := belt_two_custodian_round_exists
    (beltRoundEnd (beltRoundEnd beltWitnessState0 10#u64 beltWitnessBytes 0#u8 1#u8)
      11#u64 beltWitnessBytes 1#u8 2#u8) 12#u64
    beltWitnessBytes 0#u8 2#u8 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨_, _, _, hnew, h1.append (h2.append h3), by decide, by decide, by decide⟩

/-- The wrapper's fresh-acknowledgment path with its bitmap test removed: forward the
    acknowledgment to the core and set the custodian's bit, without first checking
    whether the bit is already set. -/
@[expose]
def beltAckWithoutDedup (st : authenticated_belt.VerifiedBeltQuorumGuard) (ep : Std.U64)
    (msg : Array Std.U8 32#usize) (id : Std.U8) :
    Result (authenticated_belt.VerifiedBeltQuorumGuard ×
      core.result.Result Std.U32 pants_and_quorum_guards.PantsGuardError) := do
  let (inner, r) ←
    pants_and_quorum_guards.BeltQuorumCore.record_custodian_ack st.inner ep msg
  ok ({ st with inner := inner, ack_bitmap := st.ack_bitmap ||| beltCustodianBit id }, r)

/-- The mutant accepts an acknowledgment whether or not the custodian has signed
    already: the extracted core counts calls, not custodians. -/
theorem beltAckWithoutDedup_accepts (st : authenticated_belt.VerifiedBeltQuorumGuard)
    (id : Std.U8) (hc : beltGuardCorrupt st.inner = false)
    (hb : st.inner.has_bound_epoch = true)
    (hcnt : st.inner.ack_count.val < st.inner.n.val) :
    beltAckWithoutDedup st st.inner.bound_epoch st.inner.bound_msg_tag id =
      .ok (beltAfterAck st id, .Ok ⟨st.inner.ack_count.bv + (1#u32).bv⟩) := by
  unfold beltAckWithoutDedup
  rw [belt_core_ack_of_mealy (belt_mealy_ack_fresh hc hb hcnt)]
  rfl

/-- A guard with `n = 3, f = 1, q = 3` that has bound epoch 10 and recorded nothing. -/
abbrev beltToothState : authenticated_belt.VerifiedBeltQuorumGuard :=
  { inner :=
      { n := 3#u32, t := 2#u32, f := 1#u32, q := 3#u32, global_liveness_mode := false,
        next_epoch := 11#u64, max_jump_window := 4#u64, phase := .EpochBoundPendingQuorum,
        has_bound_epoch := true, bound_epoch := 10#u64, bound_msg_tag := beltWitnessBytes,
        ack_count := 0#u32, poisoned := false },
    guard_key_commit := beltWitnessBytes,
    custodian_keys := beltWitnessKeys,
    wal_key := beltWitnessBytes,
    ack_bitmap := 0#u64 }

/-- `#tooth`: the signer bitmap test is load-bearing. Starting from a state that
    satisfies `BeltGuardInv`, custodian `0` alone replays its acknowledgment three
    times through the mutant `beltAckWithoutDedup`. The extracted `step` then grants
    a certificate with `certified_acks = 3` while the signer bitmap holds one
    custodian. Both `BeltGuardInv` and the conclusion `q ≤ beltPopcount signers` of
    `belt_trace_certs_quorum` fail, with `q = 3`. -/
theorem tooth_belt_ack_without_signer_dedup_forges_quorum :
    BeltGuardInv 3#u32 3#u32 beltToothState ∧
    beltAckWithoutDedup beltToothState 10#u64 beltWitnessBytes 0#u8 =
      .ok (beltAfterAck beltToothState 0#u8, .Ok 1#u32) ∧
    beltAckWithoutDedup (beltAfterAck beltToothState 0#u8) 10#u64 beltWitnessBytes 0#u8 =
      .ok (beltAfterAck (beltAfterAck beltToothState 0#u8) 0#u8, .Ok 2#u32) ∧
    beltAckWithoutDedup (beltAfterAck (beltAfterAck beltToothState 0#u8) 0#u8)
        10#u64 beltWitnessBytes 0#u8 =
      .ok (beltAfterAck (beltAfterAck (beltAfterAck beltToothState 0#u8) 0#u8) 0#u8,
           .Ok 3#u32) ∧
    authenticated_belt.VerifiedBeltQuorumGuard.step
        (beltAfterAck (beltAfterAck (beltAfterAck beltToothState 0#u8) 0#u8) 0#u8)
        (.AuthorizeShares 10#u64 beltWitnessBytes) =
      .ok (beltAfterGrant
             (beltAfterAck (beltAfterAck (beltAfterAck beltToothState 0#u8) 0#u8) 0#u8),
           .Ok (.SharesAuthorized { _private := (), authorized_epoch := 10#u64,
                                    msg_tag := beltWitnessBytes,
                                    certified_acks := 3#u32 })) ∧
    beltPopcount
      (beltAfterAck (beltAfterAck (beltAfterAck beltToothState 0#u8) 0#u8) 0#u8).ack_bitmap
        = 1 ∧
    ¬ BeltGuardInv 3#u32 3#u32
      (beltAfterAck (beltAfterAck (beltAfterAck beltToothState 0#u8) 0#u8) 0#u8) := by
  refine ⟨⟨rfl, rfl, belt_zero_count_popcount, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have hi' : (0#u64 : Std.U64).bv.getLsbD i = true := hi
    rw [belt_zero_getLsbD] at hi'
    cases hi'
  · exact beltAckWithoutDedup_accepts beltToothState 0#u8 (by decide) rfl (by decide)
  · exact beltAckWithoutDedup_accepts (beltAfterAck beltToothState 0#u8) 0#u8
      (by decide) rfl (by decide)
  · exact beltAckWithoutDedup_accepts (beltAfterAck (beltAfterAck beltToothState 0#u8) 0#u8)
      0#u8 (by decide) rfl (by decide)
  · exact belt_step_authorize_granted
      (beltAfterAck (beltAfterAck (beltAfterAck beltToothState 0#u8) 0#u8) 0#u8)
      (by decide) rfl (by decide) (by intro h; cases h)
  · decide
  · intro h
    exact absurd h.2.2.1 (by decide)

/-! ## 11. Velocity guard and BDOZ burn latch: accepted paths and inhabited traces -/

theorem velocity_max_sub_spent (spent : Std.U128) :
    ∃ rem : Std.U128,
      (policy_and_addr.MAX_VELOCITY_U128 - spent : Result Std.U128) = .ok rem ∧
      rem.val = 340282366920938463463374607431768211455 - spent.val := by
  have hb : spent.val ≤ 340282366920938463463374607431768211455 :=
    Nat.le_of_lt_succ spent.bv.isLt
  refine ⟨⟨(340282366920938463463374607431768211455#u128).bv - spent.bv⟩, ?_, ?_⟩
  · unfold policy_and_addr.MAX_VELOCITY_U128
    have hb' : spent.val ≤ (340282366920938463463374607431768211455#u128).val := hb
    simp only [hSub_uscalar_eq, hb', ↓reduceIte]
  · change ((340282366920938463463374607431768211455#u128).bv - spent.bv).toNat = _
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hb)]
    rfl

/-- `authorize_spend` returns on every state and request: the checked addition is only
    reached when the amount fits under `u128::MAX - spent_units`. -/
theorem velocity_authorize_spend_total (st : policy_and_addr.StatefulVelocityGuard)
    (req : policy_and_addr.VelocitySpendRequest) :
    ∃ p, policy_and_addr.StatefulVelocityGuard.authorize_spend st req = .ok p := by
  obtain ⟨rem, hrem, hremv⟩ := velocity_max_sub_spent st.spent_units
  unfold policy_and_addr.StatefulVelocityGuard.authorize_spend
  rw [ct_eq_bytes32_spec, ct_eq_bytes32_spec, hrem]
  simp only [bind_eq_result_bind, result_bind_ok]
  by_cases hov : req.amount_units > rem
  · simp only [eq_true hov, ↓reduceIte]
    (repeat' (first | split | simp only [result_bind_ok])) <;> exact ⟨_, rfl⟩
  · have hle : req.amount_units.val ≤ rem.val :=
      Nat.le_of_not_lt (fun h => hov ((UScalar.lt_iff_val _ _).mpr h))
    have hsp : st.spent_units.val ≤ 340282366920938463463374607431768211455 :=
      Nat.le_of_lt_succ st.spent_units.bv.isLt
    obtain ⟨c, hc, _⟩ := checked_add_val st.spent_units req.amount_units
      (by show st.spent_units.val + req.amount_units.val < 2 ^ 128; omega)
    simp only [eq_false hov, hc, result_bind_ok, ↓reduceIte]
    (repeat' (first | split | simp only [result_bind_ok])) <;> exact ⟨_, rfl⟩

/-- Every accepting step of the pure velocity specification is realised by the extracted
    `authorize_spend`. -/
theorem velocity_spend_of_step
    {st st' : policy_and_addr.StatefulVelocityGuard}
    {req : policy_and_addr.VelocitySpendRequest} {amt : Std.U128}
    (hs : velocitySpendStep st req = some (st', amt)) :
    policy_and_addr.StatefulVelocityGuard.authorize_spend st req = .ok (st', .Ok amt) := by
  obtain ⟨⟨s2, r⟩, hcore⟩ := velocity_authorize_spend_total st req
  cases r with
  | Ok amt2 =>
    have h2 := mirSim_ok_step_eq velocity_spend_step_sim hcore
    dsimp only [velocitySpendMealy, MealySpec.ofPure] at h2
    rw [hs] at h2
    injection h2 with h2
    injection h2 with h3 h4
    rw [hcore, h3, h4]
  | Err e =>
    have h2 := (mirSim_err_step_eq velocity_spend_step_sim hcore).1
    dsimp only [velocitySpendMealy, MealySpec.ofPure] at h2
    rw [hs] at h2
    cases h2

/-- A request with matching pins, the current window, a fresh nonce and an amount that
    fits under the cap is authorized. -/
theorem velocity_spend_accepts (st : policy_and_addr.StatefulVelocityGuard)
    (req : policy_and_addr.VelocitySpendRequest)
    (hc : (decide (st.policy_pin = req.policy_pin) &&
           decide (st.authority_pin = req.authority_pin) &&
           decide (req.window_id = st.window_id) &&
           decide (st.last_nonce.val < req.nonce.val) &&
           decide (st.spent_units.val + req.amount_units.val ≤ st.cap_units.val)) = true) :
    policy_and_addr.StatefulVelocityGuard.authorize_spend st req =
      .ok ({ st with spent_units := ⟨st.spent_units.bv + req.amount_units.bv⟩,
                     last_nonce := req.nonce }, .Ok req.amount_units) := by
  apply velocity_spend_of_step
  unfold velocitySpendStep
  rw [ite_eq_left hc]

/-- A rotation with matching pins to a strictly larger window id is accepted and
    resets the spent counter. -/
theorem velocity_rotate_accepts (st : policy_and_addr.StatefulVelocityGuard) (w : Std.U64)
    (p a : Array Std.U8 32#usize)
    (hp : st.policy_pin = p) (ha : st.authority_pin = a) (hlt : st.window_id.val < w.val) :
    policy_and_addr.StatefulVelocityGuard.rotate_window st w p a =
      .ok ({ st with window_id := w, spent_units := 0#u128 }, .Ok ()) := by
  obtain ⟨st', res, heq, hiff, hok, _⟩ := rotate_window_resets_spent_monotone_spec st w p a
  have hres := hiff.mpr ⟨hp, ha, hlt⟩
  rw [heq, hres, hok hres]

/-- Inhabitedness of `velocity_multiwindow_cap_conservation`: a spend of 60 under a cap
    of 100, a rotation from window 7 to window 8, and a second spend of 60. Each window
    stays under the cap while the two windows together exceed it, which is what a
    rolling window is for. -/
theorem inhabited_velocity_trace_two_windows :
    ∃ (st0 stF : policy_and_addr.StatefulVelocityGuard) (acts : List VelocityAction)
      (acc : List policy_and_addr.VelocitySpendRequest),
      policy_and_addr.StatefulVelocityGuard.new_window 7#u64 100#u128
        (Array.repeat 32#usize 0#u8) (Array.repeat 32#usize 0#u8) = .ok st0 ∧
      VelocityTraceReachable st0 acts acc stF ∧
      acts.length = 3 ∧
      windowSpendNat 7#u64 acc = 60 ∧ windowSpendNat 8#u64 acc = 60 := by
  exact ⟨_, _, _, _, rfl,
    VelocityTraceReachable.spend_ok
      (velocity_spend_accepts _
        { window_id := 7#u64, nonce := 1#u64, amount_units := 60#u128,
          policy_pin := Array.repeat 32#usize 0#u8,
          authority_pin := Array.repeat 32#usize 0#u8 } (by decide))
    (VelocityTraceReachable.rotate_ok
      (velocity_rotate_accepts _ 8#u64 (Array.repeat 32#usize 0#u8)
        (Array.repeat 32#usize 0#u8) rfl rfl (by decide))
    (VelocityTraceReachable.spend_ok
      (velocity_spend_accepts _
        { window_id := 8#u64, nonce := 2#u64, amount_units := 60#u128,
          policy_pin := Array.repeat 32#usize 0#u8,
          authority_pin := Array.repeat 32#usize 0#u8 } (by decide))
    (VelocityTraceReachable.nil _))),
    rfl, by decide, by decide⟩

/-- Inhabitedness of the burn-latch theorems: an unburned verifier session rejects an
    empty opening batch, is burned by that rejection, and rejects again. -/
theorem inhabited_bdoz_burn_trace (s : tower.BdozVerifierSession2Lane)
    (batch : tower.BdozCommittedBatchOpening2Lane) (hb : s.burned = false) :
    ∃ sF, BdozBurnTrace s
        [(batch, ⟨[], by decide⟩), (batch, ⟨[], by decide⟩)] [false, false] sF ∧
      sF.burned = true := by
  have h1 : tower.verify_mac_2lane_with_burn s batch ⟨[], by decide⟩ =
      .ok ({ alpha_lanes := Array.make 2#usize [0#u128, 0#u128], burned := true }, false) := by
    unfold tower.verify_mac_2lane_with_burn
    rw [verify_mac_2lane_rejects_empty]
    simp [hb]
  have h2 := (verify_mac_2lane_burn_irreversible
    { alpha_lanes := Array.make 2#usize [0#u128, 0#u128], burned := true }
    batch ⟨[], by decide⟩).1 rfl
  exact ⟨_, .call h1 (.call h2 (.nil _)), rfl⟩


/-- The extracted verifier has no successful-opening consumption transition: every
accepted opening can be replayed any number of times, with exactly the same state.
This is a counterexample to imposing a no-replay interpretation on `BdozBurnTrace`. -/
theorem bdoz_accepted_opening_replays
    {s s' : tower.BdozVerifierSession2Lane}
    {batch : tower.BdozCommittedBatchOpening2Lane}
    {openings : Slice tower.BdozWireOpening2Lane}
    (h : tower.verify_mac_2lane_with_burn s batch openings = .ok (s', true))
    (k : Nat) :
    BdozBurnTrace s (List.replicate k (batch, openings)) (List.replicate k true) s := by
  have hs := (bdoz_burn_step_inv h).1 rfl
  rw [hs.2] at h
  induction k with
  | zero => exact .nil s
  | succ k ih =>
    simpa only [List.replicate_succ] using BdozBurnTrace.call h ih

/-- The generated constructor has no old-state argument or session tombstone. Even
for a poisoned session ID it returns a clean round-one session. Cross-session no-reset
therefore needs an extracted registry, not a stronger theorem about this constructor. -/
theorem rss_constructor_reinitializes_poisoned_id
    (old : rss_cut_session.RssCutGateSession) (mask : Array Std.U8 32#usize)
    (_hpoisoned : old.poisoned = true) :
    ∃ fresh, rss_cut_session.RssCutGateSession.new_round1_committed old.session_id mask =
      .ok fresh ∧ fresh.session_id = old.session_id ∧ fresh.poisoned = false ∧
      fresh.phase = .Round1MaskCommitted := by
  exact ⟨_, rfl, rfl, rfl, rfl⟩


/-- The four accumulators of the generated opening loop. -/
abbrev BdozBatchFoldState := Std.U8 × tower.Tower128 × tower.Tower128 × tower.Tower128

def bdozBatchFoldStep (a : BdozBatchFoldState) (item : tower.BdozWireOpening2Lane) :
    BdozBatchFoldState :=
  (if item.chal_weight = 0#u128 then 0#u8 else a.1,
   a.2.1 ^^^ pureTower128Mul item.chal_weight (UScalar.cast .U128 item.opened_value),
   a.2.2.1 ^^^ pureTower128Mul item.chal_weight (item.key_lanes.val.getD 0 0#u128),
   a.2.2.2 ^^^ pureTower128Mul item.chal_weight (item.key_lanes.val.getD 1 0#u128))

/-- Arbitrary-length masked-value and two-key fold, with nonzero-weight tracking. -/
def bdozBatchFold : List tower.BdozWireOpening2Lane → BdozBatchFoldState → BdozBatchFoldState
  | [], a => a
  | item :: rest, a => bdozBatchFold rest (bdozBatchFoldStep a item)

private theorem bdoz_loopFuel_suffix
    (openings : Slice tower.BdozWireOpening2Lane)
    (xs : List tower.BdozWireOpening2Lane) (i : Std.Usize)
    (w : Std.U8) (v k0 k1 : tower.Tower128)
    (hsuffix : openings.val.drop i.val = xs) :
    loopFuel (xs.length + 1)
      (fun (w, v, k0, k1, i) => tower.verify_mac_2lane_loop.body openings w v k0 k1 i)
      (w, v, k0, k1, i) = .ok (bdozBatchFold xs (w, v, k0, k1)) := by
  induction xs generalizing i w v k0 k1 with
  | nil =>
    have hlen := congrArg List.length hsuffix
    simp only [List.length_drop, List.length_nil] at hlen
    have hstop : ¬ i < Slice.len openings := by
      change ¬ i.val < (Slice.len openings).val
      rw [Slice.len_val]
      omega
    have hbody : tower.verify_mac_2lane_loop.body openings w v k0 k1 i =
        .ok (.done (w, v, k0, k1)) := by
      unfold tower.verify_mac_2lane_loop.body
      exact ite_eq_right_of_eq_false _ _ (eq_false hstop)
    refine (loopFuel_succ _ _ _).trans ?_
    show Result.bind (tower.verify_mac_2lane_loop.body openings w v k0 k1 i) _ = _
    rw [hbody]
    rfl
  | cons item rest ih =>
    have hlen := congrArg List.length hsuffix
    simp only [List.length_drop, List.length_cons] at hlen
    have hlt : i.val < openings.val.length := by omega
    have hgo : i < Slice.len openings := by
      change i.val < (Slice.len openings).val
      rw [Slice.len_val]
      exact hlt
    have hsplit := List.drop_eq_getElem_cons hlt
    rw [hsuffix] at hsplit
    have hitem := (List.cons.inj hsplit).1.symm
    have htail := (List.cons.inj hsplit).2.symm
    have hindex : Slice.index_usize openings i = .ok item := by
      simp only [Slice.index_usize, dite_eq_left hlt, hitem]
    have hk0 : Array.index_usize item.key_lanes 0#usize =
        .ok (item.key_lanes.val.getD 0 0#u128) :=
      array_index_getD item.key_lanes 0#usize 0#u128 (by decide)
    have hk1 : Array.index_usize item.key_lanes 1#usize =
        .ok (item.key_lanes.val.getD 1 0#u128) :=
      array_index_getD item.key_lanes 1#usize 0#u128 (by decide)
    obtain ⟨j, hj, hvj⟩ := checked_add_val i 1#usize (by
      change i.val + 1 < 2 ^ 64
      have hb : openings.val.length < 2 ^ 64 := by
        simpa only [← Slice.len_val] using (Slice.len openings).bv.isLt
      omega)
    change j.val = i.val + 1 at hvj
    have hrest : openings.val.drop j.val = rest := by rw [hvj]; exact htail
    have hbody : tower.verify_mac_2lane_loop.body openings w v k0 k1 i =
        .ok (.cont ((bdozBatchFoldStep (w, v, k0, k1) item).1,
          (bdozBatchFoldStep (w, v, k0, k1) item).2.1,
          (bdozBatchFoldStep (w, v, k0, k1) item).2.2.1,
          (bdozBatchFoldStep (w, v, k0, k1) item).2.2.2, j)) := by
      by_cases hw : item.chal_weight = 0#u128
      all_goals simp [tower.verify_mac_2lane_loop.body, hgo, hindex, hw,
        tower.embed_gf256_to_tower128, tower128_mul_eq_independent,
        tower.tower128_add, hk0, hk1, hj, bdozBatchFoldStep]
    refine (loopFuel_succ _ _ _).trans ?_
    show Result.bind (tower.verify_mac_2lane_loop.body openings w v k0 k1 i) _ = _
    rw [hbody]
    exact ih j _ _ _ _ hrest

/-- List induction over the generated MIR loop identifies all four accumulators,
for arbitrary slice length (including zero), rather than only singleton openings. -/
theorem bdoz_generated_loop_fold
    (openings : Slice tower.BdozWireOpening2Lane)
    (w : Std.U8) (v k0 k1 : tower.Tower128) :
    tower.verify_mac_2lane_loop openings w v k0 k1 0#usize =
      .ok (bdozBatchFold openings.val (w, v, k0, k1)) := by
  unfold tower.verify_mac_2lane_loop
  apply loop_ok_of_loopFuel (fuel := openings.val.length + 1)
  · simpa only [Slice.len_val] using usize_lt_loopMaxFuel (Slice.len openings)
  · exact bdoz_loopFuel_suffix openings openings.val 0#usize w v k0 k1 rfl

/-- The generated loop's weight byte is exactly the conjunction of nonzero weights. -/
theorem bdoz_batch_fold_weights (xs : List tower.BdozWireOpening2Lane)
    (w : Std.U8) (v k0 k1 : tower.Tower128) :
    (bdozBatchFold xs (w, v, k0, k1)).1 = 1#u8 ↔
      w = 1#u8 ∧ ∀ item ∈ xs, item.chal_weight ≠ 0#u128 := by
  induction xs generalizing w v k0 k1 with
  | nil => simp [bdozBatchFold]
  | cons item rest ih =>
    change (bdozBatchFold rest _).1 = 1#u8 ↔ _
    dsimp only [bdozBatchFoldStep]
    rw [ih]
    by_cases hw : item.chal_weight = 0#u128
    · simp [hw]
    · simp [hw]

/-- Initial accumulators include the supplied mask and both mask keys. -/
def bdozBatchAccum (batch : tower.BdozCommittedBatchOpening2Lane)
    (openings : Slice tower.BdozWireOpening2Lane) : BdozBatchFoldState :=
  bdozBatchFold openings.val (1#u8, batch.mask_value,
    batch.mask_key_lanes.val.getD 0 0#u128, batch.mask_key_lanes.val.getD 1 0#u128)

/-- Exact acceptance for arbitrary batches, expressed as both folded MAC residuals.
The hash equality is an execution premise, not a hash-binding or timing assumption.
Commitment-before-challenge and mask freshness are absent from the extracted state. -/
theorem bdoz_verify_arbitrary_batch
    (alphas : Array tower.Tower128 2#usize)
    (batch : tower.BdozCommittedBatchOpening2Lane)
    (openings : Slice tower.BdozWireOpening2Lane) (tag : Array Std.U8 32#usize)
    (htag : tower.bdoz_commit_masked_tag batch.session_id batch.round_id
      (bdozBatchAccum batch openings).2.1 batch.peer_masked_mac_lanes batch.open_nonce = .ok tag) :
    tower.verify_mac_2lane alphas batch openings = .ok (decide (
      openings.val ≠ [] ∧
      (∀ item ∈ openings.val, item.chal_weight ≠ 0#u128) ∧
      tag = batch.tag_commitment ∧
      ((batch.peer_masked_mac_lanes.val.getD 0 0#u128 ^^^
          ((bdozBatchAccum batch openings).2.2.1 ^^^
            pureTower128Mul (alphas.val.getD 0 0#u128) (bdozBatchAccum batch openings).2.1)) |||
       (batch.peer_masked_mac_lanes.val.getD 1 0#u128 ^^^
          ((bdozBatchAccum batch openings).2.2.2 ^^^
            pureTower128Mul (alphas.val.getD 1 0#u128) (bdozBatchAccum batch openings).2.1))) = 0#u128)) := by
  have mk0 : Array.index_usize batch.mask_key_lanes 0#usize =
      .ok (batch.mask_key_lanes.val.getD 0 0#u128) :=
    array_index_getD batch.mask_key_lanes 0#usize 0#u128 (by decide)
  have mk1 : Array.index_usize batch.mask_key_lanes 1#usize =
      .ok (batch.mask_key_lanes.val.getD 1 0#u128) :=
    array_index_getD batch.mask_key_lanes 1#usize 0#u128 (by decide)
  have a0 : Array.index_usize alphas 0#usize = .ok (alphas.val.getD 0 0#u128) :=
    array_index_getD alphas 0#usize 0#u128 (by decide)
  have a1 : Array.index_usize alphas 1#usize = .ok (alphas.val.getD 1 0#u128) :=
    array_index_getD alphas 1#usize 0#u128 (by decide)
  have m0 : Array.index_usize batch.peer_masked_mac_lanes 0#usize =
      .ok (batch.peer_masked_mac_lanes.val.getD 0 0#u128) :=
    array_index_getD batch.peer_masked_mac_lanes 0#usize 0#u128 (by decide)
  have m1 : Array.index_usize batch.peer_masked_mac_lanes 1#usize =
      .ok (batch.peer_masked_mac_lanes.val.getD 1 0#u128) :=
    array_index_getD batch.peer_masked_mac_lanes 1#usize 0#u128 (by decide)
  have hw : (bdozBatchAccum batch openings).1 = 1#u8 ↔
      ∀ item ∈ openings.val, item.chal_weight ≠ 0#u128 := by
    simpa only [bdozBatchAccum, eq_self_iff_true, true_and] using
      bdoz_batch_fold_weights openings.val 1#u8 batch.mask_value
        (batch.mask_key_lanes.val.getD 0 0#u128) (batch.mask_key_lanes.val.getD 1 0#u128)
  have hloop : tower.verify_mac_2lane_loop openings 1#u8 batch.mask_value
      (batch.mask_key_lanes.val.getD 0 0#u128) (batch.mask_key_lanes.val.getD 1 0#u128)
      0#usize = .ok (bdozBatchAccum batch openings) :=
    bdoz_generated_loop_fold openings 1#u8 batch.mask_value _ _
  rcases hA : bdozBatchAccum batch openings with ⟨wok, ms, fk0, fk1⟩
  rw [hA] at htag hw hloop
  dsimp only at htag hw ⊢
  unfold tower.verify_mac_2lane
  simp only [core.slice.Slice.is_empty, bind_eq_result_bind, result_bind_ok]
  by_cases he : openings.val = []
  · simp [he]
  · have hne : openings.val.isEmpty = false := List.isEmpty_eq_false_iff.mpr he
    simp only [hne, Bool.false_eq_true, ite_false, mk0, mk1, result_bind_ok]
    rw [hloop]
    simp only [result_bind_ok, htag, ct_eq_bytes32_spec, a0, a1, m0, m1,
      tower128_mul_eq_independent, tower.tower128_add,
      bind_eq_result_bind, lift_eq_ok]
    by_cases hw' : wok = 1#u8
    · have hall := hw.mp hw'
      rw [ite_eq_left_of_eq_true _ _ (eq_true hw')]
      by_cases ht : tag = batch.tag_commitment
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (decide_eq_true ht))]
        exact congrArg Result.ok
          (decide_eq_decide.mpr ⟨fun h => ⟨he, hall, ht, h⟩, fun h => h.2.2.2⟩)
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => ht (of_decide_eq_true h)))]
        exact congrArg Result.ok (decide_eq_false (fun h => ht h.2.2.1)).symm
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hw')]
      exact congrArg Result.ok (decide_eq_false (fun h => hw' (hw.mpr h.2.1))).symm


private theorem bdoz_accepted_call_checks_batch
    {s s' : tower.BdozVerifierSession2Lane}
    {batch : tower.BdozCommittedBatchOpening2Lane}
    {openings : Slice tower.BdozWireOpening2Lane}
    (h : tower.verify_mac_2lane_with_burn s batch openings = .ok (s', true)) :
    tower.verify_mac_2lane s.alpha_lanes batch openings = .ok true := by
  have hb := ((bdoz_burn_step_inv h).1 rfl).1
  cases hv : tower.verify_mac_2lane s.alpha_lanes batch openings with
  | fail e =>
    simp [tower.verify_mac_2lane_with_burn, hb, hv] at h
    cases h
  | div =>
    simp [tower.verify_mac_2lane_with_burn, hb, hv] at h
    cases h
  | ok b =>
    cases b with
    | false => simp [tower.verify_mac_2lane_with_burn, hb, hv] at h
    | true => rfl

/-- Arbitrarily many successful batches all satisfy the generated opening verifier
under the same original keys. Together with `bdoz_verify_arbitrary_batch` this gives
folded-value/key soundness for every batch in the list. It does not imply freshness. -/
theorem bdoz_successful_trace_checks_every_batch
    {s t : tower.BdozVerifierSession2Lane}
    {calls : List (tower.BdozCommittedBatchOpening2Lane × Slice tower.BdozWireOpening2Lane)}
    {verdicts : List Bool}
    (ht : BdozBurnTrace s calls verdicts t)
    (ha : ∀ b ∈ verdicts, b = true) :
    ∀ call ∈ calls, tower.verify_mac_2lane s.alpha_lanes call.1 call.2 = .ok true := by
  induction ht with
  | nil s => intro call hc; cases hc
  | @call s s' t batch openings b calls verdicts h htail ih =>
    have hb : b = true := ha b (List.mem_cons_self)
    subst b
    have hs : s' = s := ((bdoz_burn_step_inv h).1 rfl).2
    subst s'
    have hrest := ih (fun b hb => ha b (List.mem_cons_of_mem _ hb))
    intro call hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact bdoz_accepted_call_checks_batch h
    · exact hrest call hc

end qsag_verified.proofs
