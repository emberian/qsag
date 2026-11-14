module

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

One statement in the usual wording of this property is false for the extracted code and
is not claimed: certificate epochs are not strictly increasing. `authorize_shares` has
no phase test, so a second authorization request for the bound epoch returns a second
grant for the same epoch and message (possibly with more signers). What holds, and what
`belt_trace_certs_monotone` states, is that a later certificate has a strictly larger
epoch or the same epoch and the same message.
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
    o = .SharesAuthorized { authorized_epoch := s.bound_epoch,
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
          · have hf : beltQuorumMealy.step s (.AuthorizeShares reqEp reqTag) =
                some ({ s with phase := .SharesAuthorized },
                      .SharesAuthorized { authorized_epoch := s.bound_epoch,
                                          msg_tag := s.bound_msg_tag,
                                          certified_acks := s.ack_count }) := by
              dsimp only [beltQuorumMealy]; rw [hc]; simp [hb, he, ht, hq]
            rw [hf] at h
            injection h with h
            injection h with h1 h2
            exact ⟨rfl, hb, he, ht, Nat.le_of_not_lt hq, h1.symm, h2.symm⟩
        · simp [hb, he, ht] at h2
      · simp [hb, he] at h2
    · simp [hb] at h2

/-- A refused step either leaves an uncorrupted core exactly as it was, or poisons it. -/
