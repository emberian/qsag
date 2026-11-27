module
import all QsagVerified.Funs

public import QsagVerified.Proofs.Common
import all QsagVerified.Proofs.Adrs

public section

namespace qsag_verified.proofs

open Aeneas Aeneas.Std Result ControlFlow Error
open qsag_verified

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

attribute [-simp] BitVec.getLsbD_eq_getElem
attribute [local simp] UScalar.val UScalarTy.numBits

set_option genSizeOf false in
set_option genInjectivity false in
/-- One observable protocol call, retaining domain rejections in the history. -/
inductive EpochTurn where
  | acquire (request : threshold.EpochSignRequest)
      (result : core.result.Result threshold.EpochAuthGrant threshold.EpochLatchError)
  | advance (request : threshold.EpochRequest)
      (result : core.result.Result Std.U64 threshold.EpochLatchError)

@[expose]
def traceGrants : List EpochTurn → List threshold.EpochAuthGrant
  | [] => []
  | .acquire _ (.Ok g) :: ts => g :: traceGrants ts
  | _ :: ts => traceGrants ts

/-- Executable MIR transitions, with rejections leaving the persisted state unchanged. -/
inductive EpochTrace : threshold.EpochLatch → List EpochTurn → threshold.EpochLatch → Prop where
  | nil (st) : EpochTrace st [] st
  | acquire_ok {st mid final req g ts}
      (step : threshold.EpochLatch.acquire_or_retry st req = .ok (.Ok (mid, g)))
      (tail : EpochTrace mid ts final) : EpochTrace st (.acquire req (.Ok g) :: ts) final
  | acquire_err {st final req e ts}
      (step : threshold.EpochLatch.acquire_or_retry st req = .ok (.Err e))
      (tail : EpochTrace st ts final) : EpochTrace st (.acquire req (.Err e) :: ts) final
  | advance_ok {st mid final req ep ts}
      (step : threshold.epoch_latch_advance st req = .ok (.Ok (mid, ep)))
      (tail : EpochTrace mid ts final) : EpochTrace st (.advance req (.Ok ep) :: ts) final
  | advance_err {st final req e ts}
      (step : threshold.epoch_latch_advance st req = .ok (.Err e))
      (tail : EpochTrace st ts final) : EpochTrace st (.advance req (.Err e) :: ts) final


/-! ## Initial write-ahead-log invariant -/

@[expose]
def WellFormedWal (st : threshold.EpochLatch) : Prop :=
  st.next_epoch.val ≤ st.max_epoch.val ∧
    ∀ b, st.last_bound = .Bound b → b.epoch.val < st.next_epoch.val

theorem epoch_latch_new_spec (max_epoch : Std.U64) (key_epoch_id : Array Std.U8 32#usize) :
    ∃ st, threshold.EpochLatch.new max_epoch key_epoch_id = .ok st ∧
      WellFormedWal st ∧ st.key_epoch_id = key_epoch_id ∧
      st.max_epoch = max_epoch ∧ st.next_epoch = 0#u64 ∧ st.last_bound = .Unset := by
  refine ⟨⟨0#u64, max_epoch, key_epoch_id, .Unset⟩, rfl, ?_, rfl, rfl, rfl, rfl⟩
  constructor
  · exact Nat.zero_le _
  · intro b h; cases h

/-- Every successful recovery supplies the invariant required by the transition theorems. -/
theorem epoch_latch_from_cursor_well_formed (next limit : Std.U64)
    (key : Array Std.U8 32#usize) (last : threshold.LastBoundEpoch) (st : threshold.EpochLatch)
    (accepted : threshold.EpochLatch.from_cursor next limit key last = .ok (.Ok st)) :
    WellFormedWal st := by
  unfold threshold.EpochLatch.from_cursor at accepted
  by_cases over : next > limit
  · simp [over] at accepted
  have hn : next.val ≤ limit.val := Nat.le_of_not_gt (fun h => over ((UScalar.lt_iff_val _ _).mpr h))
  cases last with
  | Unset =>
    simp [over] at accepted
    subst st
    exact ⟨hn, fun _ h => by cases h⟩
  | Bound b =>
    by_cases stale : b.epoch ≥ next
    · simp [over, stale] at accepted
    · simp [over, stale] at accepted
      subst st
      refine ⟨hn, ?_⟩
      intro record h
      cases h
      exact Nat.lt_of_not_ge (fun h => stale ((UScalar.le_iff_val _ _).mpr h))

private theorem epoch_increment_ok (st : threshold.EpochLatch)
    (h : st.next_epoch < st.max_epoch) :
    ∃ next : Std.U64, (st.next_epoch + 1#u64 : Result Std.U64) = .ok next ∧
      next.val = st.next_epoch.val + 1 := by
  have hm : st.max_epoch.val < 2 ^ 64 := st.max_epoch.bv.isLt
  have hn : st.next_epoch.val < st.max_epoch.val := (UScalar.lt_iff_val _ _).mp h
  have hb : st.next_epoch.val + 1 < 2 ^ 64 := Nat.lt_of_le_of_lt hn hm
  refine ⟨⟨st.next_epoch.bv + (1#u64).bv⟩, ?_, ?_⟩
  · simp [hAdd_uscalar_eq, hb]
  · change (st.next_epoch.bv + (1#u64).bv).toNat = st.next_epoch.val + 1
    rw [BitVec.toNat_add]
    change (_ + _) % (2 ^ 64) = _
    exact Nat.mod_eq_of_lt hb

@[expose]
def EpochAdvanceError (st : threshold.EpochLatch) (req : threshold.EpochRequest)
    (e : threshold.EpochLatchError) : Prop :=
  (st.key_epoch_id ≠ req.key_epoch_id ∧ e = .KeyBindingMismatch) ∨
  (st.key_epoch_id = req.key_epoch_id ∧ req.requested_epoch ≠ st.next_epoch ∧
    e = .NonSequentialEpoch st.next_epoch req.requested_epoch) ∨
  (st.key_epoch_id = req.key_epoch_id ∧ req.requested_epoch = st.next_epoch ∧
    st.next_epoch >= st.max_epoch ∧ e = .TreeExhausted st.max_epoch)

theorem epoch_latch_advance_spec (st : threshold.EpochLatch)
    (req : threshold.EpochRequest) (hw : WellFormedWal st) :
    ∃ res, threshold.epoch_latch_advance st req = .ok res ∧
      match res with
      | .Err e => EpochAdvanceError st req e
      | .Ok (st', assigned_epoch) =>
        WellFormedWal st' ∧ assigned_epoch = st.next_epoch ∧
        st'.next_epoch.val = st.next_epoch.val + 1 ∧
        st'.last_bound = .Unset ∧ st'.key_epoch_id = st.key_epoch_id ∧
        st'.max_epoch = st.max_epoch ∧
        req.key_epoch_id = st.key_epoch_id ∧ req.requested_epoch = st.next_epoch := by
  unfold threshold.epoch_latch_advance
  rw [ct_eq_bytes32_spec]
  simp only [bind_eq_result_bind, result_bind_ok, decide_eq_true_eq]
  by_cases hk : st.key_epoch_id = req.key_epoch_id
  · simp only [hk, ite_true]
    cases hl : st.last_bound with
    | Unset =>
      by_cases he : req.requested_epoch = st.next_epoch
      · simp only [he, bne_self_eq_false, Bool.false_eq_true, ite_false]
        by_cases hg : st.next_epoch >= st.max_epoch
        · simp only [hg, ite_true]
          exact ⟨_, rfl, Or.inr (Or.inr ⟨hk, he, hg, rfl⟩)⟩
        · have hlt : st.next_epoch < st.max_epoch := by
            apply (UScalar.lt_iff_val _ _).mpr
            have hn : ¬ st.max_epoch.val ≤ st.next_epoch.val := by
              intro h; exact hg ((UScalar.le_iff_val _ _).mpr h)
            exact Nat.lt_of_not_ge hn
          obtain ⟨next, hn, hv⟩ := epoch_increment_ok st hlt
          simp only [hg, ite_false, hn, result_bind_ok]
          refine ⟨_, rfl, ?_, rfl, hv, ?_, rfl, rfl, by trivial, by trivial⟩
          · constructor
            · change next.val ≤ st.max_epoch.val
              have hlt' := (UScalar.lt_iff_val _ _).mp hlt
              rw [hv]; exact hlt'
            · intro b hb
              cases hb
          · rfl
      · have hb : (req.requested_epoch != st.next_epoch) = true := by simp [he]
        simp only [hb, ite_true]
        exact ⟨_, rfl, Or.inr (Or.inl ⟨hk, he, rfl⟩)⟩
    | Bound bound =>
      have hc : ¬ bound.epoch >= st.next_epoch := by
        intro h
        have hlt := hw.2 bound hl
        have hle := (UScalar.le_iff_val _ _).mp h
        exact Nat.not_lt_of_ge hle hlt
      simp only [hc, ite_false]
      by_cases he : req.requested_epoch = st.next_epoch
      · simp only [he, bne_self_eq_false, Bool.false_eq_true, ite_false]
        by_cases hg : st.next_epoch >= st.max_epoch
        · simp only [hg, ite_true]
          exact ⟨_, rfl, Or.inr (Or.inr ⟨hk, he, hg, rfl⟩)⟩
        · have hlt : st.next_epoch < st.max_epoch := by
            apply (UScalar.lt_iff_val _ _).mpr
            have hn : ¬ st.max_epoch.val ≤ st.next_epoch.val := by
              intro h; exact hg ((UScalar.le_iff_val _ _).mpr h)
            exact Nat.lt_of_not_ge hn
          obtain ⟨next, hn, hv⟩ := epoch_increment_ok st hlt
          simp only [hg, ite_false, hn, result_bind_ok]
          refine ⟨_, rfl, ?_, rfl, hv, ?_, rfl, rfl, by trivial, by trivial⟩
          · constructor
            · change next.val ≤ st.max_epoch.val
              have hlt' := (UScalar.lt_iff_val _ _).mp hlt
              rw [hv]; exact hlt'
            · intro b hb
              cases hb
          · rfl
      · have hb : (req.requested_epoch != st.next_epoch) = true := by simp [he]
        simp only [hb, ite_true]
        exact ⟨_, rfl, Or.inr (Or.inl ⟨hk, he, rfl⟩)⟩
  · simp only [hk, ite_false]
    exact ⟨_, rfl, Or.inl ⟨hk, rfl⟩⟩

/-- Complete successful acquire-or-retry transition, including the persisted binding. -/
@[expose]
def EpochAcquireSuccess (st : threshold.EpochLatch) (req : threshold.EpochSignRequest)
    (st' : threshold.EpochLatch) (g : threshold.EpochAuthGrant) : Prop :=
  WellFormedWal st' ∧ st'.key_epoch_id = st.key_epoch_id ∧ st'.max_epoch = st.max_epoch ∧
  st.key_epoch_id = req.key_epoch_id ∧ g.authorized_epoch = req.requested_epoch ∧
  g.msg_digest = req.msg_digest ∧ g.r_rand = req.deterministic_r_rand ∧
  st'.last_bound = .Bound ⟨g.authorized_epoch, g.msg_digest, g.r_rand⟩ ∧
  ((g.is_idempotent_retry = true ∧ st' = st) ∨
   (g.is_idempotent_retry = false ∧ g.authorized_epoch = st.next_epoch ∧
    st'.next_epoch.val = st.next_epoch.val + 1))

private theorem epoch_fresh_success (st : threshold.EpochLatch)
    (req : threshold.EpochSignRequest) (next : Std.U64)
    (hk : st.key_epoch_id = req.key_epoch_id) (he : req.requested_epoch = st.next_epoch)
    (hlt : st.next_epoch.val < st.max_epoch.val) (hv : next.val = st.next_epoch.val + 1) :
    EpochAcquireSuccess st req
      { st with next_epoch := next, last_bound := .Bound ⟨st.next_epoch, req.msg_digest, req.deterministic_r_rand⟩ }
      ⟨(), st.next_epoch, req.msg_digest, req.deterministic_r_rand, false⟩ := by
  refine ⟨⟨?_, ?_⟩, rfl, rfl, hk, he.symm, rfl, rfl, rfl, Or.inr ⟨rfl, rfl, hv⟩⟩
  · change next.val ≤ st.max_epoch.val
    rw [hv]; exact hlt
  · intro b hb
    cases hb
    change st.next_epoch.val < next.val
    rw [hv]; exact Nat.lt_succ_self _

@[expose]
def EpochFreshError (st : threshold.EpochLatch) (requested : Std.U64)
    (e : threshold.EpochLatchError) : Prop :=
  (requested ≠ st.next_epoch ∧ e = .NonSequentialEpoch st.next_epoch requested) ∨
  (requested = st.next_epoch ∧ st.next_epoch >= st.max_epoch ∧ e = .TreeExhausted st.max_epoch)

@[expose]
def EpochAcquireError (st : threshold.EpochLatch) (req : threshold.EpochSignRequest)
    (e : threshold.EpochLatchError) : Prop :=
  if st.key_epoch_id = req.key_epoch_id then
    match st.last_bound with
    | .Unset => EpochFreshError st req.requested_epoch e
    | .Bound b =>
      if req.requested_epoch = b.epoch then
        (b.msg_digest ≠ req.msg_digest ∧ e = .EpochEquivocationAttempt b.epoch) ∨
        (b.msg_digest = req.msg_digest ∧ b.r_rand ≠ req.deterministic_r_rand ∧
          e = .RetryRandomizerMismatch b.epoch)
      else EpochFreshError st req.requested_epoch e
  else e = .KeyBindingMismatch

theorem epoch_latch_acquire_or_retry_spec (st : threshold.EpochLatch)
    (req : threshold.EpochSignRequest) (hw : WellFormedWal st) :
    ∃ res, threshold.EpochLatch.acquire_or_retry st req = .ok res ∧
      match res with
      | .Err e => EpochAcquireError st req e
      | .Ok (st', grant) => EpochAcquireSuccess st req st' grant := by
  unfold threshold.EpochLatch.acquire_or_retry
  rw [ct_eq_bytes32_spec]
  simp only [bind_eq_result_bind, result_bind_ok, decide_eq_true_eq]
  by_cases hk : st.key_epoch_id = req.key_epoch_id
  · simp only [hk, ite_true]
    have fresh : ∃ res : core.result.Result (threshold.EpochLatch × threshold.EpochAuthGrant) threshold.EpochLatchError,
        (if req.requested_epoch != st.next_epoch then
          Result.ok (.Err (threshold.EpochLatchError.NonSequentialEpoch st.next_epoch req.requested_epoch))
        else if st.next_epoch >= st.max_epoch then
          Result.ok (.Err (threshold.EpochLatchError.TreeExhausted st.max_epoch))
        else do
          let next ← st.next_epoch + 1#u64
          Result.ok (.Ok ({ st with next_epoch := next, last_bound := .Bound ⟨st.next_epoch, req.msg_digest, req.deterministic_r_rand⟩ },
            ⟨(), st.next_epoch, req.msg_digest, req.deterministic_r_rand, false⟩))) = .ok res ∧
        match res with
        | .Err e => EpochFreshError st req.requested_epoch e
        | .Ok (st', g) => EpochAcquireSuccess st req st' g := by
      by_cases he : req.requested_epoch = st.next_epoch
      · simp only [he, bne_self_eq_false, Bool.false_eq_true, ite_false]
        by_cases hg : st.next_epoch >= st.max_epoch
        · simp only [hg, ite_true]
          exact ⟨_, rfl, Or.inr ⟨rfl, hg, rfl⟩⟩
        · have hlt : st.next_epoch.val < st.max_epoch.val := by
            have : ¬ st.max_epoch.val ≤ st.next_epoch.val := by
              intro h; exact hg ((UScalar.le_iff_val _ _).mpr h)
            exact Nat.lt_of_not_ge this
          obtain ⟨next, hn, hv⟩ := epoch_increment_ok st ((UScalar.lt_iff_val _ _).mpr hlt)
          simp only [hg, ite_false, hn, bind_eq_result_bind, result_bind_ok]
          exact ⟨_, rfl, epoch_fresh_success st req next hk he hlt hv⟩
      · have hb : (req.requested_epoch != st.next_epoch) = true := by simp [he]
        simp only [hb, ite_true]
        exact ⟨_, rfl, Or.inl ⟨he, rfl⟩⟩
    cases hl : st.last_bound with
    | Unset => simpa only [EpochAcquireError, hk, ite_true, hl, bind_eq_result_bind] using fresh
    | Bound b =>
      have hc : ¬ b.epoch >= st.next_epoch := by
        intro h
        have hlt := hw.2 b hl
        have hle := (UScalar.le_iff_val _ _).mp h
        exact Nat.not_lt_of_ge hle hlt
      simp only [hc, ite_false]
      by_cases he : req.requested_epoch = b.epoch
      · simp only [he, ite_true, ct_eq_bytes32_spec, result_bind_ok, decide_eq_true_eq]
        by_cases hm : b.msg_digest = req.msg_digest
        · simp only [hm, ite_true]
          by_cases hr : b.r_rand = req.deterministic_r_rand
          · simp only [hr, ite_true]
            refine ⟨_, rfl, hw, rfl, rfl, hk, he.symm, rfl, rfl, ?_, Or.inl ⟨rfl, rfl⟩⟩
            simpa only [← hm, ← hr] using hl
          · simp only [hr, ite_false]
            exact ⟨_, rfl, by simp [EpochAcquireError, hk, hl, he, hm, hr]⟩
        · simp only [hm, ite_false]
          exact ⟨_, rfl, by simp [EpochAcquireError, hk, hl, he, hm]⟩
      · simp only [he, ite_false]
        simpa only [EpochAcquireError, hk, ite_true, hl, he, ite_false, bind_eq_result_bind] using fresh
  · simp only [hk, ite_false]
    exact ⟨_, rfl, by simp [EpochAcquireError, hk]⟩

theorem epoch_latch_key_binding_mismatch (st : threshold.EpochLatch)
    (req : threshold.EpochSignRequest) (hk : st.key_epoch_id ≠ req.key_epoch_id) :
    threshold.EpochLatch.acquire_or_retry st req = .ok (.Err .KeyBindingMismatch) := by
  simp [threshold.EpochLatch.acquire_or_retry, ct_eq_bytes32_spec, hk]

theorem epoch_latch_equivocation_rejected (st : threshold.EpochLatch)
    (req : threshold.EpochSignRequest) (b : threshold.BoundEpochRecord)
    (hw : WellFormedWal st) (hk : st.key_epoch_id = req.key_epoch_id)
    (hb : st.last_bound = .Bound b) (he : req.requested_epoch = b.epoch)
    (hm : b.msg_digest ≠ req.msg_digest) :
    threshold.EpochLatch.acquire_or_retry st req = .ok (.Err (.EpochEquivocationAttempt b.epoch)) := by
  have hc : ¬ b.epoch >= st.next_epoch := by
    intro h
    have hlt := hw.2 b hb
    have hle := (UScalar.le_iff_val _ _).mp h
    exact Nat.not_lt_of_ge hle hlt
  simp [threshold.EpochLatch.acquire_or_retry, ct_eq_bytes32_spec, hk, hb, hc, he, hm]

theorem epoch_latch_randomizer_mismatch (st : threshold.EpochLatch)
    (req : threshold.EpochSignRequest) (b : threshold.BoundEpochRecord)
    (hw : WellFormedWal st) (hk : st.key_epoch_id = req.key_epoch_id)
    (hb : st.last_bound = .Bound b) (he : req.requested_epoch = b.epoch)
    (hm : b.msg_digest = req.msg_digest) (hr : b.r_rand ≠ req.deterministic_r_rand) :
    threshold.EpochLatch.acquire_or_retry st req = .ok (.Err (.RetryRandomizerMismatch b.epoch)) := by
  have hc : ¬ b.epoch >= st.next_epoch := by
    intro h
    have hlt := hw.2 b hb
    have hle := (UScalar.le_iff_val _ _).mp h
    exact Nat.not_lt_of_ge hle hlt
  simp [threshold.EpochLatch.acquire_or_retry, ct_eq_bytes32_spec, hk, hb, hc, he, hm, hr]

private theorem epoch_acquire_success_of_eq {st st' : threshold.EpochLatch}
    {req : threshold.EpochSignRequest} {g : threshold.EpochAuthGrant}
    (hw : WellFormedWal st)
    (h : threshold.EpochLatch.acquire_or_retry st req = .ok (.Ok (st', g))) :
    EpochAcquireSuccess st req st' g := by
  obtain ⟨res, hr, hp⟩ := epoch_latch_acquire_or_retry_spec st req hw
  rw [h] at hr
  cases hr
  exact hp

private theorem epoch_advance_success_of_eq {st st' : threshold.EpochLatch}
    {req : threshold.EpochRequest} {ep : Std.U64} (hw : WellFormedWal st)
    (h : threshold.epoch_latch_advance st req = .ok (.Ok (st', ep))) :
    WellFormedWal st' ∧ ep = st.next_epoch ∧ st'.next_epoch.val = st.next_epoch.val + 1 ∧
      st'.last_bound = .Unset ∧ st'.key_epoch_id = st.key_epoch_id ∧ st'.max_epoch = st.max_epoch := by
  obtain ⟨res, hr, hp⟩ := epoch_latch_advance_spec st req hw
  rw [h] at hr
  cases hr
  exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1⟩

private def GrantsSafe (st : threshold.EpochLatch) (gs : List threshold.EpochAuthGrant) : Prop :=
  (∀ g ∈ gs, g.authorized_epoch.val < st.next_epoch.val) ∧
  (∀ g ∈ gs, ∀ b, st.last_bound = .Bound b → g.authorized_epoch = b.epoch →
    g.msg_digest = b.msg_digest ∧ g.r_rand = b.r_rand) ∧
  (∀ g1 ∈ gs, ∀ g2 ∈ gs, g1.authorized_epoch = g2.authorized_epoch →
    g1.msg_digest = g2.msg_digest ∧ g1.r_rand = g2.r_rand)

private theorem grants_safe_acquire {st st' : threshold.EpochLatch}
    {req : threshold.EpochSignRequest} {g : threshold.EpochAuthGrant}
    {gs : List threshold.EpochAuthGrant} (hs : GrantsSafe st gs)
    (hp : EpochAcquireSuccess st req st' g) : GrantsSafe st' (gs ++ [g]) := by
  rcases hp with ⟨hw, _, _, _, _, _, _, hb, hd⟩
  have hg : g.authorized_epoch.val < st'.next_epoch.val := hw.2 _ hb
  have hmono : st.next_epoch.val ≤ st'.next_epoch.val := by
    rcases hd with ⟨_, rfl⟩ | ⟨_, _, hn⟩
    · exact Nat.le_refl _
    · rw [hn]; exact Nat.le_succ _
  have agree (old : threshold.EpochAuthGrant) (ho : old ∈ gs)
      (he : old.authorized_epoch = g.authorized_epoch) :
      old.msg_digest = g.msg_digest ∧ old.r_rand = g.r_rand := by
    rcases hd with ⟨_, rfl⟩ | ⟨_, hepoch, _⟩
    · exact hs.2.1 old ho _ hb he
    · have hlt := hs.1 old ho
      rw [he, hepoch] at hlt
      exact False.elim (Nat.lt_irrefl _ hlt)
  refine ⟨?_, ?_, ?_⟩
  · intro old ho
    rcases List.mem_append.mp ho with ho | ho
    · exact Nat.lt_of_lt_of_le (hs.1 old ho) hmono
    · have : old = g := List.mem_singleton.mp ho
      subst old; exact hg
  · intro old ho b hbound he
    rw [hb] at hbound
    cases hbound
    rcases List.mem_append.mp ho with ho | ho
    · exact agree old ho he
    · have : old = g := List.mem_singleton.mp ho
      subst old; exact ⟨rfl, rfl⟩
  · intro g1 h1 g2 h2 he
    rcases List.mem_append.mp h1 with h1 | h1 <;>
      rcases List.mem_append.mp h2 with h2 | h2
    · exact hs.2.2 g1 h1 g2 h2 he
    · have : g2 = g := List.mem_singleton.mp h2
      subst g2; exact agree g1 h1 he
    · have : g1 = g := List.mem_singleton.mp h1
      subst g1
      obtain ⟨hm, hr⟩ := agree g2 h2 he.symm
      exact ⟨hm.symm, hr.symm⟩
    · have h1' : g1 = g := List.mem_singleton.mp h1
      have h2' : g2 = g := List.mem_singleton.mp h2
      subst g1; subst g2; exact ⟨rfl, rfl⟩

private theorem grants_safe_advance {st st' : threshold.EpochLatch}
    {gs : List threshold.EpochAuthGrant} (hs : GrantsSafe st gs)
    (hn : st'.next_epoch.val = st.next_epoch.val + 1) (hb : st'.last_bound = .Unset) :
    GrantsSafe st' gs := by
  refine ⟨?_, ?_, hs.2.2⟩
  · intro g hg
    have hlt := hs.1 g hg
    rw [hn]; exact Nat.lt_trans hlt (Nat.lt_succ_self _)
  · intro g hg b hbound he
    rw [hb] at hbound
    cases hbound

private theorem epoch_trace_preserves {st final : threshold.EpochLatch} {ts : List EpochTurn}
    (trace : EpochTrace st ts final) (hw : WellFormedWal st)
    (gs : List threshold.EpochAuthGrant) (hs : GrantsSafe st gs) :
    WellFormedWal final ∧ final.key_epoch_id = st.key_epoch_id ∧ final.max_epoch = st.max_epoch ∧
      GrantsSafe final (gs ++ traceGrants ts) := by
  induction trace generalizing gs with
  | nil => exact ⟨hw, rfl, rfl, by simpa only [traceGrants, List.append_nil] using hs⟩
  | acquire_ok step tail ih =>
    have hp := epoch_acquire_success_of_eq hw step
    obtain ⟨hw', hk, hm, hs'⟩ := ih hp.1 (gs ++ [_]) (grants_safe_acquire hs hp)
    refine ⟨hw', hk.trans hp.2.1, hm.trans hp.2.2.1, ?_⟩
    simpa only [traceGrants, List.append_assoc, List.singleton_append] using hs'
  | acquire_err step tail ih =>
    exact ih hw gs hs
  | advance_ok step tail ih =>
    obtain ⟨hw', _, hn, hb, hk, hm⟩ := epoch_advance_success_of_eq hw step
    obtain ⟨hw'', hk', hm', hs'⟩ := ih hw' gs (grants_safe_advance hs hn hb)
    exact ⟨hw'', hk'.trans hk, hm'.trans hm, hs'⟩
  | advance_err step tail ih =>
    exact ih hw gs hs


@[expose]
def traceAssignedEpochs : List EpochTurn → List Std.U64
  | [] => []
  | .advance _ (.Ok ep) :: ts => ep :: traceAssignedEpochs ts
  | _ :: ts => traceAssignedEpochs ts

private def AssignedSafe (st : threshold.EpochLatch)
    (gs : List threshold.EpochAuthGrant) (es : List Std.U64) : Prop :=
  (∀ ep ∈ es, ep.val < st.next_epoch.val) ∧
  es.Pairwise (fun a b => a ≠ b) ∧
  (∀ ep ∈ es, ∀ b, st.last_bound = .Bound b → b.epoch ≠ ep) ∧
  (∀ ep ∈ es, ∀ g ∈ gs, g.authorized_epoch ≠ ep)

private theorem assigned_safe_acquire {st st' : threshold.EpochLatch}
    {req : threshold.EpochSignRequest} {g : threshold.EpochAuthGrant}
    {gs : List threshold.EpochAuthGrant} {es : List Std.U64}
    (hs : AssignedSafe st gs es) (hp : EpochAcquireSuccess st req st' g) :
    AssignedSafe st' (gs ++ [g]) es := by
  have hb := hp.2.2.2.2.2.2.2.1
  have hd := hp.2.2.2.2.2.2.2.2
  have hn : st.next_epoch.val ≤ st'.next_epoch.val := by
    rcases hd with ⟨_, rfl⟩ | ⟨_, _, hn⟩
    · exact Nat.le_refl _
    · rw [hn]; exact Nat.le_succ _
  have hg (ep) (he : ep ∈ es) : g.authorized_epoch ≠ ep := by
    rcases hd with ⟨_, rfl⟩ | ⟨_, hepoch, _⟩
    · exact hs.2.2.1 ep he _ hb
    · intro h
      have hlt := hs.1 ep he
      rw [← h, hepoch] at hlt
      exact Nat.lt_irrefl _ hlt
  refine ⟨fun ep he => Nat.lt_of_lt_of_le (hs.1 ep he) hn, hs.2.1, ?_, ?_⟩
  · intro ep he b hbound
    rw [hb] at hbound
    cases hbound
    exact hg ep he
  · intro ep he old ho
    rcases List.mem_append.mp ho with ho | ho
    · exact hs.2.2.2 ep he old ho
    · have heq := List.mem_singleton.mp ho
      subst old
      exact hg ep he

private theorem assigned_safe_advance {st st' : threshold.EpochLatch} {ep : Std.U64}
    {gs : List threshold.EpochAuthGrant} {es : List Std.U64}
    (hg : GrantsSafe st gs) (hs : AssignedSafe st gs es)
    (he : ep = st.next_epoch) (hn : st'.next_epoch.val = st.next_epoch.val + 1)
    (hb : st'.last_bound = .Unset) : AssignedSafe st' gs (es ++ [ep]) := by
  have different (old : Std.U64) (ho : old ∈ es) : old ≠ ep := by
    intro h
    have hlt := hs.1 old ho
    rw [h, he] at hlt
    exact Nat.lt_irrefl _ hlt
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro old ho
    rw [hn]
    rcases List.mem_append.mp ho with ho | ho
    · exact Nat.lt_trans (hs.1 old ho) (Nat.lt_succ_self _)
    · rw [List.mem_singleton.mp ho, he]; exact Nat.lt_succ_self _
  · rw [List.pairwise_append]
    refine ⟨hs.2.1, by simp, ?_⟩
    intro old ho new hn
    rw [List.mem_singleton.mp hn]
    exact different old ho
  · intro old ho b hbound
    rw [hb] at hbound
    cases hbound
  · intro old ho g hmem
    rcases List.mem_append.mp ho with ho | ho
    · exact hs.2.2.2 old ho g hmem
    · rw [List.mem_singleton.mp ho, he]
      intro h
      have hlt := hg.1 g hmem
      rw [h] at hlt
      exact Nat.lt_irrefl _ hlt

private theorem assigned_trace_preserves {st final : threshold.EpochLatch} {ts : List EpochTurn}
    (trace : EpochTrace st ts final) (hw : WellFormedWal st)
    (gs : List threshold.EpochAuthGrant) (es : List Std.U64)
    (hg : GrantsSafe st gs) (hs : AssignedSafe st gs es) :
    AssignedSafe final (gs ++ traceGrants ts) (es ++ traceAssignedEpochs ts) := by
  induction trace generalizing gs es with
  | nil => simpa only [traceGrants, traceAssignedEpochs, List.append_nil] using hs
  | acquire_ok step tail ih =>
    have hp := epoch_acquire_success_of_eq hw step
    have h := ih hp.1 (gs ++ [_]) es (grants_safe_acquire hg hp) (assigned_safe_acquire hs hp)
    simpa only [traceGrants, traceAssignedEpochs, List.append_assoc, List.singleton_append] using h
  | acquire_err step tail ih => exact ih hw gs es hg hs
  | advance_ok step tail ih =>
    obtain ⟨hw', he, hn, hb, _, _⟩ := epoch_advance_success_of_eq hw step
    have h := ih hw' gs (es ++ [_]) (grants_safe_advance hg hn hb) (assigned_safe_advance hg hs he hn hb)
    simpa only [traceGrants, traceAssignedEpochs, List.append_assoc, List.singleton_append] using h
  | advance_err step tail ih => exact ih hw gs es hg hs

theorem epoch_latch_multiturn_safety (max_epoch : Std.U64)
    (key_epoch_id : Std.Array Std.U8 32#usize) (st0 st : threshold.EpochLatch)
    (turns : List EpochTurn)
    (hnew : threshold.EpochLatch.new max_epoch key_epoch_id = .ok st0)
    (trace : EpochTrace st0 turns st) :
    (WellFormedWal st ∧ st.key_epoch_id = key_epoch_id ∧ st.max_epoch = max_epoch) ∧
    (∀ g ∈ traceGrants turns,
      g.authorized_epoch.val < st.next_epoch.val ∧ st.next_epoch.val ≤ max_epoch.val) ∧
    (∀ g1 ∈ traceGrants turns, ∀ g2 ∈ traceGrants turns,
      g1.authorized_epoch = g2.authorized_epoch →
        g1.msg_digest = g2.msg_digest ∧ g1.r_rand = g2.r_rand) ∧
    (∀ ep ∈ traceAssignedEpochs turns, ep.val < st.next_epoch.val) ∧
    (traceAssignedEpochs turns).Pairwise (fun a b => a ≠ b) ∧
    (∀ ep ∈ traceAssignedEpochs turns, ∀ g ∈ traceGrants turns, g.authorized_epoch ≠ ep) := by
  obtain ⟨initial, hi, hw, hk, hm, _, _⟩ := epoch_latch_new_spec max_epoch key_epoch_id
  rw [hnew] at hi
  cases hi
  have hs : GrantsSafe st0 [] := by
    exact ⟨by simp, by simp, by simp⟩
  obtain ⟨hw', hk', hm', hs'⟩ := epoch_trace_preserves trace hw [] hs
  simp only [List.nil_append] at hs'
  have ha : AssignedSafe st0 [] [] := ⟨by simp, by simp, by simp, by simp⟩
  have ha' := assigned_trace_preserves trace hw [] [] hs ha
  simp only [List.nil_append] at ha'
  refine ⟨⟨hw', hk'.trans hk, hm'.trans hm⟩, ?_, hs'.2.2, ha'.1, ha'.2.1, ha'.2.2.2⟩
  intro g hg
  refine ⟨hs'.1 g hg, ?_⟩
  rw [← hm, ← hm']
  exact hw'.1

theorem epoch_latch_advance_seals_prior_epochs
    (st st' : threshold.EpochLatch) (req : threshold.EpochRequest)
    (ep : Std.U64) (req2 : threshold.EpochSignRequest)
    (hw : WellFormedWal st)
    (ha : threshold.epoch_latch_advance st req = .ok (.Ok (st', ep)))
    (hk : st'.key_epoch_id = req2.key_epoch_id)
    (he : req2.requested_epoch.val < st'.next_epoch.val) :
    threshold.EpochLatch.acquire_or_retry st' req2 =
      .ok (.Err (.NonSequentialEpoch st'.next_epoch req2.requested_epoch)) := by
  obtain ⟨res, hr, hp⟩ := epoch_latch_advance_spec st req hw
  have hres : res = .Ok (st', ep) := Result.ok.inj (hr.symm.trans ha)
  subst res
  have hs : st'.last_bound = .Unset := hp.2.2.2.1
  have hn : req2.requested_epoch ≠ st'.next_epoch := by
    intro h; rw [h] at he; exact Nat.lt_irrefl _ he
  simp [threshold.EpochLatch.acquire_or_retry, ct_eq_bytes32_spec, hk, hs, hn]

theorem tooth_goldilocks_noncanonical_rejected :
    goldilocks.goldilocks_from_canonical 18446744069414584321#u64 =
      .ok (.Err { raw_value := 18446744069414584321#u64 }) := by
  unfold goldilocks.goldilocks_from_canonical goldilocks.GOLDILOCKS_PRIME
  rfl

theorem tooth_gf256_nonboolean_rejected :
    tower.gf256_is_boolean_frobenius 2#u8 = .ok false := by
  decide

theorem tooth_shamir_duplicate_points_rejected :
    threshold.shamir_validate_points_gf256
      (Array.to_slice (Array.make 3#usize [1#u8, 1#u8, 2#u8])) = .ok false := by
  decide

theorem tooth_adrs_invalid_type_rejected :
    fips205.decode_fips205_adrs
      (Array.make 32#usize [
        0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
        0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
        0#u8, 0#u8, 0#u8, 7#u8, 0#u8, 0#u8, 0#u8, 0#u8,
        0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8]) = .ok none := by
  exact fips205_adrs_decode_invalid_type_none _ (by decide)

theorem tooth_tsw_wrong_sum_rejected :
    fips205.tsw_check_target_sum 16#u32 1#usize 8#u64
      (Array.to_slice (Array.make 1#usize [7#u32])) = .ok false := by
  unfold fips205.tsw_check_target_sum
  dsimp only
  have hlen : Slice.len (Std.Array.to_slice (Std.Array.make 1#usize [7#u32])) = 1#usize := rfl
  rw [hlen]
  simp only [bne_self_eq_false, Bool.false_eq_true, ite_false]
  unfold fips205.tsw_check_target_sum_loop
  apply loop_ok_of_loopFuel (fuel := 2) (by decide)
  rfl

@[expose]
def epochWitnessBytes : Array Std.U8 32#usize := Array.repeat 32#usize 0#u8
@[expose]
def epochWitnessChanged : Array Std.U8 32#usize := Array.repeat 32#usize 1#u8
def epochWitnessState : threshold.EpochLatch :=
  ⟨2#u64, 4#u64, epochWitnessBytes,
    .Bound ⟨1#u64, epochWitnessBytes, epochWitnessBytes⟩⟩

theorem tooth_epoch_equivocation_rejected :
    threshold.EpochLatch.acquire_or_retry epochWitnessState
      ⟨1#u64, epochWitnessBytes, epochWitnessChanged, epochWitnessBytes⟩ =
      .ok (.Err (.EpochEquivocationAttempt 1#u64)) := by
  have hn : epochWitnessBytes ≠ epochWitnessChanged := by decide
  simp [threshold.EpochLatch.acquire_or_retry, epochWitnessState, ct_eq_bytes32_spec, hn]

theorem tooth_epoch_r_rand_drift_rejected :
    threshold.EpochLatch.acquire_or_retry epochWitnessState
      ⟨1#u64, epochWitnessBytes, epochWitnessBytes, epochWitnessChanged⟩ =
      .ok (.Err (.RetryRandomizerMismatch 1#u64)) := by
  have hn : epochWitnessBytes ≠ epochWitnessChanged := by decide
  simp [threshold.EpochLatch.acquire_or_retry, epochWitnessState, ct_eq_bytes32_spec, hn]

theorem tooth_epoch_advance_seals_retry :
    threshold.epoch_latch_advance epochWitnessState ⟨2#u64, epochWitnessBytes⟩ =
      .ok (.Ok (⟨3#u64, 4#u64, epochWitnessBytes, .Unset⟩, 2#u64)) ∧
    threshold.EpochLatch.acquire_or_retry ⟨3#u64, 4#u64, epochWitnessBytes, .Unset⟩
      ⟨1#u64, epochWitnessBytes, epochWitnessBytes, epochWitnessBytes⟩ =
      .ok (.Err (.NonSequentialEpoch 3#u64 1#u64)) := by
  unfold epochWitnessState
  constructor
  · simp [threshold.epoch_latch_advance, ct_eq_bytes32_spec]
  · simp [threshold.EpochLatch.acquire_or_retry, ct_eq_bytes32_spec]


theorem tooth_epoch_acquire_and_retry_ok :
    threshold.EpochLatch.new 4#u64 epochWitnessBytes =
      .ok ⟨0#u64, 4#u64, epochWitnessBytes, .Unset⟩ ∧
    threshold.EpochLatch.acquire_or_retry ⟨0#u64, 4#u64, epochWitnessBytes, .Unset⟩
      ⟨0#u64, epochWitnessBytes, epochWitnessBytes, epochWitnessBytes⟩ =
      .ok (.Ok (⟨1#u64, 4#u64, epochWitnessBytes,
        .Bound ⟨0#u64, epochWitnessBytes, epochWitnessBytes⟩⟩,
        ⟨(), 0#u64, epochWitnessBytes, epochWitnessBytes, false⟩)) ∧
    threshold.EpochLatch.acquire_or_retry
      ⟨1#u64, 4#u64, epochWitnessBytes, .Bound ⟨0#u64, epochWitnessBytes, epochWitnessBytes⟩⟩
      ⟨0#u64, epochWitnessBytes, epochWitnessBytes, epochWitnessBytes⟩ =
      .ok (.Ok (⟨1#u64, 4#u64, epochWitnessBytes,
        .Bound ⟨0#u64, epochWitnessBytes, epochWitnessBytes⟩⟩,
        ⟨(), 0#u64, epochWitnessBytes, epochWitnessBytes, true⟩)) := by
  refine ⟨rfl, ?_, ?_⟩ <;>
    simp [threshold.EpochLatch.acquire_or_retry, ct_eq_bytes32_spec]


end qsag_verified.proofs
