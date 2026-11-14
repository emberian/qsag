module
public import QsagVerified.Proofs.MultiTurnMediationAndReachability

public section
namespace qsag_verified.proofs
open Aeneas Aeneas.Std Result
open qsag_verified
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

/-- An accepted ack either repeats a signer or inserts precisely its authenticated slot.
The epoch and message are checked against the current binding before either success. -/
theorem belt_ack_success_shape
    {st st' : authenticated_belt.VerifiedBeltQuorumGuard} {ep : Std.U64}
    {msg tag : Array Std.U8 32#usize} {id : Std.U8} {k : Std.U32}
    (h : authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack st ep msg id tag =
      .ok (st', .Ok k)) :
    st.inner.has_bound_epoch = true ∧ ep = st.inner.bound_epoch ∧
    msg = st.inner.bound_msg_tag ∧
    (st' = st ∨ ∃ inner,
      pants_and_quorum_guards.BeltQuorumCore.record_custodian_ack st.inner ep msg =
        .ok (inner, .Ok k) ∧
      st' = { st with inner := inner, ack_bitmap := st.ack_bitmap ||| beltCustodianBit id }) := by
  obtain ⟨hn, hi, key, hk, ht⟩ := authenticated_belt_accepted_ack_tag st st' ep msg tag id k h
  have hs : (1#u64 <<< id : Result Std.U64) = .ok (beltCustodianBit id) := by
    rw [hShlU_uscalar_eq]
    simp [hi, beltCustodianBit]
  cases hc : pants_and_quorum_guards.BeltQuorumCore.record_custodian_ack st.inner ep msg with
  | fail e =>
    unfold authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack at h
    simp only [bind_eq_result_bind, lift_eq_ok,
      pants_and_quorum_guards.BeltQuorumCore.impl.n,
      pants_and_quorum_guards.BeltQuorumCore.impl.has_bound_epoch,
      pants_and_quorum_guards.BeltQuorumCore.impl.bound_epoch,
      pants_and_quorum_guards.BeltQuorumCore.impl.bound_msg_tag,
      pants_and_quorum_guards.BeltQuorumCore.impl.ack_count,
      pants_and_quorum_guards.BeltQuorumCore.is_poisoned,
      ct_eq_bytes32_spec, hk, ht, hs, hc, Result.bind] at h
    repeat (any_goals split at h)
    all_goals cases h
    all_goals simp_all [bne_iff_ne]
  | div =>
    unfold authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack at h
    simp only [bind_eq_result_bind, lift_eq_ok,
      pants_and_quorum_guards.BeltQuorumCore.impl.n,
      pants_and_quorum_guards.BeltQuorumCore.impl.has_bound_epoch,
      pants_and_quorum_guards.BeltQuorumCore.impl.bound_epoch,
      pants_and_quorum_guards.BeltQuorumCore.impl.bound_msg_tag,
      pants_and_quorum_guards.BeltQuorumCore.impl.ack_count,
      pants_and_quorum_guards.BeltQuorumCore.is_poisoned,
      ct_eq_bytes32_spec, hk, ht, hs, hc, Result.bind] at h
    repeat (any_goals split at h)
    all_goals cases h
    all_goals simp_all [bne_iff_ne]
  | ok v =>
    rcases v with ⟨inner, res⟩
    cases res with
    | Err e =>
      unfold authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack at h
      simp only [bind_eq_result_bind, result_bind_ok, lift_eq_ok,
        pants_and_quorum_guards.BeltQuorumCore.impl.n,
        pants_and_quorum_guards.BeltQuorumCore.impl.has_bound_epoch,
        pants_and_quorum_guards.BeltQuorumCore.impl.bound_epoch,
        pants_and_quorum_guards.BeltQuorumCore.impl.bound_msg_tag,
        pants_and_quorum_guards.BeltQuorumCore.impl.ack_count,
        pants_and_quorum_guards.BeltQuorumCore.is_poisoned,
        ct_eq_bytes32_spec, hk, ht, hs, hc] at h
      repeat (any_goals split at h)
      all_goals cases h
      all_goals simp_all [bne_iff_ne]
    | Ok count =>
      obtain ⟨_, hb, he, hm, _⟩ := belt_mealy_ack_inv (belt_core_ack_ok_mealy hc)
      unfold authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack at h
      simp only [bind_eq_result_bind, result_bind_ok, lift_eq_ok,
        pants_and_quorum_guards.BeltQuorumCore.impl.n,
        pants_and_quorum_guards.BeltQuorumCore.impl.has_bound_epoch,
        pants_and_quorum_guards.BeltQuorumCore.impl.bound_epoch,
        pants_and_quorum_guards.BeltQuorumCore.impl.bound_msg_tag,
        pants_and_quorum_guards.BeltQuorumCore.impl.ack_count,
        pants_and_quorum_guards.BeltQuorumCore.is_poisoned,
        ct_eq_bytes32_spec, hk, ht, hs, hc] at h
      repeat (any_goals split at h)
      all_goals cases h
      all_goals try { simp_all only [bne_iff_ne, decide_eq_true_eq]; done }
      all_goals exact ⟨hb, he, hm.symm, by first | exact Or.inl rfl | exact Or.inr ⟨_, rfl, rfl⟩⟩

/-- Transport of an already-set bit, including its binding. -/
def BeltBitInherited (st st' : authenticated_belt.VerifiedBeltQuorumGuard) (i : Nat) : Prop :=
  st'.inner.bound_epoch = st.inner.bound_epoch ∧
  st'.inner.bound_msg_tag = st.inner.bound_msg_tag ∧
  st.ack_bitmap.bv.getLsbD i = true

/-- A newly inserted bit names precisely the input slot, at the checked binding. -/
def BeltBitInserted (st st' : authenticated_belt.VerifiedBeltQuorumGuard)
    (a : BeltAction) (r : core.result.Result authenticated_belt.BeltQuorumStepOutput
      authenticated_belt.BeltAuthError) (i : Nat) : Prop :=
  ∃ ep msg id tag k,
    a = .RecordCustodianAck ep msg id tag ∧ r = .Ok (.AckRecorded k) ∧
    id.val = i ∧ st.inner.has_bound_epoch = true ∧
    ep = st.inner.bound_epoch ∧ msg = st.inner.bound_msg_tag ∧
    st'.inner.bound_epoch = ep ∧ st'.inner.bound_msg_tag = msg

private theorem belt_nonack_bit_inherited
    {st st' : authenticated_belt.VerifiedBeltQuorumGuard} {obs : BeltObs} {i : Nat}
    (ho : BeltStepOutcome st st' obs) (hne : obs ≠ .ackRecorded)
    (hb : st'.ack_bitmap.bv.getLsbD i = true) : BeltBitInherited st st' i := by
  cases ho with
  | rejected_unchanged h | retried h => subst h; exact ⟨rfl, rfl, hb⟩
  | rejected_poisoned h1 h2 => rw [h2, belt_zero_getLsbD] at hb; cases hb
  | bound ep msg hc hn hge hlt h => subst h; change (0#u64).bv.getLsbD i = true at hb; rw [belt_zero_getLsbD] at hb; cases hb
  | duplicate h => exact (hne rfl).elim
  | acked id hc hb hn h64 hz hcount h => exact (hne rfl).elim
  | granted hc hbound hq h => subst h; exact ⟨rfl, rfl, hb⟩

/-- Per-bit complete mediation for the actual extracted entry point. -/
theorem belt_step_bit_origin
    {st st' : authenticated_belt.VerifiedBeltQuorumGuard} {a : BeltAction}
    {r : core.result.Result authenticated_belt.BeltQuorumStepOutput authenticated_belt.BeltAuthError}
    {i : Nat}
    (h : authenticated_belt.VerifiedBeltQuorumGuard.step st a = .ok (st', r))
    (hb : st'.ack_bitmap.bv.getLsbD i = true) :
    BeltBitInherited st st' i ∨ BeltBitInserted st st' a r i := by
  have ho := belt_step_outcome h
  cases a with
  | ProposeOrRetryEpoch ep msg digest tag =>
    unfold authenticated_belt.VerifiedBeltQuorumGuard.step at h
    cases he : authenticated_belt.VerifiedBeltQuorumGuard.propose_or_retry_epoch st ep msg digest tag with
    | fail e => simp [he, bind_eq_result_bind, Result.bind] at h
    | div => simp [he, bind_eq_result_bind, Result.bind] at h
    | ok v =>
      rcases v with ⟨next, res⟩
      cases res <;> simp only [he, bind_eq_result_bind, result_bind_ok] at h <;> cases h
      all_goals exact Or.inl (belt_nonack_bit_inherited ho (by intro h; cases h) hb)
  | AuthorizeShares ep msg =>
    unfold authenticated_belt.VerifiedBeltQuorumGuard.step at h
    cases he : authenticated_belt.VerifiedBeltQuorumGuard.authorize_shares st ep msg with
    | fail e => simp [he, bind_eq_result_bind, Result.bind] at h
    | div => simp [he, bind_eq_result_bind, Result.bind] at h
    | ok v =>
      rcases v with ⟨next, res⟩
      cases res <;> simp only [he, bind_eq_result_bind, result_bind_ok] at h <;> cases h
      all_goals exact Or.inl (belt_nonack_bit_inherited ho (by intro h; cases h) hb)
  | RecordCustodianAck ep msg id tag =>
    unfold authenticated_belt.VerifiedBeltQuorumGuard.step at h
    cases he : authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack st ep msg id tag with
    | fail e => simp [he, bind_eq_result_bind, Result.bind] at h
    | div => simp [he, bind_eq_result_bind, Result.bind] at h
    | ok v =>
      rcases v with ⟨next, res⟩
      cases res with
      | Err e =>
        simp only [he, bind_eq_result_bind, result_bind_ok] at h
        cases h
        exact Or.inl (belt_nonack_bit_inherited ho (by intro h; cases h) hb)
      | Ok k =>
        simp only [he, bind_eq_result_bind, result_bind_ok] at h
        cases h
        obtain ⟨hbound, hep, hmsg, hs⟩ := belt_ack_success_shape he
        rcases hs with rfl | ⟨inner, hcore, rfl⟩
        · exact Or.inl ⟨rfl, rfl, hb⟩
        · obtain ⟨_, _, _, _, _, hinner, _⟩ := belt_mealy_ack_inv (belt_core_ack_ok_mealy hcore)
          subst hinner
          have h64 := (authenticated_belt_accepted_ack_tag _ _ _ _ _ _ _ he).2.1
          rcases belt_or_bit_getLsbD_true h64 hb with hold | hid
          · exact Or.inl ⟨rfl, rfl, hold⟩
          · exact Or.inr ⟨ep, msg, id, tag, k, rfl, rfl, hid.symm,
              hbound, hep, hmsg, hep.symm, hmsg.symm⟩


/-- A call record preserves rejected turns as well as accepted ones. -/
structure BeltCall where
  before : authenticated_belt.VerifiedBeltQuorumGuard
  input : BeltAction
  after : authenticated_belt.VerifiedBeltQuorumGuard
  result : core.result.Result authenticated_belt.BeltQuorumStepOutput authenticated_belt.BeltAuthError

/-- Chronological execution of the extracted function; there are no input contracts. -/
inductive BeltRun (initial : authenticated_belt.VerifiedBeltQuorumGuard) :
    List BeltCall → authenticated_belt.VerifiedBeltQuorumGuard → Prop where
  | nil : BeltRun initial [] initial
  | snoc {calls st st' a r} : BeltRun initial calls st →
      authenticated_belt.VerifiedBeltQuorumGuard.step st a = .ok (st', r) →
      BeltRun initial (calls ++ [⟨st, a, st', r⟩]) st'

/-- An actual accepted ack in the history, for this exact binding and enrolled slot.
The recorded pre-state was already bound to that epoch and message. -/
def BeltAckSeen (enrollment : authenticated_belt.VerifiedBeltQuorumGuard)
    (ep : Std.U64) (msg : Array Std.U8 32#usize) (i : Nat) (calls : List BeltCall) : Prop :=
  ∃ before after id tag k key,
    (⟨before, .RecordCustodianAck ep msg id tag, after, .Ok (.AckRecorded k)⟩ : BeltCall) ∈ calls ∧
    authenticated_belt.VerifiedBeltQuorumGuard.step before (.RecordCustodianAck ep msg id tag) =
      .ok (after, .Ok (.AckRecorded k)) ∧
    before.inner.has_bound_epoch = true ∧ before.inner.bound_epoch = ep ∧
    before.inner.bound_msg_tag = msg ∧ id.val = i ∧
    Array.index_usize enrollment.custodian_keys (UScalar.cast .Usize id) = .ok key ∧
    authenticated_belt.custodian_ack_tag key enrollment.guard_key_commit ep msg id = .ok tag

@[expose] def BeltBitmapProvenance (st : authenticated_belt.VerifiedBeltQuorumGuard)
    (calls : List BeltCall) : Prop :=
  ∀ i, st.ack_bitmap.bv.getLsbD i = true →
    BeltAckSeen st st.inner.bound_epoch st.inner.bound_msg_tag i calls

theorem belt_bitmap_provenance_step
    {st st' : authenticated_belt.VerifiedBeltQuorumGuard} {a : BeltAction}
    {r : core.result.Result authenticated_belt.BeltQuorumStepOutput authenticated_belt.BeltAuthError}
    {calls : List BeltCall}
    (h : authenticated_belt.VerifiedBeltQuorumGuard.step st a = .ok (st', r))
    (hp : BeltBitmapProvenance st calls) :
    BeltBitmapProvenance st' (calls ++ [⟨st, a, st', r⟩]) := by
  intro i hi
  have hen := authenticated_belt_step_enrollment_unchanged st st' a r h
  rcases belt_step_bit_origin h hi with ⟨hep, hmsg, hbit⟩ | hnew
  · obtain ⟨before, after, id, tag, k, key, hm, hs, hb, he, ht, hid, hk, hmac⟩ := hp i hbit
    rw [hep, hmsg]
    exact ⟨before, after, id, tag, k, key, List.mem_append_left _ hm, hs, hb, he, ht,
      hid, hen.2.1 ▸ hk, hen.1 ▸ hmac⟩
  · obtain ⟨ep, msg, id, tag, k, rfl, rfl, hid, hb, he, hm, hep, hmsg⟩ := hnew
    obtain ⟨_, key, hk, hmac⟩ := authenticated_belt_step_accepted_input st st'
      (.RecordCustodianAck ep msg id tag) (.AckRecorded k) h
    rw [hep, hmsg]
    exact ⟨st, st', id, tag, k, key, List.mem_append_right _ (List.mem_cons_self),
      h, hb, he.symm, hm.symm, hid, hen.2.1 ▸ hk, hen.1 ▸ hmac⟩

/-- Every set bit throughout arbitrary accepted/rejected multi-turn executions has an
accepted MAC-valid ack for its exact current binding. An empty initial bitmap is sufficient. -/
theorem belt_run_bitmap_provenance
    {initial st : authenticated_belt.VerifiedBeltQuorumGuard} {calls : List BeltCall}
    (hr : BeltRun initial calls st) (hz : initial.ack_bitmap = 0#u64) :
    BeltBitmapProvenance st calls := by
  induction hr with
  | nil =>
    intro i hi
    rw [hz, belt_zero_getLsbD] at hi
    cases hi
  | snoc _ h ih => exact belt_bitmap_provenance_step h ih

theorem belt_run_guard_inv
    {initial st : authenticated_belt.VerifiedBeltQuorumGuard} {calls : List BeltCall}
    {n q : Std.U32} (hr : BeltRun initial calls st) (hi : BeltGuardInv n q initial) :
    BeltGuardInv n q st := by
  induction hr with
  | nil => exact hi
  | snoc _ h ih => exact belt_outcome_preserves_inv ih (belt_step_outcome h)

/-- The finite signer set of a bitmap. No custodian appears twice. -/
def beltSigners (bm : Std.U64) : List Nat := (List.range 64).filter bm.bv.getLsbD

theorem beltSigners_nodup (bm : Std.U64) : (beltSigners bm).Nodup :=
  List.Pairwise.filter _ (by decide : (List.range 64).Nodup)

theorem beltSigners_length (bm : Std.U64) : (beltSigners bm).length = beltPopcount bm := by
  simp only [beltSigners, beltPopcount, List.countP_eq_length_filter]

/-- Every granted certificate has at least q distinct enrolled custodians, each backed
by an earlier accepted MAC-valid ack for exactly the certificate's epoch and message. -/
theorem belt_grant_authenticated_history
    {initial st st' : authenticated_belt.VerifiedBeltQuorumGuard} {calls : List BeltCall}
    {a : BeltAction} {g : pants_and_quorum_guards.BeltAuthorizationGrant} {n q : Std.U32}
    (hr : BeltRun initial calls st) (hz : initial.ack_bitmap = 0#u64)
    (hinv : BeltGuardInv n q initial)
    (hg : authenticated_belt.VerifiedBeltQuorumGuard.step st a =
      .ok (st', .Ok (.SharesAuthorized g))) :
    ∃ signers : List Nat, signers.Nodup ∧ q.val ≤ signers.length ∧
      g.certified_acks.val = signers.length ∧
      ∀ i ∈ signers, i < n.val ∧ BeltAckSeen st g.authorized_epoch g.msg_tag i calls := by
  have hi := belt_run_guard_inv hr hinv
  have hp := belt_run_bitmap_provenance hr hz
  obtain ⟨_, _, hep, hmsg, hcount, hq, _⟩ := belt_outcome_granted_inv (belt_step_outcome hg)
  refine ⟨beltSigners st.ack_bitmap, beltSigners_nodup _, ?_, ?_, ?_⟩
  · rw [beltSigners_length, ← hi.2.2.1, ← hi.2.1] ; exact hq
  · rw [hcount, beltSigners_length]; exact hi.2.2.1
  · intro i hm
    have hb := (List.mem_filter.mp hm).2
    exact ⟨hi.2.2.2 i hb, hep ▸ hmsg ▸ hp i hb⟩


/-- Enrollment remains fixed even through rejected turns. -/
theorem belt_run_enrollment
    {initial st : authenticated_belt.VerifiedBeltQuorumGuard} {calls : List BeltCall}
    (hr : BeltRun initial calls st) :
    st.guard_key_commit = initial.guard_key_commit ∧ st.custodian_keys = initial.custodian_keys := by
  induction hr with
  | nil => exact ⟨rfl, rfl⟩
  | snoc _ h ih =>
    have he := authenticated_belt_step_enrollment_unchanged _ _ _ _ h
    exact ⟨he.1.trans ih.1, he.2.1.trans ih.2⟩

private theorem belt_ack_seen_initial
    {initial st : authenticated_belt.VerifiedBeltQuorumGuard} {calls : List BeltCall}
    {ep : Std.U64} {msg : Array Std.U8 32#usize} {i : Nat}
    (hr : BeltRun initial calls st) (ha : BeltAckSeen st ep msg i calls) :
    BeltAckSeen initial ep msg i calls := by
  obtain ⟨before, after, id, tag, k, key, hm, hs, hb, he, ht, hid, hk, hmac⟩ := ha
  obtain ⟨hc, hkeys⟩ := belt_run_enrollment hr
  exact ⟨before, after, id, tag, k, key, hm, hs, hb, he, ht, hid,
    hkeys ▸ hk, hc ▸ hmac⟩

/-- Provisioning turns an authenticated history witness into an explicitly nonzero,
uniquely enrolled key witness. No secrecy or MAC unforgeability is inferred from this. -/
theorem belt_ack_seen_provisioned
    {initial : authenticated_belt.VerifiedBeltQuorumGuard} {calls : List BeltCall}
    {ep : Std.U64} {msg : Array Std.U8 32#usize} {i : Nat} {n : Std.U32}
    (ha : BeltAckSeen initial ep msg i calls) (hi : i < n.val)
    (hk : BeltProvisionedKeys n initial.custodian_keys) :
    ∃ id key tag, id.val = i ∧
      Array.index_usize initial.custodian_keys (UScalar.cast .Usize id) = .ok key ∧
      authenticated_belt.custodian_ack_tag key initial.guard_key_commit ep msg id = .ok tag ∧
      key ≠ Array.repeat 32#usize 0#u8 ∧
      ∀ j key', j.val < n.val →
        Array.index_usize initial.custodian_keys (UScalar.cast .Usize j) = .ok key' →
        key' = key → j = id := by
  obtain ⟨before, after, id, tag, k, key, _, _, _, _, _, hid, hlookup, hmac⟩ := ha
  have hn : id.val < n.val := hid ▸ hi
  exact ⟨id, key, tag, hid, hlookup, hmac, hk.1 id key hn hlookup,
    fun j key' hj hlookup' heq => hk.2 j id key' key hj hn hlookup' hlookup heq⟩

/-- Two grants, even at different epochs, have more than f common distinct custodians.
Every common custodian has an accepted authenticated ack in each grant's own earlier
history, under the initial enrolled key and for that grant's exact epoch/message. -/
theorem belt_two_grants_authenticated_intersection
    {initial s1 s1' s2 s2' : authenticated_belt.VerifiedBeltQuorumGuard}
    {calls1 calls2 : List BeltCall} {a1 a2 : BeltAction}
    {g1 g2 : pants_and_quorum_guards.BeltAuthorizationGrant} {n f q : Std.U32}
    (hr1 : BeltRun initial calls1 s1) (hr2 : BeltRun initial calls2 s2)
    (hz : initial.ack_bitmap = 0#u64) (hinv : BeltGuardInv n q initial)
    (hcfg : n.val + f.val < 2 * q.val)
    (hg1 : authenticated_belt.VerifiedBeltQuorumGuard.step s1 a1 = .ok (s1', .Ok (.SharesAuthorized g1)))
    (hg2 : authenticated_belt.VerifiedBeltQuorumGuard.step s2 a2 = .ok (s2', .Ok (.SharesAuthorized g2))) :
    ∃ shared : List Nat, shared.Nodup ∧ f.val < shared.length ∧
      ∀ i ∈ shared, i < n.val ∧
        BeltAckSeen initial g1.authorized_epoch g1.msg_tag i calls1 ∧
        BeltAckSeen initial g2.authorized_epoch g2.msg_tag i calls2 := by
  have hi1 := belt_run_guard_inv hr1 hinv
  have hi2 := belt_run_guard_inv hr2 hinv
  obtain ⟨_, _, he1, hm1, _, hq1, _⟩ := belt_outcome_granted_inv (belt_step_outcome hg1)
  obtain ⟨_, _, he2, hm2, _, hq2, _⟩ := belt_outcome_granted_inv (belt_step_outcome hg2)
  have hq1' : q.val ≤ beltPopcount s1.ack_bitmap := by rw [← hi1.2.1, ← hi1.2.2.1]; exact hq1
  have hq2' : q.val ≤ beltPopcount s2.ack_bitmap := by rw [← hi2.2.1, ← hi2.2.2.1]; exact hq2
  refine ⟨beltSigners (s1.ack_bitmap &&& s2.ack_bitmap), beltSigners_nodup _, ?_, ?_⟩
  · rw [beltSigners_length]
    exact belt_quorum_intersection hcfg hq1' hi1.2.2.2 hq2' hi2.2.2.2
  · intro i hm
    have hb := (List.mem_filter.mp hm).2
    change (s1.ack_bitmap.bv &&& s2.ack_bitmap.bv).getLsbD i = true at hb
    rw [BitVec.getLsbD_and, Bool.and_eq_true] at hb
    refine ⟨hi1.2.2.2 i hb.1, ?_, ?_⟩
    · rw [he1, hm1]
      exact belt_ack_seen_initial hr1 (belt_run_bitmap_provenance hr1 hz i hb.1)
    · rw [he2, hm2]
      exact belt_ack_seen_initial hr2 (belt_run_bitmap_provenance hr2 hz i hb.2)


/-- Concatenation keeps every refused call in the authenticated history. -/
theorem BeltRun.append
    {s m t : authenticated_belt.VerifiedBeltQuorumGuard} {xs ys : List BeltCall}
    (hx : BeltRun s xs m) (hy : BeltRun m ys t) : BeltRun s (xs ++ ys) t := by
  induction hy with
  | nil => simpa using hx
  | snoc _ h ih => simpa only [List.append_assoc] using BeltRun.snoc ih h

/-- Every previously defined reachable trace has a chronological real-call history.
Thus the provenance semantics includes all actions of the reachability/completeness API. -/
theorem belt_trace_to_run
    {s t : authenticated_belt.VerifiedBeltQuorumGuard} {acts : List BeltAction}
    {certs : List BeltCert} (ht : BeltTraceReachable s acts certs t) :
    ∃ calls, BeltRun s calls t ∧ calls.map BeltCall.input = acts := by
  induction ht with
  | nil st => exact ⟨[], .nil, rfl⟩
  | bound h _ ih | acked h _ ih | certified h _ ih | failed h _ ih =>
    obtain ⟨calls, hr, hmap⟩ := ih
    exact ⟨_ :: calls, (BeltRun.snoc .nil h).append hr, by simp only [List.map_cons, hmap]⟩


/-- Constructor-established provenance preconditions, with no extra caller invariant. -/
theorem belt_new_validated_provenance_init
    {n t f q : Std.U32} {gl : Bool} {e0 window : Std.U64}
    {commit wal : Array Std.U8 32#usize} {keys : Array (Array Std.U8 32#usize) 64#usize}
    {initial : authenticated_belt.VerifiedBeltQuorumGuard}
    (hn : authenticated_belt.VerifiedBeltQuorumGuard.new_validated
      n t f q gl e0 window commit keys wal = .ok (.Ok initial)) :
    initial.ack_bitmap = 0#u64 ∧ BeltGuardInv n q initial ∧ n.val + f.val < 2 * q.val := by
  obtain ⟨hcfg, _, hn, hq, _, _, _, hc, hb⟩ := auth_belt_new_validated_inv hn
  refine ⟨hb, ⟨hn, hq, ?_, ?_⟩, hcfg.2.2.2.2.1⟩
  · rw [hc, hb]; exact belt_zero_count_popcount
  · intro i hi
    rw [hb, belt_zero_getLsbD] at hi
    cases hi


/-- Three distinct enrolled custodians, after a fresh proposal. The tags are computed
by the extracted authentication functions; liveness presumes all three peers supply
these acknowledgments. This is about `VerifiedBeltQuorumGuard`, not production IO. -/
theorem belt_three_custodian_round_exists
    (st : authenticated_belt.VerifiedBeltQuorumGuard) (e : Std.U64)
    (msg : Array Std.U8 32#usize)
    (hc : beltGuardCorrupt st.inner = false)
    (hn : 3 ≤ st.inner.n.val) (hq : st.inner.q.val ≤ 3)
    (hnr : ¬ (st.inner.has_bound_epoch = true ∧ e = st.inner.bound_epoch))
    (hge : st.inner.next_epoch.val ≤ e.val)
    (hwin : e.val - st.inner.next_epoch.val ≤ st.inner.max_jump_window.val)
    (hmax : e ≠ core.num.U64.MAX) :
    ∃ acts : List BeltAction, acts.length = 5 ∧
      BeltTraceReachable st acts
        [⟨{ authorized_epoch := e, msg_tag := msg, certified_acks := 3#u32 },
          ((0#u64 ||| beltCustodianBit 0#u8) ||| beltCustodianBit 1#u8) |||
            beltCustodianBit 2#u8⟩]
        (beltAfterGrant (beltAfterAck (beltAfterAck
          (beltAfterAck (beltAfterPropose st e msg) 0#u8) 1#u8) 2#u8)) := by
  obtain ⟨rt, hwal⟩ := belt_wal_receipt_tag_total st.wal_key st.guard_key_commit e msg msg
  obtain ⟨k0, hk0⟩ := array_index_total st.custodian_keys
    (UScalar.cast .Usize (0#u8)) (by decide)
  obtain ⟨k1, hk1⟩ := array_index_total st.custodian_keys
    (UScalar.cast .Usize (1#u8)) (by decide)
  obtain ⟨k2, hk2⟩ := array_index_total st.custodian_keys
    (UScalar.cast .Usize (2#u8)) (by decide)
  obtain ⟨t0, ht0⟩ := belt_custodian_ack_tag_total k0 st.guard_key_commit e msg 0#u8
  obtain ⟨t1, ht1⟩ := belt_custodian_ack_tag_total k1 st.guard_key_commit e msg 1#u8
  obtain ⟨t2, ht2⟩ := belt_custodian_ack_tag_total k2 st.guard_key_commit e msg 2#u8
  have hc0 : beltGuardCorrupt (beltAfterPropose st e msg).inner = false :=
    belt_not_corrupt_fresh msg hc (u64_val_succ_lt_of_ne_max hmax)
  have hc1 : beltGuardCorrupt
      (beltAfterAck (beltAfterPropose st e msg) 0#u8).inner = false :=
    belt_not_corrupt_set_ack_count _ hc0
  have hc2 : beltGuardCorrupt
      (beltAfterAck (beltAfterAck (beltAfterPropose st e msg) 0#u8) 1#u8).inner = false :=
    belt_not_corrupt_set_ack_count _ hc1
  have hc3 : beltGuardCorrupt
      (beltAfterAck (beltAfterAck (beltAfterAck
        (beltAfterPropose st e msg) 0#u8) 1#u8) 2#u8).inner = false :=
    belt_not_corrupt_set_ack_count _ hc2
  refine ⟨_, rfl, .bound
    (belt_step_propose_fresh st e msg msg rt hwal hc hnr hge hwin hmax) ?_⟩
  refine .acked (belt_step_ack_fresh (beltAfterPropose st e msg) e msg 0#u8 t0 k0
    (by change 0 < st.inner.n.val; omega) (by decide) hk0 ht0 hc0 rfl rfl rfl
    (by decide) (by change 0 < st.inner.n.val; omega)) ?_
  refine .acked (belt_step_ack_fresh (beltAfterAck (beltAfterPropose st e msg) 0#u8)
    e msg 1#u8 t1 k1 (by change 1 < st.inner.n.val; omega) (by decide)
    hk1 ht1 hc1 rfl rfl rfl (by decide) (by change 1 < st.inner.n.val; omega)) ?_
  refine .acked (belt_step_ack_fresh
    (beltAfterAck (beltAfterAck (beltAfterPropose st e msg) 0#u8) 1#u8)
    e msg 2#u8 t2 k2 (by change 2 < st.inner.n.val; omega) (by decide)
    hk2 ht2 hc2 rfl rfl rfl (by decide) (by change 2 < st.inner.n.val; omega)) ?_
  refine .certified (belt_step_authorize_granted
    (beltAfterAck (beltAfterAck (beltAfterAck (beltAfterPropose st e msg) 0#u8) 1#u8) 2#u8)
    hc3 rfl hq) (.nil _)

abbrev beltThreeRoundEnd (st : authenticated_belt.VerifiedBeltQuorumGuard)
    (e : Std.U64) (msg : Array Std.U8 32#usize) :=
  beltAfterGrant (beltAfterAck (beltAfterAck
    (beltAfterAck (beltAfterPropose st e msg) 0#u8) 1#u8) 2#u8)

/-- The one-fault configuration needs all three acknowledgments. The witness keys are
computable test data, not a claim of key secrecy or Byzantine availability. -/
abbrev beltOneFaultState : authenticated_belt.VerifiedBeltQuorumGuard :=
  { beltWitnessState0 with inner := { beltWitnessState0.inner with f := 1#u32, q := 3#u32 } }

/-- A validated `n=3,t=2,f=1,q=3` guard certifies two successive epochs. The real-call
history is retained so `belt_run_bitmap_provenance` applies without a wrapper premise. -/
theorem inhabited_belt_one_fault_multi_epoch :
    ∃ (stF : authenticated_belt.VerifiedBeltQuorumGuard) (acts : List BeltAction)
      (certs : List BeltCert) (calls : List BeltCall),
      authenticated_belt.VerifiedBeltQuorumGuard.new_validated
        3#u32 2#u32 1#u32 3#u32 false 10#u64 4#u64
        beltWitnessBytes beltWitnessKeys beltWitnessBytes = .ok (.Ok beltOneFaultState) ∧
      BeltTraceReachable beltOneFaultState acts certs stF ∧
      BeltRun beltOneFaultState calls stF ∧ calls.map BeltCall.input = acts ∧
      acts.length = 10 ∧
      certs.map (fun c => c.grant.authorized_epoch.val) = [10, 11] ∧
      certs.map (fun c => beltPopcount c.signers) = [3, 3] := by
  have hnew : authenticated_belt.VerifiedBeltQuorumGuard.new_validated
      3#u32 2#u32 1#u32 3#u32 false 10#u64 4#u64
      beltWitnessBytes beltWitnessKeys beltWitnessBytes = .ok (.Ok beltOneFaultState) := by
    unfold authenticated_belt.VerifiedBeltQuorumGuard.new_validated
      pants_and_quorum_guards.BeltQuorumCore.new_validated
    rw [validate_belt_quorum_config_eq]
    rfl
  obtain ⟨acts1, hl1, h1⟩ := belt_three_custodian_round_exists beltOneFaultState 10#u64
    beltWitnessBytes (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  obtain ⟨acts2, hl2, h2⟩ := belt_three_custodian_round_exists
    (beltThreeRoundEnd beltOneFaultState 10#u64 beltWitnessBytes) 11#u64
    beltWitnessBytes (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have ht := h1.append h2
  obtain ⟨calls, hr, hm⟩ := belt_trace_to_run ht
  exact ⟨_, _, _, calls, hnew, ht, hr, hm,
    by simp only [List.length_append, hl1, hl2], by decide, by decide⟩

end qsag_verified.proofs
