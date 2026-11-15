module
public import Qsag.Custody.CompleteMediationBoundary
import all Qsag.Custody.CompleteMediationBoundary
import all Qsag.Custody.SeparatedCustodyCore
import all Qsag.Protocol.Signing.HypertreeEufCma
import Qsag.Tactic.AssuranceKit

/-! Composition entry point for independently keyed production custody approvals.
This proves structural extraction to the existing production hash-signature break
events. It is not a computational advantage bound, a distributed threshold signer,
or a refinement of an ELF/MIR implementation. In particular no simulator may
replace a successfully issued certificate with an arbitrary signature.
-/
public section
namespace Qsag.Custody
set_option autoImplicit false
set_option maxRecDepth 4096

-- Nat-only constructive pigeonhole proof; the core List subset cardinality
-- lemma currently depends on Classical.choice.
private def eraseParty (x : Nat) : List Nat → List Nat
  | [] => []
  | y :: ys => if x = y then ys else y :: eraseParty x ys

private theorem eraseParty_length {x : Nat} :
    ∀ {xs : List Nat}, x ∈ xs → (eraseParty x xs).length + 1 = xs.length
  | [], h => by cases h
  | y :: ys, h => by
    unfold eraseParty
    by_cases he : x = y
    · simp only [he, ↓reduceIte, List.length_cons]
    · simp only [he, ↓reduceIte, List.length_cons]
      cases h with
      | head => exact False.elim (he rfl)
      | tail _ ht => exact congrArg Nat.succ (eraseParty_length ht)

private theorem eraseParty_mem {x z : Nat} (hn : z ≠ x) :
    ∀ {xs : List Nat}, z ∈ xs → z ∈ eraseParty x xs
  | [], h => by cases h
  | y :: ys, h => by
    unfold eraseParty
    by_cases he : x = y
    · simp only [he, ↓reduceIte]
      subst y
      cases h with
      | head => exact False.elim (hn rfl)
      | tail _ ht => exact ht
    · simp only [he, ↓reduceIte]
      cases h with
      | head => exact .head _
      | tail _ ht => exact .tail _ (eraseParty_mem hn ht)

private theorem party_subset_length : ∀ {xs ys : List Nat},
    xs.Nodup → xs ⊆ ys → xs.length ≤ ys.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, ys, .cons hn hd, hs => by
    have he := eraseParty_length (hs (.head _))
    have hsub : xs ⊆ eraseParty x ys := by
      intro z hz
      exact eraseParty_mem (fun hzx => hn z hz hzx.symm) (hs (.tail _ hz))
    have hi := party_subset_length hd hsub
    rw [List.length_cons, ← he]
    exact Nat.add_le_add_right hi 1

/-- Coordinator state is public; replay protection is independent of signature
validity. The corrupt-party list is used only in the theorem, not by this check. -/
def acceptQuorum (cfg : SigningConfig) (pks : Nat → PqPublicKey)
    (numParties threshold : Nat) (consumedSessions : List Nat)
    (r : Intent) (certs : List Certificate) : Bool :=
  decide (r.session ∉ consumedSessions) &&
  decide (0 < threshold ∧ threshold ≤ certs.length ∧
    (certs.map Certificate.party).Nodup ∧ ∀ c ∈ certs, c.party < numParties) &&
  certs.all (verifyCertificate cfg pks r)

structure Coordinator where
  consumedSessions : List Nat := []
  spent : Nat := 0
  capacity : Nat := 0

/-- The public coordinator records consumption on acceptance. Callers cannot
replay a session merely by supplying a different valid certificate set. -/
def submit (cfg : SigningConfig) (pks : Nat → PqPublicKey) (n t : Nat)
    (st : Coordinator) (r : Intent) (cs : List Certificate) : Coordinator × Bool :=
  if acceptQuorum cfg pks n t st.consumedSessions r cs then
    if st.spent + r.spend ≤ st.capacity then
      ({ st with
        consumedSessions := r.session :: st.consumedSessions
        spent := st.spent + r.spend }, true)
    else (st, false)
  else (st, false)

theorem submit_accepted (cfg : SigningConfig) (pks : Nat → PqPublicKey)
    (n t : Nat) (st : Coordinator) (r : Intent) (cs : List Certificate)
    (h : (submit cfg pks n t st r cs).2 = true) :
    acceptQuorum cfg pks n t st.consumedSessions r cs = true ∧
    st.spent + r.spend ≤ st.capacity ∧
    (submit cfg pks n t st r cs).1 =
      { st with
        consumedSessions := r.session :: st.consumedSessions
        spent := st.spent + r.spend } := by
  unfold submit at h ⊢
  split at h
  next ha =>
    split at h
    next hb => exact ⟨ha, hb, by simp only [ha, hb, ↓reduceIte]⟩
    next => cases h
  next => cases h

theorem submit_budget (cfg : SigningConfig) (pks : Nat → PqPublicKey)
    (n t : Nat) (st : Coordinator) (r : Intent) (cs : List Certificate)
    (h : (submit cfg pks n t st r cs).2 = true) :
    (submit cfg pks n t st r cs).1.spent ≤ st.capacity := by
  obtain ⟨_, hb, he⟩ := submit_accepted cfg pks n t st r cs h
  rw [he]
  exact hb

theorem quorum_replay_rejected (cfg : SigningConfig) (pks : Nat → PqPublicKey)
    (n t : Nat) (used : List Nat) (r : Intent) (cs : List Certificate)
    (h : r.session ∈ used) : acceptQuorum cfg pks n t used r cs = false := by
  simp [acceptQuorum, h]

theorem submit_replay_rejected (cfg : SigningConfig) (pks : Nat → PqPublicKey)
    (n t : Nat) (st : Coordinator) (r : Intent) (cs cs' : List Certificate)
    (h : (submit cfg pks n t st r cs).2 = true) :
    (submit cfg pks n t (submit cfg pks n t st r cs).1 r cs').2 = false := by
  rw [(submit_accepted cfg pks n t st r cs h).2.2]
  unfold submit
  rw [quorum_replay_rejected cfg pks n t _ r cs' List.mem_cons_self]
  rfl

theorem quorum_has_honest (cfg : SigningConfig) (pks : Nat → PqPublicKey)
    (n t : Nat) (used corrupt : List Nat) (r : Intent) (cs : List Certificate)
    (hc : corrupt.length < t) (h : acceptQuorum cfg pks n t used r cs = true) :
    ∃ c ∈ cs, c.party ∉ corrupt ∧ c.intent = r ∧
      verify cfg (pks c.party) c.party r c.signature = true := by
  obtain ⟨hg, ha⟩ := Bool.and_eq_true_iff.mp h
  have shape := of_decide_eq_true (Bool.and_eq_true_iff.mp hg).2
  rcases list_search (fun c : Certificate => c.party ∉ corrupt)
      (fun _ => Decidable.em _) cs with ⟨c, hm, hn⟩ | hall
  · have hv := Bool.and_eq_true_iff.mp (List.all_eq_true.mp ha c hm)
    have he := of_decide_eq_true hv.1
    exact ⟨c, hm, hn, he, by simpa only [he] using hv.2⟩
  · have hsub : cs.map Certificate.party ⊆ corrupt := by
      intro i hi
      obtain ⟨c, hm, rfl⟩ := List.mem_map.mp hi
      exact Decidable.byContradiction (hall c hm)
    have hlen := party_subset_length shape.2.2.1 hsub
    rw [List.length_map] at hlen
    exact False.elim ((Nat.not_lt_of_ge (Nat.le_trans shape.2.1 hlen)) hc)

def stateAfter (cfg : SigningConfig) (keys : Nat → PqSecretKey)
    (policies : Nat → RoundPolicy) (caps : Nat → Nat)
    (traces : Nat → List Command) (i : Nat) : Vault :=
  run cfg (keys i) i (policies i) (caps i) initial (traces i)

def signingLog (cfg : SigningConfig) (sk : PqSecretKey) (i : Nat) (v : Vault) :=
  productionSigningLog cfg.suite cfg.params sk (queries cfg i v)

/-- `BurnedApproval` is concrete data membership plus the real MAC checker;
it is derived from execution, not a hypothetical judgement supplied to it. -/
def BurnedApproval (p : RoundPolicy) (v : Vault) (r : Intent) : Prop :=
  ∃ b ∈ v.durable.burned, b.intent = r ∧
    checkRound p b.intent b.digest b.openings = true ∧ b.intent.message ≠ []

theorem attempted_approved (p : RoundPolicy) (cap : Nat) (v : Vault)
    (hs : Safe p cap v) (r : Intent) (hm : r ∈ v.attempted) : BurnedApproval p v r := by
  obtain ⟨b, hb, he⟩ := hs.attemptedBurned r hm
  exact ⟨b, hb, he, hs.approved b hb⟩

theorem log_fresh_of_not_attempted (cfg : SigningConfig) (sk : PqSecretKey)
    (i : Nat) (v : Vault) (r : Intent) (hn : r ∉ v.attempted) :
    ∀ e ∈ signingLog cfg sk i v, e.1 ≠ payload i r := by
  intro e he hEq
  obtain ⟨q, hq, hm, _⟩ := productionSigningLog_generated _ _ _ _ e he
  obtain ⟨s, hs, hsq⟩ := List.mem_map.mp hq
  have hp : payload i s = payload i r := by
    simpa only [← hsq, query] using hm.symm.trans hEq
  exact hn ((payload_injective hp).2 ▸ hs)

/-- The candidate supplied to the signature game is the accepted certificate
itself, with the exact trace-derived oracle queries. This does not replace the
candidate by an arbitrary existential collision. -/
theorem accepted_fresh_certificate_wins (cfg : SigningConfig) (sk : PqSecretKey)
    (i : Nat) (v : Vault) (r : Intent) (sig : PqHashSig)
    (hn : r ∉ v.attempted)
    (hv : verify cfg (derivePublicKey cfg.suite cfg.params sk) i r sig = true) :
    prodEufCmaWin cfg.suite cfg.params ⟨sk, queries cfg i v, payload i r, sig⟩ = true := by
  have hf := log_fresh_of_not_attempted cfg sk i v r hn
  have hnot : payload i r ∉ (signingLog cfg sk i v).map Prod.fst := by
    intro hm
    obtain ⟨e, he, heq⟩ := List.mem_map.mp hm
    exact hf e he heq
  unfold prodEufCmaWin
  exact Bool.and_eq_true_iff.mpr ⟨hv, decide_eq_true hnot⟩

/-- Composition of the actual quorum checker, hostile per-party execution,
durable policy checks, real production verifier, and hash-signature reduction.
One-time leaf use and fresh-message signing-log separation are proved here.
Only the explicit stateful profile and supported radix select the existing
production reduction; no unforgeability or whole-system conclusion is a premise.
-/
theorem accepted_quorum_approval_or_hash_break
    (cfg : SigningConfig) (keys : Nat → PqSecretKey)
    (policies : Nat → RoundPolicy) (caps : Nat → Nat) (traces : Nat → List Command)
    (n t : Nat) (st : Coordinator) (corrupt : List Nat) (r : Intent) (cs : List Certificate)
    (hw : cfg.params.w = 4 ∨ cfg.params.w = 16)
    (hst : cfg.params.statefulJorts = true) (hc : corrupt.length < t)
    (h : (submit cfg (fun i => derivePublicKey cfg.suite cfg.params (keys i))
      n t st r cs).2 = true) :
    ∃ c ∈ cs, c.party ∉ corrupt ∧
      (BurnedApproval (policies c.party) (stateAfter cfg keys policies caps traces c.party) r ∨
       (prodEufCmaWin cfg.suite cfg.params
         ⟨keys c.party, queries cfg c.party (stateAfter cfg keys policies caps traces c.party),
           payload c.party r, c.signature⟩ = true ∧
       (ProdSmTcrBreak cfg.suite cfg.params (keys c.party)
         (signingLog cfg (keys c.party) c.party (stateAfter cfg keys policies caps traces c.party)) ∨
       ProdPreimageBreak cfg.suite cfg.params (keys c.party)
         (signingLog cfg (keys c.party) c.party (stateAfter cfg keys policies caps traces c.party))
         (payload c.party r) c.signature))) := by
  have hcheck := (submit_accepted cfg _ n t st r cs h).1
  obtain ⟨c, hcm, hch, _hctx, hv⟩ :=
    quorum_has_honest cfg _ n t st.consumedSessions corrupt r cs hc hcheck
  refine ⟨c, hcm, hch, ?_⟩
  let v := stateAfter cfg keys policies caps traces c.party
  have hs : Safe (policies c.party) (caps c.party) v :=
    run_safe cfg (keys c.party) c.party (policies c.party) (caps c.party)
      (traces c.party) initial (initial_safe _ _)
  by_cases hm : r ∈ v.attempted
  · exact .inl (attempted_approved _ _ v hs r hm)
  · right
    refine ⟨accepted_fresh_certificate_wins cfg (keys c.party) c.party v r c.signature hm hv, ?_⟩
    exact production_stateful_forgery_break cfg.suite cfg.params (keys c.party)
      (queries cfg c.party v) (payload c.party r) c.signature hw hst
      (queries_one_time cfg c.party _ _ v hs)
      (log_fresh_of_not_attempted cfg (keys c.party) c.party v r hm) hv

/-- The scheduler selects one custodian. Changing any other custodian's secret,
policy, capacity or history cannot change the selected local execution. -/
theorem local_state_isolated (cfg : SigningConfig) (keys keys' : Nat → PqSecretKey)
    (policies : Nat → RoundPolicy) (caps : Nat → Nat) (traces : Nat → List Command)
    (i : Nat) (h : keys i = keys' i) :
    stateAfter cfg keys policies caps traces i = stateAfter cfg keys' policies caps traces i := by
  simp only [stateAfter, h]

end Qsag.Custody
end
set_option maxRecDepth 4096
#verify_constructive Qsag.Custody.quorum_has_honest
#verify_constructive Qsag.Custody.accepted_quorum_approval_or_hash_break
#verify_constructive Qsag.Custody.accepted_fresh_certificate_wins
#verify_constructive Qsag.Custody.quorum_replay_rejected
#verify_constructive Qsag.Custody.submit_replay_rejected
#verify_constructive Qsag.Custody.submit_budget
#verify_constructive Qsag.Custody.local_state_isolated
