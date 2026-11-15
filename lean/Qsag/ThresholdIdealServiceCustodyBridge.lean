module
public import Qsag.ThresholdIdealService
public import Qsag.SeparatedCustodyResourceHistory
import all Qsag.ThresholdIdealService
import all Qsag.SeparatedCustodyUcResource
import all Qsag.SeparatedCustodyUcBridge
import all Qsag.ThresholdApproval

public section
namespace Qsag.ThresholdIdealService
set_option autoImplicit false

/-- The service's public quorum parameters, with static corruption and no
runtime quarantine yet. The enrollment key is the actual profile's derived key. -/
def publicState (c : Config) : IdealTsigState PqPublicKey (List UInt8) :=
  ⟨RssProduction.enrolledKey c.profile, c.threshold, c.parties, c.corrupt, [], []⟩

theorem authorized_of_verified_threshold (c : Config) (s : State)
    (r : SessionScheduleReq)
    (h : validThresholdApproval (publicState c) r.honestApprovers = true)
    (hi : ∀ p ∈ r.honestApprovers, (p,r) ∈ s.approvals) :
    authorized c s r = true := by
  have hf : c.corrupt.filter (fun _ => true) = c.corrupt := by
    induction c.corrupt with
    | nil => rfl
    | cons x xs ih => simp [List.filter, ih]
  simp [validThresholdApproval, publicState, List.all_eq_true, hf] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨hpair, hminor⟩, hnonempty⟩, hcnd⟩, hcr⟩, hnd⟩, hhr⟩, hq⟩
  have hbounds := of_decide_eq_true hpair
  apply decide_eq_true
  refine ⟨hbounds.1, hbounds.2, of_decide_eq_true hcnd, ?_,
    of_decide_eq_true hminor, ?_, hnd, ?_, hq⟩
  · intro p hp
    exact of_decide_eq_true (hcr p hp)
  · intro he
    rw [he] at hnonempty
    exact Nat.lt_irrefl 0 hnonempty
  · intro p hp
    exact ⟨of_decide_eq_true (hhr p hp).1,
      of_decide_eq_true (hhr p hp).2, hi p hp⟩

/-- Constructive finite aggregation: if every roster member has its input or
exhibits a forged submitted certificate, either all inputs exist or one actual
certificate is a forgery. No excluded-middle choice of a missing party. -/
private theorem inputs_or_forgery (ids : List Nat) (input : Nat → Prop) (forgery : Prop)
    (h : ∀ i ∈ ids, input i ∨ forgery) :
    (∀ i ∈ ids, input i) ∨ forgery := by
  induction ids with
  | nil => exact .inl (by intro i hi; cases hi)
  | cons i ids ih =>
    rcases h i (.head _) with hi | hf
    · rcases ih (fun j hj => h j (.tail _ hj)) with hs | hf
      · left
        intro j hj
        cases hj with
        | head => exact hi
        | tail _ hj => exact hs j hj
      · exact .inr hf
    · exact .inr hf

/-- The service approval ledger is linked to actual contextual participant
inputs, not adversarial roster claims. An accepted gate yields authorization
or an explicit accepted signature-game forgery. The key/threshold alignment
is public configuration; there is no assumed signer-origin premise. -/
theorem gate_authorizes_or_forgery (c : Config) (s : State)
    (d : Custody.Deployment) (commands : List Custody.RequestPolicy.HistoryCommand)
    (a : Custody.RequestPolicy.Input) (certs : List Custody.Certificate)
    (ha : CustodyTsigAligned d (publicState c))
    (hw : d.signer.params.w = 4 ∨ d.signer.params.w = 16)
    (hst : d.signer.params.statefulJorts = true)
    (hledger : s.approvals = Custody.RequestPolicy.approvedParticipantInputs
      (Custody.RequestPolicy.generatedHistory c.profile d commands))
    (hg : Custody.RequestPolicy.gate c.profile d c.corrupt
      (Custody.RequestPolicy.generatedHistory c.profile d commands) a certs = true) :
    authorized c s a.request = true ∨
      ∃ cert ∈ certs, Custody.RequestPolicy.CandidateForgery d
        (Custody.RequestPolicy.generatedHistory c.profile d commands) cert := by
  have hall := inputs_or_forgery a.request.honestApprovers
    (fun i => (i, a.request) ∈ s.approvals)
    (∃ cert ∈ certs, Custody.RequestPolicy.CandidateForgery d
      (Custody.RequestPolicy.generatedHistory c.profile d commands) cert) (by
      intro i hi
      rcases Custody.RequestPolicy.gate_approved_participant_input_or_forgery
        c.profile d c.corrupt commands a certs hw hst hg i hi with hin | hf
      · left
        rw [hledger]
        exact hin
      · obtain ⟨cert, hm, _, hf⟩ := hf
        exact .inr ⟨cert, hm, hf⟩)
  rcases hall with hin | hf
  · left
    apply authorized_of_verified_threshold c s a.request
    · exact Custody.RequestPolicy.gate_threshold c.profile d (publicState c) ha _ a certs
        (by intro cert hm; simp [publicState]) hg
    · exact hin
  · exact .inr hf


/-- The same result for an actual arbitrary resource execution prefix, including
crashes, production, commits and retries. The history projection theorem supplies
the generated-history premise; it is not an extra provenance hypothesis. -/
theorem actual_prefix_authorizes_or_forgery (c : Config) (s : State)
    (d : Custody.Deployment) (commands : List Custody.RequestPolicy.ResourceCommand)
    (a : Custody.RequestPolicy.Input) (certs : List Custody.Certificate)
    (ha : CustodyTsigAligned d (publicState c))
    (hw : d.signer.params.w = 4 ∨ d.signer.params.w = 16)
    (hst : d.signer.params.statefulJorts = true)
    (hledger : s.approvals = Custody.RequestPolicy.approvedParticipantInputs
      (Custody.RequestPolicy.resourceRun c.profile d c.corrupt
        (Custody.RequestPolicy.resourceInitial c.profile d) commands).history)
    (hg : Custody.RequestPolicy.gate c.profile d c.corrupt
      (Custody.RequestPolicy.resourceRun c.profile d c.corrupt
        (Custody.RequestPolicy.resourceInitial c.profile d) commands).history a certs = true) :
    authorized c s a.request = true ∨
      ∃ cert ∈ certs, Custody.RequestPolicy.CandidateForgery d
        (Custody.RequestPolicy.resourceRun c.profile d c.corrupt
          (Custody.RequestPolicy.resourceInitial c.profile d) commands).history cert := by
  rw [Custody.RequestPolicy.resource_history_is_generated] at hledger hg ⊢
  exact gate_authorizes_or_forgery c s d _ a certs ha hw hst hledger hg

end Qsag.ThresholdIdealService
