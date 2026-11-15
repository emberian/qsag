module
public import Qsag.SeparatedCustodySpine
public import Qsag.CustodySuiteFull
import all Qsag.SeparatedCustodyCore
import all Qsag.CompleteMediationBoundary
import all Qsag.CustodySuiteFull
import Qsag.Tactic.AssuranceKit

/-! Bridge from the operational production transaction-policy specification to
the separate-key custody approval construction. Amount and signing bytes are
derived from the admitted transaction; they are not additional host arguments.
This does not claim implementation-level durable-store or threshold-MPC refinement.
-/
public section
namespace Qsag.Custody
set_option autoImplicit false
set_option maxRecDepth 4096

def transactionIntent (tx : TransactionIntent) (round leaf : Nat) : Intent :=
  ⟨ofLE tx.session_id.reverse, round, leaf, tx.amount_units, toCanonicalSigningBytes tx⟩

structure PolicyVault where
  policy : AuthenticatedPolicyState
  vault : Vault

/-- Both policy evaluation and resource reservation burn before signing. A
rejected request clears any older volatile grant while retaining durable burns.
Policy admission may burn even if the later MAC/resource check rejects, which
is deliberately fail-closed and does not refund an already authorized spend. -/
def mintTransaction (p : RoundPolicy) (cap anchor : Nat) (st : PolicyVault)
    (tx : TransactionIntent) (tags : List InitiatorPeerTag) (timestamp round leaf : Nat)
    (ops : List RoundOpening) : PolicyVault :=
  let cleared := forget st.vault
  match authenticatedPolicyGuardStep st.policy tx tags timestamp with
  | .accepted policy' _ =>
    let r := transactionIntent tx round leaf
    ⟨policy', mint p cap anchor cleared ⟨r, roundCommitment r, ops⟩⟩
  | .rejected _ _ => ⟨st.policy, cleared⟩

/-- No hypothetical approval judgement is an argument: admission is recovered
from a successful execution of the actual policy-and-mediation entry point. -/
theorem transaction_grant_admitted (p : RoundPolicy) (cap anchor : Nat) (st : PolicyVault)
    (tx : TransactionIntent) (tags : List InitiatorPeerTag) (timestamp round leaf : Nat)
    (ops : List RoundOpening) (r : Intent)
    (h : (mintTransaction p cap anchor st tx tags timestamp round leaf ops).vault.active = some r) :
    policyCheckAdmission st.policy tx tags timestamp = true ∧
    r = transactionIntent tx round leaf ∧
    checkRound p r (roundCommitment r) ops = true := by
  by_cases ha : policyCheckAdmission st.policy tx tags timestamp = true
  · simp only [mintTransaction, authenticatedPolicyGuardStep, ha, ↓reduceIte] at h
    obtain ⟨hg, he⟩ := mint_granted p cap anchor (forget st.vault)
      ⟨transactionIntent tx round leaf, roundCommitment (transactionIntent tx round leaf), ops⟩
      r rfl h
    change transactionIntent tx round leaf = r at he
    refine ⟨ha, he.symm, ?_⟩
    have hm := (Bool.and_eq_true_iff.mp hg).2
    rw [← he]
    exact hm
  · simp only [mintTransaction, authenticatedPolicyGuardStep, ha] at h
    cases h

/-- The resource charge and signed message come from the exact transaction
that passed wire-width, time, pinned-policy, initiator-authentication, nonce,
session, recipient and rolling-spend checks. -/
theorem transaction_grant_binding (p : RoundPolicy) (cap anchor : Nat) (st : PolicyVault)
    (tx : TransactionIntent) (tags : List InitiatorPeerTag) (timestamp round leaf : Nat)
    (ops : List RoundOpening) (r : Intent)
    (h : (mintTransaction p cap anchor st tx tags timestamp round leaf ops).vault.active = some r) :
    r.spend = tx.amount_units ∧ r.message = toCanonicalSigningBytes tx ∧
    tx.amount_units ≤ st.policy.rules.per_tx_cap ∧
    policyProjectedSpend st.policy tx ≤ st.policy.rules.velocity_window_cap ∧
    policyAuthenticatedInitiator st.policy tx tags = true := by
  obtain ⟨ha, hr, _⟩ := transaction_grant_admitted p cap anchor st tx tags timestamp round leaf ops r h
  have hb := policyAdmission_wire_and_burns ha
  rw [hr]
  exact ⟨rfl, rfl, hb.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.2⟩

theorem transaction_rejected_clears_grant (p : RoundPolicy) (cap anchor : Nat) (st : PolicyVault)
    (tx : TransactionIntent) (tags : List InitiatorPeerTag) (timestamp round leaf : Nat)
    (ops : List RoundOpening) (h : policyCheckAdmission st.policy tx tags timestamp = false) :
    (mintTransaction p cap anchor st tx tags timestamp round leaf ops).vault.active = none ∧
    (mintTransaction p cap anchor st tx tags timestamp round leaf ops).vault.durable = st.vault.durable := by
  simp only [mintTransaction, authenticatedPolicyGuardStep, h, Bool.false_eq_true, ↓reduceIte]
  exact ⟨rfl, rfl⟩

/-- After admission, changing the asserted amount at release cannot substitute
another transaction or reuse an older grant. -/
theorem transaction_wrong_amount_rejected (cfg : SigningConfig) (sk : PqSecretKey)
    (party : Nat) (p : RoundPolicy) (cap anchor : Nat) (st : PolicyVault)
    (tx : TransactionIntent) (tags : List InitiatorPeerTag) (timestamp round leaf : Nat)
    (ops : List RoundOpening) (r bad : Intent)
    (h : (mintTransaction p cap anchor st tx tags timestamp round leaf ops).vault.active = some r)
    (hne : bad.spend ≠ tx.amount_units) :
    (release cfg sk party (anchor + 1)
      (mintTransaction p cap anchor st tx tags timestamp round leaf ops).vault bad).2 = none := by
  apply release_wrong_request cfg sk party (anchor + 1) _ bad r h
  intro he
  exact hne ((congrArg Intent.spend he).trans
    (transaction_grant_binding p cap anchor st tx tags timestamp round leaf ops r h).1)

/-- No successful release can bypass the policy result, even if a stale handle
was live before this mint attempt. -/
theorem transaction_release_binding (cfg : SigningConfig) (sk : PqSecretKey)
    (party releaseAnchor : Nat) (p : RoundPolicy) (cap anchor : Nat) (st : PolicyVault)
    (tx : TransactionIntent) (tags : List InitiatorPeerTag) (timestamp round leaf : Nat)
    (ops : List RoundOpening) (r : Intent) (c : Certificate)
    (h : (release cfg sk party releaseAnchor
      (mintTransaction p cap anchor st tx tags timestamp round leaf ops).vault r).2 = some c) :
    policyCheckAdmission st.policy tx tags timestamp = true ∧
    c.intent.spend = tx.amount_units ∧ c.intent.message = toCanonicalSigningBytes tx ∧
    verify cfg (derivePublicKey cfg.suite cfg.params sk) c.party c.intent c.signature = true := by
  have hv := release_verifies cfg sk party releaseAnchor _ r c h
  have hout := release_output cfg sk party releaseAnchor _ r c h
  have ha : (mintTransaction p cap anchor st tx tags timestamp round leaf ops).vault.active = some r := by
    unfold release at h
    split at h
    · cases h
    · split at h
      next ha => exact ha
      next => cases h
  have had := (transaction_grant_admitted p cap anchor st tx tags timestamp round leaf ops r ha).1
  have hb := transaction_grant_binding p cap anchor st tx tags timestamp round leaf ops r ha
  exact ⟨had, hout.2.1 ▸ hb.1, hout.2.1 ▸ hb.2.1, hv⟩

/-- Complete local entry point. Signer identity, amount, message and session are
derived from local policy state and the admitted transaction. Failed signing
returns the already-burned state. The split mint/release API remains available
to model crashes and forgetting between these atomic transitions. -/
def executeTransaction (cfg : SigningConfig) (sk : PqSecretKey)
    (p : RoundPolicy) (cap anchor : Nat) (st : PolicyVault)
    (tx : TransactionIntent) (tags : List InitiatorPeerTag) (timestamp round leaf : Nat)
    (ops : List RoundOpening) : PolicyVault × Option Certificate :=
  let granted := mintTransaction p cap anchor st tx tags timestamp round leaf ops
  let (v, out) := release cfg sk st.policy.party granted.vault.durable.anchor granted.vault
    (transactionIntent tx round leaf)
  (⟨granted.policy, v⟩, out)

/-- Ordinary policy rejection does not invent an anchor advance or poison a
healthy vault. The separate mint transition still rejects a real anchor mismatch. -/
theorem executeTransaction_rejected (cfg : SigningConfig) (sk : PqSecretKey)
    (p : RoundPolicy) (cap anchor : Nat) (st : PolicyVault)
    (tx : TransactionIntent) (tags : List InitiatorPeerTag) (timestamp round leaf : Nat)
    (ops : List RoundOpening) (ha : policyCheckAdmission st.policy tx tags timestamp = false) :
    (executeTransaction cfg sk p cap anchor st tx tags timestamp round leaf ops).1.vault =
      forget st.vault ∧
    (executeTransaction cfg sk p cap anchor st tx tags timestamp round leaf ops).2 = none := by
  cases hp : st.vault.poisoned <;>
    simp [executeTransaction, mintTransaction, authenticatedPolicyGuardStep, ha, release, forget, hp]

theorem executeTransaction_sound (cfg : SigningConfig) (sk : PqSecretKey)
    (p : RoundPolicy) (cap anchor : Nat) (st : PolicyVault)
    (tx : TransactionIntent) (tags : List InitiatorPeerTag) (timestamp round leaf : Nat)
    (ops : List RoundOpening) (c : Certificate)
    (h : (executeTransaction cfg sk p cap anchor st tx tags timestamp round leaf ops).2 = some c) :
    c.party = st.policy.party ∧
    policyCheckAdmission st.policy tx tags timestamp = true ∧
    c.intent.spend = tx.amount_units ∧ c.intent.message = toCanonicalSigningBytes tx ∧
    verify cfg (derivePublicKey cfg.suite cfg.params sk) c.party c.intent c.signature = true := by
  exact ⟨(release_output cfg sk st.policy.party _ _ _ c h).1,
    transaction_release_binding cfg sk st.policy.party _ p cap anchor st tx tags timestamp round leaf
      ops (transactionIntent tx round leaf) c h⟩

/-- The policy adapter uses the same local trace semantics whose oracle log,
one-time discipline and burn accounting are consumed by the quorum spine. -/
theorem executeTransaction_local_trace (cfg : SigningConfig) (sk : PqSecretKey)
    (p : RoundPolicy) (cap anchor : Nat) (st : PolicyVault)
    (tx : TransactionIntent) (tags : List InitiatorPeerTag) (timestamp round leaf : Nat)
    (ops : List RoundOpening) (ha : policyCheckAdmission st.policy tx tags timestamp = true) :
    (executeTransaction cfg sk p cap anchor st tx tags timestamp round leaf ops).1.vault =
      run cfg sk st.policy.party p cap st.vault
        [.forget,
         .mint anchor ⟨transactionIntent tx round leaf,
           roundCommitment (transactionIntent tx round leaf), ops⟩,
         .release (mint p cap anchor (forget st.vault)
           ⟨transactionIntent tx round leaf, roundCommitment (transactionIntent tx round leaf), ops⟩).durable.anchor
           (transactionIntent tx round leaf)] := by
  simp only [executeTransaction, mintTransaction, authenticatedPolicyGuardStep, ha, ↓reduceIte,
    run, step]

theorem mint_attempted (p : RoundPolicy) (cap anchor : Nat) (v : Vault) (b : Burn) :
    (mint p cap anchor v b).attempted = v.attempted := by
  unfold mint
  split
  · rfl
  · split <;> rfl

theorem mintTransaction_attempted (p : RoundPolicy) (cap anchor : Nat) (st : PolicyVault)
    (tx : TransactionIntent) (tags : List InitiatorPeerTag) (timestamp round leaf : Nat)
    (ops : List RoundOpening) :
    (mintTransaction p cap anchor st tx tags timestamp round leaf ops).vault.attempted =
      st.vault.attempted := by
  unfold mintTransaction
  split
  · exact mint_attempted p cap anchor (forget st.vault) _
  · rfl

theorem mintTransaction_safe (p : RoundPolicy) (cap anchor : Nat) (st : PolicyVault)
    (tx : TransactionIntent) (tags : List InitiatorPeerTag) (timestamp round leaf : Nat)
    (ops : List RoundOpening) (hs : Safe p cap st.vault) :
    Safe p cap (mintTransaction p cap anchor st tx tags timestamp round leaf ops).vault := by
  unfold mintTransaction
  split
  · exact mint_safe p cap anchor (forget st.vault) _ (forget_safe p cap st.vault hs)
  · exact forget_safe p cap st.vault hs

theorem executeTransaction_safe (cfg : SigningConfig) (sk : PqSecretKey)
    (p : RoundPolicy) (cap anchor : Nat) (st : PolicyVault)
    (tx : TransactionIntent) (tags : List InitiatorPeerTag) (timestamp round leaf : Nat)
    (ops : List RoundOpening) (hs : Safe p cap st.vault) :
    Safe p cap (executeTransaction cfg sk p cap anchor st tx tags timestamp round leaf ops).1.vault :=
  release_safe cfg sk st.policy.party _ p cap _ _
    (mintTransaction_safe p cap anchor st tx tags timestamp round leaf ops hs)

theorem executeTransaction_party (cfg : SigningConfig) (sk : PqSecretKey)
    (p : RoundPolicy) (cap anchor : Nat) (st : PolicyVault)
    (tx : TransactionIntent) (tags : List InitiatorPeerTag) (timestamp round leaf : Nat)
    (ops : List RoundOpening) :
    (executeTransaction cfg sk p cap anchor st tx tags timestamp round leaf ops).1.policy.party =
      st.policy.party := by
  by_cases ha : policyCheckAdmission st.policy tx tags timestamp = true
  · simp only [executeTransaction, mintTransaction, authenticatedPolicyGuardStep, ha, ↓reduceIte]
  · simp only [executeTransaction, mintTransaction, authenticatedPolicyGuardStep, ha, Bool.false_eq_true, ↓reduceIte]

/-- Signing-attempt provenance includes the actual optional output, so a
failed signer call cannot later be presented as an issued certificate. -/
theorem executeTransaction_attempt_origin (cfg : SigningConfig) (sk : PqSecretKey)
    (p : RoundPolicy) (cap anchor : Nat) (st : PolicyVault)
    (tx : TransactionIntent) (tags : List InitiatorPeerTag) (timestamp round leaf : Nat)
    (ops : List RoundOpening) (r : Intent)
    (hm : r ∈ (executeTransaction cfg sk p cap anchor st tx tags timestamp round leaf ops).1.vault.attempted) :
    r ∈ st.vault.attempted ∨
      (policyCheckAdmission st.policy tx tags timestamp = true ∧
       r = transactionIntent tx round leaf ∧
       (executeTransaction cfg sk p cap anchor st tx tags timestamp round leaf ops).2 =
         (sign cfg sk st.policy.party r).map (fun sig => ⟨st.policy.party, r, sig⟩)) := by
  let granted := mintTransaction p cap anchor st tx tags timestamp round leaf ops
  have hattempt : granted.vault.attempted = st.vault.attempted :=
    mintTransaction_attempted p cap anchor st tx tags timestamp round leaf ops
  change r ∈ (release cfg sk st.policy.party granted.vault.durable.anchor granted.vault
    (transactionIntent tx round leaf)).1.attempted at hm
  change _ ∨ (_ ∧ _ ∧ (release cfg sk st.policy.party granted.vault.durable.anchor granted.vault
    (transactionIntent tx round leaf)).2 = _)
  unfold release at hm ⊢
  split at hm
  next hp => exact .inl (hattempt ▸ hm)
  next hp =>
    split at hm
    next ha =>
      rcases List.mem_cons.mp hm with he | hold
      · have had := (transaction_grant_admitted p cap anchor st tx tags timestamp round leaf ops
          (transactionIntent tx round leaf) ha).1
        refine .inr ⟨had, he, ?_⟩
        simp only [hp, ha, Bool.false_eq_true, ↓reduceIte, he]
      · exact .inl (hattempt ▸ hold)
    next ha => exact .inl (hattempt ▸ hm)

end Qsag.Custody
end
set_option maxRecDepth 4096
#verify_constructive Qsag.Custody.transaction_grant_admitted
#verify_constructive Qsag.Custody.transaction_grant_binding
#verify_constructive Qsag.Custody.transaction_release_binding
#verify_constructive Qsag.Custody.transaction_wrong_amount_rejected
#verify_constructive Qsag.Custody.executeTransaction_sound
#verify_constructive Qsag.Custody.executeTransaction_local_trace
#verify_constructive Qsag.Custody.executeTransaction_rejected
