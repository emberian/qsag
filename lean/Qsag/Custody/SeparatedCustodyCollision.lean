module
public import Qsag.Custody.SeparatedCustodyHistory
public import Qsag.Protocol.Signing.ProdCollisionExtraction
import all Qsag.Custody.SeparatedCustodyHistory
import all Qsag.Custody.SeparatedCustodyPolicy
import all Qsag.Custody.SeparatedCustodySpine
import all Qsag.Custody.CompleteMediationBoundary
import all Qsag.Custody.SeparatedCustodyCore
import all Qsag.Protocol.Signing.HypertreeEufCma
import all Qsag.Protocol.Signing.ProdCollisionExtraction
import all Qsag.Protocol.Signing.ProdCollisionLayers
import all Qsag.Protocol.Signing.ProdCollisionWitness
import Qsag.Tactic.AssuranceKit

/-! Custody consumers of the returned production collision witness.

`accepted_quorum_approval_or_hash_break` and `generated_submit_provenance` end, in their
signature-game branch, in `ProdSmTcrBreak ∨ ProdPreimageBreak`. `ProdSmTcrBreak` is an existential
over every honest hash input of the custodian key and does not mention the accepted certificate.
The two theorems here keep every other part of those statements and replace that disjunct by a
`ProdTcrWitness` for the accepted certificate itself: a collision with an honest input on the
verification path of `(payload c.party r, c.signature)`, at a hash call the verifier makes on that
certificate. `returned_break_implies_hash_break` shows the new branch implies the old one, so the
existing theorems are corollaries and are not weakened.

These remain structural extraction statements: no probability, no oracle model of the hash, no
running time.
-/
public section
namespace Qsag.Custody
set_option autoImplicit false
set_option maxRecDepth 4096

/-- The returned-witness branch implies the existential branch of the existing theorems. -/
theorem returned_break_implies_hash_break (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (log : List (List UInt8 × PqHashSig)) (msg : List UInt8) (sig : PqHashSig)
    (h : Nonempty (ProdTcrWitness suite params sk log msg sig) ∨
      ProdPreimageBreak suite params sk log msg sig) :
    ProdSmTcrBreak suite params sk log ∨ ProdPreimageBreak suite params sk log msg sig :=
  match h with
  | .inl ⟨w⟩ => .inl w.toSmTcrBreak
  | .inr hp => .inr hp

/-- `accepted_quorum_approval_or_hash_break` with the collision returned for the accepted
certificate. -/
theorem accepted_quorum_approval_or_returned_break
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
       (Nonempty (ProdTcrWitness cfg.suite cfg.params (keys c.party)
         (signingLog cfg (keys c.party) c.party (stateAfter cfg keys policies caps traces c.party))
         (payload c.party r) c.signature) ∨
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
    exact production_stateful_forgery_witness cfg.suite cfg.params (keys c.party)
      (queries cfg c.party v) (payload c.party r) c.signature hw hst
      (queries_one_time cfg c.party _ _ v hs)
      (log_fresh_of_not_attempted cfg (keys c.party) c.party v r hm) hv

/-- `generated_submit_provenance` with the collision returned for the accepted certificate. At
every generated-history prefix, an accepted quorum has an honest certificate whose full intent
was produced by an earlier admitted policy invocation, or that certificate wins the signature game
and its verification yields a collision on its own path or the WOTS preimage event. -/
theorem generated_submit_provenance_returned (d : Deployment) (commands : List HistoryCommand)
    (corrupt : List Nat) (r : Intent) (cs : List Certificate)
    (hw : d.signer.params.w = 4 ∨ d.signer.params.w = 16)
    (hst : d.signer.params.statefulJorts = true) (hc : corrupt.length < d.threshold)
    (ha : (submitRecorded d (generatedHistory d commands).shared r cs).2 = true) :
    ∃ c ∈ cs, c.party ∉ corrupt ∧
      (ProducedPolicyApproval d (generatedHistory d commands) c.party r ∨
       (prodEufCmaWin d.signer.suite d.signer.params
          ⟨d.keys c.party,
            queries d.signer c.party ((generatedHistory d commands).parties c.party).vault,
            payload c.party r, c.signature⟩ = true ∧
        (Nonempty (ProdTcrWitness d.signer.suite d.signer.params (d.keys c.party)
           (signingLog d.signer (d.keys c.party) c.party
             ((generatedHistory d commands).parties c.party).vault)
           (payload c.party r) c.signature) ∨
         ProdPreimageBreak d.signer.suite d.signer.params (d.keys c.party)
           (signingLog d.signer (d.keys c.party) c.party
             ((generatedHistory d commands).parties c.party).vault)
           (payload c.party r) c.signature))) := by
  let s := generatedHistory d commands
  have hs : Generated d s := generatedHistory_valid d commands
  rw [submitRecorded_verdict] at ha
  obtain ⟨c, hcm, hch, _, hv⟩ := quorum_has_honest d.signer (publicKeys d)
    d.numParties d.threshold s.shared.coordinator.consumedSessions corrupt r cs hc
    (submit_accepted _ _ _ _ _ _ _ ha).1
  refine ⟨c, hcm, hch, ?_⟩
  by_cases hm : payload c.party r ∈
      (signingLog d.signer (d.keys c.party) c.party (s.parties c.party).vault).map Prod.fst
  · exact .inl (successful_log_produced d s c.party r hs hst hm)
  · have hf : ∀ e ∈ signingLog d.signer (d.keys c.party) c.party (s.parties c.party).vault,
        e.1 ≠ payload c.party r := by
      intro e he heq
      exact hm (List.mem_map.mpr ⟨e, he, heq⟩)
    right
    refine ⟨?_, ?_⟩
    · unfold prodEufCmaWin
      exact Bool.and_eq_true_iff.mpr ⟨hv, decide_eq_true hm⟩
    · exact production_stateful_forgery_witness d.signer.suite d.signer.params (d.keys c.party)
        (queries d.signer c.party (s.parties c.party).vault) (payload c.party r) c.signature hw hst
        (queries_one_time d.signer c.party _ _ _ (hs.safe c.party)) hf hv

end Qsag.Custody
end
set_option maxRecDepth 4096
#verify_constructive Qsag.Custody.returned_break_implies_hash_break
#verify_constructive Qsag.Custody.accepted_quorum_approval_or_returned_break
#verify_constructive Qsag.Custody.generated_submit_provenance_returned
