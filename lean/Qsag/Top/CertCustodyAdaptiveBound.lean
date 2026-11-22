module
/-
# Qsag.Top.CertCustodyAdaptiveBound — the certificate-pool coordinator against an adaptive
# adversary, reduced to the tag-forgery experiment under `Spec.PrfHard`

**Scope.**

1. Step equations of `certCustodyMachine` by input (`certRunStep_approve`, `_submit`, `_corrupt`,
   `_sign_frame`), derived from the exported equations of `Qsag.Top.Custody`, and the forgery
   event of one step: a certificate is logged exactly when it is submitted, verifies for the
   deployment, and asserts a permit of a party that is then uncorrupted and has not issued it
   (`certRunStep_forgery_origin`, `certRunStep_forgery_flagged`).
2. The adaptive certificate world. An adversary is a `Spec.Code` program over `certAdvIface`:
   each query is an input of the coordinator; the answer is the outcome, the issued certificate
   of an accepted `.approve`, and the party's key of an accepted `.corrupt`. `certWorldOracle`
   threads the machine state with `Machine.runStep` for at most `budget` queries.
   `certAdaptiveRun_state_eq_certRun`: the final state is `certRun` of the inputs the adversary
   issued, so the theorems about `certRun` apply
   (`certAdaptiveRun_unsafe_release_forgery`).
3. `encTagCertLayer prf enc key`: certificate `(prf (key p) (enc permit), permit)`. With
   `enc = KeyHidingCustody.permitInput dg` it is the definition of `prfCertLayer` in
   `Qsag.Top.CustodyKeyHidingBound` (tag `prfCustodyTag`), restated here because that
   definition's projections are not available to importers.
4. The reduction. `redCode r keys' A j` is a tag-forgery adversary (a program over
   `KeyHidingCustody.tagIface`) for key index `r`: it runs `A`, simulates the coordinator with
   the other keys, answers approvals under key `r` with its tag oracle, verifies submitted
   certificates for issued permits against the tags it received, stops when a party with key
   `r` is corrupted, and outputs the `j`-th submission for a permit of key `r` that was not
   issued. `red_sim` proves, per run and by induction on `A`, that the answers it gives `A` are
   those of the certificate world until it outputs, and that a forgery event for key `r` makes
   it output a correct tag on a permit its oracle was not asked, for some `j` below the budget.
   `redCode_within`: at most `budget` oracle queries.
5. `certCustody_adaptive_unsafe_release_bound`:
   `Pr[unsafe release] ≤ (numParties + 1) * budget * (εPrf + 256 ^ (-outLen) + εColl)`
   under `Spec.PrfHard … (budget + 1) εPrf`, by `KeyHidingCustody.prfCustodyTag_unforgeable` and
   `KeyHidingCustody.event_le_family_reductions`. The witness-extraction form
   `certAdaptiveRun_unsafe_release_fresh_forgery_or_collision` gives, per run, a forgery on a
   fresh PRF input or an explicit `Spec.HashCollision dg`.
6. Negative results: a tag that equals the key is broken with probability one by an adversary
   that reads one honest certificate
   (`certCustody_tooth_key_revealing_tag_adaptive_unsafe_release`); with one-byte tags, `257`
   queries give an unsafe release with certainty, so the bound must depend on the number of
   submissions (`certCustody_tooth_guess_all_tags_unsafe_release`); a certificate for any party
   identifier, enrolled or not, is a forgery event when that party did not issue it
   (`certCustody_tooth_unissued_claim_flagged`).
7. `partyCoinSplit` isolates any one of the independently sampled party coordinates.
   `inhabited_certCustody_adaptive` constructs all premises jointly for every positive party
   count, with one further key for unenrolled identifiers. Its one-byte PRF has a singleton
   input domain and exact advantage zero. The reduction for the submit-then-sign strategy
   makes no tag queries. In the 1-of-1 instance, `certCustody_one_guess_nontrivial` proves both
   existence of a winning coin and the upper bound 4/256 for the same game.

The union bound counts a guess of the first successful submission and every key that can
occur in the forgery log. The generic reduction takes a PRF bound, membership of its
distinguishers, a digest collision-game bound and the independent-key sampling hypotheses.
`prfSample_shiftClosed` establishes closure of the full challenger support for all lengths.
The experiment models the certificate-pool coordinator. The authenticated custodian network
uses a separate machine, `authRun`.

-/

public import Qsag.Protocol.Threshold.ComputationalMacBlind
public import Qsag.Top.Custody
public import Qsag.Custody.KeyHidingAuthCustodyBound
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Top

open Qsag.Spec Qsag.KeyHidingCustody

set_option autoImplicit false

private theorem ifP.{u} {α : Sort u} {p : Prop} [Decidable p] (hp : p) (a b : α) :
    (if p then a else b) = a := by
  cases ‹Decidable p› with
  | isTrue _ => rfl
  | isFalse hn => exact False.elim (hn hp)

private theorem ifN.{u} {α : Sort u} {p : Prop} [Decidable p] (hnp : ¬ p) (a b : α) :
    (if p then a else b) = b := by
  cases ‹Decidable p› with
  | isTrue hp => exact False.elim (hnp hp)
  | isFalse _ => rfl

/-! ## 1. One step of the certificate-pool coordinator, by input -/

section Step

variable {PK D Sig Cert : Type} [DecidableEq D]
variable (L : CustodyCertLayer Cert) (S : CustodyDigestScheme D) (oracleSign : D → Sig)
variable (dep₀ : Nat) (pk₀ : PK) (quorum₀ : CustodyQuorumProfile)

private theorem certRunStep_of_none {c : CertCustodyState PK D Sig Cert} {inp : CertCustodyInput Cert}
    (h : certCustodyStep L S oracleSign c inp = none) :
    (certCustodyMachine L S oracleSign dep₀ pk₀ quorum₀).runStep c inp = (c, none) := by
  rw [certCustodyMachine.public_eqs]
  unfold Machine.runStep
  dsimp only
  rw [h]

private theorem certRunStep_of_some {c c' : CertCustodyState PK D Sig Cert} {inp : CertCustodyInput Cert}
    {o : CustodyOutcome Sig} (h : certCustodyStep L S oracleSign c inp = some (c', o)) :
    (certCustodyMachine L S oracleSign dep₀ pk₀ quorum₀).runStep c inp = (c', some o) := by
  rw [certCustodyMachine.public_eqs]
  unfold Machine.runStep
  dsimp only
  rw [h]

/-- An honest approval: accepted for an enrolled, uncorrupted party and the ledger's deployment;
    it records the permit as issued. -/
theorem certRunStep_approve (c : CertCustodyState PK D Sig Cert) (p dep : Nat)
    (i : CustodyIntent) :
    (certCustodyMachine L S oracleSign dep₀ pk₀ quorum₀).runStep c (.approve p dep i) =
      if p < c.ledger.quorum.numParties ∧ p ∉ c.corruptParties ∧ dep = c.ledger.deploymentId then
        ({ c with issued := CustodyApproval.mk p dep i :: c.issued }, some .approvalRecorded)
      else (c, none) := by
  by_cases hg : p < c.ledger.quorum.numParties ∧ p ∉ c.corruptParties ∧
      dep = c.ledger.deploymentId
  · rw [ifP hg]
    exact certRunStep_of_some L S oracleSign dep₀ pk₀ quorum₀
      (by rw [certCustodyStep.public_eq_1, ifP hg])
  · rw [ifN hg]
    exact certRunStep_of_none L S oracleSign dep₀ pk₀ quorum₀
      (by rw [certCustodyStep.public_eq_1, ifN hg])

/-- A submission: admitted when the certificate verifies for the ledger's deployment. -/
theorem certRunStep_submit (c : CertCustodyState PK D Sig Cert) (x : Cert) :
    (certCustodyMachine L S oracleSign dep₀ pk₀ quorum₀).runStep c (.submit x) =
      if L.valid x = true ∧ (L.claim x).deploymentId = c.ledger.deploymentId then
        ({ c with
            pool := x :: c.pool
            advClaims := certAdvClaims L c x
            forgeries := certForgeries L c x }, some .approvalRecorded)
      else (c, none) := by
  by_cases hg : L.valid x = true ∧ (L.claim x).deploymentId = c.ledger.deploymentId
  · rw [ifP hg]
    exact certRunStep_of_some L S oracleSign dep₀ pk₀ quorum₀
      (by rw [certCustodyStep.public_eq_2, ifP hg])
  · rw [ifN hg]
    exact certRunStep_of_none L S oracleSign dep₀ pk₀ quorum₀
      (by rw [certCustodyStep.public_eq_2, ifN hg])

/-- A corruption: accepted for an enrolled, uncorrupted party while fewer than `threshold - 1`
    parties are corrupted. -/
theorem certRunStep_corrupt (c : CertCustodyState PK D Sig Cert) (p : Nat) :
    (certCustodyMachine L S oracleSign dep₀ pk₀ quorum₀).runStep c (.corrupt p) =
      if p < c.ledger.quorum.numParties ∧ p ∉ c.corruptParties ∧
          c.corruptParties.length + 1 < c.ledger.quorum.threshold then
        ({ c with corruptParties := p :: c.corruptParties },
          some (.corrupted (custodyRevealed c.issued p)))
      else (c, none) := by
  by_cases hg : p < c.ledger.quorum.numParties ∧ p ∉ c.corruptParties ∧
      c.corruptParties.length + 1 < c.ledger.quorum.threshold
  · rw [ifP hg]
    exact certRunStep_of_some L S oracleSign dep₀ pk₀ quorum₀
      (by rw [certCustodyStep.public_eq_3, ifP hg])
  · rw [ifN hg]
    exact certRunStep_of_none L S oracleSign dep₀ pk₀ quorum₀
      (by rw [certCustodyStep.public_eq_3, ifN hg])

/-- A signing step changes the ledger only, and not its quorum profile. -/
theorem certRunStep_sign_frame (c : CertCustodyState PK D Sig Cert) (dep : Nat)
    (i : CustodyIntent) (ab : Bool) :
    ((certCustodyMachine L S oracleSign dep₀ pk₀ quorum₀).runStep c
        (.sign dep i ab)).1.corruptParties = c.corruptParties ∧
    ((certCustodyMachine L S oracleSign dep₀ pk₀ quorum₀).runStep c
        (.sign dep i ab)).1.issued = c.issued ∧
    ((certCustodyMachine L S oracleSign dep₀ pk₀ quorum₀).runStep c
        (.sign dep i ab)).1.forgeries = c.forgeries ∧
    ((certCustodyMachine L S oracleSign dep₀ pk₀ quorum₀).runStep c
        (.sign dep i ab)).1.ledger.quorum = c.ledger.quorum := by
  cases h : custodyLedgerSign S oracleSign c.ledger
      (certApprovers L c.ledger.quorum.numParties c.pool c.ledger.deploymentId i).length
      dep i ab with
  | none =>
    rw [certRunStep_of_none L S oracleSign dep₀ pk₀ quorum₀
      (by rw [certCustodyStep.public_eq_4, h]; rfl)]
    exact ⟨rfl, rfl, rfl, rfl⟩
  | some r =>
    obtain ⟨l', o⟩ := r
    rw [certRunStep_of_some L S oracleSign dep₀ pk₀ quorum₀
      (c' := { c with ledger := l' }) (o := o)
      (by rw [certCustodyStep.public_eq_4, h]; rfl)]
    exact ⟨rfl, rfl, rfl, (custodyLedgerSign_static h).2.2⟩

/-- **The forgery event of one step.** A certificate enters the forgery log exactly when it is
    submitted, verifies for the ledger's deployment, and asserts a permit of a party that at that
    moment is uncorrupted and has not issued that permit. -/
theorem certRunStep_forgery_origin {c : CertCustodyState PK D Sig Cert}
    {inp : CertCustodyInput Cert} {x : Cert}
    (hx : x ∈ ((certCustodyMachine L S oracleSign dep₀ pk₀ quorum₀).runStep c inp).1.forgeries) :
    x ∈ c.forgeries ∨
      (inp = .submit x ∧ L.valid x = true ∧
        (L.claim x).deploymentId = c.ledger.deploymentId ∧
        (L.claim x).party ∉ c.corruptParties ∧ L.claim x ∉ c.issued) := by
  cases inp with
  | approve p dep i =>
    rw [certRunStep_approve] at hx
    by_cases hg : p < c.ledger.quorum.numParties ∧ p ∉ c.corruptParties ∧
        dep = c.ledger.deploymentId
    · rw [ifP hg] at hx; exact .inl hx
    · rw [ifN hg] at hx; exact .inl hx
  | submit y =>
    rw [certRunStep_submit] at hx
    by_cases hg : L.valid y = true ∧ (L.claim y).deploymentId = c.ledger.deploymentId
    · rw [ifP hg] at hx
      have hx' : x ∈ certForgeries L c y := hx
      rw [certForgeries.public_eqs] at hx'
      by_cases hc : (L.claim y).party ∉ c.corruptParties ∧ L.claim y ∉ c.issued
      · rw [ifP hc] at hx'
        rcases List.mem_cons.mp hx' with hEq | hT
        · subst hEq
          exact .inr ⟨rfl, hg.1, hg.2, hc.1, hc.2⟩
        · exact .inl hT
      · rw [ifN hc] at hx'
        exact .inl hx'
    · rw [ifN hg] at hx; exact .inl hx
  | corrupt p =>
    rw [certRunStep_corrupt] at hx
    by_cases hg : p < c.ledger.quorum.numParties ∧ p ∉ c.corruptParties ∧
        c.corruptParties.length + 1 < c.ledger.quorum.threshold
    · rw [ifP hg] at hx; exact .inl hx
    · rw [ifN hg] at hx; exact .inl hx
  | sign dep i ab =>
    rw [(certRunStep_sign_frame L S oracleSign dep₀ pk₀ quorum₀ c dep i ab).2.2.1] at hx
    exact .inl hx

/-- The converse: such a submission is logged as a forgery. -/
theorem certRunStep_forgery_flagged (c : CertCustodyState PK D Sig Cert) (x : Cert)
    (hV : L.valid x = true) (hD : (L.claim x).deploymentId = c.ledger.deploymentId)
    (hC : (L.claim x).party ∉ c.corruptParties) (hI : L.claim x ∉ c.issued) :
    ((certCustodyMachine L S oracleSign dep₀ pk₀ quorum₀).runStep c (.submit x)).1.forgeries =
      x :: c.forgeries := by
  rw [certRunStep_submit, ifP (And.intro hV hD)]
  show certForgeries L c x = _
  rw [certForgeries.public_eqs, ifP (And.intro hC hI)]

theorem certRun_nil :
    certRun L S oracleSign dep₀ pk₀ quorum₀ [] =
      (CertCustodyState.init dep₀ pk₀ quorum₀ : CertCustodyState PK D Sig Cert) := by
  rw [certRun.public_eqs]
  rfl

theorem certRun_snoc (inps : List (CertCustodyInput Cert)) (inp : CertCustodyInput Cert) :
    certRun L S oracleSign dep₀ pk₀ quorum₀ (inps ++ [inp]) =
      ((certCustodyMachine L S oracleSign dep₀ pk₀ quorum₀).runStep
        (certRun L S oracleSign dep₀ pk₀ quorum₀ inps) inp).1 := by
  rw [certRun.public_eqs, certRun.public_eqs, List.foldl_append]
  rfl

end Step


/-! ## 2. The adaptive certificate world -/

section World

variable {PK D Sig Cert K : Type} [DecidableEq D]

/-- Interface of an adaptive adversary of the certificate world. A query is an input of the
    coordinator; the answer is the outcome of the step (`none` when it is refused), the issued
    certificate of an accepted `.approve`, and the party's key of an accepted `.corrupt`. -/
@[expose, reducible] def certAdvIface (Cert K Sig : Type) : Iface where
  Query := CertCustodyInput Cert
  Resp _ := Option (CustodyOutcome Sig) × Option Cert × Option K

/-- What the adversary learns from a step with outcome `out`. -/
def certAdvResp (L : CustodyCertLayer Cert) (key : Nat → K) (inp : CertCustodyInput Cert)
    (out : Option (CustodyOutcome Sig)) : Option (CustodyOutcome Sig) × Option Cert × Option K :=
  match out, inp with
  | none, _ => (none, none, none)
  | some o, .approve p dep i => (some o, some (L.issue p dep i), none)
  | some o, .corrupt p => (some o, none, some (key p))
  | some o, _ => (some o, none, none)

/-- The challenger of the adaptive certificate world. Its state is the state of
    `certCustodyMachine` and the list of inputs fed so far. The first `budget` queries are fed to
    the machine with `Machine.runStep`; later ones are refused without a step. -/
def certWorldOracle (L : CustodyCertLayer Cert) (key : Nat → K) (S : CustodyDigestScheme D)
    (oracleSign : D → Sig) (dep₀ : Nat) (pk₀ : PK) (quorum₀ : CustodyQuorumProfile)
    (budget : Nat)
    (st : CertCustodyState PK D Sig Cert × List (CertCustodyInput Cert)) :
    (inp : (certAdvIface Cert K Sig).Query) → (certAdvIface Cert K Sig).Resp inp ×
      (CertCustodyState PK D Sig Cert × List (CertCustodyInput Cert)) :=
  fun inp =>
    if st.2.length < budget then
      (certAdvResp L key inp
          ((certCustodyMachine L S oracleSign dep₀ pk₀ quorum₀).runStep st.1 inp).2,
        (((certCustodyMachine L S oracleSign dep₀ pk₀ quorum₀).runStep st.1 inp).1,
          st.2 ++ [inp]))
    else ((none, none, none), st)

theorem certWorldOracle_pos (L : CustodyCertLayer Cert) (key : Nat → K)
    (S : CustodyDigestScheme D) (oracleSign : D → Sig) (dep₀ : Nat) (pk₀ : PK)
    (quorum₀ : CustodyQuorumProfile) (budget : Nat)
    (c : CertCustodyState PK D Sig Cert) (tr : List (CertCustodyInput Cert))
    (h : tr.length < budget) (inp : CertCustodyInput Cert) :
    certWorldOracle L key S oracleSign dep₀ pk₀ quorum₀ budget (c, tr) inp =
      (certAdvResp L key inp
          ((certCustodyMachine L S oracleSign dep₀ pk₀ quorum₀).runStep c inp).2,
        (((certCustodyMachine L S oracleSign dep₀ pk₀ quorum₀).runStep c inp).1, tr ++ [inp])) :=
  ifP h _ _

theorem certWorldOracle_neg (L : CustodyCertLayer Cert) (key : Nat → K)
    (S : CustodyDigestScheme D) (oracleSign : D → Sig) (dep₀ : Nat) (pk₀ : PK)
    (quorum₀ : CustodyQuorumProfile) (budget : Nat)
    (c : CertCustodyState PK D Sig Cert) (tr : List (CertCustodyInput Cert))
    (h : ¬ tr.length < budget) (inp : CertCustodyInput Cert) :
    certWorldOracle L key S oracleSign dep₀ pk₀ quorum₀ budget (c, tr) inp =
      ((none, none, none), (c, tr)) :=
  ifN h _ _

/-- One run of an adaptive adversary `A` against the certificate world from the initial state:
    its output, the final machine state and the list of inputs it issued. -/
def certAdaptiveRun {R : Type} (L : CustodyCertLayer Cert) (key : Nat → K)
    (S : CustodyDigestScheme D) (oracleSign : D → Sig) (dep₀ : Nat) (pk₀ : PK)
    (quorum₀ : CustodyQuorumProfile) (budget : Nat) (A : Code (certAdvIface Cert K Sig) R) :
    R × (CertCustodyState PK D Sig Cert × List (CertCustodyInput Cert)) :=
  Code.play (certWorldOracle L key S oracleSign dep₀ pk₀ quorum₀ budget) A
    (CertCustodyState.init dep₀ pk₀ quorum₀, [])

/-- **The adaptive run is `certRun` of its transcript.** The final machine state of an adaptive
    run is the state `certRun` reaches on the list of inputs the adversary issued. -/
theorem certAdaptiveRun_state_eq_certRun {R : Type} (L : CustodyCertLayer Cert) (key : Nat → K)
    (S : CustodyDigestScheme D) (oracleSign : D → Sig) (dep₀ : Nat) (pk₀ : PK)
    (quorum₀ : CustodyQuorumProfile) (budget : Nat) (A : Code (certAdvIface Cert K Sig) R) :
    (certAdaptiveRun L key S oracleSign dep₀ pk₀ quorum₀ budget A).2.1 =
      certRun L S oracleSign dep₀ pk₀ quorum₀
        (certAdaptiveRun L key S oracleSign dep₀ pk₀ quorum₀ budget A).2.2 :=
  Code.play_invariant (certWorldOracle L key S oracleSign dep₀ pk₀ quorum₀ budget)
    (fun st => st.1 = certRun L S oracleSign dep₀ pk₀ quorum₀ st.2)
    (fun st inp h => by
      obtain ⟨c, tr⟩ := st
      have h' : c = certRun L S oracleSign dep₀ pk₀ quorum₀ tr := h
      by_cases hb : tr.length < budget
      · rw [certWorldOracle_pos L key S oracleSign dep₀ pk₀ quorum₀ budget c tr hb]
        show ((certCustodyMachine L S oracleSign dep₀ pk₀ quorum₀).runStep c inp).1 =
          certRun L S oracleSign dep₀ pk₀ quorum₀ (tr ++ [inp])
        rw [certRun_snoc, ← h']
      · rw [certWorldOracle_neg L key S oracleSign dep₀ pk₀ quorum₀ budget c tr hb]
        exact h)
    A _ (certRun_nil L S oracleSign dep₀ pk₀ quorum₀).symm

/-- The adversary issues at most `budget` inputs. -/
theorem certAdaptiveRun_length_le {R : Type} (L : CustodyCertLayer Cert) (key : Nat → K)
    (S : CustodyDigestScheme D) (oracleSign : D → Sig) (dep₀ : Nat) (pk₀ : PK)
    (quorum₀ : CustodyQuorumProfile) (budget : Nat) (A : Code (certAdvIface Cert K Sig) R) :
    (certAdaptiveRun L key S oracleSign dep₀ pk₀ quorum₀ budget A).2.2.length ≤ budget :=
  Code.play_invariant (certWorldOracle L key S oracleSign dep₀ pk₀ quorum₀ budget)
    (fun st => st.2.length ≤ budget)
    (fun st inp h => by
      obtain ⟨c, tr⟩ := st
      by_cases hb : tr.length < budget
      · rw [certWorldOracle_pos L key S oracleSign dep₀ pk₀ quorum₀ budget c tr hb]
        show (tr ++ [inp]).length ≤ budget
        rw [List.length_append]
        exact hb
      · rw [certWorldOracle_neg L key S oracleSign dep₀ pk₀ quorum₀ budget c tr hb]
        exact h)
    A _ (Nat.zero_le budget)

/-- An adaptive run that ends in an unsafe release has logged a forgery. -/
theorem certAdaptiveRun_unsafe_release_forgery {R : Type} (L : CustodyCertLayer Cert)
    (key : Nat → K) (S : CustodyDigestScheme D) (oracleSign : D → Sig) (dep₀ : Nat) (pk₀ : PK)
    (quorum₀ : CustodyQuorumProfile) (budget : Nat) (A : Code (certAdvIface Cert K Sig) R)
    (hU : certUnsafeRelease quorum₀.numParties dep₀
      (certAdaptiveRun L key S oracleSign dep₀ pk₀ quorum₀ budget A).2.1 = true) :
    (certAdaptiveRun L key S oracleSign dep₀ pk₀ quorum₀ budget A).2.1.forgeries ≠ [] := by
  intro hNF
  rw [certAdaptiveRun_state_eq_certRun] at hU hNF
  rw [certCustody_noForgery_no_unsafe_release L S oracleSign dep₀ pk₀ quorum₀ _ hNF] at hU
  exact Bool.false_ne_true hU

end World

/-! ## 3. Tag certificates and the coordinator's step over them -/

/-- Certificate layer with keyed tags over an encoding `enc` of permits: party `p`'s certificate
    for a permit is the permit with `prf (key p) (enc permit)`; the coordinator recomputes the
    tag. With `enc = KeyHidingCustody.permitInput dg` the tag is
    `KeyHidingCustody.prfCustodyTag prf dg (key p)`, and the layer has the definition of
    `prfCertLayer` in `Qsag.Top.CustodyKeyHidingBound`. -/
def encTagCertLayer (prf : Spec.Bytes → Spec.Bytes → Spec.Bytes)
    (enc : CustodyApproval → Spec.Bytes) (key : Nat → Spec.Bytes) :
    CustodyCertLayer (Spec.Bytes × CustodyApproval) where
  claim c := c.2
  valid c := decide (c.1 = prf (key c.2.party) (enc c.2))
  issue p dep i := (prf (key p) (enc (CustodyApproval.mk p dep i)), CustodyApproval.mk p dep i)
  issue_valid _ _ _ := decide_eq_true rfl
  issue_claim _ _ _ := rfl

theorem encTagCertLayer_claim (prf : Spec.Bytes → Spec.Bytes → Spec.Bytes)
    (enc : CustodyApproval → Spec.Bytes) (key : Nat → Spec.Bytes)
    (x : Spec.Bytes × CustodyApproval) : (encTagCertLayer prf enc key).claim x = x.2 := by
  rfl

theorem encTagCertLayer_valid_iff (prf : Spec.Bytes → Spec.Bytes → Spec.Bytes)
    (enc : CustodyApproval → Spec.Bytes) (key : Nat → Spec.Bytes)
    (x : Spec.Bytes × CustodyApproval) :
    (encTagCertLayer prf enc key).valid x = true ↔ x.1 = prf (key x.2.party) (enc x.2) := by
  unfold encTagCertLayer
  exact decide_eq_true_iff

theorem encTagCertLayer_issue (prf : Spec.Bytes → Spec.Bytes → Spec.Bytes)
    (enc : CustodyApproval → Spec.Bytes) (key : Nat → Spec.Bytes) (p dep : Nat)
    (i : CustodyIntent) :
    (encTagCertLayer prf enc key).issue p dep i =
      (prf (key p) (enc (CustodyApproval.mk p dep i)), CustodyApproval.mk p dep i) := by
  rfl

/-- Over `permitInput dg` the layer verifies `prfCustodyTag`. -/
theorem encTagCertLayer_permitInput_valid_iff (prf : Spec.Bytes → Spec.Bytes → Spec.Bytes)
    (dg : Spec.Bytes → Spec.Bytes) (key : Nat → Spec.Bytes) (x : Spec.Bytes × CustodyApproval) :
    (encTagCertLayer prf (permitInput dg) key).valid x = true ↔
      x.1 = prfCustodyTag prf dg (key x.2.party) x.2 := by
  rw [encTagCertLayer_valid_iff, prfCustodyTag_eq]

/-- The coordinator's vote count reads a certificate layer through `claim` only. -/
theorem certApprovers_claim_congr {Cert : Type} (L L' : CustodyCertLayer Cert)
    (hC : ∀ x, L.claim x = L'.claim x) (n : Nat) (pool : List Cert) (dep : Nat)
    (i : CustodyIntent) : certApprovers L n pool dep i = certApprovers L' n pool dep i := by
  have hf : L.claim = L'.claim := funext hC
  rw [certApprovers.public_eqs, certApprovers.public_eqs]
  congr 1
  funext p
  rw [certVoted.public_eqs, certVoted.public_eqs, hf]

/-- Index of the key that party identifier `p` uses among `k + 1` keys: enrolled parties
    `p < k` have their own key; every identifier `p ≥ k` uses the key with index `k`. -/
def custIdx (k p : Nat) : Fin (k + 1) :=
  ⟨min p k, Nat.lt_succ_of_le (Nat.min_le_right p k)⟩

private theorem custIdx_val (k p : Nat) : (custIdx k p).val = min p k := by
  rfl

private theorem custIdx_eq_of_lt {k p q : Nat} (hp : p < k) (h : custIdx k q = custIdx k p) : q = p := by
  have h' := congrArg Fin.val h
  rw [custIdx_val, custIdx_val] at h'
  omega

/-- The key of party identifier `p` among the `k + 1` keys `keys`. -/
def custKey (k : Nat) (keys : Fin (k + 1) → Spec.Bytes) (p : Nat) : Spec.Bytes :=
  keys (custIdx k p)

section Reduction

variable {PK D Sig : Type} [DecidableEq D]

/-- The submission step of the coordinator over a tag layer, as a function of the verification
    bit `v`. -/
def submitWith (v : Bool) (c : CertCustodyState PK D Sig (Spec.Bytes × CustodyApproval))
    (x : Spec.Bytes × CustodyApproval) :
    CertCustodyState PK D Sig (Spec.Bytes × CustodyApproval) × Option (CustodyOutcome Sig) :=
  if v = true ∧ x.2.deploymentId = c.ledger.deploymentId then
    ({ c with
        pool := x :: c.pool
        advClaims := if x.2.party ∈ c.corruptParties then x.2 :: c.advClaims else c.advClaims
        forgeries :=
          if x.2.party ∉ c.corruptParties ∧ x.2 ∉ c.issued then x :: c.forgeries
          else c.forgeries }, some .approvalRecorded)
  else (c, none)

omit [DecidableEq D] in
private theorem submitWith_false (c : CertCustodyState PK D Sig (Spec.Bytes × CustodyApproval))
    (x : Spec.Bytes × CustodyApproval) : submitWith false c x = (c, none) :=
  ifN (fun h => Bool.false_ne_true h.1) _ _

omit [DecidableEq D] in
private theorem submitWith_frame (v : Bool) (c : CertCustodyState PK D Sig (Spec.Bytes × CustodyApproval))
    (x : Spec.Bytes × CustodyApproval) :
    (submitWith v c x).1.ledger = c.ledger ∧ (submitWith v c x).1.issued = c.issued ∧
      (submitWith v c x).1.corruptParties = c.corruptParties := by
  unfold submitWith
  by_cases hg : v = true ∧ x.2.deploymentId = c.ledger.deploymentId
  · rw [ifP hg]; exact ⟨rfl, rfl, rfl⟩
  · rw [ifN hg]; exact ⟨rfl, rfl, rfl⟩

variable (prf : Spec.Bytes → Spec.Bytes → Spec.Bytes) (enc : CustodyApproval → Spec.Bytes)
variable (S : CustodyDigestScheme D) (oracleSign : D → Sig)
variable (dep₀ : Nat) (pk₀ : PK) (quorum₀ : CustodyQuorumProfile) (budget : Nat) (k : Nat)

private theorem encTag_runStep_submit (key : Nat → Spec.Bytes)
    (c : CertCustodyState PK D Sig (Spec.Bytes × CustodyApproval))
    (x : Spec.Bytes × CustodyApproval) :
    (certCustodyMachine (encTagCertLayer prf enc key) S oracleSign dep₀ pk₀ quorum₀).runStep c
        (.submit x) =
      submitWith (decide (x.1 = prf (key x.2.party) (enc x.2))) c x := by
  rw [certRunStep_submit, certAdvClaims.public_eqs, certForgeries.public_eqs]
  rfl

/-- A signing step does not depend on the keys of the layer. -/
private theorem encTag_runStep_sign_congr (key key' : Nat → Spec.Bytes)
    (c : CertCustodyState PK D Sig (Spec.Bytes × CustodyApproval)) (dep : Nat)
    (i : CustodyIntent) (ab : Bool) :
    (certCustodyMachine (encTagCertLayer prf enc key) S oracleSign dep₀ pk₀ quorum₀).runStep c
        (.sign dep i ab) =
      (certCustodyMachine (encTagCertLayer prf enc key') S oracleSign dep₀ pk₀ quorum₀).runStep c
        (.sign dep i ab) := by
  rw [certCustodyMachine.public_eqs, certCustodyMachine.public_eqs]
  unfold Machine.runStep
  dsimp only
  rw [certCustodyStep.public_eq_4, certCustodyStep.public_eq_4,
    certApprovers_claim_congr (encTagCertLayer prf enc key) (encTagCertLayer prf enc key')
      (fun _ => rfl)]

private theorem certAdvResp_submit {Cert K : Type} (L : CustodyCertLayer Cert) (key : Nat → K)
    (x : Cert) (out : Option (CustodyOutcome Sig)) :
    certAdvResp L key (.submit x) out = (out, none, none) := by
  cases out <;> rfl

private theorem certAdvResp_sign {Cert K : Type} (L : CustodyCertLayer Cert) (key : Nat → K)
    (dep : Nat) (i : CustodyIntent) (ab : Bool) (out : Option (CustodyOutcome Sig)) :
    certAdvResp L key (.sign dep i ab) out = (out, none, none) := by
  cases out <;> rfl

/-- The logged forgeries that assert a permit of a party identifier using key `r`. -/
def rForg (r : Fin (k + 1)) (c : CertCustodyState PK D Sig (Spec.Bytes × CustodyApproval)) :
    List (Spec.Bytes × CustodyApproval) :=
  c.forgeries.filter (fun x => decide (custIdx k x.2.party = r))

omit [DecidableEq D] in
private theorem rForg_congr (r : Fin (k + 1))
    {c c' : CertCustodyState PK D Sig (Spec.Bytes × CustodyApproval)}
    (h : c'.forgeries = c.forgeries) : rForg k r c' = rForg k r c := by
  unfold rForg
  rw [h]

omit [DecidableEq D] in
private theorem submitWith_rForg (r : Fin (k + 1)) (v : Bool)
    (c : CertCustodyState PK D Sig (Spec.Bytes × CustodyApproval))
    (x : Spec.Bytes × CustodyApproval)
    (h : custIdx k x.2.party = r → x.2.party ∈ c.corruptParties ∨ x.2 ∈ c.issued) :
    rForg k r (submitWith v c x).1 = rForg k r c := by
  unfold submitWith
  by_cases hg : v = true ∧ x.2.deploymentId = c.ledger.deploymentId
  · rw [ifP hg]
    by_cases hc : x.2.party ∉ c.corruptParties ∧ x.2 ∉ c.issued
    · have hr : ¬ decide (custIdx k x.2.party = r) = true := fun hr =>
        (h (of_decide_eq_true hr)).elim (fun h1 => hc.1 h1) (fun h2 => hc.2 h2)
      show List.filter _ (if x.2.party ∉ c.corruptParties ∧ x.2 ∉ c.issued then x :: c.forgeries
        else c.forgeries) = _
      rw [ifP hc]
      exact List.filter_cons_of_neg
        (p := fun y : Spec.Bytes × CustodyApproval => decide (custIdx k y.2.party = r)) hr
    · show List.filter _ (if x.2.party ∉ c.corruptParties ∧ x.2 ∉ c.issued then x :: c.forgeries
        else c.forgeries) = _
      rw [ifN hc]
      rfl
  · rw [ifN hg]

/-! ## 4. The tag-forgery adversary of one key -/

/-- The default output of the reduction (no forgery found). -/
def redDefault : CustodyApproval × Spec.Bytes :=
  (⟨0, 0, ⟨0, 0, 0, 0, []⟩⟩, [])

/-- What the reduction does with one adversary query: stop with an output, ask its tag oracle
    for the tag of a permit, or answer directly. -/
inductive RedAct (PK D Sig : Type) where
  | stop (out : CustodyApproval × Spec.Bytes)
  | ask (a : CustodyApproval) (c : CertCustodyState PK D Sig (Spec.Bytes × CustodyApproval))
  | go (ρ : Option (CustodyOutcome Sig) × Option (Spec.Bytes × CustodyApproval) ×
      Option Spec.Bytes) (c : CertCustodyState PK D Sig (Spec.Bytes × CustodyApproval)) (j : Nat)

/-- One simulated step of the reduction for key index `r`. It holds the keys `keys'` of the
    other indices (its value at `r` is not read on any path that is compared with the real
    world), the simulated machine state `c`, the tags `tags` it received from its oracle, and the
    number `j` of unverifiable submissions it will still treat as refused.

    * `.approve` by a party using key `r`: asks the tag oracle.
    * `.corrupt` of a party using key `r`: stops.
    * `.submit x` for a party using key `r`: a permit that party issued is verified against the
      received tag; any other one cannot be verified without the key: the `j`-th such submission
      is output as the forgery, earlier ones are answered as refused.
    * everything else: computed with `keys'`. -/
def redAct (r : Fin (k + 1)) (keys' : Fin (k + 1) → Spec.Bytes) :
    CertCustodyInput (Spec.Bytes × CustodyApproval) → Nat →
      CertCustodyState PK D Sig (Spec.Bytes × CustodyApproval) →
      List (CustodyApproval × Spec.Bytes) → RedAct PK D Sig
  | .approve p dep i, j, c, _ =>
    if p < c.ledger.quorum.numParties ∧ p ∉ c.corruptParties ∧ dep = c.ledger.deploymentId then
      if custIdx k p = r then
        .ask ⟨p, dep, i⟩ { c with issued := CustodyApproval.mk p dep i :: c.issued }
      else
        .go (some .approvalRecorded,
            some (prf (keys' (custIdx k p)) (enc ⟨p, dep, i⟩), ⟨p, dep, i⟩), none)
          { c with issued := CustodyApproval.mk p dep i :: c.issued } j
    else .go (none, none, none) c j
  | .corrupt p, j, c, _ =>
    if p < c.ledger.quorum.numParties ∧ p ∉ c.corruptParties ∧
        c.corruptParties.length + 1 < c.ledger.quorum.threshold then
      if custIdx k p = r then .stop redDefault
      else
        .go (some (.corrupted (custodyRevealed c.issued p)), none, some (keys' (custIdx k p)))
          { c with corruptParties := p :: c.corruptParties } j
    else .go (none, none, none) c j
  | .submit x, j, c, tags =>
    if custIdx k x.2.party = r then
      if x.2 ∈ c.issued then
        .go ((submitWith (decide ((x.2, x.1) ∈ tags)) c x).2, none, none)
          (submitWith (decide ((x.2, x.1) ∈ tags)) c x).1 j
      else
        match j with
        | 0 => .stop (x.2, x.1)
        | j' + 1 => .go (none, none, none) c j'
    else
      .go ((submitWith (decide (x.1 = prf (keys' (custIdx k x.2.party)) (enc x.2))) c x).2,
          none, none)
        (submitWith (decide (x.1 = prf (keys' (custIdx k x.2.party)) (enc x.2))) c x).1 j
  | .sign dep i ab, j, c, _ =>
    .go (((certCustodyMachine (encTagCertLayer prf enc (custKey k keys')) S
            oracleSign dep₀ pk₀ quorum₀).runStep c (.sign dep i ab)).2, none, none)
      ((certCustodyMachine (encTagCertLayer prf enc (custKey k keys')) S
            oracleSign dep₀ pk₀ quorum₀).runStep c (.sign dep i ab)).1 j

/-- **The tag-forgery adversary for key index `r`.** It runs the adaptive adversary `A` of the
    certificate world, answering each query by `redAct`, with the step budget of the world. -/
def redCode {R : Type} (r : Fin (k + 1)) (keys' : Fin (k + 1) → Spec.Bytes) :
    Code (certAdvIface (Spec.Bytes × CustodyApproval) Spec.Bytes Sig) R → Nat →
      CertCustodyState PK D Sig (Spec.Bytes × CustodyApproval) → Nat →
      List (CustodyApproval × Spec.Bytes) →
      Code (tagIface CustodyApproval) (CustodyApproval × Spec.Bytes)
  | .ret _, _, _, _, _ => .ret redDefault
  | .call inp kont, j, c, n, tags =>
    if n < budget then
      match redAct prf enc S oracleSign dep₀ pk₀ quorum₀ k r keys' inp j c tags with
      | .stop out => .ret out
      | .ask a c' =>
        .call (E := tagIface CustodyApproval) a (fun t =>
          redCode r keys' (kont (some .approvalRecorded, some (t, a), none)) j c' (n + 1)
            ((a, t) :: tags))
      | .go ρ c' j' => redCode r keys' (kont ρ) j' c' (n + 1) tags
    else redCode r keys' (kont (none, none, none)) j c n tags

local notation "RA" => redAct prf enc S oracleSign dep₀ pk₀ quorum₀ k
local notation "RC" => redCode prf enc S oracleSign dep₀ pk₀ quorum₀ budget k

private theorem redCode_call_exhausted {R : Type} (r : Fin (k + 1)) (keys' : Fin (k + 1) → Spec.Bytes)
    (inp : CertCustodyInput (Spec.Bytes × CustodyApproval))
    (kont : Option (CustodyOutcome Sig) × Option (Spec.Bytes × CustodyApproval) ×
      Option Spec.Bytes → Code (certAdvIface (Spec.Bytes × CustodyApproval) Spec.Bytes Sig) R)
    (j : Nat) (c : CertCustodyState PK D Sig (Spec.Bytes × CustodyApproval)) (n : Nat)
    (tags : List (CustodyApproval × Spec.Bytes)) (hn : ¬ n < budget) :
    RC r keys' (Code.call (E := certAdvIface (Spec.Bytes × CustodyApproval) Spec.Bytes Sig)
        inp kont) j c n tags =
      RC r keys' (kont (none, none, none)) j c n tags := by
  rw [redCode, ifN hn]

private theorem redCode_call_go {R : Type} (r : Fin (k + 1)) (keys' : Fin (k + 1) → Spec.Bytes)
    (inp : CertCustodyInput (Spec.Bytes × CustodyApproval))
    (kont : Option (CustodyOutcome Sig) × Option (Spec.Bytes × CustodyApproval) ×
      Option Spec.Bytes → Code (certAdvIface (Spec.Bytes × CustodyApproval) Spec.Bytes Sig) R)
    (j : Nat) (c : CertCustodyState PK D Sig (Spec.Bytes × CustodyApproval)) (n : Nat)
    (tags : List (CustodyApproval × Spec.Bytes)) (hn : n < budget)
    {ρ : Option (CustodyOutcome Sig) × Option (Spec.Bytes × CustodyApproval) × Option Spec.Bytes}
    {c' : CertCustodyState PK D Sig (Spec.Bytes × CustodyApproval)} {j' : Nat}
    (h : RA r keys' inp j c tags = .go ρ c' j') :
    RC r keys' (Code.call (E := certAdvIface (Spec.Bytes × CustodyApproval) Spec.Bytes Sig)
        inp kont) j c n tags =
      RC r keys' (kont ρ) j' c' (n + 1) tags := by
  rw [redCode, ifP hn, h]

private theorem redCode_call_stop {R : Type} (r : Fin (k + 1)) (keys' : Fin (k + 1) → Spec.Bytes)
    (inp : CertCustodyInput (Spec.Bytes × CustodyApproval))
    (kont : Option (CustodyOutcome Sig) × Option (Spec.Bytes × CustodyApproval) ×
      Option Spec.Bytes → Code (certAdvIface (Spec.Bytes × CustodyApproval) Spec.Bytes Sig) R)
    (j : Nat) (c : CertCustodyState PK D Sig (Spec.Bytes × CustodyApproval)) (n : Nat)
    (tags : List (CustodyApproval × Spec.Bytes)) (hn : n < budget)
    {out : CustodyApproval × Spec.Bytes}
    (h : RA r keys' inp j c tags = .stop out) :
    RC r keys' (Code.call (E := certAdvIface (Spec.Bytes × CustodyApproval) Spec.Bytes Sig)
        inp kont) j c n tags = Code.ret out := by
  rw [redCode, ifP hn, h]

private theorem redCode_call_ask {R : Type} (r : Fin (k + 1)) (keys' : Fin (k + 1) → Spec.Bytes)
    (inp : CertCustodyInput (Spec.Bytes × CustodyApproval))
    (kont : Option (CustodyOutcome Sig) × Option (Spec.Bytes × CustodyApproval) ×
      Option Spec.Bytes → Code (certAdvIface (Spec.Bytes × CustodyApproval) Spec.Bytes Sig) R)
    (j : Nat) (c : CertCustodyState PK D Sig (Spec.Bytes × CustodyApproval)) (n : Nat)
    (tags : List (CustodyApproval × Spec.Bytes)) (hn : n < budget)
    {a : CustodyApproval} {c' : CertCustodyState PK D Sig (Spec.Bytes × CustodyApproval)}
    (h : RA r keys' inp j c tags = .ask a c') :
    RC r keys' (Code.call (E := certAdvIface (Spec.Bytes × CustodyApproval) Spec.Bytes Sig)
        inp kont) j c n tags =
      Code.call (E := tagIface CustodyApproval) a (fun t =>
        RC r keys' (kont (some .approvalRecorded, some (t, a), none)) j c' (n + 1)
          ((a, t) :: tags)) := by
  rw [redCode, ifP hn, h]

/-! ## 5. The reduction's simulation of the certificate world -/

local notation "RO" keys =>
  certWorldOracle (encTagCertLayer prf enc (custKey k keys)) (custKey k keys) S oracleSign
    dep₀ pk₀ quorum₀ budget

/-- The reduction asks its tag oracle at most `budget - n` times from step counter `n`. -/
theorem redCode_within {R : Type} (r : Fin (k + 1)) (keys' : Fin (k + 1) → Spec.Bytes) :
    ∀ (A : Code (certAdvIface (Spec.Bytes × CustodyApproval) Spec.Bytes Sig) R) (j : Nat)
      (c : CertCustodyState PK D Sig (Spec.Bytes × CustodyApproval)) (n : Nat)
      (tags : List (CustodyApproval × Spec.Bytes)),
      Within (budget - n) (RC r keys' A j c n tags)
  | .ret _, _, _, _, _ => by
    rw [redCode]
    exact .ret _ _
  | .call inp kont, j, c, n, tags => by
    by_cases hn : n < budget
    · cases hA : RA r keys' inp j c tags with
      | stop out =>
        rw [redCode_call_stop prf enc S oracleSign dep₀ pk₀ quorum₀ budget k r keys' inp kont j c n
          tags hn hA]
        exact .ret _ _
      | ask a c' =>
        rw [redCode_call_ask prf enc S oracleSign dep₀ pk₀ quorum₀ budget k r keys' inp kont j c n
          tags hn hA]
        have hEq : budget - n = (budget - (n + 1)) + 1 := by omega
        rw [hEq]
        exact .call (E := tagIface CustodyApproval) _ _
          (fun t => redCode_within r keys' (kont _) j c' (n + 1) _)
      | go ρ c' j' =>
        rw [redCode_call_go prf enc S oracleSign dep₀ pk₀ quorum₀ budget k r keys' inp kont j c n
          tags hn hA]
        exact Within.mono (by omega) (redCode_within r keys' (kont ρ) j' c' (n + 1) tags)
    · rw [redCode_call_exhausted prf enc S oracleSign dep₀ pk₀ quorum₀ budget k r keys' inp kont j
        c n tags hn]
      exact redCode_within r keys' (kont _) j c n tags

/-- Once an enrolled party `p < k` is corrupted, no step logs a forgery for its key. -/
private theorem runStep_frozen (keys : Fin (k + 1) → Spec.Bytes) (p : Nat) (hp : p < k)
    (c : CertCustodyState PK D Sig (Spec.Bytes × CustodyApproval))
    (inp : CertCustodyInput (Spec.Bytes × CustodyApproval))
    (h : p ∈ c.corruptParties ∧ rForg k (custIdx k p) c = []) :
    p ∈ ((certCustodyMachine (encTagCertLayer prf enc (custKey k keys)) S oracleSign dep₀ pk₀
        quorum₀).runStep c inp).1.corruptParties ∧
      rForg k (custIdx k p) ((certCustodyMachine (encTagCertLayer prf enc (custKey k keys)) S
        oracleSign dep₀ pk₀ quorum₀).runStep c inp).1 = [] := by
  cases inp with
  | approve q dep i =>
    rw [certRunStep_approve]
    by_cases hg : q < c.ledger.quorum.numParties ∧ q ∉ c.corruptParties ∧
        dep = c.ledger.deploymentId
    · rw [ifP hg]; exact h
    · rw [ifN hg]; exact h
  | submit x =>
    rw [encTag_runStep_submit]
    refine ⟨?_, ?_⟩
    · rw [(submitWith_frame _ c x).2.2]; exact h.1
    · rw [submitWith_rForg k _ _ c x (fun hx => .inl (by
        rw [custIdx_eq_of_lt hp hx]; exact h.1))]
      exact h.2
  | corrupt q =>
    rw [certRunStep_corrupt]
    by_cases hg : q < c.ledger.quorum.numParties ∧ q ∉ c.corruptParties ∧
        c.corruptParties.length + 1 < c.ledger.quorum.threshold
    · rw [ifP hg]; exact ⟨List.mem_cons_of_mem _ h.1, h.2⟩
    · rw [ifN hg]; exact h
  | sign dep i ab =>
    have fr := certRunStep_sign_frame (encTagCertLayer prf enc (custKey k keys)) S oracleSign
      dep₀ pk₀ quorum₀ c dep i ab
    exact ⟨by rw [fr.1]; exact h.1, by rw [rForg_congr k _ fr.2.2.1]; exact h.2⟩

private theorem play_frozen {R : Type} (keys : Fin (k + 1) → Spec.Bytes) (p : Nat) (hp : p < k)
    (A : Code (certAdvIface (Spec.Bytes × CustodyApproval) Spec.Bytes Sig) R)
    (c : CertCustodyState PK D Sig (Spec.Bytes × CustodyApproval))
    (tr : List (CertCustodyInput (Spec.Bytes × CustodyApproval)))
    (h : p ∈ c.corruptParties ∧ rForg k (custIdx k p) c = []) :
    rForg k (custIdx k p) (Code.play (RO keys) A (c, tr)).2.1 = [] :=
  (Code.play_invariant (RO keys)
    (fun st => p ∈ st.1.corruptParties ∧ rForg k (custIdx k p) st.1 = [])
    (fun st inp h => by
      obtain ⟨c, tr⟩ := st
      by_cases hb : tr.length < budget
      · rw [certWorldOracle_pos _ _ S oracleSign dep₀ pk₀ quorum₀ budget c tr hb]
        exact runStep_frozen prf enc S oracleSign dep₀ pk₀ quorum₀ k keys p hp c inp h
      · rw [certWorldOracle_neg _ _ S oracleSign dep₀ pk₀ quorum₀ budget c tr hb]
        exact h)
    A (c, tr) h).2

/-- Invariant of the simulation for key index `r` with key `kr`: no forgery for `r` is logged,
    every enrolled party has its own key, every permit issued under key `r` has its tag in
    `tags`, every recorded tag is correct, and the tag oracle's log lists issued permits. -/
structure RedInv (r : Fin (k + 1)) (kr : Spec.Bytes)
    (c : CertCustodyState PK D Sig (Spec.Bytes × CustodyApproval))
    (tags : List (CustodyApproval × Spec.Bytes)) (log : List CustodyApproval) (n : Nat) :
    Prop where
  noForg : rForg k r c = []
  enrolled : c.ledger.quorum.numParties ≤ k
  tagged : ∀ a ∈ c.issued, custIdx k a.party = r → (a, prf kr (enc a)) ∈ tags
  tagsOk : ∀ (a : CustodyApproval) (t : Spec.Bytes), (a, t) ∈ tags → t = prf kr (enc a)
  logIssued : ∀ a ∈ log, a ∈ c.issued
  logLen : log.length ≤ n

/-- The reduction's output is a correct tag under `kr` on a permit its oracle was not asked. -/
def redWin (kr : Spec.Bytes) (res : (CustodyApproval × Spec.Bytes) × List CustodyApproval) :
    Prop :=
  res.1.1 ∉ res.2 ∧ res.1.2 = prf kr (enc res.1.1)

omit [DecidableEq D] in
private theorem RedInv.submit {r : Fin (k + 1)} {kr : Spec.Bytes}
    {c : CertCustodyState PK D Sig (Spec.Bytes × CustodyApproval)}
    {tags : List (CustodyApproval × Spec.Bytes)} {log : List CustodyApproval} {n : Nat}
    (hI : RedInv prf enc k r kr c tags log n) (v : Bool) (x : Spec.Bytes × CustodyApproval)
    (h : custIdx k x.2.party = r → x.2.party ∈ c.corruptParties ∨ x.2 ∈ c.issued) :
    RedInv prf enc k r kr (submitWith v c x).1 tags log (n + 1) where
  noForg := by rw [submitWith_rForg k r v c x h]; exact hI.noForg
  enrolled := by rw [(submitWith_frame v c x).1]; exact hI.enrolled
  tagged := by rw [(submitWith_frame v c x).2.1]; exact hI.tagged
  tagsOk := hI.tagsOk
  logIssued := by rw [(submitWith_frame v c x).2.1]; exact hI.logIssued
  logLen := Nat.le_succ_of_le hI.logLen

/-- A step the reduction answers without its oracle and without stopping. -/
private theorem red_go {R : Type} (r : Fin (k + 1)) (keys keys' : Fin (k + 1) → Spec.Bytes)
    (inp : CertCustodyInput (Spec.Bytes × CustodyApproval))
    (kont : Option (CustodyOutcome Sig) × Option (Spec.Bytes × CustodyApproval) ×
      Option Spec.Bytes → Code (certAdvIface (Spec.Bytes × CustodyApproval) Spec.Bytes Sig) R)
    (c c' : CertCustodyState PK D Sig (Spec.Bytes × CustodyApproval))
    (tr : List (CertCustodyInput (Spec.Bytes × CustodyApproval)))
    (tags : List (CustodyApproval × Spec.Bytes)) (log : List CustodyApproval)
    (ρ : Option (CustodyOutcome Sig) × Option (Spec.Bytes × CustodyApproval) × Option Spec.Bytes)
    (hn : tr.length < budget)
    (hO : (RO keys) (c, tr) inp = (ρ, (c', tr ++ [inp])))
    (hRA : ∀ j, RA r keys' inp j c tags = .go ρ c' j)
    (ih : rForg k r (Code.play (RO keys) (kont ρ) (c', tr ++ [inp])).2.1 ≠ [] →
      ∃ j, j < budget - (tr.length + 1) ∧ redWin prf enc (keys r)
        (Code.play (tagOracle enc (prf (keys r)) budget)
          (RC r keys' (kont ρ) j c' (tr.length + 1) tags) log))
    (hF : rForg k r (Code.play (RO keys)
      (Code.call (E := certAdvIface (Spec.Bytes × CustodyApproval) Spec.Bytes Sig) inp kont)
      (c, tr)).2.1 ≠ []) :
    ∃ j, j < budget - tr.length ∧ redWin prf enc (keys r)
      (Code.play (tagOracle enc (prf (keys r)) budget)
        (RC r keys' (Code.call (E := certAdvIface (Spec.Bytes × CustodyApproval) Spec.Bytes Sig)
          inp kont) j c tr.length tags) log) := by
  rw [Code.play_call, hO] at hF
  obtain ⟨j, hj, hW⟩ := ih hF
  refine ⟨j, by omega, ?_⟩
  rw [redCode_call_go prf enc S oracleSign dep₀ pk₀ quorum₀ budget k r keys' inp kont j c
    tr.length tags hn (hRA j)]
  exact hW

/-- One query of the simulation, given the simulation statement for every continuation. -/
private theorem red_sim_step {R : Type} (r : Fin (k + 1)) (keys keys' : Fin (k + 1) → Spec.Bytes)
    (hK : ∀ i, i ≠ r → keys' i = keys i)
    (inp : CertCustodyInput (Spec.Bytes × CustodyApproval))
    (kont : Option (CustodyOutcome Sig) × Option (Spec.Bytes × CustodyApproval) ×
      Option Spec.Bytes → Code (certAdvIface (Spec.Bytes × CustodyApproval) Spec.Bytes Sig) R)
    (ih : ∀ (ρ : Option (CustodyOutcome Sig) × Option (Spec.Bytes × CustodyApproval) ×
        Option Spec.Bytes)
      (c : CertCustodyState PK D Sig (Spec.Bytes × CustodyApproval))
      (tr : List (CertCustodyInput (Spec.Bytes × CustodyApproval)))
      (n : Nat) (_ : tr.length = n)
      (tags : List (CustodyApproval × Spec.Bytes)) (log : List CustodyApproval),
      RedInv prf enc k r (keys r) c tags log n →
      rForg k r (Code.play (RO keys) (kont ρ) (c, tr)).2.1 ≠ [] →
      ∃ j, j < budget - n ∧ redWin prf enc (keys r)
        (Code.play (tagOracle enc (prf (keys r)) budget) (RC r keys' (kont ρ) j c n tags) log))
    (c : CertCustodyState PK D Sig (Spec.Bytes × CustodyApproval))
    (tr : List (CertCustodyInput (Spec.Bytes × CustodyApproval)))
    (n : Nat) (hlen : tr.length = n)
    (tags : List (CustodyApproval × Spec.Bytes)) (log : List CustodyApproval)
    (hI : RedInv prf enc k r (keys r) c tags log n)
    (hF : rForg k r (Code.play (RO keys)
      (Code.call (E := certAdvIface (Spec.Bytes × CustodyApproval) Spec.Bytes Sig) inp kont)
      (c, tr)).2.1 ≠ []) :
    ∃ j, j < budget - n ∧ redWin prf enc (keys r)
      (Code.play (tagOracle enc (prf (keys r)) budget)
        (RC r keys' (Code.call (E := certAdvIface (Spec.Bytes × CustodyApproval) Spec.Bytes Sig)
          inp kont) j c n tags) log) := by
  subst hlen
  by_cases hn : tr.length < budget
  · have hPos := certWorldOracle_pos (encTagCertLayer prf enc (custKey k keys))
      (custKey k keys) S oracleSign dep₀ pk₀ quorum₀ budget c tr hn
    have hlen1 : ∀ i : CertCustodyInput (Spec.Bytes × CustodyApproval),
        (tr ++ [i]).length = tr.length + 1 := fun i => by
      rw [List.length_append]; rfl
    cases inp with
    | approve p dep i =>
      by_cases hg : p < c.ledger.quorum.numParties ∧ p ∉ c.corruptParties ∧
          dep = c.ledger.deploymentId
      · by_cases hr : custIdx k p = r
        · have hO : (RO keys) (c, tr) (.approve p dep i) =
              ((some .approvalRecorded, some (prf (keys r) (enc ⟨p, dep, i⟩), ⟨p, dep, i⟩),
                  none),
                ({ c with issued := CustodyApproval.mk p dep i :: c.issued },
                  tr ++ [.approve p dep i])) := by
            rw [hPos, certRunStep_approve, ifP hg, ← hr]
            rfl
          have hA : ∀ j, RA r keys' (.approve p dep i) j c tags =
              .ask ⟨p, dep, i⟩ { c with issued := CustodyApproval.mk p dep i :: c.issued } :=
            fun j => by
              show (if _ then (if _ then _ else _) else _) = _
              rw [ifP hg, ifP hr]
          rw [Code.play_call, hO] at hF
          have hlog : log.length < budget := Nat.lt_of_le_of_lt hI.logLen hn
          obtain ⟨j, hj, hW⟩ := ih _
            { c with issued := CustodyApproval.mk p dep i :: c.issued } (tr ++ [.approve p dep i])
            (tr.length + 1) (hlen1 _)
            ((⟨p, dep, i⟩, prf (keys r) (enc ⟨p, dep, i⟩)) :: tags) (log ++ [⟨p, dep, i⟩])
            { noForg := hI.noForg
              enrolled := hI.enrolled
              tagged := fun a ha _ => by
                rcases List.mem_cons.mp ha with hEq | hT
                · rw [hEq]; exact List.mem_cons_self
                · exact List.mem_cons_of_mem _ (hI.tagged a hT ‹_›)
              tagsOk := fun a t hat => by
                rcases List.mem_cons.mp hat with hEq | hT
                · rw [(Prod.mk.inj hEq).1, (Prod.mk.inj hEq).2]
                · exact hI.tagsOk a t hT
              logIssued := fun a ha => by
                rcases List.mem_append.mp ha with h1 | h1
                · exact List.mem_cons_of_mem _ (hI.logIssued a h1)
                · rw [List.mem_singleton.mp h1]; exact List.mem_cons_self
              logLen := by
                rw [List.length_append]
                exact Nat.succ_le_succ hI.logLen } hF
          refine ⟨j, by omega, ?_⟩
          rw [redCode_call_ask prf enc S oracleSign dep₀ pk₀ quorum₀ budget k r keys' _ kont j c
            tr.length tags hn (hA j), Code.play_call, tagOracle_pos enc _ budget hlog]
          exact hW
        · refine red_go prf enc S oracleSign dep₀ pk₀ quorum₀ budget k r keys keys' _ kont c
            { c with issued := CustodyApproval.mk p dep i :: c.issued } tr tags log
            (some .approvalRecorded,
              some (prf (keys' (custIdx k p)) (enc ⟨p, dep, i⟩), ⟨p, dep, i⟩), none) hn
            (by rw [hPos, certRunStep_approve, ifP hg, hK _ hr]; rfl)
            (fun j => by
              show (if _ then (if _ then _ else _) else _) = _
              rw [ifP hg, ifN hr])
            (ih _
            { c with issued := CustodyApproval.mk p dep i :: c.issued } (tr ++ [.approve p dep i]) (tr.length + 1)
              (hlen1 _) tags log
              { noForg := hI.noForg
                enrolled := hI.enrolled
                tagged := fun a ha har => by
                  rcases List.mem_cons.mp ha with hEq | hT
                  · rw [hEq] at har; exact absurd har hr
                  · exact hI.tagged a hT har
                tagsOk := hI.tagsOk
                logIssued := fun a ha => List.mem_cons_of_mem _ (hI.logIssued a ha)
                logLen := Nat.le_succ_of_le hI.logLen }) hF
      · refine red_go prf enc S oracleSign dep₀ pk₀ quorum₀ budget k r keys keys' _ kont c c tr
          tags log (none, none, none) hn
          (by rw [hPos, certRunStep_approve, ifN hg]; rfl)
          (fun j => by
            show (if _ then _ else _) = _
            rw [ifN hg])
          (ih _ c (tr ++ [.approve p dep i]) (tr.length + 1)
            (hlen1 _) tags log { hI with logLen := Nat.le_succ_of_le hI.logLen }) hF
    | corrupt p =>
      by_cases hg : p < c.ledger.quorum.numParties ∧ p ∉ c.corruptParties ∧
          c.corruptParties.length + 1 < c.ledger.quorum.threshold
      · by_cases hr : custIdx k p = r
        · have hO : (RO keys) (c, tr) (.corrupt p) =
              ((some (.corrupted (custodyRevealed c.issued p)), none, some (custKey k keys p)),
                ({ c with corruptParties := p :: c.corruptParties }, tr ++ [.corrupt p])) := by
            rw [hPos, certRunStep_corrupt, ifP hg]
            rfl
          rw [Code.play_call, hO] at hF
          have h0 := hI.noForg
          rw [← hr] at h0 hF
          exact absurd (play_frozen prf enc S oracleSign dep₀ pk₀ quorum₀ budget k keys p
            (Nat.lt_of_lt_of_le hg.1 hI.enrolled) (kont _)
            { c with corruptParties := p :: c.corruptParties } _
            ⟨List.mem_cons_self, h0⟩) hF
        · refine red_go prf enc S oracleSign dep₀ pk₀ quorum₀ budget k r keys keys' _ kont c
            { c with corruptParties := p :: c.corruptParties } tr tags log
            (some (.corrupted (custodyRevealed c.issued p)), none,
              some (keys' (custIdx k p))) hn
            (by rw [hPos, certRunStep_corrupt, ifP hg, hK _ hr]; rfl)
            (fun j => by
              show (if _ then (if _ then _ else _) else _) = _
              rw [ifP hg, ifN hr])
            (ih _
            { c with corruptParties := p :: c.corruptParties } (tr ++ [.corrupt p]) (tr.length + 1)
              (hlen1 _) tags log
              { noForg := hI.noForg
                enrolled := hI.enrolled
                tagged := hI.tagged
                tagsOk := hI.tagsOk
                logIssued := hI.logIssued
                logLen := Nat.le_succ_of_le hI.logLen }) hF
      · refine red_go prf enc S oracleSign dep₀ pk₀ quorum₀ budget k r keys keys' _ kont c c tr
          tags log (none, none, none) hn
          (by rw [hPos, certRunStep_corrupt, ifN hg]; rfl)
          (fun j => by
            show (if _ then _ else _) = _
            rw [ifN hg])
          (ih _ c (tr ++ [.corrupt p]) (tr.length + 1)
            (hlen1 _) tags log { hI with logLen := Nat.le_succ_of_le hI.logLen }) hF
    | submit x =>
      have hStep := encTag_runStep_submit prf enc S oracleSign dep₀ pk₀ quorum₀
        (custKey k keys) c x
      by_cases hr : custIdx k x.2.party = r
      · have hkey : custKey k keys x.2.party = keys r := congrArg keys hr
        by_cases hi : x.2 ∈ c.issued
        · have hdec : decide (x.1 = prf (custKey k keys x.2.party) (enc x.2)) =
              decide ((x.2, x.1) ∈ tags) := by
            rw [hkey]
            exact decide_eq_decide.mpr
              ⟨fun h => by rw [h]; exact hI.tagged x.2 hi hr, fun h => hI.tagsOk x.2 x.1 h⟩
          refine red_go prf enc S oracleSign dep₀ pk₀ quorum₀ budget k r keys keys' _ kont c
            (submitWith (decide ((x.2, x.1) ∈ tags)) c x).1 tr tags log
            ((submitWith (decide ((x.2, x.1) ∈ tags)) c x).2, none, none) hn
            (by rw [hPos, hStep, certAdvResp_submit, hdec])
            (fun j => by
              show (if _ then (if _ then _ else _) else _) = _
              rw [ifP hr, ifP hi])
            (ih _ _ (tr ++ [.submit x]) (tr.length + 1)
              (hlen1 _) tags log (hI.submit prf enc k _ x (fun _ => .inr hi))) hF
        · by_cases ha : decide (x.1 = prf (custKey k keys x.2.party) (enc x.2)) = true ∧
              x.2.deploymentId = c.ledger.deploymentId
          · have h0 : RA r keys' (.submit x) 0 c tags = .stop (x.2, x.1) := by
              show (if _ then (if _ then _ else _) else _) = _
              rw [ifP hr, ifN hi]
            refine ⟨0, by omega, ?_⟩
            rw [redCode_call_stop prf enc S oracleSign dep₀ pk₀ quorum₀ budget k r keys' _ kont
              0 c tr.length tags hn h0, Code.play_ret]
            have hv := of_decide_eq_true ha.1
            rw [hkey] at hv
            exact ⟨fun hm => hi (hI.logIssued _ hm), hv⟩
          · have hs : submitWith (decide (x.1 = prf (custKey k keys x.2.party) (enc x.2))) c x =
                (c, none) := ifN ha _ _
            have hO : (RO keys) (c, tr) (.submit x) =
                ((none, none, none), (c, tr ++ [.submit x])) := by
              rw [hPos, hStep, hs]
              rfl
            rw [Code.play_call, hO] at hF
            obtain ⟨j, hj, hW⟩ := ih _ c (tr ++ [.submit x])
              (tr.length + 1) (hlen1 _) tags log
              { hI with logLen := Nat.le_succ_of_le hI.logLen } hF
            have hsucc : RA r keys' (.submit x) (j + 1) c tags = .go (none, none, none) c j := by
              show (if _ then (if _ then _ else _) else _) = _
              rw [ifP hr, ifN hi]
            refine ⟨j + 1, by omega, ?_⟩
            rw [redCode_call_go prf enc S oracleSign dep₀ pk₀ quorum₀ budget k r keys' _ kont
              (j + 1) c tr.length tags hn hsucc]
            exact hW
      · have hkey : custKey k keys x.2.party = keys' (custIdx k x.2.party) := (hK _ hr).symm
        refine red_go prf enc S oracleSign dep₀ pk₀ quorum₀ budget k r keys keys' _ kont c
          (submitWith (decide (x.1 = prf (keys' (custIdx k x.2.party)) (enc x.2))) c x).1 tr
          tags log
          ((submitWith (decide (x.1 = prf (keys' (custIdx k x.2.party)) (enc x.2))) c x).2,
            none, none) hn
          (by rw [hPos, hStep, certAdvResp_submit, hkey])
          (fun j => by
            show (if _ then _ else _) = _
            rw [ifN hr])
          (ih _ _ (tr ++ [.submit x]) (tr.length + 1)
            (hlen1 _) tags log (hI.submit prf enc k _ x (fun h => absurd h hr))) hF
    | sign dep i ab =>
      have fr := certRunStep_sign_frame (encTagCertLayer prf enc (custKey k keys')) S
        oracleSign dep₀ pk₀ quorum₀ c dep i ab
      refine red_go prf enc S oracleSign dep₀ pk₀ quorum₀ budget k r keys keys' _ kont c
        ((certCustodyMachine (encTagCertLayer prf enc (custKey k keys')) S oracleSign dep₀ pk₀
          quorum₀).runStep c (.sign dep i ab)).1 tr tags log
        (((certCustodyMachine (encTagCertLayer prf enc (custKey k keys')) S oracleSign dep₀ pk₀
          quorum₀).runStep c (.sign dep i ab)).2, none, none) hn
        (by rw [hPos, certAdvResp_sign, encTag_runStep_sign_congr prf enc S oracleSign dep₀ pk₀
          quorum₀ (custKey k keys) (custKey k keys')])
        (fun j => rfl)
        (ih _ _ (tr ++ [.sign dep i ab]) (tr.length + 1)
          (hlen1 _) tags log
          { noForg := by rw [rForg_congr k r fr.2.2.1]; exact hI.noForg
            enrolled := by rw [fr.2.2.2]; exact hI.enrolled
            tagged := by rw [fr.2.1]; exact hI.tagged
            tagsOk := hI.tagsOk
            logIssued := by rw [fr.2.1]; exact hI.logIssued
            logLen := Nat.le_succ_of_le hI.logLen }) hF
  · have hO : (RO keys) (c, tr) inp = ((none, none, none), (c, tr)) :=
      certWorldOracle_neg _ _ S oracleSign dep₀ pk₀ quorum₀ budget c tr hn inp
    rw [Code.play_call, hO] at hF
    obtain ⟨j, hj, hW⟩ := ih _ c tr tr.length rfl tags log hI hF
    exact ⟨j, hj, by
      rw [redCode_call_exhausted prf enc S oracleSign dep₀ pk₀ quorum₀ budget k r keys' inp kont
        j c tr.length tags hn]
      exact hW⟩

/-- **Simulation.** Run the adaptive adversary `A` in the certificate world with keys `keys`
    from a state satisfying `RedInv`. If the run logs a forgery for key index `r`, then for some
    guess `j` below the remaining budget the reduction `redCode r keys' A j`, run against the tag
    oracle of `prf (keys r)` and holding only keys `keys'` that agree with `keys` away from `r`,
    outputs a correct tag on a permit its oracle was not asked. Up to that output the reduction
    gives `A` the answers of the certificate world. -/
theorem red_sim {R : Type} (r : Fin (k + 1)) (keys keys' : Fin (k + 1) → Spec.Bytes)
    (hK : ∀ i, i ≠ r → keys' i = keys i) :
    ∀ (A : Code (certAdvIface (Spec.Bytes × CustodyApproval) Spec.Bytes Sig) R)
      (c : CertCustodyState PK D Sig (Spec.Bytes × CustodyApproval))
      (tr : List (CertCustodyInput (Spec.Bytes × CustodyApproval)))
      (n : Nat) (_ : tr.length = n)
      (tags : List (CustodyApproval × Spec.Bytes)) (log : List CustodyApproval),
      RedInv prf enc k r (keys r) c tags log n →
      rForg k r (Code.play (RO keys) A (c, tr)).2.1 ≠ [] →
      ∃ j, j < budget - n ∧ redWin prf enc (keys r)
        (Code.play (tagOracle enc (prf (keys r)) budget) (RC r keys' A j c n tags) log)
  | .ret _, c, tr, _, _, tags, log, hI, hF => by
    rw [Code.play_ret] at hF
    exact absurd hI.noForg hF
  | .call inp kont, c, tr, n, hlen, tags, log, hI, hF =>
    red_sim_step prf enc S oracleSign dep₀ pk₀ quorum₀ budget k r keys keys' hK inp kont
      (fun ρ c' tr' n' h' tags' log' =>
        red_sim r keys keys' hK (kont ρ) c' tr' n' h' tags' log') c tr n hlen tags log hI hF

end Reduction

/-! ## 6. The game and the bound -/

/-- Shifting a single answer preserves the full keyed-function challenger support. -/
theorem prfSample_shiftClosed (keyLen inLen outLen : Nat) :
    SupportShiftClosed inLen outLen (PrfSampleOk keyLen inLen outLen) :=
  prfSampleOk_shiftClosed keyLen inLen outLen

section Game

variable {PK D Sig : Type} [DecidableEq D]

/-- **The tag-forgery adversary** for key index `r` and guess `j`, built from an adaptive
    adversary `A` of the certificate world with `quorum₀.numParties + 1` keys: `redCode` from the
    initial state. `keys'` is read at indices other than `r` only where it matters. -/
def certTagForger {R : Type} (prf : Spec.Bytes → Spec.Bytes → Spec.Bytes)
    (enc : CustodyApproval → Spec.Bytes) (S : CustodyDigestScheme D) (oracleSign : D → Sig)
    (dep₀ : Nat) (pk₀ : PK) (quorum₀ : CustodyQuorumProfile) (budget : Nat)
    (keys' : Fin (quorum₀.numParties + 1) → Spec.Bytes)
    (A : Code (certAdvIface (Spec.Bytes × CustodyApproval) Spec.Bytes Sig) R)
    (r : Fin (quorum₀.numParties + 1)) (j : Nat) :
    Code (tagIface CustodyApproval) (CustodyApproval × Spec.Bytes) :=
  redCode prf enc S oracleSign dep₀ pk₀ quorum₀ budget quorum₀.numParties r keys' A j
    (CertCustodyState.init dep₀ pk₀ quorum₀) 0 []

/-- The tag-forgery adversary asks its oracle at most `budget` times, whatever `A` does. -/
theorem certTagForger_within {R : Type} (prf : Spec.Bytes → Spec.Bytes → Spec.Bytes)
    (enc : CustodyApproval → Spec.Bytes) (S : CustodyDigestScheme D) (oracleSign : D → Sig)
    (dep₀ : Nat) (pk₀ : PK) (quorum₀ : CustodyQuorumProfile) (budget : Nat)
    (keys' : Fin (quorum₀.numParties + 1) → Spec.Bytes)
    (A : Code (certAdvIface (Spec.Bytes × CustodyApproval) Spec.Bytes Sig) R)
    (r : Fin (quorum₀.numParties + 1)) (j : Nat) :
    Within budget (certTagForger prf enc S oracleSign dep₀ pk₀ quorum₀ budget keys' A r j) :=
  Within.mono (Nat.sub_le budget 0)
    (redCode_within prf enc S oracleSign dep₀ pk₀ quorum₀ budget quorum₀.numParties r keys' A j
      (CertCustodyState.init dep₀ pk₀ quorum₀) 0 [])

/-- **Per-coin reduction.** If an adaptive run of `A` in the certificate world over tag
    certificates ends in an unsafe release, then for some key index `r`, every reduction that
    holds keys agreeing with the real ones away from `r` has a guess `j < budget` with which it
    wins the fresh-message tag experiment under key `r` with `budget` oracle queries. -/
theorem certAdaptiveRun_unsafe_release_tag_forgery {R : Type}
    (prf : Spec.Bytes → Spec.Bytes → Spec.Bytes)
    (enc : CustodyApproval → Spec.Bytes) (S : CustodyDigestScheme D) (oracleSign : D → Sig)
    (dep₀ : Nat) (pk₀ : PK) (quorum₀ : CustodyQuorumProfile) (budget : Nat)
    (keys : Fin (quorum₀.numParties + 1) → Spec.Bytes)
    (A : Code (certAdvIface (Spec.Bytes × CustodyApproval) Spec.Bytes Sig) R)
    (hU : certUnsafeRelease quorum₀.numParties dep₀
      (certAdaptiveRun (encTagCertLayer prf enc (custKey quorum₀.numParties keys))
        (custKey quorum₀.numParties keys) S oracleSign dep₀ pk₀ quorum₀ budget A).2.1 = true) :
    ∃ r : Fin (quorum₀.numParties + 1),
      ∀ keys' : Fin (quorum₀.numParties + 1) → Spec.Bytes, (∀ i, i ≠ r → keys' i = keys i) →
        ∃ j, j < budget ∧
          msgFreshWin enc (prf (keys r)) (tagRun enc (prf (keys r)) budget
            (certTagForger prf enc S oracleSign dep₀ pk₀ quorum₀ budget keys' A r j)) = true := by
  have hne := certAdaptiveRun_unsafe_release_forgery _ _ S oracleSign dep₀ pk₀ quorum₀ budget A hU
  cases hf : (certAdaptiveRun (encTagCertLayer prf enc (custKey quorum₀.numParties keys))
      (custKey quorum₀.numParties keys) S oracleSign dep₀ pk₀ quorum₀ budget A).2.1.forgeries with
  | nil => exact absurd hf hne
  | cons x rest =>
    refine ⟨custIdx quorum₀.numParties x.2.party, fun keys' hK => ?_⟩
    have hm : x ∈ rForg quorum₀.numParties (custIdx quorum₀.numParties x.2.party)
        (certAdaptiveRun (encTagCertLayer prf enc (custKey quorum₀.numParties keys))
          (custKey quorum₀.numParties keys) S oracleSign dep₀ pk₀ quorum₀ budget A).2.1 :=
      List.mem_filter.mpr ⟨by rw [hf]; exact List.mem_cons_self, decide_eq_true rfl⟩
    have hF : rForg quorum₀.numParties (custIdx quorum₀.numParties x.2.party)
        (certAdaptiveRun (encTagCertLayer prf enc (custKey quorum₀.numParties keys))
          (custKey quorum₀.numParties keys) S oracleSign dep₀ pk₀ quorum₀ budget A).2.1 ≠ [] :=
      fun h => by rw [h] at hm; cases hm
    obtain ⟨j, hj, hW⟩ := red_sim prf enc S oracleSign dep₀ pk₀ quorum₀ budget quorum₀.numParties
      (custIdx quorum₀.numParties x.2.party) keys keys' hK A
      (CertCustodyState.init dep₀ pk₀ quorum₀) [] 0 rfl [] []
      { noForg := by rw [CertCustodyState.init.public_eqs]; rfl
        enrolled := by rw [CertCustodyState.init.public_eqs]; exact Nat.le_refl _
        tagged := by rw [CertCustodyState.init.public_eqs]; intro a ha; cases ha
        tagsOk := fun a t h => by cases h
        logIssued := fun a h => by cases h
        logLen := Nat.le_refl 0 } hF
    refine ⟨j, by omega, ?_⟩
    rw [msgFreshWin.public_eqs, tagRun.public_eqs]
    exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true hW.1, decide_eq_true hW.2⟩

/-- **Witness-extraction form.** With permits encoded by `permitInput dg` to `inLen` bytes, the
    winning run of the reduction is a correct tag on a fresh input of the keyed function, or it
    exhibits an explicit collision of the digest `dg`. -/
theorem certAdaptiveRun_unsafe_release_fresh_forgery_or_collision {R : Type}
    (prf : Spec.Bytes → Spec.Bytes → Spec.Bytes) (dg : Spec.Bytes → Spec.Bytes) (inLen : Nat)
    (hLen : ∀ x : Spec.Bytes, (dg x).length = inLen)
    (S : CustodyDigestScheme D) (oracleSign : D → Sig)
    (dep₀ : Nat) (pk₀ : PK) (quorum₀ : CustodyQuorumProfile) (budget : Nat)
    (keys : Fin (quorum₀.numParties + 1) → Spec.Bytes)
    (A : Code (certAdvIface (Spec.Bytes × CustodyApproval) Spec.Bytes Sig) R)
    (hU : certUnsafeRelease quorum₀.numParties dep₀
      (certAdaptiveRun (encTagCertLayer prf (permitInput dg) (custKey quorum₀.numParties keys))
        (custKey quorum₀.numParties keys) S oracleSign dep₀ pk₀ quorum₀ budget A).2.1 = true) :
    ∃ r : Fin (quorum₀.numParties + 1),
      ∀ keys' : Fin (quorum₀.numParties + 1) → Spec.Bytes, (∀ i, i ≠ r → keys' i = keys i) →
        ∃ j, j < budget ∧
          (encFreshWin (permitInput dg) inLen (prf (keys r))
              (tagRun (permitInput dg) (prf (keys r)) budget
                (certTagForger prf (permitInput dg) S oracleSign dep₀ pk₀ quorum₀ budget keys' A
                  r j)) = true ∨
            Nonempty (HashCollision dg)) := by
  obtain ⟨r, hr⟩ := certAdaptiveRun_unsafe_release_tag_forgery prf (permitInput dg) S oracleSign
    dep₀ pk₀ quorum₀ budget keys A hU
  refine ⟨r, fun keys' hK => ?_⟩
  obtain ⟨j, hj, hW⟩ := hr keys' hK
  refine ⟨j, hj, ?_⟩
  rcases msgFreshWin_encFresh_or_collision (permitInput dg) inLen
      (fun m => by rw [permitInput.public_eqs]; exact hLen _) _ _ hW with h | h
  · exact .inl h
  · exact .inr (permitCollision_yields_digest_collision dg _ h)

/-- The coin with adversary coordinate `a` and the challenger coordinate of coin `0`. -/
def repCoin {N nC nA : Nat} (hN : 0 < N) (π : CoinSplit N nC nA) (a : Fin nA) : Fin N :=
  π.pair (π.chal ⟨0, hN⟩) a

/-- **Independence of the custodian keys.** For every key index `r`, with `π r` the coin split
    whose challenger coordinate carries key `r`: the adversary's program, the signing oracle and
    every other key are functions of the adversary coordinate of `π r`. -/
def KeyIndependent {R : Type} {N k : Nat} {nC nA : Fin (k + 1) → Nat}
    (π : (r : Fin (k + 1)) → CoinSplit N (nC r) (nA r))
    (keys : Fin N → Fin (k + 1) → Spec.Bytes) (oracleSign : Fin N → D → Sig)
    (adv : Fin N → Code (certAdvIface (Spec.Bytes × CustodyApproval) Spec.Bytes Sig) R) : Prop :=
  ∀ (r : Fin (k + 1)) (ω ω' : Fin N), (π r).advc ω = (π r).advc ω' →
    adv ω = adv ω' ∧ oracleSign ω = oracleSign ω' ∧ ∀ i, i ≠ r → keys ω i = keys ω' i

/-- The tag-forgery adversary of key index `r` and guess `j` as a function of the adversary
    coordinate `a` of the split `π`: `certTagForger` on the data of the coin `repCoin hN π a`. -/
def coinTagForger {R : Type} {N nC nA : Nat} (hN : 0 < N)
    (prf : Spec.Bytes → Spec.Bytes → Spec.Bytes)
    (enc : CustodyApproval → Spec.Bytes) (S : CustodyDigestScheme D)
    (dep₀ : Nat) (pk₀ : PK) (quorum₀ : CustodyQuorumProfile) (budget : Nat)
    (keys : Fin N → Fin (quorum₀.numParties + 1) → Spec.Bytes) (oracleSign : Fin N → D → Sig)
    (adv : Fin N → Code (certAdvIface (Spec.Bytes × CustodyApproval) Spec.Bytes Sig) R)
    (π : CoinSplit N nC nA) (r : Fin (quorum₀.numParties + 1)) (j : Nat) (a : Fin nA) :
    Code (tagIface CustodyApproval) (CustodyApproval × Spec.Bytes) :=
  certTagForger prf enc S (oracleSign (repCoin hN π a)) dep₀ pk₀ quorum₀ budget
    (keys (repCoin hN π a)) (adv (repCoin hN π a)) r j

/-- The fresh-message tag experiment of key index `r` and guess `j`. -/
def certForgeGame {R : Type} {N : Nat} (hN : 0 < N)
    (prf : Spec.Bytes → Spec.Bytes → Spec.Bytes)
    (enc : CustodyApproval → Spec.Bytes) (S : CustodyDigestScheme D)
    (dep₀ : Nat) (pk₀ : PK) (quorum₀ : CustodyQuorumProfile) (budget : Nat)
    (keys : Fin N → Fin (quorum₀.numParties + 1) → Spec.Bytes) (oracleSign : Fin N → D → Sig)
    (adv : Fin N → Code (certAdvIface (Spec.Bytes × CustodyApproval) Spec.Bytes Sig) R)
    {nC nA : Fin (quorum₀.numParties + 1) → Nat}
    (π : (r : Fin (quorum₀.numParties + 1)) → CoinSplit N (nC r) (nA r))
    (sample : (r : Fin (quorum₀.numParties + 1)) → Fin (nC r) →
      Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (r : Fin (quorum₀.numParties + 1)) (j : Fin budget) : FinGame N :=
  eufCmaTagGame hN enc budget (fun ω => prf (sample r ((π r).chal ω)).1)
    (fun ω => coinTagForger hN prf enc S dep₀ pk₀ quorum₀ budget keys oracleSign adv (π r) r
      j.val ((π r).advc ω))

/-- **`Pr[unsafe release] ≤ Pr[some tag experiment is won]`, per coin.** Over a coin space with
    independent custodian keys, every coin with an unsafe release in the adaptive certificate
    world is a winning coin of the tag experiment `certForgeGame r j` for some key index `r` and
    guess `j`. No assumption on `prf`. -/
theorem certCustody_adaptive_unsafe_release_extract {R : Type} {N : Nat} (hN : 0 < N)
    (prf : Spec.Bytes → Spec.Bytes → Spec.Bytes)
    (enc : CustodyApproval → Spec.Bytes) (S : CustodyDigestScheme D)
    (dep₀ : Nat) (pk₀ : PK) (quorum₀ : CustodyQuorumProfile) (budget : Nat)
    (keys : Fin N → Fin (quorum₀.numParties + 1) → Spec.Bytes) (oracleSign : Fin N → D → Sig)
    (adv : Fin N → Code (certAdvIface (Spec.Bytes × CustodyApproval) Spec.Bytes Sig) R)
    {nC nA : Fin (quorum₀.numParties + 1) → Nat}
    (π : (r : Fin (quorum₀.numParties + 1)) → CoinSplit N (nC r) (nA r))
    (sample : (r : Fin (quorum₀.numParties + 1)) → Fin (nC r) →
      Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (hKey : ∀ (r : Fin (quorum₀.numParties + 1)) (ω : Fin N),
      keys ω r = (sample r ((π r).chal ω)).1)
    (hInd : KeyIndependent π keys oracleSign adv) (ω : Fin N)
    (hU : certUnsafeRelease quorum₀.numParties dep₀
      (certAdaptiveRun (encTagCertLayer prf enc (custKey quorum₀.numParties (keys ω)))
        (custKey quorum₀.numParties (keys ω)) S (oracleSign ω) dep₀ pk₀ quorum₀ budget
        (adv ω)).2.1 = true) :
    ∃ (r : Fin (quorum₀.numParties + 1)) (j : Fin budget),
      (certForgeGame hN prf enc S dep₀ pk₀ quorum₀ budget keys oracleSign adv π sample r j).win ω =
        true := by
  obtain ⟨r, hr⟩ := certAdaptiveRun_unsafe_release_tag_forgery prf enc S (oracleSign ω) dep₀ pk₀
    quorum₀ budget (keys ω) (adv ω) hU
  obtain ⟨hA, hS, hKo⟩ := hInd r (repCoin hN (π r) ((π r).advc ω)) ω ((π r).advc_pair _ _)
  obtain ⟨j, hj, hW⟩ := hr (keys (repCoin hN (π r) ((π r).advc ω))) hKo
  refine ⟨r, ⟨j, hj⟩, ?_⟩
  rw [← hA, ← hS, hKey r ω] at hW
  unfold certForgeGame
  rw [eufCmaTagGame.public_eqs]
  exact hW

/-- **Adaptive unsafe-release bound for the certificate-pool coordinator over PRF tags.**

    The game: `quorum₀.numParties + 1` keys (one per enrolled custodian, and one under which
    certificates naming an unenrolled party identifier are verified; no honest port issues under
    it), a signing oracle and an adaptive adversary `adv` are functions of a coin `ω`. The
    adversary runs against `certCustodyMachine` over `encTagCertLayer prf (permitInput dg)`
    (certificate tag `prfCustodyTag prf dg key`) for at most `budget` queries: honest approvals
    (it receives the certificate), submissions of arbitrary certificates, corruptions (it
    receives the key; each accepted corruption keeps the total below `threshold`), and signing requests. It
    wins when the WAL holds a release no enrolled custodian issued a permit for.

    Hypotheses: `PrfHard` for `prf` with `budget + 1` queries against a class `𝒜` containing the
    forgery distinguishers of the reduction adversaries `coinTagForger` (`hD`); `dg` maps to `inLen` bytes; key `r` is the first component of a
    uniform PRF sample on the challenger coordinate of `π r` (`hU`, `hKey`) and everything else
    is independent of it (`hInd`); and collision resistance of the permit digest against the
    reduction adversaries: each of their runs exhibits two different permits with one digest
    with probability at most `εColl` (`hColl`).

    Conclusion:
    `Pr[unsafe release] ≤ (numParties + 1) * budget * (εPrf + 256 ^ (-outLen) + εColl)`.
    The factor `budget` pays for the guess of which submission is the first forgery. -/
theorem certCustody_adaptive_unsafe_release_bound {R : Type} {N : Nat} (hN : 0 < N)
    (S : CustodyDigestScheme D) (dep₀ : Nat) (pk₀ : PK) (quorum₀ : CustodyQuorumProfile)
    (budget : Nat)
    (prf : Spec.Bytes → Spec.Bytes → Spec.Bytes) (dg : Spec.Bytes → Spec.Bytes) (inLen : Nat)
    (hLen : ∀ x : Spec.Bytes, (dg x).length = inLen) (keyLen outLen : Nat)
    {𝒜 : Code byteOracleIface Bool → Prop} {εPrf εColl : Spec.RatBound}
    (hPrf : PrfHard 𝒜 prf keyLen inLen outLen (budget + 1) εPrf)
    {nC nA : Fin (quorum₀.numParties + 1) → Nat}
    (π : (r : Fin (quorum₀.numParties + 1)) → CoinSplit N (nC r) (nA r))
    (sample : (r : Fin (quorum₀.numParties + 1)) → Fin (nC r) →
      Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (hU : ∀ r, UniformOn (PrfSampleOk keyLen inLen outLen) (sample r))
    (keys : Fin N → Fin (quorum₀.numParties + 1) → Spec.Bytes) (oracleSign : Fin N → D → Sig)
    (adv : Fin N → Code (certAdvIface (Spec.Bytes × CustodyApproval) Spec.Bytes Sig) R)
    (hKey : ∀ (r : Fin (quorum₀.numParties + 1)) (ω : Fin N),
      keys ω r = (sample r ((π r).chal ω)).1)
    (hInd : KeyIndependent π keys oracleSign adv)
    (hD : ∀ (r : Fin (quorum₀.numParties + 1)) (j : Fin budget) (a : Fin (nA r)),
      𝒜 (tagForgeDistinguisher (permitInput dg) budget inLen
        (coinTagForger hN prf (permitInput dg) S dep₀ pk₀ quorum₀ budget keys oracleSign adv
          (π r) r j.val a)))
    (hColl : ∀ (r : Fin (quorum₀.numParties + 1)) (j : Fin budget),
      GameBound
        (encCollisionGame hN (permitInput dg) budget (fun ω => prf (sample r ((π r).chal ω)).1)
          (fun ω => coinTagForger hN prf (permitInput dg) S dep₀ pk₀ quorum₀ budget keys
            oracleSign adv (π r) r j.val ((π r).advc ω))).winProb εColl) :
    GameBound
      (FinGame.mk hN (fun ω => certUnsafeRelease quorum₀.numParties dep₀
        (certAdaptiveRun
          (encTagCertLayer prf (permitInput dg) (custKey quorum₀.numParties (keys ω)))
          (custKey quorum₀.numParties (keys ω)) S (oracleSign ω) dep₀ pk₀ quorum₀ budget
          (adv ω)).2.1)).winProb
      (((εPrf.add (tagGuessBound outLen)).add εColl).scale
        ((quorum₀.numParties + 1) * budget)) :=
  event_le_family_reductions _
    (fun z => certForgeGame hN prf (permitInput dg) S dep₀ pk₀ quorum₀ budget keys oracleSign
      adv π sample ((CoinSplit.prod (quorum₀.numParties + 1) budget).chal z)
      ((CoinSplit.prod (quorum₀.numParties + 1) budget).advc z))
    (fun ω hWin => by
      obtain ⟨r, j, hW⟩ := certCustody_adaptive_unsafe_release_extract hN prf (permitInput dg) S
        dep₀ pk₀ quorum₀ budget keys oracleSign adv π sample hKey hInd ω hWin
      refine ⟨(CoinSplit.prod (quorum₀.numParties + 1) budget).pair r j, ?_⟩
      rw [(CoinSplit.prod (quorum₀.numParties + 1) budget).chal_pair,
        (CoinSplit.prod (quorum₀.numParties + 1) budget).advc_pair]
      exact hW)
    (fun z => GameBound.trans
      (prfCustodyTag_unforgeable hN dg budget inLen hLen prf keyLen outLen hPrf
        (π ((CoinSplit.prod (quorum₀.numParties + 1) budget).chal z))
        (sample ((CoinSplit.prod (quorum₀.numParties + 1) budget).chal z)) (hU _)
        (fun a => coinTagForger hN prf (permitInput dg) S dep₀ pk₀ quorum₀ budget keys oracleSign
          adv (π ((CoinSplit.prod (quorum₀.numParties + 1) budget).chal z))
          ((CoinSplit.prod (quorum₀.numParties + 1) budget).chal z)
          ((CoinSplit.prod (quorum₀.numParties + 1) budget).advc z).val a)
        (hD _ _)).1
      (Spec.RatBound.add_le_add (Spec.RatBound.le_refl _) (hColl _ _)))

end Game

/-! ## 7. Negative results and inhabitants -/

section Teeth

variable {PK D Sig : Type} [DecidableEq D]

/-- 1-of-1 custody with spend cap `100`. -/
def toothQuorum : CustodyQuorumProfile :=
  { numParties := 1, threshold := 1, spendCap := 100, h_pos := by decide, h_le := by decide }

/-- The intent the tooth adversaries get released. -/
def toothTarget : CustodyIntent :=
  { sessionId := 1, round := 0, epoch := 0, spend := 40, payload := [] }

/-- The intent the key-reading adversary asks an honest certificate for. -/
def toothDecoy : CustodyIntent :=
  { sessionId := 2, round := 0, epoch := 0, spend := 0, payload := [] }

private theorem pooled_sign_unsafe {Cert : Type} (L : CustodyCertLayer Cert)
    (S : CustodyDigestScheme D) (oracleSign : D → Sig) (dep₀ : Nat) (pk₀ : PK)
    (c : CertCustodyState PK D Sig Cert) (x : Cert)
    (hL : c.ledger = (IdealCustodyState.init (D := D) (Sig := Sig) dep₀ pk₀ toothQuorum).ledger)
    (hx : x ∈ c.pool) (hcl : L.claim x = ⟨0, dep₀, toothTarget⟩)
    (hni : (⟨0, dep₀, toothTarget⟩ : CustodyApproval) ∉ c.issued) :
    certUnsafeRelease 1 dep₀ ((certCustodyMachine L S oracleSign dep₀ pk₀ toothQuorum).runStep c
      (.sign dep₀ toothTarget false)).1 = true := by
  have hv : certVoted L c.pool 0 dep₀ toothTarget = true := by
    rw [certVoted.public_eqs]
    exact List.any_eq_true.mpr ⟨x, hx, decide_eq_true hcl⟩
  have hApp : (certApprovers L c.ledger.quorum.numParties c.pool c.ledger.deploymentId
      toothTarget).length = 1 := by
    rw [hL, certApprovers.public_eqs]
    exact congrArg List.length (List.filter_cons_of_pos
      (p := fun p => certVoted L c.pool p dep₀ toothTarget) (a := 0) (l := []) hv)
  have hStep := custodyLedgerSign_fresh_release (S := S) (oracleSign := oracleSign)
    (L := c.ledger) (n := 1) (dep := dep₀) (i := toothTarget)
    (by rw [hL]; rfl) (by rw [hL]; rfl) (by rw [hL]; rfl) (by rw [hL]; exact Nat.zero_le _)
    (by rw [hL]; intro h; cases h) (by rw [hL]; exact Nat.le_refl 1)
    (by rw [hL]; show 0 + 40 ≤ 100; decide)
  rw [certRunStep_of_some L S oracleSign dep₀ pk₀ toothQuorum
    (by rw [certCustodyStep.public_eq_4, hApp, hStep]; rfl), certUnsafeRelease.public_eqs]
  refine List.any_eq_true.mpr ⟨⟨toothTarget, _, _⟩, List.mem_cons_self, ?_⟩
  show (!(decide ((⟨0, dep₀, toothTarget⟩ : CustodyApproval) ∈ c.issued) || false)) = true
  rw [decide_eq_false hni]
  rfl

omit [DecidableEq D] in
private theorem submitWith_pool_valid (c : CertCustodyState PK D Sig (Spec.Bytes × CustodyApproval))
    (x : Spec.Bytes × CustodyApproval) (hd : x.2.deploymentId = c.ledger.deploymentId) :
    x ∈ (submitWith true c x).1.pool := by
  unfold submitWith
  rw [ifP (And.intro rfl hd)]
  exact List.mem_cons_self

omit [DecidableEq D] in
private theorem submitWith_pool_mono (v : Bool)
    (c : CertCustodyState PK D Sig (Spec.Bytes × CustodyApproval))
    (x y : Spec.Bytes × CustodyApproval) (h : y ∈ c.pool) : y ∈ (submitWith v c x).1.pool := by
  unfold submitWith
  by_cases hg : v = true ∧ x.2.deploymentId = c.ledger.deploymentId
  · rw [ifP hg]; exact List.mem_cons_of_mem _ h
  · rw [ifN hg]; exact h

/-- Submit the certificates `(t, a)` for the tags `t` of a list, then continue. -/
def submitAll (a : CustodyApproval) :
    List Spec.Bytes → Code (certAdvIface (Spec.Bytes × CustodyApproval) Spec.Bytes Sig) Unit →
      Code (certAdvIface (Spec.Bytes × CustodyApproval) Spec.Bytes Sig) Unit
  | [], rest => rest
  | t :: ts, rest =>
    .call (E := certAdvIface (Spec.Bytes × CustodyApproval) Spec.Bytes Sig) (.submit (t, a))
      (fun _ => submitAll a ts rest)

/-- Ask the coordinator to sign `toothTarget`. -/
def signTarget (dep : Nat) :
    Code (certAdvIface (Spec.Bytes × CustodyApproval) Spec.Bytes Sig) Unit :=
  .call (E := certAdvIface (Spec.Bytes × CustodyApproval) Spec.Bytes Sig)
    (.sign dep toothTarget false) (fun _ => .ret ())

private theorem submitAll_sign_unsafe (prf : Spec.Bytes → Spec.Bytes → Spec.Bytes)
    (enc : CustodyApproval → Spec.Bytes) (key : Nat → Spec.Bytes) (S : CustodyDigestScheme D)
    (oracleSign : D → Sig) (dep₀ : Nat) (pk₀ : PK) (budget : Nat) :
    ∀ (ts : List Spec.Bytes) (c : CertCustodyState PK D Sig (Spec.Bytes × CustodyApproval))
      (tr : List (CertCustodyInput (Spec.Bytes × CustodyApproval))),
      tr.length + ts.length < budget →
      c.ledger = (IdealCustodyState.init (D := D) (Sig := Sig) dep₀ pk₀ toothQuorum).ledger →
      (⟨0, dep₀, toothTarget⟩ : CustodyApproval) ∉ c.issued →
      (prf (key 0) (enc ⟨0, dep₀, toothTarget⟩) ∈ ts ∨
        (prf (key 0) (enc ⟨0, dep₀, toothTarget⟩), ⟨0, dep₀, toothTarget⟩) ∈ c.pool) →
      certUnsafeRelease 1 dep₀
        (Code.play (certWorldOracle (encTagCertLayer prf enc key) key S oracleSign dep₀ pk₀
          toothQuorum budget) (submitAll ⟨0, dep₀, toothTarget⟩ ts (signTarget dep₀))
          (c, tr)).2.1 = true
  | [], c, tr, hb, hL, hni, hv => by
    rw [submitAll]
    unfold signTarget
    rw [Code.play_call, certWorldOracle_pos _ _ S oracleSign dep₀ pk₀ toothQuorum budget c tr
      (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hb), Code.play_ret]
    exact pooled_sign_unsafe (encTagCertLayer prf enc key) S oracleSign dep₀ pk₀ c _ hL
      (hv.resolve_left (fun h => by cases h)) rfl hni
  | t :: ts, c, tr, hb, hL, hni, hv => by
    have h1 : (tr ++ [CertCustodyInput.submit
        (t, (⟨0, dep₀, toothTarget⟩ : CustodyApproval))]).length = tr.length + 1 := by
      rw [List.length_append]; rfl
    have h2 : (t :: ts).length = ts.length + 1 := rfl
    rw [h2] at hb
    rw [submitAll, Code.play_call, certWorldOracle_pos _ _ S oracleSign dep₀ pk₀ toothQuorum
      budget c tr (by omega), encTag_runStep_submit]
    refine submitAll_sign_unsafe prf enc key S oracleSign dep₀ pk₀ budget ts _ _ (by omega)
      ((submitWith_frame _ c _).1.trans hL)
      (by rw [(submitWith_frame _ c _).2.1]; exact hni) ?_
    rcases hv with hmem | hpool
    · rcases List.mem_cons.mp hmem with hEq | hT
      · refine .inr ?_
        show (prf (key 0) (enc ⟨0, dep₀, toothTarget⟩),
            (⟨0, dep₀, toothTarget⟩ : CustodyApproval)) ∈
          (submitWith (decide (t = prf (key 0) (enc ⟨0, dep₀, toothTarget⟩))) c
            (t, ⟨0, dep₀, toothTarget⟩)).1.pool
        rw [decide_eq_true hEq.symm, hEq]
        exact submitWith_pool_valid c _ (by rw [hL]; rfl)
      · exact .inl hT
    · exact .inr (submitWith_pool_mono _ c _ _ hpool)

/-- The key-reading adversary: one honest certificate from custodian `0` for `toothDecoy`, then
    a certificate for `toothTarget` carrying the tag of the first one, then a signing request. -/
def toothKeyReadAdv (dep : Nat) :
    Code (certAdvIface (Spec.Bytes × CustodyApproval) Spec.Bytes Sig) Unit :=
  .call (E := certAdvIface (Spec.Bytes × CustodyApproval) Spec.Bytes Sig)
    (.approve 0 dep toothDecoy)
    (fun ρ =>
      match ρ.2.1 with
      | some cert => submitAll ⟨0, dep, toothTarget⟩ [cert.1] (signTarget dep)
      | none => .ret ())

private theorem toothKeyReadAdv_unsafe (enc : CustodyApproval → Spec.Bytes) (key : Nat → Spec.Bytes)
    (S : CustodyDigestScheme D) (oracleSign : D → Sig) (dep₀ : Nat) (pk₀ : PK) {budget : Nat}
    (hb : 3 ≤ budget) :
    certUnsafeRelease 1 dep₀
      (certAdaptiveRun (encTagCertLayer (fun kk _ => kk) enc key) key S oracleSign dep₀ pk₀
        toothQuorum budget (toothKeyReadAdv dep₀)).2.1 = true := by
  have hA : (certCustodyMachine (encTagCertLayer (fun kk _ => kk) enc key) S oracleSign dep₀ pk₀
        toothQuorum).runStep (CertCustodyState.init dep₀ pk₀ toothQuorum)
        (.approve 0 dep₀ toothDecoy) =
      ({ (CertCustodyState.init dep₀ pk₀ toothQuorum :
            CertCustodyState PK D Sig (Spec.Bytes × CustodyApproval)) with
          issued := CustodyApproval.mk 0 dep₀ toothDecoy ::
            (CertCustodyState.init dep₀ pk₀ toothQuorum :
              CertCustodyState PK D Sig (Spec.Bytes × CustodyApproval)).issued },
        some .approvalRecorded) := by
    rw [certRunStep_approve]
    have g1 : 0 < (CertCustodyState.init dep₀ pk₀ toothQuorum :
        CertCustodyState PK D Sig (Spec.Bytes × CustodyApproval)).ledger.quorum.numParties := by
      rw [CertCustodyState.init.public_eqs]; exact Nat.one_pos
    have g2 : 0 ∉ (CertCustodyState.init dep₀ pk₀ toothQuorum :
        CertCustodyState PK D Sig (Spec.Bytes × CustodyApproval)).corruptParties := by
      rw [CertCustodyState.init.public_eqs]; intro h; cases h
    have g3 : dep₀ = (CertCustodyState.init dep₀ pk₀ toothQuorum :
        CertCustodyState PK D Sig (Spec.Bytes × CustodyApproval)).ledger.deploymentId := by
      rw [CertCustodyState.init.public_eqs]; rfl
    exact ifP (And.intro g1 (And.intro g2 g3)) _ _
  unfold certAdaptiveRun toothKeyReadAdv
  rw [Code.play_call, certWorldOracle_pos _ _ S oracleSign dep₀ pk₀ toothQuorum budget _ []
    (Nat.lt_of_lt_of_le (by decide) hb), hA]
  refine submitAll_sign_unsafe (fun kk _ => kk) enc key S oracleSign dep₀ pk₀ budget [key 0] _ _
    (Nat.lt_of_lt_of_le (by decide : 2 < 3) hb)
    (by rw [CertCustodyState.init.public_eqs]) ?_ (.inl List.mem_cons_self)
  rw [CertCustodyState.init.public_eqs]
  intro h
  rcases List.mem_cons.mp h with h | h
  · have h' : (1 : Nat) = 2 := congrArg (fun a : CustodyApproval => a.intent.sessionId) h
    exact absurd h' (by decide)
  · cases h

/-- **A certificate layer whose tags reveal the key is broken by an adaptive adversary.** With
    the tag equal to the custodian's key (the tag of `macCertLayer`), in the game of
    `certCustody_adaptive_unsafe_release_bound` for 1-of-1 custody, the adversary that asks one
    honest certificate, reads the key off it and certifies an intent the custodian never approved
    obtains an unsafe release on every coin: no bound below `1` holds. -/
theorem certCustody_tooth_key_revealing_tag_adaptive_unsafe_release {N : Nat} (hN : 0 < N)
    (enc : CustodyApproval → Spec.Bytes) (keys : Fin N → Nat → Spec.Bytes)
    (S : CustodyDigestScheme D) (oracleSign : Fin N → D → Sig) (dep₀ : Nat) (pk₀ : PK)
    {budget : Nat} (hb : 3 ≤ budget) {ε : Spec.RatBound} (hε : ε.num < ε.den) :
    ¬ GameBound
      (FinGame.mk hN (fun ω => certUnsafeRelease 1 dep₀
        (certAdaptiveRun (encTagCertLayer (fun kk _ => kk) enc (keys ω)) (keys ω) S
          (oracleSign ω) dep₀ pk₀ toothQuorum budget (toothKeyReadAdv dep₀)).2.1)).winProb ε :=
  FinGame.not_bound_of_forall_win _
    (fun ω => toothKeyReadAdv_unsafe enc (keys ω) S (oracleSign ω) dep₀ pk₀ hb) hε

/-- All one-byte tags. -/
def allByteTags : List Spec.Bytes :=
  (List.range 256).map (fun n => [UInt8.ofNat n])

private theorem mem_allByteTags : ∀ t : Spec.Bytes, t.length = 1 → t ∈ allByteTags
  | [], h => absurd h (by decide)
  | [b], _ => List.mem_map.mpr ⟨b.toNat, List.mem_range.mpr b.toBitVec.isLt, by
      rw [UInt8.ofNat_toNat]⟩
  | _ :: _ :: _, h => absurd (Nat.succ.inj h) (Nat.succ_ne_zero _)

/-- The guessing adversary: submit a certificate for `toothTarget` with every one-byte tag, then
    request the signature. `257` queries, no honest certificate. -/
def toothGuessAdv (dep : Nat) :
    Code (certAdvIface (Spec.Bytes × CustodyApproval) Spec.Bytes Sig) Unit :=
  submitAll ⟨0, dep, toothTarget⟩ allByteTags (signTarget dep)

/-- **Exhausting the tag space forces release.** For every keyed function with
    one-byte outputs (`outLen = 1`), every encoding and every key, the guessing adversary obtains
    an unsafe release on every coin with `257` queries. A bound
    `(numParties + 1) * (εPrf + 256 ^ (-outLen) + εColl)` without the number of submissions would
    be `2 * (εPrf + 1 / 256 + εColl)` here, below `1` for small `εPrf`, `εColl`. -/
theorem certCustody_tooth_guess_all_tags_unsafe_release {N : Nat} (hN : 0 < N)
    (prf : Spec.Bytes → Spec.Bytes → Spec.Bytes)
    (hOut : ∀ kk x : Spec.Bytes, (prf kk x).length = 1)
    (enc : CustodyApproval → Spec.Bytes) (keys : Fin N → Nat → Spec.Bytes)
    (S : CustodyDigestScheme D) (oracleSign : Fin N → D → Sig) (dep₀ : Nat) (pk₀ : PK)
    {budget : Nat} (hb : 257 ≤ budget) {ε : Spec.RatBound} (hε : ε.num < ε.den) :
    ¬ GameBound
      (FinGame.mk hN (fun ω => certUnsafeRelease 1 dep₀
        (certAdaptiveRun (encTagCertLayer prf enc (keys ω)) (keys ω) S (oracleSign ω) dep₀ pk₀
          toothQuorum budget (toothGuessAdv dep₀)).2.1)).winProb ε :=
  FinGame.not_bound_of_forall_win _
    (fun ω => by
      have hl : allByteTags.length = 256 := by
        unfold allByteTags
        rw [List.length_map, List.length_range]
      exact submitAll_sign_unsafe prf enc (keys ω) S (oracleSign ω) dep₀ pk₀ budget allByteTags
        (CertCustodyState.init dep₀ pk₀ toothQuorum) []
        (by rw [hl]; exact Nat.lt_of_lt_of_le (by decide : 0 + 256 < 257) hb)
        (by rw [CertCustodyState.init.public_eqs])
        (by rw [CertCustodyState.init.public_eqs]; intro h; cases h)
        (.inl (mem_allByteTags _ (hOut _ _)))) hε

/-- **A certificate naming any party identifier is a forgery event when that party did not
    issue it**, enrolled or not: from the initial state, the honest-format certificate
    `L.issue p dep₀ i` for an arbitrary `p` (in particular `p ≥ numParties`) is admitted and
    logged in `forgeries`. This is why the bound counts `numParties + 1` keys: the layer must
    verify certificates for unenrolled identifiers under some key. -/
theorem certCustody_tooth_unissued_claim_flagged {Cert : Type} (L : CustodyCertLayer Cert)
    (S : CustodyDigestScheme D) (oracleSign : D → Sig) (dep₀ : Nat) (pk₀ : PK)
    (quorum₀ : CustodyQuorumProfile) (p : Nat) (i : CustodyIntent) :
    ¬ (((certCustodyMachine L S oracleSign dep₀ pk₀ quorum₀).runStep
        (CertCustodyState.init dep₀ pk₀ quorum₀) (.submit (L.issue p dep₀ i))).1.forgeries =
      []) := by
  rw [certRunStep_forgery_flagged L S oracleSign dep₀ pk₀ quorum₀ _ _ (L.issue_valid p dep₀ i)
    (by rw [L.issue_claim, CertCustodyState.init.public_eqs]; rfl)
    (by rw [L.issue_claim, CertCustodyState.init.public_eqs]; intro h; cases h)
    (by rw [L.issue_claim, CertCustodyState.init.public_eqs]; intro h; cases h)]
  exact List.cons_ne_nil _ _

/-- The coin split of `Fin (n * n)` with the two coordinates exchanged. -/
def swapSplit (n : Nat) : CoinSplit (n * n) n n where
  chal := (CoinSplit.prod n n).advc
  advc := (CoinSplit.prod n n).chal
  pair c a := (CoinSplit.prod n n).pair a c
  chal_pair c a := (CoinSplit.prod n n).advc_pair a c
  advc_pair c a := (CoinSplit.prod n n).chal_pair a c
  pair_eta := (CoinSplit.prod n n).pair_eta

omit [DecidableEq D] in
/-- **The independence hypotheses of the bound are satisfiable with two keys.** On the coin
    space `Fin (n * n)`, key `0` read from the first coordinate and key `1` from the second, with
    any fixed adversary and signing oracle: each key is the challenger coordinate of its split
    (`hKey` of the bound), and `KeyIndependent` holds. -/
theorem keyIndependent_two_keys {R : Type} (n : Nat)
    (sample : Fin n → Spec.Bytes × (Spec.Bytes → Spec.Bytes)) (sign : D → Sig)
    (A : Code (certAdvIface (Spec.Bytes × CustodyApproval) Spec.Bytes Sig) R) :
    ∃ (π : (r : Fin (1 + 1)) → CoinSplit (n * n) n n)
      (keys : Fin (n * n) → Fin (1 + 1) → Spec.Bytes),
      (∀ (r : Fin (1 + 1)) (ω : Fin (n * n)), keys ω r = (sample ((π r).chal ω)).1) ∧
      KeyIndependent π keys (fun _ => sign) (fun _ => A) := by
  refine ⟨fun r => match r with
      | ⟨0, _⟩ => CoinSplit.prod n n
      | ⟨_ + 1, _⟩ => swapSplit n,
    fun ω r => match r with
      | ⟨0, _⟩ => (sample ((CoinSplit.prod n n).chal ω)).1
      | ⟨_ + 1, _⟩ => (sample ((CoinSplit.prod n n).advc ω)).1, ?_, ?_⟩
  · intro r ω
    match r with
    | ⟨0, _⟩ => rfl
    | ⟨_ + 1, _⟩ => rfl
  · intro r ω ω' h
    refine ⟨rfl, rfl, fun i hi => ?_⟩
    match r, i, h, hi with
    | ⟨0, _⟩, ⟨0, _⟩, _, hi => exact absurd rfl hi
    | ⟨0, _⟩, ⟨_ + 1, _⟩, h, _ =>
      have h' : (CoinSplit.prod n n).advc ω = (CoinSplit.prod n n).advc ω' := h
      show (sample ((CoinSplit.prod n n).advc ω)).1 = (sample ((CoinSplit.prod n n).advc ω')).1
      rw [h']
    | ⟨_ + 1, _⟩, ⟨0, _⟩, h, _ =>
      have h' : (CoinSplit.prod n n).chal ω = (CoinSplit.prod n n).chal ω' := h
      show (sample ((CoinSplit.prod n n).chal ω)).1 = (sample ((CoinSplit.prod n n).chal ω')).1
      rw [h']
    | ⟨a + 1, ha⟩, ⟨b + 1, hb⟩, _, hi =>
      have ha' : a = 0 := by omega
      have hb' : b = 0 := by omega
      subst ha'
      subst hb'
      exact absurd rfl hi

/-- Cardinality of a vector of independent coins, keeping its head/tail product explicit. -/
def partyCoinCard (n : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => n * partyCoinCard n k

theorem partyCoinCard_pos {n : Nat} (hn : 0 < n) : ∀ k, 0 < partyCoinCard n k
  | 0 => Nat.one_pos
  | k + 1 => Nat.mul_pos hn (partyCoinCard_pos hn k)

/-- Extract a coordinate in the tail, keeping the head among the remaining coins. -/
private def liftPartySplit {n t a : Nat} (tail : CoinSplit t n a) :
    CoinSplit (n * t) n (n * a) where
  chal w := tail.chal ((CoinSplit.prod n t).advc w)
  advc w := (CoinSplit.prod n a).pair ((CoinSplit.prod n t).chal w)
    (tail.advc ((CoinSplit.prod n t).advc w))
  pair c v := (CoinSplit.prod n t).pair ((CoinSplit.prod n a).chal v)
    (tail.pair c ((CoinSplit.prod n a).advc v))
  chal_pair _ _ := by rw [CoinSplit.advc_pair, CoinSplit.chal_pair]
  advc_pair _ _ := by rw [CoinSplit.chal_pair, CoinSplit.advc_pair, CoinSplit.advc_pair,
    CoinSplit.pair_eta]
  pair_eta _ := by rw [CoinSplit.chal_pair, CoinSplit.advc_pair, CoinSplit.pair_eta,
    CoinSplit.pair_eta]

/-- Split all party samples at the selected index. Its complement contains exactly the
    other coordinates, in their original order. -/
def partyCoinSplit (n : Nat) : (k : Nat) → Fin (k + 1) →
    CoinSplit (partyCoinCard n (k + 1)) n (partyCoinCard n k)
  | 0, _ => CoinSplit.prod n 1
  | k + 1, ⟨0, _⟩ => CoinSplit.prod n (partyCoinCard n (k + 1))
  | k + 1, ⟨r + 1, hr⟩ => liftPartySplit (partyCoinSplit n k ⟨r, Nat.lt_of_succ_lt_succ hr⟩)

private theorem otherPartyCoin (n : Nat) : ∀ (k : Nat) (r i : Fin (k + 1))
    (w v : Fin (partyCoinCard n (k + 1))), i ≠ r →
    (partyCoinSplit n k r).advc w = (partyCoinSplit n k r).advc v →
    (partyCoinSplit n k i).chal w = (partyCoinSplit n k i).chal v
  | 0, i, r, _, _, hi, _ => False.elim (hi (Fin.ext (by have := i.isLt; have := r.isLt; omega)))
  | _ + 1, ⟨0, _⟩, ⟨0, _⟩, _, _, hi, _ => False.elim (hi rfl)
  | k + 1, ⟨0, _⟩, ⟨i + 1, _⟩, _, _, _, h =>
    congrArg (partyCoinSplit n k ⟨i, by omega⟩).chal h
  | k + 1, ⟨r + 1, _⟩, i, w, v, hi, h => by
    let head := CoinSplit.prod n (partyCoinCard n (k + 1))
    let rest := CoinSplit.prod n (partyCoinCard n k)
    let t := partyCoinSplit n k ⟨r, by omega⟩
    change rest.pair (head.chal w) (t.advc (head.advc w)) =
      rest.pair (head.chal v) (t.advc (head.advc v)) at h
    match i with
    | ⟨0, _⟩ =>
      have hh := congrArg rest.chal h
      rwa [rest.chal_pair, rest.chal_pair] at hh
    | ⟨i + 1, _⟩ =>
      have hh := congrArg rest.advc h
      rw [rest.advc_pair, rest.advc_pair] at hh
      exact otherPartyCoin n k ⟨r, by omega⟩ ⟨i, by omega⟩ _ _
        (fun eq => hi (Fin.ext (congrArg Nat.succ (congrArg Fin.val eq)))) hh

omit [DecidableEq D] in
theorem keyIndependent_product {R : Type} (n k : Nat)
    (sample : Fin n → Spec.Bytes × (Spec.Bytes → Spec.Bytes)) (sign : D → Sig)
    (A : Code (certAdvIface (Spec.Bytes × CustodyApproval) Spec.Bytes Sig) R) :
    KeyIndependent (partyCoinSplit n k)
      (fun w i => (sample ((partyCoinSplit n k i).chal w)).1) (fun _ => sign) (fun _ => A) :=
  fun r w v hw => ⟨rfl, rfl, fun i hi =>
    congrArg (fun c => (sample c).1) (otherPartyCoin n k r i w v hi hw)⟩

/-- One-entry function table. Inputs outside the zero-byte domain return the sentinel. -/
def singletonTable (value : Spec.Bytes) : Spec.Bytes → Spec.Bytes
  | [] => value
  | _ :: _ => []

private theorem singletonTable_eta {k l : Nat} {x : Spec.Bytes × (Spec.Bytes → Spec.Bytes)}
    (hx : PrfSampleOk k 0 l x) : singletonTable (x.2 []) = x.2 := by
  rw [PrfSampleOk.public_eqs] at hx
  funext y
  cases y with
  | nil => rfl
  | cons a t => exact ((hx.2 (a :: t)).2 (Nat.succ_ne_zero _)).symm

/-- When key and tag have the same length, a uniformly sampled key is an exact
    random function on the singleton domain. This includes arbitrary off-domain queries. -/
theorem singletonTable_prfHard (len q : Nat) (classify : Code byteOracleIface Bool → Prop) :
    PrfHard classify singletonTable len 0 len q Spec.RatBound.zero := by
  intro n nc na hn π sample hu adv _
  let read (c : Fin nc) := ((sample c).1, (sample c).2 [])
  let valid (z : Spec.Bytes × Spec.Bytes) := z.1.length = len ∧ z.2.length = len
  have uniform : UniformOn valid read := by
    constructor
    · intro c
      have h := hu.mem c
      rw [PrfSampleOk.public_eqs] at h
      exact ⟨h.1, (h.2 []).1 rfl⟩
    · intro i j h
      apply hu.injective
      refine Prod.ext (congrArg (Prod.fst (β := Spec.Bytes)) h) ?_
      rw [← singletonTable_eta (hu.mem i), ← singletonTable_eta (hu.mem j)]
      exact congrArg singletonTable (congrArg (Prod.snd (α := Spec.Bytes)) h)
    · intro z hz
      have hm : PrfSampleOk len 0 len (z.1, singletonTable z.2) := by
        rw [PrfSampleOk.public_eqs]
        refine ⟨hz.1, fun y => ?_⟩
        cases y with
        | nil => exact ⟨fun _ => hz.2, fun hh => False.elim (hh rfl)⟩
        | cons a t => exact ⟨fun hh => False.elim (Nat.succ_ne_zero _ hh), fun _ => rfl⟩
      obtain ⟨i, hi⟩ := hu.surjective _ hm
      exact ⟨i, (congrArg (fun x : Spec.Bytes × (Spec.Bytes → Spec.Bytes) => (x.1, x.2 [])) hi)⟩
  have swapped : UniformOn valid (fun c => (read c).swap) :=
    ⟨fun c => ⟨(uniform.mem c).2, (uniform.mem c).1⟩,
     fun i j h => uniform.injective i j (congrArg Prod.swap h),
     fun z hz => by
       obtain ⟨i, hi⟩ := uniform.surjective z.swap ⟨hz.2, hz.1⟩
       exact ⟨i, congrArg Prod.swap hi⟩⟩
  let verdict (f : Spec.Bytes → Spec.Bytes) (a : Fin na) : Nat :=
    if (Code.play (budgetedFunOracle f q) (adv a) 0).1 then 1 else 0
  have same : sampleSum n (fun w => verdict (singletonTable (sample (π.chal w)).1) (π.advc w)) =
      sampleSum n (fun w => verdict (sample (π.chal w)).2 (π.advc w)) := by
    rw [π.sampleSum_eq, π.sampleSum_eq (fun w => verdict (sample (π.chal w)).2 (π.advc w))]
    simp only [π.chal_pair, π.advc_pair]
    refine (uniform.card_and_sampleSum_eq swapped (fun z =>
      sampleSum na (verdict (singletonTable z.1)))).2.trans ?_
    apply sampleSum_ext
    intro c
    change sampleSum na (verdict (singletonTable ((sample c).2 []))) = _
    rw [singletonTable_eta (hu.mem c)]
  change Spec.natAbsDiff _ _ * 1 ≤ 0 * n
  unfold FinGame.winCount
  simp only [prfRealGame.public_eqs, prfIdealGame.public_eqs]
  change Spec.natAbsDiff (sampleSum n (fun w => verdict (singletonTable (sample (π.chal w)).1) (π.advc w)))
    (sampleSum n (fun w => verdict (sample (π.chal w)).2 (π.advc w))) * 1 ≤ _
  rw [same]
  simp only [Spec.natAbsDiff, Nat.le_refl, ↓reduceIte, Nat.sub_self, Nat.zero_mul]

/-- The reduction against a submit-then-sign adversary makes no tag queries. Its returned
    candidate can be a valid guess, but there is no pair of colliding permits in its log. -/
private theorem guessForger_ret {k : Nat}
    (S : CustodyDigestScheme D) (sign : D → Sig) (pk : PK) (profile : CustodyQuorumProfile)
    (prf : Spec.Bytes → Spec.Bytes → Spec.Bytes) (enc : CustodyApproval → Spec.Bytes)
    (r : Fin (k+1)) (keys : Fin (k+1) → Spec.Bytes) (j : Nat)
    (c : CertCustodyState PK D Sig (Spec.Bytes × CustodyApproval)) :
    ∃ z, redCode prf enc S sign 0 pk profile 2 k r keys
      (submitAll ⟨0, 0, toothTarget⟩ [[0]] (signTarget 0)) j c 0 [] = .ret z := by
  by_cases hr : custIdx k 0 = r <;>
    by_cases issued : (⟨0, 0, toothTarget⟩ : CustodyApproval) ∈ c.issued <;>
    cases j <;>
    simp only [submitAll, signTarget, redCode, redAct, Nat.reduceLT, hr, issued, ↓reduceIte] <;>
    exact ⟨_, rfl⟩

abbrev jointSampler := MacBlind.prgPrfSampler (MacBlind.bytesSampler 1) (MacBlind.bytesSampler 1)
abbrev jointCard := 256 ^ 1 * 256 ^ 1
abbrev jointProfile (k : Nat) : CustodyQuorumProfile :=
  ⟨k + 1, 1, 100, Nat.one_pos, Nat.succ_le_succ (Nat.zero_le _)⟩
abbrev jointAdv : Code (certAdvIface (Spec.Bytes × CustodyApproval) Spec.Bytes Unit) Unit :=
  submitAll ⟨0, 0, toothTarget⟩ [[0]] (signTarget 0)

private theorem jointUniform : UniformOn (PrfSampleOk 1 0 1) jointSampler :=
  MacBlind.uniformOn_prgPrfSampler
    (MacBlind.uniformOn_bytesSampler 1) (MacBlind.uniformOn_bytesSampler 1)

abbrev guessKeys (k : Nat) (w : Fin (partyCoinCard jointCard (k+1))) (r : Fin (k+1)) :=
  (jointSampler ((partyCoinSplit jointCard k r).chal w)).1

private theorem guessCollision (k : Nat) (r : Fin ((jointProfile k).numParties+1)) (j : Fin 2) :
    let π := partyCoinSplit jointCard (k+1) r
    let hn := partyCoinCard_pos (by decide : 0 < jointCard) (k+1+1)
    let enc := permitInput (fun _ => [])
    GameBound (encCollisionGame hn enc 2 (fun w => singletonTable (jointSampler (π.chal w)).1)
      (fun w => coinTagForger hn singletonTable enc CustodyDigestScheme.transparent 0 () (jointProfile k)
        2 (guessKeys (k+1)) (fun _ _ => ()) (fun _ => jointAdv) π r j.val (π.advc w))).winProb
      Spec.RatBound.zero := by
  apply FinGame.bound_zero_of_forall_lose
  intro w
  rw [encCollisionGame.public_eqs]
  dsimp only
  unfold coinTagForger certTagForger
  obtain ⟨z, he⟩ := guessForger_ret CustodyDigestScheme.transparent (fun _ => ()) () (jointProfile k)
    singletonTable (permitInput (fun _ => [])) r _ j.val _
  rw [he, tagRun.public_eqs, Code.play_ret, encCollision.public_eqs]
  rfl

/-- All premises of the adaptive bound, on one common product of independent one-byte
    keys and tables. The adversary guesses a tag and requests release. Both error terms
    vanish: a singleton-domain PRF is perfect and this reduction's tag log is empty. -/
theorem inhabited_certCustody_adaptive (k : Nat) :
    ∃ (profile : CustodyQuorumProfile) (N : Nat) (hn : 0 < N)
      (π : (r : Fin (profile.numParties+1)) → CoinSplit N jointCard (partyCoinCard jointCard profile.numParties))
      (sample : (r : Fin (profile.numParties+1)) → Fin jointCard → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
      (keys : Fin N → Fin (profile.numParties+1) → Spec.Bytes)
      (dg : Spec.Bytes → Spec.Bytes),
    profile = jointProfile k ∧
    (∀ x : Spec.Bytes, (dg x).length = 0) ∧
    PrfHard (fun c => Within (2+1) c) singletonTable 1 0 1 (2+1) Spec.RatBound.zero ∧
    (∀ r, UniformOn (PrfSampleOk 1 0 1) (sample r)) ∧
    (∀ r w, keys w r = (sample r ((π r).chal w)).1) ∧
    KeyIndependent π keys (fun _ (_ : Nat × CustodyIntent) => ()) (fun _ => jointAdv) ∧
    (∀ (r : Fin (profile.numParties+1)) (j : Fin 2) (a : Fin (partyCoinCard jointCard profile.numParties)),
      Within (2+1) (tagForgeDistinguisher (permitInput dg) 2 0
        (coinTagForger hn singletonTable (permitInput dg) CustodyDigestScheme.transparent 0 ()
          profile 2 keys (fun _ _ => ()) (fun _ => jointAdv) (π r) r j.val a))) ∧
    (∀ (r : Fin (profile.numParties+1)) (j : Fin 2),
      GameBound (encCollisionGame hn (permitInput dg) 2 (fun w => singletonTable (sample r ((π r).chal w)).1)
        (fun w => coinTagForger hn singletonTable (permitInput dg) CustodyDigestScheme.transparent 0 ()
          profile 2 keys (fun _ _ => ()) (fun _ => jointAdv) (π r) r j.val ((π r).advc w))).winProb
        Spec.RatBound.zero) := by
  exact ⟨jointProfile k, _, partyCoinCard_pos (by decide : 0 < jointCard) _, partyCoinSplit jointCard (k+1),
    fun _ => jointSampler, guessKeys (k+1), fun _ => [], rfl, fun _ => rfl,
    singletonTable_prfHard 1 3 _, fun _ => jointUniform, fun _ _ => rfl,
    keyIndependent_product _ _ jointSampler _ jointAdv,
    fun _ _ _ => tagForgeDistinguisher_within .., guessCollision k⟩

/-- The finite game on two independent one-byte key/table coordinates. -/
def oneGuessReleaseGame : FinGame (partyCoinCard jointCard 2) :=
  ⟨partyCoinCard_pos (by decide : 0 < jointCard) 2, fun w =>
    let key := custKey 1 (guessKeys 1 w)
    certUnsafeRelease 1 0 (certAdaptiveRun (encTagCertLayer singletonTable (permitInput (fun _ => [])) key)
      key CustodyDigestScheme.transparent (fun _ => ()) 0 () toothQuorum 2 jointAdv).2.1⟩

/-- For one custodian the joint example admits a winning coin and has winning probability
    at most 4/256 in the very same game. -/
theorem certCustody_one_guess_nontrivial :
    (∃ w, oneGuessReleaseGame.win w = true) ∧
      GameBound oneGuessReleaseGame.winProb ⟨4,256,by decide⟩ := by
  let hn := partyCoinCard_pos (by decide : 0 < jointCard) 2
  let π := partyCoinSplit jointCard 1
  let S := CustodyDigestScheme.transparent
  let dg := fun _ : Spec.Bytes => ([] : Spec.Bytes)
  constructor
  · let r := custIdx 1 0
    have ok : PrfSampleOk 1 0 1 ([0], singletonTable [0]) := by
      rw [PrfSampleOk.public_eqs]
      refine ⟨rfl, fun y => ?_⟩
      cases y with
      | nil => exact ⟨fun _ => rfl, fun h => False.elim (h rfl)⟩
      | cons a t => exact ⟨fun h => False.elim (Nat.succ_ne_zero _ h), fun _ => rfl⟩
    obtain ⟨c,hs⟩ := jointUniform.surjective _ ok
    let w := (π r).pair c ((π r).advc ⟨0,hn⟩)
    have hk : custKey 1 (guessKeys 1 w) 0 = [0] := by
      change (jointSampler ((π r).chal w)).1 = _
      rw [show (π r).chal w = c from (π r).chal_pair .., hs]
    refine ⟨w,submitAll_sign_unsafe singletonTable (permitInput dg) (custKey 1 (guessKeys 1 w))
      S (fun _ => ()) 0 () 2 [[0]] _ [] (by decide)
      (by rw [CertCustodyState.init.public_eqs])
      (by rw [CertCustodyState.init.public_eqs]; intro h; cases h) (.inl ?_)⟩
    rw [permitInput.public_eqs, hk]
    exact List.mem_cons_self
  · have hb := certCustody_adaptive_unsafe_release_bound
      (nC := fun _ => jointCard) (nA := fun _ => partyCoinCard jointCard 1)
      (εColl := Spec.RatBound.zero) hn S 0 () toothQuorum 2 singletonTable
      dg 0 (fun _ => rfl) 1 1 (singletonTable_prfHard 1 3 (Within 3)) π (fun _ => jointSampler)
      (fun _ => jointUniform) (guessKeys 1) (fun _ _ => ()) (fun _ => jointAdv) (fun _ _ => rfl)
      (keyIndependent_product _ _ jointSampler _ jointAdv) (fun _ _ _ => tagForgeDistinguisher_within ..)
      (guessCollision 0)
    exact hb

end Teeth

#print axioms certCustody_adaptive_unsafe_release_bound
#print axioms prfSample_shiftClosed
#print axioms keyIndependent_product
#print axioms singletonTable_prfHard
#print axioms inhabited_certCustody_adaptive
#print axioms certCustody_one_guess_nontrivial

#verify_constructive
  Qsag.Top.certRunStep_approve
  Qsag.Top.certRunStep_submit
  Qsag.Top.certRunStep_corrupt
  Qsag.Top.certRunStep_sign_frame
  Qsag.Top.certRunStep_forgery_origin
  Qsag.Top.certRunStep_forgery_flagged
  Qsag.Top.certRun_nil
  Qsag.Top.certRun_snoc
  Qsag.Top.certWorldOracle_pos
  Qsag.Top.certWorldOracle_neg
  Qsag.Top.certAdaptiveRun_state_eq_certRun
  Qsag.Top.certAdaptiveRun_length_le
  Qsag.Top.certAdaptiveRun_unsafe_release_forgery
  Qsag.Top.encTagCertLayer_claim
  Qsag.Top.encTagCertLayer_valid_iff
  Qsag.Top.encTagCertLayer_issue
  Qsag.Top.encTagCertLayer_permitInput_valid_iff
  Qsag.Top.certApprovers_claim_congr
  Qsag.Top.redCode_within
  Qsag.Top.red_sim
  Qsag.Top.certTagForger_within
  Qsag.Top.certAdaptiveRun_unsafe_release_tag_forgery
  Qsag.Top.certAdaptiveRun_unsafe_release_fresh_forgery_or_collision
  Qsag.Top.certCustody_adaptive_unsafe_release_extract
  Qsag.Top.certCustody_adaptive_unsafe_release_bound
  Qsag.Top.certCustody_tooth_key_revealing_tag_adaptive_unsafe_release
  Qsag.Top.certCustody_tooth_guess_all_tags_unsafe_release
  Qsag.Top.certCustody_tooth_unissued_claim_flagged
  Qsag.Top.keyIndependent_two_keys
  Qsag.Top.prfSample_shiftClosed
  Qsag.Top.partyCoinCard_pos
  Qsag.Top.keyIndependent_product
  Qsag.Top.singletonTable_prfHard
  Qsag.Top.inhabited_certCustody_adaptive
  Qsag.Top.certCustody_one_guess_nontrivial

#verify_inhabited Qsag.Top.certCustody_adaptive_unsafe_release_bound Qsag.Top.inhabited_certCustody_adaptive

#tooth_pair Qsag.Top.certCustody_adaptive_unsafe_release_bound vs
  Qsag.Top.certCustody_tooth_key_revealing_tag_adaptive_unsafe_release
#tooth_pair Qsag.Top.certCustody_adaptive_unsafe_release_bound vs
  Qsag.Top.certCustody_tooth_guess_all_tags_unsafe_release
#tooth_pair Qsag.Top.certRunStep_forgery_origin vs
  Qsag.Top.certCustody_tooth_unissued_claim_flagged

end Qsag.Top
end
