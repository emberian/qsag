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
