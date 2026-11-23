module
/-
# Qsag.Top.CustodyKeyHidingBound — refinement witnesses for the shared services, the PRF
# certificate layer, and the composition of the authenticated-custody bound with `Spec.PrfHard`
# and `Spec.SmDtTcrHard`

**Scope.**

1. `Spec.Refines` witnesses for the three machine equalities of `Qsag.Top.Custody`
   (`rssSharedRelease_refines_reference`, `thresholdServiceShared_refines_ideal`,
   `thresholdDurableShared_refines_ideal`), built with `KeyHidingCustody.refinesOfEq`. Their
   relation is equality of states. Consequences read through the library's refinement interface:
   trace inclusion (`rssSharedRelease_admits_reference_traces`) and prefix equivalence under every
   adaptive environment (`thresholdServiceShared_prefixEquivalent_ideal`,
   `thresholdDurableShared_prefixEquivalent_ideal`). The witnesses carry no more information than
   the equalities they are built from.
2. `prfCertLayer`: a `CustodyCertLayer` whose certificate for a permit is
   `KeyHidingCustody.prfCustodyTag` under the party's key. A forgery event of `certRun` over this
   layer is a submitted certificate that carries the PRF tag of the permit it asserts
   (`prfCertCustody_forgery_carries_prf_tag`); a certificate with any other tag is refused
   (`tooth_prfCertLayer_wrong_tag_rejected`). Unforgeability of the tag after `q` adaptive honest
   tags is `KeyHidingCustody.prfCustodyTag_unforgeable`.
3. `AuthCustodyReductionEmbedding`: the data of a reduction of the two violation events of
   `DistCustody.authMachine` to the tag-forgery experiment under one of `custodians` PRF keys and
   to `Spec.smDtTcrGame`: coin splits, uniform samplers, reduction adversaries in the assumed
   classes, and the two per-coin implications `extract_ack`, `extract_wal`.
   Given an embedding, `Spec.PrfHard` and `Spec.SmDtTcrHard`:
   * `AuthCustodyReductionEmbedding.violation_probabilities_prf_tcr_bound` bounds the two
     right-hand probabilities of `authenticatedCustody_unsafe_release_le_violations`;
   * `AuthCustodyReductionEmbedding.unsafe_release_prf_tcr_bound`:
     `Pr[unsafe release] ≤ custodians * (εPrf + 256 ^ (-outLen)) + εTcr`.
   Both are conditional on the embedding.

**Remaining reduction obligations.** An authenticated deployment must supply the coin
maps, sampler laws and extraction proofs for its acknowledgment and WAL events. The public
challenger equations simplify the target side of those proofs. The certificate-world freshness
bookkeeping must also connect a fresh submission to the adaptive tag experiment. The schedule
`adv` is a function of the coin. The embedding supplies the reduction adversaries `advTag`
and `advT`.
-/

public import Qsag.Top.Custody
public import Qsag.Custody.KeyHidingAuthCustodyBound
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Top

open scoped Qsag.Spec
open Qsag.Spec Qsag.KeyHidingCustody

set_option autoImplicit false

/-! ## 1. `Spec.Refines` witnesses for the machine equalities -/

/-- The shared-evaluation RSS release machine refines the reference release machine, through the
    identity relation on the WAL latch state. -/
def rssSharedRelease_refines_reference (p : Qsag.RssProduction.Profile) :
    rssSharedReleaseMachine p ⊑ rssReferenceReleaseMachine p :=
  refinesOfEq (rssSharedReleaseMachine_eq_reference p)

theorem rssSharedRelease_refines_reference_rel (p : Qsag.RssProduction.Profile)
    (w w' : Qsag.WalLatchState) :
    (rssSharedRelease_refines_reference p).Rel w w' ↔ w = w' := by
  unfold rssSharedRelease_refines_reference
  exact refinesOfEq_rel _ w w'

/-- Trace inclusion obtained from the packaged witness through
    `Spec.Refines.preserve_admitsTrace`. -/
theorem rssSharedRelease_admits_reference_traces (p : Qsag.RssProduction.Profile)
    {tr : List (Qsag.SessionScheduleReq × Except Qsag.RssProduction.Failure (List UInt8))}
    (hAdmits : (rssSharedReleaseMachine p).AdmitsTrace tr) :
    (rssReferenceReleaseMachine p).AdmitsTrace tr :=
  (rssSharedRelease_refines_reference p).preserve_admitsTrace hAdmits

/-- From one WAL latch state the two release machines give the same output and the same next
    state on every request. -/
theorem rssSharedRelease_runStep_eq_reference (p : Qsag.RssProduction.Profile)
    (w : Qsag.WalLatchState) (req : Qsag.SessionScheduleReq) :
    ((rssSharedReleaseMachine p).runStep w req).2 =
        ((rssReferenceReleaseMachine p).runStep w req).2 ∧
      ((rssSharedReleaseMachine p).runStep w req).1 =
        ((rssReferenceReleaseMachine p).runStep w req).1 :=
  refinesOfEq_runStep (rssSharedReleaseMachine_eq_reference p) w req

/-- The shared interactive threshold service, started in its initial state, refines the ideal
    service started in the same state. -/
def thresholdServiceShared_refines_ideal (c : Qsag.ThresholdIdealService.Config) :
    Machine.ofInteractive (fun s => s = Qsag.ThresholdIdealService.initial c)
        (Qsag.ThresholdIdealService.shared c) ⊑
      Machine.ofInteractive (fun s => s = Qsag.ThresholdIdealService.initial c)
        (Qsag.ThresholdIdealService.ideal c) :=
  refinesOfEq (congrArg
    (Machine.ofInteractive (fun s => s = Qsag.ThresholdIdealService.initial c))
    (thresholdServiceShared_eq_ideal c))

/-- Through `Spec.Refines.toInteractivePrefixEquivalent`: from the initial state the shared and
    ideal services give every adaptive environment the same view at every horizon. -/
theorem thresholdServiceShared_prefixEquivalent_ideal (c : Qsag.ThresholdIdealService.Config) :
    Qsag.InteractiveService.PrefixEquivalent (Qsag.ThresholdIdealService.shared c)
      (Qsag.ThresholdIdealService.ideal c) (Qsag.ThresholdIdealService.initial c)
      (Qsag.ThresholdIdealService.initial c) := by
  have h := (thresholdServiceShared_refines_ideal c).toInteractivePrefixEquivalent
    (c₀ := Qsag.ThresholdIdealService.initial c) rfl
  have hAbs : (thresholdServiceShared_refines_ideal c).absInit
      (Qsag.ThresholdIdealService.initial c) = Qsag.ThresholdIdealService.initial c := by
    unfold thresholdServiceShared_refines_ideal
    exact refinesOfEq_absInit _ _
  rw [hAbs] at h
  exact h

/-- The shared durable threshold service refines the ideal durable service. -/
def thresholdDurableShared_refines_ideal (c : Qsag.ThresholdIdealService.Config) :
    Machine.ofInteractive (fun s => s = Qsag.ThresholdIdealDurableService.initial)
        (Qsag.ThresholdIdealDurableService.shared c) ⊑
      Machine.ofInteractive (fun s => s = Qsag.ThresholdIdealDurableService.initial)
        (Qsag.ThresholdIdealDurableService.ideal c) :=
  refinesOfEq (congrArg
    (Machine.ofInteractive (fun s => s = Qsag.ThresholdIdealDurableService.initial))
    (thresholdDurableShared_eq_ideal c))

theorem thresholdDurableShared_prefixEquivalent_ideal (c : Qsag.ThresholdIdealService.Config) :
    Qsag.InteractiveService.PrefixEquivalent (Qsag.ThresholdIdealDurableService.shared c)
      (Qsag.ThresholdIdealDurableService.ideal c) Qsag.ThresholdIdealDurableService.initial
      Qsag.ThresholdIdealDurableService.initial := by
  have h := (thresholdDurableShared_refines_ideal c).toInteractivePrefixEquivalent
    (c₀ := Qsag.ThresholdIdealDurableService.initial) rfl
  have hAbs : (thresholdDurableShared_refines_ideal c).absInit
      Qsag.ThresholdIdealDurableService.initial = Qsag.ThresholdIdealDurableService.initial := by
    unfold thresholdDurableShared_refines_ideal
    exact refinesOfEq_absInit _ _
  rw [hAbs] at h
  exact h

/-! ## 2. The PRF certificate layer -/

/-- Certificate layer with key-hiding tags: party `p`'s certificate for a permit is the permit
    with `prfCustodyTag prf dg (key p)` of it. The coordinator recomputes the tag. -/
def prfCertLayer (prf : Spec.Bytes → Spec.Bytes → Spec.Bytes) (dg : Spec.Bytes → Spec.Bytes) (key : Nat → Spec.Bytes) :
    CustodyCertLayer (Spec.Bytes × CustodyApproval) where
  claim c := c.2
  valid c := decide (c.1 = prfCustodyTag prf dg (key c.2.party) c.2)
  issue p dep i := (prfCustodyTag prf dg (key p) (CustodyApproval.mk p dep i),
    CustodyApproval.mk p dep i)
  issue_valid _ _ _ := decide_eq_true rfl
  issue_claim _ _ _ := rfl

theorem prfCertLayer_valid_iff (prf : Spec.Bytes → Spec.Bytes → Spec.Bytes) (dg : Spec.Bytes → Spec.Bytes)
    (key : Nat → Spec.Bytes) (c : Spec.Bytes × CustodyApproval) :
    (prfCertLayer prf dg key).valid c = true ↔
      c.1 = prfCustodyTag prf dg (key c.2.party) c.2 := by
  unfold prfCertLayer
  exact decide_eq_true_iff

theorem prfCertLayer_issue (prf : Spec.Bytes → Spec.Bytes → Spec.Bytes) (dg : Spec.Bytes → Spec.Bytes)
    (key : Nat → Spec.Bytes) (p dep : Nat) (i : CustodyIntent) :
    (prfCertLayer prf dg key).issue p dep i =
      (prfCustodyTag prf dg (key p) (CustodyApproval.mk p dep i), CustodyApproval.mk p dep i) := by
  unfold prfCertLayer
  rfl

/-- **A forgery event of the certificate world over `prfCertLayer` is a submitted certificate
    carrying the PRF tag of its permit.** By `certRun_forgery_submitted`. -/
theorem prfCertCustody_forgery_carries_prf_tag {PK D Sig : Type} [DecidableEq D]
    (prf : Spec.Bytes → Spec.Bytes → Spec.Bytes) (dg : Spec.Bytes → Spec.Bytes) (key : Nat → Spec.Bytes)
    (S : CustodyDigestScheme D) (oracleSign : D → Sig)
    (dep₀ : Nat) (pk₀ : PK) (quorum₀ : CustodyQuorumProfile)
    (inps : List (CertCustodyInput (Spec.Bytes × CustodyApproval)))
    {x : Spec.Bytes × CustodyApproval}
    (hx : x ∈ (certRun (prfCertLayer prf dg key) S oracleSign dep₀ pk₀ quorum₀ inps).forgeries) :
    CertCustodyInput.submit x ∈ inps ∧ x.1 = prfCustodyTag prf dg (key x.2.party) x.2 := by
  obtain ⟨hIn, hValid⟩ := certRun_forgery_submitted (prfCertLayer prf dg key) S oracleSign
    dep₀ pk₀ quorum₀ inps hx
  exact ⟨hIn, (prfCertLayer_valid_iff prf dg key x).mp hValid⟩

/-- A certificate whose tag is not the PRF tag of its permit is not valid. -/
theorem tooth_prfCertLayer_wrong_tag_rejected (prf : Spec.Bytes → Spec.Bytes → Spec.Bytes) (dg : Spec.Bytes → Spec.Bytes)
    (key : Nat → Spec.Bytes) (c : Spec.Bytes × CustodyApproval)
    (hNe : c.1 ≠ prfCustodyTag prf dg (key c.2.party) c.2) :
    ¬ ((prfCertLayer prf dg key).valid c = true) :=
  fun h => hNe ((prfCertLayer_valid_iff prf dg key c).mp h)

/-! ## 3. The authenticated custodian network under `Spec.PrfHard` and `Spec.SmDtTcrHard` -/

/-- **Reduction embedding for the authenticated custodian network.** For the coin-indexed
    deployment `dep` and schedule `adv`:

    * for each of `custodians` PRF keys, a coin split with the key (and the independent random
      function of the PRF experiment) on the challenger coordinate, and a tag-forgery adversary
      on the other coordinate whose forgery distinguisher lies in the class `𝒜P`;
    * one `SM-DT-TCR` experiment for a tweakable hash `th` with a uniform seed on the challenger
      coordinate of its split and an adversary in `𝒜T`;
    * `extract_ack`: on every coin on which the run flags an acknowledgement violation, one of
      the tag-forgery experiments or the `SM-DT-TCR` experiment is won;
    * `extract_wal`: on every coin on which the run flags a WAL violation, the `SM-DT-TCR`
      experiment is won.

    The two implications are the simulation obligations of the reduction. -/
structure AuthCustodyReductionEmbedding {F C PK D Sig : Type}
    [Qsag.LawfulField F] [DecidableEq F] [DecidableEq C] [DecidableEq D]
    {N : Nat} (hN : 0 < N)
    (dep : Fin N → Qsag.DistCustody.AuthDeployment F C PK D Sig)
    (adv : (ω : Fin N) → List (Qsag.DistCustody.AuthTurn F (dep ω).core.quorum.numParties)) :
    Type 1 where
  custodians : Nat
  Msg : Type
  enc : Msg → Spec.Bytes
  prf : Spec.Bytes → Spec.Bytes → Spec.Bytes
  keyLen : Nat
  inLen : Nat
  outLen : Nat
  qTag : Nat
  𝒜P : Code byteOracleIface Bool → Prop
  nCp : Fin custodians → Nat
  nAp : Fin custodians → Nat
  πp : (p : Fin custodians) → CoinSplit N (nCp p) (nAp p)
  sample : (p : Fin custodians) → Fin (nCp p) → Spec.Bytes × (Spec.Bytes → Spec.Bytes)
  hSample : ∀ p : Fin custodians, UniformOn (PrfSampleOk keyLen inLen outLen) (sample p)
  advTag : (p : Fin custodians) → Fin (nAp p) → Code (tagIface Msg) (Msg × Spec.Bytes)
  hAdvTag : ∀ (p : Fin custodians) (a : Fin (nAp p)),
    𝒜P (tagForgeDistinguisher enc qTag inLen (advTag p a))
  th : Spec.Bytes → Spec.Bytes → Spec.Bytes → Spec.Bytes
  seedLen : Nat
  qTcr : Nat
  𝒜T : Code targetIface TargetBreak → Prop
  nCt : Nat
  nAt : Nat
  πt : CoinSplit N nCt nAt
  seed : Fin nCt → Spec.Bytes
  hSeed : UniformOn (fun s : Spec.Bytes => s.length = seedLen) seed
  advT : Fin nAt → Code targetIface TargetBreak
  hAdvT : ∀ a : Fin nAt, 𝒜T (advT a)
  extract_ack : ∀ ω : Fin N,
    (Qsag.DistCustody.authRun (dep ω) (Qsag.DistCustody.authAckViolation (dep ω))
      (Qsag.DistCustody.AuthState.init (dep ω)) (adv ω)).2 = true →
    (∃ p : Fin custodians,
      (encFreshTagGame hN enc qTag inLen (fun ω => prf (sample p ((πp p).chal ω)).1)
        (fun ω => advTag p ((πp p).advc ω))).win ω = true) ∨
    (smDtTcrGame hN th qTcr (fun ω => seed (πt.chal ω)) (fun ω => advT (πt.advc ω))).win ω = true
  extract_wal : ∀ ω : Fin N,
    (Qsag.DistCustody.authRun (dep ω) (Qsag.DistCustody.authWalViolation (dep ω))
      (Qsag.DistCustody.AuthState.init (dep ω)) (adv ω)).2 = true →
    (smDtTcrGame hN th qTcr (fun ω => seed (πt.chal ω)) (fun ω => advT (πt.advc ω))).win ω = true

section AuthBound

variable {F C PK D Sig : Type}
  [Qsag.LawfulField F] [DecidableEq F] [DecidableEq C] [DecidableEq D]

/-- An event whose coins are forgeries under one of the embedding's keys or `SM-DT-TCR` wins has
    probability at most `custodians * (εPrf + 256 ^ (-outLen)) + εTcr`. -/
private theorem embedding_event_bound {N : Nat} {hN : 0 < N}
    {dep : Fin N → Qsag.DistCustody.AuthDeployment F C PK D Sig}
    {adv : (ω : Fin N) → List (Qsag.DistCustody.AuthTurn F (dep ω).core.quorum.numParties)}
    (E : AuthCustodyReductionEmbedding hN dep adv)
    {εPrf εTcr : Spec.RatBound}
    (hPrf : PrfHard E.𝒜P E.prf E.keyLen E.inLen E.outLen (E.qTag + 1) εPrf)
    (hTcr : SmDtTcrHard E.𝒜T E.th E.seedLen E.qTcr εTcr)
    (G : FinGame N)
    (hG : ∀ ω : Fin N, G.win ω = true →
      (∃ p : Fin E.custodians,
        (encFreshTagGame hN E.enc E.qTag E.inLen (fun ω => E.prf (E.sample p ((E.πp p).chal ω)).1)
          (fun ω => E.advTag p ((E.πp p).advc ω))).win ω = true) ∨
      (smDtTcrGame hN E.th E.qTcr (fun ω => E.seed (E.πt.chal ω))
        (fun ω => E.advT (E.πt.advc ω))).win ω = true) :
    GameBound G.winProb
      (((εPrf.add (tagGuessBound E.outLen)).scale E.custodians).add εTcr) := by
  let T : FinGame N := smDtTcrGame hN E.th E.qTcr (fun ω => E.seed (E.πt.chal ω))
    (fun ω => E.advT (E.πt.advc ω))
  let A : FinGame N := ⟨hN, fun ω => G.win ω && !T.win ω⟩
  have hSplit : ∀ ω : Fin N, G.win ω = true → A.win ω = true ∨ T.win ω = true := by
    intro ω hg
    cases ht : T.win ω with
    | true => exact .inr rfl
    | false =>
      refine .inl ?_
      show (G.win ω && !T.win ω) = true
      rw [hg, ht]
      rfl
  have hA : ∀ ω : Fin N, A.win ω = true → ∃ p : Fin E.custodians,
      (encFreshTagGame hN E.enc E.qTag E.inLen (fun ω => E.prf (E.sample p ((E.πp p).chal ω)).1)
        (fun ω => E.advTag p ((E.πp p).advc ω))).win ω = true := by
    intro ω ha
    have ha' : (G.win ω && !T.win ω) = true := ha
    obtain ⟨hg, hnt⟩ := Bool.and_eq_true_iff.mp ha'
    rcases hG ω hg with h | h
    · exact h
    · have ht : T.win ω = true := h
      rw [ht] at hnt
      exact absurd hnt Bool.false_ne_true
  exact GameBound.trans (event_le_two_reductions G A T hSplit)
    (Spec.RatBound.add_le_add
      (custodianKeys_forgery_union_bound hN E.enc E.qTag E.inLen E.prf E.keyLen E.outLen hPrf
        E.nCp E.nAp E.πp E.sample E.hSample E.advTag E.hAdvTag A hA)
      (hTcr N E.nCt E.nAt hN E.πt E.seed E.hSeed E.advT E.hAdvT))

/-- **The two violation probabilities of `authenticatedCustody_unsafe_release_le_violations`,
    bounded.** Given a reduction embedding, `Spec.PrfHard` for its PRF with `qTag + 1` queries and
    `Spec.SmDtTcrHard` for its tweakable hash: the acknowledgement-violation event has probability
    at most `custodians * (εPrf + 256 ^ (-outLen)) + εTcr` and the WAL-violation event at most
    `εTcr`. These are the hypotheses `hAck`, `hWal` of
    `authenticatedCustody_unsafe_release_bound`. -/
theorem AuthCustodyReductionEmbedding.violation_probabilities_prf_tcr_bound
    {N : Nat} {hN : 0 < N}
    {dep : Fin N → Qsag.DistCustody.AuthDeployment F C PK D Sig}
    {adv : (ω : Fin N) → List (Qsag.DistCustody.AuthTurn F (dep ω).core.quorum.numParties)}
    (E : AuthCustodyReductionEmbedding hN dep adv)
    {εPrf εTcr : Spec.RatBound}
    (hPrf : PrfHard E.𝒜P E.prf E.keyLen E.inLen E.outLen (E.qTag + 1) εPrf)
    (hTcr : SmDtTcrHard E.𝒜T E.th E.seedLen E.qTcr εTcr) :
    GameBound
      (FinGame.mk hN (fun ω =>
        (Qsag.DistCustody.authRun (dep ω) (Qsag.DistCustody.authAckViolation (dep ω))
          (Qsag.DistCustody.AuthState.init (dep ω)) (adv ω)).2)).winProb
      (((εPrf.add (tagGuessBound E.outLen)).scale E.custodians).add εTcr) ∧
    GameBound
      (FinGame.mk hN (fun ω =>
        (Qsag.DistCustody.authRun (dep ω) (Qsag.DistCustody.authWalViolation (dep ω))
          (Qsag.DistCustody.AuthState.init (dep ω)) (adv ω)).2)).winProb
      εTcr :=
  ⟨embedding_event_bound E hPrf hTcr _ (fun ω h => E.extract_ack ω h),
    GameBound.trans
      (event_le_reduction_win _
        (smDtTcrGame hN E.th E.qTcr (fun ω => E.seed (E.πt.chal ω))
          (fun ω => E.advT (E.πt.advc ω)))
        (fun ω h => E.extract_wal ω h))
      (hTcr N E.nCt E.nAt hN E.πt E.seed E.hSeed E.advT E.hAdvT)⟩

/-- **`Pr[unsafe release] ≤ custodians * (εPrf + 256 ^ (-outLen)) + εTcr`, given a reduction
    embedding.** Over a finite coin space that determines the deployment and the schedule against
    the unguarded `DistCustody.authMachine`, and given a reduction embedding of the two violation
    events, `Spec.PrfHard` for the embedding's PRF against `qTag + 1` queries and
    `Spec.SmDtTcrHard` for its tweakable hash: the coordinator's WAL holds a release no enrolled
    custodian approved with probability at most the stated bound. The `256 ^ (-outLen)` term
    bounds the forgery probability against a random function
    (`KeyHidingCustody.encFreshTagGame_random_function_bound`). The ideal sample set satisfies the required closure by
    `KeyHidingCustody.prfSampleOk_shiftClosed`.

    An unsafe release needs a violation (`DistCustody.authRun_unsafe_release_violation`), a
    violation is one of the two kinds (`DistCustody.authRun_violation_split`), and the embedding
    maps both kinds to the experiments; a coin is charged to the `SM-DT-TCR` experiment once. -/
theorem AuthCustodyReductionEmbedding.unsafe_release_prf_tcr_bound
    {N : Nat} {hN : 0 < N}
    {dep : Fin N → Qsag.DistCustody.AuthDeployment F C PK D Sig}
    {adv : (ω : Fin N) → List (Qsag.DistCustody.AuthTurn F (dep ω).core.quorum.numParties)}
    (E : AuthCustodyReductionEmbedding hN dep adv)
    (hWf : ∀ ω, (dep ω).WellFormed)
    {εPrf εTcr : Spec.RatBound}
    (hPrf : PrfHard E.𝒜P E.prf E.keyLen E.inLen E.outLen (E.qTag + 1) εPrf)
    (hTcr : SmDtTcrHard E.𝒜T E.th E.seedLen E.qTcr εTcr) :
    GameBound
      (FinGame.mk hN (fun ω => Qsag.DistCustody.authUnsafeRelease (dep ω)
        (Qsag.DistCustody.authRun (dep ω) (Qsag.DistCustody.authViolation (dep ω))
          (Qsag.DistCustody.AuthState.init (dep ω)) (adv ω)).1)).winProb
      (((εPrf.add (tagGuessBound E.outLen)).scale E.custodians).add εTcr) :=
  embedding_event_bound E hPrf hTcr _ (fun ω hU => by
    have hV := Qsag.DistCustody.authRun_unsafe_release_violation (dep ω) (hWf ω) (adv ω) hU
    rw [Qsag.DistCustody.authRun_violation_split] at hV
    rcases Bool.or_eq_true_iff.mp hV with h | h
    · exact E.extract_ack ω h
    · exact .inr (E.extract_wal ω h))

end AuthBound

#verify_constructive
  Qsag.Top.rssSharedRelease_refines_reference_rel
  Qsag.Top.rssSharedRelease_admits_reference_traces
  Qsag.Top.rssSharedRelease_runStep_eq_reference
  Qsag.Top.thresholdServiceShared_prefixEquivalent_ideal
  Qsag.Top.thresholdDurableShared_prefixEquivalent_ideal
  Qsag.Top.prfCertLayer_valid_iff
  Qsag.Top.prfCertLayer_issue
  Qsag.Top.prfCertCustody_forgery_carries_prf_tag
  Qsag.Top.tooth_prfCertLayer_wrong_tag_rejected
  Qsag.Top.AuthCustodyReductionEmbedding.violation_probabilities_prf_tcr_bound
  Qsag.Top.AuthCustodyReductionEmbedding.unsafe_release_prf_tcr_bound

#tooth_pair Qsag.Top.prfCertCustody_forgery_carries_prf_tag vs
  Qsag.Top.tooth_prfCertLayer_wrong_tag_rejected

#verify_constructive
  Qsag.KeyHidingCustody.tagForge_prf_hop
  Qsag.KeyHidingCustody.encFreshTagGame_random_function_bound
  Qsag.KeyHidingCustody.prfCustodyTag_unforgeable
  Qsag.KeyHidingCustody.custodianKeys_forgery_union_bound
  Qsag.KeyHidingCustody.prfTag_view_key_hiding

#verify_kernel
  Qsag.Top.rssSharedRelease_refines_reference
  Qsag.Top.thresholdServiceShared_refines_ideal
  Qsag.Top.thresholdDurableShared_refines_ideal

end Qsag.Top
end
