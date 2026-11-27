module
public import Qsag.Protocol.Threshold.SacrificeFreezeSample

public import Qsag.Spec.Primitives
public import Qsag.Oracle.SpecRatBridges
public import Qsag.Spec.Parameters
public import Qsag.Spec.Refines
public import Qsag.Spec.GameBound
public import Qsag.Spec.Assumptions
public import Qsag.Spec.IdealCred
public import Qsag.Protocol.Threshold.LatticePreprocessingFull
public import Qsag.Protocol.Threshold.RlweExtraction
public import Qsag.Math.TapRowParityBias
public import Qsag.Math.Lattices
public import Qsag.Protocol.Threshold.DensePcgTaps
public import Qsag.Protocol.Threshold.ThresholdMlDsaSecurity
public import Qsag.Protocol.Threshold.ThresholdMlDsaAndToprf
public import Qsag.Protocol.Credentials.BlindVcCollisionFinder
public import Qsag.Protocol.Credentials.RepetitionCutAndChoose
public import Qsag.Protocol.Credentials.AdvancedMpcAndCreds
public import Qsag.Protocol.Credentials.BlindVcQromSecurity
public import Qsag.Protocol.Credentials.ToprfSpdzArithmeticRefinement
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Top

set_option autoImplicit false

/-! ## 3. Threshold FIPS-204 `ML-DSA` HVZK Plateau, `𝔽_{q^6}` Sacrifice, and Multi-Key PRSS Hybrid -/

/-- **Coin-After-Freeze `SacrificeFreezeSample` ↔ `rssSacrificedSignStep` Composition
    (`threshold_mldsa_frozen_sacrifice_sign_step_soundness`)**:
    Composes `SacrificeFreezeSample` (`FrozenChallenge.vectors SacrificeFreeze.fq204Elems 6`,
    freezing the prover's `(inp, T)` before sampling the 6-coordinate `Ext6Fq204` challenge) with
    threshold FIPS-204 `rssSacrificedSignStep` (`rssSacrificedSignStep_mldsaQ6_frozen_soundness`),
    proving that any forged multiplication product is accepted on at most `1` of `mldsaQ ^ 6`
    challenges (`< 2^-137`). -/
theorem threshold_mldsa_frozen_sacrifice_sign_step_soundness
    (chalHash : List UInt8 → (Fin 4 → Qsag.NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Qsag.Poly256)
    (st : Qsag.RssMlDsaSignerState)
    (A : Qsag.FrozenChallenge.Adversary
      (Qsag.RssMlDsaAttemptInput × Qsag.RssSacrificeTranscript204) Qsag.Fq204)
    (hForged : (A.commit []).1.products ≠
      Qsag.rssComputeProducts chalHash sampleInBall st (A.commit []).1.mu (A.commit []).1.ySubsets) :
    Qsag.FrozenChallenge.countIf
      (fun chis => Qsag.rssSignStepAcceptsSacrifice chalHash sampleInBall st
        (A.commit []).1 (Qsag.ext6OfList chis) (A.commit []).2)
      (Qsag.FrozenChallenge.vectors Qsag.SacrificeFreeze.fq204Elems 6) ≤ 1 ∧
    Qsag.FrozenChallenge.countIf
      (fun chis => Qsag.rssSignStepAcceptsSacrifice chalHash sampleInBall st
        (A.commit []).1 (Qsag.ext6OfList chis) (A.commit []).2)
      (Qsag.FrozenChallenge.vectors Qsag.SacrificeFreeze.fq204Elems 6) * 2 ^ 137 <
      Qsag.mldsaQ ^ 6 ∧
    (Qsag.FrozenChallenge.vectors Qsag.SacrificeFreeze.fq204Elems 6).length = Qsag.mldsaQ ^ 6 :=
  Qsag.rssSacrificedSignStep_mldsaQ6_frozen_soundness chalHash sampleInBall st A hForged

/-! ## 4. `PiBlindVc` Selective-Disclosure Soundness & Fiat–Shamir Collision Extraction -/

/-- Interactive soundness at the credential profile's repetition count. The checker
    supplies the algebraic soundness premise for independent folding challenges and
    evaluation points. The bound counts accepted challenge triples. -/
theorem credential_sd_limbo256_tau33_interactive_soundness {C G B1 R B2 : Type}
    (K : Qsag.CutAndChoose.DefectChecker C G B1 R B2) (P : Qsag.CutAndChoose.Prover C G B1 R B2)
    (Gs : List G) (Rs : List R) (dG : Nat)
    (hS : K.AlgebraicSound P.commit Gs Rs dG Qsag.CutAndChoose.limboEvalDegree)
    (hRs : Rs.length = Qsag.CutAndChoose.fp5NonzeroCount) (hG : dG * 2 ^ 300 ≤ Gs.length)
    (hGpos : 0 < Gs.length) :
    Qsag.CutAndChoose.winCount K.toChecker Qsag.Spec.pqCredentialProfile.sdRepsQuantum P Gs Rs
        Qsag.CutAndChoose.limboParties * 2 ^ 263 <
      Qsag.CutAndChoose.challengeCount Qsag.Spec.pqCredentialProfile.sdRepsQuantum Gs Rs
        Qsag.CutAndChoose.limboParties := by
  have reps : Qsag.credentialSdRepetitions = Qsag.Spec.pqCredentialProfile.sdRepsQuantum :=
    Qsag.credentialSdRepetitions_eq.trans (by decide)
  rw [← reps]
  exact Qsag.CutAndChoose.limbo256_tau33_defect_check_soundness K P Gs Rs dG hS hRs hG hGpos

/-! ## 5. Refinement Obligation for a Concrete Credential Service -/

structure CredentialImplementation {O S W : Type} (Attr : Type) [DecidableEq Attr]
    (cfg : Qsag.Spec.IdealCredConfig O)
    (M : Qsag.Spec.Machine S (Qsag.Spec.CredPort × W) (Qsag.Spec.IdealCredOutput O)) : Type where
  Rel : S → Qsag.Spec.IdealCredState Attr O → Prop
  extract : S → Qsag.Spec.CredPort → W → Option (Qsag.Spec.CredCommand Attr)
  init_ok : ∀ {c₀ : S}, M.Init c₀ → Rel c₀ (Qsag.Spec.IdealCredState.empty cfg)
  accept_ok : ∀ {c c' : S} {a : Qsag.Spec.IdealCredState Attr O} {sender : Qsag.Spec.CredPort}
    {w : W} {out : Qsag.Spec.IdealCredOutput O},
    Rel c a → M.step c (sender, w) = some (c', out) →
    ∃ (cmd : Qsag.Spec.CredCommand Attr) (a' : Qsag.Spec.IdealCredState Attr O),
      extract c sender w = some cmd ∧
      (Qsag.Spec.idealCredMachine cfg).step a (sender, cmd) = some (a', out) ∧ Rel c' a'
  reject_ok : ∀ {c : S} {a : Qsag.Spec.IdealCredState Attr O} {x : Qsag.Spec.CredPort × W},
    Rel c a → M.step c x = none → Rel (M.errStep c x) a

/-- What a run shows at the interface: per step, the delivering sender and the output. -/
def credSenderView {O W : Type}
    (tr : List ((Qsag.Spec.CredPort × W) × Qsag.Spec.IdealCredOutput O)) :
    List (Qsag.Spec.CredPort × Qsag.Spec.IdealCredOutput O) :=
  tr.map (fun e => (e.1.1, e.2))

private theorem credSenderView_mem {O W W' : Type}
    {aTr : List ((Qsag.Spec.CredPort × W') × Qsag.Spec.IdealCredOutput O)}
    {tr : List ((Qsag.Spec.CredPort × W) × Qsag.Spec.IdealCredOutput O)}
    (hView : credSenderView aTr = credSenderView tr)
    {p : Qsag.Spec.CredPort} {cmd : W'} {out : Qsag.Spec.IdealCredOutput O}
    (hMem : ((p, cmd), out) ∈ aTr) : ∃ w : W, ((p, w), out) ∈ tr := by
  have h1 : (p, out) ∈ credSenderView aTr := by
    unfold credSenderView
    exact List.mem_map.mpr ⟨((p, cmd), out), hMem, rfl⟩
  rw [hView] at h1
  unfold credSenderView at h1
  obtain ⟨e, he, hfe⟩ := List.mem_map.mp h1
  obtain ⟨⟨q, w⟩, o⟩ := e
  obtain ⟨hq, ho⟩ := Prod.mk.inj hfe
  have hq' : q = p := hq
  have ho' : o = out := ho
  subst hq'
  subst ho'
  exact ⟨w, he⟩

/-- Every run of an implementation from an initial state is matched by a run of the ideal machine
    from its initial state, with the same sender and the same output at every step, ending in a
    related state. -/
theorem CredentialImplementation.abstract_run {Attr O S W : Type} [DecidableEq Attr]
    {cfg : Qsag.Spec.IdealCredConfig O}
    {M : Qsag.Spec.Machine S (Qsag.Spec.CredPort × W) (Qsag.Spec.IdealCredOutput O)}
    (impl : CredentialImplementation Attr cfg M)
    {c₀ c : S} {tr : List ((Qsag.Spec.CredPort × W) × Qsag.Spec.IdealCredOutput O)}
    (hInit : M.Init c₀) (hTrace : M.ValidTrace c₀ tr c) :
    ∃ (a : Qsag.Spec.IdealCredState Attr O)
      (aTr : List (Qsag.Spec.IdealCredInput Attr × Qsag.Spec.IdealCredOutput O)),
      impl.Rel c a ∧
      (Qsag.Spec.idealCredMachine cfg).ValidTrace (Qsag.Spec.IdealCredState.empty cfg) aTr a ∧
      credSenderView aTr = credSenderView tr := by
  have hGen : ∀ {c₁ c₂ : S} {t : List ((Qsag.Spec.CredPort × W) × Qsag.Spec.IdealCredOutput O)},
      M.ValidTrace c₁ t c₂ → ∀ a₁ : Qsag.Spec.IdealCredState Attr O, impl.Rel c₁ a₁ →
      ∃ (a : Qsag.Spec.IdealCredState Attr O)
        (aTr : List (Qsag.Spec.IdealCredInput Attr × Qsag.Spec.IdealCredOutput O)),
        impl.Rel c₂ a ∧ (Qsag.Spec.idealCredMachine cfg).ValidTrace a₁ aTr a ∧
        credSenderView aTr = credSenderView t := by
    intro c₁ c₂ t hT
    induction hT with
    | nil s => exact fun a₁ hRel => ⟨a₁, [], hRel, .nil a₁, rfl⟩
    | @accept s s' sf inp out rest hStep _ ih =>
      intro a₁ hRel
      obtain ⟨sender, w⟩ := inp
      obtain ⟨cmd, a', _, hStepA, hRel'⟩ := impl.accept_ok hRel hStep
      obtain ⟨a, aTr, hRelF, hTrA, hOut⟩ := ih a' hRel'
      refine ⟨a, ((sender, cmd), out) :: aTr, hRelF, .accept hStepA hTrA, ?_⟩
      unfold credSenderView at hOut ⊢
      simp only [List.map_cons, hOut]
    | reject x hNone _ ih =>
      intro a₁ hRel
      exact ih a₁ (impl.reject_ok hRel hNone)
  exact hGen hTrace _ (impl.init_ok hInit)

/-- `a` is an ideal state reached by an ideal run from the initial state that shows the same
    senders and outputs as the service run `tr`, and it is related to the service state `c`.
    Corruption is adaptive in `Spec.idealCredMachine`, so who is corrupt "now" is a fact about
    this state, not about the configuration. -/
def CredentialImplementation.AbstractAt {Attr O S W : Type} [DecidableEq Attr]
    {cfg : Qsag.Spec.IdealCredConfig O}
    {M : Qsag.Spec.Machine S (Qsag.Spec.CredPort × W) (Qsag.Spec.IdealCredOutput O)}
    (impl : CredentialImplementation Attr cfg M)
    (tr : List ((Qsag.Spec.CredPort × W) × Qsag.Spec.IdealCredOutput O)) (c : S)
    (a : Qsag.Spec.IdealCredState Attr O) : Prop :=
  impl.Rel c a ∧
  ∃ aTr : List (Qsag.Spec.IdealCredInput Attr × Qsag.Spec.IdealCredOutput O),
    (Qsag.Spec.idealCredMachine cfg).ValidTrace (Qsag.Spec.IdealCredState.empty cfg) aTr a ∧
    credSenderView aTr = credSenderView tr

/-- **Issuance authentication for an implementation.** If the service answers `.issued credId`
    to a message, then there is an ideal state `a` matching the run in which: the message was
    delivered on the issuer port, or on the adversary port with the issuer corrupt in `a`; and it
    stands for the issuance of a credential with between `1` and `maxAttrs` attributes. -/
theorem credentialImplementation_issuance_authenticated {Attr O S W : Type} [DecidableEq Attr]
    {cfg : Qsag.Spec.IdealCredConfig O}
    {M : Qsag.Spec.Machine S (Qsag.Spec.CredPort × W) (Qsag.Spec.IdealCredOutput O)}
    (impl : CredentialImplementation Attr cfg M)
    {c₀ c c' : S} {tr : List ((Qsag.Spec.CredPort × W) × Qsag.Spec.IdealCredOutput O)}
    {sender : Qsag.Spec.CredPort} {w : W} {credId : Nat}
    (hInit : M.Init c₀) (hTrace : M.ValidTrace c₀ tr c)
    (hAccepted : M.step c (sender, w) = some (c', .issued credId)) :
    ∃ a : Qsag.Spec.IdealCredState Attr O, impl.AbstractAt tr c a ∧
      (sender = Qsag.Spec.CredPort.issuer ∨
        (sender = Qsag.Spec.CredPort.adversary ∧ a.issuerCorrupt = true)) ∧
      ∃ (holder : Nat) (attrs : List Attr) (newRoot : Qsag.Spec.Digest256),
        impl.extract c sender w = some (.issue holder attrs newRoot) ∧
        0 < attrs.length ∧ attrs.length ≤ Qsag.Spec.pqCredentialProfile.maxAttrs := by
  obtain ⟨a, aTr, hRel, hTrA, hView⟩ := impl.abstract_run hInit hTrace
  obtain ⟨cmd, a', hExt, hStepA, _⟩ := impl.accept_ok hRel hAccepted
  obtain ⟨holder, attrs, newRoot, hCmd⟩ := Qsag.Spec.idealCredStep_output_command hStepA
  subst hCmd
  obtain ⟨hPort, hPos, hMax⟩ := Qsag.Spec.idealCredMachine_issuance_authenticated cfg hStepA
  exact ⟨a, ⟨hRel, aTr, hTrA, hView⟩, hPort, holder, attrs, newRoot, hExt, hPos, hMax⟩

/-- **Possession provenance for an implementation.** If the service answers a message with the
    verdict `true`, then there is an ideal state `a` matching the run in which: the message
    stands for a presentation of some credential `credId` by some `holder`; it was delivered on
    that holder's port (or on the adversary port with that holder corrupt in `a`); the statement
    names the configured issuer key; and the run contains a message the service answered
    `.issued credId`, delivered on the issuer port, or on the adversary port with the issuer
    corrupt in `a`. -/
theorem credentialImplementation_presentation_provenance {Attr O S W : Type} [DecidableEq Attr]
    {cfg : Qsag.Spec.IdealCredConfig O}
    {M : Qsag.Spec.Machine S (Qsag.Spec.CredPort × W) (Qsag.Spec.IdealCredOutput O)}
    (impl : CredentialImplementation Attr cfg M)
    {c₀ c c' : S} {tr : List ((Qsag.Spec.CredPort × W) × Qsag.Spec.IdealCredOutput O)}
    {sender : Qsag.Spec.CredPort} {w : W}
    (hInit : M.Init c₀) (hTrace : M.ValidTrace c₀ tr c)
    (hAccepted : M.step c (sender, w) = some (c', .presentationVerdict true)) :
    ∃ a : Qsag.Spec.IdealCredState Attr O, impl.AbstractAt tr c a ∧
      ∃ (holder credId : Nat) (stmt : Qsag.Spec.CredentialStatement Attr),
        impl.extract c sender w = some (.present holder credId stmt) ∧
        (sender = Qsag.Spec.CredPort.holder holder ∨
          (sender = Qsag.Spec.CredPort.adversary ∧ holder ∈ a.corruptHolders)) ∧
        stmt.issuerPk = cfg.issuerPk ∧
        ∃ (issuePort : Qsag.Spec.CredPort) (w₀ : W),
          ((issuePort, w₀), Qsag.Spec.IdealCredOutput.issued credId) ∈ tr ∧
          (issuePort = Qsag.Spec.CredPort.issuer ∨
            (issuePort = Qsag.Spec.CredPort.adversary ∧ a.issuerCorrupt = true)) := by
  obtain ⟨a, aTr, hRel, hTrA, hView⟩ := impl.abstract_run hInit hTrace
  obtain ⟨cmd, a', hExt, hStepA, _⟩ := impl.accept_ok hRel hAccepted
  obtain ⟨holder, credId, stmt, hCmd⟩ := Qsag.Spec.idealCredStep_output_command hStepA
  subst hCmd
  obtain ⟨hPort, hPk, r, _, _, _, _, _, issuePort, hMem, hIssuePort⟩ :=
    Qsag.Spec.idealCredMachine_presentation_provenance cfg rfl hTrA hStepA
  obtain ⟨w₀, hw₀⟩ := credSenderView_mem hView hMem
  exact ⟨a, ⟨hRel, aTr, hTrA, hView⟩, holder, credId, stmt, hExt, hPort, hPk,
    issuePort, w₀, hw₀, hIssuePort⟩

/-- Tooth: if the issuer is not corrupt in any ideal state matching the run, the service never
    answers `.issued` to a message delivered on any port other than the issuer's — in particular
    to one the adversary delivered. -/
theorem credentialImplementation_rejects_foreign_issue {Attr O S W : Type} [DecidableEq Attr]
    {cfg : Qsag.Spec.IdealCredConfig O}
    {M : Qsag.Spec.Machine S (Qsag.Spec.CredPort × W) (Qsag.Spec.IdealCredOutput O)}
    (impl : CredentialImplementation Attr cfg M)
    {c₀ c c' : S} {tr : List ((Qsag.Spec.CredPort × W) × Qsag.Spec.IdealCredOutput O)}
    {sender : Qsag.Spec.CredPort} {w : W} {credId : Nat}
    (hInit : M.Init c₀) (hTrace : M.ValidTrace c₀ tr c)
    (hHonest : ∀ a : Qsag.Spec.IdealCredState Attr O, impl.AbstractAt tr c a →
      a.issuerCorrupt = false)
    (hSender : ¬ (sender = Qsag.Spec.CredPort.issuer)) :
    ¬ (M.step c (sender, w) = some (c', .issued credId)) := by
  intro hAccepted
  obtain ⟨a, hAt, hAuth, _⟩ :=
    credentialImplementation_issuance_authenticated impl hInit hTrace hAccepted
  rcases hAuth with hP | ⟨_, hC⟩
  · exact hSender hP
  · rw [hHonest a hAt] at hC
    cases hC

/-- Tooth: if no holder is corrupt in any ideal state matching the run, the service never
    answers the verdict `true` to a message the adversary delivered. -/
theorem credentialImplementation_rejects_foreign_presentation {Attr O S W : Type}
    [DecidableEq Attr] {cfg : Qsag.Spec.IdealCredConfig O}
    {M : Qsag.Spec.Machine S (Qsag.Spec.CredPort × W) (Qsag.Spec.IdealCredOutput O)}
    (impl : CredentialImplementation Attr cfg M)
    {c₀ c c' : S} {tr : List ((Qsag.Spec.CredPort × W) × Qsag.Spec.IdealCredOutput O)} {w : W}
    (hInit : M.Init c₀) (hTrace : M.ValidTrace c₀ tr c)
    (hHonest : ∀ a : Qsag.Spec.IdealCredState Attr O, impl.AbstractAt tr c a →
      a.corruptHolders = []) :
    ¬ (M.step c (Qsag.Spec.CredPort.adversary, w) = some (c', .presentationVerdict true)) := by
  intro hAccepted
  obtain ⟨a, hAt, holder, _, _, _, hAuth, _⟩ :=
    credentialImplementation_presentation_provenance impl hInit hTrace hAccepted
  rcases hAuth with hP | ⟨_, hC⟩
  · cases hP
  · rw [hHonest a hAt] at hC
    exact nomatch hC

/-- **TOPRF provenance for an implementation.** If every ideal state matching the run has at
    most `toprfMaxCorrupt` corrupt servers and the service answers a message with a TOPRF value,
    then there is such a state `a` in which: the message stands for an evaluation of some ticket
    and input, the value is the keyed-table value of `(keyId, epoch, input)`, and the run
    contains a message delivered on the port of a committee server not corrupt in `a` that the
    service answered `.toprfApproved`. -/
theorem credentialImplementation_toprf_provenance {Attr O S W : Type} [DecidableEq Attr]
    {cfg : Qsag.Spec.IdealCredConfig O}
    {M : Qsag.Spec.Machine S (Qsag.Spec.CredPort × W) (Qsag.Spec.IdealCredOutput O)}
    (impl : CredentialImplementation Attr cfg M)
    {c₀ c c' : S} {tr : List ((Qsag.Spec.CredPort × W) × Qsag.Spec.IdealCredOutput O)}
    {sender : Qsag.Spec.CredPort} {w : W} {v : O}
    (hInit : M.Init c₀) (hTrace : M.ValidTrace c₀ tr c)
    (hCorrupt : ∀ a : Qsag.Spec.IdealCredState Attr O, impl.AbstractAt tr c a →
      a.corruptServerCount ≤ Qsag.Spec.pqCredentialProfile.toprfMaxCorrupt)
    (hAccepted : M.step c (sender, w) = some (c', .toprfEvaluated v)) :
    ∃ a : Qsag.Spec.IdealCredState Attr O, impl.AbstractAt tr c a ∧
      ∃ (t : Qsag.Spec.ToprfTicket) (input : Qsag.Spec.Bytes),
        impl.extract c sender w = some (.evalToprf t input) ∧
        v = cfg.oprf ⟨t.keyId, t.epoch, input⟩ ∧
        ∃ (i : Nat) (w₀ : W),
          i < Qsag.Spec.pqCredentialProfile.toprfServers ∧ i ∉ a.corruptServers ∧
          ((Qsag.Spec.CredPort.server i, w₀), Qsag.Spec.IdealCredOutput.toprfApproved) ∈ tr := by
  obtain ⟨a, aTr, hRel, hTrA, hView⟩ := impl.abstract_run hInit hTrace
  have hAt : impl.AbstractAt tr c a := ⟨hRel, aTr, hTrA, hView⟩
  obtain ⟨cmd, a', hExt, hStepA, _⟩ := impl.accept_ok hRel hAccepted
  obtain ⟨t, input, hCmd⟩ := Qsag.Spec.idealCredStep_output_command hStepA
  subst hCmd
  obtain ⟨hVal, _, i, hi, hHonest, hMem, _⟩ :=
    Qsag.Spec.idealCredMachine_toprf_provenance cfg rfl hTrA (hCorrupt a hAt) hStepA
  obtain ⟨w₀, hw₀⟩ := credSenderView_mem hView hMem
  exact ⟨a, hAt, t, input, hExt, Qsag.Spec.IdealCredOutput.toprfEvaluated.inj hVal, i, w₀, hi,
    hHonest, hw₀⟩

/-! ### The unauthenticated service is not an implementation -/

/-- The port a command claims to come from. -/
def credCommandClaimedPort {Attr : Type} : Qsag.Spec.CredCommand Attr → Qsag.Spec.CredPort
  | .issue _ _ _ => .issuer
  | .advanceEpoch _ _ => .issuer
  | .present h _ _ => .holder h
  | .advanceClock verifier _ => .verifier verifier
  | .issueChallenge verifier _ _ _ => .verifier verifier
  | .approveToprf i _ => .server i
  | .evalToprf _ _ => .client
  | .corrupt _ => .adversary

/-- A service that authenticates nobody: it ignores who delivered a command and runs the ideal
    transition on the port the command claims. Any caller can issue invented attributes and
    present for any holder. -/
@[expose] def unauthenticatedCredService {Attr O : Type} [DecidableEq Attr]
    (cfg : Qsag.Spec.IdealCredConfig O) :
    Qsag.Spec.Machine (Qsag.Spec.IdealCredState Attr O)
      (Qsag.Spec.CredPort × Qsag.Spec.CredCommand Attr) (Qsag.Spec.IdealCredOutput O) where
  Init st := st = Qsag.Spec.IdealCredState.empty cfg
  step st x := Qsag.Spec.idealCredStep cfg st (credCommandClaimedPort x.2, x.2)
  errStep st _ := st

/-- The unauthenticated service answers an issuance of an invented attribute delivered by the
    adversary. -/
theorem unauthenticatedCredService_adversary_issues {Attr O : Type} [DecidableEq Attr]
    (cfg : Qsag.Spec.IdealCredConfig O) (holder : Nat) (attr : Attr)
    (newRoot : Qsag.Spec.Digest256) :
    ((unauthenticatedCredService cfg).step (Qsag.Spec.IdealCredState.empty cfg)
        (Qsag.Spec.CredPort.adversary, .issue holder [attr] newRoot)).map Prod.snd =
      some (.issued 0) :=
  Qsag.Spec.idealCredStep_issuer_issues_at_init cfg holder attr newRoot

/-- An ideal run with no accepted input ends in the state it started from. -/
private theorem idealCred_validTrace_nil {Attr O : Type} [DecidableEq Attr]
    (cfg : Qsag.Spec.IdealCredConfig O) {s a : Qsag.Spec.IdealCredState Attr O}
    {t : List (Qsag.Spec.IdealCredInput Attr × Qsag.Spec.IdealCredOutput O)}
    (h : (Qsag.Spec.idealCredMachine cfg).ValidTrace s t a) (ht : t = []) : a = s := by
  induction h with
  | nil _ => rfl
  | accept _ _ _ => cases ht
  | reject _ _ _ ih => exact ih ht

/-- Tooth (referee 3, N2): with an issuer that is not corrupt at the start, the unauthenticated
    service satisfies `CredentialImplementation` for no relation and no extractor. -/
theorem unauthenticatedCredService_not_implementation {Attr O : Type} [DecidableEq Attr]
    (cfg : Qsag.Spec.IdealCredConfig O) (hHonest : cfg.issuerCorrupt = false) (attr : Attr) :
    ¬ Nonempty (CredentialImplementation Attr cfg (unauthenticatedCredService (Attr := Attr) cfg)) := by
  intro hImpl
  obtain ⟨impl⟩ := hImpl
  have hIssues := unauthenticatedCredService_adversary_issues cfg 0 attr 0#256
  cases hStep : (unauthenticatedCredService cfg).step (Qsag.Spec.IdealCredState.empty cfg)
      (Qsag.Spec.CredPort.adversary, Qsag.Spec.CredCommand.issue 0 [attr] 0#256) with
  | none =>
    rw [hStep] at hIssues
    cases hIssues
  | some res =>
    obtain ⟨st', out⟩ := res
    rw [hStep] at hIssues
    have hOut : out = Qsag.Spec.IdealCredOutput.issued 0 := Option.some.inj hIssues
    subst hOut
    refine credentialImplementation_rejects_foreign_issue impl
      (c₀ := Qsag.Spec.IdealCredState.empty cfg) (tr := []) rfl (.nil _) ?_
      (by intro h; cases h) hStep
    intro a hAt
    obtain ⟨_, aTr, hTrA, hView⟩ := hAt
    have hNil : aTr = [] := List.map_eq_nil_iff.mp hView
    rw [idealCred_validTrace_nil cfg hTrA hNil]
    exact hHonest

#verify_constructive
  Qsag.Top.credential_sd_limbo256_tau33_interactive_soundness
  Qsag.Top.CredentialImplementation.abstract_run
  Qsag.Top.credentialImplementation_presentation_provenance
  Qsag.Top.credentialImplementation_issuance_authenticated
  Qsag.Top.credentialImplementation_toprf_provenance
  Qsag.Top.unauthenticatedCredService_adversary_issues

#tooth_pair Qsag.Top.credentialImplementation_issuance_authenticated vs
  Qsag.Top.credentialImplementation_rejects_foreign_issue
#tooth_pair Qsag.Top.credentialImplementation_presentation_provenance vs
  Qsag.Top.credentialImplementation_rejects_foreign_presentation
#tooth_pair Qsag.Top.credentialImplementation_issuance_authenticated vs
  Qsag.Top.unauthenticatedCredService_not_implementation

/-! ## 8. Connecting `Spec.CredPort` Caller Labels to `Spec.AuthenticatedChannelContract` -/

/-- Canonical peer-channel endpoint identifier (`Spec.ChannelMsg.sender`) for each `Spec.CredParty`:
    * `0`: `.issuer`
    * `1`: reserved `.client` endpoint
    * `2 + i` (`i < toprfServers`): committee `.server i`
    * `2 + toprfServers + h`: `.holder h` -/
def credPartyEndpointId : Qsag.Spec.CredParty → Nat
  | .issuer => 0
  | .server i => 2 + i
  | .holder h => 2 + Qsag.Spec.pqCredentialProfile.toprfServers + h

/-- Map an authenticated channel sender ID (`Spec.ChannelMsg.sender`) onto `Spec.CredPort`,
    routing any sender in `adversaryIds` onto `.adversary`. -/
def credChannelEndpointPort (adversaryIds : List Nat) (senderId : Nat) : Qsag.Spec.CredPort :=
  if decide (senderId ∈ adversaryIds) then
    .adversary
  else if senderId = 0 then
    .issuer
  else if senderId = 1 then
    .client
  else if senderId < 2 + Qsag.Spec.pqCredentialProfile.toprfServers then
    .server (senderId - 2)
  else
    .holder (senderId - (2 + Qsag.Spec.pqCredentialProfile.toprfServers))

/-- Valid party bound on `CredParty` (committee servers satisfy `i < toprfServers`). -/
def CredPartyInCommittee : Qsag.Spec.CredParty → Prop
  | .issuer => True
  | .holder _ => True
  | .server i => i < Qsag.Spec.pqCredentialProfile.toprfServers

theorem credChannelEndpointPort_roundtrip
    (adversaryIds : List Nat) (party : Qsag.Spec.CredParty)
    (hBound : CredPartyInCommittee party)
    (hHonestEndpoint : credPartyEndpointId party ∉ adversaryIds) :
    credChannelEndpointPort adversaryIds (credPartyEndpointId party) = party.port := by
  cases party with
  | issuer =>
    unfold credPartyEndpointId at hHonestEndpoint ⊢
    unfold credChannelEndpointPort Qsag.Spec.CredParty.port
    rw [decide_eq_false hHonestEndpoint]
    rfl
  | server i =>
    have hi : i < Qsag.Spec.pqCredentialProfile.toprfServers := hBound
    unfold credPartyEndpointId at hHonestEndpoint ⊢
    unfold credChannelEndpointPort Qsag.Spec.CredParty.port
    rw [decide_eq_false hHonestEndpoint]
    have hNe0 : ¬ (2 + i = 0) := by omega
    have hNe1 : ¬ (2 + i = 1) := by omega
    have hLt : 2 + i < 2 + Qsag.Spec.pqCredentialProfile.toprfServers := by omega
    have hSub : 2 + i - 2 = i := by omega
    simp only [Bool.false_eq_true, ↓reduceIte, hNe0, hNe1, hLt, hSub]
  | holder h =>
    unfold credPartyEndpointId at hHonestEndpoint ⊢
    unfold credChannelEndpointPort Qsag.Spec.CredParty.port
    rw [decide_eq_false hHonestEndpoint]
    have hSrvPos : 0 < Qsag.Spec.pqCredentialProfile.toprfServers := by decide
    have hNe0 : ¬ (2 + Qsag.Spec.pqCredentialProfile.toprfServers + h = 0) := by omega
    have hNe1 : ¬ (2 + Qsag.Spec.pqCredentialProfile.toprfServers + h = 1) := by omega
    have hNotLt : ¬ (2 + Qsag.Spec.pqCredentialProfile.toprfServers + h <
        2 + Qsag.Spec.pqCredentialProfile.toprfServers) := by omega
    have hSub : 2 + Qsag.Spec.pqCredentialProfile.toprfServers + h -
        (2 + Qsag.Spec.pqCredentialProfile.toprfServers) = h := by omega
    simp only [Bool.false_eq_true, ↓reduceIte, hNe0, hNe1, hNotLt, hSub]

theorem credChannelEndpointPort_unique_sender
    (adversaryIds : List Nat) (senderId : Nat) (party : Qsag.Spec.CredParty)
    (_hBound : CredPartyInCommittee party)
    (hPortEq : credChannelEndpointPort adversaryIds senderId = party.port) :
    senderId ∉ adversaryIds ∧ senderId = credPartyEndpointId party := by
  unfold credChannelEndpointPort at hPortEq
  cases hAdv : decide (senderId ∈ adversaryIds) with
  | true =>
    rw [hAdv] at hPortEq
    simp only [↓reduceIte] at hPortEq
    cases party <;> cases hPortEq
  | false =>
    have hNotAdv : senderId ∉ adversaryIds := of_decide_eq_false hAdv
    rw [hAdv] at hPortEq
    simp only [Bool.false_eq_true, ↓reduceIte] at hPortEq
    refine ⟨hNotAdv, ?_⟩
    by_cases h0 : senderId = 0
    · rw [h0] at hPortEq ⊢
      simp only [↓reduceIte] at hPortEq
      cases party with
      | issuer => rfl
      | server _ => cases hPortEq
      | holder _ => cases hPortEq
    · simp only [h0, ↓reduceIte] at hPortEq
      by_cases h1 : senderId = 1
      · rw [h1] at hPortEq
        simp only [↓reduceIte] at hPortEq
        cases party <;> cases hPortEq
      · simp only [h1, ↓reduceIte] at hPortEq
        by_cases hLt : senderId < 2 + Qsag.Spec.pqCredentialProfile.toprfServers
        · simp only [hLt, ↓reduceIte] at hPortEq
          cases party with
          | issuer => cases hPortEq
          | holder _ => cases hPortEq
          | server i =>
            dsimp only [credPartyEndpointId]
            injection hPortEq with hiEq
            omega
        · simp only [hLt, ↓reduceIte] at hPortEq
          cases party with
          | issuer => cases hPortEq
          | server _ => cases hPortEq
          | holder h =>
            dsimp only [credPartyEndpointId]
            have hSrvPos : 0 < Qsag.Spec.pqCredentialProfile.toprfServers := by decide
            injection hPortEq with hhEq
            omega

/-- **`CredPort` Authenticated by `Spec.AuthenticatedChannelContract`
    (`credPort_authenticated_by_channel_contract`)**:
    Discharges the authenticated-port assumption of `CredentialImplementation` from
    `Spec.AuthenticatedChannelContract admits` (inhabited by `Spec.checkedChannel_contract`):
    whenever a network event `tr = pre ++ .deliver m :: post` admitted by `admits` maps onto an
    authenticated party port `credChannelEndpointPort adversaryIds m.sender = party.port`:
    1. `m.sender` is uniquely that honest party's endpoint `credPartyEndpointId party` and
       `m.sender ∉ adversaryIds`,
    2. `party` genuinely transmitted `.send m ∈ pre` earlier in the trace, and
    3. `.deliver m ∉ post` (strict replay protection — `m` is never re-delivered)! -/
theorem credPort_authenticated_by_channel_contract
    {admits : List Qsag.Spec.ChannelEvent → Prop}
    (hContract : Qsag.Spec.AuthenticatedChannelContract admits)
    (adversaryIds : List Nat)
    {tr pre post : List Qsag.Spec.ChannelEvent} {m : Qsag.Spec.ChannelMsg}
    (hAdmits : admits tr)
    (hSplit : tr = pre ++ .deliver m :: post)
    (party : Qsag.Spec.CredParty) (hBound : CredPartyInCommittee party)
    (hPort : credChannelEndpointPort adversaryIds m.sender = party.port) :
    m.sender ∉ adversaryIds ∧
    m.sender = credPartyEndpointId party ∧
    Qsag.Spec.ChannelEvent.send m ∈ pre ∧
    Qsag.Spec.ChannelEvent.deliver m ∉ post := by
  obtain ⟨hNotAdv, hSenderEq⟩ :=
    credChannelEndpointPort_unique_sender adversaryIds m.sender party hBound hPort
  exact ⟨hNotAdv, hSenderEq,
    hContract.peerAuthenticated tr hAdmits pre post m hSplit,
    hContract.replayProtected tr hAdmits pre post m hSplit⟩

/-- `#tooth` Without `AuthenticatedChannelContract` (on an open relay `admits := fun _ => True`),
    an unauthenticated delivery forged with `m.sender = 0` arrives on `.issuer` with `.send m ∉ pre`
    and can even be replayed twice in `post`! -/
theorem tooth_open_relay_spoofs_issuer_credPort :
    ∃ (tr : List Qsag.Spec.ChannelEvent) (m : Qsag.Spec.ChannelMsg),
      ¬ Qsag.Spec.AuthenticatedChannelContract (fun _ => True) ∧
      tr = [] ++ .deliver m :: [.deliver m] ∧
      credChannelEndpointPort [99] m.sender = Qsag.Spec.CredPort.issuer ∧
      Qsag.Spec.ChannelEvent.deliver m ∈ [.deliver m] ∧
      Qsag.Spec.ChannelEvent.send m ∉ ([] : List Qsag.Spec.ChannelEvent) := by
  let m : Qsag.Spec.ChannelMsg := ⟨0, 1, 0, [0x42]⟩
  have hPort : credChannelEndpointPort [99] m.sender = Qsag.Spec.CredPort.issuer :=
    credChannelEndpointPort_roundtrip [99] .issuer trivial (by decide)
  exact ⟨[.deliver m, .deliver m], m, Qsag.Spec.open_relay_has_no_channel_contract,
    rfl, hPort, List.Mem.head _, fun h => nomatch h⟩

/-! ## 9. Canonical `Spec.Assumptions` Lattice & Regular-Dual-LPN Preprocessing Locale Bridge -/

/-- `#tooth` Degenerate `0`-row Module-SIS (`rows = 0`) is refuted for every nontrivial bound
    `ε < 1` (`Spec.moduleSisHard_noRows_refuted`), confirming `ModuleSisHard` is non-vacuous! -/
theorem tooth_degenerate_moduleSis_noRows_refuted
    (𝒜 : (List (List (List Nat)) → List (List Nat)) → Prop)
    (h𝒜 : 𝒜 (fun _ => [[1]]))
    {ε : Qsag.Spec.RatBound} (hε : ε.num < ε.den) :
    ¬ Qsag.Spec.ModuleSisHard 𝒜 1 2 0 1 1 ε :=
  Qsag.Spec.moduleSisHard_noRows_refuted 𝒜 h𝒜 hε

#verify_constructive Qsag.Top.threshold_mldsa_frozen_sacrifice_sign_step_soundness
  Qsag.Top.credPort_authenticated_by_channel_contract
  Qsag.Top.tooth_open_relay_spoofs_issuer_credPort
  Qsag.Top.tooth_degenerate_moduleSis_noRows_refuted

#verify_constructive Qsag.SpdzToprf.spdzEval_sound_or_mac_forgery
  Qsag.SpdzToprf.evalFooled_macKey_unique
  Qsag.SpdzToprf.spdz_mac_forgery_game_bound
  Qsag.SpdzToprf.goldilocksExt2_card_bits
  Qsag.SpdzToprf.spdzEval_macKey_zero_leakage
  Qsag.SpdzToprf.spdzEval_honest_complete

#tooth_pair Qsag.Top.credPort_authenticated_by_channel_contract vs
  Qsag.Top.tooth_open_relay_spoofs_issuer_credPort

#tooth_pair Qsag.Top.threshold_mldsa_frozen_sacrifice_sign_step_soundness vs
  Qsag.tooth_rssSacrificedSignStep_swapped_order_forges

-- Equations used by `Tests/CredentialsTeeth`; no body is exposed.
#export_eqns CredPartyInCommittee credPartyEndpointId

end Qsag.Top
end
