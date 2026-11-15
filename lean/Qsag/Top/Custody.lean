module
/-
# Qsag.Top.Custody — End-to-End Composed Separated Threshold Custody Refinements and Mediation

Top-level composition module (zero `import all`) unifying the threshold custody, crash-WAL,
complete-mediation, and 4-layer ELF-to-Ideal simulation proofs through `Qsag.Spec.Refines` and
`Qsag.Spec.IdealCustody`:
1. Vertical `Spec.Refines.trans` composition of the 4-layer `ELF → MIR → Protocol → IdealTsig`
   machine hierarchy (`MirSpecBridgeCore`, `MirSpecBridge`),
2. `Spec.Refines` lockstep equivalence between distributed RSS threshold release
   (`RssProduction.release`) and reference release (`RssProduction.referenceRelease`),
3. End-to-end authenticated custody quorum submission → `validThresholdApproval` → `IdealTsig`
   execution + policy-mediation provenance / `prodEufCmaWin` reduction (`SeparatedCustodyUcBridge`,
   `CompleteMediationBoundary`, `SeparatedCustodyCollision`), and
4. Crash-consistent POSIX atomic `replaceAtomic` + external monotone anchor coherence with
   `WalLatchState` and `CompleteMediationBoundary` watermarks (`PosixCrashWal`, `SeparatedCustodyUcBridge`),
5. Lockstep `Spec.Refines` of the certificate-quorum coordinator (`certCustodyMachine`: custodian
   certificates bound to `(deploymentId, intent)`, adversarial certificate submission, adaptive
   corruption, shared `Spec.CustodyLedger`) into `Spec.idealCustodyMachine`, conditional on the named
   certificate-layer obligations `CustodyCertLayer` (signing correctness) and `CustodyUnforgeable`.
-/

public import Qsag.Spec.Primitives
public import Qsag.Spec.Parameters
public import Qsag.Spec.Refines
public import Qsag.Exec.RefinesBridges
public import Qsag.Spec.GameBound
public import Qsag.Spec.Assumptions
public import Qsag.Spec.IdealCustody
public import Qsag.Top.Signing
public import Qsag.Custody.SeparatedCustodyUcBridge
public import Qsag.Custody.SeparatedCustodyCollision
public import Qsag.Custody.SeparatedCustodyUcResource
public import Qsag.Custody.SeparatedCustodyResourceSoundness
public import Qsag.Custody.JortsBeltLatchAndQuorumSwitching
public import Qsag.Exec.ThresholdIdealService
public import Qsag.Exec.ThresholdIdealDurableService
public import Qsag.Custody.ThresholdIdealServiceCustodyBridge
public import Qsag.Exec.CeremonyAtomicityAndAbort
public import Qsag.Exec.RssParticipantMachine
public import Qsag.Exec.RssParticipantSponge
public import Qsag.Exec.RssParticipantBinding
public import Qsag.Exec.RssParticipantNetwork
public import Qsag.Exec.RssParticipantPassiveSimulation
public import Qsag.Exec.RssParticipantFixedTape
public import Qsag.Exec.RssParticipantGateChecks
public import Qsag.Exec.RssParticipantGateWeights
public import Qsag.Exec.RssParticipantGateEvidence
public import Qsag.Exec.RssParticipantGateBatches
public import Qsag.Exec.RssSigningEnrollment
public import Qsag.Exec.RssSigningExecution
public import Qsag.Exec.RssSigningPublicCompletion
public import Qsag.Exec.RssProductionProfile
public import Qsag.Exec.MirSpecBridge
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Top

open scoped Qsag.Spec

set_option autoImplicit false

/-! ## 1. Distributed RSS Release Refines Reference Release (`rssSharedMachine ⊑ rssReferenceMachine`) -/

/-- Reactive `Spec.Machine` wrapping distributed shared-circuit `RssProduction.release`. -/
def rssSharedReleaseMachine (p : Qsag.RssProduction.Profile) :
    Qsag.Spec.Machine Qsag.WalLatchState Qsag.SessionScheduleReq
      (Except Qsag.RssProduction.Failure (List UInt8)) :=
  Qsag.Spec.Machine.ofTotal
    (fun w => w = Qsag.RssProduction.initial p)
    (fun w req => Qsag.RssProduction.release p req w)

/-- Reactive `Spec.Machine` wrapping single-key `RssProduction.referenceRelease`. -/
def rssReferenceReleaseMachine (p : Qsag.RssProduction.Profile) :
    Qsag.Spec.Machine Qsag.WalLatchState Qsag.SessionScheduleReq
      (Except Qsag.RssProduction.Failure (List UInt8)) :=
  Qsag.Spec.Machine.ofTotal
    (fun w => w = Qsag.RssProduction.initial p)
    (fun w req => Qsag.RssProduction.referenceRelease p req w)

/-- **Distributed RSS Release Forward Refinement (`rssSharedRelease_refines_reference`)**:
    Distributed threshold evaluation + atomic WAL gating (`rssSharedReleaseMachine p`) refines
    `rssReferenceReleaseMachine p` across all multi-turn request schedules, including exact retry
    replays and sticky quarantine on signing/encoding failures! -/
def rssSharedRelease_refines_reference (p : Qsag.RssProduction.Profile) :
    rssSharedReleaseMachine p ⊑ rssReferenceReleaseMachine p :=
  Qsag.Spec.LockstepSim.toRefines
    { Inv := fun _ => True
      abs := id
      init_inv := fun hInit => ⟨trivial, hInit⟩
      step_eq := fun {w} req _ => by
        dsimp only [rssSharedReleaseMachine, rssReferenceReleaseMachine, Qsag.Spec.Machine.ofTotal, id]
        rw [Qsag.RssProduction.release_eq_reference p req w]
        exact ⟨trivial, rfl⟩ }

theorem rssSharedRelease_preserves_traces (p : Qsag.RssProduction.Profile)
    {tr : List (Qsag.SessionScheduleReq × Except Qsag.RssProduction.Failure (List UInt8))}
    (hAdmits : (rssSharedReleaseMachine p).AdmitsTrace tr) :
    (rssReferenceReleaseMachine p).AdmitsTrace tr :=
  (rssSharedRelease_refines_reference p).preserve_admitsTrace hAdmits

/-! ## 2. Vertical 4-Layer `ELF ⊑ MIR ⊑ Protocol ⊑ IdealTsig` Refinement via `Spec.Refines.trans` -/

/-- Wrap `MirPolicyGuardState` (`mirPolicyGuardMachine`) as an initialized `Spec.Machine`. -/
def mirPolicyMachine (m₀ : Qsag.MirPolicyGuardState) :
    Qsag.Spec.Machine Qsag.MirPolicyGuardState Qsag.MirTxIntent Qsag.ApprovedIntentEnvelope :=
  Qsag.Spec.Machine.ofPartyMachine (fun m => m = m₀) Qsag.mirPolicyGuardMachine

/-- Wrap `StatefulPolicyGuard` (`specPolicyGuardMachine`) as an initialized `Spec.Machine`. -/
def specPolicyMachine (s₀ : Qsag.StatefulPolicyGuard) :
    Qsag.Spec.Machine Qsag.StatefulPolicyGuard Qsag.MirTxIntent Qsag.ApprovedIntentEnvelope :=
  Qsag.Spec.Machine.ofPartyMachine (fun s => s = s₀) Qsag.specPolicyGuardMachine

/-- Lift `mirPolicyGuard_forwardSim_custodyPolicy` into `Spec.Refines`. -/
def mirPolicy_refines_specPolicy
    (m₀ : Qsag.MirPolicyGuardState) (s₀ : Qsag.StatefulPolicyGuard)
    (hRel₀ : Qsag.mirPolicyGuard_forwardSim_custodyPolicy.Rel m₀ s₀) :
    mirPolicyMachine m₀ ⊑ specPolicyMachine s₀ :=
  Qsag.Spec.Refines.ofPartyForwardSim
    Qsag.mirPolicyGuard_forwardSim_custodyPolicy
    (fun _ => s₀)
    (fun {c} hc => by subst hc; exact ⟨rfl, hRel₀⟩)

/-- **Four-Layer ELF-to-Ideal Vertical `Spec.Refines` Composition (`elf_to_idealTsig_refines`)**:
    Lifts the compiled ELF (`Layer1`) → MIR (`Layer2`) → interactive protocol (`Layer3`) →
    `IdealTsig` (`Layer4`) stack into `Spec.Machine` and composes the forward simulation together
    with `shamirSubset_preserves_multiturn_safety`! -/
def elf_to_idealTsig_refines {PK : Type} {n q f : Nat}
    (corrupt : List (Fin n)) (pkDigestOf : PK → List UInt8) (pk : PK)
    (dealtShares : Nat → Option (List UInt8))
    (custodianShare : List UInt8)
    (signFromShare : List UInt8 → List UInt8 → ByteArray)
    (assembleThresholdSig : (Nat → Option (List UInt8)) → List UInt8 → ByteArray)
    (idealSignOracle : List UInt8 → ByteArray)
    (hBound : n + f < 2 * q) (hQPos : 0 < q) (hQLeN : q ≤ n)
    (hCorruptNd : corrupt.Nodup) (hCorruptLe : corrupt.length ≤ f)
    (hSigMatch : ∀ msg : List UInt8, assembleThresholdSig dealtShares msg = signFromShare custodianShare msg)
    (hOracleEq : ∀ msg : List UInt8, assembleThresholdSig dealtShares msg = idealSignOracle msg)
    (s1₀ : Qsag.Layer1ElfState) (s4₀ : Qsag.Layer4IdealState PK)
    (hRel₀ : (Qsag.isa_to_mir_to_protocol_to_ideal_sim corrupt pkDigestOf pk dealtShares
      custodianShare signFromShare assembleThresholdSig idealSignOracle
      hBound hQPos hQLeN hCorruptNd hCorruptLe hSigMatch hOracleEq).Rel s1₀ s4₀) :
    Qsag.Spec.Machine.ofPartyMachine (fun s => s = s1₀)
      (Qsag.layer1CompiledElfMachine q (pkDigestOf pk)
        (fun m msg => signFromShare (Qsag.readShareMem32 m) msg)) ⊑
    Qsag.Spec.Machine.ofPartyMachine (fun s => s = s4₀)
      (Qsag.layer4IdealTsigMachine corrupt pkDigestOf idealSignOracle) :=
  Qsag.Spec.Refines.ofPartyForwardSim
    (Qsag.isa_to_mir_to_protocol_to_ideal_sim corrupt pkDigestOf pk dealtShares
      custodianShare signFromShare assembleThresholdSig idealSignOracle
      hBound hQPos hQLeN hCorruptNd hCorruptLe hSigMatch hOracleEq)
    (fun _ => s4₀)
    (fun {c} hc => by subst hc; exact ⟨rfl, hRel₀⟩)

theorem elf_to_idealTsig_trace_inclusion {PK : Type} {n q f : Nat}
    (corrupt : List (Fin n)) (pkDigestOf : PK → List UInt8) (pk : PK)
    (dealtShares : Nat → Option (List UInt8))
    (custodianShare : List UInt8)
    (signFromShare : List UInt8 → List UInt8 → ByteArray)
    (assembleThresholdSig : (Nat → Option (List UInt8)) → List UInt8 → ByteArray)
    (idealSignOracle : List UInt8 → ByteArray)
    (hBound : n + f < 2 * q) (hQPos : 0 < q) (hQLeN : q ≤ n)
    (hCorruptNd : corrupt.Nodup) (hCorruptLe : corrupt.length ≤ f)
    (hSigMatch : ∀ msg : List UInt8, assembleThresholdSig dealtShares msg = signFromShare custodianShare msg)
    (hOracleEq : ∀ msg : List UInt8, assembleThresholdSig dealtShares msg = idealSignOracle msg)
    (s1₀ : Qsag.Layer1ElfState) (s4₀ : Qsag.Layer4IdealState PK)
    (hRel₀ : (Qsag.isa_to_mir_to_protocol_to_ideal_sim corrupt pkDigestOf pk dealtShares
      custodianShare signFromShare assembleThresholdSig idealSignOracle
      hBound hQPos hQLeN hCorruptNd hCorruptLe hSigMatch hOracleEq).Rel s1₀ s4₀)
    {tr : List (Qsag.FourLayerReq n × Qsag.FourLayerOut)}
    (hAdmits : (Qsag.Spec.Machine.ofPartyMachine (fun s => s = s1₀)
      (Qsag.layer1CompiledElfMachine q (pkDigestOf pk)
        (fun m msg => signFromShare (Qsag.readShareMem32 m) msg))).AdmitsTrace tr) :
    (Qsag.Spec.Machine.ofPartyMachine (fun s => s = s4₀)
      (Qsag.layer4IdealTsigMachine corrupt pkDigestOf idealSignOracle)).AdmitsTrace tr :=
  (elf_to_idealTsig_refines corrupt pkDigestOf pk dealtShares custodianShare
    signFromShare assembleThresholdSig idealSignOracle
    hBound hQPos hQLeN hCorruptNd hCorruptLe hSigMatch hOracleEq s1₀ s4₀ hRel₀).preserve_admitsTrace hAdmits

/-! ## 3. Separated Custody Quorum Provenance + Non-Hiding RSS Release + Quarantine Isolation -/

/-- **End-to-End Custody Quorum Provenance, Non-Hiding Release, and Party Quarantine Composition
    (`separated_custody_provenance_and_release_chain`)**:
    Chains `SeparatedCustodyUcBridge.custodyHistory_submit_validThresholdApproval_and_provenance`,
    `SeparatedCustodyUcBridge.evalNonHidingRssCutRelease_sound`,
    `SeparatedCustodyUcBridge.quarantinePartyNodes_isolates_and_wipes`, and
    `CompleteMediationBoundary.trace_burned_spend_le_cap`:
    1. Every accepted `Custody.submitRecorded` quorum synthesizes a non-empty `hon` satisfying
       `validThresholdApproval st hon = true` and advances `execIdealTsig` to `.signed`,
    2. Cumulative coordinator spend AND every custodian's durable burned spend remain `≤ capacity`,
    3. At least one unquarantined honest custodian `c.party ∈ hon` either approved `r` through
       `CompleteMediationBoundary` (`ProducedPolicyApproval`) or witnesses an explicit `prodEufCmaWin`
       + `(ProdSmTcrBreak ∨ ProdPreimageBreak)` hash break,
    4. Any accepted `evalNonHidingRssCutRelease` byte slice decodes to a verified `PqHashSig` under
       `b.enrolledPk`, and
    5. Quarantine of any faulted party `targetPid` zeroizes its projected share (`= none`) without
       perturbing any other honest party! -/
theorem separated_custody_provenance_and_release_chain {PK SK Sig ShareT : Type}
    (S : Qsag.AbstractSigScheme PK SK (List UInt8) Sig) (simSign : List UInt8 → Sig)
    (d : Qsag.Custody.Deployment) (commands : List Qsag.Custody.HistoryCommand)
    (st : Qsag.IdealTsigState PK (List UInt8))
    (hAlign : Qsag.CustodyTsigAligned d st)
    (r : Qsag.Custody.Intent) (certs : List Qsag.Custody.Certificate)
    (hRadix : d.signer.params.w = 4 ∨ d.signer.params.w = 16)
    (hStateful : d.signer.params.statefulJorts = true)
    (hUnquarantined : ∀ c ∈ certs, c.party ∉ st.identifiedCheaters)
    (hSub : (Qsag.Custody.submitRecorded d (Qsag.Custody.generatedHistory d commands).shared r certs).2 = true)
    (b : Qsag.GroundedRssSigningBundle) (req : Qsag.SessionScheduleReq) (sigBytes : ByteArray)
    (hReleaseOk : Qsag.evalNonHidingRssCutRelease b req = .inr sigBytes)
    (nodes : List (Qsag.PartyCustodyNode ShareT)) (targetPid : Nat) :
    let hon := Qsag.custodyQuorumHonestApprovers st.corruptParties certs
    let hist := Qsag.Custody.generatedHistory d commands
    hon ≠ [] ∧
    Qsag.validThresholdApproval st hon = true ∧
    hist.shared.coordinator.spent + r.spend ≤ d.capacity ∧
    (∃ c ∈ certs, c.party ∈ hon ∧ c.party ∉ st.corruptParties ∧
      (Qsag.Custody.ProducedPolicyApproval d hist c.party r ∨
       (Qsag.prodEufCmaWin d.signer.suite d.signer.params
          ⟨d.keys c.party, Qsag.Custody.queries d.signer c.party (hist.parties c.party).vault,
            Qsag.Custody.payload c.party r, c.signature⟩ = true ∧
        (Qsag.ProdSmTcrBreak d.signer.suite d.signer.params (d.keys c.party)
           (Qsag.Custody.signingLog d.signer (d.keys c.party) c.party (hist.parties c.party).vault) ∨
         Qsag.ProdPreimageBreak d.signer.suite d.signer.params (d.keys c.party)
           (Qsag.Custody.signingLog d.signer (d.keys c.party) c.party (hist.parties c.party).vault)
           (Qsag.Custody.payload c.party r) c.signature)))) ∧
    (∃ sig : Qsag.PqHashSig,
      Qsag.decodeProductionSigWire b.params (Qsag.unpackWire sigBytes) = .ok sig ∧
      Qsag.verifyProductionPqHashSig Qsag.cshake256Suite b.params b.enrolledPk
        (Qsag.encodeUcSigningRequest req) sig = true) ∧
    Qsag.projectPartyLocalShares (Qsag.quarantinePartyNodes targetPid nodes) targetPid = none := by
  intro hon hist
  obtain ⟨hHonNe, hVal, _, hCap, hProv⟩ :=
    Qsag.custodyHistory_submit_validThresholdApproval_and_provenance
      S simSign d commands st hAlign r certs hRadix hStateful hUnquarantined hSub
  obtain ⟨sig, hDec, _, hVer⟩ := Qsag.evalNonHidingRssCutRelease_sound b req sigBytes hReleaseOk
  obtain ⟨hWipe, _⟩ := Qsag.quarantinePartyNodes_isolates_and_wipes nodes targetPid targetPid
  exact ⟨hHonNe, hVal, hCap, hProv, ⟨sig, hDec, hVer⟩, hWipe⟩

/-! ## 4. Unified Interactive & Durable Threshold Service Refinement (`ThresholdIdeal* ⊑ Ideal`) -/

/-- **Threshold Interactive Service Forward Refinement (`thresholdServiceShared_refines_ideal`)**:
    Folds `ThresholdIdealService.shared` and `ThresholdIdealService.ideal` into canonical
    `Spec.Refines` (`Machine.ofInteractive ... ⊑ Machine.ofInteractive ...`). -/
def thresholdServiceShared_refines_ideal (c : Qsag.ThresholdIdealService.Config) :
    Qsag.Spec.Machine.ofInteractive
      (fun s => s = Qsag.ThresholdIdealService.initial c)
      (Qsag.ThresholdIdealService.shared c) ⊑
    Qsag.Spec.Machine.ofInteractive
      (fun s => s = Qsag.ThresholdIdealService.initial c)
      (Qsag.ThresholdIdealService.ideal c) :=
  Qsag.Spec.LockstepSim.toRefines
    { Inv := fun _ => True
      abs := id
      init_inv := fun hInit => ⟨trivial, hInit⟩
      step_eq := fun {s} inp _ => by
        change True ∧ some ((Qsag.ThresholdIdealService.ideal c).step s inp) =
          some ((Qsag.ThresholdIdealService.shared c).step s inp)
        rw [Qsag.ThresholdIdealService.shared_step_eq_ideal c s inp]
        exact ⟨trivial, rfl⟩ }

/-- **Threshold Durable Service Forward Refinement (`thresholdDurableShared_refines_ideal`)**:
    Folds `ThresholdIdealDurableService.shared` and `ThresholdIdealDurableService.ideal` into
    canonical `Spec.Refines` (`Machine.ofInteractive ... ⊑ Machine.ofInteractive ...`). -/
def thresholdDurableShared_refines_ideal (c : Qsag.ThresholdIdealService.Config) :
    Qsag.Spec.Machine.ofInteractive
      (fun s => s = Qsag.ThresholdIdealDurableService.initial)
      (Qsag.ThresholdIdealDurableService.shared c) ⊑
    Qsag.Spec.Machine.ofInteractive
      (fun s => s = Qsag.ThresholdIdealDurableService.initial)
      (Qsag.ThresholdIdealDurableService.ideal c) :=
  Qsag.Spec.LockstepSim.toRefines
    { Inv := fun _ => True
      abs := id
      init_inv := fun hInit => ⟨trivial, hInit⟩
      step_eq := fun {s} cmd _ => by
        change True ∧ some ((Qsag.ThresholdIdealDurableService.ideal c).step s cmd) =
          some ((Qsag.ThresholdIdealDurableService.shared c).step s cmd)
        rw [Qsag.ThresholdIdealDurableService.shared_step_eq_ideal c s cmd]
        exact ⟨trivial, rfl⟩ }

/-- **Interactive Feedback Emulation, Durable Crash Safety, and Resource Burn Soundness
    (`threshold_durable_feedback_and_resource_burn_chain`)**:
    Composes `thresholdDurableShared_refines_ideal` (transported to `InteractiveService.PrefixEquivalent`
    and `coupled_accept_bits` via `Spec.Refines.toInteractivePrefixEquivalent` /
    `toInteractiveCoupledAcceptBits`), `ThresholdIdealDurableService.crash_preserves_durable`,
    `ThresholdIdealService.authorized_of_verified_threshold`,
    `Custody.RequestPolicy.every_observed_wire_has_burn`, and
    `Custody.RequestPolicy.returned_production_sound`! -/
theorem threshold_durable_feedback_and_resource_burn_chain
    {E : Type}
    (c : Qsag.ThresholdIdealService.Config)
    (compute : Qsag.ThresholdIdealDurableService.Compute)
    (sDur : Qsag.ThresholdIdealDurableService.State)
    (zObs : Qsag.InteractiveService.Observer
      Qsag.ThresholdIdealDurableService.Command
      Qsag.ThresholdIdealService.Output E)
    (e₀ : E)
    (sSvc : Qsag.ThresholdIdealService.State)
    (reqAuth : Qsag.SessionScheduleReq)
    (hThresh : Qsag.validThresholdApproval (Qsag.ThresholdIdealService.publicState c) reqAuth.honestApprovers = true)
    (hInputs : ∀ p ∈ reqAuth.honestApprovers, (p, reqAuth) ∈ sSvc.approvals)
    (profile : Qsag.RssProduction.Profile) (d : Qsag.Custody.Deployment)
    (corrupt : List Nat) (cmds : List Qsag.Custody.RequestPolicy.ResourceCommand)
    (obsPair : Qsag.SessionScheduleReq × List UInt8)
    (hObs : obsPair ∈ (Qsag.Custody.RequestPolicy.resourceRun profile d corrupt
      (Qsag.Custody.RequestPolicy.resourceInitial d) cmds).observed)
    (retReq : Qsag.SessionScheduleReq) (retBytes : List UInt8)
    (hRet : (retReq, retBytes) ∈ (Qsag.Custody.RequestPolicy.resourceRun profile d corrupt
      (Qsag.Custody.RequestPolicy.resourceInitial d) cmds).returned) :
    Qsag.InteractiveService.PrefixEquivalent
      (Qsag.ThresholdIdealDurableService.shared c)
      (Qsag.ThresholdIdealDurableService.ideal c)
      Qsag.ThresholdIdealDurableService.initial
      Qsag.ThresholdIdealDurableService.initial ∧
    zObs.accept (Qsag.InteractiveService.run (Qsag.ThresholdIdealDurableService.shared c)
      zObs.environment zObs.fuel Qsag.ThresholdIdealDurableService.initial e₀).2 =
      zObs.accept (Qsag.InteractiveService.run (Qsag.ThresholdIdealDurableService.ideal c)
      zObs.environment zObs.fuel Qsag.ThresholdIdealDurableService.initial e₀).2 ∧
    (Qsag.ThresholdIdealDurableService.stepWith c compute sDur .crash).1.nextLeaf = sDur.nextLeaf ∧
    Qsag.ThresholdIdealService.authorized c sSvc reqAuth = true ∧
    (∃ r ∈ (Qsag.Custody.RequestPolicy.resourceRun profile d corrupt
        (Qsag.Custody.RequestPolicy.resourceInitial d) cmds).durable.reserved,
      r.request = obsPair.1) ∧
    (∃ sig, Qsag.RssProduction.sharedSign profile retReq = some sig ∧
      Qsag.decodeProductionSigWire profile.params retBytes = .ok sig) := by
  let ref := thresholdDurableShared_refines_ideal c
  obtain ⟨hAbsEq, hRelRaw⟩ := ref.init_ok (rfl : Qsag.ThresholdIdealDurableService.initial = _)
  have hRelInit : ref.Rel Qsag.ThresholdIdealDurableService.initial
      Qsag.ThresholdIdealDurableService.initial := by
    rw [hAbsEq] at hRelRaw
    exact hRelRaw
  have hPref : Qsag.InteractiveService.PrefixEquivalent
      (Qsag.ThresholdIdealDurableService.shared c)
      (Qsag.ThresholdIdealDurableService.ideal c)
      Qsag.ThresholdIdealDurableService.initial
      Qsag.ThresholdIdealDurableService.initial := by
    have hP := Qsag.Spec.Refines.toInteractivePrefixEquivalent ref rfl
    rw [hAbsEq] at hP
    exact hP
  have hCoup := Qsag.Spec.Refines.toInteractiveCoupledAcceptBits ref zObs
    [((Qsag.ThresholdIdealDurableService.initial, Qsag.ThresholdIdealDurableService.initial), e₀)]
    (fun st hMem => by
      cases hMem with
      | head => exact hRelInit
      | tail _ hNil => cases hNil)
  have hAccEq : zObs.accept (Qsag.InteractiveService.run (Qsag.ThresholdIdealDurableService.shared c)
      zObs.environment zObs.fuel Qsag.ThresholdIdealDurableService.initial e₀).2 =
      zObs.accept (Qsag.InteractiveService.run (Qsag.ThresholdIdealDurableService.ideal c)
      zObs.environment zObs.fuel Qsag.ThresholdIdealDurableService.initial e₀).2 := by
    injection hCoup with hHead _
  obtain ⟨hNextLeaf, _, _, _⟩ := Qsag.ThresholdIdealDurableService.crash_preserves_durable c compute sDur
  have hAuth := Qsag.ThresholdIdealService.authorized_of_verified_threshold c sSvc reqAuth hThresh hInputs
  have hBurn := Qsag.Custody.RequestPolicy.every_observed_wire_has_burn profile d corrupt cmds obsPair hObs
  obtain ⟨sig, hSign, _, hDec, _⟩ :=
    Qsag.Custody.RequestPolicy.returned_production_sound profile d corrupt cmds retReq retBytes hRet
  exact ⟨hPref, hAccEq, hNextLeaf, hAuth, hBurn, ⟨sig, hSign, hDec⟩⟩

/-! ## 5. POSIX Crash-Consistent WAL + Monotone External Anchor + Whole-Device Rollback Fence -/

/-- **POSIX Crash-Consistent Atomic WAL Commit & Anti-Rollback Anchor Fence
    (`posix_wal_commit_and_anchor_rollback_fence`)**:
    Composes `SeparatedCustodyUcBridge.posixWalCommit_refines_walCommitBeforeRelease` with
    `CeremonyAtomicityAndAbort.whole_device_rollback_below_anchor_fails_closed`. -/
theorem posix_wal_commit_and_anchor_rollback_fence
    {fs fs' : Qsag.PosixFsState} {lockIno : Qsag.InodeId} {genesisNonce : List UInt8}
    {macFn : Qsag.KeyedMacFn} (hMacWf : Qsag.WellFormedMacFn macFn) {macKey : List UInt8}
    {absWal wal' : Qsag.WalLatchState} {oldLedger newLedger : Qsag.Custody.Ledger}
    {anchor : Qsag.ExternalMonotoneAnchor}
    {h h' : Qsag.LockedVaultHandle} {oldRec newRec : Qsag.WalRecord}
    {pkDigest msgDigest : List UInt8} {reqEpoch ep : Nat} {freshSig : ByteArray}
    {faults : Qsag.IoFaultSchedule}
    (hCoh : Qsag.WalPosixCoherent fs lockIno genesisNonce macFn macKey absWal oldLedger anchor h oldRec)
    (hAuth : Qsag.walPreSignStep absWal pkDigest reqEpoch msgDigest = .ok wal' (.authorizedFresh ep))
    (hRep : Qsag.replaceAtomic fs h (ep + 1)
              (Qsag.encodeDurableLatchPayload (some (ep, msgDigest, freshSig))
                newLedger.nextLeaf newLedger.nextRound newLedger.spent)
              macFn macKey faults = (fs', h', .ok newRec))
    {S : Type} (twoSlot : Qsag.TwoSlotWal S) (oldEven oldOdd : Option (Qsag.WalSlot S))
    (hEven : ∀ s, oldEven = some s → s.generation < twoSlot.anchorGen)
    (hOdd : ∀ s, oldOdd = some s → s.generation < twoSlot.anchorGen) :
    let walCommitted := Qsag.walCommitAuthorized wal' ep msgDigest freshSig
    let anchor' : Qsag.ExternalMonotoneAnchor := ⟨ep + 1, newRec.keyedMac⟩
    Qsag.walCommitBeforeRelease absWal pkDigest reqEpoch msgDigest freshSig =
      .ok walCommitted freshSig ∧
    Qsag.WalPosixCoherent fs' lockIno genesisNonce macFn macKey walCommitted newLedger anchor' h' newRec ∧
    Qsag.verifyAgainstExternalAnchor anchor newRec.body.epoch newRec.keyedMac = true ∧
    Qsag.verifyAgainstExternalAnchor anchor' oldRec.body.epoch oldRec.keyedMac = false ∧
    Qsag.walRecoverable { twoSlot with slotEven := oldEven, slotOdd := oldOdd, volatileStage := none } = false := by
  intro walCommitted anchor'
  obtain ⟨hCom, hCoh', hVerNew, hVerOld⟩ :=
    Qsag.posixWalCommit_refines_walCommitBeforeRelease hMacWf hCoh hAuth hRep
  obtain ⟨_, hFailClosed⟩ :=
    Qsag.whole_device_rollback_below_anchor_fails_closed twoSlot oldEven oldOdd hEven hOdd
  exact ⟨hCom, hCoh', hVerNew, hVerOld, hFailClosed⟩

/-! ## 6. 3-Party RSS Participant Network, Invocation Binding, Gate Checks, and Signing Execution -/

/-- **Distributed 3-Party RSS Participant Protocol, Gate Check, and Signing Execution Chain
    (`rss_participant_network_gate_and_signing_execution_chain`)**:
    Composes `RssParticipantNetwork` (`no_payload_visible_without_corruption`,
    `only_corrupt_sender_can_inject`), `RssParticipantBinding` (`cshakeForRequest_refines_existing`,
    `other_invocation_aborts`), `RssParticipant.GateChecks` (`false_final_accepting_challenges_le_two`),
    `RssSigning.enrolledSigningProgram_refines`, and `RssSigning.honestSigningExecution_wire_refines`! -/
theorem rss_participant_network_gate_and_signing_execution_chain
    (profile : Qsag.RssProduction.Profile) (request : Qsag.SessionScheduleReq)
    (inv₁ inv₂ : Nat) (hInvNe : inv₂ ≠ inv₁)
    (phase₁ phase₂ customization : List UInt8)
    (inputShares : Qsag.RssByteShares) (hWf : inputShares.WellFormed)
    (localTape : Nat → Nat → Qsag.RssPrfZeroSeeds)
    (oldTape : Nat → Nat → Nat → Qsag.RssPrfZeroSeeds)
    (node : Qsag.RssParticipant.Node) (msgEnv : Qsag.RssParticipant.Envelope)
    (hNodeBind : node.binding = Qsag.RssParticipant.invocationBinding profile request inv₁ phase₁)
    (hMsgBind : msgEnv.binding = Qsag.RssParticipant.invocationBinding profile request inv₂ phase₂)
    (net : Qsag.RssParticipant.Network)
    (corruptOpt : Option (Fin 3)) (localMasks : Fin 3 → Nat → Qsag.RssParticipant.LocalMasks)
    (hNotCorruptSender : corruptOpt ≠ some msgEnv.sender)
    (finalComm : Qsag.RssParticipant.GateChecks.FinalCommitment)
    (hFalseClaim : finalComm.claim ≠ Qsag.towerMul 7 finalComm.x finalComm.y)
    (chalPool : List Qsag.Tower128) (hPoolNd : chalPool.Nodup)
    (partTape : Qsag.RssSigning.ParticipantTape) (firstCut : Nat)
    (simNodes : Qsag.RssParticipant.Nodes) (simBind : List UInt8) (simKState : Qsag.RssKState)
    (simRounds : List Qsag.RssParticipant.PassiveRound) (simCursor : Nat)
    (simSamples : List Qsag.KState)
    (hSimRep : Qsag.RssParticipant.Represents simNodes simBind simKState
      (simRounds.map Qsag.RssParticipant.PassiveRound.constant) simCursor)
    (cutLayer : UInt32) (cutTree : UInt64) (cutKp : Nat) (cutDigits : List Nat)
    (hCutCheck : Qsag.checkTargetSum profile.params.w profile.params.ell1 profile.params.targetSum cutDigits = true)
    (gateDepth : Nat) (gateTbl : Qsag.RssParticipant.GateChecks.GateTable gateDepth)
    (hTblInvalid : ¬ Qsag.RssParticipant.GateChecks.gateTableValid gateTbl)
    (validGateTbl : Qsag.RssParticipant.GateChecks.GateTable gateDepth)
    (hTblValid : Qsag.RssParticipant.GateChecks.gateTableValid validGateTbl)
    (gsTuple : Qsag.Rss256ProductProof.ChallengeTuple gateDepth) :
    (((Qsag.RssParticipant.cshakeForRequest profile request inv₁ phase₁ customization inputShares localTape).2.map
        Qsag.reconstructRssBytes) =
      some (Qsag.reconstructRssBytes (Qsag.mpcCshake256SharedRss 32 customization inputShares oldTape))) ∧
    (Qsag.RssParticipant.receive node msgEnv).phase = .aborted ∧
    (Qsag.RssParticipant.observe none net).visiblePayloads = [] ∧
    Qsag.RssParticipant.networkStep corruptOpt localMasks net (.corruptSend msgEnv) = net ∧
    (chalPool.filter (Qsag.RssParticipant.GateChecks.accepts finalComm)).length ≤ 2 ∧
    Qsag.RssSigning.evaluate (Qsag.RssProduction.sharedOracle profile)
      (Qsag.RssSigning.enrolledSigningProgram (Qsag.RssSigning.sharedEnrollment profile) request) =
      Qsag.RssProduction.sharedSign profile request ∧
    Qsag.RssProduction.encodeResult profile.params
      (Qsag.RssSigning.honestSigningExecution profile request partTape firstCut).result =
      Qsag.RssProduction.partialOutput profile request ∧
    (Qsag.RssParticipant.runPassiveReal simNodes simRounds
      ((Qsag.RssParticipant.passiveTapeEquiv simKState simRounds).invFun simSamples)).n0 =
      Qsag.RssParticipant.runPassiveSimulator simNodes.n0 simRounds simSamples ∧
    (Qsag.RssParticipant.forwardTape simKState simRounds simSamples).length = simSamples.length ∧
    Qsag.RssSigning.completeSelectedLeaf profile.params profile.material.pkSeed cutLayer cutTree cutKp cutDigits
      (Qsag.RssSigning.selectedValues profile cutLayer cutTree cutKp cutDigits) =
      Qsag.mpcComputeWotsPk Qsag.cshake256Suite profile.params
        (Qsag.RssProduction.sharedOracle profile).toPqHashMpcOracles
        profile.material.pkSeed cutLayer cutTree cutKp ∧
    ((Qsag.Rss256ProductProof.challengeTuples chalPool gateDepth).filter (fun gs => decide
      (Qsag.RssParticipant.GateChecks.weightEval gs (Qsag.RssParticipant.GateChecks.claimedCoeffs gateTbl) =
        Qsag.RssParticipant.GateChecks.weightEval gs (Qsag.RssParticipant.GateChecks.trueCoeffs gateTbl)))).length ≤
      Qsag.RssParticipant.GateChecks.weightBadBound chalPool.length gateDepth ∧
    Qsag.RssParticipant.GateChecks.weightEval gsTuple (Qsag.RssParticipant.GateChecks.claimedCoeffs validGateTbl) =
      Qsag.RssParticipant.GateChecks.weightEval gsTuple (Qsag.RssParticipant.GateChecks.trueCoeffs validGateTbl) :=
  ⟨Qsag.RssParticipant.cshakeForRequest_refines_existing profile request inv₁ phase₁ customization
     inputShares localTape oldTape hWf,
   Qsag.RssParticipant.other_invocation_aborts profile request inv₁ inv₂ phase₁ phase₂ node msgEnv
     hNodeBind hMsgBind hInvNe,
   Qsag.RssParticipant.no_payload_visible_without_corruption net,
   Qsag.RssParticipant.only_corrupt_sender_can_inject corruptOpt localMasks net msgEnv hNotCorruptSender,
   Qsag.RssParticipant.GateChecks.false_final_accepting_challenges_le_two finalComm hFalseClaim chalPool hPoolNd,
   Qsag.RssSigning.enrolledSigningProgram_refines profile request,
   Qsag.RssSigning.honestSigningExecution_wire_refines profile request partTape firstCut,
   Qsag.RssParticipant.passive_prefix_simulation simNodes simBind simKState simRounds simCursor simSamples hSimRep,
   Qsag.RssParticipant.forwardTape_length simKState simRounds simSamples,
   Qsag.RssSigning.selectedLeaf_from_actual_cut profile cutLayer cutTree cutKp cutDigits hCutCheck,
   Qsag.RssParticipant.GateChecks.invalid_weighted_claim_equal_le gateDepth gateTbl hTblInvalid chalPool hPoolNd,
   Qsag.RssParticipant.GateChecks.validTable_weighted_claim_eq gateDepth validGateTbl hTblValid gsTuple⟩

/-- **Grouped Gate Batch Extraction & Quorum-Switching Leaf Disjointness
    (`gate_batches_and_quorum_switching_disjointness`)**:
    Composes `RssParticipantGateBatches.group_bad_gate_weight_bound` and
    `JortsBeltLatchAndQuorumSwitching.qsB_signature_quorum_switching_disjoint`! -/
theorem gate_batches_and_quorum_switching_disjointness
    {d₁ d₂ : Nat}
    (batchDepth : Nat) (hashes : List Qsag.RssSigning.HashEvidence)
    (gates : List Qsag.RssParticipant.GateChecks.IndexedGate)
    (hExtract : Qsag.RssParticipant.GateChecks.extractHashes hashes = some gates)
    (hCap : gates.length ≤ 2 ^ batchDepth)
    (hBadGate : ∃ i, i < gates.length ∧
      let g := (gates.map Qsag.RssParticipant.GateChecks.IndexedGate.records).getD i
        Qsag.RssParticipant.GateChecks.zeroTriple
      ¬ Qsag.RssParticipant.GateChecks.relation g.1 g.2.1 g.2.2)
    (S : List Qsag.Tower128) (hS : S.Nodup)
    (H : List UInt8 → Qsag.Digest256) (masterSeed : Qsag.Digest256)
    (height : Nat) (s₀ s₁ s₂ : Qsag.QsBGlobalAllocator) (c₁ c₂ : UInt32) (ds₁ ds₂ : List (Fin 4))
    (path₁ path₂ : List Qsag.Digest256)
    (tape₁ : Fin ds₁.length → Qsag.ShamirPadPoly (Qsag.TowerElem 7) d₁ × Qsag.ShamirPadPoly (Qsag.TowerElem 7) d₁)
    (tape₂ : Fin ds₂.length → Qsag.ShamirPadPoly (Qsag.TowerElem 7) d₂ × Qsag.ShamirPadPoly (Qsag.TowerElem 7) d₂)
    (pts₁ ws₁ pts₂ ws₂ : List (Qsag.TowerElem 7)) (sig₁ sig₂ : Qsag.QuorumJortsSig)
    (hAlloc₁ : Qsag.qsBAllocateAndSign H masterSeed height s₀ c₁ ds₁ path₁ tape₁ pts₁ ws₁ = (s₁, some sig₁))
    (hAlloc₂ : Qsag.qsBAllocateAndSign H masterSeed height s₁ c₂ ds₂ path₂ tape₂ pts₂ ws₂ = (s₂, some sig₂)) :
    ((Qsag.Rss256ProductProof.challengeTuples S batchDepth).filter
      (Qsag.RssParticipant.GateChecks.groupWeightAccept batchDepth hashes)).length ≤
      Qsag.RssParticipant.GateChecks.weightBadBound S.length batchDepth ∧
    sig₁.leaf ≠ sig₂.leaf :=
  ⟨Qsag.RssParticipant.GateChecks.group_bad_gate_weight_bound batchDepth hashes gates hExtract hCap hBadGate S hS,
   Qsag.qsB_signature_quorum_switching_disjoint H masterSeed height s₀ s₁ s₂ c₁ c₂ ds₁ ds₂ path₁ path₂
     tape₁ tape₂ pts₁ ws₁ pts₂ ws₂ sig₁ sig₂ hAlloc₁ hAlloc₂⟩

/-! ## 7. Certificate-Quorum Coordinator Refines `Spec.IdealCustody` -/

section CertCustody

open Qsag.Spec

/-- Certificate layer shared by the custodians and the coordinator. `claim c` is the permit a
    certificate asserts (party, deployment, full intent), `valid c` is the coordinator's
    verification, and `issue p dep i` is party `p`'s signing of `(dep, i)` under its own key.
    The two laws are correctness of honest signing. -/
structure CustodyCertLayer (Cert : Type) where
  claim : Cert → CustodyApproval
  valid : Cert → Bool
  issue : Nat → Nat → CustodyIntent → Cert
  issue_valid : ∀ (p dep : Nat) (i : CustodyIntent), valid (issue p dep i) = true
  issue_claim : ∀ (p dep : Nat) (i : CustodyIntent),
    claim (issue p dep i) = CustodyApproval.mk p dep i

/-- Coordinator state: the shared ledger, the corruption set, and the pool of certificates
    delivered to the coordinator. The Boolean tag records the port a certificate arrived through
    (`true`: the issuing custodian's own port). The coordinator's quorum check never reads it. -/
structure CertCustodyState (PK D Sig Cert : Type) where
  ledger : CustodyLedger PK D Sig
  corruptParties : List Nat
  pool : List (Bool × Cert)

def CertCustodyState.init {PK D Sig Cert : Type}
    (dep : Nat) (pk : PK) (quorum : CustodyQuorumProfile) : CertCustodyState PK D Sig Cert :=
  { ledger := (IdealCustodyState.init (D := D) (Sig := Sig) dep pk quorum).ledger
    corruptParties := []
    pool := [] }

/-- Permits asserted by the pooled certificates that arrived through ports tagged `tag`. -/
def certRecords {Cert : Type} (L : CustodyCertLayer Cert) (tag : Bool)
    (pool : List (Bool × Cert)) : List CustodyApproval :=
  (pool.filter (fun tc => tc.1 == tag)).map (fun tc => L.claim tc.2)

/-- The coordinator's per-party check: some pooled certificate verifies and asserts exactly
    `(p, dep, i)`. -/
def certVoted {Cert : Type} (L : CustodyCertLayer Cert) (pool : List (Bool × Cert))
    (p dep : Nat) (i : CustodyIntent) : Bool :=
  pool.any (fun tc => L.valid tc.2 && decide (L.claim tc.2 = CustodyApproval.mk p dep i))

/-- Enrolled parties with a verifying certificate for exactly `(dep, i)`, each counted once. -/
def certApprovers {Cert : Type} (L : CustodyCertLayer Cert) (numParties : Nat)
    (pool : List (Bool × Cert)) (dep : Nat) (i : CustodyIntent) : List Nat :=
  (List.range numParties).filter (fun p => certVoted L pool p dep i)

/-- The certificate the adversary submits for `p`: with `p`'s key once `p` is corrupted, and its
    forgery attempt `forge` otherwise. -/
def certAdvCert {PK D Sig Cert : Type} (L : CustodyCertLayer Cert)
    (forge : CertCustodyState PK D Sig Cert → Nat → Nat → CustodyIntent → Cert)
    (c : CertCustodyState PK D Sig Cert) (p dep : Nat) (i : CustodyIntent) : Cert :=
  if p ∈ c.corruptParties then L.issue p dep i else forge c p dep i

/-- Transition of the certificate-quorum coordinator. Custodians issue certificates, the adversary
    submits certificates that the coordinator accepts whenever they verify for the asserted
    permit, corruption hands over a party, and signing runs the shared ledger transition on the
    number of parties with a verifying certificate for exactly `(deploymentId, intent)`. -/
def certCustodyStep {PK D Sig Cert : Type} [DecidableEq D] (L : CustodyCertLayer Cert)
    (forge : CertCustodyState PK D Sig Cert → Nat → Nat → CustodyIntent → Cert)
    (S : CustodyDigestScheme D) (oracleSign : D → Sig)
    (c : CertCustodyState PK D Sig Cert) (inp : CustodyInput) :
    Option (CertCustodyState PK D Sig Cert × CustodyOutcome Sig) :=
  match inp with
  | .approve p dep i =>
    if p < c.ledger.quorum.numParties ∧ p ∉ c.corruptParties ∧ dep = c.ledger.deploymentId then
      some ({ c with pool := (true, L.issue p dep i) :: c.pool }, .approvalRecorded)
    else none
  | .advApprove p dep i =>
    if dep = c.ledger.deploymentId ∧ L.valid (certAdvCert L forge c p dep i) = true ∧
        L.claim (certAdvCert L forge c p dep i) = CustodyApproval.mk p dep i then
      some ({ c with pool := (false, certAdvCert L forge c p dep i) :: c.pool }, .approvalRecorded)
    else none
  | .corrupt p =>
    if p < c.ledger.quorum.numParties ∧ p ∉ c.corruptParties ∧
        c.corruptParties.length + 1 < c.ledger.quorum.threshold then
      some ({ c with corruptParties := p :: c.corruptParties },
            .corrupted (custodyRevealed (certRecords L true c.pool) p))
    else none
  | .sign dep i ab =>
    (custodyLedgerSign S oracleSign c.ledger
      (certApprovers L c.ledger.quorum.numParties c.pool c.ledger.deploymentId i).length
      dep i ab).map (fun r => ({ c with ledger := r.1 }, r.2))

def certCustodyMachine {PK D Sig Cert : Type} [DecidableEq D] (L : CustodyCertLayer Cert)
    (forge : CertCustodyState PK D Sig Cert → Nat → Nat → CustodyIntent → Cert)
    (S : CustodyDigestScheme D) (oracleSign : D → Sig)
    (dep₀ : Nat) (pk₀ : PK) (quorum₀ : CustodyQuorumProfile) :
    Qsag.Spec.Machine (CertCustodyState PK D Sig Cert) CustodyInput (CustodyOutcome Sig) where
  Init c := c = CertCustodyState.init dep₀ pk₀ quorum₀
  step := certCustodyStep L forge S oracleSign
  errStep c _ := c

/-- Abstraction to the ideal state: a pooled certificate becomes the permit it asserts. -/
def certCustodyAbs {PK D Sig Cert : Type} (L : CustodyCertLayer Cert)
    (c : CertCustodyState PK D Sig Cert) : IdealCustodyState PK D Sig :=
  { ledger := c.ledger
    corruptParties := c.corruptParties
    honestApprovals := certRecords L true c.pool
    corruptApprovals := certRecords L false c.pool }

/-- **Obligation of the certificate layer (unforgeability).** Whatever the coordinator state, the
    adversary's certificate for a party it has not corrupted does not both verify and assert that
    party's permit. For a signature-based layer this is existential unforgeability of the
    custodians' signatures, taken as an exact (zero-advantage) property. -/
structure CustodyUnforgeable {PK D Sig Cert : Type} (L : CustodyCertLayer Cert)
    (forge : CertCustodyState PK D Sig Cert → Nat → Nat → CustodyIntent → Cert) : Prop where
  honest_not_forged : ∀ (c : CertCustodyState PK D Sig Cert) (p dep : Nat) (i : CustodyIntent),
    (∀ tc ∈ c.pool, L.valid tc.2 = true) → p ∉ c.corruptParties →
    ¬ (L.valid (forge c p dep i) = true ∧ L.claim (forge c p dep i) = CustodyApproval.mk p dep i)

/-- A certificate layer whose certificates are the permits themselves; `none` never verifies. -/
def transparentCertLayer : CustodyCertLayer (Option CustodyApproval) where
  claim c := c.getD (CustodyApproval.mk 0 0 ⟨0, 0, 0, 0, []⟩)
  valid c := c.isSome
  issue p dep i := some (CustodyApproval.mk p dep i)
  issue_valid _ _ _ := rfl
  issue_claim _ _ _ := rfl

/-- The unforgeability obligation is satisfiable. -/
theorem transparentCertLayer_unforgeable {PK D Sig : Type} :
    CustodyUnforgeable (PK := PK) (D := D) (Sig := Sig) transparentCertLayer
      (fun _ _ _ _ => none) :=
  ⟨fun _ _ _ _ _ _ h => Bool.noConfusion (show false = true from h.1)⟩

private theorem cert_if_pos {α : Type} {p : Prop} [Decidable p] (hp : p) (a b : α) :
    (if p then a else b) = a := by
  cases ‹Decidable p› with
  | isTrue _ => rfl
  | isFalse hn => exact False.elim (hn hp)

private theorem cert_if_neg {α : Type} {p : Prop} [Decidable p] (hnp : ¬ p) (a b : α) :
    (if p then a else b) = b := by
  cases ‹Decidable p› with
  | isTrue hp => exact False.elim (hnp hp)
  | isFalse _ => rfl

private theorem cert_bool_eq_of_iff : ∀ {a b : Bool}, (a = true ↔ b = true) → a = b
  | true, true, _ => rfl
  | false, false, _ => rfl
  | true, false, h => (h.mp rfl).symm
  | false, true, h => h.mpr rfl

private theorem cert_filter_congr {α : Type} {p q : α → Bool} :
    ∀ (l : List α), (∀ x ∈ l, p x = q x) → l.filter p = l.filter q
  | [], _ => rfl
  | x :: xs, h => by
    have hx := h x List.mem_cons_self
    have ih := cert_filter_congr xs (fun y hy => h y (List.mem_cons_of_mem _ hy))
    rw [List.filter_cons, List.filter_cons, hx, ih]

/-- With every pooled certificate verifying, the coordinator's per-party check agrees with
    permit membership in the abstracted state. -/
private theorem certVoted_iff {Cert : Type} (L : CustodyCertLayer Cert)
    {pool : List (Bool × Cert)} (hValid : ∀ tc ∈ pool, L.valid tc.2 = true)
    (p dep : Nat) (i : CustodyIntent) :
    certVoted L pool p dep i = true ↔
      (CustodyApproval.mk p dep i ∈ certRecords L true pool ∨
        CustodyApproval.mk p dep i ∈ certRecords L false pool) := by
  unfold certVoted certRecords
  constructor
  · intro h
    obtain ⟨tc, hm, hp⟩ := List.any_eq_true.mp h
    obtain ⟨_, hc⟩ := Bool.and_eq_true_iff.mp hp
    have hcl : L.claim tc.2 = CustodyApproval.mk p dep i := of_decide_eq_true hc
    cases hb : tc.1 with
    | true =>
      exact .inl (List.mem_map.mpr ⟨tc, List.mem_filter.mpr ⟨hm, beq_iff_eq.mpr hb⟩, hcl⟩)
    | false =>
      exact .inr (List.mem_map.mpr ⟨tc, List.mem_filter.mpr ⟨hm, beq_iff_eq.mpr hb⟩, hcl⟩)
  · intro h
    have key : ∀ t : Bool,
        CustodyApproval.mk p dep i ∈
          (pool.filter (fun tc => tc.1 == t)).map (fun tc => L.claim tc.2) →
        pool.any (fun tc =>
          L.valid tc.2 && decide (L.claim tc.2 = CustodyApproval.mk p dep i)) = true := by
      intro t ht
      obtain ⟨tc, hf, hcl⟩ := List.mem_map.mp ht
      obtain ⟨hm, _⟩ := List.mem_filter.mp hf
      exact List.any_eq_true.mpr
        ⟨tc, hm, Bool.and_eq_true_iff.mpr ⟨hValid tc hm, decide_eq_true hcl⟩⟩
    rcases h with h | h
    · exact key true h
    · exact key false h

private theorem certApprovers_eq {Cert : Type} (L : CustodyCertLayer Cert)
    {pool : List (Bool × Cert)} (hValid : ∀ tc ∈ pool, L.valid tc.2 = true)
    (n dep : Nat) (i : CustodyIntent) :
    certApprovers L n pool dep i =
      custodyApprovers n (certRecords L true pool) (certRecords L false pool) dep i := by
  unfold certApprovers custodyApprovers
  apply cert_filter_congr
  intro p _
  exact cert_bool_eq_of_iff ((certVoted_iff L hValid p dep i).trans
    ⟨fun h => Bool.or_eq_true_iff.mpr (h.imp decide_eq_true decide_eq_true),
     fun h => (Bool.or_eq_true_iff.mp h).imp of_decide_eq_true of_decide_eq_true⟩)

section Sim

variable {PK D Sig Cert : Type} [DecidableEq D]
variable {L : CustodyCertLayer Cert}
variable {forge : CertCustodyState PK D Sig Cert → Nat → Nat → CustodyIntent → Cert}
variable {S : CustodyDigestScheme D} {oracleSign : D → Sig}

/-- Accepted coordinator steps keep every pooled certificate verifying. -/
private theorem certCustodyStep_valid
    {c c' : CertCustodyState PK D Sig Cert} {inp : CustodyInput} {out : CustodyOutcome Sig}
    (hValid : ∀ tc ∈ c.pool, L.valid tc.2 = true)
    (h : certCustodyStep L forge S oracleSign c inp = some (c', out)) :
    ∀ tc ∈ c'.pool, L.valid tc.2 = true := by
  cases inp with
  | approve p dep i =>
    unfold certCustodyStep at h
    dsimp only at h
    by_cases hg : p < c.ledger.quorum.numParties ∧ p ∉ c.corruptParties ∧
        dep = c.ledger.deploymentId
    · rw [cert_if_pos hg] at h
      cases h
      intro tc htc
      rcases List.mem_cons.mp htc with hEq | hTail
      · rw [hEq]
        exact L.issue_valid p dep i
      · exact hValid tc hTail
    · rw [cert_if_neg hg] at h
      cases h
  | advApprove p dep i =>
    unfold certCustodyStep at h
    dsimp only at h
    by_cases hg : dep = c.ledger.deploymentId ∧ L.valid (certAdvCert L forge c p dep i) = true ∧
        L.claim (certAdvCert L forge c p dep i) = CustodyApproval.mk p dep i
    · rw [cert_if_pos hg] at h
      cases h
      intro tc htc
      rcases List.mem_cons.mp htc with hEq | hTail
      · rw [hEq]
        exact hg.2.1
      · exact hValid tc hTail
    · rw [cert_if_neg hg] at h
      cases h
  | corrupt p =>
    unfold certCustodyStep at h
    dsimp only at h
    by_cases hg : p < c.ledger.quorum.numParties ∧ p ∉ c.corruptParties ∧
        c.corruptParties.length + 1 < c.ledger.quorum.threshold
    · rw [cert_if_pos hg] at h
      cases h
      exact hValid
    · rw [cert_if_neg hg] at h
      cases h
  | sign dep i ab =>
    unfold certCustodyStep at h
    dsimp only at h
    cases hL : custodyLedgerSign S oracleSign c.ledger
        (certApprovers L c.ledger.quorum.numParties c.pool c.ledger.deploymentId i).length
        dep i ab with
    | none =>
      rw [hL] at h
      cases h
    | some r =>
      rw [hL] at h
      cases h
      exact hValid

/-- Lockstep: under unforgeability, a coordinator step and the ideal step on the abstracted state
    accept the same inputs with the same outcome and commuting successor states. -/
private theorem certCustodyStep_abs (hUnf : CustodyUnforgeable L forge)
    (c : CertCustodyState PK D Sig Cert) (inp : CustodyInput)
    (hValid : ∀ tc ∈ c.pool, L.valid tc.2 = true) :
    (certCustodyStep L forge S oracleSign c inp).map (fun r => (certCustodyAbs L r.1, r.2)) =
      idealCustodyStep S oracleSign (certCustodyAbs L c) inp := by
  cases inp with
  | approve p dep i =>
    by_cases hg : p < c.ledger.quorum.numParties ∧ p ∉ c.corruptParties ∧
        dep = c.ledger.deploymentId
    · have hC : certCustodyStep L forge S oracleSign c (.approve p dep i) =
          some ({ c with pool := (true, L.issue p dep i) :: c.pool }, .approvalRecorded) := by
        unfold certCustodyStep
        dsimp only
        exact cert_if_pos hg _ _
      have hA : idealCustodyStep S oracleSign (certCustodyAbs L c) (.approve p dep i) =
          some ({ certCustodyAbs L c with
                  honestApprovals :=
                    CustodyApproval.mk p dep i :: (certCustodyAbs L c).honestApprovals },
                .approvalRecorded) := by
        unfold idealCustodyStep
        dsimp only
        exact cert_if_pos hg _ _
      rw [hC, hA]
      exact congrArg
        (fun a => some ((⟨c.ledger, c.corruptParties, a :: certRecords L true c.pool,
          certRecords L false c.pool⟩ : IdealCustodyState PK D Sig),
          (CustodyOutcome.approvalRecorded : CustodyOutcome Sig)))
        (L.issue_claim p dep i)
    · have hC : certCustodyStep L forge S oracleSign c (.approve p dep i) = none := by
        unfold certCustodyStep
        dsimp only
        exact cert_if_neg hg _ _
      have hA : idealCustodyStep S oracleSign (certCustodyAbs L c) (.approve p dep i) = none := by
        unfold idealCustodyStep
        dsimp only
        exact cert_if_neg hg _ _
      rw [hC, hA]
      rfl
  | advApprove p dep i =>
    by_cases hp : p ∈ c.corruptParties
    · have hCert : certAdvCert L forge c p dep i = L.issue p dep i := cert_if_pos hp _ _
      by_cases hd : dep = c.ledger.deploymentId
      · have hgC : dep = c.ledger.deploymentId ∧
            L.valid (certAdvCert L forge c p dep i) = true ∧
            L.claim (certAdvCert L forge c p dep i) = CustodyApproval.mk p dep i := by
          rw [hCert]
          exact ⟨hd, L.issue_valid p dep i, L.issue_claim p dep i⟩
        have hC : certCustodyStep L forge S oracleSign c (.advApprove p dep i) =
            some ({ c with pool := (false, certAdvCert L forge c p dep i) :: c.pool },
                  .approvalRecorded) := by
          unfold certCustodyStep
          dsimp only
          exact cert_if_pos hgC _ _
        have hA : idealCustodyStep S oracleSign (certCustodyAbs L c) (.advApprove p dep i) =
            some ({ certCustodyAbs L c with
                    corruptApprovals :=
                      CustodyApproval.mk p dep i :: (certCustodyAbs L c).corruptApprovals },
                  .approvalRecorded) := by
          unfold idealCustodyStep
          dsimp only
          exact cert_if_pos (And.intro hp hd) _ _
        rw [hC, hA]
        exact congrArg
          (fun a => some ((⟨c.ledger, c.corruptParties, certRecords L true c.pool,
            a :: certRecords L false c.pool⟩ : IdealCustodyState PK D Sig),
            (CustodyOutcome.approvalRecorded : CustodyOutcome Sig)))
          hgC.2.2
      · have hC : certCustodyStep L forge S oracleSign c (.advApprove p dep i) = none := by
          unfold certCustodyStep
          dsimp only
          exact cert_if_neg (fun h => hd h.1) _ _
        have hA : idealCustodyStep S oracleSign (certCustodyAbs L c) (.advApprove p dep i) =
            none := by
          unfold idealCustodyStep
          dsimp only
          exact cert_if_neg (fun h => hd h.2) _ _
        rw [hC, hA]
        rfl
    · have hCert : certAdvCert L forge c p dep i = forge c p dep i := cert_if_neg hp _ _
      have hC : certCustodyStep L forge S oracleSign c (.advApprove p dep i) = none := by
        unfold certCustodyStep
        dsimp only
        refine cert_if_neg (fun h => ?_) _ _
        rw [hCert] at h
        exact hUnf.honest_not_forged c p dep i hValid hp h.2
      have hA : idealCustodyStep S oracleSign (certCustodyAbs L c) (.advApprove p dep i) =
          none := by
        unfold idealCustodyStep
        dsimp only
        exact cert_if_neg (fun h => hp h.1) _ _
      rw [hC, hA]
      rfl
  | corrupt p =>
    by_cases hg : p < c.ledger.quorum.numParties ∧ p ∉ c.corruptParties ∧
        c.corruptParties.length + 1 < c.ledger.quorum.threshold
    · have hC : certCustodyStep L forge S oracleSign c (.corrupt p) =
          some ({ c with corruptParties := p :: c.corruptParties },
                .corrupted (custodyRevealed (certRecords L true c.pool) p)) := by
        unfold certCustodyStep
        dsimp only
        exact cert_if_pos hg _ _
      have hA : idealCustodyStep S oracleSign (certCustodyAbs L c) (.corrupt p) =
          some ({ certCustodyAbs L c with corruptParties := p :: c.corruptParties },
                .corrupted (custodyRevealed (certRecords L true c.pool) p)) := by
        unfold idealCustodyStep
        dsimp only
        exact cert_if_pos hg _ _
      rw [hC, hA]
      rfl
    · have hC : certCustodyStep L forge S oracleSign c (.corrupt p) = none := by
        unfold certCustodyStep
        dsimp only
        exact cert_if_neg hg _ _
      have hA : idealCustodyStep S oracleSign (certCustodyAbs L c) (.corrupt p) = none := by
        unfold idealCustodyStep
        dsimp only
        exact cert_if_neg hg _ _
      rw [hC, hA]
      rfl
  | sign dep i ab =>
    have hN := certApprovers_eq L hValid c.ledger.quorum.numParties c.ledger.deploymentId i
    change Option.map _ (Option.map _ (custodyLedgerSign S oracleSign c.ledger
        (certApprovers L c.ledger.quorum.numParties c.pool c.ledger.deploymentId i).length
        dep i ab)) =
      Option.map _ (custodyLedgerSign S oracleSign c.ledger
        (custodyApprovers c.ledger.quorum.numParties (certRecords L true c.pool)
          (certRecords L false c.pool) c.ledger.deploymentId i).length dep i ab)
    rw [hN]
    cases custodyLedgerSign S oracleSign c.ledger
        (custodyApprovers c.ledger.quorum.numParties (certRecords L true c.pool)
          (certRecords L false c.pool) c.ledger.deploymentId i).length dep i ab with
    | none => rfl
    | some r => rfl

/-- **Certificate-Quorum Coordinator Refinement (`certCustody_refines_idealCustody`)**: under the
    certificate layer's signing-correctness laws and the unforgeability obligation, the coordinator
    that counts verifying certificates for exactly `(deploymentId, intent)` refines
    `Spec.idealCustodyMachine` in lockstep (`Spec.Refines`), corruption steps included. -/
def certCustody_refines_idealCustody (L : CustodyCertLayer Cert)
    (forge : CertCustodyState PK D Sig Cert → Nat → Nat → CustodyIntent → Cert)
    (hUnf : CustodyUnforgeable L forge)
    (S : CustodyDigestScheme D) (oracleSign : D → Sig)
    (dep₀ : Nat) (pk₀ : PK) (quorum₀ : CustodyQuorumProfile) :
    certCustodyMachine L forge S oracleSign dep₀ pk₀ quorum₀ ⊑
      idealCustodyMachine S oracleSign dep₀ pk₀ quorum₀ :=
  Qsag.Spec.LockstepSim.toRefines
    { Inv := fun c => ∀ tc ∈ c.pool, L.valid tc.2 = true
      abs := certCustodyAbs L
      init_inv := fun {c₀} hInit => by
        have h0 : c₀ = CertCustodyState.init dep₀ pk₀ quorum₀ := hInit
        subst h0
        exact ⟨fun _ h => False.elim (List.not_mem_nil h), rfl⟩
      step_eq := fun {c} inp hI => by
        have hm := certCustodyStep_abs (S := S) (oracleSign := oracleSign) hUnf c inp hI
        cases hC : (certCustodyMachine L forge S oracleSign dep₀ pk₀ quorum₀).step c inp with
        | none =>
          have hC' : certCustodyStep L forge S oracleSign c inp = none := hC
          rw [hC'] at hm
          exact ⟨hI, hm.symm, rfl⟩
        | some r =>
          rcases r with ⟨c', out⟩
          have hC' : certCustodyStep L forge S oracleSign c inp = some (c', out) := hC
          rw [hC'] at hm
          exact ⟨certCustodyStep_valid hI hC', hm.symm⟩ }

/-- Every coordinator trace from an invariant state is an ideal trace between the abstractions. -/
private theorem certCustody_validTrace_abs (hUnf : CustodyUnforgeable L forge)
    {dep₀ : Nat} {pk₀ : PK} {quorum₀ : CustodyQuorumProfile}
    {c c' : CertCustodyState PK D Sig Cert} {tr : List (CustodyInput × CustodyOutcome Sig)}
    (hValid : ∀ tc ∈ c.pool, L.valid tc.2 = true)
    (hTr : (certCustodyMachine L forge S oracleSign dep₀ pk₀ quorum₀).ValidTrace c tr c') :
    (idealCustodyMachine S oracleSign dep₀ pk₀ quorum₀).ValidTrace
      (certCustodyAbs L c) tr (certCustodyAbs L c') := by
  induction hTr with
  | nil _ => exact .nil _
  | @accept s s' _ inp out _ hStep _ ih =>
    have hStep' : certCustodyStep L forge S oracleSign s inp = some (s', out) := hStep
    have hm := certCustodyStep_abs (S := S) (oracleSign := oracleSign) hUnf s inp hValid
    rw [hStep'] at hm
    exact .accept hm.symm (ih (certCustodyStep_valid hValid hStep'))
  | @reject s _ inp _ hNone _ ih =>
    have hNone' : certCustodyStep L forge S oracleSign s inp = none := hNone
    have hm := certCustodyStep_abs (S := S) (oracleSign := oracleSign) hUnf s inp hValid
    rw [hNone'] at hm
    exact .reject inp hm.symm (ih hValid)

/-- **Honest authorization of every coordinator signature.** In any coordinator trace, a released
    signature is the oracle's signature on `digest dep₀ i`, and the trace contains custodian `p`'s
    own accepted `.approve p dep₀ i`. -/
theorem certCustody_trace_release_honestly_approved (hUnf : CustodyUnforgeable L forge)
    {dep₀ : Nat} {pk₀ : PK} {quorum₀ : CustodyQuorumProfile}
    {tr : List (CustodyInput × CustodyOutcome Sig)}
    {dep : Nat} {i : CustodyIntent} {ab : Bool} {sig : Sig}
    (hAdmits : (certCustodyMachine L forge S oracleSign dep₀ pk₀ quorum₀).AdmitsTrace tr)
    (hEv : (CustodyInput.sign dep i ab, CustodyOutcome.released sig) ∈ tr) :
    dep = dep₀ ∧ sig = oracleSign (S.digest dep₀ i) ∧
    ∃ p, p < quorum₀.numParties ∧
      (CustodyInput.approve p dep₀ i, (CustodyOutcome.approvalRecorded : CustodyOutcome Sig)) ∈ tr :=
  idealCustody_admitsTrace_release_honestly_approved
    ((certCustody_refines_idealCustody L forge hUnf S oracleSign dep₀ pk₀ quorum₀).preserve_admitsTrace
      hAdmits) hEv

/-- **Coordinator expenditure and certificate provenance.** On every reachable coordinator state
    the amount spent is the sum of `intent.spend` over the authorized intents and within the
    budget, and every WAL record carries the oracle's signature on `digest dep₀ intent` for an
    intent certified through an enrolled custodian's own port. -/
theorem certCustody_reachable_spend_and_provenance (hUnf : CustodyUnforgeable L forge)
    {dep₀ : Nat} {pk₀ : PK} {quorum₀ : CustodyQuorumProfile}
    {c : CertCustodyState PK D Sig Cert}
    (hR : (certCustodyMachine L forge S oracleSign dep₀ pk₀ quorum₀).Reachable c) :
    c.ledger.spent = (c.ledger.authorized.map CustodyIntent.spend).sum ∧
    c.ledger.spent ≤ quorum₀.spendCap ∧
    ∀ r ∈ c.ledger.releasedHistory,
      r.sig = oracleSign (S.digest dep₀ r.intent) ∧
      ∃ p, p < quorum₀.numParties ∧
        CustodyApproval.mk p dep₀ r.intent ∈ certRecords L true c.pool := by
  obtain ⟨c₀, tr, hInit, hTr⟩ := hR
  have h0 : c₀ = CertCustodyState.init dep₀ pk₀ quorum₀ := hInit
  subst h0
  have hIdeal : (idealCustodyMachine S oracleSign dep₀ pk₀ quorum₀).Reachable
      (certCustodyAbs L c) :=
    ⟨certCustodyAbs L (CertCustodyState.init dep₀ pk₀ quorum₀), tr, rfl,
      certCustody_validTrace_abs hUnf (fun _ h => False.elim (List.not_mem_nil h)) hTr⟩
  obtain ⟨hAcc, hBud, _, _⟩ := idealCustody_reachable_spend_accounting hIdeal
  exact ⟨hAcc, hBud, fun r hr => idealCustody_reachable_release_honestly_approved hIdeal hr⟩

end Sim

end CertCustody

#verify_constructive
  Qsag.Top.rssSharedRelease_preserves_traces
  Qsag.Top.elf_to_idealTsig_trace_inclusion
  Qsag.Top.separated_custody_provenance_and_release_chain
  Qsag.Top.threshold_durable_feedback_and_resource_burn_chain
  Qsag.Top.posix_wal_commit_and_anchor_rollback_fence
  Qsag.Top.rss_participant_network_gate_and_signing_execution_chain
  Qsag.Top.gate_batches_and_quorum_switching_disjointness
  Qsag.Top.transparentCertLayer_unforgeable
  Qsag.Top.certCustody_trace_release_honestly_approved
  Qsag.Top.certCustody_reachable_spend_and_provenance

end Qsag.Top
end
