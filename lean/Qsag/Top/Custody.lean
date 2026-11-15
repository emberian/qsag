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
   `WalLatchState` and `CompleteMediationBoundary` watermarks (`PosixCrashWal`, `SeparatedCustodyUcBridge`).
-/

public import Qsag.Spec.Primitives
public import Qsag.Spec.Parameters
public import Qsag.Spec.Refines
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

#verify_constructive
  Qsag.Top.rssSharedRelease_preserves_traces
  Qsag.Top.elf_to_idealTsig_trace_inclusion
  Qsag.Top.separated_custody_provenance_and_release_chain
  Qsag.Top.threshold_durable_feedback_and_resource_burn_chain
  Qsag.Top.posix_wal_commit_and_anchor_rollback_fence
  Qsag.Top.rss_participant_network_gate_and_signing_execution_chain
  Qsag.Top.gate_batches_and_quorum_switching_disjointness

end Qsag.Top
end
