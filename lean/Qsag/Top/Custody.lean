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
5. A certificate-pool coordinator model with a raw certificate interface (`certCustodyMachine`:
   custodian certificates bound to `(deploymentId, intent)`, arbitrary submitted certificates,
   adaptive corruption, the ledger transition `Spec.custodyLedgerSign`). On traces without a forgery
   event it is simulated by `Spec.idealCustodyMachine`, and `Pr[unsafe release] ≤ Pr[forgery event]`
   (`certCustody_unsafe_release_le_forgery`).
6. The real coordinator `Custody.submitRecorded` in a world with production signing and adaptive
   corruption (`sepCustodyMachine`), related to `Spec.idealCustodyMachine` on runs satisfying
   `SeparatedCustodyRunAssumptions` (`separatedCustody_refines_idealCustody_of`). The ELF, MIR,
   `IdealTsig`, RSS and WAL machines of items 1–4 are not connected to `Spec.idealCustodyMachine`.
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

/-! ## 7. Certificate-Pool Coordinator with a Raw Certificate Interface -/

section CertCustody

open Qsag.Spec

/-- Certificate layer shared by the custodians and the coordinator. `claim c` is the permit a
    certificate asserts (party, deployment, full intent), `valid c` is the coordinator's
    verification, and `issue p dep i` is party `p`'s signing of `(dep, i)` under its own key.
    The two laws are correctness of honest signing; unforgeability is not a law of the layer. -/
structure CustodyCertLayer (Cert : Type) where
  claim : Cert → CustodyApproval
  valid : Cert → Bool
  issue : Nat → Nat → CustodyIntent → Cert
  issue_valid : ∀ (p dep : Nat) (i : CustodyIntent), valid (issue p dep i) = true
  issue_claim : ∀ (p dep : Nat) (i : CustodyIntent),
    claim (issue p dep i) = CustodyApproval.mk p dep i

/-- Inputs of the certificate-pool coordinator. `.submit` is the network interface: it carries an
    arbitrary certificate, whoever produced it. -/
inductive CertCustodyInput (Cert : Type) where
  | approve (party deploymentId : Nat) (intent : CustodyIntent)
  | submit (cert : Cert)
  | corrupt (party : Nat)
  | sign (deploymentId : Nat) (intent : CustodyIntent) (abortBeforeRelease : Bool)

/-- State of the certificate world. The coordinator's decisions read `ledger` and `pool` only.
    `corruptParties` and `issued` (what each custodian signed through its own port) are history of
    the world. `advClaims` and `forgeries` are bookkeeping for the analysis: the permits submitted
    for already corrupted parties, and the admitted certificates that assert a permit of an
    uncorrupted party which that party never issued. -/
structure CertCustodyState (PK D Sig Cert : Type) where
  ledger : CustodyLedger PK D Sig
  corruptParties : List Nat
  pool : List Cert
  issued : List CustodyApproval
  advClaims : List CustodyApproval
  forgeries : List Cert

def CertCustodyState.init {PK D Sig Cert : Type}
    (dep : Nat) (pk : PK) (quorum : CustodyQuorumProfile) : CertCustodyState PK D Sig Cert :=
  { ledger := (IdealCustodyState.init (D := D) (Sig := Sig) dep pk quorum).ledger
    corruptParties := []
    pool := []
    issued := []
    advClaims := []
    forgeries := [] }

/-- The coordinator's per-party check: some pooled certificate asserts exactly `(p, dep, i)`.
    Certificates are verified when they are admitted to the pool. -/
def certVoted {Cert : Type} (L : CustodyCertLayer Cert) (pool : List Cert)
    (p dep : Nat) (i : CustodyIntent) : Bool :=
  pool.any (fun x => decide (L.claim x = CustodyApproval.mk p dep i))

/-- Enrolled parties with a pooled certificate for exactly `(dep, i)`, each counted once. -/
def certApprovers {Cert : Type} (L : CustodyCertLayer Cert) (numParties : Nat)
    (pool : List Cert) (dep : Nat) (i : CustodyIntent) : List Nat :=
  (List.range numParties).filter (fun p => certVoted L pool p dep i)

def certAdvClaims {PK D Sig Cert : Type} (L : CustodyCertLayer Cert)
    (c : CertCustodyState PK D Sig Cert) (x : Cert) : List CustodyApproval :=
  if (L.claim x).party ∈ c.corruptParties then L.claim x :: c.advClaims else c.advClaims

/-- The forgery event of one admission: `x` asserts a permit of a party that is not corrupted and
    never issued that permit. A relayed or replayed honest certificate is not a forgery. -/
def certForgeries {PK D Sig Cert : Type} (L : CustodyCertLayer Cert)
    (c : CertCustodyState PK D Sig Cert) (x : Cert) : List Cert :=
  if (L.claim x).party ∉ c.corruptParties ∧ L.claim x ∉ c.issued then x :: c.forgeries
  else c.forgeries

/-- Transition of the certificate world. A custodian signs through its own port; the coordinator
    admits any submitted certificate that verifies for this deployment; corruption hands a party
    over; signing runs the ledger transition on the number of enrolled parties with a pooled
    certificate for exactly `(deploymentId, intent)`. -/
def certCustodyStep {PK D Sig Cert : Type} [DecidableEq D] (L : CustodyCertLayer Cert)
    (S : CustodyDigestScheme D) (oracleSign : D → Sig)
    (c : CertCustodyState PK D Sig Cert) (inp : CertCustodyInput Cert) :
    Option (CertCustodyState PK D Sig Cert × CustodyOutcome Sig) :=
  match inp with
  | .approve p dep i =>
    if p < c.ledger.quorum.numParties ∧ p ∉ c.corruptParties ∧ dep = c.ledger.deploymentId then
      some ({ c with issued := CustodyApproval.mk p dep i :: c.issued }, .approvalRecorded)
    else none
  | .submit x =>
    if L.valid x = true ∧ (L.claim x).deploymentId = c.ledger.deploymentId then
      some ({ c with
              pool := x :: c.pool
              advClaims := certAdvClaims L c x
              forgeries := certForgeries L c x }, .approvalRecorded)
    else none
  | .corrupt p =>
    if p < c.ledger.quorum.numParties ∧ p ∉ c.corruptParties ∧
        c.corruptParties.length + 1 < c.ledger.quorum.threshold then
      some ({ c with corruptParties := p :: c.corruptParties },
            .corrupted (custodyRevealed c.issued p))
    else none
  | .sign dep i ab =>
    (custodyLedgerSign S oracleSign c.ledger
      (certApprovers L c.ledger.quorum.numParties c.pool c.ledger.deploymentId i).length
      dep i ab).map (fun r => ({ c with ledger := r.1 }, r.2))

def certCustodyMachine {PK D Sig Cert : Type} [DecidableEq D] (L : CustodyCertLayer Cert)
    (S : CustodyDigestScheme D) (oracleSign : D → Sig)
    (dep₀ : Nat) (pk₀ : PK) (quorum₀ : CustodyQuorumProfile) :
    Qsag.Spec.Machine (CertCustodyState PK D Sig Cert) (CertCustodyInput Cert)
      (CustodyOutcome Sig) where
  Init c := c = CertCustodyState.init dep₀ pk₀ quorum₀
  step := certCustodyStep L S oracleSign
  errStep c _ := c

/-- Abstraction to the ideal state: honest permits are the issued ones. -/
def certCustodyAbs {PK D Sig Cert : Type}
    (c : CertCustodyState PK D Sig Cert) : IdealCustodyState PK D Sig :=
  { ledger := c.ledger
    corruptParties := c.corruptParties
    honestApprovals := c.issued
    corruptApprovals := c.advClaims }

/-- Partial decoder from raw inputs to ideal inputs. A submitted certificate for a corrupted party
    is an adversarial approval; a submitted certificate for an uncorrupted party is a delivery and
    has no ideal counterpart (the ideal permit was recorded when the party issued it). -/
def certDecode {PK D Sig Cert : Type} (L : CustodyCertLayer Cert)
    (c : CertCustodyState PK D Sig Cert) : CertCustodyInput Cert → Option CustodyInput
  | .approve p dep i => some (.approve p dep i)
  | .submit x =>
    if (L.claim x).party ∈ c.corruptParties then
      some (.advApprove (L.claim x).party (L.claim x).deploymentId (L.claim x).intent)
    else none
  | .corrupt p => some (.corrupt p)
  | .sign dep i ab => some (.sign dep i ab)

/-- Every pooled certificate asserts a permit that was issued by its party or submitted for a
    corrupted party. -/
def CertPoolAccounted {PK D Sig Cert : Type} (L : CustodyCertLayer Cert)
    (c : CertCustodyState PK D Sig Cert) : Prop :=
  ∀ x ∈ c.pool, L.claim x ∈ c.issued ∨ L.claim x ∈ c.advClaims

/-- One simulated step: the decoded input drives the ideal machine between the abstractions with
    the same outcome; an undecoded (delivery) input leaves the abstraction unchanged. -/
def CertSimStep {PK D Sig Cert : Type} [DecidableEq D]
    (S : CustodyDigestScheme D) (oracleSign : D → Sig)
    (c c' : CertCustodyState PK D Sig Cert) (out : CustodyOutcome Sig) :
    Option CustodyInput → Prop
  | some inp' =>
    idealCustodyStep S oracleSign (certCustodyAbs c) inp' = some (certCustodyAbs c', out)
  | none => certCustodyAbs c' = certCustodyAbs c

/-- A release in the WAL whose intent no enrolled custodian issued a certificate for. -/
def certUnsafeRelease {PK D Sig Cert : Type} (numParties dep : Nat)
    (c : CertCustodyState PK D Sig Cert) : Bool :=
  c.ledger.releasedHistory.any (fun r =>
    !(List.range numParties).any (fun p => decide (CustodyApproval.mk p dep r.intent ∈ c.issued)))

/-- State after feeding `inps` in order from the initial state (rejected inputs are skipped). -/
def certRun {PK D Sig Cert : Type} [DecidableEq D] (L : CustodyCertLayer Cert)
    (S : CustodyDigestScheme D) (oracleSign : D → Sig)
    (dep₀ : Nat) (pk₀ : PK) (quorum₀ : CustodyQuorumProfile)
    (inps : List (CertCustodyInput Cert)) : CertCustodyState PK D Sig Cert :=
  inps.foldl
    (fun c inp => ((certCustodyMachine L S oracleSign dep₀ pk₀ quorum₀).runStep c inp).1)
    (CertCustodyState.init dep₀ pk₀ quorum₀)

/-- A toy MAC-style layer: party `p`'s certificate for a permit is the permit tagged with `key p`.
    Tags reveal the key, so this layer is unforgeable only against adversaries whose submissions do
    not depend on the keys. -/
def macCertLayer (key : Nat → Nat) : CustodyCertLayer (Nat × CustodyApproval) where
  claim c := c.2
  valid c := c.1 == key c.2.party
  issue p dep i := (key p, CustodyApproval.mk p dep i)
  issue_valid _ _ _ := beq_self_eq_true _
  issue_claim _ _ _ := rfl

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

private theorem cert_exists_of_not_isEmpty {α : Type} {l : List α}
    (h : (!l.isEmpty) = true) : ∃ x, x ∈ l := by
  cases l with
  | nil => cases h
  | cons x _ => exact ⟨x, List.mem_cons_self⟩

private theorem certForgeries_nil {PK D Sig Cert : Type} {L : CustodyCertLayer Cert}
    {c : CertCustodyState PK D Sig Cert} {x : Cert} (h : certForgeries L c x = []) :
    c.forgeries = [] ∧ ((L.claim x).party ∈ c.corruptParties ∨ L.claim x ∈ c.issued) := by
  unfold certForgeries at h
  by_cases hc : (L.claim x).party ∉ c.corruptParties ∧ L.claim x ∉ c.issued
  · rw [cert_if_pos hc] at h
    exact absurd h (List.cons_ne_nil _ _)
  · rw [cert_if_neg hc] at h
    refine ⟨h, ?_⟩
    by_cases hp : (L.claim x).party ∈ c.corruptParties
    · exact .inl hp
    · by_cases hi : L.claim x ∈ c.issued
      · exact .inr hi
      · exact absurd ⟨hp, hi⟩ hc

private theorem certApprovers_nodup {Cert : Type} (L : CustodyCertLayer Cert) (n : Nat)
    (pool : List Cert) (dep : Nat) (i : CustodyIntent) : (certApprovers L n pool dep i).Nodup := by
  unfold certApprovers
  exact List.Pairwise.filter _ (Qsag.Constructive.nodup_range n)

private theorem certApprovers_spec {Cert : Type} {L : CustodyCertLayer Cert} {n : Nat}
    {pool : List Cert} {dep : Nat} {i : CustodyIntent} {issued adv : List CustodyApproval} {p : Nat}
    (hJ : ∀ x ∈ pool, L.claim x ∈ issued ∨ L.claim x ∈ adv)
    (hp : p ∈ certApprovers L n pool dep i) :
    p < n ∧ (CustodyApproval.mk p dep i ∈ issued ∨ CustodyApproval.mk p dep i ∈ adv) := by
  unfold certApprovers at hp
  obtain ⟨hR, hV⟩ := List.mem_filter.mp hp
  unfold certVoted at hV
  obtain ⟨x, hx, hc⟩ := List.any_eq_true.mp hV
  have hcl : L.claim x = CustodyApproval.mk p dep i := of_decide_eq_true hc
  refine ⟨List.mem_range.mp hR, ?_⟩
  rw [← hcl]
  exact hJ x hx

section Sim

variable {PK D Sig Cert : Type} [DecidableEq D]
variable {L : CustodyCertLayer Cert}
variable {S : CustodyDigestScheme D} {oracleSign : D → Sig}

private theorem certCustodyStep_inv
    {c c' : CertCustodyState PK D Sig Cert} {inp : CertCustodyInput Cert}
    {out : CustodyOutcome Sig}
    (h : certCustodyStep L S oracleSign c inp = some (c', out)) :
    match inp with
    | .approve p dep i =>
      (p < c.ledger.quorum.numParties ∧ p ∉ c.corruptParties ∧ dep = c.ledger.deploymentId) ∧
      c' = { c with issued := CustodyApproval.mk p dep i :: c.issued } ∧
      out = .approvalRecorded
    | .submit x =>
      (L.valid x = true ∧ (L.claim x).deploymentId = c.ledger.deploymentId) ∧
      c' = { c with
             pool := x :: c.pool
             advClaims := certAdvClaims L c x
             forgeries := certForgeries L c x } ∧
      out = .approvalRecorded
    | .corrupt p =>
      (p < c.ledger.quorum.numParties ∧ p ∉ c.corruptParties ∧
        c.corruptParties.length + 1 < c.ledger.quorum.threshold) ∧
      c' = { c with corruptParties := p :: c.corruptParties } ∧
      out = .corrupted (custodyRevealed c.issued p)
    | .sign dep i ab =>
      ∃ L', custodyLedgerSign S oracleSign c.ledger
          (certApprovers L c.ledger.quorum.numParties c.pool c.ledger.deploymentId i).length
          dep i ab = some (L', out) ∧
        c' = { c with ledger := L' } := by
  cases inp with
  | approve p dep i =>
    unfold certCustodyStep at h
    dsimp only at h ⊢
    by_cases hg : p < c.ledger.quorum.numParties ∧ p ∉ c.corruptParties ∧
        dep = c.ledger.deploymentId
    · rw [cert_if_pos hg] at h
      cases h
      exact ⟨hg, rfl, rfl⟩
    · rw [cert_if_neg hg] at h
      cases h
  | submit x =>
    unfold certCustodyStep at h
    dsimp only at h ⊢
    by_cases hg : L.valid x = true ∧ (L.claim x).deploymentId = c.ledger.deploymentId
    · rw [cert_if_pos hg] at h
      cases h
      exact ⟨hg, rfl, rfl⟩
    · rw [cert_if_neg hg] at h
      cases h
  | corrupt p =>
    unfold certCustodyStep at h
    dsimp only at h ⊢
    by_cases hg : p < c.ledger.quorum.numParties ∧ p ∉ c.corruptParties ∧
        c.corruptParties.length + 1 < c.ledger.quorum.threshold
    · rw [cert_if_pos hg] at h
      cases h
      exact ⟨hg, rfl, rfl⟩
    · rw [cert_if_neg hg] at h
      cases h
  | sign dep i ab =>
    unfold certCustodyStep at h
    dsimp only at h ⊢
    cases hL : custodyLedgerSign S oracleSign c.ledger
        (certApprovers L c.ledger.quorum.numParties c.pool c.ledger.deploymentId i).length
        dep i ab with
    | none =>
      rw [hL] at h
      cases h
    | some r =>
      rcases r with ⟨L', out'⟩
      rw [hL] at h
      cases h
      exact ⟨L', rfl, rfl⟩

/-- The forgery log only grows. -/
private theorem certCustodyStep_forgeries_nil
    {c c' : CertCustodyState PK D Sig Cert} {inp : CertCustodyInput Cert}
    {out : CustodyOutcome Sig}
    (h : certCustodyStep L S oracleSign c inp = some (c', out))
    (hNF : c'.forgeries = []) : c.forgeries = [] := by
  have h1 := certCustodyStep_inv h
  cases inp with
  | approve p dep i =>
    dsimp only at h1
    obtain ⟨_, hc, _⟩ := h1
    subst hc
    exact hNF
  | submit x =>
    dsimp only at h1
    obtain ⟨_, hc, _⟩ := h1
    subst hc
    exact (certForgeries_nil hNF).1
  | corrupt p =>
    dsimp only at h1
    obtain ⟨_, hc, _⟩ := h1
    subst hc
    exact hNF
  | sign dep i ab =>
    dsimp only at h1
    obtain ⟨L', _, hc⟩ := h1
    subst hc
    exact hNF

private theorem certCustodyStep_issued_provenance
    {c c' : CertCustodyState PK D Sig Cert} {inp : CertCustodyInput Cert}
    {out : CustodyOutcome Sig} {a : CustodyApproval}
    (h : certCustodyStep L S oracleSign c inp = some (c', out)) (ha : a ∈ c'.issued) :
    a ∈ c.issued ∨
      (inp = .approve a.party a.deploymentId a.intent ∧ out = .approvalRecorded) := by
  have h1 := certCustodyStep_inv h
  cases inp with
  | approve p dep i =>
    dsimp only at h1
    obtain ⟨_, hc, ho⟩ := h1
    subst hc
    rcases List.mem_cons.mp ha with hEq | hT
    · subst hEq
      exact .inr ⟨rfl, ho⟩
    · exact .inl hT
  | submit x =>
    dsimp only at h1
    obtain ⟨_, hc, _⟩ := h1
    subst hc
    exact .inl ha
  | corrupt p =>
    dsimp only at h1
    obtain ⟨_, hc, _⟩ := h1
    subst hc
    exact .inl ha
  | sign dep i ab =>
    dsimp only at h1
    obtain ⟨L', _, hc⟩ := h1
    subst hc
    exact .inl ha

/-- Step simulation on forgery-free steps. The coordinator counts delivered certificates, the
    ideal functionality counts recorded permits; every delivered certificate is accounted for, so
    an accepted concrete signing step is accepted by the ideal functionality with the same result. -/
private theorem certCustodyStep_sim
    {c c' : CertCustodyState PK D Sig Cert} {inp : CertCustodyInput Cert}
    {out : CustodyOutcome Sig}
    (hJ : CertPoolAccounted L c)
    (h : certCustodyStep L S oracleSign c inp = some (c', out))
    (hNF : c'.forgeries = []) :
    CertPoolAccounted L c' ∧ CertSimStep S oracleSign c c' out (certDecode L c inp) := by
  have h1 := certCustodyStep_inv h
  cases inp with
  | approve p dep i =>
    dsimp only at h1
    obtain ⟨hg, hc, ho⟩ := h1
    subst hc
    subst ho
    refine ⟨fun x hx => (hJ x hx).imp (List.mem_cons_of_mem _) id, ?_⟩
    change idealCustodyStep S oracleSign (certCustodyAbs c) (.approve p dep i) = _
    unfold idealCustodyStep
    dsimp only
    exact cert_if_pos hg _ _
  | submit x =>
    dsimp only at h1
    obtain ⟨hg, hc, ho⟩ := h1
    subst hc
    subst ho
    obtain ⟨_, hWho⟩ := certForgeries_nil hNF
    by_cases hp : (L.claim x).party ∈ c.corruptParties
    · have hA : certAdvClaims L c x = L.claim x :: c.advClaims := cert_if_pos hp _ _
      have hD : certDecode L c (.submit x) =
          some (.advApprove (L.claim x).party (L.claim x).deploymentId (L.claim x).intent) :=
        cert_if_pos hp _ _
      refine ⟨fun y hy => ?_, ?_⟩
      · change L.claim y ∈ c.issued ∨ L.claim y ∈ certAdvClaims L c x
        rw [hA]
        rcases List.mem_cons.mp hy with hEq | hTail
        · rw [hEq]
          exact .inr List.mem_cons_self
        · exact (hJ y hTail).imp id (List.mem_cons_of_mem _)
      · rw [hD, hA]
        change idealCustodyStep S oracleSign (certCustodyAbs c)
          (.advApprove (L.claim x).party (L.claim x).deploymentId (L.claim x).intent) = _
        unfold idealCustodyStep
        dsimp only
        exact cert_if_pos (And.intro hp hg.2) _ _
    · have hA : certAdvClaims L c x = c.advClaims := cert_if_neg hp _ _
      have hD : certDecode L c (.submit x) = none := cert_if_neg hp _ _
      have hi : L.claim x ∈ c.issued := hWho.resolve_left hp
      refine ⟨fun y hy => ?_, ?_⟩
      · change L.claim y ∈ c.issued ∨ L.claim y ∈ certAdvClaims L c x
        rw [hA]
        rcases List.mem_cons.mp hy with hEq | hTail
        · rw [hEq]
          exact .inl hi
        · exact hJ y hTail
      · rw [hD, hA]
        exact rfl
  | corrupt p =>
    dsimp only at h1
    obtain ⟨hg, hc, ho⟩ := h1
    subst hc
    subst ho
    refine ⟨hJ, ?_⟩
    change idealCustodyStep S oracleSign (certCustodyAbs c) (.corrupt p) = _
    unfold idealCustodyStep
    dsimp only
    exact cert_if_pos hg _ _
  | sign dep i ab =>
    dsimp only at h1
    obtain ⟨L', hL, hc⟩ := h1
    subst hc
    refine ⟨hJ, ?_⟩
    have hLe : (certApprovers L c.ledger.quorum.numParties c.pool c.ledger.deploymentId i).length ≤
        (custodyApprovers c.ledger.quorum.numParties c.issued c.advClaims
          c.ledger.deploymentId i).length :=
      custodyApprovers_length_le_of_subset (certApprovers_nodup L _ _ _ _)
        (fun p hp => certApprovers_spec hJ hp)
    have hM := custodyLedgerSign_mono hL hLe
    change Option.map _ (custodyLedgerSign S oracleSign c.ledger
      (custodyApprovers c.ledger.quorum.numParties c.issued c.advClaims
        c.ledger.deploymentId i).length dep i ab) = _
    rw [hM]
    exact rfl

private theorem certSim_safeInv
    {dep₀ : Nat} {pk₀ : PK} {quorum₀ : CustodyQuorumProfile}
    {c c' : CertCustodyState PK D Sig Cert} {out : CustodyOutcome Sig} {dec : Option CustodyInput}
    (hSafe : (certCustodyAbs c).SafeInv S oracleSign dep₀ pk₀ quorum₀)
    (hSim : CertSimStep S oracleSign c c' out dec) :
    (certCustodyAbs c').SafeInv S oracleSign dep₀ pk₀ quorum₀ := by
  cases dec with
  | none =>
    have hEq : certCustodyAbs c' = certCustodyAbs c := hSim
    rw [hEq]
    exact hSafe
  | some inp' =>
    have hStep : idealCustodyStep S oracleSign (certCustodyAbs c) inp' =
        some (certCustodyAbs c', out) := hSim
    exact idealCustodyStep_preserves_safeInv hSafe hStep

private theorem certCustody_validTrace_forgeries_nil
    {dep₀ : Nat} {pk₀ : PK} {quorum₀ : CustodyQuorumProfile}
    {c c' : CertCustodyState PK D Sig Cert}
    {tr : List (CertCustodyInput Cert × CustodyOutcome Sig)}
    (hTr : (certCustodyMachine L S oracleSign dep₀ pk₀ quorum₀).ValidTrace c tr c')
    (hNF : c'.forgeries = []) : c.forgeries = [] := by
  induction hTr with
  | nil _ => exact hNF
  | accept hStep _ ih =>
    exact certCustodyStep_forgeries_nil (L := L) (S := S) (oracleSign := oracleSign) hStep (ih hNF)
  | reject _ _ _ ih => exact ih hNF

/-- **Forgery-free traces map to ideal traces.** A coordinator trace that ends without a forgery
    event is simulated by a trace of `Spec.idealCustodyMachine` between the abstractions. -/
theorem certCustody_noForgery_validTrace_abs
    {dep₀ : Nat} {pk₀ : PK} {quorum₀ : CustodyQuorumProfile}
    {c c' : CertCustodyState PK D Sig Cert}
    {tr : List (CertCustodyInput Cert × CustodyOutcome Sig)}
    (hJ : CertPoolAccounted L c)
    (hTr : (certCustodyMachine L S oracleSign dep₀ pk₀ quorum₀).ValidTrace c tr c')
    (hNF : c'.forgeries = []) :
    CertPoolAccounted L c' ∧
    ∃ itr, (idealCustodyMachine S oracleSign dep₀ pk₀ quorum₀).ValidTrace
      (certCustodyAbs c) itr (certCustodyAbs c') := by
  induction hTr with
  | nil _ => exact ⟨hJ, [], .nil _⟩
  | @accept s s1 _ inp out _ hStep hRest ih =>
    have hStep' : certCustodyStep L S oracleSign s inp = some (s1, out) := hStep
    have hNF1 := certCustody_validTrace_forgeries_nil hRest hNF
    obtain ⟨hJ1, hSim⟩ := certCustodyStep_sim hJ hStep' hNF1
    obtain ⟨hJ', itr, hI⟩ := ih hJ1 hNF
    refine ⟨hJ', ?_⟩
    cases hd : certDecode L s inp with
    | none =>
      rw [hd] at hSim
      have hEq : certCustodyAbs s1 = certCustodyAbs s := hSim
      rw [← hEq]
      exact ⟨itr, hI⟩
    | some inp' =>
      rw [hd] at hSim
      have hIdeal : (idealCustodyMachine S oracleSign dep₀ pk₀ quorum₀).step (certCustodyAbs s) inp' =
          some (certCustodyAbs s1, out) := hSim
      exact ⟨(inp', out) :: itr, .accept hIdeal hI⟩
  | reject _ _ _ ih => exact ih hJ hNF

/-- A forgery-free reachable coordinator state abstracts to a reachable ideal state. -/
theorem certCustody_noForgery_reachable_ideal
    {dep₀ : Nat} {pk₀ : PK} {quorum₀ : CustodyQuorumProfile}
    {c : CertCustodyState PK D Sig Cert}
    (hR : (certCustodyMachine L S oracleSign dep₀ pk₀ quorum₀).Reachable c)
    (hNF : c.forgeries = []) :
    (idealCustodyMachine S oracleSign dep₀ pk₀ quorum₀).Reachable (certCustodyAbs c) := by
  obtain ⟨c₀, tr, hInit, hTr⟩ := hR
  have h0 : c₀ = CertCustodyState.init dep₀ pk₀ quorum₀ := hInit
  subst h0
  obtain ⟨_, itr, hI⟩ := certCustody_noForgery_validTrace_abs
    (fun _ h => False.elim (List.not_mem_nil h)) hTr hNF
  exact ⟨_, itr, rfl, hI⟩

/-- **Coordinator expenditure and certificate provenance.** On every forgery-free reachable
    coordinator state the amount spent is the sum of `intent.spend` over the authorized intents and
    within the budget, and every WAL record carries the oracle's signature on `digest dep₀ intent`
    for an intent that an enrolled custodian certified through its own port. -/
theorem certCustody_reachable_spend_and_provenance
    {dep₀ : Nat} {pk₀ : PK} {quorum₀ : CustodyQuorumProfile}
    {c : CertCustodyState PK D Sig Cert}
    (hR : (certCustodyMachine L S oracleSign dep₀ pk₀ quorum₀).Reachable c)
    (hNF : c.forgeries = []) :
    c.ledger.spent = (c.ledger.authorized.map CustodyIntent.spend).sum ∧
    c.ledger.spent ≤ quorum₀.spendCap ∧
    ∀ r ∈ c.ledger.releasedHistory,
      r.sig = oracleSign (S.digest dep₀ r.intent) ∧
      ∃ p, p < quorum₀.numParties ∧ CustodyApproval.mk p dep₀ r.intent ∈ c.issued := by
  have hIdeal := certCustody_noForgery_reachable_ideal hR hNF
  obtain ⟨hAcc, hBud, _, _⟩ := idealCustody_reachable_spend_accounting hIdeal
  exact ⟨hAcc, hBud, fun r hr => idealCustody_reachable_release_honestly_approved hIdeal hr⟩

private theorem certCustody_signature_approved_before_aux
    {dep₀ : Nat} {pk₀ : PK} {quorum₀ : CustodyQuorumProfile}
    {c c' : CertCustodyState PK D Sig Cert}
    {tr pre post : List (CertCustodyInput Cert × CustodyOutcome Sig)}
    {dep : Nat} {i : CustodyIntent} {ab : Bool} {out : CustodyOutcome Sig} {sig : Sig}
    (hJ : CertPoolAccounted L c)
    (hSafe : (certCustodyAbs c).SafeInv S oracleSign dep₀ pk₀ quorum₀)
    (hTr : (certCustodyMachine L S oracleSign dep₀ pk₀ quorum₀).ValidTrace c tr c')
    (hNF : c'.forgeries = [])
    (hSplit : tr = pre ++ (CertCustodyInput.sign dep i ab, out) :: post)
    (hOut : out = .released sig ∨ out = .replayedFromWal sig) :
    dep = dep₀ ∧ sig = oracleSign (S.digest dep₀ i) ∧
    ∃ p, p < quorum₀.numParties ∧
      (CustodyApproval.mk p dep₀ i ∈ c.issued ∨
       (CertCustodyInput.approve p dep₀ i,
         (CustodyOutcome.approvalRecorded : CustodyOutcome Sig)) ∈ pre) := by
  induction hTr generalizing pre with
  | nil _ => cases pre <;> cases hSplit
  | @accept s s1 _ inp o rest hStep hRest ih =>
    have hStep' : certCustodyStep L S oracleSign s inp = some (s1, o) := hStep
    have hNF1 := certCustody_validTrace_forgeries_nil hRest hNF
    obtain ⟨hJ1, hSim⟩ := certCustodyStep_sim hJ hStep' hNF1
    cases pre with
    | nil =>
      rw [List.nil_append] at hSplit
      have hHead := (List.cons.inj hSplit).1
      cases hHead
      have hIdeal : idealCustodyStep S oracleSign (certCustodyAbs s) (.sign dep i ab) =
          some (certCustodyAbs s1, out) := hSim
      obtain ⟨hD, hS, p, hp, hm⟩ := idealCustodyStep_sign_output_honest hSafe hIdeal hOut
      exact ⟨hD, hS, p, hp, .inl hm⟩
    | cons x pre' =>
      rw [List.cons_append] at hSplit
      have hx : (inp, o) = x := (List.cons.inj hSplit).1
      obtain ⟨hD, hS, p, hp, hm⟩ :=
        ih hJ1 (certSim_safeInv hSafe hSim) hNF (List.cons.inj hSplit).2
      refine ⟨hD, hS, p, hp, ?_⟩
      rcases hm with hm | hm
      · rcases certCustodyStep_issued_provenance hStep' hm with hOld | ⟨hI, hO⟩
        · exact .inl hOld
        · refine .inr ?_
          rw [← hx, hI, hO]
          exact List.mem_cons_self
      · exact .inr (List.mem_cons_of_mem _ hm)
  | reject _ _ _ ih => exact ih hJ hSafe hNF hSplit

/-- **On forgery-free traces every coordinator signature is preceded by an honest approval.** In a
    coordinator trace from the initial state that ends without a forgery event, a signature output
    for `i` (fresh release or WAL replay) is the oracle's signature on `digest dep₀ i`, and an
    enrolled custodian's own accepted `.approve p dep₀ i` occurs strictly earlier in the trace.
    Relayed and replayed honest certificates are admitted on such traces. -/
theorem certCustody_noForgery_signature_approved_before
    {dep₀ : Nat} {pk₀ : PK} {quorum₀ : CustodyQuorumProfile}
    {c₀ c : CertCustodyState PK D Sig Cert}
    {tr pre post : List (CertCustodyInput Cert × CustodyOutcome Sig)}
    {dep : Nat} {i : CustodyIntent} {ab : Bool} {out : CustodyOutcome Sig} {sig : Sig}
    (hInit : (certCustodyMachine L S oracleSign dep₀ pk₀ quorum₀).Init c₀)
    (hTr : (certCustodyMachine L S oracleSign dep₀ pk₀ quorum₀).ValidTrace c₀ tr c)
    (hNF : c.forgeries = [])
    (hSplit : tr = pre ++ (CertCustodyInput.sign dep i ab, out) :: post)
    (hOut : out = .released sig ∨ out = .replayedFromWal sig) :
    dep = dep₀ ∧ sig = oracleSign (S.digest dep₀ i) ∧
    ∃ p, p < quorum₀.numParties ∧
      (CertCustodyInput.approve p dep₀ i,
        (CustodyOutcome.approvalRecorded : CustodyOutcome Sig)) ∈ pre := by
  have h0 : c₀ = CertCustodyState.init dep₀ pk₀ quorum₀ := hInit
  subst h0
  obtain ⟨hD, hS, p, hp, hm⟩ := certCustody_signature_approved_before_aux
    (fun _ h => False.elim (List.not_mem_nil h))
    (IdealCustodyState.init_safeInv (PK := PK) S oracleSign dep₀ pk₀ quorum₀) hTr hNF hSplit hOut
  rcases hm with hm | hm
  · exact False.elim (List.not_mem_nil hm)
  · exact ⟨hD, hS, p, hp, hm⟩

/-! ### The forgery game -/

private theorem certRunStep_noForgery_safe
    {dep₀ : Nat} {pk₀ : PK} {quorum₀ : CustodyQuorumProfile}
    {c : CertCustodyState PK D Sig Cert} (inp : CertCustodyInput Cert)
    (hK : c.forgeries = [] →
      CertPoolAccounted L c ∧ (certCustodyAbs c).SafeInv S oracleSign dep₀ pk₀ quorum₀) :
    ((certCustodyMachine L S oracleSign dep₀ pk₀ quorum₀).runStep c inp).1.forgeries = [] →
      CertPoolAccounted L ((certCustodyMachine L S oracleSign dep₀ pk₀ quorum₀).runStep c inp).1 ∧
      (certCustodyAbs ((certCustodyMachine L S oracleSign dep₀ pk₀ quorum₀).runStep c inp).1).SafeInv
        S oracleSign dep₀ pk₀ quorum₀ := by
  cases hS : certCustodyStep L S oracleSign c inp with
  | none =>
    have hR : ((certCustodyMachine L S oracleSign dep₀ pk₀ quorum₀).runStep c inp).1 = c := by
      unfold Qsag.Spec.Machine.runStep
      have hS' : (certCustodyMachine L S oracleSign dep₀ pk₀ quorum₀).step c inp = none := hS
      rw [hS']
      rfl
    rw [hR]
    exact hK
  | some r =>
    obtain ⟨c1, o⟩ := r
    have hR : ((certCustodyMachine L S oracleSign dep₀ pk₀ quorum₀).runStep c inp).1 = c1 := by
      unfold Qsag.Spec.Machine.runStep
      have hS' : (certCustodyMachine L S oracleSign dep₀ pk₀ quorum₀).step c inp = some (c1, o) := hS
      rw [hS']
    rw [hR]
    intro hNF
    obtain ⟨hJ, hSafe⟩ := hK (certCustodyStep_forgeries_nil hS hNF)
    obtain ⟨hJ', hSim⟩ := certCustodyStep_sim hJ hS hNF
    exact ⟨hJ', certSim_safeInv hSafe hSim⟩

private theorem certFold_noForgery_safe
    {dep₀ : Nat} {pk₀ : PK} {quorum₀ : CustodyQuorumProfile} :
    ∀ (inps : List (CertCustodyInput Cert)) (c : CertCustodyState PK D Sig Cert),
      (c.forgeries = [] →
        CertPoolAccounted L c ∧ (certCustodyAbs c).SafeInv S oracleSign dep₀ pk₀ quorum₀) →
      (inps.foldl
        (fun c inp => ((certCustodyMachine L S oracleSign dep₀ pk₀ quorum₀).runStep c inp).1)
        c).forgeries = [] →
      (certCustodyAbs (inps.foldl
        (fun c inp => ((certCustodyMachine L S oracleSign dep₀ pk₀ quorum₀).runStep c inp).1)
        c)).SafeInv S oracleSign dep₀ pk₀ quorum₀
  | [], _, hK, hNF => (hK hNF).2
  | inp :: rest, _, hK, hNF =>
    certFold_noForgery_safe rest _ (certRunStep_noForgery_safe inp hK) hNF

/-- A run without a forgery event has no unsafe release. -/
theorem certCustody_noForgery_no_unsafe_release
    (L : CustodyCertLayer Cert) (S : CustodyDigestScheme D) (oracleSign : D → Sig)
    (dep₀ : Nat) (pk₀ : PK) (quorum₀ : CustodyQuorumProfile)
    (inps : List (CertCustodyInput Cert))
    (hNF : (certRun L S oracleSign dep₀ pk₀ quorum₀ inps).forgeries = []) :
    certUnsafeRelease quorum₀.numParties dep₀ (certRun L S oracleSign dep₀ pk₀ quorum₀ inps) =
      false := by
  have hSafe := certFold_noForgery_safe (L := L) (S := S) (oracleSign := oracleSign)
    (dep₀ := dep₀) (pk₀ := pk₀) (quorum₀ := quorum₀) inps
    (CertCustodyState.init dep₀ pk₀ quorum₀)
    (fun _ => ⟨fun _ h => False.elim (List.not_mem_nil h),
      IdealCustodyState.init_safeInv (PK := PK) S oracleSign dep₀ pk₀ quorum₀⟩) hNF
  cases hU : certUnsafeRelease quorum₀.numParties dep₀
      (certRun L S oracleSign dep₀ pk₀ quorum₀ inps) with
  | false => rfl
  | true =>
    unfold certUnsafeRelease at hU
    obtain ⟨r, hr, hb⟩ := List.any_eq_true.mp hU
    obtain ⟨p, hp, hm⟩ := hSafe.honestAuthorized _ (hSafe.walAuthorized r hr)
    have hAny : (List.range quorum₀.numParties).any (fun p => decide (CustodyApproval.mk p dep₀
        r.intent ∈ (certRun L S oracleSign dep₀ pk₀ quorum₀ inps).issued)) = true :=
      List.any_eq_true.mpr ⟨p, List.mem_range.mpr hp, decide_eq_true hm⟩
    rw [hAny] at hb
    cases hb

private theorem certRun_unsafe_forged
    (L : CustodyCertLayer Cert) (S : CustodyDigestScheme D) (oracleSign : D → Sig)
    (dep₀ : Nat) (pk₀ : PK) (quorum₀ : CustodyQuorumProfile)
    (inps : List (CertCustodyInput Cert))
    (hU : certUnsafeRelease quorum₀.numParties dep₀
      (certRun L S oracleSign dep₀ pk₀ quorum₀ inps) = true) :
    (!(certRun L S oracleSign dep₀ pk₀ quorum₀ inps).forgeries.isEmpty) = true := by
  cases hf : (certRun L S oracleSign dep₀ pk₀ quorum₀ inps).forgeries with
  | nil =>
    rw [certCustody_noForgery_no_unsafe_release L S oracleSign dep₀ pk₀ quorum₀ inps hf] at hU
    cases hU
  | cons _ _ => rfl

/-- **`Pr[unsafe release] ≤ Pr[forgery event]`.** Over a finite coin space that determines the
    certificate layer (its keys), the signing oracle and the adversary's whole input schedule, the
    probability that the coordinator's WAL holds a release no enrolled custodian certified is at
    most the probability that the forgery event occurred. The right-hand side is the quantity an
    unforgeability theorem for the certificate layer has to bound. -/
theorem certCustody_unsafe_release_le_forgery {n : Nat} (hn : 0 < n)
    (L : Fin n → CustodyCertLayer Cert) (S : CustodyDigestScheme D) (oracleSign : Fin n → D → Sig)
    (dep₀ : Nat) (pk₀ : PK) (quorum₀ : CustodyQuorumProfile)
    (adv : Fin n → List (CertCustodyInput Cert)) :
    GameBound
      (FinGame.mk hn (fun ω => certUnsafeRelease quorum₀.numParties dep₀
        (certRun (L ω) S (oracleSign ω) dep₀ pk₀ quorum₀ (adv ω)))).winProb
      (FinGame.mk hn (fun ω =>
        !(certRun (L ω) S (oracleSign ω) dep₀ pk₀ quorum₀ (adv ω)).forgeries.isEmpty)).winProb :=
  event_le_reduction_win _ _
    (fun ω h => certRun_unsafe_forged (L ω) S (oracleSign ω) dep₀ pk₀ quorum₀ (adv ω) h)

private theorem certRunStep_forgery_origin
    {dep₀ : Nat} {pk₀ : PK} {quorum₀ : CustodyQuorumProfile}
    {c : CertCustodyState PK D Sig Cert} {inp : CertCustodyInput Cert} {x : Cert}
    (hx : x ∈ ((certCustodyMachine L S oracleSign dep₀ pk₀ quorum₀).runStep c inp).1.forgeries) :
    x ∈ c.forgeries ∨ (inp = .submit x ∧ L.valid x = true) := by
  cases hS : certCustodyStep L S oracleSign c inp with
  | none =>
    have hR : ((certCustodyMachine L S oracleSign dep₀ pk₀ quorum₀).runStep c inp).1 = c := by
      unfold Qsag.Spec.Machine.runStep
      have hS' : (certCustodyMachine L S oracleSign dep₀ pk₀ quorum₀).step c inp = none := hS
      rw [hS']
      rfl
    rw [hR] at hx
    exact .inl hx
  | some r =>
    obtain ⟨c1, o⟩ := r
    have hR : ((certCustodyMachine L S oracleSign dep₀ pk₀ quorum₀).runStep c inp).1 = c1 := by
      unfold Qsag.Spec.Machine.runStep
      have hS' : (certCustodyMachine L S oracleSign dep₀ pk₀ quorum₀).step c inp = some (c1, o) := hS
      rw [hS']
    rw [hR] at hx
    have h1 := certCustodyStep_inv hS
    cases inp with
    | approve p dep i =>
      dsimp only at h1
      obtain ⟨_, hc, _⟩ := h1
      subst hc
      exact .inl hx
    | submit y =>
      dsimp only at h1
      obtain ⟨hg, hc, _⟩ := h1
      subst hc
      have hx' : x ∈ certForgeries L c y := hx
      unfold certForgeries at hx'
      by_cases hc : (L.claim y).party ∉ c.corruptParties ∧ L.claim y ∉ c.issued
      · rw [cert_if_pos hc] at hx'
        rcases List.mem_cons.mp hx' with hEq | hT
        · rw [hEq]
          exact .inr ⟨rfl, hg.1⟩
        · exact .inl hT
      · rw [cert_if_neg hc] at hx'
        exact .inl hx'
    | corrupt p =>
      dsimp only at h1
      obtain ⟨_, hc, _⟩ := h1
      subst hc
      exact .inl hx
    | sign dep i ab =>
      dsimp only at h1
      obtain ⟨L', _, hc⟩ := h1
      subst hc
      exact .inl hx

private theorem certFold_forgery_origin
    {dep₀ : Nat} {pk₀ : PK} {quorum₀ : CustodyQuorumProfile} {x : Cert} :
    ∀ (inps : List (CertCustodyInput Cert)) (c : CertCustodyState PK D Sig Cert),
      x ∈ (inps.foldl
        (fun c inp => ((certCustodyMachine L S oracleSign dep₀ pk₀ quorum₀).runStep c inp).1)
        c).forgeries →
      x ∈ c.forgeries ∨ (CertCustodyInput.submit x ∈ inps ∧ L.valid x = true)
  | [], _, h => .inl h
  | inp :: rest, c, h => by
    rcases certFold_forgery_origin rest _ h with h1 | ⟨h1, h2⟩
    · rcases certRunStep_forgery_origin h1 with h3 | ⟨h3, h4⟩
      · exact .inl h3
      · exact .inr ⟨h3 ▸ List.mem_cons_self, h4⟩
    · exact .inr ⟨List.mem_cons_of_mem _ h1, h2⟩

/-- Every forgery of a run is a submitted certificate that verifies. -/
theorem certRun_forgery_submitted
    (L : CustodyCertLayer Cert) (S : CustodyDigestScheme D) (oracleSign : D → Sig)
    (dep₀ : Nat) (pk₀ : PK) (quorum₀ : CustodyQuorumProfile)
    (inps : List (CertCustodyInput Cert)) {x : Cert}
    (hx : x ∈ (certRun L S oracleSign dep₀ pk₀ quorum₀ inps).forgeries) :
    CertCustodyInput.submit x ∈ inps ∧ L.valid x = true := by
  rcases certFold_forgery_origin (L := L) (S := S) (oracleSign := oracleSign) (dep₀ := dep₀)
    (pk₀ := pk₀) (quorum₀ := quorum₀) inps (CertCustodyState.init dep₀ pk₀ quorum₀) hx with h | h
  · exact False.elim (List.not_mem_nil h)
  · exact h

/-- **A non-degenerate instance of the forgery bound.** For `macCertLayer` with one key drawn from
    the coin space and an adversary whose input schedule does not depend on the key, an unsafe
    release needs a submitted tag equal to the key:
    `Pr[unsafe release] ≤ Pr[forgery] ≤ Pr[key ∈ submitted tags]`. -/
theorem macCustody_unsafe_release_le_key_guess {n : Nat} (hn : 0 < n)
    (S : CustodyDigestScheme D) (oracleSign : D → Sig)
    (dep₀ : Nat) (pk₀ : PK) (quorum₀ : CustodyQuorumProfile)
    (adv : List (CertCustodyInput (Nat × CustodyApproval))) :
    GameBound
      (FinGame.mk hn (fun ω => certUnsafeRelease quorum₀.numParties dep₀
        (certRun (macCertLayer (fun _ => ω.val)) S oracleSign dep₀ pk₀ quorum₀ adv))).winProb
      (FinGame.mk hn (fun ω => adv.any (fun inp =>
        match inp with
        | .submit x => x.1 == ω.val
        | _ => false))).winProb :=
  GameBound.trans
    (certCustody_unsafe_release_le_forgery hn (fun ω => macCertLayer (fun _ => ω.val)) S
      (fun _ => oracleSign) dep₀ pk₀ quorum₀ (fun _ => adv))
    (event_le_reduction_win _ _ (fun ω h => by
      obtain ⟨x, hx⟩ := cert_exists_of_not_isEmpty h
      obtain ⟨hIn, hV⟩ := certRun_forgery_submitted _ S oracleSign dep₀ pk₀ quorum₀ adv hx
      exact List.any_eq_true.mpr ⟨.submit x, hIn, hV⟩))

end Sim

/-! ### Concrete runs: 2-of-3 custody for deployment `7`, MAC keys `1000 + p` -/

def certToothQuorum : CustodyQuorumProfile :=
  { numParties := 3, threshold := 2, spendCap := 100, h_pos := by decide, h_le := by decide }

def certToothIntent : CustodyIntent :=
  { sessionId := 1, round := 0, epoch := 0, spend := 40, payload := [0x51, 0x53] }

def certToothRun (inps : List (CertCustodyInput (Nat × CustodyApproval))) :
    CertCustodyState Unit (Nat × CustodyIntent) (Nat × CustodyIntent) (Nat × CustodyApproval) :=
  certRun (macCertLayer (fun p => 1000 + p)) CustodyDigestScheme.transparent id 7 ()
    certToothQuorum inps

/-- Two custodians approve; their certificates are relayed to the coordinator through the raw
    `.submit` interface. No forgery event occurs, the release is safe and charges `40`. -/
theorem certCustody_tooth_relayed_certificates_release :
    ((certToothRun
        [.approve 0 7 certToothIntent, .approve 1 7 certToothIntent,
         .submit (1000, ⟨0, 7, certToothIntent⟩), .submit (1001, ⟨1, 7, certToothIntent⟩),
         .sign 7 certToothIntent false]).forgeries.isEmpty,
      (certToothRun
        [.approve 0 7 certToothIntent, .approve 1 7 certToothIntent,
         .submit (1000, ⟨0, 7, certToothIntent⟩), .submit (1001, ⟨1, 7, certToothIntent⟩),
         .sign 7 certToothIntent false]).ledger.spent,
      certUnsafeRelease 3 7 (certToothRun
        [.approve 0 7 certToothIntent, .approve 1 7 certToothIntent,
         .submit (1000, ⟨0, 7, certToothIntent⟩), .submit (1001, ⟨1, 7, certToothIntent⟩),
         .sign 7 certToothIntent false])) = (true, 40, false) := by
  decide +kernel

/-- The forgery-free hypothesis is necessary: when certificates carrying the keys of two
    uncorrupted custodians who approved nothing are admitted, the coordinator releases a signature
    that no custodian approved. -/
theorem certCustody_tooth_forged_certificates_unsafe_release :
    ¬ (certUnsafeRelease 3 7 (certToothRun
        [.submit (1000, ⟨0, 7, certToothIntent⟩), .submit (1001, ⟨1, 7, certToothIntent⟩),
         .sign 7 certToothIntent false]) = false) := by
  decide +kernel

/-- A certificate with a wrong tag is not admitted, so it produces neither a vote nor a release. -/
theorem certCustody_tooth_wrong_tag_rejected :
    ¬ ((certToothRun
        [.submit (999, ⟨0, 7, certToothIntent⟩), .submit (1001, ⟨1, 7, certToothIntent⟩),
         .sign 7 certToothIntent false]).ledger.spent = 40) := by
  decide +kernel

end CertCustody

/-! ## 8. The Separated-Custody Coordinator `Custody.submitRecorded` and `Spec.IdealCustody` -/

section SeparatedCustodyIdeal

open Qsag.Spec

/-- The ideal intent of a separated-custody intent. The hash-signature leaf is the epoch. -/
def sepIntent (r : Qsag.Custody.Intent) : CustodyIntent :=
  { sessionId := r.session, round := r.round, epoch := r.leaf, spend := r.spend,
    payload := r.message }

theorem sepIntent_injective {r s : Qsag.Custody.Intent} (h : sepIntent r = sepIntent s) :
    r = s := by
  cases r
  cases s
  unfold sepIntent at h
  cases h
  rfl

/-- A successful signing by custodian `party` of `intent`, with the deployment the custodian was
    acting for. `Custody.payload` does not contain the deployment, so the certificate produced is
    the same for every `deploymentId`. -/
structure SepIssue where
  party : Nat
  deploymentId : Nat
  intent : Qsag.Custody.Intent

/-- The separated-custody world around the real coordinator. The coordinator's decisions are
    `Custody.submitRecorded` on `shared`. `corruptParties` and `issued` are history of the world;
    `forgeries` is bookkeeping for the analysis. -/
structure SepCustodyState where
  shared : Qsag.Custody.SharedHistory
  corruptParties : List Nat
  issued : List SepIssue
  forgeries : List Qsag.Custody.Certificate

/-- `.submit` is the coordinator's real interface: an intent and an arbitrary certificate list. -/
inductive SepCustodyInput where
  | approve (party deploymentId : Nat) (intent : Qsag.Custody.Intent)
  | corrupt (party : Nat)
  | submit (intent : Qsag.Custody.Intent) (certs : List Qsag.Custody.Certificate)

inductive SepCustodyOutput where
  | certificate (c : Qsag.Custody.Certificate)
  | corrupted
  | accepted

def sepIssuedBy (issued : List SepIssue) (p : Nat) (r : Qsag.Custody.Intent) : Bool :=
  issued.any (fun a => decide (a.party = p ∧ a.intent = r))

/-- The forgery event of one accepted submission: the certificates of uncorrupted parties that
    never signed the submitted intent (for any deployment). -/
def sepForged (c : SepCustodyState) (r : Qsag.Custody.Intent)
    (cs : List Qsag.Custody.Certificate) : List Qsag.Custody.Certificate :=
  cs.filter (fun x => decide (x.party ∉ c.corruptParties) && !sepIssuedBy c.issued x.party r)

/-- Transition of the separated-custody world. An uncorrupted enrolled custodian signs with the
    production signer `Custody.sign` under its own key; a failed signing is no event. Corruption is
    budgeted below the threshold. A submission is the real `Custody.submitRecorded`. -/
def sepCustodyStep (d : Qsag.Custody.Deployment) (c : SepCustodyState) :
    SepCustodyInput → Option (SepCustodyState × SepCustodyOutput)
  | .approve p dep r =>
    if p < d.numParties ∧ p ∉ c.corruptParties then
      match Qsag.Custody.sign d.signer (d.keys p) p r with
      | some sig => some ({ c with issued := ⟨p, dep, r⟩ :: c.issued }, .certificate ⟨p, r, sig⟩)
      | none => none
    else none
  | .corrupt p =>
    if p < d.numParties ∧ p ∉ c.corruptParties ∧ c.corruptParties.length + 1 < d.threshold then
      some ({ c with corruptParties := p :: c.corruptParties }, .corrupted)
    else none
  | .submit r cs =>
    if (Qsag.Custody.submitRecorded d c.shared r cs).2 = true then
      some ({ c with
              shared := (Qsag.Custody.submitRecorded d c.shared r cs).1
              forgeries := sepForged c r cs ++ c.forgeries }, .accepted)
    else none

def sepCustodyMachine (d : Qsag.Custody.Deployment) :
    Qsag.Spec.Machine SepCustodyState SepCustodyInput SepCustodyOutput where
  Init c := c = ⟨⟨⟨[], 0, d.capacity⟩, []⟩, [], [], []⟩
  step := sepCustodyStep d
  errStep c _ := c

def sepLeafOk (w : Nat) : SepCustodyInput → Prop
  | .submit r _ => w ≤ r.leaf
  | _ => True

def sepNextLeaf (w : Nat) : SepCustodyInput → Nat
  | .submit r _ => r.leaf + 1
  | _ => w

/-- Accepted submissions use strictly increasing leaves, starting at or above `w`. -/
def sepLeavesFresh : Nat → List (SepCustodyInput × SepCustodyOutput) → Prop
  | _, [] => True
  | w, e :: rest => sepLeafOk w e.1 ∧ sepLeavesFresh (sepNextLeaf w e.1) rest

/-- The deployment's quorum parameters are those of the ideal profile (which carries
    `0 < threshold ≤ numParties`). -/
structure SepDeploymentProfile (d : Qsag.Custody.Deployment) (q : CustodyQuorumProfile) :
    Prop where
  parties : d.numParties = q.numParties
  threshold : d.threshold = q.threshold
  capacity : d.capacity = q.spendCap

/-- What `Qsag.Custody.*` does not provide, as conditions on one run `tr` ending in `c`.

* `noForgery`: no accepted submission contained a verifying certificate of an uncorrupted party
  for an intent that party never signed. Its probability is not bounded here.
* `singleDeployment`: custodians signed only for deployment `dep₀`. `Custody.payload` omits the
  deployment, so a certificate signed for another deployment under the same key verifies here.
* `leavesIncrease`: accepted submissions use strictly increasing leaves. The coordinator
  `Custody.submit` checks session freshness only; it has no epoch watermark and no WAL. -/
structure SeparatedCustodyRunAssumptions (dep₀ : Nat)
    (tr : List (SepCustodyInput × SepCustodyOutput)) (c : SepCustodyState) : Prop where
  noForgery : c.forgeries = []
  singleDeployment : ∀ a ∈ c.issued, a.deploymentId = dep₀
  leavesIncrease : sepLeavesFresh 0 tr

/-- Correspondence between a state of the separated-custody world and an ideal custody state. -/
structure SepCustodyIdealRel {PK D Sig : Type} (quorum₀ : CustodyQuorumProfile)
    (c : SepCustodyState) (st : IdealCustodyState PK D Sig) : Prop where
  poisoned : st.ledger.poisoned = false
  spent : st.ledger.spent = c.shared.coordinator.spent
  capacity : c.shared.coordinator.capacity = quorum₀.spendCap
  sessions : st.ledger.usedSessions = c.shared.coordinator.consumedSessions
  corrupt : st.corruptParties = c.corruptParties
  honest : st.honestApprovals =
    c.issued.map (fun a => CustodyApproval.mk a.party a.deploymentId (sepIntent a.intent))
  authorized : st.ledger.authorized = c.shared.accepted.map (fun a => sepIntent a.intent)

private theorem sep_append_nil {α : Type} : ∀ {l m : List α}, l ++ m = [] → l = [] ∧ m = []
  | [], _, h => ⟨rfl, h⟩
  | _ :: _, _, h => by cases h

private theorem sep_filter_nil {α : Type} {p : α → Bool} :
    ∀ {l : List α}, l.filter p = [] → ∀ x ∈ l, p x = false
  | [], _, _, hx => False.elim (List.not_mem_nil hx)
  | y :: ys, h, x, hx => by
    cases hp : p y with
    | true =>
      rw [List.filter_cons_of_pos hp] at h
      cases h
    | false =>
      rw [List.filter_cons_of_neg (fun hd => Bool.false_ne_true (hp.symm.trans hd))] at h
      rcases List.mem_cons.mp hx with he | ht
      · rw [he]
        exact hp
      · exact sep_filter_nil h x ht

private theorem sepIssuedBy_spec {issued : List SepIssue} {p : Nat} {r : Qsag.Custody.Intent}
    (h : sepIssuedBy issued p r = true) : ∃ a ∈ issued, a.party = p ∧ a.intent = r := by
  unfold sepIssuedBy at h
  obtain ⟨a, ha, hd⟩ := List.any_eq_true.mp h
  exact ⟨a, ha, of_decide_eq_true hd⟩

private theorem sep_validTrace_append {σ In Out : Type} {M : Qsag.Spec.Machine σ In Out}
    {a b c : σ} {t1 t2 : List (In × Out)}
    (h1 : M.ValidTrace a t1 b) (h2 : M.ValidTrace b t2 c) : M.ValidTrace a (t1 ++ t2) c := by
  induction h1 with
  | nil _ => exact h2
  | accept hs _ ih => exact .accept hs (ih h2)
  | reject inp hs _ ih => exact .reject inp hs (ih h2)

private theorem sepCustodyStep_inv {d : Qsag.Custody.Deployment} {c c1 : SepCustodyState}
    {inp : SepCustodyInput} {out : SepCustodyOutput}
    (h : sepCustodyStep d c inp = some (c1, out)) :
    match inp with
    | .approve p dep r =>
      (p < d.numParties ∧ p ∉ c.corruptParties) ∧
      c1 = { c with issued := ⟨p, dep, r⟩ :: c.issued }
    | .corrupt p =>
      (p < d.numParties ∧ p ∉ c.corruptParties ∧ c.corruptParties.length + 1 < d.threshold) ∧
      c1 = { c with corruptParties := p :: c.corruptParties }
    | .submit r cs =>
      (Qsag.Custody.submitRecorded d c.shared r cs).2 = true ∧
      c1 = { c with
             shared := (Qsag.Custody.submitRecorded d c.shared r cs).1
             forgeries := sepForged c r cs ++ c.forgeries } := by
  cases inp with
  | approve p dep r =>
    unfold sepCustodyStep at h
    dsimp only at h ⊢
    by_cases hg : p < d.numParties ∧ p ∉ c.corruptParties
    · rw [cert_if_pos hg] at h
      cases hs : Qsag.Custody.sign d.signer (d.keys p) p r with
      | none =>
        rw [hs] at h
        cases h
      | some sig =>
        rw [hs] at h
        cases h
        exact ⟨hg, rfl⟩
    · rw [cert_if_neg hg] at h
      cases h
  | corrupt p =>
    unfold sepCustodyStep at h
    dsimp only at h ⊢
    by_cases hg : p < d.numParties ∧ p ∉ c.corruptParties ∧
        c.corruptParties.length + 1 < d.threshold
    · rw [cert_if_pos hg] at h
      cases h
      exact ⟨hg, rfl⟩
    · rw [cert_if_neg hg] at h
      cases h
  | submit r cs =>
    unfold sepCustodyStep at h
    dsimp only at h ⊢
    by_cases hg : (Qsag.Custody.submitRecorded d c.shared r cs).2 = true
    · rw [cert_if_pos hg] at h
      cases h
      exact ⟨hg, rfl⟩
    · rw [cert_if_neg hg] at h
      cases h

/-- The forgery log and the issue log only grow. -/
private theorem sepCustodyStep_mono {d : Qsag.Custody.Deployment} {c c1 : SepCustodyState}
    {inp : SepCustodyInput} {out : SepCustodyOutput}
    (h : sepCustodyStep d c inp = some (c1, out)) :
    (c1.forgeries = [] → c.forgeries = []) ∧ (∀ a ∈ c.issued, a ∈ c1.issued) := by
  have h1 := sepCustodyStep_inv h
  cases inp with
  | approve p dep r =>
    dsimp only at h1
    obtain ⟨_, hc⟩ := h1
    subst hc
    exact ⟨id, fun _ ha => List.mem_cons_of_mem _ ha⟩
  | corrupt p =>
    dsimp only at h1
    obtain ⟨_, hc⟩ := h1
    subst hc
    exact ⟨id, fun _ ha => ha⟩
  | submit r cs =>
    dsimp only at h1
    obtain ⟨_, hc⟩ := h1
    subst hc
    exact ⟨fun hf => (sep_append_nil hf).2, fun _ ha => ha⟩

private theorem sepCustody_validTrace_mono {d : Qsag.Custody.Deployment}
    {c c' : SepCustodyState} {tr : List (SepCustodyInput × SepCustodyOutput)}
    (hTr : (sepCustodyMachine d).ValidTrace c tr c') :
    (c'.forgeries = [] → c.forgeries = []) ∧ (∀ a ∈ c.issued, a ∈ c'.issued) := by
  induction hTr with
  | nil _ => exact ⟨id, fun _ ha => ha⟩
  | @accept s s1 _ inp out _ hStep _ ih =>
    have hStep' : sepCustodyStep d s inp = some (s1, out) := hStep
    have h1 := sepCustodyStep_mono hStep'
    exact ⟨fun hf => h1.1 (ih.1 hf), fun a ha => ih.2 a (h1.2 a ha)⟩
  | reject _ _ _ ih => exact ih

private theorem sep_findReleased_none {D Sig : Type} {hist : List (CustodyRelease D Sig)}
    {w ep : Nat} (hFresh : ∀ r ∈ hist, r.intent.epoch < w) (hW : w ≤ ep) :
    findReleasedEpoch hist ep = none := by
  cases h : findReleasedEpoch hist ep with
  | none => rfl
  | some r =>
    obtain ⟨hr, he⟩ := findReleasedEpoch_some h
    have hlt : ep < w := by
      rw [← he]
      exact hFresh r hr
    exact absurd hlt (Nat.not_lt_of_le hW)

section Sim

variable {PK D Sig : Type} [DecidableEq D]
variable {S : CustodyDigestScheme D} {oracleSign : D → Sig}

private theorem sep_ledgerSign_fresh
    {L : CustodyLedger PK D Sig} {n dep : Nat} {i : CustodyIntent}
    (hP : L.poisoned = false) (hD : dep = L.deploymentId)
    (hF : findReleasedEpoch L.releasedHistory i.epoch = none)
    (hEp : L.nextFreshEpoch ≤ i.epoch) (hSess : i.sessionId ∉ L.usedSessions)
    (hQ : L.quorum.threshold ≤ n) (hCap : L.spent + i.spend ≤ L.quorum.spendCap) :
    custodyLedgerSign S oracleSign L n dep i false =
      some ({ L.authorize i with
              releasedHistory :=
                ⟨i, S.digest L.deploymentId i, oracleSign (S.digest L.deploymentId i)⟩ ::
                  L.releasedHistory },
            .released (oracleSign (S.digest L.deploymentId i))) := by
  unfold custodyLedgerSign
  rw [cert_if_pos (And.intro hP hD), hF]
  dsimp only
  rw [cert_if_pos (show L.nextFreshEpoch ≤ i.epoch ∧ i.sessionId ∉ L.usedSessions ∧
    L.quorum.threshold ≤ n ∧ L.spent + i.spend ≤ L.quorum.spendCap from ⟨hEp, hSess, hQ, hCap⟩)]
  exact cert_if_neg Bool.false_ne_true _ _

/-- The ideal functionality refuses a fresh signing below its epoch watermark. A real run that
    accepts a submission on an older leaf than an earlier one therefore has no ideal counterpart:
    `leavesIncrease` cannot be dropped. -/
theorem sepCustody_stale_leaf_rejected_by_ideal
    (st : IdealCustodyState PK D Sig) (dep : Nat) (i : CustodyIntent) (ab : Bool)
    (hF : findReleasedEpoch st.ledger.releasedHistory i.epoch = none)
    (hStale : i.epoch < st.ledger.nextFreshEpoch) :
    idealCustodyStep S oracleSign st (.sign dep i ab) = none := by
  cases h : idealCustodyStep S oracleSign st (.sign dep i ab) with
  | none => rfl
  | some r =>
    obtain ⟨st', out⟩ := r
    obtain ⟨L', hL, _⟩ := idealCustodyStep_sign_inv h
    obtain ⟨_, _, hCase⟩ := custodyLedgerSign_inv hL
    rcases hCase with ⟨rec, hFound, _⟩ | ⟨_, hEp, _⟩
    · rw [hF] at hFound
      cases hFound
    · exact absurd hStale (Nat.not_lt_of_le hEp)

/-- The adversary records a permit for each listed party it has corrupted. -/
private theorem idealCustody_advApprove_all
    {dep₀ : Nat} {pk₀ : PK} {quorum₀ : CustodyQuorumProfile} (i : CustodyIntent) :
    ∀ (ps : List Nat) (st : IdealCustodyState PK D Sig), st.ledger.deploymentId = dep₀ →
      ∃ st' itr, (idealCustodyMachine S oracleSign dep₀ pk₀ quorum₀).ValidTrace st itr st' ∧
        st'.ledger = st.ledger ∧ st'.corruptParties = st.corruptParties ∧
        st'.honestApprovals = st.honestApprovals ∧
        (∀ a ∈ st.corruptApprovals, a ∈ st'.corruptApprovals) ∧
        ∀ p ∈ ps, p ∈ st.corruptParties → CustodyApproval.mk p dep₀ i ∈ st'.corruptApprovals
  | [], st, _ =>
    ⟨st, [], .nil _, rfl, rfl, rfl, fun _ h => h, fun _ h => False.elim (List.not_mem_nil h)⟩
  | p :: ps, st, hD => by
    by_cases hp : p ∈ st.corruptParties
    · have hStep : (idealCustodyMachine S oracleSign dep₀ pk₀ quorum₀).step st
          (.advApprove p dep₀ i) =
          some ({ st with corruptApprovals := CustodyApproval.mk p dep₀ i :: st.corruptApprovals },
                .approvalRecorded) := by
        change idealCustodyStep S oracleSign st (.advApprove p dep₀ i) = _
        unfold idealCustodyStep
        dsimp only
        exact cert_if_pos (And.intro hp hD.symm) _ _
      obtain ⟨st', itr, hT, hL, hC, hH, hKeep, hAll⟩ := idealCustody_advApprove_all i ps
        { st with corruptApprovals := CustodyApproval.mk p dep₀ i :: st.corruptApprovals } hD
      refine ⟨st', _ :: itr, .accept hStep hT, hL, hC, hH,
        fun a ha => hKeep a (List.mem_cons_of_mem _ ha), ?_⟩
      intro q hq hqc
      rcases List.mem_cons.mp hq with he | ht
      · rw [he]
        exact hKeep _ List.mem_cons_self
      · exact hAll q ht hqc
    · obtain ⟨st', itr, hT, hL, hC, hH, hKeep, hAll⟩ := idealCustody_advApprove_all i ps st hD
      refine ⟨st', itr, hT, hL, hC, hH, hKeep, ?_⟩
      intro q hq hqc
      rcases List.mem_cons.mp hq with he | ht
      · exact absurd (he ▸ hqc) hp
      · exact hAll q ht hqc

/-- One accepted step of the separated-custody world is matched by ideal steps: an approval by the
    custodian's `.approve`, a corruption by `.corrupt`, an accepted submission by the adversary's
    permits for the corrupted signers followed by `.sign`. -/
private theorem sepCustodyStep_sim
    {d : Qsag.Custody.Deployment} {dep₀ : Nat} {pk₀ : PK} {quorum₀ : CustodyQuorumProfile}
    (hP : SepDeploymentProfile d quorum₀)
    {c c1 : SepCustodyState} {inp : SepCustodyInput} {out : SepCustodyOutput} {w : Nat}
    {st : IdealCustodyState PK D Sig}
    (hStep : sepCustodyStep d c inp = some (c1, out))
    (hNF : c1.forgeries = []) (hSD : ∀ a ∈ c1.issued, a.deploymentId = dep₀)
    (hLeaf : sepLeafOk w inp)
    (hSafe : st.SafeInv S oracleSign dep₀ pk₀ quorum₀)
    (hRel : SepCustodyIdealRel quorum₀ c st) (hW : st.ledger.nextFreshEpoch ≤ w) :
    ∃ st1 itr, (idealCustodyMachine S oracleSign dep₀ pk₀ quorum₀).ValidTrace st itr st1 ∧
      SepCustodyIdealRel quorum₀ c1 st1 ∧ st1.ledger.nextFreshEpoch ≤ sepNextLeaf w inp := by
  have h1 := sepCustodyStep_inv hStep
  have hD := hSafe.deployment
  cases inp with
  | approve p dep r =>
    dsimp only at h1
    obtain ⟨hg, hc⟩ := h1
    subst hc
    have hDep : dep = dep₀ := hSD ⟨p, dep, r⟩ List.mem_cons_self
    have hg' : p < st.ledger.quorum.numParties ∧ p ∉ st.corruptParties ∧
        dep = st.ledger.deploymentId := by
      rw [hSafe.profile, hRel.corrupt, ← hP.parties, hD]
      exact ⟨hg.1, hg.2, hDep⟩
    have hI : (idealCustodyMachine S oracleSign dep₀ pk₀ quorum₀).step st
        (.approve p dep (sepIntent r)) =
        some ({ st with
                honestApprovals := CustodyApproval.mk p dep (sepIntent r) :: st.honestApprovals },
              .approvalRecorded) := by
      change idealCustodyStep S oracleSign st (.approve p dep (sepIntent r)) = _
      unfold idealCustodyStep
      dsimp only
      exact cert_if_pos hg' _ _
    refine ⟨_, _, .accept hI (.nil _), ?_, hW⟩
    exact
      { poisoned := hRel.poisoned
        spent := hRel.spent
        capacity := hRel.capacity
        sessions := hRel.sessions
        corrupt := hRel.corrupt
        honest := congrArg (fun l => CustodyApproval.mk p dep (sepIntent r) :: l) hRel.honest
        authorized := hRel.authorized }
  | corrupt p =>
    dsimp only at h1
    obtain ⟨hg, hc⟩ := h1
    subst hc
    have hg' : p < st.ledger.quorum.numParties ∧ p ∉ st.corruptParties ∧
        st.corruptParties.length + 1 < st.ledger.quorum.threshold := by
      rw [hSafe.profile, hRel.corrupt, ← hP.parties, ← hP.threshold]
      exact hg
    have hI : (idealCustodyMachine S oracleSign dep₀ pk₀ quorum₀).step st (.corrupt p) =
        some ({ st with corruptParties := p :: st.corruptParties },
              .corrupted (custodyRevealed st.honestApprovals p)) := by
      change idealCustodyStep S oracleSign st (.corrupt p) = _
      unfold idealCustodyStep
      dsimp only
      exact cert_if_pos hg' _ _
    refine ⟨_, _, .accept hI (.nil _), ?_, hW⟩
    exact
      { poisoned := hRel.poisoned
        spent := hRel.spent
        capacity := hRel.capacity
        sessions := hRel.sessions
        corrupt := congrArg (fun l => p :: l) hRel.corrupt
        honest := hRel.honest
        authorized := hRel.authorized }
  | submit r cs =>
    dsimp only at h1
    obtain ⟨hv, hc⟩ := h1
    subst hc
    obtain ⟨hAcc, hCap, hEq⟩ := Qsag.Custody.submitRecorded_accepted d c.shared r cs hv
    obtain ⟨hSess, _, hTle, hNd, hRange, _⟩ :=
      (Qsag.Custody.acceptQuorum_spec _ _ _ _ _ _ _).mp hAcc
    have hNo : sepForged c r cs = [] := (sep_append_nil hNF).1
    unfold sepForged at hNo
    have hLeaf' : w ≤ r.leaf := hLeaf
    obtain ⟨st2, itrA, hTA, hL2, hC2, hH2, _, hAdv⟩ :=
      idealCustody_advApprove_all (S := S) (oracleSign := oracleSign) (pk₀ := pk₀)
        (quorum₀ := quorum₀) (sepIntent r) (cs.map Qsag.Custody.Certificate.party) st hD
    have hSub : ∀ p ∈ cs.map Qsag.Custody.Certificate.party,
        p < st.ledger.quorum.numParties ∧
        (CustodyApproval.mk p st.ledger.deploymentId (sepIntent r) ∈ st2.honestApprovals ∨
         CustodyApproval.mk p st.ledger.deploymentId (sepIntent r) ∈ st2.corruptApprovals) := by
      intro p hp
      obtain ⟨x, hx, hxp⟩ := List.mem_map.mp hp
      rw [hSafe.profile, hD, ← hP.parties]
      refine ⟨by rw [← hxp]; exact hRange x hx, ?_⟩
      by_cases hpc : p ∈ st.corruptParties
      · exact .inr (hAdv p hp hpc)
      · refine .inl ?_
        have hpc' : x.party ∉ c.corruptParties := by
          rw [hxp, ← hRel.corrupt]
          exact hpc
        have hIss : sepIssuedBy c.issued x.party r = true := by
          cases hI : sepIssuedBy c.issued x.party r with
          | true => rfl
          | false =>
            have hf : (decide (x.party ∉ c.corruptParties) &&
                !sepIssuedBy c.issued x.party r) = false := sep_filter_nil hNo x hx
            rw [hI, decide_eq_true hpc'] at hf
            exact absurd hf (by decide)
        obtain ⟨a, ha, hap, hai⟩ := sepIssuedBy_spec hIss
        have hm : CustodyApproval.mk a.party a.deploymentId (sepIntent a.intent) ∈
            c.issued.map (fun a =>
              CustodyApproval.mk a.party a.deploymentId (sepIntent a.intent)) :=
          List.mem_map_of_mem ha
        rw [hap, hai, hSD a ha, hxp] at hm
        rw [hH2, hRel.honest]
        exact hm
    have hQ : st.ledger.quorum.threshold ≤
        (custodyApprovers st.ledger.quorum.numParties st2.honestApprovals st2.corruptApprovals
          st.ledger.deploymentId (sepIntent r)).length := by
      have hLen := custodyApprovers_length_le_of_subset hNd hSub
      rw [List.length_map] at hLen
      have ht : st.ledger.quorum.threshold = d.threshold := by
        rw [hSafe.profile]
        exact hP.threshold.symm
      rw [ht]
      exact Nat.le_trans hTle hLen
    have hLS := sep_ledgerSign_fresh (S := S) (oracleSign := oracleSign) (L := st.ledger)
      (dep := dep₀) (i := sepIntent r) hRel.poisoned hD.symm
      (sep_findReleased_none hSafe.walFresh (Nat.le_trans hW hLeaf'))
      (Nat.le_trans hW hLeaf')
      (by rw [hRel.sessions]; exact hSess)
      hQ
      (by rw [hRel.spent, hSafe.profile, ← hRel.capacity]; exact hCap)
    have hI : (idealCustodyMachine S oracleSign dep₀ pk₀ quorum₀).step st2
        (.sign dep₀ (sepIntent r) false) =
        some ({ st2 with
                ledger :=
                  { st.ledger.authorize (sepIntent r) with
                    releasedHistory :=
                      ⟨sepIntent r, S.digest st.ledger.deploymentId (sepIntent r),
                        oracleSign (S.digest st.ledger.deploymentId (sepIntent r))⟩ ::
                        st.ledger.releasedHistory } },
              .released (oracleSign (S.digest st.ledger.deploymentId (sepIntent r)))) := by
      change Option.map _ (custodyLedgerSign S oracleSign st2.ledger
        (custodyApprovers st2.ledger.quorum.numParties st2.honestApprovals st2.corruptApprovals
          st2.ledger.deploymentId (sepIntent r)).length dep₀ (sepIntent r) false) = _
      rw [hL2, hLS]
      rfl
    refine ⟨_, _, sep_validTrace_append hTA (.accept hI (.nil _)), ?_, Nat.le_refl _⟩
    exact
      { poisoned := hRel.poisoned
        spent := (congrArg (fun x => x + r.spend) hRel.spent).trans
          (congrArg (fun s : Qsag.Custody.SharedHistory => s.coordinator.spent) hEq).symm
        capacity := (congrArg (fun s : Qsag.Custody.SharedHistory => s.coordinator.capacity)
          hEq).trans hRel.capacity
        sessions := (congrArg (fun l => r.session :: l) hRel.sessions).trans
          (congrArg (fun s : Qsag.Custody.SharedHistory => s.coordinator.consumedSessions)
            hEq).symm
        corrupt := hC2.trans hRel.corrupt
        honest := hH2.trans hRel.honest
        authorized := (congrArg (fun l => sepIntent r :: l) hRel.authorized).trans
          (congrArg (fun s : Qsag.Custody.SharedHistory =>
            s.accepted.map (fun a : Qsag.Custody.AcceptedSubmission => sepIntent a.intent))
            hEq).symm }

private theorem sepCustody_validTrace_sim
    {d : Qsag.Custody.Deployment} {dep₀ : Nat} {pk₀ : PK} {quorum₀ : CustodyQuorumProfile}
    (hP : SepDeploymentProfile d quorum₀)
    {c c' : SepCustodyState} {tr : List (SepCustodyInput × SepCustodyOutput)}
    (hTr : (sepCustodyMachine d).ValidTrace c tr c')
    (hNF : c'.forgeries = []) (hSD : ∀ a ∈ c'.issued, a.deploymentId = dep₀) :
    ∀ (w : Nat) (st : IdealCustodyState PK D Sig), sepLeavesFresh w tr →
      st.SafeInv S oracleSign dep₀ pk₀ quorum₀ → SepCustodyIdealRel quorum₀ c st →
      st.ledger.nextFreshEpoch ≤ w →
      ∃ st' itr, (idealCustodyMachine S oracleSign dep₀ pk₀ quorum₀).ValidTrace st itr st' ∧
        SepCustodyIdealRel quorum₀ c' st' := by
  induction hTr with
  | nil _ =>
    intro _ st _ _ hRel _
    exact ⟨st, [], .nil _, hRel⟩
  | @accept s s1 _ inp out _ hStep hRest ih =>
    intro w st hLv hSafe hRel hW
    have hStep' : sepCustodyStep d s inp = some (s1, out) := hStep
    have hMono := sepCustody_validTrace_mono hRest
    have hLv' : sepLeafOk w inp ∧ sepLeavesFresh (sepNextLeaf w inp) _ := hLv
    obtain ⟨st1, itr1, hT1, hRel1, hW1⟩ := sepCustodyStep_sim hP hStep' (hMono.1 hNF)
      (fun a ha => hSD a (hMono.2 a ha)) hLv'.1 hSafe hRel hW
    obtain ⟨st', itr, hT, hRel'⟩ := ih hNF hSD _ st1 hLv'.2
      (idealCustody_validTrace_safeInv hSafe hT1) hRel1 hW1
    exact ⟨st', itr1 ++ itr, sep_validTrace_append hT1 hT, hRel'⟩
  | reject _ _ _ ih => exact ih hNF hSD

/-- **The real separated-custody coordinator against the ideal custody functionality.** Take any
    run of the separated-custody world for deployment `d` from its initial state: custodians sign
    with the production signer `Custody.sign`, parties are corrupted adaptively below the
    threshold, and the coordinator is `Custody.submitRecorded` on arbitrary submitted certificate
    lists. If the run satisfies `SeparatedCustodyRunAssumptions`, its final state corresponds
    (`SepCustodyIdealRel`) to a reachable state of `Spec.idealCustodyMachine`: same spend, same
    consumed sessions, same corruption set, the custodians' signings as honest permits and the
    accepted intents as the authorized intents.

    Proved here: the quorum step. An accepted `submitRecorded` has `threshold` distinct enrolled
    signers (`Custody.acceptQuorum_spec`), each a corrupted party or, by `noForgery` and
    `singleDeployment`, a custodian with a recorded permit, so the ideal `.sign` is accepted.

    Assumed (fields of `SeparatedCustodyRunAssumptions`, none provable from `Qsag.Custody.*`):
    `noForgery`, `singleDeployment`, `leavesIncrease`. Not covered: the ideal machine's signature
    output and WAL replay (the coordinator outputs a verdict only, so `S` and `oracleSign` are
    arbitrary), and any bound on the probability of the forgery event. No run with an accepted
    submission is exhibited in the tree; that needs an evaluated production signature. -/
theorem separatedCustody_refines_idealCustody_of
    (d : Qsag.Custody.Deployment) (S : CustodyDigestScheme D) (oracleSign : D → Sig)
    (dep₀ : Nat) (pk₀ : PK) (quorum₀ : CustodyQuorumProfile)
    (hProfile : SepDeploymentProfile d quorum₀)
    {c₀ c : SepCustodyState} {tr : List (SepCustodyInput × SepCustodyOutput)}
    (hInit : (sepCustodyMachine d).Init c₀)
    (hTr : (sepCustodyMachine d).ValidTrace c₀ tr c)
    (hRun : SeparatedCustodyRunAssumptions dep₀ tr c) :
    ∃ st : IdealCustodyState PK D Sig,
      (idealCustodyMachine S oracleSign dep₀ pk₀ quorum₀).Reachable st ∧
      SepCustodyIdealRel quorum₀ c st := by
  have h0 : c₀ = ⟨⟨⟨[], 0, d.capacity⟩, []⟩, [], [], []⟩ := hInit
  subst h0
  obtain ⟨st', itr, hT, hRel⟩ := sepCustody_validTrace_sim (S := S) (oracleSign := oracleSign)
    (pk₀ := pk₀) hProfile hTr hRun.noForgery hRun.singleDeployment 0
    (IdealCustodyState.init dep₀ pk₀ quorum₀) hRun.leavesIncrease
    (IdealCustodyState.init_safeInv (PK := PK) S oracleSign dep₀ pk₀ quorum₀)
    { poisoned := rfl
      spent := rfl
      capacity := hProfile.capacity
      sessions := rfl
      corrupt := rfl
      honest := rfl
      authorized := rfl }
    (Nat.le_refl _)
  exact ⟨st', ⟨_, itr, rfl, hT⟩, hRel⟩

end Sim

/-- **Every submission the real coordinator accepted was signed by an enrolled custodian for this
    deployment**, on runs satisfying `SeparatedCustodyRunAssumptions`. Obtained through the ideal
    functionality's honest-approval theorem. -/
theorem separatedCustody_accepted_honestly_approved
    (d : Qsag.Custody.Deployment) (dep₀ : Nat) (quorum₀ : CustodyQuorumProfile)
    (hProfile : SepDeploymentProfile d quorum₀)
    {c₀ c : SepCustodyState} {tr : List (SepCustodyInput × SepCustodyOutput)}
    (hInit : (sepCustodyMachine d).Init c₀)
    (hTr : (sepCustodyMachine d).ValidTrace c₀ tr c)
    (hRun : SeparatedCustodyRunAssumptions dep₀ tr c) :
    ∀ a ∈ c.shared.accepted, ∃ b ∈ c.issued,
      b.party < d.numParties ∧ b.deploymentId = dep₀ ∧ b.intent = a.intent := by
  obtain ⟨st, hR, hRel⟩ := separatedCustody_refines_idealCustody_of d
    CustodyDigestScheme.transparent id dep₀ () quorum₀ hProfile hInit hTr hRun
  obtain ⟨_, _, hAuth, _⟩ := idealCustody_reachable_spend_accounting hR
  intro a ha
  have hMem : sepIntent a.intent ∈ st.ledger.authorized := by
    rw [hRel.authorized]
    exact List.mem_map_of_mem (f := fun a : Qsag.Custody.AcceptedSubmission => sepIntent a.intent) ha
  obtain ⟨p, hp, hm⟩ := hAuth _ hMem
  rw [hRel.honest] at hm
  obtain ⟨b, hb, hbe⟩ := List.mem_map.mp hm
  have h1 : b.party = p := congrArg CustodyApproval.party hbe
  have h2 : b.deploymentId = dep₀ := congrArg CustodyApproval.deploymentId hbe
  have h3 : sepIntent b.intent = sepIntent a.intent := congrArg CustodyApproval.intent hbe
  refine ⟨b, hb, ?_, h2, sepIntent_injective h3⟩
  rw [h1, hProfile.parties]
  exact hp

end SeparatedCustodyIdeal

#verify_constructive
  Qsag.Top.rssSharedRelease_preserves_traces
  Qsag.Top.elf_to_idealTsig_trace_inclusion
  Qsag.Top.separated_custody_provenance_and_release_chain
  Qsag.Top.threshold_durable_feedback_and_resource_burn_chain
  Qsag.Top.posix_wal_commit_and_anchor_rollback_fence
  Qsag.Top.rss_participant_network_gate_and_signing_execution_chain
  Qsag.Top.gate_batches_and_quorum_switching_disjointness
  Qsag.Top.certCustody_noForgery_validTrace_abs
  Qsag.Top.certCustody_noForgery_reachable_ideal
  Qsag.Top.certCustody_reachable_spend_and_provenance
  Qsag.Top.certCustody_noForgery_signature_approved_before
  Qsag.Top.certCustody_noForgery_no_unsafe_release
  Qsag.Top.certCustody_unsafe_release_le_forgery
  Qsag.Top.certRun_forgery_submitted
  Qsag.Top.macCustody_unsafe_release_le_key_guess
  Qsag.Top.certCustody_tooth_relayed_certificates_release
  Qsag.Top.sepCustody_stale_leaf_rejected_by_ideal
  Qsag.Top.separatedCustody_refines_idealCustody_of
  Qsag.Top.separatedCustody_accepted_honestly_approved

#tooth_pair Qsag.Top.certCustody_noForgery_no_unsafe_release vs
  Qsag.Top.certCustody_tooth_forged_certificates_unsafe_release
#tooth_pair Qsag.Top.certRun_forgery_submitted vs
  Qsag.Top.certCustody_tooth_wrong_tag_rejected

end Qsag.Top
end
