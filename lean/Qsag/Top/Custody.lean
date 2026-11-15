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
public import Qsag.SeparatedCustodyUcBridge
public import Qsag.RssProductionProfile
public import Qsag.MirSpecBridge
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
    Qsag.Spec.Machine Qsag.MirPolicyGuardState Qsag.PolicyEvalInput Qsag.PolicyEvalVerdict :=
  Qsag.Spec.Machine.ofPartyMachine (fun m => m = m₀) Qsag.mirPolicyGuardMachine

/-- Wrap `SpecPolicyGuardState` (`specPolicyGuardMachine`) as an initialized `Spec.Machine`. -/
def specPolicyMachine (s₀ : Qsag.SpecPolicyGuardState) :
    Qsag.Spec.Machine Qsag.SpecPolicyGuardState Qsag.PolicyEvalInput Qsag.PolicyEvalVerdict :=
  Qsag.Spec.Machine.ofPartyMachine (fun s => s = s₀) Qsag.specPolicyGuardMachine

/-- Lift `mirPolicyGuard_forwardSim_custodyPolicy` into `Spec.Refines`. -/
def mirPolicy_refines_specPolicy
    (m₀ : Qsag.MirPolicyGuardState) (s₀ : Qsag.SpecPolicyGuardState)
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

#verify_constructive
  Qsag.Top.rssSharedRelease_preserves_traces
  Qsag.Top.elf_to_idealTsig_trace_inclusion
  Qsag.Top.separated_custody_provenance_and_release_chain

end Qsag.Top
end
