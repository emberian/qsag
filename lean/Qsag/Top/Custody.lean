module
public import Qsag.Custody.VolatileCoupon
/-
# Qsag.Top.Custody — End-to-End Composed Separated Threshold Custody Refinements and Mediation

Top-level composition module (zero `import all`) unifying the threshold custody, crash-WAL,
complete-mediation, and 4-layer ELF-to-Ideal simulation proofs through `Qsag.Spec.Refines` and
`Qsag.Spec.IdealCustody`:
1. Vertical `Spec.Refines.trans` composition of the 4-layer `ELF → MIR → Protocol → IdealTsig`
   machine hierarchy (`MirSpecBridgeCore`, `MirSpecBridge`),
2. Equality of the shared-evaluation RSS release machine and the reference release machine
   (`rssSharedReleaseMachine_eq_reference`), and of the shared and ideal threshold services
   (`thresholdServiceShared_eq_ideal`, `thresholdDurableShared_eq_ideal`). These are equalities of
   machines over one state type; no `Spec.Refines` witness is packaged for them,
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
   `SeparatedCustodyRunAssumptions` (`separatedCustody_refines_idealCustody_of`), and its guarded
   restriction `sepCustodyGuardedMachine` (no forged certificate, increasing leaves), which outputs
   the coordinator's decision and no signature. The ELF, MIR, `IdealTsig`, RSS and WAL machines of
   items 1–4 are not connected to `Spec.idealCustodyMachine`.
7. Distributed `(t, n)` Shamir custody (`DistCustody.distMachine`: custodians, network buffer,
   adaptive corruption, coordinator ledger) refines `Spec.idealCustodyMachine` for its own
   `deploymentId` (`distributedCustody_refines_idealCustody`), and the Shamir + `BeltLatch`
   validator network: per-custodian refinement to the mediation vault and network non-equivocation
   (`shamirCustodian_refines_mediationVault`, `shamir_custody_network_non_equivocation`).
8. The authenticated custodian network (`DistCustody.authMachine`: a `Fin n` family of custodians
   with WAL records sealed under `"QSAG.BELT.LATCH.WAL.MAC/v3"` and an external anchor,
   acknowledgements tagged under `"QSAG.BELT.ACK.v1"`, a wire the adversary writes freely, disk
   tampering, crashes and adaptive corruption). Its guarded restriction refines
   `Spec.idealCustodyMachine` (`authenticatedCustody_refines_idealCustody`); every execution of the
   unguarded machine is an ideal execution or exhibits a tag forgery, a message-tag collision or a
   hash collision (`authenticatedCustody_ideal_or_forgery`); and over any finite coin space
   `Pr[unsafe release] ≤ Pr[acknowledgement violation] + Pr[WAL violation]`
   (`authenticatedCustody_unsafe_release_le_violations`). The two right-hand probabilities are not
   bounded in this library.
-/

public import Qsag.Protocol.Migration.HdToprfAndMigrationSecurity
public import Qsag.Spec.Primitives
public import Qsag.Spec.Parameters
public import Qsag.Spec.Refines
public import Qsag.Exec.RefinesBridges
public import Qsag.Spec.GameBound
public import Qsag.Spec.Assumptions
public import Qsag.Spec.IdealCustody
public import Qsag.Top.Signing
public import Qsag.Exec.SeparatedCustodyUc
public import Qsag.Custody.SeparatedCustody
public import Qsag.Exec.SeparatedCustodyResource
public import Qsag.Custody.JortsBeltLatchAndQuorumSwitching
public import Qsag.Custody.ShamirThresholdCustodyRefinement
public import Qsag.Custody.DistributedThresholdCustodyRefinement
public import Qsag.Exec.ThresholdIdealService
public import Qsag.Exec.ThresholdIdealDurableService
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
public import Qsag.Machine.MirSpecBridge
public import Qsag.Protocol.Threshold.IdealTsig
public import Qsag.Protocol.Aggregation.UcGames
public import Qsag.Protocol.Threshold.MaliciousSecurity
public import Qsag.Protocol.Threshold.Preprocessing
public import Qsag.Exec.InteractiveUcEngine
public import Qsag.Protocol.Threshold.BaggyAndRss256Security
public import Qsag.Exec.PosixCrashWal
public import Qsag.Exec.PlatformContractInstances
public import Qsag.Exec.TwoSlotHwmCrashModel
public import Qsag.Exec.GuardedMachineSim
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Top

open scoped Qsag.Spec

set_option autoImplicit false

/-! ## 1. Shared RSS Release Equals Reference Release -/

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

/-- The shared-evaluation release machine and the reference release machine are the same
    machine: `RssProduction.release` computes the reference output. The state is the WAL latch
    alone, so this is an equality of functions and not a statement about distributed shares. -/
theorem rssSharedReleaseMachine_eq_reference (p : Qsag.RssProduction.Profile) :
    rssSharedReleaseMachine p = rssReferenceReleaseMachine p := by
  have h : (fun (w : Qsag.WalLatchState) (req : Qsag.SessionScheduleReq) =>
        Qsag.RssProduction.release p req w) =
      (fun w req => Qsag.RssProduction.referenceRelease p req w) :=
    funext fun w => funext fun req => Qsag.RssProduction.release_eq_reference p req w
  unfold rssSharedReleaseMachine rssReferenceReleaseMachine
  rw [h]

/-- A consequence of the equality `rssSharedReleaseMachine_eq_reference` and of nothing else: the
    two machines admit the same traces. No refinement witness is packaged for this pair; the
    distributed custody refinements are in Section 9. -/
theorem rssSharedRelease_preserves_traces (p : Qsag.RssProduction.Profile)
    {tr : List (Qsag.SessionScheduleReq × Except Qsag.RssProduction.Failure (List UInt8))}
    (hAdmits : (rssSharedReleaseMachine p).AdmitsTrace tr) :
    (rssReferenceReleaseMachine p).AdmitsTrace tr :=
  rssSharedReleaseMachine_eq_reference p ▸ hAdmits

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

/-- Vertical composition of lockstep forward refinement (`M₁ ⊑ M₂`) followed by interface-abstracting
    stuttering simulation (`Spec.DataRefines M₂ M₃ visIn visOut`), using `0 Classical.choice`. -/
def refines_trans_dataRefines {S₁ S₂ S₃ In₁₂ In₃ Out₁₂ Out₃ : Type}
    {M₁ : Qsag.Spec.Machine S₁ In₁₂ Out₁₂}
    {M₂ : Qsag.Spec.Machine S₂ In₁₂ Out₁₂}
    {M₃ : Qsag.Spec.Machine S₃ In₃ Out₃}
    {visIn : In₁₂ → Option In₃} {visOut : Out₁₂ → Out₃}
    (r₁₂ : M₁ ⊑ M₂) (d₂₃ : Qsag.Spec.DataRefines M₂ M₃ visIn visOut) :
    Qsag.Spec.DataRefines M₁ M₃ visIn visOut where
  Rel c₁ a₃ := ∃ c₂ : S₂, r₁₂.Rel c₁ c₂ ∧ d₂₃.Rel c₂ a₃
  absInit c₁ := d₂₃.absInit (r₁₂.absInit c₁)
  init_ok {c₁} hInit₁ := by
    obtain ⟨hInit₂, hR₁₂⟩ := r₁₂.init_ok hInit₁
    obtain ⟨hInit₃, hR₂₃⟩ := d₂₃.init_ok hInit₂
    exact ⟨hInit₃, r₁₂.absInit c₁, hR₁₂, hR₂₃⟩
  sim_visible {c₁ c₁' a₃ inp out j} hRel hStep₁ hVis := by
    obtain ⟨c₂, hR₁₂, hR₂₃⟩ := hRel
    have hSim := r₁₂.sim_ok hR₁₂ hStep₁
    cases hStep₂ : M₂.step c₂ inp with
    | none => rw [hStep₂] at hSim; exact False.elim hSim
    | some pair =>
      rcases pair with ⟨c₂', out₂⟩
      rw [hStep₂] at hSim
      rcases hSim with ⟨rfl, hR₁₂'⟩
      obtain ⟨a₃', hStep₃, hR₂₃'⟩ := d₂₃.sim_visible hR₂₃ hStep₂ hVis
      exact ⟨a₃', hStep₃, c₂', hR₁₂', hR₂₃'⟩
  sim_internal {c₁ c₁' a₃ inp out} hRel hStep₁ hInt := by
    obtain ⟨c₂, hR₁₂, hR₂₃⟩ := hRel
    have hSim := r₁₂.sim_ok hR₁₂ hStep₁
    cases hStep₂ : M₂.step c₂ inp with
    | none => rw [hStep₂] at hSim; exact False.elim hSim
    | some pair =>
      rcases pair with ⟨c₂', out₂⟩
      rw [hStep₂] at hSim
      rcases hSim with ⟨_, hR₁₂'⟩
      exact ⟨c₂', hR₁₂', d₂₃.sim_internal hR₂₃ hStep₂ hInt⟩
  sim_reject {c₁ a₃ inp} hRel hNone₁ := by
    obtain ⟨c₂, hR₁₂, hR₂₃⟩ := hRel
    have hErr := r₁₂.sim_err hR₁₂ hNone₁
    cases hStep₂ : M₂.step c₂ inp with
    | none =>
      rw [hStep₂] at hErr
      exact ⟨M₂.errStep c₂ inp, hErr.2, d₂₃.sim_reject hR₂₃ hStep₂⟩
    | some _ =>
      rw [hStep₂] at hErr
      exact nomatch hErr.1

/-- Top-level re-export of `IdealTsig ⊑ Spec.idealCustodyMachine` (`L-Ex-7`):
    `idealTsigCustodyMachine` refines `Spec.idealCustodyMachine` under `Spec.DataRefines`,
    resolving the side-by-side custody target split. -/
def idealTsig_refines_idealCustody {PK SK D Sig : Type} [DecidableEq D]
    (S_sig : Qsag.AbstractSigScheme PK SK D Sig)
    (S_dig : Qsag.Spec.CustodyDigestScheme D) (oracleSign : D → Sig)
    (dep₀ : Nat) (pk₀ : PK) (quorum₀ : Qsag.Spec.CustodyQuorumProfile) :
    Qsag.Spec.DataRefines
      (Qsag.idealTsigCustodyMachine S_sig S_dig oracleSign dep₀ pk₀ quorum₀)
      (Qsag.Spec.idealCustodyMachine S_dig oracleSign dep₀ pk₀ quorum₀)
      Qsag.idealTsigVisIn Qsag.idealTsigVisOut :=
  Qsag.idealTsig_dataRefines_idealCustody S_sig S_dig oracleSign dep₀ pk₀ quorum₀

/-- Canonical `CustodyIntent` corresponding to a 4-layer signing request `req : FourLayerReq n`. -/
def fourLayerCustodyIntent {n : Nat} (req : Qsag.FourLayerReq n) : Qsag.Spec.CustodyIntent :=
  let tx := req.tx.toTransactionIntent
  { sessionId := tx.nonce
    round := 0
    epoch := req.reqEpoch
    spend := tx.amount_units
    payload := Qsag.encodeTransactionIntent tx }

/-- Custody-harness state wrapping any 4-layer machine state `S_core` (`Layer1ElfState` or
    `Layer4IdealState PK`) with explicit per-party custody permits and adaptive corruption
    enrollment up to the static corruption set. -/
structure FourLayerCustodyState (S_core : Type) where
  core : S_core
  honestPermits : List Qsag.Spec.CustodyApproval
  corruptPermits : List Qsag.Spec.CustodyApproval
  enrolledCorrupt : List Nat
  poisoned : Bool

/-- Alphabet of the 4-layer custody harness. -/
inductive FourLayerCustodyTurn (n : Nat) where
  | approve (party deploymentId : Nat) (intent : Qsag.Spec.CustodyIntent)
  | advApprove (party deploymentId : Nat) (intent : Qsag.Spec.CustodyIntent)
  | corrupt (party : Fin n)
  | execute (deploymentId : Nat) (req : Qsag.FourLayerReq n)

/-- Output events of the 4-layer custody harness. -/
abbrev FourLayerCustodyOut := Qsag.Spec.CustodyOutcome ByteArray

/-- Quorum-permit check verifying `q` distinct validators in `req.quorum`, each backed by a
    recorded honest or adversarial custody permit for `(dep₀, i)`. -/
def fourLayerPermitsReady {n : Nat} (q dep₀ : Nat)
    (honestPermits corruptPermits : List Qsag.Spec.CustodyApproval)
    (enrolledCorrupt : List Nat)
    (quorum : List (Fin n)) (i : Qsag.Spec.CustodyIntent) : Bool :=
  decide (q ≤ quorum.length) &&
  decide (quorum.map Fin.val).Nodup &&
  quorum.all (fun p =>
    if decide (p.val ∈ enrolledCorrupt) then
      decide (Qsag.Spec.CustodyApproval.mk p.val dep₀ i ∈ corruptPermits)
    else
      decide (Qsag.Spec.CustodyApproval.mk p.val dep₀ i ∈ honestPermits))

/-- Step function lifting a 4-layer core machine `M` into the `Spec.CustodyInput` alphabet. -/
@[expose] def fourLayerCustodyStep {S_core : Type} {n : Nat}
    (q dep₀ : Nat) (corrupt : List (Fin n))
    (M : Qsag.Spec.Machine S_core (Qsag.FourLayerReq n) Qsag.FourLayerOut)
    (st : FourLayerCustodyState S_core) (turn : FourLayerCustodyTurn n) :
    Option (FourLayerCustodyState S_core × FourLayerCustodyOut) :=
  if st.poisoned then none
  else
    match turn with
    | .approve p dep i =>
      if p < n ∧ p ∉ st.enrolledCorrupt ∧ dep = dep₀ then
        some ({ st with honestPermits := ⟨p, dep, i⟩ :: st.honestPermits }, .approvalRecorded)
      else none
    | .advApprove p dep i =>
      if p ∈ st.enrolledCorrupt ∧ dep = dep₀ then
        some ({ st with corruptPermits := ⟨p, dep, i⟩ :: st.corruptPermits }, .approvalRecorded)
      else none
    | .corrupt p =>
      if p.val ∈ corrupt.map Fin.val ∧ p.val ∉ st.enrolledCorrupt ∧ st.enrolledCorrupt.length + 1 < q then
        some ({ st with enrolledCorrupt := p.val :: st.enrolledCorrupt },
              .corrupted (Qsag.Spec.custodyRevealed st.honestPermits p.val))
      else none
    | .execute dep req =>
      let i := fourLayerCustodyIntent req
      if dep = dep₀ ∧ fourLayerPermitsReady q dep₀ st.honestPermits st.corruptPermits
          st.enrolledCorrupt req.quorum i = true then
        match M.step st.core req with
        | some (core', out4) =>
          some ({ st with core := core' }, .released out4.sigBytes)
        | none => none
      else none

/-- Persistent error transition propagating `M.errStep` (including Layer-1 ELF `ct_memzero`
    secret-share zeroization) and latching `poisoned := true` on core execution failure. -/
def fourLayerCustodyErrStep {S_core : Type} {n : Nat}
    (q dep₀ : Nat)
    (M : Qsag.Spec.Machine S_core (Qsag.FourLayerReq n) Qsag.FourLayerOut)
    (st : FourLayerCustodyState S_core) (turn : FourLayerCustodyTurn n) :
    FourLayerCustodyState S_core :=
  if st.poisoned then st
  else
    match turn with
    | .execute dep req =>
      let i := fourLayerCustodyIntent req
      if dep = dep₀ ∧ fourLayerPermitsReady q dep₀ st.honestPermits st.corruptPermits
          st.enrolledCorrupt req.quorum i = true then
        match M.step st.core req with
        | some _ => st
        | none => { st with core := M.errStep st.core req, poisoned := true }
      else st
    | _ => st

/-- Reactive `Spec.Machine` wrapping a 4-layer core machine `M` at initial state `s₀`. -/
def fourLayerCustodyMachine {S_core : Type} {n : Nat}
    (q dep₀ : Nat) (corrupt : List (Fin n)) (s₀ : S_core)
    (M : Qsag.Spec.Machine S_core (Qsag.FourLayerReq n) Qsag.FourLayerOut) :
    Qsag.Spec.Machine (FourLayerCustodyState S_core) (FourLayerCustodyTurn n) FourLayerCustodyOut where
  Init st := st = ⟨s₀, [], [], [], false⟩
  step := fourLayerCustodyStep q dep₀ corrupt M
  errStep := fourLayerCustodyErrStep q dep₀ M

@[expose] def fourLayerCustodyVisIn {n : Nat} :
    FourLayerCustodyTurn n → Option Qsag.Spec.CustodyInput
  | .approve p dep i => some (.approve p dep i)
  | .advApprove p dep i => some (.advApprove p dep i)
  | .corrupt p => some (.corrupt p.val)
  | .execute dep req => some (.sign dep (fourLayerCustodyIntent req) false)

@[expose] def fourLayerCustodyVisOut : FourLayerCustodyOut → FourLayerCustodyOut := id

private theorem fl_if_pos {α : Type} {p : Prop} [Decidable p] (hp : p) (a b : α) :
    (if p then a else b) = a := by
  cases ‹Decidable p› with
  | isTrue _ => rfl
  | isFalse hn => exact False.elim (hn hp)

private theorem fl_if_neg {α : Type} {p : Prop} [Decidable p] (hnp : ¬ p) (a b : α) :
    (if p then a else b) = b := by
  cases ‹Decidable p› with
  | isTrue hp => exact False.elim (hnp hp)
  | isFalse _ => rfl

/-- Functorial lift: any forward simulation `M₁ ⊑ M₂` lifts to
    `fourLayerCustodyMachine q dep₀ corrupt s₁₀ M₁ ⊑ fourLayerCustodyMachine q dep₀ corrupt s₂₀ M₂`. -/
def fourLayerCustody_lift_refines {S₁ S₂ : Type} {n : Nat}
    (q dep₀ : Nat) (corrupt : List (Fin n))
    (s₁₀ : S₁) (s₂₀ : S₂)
    {M₁ : Qsag.Spec.Machine S₁ (Qsag.FourLayerReq n) Qsag.FourLayerOut}
    {M₂ : Qsag.Spec.Machine S₂ (Qsag.FourLayerReq n) Qsag.FourLayerOut}
    (sim : M₁ ⊑ M₂)
    (hInit₁ : M₁.Init s₁₀)
    (hMap₀ : sim.absInit s₁₀ = s₂₀) :
    fourLayerCustodyMachine q dep₀ corrupt s₁₀ M₁ ⊑
      fourLayerCustodyMachine q dep₀ corrupt s₂₀ M₂ where
  Rel c₁ c₂ :=
    sim.Rel c₁.core c₂.core ∧
    c₁.honestPermits = c₂.honestPermits ∧
    c₁.corruptPermits = c₂.corruptPermits ∧
    c₁.enrolledCorrupt = c₂.enrolledCorrupt ∧
    c₁.poisoned = c₂.poisoned
  absInit _ := ⟨s₂₀, [], [], [], false⟩
  init_ok {c₁} hC₁ := by
    subst hC₁
    obtain ⟨_, hRel₀⟩ := sim.init_ok hInit₁
    rw [hMap₀] at hRel₀
    exact ⟨rfl, hRel₀, rfl, rfl, rfl, rfl⟩
  sim_ok {c₁ c₁' c₂ turn out} hRel hStep₁ := by
    rcases hRel with ⟨hCore, hHon, hCorr, hEnr, hPois⟩
    dsimp only [fourLayerCustodyMachine] at hStep₁ ⊢
    unfold fourLayerCustodyStep at hStep₁ ⊢
    cases hP₁ : c₁.poisoned with
    | true => rw [hP₁] at hStep₁; simp at hStep₁
    | false =>
      have hP₂ : c₂.poisoned = false := hPois.symm.trans hP₁
      rw [hP₁] at hStep₁
      rw [hP₂]
      simp only [Bool.false_eq_true, ↓reduceIte] at hStep₁ ⊢
      cases turn with
      | approve p dep i =>
        dsimp only at hStep₁ ⊢
        by_cases hg : p < n ∧ p ∉ c₁.enrolledCorrupt ∧ dep = dep₀
        · rw [fl_if_pos hg] at hStep₁
          cases hStep₁
          have hg₂ : p < n ∧ p ∉ c₂.enrolledCorrupt ∧ dep = dep₀ := by
            rw [← hEnr]; exact hg
          rw [fl_if_pos hg₂]
          exact ⟨rfl, hCore, congrArg (List.cons _) hHon, hCorr, hEnr, rfl⟩
        · rw [fl_if_neg hg] at hStep₁; cases hStep₁
      | advApprove p dep i =>
        dsimp only at hStep₁ ⊢
        by_cases hg : p ∈ c₁.enrolledCorrupt ∧ dep = dep₀
        · rw [fl_if_pos hg] at hStep₁
          cases hStep₁
          have hg₂ : p ∈ c₂.enrolledCorrupt ∧ dep = dep₀ := by
            rw [← hEnr]; exact hg
          rw [fl_if_pos hg₂]
          exact ⟨rfl, hCore, hHon, congrArg (List.cons _) hCorr, hEnr, rfl⟩
        · rw [fl_if_neg hg] at hStep₁; cases hStep₁
      | corrupt p =>
        dsimp only at hStep₁ ⊢
        by_cases hg : p.val ∈ corrupt.map Fin.val ∧ p.val ∉ c₁.enrolledCorrupt ∧ c₁.enrolledCorrupt.length + 1 < q
        · rw [fl_if_pos hg] at hStep₁
          cases hStep₁
          have hg₂ : p.val ∈ corrupt.map Fin.val ∧ p.val ∉ c₂.enrolledCorrupt ∧ c₂.enrolledCorrupt.length + 1 < q := by
            rw [← hEnr]; exact hg
          rw [fl_if_pos hg₂, ← hHon]
          exact ⟨rfl, hCore, rfl, hCorr, congrArg (List.cons _) hEnr, rfl⟩
        · rw [fl_if_neg hg] at hStep₁; cases hStep₁
      | execute dep req =>
        dsimp only at hStep₁ ⊢
        let i := fourLayerCustodyIntent req
        by_cases hg : dep = dep₀ ∧ fourLayerPermitsReady q dep₀ c₁.honestPermits c₁.corruptPermits
            c₁.enrolledCorrupt req.quorum i = true
        · rw [fl_if_pos hg] at hStep₁
          have hg₂ : dep = dep₀ ∧ fourLayerPermitsReady q dep₀ c₂.honestPermits c₂.corruptPermits
              c₂.enrolledCorrupt req.quorum i = true := by
            rw [← hHon, ← hCorr, ← hEnr]; exact hg
          rw [fl_if_pos hg₂]
          cases hM₁ : M₁.step c₁.core req with
          | none => rw [hM₁] at hStep₁; cases hStep₁
          | some p₁ =>
            rcases p₁ with ⟨core₁', out4⟩
            rw [hM₁] at hStep₁
            cases hStep₁
            have hSim := sim.sim_ok hCore hM₁
            cases hM₂ : M₂.step c₂.core req with
            | none => rw [hM₂] at hSim; exact False.elim hSim
            | some p₂ =>
              rcases p₂ with ⟨core₂', out4₂⟩
              rw [hM₂] at hSim
              rcases hSim with ⟨rfl, hCore'⟩
              exact ⟨rfl, hCore', hHon, hCorr, hEnr, rfl⟩
        · rw [fl_if_neg hg] at hStep₁; cases hStep₁
  sim_err {c₁ c₂ turn} hRel hNone₁ := by
    rcases hRel with ⟨hCore, hHon, hCorr, hEnr, hPois⟩
    dsimp only [fourLayerCustodyMachine] at hNone₁ ⊢
    unfold fourLayerCustodyStep at hNone₁ ⊢
    unfold fourLayerCustodyErrStep
    cases hP₁ : c₁.poisoned with
    | true =>
      have hP₂ : c₂.poisoned = true := hPois.symm.trans hP₁
      rw [hP₂]
      simp only [↓reduceIte]
      exact ⟨trivial, hCore, hHon, hCorr, hEnr, hPois⟩
    | false =>
      have hP₂ : c₂.poisoned = false := hPois.symm.trans hP₁
      rw [hP₁] at hNone₁
      rw [hP₂]
      simp only [Bool.false_eq_true, ↓reduceIte] at hNone₁ ⊢
      cases turn with
      | approve p dep i =>
        dsimp only at hNone₁ ⊢
        by_cases hg : p < n ∧ p ∉ c₁.enrolledCorrupt ∧ dep = dep₀
        · rw [fl_if_pos hg] at hNone₁; cases hNone₁
        · have hg₂ : ¬ (p < n ∧ p ∉ c₂.enrolledCorrupt ∧ dep = dep₀) := by
            rw [← hEnr]; exact hg
          rw [fl_if_neg hg₂]
          exact ⟨rfl, hCore, hHon, hCorr, hEnr, hPois⟩
      | advApprove p dep i =>
        dsimp only at hNone₁ ⊢
        by_cases hg : p ∈ c₁.enrolledCorrupt ∧ dep = dep₀
        · rw [fl_if_pos hg] at hNone₁; cases hNone₁
        · have hg₂ : ¬ (p ∈ c₂.enrolledCorrupt ∧ dep = dep₀) := by
            rw [← hEnr]; exact hg
          rw [fl_if_neg hg₂]
          exact ⟨rfl, hCore, hHon, hCorr, hEnr, hPois⟩
      | corrupt p =>
        dsimp only at hNone₁ ⊢
        by_cases hg : p.val ∈ corrupt.map Fin.val ∧ p.val ∉ c₁.enrolledCorrupt ∧ c₁.enrolledCorrupt.length + 1 < q
        · rw [fl_if_pos hg] at hNone₁; cases hNone₁
        · have hg₂ : ¬ (p.val ∈ corrupt.map Fin.val ∧ p.val ∉ c₂.enrolledCorrupt ∧ c₂.enrolledCorrupt.length + 1 < q) := by
            rw [← hEnr]; exact hg
          rw [fl_if_neg hg₂]
          exact ⟨rfl, hCore, hHon, hCorr, hEnr, hPois⟩
      | execute dep req =>
        dsimp only at hNone₁ ⊢
        let i := fourLayerCustodyIntent req
        by_cases hg : dep = dep₀ ∧ fourLayerPermitsReady q dep₀ c₁.honestPermits c₁.corruptPermits
            c₁.enrolledCorrupt req.quorum i = true
        · have hg₂ : dep = dep₀ ∧ fourLayerPermitsReady q dep₀ c₂.honestPermits c₂.corruptPermits
              c₂.enrolledCorrupt req.quorum i = true := by
            rw [← hHon, ← hCorr, ← hEnr]; exact hg
          rw [fl_if_pos hg] at hNone₁ ⊢
          rw [fl_if_pos hg₂, fl_if_pos hg₂]
          cases hM₁ : M₁.step c₁.core req with
          | some _ => rw [hM₁] at hNone₁; cases hNone₁
          | none =>
            have hErr := sim.sim_err hCore hM₁
            cases hM₂ : M₂.step c₂.core req with
            | some _ => rw [hM₂] at hErr; exact nomatch hErr.1
            | none =>
              rw [hM₂] at hErr
              exact ⟨rfl, hErr.2, hHon, hCorr, hEnr, rfl⟩
        · have hg₂ : ¬ (dep = dep₀ ∧ fourLayerPermitsReady q dep₀ c₂.honestPermits c₂.corruptPermits
              c₂.enrolledCorrupt req.quorum i = true) := by
            rw [← hHon, ← hCorr, ← hEnr]; exact hg
          rw [fl_if_neg hg, fl_if_neg hg₂, fl_if_neg hg₂]
          exact ⟨rfl, hCore, hHon, hCorr, hEnr, hPois⟩

/-- Simulation invariant connecting `fourLayerCustodyMachine ... (layer4IdealTsigMachine ...)`
    to `Spec.idealCustodyMachine` with zero extra initial-state hypotheses on `s4₀`. -/
structure Layer4CustodyIdealRel {PK : Type} {n : Nat}
    (dep₀ : Nat) (pk₀ : PK) (quorum₀ : Qsag.Spec.CustodyQuorumProfile)
    (c : FourLayerCustodyState (Qsag.Layer4IdealState PK))
    (a : Qsag.Spec.IdealCustodyState PK (Nat × Qsag.Spec.CustodyIntent) ByteArray)
    (idealSignOracle : List UInt8 → ByteArray) : Prop where
  safe : a.SafeInv Qsag.Spec.CustodyDigestScheme.transparent
    (fun d => idealSignOracle d.2.payload) dep₀ pk₀ quorum₀
  notPoisonedA : a.ledger.poisoned = false
  honestEq : a.honestApprovals = c.honestPermits
  corruptAppEq : a.corruptApprovals = c.corruptPermits
  corruptEq : a.corruptParties = c.enrolledCorrupt
  activeAlign : c.poisoned = false →
    a.ledger.nextFreshEpoch ≤ c.core.ideal.honestWal.nextEpoch ∧
    a.ledger.spent ≤ c.core.policy.accumulated_spend ∧
    c.core.policy.velocity_window_cap = quorum₀.spendCap ∧
    (∀ u ∈ a.ledger.usedSessions, u ∈ c.core.policy.burned_intent_nonces)

/-- **`layer4IdealTsigMachine` Refines `Spec.idealCustodyMachine` (`layer4IdealTsig_dataRefines_idealCustody`)**:
    Proves `Spec.DataRefines` from the Layer-4 `IdealTsig` custody machine into
    `Spec.idealCustodyMachine` using `policyGuardStep_accepted_inv`, `WalLatchState` strict epoch
    monotonicity, and `custodyApprovers_length_le_of_subset`. -/
def layer4IdealTsig_dataRefines_idealCustody {PK : Type} {n q : Nat}
    (corrupt : List (Fin n)) (pkDigestOf : PK → List UInt8) (pk : PK)
    (idealSignOracle : List UInt8 → ByteArray)
    (hQPos : 0 < q) (hQLeN : q ≤ n)
    (dep₀ : Nat) (s4₀ : Qsag.Layer4IdealState PK) :
    let quorum₀ : Qsag.Spec.CustodyQuorumProfile :=
      { numParties := n
        threshold := q
        spendCap := s4₀.policy.velocity_window_cap
        h_pos := hQPos
        h_le := hQLeN }
    let M4 := Qsag.Spec.Machine.ofPartyMachine (fun s => s = s4₀)
      (Qsag.layer4IdealTsigMachine corrupt pkDigestOf idealSignOracle)
    Qsag.Spec.DataRefines
      (fourLayerCustodyMachine q dep₀ corrupt s4₀ M4)
      (Qsag.Spec.idealCustodyMachine Qsag.Spec.CustodyDigestScheme.transparent
        (fun d => idealSignOracle d.2.payload) dep₀ pk quorum₀)
      fourLayerCustodyVisIn fourLayerCustodyVisOut := by
  intro quorum₀ M4
  let oracle4 : Nat × Qsag.Spec.CustodyIntent → ByteArray := fun d => idealSignOracle d.2.payload
  refine
    { Rel := fun c a => Layer4CustodyIdealRel (n := n) dep₀ pk quorum₀ c a idealSignOracle
      absInit := fun _ => Qsag.Spec.IdealCustodyState.init dep₀ pk quorum₀
      init_ok := ?_
      sim_visible := ?_
      sim_internal := ?_
      sim_reject := ?_ }
  · intro c₀ hInit
    subst hInit
    exact ⟨rfl,
      { safe := Qsag.Spec.IdealCustodyState.init_safeInv
          Qsag.Spec.CustodyDigestScheme.transparent oracle4 dep₀ pk quorum₀
        notPoisonedA := rfl
        honestEq := rfl
        corruptAppEq := rfl
        corruptEq := rfl
        activeAlign := fun _ => ⟨Nat.zero_le _, Nat.zero_le _, rfl, fun _ hm => False.elim (List.not_mem_nil hm)⟩ }⟩
  · intro c c' a turn out j hRel hStepC hVis
    dsimp only [fourLayerCustodyMachine] at hStepC
    unfold fourLayerCustodyStep at hStepC
    cases hPC : c.poisoned with
    | true => rw [hPC] at hStepC; simp at hStepC
    | false =>
      rw [hPC] at hStepC
      simp only [Bool.false_eq_true, ↓reduceIte] at hStepC
      obtain ⟨hEpLe, hSpentLe, hCapEq, hUsedSub⟩ := hRel.activeAlign hPC
      cases turn with
      | approve p dep i =>
        cases hVis
        dsimp only at hStepC
        by_cases hg : p < n ∧ p ∉ c.enrolledCorrupt ∧ dep = dep₀
        · rw [fl_if_pos hg] at hStepC
          cases hStepC
          have hgA : p < a.ledger.quorum.numParties ∧ p ∉ a.corruptParties ∧
              dep = a.ledger.deploymentId := by
            rw [hRel.safe.profile, hRel.corruptEq, hRel.safe.deployment]
            exact hg
          have hStepA := Qsag.Spec.idealCustodyStep_approve_of
            (S := Qsag.Spec.CustodyDigestScheme.transparent) (oracleSign := oracle4) (st := a) i hgA
          exact ⟨_, hStepA,
            { safe := Qsag.Spec.idealCustodyStep_preserves_safeInv hRel.safe hStepA
              notPoisonedA := hRel.notPoisonedA
              honestEq := congrArg (List.cons _) hRel.honestEq
              corruptAppEq := hRel.corruptAppEq
              corruptEq := hRel.corruptEq
              activeAlign := fun _ => ⟨hEpLe, hSpentLe, hCapEq, hUsedSub⟩ }⟩
        · rw [fl_if_neg hg] at hStepC; cases hStepC
      | advApprove p dep i =>
        cases hVis
        dsimp only at hStepC
        by_cases hg : p ∈ c.enrolledCorrupt ∧ dep = dep₀
        · rw [fl_if_pos hg] at hStepC
          cases hStepC
          have hgA : p ∈ a.corruptParties ∧ dep = a.ledger.deploymentId := by
            rw [hRel.corruptEq, hRel.safe.deployment]
            exact hg
          have hStepA := Qsag.Spec.idealCustodyStep_advApprove_of
            (S := Qsag.Spec.CustodyDigestScheme.transparent) (oracleSign := oracle4) (st := a) i hgA
          exact ⟨_, hStepA,
            { safe := Qsag.Spec.idealCustodyStep_preserves_safeInv hRel.safe hStepA
              notPoisonedA := hRel.notPoisonedA
              honestEq := hRel.honestEq
              corruptAppEq := congrArg (List.cons _) hRel.corruptAppEq
              corruptEq := hRel.corruptEq
              activeAlign := fun _ => ⟨hEpLe, hSpentLe, hCapEq, hUsedSub⟩ }⟩
        · rw [fl_if_neg hg] at hStepC; cases hStepC
      | corrupt p =>
        cases hVis
        dsimp only at hStepC
        by_cases hg : p.val ∈ corrupt.map Fin.val ∧ p.val ∉ c.enrolledCorrupt ∧ c.enrolledCorrupt.length + 1 < q
        · rw [fl_if_pos hg] at hStepC
          cases hStepC
          have hgA : p.val < a.ledger.quorum.numParties ∧ p.val ∉ a.corruptParties ∧
              a.corruptParties.length + 1 < a.ledger.quorum.threshold := by
            rw [hRel.safe.profile, hRel.corruptEq]
            exact ⟨p.isLt, hg.2.1, hg.2.2⟩
          have hStepA := Qsag.Spec.idealCustodyStep_corrupt_of
            (S := Qsag.Spec.CustodyDigestScheme.transparent) (oracleSign := oracle4) (st := a) (p := p.val) hgA
          refine ⟨{ a with corruptParties := p.val :: a.corruptParties }, ?_, ?_⟩
          · change Qsag.Spec.idealCustodyStep Qsag.Spec.CustodyDigestScheme.transparent oracle4 a (.corrupt p.val) =
              some ({ a with corruptParties := p.val :: a.corruptParties },
                    .corrupted (Qsag.Spec.custodyRevealed c.honestPermits p.val))
            rw [hStepA, hRel.honestEq]
          · exact
              { safe := Qsag.Spec.idealCustodyStep_preserves_safeInv hRel.safe hStepA
                notPoisonedA := hRel.notPoisonedA
                honestEq := hRel.honestEq
                corruptAppEq := hRel.corruptAppEq
                corruptEq := congrArg (List.cons _) hRel.corruptEq
                activeAlign := fun _ => ⟨hEpLe, hSpentLe, hCapEq, hUsedSub⟩ }
        · rw [fl_if_neg hg] at hStepC; cases hStepC
      | execute dep req =>
        cases hVis
        dsimp only at hStepC
        let i := fourLayerCustodyIntent req
        by_cases hg : dep = dep₀ ∧ fourLayerPermitsReady q dep₀ c.honestPermits c.corruptPermits
            c.enrolledCorrupt req.quorum i = true
        · rw [fl_if_pos hg] at hStepC
          cases hM4 : M4.step c.core req with
          | none => rw [hM4] at hStepC; cases hStepC
          | some pair4 =>
            rcases pair4 with ⟨core4', out4⟩
            rw [hM4] at hStepC
            cases hStepC
            -- Extract Layer-4 authorization facts from `M4.step`
            dsimp only [M4, Qsag.Spec.Machine.ofPartyMachine, Qsag.layer4IdealTsigMachine,
              Qsag.PartyMachine.ofOutcome] at hM4
            cases hPois4 : c.core.ideal.honestWal.poisoned with
            | true => rw [hPois4] at hM4; simp at hM4
            | false =>
              rw [hPois4] at hM4
              simp only [Bool.false_eq_true, ↓reduceIte] at hM4
              cases hPG : Qsag.policyGuardStep c.core.policy req.tx.toTransactionIntent with
              | rejected _ _ => rw [hPG] at hM4; cases hM4
              | accepted pol' env =>
                rw [hPG] at hM4
                dsimp only at hM4
                let honApp := (req.quorum.filter (fun p => !Qsag.finMemBool p corrupt)).map Fin.val
                cases hQ4 : (Qsag.verifyFourLayerQuorumCert c.core.quorumCertConfig
                    c.core.ideal.tsig.threshold (pkDigestOf c.core.ideal.tsig.pk)
                    env.canonicalBytes req && Qsag.validThresholdApproval c.core.ideal.tsig honApp) with
                | false => rw [hQ4] at hM4; simp at hM4
                | true =>
                  rw [hQ4] at hM4
                  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hM4
                  cases hE4 : (decide (pkDigestOf c.core.ideal.tsig.pk =
                      c.core.ideal.honestWal.enrolledPkDigest) &&
                      (req.reqEpoch == c.core.ideal.honestWal.nextEpoch)) with
                  | false => rw [hE4] at hM4; simp at hM4
                  | true =>
                    rw [hE4] at hM4
                    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hM4
                    cases hC4 : Qsag.verifyPreCutTranscript c.core.activeSessionTag
                        c.core.storedRound1Commits c.core.verifierBginAlpha
                        c.core.verifierBginKeyOffsets req.quorum
                        req.round1Openings req.round2Wires with
                    | false => rw [hC4] at hM4; simp at hM4
                    | true =>
                      rw [hC4] at hM4
                      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                        Option.some.injEq, Prod.mk.injEq] at hM4
                      rcases hM4 with ⟨hCoreEq, hOutEq⟩
                      obtain ⟨hNonceFresh, hPolSpendLe, hPolSpend', hPolNonces', hPolCap',
                        _, hEnvBytes⟩ := Qsag.policyGuardStep_accepted_inv hPG
                      have hEpEq : req.reqEpoch = c.core.ideal.honestWal.nextEpoch :=
                        Nat.eq_of_beq_eq_true (Bool.and_eq_true_iff.mp hE4).2
                      have hFreshEp : a.ledger.nextFreshEpoch ≤ i.epoch := by
                        show a.ledger.nextFreshEpoch ≤ req.reqEpoch
                        omega
                      have hFindNone : Qsag.Spec.findReleasedEpoch a.ledger.releasedHistory i.epoch = none := by
                        cases hF : Qsag.Spec.findReleasedEpoch a.ledger.releasedHistory i.epoch with
                        | none => rfl
                        | some r =>
                          obtain ⟨hr, he⟩ := Qsag.Spec.findReleasedEpoch_some hF
                          have hLt := hRel.safe.walFresh r hr
                          omega
                      have hSessFresh : i.sessionId ∉ a.ledger.usedSessions :=
                        fun hIn => hNonceFresh (hUsedSub _ hIn)
                      have hSpendFit : a.ledger.spent + i.spend ≤ a.ledger.quorum.spendCap := by
                        rw [hRel.safe.profile]
                        show a.ledger.spent + req.tx.toTransactionIntent.amount_units ≤ quorum₀.spendCap
                        omega
                      -- Prove quorum permit count
                      unfold fourLayerPermitsReady at hg
                      rcases Bool.and_eq_true_iff.mp hg.2 with ⟨hLeftP, hAllP⟩
                      rcases Bool.and_eq_true_iff.mp hLeftP with ⟨hQLeP, hNdP⟩
                      have hSubP : ∀ pVal ∈ req.quorum.map Fin.val,
                          pVal < a.ledger.quorum.numParties ∧
                          (Qsag.Spec.CustodyApproval.mk pVal a.ledger.deploymentId i ∈ a.honestApprovals ∨
                           Qsag.Spec.CustodyApproval.mk pVal a.ledger.deploymentId i ∈ a.corruptApprovals) := by
                        intro pVal hpVal
                        obtain ⟨pFin, hpFin, rfl⟩ := List.mem_map.mp hpVal
                        rw [hRel.safe.profile, hRel.safe.deployment, hRel.honestEq, hRel.corruptAppEq]
                        refine ⟨pFin.isLt, ?_⟩
                        have hpA := List.all_eq_true.mp hAllP pFin hpFin
                        by_cases hpC : pFin.val ∈ c.enrolledCorrupt
                        · rw [decide_eq_true hpC] at hpA
                          simp only [↓reduceIte] at hpA
                          exact .inr (of_decide_eq_true hpA)
                        · rw [decide_eq_false hpC] at hpA
                          simp only [Bool.false_eq_true, ↓reduceIte] at hpA
                          exact .inl (of_decide_eq_true hpA)
                      have hAppLen : a.ledger.quorum.threshold ≤
                          (Qsag.Spec.custodyApprovers a.ledger.quorum.numParties
                            a.honestApprovals a.corruptApprovals a.ledger.deploymentId i).length := by
                        have hSub := Qsag.Spec.custodyApprovers_length_le_of_subset
                          (of_decide_eq_true hNdP) hSubP
                        rw [List.length_map] at hSub
                        rw [hRel.safe.profile] at hSub ⊢
                        exact Nat.le_trans (of_decide_eq_true hQLeP) hSub
                      have hDepA : dep = a.ledger.deploymentId := hg.1.trans hRel.safe.deployment.symm
                      have hLSign : Qsag.Spec.custodyLedgerSign
                          Qsag.Spec.CustodyDigestScheme.transparent oracle4
                          a.ledger
                          (Qsag.Spec.custodyApprovers a.ledger.quorum.numParties
                            a.honestApprovals a.corruptApprovals a.ledger.deploymentId i).length
                          dep i false =
                          some ({ a.ledger.authorize i with
                                  releasedHistory :=
                                    ⟨i, Qsag.Spec.CustodyDigestScheme.transparent.digest a.ledger.deploymentId i,
                                      oracle4 (Qsag.Spec.CustodyDigestScheme.transparent.digest a.ledger.deploymentId i)⟩ ::
                                      a.ledger.releasedHistory },
                                .released (oracle4 (Qsag.Spec.CustodyDigestScheme.transparent.digest a.ledger.deploymentId i))) := by
                        unfold Qsag.Spec.custodyLedgerSign
                        rw [fl_if_pos (And.intro hRel.notPoisonedA hDepA), hFindNone]
                        dsimp only
                        rw [fl_if_pos (show a.ledger.nextFreshEpoch ≤ i.epoch ∧
                            i.sessionId ∉ a.ledger.usedSessions ∧
                            a.ledger.quorum.threshold ≤ _ ∧
                            a.ledger.spent + i.spend ≤ a.ledger.quorum.spendCap from
                          ⟨hFreshEp, hSessFresh, hAppLen, hSpendFit⟩)]
                        exact fl_if_neg Bool.false_ne_true _ _
                      have hStepA := Qsag.Spec.idealCustodyStep_sign_of
                        (S := Qsag.Spec.CustodyDigestScheme.transparent) (oracleSign := oracle4) (st := a) hLSign
                      have hSigEq : out4.sigBytes =
                          oracle4 (Qsag.Spec.CustodyDigestScheme.transparent.digest a.ledger.deploymentId i) := by
                        rw [← hOutEq]
                        dsimp only [oracle4, Qsag.Spec.CustodyDigestScheme.transparent, i, fourLayerCustodyIntent]
                        rw [hEnvBytes]
                      rw [← hSigEq] at hStepA
                      refine ⟨_, hStepA,
                        { safe := Qsag.Spec.idealCustodyStep_preserves_safeInv hRel.safe
                            hStepA
                          notPoisonedA := hRel.notPoisonedA
                          honestEq := hRel.honestEq
                          corruptAppEq := hRel.corruptAppEq
                          corruptEq := hRel.corruptEq
                          activeAlign := fun _ => ?_ }⟩
                      subst hCoreEq
                      dsimp only [Qsag.Spec.CustodyLedger.authorize, i, fourLayerCustodyIntent]
                      refine ⟨Nat.le_refl _, ?_, hPolCap'.trans hCapEq, ?_⟩
                      · rw [hPolSpend']
                        exact Nat.add_le_add_right hSpentLe _
                      · intro u hu
                        rw [hPolNonces']
                        rcases List.mem_cons.mp hu with rfl | hOld
                        · exact List.mem_cons_self
                        · exact List.mem_cons_of_mem _ (hUsedSub u hOld)
        · rw [fl_if_neg hg] at hStepC; cases hStepC
  · intro _ _ _ turn _ _ _ hInt
    cases turn <;> cases hInt
  · intro c a turn hRel hNone
    dsimp only [fourLayerCustodyMachine] at hNone ⊢
    unfold fourLayerCustodyStep at hNone
    unfold fourLayerCustodyErrStep
    cases hPC : c.poisoned with
    | true =>
      simp only [↓reduceIte]; exact hRel
    | false =>
      rw [hPC] at hNone
      simp only [Bool.false_eq_true, ↓reduceIte] at hNone ⊢
      cases turn with
      | approve _ _ _ => exact hRel
      | advApprove _ _ _ => exact hRel
      | corrupt _ => exact hRel
      | execute dep req =>
        dsimp only at hNone ⊢
        let i := fourLayerCustodyIntent req
        by_cases hg : dep = dep₀ ∧ fourLayerPermitsReady q dep₀ c.honestPermits c.corruptPermits
            c.enrolledCorrupt req.quorum i = true
        · rw [fl_if_pos hg] at hNone ⊢
          cases hM4 : M4.step c.core req with
          | some _ => rw [hM4] at hNone; cases hNone
          | none =>
            exact
              { safe := hRel.safe
                notPoisonedA := hRel.notPoisonedA
                honestEq := hRel.honestEq
                corruptAppEq := hRel.corruptAppEq
                corruptEq := hRel.corruptEq
                activeAlign := fun hF => nomatch hF }
        · rw [fl_if_neg hg]
          exact hRel

/-- **End-to-End Unified 4-Layer ELF-to-`IdealCustody` Refinement (`elf_to_idealCustody_dataRefines`, `L-Ex-7`)**:
    Composes `elf_to_idealTsig_refines` (`ELF ⊑ MIR ⊑ Protocol ⊑ IdealTsig`) with
    `layer4IdealTsig_dataRefines_idealCustody` (`IdealTsig ⊑ Spec.idealCustodyMachine`) via
    `refines_trans_dataRefines`, unifying the 4-layer compiled ELF custody stack with the
    canonical `Spec.idealCustodyMachine` target (`0 Classical.choice`). -/
def elf_to_idealCustody_dataRefines {PK : Type} {n q f : Nat}
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
    (dep₀ : Nat) (s1₀ : Qsag.Layer1ElfState) (s4₀ : Qsag.Layer4IdealState PK)
    (hRel₀ : (Qsag.isa_to_mir_to_protocol_to_ideal_sim corrupt pkDigestOf pk dealtShares
      custodianShare signFromShare assembleThresholdSig idealSignOracle
      hBound hQPos hQLeN hCorruptNd hCorruptLe hSigMatch hOracleEq).Rel s1₀ s4₀) :
    let quorum₀ : Qsag.Spec.CustodyQuorumProfile :=
      ⟨n, q, s4₀.policy.velocity_window_cap, hQPos, hQLeN⟩
    let M1 := Qsag.Spec.Machine.ofPartyMachine (fun s => s = s1₀)
      (Qsag.layer1CompiledElfMachine q (pkDigestOf pk)
        (fun m msg => signFromShare (Qsag.readShareMem32 m) msg))
    Qsag.Spec.DataRefines
      (fourLayerCustodyMachine q dep₀ corrupt s1₀ M1)
      (Qsag.Spec.idealCustodyMachine Qsag.Spec.CustodyDigestScheme.transparent
        (fun d => idealSignOracle d.2.payload) dep₀ pk quorum₀)
      fourLayerCustodyVisIn fourLayerCustodyVisOut :=
  refines_trans_dataRefines
    (fourLayerCustody_lift_refines q dep₀ corrupt s1₀ s4₀
      (elf_to_idealTsig_refines corrupt pkDigestOf pk dealtShares custodianShare
        signFromShare assembleThresholdSig idealSignOracle
        hBound hQPos hQLeN hCorruptNd hCorruptLe hSigMatch hOracleEq s1₀ s4₀ hRel₀) rfl rfl)
    (layer4IdealTsig_dataRefines_idealCustody corrupt pkDigestOf pk idealSignOracle
      hQPos hQLeN dep₀ s4₀)

/-- Observable trace inclusion from the 4-layer compiled ELF custody machine into
    `Spec.idealCustodyMachine` (`elf_to_idealCustody_trace_inclusion`). -/
theorem elf_to_idealCustody_trace_inclusion {PK : Type} {n q f : Nat}
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
    (dep₀ : Nat) (s1₀ : Qsag.Layer1ElfState) (s4₀ : Qsag.Layer4IdealState PK)
    (hRel₀ : (Qsag.isa_to_mir_to_protocol_to_ideal_sim corrupt pkDigestOf pk dealtShares
      custodianShare signFromShare assembleThresholdSig idealSignOracle
      hBound hQPos hQLeN hCorruptNd hCorruptLe hSigMatch hOracleEq).Rel s1₀ s4₀)
    {tr : List (FourLayerCustodyTurn n × FourLayerCustodyOut)}
    (hAdmits : (fourLayerCustodyMachine q dep₀ corrupt s1₀
      (Qsag.Spec.Machine.ofPartyMachine (fun s => s = s1₀)
        (Qsag.layer1CompiledElfMachine q (pkDigestOf pk)
          (fun m msg => signFromShare (Qsag.readShareMem32 m) msg)))).AdmitsTrace tr) :
    (Qsag.Spec.idealCustodyMachine Qsag.Spec.CustodyDigestScheme.transparent
      (fun d => idealSignOracle d.2.payload) dep₀ pk
      ⟨n, q, s4₀.policy.velocity_window_cap, hQPos, hQLeN⟩).AdmitsTrace
      (Qsag.Spec.projectTrace fourLayerCustodyVisIn fourLayerCustodyVisOut tr) :=
  (elf_to_idealCustody_dataRefines corrupt pkDigestOf pk dealtShares custodianShare
    signFromShare assembleThresholdSig idealSignOracle
    hBound hQPos hQLeN hCorruptNd hCorruptLe hSigMatch hOracleEq dep₀ s1₀ s4₀ hRel₀).preserve_admitsTrace hAdmits

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
          ⟨d.keys c.party,
            Qsag.Custody.queries d.signer d.deploymentId c.party (hist.parties c.party).vault,
            Qsag.Custody.payload d.deploymentId c.party r, c.signature⟩ = true ∧
        (Qsag.ProdSmTcrBreak d.signer.suite d.signer.params (d.keys c.party)
           (Qsag.Custody.signingLog d.signer (d.keys c.party) d.deploymentId c.party
             (hist.parties c.party).vault) ∨
         Qsag.ProdPreimageBreak d.signer.suite d.signer.params (d.keys c.party)
           (Qsag.Custody.signingLog d.signer (d.keys c.party) d.deploymentId c.party
             (hist.parties c.party).vault)
           (Qsag.Custody.payload d.deploymentId c.party r) c.signature)))) ∧
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

/-! ## 4. Interactive and Durable Threshold Services: Shared Evaluation Equals Ideal -/

private theorem interactiveMachine_ext {I O S : Type} :
    ∀ (m n : Qsag.InteractiveService.Machine I O S), m.step = n.step → m = n
  | ⟨_⟩, ⟨_⟩, rfl => rfl

/-- The shared interactive threshold service is the ideal service: their step functions agree
    on every state and input. An equality of machines over one state type. -/
theorem thresholdServiceShared_eq_ideal (c : Qsag.ThresholdIdealService.Config) :
    Qsag.ThresholdIdealService.shared c = Qsag.ThresholdIdealService.ideal c :=
  interactiveMachine_ext _ _
    (funext fun s => funext fun i => Qsag.ThresholdIdealService.shared_step_eq_ideal c s i)

/-- The shared durable threshold service is the ideal durable service. -/
theorem thresholdDurableShared_eq_ideal (c : Qsag.ThresholdIdealService.Config) :
    Qsag.ThresholdIdealDurableService.shared c = Qsag.ThresholdIdealDurableService.ideal c :=
  interactiveMachine_ext _ _
    (funext fun s => funext fun i => Qsag.ThresholdIdealDurableService.shared_step_eq_ideal c s i)

/-- **Durable crash safety, threshold authorization and resource-burn soundness
    (`threshold_durable_feedback_and_resource_burn_chain`)**: collects
    `ThresholdIdealDurableService.crash_preserves_durable`,
    `ThresholdIdealService.authorized_of_verified_threshold`,
    `Custody.RequestPolicy.every_observed_wire_has_burn` and
    `Custody.RequestPolicy.returned_production_sound`. It says nothing about the relation of the
    shared services to the ideal ones: those are equal as machines
    (`thresholdServiceShared_eq_ideal`, `thresholdDurableShared_eq_ideal`), and no refinement
    witness is packaged for an equality. -/
theorem threshold_durable_feedback_and_resource_burn_chain
    (c : Qsag.ThresholdIdealService.Config)
    (compute : Qsag.ThresholdIdealDurableService.Compute)
    (sDur : Qsag.ThresholdIdealDurableService.State)
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
    (Qsag.ThresholdIdealDurableService.stepWith c compute sDur .crash).1.nextLeaf = sDur.nextLeaf ∧
    Qsag.ThresholdIdealService.authorized c sSvc reqAuth = true ∧
    (∃ r ∈ (Qsag.Custody.RequestPolicy.resourceRun profile d corrupt
        (Qsag.Custody.RequestPolicy.resourceInitial d) cmds).durable.reserved,
      r.request = obsPair.1) ∧
    (∃ sig, Qsag.RssProduction.sharedSign profile retReq = some sig ∧
      Qsag.decodeProductionSigWire profile.params retBytes = .ok sig) := by
  obtain ⟨hNextLeaf, _, _, _⟩ := Qsag.ThresholdIdealDurableService.crash_preserves_durable c compute sDur
  have hAuth := Qsag.ThresholdIdealService.authorized_of_verified_threshold c sSvc reqAuth hThresh hInputs
  have hBurn := Qsag.Custody.RequestPolicy.every_observed_wire_has_burn profile d corrupt cmds obsPair hObs
  obtain ⟨sig, hSign, _, hDec, _⟩ :=
    Qsag.Custody.RequestPolicy.returned_production_sound profile d corrupt cmds retReq retBytes hRet
  exact ⟨hNextLeaf, hAuth, hBurn, ⟨sig, hSign, hDec⟩⟩

/-- The commit and rollback boundary of any platform satisfying the explicit fsync contract.
The record survives every subsequent event trace, and a retained external anchor remains a
lower bound on the recovered durable log. -/
theorem posix_wal_commit_and_anchor_rollback_fence
    {M : Qsag.Spec.FsyncStorageModel} (platform : Qsag.Spec.PosixFsyncContract M)
    (s : M.State) (rec : Qsag.Spec.Bytes) (post : List Qsag.Spec.FsyncOp)
    (hAnchor : M.anchor s ≤ (M.durable s).length) :
    rec ∈ M.durable (M.run s (Qsag.Spec.walCommitOps rec ++ post)) ∧
    M.anchor s ≤ (M.durable (M.run s (Qsag.Spec.walCommitOps rec ++ post))).length :=
  ⟨platform.committed_survives s rec post,
    platform.anchor_excludes_stale_snapshot s (Qsag.Spec.walCommitOps rec ++ post) hAnchor⟩

/-! ## 5. POSIX Crash-Consistent WAL + Monotone External Anchor + Whole-Device Rollback Fence -/

/-- **POSIX Crash-Consistent Atomic WAL Commit & Anti-Rollback Anchor Fence
    (`posix_wal_commit_and_anchor_rollback_fence`)**:
    Composes `SeparatedCustodyUcBridge.posixWalCommit_refines_walCommitBeforeRelease` with
    `CeremonyAtomicityAndAbort.whole_device_rollback_below_anchor_fails_closed`. -/
theorem posix_atomic_commit_and_two_slot_rollback_fence
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

/-- **Abstract `Spec.PosixFsyncContract` WAL Commit Survival & Monotone Anchor Fence
    (`posix_fsync_contract_wal_commit_and_anchor_fence`, `L-Ex-3`)**:
    For any storage environment `M` satisfying `Spec.PosixFsyncContract M`, any valid anchor state
    `M.anchor s ≤ (M.durable s).length`, any committed record `rec`, and any subsequent crash/I/O
    schedule `post`:
    1. `rec` remains durable after `walCommitOps rec ++ post`, and
    2. the pre-commit monotone anchor lower-bounds the recovered durable log length. -/
theorem posix_fsync_contract_wal_commit_and_anchor_fence
    {M : Qsag.Spec.FsyncStorageModel} (hContract : Qsag.Spec.PosixFsyncContract M)
    (s : M.State) (rec : Qsag.Spec.Bytes) (post : List Qsag.Spec.FsyncOp)
    (hAnchor : M.anchor s ≤ (M.durable s).length) :
    rec ∈ M.durable (M.run s (Qsag.Spec.walCommitOps rec ++ post)) ∧
    M.anchor s ≤ (M.durable (M.run s (Qsag.Spec.walCommitOps rec ++ post))).length :=
  ⟨hContract.committed_survives s rec post,
   hContract.anchor_excludes_stale_snapshot s (Qsag.Spec.walCommitOps rec ++ post) hAnchor⟩

/-- Concrete instantiation of `posix_fsync_contract_wal_commit_and_anchor_fence` on the 3-tier
    `PosixFsState` WAL host (`PosixWalHost.walModel_contract`). -/
theorem posixWalHost_wal_commit_and_anchor_fence
    (ly : Qsag.PosixWalHost.WalLayout)
    (s : (Qsag.PosixWalHost.walModel ly).State)
    (rec : Qsag.Spec.Bytes) (post : List Qsag.Spec.FsyncOp)
    (hAnchor : (Qsag.PosixWalHost.walModel ly).anchor s ≤
      ((Qsag.PosixWalHost.walModel ly).durable s).length) :
    rec ∈ (Qsag.PosixWalHost.walModel ly).durable
      ((Qsag.PosixWalHost.walModel ly).run s (Qsag.Spec.walCommitOps rec ++ post)) ∧
    (Qsag.PosixWalHost.walModel ly).anchor s ≤
      ((Qsag.PosixWalHost.walModel ly).durable
        ((Qsag.PosixWalHost.walModel ly).run s (Qsag.Spec.walCommitOps rec ++ post))).length :=
  posix_fsync_contract_wal_commit_and_anchor_fence (Qsag.PosixWalHost.walModel_contract ly)
    s rec post hAnchor

/-! ### 5b. Concrete Sequence-Numbered Session Channel & Custody Anti-Replay (`L-Ex-3`) -/

/-- Concrete sequence-numbered point-to-point session channel state partitioned by directed peer
    link `(sender, receiver)` and keyed by `(seq, payload)`. -/
structure SeqSessionChannelState where
  outbox : Nat → Nat → List (Nat × Qsag.Spec.Bytes)
  replayWindow : Nat → Nat → List (Nat × Qsag.Spec.Bytes)

/-- Initial empty session channel state across all `(sender, receiver)` peer pairs. -/
def SeqSessionChannelState.empty : SeqSessionChannelState where
  outbox _ _ := []
  replayWindow _ _ := []

/-- Directed link lookup of `(m.seq, m.payload)` on `(m.sender, m.receiver)`. -/
def seqLinkLookup (tbl : Nat → Nat → List (Nat × Qsag.Spec.Bytes))
    (m : Qsag.Spec.ChannelMsg) : Bool :=
  decide ((m.seq, m.payload) ∈ tbl m.sender m.receiver)

/-- Directed link insertion of `(m.seq, m.payload)` on `(m.sender, m.receiver)`. -/
def seqLinkInsert (tbl : Nat → Nat → List (Nat × Qsag.Spec.Bytes))
    (m : Qsag.Spec.ChannelMsg) : Nat → Nat → List (Nat × Qsag.Spec.Bytes) :=
  fun u v =>
    if u = m.sender ∧ v = m.receiver then
      (m.seq, m.payload) :: tbl u v
    else
      tbl u v

/-- Single-event transition of the sequence-numbered session channel. -/
def seqSessionStep (st : SeqSessionChannelState) (ev : Qsag.Spec.ChannelEvent) :
    Option (SeqSessionChannelState × Unit) :=
  match ev with
  | .send m =>
    some ({ st with outbox := seqLinkInsert st.outbox m }, ())
  | .deliver m =>
    if seqLinkLookup st.outbox m && !seqLinkLookup st.replayWindow m then
      some ({ st with replayWindow := seqLinkInsert st.replayWindow m }, ())
    else
      none

/-- Reactive `Spec.Machine` for the sequence-numbered session channel. -/
def seqSessionChannelMachine :
    Qsag.Spec.Machine SeqSessionChannelState Qsag.Spec.ChannelEvent Unit where
  Init st := st = SeqSessionChannelState.empty
  step := seqSessionStep
  errStep st _ := st

/-- Executable trace checker for the sequence-numbered session channel. -/
@[expose] def seqSessionRun : SeqSessionChannelState → List Qsag.Spec.ChannelEvent → Bool
  | _, [] => true
  | st, .send m :: rest =>
    seqSessionRun { st with outbox := seqLinkInsert st.outbox m } rest
  | st, .deliver m :: rest =>
    seqLinkLookup st.outbox m &&
    (!seqLinkLookup st.replayWindow m &&
      seqSessionRun { st with replayWindow := seqLinkInsert st.replayWindow m } rest)

private theorem seqLinkLookup_insert (tbl : Nat → Nat → List (Nat × Qsag.Spec.Bytes))
    (m' m : Qsag.Spec.ChannelMsg) :
    seqLinkLookup (seqLinkInsert tbl m') m = (decide (m = m') || seqLinkLookup tbl m) := by
  unfold seqLinkLookup seqLinkInsert
  by_cases hLink : m.sender = m'.sender ∧ m.receiver = m'.receiver
  · rw [fl_if_pos hLink]
    by_cases hEq : m = m'
    · subst hEq
      simp
    · have hPairNe : (m.seq, m.payload) ≠ (m'.seq, m'.payload) := by
        intro hp
        apply hEq
        cases m; cases m'
        dsimp only at hLink hp
        injection hp with hs hpay
        rw [hLink.1, hLink.2, hs, hpay]
      rw [decide_eq_false hEq, Bool.false_or]
      by_cases hMem : (m.seq, m.payload) ∈ tbl m.sender m.receiver
      · rw [decide_eq_true (List.mem_cons_of_mem _ hMem), decide_eq_true hMem]
      · have hNotCons : (m.seq, m.payload) ∉ (m'.seq, m'.payload) :: tbl m.sender m.receiver := by
          intro hc
          rcases List.mem_cons.mp hc with h1 | h2
          · exact hPairNe h1
          · exact hMem h2
        rw [decide_eq_false hNotCons, decide_eq_false hMem]
  · rw [fl_if_neg hLink]
    have hNe : m ≠ m' := fun h => hLink (by subst h; exact ⟨rfl, rfl⟩)
    rw [decide_eq_false hNe, Bool.false_or]

private theorem seqSessionRun_delivered_absent (m : Qsag.Spec.ChannelMsg) :
    ∀ (tr : List Qsag.Spec.ChannelEvent) (st : SeqSessionChannelState),
      seqSessionRun st tr = true →
      seqLinkLookup st.replayWindow m = true →
      .deliver m ∉ tr
  | [], _, _, _, h => nomatch h
  | .send m' :: rest, st, hRun, hConsumed, hMem => by
    rcases List.mem_cons.mp hMem with hEq | hTail
    · cases hEq
    · exact seqSessionRun_delivered_absent m rest
        { st with outbox := seqLinkInsert st.outbox m' } hRun hConsumed hTail
  | .deliver m' :: rest, st, hRun, hConsumed, hMem => by
    obtain ⟨_, h2⟩ := Bool.and_eq_true_iff.mp hRun
    obtain ⟨hFresh, hRest⟩ := Bool.and_eq_true_iff.mp h2
    rcases List.mem_cons.mp hMem with hEq | hTail
    · cases hEq
      rw [hConsumed] at hFresh
      cases hFresh
    · have hConsumed' : seqLinkLookup (seqLinkInsert st.replayWindow m') m = true := by
        rw [seqLinkLookup_insert, hConsumed, Bool.or_true]
      exact seqSessionRun_delivered_absent m rest
        { st with replayWindow := seqLinkInsert st.replayWindow m' } hRest hConsumed' hTail

private theorem seqSessionRun_no_replay (m : Qsag.Spec.ChannelMsg)
    (post : List Qsag.Spec.ChannelEvent) :
    ∀ (pre : List Qsag.Spec.ChannelEvent) (st : SeqSessionChannelState),
      seqSessionRun st (pre ++ .deliver m :: post) = true →
      .deliver m ∉ post
  | [], st, hRun => by
    obtain ⟨_, h2⟩ := Bool.and_eq_true_iff.mp hRun
    obtain ⟨_, hRest⟩ := Bool.and_eq_true_iff.mp h2
    have hSelf : seqLinkLookup (seqLinkInsert st.replayWindow m) m = true := by
      rw [seqLinkLookup_insert, decide_eq_true rfl, Bool.true_or]
    exact seqSessionRun_delivered_absent m post
      { st with replayWindow := seqLinkInsert st.replayWindow m } hRest hSelf
  | .send m' :: pre, st, hRun =>
    seqSessionRun_no_replay m post pre { st with outbox := seqLinkInsert st.outbox m' } hRun
  | .deliver m' :: pre, st, hRun => by
    obtain ⟨_, h2⟩ := Bool.and_eq_true_iff.mp hRun
    exact seqSessionRun_no_replay m post pre
      { st with replayWindow := seqLinkInsert st.replayWindow m' }
      (Bool.and_eq_true_iff.mp h2).2

private theorem seqSessionRun_authentic (m : Qsag.Spec.ChannelMsg)
    (post : List Qsag.Spec.ChannelEvent) :
    ∀ (pre : List Qsag.Spec.ChannelEvent) (st : SeqSessionChannelState),
      seqSessionRun st (pre ++ .deliver m :: post) = true →
      seqLinkLookup st.outbox m = true ∨ .send m ∈ pre
  | [], st, hRun => .inl (Bool.and_eq_true_iff.mp hRun).1
  | .send m' :: pre, st, hRun => by
    rcases seqSessionRun_authentic m post pre
        { st with outbox := seqLinkInsert st.outbox m' } hRun with hOut | hPre
    · rw [seqLinkLookup_insert] at hOut
      rcases Bool.or_eq_true_iff.mp hOut with hEq | hOld
      · exact .inr (of_decide_eq_true hEq ▸ List.mem_cons_self)
      · exact .inl hOld
    · exact .inr (List.mem_cons_of_mem _ hPre)
  | .deliver m' :: pre, st, hRun => by
    obtain ⟨_, h2⟩ := Bool.and_eq_true_iff.mp hRun
    rcases seqSessionRun_authentic m post pre
        { st with replayWindow := seqLinkInsert st.replayWindow m' }
        (Bool.and_eq_true_iff.mp h2).2 with hOut | hPre
    · exact .inl hOut
    · exact .inr (List.mem_cons_of_mem _ hPre)

/-- Predicate characterizing traces admitted by the sequence-numbered session channel
    (covering both concrete `seqSessionRun` traces and canonical `Spec.honestChannelRun` batches). -/
def admitsSeqSessionChannel (tr : List Qsag.Spec.ChannelEvent) : Prop :=
  seqSessionRun SeqSessionChannelState.empty tr = true ∨
  ∃ msgs : List Qsag.Spec.ChannelMsg, msgs.Nodup ∧ tr = Qsag.Spec.honestChannelRun msgs

/-- **Concrete Sequence-Numbered Session Channel Satisfies `Spec.AuthenticatedChannelContract`
    (`seqSessionChannel_contract`, `L-Ex-3`)**:
    First concrete per-link `(sender, receiver)` session-table model instantiating
    `Spec.AuthenticatedChannelContract`. -/
theorem seqSessionChannel_contract :
    Qsag.Spec.AuthenticatedChannelContract admitsSeqSessionChannel where
  honestRunsAdmitted msgs hNd := .inr ⟨msgs, hNd, rfl⟩
  peerAuthenticated tr hAdm pre post m hEq := by
    rcases hAdm with hRun | ⟨msgs, hNd, hTr⟩
    · rw [hEq] at hRun
      rcases seqSessionRun_authentic m post pre SeqSessionChannelState.empty hRun with hEmpty | hPre
      · cases hEmpty
      · exact hPre
    · exact Qsag.Spec.checkedChannel_contract.peerAuthenticated tr
        (hTr ▸ Qsag.Spec.checkedChannel_contract.honestRunsAdmitted msgs hNd) pre post m hEq
  replayProtected tr hAdm pre post m hEq := by
    rcases hAdm with hRun | ⟨msgs, hNd, hTr⟩
    · rw [hEq] at hRun
      exact seqSessionRun_no_replay m post pre SeqSessionChannelState.empty hRun
    · exact Qsag.Spec.checkedChannel_contract.replayProtected tr
        (hTr ▸ Qsag.Spec.checkedChannel_contract.honestRunsAdmitted msgs hNd) pre post m hEq

/-- Extract the ordered sequence of delivered `ChannelMsg` frames from a channel trace. -/
def deliveredChannelMsgs : List Qsag.Spec.ChannelEvent → List Qsag.Spec.ChannelMsg
  | [] => []
  | .send _ :: rest => deliveredChannelMsgs rest
  | .deliver m :: rest => m :: deliveredChannelMsgs rest

private theorem mem_deliveredChannelMsgs_split {m : Qsag.Spec.ChannelMsg} :
    ∀ (tr : List Qsag.Spec.ChannelEvent),
      m ∈ deliveredChannelMsgs tr →
      ∃ pre post : List Qsag.Spec.ChannelEvent, tr = pre ++ .deliver m :: post
  | [], h => False.elim (List.not_mem_nil h)
  | .send m' :: rest, h => by
    obtain ⟨pre, post, hEq⟩ := mem_deliveredChannelMsgs_split rest h
    exact ⟨.send m' :: pre, post, congrArg (List.cons (.send m')) hEq⟩
  | .deliver m' :: rest, h => by
    rcases List.mem_cons.mp h with rfl | hTail
    · exact ⟨[], rest, rfl⟩
    · obtain ⟨pre, post, hEq⟩ := mem_deliveredChannelMsgs_split rest hTail
      exact ⟨.deliver m' :: pre, post, congrArg (List.cons (.deliver m')) hEq⟩

private theorem mem_deliveredChannelMsgs_imp_mem {m : Qsag.Spec.ChannelMsg} :
    ∀ (tr : List Qsag.Spec.ChannelEvent),
      m ∈ deliveredChannelMsgs tr → .deliver m ∈ tr
  | [], h => False.elim (List.not_mem_nil h)
  | .send _ :: rest, h => List.mem_cons_of_mem _ (mem_deliveredChannelMsgs_imp_mem rest h)
  | .deliver m' :: rest, h => by
    rcases List.mem_cons.mp h with rfl | hTail
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_deliveredChannelMsgs_imp_mem rest hTail)

private theorem deliveredChannelMsgs_nodup_aux
    {admits : List Qsag.Spec.ChannelEvent → Prop}
    (hContract : Qsag.Spec.AuthenticatedChannelContract admits)
    {tr : List Qsag.Spec.ChannelEvent} (hAdm : admits tr) :
    ∀ (pre suff : List Qsag.Spec.ChannelEvent),
      tr = pre ++ suff → (deliveredChannelMsgs suff).Nodup
  | _, [], _ => List.nodup_nil
  | pre, .send m :: rest, hEq =>
    deliveredChannelMsgs_nodup_aux hContract hAdm (pre ++ [.send m]) rest
      (by rw [hEq, List.append_assoc]; rfl)
  | pre, .deliver m :: rest, hEq => by
    have hTail := deliveredChannelMsgs_nodup_aux hContract hAdm (pre ++ [.deliver m]) rest
      (by rw [hEq, List.append_assoc]; rfl)
    refine List.nodup_cons.mpr ⟨fun hIn => ?_, hTail⟩
    have hDelMem : .deliver m ∈ rest := mem_deliveredChannelMsgs_imp_mem rest hIn
    exact hContract.replayProtected tr hAdm pre rest m hEq hDelMem

/-- **Top-Level Consumer of `Spec.AuthenticatedChannelContract` (`authenticated_channel_prevents_custody_replay`, `L-Ex-3`)**:
    Over any network channel satisfying `Spec.AuthenticatedChannelContract`:
    1. Every admitted custody/MPC channel trace delivers each `(sender, receiver, seq, payload)`
       frame at most once (`(deliveredChannelMsgs tr).Nodup` — zero replay),
    2. Every delivered frame is preceded in the trace by an authentic `.send m` from `m.sender`, and
    3. Every duplicate-free batch of honest custody messages is realizable on the channel. -/
theorem authenticated_channel_prevents_custody_replay
    {admits : List Qsag.Spec.ChannelEvent → Prop}
    (hContract : Qsag.Spec.AuthenticatedChannelContract admits) :
    (∀ tr : List Qsag.Spec.ChannelEvent, admits tr →
      (deliveredChannelMsgs tr).Nodup ∧
      (∀ m ∈ deliveredChannelMsgs tr,
        ∃ pre post : List Qsag.Spec.ChannelEvent,
          tr = pre ++ .deliver m :: post ∧
          .send m ∈ pre ∧ .deliver m ∉ post)) ∧
    (∀ msgs : List Qsag.Spec.ChannelMsg, msgs.Nodup → admits (Qsag.Spec.honestChannelRun msgs)) := by
  refine ⟨fun tr hAdm => ⟨deliveredChannelMsgs_nodup_aux hContract hAdm [] tr rfl, ?_⟩,
    hContract.honestRunsAdmitted⟩
  intro m hm
  obtain ⟨pre, post, hEq⟩ := mem_deliveredChannelMsgs_split tr hm
  exact ⟨pre, post, hEq,
    hContract.peerAuthenticated tr hAdm pre post m hEq,
    hContract.replayProtected tr hAdm pre post m hEq⟩

/-- Concrete corollary instantiating `authenticated_channel_prevents_custody_replay` on
    `seqSessionChannel_contract`. -/
theorem seqSessionChannel_prevents_custody_replay
    {tr : List Qsag.Spec.ChannelEvent}
    (hRun : seqSessionRun SeqSessionChannelState.empty tr = true) :
    (deliveredChannelMsgs tr).Nodup ∧
    (∀ m ∈ deliveredChannelMsgs tr,
      ∃ pre post : List Qsag.Spec.ChannelEvent,
        tr = pre ++ .deliver m :: post ∧
        .send m ∈ pre ∧ .deliver m ∉ post) :=
  (authenticated_channel_prevents_custody_replay seqSessionChannel_contract).1 tr (.inl hRun)

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

/-- A successful signing by custodian `party` of `intent` for deployment `deploymentId`.
    `Custody.payload` frames the deployment first, so the certificate is a signature on that
    deployment's approval bytes and on no other deployment's. -/
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

@[expose] def sepIssuedBy (issued : List SepIssue) (p dep : Nat) (r : Qsag.Custody.Intent) : Bool :=
  issued.any (fun a => decide (a.party = p ∧ a.deploymentId = dep ∧ a.intent = r))

/-- The forgery event of one accepted submission to the coordinator of deployment `dep`: the
    certificates of uncorrupted parties that never signed the submitted intent for `dep`. A
    signing of the same intent for another deployment does not count: it is a signature on
    different bytes (`Custody.payload_ne_of_deployment_ne`). -/
@[expose] def sepForged (c : SepCustodyState) (dep : Nat) (r : Qsag.Custody.Intent)
    (cs : List Qsag.Custody.Certificate) : List Qsag.Custody.Certificate :=
  cs.filter (fun x => decide (x.party ∉ c.corruptParties) && !sepIssuedBy c.issued x.party dep r)

/-- Transition of the separated-custody world. An uncorrupted enrolled custodian signs, for the
    deployment named in the request, with the production signer `Custody.sign` under its own key
    (the same key may serve several deployments); a failed signing is no event. Corruption is
    budgeted below the threshold. A submission is the real `Custody.submitRecorded`. -/
@[expose] def sepCustodyStep (d : Qsag.Custody.Deployment) (c : SepCustodyState) :
    SepCustodyInput → Option (SepCustodyState × SepCustodyOutput)
  | .approve p dep r =>
    if p < d.numParties ∧ p ∉ c.corruptParties then
      match Qsag.Custody.sign d.signer (d.keys p) dep p r with
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
              forgeries := sepForged c d.deploymentId r cs ++ c.forgeries }, .accepted)
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
  for an intent that party never signed for this deployment. Its probability is not bounded here.
* `leavesIncrease`: accepted submissions use strictly increasing leaves. The coordinator
  `Custody.submit` checks session freshness only; it has no epoch watermark and no WAL.

There is no single-deployment condition: custodians may sign for any deployment, and the
approval bytes carry the deployment. -/
structure SeparatedCustodyRunAssumptions
    (tr : List (SepCustodyInput × SepCustodyOutput)) (c : SepCustodyState) : Prop where
  noForgery : c.forgeries = []
  leavesIncrease : sepLeavesFresh 0 tr

/-- Correspondence between a state of the separated-custody world for deployment `dep₀` and an
    ideal custody state. The ideal honest permits are the signings for `dep₀`; signings for other
    deployments have no ideal counterpart. -/
structure SepCustodyIdealRel {PK D Sig : Type} (dep₀ : Nat) (quorum₀ : CustodyQuorumProfile)
    (c : SepCustodyState) (st : IdealCustodyState PK D Sig) : Prop where
  poisoned : st.ledger.poisoned = false
  spent : st.ledger.spent = c.shared.coordinator.spent
  capacity : c.shared.coordinator.capacity = quorum₀.spendCap
  sessions : st.ledger.usedSessions = c.shared.coordinator.consumedSessions
  corrupt : st.corruptParties = c.corruptParties
  honest : st.honestApprovals =
    (c.issued.filter (fun a => decide (a.deploymentId = dep₀))).map
      (fun a => CustodyApproval.mk a.party a.deploymentId (sepIntent a.intent))
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

private theorem sepIssuedBy_spec {issued : List SepIssue} {p dep : Nat}
    {r : Qsag.Custody.Intent} (h : sepIssuedBy issued p dep r = true) :
    ∃ a ∈ issued, a.party = p ∧ a.deploymentId = dep ∧ a.intent = r := by
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
             forgeries := sepForged c d.deploymentId r cs ++ c.forgeries } := by
  cases inp with
  | approve p dep r =>
    unfold sepCustodyStep at h
    dsimp only at h ⊢
    by_cases hg : p < d.numParties ∧ p ∉ c.corruptParties
    · rw [cert_if_pos hg] at h
      cases hs : Qsag.Custody.sign d.signer (d.keys p) dep p r with
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
    {d : Qsag.Custody.Deployment} {pk₀ : PK} {quorum₀ : CustodyQuorumProfile}
    (hP : SepDeploymentProfile d quorum₀)
    {c c1 : SepCustodyState} {inp : SepCustodyInput} {out : SepCustodyOutput} {w : Nat}
    {st : IdealCustodyState PK D Sig}
    (hStep : sepCustodyStep d c inp = some (c1, out))
    (hNF : c1.forgeries = [])
    (hLeaf : sepLeafOk w inp)
    (hSafe : st.SafeInv S oracleSign d.deploymentId pk₀ quorum₀)
    (hRel : SepCustodyIdealRel d.deploymentId quorum₀ c st) (hW : st.ledger.nextFreshEpoch ≤ w) :
    ∃ st1 itr, (idealCustodyMachine S oracleSign d.deploymentId pk₀ quorum₀).ValidTrace st itr st1 ∧
      SepCustodyIdealRel d.deploymentId quorum₀ c1 st1 ∧ st1.ledger.nextFreshEpoch ≤ sepNextLeaf w inp := by
  have h1 := sepCustodyStep_inv hStep
  have hD := hSafe.deployment
  cases inp with
  | approve p dep r =>
    dsimp only at h1
    obtain ⟨hg, hc⟩ := h1
    subst hc
    by_cases hDep : dep = d.deploymentId
    · have hg' : p < st.ledger.quorum.numParties ∧ p ∉ st.corruptParties ∧
          dep = st.ledger.deploymentId := by
        rw [hSafe.profile, hRel.corrupt, ← hP.parties, hD]
        exact ⟨hg.1, hg.2, hDep⟩
      have hI : (idealCustodyMachine S oracleSign d.deploymentId pk₀ quorum₀).step st
          (.approve p dep (sepIntent r)) =
          some ({ st with
                  honestApprovals := CustodyApproval.mk p dep (sepIntent r) :: st.honestApprovals },
                .approvalRecorded) := by
        change idealCustodyStep S oracleSign st (.approve p dep (sepIntent r)) = _
        unfold idealCustodyStep
        dsimp only
        exact cert_if_pos hg' _ _
      refine ⟨_, _, .accept hI (.nil _), ?_, hW⟩
      have hf : (SepIssue.mk p dep r :: c.issued).filter
            (fun a => decide (a.deploymentId = d.deploymentId)) =
          SepIssue.mk p dep r ::
            c.issued.filter (fun a => decide (a.deploymentId = d.deploymentId)) :=
        List.filter_cons_of_pos (decide_eq_true hDep)
      exact
        { poisoned := hRel.poisoned
          spent := hRel.spent
          capacity := hRel.capacity
          sessions := hRel.sessions
          corrupt := hRel.corrupt
          honest := by
            show CustodyApproval.mk p dep (sepIntent r) :: st.honestApprovals = _
            rw [hf, List.map_cons, hRel.honest]
          authorized := hRel.authorized }
    · -- A signing for another deployment is no event of this deployment's ideal functionality.
      refine ⟨st, [], .nil _, ?_, hW⟩
      have hf : (SepIssue.mk p dep r :: c.issued).filter
            (fun a => decide (a.deploymentId = d.deploymentId)) =
          c.issued.filter (fun a => decide (a.deploymentId = d.deploymentId)) :=
        List.filter_cons_of_neg (fun hd => hDep (of_decide_eq_true hd))
      exact
        { poisoned := hRel.poisoned
          spent := hRel.spent
          capacity := hRel.capacity
          sessions := hRel.sessions
          corrupt := hRel.corrupt
          honest := by
            show st.honestApprovals = _
            rw [hf]
            exact hRel.honest
          authorized := hRel.authorized }
  | corrupt p =>
    dsimp only at h1
    obtain ⟨hg, hc⟩ := h1
    subst hc
    have hg' : p < st.ledger.quorum.numParties ∧ p ∉ st.corruptParties ∧
        st.corruptParties.length + 1 < st.ledger.quorum.threshold := by
      rw [hSafe.profile, hRel.corrupt, ← hP.parties, ← hP.threshold]
      exact hg
    have hI : (idealCustodyMachine S oracleSign d.deploymentId pk₀ quorum₀).step st (.corrupt p) =
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
      (Qsag.Custody.acceptQuorum_spec _ _ _ _ _ _ _ _).mp hAcc
    have hNo : sepForged c d.deploymentId r cs = [] := (sep_append_nil hNF).1
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
        have hIss : sepIssuedBy c.issued x.party d.deploymentId r = true := by
          cases hI : sepIssuedBy c.issued x.party d.deploymentId r with
          | true => rfl
          | false =>
            have hf : (decide (x.party ∉ c.corruptParties) &&
                !sepIssuedBy c.issued x.party d.deploymentId r) = false := sep_filter_nil hNo x hx
            rw [hI, decide_eq_true hpc'] at hf
            exact absurd hf (by decide)
        obtain ⟨a, ha, hap, had, hai⟩ := sepIssuedBy_spec hIss
        have hm : CustodyApproval.mk a.party a.deploymentId (sepIntent a.intent) ∈
            (c.issued.filter (fun a => decide (a.deploymentId = d.deploymentId))).map (fun a =>
              CustodyApproval.mk a.party a.deploymentId (sepIntent a.intent)) :=
          List.mem_map_of_mem (List.mem_filter.mpr ⟨ha, decide_eq_true had⟩)
        rw [hap, hai, had, hxp] at hm
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
      (dep := d.deploymentId) (i := sepIntent r) hRel.poisoned hD.symm
      (sep_findReleased_none hSafe.walFresh (Nat.le_trans hW hLeaf'))
      (Nat.le_trans hW hLeaf')
      (by rw [hRel.sessions]; exact hSess)
      hQ
      (by rw [hRel.spent, hSafe.profile, ← hRel.capacity]; exact hCap)
    have hI : (idealCustodyMachine S oracleSign d.deploymentId pk₀ quorum₀).step st2
        (.sign d.deploymentId (sepIntent r) false) =
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
          st2.ledger.deploymentId (sepIntent r)).length d.deploymentId (sepIntent r) false) = _
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
    {d : Qsag.Custody.Deployment} {pk₀ : PK} {quorum₀ : CustodyQuorumProfile}
    (hP : SepDeploymentProfile d quorum₀)
    {c c' : SepCustodyState} {tr : List (SepCustodyInput × SepCustodyOutput)}
    (hTr : (sepCustodyMachine d).ValidTrace c tr c')
    (hNF : c'.forgeries = []) :
    ∀ (w : Nat) (st : IdealCustodyState PK D Sig), sepLeavesFresh w tr →
      st.SafeInv S oracleSign d.deploymentId pk₀ quorum₀ → SepCustodyIdealRel d.deploymentId quorum₀ c st →
      st.ledger.nextFreshEpoch ≤ w →
      ∃ st' itr, (idealCustodyMachine S oracleSign d.deploymentId pk₀ quorum₀).ValidTrace st itr st' ∧
        SepCustodyIdealRel d.deploymentId quorum₀ c' st' := by
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
      hLv'.1 hSafe hRel hW
    obtain ⟨st', itr, hT, hRel'⟩ := ih hNF _ st1 hLv'.2
      (idealCustody_validTrace_safeInv hSafe hT1) hRel1 hW1
    exact ⟨st', itr1 ++ itr, sep_validTrace_append hT1 hT, hRel'⟩
  | reject _ _ _ ih => exact ih hNF

/-- **The real separated-custody coordinator against the ideal custody functionality.** Take any
    run of the separated-custody world for deployment `d` from its initial state: custodians sign
    with the production signer `Custody.sign`, parties are corrupted adaptively below the
    threshold, and the coordinator is `Custody.submitRecorded` on arbitrary submitted certificate
    lists. If the run satisfies `SeparatedCustodyRunAssumptions`, its final state corresponds
    (`SepCustodyIdealRel`) to a reachable state of `Spec.idealCustodyMachine`: same spend, same
    consumed sessions, same corruption set, the custodians' signings as honest permits and the
    accepted intents as the authorized intents.

    Proved here: the quorum step. An accepted `submitRecorded` has `threshold` distinct enrolled
    signers (`Custody.acceptQuorum_spec`), each a corrupted party or, by `noForgery`, a custodian
    that signed this intent for this deployment and so holds a recorded permit, so the ideal
    `.sign` is accepted. A custodian's signing for another deployment is matched by no ideal step.

    Assumed (fields of `SeparatedCustodyRunAssumptions`, none provable from `Qsag.Custody.*`):
    `noForgery`, `leavesIncrease`. Not covered: the ideal machine's signature
    output and WAL replay (the coordinator outputs a verdict only, so `S` and `oracleSign` are
    arbitrary), and any bound on the probability of the forgery event. No run with an accepted
    submission is exhibited in the tree; that needs an evaluated production signature. -/
theorem separatedCustody_refines_idealCustody_of
    (d : Qsag.Custody.Deployment) (S : CustodyDigestScheme D) (oracleSign : D → Sig)
    (pk₀ : PK) (quorum₀ : CustodyQuorumProfile)
    (hProfile : SepDeploymentProfile d quorum₀)
    {c₀ c : SepCustodyState} {tr : List (SepCustodyInput × SepCustodyOutput)}
    (hInit : (sepCustodyMachine d).Init c₀)
    (hTr : (sepCustodyMachine d).ValidTrace c₀ tr c)
    (hRun : SeparatedCustodyRunAssumptions tr c) :
    ∃ st : IdealCustodyState PK D Sig,
      (idealCustodyMachine S oracleSign d.deploymentId pk₀ quorum₀).Reachable st ∧
      SepCustodyIdealRel d.deploymentId quorum₀ c st := by
  have h0 : c₀ = ⟨⟨⟨[], 0, d.capacity⟩, []⟩, [], [], []⟩ := hInit
  subst h0
  obtain ⟨st', itr, hT, hRel⟩ := sepCustody_validTrace_sim (S := S) (oracleSign := oracleSign)
    (pk₀ := pk₀) hProfile hTr hRun.noForgery 0
    (IdealCustodyState.init d.deploymentId pk₀ quorum₀) hRun.leavesIncrease
    (IdealCustodyState.init_safeInv (PK := PK) S oracleSign d.deploymentId pk₀ quorum₀)
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
    (d : Qsag.Custody.Deployment) (quorum₀ : CustodyQuorumProfile)
    (hProfile : SepDeploymentProfile d quorum₀)
    {c₀ c : SepCustodyState} {tr : List (SepCustodyInput × SepCustodyOutput)}
    (hInit : (sepCustodyMachine d).Init c₀)
    (hTr : (sepCustodyMachine d).ValidTrace c₀ tr c)
    (hRun : SeparatedCustodyRunAssumptions tr c) :
    ∀ a ∈ c.shared.accepted, ∃ b ∈ c.issued,
      b.party < d.numParties ∧ b.deploymentId = d.deploymentId ∧ b.intent = a.intent := by
  obtain ⟨st, hR, hRel⟩ := separatedCustody_refines_idealCustody_of d
    CustodyDigestScheme.transparent id () quorum₀ hProfile hInit hTr hRun
  obtain ⟨_, _, hAuth, _⟩ := idealCustody_reachable_spend_accounting hR
  intro a ha
  have hMem : sepIntent a.intent ∈ st.ledger.authorized := by
    rw [hRel.authorized]
    exact List.mem_map_of_mem (f := fun a : Qsag.Custody.AcceptedSubmission => sepIntent a.intent) ha
  obtain ⟨p, hp, hm⟩ := hAuth _ hMem
  rw [hRel.honest] at hm
  obtain ⟨b, hbf, hbe⟩ := List.mem_map.mp hm
  have hb : b ∈ c.issued := (List.mem_filter.mp hbf).1
  have h1 : b.party = p := congrArg CustodyApproval.party hbe
  have h2 : b.deploymentId = d.deploymentId := congrArg CustodyApproval.deploymentId hbe
  have h3 : sepIntent b.intent = sepIntent a.intent := congrArg CustodyApproval.intent hbe
  refine ⟨b, hb, ?_, h2, sepIntent_injective h3⟩
  rw [h1, hProfile.parties]
  exact hp

/-- **The forgery event is a signature on bytes its custodian never signed, in any deployment.**
    A certificate counted by `sepForged` in an accepted submission verifies under the uncorrupted
    custodian's own key on `Custody.payload d.deploymentId party r`, and every signing that
    custodian performed, for whatever deployment and intent, was on different bytes. -/
theorem sepForged_fresh_verifying_signature (d : Qsag.Custody.Deployment) (c : SepCustodyState)
    (r : Qsag.Custody.Intent) (cs : List Qsag.Custody.Certificate)
    (hAcc : (Qsag.Custody.submitRecorded d c.shared r cs).2 = true)
    (x : Qsag.Custody.Certificate) (hx : x ∈ sepForged c d.deploymentId r cs) :
    x.party ∉ c.corruptParties ∧
    Qsag.Custody.verify d.signer (Qsag.Custody.publicKeys d x.party) d.deploymentId x.party r
      x.signature = true ∧
    ∀ a ∈ c.issued, a.party = x.party →
      ¬ (Qsag.Custody.payload a.deploymentId a.party a.intent =
          Qsag.Custody.payload d.deploymentId x.party r) := by
  unfold sepForged at hx
  obtain ⟨hMem, hCond⟩ := List.mem_filter.mp hx
  obtain ⟨hHon, hNotIssued⟩ := Bool.and_eq_true_iff.mp hCond
  refine ⟨of_decide_eq_true hHon,
    (Qsag.Custody.submitRecorded_accepted_deployment d c.shared r cs hAcc x hMem).2, ?_⟩
  intro a ha _ hPay
  obtain ⟨hDep, hParty, hIntent⟩ := Qsag.Custody.payload_injective hPay
  have hIss : sepIssuedBy c.issued x.party d.deploymentId r = true := by
    unfold sepIssuedBy
    exact List.any_eq_true.mpr ⟨a, ha, decide_eq_true ⟨hParty, hDep, hIntent⟩⟩
  rw [hIss] at hNotIssued
  exact absurd hNotIssued (by decide)

/-! ### 8b. A guarded restriction of `sepCustodyMachine` and its `Spec.DataRefines` (`L-Ex-6b`)

`sepCustodyGuardedMachine d` is `sepCustodyMachine d` restricted by three guards on `.submit`, with
one bookkeeping turn added. It is not the real coordinator and it is not a signer:

* **No forged certificate.** A submission is refused when `sepForged` is nonempty, that is, when
  it carries a certificate of an uncorrupted party that never signed the intent for this
  deployment. The probability of that event is bounded separately, under hypotheses, in 8c.
* **Increasing leaves.** A submission is refused unless its leaf is at or above the watermark
  `nextLeaf`. `Custody.submitRecorded` has no such check (it checks session freshness only), so
  this guard removes real behaviours; `sepCustody_stale_leaf_rejected_by_ideal` is the reason the
  ideal functionality needs it.
* **Announced adversarial permits.** A certificate of a corrupted party counts only if the
  adversary announced it with `.advInject`. This costs the adversary nothing: `.advInject` is
  free for corrupted parties.

The machine outputs the coordinator's decision, `.accepted intent`. `Custody.submitRecorded`
returns a Boolean and produces no signature, so neither does this machine. The signature that
`Spec.idealCustodyMachine` releases appears only in the interface map `sepGuardedVisOut`, which
sends `.accepted r` to the ideal oracle's signature on `digest deploymentId (sepIntent r)`.

`separatedCustody_dataRefines_idealCustody` is a one-directional simulation of this restricted
machine. `sepCustodyGuarded_projects_to_sepCustody` shows every guarded execution is an execution
of `sepCustodyMachine` satisfying `SeparatedCustodyRunAssumptions`; the converse holds only for
real runs that meet those assumptions. -/

/-- State of the guarded machine: the separated-custody world, the adversarial permits announced
    so far, and the leaf watermark. -/
structure SepGuardedState where
  base : SepCustodyState
  advPermits : List CustodyApproval
  nextLeaf : Nat

/-- Alphabet of the guarded separated-custody machine (`advInject` records corrupt-party permits
    so every visible step maps 1-to-1 into `Spec.CustodyInput`). -/
inductive SepGuardedInput where
  | approve (party deploymentId : Nat) (intent : Qsag.Custody.Intent)
  | advInject (party deploymentId : Nat) (intent : Qsag.Custody.Intent)
  | corrupt (party : Nat)
  | submit (intent : Qsag.Custody.Intent) (certs : List Qsag.Custody.Certificate)

/-- Output events of the guarded separated-custody machine. `.accepted` is the coordinator's
    decision on a submission; no signature is produced. -/
inductive SepGuardedOutput where
  | certificate (c : Qsag.Custody.Certificate)
  | injected
  | corrupted (revealed : List CustodyIntent)
  | accepted (intent : Qsag.Custody.Intent)

/-- Initial state of `sepCustodyMachine d`. -/
def sepCustodyInit (d : Qsag.Custody.Deployment) : SepCustodyState :=
  ⟨⟨⟨[], 0, d.capacity⟩, []⟩, [], [], []⟩

/-- Initial state of `sepCustodyGuardedMachine`. -/
def sepGuardedInit (d : Qsag.Custody.Deployment) : SepGuardedState :=
  ⟨sepCustodyInit d, [], 0⟩

/-- Honest intents previously signed by `p` for `d.deploymentId`, matching `custodyRevealed`. -/
def sepRevealedFor (d : Qsag.Custody.Deployment) (issued : List SepIssue) (p : Nat) :
    List CustodyIntent :=
  custodyRevealed
    ((issued.filter (fun a => decide (a.deploymentId = d.deploymentId))).map
      (fun a => CustodyApproval.mk a.party a.deploymentId (sepIntent a.intent)))
    p

/-- Transition of the guarded machine: `Custody.sign` and `Custody.submitRecorded` as in
    `sepCustodyStep`, with `.submit` refused unless the leaf is at or above the watermark, no
    certificate is forged, and every corrupted party's certificate was announced. -/
@[expose] def sepCustodyGuardedStep
    (d : Qsag.Custody.Deployment) (c : SepGuardedState) :
    SepGuardedInput → Option (SepGuardedState × SepGuardedOutput)
  | .approve p dep r =>
    if p < d.numParties ∧ p ∉ c.base.corruptParties then
      match Qsag.Custody.sign d.signer (d.keys p) dep p r with
      | some sig =>
        some ({ c with base := { c.base with issued := ⟨p, dep, r⟩ :: c.base.issued } },
              .certificate ⟨p, r, sig⟩)
      | none => none
    else none
  | .advInject p dep r =>
    if p ∈ c.base.corruptParties then
      if dep = d.deploymentId then
        some ({ c with advPermits := ⟨p, dep, sepIntent r⟩ :: c.advPermits }, .injected)
      else
        some (c, .injected)
    else none
  | .corrupt p =>
    if p < d.numParties ∧ p ∉ c.base.corruptParties ∧
        c.base.corruptParties.length + 1 < d.threshold then
      some ({ c with base := { c.base with corruptParties := p :: c.base.corruptParties } },
            .corrupted (sepRevealedFor d c.base.issued p))
    else none
  | .submit r cs =>
    if c.nextLeaf ≤ r.leaf ∧
        sepForged c.base d.deploymentId r cs = [] ∧
        cs.all (fun x => !decide (x.party ∈ c.base.corruptParties) ||
          decide (CustodyApproval.mk x.party d.deploymentId (sepIntent r) ∈ c.advPermits)) = true ∧
        (Qsag.Custody.submitRecorded d c.base.shared r cs).2 = true then
      some ({ c with
              base := { c.base with shared := (Qsag.Custody.submitRecorded d c.base.shared r cs).1 }
              nextLeaf := r.leaf + 1 },
            .accepted r)
    else none

/-- The guarded restriction of `sepCustodyMachine d`. -/
def sepCustodyGuardedMachine (d : Qsag.Custody.Deployment) :
    Qsag.Spec.Machine SepGuardedState SepGuardedInput SepGuardedOutput where
  Init c := c = sepGuardedInit d
  step := sepCustodyGuardedStep d
  errStep c _ := c

@[expose] def sepGuardedVisIn (d : Qsag.Custody.Deployment) :
    SepGuardedInput → Option CustodyInput
  | .approve p dep r =>
    if dep = d.deploymentId then some (.approve p dep (sepIntent r)) else none
  | .advInject p dep r =>
    if dep = d.deploymentId then some (.advApprove p dep (sepIntent r)) else none
  | .corrupt p => some (.corrupt p)
  | .submit r _ => some (.sign d.deploymentId (sepIntent r) false)

/-- Interface map on outputs. The coordinator's acceptance of `r` is read as the ideal
    functionality's release of `oracleSign (digest deploymentId (sepIntent r))`; the signature is
    supplied here, by the ideal oracle, and not by the machine. -/
@[expose] def sepGuardedVisOut {D Sig : Type}
    (d : Qsag.Custody.Deployment) (S : CustodyDigestScheme D) (oracleSign : D → Sig) :
    SepGuardedOutput → CustodyOutcome Sig
  | .certificate _ => .approvalRecorded
  | .injected => .approvalRecorded
  | .corrupted rev => .corrupted rev
  | .accepted r => .released (oracleSign (S.digest d.deploymentId (sepIntent r)))

/-- Simulation invariant for `separatedCustody_dataRefines_idealCustody`. -/
structure SepGuardedIdealRel {PK D Sig : Type}
    (d : Qsag.Custody.Deployment) (S : CustodyDigestScheme D) (oracleSign : D → Sig)
    (pk₀ : PK) (quorum₀ : CustodyQuorumProfile)
    (c : SepGuardedState) (st : IdealCustodyState PK D Sig) : Prop where
  safe : st.SafeInv S oracleSign d.deploymentId pk₀ quorum₀
  baseRel : SepCustodyIdealRel d.deploymentId quorum₀ c.base st
  advEq : st.corruptApprovals = c.advPermits
  watermark : st.ledger.nextFreshEpoch ≤ c.nextLeaf
  noForgeries : c.base.forgeries = []

/-- **The guarded restriction of separated custody is simulated by `Spec.idealCustodyMachine`
    (`separatedCustody_dataRefines_idealCustody`, `L-Ex-6b`)**: a stuttering forward simulation
    `Spec.DataRefines` of `sepCustodyGuardedMachine d`, with the coordinator's acceptance mapped to
    the ideal release by `sepGuardedVisOut`. The statement is about the guarded machine only; see
    the head of this subsection for the three guards. -/
def separatedCustody_dataRefines_idealCustody {PK D Sig : Type} [DecidableEq D]
    (d : Qsag.Custody.Deployment) (S : CustodyDigestScheme D) (oracleSign : D → Sig)
    (pk₀ : PK) (quorum₀ : CustodyQuorumProfile)
    (hProfile : SepDeploymentProfile d quorum₀) :
    Qsag.Spec.DataRefines
      (sepCustodyGuardedMachine d)
      (idealCustodyMachine S oracleSign d.deploymentId pk₀ quorum₀)
      (sepGuardedVisIn d) (sepGuardedVisOut d S oracleSign) where
  Rel := SepGuardedIdealRel d S oracleSign pk₀ quorum₀
  absInit _ := IdealCustodyState.init d.deploymentId pk₀ quorum₀
  init_ok {c₀} hInit := by
    subst hInit
    exact ⟨rfl,
      { safe := IdealCustodyState.init_safeInv S oracleSign d.deploymentId pk₀ quorum₀
        baseRel :=
          { poisoned := rfl
            spent := rfl
            capacity := hProfile.capacity
            sessions := rfl
            corrupt := rfl
            honest := rfl
            authorized := rfl }
        advEq := rfl
        watermark := Nat.le_refl _
        noForgeries := rfl }⟩
  sim_visible {c c' st inp out j} hRel hStepC hVis := by
    have hD := hRel.safe.deployment
    cases inp with
    | approve p dep r =>
      dsimp only [sepCustodyGuardedMachine, sepCustodyGuardedStep] at hStepC
      dsimp only [sepGuardedVisIn] at hVis
      by_cases hDep : dep = d.deploymentId
      · rw [cert_if_pos hDep] at hVis
        cases hVis
        by_cases hg : p < d.numParties ∧ p ∉ c.base.corruptParties
        · rw [cert_if_pos hg] at hStepC
          cases hSign : Qsag.Custody.sign d.signer (d.keys p) dep p r with
          | none => rw [hSign] at hStepC; cases hStepC
          | some sig =>
            rw [hSign] at hStepC
            cases hStepC
            have hgA : p < st.ledger.quorum.numParties ∧ p ∉ st.corruptParties ∧
                dep = st.ledger.deploymentId := by
              rw [hRel.safe.profile, hRel.baseRel.corrupt, ← hProfile.parties, hD]
              exact ⟨hg.1, hg.2, hDep⟩
            have hStepA := idealCustodyStep_approve_of (S := S) (oracleSign := oracleSign)
              (st := st) (sepIntent r) hgA
            have hf : (SepIssue.mk p dep r :: c.base.issued).filter
                  (fun a => decide (a.deploymentId = d.deploymentId)) =
                SepIssue.mk p dep r ::
                  c.base.issued.filter (fun a => decide (a.deploymentId = d.deploymentId)) :=
              List.filter_cons_of_pos (decide_eq_true hDep)
            exact ⟨_, hStepA,
              { safe := idealCustodyStep_preserves_safeInv hRel.safe hStepA
                baseRel :=
                  { poisoned := hRel.baseRel.poisoned
                    spent := hRel.baseRel.spent
                    capacity := hRel.baseRel.capacity
                    sessions := hRel.baseRel.sessions
                    corrupt := hRel.baseRel.corrupt
                    honest := by
                      show CustodyApproval.mk p dep (sepIntent r) :: st.honestApprovals = _
                      rw [hf, List.map_cons, hRel.baseRel.honest]
                    authorized := hRel.baseRel.authorized }
                advEq := hRel.advEq
                watermark := hRel.watermark
                noForgeries := hRel.noForgeries }⟩
        · rw [cert_if_neg hg] at hStepC; cases hStepC
      · rw [cert_if_neg hDep] at hVis; cases hVis
    | advInject p dep r =>
      dsimp only [sepCustodyGuardedMachine, sepCustodyGuardedStep] at hStepC
      dsimp only [sepGuardedVisIn] at hVis
      by_cases hDep : dep = d.deploymentId
      · rw [cert_if_pos hDep] at hVis
        cases hVis
        by_cases hp : p ∈ c.base.corruptParties
        · rw [cert_if_pos hp, cert_if_pos hDep] at hStepC
          cases hStepC
          have hgA : p ∈ st.corruptParties ∧ dep = st.ledger.deploymentId := by
            rw [hRel.baseRel.corrupt, hD]
            exact ⟨hp, hDep⟩
          have hStepA := idealCustodyStep_advApprove_of (S := S) (oracleSign := oracleSign)
            (st := st) (sepIntent r) hgA
          exact ⟨_, hStepA,
            { safe := idealCustodyStep_preserves_safeInv hRel.safe hStepA
              baseRel :=
                { poisoned := hRel.baseRel.poisoned
                  spent := hRel.baseRel.spent
                  capacity := hRel.baseRel.capacity
                  sessions := hRel.baseRel.sessions
                  corrupt := hRel.baseRel.corrupt
                  honest := hRel.baseRel.honest
                  authorized := hRel.baseRel.authorized }
              advEq := congrArg (List.cons _) hRel.advEq
              watermark := hRel.watermark
              noForgeries := hRel.noForgeries }⟩
        · rw [cert_if_neg hp] at hStepC; cases hStepC
      · rw [cert_if_neg hDep] at hVis; cases hVis
    | corrupt p =>
      dsimp only [sepCustodyGuardedMachine, sepCustodyGuardedStep] at hStepC
      cases hVis
      by_cases hg : p < d.numParties ∧ p ∉ c.base.corruptParties ∧
          c.base.corruptParties.length + 1 < d.threshold
      · rw [cert_if_pos hg] at hStepC
        cases hStepC
        have hgA : p < st.ledger.quorum.numParties ∧ p ∉ st.corruptParties ∧
            st.corruptParties.length + 1 < st.ledger.quorum.threshold := by
          rw [hRel.safe.profile, hRel.baseRel.corrupt, ← hProfile.parties, ← hProfile.threshold]
          exact hg
        have hStepA := idealCustodyStep_corrupt_of (S := S) (oracleSign := oracleSign)
          (st := st) (p := p) hgA
        refine ⟨{ st with corruptParties := p :: st.corruptParties }, ?_, ?_⟩
        · change idealCustodyStep S oracleSign st (.corrupt p) =
            some ({ st with corruptParties := p :: st.corruptParties },
                  .corrupted (sepRevealedFor d c.base.issued p))
          rw [hStepA]
          unfold sepRevealedFor
          rw [← hRel.baseRel.honest]
        · exact
            { safe := idealCustodyStep_preserves_safeInv hRel.safe hStepA
              baseRel :=
                { poisoned := hRel.baseRel.poisoned
                  spent := hRel.baseRel.spent
                  capacity := hRel.baseRel.capacity
                  sessions := hRel.baseRel.sessions
                  corrupt := congrArg (List.cons _) hRel.baseRel.corrupt
                  honest := hRel.baseRel.honest
                  authorized := hRel.baseRel.authorized }
              advEq := hRel.advEq
              watermark := hRel.watermark
              noForgeries := hRel.noForgeries }
      · rw [cert_if_neg hg] at hStepC; cases hStepC
    | submit r cs =>
      dsimp only [sepCustodyGuardedMachine, sepCustodyGuardedStep] at hStepC
      cases hVis
      by_cases hg : c.nextLeaf ≤ r.leaf ∧
          sepForged c.base d.deploymentId r cs = [] ∧
          cs.all (fun x => !decide (x.party ∈ c.base.corruptParties) ||
            decide (CustodyApproval.mk x.party d.deploymentId (sepIntent r) ∈ c.advPermits)) = true ∧
          (Qsag.Custody.submitRecorded d c.base.shared r cs).2 = true
      · rw [cert_if_pos hg] at hStepC
        cases hStepC
        rcases hg with ⟨hLeaf, hNoForg, hAdvCov, hSubOk⟩
        obtain ⟨hAcc, hCap, hEq⟩ := Qsag.Custody.submitRecorded_accepted d c.base.shared r cs hSubOk
        obtain ⟨hSess, _, hTle, hNd, hRange, _⟩ :=
          (Qsag.Custody.acceptQuorum_spec _ _ _ _ _ _ _ _).mp hAcc
        have hNoForg' : (cs.filter (fun x => decide (x.party ∉ c.base.corruptParties) &&
            !sepIssuedBy c.base.issued x.party d.deploymentId r)) = [] := hNoForg
        have hSub : ∀ p ∈ cs.map Qsag.Custody.Certificate.party,
            p < st.ledger.quorum.numParties ∧
            (CustodyApproval.mk p st.ledger.deploymentId (sepIntent r) ∈ st.honestApprovals ∨
             CustodyApproval.mk p st.ledger.deploymentId (sepIntent r) ∈ st.corruptApprovals) := by
          intro p hp
          obtain ⟨x, hx, hxp⟩ := List.mem_map.mp hp
          rw [hRel.safe.profile, hD, ← hProfile.parties]
          refine ⟨by rw [← hxp]; exact hRange x hx, ?_⟩
          by_cases hpc : x.party ∈ c.base.corruptParties
          · have hAllX := List.all_eq_true.mp hAdvCov x hx
            rw [decide_eq_true hpc] at hAllX
            simp only [Bool.not_true, Bool.false_or] at hAllX
            rw [← hxp, hRel.advEq]
            exact .inr (of_decide_eq_true hAllX)
          · refine .inl ?_
            have hIss : sepIssuedBy c.base.issued x.party d.deploymentId r = true := by
              cases hI : sepIssuedBy c.base.issued x.party d.deploymentId r with
              | true => rfl
              | false =>
                have hf := sep_filter_nil hNoForg' x hx
                rw [hI, decide_eq_true hpc] at hf
                exact absurd hf (by decide)
            obtain ⟨a, ha, hap, had, hai⟩ := sepIssuedBy_spec hIss
            have hm : CustodyApproval.mk a.party a.deploymentId (sepIntent a.intent) ∈
                (c.base.issued.filter (fun a => decide (a.deploymentId = d.deploymentId))).map
                  (fun a => CustodyApproval.mk a.party a.deploymentId (sepIntent a.intent)) :=
              List.mem_map_of_mem (List.mem_filter.mpr ⟨ha, decide_eq_true had⟩)
            rw [hap, hai, had, hxp] at hm
            rw [hRel.baseRel.honest]
            exact hm
        have hQ : st.ledger.quorum.threshold ≤
            (custodyApprovers st.ledger.quorum.numParties st.honestApprovals st.corruptApprovals
              st.ledger.deploymentId (sepIntent r)).length := by
          have hLen := custodyApprovers_length_le_of_subset hNd hSub
          rw [List.length_map] at hLen
          have ht : st.ledger.quorum.threshold = d.threshold := by
            rw [hRel.safe.profile]; exact hProfile.threshold.symm
          rw [ht]
          exact Nat.le_trans hTle hLen
        have hLS := sep_ledgerSign_fresh (S := S) (oracleSign := oracleSign) (L := st.ledger)
          (dep := d.deploymentId) (i := sepIntent r) hRel.baseRel.poisoned hD.symm
          (sep_findReleased_none hRel.safe.walFresh (Nat.le_trans hRel.watermark hLeaf))
          (Nat.le_trans hRel.watermark hLeaf)
          (by rw [hRel.baseRel.sessions]; exact hSess)
          hQ
          (by rw [hRel.baseRel.spent, hRel.safe.profile, ← hRel.baseRel.capacity]; exact hCap)
        have hStepA := idealCustodyStep_sign_of (S := S) (oracleSign := oracleSign) (st := st) hLS
        have hDigEq : oracleSign (S.digest st.ledger.deploymentId (sepIntent r)) =
            oracleSign (S.digest d.deploymentId (sepIntent r)) := by
          rw [hD]
        rw [hDigEq] at hStepA
        refine ⟨_, hStepA, ?_⟩
        · exact
            { safe := idealCustodyStep_preserves_safeInv hRel.safe hStepA
              baseRel :=
                { poisoned := hRel.baseRel.poisoned
                  spent := (congrArg (fun x => x + r.spend) hRel.baseRel.spent).trans
                    (congrArg (fun s : Qsag.Custody.SharedHistory => s.coordinator.spent) hEq).symm
                  capacity := (congrArg (fun s : Qsag.Custody.SharedHistory => s.coordinator.capacity)
                    hEq).trans hRel.baseRel.capacity
                  sessions := (congrArg (fun l => r.session :: l) hRel.baseRel.sessions).trans
                    (congrArg (fun s : Qsag.Custody.SharedHistory => s.coordinator.consumedSessions)
                      hEq).symm
                  corrupt := hRel.baseRel.corrupt
                  honest := hRel.baseRel.honest
                  authorized := (congrArg (fun l => sepIntent r :: l) hRel.baseRel.authorized).trans
                    (congrArg (fun s : Qsag.Custody.SharedHistory =>
                      s.accepted.map (fun a : Qsag.Custody.AcceptedSubmission => sepIntent a.intent))
                      hEq).symm }
              advEq := hRel.advEq
              watermark := Nat.le_refl _
              noForgeries := hRel.noForgeries }
      · rw [cert_if_neg hg] at hStepC; cases hStepC
  sim_internal {c c' st inp out} hRel hStepC hInt := by
    cases inp with
    | approve p dep r =>
      dsimp only [sepCustodyGuardedMachine, sepCustodyGuardedStep] at hStepC
      dsimp only [sepGuardedVisIn] at hInt
      by_cases hDep : dep = d.deploymentId
      · rw [cert_if_pos hDep] at hInt; cases hInt
      · by_cases hg : p < d.numParties ∧ p ∉ c.base.corruptParties
        · rw [cert_if_pos hg] at hStepC
          cases hSign : Qsag.Custody.sign d.signer (d.keys p) dep p r with
          | none => rw [hSign] at hStepC; cases hStepC
          | some sig =>
            rw [hSign] at hStepC
            cases hStepC
            have hf : (SepIssue.mk p dep r :: c.base.issued).filter
                  (fun a => decide (a.deploymentId = d.deploymentId)) =
                c.base.issued.filter (fun a => decide (a.deploymentId = d.deploymentId)) :=
              List.filter_cons_of_neg (fun hd => hDep (of_decide_eq_true hd))
            exact
              { safe := hRel.safe
                baseRel :=
                  { poisoned := hRel.baseRel.poisoned
                    spent := hRel.baseRel.spent
                    capacity := hRel.baseRel.capacity
                    sessions := hRel.baseRel.sessions
                    corrupt := hRel.baseRel.corrupt
                    honest := by
                      show st.honestApprovals = _
                      rw [hf]; exact hRel.baseRel.honest
                    authorized := hRel.baseRel.authorized }
                advEq := hRel.advEq
                watermark := hRel.watermark
                noForgeries := hRel.noForgeries }
        · rw [cert_if_neg hg] at hStepC; cases hStepC
    | advInject p dep r =>
      dsimp only [sepCustodyGuardedMachine, sepCustodyGuardedStep] at hStepC
      dsimp only [sepGuardedVisIn] at hInt
      by_cases hDep : dep = d.deploymentId
      · rw [cert_if_pos hDep] at hInt; cases hInt
      · by_cases hp : p ∈ c.base.corruptParties
        · rw [cert_if_pos hp, cert_if_neg hDep] at hStepC
          cases hStepC
          exact hRel
        · rw [cert_if_neg hp] at hStepC; cases hStepC
    | corrupt _ => cases hInt
    | submit _ _ => cases hInt
  sim_reject hRel _ := hRel

/-- Project a `sepCustodyGuardedMachine` trace onto `sepCustodyMachine` (erasing `.advInject`). -/
def projectSepGuardedTrace :
    List (SepGuardedInput × SepGuardedOutput) → List (SepCustodyInput × SepCustodyOutput)
  | [] => []
  | (inp, out) :: rest =>
    match inp, out with
    | .approve p dep r, .certificate cert => (.approve p dep r, .certificate cert) :: projectSepGuardedTrace rest
    | .corrupt p, .corrupted _ => (.corrupt p, .corrupted) :: projectSepGuardedTrace rest
    | .submit r cs, .accepted _ => (.submit r cs, .accepted) :: projectSepGuardedTrace rest
    | _, _ => projectSepGuardedTrace rest

private theorem sepCustodyGuarded_validTrace_projects
    {d : Qsag.Custody.Deployment}
    {c c' : SepGuardedState} {tr : List (SepGuardedInput × SepGuardedOutput)}
    (hNF₀ : c.base.forgeries = [])
    (hTr : (sepCustodyGuardedMachine d).ValidTrace c tr c') :
    (sepCustodyMachine d).ValidTrace c.base (projectSepGuardedTrace tr) c'.base ∧
    c'.base.forgeries = [] ∧
    sepLeavesFresh c.nextLeaf (projectSepGuardedTrace tr) := by
  induction hTr with
  | nil _ => exact ⟨.nil _, hNF₀, trivial⟩
  | @accept s s₁ _ inp out rest hStep _ ih =>
    cases inp with
    | approve p dep r =>
      dsimp only [sepCustodyGuardedMachine, sepCustodyGuardedStep] at hStep
      by_cases hg : p < d.numParties ∧ p ∉ s.base.corruptParties
      · rw [cert_if_pos hg] at hStep
        cases hSign : Qsag.Custody.sign d.signer (d.keys p) dep p r with
        | none => rw [hSign] at hStep; cases hStep
        | some sig =>
          rw [hSign] at hStep
          cases hStep
          obtain ⟨hTrR, hNFR, hLvR⟩ := ih hNF₀
          have hBaseStep : (sepCustodyMachine d).step s.base (.approve p dep r) =
              some ({ s.base with issued := ⟨p, dep, r⟩ :: s.base.issued }, .certificate ⟨p, r, sig⟩) := by
            dsimp only [sepCustodyMachine, sepCustodyStep]
            rw [cert_if_pos hg, hSign]
          exact ⟨.accept hBaseStep hTrR, hNFR, trivial, hLvR⟩
      · rw [cert_if_neg hg] at hStep; cases hStep
    | advInject p dep r =>
      dsimp only [sepCustodyGuardedMachine, sepCustodyGuardedStep] at hStep
      by_cases hp : p ∈ s.base.corruptParties
      · rw [cert_if_pos hp] at hStep
        by_cases hDep : dep = d.deploymentId
        · rw [cert_if_pos hDep] at hStep; cases hStep; exact ih hNF₀
        · rw [cert_if_neg hDep] at hStep; cases hStep; exact ih hNF₀
      · rw [cert_if_neg hp] at hStep; cases hStep
    | corrupt p =>
      dsimp only [sepCustodyGuardedMachine, sepCustodyGuardedStep] at hStep
      by_cases hg : p < d.numParties ∧ p ∉ s.base.corruptParties ∧
          s.base.corruptParties.length + 1 < d.threshold
      · rw [cert_if_pos hg] at hStep
        cases hStep
        obtain ⟨hTrR, hNFR, hLvR⟩ := ih hNF₀
        have hBaseStep : (sepCustodyMachine d).step s.base (.corrupt p) =
            some ({ s.base with corruptParties := p :: s.base.corruptParties }, .corrupted) := by
          dsimp only [sepCustodyMachine, sepCustodyStep]
          rw [cert_if_pos hg]
        exact ⟨.accept hBaseStep hTrR, hNFR, trivial, hLvR⟩
      · rw [cert_if_neg hg] at hStep; cases hStep
    | submit r cs =>
      dsimp only [sepCustodyGuardedMachine, sepCustodyGuardedStep] at hStep
      by_cases hg : s.nextLeaf ≤ r.leaf ∧
          sepForged s.base d.deploymentId r cs = [] ∧
          cs.all (fun x => !decide (x.party ∈ s.base.corruptParties) ||
            decide (CustodyApproval.mk x.party d.deploymentId (sepIntent r) ∈ s.advPermits)) = true ∧
          (Qsag.Custody.submitRecorded d s.base.shared r cs).2 = true
      · rw [cert_if_pos hg] at hStep
        cases hStep
        obtain ⟨hTrR, hNFR, hLvR⟩ := ih hNF₀
        have hBaseStep : (sepCustodyMachine d).step s.base (.submit r cs) =
            some ({ s.base with shared := (Qsag.Custody.submitRecorded d s.base.shared r cs).1 },
                  .accepted) := by
          dsimp only [sepCustodyMachine, sepCustodyStep]
          rw [cert_if_pos hg.2.2.2, hg.2.1, List.nil_append, hNF₀]
        exact ⟨.accept hBaseStep hTrR, hNFR, hg.1, hLvR⟩
      · rw [cert_if_neg hg] at hStep; cases hStep
  | reject _ _ _ ih => exact ih hNF₀

/-- Every initialized execution of `sepCustodyGuardedMachine d` projects onto an execution of
    `sepCustodyMachine d` that satisfies `SeparatedCustodyRunAssumptions`, and its image under the
    interface maps is a trace of `Spec.idealCustodyMachine`. The converse direction (from an
    execution of `sepCustodyMachine d` to a guarded one) is not claimed. -/
theorem sepCustodyGuarded_projects_to_sepCustody {PK D Sig : Type} [DecidableEq D]
    (d : Qsag.Custody.Deployment) (S : CustodyDigestScheme D) (oracleSign : D → Sig)
    (pk₀ : PK) (quorum₀ : CustodyQuorumProfile)
    (hProfile : SepDeploymentProfile d quorum₀)
    {cFinal : SepGuardedState} {tr : List (SepGuardedInput × SepGuardedOutput)}
    (hTr : (sepCustodyGuardedMachine d).ValidTrace (sepGuardedInit d) tr cFinal) :
    (sepCustodyMachine d).ValidTrace (sepCustodyInit d) (projectSepGuardedTrace tr) cFinal.base ∧
    SeparatedCustodyRunAssumptions (projectSepGuardedTrace tr) cFinal.base ∧
    (idealCustodyMachine S oracleSign d.deploymentId pk₀ quorum₀).AdmitsTrace
      (Qsag.Spec.projectTrace (sepGuardedVisIn d) (sepGuardedVisOut d S oracleSign) tr) := by
  obtain ⟨hBaseTr, hNF, hLv⟩ := sepCustodyGuarded_validTrace_projects rfl hTr
  have hAdm : (sepCustodyGuardedMachine d).AdmitsTrace tr :=
    ⟨sepGuardedInit d, cFinal, rfl, hTr⟩
  exact ⟨hBaseTr, ⟨hNF, hLv⟩,
    (separatedCustody_dataRefines_idealCustody d S oracleSign pk₀ quorum₀ hProfile).preserve_admitsTrace hAdm⟩

/-! ### 8c. Composing `sepForged_fresh_verifying_signature` with Production `EUF-CMA` `GameBound` (`L-Ex-6b`) -/

/-- Total multi-step execution of `sepCustodyMachine d` over an adversarial input schedule. -/
@[expose] def sepCustodyRun (d : Qsag.Custody.Deployment) :
    SepCustodyState → List SepCustodyInput → SepCustodyState
  | c, [] => c
  | c, inp :: rest =>
    match sepCustodyStep d c inp with
    | some (c', _) => sepCustodyRun d c' rest
    | none => sepCustodyRun d c rest

/-- Oracle signing queries issued by custodian `p` in `issued`. -/
def sepIssuedQueries (cfg : Qsag.Custody.SigningConfig) (issued : List SepIssue) (p : Nat) :
    List Qsag.ProdSigningQuery :=
  (issued.filter (fun a => decide (a.party = p))).map
    (fun a => Qsag.Custody.query cfg a.deploymentId a.party a.intent)

/-- Candidate signing issues appearing in an input schedule. -/
def sepScheduleIssues : List SepCustodyInput → List SepIssue
  | [] => []
  | .approve p dep r :: rest => ⟨p, dep, r⟩ :: sepScheduleIssues rest
  | _ :: rest => sepScheduleIssues rest

/-- Stateful Jorts one-time leaf discipline on a separated-custody input schedule: no custodian
    is asked to sign two distinct `(deploymentId, intent)` pairs on the same hypertree leaf. -/
def sepScheduleOneTime (sched : List SepCustodyInput) : Prop :=
  ∀ a ∈ sepScheduleIssues sched, ∀ b ∈ sepScheduleIssues sched,
    a.party = b.party → a.intent.leaf = b.intent.leaf → a = b

/-- Constructive extractor scanning a `sepCustodyRun` schedule for the first accepted submission
    that triggers a non-empty `sepForged`, returning the forged custodian index and exact
    `ProdEufCmaOutcome` against that custodian's issued signing log at that step. -/
def extractSepForgeryOutcome (d : Qsag.Custody.Deployment) :
    SepCustodyState → List SepCustodyInput → Option (Nat × Qsag.ProdEufCmaOutcome)
  | _, [] => none
  | c, inp :: rest =>
    match inp with
    | .submit r cs =>
      if (Qsag.Custody.submitRecorded d c.shared r cs).2 = true then
        match sepForged c d.deploymentId r cs with
        | x :: _ =>
          some (x.party,
            { sk := d.keys x.party
              queries := sepIssuedQueries d.signer c.issued x.party
              msgStar := Qsag.Custody.payload d.deploymentId x.party r
              sigStar := x.signature })
        | [] =>
          let c' : SepCustodyState :=
            { c with
              shared := (Qsag.Custody.submitRecorded d c.shared r cs).1
              forgeries := [] ++ c.forgeries }
          extractSepForgeryOutcome d c' rest
      else
        extractSepForgeryOutcome d c rest
    | other =>
      match sepCustodyStep d c other with
      | some (c', _) => extractSepForgeryOutcome d c' rest
      | none => extractSepForgeryOutcome d c rest

private theorem mem_productionSigningLog_msg {suite : Qsag.TweakableHashSuite}
    {params : Qsag.PqHashParams} {sk : Qsag.PqSecretKey} {msg : List UInt8} :
    ∀ (qs : List Qsag.ProdSigningQuery),
      msg ∈ (Qsag.productionSigningLog suite params sk qs).map Prod.fst →
      ∃ q ∈ qs, q.message = msg
  | [], h => False.elim (List.not_mem_nil h)
  | q :: qs, h => by
    dsimp only [Qsag.productionSigningLog] at h
    cases hs : Qsag.prodSignQuery suite params sk q with
    | none =>
      rw [hs] at h
      obtain ⟨q', hq', hm⟩ := mem_productionSigningLog_msg qs h
      exact ⟨q', List.mem_cons_of_mem _ hq', hm⟩
    | some sig =>
      rw [hs, List.map_cons] at h
      rcases List.mem_cons.mp h with hEq | hTail
      · exact ⟨q, List.mem_cons_self, hEq.symm⟩
      · obtain ⟨q', hq', hm⟩ := mem_productionSigningLog_msg qs hTail
        exact ⟨q', List.mem_cons_of_mem _ hq', hm⟩

private theorem extractSepForgeryOutcome_complete (d : Qsag.Custody.Deployment) :
    ∀ (sched : List SepCustodyInput) (c : SepCustodyState),
      c.forgeries = [] →
      (sepCustodyRun d c sched).forgeries ≠ [] →
      ∃ pOut, extractSepForgeryOutcome d c sched = some pOut
  | [], c, hNF, hNe => False.elim (hNe hNF)
  | .approve p dep r :: rest, c, hNF, hNe => by
    dsimp only [sepCustodyRun] at hNe
    dsimp only [extractSepForgeryOutcome]
    cases hS : sepCustodyStep d c (.approve p dep r) with
    | none =>
      rw [hS] at hNe
      exact extractSepForgeryOutcome_complete d rest c hNF hNe
    | some pair =>
      rcases pair with ⟨c', out⟩
      rw [hS] at hNe
      have hInv := sepCustodyStep_inv hS
      dsimp only at hInv
      have hNF' : c'.forgeries = [] := by rw [hInv.2]; exact hNF
      exact extractSepForgeryOutcome_complete d rest c' hNF' hNe
  | .corrupt p :: rest, c, hNF, hNe => by
    dsimp only [sepCustodyRun] at hNe
    dsimp only [extractSepForgeryOutcome]
    cases hS : sepCustodyStep d c (.corrupt p) with
    | none =>
      rw [hS] at hNe
      exact extractSepForgeryOutcome_complete d rest c hNF hNe
    | some pair =>
      rcases pair with ⟨c', out⟩
      rw [hS] at hNe
      have hInv := sepCustodyStep_inv hS
      dsimp only at hInv
      have hNF' : c'.forgeries = [] := by rw [hInv.2]; exact hNF
      exact extractSepForgeryOutcome_complete d rest c' hNF' hNe
  | .submit r cs :: rest, c, hNF, hNe => by
    dsimp only [sepCustodyRun, sepCustodyStep] at hNe
    dsimp only [extractSepForgeryOutcome]
    by_cases hAcc : (Qsag.Custody.submitRecorded d c.shared r cs).2 = true
    · rw [cert_if_pos hAcc] at hNe ⊢
      dsimp only at hNe
      cases hF : sepForged c d.deploymentId r cs with
      | cons x xs => exact ⟨_, rfl⟩
      | nil =>
        rw [hF] at hNe
        exact extractSepForgeryOutcome_complete d rest _ (by simp [hNF]) hNe
    · rw [cert_if_neg hAcc] at hNe ⊢
      exact extractSepForgeryOutcome_complete d rest c hNF hNe

private theorem extractSepForgeryOutcome_sound (d : Qsag.Custody.Deployment) :
    ∀ (sched : List SepCustodyInput) (c : SepCustodyState)
      (pool : List SepIssue)
      (_hSub : ∀ a ∈ c.issued, a ∈ pool)
      {pStar : Nat} {o : Qsag.ProdEufCmaOutcome},
      extractSepForgeryOutcome d c sched = some (pStar, o) →
      pStar < d.numParties ∧
      o.sk = d.keys pStar ∧
      Qsag.prodEufCmaWin d.signer.suite d.signer.params o = true ∧
      (∀ q ∈ o.queries, ∃ a ∈ pool ++ sepScheduleIssues sched,
        a.party = pStar ∧ q = Qsag.Custody.query d.signer a.deploymentId a.party a.intent)
  | [], _, _, _, _, _, h => by cases h
  | .approve p dep r :: rest, c, pool, hSub, pStar, o, h => by
    dsimp only [extractSepForgeryOutcome] at h
    have hPoolSub : ∀ x ∈ pool ++ sepScheduleIssues rest,
        x ∈ pool ++ sepScheduleIssues (.approve p dep r :: rest) := by
      intro x hx
      rcases List.mem_append.mp hx with hL | hR
      · exact List.mem_append_left _ hL
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hR)
    cases hS : sepCustodyStep d c (.approve p dep r) with
    | none =>
      rw [hS] at h
      obtain ⟨hLt, hSk, hWin, hQ⟩ := extractSepForgeryOutcome_sound d rest c pool hSub h
      exact ⟨hLt, hSk, hWin, fun q hq => by
        obtain ⟨a, ha, hpA, hqEq⟩ := hQ q hq
        exact ⟨a, hPoolSub a ha, hpA, hqEq⟩⟩
    | some pair =>
      rcases pair with ⟨c', out⟩
      rw [hS] at h
      have hInv := sepCustodyStep_inv hS
      dsimp only at hInv
      have hSub' : ∀ a ∈ c'.issued, a ∈ pool ++ [SepIssue.mk p dep r] := by
        rw [hInv.2]
        intro a ha
        rcases List.mem_cons.mp ha with rfl | hOld
        · exact List.mem_append_right _ List.mem_cons_self
        · exact List.mem_append_left _ (hSub a hOld)
      obtain ⟨hLt, hSk, hWin, hQ⟩ :=
        extractSepForgeryOutcome_sound d rest c' (pool ++ [SepIssue.mk p dep r]) hSub' h
      refine ⟨hLt, hSk, hWin, fun q hq => ?_⟩
      obtain ⟨a, ha, hpA, hqEq⟩ := hQ q hq
      have ha' : a ∈ pool ++ sepScheduleIssues (.approve p dep r :: rest) := by
        rw [List.append_assoc] at ha
        exact ha
      exact ⟨a, ha', hpA, hqEq⟩
  | .corrupt p :: rest, c, pool, hSub, pStar, o, h => by
    dsimp only [extractSepForgeryOutcome] at h
    cases hS : sepCustodyStep d c (.corrupt p) with
    | none =>
      rw [hS] at h
      exact extractSepForgeryOutcome_sound d rest c pool hSub h
    | some pair =>
      rcases pair with ⟨c', out⟩
      rw [hS] at h
      have hInv := sepCustodyStep_inv hS
      dsimp only at hInv
      have hSub' : ∀ a ∈ c'.issued, a ∈ pool := by rw [hInv.2]; exact hSub
      exact extractSepForgeryOutcome_sound d rest c' pool hSub' h
  | .submit r cs :: rest, c, pool, hSub, pStar, o, h => by
    dsimp only [extractSepForgeryOutcome] at h
    by_cases hAcc : (Qsag.Custody.submitRecorded d c.shared r cs).2 = true
    · rw [cert_if_pos hAcc] at h
      cases hF : sepForged c d.deploymentId r cs with
      | cons x xs =>
        rw [hF] at h
        injection h with hPair
        injection hPair with hpEq hoEq
        subst hpEq; subst hoEq
        have hxForg : x ∈ sepForged c d.deploymentId r cs := by
          rw [hF]; exact List.mem_cons_self
        have hxMemCs : x ∈ cs := (List.mem_filter.mp hxForg).1
        obtain ⟨hAccQ, _, _⟩ := Qsag.Custody.submitRecorded_accepted d c.shared r cs hAcc
        have hxLt : x.party < d.numParties :=
          ((Qsag.Custody.acceptQuorum_spec _ _ _ _ _ _ _ _).mp hAccQ).2.2.2.2.1 x hxMemCs
        obtain ⟨_, hVer, hFreshPay⟩ := sepForged_fresh_verifying_signature d c r cs hAcc x hxForg
        rw [Qsag.Custody.publicKeys_eq, Qsag.Custody.verify_eq] at hVer
        have hNotInLog : Qsag.Custody.payload d.deploymentId x.party r ∉
            (Qsag.productionSigningLog d.signer.suite d.signer.params (d.keys x.party)
              (sepIssuedQueries d.signer c.issued x.party)).map Prod.fst := by
          intro hMemL
          obtain ⟨q, hqM, hqMsg⟩ := mem_productionSigningLog_msg _ hMemL
          obtain ⟨a, haFilt, rfl⟩ := List.mem_map.mp hqM
          obtain ⟨haIss, haParty⟩ := List.mem_filter.mp haFilt
          rw [Qsag.Custody.query_eq] at hqMsg
          exact hFreshPay a haIss (of_decide_eq_true haParty) hqMsg
        have hWin : Qsag.prodEufCmaWin d.signer.suite d.signer.params
            { sk := d.keys x.party
              queries := sepIssuedQueries d.signer c.issued x.party
              msgStar := Qsag.Custody.payload d.deploymentId x.party r
              sigStar := x.signature } = true := by
          rw [Qsag.prodEufCmaWin_eq]
          exact Bool.and_eq_true_iff.mpr ⟨hVer, decide_eq_true hNotInLog⟩
        refine ⟨hxLt, rfl, hWin, ?_⟩
        intro q hq
        obtain ⟨a, haFilt, rfl⟩ := List.mem_map.mp hq
        obtain ⟨haIss, haParty⟩ := List.mem_filter.mp haFilt
        exact ⟨a, List.mem_append_left _ (hSub a haIss), of_decide_eq_true haParty, rfl⟩
      | nil =>
        rw [hF] at h
        refine extractSepForgeryOutcome_sound d rest _ pool ?_ h
        exact hSub
    · rw [cert_if_neg hAcc] at h
      exact extractSepForgeryOutcome_sound d rest c pool hSub h

/-- **Violating `noForgery` in `sepCustodyMachine` Constructively Wins Production `EUF-CMA` and
    Yields a Hash Break (`separatedCustody_forgery_wins_eufCma`, `L-Ex-6b`)**:
    Composes `sepForged_fresh_verifying_signature` with `prodEufCmaWin_eq` and
    `production_stateful_forgery_witness`: any run of `sepCustodyRun` ending with `forgeries ≠ []`
    constructively extracts `(pStar, o)` via `extractSepForgeryOutcome` such that
    `prodEufCmaWin = true` AND (under stateful Jorts one-time leaf discipline) extracts a concrete
    `ProdTcrWitness` or `ProdPreimageBreak`! -/
theorem separatedCustody_forgery_wins_eufCma
    (d : Qsag.Custody.Deployment)
    (sched : List SepCustodyInput)
    (hw : d.signer.params.w = 4 ∨ d.signer.params.w = 16)
    (hst : d.signer.params.statefulJorts = true)
    (hOneTimeSched : sepScheduleOneTime sched)
    (hForg : (sepCustodyRun d (sepCustodyInit d) sched).forgeries ≠ []) :
    ∃ (pStar : Nat) (o : Qsag.ProdEufCmaOutcome),
      extractSepForgeryOutcome d (sepCustodyInit d) sched = some (pStar, o) ∧
      pStar < d.numParties ∧
      o.sk = d.keys pStar ∧
      Qsag.prodEufCmaWin d.signer.suite d.signer.params o = true ∧
      (Nonempty (Qsag.ProdTcrWitness d.signer.suite d.signer.params o.sk
          (Qsag.productionSigningLog d.signer.suite d.signer.params o.sk o.queries)
          o.msgStar o.sigStar) ∨
        Qsag.ProdPreimageBreak d.signer.suite d.signer.params o.sk
          (Qsag.productionSigningLog d.signer.suite d.signer.params o.sk o.queries)
          o.msgStar o.sigStar) := by
  obtain ⟨⟨pStar, o⟩, hExt⟩ :=
    extractSepForgeryOutcome_complete d sched (sepCustodyInit d) rfl hForg
  obtain ⟨hLt, hSk, hWin, hQOrigin⟩ :=
    extractSepForgeryOutcome_sound d sched (sepCustodyInit d) []
      (fun _ hm => False.elim (List.not_mem_nil hm)) hExt
  have hOneTimeQ : ∀ q, q ∈ o.queries → ∀ q', q' ∈ o.queries → q.epoch = q'.epoch → q = q' := by
    intro q hq q' hq' hEp
    obtain ⟨a, ha, haP, rfl⟩ := hQOrigin q hq
    obtain ⟨b, hb, hbP, rfl⟩ := hQOrigin q' hq'
    rw [List.nil_append] at ha hb
    have hLeafEq : a.intent.leaf = b.intent.leaf := by
      rw [Qsag.Custody.query_eq, Qsag.Custody.query_eq] at hEp
      exact hEp
    rw [hOneTimeSched a ha b hb (haP.trans hbP.symm) hLeafEq]
  have hWinSplit := Bool.and_eq_true_iff.mp (Qsag.prodEufCmaWin_eq _ _ o ▸ hWin)
  have hFreshLog : ∀ e ∈ Qsag.productionSigningLog d.signer.suite d.signer.params o.sk o.queries,
      e.1 ≠ o.msgStar := by
    intro e he hEq
    exact of_decide_eq_true hWinSplit.2 (List.mem_map.mpr ⟨e, he, hEq⟩)
  have hBreak := Qsag.production_stateful_forgery_witness d.signer.suite d.signer.params
    o.sk o.queries o.msgStar o.sigStar hw hst hOneTimeQ hFreshLog hWinSplit.1
  exact ⟨pStar, o, hExt, hLt, hSk, hWin, hBreak⟩

/-- Fallback outcome (`queries := []`) used on forgery-free coins in `sepForgeryForgerOutcome`. -/
def sepFallbackOutcome (d : Qsag.Custody.Deployment) : Qsag.ProdEufCmaOutcome where
  sk := d.keys 0
  queries := []
  msgStar := []
  sigStar := ⟨[], 0, 0, [], []⟩

/-- Coin-indexed `ProdEufCmaOutcome` induced by a `sepCustodyMachine` schedule family `sched`. -/
def sepForgeryForgerOutcome {n : Nat} (d : Qsag.Custody.Deployment)
    (sched : Fin n → List SepCustodyInput) (ω : Fin n) : Qsag.ProdEufCmaOutcome :=
  match extractSepForgeryOutcome d (sepCustodyInit d) (sched ω) with
  | some (_, o) => o
  | none => sepFallbackOutcome d

theorem sepForgeryForgerOutcome_oneTime {n : Nat} (d : Qsag.Custody.Deployment)
    (sched : Fin n → List SepCustodyInput)
    (hOneTimeSched : ∀ ω : Fin n, sepScheduleOneTime (sched ω))
    (ω : Fin n) (_hst : d.signer.params.statefulJorts = true) :
    ∀ q, q ∈ (sepForgeryForgerOutcome d sched ω).queries →
      ∀ q', q' ∈ (sepForgeryForgerOutcome d sched ω).queries → q.epoch = q'.epoch → q = q' := by
  unfold sepForgeryForgerOutcome
  cases hExt : extractSepForgeryOutcome d (sepCustodyInit d) (sched ω) with
  | none => intro _ hq; exact False.elim (List.not_mem_nil hq)
  | some pair =>
    rcases pair with ⟨pStar, o⟩
    obtain ⟨_, _, _, hQOrigin⟩ :=
      extractSepForgeryOutcome_sound d (sched ω) (sepCustodyInit d) []
        (fun _ hm => False.elim (List.not_mem_nil hm)) hExt
    intro q hq q' hq' hEp
    obtain ⟨a, ha, haP, rfl⟩ := hQOrigin q hq
    obtain ⟨b, hb, hbP, rfl⟩ := hQOrigin q' hq'
    rw [List.nil_append] at ha hb
    have hLeafEq : a.intent.leaf = b.intent.leaf := by
      rw [Qsag.Custody.query_eq, Qsag.Custody.query_eq] at hEp
      exact hEp
    rw [hOneTimeSched ω a ha b hb (haP.trans hbP.symm) hLeafEq]

/-- **Composed `Spec.GameBound` Bounding Separated-Custody Forgery Probability via Production
    `EUF-CMA` (`separatedCustody_forgery_eufCma_gameBound`, `L-Ex-6b`)**:
    Composes `sepForged_fresh_verifying_signature` and `extractSepForgeryOutcome` directly with
    `Top.production_euf_cma_gameBound` (`Spec.event_le_reduction_win` + `Spec.GameBound.trans`),
    bounding `Pr[(sepCustodyRun d (sepCustodyInit d) (sched ω)).forgeries ≠ []] ≤ εItsr + εTcr + εPre`! -/
theorem separatedCustody_forgery_eufCma_gameBound {n : Nat}
    (hPos : 0 < n)
    (d : Qsag.Custody.Deployment)
    (hw : d.signer.params.w = 4 ∨ d.signer.params.w = 16)
    (sched : Fin n → List SepCustodyInput)
    (hOneTimeSched : ∀ ω : Fin n, sepScheduleOneTime (sched ω))
    (εItsr εTcr εPre : Qsag.Spec.RatBound)
    (hItsr : Qsag.Spec.GameBound
      (Qsag.Spec.FinGame.mk hPos (fun ω =>
        Qsag.prodItsrEvent d.signer.suite d.signer.params hw
          (sepForgeryForgerOutcome d sched ω)
          (sepForgeryForgerOutcome_oneTime d sched hOneTimeSched ω))).winProb
      εItsr)
    (hTcr : Qsag.Spec.GameBound
      (Qsag.Spec.FinGame.mk hPos (fun ω =>
        Qsag.prodTcrEvent d.signer.suite d.signer.params hw
          (sepForgeryForgerOutcome d sched ω)
          (sepForgeryForgerOutcome_oneTime d sched hOneTimeSched ω))).winProb
      εTcr)
    (hPre : Qsag.Spec.GameBound
      (Qsag.Spec.FinGame.mk hPos (fun ω =>
        Qsag.prodPreEvent d.signer.suite d.signer.params hw
          (sepForgeryForgerOutcome d sched ω)
          (sepForgeryForgerOutcome_oneTime d sched hOneTimeSched ω))).winProb
      εPre) :
    let sepForgeryGame : Qsag.Spec.FinGame n :=
      Qsag.Spec.FinGame.mk hPos (fun ω =>
        decide ((sepCustodyRun d (sepCustodyInit d) (sched ω)).forgeries ≠ []))
    Qsag.Spec.GameBound sepForgeryGame.winProb ((εItsr.add εTcr).add εPre) := by
  intro sepForgeryGame
  let forgerGame : Qsag.Spec.FinGame n :=
    Qsag.Spec.FinGame.mk hPos (fun ω =>
      Qsag.prodEufCmaWin d.signer.suite d.signer.params (sepForgeryForgerOutcome d sched ω))
  have hForgerBound := (production_euf_cma_gameBound hPos d.signer.suite d.signer.params hw
    (sepForgeryForgerOutcome d sched)
    (sepForgeryForgerOutcome_oneTime d sched hOneTimeSched)
    εItsr εTcr εPre hItsr hTcr hPre).1
  have hRed := Qsag.Spec.event_le_reduction_win sepForgeryGame forgerGame (fun ω hForgWin => by
    have hForgNe : (sepCustodyRun d (sepCustodyInit d) (sched ω)).forgeries ≠ [] :=
      of_decide_eq_true hForgWin
    obtain ⟨⟨pStar, o⟩, hExt⟩ :=
      extractSepForgeryOutcome_complete d (sched ω) (sepCustodyInit d) rfl hForgNe
    obtain ⟨_, _, hWin, _⟩ :=
      extractSepForgeryOutcome_sound d (sched ω) (sepCustodyInit d) []
        (fun _ hm => False.elim (List.not_mem_nil hm)) hExt
    show Qsag.prodEufCmaWin d.signer.suite d.signer.params (sepForgeryForgerOutcome d sched ω) = true
    unfold sepForgeryForgerOutcome
    rw [hExt]
    exact hWin)
  exact Qsag.Spec.GameBound.trans hRed hForgerBound

end SeparatedCustodyIdeal

/-! ## 9. Distributed `(t, n)` Custody, the Authenticated Custodian Network, and the Shamir + `BeltLatch` Validator Network -/

/-- **Distributed threshold custody refines the ideal custody functionality** for its own
    `deploymentId`. The concrete machine is `DistCustody.distMachine`: Shamir custodians with
    durable latches and volatile coupons, an adversarially scheduled network buffer, adaptive
    corruption below the threshold, and a coordinator that runs `Spec.custodyLedgerSign` with the
    Lagrange reconstruction of the buffered verified shares. `approve`, `inject` (for this
    deployment), `corrupt` and `execute` implement the four ideal ports. -/
def distributedCustody_refines_idealCustody {F C PK D Sig : Type}
    [Qsag.LawfulField F] [DecidableEq F] [DecidableEq C] [DecidableEq D]
    (dep : Qsag.DistCustody.Deployment F C PK D Sig) (hWf : dep.WellFormed) :
    Qsag.Spec.DataRefines (Qsag.DistCustody.distMachine dep)
      (Qsag.Spec.idealCustodyMachine dep.digests dep.idealOracle dep.deploymentId dep.pk
        dep.quorum)
      (Qsag.DistCustody.visIn dep) Qsag.DistCustody.visOut :=
  Qsag.DistCustody.distCustody_refines_ideal dep hWf

/-- **Trace inclusion, reachable-state safety, completeness and share secrecy of distributed
    custody.**
    1. Every execution, under any interleaving of approvals, corruptions, injected messages, drops
       and crashes, projects to an execution of `Spec.idealCustodyMachine`.
    2. In every reachable state fewer than `threshold` custodians are corrupted, the spend is
       within the cap, and each WAL record carries the dealt key's signature on
       `digest deploymentId intent` and lies in the durable log of an enrolled custodian whose
       latch has advanced past it; no custodian has latched two intents at one epoch.
    3. Any duplicate-free list of at least `threshold` enrolled custodians reconstructs the dealt
       key from the dealt shares.
    4. The shares of fewer than `threshold` enrolled custodians are unchanged under a bijection
       of the dealer polynomials that shifts the key by any `w`. -/
theorem distributedCustody_trace_inclusion_and_safety {F C PK D Sig : Type}
    [Qsag.LawfulField F] [DecidableEq F] [DecidableEq C] [DecidableEq D]
    (dep : Qsag.DistCustody.Deployment F C PK D Sig) (hWf : dep.WellFormed) :
    (∀ tr : List (Qsag.DistCustody.Turn F × Qsag.DistCustody.Event F Sig),
      (Qsag.DistCustody.distMachine dep).AdmitsTrace tr →
      (Qsag.Spec.idealCustodyMachine dep.digests dep.idealOracle dep.deploymentId dep.pk
        dep.quorum).AdmitsTrace
        (Qsag.Spec.projectTrace (Qsag.DistCustody.visIn dep) Qsag.DistCustody.visOut tr)) ∧
    (∀ st : Qsag.DistCustody.State F PK D Sig, (Qsag.DistCustody.distMachine dep).Reachable st →
      st.corrupt.length < dep.quorum.threshold ∧
      st.ledger.spent ≤ dep.quorum.spendCap ∧
      (∀ r : Qsag.Spec.CustodyRelease D Sig, r ∈ st.ledger.releasedHistory →
        r.sig = dep.signWith dep.secret (dep.digests.digest dep.deploymentId r.intent) ∧
        ∃ p : Nat, p < dep.quorum.numParties ∧ r.intent ∈ (st.nodes p).latched ∧
          r.intent.epoch < (st.nodes p).latch) ∧
      (∀ p : Nat, ((st.nodes p).latched.map Qsag.Spec.CustodyIntent.epoch).Nodup)) ∧
    (∀ approvers : List Nat, approvers.Nodup →
      (∀ p, p ∈ approvers → p < dep.quorum.numParties) →
      dep.quorum.threshold ≤ approvers.length →
      Qsag.DistCustody.reconstruct (approvers.map dep.point) (approvers.map dep.trueShare) =
        dep.secret) ∧
    (∀ (corrupt : List Nat) (w : F), (∀ p, p ∈ corrupt → p < dep.quorum.numParties) →
      corrupt.length < dep.quorum.threshold →
      ∃ e : Qsag.SimpleEquiv (Qsag.ShamirPadPoly F dep.quorum.threshold)
          (Qsag.ShamirPadPoly F dep.quorum.threshold),
        ∀ P : Qsag.ShamirPadPoly F dep.quorum.threshold,
          Qsag.RoundPoly.evalCoeffs (e.toFun P).1 Qsag.CommRingOps.zero =
            Qsag.CommRingOps.add w (Qsag.RoundPoly.evalCoeffs P.1 Qsag.CommRingOps.zero) ∧
          ∀ p : Nat, p ∈ corrupt →
            Qsag.RoundPoly.evalCoeffs (e.toFun P).1 (dep.point p) =
              Qsag.RoundPoly.evalCoeffs P.1 (dep.point p)) := by
  refine ⟨fun _ h => Qsag.DistCustody.distCustody_trace_inclusion dep hWf h, ?_,
    fun approvers hNd hEnr hThr =>
      Qsag.DistCustody.reconstruct_dealt_shares dep hWf approvers hNd hEnr hThr,
    fun corrupt w hEnr hFew =>
      Qsag.DistCustody.corrupt_shares_independent_of_secret dep hWf corrupt hEnr hFew w⟩
  intro st hReach
  obtain ⟨hCor, hSpent, hWal⟩ := Qsag.DistCustody.distCustody_reachable_safe dep hWf hReach
  exact ⟨hCor, hSpent, hWal,
    fun p => Qsag.DistCustody.distCustody_latch_unique dep hWf hReach p⟩

/-- **Share-Opening Distributed Custody Refines `Spec.idealCustodyMachine` under Finite-Set `InjOn`
    (`distributedShareCustody_injOn_dataRefines_ideal`, `L-Ex-6a`)**:
    Upgrades distributed custody to a real `Spec.SigScheme` (`sigScheme.verify = true`), per-request
    share-opening contributions with zero secret-key reconstruction, and 256-bit compressing
    commitments (`BitVec 256`) under decidable finite-set `InjOnPreimages` instead of impossible
    global hash injectivity. -/
def distributedShareCustody_injOn_dataRefines_ideal
    {Share Contrib Preimage PK SK D Sig : Type}
    [DecidableEq Contrib] [DecidableEq Preimage] [DecidableEq D]
    (dep : Qsag.DistCustody.ShareOpeningDeployment Share Contrib Preimage PK SK D Sig)
    (hWf : dep.WellFormed) (obs : List Preimage)
    (hInj : Qsag.DistCustody.InjOnPreimages dep.commit obs) :
    Qsag.Spec.DataRefines
      (Qsag.DistCustody.shareOpeningObservedMachine dep obs)
      (Qsag.Spec.idealCustodyMachine dep.digests dep.idealOracle dep.deploymentId dep.pk dep.quorum)
      (Qsag.DistCustody.shareVisIn dep) Qsag.DistCustody.shareVisOut :=
  Qsag.DistCustody.distCustody_injOn_dataRefines_ideal dep hWf obs hInj

/-- **Unconditional Collision-Branching Refinement of Share-Opening Distributed Custody
    (`distributedShareCustody_dataRefines_or_collision`, `L-Ex-6a`)**:
    For ANY compressing 256-bit commitment hash `commit : Preimage → BitVec 256` with ZERO
    injectivity assumption, every multi-turn execution of `shareOpeningMachine dep` either:
    1. projects onto an execution of `Spec.idealCustodyMachine` where every WAL-released signature
       satisfies `dep.sigScheme.verify = true`, OR
    2. constructively exhibits two distinct colliding preimages `x₁ ≠ x₂` in the observed transcript
       with `dep.commit x₁ = dep.commit x₂`. -/
theorem distributedShareCustody_dataRefines_or_collision
    {Share Contrib Preimage PK SK D Sig : Type}
    [DecidableEq Contrib] [DecidableEq Preimage] [DecidableEq D]
    (dep : Qsag.DistCustody.ShareOpeningDeployment Share Contrib Preimage PK SK D Sig)
    (hWf : dep.WellFormed)
    {stFinal : Qsag.DistCustody.ShareState Share Contrib PK D Sig}
    {tr : List (Qsag.DistCustody.ShareTurn Contrib × Qsag.DistCustody.ShareEvent Share Sig)}
    (hTr : (Qsag.DistCustody.shareOpeningMachine dep).ValidTrace
      (Qsag.DistCustody.ShareState.init dep) tr stFinal) :
    ((Qsag.Spec.idealCustodyMachine dep.digests dep.idealOracle dep.deploymentId dep.pk
        dep.quorum).AdmitsTrace
        (Qsag.Spec.projectTrace (Qsag.DistCustody.shareVisIn dep) Qsag.DistCustody.shareVisOut tr) ∧
      stFinal.corrupt.length < dep.quorum.threshold ∧
      stFinal.ledger.spent ≤ dep.quorum.spendCap ∧
      (∀ r : Qsag.Spec.CustodyRelease D Sig, r ∈ stFinal.ledger.releasedHistory →
        dep.sigScheme.verify dep.pk (dep.encodeDigest r.digest) r.sig = true ∧
        r.sig = dep.idealOracle (dep.digests.digest dep.deploymentId r.intent) ∧
        ∃ p : Nat, p < dep.quorum.numParties ∧ r.intent ∈ (stFinal.nodes p).latched ∧
          r.intent.epoch < (stFinal.nodes p).latch)) ∨
    (∃ x₁ x₂ : Preimage,
      x₁ ≠ x₂ ∧ dep.commit x₁ = dep.commit x₂ ∧
      x₁ ∈ Qsag.DistCustody.observedSharePreimages dep tr ∧
      x₂ ∈ Qsag.DistCustody.observedSharePreimages dep tr) :=
  Qsag.DistCustody.distCustody_dataRefines_or_collision dep hWf hTr

/-- **The guarded authenticated custodian network refines the ideal custody functionality.**
    The concrete machine is `DistCustody.authGuardedMachine`: a `Fin n` family of custodians, each
    with a WAL record sealed under `"QSAG.BELT.LATCH.WAL.MAC/v3"` and an external anchor;
    acknowledgements tagged with `custodianAckTag` under `"QSAG.BELT.ACK.v1"`; a wire on which the
    adversary places any message; disk tampering, crashes and adaptive corruption below the
    threshold. It is `DistCustody.authMachine` with two kinds of turn refused: delivery of a validly
    tagged message in the name of an uncorrupted custodian for an intent it has not approved, and
    a crash whose disk record passes recovery with another latch or log. Assumed in
    `dep.WellFormed`: the Shamir deployment conditions, among them injectivity of the share
    commitment, and the round trip of the state codec. -/
def authenticatedCustody_refines_idealCustody {F C PK D Sig : Type}
    [Qsag.LawfulField F] [DecidableEq F] [DecidableEq C] [DecidableEq D]
    (dep : Qsag.DistCustody.AuthDeployment F C PK D Sig) (hWf : dep.WellFormed) :
    Qsag.Spec.DataRefines (Qsag.DistCustody.authGuardedMachine dep)
      (Qsag.Spec.idealCustodyMachine dep.core.digests dep.core.idealOracle dep.core.deploymentId
        dep.core.pk dep.core.quorum)
      (Qsag.DistCustody.authVisIn dep) Qsag.DistCustody.authVisOut :=
  Qsag.DistCustody.authCustody_refines_ideal dep hWf

/-- **Every execution of the authenticated custodian network is an ideal execution, or exhibits a
    forgery or a collision.** For every trace of the unguarded `DistCustody.authMachine`, one of
    the following holds.
    1. Its image under the interface maps is a trace of `Spec.idealCustodyMachine`.
    2. A state reached without any violation admits a message carrying the correct
       `"QSAG.BELT.ACK.v1"` tag under the key of an enrolled, uncorrupted custodian whose 121-byte
       preimage differs from the preimage of every acknowledgement that custodian sent.
    3. Two distinct intents of this deployment have the same message tag.
    4. The hash has a collision (a disk record other than the custodian's own carries the
       anchor's `"QSAG.BELT.LATCH.WAL.MAC/v3"` tag).
    No probability is attached to alternatives 2 to 4 here. -/
theorem authenticatedCustody_ideal_or_forgery {F C PK D Sig : Type}
    [Qsag.LawfulField F] [DecidableEq F] [DecidableEq C] [DecidableEq D]
    (dep : Qsag.DistCustody.AuthDeployment F C PK D Sig) (hWf : dep.WellFormed)
    {tr : List (Qsag.DistCustody.AuthTurn F dep.core.quorum.numParties ×
      Qsag.DistCustody.AuthEvent F Sig)}
    (hAdmits : (Qsag.DistCustody.authMachine dep).AdmitsTrace tr) :
    (Qsag.Spec.idealCustodyMachine dep.core.digests dep.core.idealOracle dep.core.deploymentId
        dep.core.pk dep.core.quorum).AdmitsTrace
        (Qsag.Spec.projectTrace (Qsag.DistCustody.authVisIn dep) Qsag.DistCustody.authVisOut tr) ∨
    (∃ (st : Qsag.DistCustody.AuthState F PK D Sig dep.core.quorum.numParties)
        (m : Qsag.DistCustody.AuthAck F),
      (Qsag.DistCustody.authGuardedMachine dep).Reachable st ∧
        Qsag.DistCustody.AckMacForgery dep st m) ∨
    Qsag.DistCustody.MsgTagCollision dep ∨ Nonempty (Qsag.HashCollision256 dep.hash) :=
  Qsag.DistCustody.authCustody_ideal_or_forgery dep hWf hAdmits

/-- **Reachable-state safety of the guarded authenticated network.** Fewer than `threshold`
    custodians are corrupted; the spend is within the cap; every WAL release carries the dealt
    key's signature on `digest deploymentId intent` and its intent is in the approval log of an
    enrolled custodian whose latch has moved past its epoch; no custodian has approved two
    intents at one epoch. -/
theorem authenticatedCustody_reachable_safe {F C PK D Sig : Type}
    [Qsag.LawfulField F] [DecidableEq F] [DecidableEq C] [DecidableEq D]
    (dep : Qsag.DistCustody.AuthDeployment F C PK D Sig) (hWf : dep.WellFormed)
    {st : Qsag.DistCustody.AuthState F PK D Sig dep.core.quorum.numParties}
    (hReach : (Qsag.DistCustody.authGuardedMachine dep).Reachable st) :
    st.corrupt.length < dep.core.quorum.threshold ∧
    st.ledger.spent ≤ dep.core.quorum.spendCap ∧
    (∀ r : Qsag.Spec.CustodyRelease D Sig, r ∈ st.ledger.releasedHistory →
      r.sig = dep.core.signWith dep.core.secret
        (dep.core.digests.digest dep.core.deploymentId r.intent) ∧
      ∃ p : Fin dep.core.quorum.numParties, r.intent ∈ (st.parties p).latched ∧
        r.intent.epoch < (st.parties p).latch) ∧
    (∀ p : Fin dep.core.quorum.numParties,
      ((st.parties p).latched.map Qsag.Spec.CustodyIntent.epoch).Nodup) := by
  obtain ⟨h1, h2, h3, h4, _⟩ := Qsag.DistCustody.authCustody_reachable_safe dep hWf hReach
  exact ⟨h1, h2, h3, h4⟩

/-- **`Pr[unsafe release] ≤ Pr[acknowledgement violation] + Pr[WAL violation]`.** Over a finite
    coin space that determines the whole deployment (keys, hash, dealt polynomial) and the
    adversary's schedule against the unguarded `DistCustody.authMachine`, the probability that the
    coordinator's WAL ends up holding a release no enrolled custodian approved is at most the sum
    of the probabilities of the two violation events.

    The two events on the right are what an unforgeability argument has to bound, and this
    library does not bound them. By `DistCustody.deliver_violation_classified` the first is a tag
    forgery under an uncorrupted custodian's key or a message-tag collision; by
    `DistCustody.crash_violation_collision` the second is a hash collision. -/
theorem authenticatedCustody_unsafe_release_le_violations {F C PK D Sig : Type}
    [Qsag.LawfulField F] [DecidableEq F] [DecidableEq C] [DecidableEq D]
    {N : Nat} (hN : 0 < N)
    (dep : Fin N → Qsag.DistCustody.AuthDeployment F C PK D Sig)
    (hWf : ∀ ω, (dep ω).WellFormed)
    (adv : (ω : Fin N) → List (Qsag.DistCustody.AuthTurn F (dep ω).core.quorum.numParties)) :
    Qsag.Spec.GameBound
      (Qsag.Spec.FinGame.mk hN (fun ω => Qsag.DistCustody.authUnsafeRelease (dep ω)
        (Qsag.DistCustody.authRun (dep ω) (Qsag.DistCustody.authViolation (dep ω))
          (Qsag.DistCustody.AuthState.init (dep ω)) (adv ω)).1)).winProb
      ((Qsag.Spec.FinGame.mk hN (fun ω =>
          (Qsag.DistCustody.authRun (dep ω) (Qsag.DistCustody.authAckViolation (dep ω))
            (Qsag.DistCustody.AuthState.init (dep ω)) (adv ω)).2)).winProb.add
        (Qsag.Spec.FinGame.mk hN (fun ω =>
          (Qsag.DistCustody.authRun (dep ω) (Qsag.DistCustody.authWalViolation (dep ω))
            (Qsag.DistCustody.AuthState.init (dep ω)) (adv ω)).2)).winProb) :=
  Qsag.Spec.event_le_two_reductions _ _ _ (fun ω hU => by
    have hV := Qsag.DistCustody.authRun_unsafe_release_violation (dep ω) (hWf ω) (adv ω) hU
    rw [Qsag.DistCustody.authRun_violation_split] at hV
    exact Bool.or_eq_true_iff.mp hV)

/-- **Conditional bound on unsafe release.** If the acknowledgement-violation event has
    probability at most `εAck` and the WAL-violation event at most `εWal`, then an unsafe release
    has probability at most `εAck + εWal`; if that sum is at most `2^{-b}`, so is the probability
    of an unsafe release. `hAck` and `hWal` are hypotheses: they are the unforgeability of
    `custodianAckTag` under uncorrupted keys together with collision resistance of the message
    tag, and collision resistance of the hash. Nothing in this library discharges them. -/
theorem authenticatedCustody_unsafe_release_bound {F C PK D Sig : Type}
    [Qsag.LawfulField F] [DecidableEq F] [DecidableEq C] [DecidableEq D]
    {N : Nat} (hN : 0 < N)
    (dep : Fin N → Qsag.DistCustody.AuthDeployment F C PK D Sig)
    (hWf : ∀ ω, (dep ω).WellFormed)
    (adv : (ω : Fin N) → List (Qsag.DistCustody.AuthTurn F (dep ω).core.quorum.numParties))
    (εAck εWal : Qsag.Spec.RatBound)
    (hAck : Qsag.Spec.GameBound
      (Qsag.Spec.FinGame.mk hN (fun ω =>
        (Qsag.DistCustody.authRun (dep ω) (Qsag.DistCustody.authAckViolation (dep ω))
          (Qsag.DistCustody.AuthState.init (dep ω)) (adv ω)).2)).winProb εAck)
    (hWal : Qsag.Spec.GameBound
      (Qsag.Spec.FinGame.mk hN (fun ω =>
        (Qsag.DistCustody.authRun (dep ω) (Qsag.DistCustody.authWalViolation (dep ω))
          (Qsag.DistCustody.AuthState.init (dep ω)) (adv ω)).2)).winProb εWal) :
    Qsag.Spec.GameBound
      (Qsag.Spec.FinGame.mk hN (fun ω => Qsag.DistCustody.authUnsafeRelease (dep ω)
        (Qsag.DistCustody.authRun (dep ω) (Qsag.DistCustody.authViolation (dep ω))
          (Qsag.DistCustody.AuthState.init (dep ω)) (adv ω)).1)).winProb
      (εAck.add εWal) ∧
    (∀ b : Nat, (εAck.add εWal).atLeastBits b →
      (Qsag.Spec.FinGame.mk hN (fun ω => Qsag.DistCustody.authUnsafeRelease (dep ω)
        (Qsag.DistCustody.authRun (dep ω) (Qsag.DistCustody.authViolation (dep ω))
          (Qsag.DistCustody.AuthState.init (dep ω)) (adv ω)).1)).winProb.atLeastBits b) := by
  have hBound := Qsag.Spec.GameBound.trans
    (authenticatedCustody_unsafe_release_le_violations hN dep hWf adv)
    (Qsag.Spec.RatBound.add_le_add hAck hWal)
  exact ⟨hBound, fun _ hBits => Qsag.Spec.GameBound.atLeastBits hBound hBits⟩

/-- **A Shamir custodian refines the complete-mediation vault machine.** Concrete state is the
    custodian's `BeltLatchNodeState` and `Custody.Vault`; both machines start in any
    `Custody.Safe` vault, and the alphabet covers certified mints (for `deploymentId`), one-time
    share releases, forgets and crashes. -/
def shamirCustodian_refines_mediationVault {n L d : Nat}
    (H : List UInt8 → Qsag.Digest256)
    (MAC : Qsag.Digest256 → List UInt8 → Qsag.Digest256)
    (macKeys : Fin n → Fin n → Qsag.Digest256)
    (masterSeed : Qsag.Digest256)
    (polyTape : UInt64 → Qsag.PreSteppedDigest256ShamirTape d L)
    (evalPt : Qsag.TowerElem 7) (party : Fin n)
    (q deploymentId : Nat) (policy : Qsag.Custody.RoundPolicy) (cap : Nat) :
    Qsag.shamirCustodianMachine H MAC macKeys masterSeed polyTape evalPt party q deploymentId
        policy cap ⊑
      Qsag.abstractMediationVaultMachine H MAC macKeys masterSeed polyTape evalPt party q
        deploymentId policy cap :=
  Qsag.shamirCustodianRefines H MAC macKeys masterSeed polyTape evalPt party q deploymentId
    policy cap

/-- **Multi-turn Shamir custody network: spend caps, leaf uniqueness, epoch non-equivocation and
    deployment-bound vaults.** Over any open-world schedule of belt turns, certified mints, share
    releases, combines, forgets and crashes: every vault stays within its cap and keeps the
    identity of its custodian in this deployment, no honest custodian releases shares for two
    intents at one leaf, and two threshold subsets that obtain releases at one leaf agree on the
    intent unless a pairwise echo MAC is forged or `dep.H` collides. -/
theorem shamir_custody_network_non_equivocation {n L d : Nat}
    (dep : Qsag.ShamirValidatorDeployment n L d)
    (hCorrupt : Qsag.maskCard dep.Corrupt ≤ dep.f)
    (hFltT : dep.f < dep.t)
    (hLatchQuorum : 2 * dep.q > n + dep.f)
    (trace : List (Qsag.ShamirCustodyTurn n L)) :
    let st := Qsag.runShamirCustodyTrace dep (Qsag.ShamirCustodyNetworkState.init dep) trace
    (∀ p : Fin n, (st.vaults p).durable.spent ≤ dep.caps p) ∧
    (∀ p : Fin n, (st.vaults p).identity = dep.vaultIdentity p) ∧
    (∀ op₁ ∈ st.honestShareReleases, ∀ op₂ ∈ st.honestShareReleases,
      op₁.party = op₂.party → op₁.intent.leaf = op₂.intent.leaf → op₁.intent = op₂.intent) ∧
    (∀ (S₁ S₂ : Qsag.CustodiansMask n) (r₁ r₂ : Qsag.Custody.Intent),
      dep.t ≤ Qsag.maskCard S₁ →
      dep.t ≤ Qsag.maskCard S₂ →
      Qsag.HonestQuorumReleasedIntent dep.Corrupt st S₁ r₁ →
      Qsag.HonestQuorumReleasedIntent dep.Corrupt st S₂ r₂ →
      r₁.leaf = r₂.leaf →
      r₁ = r₂ ∨
        Nonempty (Qsag.PairwiseEchoMacForgery dep.MAC dep.macKeys dep.Corrupt
          st.beltNet.emittedHonestEchoes) ∨
        Nonempty (Qsag.HashCollision256 dep.H)) := by
  intro st
  obtain ⟨h1, h2, h3⟩ :=
    Qsag.shamir_custody_epoch_non_equivocation dep hCorrupt hFltT hLatchQuorum trace
  exact ⟨h1, fun p => Qsag.runShamirCustodyTrace_identity dep trace p, h2, h3⟩


/-! ## 10. Roster: library theorems restated verbatim at the top level

Each theorem below restates a theorem of the imported modules with its full type and is
proved by citing it. The block between the markers is the comparator roster: the statements a
challenge-file generator copies out to be re-proved against the library. -/

/-- A well-formed Shamir deployment reconstructs from every distinct quorum of threshold size. -/
theorem shamir_wellformed_lagrange_reconstructs {n L d : Nat}
    {dep : Qsag.ShamirValidatorDeployment n L d} (hWf : dep.WellFormed)
    (parties : List (Fin n)) (hNd : parties.Nodup) (hThr : dep.t ≤ parties.length)
    (c₀ : Qsag.TowerElem 7) (tail : Qsag.ShamirPadPoly (Qsag.TowerElem 7) d) :
    Qsag.ringDot (dep.lagrangeWeights parties)
      ((parties.map dep.evalPts).map (fun x => Qsag.RoundPoly.evalCoeffs (c₀ :: tail.1) x)) = c₀ :=
  Qsag.wellFormed_lagrange_reconstructs hWf parties hNd hThr c₀ tail

section Roster
open Qsag

open CommRingOps
open Qsag.RustDurability

-- BEGIN COMPARATOR ROSTER

/-! ### Threshold approval, BDOZ MAC-before-open and key-recovery alternative, KOS correlation check -/

open CommRingOps in
theorem thresholdApproval_requires_honest_party {PK Msg : Type}
    (st : IdealTsigState PK Msg) (honestApprovers : List Nat)
    (_hDishonestBound : st.corruptParties.length + 1 ≤ st.threshold)
    (hValid : validThresholdApproval st honestApprovers = true) :
    ∃ h ∈ honestApprovers, h < st.numParties ∧ h ∉ st.corruptParties :=
  _root_.Qsag.thresholdApproval_requires_honest_party st honestApprovers _hDishonestBound hValid

open CommRingOps in
theorem unilateral_empty_quorum_rejected {PK Msg : Type}
    (st : IdealTsigState PK Msg)
    (hThreshold : 0 < st.threshold ∧ st.threshold ≤ st.numParties)
    (hCorruptNd : st.corruptParties.Nodup)
    (hCorruptRange : ∀ c ∈ st.corruptParties, c < st.numParties)
    (hCorruptFull : st.corruptParties.length = st.threshold) :
    let mutantAllowFullCorruptQuorum (s : IdealTsigState PK Msg) (hon : List Nat) : Bool :=
      decide (0 < s.threshold ∧ s.threshold ≤ s.numParties) &&
      decide s.corruptParties.Nodup &&
      s.corruptParties.all (fun c => decide (c < s.numParties)) &&
      decide hon.Nodup &&
      decide (s.threshold ≤ s.corruptParties.length + hon.length)
    validThresholdApproval st [] = false ∧
    mutantAllowFullCorruptQuorum st [] = true :=
  _root_.Qsag.unilateral_empty_quorum_rejected st hThreshold hCorruptNd hCorruptRange hCorruptFull

open CommRingOps in
theorem duplicate_corrupt_parties_rejected {PK Msg : Type}
    (st : IdealTsigState PK Msg) (honestApprovers : List Nat)
    (hDup : ¬ st.corruptParties.Nodup) :
    validThresholdApproval st honestApprovers = false :=
  _root_.Qsag.duplicate_corrupt_parties_rejected st honestApprovers hDup

open CommRingOps in
theorem out_of_range_corrupt_parties_rejected {PK Msg : Type}
    (st : IdealTsigState PK Msg) (honestApprovers : List Nat)
    (c : Nat) (hc : c ∈ st.corruptParties) (hRange : ¬ c < st.numParties) :
    validThresholdApproval st honestApprovers = false :=
  _root_.Qsag.out_of_range_corrupt_parties_rejected st honestApprovers c hc hRange

open CommRingOps in
theorem ratLe_zero_den_false (a b c : Nat) : ¬ ratLe (a, 0) (b, c) ∧ ¬ ratLe (a, c) (b, 0) :=
  _root_.Qsag.ratLe_zero_den_false a b c

theorem bdoz_pair_key_recovery
    (vk : BdozVerifierKeys) (opHon opAdv : BdozPairOpening)
    (hPid : opHon.partyId = opAdv.partyId)
    (hNe : opHon.shareX ≠ opAdv.shareX)
    (hVerH : verifyBdozPairMac vk opHon = true)
    (hVerA : verifyBdozPairMac vk opAdv = true) :
    let dxInv := towerInv 7 (towerAdd 7 opAdv.shareX opHon.shareX)
    towerMul 7 (towerAdd 7 opAdv.mac0 opHon.mac0) dxInv = vk.alpha0 ∧
    towerMul 7 (towerAdd 7 opAdv.mac1 opHon.mac1) dxInv = vk.alpha1 :=
  _root_.Qsag.bdoz_pair_key_recovery vk opHon opAdv hPid hNe hVerH hVerA

theorem bdoz_2lane_mac_soundness
    (L : Nat) (deltas : List Tower128) (S : List Tower128)
    (hNodup : S.Nodup) (hLen : deltas.length ≤ L) (hDom : L + 1 ≤ S.length)
    (hNonzero : ∃ d ∈ deltas, d ≠ towerZero 7) :
    (S.filter (fun r => decide (batchDeviationPoly deltas r = towerZero 7))).length ≤ L ∧
    (∀ (vk : BdozVerifierKeys) (opHon opAdv : BdozPairOpening),
      opHon.partyId = opAdv.partyId →
      opHon.shareX ≠ opAdv.shareX →
      verifyBdozPairMac vk opHon = true →
      verifyBdozPairMac vk opAdv = true →
      let dxInv := towerInv 7 (towerAdd 7 opAdv.shareX opHon.shareX)
      towerMul 7 (towerAdd 7 opAdv.mac0 opHon.mac0) dxInv = vk.alpha0 ∧
      towerMul 7 (towerAdd 7 opAdv.mac1 opHon.mac1) dxInv = vk.alpha1) :=
  _root_.Qsag.bdoz_2lane_mac_soundness L deltas S hNodup hLen hDom hNonzero

theorem mac_before_open_released_origin
    (vk : BdozVerifierKeys) (turns : List CutCandidateOpening) (initialEpoch : Nat) :
    ∀ pair ∈ (runMacBeforeOpenTrace vk ⟨initialEpoch, [], 0, false⟩ turns).releasedHistory,
      ∃ t ∈ turns, pair = (t.epoch, t.candidateBytes) ∧
        verifyBdozPairMac vk t.opening = true :=
  _root_.Qsag.mac_before_open_released_origin vk turns initialEpoch

theorem mac_before_open_blocks_faulted_cut_leakage
    (vk : BdozVerifierKeys) (turns : List CutCandidateOpening) (initialEpoch : Nat)
    (honestOpening : CutCandidateOpening → BdozPairOpening)
    (hHonest : ∀ t ∈ turns, verifyBdozPairMac vk (honestOpening t) = true)
    (hParty : ∀ t ∈ turns, (honestOpening t).partyId = t.opening.partyId)
    (hBind : ∀ t ∈ turns, t.candidateBytes ≠ t.trueCutBytes →
      (honestOpening t).shareX ≠ t.opening.shareX) :
    ∀ pair ∈ (runMacBeforeOpenTrace vk ⟨initialEpoch, [], 0, false⟩ turns).releasedHistory,
      ∃ t ∈ turns, pair = (t.epoch, t.candidateBytes) ∧
        verifyBdozPairMac vk t.opening = true ∧
        (t.candidateBytes = t.trueCutBytes ∨
          let dxInv := towerInv 7 (towerAdd 7 t.opening.shareX (honestOpening t).shareX)
          towerMul 7 (towerAdd 7 t.opening.mac0 (honestOpening t).mac0) dxInv = vk.alpha0 ∧
          towerMul 7 (towerAdd 7 t.opening.mac1 (honestOpening t).mac1) dxInv = vk.alpha1) :=
  _root_.Qsag.mac_before_open_blocks_faulted_cut_leakage vk turns initialEpoch honestOpening hHonest hParty hBind

theorem kos_interactive_check_sound (k : Nat) (deltaU secretDelta : TowerBitVec k)
    (chi : TowerElem k) (hChi : chi ≠ towerZero k) :
    kosColumnResidual k deltaU secretDelta (towerZero k) chi = towerZero k ↔
      unpackTower k (deltaU &&& secretDelta) = towerZero k :=
  _root_.Qsag.kos_interactive_check_sound k deltaU secretDelta chi hChi

theorem kos_single_bit_does_not_pin_key :
    (0#128 : TowerBitVec 7) ≠ 2#128 ∧
    kosColumnResidual 7 1#128 0#128 (towerZero 7) (towerOne 7) = towerZero 7 ∧
    kosColumnResidual 7 1#128 2#128 (towerZero 7) (towerOne 7) = towerZero 7 :=
  _root_.Qsag.kos_single_bit_does_not_pin_key

/-! ### Concrete UC simulator over 128-bit BinaryTower -/

open CommRingOps in
theorem shamir_share_pad_rebalance {R : Type} [LawfulCommRing R]
    (inv : R → R) (hInv : ∀ x : R, x ≠ zero → mul x (inv x) = one)
    (d : Nat) (corruptPts : List R) (w : R)
    (hCard : corruptPts.length + 1 ≤ d + 1)
    (hNonZero : ∀ c ∈ corruptPts, c ≠ zero)
    (A : ShamirPadPoly R d) (P : ShamirPadPoly R (d + 1)) :
    let A' := (shamirShare_rebalanceEquiv inv d corruptPts w hCard).toFun A
    let P' := (shamir_rebalanceEquiv inv (d + 1) corruptPts w hCard).toFun P
    (∀ xc ∈ corruptPts,
      RoundPoly.evalCoeffs (zero :: A'.1) xc = RoundPoly.evalCoeffs (w :: A.1) xc) ∧
    (∀ xc ∈ corruptPts, RoundPoly.evalCoeffs P'.1 xc = RoundPoly.evalCoeffs P.1 xc) ∧
    (∀ x : R,
      add (RoundPoly.evalCoeffs (zero :: A'.1) x) (RoundPoly.evalCoeffs P'.1 x) =
        add (RoundPoly.evalCoeffs (w :: A.1) x) (RoundPoly.evalCoeffs P.1 x)) :=
  _root_.Qsag.shamir_share_pad_rebalance inv hInv d corruptPts w hCard hNonZero A P

theorem bdoz_tampered_opening_accepting_keys_le_one
    (CK : Nat) (keyDec : Fin CK → Tower128 × Tower128)
    (hInj : ∀ i j, keyDec i = keyDec j → i = j)
    (hon : Nat → Tower128 × Tower128 × Tower128) (op : BdozPairOpening)
    (hNe : op.shareX ≠ (hon op.partyId).1) :
    qsum CK (fun i =>
      if verifyBdozPairMac (bdozKeyFromView (keyDec i) hon) op then 1 else 0) ≤ 1 :=
  _root_.Qsag.bdoz_tampered_opening_accepting_keys_le_one CK keyDec hInj hon op hNe

theorem bdoz_tag_tamper_rejected (vk : BdozVerifierKeys) (op : BdozPairOpening)
    (hAcc : verifyBdozPairMac vk op = true) (delta : Tower128) (hDelta : delta ≠ towerZero 7) :
    verifyBdozPairMac vk { op with mac0 := towerAdd 7 op.mac0 delta } = false :=
  _root_.Qsag.bdoz_tag_tamper_rejected vk op hAcc delta hDelta

open CommRingOps in
theorem ucSimulatorTsig_hop1_perfect {R PK SK Msg Sig : Type} [LawfulCommRing R]
    (S : AbstractSigScheme PK SK Msg Sig) (pp : TsigParams R Sig)
    (wireVals : SK → Msg → Fin pp.k → R) (outVal : SK → Msg → R)
    (hCircuit : ∀ sk m, outVal sk m = pp.encSig (S.sign sk m))
    (inv : R → R) (hInv : ∀ x : R, x ≠ zero → mul x (inv x) = one)
    (pk : PK) (corrupt honest : List (Nat × R))
    (hCard : (corrupt.map Prod.snd).length + 1 ≤ pp.d + 1)
    (hNonZero : ∀ cx ∈ corrupt, cx.2 ≠ zero)
    (corruptVk : Nat → BdozVerifierKeys) (corruptTags : Nat → Tower128 × Tower128)
    (sk : SK) (m : Msg)
    (Ct : Nat) (padEnum : SimpleEquiv (Fin Ct) (TsigPadTape R pp.d pp.k))
    (macKey : Tower128 × Tower128) (D : Option (TsigAdvView R pp.k) → Bool) :
    qsum Ct (fun i =>
      if D (some (tsigSessionView pp corruptVk corrupt honest (wireVals sk m) (outVal sk m)
        (padEnum.toFun i))) then 1 else 0) =
    qsum Ct (fun i =>
      if D (ucSimulatorTsig pp
        ⟨pk, m, corrupt, honest, corruptVk, corruptTags, .signed (S.sign sk m)⟩
        ⟨padEnum.toFun i, macKey⟩) then 1 else 0) :=
  _root_.Qsag.ucSimulatorTsig_hop1_perfect S pp wireVals outVal hCircuit inv hInv pk corrupt honest hCard hNonZero corruptVk corruptTags sk m Ct padEnum macKey D

open CommRingOps in
theorem tsig_real_eq_ideal_or_forgery {R PK SK Msg Sig : Type} [LawfulCommRing R]
    (S : AbstractSigScheme PK SK Msg Sig) (pp : TsigParams R Sig)
    (wireVals : SK → Msg → Fin pp.k → R) (outVal : SK → Msg → R)
    (hCircuit : ∀ sk m, outVal sk m = pp.encSig (S.sign sk m))
    (hDec : ∀ s, pp.decSig (pp.encSig s) = s)
    (hEmb : ∀ r, pp.unemb (pp.emb r) = r)
    (inv : R → R) (hInv : ∀ x : R, x ≠ zero → mul x (inv x) = one)
    (st : IdealTsigState PK Msg) (corrupt honest : List (Nat × R))
    (hIds : st.corruptParties = corrupt.map Prod.fst)
    (hCard : (corrupt.map Prod.snd).length + 1 ≤ pp.d + 1)
    (hNonZero : ∀ cx ∈ corrupt, cx.2 ≠ zero)
    (hRecon : ∀ coeffs : List R, coeffs.length ≤ pp.d + 1 →
      ringDot pp.lambdas ((honest ++ corrupt).map (fun hx => RoundPoly.evalCoeffs coeffs hx.2)) =
        RoundPoly.evalCoeffs coeffs zero)
    (corruptVk : Nat → BdozVerifierKeys) (corruptTags : Nat → Tower128 × Tower128)
    (sk : SK) (m : Msg) (approvers : List Nat) (Adv : TsigAdversary R Sig pp.k)
    (τ : TsigPadTape R pp.d pp.k) (κ : Tower128 × Tower128) :
    tsigRealExec pp wireVals outVal st corrupt honest corruptVk corruptTags sk m approvers Adv τ κ =
      tsigIdealExec S pp st corrupt honest corruptVk corruptTags sk m approvers Adv
        ⟨(tsigTapeRebalance inv pp.d pp.k (corrupt.map Prod.snd) hCard (wireVals sk m)).toFun τ, κ⟩ ∨
    ∃ op ∈ Adv.openings
        (tsigSessionView pp corruptVk corrupt honest (wireVals sk m) (outVal sk m) τ),
      BdozMacForgeryWitness
        (tsigVerifierKey κ corruptTags
          (tsigSessionExpected pp corrupt (wireVals sk m) (outVal sk m) τ))
        (bdozViewOpening (fun s =>
          (tsigShareAt (tsigSessionExpected pp corrupt (wireVals sk m) (outVal sk m) τ) s,
            corruptTags s)) op.partyId) op ∧
      κ = bdozKeyGuess (fun s =>
          (tsigShareAt (tsigSessionExpected pp corrupt (wireVals sk m) (outVal sk m) τ) s,
            corruptTags s)) op :=
  _root_.Qsag.tsig_real_eq_ideal_or_forgery S pp wireVals outVal hCircuit hDec hEmb inv hInv st corrupt honest hIds hCard hNonZero hRecon corruptVk corruptTags sk m approvers Adv τ κ

open CommRingOps in
theorem tsigForgery_keys_le (CK : Nat) (keyDec : Fin CK → Tower128 × Tower128)
    (hInj : ∀ i j, keyDec i = keyDec j → i = j) :
    ∀ (es : List (Nat × Tower128)) (s : Nat) (ops : List BdozPairOpening)
      (hon : Nat → Tower128 × Tower128 × Tower128),
      (∀ i, (hon (s + i)).1 = tsigShareAt es i) →
      qsum CK (fun i =>
        if (tsigFindForgery (bdozKeyFromView (keyDec i) hon) s es ops).isSome then 1 else 0) ≤
        es.length :=
  _root_.Qsag.tsigForgery_keys_le CK keyDec hInj

open CommRingOps in
theorem ucSimulatorTsig_advantage_bound {R PK SK Msg Sig : Type} [LawfulCommRing R]
    (S : AbstractSigScheme PK SK Msg Sig) (pp : TsigParams R Sig)
    (wireVals : SK → Msg → Fin pp.k → R) (outVal : SK → Msg → R)
    (hCircuit : ∀ sk m, outVal sk m = pp.encSig (S.sign sk m))
    (hDec : ∀ s, pp.decSig (pp.encSig s) = s)
    (hEmb : ∀ r, pp.unemb (pp.emb r) = r)
    (inv : R → R) (hInv : ∀ x : R, x ≠ zero → mul x (inv x) = one)
    (st : IdealTsigState PK Msg) (corrupt honest : List (Nat × R))
    (hIds : st.corruptParties = corrupt.map Prod.fst)
    (hThreshold : st.threshold = pp.d + 1)
    (hBound : st.corruptParties.length + 1 ≤ st.threshold)
    (hNonZero : ∀ cx ∈ corrupt, cx.2 ≠ zero)
    (hRecon : ∀ coeffs : List R, coeffs.length ≤ pp.d + 1 →
      ringDot pp.lambdas ((honest ++ corrupt).map (fun hx => RoundPoly.evalCoeffs coeffs hx.2)) =
        RoundPoly.evalCoeffs coeffs zero)
    (corruptVk : Nat → BdozVerifierKeys) (corruptTags : Nat → Tower128 × Tower128)
    (sk : SK) (m : Msg) (approvers : List Nat) (Adv : TsigAdversary R Sig pp.k)
    (Ct : Nat) (padEnum : SimpleEquiv (Fin Ct) (TsigPadTape R pp.d pp.k))
    (CK : Nat) (keyDec : Fin CK → Tower128 × Tower128)
    (hKeyInj : ∀ i j, keyDec i = keyDec j → i = j)
    (Cs : Nat) (prg : Fin Cs → TsigPadTape R pp.d pp.k)
    (Co : Nat) (ot : Fin Co → Tower128 × Tower128) :
    let real := fun (τ : TsigPadTape R pp.d pp.k) (κ : Tower128 × Tower128) =>
      tsigRealExec pp wireVals outVal st corrupt honest corruptVk corruptTags sk m approvers Adv τ κ
    let ideal := fun (τ : TsigPadTape R pp.d pp.k) (κ : Tower128 × Tower128) =>
      tsigIdealExec S pp st corrupt honest corruptVk corruptTags sk m approvers Adv ⟨τ, κ⟩
    natAbsDiff (acceptPairs Cs Co prg ot real * (Ct * CK))
               (acceptPairs Ct CK padEnum.toFun keyDec ideal * (Cs * Co)) ≤
      Cs * Co * (Ct * ((pp.k + 1) * corrupt.length))
        + CK * prgReductionAdvNum Cs Ct Co prg padEnum.toFun ot real
        + Cs * otReductionAdvNum Ct Co CK padEnum.toFun ot keyDec real :=
  _root_.Qsag.ucSimulatorTsig_advantage_bound S pp wireVals outVal hCircuit hDec hEmb inv hInv st corrupt honest hIds hThreshold hBound hNonZero hRecon corruptVk corruptTags sk m approvers Adv Ct padEnum CK keyDec hKeyInj Cs prg Co ot

open CommRingOps in
theorem ucSimulatorTsig_distinguisher_breaks_generator {R PK SK Msg Sig : Type} [LawfulCommRing R]
    (S : AbstractSigScheme PK SK Msg Sig) (pp : TsigParams R Sig)
    (wireVals : SK → Msg → Fin pp.k → R) (outVal : SK → Msg → R)
    (hCircuit : ∀ sk m, outVal sk m = pp.encSig (S.sign sk m))
    (hDec : ∀ s, pp.decSig (pp.encSig s) = s)
    (hEmb : ∀ r, pp.unemb (pp.emb r) = r)
    (inv : R → R) (hInv : ∀ x : R, x ≠ zero → mul x (inv x) = one)
    (st : IdealTsigState PK Msg) (corrupt honest : List (Nat × R))
    (hIds : st.corruptParties = corrupt.map Prod.fst)
    (hThreshold : st.threshold = pp.d + 1)
    (hBound : st.corruptParties.length + 1 ≤ st.threshold)
    (hNonZero : ∀ cx ∈ corrupt, cx.2 ≠ zero)
    (hRecon : ∀ coeffs : List R, coeffs.length ≤ pp.d + 1 →
      ringDot pp.lambdas ((honest ++ corrupt).map (fun hx => RoundPoly.evalCoeffs coeffs hx.2)) =
        RoundPoly.evalCoeffs coeffs zero)
    (corruptVk : Nat → BdozVerifierKeys) (corruptTags : Nat → Tower128 × Tower128)
    (sk : SK) (m : Msg) (approvers : List Nat) (Adv : TsigAdversary R Sig pp.k)
    (Ct : Nat) (padEnum : SimpleEquiv (Fin Ct) (TsigPadTape R pp.d pp.k))
    (CK : Nat) (keyDec : Fin CK → Tower128 × Tower128)
    (hKeyInj : ∀ i j, keyDec i = keyDec j → i = j)
    (Cs : Nat) (prg : Fin Cs → TsigPadTape R pp.d pp.k)
    (Co : Nat) (ot : Fin Co → Tower128 × Tower128) :
    let real := fun (τ : TsigPadTape R pp.d pp.k) (κ : Tower128 × Tower128) =>
      tsigRealExec pp wireVals outVal st corrupt honest corruptVk corruptTags sk m approvers Adv τ κ
    let ideal := fun (τ : TsigPadTape R pp.d pp.k) (κ : Tower128 × Tower128) =>
      tsigIdealExec S pp st corrupt honest corruptVk corruptTags sk m approvers Adv ⟨τ, κ⟩
    Cs * Co * (Ct * ((pp.k + 1) * corrupt.length)) <
        natAbsDiff (acceptPairs Cs Co prg ot real * (Ct * CK))
                   (acceptPairs Ct CK padEnum.toFun keyDec ideal * (Cs * Co)) →
    0 < prgReductionAdvNum Cs Ct Co prg padEnum.toFun ot real ∨
    0 < otReductionAdvNum Ct Co CK padEnum.toFun ot keyDec real :=
  _root_.Qsag.ucSimulatorTsig_distinguisher_breaks_generator S pp wireVals outVal hCircuit hDec hEmb inv hInv st corrupt honest hIds hThreshold hBound hNonZero hRecon corruptVk corruptTags sk m approvers Adv Ct padEnum CK keyDec hKeyInj Cs prg Co ot

open CommRingOps in
theorem ucSimulatorTsig_advantage_bound_tower128
    (Adv : TsigAdversary Tower128 Tower128 tower128Params.k)
    (corruptVk : Nat → BdozVerifierKeys) (corruptTags : Nat → Tower128 × Tower128)
    (a b : Tower128) (skPad aPad bPad cPad : ShamirPadPoly Tower128 1)
    (sk m : Tower128)
    (Cs : Nat) (prg : Fin Cs → TsigPadTape Tower128 tower128Params.d tower128Params.k)
    (Co : Nat) (ot : Fin Co → Tower128 × Tower128) :
    let vault : SharedBeaverSessionVault Tower128 1 := ⟨sk, skPad, a, aPad, b, bPad, cPad⟩
    let real := fun (τ : TsigPadTape Tower128 tower128Params.d tower128Params.k)
        (κ : Tower128 × Tower128) =>
      tsigSharedBeaverRealExec tower128Params tower128State tower128Corrupt
        tower128Honest corruptVk corruptTags (dealPartyBeaverShares vault) m [0] Adv τ κ
    let ideal := fun (τ : TsigPadTape Tower128 tower128Params.d tower128Params.k)
        (κ : Tower128 × Tower128) =>
      tsigIdealExec tower128BeaverSig tower128Params tower128State tower128Corrupt tower128Honest
        corruptVk corruptTags sk m [0] Adv ⟨τ, κ⟩
    validThresholdApproval tower128State [0] = true ∧
    natAbsDiff
      (acceptPairs Cs Co prg ot real * (tower128PadCard * tower128KeyCard))
      (acceptPairs tower128PadCard tower128KeyCard tower128PadEnum.toFun tower128KeyDec ideal * (Cs * Co)) ≤
      Cs * Co * (tower128PadCard * ((tower128Params.k + 1) * tower128Corrupt.length))
        + tower128KeyCard * prgReductionAdvNum Cs tower128PadCard Co prg tower128PadEnum.toFun ot real
        + Cs * otReductionAdvNum tower128PadCard Co tower128KeyCard tower128PadEnum.toFun ot tower128KeyDec real :=
  _root_.Qsag.ucSimulatorTsig_advantage_bound_tower128 Adv corruptVk corruptTags a b skPad aPad bPad cPad sk m Cs prg Co ot

open CommRingOps in
theorem ucSimulatorTsig_nonvacuous_sub_unity_tower128
    (Adv : TsigAdversary Tower128 Tower128 tower128Params.k)
    (corruptVk : Nat → BdozVerifierKeys) (corruptTags : Nat → Tower128 × Tower128)
    (a b : Tower128) (skPad aPad bPad cPad : ShamirPadPoly Tower128 1)
    (sk m : Tower128) :
    let vault : SharedBeaverSessionVault Tower128 1 := ⟨sk, skPad, a, aPad, b, bPad, cPad⟩
    let real := fun (τ : TsigPadTape Tower128 tower128Params.d tower128Params.k)
        (κ : Tower128 × Tower128) =>
      tsigSharedBeaverRealExec tower128Params tower128State tower128Corrupt
        tower128Honest corruptVk corruptTags (dealPartyBeaverShares vault) m [0] Adv τ κ
    let ideal := fun (τ : TsigPadTape Tower128 tower128Params.d tower128Params.k)
        (κ : Tower128 × Tower128) =>
      tsigIdealExec tower128BeaverSig tower128Params tower128State tower128Corrupt tower128Honest
        corruptVk corruptTags sk m [0] Adv ⟨τ, κ⟩
    let sampleSpace := tower128PadCard * tower128KeyCard
    let advGap := natAbsDiff
      (acceptPairs tower128PadCard tower128KeyCard tower128PadEnum.toFun tower128KeyDec real)
      (acceptPairs tower128PadCard tower128KeyCard tower128PadEnum.toFun tower128KeyDec ideal)
    ratLe (advGap, sampleSpace) (3, tower128KeyCard) ∧
    3 < tower128KeyCard :=
  _root_.Qsag.ucSimulatorTsig_nonvacuous_sub_unity_tower128 Adv corruptVk corruptTags a b skPad aPad bPad cPad sk m

open CommRingOps in
theorem tsigRealOutcome_tower128_signs_and_rejects
    (corruptVk : Nat → BdozVerifierKeys) (tags : Nat → Tower128 × Tower128)
    (alpha : Tower128 × Tower128) (a b sk m : Tower128)
    (skPad aPad bPad cPad : ShamirPadPoly Tower128 1)
    (τ : TsigPadTape Tower128 tower128Params.d tower128Params.k) (ops : List BdozPairOpening) :
    let w := tower128SharedWireVals a b skPad aPad bPad cPad sk m
    let y := tower128SharedOutVal a b skPad aPad bPad cPad sk m
    tsigRealOutcome tower128Params tower128Corrupt.length
        (tsigVerifierKey alpha tags
          (tsigSessionExpected tower128Params tower128Corrupt w y τ))
        (tsigSessionExpected tower128Params tower128Corrupt w y τ)
        (tsigSessionView tower128Params corruptVk tower128Corrupt tower128Honest w y τ).outHonestOpenings
        (tsigDealtOpenings
          (fun s => (tsigShareAt
            (tsigSessionExpected tower128Params tower128Corrupt w y τ) s, tags s))
          0 (tsigSessionExpected tower128Params tower128Corrupt w y τ).length) =
      .signed (towerMul 7 sk (towerAdd 7 sk m)) ∧
    tsigRealOutcome tower128Params tower128Corrupt.length
        (tsigVerifierKey alpha tags
          (tsigSessionExpected tower128Params tower128Corrupt w y τ))
        (tsigSessionExpected tower128Params tower128Corrupt w y τ)
        (tsigSessionView tower128Params corruptVk tower128Corrupt tower128Honest w y τ).outHonestOpenings
        ({ bdozViewOpening (fun s => (tsigShareAt
            (tsigSessionExpected tower128Params tower128Corrupt w y τ) s,
              tags s)) 0 with
            mac0 := towerAdd 7 (tags 0).1 (towerOne 7) } :: ops) = .abortedBy 2 :=
  _root_.Qsag.tsigRealOutcome_tower128_signs_and_rejects corruptVk tags alpha a b sk m skPad aPad bPad cPad τ ops

theorem rss3_toprf_honest {F : Type} [LawfulCommRing F] [DecidableEq F] (shares : Fin 3 → F)
    (responses : Fin 3 → Fin 3 → Option F)
    (h : ∀ p c, p ≠ c → responses p c = some (shares c)) :
    reconstructRss3Toprf responses = some (sum3 shares) :=
  _root_.Qsag.rss3_toprf_honest shares responses h

theorem rss3_toprf_single_byzantine_detected {F : Type} [LawfulCommRing F] [DecidableEq F]
    (shares : Fin 3 → F) (liar : Fin 3) (responses : Fin 3 → Fin 3 → Option F)
    (h : ∀ p c, p ≠ c → p ≠ liar → responses p c = some (shares c)) :
    reconstructRss3Toprf responses = some (sum3 shares) ∨
      reconstructRss3Toprf responses = none :=
  _root_.Qsag.rss3_toprf_single_byzantine_detected shares liar responses h

theorem rss3_two_server_reconstruct {F : Type} [LawfulCommRing F]
    (a b : Fin 3) (hab : a ≠ b) (shares : Fin 3 → F) :
    (fun c => if c = a then rss3ServerView b shares c else rss3ServerView a shares c) =
      shares :=
  _root_.Qsag.rss3_two_server_reconstruct a b hab shares

theorem rss3_client_blind_perfect_privacy {F : Type} [LawfulCommRing F]
    (p : Fin 3) (view : Fin 3 → F) (hview : view p = CommRingOps.zero) (x : F) :
    ∃ c : Fin 3 → F, (sum3 c = x ∧ rss3ServerView p c = view) ∧
      ∀ c' : Fin 3 → F, sum3 c' = x → rss3ServerView p c' = view → c' = c :=
  _root_.Qsag.rss3_client_blind_perfect_privacy p view hview x

theorem tooth_rss3_single_silent_server_aborts :
    ∃ (shares : Fin 3 → Goldilocks) (liar : Fin 3)
      (responses : Fin 3 → Fin 3 → Option Goldilocks),
      (∀ p c, p ≠ c → p ≠ liar → responses p c = some (shares c)) ∧
      reconstructRss3Toprf responses = none :=
  _root_.Qsag.tooth_rss3_single_silent_server_aborts

theorem toprf_2of5_byzantine_unique_decoding (key slope : Goldilocks)
    (ys : Fin 5 → Option Goldilocks) (h : ToprfOneByzantine toprfPoint ys (key, slope)) :
    (∀ l : Goldilocks × Goldilocks,
      3 ≤ count5 (toprfAgree toprfPoint ys l) → l = (key, slope)) ∧
    extractUniqueToprfEval Goldilocks.inv toprfPoint ys = some key ∧
    lineAt (key, slope) CommRingOps.zero = key :=
  _root_.Qsag.toprf_2of5_byzantine_unique_decoding key slope ys h

theorem replicated_toprf_any_single_byzantine {F : Type} [LawfulCommRing F] [DecidableEq F]
    (shares : Fin 5 → F) (liar : Fin 5) (responses : Fin 5 → Fin 5 → Option F)
    (h : ∀ p c, p ≠ c → p ≠ liar → responses p c = some (shares c)) :
    reconstructReplicatedToprf2of5 responses = some (sum5 shares) :=
  _root_.Qsag.replicated_toprf_any_single_byzantine shares liar responses h

/-! ### Production hypertree verifier, UC threshold bridge, StepOp256 extraction, TOPRF & crash-durable WAL -/

theorem productionThresholdSignOracle_eq (suite : TweakableHashSuite) (params : PqHashParams)
    (o : ProductionPqHashMpcOracles) (sk : PqSecretKey) (hm : o.MatchesKey suite sk)
    (grindLimit : Nat) (ser : Option PqHashSig → ByteArray) :
    productionThresholdSignOracle suite params o sk.pkSeed grindLimit ser =
      fun req => ser (evalProductionStatelessSign suite params sk req.msg req.optRand grindLimit) :=
  _root_.Qsag.productionThresholdSignOracle_eq suite params o sk hm grindLimit ser

theorem productionForgeryBreak_of_wins {AdvState : Type}
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey) (grindLimit : Nat)
    (hw : params.w = 4 ∨ params.w = 16) (hStateless : params.statefulJorts = false)
    (forgeOut : ExecTranscript AdvState → List UInt8 × PqHashSig) (tr : ExecTranscript AdvState)
    (hWin : productionForgeryWins suite params (derivePublicKey suite params sk) forgeOut tr = true) :
    ProductionTranscriptBreak suite params sk grindLimit forgeOut tr :=
  _root_.Qsag.productionForgeryBreak_of_wins suite params sk grindLimit hw hStateless forgeOut tr hWin

theorem uc_production_threshold_forgery_transfer
    {PK ShareT SessionTape R1St R2St R3St SimTape SimR1 SimR2 SimR3 AdvState : Type}
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (o : ProductionPqHashMpcOracles) (hm : o.MatchesKey suite sk)
    (grindLimit : Nat) (ser : Option PqHashSig → ByteArray)
    (hw : params.w = 4 ∨ params.w = 16) (hStateless : params.statefulJorts = false)
    (proto : InteractiveThresholdProtocol PK ShareT SessionTape R1St R2St R3St)
    (sim : BlackBoxUcSimulator PK SimTape SimR1 SimR2 SimR3)
    (A : UcRushingAdversary AdvState) (Q_s card : Nat)
    (realTapes : Fin card → Nat → SessionTape) (simTapes : Fin card → Nat → SimTape)
    (cl : RealClusterState PK ShareT) (icl : IdealClusterState PK) (advSt : AdvState)
    (forgeOut : ExecTranscript AdvState → List UInt8 × PqHashSig) (eps : Nat × Nat)
    (hUc : ratLe (rationalAcceptDiff card
      (fun ω => (RealProtocolExec proto A Q_s (realTapes ω) cl advSt).2) card
      (fun ω => (IdealFunctionalityExec
        (productionThresholdSignOracle suite params o sk.pkSeed grindLimit ser)
        sim A Q_s (simTapes ω) icl advSt).2)
      (productionForgeryWins suite params (derivePublicKey suite params sk) forgeOut)) eps) :
    let oracle := productionThresholdSignOracle suite params o sk.pkSeed grindLimit ser
    let win := productionForgeryWins suite params (derivePublicKey suite params sk) forgeOut
    let realView := fun ω => (RealProtocolExec proto A Q_s (realTapes ω) cl advSt).2
    let idealView := fun ω => (IdealFunctionalityExec oracle sim A Q_s (simTapes ω) icl advSt).2
    (oracle = fun req => ser (evalProductionStatelessSign suite params sk req.msg req.optRand grindLimit)) ∧
    distAcceptCount card realView win * eps.2 ≤
      distAcceptCount card idealView win * eps.2 + eps.1 * card ∧
    (∀ ω : Fin card, win (idealView ω) = true →
      ProductionTranscriptBreak suite params sk grindLimit forgeOut (idealView ω)) :=
  _root_.Qsag.uc_production_threshold_forgery_transfer suite params sk o hm grindLimit ser
    hw hStateless proto sim A Q_s card realTapes simTapes cl icl advSt forgeOut eps hUc

theorem baggy_multiturn_durable_and_non_equivocating (identity : BaggyLedgerIdentity)
    (ops : List BaggyReleaseOp) :
    let final := baggyReleaseTrace (BaggyReleaseState.init identity) ops
    (∀ r ∈ final.released,
      lookupDurableDigits final.durable r.layer r.tree r.kp = some r.digits) ∧
    (∀ r₁ ∈ final.released, ∀ r₂ ∈ final.released,
      r₁.layer = r₂.layer → r₁.tree = r₂.tree → r₁.kp = r₂.kp → r₁.digits = r₂.digits) :=
  _root_.Qsag.baggy_multiturn_durable_and_non_equivocating identity ops

theorem rss256_recorded_trace_integrity (ops : List Rss256EngineOp) :
    (rss256TraceHardened Rss256EngineState.init ops).1.Checked ∧
    (∀ out ∈ (rss256TraceHardened Rss256EngineState.init ops).2,
      ∃ w : Rss256InlineWave, ∃ a b : Tower128,
        out = rss256GateOutput w.input w.gates ∧
        (out = rss256GateIdeal w.input w.gates ∨ (Rss256Wave.inlineWave w).BadChallenge a b)) :=
  _root_.Qsag.rss256_recorded_trace_integrity ops

open RustDurability in
theorem burnAppend_sync_welds_host_reserve (key identity keyId genesis : RustDurability.Bytes)
    (s : BurnAppendState) (f : BurnJournalFile) (party epoch : Nat)
    (hOpen : openBurnJournal (burnRecordTag key keyId genesis)
      (burnGenesisTag key identity keyId genesis) f = some (s.bodies, s.lastTag))
    (hPending : s.pending = some (burnRecord key keyId genesis s.lastTag party epoch))
    (hVisible : s.visible = s.disk ++ burnRecord key keyId genesis s.lastTag party epoch)
    (hFailed : s.failed = false)
    (hFresh : burnRecordBody party epoch ∉ s.bodies) :
    BurnHostStep (burnRecordTag key keyId genesis) (burnGenesisTag key identity keyId genesis)
      (burnAppendHostOfFile s f)
      (burnAppendHostOfFile (syncBurnAppend s true).1
        (appendBurnRecord (burnRecordTag key keyId genesis) s.lastTag
          (burnRecordBody party epoch) f)) ∧
    BurnHostInv (burnRecordTag key keyId genesis) (burnGenesisTag key identity keyId genesis)
      (burnAppendHostOfFile (syncBurnAppend s true).1
        (appendBurnRecord (burnRecordTag key keyId genesis) s.lastTag
          (burnRecordBody party epoch) f)) :=
  _root_.Qsag.RustDurability.burnAppend_sync_welds_host_reserve key identity keyId genesis s f party epoch
    hOpen hPending hVisible hFailed hFresh

-- END COMPARATOR ROSTER

end Roster

#verify_constructive
  Qsag.Top.rssSharedReleaseMachine_eq_reference
  Qsag.Top.thresholdServiceShared_eq_ideal
  Qsag.Top.thresholdDurableShared_eq_ideal
  Qsag.Top.sepForged_fresh_verifying_signature
  Qsag.Top.distributedCustody_trace_inclusion_and_safety
  Qsag.Top.shamir_custody_network_non_equivocation
  Qsag.Top.rssSharedRelease_preserves_traces
  Qsag.Top.authenticatedCustody_ideal_or_forgery
  Qsag.Top.authenticatedCustody_reachable_safe
  Qsag.Top.authenticatedCustody_unsafe_release_le_violations
  Qsag.Top.authenticatedCustody_unsafe_release_bound
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
  Qsag.Top.elf_to_idealCustody_trace_inclusion
  Qsag.Top.posix_fsync_contract_wal_commit_and_anchor_fence
  Qsag.Top.posixWalHost_wal_commit_and_anchor_fence
  Qsag.Top.seqSessionChannel_contract
  Qsag.Top.authenticated_channel_prevents_custody_replay
  Qsag.Top.seqSessionChannel_prevents_custody_replay
  Qsag.Top.sepCustodyGuarded_projects_to_sepCustody
  Qsag.Top.separatedCustody_forgery_wins_eufCma
  Qsag.Top.separatedCustody_forgery_eufCma_gameBound
  Qsag.Top.distributedShareCustody_dataRefines_or_collision

#tooth_pair Qsag.Top.certCustody_noForgery_no_unsafe_release vs
  Qsag.Top.certCustody_tooth_forged_certificates_unsafe_release
#tooth_pair Qsag.Top.certRun_forgery_submitted vs
  Qsag.Top.certCustody_tooth_wrong_tag_rejected

end Qsag.Top
end
