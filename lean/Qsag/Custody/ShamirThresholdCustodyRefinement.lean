module

public import Qsag.Custody.JortsBeltLatchAndQuorumSwitching
public import Qsag.Custody.SeparatedCustody
public import Qsag.Protocol.Signing.ProdHashReductions
public import Qsag.Protocol.Threshold.ThresholdMpc
public import Qsag.Spec.Refines
public import Qsag.Protocol.Threshold.ParametricThresholdAndUnlinkableQsa
import Qsag.Tactic.AssuranceKit

/-!
# `(t, n)` Shamir Single-Validator Threshold Custody Refinement

## Architectural Scope (`M3` & `M2` Closure)

`SeparatedCustody{Core,Spine,Policy,History,Collision}` and `CompleteMediationBoundary`
model `n` **independently keyed** custodian vaults (`keys : Nat → PqSecretKey`), where
each custodian produces an individual stateful Jorts signature under its own key and a
coordinator checks `t` distinct custodian certificates. By contrast, `BftShamirJorts`
(`QS-B` in `JortsBeltLatchAndQuorumSwitching`) and dynamic Shamir threshold custody
reconstruct a **single enrolled validator public key** `pk` from any `t`-of-`n` Shamir
shares over `GF(2^128)` (`TowerElem 7`), gated by a `2 * q > n + f` pairwise-MAC
`BeltLatch` certificate.

This module bridges `CompleteMediationBoundary` / `SeparatedCustody` to single-validator
`(t, n)` Shamir + `BeltLatch` custody:

1. **Deployment-bound approval bytes (`intentCanonicalPayload`)**: the belt-latch record digest
   and the validator signature message both frame the deployment identifier before the intent, and
   every custodian vault carries `dep.vaultIdentity p` (`runShamirCustodyTrace_identity`), so the
   BDOZ round of a burn is checked against this deployment's commitment. The single-validator
   `QuorumPublicKey` enrolment, Merkle verification and collision extraction
   (`deriveQuorumValidatorPublicKey`, `verifyQuorumJortsSigAt`,
   `verifyQuorumJortsSigAt_extract_reference_or_collision`) are in
   `Qsag.Custody.JortsBeltLatchAndQuorumSwitching`.

2. **Per-custodian refinement to `CompleteMediationBoundary`
   (`shamirCustodianLockstepSim`, `shamirCustodianRefines`)**:
   - Packages each custodian's `BeltLatch`-gated `Custody.Vault` (durable monotone `nextLeaf`,
     `nextRound`, `spent ≤ cap`, BDOZ `Custody.checkRound` approval, `BeltLatch` quorum echo
     certification on `mint`, one-time handle burn on share release) as a `Spec.Machine` that
     refines (`Spec.Refines`) the abstract complete-mediation vault machine across arbitrary mint,
     share-release, forget and crash schedules.

2b. **Deployment well-formedness (`ShamirValidatorDeployment.WellFormed`,
   `WellFormed.quorum_exists`, `WellFormed.corrupt_shares_independent_of_secret`,
   `shamir_custody_wellFormed_epoch_non_equivocation`)**: evaluation points are nonzero and
   pairwise distinct, the sharing degree is `t - 1`, `t ≤ n`, fewer than `t` custodians are
   corrupted and latch quorums intersect honestly. From these, the shares of fewer than `t`
   custodians are unchanged under a bijection of the sharing polynomials that shifts the shared
   value. Lagrange completeness from `WellFormed` is derived below: any duplicate-free list of at
   least `t` custodians reconstructs every shared chain node, and the combiner outputs the
   reference signature. No interpolation identity is assumed.

   Not proved here: a refinement of the whole Shamir network into `Spec.idealCustodyMachine`
   (that refinement is proved for `Qsag.DistCustody.distMachine`), and any liveness of the network.

3. **Multi-Turn `(t, n)` Shamir + `2q > n + f` `BeltLatch` Epoch Non-Equivocation
   (`shamir_custody_epoch_non_equivocation`)**:
   - Across any multi-turn open-world network trace `runShamirCustodyTrace` with
     `maskCard Corrupt ≤ f`, `f < t`, and `2 * q > n + f`:
     * **(a) Per-Honest-Custodian Leaf Uniqueness:** No honest custodian ever releases
       Shamir shares for two distinct `Custody.Intent`s at the same leaf epoch.
     * **(b) Global `(q, t)` Epoch Non-Equivocation:** No two distinct intents `r₁ ≠ r₂`
       at the same leaf epoch (`r₁.leaf = r₂.leaf`) can both obtain `q`-latch certified
       mints and `t`-custodian Shamir share releases unless an explicit
       `PairwiseEchoMacForgery` or `HashCollision256 H` witness is constructively
       extracted (`PSum` / disjunction, `0 Classical.choice`).

4. **Combined Single-Validator Signature Soundness, Quorum Invariance & Production Hypertree Bridge
   (`shamir_custody_combined_sig_verifies_or_collision`,
   `shamir_custody_single_validator_pq_bridge`)**:
   - Any combined signature reconstructed from `t` honest pre-stepped `GF(2^128)²`
     Shamir share openings equals `quorumJortsReferenceSign` (bit-for-bit invariant
     across any two honest `t`-subsets) and verifies under the single enrolled
     `validatorPk`; any share-corrupted combiner output accepted by self-verification +
     Merkle check constructively equals the reference signature or yields a
     `WotsChainCollisionWitness` (`HashCollision256 H`).
   - Connects single-validator `mpcEvalProductionStatefulSign` (`ThresholdMpc`) to
     `ProdCollisionExtraction` and the seed-withheld `Within` challenger games of
     `ProdHashGameReductions`.
-/

public section

namespace Qsag

set_option autoImplicit false
set_option maxRecDepth 4096

/-! ## §1. Single-Validator `QuorumPublicKey` Merkle Enrolment, Verification & Collision Extraction -/

/-- Canonical domain-framed byte payload of a Shamir custody approval: the deployment identifier
    followed by all 5 fields of `Custody.Intent` (`session`, `round`, `leaf`, `spend`, `message`),
    via `encodeMultiFrame` + `leb128` under a byte-literal domain tag. It is the message of the
    belt-latch record and of the validator signature, so both are bound to one deployment. -/
def intentCanonicalPayload (deploymentId : Nat) (r : Custody.Intent) : List UInt8 :=
  encodeMultiFrame
    [[0x51, 0x53, 0x41, 0x47, 0x2e, 0x53, 0x48, 0x41, 0x4d, 0x49, 0x52],
     leb128 deploymentId,
     leb128 r.session, leb128 r.round, leb128 r.leaf, leb128 r.spend, r.message]

theorem intentCanonicalPayload_injective {d₁ d₂ : Nat} {r₁ r₂ : Custody.Intent}
    (h : intentCanonicalPayload d₁ r₁ = intentCanonicalPayload d₂ r₂) : d₁ = d₂ ∧ r₁ = r₂ := by
  have hf := encodeMultiFrame_injective h
  simp only [List.cons.injEq] at hf
  have hLeb : ∀ {a b : Nat}, leb128 a = leb128 b → a = b := fun {a b} hEq =>
    (leb128_prefix_inj (show leb128 a ++ [] = leb128 b ++ [] by simpa using hEq)).1
  have hd := hLeb hf.2.1
  have hs := hLeb hf.2.2.1
  have hr := hLeb hf.2.2.2.1
  have hl := hLeb hf.2.2.2.2.1
  have hv := hLeb hf.2.2.2.2.2.1
  have hm := hf.2.2.2.2.2.2.1
  refine ⟨hd, ?_⟩
  cases r₁; cases r₂
  simp_all only

/-! ## §2. Per-Custodian Refinement to `CompleteMediationBoundary` -/

/-- Pre-stepped `GF(2^128)²` (`TowerElem 7 × TowerElem 7`) Shamir share opening released by a
    single custodian `party : Fin n` upon consuming its one-time `Custody.Vault.active` handle. -/
structure ShamirCustodianShareOpening (n L : Nat) where
  party : Fin n
  intent : Custody.Intent
  epoch : UInt64
  counter : UInt32
  evalPoint : TowerElem 7
  chainShares : Fin L → Option (TowerElem 7 × TowerElem 7)

/-- Compute custodian `party`'s pre-stepped `GF(2^128)²` Shamir share opening at `evalPt`. -/
@[expose] def computeShamirCustodianOpening {n L d : Nat}
    (H : List UInt8 → Digest256) (masterSeed : Digest256)
    (polyTape : UInt64 → PreSteppedDigest256ShamirTape d L)
    (evalPt : TowerElem 7) (party : Fin n)
    (r : Custody.Intent) (counter : UInt32)
    (digits : Fin L → Fin 4) : ShamirCustodianShareOpening n L :=
  let gLeaf := UInt64.ofNat r.leaf
  let pkSeed := quorumStagePkSeed H masterSeed
  { party := party
    intent := r
    epoch := gLeaf
    counter := counter
    evalPoint := evalPt
    chainShares := fun i =>
      if hStep : (digits i).val < 3 then
        let k : Fin 3 := ⟨(digits i).val, hStep⟩
        let sk₀ := quorumStageChainSk H masterSeed gLeaf (UInt32.ofNat i.1)
        let trueNode := wotsChainIter (quorumChainStep H pkSeed gLeaf) i.1 0 (digits i).val sk₀
        let (lo, hi) := splitDigest256Tower128 trueNode
        some (RoundPoly.evalCoeffs (lo :: (polyTape gLeaf i k).1.1) evalPt,
              RoundPoly.evalCoeffs (hi :: (polyTape gLeaf i k).2.1) evalPt)
      else
        none }

/-- One-time complete-mediation share release on `Custody.Vault`:
    enforces exact anchor continuity, poisons on mismatch, and atomically burns `v.active = some r`
    into `r :: v.attempted` before emitting `ShamirCustodianShareOpening` (matching
    `Custody.release`'s vault transition in `CompleteMediationBoundary`). -/
def releaseShamirShareFromVault {n L d : Nat}
    (H : List UInt8 → Digest256) (masterSeed : Digest256)
    (polyTape : UInt64 → PreSteppedDigest256ShamirTape d L)
    (evalPt : TowerElem 7) (party : Fin n)
    (anchor : Nat) (v : Custody.Vault)
    (r : Custody.Intent) (counter : UInt32) (digits : Fin L → Fin 4) :
    Custody.Vault × Option (ShamirCustodianShareOpening n L) :=
  if v.poisoned || decide (v.durable.anchor ≠ anchor) then
    ({ v with poisoned := true, active := none }, none)
  else if v.active = some r then
    ({ v with active := none, attempted := r :: v.attempted },
     some (computeShamirCustodianOpening H masterSeed polyTape evalPt party r counter digits))
  else
    (v, none)

theorem releaseShamirShareFromVault_safe {n L d : Nat}
    (H : List UInt8 → Digest256) (masterSeed : Digest256)
    (polyTape : UInt64 → PreSteppedDigest256ShamirTape d L)
    (evalPt : TowerElem 7) (party : Fin n)
    (policy : Custody.RoundPolicy) (cap anchor : Nat) (v : Custody.Vault)
    (r : Custody.Intent) (counter : UInt32) (digits : Fin L → Fin 4)
    (hSafe : Custody.Safe policy cap v) :
    Custody.Safe policy cap
      (releaseShamirShareFromVault H masterSeed polyTape evalPt party anchor v r counter digits).1 := by
  unfold releaseShamirShareFromVault
  split
  · exact ⟨hSafe.budget, hSafe.accounting, hSafe.past, hSafe.uniqueLeaf, hSafe.approved,
      (fun _ he => by cases he), hSafe.attemptedBurned, (fun _ he => by cases he),
      hSafe.attemptedNodup⟩
  · split
    next ha =>
      refine ⟨hSafe.budget, hSafe.accounting, hSafe.past, hSafe.uniqueLeaf, hSafe.approved,
        (fun _ he => by cases he), ?_, (fun _ he => by cases he), ?_⟩
      · intro s hs
        rcases List.mem_cons.mp hs with hs | hs
        · subst s; exact hSafe.activeBurned r ha
        · exact hSafe.attemptedBurned s hs
      · exact List.nodup_cons.mpr ⟨hSafe.activeFresh r ha, hSafe.attemptedNodup⟩
    next => exact hSafe

theorem releaseShamirShareFromVault_replay_rejected {n L d : Nat}
    (H : List UInt8 → Digest256) (masterSeed : Digest256)
    (polyTape : UInt64 → PreSteppedDigest256ShamirTape d L)
    (evalPt : TowerElem 7) (party : Fin n)
    (anchor : Nat) (v : Custody.Vault)
    (r : Custody.Intent) (counter₁ counter₂ : UInt32) (digits₁ digits₂ : Fin L → Fin 4)
    (op : ShamirCustodianShareOpening n L)
    (hRel : (releaseShamirShareFromVault H masterSeed polyTape evalPt party anchor v r
      counter₁ digits₁).2 = some op) :
    (releaseShamirShareFromVault H masterSeed polyTape evalPt party anchor
      (releaseShamirShareFromVault H masterSeed polyTape evalPt party anchor v r counter₁ digits₁).1
      r counter₂ digits₂).2 = none := by
  generalize hV1 : (releaseShamirShareFromVault H masterSeed polyTape evalPt party anchor v r
    counter₁ digits₁) = res₁ at hRel ⊢
  have hActNone : res₁.1.active = none := by
    dsimp only [releaseShamirShareFromVault] at hV1
    split at hV1
    · rw [← hV1] at hRel; cases hRel
    · split at hV1
      · rw [← hV1]
      · rw [← hV1] at hRel; cases hRel
  unfold releaseShamirShareFromVault
  split
  · rfl
  · have hNotSome : ¬(res₁.1.active = some r) := by rw [hActNone]; intro h; cases h
    simp only [hNotSome, ↓reduceIte]

/-- Certified `BeltLatch` mint check binding `BeltLatchRecord` to `Custody.Burn`:
    requires `b.intent.leaf < 2 ^ 64`, `rec.epoch = UInt64.ofNat b.intent.leaf`,
    `rec.msgDigest = H (intentCanonicalPayload deploymentId b.intent)`, unpoisoned `nodeSt.inFlight = some rec`,
    and a valid `q`-of-`n` pairwise-MAC `BeltEcho` certificate `verifyQuorumEchoCertificate`. -/
def checkLatchCertifiedBurn {n : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (macKeys : Fin n → Fin n → Digest256)
    (q deploymentId : Nat) (verifier : Fin n) (nodeSt : BeltLatchNodeState)
    (Q : CustodiansMask n) (rec : BeltLatchRecord)
    (echoes : List (AuthenticatedBeltEcho n)) (b : Custody.Burn) : Bool :=
  !nodeSt.walPoisoned &&
  decide (nodeSt.inFlight = some rec) &&
  decide (b.intent.leaf < 2 ^ 64) &&
  decide (rec.epoch = UInt64.ofNat b.intent.leaf) &&
  decide (rec.msgDigest = H (intentCanonicalPayload deploymentId b.intent)) &&
  verifyQuorumEchoCertificate H MAC macKeys q verifier Q rec echoes

/-- Per-custodian input alphabet of the refinement between concrete Shamir-custodian state and
    abstract `CompleteMediationBoundary` vault state. -/
inductive ShamirVaultMachineInput (n L : Nat) where
  | certifiedMint (anchor : Nat) (Q : CustodiansMask n) (rec : BeltLatchRecord)
      (echoes : List (AuthenticatedBeltEcho n)) (b : Custody.Burn)
  | releaseShare (anchor : Nat) (r : Custody.Intent) (counter : UInt32) (digits : Fin L → Fin 4)
  | forget
  | crash

/-- Per-custodian observable output event. -/
inductive ShamirVaultMachineOutput (n L : Nat) where
  | minted (intent : Custody.Intent)
  | shareReleased (opening : ShamirCustodianShareOpening n L)
  | wiped

/-- Concrete Shamir custodian state pairing local `BeltLatchNodeState` with `Custody.Vault`. -/
structure ShamirCustodianLocalState where
  latchNode : BeltLatchNodeState
  vault : Custody.Vault

/-- Step transition of the concrete Shamir custodian. A rejected input may still poison the
    vault. -/
def shamirCustodianStep {n L d : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (macKeys : Fin n → Fin n → Digest256)
    (masterSeed : Digest256)
    (polyTape : UInt64 → PreSteppedDigest256ShamirTape d L)
    (evalPt : TowerElem 7) (party : Fin n)
    (q deploymentId : Nat) (policy : Custody.RoundPolicy) (cap : Nat) :
    ShamirCustodianLocalState → ShamirVaultMachineInput n L →
      CustodyStepOutcome ShamirCustodianLocalState (ShamirVaultMachineOutput n L) Unit :=
  fun s inp =>
    match inp with
    | .certifiedMint anchor Q rec echoes b =>
      if checkLatchCertifiedBurn H MAC macKeys q deploymentId party s.latchNode Q rec echoes b then
        if s.vault.poisoned || decide (s.vault.durable.anchor ≠ anchor) then
          .rejected { s with vault := { s.vault with poisoned := true, active := none } } ()
        else if Custody.mintGuard policy cap s.vault b then
          let v' := Custody.mint policy cap anchor s.vault b
          .accepted { s with vault := v' } (.minted b.intent)
        else
          .rejected s ()
      else
        .rejected s ()
    | .releaseShare anchor r counter digits =>
      let res := releaseShamirShareFromVault H masterSeed polyTape evalPt party anchor
        s.vault r counter digits
      match res.2 with
      | some op => .accepted { s with vault := res.1 } (.shareReleased op)
      | none => .rejected { s with vault := res.1 } ()
    | .forget =>
      .accepted { s with vault := Custody.forget s.vault } .wiped
    | .crash =>
      .accepted
        { latchNode := beltLatchCrashAndRecover s.latchNode
          vault := Custody.forget s.vault } .wiped

/-- The concrete Shamir custodian as a `Spec.Machine`; it may start in any state whose vault is
    `Custody.Safe`. -/
def shamirCustodianMachine {n L d : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (macKeys : Fin n → Fin n → Digest256)
    (masterSeed : Digest256)
    (polyTape : UInt64 → PreSteppedDigest256ShamirTape d L)
    (evalPt : TowerElem 7) (party : Fin n)
    (q deploymentId : Nat) (policy : Custody.RoundPolicy) (cap : Nat) :
    Spec.Machine ShamirCustodianLocalState
      (ShamirVaultMachineInput n L) (ShamirVaultMachineOutput n L) :=
  custodyStepMachine (fun s => Custody.Safe policy cap s.vault)
    (shamirCustodianStep H MAC macKeys masterSeed polyTape evalPt party q deploymentId policy cap)

/-- Step transition of the abstract `CompleteMediationBoundary` machine over `ShamirCustodianLocalState`'s
    projected `(latchNode, vault)` specification, delegating durable mediation directly to
    `Custody.mint`, `Custody.forget`, and one-time handle consumption. -/
def abstractMediationVaultStep {n L d : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (macKeys : Fin n → Fin n → Digest256)
    (masterSeed : Digest256)
    (polyTape : UInt64 → PreSteppedDigest256ShamirTape d L)
    (evalPt : TowerElem 7) (party : Fin n)
    (q deploymentId : Nat) (policy : Custody.RoundPolicy) (cap : Nat) :
    BeltLatchNodeState × Custody.Vault → ShamirVaultMachineInput n L →
      CustodyStepOutcome (BeltLatchNodeState × Custody.Vault) (ShamirVaultMachineOutput n L) Unit :=
  fun sv inp =>
    match inp with
    | .certifiedMint anchor Q rec echoes b =>
      if checkLatchCertifiedBurn H MAC macKeys q deploymentId party sv.1 Q rec echoes b then
        if sv.2.poisoned || decide (sv.2.durable.anchor ≠ anchor) then
          .rejected (sv.1, Custody.mint policy cap anchor sv.2 b) ()
        else if Custody.mintGuard policy cap sv.2 b then
          .accepted (sv.1, Custody.mint policy cap anchor sv.2 b) (.minted b.intent)
        else
          .rejected (sv.1, Custody.mint policy cap anchor sv.2 b) ()
      else
        .rejected sv ()
    | .releaseShare anchor r counter digits =>
      let res := releaseShamirShareFromVault H masterSeed polyTape evalPt party anchor
        sv.2 r counter digits
      match res.2 with
      | some op => .accepted (sv.1, res.1) (.shareReleased op)
      | none => .rejected (sv.1, res.1) ()
    | .forget =>
      .accepted (sv.1, Custody.forget sv.2) .wiped
    | .crash =>
      .accepted (beltLatchCrashAndRecover sv.1, Custody.forget sv.2) .wiped

/-- The abstract mediation-vault machine as a `Spec.Machine`, starting in any `Custody.Safe`
    vault. -/
def abstractMediationVaultMachine {n L d : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (macKeys : Fin n → Fin n → Digest256)
    (masterSeed : Digest256)
    (polyTape : UInt64 → PreSteppedDigest256ShamirTape d L)
    (evalPt : TowerElem 7) (party : Fin n)
    (q deploymentId : Nat) (policy : Custody.RoundPolicy) (cap : Nat) :
    Spec.Machine (BeltLatchNodeState × Custody.Vault)
      (ShamirVaultMachineInput n L) (ShamirVaultMachineOutput n L) :=
  custodyStepMachine (fun sv => Custody.Safe policy cap sv.2)
    (abstractMediationVaultStep H MAC macKeys masterSeed polyTape evalPt party q deploymentId
      policy cap)

/-- `Spec.LockstepSim` from `shamirCustodianMachine` to `abstractMediationVaultMachine`,
    preserving `Custody.Safe policy cap s.vault` on every accepted and rejected transition. -/
def shamirCustodianLockstepSim {n L d : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (macKeys : Fin n → Fin n → Digest256)
    (masterSeed : Digest256)
    (polyTape : UInt64 → PreSteppedDigest256ShamirTape d L)
    (evalPt : TowerElem 7) (party : Fin n)
    (q deploymentId : Nat) (policy : Custody.RoundPolicy) (cap : Nat) :
    Spec.LockstepSim
      (shamirCustodianMachine H MAC macKeys masterSeed polyTape evalPt party q deploymentId policy cap)
      (abstractMediationVaultMachine H MAC macKeys masterSeed polyTape evalPt party q deploymentId policy cap) where
  Inv s := Custody.Safe policy cap s.vault
  abs s := (s.latchNode, s.vault)
  init_inv h := ⟨h, h⟩
  step_eq {s} inp hInv := by
    cases inp with
    | certifiedMint anchor Q rec echoes b =>
      unfold shamirCustodianMachine abstractMediationVaultMachine custodyStepMachine
        custodyAcceptedStep custodyNextState shamirCustodianStep abstractMediationVaultStep
      dsimp only
      by_cases hCert : checkLatchCertifiedBurn H MAC macKeys q deploymentId party s.latchNode Q rec echoes b = true
      · simp only [hCert, ↓reduceIte]
        by_cases hPois : (s.vault.poisoned || decide (s.vault.durable.anchor ≠ anchor)) = true
        · simp only [hPois, ↓reduceIte]
          have hMintPois : Custody.mint policy cap anchor s.vault b =
              { s.vault with poisoned := true, active := none } := by
            rw [Custody.mint_eq]; simp only [hPois, ↓reduceIte]
          rw [hMintPois]
          exact ⟨hMintPois ▸ Custody.mint_safe policy cap anchor s.vault b hInv, trivial, rfl⟩
        · have hPoisF : (s.vault.poisoned || decide (s.vault.durable.anchor ≠ anchor)) = false :=
            Bool.not_eq_true _ |>.mp hPois
          simp only [hPoisF, Bool.false_eq_true, ↓reduceIte]
          by_cases hGuard : Custody.mintGuard policy cap s.vault b = true
          · simp only [hGuard, ↓reduceIte]
            exact ⟨Custody.mint_safe policy cap anchor s.vault b hInv, trivial⟩
          · have hGuardF : Custody.mintGuard policy cap s.vault b = false :=
              Bool.not_eq_true _ |>.mp hGuard
            simp only [hGuardF, Bool.false_eq_true, ↓reduceIte]
            have hMintNoop : Custody.mint policy cap anchor s.vault b = s.vault := by
              rw [Custody.mint_eq]
              simp only [hPoisF, hGuardF, Bool.false_eq_true, ↓reduceIte]
            rw [hMintNoop]
            exact ⟨hInv, trivial, rfl⟩
      · have hCertF : checkLatchCertifiedBurn H MAC macKeys q deploymentId party s.latchNode Q rec echoes b = false :=
          Bool.not_eq_true _ |>.mp hCert
        simp only [hCertF, Bool.false_eq_true, ↓reduceIte]
        exact ⟨hInv, trivial, trivial⟩
    | releaseShare anchor r counter digits =>
      unfold shamirCustodianMachine abstractMediationVaultMachine custodyStepMachine
        custodyAcceptedStep custodyNextState shamirCustodianStep abstractMediationVaultStep
      dsimp only
      have hRelSafe := releaseShamirShareFromVault_safe H masterSeed polyTape evalPt party
        policy cap anchor s.vault r counter digits hInv
      cases hOut : (releaseShamirShareFromVault H masterSeed polyTape evalPt party anchor
          s.vault r counter digits).2 with
      | some op =>
        dsimp only
        exact ⟨hRelSafe, rfl⟩
      | none =>
        dsimp only
        exact ⟨hRelSafe, rfl, rfl⟩
    | forget =>
      unfold shamirCustodianMachine abstractMediationVaultMachine custodyStepMachine
        custodyAcceptedStep custodyNextState shamirCustodianStep abstractMediationVaultStep
      exact ⟨Custody.forget_safe policy cap s.vault hInv, rfl⟩
    | crash =>
      unfold shamirCustodianMachine abstractMediationVaultMachine custodyStepMachine
        custodyAcceptedStep custodyNextState shamirCustodianStep abstractMediationVaultStep
      exact ⟨Custody.forget_safe policy cap s.vault hInv, rfl⟩

/-- Each Shamir custodian refines the abstract mediation vault (`Spec.Refines`). -/
def shamirCustodianRefines {n L d : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (macKeys : Fin n → Fin n → Digest256)
    (masterSeed : Digest256)
    (polyTape : UInt64 → PreSteppedDigest256ShamirTape d L)
    (evalPt : TowerElem 7) (party : Fin n)
    (q deploymentId : Nat) (policy : Custody.RoundPolicy) (cap : Nat) :
    Spec.Refines
      (shamirCustodianMachine H MAC macKeys masterSeed polyTape evalPt party q deploymentId
        policy cap)
      (abstractMediationVaultMachine H MAC macKeys masterSeed polyTape evalPt party q deploymentId
        policy cap) :=
  (shamirCustodianLockstepSim H MAC macKeys masterSeed polyTape evalPt party q deploymentId
    policy cap).toRefines

/-! ## §3. Multi-Turn `(t, n)` Shamir + `2q > n + f` `BeltLatch` Network & Epoch Non-Equivocation -/

/-- Certified latch-mint provenance entry recorded when an honest custodian mints `intent` in its
    `Custody.Vault` after verifying a `q`-of-`n` `BeltLatch` echo certificate. -/
structure CertifiedVaultMintRecord (n : Nat) where
  quorum : CustodiansMask n
  latchRec : BeltLatchRecord
  echoes : List (AuthenticatedBeltEcho n)
  intent : Custody.Intent

/-- Online `(t, n)` Lagrange Shamir combiner producing a candidate `QuorumJortsSig` from
    `submitted : SubmittedDigest256ShamirShares L` and checking BOTH MAC-free WOTS+C endpoint
    self-verification (`preSteppedDigest256ReconstructAndSelfVerify`) AND full single-validator
    Merkle root verification (`verifyQuorumJortsSigAt`). -/
def combineAndVerifyShamirValidatorSig (L targetSum deploymentId : Nat)
    (H : List UInt8 → Digest256) (validatorPk : QuorumPublicKey)
    (digitsOf : Digest256 → List (Fin 4))
    (lambdas : List (TowerElem 7))
    (r : Custody.Intent) (counter : UInt32)
    (submitted : SubmittedDigest256ShamirShares L)
    (authPath : List Digest256) : Option QuorumJortsSig :=
  let gLeaf := UInt64.ofNat r.leaf
  let msg := intentCanonicalPayload deploymentId r
  let msgHash := quorumMessageHash H validatorPk gLeaf msg
  let dig := quorumCounterDigest H msgHash counter
  let digitsList := digitsOf dig
  if digitsList.length = L then
    let digitsFn : Fin L → Fin 4 := fun i => digitsList.getD i.1 ⟨0, by decide⟩
    let chainEndsFromPath := fun i : Fin L =>
      -- Reference chain endpoint check is performed by verifyQuorumJortsSigAt against validatorPk.root;
      -- here we reconstruct candidate nodes via Lagrange ringDot over GF(2^128)²:
      if (digitsFn i).val < 3 then
        joinTower128Digest256
          (ringDot lambdas (submitted i).1, ringDot lambdas (submitted i).2)
      else
        0#256
    let candNodes := (List.finRange L).map chainEndsFromPath
    let candSig : QuorumJortsSig :=
      { leaf := gLeaf, counter := counter, nodes := candNodes, authPath := authPath }
    if verifyQuorumJortsSigAt L targetSum H validatorPk digitsOf msg candSig then
      some candSig
    else
      none
  else
    none

/-- Full MAC-free self-verifying + Merkle-verifying `(t, n)` Shamir combiner when the leaf's
    public chain endpoints `leafChainPk : Fin L → Digest256` are also supplied (so chains with
    digit `d_i = 3` require `0` share transmissions!). -/
def combinePreSteppedShamirValidatorSig (L targetSum deploymentId : Nat)
    (H : List UInt8 → Digest256) (validatorPk : QuorumPublicKey)
    (digitsOf : Digest256 → List (Fin 4))
    (leafChainPk : Fin L → Digest256)
    (lambdas : List (TowerElem 7))
    (r : Custody.Intent) (counter : UInt32)
    (submitted : SubmittedDigest256ShamirShares L)
    (authPath : List Digest256) : Option QuorumJortsSig :=
  let gLeaf := UInt64.ofNat r.leaf
  let msg := intentCanonicalPayload deploymentId r
  let msgHash := quorumMessageHash H validatorPk gLeaf msg
  let dig := quorumCounterDigest H msgHash counter
  let digitsList := digitsOf dig
  let digitsFn : Fin L → Fin 4 := fun i => digitsList.getD i.1 ⟨0, by decide⟩
  match preSteppedDigest256ReconstructAndSelfVerify
      (quorumChainStep H validatorPk.pkSeed gLeaf) leafChainPk lambdas digitsFn submitted with
  | none => none
  | some candFn =>
    let candSig : QuorumJortsSig :=
      { leaf := gLeaf
        counter := counter
        nodes := (List.finRange L).map candFn
        authPath := authPath }
    if verifyQuorumJortsSigAt L targetSum H validatorPk digitsOf msg candSig then
      some candSig
    else
      none

/-- Distributed multi-turn `(t, n)` Shamir + `BeltLatch` custody network state. -/
structure ShamirCustodyNetworkState (n L : Nat) where
  beltTrace : List (BeltNetworkTurn n)
  beltNet : BeltLatchNetworkState n
  vaults : Fin n → Custody.Vault
  mintCerts : Fin n → List (CertifiedVaultMintRecord n)
  honestShareReleases : List (ShamirCustodianShareOpening n L)
  combinedSignatures : List (Custody.Intent × QuorumJortsSig)

/-- Open-world multi-turn schedule alphabet for `(t, n)` Shamir threshold custody. -/
inductive ShamirCustodyTurn (n L : Nat) where
  | belt (turn : BeltNetworkTurn n)
  | certifiedMint (p : Fin n) (anchor : Nat) (Q : CustodiansMask n)
      (rec : BeltLatchRecord) (echoes : List (AuthenticatedBeltEcho n)) (b : Custody.Burn)
  | releaseShare (p : Fin n) (anchor : Nat) (r : Custody.Intent) (counter : UInt32)
  | combineSig (leafChainPk : Fin L → Digest256) (lambdas : List (TowerElem 7))
      (r : Custody.Intent) (counter : UInt32)
      (submitted : SubmittedDigest256ShamirShares L) (authPath : List Digest256)
  | forgetVault (p : Fin n)
  | crashAndRecoverCustodian (p : Fin n)

/-- Static deployment parameters for a single-validator `(t, n)` Shamir custody cluster. -/
structure ShamirValidatorDeployment (n L d : Nat) where
  deploymentId : Nat
  H : List UInt8 → Digest256
  MAC : Digest256 → List UInt8 → Digest256
  macKeys : Fin n → Fin n → Digest256
  Corrupt : CustodiansMask n
  t : Nat
  f : Nat
  q : Nat
  height : Nat
  maxWindow : Nat
  targetSum : Nat
  masterSeed : Digest256
  digitsOf : Digest256 → List (Fin 4)
  evalPts : Fin n → TowerElem 7
  polyTape : UInt64 → PreSteppedDigest256ShamirTape d L
  policies : Fin n → Custody.RoundPolicy
  caps : Fin n → Nat

/-- Derived single-validator `QuorumPublicKey` for deployment `dep`. -/
def ShamirValidatorDeployment.validatorPk {n L d : Nat}
    (dep : ShamirValidatorDeployment n L d) : QuorumPublicKey :=
  deriveQuorumValidatorPublicKey L dep.height dep.H dep.masterSeed

/-- Vault identity of custodian `p`: this deployment, the custodian's index, and the single
    enrolled validator key (seed and root) as the key identity. -/
def ShamirValidatorDeployment.vaultIdentity {n L d : Nat}
    (dep : ShamirValidatorDeployment n L d) (p : Fin n) : Custody.VaultIdentity :=
  ⟨dep.deploymentId, p.val,
    encodeDigest256 dep.validatorPk.pkSeed ++ encodeDigest256 dep.validatorPk.root⟩

/-- Initial `(t, n)` Shamir + `BeltLatch` custody network state at epoch `0`: every vault is empty
    and carries the identity of its custodian in this deployment. -/
@[expose] def ShamirCustodyNetworkState.init {n L d : Nat} (dep : ShamirValidatorDeployment n L d) :
    ShamirCustodyNetworkState n L where
  beltTrace := []
  beltNet := BeltLatchNetworkState.init n dep.height dep.maxWindow
  vaults := fun p => Custody.initial (dep.vaultIdentity p)
  mintCerts := fun _ => []
  honestShareReleases := []
  combinedSignatures := []

/-- Execute one open-world network transition on `ShamirCustodyNetworkState n L`. -/
@[expose] def stepShamirCustody {n L d : Nat}
    (dep : ShamirValidatorDeployment n L d)
    (st : ShamirCustodyNetworkState n L)
    (turn : ShamirCustodyTurn n L) : ShamirCustodyNetworkState n L :=
  match turn with
  | .belt bTurn =>
    { st with
      beltTrace := st.beltTrace ++ [bTurn]
      beltNet := stepBeltNetwork dep.H dep.MAC dep.macKeys dep.Corrupt dep.q st.beltNet bTurn }
  | .certifiedMint p anchor Q rec echoes b =>
    if dep.Corrupt.mem p then st
    else if checkLatchCertifiedBurn dep.H dep.MAC dep.macKeys dep.q dep.deploymentId p
        (st.beltNet.nodes p) Q rec echoes b then
      let vOld := st.vaults p
      let vNew := Custody.mint (dep.policies p) (dep.caps p) anchor vOld b
      if !vOld.poisoned && decide (vOld.durable.anchor = anchor) &&
          Custody.mintGuard (dep.policies p) (dep.caps p) vOld b then
        { st with
          vaults := fun i => if i = p then vNew else st.vaults i
          mintCerts := fun i =>
            if i = p then ⟨Q, rec, echoes, b.intent⟩ :: st.mintCerts p else st.mintCerts i }
      else
        { st with vaults := fun i => if i = p then vNew else st.vaults i }
    else
      st
  | .releaseShare p anchor r counter =>
    if dep.Corrupt.mem p then st
    else
      let pk := dep.validatorPk
      let gLeaf := UInt64.ofNat r.leaf
      let msg := intentCanonicalPayload dep.deploymentId r
      let dig := quorumCounterDigest dep.H (quorumMessageHash dep.H pk gLeaf msg) counter
      let digitsList := dep.digitsOf dig
      let digitsFn : Fin L → Fin 4 := fun i => digitsList.getD i.1 ⟨0, by decide⟩
      let res := releaseShamirShareFromVault dep.H dep.masterSeed dep.polyTape
        (dep.evalPts p) p anchor (st.vaults p) r counter digitsFn
      match res.2 with
      | some op =>
        { st with
          vaults := fun i => if i = p then res.1 else st.vaults i
          honestShareReleases := op :: st.honestShareReleases }
      | none =>
        { st with vaults := fun i => if i = p then res.1 else st.vaults i }
  | .combineSig leafChainPk lambdas r counter submitted authPath =>
    match combinePreSteppedShamirValidatorSig L dep.targetSum dep.deploymentId dep.H dep.validatorPk
        dep.digitsOf leafChainPk lambdas r counter submitted authPath with
    | none => st
    | some sig => { st with combinedSignatures := (r, sig) :: st.combinedSignatures }
  | .forgetVault p =>
    if dep.Corrupt.mem p then st
    else
      { st with vaults := fun i => if i = p then Custody.forget (st.vaults p) else st.vaults i }
  | .crashAndRecoverCustodian p =>
    { st with
      beltTrace := st.beltTrace ++ [.crashAndRecoverNode p]
      beltNet := stepBeltNetwork dep.H dep.MAC dep.macKeys dep.Corrupt dep.q
        st.beltNet (.crashAndRecoverNode p)
      vaults := fun i =>
        if i = p && !dep.Corrupt.mem p then Custody.forget (st.vaults p) else st.vaults i }

/-- Execute a multi-turn open-world schedule `List (ShamirCustodyTurn n L)`. -/
@[expose] def runShamirCustodyTrace {n L d : Nat}
    (dep : ShamirValidatorDeployment n L d)
    (st : ShamirCustodyNetworkState n L) :
    List (ShamirCustodyTurn n L) → ShamirCustodyNetworkState n L
  | [] => st
  | turn :: rest => runShamirCustodyTrace dep (stepShamirCustody dep st turn) rest

/-- Joint multi-turn safety invariant across `BeltLatchNetworkState`, all `n` custodian
    `Custody.Vault`s, honest Shamir share releases, and combined validator signatures. -/
structure ShamirCustodyNetworkInv {n L d : Nat}
    (dep : ShamirValidatorDeployment n L d)
    (st : ShamirCustodyNetworkState n L) : Prop where
  beltSync :
    st.beltNet = runBeltNetworkTrace dep.H dep.MAC dep.macKeys dep.Corrupt dep.q
      (BeltLatchNetworkState.init n dep.height dep.maxWindow) st.beltTrace
  vaultSafe :
    ∀ p : Fin n, Custody.Safe (dep.policies p) (dep.caps p) (st.vaults p)
  burnedCertified :
    ∀ (p : Fin n), dep.Corrupt.mem p = false →
      ∀ b ∈ (st.vaults p).durable.burned,
        ∃ mc ∈ st.mintCerts p,
          mc.intent = b.intent ∧
          b.intent.leaf < 2 ^ 64 ∧
          mc.latchRec.epoch = UInt64.ofNat b.intent.leaf ∧
          mc.latchRec.msgDigest = dep.H (intentCanonicalPayload dep.deploymentId b.intent) ∧
          verifyQuorumEchoCertificate dep.H dep.MAC dep.macKeys dep.q p
            mc.quorum mc.latchRec mc.echoes = true
  shareReleaseProvenance :
    ∀ op ∈ st.honestShareReleases,
      dep.Corrupt.mem op.party = false ∧
      op.intent ∈ (st.vaults op.party).attempted ∧
      op.epoch = UInt64.ofNat op.intent.leaf
  shareReleasesNodupPartyIntent :
    (st.honestShareReleases.map (fun op => (op.party, op.intent))).Nodup
  combinedVerified :
    ∀ entry ∈ st.combinedSignatures,
      entry.2.leaf = UInt64.ofNat entry.1.leaf ∧
      verifyQuorumJortsSigAt L dep.targetSum dep.H dep.validatorPk dep.digitsOf
        (intentCanonicalPayload dep.deploymentId entry.1) entry.2 = true

theorem stepShamirCustody_preserves_inv {n L d : Nat}
    (dep : ShamirValidatorDeployment n L d)
    (st : ShamirCustodyNetworkState n L)
    (turn : ShamirCustodyTurn n L)
    (hInv : ShamirCustodyNetworkInv dep st) :
    ShamirCustodyNetworkInv dep (stepShamirCustody dep st turn) := by
  cases turn with
  | belt bTurn =>
    unfold stepShamirCustody
    refine ⟨?_, hInv.vaultSafe, hInv.burnedCertified, hInv.shareReleaseProvenance,
      hInv.shareReleasesNodupPartyIntent, hInv.combinedVerified⟩
    rw [runBeltNetworkTrace_append_singleton, ← hInv.beltSync]
  | certifiedMint p anchor Q rec echoes b =>
    unfold stepShamirCustody
    by_cases hCorr : dep.Corrupt.mem p = true
    · simp only [hCorr, ↓reduceIte]; exact hInv
    · have hHon : dep.Corrupt.mem p = false := Bool.not_eq_true _ |>.mp hCorr
      simp only [hHon, Bool.false_eq_true, ↓reduceIte]
      by_cases hLatch : checkLatchCertifiedBurn dep.H dep.MAC dep.macKeys dep.q dep.deploymentId p
          (st.beltNet.nodes p) Q rec echoes b = true
      · simp only [hLatch, ↓reduceIte]
        have hCertUnpack :
            b.intent.leaf < 2 ^ 64 ∧
            rec.epoch = UInt64.ofNat b.intent.leaf ∧
            rec.msgDigest = dep.H (intentCanonicalPayload dep.deploymentId b.intent) ∧
            verifyQuorumEchoCertificate dep.H dep.MAC dep.macKeys dep.q p Q rec echoes = true := by
          unfold checkLatchCertifiedBurn at hLatch
          rcases Bool.and_eq_true_iff.mp hLatch with ⟨h15, hVerQ⟩
          rcases Bool.and_eq_true_iff.mp h15 with ⟨h14, hMd⟩
          rcases Bool.and_eq_true_iff.mp h14 with ⟨h13, hEp⟩
          rcases Bool.and_eq_true_iff.mp h13 with ⟨_, hLf⟩
          exact ⟨of_decide_eq_true hLf, of_decide_eq_true hEp, of_decide_eq_true hMd, hVerQ⟩
        by_cases hGrant : (!((st.vaults p).poisoned) &&
            decide ((st.vaults p).durable.anchor = anchor) &&
            Custody.mintGuard (dep.policies p) (dep.caps p) (st.vaults p) b) = true
        · simp only [hGrant, ↓reduceIte]
          refine ⟨hInv.beltSync, ?_, ?_, ?_, hInv.shareReleasesNodupPartyIntent,
            hInv.combinedVerified⟩
          · intro i
            by_cases hip : i = p
            · subst hip; simp only [↓reduceIte]
              exact Custody.mint_safe _ _ anchor _ b (hInv.vaultSafe i)
            · simp only [hip, ↓reduceIte]; exact hInv.vaultSafe i
          · intro i hiHon b' hb'
            by_cases hip : i = p
            · subst hip
              simp only [↓reduceIte] at hb' ⊢
              have hMintEq : (Custody.mint (dep.policies i) (dep.caps i) anchor (st.vaults i) b).durable.burned =
                  b :: (st.vaults i).durable.burned := by
                rcases Bool.and_eq_true_iff.mp hGrant with ⟨hPA, hMG⟩
                rcases Bool.and_eq_true_iff.mp hPA with ⟨hNP, hAnc⟩
                have hPF : (st.vaults i).poisoned = false := Bool.not_eq_true _ |>.mp
                  (fun hT => by rw [hT] at hNP; cases hNP)
                have hAEq : (st.vaults i).durable.anchor = anchor := of_decide_eq_true hAnc
                rw [Custody.mint_eq]
                simp [hPF, hAEq, hMG]
              rw [hMintEq] at hb'
              rcases List.mem_cons.mp hb' with rfl | hOldB
              · exact ⟨⟨Q, rec, echoes, b'.intent⟩, .head _, rfl,
                  hCertUnpack.1, hCertUnpack.2.1, hCertUnpack.2.2.1, hCertUnpack.2.2.2⟩
              · obtain ⟨mc, hmc, h1, h2, h3, h4, h5⟩ := hInv.burnedCertified i hiHon b' hOldB
                exact ⟨mc, .tail _ hmc, h1, h2, h3, h4, h5⟩
            · simp only [hip, ↓reduceIte] at hb' ⊢
              exact hInv.burnedCertified i hiHon b' hb'
          · intro op hop
            obtain ⟨hOpHon, hAtt, hEp⟩ := hInv.shareReleaseProvenance op hop
            refine ⟨hOpHon, ?_, hEp⟩
            by_cases hopp : op.party = p
            · rw [hopp] at hAtt ⊢
              simp only [↓reduceIte]
              rw [Custody.mint_eq]
              split
              · exact hAtt
              · split <;> exact hAtt
            · simp only [hopp, ↓reduceIte]; exact hAtt
        · have hGrantF : (!((st.vaults p).poisoned) &&
              decide ((st.vaults p).durable.anchor = anchor) &&
              Custody.mintGuard (dep.policies p) (dep.caps p) (st.vaults p) b) = false :=
            Bool.not_eq_true _ |>.mp hGrant
          simp only [hGrantF, Bool.false_eq_true, ↓reduceIte]
          have hBurnUnchanged :
              (Custody.mint (dep.policies p) (dep.caps p) anchor (st.vaults p) b).durable.burned =
              (st.vaults p).durable.burned := by
            rw [Custody.mint_eq]
            split
            · rfl
            · rename_i hNotPoisOrAnc
              split
              · rename_i hMG
                exfalso
                have hPF : (st.vaults p).poisoned = false := by
                  cases hP : (st.vaults p).poisoned
                  · rfl
                  · simp [hP] at hNotPoisOrAnc
                have hAEq : (st.vaults p).durable.anchor = anchor := by
                  by_cases hA : (st.vaults p).durable.anchor = anchor
                  · exact hA
                  · simp [hPF, hA] at hNotPoisOrAnc
                have hGTrue : (!((st.vaults p).poisoned) &&
                    decide ((st.vaults p).durable.anchor = anchor) &&
                    Custody.mintGuard (dep.policies p) (dep.caps p) (st.vaults p) b) = true := by
                  simp [hPF, hAEq, hMG]
                rw [hGTrue] at hGrantF
                cases hGrantF
              · rfl
          refine ⟨hInv.beltSync, ?_, ?_, ?_, hInv.shareReleasesNodupPartyIntent,
            hInv.combinedVerified⟩
          · intro i
            by_cases hip : i = p
            · subst hip; simp only [↓reduceIte]
              exact Custody.mint_safe _ _ anchor _ b (hInv.vaultSafe i)
            · simp only [hip, ↓reduceIte]; exact hInv.vaultSafe i
          · intro i hiHon b' hb'
            by_cases hip : i = p
            · subst hip
              simp only [↓reduceIte, hBurnUnchanged] at hb'
              exact hInv.burnedCertified i hiHon b' hb'
            · simp only [hip, ↓reduceIte] at hb'
              exact hInv.burnedCertified i hiHon b' hb'
          · intro op hop
            obtain ⟨hOpHon, hAtt, hEp⟩ := hInv.shareReleaseProvenance op hop
            refine ⟨hOpHon, ?_, hEp⟩
            by_cases hopp : op.party = p
            · rw [hopp] at hAtt ⊢
              simp only [↓reduceIte]
              rw [Custody.mint_eq]
              split
              · exact hAtt
              · split <;> exact hAtt
            · simp only [hopp, ↓reduceIte]; exact hAtt
      · have hLatchF : checkLatchCertifiedBurn dep.H dep.MAC dep.macKeys dep.q dep.deploymentId p
            (st.beltNet.nodes p) Q rec echoes b = false := Bool.not_eq_true _ |>.mp hLatch
        simp only [hLatchF, Bool.false_eq_true, ↓reduceIte]
        exact hInv
  | releaseShare p anchor r counter =>
    unfold stepShamirCustody
    by_cases hCorr : dep.Corrupt.mem p = true
    · simp only [hCorr, ↓reduceIte]; exact hInv
    · have hHon : dep.Corrupt.mem p = false := Bool.not_eq_true _ |>.mp hCorr
      simp only [hHon, Bool.false_eq_true, ↓reduceIte]
      let pk := dep.validatorPk
      let gLeaf := UInt64.ofNat r.leaf
      let msg := intentCanonicalPayload dep.deploymentId r
      let dig := quorumCounterDigest dep.H (quorumMessageHash dep.H pk gLeaf msg) counter
      let digitsList := dep.digitsOf dig
      let digitsFn : Fin L → Fin 4 := fun i => digitsList.getD i.1 ⟨0, by decide⟩
      let res := releaseShamirShareFromVault dep.H dep.masterSeed dep.polyTape
        (dep.evalPts p) p anchor (st.vaults p) r counter digitsFn
      have hResSafe : Custody.Safe (dep.policies p) (dep.caps p) res.1 :=
        releaseShamirShareFromVault_safe dep.H dep.masterSeed dep.polyTape (dep.evalPts p) p
          (dep.policies p) (dep.caps p) anchor (st.vaults p) r counter digitsFn (hInv.vaultSafe p)
      have hResBurn : res.1.durable.burned = (st.vaults p).durable.burned := by
        dsimp only [res, releaseShamirShareFromVault]
        split
        · rfl
        · split <;> rfl
      cases hOut : res.2 with
      | some op =>
        dsimp only
        have hRelUnpack :
            (st.vaults p).active = some r ∧
            res.1.attempted = r :: (st.vaults p).attempted ∧
            op.party = p ∧ op.intent = r ∧ op.epoch = UInt64.ofNat r.leaf := by
          dsimp only [res, releaseShamirShareFromVault] at hOut ⊢
          split at hOut
          · cases hOut
          · split at hOut
            · rename_i hNP hAct
              have hNPF : ((st.vaults p).poisoned || decide ((st.vaults p).durable.anchor ≠ anchor)) = false :=
                Bool.not_eq_true _ |>.mp hNP
              injection hOut with hOpEq
              rw [← hOpEq]
              simp only [hNPF, Bool.false_eq_true, ↓reduceIte, hAct, computeShamirCustodianOpening,
                and_self]
            · cases hOut
        refine ⟨hInv.beltSync, ?_, ?_, ?_, ?_, hInv.combinedVerified⟩
        · intro i
          by_cases hip : i = p
          · subst hip; simp only [↓reduceIte]; exact hResSafe
          · simp only [hip, ↓reduceIte]; exact hInv.vaultSafe i
        · intro i hiHon b' hb'
          by_cases hip : i = p
          · subst hip; simp only [↓reduceIte] at hb'; rw [hResBurn] at hb'
            exact hInv.burnedCertified i hiHon b' hb'
          · simp only [hip, ↓reduceIte] at hb'
            exact hInv.burnedCertified i hiHon b' hb'
        · intro op' hop'
          rcases List.mem_cons.mp hop' with rfl | hOldOp
          · refine ⟨hRelUnpack.2.2.1 ▸ hHon, ?_, hRelUnpack.2.2.2.1.symm ▸ hRelUnpack.2.2.2.2⟩
            rw [hRelUnpack.2.2.1, hRelUnpack.2.2.2.1]
            simp only [↓reduceIte]
            rw [hRelUnpack.2.1]
            exact .head _
          · obtain ⟨hOpHon, hAtt, hEp⟩ := hInv.shareReleaseProvenance op' hOldOp
            refine ⟨hOpHon, ?_, hEp⟩
            by_cases hopp : op'.party = p
            · rw [hopp] at hAtt ⊢
              simp only [↓reduceIte]
              rw [hRelUnpack.2.1]
              exact .tail _ hAtt
            · simp only [hopp, ↓reduceIte]; exact hAtt
        · simp only [List.map_cons, List.nodup_cons]
          refine ⟨?_, hInv.shareReleasesNodupPartyIntent⟩
          intro hMemMap
          obtain ⟨opOld, hOldMem, hPairEq⟩ := List.mem_map.mp hMemMap
          rcases Prod.mk.inj hPairEq with ⟨hPartyOld, hIntentOld⟩
          obtain ⟨_, hAttOld, _⟩ := hInv.shareReleaseProvenance opOld hOldMem
          rw [hPartyOld, hRelUnpack.2.2.1, hIntentOld, hRelUnpack.2.2.2.1] at hAttOld
          exact (hInv.vaultSafe p).activeFresh r hRelUnpack.1 hAttOld
      | none =>
        dsimp only
        have hAttSub : ∀ s ∈ (st.vaults p).attempted, s ∈ res.1.attempted := by
          intro s hs
          dsimp only [res, releaseShamirShareFromVault]
          split
          · exact hs
          · split
            · exact .tail _ hs
            · exact hs
        refine ⟨hInv.beltSync, ?_, ?_, ?_, hInv.shareReleasesNodupPartyIntent,
          hInv.combinedVerified⟩
        · intro i
          by_cases hip : i = p
          · subst hip; simp only [↓reduceIte]; exact hResSafe
          · simp only [hip, ↓reduceIte]; exact hInv.vaultSafe i
        · intro i hiHon b' hb'
          by_cases hip : i = p
          · subst hip; simp only [↓reduceIte] at hb'; rw [hResBurn] at hb'
            exact hInv.burnedCertified i hiHon b' hb'
          · simp only [hip, ↓reduceIte] at hb'
            exact hInv.burnedCertified i hiHon b' hb'
        · intro op' hop'
          obtain ⟨hOpHon, hAtt, hEp⟩ := hInv.shareReleaseProvenance op' hop'
          refine ⟨hOpHon, ?_, hEp⟩
          by_cases hopp : op'.party = p
          · rw [hopp] at hAtt ⊢
            simp only [↓reduceIte]
            exact hAttSub _ hAtt
          · simp only [hopp, ↓reduceIte]; exact hAtt
  | combineSig leafChainPk lambdas r counter submitted authPath =>
    unfold stepShamirCustody
    dsimp only
    cases hComb : combinePreSteppedShamirValidatorSig L dep.targetSum dep.deploymentId dep.H dep.validatorPk
        dep.digitsOf leafChainPk lambdas r counter submitted authPath with
    | none => exact hInv
    | some sig =>
      dsimp only
      have hCombOk :
          sig.leaf = UInt64.ofNat r.leaf ∧
          verifyQuorumJortsSigAt L dep.targetSum dep.H dep.validatorPk dep.digitsOf
            (intentCanonicalPayload dep.deploymentId r) sig = true := by
        unfold combinePreSteppedShamirValidatorSig at hComb
        dsimp only at hComb
        split at hComb
        · cases hComb
        · split at hComb
          · rename_i candFn _ hVer
            injection hComb with hSigEq
            rw [← hSigEq]
            exact ⟨rfl, hVer⟩
          · cases hComb
      refine ⟨hInv.beltSync, hInv.vaultSafe, hInv.burnedCertified,
        hInv.shareReleaseProvenance, hInv.shareReleasesNodupPartyIntent, ?_⟩
      intro entry hMem
      rcases List.mem_cons.mp hMem with rfl | hOld
      · exact hCombOk
      · exact hInv.combinedVerified entry hOld
  | forgetVault p =>
    unfold stepShamirCustody
    dsimp only
    by_cases hCorr : dep.Corrupt.mem p = true
    · simp only [hCorr, ↓reduceIte]; exact hInv
    · have hHon : dep.Corrupt.mem p = false := Bool.not_eq_true _ |>.mp hCorr
      simp only [hHon, Bool.false_eq_true, ↓reduceIte]
      refine ⟨hInv.beltSync, ?_, ?_, ?_, hInv.shareReleasesNodupPartyIntent,
        hInv.combinedVerified⟩
      · intro i
        by_cases hip : i = p
        · subst hip; simp only [↓reduceIte]
          exact Custody.forget_safe _ _ _ (hInv.vaultSafe i)
        · simp only [hip, ↓reduceIte]; exact hInv.vaultSafe i
      · intro i hiHon b' hb'
        by_cases hip : i = p
        · subst hip; simp only [↓reduceIte, Custody.forget] at hb'
          exact hInv.burnedCertified i hiHon b' hb'
        · simp only [hip, ↓reduceIte] at hb'
          exact hInv.burnedCertified i hiHon b' hb'
      · intro op hop
        obtain ⟨hOpHon, hAtt, hEp⟩ := hInv.shareReleaseProvenance op hop
        refine ⟨hOpHon, ?_, hEp⟩
        by_cases hopp : op.party = p
        · rw [hopp] at hAtt ⊢; simp [Custody.forget, hAtt]
        · simp [hopp, hAtt]
  | crashAndRecoverCustodian p =>
    unfold stepShamirCustody
    dsimp only
    refine ⟨?_, ?_, ?_, ?_, hInv.shareReleasesNodupPartyIntent, hInv.combinedVerified⟩
    · rw [runBeltNetworkTrace_append_singleton, ← hInv.beltSync]
    · intro i
      dsimp only
      by_cases hip : i = p
      · subst hip
        cases hC : dep.Corrupt.mem i
        · simp only [Bool.not_false]
          exact Custody.forget_safe _ _ _ (hInv.vaultSafe i)
        · simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          exact hInv.vaultSafe i
      · have hDecF : decide (i = p) = false := decide_eq_false hip
        simp only [hDecF, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        exact hInv.vaultSafe i
    · intro i hiHon b' hb'
      dsimp only at hb'
      by_cases hip : i = p
      · subst hip
        simp only [hiHon, Bool.not_false, Custody.forget] at hb'
        exact hInv.burnedCertified i hiHon b' hb'
      · have hDecF : decide (i = p) = false := decide_eq_false hip
        simp only [hDecF, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hb'
        exact hInv.burnedCertified i hiHon b' hb'
    · intro op hop
      obtain ⟨hOpHon, hAtt, hEp⟩ := hInv.shareReleaseProvenance op hop
      dsimp only
      refine ⟨hOpHon, ?_, hEp⟩
      by_cases hopp : op.party = p
      · rw [hopp] at hOpHon hAtt ⊢
        simp only [hOpHon, Bool.not_false, Custody.forget]
        exact hAtt
      · have hDecF : decide (op.party = p) = false := decide_eq_false hopp
        simp only [hDecF, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        exact hAtt

theorem runShamirCustodyTrace_inv {n L d : Nat}
    (dep : ShamirValidatorDeployment n L d)
    (trace : List (ShamirCustodyTurn n L)) :
    ShamirCustodyNetworkInv dep
      (runShamirCustodyTrace dep
        (ShamirCustodyNetworkState.init dep) trace) := by
  have hInit : ShamirCustodyNetworkInv dep
      (ShamirCustodyNetworkState.init dep) :=
    { beltSync := (runBeltNetworkTrace_nil _ _ _ _ _ _).symm
      vaultSafe := fun p => Custody.initial_safe (dep.policies p) (dep.caps p) (dep.vaultIdentity p)
      burnedCertified := fun p _ b h => by
        have h' : b ∈ (Custody.initial (dep.vaultIdentity p)).durable.burned := h
        rw [Custody.initial_eq] at h'
        cases h'
      shareReleaseProvenance := fun _ h => by cases h
      shareReleasesNodupPartyIntent := List.nodup_nil
      combinedVerified := fun _ h => by cases h }
  generalize ShamirCustodyNetworkState.init dep = st₀ at hInit
  induction trace generalizing st₀ with
  | nil => exact hInit
  | cons turn rest ih =>
    exact ih _ (stepShamirCustody_preserves_inv dep st₀ turn hInit)

private theorem list_getD_eq_getElem_local {α : Type} (xs : List α) (d : α) {i : Nat}
    (hi : i < xs.length) : xs.getD i d = xs[i] := by
  induction xs generalizing i with
  | nil => cases hi
  | cons x rest ih =>
    cases i with
    | zero => rfl
    | succ k => exact ih (Nat.lt_of_succ_lt_succ hi)

private theorem vault_update_identity {n : Nat} (vs : Fin n → Custody.Vault) (p : Fin n)
    (v : Custody.Vault) (ids : Fin n → Custody.VaultIdentity)
    (h : ∀ q, (vs q).identity = ids q) (hv : v.identity = (vs p).identity) (q : Fin n) :
    (if q = p then v else vs q).identity = ids q := by
  by_cases hqp : q = p
  · subst hqp
    simp only [↓reduceIte]
    exact hv.trans (h q)
  · simp only [hqp, ↓reduceIte]
    exact h q

/-- No turn changes a vault's identity. -/
theorem stepShamirCustody_identity {n L d : Nat}
    (dep : ShamirValidatorDeployment n L d)
    (st : ShamirCustodyNetworkState n L) (turn : ShamirCustodyTurn n L)
    (h : ∀ p : Fin n, (st.vaults p).identity = dep.vaultIdentity p) :
    ∀ p : Fin n, ((stepShamirCustody dep st turn).vaults p).identity = dep.vaultIdentity p := by
  intro q
  cases turn with
  | belt bTurn => exact h q
  | certifiedMint p anchor Q rec echoes b =>
    unfold stepShamirCustody
    dsimp only
    split
    · exact h q
    · split
      · split
        · exact vault_update_identity st.vaults p _ dep.vaultIdentity h
            (Custody.mint_identity _ _ _ _ _) q
        · exact vault_update_identity st.vaults p _ dep.vaultIdentity h
            (Custody.mint_identity _ _ _ _ _) q
      · exact h q
  | releaseShare p anchor r counter =>
    unfold stepShamirCustody
    dsimp only
    have hRel : ∀ digits : Fin L → Fin 4,
        (releaseShamirShareFromVault dep.H dep.masterSeed dep.polyTape (dep.evalPts p) p anchor
          (st.vaults p) r counter digits).1.identity = (st.vaults p).identity := by
      intro digits
      unfold releaseShamirShareFromVault
      split
      · rfl
      · split <;> rfl
    split
    · exact h q
    · split
      · exact vault_update_identity st.vaults p _ dep.vaultIdentity h (hRel _) q
      · exact vault_update_identity st.vaults p _ dep.vaultIdentity h (hRel _) q
  | combineSig leafChainPk lambdas r counter submitted authPath =>
    unfold stepShamirCustody
    dsimp only
    split
    · exact h q
    · exact h q
  | forgetVault p =>
    unfold stepShamirCustody
    dsimp only
    split
    · exact h q
    · exact vault_update_identity st.vaults p _ dep.vaultIdentity h
        (Custody.forget_identity _) q
  | crashAndRecoverCustodian p =>
    unfold stepShamirCustody
    dsimp only
    split
    · exact (Custody.forget_identity _).trans (by
        rename_i hc
        have hqp : q = p := by
          rcases Bool.and_eq_true_iff.mp hc with ⟨h1, _⟩
          exact of_decide_eq_true h1
        rw [← hqp]
        exact h q)
    · exact h q

/-- Along every schedule each custodian's vault keeps the identity
    `(dep.deploymentId, p, validator key)` it was created with. -/
theorem runShamirCustodyTrace_identity {n L d : Nat}
    (dep : ShamirValidatorDeployment n L d)
    (trace : List (ShamirCustodyTurn n L)) (p : Fin n) :
    ((runShamirCustodyTrace dep (ShamirCustodyNetworkState.init dep) trace).vaults p).identity =
      dep.vaultIdentity p := by
  have hInit : ∀ q : Fin n,
      ((ShamirCustodyNetworkState.init dep : ShamirCustodyNetworkState n L).vaults q).identity =
        dep.vaultIdentity q := fun q => by
    show (Custody.initial (dep.vaultIdentity q)).identity = dep.vaultIdentity q
    rw [Custody.initial_eq]
  generalize ShamirCustodyNetworkState.init dep = st₀ at hInit
  induction trace generalizing st₀ with
  | nil => exact hInit p
  | cons turn rest ih => exact ih _ (stepShamirCustody_identity dep st₀ turn hInit)

/-! ### Deployment well-formedness, Lagrange completeness and share secrecy -/

/-- Lagrange-at-zero weights of a list of custodians, computed from their evaluation points. -/
def ShamirValidatorDeployment.lagrangeWeights {n L d : Nat}
    (dep : ShamirValidatorDeployment n L d) (parties : List (Fin n)) : List (TowerElem 7) :=
  (parties.map dep.evalPts).map (lagrangeWeightAtZero (parties.map dep.evalPts))

/-- Conditions on the static deployment. -/
structure ShamirValidatorDeployment.WellFormed {n L d : Nat}
    (dep : ShamirValidatorDeployment n L d) : Prop where
  /-- No custodian is dealt the shared value itself. -/
  evalPts_nonzero : ∀ p : Fin n, dep.evalPts p ≠ CommRingOps.zero
  /-- Custodians have pairwise distinct evaluation points. -/
  evalPts_injective : ∀ p q : Fin n, dep.evalPts p = dep.evalPts q → p = q
  /-- The sharing polynomials have `t` coefficients (degree `t - 1`). -/
  threshold_degree : dep.t = d + 1
  threshold_le : dep.t ≤ n
  /-- At most `f < t` custodians are corrupted. -/
  corrupt_le : maskCard dep.Corrupt ≤ dep.f
  f_lt_threshold : dep.f < dep.t
  /-- Two latch quorums intersect in an honest custodian. -/
  latch_quorum : n + dep.f < 2 * dep.q

/-- A well-formed deployment has a signing quorum: all `n` custodians. -/
theorem ShamirValidatorDeployment.WellFormed.quorum_exists {n L d : Nat}
    {dep : ShamirValidatorDeployment n L d} (hWf : dep.WellFormed) :
    ∃ parties : List (Fin n), parties.Nodup ∧ dep.t ≤ parties.length :=
  ⟨List.finRange n, List.nodup_finRange n, by
    rw [List.length_finRange]
    exact hWf.threshold_le⟩

private theorem nodup_map_of_injective {α β : Type} (f : α → β)
    (hInj : ∀ a b : α, f a = f b → a = b) :
    ∀ (l : List α), l.Nodup → (l.map f).Nodup
  | [], _ => List.nodup_nil
  | x :: xs, hNd => by
    obtain ⟨hxNot, hNdXs⟩ := List.nodup_cons.mp hNd
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, nodup_map_of_injective f hInj xs hNdXs⟩
    intro hMem
    obtain ⟨y, hy, hEq⟩ := List.mem_map.mp hMem
    exact hxNot (hInj y x hEq ▸ hy)

private theorem ringDot_map_map {R : Type} [LawfulCommRing R] (w g : R → R) :
    ∀ (S : List R), ringDot (S.map w) (S.map g) =
      ringListSum (S.map (fun x => CommRingOps.mul (w x) (g x)))
  | [] => by
    rw [ringDot_eq]
    rfl
  | x :: xs => by
    rw [List.map_cons, List.map_cons, List.map_cons, ringDot_eq]
    show CommRingOps.add (CommRingOps.mul (w x) (g x)) (dotVec (xs.map w) (xs.map g)) =
      CommRingOps.add (CommRingOps.mul (w x) (g x))
        (ringListSum (xs.map (fun x => CommRingOps.mul (w x) (g x))))
    rw [← ringDot_eq, ringDot_map_map w g xs]

/-- **Share secrecy below the threshold.** In a well-formed deployment, for any list of fewer than
    `t` custodians and any shift `w` of the shared value, there is a bijection of the sharing
    polynomials (`t` coefficients) that adds `w` to the shared value and leaves every share of
    those custodians unchanged. Their joint share vector therefore has the same distribution for
    every shared value when the polynomial's other coefficients are uniform. -/
theorem ShamirValidatorDeployment.WellFormed.corrupt_shares_independent_of_secret {n L d : Nat}
    {dep : ShamirValidatorDeployment n L d} (hWf : dep.WellFormed)
    (corrupt : List (Fin n)) (hFew : corrupt.length < dep.t) (w : TowerElem 7) :
    ∃ e : SimpleEquiv (ShamirPadPoly (TowerElem 7) (d + 1)) (ShamirPadPoly (TowerElem 7) (d + 1)),
      ∀ P : ShamirPadPoly (TowerElem 7) (d + 1),
        RoundPoly.evalCoeffs (e.toFun P).1 CommRingOps.zero =
          CommRingOps.add w (RoundPoly.evalCoeffs P.1 CommRingOps.zero) ∧
        ∀ p : Fin n, p ∈ corrupt →
          RoundPoly.evalCoeffs (e.toFun P).1 (dep.evalPts p) =
            RoundPoly.evalCoeffs P.1 (dep.evalPts p) := by
  have hCard : (corrupt.map dep.evalPts).length + 1 ≤ d + 1 := by
    rw [List.length_map, ← hWf.threshold_degree]
    exact Nat.succ_le_of_lt hFew
  have hNz : ∀ c ∈ corrupt.map dep.evalPts, c ≠ CommRingOps.zero := by
    intro c hc
    obtain ⟨q, _, hq⟩ := List.mem_map.mp hc
    exact hq ▸ hWf.evalPts_nonzero q
  refine ⟨shamir_rebalanceEquiv LawfulField.inv (d + 1) (corrupt.map dep.evalPts) w hCard,
    fun P => ?_⟩
  have h := pad_bijection_masked_openings_uniform (R := TowerElem 7) LawfulField.inv
    (fun _ hx => LawfulField.mul_inv_cancel hx) (d + 1) (corrupt.map dep.evalPts) w hCard hNz P
  exact ⟨(LawfulCommRing.zero_add _).symm.trans h.1,
    fun p hp => h.2 _ (List.mem_map_of_mem hp)⟩

/-- Predicate stating that every honest member of `t`-quorum `S` (`S.mem p = true`,
    `Corrupt.mem p = false`) released its Shamir share for `intent` during `st`. -/
@[expose] def HonestQuorumReleasedIntent {n L : Nat}
    (Corrupt : CustodiansMask n) (st : ShamirCustodyNetworkState n L)
    (S : CustodiansMask n) (intent : Custody.Intent) : Prop :=
  ∀ p : Fin n, S.mem p = true → Corrupt.mem p = false →
    ∃ op ∈ st.honestShareReleases, op.party = p ∧ op.intent = intent

/-- **Crown Jewel 1 (`M3` Epoch Non-Equivocation) — `(t, n)` Shamir + `2q > n + f` `BeltLatch`
    Multi-Turn Non-Equivocation (`shamir_custody_epoch_non_equivocation`)**:
    Under `maskCard dep.Corrupt ≤ dep.f`, `dep.f < dep.t`, and `2 * dep.q > n + dep.f`, across ANY
    reachable multi-turn state `st = runShamirCustodyTrace dep init trace`:
    1. **Per-Custodian Unconditional Leaf Uniqueness & Spend Cap:** Every custodian's `Custody.Vault`
       satisfies `(st.vaults p).durable.spent ≤ dep.caps p`, and no honest custodian ever releases
       Shamir shares for two distinct intents `r₁ ≠ r₂` at the same leaf epoch `r₁.leaf = r₂.leaf`.
    2. **Global `(q, t)` Epoch Non-Equivocation:** Whenever two `t`-subsets `S₁, S₂`
       (`dep.t ≤ maskCard S₁`, `dep.t ≤ maskCard S₂`) obtain Shamir share releases from their
       honest members for intents `r₁` and `r₂` at the **same leaf epoch** (`r₁.leaf = r₂.leaf`),
       we constructively extract honest share-holders `h₁ ∈ S₁ \ Corrupt` and `h₂ ∈ S₂ \ Corrupt`
       plus an honest latch witness `pLatch ∈ (Q₁ ∩ Q₂) \ Corrupt`, and prove that EITHER:
       - `r₁ = r₂` (exact message/session/round/spend agreement — zero equivocation!), OR
       - an explicit `PairwiseEchoMacForgery` on `st.beltNet.emittedHonestEchoes` occurred, OR
       - an explicit 256-bit `HashCollision256 dep.H` (`intentCanonicalPayload dep.deploymentId r₁ ≠ intentCanonicalPayload dep.deploymentId r₂`
         with equal `dep.H` digests) occurred! -/
theorem shamir_custody_epoch_non_equivocation {n L d : Nat}
    (dep : ShamirValidatorDeployment n L d)
    (hCorrupt : maskCard dep.Corrupt ≤ dep.f)
    (hFltT : dep.f < dep.t)
    (hLatchQuorum : 2 * dep.q > n + dep.f)
    (trace : List (ShamirCustodyTurn n L)) :
    let st := runShamirCustodyTrace dep
      (ShamirCustodyNetworkState.init dep) trace
    -- (1) Spend cap & unconditional per-honest-custodian leaf uniqueness:
    (∀ p : Fin n, (st.vaults p).durable.spent ≤ dep.caps p) ∧
    (∀ op₁ ∈ st.honestShareReleases, ∀ op₂ ∈ st.honestShareReleases,
      op₁.party = op₂.party → op₁.intent.leaf = op₂.intent.leaf → op₁.intent = op₂.intent) ∧
    -- (2) Global cross-quorum (q, t) epoch non-equivocation:
    (∀ (S₁ S₂ : CustodiansMask n) (r₁ r₂ : Custody.Intent),
      dep.t ≤ maskCard S₁ →
      dep.t ≤ maskCard S₂ →
      HonestQuorumReleasedIntent dep.Corrupt st S₁ r₁ →
      HonestQuorumReleasedIntent dep.Corrupt st S₂ r₂ →
      r₁.leaf = r₂.leaf →
      r₁ = r₂ ∨
        Nonempty (PairwiseEchoMacForgery dep.MAC dep.macKeys dep.Corrupt
          st.beltNet.emittedHonestEchoes) ∨
        Nonempty (HashCollision256 dep.H)) := by
  intro st
  have hInv := runShamirCustodyTrace_inv dep trace
  refine ⟨fun p => (hInv.vaultSafe p).budget, ?_, ?_⟩
  · -- Part 1b: Per-honest-custodian leaf uniqueness
    intro op₁ hMem₁ op₂ hMem₂ hSameParty hSameLeaf
    obtain ⟨_, hAtt₁, _⟩ := hInv.shareReleaseProvenance op₁ hMem₁
    obtain ⟨_, hAtt₂, _⟩ := hInv.shareReleaseProvenance op₂ hMem₂
    rw [← hSameParty] at hAtt₂
    have hSafe := hInv.vaultSafe op₁.party
    obtain ⟨b₁, hb₁, hb₁Eq⟩ := hSafe.attemptedBurned op₁.intent hAtt₁
    obtain ⟨b₂, hb₂, hb₂Eq⟩ := hSafe.attemptedBurned op₂.intent hAtt₂
    rw [← hb₁Eq, ← hb₂Eq]
    exact hSafe.uniqueLeaf b₁ hb₁ b₂ hb₂ (by rw [hb₁Eq, hb₂Eq]; exact hSameLeaf)
  · -- Part 2: Global (q, t) epoch non-equivocation across S₁ and S₂
    intro S₁ S₂ r₁ r₂ hCard₁ hCard₂ hRel₁ hRel₂ hSameLeaf
    have hDiff₁ : 0 < maskCard (maskDiff S₁ dep.Corrupt) := by
      have hGe := maskCard_diff_ge S₁ dep.Corrupt; omega
    have hDiff₂ : 0 < maskCard (maskDiff S₂ dep.Corrupt) := by
      have hGe := maskCard_diff_ge S₂ dep.Corrupt; omega
    let ⟨h₁, hh₁⟩ := extractMaskMember (maskDiff S₁ dep.Corrupt) hDiff₁
    let ⟨h₂, hh₂⟩ := extractMaskMember (maskDiff S₂ dep.Corrupt) hDiff₂
    simp only [maskDiff, Bool.and_eq_true, Bool.not_eq_true'] at hh₁ hh₂
    obtain ⟨op₁, hop₁, hp₁Eq, hr₁Eq⟩ := hRel₁ h₁ hh₁.1 hh₁.2
    obtain ⟨op₂, hop₂, hp₂Eq, hr₂Eq⟩ := hRel₂ h₂ hh₂.1 hh₂.2
    obtain ⟨_, hAtt₁, _⟩ := hInv.shareReleaseProvenance op₁ hop₁
    obtain ⟨_, hAtt₂, _⟩ := hInv.shareReleaseProvenance op₂ hop₂
    rw [hp₁Eq, hr₁Eq] at hAtt₁
    rw [hp₂Eq, hr₂Eq] at hAtt₂
    obtain ⟨b₁, hb₁, hbi₁⟩ := (hInv.vaultSafe h₁).attemptedBurned r₁ hAtt₁
    obtain ⟨b₂, hb₂, hbi₂⟩ := (hInv.vaultSafe h₂).attemptedBurned r₂ hAtt₂
    obtain ⟨mc₁, _, hmcInt₁, _, hEp₁, hMd₁, hCert₁⟩ := hInv.burnedCertified h₁ hh₁.2 b₁ hb₁
    obtain ⟨mc₂, _, hmcInt₂, _, hEp₂, hMd₂, hCert₂⟩ := hInv.burnedCertified h₂ hh₂.2 b₂ hb₂
    have hQ₁ : dep.q ≤ maskCard mc₁.quorum :=
      verifyQuorumEchoCertificate_quorum_card hCert₁
    have hQ₂ : dep.q ≤ maskCard mc₂.quorum :=
      verifyQuorumEchoCertificate_quorum_card hCert₂
    have hSameRecEpoch : mc₁.latchRec.epoch = mc₂.latchRec.epoch := by
      rw [hEp₁, hEp₂, hbi₁, hbi₂, hSameLeaf]
    have hBeltUniq := beltLatch_quorum_intersection_global_uniqueness
      (height := dep.height) (maxWindow := dep.maxWindow)
      dep.H dep.MAC dep.macKeys dep.Corrupt mc₁.quorum mc₂.quorum
      hLatchQuorum hCorrupt hQ₁ hQ₂ st.beltTrace h₁ h₂ hh₁.2 hh₂.2
      mc₁.latchRec mc₂.latchRec hSameRecEpoch mc₁.echoes mc₂.echoes hCert₁ hCert₂
    rw [← hInv.beltSync] at hBeltUniq
    rcases hBeltUniq.2.2 with ⟨_, hMsgDigEq, _, _⟩ | hMacForge
    · by_cases hEqR : r₁ = r₂
      · exact .inl hEqR
      · right; right
        have hPayNe : intentCanonicalPayload dep.deploymentId r₁ ≠ intentCanonicalPayload dep.deploymentId r₂ :=
          fun hPayEq => hEqR (intentCanonicalPayload_injective hPayEq).2
        have hHashEq : dep.H (intentCanonicalPayload dep.deploymentId r₁) = dep.H (intentCanonicalPayload dep.deploymentId r₂) := by
          rw [← hbi₁, ← hMd₁, hMsgDigEq, hMd₂, hbi₂]
        exact ⟨⟨intentCanonicalPayload dep.deploymentId r₁, intentCanonicalPayload dep.deploymentId r₂, hPayNe, hHashEq⟩⟩
    · exact .inr (.inl hMacForge)

/-- Epoch non-equivocation for a well-formed deployment: the corruption bound, `f < t` and the
    latch-quorum intersection condition are the `WellFormed` fields. -/
theorem shamir_custody_wellFormed_epoch_non_equivocation {n L d : Nat}
    (dep : ShamirValidatorDeployment n L d) (hWf : dep.WellFormed)
    (trace : List (ShamirCustodyTurn n L)) :
    let st := runShamirCustodyTrace dep (ShamirCustodyNetworkState.init dep) trace
    (∀ p : Fin n, (st.vaults p).durable.spent ≤ dep.caps p) ∧
    (∀ op₁ ∈ st.honestShareReleases, ∀ op₂ ∈ st.honestShareReleases,
      op₁.party = op₂.party → op₁.intent.leaf = op₂.intent.leaf → op₁.intent = op₂.intent) ∧
    (∀ (S₁ S₂ : CustodiansMask n) (r₁ r₂ : Custody.Intent),
      dep.t ≤ maskCard S₁ →
      dep.t ≤ maskCard S₂ →
      HonestQuorumReleasedIntent dep.Corrupt st S₁ r₁ →
      HonestQuorumReleasedIntent dep.Corrupt st S₂ r₂ →
      r₁.leaf = r₂.leaf →
      r₁ = r₂ ∨
        Nonempty (PairwiseEchoMacForgery dep.MAC dep.macKeys dep.Corrupt
          st.beltNet.emittedHonestEchoes) ∨
        Nonempty (HashCollision256 dep.H)) :=
  shamir_custody_epoch_non_equivocation dep hWf.corrupt_le hWf.f_lt_threshold hWf.latch_quorum
    trace

/-! ## §4. Single-Validator Lagrange `(t, n)` Signature Reconstruction & Hypertree Bridge -/

/-- Assemble `SubmittedDigest256ShamirShares L` from `t` honest custodian share openings. -/
def assembleSubmittedSharesFromOpenings {n L : Nat}
    (openings : List (ShamirCustodianShareOpening n L)) :
    SubmittedDigest256ShamirShares L :=
  fun i =>
    (openings.filterMap (fun op => (op.chainShares i).map Prod.fst),
     openings.filterMap (fun op => (op.chainShares i).map Prod.snd))

/-- **Crown Jewel 2A (`M3` Single-Validator Reconstruction & Collision Soundness) —
    (`shamir_custody_combined_sig_verifies_or_collision`)**:
    For the single enrolled validator public key `validatorPk = dep.validatorPk`
    (`dep.height < 256`, `32 * L < 256 ^ 8`):
    1. **Honest `(t, n)` Completeness & Single-Key Verification:** Whenever `t` custodians at
       evaluation points `pts` with Lagrange weights `lambdas` (`∀ c₀ tail, ringDot lambdas ... = c₀`)
       release honest `ShamirCustodianShareOpening`s for `(r, counter)` (`r.leaf < 2 ^ dep.height`,
       `counter.toNat < 2 ^ 16`, balanced digits of length `L`), `combinePreSteppedShamirValidatorSig`
       deterministically outputs `some (quorumJortsReferenceSign ...)` AND that signature verifies
       under the single enrolled `validatorPk`!
    2. **Quorum Invariance (`QS-B`):** Any two honest `t`-subsets `(parties₁, lambdas₁)` and
       `(parties₂, lambdas₂)` reconstruct the **bit-for-bit identical** single-validator
       `QuorumJortsSig`!
    3. **Concrete `(t = 2, n = 4)` `GF(2^128)` (`TowerElem 7`) Instantiation:** Any two distinct
       custodian points `x₀ ≠ x₁` in `TowerElem 7` satisfy the Lagrange hypothesis via
       `lagrange2WeightsTower 7 x₀ x₁`.
    4. **Adversarial Share-Corruption & Combiner Soundness:** Every `(r, sig)` recorded in
       `st.combinedSignatures` along any multi-turn trace verifies under `validatorPk`, AND
       constructively either equals the exact single-validator reference chain nodes or yields an
       explicit `WotsChainCollisionWitness` / `HashCollision256 dep.H`! -/
theorem shamir_custody_combined_sig_verifies_or_collision {n L d : Nat}
    (dep : ShamirValidatorDeployment n L d)
    (hHeightLt : dep.height < 256)
    (hChainBound : 32 * L < 256 ^ 8) :
    let pk := dep.validatorPk
    -- (1) Honest (t, n) completeness & verification under single enrolled validatorPk:
    (∀ (parties : List (Fin n)) (lambdas : List (TowerElem 7))
       (r : Custody.Intent) (counter : UInt32),
      let gLeaf := UInt64.ofNat r.leaf
      let msg := intentCanonicalPayload dep.deploymentId r
      let digits := dep.digitsOf (quorumCounterDigest dep.H (quorumMessageHash dep.H pk gLeaf msg) counter)
      let digitsFn : Fin L → Fin 4 := fun i => digits.getD i.1 ⟨0, by decide⟩
      let leafChainPk : Fin L → Digest256 := fun i =>
        wotsChainIter (quorumChainStep dep.H pk.pkSeed gLeaf) i.1 0 3
          (quorumStageChainSk dep.H dep.masterSeed gLeaf (UInt32.ofNat i.1))
      let authPath := quorumAuthPath dep.H pk.pkSeed
        (quorumHonestLeafDigest L dep.H dep.masterSeed) dep.height 0 gLeaf.toNat
      let openings := parties.map (fun p =>
        computeShamirCustodianOpening dep.H dep.masterSeed dep.polyTape (dep.evalPts p)
          p r counter digitsFn)
      (∀ (c₀ : TowerElem 7) (tail : ShamirPadPoly (TowerElem 7) d),
        ringDot lambdas ((parties.map dep.evalPts).map
          (fun x => RoundPoly.evalCoeffs (c₀ :: tail.1) x)) = c₀) →
      r.leaf < 2 ^ dep.height →
      r.leaf < 2 ^ 64 →
      counter.toNat < 2 ^ 16 →
      digits.length = L →
      ((digits.map Fin.val).foldr (· + ·) 0) = dep.targetSum →
      combinePreSteppedShamirValidatorSig L dep.targetSum dep.deploymentId dep.H pk dep.digitsOf
        leafChainPk lambdas r counter (assembleSubmittedSharesFromOpenings openings) authPath =
          some (quorumJortsReferenceSign dep.H dep.masterSeed gLeaf counter digits authPath) ∧
      verifyQuorumJortsSigAt L dep.targetSum dep.H pk dep.digitsOf msg
        (quorumJortsReferenceSign dep.H dep.masterSeed gLeaf counter digits authPath) = true) ∧
    -- (2) Quorum invariance across any two honest t-subsets:
    (∀ (parties₁ parties₂ : List (Fin n)) (lambdas₁ lambdas₂ : List (TowerElem 7))
       (r : Custody.Intent) (counter : UInt32),
      let gLeaf := UInt64.ofNat r.leaf
      let msg := intentCanonicalPayload dep.deploymentId r
      let digits := dep.digitsOf (quorumCounterDigest dep.H (quorumMessageHash dep.H pk gLeaf msg) counter)
      let digitsFn : Fin L → Fin 4 := fun i => digits.getD i.1 ⟨0, by decide⟩
      let leafChainPk : Fin L → Digest256 := fun i =>
        wotsChainIter (quorumChainStep dep.H pk.pkSeed gLeaf) i.1 0 3
          (quorumStageChainSk dep.H dep.masterSeed gLeaf (UInt32.ofNat i.1))
      let authPath := quorumAuthPath dep.H pk.pkSeed
        (quorumHonestLeafDigest L dep.H dep.masterSeed) dep.height 0 gLeaf.toNat
      let ops₁ := parties₁.map (fun p =>
        computeShamirCustodianOpening dep.H dep.masterSeed dep.polyTape (dep.evalPts p)
          p r counter digitsFn)
      let ops₂ := parties₂.map (fun p =>
        computeShamirCustodianOpening dep.H dep.masterSeed dep.polyTape (dep.evalPts p)
          p r counter digitsFn)
      (∀ (c₀ : TowerElem 7) (tail : ShamirPadPoly (TowerElem 7) d),
        ringDot lambdas₁ ((parties₁.map dep.evalPts).map
          (fun x => RoundPoly.evalCoeffs (c₀ :: tail.1) x)) = c₀) →
      (∀ (c₀ : TowerElem 7) (tail : ShamirPadPoly (TowerElem 7) d),
        ringDot lambdas₂ ((parties₂.map dep.evalPts).map
          (fun x => RoundPoly.evalCoeffs (c₀ :: tail.1) x)) = c₀) →
      r.leaf < 2 ^ dep.height →
      r.leaf < 2 ^ 64 →
      counter.toNat < 2 ^ 16 →
      digits.length = L →
      ((digits.map Fin.val).foldr (· + ·) 0) = dep.targetSum →
      combinePreSteppedShamirValidatorSig L dep.targetSum dep.deploymentId dep.H pk dep.digitsOf
        leafChainPk lambdas₁ r counter (assembleSubmittedSharesFromOpenings ops₁) authPath =
      combinePreSteppedShamirValidatorSig L dep.targetSum dep.deploymentId dep.H pk dep.digitsOf
        leafChainPk lambdas₂ r counter (assembleSubmittedSharesFromOpenings ops₂) authPath) ∧
    -- (3) Adversarial share-corruption soundness along every multi-turn trace:
    (∀ (trace : List (ShamirCustodyTurn n L)) (entry : Custody.Intent × QuorumJortsSig),
      let st := runShamirCustodyTrace dep
        (ShamirCustodyNetworkState.init dep) trace
      entry ∈ st.combinedSignatures →
      let msg := intentCanonicalPayload dep.deploymentId entry.1
      let digits := dep.digitsOf (quorumCounterDigest dep.H
        (quorumMessageHash dep.H pk entry.2.leaf msg) entry.2.counter)
      verifyQuorumJortsSigAt L dep.targetSum dep.H pk dep.digitsOf msg entry.2 = true ∧
      (entry.2.nodes =
          (quorumJortsReferenceSign dep.H dep.masterSeed entry.2.leaf entry.2.counter
            digits entry.2.authPath).nodes ∨
       Nonempty (WotsChainCollisionWitness (quorumChainStep dep.H pk.pkSeed entry.2.leaf) 4) ∨
       Nonempty (HashCollision256 dep.H))) := by
  intro pk
  have hHonestCombine :
      ∀ (parties : List (Fin n)) (lambdas : List (TowerElem 7))
        (r : Custody.Intent) (counter : UInt32),
      let gLeaf := UInt64.ofNat r.leaf
      let msg := intentCanonicalPayload dep.deploymentId r
      let digits := dep.digitsOf (quorumCounterDigest dep.H (quorumMessageHash dep.H pk gLeaf msg) counter)
      let digitsFn : Fin L → Fin 4 := fun i => digits.getD i.1 ⟨0, by decide⟩
      let leafChainPk : Fin L → Digest256 := fun i =>
        wotsChainIter (quorumChainStep dep.H pk.pkSeed gLeaf) i.1 0 3
          (quorumStageChainSk dep.H dep.masterSeed gLeaf (UInt32.ofNat i.1))
      let authPath := quorumAuthPath dep.H pk.pkSeed
        (quorumHonestLeafDigest L dep.H dep.masterSeed) dep.height 0 gLeaf.toNat
      let openings := parties.map (fun p =>
        computeShamirCustodianOpening dep.H dep.masterSeed dep.polyTape (dep.evalPts p)
          p r counter digitsFn)
      (∀ (c₀ : TowerElem 7) (tail : ShamirPadPoly (TowerElem 7) d),
        ringDot lambdas ((parties.map dep.evalPts).map
          (fun x => RoundPoly.evalCoeffs (c₀ :: tail.1) x)) = c₀) →
      r.leaf < 2 ^ dep.height →
      r.leaf < 2 ^ 64 →
      counter.toNat < 2 ^ 16 →
      digits.length = L →
      ((digits.map Fin.val).foldr (· + ·) 0) = dep.targetSum →
      combinePreSteppedShamirValidatorSig L dep.targetSum dep.deploymentId dep.H pk dep.digitsOf
        leafChainPk lambdas r counter (assembleSubmittedSharesFromOpenings openings) authPath =
          some (quorumJortsReferenceSign dep.H dep.masterSeed gLeaf counter digits authPath) ∧
      verifyQuorumJortsSigAt L dep.targetSum dep.H pk dep.digitsOf msg
        (quorumJortsReferenceSign dep.H dep.masterSeed gLeaf counter digits authPath) = true := by
    intro parties lambdas r counter gLeaf msg digits digitsFn leafChainPk authPath openings
      hLag hLeafH hLeaf64 hCtr hDigLen hSum
    have hGLeafNat : gLeaf.toNat = r.leaf := by
      change (BitVec.ofNat 64 r.leaf).toNat = r.leaf
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hLeaf64]
    have hRefVer := quorumJortsReferenceSign_verifies L dep.targetSum dep.height hHeightLt
      dep.H dep.masterSeed dep.digitsOf gLeaf counter msg (hGLeafNat ▸ hLeafH) hCtr hDigLen hSum
    have hSelfVer := (preStepped_tower128_digest256_self_verification
      (quorumChainStep dep.H pk.pkSeed gLeaf)
      (fun i : Fin L => quorumStageChainSk dep.H dep.masterSeed gLeaf (UInt32.ofNat i.1))
      (dep.polyTape gLeaf) lambdas (parties.map dep.evalPts) hLag digitsFn).1
    have hSubEq : assembleSubmittedSharesFromOpenings openings =
        (fun i : Fin L =>
          if h : (digitsFn i).val < 3 then
            let k : Fin 3 := ⟨(digitsFn i).val, h⟩
            let trueNode := wotsChainIter (quorumChainStep dep.H pk.pkSeed gLeaf) i.1 0
              (digitsFn i).val (quorumStageChainSk dep.H dep.masterSeed gLeaf (UInt32.ofNat i.1))
            let (lo, hi) := splitDigest256Tower128 trueNode
            ((parties.map dep.evalPts).map (fun x => RoundPoly.evalCoeffs (lo :: (dep.polyTape gLeaf i k).1.1) x),
             (parties.map dep.evalPts).map (fun x => RoundPoly.evalCoeffs (hi :: (dep.polyTape gLeaf i k).2.1) x))
          else
            ([], [])) := by
      funext i
      unfold assembleSubmittedSharesFromOpenings
      dsimp only [openings, computeShamirCustodianOpening]
      by_cases hd : (digitsFn i).val < 3
      · simp only [hd, ↓reduceDIte]
        have hFst : ∀ ps : List (Fin n),
            (ps.map (fun p =>
              ({ party := p, intent := r, epoch := gLeaf, counter := counter,
                 evalPoint := dep.evalPts p,
                 chainShares := fun j =>
                   if hStep : (digitsFn j).val < 3 then
                     let k : Fin 3 := ⟨(digitsFn j).val, hStep⟩
                     let sk₀ := quorumStageChainSk dep.H dep.masterSeed gLeaf (UInt32.ofNat j.1)
                     let trueNode := wotsChainIter
                       (quorumChainStep dep.H (quorumStagePkSeed dep.H dep.masterSeed) gLeaf)
                       j.1 0 (digitsFn j).val sk₀
                     let (lo, hi) := splitDigest256Tower128 trueNode
                     some (RoundPoly.evalCoeffs (lo :: (dep.polyTape gLeaf j k).1.1) (dep.evalPts p),
                           RoundPoly.evalCoeffs (hi :: (dep.polyTape gLeaf j k).2.1) (dep.evalPts p))
                   else none } : ShamirCustodianShareOpening n L))).filterMap
              (fun op => (op.chainShares i).map Prod.fst) =
            (ps.map dep.evalPts).map (fun x =>
              RoundPoly.evalCoeffs
                ((splitDigest256Tower128
                  (wotsChainIter (quorumChainStep dep.H pk.pkSeed gLeaf) i.1 0 (digitsFn i).val
                    (quorumStageChainSk dep.H dep.masterSeed gLeaf (UInt32.ofNat i.1)))).1 ::
                 (dep.polyTape gLeaf i ⟨(digitsFn i).val, hd⟩).1.1) x) := by
          intro ps
          induction ps with
          | nil => rfl
          | cons p rest ih =>
            simp only [List.map_cons, List.filterMap_cons, hd, ↓reduceDIte, Option.map_some]
            exact congrArg _ ih
        have hSnd : ∀ ps : List (Fin n),
            (ps.map (fun p =>
              ({ party := p, intent := r, epoch := gLeaf, counter := counter,
                 evalPoint := dep.evalPts p,
                 chainShares := fun j =>
                   if hStep : (digitsFn j).val < 3 then
                     let k : Fin 3 := ⟨(digitsFn j).val, hStep⟩
                     let sk₀ := quorumStageChainSk dep.H dep.masterSeed gLeaf (UInt32.ofNat j.1)
                     let trueNode := wotsChainIter
                       (quorumChainStep dep.H (quorumStagePkSeed dep.H dep.masterSeed) gLeaf)
                       j.1 0 (digitsFn j).val sk₀
                     let (lo, hi) := splitDigest256Tower128 trueNode
                     some (RoundPoly.evalCoeffs (lo :: (dep.polyTape gLeaf j k).1.1) (dep.evalPts p),
                           RoundPoly.evalCoeffs (hi :: (dep.polyTape gLeaf j k).2.1) (dep.evalPts p))
                   else none } : ShamirCustodianShareOpening n L))).filterMap
              (fun op => (op.chainShares i).map Prod.snd) =
            (ps.map dep.evalPts).map (fun x =>
              RoundPoly.evalCoeffs
                ((splitDigest256Tower128
                  (wotsChainIter (quorumChainStep dep.H pk.pkSeed gLeaf) i.1 0 (digitsFn i).val
                    (quorumStageChainSk dep.H dep.masterSeed gLeaf (UInt32.ofNat i.1)))).2 ::
                 (dep.polyTape gLeaf i ⟨(digitsFn i).val, hd⟩).2.1) x) := by
          intro ps
          induction ps with
          | nil => rfl
          | cons p rest ih =>
            simp only [List.map_cons, List.filterMap_cons, hd, ↓reduceDIte, Option.map_some]
            exact congrArg _ ih
        exact Prod.ext (hFst parties) (hSnd parties)
      · simp only [hd, ↓reduceDIte]
        have hNilFst : ∀ ps : List (Fin n),
            (ps.map (fun p =>
              ({ party := p, intent := r, epoch := gLeaf, counter := counter,
                 evalPoint := dep.evalPts p,
                 chainShares := fun j =>
                   if hStep : (digitsFn j).val < 3 then
                     let k : Fin 3 := ⟨(digitsFn j).val, hStep⟩
                     let sk₀ := quorumStageChainSk dep.H dep.masterSeed gLeaf (UInt32.ofNat j.1)
                     let trueNode := wotsChainIter
                       (quorumChainStep dep.H (quorumStagePkSeed dep.H dep.masterSeed) gLeaf)
                       j.1 0 (digitsFn j).val sk₀
                     let (lo, hi) := splitDigest256Tower128 trueNode
                     some (RoundPoly.evalCoeffs (lo :: (dep.polyTape gLeaf j k).1.1) (dep.evalPts p),
                           RoundPoly.evalCoeffs (hi :: (dep.polyTape gLeaf j k).2.1) (dep.evalPts p))
                   else none } : ShamirCustodianShareOpening n L))).filterMap
              (fun op => (op.chainShares i).map Prod.fst) = [] := by
          intro ps
          induction ps with
          | nil => rfl
          | cons p rest ih =>
            simp only [List.map_cons, List.filterMap_cons, hd, ↓reduceDIte, Option.map_none]
            exact ih
        have hNilSnd : ∀ ps : List (Fin n),
            (ps.map (fun p =>
              ({ party := p, intent := r, epoch := gLeaf, counter := counter,
                 evalPoint := dep.evalPts p,
                 chainShares := fun j =>
                   if hStep : (digitsFn j).val < 3 then
                     let k : Fin 3 := ⟨(digitsFn j).val, hStep⟩
                     let sk₀ := quorumStageChainSk dep.H dep.masterSeed gLeaf (UInt32.ofNat j.1)
                     let trueNode := wotsChainIter
                       (quorumChainStep dep.H (quorumStagePkSeed dep.H dep.masterSeed) gLeaf)
                       j.1 0 (digitsFn j).val sk₀
                     let (lo, hi) := splitDigest256Tower128 trueNode
                     some (RoundPoly.evalCoeffs (lo :: (dep.polyTape gLeaf j k).1.1) (dep.evalPts p),
                           RoundPoly.evalCoeffs (hi :: (dep.polyTape gLeaf j k).2.1) (dep.evalPts p))
                   else none } : ShamirCustodianShareOpening n L))).filterMap
              (fun op => (op.chainShares i).map Prod.snd) = [] := by
          intro ps
          induction ps with
          | nil => rfl
          | cons p rest ih =>
            simp only [List.map_cons, List.filterMap_cons, hd, ↓reduceDIte, Option.map_none]
            exact ih
        exact Prod.ext (hNilFst parties) (hNilSnd parties)
    unfold combinePreSteppedShamirValidatorSig
    dsimp only
    rw [hSubEq]
    change (match preSteppedDigest256ReconstructAndSelfVerify
        (quorumChainStep dep.H pk.pkSeed gLeaf) leafChainPk lambdas digitsFn _ with
      | none => none
      | some candFn => _) = _ ∧ _
    rw [hSelfVer]
    dsimp only
    have hSigEq :
        ({ leaf := gLeaf
           counter := counter
           nodes := (List.finRange L).map (fun i : Fin L =>
             wotsChainIter (quorumChainStep dep.H pk.pkSeed gLeaf) i.1 0 (digitsFn i).val
               (quorumStageChainSk dep.H dep.masterSeed gLeaf (UInt32.ofNat i.1)))
           authPath := authPath } : QuorumJortsSig) =
        quorumJortsReferenceSign dep.H dep.masterSeed gLeaf counter digits authPath := by
      unfold quorumJortsReferenceSign
      congr 1
      apply List.ext_getElem
      · simp [hDigLen]
      · intro k hk1 hk2
        simp only [List.getElem_map, List.getElem_finRange]
        dsimp only [digitsFn, pk, ShamirValidatorDeployment.validatorPk, deriveQuorumValidatorPublicKey]
        rw [list_getD_eq_getElem_local digits _ (by simp at hk1; omega)]
        simp
    have hRefVer' :
        verifyQuorumJortsSigAt L dep.targetSum dep.H pk dep.digitsOf (intentCanonicalPayload dep.deploymentId r)
          (quorumJortsReferenceSign dep.H dep.masterSeed gLeaf counter digits authPath) = true :=
      hRefVer
    rw [hSigEq, hRefVer']
    exact ⟨rfl, rfl⟩
  refine ⟨hHonestCombine, ?_, ?_⟩
  · -- Part 2: Quorum invariance across (parties₁, lambdas₁) and (parties₂, lambdas₂)
    intro p₁ p₂ l₁ l₂ r counter _ _ _ _ _ _ _ _ hLag₁ hLag₂ hLH hL64 hCtr hDL hS
    have h1 := (hHonestCombine p₁ l₁ r counter hLag₁ hLH hL64 hCtr hDL hS).1
    have h2 := (hHonestCombine p₂ l₂ r counter hLag₂ hLH hL64 hCtr hDL hS).1
    exact h1.trans h2.symm
  · -- Part 3: Multi-turn combined signature verification & constructive collision extraction
    intro trace entry st hMem msg digits
    have hInv := runShamirCustodyTrace_inv dep trace
    have hVer := (hInv.combinedVerified entry hMem).2
    refine ⟨hVer, ?_⟩
    cases verifyQuorumJortsSigAt_extract_reference_or_collision L dep.targetSum dep.height
        hHeightLt hChainBound dep.H dep.masterSeed dep.digitsOf msg entry.2 hVer with
    | inl hEqNodes => exact .inl hEqNodes
    | inr sub =>
      cases sub with
      | inl w => exact .inr (.inl ⟨w⟩)
      | inr c => exact .inr (.inr ⟨c⟩)

/-- **Crown Jewel 2B (`M3` + `M7` Production Hypertree Single-Validator Bridge) —
    (`shamir_custody_single_validator_pq_bridge`)**:
    Connects single-validator threshold MPC signing (`mpcEvalProductionStatefulSign` under a
    **single** enrolled `validatorSk : PqSecretKey`, `o.MatchesKey cfg.suite validatorSk`) to
    both `CompleteMediationBoundary` custodian vaults AND `ProdCollisionExtraction` /
    `ProdHashGameReductions`:
    1. **Single-Validator MPC Equivalence & Verification:** For every `r` signed via
       `mpcEvalProductionStatefulSign`, the output equals `evalProductionStatefulSign` and
       verifies under the **single** enrolled `derivePublicKey cfg.suite cfg.params validatorSk`!
    2. **Unapproved Forgery Extraction (`f < t`):** If `t` custodian approvals are required
       (`maskCard Corrupt ≤ f < t`) for a subset `S` (`t ≤ maskCard S`), then there is an honest
       custodian `h ∈ S \ Corrupt` whose vault satisfies `queries_one_time`. Whenever any
       `sigStar` verifies under the single enrolled `derivePublicKey cfg.suite cfg.params validatorSk`
       on `intentCanonicalPayload dep.deploymentId rStar` while `rStar ∉ (st.vaults h).attempted` (never released
       by honest custodian `h`, where the validator's signing history is recorded in `(st.vaults h)`),
       it wins `prodEufCmaWin` AND constructively yields `Nonempty (ProdTcrWitness ...)` or
       `ProdPreimageBreak ...` (`0 Classical.choice`)! -/
theorem shamir_custody_single_validator_pq_bridge {n L d : Nat}
    (dep : ShamirValidatorDeployment n L d)
    (cfg : Custody.SigningConfig)
    (validatorSk : PqSecretKey)
    (o : ProductionPqHashMpcOracles)
    (hMatch : o.MatchesKey cfg.suite validatorSk)
    (hw : cfg.params.w = 4 ∨ cfg.params.w = 16)
    (hst : cfg.params.statefulJorts = true)
    (hCorrupt : maskCard dep.Corrupt ≤ dep.f)
    (hFltT : dep.f < dep.t)
    (trace : List (ShamirCustodyTurn n L)) :
    let st := runShamirCustodyTrace dep
      (ShamirCustodyNetworkState.init dep) trace
    let validatorPqPk := derivePublicKey cfg.suite cfg.params validatorSk
    -- (1) Threshold MPC signing matches single-validator reference & verifies under validatorPqPk:
    (∀ (r : Custody.Intent),
      mpcEvalProductionStatefulSign cfg.suite cfg.params o validatorSk.pkSeed
        (Custody.payload dep.deploymentId 0 r) cfg.randomness r.leaf cfg.grindLimit =
      evalProductionStatefulSign cfg.suite cfg.params validatorSk
        (Custody.payload dep.deploymentId 0 r) cfg.randomness r.leaf cfg.grindLimit ∧
      (∀ sig, mpcEvalProductionStatefulSign cfg.suite cfg.params o validatorSk.pkSeed
          (Custody.payload dep.deploymentId 0 r) cfg.randomness r.leaf cfg.grindLimit = some sig →
        verifyProductionPqHashSig cfg.suite cfg.params validatorPqPk
          (Custody.payload dep.deploymentId 0 r) sig = true)) ∧
    -- (2) Any signature verifying under single validatorPqPk without t-of-n honest release
    --     constructively extracts a ProdTcrWitness or ProdPreimageBreak:
    (∀ (S : CustodiansMask n) (rStar : Custody.Intent) (sigStar : PqHashSig),
      dep.t ≤ maskCard S →
      verifyProductionPqHashSig cfg.suite cfg.params validatorPqPk
        (Custody.payload dep.deploymentId 0 rStar) sigStar = true →
      ∃ h : Fin n, S.mem h = true ∧ dep.Corrupt.mem h = false ∧
        (Custody.BurnedApproval (dep.policies h) (st.vaults h) rStar ∨
         (rStar ∉ (st.vaults h).attempted ∧
          prodEufCmaWin cfg.suite cfg.params
            ⟨validatorSk, Custody.queries cfg dep.deploymentId 0 (st.vaults h),
             Custody.payload dep.deploymentId 0 rStar, sigStar⟩ = true ∧
          (Nonempty (ProdTcrWitness cfg.suite cfg.params validatorSk
             (Custody.signingLog cfg validatorSk dep.deploymentId 0 (st.vaults h))
             (Custody.payload dep.deploymentId 0 rStar) sigStar) ∨
           ProdPreimageBreak cfg.suite cfg.params validatorSk
             (Custody.signingLog cfg validatorSk dep.deploymentId 0 (st.vaults h))
             (Custody.payload dep.deploymentId 0 rStar) sigStar)))) := by
  intro st validatorPqPk
  have hInv := runShamirCustodyTrace_inv dep trace
  refine ⟨?_, ?_⟩
  · intro r
    have hEq := thresholdProductionStatefulSign_eq_evalProductionStatefulSign
      cfg.suite cfg.params o validatorSk hMatch (Custody.payload dep.deploymentId 0 r)
      cfg.randomness r.leaf cfg.grindLimit
    refine ⟨hEq, fun sig hSome => ?_⟩
    rw [hEq] at hSome
    exact verifyProductionPqHashSig_evalProductionStatefulSign cfg.suite cfg.params
      validatorSk (Custody.payload dep.deploymentId 0 r) cfg.randomness r.leaf cfg.grindLimit sig hSome
  · intro S rStar sigStar hCardS hVer
    have hDiffPos : 0 < maskCard (maskDiff S dep.Corrupt) := by
      have hGe := maskCard_diff_ge S dep.Corrupt; omega
    let ⟨h, hh⟩ := extractMaskMember (maskDiff S dep.Corrupt) hDiffPos
    simp only [maskDiff, Bool.and_eq_true, Bool.not_eq_true'] at hh
    refine ⟨h, hh.1, hh.2, ?_⟩
    have hSafeH := hInv.vaultSafe h
    by_cases hAtt : rStar ∈ (st.vaults h).attempted
    · exact .inl (Custody.attempted_approved (dep.policies h) (dep.caps h) (st.vaults h)
        hSafeH rStar hAtt)
    · right
      have hWin : prodEufCmaWin cfg.suite cfg.params
          ⟨validatorSk, Custody.queries cfg dep.deploymentId 0 (st.vaults h),
           Custody.payload dep.deploymentId 0 rStar, sigStar⟩ = true :=
        Custody.accepted_fresh_certificate_wins cfg validatorSk dep.deploymentId 0 (st.vaults h) rStar sigStar
          hAtt ((Custody.verify_eq _ _ _ _ _ _).trans hVer)
      have hWit := production_stateful_forgery_witness cfg.suite cfg.params validatorSk
        (Custody.queries cfg dep.deploymentId 0 (st.vaults h)) (Custody.payload dep.deploymentId 0 rStar) sigStar hw hst
        (Custody.queries_one_time cfg dep.deploymentId 0 (dep.policies h) (dep.caps h) (st.vaults h) hSafeH)
        (Custody.signingLog_eq cfg validatorSk dep.deploymentId 0 (st.vaults h) ▸
          Custody.log_fresh_of_not_attempted cfg validatorSk dep.deploymentId 0 (st.vaults h) rStar hAtt) hVer
      rw [Custody.signingLog_eq]
      exact ⟨hAtt, hWin, hWit⟩

/-- Every trace of a Shamir custodian started from a `Custody.Safe` vault is a trace of the
    abstract mediation-vault machine started from a `Custody.Safe` vault, with the same accepted
    inputs and outputs. -/
theorem shamirCustodianRefines_preserves_traces {n L d : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (macKeys : Fin n → Fin n → Digest256)
    (masterSeed : Digest256)
    (polyTape : UInt64 → PreSteppedDigest256ShamirTape d L)
    (evalPt : TowerElem 7) (party : Fin n)
    (q deploymentId : Nat) (policy : Custody.RoundPolicy) (cap : Nat)
    (tr : List (ShamirVaultMachineInput n L × ShamirVaultMachineOutput n L))
    (hAdmits : (shamirCustodianMachine H MAC macKeys masterSeed polyTape evalPt party q
      deploymentId policy cap).AdmitsTrace tr) :
    (abstractMediationVaultMachine H MAC macKeys masterSeed polyTape evalPt party q
      deploymentId policy cap).AdmitsTrace tr :=
  (shamirCustodianRefines H MAC macKeys masterSeed polyTape evalPt party q deploymentId
    policy cap).preserve_admitsTrace hAdmits

/-! Lagrange completeness derived from deployment well-formedness. -/
/-- **Lagrange completeness.** In a well-formed deployment, any duplicate-free list of at least
    `t` custodians reconstructs the constant term of every sharing polynomial from its
    evaluations at their points, with the weights `dep.lagrangeWeights`. -/
theorem wellFormed_lagrange_reconstructs {n L d : Nat}
    {dep : ShamirValidatorDeployment n L d} (hWf : dep.WellFormed)
    (parties : List (Fin n)) (hNd : parties.Nodup) (hThr : dep.t ≤ parties.length)
    (c₀ : TowerElem 7) (tail : ShamirPadPoly (TowerElem 7) d) :
    ringDot (dep.lagrangeWeights parties)
      ((parties.map dep.evalPts).map (fun x => RoundPoly.evalCoeffs (c₀ :: tail.1) x)) = c₀ := by
  have hPts : (parties.map dep.evalPts).Nodup :=
    nodup_map_of_injective dep.evalPts hWf.evalPts_injective parties hNd
  have hLen : (parties.map dep.evalPts).length = parties.length := List.length_map _
  have hT : d + 1 ≤ parties.length := hWf.threshold_degree ▸ hThr
  have hRec := lagrange_to_additive_reconstructs_poly (parties.map dep.evalPts).length
    (hLen ▸ Nat.le_trans (Nat.succ_le_succ (Nat.zero_le d)) hT) (parties.map dep.evalPts) hPts rfl
    (c₀ :: tail.1) (by
      rw [List.length_cons, tail.2, hLen]
      exact hT)
  rw [RoundPoly.evalCoeffs_cons, LawfulCommRing.zero_mul, LawfulCommRing.add_zero] at hRec
  unfold ShamirValidatorDeployment.lagrangeWeights
  rw [ringDot_map_map]
  have hFun : (fun x => CommRingOps.mul (lagrangeWeightAtZero (parties.map dep.evalPts) x)
        (RoundPoly.evalCoeffs (c₀ :: tail.1) x)) =
      (fun xi => lagrangeToAdditiveShare (parties.map dep.evalPts) xi
        (RoundPoly.evalCoeffs (c₀ :: tail.1) xi)) :=
    by
      funext xi
      exact (lagrangeToAdditiveShare_eq _ _ _).symm
  rw [hFun]
  exact hRec

/-- **Threshold completeness from deployment well-formedness.** In a well-formed deployment, any
    duplicate-free list of at least `t` custodians that release their honest share openings for
    `(r, counter)` makes the combiner, run with the weights `dep.lagrangeWeights parties`, output
    the single-validator reference signature on `intentCanonicalPayload dep.deploymentId r`, and
    that signature verifies under the enrolled validator key. No interpolation identity is
    assumed. -/
theorem shamir_custody_wellFormed_quorum_signs {n L d : Nat}
    (dep : ShamirValidatorDeployment n L d) (hWf : dep.WellFormed)
    (hHeightLt : dep.height < 256)
    (hChainBound : 32 * L < 256 ^ 8) :
    let pk := dep.validatorPk
    ∀ (parties : List (Fin n)) (r : Custody.Intent) (counter : UInt32),
      parties.Nodup → dep.t ≤ parties.length →
      let gLeaf := UInt64.ofNat r.leaf
      let msg := intentCanonicalPayload dep.deploymentId r
      let digits := dep.digitsOf (quorumCounterDigest dep.H (quorumMessageHash dep.H pk gLeaf msg) counter)
      let digitsFn : Fin L → Fin 4 := fun i => digits.getD i.1 ⟨0, by decide⟩
      let leafChainPk : Fin L → Digest256 := fun i =>
        wotsChainIter (quorumChainStep dep.H pk.pkSeed gLeaf) i.1 0 3
          (quorumStageChainSk dep.H dep.masterSeed gLeaf (UInt32.ofNat i.1))
      let authPath := quorumAuthPath dep.H pk.pkSeed
        (quorumHonestLeafDigest L dep.H dep.masterSeed) dep.height 0 gLeaf.toNat
      let openings := parties.map (fun p =>
        computeShamirCustodianOpening dep.H dep.masterSeed dep.polyTape (dep.evalPts p)
          p r counter digitsFn)
      r.leaf < 2 ^ dep.height →
      r.leaf < 2 ^ 64 →
      counter.toNat < 2 ^ 16 →
      digits.length = L →
      ((digits.map Fin.val).foldr (· + ·) 0) = dep.targetSum →
      combinePreSteppedShamirValidatorSig L dep.targetSum dep.deploymentId dep.H pk dep.digitsOf
        leafChainPk (dep.lagrangeWeights parties) r counter
          (assembleSubmittedSharesFromOpenings openings) authPath =
          some (quorumJortsReferenceSign dep.H dep.masterSeed gLeaf counter digits authPath) ∧
      verifyQuorumJortsSigAt L dep.targetSum dep.H pk dep.digitsOf msg
        (quorumJortsReferenceSign dep.H dep.masterSeed gLeaf counter digits authPath) = true := by
  intro pk parties r counter hNd hThr
  exact (shamir_custody_combined_sig_verifies_or_collision dep hHeightLt hChainBound).1 parties
    (dep.lagrangeWeights parties) r counter
    (fun c₀ tail => wellFormed_lagrange_reconstructs hWf parties hNd hThr c₀ tail)

/-- **Quorum invariance from deployment well-formedness.** Any two duplicate-free lists of at
    least `t` custodians reconstruct the same combiner output for the same `(r, counter)`. -/
theorem shamir_custody_wellFormed_quorum_invariance {n L d : Nat}
    (dep : ShamirValidatorDeployment n L d) (hWf : dep.WellFormed)
    (hHeightLt : dep.height < 256)
    (hChainBound : 32 * L < 256 ^ 8) :
    let pk := dep.validatorPk
    ∀ (parties₁ parties₂ : List (Fin n)) (r : Custody.Intent) (counter : UInt32),
      parties₁.Nodup → dep.t ≤ parties₁.length →
      parties₂.Nodup → dep.t ≤ parties₂.length →
      let gLeaf := UInt64.ofNat r.leaf
      let msg := intentCanonicalPayload dep.deploymentId r
      let digits := dep.digitsOf (quorumCounterDigest dep.H (quorumMessageHash dep.H pk gLeaf msg) counter)
      let digitsFn : Fin L → Fin 4 := fun i => digits.getD i.1 ⟨0, by decide⟩
      let leafChainPk : Fin L → Digest256 := fun i =>
        wotsChainIter (quorumChainStep dep.H pk.pkSeed gLeaf) i.1 0 3
          (quorumStageChainSk dep.H dep.masterSeed gLeaf (UInt32.ofNat i.1))
      let authPath := quorumAuthPath dep.H pk.pkSeed
        (quorumHonestLeafDigest L dep.H dep.masterSeed) dep.height 0 gLeaf.toNat
      let ops₁ := parties₁.map (fun p =>
        computeShamirCustodianOpening dep.H dep.masterSeed dep.polyTape (dep.evalPts p)
          p r counter digitsFn)
      let ops₂ := parties₂.map (fun p =>
        computeShamirCustodianOpening dep.H dep.masterSeed dep.polyTape (dep.evalPts p)
          p r counter digitsFn)
      r.leaf < 2 ^ dep.height →
      r.leaf < 2 ^ 64 →
      counter.toNat < 2 ^ 16 →
      digits.length = L →
      ((digits.map Fin.val).foldr (· + ·) 0) = dep.targetSum →
      combinePreSteppedShamirValidatorSig L dep.targetSum dep.deploymentId dep.H pk dep.digitsOf
        leafChainPk (dep.lagrangeWeights parties₁) r counter
          (assembleSubmittedSharesFromOpenings ops₁) authPath =
      combinePreSteppedShamirValidatorSig L dep.targetSum dep.deploymentId dep.H pk dep.digitsOf
        leafChainPk (dep.lagrangeWeights parties₂) r counter
          (assembleSubmittedSharesFromOpenings ops₂) authPath := by
  intro pk parties₁ parties₂ r counter hNd₁ hThr₁ hNd₂ hThr₂
  exact (shamir_custody_combined_sig_verifies_or_collision dep hHeightLt hChainBound).2.1
    parties₁ parties₂ (dep.lagrangeWeights parties₁) (dep.lagrangeWeights parties₂) r counter
    (fun c₀ tail => wellFormed_lagrange_reconstructs hWf parties₁ hNd₁ hThr₁ c₀ tail)
    (fun c₀ tail => wellFormed_lagrange_reconstructs hWf parties₂ hNd₂ hThr₂ c₀ tail)


#export_eqns checkLatchCertifiedBurn releaseShamirShareFromVault ShamirValidatorDeployment.vaultIdentity intentCanonicalPayload ShamirValidatorDeployment.lagrangeWeights

end Qsag
end

set_option maxRecDepth 4096
#verify_constructive Qsag.shamirCustodianRefines_preserves_traces
#verify_constructive Qsag.runShamirCustodyTrace_identity
#verify_constructive Qsag.ShamirValidatorDeployment.WellFormed.quorum_exists
#verify_constructive Qsag.shamir_custody_wellFormed_epoch_non_equivocation
#verify_constructive Qsag.ShamirValidatorDeployment.WellFormed.corrupt_shares_independent_of_secret
#verify_constructive Qsag.shamir_custody_epoch_non_equivocation
#verify_constructive Qsag.shamir_custody_combined_sig_verifies_or_collision
#verify_constructive Qsag.shamir_custody_single_validator_pq_bridge

#verify_constructive Qsag.wellFormed_lagrange_reconstructs Qsag.shamir_custody_wellFormed_quorum_signs Qsag.shamir_custody_wellFormed_quorum_invariance
