module

public import Qsag.MirSpecBridgeCore
import all Qsag.MirSpecBridgeCore

/-! Concrete accepted traces and mutation witnesses for the four-layer model.
Kept separate from the simulation core to bound kernel elaboration memory. -/

public section
namespace Qsag
attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
-- Concrete cryptographic witnesses are checked sequentially to bound peak memory.
set_option Elab.async false
set_option autoImplicit false
set_option pp.maxSteps 1000
set_option maxRecDepth 65536

/- Shared concrete witness data; named constants bound kernel expansion. -/
def FourLayerWitness.ZeroGate.forgedZeroWire : Round2WireOpening :=
  ⟨0, towerOne 7, towerZero 7⟩

def FourLayerWitness.ZeroGate.missingWire : Round2WireOpening :=
  ⟨1, towerOne 7, towerOne 7⟩

def FourLayerWitness.ZeroGate.op1 :=
  mkSampleRound1Opening 11 22 0 1 1000

def FourLayerWitness.ZeroGate.op2 :=
  mkSampleRound1Opening 12 23 0 2 2000

def FourLayerWitness.ZeroGate.op3 :=
  mkSampleRound1Opening 13 24 0 3 3000

def FourLayerWitness.ZeroGate.quorum1 : List (Fin 4) :=
  [⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩]

def FourLayerWitness.ZeroGate.tx1 : MirTxIntent :=
  ⟨sampleRecipient, 40, 7, samplePolPin, sampleAuthPin, 10, 0⟩

def FourLayerWitness.ZeroGate.msg1 :=
  encodeTransactionIntent FourLayerWitness.ZeroGate.tx1.toTransactionIntent

def FourLayerWitness.ZeroGate.forgedReq : FourLayerReq 4 :=
  { tx := FourLayerWitness.ZeroGate.tx1
    reqEpoch := 0
    quorum := FourLayerWitness.ZeroGate.quorum1
    quorumCert := mkSampleQuorumCert FourLayerWitness.ZeroGate.quorum1 0 FourLayerWitness.ZeroGate.msg1
    round1Openings := [FourLayerWitness.ZeroGate.op1, FourLayerWitness.ZeroGate.op2, FourLayerWitness.ZeroGate.op3]
    round2Wires := [FourLayerWitness.ZeroGate.forgedZeroWire] }

def FourLayerWitness.ZeroGate.s1₀ : Layer1ElfState :=
  { mem := sampleElfMem
    windowId := 7
    velocityWindowCap := 100
    accumulatedSpend := 0
    burnedNonces := []
    allowedRecipients := [sampleRecipient]
    perTxCap := 60
    belt := ⟨samplePkPin, 0, none, false⟩
    cutPoisoned := false
    sharePresent := true
    activeSessionTag := Goldilocks.ofNat 0
    storedRound1Commits := [(1, FourLayerWitness.ZeroGate.op1.committedB0), (2, FourLayerWitness.ZeroGate.op2.committedB0), (3, FourLayerWitness.ZeroGate.op3.committedB0)]
    verifierBginAlpha := sampleBginAlpha
    verifierBginKeyOffsets := sampleBginOffsets
    quorumCertConfig := sampleQuorumCertConfig }

abbrev FourLayerWitness.ZeroGate.M1 :=
  layer1CompiledElfMachine (n := 4) 3 samplePkPin
    (fun m msg => signFromCustodianShare1WithPeers (readShareMem32 m) msg)

/-- **`#tooth` Session-Gate Refutation 1 (`tooth_caller_zero_bgin_relation_rejected`)**:
    1. Setting `verifierBginAlpha = 0` (`towerZero 7`) is unconditionally rejected,
    2. Under honest verifier keys `(verifierBginAlpha = towerX 7, storedKeyOffset_0 = towerOne 7)`,
       a forged zero-MAC wire opening `(wireId = 0, xWire = 1, macShare = 0)` is rejected by
       `verifySessionBginBatch`, rejected by `layer1CompiledElfMachine` (`step = none`), sets
       `cutPoisoned = true`, and physically zeroes all 32 share bytes `[0x180, 0x1A0)`. -/
theorem tooth_caller_zero_bgin_relation_rejected :
    let forgedZeroWire : Round2WireOpening := FourLayerWitness.ZeroGate.forgedZeroWire
    let missingWire : Round2WireOpening := FourLayerWitness.ZeroGate.missingWire
    let forgedReq : FourLayerReq 4 := FourLayerWitness.ZeroGate.forgedReq
    let s1₀ : Layer1ElfState := FourLayerWitness.ZeroGate.s1₀
    let M1 := FourLayerWitness.ZeroGate.M1
    (∀ offsets wires, verifySessionBginBatch (towerZero 7) offsets wires = false) ∧
    verifySessionBginBatch sampleBginAlpha sampleBginOffsets sampleHonestBginWires = true ∧
    verifySessionBginBatch sampleBginAlpha sampleBginOffsets [forgedZeroWire] = false ∧
    verifySessionBginBatch sampleBginAlpha sampleBginOffsets [missingWire] = false ∧
    M1.step s1₀ forgedReq = none ∧
    (M1.errStep s1₀ forgedReq).cutPoisoned = true ∧
    (∀ i : Nat, i < 32 →
      (M1.errStep s1₀ forgedReq).mem (UInt64.ofNat 0x180 + UInt64.ofNat i) = 0) := by
  intro forgedZeroWire missingWire forgedReq s1₀ M1
  let op1 := FourLayerWitness.ZeroGate.op1
  let op2 := FourLayerWitness.ZeroGate.op2
  let op3 := FourLayerWitness.ZeroGate.op3
  let quorum1 : List (Fin 4) := FourLayerWitness.ZeroGate.quorum1
  let tx1 : MirTxIntent := FourLayerWitness.ZeroGate.tx1
  let msg1 := FourLayerWitness.ZeroGate.msg1
  have hZeroAlpha : ∀ offsets wires, verifySessionBginBatch (towerZero 7) offsets wires = false := by
    qsag_aux_lemma =>
      intro offsets wires
      unfold verifySessionBginBatch
      have hF : decide (towerZero 7 ≠ towerZero 7) = false := by decide
      rw [hF]
      rfl
  obtain ⟨hPinPol, hPinAuth, _⟩ := sampleElfMem_pins
  have hCtPol : execElfCtEq32 sampleElfMem (UInt64.ofNat 0x100) samplePolPin = true := by
    qsag_aux_lemma =>
      rw [execElfCtEq32_spec (pinned := samplePolPin) rfl (by omega) hPinPol]; rfl
  have hCtAuth : execElfCtEq32 sampleElfMem (UInt64.ofNat 0x140) sampleAuthPin = true := by
    qsag_aux_lemma =>
      rw [execElfCtEq32_spec (pinned := sampleAuthPin) rfl (by omega) hPinAuth]; rfl
  have hQCert : verifyFourLayerQuorumCert sampleQuorumCertConfig 3 samplePkPin msg1 forgedReq = true := by
    qsag_aux_lemma =>
      exact sampleQuorumCert_valid rfl (by decide) (by decide)
  have hBginFalse : verifySessionBginBatch sampleBginAlpha sampleBginOffsets [forgedZeroWire] = false := by
    qsag_aux_lemma =>
      unfold verifySessionBginBatch verifySessionBginWire bginRelationHolds lookupBginKeyOffset
        sampleBginAlpha sampleBginOffsets
      dsimp only [forgedZeroWire, FourLayerWitness.ZeroGate.forgedZeroWire, List.all, List.any, List.find?, List.isEmpty, List.map]
      simp only [towerMul_one]
      decide
  have hMissingWireFalse :
      verifySessionBginBatch sampleBginAlpha sampleBginOffsets [missingWire] = false := by
    qsag_aux_lemma =>
      unfold verifySessionBginBatch sampleBginAlpha sampleBginOffsets
      dsimp only [missingWire, FourLayerWitness.ZeroGate.missingWire, List.all, List.any, List.isEmpty, List.map]
      decide
  have hPreCutFalse :
      verifyPreCutTranscript (Goldilocks.ofNat 0)
        [(1, op1.committedB0), (2, op2.committedB0), (3, op3.committedB0)]
        sampleBginAlpha sampleBginOffsets quorum1 [op1, op2, op3] [forgedZeroWire] = false := by
    qsag_aux_lemma =>
      unfold verifyPreCutTranscript
      rw [hBginFalse, Bool.and_false]
  have hOutcome :
      M1.step s1₀ forgedReq = none ∧
      (M1.errStep s1₀ forgedReq).cutPoisoned = true ∧
      (∀ i : Nat, i < 32 →
        (M1.errStep s1₀ forgedReq).mem (UInt64.ofNat 0x180 + UInt64.ofNat i) = 0) := by
    qsag_aux_lemma =>
      exact layer1_preCut_failure 3 samplePkPin
        (fun m msg => signFromCustodianShare1WithPeers (readShareMem32 m) msg)
        s1₀ forgedReq (by decide) (by decide) hCtPol hCtAuth
        (by exact .head _) (by decide) (by decide) (by decide) hQCert
        (by decide) hPreCutFalse
  exact ⟨hZeroAlpha, sampleHonestBginWires_ok, hBginFalse, hMissingWireFalse,
    hOutcome.1, hOutcome.2.1, hOutcome.2.2⟩

/- Shared concrete witness data; named constants bound kernel expansion. -/
def FourLayerWitness.Unregistered.op1 :=
  mkSampleRound1Opening 11 22 0 1 1000

def FourLayerWitness.Unregistered.op2 :=
  mkSampleRound1Opening 12 23 0 2 2000

def FourLayerWitness.Unregistered.op3 :=
  mkSampleRound1Opening 13 24 0 3 3000

def FourLayerWitness.Unregistered.op0 :=
  mkSampleRound1Opening 14 25 0 0 4000

def FourLayerWitness.Unregistered.quorum1 : List (Fin 4) :=
  [⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩]

def FourLayerWitness.Unregistered.wrongStored : List (Nat × Lane4) :=
  [(2, FourLayerWitness.Unregistered.op2.committedB0), (3, FourLayerWitness.Unregistered.op3.committedB0), (0, FourLayerWitness.Unregistered.op0.committedB0)]

def FourLayerWitness.Unregistered.rightStored : List (Nat × Lane4) :=
  [(1, FourLayerWitness.Unregistered.op1.committedB0), (2, FourLayerWitness.Unregistered.op2.committedB0), (3, FourLayerWitness.Unregistered.op3.committedB0)]

def FourLayerWitness.Unregistered.tx1 : MirTxIntent :=
  ⟨sampleRecipient, 40, 7, samplePolPin, sampleAuthPin, 10, 0⟩

def FourLayerWitness.Unregistered.msg1 :=
  encodeTransactionIntent FourLayerWitness.Unregistered.tx1.toTransactionIntent

def FourLayerWitness.Unregistered.unregReq : FourLayerReq 4 :=
  { tx := FourLayerWitness.Unregistered.tx1
    reqEpoch := 0
    quorum := FourLayerWitness.Unregistered.quorum1
    quorumCert := mkSampleQuorumCert FourLayerWitness.Unregistered.quorum1 0 FourLayerWitness.Unregistered.msg1
    round1Openings := [FourLayerWitness.Unregistered.op1, FourLayerWitness.Unregistered.op2, FourLayerWitness.Unregistered.op3]
    round2Wires := sampleHonestBginWires }

def FourLayerWitness.Unregistered.s1Unreg : Layer1ElfState :=
  { mem := sampleElfMem
    windowId := 7
    velocityWindowCap := 100
    accumulatedSpend := 0
    burnedNonces := []
    allowedRecipients := [sampleRecipient]
    perTxCap := 60
    belt := ⟨samplePkPin, 0, none, false⟩
    cutPoisoned := false
    sharePresent := true
    activeSessionTag := Goldilocks.ofNat 0
    storedRound1Commits := FourLayerWitness.Unregistered.wrongStored
    verifierBginAlpha := sampleBginAlpha
    verifierBginKeyOffsets := sampleBginOffsets
    quorumCertConfig := sampleQuorumCertConfig }

abbrev FourLayerWitness.Unregistered.M1 :=
  layer1CompiledElfMachine (n := 4) 3 samplePkPin
    (fun m msg => signFromCustodianShare1WithPeers (readShareMem32 m) msg)

namespace FourLayerWitness.UnregisteredProof
open FourLayerWitness.Unregistered

private theorem hVerOp1 : verifyRound1Opening op1 = true := verifyRound1Opening_of_eq rfl
private theorem hEmptyFalse :
    verifySessionRound1Openings (Goldilocks.ofNat 0) [] quorum1 [op1, op2, op3] = false := by
  qsag_aux_lemma =>
    unfold verifySessionRound1Openings
    change (((0 : Nat) == 3) && _ && _ && _ && _) = false
    simp only [show ((0 : Nat) == 3) = false from rfl, Bool.false_and]
private theorem hNotMem1 : (1, op1.committedB0) ∉ wrongStored.take 3 := by
  qsag_aux_lemma =>
    intro hMem
    dsimp only [wrongStored, FourLayerWitness.Unregistered.wrongStored, List.take] at hMem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with hEq | hEq | hEq
    · injection hEq with hNat _; omega
    · injection hEq with hNat _; omega
    · injection hEq with hNat _; omega
private theorem hWrongStoredFalse :
    verifySessionRound1Openings (Goldilocks.ofNat 0) wrongStored quorum1 [op1, op2, op3] = false := by
  qsag_aux_lemma =>
    unfold verifySessionRound1Openings
    dsimp only
    have hAllF :
        ([op1, op2, op3].all (fun op =>
          decide (op.sessionTag = Goldilocks.ofNat 0) &&
          decide ((op.partyId.val, op.committedB0) ∈ wrongStored.take quorum1.length) &&
          verifyRound1Opening op)) = false := by
      simp only [List.all_cons, List.all_nil]
      have hDecF : decide ((op1.partyId.val, op1.committedB0) ∈ wrongStored.take quorum1.length) = false :=
        decide_eq_false hNotMem1
      rw [hDecF]
      simp
    rw [hAllF, Bool.and_false]
private theorem hWrongSessionFalse :
    verifySessionRound1Openings (Goldilocks.ofNat 1) rightStored quorum1 [op1, op2, op3] = false := by
  qsag_aux_lemma =>
    unfold verifySessionRound1Openings
    dsimp only
    have hAllF :
        ([op1, op2, op3].all (fun op =>
          decide (op.sessionTag = Goldilocks.ofNat 1) &&
          decide ((op.partyId.val, op.committedB0) ∈ rightStored.take quorum1.length) &&
          verifyRound1Opening op)) = false := by
      dsimp only [List.all]
      have hTagF : decide (op1.sessionTag = Goldilocks.ofNat 1) = false := by decide
      rw [hTagF]
      simp
    rw [hAllF, Bool.and_false]
private theorem hCtPol : execElfCtEq32 sampleElfMem (UInt64.ofNat 0x100) samplePolPin = true := by
  qsag_aux_lemma =>
    rw [execElfCtEq32_spec (pinned := samplePolPin) rfl (by omega) sampleElfMem_pins.1]; rfl
private theorem hCtAuth : execElfCtEq32 sampleElfMem (UInt64.ofNat 0x140) sampleAuthPin = true := by
  qsag_aux_lemma =>
    rw [execElfCtEq32_spec (pinned := sampleAuthPin) rfl (by omega) sampleElfMem_pins.2.1]; rfl
private theorem hQCert : verifyFourLayerQuorumCert sampleQuorumCertConfig 3 samplePkPin msg1 unregReq = true := by
  qsag_aux_lemma =>
    exact sampleQuorumCert_valid rfl (by decide) (by decide)
private theorem hPreCutFalse :
    verifyPreCutTranscript (Goldilocks.ofNat 0) wrongStored sampleBginAlpha sampleBginOffsets
      quorum1 [op1, op2, op3] sampleHonestBginWires = false := by
  qsag_aux_lemma =>
    unfold verifyPreCutTranscript
    rw [hWrongStoredFalse, Bool.false_and]
private theorem hOutcome :
    M1.step s1Unreg unregReq = none ∧
    (M1.errStep s1Unreg unregReq).cutPoisoned = true ∧
    (∀ i : Nat, i < 32 →
      (M1.errStep s1Unreg unregReq).mem (UInt64.ofNat 0x180 + UInt64.ofNat i) = 0) := by
  qsag_aux_lemma =>
    with_reducible exact (layer1_preCut_failure 3 samplePkPin
      (fun m msg => signFromCustodianShare1WithPeers (readShareMem32 m) msg)
      s1Unreg unregReq (by decide) (by decide) (by simpa only [s1Unreg, unregReq, tx1] using hCtPol)
      (by simpa only [s1Unreg, unregReq, tx1] using hCtAuth)
      (by simpa only [s1Unreg, unregReq, tx1] using (show sampleRecipient ∈ [sampleRecipient] from List.Mem.head _)) (by decide) (by decide) (by decide)
      (by simpa only [s1Unreg, unregReq, tx1, msg1] using hQCert)
      (by decide) (by simpa only [s1Unreg, unregReq] using hPreCutFalse))
end FourLayerWitness.UnregisteredProof

/-- **`#tooth` Session-Gate Refutation 2 (`tooth_unregistered_round1_commitment_rejected`)**:
    1. A self-consistent fresh opening (`verifyRound1Opening = true`) submitted with empty
       `storedRound1Commits = []` is rejected,
    2. A self-consistent fresh opening for quorum member `1` absent from the stored batch
       `[(2, c2), (3, c3), (0, c0)]` is rejected (`step = none`, `cutPoisoned = true`, and
       `[0x180, 0x1A0)` wiped),
    3. Replaying a stored Session-`0` commitment under `activeSessionTag = 1` is rejected. -/
theorem tooth_unregistered_round1_commitment_rejected :
    let op1 := FourLayerWitness.Unregistered.op1
    let op2 := FourLayerWitness.Unregistered.op2
    let op3 := FourLayerWitness.Unregistered.op3
    let quorum1 : List (Fin 4) := FourLayerWitness.Unregistered.quorum1
    let wrongStored : List (Nat × Lane4) := FourLayerWitness.Unregistered.wrongStored
    let rightStored : List (Nat × Lane4) := FourLayerWitness.Unregistered.rightStored
    let unregReq : FourLayerReq 4 := FourLayerWitness.Unregistered.unregReq
    let s1Unreg : Layer1ElfState := FourLayerWitness.Unregistered.s1Unreg
    let M1 := FourLayerWitness.Unregistered.M1
    verifyRound1Opening op1 = true ∧
    verifySessionRound1Openings (Goldilocks.ofNat 0) [] quorum1 [op1, op2, op3] = false ∧
    verifySessionRound1Openings (Goldilocks.ofNat 0) wrongStored quorum1 [op1, op2, op3] = false ∧
    verifySessionRound1Openings (Goldilocks.ofNat 1) rightStored quorum1 [op1, op2, op3] = false ∧
    M1.step s1Unreg unregReq = none ∧
    (M1.errStep s1Unreg unregReq).cutPoisoned = true ∧
    (∀ i : Nat, i < 32 →
      (M1.errStep s1Unreg unregReq).mem (UInt64.ofNat 0x180 + UInt64.ofNat i) = 0) := by
  intro op1 op2 op3 quorum1 wrongStored rightStored unregReq s1Unreg M1
  with_reducible exact (⟨FourLayerWitness.UnregisteredProof.hVerOp1, FourLayerWitness.UnregisteredProof.hEmptyFalse, FourLayerWitness.UnregisteredProof.hWrongStoredFalse, FourLayerWitness.UnregisteredProof.hWrongSessionFalse,
    FourLayerWitness.UnregisteredProof.hOutcome.1, FourLayerWitness.UnregisteredProof.hOutcome.2.1, FourLayerWitness.UnregisteredProof.hOutcome.2.2⟩)

/- Shared concrete witness data; named constants bound kernel expansion. -/
def FourLayerWitness.Unauthenticated.corrupt : List (Fin 4) :=
  [⟨0, by decide⟩]

def FourLayerWitness.Unauthenticated.quorum2 : List (Fin 4) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩]

def FourLayerWitness.Unauthenticated.op0 :=
  mkSampleRound1Opening 31 41 0 0 5000

def FourLayerWitness.Unauthenticated.op1 :=
  mkSampleRound1Opening 32 42 0 1 6000

def FourLayerWitness.Unauthenticated.op2 :=
  mkSampleRound1Opening 33 43 0 2 7000

def FourLayerWitness.Unauthenticated.tx1 : MirTxIntent :=
  ⟨sampleRecipient, 40, 7, samplePolPin, sampleAuthPin, 10, 0⟩

def FourLayerWitness.Unauthenticated.msg1 :=
  encodeTransactionIntent FourLayerWitness.Unauthenticated.tx1.toTransactionIntent

def FourLayerWitness.Unauthenticated.missingCertReq : FourLayerReq 4 :=
  { tx := FourLayerWitness.Unauthenticated.tx1
    reqEpoch := 0
    quorum := FourLayerWitness.Unauthenticated.quorum2
    quorumCert :=
      [(⟨0, by decide⟩, computeValidatorAckTag (sampleValidatorAuthKey 0) 0 0 FourLayerWitness.Unauthenticated.msg1),
       (⟨2, by decide⟩, computeValidatorAckTag (sampleValidatorAuthKey 2) 2 0 FourLayerWitness.Unauthenticated.msg1)]
    round1Openings := [FourLayerWitness.Unauthenticated.op0, FourLayerWitness.Unauthenticated.op1, FourLayerWitness.Unauthenticated.op2]
    round2Wires := sampleHonestBginWires }

def FourLayerWitness.Unauthenticated.forgedTagReq : FourLayerReq 4 :=
  { tx := FourLayerWitness.Unauthenticated.tx1
    reqEpoch := 0
    quorum := FourLayerWitness.Unauthenticated.quorum2
    quorumCert :=
      [(⟨0, by decide⟩, computeValidatorAckTag (sampleValidatorAuthKey 0) 0 0 FourLayerWitness.Unauthenticated.msg1),
       (⟨1, by decide⟩, []),
       (⟨2, by decide⟩, computeValidatorAckTag (sampleValidatorAuthKey 2) 2 0 FourLayerWitness.Unauthenticated.msg1)]
    round1Openings := [FourLayerWitness.Unauthenticated.op0, FourLayerWitness.Unauthenticated.op1, FourLayerWitness.Unauthenticated.op2]
    round2Wires := sampleHonestBginWires }

def FourLayerWitness.Unauthenticated.s1₀ : Layer1ElfState :=
  { mem := sampleElfMem
    windowId := 7
    velocityWindowCap := 100
    accumulatedSpend := 0
    burnedNonces := []
    allowedRecipients := [sampleRecipient]
    perTxCap := 60
    belt := ⟨samplePkPin, 0, none, false⟩
    cutPoisoned := false
    sharePresent := true
    activeSessionTag := Goldilocks.ofNat 0
    storedRound1Commits := [(0, FourLayerWitness.Unauthenticated.op0.committedB0), (1, FourLayerWitness.Unauthenticated.op1.committedB0), (2, FourLayerWitness.Unauthenticated.op2.committedB0)]
    verifierBginAlpha := sampleBginAlpha
    verifierBginKeyOffsets := sampleBginOffsets
    quorumCertConfig := sampleQuorumCertConfig }

def FourLayerWitness.Unauthenticated.pol4₀ : StatefulPolicyGuard :=
  { window_id := 7
    velocity_window_cap := 100
    accumulated_spend := 0
    burned_intent_nonces := []
    pinned_policy_digest := samplePolPin
    pinned_authority_digest := sampleAuthPin
    allowed_recipients := [sampleRecipient]
    per_tx_cap := 60 }

def FourLayerWitness.Unauthenticated.s4₀ : Layer4IdealState (List UInt8) :=
  { policy := FourLayerWitness.Unauthenticated.pol4₀
    ideal := ⟨⟨samplePkPin, 3, 4, [0], [], []⟩, initWalLatchState samplePkPin, 0⟩
    activeSessionTag := Goldilocks.ofNat 0
    storedRound1Commits := [(0, FourLayerWitness.Unauthenticated.op0.committedB0), (1, FourLayerWitness.Unauthenticated.op1.committedB0), (2, FourLayerWitness.Unauthenticated.op2.committedB0)]
    verifierBginAlpha := sampleBginAlpha
    verifierBginKeyOffsets := sampleBginOffsets
    quorumCertConfig := sampleQuorumCertConfig }

abbrev FourLayerWitness.Unauthenticated.M1 :=
  layer1CompiledElfMachine (n := 4) 3 samplePkPin
    (fun m msg => signFromCustodianShare1WithPeers (readShareMem32 m) msg)

abbrev FourLayerWitness.Unauthenticated.M4 :=
  layer4IdealTsigMachine (PK := List UInt8) (n := 4) FourLayerWitness.Unauthenticated.corrupt id
    (fun msg => poseidon2TagBytes sampleSecretKeyBytes msg)

/-- **`#tooth` Session-Gate Refutation 3 (`tooth_unauthenticated_quorum_member_rejected`)**:
    Listing an honest party (`1`) in `req.quorum = [0, 1, 2]` either (a) without a matching entry
    in `req.quorumCert` or (b) with an unauthenticated/forged `ackTag := []` causes
    `verifyFourLayerQuorumCert = false` and immediate rejection (`step = none`) at both Layer 1
    (`layer1CompiledElfMachine`) and Layer 4 (`layer4IdealTsigMachine`). -/
theorem tooth_unauthenticated_quorum_member_rejected :
    let msg1 := FourLayerWitness.Unauthenticated.msg1
    let missingCertReq : FourLayerReq 4 := FourLayerWitness.Unauthenticated.missingCertReq
    let forgedTagReq : FourLayerReq 4 := FourLayerWitness.Unauthenticated.forgedTagReq
    let s1₀ : Layer1ElfState := FourLayerWitness.Unauthenticated.s1₀
    let s4₀ : Layer4IdealState (List UInt8) := FourLayerWitness.Unauthenticated.s4₀
    let M1 := FourLayerWitness.Unauthenticated.M1
    let M4 := FourLayerWitness.Unauthenticated.M4
    verifyFourLayerQuorumCert sampleQuorumCertConfig 3 samplePkPin msg1 missingCertReq = false ∧
    verifyFourLayerQuorumCert sampleQuorumCertConfig 3 samplePkPin msg1 forgedTagReq = false ∧
    M1.step s1₀ missingCertReq = none ∧
    M1.step s1₀ forgedTagReq = none ∧
    M4.step s4₀ missingCertReq = none ∧
    M4.step s4₀ forgedTagReq = none := by
  intro msg1 missingCertReq forgedTagReq s1₀ s4₀ M1 M4
  let corrupt : List (Fin 4) := FourLayerWitness.Unauthenticated.corrupt
  let quorum2 : List (Fin 4) := FourLayerWitness.Unauthenticated.quorum2
  let op0 := FourLayerWitness.Unauthenticated.op0
  let op1 := FourLayerWitness.Unauthenticated.op1
  let op2 := FourLayerWitness.Unauthenticated.op2
  let tx1 : MirTxIntent := FourLayerWitness.Unauthenticated.tx1
  let pol4₀ : StatefulPolicyGuard := FourLayerWitness.Unauthenticated.pol4₀
  have hMissingFalse :
      verifyFourLayerQuorumCert sampleQuorumCertConfig 3 samplePkPin msg1 missingCertReq = false := by
    qsag_aux_lemma =>
      unfold verifyFourLayerQuorumCert
      dsimp only
      have hSignersF :
          decide (BeltLatchCommitReq.signers
            ⟨samplePkPin, missingCertReq.reqEpoch, msg1, ByteArray.empty, missingCertReq.quorumCert⟩ =
            missingCertReq.quorum) = false := by decide
      simp only [hSignersF, Bool.false_and]
  have hEmptyAckNe : [] ≠ computeValidatorAckTag (sampleValidatorAuthKey 1) 1 0 msg1 := by
    qsag_aux_lemma =>
      intro hEq
      have hLen := congrArg List.length hEq
      unfold computeValidatorAckTag at hLen
      rw [poseidon2Hash32_length] at hLen
      cases hLen
  have hForgedAck1False :
      verifyValidatorAck sampleQuorumCertConfig (⟨1, by decide⟩ : Fin 4) 0 msg1 [] = false := by
    qsag_aux_lemma =>
      unfold verifyValidatorAck
      dsimp only
      have hLk : lookupValidatorAuthKey sampleQuorumCertConfig.validatorAuthKeys 1 =
          some (sampleValidatorAuthKey 1) := rfl
      rw [hLk]
      dsimp only
      have hTagF : decide ([] = computeValidatorAckTag (sampleValidatorAuthKey 1) 1 0 msg1) = false :=
        decide_eq_false hEmptyAckNe
      rw [hTagF, Bool.and_false]
  have hForgedFalse :
      verifyFourLayerQuorumCert sampleQuorumCertConfig 3 samplePkPin msg1 forgedTagReq = false := by
    qsag_aux_lemma =>
      unfold verifyFourLayerQuorumCert beltCertAuthenticated
      dsimp only
      have hAllF :
          forgedTagReq.quorumCert.all (fun e =>
            verifyValidatorAck sampleQuorumCertConfig e.1 forgedTagReq.reqEpoch msg1 e.2) = false := by
        dsimp only [forgedTagReq, FourLayerWitness.Unauthenticated.forgedTagReq, List.all]
        rw [hForgedAck1False]
        simp
      rw [hAllF]
      simp
  obtain ⟨hPinPol, hPinAuth, _⟩ := sampleElfMem_pins
  have hCtPol : execElfCtEq32 sampleElfMem (UInt64.ofNat 0x100) samplePolPin = true := by
    qsag_aux_lemma =>
      rw [execElfCtEq32_spec (pinned := samplePolPin) rfl (by omega) hPinPol]; rfl
  have hCtAuth : execElfCtEq32 sampleElfMem (UInt64.ofNat 0x140) sampleAuthPin = true := by
    qsag_aux_lemma =>
      rw [execElfCtEq32_spec (pinned := sampleAuthPin) rfl (by omega) hPinAuth]; rfl
  have hM1Rej : ∀ req : FourLayerReq 4,
      req.tx = tx1 →
      verifyFourLayerQuorumCert sampleQuorumCertConfig 3 samplePkPin msg1 req = false →
      M1.step s1₀ req = none := by
    qsag_aux_lemma =>
      intro req hTx hQF
      dsimp only [M1, FourLayerWitness.Unauthenticated.M1, layer1CompiledElfMachine, PartyMachine.ofOutcome, s1₀, FourLayerWitness.Unauthenticated.s1₀]
      rw [hTx]
      dsimp only [tx1, FourLayerWitness.Unauthenticated.tx1, msg1, FourLayerWitness.Unauthenticated.msg1] at hQF ⊢
      simp only [hCtPol, hCtAuth]
      rw [ite_eq_right (show ¬ ((false || false || !true) = true) by decide)]
      rw [ite_eq_right (show ¬ (((7 : UInt64) != (7 : UInt64)) = true) by decide)]
      rw [ite_eq_right (show ¬ ((!true) = true) by decide)]
      rw [ite_eq_right (show ¬ ((!true) = true) by decide)]
      rw [ite_eq_right (fun hn : ¬ (sampleRecipient ∈ [sampleRecipient]) => hn (.head _))]
      rw [ite_eq_right (show ¬ ¬ ((40 : UInt64).toNat ≤ (60 : UInt64).toNat) by decide)]
      rw [ite_eq_right (show ¬ ¬ ((40 : UInt64).toNat ≤ ((100 : UInt64) - (0 : UInt64)).toNat) by decide)]
      rw [ite_eq_right (show ¬ (u64MemBool 10 [] = true) by decide)]
      rw [hQF]
      simp only [Bool.not_false, ↓reduceIte]
  have hPol4Ok :
      policyGuardStep pol4₀ tx1.toTransactionIntent =
        .accepted
          { pol4₀ with accumulated_spend := 40, burned_intent_nonces := [10] }
          ⟨tx1.toTransactionIntent, msg1⟩ := by
    qsag_aux_lemma =>
      rfl
  have hM4Rej : ∀ req : FourLayerReq 4,
      req.tx = tx1 →
      verifyFourLayerQuorumCert sampleQuorumCertConfig 3 samplePkPin msg1 req = false →
      M4.step s4₀ req = none := by
    qsag_aux_lemma =>
      intro req hTx hQF
      dsimp only [M4, FourLayerWitness.Unauthenticated.M4, layer4IdealTsigMachine, PartyMachine.ofOutcome, s4₀, FourLayerWitness.Unauthenticated.s4₀, initWalLatchState]
      rw [hTx, ite_eq_right (by decide : ¬ (false = true)), hPol4Ok]
      dsimp only
      simp only [id_eq]
      rw [hQF, Bool.false_and]
      rfl
  exact ⟨hMissingFalse, hForgedFalse,
    hM1Rej missingCertReq rfl hMissingFalse,
    hM1Rej forgedTagReq rfl hForgedFalse,
    hM4Rej missingCertReq rfl hMissingFalse,
    hM4Rej forgedTagReq rfl hForgedFalse⟩

/- Shared concrete witness data; named constants bound kernel expansion. -/
def FourLayerWitness.Honest.corrupt : List (Fin 4) :=
  [⟨0, by decide⟩]

def FourLayerWitness.Honest.signFn : List UInt8 → List UInt8 → ByteArray :=
  signFromCustodianShare1WithPeers

def FourLayerWitness.Honest.dealt : Nat → Option (List UInt8) :=
  sampleDealtShares

def FourLayerWitness.Honest.assembleFn : (Nat → Option (List UInt8)) → List UInt8 → ByteArray :=
  assembleShamirThresholdSig

def FourLayerWitness.Honest.oracleFn : List UInt8 → ByteArray :=
  fun msg => poseidon2TagBytes sampleSecretKeyBytes msg

theorem FourLayerWitness.Honest.hSigM : ∀ msg : List UInt8, FourLayerWitness.Honest.assembleFn FourLayerWitness.Honest.dealt msg = FourLayerWitness.Honest.signFn sampleCustodianShare1 msg :=
  sampleShares_distinct_and_reconstruct.2.2.2.2.2.2.2.1

theorem FourLayerWitness.Honest.hOraE : ∀ msg : List UInt8, FourLayerWitness.Honest.assembleFn FourLayerWitness.Honest.dealt msg = FourLayerWitness.Honest.oracleFn msg :=
  sampleShares_distinct_and_reconstruct.2.2.2.2.2.2.2.2

def FourLayerWitness.Honest.sim :=
  isa_to_mir_to_protocol_to_ideal_sim
    (PK := List UInt8) (n := 4) (q := 3) (f := 1)
    FourLayerWitness.Honest.corrupt id samplePkPin FourLayerWitness.Honest.dealt sampleCustodianShare1 FourLayerWitness.Honest.signFn FourLayerWitness.Honest.assembleFn FourLayerWitness.Honest.oracleFn
    (by decide) (by decide) (by decide) (by decide) (by decide)
    FourLayerWitness.Honest.hSigM FourLayerWitness.Honest.hOraE

def FourLayerWitness.Honest.op1_s0 :=
  mkSampleRound1Opening 11 22 0 1 1000

def FourLayerWitness.Honest.op2_s0 :=
  mkSampleRound1Opening 12 23 0 2 2000

def FourLayerWitness.Honest.op3_s0 :=
  mkSampleRound1Opening 13 24 0 3 3000

def FourLayerWitness.Honest.op0_s1 :=
  mkSampleRound1Opening 31 41 1 0 4000

def FourLayerWitness.Honest.op1_s1 :=
  mkSampleRound1Opening 32 42 1 1 5000

def FourLayerWitness.Honest.op2_s1 :=
  mkSampleRound1Opening 33 43 1 2 6000

def FourLayerWitness.Honest.stored₀ : List (Nat × Lane4) :=
  [(1, FourLayerWitness.Honest.op1_s0.committedB0), (2, FourLayerWitness.Honest.op2_s0.committedB0), (3, FourLayerWitness.Honest.op3_s0.committedB0),
   (0, FourLayerWitness.Honest.op0_s1.committedB0), (1, FourLayerWitness.Honest.op1_s1.committedB0), (2, FourLayerWitness.Honest.op2_s1.committedB0)]

def FourLayerWitness.Honest.stored₁ : List (Nat × Lane4) :=
  [(0, FourLayerWitness.Honest.op0_s1.committedB0), (1, FourLayerWitness.Honest.op1_s1.committedB0), (2, FourLayerWitness.Honest.op2_s1.committedB0)]

def FourLayerWitness.Honest.belt0 : MirBeltLatchState :=
  ⟨samplePkPin, 0, none, false⟩

def FourLayerWitness.Honest.s1₀ : Layer1ElfState :=
  { mem := sampleElfMem
    windowId := 7
    velocityWindowCap := 100
    accumulatedSpend := 0
    burnedNonces := []
    allowedRecipients := [sampleRecipient]
    perTxCap := 60
    belt := FourLayerWitness.Honest.belt0
    cutPoisoned := false
    sharePresent := true
    activeSessionTag := Goldilocks.ofNat 0
    storedRound1Commits := FourLayerWitness.Honest.stored₀
    verifierBginAlpha := sampleBginAlpha
    verifierBginKeyOffsets := sampleBginOffsets
    quorumCertConfig := sampleQuorumCertConfig }

def FourLayerWitness.Honest.pol2₀ : MirPolicyGuardState :=
  { windowId := 7
    velocityWindowCap := 100
    accumulatedSpend := 0
    burnedNonces := []
    pinnedPolicyDigest := samplePolPin
    pinnedAuthorityDigest := sampleAuthPin
    allowedRecipients := [sampleRecipient]
    perTxCap := 60 }

def FourLayerWitness.Honest.s2₀ : Layer2MirState :=
  { policy := FourLayerWitness.Honest.pol2₀
    belt := FourLayerWitness.Honest.belt0
    cut := MirRssCutSession.round1Committed zeroBytes32 zeroBytes32
    shareBytes := some sampleCustodianShare1
    activeSessionTag := Goldilocks.ofNat 0
    storedRound1Commits := FourLayerWitness.Honest.stored₀
    verifierBginAlpha := sampleBginAlpha
    verifierBginKeyOffsets := sampleBginOffsets
    quorumCertConfig := sampleQuorumCertConfig }

