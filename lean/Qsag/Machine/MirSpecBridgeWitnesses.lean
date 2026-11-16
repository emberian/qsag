module

public import Qsag.Machine.MirSpecBridgeCore

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

def FourLayerWitness.Honest.tsig₀ : IdealTsigState (List UInt8) (List UInt8) :=
  ⟨samplePkPin, 3, 4, [0], [], []⟩

def FourLayerWitness.Honest.wal₀ : WalLatchState :=
  initWalLatchState samplePkPin

def FourLayerWitness.Honest.s3₀ : Layer3ProtocolState (List UInt8) :=
  { policy := FourLayerWitness.Honest.pol2₀.toStatefulPolicyGuard
    cluster := ⟨FourLayerWitness.Honest.tsig₀, FourLayerWitness.Honest.wal₀, 0, FourLayerWitness.Honest.dealt⟩
    activeSessionTag := Goldilocks.ofNat 0
    storedRound1Commits := FourLayerWitness.Honest.stored₀
    verifierBginAlpha := sampleBginAlpha
    verifierBginKeyOffsets := sampleBginOffsets
    quorumCertConfig := sampleQuorumCertConfig }

def FourLayerWitness.Honest.s4₀ : Layer4IdealState (List UInt8) :=
  { policy := FourLayerWitness.Honest.pol2₀.toStatefulPolicyGuard
    ideal := ⟨FourLayerWitness.Honest.tsig₀, FourLayerWitness.Honest.wal₀, 0⟩
    activeSessionTag := Goldilocks.ofNat 0
    storedRound1Commits := FourLayerWitness.Honest.stored₀
    verifierBginAlpha := sampleBginAlpha
    verifierBginKeyOffsets := sampleBginOffsets
    quorumCertConfig := sampleQuorumCertConfig }

def FourLayerWitness.Honest.quorum1 : List (Fin 4) :=
  [⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩]

def FourLayerWitness.Honest.quorum2 : List (Fin 4) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩]

def FourLayerWitness.Honest.tx1 : MirTxIntent :=
  ⟨sampleRecipient, 40, 7, samplePolPin, sampleAuthPin, 10, 0⟩

def FourLayerWitness.Honest.tx2 : MirTxIntent :=
  ⟨sampleRecipient, 55, 7, samplePolPin, sampleAuthPin, 11, 0⟩

def FourLayerWitness.Honest.intent1 :=
  FourLayerWitness.Honest.tx1.toTransactionIntent

def FourLayerWitness.Honest.msg1 :=
  encodeTransactionIntent FourLayerWitness.Honest.intent1

def FourLayerWitness.Honest.intent2 :=
  FourLayerWitness.Honest.tx2.toTransactionIntent

def FourLayerWitness.Honest.msg2 :=
  encodeTransactionIntent FourLayerWitness.Honest.intent2

def FourLayerWitness.Honest.req1 : FourLayerReq 4 :=
  { tx := FourLayerWitness.Honest.tx1
    reqEpoch := 0
    quorum := FourLayerWitness.Honest.quorum1
    quorumCert := mkSampleQuorumCert FourLayerWitness.Honest.quorum1 0 FourLayerWitness.Honest.msg1
    round1Openings := [FourLayerWitness.Honest.op1_s0, FourLayerWitness.Honest.op2_s0, FourLayerWitness.Honest.op3_s0]
    round2Wires := sampleHonestBginWires }

def FourLayerWitness.Honest.req2 : FourLayerReq 4 :=
  { tx := FourLayerWitness.Honest.tx2
    reqEpoch := 1
    quorum := FourLayerWitness.Honest.quorum2
    quorumCert := mkSampleQuorumCert FourLayerWitness.Honest.quorum2 1 FourLayerWitness.Honest.msg2
    round1Openings := [FourLayerWitness.Honest.op0_s1, FourLayerWitness.Honest.op1_s1, FourLayerWitness.Honest.op2_s1]
    round2Wires := sampleHonestBginWires }

abbrev FourLayerWitness.Honest.M1 :=
  layer1CompiledElfMachine (n := 4) 3 samplePkPin (fun m msg => FourLayerWitness.Honest.signFn (readShareMem32 m) msg)

abbrev FourLayerWitness.Honest.M2 :=
  layer2MirGuardedMachine (n := 4) 3 samplePkPin FourLayerWitness.Honest.signFn

def FourLayerWitness.Honest.sig1 :=
  FourLayerWitness.Honest.signFn sampleCustodianShare1 FourLayerWitness.Honest.msg1

def FourLayerWitness.Honest.out1 : FourLayerOut :=
  ⟨⟨FourLayerWitness.Honest.intent1, FourLayerWitness.Honest.msg1⟩, 0, FourLayerWitness.Honest.sig1⟩

def FourLayerWitness.Honest.pol2₁ : MirPolicyGuardState :=
  { FourLayerWitness.Honest.pol2₀ with
    accumulatedSpend := 40
    burnedNonces := [10] }

def FourLayerWitness.Honest.s2₁ : Layer2MirState :=
  { policy := FourLayerWitness.Honest.pol2₁
    belt := { FourLayerWitness.Honest.belt0 with nextEpoch := 1, latchedRecord := some (0, FourLayerWitness.Honest.msg1, FourLayerWitness.Honest.sig1) }
    cut := MirRssCutSession.round1Committed zeroBytes32 zeroBytes32
    shareBytes := some sampleCustodianShare1
    activeSessionTag := Goldilocks.ofNat 1
    storedRound1Commits := FourLayerWitness.Honest.stored₁
    verifierBginAlpha := sampleBginAlpha
    verifierBginKeyOffsets := sampleBginOffsets
    quorumCertConfig := sampleQuorumCertConfig }

def FourLayerWitness.Honest.sig2 :=
  FourLayerWitness.Honest.signFn sampleCustodianShare1 FourLayerWitness.Honest.msg2

def FourLayerWitness.Honest.out2 : FourLayerOut :=
  ⟨⟨FourLayerWitness.Honest.intent2, FourLayerWitness.Honest.msg2⟩, 1, FourLayerWitness.Honest.sig2⟩

def FourLayerWitness.Honest.pol2₂ : MirPolicyGuardState :=
  { FourLayerWitness.Honest.pol2₁ with
    accumulatedSpend := 95
    burnedNonces := [11, 10] }

def FourLayerWitness.Honest.s2₂ : Layer2MirState :=
  { policy := FourLayerWitness.Honest.pol2₂
    belt := { FourLayerWitness.Honest.s2₁.belt with nextEpoch := 2, latchedRecord := some (1, FourLayerWitness.Honest.msg2, FourLayerWitness.Honest.sig2) }
    cut := MirRssCutSession.round1Committed zeroBytes32 zeroBytes32
    shareBytes := some sampleCustodianShare1
    activeSessionTag := Goldilocks.ofNat 2
    storedRound1Commits := []
    verifierBginAlpha := sampleBginAlpha
    verifierBginKeyOffsets := sampleBginOffsets
    quorumCertConfig := sampleQuorumCertConfig }

private theorem layer2_success_step {n : Nat} (q : Nat) (pk : List UInt8)
    (sign : List UInt8 → List UInt8 → ByteArray) (s s' : Layer2MirState)
    (req : FourLayerReq n) (out : FourLayerOut) (pol : MirPolicyGuardState)
    (env : ApprovedIntentEnvelope) (sh : List UInt8)
    (hFault : (s.cut.poisoned || s.belt.poisoned || s.shareBytes.isNone) = false)
    (hPol : mirPolicyStep s.policy req.tx = some (pol, env))
    (hCert : verifyFourLayerQuorumCert s.quorumCertConfig q pk env.canonicalBytes req = true)
    (hEpoch : (decide (pk = s.belt.enrolledPkDigest) && (req.reqEpoch == s.belt.nextEpoch)) = true)
    (hCut : verifyPreCutTranscript s.activeSessionTag s.storedRound1Commits
      s.verifierBginAlpha s.verifierBginKeyOffsets req.quorum req.round1Openings req.round2Wires = true)
    (hShare : s.shareBytes = some sh)
    (hState : ({ s with policy := pol, belt := { s.belt with nextEpoch := req.reqEpoch + 1, latchedRecord := some (req.reqEpoch, env.canonicalBytes, sign sh env.canonicalBytes) }, cut := MirRssCutSession.round1Committed s.cut.sessionId s.cut.maskCommitment, shareBytes := some sh, activeSessionTag := Goldilocks.add s.activeSessionTag Goldilocks.one, storedRound1Commits := consumeRound1Commits s.storedRound1Commits req.quorum } : Layer2MirState) = s')
    (hOut : ({ envelope := env, committedEpoch := req.reqEpoch, sigBytes := sign sh env.canonicalBytes } : FourLayerOut) = out) :
    (layer2MirGuardedMachine q pk sign).step s req = some (s', out) := by
  dsimp only [layer2MirGuardedMachine, PartyMachine.ofOutcome]
  rw [hFault]
  simp only [hPol, hCert, hEpoch, hCut, hShare, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte]
  rw [hState, hOut]

/-- An accepted abstract step has a related concrete successor because errors are reflected. -/
private theorem lift_accepted_step {CState AState Input Output : Type}
    {C : PartyMachine CState Input Output} {A : PartyMachine AState Input Output}
    (sim : ForwardSim C A) {c : CState} {a a' : AState} {inp : Input} {out : Output}
    (hRel : sim.Rel c a) (hStep : A.step a inp = some (a', out)) :
    ∃ c', C.step c inp = some (c', out) ∧ sim.Rel c' a' := by
  cases hC : C.step c inp with
  | none =>
    have hNone := (sim.sim_err hRel hC).1
    rw [hStep] at hNone
    cases hNone
  | some pair =>
    rcases pair with ⟨c', out'⟩
    have hOk := sim.sim_ok hRel hC
    rw [hStep] at hOk
    rcases hOk with ⟨rfl, hRel'⟩
    exact ⟨c', rfl, hRel'⟩

namespace FourLayerWitness.HonestProof
open FourLayerWitness.Honest

private theorem hRel12 : (sim_layer1_to_layer2 (n := 4) 3 samplePkPin signFn).Rel s1₀ s2₀ :=
  ⟨rfl, rfl, sampleElfMem_pins.1, sampleElfMem_pins.2.1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    ⟨rfl, rfl, rfl, rfl, rfl⟩,
    fun _ _ _ => congrArg some sampleElfMem_pins.2.2.symm, fun hP => absurd hP (by decide)⟩
private theorem hRel23 :
    (sim_layer2_to_layer3 (PK := List UInt8) (n := 4) (q := 3) (f := 1)
      corrupt id samplePkPin dealt sampleCustodianShare1 signFn assembleFn
      (by decide) (by decide) (by decide) (by decide) (by decide) hSigM).Rel s2₀ s3₀ :=
  ⟨by decide, rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl,
    ⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩⟩
private theorem hRel34 :
    (sim_layer3_to_layer4 corrupt id dealt assembleFn oracleFn hOraE).Rel s3₀ s4₀ :=
  ⟨rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ => rfl⟩
private theorem hRel14 : sim.Rel s1₀ s4₀ := ⟨s2₀, hRel12, s3₀, hRel23, hRel34⟩
private theorem hQCert1 : verifyFourLayerQuorumCert sampleQuorumCertConfig 3 samplePkPin msg1 req1 = true := by
  qsag_aux_lemma =>
    exact sampleQuorumCert_valid rfl (by decide) (by decide)
private theorem hQCert2 : verifyFourLayerQuorumCert sampleQuorumCertConfig 3 samplePkPin msg2 req2 = true := by
  qsag_aux_lemma =>
    exact sampleQuorumCert_valid rfl (by decide) (by decide)
private theorem hBginOk : verifySessionBginBatch sampleBginAlpha sampleBginOffsets sampleHonestBginWires = true :=
  sampleHonestBginWires_ok
private theorem hR1Ok1 : verifySessionRound1Openings (Goldilocks.ofNat 0) stored₀ quorum1
    [op1_s0, op2_s0, op3_s0] = true := by
  qsag_aux_lemma =>
    apply verifySessionRound1Openings_eq_true rfl rfl (by decide) (by decide)
    intro op hop
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl
    · exact ⟨rfl, .head _, rfl⟩
    · exact ⟨rfl, .tail _ (.head _), rfl⟩
    · exact ⟨rfl, .tail _ (.tail _ (.head _)), rfl⟩
private theorem hR1Ok2 : verifySessionRound1Openings (Goldilocks.ofNat 1) stored₁ quorum2
    [op0_s1, op1_s1, op2_s1] = true := by
  qsag_aux_lemma =>
    apply verifySessionRound1Openings_eq_true rfl rfl (by decide) (by decide)
    intro op hop
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl
    · exact ⟨rfl, .head _, rfl⟩
    · exact ⟨rfl, .tail _ (.head _), rfl⟩
    · exact ⟨rfl, .tail _ (.tail _ (.head _)), rfl⟩
private theorem hPreCut1 :
    verifyPreCutTranscript (Goldilocks.ofNat 0) stored₀ sampleBginAlpha sampleBginOffsets
      quorum1 [op1_s0, op2_s0, op3_s0] sampleHonestBginWires = true := by
  qsag_aux_lemma =>
    unfold verifyPreCutTranscript
    rw [hR1Ok1, hBginOk]
    rfl
private theorem hPreCut2 :
    verifyPreCutTranscript (Goldilocks.ofNat 1) stored₁ sampleBginAlpha sampleBginOffsets
      quorum2 [op0_s1, op1_s1, op2_s1] sampleHonestBginWires = true := by
  qsag_aux_lemma =>
    unfold verifyPreCutTranscript
    rw [hR1Ok2, hBginOk]
    rfl
private theorem hPol1 : mirPolicyStep pol2₀ tx1 = some (pol2₁, ⟨intent1, msg1⟩) := by
  qsag_aux_lemma =>
    dsimp only [mirPolicyStep, pol2₀, FourLayerWitness.Honest.pol2₀, req1, FourLayerWitness.Honest.req1, tx1, FourLayerWitness.Honest.tx1, pol2₁, FourLayerWitness.Honest.pol2₁, intent1, FourLayerWitness.Honest.intent1, msg1, FourLayerWitness.Honest.msg1]
    rw [ite_eq_right (show ¬ (((7 : UInt64) != (7 : UInt64)) = true) by decide)]
    rw [ite_eq_right (show ¬ ((samplePolPin != samplePolPin) = true) by decide)]
    rw [ite_eq_right (show ¬ ((sampleAuthPin != sampleAuthPin) = true) by decide)]
    rw [ite_eq_right (fun hn : ¬ (sampleRecipient ∈ [sampleRecipient]) => hn (.head _))]
    rw [ite_eq_right (show ¬ ¬ ((40 : UInt64).toNat ≤ (60 : UInt64).toNat) by decide)]
    rw [ite_eq_right (show ¬ ¬ ((40 : UInt64).toNat ≤ ((100 : UInt64) - (0 : UInt64)).toNat) by decide)]
    rw [ite_eq_right (show ¬ (u64MemBool 10 [] = true) by decide)]
    rfl
private theorem hStep2_1 : (layer2MirGuardedMachine (n := 4) 3 samplePkPin signFn).step s2₀ req1 = some (s2₁, out1) := by
  exact layer2_success_step 3 samplePkPin signFn s2₀ s2₁ req1 out1
    pol2₁ ⟨intent1, msg1⟩ sampleCustodianShare1 rfl hPol1 hQCert1
    (by decide) hPreCut1 rfl rfl rfl

private theorem hPol2 : mirPolicyStep pol2₁ tx2 = some (pol2₂, ⟨intent2, msg2⟩) := by
  qsag_aux_lemma =>
    dsimp only [mirPolicyStep, pol2₁, FourLayerWitness.Honest.pol2₁, pol2₀, FourLayerWitness.Honest.pol2₀, req2, FourLayerWitness.Honest.req2, tx2, FourLayerWitness.Honest.tx2, pol2₂, FourLayerWitness.Honest.pol2₂, intent2, FourLayerWitness.Honest.intent2, msg2, FourLayerWitness.Honest.msg2]
    rw [ite_eq_right (show ¬ (((7 : UInt64) != (7 : UInt64)) = true) by decide)]
    rw [ite_eq_right (show ¬ ((samplePolPin != samplePolPin) = true) by decide)]
    rw [ite_eq_right (show ¬ ((sampleAuthPin != sampleAuthPin) = true) by decide)]
    rw [ite_eq_right (fun hn : ¬ (sampleRecipient ∈ [sampleRecipient]) => hn (.head _))]
    rw [ite_eq_right (show ¬ ¬ ((55 : UInt64).toNat ≤ (60 : UInt64).toNat) by decide)]
    rw [ite_eq_right (show ¬ ¬ ((55 : UInt64).toNat ≤ ((100 : UInt64) - (40 : UInt64)).toNat) by decide)]
    rw [ite_eq_right (show ¬ (u64MemBool 11 [10] = true) by decide)]
    rfl
private theorem hStep2_2 : (layer2MirGuardedMachine (n := 4) 3 samplePkPin signFn).step s2₁ req2 = some (s2₂, out2) := by
  exact layer2_success_step 3 samplePkPin signFn s2₁ s2₂ req2 out2
    pol2₂ ⟨intent2, msg2⟩ sampleCustodianShare1 rfl hPol2 hQCert2
    (by decide) hPreCut2 rfl rfl rfl

private theorem hStep1_1 : ∃ s1₁, M1.step s1₀ req1 = some (s1₁, out1) ∧
    (sim_layer1_to_layer2 (n := 4) 3 samplePkPin signFn).Rel s1₁ s2₁ := by
  have h := lift_accepted_step (sim_layer1_to_layer2 (n := 4) 3 samplePkPin signFn) hRel12 hStep2_1
  with_reducible exact h

private theorem hStep1_2 (s1₁ : Layer1ElfState)
    (hRel12_1 : (sim_layer1_to_layer2 (n := 4) 3 samplePkPin signFn).Rel s1₁ s2₁) :
    ∃ s1₂, M1.step s1₁ req2 = some (s1₂, out2) := by
  obtain ⟨s1₂, hStep, _⟩ :=
    lift_accepted_step (sim_layer1_to_layer2 (n := 4) 3 samplePkPin signFn) hRel12_1 hStep2_2
  exact ⟨s1₂, hStep⟩

attribute [-instance] Fin.instLinearOrderPackage in
private theorem hSafe : FourLayerTraceSafe s4₀.policy.velocity_window_cap corrupt
    [(req1, out1), (req2, out2)] := by
  qsag_aux_lemma =>
    change (40 + 55 + 0 ≤ 100) ∧ ([10, 11] : List Nat).Nodup ∧
      ([0, 1] : List Nat).Pairwise (· < ·) ∧ _
    refine ⟨by decide, by decide, by decide, ?_⟩
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨⟨1, by decide⟩, by decide, by decide⟩
    · exact ⟨⟨1, by decide⟩, by decide, by decide⟩
#verify_constructive hSafe
end FourLayerWitness.HonestProof

/-- Mutated Layer-1 machine replacing ONLY Link 2's authoritative `accumulatedSpend` check with
    the untrusted caller-echoed velocity `req.tx.callerEchoedSpent` while keeping real ELF
    `ct_eq_32`, `§4`-authenticated `BeltLatch` `2 * q > n + f`, and session-bound pre-cut
    consistency barrier intact. -/
def statelessPolicyLayer1Machine {n : Nat} (q : Nat) (pkDigest : List UInt8)
    (signFromShareMem : (UInt64 → UInt8) → List UInt8 → ByteArray) :
    PartyMachine Layer1ElfState (FourLayerReq n) FourLayerOut :=
  PartyMachine.ofOutcome fun s req =>
    if s.cutPoisoned || s.belt.poisoned || !s.sharePresent then
      .err { s with mem := execElfMemzeroShare32 s.mem,
                    belt := { s.belt with poisoned := true },
                    cutPoisoned := true, sharePresent := false } ()
    else if req.tx.windowId != s.windowId then .err s ()
    else if !execElfCtEq32 s.mem (UInt64.ofNat 0x100) req.tx.policyDigest then .err s ()
    else if !execElfCtEq32 s.mem (UInt64.ofNat 0x140) req.tx.authorityDigest then .err s ()
    else if ¬ (req.tx.recipient ∈ s.allowedRecipients) then .err s ()
    else if ¬ (req.tx.amountUnits.toNat ≤ s.perTxCap.toNat) then .err s ()
    -- BROKEN LINK: trusts `req.tx.callerEchoedSpent` instead of authoritative `s.accumulatedSpend`!
    else if ¬ (req.tx.amountUnits.toNat ≤ (s.velocityWindowCap - req.tx.callerEchoedSpent).toNat) then
      .err s ()
    else if u64MemBool req.tx.nonce s.burnedNonces then .err s ()
    else
      let intent := req.tx.toTransactionIntent
      let msgBytes := encodeTransactionIntent intent
      if !verifyFourLayerQuorumCert s.quorumCertConfig q pkDigest msgBytes req then .err s ()
      else if !(decide (pkDigest = s.belt.enrolledPkDigest) && (req.reqEpoch == s.belt.nextEpoch)) then
        .err s ()
      else if !verifyPreCutTranscript s.activeSessionTag s.storedRound1Commits
          s.verifierBginAlpha s.verifierBginKeyOffsets req.quorum
          req.round1Openings req.round2Wires then
        .err { s with mem := execElfMemzeroShare32 s.mem,
                      belt := { s.belt with poisoned := true },
                      cutPoisoned := true, sharePresent := false } ()
      else
        let sigBytes := signFromShareMem s.mem msgBytes
        let env : ApprovedIntentEnvelope := { intent := intent, canonicalBytes := msgBytes }
        let belt' : MirBeltLatchState :=
          { s.belt with
            nextEpoch := req.reqEpoch + 1
            latchedRecord := some (req.reqEpoch, msgBytes, sigBytes) }
        let s' : Layer1ElfState :=
          { s with
            burnedNonces := req.tx.nonce :: s.burnedNonces
            belt := belt'
            activeSessionTag := Goldilocks.add s.activeSessionTag Goldilocks.one
            storedRound1Commits := consumeRound1Commits s.storedRound1Commits req.quorum }
        .ok s' { envelope := env, committedEpoch := req.reqEpoch, sigBytes := sigBytes }

/- Shared concrete witness data; named constants bound kernel expansion. -/
def FourLayerWitness.Stateless.corrupt : List (Fin 4) :=
  [⟨0, by decide⟩]

def FourLayerWitness.Stateless.signFn : List UInt8 → List UInt8 → ByteArray :=
  signFromCustodianShare1WithPeers

def FourLayerWitness.Stateless.oracleFn : List UInt8 → ByteArray :=
  fun msg => poseidon2TagBytes sampleSecretKeyBytes msg

abbrev FourLayerWitness.Stateless.badM1 :=
  statelessPolicyLayer1Machine (n := 4) 3 samplePkPin
    (fun m msg => FourLayerWitness.Stateless.signFn (readShareMem32 m) msg)

abbrev FourLayerWitness.Stateless.M4 :=
  layer4IdealTsigMachine (PK := List UInt8) (n := 4) FourLayerWitness.Stateless.corrupt id FourLayerWitness.Stateless.oracleFn

def FourLayerWitness.Stateless.op1_s0 :=
  mkSampleRound1Opening 5 9 0 1 100

def FourLayerWitness.Stateless.op2_s0 :=
  mkSampleRound1Opening 6 10 0 2 200

def FourLayerWitness.Stateless.op3_s0 :=
  mkSampleRound1Opening 7 11 0 3 300

def FourLayerWitness.Stateless.op1_s1 :=
  mkSampleRound1Opening 15 19 1 1 400

def FourLayerWitness.Stateless.op2_s1 :=
  mkSampleRound1Opening 16 20 1 2 500

def FourLayerWitness.Stateless.op3_s1 :=
  mkSampleRound1Opening 17 21 1 3 600

def FourLayerWitness.Stateless.stored₀ : List (Nat × Lane4) :=
  [(1, FourLayerWitness.Stateless.op1_s0.committedB0), (2, FourLayerWitness.Stateless.op2_s0.committedB0), (3, FourLayerWitness.Stateless.op3_s0.committedB0),
   (1, FourLayerWitness.Stateless.op1_s1.committedB0), (2, FourLayerWitness.Stateless.op2_s1.committedB0), (3, FourLayerWitness.Stateless.op3_s1.committedB0)]

def FourLayerWitness.Stateless.stored₁ : List (Nat × Lane4) :=
  [(1, FourLayerWitness.Stateless.op1_s1.committedB0), (2, FourLayerWitness.Stateless.op2_s1.committedB0), (3, FourLayerWitness.Stateless.op3_s1.committedB0)]

def FourLayerWitness.Stateless.belt0 : MirBeltLatchState :=
  ⟨samplePkPin, 0, none, false⟩

def FourLayerWitness.Stateless.s1₀ : Layer1ElfState :=
  { mem := sampleElfMem
    windowId := 7
    velocityWindowCap := 100
    accumulatedSpend := 0
    burnedNonces := []
    allowedRecipients := [sampleRecipient]
    perTxCap := 60
    belt := FourLayerWitness.Stateless.belt0
    cutPoisoned := false
    sharePresent := true
    activeSessionTag := Goldilocks.ofNat 0
    storedRound1Commits := FourLayerWitness.Stateless.stored₀
    verifierBginAlpha := sampleBginAlpha
    verifierBginKeyOffsets := sampleBginOffsets
    quorumCertConfig := sampleQuorumCertConfig }

def FourLayerWitness.Stateless.pol4₀ : StatefulPolicyGuard :=
  { window_id := 7
    velocity_window_cap := 100
    accumulated_spend := 0
    burned_intent_nonces := []
    pinned_policy_digest := samplePolPin
    pinned_authority_digest := sampleAuthPin
    allowed_recipients := [sampleRecipient]
    per_tx_cap := 60 }

def FourLayerWitness.Stateless.s4₀ : Layer4IdealState (List UInt8) :=
  { policy := FourLayerWitness.Stateless.pol4₀
    ideal := ⟨⟨samplePkPin, 3, 4, [0], [], []⟩, initWalLatchState samplePkPin, 0⟩
    activeSessionTag := Goldilocks.ofNat 0
    storedRound1Commits := FourLayerWitness.Stateless.stored₀
    verifierBginAlpha := sampleBginAlpha
    verifierBginKeyOffsets := sampleBginOffsets
    quorumCertConfig := sampleQuorumCertConfig }

def FourLayerWitness.Stateless.quorum1 : List (Fin 4) :=
  [⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩]

def FourLayerWitness.Stateless.tx1 : MirTxIntent :=
  ⟨sampleRecipient, 60, 7, samplePolPin, sampleAuthPin, 1, 0⟩

def FourLayerWitness.Stateless.tx2 : MirTxIntent :=
  ⟨sampleRecipient, 60, 7, samplePolPin, sampleAuthPin, 2, 0⟩

def FourLayerWitness.Stateless.intent1 :=
  FourLayerWitness.Stateless.tx1.toTransactionIntent

def FourLayerWitness.Stateless.msg1 :=
  encodeTransactionIntent FourLayerWitness.Stateless.intent1

def FourLayerWitness.Stateless.intent2 :=
  FourLayerWitness.Stateless.tx2.toTransactionIntent

def FourLayerWitness.Stateless.msg2 :=
  encodeTransactionIntent FourLayerWitness.Stateless.intent2

def FourLayerWitness.Stateless.req1 : FourLayerReq 4 :=
  { tx := FourLayerWitness.Stateless.tx1
    reqEpoch := 0
    quorum := FourLayerWitness.Stateless.quorum1
    quorumCert := mkSampleQuorumCert FourLayerWitness.Stateless.quorum1 0 FourLayerWitness.Stateless.msg1
    round1Openings := [FourLayerWitness.Stateless.op1_s0, FourLayerWitness.Stateless.op2_s0, FourLayerWitness.Stateless.op3_s0]
    round2Wires := sampleHonestBginWires }

def FourLayerWitness.Stateless.req2 : FourLayerReq 4 :=
  { tx := FourLayerWitness.Stateless.tx2
    reqEpoch := 1
    quorum := FourLayerWitness.Stateless.quorum1
    quorumCert := mkSampleQuorumCert FourLayerWitness.Stateless.quorum1 1 FourLayerWitness.Stateless.msg2
    round1Openings := [FourLayerWitness.Stateless.op1_s1, FourLayerWitness.Stateless.op2_s1, FourLayerWitness.Stateless.op3_s1]
    round2Wires := sampleHonestBginWires }

def FourLayerWitness.Stateless.sig1 :=
  FourLayerWitness.Stateless.signFn (readShareMem32 sampleElfMem) FourLayerWitness.Stateless.msg1

def FourLayerWitness.Stateless.out1 : FourLayerOut :=
  ⟨⟨FourLayerWitness.Stateless.intent1, FourLayerWitness.Stateless.msg1⟩, 0, FourLayerWitness.Stateless.sig1⟩

def FourLayerWitness.Stateless.s1₁ : Layer1ElfState :=
  { FourLayerWitness.Stateless.s1₀ with
    burnedNonces := [1]
    belt := { FourLayerWitness.Stateless.belt0 with nextEpoch := 1, latchedRecord := some (0, FourLayerWitness.Stateless.msg1, FourLayerWitness.Stateless.sig1) }
    activeSessionTag := Goldilocks.ofNat 1
    storedRound1Commits := FourLayerWitness.Stateless.stored₁ }

def FourLayerWitness.Stateless.sig2 :=
  FourLayerWitness.Stateless.signFn (readShareMem32 sampleElfMem) FourLayerWitness.Stateless.msg2

def FourLayerWitness.Stateless.out2 : FourLayerOut :=
  ⟨⟨FourLayerWitness.Stateless.intent2, FourLayerWitness.Stateless.msg2⟩, 1, FourLayerWitness.Stateless.sig2⟩

def FourLayerWitness.Stateless.s1₂ : Layer1ElfState :=
  { FourLayerWitness.Stateless.s1₁ with
    burnedNonces := [2, 1]
    belt := { FourLayerWitness.Stateless.s1₁.belt with nextEpoch := 2, latchedRecord := some (1, FourLayerWitness.Stateless.msg2, FourLayerWitness.Stateless.sig2) }
    activeSessionTag := Goldilocks.ofNat 2
    storedRound1Commits := [] }

def FourLayerWitness.Stateless.badTrace :=
  [(FourLayerWitness.Stateless.req1, FourLayerWitness.Stateless.out1), (FourLayerWitness.Stateless.req2, FourLayerWitness.Stateless.out2)]

private theorem stateless_success_step {n : Nat} (q : Nat) (pk : List UInt8)
    (sign : (UInt64 → UInt8) → List UInt8 → ByteArray) (s s' : Layer1ElfState)
    (req : FourLayerReq n) (out : FourLayerOut)
    (hFault : (s.cutPoisoned || s.belt.poisoned || !s.sharePresent) = false)
    (hWindow : (req.tx.windowId != s.windowId) = false)
    (hPol : execElfCtEq32 s.mem (UInt64.ofNat 0x100) req.tx.policyDigest = true)
    (hAuth : execElfCtEq32 s.mem (UInt64.ofNat 0x140) req.tx.authorityDigest = true)
    (hRecipient : req.tx.recipient ∈ s.allowedRecipients)
    (hPerTx : req.tx.amountUnits.toNat ≤ s.perTxCap.toNat)
    (hVelocity : req.tx.amountUnits.toNat ≤ (s.velocityWindowCap - req.tx.callerEchoedSpent).toNat)
    (hNonce : u64MemBool req.tx.nonce s.burnedNonces = false)
    (hCert : verifyFourLayerQuorumCert s.quorumCertConfig q pk
      (encodeTransactionIntent req.tx.toTransactionIntent) req = true)
    (hEpoch : (decide (pk = s.belt.enrolledPkDigest) && (req.reqEpoch == s.belt.nextEpoch)) = true)
    (hCut : verifyPreCutTranscript s.activeSessionTag s.storedRound1Commits
      s.verifierBginAlpha s.verifierBginKeyOffsets req.quorum req.round1Openings req.round2Wires = true)
    (hState : ({ s with burnedNonces := req.tx.nonce :: s.burnedNonces, belt := { s.belt with nextEpoch := req.reqEpoch + 1, latchedRecord := some (req.reqEpoch, encodeTransactionIntent req.tx.toTransactionIntent, sign s.mem (encodeTransactionIntent req.tx.toTransactionIntent)) }, activeSessionTag := Goldilocks.add s.activeSessionTag Goldilocks.one, storedRound1Commits := consumeRound1Commits s.storedRound1Commits req.quorum } : Layer1ElfState) = s')
    (hOut : ({ envelope := ⟨req.tx.toTransactionIntent, encodeTransactionIntent req.tx.toTransactionIntent⟩, committedEpoch := req.reqEpoch, sigBytes := sign s.mem (encodeTransactionIntent req.tx.toTransactionIntent) } : FourLayerOut) = out) :
    (statelessPolicyLayer1Machine q pk sign).step s req = some (s', out) := by
  dsimp only [statelessPolicyLayer1Machine, PartyMachine.ofOutcome]
  simp only [hFault, hWindow, hPol, hAuth, hRecipient, hPerTx, hVelocity,
    hNonce, hCert, hEpoch, hCut, Bool.not_true, Bool.false_eq_true, not_true_eq_false, ↓reduceIte]
  rw [hState, hOut]

namespace FourLayerWitness.StatelessProof
open FourLayerWitness.Stateless

private theorem hCtPol : execElfCtEq32 sampleElfMem (UInt64.ofNat 0x100) samplePolPin = true := by
  qsag_aux_lemma =>
    rw [execElfCtEq32_spec (pinned := samplePolPin) rfl (by omega) sampleElfMem_pins.1]; rfl
private theorem hCtAuth : execElfCtEq32 sampleElfMem (UInt64.ofNat 0x140) sampleAuthPin = true := by
  qsag_aux_lemma =>
    rw [execElfCtEq32_spec (pinned := sampleAuthPin) rfl (by omega) sampleElfMem_pins.2.1]; rfl
private theorem hQCert1 : verifyFourLayerQuorumCert sampleQuorumCertConfig 3 samplePkPin msg1 req1 = true := by
  qsag_aux_lemma =>
    exact sampleQuorumCert_valid rfl (by decide) (by decide)
private theorem hQCert2 : verifyFourLayerQuorumCert sampleQuorumCertConfig 3 samplePkPin msg2 req2 = true := by
  qsag_aux_lemma =>
    exact sampleQuorumCert_valid rfl (by decide) (by decide)
private theorem hBginOk : verifySessionBginBatch sampleBginAlpha sampleBginOffsets sampleHonestBginWires = true :=
  sampleHonestBginWires_ok
private theorem hR1Ok1 : verifySessionRound1Openings (Goldilocks.ofNat 0) stored₀ quorum1
    [op1_s0, op2_s0, op3_s0] = true := by
  qsag_aux_lemma =>
    apply verifySessionRound1Openings_eq_true rfl rfl (by decide) (by decide)
    intro op hop
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl
    · exact ⟨rfl, .head _, rfl⟩
    · exact ⟨rfl, .tail _ (.head _), rfl⟩
    · exact ⟨rfl, .tail _ (.tail _ (.head _)), rfl⟩
private theorem hR1Ok2 : verifySessionRound1Openings (Goldilocks.ofNat 1) stored₁ quorum1
    [op1_s1, op2_s1, op3_s1] = true := by
  qsag_aux_lemma =>
    apply verifySessionRound1Openings_eq_true rfl rfl (by decide) (by decide)
    intro op hop
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl
    · exact ⟨rfl, .head _, rfl⟩
    · exact ⟨rfl, .tail _ (.head _), rfl⟩
    · exact ⟨rfl, .tail _ (.tail _ (.head _)), rfl⟩
private theorem hPreCut1 :
    verifyPreCutTranscript (Goldilocks.ofNat 0) stored₀ sampleBginAlpha sampleBginOffsets
      quorum1 [op1_s0, op2_s0, op3_s0] sampleHonestBginWires = true := by
  qsag_aux_lemma =>
    unfold verifyPreCutTranscript; rw [hR1Ok1, hBginOk]; rfl
private theorem hPreCut2 :
    verifyPreCutTranscript (Goldilocks.ofNat 1) stored₁ sampleBginAlpha sampleBginOffsets
      quorum1 [op1_s1, op2_s1, op3_s1] sampleHonestBginWires = true := by
  qsag_aux_lemma =>
    unfold verifyPreCutTranscript; rw [hR1Ok2, hBginOk]; rfl
private theorem hStep1 : badM1.step s1₀ req1 = some (s1₁, out1) := by
  with_reducible exact (stateless_success_step (n := 4) 3 samplePkPin (fun m msg => signFn (readShareMem32 m) msg)
    s1₀ s1₁ req1 out1 (by decide) (by decide)
    (by simpa only [s1₀, s1₀, req1, tx1] using hCtPol)
    (by simpa only [s1₀, s1₀, req1, tx1] using hCtAuth)
    (by simpa only [s1₀, s1₀, req1, tx1] using (show sampleRecipient ∈ [sampleRecipient] from List.Mem.head _))
    (by decide) (by decide) (by decide)
    (by simpa only [s1₀, s1₀, req1, tx1, msg1, intent1] using hQCert1) (by decide)
    (by simpa only [s1₀, s1₀, req1, tx1] using hPreCut1)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl))

private theorem hStep2 : badM1.step s1₁ req2 = some (s1₂, out2) := by
  with_reducible exact (stateless_success_step (n := 4) 3 samplePkPin (fun m msg => signFn (readShareMem32 m) msg)
    s1₁ s1₂ req2 out2 (by decide) (by decide)
    (by simpa only [s1₁, s1₀, req2, tx2] using hCtPol)
    (by simpa only [s1₁, s1₀, req2, tx2] using hCtAuth)
    (by simpa only [s1₁, s1₀, req2, tx2] using (show sampleRecipient ∈ [sampleRecipient] from List.Mem.head _))
    (by decide) (by decide) (by decide)
    (by simpa only [s1₁, s1₀, req2, tx2, msg2, intent2] using hQCert2) (by decide)
    (by simpa only [s1₁, s1₀, req2, tx2] using hPreCut2)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl))

private theorem hBadValid : badM1.ValidTrace s1₀ badTrace s1₂ :=
  .accept hStep1 (.accept hStep2 (.nil s1₂))
private theorem hNotSafe : ¬ FourLayerTraceSafe s4₀.policy.velocity_window_cap corrupt badTrace := by
  qsag_aux_lemma =>
    intro hSafe
    have hSumLe : (badTrace.map (fun p => p.2.envelope.intent.amount_units)).foldr (· + ·) 0 ≤
        s4₀.policy.velocity_window_cap := hSafe.1
    change 60 + (60 + 0) ≤ 100 at hSumLe
    omega
private theorem hIdealSafeAll : ∀ {tr : List (FourLayerReq 4 × FourLayerOut)} {s4F : Layer4IdealState (List UInt8)},
    M4.ValidTrace s4₀ tr s4F → FourLayerTraceSafe s4₀.policy.velocity_window_cap corrupt tr := by
  qsag_aux_lemma =>
    intro tr s4F hTr4
    obtain ⟨hCust, _, _, hEpPair, hHon⟩ :=
      layer4_validTrace_safe corrupt id oracleFn (by decide) rfl (by decide) hTr4
    have hPolMain := policy_multiturn_velocity_and_intent_binding (by decide) hCust
    rw [traceApprovedOutputs_fourLayer tr] at hPolMain
    dsimp only at hPolMain
    have hMapAmt :
        ((tr.map (fun p => p.2.envelope)).map (fun e => e.intent.amount_units)) =
          tr.map (fun p => p.2.envelope.intent.amount_units) := by
      rw [List.map_map]; rfl
    have hMapNonce :
        ((tr.map (fun p => p.2.envelope)).map (fun e => e.intent.nonce)) =
          tr.map (fun p => p.2.envelope.intent.nonce) := by
      rw [List.map_map]; rfl
    rw [hMapAmt, hMapNonce] at hPolMain
    exact ⟨hPolMain.2.2.1, hPolMain.2.2.2.1, hEpPair, hHon⟩
private theorem hNoIdeal : ∀ s4Final, ¬ M4.ValidTrace s4₀ badTrace s4Final :=
  fun _ hTr4 => hNotSafe (hIdealSafeAll hTr4)
private theorem hNoSim : ∀ sim : ForwardSim badM1 M4, sim.Rel s1₀ s4₀ → False := by
  qsag_aux_lemma =>
    intro sim hRel
    exact hNotSafe (ForwardSim.preserve_trace_pred sim hRel hIdealSafeAll hBadValid)
end FourLayerWitness.StatelessProof

open FourLayerWitness.Stateless FourLayerWitness.StatelessProof in
/-- **`#tooth` Broken-Link Refutation (`tooth_stateless_policy_link_breaks_four_layer_ideal_safety`)**:
    Breaking ONLY Link 2's authoritative spend invariant (`statelessPolicyLayer1Machine` trusting
    `callerEchoedSpent = 0` while compiled ELF `ct_eq_32`, `§4`-authenticated `BeltLatch`, and the
    session-bound pre-cut barrier remain intact) admits a 2-turn trace spending `60 + 60 = 120 > 100`,
    violates `FourLayerTraceSafe`, is rejected by `layer4IdealTsigMachine`, and makes ANY
    `ForwardSim statelessPolicyLayer1Machine layer4IdealTsigMachine` from `(s1₀, s4₀)` impossible! -/
theorem tooth_stateless_policy_link_breaks_four_layer_ideal_safety :
    let corrupt : List (Fin 4) := FourLayerWitness.Stateless.corrupt
    let badM1 := FourLayerWitness.Stateless.badM1
    let M4 := FourLayerWitness.Stateless.M4
    ∃ (s1₀ s1Final : Layer1ElfState)
      (s4₀ : Layer4IdealState (List UInt8))
      (badTrace : List (FourLayerReq 4 × FourLayerOut)),
      badM1.ValidTrace s1₀ badTrace s1Final ∧
      ¬ FourLayerTraceSafe s4₀.policy.velocity_window_cap corrupt badTrace ∧
      (∀ s4Final, ¬ M4.ValidTrace s4₀ badTrace s4Final) ∧
      (∀ sim : ForwardSim badM1 M4, sim.Rel s1₀ s4₀ → False) := by
  intro corrupt badM1 M4
  exact ⟨s1₀, s1₂, s4₀, badTrace, hBadValid, hNotSafe, hNoIdeal, hNoSim⟩

end Qsag
