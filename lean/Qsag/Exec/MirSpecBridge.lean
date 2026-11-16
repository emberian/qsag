module

public import Qsag.Exec.MirSpecBridgeCore
public import Qsag.Exec.MirSpecBridgeWitnesses
import all Qsag.Exec.MirSpecBridgeWitnesses
import Qsag.Tactic.AssuranceKit

/-! Public entry point for the hand-written MIR guard models, their four-layer
simulation chain, generalized `ShamirThresholdSubset` multi-turn safety, and concrete
accepted/rejected trace witnesses. The extracted Rust-to-model welds live in the separate
`qsag_aeneas` package (`AuthenticatedBeltAndRealSpecWeld.lean`, `RealSpecGuardBoundary.lean`). -/

public section
namespace Qsag

open FourLayerWitness.Honest FourLayerWitness.HonestProof in
/-- **Non-Vacuity Witness (`inhabited_four_layer_chain`)**:
    Exhibits a concrete `(n = 4, q = 3, f = 1)` 4-layer cluster (`2 * 3 > 4 + 1`) dealt 4 distinct
    degree-2 Shamir shares (`sampleDealtShares`, proved 1-share uniform-bijective by
    `singleShare_uniform_bijection` and distinct from `sampleSecretKeyBytes` by
    `sampleShares_distinct_and_reconstruct`), executing a 2-turn multi-quorum trace
    (`Q₁ = [1, 2, 3]` spending `40`, `Q₂ = [0, 1, 2]` spending `55`, total `95 ≤ 100` despite
    `callerEchoedSpent = 0`) with `§4`-authenticated quorum certificates, 30-round blinded
    `Poseidon2` Round-1 commitments, verifier-held `BGIN19` MAC keys, and genuine Lagrange
    reconstruction matching `oracleFn`. The signer closes over three shares and the oracle
    is a keyed tag. This witnesses joint satisfiability, not separated custody, signature
    security, session-fresh Round-2 authentication, or an extracted production refinement. -/
theorem inhabited_four_layer_chain :
    let corrupt : List (Fin 4) := FourLayerWitness.Honest.corrupt
    let signFn : List UInt8 → List UInt8 → ByteArray := FourLayerWitness.Honest.signFn
    let dealt : Nat → Option (List UInt8) := FourLayerWitness.Honest.dealt
    let sim := FourLayerWitness.Honest.sim
    ∃ (s1₀ s1Final : Layer1ElfState)
      (s4₀ : Layer4IdealState (List UInt8))
      (trace : List (FourLayerReq 4 × FourLayerOut)),
      trace.length = 2 ∧
      dealt 0 ≠ dealt 1 ∧
      dealt 1 ≠ dealt 2 ∧
      dealt 2 ≠ dealt 3 ∧
      dealt 1 ≠ some sampleSecretKeyBytes ∧
      sim.Rel s1₀ s4₀ ∧
      (layer1CompiledElfMachine (n := 4) 3 samplePkPin
        (fun m msg => signFn (readShareMem32 m) msg)).ValidTrace s1₀ trace s1Final ∧
      FourLayerTraceSafe s4₀.policy.velocity_window_cap corrupt trace := by
  intro corrupt signFn dealt sim
  obtain ⟨s1₁, hS1_1, hRel12_1⟩ := hStep1_1
  obtain ⟨s1₂, hS1_2⟩ := hStep1_2 s1₁ hRel12_1
  have hTr1 : M1.ValidTrace s1₀ [(req1, out1), (req2, out2)] s1₂ :=
    .accept hS1_1 (.accept hS1_2 (.nil s1₂))
  obtain ⟨hD01, hD12, hD23, _, hD1Sk, _⟩ := sampleShares_distinct_and_reconstruct
  exact ⟨s1₀, s1₂, s4₀, [(req1, out1), (req2, out2)], rfl,
    fun h => hD01 (Option.some.inj h),
    fun h => hD12 (Option.some.inj h),
    fun h => hD23 (Option.some.inj h),
    fun h => hD1Sk (Option.some.inj h),
    hRel14, hTr1, hSafe⟩

/-- **Generalized `ShamirThresholdSubset` Four-Layer Multi-Turn Safety
    (`shamirSubset_preserves_multiturn_safety`)**:
    For any certified distinct nonzero `t`-of-`n` subset `Q : ShamirThresholdSubset n t`
    with `n + f < 2 * t` and `t ≤ n`, any multi-turn trace accepted by `layer1CompiledElfMachine`
    satisfies `FourLayerTraceSafe` (spend cap, `Nodup` nonces, strictly increasing epochs, and
    honest validator participation) and wipes the 32-byte share window `[0x180, 0x1A0)` upon poison. -/
theorem shamirSubset_preserves_multiturn_safety {PK : Type} {n t f : Nat}
    (Q : ShamirThresholdSubset n t) (corrupt : List (Fin n))
    (pkDigestOf : PK → List UInt8) (pk : PK)
    (dealt : Nat → Option (List UInt8)) (custodian : Fin n)
    (localShare : List UInt8) (polys : Fin 4 → List Goldilocks)
    (degree : ∀ i, (polys i).length ≤ t)
    (hDealt : ∀ p : Fin n, unpackLane4Bytes32 ((dealt p.val).getD []) =
      evalShamirPolynomials polys (Goldilocks.ofNat (p.val + 1)))
    (hLocal : unpackLane4Bytes32 localShare = unpackLane4Bytes32 ((dealt custodian.val).getD []))
    (hBound : n + f < 2 * t) (hTLeN : t ≤ n)
    (hCorruptNd : corrupt.Nodup) (hCorruptLe : corrupt.length ≤ f)
    {s1₀ s1Final : Layer1ElfState}
    {s4₀ : Layer4IdealState PK}
    {trace : List (FourLayerReq n × FourLayerOut)}
    (hRel₀ :
      (shamirSubset_four_layer_sim Q corrupt pkDigestOf pk dealt custodian localShare
        polys degree hDealt hLocal hBound hTLeN hCorruptNd hCorruptLe).Rel s1₀ s4₀)
    (hTrace1 :
      (layer1CompiledElfMachine (n := n) t (pkDigestOf pk) (fun mem msg =>
        signFromCustodianWithPeers Q custodian (unpackLane4Bytes32 (readShareMem32 mem))
          (fun p => unpackLane4Bytes32 ((dealt p.val).getD [])) msg)).ValidTrace s1₀ trace s1Final) :
    FourLayerTraceSafe s4₀.policy.velocity_window_cap corrupt trace ∧
    (s1Final.cutPoisoned = true →
      ∀ i : Nat, i < 32 → s1Final.mem (UInt64.ofNat 0x180 + UInt64.ofNat i) = 0) := by
  exact isa_to_ideal_preserves_multiturn_safety corrupt pkDigestOf pk dealt localShare
    (fun bytes msg => signFromCustodianWithPeers Q custodian (unpackLane4Bytes32 bytes)
      (fun p => unpackLane4Bytes32 ((dealt p.val).getD [])) msg)
    (assembleShamirSubsetBytesSig Q)
    (poseidon2TagBytes (packLane4Bytes32 (evalShamirPolynomials polys Goldilocks.zero)))
    hBound Q.threshold_pos hTLeN hCorruptNd hCorruptLe
    (fun msg => by
      rw [hLocal]
      exact (signFromCustodianWithPeers_eq Q custodian
        (fun p => unpackLane4Bytes32 ((dealt p.val).getD [])) msg).symm)
    (fun msg => by
      unfold assembleShamirSubsetBytesSig
      have hShares : (fun p : Fin n => unpackLane4Bytes32 ((dealt p.val).getD [])) =
          (fun p => evalShamirPolynomials polys (Goldilocks.ofNat (p.val + 1))) := funext hDealt
      rw [hShares]
      exact assembleShamirSubsetSig_correct Q polys degree msg)
    hRel₀ hTrace1

open FourLayerWitness.Honest FourLayerWitness.HonestProof in
/-- Unconditional premise-inhabiting witness for `isa_to_ideal_preserves_multiturn_safety`. -/
theorem inhabited_isa_to_ideal_safety_premises :
    ∃ (corrupt : List (Fin 4))
      (pk : List UInt8)
      (dealt : Nat → Option (List UInt8))
      (custodianShare : List UInt8)
      (signFn : List UInt8 → List UInt8 → ByteArray)
      (assembleFn : (Nat → Option (List UInt8)) → List UInt8 → ByteArray)
      (oracleFn : List UInt8 → ByteArray)
      (hBound : 4 + 1 < 2 * 3)
      (hQPos : 0 < 3)
      (hQLeN : 3 ≤ 4)
      (hCorruptNd : corrupt.Nodup)
      (hCorruptLe : corrupt.length ≤ 1)
      (hSigM : ∀ msg : List UInt8, assembleFn dealt msg = signFn custodianShare msg)
      (hOraE : ∀ msg : List UInt8, assembleFn dealt msg = oracleFn msg)
      (s1₀ s1Final : Layer1ElfState)
      (s4₀ : Layer4IdealState (List UInt8))
      (trace : List (FourLayerReq 4 × FourLayerOut)),
      (isa_to_mir_to_protocol_to_ideal_sim corrupt id pk dealt custodianShare
        signFn assembleFn oracleFn
        hBound hQPos hQLeN hCorruptNd hCorruptLe hSigM hOraE).Rel s1₀ s4₀ ∧
      (layer1CompiledElfMachine (n := 4) 3 pk
        (fun m msg => signFn (readShareMem32 m) msg)).ValidTrace s1₀ trace s1Final ∧
      trace.length = 2 := by
  obtain ⟨s1₁, hS1_1, hRel12_1⟩ := hStep1_1
  obtain ⟨s1₂, hS1_2⟩ := hStep1_2 s1₁ hRel12_1
  have hTr1 : M1.ValidTrace s1₀ [(req1, out1), (req2, out2)] s1₂ :=
    .accept hS1_1 (.accept hS1_2 (.nil s1₂))
  exact ⟨corrupt, samplePkPin, dealt, sampleCustodianShare1, signFn, assembleFn, oracleFn,
    by decide, by decide, by decide, by decide, by decide, hSigM, hOraE,
    s1₀, s1₂, s4₀, [(req1, out1), (req2, out2)], hRel14, hTr1, rfl⟩

/-- Counterexample witness projection (`tooth_stateless_policy_breaks_four_layer_safety`):
    omitting stateful `MirPolicyGuardState` chaining admits a 2-turn Layer-1 trace violating
    `FourLayerTraceSafe`. -/
theorem tooth_stateless_policy_breaks_four_layer_safety :
    ∃ (s1₀ s1Final : Layer1ElfState)
      (s4₀ : Layer4IdealState (List UInt8))
      (badTrace : List (FourLayerReq 4 × FourLayerOut)),
      FourLayerWitness.Stateless.badM1.ValidTrace s1₀ badTrace s1Final ∧
      ¬ FourLayerTraceSafe s4₀.policy.velocity_window_cap FourLayerWitness.Stateless.corrupt badTrace := by
  obtain ⟨s1₀, s1F, s4₀, tr, hV, hNS, _, _⟩ :=
    tooth_stateless_policy_link_breaks_four_layer_ideal_safety
  exact ⟨s1₀, s1F, s4₀, tr, hV, hNS⟩

/-- Counterexample witness projection (`tooth_forged_bgin_opening_refused`):
    a forged Round-2 `BGIN19` opening is refused by `Layer1ElfState` (`step = none`). -/
theorem tooth_forged_bgin_opening_refused :
    ∃ (s1₀ : Layer1ElfState) (forgedReq : FourLayerReq 4),
      FourLayerWitness.ZeroGate.M1.step s1₀ forgedReq =
        (none : Option (Layer1ElfState × FourLayerOut)) :=
  ⟨FourLayerWitness.ZeroGate.s1₀, FourLayerWitness.ZeroGate.forgedReq,
   tooth_caller_zero_bgin_relation_rejected.2.2.2.2.1⟩

/-- Counterexample witness projection (`tooth_unregistered_round1_opening_refused`):
    an unregistered Round-1 commitment opening is refused by `Layer1ElfState` (`step = none`). -/
theorem tooth_unregistered_round1_opening_refused :
    ∃ (s1₀ : Layer1ElfState) (unregReq : FourLayerReq 4),
      FourLayerWitness.Unregistered.M1.step s1₀ unregReq =
        (none : Option (Layer1ElfState × FourLayerOut)) :=
  ⟨FourLayerWitness.Unregistered.s1Unreg, FourLayerWitness.Unregistered.unregReq,
   tooth_unregistered_round1_commitment_rejected.2.2.2.2.1⟩

/-- Counterexample witness projection (`tooth_forged_quorum_cert_refused`):
    a quorum request with a forged `BGIN19`/Poseidon2 custodian MAC tag is refused (`step = none`). -/
theorem tooth_forged_quorum_cert_refused :
    ∃ (s1₀ : Layer1ElfState) (forgedTagReq : FourLayerReq 4),
      FourLayerWitness.Unauthenticated.M1.step s1₀ forgedTagReq =
        (none : Option (Layer1ElfState × FourLayerOut)) :=
  ⟨FourLayerWitness.Unauthenticated.s1₀, FourLayerWitness.Unauthenticated.forgedTagReq,
   tooth_unauthenticated_quorum_member_rejected.2.2.2.1⟩

end Qsag

#verify_inhabited Qsag.isa_to_ideal_preserves_multiturn_safety Qsag.inhabited_isa_to_ideal_safety_premises
#tooth_pair Qsag.isa_to_ideal_preserves_multiturn_safety vs Qsag.tooth_stateless_policy_breaks_four_layer_safety
#tooth_pair Qsag.isa_to_ideal_preserves_multiturn_safety vs Qsag.tooth_forged_bgin_opening_refused
#tooth_pair Qsag.isa_to_ideal_preserves_multiturn_safety vs Qsag.tooth_unregistered_round1_opening_refused
#tooth_pair Qsag.isa_to_ideal_preserves_multiturn_safety vs Qsag.tooth_forged_quorum_cert_refused
#tooth_pair Qsag.shamirSubset_preserves_multiturn_safety vs Qsag.tooth_stateless_policy_breaks_four_layer_safety
#verify_constructive Qsag.inhabited_four_layer_chain
