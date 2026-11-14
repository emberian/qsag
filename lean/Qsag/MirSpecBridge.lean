module

public import Qsag.MirSpecBridgeCore
public import Qsag.MirSpecBridgeWitnesses
import all Qsag.MirSpecBridgeWitnesses

/-! Public entry point for the hand-written MIR guard models, their four-layer
simulation chain, and concrete accepted/rejected trace witnesses. The extracted
Rust-to-model welds live in the separate `qsag_aeneas` package. -/

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

end Qsag
