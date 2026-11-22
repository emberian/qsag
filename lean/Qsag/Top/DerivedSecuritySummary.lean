module
/-
# Qsag.Top.DerivedSecuritySummary — summary of reductions to stated experiments

`qsag_composed_game_security_summary` collects statements of two kinds and no others.

**Clause G (bounds on experiments).** Each conjunct bounds the winning probability, or the
distinguishing advantage, of an experiment over a finite coin space by a sum of bounds on named
experiments, for every adversary family:

1. `ExecEufCmaGame` (Jorts/Baggy, epoch latch) through any `ExecEufCmaReductionEmbedding` into
   `Spec.itsrGame`, `Spec.smDtTcrGame` and `Spec.smDtPreGame`. The embedding is a parameter;
   instances exist for the concrete suites of `ExecEufCmaClosedGame`.
2. `Compact1122.eufGame`, the one-time forgery experiment of the target-sum Winternitz layer of
   `Compact1122`, by `ITSR`, `SM-DT-TCR`, `SM-DT-PRE` and `Compact1122.ChainLinkHard`, with the
   reduction adversaries of `Compact1122ClosedEufCma`. The reduction uses the public equations of the challenger.
3. The two-stage sliced `[CWYZ26]` WHIR schedule `flatHemSlicedSched`, whose schedule
   certificate is proved: acceptance of a false statement by a `Q`-query quantum adversary is
   bounded by the schedule error plus the Merkle-collision event. The deployed `nv = 24`
   schedule is not a conjunct; its certificate is a hypothesis of
   `deployed_whir_exec_closed_qrom_128`.
4. The blinded SPDZ MAC check with a PRG-expanded honest randomizer against the simulator that
   does not read the MAC key, by `Spec.PrfHard` plus `1 / |F|`.

**Clause F (facts about deployed objects, no hypothesis on an adversary).**

5. The `24`-repetition RLWE OR-sigma fork extraction dichotomy at the production bounds.
6. The production `Q192` Bernoulli sampler (`gaussian_exp_probability::<24>` and the 192-bit
   comparison) against the discrete Gaussian with weights `q^(x^2)`, for every rational `q` in
   the enclosure `InExpNegEnclosure` (width below `2^-459`) of the two Taylor partial sums of
   `exp(-1/980000)`: every acceptance probability is within `49 / 2^192` below `q^(x^2)`, and
   across the `49152` Gaussian coordinates of the RLWE proof the joint law of the accepted
   proposals is within total variation `2^-168` of the product Gaussian. That
   `exp(-1/980000)` lies in the enclosure is the alternating-series estimate, which is not
   formalised; real exponentials are not objects of this library.
7. Row `0` of E10’s balanced eleven-tap fixture has bias strictly between `2^-220` and `2^-219`, and
   the Stern–Dumer work estimate exceeds `2^256` for `q ≤ 32`; neither uses the balance premise
   `≤ 2047`.

Not in the summary, by construction: no conjunct evaluates a closed-form bound expression at a
query ceiling (Clause II of `SecurityBounds`), and no conjunct takes a bound on an extractor
event of the run as a hypothesis (Clause III there).

What the summary does not say. The hardness propositions are relative to adversary classes that
are parameters; nothing here bounds them for a deployed primitive. Clause F is not a statement
about adversaries: conjunct 5 is a disjunction without probabilities, and conjuncts 6 and 7 are
exact arithmetic about the deployed sampler and tap row.
-/

public import Qsag.Top.ClosedProtocolReductions
public import Qsag.Top.Credentials
public import Qsag.Protocol.Signing.Compact1122ClosedEufCma
public import Qsag.Protocol.Threshold.MultiSessionMacBlindHybrid
public import Qsag.Math.Q192BernoulliTailBound
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Top

set_option autoImplicit false

/-- **Summary of reductions to stated experiments.** Clause G: four bounds on experiments by
    bounds on named experiments. Clause F: three facts about deployed objects. The module header
    says what each conjunct does and does not claim. -/
theorem qsag_composed_game_security_summary :
    -- (G1)
    (∀ {n qHash qSign : Nat} {hPos : 0 < n} {suite : Qsag.TweakableHashSuite}
        {params : Qsag.PqHashParams} {keygen : Fin n → Qsag.PqSecretKey}
        {adv : Fin n → Qsag.SeedWithheldEufCmaAdv qHash qSign}
        (E : Qsag.ExecEufCmaReductionEmbedding hPos suite params keygen adv)
        {εItsr εTcr εPre : Qsag.Spec.RatBound},
        Qsag.Spec.ItsrHard E.𝒜I E.hmsg E.randLen E.qItsr εItsr →
        Qsag.Spec.SmDtTcrHard E.𝒜T E.th E.seedLen E.qTcr εTcr →
        Qsag.Spec.SmDtPreHard E.𝒜P E.th E.seedLen E.inputLen E.qPre εPre →
        Qsag.Spec.GameBound (Qsag.ExecEufCmaGame hPos suite params keygen adv).winProb
          ((εItsr.add εTcr).add εPre)) ∧
    -- (G2)
    (∀ {th : Qsag.Compact1122.TwHash}
        (tw : Nat → Qsag.Spec.Bytes) (_ : ∀ a b : Nat, tw a = tw b → a = b)
        (_ : ∀ s t m : Qsag.Spec.Bytes, (th s t m).length = 32)
        (code : Qsag.Spec.Bytes → Qsag.Spec.Bytes → List Nat)
        (_ : ∀ r m : Qsag.Spec.Bytes, Qsag.Compact1122.CodeOk (code r m))
        (frame : Qsag.Spec.Bytes → Qsag.Spec.Bytes → Qsag.Spec.Bytes → Qsag.Spec.Bytes)
        (_ : ∀ s r m m' : Qsag.Spec.Bytes, frame s r m = frame s r m' → m = m')
        {nF : Nat} (hPos : 0 < Qsag.Compact1122.eufCoins nF)
        (forger : Fin nF → Qsag.Compact1122.Forger)
        {𝒜I : Qsag.Spec.Code Qsag.Spec.byteOracleIface (Qsag.Spec.Bytes × Qsag.Spec.Bytes) → Prop}
        {𝒜T 𝒜P : Qsag.Spec.Code Qsag.Spec.targetIface Qsag.Spec.TargetBreak → Prop}
        {εItsr εTcr εPre εLink : Qsag.Spec.RatBound},
        Qsag.Spec.ItsrHard 𝒜I (Qsag.Compact1122.codeSubset code) 32 1 εItsr →
        Qsag.Spec.SmDtTcrHard 𝒜T th 32 3231 εTcr →
        Qsag.Spec.SmDtPreHard 𝒜P th 32 32 1 εPre →
        Qsag.Compact1122.ChainLinkHard 𝒜P th tw εLink →
        (∀ b, 𝒜I (Qsag.Compact1122.itsrAdvAt th tw code frame forger b)) →
        (∀ a, 𝒜T (Qsag.Compact1122.tcrAdvAt th tw code frame forger a)) →
        (∀ (i : Fin 34) (j : Nat) b, 𝒜P (Qsag.Compact1122.linkAdvAt th tw code frame forger i j b)) →
        Qsag.Spec.GameBound (Qsag.Compact1122.eufGame hPos th tw code frame forger).winProb
          ((εItsr.add εTcr).add
            ((Qsag.Spec.RatBound.scale 34 εPre).add (Qsag.Spec.RatBound.scale 3196 εLink)))) ∧
    -- (G3)
    (∀ {D : Type} [DecidableEq D] {cardX cardAnc Q : Nat}
        (M : Qsag.ClosedFs.MerkleSetup D Qsag.QuarticGoldilocks)
        (c : Qsag.ClosedFs.FsCodec (Qsag.ClosedWhir.WhirMsg Qsag.QuarticGoldilocks)
          Qsag.ClosedWhir.flatHemSlicedSched.numRounds cardX)
        (aux : Fin cardX → List (Qsag.QuarticGoldilocks × List D))
        (x : Qsag.ClosedWhir.WhirStmt Qsag.QuarticGoldilocks)
        (_ : ¬ Qsag.ClosedWhir.whirInLang Qsag.ClosedWhir.flatHemSlicedEnv
          Qsag.ClosedWhir.flatHemSlicedSched x)
        (A : Qsag.QuantumAdv cardX 256 cardAnc Q),
        Qsag.Spec.GameBound
          (Qsag.Spec.RatBound.ofBudget
            (WhirSoundnessWinProb Qsag.ClosedWhir.flatHemSlicedEnv
              Qsag.ClosedWhir.flatHemSlicedSched M c aux x A))
          (Qsag.Spec.RatBound.ofBudget
            (Qsag.RatBound.add
              (Qsag.ClosedWhir.scheduleQromError Qsag.ClosedWhir.flatHemSlicedSched Q)
              (WhirMerkleCollisionWinProb Qsag.ClosedWhir.flatHemSlicedEnv
                Qsag.ClosedWhir.flatHemSlicedSched M c aux x A)))) ∧
    -- (G4) blinded SPDZ MAC check with a PRG-expanded honest randomizer
    (∀ {F : Type} [Qsag.LawfulField F] [DecidableEq F] {cardK cardF nA : Nat}
        (hPos : 0 < (cardK * cardF) * (cardF * nA)) (hF : 0 < cardF)
        (enum : Qsag.SimpleEquiv (Fin cardF) F)
        (prg : Qsag.Spec.Bytes → Qsag.Spec.Bytes → Qsag.Spec.Bytes) (keyLen outLen : Nat)
        (keySampler : Fin cardK → Qsag.Spec.Bytes) (maskSampler : Fin cardF → Qsag.Spec.Bytes)
        (decodeMask : Qsag.Spec.Bytes → F)
        (_ : ∀ i : Fin cardF, decodeMask (maskSampler i) = enum.toFun i)
        (_ : Qsag.Spec.UniformOn (Qsag.Spec.PrfSampleOk keyLen 0 outLen)
          (Qsag.MacBlind.prgPrfSampler keySampler maskSampler))
        {𝒜 : Qsag.Spec.Code Qsag.Spec.byteOracleIface Bool → Prop} {εPrf : Qsag.Spec.RatBound}
        (_ : Qsag.Spec.PrfHard 𝒜 prg keyLen 0 outLen 1 εPrf)
        (adv : Fin nA → Qsag.MacBlind.MacCheckAdv F)
        (_ : ∀ (alpha : F) (a : Fin nA),
          𝒜 (Qsag.MacBlind.macBlindPrfDistinguisher decodeMask alpha (adv a))),
        Qsag.Spec.GameBound
          (Qsag.Spec.AdvDist
            (Qsag.MacBlind.macCheckRealGame hPos enum prg keySampler decodeMask adv)
            (Qsag.MacBlind.macCheckSimGame hPos enum adv))
          (εPrf.add ⟨1, cardF, hF⟩)) ∧
    -- (F5) 24-repetition RLWE OR-sigma fork extraction: secret recovery or a short Ring-SIS vector
    (∀ (stmt : Qsag.RlweOrSigmaStatement 10 12289) (_ : stmt.Bz ≤ Qsag.rlweProductionBz)
        (c c' : Fin 24 → Qsag.SignedMonomialChal 10)
        (tr tr' : Qsag.RlweOrSigmaTranscript 24 10 12289)
        (hForkE : Qsag.ValidRlweOrSigmaEuclideanFork 24 10 12289 stmt Qsag.rlweZkpokPairL2SqBound
          c c' tr tr')
        (sTrue eTrue : Qsag.CycPolyInt 10)
        (_ : Qsag.ShortRlweKeyRelation stmt.A (stmt.branchU
          (Qsag.extract_rlwe_or_sigma_24_short_witness stmt c c' tr tr'
            hForkE.base.t0_eq hForkE.base.t1_eq hForkE.base.chal_ne
            hForkE.base.acc1 hForkE.base.acc2).branch) 1 sTrue eTrue)
        (_ : Qsag.cycIntL2Sq sTrue + Qsag.cycIntL2Sq eTrue ≤ 2048),
        let w := Qsag.extract_rlwe_or_sigma_24_short_witness stmt c c' tr tr'
          hForkE.base.t0_eq hForkE.base.t1_eq hForkE.base.chal_ne
          hForkE.base.acc1 hForkE.base.acc2
        (Qsag.cycZqCentered (Qsag.cycZqMul w.rRelInvZq (Qsag.cycIntToZq 12289 w.sIso)) = sTrue ∧
         Qsag.cycZqCentered (Qsag.cycZqMul w.rRelInvZq (Qsag.cycIntToZq 12289 w.eIso)) = eTrue) ∨
        Qsag.NonVacuousRingSis1024 stmt.A 6142 Qsag.rlweExtractedSisL2SqBound
          (Qsag.cycIntSub w.sIso (Qsag.cycIntMul w.rRel sTrue))
          (Qsag.cycIntSub w.eIso (Qsag.cycIntMul w.rRel eTrue))) ∧
    -- (F6) production Q192 Bernoulli sampler against the discrete Gaussian with any rational
    --      base in the certified enclosure of exp(-1/980000): 49 units of 2^-192 per acceptance
    --      test, and total variation below 2^-168 across 49152 Gaussian coordinates
    ((∀ (e : Nat), e < 2 ^ 24 → ∀ (a b : Nat), Qsag.InExpNegEnclosure a b →
        (Qsag.q192BernoulliGame (Qsag.gaussianExpProbability 24 e)).winCount * b ^ e ≤
          2 ^ 192 * a ^ e ∧
        2 ^ 192 * a ^ e ≤
          ((Qsag.q192BernoulliGame (Qsag.gaussianExpProbability 24 e)).winCount + 49) * b ^ e) ∧
      (∀ (a b : Nat), Qsag.InExpNegEnclosure a b →
        ∀ (halves : List Nat), halves.length ≤ 49152 →
        (∀ h, h ∈ halves → h = 3070 ∨ h = 3072) →
        Qsag.jointL1 (Qsag.rationalGaussianBatch a b halves) * 2 ^ 168 <
          2 * (Qsag.jointTotal Qsag.WeightPair.impl (Qsag.rationalGaussianBatch a b halves) *
            Qsag.jointTotal Qsag.WeightPair.ideal (Qsag.rationalGaussianBatch a b halves)))) ∧
    -- (F7) PCG row bias and Stern–Dumer work, no balance premise
    (∀ (q l : Nat), q ≤ 32 →
      (Qsag.TapRowBias.imbalanceProd 32768 Qsag.TapRowBias.prodRow0Bal11Weights * 2 ^ 219 < 32768 ^ 64 ∧
        32768 ^ 64 < Qsag.TapRowBias.imbalanceProd 32768 Qsag.TapRowBias.prodRow0Bal11Weights * 2 ^ 220) ∧
      Qsag.sternDumerWorkExceedsPow2 Qsag.pcgDepth15Cols Qsag.pcgDenseRows Qsag.pcgDenseWeightT q l 256) := by
  refine ⟨fun E _ _ _ hI hT hP => jorts_baggy_closed_euf_cma_spec_assumptions_bound E hI hT hP,
    fun tw hTw hOut code hCode frame hFrame _ hPos forger _ _ _ _ _ _ _
      hI hT hP hL hAI hAT hAP =>
      Qsag.Compact1122.compact1122_closed_euf_cma_bound tw hTw hOut code hCode
        frame hFrame hPos forger hI hT hP hL hAI hAT hAP,
    fun M c aux x hx A => flatHemSlicedWhir_closed_qrom_soundness M c aux x hx A,
    fun hPos hF enum prg keyLen outLen keySampler maskSampler decodeMask hDecode hU _ _ hPrf adv
      hA =>
      Qsag.MacBlind.computational_macBlind_spdz_security_bound hPos hF enum prg keyLen outLen
        keySampler maskSampler decodeMask hDecode hU hPrf adv hA,
    fun stmt hBz c c' tr tr' hForkE sTrue eTrue hKey hKeyL2 =>
      Qsag.extract_rlwe_or_sigma_24_euclidean_sis_dichotomy stmt hBz c c' tr tr' hForkE sTrue eTrue
        hKey hKeyL2,
    ⟨fun e he a b hq => Qsag.q192_sampler_pointwise_error_rational_base e he a b hq,
      fun a b hq halves hLen hHalves =>
        Qsag.q192_rlwe_batch_tvd_bound_rational_base a b hq halves hLen hHalves⟩,
    fun q l hq => ⟨⟨(pcg_dual_lpn_bias_in_spec_ratBound q l hq).1.1,
      (pcg_dual_lpn_bias_in_spec_ratBound q l hq).1.2.1⟩,
      (pcg_dual_lpn_bias_in_spec_ratBound q l hq).2.2.1⟩⟩

/-- Conjunct 7 of the summary, projected. -/
theorem summary_pcg_conjunct (q l : Nat) (hq : q ≤ 32) :
    (Qsag.TapRowBias.imbalanceProd 32768 Qsag.TapRowBias.prodRow0Bal11Weights * 2 ^ 219 < 32768 ^ 64 ∧
      32768 ^ 64 < Qsag.TapRowBias.imbalanceProd 32768 Qsag.TapRowBias.prodRow0Bal11Weights * 2 ^ 220) ∧
    Qsag.sternDumerWorkExceedsPow2 Qsag.pcgDepth15Cols Qsag.pcgDenseRows Qsag.pcgDenseWeightT q l
      256 :=
  qsag_composed_game_security_summary.2.2.2.2.2.2 q l hq

/-- **Tooth: the legacy balance premise is false for the three-tap row.** A statement about row
    `0` of the legacy three-tap matrix that assumed every tree balanced within `2047` would assume a
    falsehood; conjunct 7 of the summary takes no such premise. -/
theorem tooth_legacy_balance_premise_false_for_three_tap_row :
    ¬ (∀ w ∈ Qsag.TapRowBias.prodRow0Weights, Qsag.TapRowBias.imbalance 32768 w ≤ 2047) :=
  Qsag.TapRowBias.prodRow0_balance_premise_fails.1

#verify_constructive
  Qsag.Top.qsag_composed_game_security_summary
  Qsag.Top.summary_pcg_conjunct
  Qsag.Top.tooth_legacy_balance_premise_false_for_three_tap_row

end Qsag.Top
end
