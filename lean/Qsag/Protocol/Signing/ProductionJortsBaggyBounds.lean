module
/-
# Qsag.Protocol.Signing.ProductionJortsBaggyBounds — Concrete `< 2^{-128}` Classical & Post-Quantum `QROM` Multi-Hop EUF-CMA Bounds for `Jorts`, `Baggy`, `Corduroy` & `SLH-DSA`

Instantiates `ProductionParamRefinement` across all canonical QSAG and NIST FIPS 205 Category-1
profiles with machine-checked `< 2^{-128}` (`⟨1, 2 ^ 128, by decide⟩`) classical (`qEval ≤ 2^96`)
and post-quantum `QROM` / Grover (`qEval ≤ 2^48`) security bounds:

1. **Stateful `Jorts` (`jortsProdParams`):**
   * `jortsProd_classical_euf_cma_lt_2_neg_128`, `jortsProd_pq_qrom_euf_cma_lt_2_neg_128`,
     and `jortsProd_pq_qrom_budget_lt_2_neg_128`.
2. **Stateless `Baggy` (`PorsFpSecurity.BaggySha3_128f` & `baggyProdParams`) and `Corduroy` (`corduroyProdParams`):**
   * `baggySha3_128f_pors_itsr_lt_2_neg_131`, `baggySha3_128f_classical_euf_cma_lt_2_neg_128`,
     `baggySha3_128f_pq_qrom_euf_cma_lt_2_neg_128`, `corduroyProd_concrete_euf_cma_bound`,
     and `baggyProd_concrete_euf_cma_bound`.
3. **NIST FIPS 205 `SLH-DSA-SHAKE-128s` & `128f`:**
   * `one_sub_pow_mul_truncBinom_le`, `fips205_interleaved_itsr_128s_128f_bounds`,
     `fips205_slhDsa128s_concrete_security_lt_2_neg_128`, and
     `fips205_slhDsa128f_concrete_security_lt_2_neg_128`.
-/

public import Qsag.Protocol.Signing.ProductionParamRefinement
import Qsag.Tactic.AssuranceKit

public section
attribute [-instance] Fin.instLinearOrderPackage
namespace Qsag
open scoped Qsag.Spec

set_option autoImplicit false
set_option exponentiation.threshold 512
set_option maxRecDepth 4096

/-! ## §1. Concrete `< 2^{-128}` EUF-CMA Theorems for `Jorts`, `Baggy`, and `Corduroy` -/

/-- Exact multi-hop rational security budget for `PqHashParams` profiles. -/
@[expose] def pqMultiHopBudget (params : PqHashParams) (qSign : Nat)
    (εItsr εTcr εPre εPrfSec εPrfMsg : Spec.RatBound) : Spec.RatBound :=
  ((((εItsr.add (Spec.RatBound.scale (prodPathTargetCount params qSign) εTcr)).add
      (Spec.RatBound.scale (prodPreCandidateBudget params) εPre)).add εPrfSec).add εPrfMsg)

/-- Stateful `Jorts` multi-hop EUF-CMA budget (`ITSR = 0`). -/
@[expose] def jortsMultiHopBudget (qSign : Nat)
    (εPrfMsg εPrfSec εTcr εPre : Spec.RatBound) : Spec.RatBound :=
  pqMultiHopBudget jortsProdParams qSign Spec.RatBound.zero εTcr εPre εPrfSec εPrfMsg

theorem pqMultiHopBudget_mono (params : PqHashParams) {q₁ q₂ : Nat} (hq : q₁ ≤ q₂)
    {i₁ i₂ t₁ t₂ p₁ p₂ s₁ s₂ m₁ m₂ : Spec.RatBound}
    (hi : i₁.le i₂) (ht : t₁.le t₂) (hp : p₁.le p₂) (hs : s₁.le s₂) (hm : m₁.le m₂) :
    (pqMultiHopBudget params q₁ i₁ t₁ p₁ s₁ m₁).le (pqMultiHopBudget params q₂ i₂ t₂ p₂ s₂ m₂) := by
  have hCnt := prodPathTargetCount_mono params hq
  have hTcrScale : (Spec.RatBound.scale (prodPathTargetCount params q₁) t₁).le
      (Spec.RatBound.scale (prodPathTargetCount params q₂) t₂) := by
    refine Spec.RatBound.le_trans ?_ (Spec.RatBound.scale_le_scale _ ht)
    unfold Spec.RatBound.le Spec.RatBound.scale; dsimp only
    exact Nat.mul_le_mul_right t₁.den (Nat.mul_le_mul_right t₁.num hCnt)
  exact Spec.RatBound.add_le_add
    (Spec.RatBound.add_le_add
      (Spec.RatBound.add_le_add (Spec.RatBound.add_le_add hi hTcrScale)
        (Spec.RatBound.scale_le_scale _ hp)) hs) hm

/-- **`jortsProdParams` Classical (`256`-Bit, `qSign ≤ 2^16`, `qEval ≤ 2^96`) Multi-Hop EUF-CMA
    `< 2^{-128}` Bound (`jortsProd_classical_euf_cma_lt_2_neg_128`).** -/
theorem jortsProd_classical_euf_cma_lt_2_neg_128 {n nC1 nRest nC2 nA qHash qSign qEval : Nat}
    (hPos : 0 < n) (suite : TweakableHashSuite) (hqSign : qSign ≤ 2 ^ 16) (hqEval : qEval ≤ 2 ^ 96)
    (seedLen keyLen qPrfMsg qPrfSec : Nat) (hSeedPos : 0 < seedLen) (hqPrfMsg : qSign ≤ qPrfMsg)
    (hqPrfSec : prfSecQueryBudget jortsProdParams qSign ≤ qPrfSec)
    (π1 : Spec.CoinSplit n nC1 nRest) (π2 : Spec.CoinSplit nRest nC2 nA)
    (sampleMsg : Fin nC1 → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (hSampleMsg : Spec.UniformOn (Spec.PrfSampleOk keyLen 65 32) sampleMsg)
    (sampleSec : Fin nC2 → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (hSampleSec : Spec.UniformOn (Spec.PrfSampleOk keyLen (seedLen + 32) 32) sampleSec)
    (pkSeedA : Fin nA → List UInt8) (hSeedLen : ∀ a, (pkSeedA a).length = seedLen)
    (adv : Fin nA → SeedWithheldEufCmaAdv qHash qSign)
    {𝒜Msg 𝒜Sec : Spec.Code Spec.byteOracleIface Bool → Prop}
    (hClassMsg : ∀ r : Fin nRest, 𝒜Msg (prfMsgHopDistinguisher true suite jortsProdParams
      (pkSeedA (π2.advc r)) (sampleSec (π2.chal r)).1 (adv (π2.advc r))))
    (hClassSec : ∀ b : Fin (nC1 * nA),
      let sp := Spec.CoinSplit.prod nC1 nA
      𝒜Sec (prfSecHopDistinguisher true suite jortsProdParams (pkSeedA (sp.advc b))
        (sampleMsg (sp.chal b)).2 (adv (sp.advc b))))
    {εPrfMsg εPrfSec εTcr εPre : Spec.RatBound}
    (hPrfMsg : Spec.PrfHard 𝒜Msg (suitePrfMsg65 suite) keyLen 65 32 qPrfMsg εPrfMsg)
    (hPrfSec : Spec.PrfHard 𝒜Sec (suitePrfSec seedLen suite) keyLen (seedLen + 32) 32 qPrfSec εPrfSec)
    (hTcrB : ∀ slot : Fin (prodPathTargetCount jortsProdParams qSign), Spec.GameBound
      (idealSlotTcrGame hPos suite jortsProdParams
        (.inl (by rw [jortsProdParams, jortsPoseidon2Params_eq]))
        π1 π2 sampleMsg sampleSec pkSeedA adv slot.val).winProb εTcr)
    (hPreB : ∀ slot : Fin (prodPreCandidateBudget jortsProdParams), Spec.GameBound
      (idealSlotPreGame hPos suite jortsProdParams π1 π2 sampleMsg sampleSec pkSeedA adv slot.val).winProb εPre)
    (hEpsMsg : εPrfMsg.le (classical256PrimEps qEval)) (hEpsSec : εPrfSec.le (classical256PrimEps qEval))
    (hEpsTcr : εTcr.le (classical256PrimEps qEval)) (hEpsPre : εPre.le (classical256PrimEps qEval)) :
    (jortsMultiHopBudget qSign εPrfMsg εPrfSec εTcr εPre).lt ⟨1, 2 ^ 128, by decide⟩ ∧
    Spec.GameBound (ExecEufCmaGame hPos suite jortsProdParams
      (multiHopKeygen π1 π2 sampleMsg sampleSec pkSeedA) (multiHopAdv π1 π2 adv)).winProb
      ⟨1, 2 ^ 128, by decide⟩ := by
  have hwJ : jortsProdParams.w = 4 ∨ jortsProdParams.w = 16 :=
    .inl (by rw [jortsProdParams, jortsPoseidon2Params_eq])
  have hItsrZero : Spec.GameBound
      (idealSlotItsrGame hPos suite jortsProdParams hwJ π1 π2 sampleMsg sampleSec pkSeedA adv).winProb
      Spec.RatBound.zero :=
    Spec.FinGame.bound_zero_of_forall_lose _ (fun _ => idealPrfItsrWin_of_forsTrees_zero suite
      jortsProdParams hwJ (by rw [jortsProdParams, jortsPoseidon2Params_eq]) _ _ _ _)
  have hGame := hulsing_multiHop_idealSlot_euf_cma_bound hPos suite jortsProdParams hwJ
    seedLen keyLen qPrfMsg qPrfSec hSeedPos hqPrfMsg hqPrfSec π1 π2 sampleMsg hSampleMsg
    sampleSec hSampleSec pkSeedA hSeedLen adv hClassMsg hClassSec hPrfMsg hPrfSec hItsrZero hTcrB hPreB
  have hPrim := classical256PrimEps_mono hqEval
  have hMono := pqMultiHopBudget_mono jortsProdParams hqSign
    (Spec.RatBound.le_refl Spec.RatBound.zero)
    (Spec.RatBound.le_trans hEpsTcr hPrim) (Spec.RatBound.le_trans hEpsPre hPrim)
    (Spec.RatBound.le_trans hEpsSec hPrim) (Spec.RatBound.le_trans hEpsMsg hPrim)
  have hTopLt : (jortsMultiHopBudget (2 ^ 16) (classical256PrimEps (2 ^ 96))
      (classical256PrimEps (2 ^ 96)) (classical256PrimEps (2 ^ 96))
      (classical256PrimEps (2 ^ 96))).lt ⟨1, 2 ^ 128, by decide⟩ := by
    unfold jortsMultiHopBudget pqMultiHopBudget
    rw [jortsProdParams_accounting.2.2.2.1, jortsProdParams_accounting.2.2.2.2.1]; decide +kernel
  have hLt := Spec.RatBound.lt_of_le_of_lt hMono hTopLt
  exact ⟨hLt, Spec.RatBound.le_trans hGame (Spec.RatBound.le_of_lt hLt)⟩

/-- **`jortsProdParams` Post-Quantum `QROM` (`qSign ≤ 2^16`, Grover `qEval ≤ 2^48`) Multi-Hop
    EUF-CMA `< 2^{-128}` Bound (`jortsProd_pq_qrom_euf_cma_lt_2_neg_128`).** -/
theorem jortsProd_pq_qrom_euf_cma_lt_2_neg_128 {n nC1 nRest nC2 nA qHash qSign qEval : Nat}
    (hPos : 0 < n) (suite : TweakableHashSuite) (hqSign : qSign ≤ 2 ^ 16) (hqEval : qEval ≤ 2 ^ 48)
    (seedLen keyLen qPrfMsg qPrfSec : Nat) (hSeedPos : 0 < seedLen) (hqPrfMsg : qSign ≤ qPrfMsg)
    (hqPrfSec : prfSecQueryBudget jortsProdParams qSign ≤ qPrfSec)
    (π1 : Spec.CoinSplit n nC1 nRest) (π2 : Spec.CoinSplit nRest nC2 nA)
    (sampleMsg : Fin nC1 → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (hSampleMsg : Spec.UniformOn (Spec.PrfSampleOk keyLen 65 32) sampleMsg)
    (sampleSec : Fin nC2 → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (hSampleSec : Spec.UniformOn (Spec.PrfSampleOk keyLen (seedLen + 32) 32) sampleSec)
    (pkSeedA : Fin nA → List UInt8) (hSeedLen : ∀ a, (pkSeedA a).length = seedLen)
    (adv : Fin nA → SeedWithheldEufCmaAdv qHash qSign)
    {𝒜Msg 𝒜Sec : Spec.Code Spec.byteOracleIface Bool → Prop}
    (hClassMsg : ∀ r : Fin nRest, 𝒜Msg (prfMsgHopDistinguisher true suite jortsProdParams
      (pkSeedA (π2.advc r)) (sampleSec (π2.chal r)).1 (adv (π2.advc r))))
    (hClassSec : ∀ b : Fin (nC1 * nA),
      let sp := Spec.CoinSplit.prod nC1 nA
      𝒜Sec (prfSecHopDistinguisher true suite jortsProdParams (pkSeedA (sp.advc b))
        (sampleMsg (sp.chal b)).2 (adv (sp.advc b))))
    {εPrfMsg εPrfSec εTcr εPre : Spec.RatBound}
    (hPrfMsg : Spec.PrfHard 𝒜Msg (suitePrfMsg65 suite) keyLen 65 32 qPrfMsg εPrfMsg)
    (hPrfSec : Spec.PrfHard 𝒜Sec (suitePrfSec seedLen suite) keyLen (seedLen + 32) 32 qPrfSec εPrfSec)
    (hTcrB : ∀ slot : Fin (prodPathTargetCount jortsProdParams qSign), Spec.GameBound
      (idealSlotTcrGame hPos suite jortsProdParams
        (.inl (by rw [jortsProdParams, jortsPoseidon2Params_eq]))
        π1 π2 sampleMsg sampleSec pkSeedA adv slot.val).winProb εTcr)
    (hPreB : ∀ slot : Fin (prodPreCandidateBudget jortsProdParams), Spec.GameBound
      (idealSlotPreGame hPos suite jortsProdParams π1 π2 sampleMsg sampleSec pkSeedA adv slot.val).winProb εPre)
    (hEpsMsg : εPrfMsg.le (pqQrom256PrimEps qEval)) (hEpsSec : εPrfSec.le (pqQrom256PrimEps qEval))
    (hEpsTcr : εTcr.le (pqQrom256PrimEps qEval)) (hEpsPre : εPre.le (pqQrom256PrimEps qEval)) :
    (jortsMultiHopBudget qSign εPrfMsg εPrfSec εTcr εPre).lt ⟨1, 2 ^ 128, by decide⟩ ∧
    Spec.GameBound (ExecEufCmaGame hPos suite jortsProdParams
      (multiHopKeygen π1 π2 sampleMsg sampleSec pkSeedA) (multiHopAdv π1 π2 adv)).winProb
      ⟨1, 2 ^ 128, by decide⟩ := by
  have hwJ : jortsProdParams.w = 4 ∨ jortsProdParams.w = 16 :=
    .inl (by rw [jortsProdParams, jortsPoseidon2Params_eq])
  have hItsrZero : Spec.GameBound
      (idealSlotItsrGame hPos suite jortsProdParams hwJ π1 π2 sampleMsg sampleSec pkSeedA adv).winProb
      Spec.RatBound.zero :=
    Spec.FinGame.bound_zero_of_forall_lose _ (fun _ => idealPrfItsrWin_of_forsTrees_zero suite
      jortsProdParams hwJ (by rw [jortsProdParams, jortsPoseidon2Params_eq]) _ _ _ _)
  have hGame := hulsing_multiHop_idealSlot_euf_cma_bound hPos suite jortsProdParams hwJ
    seedLen keyLen qPrfMsg qPrfSec hSeedPos hqPrfMsg hqPrfSec π1 π2 sampleMsg hSampleMsg
    sampleSec hSampleSec pkSeedA hSeedLen adv hClassMsg hClassSec hPrfMsg hPrfSec hItsrZero hTcrB hPreB
  have hPrim := pqQrom256PrimEps_mono hqEval
  have hMono := pqMultiHopBudget_mono jortsProdParams hqSign
    (Spec.RatBound.le_refl Spec.RatBound.zero)
    (Spec.RatBound.le_trans hEpsTcr hPrim) (Spec.RatBound.le_trans hEpsPre hPrim)
    (Spec.RatBound.le_trans hEpsSec hPrim) (Spec.RatBound.le_trans hEpsMsg hPrim)
  have hTopLt : (jortsMultiHopBudget (2 ^ 16) (pqQrom256PrimEps (2 ^ 48))
      (pqQrom256PrimEps (2 ^ 48)) (pqQrom256PrimEps (2 ^ 48))
      (pqQrom256PrimEps (2 ^ 48))).lt ⟨1, 2 ^ 128, by decide⟩ := by
    unfold jortsMultiHopBudget pqMultiHopBudget
    rw [jortsProdParams_accounting.2.2.2.1, jortsProdParams_accounting.2.2.2.2.1]; decide +kernel
  have hLt := Spec.RatBound.lt_of_le_of_lt hMono hTopLt
  exact ⟨hLt, Spec.RatBound.le_trans hGame (Spec.RatBound.le_of_lt hLt)⟩

/-- Standalone rational PQ QROM `< 2^{-128}` budget theorem for `jortsProdParams` (`qSign ≤ 2^16, qEval ≤ 2^48`). -/
theorem jortsProd_pq_qrom_budget_lt_2_neg_128 {qSign qEval : Nat}
    (hqSign : qSign ≤ 2 ^ 16) (hqEval : qEval ≤ 2 ^ 48) :
    (jortsMultiHopBudget qSign (pqQrom256PrimEps qEval) (pqQrom256PrimEps qEval)
      (pqQrom256PrimEps qEval) (pqQrom256PrimEps qEval)).lt ⟨1, 2 ^ 128, by decide⟩ := by
  have hPrim := pqQrom256PrimEps_mono hqEval
  have hTopLt : (jortsMultiHopBudget (2 ^ 16) (pqQrom256PrimEps (2 ^ 48))
      (pqQrom256PrimEps (2 ^ 48)) (pqQrom256PrimEps (2 ^ 48))
      (pqQrom256PrimEps (2 ^ 48))).lt ⟨1, 2 ^ 128, by decide⟩ := by
    unfold jortsMultiHopBudget pqMultiHopBudget
    rw [jortsProdParams_accounting.2.2.2.1, jortsProdParams_accounting.2.2.2.2.1]; decide +kernel
  exact Spec.RatBound.lt_of_le_of_lt
    (pqMultiHopBudget_mono jortsProdParams hqSign (Spec.RatBound.le_refl Spec.RatBound.zero)
      hPrim hPrim hPrim hPrim) hTopLt

/-- Bridges `PorsFpSecurity.sha3_128f_forgery_bound` and `PorsFpSecurity.sha3_128f_binomial_bits`
    (`r ≤ 3` signatures per `PORS+FP` leaf yield `≤ 2^{-136}` subset-cover fraction) to a strict
    `< 2^{-131}` rational budget across `qAttempts ≤ 16`. -/
theorem baggySha3_128f_pors_itsr_lt_2_neg_131
    (acc : List Nat → Bool) (sigs : List (List Nat)) (r qAttempts : Nat)
    (hk : ∀ s ∈ sigs, s.length = PorsFpSecurity.sha3_128f.reveal)
    (hsigs : sigs.length ≤ r) (hr1 : 1 ≤ r) (hr3 : r ≤ 3) (hqAtt : qAttempts ≤ 16) :
    let hDenPos : 0 < PorsFpSecurity.choose 2048 28 := by
      have hMul := PorsFpSecurity.choose_mul_fact 28 28
      have hC28Pos : 0 < PorsFpSecurity.choose 28 28 := by
        have hf := PorsFpSecurity.sha3_128f_ff_pos.1
        rw [← hMul] at hf; exact Nat.pos_of_mul_pos_right hf
      have h209 := PorsFpSecurity.sha3_128f_binomial_bits.1.1
      unfold PorsFpSecurity.AtLeastBits at h209
      exact Nat.lt_of_lt_of_le (Nat.mul_pos (Nat.two_pow_pos 209) hC28Pos) h209
    PorsFpSecurity.AtLeastBits (PorsFpSecurity.sha3Bits r)
      (PorsFpSecurity.coverWins PorsFpSecurity.sha3_128f acc (PorsFpSecurity.revealedBy sigs)).length
      (PorsFpSecurity.subsets PorsFpSecurity.sha3_128f).length ∧
    (Spec.RatBound.scale qAttempts
      ⟨PorsFpSecurity.choose 84 28, PorsFpSecurity.choose 2048 28, hDenPos⟩).lt
      ⟨1, 2 ^ 131, by decide⟩ := by
  intro hDenPos
  refine ⟨PorsFpSecurity.sha3_128f_forgery_bound acc sigs r hk hsigs hr1
    (Decidable.byContradiction (fun _ => by omega)), ?_⟩
  have h136 := PorsFpSecurity.sha3_128f_binomial_bits.2.2.1.1
  unfold PorsFpSecurity.AtLeastBits at h136
  unfold Spec.RatBound.lt Spec.RatBound.scale; dsimp only
  have h16 := Nat.mul_le_mul_right (2 ^ 131)
    (Nat.mul_le_mul_right (PorsFpSecurity.choose 84 28) hqAtt)
  have hFactor : 16 * PorsFpSecurity.choose 84 28 * 2 ^ 131 =
      2 ^ 135 * PorsFpSecurity.choose 84 28 := by
    have hP : 16 * 2 ^ 131 = 2 ^ 135 := by decide
    rw [Nat.mul_right_comm, hP, Nat.mul_comm]
  have hDouble : 2 * (2 ^ 135 * PorsFpSecurity.choose 84 28) ≤ PorsFpSecurity.choose 2048 28 := by
    have hP2 : 2 * 2 ^ 135 = 2 ^ 136 := by decide
    rw [← Nat.mul_assoc, hP2]; exact h136
  have hPos84 : 0 < PorsFpSecurity.choose 84 28 := by
    have hMul := PorsFpSecurity.choose_mul_fact 84 28
    have hf := PorsFpSecurity.sha3_128f_ff_pos.2.2.1
    rw [← hMul] at hf; exact Nat.pos_of_mul_pos_right hf
  have hPosPow : 0 < 2 ^ 135 * PorsFpSecurity.choose 84 28 :=
    Nat.mul_pos (Nat.two_pow_pos 135) hPos84
  exact Decidable.byContradiction (fun _ => by omega)

/-- Multi-hop EUF-CMA rational budget for `BaggySha3_128f`. -/
@[expose] def baggySha3MultiHopBudget
    (εItsr εCol εPre εPrfSec εPrfMsg : Spec.RatBound) : Spec.RatBound :=
  ((((εItsr.add εCol).add εPre).add εPrfSec).add εPrfMsg)

private theorem baggySha3_128f_multiHop_core {n : Nat} (hPos : 0 < n)
    (forgerRealGame forgerHop1Game : Spec.FinGame n)
    (suite : TweakableHashSuite) (hmsgXof : PorsFpSecurity.BaggyHmsgStream)
    (skIdeal : Fin n → PqSecretKey)
    (logOf : (ω : Fin n) →
      List (PorsFpSecurity.HonestBaggySignedEntry suite hmsgXof PorsFpSecurity.BaggySha3_128f (skIdeal ω)))
    (forgerOut : Fin n → List UInt8 × PorsFpSecurity.BaggySig)
    (itsrEvent colEvent preEvent : Fin n → Bool)
    {εItsr εCol εPre εPrfSec εPrfMsg : Spec.RatBound}
    (hHop1 : Spec.GameBound (Spec.AdvDist forgerRealGame forgerHop1Game) εPrfMsg)
    (hHop2 : Spec.GameBound (Spec.AdvDist forgerHop1Game
      ⟨hPos, fun ω =>
        PorsFpSecurity.baggyVerify suite hmsgXof PorsFpSecurity.BaggySha3_128f
          (PorsFpSecurity.baggyDerivePublicKey suite PorsFpSecurity.BaggySha3_128f (skIdeal ω))
          (forgerOut ω).1 (forgerOut ω).2 &&
        decide ((forgerOut ω).1 ∉ (logOf ω).map PorsFpSecurity.HonestBaggySignedEntry.msg)⟩) εPrfSec)
    (hItsr : ∀ ω (rStar muStar : List UInt8) (ctrStar leafIdx : Nat) (idxsStar : List Nat),
      PorsFpSecurity.baggySelectAt hmsgXof PorsFpSecurity.BaggySha3_128f
        (PorsFpSecurity.baggyDerivePublicKey suite PorsFpSecurity.BaggySha3_128f (skIdeal ω))
        rStar muStar ctrStar = some (idxsStar, leafIdx) →
      (∀ u ∈ idxsStar, ∃ e ∈ logOf ω,
        PorsFpSecurity.BaggySha3_128f.pathAt e.leafIdx 0 =
          PorsFpSecurity.BaggySha3_128f.pathAt leafIdx 0 ∧ u ∈ e.idxs) →
      itsrEvent ω = true)
    (hCol : ∀ ω, Nonempty (HashCollisionWitness suite.rawHash) → colEvent ω = true)
    (hPre : ∀ ω,
      (∃ tree0 kp0 u cand,
        (∀ e ∈ logOf ω, PorsFpSecurity.BaggySha3_128f.pathAt e.leafIdx 0 = (kp0, tree0) → u ∉ e.idxs) ∧
        thChainF suite (skIdeal ω).pkSeed
          (PorsFpSecurity.porsLeafAdrs tree0 kp0 (UInt32.ofNat u)) cand =
          (PorsFpSecurity.porsTweakableSuite suite (skIdeal ω).pkSeed tree0 kp0).leaf u
            (PorsFpSecurity.porsSecretLeaf suite (skIdeal ω) tree0 kp0 u)) ∨
      Nonempty (WotsBackwardInversionWitness suite (skIdeal ω).pkSeed) →
      preEvent ω = true)
    (hBItsr : Spec.GameBound (Spec.FinGame.mk hPos itsrEvent).winProb εItsr)
    (hBCol : Spec.GameBound (Spec.FinGame.mk hPos colEvent).winProb εCol)
    (hBPre : Spec.GameBound (Spec.FinGame.mk hPos preEvent).winProb εPre) :
    Spec.GameBound forgerRealGame.winProb (baggySha3MultiHopBudget εItsr εCol εPre εPrfSec εPrfMsg) := by
  have hIdeal := PorsFpSecurity.baggy_sha3_128f_euf_cma_gameBound hPos suite hmsgXof skIdeal
    logOf forgerOut itsrEvent colEvent preEvent hItsr hCol hPre hBItsr hBCol hBPre
  have hStep2 := Spec.RatBound.le_trans (winProb_le_add_advDist forgerHop1Game _)
    (Spec.RatBound.add_le_add hIdeal hHop2)
  exact Spec.RatBound.le_trans (winProb_le_add_advDist forgerRealGame forgerHop1Game)
    (Spec.RatBound.add_le_add hStep2 hHop1)

/-- **`BaggySha3_128f` Classical (`qEval ≤ 2^96`) Multi-Hop EUF-CMA `< 2^{-128}` Bound.** -/
theorem baggySha3_128f_classical_euf_cma_lt_2_neg_128 {n qEval : Nat} (hPos : 0 < n)
    (hqEval : qEval ≤ 2 ^ 96) (forgerRealGame forgerHop1Game : Spec.FinGame n)
    (suite : TweakableHashSuite) (hmsgXof : PorsFpSecurity.BaggyHmsgStream)
    (skIdeal : Fin n → PqSecretKey)
    (logOf : (ω : Fin n) →
      List (PorsFpSecurity.HonestBaggySignedEntry suite hmsgXof PorsFpSecurity.BaggySha3_128f (skIdeal ω)))
    (forgerOut : Fin n → List UInt8 × PorsFpSecurity.BaggySig)
    (itsrEvent colEvent preEvent : Fin n → Bool)
    {εItsr εCol εPre εPrfSec εPrfMsg : Spec.RatBound}
    (hHop1 : Spec.GameBound (Spec.AdvDist forgerRealGame forgerHop1Game) εPrfMsg)
    (hHop2 : Spec.GameBound (Spec.AdvDist forgerHop1Game
      ⟨hPos, fun ω =>
        PorsFpSecurity.baggyVerify suite hmsgXof PorsFpSecurity.BaggySha3_128f
          (PorsFpSecurity.baggyDerivePublicKey suite PorsFpSecurity.BaggySha3_128f (skIdeal ω))
          (forgerOut ω).1 (forgerOut ω).2 &&
        decide ((forgerOut ω).1 ∉ (logOf ω).map PorsFpSecurity.HonestBaggySignedEntry.msg)⟩) εPrfSec)
    (hItsr : ∀ ω (rStar muStar : List UInt8) (ctrStar leafIdx : Nat) (idxsStar : List Nat),
      PorsFpSecurity.baggySelectAt hmsgXof PorsFpSecurity.BaggySha3_128f
        (PorsFpSecurity.baggyDerivePublicKey suite PorsFpSecurity.BaggySha3_128f (skIdeal ω))
        rStar muStar ctrStar = some (idxsStar, leafIdx) →
      (∀ u ∈ idxsStar, ∃ e ∈ logOf ω,
        PorsFpSecurity.BaggySha3_128f.pathAt e.leafIdx 0 =
          PorsFpSecurity.BaggySha3_128f.pathAt leafIdx 0 ∧ u ∈ e.idxs) →
      itsrEvent ω = true)
    (hCol : ∀ ω, Nonempty (HashCollisionWitness suite.rawHash) → colEvent ω = true)
    (hPre : ∀ ω,
      (∃ tree0 kp0 u cand,
        (∀ e ∈ logOf ω, PorsFpSecurity.BaggySha3_128f.pathAt e.leafIdx 0 = (kp0, tree0) → u ∉ e.idxs) ∧
        thChainF suite (skIdeal ω).pkSeed
          (PorsFpSecurity.porsLeafAdrs tree0 kp0 (UInt32.ofNat u)) cand =
          (PorsFpSecurity.porsTweakableSuite suite (skIdeal ω).pkSeed tree0 kp0).leaf u
            (PorsFpSecurity.porsSecretLeaf suite (skIdeal ω) tree0 kp0 u)) ∨
      Nonempty (WotsBackwardInversionWitness suite (skIdeal ω).pkSeed) →
      preEvent ω = true)
    (hBItsr : Spec.GameBound (Spec.FinGame.mk hPos itsrEvent).winProb εItsr)
    (hBCol : Spec.GameBound (Spec.FinGame.mk hPos colEvent).winProb εCol)
    (hBPre : Spec.GameBound (Spec.FinGame.mk hPos preEvent).winProb εPre)
    (hEpsItsr : εItsr.le ⟨1, 2 ^ 131, by decide⟩)
    (hEpsCol : εCol.le (Spec.RatBound.scale (2 ^ 21) (classical256PrimEps qEval)))
    (hEpsPre : εPre.le (Spec.RatBound.scale 8192 (classical256PrimEps qEval)))
    (hEpsSec : εPrfSec.le (classical256PrimEps qEval))
    (hEpsMsg : εPrfMsg.le (classical256PrimEps qEval)) :
    (baggySha3MultiHopBudget εItsr εCol εPre εPrfSec εPrfMsg).lt ⟨1, 2 ^ 128, by decide⟩ ∧
    Spec.GameBound forgerRealGame.winProb ⟨1, 2 ^ 128, by decide⟩ := by
  have hTotal := baggySha3_128f_multiHop_core hPos forgerRealGame forgerHop1Game suite hmsgXof
    skIdeal logOf forgerOut itsrEvent colEvent preEvent hHop1 hHop2 hItsr hCol hPre hBItsr hBCol hBPre
  have hPrim := classical256PrimEps_mono hqEval
  have hMono : (baggySha3MultiHopBudget εItsr εCol εPre εPrfSec εPrfMsg).le
      (baggySha3MultiHopBudget ⟨1, 2 ^ 131, by decide⟩
        (Spec.RatBound.scale (2 ^ 21) (classical256PrimEps (2 ^ 96)))
        (Spec.RatBound.scale 8192 (classical256PrimEps (2 ^ 96)))
        (classical256PrimEps (2 ^ 96)) (classical256PrimEps (2 ^ 96))) :=
    Spec.RatBound.add_le_add
      (Spec.RatBound.add_le_add
        (Spec.RatBound.add_le_add
          (Spec.RatBound.add_le_add hEpsItsr
            (Spec.RatBound.le_trans hEpsCol (Spec.RatBound.scale_le_scale _ hPrim)))
          (Spec.RatBound.le_trans hEpsPre (Spec.RatBound.scale_le_scale _ hPrim)))
        (Spec.RatBound.le_trans hEpsSec hPrim))
      (Spec.RatBound.le_trans hEpsMsg hPrim)
  have hLt : (baggySha3MultiHopBudget εItsr εCol εPre εPrfSec εPrfMsg).lt ⟨1, 2 ^ 128, by decide⟩ :=
    Spec.RatBound.lt_of_le_of_lt hMono (by decide +kernel)
  exact ⟨hLt, Spec.RatBound.le_trans hTotal (Spec.RatBound.le_of_lt hLt)⟩

/-- **`BaggySha3_128f` Post-Quantum `QROM` (Grover `qEval ≤ 2^48`) Multi-Hop EUF-CMA `< 2^{-128}` Bound.** -/
theorem baggySha3_128f_pq_qrom_euf_cma_lt_2_neg_128 {n qEval : Nat} (hPos : 0 < n)
    (hqEval : qEval ≤ 2 ^ 48) (forgerRealGame forgerHop1Game : Spec.FinGame n)
    (suite : TweakableHashSuite) (hmsgXof : PorsFpSecurity.BaggyHmsgStream)
    (skIdeal : Fin n → PqSecretKey)
    (logOf : (ω : Fin n) →
      List (PorsFpSecurity.HonestBaggySignedEntry suite hmsgXof PorsFpSecurity.BaggySha3_128f (skIdeal ω)))
    (forgerOut : Fin n → List UInt8 × PorsFpSecurity.BaggySig)
    (itsrEvent colEvent preEvent : Fin n → Bool)
    {εItsr εCol εPre εPrfSec εPrfMsg : Spec.RatBound}
    (hHop1 : Spec.GameBound (Spec.AdvDist forgerRealGame forgerHop1Game) εPrfMsg)
    (hHop2 : Spec.GameBound (Spec.AdvDist forgerHop1Game
      ⟨hPos, fun ω =>
        PorsFpSecurity.baggyVerify suite hmsgXof PorsFpSecurity.BaggySha3_128f
          (PorsFpSecurity.baggyDerivePublicKey suite PorsFpSecurity.BaggySha3_128f (skIdeal ω))
          (forgerOut ω).1 (forgerOut ω).2 &&
        decide ((forgerOut ω).1 ∉ (logOf ω).map PorsFpSecurity.HonestBaggySignedEntry.msg)⟩) εPrfSec)
    (hItsr : ∀ ω (rStar muStar : List UInt8) (ctrStar leafIdx : Nat) (idxsStar : List Nat),
      PorsFpSecurity.baggySelectAt hmsgXof PorsFpSecurity.BaggySha3_128f
        (PorsFpSecurity.baggyDerivePublicKey suite PorsFpSecurity.BaggySha3_128f (skIdeal ω))
        rStar muStar ctrStar = some (idxsStar, leafIdx) →
      (∀ u ∈ idxsStar, ∃ e ∈ logOf ω,
        PorsFpSecurity.BaggySha3_128f.pathAt e.leafIdx 0 =
          PorsFpSecurity.BaggySha3_128f.pathAt leafIdx 0 ∧ u ∈ e.idxs) →
      itsrEvent ω = true)
    (hCol : ∀ ω, Nonempty (HashCollisionWitness suite.rawHash) → colEvent ω = true)
    (hPre : ∀ ω,
      (∃ tree0 kp0 u cand,
        (∀ e ∈ logOf ω, PorsFpSecurity.BaggySha3_128f.pathAt e.leafIdx 0 = (kp0, tree0) → u ∉ e.idxs) ∧
        thChainF suite (skIdeal ω).pkSeed
          (PorsFpSecurity.porsLeafAdrs tree0 kp0 (UInt32.ofNat u)) cand =
          (PorsFpSecurity.porsTweakableSuite suite (skIdeal ω).pkSeed tree0 kp0).leaf u
            (PorsFpSecurity.porsSecretLeaf suite (skIdeal ω) tree0 kp0 u)) ∨
      Nonempty (WotsBackwardInversionWitness suite (skIdeal ω).pkSeed) →
      preEvent ω = true)
    (hBItsr : Spec.GameBound (Spec.FinGame.mk hPos itsrEvent).winProb εItsr)
    (hBCol : Spec.GameBound (Spec.FinGame.mk hPos colEvent).winProb εCol)
    (hBPre : Spec.GameBound (Spec.FinGame.mk hPos preEvent).winProb εPre)
    (hEpsItsr : εItsr.le ⟨1, 2 ^ 131, by decide⟩)
    (hEpsCol : εCol.le (Spec.RatBound.scale (2 ^ 21) (pqQrom256PrimEps qEval)))
    (hEpsPre : εPre.le (Spec.RatBound.scale 8192 (pqQrom256PrimEps qEval)))
    (hEpsSec : εPrfSec.le (pqQrom256PrimEps qEval))
    (hEpsMsg : εPrfMsg.le (pqQrom256PrimEps qEval)) :
    (baggySha3MultiHopBudget εItsr εCol εPre εPrfSec εPrfMsg).lt ⟨1, 2 ^ 128, by decide⟩ ∧
    Spec.GameBound forgerRealGame.winProb ⟨1, 2 ^ 128, by decide⟩ := by
  have hTotal := baggySha3_128f_multiHop_core hPos forgerRealGame forgerHop1Game suite hmsgXof
    skIdeal logOf forgerOut itsrEvent colEvent preEvent hHop1 hHop2 hItsr hCol hPre hBItsr hBCol hBPre
  have hPrim := pqQrom256PrimEps_mono hqEval
  have hMono : (baggySha3MultiHopBudget εItsr εCol εPre εPrfSec εPrfMsg).le
      (baggySha3MultiHopBudget ⟨1, 2 ^ 131, by decide⟩
        (Spec.RatBound.scale (2 ^ 21) (pqQrom256PrimEps (2 ^ 48)))
        (Spec.RatBound.scale 8192 (pqQrom256PrimEps (2 ^ 48)))
        (pqQrom256PrimEps (2 ^ 48)) (pqQrom256PrimEps (2 ^ 48))) :=
    Spec.RatBound.add_le_add
      (Spec.RatBound.add_le_add
        (Spec.RatBound.add_le_add
          (Spec.RatBound.add_le_add hEpsItsr
            (Spec.RatBound.le_trans hEpsCol (Spec.RatBound.scale_le_scale _ hPrim)))
          (Spec.RatBound.le_trans hEpsPre (Spec.RatBound.scale_le_scale _ hPrim)))
        (Spec.RatBound.le_trans hEpsSec hPrim))
      (Spec.RatBound.le_trans hEpsMsg hPrim)
  have hLt : (baggySha3MultiHopBudget εItsr εCol εPre εPrfSec εPrfMsg).lt ⟨1, 2 ^ 128, by decide⟩ :=
    Spec.RatBound.lt_of_le_of_lt hMono (by decide +kernel)
  exact ⟨hLt, Spec.RatBound.le_trans hTotal (Spec.RatBound.le_of_lt hLt)⟩

/-- **`corduroyProdParams` Concrete Multi-Hop EUF-CMA Bound & PQ QROM `< 2^{-128}` Regime.** -/
theorem corduroyProd_concrete_euf_cma_bound {n nC1 nRest nC2 nA qHash qSign qEval : Nat}
    (hPos : 0 < n) (suite : TweakableHashSuite) (hqSign : qSign ≤ 2 ^ 12) (hqEval : qEval ≤ 2 ^ 48)
    (seedLen keyLen qPrfMsg qPrfSec : Nat) (hSeedPos : 0 < seedLen) (hqPrfMsg : qSign ≤ qPrfMsg)
    (hqPrfSec : prfSecQueryBudget corduroyProdParams qSign ≤ qPrfSec)
    (π1 : Spec.CoinSplit n nC1 nRest) (π2 : Spec.CoinSplit nRest nC2 nA)
    (sampleMsg : Fin nC1 → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (hSampleMsg : Spec.UniformOn (Spec.PrfSampleOk keyLen 65 32) sampleMsg)
    (sampleSec : Fin nC2 → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (hSampleSec : Spec.UniformOn (Spec.PrfSampleOk keyLen (seedLen + 32) 32) sampleSec)
    (pkSeedA : Fin nA → List UInt8) (hSeedLen : ∀ a, (pkSeedA a).length = seedLen)
    (adv : Fin nA → SeedWithheldEufCmaAdv qHash qSign)
    {𝒜Msg 𝒜Sec : Spec.Code Spec.byteOracleIface Bool → Prop}
    (hClassMsg : ∀ r : Fin nRest, 𝒜Msg (prfMsgHopDistinguisher true suite corduroyProdParams
      (pkSeedA (π2.advc r)) (sampleSec (π2.chal r)).1 (adv (π2.advc r))))
    (hClassSec : ∀ b : Fin (nC1 * nA),
      let sp := Spec.CoinSplit.prod nC1 nA
      𝒜Sec (prfSecHopDistinguisher true suite corduroyProdParams (pkSeedA (sp.advc b))
        (sampleMsg (sp.chal b)).2 (adv (sp.advc b))))
    {εPrfMsg εPrfSec εItsr εTcr εPre : Spec.RatBound}
    (hPrfMsg : Spec.PrfHard 𝒜Msg (suitePrfMsg65 suite) keyLen 65 32 qPrfMsg εPrfMsg)
    (hPrfSec : Spec.PrfHard 𝒜Sec (suitePrfSec seedLen suite) keyLen (seedLen + 32) 32 qPrfSec εPrfSec)
    (hItsrB : Spec.GameBound
      (idealSlotItsrGame hPos suite corduroyProdParams
        (.inl (by rw [corduroyProdParams, corduroyCustody128Params_eq]))
        π1 π2 sampleMsg sampleSec pkSeedA adv).winProb εItsr)
    (hTcrB : ∀ slot : Fin (prodPathTargetCount corduroyProdParams qSign), Spec.GameBound
      (idealSlotTcrGame hPos suite corduroyProdParams
        (.inl (by rw [corduroyProdParams, corduroyCustody128Params_eq]))
        π1 π2 sampleMsg sampleSec pkSeedA adv slot.val).winProb εTcr)
    (hPreB : ∀ slot : Fin (prodPreCandidateBudget corduroyProdParams), Spec.GameBound
      (idealSlotPreGame hPos suite corduroyProdParams π1 π2 sampleMsg sampleSec pkSeedA adv slot.val).winProb εPre)
    (hEpsItsr : εItsr.le ⟨1, 2 ^ 131, by decide⟩) (hEpsTcr : εTcr.le (pqQrom256PrimEps qEval))
    (hEpsPre : εPre.le (pqQrom256PrimEps qEval)) (hEpsSec : εPrfSec.le (pqQrom256PrimEps qEval))
    (hEpsMsg : εPrfMsg.le (pqQrom256PrimEps qEval)) :
    prodPathTargetCount corduroyProdParams qSign ≤ 35690 ∧
    (pqMultiHopBudget corduroyProdParams qSign εItsr εTcr εPre εPrfSec εPrfMsg).lt ⟨1, 2 ^ 128, by decide⟩ ∧
    Spec.GameBound (ExecEufCmaGame hPos suite corduroyProdParams
      (multiHopKeygen π1 π2 sampleMsg sampleSec pkSeedA) (multiHopAdv π1 π2 adv)).winProb
      ⟨1, 2 ^ 128, by decide⟩ := by
  have hwC : corduroyProdParams.w = 4 ∨ corduroyProdParams.w = 16 :=
    .inl (by rw [corduroyProdParams, corduroyCustody128Params_eq])
  have hGame := hulsing_multiHop_idealSlot_euf_cma_bound hPos suite corduroyProdParams hwC
    seedLen keyLen qPrfMsg qPrfSec hSeedPos hqPrfMsg hqPrfSec π1 π2 sampleMsg hSampleMsg
    sampleSec hSampleSec pkSeedA hSeedLen adv hClassMsg hClassSec hPrfMsg hPrfSec hItsrB hTcrB hPreB
  have hPrim := pqQrom256PrimEps_mono hqEval
  have hMono := pqMultiHopBudget_mono corduroyProdParams hqSign hEpsItsr
    (Spec.RatBound.le_trans hEpsTcr hPrim) (Spec.RatBound.le_trans hEpsPre hPrim)
    (Spec.RatBound.le_trans hEpsSec hPrim) (Spec.RatBound.le_trans hEpsMsg hPrim)
  have hTopLt : (pqMultiHopBudget corduroyProdParams (2 ^ 12) ⟨1, 2 ^ 131, by decide⟩
      (pqQrom256PrimEps (2 ^ 48)) (pqQrom256PrimEps (2 ^ 48))
      (pqQrom256PrimEps (2 ^ 48)) (pqQrom256PrimEps (2 ^ 48))).lt ⟨1, 2 ^ 128, by decide⟩ := by
    unfold pqMultiHopBudget
    rw [corduroyProdParams_accounting.2.2.2.1, corduroyProdParams_accounting.2.2.2.2.1]; decide +kernel
  have hLt := Spec.RatBound.lt_of_le_of_lt hMono hTopLt
  have hCntLe : prodPathTargetCount corduroyProdParams qSign ≤ 35690 := by
    rw [← corduroyProdParams_accounting.2.2.2.1]; exact prodPathTargetCount_mono corduroyProdParams hqSign
  exact ⟨hCntLe, hLt, Spec.RatBound.le_trans hGame (Spec.RatBound.le_of_lt hLt)⟩

/-- **`baggyProdParams` Concrete Multi-Hop EUF-CMA Bound & PQ QROM `< 2^{-128}` Regime.** -/
theorem baggyProd_concrete_euf_cma_bound {n nC1 nRest nC2 nA qHash qSign qEval : Nat}
    (hPos : 0 < n) (suite : TweakableHashSuite) (hqSign : qSign ≤ 2 ^ 16) (hqEval : qEval ≤ 2 ^ 48)
    (seedLen keyLen qPrfMsg qPrfSec : Nat) (hSeedPos : 0 < seedLen) (hqPrfMsg : qSign ≤ qPrfMsg)
    (hqPrfSec : prfSecQueryBudget baggyProdParams qSign ≤ qPrfSec)
    (π1 : Spec.CoinSplit n nC1 nRest) (π2 : Spec.CoinSplit nRest nC2 nA)
    (sampleMsg : Fin nC1 → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (hSampleMsg : Spec.UniformOn (Spec.PrfSampleOk keyLen 65 32) sampleMsg)
    (sampleSec : Fin nC2 → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (hSampleSec : Spec.UniformOn (Spec.PrfSampleOk keyLen (seedLen + 32) 32) sampleSec)
    (pkSeedA : Fin nA → List UInt8) (hSeedLen : ∀ a, (pkSeedA a).length = seedLen)
    (adv : Fin nA → SeedWithheldEufCmaAdv qHash qSign)
    {𝒜Msg 𝒜Sec : Spec.Code Spec.byteOracleIface Bool → Prop}
    (hClassMsg : ∀ r : Fin nRest, 𝒜Msg (prfMsgHopDistinguisher true suite baggyProdParams
      (pkSeedA (π2.advc r)) (sampleSec (π2.chal r)).1 (adv (π2.advc r))))
    (hClassSec : ∀ b : Fin (nC1 * nA),
      let sp := Spec.CoinSplit.prod nC1 nA
      𝒜Sec (prfSecHopDistinguisher true suite baggyProdParams (pkSeedA (sp.advc b))
        (sampleMsg (sp.chal b)).2 (adv (sp.advc b))))
    {εPrfMsg εPrfSec εItsr εTcr εPre : Spec.RatBound}
    (hPrfMsg : Spec.PrfHard 𝒜Msg (suitePrfMsg65 suite) keyLen 65 32 qPrfMsg εPrfMsg)
    (hPrfSec : Spec.PrfHard 𝒜Sec (suitePrfSec seedLen suite) keyLen (seedLen + 32) 32 qPrfSec εPrfSec)
    (hItsrB : Spec.GameBound
      (idealSlotItsrGame hPos suite baggyProdParams
        (.inl (by rw [baggyProdParams, baggy128fParams_eq]))
        π1 π2 sampleMsg sampleSec pkSeedA adv).winProb εItsr)
    (hTcrB : ∀ slot : Fin (prodPathTargetCount baggyProdParams qSign), Spec.GameBound
      (idealSlotTcrGame hPos suite baggyProdParams
        (.inl (by rw [baggyProdParams, baggy128fParams_eq]))
        π1 π2 sampleMsg sampleSec pkSeedA adv slot.val).winProb εTcr)
    (hPreB : ∀ slot : Fin (prodPreCandidateBudget baggyProdParams), Spec.GameBound
      (idealSlotPreGame hPos suite baggyProdParams π1 π2 sampleMsg sampleSec pkSeedA adv slot.val).winProb εPre)
    (hEpsItsr : εItsr.le ⟨1, 2 ^ 131, by decide⟩) (hEpsTcr : εTcr.le (pqQrom256PrimEps qEval))
    (hEpsPre : εPre.le (pqQrom256PrimEps qEval)) (hEpsSec : εPrfSec.le (pqQrom256PrimEps qEval))
    (hEpsMsg : εPrfMsg.le (pqQrom256PrimEps qEval)) :
    prodPathTargetCount baggyProdParams qSign ≤ 1120503 ∧
    (pqMultiHopBudget baggyProdParams qSign εItsr εTcr εPre εPrfSec εPrfMsg).lt ⟨1, 2 ^ 128, by decide⟩ ∧
    Spec.GameBound (ExecEufCmaGame hPos suite baggyProdParams
      (multiHopKeygen π1 π2 sampleMsg sampleSec pkSeedA) (multiHopAdv π1 π2 adv)).winProb
      ⟨1, 2 ^ 128, by decide⟩ := by
  have hwB : baggyProdParams.w = 4 ∨ baggyProdParams.w = 16 :=
    .inl (by rw [baggyProdParams, baggy128fParams_eq])
  have hGame := hulsing_multiHop_idealSlot_euf_cma_bound hPos suite baggyProdParams hwB
    seedLen keyLen qPrfMsg qPrfSec hSeedPos hqPrfMsg hqPrfSec π1 π2 sampleMsg hSampleMsg
    sampleSec hSampleSec pkSeedA hSeedLen adv hClassMsg hClassSec hPrfMsg hPrfSec hItsrB hTcrB hPreB
  have hPrim := pqQrom256PrimEps_mono hqEval
  have hMono := pqMultiHopBudget_mono baggyProdParams hqSign hEpsItsr
    (Spec.RatBound.le_trans hEpsTcr hPrim) (Spec.RatBound.le_trans hEpsPre hPrim)
    (Spec.RatBound.le_trans hEpsSec hPrim) (Spec.RatBound.le_trans hEpsMsg hPrim)
  have hTopLt : (pqMultiHopBudget baggyProdParams (2 ^ 16) ⟨1, 2 ^ 131, by decide⟩
      (pqQrom256PrimEps (2 ^ 48)) (pqQrom256PrimEps (2 ^ 48))
      (pqQrom256PrimEps (2 ^ 48)) (pqQrom256PrimEps (2 ^ 48))).lt ⟨1, 2 ^ 128, by decide⟩ := by
    unfold pqMultiHopBudget
    rw [baggyProdParams_accounting.2.2.2.1, baggyProdParams_accounting.2.2.2.2.1]; decide +kernel
  have hLt := Spec.RatBound.lt_of_le_of_lt hMono hTopLt
  have hCntLe : prodPathTargetCount baggyProdParams qSign ≤ 1120503 := by
    rw [← baggyProdParams_accounting.2.2.2.1]; exact prodPathTargetCount_mono baggyProdParams hqSign
  exact ⟨hCntLe, hLt, Spec.RatBound.le_trans hGame (Spec.RatBound.le_of_lt hLt)⟩

/-! ## §2. NIST FIPS 205 `SLH-DSA-SHAKE-128s` & `128f` Exact Interleaved `ITSR` & `< 2^{-128}` Bounds -/

/-- Self-contained Pascal binomial coefficient `C(n, k)` for truncated-binomial accounting. -/
def binomChoose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binomChoose n k + binomChoose n (k + 1)

/-- Exposed `O(k)` factorial evaluator for kernel `decide` reduction. -/
@[expose] def factFast : Nat → Nat
  | 0 => 1
  | k + 1 => (k + 1) * factFast k

/-- Exposed `O(k)` GMP-friendly falling-factorial evaluator `n * (n - 1) * ... * (n - k + 1)`
    recursing solely on `k` (never unpacking `n + 1` on `n = 2^64`). -/
@[expose] def fallingFactFast (n : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => (n - k) * fallingFactFast n k

theorem factFast_pos : ∀ k : Nat, 0 < factFast k
  | 0 => Nat.one_pos
  | k + 1 => Nat.mul_pos (Nat.succ_pos k) (factFast_pos k)

private theorem fallingFactFast_zero_left : ∀ k : Nat, fallingFactFast 0 (k + 1) = 0
  | 0 => rfl
  | _ + 1 => by unfold fallingFactFast; rw [Nat.zero_sub, Nat.zero_mul]

private theorem fallingFactFast_succ_left :
    ∀ (k n : Nat), fallingFactFast (n + 1) (k + 1) = (n + 1) * fallingFactFast n k
  | 0, n => by unfold fallingFactFast; unfold fallingFactFast; rw [Nat.sub_zero]
  | k + 1, n => by
    conv => lhs; unfold fallingFactFast
    rw [Nat.succ_sub_succ, fallingFactFast_succ_left k n, Nat.mul_left_comm]
    rfl

theorem binomChoose_mul_factFast :
    ∀ (k n : Nat), binomChoose n k * factFast k = fallingFactFast n k
  | 0, n => by cases n <;> rfl
  | k + 1, 0 => by rw [binomChoose, Nat.zero_mul, fallingFactFast_zero_left]
  | k + 1, n + 1 => by
    rw [fallingFactFast_succ_left k n]
    have ih1 := binomChoose_mul_factFast (k + 1) n
    have ih2 := binomChoose_mul_factFast k n
    have hStep : binomChoose (n + 1) (k + 1) * factFast (k + 1) =
        binomChoose n k * ((k + 1) * factFast k) + binomChoose n (k + 1) * factFast (k + 1) := by
      conv => lhs; rw [binomChoose]
      rw [Nat.add_mul]
      rfl
    have hRec : (n + 1) * fallingFactFast n k =
        (k + 1) * fallingFactFast n k + (n - k) * fallingFactFast n k := by
      if hle : k ≤ n then
        have hEq : k + 1 + (n - k) = n + 1 := Decidable.byContradiction (fun _ => by omega)
        rw [← Nat.add_mul, hEq]
      else
        have hZero : fallingFactFast n k = 0 := by
          clear ih1 ih2 hStep
          induction k generalizing n with
          | zero => exact absurd (Nat.zero_le n) hle
          | succ k' ihK =>
            unfold fallingFactFast
            if hk' : k' ≤ n then
              have hEqN : n = k' := Decidable.byContradiction (fun _ => by omega)
              subst hEqN; rw [Nat.sub_self, Nat.zero_mul]
            else
              rw [ihK n hk', Nat.mul_zero]
        rw [hZero, Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]
    have hComm : binomChoose n k * ((k + 1) * factFast k) =
        (k + 1) * fallingFactFast n k := by
      rw [← Nat.mul_assoc, Nat.mul_comm (binomChoose n k) (k + 1), Nat.mul_assoc, ih2]
    have hSubStep : binomChoose n (k + 1) * factFast (k + 1) =
        (n - k) * fallingFactFast n k := ih1
    rw [hStep, hRec, hComm, hSubStep]

/-- Fast `O(J)` falling-factorial evaluator of `∑_{j=0}^J C(m, j) * L^(J - j)`. -/
@[expose] def truncBinomFast (L m : Nat) : Nat → Nat
  | 0 => 1
  | J + 1 =>
    L ^ (J + 1) + ((List.range (J + 1)).map fun j =>
      (fallingFactFast m (j + 1) / factFast (j + 1)) * L ^ (J - j)).sum

theorem truncBinomFast_pos (L m : Nat) (hL : 0 < L) : ∀ J : Nat, 0 < truncBinomFast L m J
  | 0 => Nat.one_pos
  | _ + 1 => Nat.lt_of_lt_of_le (Nat.pow_pos hL) (Nat.le_add_right _ _)

theorem truncBinomFast_eq_spec (L m J : Nat) :
    truncBinomFast L m J =
      ((List.range (J + 1)).map fun j => binomChoose m j * L ^ (J - j)).sum := by
  have hDiv : ∀ k, fallingFactFast m k / factFast k = binomChoose m k := by
    intro k
    rw [← binomChoose_mul_factFast k m, Nat.mul_div_cancel _ (factFast_pos k)]
  have hZ : ∀ n, binomChoose n 0 = 1 := fun n => by cases n <;> rfl
  cases J with
  | zero =>
    unfold truncBinomFast
    simp only [List.range_succ, List.range_zero, List.nil_append, List.map_singleton,
      List.sum_singleton, hZ, Nat.sub_self, Nat.pow_zero, Nat.mul_one]
  | succ J' =>
    unfold truncBinomFast; rw [prod_list_range_succ_shift (J' + 1)]
    simp only [List.sum_cons, hZ, Nat.sub_zero, Nat.one_mul]
    congr 1; congr 1; apply List.map_congr_left; intro j _
    rw [hDiv (j + 1), Nat.succ_sub_succ]

private theorem truncBinom_step (L m J : Nat) :
    ((List.range (J + 2)).map fun j => binomChoose (m + 1) j * L ^ (J + 1 - j)).sum =
      ((List.range (J + 2)).map fun j => binomChoose m j * L ^ (J + 1 - j)).sum +
      ((List.range (J + 1)).map fun j => binomChoose m j * L ^ (J - j)).sum := by
  have hZ : ∀ n, binomChoose n 0 = 1 := fun n => by cases n <;> rfl
  rw [prod_list_range_succ_shift (J + 1), prod_list_range_succ_shift (J + 1)]
  simp only [List.sum_cons, hZ, Nat.sub_zero, Nat.one_mul]
  have hSplit : ∀ xs : List Nat,
      (xs.map fun j => (binomChoose m j + binomChoose m (j + 1)) * L ^ (J - j)).sum =
      (xs.map fun j => binomChoose m (j + 1) * L ^ (J - j)).sum +
      (xs.map fun j => binomChoose m j * L ^ (J - j)).sum := by
    intro xs; induction xs with
    | nil => rfl
    | cons hd tl ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [Nat.add_mul, ih]
      exact Decidable.byContradiction (fun _ => by omega)
  have hLhsEq : ((List.range (J + 1)).map fun k =>
      binomChoose (m + 1) (k + 1) * L ^ (J + 1 - (k + 1))) =
      ((List.range (J + 1)).map fun k =>
        (binomChoose m k + binomChoose m (k + 1)) * L ^ (J - k)) := by
    apply List.map_congr_left; intro k _; rw [binomChoose, Nat.succ_sub_succ]
  have hRhsEq : ((List.range (J + 1)).map fun k =>
      binomChoose m (k + 1) * L ^ (J + 1 - (k + 1))) =
      ((List.range (J + 1)).map fun k => binomChoose m (k + 1) * L ^ (J - k)) := by
    apply List.map_congr_left; intro k _; rw [Nat.succ_sub_succ]
  rw [hLhsEq, hRhsEq, hSplit]
  exact Decidable.byContradiction (fun _ => by omega)

/-- **Constructive Truncated-Binomial Decay Bound (`one_sub_pow_mul_truncBinom_le`).**
    Proves `(L - 1)^m * truncBinomFast L m J ≤ L^(m + J)` in pure `Nat` arithmetic. -/
theorem one_sub_pow_mul_truncBinom_le (L m J : Nat) (hL : 1 ≤ L) :
    (L - 1) ^ m * truncBinomFast L m J ≤ L ^ (m + J) := by
  have hZ : ∀ n, binomChoose n 0 = 1 := fun n => by cases n <;> rfl
  have hZeroSum : ∀ (n : Nat) (f : Nat → Nat), (∀ k, f k = 0) → ((List.range n).map f).sum = 0 := by
    intro n f hf; induction n with
    | zero => rfl
    | succ n' ih =>
      rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton,
        List.sum_singleton, ih, hf n', Nat.add_zero]
  have hLower : ∀ (m' J' : Nat),
      L ^ m' * ((List.range (J' + 1)).map fun j =>
        binomChoose m' j * L ^ (J' - j)).sum ≤ (L + 1) ^ m' * L ^ J' := by
    intro m'; induction m' with
    | zero =>
      intro J'; rw [prod_list_range_succ_shift J']
      have hRest0 := hZeroSum J' (fun k => binomChoose 0 (k + 1) * L ^ (J' - (k + 1)))
        (fun k => by rw [binomChoose, Nat.zero_mul])
      simp only [List.sum_cons, hRest0, hZ, Nat.sub_zero,
        Nat.one_mul, Nat.add_zero, Nat.pow_zero]; exact Nat.le_refl _
    | succ m' ih =>
      intro J'; cases J' with
      | zero =>
        simp only [List.range_succ, List.range_zero, List.nil_append, List.map_singleton,
          List.sum_singleton, hZ, Nat.sub_self, Nat.pow_zero, Nat.mul_one]
        exact Nat.pow_le_pow_left (Nat.le_succ L) (m' + 1)
      | succ J'' =>
        rw [truncBinom_step, Nat.mul_add, Nat.pow_succ L m', Nat.mul_comm (L ^ m') L,
          Nat.mul_assoc L (L ^ m'), Nat.mul_assoc L (L ^ m')]
        have h1 := Nat.mul_le_mul_left L (ih (J'' + 1))
        have h2 : L * (L ^ m' * ((List.range (J'' + 1)).map fun j =>
            binomChoose m' j * L ^ (J'' - j)).sum) ≤
            1 * ((L + 1) ^ m' * L ^ (J'' + 1)) := by
          calc L * (L ^ m' * _)
            _ ≤ L * ((L + 1) ^ m' * L ^ J'') := Nat.mul_le_mul_left L (ih J'')
            _ = 1 * ((L + 1) ^ m' * L ^ (J'' + 1)) := by
                  rw [Nat.one_mul, Nat.pow_succ L J'', ← Nat.mul_assoc,
                    Nat.mul_comm L ((L + 1) ^ m'), Nat.mul_assoc, Nat.mul_comm L (L ^ J'')]
        calc L * (L ^ m' * _) + L * (L ^ m' * _)
          _ ≤ L * ((L + 1) ^ m' * L ^ (J'' + 1)) + 1 * ((L + 1) ^ m' * L ^ (J'' + 1)) :=
                Nat.add_le_add h1 h2
          _ = (L + 1) ^ (m' + 1) * L ^ (J'' + 1) := by
                rw [← Nat.add_mul, Nat.pow_succ (L + 1) m', Nat.mul_comm ((L + 1) ^ m') (L + 1),
                  Nat.mul_assoc]
  rw [truncBinomFast_eq_spec]
  have hSq : (L - 1) * (L + 1) ≤ L * L := by
    rw [Nat.mul_add, Nat.mul_one]
    have hSub := Nat.add_le_add_left (Nat.sub_le L 1) ((L - 1) * L)
    have hEq : (L - 1 + 1) * L = L * L := by rw [Nat.sub_add_cancel hL]
    rw [Nat.add_mul, Nat.one_mul] at hEq
    exact Decidable.byContradiction (fun _ => by omega)
  have hPowProd : ∀ k, (L - 1) ^ k * (L + 1) ^ k ≤ L ^ k * L ^ k := by
    intro k; induction k with
    | zero => exact Nat.le_refl 1
    | succ k' ih =>
      rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ]
      calc ((L - 1) ^ k' * (L - 1)) * ((L + 1) ^ k' * (L + 1))
        _ = ((L - 1) ^ k' * (L + 1) ^ k') * ((L - 1) * (L + 1)) := by
              rw [Nat.mul_assoc, Nat.mul_left_comm (L - 1), ← Nat.mul_assoc]
        _ ≤ (L ^ k' * L ^ k') * (L * L) := Nat.mul_le_mul ih hSq
        _ = (L ^ k' * L) * (L ^ k' * L) := by
              rw [Nat.mul_assoc (L ^ k') (L ^ k') (L * L), Nat.mul_left_comm (L ^ k') L L,
                ← Nat.mul_assoc (L ^ k') L (L ^ k' * L)]
  have hChain : L ^ m * ((L - 1) ^ m * ((List.range (J + 1)).map fun j =>
      binomChoose m j * L ^ (J - j)).sum) ≤ L ^ m * L ^ (m + J) := by
    calc L ^ m * ((L - 1) ^ m * _)
      _ = (L - 1) ^ m * (L ^ m * _) := Nat.mul_left_comm _ _ _
      _ ≤ (L - 1) ^ m * ((L + 1) ^ m * L ^ J) := Nat.mul_le_mul_left _ (hLower m J)
      _ = ((L - 1) ^ m * (L + 1) ^ m) * L ^ J := (Nat.mul_assoc _ _ _).symm
      _ ≤ (L ^ m * L ^ m) * L ^ J := Nat.mul_le_mul_right _ (hPowProd m)
      _ = L ^ m * L ^ (m + J) := by rw [Nat.mul_assoc, ← Nat.pow_add]
  exact Nat.le_of_mul_le_mul_left hChain (Nat.pow_pos hL)

/-- Call-by-need kernel sum of the `1 ≤ g ≤ rem` FORS subset-cover terms scaled by `2^{160}`,
    taking `tMin` as an explicit function argument so `truncBinomFast` is shared across all `g`. -/
@[expose] def fips205MainSum160 (h a k qSign G J tMin : Nat) : Nat → Nat
  | 0 => 0
  | idx + 1 =>
    let g := idx + 1
    let L := 2 ^ h
    let termNum := qSign ^ g * (factFast G / factFast g) *
      L ^ (G - g + J) * (2 ^ (a * g) - (2 ^ a - 1) ^ g) ^ k
    let termDen := factFast G * L ^ G * tMin * 2 ^ (a * g * k)
    (termNum * 2 ^ 160 + termDen) / termDen + fips205MainSum160 h a k qSign G J tMin idx

/-- Exact finite rational upper bound on the NIST FIPS 205 interleaved FORS `ITSR` sum across
    `qSign` signatures (`1 ≤ g ≤ G` exact FORS cover + geometric factorial tail `g ≥ G + 1`). -/
@[expose] def fips205InterleavedItsrBound (p : Fips205Params) (qSign G J : Nat) : Spec.RatBound :=
  let L := 2 ^ p.h
  let mainNum := fips205MainSum160 p.h p.a p.k qSign G J (truncBinomFast L (qSign - G) J) G
  Spec.RatBound.add ⟨mainNum, 2 ^ 160, Nat.two_pow_pos 160⟩
    ⟨2 * qSign ^ (G + 1), factFast (G + 1) * L ^ (G + 1),
      Nat.mul_pos (factFast_pos (G + 1)) (Nat.pow_pos (Nat.two_pow_pos p.h))⟩

/-- Kernel-certified NIST FIPS 205 interleaved FORS `ITSR` bit-security floors at `qSign = 2^64`:
    `< 2^{-133}` for `SLH-DSA-SHAKE-128s` and `< 2^{-131}` per `H_msg` evaluation (`< 2^{-129}` across
    `≤ 4` evaluations) for `SLH-DSA-SHAKE-128f`. -/
theorem fips205_interleaved_itsr_128s_128f_bounds :
    (fips205InterleavedItsrBound fips205SlhDsa128sParams (2 ^ 64) 48 12).lt ⟨1, 2 ^ 133, by decide⟩ ∧
    (fips205InterleavedItsrBound fips205SlhDsa128fParams (2 ^ 64) 26 6).lt ⟨1, 2 ^ 131, by decide⟩ ∧
    (Spec.RatBound.scale 4
      (fips205InterleavedItsrBound fips205SlhDsa128fParams (2 ^ 64) 26 6)).lt ⟨1, 2 ^ 129, by decide⟩ :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- Concrete multi-hop classical / QROM security budget for NIST FIPS 205 `SLH-DSA` Category-1. -/
@[expose] def fips205ConcreteSecurityBudget (p : Fips205Params) (qHMsg G J : Nat)
    (εPrim : Spec.RatBound) : Spec.RatBound :=
  (((Spec.RatBound.scale qHMsg (fips205InterleavedItsrBound p (2 ^ 64) G J)).add εPrim).add
    εPrim).add (Spec.RatBound.scale (2 ^ 20) εPrim)

private theorem fips205Budget_le_cap (p : Fips205Params) {qH qCap G J : Nat} (hq : qH ≤ qCap)
    {εFloor ε₁ ε₂ : Spec.RatBound}
    (hFloor : (fips205InterleavedItsrBound p (2 ^ 64) G J).le εFloor) (hEps : ε₁.le ε₂) :
    (fips205ConcreteSecurityBudget p qH G J ε₁).le
      ((((Spec.RatBound.scale qCap εFloor).add ε₂).add ε₂).add (Spec.RatBound.scale (2 ^ 20) ε₂)) := by
  have hItsr : (Spec.RatBound.scale qH (fips205InterleavedItsrBound p (2 ^ 64) G J)).le
      (Spec.RatBound.scale qCap εFloor) := by
    refine Spec.RatBound.le_trans ?_ (Spec.RatBound.scale_le_scale qCap hFloor)
    unfold Spec.RatBound.le Spec.RatBound.scale; dsimp only
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hq)
  exact Spec.RatBound.add_le_add
    (Spec.RatBound.add_le_add (Spec.RatBound.add_le_add hItsr hEps) hEps)
    (Spec.RatBound.scale_le_scale _ hEps)

/-- **NIST FIPS 205 `SLH-DSA-SHAKE-128s` Concrete Classical & QROM Security `< 2^{-128}`.**
    Combines `slhVerifyInternal_slhSignInternal`, `fips205_wots_incomparable_no_chain_forgery`, and
    the `< 2^{-133}` interleaved FORS `ITSR` bound (`qHMsg ≤ 16`). -/
theorem fips205_slhDsa128s_concrete_security_lt_2_neg_128
    {qHMsg qEvalClassical qEvalQrom : Nat}
    (hqHMsg : qHMsg ≤ 16) (hqCl : qEvalClassical ≤ 2 ^ 96) (hqQr : qEvalQrom ≤ 2 ^ 48) :
    (∀ skSeed skPrf pkSeed msgPrime optRand,
      let (sk, pk) := slhKeygenInternal fips205SlhDsa128sParams skSeed skPrf pkSeed
      slhVerifyInternal fips205SlhDsa128sParams msgPrime
        (slhSignInternal fips205SlhDsa128sParams msgPrime sk optRand) pk = true ∧
      (encodeSlhSig (slhSignInternal fips205SlhDsa128sParams msgPrime sk optRand)).length = 7856) ∧
    (∀ {msg₁ msg₂ : List UInt8},
      msg₁.length = fips205SlhDsa128sParams.n → msg₂.length = fips205SlhDsa128sParams.n →
      msg₁ ≠ msg₂ →
      let w₁ := fipsWotsDigits (2 * fips205SlhDsa128sParams.n) msg₁
      let w₂ := fipsWotsDigits (2 * fips205SlhDsa128sParams.n) msg₂
      ∃ (idx : Nat) (h1 : idx < w₁.length) (h2 : idx < w₂.length), w₂[idx]'h2 < w₁[idx]'h1) ∧
    (fips205ConcreteSecurityBudget fips205SlhDsa128sParams qHMsg 48 12
      (classical256PrimEps qEvalClassical)).lt ⟨1, 2 ^ 128, by decide⟩ ∧
    (fips205ConcreteSecurityBudget fips205SlhDsa128sParams qHMsg 48 12
      (pqQrom256PrimEps qEvalQrom)).lt ⟨1, 2 ^ 128, by decide⟩ := by
  have hFl := Spec.RatBound.le_of_lt fips205_interleaved_itsr_128s_128f_bounds.1
  refine ⟨fun skSeed skPrf pkSeed msgPrime optRand =>
    ⟨slhVerifyInternal_slhSignInternal fips205SlhDsa128sParams slhDsaShake128s_wellFormed
      skSeed skPrf pkSeed msgPrime optRand,
     (encodeSlhSig_slhSignInternal_length fips205SlhDsa128sParams msgPrime _ optRand).trans
       slhDsaShake128s_sigBytes⟩,
    fun h1 h2 hNe => fips205_wots_incomparable_no_chain_forgery (by decide) h1 h2 hNe,
    Spec.RatBound.lt_of_le_of_lt
      (fips205Budget_le_cap _ hqHMsg hFl (classical256PrimEps_mono hqCl)) (by decide +kernel),
    Spec.RatBound.lt_of_le_of_lt
      (fips205Budget_le_cap _ hqHMsg hFl (pqQrom256PrimEps_mono hqQr)) (by decide +kernel)⟩

/-- **NIST FIPS 205 `SLH-DSA-SHAKE-128f` Concrete Classical & QROM Security `< 2^{-128}`.**
    Combines `slhVerifyInternal_slhSignInternal`, `fips205_wots_incomparable_no_chain_forgery`, and
    the `< 2^{-129}` (`qHMsg ≤ 4`) interleaved FORS `ITSR` bound. -/
theorem fips205_slhDsa128f_concrete_security_lt_2_neg_128
    {qHMsg qEvalClassical qEvalQrom : Nat}
    (hqHMsg : qHMsg ≤ 4) (hqCl : qEvalClassical ≤ 2 ^ 96) (hqQr : qEvalQrom ≤ 2 ^ 48) :
    (∀ skSeed skPrf pkSeed msgPrime optRand,
      let (sk, pk) := slhKeygenInternal fips205SlhDsa128fParams skSeed skPrf pkSeed
      slhVerifyInternal fips205SlhDsa128fParams msgPrime
        (slhSignInternal fips205SlhDsa128fParams msgPrime sk optRand) pk = true ∧
      (encodeSlhSig (slhSignInternal fips205SlhDsa128fParams msgPrime sk optRand)).length = 17088) ∧
    (∀ {msg₁ msg₂ : List UInt8},
      msg₁.length = fips205SlhDsa128fParams.n → msg₂.length = fips205SlhDsa128fParams.n →
      msg₁ ≠ msg₂ →
      let w₁ := fipsWotsDigits (2 * fips205SlhDsa128fParams.n) msg₁
      let w₂ := fipsWotsDigits (2 * fips205SlhDsa128fParams.n) msg₂
      ∃ (idx : Nat) (h1 : idx < w₁.length) (h2 : idx < w₂.length), w₂[idx]'h2 < w₁[idx]'h1) ∧
    (fips205ConcreteSecurityBudget fips205SlhDsa128fParams qHMsg 26 6
      (classical256PrimEps qEvalClassical)).lt ⟨1, 2 ^ 128, by decide⟩ ∧
    (fips205ConcreteSecurityBudget fips205SlhDsa128fParams qHMsg 26 6
      (pqQrom256PrimEps qEvalQrom)).lt ⟨1, 2 ^ 128, by decide⟩ := by
  have hFl := Spec.RatBound.le_of_lt fips205_interleaved_itsr_128s_128f_bounds.2.1
  refine ⟨fun skSeed skPrf pkSeed msgPrime optRand =>
    ⟨slhVerifyInternal_slhSignInternal fips205SlhDsa128fParams slhDsaShake128f_wellFormed
      skSeed skPrf pkSeed msgPrime optRand,
     (encodeSlhSig_slhSignInternal_length fips205SlhDsa128fParams msgPrime _ optRand).trans
       slhDsaShake128f_sigBytes⟩,
    fun h1 h2 hNe => fips205_wots_incomparable_no_chain_forgery (by decide) h1 h2 hNe,
    Spec.RatBound.lt_of_le_of_lt
      (fips205Budget_le_cap _ hqHMsg hFl (classical256PrimEps_mono hqCl)) (by decide +kernel),
    Spec.RatBound.lt_of_le_of_lt
      (fips205Budget_le_cap _ hqHMsg hFl (pqQrom256PrimEps_mono hqQr)) (by decide +kernel)⟩

/-! ## §3. Inhabitedness Witnesses & Six-Kernel Assurance Audits -/

/-- Joint inhabitedness witness for `jortsProd_pq_qrom_budget_lt_2_neg_128`. -/
theorem inhabited_jortsProd_pq_qrom_budget :
    ∃ qSign qEval : Nat, qSign ≤ 2 ^ 16 ∧ qEval ≤ 2 ^ 48 ∧
      (jortsMultiHopBudget qSign (pqQrom256PrimEps qEval) (pqQrom256PrimEps qEval)
        (pqQrom256PrimEps qEval) (pqQrom256PrimEps qEval)).lt ⟨1, 2 ^ 128, by decide⟩ :=
  ⟨2 ^ 16, 2 ^ 48, Nat.le_refl _, Nat.le_refl _,
    jortsProd_pq_qrom_budget_lt_2_neg_128 (Nat.le_refl _) (Nat.le_refl _)⟩

/-- Joint inhabitedness witness for `fips205_slhDsa128s_concrete_security_lt_2_neg_128`. -/
theorem inhabited_fips205_slhDsa128s_security :
    ∃ qHMsg qCl qQr : Nat, qHMsg ≤ 16 ∧ qCl ≤ 2 ^ 96 ∧ qQr ≤ 2 ^ 48 ∧
      (fips205ConcreteSecurityBudget fips205SlhDsa128sParams qHMsg 48 12
        (pqQrom256PrimEps qQr)).lt ⟨1, 2 ^ 128, by decide⟩ :=
  ⟨16, 2 ^ 96, 2 ^ 48, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
    (fips205_slhDsa128s_concrete_security_lt_2_neg_128
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)).2.2.2⟩

/-- Joint inhabitedness witness for `fips205_slhDsa128f_concrete_security_lt_2_neg_128`. -/
theorem inhabited_fips205_slhDsa128f_concrete_security :
    ∃ qHMsg qCl qQr : Nat, qHMsg ≤ 4 ∧ qCl ≤ 2 ^ 96 ∧ qQr ≤ 2 ^ 48 ∧
      (fips205ConcreteSecurityBudget fips205SlhDsa128fParams qHMsg 26 6
        (pqQrom256PrimEps qQr)).lt ⟨1, 2 ^ 128, by decide⟩ :=
  ⟨4, 2 ^ 96, 2 ^ 48, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
    (fips205_slhDsa128f_concrete_security_lt_2_neg_128
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)).2.2.2⟩

#verify_constructive
  Qsag.pqMultiHopBudget_mono
  Qsag.jortsProd_classical_euf_cma_lt_2_neg_128
  Qsag.jortsProd_pq_qrom_euf_cma_lt_2_neg_128
  Qsag.jortsProd_pq_qrom_budget_lt_2_neg_128
  Qsag.baggySha3_128f_pors_itsr_lt_2_neg_131
  Qsag.baggySha3_128f_classical_euf_cma_lt_2_neg_128
  Qsag.baggySha3_128f_pq_qrom_euf_cma_lt_2_neg_128
  Qsag.corduroyProd_concrete_euf_cma_bound
  Qsag.baggyProd_concrete_euf_cma_bound
  Qsag.binomChoose_mul_factFast
  Qsag.one_sub_pow_mul_truncBinom_le
  Qsag.fips205_interleaved_itsr_128s_128f_bounds
  Qsag.fips205_slhDsa128s_concrete_security_lt_2_neg_128
  Qsag.fips205_slhDsa128f_concrete_security_lt_2_neg_128
  Qsag.inhabited_jortsProd_pq_qrom_budget
  Qsag.inhabited_fips205_slhDsa128s_security
  Qsag.inhabited_fips205_slhDsa128f_concrete_security

#verify_inhabited
  Qsag.jortsProd_pq_qrom_budget_lt_2_neg_128
  Qsag.inhabited_jortsProd_pq_qrom_budget
#verify_inhabited
  Qsag.fips205_slhDsa128s_concrete_security_lt_2_neg_128
  Qsag.inhabited_fips205_slhDsa128s_security
#verify_inhabited
  Qsag.fips205_slhDsa128f_concrete_security_lt_2_neg_128
  Qsag.inhabited_fips205_slhDsa128f_concrete_security

#tooth_pair Qsag.jortsProd_pq_qrom_euf_cma_lt_2_neg_128 vs
  Qsag.tooth_pq_grover_2pow64_exceeds_128bit_bound
#tooth_pair Qsag.baggySha3_128f_pq_qrom_euf_cma_lt_2_neg_128 vs
  Qsag.tooth_pq_grover_2pow64_exceeds_128bit_bound
#tooth_pair Qsag.jortsProd_classical_euf_cma_lt_2_neg_128 vs
  Qsag.tooth_classical_2pow128_exceeds_128bit_bound
#tooth_pair Qsag.fips205_slhDsa128f_concrete_security_lt_2_neg_128 vs
  Qsag.tooth_fips205_128f_bad_hmsg_rejected

end Qsag
end
