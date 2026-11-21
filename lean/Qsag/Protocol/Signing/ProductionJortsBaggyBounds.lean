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
