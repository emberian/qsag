module
/-
# Production signing reductions and numerical budgets

The QSAG reductions evaluate the real signing game. Their right-hand sides include
the primitive costs of the PRF, ITSR, open-seed TCR, PRE, and UD reductions.
The global slot count charges one PRE per slot and one UD per preceding WOTS step. The PORS+FP subset count and FIPS 205 arithmetic use their
respective parameter models.
-/

public import Qsag.Protocol.Signing.HulsingClosedMultiHop
public import Qsag.Protocol.Threshold.MultiSessionMacBlindHybrid
import Qsag.Tactic.AssuranceKit

public section
attribute [-instance] Fin.instLinearOrderPackage
namespace Qsag
open scoped Qsag.Spec

set_option autoImplicit false
set_option exponentiation.threshold 512
set_option maxRecDepth 4096

/-! ## QSAG profile reductions and budget arithmetic -/

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

/-- Jorts runs the epoch latch during all three reductions. -/
theorem jortsProd_exec_prf_tcr_reduction :
    PrfTcrReductionFor true jortsProdParams (fun _ => rfl)
      (.inl (by rw [jortsProdParams, jortsPoseidon2Params_eq])) :=
  hulsing_prf_tcr_residual_bound _ _ _ _

/-- Baggy admits all adaptive signing requests, including repeated epochs. -/
theorem baggyProd_exec_prf_tcr_reduction :
    PrfTcrReductionFor false baggyProdParams (by rw [baggyProdParams, baggy128fParams_eq]; decide)
      (.inl (by rw [baggyProdParams, baggy128fParams_eq])) :=
  hulsing_prf_tcr_residual_bound _ _ _ _

/-- Corduroy uses the same stateless signing experiment as Baggy. -/
theorem corduroyProd_exec_prf_tcr_reduction :
    PrfTcrReductionFor false corduroyProdParams (by rw [corduroyProdParams, corduroyCustody128Params_eq]; decide)
      (.inl (by rw [corduroyProdParams, corduroyCustody128Params_eq])) :=
  hulsing_prf_tcr_residual_bound _ _ _ _

theorem globalSlotBudget_mono (p : PqHashParams) {q qMax : Nat} (hq : q ≤ qMax)
    {cover coverMax prim primMax : Spec.RatBound} (hc : cover.le coverMax) (hp : prim.le primMax) :
    (globalSlotBudget p q cover prim).le (globalSlotBudget p qMax coverMax primMax) := by
  apply Spec.RatBound.add_le_add _ (Spec.RatBound.scale_le_scale _ hp)
  apply Spec.RatBound.add_le_add hc
  show (if p.statefulJorts then 0 else q) * 2 ^ 256 ≤ (if p.statefulJorts then 0 else qMax) * 2 ^ 256
  exact Nat.mul_le_mul_right _ (by cases p.statefulJorts <;> simp [hq])

theorem jortsProd_classical_global_slot_budget_lt_2_neg_128 {qSign qEval : Nat}
    (hSign : qSign ≤ 2 ^ 16) (hEval : qEval ≤ 2 ^ 96) :
    (globalSlotBudget jortsProdParams qSign Spec.RatBound.zero (classical256PrimEps qEval)).lt
      ⟨1, 2 ^ 128, by decide⟩ := by
  apply Spec.RatBound.lt_of_le_of_lt (globalSlotBudget_mono jortsProdParams hSign
    (Spec.RatBound.le_refl _) (classical256PrimEps_mono hEval))
  unfold globalSlotBudget globalPreUdCalls
  rw [jortsProdParams, jortsPoseidon2Params_eq]
  decide +kernel

theorem jortsProd_pq_qrom_global_slot_budget_lt_2_neg_128 {qSign qEval : Nat}
    (hSign : qSign ≤ 2 ^ 16) (hEval : qEval ≤ 2 ^ 48) :
    (globalSlotBudget jortsProdParams qSign Spec.RatBound.zero (pqQrom256PrimEps qEval)).lt
      ⟨1, 2 ^ 128, by decide⟩ := by
  apply Spec.RatBound.lt_of_le_of_lt (globalSlotBudget_mono jortsProdParams hSign
    (Spec.RatBound.le_refl _) (pqQrom256PrimEps_mono hEval))
  unfold globalSlotBudget globalPreUdCalls
  rw [jortsProdParams, jortsPoseidon2Params_eq]
  decide +kernel

theorem baggyProd_classical_global_slot_budget_lt_2_neg_128 {qSign qEval : Nat}
    (hSign : qSign ≤ 2 ^ 16) (hEval : qEval ≤ 2 ^ 80) :
    (globalSlotBudget baggyProdParams qSign ⟨1, 2 ^ 131, by decide⟩ (classical256PrimEps qEval)).lt
      ⟨1, 2 ^ 128, by decide⟩ := by
  apply Spec.RatBound.lt_of_le_of_lt (globalSlotBudget_mono baggyProdParams hSign
    (Spec.RatBound.le_refl _) (classical256PrimEps_mono hEval))
  unfold globalSlotBudget globalPreUdCalls
  rw [baggyProdParams, baggy128fParams_eq]
  decide +kernel

theorem baggyProd_pq_qrom_global_slot_budget_lt_2_neg_128 {qSign qEval : Nat}
    (hSign : qSign ≤ 2 ^ 16) (hEval : qEval ≤ 2 ^ 40) :
    (globalSlotBudget baggyProdParams qSign ⟨1, 2 ^ 131, by decide⟩ (pqQrom256PrimEps qEval)).lt
      ⟨1, 2 ^ 128, by decide⟩ := by
  apply Spec.RatBound.lt_of_le_of_lt (globalSlotBudget_mono baggyProdParams hSign
    (Spec.RatBound.le_refl _) (pqQrom256PrimEps_mono hEval))
  unfold globalSlotBudget globalPreUdCalls
  rw [baggyProdParams, baggy128fParams_eq]
  decide +kernel

theorem corduroyProd_pq_qrom_global_slot_budget_lt_2_neg_128 {qSign qEval : Nat}
    (hSign : qSign ≤ 2 ^ 12) (hEval : qEval ≤ 2 ^ 40) :
    (globalSlotBudget corduroyProdParams qSign ⟨1, 2 ^ 131, by decide⟩ (pqQrom256PrimEps qEval)).lt
      ⟨1, 2 ^ 128, by decide⟩ := by
  apply Spec.RatBound.lt_of_le_of_lt (globalSlotBudget_mono corduroyProdParams hSign
    (Spec.RatBound.le_refl _) (pqQrom256PrimEps_mono hEval))
  unfold globalSlotBudget globalPreUdCalls
  rw [corduroyProdParams, corduroyCustody128Params_eq]
  decide +kernel

/-- Height-60 stateless WOTS+C execution profile for the QSAG production verifier. -/
def slhDsaW16StatelessParams : PqHashParams := ⟨16, 64, 5, 12, 33, 6, 16, false⟩

theorem slhDsaW16StatelessParams_geometry :
    slhDsaW16StatelessParams.productionWellFormed = true ∧
    slhDsaW16StatelessParams.statefulJorts = false ∧ slhDsaW16StatelessParams.w = 16 ∧
    slhDsaW16StatelessParams.numLayers * slhDsaW16StatelessParams.subtreeHeight = 60 ∧
    slhDsaW16StatelessParams.forsTrees ≤ 2 ^ 32 := by
  rw [PqHashParams.productionWellFormed_eq]
  decide +kernel

theorem slhDsaW16_pq_qrom_global_slot_budget_lt_2_neg_128 {qSign qEval : Nat}
    (hSign : qSign ≤ 2 ^ 16) (hEval : qEval ≤ 2 ^ 25) :
    (globalSlotBudget slhDsaW16StatelessParams qSign ⟨1, 2 ^ 131, by decide⟩
      (pqQrom256PrimEps qEval)).lt ⟨1, 2 ^ 128, by decide⟩ := by
  apply Spec.RatBound.lt_of_le_of_lt (globalSlotBudget_mono slhDsaW16StatelessParams hSign
    (Spec.RatBound.le_refl _) (pqQrom256PrimEps_mono hEval))
  decide +kernel

/-- Existence of a single consistent choice of all primitive classes and their hardness proofs. -/
def BaggyPrimitiveAssumptions {q : Nat} (E : SigningExperiment q) (suite : TweakableHashSuite)
    (cover prim : Spec.RatBound) : Prop := Nonempty (SigningPrimitiveBounds E false suite baggyProdParams cover prim)

theorem baggyProd_stateless_exec_euf_cma_bound {q : Nat} (E : SigningExperiment q) (suite : TweakableHashSuite)
    (cover prim : Spec.RatBound) (H : BaggyPrimitiveAssumptions E suite cover prim) :
    Spec.GameBound (ExecStatelessEufCmaGame E.pos suite baggyProdParams E.keygen E.adversary).winProb
      (globalSlotBudget baggyProdParams q cover prim) := by
  obtain ⟨h⟩ := H
  exact hulsing_closed_multihop_euf_cma_bound E false suite baggyProdParams baggy128f_productionWellFormed
    (by rw [baggyProdParams, baggy128fParams_eq]; decide) cover prim h

#verify_constructive baggyProd_stateless_exec_euf_cma_bound

theorem jortsProd_classical_exec_euf_cma_lt_2_neg_128 {q qEval : Nat} (E : SigningExperiment q)
    (suite : TweakableHashSuite) (hq : q ≤ 2^16) (he : qEval ≤ 2^96)
    (H : SigningPrimitiveBounds E true suite jortsProdParams Spec.RatBound.zero (classical256PrimEps qEval)) :
    (ExecEufCmaGame E.pos suite jortsProdParams E.keygen E.adversary).winProb.lt ⟨1, 2^128, Nat.two_pow_pos 128⟩ :=
  Spec.RatBound.lt_of_le_of_lt (hulsing_closed_multihop_euf_cma_bound E true suite jortsProdParams
    jortsPoseidon2_productionWellFormed (by rw [jortsProdParams, jortsPoseidon2Params_eq]; decide) _ _ H)
    (jortsProd_classical_global_slot_budget_lt_2_neg_128 hq he)

theorem jortsProd_pq_qrom_exec_euf_cma_lt_2_neg_128 {q qEval : Nat} (E : SigningExperiment q)
    (suite : TweakableHashSuite) (hq : q ≤ 2^16) (he : qEval ≤ 2^48)
    (H : SigningPrimitiveBounds E true suite jortsProdParams Spec.RatBound.zero (pqQrom256PrimEps qEval)) :
    (ExecEufCmaGame E.pos suite jortsProdParams E.keygen E.adversary).winProb.lt ⟨1, 2^128, Nat.two_pow_pos 128⟩ :=
  Spec.RatBound.lt_of_le_of_lt (hulsing_closed_multihop_euf_cma_bound E true suite jortsProdParams
    jortsPoseidon2_productionWellFormed (by rw [jortsProdParams, jortsPoseidon2Params_eq]; decide) _ _ H)
    (jortsProd_pq_qrom_global_slot_budget_lt_2_neg_128 hq he)

theorem baggyProd_classical_exec_euf_cma_lt_2_neg_128 {q qEval : Nat} (E : SigningExperiment q)
    (suite : TweakableHashSuite) (hq : q ≤ 2^16) (he : qEval ≤ 2^80)
    (H : SigningPrimitiveBounds E false suite baggyProdParams ⟨1, 2^131, Nat.two_pow_pos 131⟩ (classical256PrimEps qEval)) :
    (ExecStatelessEufCmaGame E.pos suite baggyProdParams E.keygen E.adversary).winProb.lt ⟨1, 2^128, Nat.two_pow_pos 128⟩ :=
  Spec.RatBound.lt_of_le_of_lt (hulsing_closed_multihop_euf_cma_bound E false suite baggyProdParams
    baggy128f_productionWellFormed (by rw [baggyProdParams, baggy128fParams_eq]; decide) _ _ H)
    (baggyProd_classical_global_slot_budget_lt_2_neg_128 hq he)

theorem baggyProd_pq_qrom_exec_euf_cma_lt_2_neg_128 {q qEval : Nat} (E : SigningExperiment q)
    (suite : TweakableHashSuite) (hq : q ≤ 2^16) (he : qEval ≤ 2^40)
    (H : SigningPrimitiveBounds E false suite baggyProdParams ⟨1, 2^131, Nat.two_pow_pos 131⟩ (pqQrom256PrimEps qEval)) :
    (ExecStatelessEufCmaGame E.pos suite baggyProdParams E.keygen E.adversary).winProb.lt ⟨1, 2^128, Nat.two_pow_pos 128⟩ :=
  Spec.RatBound.lt_of_le_of_lt (hulsing_closed_multihop_euf_cma_bound E false suite baggyProdParams
    baggy128f_productionWellFormed (by rw [baggyProdParams, baggy128fParams_eq]; decide) _ _ H)
    (baggyProd_pq_qrom_global_slot_budget_lt_2_neg_128 hq he)

theorem corduroyProd_pq_qrom_exec_euf_cma_lt_2_neg_128 {q qEval : Nat} (E : SigningExperiment q)
    (suite : TweakableHashSuite) (hq : q ≤ 2^12) (he : qEval ≤ 2^40)
    (H : SigningPrimitiveBounds E false suite corduroyProdParams ⟨1, 2^131, Nat.two_pow_pos 131⟩ (pqQrom256PrimEps qEval)) :
    (ExecStatelessEufCmaGame E.pos suite corduroyProdParams E.keygen E.adversary).winProb.lt ⟨1, 2^128, Nat.two_pow_pos 128⟩ :=
  Spec.RatBound.lt_of_le_of_lt (hulsing_closed_multihop_euf_cma_bound E false suite corduroyProdParams
    corduroyCustody128_productionWellFormed (by rw [corduroyProdParams, corduroyCustody128Params_eq]; decide) _ _ H)
    (corduroyProd_pq_qrom_global_slot_budget_lt_2_neg_128 hq he)

theorem slhDsaW16_pq_qrom_exec_euf_cma_lt_2_neg_128 {q qEval : Nat} (E : SigningExperiment q)
    (suite : TweakableHashSuite) (hq : q ≤ 2^16) (he : qEval ≤ 2^25)
    (H : SigningPrimitiveBounds E false suite slhDsaW16StatelessParams ⟨1, 2^131, Nat.two_pow_pos 131⟩ (pqQrom256PrimEps qEval)) :
    (ExecStatelessEufCmaGame E.pos suite slhDsaW16StatelessParams E.keygen E.adversary).winProb.lt ⟨1, 2^128, Nat.two_pow_pos 128⟩ :=
  Spec.RatBound.lt_of_le_of_lt (hulsing_closed_multihop_euf_cma_bound E false suite slhDsaW16StatelessParams
    slhDsaW16StatelessParams_geometry.1 (by exact slhDsaW16StatelessParams_geometry.2.2.2.2) _ _ H)
    (slhDsaW16_pq_qrom_global_slot_budget_lt_2_neg_128 hq he)

#verify_constructive jortsProd_classical_exec_euf_cma_lt_2_neg_128
  jortsProd_pq_qrom_exec_euf_cma_lt_2_neg_128
  baggyProd_classical_exec_euf_cma_lt_2_neg_128
  baggyProd_pq_qrom_exec_euf_cma_lt_2_neg_128
  corduroyProd_pq_qrom_exec_euf_cma_lt_2_neg_128
  slhDsaW16_pq_qrom_exec_euf_cma_lt_2_neg_128

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

private structure WitnessPrfTable (keyLen inputLen : Nat) where
  size : Nat
  pos : 0 < size
  sample : Fin size → Spec.Bytes × (Spec.Bytes → Spec.Bytes)
  uniform : Spec.UniformOn (Spec.PrfSampleOk keyLen inputLen 32) sample

private def witnessTable (keyLen inputLen : Nat) : WitnessPrfTable keyLen inputLen where
  size := pow256 keyLen * MacBlind.seqTapeCard (pow256 32) (256^inputLen)
  pos := Nat.mul_pos (pow256_pos keyLen) (MacBlind.seqTapeCard_pos (pow256_pos 32) _)
  sample := MacBlind.funTapePrfSampler (byteVecSampler keyLen) (byteVecSampler 32) inputLen
  uniform := MacBlind.uniformOn_funTapePrfSampler (uniformOn_byteVecSampler keyLen) (uniformOn_byteVecSampler 32)

private def mkWitnessExperiment (keyLen seedLen : Nat) (msg : WitnessPrfTable keyLen 65)
    (sec : WitnessPrfTable keyLen (seedLen+32)) : SigningExperiment 0 where
  n := msg.size * (sec.size * (pow256 seedLen * 1))
  nm := msg.size
  nr := sec.size * (pow256 seedLen * 1)
  nc := sec.size
  nz := pow256 seedLen * 1
  ns := pow256 seedLen
  na := 1
  keyLen := keyLen
  seedLen := seedLen
  qHash := 0
  pos := Nat.mul_pos msg.pos (Nat.mul_pos sec.pos (Nat.mul_pos (pow256_pos seedLen) Nat.one_pos))
  a := Spec.CoinSplit.prod _ _
  b := Spec.CoinSplit.prod _ _
  c := Spec.CoinSplit.prod _ _
  msg := msg.sample
  sec := sec.sample
  seed := byteVecSampler seedLen
  adv := fun _ => emptySigningForgery
  uniformMsg := msg.uniform
  uniformSec := sec.uniform
  uniformSeed := uniformOn_byteVecSampler seedLen

private def witnessExperiment := mkWitnessExperiment 32 32 (witnessTable 32 65) (witnessTable 32 64)

private theorem advDist_one {n : Nat} (a b : Spec.FinGame n) : Spec.GameBound (Spec.AdvDist a b) Spec.RatBound.one := by
  have ha : a.winCount*1 ≤ 1*n := Spec.FinGame.winProb_le_one a
  have hb : b.winCount*1 ≤ 1*n := Spec.FinGame.winProb_le_one b
  change Spec.natAbsDiff _ _ * 1 ≤ 1*n
  unfold Spec.natAbsDiff; split <;> omega

private def baggyUnitBounds (E : SigningExperiment 0) (suite : TweakableHashSuite) :
    SigningPrimitiveBounds E false suite baggyProdParams Spec.RatBound.one Spec.RatBound.one where
  word := .inl (by rw [baggyProdParams, baggy128fParams_eq])
  oneTime := by rw [baggyProdParams, baggy128fParams_eq]; decide
  msgClass := fun _ => True
  secClass := fun _ => True
  itsrClass := fun _ => True
  tcrClass := fun _ => True
  preClass := fun _ => True
  udClass := fun _ => True
  msgMember := fun _ => trivial
  secMember := fun _ _ => trivial
  itsrMember := fun _ _ _ => trivial
  tcrMember := fun _ _ _ => trivial
  prehashMember := fun _ _ _ => trivial
  slotMember := fun _ _ _ slot => slotReductionClass_unrestricted _ _ _ _ _ _ slot
  prfMsg := MacBlind.prfHard_one _ _ _ _ _ _
  prfSec := MacBlind.prfHard_one _ _ _ _ _ _
  itsr := fun _ _ _ _ _ _ _ _ _ _ _ _ => Spec.FinGame.winProb_le_one _
  tcr := fun _ _ _ _ _ _ _ _ _ => Spec.FinGame.winProb_le_one _
  pre := fun _ _ _ _ _ _ _ _ _ => Spec.FinGame.winProb_le_one _
  ud := fun _ _ _ _ _ _ _ _ _ => advDist_one _ _

/-- Joint unit-loss witness on full 32-byte uniform samplers and unrestricted primitive classes. -/
theorem inhabited_baggyProd_stateless_exec_euf_cma :
    ∃ (E : SigningExperiment 0) (suite : TweakableHashSuite),
      BaggyPrimitiveAssumptions E suite Spec.RatBound.one Spec.RatBound.one ∧
      Spec.GameBound (ExecStatelessEufCmaGame E.pos suite baggyProdParams E.keygen E.adversary).winProb
        (globalSlotBudget baggyProdParams 0 Spec.RatBound.one Spec.RatBound.one) := by
  let h := baggyUnitBounds witnessExperiment cshake256Suite
  exact ⟨witnessExperiment, cshake256Suite, ⟨h⟩, baggyProd_stateless_exec_euf_cma_bound _ _ _ _ ⟨h⟩⟩

#verify_constructive advDist_one inhabited_baggyProd_stateless_exec_euf_cma
#verify_inhabited baggyProd_stateless_exec_euf_cma_bound inhabited_baggyProd_stateless_exec_euf_cma

theorem inhabited_baggyProd_pq_qrom_exec_euf_cma_lt_2_neg_128 :
    ∃ (q qEval : Nat) (E : SigningExperiment q) (suite : TweakableHashSuite),
      q ≤ 2^16 ∧ qEval ≤ 2^40 ∧
      Nonempty (SigningPrimitiveBounds E false suite baggyProdParams ⟨1,2^131,Nat.two_pow_pos 131⟩ (pqQrom256PrimEps qEval)) ∧
      (ExecStatelessEufCmaGame E.pos suite baggyProdParams E.keygen E.adversary).winProb.lt ⟨1,2^128,Nat.two_pow_pos 128⟩ := by
  let H := emptyForgeryBaggyPrimitiveBounds witnessExperiment (fun _ => rfl) ⟨1,2^131,Nat.two_pow_pos 131⟩ (pqQrom256PrimEps 1)
  exact ⟨0, 1, witnessExperiment, signingWitnessSuite, by decide, by decide, ⟨H⟩,
    baggyProd_pq_qrom_exec_euf_cma_lt_2_neg_128 _ _ (by decide) (by decide) H⟩

#verify_constructive inhabited_baggyProd_pq_qrom_exec_euf_cma_lt_2_neg_128
#verify_inhabited baggyProd_pq_qrom_exec_euf_cma_lt_2_neg_128 inhabited_baggyProd_pq_qrom_exec_euf_cma_lt_2_neg_128

theorem inhabited_baggyProd_classical_exec_euf_cma_lt_2_neg_128 :
    ∃ (q qEval : Nat) (E : SigningExperiment q) (suite : TweakableHashSuite),
      q ≤ 2^16 ∧ qEval ≤ 2^80 ∧
      Nonempty (SigningPrimitiveBounds E false suite baggyProdParams ⟨1,2^131,Nat.two_pow_pos 131⟩ (classical256PrimEps qEval)) ∧
      (ExecStatelessEufCmaGame E.pos suite baggyProdParams E.keygen E.adversary).winProb.lt ⟨1,2^128,Nat.two_pow_pos 128⟩ := by
  let H := emptyForgeryBaggyPrimitiveBounds witnessExperiment (fun _ => rfl) ⟨1,2^131,Nat.two_pow_pos 131⟩ (classical256PrimEps 1)
  exact ⟨0, 1, witnessExperiment, signingWitnessSuite, by decide, by decide, ⟨H⟩,
    baggyProd_classical_exec_euf_cma_lt_2_neg_128 _ _ (by decide) (by decide) H⟩

#verify_constructive inhabited_baggyProd_classical_exec_euf_cma_lt_2_neg_128
#verify_inhabited baggyProd_classical_exec_euf_cma_lt_2_neg_128 inhabited_baggyProd_classical_exec_euf_cma_lt_2_neg_128

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

#verify_constructive slhDsaW16StatelessParams_geometry slhDsaW16_pq_qrom_global_slot_budget_lt_2_neg_128

#verify_constructive
  factFast_pos fallingFactFast_zero_left fallingFactFast_succ_left truncBinomFast_pos
  truncBinomFast_eq_spec truncBinom_step fips205Budget_le_cap
  Qsag.pqMultiHopBudget_mono
  Qsag.jortsProd_pq_qrom_budget_lt_2_neg_128
  Qsag.baggySha3_128f_pors_itsr_lt_2_neg_131
  Qsag.binomChoose_mul_factFast
  Qsag.one_sub_pow_mul_truncBinom_le
  Qsag.fips205_interleaved_itsr_128s_128f_bounds
  Qsag.jortsProd_exec_prf_tcr_reduction
  Qsag.baggyProd_exec_prf_tcr_reduction
  Qsag.corduroyProd_exec_prf_tcr_reduction
  Qsag.globalSlotBudget_mono
  Qsag.jortsProd_classical_global_slot_budget_lt_2_neg_128
  Qsag.jortsProd_pq_qrom_global_slot_budget_lt_2_neg_128
  Qsag.baggyProd_classical_global_slot_budget_lt_2_neg_128
  Qsag.baggyProd_pq_qrom_global_slot_budget_lt_2_neg_128
  Qsag.corduroyProd_pq_qrom_global_slot_budget_lt_2_neg_128
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

#tooth_pair Qsag.jortsProd_pq_qrom_global_slot_budget_lt_2_neg_128 vs
  Qsag.tooth_pq_grover_2pow64_exceeds_128bit_bound
#tooth_pair Qsag.baggyProd_pq_qrom_global_slot_budget_lt_2_neg_128 vs
  Qsag.tooth_pq_grover_2pow64_exceeds_128bit_bound
#tooth_pair Qsag.jortsProd_classical_global_slot_budget_lt_2_neg_128 vs
  Qsag.tooth_classical_2pow128_exceeds_128bit_bound
#tooth_pair Qsag.baggyProd_classical_global_slot_budget_lt_2_neg_128 vs
  Qsag.tooth_classical_2pow128_exceeds_128bit_bound
#tooth_pair Qsag.fips205_slhDsa128f_concrete_security_lt_2_neg_128 vs
  Qsag.tooth_fips205_128f_bad_hmsg_rejected

end Qsag
end
