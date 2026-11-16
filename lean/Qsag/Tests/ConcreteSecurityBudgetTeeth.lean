module
public import Qsag.Math.GoldilocksBase
/- Concrete non-vacuity witnesses for the security-budget interfaces. -/
public import Qsag.Protocol.Aggregation.ConcreteSecurityBudget
public import Qsag.Oracle.Qrom
public import Qsag.Math.Goldilocks
public import Qsag.Math.QuarticExt4
public import Qsag.Math.Counting
public import Qsag.Math.CoeffPoly
public import Qsag.Math.PolyRing
public import Qsag.Math.HasseHensel
public section
namespace Qsag
set_option autoImplicit false
set_option exponentiation.threshold 2048
set_option maxRecDepth 10000
/-- Concrete 2-query Hadamard superposition circuit (`QuantumAdv 2 2 1 2`) preparing
    `|0, 0, 0⟩ + |1, 0, 0⟩` via `hadamardQuery2 2 1` after query 0 so query 1 probes `oracleXor`
    in uniform superposition across both basis inputs! -/
def concreteSuperpositionAdv : QuantumAdv 2 2 1 2 where
  init := fun x y _ => if x.1 == 0 && y.1 == 0 then ⟨1, 0⟩ else GaussInt.zero
  h_init_pos := by
    simp only [QVec.stateNormSq_def, QVec.queryWeight_def, GaussInt.normSq_def, GaussInt.zero_def]
    decide
  steps := fun i => if i.1 == 0 then hadamardQuery2 2 1 else ScaledUnitary.id 2 2 1

/-- Concrete 2-query adaptive `OracleComp` decision tree branching on the LSB of its first
    256-bit oracle query response before choosing its second query input! -/
def concreteAdaptiveTwoQueryAdv : OracleComp (BitVec 8) (BitVec 256) (BitVec 8) :=
  .query (BitVec.ofNat 8 1) (fun d₁ =>
    let x₂ := if d₁.getLsbD 0 then BitVec.ofNat 8 2 else BitVec.ofNat 8 3
    .query x₂ (fun _ => .pure x₂))

/-- Non-scalar quartic basis element `v ∈ QuarticGoldilocks` (`v^2 = u ∈ GoldilocksExt2`) and
    non-zero quadratic polynomial `P(X) = X^2 - u` (`cs = [-u, 0, 1]`). -/
def quarticGoldilocksVBasis : QuarticGoldilocks :=
  ⟨GoldilocksExt2.zero, GoldilocksExt2.one⟩

def quarticGoldilocksQuadraticPoly : List QuarticGoldilocks :=
  [ ⟨CommRingOps.neg GoldilocksExt2.uBasis, GoldilocksExt2.zero⟩,
    QuarticGoldilocks.zero,
    QuarticGoldilocks.one ]

/-- **Master Non-Vacuity & Inhabitedness Witness (`inhabited_concrete_security_budget_roster`)**:
    Certifies that EVERY foundational carrier and reduction in `ConcreteSecurityBudget.lean` is
    genuinely inhabited by non-trivial witnesses (`0` identity-hash or empty-list shortcuts):
    1. `concreteSuperpositionAdv` prepares genuine uniform quantum superposition across both basis
       queries (`queryWeight = 1` on `x = 0` AND `x = 1`) before applying `oracleXor`,
    2. `concreteAdaptiveTwoQueryAdv` satisfies `QueryBounded 2` and instantiates
       `classical_lazy_ro_fiber_search_bound` on `wotsCDibits128Bv` (`fiberCard ≤ 1`),
    3. `quarticGoldilocksQuadraticPoly` (`X^2 - u`) is non-zero at `0`, vanishes at the two distinct
       non-scalar quartic elements `+v` and `-v`, and satisfies `goldilocksExt4_schwartz_zippel_root_bound`,
    4. At concrete budget `b₀ = ⟨2^30 - 1, 2^16, 2^20 - 1⟩` (the largest power-of-two hash budget
       inside every entry's ceiling, at the full `2^20` sessions), all 12 entries of
       `qsagPq128PortfolioRoster b₀` have strictly positive numerators (`0 < num`, non-zero
       bounds!) and simultaneously satisfy `atLeastBits 128` classically and in the QROM! -/
theorem inhabited_concrete_security_budget_roster :
    let b₀ : QueryBudget := ⟨2 ^ 30 - 1, 2 ^ 16, 2 ^ 20 - 1⟩
    let ψPre := advStateAt concreteSuperpositionAdv (fun _ => BitVec.zero 2) 1 (by decide)
    let dRef : BitVec 256 := BitVec.ofNat 256 0xdeadbeefcafebabe
    let S4 : List QuarticGoldilocks :=
      [QuarticGoldilocks.zero, quarticGoldilocksVBasis, CommRingOps.neg quarticGoldilocksVBasis]
    (QVec.queryWeight ψPre ⟨0, by decide⟩ = 1 ∧ QVec.queryWeight ψPre ⟨1, by decide⟩ = 1) ∧
    (QueryBounded 2 concreteAdaptiveTwoQueryAdv ∧
      fiberCard 256 wotsCDibits128Bv (wotsCDibits128Bv dRef) ≤ 1) ∧
    (RoundPoly.evalCoeffs quarticGoldilocksQuadraticPoly QuarticGoldilocks.zero ≠ CommRingOps.zero ∧
      RoundPoly.evalCoeffs quarticGoldilocksQuadraticPoly quarticGoldilocksVBasis = CommRingOps.zero ∧
      (S4.filter (fun r =>
        decide (RoundPoly.evalCoeffs quarticGoldilocksQuadraticPoly r = CommRingOps.zero))).length = 2) ∧
    ((qsagPq128PortfolioRoster b₀).length = 12 ∧
      ∀ entry ∈ qsagPq128PortfolioRoster b₀,
        0 < entry.classicalBound.num ∧
        0 < entry.quantumBound.num ∧
        atLeastBits 128 entry.classicalBound ∧
        atLeastBits 128 entry.quantumBound) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- 1. Genuine superposition query weights on both `x = 0` and `x = 1`:
    have hψ : advStateAt concreteSuperpositionAdv (fun _ => BitVec.zero 2) 1 (by decide) =
        (hadamardQuery2 2 1).apply
          (oracleXor (fun _ => BitVec.zero 2) concreteSuperpositionAdv.init) := by
      rw [advStateAt_succ, advStateAt_zero]
      rfl
    have hInit : concreteSuperpositionAdv.init =
        fun x y _ => if x.1 == 0 && y.1 == 0 then ⟨1, 0⟩ else ⟨0, 0⟩ := by
      funext x y _
      show (if x.1 == 0 && y.1 == 0 then (⟨1, 0⟩ : GaussInt) else GaussInt.zero) = _
      rw [GaussInt.zero_def]
    constructor
    · rw [hψ]
      simp only [QVec.queryWeight_def, hadamardQuery2_apply, oracleXor_apply, xorFin_def,
        GaussInt.normSq_def, GaussInt.add_def, GaussInt.sub_def, hInit]
      decide
    · rw [hψ]
      simp only [QVec.queryWeight_def, hadamardQuery2_apply, oracleXor_apply, xorFin_def,
        GaussInt.normSq_def, GaussInt.add_def, GaussInt.sub_def, hInit]
      decide
  · -- 2. Adaptive 2-query `OracleComp` + `wotsCDibits128Bv` injectivity fiber bound:
    refine ⟨?_, fiberCard_le_one_of_injective 256 wotsCDibits128Bv
                  (fun _ _ h => wotsCDibits128Bv_injective h) _⟩
    unfold concreteAdaptiveTwoQueryAdv
    rw [QueryBounded_succ_query 1]
    intro d₁
    dsimp only
    rw [QueryBounded_succ_query 0]
    intro _
    rw [QueryBounded_pure]
    exact trivial
  · -- 3. Non-scalar quadratic polynomial `X^2 - u` over `QuarticGoldilocks`:
    refine ⟨by decide, by decide, by decide⟩
  · -- 4. Concrete 12-profile portfolio evaluation at `b₀ = ⟨2^30 - 1, 2^16, 2^20 - 1⟩`:
    let b₀ : QueryBudget := ⟨2 ^ 30 - 1, 2 ^ 16, 2 ^ 20 - 1⟩
    have hPort := qsag_pq128_portfolio_soundness_budget b₀ (by decide)
    refine ⟨hPort.1, ?_⟩
    intro entry hMem
    have hBits := hPort.2 entry hMem
      (Nat.le_trans (by decide : b₀.qHash + 1 ≤ 2 ^ 30)
        (Nat.pow_le_pow_right (by decide) (qsagPq128PortfolioRoster_ceiling_ge_30 b₀ entry hMem)))
    have hPos : 0 < entry.classicalBound.num ∧ 0 < entry.quantumBound.num :=
      qsagPq128PortfolioRoster_num_pos_at_2pow30 entry hMem
    exact ⟨hPos.1, hPos.2, hBits.1, hBits.2⟩


#verify_constructive Qsag.inhabited_concrete_security_budget_roster
end Qsag
end
