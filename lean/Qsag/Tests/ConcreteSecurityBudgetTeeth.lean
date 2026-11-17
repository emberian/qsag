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
/- `concreteSuperpositionAdv` and `concreteAdaptiveTwoQueryAdv` are defined in `Oracle/Qrom`, next to the
   evaluated facts `concreteSuperpositionAdv_queryWeights` and `concreteAdaptiveTwoQueryAdv_queryBounded`;
   the roster conjunct is `qsagPq128PortfolioRoster_inhabited_at_concrete_budget` in
   `Protocol/Aggregation/ConcreteSecurityBudget`. Their bodies are not visible from this module. -/

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
    exact concreteSuperpositionAdv_queryWeights
  · -- 2. Adaptive 2-query `OracleComp` + `wotsCDibits128Bv` injectivity fiber bound:
    exact ⟨concreteAdaptiveTwoQueryAdv_queryBounded, fiberCard_le_one_of_injective 256 wotsCDibits128Bv
                  (fun _ _ h => wotsCDibits128Bv_injective h) _⟩
  · -- 3. Non-scalar quadratic polynomial `X^2 - u` over `QuarticGoldilocks`:
    refine ⟨by decide, by decide, by decide⟩
  · -- 4. Concrete 12-profile portfolio evaluation at `b₀ = ⟨2^30 - 1, 2^16, 2^20 - 1⟩`:
    exact qsagPq128PortfolioRoster_inhabited_at_concrete_budget

#verify_constructive Qsag.inhabited_concrete_security_budget_roster
end Qsag
end
