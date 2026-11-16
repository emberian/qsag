module
/-
# Qsag.Top.SecurityBounds — Unified Concrete Security Summary Over `Spec.RatBound`

Top-level summary module (zero `import all`) collecting, under the canonical `Spec.RatBound`, the
statement `qsag_unified_concrete_security_summary`. What that theorem states, exactly:
- **Clause I (facts with no cryptographic hypothesis)**:
  1. The production tap-row parity bias lies strictly between `2^{-118}` and `2^{-117}`,
     from the exact heterogeneous 64-block calculation in `Math/TapRowParityBias`.
  2. The arithmetic inequality `8 (q+1)^2 2^438 2^128 ≤ 3^438` behind the 438-repetition ZKBoo count,
     for `q + 1 ≤ 2^56`.
  3. Trace inclusion of the RSS shared-release machine in its reference machine, and prefix equivalence
     of the durable threshold service with its ideal.
- **Clause II (arithmetic on bound formulas)**: the 12-entry portfolio roster and the RLWE OR-sigma and
  HEM `nv = 24` QROM compiler bound formulas evaluate to at most `2^{-128}` within the stated query
  ceilings. These are evaluations of closed-form expressions; the theorem takes no hardness or
  oracle-model hypothesis and does not show that any protocol's adversarial advantage is bounded by
  them.
The EUF-CMA event bound (`Top.Signing.production_euf_cma_gameBound`), the `[CWYZ26]` stage budget
(`Top.Aggregation`) and the waistband-cache refinement (`Top.Custody`) are separate theorems in the
imported modules and are not conjuncts of the summary.

The platform-contract instances for the real storage, GPU and constant-time models
(`Exec.PlatformContractInstances`, `Machine.PlatformContractInstances`) are re-exported here; no
clause of the summary theorem below consumes a platform contract.
-/

public import Qsag.Math.TapRowParityBias
public import Qsag.Top.Aggregation
public import Qsag.Exec.RefinesBridges
public import Qsag.Oracle.SpecRatBridges
public import Qsag.Top.Signing
public import Qsag.Top.Custody
public import Qsag.Top.Credentials
public import Qsag.Top.Migration
public import Qsag.Exec.PlatformContractInstances
public import Qsag.Machine.PlatformContractInstances
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Top

set_option autoImplicit false

/-- **Two-clause summary (`qsag_unified_concrete_security_summary`)**: Clause I collects facts with no
    cryptographic hypothesis; Clause II evaluates
    bound formulas at the stated query ceilings. See the module header for what is not claimed. -/
theorem qsag_unified_concrete_security_summary
    -- Portfolio & query-ceiling parameters
    (budget : Qsag.QueryBudget) (hqSess : budget.qOnlineSessions + 1 ≤ 2 ^ 20)
    (hqRlwe : budget.qHash + 1 ≤ 2 ^ 66)
    (qQrom : Nat) (hqQrom : qQrom + 1 ≤ 2 ^ 40)
    (qMig : Nat) (hqMig : qMig + 1 ≤ 2 ^ 56)
    -- Custody & cache refinement parameters
    (rssProf : Qsag.RssProduction.Profile)
    (durCfg : Qsag.ThresholdIdealService.Config) :
    -- === Clause I: Unconditional Algebraic, Statistical, and Simulation Guarantees ===
    ((Qsag.TapRowBias.imbalanceProd 32768 Qsag.TapRowBias.prodRow0Weights * 2 ^ 117 < 32768 ^ 64 ∧
      32768 ^ 64 < Qsag.TapRowBias.imbalanceProd 32768 Qsag.TapRowBias.prodRow0Weights * 2 ^ 118) ∧
     8 * (qMig + 1) ^ 2 * 2 ^ 438 * 2 ^ 128 ≤ 3 ^ 438 ∧
     (∀ tr, (rssSharedReleaseMachine rssProf).AdmitsTrace tr →
       (rssReferenceReleaseMachine rssProf).AdmitsTrace tr) ∧
     Qsag.InteractiveService.PrefixEquivalent
       (Qsag.ThresholdIdealDurableService.shared durCfg)
       (Qsag.ThresholdIdealDurableService.ideal durCfg)
       Qsag.ThresholdIdealDurableService.initial
       Qsag.ThresholdIdealDurableService.initial) ∧
    -- === Clause II: evaluations of bound formulas within the query ceilings ===
    ((Qsag.qsagPq128PortfolioRoster budget).length = 12 ∧
     (∀ entry ∈ Qsag.qsagPq128PortfolioRoster budget,
       budget.qHash + 1 ≤ 2 ^ entry.pq128HashQueryCeilingLog2 →
       (Qsag.Spec.RatBound.ofBudget entry.classicalBound).atLeastBits 128 ∧
       (Qsag.Spec.RatBound.ofBudget entry.quantumBound).atLeastBits 128) ∧
     (Qsag.Spec.RatBound.ofBudget
       (Qsag.classicalFiatShamirBound budget.qHash (Qsag.rlweOrSigmaSoundnessError 24))).atLeastBits 128 ∧
     (Qsag.Spec.RatBound.ofBudget
       (Qsag.quantumGroverGrindingBound budget.qHash (Qsag.rlweOrSigmaSoundnessError 24))).atLeastBits 128 ∧
     (Qsag.Spec.RatBound.ofBudget
       (Qsag.powScaledFsQromCompilerBound qQrom 5 256 16
         Qsag.hemV6FiveRoundRbrBounds
         (Qsag.hemOptimizedQueryBounds .unitaryPow16 24))).atLeastBits 128) := by
  -- Clause I
  have hBias := Qsag.TapRowBias.prodRow0_bias_bracket
  obtain ⟨hMigQrom, _⟩ := Qsag.MigrationExecution.migration_438_zkboo_and_ceremony_qrom_soundness qMig hqMig
  have hRssTr : ∀ tr, (rssSharedReleaseMachine rssProf).AdmitsTrace tr →
      (rssReferenceReleaseMachine rssProf).AdmitsTrace tr :=
    fun _ h => rssSharedRelease_preserves_traces rssProf h
  let refDur := thresholdDurableShared_refines_ideal durCfg
  obtain ⟨hAbsDur, _⟩ := refDur.init_ok (rfl : Qsag.ThresholdIdealDurableService.initial = _)
  have hPrefDur : Qsag.InteractiveService.PrefixEquivalent
      (Qsag.ThresholdIdealDurableService.shared durCfg)
      (Qsag.ThresholdIdealDurableService.ideal durCfg)
      Qsag.ThresholdIdealDurableService.initial
      Qsag.ThresholdIdealDurableService.initial := by
    have hP := Qsag.Spec.Refines.toInteractivePrefixEquivalent refDur rfl
    rw [hAbsDur] at hP
    exact hP
  -- Clause II
  obtain ⟨hPortLen, hPortEntries⟩ := Qsag.qsag_pq128_portfolio_soundness_budget budget hqSess
  obtain ⟨hRlweC, hRlweQ⟩ := Qsag.rlwe_or_sigma_24_pq128_within_ceiling budget hqRlwe
  obtain ⟨_, hHemPow⟩ := Qsag.hemNv24_unitaryPow16_sound_up_to_2pow40 qQrom hqQrom
  refine ⟨⟨hBias, hMigQrom, hRssTr, hPrefDur⟩, ⟨hPortLen, ?_, ?_, ?_, ?_⟩⟩
  · intro entry hMem hCeil
    obtain ⟨hc, hq⟩ := hPortEntries entry hMem hCeil
    exact ⟨(Qsag.Spec.RatBound.ofBudget_atLeastBits_iff 128 _).mpr hc,
           (Qsag.Spec.RatBound.ofBudget_atLeastBits_iff 128 _).mpr hq⟩
  · exact (Qsag.Spec.RatBound.ofBudget_atLeastBits_iff 128 _).mpr hRlweC
  · exact (Qsag.Spec.RatBound.ofBudget_atLeastBits_iff 128 _).mpr hRlweQ
  · exact (Qsag.Spec.RatBound.ofBudget_atLeastBits_iff 128 _).mpr hHemPow

/-- **Sharp Query-Ceiling Sensitivity Witness (`securityBounds_sharp_query_ceiling_sensitivity`)**:
    Certifies that `Spec.RatBound.atLeastBits 128` is non-vacuous and mutation-sensitive:
    1. Under the fallacious linear state-restoration query schedule at `Q = 2 ^ 40 - 1`, the
       `HEM` QROM bound strictly exceeds `2^{-128}` (`exceedsBitBudget 128` and `¬ atLeastBits 128`), and
    2. Raw unsalted CDHZ Merkle partition at `Q = 2 ^ 39` strictly fails `atLeastBits 128`! -/
theorem securityBounds_sharp_query_ceiling_sensitivity :
    (∃ Q : Nat, Q = 2 ^ 40 - 1 ∧
      (Qsag.Spec.RatBound.ofBudget
        (Qsag.powScaledFsQromCompilerBound Q 5 256 16
          Qsag.hemV6FiveRoundRbrBounds Qsag.hemNv24LinearSrFallacyQueryBounds)).exceedsBitBudget 128 ∧
      ¬ (Qsag.Spec.RatBound.ofBudget
        (Qsag.powScaledFsQromCompilerBound Q 5 256 16
          Qsag.hemV6FiveRoundRbrBounds Qsag.hemNv24LinearSrFallacyQueryBounds)).atLeastBits 128) ∧
    ¬ (Qsag.Spec.RatBound.ofBudget
      (Qsag.cdhzSnargPartitionBound (2 ^ 39) (2 ^ 38) (2 ^ 38) 426 20 256 16
        Qsag.hemV6FiveRoundRbrBounds
        (Qsag.hemOptimizedQueryBounds .cdhzPow16At2pow38 24))).atLeastBits 128 := by
  obtain ⟨Q, hQEq, hNotAtLeast, hExceeds⟩ := Qsag.tooth_linear_sr_query_schedule_unsound_in_qrom
  have hCdhzFail := Qsag.tooth_cdhz_raw_merkle_fails_at_2pow39
  refine ⟨⟨Q, hQEq, ?_, ?_⟩, ?_⟩
  · exact (Qsag.Spec.RatBound.ofBudget_exceedsBitBudget_iff 128 _).mpr hExceeds.1
  · intro hAt
    exact hNotAtLeast ((Qsag.Spec.RatBound.ofBudget_atLeastBits_iff 128 _).mp hAt)
  · intro hAt
    exact hCdhzFail ((Qsag.Spec.RatBound.ofBudget_atLeastBits_iff 128 _).mp hAt)

#verify_constructive
  Qsag.Top.qsag_unified_concrete_security_summary
  Qsag.Top.securityBounds_sharp_query_ceiling_sensitivity

end Qsag.Top
end
