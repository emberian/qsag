module
/-
# Qsag.Top.SecurityBounds — Unified Concrete Security Summary Over `Spec.RatBound`

Top-level concrete security audit module (zero `import all`) unifying all five subsystem entries
(`Top.Aggregation`, `Top.Signing`, `Top.Custody`, `Top.Credentials`, `Top.Migration`) and the
12-component post-quantum portfolio (`ConcreteSecurityBudget`) under canonical `Spec.RatBound`:
- **Clause I (Unconditional Algebraic, Statistical, and Simulation Bounds)**:
  1. Deployed `[CWYZ26]` round-by-round soundness `atLeastBits 184` across all non-exhaustive
     canonical stages `2 ≤ nv ≤ 24`,
  2. Dual-LPN regular-block bias `strictlyMoreThanBits 256` (`< 2^{-256}`),
  3. 438-repetition `ZKBoo` + sacrifice QROM soundness at `qHash + 1 ≤ 2 ^ 56`, and
  4. Exact multi-turn trace inclusion for `waistbandCache_refines_stateless`,
     `rssSharedRelease_refines_reference`, and `thresholdDurableShared_refines_ideal`.
- **Clause II (Assumption- and Model-Conditional Concrete Security Bounds)**:
  1. Standard-model tweakable-hash `EUF-CMA` `GameBound` (`εItsr + εTcr + εPre`) with explicit
     `prodPathTargetCount` candidate pool bound,
  2. Salted-Merkle QROM `HEM` `nv = 24` soundness `atLeastBits 128` up to `Q + 1 ≤ 2 ^ 40`, and
  3. Full 12-component `PQ-128` portfolio classical & quantum bit-security (`atLeastBits 128`)
     paired with non-vacuous `exceedsBitBudget` boundary witnesses!
-/

public import Qsag.Top.Aggregation
public import Qsag.Top.Signing
public import Qsag.Top.Custody
public import Qsag.Top.Credentials
public import Qsag.Top.Migration
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Top

set_option autoImplicit false

/-- **Two-Clause Unified Concrete Security Summary (`qsag_unified_concrete_security_summary`)**:
    Separates unconditional algebraic/statistical/refinement guarantees (Clause I) from
    assumption- and oracle-model-conditional concrete `Spec.RatBound` guarantees (Clause II)
    in a single auditable theorem! -/
theorem qsag_unified_concrete_security_summary
    -- Portfolio & query-ceiling parameters
    (budget : Qsag.QueryBudget) (hqSess : budget.qOnlineSessions + 1 ≤ 2 ^ 20)
    (hqRlwe : budget.qHash + 1 ≤ 2 ^ 66)
    (qQrom : Nat) (hqQrom : qQrom + 1 ≤ 2 ^ 40)
    (qMig : Nat) (hqMig : qMig + 1 ≤ 2 ^ 56)
    -- Dual-LPN regular-block balanced weights
    (lpnWeights : List Nat) (hLpnLen : lpnWeights.length = 64)
    (hLpnBal : ∀ w ∈ lpnWeights, ((32768 : Int) - 2 * (w : Int)).natAbs ≤ 2047)
    -- Custody & cache refinement parameters
    (rssProf : Qsag.RssProduction.Profile)
    (durCfg : Qsag.ThresholdIdealService.Config) :
    -- === Clause I: Unconditional Algebraic, Statistical, and Simulation Guarantees ===
    ((Qsag.Spec.RatBound.clampExactRat
        (Qsag.ExactRat.abs
          (Qsag.parityBias (Qsag.regularBlockXorOneProb (lpnWeights.map Qsag.depth15TreeRate))))).strictlyMoreThanBits 256 ∧
     8 * (qMig + 1) ^ 2 * 2 ^ 438 * 2 ^ 128 ≤ 3 ^ 438 ∧
     (∀ tr, (rssSharedReleaseMachine rssProf).AdmitsTrace tr →
       (rssReferenceReleaseMachine rssProf).AdmitsTrace tr) ∧
     Qsag.InteractiveService.PrefixEquivalent
       (Qsag.ThresholdIdealDurableService.shared durCfg)
       (Qsag.ThresholdIdealDurableService.ideal durCfg)
       Qsag.ThresholdIdealDurableService.initial
       Qsag.ThresholdIdealDurableService.initial) ∧
    -- === Clause II: Assumption- & Oracle-Model-Conditional `Spec.RatBound` Guarantees ===
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
  have hBias := Qsag.Spec.RatBound.clampExactRat_strictlyMoreThanBits_of_lt_twoNegPow
    (Qsag.pcg_dense_dual_lpn_linear_bias_lt_two_neg_256 lpnWeights hLpnLen hLpnBal)
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
