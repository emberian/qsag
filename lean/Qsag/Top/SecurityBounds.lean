module
/-
# Qsag.Top.SecurityBounds — Unified Concrete Security Summary Over `Spec.RatBound`

Top-level summary module (zero `import all`) collecting, under the canonical `Spec.RatBound`, the
statement `qsag_unified_concrete_security_summary`. It has three clauses, and they are three
different kinds of statement.

- **Clause I (facts with no cryptographic hypothesis)**:
  1. The production tap-row parity bias lies strictly between `2^{-118}` and `2^{-117}`,
     from the exact heterogeneous 64-block calculation in `Math/TapRowParityBias`.
  2. The arithmetic inequality `8 (q+1)^2 2^438 2^128 ≤ 3^438` behind the 438-repetition ZKBoo
     count, for `q + 1 ≤ 2^56`.
  3. The dichotomy of the authenticated custodian network of `Top.Custody`, Section 9: every
     execution of `DistCustody.authMachine` (a `Fin n` family of custodians with sealed WAL
     records, tagged acknowledgements and an adversarial wire and disk) projects to an execution
     of `Spec.idealCustodyMachine`, or exhibits a tag forgery, a message-tag collision or a hash
     collision. This is a disjunction; it assigns no probability to the last three alternatives.
     Its hypotheses are the deployment conditions `AuthDeployment.WellFormed`.
- **Clause II (arithmetic on bound formulas)**: the 12-entry portfolio roster and the RLWE
  OR-sigma and HEM `nv = 24` QROM compiler bound formulas evaluate to at most `2^{-128}` within the
  stated query ceilings. These are evaluations of closed-form expressions. This clause takes no
  hardness or oracle-model hypothesis and does not show that any protocol's adversarial advantage
  is bounded by them.
- **Clause III (bounds on events, conditional on stated assumptions)**: two reductions over an
  arbitrary finite coin space, each of the form "if the named extractor events have probability
  at most `ε₁, …`, and `ε₁ + …` is at most `2^{-128}`, then the bad event has probability at most
  `2^{-128}`".
  1. Custody: the bad event is an unsafe release by the authenticated custodian network (the
     coordinator's WAL holds a release no enrolled custodian approved); the assumed events are an
     acknowledgement violation (a tag forgery under an uncorrupted custodian's key, or a
     message-tag collision) and a WAL violation (a hash collision).
  2. Signing: the bad event is `prodEufCmaWin` of the production hash-based signature; the assumed
     events are the three extractor events `prodItsrEvent`, `prodTcrEvent`, `prodPreEvent`.
  The `ε` hypotheses are assumptions about the run. Nothing in this library bounds them, and they
  are not the standard-model experiments of `Spec.Assumptions`.

Not conjuncts of the summary: the closed EUF-CMA bound by adversaries that see only the public key
and the oracles (`Top.ClosedProtocolReductions`), the `[CWYZ26]` stage budget (`Top.Aggregation`)
and the separated-custody forgery bound (`Top.separatedCustody_forgery_eufCma_gameBound`).

The platform-contract instances for the real storage, GPU and constant-time models
(`Exec.PlatformContractInstances`, `Machine.PlatformContractInstances`) are re-exported here; no
clause of the summary theorem below consumes a platform contract. One of them,
`Machine.nttStageAddressModel`, is not built from a kernel: the Machine layer has no instruction
stream for `goldilocks_ntt.comp`, so its block traces are empty and its access sets are written by
hand from the address formulas.
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

/-- **Three-clause summary (`qsag_unified_concrete_security_summary`)**: Clause I collects facts
    with no cryptographic hypothesis; Clause II evaluates bound formulas at the stated query
    ceilings; Clause III states two event bounds, each conditional on explicit bounds for named
    extractor events. The module header says what each clause does and does not claim. -/
theorem qsag_unified_concrete_security_summary
    -- Portfolio & query-ceiling parameters
    (budget : Qsag.QueryBudget) (hqSess : budget.qOnlineSessions + 1 ≤ 2 ^ 20)
    (hqRlwe : budget.qHash + 1 ≤ 2 ^ 66)
    (qQrom : Nat) (hqQrom : qQrom + 1 ≤ 2 ^ 40)
    (qMig : Nat) (hqMig : qMig + 1 ≤ 2 ^ 56) :
    -- === Clause I: facts with no cryptographic hypothesis ===
    ((Qsag.TapRowBias.imbalanceProd 32768 Qsag.TapRowBias.prodRow0Weights * 2 ^ 117 < 32768 ^ 64 ∧
      32768 ^ 64 < Qsag.TapRowBias.imbalanceProd 32768 Qsag.TapRowBias.prodRow0Weights * 2 ^ 118) ∧
     8 * (qMig + 1) ^ 2 * 2 ^ 438 * 2 ^ 128 ≤ 3 ^ 438 ∧
     (∀ (F C PK D Sig : Type) [Qsag.LawfulField F] [DecidableEq F] [DecidableEq C]
        [DecidableEq D] (dep : Qsag.DistCustody.AuthDeployment F C PK D Sig),
        dep.WellFormed →
        ∀ tr : List (Qsag.DistCustody.AuthTurn F dep.core.quorum.numParties ×
            Qsag.DistCustody.AuthEvent F Sig),
          (Qsag.DistCustody.authMachine dep).AdmitsTrace tr →
          (Qsag.Spec.idealCustodyMachine dep.core.digests dep.core.idealOracle
              dep.core.deploymentId dep.core.pk dep.core.quorum).AdmitsTrace
              (Qsag.Spec.projectTrace (Qsag.DistCustody.authVisIn dep)
                Qsag.DistCustody.authVisOut tr) ∨
          (∃ (st : Qsag.DistCustody.AuthState F PK D Sig dep.core.quorum.numParties)
              (m : Qsag.DistCustody.AuthAck F),
            (Qsag.DistCustody.authGuardedMachine dep).Reachable st ∧
              Qsag.DistCustody.AckMacForgery dep st m) ∨
          Qsag.DistCustody.MsgTagCollision dep ∨ Nonempty (Qsag.HashCollision256 dep.hash))) ∧
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
         (Qsag.hemOptimizedQueryBounds .unitaryPow16 24))).atLeastBits 128) ∧
    -- === Clause III: event bounds conditional on bounds for named extractor events ===
    ((∀ (F C PK D Sig : Type) [Qsag.LawfulField F] [DecidableEq F] [DecidableEq C]
        [DecidableEq D] (N : Nat) (hN : 0 < N)
        (dep : Fin N → Qsag.DistCustody.AuthDeployment F C PK D Sig)
        (adv : (ω : Fin N) →
          List (Qsag.DistCustody.AuthTurn F (dep ω).core.quorum.numParties))
        (εAck εWal : Qsag.Spec.RatBound),
        (∀ ω, (dep ω).WellFormed) →
        Qsag.Spec.GameBound
          (Qsag.Spec.FinGame.mk hN (fun ω =>
            (Qsag.DistCustody.authRun (dep ω) (Qsag.DistCustody.authAckViolation (dep ω))
              (Qsag.DistCustody.AuthState.init (dep ω)) (adv ω)).2)).winProb εAck →
        Qsag.Spec.GameBound
          (Qsag.Spec.FinGame.mk hN (fun ω =>
            (Qsag.DistCustody.authRun (dep ω) (Qsag.DistCustody.authWalViolation (dep ω))
              (Qsag.DistCustody.AuthState.init (dep ω)) (adv ω)).2)).winProb εWal →
        (εAck.add εWal).atLeastBits 128 →
        (Qsag.Spec.FinGame.mk hN (fun ω => Qsag.DistCustody.authUnsafeRelease (dep ω)
          (Qsag.DistCustody.authRun (dep ω) (Qsag.DistCustody.authViolation (dep ω))
            (Qsag.DistCustody.AuthState.init (dep ω)) (adv ω)).1)).winProb.atLeastBits 128) ∧
     (∀ (n : Nat) (hPos : 0 < n) (suite : Qsag.TweakableHashSuite) (params : Qsag.PqHashParams)
        (hw : params.w = 4 ∨ params.w = 16) (game : Fin n → Qsag.ProdEufCmaOutcome)
        (hOneTime : ∀ ω : Fin n, params.statefulJorts = true →
          ∀ q, q ∈ (game ω).queries → ∀ q', q' ∈ (game ω).queries → q.epoch = q'.epoch → q = q')
        (εItsr εTcr εPre : Qsag.Spec.RatBound),
        Qsag.Spec.GameBound
          (Qsag.Spec.FinGame.mk hPos (fun ω =>
            Qsag.prodItsrEvent suite params hw (game ω) (hOneTime ω))).winProb εItsr →
        Qsag.Spec.GameBound
          (Qsag.Spec.FinGame.mk hPos (fun ω =>
            Qsag.prodTcrEvent suite params hw (game ω) (hOneTime ω))).winProb εTcr →
        Qsag.Spec.GameBound
          (Qsag.Spec.FinGame.mk hPos (fun ω =>
            Qsag.prodPreEvent suite params hw (game ω) (hOneTime ω))).winProb εPre →
        ((εItsr.add εTcr).add εPre).atLeastBits 128 →
        (Qsag.Spec.FinGame.mk hPos (fun ω =>
          Qsag.prodEufCmaWin suite params (game ω))).winProb.atLeastBits 128)) := by
  -- Clause I
  have hBias := Qsag.TapRowBias.prodRow0_bias_bracket
  obtain ⟨hMigQrom, _⟩ := Qsag.MigrationExecution.migration_438_zkboo_and_ceremony_qrom_soundness qMig hqMig
  -- Clause II
  obtain ⟨hPortLen, hPortEntries⟩ := Qsag.qsag_pq128_portfolio_soundness_budget budget hqSess
  obtain ⟨hRlweC, hRlweQ⟩ := Qsag.rlwe_or_sigma_24_pq128_within_ceiling budget hqRlwe
  obtain ⟨_, hHemPow⟩ := Qsag.hemNv24_unitaryPow16_sound_up_to_2pow40 qQrom hqQrom
  refine ⟨⟨hBias, hMigQrom, ?_⟩, ⟨hPortLen, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro F C PK D Sig _ _ _ _ dep hWf tr hAdmits
    exact authenticatedCustody_ideal_or_forgery dep hWf hAdmits
  · intro entry hMem hCeil
    obtain ⟨hc, hq⟩ := hPortEntries entry hMem hCeil
    exact ⟨(Qsag.Spec.RatBound.ofBudget_atLeastBits_iff 128 _).mpr hc,
           (Qsag.Spec.RatBound.ofBudget_atLeastBits_iff 128 _).mpr hq⟩
  · exact (Qsag.Spec.RatBound.ofBudget_atLeastBits_iff 128 _).mpr hRlweC
  · exact (Qsag.Spec.RatBound.ofBudget_atLeastBits_iff 128 _).mpr hRlweQ
  · exact (Qsag.Spec.RatBound.ofBudget_atLeastBits_iff 128 _).mpr hHemPow
  -- Clause III
  · intro F C PK D Sig _ _ _ _ N hN dep adv εAck εWal hWf hAck hWal hBits
    exact (authenticatedCustody_unsafe_release_bound hN dep hWf adv εAck εWal hAck hWal).2 128
      hBits
  · intro n hPos suite params hw game hOneTime εItsr εTcr εPre hItsr hTcr hPre hBits
    exact Qsag.Spec.GameBound.atLeastBits
      (production_euf_cma_gameBound hPos suite params hw game hOneTime εItsr εTcr εPre
        hItsr hTcr hPre).1 hBits

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
