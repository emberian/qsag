module
/-
# Qsag.Protocol.Aggregation.ClosedWhirSchedule — WHIR verifier schedule, Johnson list size, schedule-derived QROM error

* `WhirStage`, `WhirVerifierSchedule`: per-stage folding factor, rate, OOD and query counts,
  agreement `A / n = 1 - δ`, Johnson slack `η = etaNum / etaDen` and list size `L`.
  `WhirStage.johnsonOk` decides `(1 - δ) > √ρ + η` (as `(A/n - η)² > d/n`, `ρ = d/n`) and that
  `L = ⌈1 / (2 η √ρ)⌉`.
* `WhirStage.johnson_list_le`: under `johnsonOk`, `n·d < A²` and the integer Johnson bound
  `n(A - d) / (A² - n·d)` is at most `L`. `WhirStage.decode_list_le`: hence every
  Guruswami–Sudan decode list `gsDecodeList d A D word` over an `n`-point domain has at most
  `L` elements.
* `whirOracleIop`: the executable multi-round verifier as an `OracleIop`: sumcheck round
  consistency, OOD answers, coset reads of the stage oracle folded with the round challenges,
  the terminal polynomial's degree and its agreement with OOD answers and folded reads.
* `scheduleQromError sched Q`: a fold over `sched.stages`, each round scaled by `(2Q+1)²`:
  fold rounds `(L·d* + mca) / q`, OOD `C(L,2)·d^s / q^s`, shift queries
  `((A + k)/n)^t + L·(t + s)/q`.
* `whir_exec_closed_qrom_soundness`: `ClosedFs.exec_fs_qrom_closed_soundness` at this verifier,
  with the bound `scheduleQromError sched Q` plus the collision-finder mass.
* `deployedSched`: the `nv = 24` `unitaryZeroPow` stages read from
  `hemOptimizedStageWitnesses`; `deployedSched_error_at_2pow40`.

What is proved and what is assumed about `WhirScheduleCert`:
* Constructed (§5): `sampledQueryCert`, a certificate for a one-stage schedule over a four-point
  domain whose single query position is the round challenge. Its verifier accepts honest proofs
  (`sampledQuery_honest_accepts`), a false statement is accepted on at most two of four
  challenges and on at least one (`sampledQuery_query_round_flips`,
  `sampledQuery_false_statement_accepted_once`), and the flip count is covered by the stage's
  shift-query bound. The schedule has no fold, sumcheck or out-of-domain round, so those bounds
  are not exercised, and its `scheduleQromError` is above one.
* Constructed (§5b): `flatHemSlicedCert`, an unconditional multi-stage (`2` stages, `6` rounds)
  certificate for `flatHemSlicedSched` (`64 → 32 → 16` coset chain over `QuarticGoldilocks`,
  challenge pool `q = 2^62`, Fiat–Shamir digest width `w = 256`) exercising fold/sumcheck,
  out-of-domain, and shift-query rounds using **strictly proved `[CWYZ26]` sliced MCA counts**
  (`sliced_singleStep_bridge_four_challenge_bound`, `WhirStage.decode_list_le`), accepting honest
  proofs (`flatHemSliced_honest_accepts`), rejecting false statements outside `whirInLang`
  (`flatHemSliced_false_not_inLang`) with `scheduleQromError flatHemSlicedSched 0 ≤ 2^-20 < 1`
  (`flatHemSlicedSched_error_bits`).
* Succinct Merkle-root-and-opening QROM soundness (§3b): `whirSuccinctBridge` and
  `whir_succinct_closed_qrom_soundness` lift wire-transmitted Merkle roots and authentication
  paths through `ClosedFs.succinct_fs_qrom_closed_soundness` with explicit `MerkleCollision`
  extraction (`succinctFsCollisionEvent`).
* Assumed: a certificate for `deployedSched`. `deployed_whir_exec_closed_qrom_128` takes
  `(sc : WhirScheduleCert env deployedSched w)` as a hypothesis and no such certificate is
  constructed for `deployedSched` (`nv = 24`). In addition `deployedStages` uses the profile input
  `mcaNum := whirAffineStageSimpleNum`, which the proved sliced MCA counts of
  `Cwyz26EqualDegreeAndMultiFold` do not reach. The `2^-128` statement for the `nv = 24` deployed
  schedule remains conditional on both.
-/

public import Qsag.Protocol.Aggregation.ClosedFsQromCompile
public import Qsag.Protocol.Aggregation.Cwyz26EqualDegreeAndMultiFold
public import Qsag.Protocol.Aggregation.HemMultistageCascadeRbr
public import Qsag.Protocol.Aggregation.QromSaltedMerkleStateRestoration
import Qsag.Math.Counting
import Qsag.Math.CoeffPoly
import Qsag.Math.PolyRing
import Qsag.Math.HasseHensel
import Qsag.Math.GoldilocksBase
import Qsag.Math.Tactic.CommRing
import Qsag.Coding.GuruswamiSudan
import Qsag.Coding.ReedSolomon
import Qsag.Coding.AffineProximity
import Qsag.Protocol.Aggregation.HemRbrSoundness
import Qsag.Protocol.Aggregation.MultiRoundFsQrom
import Qsag.Protocol.Aggregation.ConcreteSecurityBudget
import Qsag.Coding.Cwyz26
import Qsag.Protocol.Aggregation.HemOpening
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.ClosedWhir

open Qsag.ClosedFs

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 100000

/-! ## §1. Stages, the Johnson condition and the list size -/

/-- One WHIR stage. The folded evaluation domain has `n = 2^logDomain` fibers and the stage
    oracle `n · 2^foldK` points; `degBound = d` bounds the agreement of two distinct candidates,
    `agree = A` is the agreement threshold `(1 - δ) n`, `η = etaNum / etaDen`. -/
structure WhirStage where
  foldK : Nat
  logDomain : Nat
  logInvRate : Nat
  oodCount : Nat
  queryCount : Nat
  degBound : Nat
  agree : Nat
  etaNum : Nat
  etaDen : Nat
  listSize : Nat
  sumcheckDeg : Nat
  mcaNum : Nat
  deriving DecidableEq, Repr

@[expose] def WhirStage.domainSize (s : WhirStage) : Nat := 2 ^ s.logDomain

/-- `(1 - δ) > √ρ + η` with `ρ = d / n`, the nominal rate `ρ ≥ 2^-logInvRate`, and
    `L = ⌈1 / (2 η √ρ)⌉`. -/
@[expose] def WhirStage.johnsonOk (s : WhirStage) : Bool :=
  decide (0 < s.etaNum ∧ 0 < s.degBound ∧ s.agree ≤ s.domainSize ∧
    s.domainSize ≤ s.degBound * 2 ^ s.logInvRate ∧
    s.etaNum * s.domainSize < s.agree * s.etaDen ∧
    s.domainSize * s.degBound * (s.etaDen * s.etaDen) <
      (s.agree * s.etaDen - s.etaNum * s.domainSize) * (s.agree * s.etaDen - s.etaNum * s.domainSize) ∧
    (s.etaDen * s.etaDen) * s.domainSize ≤
      (2 * s.listSize) * (2 * s.listSize) * (s.etaNum * s.etaNum) * s.degBound ∧
    (s.listSize = 0 ∨
      (2 * (s.listSize - 1)) * (2 * (s.listSize - 1)) * (s.etaNum * s.etaNum) * s.degBound <
        (s.etaDen * s.etaDen) * s.domainSize))

syntax "ac_mul" : tactic
macro_rules
  | `(tactic| ac_mul) => `(tactic| simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm])

theorem nat_mul_lt_mul_right' {a b c : Nat} (h : a < b) (hc : 0 < c) : a * c < b * c :=
  Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hc)
    (Nat.le_trans (Nat.le_of_eq (Nat.succ_mul a c).symm) (Nat.mul_le_mul_right c h))

theorem nat_lt_of_mul_lt_mul_right' {a b c : Nat} (h : a * c < b * c) : a < b :=
  Nat.lt_of_not_ge (fun hge => Nat.not_lt_of_ge (Nat.mul_le_mul_right c hge) h)

theorem nat_lt_of_mul_lt_mul_left' {a b c : Nat} (h : c * a < c * b) : a < b :=
  Nat.lt_of_not_ge (fun hge => Nat.not_lt_of_ge (Nat.mul_le_mul_left c hge) h)

theorem nat_le_of_mul_le_mul_right' {a b c : Nat} (h : a * c ≤ b * c) (hc : 0 < c) : a ≤ b :=
  Nat.le_of_not_gt (fun hgt => Nat.not_lt_of_ge h (nat_mul_lt_mul_right' hgt hc))

theorem nat_lt_of_mul_self_lt' {a b : Nat} (h : a * a < b * b) : a < b :=
  Nat.lt_of_not_ge (fun hge => Nat.not_lt_of_ge (Nat.mul_le_mul hge hge) h)

/-- The arithmetic of the Johnson list bound: with `A/n - e/E > √(d/n)` (as `n·d·E² < U²`,
    `U = A·E - e·n`) and `(2L)² e² d ≥ E² n`, any `J` with `J·(A² - n·d) ≤ n·(A - d)` is at
    most `L`. -/
theorem johnson_core (n d A e E L J U : Nat)
    (hn : 0 < n) (hAn : A ≤ n) (he : 0 < e)
    (hAE : A * E = U + e * n)
    (hJ : n * d * (E * E) < U * U)
    (hL : (E * E) * n ≤ (2 * L) * (2 * L) * (e * e) * d)
    (hJy : J * (A * A - n * d) ≤ n * (A - d)) :
    n * d < A * A ∧ J ≤ L := by
  have hSq : U * U + 2 * (U * (e * n)) ≤ (U + e * n) * (U + e * n) := by
    have ex : (U + e * n) * (U + e * n) =
        U * U + U * (e * n) + (e * n * U + e * n * (e * n)) := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
    rw [ex, Nat.mul_comm (e * n) U, Nat.two_mul]
    exact Nat.le_trans (Nat.le_of_eq (Nat.add_assoc _ _ _).symm)
      (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_eq (Nat.add_assoc _ _ _)))
  have hAA : A * A * (E * E) = (U + e * n) * (U + e * n) := by
    rw [← hAE]; ac_mul
  have hS2 : n * d * (E * E) + 2 * (U * (e * n)) < A * A * (E * E) := by
    rw [hAA]; exact Nat.lt_of_lt_of_le (Nat.add_lt_add_right hJ _) hSq
  have hnd : n * d < A * A :=
    nat_lt_of_mul_lt_mul_right' (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hS2)
  refine ⟨hnd, ?_⟩
  have hyEq : (A * A - n * d) * (E * E) + n * d * (E * E) = A * A * (E * E) := by
    rw [← Nat.add_mul, Nat.sub_add_cancel (Nat.le_of_lt hnd)]
  have hy2 : 2 * (U * (e * n)) < (A * A - n * d) * (E * E) := by
    rw [← hyEq, Nat.add_comm] at hS2
    exact Nat.lt_of_add_lt_add_right hS2
  have hJn : J * (A * A - n * d) ≤ n * n :=
    Nat.le_trans hJy (Nat.mul_le_mul_left n (Nat.le_trans (Nat.sub_le A d) hAn))
  have h3 : J * (2 * (U * (e * n))) ≤ J * ((A * A - n * d) * (E * E)) :=
    Nat.mul_le_mul_left J (Nat.le_of_lt hy2)
  have h3' : J * ((A * A - n * d) * (E * E)) ≤ n * n * (E * E) := by
    rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ hJn
  have h3'' : (2 * J * (U * e)) * n ≤ (n * (E * E)) * n := by
    have e1 : (2 * J * (U * e)) * n = J * (2 * (U * (e * n))) := by ac_mul
    have e2 : (n * (E * E)) * n = n * n * (E * E) := by ac_mul
    rw [e1, e2]; exact Nat.le_trans h3 h3'
  have hT : 2 * J * (U * e) ≤ n * (E * E) := nat_le_of_mul_le_mul_right' h3'' hn
  have hTT : (2 * J * (U * e)) * (2 * J * (U * e)) ≤ (n * (E * E)) * (n * (E * E)) :=
    Nat.mul_le_mul hT hT
  rcases Nat.eq_zero_or_pos J with hJ0 | hJpos
  · rw [hJ0]; exact Nat.zero_le _
  · have h2J : 0 < 2 * J := Nat.mul_pos (Nat.zero_lt_succ 1) hJpos
    have hK : 0 < (2 * J) * (2 * J) * (e * e) :=
      Nat.mul_pos (Nat.mul_pos h2J h2J) (Nat.mul_pos he he)
    have hU : 0 < U * U := Nat.lt_of_le_of_lt (Nat.zero_le _) hJ
    have hE : 0 < E * E := by
      rcases Nat.eq_zero_or_pos (E * E) with h0 | h
      · rw [h0, Nat.mul_zero] at hTT
        have hz : (2 * J * (U * e)) * (2 * J * (U * e)) = 0 := Nat.le_zero.mp hTT
        have hpos : 0 < (2 * J * (U * e)) * (2 * J * (U * e)) := by
          have hUpos : 0 < U := by
            rcases Nat.eq_zero_or_pos U with hu | hu
            · rw [hu] at hU; exact absurd hU (Nat.lt_irrefl 0)
            · exact hu
          exact Nat.mul_pos (Nat.mul_pos h2J (Nat.mul_pos hUpos he))
            (Nat.mul_pos h2J (Nat.mul_pos hUpos he))
        rw [hz] at hpos
        exact absurd hpos (Nat.lt_irrefl 0)
      · exact h
    have h5 : n * d * (E * E) * ((2 * J) * (2 * J) * (e * e) * n) <
        U * U * ((2 * J) * (2 * J) * (e * e) * n) :=
      nat_mul_lt_mul_right' hJ (Nat.mul_pos hK hn)
    have e3 : U * U * ((2 * J) * (2 * J) * (e * e) * n) =
        (2 * J * (U * e)) * (2 * J * (U * e)) * n := by ac_mul
    have h6 : (2 * J * (U * e)) * (2 * J * (U * e)) * n ≤ (n * (E * E)) * (n * (E * E)) * n :=
      Nat.mul_le_mul_right n hTT
    have e4 : n * d * (E * E) * ((2 * J) * (2 * J) * (e * e) * n) =
        ((2 * J) * (2 * J) * (e * e) * d) * (n * (E * E) * n) := by ac_mul
    have e5 : (n * (E * E)) * (n * (E * E)) * n = ((E * E) * n) * (n * (E * E) * n) := by ac_mul
    have h7 : ((2 * J) * (2 * J) * (e * e) * d) * (n * (E * E) * n) <
        ((E * E) * n) * (n * (E * E) * n) := by
      rw [← e4, ← e5]; rw [e3] at h5; exact Nat.lt_of_lt_of_le h5 h6
    have h8 : (2 * J) * (2 * J) * (e * e) * d < (E * E) * n := nat_lt_of_mul_lt_mul_right' h7
    have h9 : (2 * J) * (2 * J) * ((e * e) * d) < (2 * L) * (2 * L) * ((e * e) * d) := by
      have e6 : ∀ X : Nat, X * ((e * e) * d) = X * (e * e) * d :=
        fun X => (Nat.mul_assoc X (e * e) d).symm
      rw [e6, e6]; exact Nat.lt_of_lt_of_le h8 hL
    have h10 : (2 * J) * (2 * J) < (2 * L) * (2 * L) := nat_lt_of_mul_lt_mul_right' h9
    have h11 : 2 * J < 2 * L := nat_lt_of_mul_self_lt' h10
    exact Nat.le_of_lt (nat_lt_of_mul_lt_mul_left' h11)

/-- **Schedule-derived Johnson list size.** A stage passing `johnsonOk` is inside the Johnson
    radius (`n·d < A²`) and its integer Johnson bound is at most the declared `listSize`. -/
theorem WhirStage.johnson_list_le (s : WhirStage) (h : s.johnsonOk = true) :
    s.domainSize * s.degBound < s.agree * s.agree ∧
    JohnsonBound.johnsonBound s.domainSize s.agree s.degBound ≤ s.listSize := by
  unfold WhirStage.johnsonOk at h
  obtain ⟨he, _, hAn, _, hU, hJ, hL, _⟩ := of_decide_eq_true h
  have hn : 0 < s.domainSize := Nat.two_pow_pos s.logDomain
  have hAE : s.agree * s.etaDen =
      (s.agree * s.etaDen - s.etaNum * s.domainSize) + s.etaNum * s.domainSize :=
    (Nat.sub_add_cancel (Nat.le_of_lt hU)).symm
  exact johnson_core s.domainSize s.degBound s.agree s.etaNum s.etaDen s.listSize
    (JohnsonBound.johnsonBound s.domainSize s.agree s.degBound)
    (s.agree * s.etaDen - s.etaNum * s.domainSize) hn hAn he hAE hJ hL
    (by simpa only [JohnsonBound.johnsonBound_eq] using
      (Nat.div_mul_le_self (s.domainSize * (s.agree - s.degBound))
        (s.agree * s.agree - s.domainSize * s.degBound)))

/-- Outside the Johnson radius no slack and no list size pass the check. -/
theorem WhirStage.johnsonOk_false_of_beyond_radius (s : WhirStage)
    (h : s.agree * s.agree ≤ s.domainSize * s.degBound) : s.johnsonOk = false := by
  cases hOk : s.johnsonOk with
  | false => rfl
  | true => exact absurd (s.johnson_list_le hOk).1 (Nat.not_lt_of_ge h)

/-- **Decode lists of a Johnson stage have at most `listSize` elements**, for every received
    word over every `n`-point domain of any constructive field. -/
theorem WhirStage.decode_list_le {F : Type} [LawfulField F] [DecidableEq F] (s : WhirStage)
    (h : s.johnsonOk = true) (D : List F) (word : F → F) (hD : D.Nodup)
    (hLen : D.length = s.domainSize) :
    (gsDecodeList s.degBound s.agree D word).length ≤ s.listSize := by
  obtain ⟨hnd, hJL⟩ := s.johnson_list_le h
  unfold WhirStage.johnsonOk at h
  obtain ⟨_, _, hAn, _⟩ := of_decide_eq_true h
  have hdA : s.degBound + 1 ≤ s.agree := by
    apply Nat.lt_of_not_ge
    intro hge
    exact Nat.not_le_of_gt hnd (Nat.mul_le_mul hAn hge)
  have hDen : D.length * s.degBound < s.agree * s.agree := by rw [hLen]; exact hnd
  have hList := gsDecodeList_length_le_johnson D word s.degBound s.agree hD hdA hDen
  rw [hLen] at hList
  exact Nat.le_trans hList hJL

/-! ## §2. The schedule and its round bounds -/

structure WhirVerifierSchedule where
  nv : Nat
  fieldCard : Nat
  fieldPos : 0 < fieldCard
  stages : List WhirStage

@[expose] def WhirVerifierSchedule.johnsonOk (sched : WhirVerifierSchedule) : Bool :=
  sched.stages.all (fun s => s.johnsonOk)

@[expose] def stageRounds (s : WhirStage) : Nat := s.foldK + 2

@[expose] def roundsOf : List WhirStage → Nat
  | [] => 0
  | s :: rest => stageRounds s + roundsOf rest

@[expose] def WhirVerifierSchedule.numRounds (sched : WhirVerifierSchedule) : Nat := roundsOf sched.stages

/-- Fold / sumcheck round: `(L · d* + mca) / q`. -/
def WhirStage.foldBound (q : Nat) (hq : 0 < q) (s : WhirStage) : RatBound :=
  ⟨s.listSize * s.sumcheckDeg + s.mcaNum, q, hq⟩

/-- OOD round: two of the `≤ L` candidates agree on all `s` sampled points: `C(L,2) · d^s / q^s`. -/
def WhirStage.oodBound (q : Nat) (hq : 0 < q) (s : WhirStage) : RatBound :=
  ⟨binom2 s.listSize * s.degBound ^ s.oodCount, q ^ s.oodCount, Nat.pow_pos hq⟩

/-- Shift-query round: every one of the `t` queried fibers lies in an agreement set of
    `A + k` fibers (`((A + k) / n)^t`, i.e. `(1 - δ)^t` with the fold loss), plus the
    combination-randomness term `L · (t + s) / q`. -/
def WhirStage.shiftBound (q : Nat) (hq : 0 < q) (s : WhirStage) : RatBound :=
  RatBound.add
    ⟨(s.agree + s.foldK) ^ s.queryCount, s.domainSize ^ s.queryCount,
      Nat.pow_pos (Nat.two_pow_pos s.logDomain)⟩
    ⟨s.listSize * (s.queryCount + s.oodCount), q, hq⟩

/-- Round bounds of one stage, in round order: `foldK` fold rounds, the commit/OOD round, the
    answer/shift round. -/
def WhirStage.roundBounds (q : Nat) (hq : 0 < q) (s : WhirStage) : List RatBound :=
  List.replicate s.foldK (s.foldBound q hq) ++ [s.oodBound q hq, s.shiftBound q hq]

def stagesRoundBounds (q : Nat) (hq : 0 < q) : List WhirStage → List RatBound
  | [] => []
  | s :: rest => s.roundBounds q hq ++ stagesRoundBounds q hq rest

def WhirVerifierSchedule.roundBounds (sched : WhirVerifierSchedule) : List RatBound :=
  stagesRoundBounds sched.fieldCard sched.fieldPos sched.stages

theorem stagesRoundBounds_length (q : Nat) (hq : 0 < q) :
    ∀ stages : List WhirStage, (stagesRoundBounds q hq stages).length = roundsOf stages
  | [] => by rfl
  | s :: rest => by
    show (s.roundBounds q hq ++ stagesRoundBounds q hq rest).length = stageRounds s + roundsOf rest
    rw [List.length_append, stagesRoundBounds_length q hq rest]
    unfold WhirStage.roundBounds stageRounds
    rw [List.length_append, List.length_replicate]
    rfl

theorem WhirVerifierSchedule.roundBounds_length (sched : WhirVerifierSchedule) :
    sched.roundBounds.length = sched.numRounds :=
  stagesRoundBounds_length _ _ _

/-- **The schedule's QROM error**: every round bound of every stage, scaled by the
    measure-and-reprogram factor `(2Q+1)²`, summed. -/
def scheduleQromError (sched : WhirVerifierSchedule) (Q : Nat) : RatBound :=
  RatBound.sumList (sched.roundBounds.map (dfmRoundScale Q))

theorem dfm_sum_le (Q w : Nat) :
    ∀ (k : Nat) (bad : Fin k → Nat) (bs : List RatBound), bs.length = k →
      (∀ r : Fin k, RatBound.le ⟨bad r, 2 ^ w, Nat.two_pow_pos w⟩ (bs.getD r.1 RatBound.one)) →
      RatBound.le ⟨(2 * Q + 1) ^ 2 * qsum k bad, 2 ^ w, Nat.two_pow_pos w⟩
        (RatBound.sumList (bs.map (dfmRoundScale Q)))
  | 0, _, _, _, _ => by
    show (2 * Q + 1) ^ 2 * 0 * _ ≤ _
    rw [Nat.mul_zero, Nat.zero_mul]
    exact Nat.zero_le _
  | k + 1, _, [], hLen, _ => absurd hLen (Nat.succ_ne_zero k).symm
  | k + 1, bad, b :: bs, hLen, hCov => by
    have ih := dfm_sum_le Q w k (fun i => bad ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) bs
      (Nat.succ.inj hLen) (fun r => hCov ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩)
    have h0 : RatBound.le ⟨bad ⟨0, Nat.zero_lt_succ k⟩, 2 ^ w, Nat.two_pow_pos w⟩ b :=
      hCov ⟨0, Nat.zero_lt_succ k⟩
    have h0' : RatBound.le
        ⟨(2 * Q + 1) ^ 2 * bad ⟨0, Nat.zero_lt_succ k⟩, 2 ^ w, Nat.two_pow_pos w⟩
        (dfmRoundScale Q b) := by
      show (2 * Q + 1) ^ 2 * bad ⟨0, Nat.zero_lt_succ k⟩ * b.den ≤
        (2 * Q + 1) ^ 2 * b.num * 2 ^ w
      rw [Nat.mul_assoc, Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ h0
    have hAdd := RatBound.add_le_add h0' ih
    refine RatBound.le_trans ?_ hAdd
    show (2 * Q + 1) ^ 2 *
        (bad ⟨0, Nat.zero_lt_succ k⟩ + qsum k (fun i => bad ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)) *
        (2 ^ w * 2 ^ w) ≤
      ((2 * Q + 1) ^ 2 * bad ⟨0, Nat.zero_lt_succ k⟩ * 2 ^ w +
        (2 * Q + 1) ^ 2 * qsum k (fun i => bad ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) * 2 ^ w) * 2 ^ w
    generalize (2 * Q + 1) ^ 2 = C
    generalize bad ⟨0, Nat.zero_lt_succ k⟩ = b0
    generalize qsum k (fun i => bad ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) = S
    generalize 2 ^ w = W
    have hEq : C * (b0 + S) * (W * W) = (C * b0 * W + C * S * W) * W := by
      rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, ← Nat.mul_assoc, ← Nat.mul_assoc]
    exact Nat.le_of_eq hEq

/-! ## §3. The executable verifier as an oracle IOP -/

structure WhirMsg (F : Type) where
  table : List F
  poly : List F
  answers : List F
  deriving DecidableEq

structure WhirPub (F : Type) where
  poly : List F
  answers : List F

structure WhirStmt (F : Type) where
  table : List F
  claim : F

structure StageView (F : Type) where
  folds : List (WhirPub F × Nat)
  commit : WhirPub F × Nat
  answer : WhirPub F × Nat

/-- Field- and domain-specific algebra used by the verifier: challenge decoding, evaluation
    points, the binary fold at a point, and the terminal weight evaluation of the sumcheck.
    Optional hooks (`foldClaimStep`, `foldBlockRaw`, `finalClaimViews`, all defaulting to `none`)
    support multi-slot `[CWYZ26]` dual-bridge coset folding and multi-stage kernel evaluation
    claims while keeping `sampledQueryEnv` and `sumcheckRun` definitionally unchanged. -/
structure WhirEnv (F : Type) where
  chalField : Nat → Nat → F
  chalPos : Nat → Nat → Nat → Nat
  domPt : Nat → Nat → F
  fold2 : F → F → F → F → F
  finalClaim : List F → List F → F
  initClaim : List F → F
  finalDeg : Nat
  foldClaimStep : Option (Nat → F → List F → Nat → Option F) := none
  foldBlockRaw : Option (Nat → List (WhirPub F × Nat) → Nat → Nat → List F → F) := none
  finalClaimViews : Option (List (StageView F) → List F → F) := none
  /-- Point of pair j in a fiber of order 2^k with representative x. -/
  fiberPoint : Option (Nat → F → Nat → F) := none

section Verifier
variable {F : Type} [CommRingOps F] [DecidableEq F]

/-- Split the public transcript into per-stage views. -/
@[expose] def splitStages : List WhirStage → List (WhirPub F × Nat) → Option (List (StageView F))
  | [], [] => some []
  | [], _ :: _ => none
  | st :: rest, rounds =>
    match rounds.drop st.foldK with
    | cm :: an :: tail =>
      (splitStages rest tail).map (fun vs => ⟨rounds.take st.foldK, cm, an⟩ :: vs)
    | _ => none

/-- Sumcheck rounds: degree bound, `h(0) + h(1) = claim`, next claim `h(α)`. Returns the
    residual claim and the fold challenges. -/
def sumcheckRun (env : WhirEnv F) (deg : Nat) : F → List (WhirPub F × Nat) → Option (F × List F)
  | claim, [] => some (claim, [])
  | claim, (pub, c) :: rest =>
    if pub.poly.length ≤ deg + 1 ∧
        CommRingOps.add (RoundPoly.evalCoeffs pub.poly CommRingOps.zero)
          (RoundPoly.evalCoeffs pub.poly CommRingOps.one) = claim then
      (sumcheckRun env deg (RoundPoly.evalCoeffs pub.poly (env.chalField c 0)) rest).map
        (fun r => (r.1, env.chalField c 0 :: r.2))
    else none

/-- One binary fold of a block: first half against second half. -/
def foldLayer (env : WhirEnv F) (x α : F) (block : List F) : List F :=
  (List.zip (block.take (block.length / 2)) (block.drop (block.length / 2))).map
    (fun ab => env.fold2 x α ab.1 ab.2)

/-- Fold a `2^k` block with the `k` round challenges. -/
@[expose] def foldBlock (env : WhirEnv F) : List F → F → List F → F
  | [], _, block => block.headD CommRingOps.zero
  | α :: rest, x, block =>
    let layer := match env.fiberPoint with
      | none => foldLayer env x α block
      | some point =>
        let half := block.length / 2
        (List.range half).map fun j =>
          env.fold2 (point (rest.length + 1) x j) α
            (block.getD j CommRingOps.zero) (block.getD (half + j) CommRingOps.zero)
    foldBlock env rest (CommRingOps.mul x x) layer

/-- `claim + Σ_l γ^(l+1) v_l`. -/
def combineClaim (claim γ : F) (vs : List F) : F :=
  (vs.foldl (fun (acc : F × F) v =>
    (CommRingOps.add acc.1 (CommRingOps.mul acc.2 v), CommRingOps.mul acc.2 γ)) (claim, γ)).1

/-- Positions of stage `i` read by the verifier: for each of the `t` sampled fibers, its
    `2^k` points. -/
def stageQueries (env : WhirEnv F) (i : Nat) (st : WhirStage) (v : StageView F) : List (Nat × Nat) :=
  (List.range st.queryCount).flatMap (fun j =>
    (List.range (2 ^ st.foldK)).map (fun b =>
      (i, env.chalPos v.answer.2 j st.domainSize + b * st.domainSize)))

def allStageQueries (env : WhirEnv F) : Nat → List WhirStage → List (StageView F) → List (Nat × Nat)
  | i, st :: rest, v :: vs => stageQueries env i st v ++ allStageQueries env (i + 1) rest vs
  | _, _, _ => []

/-- Custom per-round fold-claim runner when `env.foldClaimStep = some stepFn`. -/
def stageFoldRunAux (stepFn : Nat → F → List F → Nat → Option F) (i : Nat) :
    F → List (WhirPub F × Nat) → Option (F × List F)
  | claim, [] => some (claim, [])
  | claim, (pub, c) :: rest =>
    match stepFn i claim pub.poly c with
    | none => none
    | some nextClaim =>
      (stageFoldRunAux stepFn i nextClaim rest).map (fun r => (r.1, CommRingOps.zero :: r.2))

def stageFoldRun (env : WhirEnv F) (i deg : Nat) (claim : F)
    (folds : List (WhirPub F × Nat)) : Option (F × List F) :=
  match env.foldClaimStep with
  | none => sumcheckRun env deg claim folds
  | some stepFn => stageFoldRunAux stepFn i claim folds

/-- Stage-by-stage verifier helper retaining the full `StageView` list `allVs` for optional
    multi-stage terminal kernel evaluation (`env.finalClaimViews`). -/
@[expose] def whirCheckStagesAux (env : WhirEnv F) (allVs : List (StageView F)) :
    Nat → List WhirStage → List (StageView F) → F → List F → Bool
  | i, st :: rest, v :: vs, claim, vals =>
    match stageFoldRun env i st.sumcheckDeg claim v.folds with
    | none => false
    | some (claim1, αs) =>
      let zs := (List.range st.oodCount).map (env.chalField v.commit.2)
      let ys := v.answer.1.answers
      let γ := env.chalField v.answer.2 st.queryCount
      let blockLen := 2 ^ st.foldK
      let need := st.queryCount * blockLen
      let folded := (List.range st.queryCount).map (fun j =>
        match env.foldBlockRaw with
        | none =>
          foldBlock env αs (env.domPt i (env.chalPos v.answer.2 j st.domainSize))
            ((vals.drop (j * blockLen)).take blockLen)
        | some rawFn =>
          rawFn i v.folds j (env.chalPos v.answer.2 j st.domainSize)
            ((vals.drop (j * blockLen)).take blockLen))
      let expFinal :=
        match env.finalClaimViews with
        | none => env.finalClaim v.commit.1.poly αs
        | some viewsFn => viewsFn allVs αs
      decide (ys.length = st.oodCount) && decide (need ≤ vals.length) &&
      (if rest.isEmpty then
        decide (v.commit.1.poly.length ≤ env.finalDeg + 1) &&
        (zs.zip ys).all (fun zy => decide (RoundPoly.evalCoeffs v.commit.1.poly zy.1 = zy.2)) &&
        ((List.range st.queryCount).zip folded).all (fun jv =>
          decide (RoundPoly.evalCoeffs v.commit.1.poly
            (env.domPt (i + 1) (env.chalPos v.answer.2 jv.1 st.domainSize)) = jv.2)) &&
        decide (claim1 = expFinal) && decide (vals.length = need)
      else
        whirCheckStagesAux env allVs (i + 1) rest vs (combineClaim claim1 γ (ys ++ folded))
          (vals.drop need))
  | _, _, _, _, _ => false

/-- The verifier's checks, stage by stage, on the values read. -/
def whirCheckStages (env : WhirEnv F) (i : Nat) (stages : List WhirStage)
    (vs : List (StageView F)) (claim : F) (vals : List F) : Bool :=
  whirCheckStagesAux env vs i stages vs claim vals

def whirQueries (env : WhirEnv F) (sched : WhirVerifierSchedule)
    (ptr : List (WhirPub F × Nat)) : List (Nat × Nat) :=
  match splitStages sched.stages ptr with
  | none => []
  | some vs => allStageQueries env 0 sched.stages vs

def whirVerdict (env : WhirEnv F) (sched : WhirVerifierSchedule) (claim : F)
    (ptr : List (WhirPub F × Nat)) (vals : List F) : Bool :=
  match splitStages sched.stages ptr with
  | none => false
  | some vs => whirCheckStages env 0 sched.stages vs claim vals

/-- Index of the commit round of stage `j`. -/
def commitRoundIdx : List WhirStage → Nat → Nat
  | [], _ => 0
  | st :: _, 0 => st.foldK
  | st :: rest, j + 1 => stageRounds st + commitRoundIdx rest j

/-- Oracle `0` is the statement's table; oracle `j + 1` is the table sent in the commit round
    of stage `j`. -/
def whirTable (sched : WhirVerifierSchedule) (x : WhirStmt F) (ms : List (WhirMsg F)) :
    Nat → Nat → F
  | 0, p => x.table.getD p CommRingOps.zero
  | j + 1, p =>
    ((ms.getD (commitRoundIdx sched.stages j) ⟨[], [], []⟩).table).getD p CommRingOps.zero

def stageDepth (stages : List WhirStage) (i : Nat) : Nat :=
  match stages[i]? with
  | some st => st.logDomain + st.foldK
  | none => 0

@[expose] def agreeCount (env : WhirEnv F) (size : Nat) (table P : List F) : Nat :=
  ((List.range size).filter (fun p =>
    decide (RoundPoly.evalCoeffs P (env.domPt 0 p) = table.getD p CommRingOps.zero))).length

/-- The statement language: some polynomial within the first stage's degree bound agrees with
    the committed table on the first stage's agreement threshold and carries the claim. -/
@[expose] def whirInLang (env : WhirEnv F) (sched : WhirVerifierSchedule) (x : WhirStmt F) : Prop :=
  match sched.stages with
  | [] => False
  | st :: _ =>
    ∃ P : List F, P.length ≤ 2 ^ st.foldK * st.degBound + 1 ∧
      2 ^ st.foldK * st.agree ≤ agreeCount env (2 ^ st.foldK * st.domainSize) x.table P ∧
      env.initClaim P = x.claim

/-- **The executable multi-round WHIR verifier**, as an oracle IOP with `2^w` challenges per
    round. -/
@[expose] def whirOracleIop (env : WhirEnv F) (sched : WhirVerifierSchedule) (w : Nat) :
    OracleIop (WhirStmt F) F (WhirMsg F) (WhirPub F) F sched.numRounds where
  w := w
  inLang := whirInLang env sched
  pubStmt := fun x => x.claim
  pubMsg := fun m => ⟨m.poly, m.answers⟩
  depth := stageDepth sched.stages
  table := whirTable sched
  queries := fun _ ptr => whirQueries env sched ptr
  verdict := fun claim ptr vals => whirVerdict env sched claim ptr vals

/-- `execWhirVerify`: the verifier of `whirOracleIop` run on Merkle openings. -/
def execWhirVerify {D : Type} [DecidableEq D] (env : WhirEnv F) (sched : WhirVerifierSchedule)
    (w : Nat) (M : MerkleSetup D F) (claim : F) (roots : Nat → D)
    (ptr : List (WhirPub F × Nat)) (ops : List (F × List D)) : Bool :=
  execVerify (whirOracleIop env sched w) M claim roots ptr ops

/-- The algebraic obligation: a Boolean round-by-round state function for the verifier whose
    per-round flip counts are within the schedule's round bounds. -/
structure WhirScheduleCert (env : WhirEnv F) (sched : WhirVerifierSchedule) (w : Nat) where
  cert : BoolRbrCert (whirOracleIop env sched w)
  covers : ∀ r : Fin sched.numRounds,
    RatBound.le ⟨cert.bad r, 2 ^ w, Nat.two_pow_pos w⟩ (sched.roundBounds.getD r.1 RatBound.one)

/-- **Closed QROM soundness of the executable WHIR verifier.** For a statement outside the
    language and any `Q`-query adversary producing messages and openings, the acceptance
    probability of `execWhirVerify` under Fiat–Shamir is at most
    `scheduleQromError sched Q` plus the probability that the explicit collision finder
    `execFsCollision` outputs a collision of the Merkle hash. -/
theorem whir_exec_closed_qrom_soundness {D : Type} [DecidableEq D] {cardX cardAnc Q w : Nat}
    (env : WhirEnv F) (sched : WhirVerifierSchedule) (M : MerkleSetup D F)
    (sc : WhirScheduleCert env sched w)
    (c : FsCodec (WhirMsg F) sched.numRounds cardX)
    (aux : Fin cardX → List (F × List D))
    (x : WhirStmt F) (hx : ¬ whirInLang env sched x)
    (A : QuantumAdv cardX w cardAnc Q) :
    RatBound.le
      ⟨uniformOracleSum w cardX (fun H =>
          QVec.queryMassOn (execFsAccept (whirOracleIop env sched w) M c aux x H)
            (runQuantumAdv A H)),
        (2 ^ w) ^ cardX * (prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init),
        Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos w))
          (Nat.mul_pos (prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩
      (RatBound.add (scheduleQromError sched Q)
        ⟨uniformOracleSum w cardX (fun H =>
            QVec.queryMassOn (execFsCollisionEvent (whirOracleIop env sched w) M c aux x H)
              (runQuantumAdv A H)),
          (2 ^ w) ^ cardX * (prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init),
          Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos w))
            (Nat.mul_pos (prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩) := by
  have hMain := exec_fs_qrom_closed_soundness (whirOracleIop env sched w) M sc.cert c aux x hx A
  have hSum := dfm_sum_le Q w sched.numRounds sc.cert.bad sched.roundBounds
    sched.roundBounds_length sc.covers
  exact RatBound.le_trans hMain (RatBound.add_le_add hSum (RatBound.le_refl _))

/-! ### §3b. Succinct Merkle-root-and-opening WHIR compilation -/

/-- Inverse of `commitRoundIdx`: returns `some j` iff round `r` is the commit round of stage `j`. -/
def stageOfCommitRound : List WhirStage → Nat → Option Nat
  | [], _ => none
  | st :: rest, r =>
    if r = st.foldK then some 0
    else if st.foldK + 2 ≤ r then
      (stageOfCommitRound rest (r - (st.foldK + 2))).map (· + 1)
    else none

theorem commitRoundIdx_lt_roundsOf :
    ∀ (stages : List WhirStage) (j : Nat), j < stages.length →
      commitRoundIdx stages j < roundsOf stages
  | [], _, hj => nomatch hj
  | st :: rest, 0, _ => by
    show st.foldK < (st.foldK + 2) + roundsOf rest
    omega
  | st :: rest, j + 1, hj => by
    show (st.foldK + 2) + commitRoundIdx rest j < (st.foldK + 2) + roundsOf rest
    have ih := commitRoundIdx_lt_roundsOf rest j (Nat.lt_of_succ_lt_succ hj)
    omega

theorem stageOfCommitRound_commitRoundIdx :
    ∀ (stages : List WhirStage) (j : Nat), j < stages.length →
      stageOfCommitRound stages (commitRoundIdx stages j) = some j
  | [], _, hj => nomatch hj
  | st :: _, 0, _ => by
    unfold commitRoundIdx stageOfCommitRound
    rw [ite_true_eq _ _ rfl]
  | st :: rest, j + 1, hj => by
    show stageOfCommitRound (st :: rest) ((st.foldK + 2) + commitRoundIdx rest j) = some (j + 1)
    unfold stageOfCommitRound
    have hNe : (st.foldK + 2) + commitRoundIdx rest j ≠ st.foldK := by omega
    have hGe : st.foldK + 2 ≤ (st.foldK + 2) + commitRoundIdx rest j := by omega
    have hSub : (st.foldK + 2) + commitRoundIdx rest j - (st.foldK + 2) =
        commitRoundIdx rest j := by omega
    rw [ite_false_eq _ _ hNe, ite_true_eq _ _ hGe, hSub,
        stageOfCommitRound_commitRoundIdx rest j (Nat.lt_of_succ_lt_succ hj)]
    rfl

omit [CommRingOps F] [DecidableEq F] in
theorem allStageQueries_fst_lt (env : WhirEnv F) :
    ∀ (stages : List WhirStage) (vs : List (StageView F)) (i : Nat) (q : Nat × Nat),
      q ∈ allStageQueries env i stages vs → q.1 < i + stages.length
  | [], _, _, _, h => nomatch h
  | _ :: _, [], _, _, h => nomatch h
  | _ :: rest, _ :: vs, i, q, h => by
    unfold allStageQueries at h
    rcases List.mem_append.mp h with hHead | hTail
    · unfold stageQueries at hHead
      rcases List.mem_flatMap.mp hHead with ⟨_, _, hMap⟩
      rcases List.mem_map.mp hMap with ⟨_, _, hEq⟩
      rw [← hEq]
      show i < i + (rest.length + 1)
      omega
    · have ih := allStageQueries_fst_lt env rest vs (i + 1) q hTail
      show q.1 < i + (rest.length + 1)
      omega

private theorem range_map_getD_of_lt {α : Type} (f : Nat → α) (dflt : α) (n p : Nat)
    (hp : p < n) :
    ((List.range n).map f).getD p dflt = f p := by
  have hLen : (List.range n).length = n := List.length_range
  have hp' : p < (List.range n).length := by rw [hLen]; exact hp
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hp',
      List.getElem_range]
  rfl

/-- Wire-transmitted Merkle roots for `whirOracleIop`: oracle `0` comes from the statement's
    initial root `r0 0`, and oracle `j + 1` comes from stage `j`'s commit-round `root`. -/
def whirSuccinctRootsOf {D Pub : Type} (stages : List WhirStage) (dfltRoot : D)
    (r0 : Nat → D) (sms : List (SuccinctRoundMsg D Pub)) : Nat → D
  | 0 => r0 0
  | j + 1 =>
    match sms[commitRoundIdx stages j]? with
    | some sm => sm.root.getD dfltRoot
    | none => dfltRoot

/-- Lift a succinct public claim and initial root `r0 0` into a `WhirStmt F` via `tblOf`. -/
def whirSuccinctLiftStmt {D : Type} (sched : WhirVerifierSchedule)
    (claim : F) (r0 : Nat → D) (tblOf : Nat → D → Nat → F) : WhirStmt F :=
  ⟨(List.range (2 ^ stageDepth sched.stages 0)).map (tblOf 0 (r0 0)), claim⟩

/-- Lift a succinct round message `(root, pub)` at round `r` into a `WhirMsg F` via `tblOf`. -/
def whirSuccinctLiftMsg {D : Type} (sched : WhirVerifierSchedule) (dfltRoot : D)
    (r : Nat) (sm : SuccinctRoundMsg D (WhirPub F)) (tblOf : Nat → D → Nat → F) : WhirMsg F :=
  match stageOfCommitRound sched.stages r with
  | some j =>
    ⟨(List.range (2 ^ stageDepth sched.stages (j + 1))).map
      (tblOf (j + 1) (sm.root.getD dfltRoot)),
     sm.pub.poly, sm.pub.answers⟩
  | none => ⟨[], sm.pub.poly, sm.pub.answers⟩

/-- **Protocol-specific `SuccinctIopBridge` for `whirOracleIop` (`whirSuccinctBridge`)**:
    Fiat–Shamir hashes ONLY succinct `(Option D, WhirPub F)` round messages and `succinctVerify`
    checks Merkle openings directly against the wire-transmitted roots. -/
def whirSuccinctBridge {D : Type} (env : WhirEnv F) (sched : WhirVerifierSchedule)
    (w : Nat) (dfltRoot : D) :
    SuccinctIopBridge (whirOracleIop env sched w) D where
  rootsOf := whirSuccinctRootsOf sched.stages dfltRoot
  liftStmt := whirSuccinctLiftStmt sched
  liftMsg := whirSuccinctLiftMsg sched dfltRoot
  pubStmt_lift := fun _ _ _ => rfl
  pubMsg_lift := fun r sm tblOf => by
    unfold whirOracleIop whirSuccinctLiftMsg
    dsimp only
    cases stageOfCommitRound sched.stages r <;> rfl
  table_lift := fun ps r0 str tblOf q hStrLen hq hp => by
    have hqStages : q.1 < sched.stages.length := by
      unfold whirOracleIop whirQueries at hq
      dsimp only at hq
      cases hSplit : splitStages sched.stages (str.map (fun sc => (sc.1.pub, sc.2))) with
      | none => rw [hSplit] at hq; exact nomatch hq
      | some vs =>
        rw [hSplit] at hq
        have hLt := allStageQueries_fst_lt env sched.stages vs 0 q hq
        omega
    cases hq1 : q.1 with
    | zero =>
      rw [hq1] at hp
      unfold whirOracleIop whirTable whirSuccinctLiftStmt whirSuccinctRootsOf
      dsimp only
      exact range_map_getD_of_lt (tblOf 0 (r0 0)) CommRingOps.zero
        (2 ^ stageDepth sched.stages 0) q.2 hp
    | succ j =>
      rw [hq1] at hp hqStages
      have hjLt : j < sched.stages.length := Nat.lt_of_succ_lt hqStages
      have hrRounds : commitRoundIdx sched.stages j < sched.numRounds :=
        commitRoundIdx_lt_roundsOf sched.stages j hjLt
      have hrSms : commitRoundIdx sched.stages j < (str.map Prod.fst).length := by
        rw [List.length_map, hStrLen]; exact hrRounds
      let sm := (str.map Prod.fst)[commitRoundIdx sched.stages j]
      have hSmsGet : (str.map Prod.fst)[commitRoundIdx sched.stages j]? = some sm :=
        List.getElem?_eq_getElem hrSms
      unfold whirOracleIop whirTable whirSuccinctRootsOf
      dsimp only
      rw [List.getD_eq_getElem?_getD
            (l := liftMsgsAux (whirSuccinctLiftMsg sched dfltRoot) tblOf 0 (str.map Prod.fst)),
          liftMsgsAux_getElem? (whirSuccinctLiftMsg sched dfltRoot) tblOf (str.map Prod.fst) 0
            (commitRoundIdx sched.stages j),
          hSmsGet, Option.map_some, Option.getD_some, Nat.zero_add]
      unfold whirSuccinctLiftMsg
      rw [stageOfCommitRound_commitRoundIdx sched.stages j hjLt]
      dsimp only
      exact range_map_getD_of_lt (tblOf (j + 1) (sm.root.getD dfltRoot)) CommRingOps.zero
        (2 ^ stageDepth sched.stages (j + 1)) q.2 hp

theorem whirSuccinctBridge_rootsOf {D : Type} (env : WhirEnv F) (sched : WhirVerifierSchedule)
    (w : Nat) (dflt : D) :
    (whirSuccinctBridge env sched w dflt).rootsOf = whirSuccinctRootsOf sched.stages dflt := by unfold whirSuccinctBridge; rfl

/-- **Closed Succinct-Transcript QROM Soundness of Multi-Round WHIR
    (`whir_succinct_closed_qrom_soundness`)**:
    With Fiat–Shamir hashing ONLY succinct `(Option D, WhirPub F)` message prefixes, for any
    statement outside `whirInLang` and any `Q`-query quantum adversary `A`, the acceptance
    probability of `succinctFsAccept` is bounded by `scheduleQromError sched Q` plus the explicit
    Merkle-collision event `succinctFsCollisionEvent`. -/
theorem whir_succinct_closed_qrom_soundness {D : Type} [DecidableEq D] {cardX cardAnc Q w : Nat}
    (env : WhirEnv F) (sched : WhirVerifierSchedule) (M : MerkleSetup D F)
    (dfltRoot : D)
    (sc : WhirScheduleCert env sched w)
    (codec : FsCodec (SuccinctRoundMsg D (WhirPub F)) sched.numRounds cardX)
    (aux : Fin cardX → List (F × List D))
    (claim : F) (initRoots : Nat → D) (tblOf : Nat → D → Nat → F)
    (hx : ¬ whirInLang env sched
      ((whirSuccinctBridge env sched w dfltRoot).liftStmt claim initRoots tblOf))
    (hRoots : ∀ (H : Fin cardX → BitVec w) (o : Fin cardX),
      succinctFsAccept (whirOracleIop env sched w)
        (whirSuccinctBridge env sched w dfltRoot) M codec aux claim initRoots H o = true →
      let str := fsTranscript codec H (codec.dec o)
      ∀ q ∈ (whirOracleIop env sched w).queries claim (str.map (fun sc' => (sc'.1.pub, sc'.2))),
        M.root q.1 ((whirOracleIop env sched w).depth q.1)
          (tblOf q.1 ((whirSuccinctBridge env sched w dfltRoot).rootsOf
            initRoots (str.map Prod.fst) q.1)) =
          (whirSuccinctBridge env sched w dfltRoot).rootsOf initRoots (str.map Prod.fst) q.1)
    (A : QuantumAdv cardX w cardAnc Q) :
    RatBound.le
      ⟨uniformOracleSum w cardX (fun H =>
          QVec.queryMassOn
            (succinctFsAccept (whirOracleIop env sched w)
              (whirSuccinctBridge env sched w dfltRoot) M codec aux claim initRoots H)
            (runQuantumAdv A H)),
        (2 ^ w) ^ cardX * (prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init),
        Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos w))
          (Nat.mul_pos (prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩
      (RatBound.add (scheduleQromError sched Q)
        ⟨uniformOracleSum w cardX (fun H =>
            QVec.queryMassOn
              (succinctFsCollisionEvent (whirOracleIop env sched w)
                (whirSuccinctBridge env sched w dfltRoot) M codec aux claim initRoots tblOf H)
              (runQuantumAdv A H)),
          (2 ^ w) ^ cardX * (prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init),
          Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos w))
            (Nat.mul_pos (prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩) := by
  have hMain := succinct_fs_qrom_closed_soundness (whirOracleIop env sched w)
    (whirSuccinctBridge env sched w dfltRoot) M sc.cert codec aux claim initRoots tblOf hx hRoots A
  have hSum := dfm_sum_le Q w sched.numRounds sc.cert.bad sched.roundBounds
    sched.roundBounds_length sc.covers
  exact RatBound.le_trans hMain (RatBound.add_le_add hSum (RatBound.le_refl _))


end Verifier

/-! ## §4. The deployed `nv = 24` schedule -/

/-- Johnson slack and list size per deployed stage: `(etaNum, etaDen, L)`. -/
def deployedSlack : List (Nat × Nat × Nat) :=
  [(1, 400, 400), (1, 200, 400), (1, 125, 500), (1, 200, 1594)]

/-- The deployed stages, read from the `unitaryZeroPow` witness rows and stage geometry of
    `nv = 24` (`n`, `d`, `A`, fold count, query count, MCA profile numerator), with dual OOD
    and degree-3 sumcheck rounds. -/
def deployedStages : List WhirStage :=
  ((hemOptimizedStageWitnesses .unitaryZeroPow 24).zip
    ((hemStageGeoms 24).zip deployedSlack)).map (fun wg =>
      { foldK := wg.1.sFolds
        logDomain := Nat.log2 wg.1.n
        logInvRate := wg.2.1.logBlowup
        oodCount := 2
        queryCount := wg.1.queries
        degBound := wg.1.d
        agree := wg.1.A
        etaNum := wg.2.2.1
        etaDen := wg.2.2.2.1
        listSize := wg.2.2.2.2
        sumcheckDeg := 3
        mcaNum := whirAffineStageSimpleNum wg.1 })

def deployedSched : WhirVerifierSchedule :=
  ⟨24, goldilocksExt4Card, goldilocksExt4Card_pos, deployedStages⟩

/-- The full concrete stage records, including the MCA profile inputs. -/
theorem deployedStages_full_eq : deployedStages =
  [ { foldK := 6, logDomain := 20, logInvRate := 2, oodCount := 2,
      queryCount := 216, degBound := 262146, agree := 527170, etaNum := 1, etaDen := 400,
      listSize := 400, sumcheckDeg := 3, mcaNum := 1644 },
    { foldK := 4, logDomain := 18, logInvRate := 4, oodCount := 2,
      queryCount := 109, degBound := 16386, agree := 66992, etaNum := 1, etaDen := 200,
      listSize := 400, sumcheckDeg := 3, mcaNum := 824 },
    { foldK := 3, logDomain := 17, logInvRate := 6, oodCount := 2,
      queryCount := 74, degBound := 2050, agree := 17484, etaNum := 1, etaDen := 125,
      listSize := 500, sumcheckDeg := 3, mcaNum := 489 },
    { foldK := 3, logDomain := 16, logInvRate := 8, oodCount := 2,
      queryCount := 56, degBound := 258, agree := 4482, etaNum := 1, etaDen := 200,
      listSize := 1594, sumcheckDeg := 3, mcaNum := 792 } ] := by
  simp only [deployedStages, hemOptimizedStageWitnesses_unitaryZeroPow_24,
    hemStageGeoms_24_eq, deployedSlack, List.zip_cons_cons, List.zip_nil_left,
    List.map_cons, List.map_nil, whirAffineStageSimpleNum_def]
  rfl

/-- The deployed stage parameters, spelled out. -/
theorem deployedStages_eq :
    deployedStages.map (fun s => (s.foldK, s.logDomain, s.logInvRate, s.queryCount,
      s.degBound, s.agree, s.listSize)) =
      [(6, 20, 2, 216, 262146, 527170, 400), (4, 18, 4, 109, 16386, 66992, 400),
       (3, 17, 6, 74, 2050, 17484, 500), (3, 16, 8, 56, 258, 4482, 1594)] := by
  rw [deployedStages_full_eq]
  rfl

/-- Every deployed stage satisfies the Johnson condition with its slack, and its list size is
    the exact ceiling. -/
theorem deployedSched_johnsonOk : deployedSched.johnsonOk = true := by
  simp only [WhirVerifierSchedule.johnsonOk, deployedSched, deployedStages_full_eq]
  decide +kernel

theorem deployedSched_numRounds : deployedSched.numRounds = 24 := by
  simp only [WhirVerifierSchedule.numRounds, deployedSched, deployedStages_full_eq]
  decide +kernel

private inductive RoundBoundsLe : List RatBound → List RatBound → Prop where
  | nil : RoundBoundsLe [] []
  | cons {x y xs ys} : RatBound.le x y → RoundBoundsLe xs ys →
      RoundBoundsLe (x :: xs) (y :: ys)

private theorem RoundBoundsLe.append {xs ys us vs : List RatBound}
    (h : RoundBoundsLe xs ys) (k : RoundBoundsLe us vs) :
    RoundBoundsLe (xs ++ us) (ys ++ vs) := by
  induction h with
  | nil => exact k
  | cons hxy hrest ih => exact .cons hxy ih

private theorem scaled_sum_mono (Q : Nat) {xs ys : List RatBound}
    (h : RoundBoundsLe xs ys) :
    RatBound.le (RatBound.sumList (xs.map (dfmRoundScale Q)))
      (RatBound.sumList (ys.map (dfmRoundScale Q))) := by
  induction h with
  | nil => exact RatBound.le_refl _
  | @cons x y xs ys hxy hrest ih =>
    apply RatBound.add_le_add ?_ ih
    show (2 * Q + 1) ^ 2 * x.num * y.den ≤ (2 * Q + 1) ^ 2 * y.num * x.den
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left ((2 * Q + 1) ^ 2) hxy

private def stageEnvelope (s : WhirStage) : List RatBound :=
  List.replicate s.foldK (RatBound.invPow2 220) ++
    [RatBound.invPow2 220, RatBound.invPow2 214]

private theorem stageEnvelope_covers (q : Nat) (hq : 0 < q) (s : WhirStage)
    (hf : (s.foldBound q hq).le (RatBound.invPow2 220))
    (ho : (s.oodBound q hq).le (RatBound.invPow2 220))
    (hs : (s.shiftBound q hq).le (RatBound.invPow2 214)) :
    RoundBoundsLe (s.roundBounds q hq) (stageEnvelope s) := by
  apply RoundBoundsLe.append
  · induction s.foldK with
    | zero => exact .nil
    | succ n ih => exact .cons hf ih
  · exact .cons ho (.cons hs .nil)

private def deployedEnvelope : List RatBound := deployedStages.flatMap stageEnvelope

private theorem ood_le_of_binom (q : Nat) (hq : 0 < q) (s : WhirStage) (B bits : Nat)
    (hbin : binom2 s.listSize = B)
    (h : B * s.degBound ^ s.oodCount * 2 ^ bits ≤ q ^ s.oodCount) :
    (s.oodBound q hq).le (RatBound.invPow2 bits) := by
  change binom2 s.listSize * s.degBound ^ s.oodCount * 2 ^ bits ≤ 1 * q ^ s.oodCount
  rw [hbin, Nat.one_mul]
  exact h

private theorem binom2_400 : binom2 400 = 79800 := by
  apply Eq.trans (binom2_eq 400)
  exact Nat.div_eq_of_eq_mul_left (by decide : 0 < 2)
    (by decide : 400 * (400 - 1) = 79800 * 2)

private theorem binom2_500 : binom2 500 = 124750 := by
  apply Eq.trans (binom2_eq 500)
  exact Nat.div_eq_of_eq_mul_left (by decide : 0 < 2)
    (by decide : 500 * (500 - 1) = 124750 * 2)

private theorem binom2_1594 : binom2 1594 = 1269621 := by
  apply Eq.trans (binom2_eq 1594)
  exact Nat.div_eq_of_eq_mul_left (by decide : 0 < 2)
    (by decide : 1594 * (1594 - 1) = 1269621 * 2)

set_option maxRecDepth 8192 in
private theorem deployed_stage0_fold :
    (({ foldK := 6, logDomain := 20, logInvRate := 2, oodCount := 2, queryCount := 216, degBound := 262146, agree := 527170, etaNum := 1, etaDen := 400, listSize := 400, sumcheckDeg := 3, mcaNum := 1644 } : WhirStage).foldBound goldilocksExt4Card goldilocksExt4Card_pos).le
      (RatBound.invPow2 220) := by

  change 2844 * 2 ^ 220 ≤ 115792089129476408817739443160502628952720274482139873392618675794070921543681
  decide +kernel

set_option maxRecDepth 8192 in
private theorem deployed_stage0_ood :
    (({ foldK := 6, logDomain := 20, logInvRate := 2, oodCount := 2, queryCount := 216, degBound := 262146, agree := 527170, etaNum := 1, etaDen := 400, listSize := 400, sumcheckDeg := 3, mcaNum := 1644 } : WhirStage).oodBound goldilocksExt4Card goldilocksExt4Card_pos).le
      (RatBound.invPow2 220) := by

  apply ood_le_of_binom _ _ _ 79800 220 binom2_400
  decide +kernel

set_option maxRecDepth 8192 in
private theorem deployed_stage0_shift :
    (({ foldK := 6, logDomain := 20, logInvRate := 2, oodCount := 2, queryCount := 216, degBound := 262146, agree := 527170, etaNum := 1, etaDen := 400, listSize := 400, sumcheckDeg := 3, mcaNum := 1644 } : WhirStage).shiftBound goldilocksExt4Card goldilocksExt4Card_pos).le
      (RatBound.invPow2 214) := by

  change (527176 ^ 216 * 115792089129476408817739443160502628952720274482139873392618675794070921543681 + 87200 * (1048576 ^ 216)) * 2 ^ 214 ≤ (1048576 ^ 216) * 115792089129476408817739443160502628952720274482139873392618675794070921543681
  decide +kernel

set_option maxRecDepth 8192 in
private theorem deployed_stage1_fold :
    (({ foldK := 4, logDomain := 18, logInvRate := 4, oodCount := 2, queryCount := 109, degBound := 16386, agree := 66992, etaNum := 1, etaDen := 200, listSize := 400, sumcheckDeg := 3, mcaNum := 824 } : WhirStage).foldBound goldilocksExt4Card goldilocksExt4Card_pos).le
      (RatBound.invPow2 220) := by

  change 2024 * 2 ^ 220 ≤ 115792089129476408817739443160502628952720274482139873392618675794070921543681
  decide +kernel

set_option maxRecDepth 8192 in
private theorem deployed_stage1_ood :
    (({ foldK := 4, logDomain := 18, logInvRate := 4, oodCount := 2, queryCount := 109, degBound := 16386, agree := 66992, etaNum := 1, etaDen := 200, listSize := 400, sumcheckDeg := 3, mcaNum := 824 } : WhirStage).oodBound goldilocksExt4Card goldilocksExt4Card_pos).le
      (RatBound.invPow2 220) := by

  apply ood_le_of_binom _ _ _ 79800 220 binom2_400
  decide +kernel

set_option maxRecDepth 8192 in
private theorem deployed_stage1_shift :
    (({ foldK := 4, logDomain := 18, logInvRate := 4, oodCount := 2, queryCount := 109, degBound := 16386, agree := 66992, etaNum := 1, etaDen := 200, listSize := 400, sumcheckDeg := 3, mcaNum := 824 } : WhirStage).shiftBound goldilocksExt4Card goldilocksExt4Card_pos).le
      (RatBound.invPow2 214) := by

  change (66996 ^ 109 * 115792089129476408817739443160502628952720274482139873392618675794070921543681 + 44400 * (262144 ^ 109)) * 2 ^ 214 ≤ (262144 ^ 109) * 115792089129476408817739443160502628952720274482139873392618675794070921543681
  decide +kernel

set_option maxRecDepth 8192 in
private theorem deployed_stage2_fold :
    (({ foldK := 3, logDomain := 17, logInvRate := 6, oodCount := 2, queryCount := 74, degBound := 2050, agree := 17484, etaNum := 1, etaDen := 125, listSize := 500, sumcheckDeg := 3, mcaNum := 489 } : WhirStage).foldBound goldilocksExt4Card goldilocksExt4Card_pos).le
      (RatBound.invPow2 220) := by

  change 1989 * 2 ^ 220 ≤ 115792089129476408817739443160502628952720274482139873392618675794070921543681
  decide +kernel

set_option maxRecDepth 8192 in
private theorem deployed_stage2_ood :
    (({ foldK := 3, logDomain := 17, logInvRate := 6, oodCount := 2, queryCount := 74, degBound := 2050, agree := 17484, etaNum := 1, etaDen := 125, listSize := 500, sumcheckDeg := 3, mcaNum := 489 } : WhirStage).oodBound goldilocksExt4Card goldilocksExt4Card_pos).le
      (RatBound.invPow2 220) := by

  apply ood_le_of_binom _ _ _ 124750 220 binom2_500
  decide +kernel

set_option maxRecDepth 8192 in
private theorem deployed_stage2_shift :
    (({ foldK := 3, logDomain := 17, logInvRate := 6, oodCount := 2, queryCount := 74, degBound := 2050, agree := 17484, etaNum := 1, etaDen := 125, listSize := 500, sumcheckDeg := 3, mcaNum := 489 } : WhirStage).shiftBound goldilocksExt4Card goldilocksExt4Card_pos).le
      (RatBound.invPow2 214) := by

  change (17487 ^ 74 * 115792089129476408817739443160502628952720274482139873392618675794070921543681 + 38000 * (131072 ^ 74)) * 2 ^ 214 ≤ (131072 ^ 74) * 115792089129476408817739443160502628952720274482139873392618675794070921543681
  decide +kernel

set_option maxRecDepth 8192 in
private theorem deployed_stage3_fold :
    (({ foldK := 3, logDomain := 16, logInvRate := 8, oodCount := 2, queryCount := 56, degBound := 258, agree := 4482, etaNum := 1, etaDen := 200, listSize := 1594, sumcheckDeg := 3, mcaNum := 792 } : WhirStage).foldBound goldilocksExt4Card goldilocksExt4Card_pos).le
      (RatBound.invPow2 220) := by

  change 5574 * 2 ^ 220 ≤ 115792089129476408817739443160502628952720274482139873392618675794070921543681
  decide +kernel

set_option maxRecDepth 8192 in
private theorem deployed_stage3_ood :
    (({ foldK := 3, logDomain := 16, logInvRate := 8, oodCount := 2, queryCount := 56, degBound := 258, agree := 4482, etaNum := 1, etaDen := 200, listSize := 1594, sumcheckDeg := 3, mcaNum := 792 } : WhirStage).oodBound goldilocksExt4Card goldilocksExt4Card_pos).le
      (RatBound.invPow2 220) := by

  apply ood_le_of_binom _ _ _ 1269621 220 binom2_1594
  decide +kernel

set_option maxRecDepth 8192 in
private theorem deployed_stage3_shift :
    (({ foldK := 3, logDomain := 16, logInvRate := 8, oodCount := 2, queryCount := 56, degBound := 258, agree := 4482, etaNum := 1, etaDen := 200, listSize := 1594, sumcheckDeg := 3, mcaNum := 792 } : WhirStage).shiftBound goldilocksExt4Card goldilocksExt4Card_pos).le
      (RatBound.invPow2 214) := by

  change (4485 ^ 56 * 115792089129476408817739443160502628952720274482139873392618675794070921543681 + 92452 * (65536 ^ 56)) * 2 ^ 214 ≤ (65536 ^ 56) * 115792089129476408817739443160502628952720274482139873392618675794070921543681
  decide +kernel

private theorem deployedEnvelope_covers :
    RoundBoundsLe deployedSched.roundBounds deployedEnvelope := by
  simp only [WhirVerifierSchedule.roundBounds, deployedSched, deployedEnvelope,
    deployedStages_full_eq, stagesRoundBounds, List.flatMap_cons, List.flatMap_nil]
  refine RoundBoundsLe.append ?_ (RoundBoundsLe.append ?_
    (RoundBoundsLe.append ?_ (RoundBoundsLe.append ?_ .nil)))

  · exact stageEnvelope_covers _ _ _ deployed_stage0_fold deployed_stage0_ood deployed_stage0_shift

  · exact stageEnvelope_covers _ _ _ deployed_stage1_fold deployed_stage1_ood deployed_stage1_shift

  · exact stageEnvelope_covers _ _ _ deployed_stage2_fold deployed_stage2_ood deployed_stage2_shift

  · exact stageEnvelope_covers _ _ _ deployed_stage3_fold deployed_stage3_ood deployed_stage3_shift

set_option maxRecDepth 8192 in
/-- **`scheduleQromError deployedSched (2^40) ≤ 2^-128`**, list-size multipliers included.
Each stage is bounded before summation, avoiding products of the unreduced query denominators. -/
theorem deployedSched_error_at_2pow40 :
    atLeastBits 128 (scheduleQromError deployedSched (2 ^ 40)) := by
  apply atLeastBits_of_le (scaled_sum_mono (2 ^ 40) deployedEnvelope_covers)
  simp only [deployedEnvelope, deployedStages_full_eq, List.flatMap_cons, List.flatMap_nil,
    stageEnvelope, List.replicate_succ, List.replicate_zero, List.cons_append,
    List.nil_append, List.map_cons, List.map_nil]
  decide +kernel

/-- Monotonicity in the query budget. -/
theorem scheduleQromError_mono (sched : WhirVerifierSchedule) {Q Q' : Nat} (h : Q ≤ Q') :
    RatBound.le (scheduleQromError sched Q) (scheduleQromError sched Q') := by
  unfold scheduleQromError
  generalize sched.roundBounds = bs
  induction bs with
  | nil => exact RatBound.le_refl _
  | cons b bs ih =>
    refine RatBound.add_le_add ?_ ih
    show (2 * Q + 1) ^ 2 * b.num * b.den ≤ (2 * Q' + 1) ^ 2 * b.num * b.den
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
      (Nat.pow_le_pow_left (Nat.succ_le_succ (Nat.mul_le_mul_left 2 h)) 2))

/-- **Deployed corollary.** With a certificate for `deployedSched` and `Q ≤ 2^40` oracle
    queries, the acceptance probability of `execWhirVerify` on a false statement is at most
    `2^-128` plus the collision-finder probability. -/
theorem deployed_whir_exec_closed_qrom_128 {F D : Type} [CommRingOps F] [DecidableEq F]
    [DecidableEq D] {cardX cardAnc Q w : Nat}
    (env : WhirEnv F) (M : MerkleSetup D F)
    (sc : WhirScheduleCert env deployedSched w)
    (c : FsCodec (WhirMsg F) deployedSched.numRounds cardX)
    (aux : Fin cardX → List (F × List D))
    (x : WhirStmt F) (hx : ¬ whirInLang env deployedSched x)
    (A : QuantumAdv cardX w cardAnc Q) (hQ : Q ≤ 2 ^ 40) :
    RatBound.le
      ⟨uniformOracleSum w cardX (fun H =>
          QVec.queryMassOn (execFsAccept (whirOracleIop env deployedSched w) M c aux x H)
            (runQuantumAdv A H)),
        (2 ^ w) ^ cardX * (prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init),
        Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos w))
          (Nat.mul_pos (prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩
      (RatBound.add (RatBound.invPow2 128)
        ⟨uniformOracleSum w cardX (fun H =>
            QVec.queryMassOn (execFsCollisionEvent (whirOracleIop env deployedSched w) M c aux x H)
              (runQuantumAdv A H)),
          (2 ^ w) ^ cardX * (prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init),
          Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos w))
            (Nat.mul_pos (prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩) := by
  have hMain := whir_exec_closed_qrom_soundness env deployedSched M sc c aux x hx A
  have h128 : RatBound.le (scheduleQromError deployedSched (2 ^ 40)) (RatBound.invPow2 128) := by
    have h := deployedSched_error_at_2pow40
    show (scheduleQromError deployedSched (2 ^ 40)).num * 2 ^ 128 ≤
      1 * (scheduleQromError deployedSched (2 ^ 40)).den
    rw [Nat.one_mul]
    exact h
  exact RatBound.le_trans hMain
    (RatBound.add_le_add (RatBound.le_trans (scheduleQromError_mono deployedSched hQ) h128)
      (RatBound.le_refl _))

/-! ## §5. A constructed certificate for a one-stage schedule with a sampled query

The schedule `sampledQuerySched` has one stage over a four-point domain: no fold rounds, no
out-of-domain sample, one query whose position is the round challenge modulo four, agreement
threshold three, and a final polynomial of degree at most one. Its verifier reads one point of
the statement's table and compares it with the committed polynomial. For a statement outside
the language at most two of the four challenges are accepted, and that count is within the
stage's shift-query bound: `sampledQueryCert` inhabits `WhirScheduleCert` at challenge width two
with flip count `2` in the query round.

This is evidence that the certificate interface is satisfiable by a verifier that accepts honest
proofs, rejects with nonzero and non-total probability, and meets `covers` through the shift
bound. It is a toy: it has no folding, no sumcheck round and no out-of-domain round, so the
fold and OOD bounds are not exercised, and `scheduleQromError sampledQuerySched Q` exceeds one.
It says nothing about `deployedSched`. -/

/-- One stage: `n = 4`, `d = 1`, `A = 3`, `η = 1/100`, `L = 100`, no folds, no OOD sample, one
    query. -/
def sampledQueryStage : WhirStage where
  foldK := 0
  logDomain := 2
  logInvRate := 2
  oodCount := 0
  queryCount := 1
  degBound := 1
  agree := 3
  etaNum := 1
  etaDen := 100
  listSize := 100
  sumcheckDeg := 0
  mcaNum := 0

def sampledQuerySched : WhirVerifierSchedule where
  nv := 2
  fieldCard := goldilocksPrime
  fieldPos := by decide
  stages := [sampledQueryStage]

theorem sampledQuerySched_shape :
    sampledQuerySched.stages.length = 1 ∧
    sampledQuerySched.johnsonOk = true ∧
    sampledQuerySched.numRounds = 2 := by
  decide

/-- Evaluation points `0, 1, 2, 3`; the query position is the challenge modulo the domain size;
    the claim of a polynomial is its value at zero; the final polynomial has degree at most one. -/
def sampledQueryEnv : WhirEnv Goldilocks where
  chalField _ _ := Goldilocks.zero
  chalPos c _ n := c % n
  domPt _ p := Goldilocks.ofNat p
  fold2 _ _ a _ := a
  finalClaim P _ := RoundPoly.evalCoeffs P CommRingOps.zero
  initClaim P := RoundPoly.evalCoeffs P CommRingOps.zero
  finalDeg := 1

/-- The verifier on a two-round transcript, spelled out: no OOD answers, a committed polynomial
    of at most two coefficients that carries the claim, and agreement with the table at the
    sampled position. -/
theorem sampledQuery_verify_iff (w : Nat) (x : WhirStmt Goldilocks)
    (m0 m1 : WhirMsg Goldilocks) (c0 c1 : Nat) :
    (whirOracleIop sampledQueryEnv sampledQuerySched w).verify x [(m0, c0), (m1, c1)] = true ↔
      (m1.answers.length = 0 ∧ m0.poly.length ≤ 2 ∧
        x.claim = RoundPoly.evalCoeffs m0.poly CommRingOps.zero ∧
        RoundPoly.evalCoeffs m0.poly (Goldilocks.ofNat (c1 % 4)) =
          x.table.getD (c1 % 4) CommRingOps.zero) := by
  rw [OracleIop.verify_eq]
  have hRounds : decide (([(m0, c0), (m1, c1)] : List (WhirMsg Goldilocks × Nat)).length =
      sampledQuerySched.numRounds) = true := decide_eq_true rfl
  rw [hRounds, Bool.true_and]
  have hR1 : List.range 1 = [0] := by decide
  have hR0 : List.range 0 = ([] : List Nat) := by decide
  simp only [whirOracleIop, whirVerdict, whirQueries, sampledQuerySched, sampledQueryStage,
    sampledQueryEnv, splitStages, allStageQueries, stageQueries, whirTable, whirCheckStages,
    whirCheckStagesAux, stageFoldRun, sumcheckRun, foldBlock, WhirStage.domainSize, List.map_cons,
    List.map_nil, List.drop_zero,
    List.take_zero, Option.map_some, hR1, hR0, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, Nat.pow_zero, Nat.zero_mul, Nat.add_zero, Nat.one_mul, List.length_cons,
    List.length_nil, List.isEmpty_nil, ↓reduceIte, List.zip_nil_left, List.all_nil,
    List.zip_cons_cons, List.all_cons, List.take_succ_cons, List.headD_cons,
    Bool.and_true, Bool.and_eq_true, decide_eq_true_eq, Nat.le_refl, decide_true, Bool.true_and,
    and_true, true_and, Nat.reduceAdd, Nat.reducePow, Nat.reduceMul]
  exact ⟨fun h => ⟨h.1, h.2.1.1, h.2.2, of_decide_eq_true h.2.1.2⟩,
    fun h => ⟨h.1, ⟨h.2.1, decide_eq_true h.2.2.2⟩, h.2.2.1⟩⟩

private theorem sampledQuery_verify_length (w : Nat) (x : WhirStmt Goldilocks)
    (tr : List (WhirMsg Goldilocks × Nat))
    (h : (whirOracleIop sampledQueryEnv sampledQuerySched w).verify x tr = true) :
    tr.length = 2 := by
  rw [OracleIop.verify_eq] at h
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).1

/-- `1` for an accepted challenge, `0` otherwise. -/
def acceptBit (b : Bool) : Nat := if b = true then 1 else 0

private theorem bit_filter4 (p : Nat → Bool) :
    (([0, 1, 2, 3] : List Nat).filter p).length = acceptBit (p 0) + acceptBit (p 1) + acceptBit (p 2) + acceptBit (p 3) := by
  cases h0 : p 0 <;> cases h1 : p 1 <;> cases h2 : p 2 <;> cases h3 : p 3 <;>
    simp only [List.filter_cons, List.filter_nil, h0, h1, h2, h3, ↓reduceIte, Bool.false_eq_true,
      List.length_cons, List.length_nil, acceptBit] <;> rfl

/-- Agreement of `P` with the table over the stage's four points, as a sum of four bits. -/
private theorem sampledQuery_agreeCount (table P : List Goldilocks) :
    agreeCount sampledQueryEnv (2 ^ sampledQueryStage.foldK * sampledQueryStage.domainSize)
        table P =
      acceptBit (decide (RoundPoly.evalCoeffs P (Goldilocks.ofNat 0) = table.getD 0 CommRingOps.zero)) +
      acceptBit (decide (RoundPoly.evalCoeffs P (Goldilocks.ofNat 1) = table.getD 1 CommRingOps.zero)) +
      acceptBit (decide (RoundPoly.evalCoeffs P (Goldilocks.ofNat 2) = table.getD 2 CommRingOps.zero)) +
      acceptBit (decide (RoundPoly.evalCoeffs P (Goldilocks.ofNat 3) = table.getD 3 CommRingOps.zero)) := by
  have hRange : List.range (2 ^ sampledQueryStage.foldK * sampledQueryStage.domainSize) =
      [0, 1, 2, 3] := by decide
  unfold agreeCount
  rw [hRange]
  exact bit_filter4 _

/-- If each accepted challenge needs the gate `g` and its own agreement acceptBit, and the gate with
    three agreements is impossible, at most two of the four challenges are accepted. -/
private theorem at_most_two_of_four (g a0 a1 a2 a3 v0 v1 v2 v3 : Bool)
    (h0 : v0 = true → g = true ∧ a0 = true) (h1 : v1 = true → g = true ∧ a1 = true)
    (h2 : v2 = true → g = true ∧ a2 = true) (h3 : v3 = true → g = true ∧ a3 = true)
    (hN : ¬ (g = true ∧ 3 ≤ acceptBit a0 + acceptBit a1 + acceptBit a2 + acceptBit a3)) :
    acceptBit v0 + (acceptBit v1 + (acceptBit v2 + (acceptBit v3 + 0))) ≤ 2 := by
  cases g <;> cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;>
    cases v0 <;> cases v1 <;> cases v2 <;> cases v3 <;>
    first
    | decide
    | exact absurd (h0 rfl).1 (by decide)
    | exact absurd (h0 rfl).2 (by decide)
    | exact absurd (h1 rfl).1 (by decide)
    | exact absurd (h1 rfl).2 (by decide)
    | exact absurd (h2 rfl).1 (by decide)
    | exact absurd (h2 rfl).2 (by decide)
    | exact absurd (h3 rfl).1 (by decide)
    | exact absurd (h3 rfl).2 (by decide)
    | exact absurd ⟨rfl, by decide⟩ hN

/-- **Query-round soundness of the one-stage verifier.** For a statement outside the language and
    any first-round message, at most two of the four query challenges are accepted. -/
theorem sampledQuery_query_round_flips (x : WhirStmt Goldilocks)
    (hx : ¬ whirInLang sampledQueryEnv sampledQuerySched x)
    (m0 m1 : WhirMsg Goldilocks) (c0 : Nat) :
    acceptBit ((whirOracleIop sampledQueryEnv sampledQuerySched 2).verify x [(m0, c0), (m1, 0)]) +
    (acceptBit ((whirOracleIop sampledQueryEnv sampledQuerySched 2).verify x [(m0, c0), (m1, 1)]) +
    (acceptBit ((whirOracleIop sampledQueryEnv sampledQuerySched 2).verify x [(m0, c0), (m1, 2)]) +
    (acceptBit ((whirOracleIop sampledQueryEnv sampledQuerySched 2).verify x [(m0, c0), (m1, 3)]) +
      0))) ≤ 2 := by
  have hGate : ∀ c1 : Nat,
      (whirOracleIop sampledQueryEnv sampledQuerySched 2).verify x [(m0, c0), (m1, c1)] = true →
      decide (m0.poly.length ≤ 2 ∧
          x.claim = RoundPoly.evalCoeffs m0.poly CommRingOps.zero) = true ∧
        decide (RoundPoly.evalCoeffs m0.poly (Goldilocks.ofNat (c1 % 4)) =
          x.table.getD (c1 % 4) CommRingOps.zero) = true := fun c1 hv =>
    have h := (sampledQuery_verify_iff 2 x m0 m1 c0 c1).mp hv
    ⟨decide_eq_true ⟨h.2.1, h.2.2.1⟩, decide_eq_true h.2.2.2⟩
  refine at_most_two_of_four _ _ _ _ _ _ _ _ _ (hGate 0) (hGate 1) (hGate 2) (hGate 3) ?_
  rintro ⟨hG, hAgree⟩
  have hG' := of_decide_eq_true hG
  rw [← sampledQuery_agreeCount] at hAgree
  exact hx ⟨m0.poly, hG'.1, hAgree, hG'.2.symm⟩

/-- **A constructed `WhirScheduleCert` for a schedule with a stage.** The state is the verifier's
    verdict, the commit round never flips, and the query round flips on at most two of the four
    challenges, within the stage's shift-query bound `(3/4)^1 + 100/q`. -/
def sampledQueryCert : WhirScheduleCert sampledQueryEnv sampledQuerySched 2 where
  cert := {
    state := (whirOracleIop sampledQueryEnv sampledQuerySched 2).verify
    bad := fun r => if r.1 = 1 then 2 else 0
    init := fun x _ => by
      cases hv : (whirOracleIop sampledQueryEnv sampledQuerySched 2).verify x [] with
      | false => rfl
      | true => exact absurd (sampledQuery_verify_length 2 x [] hv) (show ¬ (0 : Nat) = 2 by decide)
    accept := fun _ _ hv => hv
    flip := fun x hx r pref m hLen _ => by
      match r, pref, hLen with
      | ⟨0, _⟩, [], _ =>
        have hZero : ∀ ch : Nat,
            (whirOracleIop sampledQueryEnv sampledQuerySched 2).verify x [(m, ch)] = false :=
          fun ch => by
            cases hv : (whirOracleIop sampledQueryEnv sampledQuerySched 2).verify x [(m, ch)] with
            | false => rfl
            | true =>
              exact absurd (sampledQuery_verify_length 2 x _ hv) (show ¬ (1 : Nat) = 2 by decide)
        show acceptBit ((whirOracleIop sampledQueryEnv sampledQuerySched 2).verify x [(m, 0)]) +
          (acceptBit ((whirOracleIop sampledQueryEnv sampledQuerySched 2).verify x [(m, 1)]) +
          (acceptBit ((whirOracleIop sampledQueryEnv sampledQuerySched 2).verify x [(m, 2)]) +
          (acceptBit ((whirOracleIop sampledQueryEnv sampledQuerySched 2).verify x [(m, 3)]) + 0))) ≤ 0
        rw [hZero 0, hZero 1, hZero 2, hZero 3]
        exact Nat.le_refl 0
      | ⟨1, _⟩, [(m0, c0)], _ => exact sampledQuery_query_round_flips x hx m0 m c0
      | ⟨0, _⟩, _ :: _, h => exact absurd h (by simp only [List.length_cons]; exact Nat.succ_ne_zero _)
      | ⟨1, _⟩, [], h => exact absurd h (show ¬ (0 : Nat) = 1 by decide)
      | ⟨1, _⟩, _ :: _ :: _, h =>
        exact absurd (Nat.succ.inj h) (by simp only [List.length_cons]; exact Nat.succ_ne_zero _)
      | ⟨n + 2, hn⟩, _, _ =>
        exact absurd hn (by
          have h2 : sampledQuerySched.numRounds = 2 := by decide
          rw [h2]
          exact Nat.not_lt.mpr (Nat.le_add_left 2 n))
  }
  covers := fun r => by
    match r with
    | ⟨0, _⟩ =>
      show 0 * _ ≤ _
      rw [Nat.zero_mul]
      exact Nat.zero_le _
    | ⟨1, _⟩ =>
      show 2 * (4 ^ 1 * goldilocksPrime) ≤ ((3 + 0) ^ 1 * goldilocksPrime + 100 * (1 + 0) * 4 ^ 1) * 2 ^ 2
      decide
    | ⟨n + 2, hn⟩ =>
      exact absurd hn (by
        have h2 : sampledQuerySched.numRounds = 2 := by decide
        rw [h2]
        exact Nat.not_lt.mpr (Nat.le_add_left 2 n))

/-- The query round's flip count is not zero: the certificate is not the all-rejecting one. -/
theorem sampledQueryCert_query_round_bad :
    sampledQueryCert.cert.bad ⟨1, by decide⟩ = 2 := by rfl

/-- The all-ones table with claim `1` and the committed constant `1` is accepted on every query
    challenge. -/
theorem sampledQuery_honest_accepts :
    (whirOracleIop sampledQueryEnv sampledQuerySched 2).verify
        ⟨[Goldilocks.one, Goldilocks.one, Goldilocks.one, Goldilocks.one], Goldilocks.one⟩
        [(⟨[], [Goldilocks.one], []⟩, 0), (⟨[], [], []⟩, 0)] = true ∧
    (whirOracleIop sampledQueryEnv sampledQuerySched 2).verify
        ⟨[Goldilocks.one, Goldilocks.one, Goldilocks.one, Goldilocks.one], Goldilocks.one⟩
        [(⟨[], [Goldilocks.one], []⟩, 0), (⟨[], [], []⟩, 1)] = true ∧
    (whirOracleIop sampledQueryEnv sampledQuerySched 2).verify
        ⟨[Goldilocks.one, Goldilocks.one, Goldilocks.one, Goldilocks.one], Goldilocks.one⟩
        [(⟨[], [Goldilocks.one], []⟩, 0), (⟨[], [], []⟩, 2)] = true ∧
    (whirOracleIop sampledQueryEnv sampledQuerySched 2).verify
        ⟨[Goldilocks.one, Goldilocks.one, Goldilocks.one, Goldilocks.one], Goldilocks.one⟩
        [(⟨[], [Goldilocks.one], []⟩, 0), (⟨[], [], []⟩, 3)] = true :=
  ⟨(sampledQuery_verify_iff 2 _ _ _ 0 0).mpr ⟨rfl, by decide, by decide, by decide⟩,
   (sampledQuery_verify_iff 2 _ _ _ 0 1).mpr ⟨rfl, by decide, by decide, by decide⟩,
   (sampledQuery_verify_iff 2 _ _ _ 0 2).mpr ⟨rfl, by decide, by decide, by decide⟩,
   (sampledQuery_verify_iff 2 _ _ _ 0 3).mpr ⟨rfl, by decide, by decide, by decide⟩⟩

/-- The all-ones table with claim `0` is outside the language: a polynomial `c₀ + c₁ X` with
    value `0` at `0` misses the table there, and agreement at `1` forces `c₁ = 1`, which misses
    the table at `2`. -/
theorem sampledQuery_false_not_inLang :
    ¬ whirInLang sampledQueryEnv sampledQuerySched
      ⟨[Goldilocks.one, Goldilocks.one, Goldilocks.one, Goldilocks.one], Goldilocks.zero⟩ := by
  rintro ⟨P, hLen, hAgree, hClaim⟩
  rw [sampledQuery_agreeCount] at hAgree
  have hZeroEq : Goldilocks.ofNat 0 = CommRingOps.zero := by decide
  have hOneEq : Goldilocks.ofNat 1 = CommRingOps.one := by decide
  have hClaim0 : RoundPoly.evalCoeffs P CommRingOps.zero = Goldilocks.zero := hClaim
  have hA0 : decide (RoundPoly.evalCoeffs P (Goldilocks.ofNat 0) =
      ([Goldilocks.one, Goldilocks.one, Goldilocks.one, Goldilocks.one] : List Goldilocks).getD 0
        CommRingOps.zero) = false := by
    rw [hZeroEq, hClaim0]
    decide
  rw [hA0] at hAgree
  have hBoth : ∀ a1 a2 a3 : Bool, 2 ^ sampledQueryStage.foldK * sampledQueryStage.agree ≤
      acceptBit false + acceptBit a1 + acceptBit a2 + acceptBit a3 → a1 = true ∧ a2 = true := by
    intro a1 a2 a3
    cases a1 <;> cases a2 <;> cases a3 <;> decide
  obtain ⟨h1, h2⟩ := hBoth _ _ _ hAgree
  have he1 := of_decide_eq_true h1
  have he2 := of_decide_eq_true h2
  rcases P with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, rest⟩⟩⟩
  · exact (by decide : (CommRingOps.zero : Goldilocks) ≠ Goldilocks.one) he1
  · have hc0 : c0 = Goldilocks.zero := by
      dsimp only [RoundPoly.evalCoeffs] at hClaim0
      rw [LawfulCommRing.mul_zero, LawfulCommRing.add_zero] at hClaim0
      exact hClaim0
    subst hc0
    exact (by decide : RoundPoly.evalCoeffs [Goldilocks.zero] (Goldilocks.ofNat 1) ≠
      ([Goldilocks.one, Goldilocks.one, Goldilocks.one, Goldilocks.one] : List Goldilocks).getD 1
        CommRingOps.zero) he1
  · have hc0 : c0 = Goldilocks.zero := by
      dsimp only [RoundPoly.evalCoeffs] at hClaim0
      rw [LawfulCommRing.zero_mul, LawfulCommRing.add_zero] at hClaim0
      exact hClaim0
    subst hc0
    have hc1 : c1 = Goldilocks.one := by
      dsimp only [RoundPoly.evalCoeffs] at he1
      rw [LawfulCommRing.mul_zero, LawfulCommRing.add_zero, hOneEq, LawfulCommRing.one_mul] at he1
      exact (LawfulCommRing.zero_add c1).symm.trans he1
    subst hc1
    exact (by decide : RoundPoly.evalCoeffs [Goldilocks.zero, Goldilocks.one] (Goldilocks.ofNat 2) ≠
      ([Goldilocks.one, Goldilocks.one, Goldilocks.one, Goldilocks.one] : List Goldilocks).getD 2
        CommRingOps.zero) he2
  · have h3 : rest.length + 3 ≤ 2 := hLen
    exact absurd (Nat.le_trans (Nat.le_add_left 3 rest.length) h3) (by decide)

/-- That false statement is still accepted on one challenge: with the committed polynomial `X`
    the query at position `1` passes. The verifier's soundness error is not zero, and the
    certificate's count of two is an upper bound on a real event. -/
theorem sampledQuery_false_statement_accepted_once :
    (whirOracleIop sampledQueryEnv sampledQuerySched 2).verify
        ⟨[Goldilocks.one, Goldilocks.one, Goldilocks.one, Goldilocks.one], Goldilocks.zero⟩
        [(⟨[], [Goldilocks.zero, Goldilocks.one], []⟩, 0), (⟨[], [], []⟩, 1)] = true ∧
    (whirOracleIop sampledQueryEnv sampledQuerySched 2).verify
        ⟨[Goldilocks.one, Goldilocks.one, Goldilocks.one, Goldilocks.one], Goldilocks.zero⟩
        [(⟨[], [Goldilocks.zero, Goldilocks.one], []⟩, 0), (⟨[], [], []⟩, 2)] = false :=
  ⟨(sampledQuery_verify_iff 2 _ _ _ 0 1).mpr ⟨rfl, by decide, by decide, by decide⟩,
   Bool.eq_false_iff.mpr (fun h =>
     absurd ((sampledQuery_verify_iff 2 _ _ _ 0 2).mp h).2.2.2 (by decide))⟩

/-! ## §5b. Unconditional Multi-Stage `[CWYZ26]` Sliced-MCA `WhirScheduleCert` (`flatHemSlicedCert`)

Two-stage (`6`-round) WHIR verifier schedule `flatHemSlicedSched` (`64 → 32 → 16` coset chain
`hemFoldDom64 → hemFoldDom32 → hemFoldDom16` over `QuarticGoldilocks`, challenge pool
`|flatHemPool| = 2^62`, Fiat–Shamir digest width `w = 256`) whose `WhirScheduleCert` is proved
unconditionally using **only the proved `[CWYZ26]` sliced MCA counts**
(`sliced_singleStep_bridge_four_challenge_bound`, `WhirStage.decode_list_le`), exercising fold,
out-of-domain, and shift-query rounds across multiple stages with `scheduleQromError < 2^-20 < 1`. -/

set_option maxRecDepth 100000

/-- Challenge pool cardinality `q = 2^62 < goldilocksPrime` (exact power of two so `2^256` splits
    into uniform fibers over `S^4`, `S^2`, and `[0, n_i)^t_i × S`). -/
def flatHemQ : Nat := 2 ^ 62

theorem flatHemQ_pos : 0 < flatHemQ := Nat.two_pow_pos 62

/-- Duplicate-free challenge pool of `2^62` base-field elements in `QuarticGoldilocks`. -/
def flatHemPool : List QuarticGoldilocks :=
  (List.range flatHemQ).map hemFoldQg

theorem flatHemPool_length : flatHemPool.length = flatHemQ := by
  unfold flatHemPool
  rw [List.length_map, List.length_range]

private theorem nodup_append_disj {α : Type} :
    ∀ {l₁ l₂ : List α}, l₁.Nodup → l₂.Nodup → (∀ x ∈ l₁, ∀ y ∈ l₂, x ≠ y) → (l₁ ++ l₂).Nodup
  | [], _, _, h2, _ => h2
  | a :: l₁, l₂, h1, h2, hDisj => by
    obtain ⟨hNot1, hTail1⟩ := List.pairwise_cons.mp h1
    refine List.Pairwise.cons ?_
      (nodup_append_disj hTail1 h2 (fun x hx y hy => hDisj x (List.mem_cons_of_mem a hx) y hy))
    intro y hy hEq
    rcases List.mem_append.mp hy with hy1 | hy2
    · exact hNot1 y hy1 hEq
    · exact hDisj a List.mem_cons_self y hy2 hEq

private theorem hemFoldQg_inj_lt {a b : Nat} (ha : a < flatHemQ) (hb : b < flatHemQ)
    (hEq : hemFoldQg a = hemFoldQg b) : a = b := by
  have hv : ((hemFoldQg a).c0.c0).val = ((hemFoldQg b).c0.c0).val :=
    congrArg (fun x => x.c0.c0.val) hEq
  unfold hemFoldQg at hv
  dsimp only [Goldilocks.ofNat] at hv
  have hp : flatHemQ < goldilocksPrime := by unfold flatHemQ goldilocksPrime; decide
  rw [Nat.mod_eq_of_lt (Nat.lt_trans ha hp), Nat.mod_eq_of_lt (Nat.lt_trans hb hp)] at hv
  exact hv

private theorem flatHemPool_prefix_nodup :
    ∀ k : Nat, k ≤ flatHemQ → ((List.range k).map hemFoldQg).Nodup
  | 0, _ => .nil
  | k + 1, hk => by
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil]
    refine nodup_append_disj (flatHemPool_prefix_nodup k (Nat.le_of_succ_le hk))
      (List.Pairwise.cons (fun _ h => nomatch h) .nil) ?_
    intro x hx y hy hEq
    rcases List.mem_map.mp hx with ⟨a, haMem, rfl⟩
    have haLt : a < k := List.mem_range.mp haMem
    rcases List.mem_cons.mp hy with rfl | hNil
    · have haEq := hemFoldQg_inj_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_of_lt haLt) hk) hk hEq
      omega
    · exact nomatch hNil

theorem flatHemPool_nodup : flatHemPool.Nodup :=
  flatHemPool_prefix_nodup flatHemQ (Nat.le_refl flatHemQ)

theorem flatHemPool_getD (u : Nat) (hu : u < flatHemQ) :
    flatHemPool.getD u CommRingOps.zero = hemFoldQg u :=
  range_map_getD_of_lt hemFoldQg CommRingOps.zero flatHemQ u hu

/-- Stage 0 of `flatHemSlicedSched`: `64 → 32` coset fold (`n = 32, d = 3, A = 20, L = 33`),
    `mcaNum` derived directly from `[CWYZ26]` `slicedRest 32 3 21 12 (1 * 21 - 3) 3 flatHemQ`. -/
def flatHemStage0 : WhirStage where
  foldK := 1
  logDomain := 5
  logInvRate := 4
  oodCount := 2
  queryCount := 36
  degBound := 3
  agree := 20
  etaNum := 1
  etaDen := 20
  listSize := 33
  sumcheckDeg := 4
  mcaNum := natCeilDiv (3 + slicedRest 32 3 21 12 (1 * 21 - 3) 3 flatHemQ) flatHemQ + 4 * 33 * 33

/-- Stage 1 of `flatHemSlicedSched`: `32 → 16` coset fold (`n = 16, d = 2, A = 10, L = 29`),
    `mcaNum` derived directly from `[CWYZ26]` `slicedRest 16 2 11 7 (2 * 11 - 4) 4 flatHemQ`. -/
def flatHemStage1 : WhirStage where
  foldK := 1
  logDomain := 4
  logInvRate := 3
  oodCount := 2
  queryCount := 46
  degBound := 2
  agree := 10
  etaNum := 1
  etaDen := 20
  listSize := 29
  sumcheckDeg := 4
  mcaNum := natCeilDiv (4 + slicedRest 16 2 11 7 (2 * 11 - 4) 4 flatHemQ) flatHemQ + 4 * 29 * 29

/-- **Two-stage WHIR verifier schedule (`flatHemSlicedSched`)** backed exclusively by proved
    `[CWYZ26]` sliced MCA counts. -/
def flatHemSlicedSched : WhirVerifierSchedule where
  nv := 6
  fieldCard := flatHemQ
  fieldPos := flatHemQ_pos
  stages := [flatHemStage0, flatHemStage1]

theorem flatHemStage_mcaNums_eq :
    flatHemStage0.mcaNum = 6110 ∧ flatHemStage1.mcaNum = 7541 := by
  decide +kernel

theorem flatHemSlicedSched_shape :
    flatHemSlicedSched.stages.length = 2 ∧
    flatHemSlicedSched.johnsonOk = true ∧
    flatHemSlicedSched.numRounds = 6 := by
  refine ⟨rfl, ?_, rfl⟩
  decide +kernel

private theorem binom2_33 : binom2 33 = 528 := by
  rw [binom2_eq]

private theorem binom2_29 : binom2 29 = 406 := by
  rw [binom2_eq]

private theorem sumList_same_den (D : Nat) (hD : 0 < D) :
    ∀ (nums : List Nat),
      RatBound.le (RatBound.sumList (nums.map (fun a => (⟨a, D, hD⟩ : RatBound))))
        ⟨nums.sum, D, hD⟩
  | [] => by show 0 * D ≤ 0 * 1; simp
  | a :: as => by
    refine RatBound.le_trans
      (RatBound.add_le_add (RatBound.le_refl _) (sumList_same_den D hD as)) ?_
    show (a * D + as.sum * D) * D ≤ (a + as.sum) * (D * D)
    rw [← Nat.add_mul, Nat.mul_assoc]
    exact Nat.le_refl _

/-- Concrete `< 2^-20` QROM error budget at `Q = 0` and `< 1` budget through `Q = 256` on
    `flatHemSlicedSched`. -/
theorem flatHemSlicedSched_error_bits :
    atLeastBits 20 (scheduleQromError flatHemSlicedSched 0) ∧
    RatBound.lt (scheduleQromError flatHemSlicedSched 256) RatBound.one := by
  have hD24 : 0 < 2 ^ 24 := by decide
  have hStage0 : RoundBoundsLe (flatHemStage0.roundBounds flatHemQ flatHemQ_pos)
      [⟨1, 2 ^ 24, hD24⟩, ⟨1, 2 ^ 24, hD24⟩, ⟨8, 2 ^ 24, hD24⟩] := by
    refine RoundBoundsLe.append (.cons ?_ .nil) (.cons ?_ (.cons ?_ .nil))
    · show (flatHemStage0.listSize * flatHemStage0.sumcheckDeg + flatHemStage0.mcaNum) * 2 ^ 24 ≤
        1 * flatHemQ
      decide +kernel
    · show binom2 33 * 3 ^ 2 * 2 ^ 24 ≤ 1 * flatHemQ ^ 2
      rw [binom2_33]; decide +kernel
    · show ((20 + 1) ^ 36 * flatHemQ + 33 * (36 + 2) * 32 ^ 36) * 2 ^ 24 ≤
        8 * (32 ^ 36 * flatHemQ)
      decide +kernel
  have hStage1 : RoundBoundsLe (flatHemStage1.roundBounds flatHemQ flatHemQ_pos)
      [⟨1, 2 ^ 24, hD24⟩, ⟨1, 2 ^ 24, hD24⟩, ⟨1, 2 ^ 24, hD24⟩] := by
    refine RoundBoundsLe.append (.cons ?_ .nil) (.cons ?_ (.cons ?_ .nil))
    · show (flatHemStage1.listSize * flatHemStage1.sumcheckDeg + flatHemStage1.mcaNum) * 2 ^ 24 ≤
        1 * flatHemQ
      decide +kernel
    · show binom2 29 * 2 ^ 2 * 2 ^ 24 ≤ 1 * flatHemQ ^ 2
      rw [binom2_29]; decide +kernel
    · show ((10 + 1) ^ 46 * flatHemQ + 29 * (46 + 2) * 16 ^ 46) * 2 ^ 24 ≤
        1 * (16 ^ 46 * flatHemQ)
      decide +kernel
  have hCov : RoundBoundsLe flatHemSlicedSched.roundBounds
      ([1, 1, 8, 1, 1, 1].map (fun a => (⟨a, 2 ^ 24, hD24⟩ : RatBound))) :=
    RoundBoundsLe.append hStage0 (RoundBoundsLe.append hStage1 .nil)
  have hBoundQ : ∀ Q : Nat,
      RatBound.le (scheduleQromError flatHemSlicedSched Q)
        ⟨([1, 1, 8, 1, 1, 1].map (fun a => (2 * Q + 1) ^ 2 * a)).sum, 2 ^ 24, hD24⟩ := by
    intro Q
    refine RatBound.le_trans (scaled_sum_mono Q hCov) ?_
    exact sumList_same_den (2 ^ 24) hD24
      ([1, 1, 8, 1, 1, 1].map (fun a => (2 * Q + 1) ^ 2 * a))
  refine ⟨?_, ?_⟩
  · apply atLeastBits_of_le (hBoundQ 0)
    show ([1, 1, 8, 1, 1, 1].map (fun a => (2 * 0 + 1) ^ 2 * a)).sum * 2 ^ 20 ≤ 2 ^ 24
    decide +kernel
  · have hRatLt : ∀ {a b c : RatBound}, RatBound.le a b → RatBound.lt b c → RatBound.lt a c := by
      intro a b c h1 h2
      unfold RatBound.le RatBound.lt at *
      have m1 : a.num * b.den * c.den ≤ b.num * a.den * c.den := Nat.mul_le_mul_right c.den h1
      have m2 : b.num * c.den * a.den < c.num * b.den * a.den :=
        nat_mul_lt_mul_right' h2 a.h_pos
      have e1 : a.num * c.den * b.den = a.num * b.den * c.den := by rw [Nat.mul_right_comm]
      have e2 : b.num * a.den * c.den = b.num * c.den * a.den := by rw [Nat.mul_right_comm]
      have e3 : c.num * b.den * a.den = c.num * a.den * b.den := by rw [Nat.mul_right_comm]
      have hChain : a.num * c.den * b.den < c.num * a.den * b.den := by
        rw [e1, ← e3]
        exact Nat.lt_of_le_of_lt m1 (e2 ▸ m2)
      exact nat_lt_of_mul_lt_mul_right' hChain
    refine hRatLt (hBoundQ 256) ?_
    rw [RatBound.one_eq]
    show ([1, 1, 8, 1, 1, 1].map (fun a => (2 * 256 + 1) ^ 2 * a)).sum * 1 < 1 * 2 ^ 24
    decide +kernel

/-- Halves-order evaluation point lookup on a `2n`-point antipodal domain `D_in`. -/
def halfDomPt (D_in : List QuarticGoldilocks) (n p : Nat) : QuarticGoldilocks :=
  if p < n then D_in.getD (2 * p) CommRingOps.zero
  else D_in.getD (2 * (p - n) + 1) CommRingOps.zero

/-- Inverse halves-to-interleaved oracle adapter: maps halves-ordered `(pos, pos + n)` to
    adjacent antipodal pairs `(2 * pos, 2 * pos + 1)`. -/
def interleaveOracle (n : Nat) (raw : Nat → QuarticGoldilocks) (idx : Nat) : QuarticGoldilocks :=
  if idx % 2 = 0 then raw (idx / 2) else raw (idx / 2 + n)

/-- Decode a 4-challenge quadruple `(φ, θ, α, β) ∈ flatHemPool⁴` from `c % q⁴`. -/
def decodeQuad (c : Nat) :
    QuarticGoldilocks × QuarticGoldilocks × QuarticGoldilocks × QuarticGoldilocks :=
  let q := flatHemQ
  let idx := c % (q * (q * (q * q)))
  let iβ := idx % q
  let r1 := idx / q
  let iα := r1 % q
  let r2 := r1 / q
  let iθ := r2 % q
  let iφ := r2 / q
  (hemFoldQg iφ, hemFoldQg iθ, hemFoldQg iα, hemFoldQg iβ)

/-- Decode a 2-challenge OOD pair `(z₀, z₁) ∈ flatHemPool²` from `c % q²`. -/
def decodeOod (c : Nat) : QuarticGoldilocks × QuarticGoldilocks :=
  let q := flatHemQ
  let idx := c % (q * q)
  (hemFoldQg (idx / q), hemFoldQg (idx % q))

/-- Local copy of the `[CWYZ26]` 5-wire dual-bridge claim update so kernel evaluation inside
    `ClosedWhirSchedule` unfolds directly. -/
def flatHemBridgeClaim (claim w₀ w₁ w₂ c_F c_G φ θ α β : QuarticGoldilocks) :
    QuarticGoldilocks :=
  CommRingOps.add
    (CommRingOps.add w₂ (CommRingOps.mul φ (CommRingOps.sub claim w₀)))
    (CommRingOps.add
      (CommRingOps.mul α
        (CommRingOps.add (CommRingOps.add w₀ (CommRingOps.mul φ w₁))
          (CommRingOps.mul θ
            (CommRingOps.add w₂ (CommRingOps.mul φ (CommRingOps.sub claim w₀))))))
      (CommRingOps.mul β (CommRingOps.add c_F (CommRingOps.mul θ c_G))))

theorem flatHemBridgeClaim_eq (claim w₀ w₁ w₂ c_F c_G φ θ α β : QuarticGoldilocks) :
    flatHemBridgeClaim claim w₀ w₁ w₂ c_F c_G φ θ α β =
      hemBridgeFoldClaim claim w₀ w₁ w₂ c_F c_G φ θ α β :=
  (hemBridgeFoldClaim_def claim w₀ w₁ w₂ c_F c_G φ θ α β).symm

/-- Local copy of `hemKernelFold` for direct kernel evaluation. -/
def flatHemKernelFold (φ : QuarticGoldilocks) : List QuarticGoldilocks → List QuarticGoldilocks
  | a :: b :: rest => CommRingOps.add a (CommRingOps.mul φ b) :: flatHemKernelFold φ rest
  | _ => [CommRingOps.zero]

theorem flatHemKernelFold_eq (φ : QuarticGoldilocks) :
    ∀ K : List QuarticGoldilocks, flatHemKernelFold φ K = hemKernelFold φ K
  | a :: b :: rest => by
    rw [hemKernelFold.public_eqs.1, ← flatHemKernelFold_eq φ rest]; rfl
  | [] => (hemKernelFold.public_eqs.2 _ _ (by intro _ _ _ h; cases h)).symm
  | [_] => (hemKernelFold.public_eqs.2 _ _ (by intro _ _ _ h; cases h)).symm

/-- Local copy of single-fiber `[CWYZ26]` coset folding on a halves-ordered `[v0, v1]` block. -/
def flatHemFoldPoint (D_in D_out : List QuarticGoldilocks)
    (θ α β : QuarticGoldilocks) (pos : Nat) (v0 v1 : QuarticGoldilocks) : QuarticGoldilocks :=
  let two := CommRingOps.add CommRingOps.one CommRingOps.one
  let x := D_in.getD (2 * pos) CommRingOps.one
  let y := D_out.getD pos CommRingOps.zero
  let fE := CommRingOps.mul (LawfulField.inv two) (CommRingOps.add v0 v1)
  let fO := CommRingOps.mul (LawfulField.inv (CommRingOps.mul two x)) (CommRingOps.sub v0 v1)
  let hComb := CommRingOps.add fE (CommRingOps.mul θ fO)
  CommRingOps.add fO (CommRingOps.mul (CommRingOps.add α (CommRingOps.mul β y)) hComb)

theorem flatHemFoldPoint_eq_virtual (D_in D_out : List QuarticGoldilocks) (n : Nat)
    (raw : Nat → QuarticGoldilocks) (θ α β : QuarticGoldilocks) (pos : Nat) :
    flatHemFoldPoint D_in D_out θ α β pos (raw pos) (raw (pos + n)) =
      hemVirtualFoldOracle θ α β D_in D_out (interleaveOracle n raw) pos := by
  have hEven : interleaveOracle n raw (2 * pos) = raw pos := by
    unfold interleaveOracle
    have hm : (2 * pos) % 2 = 0 := by omega
    have hd : (2 * pos) / 2 = pos := by omega
    rw [ite_true_eq _ _ hm, hd]
  have hOdd : interleaveOracle n raw (2 * pos + 1) = raw (pos + n) := by
    unfold interleaveOracle
    have hm : ¬ ((2 * pos + 1) % 2 = 0) := by omega
    have hd : (2 * pos + 1) / 2 = pos := by omega
    rw [ite_false_eq _ _ hm, hd]
  rw [hemVirtualFoldOracle_def, hEven, hOdd]
  rfl

/-- Initial length-10 evaluation-at-0 kernel `[1, 0, ..., 0]`. -/
def flatHemInitKernel : List QuarticGoldilocks :=
  [CommRingOps.one, CommRingOps.zero, CommRingOps.zero, CommRingOps.zero, CommRingOps.zero,
   CommRingOps.zero, CommRingOps.zero, CommRingOps.zero, CommRingOps.zero, CommRingOps.zero]

/-- Length-6 point-evaluation kernel `[1, x, x², x³, 0, 0]` for degree-`≤ 3` polynomials. -/
def evalVec6 (x : QuarticGoldilocks) : List QuarticGoldilocks :=
  let x2 := CommRingOps.mul x x
  let x3 := CommRingOps.mul x x2
  [CommRingOps.one, x, x2, x3, CommRingOps.zero, CommRingOps.zero]

def vecAdd6 (u v : List QuarticGoldilocks) : List QuarticGoldilocks :=
  List.zipWith CommRingOps.add u v

def vecScale6 (s : QuarticGoldilocks) (u : List QuarticGoldilocks) : List QuarticGoldilocks :=
  u.map (CommRingOps.mul s)

/-- Fold evaluation points `pts` into a length-6 kernel `K` with powers of `γ` matching
    `combineClaim`. -/
def combineKernel6 (K : List QuarticGoldilocks) (γ : QuarticGoldilocks)
    (pts : List QuarticGoldilocks) : List QuarticGoldilocks :=
  (pts.foldl (fun (acc : List QuarticGoldilocks × QuarticGoldilocks) pt =>
    (vecAdd6 acc.1 (vecScale6 acc.2 (evalVec6 pt)), CommRingOps.mul acc.2 γ)) (K, γ)).1

def flatHemChalPos (c j n : Nat) : Nat :=
  let t := if n = 32 then 36 else 46
  let cs := c % (n ^ t * flatHemQ)
  let qIdx := cs / flatHemQ
  (qIdx / n ^ j) % n

def flatHemChalField (c slot : Nat) : QuarticGoldilocks :=
  if slot = 0 then (decodeOod c).1
  else if slot = 1 then (decodeOod c).2
  else if slot = 36 then hemFoldQg ((c % (32 ^ 36 * flatHemQ)) % flatHemQ)
  else hemFoldQg ((c % (16 ^ 46 * flatHemQ)) % flatHemQ)

def flatHemStepClaim (_stageIdx : Nat) (curClaim : QuarticGoldilocks)
    (wires : List QuarticGoldilocks) (c : Nat) : Option QuarticGoldilocks :=
  if wires.length ≤ 5 then
    let q := decodeQuad c
    let w₀ := wires.getD 0 CommRingOps.zero
    let w₁ := wires.getD 1 CommRingOps.zero
    let w₂ := wires.getD 2 CommRingOps.zero
    let cF := wires.getD 3 CommRingOps.zero
    let cG := wires.getD 4 CommRingOps.zero
    some (flatHemBridgeClaim curClaim w₀ w₁ w₂ cF cG q.1 q.2.1 q.2.2.1 q.2.2.2)
  else none

def flatHemRawFold (stageIdx : Nat) (folds : List (WhirPub QuarticGoldilocks × Nat))
    (_j pos : Nat) (block : List QuarticGoldilocks) : QuarticGoldilocks :=
  let c := match folds with | (_, c0) :: _ => c0 | [] => 0
  let q := decodeQuad c
  let v0 := block.getD 0 CommRingOps.zero
  let v1 := block.getD 1 CommRingOps.zero
  if stageIdx = 0 then
    flatHemFoldPoint hemFoldDom64 hemFoldDom32 q.2.1 q.2.2.1 q.2.2.2 pos v0 v1
  else
    flatHemFoldPoint hemFoldDom32 hemFoldDom16 q.2.1 q.2.2.1 q.2.2.2 pos v0 v1

def flatHemFinalClaimViews (views : List (StageView QuarticGoldilocks))
    (_αs : List QuarticGoldilocks) : QuarticGoldilocks :=
  match views with
  | [v0, v1] =>
    let c0 := match v0.folds with | (_, c) :: _ => c | [] => 0
    let c3 := match v1.folds with | (_, c) :: _ => c | [] => 0
    let φ₀ := (decodeQuad c0).1
    let φ₁ := (decodeQuad c3).1
    let ood0 := decodeOod v0.commit.2
    let γ₀ := flatHemChalField v0.answer.2 36
    let qPts0 := (List.range 36).map (fun j =>
      hemFoldDom32.getD (flatHemChalPos v0.answer.2 j 32) CommRingOps.zero)
    let K0' := flatHemKernelFold φ₀ flatHemInitKernel
    let K1 := combineKernel6 K0' γ₀ ([ood0.1, ood0.2] ++ qPts0)
    let K2 := flatHemKernelFold φ₁ K1
    ringDot v1.commit.1.poly K2
  | _ => CommRingOps.zero

/-- **`WhirEnv` for the two-stage `[CWYZ26]` schedule `flatHemSlicedSched`.** -/
def flatHemSlicedEnv : WhirEnv QuarticGoldilocks where
  chalField := flatHemChalField
  chalPos := flatHemChalPos
  domPt i p :=
    if i = 0 then halfDomPt hemFoldDom64 32 p
    else if i = 1 then halfDomPt hemFoldDom32 16 p
    else hemFoldDom16.getD p CommRingOps.zero
  fold2 _ _ a _ := a
  finalClaim P _ := RoundPoly.evalCoeffs P CommRingOps.zero
  initClaim P := ringDot P flatHemInitKernel
  finalDeg := 2
  foldClaimStep := some flatHemStepClaim
  foldBlockRaw := some flatHemRawFold
  finalClaimViews := some flatHemFinalClaimViews

/-- Computable Boolean witness test via `gsDecodeList`. -/
def hasValidWitness (d A : Nat) (D : List QuarticGoldilocks)
    (O : Nat → QuarticGoldilocks) (kernel : List QuarticGoldilocks)
    (claim : QuarticGoldilocks) : Bool :=
  (gsDecodeList d A D (lookupDomOracle D O)).any (fun P =>
    decide (ringDot P.coeffs kernel = claim))

/-- Unordered-pair OOD collision check across a candidate list `cands`. -/
def oodCollidesAux : List (GsUniPoly QuarticGoldilocks) →
    QuarticGoldilocks → QuarticGoldilocks → Bool
  | [], _, _ => false
  | P :: rest, z₀, z₁ =>
    rest.any (fun Q =>
      decide (RoundPoly.evalCoeffs P.coeffs z₀ = RoundPoly.evalCoeffs Q.coeffs z₀) &&
      decide (RoundPoly.evalCoeffs P.coeffs z₁ = RoundPoly.evalCoeffs Q.coeffs z₁)) ||
    oodCollidesAux rest z₀ z₁

private theorem antipodal_64_32 : IsAntipodalDomainPair hemFoldDom64 hemFoldDom32 := by
  have h := hemFoldStageGeom_antipodal hemFoldWitnessGeom1
  rw [hemFoldWitnessStage1.public_eqs] at h
  exact h

private theorem antipodal_32_16 : IsAntipodalDomainPair hemFoldDom32 hemFoldDom16 := by
  have h := hemFoldStageGeom_antipodal hemFoldWitnessGeom2
  rw [hemFoldWitnessStage2.public_eqs] at h
  exact h

private theorem hemFoldDom64_len : hemFoldDom64.length = 64 := rfl
private theorem hemFoldDom16_len : hemFoldDom16.length = 16 := rfl
private theorem hemFoldDom32_len : hemFoldDom32.length = 32 := by
  have h := antipodal_64_32.len_eq
  rw [hemFoldDom64_len] at h
  omega

private theorem hasValidWitness_true_iff (d A : Nat) (D : List QuarticGoldilocks)
    (hD : D.Nodup) (hdA : d + 1 ≤ A)
    (O : Nat → QuarticGoldilocks) (kernel : List QuarticGoldilocks)
    (claim : QuarticGoldilocks) :
    hasValidWitness d A D O kernel claim = true ↔
      ∃ Q : List QuarticGoldilocks, polyWitnessValid D A d O kernel claim Q = true := by
  unfold hasValidWitness
  constructor
  · intro h
    obtain ⟨P, hPMem, hPDot⟩ := List.any_eq_true.mp h
    obtain ⟨hPLen, hPAg⟩ := (mem_gsDecodeList_iff (lookupDomOracle D O) hD hdA P).mp hPMem
    refine ⟨P.coeffs, ?_⟩
    rw [polyWitnessValid_def, hemCosetAgreeCount_eq_filter_lookup D O P.coeffs hD,
        decide_eq_true hPLen, decide_eq_true hPAg,
        decide_eq_true (of_decide_eq_true hPDot)]
    rfl
  · rintro ⟨Q, hQ⟩
    rw [polyWitnessValid_def] at hQ
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hQ
    rw [hemCosetAgreeCount_eq_filter_lookup D O Q hD] at hQ
    let P : GsUniPoly QuarticGoldilocks := GsUniPoly.ofCoeffs Q
    have hPVal : P.coeffs = trimPoly Q := rfl
    have hPLen : P.coeffs.length ≤ d + 1 := by
      rw [hPVal]; exact Nat.le_trans (trimPoly_length_le Q) hQ.1.1
    have hFiltEq : D.filter (fun z => decide (RoundPoly.evalCoeffs P.coeffs z = lookupDomOracle D O z)) =
        D.filter (fun z => decide (RoundPoly.evalCoeffs Q z = lookupDomOracle D O z)) :=
      congrArg (fun p => List.filter p D) (funext fun z => by
        rw [hPVal, evalCoeffs_trimPoly])
    have hPMem : P ∈ gsDecodeList d A D (lookupDomOracle D O) :=
      (mem_gsDecodeList_iff (lookupDomOracle D O) hD hdA P).mpr ⟨hPLen, by rw [hFiltEq]; exact hQ.1.2⟩
    have hPDot : ringDot P.coeffs kernel = claim := by
      rw [hPVal, ringDot_trimPoly_eq]; exact hQ.2
    exact List.any_eq_true.mpr ⟨P, hPMem, decide_eq_true hPDot⟩

private theorem hasValidWitness_false_imp (d A : Nat) (D : List QuarticGoldilocks)
    (hD : D.Nodup) (hdA : d + 1 ≤ A)
    (O : Nat → QuarticGoldilocks) (kernel : List QuarticGoldilocks)
    (claim : QuarticGoldilocks)
    (hFalse : hasValidWitness d A D O kernel claim = false) :
    ∀ Q : List QuarticGoldilocks, polyWitnessValid D A d O kernel claim Q = false := by
  intro Q
  cases hQ : polyWitnessValid D A d O kernel claim Q with
  | false => rfl
  | true =>
    have hT := (hasValidWitness_true_iff d A D hD hdA O kernel claim).mpr ⟨Q, hQ⟩
    rw [hFalse] at hT
    exact absurd hT Bool.false_ne_true

private theorem qsum_congr_len {m n : Nat} (h : m = n) (f : Fin m → Nat) (g : Fin n → Nat)
    (hfg : ∀ (i : Fin m) (j : Fin n), i.1 = j.1 → f i = g j) :
    qsum m f = qsum n g := by
  subst h
  exact qsum_congr (fun i => hfg i i rfl)

private theorem ite_decide_eq (P : Prop) [Decidable P] :
    (if decide P = true then 1 else 0) = (if P then 1 else 0) := by
  by_cases h : P <;> simp [h]

private def qsumNat (n : Nat) (g : Nat → Nat) : Nat :=
  qsum n (fun i => g i.1)

private theorem qsumNat_zero (g : Nat → Nat) : qsumNat 0 g = 0 :=
  qsum_zero _

private theorem qsumNat_succ (n : Nat) (g : Nat → Nat) :
    qsumNat (n + 1) g = g 0 + qsumNat n (fun k => g (k + 1)) :=
  qsum_succ n _

private theorem qsumNat_congr {n : Nat} {f g : Nat → Nat} (h : ∀ k < n, f k = g k) :
    qsumNat n f = qsumNat n g :=
  qsum_congr (fun i => h i.1 i.2)

private theorem qsumNat_add_split :
    ∀ (a b : Nat) (g : Nat → Nat),
      qsumNat (a + b) g = qsumNat a g + qsumNat b (fun j => g (a + j))
  | 0, b, g => by
    rw [Nat.zero_add, qsumNat_zero, Nat.zero_add]
    exact qsumNat_congr (fun j _ => by rw [Nat.zero_add])
  | a + 1, b, g => by
    rw [Nat.succ_add, qsumNat_succ, qsumNat_succ,
        qsumNat_add_split a b (fun k => g (k + 1)), Nat.add_assoc]
    refine congrArg (g 0 + ·) (congrArg (qsumNat a _ + ·) (qsumNat_congr (fun j _ => ?_)))
    exact congrArg g (by omega)

private theorem qsumNat_mul_mod :
    ∀ (F M : Nat) (_hM : 0 < M) (g : Nat → Nat),
      qsumNat (F * M) (fun c => g (c % M)) = F * qsumNat M g
  | 0, M, _, g => by
    rw [Nat.zero_mul, qsumNat_zero, Nat.zero_mul]
  | F + 1, M, hM, g => by
    rw [Nat.succ_mul, qsumNat_add_split (F * M) M, qsumNat_mul_mod F M hM g, Nat.succ_mul]
    refine congrArg (F * qsumNat M g + ·) (qsumNat_congr (fun j hj => ?_))
    rw [Nat.add_comm (F * M) j, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

private theorem qsumNat_mul_div_mod :
    ∀ (A B : Nat) (_hB : 0 < B) (g : Nat → Nat → Nat),
      qsumNat (A * B) (fun c => g (c / B) (c % B)) =
        qsumNat A (fun i => qsumNat B (fun j => g i j))
  | 0, B, _, _ => by
    rw [Nat.zero_mul, qsumNat_zero, qsumNat_zero]
  | A + 1, B, hB, g => by
    rw [Nat.succ_mul, qsumNat_add_split (A * B) B, qsumNat_mul_div_mod A B hB g,
        qsumNat_add_split A 1, qsumNat_succ, qsumNat_zero, Nat.add_zero, Nat.add_zero]
    refine congrArg (qsumNat A _ + ·) (qsumNat_congr (fun j hj => ?_))
    have hDiv : (A * B + j) / B = A := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hj, Nat.zero_add]
    have hMod : (A * B + j) % B = j := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    rw [hDiv, hMod]

private theorem qsumNat_even_odd_split :
    ∀ (n : Nat) (g : Nat → Nat),
      qsumNat (2 * n) g =
        qsumNat n (fun k => g (2 * k)) + qsumNat n (fun k => g (2 * k + 1))
  | 0, _ => by rw [Nat.mul_zero, qsumNat_zero, qsumNat_zero, qsumNat_zero]
  | n + 1, g => by
    have e : 2 * (n + 1) = 2 + 2 * n := by omega
    rw [e, qsumNat_add_split 2 (2 * n), qsumNat_succ, qsumNat_succ, qsumNat_zero, Nat.add_zero,
        qsumNat_even_odd_split n (fun idx => g (2 + idx)),
        qsumNat_succ, qsumNat_succ]
    have h1 : qsumNat n (fun i => g (2 + 2 * i)) = qsumNat n (fun i => g (2 * (i + 1))) :=
      qsumNat_congr (fun i _ => congrArg g (by omega))
    have h2 : qsumNat n (fun i => g (2 + (2 * i + 1))) = qsumNat n (fun i => g (2 * (i + 1) + 1)) :=
      qsumNat_congr (fun i _ => congrArg g (by omega))
    have g0 : g (2 * 0) = g 0 := rfl
    have g1 : g (2 * 0 + 1) = g (0 + 1) := rfl
    rw [h1, h2, g0, g1]
    omega

theorem qsum_mul_div_mod_eq (A B : Nat) (hB : 0 < B) (g : Nat → Nat → Nat) :
    qsum (A * B) (fun c => g (c.1 / B) (c.1 % B)) =
      qsum A (fun i => qsum B (fun j => g i.1 j.1)) :=
  qsumNat_mul_div_mod A B hB g

theorem qsum_mul_mod_eq {N F M : Nat} (hN : N = F * M) (hM : 0 < M)
    (f : Fin N → Nat) (g : Nat → Nat) (hfg : ∀ c : Fin N, f c = g (c.1 % M)) :
    qsum N f = F * qsum M (fun j => g j.1) := by
  rw [qsum_congr hfg]
  change qsumNat N (fun u => g (u % M)) = F * qsumNat M g
  rw [hN, qsumNat_mul_mod F M hM g]

private theorem filter_range_eq_qsum (p : Nat → Bool) :
    ∀ n : Nat, ((List.range n).filter p).length = qsumNat n (fun i => if p i = true then 1 else 0)
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.filter_append, List.length_append, filter_range_eq_qsum p n,
        qsumNat_add_split n 1, qsumNat_succ, qsumNat_zero, Nat.add_zero, Nat.add_zero]
    dsimp only [List.filter, List.length]
    cases p n <;> simp

theorem filter_range_length_qsum (p : Nat → Bool) (n : Nat) :
    ((List.range n).filter p).length = qsum n (fun i => if p i.val then 1 else 0) :=
  filter_range_eq_qsum p n

private theorem agreeCount_flatHem_eq (table P : List QuarticGoldilocks) :
    agreeCount flatHemSlicedEnv 64 table P =
      hemCosetAgreeCount hemFoldDom64
        (interleaveOracle 32 (fun p => table.getD p CommRingOps.zero)) P := by
  unfold agreeCount
  rw [filter_range_eq_qsum, hemCosetAgreeCount_def]
  have hRhs :
      qsum hemFoldDom64.length (fun idx =>
        if interleaveOracle 32 (fun p => table.getD p CommRingOps.zero) idx.1 =
            RoundPoly.evalCoeffs P (hemFoldDom64.get idx) then 1 else 0) =
      qsumNat (2 * 32) (fun u =>
        if interleaveOracle 32 (fun p => table.getD p CommRingOps.zero) u =
            RoundPoly.evalCoeffs P (hemFoldDom64.getD u CommRingOps.zero) then 1 else 0) :=
    qsum_congr_len hemFoldDom64_len _ _ (fun idx j hij => by
      rw [← list_getD_eq_get hemFoldDom64 CommRingOps.zero idx, hij])
  rw [hRhs, show (64 : Nat) = 32 + 32 from rfl, qsumNat_add_split 32 32, qsumNat_even_odd_split 32]
  have hEvenSum :
      qsumNat 32 (fun i =>
        if decide (RoundPoly.evalCoeffs P (flatHemSlicedEnv.domPt 0 i) =
            table.getD i CommRingOps.zero) = true then 1 else 0) =
      qsumNat 32 (fun k =>
        if interleaveOracle 32 (fun p => table.getD p CommRingOps.zero) (2 * k) =
            RoundPoly.evalCoeffs P (hemFoldDom64.getD (2 * k) CommRingOps.zero) then 1 else 0) := by
    apply qsum_congr; intro k
    have hkLt : k.1 < 32 := k.2
    have hDom : flatHemSlicedEnv.domPt 0 k.1 = hemFoldDom64.getD (2 * k.1) CommRingOps.zero := by
      unfold flatHemSlicedEnv halfDomPt
      dsimp only
      rw [ite_true_eq _ _ rfl, ite_true_eq _ _ hkLt]
    have hInt : interleaveOracle 32 (fun p => table.getD p CommRingOps.zero) (2 * k.1) =
        table.getD k.1 CommRingOps.zero := by
      unfold interleaveOracle
      have hm : (2 * k.1) % 2 = 0 := by omega
      have hd : (2 * k.1) / 2 = k.1 := by omega
      rw [ite_true_eq _ _ hm, hd]
    dsimp only
    rw [hDom, hInt]
    by_cases hEq : RoundPoly.evalCoeffs P (hemFoldDom64.getD (2 * k.1) CommRingOps.zero) =
        table.getD k.1 CommRingOps.zero
    · rw [decide_eq_true hEq, ite_true_eq _ _ rfl, ite_true_eq _ _ hEq.symm]
    · have hNe' : table.getD k.1 CommRingOps.zero ≠
          RoundPoly.evalCoeffs P (hemFoldDom64.getD (2 * k.1) CommRingOps.zero) :=
        fun e => hEq e.symm
      rw [decide_eq_false hEq, ite_false_eq _ _ Bool.false_ne_true, ite_false_eq _ _ hNe']
  have hOddSum :
      qsumNat 32 (fun j =>
        if decide (RoundPoly.evalCoeffs P (flatHemSlicedEnv.domPt 0 (32 + j)) =
            table.getD (32 + j) CommRingOps.zero) = true then 1 else 0) =
      qsumNat 32 (fun k =>
        if interleaveOracle 32 (fun p => table.getD p CommRingOps.zero) (2 * k + 1) =
            RoundPoly.evalCoeffs P (hemFoldDom64.getD (2 * k + 1) CommRingOps.zero) then 1 else 0) := by
    apply qsum_congr; intro k
    have hkNotLt : ¬ (32 + k.1 < 32) := by omega
    have hkSub : 32 + k.1 - 32 = k.1 := by omega
    have hDom : flatHemSlicedEnv.domPt 0 (32 + k.1) =
        hemFoldDom64.getD (2 * k.1 + 1) CommRingOps.zero := by
      unfold flatHemSlicedEnv halfDomPt
      dsimp only
      rw [ite_true_eq _ _ rfl, ite_false_eq _ _ hkNotLt, hkSub]
    have hInt : interleaveOracle 32 (fun p => table.getD p CommRingOps.zero) (2 * k.1 + 1) =
        table.getD (32 + k.1) CommRingOps.zero := by
      unfold interleaveOracle
      have hm : ¬ ((2 * k.1 + 1) % 2 = 0) := by omega
      have hd : (2 * k.1 + 1) / 2 + 32 = 32 + k.1 := by omega
      rw [ite_false_eq _ _ hm, hd]
    dsimp only
    rw [hDom, hInt]
    by_cases hEq : RoundPoly.evalCoeffs P (hemFoldDom64.getD (2 * k.1 + 1) CommRingOps.zero) =
        table.getD (32 + k.1) CommRingOps.zero
    · rw [decide_eq_true hEq, ite_true_eq _ _ rfl, ite_true_eq _ _ hEq.symm]
    · have hNe' : table.getD (32 + k.1) CommRingOps.zero ≠
          RoundPoly.evalCoeffs P (hemFoldDom64.getD (2 * k.1 + 1) CommRingOps.zero) :=
        fun e => hEq e.symm
      rw [decide_eq_false hEq, ite_false_eq _ _ Bool.false_ne_true, ite_false_eq _ _ hNe']
  rw [hEvenSum, hOddSum]

private theorem quadPool_flatHem_len :
    (quadPool flatHemPool).length = flatHemQ * (flatHemQ * (flatHemQ * flatHemQ)) := by
  rw [quadPool_length, flatHemPool_length]
  change flatHemQ ^ 4 = flatHemQ * (flatHemQ * (flatHemQ * flatHemQ))
  decide +kernel

private theorem decodeQuad_eq_quadPool_get (idx : Fin (quadPool flatHemPool).length) :
    decodeQuad idx.1 = (quadPool flatHemPool).get idx := by
  let q := flatHemQ
  have hQPos : 0 < q := flatHemQ_pos
  have hIdxLt : idx.1 < q * (q * (q * q)) := quadPool_flatHem_len ▸ idx.2
  have hMod : idx.1 % (q * (q * (q * q))) = idx.1 := Nat.mod_eq_of_lt hIdxLt
  let iβ := idx.1 % q
  let r1 := idx.1 / q
  let iα := r1 % q
  let r2 := r1 / q
  let iθ := r2 % q
  let iφ := r2 / q
  have hiβ : iβ < q := Nat.mod_lt _ hQPos
  have hiα : iα < q := Nat.mod_lt _ hQPos
  have hiθ : iθ < q := Nat.mod_lt _ hQPos
  have hr1 : idx.1 = r1 * q + iβ := by
    have h := Nat.div_add_mod idx.1 q; rw [Nat.mul_comm] at h; exact h.symm
  have hr2 : r1 = r2 * q + iα := by
    have h := Nat.div_add_mod r1 q; rw [Nat.mul_comm] at h; exact h.symm
  have hr3 : r2 = iφ * q + iθ := by
    have h := Nat.div_add_mod r2 q; rw [Nat.mul_comm] at h; exact h.symm
  have hDecomp : idx.1 = iφ * (q * (q * q)) + (iθ * (q * q) + (iα * q + iβ)) := by
    have s1 : r2 * q = iφ * (q * q) + iθ * q := by
      rw [hr3, Nat.add_mul, Nat.mul_assoc]
    have s2 : r1 * q = iφ * (q * (q * q)) + iθ * (q * q) + iα * q := by
      rw [hr2, Nat.add_mul, s1, Nat.add_mul, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc]
    rw [hr1, s2, Nat.add_assoc, Nat.add_assoc]
  have hiφ : iφ < q := by
    apply Nat.lt_of_not_ge; intro hGe
    have hLe : q * (q * (q * q)) ≤ iφ * (q * (q * q)) := Nat.mul_le_mul_right _ hGe
    dsimp only [q] at *; omega
  have h2LtNum : iα * q + iβ < q * q := by
    have h1 : (iα + 1) * q ≤ q * q := Nat.mul_le_mul_right q hiα
    rw [Nat.add_mul, Nat.one_mul] at h1
    dsimp only [q] at *; omega
  have h2Lt : iα * q + iβ < (prodPool flatHemPool).length := by
    rw [prodPool_length, flatHemPool_length]; exact h2LtNum
  have h3LtNum : iθ * (q * q) + (iα * q + iβ) < q * (q * q) := by
    have h1 : (iθ + 1) * (q * q) ≤ q * (q * q) := Nat.mul_le_mul_right (q * q) hiθ
    rw [Nat.add_mul, Nat.one_mul] at h1
    dsimp only [q] at *; omega
  have h3Lt : iθ * (q * q) + (iα * q + iβ) < (threePool flatHemPool flatHemPool).length := by
    rw [threePool_length, flatHemPool_length]; exact h3LtNum
  rw [← list_getD_eq_get (quadPool flatHemPool)
    (CommRingOps.zero, CommRingOps.zero, CommRingOps.zero, CommRingOps.zero) idx]
  have h3Len : (threePool flatHemPool flatHemPool).length = q * (q * q) := by
    rw [threePool_length, flatHemPool_length]
  have h2Len : (prodPool flatHemPool).length = q * q := by
    rw [prodPool_length, flatHemPool_length]
  conv => rhs; arg 1; rw [quadPool.public_eqs]
  have hStep1 := poolGrid_getD (fun φ t => (φ, t.1, t.2.1, t.2.2))
    (threePool flatHemPool flatHemPool) CommRingOps.zero
    (CommRingOps.zero, CommRingOps.zero, CommRingOps.zero)
    (CommRingOps.zero, CommRingOps.zero, CommRingOps.zero, CommRingOps.zero)
    (iθ * (q * q) + (iα * q + iβ)) h3Lt flatHemPool iφ
    (by rw [flatHemPool_length]; exact hiφ)
  rw [h3Len, ← hDecomp] at hStep1
  rw [hStep1, threePool.public_eqs]
  have hStep2 := poolGrid_getD (fun θ p => (θ, p.1, p.2))
    (prodPool flatHemPool) CommRingOps.zero (CommRingOps.zero, CommRingOps.zero)
    (CommRingOps.zero, CommRingOps.zero, CommRingOps.zero)
    (iα * q + iβ) h2Lt flatHemPool iθ (by rw [flatHemPool_length]; exact hiθ)
  rw [h2Len] at hStep2
  rw [hStep2]
  have hStep3 := prodPool_getD_mul flatHemPool CommRingOps.zero iα iβ
    (by rw [flatHemPool_length]; exact hiα) (by rw [flatHemPool_length]; exact hiβ)
  rw [flatHemPool_length] at hStep3
  rw [hStep3, flatHemPool_getD iφ hiφ, flatHemPool_getD iθ hiθ,
      flatHemPool_getD iα hiα, flatHemPool_getD iβ hiβ]
  unfold decodeQuad
  dsimp only [q]
  rw [hMod]

private theorem binom2_succ (m : Nat) : binom2 (m + 1) = m + binom2 m := by
  rw [binom2_eq, binom2_eq]
  have hEq : (m + 1) * m = 2 * m + m * (m - 1) := by
    cases m with
    | zero => rfl
    | succ k =>
      show (k + 2) * (k + 1) = 2 * (k + 1) + (k + 1) * k
      rw [Nat.add_comm k 2, Nat.add_mul, Nat.mul_comm (k + 1) k]
  show ((m + 1) * m) / 2 = m + (m * (m - 1)) / 2
  rw [hEq, Nat.add_comm (2 * m), Nat.add_mul_div_left _ _ (by decide : 0 < 2), Nat.add_comm]

private theorem binom2_mono {a b : Nat} (h : a ≤ b) : binom2 a ≤ binom2 b := by
  rw [binom2_eq, binom2_eq]
  exact Nat.div_le_div_right (Nat.mul_le_mul h (Nat.sub_le_sub_right h 1))

private theorem gsUniPoly_agree_pool_le {d : Nat} {P Q : GsUniPoly QuarticGoldilocks}
    (hNe : P ≠ Q) (hP : P.coeffs.length ≤ d + 1) (hQ : Q.coeffs.length ≤ d + 1) :
    qsum flatHemQ (fun u =>
      if RoundPoly.evalCoeffs P.coeffs (hemFoldQg u.1) =
          RoundPoly.evalCoeffs Q.coeffs (hemFoldQg u.1) then 1 else 0) ≤ d := by
  let pred : QuarticGoldilocks → Bool :=
    fun z => decide (RoundPoly.evalCoeffs P.coeffs z = RoundPoly.evalCoeffs Q.coeffs z)
  have hQsumEq :
      qsum flatHemQ (fun u =>
        if RoundPoly.evalCoeffs P.coeffs (hemFoldQg u.1) =
            RoundPoly.evalCoeffs Q.coeffs (hemFoldQg u.1) then 1 else 0) =
      (flatHemPool.filter pred).length := by
    rw [← qsum_get_filter_length pred flatHemPool]
    exact qsum_congr_len flatHemPool_length.symm _ _ (fun u j huj => by
      dsimp only [pred]
      rw [← list_getD_eq_get flatHemPool CommRingOps.zero j, ← huj, flatHemPool_getD u.1 u.2]
      exact (ite_decide_eq _).symm)
  rw [hQsumEq]
  apply Decidable.byContradiction
  intro hGt
  have hGe : d + 1 ≤ (flatHemPool.filter pred).length := by omega
  have hNd : (flatHemPool.filter pred).Nodup := List.Pairwise.filter _ flatHemPool_nodup
  have hTrim := trimPoly_eq_of_agree_on_nodup hP hQ hNd hGe
    (fun z hz => of_decide_eq_true (List.mem_filter.mp hz).2)
  rw [P.trimmed, Q.trimmed] at hTrim
  exact hNe (UPoly.ext hTrim)

private theorem ood_pair_collision_le {d : Nat} {P Q : GsUniPoly QuarticGoldilocks}
    (hNe : P ≠ Q) (hP : P.coeffs.length ≤ d + 1) (hQ : Q.coeffs.length ≤ d + 1) :
    qsum flatHemQ (fun u => qsum flatHemQ (fun v =>
      if (decide (RoundPoly.evalCoeffs P.coeffs (hemFoldQg u.1) =
            RoundPoly.evalCoeffs Q.coeffs (hemFoldQg u.1)) &&
          decide (RoundPoly.evalCoeffs P.coeffs (hemFoldQg v.1) =
            RoundPoly.evalCoeffs Q.coeffs (hemFoldQg v.1))) = true then 1 else 0)) ≤ d * d := by
  have h1 := gsUniPoly_agree_pool_le hNe hP hQ
  have hRow : ∀ u : Fin flatHemQ,
      qsum flatHemQ (fun v =>
        if (decide (RoundPoly.evalCoeffs P.coeffs (hemFoldQg u.1) =
              RoundPoly.evalCoeffs Q.coeffs (hemFoldQg u.1)) &&
            decide (RoundPoly.evalCoeffs P.coeffs (hemFoldQg v.1) =
              RoundPoly.evalCoeffs Q.coeffs (hemFoldQg v.1))) = true then 1 else 0) ≤
      (if RoundPoly.evalCoeffs P.coeffs (hemFoldQg u.1) =
          RoundPoly.evalCoeffs Q.coeffs (hemFoldQg u.1) then 1 else 0) * d := by
    intro u
    by_cases hu : RoundPoly.evalCoeffs P.coeffs (hemFoldQg u.1) =
        RoundPoly.evalCoeffs Q.coeffs (hemFoldQg u.1)
    · rw [ite_true_eq _ _ hu, Nat.one_mul]
      have hCongr :
          qsum flatHemQ (fun v =>
            if (decide (RoundPoly.evalCoeffs P.coeffs (hemFoldQg u.1) =
                  RoundPoly.evalCoeffs Q.coeffs (hemFoldQg u.1)) &&
                decide (RoundPoly.evalCoeffs P.coeffs (hemFoldQg v.1) =
                  RoundPoly.evalCoeffs Q.coeffs (hemFoldQg v.1))) = true then 1 else 0) =
          qsum flatHemQ (fun v =>
            if RoundPoly.evalCoeffs P.coeffs (hemFoldQg v.1) =
                RoundPoly.evalCoeffs Q.coeffs (hemFoldQg v.1) then 1 else 0) := by
        apply qsum_congr; intro v
        rw [decide_eq_true hu, Bool.true_and]
        exact ite_decide_eq _
      rw [hCongr]; exact h1
    · rw [ite_false_eq _ _ hu, Nat.zero_mul]
      have hZero : ∀ v : Fin flatHemQ,
          (if (decide (RoundPoly.evalCoeffs P.coeffs (hemFoldQg u.1) =
                RoundPoly.evalCoeffs Q.coeffs (hemFoldQg u.1)) &&
              decide (RoundPoly.evalCoeffs P.coeffs (hemFoldQg v.1) =
                RoundPoly.evalCoeffs Q.coeffs (hemFoldQg v.1))) = true then 1 else 0) = 0 := by
        intro v
        rw [decide_eq_false hu, Bool.false_and]
        rfl
      rw [qsum_congr hZero, qsum_const, Nat.mul_zero]
      exact Nat.le_refl 0
  exact Nat.le_trans (qsum_le_qsum hRow)
    (by rw [qsum_mul_right]; exact Nat.mul_le_mul_right d h1)

theorem qsum_any_le_mul {α : Type} (B M : Nat) (pred : α → Fin M → Bool) :
    ∀ (xs : List α),
      (∀ x ∈ xs, qsum M (fun i => if pred x i = true then 1 else 0) ≤ B) →
      qsum M (fun i => if xs.any (fun x => pred x i) = true then 1 else 0) ≤ xs.length * B
  | [], _ => by
    have h0 : ∀ i : Fin M, (if ([] : List α).any (fun x => pred x i) = true then 1 else 0) = 0 :=
      fun _ => rfl
    rw [qsum_congr h0, qsum_const, Nat.mul_zero, List.length_nil, Nat.zero_mul]
    exact Nat.le_refl 0
  | x :: rest, hEach => by
    have hSplit : ∀ i : Fin M,
        (if (x :: rest).any (fun y => pred y i) = true then 1 else 0) ≤
          (if pred x i = true then 1 else 0) +
          (if rest.any (fun y => pred y i) = true then 1 else 0) := by
      intro i
      rw [List.any_cons]
      cases pred x i <;> cases rest.any (fun y => pred y i) <;> decide
    have hSum := qsum_le_qsum hSplit
    rw [qsum_add] at hSum
    have hx := hEach x List.mem_cons_self
    have hr := qsum_any_le_mul B M pred rest (fun y hy => hEach y (List.mem_cons_of_mem x hy))
    rw [List.length_cons, Nat.succ_mul, Nat.add_comm (rest.length * B) B]
    exact Nat.le_trans hSum (Nat.add_le_add hx hr)

private theorem oodCollidesAux_count_le (d : Nat) :
    ∀ (cands : List (GsUniPoly QuarticGoldilocks)),
      cands.Nodup →
      (∀ P ∈ cands, P.coeffs.length ≤ d + 1) →
      qsum (flatHemQ * flatHemQ) (fun c =>
        if oodCollidesAux cands (hemFoldQg (c.1 / flatHemQ)) (hemFoldQg (c.1 % flatHemQ)) = true
        then 1 else 0) ≤
        binom2 cands.length * (d * d)
  | [], _, _ => by
    have h0 : ∀ c : Fin (flatHemQ * flatHemQ),
        (if oodCollidesAux [] (hemFoldQg (c.1 / flatHemQ)) (hemFoldQg (c.1 % flatHemQ)) = true
         then 1 else 0) = 0 := fun _ => rfl
    rw [qsum_congr h0, qsum_const, Nat.mul_zero]
    exact Nat.zero_le _
  | P :: rest, hNd, hDeg => by
    obtain ⟨hNotMem, hRestNd⟩ := List.pairwise_cons.mp hNd
    have hSplit : ∀ c : Fin (flatHemQ * flatHemQ),
        (if oodCollidesAux (P :: rest) (hemFoldQg (c.1 / flatHemQ)) (hemFoldQg (c.1 % flatHemQ)) = true
         then 1 else 0) ≤
        (if rest.any (fun Q =>
            decide (RoundPoly.evalCoeffs P.coeffs (hemFoldQg (c.1 / flatHemQ)) =
              RoundPoly.evalCoeffs Q.coeffs (hemFoldQg (c.1 / flatHemQ))) &&
            decide (RoundPoly.evalCoeffs P.coeffs (hemFoldQg (c.1 % flatHemQ)) =
              RoundPoly.evalCoeffs Q.coeffs (hemFoldQg (c.1 % flatHemQ)))) = true then 1 else 0) +
        (if oodCollidesAux rest (hemFoldQg (c.1 / flatHemQ)) (hemFoldQg (c.1 % flatHemQ)) = true
         then 1 else 0) := by
      intro c
      change (if (rest.any _ || oodCollidesAux rest _ _) = true then 1 else 0) ≤ _
      cases rest.any _ <;> cases oodCollidesAux rest _ _ <;> decide
    have hSum := qsum_le_qsum hSplit
    rw [qsum_add] at hSum
    have hHead :
        qsum (flatHemQ * flatHemQ) (fun c =>
          if rest.any (fun Q =>
              decide (RoundPoly.evalCoeffs P.coeffs (hemFoldQg (c.1 / flatHemQ)) =
                RoundPoly.evalCoeffs Q.coeffs (hemFoldQg (c.1 / flatHemQ))) &&
              decide (RoundPoly.evalCoeffs P.coeffs (hemFoldQg (c.1 % flatHemQ)) =
                RoundPoly.evalCoeffs Q.coeffs (hemFoldQg (c.1 % flatHemQ)))) = true then 1 else 0) ≤
        rest.length * (d * d) := by
      refine qsum_any_le_mul (d * d) (flatHemQ * flatHemQ) _ rest (fun Q hQ => ?_)
      rw [qsum_mul_div_mod_eq flatHemQ flatHemQ flatHemQ_pos
        (fun u v => if (decide (RoundPoly.evalCoeffs P.coeffs (hemFoldQg u) =
              RoundPoly.evalCoeffs Q.coeffs (hemFoldQg u)) &&
            decide (RoundPoly.evalCoeffs P.coeffs (hemFoldQg v) =
              RoundPoly.evalCoeffs Q.coeffs (hemFoldQg v))) = true then 1 else 0)]
      exact ood_pair_collision_le (fun hEq => hNotMem Q hQ hEq)
        (hDeg P List.mem_cons_self) (hDeg Q (List.mem_cons_of_mem P hQ))
    have hTail := oodCollidesAux_count_le d rest hRestNd
      (fun Q hQ => hDeg Q (List.mem_cons_of_mem P hQ))
    rw [List.length_cons, binom2_succ, Nat.add_mul]
    exact Nat.le_trans hSum (Nat.add_le_add hHead hTail)

private theorem oodCollidesAux_false_unique :
    ∀ (cands : List (GsUniPoly QuarticGoldilocks)) (z₀ z₁ y₀ y₁ : QuarticGoldilocks),
      oodCollidesAux cands z₀ z₁ = false →
      ∀ P₁ ∈ cands, ∀ P₂ ∈ cands,
        RoundPoly.evalCoeffs P₁.coeffs z₀ = y₀ →
        RoundPoly.evalCoeffs P₁.coeffs z₁ = y₁ →
        RoundPoly.evalCoeffs P₂.coeffs z₀ = y₀ →
        RoundPoly.evalCoeffs P₂.coeffs z₁ = y₁ →
        P₁ = P₂
  | [], _, _, _, _, _, _, h, _, _, _, _, _, _ => nomatch h
  | P :: rest, z₀, z₁, y₀, y₁, hFalse, P₁, h1, P₂, h2, e10, e11, e20, e21 => by
    unfold oodCollidesAux at hFalse
    have hAnyF : rest.any (fun Q =>
        decide (RoundPoly.evalCoeffs P.coeffs z₀ = RoundPoly.evalCoeffs Q.coeffs z₀) &&
        decide (RoundPoly.evalCoeffs P.coeffs z₁ = RoundPoly.evalCoeffs Q.coeffs z₁)) = false := by
      cases ha : rest.any _ with
      | false => rfl
      | true => rw [ha] at hFalse; exact nomatch hFalse
    have hRestF : oodCollidesAux rest z₀ z₁ = false := by
      rw [hAnyF, Bool.false_or] at hFalse; exact hFalse
    rcases List.mem_cons.mp h1 with rfl | h1r
    · rcases List.mem_cons.mp h2 with rfl | h2r
      · rfl
      · exfalso
        have hHit : rest.any (fun Q =>
            decide (RoundPoly.evalCoeffs P₁.coeffs z₀ = RoundPoly.evalCoeffs Q.coeffs z₀) &&
            decide (RoundPoly.evalCoeffs P₁.coeffs z₁ = RoundPoly.evalCoeffs Q.coeffs z₁)) = true :=
          List.any_eq_true.mpr ⟨P₂, h2r, Bool.and_eq_true_iff.mpr
            ⟨decide_eq_true (e10.trans e20.symm), decide_eq_true (e11.trans e21.symm)⟩⟩
        rw [hAnyF] at hHit; exact Bool.false_ne_true hHit
    · rcases List.mem_cons.mp h2 with rfl | h2r
      · exfalso
        have hHit : rest.any (fun Q =>
            decide (RoundPoly.evalCoeffs P₂.coeffs z₀ = RoundPoly.evalCoeffs Q.coeffs z₀) &&
            decide (RoundPoly.evalCoeffs P₂.coeffs z₁ = RoundPoly.evalCoeffs Q.coeffs z₁)) = true :=
          List.any_eq_true.mpr ⟨P₁, h1r, Bool.and_eq_true_iff.mpr
            ⟨decide_eq_true (e20.trans e10.symm), decide_eq_true (e21.trans e11.symm)⟩⟩
        rw [hAnyF] at hHit; exact Bool.false_ne_true hHit
      · exact oodCollidesAux_false_unique rest z₀ z₁ y₀ y₁ hRestF P₁ h1r P₂ h2r e10 e11 e20 e21

private theorem combineClaim_foldl_eq {F : Type} [LawfulCommRing F] (γ : F) :
    ∀ (vs : List F) (acc wt : F),
      (vs.foldl (fun (st : F × F) v =>
        (CommRingOps.add st.1 (CommRingOps.mul st.2 v), CommRingOps.mul st.2 γ)) (acc, wt)).1 =
      CommRingOps.add acc (CommRingOps.mul wt (RoundPoly.evalCoeffs vs γ))
  | [], acc, wt => by
    show acc = CommRingOps.add acc (CommRingOps.mul wt CommRingOps.zero)
    rw [LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | v :: rest, acc, wt => by
    simp only [List.foldl_cons, RoundPoly.evalCoeffs_cons, combineClaim_foldl_eq γ rest]
    constructive_ring

/-- The shift/OOD batch is evaluation in γ of the vector of claimed readings,
    with the previous claim as its constant coefficient. -/
theorem combineClaim_eq_eval {F : Type} [LawfulCommRing F] (claim γ : F) (vs : List F) :
    combineClaim claim γ vs = RoundPoly.evalCoeffs (claim :: vs) γ := by
  exact combineClaim_foldl_eq γ vs claim γ

private theorem ringDot_evalVec6 (P : List QuarticGoldilocks) (hP : P.length ≤ 4)
    (x : QuarticGoldilocks) :
    ringDot P (evalVec6 x) = RoundPoly.evalCoeffs P x := by
  unfold evalVec6
  dsimp only
  rcases P with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, _ | ⟨c4, rest⟩⟩⟩⟩⟩
  · rw [ringDot_nil_left]; rfl
  · simp only [ringDot_cons_cons, ringDot_nil_left, RoundPoly.evalCoeffs_cons,
      RoundPoly.evalCoeffs_nil]
    constructive_ring
  · simp only [ringDot_cons_cons, ringDot_nil_left, RoundPoly.evalCoeffs_cons,
      RoundPoly.evalCoeffs_nil]
    constructive_ring
  · simp only [ringDot_cons_cons, ringDot_nil_left, RoundPoly.evalCoeffs_cons,
      RoundPoly.evalCoeffs_nil]
    constructive_ring
  · simp only [ringDot_cons_cons, ringDot_nil_left, RoundPoly.evalCoeffs_cons,
      RoundPoly.evalCoeffs_nil]
    constructive_ring
  · simp only [List.length_cons] at hP; omega

private theorem ringDot_vecAdd6 :
    ∀ (P u v : List QuarticGoldilocks), u.length = v.length →
      ringDot P (vecAdd6 u v) = CommRingOps.add (ringDot P u) (ringDot P v)
  | [], _, _, _ => by
    rw [ringDot_nil_left, ringDot_nil_left, ringDot_nil_left, LawfulCommRing.add_zero]
  | _ :: _, [], [], _ => by
    unfold vecAdd6
    rw [List.zipWith_nil_left, ringDot_nil_right, LawfulCommRing.add_zero]
  | _ :: _, [], _ :: _, h => nomatch h
  | _ :: _, _ :: _, [], h => nomatch h
  | c :: cs, a :: as, b :: bs, h => by
    change ringDot (c :: cs) (CommRingOps.add a b :: vecAdd6 as bs) = _
    rw [ringDot_cons_cons, ringDot_cons_cons, ringDot_cons_cons,
        ringDot_vecAdd6 cs as bs (Nat.succ.inj h)]
    constructive_ring

private theorem ringDot_vecScale6 (s : QuarticGoldilocks) :
    ∀ (P u : List QuarticGoldilocks),
      ringDot P (vecScale6 s u) = CommRingOps.mul s (ringDot P u)
  | [], _ => by rw [ringDot_nil_left, ringDot_nil_left, LawfulCommRing.mul_zero]
  | _ :: _, [] => by
    unfold vecScale6
    rw [List.map_nil, ringDot_nil_right, LawfulCommRing.mul_zero]
  | c :: cs, a :: as => by
    change ringDot (c :: cs) (CommRingOps.mul s a :: vecScale6 s as) = _
    rw [ringDot_cons_cons, ringDot_cons_cons, ringDot_vecScale6 s cs as]
    constructive_ring

private theorem combineKernel6_foldl_spec (γ : QuarticGoldilocks)
    (P : List QuarticGoldilocks) (hP : P.length ≤ 4) :
    ∀ (pts : List QuarticGoldilocks) (acc : List QuarticGoldilocks) (wt : QuarticGoldilocks),
      acc.length = 6 →
      ((pts.foldl (fun (st : List QuarticGoldilocks × QuarticGoldilocks) pt =>
          (vecAdd6 st.1 (vecScale6 st.2 (evalVec6 pt)), CommRingOps.mul st.2 γ)) (acc, wt)).1).length = 6 ∧
      ringDot P (pts.foldl (fun (st : List QuarticGoldilocks × QuarticGoldilocks) pt =>
          (vecAdd6 st.1 (vecScale6 st.2 (evalVec6 pt)), CommRingOps.mul st.2 γ)) (acc, wt)).1 =
        CommRingOps.add (ringDot P acc)
          (CommRingOps.mul wt (RoundPoly.evalCoeffs (pts.map (RoundPoly.evalCoeffs P)) γ))
  | [], acc, wt, hAcc => by
    refine ⟨hAcc, ?_⟩
    show ringDot P acc = CommRingOps.add (ringDot P acc) (CommRingOps.mul wt CommRingOps.zero)
    rw [LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | pt :: rest, acc, wt, hAcc => by
    have hNextLen : (vecAdd6 acc (vecScale6 wt (evalVec6 pt))).length = 6 := by
      unfold vecAdd6 vecScale6 evalVec6
      rw [List.length_zipWith, hAcc, List.length_map]
      rfl
    have hScaleLen : (vecScale6 wt (evalVec6 pt)).length = 6 := by
      unfold vecScale6 evalVec6; rw [List.length_map]; rfl
    obtain ⟨hLenEnd, hDotEnd⟩ :=
      combineKernel6_foldl_spec γ P hP rest (vecAdd6 acc (vecScale6 wt (evalVec6 pt)))
        (CommRingOps.mul wt γ) hNextLen
    refine ⟨hLenEnd, ?_⟩
    simp only [List.foldl_cons, List.map_cons, RoundPoly.evalCoeffs_cons]
    rw [hDotEnd, ringDot_vecAdd6 P acc _ (hAcc.trans hScaleLen.symm),
        ringDot_vecScale6 wt P (evalVec6 pt), ringDot_evalVec6 P hP pt]
    constructive_ring

private theorem evalCoeffs_zipWith_sub (γ : QuarticGoldilocks) :
    ∀ (us vs : List QuarticGoldilocks), us.length = vs.length →
      RoundPoly.evalCoeffs (List.zipWith CommRingOps.sub us vs) γ =
        CommRingOps.sub (RoundPoly.evalCoeffs us γ) (RoundPoly.evalCoeffs vs γ)
  | [], [], _ => by
    show CommRingOps.zero = CommRingOps.sub CommRingOps.zero CommRingOps.zero
    rw [LawfulCommRing.sub_self]
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | u :: us, v :: vs, h => by
    simp only [List.zipWith_cons_cons, RoundPoly.evalCoeffs_cons,
      evalCoeffs_zipWith_sub γ us vs (Nat.succ.inj h)]
    constructive_ring

private theorem combineKernel6_diff_eval (K : List QuarticGoldilocks) (hK : K.length = 6)
    (P : List QuarticGoldilocks) (hP : P.length ≤ 4)
    (cl γ : QuarticGoldilocks) (pts vs : List QuarticGoldilocks) (hLen : pts.length = vs.length) :
    CommRingOps.sub (ringDot P (combineKernel6 K γ pts)) (combineClaim cl γ vs) =
      RoundPoly.evalCoeffs
        (CommRingOps.sub (ringDot P K) cl ::
          List.zipWith (fun x y => CommRingOps.sub (RoundPoly.evalCoeffs P x) y) pts vs) γ := by
  unfold combineKernel6 combineClaim
  rw [(combineKernel6_foldl_spec γ P hP pts K γ hK).2, combineClaim_foldl_eq γ vs cl γ]
  have hZip : List.zipWith (fun x y => CommRingOps.sub (RoundPoly.evalCoeffs P x) y) pts vs =
      List.zipWith CommRingOps.sub (pts.map (RoundPoly.evalCoeffs P)) vs := by
    clear hK hP
    induction pts generalizing vs with
    | nil => cases vs <;> rfl
    | cons x xs ih =>
      cases vs with
      | nil => nomatch hLen
      | cons y ys =>
        simp only [List.zipWith_cons_cons, List.map_cons, ih ys (Nat.succ.inj hLen)]
  rw [RoundPoly.evalCoeffs_cons, hZip,
      evalCoeffs_zipWith_sub γ (pts.map (RoundPoly.evalCoeffs P)) vs (by rw [List.length_map, hLen])]
  constructive_ring

private def allGoodDigits (n : Nat) (good : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | t + 1, qIdx => good (qIdx % n) && allGoodDigits n good t (qIdx / n)

private theorem list_all_congr {α : Type} (p q : α → Bool) (h : ∀ x, p x = q x) :
    ∀ l : List α, l.all p = l.all q
  | [] => rfl
  | a :: as => by simp only [List.all_cons, h a, list_all_congr p q h as]

private theorem range_succ_eq_zero_cons_map :
    ∀ k : Nat, List.range (k + 1) = 0 :: (List.range k).map (· + 1)
  | 0 => rfl
  | m + 1 => by
    conv => lhs; rw [List.range_succ, range_succ_eq_zero_cons_map m]
    conv => rhs; rw [List.range_succ]
    rw [List.map_append, List.map_cons, List.map_nil, List.cons_append]

private theorem allGoodDigits_eq_range (n : Nat) (hn : 0 < n) (good : Nat → Bool) :
    ∀ (t qIdx : Nat),
      ((List.range t).all (fun j => good ((qIdx / n ^ j) % n))) = allGoodDigits n good t qIdx
  | 0, _ => rfl
  | t + 1, qIdx => by
    rw [range_succ_eq_zero_cons_map t, List.all_cons]
    unfold allGoodDigits
    rw [Nat.pow_zero, Nat.div_one]
    congr 1
    rw [List.all_map, ← allGoodDigits_eq_range n hn good t (qIdx / n)]
    refine list_all_congr _ _ (fun j => ?_) _
    dsimp only [Function.comp]
    rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul]

private theorem qsum_allGoodDigits_le (n B : Nat) (hn : 0 < n) (good : Nat → Bool)
    (hGood : qsum n (fun pos => if good pos.1 = true then 1 else 0) ≤ B) :
    ∀ t : Nat,
      qsum (n ^ t) (fun qIdx => if allGoodDigits n good t qIdx.1 = true then 1 else 0) ≤ B ^ t
  | 0 => by
    change qsumNat 1 (fun u => if allGoodDigits n good 0 u = true then 1 else 0) ≤ 1
    rw [qsumNat_succ, qsumNat_zero, Nat.add_zero]
    exact Nat.le_refl 1
  | t + 1 => by
    change qsumNat (n ^ (t + 1)) (fun u => if allGoodDigits n good (t + 1) u = true then 1 else 0) ≤
      B ^ (t + 1)
    rw [Nat.pow_succ n t,
        show (fun u => if allGoodDigits n good (t + 1) u = true then 1 else 0) =
          (fun u => if (good (u % n) && allGoodDigits n good t (u / n)) = true then 1 else 0) from rfl,
        qsumNat_mul_div_mod (n ^ t) n hn
          (fun hi lo => if (good lo && allGoodDigits n good t hi) = true then 1 else 0)]
    change qsum (n ^ t) (fun hi => qsum n (fun lo =>
      if (good lo.1 && allGoodDigits n good t hi.1) = true then 1 else 0)) ≤ B ^ (t + 1)
    have hRow : ∀ hi : Fin (n ^ t),
        qsum n (fun lo => if (good lo.1 && allGoodDigits n good t hi.1) = true then 1 else 0) ≤
          (if allGoodDigits n good t hi.1 = true then 1 else 0) * B := by
      intro hi
      cases hHi : allGoodDigits n good t hi.1
      · simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte, Nat.zero_mul]
        rw [qsum_const, Nat.mul_zero]; exact Nat.le_refl 0
      · simp only [Bool.and_true, ↓reduceIte, Nat.one_mul]
        exact hGood
    have hSum := qsum_le_qsum hRow
    rw [qsum_mul_right] at hSum
    rw [Nat.pow_succ]
    exact Nat.le_trans hSum (Nat.mul_le_mul_right B (qsum_allGoodDigits_le n B hn good hGood t))

/-- Independent base-n digits hit a set of size at most B in every draw with
    numerator at most B^t over the n^t possible seeds. -/
theorem qsum_good_digits_le (n t B : Nat) (hn : 0 < n) (good : Nat → Bool)
    (hgood : qsum n (fun p => if good p.val then 1 else 0) ≤ B) :
    qsum (n^t) (fun c => if (List.range t).all (fun j => good ((c.val / n^j) % n))
      then 1 else 0) ≤ B^t := by
  simp only [allGoodDigits_eq_range n hn]
  exact qsum_allGoodDigits_le n B hn good hgood t

private theorem poly_roots_in_flatHemPool_le {k : Nat} (Δ : List QuarticGoldilocks)
    (hLen : Δ.length ≤ k + 1) (hNz : ∃ c ∈ Δ, c ≠ CommRingOps.zero) :
    qsum flatHemQ (fun gIdx =>
      if RoundPoly.evalCoeffs Δ (hemFoldQg gIdx.1) = CommRingOps.zero then 1 else 0) ≤ k := by
  letI : NoZeroDivisors QuarticGoldilocks := LawfulField.toNoZeroDivisors QuarticGoldilocks
  let pred : QuarticGoldilocks → Bool :=
    fun z => decide (RoundPoly.evalCoeffs Δ z = CommRingOps.zero)
  have hQsumEq :
      qsum flatHemQ (fun gIdx =>
        if RoundPoly.evalCoeffs Δ (hemFoldQg gIdx.1) = CommRingOps.zero then 1 else 0) =
      (flatHemPool.filter pred).length := by
    rw [← qsum_get_filter_length pred flatHemPool]
    exact qsum_congr_len flatHemPool_length.symm _ _ (fun u j huj => by
      dsimp only [pred]
      rw [← list_getD_eq_get flatHemPool CommRingOps.zero j, ← huj, flatHemPool_getD u.1 u.2]
      exact (ite_decide_eq _).symm)
  rw [hQsumEq]
  exact gs_formal_root_bound k Δ (flatHemPool.filter pred) hLen hNz
    (List.Pairwise.filter _ flatHemPool_nodup)
    (fun z hz => of_decide_eq_true (List.mem_filter.mp hz).2)

/-- Boolean RBR state function for `flatHemSlicedSched` across prefix lengths `0 .. 6`. -/
def flatHemState (x : WhirStmt QuarticGoldilocks) :
    List (WhirMsg QuarticGoldilocks × Nat) → Bool
  | [] =>
    let O0 := interleaveOracle 32 (fun p => x.table.getD p CommRingOps.zero)
    hasValidWitness 5 40 hemFoldDom64 O0 flatHemInitKernel x.claim
  | [(m0, c0)] =>
    let O0 := interleaveOracle 32 (fun p => x.table.getD p CommRingOps.zero)
    let q0 := decodeQuad c0
    let V0 := hemVirtualFoldOracle q0.2.1 q0.2.2.1 q0.2.2.2 hemFoldDom64 hemFoldDom32 O0
    let K0' := hemKernelFold q0.1 flatHemInitKernel
    let cl0' := hemBridgeFoldClaim x.claim
      (m0.poly.getD 0 CommRingOps.zero) (m0.poly.getD 1 CommRingOps.zero)
      (m0.poly.getD 2 CommRingOps.zero) (m0.poly.getD 3 CommRingOps.zero)
      (m0.poly.getD 4 CommRingOps.zero) q0.1 q0.2.1 q0.2.2.1 q0.2.2.2
    decide (m0.poly.length ≤ 5) && hasValidWitness 3 21 hemFoldDom32 V0 K0' cl0'
  | [(m0, c0), (m1, c1)] =>
    let O1 := interleaveOracle 16 (fun p => m1.table.getD p CommRingOps.zero)
    let cands := gsDecodeList 3 20 hemFoldDom32 (lookupDomOracle hemFoldDom32 O1)
    let ood := decodeOod c1
    flatHemState x [(m0, c0)] || oodCollidesAux cands ood.1 ood.2
  | [(m0, c0), (m1, c1), (m2, c2)] =>
    let O0 := interleaveOracle 32 (fun p => x.table.getD p CommRingOps.zero)
    let q0 := decodeQuad c0
    let V0 := hemVirtualFoldOracle q0.2.1 q0.2.2.1 q0.2.2.2 hemFoldDom64 hemFoldDom32 O0
    let K0' := hemKernelFold q0.1 flatHemInitKernel
    let cl0' := hemBridgeFoldClaim x.claim
      (m0.poly.getD 0 CommRingOps.zero) (m0.poly.getD 1 CommRingOps.zero)
      (m0.poly.getD 2 CommRingOps.zero) (m0.poly.getD 3 CommRingOps.zero)
      (m0.poly.getD 4 CommRingOps.zero) q0.1 q0.2.1 q0.2.2.1 q0.2.2.2
    let ood0 := decodeOod c1
    let γ₀ := flatHemChalField c2 36
    let qPts0 := (List.range 36).map (fun j =>
      hemFoldDom32.getD (flatHemChalPos c2 j 32) CommRingOps.zero)
    let folded0 := (List.range 36).map (fun j => V0 (flatHemChalPos c2 j 32))
    let K1 := combineKernel6 K0' γ₀ ([ood0.1, ood0.2] ++ qPts0)
    let cl1 := combineClaim cl0' γ₀ (m2.answers ++ folded0)
    let O1 := interleaveOracle 16 (fun p => m1.table.getD p CommRingOps.zero)
    decide (m0.poly.length ≤ 5 ∧ m2.answers.length = 2) &&
      hasValidWitness 3 20 hemFoldDom32 O1 K1 cl1
  | [(m0, c0), (m1, c1), (m2, c2), (m3, c3)] =>
    let O0 := interleaveOracle 32 (fun p => x.table.getD p CommRingOps.zero)
    let q0 := decodeQuad c0
    let V0 := hemVirtualFoldOracle q0.2.1 q0.2.2.1 q0.2.2.2 hemFoldDom64 hemFoldDom32 O0
    let K0' := hemKernelFold q0.1 flatHemInitKernel
    let cl0' := hemBridgeFoldClaim x.claim
      (m0.poly.getD 0 CommRingOps.zero) (m0.poly.getD 1 CommRingOps.zero)
      (m0.poly.getD 2 CommRingOps.zero) (m0.poly.getD 3 CommRingOps.zero)
      (m0.poly.getD 4 CommRingOps.zero) q0.1 q0.2.1 q0.2.2.1 q0.2.2.2
    let ood0 := decodeOod c1
    let γ₀ := flatHemChalField c2 36
    let qPts0 := (List.range 36).map (fun j =>
      hemFoldDom32.getD (flatHemChalPos c2 j 32) CommRingOps.zero)
    let folded0 := (List.range 36).map (fun j => V0 (flatHemChalPos c2 j 32))
    let K1 := combineKernel6 K0' γ₀ ([ood0.1, ood0.2] ++ qPts0)
    let cl1 := combineClaim cl0' γ₀ (m2.answers ++ folded0)
    let O1 := interleaveOracle 16 (fun p => m1.table.getD p CommRingOps.zero)
    let q1 := decodeQuad c3
    let V1 := hemVirtualFoldOracle q1.2.1 q1.2.2.1 q1.2.2.2 hemFoldDom32 hemFoldDom16 O1
    let K2 := hemKernelFold q1.1 K1
    let cl2 := hemBridgeFoldClaim cl1
      (m3.poly.getD 0 CommRingOps.zero) (m3.poly.getD 1 CommRingOps.zero)
      (m3.poly.getD 2 CommRingOps.zero) (m3.poly.getD 3 CommRingOps.zero)
      (m3.poly.getD 4 CommRingOps.zero) q1.1 q1.2.1 q1.2.2.1 q1.2.2.2
    decide (m0.poly.length ≤ 5 ∧ m2.answers.length = 2) &&
      decide (m3.poly.length ≤ 5) &&
      hasValidWitness 2 11 hemFoldDom16 V1 K2 cl2
  | [(m0, c0), (m1, c1), (m2, c2), (m3, c3), _] =>
    flatHemState x [(m0, c0), (m1, c1), (m2, c2), (m3, c3)]
  | tr => (whirOracleIop flatHemSlicedEnv flatHemSlicedSched 256).verify x tr

/-- Certified per-round flip counts for `flatHemSlicedSched` at `w = 256`. -/
def flatHemBad : Fin flatHemSlicedSched.numRounds → Nat
  | ⟨0, _⟩ => 2 ^ 8 * slicedFourChallengeCount 32 2 20 12 1 3 flatHemQ
  | ⟨1, _⟩ => 2 ^ 132 * (binom2 33 * 3 ^ 2)
  | ⟨2, _⟩ => 2 ^ 14 * (21 ^ 36 * flatHemQ + 33 * 38 * 32 ^ 36)
  | ⟨3, _⟩ => 2 ^ 8 * slicedFourChallengeCount 16 1 10 7 2 4 flatHemQ
  | ⟨4, _⟩ => 0
  | ⟨5, _⟩ => 2 ^ 10 * (11 ^ 46 * flatHemQ)
  | ⟨n + 6, h⟩ => by have h' : n + 6 < 6 := h; omega

private theorem flatHem_round0_flips (x : WhirStmt QuarticGoldilocks)
    (hDoomed : flatHemState x [] = false) (m0 : WhirMsg QuarticGoldilocks) :
    qsum (2 ^ 256) (fun ch => if flatHemState x [(m0, ch.1)] = true then 1 else 0) ≤
      2 ^ 8 * slicedFourChallengeCount 32 2 20 12 1 3 flatHemQ := by
  let O0 := interleaveOracle 32 (fun p => x.table.getD p CommRingOps.zero)
  have hInv : ∀ Q : List QuarticGoldilocks,
      polyWitnessValid hemFoldDom64 (2 * 20) (2 * 2 + 1) O0 flatHemInitKernel x.claim Q = false :=
    hasValidWitness_false_imp 5 40 hemFoldDom64 antipodal_64_32.nodup_in (by decide)
      O0 flatHemInitKernel x.claim (by unfold flatHemState at hDoomed; exact hDoomed)
  let M := flatHemQ * (flatHemQ * (flatHemQ * flatHemQ))
  have hMPos : 0 < M := Nat.mul_pos flatHemQ_pos
    (Nat.mul_pos flatHemQ_pos (Nat.mul_pos flatHemQ_pos flatHemQ_pos))
  have hModInv : ∀ c : Nat, flatHemState x [(m0, c)] = flatHemState x [(m0, c % M)] := by
    intro c
    unfold flatHemState decodeQuad
    dsimp only [M]
    rw [Nat.mod_mod]
  have h256 : 2 ^ 256 = 2 ^ 8 * M := by decide +kernel
  have hSplit :
      qsum (2 ^ 256) (fun ch => if flatHemState x [(m0, ch.1)] = true then 1 else 0) =
      2 ^ 8 * qsum M (fun idx => if flatHemState x [(m0, idx.1)] = true then 1 else 0) :=
    qsum_mul_mod_eq h256 hMPos _ (fun u => if flatHemState x [(m0, u)] = true then 1 else 0)
      (fun ch => by rw [hModInv ch.1])
  rw [hSplit]
  apply Nat.mul_le_mul_left (2 ^ 8)
  let predPool : Fin (quadPool flatHemPool).length → Bool :=
    fun idx => flatHemState x [(m0, idx.1)]
  have hQsumPool :
      qsum M (fun idx => if flatHemState x [(m0, idx.1)] = true then 1 else 0) =
      (finFilterList (quadPool flatHemPool).length predPool).length := by
    rw [finFilterList_length]
    exact qsum_congr_len quadPool_flatHem_len.symm _ _
      (fun _ _ hij => by dsimp only [predPool]; rw [hij])
  rw [hQsumPool]
  have hParams : slicedParamsOk hemFoldDom32.length (2 + 1) (20 + 1) 12 1 3 = true := by
    rw [hemFoldDom32_len]; decide +kernel
  have hBound := sliced_singleStep_bridge_four_challenge_bound
    hemFoldDom64 hemFoldDom32 flatHemPool flatHemInitKernel 2 20 12 1 3 5
    O0 x.claim
    (m0.poly.getD 0 CommRingOps.zero) (m0.poly.getD 1 CommRingOps.zero)
    (m0.poly.getD 2 CommRingOps.zero) (m0.poly.getD 3 CommRingOps.zero)
    (m0.poly.getD 4 CommRingOps.zero)
    antipodal_64_32 flatHemPool_nodup (by decide) rfl hParams hInv
    (finFilterList (quadPool flatHemPool).length predPool)
    (finFilterList_nodup _ _)
    (fun ch hch hNo => by
      have hSt : flatHemState x [(m0, ch.1)] = true := finFilterList_sound _ _ ch hch
      unfold flatHemState at hSt
      rw [Bool.and_eq_true, decodeQuad_eq_quadPool_get ch] at hSt
      obtain ⟨P, hP⟩ := (hasValidWitness_true_iff 3 21 hemFoldDom32 antipodal_64_32.nodup_out
        (by decide) _ _ _).mp hSt.2
      exact hNo ⟨P, hP⟩)
  rwa [hemFoldDom32_len, flatHemPool_length] at hBound

private theorem flatHem_round1_flips (x : WhirStmt QuarticGoldilocks)
    (m0 m1 : WhirMsg QuarticGoldilocks) (c0 : Nat)
    (hDoomed : flatHemState x [(m0, c0)] = false) :
    qsum (2 ^ 256) (fun ch => if flatHemState x [(m0, c0), (m1, ch.1)] = true then 1 else 0) ≤
      2 ^ 132 * (binom2 33 * 3 ^ 2) := by
  let O1 := interleaveOracle 16 (fun p => m1.table.getD p CommRingOps.zero)
  let cands := gsDecodeList 3 20 hemFoldDom32 (lookupDomOracle hemFoldDom32 O1)
  have hCandsLen : cands.length ≤ 33 :=
    WhirStage.decode_list_le flatHemStage0 (by decide +kernel) hemFoldDom32
      (lookupDomOracle hemFoldDom32 O1) antipodal_64_32.nodup_out hemFoldDom32_len
  have hCandsNd : cands.Nodup := gsDecodeList_nodup 3 20 hemFoldDom32 _
  have hCandsDeg : ∀ P ∈ cands, P.coeffs.length ≤ 3 + 1 :=
    fun P hP => ((mem_gsDecodeList_iff _ antipodal_64_32.nodup_out (by decide) P).mp hP).1
  have hEq : ∀ c : Nat,
      flatHemState x [(m0, c0), (m1, c)] =
      oodCollidesAux cands
        (hemFoldQg ((c % (flatHemQ * flatHemQ)) / flatHemQ))
        (hemFoldQg ((c % (flatHemQ * flatHemQ)) % flatHemQ)) := by
    intro c
    unfold flatHemState
    change (flatHemState x [(m0, c0)] ||
      oodCollidesAux cands (decodeOod c).1 (decodeOod c).2) = _
    rw [hDoomed, Bool.false_or]
    rfl
  have h256 : 2 ^ 256 = 2 ^ 132 * (flatHemQ * flatHemQ) := by decide +kernel
  rw [qsum_mul_mod_eq h256 (Nat.mul_pos flatHemQ_pos flatHemQ_pos) _
    (fun u => if oodCollidesAux cands (hemFoldQg (u / flatHemQ)) (hemFoldQg (u % flatHemQ)) = true
      then 1 else 0)
    (fun ch => by rw [hEq ch.1])]
  apply Nat.mul_le_mul_left (2 ^ 132)
  exact Nat.le_trans (oodCollidesAux_count_le 3 cands hCandsNd hCandsDeg)
    (Nat.mul_le_mul_right 9 (binom2_mono hCandsLen))

private theorem flatHem_round2_flips (x : WhirStmt QuarticGoldilocks)
    (m0 m1 m2 : WhirMsg QuarticGoldilocks) (c0 c1 : Nat)
    (hDoomed : flatHemState x [(m0, c0), (m1, c1)] = false) :
    qsum (2 ^ 256) (fun ch =>
      if flatHemState x [(m0, c0), (m1, c1), (m2, ch.1)] = true then 1 else 0) ≤
      2 ^ 14 * (21 ^ 36 * flatHemQ + 33 * 38 * 32 ^ 36) := by
  have hD0 : flatHemState x [(m0, c0)] = false := by
    cases h : flatHemState x [(m0, c0)] with
    | false => rfl
    | true =>
      have h2 : flatHemState x [(m0, c0), (m1, c1)] = true := by
        unfold flatHemState
        change (flatHemState x [(m0, c0)] || _) = true
        rw [h, Bool.true_or]
      rw [hDoomed] at h2; exact absurd h2 Bool.false_ne_true
  let O1 := interleaveOracle 16 (fun p => m1.table.getD p CommRingOps.zero)
  let cands := gsDecodeList 3 20 hemFoldDom32 (lookupDomOracle hemFoldDom32 O1)
  let ood0 := decodeOod c1
  have hNoOod : oodCollidesAux cands ood0.1 ood0.2 = false := by
    have h2 := hDoomed
    unfold flatHemState at h2
    change (flatHemState x [(m0, c0)] || oodCollidesAux cands ood0.1 ood0.2) = false at h2
    rw [hD0, Bool.false_or] at h2
    exact h2
  if hWF : m0.poly.length ≤ 5 ∧ m2.answers.length = 2 then
    have hD0Wit : hasValidWitness 3 21 hemFoldDom32
        (hemVirtualFoldOracle (decodeQuad c0).2.1 (decodeQuad c0).2.2.1 (decodeQuad c0).2.2.2
          hemFoldDom64 hemFoldDom32 (interleaveOracle 32 (fun p => x.table.getD p CommRingOps.zero)))
        (hemKernelFold (decodeQuad c0).1 flatHemInitKernel)
        (hemBridgeFoldClaim x.claim
          (m0.poly.getD 0 CommRingOps.zero) (m0.poly.getD 1 CommRingOps.zero)
          (m0.poly.getD 2 CommRingOps.zero) (m0.poly.getD 3 CommRingOps.zero)
          (m0.poly.getD 4 CommRingOps.zero)
          (decodeQuad c0).1 (decodeQuad c0).2.1 (decodeQuad c0).2.2.1 (decodeQuad c0).2.2.2) = false := by
      unfold flatHemState at hD0
      rw [decide_eq_true hWF.1, Bool.true_and] at hD0
      exact hD0
    let V0 := hemVirtualFoldOracle (decodeQuad c0).2.1 (decodeQuad c0).2.2.1 (decodeQuad c0).2.2.2
      hemFoldDom64 hemFoldDom32 (interleaveOracle 32 (fun p => x.table.getD p CommRingOps.zero))
    let K0' := hemKernelFold (decodeQuad c0).1 flatHemInitKernel
    let cl0' := hemBridgeFoldClaim x.claim
      (m0.poly.getD 0 CommRingOps.zero) (m0.poly.getD 1 CommRingOps.zero)
      (m0.poly.getD 2 CommRingOps.zero) (m0.poly.getD 3 CommRingOps.zero)
      (m0.poly.getD 4 CommRingOps.zero)
      (decodeQuad c0).1 (decodeQuad c0).2.1 (decodeQuad c0).2.2.1 (decodeQuad c0).2.2.2
    have hK0Len : K0'.length = 6 :=
      (splitEvenOdd_spec 5 flatHemInitKernel (decodeQuad c0).1 rfl).2.2.2.2
    have hCandsLen : cands.length ≤ 33 :=
      WhirStage.decode_list_le flatHemStage0 (by decide +kernel) hemFoldDom32
        (lookupDomOracle hemFoldDom32 O1) antipodal_64_32.nodup_out hemFoldDom32_len
    have hCandsDeg : ∀ P ∈ cands, P.coeffs.length ≤ 4 :=
      fun P hP => ((mem_gsDecodeList_iff _ antipodal_64_32.nodup_out (by decide) P).mp hP).1
    let M := 32 ^ 36 * flatHemQ
    have hMPos : 0 < M := Nat.mul_pos (Nat.pow_pos (by decide)) flatHemQ_pos
    let ptsOf (qIdx : Nat) : List QuarticGoldilocks :=
      [ood0.1, ood0.2] ++ (List.range 36).map (fun j =>
        hemFoldDom32.getD ((qIdx / 32 ^ j) % 32) CommRingOps.zero)
    let vsOf (qIdx : Nat) : List QuarticGoldilocks :=
      m2.answers ++ (List.range 36).map (fun j => V0 ((qIdx / 32 ^ j) % 32))
    have hPtsVsLen : ∀ qIdx : Nat, (ptsOf qIdx).length = (vsOf qIdx).length := by
      intro qIdx
      dsimp only [ptsOf, vsOf]
      rw [List.length_append, List.length_append, hWF.2]; rfl
    have hPtsLen38 : ∀ qIdx : Nat, (ptsOf qIdx).length = 38 := by
      intro qIdx; dsimp only [ptsOf]; rw [List.length_append, List.length_map, List.length_range]; rfl
    have hModEq : ∀ c : Nat,
        flatHemState x [(m0, c0), (m1, c1), (m2, c)] =
        cands.any (fun P => decide (ringDot P.coeffs
          (combineKernel6 K0' (hemFoldQg ((c % M) % flatHemQ)) (ptsOf ((c % M) / flatHemQ))) =
          combineClaim cl0' (hemFoldQg ((c % M) % flatHemQ)) (vsOf ((c % M) / flatHemQ)))) := by
      intro c
      unfold flatHemState
      dsimp only [hasValidWitness]
      rw [decide_eq_true hWF, Bool.true_and]
      rfl
    have h256 : 2 ^ 256 = 2 ^ 14 * M := by decide +kernel
    rw [qsum_mul_mod_eq h256 hMPos _
      (fun u => if cands.any (fun P => decide (ringDot P.coeffs
        (combineKernel6 K0' (hemFoldQg (u % flatHemQ)) (ptsOf (u / flatHemQ))) =
        combineClaim cl0' (hemFoldQg (u % flatHemQ)) (vsOf (u / flatHemQ)))) = true then 1 else 0)
      (fun ch => by rw [hModEq ch.1])]
    apply Nat.mul_le_mul_left (2 ^ 14)
    rw [qsum_mul_div_mod_eq (32 ^ 36) flatHemQ flatHemQ_pos
      (fun qIdx gIdx => if cands.any (fun P => decide (ringDot P.coeffs
        (combineKernel6 K0' (hemFoldQg gIdx) (ptsOf qIdx)) =
        combineClaim cl0' (hemFoldQg gIdx) (vsOf qIdx))) = true then 1 else 0)]
    let deltaOf (P : GsUniPoly QuarticGoldilocks) (qIdx : Nat) : List QuarticGoldilocks :=
      CommRingOps.sub (ringDot P.coeffs K0') cl0' ::
        List.zipWith (fun x y => CommRingOps.sub (RoundPoly.evalCoeffs P.coeffs x) y)
          (ptsOf qIdx) (vsOf qIdx)
    let allZero (xs : List QuarticGoldilocks) : Bool :=
      xs.all (fun z => decide (z = CommRingOps.zero))
    let matchOod (P : GsUniPoly QuarticGoldilocks) : Bool :=
      decide (RoundPoly.evalCoeffs P.coeffs ood0.1 = m2.answers.getD 0 CommRingOps.zero) &&
      decide (RoundPoly.evalCoeffs P.coeffs ood0.2 = m2.answers.getD 1 CommRingOps.zero)
    let evA (qIdx : Nat) : Bool :=
      (cands.filter matchOod).any (fun P => allZero (deltaOf P qIdx))
    let evB (qIdx gIdx : Nat) : Bool :=
      cands.any (fun P => !allZero (deltaOf P qIdx) &&
        decide (RoundPoly.evalCoeffs (deltaOf P qIdx) (hemFoldQg gIdx) = CommRingOps.zero))
    have hCover : ∀ (qIdx : Fin (32 ^ 36)) (gIdx : Fin flatHemQ),
        (if cands.any (fun P => decide (ringDot P.coeffs
            (combineKernel6 K0' (hemFoldQg gIdx.1) (ptsOf qIdx.1)) =
            combineClaim cl0' (hemFoldQg gIdx.1) (vsOf qIdx.1))) = true then 1 else 0) ≤
        (if evA qIdx.1 = true then 1 else 0) + (if evB qIdx.1 gIdx.1 = true then 1 else 0) := by
      intro qIdx gIdx
      cases hAny : cands.any _ with
      | false => rw [ite_false_eq _ _ Bool.false_ne_true]; exact Nat.zero_le _
      | true =>
        rw [ite_true_eq _ _ rfl]
        obtain ⟨P, hPMem, hEqD⟩ := List.any_eq_true.mp hAny
        have hSub0 : CommRingOps.sub
            (ringDot P.coeffs (combineKernel6 K0' (hemFoldQg gIdx.1) (ptsOf qIdx.1)))
            (combineClaim cl0' (hemFoldQg gIdx.1) (vsOf qIdx.1)) = CommRingOps.zero :=
          LawfulCommRing.sub_eq_zero_iff.mpr (of_decide_eq_true hEqD)
        rw [combineKernel6_diff_eval K0' hK0Len P.coeffs (hCandsDeg P hPMem)
            cl0' (hemFoldQg gIdx.1) (ptsOf qIdx.1) (vsOf qIdx.1) (hPtsVsLen qIdx.1)] at hSub0
        cases hZ : allZero (deltaOf P qIdx.1) with
        | false =>
          have hB : evB qIdx.1 gIdx.1 = true :=
            List.any_eq_true.mpr ⟨P, hPMem, Bool.and_eq_true_iff.mpr
              ⟨by rw [hZ]; rfl, decide_eq_true hSub0⟩⟩
          rw [ite_true_eq _ _ hB]; omega
        | true =>
          have hAll := List.all_eq_true.mp hZ
          rcases hAns : m2.answers with _ | ⟨y0, _ | ⟨y1, _ | _⟩⟩
          · rw [hAns] at hWF; exact absurd hWF.2 (by decide)
          · rw [hAns] at hWF; simp only [List.length_cons, List.length_nil] at hWF; omega
          · have hZ1 : CommRingOps.sub (RoundPoly.evalCoeffs P.coeffs ood0.1) y0 = CommRingOps.zero :=
              of_decide_eq_true (hAll _ (by
                dsimp only [deltaOf, ptsOf, vsOf]
                rw [hAns]
                exact List.mem_cons_of_mem _ List.mem_cons_self))
            have hZ2 : CommRingOps.sub (RoundPoly.evalCoeffs P.coeffs ood0.2) y1 = CommRingOps.zero :=
              of_decide_eq_true (hAll _ (by
                dsimp only [deltaOf, ptsOf, vsOf]
                rw [hAns]
                exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
            have hMO : matchOod P = true := by
              dsimp only [matchOod]; rw [hAns]
              exact Bool.and_eq_true_iff.mpr
                ⟨decide_eq_true (LawfulCommRing.sub_eq_zero_iff.mp hZ1),
                 decide_eq_true (LawfulCommRing.sub_eq_zero_iff.mp hZ2)⟩
            have hA : evA qIdx.1 = true :=
              List.any_eq_true.mpr ⟨P, List.mem_filter.mpr ⟨hPMem, hMO⟩, hZ⟩
            rw [ite_true_eq _ _ hA]; omega
          · rw [hAns] at hWF; simp only [List.length_cons] at hWF; omega
    have hStepSplit :
        qsum (32 ^ 36) (fun qIdx => qsum flatHemQ (fun gIdx =>
          if cands.any (fun P => decide (ringDot P.coeffs
            (combineKernel6 K0' (hemFoldQg gIdx.1) (ptsOf qIdx.1)) =
            combineClaim cl0' (hemFoldQg gIdx.1) (vsOf qIdx.1))) = true then 1 else 0)) ≤
        qsum (32 ^ 36) (fun qIdx => (if evA qIdx.1 = true then 1 else 0) * flatHemQ) +
        qsum (32 ^ 36) (fun qIdx => qsum flatHemQ (fun gIdx =>
          if evB qIdx.1 gIdx.1 = true then 1 else 0)) := by
      rw [← qsum_add]
      apply qsum_le_qsum; intro qIdx
      have hInner := qsum_le_qsum (hCover qIdx)
      rw [qsum_add, qsum_const, Nat.mul_comm flatHemQ] at hInner
      exact hInner
    have hBoundA :
        qsum (32 ^ 36) (fun qIdx => (if evA qIdx.1 = true then 1 else 0) * flatHemQ) ≤
          21 ^ 36 * flatHemQ := by
      rw [qsum_mul_right]
      apply Nat.mul_le_mul_right flatHemQ
      rcases hFilt : cands.filter matchOod with _ | ⟨Pstar, restStar⟩
      · have h0 : ∀ qIdx : Fin (32 ^ 36), (if evA qIdx.1 = true then 1 else 0) = 0 := by
          intro qIdx
          have hF : evA qIdx.1 = false := by dsimp only [evA]; rw [hFilt]; rfl
          rw [hF]; rfl
        rw [qsum_congr h0, qsum_const, Nat.mul_zero]; exact Nat.zero_le _
      · have hRestNil : restStar = [] := by
          cases restStar with
          | nil => rfl
          | cons P2 _ =>
            exfalso
            have hNdF : (Pstar :: P2 :: _).Nodup :=
              hFilt ▸ List.Pairwise.filter _ (gsDecodeList_nodup 3 20 hemFoldDom32 _)
            have hNeP : Pstar ≠ P2 := fun e => (List.pairwise_cons.mp hNdF).1 P2 List.mem_cons_self e
            have h1Mem : Pstar ∈ cands.filter matchOod := by rw [hFilt]; exact List.mem_cons_self
            have h2Mem : P2 ∈ cands.filter matchOod := by
              rw [hFilt]; exact List.mem_cons_of_mem _ List.mem_cons_self
            obtain ⟨h1C, h1M⟩ := List.mem_filter.mp h1Mem
            obtain ⟨h2C, h2M⟩ := List.mem_filter.mp h2Mem
            rw [Bool.and_eq_true] at h1M h2M
            exact hNeP (oodCollidesAux_false_unique cands ood0.1 ood0.2 _ _ hNoOod
              Pstar h1C P2 h2C
              (of_decide_eq_true h1M.1) (of_decide_eq_true h1M.2)
              (of_decide_eq_true h2M.1) (of_decide_eq_true h2M.2))
        let goodPos (pos : Nat) : Bool :=
          decide (RoundPoly.evalCoeffs Pstar.coeffs (hemFoldDom32.getD pos CommRingOps.zero) = V0 pos)
        if hClEq : ringDot Pstar.coeffs K0' = cl0' then
          have hGoodLe : qsum 32 (fun pos => if goodPos pos.1 = true then 1 else 0) ≤ 21 := by
            apply Decidable.byContradiction
            intro hGt21
            have hPstarC : Pstar ∈ cands :=
              (List.mem_filter.mp (by rw [hFilt]; exact List.mem_cons_self)).1
            have hAgCount :
                qsum 32 (fun pos => if goodPos pos.1 = true then 1 else 0) =
                hemCosetAgreeCount hemFoldDom32 V0 Pstar.coeffs := by
              rw [hemCosetAgreeCount_def]
              exact qsum_congr_len hemFoldDom32_len.symm _ _ (fun pos j hpj => by
                dsimp only [goodPos]
                rw [← list_getD_eq_get hemFoldDom32 CommRingOps.zero j, ← hpj]
                by_cases he : RoundPoly.evalCoeffs Pstar.coeffs
                    (hemFoldDom32.getD pos.1 CommRingOps.zero) = V0 pos.1
                · simp only [he, decide_true, ↓reduceIte]
                · have he' : V0 pos.1 ≠ RoundPoly.evalCoeffs Pstar.coeffs
                      (hemFoldDom32.getD pos.1 CommRingOps.zero) := fun e => he e.symm
                  simp only [he, he', decide_false, Bool.false_eq_true, ↓reduceIte])
            have hPW : polyWitnessValid hemFoldDom32 21 3 V0 K0' cl0' Pstar.coeffs = true := by
              rw [polyWitnessValid_def, ← hAgCount, decide_eq_true (hCandsDeg Pstar hPstarC),
                  decide_eq_true (by omega : 21 ≤ _), decide_eq_true hClEq]
              rfl
            have hWit := (hasValidWitness_true_iff 3 21 hemFoldDom32 antipodal_64_32.nodup_out
              (by decide) V0 K0' cl0').mpr ⟨Pstar.coeffs, hPW⟩
            rw [hD0Wit] at hWit
            exact Bool.false_ne_true hWit
          have hEvALe : ∀ qIdx : Fin (32 ^ 36),
              (if evA qIdx.1 = true then 1 else 0) ≤
              (if allGoodDigits 32 goodPos 36 qIdx.1 = true then 1 else 0) := by
            intro qIdx
            cases hEv : evA qIdx.1 with
            | false => rw [ite_false_eq _ _ Bool.false_ne_true]; exact Nat.zero_le _
            | true =>
              rw [ite_true_eq _ _ rfl]
              have hEv' : ([Pstar] : List _).any (fun P => allZero (deltaOf P qIdx.1)) = true := by
                dsimp only [evA] at hEv; rwa [hFilt, hRestNil] at hEv
              rw [List.any_cons, List.any_nil, Bool.or_false] at hEv'
              have hAllZ := List.all_eq_true.mp hEv'
              have hRangeAll : ((List.range 36).all (fun j =>
                  goodPos ((qIdx.1 / 32 ^ j) % 32))) = true := by
                refine List.all_eq_true.mpr (fun j hj => ?_)
                have hjLt : j < 36 := List.mem_range.mp hj
                rcases hAns : m2.answers with _ | ⟨y0, _ | ⟨y1, _ | _⟩⟩
                · rw [hAns] at hWF; exact absurd hWF.2 (by decide)
                · rw [hAns] at hWF; simp only [List.length_cons, List.length_nil] at hWF; omega
                · have hMemZip : CommRingOps.sub
                      (RoundPoly.evalCoeffs Pstar.coeffs
                        (hemFoldDom32.getD ((qIdx.1 / 32 ^ j) % 32) CommRingOps.zero))
                      (V0 ((qIdx.1 / 32 ^ j) % 32)) ∈ deltaOf Pstar qIdx.1 := by
                    dsimp only [deltaOf, ptsOf, vsOf]
                    rw [hAns]
                    refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                      (List.mem_cons_of_mem _ ?_))
                    dsimp only [List.append]
                    have hZipEq : List.zipWith
                        (fun x y => CommRingOps.sub (RoundPoly.evalCoeffs Pstar.coeffs x) y)
                        ((List.range 36).map (fun j =>
                          hemFoldDom32.getD ((qIdx.1 / 32 ^ j) % 32) CommRingOps.zero))
                        ((List.range 36).map (fun j => V0 ((qIdx.1 / 32 ^ j) % 32))) =
                      (List.range 36).map (fun j =>
                        CommRingOps.sub
                          (RoundPoly.evalCoeffs Pstar.coeffs
                            (hemFoldDom32.getD ((qIdx.1 / 32 ^ j) % 32) CommRingOps.zero))
                          (V0 ((qIdx.1 / 32 ^ j) % 32))) := by
                      generalize List.range 36 = idxs
                      induction idxs with
                      | nil => rfl
                      | cons u us ihu => simp only [List.map_cons, List.zipWith_cons_cons, ihu]
                    rw [hZipEq]
                    exact List.mem_map.mpr ⟨j, hj, rfl⟩
                  exact decide_eq_true
                    (LawfulCommRing.sub_eq_zero_iff.mp (of_decide_eq_true (hAllZ _ hMemZip)))
                · rw [hAns] at hWF; simp only [List.length_cons] at hWF; omega
              rw [allGoodDigits_eq_range 32 (by decide) goodPos 36 qIdx.1] at hRangeAll
              rw [ite_true_eq _ _ hRangeAll]
              exact Nat.le_refl 1
          exact Nat.le_trans (qsum_le_qsum hEvALe)
            (qsum_allGoodDigits_le 32 21 (by decide) goodPos hGoodLe 36)
        else
          have h0 : ∀ qIdx : Fin (32 ^ 36), (if evA qIdx.1 = true then 1 else 0) = 0 := by
            intro qIdx
            cases hEv : evA qIdx.1 with
            | false => exact ite_false_eq _ _ Bool.false_ne_true
            | true =>
              exfalso
              have hEv' : ([Pstar] : List _).any (fun P => allZero (deltaOf P qIdx.1)) = true := by
                dsimp only [evA] at hEv; rwa [hFilt, hRestNil] at hEv
              rw [List.any_cons, List.any_nil, Bool.or_false] at hEv'
              have hHead0 := of_decide_eq_true (List.all_eq_true.mp hEv' _ List.mem_cons_self)
              exact hClEq (LawfulCommRing.sub_eq_zero_iff.mp hHead0)
          rw [qsum_congr h0, qsum_const, Nat.mul_zero]
          exact Nat.zero_le _
    have hBoundB :
        qsum (32 ^ 36) (fun qIdx => qsum flatHemQ (fun gIdx =>
          if evB qIdx.1 gIdx.1 = true then 1 else 0)) ≤
        33 * 38 * 32 ^ 36 := by
      have hPerQ : ∀ qIdx : Fin (32 ^ 36),
          qsum flatHemQ (fun gIdx => if evB qIdx.1 gIdx.1 = true then 1 else 0) ≤
            cands.length * 38 := by
        intro qIdx
        refine qsum_any_le_mul 38 flatHemQ _ cands (fun P _ => ?_)
        cases hAZ : allZero (deltaOf P qIdx.1) with
        | true =>
          simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
          rw [qsum_const, Nat.mul_zero]; exact Nat.zero_le 38
        | false =>
          have hNz : ∃ c ∈ deltaOf P qIdx.1, c ≠ CommRingOps.zero := by
            apply Decidable.byContradiction
            intro hNoNz
            have hAllT : allZero (deltaOf P qIdx.1) = true :=
              List.all_eq_true.mpr (fun c hc =>
                decide_eq_true (Decidable.byContradiction (fun hNe => hNoNz ⟨c, hc, hNe⟩)))
            rw [hAZ] at hAllT; exact Bool.false_ne_true hAllT
          have hDeltaLen : (deltaOf P qIdx.1).length ≤ 38 + 1 := by
            dsimp only [deltaOf]
            rw [List.length_cons, List.length_zipWith, hPtsLen38 qIdx.1, ← hPtsVsLen qIdx.1,
                hPtsLen38 qIdx.1, Nat.min_self]
            exact Nat.le_refl 39
          simp only [Bool.not_false, Bool.true_and, ite_decide_eq]
          exact poly_roots_in_flatHemPool_le (deltaOf P qIdx.1) hDeltaLen hNz
      have hSumQ := qsum_le_qsum hPerQ
      rw [qsum_const, Nat.mul_comm (32 ^ 36)] at hSumQ
      exact Nat.le_trans hSumQ
        (Nat.mul_le_mul_right (32 ^ 36) (Nat.mul_le_mul_right 38 hCandsLen))
    exact Nat.le_trans hStepSplit (Nat.add_le_add hBoundA hBoundB)
  else
    have hZero : ∀ ch : Fin (2 ^ 256),
        (if flatHemState x [(m0, c0), (m1, c1), (m2, ch.1)] = true then 1 else 0) = 0 := by
      intro ch
      unfold flatHemState
      rw [decide_eq_false hWF, Bool.false_and]
      rfl
    rw [qsum_congr hZero, qsum_const, Nat.mul_zero]
    exact Nat.zero_le _

private theorem flatHem_round3_flips (x : WhirStmt QuarticGoldilocks)
    (m0 m1 m2 m3 : WhirMsg QuarticGoldilocks) (c0 c1 c2 : Nat)
    (hDoomed : flatHemState x [(m0, c0), (m1, c1), (m2, c2)] = false) :
    qsum (2 ^ 256) (fun ch =>
      if flatHemState x [(m0, c0), (m1, c1), (m2, c2), (m3, ch.1)] = true then 1 else 0) ≤
      2 ^ 8 * slicedFourChallengeCount 16 1 10 7 2 4 flatHemQ := by
  if hWF : m0.poly.length ≤ 5 ∧ m2.answers.length = 2 then
    let O0 := interleaveOracle 32 (fun p => x.table.getD p CommRingOps.zero)
    let q0 := decodeQuad c0
    let V0 := hemVirtualFoldOracle q0.2.1 q0.2.2.1 q0.2.2.2 hemFoldDom64 hemFoldDom32 O0
    let K0' := hemKernelFold q0.1 flatHemInitKernel
    let cl0' := hemBridgeFoldClaim x.claim
      (m0.poly.getD 0 CommRingOps.zero) (m0.poly.getD 1 CommRingOps.zero)
      (m0.poly.getD 2 CommRingOps.zero) (m0.poly.getD 3 CommRingOps.zero)
      (m0.poly.getD 4 CommRingOps.zero) q0.1 q0.2.1 q0.2.2.1 q0.2.2.2
    let ood0 := decodeOod c1
    let γ₀ := flatHemChalField c2 36
    let qPts0 := (List.range 36).map (fun j =>
      hemFoldDom32.getD (flatHemChalPos c2 j 32) CommRingOps.zero)
    let folded0 := (List.range 36).map (fun j => V0 (flatHemChalPos c2 j 32))
    let K1 := combineKernel6 K0' γ₀ ([ood0.1, ood0.2] ++ qPts0)
    let cl1 := combineClaim cl0' γ₀ (m2.answers ++ folded0)
    let O1 := interleaveOracle 16 (fun p => m1.table.getD p CommRingOps.zero)
    have hD3 : hasValidWitness 3 20 hemFoldDom32 O1 K1 cl1 = false := by
      unfold flatHemState at hDoomed
      rw [decide_eq_true hWF, Bool.true_and] at hDoomed
      exact hDoomed
    have hInv : ∀ Q : List QuarticGoldilocks,
        polyWitnessValid hemFoldDom32 (2 * 10) (2 * 1 + 1) O1 K1 cl1 Q = false :=
      hasValidWitness_false_imp 3 20 hemFoldDom32 antipodal_32_16.nodup_in (by decide)
        O1 K1 cl1 hD3
    have hK0Len : K0'.length = 6 :=
      (splitEvenOdd_spec 5 flatHemInitKernel q0.1 rfl).2.2.2.2
    have hK1Len : K1.length = 2 * 3 :=
      (combineKernel6_foldl_spec γ₀ [] (Nat.zero_le 4) ([ood0.1, ood0.2] ++ qPts0) K0' γ₀ hK0Len).1
    let M := flatHemQ * (flatHemQ * (flatHemQ * flatHemQ))
    have hMPos : 0 < M := Nat.mul_pos flatHemQ_pos
      (Nat.mul_pos flatHemQ_pos (Nat.mul_pos flatHemQ_pos flatHemQ_pos))
    have hModInv : ∀ c : Nat,
        flatHemState x [(m0, c0), (m1, c1), (m2, c2), (m3, c)] =
        flatHemState x [(m0, c0), (m1, c1), (m2, c2), (m3, c % M)] := by
      intro c
      unfold flatHemState
      dsimp only [M]
      have hDec : decodeQuad c = decodeQuad (c % M) := by
        unfold decodeQuad; dsimp only [M]; rw [Nat.mod_mod]
      rw [hDec]
    have h256 : 2 ^ 256 = 2 ^ 8 * M := by decide +kernel
    rw [qsum_mul_mod_eq h256 hMPos _
      (fun u => if flatHemState x [(m0, c0), (m1, c1), (m2, c2), (m3, u)] = true then 1 else 0)
      (fun ch => by rw [hModInv ch.1])]
    apply Nat.mul_le_mul_left (2 ^ 8)
    let predPool : Fin (quadPool flatHemPool).length → Bool :=
      fun idx => flatHemState x [(m0, c0), (m1, c1), (m2, c2), (m3, idx.1)]
    have hQsumPool :
        qsum M (fun idx =>
          if flatHemState x [(m0, c0), (m1, c1), (m2, c2), (m3, idx.1)] = true then 1 else 0) =
        (finFilterList (quadPool flatHemPool).length predPool).length := by
      rw [finFilterList_length]
      exact qsum_congr_len quadPool_flatHem_len.symm _ _
        (fun _ _ hij => by dsimp only [predPool]; rw [hij])
    rw [hQsumPool]
    have hParams : slicedParamsOk hemFoldDom16.length (1 + 1) (10 + 1) 7 2 4 = true := by
      rw [hemFoldDom16_len]; decide +kernel
    have hBound := sliced_singleStep_bridge_four_challenge_bound
      hemFoldDom32 hemFoldDom16 flatHemPool K1 1 10 7 2 4 3
      O1 cl1
      (m3.poly.getD 0 CommRingOps.zero) (m3.poly.getD 1 CommRingOps.zero)
      (m3.poly.getD 2 CommRingOps.zero) (m3.poly.getD 3 CommRingOps.zero)
      (m3.poly.getD 4 CommRingOps.zero)
      antipodal_32_16 flatHemPool_nodup (by decide) hK1Len hParams hInv
      (finFilterList (quadPool flatHemPool).length predPool)
      (finFilterList_nodup _ _)
      (fun ch hch hNo => by
        have hSt : flatHemState x [(m0, c0), (m1, c1), (m2, c2), (m3, ch.1)] = true :=
          finFilterList_sound _ _ ch hch
        unfold flatHemState at hSt
        rw [Bool.and_eq_true, Bool.and_eq_true, decodeQuad_eq_quadPool_get ch] at hSt
        obtain ⟨P, hP⟩ := (hasValidWitness_true_iff 2 11 hemFoldDom16 antipodal_32_16.nodup_out
          (by decide) _ _ _).mp hSt.2
        exact hNo ⟨P, hP⟩)
    rwa [hemFoldDom16_len, flatHemPool_length] at hBound
  else
    have hZero : ∀ ch : Fin (2 ^ 256),
        (if flatHemState x [(m0, c0), (m1, c1), (m2, c2), (m3, ch.1)] = true then 1 else 0) = 0 := by
      intro ch
      unfold flatHemState
      rw [decide_eq_false hWF, Bool.false_and, Bool.false_and]
      rfl
    rw [qsum_congr hZero, qsum_const, Nat.mul_zero]
    exact Nat.zero_le _

private theorem flatHem_stage_folded_eq
    (D_in D_out : List QuarticGoldilocks) (i t n : Nat)
    (raw : Nat → QuarticGoldilocks) (cFold cAns : Nat) (pub : WhirPub QuarticGoldilocks)
    (tailVals : List QuarticGoldilocks)
    (hi : (i = 0 ∧ D_in = hemFoldDom64 ∧ D_out = hemFoldDom32) ∨
          (i = 1 ∧ D_in = hemFoldDom32 ∧ D_out = hemFoldDom16)) :
    let qs := (List.range t).flatMap (fun j =>
      [flatHemChalPos cAns j n, flatHemChalPos cAns j n + n])
    let vals := qs.map raw ++ tailVals
    (List.range t).map (fun j =>
      flatHemRawFold i [(pub, cFold)] j (flatHemChalPos cAns j n)
        ((vals.drop (j * 2)).take 2)) =
    (List.range t).map (fun j =>
      let q := decodeQuad cFold
      hemVirtualFoldOracle q.2.1 q.2.2.1 q.2.2.2 D_in D_out (interleaveOracle n raw)
        (flatHemChalPos cAns j n)) := by
  dsimp only
  apply List.map_congr_left
  intro j hj
  have hjLt : j < t := List.mem_range.mp hj
  have hSplitRange : List.range t = List.range j ++ (j :: (List.range (t - j - 1)).map (fun u => j + 1 + u)) := by
    have h1 : t = j + (1 + (t - j - 1)) := by omega
    have hGen : ∀ (a b : Nat), List.range (a + b) = List.range a ++ (List.range b).map (a + ·) := by
      intro a b
      induction b with
      | zero => rw [Nat.add_zero, List.range_zero, List.map_nil, List.append_nil]
      | succ b ihb =>
        rw [← Nat.add_assoc, List.range_succ, ihb, List.range_succ, List.map_append,
            List.map_cons, List.map_nil, List.append_assoc]
    conv => lhs; rw [h1, hGen j (1 + (t - j - 1)), hGen 1 (t - j - 1)]
    simp only [List.range_one, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
      Nat.add_zero, List.map_map]
    congr 1
    congr 1
    apply List.map_congr_left; intro u _; dsimp only [Function.comp]; omega
  let pre := (List.range j).flatMap (fun u =>
    [flatHemChalPos cAns u n, flatHemChalPos cAns u n + n])
  have hPreLen : (pre.map raw).length = j * 2 := by
    rw [List.length_map]
    dsimp only [pre]
    clear hj hjLt hSplitRange
    induction j with
    | zero => rfl
    | succ k ihk =>
      rw [List.range_succ, List.flatMap_append, List.length_append, ihk,
          List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_cons,
          List.length_cons, List.length_nil, Nat.succ_mul]
  have hBlock :
      ((((List.range t).flatMap (fun u =>
          [flatHemChalPos cAns u n, flatHemChalPos cAns u n + n])).map raw ++ tailVals).drop
        (j * 2)).take 2 =
      [raw (flatHemChalPos cAns j n), raw (flatHemChalPos cAns j n + n)] := by
    rw [hSplitRange, List.flatMap_append, List.flatMap_cons, List.map_append, List.map_append,
        List.append_assoc, List.append_assoc, ← hPreLen]
    have hDropApp : ∀ {α : Type} (xs ys : List α), (xs ++ ys).drop xs.length = ys := by
      intro α xs ys; induction xs with | nil => rfl | cons _ tl iht => exact iht
    rw [hDropApp (pre.map raw)]
    rfl
  rw [hBlock]
  unfold flatHemRawFold
  dsimp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  rcases hi with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · rw [ite_true_eq _ _ rfl]
    exact flatHemFoldPoint_eq_virtual hemFoldDom64 hemFoldDom32 n raw _ _ _ _
  · rw [ite_false_eq _ _ (by decide)]
    exact flatHemFoldPoint_eq_virtual hemFoldDom32 hemFoldDom16 n raw _ _ _ _

private theorem splitStages_flatHem {F : Type} [CommRingOps F] [DecidableEq F]
    (a0 a1 a2 a3 a4 a5 : WhirPub F × Nat) :
    splitStages [flatHemStage0, flatHemStage1] [a0, a1, a2, a3, a4, a5] =
      some [⟨[a0], a1, a2⟩, ⟨[a3], a4, a5⟩] := rfl

private theorem flatHemStage_ver_fields :
    flatHemStage0.foldK = 1 ∧ flatHemStage0.sumcheckDeg = 4 ∧ flatHemStage0.oodCount = 2 ∧
    flatHemStage0.queryCount = 36 ∧ flatHemStage0.domainSize = 32 ∧
    flatHemStage1.foldK = 1 ∧ flatHemStage1.sumcheckDeg = 4 ∧ flatHemStage1.oodCount = 2 ∧
    flatHemStage1.queryCount = 46 ∧ flatHemStage1.domainSize = 16 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem list_append_congr {α : Type} {a₁ a₂ b₁ b₂ : List α}
    (h1 : a₁ = a₂) (h2 : b₁ = b₂) : a₁ ++ b₁ = a₂ ++ b₂ := by
  rw [h1, h2]

private theorem flatHemQueries_eq {F : Type} [CommRingOps F] [DecidableEq F]
    (a0 a1 a2 a3 a4 a5 : WhirPub QuarticGoldilocks × Nat) :
    whirQueries flatHemSlicedEnv flatHemSlicedSched [a0, a1, a2, a3, a4, a5] =
      ((List.range 36).flatMap (fun j =>
        [(0, flatHemChalPos a2.2 j 32), (0, flatHemChalPos a2.2 j 32 + 32)])) ++
      ((List.range 46).flatMap (fun j =>
        [(1, flatHemChalPos a5.2 j 16), (1, flatHemChalPos a5.2 j 16 + 16)])) := by
  unfold whirQueries flatHemSlicedSched
  dsimp only
  rw [splitStages_flatHem]
  unfold allStageQueries stageQueries
  dsimp only
  rcases flatHemStage_ver_fields with ⟨hf0, _, _, hq0, hd0, hf1, _, _, hq1, hd1⟩
  rw [hf0, hq0, hd0]
  unfold allStageQueries stageQueries
  dsimp only
  rw [hf1, hq1, hd1]
  unfold allStageQueries
  have hR2 : List.range (2 ^ 1) = [0, 1] := rfl
  simp only [flatHemSlicedEnv, hR2, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.add_zero, Nat.one_mul, List.append_nil]

private theorem flatHem_verify_extract_final (x : WhirStmt QuarticGoldilocks)
    (m0 m1 m2 m3 m4 m5 : WhirMsg QuarticGoldilocks) (c0 c1 c2 c3 c4 c5 : Nat)
    (hVer : (whirOracleIop flatHemSlicedEnv flatHemSlicedSched 256).verify x
      [(m0, c0), (m1, c1), (m2, c2), (m3, c3), (m4, c4), (m5, c5)] = true) :
    let O0 := interleaveOracle 32 (fun p => x.table.getD p CommRingOps.zero)
    let q0 := decodeQuad c0
    let V0 := hemVirtualFoldOracle q0.2.1 q0.2.2.1 q0.2.2.2 hemFoldDom64 hemFoldDom32 O0
    let K0' := hemKernelFold q0.1 flatHemInitKernel
    let cl0' := hemBridgeFoldClaim x.claim
      (m0.poly.getD 0 CommRingOps.zero) (m0.poly.getD 1 CommRingOps.zero)
      (m0.poly.getD 2 CommRingOps.zero) (m0.poly.getD 3 CommRingOps.zero)
      (m0.poly.getD 4 CommRingOps.zero) q0.1 q0.2.1 q0.2.2.1 q0.2.2.2
    let ood0 := decodeOod c1
    let γ₀ := flatHemChalField c2 36
    let qPts0 := (List.range 36).map (fun j =>
      hemFoldDom32.getD (flatHemChalPos c2 j 32) CommRingOps.zero)
    let folded0 := (List.range 36).map (fun j => V0 (flatHemChalPos c2 j 32))
    let K1 := combineKernel6 K0' γ₀ ([ood0.1, ood0.2] ++ qPts0)
    let cl1 := combineClaim cl0' γ₀ (m2.answers ++ folded0)
    let O1 := interleaveOracle 16 (fun p => m1.table.getD p CommRingOps.zero)
    let q1 := decodeQuad c3
    let V1 := hemVirtualFoldOracle q1.2.1 q1.2.2.1 q1.2.2.2 hemFoldDom32 hemFoldDom16 O1
    let K2 := hemKernelFold q1.1 K1
    let cl2 := hemBridgeFoldClaim cl1
      (m3.poly.getD 0 CommRingOps.zero) (m3.poly.getD 1 CommRingOps.zero)
      (m3.poly.getD 2 CommRingOps.zero) (m3.poly.getD 3 CommRingOps.zero)
      (m3.poly.getD 4 CommRingOps.zero) q1.1 q1.2.1 q1.2.2.1 q1.2.2.2
    (m0.poly.length ≤ 5 ∧ m2.answers.length = 2) ∧
    m3.poly.length ≤ 5 ∧
    m4.poly.length ≤ 3 ∧
    ringDot m4.poly K2 = cl2 ∧
    ∀ j < 46,
      RoundPoly.evalCoeffs m4.poly
        (hemFoldDom16.getD (flatHemChalPos c5 j 16) CommRingOps.zero) =
      V1 (flatHemChalPos c5 j 16) := by
  dsimp only
  rw [OracleIop.verify_eq] at hVer
  obtain ⟨_, hVerd⟩ := Bool.and_eq_true_iff.mp hVer
  dsimp only [whirOracleIop, List.map] at hVerd
  have hValsEq :
      (whirQueries flatHemSlicedEnv flatHemSlicedSched
        [(⟨m0.poly, m0.answers⟩, c0), (⟨m1.poly, m1.answers⟩, c1),
         (⟨m2.poly, m2.answers⟩, c2), (⟨m3.poly, m3.answers⟩, c3),
         (⟨m4.poly, m4.answers⟩, c4), (⟨m5.poly, m5.answers⟩, c5)]).map
        (fun q => whirTable flatHemSlicedSched x
          [m0, m1, m2, m3, m4, m5] q.1 q.2) =
      ((List.range 36).flatMap (fun j =>
        [flatHemChalPos c2 j 32, flatHemChalPos c2 j 32 + 32])).map
          (fun p => x.table.getD p CommRingOps.zero) ++
      ((List.range 46).flatMap (fun j =>
        [flatHemChalPos c5 j 16, flatHemChalPos c5 j 16 + 16])).map
          (fun p => m1.table.getD p CommRingOps.zero) := by
    rw [flatHemQueries_eq (F := QuarticGoldilocks), List.map_append]
    dsimp only
    refine list_append_congr ?_ ?_
    · generalize List.range 36 = l0
      induction l0 with
      | nil => rfl
      | cons u us ih =>
        rw [List.flatMap_cons, List.map_append, ih, List.flatMap_cons, List.map_append]; rfl
    · generalize List.range 46 = l1
      induction l1 with
      | nil => rfl
      | cons u us ih =>
        rw [List.flatMap_cons, List.map_append, ih, List.flatMap_cons, List.map_append]; rfl
  rw [hValsEq] at hVerd
  unfold whirVerdict flatHemSlicedSched at hVerd
  dsimp only at hVerd
  rw [splitStages_flatHem] at hVerd
  unfold whirCheckStages whirCheckStagesAux stageFoldRun stageFoldRunAux flatHemSlicedEnv at hVerd
  dsimp only at hVerd
  rcases flatHemStage_ver_fields with ⟨hf0, _, ho0, hq0, hd0, hf1, _, ho1, hq1, hd1⟩
  rw [hf0, ho0, hq0, hd0] at hVerd
  if hm0 : m0.poly.length ≤ 5 then
    have hStep0 : flatHemStepClaim 0 x.claim m0.poly c0 =
        some (hemBridgeFoldClaim x.claim
          (m0.poly.getD 0 CommRingOps.zero) (m0.poly.getD 1 CommRingOps.zero)
          (m0.poly.getD 2 CommRingOps.zero) (m0.poly.getD 3 CommRingOps.zero)
          (m0.poly.getD 4 CommRingOps.zero)
          (decodeQuad c0).1 (decodeQuad c0).2.1 (decodeQuad c0).2.2.1 (decodeQuad c0).2.2.2) := by
      unfold flatHemStepClaim
      rw [ite_true_eq _ _ hm0]
      dsimp only
      rw [flatHemBridgeClaim_eq]
    rw [hStep0] at hVerd
    unfold stageFoldRunAux at hVerd
    dsimp only [Option.map] at hVerd
    have hLen0 : (((List.range 36).flatMap (fun j =>
        [flatHemChalPos c2 j 32, flatHemChalPos c2 j 32 + 32])).map
          (fun p => x.table.getD p CommRingOps.zero)).length = 36 * 2 := by
      rw [List.length_map]
      clear hVerd hValsEq
      have hAux : ∀ k : Nat,
          ((List.range k).flatMap (fun j =>
            [flatHemChalPos c2 j 32, flatHemChalPos c2 j 32 + 32])).length = k * 2 := by
        intro k; induction k with
        | zero => rfl
        | succ k ih =>
          rw [List.range_succ, List.flatMap_append, List.length_append, ih,
              List.flatMap_cons, List.flatMap_nil, List.append_nil, Nat.succ_mul]; rfl
      exact hAux 36
    have hFolded0 := flatHem_stage_folded_eq hemFoldDom64 hemFoldDom32 0 36 32
      (fun p => x.table.getD p CommRingOps.zero) c0 c2 ⟨m0.poly, m0.answers⟩
      (((List.range 46).flatMap (fun j =>
        [flatHemChalPos c5 j 16, flatHemChalPos c5 j 16 + 16])).map
          (fun p => m1.table.getD p CommRingOps.zero))
      (.inl ⟨rfl, rfl, rfl⟩)
    dsimp only at hFolded0
    rw [show 2 ^ 1 = 2 from rfl, hFolded0] at hVerd
    have hDrop0 : ∀ {α : Type} (xs ys : List α), (xs ++ ys).drop xs.length = ys := by
      intro α xs ys; induction xs with | nil => rfl | cons _ tl iht => exact iht
    rw [Bool.and_eq_true, Bool.and_eq_true] at hVerd
    obtain ⟨⟨hYs0D, _⟩, hStage1⟩ := hVerd
    have hYs0 : m2.answers.length = 2 := of_decide_eq_true hYs0D
    dsimp only [List.isEmpty] at hStage1
    rw [ite_false_eq _ _ Bool.false_ne_true, ← hLen0, hDrop0,
        show (0 : Nat) + 1 = 1 from rfl] at hStage1
    generalize combineClaim
      (hemBridgeFoldClaim x.claim
        (m0.poly.getD 0 CommRingOps.zero) (m0.poly.getD 1 CommRingOps.zero)
        (m0.poly.getD 2 CommRingOps.zero) (m0.poly.getD 3 CommRingOps.zero)
        (m0.poly.getD 4 CommRingOps.zero)
        (decodeQuad c0).1 (decodeQuad c0).2.1 (decodeQuad c0).2.2.1 (decodeQuad c0).2.2.2)
      (flatHemChalField c2 36)
      (m2.answers ++ (List.range 36).map (fun j =>
        hemVirtualFoldOracle (decodeQuad c0).2.1 (decodeQuad c0).2.2.1 (decodeQuad c0).2.2.2
          hemFoldDom64 hemFoldDom32
          (interleaveOracle 32 (fun p => x.table.getD p CommRingOps.zero))
          (flatHemChalPos c2 j 32))) = cl1 at hStage1 ⊢
    unfold whirCheckStagesAux stageFoldRun stageFoldRunAux at hStage1
    dsimp only at hStage1
    rw [hf1, ho1, hq1, hd1] at hStage1
    if hm3 : m3.poly.length ≤ 5 then
      have hStep1 : flatHemStepClaim 1 cl1 m3.poly c3 =
          some (hemBridgeFoldClaim cl1
            (m3.poly.getD 0 CommRingOps.zero) (m3.poly.getD 1 CommRingOps.zero)
            (m3.poly.getD 2 CommRingOps.zero) (m3.poly.getD 3 CommRingOps.zero)
            (m3.poly.getD 4 CommRingOps.zero)
            (decodeQuad c3).1 (decodeQuad c3).2.1 (decodeQuad c3).2.2.1 (decodeQuad c3).2.2.2) := by
        unfold flatHemStepClaim
        rw [ite_true_eq _ _ hm3]
        dsimp only
        rw [flatHemBridgeClaim_eq]
      rw [hStep1] at hStage1
      unfold stageFoldRunAux at hStage1
      dsimp only [Option.map, List.isEmpty] at hStage1
      have hFolded1 := flatHem_stage_folded_eq hemFoldDom32 hemFoldDom16 1 46 16
        (fun p => m1.table.getD p CommRingOps.zero) c3 c5 ⟨m3.poly, m3.answers⟩ []
        (.inr ⟨rfl, rfl, rfl⟩)
      dsimp only at hFolded1
      rw [List.append_nil] at hFolded1
      rw [show 2 ^ 1 = 2 from rfl, hFolded1] at hStage1
      simp only [↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hStage1
      obtain ⟨_, ⟨⟨⟨hm4, _⟩, hShifts1⟩, hClEq⟩, _⟩ := hStage1
      have hFinalEq :
          flatHemFinalClaimViews
            [⟨[(⟨m0.poly, m0.answers⟩, c0)], (⟨m1.poly, m1.answers⟩, c1),
              (⟨m2.poly, m2.answers⟩, c2)⟩,
             ⟨[(⟨m3.poly, m3.answers⟩, c3)], (⟨m4.poly, m4.answers⟩, c4),
              (⟨m5.poly, m5.answers⟩, c5)⟩] [CommRingOps.zero] =
          ringDot m4.poly
            (hemKernelFold (decodeQuad c3).1
              (combineKernel6 (hemKernelFold (decodeQuad c0).1 flatHemInitKernel)
                (flatHemChalField c2 36)
                ([(decodeOod c1).1, (decodeOod c1).2] ++
                  (List.range 36).map (fun j =>
                    hemFoldDom32.getD (flatHemChalPos c2 j 32) CommRingOps.zero)))) := by
        unfold flatHemFinalClaimViews
        dsimp only
        rw [flatHemKernelFold_eq, flatHemKernelFold_eq]
      rw [hFinalEq] at hClEq
      refine ⟨⟨hm0, hYs0⟩, hm3, hm4, hClEq.symm, ?_⟩
      intro j hj
      have hZipMem : (j, hemVirtualFoldOracle (decodeQuad c3).2.1 (decodeQuad c3).2.2.1
          (decodeQuad c3).2.2.2 hemFoldDom32 hemFoldDom16
          (interleaveOracle 16 (fun p => m1.table.getD p CommRingOps.zero))
          (flatHemChalPos c5 j 16)) ∈
        (List.range 46).zip ((List.range 46).map (fun u =>
          hemVirtualFoldOracle (decodeQuad c3).2.1 (decodeQuad c3).2.2.1 (decodeQuad c3).2.2.2
            hemFoldDom32 hemFoldDom16
            (interleaveOracle 16 (fun p => m1.table.getD p CommRingOps.zero))
            (flatHemChalPos c5 u 16))) := by
        have hZipSelf : ∀ {α β : Type} (l : List α) (f : α → β),
            l.zip (l.map f) = l.map (fun a => (a, f a)) := by
          intro α β l f; induction l with
          | nil => rfl
          | cons a as iha => simp only [List.map_cons, List.zip_cons_cons, iha]
        rw [hZipSelf]
        exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
      exact of_decide_eq_true (List.all_eq_true.mp hShifts1 _ hZipMem)
    else
      unfold flatHemStepClaim at hStage1
      rw [ite_false_eq _ _ hm3] at hStage1
      exact absurd hStage1 Bool.false_ne_true
  else
    unfold flatHemStepClaim at hVerd
    rw [ite_false_eq _ _ hm0] at hVerd
    exact absurd hVerd Bool.false_ne_true

private theorem flatHem_verify_mod_c5 (x : WhirStmt QuarticGoldilocks)
    (m0 m1 m2 m3 m4 m5 : WhirMsg QuarticGoldilocks) (c0 c1 c2 c3 c4 c5 : Nat) :
    (whirOracleIop flatHemSlicedEnv flatHemSlicedSched 256).verify x
      [(m0, c0), (m1, c1), (m2, c2), (m3, c3), (m4, c4), (m5, c5)] =
    (whirOracleIop flatHemSlicedEnv flatHemSlicedSched 256).verify x
      [(m0, c0), (m1, c1), (m2, c2), (m3, c3), (m4, c4),
       (m5, c5 % (16 ^ 46 * flatHemQ))] := by
  have hPosMod : ∀ j : Nat,
      flatHemChalPos c5 j 16 = flatHemChalPos (c5 % (16 ^ 46 * flatHemQ)) j 16 := by
    intro j
    unfold flatHemChalPos
    dsimp only
    have hNe : ¬ (16 = 32) := by decide
    simp only [hNe, ↓reduceIte, Nat.mod_mod]
  have hQMod :
      whirQueries flatHemSlicedEnv flatHemSlicedSched
        [(⟨m0.poly, m0.answers⟩, c0), (⟨m1.poly, m1.answers⟩, c1),
         (⟨m2.poly, m2.answers⟩, c2), (⟨m3.poly, m3.answers⟩, c3),
         (⟨m4.poly, m4.answers⟩, c4), (⟨m5.poly, m5.answers⟩, c5)] =
      whirQueries flatHemSlicedEnv flatHemSlicedSched
        [(⟨m0.poly, m0.answers⟩, c0), (⟨m1.poly, m1.answers⟩, c1),
         (⟨m2.poly, m2.answers⟩, c2), (⟨m3.poly, m3.answers⟩, c3),
         (⟨m4.poly, m4.answers⟩, c4),
         (⟨m5.poly, m5.answers⟩, c5 % (16 ^ 46 * flatHemQ))] := by
    rw [flatHemQueries_eq (F := QuarticGoldilocks), flatHemQueries_eq (F := QuarticGoldilocks)]
    refine list_append_congr rfl ?_
    generalize List.range 46 = js
    induction js with
    | nil => rfl
    | cons j rest ih => simp only [List.flatMap_cons, hPosMod j, ih]
  rw [OracleIop.verify_eq, OracleIop.verify_eq]
  dsimp only [whirOracleIop, List.map, List.length]
  rw [hQMod]
  refine congrArg (decide (6 = flatHemSlicedSched.numRounds) && ·) ?_
  unfold whirVerdict flatHemSlicedSched
  dsimp only
  rw [splitStages_flatHem, splitStages_flatHem]
  unfold whirCheckStages whirCheckStagesAux flatHemSlicedEnv
  dsimp only
  rcases flatHemStage_ver_fields with ⟨hf0, hs0, ho0, hq0, hd0, hf1, hs1, ho1, hq1, hd1⟩
  rw [hf0, hs0, ho0, hq0, hd0]
  cases stageFoldRun _ 0 4 x.claim [(⟨m0.poly, m0.answers⟩, c0)] with
  | none => rfl
  | some p0 =>
    dsimp only [List.isEmpty]
    rw [ite_false_eq _ _ Bool.false_ne_true, ite_false_eq _ _ Bool.false_ne_true]
    refine congrArg (_ && ·) ?_
    unfold whirCheckStagesAux
    dsimp only
    rw [hf1, hs1, ho1, hq1, hd1]
    cases stageFoldRun _ 1 4 _ [(⟨m3.poly, m3.answers⟩, c3)] with
    | none => rfl
    | some p1 =>
      dsimp only [List.isEmpty, flatHemFinalClaimViews]
      rw [ite_true_eq _ _ rfl, ite_true_eq _ _ rfl]
      have hFoldCongr : ∀ vals1 : List QuarticGoldilocks,
          (List.range 46).map (fun j =>
            flatHemRawFold 1 [(⟨m3.poly, m3.answers⟩, c3)] j (flatHemChalPos c5 j 16)
              ((vals1.drop (j * 2)).take 2)) =
          (List.range 46).map (fun j =>
            flatHemRawFold 1 [(⟨m3.poly, m3.answers⟩, c3)] j
              (flatHemChalPos (c5 % (16 ^ 46 * flatHemQ)) j 16)
              ((vals1.drop (j * 2)).take 2)) := by
        intro vals1; apply List.map_congr_left; intro j _; rw [hPosMod j]
      rw [hFoldCongr]
      congr 2
      congr 1
      congr 1
      exact list_all_congr _ _ (fun jv => by simp only [hPosMod jv.1]) _

private theorem flatHem_round5_flips (x : WhirStmt QuarticGoldilocks)
    (m0 m1 m2 m3 m4 m5 : WhirMsg QuarticGoldilocks) (c0 c1 c2 c3 c4 : Nat)
    (hDoomed : flatHemState x [(m0, c0), (m1, c1), (m2, c2), (m3, c3), (m4, c4)] = false) :
    qsum (2 ^ 256) (fun ch =>
      if flatHemState x [(m0, c0), (m1, c1), (m2, c2), (m3, c3), (m4, c4), (m5, ch.1)] = true
      then 1 else 0) ≤
      2 ^ 10 * (11 ^ 46 * flatHemQ) := by
  let M := 16 ^ 46 * flatHemQ
  have hMPos : 0 < M := Nat.mul_pos (Nat.pow_pos (by decide)) flatHemQ_pos
  have h256 : 2 ^ 256 = 2 ^ 10 * M := by decide +kernel
  have hSt6 : ∀ c : Nat,
      flatHemState x [(m0, c0), (m1, c1), (m2, c2), (m3, c3), (m4, c4), (m5, c)] =
      (whirOracleIop flatHemSlicedEnv flatHemSlicedSched 256).verify x
        [(m0, c0), (m1, c1), (m2, c2), (m3, c3), (m4, c4), (m5, c % M)] := by
    intro c
    unfold flatHemState
    exact flatHem_verify_mod_c5 x m0 m1 m2 m3 m4 m5 c0 c1 c2 c3 c4 c
  rw [qsum_mul_mod_eq h256 hMPos _
      (fun u => if (whirOracleIop flatHemSlicedEnv flatHemSlicedSched 256).verify x
        [(m0, c0), (m1, c1), (m2, c2), (m3, c3), (m4, c4), (m5, u)] = true then 1 else 0)
      (fun ch => by rw [hSt6 ch.1])]
  apply Nat.mul_le_mul_left (2 ^ 10)
  let O0 := interleaveOracle 32 (fun p => x.table.getD p CommRingOps.zero)
  let q0 := decodeQuad c0
  let V0 := hemVirtualFoldOracle q0.2.1 q0.2.2.1 q0.2.2.2 hemFoldDom64 hemFoldDom32 O0
  let K0' := hemKernelFold q0.1 flatHemInitKernel
  let cl0' := hemBridgeFoldClaim x.claim
    (m0.poly.getD 0 CommRingOps.zero) (m0.poly.getD 1 CommRingOps.zero)
    (m0.poly.getD 2 CommRingOps.zero) (m0.poly.getD 3 CommRingOps.zero)
    (m0.poly.getD 4 CommRingOps.zero) q0.1 q0.2.1 q0.2.2.1 q0.2.2.2
  let ood0 := decodeOod c1
  let γ₀ := flatHemChalField c2 36
  let qPts0 := (List.range 36).map (fun j =>
    hemFoldDom32.getD (flatHemChalPos c2 j 32) CommRingOps.zero)
  let folded0 := (List.range 36).map (fun j => V0 (flatHemChalPos c2 j 32))
  let K1 := combineKernel6 K0' γ₀ ([ood0.1, ood0.2] ++ qPts0)
  let cl1 := combineClaim cl0' γ₀ (m2.answers ++ folded0)
  let O1 := interleaveOracle 16 (fun p => m1.table.getD p CommRingOps.zero)
  let q1 := decodeQuad c3
  let V1 := hemVirtualFoldOracle q1.2.1 q1.2.2.1 q1.2.2.2 hemFoldDom32 hemFoldDom16 O1
  let K2 := hemKernelFold q1.1 K1
  let cl2 := hemBridgeFoldClaim cl1
    (m3.poly.getD 0 CommRingOps.zero) (m3.poly.getD 1 CommRingOps.zero)
    (m3.poly.getD 2 CommRingOps.zero) (m3.poly.getD 3 CommRingOps.zero)
    (m3.poly.getD 4 CommRingOps.zero) q1.1 q1.2.1 q1.2.2.1 q1.2.2.2
  let goodPos (pos : Nat) : Bool :=
    decide (RoundPoly.evalCoeffs m4.poly (hemFoldDom16.getD pos CommRingOps.zero) = V1 pos)
  if hAnyVer : (finFilterList M (fun idx =>
      (whirOracleIop flatHemSlicedEnv flatHemSlicedSched 256).verify x
        [(m0, c0), (m1, c1), (m2, c2), (m3, c3), (m4, c4), (m5, idx.1)])).isEmpty = false then
    rcases hFL : finFilterList M _ with _ | ⟨idx0, _⟩
    · rw [hFL] at hAnyVer; exact nomatch hAnyVer
    · have hVer0 : (whirOracleIop flatHemSlicedEnv flatHemSlicedSched 256).verify x
          [(m0, c0), (m1, c1), (m2, c2), (m3, c3), (m4, c4), (m5, idx0.1)] = true :=
        finFilterList_sound _ _ idx0 (by rw [hFL]; exact List.mem_cons_self)
      obtain ⟨hWF02, hm3, hm4, hDot, _⟩ :=
        flatHem_verify_extract_final x m0 m1 m2 m3 m4 m5 c0 c1 c2 c3 c4 idx0.1 hVer0
      have hD4 : hasValidWitness 2 11 hemFoldDom16 V1 K2 cl2 = false := by
        have h4 := hDoomed
        unfold flatHemState at h4
        unfold flatHemState at h4
        change (decide (m0.poly.length ≤ 5 ∧ m2.answers.length = 2) &&
          decide (m3.poly.length ≤ 5) &&
          hasValidWitness 2 11 hemFoldDom16 V1 K2 cl2) = false at h4
        rw [decide_eq_true hWF02, decide_eq_true hm3, Bool.true_and, Bool.true_and] at h4
        exact h4
      have hGoodLe : qsum 16 (fun pos => if goodPos pos.1 = true then 1 else 0) ≤ 11 := by
        apply Decidable.byContradiction
        intro hGt11
        have hAgCount :
            qsum 16 (fun pos => if goodPos pos.1 = true then 1 else 0) =
            hemCosetAgreeCount hemFoldDom16 V1 m4.poly := by
          rw [hemCosetAgreeCount_def]
          exact qsum_congr_len hemFoldDom16_len.symm _ _ (fun pos j hpj => by
            dsimp only [goodPos]
            rw [← list_getD_eq_get hemFoldDom16 CommRingOps.zero j, ← hpj]
            by_cases he : RoundPoly.evalCoeffs m4.poly
                (hemFoldDom16.getD pos.1 CommRingOps.zero) = V1 pos.1
            · simp only [he, decide_true, ↓reduceIte]
            · have he' : V1 pos.1 ≠ RoundPoly.evalCoeffs m4.poly
                  (hemFoldDom16.getD pos.1 CommRingOps.zero) := fun e => he e.symm
              simp only [he, he', decide_false, Bool.false_eq_true, ↓reduceIte])
        have hPW : polyWitnessValid hemFoldDom16 11 2 V1 K2 cl2 m4.poly = true := by
          rw [polyWitnessValid_def, ← hAgCount, decide_eq_true hm4,
              decide_eq_true (by omega : 11 ≤ _), decide_eq_true hDot]
          rfl
        have hWit := (hasValidWitness_true_iff 2 11 hemFoldDom16 antipodal_32_16.nodup_out
          (by decide) V1 K2 cl2).mpr ⟨m4.poly, hPW⟩
        rw [hD4] at hWit
        exact Bool.false_ne_true hWit
      have hIdxEq : ∀ idx : Fin M,
          idx.1 = (idx.1 / flatHemQ) * flatHemQ + idx.1 % flatHemQ := by
        intro idx
        have h := Nat.div_add_mod idx.1 flatHemQ
        rw [Nat.mul_comm] at h; exact h.symm
      have hRew : ∀ idx : Fin M,
          (if (whirOracleIop flatHemSlicedEnv flatHemSlicedSched 256).verify x
            [(m0, c0), (m1, c1), (m2, c2), (m3, c3), (m4, c4), (m5, idx.1)] = true then 1 else 0) =
          (fun qIdx gIdx =>
            if (whirOracleIop flatHemSlicedEnv flatHemSlicedSched 256).verify x
              [(m0, c0), (m1, c1), (m2, c2), (m3, c3), (m4, c4),
               (m5, qIdx * flatHemQ + gIdx)] = true then 1 else 0)
            (idx.1 / flatHemQ) (idx.1 % flatHemQ) := by
        intro idx; dsimp only; rw [← hIdxEq idx]
      rw [qsum_congr hRew]
      dsimp only [M]
      rw [qsum_mul_div_mod_eq (16 ^ 46) flatHemQ flatHemQ_pos
        (fun qIdx gIdx =>
          if (whirOracleIop flatHemSlicedEnv flatHemSlicedSched 256).verify x
            [(m0, c0), (m1, c1), (m2, c2), (m3, c3), (m4, c4),
             (m5, qIdx * flatHemQ + gIdx)] = true then 1 else 0)]
      have hPerPair : ∀ (qIdx : Fin (16 ^ 46)) (gIdx : Fin flatHemQ),
          (if (whirOracleIop flatHemSlicedEnv flatHemSlicedSched 256).verify x
            [(m0, c0), (m1, c1), (m2, c2), (m3, c3), (m4, c4),
             (m5, qIdx.1 * flatHemQ + gIdx.1)] = true then 1 else 0) ≤
          (if allGoodDigits 16 goodPos 46 qIdx.1 = true then 1 else 0) := by
        intro qIdx gIdx
        cases hV : (whirOracleIop flatHemSlicedEnv flatHemSlicedSched 256).verify x
            [(m0, c0), (m1, c1), (m2, c2), (m3, c3), (m4, c4),
             (m5, qIdx.1 * flatHemQ + gIdx.1)] with
        | false => rw [ite_false_eq _ _ Bool.false_ne_true]; exact Nat.zero_le _
        | true =>
          rw [ite_true_eq _ _ rfl]
          have hChecks := (flatHem_verify_extract_final x m0 m1 m2 m3 m4 m5
            c0 c1 c2 c3 c4 (qIdx.1 * flatHemQ + gIdx.1) hV).2.2.2.2
          have hAll : ((List.range 46).all (fun j => goodPos ((qIdx.1 / 16 ^ j) % 16))) = true := by
            refine List.all_eq_true.mpr (fun j hj => ?_)
            have hlt : qIdx.1 * flatHemQ + gIdx.1 < 16 ^ 46 * flatHemQ := by
              have h1 : (qIdx.1 + 1) * flatHemQ ≤ 16 ^ 46 * flatHemQ :=
                Nat.mul_le_mul_right flatHemQ qIdx.2
              rw [Nat.add_mul, Nat.one_mul] at h1
              have hg := gIdx.2
              omega
            have hPosEq : flatHemChalPos (qIdx.1 * flatHemQ + gIdx.1) j 16 =
                (qIdx.1 / 16 ^ j) % 16 := by
              unfold flatHemChalPos
              dsimp only
              have hNe : ¬ (16 = 32) := by decide
              simp only [hNe, ↓reduceIte]
              rw [Nat.mod_eq_of_lt hlt,
                  Nat.add_comm (qIdx.1 * flatHemQ), Nat.add_mul_div_right _ _ flatHemQ_pos,
                  Nat.div_eq_of_lt gIdx.2, Nat.zero_add]
            have hCj := hChecks j (List.mem_range.mp hj)
            rw [hPosEq] at hCj
            exact decide_eq_true hCj
          rw [allGoodDigits_eq_range 16 (by decide) goodPos 46 qIdx.1] at hAll
          rw [ite_true_eq _ _ hAll]
          exact Nat.le_refl 1
      have hStep := qsum_le_qsum (fun qIdx => by
        have hS := qsum_le_qsum (hPerPair qIdx)
        rw [qsum_const, Nat.mul_comm flatHemQ] at hS
        exact hS)
      rw [qsum_mul_right] at hStep
      exact Nat.le_trans hStep
        (Nat.mul_le_mul_right flatHemQ
          (qsum_allGoodDigits_le 16 11 (by decide) goodPos hGoodLe 46))
  else
    have hEmp : (finFilterList M (fun idx =>
        (whirOracleIop flatHemSlicedEnv flatHemSlicedSched 256).verify x
          [(m0, c0), (m1, c1), (m2, c2), (m3, c3), (m4, c4), (m5, idx.1)])).length = 0 := by
      cases hL : finFilterList M _ with
      | nil => rfl
      | cons _ _ => rw [hL] at hAnyVer; exact absurd rfl hAnyVer
    rw [← finFilterList_length, hEmp]
    exact Nat.zero_le _

private theorem slicedFour_le_mcaNum_core (q W badMca jb0 jb1 L : Nat)
    (hQ : 0 < q) (hPowEq : 2 ^ 8 * (q ^ 3) * q = W)
    (hLo : jb0 ≤ L) (hHi : jb1 ≤ L) :
    2 ^ 8 * ((q * q) * badMca + (3 * (jb0 * jb0) + jb1 * jb1) * (q ^ 3)) * q ≤
      (L * 4 + (natCeilDiv badMca q + 4 * L * L)) * W := by
  have hCeil : badMca ≤ natCeilDiv badMca q * q := by
    unfold natCeilDiv
    have hDiv := Nat.div_add_mod (badMca + q - 1) q
    have hMod := Nat.mod_lt (badMca + q - 1) hQ
    rw [Nat.mul_comm] at hDiv
    omega
  have hMcaPart : (q * q) * badMca ≤ natCeilDiv badMca q * (q ^ 3) := by
    have h1 := Nat.mul_le_mul_left (q * q) hCeil
    have hEq : (q * q) * (natCeilDiv badMca q * q) = natCeilDiv badMca q * (q ^ 3) := by
      have hCube : q ^ 3 = (q * q) * q := by rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_one]
      rw [hCube, Nat.mul_left_comm (q * q)]
    rwa [hEq] at h1
  have hJbPart : 3 * (jb0 * jb0) + jb1 * jb1 ≤ 4 * L * L := by
    have h1 : jb0 * jb0 ≤ L * L := Nat.mul_le_mul hLo hLo
    have h2 : jb1 * jb1 ≤ L * L := Nat.mul_le_mul hHi hHi
    have h3 : 3 * (L * L) + L * L = 4 * L * L := by
      rw [Nat.mul_assoc 4 L L]
      generalize L * L = sq
      omega
    exact Nat.le_trans (Nat.add_le_add (Nat.mul_le_mul_left 3 h1) h2) (Nat.le_of_eq h3)
  have hTot : (q * q) * badMca + (3 * (jb0 * jb0) + jb1 * jb1) * (q ^ 3) ≤
      (natCeilDiv badMca q + 4 * L * L) * (q ^ 3) := by
    conv => rhs; rw [Nat.add_mul]
    exact Nat.add_le_add hMcaPart (Nat.mul_le_mul_right (q ^ 3) hJbPart)
  have hMul := Nat.mul_le_mul_right q (Nat.mul_le_mul_left (2 ^ 8) hTot)
  have hRhs : 2 ^ 8 * ((natCeilDiv badMca q + 4 * L * L) * (q ^ 3)) * q =
      (natCeilDiv badMca q + 4 * L * L) * (2 ^ 8 * (q ^ 3) * q) := by
    rw [Nat.mul_left_comm (2 ^ 8), Nat.mul_assoc, Nat.mul_assoc]
  rw [hRhs, hPowEq] at hMul
  exact Nat.le_trans hMul (Nat.mul_le_mul_right W (Nat.le_add_left _ (L * 4)))

private theorem slicedFour_le_mcaNum (n d A B m Dy L : Nat)
    (hLo : JohnsonBound.johnsonBound n A d ≤ L)
    (hHi : JohnsonBound.johnsonBound n A (d + 1) ≤ L) :
    2 ^ 8 * slicedFourChallengeCount n d A B m Dy flatHemQ * flatHemQ ≤
      (L * 4 + (natCeilDiv (Dy + slicedRest n (d + 1) (A + 1) B (m * (A + 1) - Dy) Dy flatHemQ)
          flatHemQ + 4 * L * L)) * 2 ^ 256 := by
  rw [slicedFourChallengeCount_def]
  exact slicedFour_le_mcaNum_core flatHemQ (2 ^ 256) _ _ _ L flatHemQ_pos
    (by decide +kernel) hLo hHi

/-- **Unconditional Multi-Stage `[CWYZ26]` Sliced-MCA `WhirScheduleCert` (`flatHemSlicedCert`)**:
    Constructively certifies the two-stage (`6`-round) WHIR schedule `flatHemSlicedSched` at
    Fiat–Shamir challenge width `w = 256` using **strictly proved `[CWYZ26]` sliced MCA counts**. -/
def flatHemSlicedCert : WhirScheduleCert flatHemSlicedEnv flatHemSlicedSched 256 where
  cert := {
    state := flatHemState
    bad := flatHemBad
    init := fun x hx => by
      cases hInit : flatHemState x [] with
      | false => rfl
      | true =>
        exfalso
        unfold flatHemState at hInit
        obtain ⟨Q, hQ⟩ := (hasValidWitness_true_iff 5 40 hemFoldDom64 antipodal_64_32.nodup_in
          (by decide) _ flatHemInitKernel x.claim).mp hInit
        rw [polyWitnessValid_def] at hQ
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hQ
        refine hx ⟨Q, Nat.le_trans hQ.1.1 (by decide : 6 ≤ 2 ^ 1 * 3 + 1), ?_, hQ.2⟩
        show 40 ≤ agreeCount flatHemSlicedEnv 64 x.table Q
        rw [agreeCount_flatHem_eq]
        exact hQ.1.2
    accept := fun x tr hv => by
      have hLen : tr.length = 6 := by
        rw [OracleIop.verify_eq] at hv
        exact of_decide_eq_true (Bool.and_eq_true_iff.mp hv).1
      rcases tr with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, rest⟩⟩⟩⟩⟩⟩
      · exact nomatch hLen
      · exact nomatch hLen
      · exact nomatch hLen
      · exact nomatch hLen
      · exact nomatch hLen
      · exact nomatch hLen
      · cases rest with
        | nil => unfold flatHemState; exact hv
        | cons _ _ => simp only [List.length_cons] at hLen; omega
    flip := fun x _ r pref m hLen hDoomed => by
      rcases r with ⟨_ | _ | _ | _ | _ | _ | n, hn⟩
      · rcases pref with _ | ⟨_, _⟩
        · exact flatHem_round0_flips x hDoomed m
        · exact nomatch hLen
      · rcases pref with _ | ⟨⟨m0, c0⟩, _ | ⟨_, _⟩⟩
        · exact nomatch hLen
        · exact flatHem_round1_flips x m0 m c0 hDoomed
        · exact nomatch (Nat.succ.inj hLen)
      · rcases pref with _ | ⟨⟨m0, c0⟩, _ | ⟨⟨m1, c1⟩, _ | ⟨_, _⟩⟩⟩
        · exact nomatch hLen
        · exact nomatch (Nat.succ.inj hLen)
        · exact flatHem_round2_flips x m0 m1 m c0 c1 hDoomed
        · exact nomatch (Nat.succ.inj (Nat.succ.inj hLen))
      · rcases pref with _ | ⟨⟨m0, c0⟩, _ | ⟨⟨m1, c1⟩, _ | ⟨⟨m2, c2⟩, _ | ⟨_, _⟩⟩⟩⟩
        · exact nomatch hLen
        · exact nomatch (Nat.succ.inj hLen)
        · exact nomatch (Nat.succ.inj (Nat.succ.inj hLen))
        · exact flatHem_round3_flips x m0 m1 m2 m c0 c1 c2 hDoomed
        · exact nomatch (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj hLen)))
      · rcases pref with _ | ⟨⟨m0, c0⟩, _ | ⟨⟨m1, c1⟩, _ | ⟨⟨m2, c2⟩, _ | ⟨⟨m3, c3⟩, _ | ⟨_, _⟩⟩⟩⟩⟩
        · exact nomatch hLen
        · exact nomatch (Nat.succ.inj hLen)
        · exact nomatch (Nat.succ.inj (Nat.succ.inj hLen))
        · exact nomatch (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj hLen)))
        · have hZero : ∀ ch : Fin (2 ^ 256),
              (if flatHemState x [(m0, c0), (m1, c1), (m2, c2), (m3, c3), (m, ch.1)] = true
               then 1 else 0) = 0 := by
            intro ch
            unfold flatHemState
            change (if flatHemState x [(m0, c0), (m1, c1), (m2, c2), (m3, c3)] = true
              then 1 else 0) = 0
            rw [hDoomed]; rfl
          dsimp only [whirOracleIop, List.cons_append, List.nil_append]
          rw [qsum_congr hZero, qsum_const, Nat.mul_zero]
          exact Nat.le_refl 0
        · exact nomatch (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj hLen))))
      · rcases pref with _ | ⟨⟨m0, c0⟩, _ | ⟨⟨m1, c1⟩, _ | ⟨⟨m2, c2⟩,
          _ | ⟨⟨m3, c3⟩, _ | ⟨⟨m4, c4⟩, _ | ⟨_, _⟩⟩⟩⟩⟩⟩
        · exact nomatch hLen
        · exact nomatch (Nat.succ.inj hLen)
        · exact nomatch (Nat.succ.inj (Nat.succ.inj hLen))
        · exact nomatch (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj hLen)))
        · exact nomatch (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj hLen))))
        · exact flatHem_round5_flips x m0 m1 m2 m3 m4 m c0 c1 c2 c3 c4 hDoomed
        · exact nomatch (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj hLen)))))
      · have hn' : n + 6 < 6 := hn; omega
  }
  covers := fun r => by
    rcases r with ⟨_ | _ | _ | _ | _ | _ | n, hn⟩
    · exact slicedFour_le_mcaNum 32 2 20 12 1 3 33
        (by rw [JohnsonBound.johnsonBound_eq]; decide)
        (by rw [JohnsonBound.johnsonBound_eq]; decide)
    · show 2 ^ 132 * (binom2 33 * 3 ^ 2) * (flatHemQ ^ 2) ≤
        binom2 33 * 3 ^ 2 * 2 ^ 256
      rw [binom2_33]
      decide +kernel
    · show 2 ^ 14 * (21 ^ 36 * flatHemQ + 33 * 38 * 32 ^ 36) * (32 ^ 36 * flatHemQ) ≤
        ((20 + 1) ^ 36 * flatHemQ + 33 * (36 + 2) * 32 ^ 36) * 2 ^ 256
      decide +kernel
    · exact slicedFour_le_mcaNum 16 1 10 7 2 4 29
        (by rw [JohnsonBound.johnsonBound_eq]; decide)
        (by rw [JohnsonBound.johnsonBound_eq]; decide)
    · show 0 * _ ≤ _
      rw [Nat.zero_mul]; exact Nat.zero_le _
    · show 2 ^ 10 * (11 ^ 46 * flatHemQ) * (16 ^ 46 * flatHemQ) ≤
        ((10 + 1) ^ 46 * flatHemQ + 29 * (46 + 2) * 16 ^ 46) * 2 ^ 256
      decide +kernel
    · have hn' : n + 6 < 6 := hn; omega

theorem flatHemSlicedCert_fold0_bad_pos :
    0 < flatHemSlicedCert.cert.bad ⟨0, by decide⟩ := by
  show 0 < 2 ^ 8 * slicedFourChallengeCount 32 2 20 12 1 3 flatHemQ
  rw [slicedFourChallengeCount_def, JohnsonBound.johnsonBound_eq, JohnsonBound.johnsonBound_eq]
  decide +kernel

private theorem flatHemFoldPoint_const_beta0 (D_in D_out : List QuarticGoldilocks)
    (θ α : QuarticGoldilocks) (pos : Nat) (v : QuarticGoldilocks) :
    flatHemFoldPoint D_in D_out θ α CommRingOps.zero pos v v = CommRingOps.mul α v := by
  unfold flatHemFoldPoint
  dsimp only
  let two : QuarticGoldilocks := CommRingOps.add CommRingOps.one CommRingOps.one
  have hTwoNz : two ≠ CommRingOps.zero := antipodal_64_32.two_ne_zero
  have hSub : CommRingOps.sub v v = CommRingOps.zero := LawfulCommRing.sub_self v
  have hAdd : CommRingOps.add v v = CommRingOps.mul two v := by
    dsimp only [two]; constructive_ring
  have hInvTwo : CommRingOps.mul (LawfulField.inv two) (CommRingOps.mul two v) = v := by
    rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm (LawfulField.inv two) two,
        LawfulField.mul_inv_cancel hTwoNz, LawfulCommRing.one_mul]
  rw [hSub, LawfulCommRing.mul_zero, hAdd, hInvTwo]
  constructive_ring

private theorem flatHem_stage_folded_const
    (i t n : Nat) (v : QuarticGoldilocks) (tbl : List QuarticGoldilocks)
    (hTbl : ∀ p < 2 * n, tbl.getD p CommRingOps.zero = v)
    (cFold cAns : Nat) (pub : WhirPub QuarticGoldilocks)
    (tailVals : List QuarticGoldilocks)
    (hnPos : 0 < n)
    (hBeta0 : (decodeQuad cFold).2.2.2 = CommRingOps.zero) :
    let qs := (List.range t).flatMap (fun j =>
      [flatHemChalPos cAns j n, flatHemChalPos cAns j n + n])
    let vals := qs.map (fun p => tbl.getD p CommRingOps.zero) ++ tailVals
    (List.range t).map (fun j =>
      flatHemRawFold i [(pub, cFold)] j (flatHemChalPos cAns j n)
        ((vals.drop (j * 2)).take 2)) =
    List.replicate t (CommRingOps.mul (decodeQuad cFold).2.2.1 v) := by
  dsimp only
  have hMapEq : ∀ (k : Nat) (f : Nat → QuarticGoldilocks) (val : QuarticGoldilocks),
      (∀ j < k, f j = val) → (List.range k).map f = List.replicate k val := by
    intro k f val hf
    induction k with
    | zero => rfl
    | succ m ihm =>
      rw [List.range_succ, List.map_append, List.map_cons, List.map_nil,
          ihm (fun j hj => hf j (Nat.lt_succ_of_lt hj)),
          hf m (Nat.lt_succ_self m), ← List.replicate_append_replicate,
          List.replicate_one]
  refine hMapEq t _ _ (fun j hj => ?_)
  have hSplitRange : List.range t =
      List.range j ++ (j :: (List.range (t - j - 1)).map (fun u => j + 1 + u)) := by
    have h1 : t = j + (1 + (t - j - 1)) := by omega
    have hGen : ∀ (a b : Nat), List.range (a + b) = List.range a ++ (List.range b).map (a + ·) := by
      intro a b
      induction b with
      | zero => rw [Nat.add_zero, List.range_zero, List.map_nil, List.append_nil]
      | succ b ihb =>
        rw [← Nat.add_assoc, List.range_succ, ihb, List.range_succ, List.map_append,
            List.map_cons, List.map_nil, List.append_assoc]
    conv => lhs; rw [h1, hGen j (1 + (t - j - 1)), hGen 1 (t - j - 1)]
    simp only [List.range_one, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
      Nat.add_zero, List.map_map]
    congr 1
    congr 1
    apply List.map_congr_left; intro u _; dsimp only [Function.comp]; omega
  let raw := fun p => tbl.getD p CommRingOps.zero
  let pre := (List.range j).flatMap (fun u =>
    [flatHemChalPos cAns u n, flatHemChalPos cAns u n + n])
  have hPreLen : (pre.map raw).length = j * 2 := by
    rw [List.length_map]
    dsimp only [pre]
    clear hj hSplitRange
    induction j with
    | zero => rfl
    | succ k ihk =>
      rw [List.range_succ, List.flatMap_append, List.length_append, ihk,
          List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_cons,
          List.length_cons, List.length_nil, Nat.succ_mul]
  have hDropApp : ∀ {α : Type} (xs ys : List α), (xs ++ ys).drop xs.length = ys := by
    intro α xs ys; induction xs with | nil => rfl | cons _ tl iht => exact iht
  have hBlock :
      ((((List.range t).flatMap (fun u =>
          [flatHemChalPos cAns u n, flatHemChalPos cAns u n + n])).map raw ++ tailVals).drop
        (j * 2)).take 2 =
      [raw (flatHemChalPos cAns j n), raw (flatHemChalPos cAns j n + n)] := by
    rw [hSplitRange, List.flatMap_append, List.flatMap_cons, List.map_append, List.map_append,
        List.append_assoc, List.append_assoc, ← hPreLen, hDropApp (pre.map raw)]
    rfl
  have hPosLt : flatHemChalPos cAns j n < n := Nat.mod_lt _ hnPos
  have hR0 : raw (flatHemChalPos cAns j n) = v := hTbl _ (by omega)
  have hR1 : raw (flatHemChalPos cAns j n + n) = v := hTbl _ (by omega)
  rw [hBlock, hR0, hR1]
  unfold flatHemRawFold
  dsimp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  rw [hBeta0]
  by_cases hi : i = 0
  · rw [ite_true_eq _ _ hi, flatHemFoldPoint_const_beta0]
  · rw [ite_false_eq _ _ hi, flatHemFoldPoint_const_beta0]

private theorem evalCoeffs_le_one {p : List QuarticGoldilocks} (hp : p.length ≤ 1)
    (x : QuarticGoldilocks) :
    RoundPoly.evalCoeffs p x = p.getD 0 CommRingOps.zero := by
  rcases p with _ | ⟨c, _ | _⟩
  · rfl
  · simp only [RoundPoly.evalCoeffs_cons, RoundPoly.evalCoeffs_nil,
      LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    rfl
  · simp only [List.length_cons] at hp; omega

private theorem flatHem_verify_const_eval
    (v0 v1 cl0 : QuarticGoldilocks) (tbl1 : List QuarticGoldilocks)
    (htbl1 : ∀ p < 32, tbl1.getD p CommRingOps.zero = v1)
    (p0 p3 p4 : List QuarticGoldilocks)
    (y0 y1 z0 z1 : QuarticGoldilocks)
    (c0 c1 c2 c3 c4 c5 : Nat)
    (hp0 : p0.length ≤ 5) (hp3 : p3.length ≤ 5) (hp4 : p4.length ≤ 1)
    (hBeta0 : (decodeQuad c0).2.2.2 = CommRingOps.zero)
    (hBeta1 : (decodeQuad c3).2.2.2 = CommRingOps.zero)
    (hPhi1 : p4 = [] ∨ (decodeQuad c3).1 = CommRingOps.zero) :
    (whirOracleIop flatHemSlicedEnv flatHemSlicedSched 256).verify
      ⟨List.replicate 64 v0, cl0⟩
      [(⟨[], p0, []⟩, c0),
       (⟨tbl1, [], []⟩, c1),
       (⟨[], [], [y0, y1]⟩, c2),
       (⟨[], p3, []⟩, c3),
       (⟨[], p4, []⟩, c4),
       (⟨[], [], [z0, z1]⟩, c5)] =
    (let q0 := decodeQuad c0
     let q1 := decodeQuad c3
     let cl0' := flatHemBridgeClaim cl0
       (p0.getD 0 CommRingOps.zero) (p0.getD 1 CommRingOps.zero)
       (p0.getD 2 CommRingOps.zero) (p0.getD 3 CommRingOps.zero)
       (p0.getD 4 CommRingOps.zero) q0.1 q0.2.1 q0.2.2.1 q0.2.2.2
     let γ₀ := flatHemChalField c2 36
     let f0 := CommRingOps.mul q0.2.2.1 v0
     let cl1 := combineClaim cl0' γ₀ ([y0, y1] ++ List.replicate 36 f0)
     let cl2 := flatHemBridgeClaim cl1
       (p3.getD 0 CommRingOps.zero) (p3.getD 1 CommRingOps.zero)
       (p3.getD 2 CommRingOps.zero) (p3.getD 3 CommRingOps.zero)
       (p3.getD 4 CommRingOps.zero) q1.1 q1.2.1 q1.2.2.1 q1.2.2.2
     let f1 := CommRingOps.mul q1.2.2.1 v1
     let cFin := p4.getD 0 CommRingOps.zero
     let expFinal :=
       if p4.isEmpty then CommRingOps.zero
       else CommRingOps.add cFin
         (CommRingOps.mul γ₀ (RoundPoly.evalCoeffs (List.replicate 38 cFin) γ₀))
     decide (cFin = z0) && decide (cFin = z1) &&
     decide (cFin = f1) && decide (cl2 = expFinal)) := by
  rw [OracleIop.verify_eq]
  have hLen6 : decide (([
      (⟨[], p0, []⟩, c0),
      (⟨tbl1, [], []⟩, c1),
      (⟨[], [], [y0, y1]⟩, c2),
      (⟨[], p3, []⟩, c3),
      (⟨[], p4, []⟩, c4),
      (⟨[], [], [z0, z1]⟩, c5)] : List (WhirMsg QuarticGoldilocks × Nat)).length =
      flatHemSlicedSched.numRounds) = true := decide_eq_true rfl
  rw [hLen6, Bool.true_and]
  dsimp only [whirOracleIop, List.map]
  have hValsEq :
      (whirQueries flatHemSlicedEnv flatHemSlicedSched
        [(⟨p0, []⟩, c0), (⟨[], []⟩, c1), (⟨[], [y0, y1]⟩, c2),
         (⟨p3, []⟩, c3), (⟨p4, []⟩, c4), (⟨[], [z0, z1]⟩, c5)]).map
        (fun q => whirTable flatHemSlicedSched ⟨List.replicate 64 v0, cl0⟩
          [⟨[], p0, []⟩, ⟨tbl1, [], []⟩, ⟨[], [], [y0, y1]⟩,
           ⟨[], p3, []⟩, ⟨[], p4, []⟩, ⟨[], [], [z0, z1]⟩] q.1 q.2) =
      ((List.range 36).flatMap (fun j =>
        [flatHemChalPos c2 j 32, flatHemChalPos c2 j 32 + 32])).map
          (fun p => (List.replicate 64 v0).getD p CommRingOps.zero) ++
      ((List.range 46).flatMap (fun j =>
        [flatHemChalPos c5 j 16, flatHemChalPos c5 j 16 + 16])).map
          (fun p => tbl1.getD p CommRingOps.zero) := by
    rw [flatHemQueries_eq (F := QuarticGoldilocks), List.map_append]
    dsimp only
    refine list_append_congr ?_ ?_
    · generalize List.range 36 = l0
      induction l0 with
      | nil => rfl
      | cons u us ih =>
        rw [List.flatMap_cons, List.map_append, ih, List.flatMap_cons, List.map_append]; rfl
    · generalize List.range 46 = l1
      induction l1 with
      | nil => rfl
      | cons u us ih =>
        rw [List.flatMap_cons, List.map_append, ih, List.flatMap_cons, List.map_append]; rfl
  rw [hValsEq]
  unfold whirVerdict flatHemSlicedSched
  dsimp only
  rw [splitStages_flatHem]
  unfold whirCheckStages whirCheckStagesAux stageFoldRun stageFoldRunAux flatHemSlicedEnv
  dsimp only
  rcases flatHemStage_ver_fields with ⟨hf0, _, ho0, hq0, hd0, hf1, _, ho1, hq1, hd1⟩
  rw [hf0, ho0, hq0, hd0]
  have hStep0 : flatHemStepClaim 0 cl0 p0 c0 =
      some (flatHemBridgeClaim cl0
        (p0.getD 0 CommRingOps.zero) (p0.getD 1 CommRingOps.zero)
        (p0.getD 2 CommRingOps.zero) (p0.getD 3 CommRingOps.zero)
        (p0.getD 4 CommRingOps.zero)
        (decodeQuad c0).1 (decodeQuad c0).2.1 (decodeQuad c0).2.2.1 (decodeQuad c0).2.2.2) := by
    unfold flatHemStepClaim; rw [ite_true_eq _ _ hp0]
  rw [hStep0]
  unfold stageFoldRunAux
  dsimp only [Option.map]
  have hTbl0 : ∀ p < 2 * 32, (List.replicate 64 v0).getD p CommRingOps.zero = v0 := by
    intro p hp
    have hp64 : p < 64 := hp
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, ite_true_eq _ _ hp64, Option.getD_some]
  have hLen0 : (((List.range 36).flatMap (fun j =>
      [flatHemChalPos c2 j 32, flatHemChalPos c2 j 32 + 32])).map
        (fun p => (List.replicate 64 v0).getD p CommRingOps.zero)).length = 36 * 2 := by
    rw [List.length_map]
    have hAux : ∀ k : Nat,
        ((List.range k).flatMap (fun j =>
          [flatHemChalPos c2 j 32, flatHemChalPos c2 j 32 + 32])).length = k * 2 := by
      intro k; induction k with
      | zero => rfl
      | succ k ih =>
        rw [List.range_succ, List.flatMap_append, List.length_append, ih,
            List.flatMap_cons, List.flatMap_nil, List.append_nil, Nat.succ_mul]; rfl
    exact hAux 36
  have hLen1 : (((List.range 46).flatMap (fun j =>
      [flatHemChalPos c5 j 16, flatHemChalPos c5 j 16 + 16])).map
        (fun p => tbl1.getD p CommRingOps.zero)).length = 46 * 2 := by
    rw [List.length_map]
    have hAux : ∀ k : Nat,
        ((List.range k).flatMap (fun j =>
          [flatHemChalPos c5 j 16, flatHemChalPos c5 j 16 + 16])).length = k * 2 := by
      intro k; induction k with
      | zero => rfl
      | succ k ih =>
        rw [List.range_succ, List.flatMap_append, List.length_append, ih,
            List.flatMap_cons, List.flatMap_nil, List.append_nil, Nat.succ_mul]; rfl
    exact hAux 46
  have hDropApp : ∀ {α : Type} (xs ys : List α), (xs ++ ys).drop xs.length = ys := by
    intro α xs ys; induction xs with | nil => rfl | cons _ tl iht => exact iht
  have hFolded0 := flatHem_stage_folded_const 0 36 32 v0 (List.replicate 64 v0) hTbl0
    c0 c2 ⟨p0, []⟩
    (((List.range 46).flatMap (fun j =>
      [flatHemChalPos c5 j 16, flatHemChalPos c5 j 16 + 16])).map
        (fun p => tbl1.getD p CommRingOps.zero))
    (by decide) hBeta0
  dsimp only at hFolded0
  rw [show 2 ^ 1 = 2 from rfl, hFolded0,
      List.length_append, hLen0, hLen1,
      show decide (([y0, y1] : List QuarticGoldilocks).length = 2) = true from rfl,
      show decide (36 * 2 ≤ 36 * 2 + 46 * 2) = true from rfl,
      Bool.true_and, Bool.true_and]
  dsimp only [List.isEmpty]
  rw [ite_false_eq _ _ Bool.false_ne_true, ← hLen0, hDropApp,
      show (0 : Nat) + 1 = 1 from rfl]
  have hFolded1 := flatHem_stage_folded_const 1 46 16 v1 tbl1 htbl1 c3 c5 ⟨p3, []⟩ []
    (by decide) hBeta1
  dsimp only at hFolded1
  rw [List.append_nil] at hFolded1
  generalize ((List.range 46).flatMap (fun j =>
      [flatHemChalPos c5 j 16, flatHemChalPos c5 j 16 + 16])).map
        (fun p => tbl1.getD p CommRingOps.zero) = vals1 at hLen1 hFolded1 ⊢
  generalize combineClaim
    (flatHemBridgeClaim cl0
      (p0.getD 0 CommRingOps.zero) (p0.getD 1 CommRingOps.zero)
      (p0.getD 2 CommRingOps.zero) (p0.getD 3 CommRingOps.zero)
      (p0.getD 4 CommRingOps.zero)
      (decodeQuad c0).1 (decodeQuad c0).2.1 (decodeQuad c0).2.2.1 (decodeQuad c0).2.2.2)
    (flatHemChalField c2 36)
    ([y0, y1] ++ List.replicate 36 (CommRingOps.mul (decodeQuad c0).2.2.1 v0)) = cl1
  let cFin := p4.getD 0 CommRingOps.zero
  have hFinalVal :
      flatHemFinalClaimViews
        [⟨[(⟨p0, []⟩, c0)], (⟨[], []⟩, c1), (⟨[], [y0, y1]⟩, c2)⟩,
         ⟨[(⟨p3, []⟩, c3)], (⟨p4, []⟩, c4), (⟨[], [z0, z1]⟩, c5)⟩]
        [CommRingOps.zero] =
      (if p4.isEmpty then CommRingOps.zero
       else CommRingOps.add (p4.getD 0 CommRingOps.zero)
         (CommRingOps.mul (flatHemChalField c2 36)
           (RoundPoly.evalCoeffs (List.replicate 38 (p4.getD 0 CommRingOps.zero))
             (flatHemChalField c2 36)))) := by
    unfold flatHemFinalClaimViews
    dsimp only
    rcases hPhi1 with rfl | hPhi1Zero
    · dsimp only [List.isEmpty]; exact ringDot_nil_left _
    · rcases p4 with _ | ⟨c, _ | _⟩
      · dsimp only [List.isEmpty]; exact ringDot_nil_left _
      · dsimp only [List.isEmpty]
        rw [ite_false_eq _ _ Bool.false_ne_true]
        have hGetC : ([c] : List QuarticGoldilocks).getD 0 CommRingOps.zero = c := rfl
        rw [hGetC, hPhi1Zero]
        let K0' := flatHemKernelFold (decodeQuad c0).1 flatHemInitKernel
        have hK0Eq : K0' = [CommRingOps.one, CommRingOps.zero, CommRingOps.zero,
            CommRingOps.zero, CommRingOps.zero, CommRingOps.zero] := by
          dsimp only [K0', flatHemInitKernel, flatHemKernelFold]
          simp only [LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
        have hK0Len : K0'.length = 6 := by rw [hK0Eq]; rfl
        let pts := [(decodeOod c1).1, (decodeOod c1).2] ++
          (List.range 36).map (fun j =>
            hemFoldDom32.getD (flatHemChalPos c2 j 32) CommRingOps.zero)
        let K1 := combineKernel6 K0' (flatHemChalField c2 36) pts
        have hcLe4 : ([c] : List QuarticGoldilocks).length ≤ 4 := show 1 ≤ 4 by decide
        have hSpec := combineKernel6_foldl_spec (flatHemChalField c2 36) [c] hcLe4
          pts K0' (flatHemChalField c2 36) hK0Len
        have hK1Len : K1.length = 6 := hSpec.1
        have hFold0Dot : ringDot [c] (flatHemKernelFold CommRingOps.zero K1) = ringDot [c] K1 := by
          rcases hK1 : K1 with _ | ⟨k0, _ | ⟨k1, krest⟩⟩
          · rw [hK1] at hK1Len; exact nomatch hK1Len
          · rw [hK1] at hK1Len; exact nomatch (Nat.succ.inj hK1Len)
          · dsimp only [flatHemKernelFold]
            simp only [ringDot_cons_cons, ringDot_nil_left,
              LawfulCommRing.zero_mul, LawfulCommRing.add_zero]
        have hDotK0 : ringDot [c] K0' = c := by
          rw [hK0Eq, ringDot_cons_cons, ringDot_nil_left, LawfulCommRing.mul_one,
              LawfulCommRing.add_zero]
        have hPtsMap : pts.map (RoundPoly.evalCoeffs [c]) = List.replicate 38 c := by
          have hPtsLen : pts.length = 38 := by
            dsimp only [pts]; rw [List.length_append, List.length_map, List.length_range]; rfl
          have hcLe1 : ([c] : List QuarticGoldilocks).length ≤ 1 := Nat.le_refl 1
          have hConstMap : ∀ (l : List QuarticGoldilocks),
              l.map (RoundPoly.evalCoeffs [c]) = List.replicate l.length c := by
            intro l; induction l with
            | nil => rfl
            | cons a as iha =>
              rw [List.map_cons, List.length_cons, List.replicate_succ, iha,
                  evalCoeffs_le_one hcLe1]
              rfl
          rw [hConstMap pts, hPtsLen]
        rw [hFold0Dot]
        have hK1Unf : K1 = (pts.foldl (fun (acc : List QuarticGoldilocks × QuarticGoldilocks) pt =>
            (vecAdd6 acc.1 (vecScale6 acc.2 (evalVec6 pt)),
             CommRingOps.mul acc.2 (flatHemChalField c2 36)))
            (K0', flatHemChalField c2 36)).1 := rfl
        rw [hK1Unf, hSpec.2, hDotK0, hPtsMap]
      · simp only [List.length_cons] at hp4; omega
  generalize RoundPoly.evalCoeffs (List.replicate 38 (p4.getD 0 CommRingOps.zero))
    (flatHemChalField c2 36) = ev38 at hFinalVal ⊢
  unfold whirCheckStagesAux stageFoldRun stageFoldRunAux
  dsimp only
  rw [hf1, ho1, hq1, hd1]
  have hStep1 : flatHemStepClaim 1 cl1 p3 c3 =
      some (flatHemBridgeClaim cl1
        (p3.getD 0 CommRingOps.zero) (p3.getD 1 CommRingOps.zero)
        (p3.getD 2 CommRingOps.zero) (p3.getD 3 CommRingOps.zero)
        (p3.getD 4 CommRingOps.zero)
        (decodeQuad c3).1 (decodeQuad c3).2.1 (decodeQuad c3).2.2.1 (decodeQuad c3).2.2.2) := by
    unfold flatHemStepClaim; rw [ite_true_eq _ _ hp3]
  rw [hStep1]
  unfold stageFoldRunAux
  dsimp only [Option.map, List.isEmpty]
  rw [show 2 ^ 1 = 2 from rfl, hFolded1, hLen1,
      show decide (([z0, z1] : List QuarticGoldilocks).length = 2) = true from rfl,
      show decide (46 * 2 ≤ 46 * 2) = true from rfl,
      Bool.true_and, Bool.true_and, ite_true_eq _ _ rfl,
      decide_eq_true (Nat.le_trans hp4 (by decide : 1 ≤ 3)), Bool.true_and,
      decide_eq_true (rfl : 46 * 2 = 46 * 2), Bool.and_true]
  have hOodZip :
      (((List.range 2).map (flatHemChalField c4)).zip [z0, z1]).all
        (fun zy => decide (RoundPoly.evalCoeffs p4 zy.1 = zy.2)) =
      (decide (cFin = z0) && decide (cFin = z1)) := by
    have hR2' : List.range 2 = [0, 1] := rfl
    rw [hR2', List.map_cons, List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_cons_cons,
        List.zip_nil_left, List.all_cons, List.all_cons, List.all_nil, Bool.and_true,
        evalCoeffs_le_one hp4, evalCoeffs_le_one hp4]
  let f1 := CommRingOps.mul (decodeQuad c3).2.2.1 v1
  have hShiftZip :
      ((List.range 46).zip (List.replicate 46 f1)).all (fun jv =>
        decide (RoundPoly.evalCoeffs p4
          (if 1 + 1 = 0 then halfDomPt hemFoldDom64 32 (flatHemChalPos c5 jv.1 16)
           else if 1 + 1 = 1 then halfDomPt hemFoldDom32 16 (flatHemChalPos c5 jv.1 16)
           else hemFoldDom16.getD (flatHemChalPos c5 jv.1 16) CommRingOps.zero) = jv.2)) =
      decide (cFin = f1) := by
    have hEvalF : (fun jv : Nat × QuarticGoldilocks =>
        decide (RoundPoly.evalCoeffs p4
          (if 1 + 1 = 0 then halfDomPt hemFoldDom64 32 (flatHemChalPos c5 jv.1 16)
           else if 1 + 1 = 1 then halfDomPt hemFoldDom32 16 (flatHemChalPos c5 jv.1 16)
           else hemFoldDom16.getD (flatHemChalPos c5 jv.1 16) CommRingOps.zero) = jv.2)) =
      (fun jv : Nat × QuarticGoldilocks => decide (cFin = jv.2)) := by
      funext jv; rw [evalCoeffs_le_one hp4]
    rw [hEvalF]
    have hTail : ∀ (xs : List Nat), decide (cFin = f1) = true →
        (xs.zip (List.replicate xs.length f1)).all (fun jv => decide (cFin = jv.2)) = true := by
      intro xs hD
      induction xs with
      | nil => rfl
      | cons a as iha =>
        simp only [List.length_cons, List.replicate_succ, List.zip_cons_cons, List.all_cons,
          hD, iha, Bool.and_self]
    have hR46 : List.range 46 = 0 :: (List.range 45).map (· + 1) := range_succ_eq_zero_cons_map 45
    have hL45 : ((List.range 45).map (· + 1)).length = 45 := by
      rw [List.length_map, List.length_range]
    rw [hR46, show List.replicate 46 f1 = f1 :: List.replicate 45 f1 from rfl, ← hL45,
        List.zip_cons_cons, List.all_cons]
    cases hD : decide (cFin = f1)
    · exact Bool.false_and _
    · rw [Bool.true_and]; exact hTail _ hD
  rw [hOodZip, hShiftZip, hFinalVal]
  cases p4 <;> rfl

/-- Honest two-stage proof on `flatHemSlicedSched`: the constant-`1` polynomial on `hemFoldDom64`
    with claim `1` is accepted across non-zero fold and batching challenges (`α₀ = 1, γ₀ = 1, α₁ = 1`). -/
theorem flatHemSliced_honest_accepts :
    (whirOracleIop flatHemSlicedEnv flatHemSlicedSched 256).verify
      ⟨List.replicate 64 (hemFoldQg 1), hemFoldQg 1⟩
      [(⟨[], [hemFoldQg 1, CommRingOps.zero, CommRingOps.zero, CommRingOps.zero, CommRingOps.zero], []⟩,
        flatHemQ),
       (⟨List.replicate 32 (hemFoldQg 1), [], []⟩, 0),
       (⟨[], [], [hemFoldQg 1, hemFoldQg 1]⟩, 1),
       (⟨[], [hemFoldQg 39, CommRingOps.zero, CommRingOps.zero, CommRingOps.zero, CommRingOps.zero], []⟩,
        flatHemQ),
       (⟨[], [hemFoldQg 1], []⟩, 0),
       (⟨[], [], [hemFoldQg 1, hemFoldQg 1]⟩, 0)] = true := by
  have hTbl1 : ∀ p < 32,
      (List.replicate 32 (hemFoldQg 1)).getD p CommRingOps.zero = hemFoldQg 1 := by
    intro p hp
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, ite_true_eq _ _ hp, Option.getD_some]
  rw [flatHem_verify_const_eval (hemFoldQg 1) (hemFoldQg 1) (hemFoldQg 1)
    (List.replicate 32 (hemFoldQg 1)) hTbl1
    [hemFoldQg 1, CommRingOps.zero, CommRingOps.zero, CommRingOps.zero, CommRingOps.zero]
    [hemFoldQg 39, CommRingOps.zero, CommRingOps.zero, CommRingOps.zero, CommRingOps.zero]
    [hemFoldQg 1]
    (hemFoldQg 1) (hemFoldQg 1) (hemFoldQg 1) (hemFoldQg 1)
    flatHemQ 0 1 flatHemQ 0 0
    (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (.inr (by decide +kernel))]
  decide +kernel

/-- False statement outside `whirInLang`: the all-ones table on `hemFoldDom64` with claim `2`
    cannot be explained by any polynomial of degree `≤ 6` agreeing on `≥ 40` points. -/
theorem flatHemSliced_false_not_inLang :
    ¬ whirInLang flatHemSlicedEnv flatHemSlicedSched
      ⟨List.replicate 64 (hemFoldQg 1), hemFoldQg 2⟩ := by
  unfold whirInLang flatHemSlicedSched flatHemStage0
  rintro ⟨P, hLen, hAg, hCl⟩
  change 40 ≤ agreeCount flatHemSlicedEnv 64 (List.replicate 64 (hemFoldQg 1)) P at hAg
  rw [agreeCount_flatHem_eq,
      hemCosetAgreeCount_eq_filter_lookup hemFoldDom64 _ P antipodal_64_32.nodup_in] at hAg
  have hConst1 : ∀ z ∈ hemFoldDom64,
      lookupDomOracle hemFoldDom64
        (interleaveOracle 32
          (fun p => (List.replicate 64 (hemFoldQg 1)).getD p CommRingOps.zero)) z =
      hemFoldQg 1 := by
    intro z hz
    let idx : Fin hemFoldDom64.length := ⟨hemFoldDom64.idxOf z, List.idxOf_lt_length_of_mem hz⟩
    have hGet : hemFoldDom64.get idx = z := List.getElem_idxOf _
    rw [← hGet, lookupDomOracle_get hemFoldDom64 _ antipodal_64_32.nodup_in idx]
    have hIdxLt : idx.1 < 64 := hemFoldDom64_len ▸ idx.2
    unfold interleaveOracle
    by_cases hEven : idx.1 % 2 = 0
    · rw [ite_true_eq _ _ hEven]
      dsimp only
      have hd : idx.1 / 2 < 64 := by omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, ite_true_eq _ _ hd, Option.getD_some]
    · rw [ite_false_eq _ _ hEven]
      dsimp only
      have hd : idx.1 / 2 + 32 < 64 := by omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, ite_true_eq _ _ hd, Option.getD_some]
  have hFiltEq :
      hemFoldDom64.filter (fun z =>
        decide (RoundPoly.evalCoeffs P z =
          lookupDomOracle hemFoldDom64
            (interleaveOracle 32
              (fun p => (List.replicate 64 (hemFoldQg 1)).getD p CommRingOps.zero)) z)) =
      hemFoldDom64.filter (fun z =>
        decide (RoundPoly.evalCoeffs P z = RoundPoly.evalCoeffs [hemFoldQg 1] z)) := by
    refine List.filter_congr (fun z hz => ?_)
    rw [hConst1 z hz]
    have hOneEval : RoundPoly.evalCoeffs [hemFoldQg 1] z = hemFoldQg 1 := by
      simp only [RoundPoly.evalCoeffs_cons, RoundPoly.evalCoeffs_nil, LawfulCommRing.mul_zero,
        LawfulCommRing.add_zero]
    rw [hOneEval]
  rw [hFiltEq] at hAg
  have hTrim := trimPoly_eq_of_agree_on_nodup hLen (by decide : [hemFoldQg 1].length ≤ 7)
    (List.Pairwise.filter _ antipodal_64_32.nodup_in)
    (Nat.le_trans (by decide : 7 ≤ 40) hAg)
    (fun z hz => of_decide_eq_true (List.mem_filter.mp hz).2)
  have hDot1 : ringDot P flatHemInitKernel = hemFoldQg 1 := by
    rw [← ringDot_trimPoly_eq, hTrim, ringDot_trimPoly_eq]
    decide +kernel
  have hCl' : ringDot P flatHemInitKernel = hemFoldQg 2 := hCl
  rw [hDot1] at hCl'
  exact (by decide +kernel : hemFoldQg 1 ≠ hemFoldQg 2) hCl'

/-- That false statement (`claim = 2` on the all-ones table) is genuinely accepted on the
    zero-challenge quadruple `(φ₀ = 0, θ₀ = 0, α₀ = 0, β₀ = 0)` and rejected at `φ₀ = 1, φ₁ = 1`,
    confirming that soundness error on `flatHemSlicedSched` is strictly positive while `< 2^-20`. -/
theorem flatHemSliced_false_accepted_once :
    (whirOracleIop flatHemSlicedEnv flatHemSlicedSched 256).verify
      ⟨List.replicate 64 (hemFoldQg 1), hemFoldQg 2⟩
      [(⟨[], [], []⟩, 0),
       (⟨[], [], []⟩, 0),
       (⟨[], [], [CommRingOps.zero, CommRingOps.zero]⟩, 0),
       (⟨[], [], []⟩, 0),
       (⟨[], [], []⟩, 0),
       (⟨[], [], [CommRingOps.zero, CommRingOps.zero]⟩, 0)] = true ∧
    (whirOracleIop flatHemSlicedEnv flatHemSlicedSched 256).verify
      ⟨List.replicate 64 (hemFoldQg 1), hemFoldQg 2⟩
      [(⟨[], [], []⟩, flatHemQ * (flatHemQ * flatHemQ)),
       (⟨[], [], []⟩, 0),
       (⟨[], [], [CommRingOps.zero, CommRingOps.zero]⟩, 0),
       (⟨[], [], []⟩, flatHemQ * (flatHemQ * flatHemQ)),
       (⟨[], [], []⟩, 0),
       (⟨[], [], [CommRingOps.zero, CommRingOps.zero]⟩, 0)] = false := by
  have hNilTbl : ∀ p < 32, ([] : List QuarticGoldilocks).getD p CommRingOps.zero = CommRingOps.zero :=
    fun _ _ => rfl
  refine ⟨?_, ?_⟩
  · rw [flatHem_verify_const_eval (hemFoldQg 1) CommRingOps.zero (hemFoldQg 2) [] hNilTbl
      [] [] [] CommRingOps.zero CommRingOps.zero CommRingOps.zero CommRingOps.zero
      0 0 0 0 0 0 (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (.inl rfl)]
    decide +kernel
  · rw [flatHem_verify_const_eval (hemFoldQg 1) CommRingOps.zero (hemFoldQg 2) [] hNilTbl
      [] [] [] CommRingOps.zero CommRingOps.zero CommRingOps.zero CommRingOps.zero
      (flatHemQ * (flatHemQ * flatHemQ)) 0 0 (flatHemQ * (flatHemQ * flatHemQ)) 0 0
      (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) (.inl rfl)]
    decide +kernel

/-! ## §6. Negative controls evaluated on this module's definitions

These statements evaluate `johnsonOk`, `scheduleQromError` and the verifier on concrete
schedules, so they are proved here, where the definitions can be unfolded.
`Qsag.Tests.ClosedReductionTeeth` pairs them with the theorems they guard. -/

/-- A stage with its Johnson list size replaced by `1`. -/
def dropListSize (s : WhirStage) : WhirStage := { s with listSize := 1 }

/-- The deployed schedule with the Johnson list-size multipliers omitted. -/
def deployedNoList : WhirVerifierSchedule :=
  ⟨24, goldilocksExt4Card, goldilocksExt4Card_pos, deployedStages.map dropListSize⟩

/-- `#tooth` The list size is load-bearing in every deployed stage: no stage's fold-round bound
    survives replacing its list size by `1`. (A statement about each stage's fold bound; the
    comparison of the two whole-schedule sums is not proved here.) -/
theorem tooth_omitting_list_size_lowers_every_fold_bound :
    ¬ (∃ s ∈ deployedSched.stages,
        RatBound.le (s.foldBound goldilocksExt4Card goldilocksExt4Card_pos)
          ((dropListSize s).foldBound goldilocksExt4Card goldilocksExt4Card_pos)) := by
  have hSt : deployedSched.stages = deployedStages := rfl
  rw [hSt, deployedStages_full_eq]
  unfold RatBound.le WhirStage.foldBound dropListSize
  decide +kernel

/-- `#tooth` The schedule without list sizes fails the Johnson check. -/
theorem tooth_omitting_list_size_fails_johnson_check :
    ¬ (deployedNoList.johnsonOk = true) := by
  simp only [WhirVerifierSchedule.johnsonOk, deployedNoList, deployedStages_full_eq,
    List.map_cons, List.map_nil, dropListSize]
  decide +kernel

/-- First deployed stage with agreement `n / 2`, any slack `e / E` and any list size `L`. -/
def beyondRadiusStage (e E L : Nat) : WhirStage :=
  { foldK := 6, logDomain := 20, logInvRate := 2, oodCount := 2, queryCount := 216,
    degBound := 262146, agree := 524288, etaNum := e, etaDen := E, listSize := L,
    sumcheckDeg := 3, mcaNum := 0 }

/-- `#tooth` Beyond the Johnson radius no slack and no list size pass the check. -/
theorem tooth_beyond_johnson_radius_invalidates_certificate (e E L : Nat) :
    ¬ ((beyondRadiusStage e E L).johnsonOk = true) := by
  have h : (beyondRadiusStage e E L).johnsonOk = false :=
    WhirStage.johnsonOk_false_of_beyond_radius _ (by
      show (524288 : Nat) * 524288 ≤ 2 ^ 20 * 262146
      decide +kernel)
  rw [h]
  exact Bool.false_ne_true

section EmptySchedule
variable {F : Type} [CommRingOps F] [DecidableEq F]

/-- The certificate type is also inhabited at the stage-free schedule, whose verifier rejects
    everything. This is the degenerate inhabitant; `sampledQueryCert` is the one with a stage. -/
def emptyScheduleCert (env : WhirEnv F) (nv q : Nat) (hq : 0 < q) (w : Nat) :
    WhirScheduleCert env ⟨nv, q, hq, []⟩ w where
  cert :=
    { state := fun _ _ => false
      bad := fun r => Fin.elim0 r
      init := fun _ _ => rfl
      accept := fun x tr h => by
        rw [OracleIop.verify_eq] at h
        obtain ⟨hLenD, hVerd⟩ := Bool.and_eq_true_iff.mp h
        have hLen : tr = [] := List.eq_nil_of_length_eq_zero (of_decide_eq_true hLenD)
        subst hLen
        exact absurd hVerd Bool.false_ne_true
      flip := fun _ _ r _ _ _ _ => Fin.elim0 r }
  covers := fun r => Fin.elim0 r

/-- `#tooth` A stage-free schedule accepts no transcript: its certificate is a negative control,
    not evidence about a verifier that can accept. -/
theorem tooth_empty_schedule_rejects (env : WhirEnv F) (nv q w : Nat) (hq : 0 < q)
    (x : WhirStmt F) (tr : List (WhirMsg F × Nat)) :
    (whirOracleIop env ⟨nv, q, hq, []⟩ w).verify x tr = false := by
  cases h : (whirOracleIop env ⟨nv, q, hq, []⟩ w).verify x tr
  · rfl
  · have bad := (emptyScheduleCert env nv q hq w).cert.accept x tr h
    exact False.elim (Bool.false_ne_true bad)

end EmptySchedule

theorem WhirStage.foldBound_eq (q : Nat) (hq : 0 < q) (s : WhirStage) :
    s.foldBound q hq = ⟨s.listSize * s.sumcheckDeg + s.mcaNum, q, hq⟩ := by rfl

theorem WhirStage.oodBound_eq (q : Nat) (hq : 0 < q) (s : WhirStage) :
    s.oodBound q hq =
      ⟨binom2 s.listSize * s.degBound ^ s.oodCount, q ^ s.oodCount, Nat.pow_pos hq⟩ := by rfl

theorem WhirStage.shiftBound_eq (q : Nat) (hq : 0 < q) (s : WhirStage) :
    s.shiftBound q hq =
      RatBound.add
        ⟨(s.agree + s.foldK) ^ s.queryCount, s.domainSize ^ s.queryCount,
          Nat.pow_pos (Nat.two_pow_pos s.logDomain)⟩
        ⟨s.listSize * (s.queryCount + s.oodCount), q, hq⟩ := by rfl

theorem WhirStage.roundBounds_eq (q : Nat) (hq : 0 < q) (s : WhirStage) :
    s.roundBounds q hq =
      List.replicate s.foldK (s.foldBound q hq) ++ [s.oodBound q hq, s.shiftBound q hq] := by rfl

theorem stagesRoundBounds_nil (q : Nat) (hq : 0 < q) :
    stagesRoundBounds q hq [] = [] := by rfl

theorem stagesRoundBounds_cons (q : Nat) (hq : 0 < q) (s : WhirStage) (rest : List WhirStage) :
    stagesRoundBounds q hq (s :: rest) =
      s.roundBounds q hq ++ stagesRoundBounds q hq rest := by rfl

theorem WhirVerifierSchedule.roundBounds_eq (sched : WhirVerifierSchedule) :
    sched.roundBounds = stagesRoundBounds sched.fieldCard sched.fieldPos sched.stages := by rfl

theorem scheduleQromError_eq (sched : WhirVerifierSchedule) (Q : Nat) :
    scheduleQromError sched Q = RatBound.sumList (sched.roundBounds.map (dfmRoundScale Q)) := by rfl

/-- Exact evaluation of `(whirOracleIop env ⟨nv, q, hq, [st]⟩ w).verify x [(m0, c0), (m1, c1)]`
    for a single-stage schedule with `st.foldK = 0` and default hooks (`none`). -/
theorem whirOracleIop_verify_oneStage_noFold_eq {F : Type} [CommRingOps F] [DecidableEq F]
    (env : WhirEnv F) (nv q : Nat) (hq : 0 < q) (st : WhirStage) (w : Nat)
    (hfk : st.foldK = 0)
    (hStep : env.foldClaimStep = none)
    (hRaw : env.foldBlockRaw = none)
    (hViews : env.finalClaimViews = none)
    (x : WhirStmt F) (m0 m1 : WhirMsg F) (c0 c1 : Nat) :
    let sched : WhirVerifierSchedule := ⟨nv, q, hq, [st]⟩
    let zs := (List.range st.oodCount).map (env.chalField c0)
    let ys := m1.answers
    let folded := (List.range st.queryCount).map (fun j =>
      x.table.getD (env.chalPos c1 j st.domainSize) CommRingOps.zero)
    (whirOracleIop env sched w).verify x [(m0, c0), (m1, c1)] =
      (decide (ys.length = st.oodCount) &&
       decide (m0.poly.length ≤ env.finalDeg + 1) &&
       (zs.zip ys).all (fun zy => decide (RoundPoly.evalCoeffs m0.poly zy.1 = zy.2)) &&
       ((List.range st.queryCount).zip folded).all (fun jv =>
         decide (RoundPoly.evalCoeffs m0.poly
           (env.domPt 1 (env.chalPos c1 jv.1 st.domainSize)) = jv.2)) &&
       decide (x.claim = env.finalClaim m0.poly [])) := by
  dsimp only
  rw [OracleIop.verify_eq]
  have hNumR : (⟨nv, q, hq, [st]⟩ : WhirVerifierSchedule).numRounds = 2 := by
    show (st.foldK + 2) + 0 = 2; rw [hfk]
  let trPub : List (WhirPub F × Nat) :=
    [(⟨m0.poly, m0.answers⟩, c0), (⟨m1.poly, m1.answers⟩, c1)]
  let vals : List F := (List.range st.queryCount).map (fun j =>
    x.table.getD (env.chalPos c1 j st.domainSize) CommRingOps.zero)
  have hLenV : vals.length = st.queryCount := by
    dsimp only [vals]; rw [List.length_map, List.length_range]
  have hSplit : splitStages [st] trPub =
      some [⟨[], (⟨m0.poly, m0.answers⟩, c0), (⟨m1.poly, m1.answers⟩, c1)⟩] := by
    unfold splitStages; dsimp only [trPub]; rw [hfk]; rfl
  have hQueries : whirQueries env ⟨nv, q, hq, [st]⟩ trPub =
      (List.range st.queryCount).map (fun j => (0, env.chalPos c1 j st.domainSize)) := by
    unfold whirQueries
    rw [hSplit]
    change stageQueries env 0 st ⟨[], (⟨m0.poly, m0.answers⟩, c0), (⟨m1.poly, m1.answers⟩, c1)⟩ ++
        [] = _
    rw [List.append_nil]
    unfold stageQueries
    rw [hfk]
    have hFlat : ∀ r : List Nat,
        r.flatMap (fun j => List.map (fun b => (0, env.chalPos c1 j st.domainSize + b * st.domainSize))
          (List.range (2 ^ 0))) =
        r.map (fun j => (0, env.chalPos c1 j st.domainSize)) := by
      intro r; induction r with
      | nil => rfl
      | cons k ks ih =>
        show (0, env.chalPos c1 k st.domainSize + 0 * st.domainSize) :: _ =
          (0, env.chalPos c1 k st.domainSize) :: _
        rw [Nat.zero_mul, Nat.add_zero]
        exact congrArg (_ :: ·) ih
    exact hFlat (List.range st.queryCount)
  have hMapVals :
      (whirQueries env ⟨nv, q, hq, [st]⟩ trPub).map
        (fun q' => whirTable ⟨nv, q, hq, [st]⟩ x [m0, m1] q'.1 q'.2) = vals := by
    rw [hQueries, List.map_map]; rfl
  unfold whirOracleIop
  change (decide ([(m0, c0), (m1, c1)].length = (⟨nv, q, hq, [st]⟩ : WhirVerifierSchedule).numRounds) &&
    whirVerdict env ⟨nv, q, hq, [st]⟩ x.claim trPub
      ((whirQueries env ⟨nv, q, hq, [st]⟩ trPub).map
        (fun q' => whirTable ⟨nv, q, hq, [st]⟩ x [m0, m1] q'.1 q'.2))) = _
  rw [hNumR, hMapVals]
  have hDropMap : ∀ (r : List Nat) (f : Nat → F) (idx : Nat),
      idx < r.length → (((r.map f).drop idx).take 1).headD CommRingOps.zero = f (r.getD idx 0) := by
    intro r f idx
    induction r generalizing idx with
    | nil => intro h; nomatch h
    | cons _ as ih =>
      cases idx with
      | zero => intro _; rfl
      | succ idx => intro h; exact ih idx (Nat.lt_of_succ_lt_succ h)
  have hRangeGetD : ∀ (n j : Nat), j < n → (List.range n).getD j 0 = j := by
    intro n j hj; unfold List.getD; rw [List.getElem?_range hj]; rfl
  have hFoldEq :
      (List.range st.queryCount).map (fun j =>
        foldBlock env [] (env.domPt 0 (env.chalPos c1 j st.domainSize)) ((vals.drop (j * 1)).take 1)) =
      vals := by
    apply List.ext_getElem
    · rw [List.length_map, List.length_range, hLenV]
    · intro j _ hj2
      rw [List.getElem_map, List.getElem_range, Nat.mul_one]
      unfold foldBlock
      have hjLt : j < st.queryCount := by rwa [← hLenV]
      have hjR : j < (List.range st.queryCount).length := by rwa [List.length_range]
      rw [hDropMap (List.range st.queryCount) _ j hjR, hRangeGetD st.queryCount j hjLt]
      dsimp only [vals]
      rw [List.getElem_map, List.getElem_range]
  unfold whirVerdict
  rw [hSplit]
  change (decide ([(m0, c0), (m1, c1)].length = 2) &&
    whirCheckStages env 0 [st]
      [⟨[], (⟨m0.poly, m0.answers⟩, c0), (⟨m1.poly, m1.answers⟩, c1)⟩] x.claim vals) = _
  unfold whirCheckStages whirCheckStagesAux stageFoldRun sumcheckRun
  rw [hfk, hStep, hRaw, hViews]
  let sv0 : StageView F := ⟨[], (⟨m0.poly, m0.answers⟩, c0), (⟨m1.poly, m1.answers⟩, c1)⟩
  let flds := (List.range st.queryCount).map (fun j =>
    foldBlock env [] (env.domPt 0 (env.chalPos c1 j st.domainSize)) ((vals.drop (j * 1)).take 1))
  change (decide ([(m0, c0), (m1, c1)].length = 2) &&
    (decide (m1.answers.length = st.oodCount) &&
     decide (st.queryCount * 1 ≤ vals.length) &&
     (if ([] : List WhirStage).isEmpty then
        decide (m0.poly.length ≤ env.finalDeg + 1) &&
        (((List.range st.oodCount).map (env.chalField c0)).zip m1.answers).all
          (fun zy => decide (RoundPoly.evalCoeffs m0.poly zy.1 = zy.2)) &&
        ((List.range st.queryCount).zip flds).all
          (fun jv => decide (RoundPoly.evalCoeffs m0.poly
            (env.domPt (0 + 1) (env.chalPos c1 jv.1 st.domainSize)) = jv.2)) &&
        decide (x.claim = env.finalClaim m0.poly []) &&
        decide (vals.length = st.queryCount * 1)
      else
        whirCheckStagesAux env [sv0] (0 + 1) [] [sv0]
          (combineClaim x.claim (env.chalField c1 st.queryCount) (m1.answers ++ flds))
          (vals.drop (st.queryCount * 1))))) = _
  have hEmpty : ([] : List WhirStage).isEmpty = true := rfl
  have hZeroAdd : 0 + 1 = 1 := rfl
  have hLen2 : ([(m0, c0), (m1, c1)].length = 2) := rfl
  rw [hEmpty]
  dsimp only [↓reduceIte, flds]
  rw [hFoldEq, hZeroAdd, Nat.mul_one, hLenV, decide_eq_true hLen2,
      decide_eq_true (Nat.le_refl st.queryCount)]
  simp only [decide_true, Bool.true_and, Bool.and_true, Bool.and_assoc]
  rfl

#verify_constructive Qsag.ClosedWhir.WhirStage.foldBound_eq
#verify_constructive Qsag.ClosedWhir.WhirStage.oodBound_eq
#verify_constructive Qsag.ClosedWhir.WhirStage.shiftBound_eq
#verify_constructive Qsag.ClosedWhir.WhirStage.roundBounds_eq
#verify_constructive Qsag.ClosedWhir.stagesRoundBounds_nil
#verify_constructive Qsag.ClosedWhir.stagesRoundBounds_cons
#verify_constructive Qsag.ClosedWhir.WhirVerifierSchedule.roundBounds_eq
#verify_constructive Qsag.ClosedWhir.scheduleQromError_eq
#verify_constructive Qsag.ClosedWhir.whirOracleIop_verify_oneStage_noFold_eq
#verify_constructive Qsag.ClosedWhir.johnson_core
#verify_constructive Qsag.ClosedWhir.WhirStage.johnson_list_le
#verify_constructive Qsag.ClosedWhir.WhirStage.johnsonOk_false_of_beyond_radius
#verify_constructive Qsag.ClosedWhir.WhirStage.decode_list_le
#verify_constructive Qsag.ClosedWhir.stagesRoundBounds_length
#verify_constructive Qsag.ClosedWhir.dfm_sum_le
#verify_constructive Qsag.ClosedWhir.whir_exec_closed_qrom_soundness
#verify_constructive Qsag.ClosedWhir.deployedStages_eq
#verify_constructive Qsag.ClosedWhir.deployedSched_johnsonOk
#verify_constructive Qsag.ClosedWhir.deployedSched_numRounds
#verify_constructive Qsag.ClosedWhir.deployedSched_error_at_2pow40
#verify_constructive Qsag.ClosedWhir.scheduleQromError_mono
#verify_constructive Qsag.ClosedWhir.deployed_whir_exec_closed_qrom_128
#verify_constructive Qsag.ClosedWhir.sampledQuerySched_shape
#verify_constructive Qsag.ClosedWhir.sampledQuery_verify_iff
#verify_constructive Qsag.ClosedWhir.sampledQuery_query_round_flips
#verify_constructive Qsag.ClosedWhir.sampledQueryCert_query_round_bad
#verify_constructive Qsag.ClosedWhir.sampledQuery_honest_accepts
#verify_constructive Qsag.ClosedWhir.sampledQuery_false_not_inLang
#verify_constructive Qsag.ClosedWhir.sampledQuery_false_statement_accepted_once
#verify_constructive Qsag.ClosedWhir.commitRoundIdx_lt_roundsOf
#verify_constructive Qsag.ClosedWhir.stageOfCommitRound_commitRoundIdx
#verify_constructive Qsag.ClosedWhir.allStageQueries_fst_lt
#verify_constructive Qsag.ClosedWhir.whir_succinct_closed_qrom_soundness
#verify_constructive Qsag.ClosedWhir.flatHemPool_nodup
#verify_constructive Qsag.ClosedWhir.flatHemStage_mcaNums_eq
#verify_constructive Qsag.ClosedWhir.flatHemSlicedSched_shape
#verify_constructive Qsag.ClosedWhir.flatHemSlicedSched_error_bits
#verify_constructive Qsag.ClosedWhir.flatHemSlicedCert_fold0_bad_pos
#verify_constructive Qsag.ClosedWhir.flatHemSliced_honest_accepts
#verify_constructive Qsag.ClosedWhir.flatHemSliced_false_not_inLang
#verify_constructive Qsag.ClosedWhir.flatHemSliced_false_accepted_once

#verify_constructive Qsag.ClosedWhir.tooth_omitting_list_size_lowers_every_fold_bound
#verify_constructive Qsag.ClosedWhir.tooth_omitting_list_size_fails_johnson_check
#verify_constructive Qsag.ClosedWhir.tooth_beyond_johnson_radius_invalidates_certificate
#verify_constructive Qsag.ClosedWhir.tooth_empty_schedule_rejects

#tooth_pair Qsag.ClosedWhir.sampledQuery_honest_accepts vs
  Qsag.ClosedWhir.sampledQuery_false_not_inLang
#tooth_pair Qsag.ClosedWhir.flatHemSliced_honest_accepts vs
  Qsag.ClosedWhir.flatHemSliced_false_not_inLang
#tooth_pair Qsag.ClosedWhir.deployedSched_error_at_2pow40 vs
  Qsag.ClosedWhir.tooth_omitting_list_size_lowers_every_fold_bound
#tooth_pair Qsag.ClosedWhir.deployedSched_johnsonOk vs
  Qsag.ClosedWhir.tooth_omitting_list_size_fails_johnson_check
#tooth_pair Qsag.ClosedWhir.deployedSched_johnsonOk vs
  Qsag.ClosedWhir.tooth_beyond_johnson_radius_invalidates_certificate
#tooth_pair Qsag.ClosedWhir.whir_exec_closed_qrom_soundness vs
  Qsag.ClosedWhir.tooth_empty_schedule_rejects

end Qsag.ClosedWhir
end

public section
namespace Qsag.ClosedWhir
#export_eqns stageDepth whirSuccinctRootsOf whirQueries commitRoundIdx
#verify_constructive filter_range_length_qsum combineClaim_eq_eval qsum_mul_mod_eq qsum_mul_div_mod_eq qsum_any_le_mul qsum_good_digits_le
#export_eqns whirVerdict whirCheckStages stageFoldRun sumcheckRun
#export_eqns combineClaim allStageQueries stageQueries whirTable
end Qsag.ClosedWhir
end
