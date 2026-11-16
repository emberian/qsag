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
* Assumed: a certificate for `deployedSched`. `deployed_whir_exec_closed_qrom_128` takes
  `(sc : WhirScheduleCert env deployedSched w)` as a hypothesis and no such certificate is
  constructed in this library. In addition `deployedStages` uses the profile input
  `mcaNum := whirAffineStageSimpleNum`, which the proved sliced MCA counts of
  `Cwyz26EqualDegreeAndMultiFold` do not reach. The `2^-128` statement for the deployed
  schedule is conditional on both.
-/

public import Qsag.Protocol.Aggregation.ClosedFsQromCompile
public import Qsag.Protocol.Aggregation.Cwyz26EqualDegreeAndMultiFold
public import Qsag.Protocol.Aggregation.QromSaltedMerkleStateRestoration
import Qsag.Math.Counting
import Qsag.Math.CoeffPoly
import Qsag.Math.PolyRing
import Qsag.Math.HasseHensel
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

def WhirStage.domainSize (s : WhirStage) : Nat := 2 ^ s.logDomain

/-- `(1 - δ) > √ρ + η` with `ρ = d / n`, the nominal rate `ρ ≥ 2^-logInvRate`, and
    `L = ⌈1 / (2 η √ρ)⌉`. -/
def WhirStage.johnsonOk (s : WhirStage) : Bool :=
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

def WhirVerifierSchedule.johnsonOk (sched : WhirVerifierSchedule) : Bool :=
  sched.stages.all (fun s => s.johnsonOk)

def stageRounds (s : WhirStage) : Nat := s.foldK + 2

def roundsOf : List WhirStage → Nat
  | [] => 0
  | s :: rest => stageRounds s + roundsOf rest

def WhirVerifierSchedule.numRounds (sched : WhirVerifierSchedule) : Nat := roundsOf sched.stages

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

/-- Field- and domain-specific algebra used by the verifier: challenge decoding, evaluation
    points, the binary fold at a point, and the terminal weight evaluation of the sumcheck. -/
structure WhirEnv (F : Type) where
  chalField : Nat → Nat → F
  chalPos : Nat → Nat → Nat → Nat
  domPt : Nat → Nat → F
  fold2 : F → F → F → F → F
  finalClaim : List F → List F → F
  initClaim : List F → F
  finalDeg : Nat

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

section Verifier
variable {F : Type} [CommRingOps F] [DecidableEq F]

/-- Split the public transcript into per-stage views. -/
def splitStages : List WhirStage → List (WhirPub F × Nat) → Option (List (StageView F))
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
def foldBlock (env : WhirEnv F) : List F → F → List F → F
  | [], _, block => block.headD CommRingOps.zero
  | α :: rest, x, block => foldBlock env rest (CommRingOps.mul x x) (foldLayer env x α block)

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

/-- The verifier's checks, stage by stage, on the values read. -/
def whirCheckStages (env : WhirEnv F) :
    Nat → List WhirStage → List (StageView F) → F → List F → Bool
  | i, st :: rest, v :: vs, claim, vals =>
    match sumcheckRun env st.sumcheckDeg claim v.folds with
    | none => false
    | some (claim1, αs) =>
      let zs := (List.range st.oodCount).map (env.chalField v.commit.2)
      let ys := v.answer.1.answers
      let γ := env.chalField v.answer.2 st.queryCount
      let blockLen := 2 ^ st.foldK
      let need := st.queryCount * blockLen
      let folded := (List.range st.queryCount).map (fun j =>
        foldBlock env αs (env.domPt i (env.chalPos v.answer.2 j st.domainSize))
          ((vals.drop (j * blockLen)).take blockLen))
      decide (ys.length = st.oodCount) && decide (need ≤ vals.length) &&
      (if rest.isEmpty then
        decide (v.commit.1.poly.length ≤ env.finalDeg + 1) &&
        (zs.zip ys).all (fun zy => decide (RoundPoly.evalCoeffs v.commit.1.poly zy.1 = zy.2)) &&
        ((List.range st.queryCount).zip folded).all (fun jv =>
          decide (RoundPoly.evalCoeffs v.commit.1.poly
            (env.domPt (i + 1) (env.chalPos v.answer.2 jv.1 st.domainSize)) = jv.2)) &&
        decide (claim1 = env.finalClaim v.commit.1.poly αs) && decide (vals.length = need)
      else
        whirCheckStages env (i + 1) rest vs (combineClaim claim1 γ (ys ++ folded))
          (vals.drop need))
  | _, _, _, _, _ => false

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

def agreeCount (env : WhirEnv F) (size : Nat) (table P : List F) : Nat :=
  ((List.range size).filter (fun p =>
    decide (RoundPoly.evalCoeffs P (env.domPt 0 p) = table.getD p CommRingOps.zero))).length

/-- The statement language: some polynomial within the first stage's degree bound agrees with
    the committed table on the first stage's agreement threshold and carries the claim. -/
def whirInLang (env : WhirEnv F) (sched : WhirVerifierSchedule) (x : WhirStmt F) : Prop :=
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
    sumcheckRun, foldBlock, WhirStage.domainSize, List.map_cons, List.map_nil, List.drop_zero,
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

#tooth_pair Qsag.ClosedWhir.sampledQuery_honest_accepts vs
  Qsag.ClosedWhir.sampledQuery_false_not_inLang

end Qsag.ClosedWhir
end
