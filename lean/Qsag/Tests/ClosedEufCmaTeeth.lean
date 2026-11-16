module
/-
# Qsag.Tests.ClosedEufCmaTeeth — the epoch latch of `ExecEufCmaGame` is load-bearing

Instance: `crumbToySuite` (constant hash), `prodToyStatefulParams` (stateful, one layer), the
empty key, one coin.

* `inhabited_execEufCmaGame_win`: the latched experiment is not identically lost; a zero-query
  adversary wins on the single coin. With a constant hash this is expected: the bound of
  `jorts_baggy_closed_euf_cma_same_trace_classification` is then met by the extractor events,
  not by `0`.
* `tooth_reused_epoch_latch_wins_euf_cma_prob_one`: in the experiment with the latch check
  removed (`execEufCmaGameWith false`), an explicit adversary that asks for two different
  messages at epoch `0` wins on every coin, and its signing log is not one-time. The one-time
  property is the hypothesis under which the extractor events `prodItsrEvent`, `prodTcrEvent`,
  `prodPreEvent` are defined, so for this run the extractor events do not exist. Under the latch
  the same adversary's second request is refused (`latched_reuse_adversary_logs_one_query`).
* `witness_toy_forgery_reduction_adversary_wins`, `witness_keyed_target_bound_toy`: the
  statement of `execEufCma_win_reduction_adversary_wins` on the winning toy run, and
  `jorts_baggy_closed_euf_cma_keyed_target_bound` instantiated with the three hardness
  hypotheses at bound `1`.
* `tooth_constant_hash_refutes_zero_keyed_hardness`: for the constant hash the three hardness
  hypotheses of `jorts_baggy_closed_euf_cma_keyed_target_bound` cannot all hold with bound `0`,
  even against the class of all programs with the reduction budgets: the forger wins with
  probability one, so one of the three games is won by an adversary that never sees the key.

What the latch tooth does not show: it does not exhibit a forgery assembled from the two
same-epoch signatures under a collision-resistant hash. The winning signature is the
constant-hash forgery `prodToyForgery`, which also wins without any query. The tooth is about
the derivation: without the latch, a run with probability-one winning falls outside the
classification.
-/

public import Qsag.Protocol.Signing.ExecEufCmaClosedGame
public import Qsag.Tests.SigningTeeth
import all Qsag.Protocol.Signing.ExecEufCmaClosedGame
import all Qsag.Protocol.Signing.ProdHashReductions
import all Qsag.Protocol.Signing.HypertreeEufCma
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.ClosedEufCmaTeeth

set_option autoImplicit false

def toyKeygen : Fin 1 → PqSecretKey := fun _ => ⟨[], [], []⟩

def reuseQueryA : ProdSigningQuery := ⟨[1], [], 0, 0⟩
def reuseQueryB : ProdSigningQuery := ⟨[2], [], 0, 0⟩

/-- No signing query; outputs the constant-hash forgery on the empty message. -/
def zeroQueryAdv : SeedWithheldEufCmaAdv 0 0 where
  run := fun _ => .pure ([], prodToyForgery)
  bounded := fun _ => trivial

/-- Two signing queries on different messages at the same epoch `0`, then the same output. -/
def reuseEpochAdv : SeedWithheldEufCmaAdv 0 2 where
  run := fun _ => .signQuery reuseQueryA (fun _ =>
    .signQuery reuseQueryB (fun _ => .pure ([], prodToyForgery)))
  bounded := fun _ _ _ => trivial

/-- A message that was never requested is not in the signer's transcript. -/
theorem fresh_of_not_requested (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (qs : List ProdSigningQuery) (m : List UInt8)
    (h : m ∉ qs.map (fun q => q.message)) :
    m ∉ (productionSigningLog suite params sk qs).map Prod.fst := by
  intro hm
  obtain ⟨e, he, hfst⟩ := List.mem_map.mp hm
  obtain ⟨q, hq, hmsg, _⟩ := productionSigningLog_generated suite params sk qs e he
  exact h (List.mem_map.mpr ⟨q, hq, by rw [← hmsg, hfst]⟩)

theorem toyOutcome_wins (qs : List ProdSigningQuery)
    (h : ([] : List UInt8) ∉ qs.map (fun q => q.message)) :
    prodEufCmaWin crumbToySuite prodToyStatefulParams ⟨⟨[], [], []⟩, qs, [], prodToyForgery⟩ =
      true := by
  unfold prodEufCmaWin
  exact (Bool.and_eq_true _ _).mpr ⟨prodToyForgery_accepted,
    decide_eq_true (fresh_of_not_requested _ _ _ qs [] h)⟩

theorem execEufCmaGameWith_win_eq {n qHash qSign : Nat} (latchOn : Bool) (hPos : 0 < n)
    (suite : TweakableHashSuite) (params : PqHashParams) (keygen : Fin n → PqSecretKey)
    (adv : Fin n → SeedWithheldEufCmaAdv qHash qSign) (ω : Fin n) :
    (execEufCmaGameWith latchOn hPos suite params keygen adv).win ω =
      prodEufCmaWin suite params (execEufCmaOutcome latchOn suite params keygen adv ω) := by
  rfl

theorem finGame_one_winCount (G : Spec.FinGame 1) (h : G.win ⟨0, Nat.zero_lt_succ 0⟩ = true) :
    G.winCount = 1 := by
  refine G.winCount_of_forall_win (fun ω => ?_)
  have hω : ω = ⟨0, Nat.zero_lt_succ 0⟩ := Fin.ext (Nat.lt_one_iff.mp ω.2)
  rw [hω]
  exact h

/-- The latched experiment has a winning run. -/
theorem inhabited_execEufCmaGame_win :
    (ExecEufCmaGame (Nat.zero_lt_one) crumbToySuite prodToyStatefulParams toyKeygen
      (fun _ => zeroQueryAdv)).winCount = 1 := by
  apply finGame_one_winCount
  unfold ExecEufCmaGame
  rw [execEufCmaGameWith_win_eq]
  have hO : execEufCmaOutcome true crumbToySuite prodToyStatefulParams toyKeygen
      (fun _ => zeroQueryAdv) ⟨0, Nat.zero_lt_succ 0⟩ =
      ⟨⟨[], [], []⟩, [], [], prodToyForgery⟩ := rfl
  rw [hO]
  exact toyOutcome_wins [] (fun h => nomatch h)

/-- Without the latch, the reuse adversary's log holds both same-epoch requests. -/
theorem unlatched_reuse_adversary_log :
    (execEufCmaOutcome false crumbToySuite prodToyStatefulParams toyKeygen
      (fun _ => reuseEpochAdv) ⟨0, Nat.zero_lt_succ 0⟩).queries = [reuseQueryA, reuseQueryB] := by
  rfl

/-- With the latch, the second request is refused and only the first is logged. -/
theorem latched_reuse_adversary_logs_one_query :
    (execEufCmaOutcome true crumbToySuite prodToyStatefulParams toyKeygen
      (fun _ => reuseEpochAdv) ⟨0, Nat.zero_lt_succ 0⟩).queries = [reuseQueryA] := by
  rfl

/-- Without the latch, the reuse adversary wins on every coin. -/
theorem unlatched_reuse_adversary_wins_every_coin :
    (execEufCmaGameWith false (Nat.zero_lt_one) crumbToySuite prodToyStatefulParams toyKeygen
      (fun _ => reuseEpochAdv)).winCount = 1 := by
  apply finGame_one_winCount
  rw [execEufCmaGameWith_win_eq]
  have hO : execEufCmaOutcome false crumbToySuite prodToyStatefulParams toyKeygen
      (fun _ => reuseEpochAdv) ⟨0, Nat.zero_lt_succ 0⟩ =
      ⟨⟨[], [], []⟩, [reuseQueryA, reuseQueryB], [], prodToyForgery⟩ := rfl
  rw [hO]
  exact toyOutcome_wins [reuseQueryA, reuseQueryB] (by decide)

/-- `#tooth`: with the latch check removed, a two-query adversary wins with probability one
    while its signing log is not one-time, so winning does not imply the hypothesis under which
    the three reduction events are defined. -/
theorem tooth_reused_epoch_latch_wins_euf_cma_prob_one :
    ¬ ((execEufCmaGameWith false (Nat.zero_lt_one) crumbToySuite prodToyStatefulParams toyKeygen
        (fun _ => reuseEpochAdv)).winCount = 1 →
      ProdOneTimeLog (execEufCmaOutcome false crumbToySuite prodToyStatefulParams toyKeygen
        (fun _ => reuseEpochAdv) ⟨0, Nat.zero_lt_succ 0⟩).queries) := by
  intro h
  have hOne : ProdOneTimeLog [reuseQueryA, reuseQueryB] :=
    h unlatched_reuse_adversary_wins_every_coin
  have hEq : reuseQueryA = reuseQueryB :=
    hOne reuseQueryA (.head _) reuseQueryB (.tail _ (.head _)) rfl
  have hMsg : ([1] : List UInt8) = [2] := congrArg ProdSigningQuery.message hEq
  exact absurd hMsg (by decide)

theorem toyKeygen_uniform :
    Spec.UniformOn (fun sk : PqSecretKey => sk = ⟨[], [], []⟩) toyKeygen :=
  Spec.uniformOn_unique _ _ rfl (fun _ h => h)

/-- The zero-query forger wins the latched toy experiment on every coin, whatever the split. -/
theorem toy_execEufCmaGame_win (π : Spec.CoinSplit 1 1 1) (ω : Fin 1) :
    (ExecEufCmaGame (Nat.zero_lt_one) crumbToySuite prodToyStatefulParams
      (fun ω => toyKeygen (π.chal ω))
      (fun ω => (fun _ : Fin 1 => zeroQueryAdv) (π.advc ω))).win ω = true := by
  unfold ExecEufCmaGame
  rw [execEufCmaGameWith_win_eq]
  have hO : execEufCmaOutcome true crumbToySuite prodToyStatefulParams
      (fun ω => toyKeygen (π.chal ω)) (fun ω => (fun _ : Fin 1 => zeroQueryAdv) (π.advc ω)) ω =
      ⟨⟨[], [], []⟩, [], [], prodToyForgery⟩ := rfl
  rw [hO]
  exact toyOutcome_wins [] (fun h => nomatch h)

/-- On the winning toy run one of the three reduction adversaries wins its game. -/
theorem witness_toy_forgery_reduction_adversary_wins :
    (execSubsetCoverGame (Nat.zero_lt_one) crumbToySuite prodToyStatefulParams
      (fun ω => toyKeygen ((Spec.CoinSplit.challengerOnly 1).chal ω))
      (fun _ => zeroQueryAdv.toOracleAdv)).win ⟨0, Nat.zero_lt_one⟩ = true ∨
    (∃ slot : Fin (prodPathTargetCount prodToyStatefulParams 0),
      (execKeyedPathCollisionGame (Nat.zero_lt_one) crumbToySuite prodToyStatefulParams
        (fun ω => toyKeygen ((Spec.CoinSplit.challengerOnly 1).chal ω))
        (fun _ => execCollisionReductionAdv prodToyStatefulParams slot.val zeroQueryAdv)).win
          ⟨0, Nat.zero_lt_one⟩ = true) ∨
    (∃ slot : Fin (prodPreCandidateCount prodToyStatefulParams),
      (execKeyedSecretPreimageGame (Nat.zero_lt_one) crumbToySuite prodToyStatefulParams
        (fun ω => toyKeygen ((Spec.CoinSplit.challengerOnly 1).chal ω))
        (fun _ => execPreimageReductionAdv prodToyStatefulParams slot.val zeroQueryAdv)).win
          ⟨0, Nat.zero_lt_one⟩ = true) :=
  execEufCma_win_reduction_adversary_wins (Nat.zero_lt_one) crumbToySuite prodToyStatefulParams
    prodToyRadix _ _ ⟨0, Nat.zero_lt_one⟩
    (toy_execEufCmaGame_win (Spec.CoinSplit.challengerOnly 1) ⟨0, Nat.zero_lt_one⟩)

/-- The hypotheses of the bound are jointly satisfiable: instance with the three hardness
    hypotheses at bound `1`. -/
theorem witness_keyed_target_bound_toy :
    Spec.GameBound
      (ExecEufCmaGame (Nat.zero_lt_one) crumbToySuite prodToyStatefulParams
        (fun ω => toyKeygen ((Spec.CoinSplit.challengerOnly 1).chal ω))
        (fun ω => (fun _ : Fin 1 => zeroQueryAdv)
          ((Spec.CoinSplit.challengerOnly 1).advc ω))).winProb
      ((Spec.RatBound.one.add
          (Spec.RatBound.scale (prodPathTargetCount prodToyStatefulParams 0) Spec.RatBound.one)).add
        (Spec.RatBound.scale (prodPreCandidateCount prodToyStatefulParams) Spec.RatBound.one)) :=
  jorts_baggy_closed_euf_cma_keyed_target_bound (Nat.zero_lt_one) crumbToySuite
    prodToyStatefulParams prodToyRadix (Spec.CoinSplit.challengerOnly 1) toyKeygen
    toyKeygen_uniform (fun _ => zeroQueryAdv)
    (𝒜I := fun _ => True) (𝒜T := fun _ => True) (𝒜P := fun _ => True)
    (fun _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ _ => Spec.FinGame.winProb_le_one _)
    (fun _ _ _ _ _ _ _ _ _ => Spec.FinGame.winProb_le_one _)
    (fun _ _ _ _ _ _ _ _ _ => Spec.FinGame.winProb_le_one _)

/-- `#tooth`: for the constant hash, the subset-cover, keyed path-collision and keyed
    secret-preimage games are not all unwinnable at the reduction budgets. -/
theorem tooth_constant_hash_refutes_zero_keyed_hardness :
    ¬ (ExecSubsetCoverHard (fun _ => True) crumbToySuite prodToyStatefulParams
        (fun sk : PqSecretKey => sk = ⟨[], [], []⟩) 0 0 Spec.RatBound.zero ∧
      ExecKeyedPathCollisionHard (fun _ => True) crumbToySuite prodToyStatefulParams
        (fun sk : PqSecretKey => sk = ⟨[], [], []⟩)
        (0 + prodTcrReductionHashBudget prodToyStatefulParams) 0 Spec.RatBound.zero ∧
      ExecKeyedSecretPreimageHard (fun _ => True) crumbToySuite prodToyStatefulParams
        (fun sk : PqSecretKey => sk = ⟨[], [], []⟩)
        (0 + (1 + prodXofHashBudget prodToyStatefulParams)) 0 Spec.RatBound.zero) := by
  intro h
  have hB := jorts_baggy_closed_euf_cma_keyed_target_bound (Nat.zero_lt_one) crumbToySuite
    prodToyStatefulParams prodToyRadix (Spec.CoinSplit.challengerOnly 1) toyKeygen
    toyKeygen_uniform (fun _ => zeroQueryAdv)
    (fun _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial) h.1 h.2.1 h.2.2
  refine Spec.FinGame.not_bound_of_forall_win _
    (toy_execEufCmaGame_win (Spec.CoinSplit.challengerOnly 1)) ?_ hB
  show (0 * 1 + prodPathTargetCount prodToyStatefulParams 0 * 0 * 1) * 1 +
    prodPreCandidateCount prodToyStatefulParams * 0 * (1 * 1) < 1 * 1 * 1
  rw [Nat.mul_zero, Nat.mul_zero]
  decide

#verify_constructive
  Qsag.ClosedEufCmaTeeth.fresh_of_not_requested
  Qsag.ClosedEufCmaTeeth.inhabited_execEufCmaGame_win
  Qsag.ClosedEufCmaTeeth.unlatched_reuse_adversary_log
  Qsag.ClosedEufCmaTeeth.latched_reuse_adversary_logs_one_query
  Qsag.ClosedEufCmaTeeth.unlatched_reuse_adversary_wins_every_coin
  Qsag.ClosedEufCmaTeeth.tooth_reused_epoch_latch_wins_euf_cma_prob_one
  Qsag.ClosedEufCmaTeeth.witness_toy_forgery_reduction_adversary_wins
  Qsag.ClosedEufCmaTeeth.witness_keyed_target_bound_toy
  Qsag.ClosedEufCmaTeeth.tooth_constant_hash_refutes_zero_keyed_hardness

#tooth_pair Qsag.jorts_baggy_closed_euf_cma_same_trace_classification vs
  Qsag.ClosedEufCmaTeeth.tooth_reused_epoch_latch_wins_euf_cma_prob_one
#tooth_pair Qsag.jorts_baggy_closed_euf_cma_keyed_target_bound vs
  Qsag.ClosedEufCmaTeeth.tooth_constant_hash_refutes_zero_keyed_hardness

end Qsag.ClosedEufCmaTeeth
end
