module
/-
# Qsag.Tests.ClosedEufCmaTeeth — the epoch latch of `ExecEufCmaGame` is load-bearing

Instance: `crumbToySuite` (constant hash), `prodToyStatefulParams` (stateful, one layer), the
empty key, one coin.

* `inhabited_execEufCmaGame_win`: the latched experiment is not identically lost; a zero-query
  adversary wins on the single coin. With a constant hash this is expected: the bound of
  `jorts_baggy_closed_euf_cma` is then met by the reduction games, not by `0`.
* `tooth_reused_epoch_latch_wins_euf_cma_prob_one`: in the experiment with the latch check
  removed (`execEufCmaGameWith false`), an explicit adversary that asks for two different
  messages at epoch `0` wins on every coin, and its signing log is not one-time. The one-time
  property is the hypothesis under which the extractor events `prodItsrEvent`, `prodTcrEvent`,
  `prodPreEvent` are defined, so for this run the reduction games of the security theorem do not
  exist. Under the latch the same adversary's second request is refused
  (`latched_reuse_adversary_logs_one_query`).

What the tooth does not show: it does not exhibit a forgery assembled from the two same-epoch
signatures under a collision-resistant hash. The winning signature is the constant-hash forgery
`prodToyForgery`, which also wins without any query. The tooth is about the derivation: without
the latch, a run with probability-one winning falls outside the classification.
-/

public import Qsag.Protocol.Signing.ExecEufCmaClosedGame
import all Qsag.Protocol.Signing.ExecEufCmaClosedGame
import all Qsag.Protocol.Signing.ProdAdaptiveTcrReduction
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

#verify_constructive
  Qsag.ClosedEufCmaTeeth.fresh_of_not_requested
  Qsag.ClosedEufCmaTeeth.inhabited_execEufCmaGame_win
  Qsag.ClosedEufCmaTeeth.unlatched_reuse_adversary_log
  Qsag.ClosedEufCmaTeeth.latched_reuse_adversary_logs_one_query
  Qsag.ClosedEufCmaTeeth.unlatched_reuse_adversary_wins_every_coin
  Qsag.ClosedEufCmaTeeth.tooth_reused_epoch_latch_wins_euf_cma_prob_one

#tooth_pair Qsag.jorts_baggy_closed_euf_cma vs
  Qsag.ClosedEufCmaTeeth.tooth_reused_epoch_latch_wins_euf_cma_prob_one

#print axioms Qsag.ClosedEufCmaTeeth.tooth_reused_epoch_latch_wins_euf_cma_prob_one

end Qsag.ClosedEufCmaTeeth
end
