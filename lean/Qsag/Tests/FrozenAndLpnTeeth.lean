module
/-
# Qsag.Tests.FrozenAndLpnTeeth — the four leaves used from outside

`#verify_constructive`, `#verify_inhabited` and `#tooth_pair` read proof bodies, and a module
does not export proof bodies, so those audits run at the end of each defining module. This
module checks the other side: that the exported statements are enough to work with. Every
proof below uses the imported theorems only as stated; nothing is unfolded. The
`#verify_constructive` lines at the end cover these local proofs only: imported proof bodies
are not visible from here.
-/
public import Qsag.Tactic.AssuranceKit
public import Qsag.Oracle.FrozenChallengeGame
public import Qsag.Protocol.Threshold.SacrificeFreezeSample
public import Qsag.Protocol.Credentials.RepetitionCutAndChoose
public import Qsag.Math.TapRowParityBias

public section
namespace Qsag.FrozenAndLpnTeeth
open Qsag.FrozenChallenge Qsag.SacrificeFreeze Qsag.CutAndChoose Qsag.TapRowBias
set_option autoImplicit false

/-- The same wrong ML-DSA transcript in both orders at six challenges: frozen first it is
accepted on fewer than `q^6 / 2^137` challenge vectors, fitted afterwards on all `q^6`. -/
theorem mldsa_six_challenges_frozen_against_swapped :
    (∀ A : Adversary (List (Gate Fq204)) Fq204, Cheats (A.commit []) →
      countIf (frozenWins (sacConfig 6) A) (vectors fq204Elems 6) * 2 ^ 137 < mldsaQ ^ 6) ∧
    (∃ A : Adversary (List (Gate Fq204)) Fq204, (∀ chis, Cheats (A.commit chis)) ∧
      countIf (swappedWins (sacConfig 6) A) (vectors fq204Elems 6) = mldsaQ ^ 6) := by
  refine ⟨fun A hA => ?_, tooth_mldsa_swapped_order_cheat_always_accepted 6 (by decide)⟩
  have h := mldsa_sacrifice_frozen_soundness 6 (Nat.le_refl 6) A hA
  rw [h.2] at h
  exact h.1

/-- The empty challenge vector never produces a verdict, in any state of the sacrifice machine. -/
theorem sacrifice_empty_challenge_vector_rejected (reps : Nat)
    (s : State (List (Gate Fq204)) Fq204) :
    step (sacConfig reps) s (.sample []) = none :=
  step_empty_sample_rejected (sacConfig reps) s

/-- The 256-party theorems apply to an existing verifier, prover and challenge spaces. -/
theorem limbo256_bounds_are_instantiated :
    ∃ (K : Checker Unit Unit Unit Unit Unit Nat) (P : Prover Unit Unit Unit Unit Unit)
      (Gs Rs : List Unit) (Hs : List Nat),
      winCount K 33 P Gs Rs Hs * 2 ^ 263 < challengeCount 33 Gs Rs Hs ∧
      winCount K 17 P Gs Rs Hs * 2 ^ 135 < challengeCount 17 Gs Rs Hs := by
  obtain ⟨K, P, Gs, Rs, Hs, dG, hS, hH, hRs, hG, hGpos⟩ := inhabited_limbo256_soundness
  exact ⟨K, P, Gs, Rs, Hs, limbo256_tau33_soundness K P Gs Rs Hs dG hS hH hRs hG hGpos,
    limbo256_tau17_soundness K P Gs Rs Hs dG hS hH hRs hG hGpos⟩

/-- The balance premise fails on row 0, derived from the uniform theorem and the row's bias
instead of by inspecting the 64 weights. -/
theorem prodRow0_cannot_satisfy_balance_premise :
    ¬ (∀ w ∈ prodRow0Weights, imbalance 32768 w ≤ 2047) := fun hBal =>
  prodRow0_bias_not_lt_two_neg_256
    (balanced_blocks_special_case prodRow0Weights prodRow0Weights_length hBal)

/-- Row 0 of the deployed generator: the test bit's signed count over the `2^960` noise tuples
is above `2^842` and below `2^843`. -/
theorem prodRow0_signed_count_bracket :
    (noiseSignedSum 32768 (rowTestFns prodRow0Taps) false).natAbs * 2 ^ 117 < 32768 ^ 64 ∧
    32768 ^ 64 < (noiseSignedSum 32768 (rowTestFns prodRow0Taps) false).natAbs * 2 ^ 118 := by
  rw [prodRow0_bias_exact.2.1]
  exact prodRow0_bias_bracket

#verify_constructive mldsa_six_challenges_frozen_against_swapped
#verify_constructive sacrifice_empty_challenge_vector_rejected
#verify_constructive limbo256_bounds_are_instantiated
#verify_constructive prodRow0_cannot_satisfy_balance_premise
#verify_constructive prodRow0_signed_count_bracket

end Qsag.FrozenAndLpnTeeth
