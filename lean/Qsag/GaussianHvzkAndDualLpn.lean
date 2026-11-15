module
/-
# Qsag.GaussianHvzkAndDualLpn — `Q192` Discrete Gaussian HVZK & Dense Expand-Accumulate Dual-LPN Cryptanalysis

Constructive rational probability, fixed-point rounding, and coding-theoretic work-factor bounds
for the 24-repetition Ring-LWE OR-Sigma proof (`RLWE_ZKPOK_REPS = 24`) and dense expand-accumulate
dual-LPN Pseudorandom Correlation Generator (`PcgTreeDepth.Depth15`):

1. **Fixed-Point `Q192` Truncated Discrete Gaussian Rejection-Sampling HVZK**:
   - Exact discrete rejection-sampling cancellation `acceptProbExact_safe_cancels_shift` and
     verifier-to-proposal box margin `rlwe_accept_box_preimage_in_proposal_box` (`[-3070, 3070)` inside `[-3072, 3072)`).
   - Fixed-point 192-bit fractional rounding bounds `q192_acceptProb_rounding_le_two_neg_190`
     (`≤ 2^-190`) and 30-step binary-exponentiation chain bound `q192_exp_chain30_error_le_two_neg_186`.
   - Constructive finite-support `K`-attempt and conditional-acceptance HVZK simulation bound
     `q192_gaussian_hvzk_statistical_distance` (`≤ K · (tailMass + 2^-190 * supportSize)`) and
     secret-independent abort marginal bound `q192_gaussian_abort_marginal_secret_independent` (`< 2^-128`).
2. **Dense Expand-Accumulate Dual-LPN Piling-Up Bias & Prange / Stern–Dumer ISD Bounds**:
   - Prefix-XOR step-indicator identity `accUnitPuncture_eq_stepIndicator` and suffix-XOR transpose
     duality `acc_transpose_duality` matching `accumulate_receiver_lpn_tree`.
   - Exact rational Piling-Up Lemmas `piling_up_lemma_bernoulli_rat` and
     `piling_up_lemma_regular_blocks_rat`, proving `< 2^-256` linear-test bias on sparse Bernoulli
     dual codewords and balanced 64-tree accumulated blocks.
   - Universal `native_decide`-free Prange and Stern–Dumer Information-Set Decoding lower bounds
     `pcg_dense_depth15_prange_and_stern_dumer_pq128` (`≥ 2^256` classical, `≥ 2^128` Grover) at
     `Depth15` ($M = 2^{21}, r = 139{,}264, t = 64$), paired with `#tooth` counterexamples.
-/

public import Qsag.Constructive
import all Qsag.Constructive
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false

/-! ## 1. Constructive Signed Rationals (`ExactRat`) -/

/-- Constructive signed rational `num / den` with positive natural denominator (`0 Classical.choice`). -/
structure ExactRat where
  num : Int
  den : Nat
  den_pos : 0 < den
  deriving DecidableEq, Repr

@[expose] def ExactRat.ofInt (n : Int) : ExactRat := ⟨n, 1, Nat.one_pos⟩
@[expose] def ExactRat.ofNatRatio (a b : Nat) (hb : 0 < b) : ExactRat := ⟨(a : Int), b, hb⟩
@[expose] def ExactRat.twoNegPow (k : Nat) : ExactRat := ⟨1, 2 ^ k, Nat.two_pow_pos k⟩

@[expose] def ExactRat.eqv (x y : ExactRat) : Prop := x.num * (y.den : Int) = y.num * (x.den : Int)
@[expose] def ExactRat.le (x y : ExactRat) : Prop := x.num * (y.den : Int) ≤ y.num * (x.den : Int)
@[expose] def ExactRat.lt (x y : ExactRat) : ExactRat → Prop := fun _ => False

end Qsag
end
