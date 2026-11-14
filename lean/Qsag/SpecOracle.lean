module

public import Qsag.HashSigs
import all Qsag.HashSigs
import Qsag.Tactic.AssuranceKit

public section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace Qsag.SpecOracle

/-- Production-profile digit guard used by differential WOTS vectors. -/
def wots128Accepts (digest : List UInt8) : Bool :=
  checkTargetSum 4 128 192 (extractBaseWDigits 4 128 digest)

/-- Removing the constant-sum guard accepts the all-zero digest. -/
theorem tooth_zero_digest_rejected :
    wots128Accepts (List.replicate 32 0) = false := by decide

/-- Exact WOTS128 digest acceptance, including its wire size. -/
def ValidWots128Digest (digest : List UInt8) : Prop :=
  digest.length = 32 ∧ wots128Accepts digest = true

theorem accepted_digest_has_target_sum (digest : List UInt8)
    (h : ValidWots128Digest digest) :
    sumDigits (extractBaseWDigits 4 128 digest) = 192 := by
  have ha := h.2
  simp only [wots128Accepts, checkTargetSum, Bool.and_eq_true, decide_eq_true_eq] at ha
  exact ha.2

theorem witness_valid_digest : ∃ digest, ValidWots128Digest digest := by
  refine ⟨List.replicate 32 0x66, ?_⟩
  unfold ValidWots128Digest
  decide

theorem tooth_zero_digest_invalid : ¬ ValidWots128Digest (List.replicate 32 0) := by
  intro h
  have hx := h.2
  rw [tooth_zero_digest_rejected] at hx
  cases hx

end Qsag.SpecOracle

#tooth_pair Qsag.SpecOracle.accepted_digest_has_target_sum vs Qsag.SpecOracle.tooth_zero_digest_invalid
#verify_inhabited Qsag.SpecOracle.accepted_digest_has_target_sum Qsag.SpecOracle.witness_valid_digest

