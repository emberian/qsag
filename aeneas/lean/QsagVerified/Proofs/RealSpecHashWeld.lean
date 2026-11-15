module
import all QsagVerified.Funs
public import QsagVerified.Proofs.PantsAndQuorumGuards
public import Qsag.Protocol.Signing.HashSigs

/-!
This file welds the WOTS+C digit predicate, including both acceptance and rejection.
It does not identify a SHAKE digest, a hash-chain signature, or a streaming sponge output.
Those require byte-level absorb/finalize/squeeze refinement in addition to the permutation.
-/

public section
namespace qsag_verified.proofs
open Aeneas Aeneas.Std Result
open qsag_verified
set_option maxRecDepth 4096

/-- The canonical specification's digit sum agrees with the library list sum. -/
theorem qsag_sumDigits_eq_sum (xs : List Nat) : Qsag.sumDigits xs = xs.sum := by
  induction xs with
  | nil => exact Qsag.sumDigits_nil
  | cons x xs ih => rw [Qsag.sumDigits_cons, ih, List.sum_cons]

/-- The real extracted WOTS+C checker refines the canonical HashSigs checker,
including its length and range checks, on the 128 base-4 digits of the input digest. -/
theorem wotsc256_verify_refines_qsag (digest : Array Std.U8 32#usize) :
    pants_and_quorum_guards.verified_wotsc256_verify_sum digest =
      .ok (Qsag.checkTargetSum 4 128 192 (pureWotsC256Digits digest)) := by
  obtain ⟨b, hb, hiff⟩ := verified_wotsc256_verify_sum_spec digest
  rw [hb]
  congr 1
  apply Bool.eq_iff_iff.mpr
  rw [hiff, Qsag.checkTargetSum_iff, qsag_sumDigits_eq_sum]
  have hlen : (pureWotsC256Digits digest).length = 128 := by
    simp [pureWotsC256Digits]
  have hbound : ∀ d ∈ pureWotsC256Digits digest, d < 4 := by
    intro d hd
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hd
    exact Nat.mod_lt _ (by decide)
  exact ⟨fun h => ⟨hlen, hbound, h⟩, fun h => h.2.2⟩

/-- A malformed constant-sum digest is rejected by both the MIR and canonical checker. -/
theorem tooth_wotsc256_zero_digest_rejected_by_qsag :
    pants_and_quorum_guards.verified_wotsc256_verify_sum (Array.repeat 32#usize 0#u8) =
      .ok false ∧
    Qsag.checkTargetSum 4 128 192
      (pureWotsC256Digits (Array.repeat 32#usize 0#u8)) = false := by
  have h : Qsag.checkTargetSum 4 128 192
      (pureWotsC256Digits (Array.repeat 32#usize 0#u8)) = false := by
    simp only [Qsag.checkTargetSum, qsag_sumDigits_eq_sum]
    decide
  exact ⟨(wotsc256_verify_refines_qsag _).trans (congrArg Result.ok h), h⟩
/-- Exact acceptance boundary, exposing all canonical checker conditions. -/
theorem wotsc256_accept_iff_qsag (digest : Array Std.U8 32#usize) :
    pants_and_quorum_guards.verified_wotsc256_verify_sum digest = .ok true ↔
      (pureWotsC256Digits digest).length = 128 ∧
      (∀ d ∈ pureWotsC256Digits digest, d < 4) ∧
      Qsag.sumDigits (pureWotsC256Digits digest) = 192 := by
  rw [wotsc256_verify_refines_qsag, Result.ok.injEq, Qsag.checkTargetSum_iff]

/-- Rejection agrees as well as acceptance; no failure or divergence is hidden by
an implication that only considers successful calls. -/
theorem wotsc256_reject_iff_qsag (digest : Array Std.U8 32#usize) :
    pants_and_quorum_guards.verified_wotsc256_verify_sum digest = .ok false ↔
      Qsag.checkTargetSum 4 128 192 (pureWotsC256Digits digest) = false := by
  rw [wotsc256_verify_refines_qsag, Result.ok.injEq]

end qsag_verified.proofs
