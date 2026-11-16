module
public import Qsag.Coding.WelchBerlekampDecoder
import Qsag.Tactic.AssuranceKit

/-!
# Qsag.Tests.WelchBerlekampTeeth

Consequences of `Qsag.Coding.WelchBerlekampDecoder` on concrete words over the seven-element
field, derived from that module's exported statements only. The kernel evaluations of the
decoder (`exWordTwoErrors_decodes`, `exWordThreeErrors_rejected`, `exWordTwoErrors_cost`) are
proved in the decoder module, where its definitions are visible; this file combines them with
the general theorems.

* corruption recovery: the decoded codeword is the only codeword within distance two, and the
  specification decoder `gsDecodeList` returns the same singleton;
* rejection: with three corrupted values no codeword is within distance two, and the
  specification list is empty;
* beyond the unique-decoding radius: two codewords are within distance two of one word;
* the operation bound on six points and at block length 256.
-/

public section
namespace Qsag
namespace Tests
namespace WelchBerlekampTeeth
set_option autoImplicit false
open CommRingOps RoundPoly WelchBerlekamp

/-! ## Corruption recovery -/

theorem radius6 : 2 + 2 * 2 ≤ exDomain6.length := by
  rw [exDomain6_length]
  decide

/-- Every codeword within distance two of the twice-corrupted word is `3 + 2 X`: completeness
    applied to the kernel-evaluated decoder output. -/
theorem recovery_is_unique (Q : List F7) (hT : IsTrimmed Q) (hK : Q.length ≤ 2)
    (hA : exDomain6.length ≤ agreeCount exWordTwoErrors Q exDomain6 + 2) :
    Q = exCodeword := by
  have h := wbDecode_complete 2 2 exDomain6 exWordTwoErrors exDomain6_nodup radius6 Q hT hK hA
  rw [exWordTwoErrors_decodes] at h
  exact (Option.some.inj h).symm

/-- The premises of `recovery_is_unique` hold for `3 + 2 X`. -/
theorem recovery_is_unique_inhabited :
    ∃ Q : List F7, IsTrimmed Q ∧ Q.length ≤ 2 ∧
      exDomain6.length ≤ agreeCount exWordTwoErrors Q exDomain6 + 2 :=
  ⟨exCodeword, exCodeword_trimmed, by rw [exCodeword_length]; decide,
    by rw [exDomain6_length, exWordTwoErrors_agree]; decide⟩

/-- Soundness applied to the decoder output: the decoded word is a codeword within distance
    two. -/
theorem recovery_is_sound :
    IsTrimmed exCodeword ∧ exCodeword.length ≤ 2 ∧
      exDomain6.length ≤ agreeCount exWordTwoErrors exCodeword exDomain6 + 2 := by
  obtain ⟨hT, hK, hA, _⟩ :=
    wbDecode_sound 2 2 exDomain6 exWordTwoErrors exCodeword exWordTwoErrors_decodes
  exact ⟨hT, hK, hA⟩

/-- The subset-enumeration specification decoder returns the same single codeword. -/
theorem recovery_matches_specification :
    gsDecodeList 1 (exDomain6.length - 2) exDomain6 exWordTwoErrors =
      [GsUniPoly.ofCoeffs exCodeword] := by
  rw [wbDecode_eq_unique 1 2 exDomain6 exWordTwoErrors exDomain6_nodup radius6]
  exact exWordTwoErrors_decodeList

/-! ## Rejection with more than `e` errors -/

/-- With three corrupted values no codeword is within distance two. -/
theorem three_errors_no_codeword (Q : List F7) (hT : IsTrimmed Q) (hK : Q.length ≤ 2) :
    ¬ exDomain6.length ≤ agreeCount exWordThreeErrors Q exDomain6 + 2 :=
  (wbDecode_eq_none_iff 2 2 exDomain6 exWordThreeErrors exDomain6_nodup radius6).mp
    exWordThreeErrors_rejected Q hT hK

/-- In particular the original codeword is at distance three. -/
theorem three_errors_original_too_far :
    ¬ exDomain6.length ≤ agreeCount exWordThreeErrors exCodeword exDomain6 + 2 := by
  rw [exDomain6_length, exWordThreeErrors_agree]
  decide

/-- The specification decoder agrees: its list is empty. -/
theorem three_errors_specification_empty :
    gsDecodeList 1 (exDomain6.length - 2) exDomain6 exWordThreeErrors = [] := by
  rw [wbDecode_eq_unique 1 2 exDomain6 exWordThreeErrors exDomain6_nodup radius6]
  exact wbDecodeList_of_none 1 2 exDomain6 exWordThreeErrors exWordThreeErrors_rejected

/-! ## Beyond the unique-decoding radius -/

/-- On five points with `k = 2`, `e = 2` the decoder rejects whatever the word is. -/
theorem short_domain_rejected (word : F7 → F7) : wbDecode 2 2 exDomain5 word = none :=
  wbDecode_none_of_short 2 2 exDomain5 word (by rw [exDomain5_length]; decide)

/-- Two different codewords are within distance two of `exWordAmbiguous`, so no decoder can
    return "the" codeword there. -/
theorem ambiguous_word_two_codewords :
    ∃ P₁ P₂ : List F7, ¬ (P₁ = P₂) ∧ IsTrimmed P₁ ∧ IsTrimmed P₂ ∧
      exDomain5.length ≤ agreeCount exWordAmbiguous P₁ exDomain5 + 2 ∧
      exDomain5.length ≤ agreeCount exWordAmbiguous P₂ exDomain5 + 2 :=
  ⟨exCodeword, [], exCodeword_ne_nil, exCodeword_trimmed, by rfl,
    by rw [exDomain5_length, exWordAmbiguous_agree.1]; decide,
    by rw [exDomain5_length, exWordAmbiguous_agree.2]; decide⟩

/-! ## Operation count -/

theorem wbOpBound_six : wbOpBound 6 = 1344 := by decide

/-- At block length 256 the bound is below `2 ^ 26` field operations, whatever the field. -/
theorem wbOpBound_256 : wbOpBound 256 = 34679844 ∧ wbOpBound 256 < 2 ^ 26 := by decide

/-- Every decoding run on the six-point domain, for every word, dimension and error budget,
    stays within 1344 field operations. -/
theorem six_point_runs_bounded (k e : Nat) (word : F7 → F7) :
    (wbDecodeT k e exDomain6 word).cost ≤ 1344 := by
  have h := wbDecode_ops_poly k e exDomain6 word
  rw [exDomain6_length, wbOpBound_six] at h
  exact h

/-- The measured recovery run: 332 operations. -/
theorem recovery_run_cost : (wbDecodeT 2 2 exDomain6 exWordTwoErrors).cost = 332 :=
  exWordTwoErrors_cost

/-- The counter is not identically zero. -/
theorem recovery_run_cost_ne_zero : ¬ ((wbDecodeT 2 2 exDomain6 exWordTwoErrors).cost = 0) := by
  rw [exWordTwoErrors_cost]
  decide

/-! ## Audits -/

#verify_constructive recovery_is_unique recovery_is_unique_inhabited recovery_is_sound
#verify_constructive recovery_matches_specification
#verify_constructive three_errors_no_codeword three_errors_original_too_far
#verify_constructive three_errors_specification_empty
#verify_constructive short_domain_rejected ambiguous_word_two_codewords
#verify_constructive wbOpBound_six wbOpBound_256 six_point_runs_bounded recovery_run_cost
#verify_constructive recovery_run_cost_ne_zero
#verify_inhabited recovery_is_unique recovery_is_unique_inhabited
#tooth_pair recovery_is_unique vs three_errors_no_codeword
#tooth_pair recovery_is_unique vs ambiguous_word_two_codewords
#tooth_pair recovery_is_sound vs three_errors_original_too_far

end WelchBerlekampTeeth
end Tests
end Qsag
