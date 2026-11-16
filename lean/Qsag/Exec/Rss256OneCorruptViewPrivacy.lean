module
/-
# Qsag.Exec.Rss256OneCorruptViewPrivacy — 1-Corrupt `Rss256Engine` View Privacy in Engine Vocabulary

`rss256_one_corrupt_perfect_view_privacy` restates
`Qsag.rss256_one_corrupt_view_pointwise_and_count_eq` with the distinguishing-advantage notions
of `Qsag.Exec.InteractiveUcEngine`: equal `distAcceptCount` and `rationalAcceptDiff` at most `0`.
-/

public import Qsag.Exec.InteractiveUcEngine
public import Qsag.Protocol.Threshold.BaggyAndRss256Security

import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false

/-- **Exact 1-Corrupt `Rss256Engine` View Privacy (`rss256_one_corrupt_perfect_view_privacy`)**:
    Under the corrected `(prg1, prg2, prg0)` mask-key assignment, for EVERY corrupt party
    `corrupt ∈ {P0, P1, P2}`, EVERY secret 256-lane input `(x, y)`, EVERY valid `BGIN19` degree-2
    witness `w`, EVERY challenge `τ ∈ GF(2^{128})`, and EVERY distinguisher `D`:
    1. `rss256SimCorruptView` (using **0** bits of the missing honest share slot) equals
       `rss256RealCorruptView` point-for-point under `rss256_and_bgin19_privacy_equiv`;
    2. Acceptance counts are equal and rational statistical distance is **identically `0`**. -/
theorem rss256_one_corrupt_perfect_view_privacy
    (corrupt : Fin 3)
    (x y : RssPlane256Share) (w : Bgin19Deg2Witness) (hValid : w.Valid)
    (knownPrgA knownPrgB : Plane256)
    (knownZpadA knownZpadB : Tower128 × Tower128)
    (tau : Tower128)
    (D : Rss256JointCorruptView → Bool) :
    let padCard := (2 ^ 256) * (2 ^ 256)
    let bij := rss256_and_bgin19_privacy_equiv corrupt x y w
    let realExec := rss256RealCorruptView corrupt x y w knownPrgA knownPrgB knownZpadA knownZpadB tau
    let simExec := rss256SimCorruptView corrupt x y w knownPrgA knownPrgB knownZpadA knownZpadB tau
    (∀ ω : Fin padCard, realExec ω = simExec (bij.toFun ω)) ∧
    distAcceptCount padCard realExec D = distAcceptCount padCard simExec D ∧
    ratLe (rationalAcceptDiff padCard realExec padCard simExec D) (0, 1) := by
  intro padCard bij realExec simExec
  have hCardPos : 0 < padCard := Nat.mul_pos (Nat.two_pow_pos 256) (Nat.two_pow_pos 256)
  obtain ⟨hPointwise, hCount⟩ := rss256_one_corrupt_view_pointwise_and_count_eq corrupt x y w
    hValid knownPrgA knownPrgB knownZpadA knownZpadB tau D
  have hCountEq : distAcceptCount padCard realExec D = distAcceptCount padCard simExec D :=
    hCount
  have hBad := bad_event_fundamental_lemma padCard hCardPos realExec simExec bij
    (fun _ => false) (fun ω _ => hPointwise ω) D
  have hZeroBad : qsum padCard (fun _ : Fin padCard => if false then 1 else 0) = 0 := by
    simp [qsum_const]
  have hRatDiff : ratLe (rationalAcceptDiff padCard realExec padCard simExec D) (0, 1) := by
    obtain ⟨_, _, hR⟩ := hBad
    rw [hZeroBad] at hR
    refine ⟨hR.1, by decide, ?_⟩
    have hNum0 : (rationalAcceptDiff padCard realExec padCard simExec D).1 * padCard ≤ 0 := by
      simpa only [Nat.zero_mul] using hR.2.2
    have hProd0 : (rationalAcceptDiff padCard realExec padCard simExec D).1 * padCard = 0 :=
      Nat.eq_zero_of_le_zero hNum0
    rcases Nat.mul_eq_zero.mp hProd0 with hN0 | hC0
    · rw [hN0]; simp
    · exact False.elim (Nat.ne_of_gt hCardPos hC0)
  exact ⟨hPointwise, hCountEq, hRatDiff⟩

#verify_constructive rss256_one_corrupt_perfect_view_privacy

end Qsag
end
