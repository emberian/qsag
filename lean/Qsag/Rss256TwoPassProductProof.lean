module
/-
# Qsag.Rss256TwoPassProductProof — 2-Pass Masked Cross-Product & Barrier Soundness

Constructive (`0 Classical.choice`, `0 sorry`) mechanization of the final `tau`-masked cross-product
opening check and adaptive 1-pass (`ROUND1`) + 2-pass (`ROUND1` + `ROUND2`) `product_proof` barrier
composition in `crates/qsag-core/src/rss256.rs` (`lines 45-81, 2441-2636`):

1. **Final `tau`-Masked Cross-Product Check & 1-Corrupt Opening Privacy (`finalMaskedCrossCheck_complete`,
   `finalMaskedOpen_privacy_equiv`, `finalMaskedCrossCheck_false_bad_coins_le_two`)**:
   Verifiers exchange `(r1x + tau * xf_p, r1y + tau * yf_p)` and `(r2x + tau * xf_q, r2y + tau * yf_q)`
   masked by slot-key pads the receiving verifier lacks (`SimpleEquiv` one-time-pad bijection), while
   any false final claim has nonzero `tau^2` residual and survives on at most `2` values of `tau ∈ S`.
2. **Full Adaptive 1-Pass (`ROUND1`) & 2-Pass (`ROUND1` + `ROUND2`) Barrier Soundness & 8-Wave Bound
   (`singlePass_false_batch_accepting_coins_bound`, `rss256_two_pass_product_proof_sound`,
   `rss256_eight_wave_barrier_concrete_bound`)**:
   Across `R` folding rounds (`b_r ≤ 4`), one pass accepts a false batch on at most
   `(B + 16 + 8 * R) * |S|^(C - 1)` out of `|S|^C` coin vectors, and two independent passes accept on
   at most `((B + 16 + 8 * R) * |S|^(C - 1))^2` out of `|S|^(2 * C)`. At the 8-wave barrier
   (`B = 614,400`, `R = 6`, `|S| = 2^128`), single-pass soundness is `< 2^-108` and 2-pass barrier
   soundness is `< 2^-217` (`rss256.rs:76-77`).
-/

public import Qsag.Rss256TernaryRound

import all Qsag.BinaryTower
import all Qsag.UcGames
import all Qsag.MaliciousSecurity
import all Qsag.Rss256TernaryRound

import Qsag.Tactic.AssuranceKit

public section
namespace Qsag
namespace Rss256ProductProof

set_option autoImplicit false
set_option maxRecDepth 8192

/-! ## 1. Final `tau`-Masked Cross-Product Check & 1-Corrupt Opening Privacy (`rss256.rs:2575-2627`) -/

structure FinalMasks where
  r1x : Tower128
  r1y : Tower128
  r2x : Tower128
  r2y : Tower128

structure FinalCrossShares where
  c0_1 : Tower128
  c0_2 : Tower128
  c1_1 : Tower128
  c1_2 : Tower128

/-- `V1`'s masked opening `[r1x + tau * xfp, r1y + tau * yfp, c0_1 + tau * c1_1 + tau^2 * claim1]`
    (`rss256.rs:2606-2610`). -/
def finalMaskedOpenV1 (m : FinalMasks) (sh : FinalCrossShares)
    (xfp yfp claim1 tau : Tower128) : Tower128 × Tower128 × Tower128 :=
  (towerAdd 7 m.r1x (towerMul 7 tau xfp),
   towerAdd 7 m.r1y (towerMul 7 tau yfp),
   towerAdd 7 (towerAdd 7 sh.c0_1 (towerMul 7 tau sh.c1_1))
              (towerMul 7 (towerMul 7 tau tau) claim1))

/-- `V2`'s masked opening `[r2x + tau * xfq, r2y + tau * yfq, c0_2 + tau * c1_2 + tau^2 * claim2]`
    (`rss256.rs:2611-2615`). -/
def finalMaskedOpenV2 (m : FinalMasks) (sh : FinalCrossShares)
    (xfq yfq claim2 tau : Tower128) : Tower128 × Tower128 × Tower128 :=
  (towerAdd 7 m.r2x (towerMul 7 tau xfq),
   towerAdd 7 m.r2y (towerMul 7 tau yfq),
   towerAdd 7 (towerAdd 7 sh.c0_2 (towerMul 7 tau sh.c1_2))
              (towerMul 7 (towerMul 7 tau tau) claim2))

/-- Exact verifier check `from_v1[0] * from_v2[1] + from_v2[0] * from_v1[1] == from_v1[2] + from_v2[2]`
    (`rss256.rs:2621-2626`). -/
@[expose] def finalMaskedCrossCheck (m : FinalMasks) (sh : FinalCrossShares)
    (xfp yfq xfq yfp claim1 claim2 tau : Tower128) : Bool :=
  let v1 := finalMaskedOpenV1 m sh xfp yfp claim1 tau
  let v2 := finalMaskedOpenV2 m sh xfq yfq claim2 tau
  let lhs := towerAdd 7 (towerMul 7 v1.1 v2.2.1) (towerMul 7 v2.1 v1.2.1)
  let rhs := towerAdd 7 v1.2.2 v2.2.2
  decide (lhs = rhs)

/-- Explicit quadratic residual `[d0, d1, d2]` of `finalMaskedCrossCheck` in `tau`. -/
def finalMaskedResidualCoeffs (m : FinalMasks) (sh : FinalCrossShares)
    (xfp yfq xfq yfp claim1 claim2 : Tower128) : List Tower128 :=
  let trueC0 := towerAdd 7 (towerMul 7 m.r1x m.r2y) (towerMul 7 m.r2x m.r1y)
  let trueC1 := towerAdd 7
    (towerAdd 7 (towerMul 7 m.r1x yfq) (towerMul 7 xfp m.r2y))
    (towerAdd 7 (towerMul 7 m.r2x yfp) (towerMul 7 xfq m.r1y))
  let trueC2 := towerAdd 7 (towerMul 7 xfp yfq) (towerMul 7 xfq yfp)
  [towerAdd 7 trueC0 (towerAdd 7 sh.c0_1 sh.c0_2),
   towerAdd 7 trueC1 (towerAdd 7 sh.c1_1 sh.c1_2),
   towerAdd 7 trueC2 (towerAdd 7 claim1 claim2)]

theorem towerAdd_eq_zero_iff_eq (a b : Tower128) :
    towerAdd 7 a b = towerZero 7 ↔ a = b := by
  constructor
  · intro h
    have h1 := congrArg (fun z => towerAdd 7 z b) h
    rw [towerAdd_assoc, towerAdd_self_zero, towerAdd_zero, towerZero_add] at h1
    exact h1
  · rintro rfl
    exact towerAdd_self_zero 7 a

theorem finalMaskedCrossCheck_iff_evalCoeffs_zero (m : FinalMasks) (sh : FinalCrossShares)
    (xfp yfq xfq yfp claim1 claim2 tau : Tower128) :
    finalMaskedCrossCheck m sh xfp yfq xfq yfp claim1 claim2 tau = true ↔
      RoundPoly.evalCoeffs (finalMaskedResidualCoeffs m sh xfp yfq xfq yfp claim1 claim2) tau =
        towerZero 7 := by
  let v1 := finalMaskedOpenV1 m sh xfp yfp claim1 tau
  let v2 := finalMaskedOpenV2 m sh xfq yfq claim2 tau
  let lhs := towerAdd 7 (towerMul 7 v1.1 v2.2.1) (towerMul 7 v2.1 v1.2.1)
  let rhs := towerAdd 7 v1.2.2 v2.2.2
  have hDec : (finalMaskedCrossCheck m sh xfp yfq xfq yfp claim1 claim2 tau = true) ↔ lhs = rhs :=
    decide_eq_true_iff
  have hXor := (towerAdd_eq_zero_iff_eq lhs rhs).symm
  have hDiff : towerAdd 7 lhs rhs =
      RoundPoly.evalCoeffs (finalMaskedResidualCoeffs m sh xfp yfq xfq yfp claim1 claim2) tau := by
    dsimp only [lhs, rhs, v1, v2, finalMaskedOpenV1, finalMaskedOpenV2,
      finalMaskedResidualCoeffs, RoundPoly.evalCoeffs]
    simp only [towerMul_zero, towerAdd_zero, towerAdd_mul_distrib, towerMul_add_distrib]
    have hMul1 : towerMul 7 m.r1x (towerMul 7 tau yfq) = towerMul 7 tau (towerMul 7 m.r1x yfq) := by ac_rfl
    have hMul2 : towerMul 7 (towerMul 7 tau xfp) m.r2y = towerMul 7 tau (towerMul 7 xfp m.r2y) := by ac_rfl
    have hMul3 : towerMul 7 (towerMul 7 tau xfp) (towerMul 7 tau yfq) =
        towerMul 7 tau (towerMul 7 tau (towerMul 7 xfp yfq)) := by ac_rfl
    have hMul4 : towerMul 7 m.r2x (towerMul 7 tau yfp) = towerMul 7 tau (towerMul 7 m.r2x yfp) := by ac_rfl
    have hMul5 : towerMul 7 (towerMul 7 tau xfq) m.r1y = towerMul 7 tau (towerMul 7 xfq m.r1y) := by ac_rfl
    have hMul6 : towerMul 7 (towerMul 7 tau xfq) (towerMul 7 tau yfp) =
        towerMul 7 tau (towerMul 7 tau (towerMul 7 xfq yfp)) := by ac_rfl
    have hMul7 : towerMul 7 (towerMul 7 tau tau) claim1 =
        towerMul 7 tau (towerMul 7 tau claim1) := by ac_rfl
    have hMul8 : towerMul 7 (towerMul 7 tau tau) claim2 =
        towerMul 7 tau (towerMul 7 tau claim2) := by ac_rfl
    rw [hMul1, hMul2, hMul3, hMul4, hMul5, hMul6, hMul7, hMul8]
    simp only [towerMul_add_distrib]
    ac_rfl
  rw [hDec, hXor, hDiff]

theorem finalMaskedCrossCheck_complete (m : FinalMasks) (sh : FinalCrossShares)
    (xfp yfq xfq yfp claim1 claim2 tau : Tower128)
    (hC0 : towerAdd 7 sh.c0_1 sh.c0_2 =
      towerAdd 7 (towerMul 7 m.r1x m.r2y) (towerMul 7 m.r2x m.r1y))
    (hC1 : towerAdd 7 sh.c1_1 sh.c1_2 =
      towerAdd 7
        (towerAdd 7 (towerMul 7 m.r1x yfq) (towerMul 7 xfp m.r2y))
        (towerAdd 7 (towerMul 7 m.r2x yfp) (towerMul 7 xfq m.r1y)))
    (hClaim : towerAdd 7 claim1 claim2 =
      towerAdd 7 (towerMul 7 xfp yfq) (towerMul 7 xfq yfp)) :
    finalMaskedCrossCheck m sh xfp yfq xfq yfp claim1 claim2 tau = true := by
  rw [finalMaskedCrossCheck_iff_evalCoeffs_zero]
  unfold finalMaskedResidualCoeffs
  dsimp only [RoundPoly.evalCoeffs]
  rw [hC0, hC1, hClaim]
  simp only [towerAdd_self_zero, towerMul_zero, towerAdd_zero]

/-- **1-Corrupt Verifier Opening Privacy (`finalMaskedOpen_privacy_equiv`)**:
    For any secret folded values `(xf, yf)` and public `tau`, the mask-to-opening map
    `(rx, ry) ↦ (rx + tau * xf, ry + tau * yf)` is an explicit involutive `SimpleEquiv` bijection on
    `Tower128 × Tower128`, so a corrupt verifier lacking the other slot's mask key sees a uniform
    independent pair! -/
def finalMaskedOpen_privacy_equiv (xf yf tau : Tower128) :
    SimpleEquiv (Tower128 × Tower128) (Tower128 × Tower128) where
  toFun r := (towerAdd 7 r.1 (towerMul 7 tau xf), towerAdd 7 r.2 (towerMul 7 tau yf))
  invFun o := (towerAdd 7 o.1 (towerMul 7 tau xf), towerAdd 7 o.2 (towerMul 7 tau yf))
  left_inv r := by
    cases r
    simp only [towerAdd_assoc, towerAdd_self_zero, towerAdd_zero]
  right_inv o := by
    cases o
    simp only [towerAdd_assoc, towerAdd_self_zero, towerAdd_zero]

theorem finalMaskedCrossCheck_false_bad_coins_le_two (m : FinalMasks) (sh : FinalCrossShares)
    (xfp yfq xfq yfp claim1 claim2 : Tower128)
    (hFalse : towerAdd 7 claim1 claim2 ≠ towerAdd 7 (towerMul 7 xfp yfq) (towerMul 7 xfq yfp))
    (S : List Tower128) (hS : S.Nodup) :
    (S.filter (fun tau => finalMaskedCrossCheck m sh xfp yfq xfq yfp claim1 claim2 tau)).length ≤ 2 := by
  have hC2Ne : towerAdd 7 (towerAdd 7 (towerMul 7 xfp yfq) (towerMul 7 xfq yfp))
      (towerAdd 7 claim1 claim2) ≠ towerZero 7 := by
    intro hZ
    have hEq := (towerAdd_eq_zero_iff_eq _ _).mp hZ
    exact hFalse hEq.symm
  have hQ := quadratic_roots_le_two_tower128
    (towerAdd 7 (towerAdd 7 (towerMul 7 m.r1x m.r2y) (towerMul 7 m.r2x m.r1y))
                (towerAdd 7 sh.c0_1 sh.c0_2))
    (towerAdd 7 (towerAdd 7
      (towerAdd 7 (towerMul 7 m.r1x yfq) (towerMul 7 xfp m.r2y))
      (towerAdd 7 (towerMul 7 m.r2x yfp) (towerMul 7 xfq m.r1y)))
      (towerAdd 7 sh.c1_1 sh.c1_2))
    (towerAdd 7 (towerAdd 7 (towerMul 7 xfp yfq) (towerMul 7 xfq yfp))
                (towerAdd 7 claim1 claim2))
    S hS (Or.inr (Or.inr hC2Ne))
  have hPred : (fun tau => finalMaskedCrossCheck m sh xfp yfq xfq yfp claim1 claim2 tau) =
      (fun tau => decide (RoundPoly.evalCoeffs
        (finalMaskedResidualCoeffs m sh xfp yfq xfq yfp claim1 claim2) tau = towerZero 7)) := by
    funext tau
    by_cases hOk : finalMaskedCrossCheck m sh xfp yfq xfq yfp claim1 claim2 tau = true
    · rw [hOk, decide_eq_true ((finalMaskedCrossCheck_iff_evalCoeffs_zero m sh
        xfp yfq xfq yfp claim1 claim2 tau).mp hOk)]
    · have hF : finalMaskedCrossCheck m sh xfp yfq xfq yfp claim1 claim2 tau = false := by
        cases h : finalMaskedCrossCheck m sh xfp yfq xfq yfp claim1 claim2 tau
        · rfl
        · exact absurd h hOk
      rw [hF]
      have hNz : RoundPoly.evalCoeffs
          (finalMaskedResidualCoeffs m sh xfp yfq xfq yfp claim1 claim2) tau ≠ towerZero 7 :=
        fun hZ => hOk ((finalMaskedCrossCheck_iff_evalCoeffs_zero m sh
          xfp yfq xfq yfp claim1 claim2 tau).mpr hZ)
      rw [decide_eq_false hNz]
  rw [hPred]
  exact hQ

/-! ## 2. Full Adaptive 1-Pass (`ROUND1`) & 2-Pass (`ROUND1` + `ROUND2`) Product Proof Composition -/

/-- Remaining folding bit-width `tailBits (b :: rs) = tailBits rs + b` so `Vec128 (tailBits (b :: rs))`
    is definitionally `Vec128 (tailBits rs + b)`. -/
def tailBits : List Nat → Nat
  | [] => 0
  | b :: rs => tailBits rs + b

theorem tailBits_eq_sum (rs : List Nat) : tailBits rs = rs.sum := by
  induction rs with
  | nil => rfl
  | cons b rs ih =>
    simp only [tailBits, List.sum_cons, ih, Nat.add_comm]

/-- Coin space of `foldBits` folding rounds + final `tau` coin (`sum foldBits + 1` elements of `S`). -/
inductive FoldAndTauCoins : List Nat → Type where
  | finalTau : Tower128 → FoldAndTauCoins []
  | step : {b : Nat} → {rs : List Nat} →
      ChallengeTuple b → FoldAndTauCoins rs → FoldAndTauCoins (b :: rs)

def foldAndTauCoinSpace (S : List Tower128) : (rs : List Nat) → List (FoldAndTauCoins rs)
  | [] => S.map FoldAndTauCoins.finalTau
  | b :: rs =>
    (challengeTuples S b).flatMap (fun gs =>
      (foldAndTauCoinSpace S rs).map (fun tl => .step gs tl))

theorem foldAndTauCoinSpace_length (S : List Tower128) (rs : List Nat) :
    (foldAndTauCoinSpace S rs).length = S.length ^ (rs.sum + 1) := by
  induction rs with
  | nil =>
    simp only [foldAndTauCoinSpace, List.length_map, List.sum_nil, Nat.zero_add, Nat.pow_one]
  | cons b rs ih =>
    rw [foldAndTauCoinSpace, flatMap_map_len, challengeTuples_length, ih,
        List.sum_cons, Nat.add_assoc, Nat.pow_add]

/-- Adaptive prover strategy across `foldBits` folding rounds + final `(c0, c1)` shares. -/
inductive FoldAndTauProver : List Nat → Type where
  | finalShares : FinalCrossShares → FoldAndTauProver []
  | step : {b : Nat} → {rs : List Nat} →
      TernaryTab b → (ChallengeTuple b → FoldAndTauProver rs) → FoldAndTauProver (b :: rs)

def foldAndTauAccepts : (rs : List Nat) → Tower128 →
    Vec128 (tailBits rs) → Vec128 (tailBits rs) →
    Vec128 (tailBits rs) → Vec128 (tailBits rs) →
    FinalMasks → FoldAndTauProver rs → FoldAndTauCoins rs → Bool
  | [], claim, .leaf xfp, .leaf yfq, .leaf xfq, .leaf yfp, masks, .finalShares sh, .finalTau tau =>
    finalMaskedCrossCheck masks sh xfp yfq xfq yfp claim (towerZero 7) tau
  | b :: rs, claim, xp, yq, xq, yp, masks, .step sProver nextP, .step gs tl =>
    let claim' := nextClaim b claim (unitBoolWeights b) sProver gs
    foldAndTauAccepts rs claim'
      (foldVec (tailBits rs) b gs xp) (foldVec (tailBits rs) b gs yq)
      (foldVec (tailBits rs) b gs xq) (foldVec (tailBits rs) b gs yp)
      masks (nextP gs) tl

theorem foldAndTau_false_claim_bad_coins_le (S : List Tower128) (hS : S.Nodup) (rs : List Nat) :
    ∀ (claim : Tower128) (xp yq xq yp : Vec128 (tailBits rs))
      (masks : FinalMasks) (p : FoldAndTauProver rs),
      claim ≠ vecCross xp yq xq yp →
      ((foldAndTauCoinSpace S rs).filter
        (foldAndTauAccepts rs claim xp yq xq yp masks p)).length ≤
        (2 * rs.sum + 2) * S.length ^ rs.sum := by
  induction rs with
  | nil =>
    intro claim xp yq xq yp masks p hFalse
    cases xp with | leaf xfp =>
    cases yq with | leaf yfq =>
    cases xq with | leaf xfq =>
    cases yp with | leaf yfp =>
    cases p with | finalShares sh =>
    unfold foldAndTauCoinSpace
    rw [filter_map_len FoldAndTauCoins.finalTau
      (foldAndTauAccepts [] claim (.leaf xfp) (.leaf yfq) (.leaf xfq) (.leaf yfp) masks
        (.finalShares sh)) S]
    simp only [foldAndTauAccepts, List.sum_nil, Nat.mul_zero, Nat.zero_add, Nat.pow_zero, Nat.mul_one]
    have hFalseAdd : towerAdd 7 claim (towerZero 7) ≠
        towerAdd 7 (towerMul 7 xfp yfq) (towerMul 7 xfq yfp) := by
      rw [towerAdd_zero]; exact hFalse
    exact finalMaskedCrossCheck_false_bad_coins_le_two masks sh xfp yfq xfq yfp
      claim (towerZero 7) hFalseAdd S hS
  | cons b rs ih =>
    intro claim xp yq xq yp masks p hFalse
    cases p with | step sProver nextP =>
    unfold foldAndTauCoinSpace
    rw [filter_flatMap_len]
    let sTrue := honestRoundTab (tailBits rs) b xp yq xq yp
    have hSumEq : weightedBoolSum (unitBoolWeights b) sTrue = vecCross xp yq xq yp :=
      weightedBoolSum_unit_honestRoundTab (tailBits rs) b xp yq xq yp
    have hFalseSum : claim ≠ weightedBoolSum (unitBoolWeights b) sTrue := by
      rw [hSumEq]; exact hFalse
    have hRoundBad := nextClaim_false_bad_coins_le b claim (unitBoolWeights b)
      (zeroCorner_unitBoolWeights b) sProver sTrue hFalseSum S hS
    have hSplit := sum_map_le_split
      (fun gs => decide (nextClaim b claim (unitBoolWeights b) sProver gs = ternaryEval gs sTrue))
      (fun gs => (((foldAndTauCoinSpace S rs).map (fun tl => FoldAndTauCoins.step gs tl)).filter
        (foldAndTauAccepts (b :: rs) claim xp yq xq yp masks (.step sProver nextP))).length)
      (S.length ^ (rs.sum + 1)) ((2 * rs.sum + 2) * S.length ^ rs.sum)
      (fun gs _ => by
        rw [filter_map_len (fun tl => FoldAndTauCoins.step gs tl)
          (foldAndTauAccepts (b :: rs) claim xp yq xq yp masks (.step sProver nextP))
          (foldAndTauCoinSpace S rs), ← foldAndTauCoinSpace_length S rs]
        exact List.length_filter_le _ _)
      (fun gs hGood => by
        rw [filter_map_len (fun tl => FoldAndTauCoins.step gs tl)
          (foldAndTauAccepts (b :: rs) claim xp yq xq yp masks (.step sProver nextP))
          (foldAndTauCoinSpace S rs)]
        have hNeNext : nextClaim b claim (unitBoolWeights b) sProver gs ≠
            vecCross (foldVec (tailBits rs) b gs xp) (foldVec (tailBits rs) b gs yq)
                     (foldVec (tailBits rs) b gs xq) (foldVec (tailBits rs) b gs yp) := by
          rw [← ternaryEval_honestRoundTab_eq]
          exact of_decide_eq_false hGood
        exact ih (nextClaim b claim (unitBoolWeights b) sProver gs)
          (foldVec (tailBits rs) b gs xp) (foldVec (tailBits rs) b gs yq)
          (foldVec (tailBits rs) b gs xq) (foldVec (tailBits rs) b gs yp)
          masks (nextP gs) hNeNext)
      (challengeTuples S b)
    rw [challengeTuples_length] at hSplit
    have hTerm1 : ((challengeTuples S b).filter (fun gs =>
        decide (nextClaim b claim (unitBoolWeights b) sProver gs = ternaryEval gs sTrue))).length *
        S.length ^ (rs.sum + 1) ≤ 2 * b * S.length ^ (b + rs.sum) := by
      let L := ((challengeTuples S b).filter (fun gs =>
        decide (nextClaim b claim (unitBoolWeights b) sProver gs = ternaryEval gs sTrue))).length
      calc L * S.length ^ (rs.sum + 1)
          ≤ ternaryBadBound S.length b * S.length ^ (rs.sum + 1) :=
            Nat.mul_le_mul_right _ hRoundBad
        _ = ternaryBadBound S.length b * (S.length * S.length ^ rs.sum) := by
            rw [Nat.pow_succ, Nat.mul_comm (S.length ^ rs.sum) S.length]
        _ = (ternaryBadBound S.length b * S.length) * S.length ^ rs.sum := by
            rw [Nat.mul_assoc]
        _ = 2 * b * S.length ^ (b + rs.sum) := by
            rw [ternaryBadBound_mul_eq, Nat.mul_assoc (2 * b), ← Nat.pow_add]
    have hTerm2 : S.length ^ b * ((2 * rs.sum + 2) * S.length ^ rs.sum) =
        (2 * rs.sum + 2) * S.length ^ (b + rs.sum) := by
      rw [← Nat.mul_assoc, Nat.mul_comm (S.length ^ b) (2 * rs.sum + 2),
          Nat.mul_assoc, ← Nat.pow_add]
    have hTotal : 2 * b * S.length ^ (b + rs.sum) + (2 * rs.sum + 2) * S.length ^ (b + rs.sum) =
        (2 * (b :: rs).sum + 2) * S.length ^ (b :: rs).sum := by
      simp only [List.sum_cons, ← Nat.add_mul]
      have hLin : 2 * b + (2 * rs.sum + 2) = 2 * (b + rs.sum) + 2 := by omega
      rw [hLin]
    exact Nat.le_trans hSplit (hTotal ▸ Nat.add_le_add hTerm1 (Nat.le_of_eq hTerm2))

/-- Full single-pass coin vector: `(chi, tensorGammas, foldAndTauCoins)` (`9 + sum foldBits` coins). -/
abbrev PassCoins (foldBits : List Nat) :=
  Tower128 × ChallengeTuple TENSOR_BITS × FoldAndTauCoins foldBits

def passCoinSpace (S : List Tower128) (foldBits : List Nat) : List (PassCoins foldBits) :=
  S.flatMap (fun chi =>
    (challengeTuples S TENSOR_BITS).flatMap (fun gTensor =>
      (foldAndTauCoinSpace S foldBits).map (fun ft => (chi, gTensor, ft))))

theorem passCoinSpace_length (S : List Tower128) (foldBits : List Nat) :
    (passCoinSpace S foldBits).length = S.length ^ (TENSOR_BITS + foldBits.sum + 2) := by
  unfold passCoinSpace
  have hInner : ∀ chi : Tower128,
      ((challengeTuples S TENSOR_BITS).flatMap (fun gTensor =>
        (foldAndTauCoinSpace S foldBits).map (fun ft => (chi, gTensor, ft)))).length =
      S.length ^ (TENSOR_BITS + foldBits.sum + 1) := by
    intro chi
    rw [flatMap_map_len, challengeTuples_length, foldAndTauCoinSpace_length,
        ← Nat.pow_add, Nat.add_assoc]
  have hOuter : ∀ xs : List Tower128,
      (xs.flatMap (fun chi =>
        (challengeTuples S TENSOR_BITS).flatMap (fun gTensor =>
          (foldAndTauCoinSpace S foldBits).map (fun ft => (chi, gTensor, ft))))).length =
      xs.length * S.length ^ (TENSOR_BITS + foldBits.sum + 1) := by
    intro xs
    induction xs with
    | nil => simp only [List.flatMap_nil, List.length_nil, Nat.zero_mul]
    | cons x xs ih =>
      simp only [List.flatMap_cons, List.length_append, hInner x, ih,
        List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm]
  rw [hOuter S, Nat.mul_comm, ← Nat.pow_succ]

/-- Adaptive single-pass prover: after `chi`, chooses `tensorTab : TernaryTab 7`, and after
    `gTensor : ChallengeTuple 7`, runs `FoldAndTauProver foldBits`. -/
structure PassProver (foldBits : List Nat) where
  tensorTab : Tower128 → TernaryTab TENSOR_BITS
  afterTensor : Tower128 → ChallengeTuple TENSOR_BITS → FoldAndTauProver foldBits

/-- Full recorded gate batch for one proof `p` over `foldBits`:
    - `gateErrorBlocks` (`≤ B` 128-bit half-plane error blocks),
    - `xp, yq, xq, yp` (`chi`-dependent bound vectors of shape `Vec128 (tailBits foldBits + 7)`),
    - `initialClaim chi` (`claim1[p] + claim2[p]` from `linear_terms`), linked to the true weighted
      sum by `initialClaim chi + trueCrossSum chi = RoundPoly.evalCoeffs gateErrorBlocks chi`! -/
structure RecordedPassBatch (foldBits : List Nat) where
  gateErrorBlocks : List Tower128
  xp : Tower128 → Vec128 (tailBits foldBits + TENSOR_BITS)
  yq : Tower128 → Vec128 (tailBits foldBits + TENSOR_BITS)
  xq : Tower128 → Vec128 (tailBits foldBits + TENSOR_BITS)
  yp : Tower128 → Vec128 (tailBits foldBits + TENSOR_BITS)
  initialClaim : Tower128 → Tower128
  masks : Tower128 → FinalMasks
  claim_defect_eq : ∀ chi : Tower128,
    towerAdd 7 (initialClaim chi)
      (weightedBoolSum (chiBoolWeights chi TENSOR_BITS)
        (honestRoundTab (tailBits foldBits) TENSOR_BITS
          (xp chi) (yq chi) (xq chi) (yp chi))) =
    RoundPoly.evalCoeffs gateErrorBlocks chi

@[expose] def singlePassAccepts (foldBits : List Nat) (batch : RecordedPassBatch foldBits)
    (prover : PassProver foldBits) (coins : PassCoins foldBits) : Bool :=
  let (chi, gTensor, ftCoins) := coins
  let claimAfterTensor := nextClaim TENSOR_BITS (batch.initialClaim chi)
    (chiBoolWeights chi TENSOR_BITS) (prover.tensorTab chi) gTensor
  foldAndTauAccepts foldBits claimAfterTensor
    (foldVec (tailBits foldBits) TENSOR_BITS gTensor (batch.xp chi))
    (foldVec (tailBits foldBits) TENSOR_BITS gTensor (batch.yq chi))
    (foldVec (tailBits foldBits) TENSOR_BITS gTensor (batch.xq chi))
    (foldVec (tailBits foldBits) TENSOR_BITS gTensor (batch.yp chi))
    (batch.masks chi) (prover.afterTensor chi gTensor) ftCoins

theorem foldBits_sum_le_four_mul (rs : List Nat)
    (h : ∀ b ∈ rs, b ≤ FOLD_BITS) : 2 * rs.sum ≤ 8 * rs.length := by
  induction rs with
  | nil => exact Nat.le_refl 0
  | cons b rs ih =>
    have hb : b ≤ 4 := h b (.head _)
    have hSub := ih (fun x hx => h x (.tail _ hx))
    simp only [List.sum_cons, List.length_cons]
    omega

/-- **Single-Pass (`ROUND1`) Adaptive Soundness (`singlePass_false_batch_accepting_coins_bound`)**:
    Matching `rss256.rs:73-75` (`(B + 2 * 7 + 8 * R + 2) / 2^128`), for ANY false gate batch of
    `≤ B` half-plane blocks (`1 ≤ B ≤ |S|`), folding schedule `foldBits` with `b_r ≤ 4`
    (`R = foldBits.length`), and adaptive `PassProver foldBits`, at most
    `(B + 16 + 8 * R) * |S|^(TENSOR_BITS + foldBits.sum + 1)` out of
    `|S|^(TENSOR_BITS + foldBits.sum + 2)` pass coin vectors accept! -/
theorem singlePass_false_batch_accepting_coins_bound
    (B : Nat) (foldBits : List Nat) (batch : RecordedPassBatch foldBits)
    (prover : PassProver foldBits) (S : List Tower128) (hS : S.Nodup)
    (hBPos : 1 ≤ B) (hBLen : batch.gateErrorBlocks.length ≤ B) (hDom : B ≤ S.length)
    (hArity : ∀ b ∈ foldBits, b ≤ FOLD_BITS)
    (hFault : ∃ e ∈ batch.gateErrorBlocks, e ≠ towerZero 7) :
    ((passCoinSpace S foldBits).filter (singlePassAccepts foldBits batch prover)).length ≤
      (B + 16 + 8 * foldBits.length) * S.length ^ (TENSOR_BITS + foldBits.sum + 1) := by
  let E := TENSOR_BITS + foldBits.sum + 1
  have hInnerBound : ∀ chi : Tower128,
      RoundPoly.evalCoeffs batch.gateErrorBlocks chi ≠ towerZero 7 →
      (((challengeTuples S TENSOR_BITS).flatMap (fun gTensor =>
        (foldAndTauCoinSpace S foldBits).map (fun ft => (chi, gTensor, ft)))).filter
        (singlePassAccepts foldBits batch prover)).length ≤
      (14 + 2 * foldBits.sum + 2) * S.length ^ (TENSOR_BITS + foldBits.sum) := by
    intro chi hChiNz
    rw [filter_flatMap_len]
    let sTrue := honestRoundTab (tailBits foldBits) TENSOR_BITS
      (batch.xp chi) (batch.yq chi) (batch.xq chi) (batch.yp chi)
    have hClaimFalse : batch.initialClaim chi ≠
        weightedBoolSum (chiBoolWeights chi TENSOR_BITS) sTrue := by
      intro hEq
      have hDef := batch.claim_defect_eq chi
      dsimp only [sTrue] at hEq
      rw [hEq, towerAdd_self_zero] at hDef
      exact hChiNz hDef.symm
    have hTensorBad := nextClaim_false_bad_coins_le TENSOR_BITS (batch.initialClaim chi)
      (chiBoolWeights chi TENSOR_BITS) (zeroCorner_chiBoolWeights chi TENSOR_BITS)
      (prover.tensorTab chi) sTrue hClaimFalse S hS
    have hSplitT := sum_map_le_split
      (fun gTensor => decide (nextClaim TENSOR_BITS (batch.initialClaim chi)
        (chiBoolWeights chi TENSOR_BITS) (prover.tensorTab chi) gTensor =
        ternaryEval gTensor sTrue))
      (fun gTensor => (((foldAndTauCoinSpace S foldBits).map (fun ft => (chi, gTensor, ft))).filter
        (singlePassAccepts foldBits batch prover)).length)
      (S.length ^ (foldBits.sum + 1)) ((2 * foldBits.sum + 2) * S.length ^ foldBits.sum)
      (fun gTensor _ => by
        rw [filter_map_len (fun ft => (chi, gTensor, ft))
          (singlePassAccepts foldBits batch prover) (foldAndTauCoinSpace S foldBits),
          ← foldAndTauCoinSpace_length S foldBits]
        exact List.length_filter_le _ _)
      (fun gTensor hGood => by
        rw [filter_map_len (fun ft => (chi, gTensor, ft))
          (singlePassAccepts foldBits batch prover) (foldAndTauCoinSpace S foldBits)]
        have hNeNext : nextClaim TENSOR_BITS (batch.initialClaim chi)
            (chiBoolWeights chi TENSOR_BITS) (prover.tensorTab chi) gTensor ≠
            vecCross
              (foldVec (tailBits foldBits) TENSOR_BITS gTensor (batch.xp chi))
              (foldVec (tailBits foldBits) TENSOR_BITS gTensor (batch.yq chi))
              (foldVec (tailBits foldBits) TENSOR_BITS gTensor (batch.xq chi))
              (foldVec (tailBits foldBits) TENSOR_BITS gTensor (batch.yp chi)) := by
          rw [← ternaryEval_honestRoundTab_eq]
          exact of_decide_eq_false hGood
        exact foldAndTau_false_claim_bad_coins_le S hS foldBits _ _ _ _ _
          (batch.masks chi) (prover.afterTensor chi gTensor) hNeNext)
      (challengeTuples S TENSOR_BITS)
    rw [challengeTuples_length] at hSplitT
    have hT1 : ((challengeTuples S TENSOR_BITS).filter (fun gTensor =>
        decide (nextClaim TENSOR_BITS (batch.initialClaim chi)
          (chiBoolWeights chi TENSOR_BITS) (prover.tensorTab chi) gTensor =
          ternaryEval gTensor sTrue))).length *
        S.length ^ (foldBits.sum + 1) ≤ 14 * S.length ^ (TENSOR_BITS + foldBits.sum) := by
      let LT := ((challengeTuples S TENSOR_BITS).filter (fun gTensor =>
        decide (nextClaim TENSOR_BITS (batch.initialClaim chi)
          (chiBoolWeights chi TENSOR_BITS) (prover.tensorTab chi) gTensor =
          ternaryEval gTensor sTrue))).length
      have hTwoT : 2 * TENSOR_BITS = 14 := rfl
      calc LT * S.length ^ (foldBits.sum + 1)
          ≤ ternaryBadBound S.length TENSOR_BITS * S.length ^ (foldBits.sum + 1) :=
            Nat.mul_le_mul_right _ hTensorBad
        _ = ternaryBadBound S.length TENSOR_BITS * (S.length * S.length ^ foldBits.sum) := by
            rw [Nat.pow_succ, Nat.mul_comm (S.length ^ foldBits.sum) S.length]
        _ = (ternaryBadBound S.length TENSOR_BITS * S.length) * S.length ^ foldBits.sum := by
            rw [Nat.mul_assoc]
        _ = 14 * S.length ^ (TENSOR_BITS + foldBits.sum) := by
            rw [ternaryBadBound_mul_eq, hTwoT, Nat.mul_assoc 14, ← Nat.pow_add]
    have hT2 : S.length ^ TENSOR_BITS * ((2 * foldBits.sum + 2) * S.length ^ foldBits.sum) =
        (2 * foldBits.sum + 2) * S.length ^ (TENSOR_BITS + foldBits.sum) := by
      rw [← Nat.mul_assoc, Nat.mul_comm (S.length ^ TENSOR_BITS) (2 * foldBits.sum + 2),
          Nat.mul_assoc, ← Nat.pow_add]
    have hCombine : 14 * S.length ^ (TENSOR_BITS + foldBits.sum) +
        (2 * foldBits.sum + 2) * S.length ^ (TENSOR_BITS + foldBits.sum) =
        (14 + 2 * foldBits.sum + 2) * S.length ^ (TENSOR_BITS + foldBits.sum) := by
      rw [← Nat.add_mul, Nat.add_assoc]
    exact Nat.le_trans hSplitT (hCombine ▸ Nat.add_le_add hT1 (Nat.le_of_eq hT2))
  unfold passCoinSpace
  rw [filter_flatMap_len]
  have hChiBad := passBatching_false_bad_coins_le B batch.gateErrorBlocks S hS hBPos hBLen hDom hFault
  have hInnerFullLen : ∀ chi : Tower128,
      ((challengeTuples S TENSOR_BITS).flatMap (fun gTensor =>
        (foldAndTauCoinSpace S foldBits).map (fun ft => (chi, gTensor, ft)))).length = S.length ^ E := by
    intro chi
    rw [flatMap_map_len, challengeTuples_length, foldAndTauCoinSpace_length,
        ← Nat.pow_add, ← Nat.add_assoc]
  have hSplitChi := sum_map_le_split
    (fun chi => decide (RoundPoly.evalCoeffs batch.gateErrorBlocks chi = towerZero 7))
    (fun chi => (((challengeTuples S TENSOR_BITS).flatMap (fun gTensor =>
      (foldAndTauCoinSpace S foldBits).map (fun ft => (chi, gTensor, ft)))).filter
      (singlePassAccepts foldBits batch prover)).length)
    (S.length ^ E) ((14 + 2 * foldBits.sum + 2) * S.length ^ (TENSOR_BITS + foldBits.sum))
    (fun chi _ => by
      rw [← hInnerFullLen chi]
      exact List.length_filter_le _ _)
    (fun chi hGood => hInnerBound chi (of_decide_eq_false hGood))
    S
  have hC1 : (S.filter (fun chi =>
      decide (RoundPoly.evalCoeffs batch.gateErrorBlocks chi = towerZero 7))).length * S.length ^ E ≤
      B * S.length ^ E := Nat.mul_le_mul_right (S.length ^ E) hChiBad
  have hC2 : S.length * ((14 + 2 * foldBits.sum + 2) * S.length ^ (TENSOR_BITS + foldBits.sum)) ≤
      (16 + 8 * foldBits.length) * S.length ^ E := by
    have hSwap : S.length * ((14 + 2 * foldBits.sum + 2) * S.length ^ (TENSOR_BITS + foldBits.sum)) =
        (14 + 2 * foldBits.sum + 2) * S.length ^ E := by
      dsimp only [E]
      rw [← Nat.mul_assoc, Nat.mul_comm S.length (14 + 2 * foldBits.sum + 2),
          Nat.mul_assoc, Nat.mul_comm S.length, ← Nat.pow_succ]
    rw [hSwap]
    have hCoef : 14 + 2 * foldBits.sum + 2 ≤ 16 + 8 * foldBits.length := by
      have hF := foldBits_sum_le_four_mul foldBits hArity
      omega
    exact Nat.mul_le_mul_right (S.length ^ E) hCoef
  have hAddE : B * S.length ^ E + (16 + 8 * foldBits.length) * S.length ^ E =
      (B + 16 + 8 * foldBits.length) * S.length ^ E := by
    rw [← Nat.add_mul, ← Nat.add_assoc]
  exact Nat.le_trans hSplitChi (hAddE ▸ Nat.add_le_add hC1 hC2)

/-- Full 2-pass (`ROUND1` + `ROUND2`, `pass ∈ {0, 1}`) adaptive prover (`rss256.rs:2441-2628`),
    even allowing `pass 1`'s adaptive prover strategy to depend on the entire `pass 0` coin transcript! -/
structure TwoPassProver (foldBits : List Nat) where
  pass0 : PassProver foldBits
  pass1 : PassCoins foldBits → PassProver foldBits

def twoPassCoinSpace (S : List Tower128) (foldBits : List Nat) :
    List (PassCoins foldBits × PassCoins foldBits) :=
  (passCoinSpace S foldBits).flatMap (fun c0 =>
    (passCoinSpace S foldBits).map (fun c1 => (c0, c1)))

theorem twoPassCoinSpace_length (S : List Tower128) (foldBits : List Nat) :
    (twoPassCoinSpace S foldBits).length =
      (S.length ^ (TENSOR_BITS + foldBits.sum + 2)) ^ 2 := by
  unfold twoPassCoinSpace
  rw [flatMap_map_len, passCoinSpace_length, Nat.pow_two]

@[expose] def twoPassAccepts (foldBits : List Nat) (batch : RecordedPassBatch foldBits)
    (prover : TwoPassProver foldBits) (coins : PassCoins foldBits × PassCoins foldBits) : Bool :=
  singlePassAccepts foldBits batch prover.pass0 coins.1 &&
  singlePassAccepts foldBits batch (prover.pass1 coins.1) coins.2

theorem filter_const_false_len {α : Type} (xs : List α) :
    (xs.filter (fun _ => false)).length = 0 := by
  induction xs with
  | nil => rfl
  | cons _ xs ih =>
    simp only [List.filter_cons, Bool.false_eq_true, ↓reduceIte, ih]

/-- **2-Pass (`ROUND1` + `ROUND2`) Product Proof Barrier Soundness (`rss256_two_pass_product_proof_sound`)**:
    Across two passes (`pass ∈ {0, 1}`) with independent `chi`, tensor, folding, and `tau` challenges,
    for ANY false gate batch of `≤ B` 128-bit blocks (`1 ≤ B ≤ |S|`), folding schedule `foldBits`
    with `b_r ≤ 4` (`R = foldBits.length`), and adaptive `TwoPassProver foldBits`, accepting 2-pass
    coin pairs out of `(|S|^C)^2` (`C = 9 + foldBits.sum`) are bounded by
    `((B + 16 + 8 * R) * |S|^(C - 1))^2`! -/
theorem rss256_two_pass_product_proof_sound
    (B : Nat) (foldBits : List Nat) (batch : RecordedPassBatch foldBits)
    (prover : TwoPassProver foldBits) (S : List Tower128) (hS : S.Nodup)
    (hBPos : 1 ≤ B) (hBLen : batch.gateErrorBlocks.length ≤ B) (hDom : B ≤ S.length)
    (hArity : ∀ b ∈ foldBits, b ≤ FOLD_BITS)
    (hFault : ∃ e ∈ batch.gateErrorBlocks, e ≠ towerZero 7) :
    ((twoPassCoinSpace S foldBits).filter (twoPassAccepts foldBits batch prover)).length ≤
      ((B + 16 + 8 * foldBits.length) * S.length ^ (TENSOR_BITS + foldBits.sum + 1)) ^ 2 := by
  let K := (B + 16 + 8 * foldBits.length) * S.length ^ (TENSOR_BITS + foldBits.sum + 1)
  have hP0 := singlePass_false_batch_accepting_coins_bound B foldBits batch prover.pass0
    S hS hBPos hBLen hDom hArity hFault
  unfold twoPassCoinSpace
  rw [filter_flatMap_len]
  have hSplit := sum_map_le_split
    (fun c0 => singlePassAccepts foldBits batch prover.pass0 c0)
    (fun c0 => (((passCoinSpace S foldBits).map (fun c1 => (c0, c1))).filter
      (twoPassAccepts foldBits batch prover)).length)
    K 0
    (fun c0 _ => by
      rw [filter_map_len (fun c1 => (c0, c1))
        (twoPassAccepts foldBits batch prover) (passCoinSpace S foldBits)]
      have hImp : ((passCoinSpace S foldBits).filter (fun c1 =>
          twoPassAccepts foldBits batch prover (c0, c1))).length ≤
          ((passCoinSpace S foldBits).filter
            (singlePassAccepts foldBits batch (prover.pass1 c0))).length :=
        filter_len_le_of_imp _ _ (fun c1 hAcc => (Bool.and_eq_true_iff.mp hAcc).2) _
      exact Nat.le_trans hImp
        (singlePass_false_batch_accepting_coins_bound B foldBits batch (prover.pass1 c0)
          S hS hBPos hBLen hDom hArity hFault))
    (fun c0 hRej => by
      rw [filter_map_len (fun c1 => (c0, c1))
        (twoPassAccepts foldBits batch prover) (passCoinSpace S foldBits)]
      have hFalsePred : (fun c1 => twoPassAccepts foldBits batch prover (c0, c1)) =
          (fun _ => false) := by
        funext c1
        unfold twoPassAccepts
        dsimp only
        rw [hRej, Bool.false_and]
      rw [hFalsePred, filter_const_false_len]
      exact Nat.le_refl 0)
    (passCoinSpace S foldBits)
  rw [Nat.mul_zero, Nat.add_zero] at hSplit
  rw [Nat.pow_two]
  exact Nat.le_trans hSplit (Nat.mul_le_mul_right K hP0)

set_option exponentiation.threshold 1024 in
/-- **Concrete 8-Wave Barrier Soundness (`rss256_eight_wave_barrier_concrete_bound`, `rss256.rs:76-77`)**:
    At the 8-wave barrier (`8` waves × `24 * 1600 = 38,400` planes = `307,200` planes = `2,400` groups,
    `B = 614,400` 128-bit blocks, `foldBits = [2, 2, 4, 4, 4, 4]`, `R = 6`, `|S| = 2^128`):
    - Single pass (`ROUND1`): `(614400 + 16 + 8 * 6) * 2^108 ≤ 2^128` (`< 2^-108`),
    - Two-pass barrier (`ROUND1` + `ROUND2`): `(614400 + 16 + 8 * 6)^2 * 2^217 ≤ (2^128)^2` (`< 2^-217`)! -/
theorem rss256_eight_wave_barrier_concrete_bound :
    let B := 614400
    let foldBits : List Nat := [2, 2, 4, 4, 4, 4]
    let R := foldBits.length
    (B + 16 + 8 * R = 614464) ∧
    ((B + 16 + 8 * R) * 2 ^ 108 ≤ 2 ^ 128) ∧
    (((B + 16 + 8 * R) ^ 2) * 2 ^ 217 ≤ (2 ^ 128) ^ 2) := by
  decide +kernel

/-- Concrete inhabitedness witness for `rss256_two_pass_product_proof_sound`. -/
def zeroFoldProver : (rs : List Nat) → FoldAndTauProver rs
  | [] => .finalShares ⟨towerZero 7, towerZero 7, towerZero 7, towerZero 7⟩
  | b :: rs => .step (zeroTab b) (fun _ => zeroFoldProver rs)

theorem honestRoundTab_vecZero (m b : Nat) :
    honestRoundTab m b (vecZero (m + b)) (vecZero (m + b))
      (vecZero (m + b)) (vecZero (m + b)) = zeroTab b := by
  induction b with
  | zero =>
    dsimp only [honestRoundTab, btreeTernaryExpand, ttreeMap4, zeroTab, vecCross]
    rw [vecDot_zero, towerAdd_self_zero]
  | succ b ih =>
    dsimp only [vecZero, honestRoundTab, btreeTernaryExpand, ttreeMap4, zeroTab]
    change TTree.branch
      (honestRoundTab m b (vecZero (m + b)) (vecZero (m + b)) (vecZero (m + b)) (vecZero (m + b)))
      (honestRoundTab m b (vecZero (m + b)) (vecZero (m + b)) (vecZero (m + b)) (vecZero (m + b)))
      (honestRoundTab m b
        (vecAdd (vecZero (m + b)) (vecZero (m + b)))
        (vecAdd (vecZero (m + b)) (vecZero (m + b)))
        (vecAdd (vecZero (m + b)) (vecZero (m + b)))
        (vecAdd (vecZero (m + b)) (vecZero (m + b)))) =
      TTree.branch (zeroTab b) (zeroTab b) (zeroTab b)
    rw [vecAdd_zero, ih]

theorem inhabited_rss256_two_pass_product_proof :
    ∃ (B : Nat) (foldBits : List Nat) (batch : RecordedPassBatch foldBits)
      (prover : TwoPassProver foldBits) (S : List Tower128),
      S.Nodup ∧
      1 ≤ B ∧
      batch.gateErrorBlocks.length ≤ B ∧
      B ≤ S.length ∧
      (∀ b ∈ foldBits, b ≤ FOLD_BITS) ∧
      (∃ e ∈ batch.gateErrorBlocks, e ≠ towerZero 7) := by
  let foldBits : List Nat := [2, 2, 4, 4, 4, 4]
  let zVec : Vec128 (tailBits foldBits + TENSOR_BITS) := vecZero (tailBits foldBits + TENSOR_BITS)
  let batch : RecordedPassBatch foldBits :=
    { gateErrorBlocks := [towerOne 7]
      xp := fun _ => zVec
      yq := fun _ => zVec
      xq := fun _ => zVec
      yp := fun _ => zVec
      initialClaim := fun _ => towerOne 7
      masks := fun _ => ⟨towerZero 7, towerZero 7, towerZero 7, towerZero 7⟩
      claim_defect_eq := fun chi => by
        dsimp only [zVec]
        rw [honestRoundTab_vecZero, weightedBoolSum_zeroTab, towerAdd_zero]
        show towerOne 7 = towerAdd 7 (towerOne 7) (towerMul 7 chi (towerZero 7))
        rw [towerMul_zero, towerAdd_zero] }
  let p0 : PassProver foldBits := ⟨fun _ => zeroTab TENSOR_BITS, fun _ _ => zeroFoldProver foldBits⟩
  refine ⟨1, foldBits, batch, ⟨p0, fun _ => p0⟩, [towerZero 7, towerOne 7], ?_,
    Nat.le_refl 1, Nat.le_refl 1, by decide, ?_, ⟨towerOne 7, .head _, by decide⟩⟩
  · decide
  · intro b hb
    rcases hb with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | hNil⟩⟩⟩⟩⟩
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · cases hNil

#verify_inhabited
  Qsag.Rss256ProductProof.rss256_two_pass_product_proof_sound
  Qsag.Rss256ProductProof.inhabited_rss256_two_pass_product_proof

#verify_constructive
  Qsag.Rss256ProductProof.finalMaskedCrossCheck_complete
  Qsag.Rss256ProductProof.finalMaskedOpen_privacy_equiv
  Qsag.Rss256ProductProof.finalMaskedCrossCheck_false_bad_coins_le_two
  Qsag.Rss256ProductProof.singlePass_false_batch_accepting_coins_bound
  Qsag.Rss256ProductProof.rss256_two_pass_product_proof_sound
  Qsag.Rss256ProductProof.rss256_eight_wave_barrier_concrete_bound
  Qsag.Rss256ProductProof.inhabited_rss256_two_pass_product_proof

end Rss256ProductProof
end Qsag
end
