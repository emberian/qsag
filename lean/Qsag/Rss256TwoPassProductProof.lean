module
/-
# Qsag.Rss256TwoPassProductProof — 2-Pass Masked Cross-Product & Barrier Soundness

Constructive (`0 Classical.choice`, `0 sorry`) mechanization of `tau`-masked cross-product opening
(`finalMaskedCrossCheck_complete`, `finalMaskedOpen_privacy_equiv`,
`finalMaskedCrossCheck_false_bad_coins_le_two`), `b`-variate ternary Frobenius-basis root counting
(`nextClaim_false_bad_coins_le`), and adaptive 1-pass (`ROUND1`) + 2-pass (`ROUND1` + `ROUND2`)
`product_proof` barrier soundness (`singlePass_false_batch_accepting_coins_bound`,
`rss256_two_pass_product_proof_sound`, `rss256_eight_wave_barrier_concrete_bound`) matching
`crates/qsag-core/src/rss256.rs:45-81, 2441-2636` (`< 2^-217` at `B = 614,400, R = 6`).
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

/-- `V1` and `V2` masked openings (`rss256.rs:2606-2615`). -/
def finalMaskedOpenV1 (m : FinalMasks) (sh : FinalCrossShares)
    (xfp yfp claim1 tau : Tower128) : Tower128 × Tower128 × Tower128 :=
  (towerAdd 7 m.r1x (towerMul 7 tau xfp), towerAdd 7 m.r1y (towerMul 7 tau yfp),
   towerAdd 7 (towerAdd 7 sh.c0_1 (towerMul 7 tau sh.c1_1)) (towerMul 7 (towerMul 7 tau tau) claim1))

def finalMaskedOpenV2 (m : FinalMasks) (sh : FinalCrossShares)
    (xfq yfq claim2 tau : Tower128) : Tower128 × Tower128 × Tower128 :=
  (towerAdd 7 m.r2x (towerMul 7 tau xfq), towerAdd 7 m.r2y (towerMul 7 tau yfq),
   towerAdd 7 (towerAdd 7 sh.c0_2 (towerMul 7 tau sh.c1_2)) (towerMul 7 (towerMul 7 tau tau) claim2))

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
    dsimp only [lhs, rhs, v1, v2, finalMaskedOpenV1, finalMaskedOpenV2, finalMaskedResidualCoeffs]
    rw [evalCoeffs3_eq]
    simp only [towerAdd_mul_distrib, towerMul_add_distrib]
    rw [show towerMul 7 m.r1x (towerMul 7 tau yfq) = towerMul 7 tau (towerMul 7 m.r1x yfq) by ac_rfl,
        show towerMul 7 (towerMul 7 tau xfp) m.r2y = towerMul 7 tau (towerMul 7 xfp m.r2y) by ac_rfl,
        show towerMul 7 (towerMul 7 tau xfp) (towerMul 7 tau yfq) =
          towerMul 7 tau (towerMul 7 tau (towerMul 7 xfp yfq)) by ac_rfl,
        show towerMul 7 m.r2x (towerMul 7 tau yfp) = towerMul 7 tau (towerMul 7 m.r2x yfp) by ac_rfl,
        show towerMul 7 (towerMul 7 tau xfq) m.r1y = towerMul 7 tau (towerMul 7 xfq m.r1y) by ac_rfl,
        show towerMul 7 (towerMul 7 tau xfq) (towerMul 7 tau yfp) =
          towerMul 7 tau (towerMul 7 tau (towerMul 7 xfq yfp)) by ac_rfl,
        show towerMul 7 (towerMul 7 tau tau) claim1 = towerMul 7 tau (towerMul 7 tau claim1) by ac_rfl,
        show towerMul 7 (towerMul 7 tau tau) claim2 = towerMul 7 tau (towerMul 7 tau claim2) by ac_rfl]
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
  rw [evalCoeffs3_eq, hC0, hC1, hClaim]
  simp only [towerAdd_self_zero, towerMul_zero]

def finalMaskedOpen_privacy_equiv (xf yf tau : Tower128) :
    SimpleEquiv (Tower128 × Tower128) (Tower128 × Tower128) where
  toFun r := (towerAdd 7 r.1 (towerMul 7 tau xf), towerAdd 7 r.2 (towerMul 7 tau yf))
  invFun o := (towerAdd 7 o.1 (towerMul 7 tau xf), towerAdd 7 o.2 (towerMul 7 tau yf))
  left_inv r := by cases r; simp only [towerAdd_assoc, towerAdd_self_zero, towerAdd_zero]
  right_inv o := by cases o; simp only [towerAdd_assoc, towerAdd_self_zero, towerAdd_zero]

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
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq]
    exact finalMaskedCrossCheck_iff_evalCoeffs_zero m sh xfp yfq xfq yfp claim1 claim2 tau
  rw [hPred]
  exact hQ

/-! ## 1b. Inductive `b`-Variate Ternary Round Schwartz–Zippel Root Bound -/

def ternaryBadBound (cardS : Nat) : Nat → Nat
  | 0 => 0
  | b + 1 => ternaryBadBound cardS b * cardS + 2 * cardS ^ b

theorem ternaryBadBound_mul_eq (cardS b : Nat) :
    ternaryBadBound cardS b * cardS = 2 * b * cardS ^ b := by
  induction b with
  | zero => simp only [ternaryBadBound, Nat.zero_mul, Nat.mul_zero]
  | succ b ih =>
    simp only [ternaryBadBound, Nat.add_mul]
    rw [ih, Nat.mul_assoc (2 * b), ← Nat.pow_succ, Nat.mul_assoc 2 (cardS ^ b) cardS,
        ← Nat.pow_succ, ← Nat.add_mul]
    have h2 : 2 * b + 2 = 2 * (b + 1) := by omega
    rw [h2]

theorem ternary_quad_coeffs_nonzero (e0 e1 e2 : Tower128)
    (h : e0 ≠ towerZero 7 ∨ e1 ≠ towerZero 7 ∨ e2 ≠ towerZero 7) :
    e0 ≠ towerZero 7 ∨ towerAdd 7 (towerAdd 7 e0 e1) e2 ≠ towerZero 7 ∨ e2 ≠ towerZero 7 := by
  by_cases h0 : e0 = towerZero 7
  · by_cases h2 : e2 = towerZero 7
    · right; left
      rcases h with h | h | h
      · exact absurd h0 h
      · rw [h0, h2, towerZero_add, towerAdd_zero]; exact h
      · exact absurd h2 h
    · exact Or.inr (Or.inr h2)
  · exact Or.inl h0

theorem ternaryEval_roots_le (S : List Tower128) (hS : S.Nodup) :
    ∀ (b : Nat) (t : TernaryTab b), t ≠ zeroTab b →
      ((challengeTuples S b).filter (fun gs => decide (ternaryEval gs t = towerZero 7))).length ≤
        ternaryBadBound S.length b := by
  intro b
  induction b with
  | zero =>
    intro t hNe
    cases t with | leaf tv =>
    have hTvNe : tv ≠ towerZero 7 := fun h => hNe (by rw [h]; rfl)
    have hF : decide (ternaryEval ChallengeTuple.nil (.leaf tv) = towerZero 7) = false :=
      decide_eq_false_iff_not.mpr hTvNe
    unfold challengeTuples List.filter ternaryBadBound
    rw [hF]
    exact Nat.le_refl 0
  | succ b ih =>
    intro t hNe
    cases t with | branch t0 t1 t2 =>
    have hPick : ∃ tStar : TernaryTab b, tStar ≠ zeroTab b ∧
        ∀ rest : ChallengeTuple b, ternaryEval rest tStar ≠ towerZero 7 →
          ternaryEval rest t0 ≠ towerZero 7 ∨
          ternaryEval rest t1 ≠ towerZero 7 ∨
          ternaryEval rest t2 ≠ towerZero 7 := by
      by_cases ht0 : t0 = zeroTab b
      · by_cases ht1 : t1 = zeroTab b
        · refine ⟨t2, fun ht2 => hNe (by rw [ht0, ht1, ht2]; rfl), fun _ h => Or.inr (Or.inr h)⟩
        · exact ⟨t1, ht1, fun _ h => Or.inr (Or.inl h)⟩
      · exact ⟨t0, ht0, fun _ h => Or.inl h⟩
    rcases hPick with ⟨tStar, htStar, hImp⟩
    unfold challengeTuples ternaryBadBound
    rw [filter_flatMap_len]
    have hSplit := sum_map_le_split
      (fun rest => decide (ternaryEval rest tStar = towerZero 7))
      (fun rest => ((S.map (fun g => ChallengeTuple.cons g rest)).filter
        (fun gs => decide (ternaryEval gs (.branch t0 t1 t2) = towerZero 7))).length)
      S.length 2
      (fun rest _ => by
        rw [filter_map_len (fun g => ChallengeTuple.cons g rest) _ S]
        exact List.length_filter_le _ S)
      (fun rest hGood => by
        rw [filter_map_len (fun g => ChallengeTuple.cons g rest) _ S]
        have hPred : (fun g => decide (ternaryEval (.cons g rest) (.branch t0 t1 t2) = towerZero 7)) =
            (fun g => decide (RoundPoly.evalCoeffs
              [ternaryEval rest t0,
               towerAdd 7 (towerAdd 7 (ternaryEval rest t0) (ternaryEval rest t1)) (ternaryEval rest t2),
               ternaryEval rest t2] g = towerZero 7)) := by
          funext g
          exact decide_eq_decide_of_iff (by rw [ternaryEval_step_eq_evalCoeffs])
        rw [hPred]
        exact quadratic_roots_le_two_tower128 _ _ _ S hS
          (ternary_quad_coeffs_nonzero _ _ _ (hImp rest (decide_eq_false_iff_not.mp hGood))))
      (challengeTuples S b)
    rw [challengeTuples_length, Nat.mul_comm (S.length ^ b) 2] at hSplit
    exact Nat.le_trans hSplit (Nat.add_le_add_right (Nat.mul_le_mul_right S.length (ih tStar htStar)) _)

theorem nextClaim_false_bad_coins_le (b : Nat) (claim : Tower128)
    (w : BoolWeights b) (hw0 : zeroCornerBool w = towerOne 7)
    (sProver sTrue : TernaryTab b) (hFalse : claim ≠ weightedBoolSum w sTrue)
    (S : List Tower128) (hS : S.Nodup) :
    ((challengeTuples S b).filter (fun gs =>
      decide (nextClaim b claim w sProver gs = ternaryEval gs sTrue))).length ≤
      ternaryBadBound S.length b := by
  let d := diffTab (lockZeroCorner claim w sProver) sTrue
  have hdNe : d ≠ zeroTab b := by
    intro hdZ
    have hSum := congrArg (weightedBoolSum w) ((diffTab_eq_zero_iff _ _).mp hdZ)
    rw [lockZeroCorner_weightedBoolSum claim w sProver hw0] at hSum
    exact hFalse hSum
  have hPred : (fun gs => decide (nextClaim b claim w sProver gs = ternaryEval gs sTrue)) =
      (fun gs => decide (ternaryEval gs d = towerZero 7)) := by
    funext gs
    exact decide_eq_decide_of_iff (by
      dsimp only [nextClaim, d]
      rw [ternaryEval_diffTab, towerAdd_eq_zero_iff_eq])
  rw [hPred]
  exact ternaryEval_roots_le S hS b d hdNe

def nextClaimUnlocked (b : Nat) (_claim : Tower128) (_w : BoolWeights b)
    (s : TernaryTab b) (gammas : ChallengeTuple b) : Tower128 :=
  ternaryEval gammas s

theorem tooth_nextClaim_unlocked_s0_forges_all (b : Nat) (S : List Tower128) :
    ∃ (claim : Tower128) (w : BoolWeights b) (sTrue : TernaryTab b),
      zeroCornerBool w = towerOne 7 ∧
      claim ≠ weightedBoolSum w sTrue ∧
      ((challengeTuples S b).filter (fun gs =>
        decide (nextClaimUnlocked b claim w sTrue gs = ternaryEval gs sTrue))).length =
        S.length ^ b := by
  refine ⟨towerOne 7, unitBoolWeights b, zeroTab b, zeroCorner_unitBoolWeights b, ?_, ?_⟩
  · rw [weightedBoolSum_zeroTab]; decide
  · have hAll : ∀ gs ∈ challengeTuples S b,
        decide (nextClaimUnlocked b (towerOne 7) (unitBoolWeights b) (zeroTab b) gs =
          ternaryEval gs (zeroTab b)) = true :=
      fun _ _ => decide_eq_true_iff.mpr rfl
    rw [List.filter_eq_self.mpr hAll, challengeTuples_length]

#tooth_pair
  Qsag.Rss256ProductProof.nextClaim_false_bad_coins_le
  vs
  Qsag.Rss256ProductProof.tooth_nextClaim_unlocked_s0_forges_all

theorem ternaryBadBound_scale_le {L cardS b e : Nat} (h : L ≤ ternaryBadBound cardS b) :
    L * cardS ^ (e + 1) ≤ 2 * b * cardS ^ (b + e) := by
  calc L * cardS ^ (e + 1)
      ≤ ternaryBadBound cardS b * cardS ^ (e + 1) := Nat.mul_le_mul_right _ h
    _ = (ternaryBadBound cardS b * cardS) * cardS ^ e := by
        rw [Nat.pow_succ, Nat.mul_comm (cardS ^ e) cardS, Nat.mul_assoc]
    _ = 2 * b * cardS ^ (b + e) := by
        rw [ternaryBadBound_mul_eq, Nat.mul_assoc (2 * b), ← Nat.pow_add]

theorem scale_pow_add (k cardS b e : Nat) :
    cardS ^ b * (k * cardS ^ e) = k * cardS ^ (b + e) := by
  rw [← Nat.mul_assoc, Nat.mul_comm (cardS ^ b) k, Nat.mul_assoc, ← Nat.pow_add]

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
        List.sum_cons, Nat.add_assoc, ← Nat.pow_add]

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
                     (foldVec (tailBits rs) b gs xq) (foldVec (tailBits rs) b gs yp) :=
          fun hEq => decide_eq_false_iff_not.mp hGood
            (hEq.trans (ternaryEval_honestRoundTab_eq (tailBits rs) b gs xp yq xq yp).symm)
        exact ih (nextClaim b claim (unitBoolWeights b) sProver gs)
          (foldVec (tailBits rs) b gs xp) (foldVec (tailBits rs) b gs yq)
          (foldVec (tailBits rs) b gs xq) (foldVec (tailBits rs) b gs yp)
          masks (nextP gs) hNeNext)
      (challengeTuples S b)
    rw [challengeTuples_length, scale_pow_add] at hSplit
    have hTerm1 := ternaryBadBound_scale_le (e := rs.sum) hRoundBad
    have hTotal : 2 * b * S.length ^ (b + rs.sum) + (2 * rs.sum + 2) * S.length ^ (b + rs.sum) =
        (2 * (b :: rs).sum + 2) * S.length ^ (b :: rs).sum := by
      simp only [List.sum_cons, ← Nat.add_mul]
      have hLin : 2 * b + (2 * rs.sum + 2) = 2 * (b + rs.sum) + 2 := by omega
      rw [hLin]
    exact Nat.le_trans hSplit (hTotal ▸ Nat.add_le_add_right hTerm1 _)

/-- Parametric `tBits` single-pass coin vector, prover, and batch (`tBits = TENSOR_BITS = 7`). -/
abbrev PassCoinsG (tBits : Nat) (foldBits : List Nat) :=
  Tower128 × ChallengeTuple tBits × FoldAndTauCoins foldBits

abbrev PassCoins (foldBits : List Nat) := PassCoinsG TENSOR_BITS foldBits

def passCoinSpaceG (tBits : Nat) (S : List Tower128) (foldBits : List Nat) :
    List (PassCoinsG tBits foldBits) :=
  S.flatMap (fun chi =>
    (challengeTuples S tBits).flatMap (fun gTensor =>
      (foldAndTauCoinSpace S foldBits).map (fun ft => (chi, gTensor, ft))))

abbrev passCoinSpace (S : List Tower128) (foldBits : List Nat) : List (PassCoins foldBits) :=
  passCoinSpaceG TENSOR_BITS S foldBits

theorem passCoinSpaceG_length (tBits : Nat) (S : List Tower128) (foldBits : List Nat) :
    (passCoinSpaceG tBits S foldBits).length = S.length ^ (tBits + foldBits.sum + 2) := by
  unfold passCoinSpaceG
  have hInner : ∀ chi : Tower128,
      ((challengeTuples S tBits).flatMap (fun gTensor =>
        (foldAndTauCoinSpace S foldBits).map (fun ft => (chi, gTensor, ft)))).length =
      S.length ^ (tBits + foldBits.sum + 1) := by
    intro chi
    rw [flatMap_map_len, challengeTuples_length, foldAndTauCoinSpace_length,
        ← Nat.pow_add, Nat.add_assoc]
  have hOuter : ∀ xs : List Tower128,
      (xs.flatMap (fun chi =>
        (challengeTuples S tBits).flatMap (fun gTensor =>
          (foldAndTauCoinSpace S foldBits).map (fun ft => (chi, gTensor, ft))))).length =
      xs.length * S.length ^ (tBits + foldBits.sum + 1) := by
    intro xs
    induction xs with
    | nil => simp only [List.flatMap_nil, List.length_nil, Nat.zero_mul]
    | cons x xs ih =>
      simp only [List.flatMap_cons, List.length_append, hInner x, ih,
        List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm]
  rw [hOuter S, Nat.mul_comm, ← Nat.pow_succ]

theorem passCoinSpace_length (S : List Tower128) (foldBits : List Nat) :
    (passCoinSpace S foldBits).length = S.length ^ (TENSOR_BITS + foldBits.sum + 2) :=
  passCoinSpaceG_length TENSOR_BITS S foldBits

structure PassProverG (tBits : Nat) (foldBits : List Nat) where
  tensorTab : Tower128 → TernaryTab tBits
  afterTensor : Tower128 → ChallengeTuple tBits → FoldAndTauProver foldBits

abbrev PassProver (foldBits : List Nat) := PassProverG TENSOR_BITS foldBits

structure RecordedPassBatchG (tBits : Nat) (foldBits : List Nat) where
  gateErrorBlocks : List Tower128
  xp : Tower128 → Vec128 (tailBits foldBits + tBits)
  yq : Tower128 → Vec128 (tailBits foldBits + tBits)
  xq : Tower128 → Vec128 (tailBits foldBits + tBits)
  yp : Tower128 → Vec128 (tailBits foldBits + tBits)
  initialClaim : Tower128 → Tower128
  masks : Tower128 → FinalMasks
  claim_defect_eq : ∀ chi : Tower128,
    towerAdd 7 (initialClaim chi)
      (weightedBoolSum (chiBoolWeights chi tBits)
        (honestRoundTab (tailBits foldBits) tBits (xp chi) (yq chi) (xq chi) (yp chi))) =
    RoundPoly.evalCoeffs gateErrorBlocks chi

abbrev RecordedPassBatch (foldBits : List Nat) := RecordedPassBatchG TENSOR_BITS foldBits

def singlePassAcceptsG (tBits : Nat) (foldBits : List Nat) (batch : RecordedPassBatchG tBits foldBits)
    (prover : PassProverG tBits foldBits) (coins : PassCoinsG tBits foldBits) : Bool :=
  let (chi, gTensor, ftCoins) := coins
  foldAndTauAccepts foldBits
    (nextClaim tBits (batch.initialClaim chi)
      (chiBoolWeights chi tBits) (prover.tensorTab chi) gTensor)
    (foldVec (tailBits foldBits) tBits gTensor (batch.xp chi))
    (foldVec (tailBits foldBits) tBits gTensor (batch.yq chi))
    (foldVec (tailBits foldBits) tBits gTensor (batch.xq chi))
    (foldVec (tailBits foldBits) tBits gTensor (batch.yp chi))
    (batch.masks chi) (prover.afterTensor chi gTensor) ftCoins

@[expose] abbrev singlePassAccepts (foldBits : List Nat) (batch : RecordedPassBatch foldBits)
    (prover : PassProver foldBits) (coins : PassCoins foldBits) : Bool :=
  singlePassAcceptsG TENSOR_BITS foldBits batch prover coins

theorem foldBits_sum_le_four_mul (rs : List Nat) (h : ∀ b ∈ rs, b ≤ FOLD_BITS) :
    2 * rs.sum ≤ 8 * rs.length := by
  induction rs with
  | nil => exact Nat.le_refl 0
  | cons b rs ih =>
    have hb : b ≤ 4 := h b (.head _)
    have hSub := ih (fun x hx => h x (.tail _ hx))
    simp only [List.sum_cons, List.length_cons]; omega

theorem singlePassG_false_batch_accepting_coins_bound
    (tBits B : Nat) (foldBits : List Nat) (batch : RecordedPassBatchG tBits foldBits)
    (prover : PassProverG tBits foldBits) (S : List Tower128) (hS : S.Nodup)
    (hBPos : 1 ≤ B) (hBLen : batch.gateErrorBlocks.length ≤ B) (hDom : B ≤ S.length)
    (hArity : ∀ b ∈ foldBits, b ≤ FOLD_BITS)
    (hFault : ∃ e ∈ batch.gateErrorBlocks, e ≠ towerZero 7) :
    ((passCoinSpaceG tBits S foldBits).filter (singlePassAcceptsG tBits foldBits batch prover)).length ≤
      (B + (2 * tBits + 2) + 8 * foldBits.length) * S.length ^ (tBits + foldBits.sum + 1) := by
  let E := tBits + foldBits.sum + 1
  have hInnerBound : ∀ chi : Tower128,
      RoundPoly.evalCoeffs batch.gateErrorBlocks chi ≠ towerZero 7 →
      (((challengeTuples S tBits).flatMap (fun gTensor =>
        (foldAndTauCoinSpace S foldBits).map (fun ft => (chi, gTensor, ft)))).filter
        (singlePassAcceptsG tBits foldBits batch prover)).length ≤
      (2 * tBits + (2 * foldBits.sum + 2)) * S.length ^ (tBits + foldBits.sum) := by
    intro chi hChiNz
    rw [filter_flatMap_len]
    let sTrue := honestRoundTab (tailBits foldBits) tBits
      (batch.xp chi) (batch.yq chi) (batch.xq chi) (batch.yp chi)
    have hClaimFalse : batch.initialClaim chi ≠
        weightedBoolSum (chiBoolWeights chi tBits) sTrue := by
      intro hEq
      have hDef := batch.claim_defect_eq chi
      dsimp only [sTrue] at hEq
      rw [hEq, towerAdd_self_zero] at hDef
      exact hChiNz hDef.symm
    have hTensorBad := nextClaim_false_bad_coins_le tBits (batch.initialClaim chi)
      (chiBoolWeights chi tBits) (zeroCorner_chiBoolWeights chi tBits)
      (prover.tensorTab chi) sTrue hClaimFalse S hS
    have hSplitT := sum_map_le_split
      (fun gTensor => decide (nextClaim tBits (batch.initialClaim chi)
        (chiBoolWeights chi tBits) (prover.tensorTab chi) gTensor =
        ternaryEval gTensor sTrue))
      (fun gTensor => (((foldAndTauCoinSpace S foldBits).map (fun ft => (chi, gTensor, ft))).filter
        (singlePassAcceptsG tBits foldBits batch prover)).length)
      (S.length ^ (foldBits.sum + 1)) ((2 * foldBits.sum + 2) * S.length ^ foldBits.sum)
      (fun gTensor _ => by
        rw [filter_map_len (fun ft => (chi, gTensor, ft))
          (singlePassAcceptsG tBits foldBits batch prover) (foldAndTauCoinSpace S foldBits),
          ← foldAndTauCoinSpace_length S foldBits]
        exact List.length_filter_le _ _)
      (fun gTensor hGood => by
        rw [filter_map_len (fun ft => (chi, gTensor, ft))
          (singlePassAcceptsG tBits foldBits batch prover) (foldAndTauCoinSpace S foldBits)]
        have hNeNext : nextClaim tBits (batch.initialClaim chi)
            (chiBoolWeights chi tBits) (prover.tensorTab chi) gTensor ≠
            vecCross
              (foldVec (tailBits foldBits) tBits gTensor (batch.xp chi))
              (foldVec (tailBits foldBits) tBits gTensor (batch.yq chi))
              (foldVec (tailBits foldBits) tBits gTensor (batch.xq chi))
              (foldVec (tailBits foldBits) tBits gTensor (batch.yp chi)) :=
          fun hEq => decide_eq_false_iff_not.mp hGood
            (hEq.trans (ternaryEval_honestRoundTab_eq (tailBits foldBits) tBits gTensor
              (batch.xp chi) (batch.yq chi) (batch.xq chi) (batch.yp chi)).symm)
        exact foldAndTau_false_claim_bad_coins_le S hS foldBits _ _ _ _ _
          (batch.masks chi) (prover.afterTensor chi gTensor) hNeNext)
      (challengeTuples S tBits)
    rw [challengeTuples_length, scale_pow_add] at hSplitT
    have hT1 := ternaryBadBound_scale_le (e := foldBits.sum) hTensorBad
    have hCombine : 2 * tBits * S.length ^ (tBits + foldBits.sum) +
        (2 * foldBits.sum + 2) * S.length ^ (tBits + foldBits.sum) =
        (2 * tBits + (2 * foldBits.sum + 2)) * S.length ^ (tBits + foldBits.sum) :=
      (Nat.add_mul _ _ _).symm
    exact Nat.le_trans hSplitT (hCombine ▸ Nat.add_le_add_right hT1 _)
  unfold passCoinSpaceG
  rw [filter_flatMap_len]
  have hChiBad := passBatching_false_bad_coins_le B batch.gateErrorBlocks S hS hBPos hBLen hDom hFault
  have hInnerFullLen : ∀ chi : Tower128,
      ((challengeTuples S tBits).flatMap (fun gTensor =>
        (foldAndTauCoinSpace S foldBits).map (fun ft => (chi, gTensor, ft)))).length = S.length ^ E := by
    intro chi
    rw [flatMap_map_len, challengeTuples_length, foldAndTauCoinSpace_length,
        ← Nat.pow_add, ← Nat.add_assoc]
  have hSplitChi := sum_map_le_split
    (fun chi => decide (RoundPoly.evalCoeffs batch.gateErrorBlocks chi = towerZero 7))
    (fun chi => (((challengeTuples S tBits).flatMap (fun gTensor =>
      (foldAndTauCoinSpace S foldBits).map (fun ft => (chi, gTensor, ft)))).filter
      (singlePassAcceptsG tBits foldBits batch prover)).length)
    (S.length ^ E) ((2 * tBits + (2 * foldBits.sum + 2)) * S.length ^ (tBits + foldBits.sum))
    (fun chi _ => by rw [← hInnerFullLen chi]; exact List.length_filter_le _ _)
    (fun chi hGood => hInnerBound chi (decide_eq_false_iff_not.mp hGood))
    S
  have hC1 : (S.filter (fun chi =>
      decide (RoundPoly.evalCoeffs batch.gateErrorBlocks chi = towerZero 7))).length * S.length ^ E ≤
      B * S.length ^ E := Nat.mul_le_mul_right (S.length ^ E) hChiBad
  have hC2 : S.length * ((2 * tBits + (2 * foldBits.sum + 2)) * S.length ^ (tBits + foldBits.sum)) ≤
      ((2 * tBits + 2) + 8 * foldBits.length) * S.length ^ E := by
    have hSwap : S.length * ((2 * tBits + (2 * foldBits.sum + 2)) * S.length ^ (tBits + foldBits.sum)) =
        (2 * tBits + (2 * foldBits.sum + 2)) * S.length ^ E := by
      dsimp only [E]
      rw [← Nat.mul_assoc, Nat.mul_comm S.length, Nat.mul_assoc, Nat.mul_comm S.length, ← Nat.pow_succ]
    rw [hSwap]
    have hCoef : 2 * tBits + (2 * foldBits.sum + 2) ≤ (2 * tBits + 2) + 8 * foldBits.length := by
      have hF := foldBits_sum_le_four_mul foldBits hArity; omega
    exact Nat.mul_le_mul_right (S.length ^ E) hCoef
  have hAddE : B * S.length ^ E + ((2 * tBits + 2) + 8 * foldBits.length) * S.length ^ E =
      (B + (2 * tBits + 2) + 8 * foldBits.length) * S.length ^ E := by
    rw [← Nat.add_mul, ← Nat.add_assoc]
  exact Nat.le_trans hSplitChi (hAddE ▸ Nat.add_le_add hC1 hC2)

/-- **Single-Pass (`ROUND1`) Adaptive Soundness (`singlePass_false_batch_accepting_coins_bound`)**
    (`rss256.rs:73-75`). -/
theorem singlePass_false_batch_accepting_coins_bound
    (B : Nat) (foldBits : List Nat) (batch : RecordedPassBatch foldBits)
    (prover : PassProver foldBits) (S : List Tower128) (hS : S.Nodup)
    (hBPos : 1 ≤ B) (hBLen : batch.gateErrorBlocks.length ≤ B) (hDom : B ≤ S.length)
    (hArity : ∀ b ∈ foldBits, b ≤ FOLD_BITS)
    (hFault : ∃ e ∈ batch.gateErrorBlocks, e ≠ towerZero 7) :
    ((passCoinSpace S foldBits).filter (singlePassAccepts foldBits batch prover)).length ≤
      (B + 16 + 8 * foldBits.length) * S.length ^ (TENSOR_BITS + foldBits.sum + 1) :=
  singlePassG_false_batch_accepting_coins_bound TENSOR_BITS B foldBits batch prover
    S hS hBPos hBLen hDom hArity hFault

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
    rw [vecDot_zero (m + 0), towerAdd_self_zero]
  | succ b ih =>
    dsimp only [vecZero, honestRoundTab, btreeTernaryExpand, ttreeMap4, zeroTab]
    change TTree.branch
      (honestRoundTab m b (vecZero (m + b)) (vecZero (m + b)) (vecZero (m + b)) (vecZero (m + b)))
      (honestRoundTab m b (vecZero (m + b)) (vecZero (m + b)) (vecZero (m + b)) (vecZero (m + b)))
      (honestRoundTab m b
        (vecAdd (vecZero (m + b)) (vecZero (m + b))) (vecAdd (vecZero (m + b)) (vecZero (m + b)))
        (vecAdd (vecZero (m + b)) (vecZero (m + b))) (vecAdd (vecZero (m + b)) (vecZero (m + b)))) =
      TTree.branch (zeroTab b) (zeroTab b) (zeroTab b)
    rw [vecAdd_zero, ih]

theorem inhabited_rss256_two_pass_product_proof :
    ∃ (B : Nat) (foldBits : List Nat) (batch : RecordedPassBatch foldBits)
      (_prover : TwoPassProver foldBits) (S : List Tower128),
      S.Nodup ∧ 1 ≤ B ∧ batch.gateErrorBlocks.length ≤ B ∧ B ≤ S.length ∧
      (∀ b ∈ foldBits, b ≤ FOLD_BITS) ∧ (∃ e ∈ batch.gateErrorBlocks, e ≠ towerZero 7) := by
  let foldBits : List Nat := []
  let zVec : Vec128 (tailBits foldBits + TENSOR_BITS) := vecZero (tailBits foldBits + TENSOR_BITS)
  let batch : RecordedPassBatch foldBits :=
    { gateErrorBlocks := [towerOne 7], xp := fun _ => zVec, yq := fun _ => zVec,
      xq := fun _ => zVec, yp := fun _ => zVec, initialClaim := fun _ => towerOne 7,
      masks := fun _ => ⟨towerZero 7, towerZero 7, towerZero 7, towerZero 7⟩,
      claim_defect_eq := fun chi => by
        rw [honestRoundTab_vecZero (tailBits foldBits) TENSOR_BITS,
            weightedBoolSum_zeroTab, towerAdd_zero]
        show towerOne 7 = towerAdd 7 (towerOne 7) (towerMul 7 chi (towerZero 7))
        rw [towerMul_zero, towerAdd_zero] }
  let p0 : PassProver foldBits := ⟨fun _ => zeroTab TENSOR_BITS, fun _ _ => zeroFoldProver foldBits⟩
  refine ⟨1, foldBits, batch, ⟨p0, fun _ => p0⟩, [towerZero 7, towerOne 7], ?_,
    Nat.le_refl 1, Nat.le_refl 1, by decide, by decide, ⟨towerOne 7, .head _, by decide⟩⟩
  decide

#verify_inhabited
  Qsag.Rss256ProductProof.rss256_two_pass_product_proof_sound
  Qsag.Rss256ProductProof.inhabited_rss256_two_pass_product_proof

#verify_constructive
  Qsag.Rss256ProductProof.finalMaskedCrossCheck_complete
  Qsag.Rss256ProductProof.finalMaskedOpen_privacy_equiv
  Qsag.Rss256ProductProof.finalMaskedCrossCheck_false_bad_coins_le_two
  Qsag.Rss256ProductProof.ternaryBadBound_mul_eq
  Qsag.Rss256ProductProof.ternaryEval_roots_le
  Qsag.Rss256ProductProof.nextClaim_false_bad_coins_le
  Qsag.Rss256ProductProof.tooth_nextClaim_unlocked_s0_forges_all
  Qsag.Rss256ProductProof.singlePass_false_batch_accepting_coins_bound
  Qsag.Rss256ProductProof.rss256_two_pass_product_proof_sound
  Qsag.Rss256ProductProof.rss256_eight_wave_barrier_concrete_bound
  Qsag.Rss256ProductProof.inhabited_rss256_two_pass_product_proof

end Rss256ProductProof
end Qsag
end
