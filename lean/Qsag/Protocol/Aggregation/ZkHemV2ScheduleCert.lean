module
/-
# Qsag.Protocol.Aggregation.ZkHemV2ScheduleCert — Production `zk-Hem v2` + DKT26 Schedule Certificate & `< 2^{-128}` QROM Soundness

This module models the E9 Rust overlay at `crates/qsag-agg/src/zk_hem/v2/`.
The live checkout uses an earlier query table.
1. Re-exports the 9-triple Toom-3 `𝔽_{p^5} mod (u^5 - 3)` identity (`toom3MulFp5_eq_quinticMul`).
2. Proves the DKT26 (`ePrint 2026/2056` Thm 5.12) mask-line bad-challenge bound (`≤ 1` per false
   pair on `ZkHemV2.maskLine` / `maskLineVec`), `dkt26_threshold_inside_johnson` via
   `gsDecodeList_length_le_johnson`, and `tooth_bcgm25_deg7_mask_line_fails_at_28`.
3. Constructs unconditional `zkHemV2QuinticCert : WhirScheduleCert zkHemV2QuinticEnv zkHemV2QuinticSched 400`
   over `QuinticGoldilocks` (`p^5`) with 5 OOD points and 400-bit digests.
4. Formalizes `zkHemV2ProdSched` (`log_cells ∈ [16, 28]`, `267/266` Stage-0 queries, 400-bit digests,
   32B `tree_nonce`), proving `johnsonOk = true` and `< 2^{-128}` composed succinct QROM + Merkle
   soundness given the schedule certificate, consistent roots and collision-event bound across `logCells ∈ [16, 28]` and `Q ≤ 2^{64}` (`#tooth_pair` vs `v1` & `𝔽_p`).
-/

public import Qsag.Math.QuinticToom3
public import Qsag.Protocol.Aggregation.ClosedWhirSchedule
public import Qsag.Protocol.Aggregation.ZkHemV2
public import Qsag.Protocol.Aggregation.QromSaltedMerkleStateRestoration
import Qsag.Math.Tactic.CommRing
import Qsag.Coding.GuruswamiSudan
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.ZkHemV2Cert

open Qsag Qsag.ClosedFs Qsag.ClosedWhir

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 100000

local infixl:65 " +ᵍ " => CommRingOps.add
local infixl:65 " -ᵍ " => CommRingOps.sub
local infixl:70 " *ᵍ " => CommRingOps.mul

theorem ratBound_lt_of_le_of_lt {a b c : RatBound}
    (hab : RatBound.le a b) (hbc : RatBound.lt b c) : RatBound.lt a c := by
  have h1 : a.num * b.den * c.den ≤ b.num * a.den * c.den := Nat.mul_le_mul_right c.den hab
  have h2 : a.den * (b.num * c.den) < a.den * (c.num * b.den) := by
    rw [Nat.mul_comm a.den _, Nat.mul_comm a.den _]
    exact nat_mul_lt_mul_right' hbc a.h_pos
  have e1 : b.num * a.den * c.den = a.den * (b.num * c.den) := by
    simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have e2 : a.den * (c.num * b.den) = a.den * c.num * b.den := by
    simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have e0 : a.num * b.den * c.den = a.num * c.den * b.den := by
    simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have h3 : a.num * c.den * b.den < a.den * c.num * b.den := by
    rw [← e0, ← e2]; rw [e1] at h1; exact Nat.lt_of_le_of_lt h1 h2
  have h4 := nat_lt_of_mul_lt_mul_right' h3
  rwa [Nat.mul_comm a.den c.num] at h4

/-! ## §1. 9-Triple Toom-3 `𝔽_{p^5} mod (u^5 - 3)` Re-Exports (`Qsag.Math.QuinticToom3`) -/

abbrev toom3MulFp5_eq_quinticMul := @Qsag.toom3MulFp5_eq_quinticMul
abbrev toom3Eval9_add := @Qsag.toom3Eval9_add
abbrev tooth_toom3_wrong_reduction_ne_quinticMul := @Qsag.tooth_toom3_wrong_reduction_ne_quinticMul

/-! ## §2. Algebraic DKT26 (`ePrint 2026/2056` Thm 5.12) Mask-Line Degree & Correlated-Pair Soundness -/

abbrev quinticGoldilocksCard : Nat := goldilocksPrime ^ 5

theorem quinticGoldilocksCard_pos : 0 < quinticGoldilocksCard := by decide +kernel

/-- Vectorized `ZkHemV2.maskLine` (`g_β = c0 + β · c1`) over coefficient/evaluation lists. -/
@[expose] def maskLineVec (β : QuinticGoldilocks) (c0 c1 : List QuinticGoldilocks) :
    List QuinticGoldilocks :=
  List.zipWith (fun a b => ZkHemV2.maskLine β (fun _ : Unit => a) (fun _ : Unit => b) ()) c0 c1

/-- Linearity of `ringDot` along `maskLineVec`:
    `ringDot (maskLineVec β c0 c1) vs = ringDot c0 vs + β · ringDot c1 vs`. -/
theorem ringDot_maskLine :
    ∀ (β : QuinticGoldilocks) (c0 c1 vs : List QuinticGoldilocks),
      c0.length = c1.length →
      ringDot (maskLineVec β c0 c1) vs = ringDot c0 vs +ᵍ β *ᵍ ringDot c1 vs
  | _, [], [], vs, _ => by
    dsimp only [maskLineVec, List.zipWith]
    rw [ringDot_eq, dotVec_nil_left]
    constructive_ring
  | _, _ :: _, [], _, hLen => nomatch hLen
  | _, [], _ :: _, _, hLen => nomatch hLen
  | _, _ :: _, _ :: _, [], _ => by
    dsimp only [maskLineVec, List.zipWith]
    rw [ringDot_nil_right, ringDot_nil_right, ringDot_nil_right]
    constructive_ring
  | β, a :: as, b :: bs, v :: vs, hLen => by
    dsimp only [maskLineVec, ZkHemV2.maskLine, List.zipWith]
    rw [ringDot_cons_cons, ringDot_cons_cons, ringDot_cons_cons]
    have ih := ringDot_maskLine β as bs vs (Nat.succ.inj hLen)
    dsimp only [maskLineVec, ZkHemV2.maskLine] at ih
    rw [ih]
    constructive_ring

private theorem filter_eq_nil_local {α : Type} (p : α → Bool) :
    ∀ (l : List α), (∀ a ∈ l, p a = false) → l.filter p = []
  | [], _ => rfl
  | a :: as, h => by
    rw [List.filter_cons, h a List.mem_cons_self]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact filter_eq_nil_local p as (fun b hb => h b (List.mem_cons_of_mem _ hb))

private theorem nodup_filter_eq_le_one {α : Type} [DecidableEq α] (w : α) :
    ∀ (pool : List α), pool.Nodup → (pool.filter (fun x => decide (x = w))).length ≤ 1
  | [], _ => Nat.zero_le 1
  | x :: xs, hNd => by
    obtain ⟨hxNotMem, hNdXs⟩ := List.nodup_cons.mp hNd
    if hEq : x = w then
      subst hEq
      have hRest : xs.filter (fun y => decide (y = x)) = [] :=
        filter_eq_nil_local _ xs (fun y hy => decide_eq_false (fun hyx => hxNotMem (hyx ▸ hy)))
      simp only [List.filter_cons, decide_true, ↓reduceIte, hRest, List.length_singleton]
      exact Nat.le_refl 1
    else
      simp only [List.filter_cons, decide_eq_false hEq, Bool.false_eq_true, ↓reduceIte]
      exact nodup_filter_eq_le_one w xs hNdXs

private theorem linear_claim_bad_le_one
    (v0 v1 σ μ : QuinticGoldilocks) (pool : List QuinticGoldilocks)
    (hPool : pool.Nodup) (hFalse : v0 ≠ σ ∨ v1 ≠ μ) :
    (pool.filter (fun β => decide (v0 +ᵍ β *ᵍ v1 = σ +ᵍ β *ᵍ μ))).length ≤ 1 := by
  let d1 := v1 -ᵍ μ
  if hd1 : d1 = CommRingOps.zero then
    have hv1 : v1 = μ := LawfulCommRing.sub_eq_zero_iff.mp hd1
    have hv0 : v0 ≠ σ := by
      cases hFalse with
      | inl h0 => exact h0
      | inr h1 => exact absurd hv1 h1
    have hEmpty : pool.filter (fun β => decide (v0 +ᵍ β *ᵍ v1 = σ +ᵍ β *ᵍ μ)) = [] := by
      refine filter_eq_nil_local _ pool (fun β _ => decide_eq_false (fun hEq => ?_))
      rw [hv1] at hEq
      exact hv0 (calc v0 = (v0 +ᵍ β *ᵍ μ) -ᵍ β *ᵍ μ := by constructive_ring
        _ = (σ +ᵍ β *ᵍ μ) -ᵍ β *ᵍ μ := by rw [hEq]
        _ = σ := by constructive_ring)
    rw [hEmpty]; exact Nat.zero_le 1
  else
    let root := (σ -ᵍ v0) *ᵍ LawfulField.inv d1
    have hSub : (pool.filter (fun β => decide (v0 +ᵍ β *ᵍ v1 = σ +ᵍ β *ᵍ μ))).length ≤
        (pool.filter (fun β => decide (β = root))).length := by
      clear hPool
      induction pool with
      | nil => exact Nat.le_refl 0
      | cons β rest ih =>
        if hHit : v0 +ᵍ β *ᵍ v1 = σ +ᵍ β *ᵍ μ then
          have hRoot : β = root := by
            have hLin : β *ᵍ d1 = σ -ᵍ v0 := by
              dsimp only [d1]
              calc β *ᵍ (v1 -ᵍ μ) = (v0 +ᵍ β *ᵍ v1) -ᵍ v0 -ᵍ β *ᵍ μ := by constructive_ring
                _ = (σ +ᵍ β *ᵍ μ) -ᵍ v0 -ᵍ β *ᵍ μ := by rw [hHit]
                _ = σ -ᵍ v0 := by constructive_ring
            calc β = β *ᵍ (d1 *ᵍ LawfulField.inv d1) := by
                  rw [LawfulField.mul_inv_cancel hd1, LawfulCommRing.mul_one]
              _ = (β *ᵍ d1) *ᵍ LawfulField.inv d1 := (LawfulCommRing.mul_assoc _ _ _).symm
              _ = root := by rw [hLin]
          simp only [List.filter_cons, decide_eq_true hHit, decide_eq_true hRoot, ↓reduceIte,
            List.length_cons]
          exact Nat.succ_le_succ ih
        else
          simp only [List.filter_cons, decide_eq_false hHit, Bool.false_eq_true, ↓reduceIte]
          cases decide (β = root) <;> simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]
          · exact ih
          · exact Nat.le_trans ih (Nat.le_succ _)
    exact Nat.le_trans hSub (nodup_filter_eq_le_one root pool hPool)

/-- Mask-line correlated-pair bad-challenge bound (`≤ 1` bad `β ∈ pool` on `ZkHemV2.maskLine`). -/
theorem v2_maskLine_linForm_false_pair_bad_challenges_le_one {ι : Type}
    (ℓ : ZkHem.LinForm ι QuinticGoldilocks) (P R : ι → QuinticGoldilocks)
    (pool : List QuinticGoldilocks) (σ μ : QuinticGoldilocks)
    (hPool : pool.Nodup) (hFalse : ℓ.app P ≠ σ ∨ ℓ.app R ≠ μ) :
    (pool.filter (fun β =>
      decide (ℓ.app (ZkHemV2.maskLine β P R) = σ +ᵍ β *ᵍ μ))).length ≤ 1 := by
  have hRew : (fun β => decide (ℓ.app (ZkHemV2.maskLine β P R) = σ +ᵍ β *ᵍ μ)) =
      (fun β => decide (ℓ.app P +ᵍ β *ᵍ ℓ.app R = σ +ᵍ β *ᵍ μ)) := by
    funext β; rw [ZkHemV2.maskLine_claim]
  rw [hRew]
  exact linear_claim_bad_le_one (ℓ.app P) (ℓ.app R) σ μ pool hPool hFalse

/-- Mask-line correlated-pair bad-challenge bound (`≤ 1` bad `β ∈ pool` on `maskLineVec`). -/
theorem v2_maskLine_false_pair_bad_challenges_le_one
    (c0 c1 vs pool : List QuinticGoldilocks) (σ μ : QuinticGoldilocks)
    (hLen : c0.length = c1.length) (hPool : pool.Nodup)
    (hFalse : ringDot c0 vs ≠ σ ∨ ringDot c1 vs ≠ μ) :
    (pool.filter (fun β =>
      decide (ringDot (maskLineVec β c0 c1) vs = σ +ᵍ β *ᵍ μ))).length ≤ 1 := by
  have hRew : (fun β => decide (ringDot (maskLineVec β c0 c1) vs = σ +ᵍ β *ᵍ μ)) =
      (fun β => decide (ringDot c0 vs +ᵍ β *ᵍ ringDot c1 vs = σ +ᵍ β *ᵍ μ)) := by
    funext β; rw [ringDot_maskLine β c0 c1 vs hLen]
  rw [hRew]
  exact linear_claim_bad_le_one (ringDot c0 vs) (ringDot c1 vs) σ μ pool hPool hFalse

private theorem filter_any_length_le :
    ∀ {α β : Type} (cands : List α) (pool : List β) (pred : α → β → Bool),
      (∀ c ∈ cands, (pool.filter (pred c)).length ≤ 1) →
      (pool.filter (fun x => cands.any (fun c => pred c x))).length ≤ cands.length
  | _, _, [], pool, _, _ => by
    have hNil : pool.filter (fun _ => false) = [] := filter_eq_nil_local _ pool (fun _ _ => rfl)
    dsimp only [List.any_nil]; rw [hNil]; exact Nat.le_refl 0
  | _, _, c :: cs, pool, pred, hEach => by
    have hSub : ∀ l : List _,
        (l.filter (fun x => pred c x || cs.any (fun d => pred d x))).length ≤
        (l.filter (pred c)).length + (l.filter (fun x => cs.any (fun d => pred d x))).length := by
      intro l
      induction l with
      | nil => exact Nat.le_refl 0
      | cons x xs ih =>
        rw [List.filter_cons, List.filter_cons, List.filter_cons]
        cases pred c x <;> cases cs.any (fun d => pred d x) <;>
          simp only [Bool.true_or, Bool.false_or, Bool.false_eq_true, ↓reduceIte, List.length_cons] <;>
          omega
    have h1 := hEach c List.mem_cons_self
    have h2 := filter_any_length_le cs pool pred (fun d hd => hEach d (List.mem_cons_of_mem _ hd))
    have hTot := hSub pool
    dsimp only [List.any_cons, List.length_cons]
    omega

/-- Summing over any list `cands` of false correlated candidate pairs (`cands.length ≤ pairs`),
    at most `pairs` challenges in `pool` satisfy the linear mask-line claim for any `p ∈ cands`. -/
theorem v2_maskLine_claim_bad_count_le_pairs
    (cands : List (List QuinticGoldilocks × List QuinticGoldilocks))
    (vs pool : List QuinticGoldilocks) (σ μ : QuinticGoldilocks) (pairs : Nat)
    (hPool : pool.Nodup) (hCandsLen : cands.length ≤ pairs)
    (hFalse : ∀ p ∈ cands, p.1.length = p.2.length ∧ (ringDot p.1 vs ≠ σ ∨ ringDot p.2 vs ≠ μ)) :
    (pool.filter (fun β => cands.any (fun p =>
      decide (ringDot (maskLineVec β p.1 p.2) vs = σ +ᵍ β *ᵍ μ)))).length ≤ pairs :=
  Nat.le_trans
    (filter_any_length_le cands pool _ (fun p hp =>
      v2_maskLine_false_pair_bad_challenges_le_one p.1 p.2 vs pool σ μ
        (hFalse p hp).1 hPool (hFalse p hp).2))
    hCandsLen

/-- DKT26 (`ePrint 2026/2056` Thm 5.12) threshold implies `n · D < A²` and `gsDecodeList` Johnson bound. -/
theorem dkt26_threshold_inside_johnson {n D m A : Nat}
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hAn : A ≤ n)
    (hCov : (2 * m + 1) * (2 * m + 1) * n * (D + 1) ≤ (2 * m * A) * (2 * m * A)) :
    n * D < A * A ∧
    ∀ (dom : List QuinticGoldilocks) (word : QuinticGoldilocks → QuinticGoldilocks),
      dom.Nodup → dom.length = n →
      (gsDecodeList D A dom word).length ≤ JohnsonBound.johnsonBound n A D := by
  have hSqLt : (2 * m) * (2 * m) < (2 * m + 1) * (2 * m + 1) := by
    have : (2 * m + 1) * (2 * m + 1) = (2 * m) * (2 * m) + (4 * m + 1) := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
    omega
  have hStrict : (2 * m) * (2 * m) * (n * (D + 1)) < (2 * m + 1) * (2 * m + 1) * n * (D + 1) := by
    rw [Nat.mul_assoc ((2 * m + 1) * (2 * m + 1)) n (D + 1)]
    exact nat_mul_lt_mul_right' hSqLt (Nat.mul_pos (by omega) (Nat.succ_pos D))
  have hRhsEq : (2 * m * A) * (2 * m * A) = (2 * m) * (2 * m) * (A * A) := by
    simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have hND1 : n * (D + 1) < A * A :=
    nat_lt_of_mul_lt_mul_left' (by rw [← hRhsEq]; exact Nat.lt_of_lt_of_le hStrict hCov)
  have hND : n * D < A * A := Nat.lt_of_le_of_lt (Nat.mul_le_mul_left n (Nat.le_succ D)) hND1
  refine ⟨hND, fun dom word hNd hLen => ?_⟩
  have hdA : D + 1 ≤ A := by
    rcases Nat.lt_or_ge (D + 1) A with hLt | hGe
    · exact Nat.le_of_lt hLt
    · exact absurd (Nat.mul_le_mul hAn hGe) (Nat.not_le_of_gt hND1)
  have hList := gsDecodeList_length_le_johnson dom word D A hNd hdA (by rw [hLen]; exact hND)
  rwa [hLen] at hList

def dkt26Covers (blowup rem m a : Nat) : Bool :=
  decide ((2 * m + 1) * (2 * m + 1) * (blowup * 2 ^ rem) * (2 ^ rem + 2) ≤ (2 * m * a) * (2 * m * a))
def dkt26Bcf (blowup rem m : Nat) : Nat :=
  let fibers := blowup * 2 ^ rem; let bigD := 2 ^ rem + 1; let twoM1 := 2 * m + 1
  (twoM1 * twoM1 * twoM1 * (fibers * fibers) + 3 * bigD - 1) / (3 * bigD)
def dkt26MaskLineTotalBad (blowup rem m a : Nat) : Nat :=
  dkt26Bcf blowup rem m + JohnsonBound.johnsonBound (blowup * 2 ^ rem) a (2 ^ rem + 1)
def bcgm25Bcf (blowup rem m : Nat) : Nat :=
  let fibers := blowup * 2 ^ rem; let bigD := 2 ^ rem + 1
  ((2 * m + 1) ^ 7 * (fibers * fibers) + 384 * bigD - 1) / (384 * bigD)

private theorem pow_cross_le {u n A B t s : Nat} (hB : 0 < B)
    (hRatio : u * B ≤ A * n) (hCap : A ^ t * s ≤ B ^ t) : u ^ t * s ≤ n ^ t := by
  have h1 : (u * B) ^ t ≤ (A * n) ^ t := Nat.pow_le_pow_left hRatio t
  rw [Nat.mul_pow, Nat.mul_pow] at h1
  have h2 : (u ^ t * s) * B ^ t ≤ n ^ t * B ^ t := by
    calc (u ^ t * s) * B ^ t = (u ^ t * B ^ t) * s := by simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      _ ≤ (A ^ t * n ^ t) * s := Nat.mul_le_mul_right s h1
      _ = (A ^ t * s) * n ^ t := by simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      _ ≤ B ^ t * n ^ t := Nat.mul_le_mul_right (n ^ t) hCap
      _ = n ^ t * B ^ t := Nat.mul_comm _ _
  exact nat_le_of_mul_le_mul_right' h2 (Nat.pow_pos hB)

theorem dkt26_at_28_clears_265 :
    dkt26Covers 4 22 512 8396803 = true ∧
    dkt26MaskLineTotalBad 4 22 512 8396803 * 2 ^ 265 ≤ quinticGoldilocksCard ∧
    (8396803 + 6) ^ 266 * 2 ^ 265 ≤ (2 ^ 24) ^ 266 := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · dsimp only [dkt26MaskLineTotalBad, dkt26Bcf]; rw [JohnsonBound.johnsonBound_eq]; decide +kernel
  · exact pow_cross_le (A := 2051) (B := 4096) (by decide) (by decide +kernel) (by decide +kernel)

/-- `#tooth` Pre-DKT26 `[BCGM25]` `(2m+1)^7` fails the `2^{-264}` RBR floor for all `m ≥ 3` at `log_cells = 28`. -/
theorem tooth_bcgm25_deg7_mask_line_fails_at_28 :
    ¬ ∃ m a : Nat, 3 ≤ m ∧ dkt26Covers 4 22 m a = true ∧
        (a + 6) ^ 266 * 2 ^ 264 ≤ (2 ^ 24) ^ 266 ∧
        bcgm25Bcf 4 22 m * 2 ^ 264 ≤ quinticGoldilocksCard := by
  rintro ⟨m, a, hm3, hCov, hQueryLe, hBcgmLe⟩
  if hm60 : m < 60 then
    have hBelow60 : (List.range 60).all
        (fun k => decide (k < 3) || !dkt26Covers 4 22 k 8459000) = true := by decide +kernel
    have hFalseAtCap : dkt26Covers 4 22 m 8459000 = false := by
      have hb := List.all_eq_true.mp hBelow60 m (List.mem_range.mpr hm60)
      have hmNotLt3 : decide (m < 3) = false := decide_eq_false (by omega)
      rw [hmNotLt3, Bool.false_or] at hb
      cases h : dkt26Covers 4 22 m 8459000
      · rfl
      · rw [h] at hb; cases hb
    have haGe : 8459001 ≤ a := by
      rcases Nat.lt_or_ge a 8459001 with haLt | haGe
      · exfalso
        have haLe : a ≤ 8459000 := by omega
        have h1 : (2 * m + 1) * (2 * m + 1) * (4 * 2 ^ 22) * (2 ^ 22 + 2) ≤
            (2 * m * 8459000) * (2 * m * 8459000) :=
          Nat.le_trans (of_decide_eq_true hCov)
            (Nat.mul_le_mul (Nat.mul_le_mul_left (2 * m) haLe) (Nat.mul_le_mul_left (2 * m) haLe))
        have hTrue : dkt26Covers 4 22 m 8459000 = true := decide_eq_true h1
        rw [hFalseAtCap] at hTrue; exact Bool.false_ne_true hTrue
      · exact haGe
    have hCross : 1032 * 2 ^ 24 ≤ 2048 * (a + 6) := by
      have hBase : 1032 * 2 ^ 24 ≤ 2048 * 8459007 := by decide +kernel
      exact Nat.le_trans hBase (Nat.mul_le_mul_left 2048 (by omega))
    have hPow1 : 1032 ^ 266 * (2 ^ 24) ^ 266 ≤ 2048 ^ 266 * (a + 6) ^ 266 := by
      rw [← Nat.mul_pow, ← Nat.mul_pow]; exact Nat.pow_le_pow_left hCross 266
    have hGap : 2048 ^ 266 < 1032 ^ 266 * 2 ^ 264 := by decide +kernel
    have hStrict : 2048 ^ 266 * (2 ^ 24) ^ 266 < 2048 ^ 266 * ((a + 6) ^ 266 * 2 ^ 264) := by
      have hL := nat_mul_lt_mul_right' hGap (Nat.pow_pos (Nat.two_pow_pos 24) : 0 < (2 ^ 24) ^ 266)
      have hR := Nat.mul_le_mul_right (2 ^ 264) hPow1
      calc 2048 ^ 266 * (2 ^ 24) ^ 266 < (1032 ^ 266 * 2 ^ 264) * (2 ^ 24) ^ 266 := hL
        _ = (1032 ^ 266 * (2 ^ 24) ^ 266) * 2 ^ 264 := by
            simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        _ ≤ (2048 ^ 266 * (a + 6) ^ 266) * 2 ^ 264 := hR
        _ = 2048 ^ 266 * ((a + 6) ^ 266 * 2 ^ 264) := Nat.mul_assoc _ _ _
    exact Nat.not_le_of_gt (nat_lt_of_mul_lt_mul_left' hStrict) hQueryLe
  else
    have hMono : bcgm25Bcf 4 22 60 ≤ bcgm25Bcf 4 22 m := by
      dsimp only [bcgm25Bcf]
      exact Nat.div_le_div_right
        (Nat.sub_le_sub_right
          (Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) 7)) _) 1)
    have h60 : quinticGoldilocksCard < bcgm25Bcf 4 22 60 * 2 ^ 264 := by
      dsimp only [bcgm25Bcf]; decide +kernel
    exact Nat.not_le_of_gt (Nat.lt_of_lt_of_le h60 (Nat.mul_le_mul_right _ hMono)) hBcgmLe

/-! ## §3. Unconditional `WhirScheduleCert` on `QuinticGoldilocks` at `w = 400`-Bit Digests -/

def quinticCoset64 : List QuinticGoldilocks :=
  (ZkHemV2.twoAdicCoset 6).map QuinticGoldilocks.ofBase

theorem quinticCoset64_length : quinticCoset64.length = 64 := by
  unfold quinticCoset64; rw [List.length_map, ZkHemV2.twoAdicCoset_length]

theorem quinticCoset64_nodup : quinticCoset64.Nodup := by
  unfold quinticCoset64
  have hGen : ∀ l : List Goldilocks, l.Nodup → (l.map QuinticGoldilocks.ofBase).Nodup := by
    intro l; induction l with
    | nil => intro _; exact .nil
    | cons a rest ih =>
      intro hCons
      obtain ⟨hNotMem, hNd⟩ := List.nodup_cons.mp hCons
      exact List.nodup_cons.mpr ⟨fun hb => by
        obtain ⟨y, hy, hEq⟩ := List.mem_map.mp hb
        exact hNotMem (QuinticGoldilocks.ofBase_injective hEq ▸ hy), ih hNd⟩
  exact hGen _ (ZkHemV2.twoAdicCoset_nodup 6 (by decide))

def zkHemV2QuinticStage : WhirStage :=
  ⟨0, 6, 6, 5, 66, 1, 9, 1, 65, 260, 1, 0⟩

def zkHemV2QuinticSched : WhirVerifierSchedule :=
  ⟨6, quinticGoldilocksCard, quinticGoldilocksCard_pos, [zkHemV2QuinticStage]⟩

theorem zkHemV2QuinticSched_johnsonOk : zkHemV2QuinticSched.johnsonOk = true := by
  decide +kernel

def zkHemV2QuinticEnv : WhirEnv QuinticGoldilocks where
  chalField := fun c j => QuinticGoldilocks.ofBase (Goldilocks.ofNat ((c + j) % goldilocksPrime))
  chalPos := fun c j n => (c / (n ^ j)) % n
  domPt := fun _ p => quinticCoset64.getD p CommRingOps.zero
  fold2 := fun _ _ a _ => a
  finalClaim := fun P _ => RoundPoly.evalCoeffs P CommRingOps.zero
  initClaim := fun P => RoundPoly.evalCoeffs P CommRingOps.zero
  finalDeg := 1

private def allGood64 (good : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | t + 1, u => good (u % 64) && allGood64 good t (u / 64)

private theorem allGood64_of_range (good : Nat → Bool) :
    ∀ (t u : Nat), (∀ j < t, good ((u / 64 ^ j) % 64) = true) → allGood64 good t u = true
  | 0, _, _ => rfl
  | t + 1, u, hAll => by
    dsimp only [allGood64]
    have h0 : good (u % 64) = true := by
      have h := hAll 0 (Nat.zero_lt_succ t); rwa [Nat.pow_zero, Nat.div_one] at h
    have hRest := allGood64_of_range good t (u / 64) (fun j hj => by
      have h := hAll (j + 1) (Nat.succ_lt_succ hj)
      rwa [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul] at h)
    rw [h0, hRest]; rfl

private theorem qsum_split_add :
    ∀ (a b : Nat) (f : Nat → Nat),
      qsum (a + b) (fun c => f c.1) = qsum a (fun i => f i.1) + qsum b (fun j => f (a + j.1))
  | 0, _, f => by
    rw [Nat.zero_add, qsum_zero, Nat.zero_add]
    exact qsum_congr (fun j => congrArg f (Nat.zero_add j.1).symm)
  | a + 1, b, f => by
    have hEq : a + 1 + b = (a + b) + 1 := by omega
    revert f; rw [hEq]; intro f
    rw [qsum_succ, qsum_succ, qsum_split_add a b (fun k => f (k + 1))]
    dsimp only
    rw [Nat.add_assoc]
    refine congrArg (f 0 + ·) (congrArg (qsum a _ + ·) (qsum_congr (fun j => congrArg f (by omega))))

private theorem qsum_mul_div_mod_local :
    ∀ (A B : Nat) (_hB : 0 < B) (g : Nat → Nat → Nat),
      qsum (A * B) (fun c => g (c.1 / B) (c.1 % B)) = qsum A (fun i => qsum B (fun j => g i.1 j.1))
  | 0, _, _, _ => by rw [Nat.zero_mul, qsum_zero, qsum_zero]
  | A + 1, B, hB, g => by
    rw [Nat.succ_mul, qsum_split_add (A * B) B (fun u => g (u / B) (u % B)),
        qsum_mul_div_mod_local A B hB g, qsum_split_add A 1 (fun i => qsum B (fun j => g i j.1))]
    have h1 : qsum 1 (fun k => qsum B (fun j => g (A + k.1) j.1)) = qsum B (fun j => g A j.1) := by
      rw [qsum_succ, qsum_zero, Nat.add_zero]
      exact qsum_congr (fun j => congrArg (g · j.1) (Nat.add_zero A))
    rw [h1]
    refine congrArg (qsum A _ + ·) (qsum_congr (fun j => ?_))
    have hDiv : (A * B + j.1) / B = A := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt j.2, Nat.zero_add]
    have hMod : (A * B + j.1) % B = j.1 := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.2]
    rw [hDiv, hMod]

private theorem qsum_allGood64_le (B : Nat) (good : Nat → Bool)
    (hGood : qsum 64 (fun i => if good i.1 = true then 1 else 0) ≤ B) :
    ∀ t : Nat, qsum (64 ^ t) (fun u => if allGood64 good t u.1 = true then 1 else 0) ≤ B ^ t
  | 0 => by show qsum 1 _ ≤ 1; rw [qsum_succ, qsum_zero]; exact Nat.le_refl 1
  | t + 1 => by
    have hPow : 64 ^ (t + 1) = 64 ^ t * 64 := Nat.pow_succ 64 t
    have hCongr : ∀ (m n : Nat), m = n → ∀ (f : Nat → Nat),
        qsum m (fun i => f i.1) = qsum n (fun j => f j.1) := by intro m n hm _; subst hm; rfl
    rw [hCongr _ _ hPow (fun u => if allGood64 good (t + 1) u = true then 1 else 0)]
    have hRew : ∀ c : Fin (64 ^ t * 64),
        (if allGood64 good (t + 1) c.1 = true then 1 else 0) =
        (if allGood64 good t (c.1 / 64) = true then 1 else 0) *
          (if good (c.1 % 64) = true then 1 else 0) := by
      intro c
      have hAnd : ∀ (u v : Bool),
          (if (u && v) = true then 1 else 0) =
          (if v = true then 1 else 0) * (if u = true then 1 else 0) := by
        intro u v; cases u <;> cases v <;> rfl
      exact hAnd (good (c.1 % 64)) (allGood64 good t (c.1 / 64))
    rw [qsum_congr hRew, qsum_mul_div_mod_local (64 ^ t) 64 (by decide)
      (fun q r => (if allGood64 good t q = true then 1 else 0) * (if good r = true then 1 else 0))]
    have hFactor : ∀ i : Fin (64 ^ t),
        qsum 64 (fun j => (if allGood64 good t i.1 = true then 1 else 0) *
          (if good j.1 = true then 1 else 0)) ≤
        (if allGood64 good t i.1 = true then 1 else 0) * B := by
      intro i; cases allGood64 good t i.1
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_mul]; rw [qsum_const, Nat.mul_zero]; exact Nat.le_refl 0
      · simp only [↓reduceIte, Nat.one_mul]; exact hGood
    have hStep1 := qsum_le_qsum hFactor
    have hScale : ∀ (m c : Nat) (f : Fin m → Nat), qsum m (fun i => f i * c) = qsum m f * c := by
      intro m c f; induction m with
      | zero => rw [qsum_zero, qsum_zero, Nat.zero_mul]
      | succ m ihm => rw [qsum_succ, qsum_succ, Nat.add_mul, ihm]
    rw [hScale] at hStep1
    rw [Nat.pow_succ]
    exact Nat.le_trans hStep1 (Nat.mul_le_mul_right B (qsum_allGood64_le B good hGood t))

private theorem filter_range_eq_qsum64 (good : Nat → Bool) :
    ((List.range 64).filter good).length = qsum 64 (fun i => if good i.1 = true then 1 else 0) := by
  have gen : ∀ n : Nat,
      ((List.range n).filter good).length = qsum n (fun i => if good i.1 = true then 1 else 0) := by
    intro n; induction n with
    | zero => rfl
    | succ n ihn =>
      rw [List.range_succ, List.filter_append, List.length_append, ihn,
          qsum_split_add n 1 (fun u => if good u = true then 1 else 0),
          qsum_succ, qsum_zero, Nat.add_zero, Nat.add_zero]
      dsimp only [List.filter, List.length]
      cases good n <;> simp
  exact gen 64

private theorem zkHemV2Quintic_verify_extract (x : WhirStmt QuinticGoldilocks)
    (m0 m1 : WhirMsg QuinticGoldilocks) (c0 c1 : Nat)
    (hv : (whirOracleIop zkHemV2QuinticEnv zkHemV2QuinticSched 400).verify x
      [(m0, c0), (m1, c1)] = true) :
    m0.poly.length ≤ 2 ∧
    RoundPoly.evalCoeffs m0.poly CommRingOps.zero = x.claim ∧
    ∀ j < 66,
      RoundPoly.evalCoeffs m0.poly (zkHemV2QuinticEnv.domPt 0 ((c1 / 64 ^ j) % 64)) =
        x.table.getD ((c1 / 64 ^ j) % 64) CommRingOps.zero := by
  have hEq := whirOracleIop_verify_oneStage_noFold_eq zkHemV2QuinticEnv 6 quinticGoldilocksCard
    quinticGoldilocksCard_pos zkHemV2QuinticStage 400 rfl rfl rfl rfl x m0 m1 c0 c1
  dsimp only at hEq
  change (whirOracleIop zkHemV2QuinticEnv zkHemV2QuinticSched 400).verify x
    [(m0, c0), (m1, c1)] = _ at hEq
  rw [hEq] at hv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
  have hDeg : m0.poly.length ≤ 2 := hv.1.1.1.2
  have hZipQ := hv.1.2
  have hClaim : x.claim = RoundPoly.evalCoeffs m0.poly CommRingOps.zero := hv.2
  refine ⟨hDeg, hClaim.symm, fun j hj => ?_⟩
  let vals := (List.range 66).map (fun k =>
    x.table.getD ((c1 / 64 ^ k) % 64) CommRingOps.zero)
  have hjR : j < (List.range 66).length := by rw [List.length_range]; exact hj
  have hjV : j < vals.length := by dsimp only [vals]; rw [List.length_map, List.length_range]; exact hj
  have hMem : (j, x.table.getD ((c1 / 64 ^ j) % 64) CommRingOps.zero) ∈ (List.range 66).zip vals := by
    have hGet : ((List.range 66).zip vals)[j]'(by rw [List.length_zip]; exact Nat.lt_min.mpr ⟨hjR, hjV⟩) =
        (j, x.table.getD ((c1 / 64 ^ j) % 64) CommRingOps.zero) := by
      dsimp only [vals]
      rw [List.getElem_zip, List.getElem_range, List.getElem_map, List.getElem_range]
    exact hGet ▸ List.getElem_mem _
  have hChk := List.all_eq_true.mp hZipQ _ hMem
  rw [decide_eq_true_eq] at hChk
  exact hChk

private theorem pow2_400_split : 2 ^ 400 = 2 ^ 4 * 64 ^ 66 := by
  calc 2 ^ 400 = 2 ^ (4 + 6 * 66) := rfl
    _ = 2 ^ 4 * (2 ^ 6) ^ 66 := by rw [Nat.pow_add, Nat.pow_mul]
    _ = 2 ^ 4 * 64 ^ 66 := rfl

private theorem qsum_eq_of_eq {n m : Nat} (h : n = m) (f : Nat → Nat) :
    qsum n (fun i => f i.1) = qsum m (fun j => f j.1) := by subst h; rfl

private theorem zkHemV2Quintic_round0_flips (x : WhirStmt QuinticGoldilocks)
    (m : WhirMsg QuinticGoldilocks) :
    qsum (2 ^ (whirOracleIop zkHemV2QuinticEnv zkHemV2QuinticSched 400).w)
      (fun ch => if (whirOracleIop zkHemV2QuinticEnv zkHemV2QuinticSched 400).verify x
        ([] ++ [(m, ch.1)]) = true then 1 else 0) ≤ 0 := by
  have hW : 2 ^ (whirOracleIop zkHemV2QuinticEnv zkHemV2QuinticSched 400).w = 2 ^ 400 := rfl
  rw [qsum_eq_of_eq hW (fun u => if (whirOracleIop zkHemV2QuinticEnv zkHemV2QuinticSched 400).verify x
    ([] ++ [(m, u)]) = true then 1 else 0)]
  dsimp only [List.nil_append]
  have hZero : ∀ ch : Fin (2 ^ 400),
      (if (whirOracleIop zkHemV2QuinticEnv zkHemV2QuinticSched 400).verify x [(m, ch.1)] = true then 1 else 0) = 0 := by
    intro ch; cases hv : (whirOracleIop zkHemV2QuinticEnv zkHemV2QuinticSched 400).verify x [(m, ch.1)]
    · rfl
    · exfalso; rw [OracleIop.verify_eq] at hv
      have hLen := of_decide_eq_true (Bool.and_eq_true_iff.mp hv).1
      have h2 : zkHemV2QuinticSched.numRounds = 2 := rfl; rw [h2] at hLen; simp at hLen
  rw [qsum_congr hZero, qsum_const, Nat.mul_zero]; exact Nat.le_refl 0

private theorem zkHemV2Quintic_round1_flips (x : WhirStmt QuinticGoldilocks)
    (hx : ¬ (whirOracleIop zkHemV2QuinticEnv zkHemV2QuinticSched 400).inLang x)
    (m0 m : WhirMsg QuinticGoldilocks) (c0 : Nat) :
    qsum (2 ^ (whirOracleIop zkHemV2QuinticEnv zkHemV2QuinticSched 400).w)
      (fun ch => if (whirOracleIop zkHemV2QuinticEnv zkHemV2QuinticSched 400).verify x
        ([(m0, c0)] ++ [(m, ch.1)]) = true then 1 else 0) ≤ 2 ^ 4 * 8 ^ 66 := by
  have hW : 2 ^ (whirOracleIop zkHemV2QuinticEnv zkHemV2QuinticSched 400).w = 2 ^ 4 * 64 ^ 66 :=
    pow2_400_split
  rw [qsum_eq_of_eq hW (fun u => if (whirOracleIop zkHemV2QuinticEnv zkHemV2QuinticSched 400).verify x
    ([(m0, c0)] ++ [(m, u)]) = true then 1 else 0)]
  dsimp only [List.cons_append, List.nil_append]
  if hPolyOk : m0.poly.length ≤ 2 ∧ RoundPoly.evalCoeffs m0.poly CommRingOps.zero = x.claim then
    let goodPos (p : Nat) : Bool :=
      decide (RoundPoly.evalCoeffs m0.poly (zkHemV2QuinticEnv.domPt 0 p) =
        x.table.getD p CommRingOps.zero)
    have hGoodLe8 : qsum 64 (fun i => if goodPos i.1 = true then 1 else 0) ≤ 8 := by
      rcases Nat.lt_or_ge 8 (qsum 64 (fun i => if goodPos i.1 = true then 1 else 0)) with hGt8 | hLe8
      · exfalso
        have hGe9 : 9 ≤ agreeCount zkHemV2QuinticEnv 64 x.table m0.poly := by
          unfold agreeCount; rw [filter_range_eq_qsum64 goodPos]; exact hGt8
        exact hx ⟨m0.poly, hPolyOk.1, hGe9, hPolyOk.2⟩
      · exact hLe8
    have hCongr :
        qsum (2 ^ 4 * 64 ^ 66) (fun ch =>
          if (whirOracleIop zkHemV2QuinticEnv zkHemV2QuinticSched 400).verify x
            [(m0, c0), (m, ch.1)] = true then 1 else 0) ≤
        qsum (2 ^ 4 * 64 ^ 66) (fun ch =>
          if allGood64 goodPos 66 (ch.1 % (64 ^ 66)) = true then 1 else 0) := by
      refine qsum_le_qsum (fun ch => ?_)
      cases hv : (whirOracleIop zkHemV2QuinticEnv zkHemV2QuinticSched 400).verify x [(m0, c0), (m, ch.1)]
      · simp only [Bool.false_eq_true, ↓reduceIte]; exact Nat.zero_le _
      · simp only [↓reduceIte]
        obtain ⟨_, _, hAllQ⟩ := zkHemV2Quintic_verify_extract x m0 m c0 ch.1 hv
        have hModAll : ∀ j < 66, goodPos (((ch.1 % (64 ^ 66)) / 64 ^ j) % 64) = true := by
          intro j hj
          have hPowSplit : 64 ^ 66 = 64 ^ j * (64 * 64 ^ (66 - j - 1)) := by
            calc 64 ^ 66 = 64 ^ (j + (66 - j - 1 + 1)) := congrArg (64 ^ ·) (by omega)
              _ = 64 ^ j * 64 ^ (66 - j - 1 + 1) := Nat.pow_add 64 j _
              _ = 64 ^ j * (64 ^ (66 - j - 1) * 64) := by rw [Nat.pow_succ]
              _ = 64 ^ j * (64 * 64 ^ (66 - j - 1)) := by rw [Nat.mul_comm (64 ^ (66 - j - 1)) 64]
          have hDivModEq : ∀ u : Nat, ((u % (64 ^ 66)) / 64 ^ j) % 64 = (u / 64 ^ j) % 64 := by
            intro u
            have hd : 64 ^ 66 * (u / 64 ^ 66) + u % 64 ^ 66 = u := Nat.div_add_mod u (64 ^ 66)
            generalize u / 64 ^ 66 = q66, u % 64 ^ 66 = r66 at hd ⊢
            rw [← hd, hPowSplit, Nat.mul_assoc (64 ^ j),
                Nat.mul_add_div (Nat.pow_pos (by decide : 0 < 64)),
                Nat.mul_assoc 64, Nat.mul_add_mod]
          rw [hDivModEq ch.1]; exact decide_eq_true (hAllQ j hj)
        rw [allGood64_of_range goodPos 66 _ hModAll]; exact Nat.le_refl 1
    rw [qsum_mul_div_mod_local (2 ^ 4) (64 ^ 66) (Nat.pow_pos (by decide))
      (fun _ r => if allGood64 goodPos 66 r = true then 1 else 0), qsum_const] at hCongr
    exact Nat.le_trans hCongr (Nat.mul_le_mul_left (2 ^ 4) (qsum_allGood64_le 8 goodPos hGoodLe8 66))
  else
    have hZero : ∀ ch : Fin (2 ^ 4 * 64 ^ 66),
        (if (whirOracleIop zkHemV2QuinticEnv zkHemV2QuinticSched 400).verify x
          [(m0, c0), (m, ch.1)] = true then 1 else 0) = 0 := by
      intro ch
      cases hv : (whirOracleIop zkHemV2QuinticEnv zkHemV2QuinticSched 400).verify x [(m0, c0), (m, ch.1)]
      · rfl
      · obtain ⟨hd, hc, _⟩ := zkHemV2Quintic_verify_extract x m0 m c0 ch.1 hv
        exact absurd ⟨hd, hc⟩ hPolyOk
    rw [qsum_congr hZero, qsum_const, Nat.mul_zero]; exact Nat.zero_le _

/-- Unconditional `WhirScheduleCert` on `QuinticGoldilocks` at `w = 400`-bit digests. -/
