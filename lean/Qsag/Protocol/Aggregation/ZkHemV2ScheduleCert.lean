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
def zkHemV2QuinticCert : WhirScheduleCert zkHemV2QuinticEnv zkHemV2QuinticSched 400 where
  cert := {
    state := (whirOracleIop zkHemV2QuinticEnv zkHemV2QuinticSched 400).verify
    bad := fun r => if r.1 = 1 then 2 ^ 4 * 8 ^ 66 else 0
    init := fun x _ => by
      rw [OracleIop.verify_eq]
      have hF : decide (([] : List (WhirMsg QuinticGoldilocks × Nat)).length =
          zkHemV2QuinticSched.numRounds) = false := by decide
      rw [hF, Bool.false_and]
    accept := fun _ _ hv => hv
    flip := fun x hx r pref m hLen _ => by
      match r, pref, hLen with
      | ⟨0, _⟩, [], _ => exact Nat.le_trans (zkHemV2Quintic_round0_flips x m) (Nat.zero_le _)
      | ⟨0, _⟩, _ :: _, h => exact absurd h (by simp only [List.length_cons]; exact Nat.succ_ne_zero _)
      | ⟨1, _⟩, [], h => exact absurd h (show ¬ (0 : Nat) = 1 by decide)
      | ⟨1, _⟩, [(m0, c0)], _ => -- explicit lemma: the kernel must not defeq-check `ite` against `2 ^ 4 * 8 ^ 66`
        exact Nat.le_trans (zkHemV2Quintic_round1_flips x hx m0 m c0) (Nat.le_of_eq (ite_eq_left rfl).symm)
      | ⟨1, _⟩, _ :: _ :: _, h =>
        exact absurd (Nat.succ.inj h) (by simp only [List.length_cons]; exact Nat.succ_ne_zero _)
      | ⟨n + 2, hn⟩, _, _ =>
        exact absurd hn (by have h2 : zkHemV2QuinticSched.numRounds = 2 := rfl; rw [h2]; omega)
  }
  covers := fun r => by
    have h2 : zkHemV2QuinticSched.numRounds = 2 := rfl
    rcases r with ⟨_ | _ | n, hn⟩
    · unfold RatBound.le
      have hZ : (if (0 : Nat) = 1 then 2 ^ 4 * 8 ^ 66 else 0) = 0 := rfl
      dsimp only; rw [hZ, Nat.zero_mul]; exact Nat.zero_le _
    · have hGet : zkHemV2QuinticSched.roundBounds.getD 1 RatBound.one =
          zkHemV2QuinticStage.shiftBound quinticGoldilocksCard quinticGoldilocksCard_pos := by
        rw [WhirVerifierSchedule.roundBounds_eq]
        unfold zkHemV2QuinticSched; dsimp only
        rw [stagesRoundBounds_cons, stagesRoundBounds_nil, List.append_nil, WhirStage.roundBounds_eq]
        rfl
      rw [hGet, WhirStage.shiftBound_eq]
      unfold RatBound.le RatBound.add
      have hO : (if (1 : Nat) = 1 then 2 ^ 4 * 8 ^ 66 else 0) = 2 ^ 4 * 8 ^ 66 := rfl
      have hDom : zkHemV2QuinticStage.domainSize = 64 := rfl
      have hQ : zkHemV2QuinticStage.queryCount = 66 := rfl
      have hAg : zkHemV2QuinticStage.agree + zkHemV2QuinticStage.foldK = 9 := rfl
      dsimp only; rw [hO, hDom, hQ, hAg, pow2_400_split]
      have hL : (2 ^ 4 * 8 ^ 66) * (64 ^ 66 * quinticGoldilocksCard) =
          (8 ^ 66 * quinticGoldilocksCard) * (2 ^ 4 * 64 ^ 66) := by
        simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      rw [hL]; refine Nat.mul_le_mul_right (2 ^ 4 * 64 ^ 66) ?_
      exact Nat.le_trans
        (Nat.mul_le_mul_right quinticGoldilocksCard (Nat.pow_le_pow_left (by decide) 66))
        (Nat.le_add_right _ _)
    · rw [h2] at hn; omega

/-- Honest all-ones codeword with claim `1` is accepted by `zkHemV2QuinticEnv` at `w = 400`. -/
theorem zkHemV2Quintic_honest_accepts :
    (whirOracleIop zkHemV2QuinticEnv zkHemV2QuinticSched 400).verify
      ⟨List.replicate 64 QuinticGoldilocks.one, QuinticGoldilocks.one⟩
      [(⟨[], [QuinticGoldilocks.one], []⟩, 0),
       (⟨[], [], List.replicate 5 QuinticGoldilocks.one⟩, 0)] = true := by
  have hEq := whirOracleIop_verify_oneStage_noFold_eq zkHemV2QuinticEnv 6 quinticGoldilocksCard
    quinticGoldilocksCard_pos zkHemV2QuinticStage 400 rfl rfl rfl rfl
    ⟨List.replicate 64 QuinticGoldilocks.one, QuinticGoldilocks.one⟩
    ⟨[], [QuinticGoldilocks.one], []⟩ ⟨[], [], List.replicate 5 QuinticGoldilocks.one⟩ 0 0
  dsimp only at hEq
  change (whirOracleIop zkHemV2QuinticEnv zkHemV2QuinticSched 400).verify _ _ = _ at hEq
  rw [hEq]; decide +kernel

/-- All-ones codeword with claim `0` is outside `whirInLang zkHemV2QuinticEnv zkHemV2QuinticSched`. -/
theorem zkHemV2Quintic_false_not_inLang :
    ¬ whirInLang zkHemV2QuinticEnv zkHemV2QuinticSched
      ⟨List.replicate 64 QuinticGoldilocks.one, QuinticGoldilocks.zero⟩ := by
  rintro ⟨P, hLen, hAgree, hClaim⟩
  have hLen2 : P.length ≤ 2 := hLen
  have hAtMost1 : agreeCount zkHemV2QuinticEnv 64 (List.replicate 64 QuinticGoldilocks.one) P ≤ 1 := by
    have hCoeff1 : ∃ c1 : QuinticGoldilocks, ∀ z : QuinticGoldilocks,
        RoundPoly.evalCoeffs P z = z *ᵍ c1 := by
      rcases P with _ | ⟨c0, _ | ⟨c1, _ | ⟨_, _⟩⟩⟩
      · exact ⟨CommRingOps.zero, fun z => by dsimp only [RoundPoly.evalCoeffs]; constructive_ring⟩
      · have hc0 : c0 = CommRingOps.zero := by
          dsimp only [zkHemV2QuinticEnv, RoundPoly.evalCoeffs] at hClaim
          calc c0 = c0 +ᵍ CommRingOps.zero *ᵍ CommRingOps.zero := by constructive_ring
            _ = CommRingOps.zero := hClaim
        subst hc0
        exact ⟨CommRingOps.zero, fun z => by dsimp only [RoundPoly.evalCoeffs]; constructive_ring⟩
      · have hc0 : c0 = CommRingOps.zero := by
          dsimp only [zkHemV2QuinticEnv, RoundPoly.evalCoeffs] at hClaim
          calc c0 = c0 +ᵍ CommRingOps.zero *ᵍ (c1 +ᵍ CommRingOps.zero *ᵍ CommRingOps.zero) := by
                  constructive_ring
            _ = CommRingOps.zero := hClaim
        subst hc0
        exact ⟨c1, fun z => by dsimp only [RoundPoly.evalCoeffs]; constructive_ring⟩
      · exfalso; simp only [List.length_cons] at hLen2; omega
    obtain ⟨c1, hEval⟩ := hCoeff1
    have hRepGetD : ∀ {p : Nat}, p < 64 →
        (List.replicate 64 QuinticGoldilocks.one).getD p CommRingOps.zero = QuinticGoldilocks.one := by
      intro p hp; rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      simp only [hp, ↓reduceIte, Option.getD_some]
    if hc1 : c1 = CommRingOps.zero then
      subst hc1; unfold agreeCount
      have hNil : (List.range 64).filter (fun p =>
          decide (RoundPoly.evalCoeffs P (zkHemV2QuinticEnv.domPt 0 p) =
            (List.replicate 64 QuinticGoldilocks.one).getD p CommRingOps.zero)) = [] := by
        refine filter_eq_nil_local _ (List.range 64) (fun p hp => decide_eq_false (fun hEq => ?_))
        rw [hEval, LawfulCommRing.mul_zero, hRepGetD (List.mem_range.mp hp)] at hEq
        exact LawfulField.zero_ne_one hEq
      rw [hNil]; exact Nat.zero_le 1
    else
      unfold agreeCount
      have hMapEq : quinticCoset64 = (List.range 64).map (zkHemV2QuinticEnv.domPt 0) := by
        apply List.ext_getElem
        · rw [quinticCoset64_length, List.length_map, List.length_range]
        · intro i hi1 _; rw [List.getElem_map, List.getElem_range]
          dsimp only [zkHemV2QuinticEnv]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi1, Option.getD_some]
      have hSub : ∀ r : List Nat, (∀ p ∈ r, p < 64) →
          (r.filter (fun p => decide (RoundPoly.evalCoeffs P (zkHemV2QuinticEnv.domPt 0 p) =
            (List.replicate 64 QuinticGoldilocks.one).getD p CommRingOps.zero))).length ≤
          ((r.map (zkHemV2QuinticEnv.domPt 0)).filter
            (fun z => decide (z = LawfulField.inv c1))).length := by
        intro r; induction r with
        | nil => intro _; exact Nat.le_refl 0
        | cons p ps ih =>
          intro hr
          have hpLt := hr p List.mem_cons_self
          have ihPs := ih (fun q hq => hr q (List.mem_cons_of_mem _ hq))
          simp only [List.filter_cons, List.map_cons]
          if hHit : RoundPoly.evalCoeffs P (zkHemV2QuinticEnv.domPt 0 p) =
              (List.replicate 64 QuinticGoldilocks.one).getD p CommRingOps.zero then
            have hInv : zkHemV2QuinticEnv.domPt 0 p = LawfulField.inv c1 := by
              have hHit1 := hHit; rw [hEval, hRepGetD hpLt] at hHit1
              calc zkHemV2QuinticEnv.domPt 0 p
                  = (zkHemV2QuinticEnv.domPt 0 p *ᵍ c1) *ᵍ LawfulField.inv c1 := by
                      rw [LawfulCommRing.mul_assoc, LawfulField.mul_inv_cancel hc1, LawfulCommRing.mul_one]
                _ = LawfulField.inv c1 := by rw [hHit1]; exact LawfulCommRing.one_mul _
            rw [decide_eq_true hHit, decide_eq_true hInv]
            simp only [↓reduceIte, List.length_cons]; exact Nat.succ_le_succ ihPs
          else
            rw [decide_eq_false hHit]; simp only [Bool.false_eq_true, ↓reduceIte]
            cases decide (zkHemV2QuinticEnv.domPt 0 p = LawfulField.inv c1) <;>
              simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]
            · exact ihPs
            · exact Nat.le_trans ihPs (Nat.le_succ _)
      have hBound := hSub (List.range 64) (fun _ hp => List.mem_range.mp hp)
      rw [← hMapEq] at hBound
      exact Nat.le_trans hBound (nodup_filter_eq_le_one _ quinticCoset64 quinticCoset64_nodup)
  have h9 : 9 ≤ agreeCount zkHemV2QuinticEnv 64 (List.replicate 64 QuinticGoldilocks.one) P := hAgree
  omega

@[expose] def merkle400QromBound (Q : Nat) : RatBound := ⟨6680 * Q ^ 3, 2 ^ 400, Nat.two_pow_pos 400⟩
@[expose] def merkle256QromBound (Q : Nat) : RatBound := ⟨6680 * Q ^ 3, 2 ^ 256, Nat.two_pow_pos 256⟩

theorem merkle400QromBound_mono {Q Q' : Nat} (h : Q ≤ Q') :
    RatBound.le (merkle400QromBound Q) (merkle400QromBound Q') := by
  show 6680 * Q ^ 3 * 2 ^ 400 ≤ 6680 * Q' ^ 3 * 2 ^ 400
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 6680 (Nat.pow_le_pow_left h 3))

theorem zkHemV2Quintic_qrom_lt_128_at_2pow28 {Q : Nat} (hQ : Q ≤ 2 ^ 28) :
    RatBound.lt (RatBound.add (scheduleQromError zkHemV2QuinticSched Q) (merkle400QromBound Q))
      (RatBound.invPow2 128) := by
  have hMono := RatBound.add_le_add (scheduleQromError_mono zkHemV2QuinticSched hQ) (merkle400QromBound_mono hQ)
  have hTop : RatBound.lt (RatBound.add (scheduleQromError zkHemV2QuinticSched (2 ^ 28)) (merkle400QromBound (2 ^ 28)))
      (RatBound.invPow2 128) := by
    rw [scheduleQromError_eq, WhirVerifierSchedule.roundBounds_eq]; unfold zkHemV2QuinticSched; dsimp only
    rw [stagesRoundBounds_cons, stagesRoundBounds_nil, List.append_nil, WhirStage.roundBounds_eq,
        WhirStage.oodBound_eq, WhirStage.shiftBound_eq]
    dsimp only [zkHemV2QuinticStage, List.replicate, List.nil_append, List.map]; rw [binom2_eq]; decide +kernel
  exact ratBound_lt_of_le_of_lt hMono hTop

/-! ## §4. Production `zk-Hem v2` + DKT26 Schedule Family (`log_cells ∈ [16, 28]`) & `< 2^{-128}` QROM Soundness -/

@[expose] def zkHemV2Stage0Queries (logCells : Nat) : Option Nat :=
  if logCells < 16 then none
  else ([267, 267, 267, 267, 267, 267, 267, 267, 266, 266, 266, 266, 266] : List Nat)[logCells - 16]?

theorem zkHemV2Stage0Queries_table :
    (List.range 13).map (fun i => zkHemV2Stage0Queries (16 + i)) =
      [some 267, some 267, some 267, some 267, some 267, some 267, some 267, some 267,
       some 266, some 266, some 266, some 266, some 266] := by decide +kernel

def zkHemV2LaterQueries (logBlowup : Nat) : Nat := (532 + logBlowup - 1) / logBlowup + 3

theorem zkHemV2LaterQueries_values :
    (zkHemV2LaterQueries 4, zkHemV2LaterQueries 6, zkHemV2LaterQueries 8) = (136, 92, 70) := by decide +kernel

def zkHemV2ProdStages : Nat → List WhirStage
  | 16 => [⟨4, 14, 2, 5, 267, 4097, 8203, 1, 2048, 2048, 16, 23519292652270⟩, ⟨3, 13, 4, 2, 136, 514, 2069, 1, 512, 1023, 3, 9210⟩, ⟨3, 12, 6, 2, 92, 66, 525, 1, 1024, 4034, 3, 36309⟩]
  | 17 => [⟨5, 14, 2, 5, 267, 4097, 8203, 1, 2048, 2048, 17, 23519292652270⟩, ⟨3, 13, 4, 2, 136, 514, 2069, 1, 512, 1023, 3, 9210⟩, ⟨4, 11, 6, 2, 92, 34, 266, 1, 1024, 3974, 3, 47692⟩]
  | 18 => [⟨5, 15, 2, 5, 267, 8193, 16403, 1, 2048, 2048, 18, 47044326618137⟩, ⟨3, 14, 4, 2, 136, 1026, 4133, 1, 512, 1024, 3, 9219⟩, ⟨4, 12, 6, 2, 92, 66, 525, 1, 1024, 4034, 3, 48412⟩]
  | 19 => [⟨5, 16, 2, 5, 267, 16385, 32803, 1, 2048, 2048, 19, 94094395601011⟩, ⟨3, 15, 4, 2, 136, 2050, 8261, 1, 512, 1024, 3, 9219⟩, ⟨4, 13, 6, 2, 92, 130, 1041, 1, 1024, 4065, 3, 48784⟩]
  | 20 => [⟨5, 17, 2, 5, 267, 32769, 65603, 1, 2048, 2048, 20, 188194534092434⟩, ⟨3, 16, 4, 2, 136, 4098, 16517, 1, 512, 1024, 3, 9219⟩, ⟨4, 14, 6, 2, 92, 258, 2073, 1, 1024, 4081, 3, 48976⟩]
  | 21 => [⟨6, 17, 2, 5, 267, 32769, 65603, 1, 2048, 2048, 21, 188194534092434⟩, ⟨3, 16, 4, 2, 136, 4098, 16517, 1, 512, 1024, 3, 9219⟩, ⟨4, 14, 6, 2, 92, 258, 2073, 1, 1024, 4081, 3, 48976⟩]
  | 22 => [⟨6, 18, 2, 5, 267, 65537, 131203, 1, 2048, 2048, 22, 376394811338141⟩, ⟨4, 16, 4, 2, 136, 4098, 16517, 1, 512, 1024, 3, 12292⟩, ⟨4, 14, 6, 2, 92, 258, 2073, 1, 1024, 4081, 3, 48976⟩]
  | 23 => [⟨6, 19, 2, 5, 267, 131073, 262403, 1, 2048, 2048, 23, 752795365960994⟩, ⟨4, 17, 4, 2, 136, 8194, 33029, 1, 512, 1024, 3, 12292⟩, ⟨3, 16, 6, 2, 92, 1026, 8265, 1, 1024, 4093, 3, 36840⟩, ⟨3, 15, 8, 2, 70, 130, 2081, 1, 2048, 16258, 3, 146325⟩]
  | 24 => [⟨6, 20, 2, 5, 266, 262145, 524803, 1, 2048, 2048, 24, 1505596475272420⟩, ⟨4, 18, 4, 2, 136, 16386, 66053, 1, 512, 1024, 3, 12292⟩, ⟨3, 17, 6, 2, 92, 2050, 16521, 1, 1024, 4095, 3, 36858⟩, ⟨3, 16, 8, 2, 70, 258, 4145, 1, 2048, 16321, 3, 146892⟩]
  | 25 => [⟨6, 21, 2, 5, 266, 524289, 1049603, 1, 2048, 2048, 25, 3011198693928133⟩, ⟨4, 19, 4, 2, 136, 32770, 132101, 1, 512, 1024, 3, 12292⟩, ⟨4, 17, 6, 2, 92, 2050, 16521, 1, 1024, 4095, 3, 49144⟩, ⟨3, 16, 8, 2, 70, 258, 4145, 1, 2048, 16321, 3, 146892⟩]
  | 26 => [⟨6, 22, 2, 5, 266, 1048577, 2099203, 1, 2048, 2048, 26, 6022403131255990⟩, ⟨5, 19, 4, 2, 136, 32770, 132101, 1, 512, 1024, 3, 15365⟩, ⟨4, 17, 6, 2, 92, 2050, 16521, 1, 1024, 4095, 3, 49144⟩, ⟨3, 16, 8, 2, 70, 258, 4145, 1, 2048, 16321, 3, 146892⟩]
  | 27 => [⟨6, 23, 2, 5, 266, 2097153, 4198403, 1, 2048, 2048, 27, 12044812005919918⟩, ⟨5, 20, 4, 2, 136, 65538, 264197, 1, 512, 1024, 3, 15365⟩, ⟨4, 18, 6, 2, 92, 4098, 33033, 1, 1024, 4096, 3, 49156⟩, ⟨4, 16, 8, 2, 70, 258, 4145, 1, 2048, 16321, 3, 195856⟩]
  | 28 => [⟨6, 24, 2, 5, 266, 4194305, 8396803, 1, 2048, 2048, 28, 24089629755251882⟩, ⟨6, 20, 4, 2, 136, 65538, 264197, 1, 512, 1024, 3, 18438⟩, ⟨4, 18, 6, 2, 92, 4098, 33033, 1, 1024, 4096, 3, 49156⟩, ⟨4, 16, 8, 2, 70, 258, 4145, 1, 2048, 16321, 3, 195856⟩]
  | _ => []

def zkHemV2ProdSched (logCells : Nat) : WhirVerifierSchedule :=
  ⟨logCells, quinticGoldilocksCard, quinticGoldilocksCard_pos, zkHemV2ProdStages logCells⟩

theorem zkHemV2ProdStages_dkt26_exact (logCells : Nat) (hLo : 16 ≤ logCells) (hHi : logCells ≤ 28) :
    match (zkHemV2ProdStages logCells)[0]? with
    | some s0 =>
      let rem0 := logCells - s0.foldK
      dkt26Covers 4 rem0 512 s0.agree = true ∧ dkt26Covers 4 rem0 512 (s0.agree - 1) = false ∧
      s0.mcaNum = dkt26MaskLineTotalBad 4 rem0 512 s0.agree ∧
      some s0.queryCount = zkHemV2Stage0Queries logCells
    | none => False := by
  have hCases : logCells = 16 ∨ logCells = 17 ∨ logCells = 18 ∨ logCells = 19 ∨ logCells = 20 ∨
      logCells = 21 ∨ logCells = 22 ∨ logCells = 23 ∨ logCells = 24 ∨ logCells = 25 ∨
      logCells = 26 ∨ logCells = 27 ∨ logCells = 28 := by omega
  rcases hCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [zkHemV2ProdStages, List.getElem?_cons_zero, dkt26MaskLineTotalBad, dkt26Bcf,
       JohnsonBound.johnsonBound_eq];
     exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩)

theorem zkHemV2ProdSched_johnsonOk (logCells : Nat) (hLo : 16 ≤ logCells) (hHi : logCells ≤ 28) :
    (zkHemV2ProdSched logCells).johnsonOk = true := by
  have hCases : logCells = 16 ∨ logCells = 17 ∨ logCells = 18 ∨ logCells = 19 ∨ logCells = 20 ∨
      logCells = 21 ∨ logCells = 22 ∨ logCells = 23 ∨ logCells = 24 ∨ logCells = 25 ∨
      logCells = 26 ∨ logCells = 27 ∨ logCells = 28 := by omega
  rcases hCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide +kernel

private def shiftCapNum (qCount : Nat) : Nat :=
  if qCount = 267 then 2052 else if qCount = 266 then 2051 else if qCount = 136 then 1036
  else if qCount = 92 then 540 else 261

private theorem shiftCapNum_pow_ok {t : Nat} (ht : t = 267 ∨ t = 266 ∨ t = 136 ∨ t = 92 ∨ t = 70) :
    (shiftCapNum t) ^ t * 2 ^ 267 ≤ 3 * 4096 ^ t := by
  rcases ht with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private def checkStageFast265 (q : Nat) (s : WhirStage) : Bool :=
  decide ((s.listSize * s.sumcheckDeg + s.mcaNum) * 2 ^ 265 ≤ q ∧
    (s.listSize * (s.listSize - 1) / 2) * s.degBound ^ s.oodCount * 2 ^ 265 ≤ q ^ s.oodCount ∧
    (s.queryCount = 267 ∨ s.queryCount = 266 ∨ s.queryCount = 136 ∨ s.queryCount = 92 ∨ s.queryCount = 70) ∧
    (s.agree + s.foldK) * 4096 ≤ shiftCapNum s.queryCount * s.domainSize ∧
    s.listSize * (s.queryCount + s.oodCount) * 2 ^ 267 ≤ q)

private inductive RBoundsLe : List RatBound → List RatBound → Prop where
  | nil : RBoundsLe [] []
  | cons {x y xs ys} : RatBound.le x y → RBoundsLe xs ys → RBoundsLe (x :: xs) (y :: ys)

private theorem RBoundsLe.append {xs ys us vs : List RatBound}
    (h : RBoundsLe xs ys) (k : RBoundsLe us vs) : RBoundsLe (xs ++ us) (ys ++ vs) := by
  induction h with | nil => exact k | cons hxy _ ih => exact .cons hxy ih

private theorem scaled_sum_mono_v2 (Q : Nat) {xs ys : List RatBound} (h : RBoundsLe xs ys) :
    RatBound.le (RatBound.sumList (xs.map (dfmRoundScale Q))) (RatBound.sumList (ys.map (dfmRoundScale Q))) := by
  induction h with
  | nil => exact RatBound.le_refl _
  | @cons x y _ _ hxy _ ih =>
    exact RatBound.add_le_add
      (by show (2 * Q + 1) ^ 2 * x.num * y.den ≤ (2 * Q + 1) ^ 2 * y.num * x.den
          simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left ((2 * Q + 1) ^ 2) hxy) ih

private theorem replicate_add_local {α : Type} (x : α) :
    ∀ (a b : Nat), List.replicate (a + b) x = List.replicate a x ++ List.replicate b x
  | 0, _ => by simp only [Nat.zero_add, List.replicate_zero, List.nil_append]
  | a + 1, b => by simp only [Nat.succ_add, List.replicate_succ, List.cons_append, replicate_add_local x a b]

private theorem stage_covers_replicate265 (q : Nat) (hq : 0 < q) (s : WhirStage)
    (hOk : checkStageFast265 q s = true) :
    RBoundsLe (s.roundBounds q hq) (List.replicate (stageRounds s) (RatBound.invPow2 265)) := by
  obtain ⟨hf, ho, hQt, hRatio, hComb⟩ := of_decide_eq_true hOk
  have hFold : RatBound.le (s.foldBound q hq) (RatBound.invPow2 265) := by
    rw [WhirStage.foldBound_eq]; show _ ≤ 1 * q; rw [Nat.one_mul]; exact hf
  have hOod : RatBound.le (s.oodBound q hq) (RatBound.invPow2 265) := by
    rw [WhirStage.oodBound_eq]; show binom2 _ * _ * _ ≤ 1 * _; rw [binom2_eq, Nat.one_mul]; exact ho
  have hShift1 : RatBound.le ⟨(s.agree + s.foldK) ^ s.queryCount, s.domainSize ^ s.queryCount,
        Nat.pow_pos (Nat.two_pow_pos s.logDomain)⟩ ⟨3, 2 ^ 267, Nat.two_pow_pos 267⟩ := by
    show (s.agree + s.foldK) ^ s.queryCount * 2 ^ 267 ≤ 3 * s.domainSize ^ s.queryCount
    have hPow := Nat.pow_le_pow_left hRatio s.queryCount
    rw [Nat.mul_pow, Nat.mul_pow] at hPow
    have hMul : ((s.agree + s.foldK) ^ s.queryCount * 2 ^ 267) * 4096 ^ s.queryCount ≤
        (3 * s.domainSize ^ s.queryCount) * 4096 ^ s.queryCount := by
      calc ((s.agree + s.foldK) ^ s.queryCount * 2 ^ 267) * 4096 ^ s.queryCount
          = ((s.agree + s.foldK) ^ s.queryCount * 4096 ^ s.queryCount) * 2 ^ 267 := by
              simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        _ ≤ ((shiftCapNum s.queryCount) ^ s.queryCount * s.domainSize ^ s.queryCount) * 2 ^ 267 :=
              Nat.mul_le_mul_right _ hPow
        _ = ((shiftCapNum s.queryCount) ^ s.queryCount * 2 ^ 267) * s.domainSize ^ s.queryCount := by
              simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        _ ≤ (3 * 4096 ^ s.queryCount) * s.domainSize ^ s.queryCount :=
              Nat.mul_le_mul_right _ (shiftCapNum_pow_ok hQt)
        _ = (3 * s.domainSize ^ s.queryCount) * 4096 ^ s.queryCount := by
              simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    exact nat_le_of_mul_le_mul_right' hMul (Nat.pow_pos (by decide : 0 < 4096))
  have hShift2 : RatBound.le ⟨s.listSize * (s.queryCount + s.oodCount), q, hq⟩
      ⟨1, 2 ^ 267, Nat.two_pow_pos 267⟩ := by
    show _ ≤ 1 * q; rw [Nat.one_mul]; exact hComb
  have h3Plus1 : RatBound.le
      (RatBound.add ⟨3, 2 ^ 267, Nat.two_pow_pos 267⟩ ⟨1, 2 ^ 267, Nat.two_pow_pos 267⟩)
      (RatBound.invPow2 265) := by decide +kernel
  have hShift : RatBound.le (s.shiftBound q hq) (RatBound.invPow2 265) := by
    rw [WhirStage.shiftBound_eq]; exact RatBound.le_trans (RatBound.add_le_add hShift1 hShift2) h3Plus1
  rw [WhirStage.roundBounds_eq]; unfold stageRounds; rw [replicate_add_local _ s.foldK 2]
  refine RBoundsLe.append ?_ (.cons hOod (.cons hShift .nil))
  induction s.foldK with | zero => exact .nil | succ _ ih => exact .cons hFold ih

private theorem stages_cover_replicate265 (q : Nat) (hq : 0 < q) :
    ∀ (stages : List WhirStage), stages.all (checkStageFast265 q) = true →
      RBoundsLe (stagesRoundBounds q hq stages)
        (List.replicate (roundsOf stages) (RatBound.invPow2 265))
  | [], _ => by rw [stagesRoundBounds_nil]; exact .nil
  | s :: rest, hAll => by
    rw [List.all_cons, Bool.and_eq_true] at hAll
    rw [stagesRoundBounds_cons]
    unfold roundsOf
    rw [replicate_add_local _ (stageRounds s) (roundsOf rest)]
    exact RBoundsLe.append (stage_covers_replicate265 q hq s hAll.1)
      (stages_cover_replicate265 q hq rest hAll.2)

private theorem all_prod_stages_cover_265 (logCells : Nat)
    (hLo : 16 ≤ logCells) (hHi : logCells ≤ 28) :
    (zkHemV2ProdStages logCells).all (checkStageFast265 quinticGoldilocksCard) = true := by
  have hCases : logCells = 16 ∨ logCells = 17 ∨ logCells = 18 ∨ logCells = 19 ∨ logCells = 20 ∨
      logCells = 21 ∨ logCells = 22 ∨ logCells = 23 ∨ logCells = 24 ∨ logCells = 25 ∨
      logCells = 26 ∨ logCells = 27 ∨ logCells = 28 := by omega
  rcases hCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide +kernel

private theorem sumList_replicate_le_scale (b : RatBound) :
    ∀ r : Nat, RatBound.le (RatBound.sumList (List.replicate r b)) ⟨r * b.num, b.den, b.h_pos⟩
  | 0 => by show 0 * b.den ≤ 0 * b.num * 1; simp
  | r + 1 => by
    have ih := sumList_replicate_le_scale b r
    let sr := RatBound.sumList (List.replicate r b)
    show (b.num * sr.den + sr.num * b.den) * b.den ≤ ((r + 1) * b.num) * (b.den * sr.den)
    calc (b.num * sr.den + sr.num * b.den) * b.den
        ≤ (b.num * sr.den + r * b.num * sr.den) * b.den :=
          Nat.mul_le_mul_right b.den (Nat.add_le_add_left ih _)
      _ = ((r + 1) * b.num) * (b.den * sr.den) := by
          rw [Nat.succ_mul, Nat.add_comm (r * b.num) b.num, Nat.add_mul, Nat.add_mul]
          have e1 : b.num * sr.den * b.den = b.num * (b.den * sr.den) := by
            simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
          have e2 : r * b.num * sr.den * b.den = r * b.num * (b.den * sr.den) := by
            simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
          rw [e1, e2]

private theorem zkHemV2ProdSched_numRounds_le_28 (logCells : Nat)
    (hLo : 16 ≤ logCells) (hHi : logCells ≤ 28) :
    (zkHemV2ProdSched logCells).numRounds ≤ 28 := by
  have hCases : logCells = 16 ∨ logCells = 17 ∨ logCells = 18 ∨ logCells = 19 ∨ logCells = 20 ∨
      logCells = 21 ∨ logCells = 22 ∨ logCells = 23 ∨ logCells = 24 ∨ logCells = 25 ∨
      logCells = 26 ∨ logCells = 27 ∨ logCells = 28 := by omega
  rcases hCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide +kernel

/-- Production `zk-Hem v2` + DKT26 `< 2^{-128}` QROM + 400-bit Merkle bound (`logCells ∈ [16, 28]`, `Q ≤ 2^64`). -/
theorem zkHemV2_prod_qrom_error_lt_128_at_2pow64 (logCells Q : Nat)
    (hLo : 16 ≤ logCells) (hHi : logCells ≤ 28) (hQ : Q ≤ 2 ^ 64) :
    RatBound.lt
      (RatBound.add (scheduleQromError (zkHemV2ProdSched logCells) Q) (merkle400QromBound Q))
      (RatBound.invPow2 128) := by
  have hMonoQ := RatBound.add_le_add
    (scheduleQromError_mono (zkHemV2ProdSched logCells) hQ) (merkle400QromBound_mono hQ)
  have hCov := stages_cover_replicate265 quinticGoldilocksCard quinticGoldilocksCard_pos
    (zkHemV2ProdStages logCells) (all_prod_stages_cover_265 logCells hLo hHi)
  let b265 := dfmRoundScale (2 ^ 64) (RatBound.invPow2 265)
  have hEnv1 : RatBound.le (scheduleQromError (zkHemV2ProdSched logCells) (2 ^ 64))
      (RatBound.sumList (List.replicate (zkHemV2ProdSched logCells).numRounds b265)) := by
    rw [← List.map_replicate, scheduleQromError_eq, WhirVerifierSchedule.roundBounds_eq]
    exact scaled_sum_mono_v2 (2 ^ 64) hCov
  have hEnv2 := sumList_replicate_le_scale b265 (zkHemV2ProdSched logCells).numRounds
  have hEnv3 : RatBound.le
      ⟨(zkHemV2ProdSched logCells).numRounds * b265.num, b265.den, b265.h_pos⟩
      ⟨28 * b265.num, b265.den, b265.h_pos⟩ := by
    show (zkHemV2ProdSched logCells).numRounds * b265.num * b265.den ≤ 28 * b265.num * b265.den
    exact Nat.mul_le_mul_right _
      (Nat.mul_le_mul_right _ (zkHemV2ProdSched_numRounds_le_28 logCells hLo hHi))
  have hCap28 : RatBound.lt
      (RatBound.add ⟨28 * b265.num, b265.den, b265.h_pos⟩ (merkle400QromBound (2 ^ 64)))
      (RatBound.invPow2 128) := by
    dsimp only [b265]; decide +kernel
  exact ratBound_lt_of_le_of_lt
    (RatBound.le_trans hMonoQ
      (RatBound.add_le_add (RatBound.le_trans hEnv1 (RatBound.le_trans hEnv2 hEnv3))
        (RatBound.le_refl _)))
    hCap28

/-- `[CDHZ25]` QROM total error formula (`320 (Q + k + 1)(Q + k) ε_rbr + 6680 Q^3 / 2^400`). -/
def cdhz25TotalQromBound (Q k : Nat) (epsRbr : RatBound) : RatBound :=
  RatBound.add ⟨320 * (Q + k + 1) * (Q + k) * epsRbr.num, epsRbr.den, epsRbr.h_pos⟩ (merkle400QromBound Q)

theorem zkHemV2_cdhz25_qrom_lt_128_at_2pow64 {Q k : Nat} {epsRbr : RatBound}
    (hQ : Q ≤ 2 ^ 64) (hk : k ≤ 100) (hRbr : RatBound.le epsRbr (RatBound.invPow2 265)) :
    RatBound.lt (cdhz25TotalQromBound Q k epsRbr) (RatBound.invPow2 128) := by
  have hTerm1 : RatBound.le
      ⟨320 * (Q + k + 1) * (Q + k) * epsRbr.num, epsRbr.den, epsRbr.h_pos⟩
      ⟨320 * (2 ^ 64 + 101) * (2 ^ 64 + 100), 2 ^ 265, Nat.two_pow_pos 265⟩ := by
    show 320 * (Q + k + 1) * (Q + k) * epsRbr.num * 2 ^ 265 ≤
      320 * (2 ^ 64 + 101) * (2 ^ 64 + 100) * epsRbr.den
    have hc : 320 * (Q + k + 1) * (Q + k) ≤ 320 * (2 ^ 64 + 101) * (2 ^ 64 + 100) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 320 (by omega)) (by omega)
    have hr : epsRbr.num * 2 ^ 265 ≤ epsRbr.den := by
      have h1 : epsRbr.num * 2 ^ 265 ≤ 1 * epsRbr.den := hRbr
      rwa [Nat.one_mul] at h1
    rw [Nat.mul_assoc (320 * (Q + k + 1) * (Q + k))]; exact Nat.mul_le_mul hc hr
  have hMono := RatBound.add_le_add hTerm1 (merkle400QromBound_mono hQ)
  have hTop : RatBound.lt
      (RatBound.add ⟨320 * (2 ^ 64 + 101) * (2 ^ 64 + 100), 2 ^ 265, Nat.two_pow_pos 265⟩
        (merkle400QromBound (2 ^ 64)))
      (RatBound.invPow2 128) := by decide +kernel
  exact ratBound_lt_of_le_of_lt hMono hTop

/-- Composed succinct-transcript QROM + 400-bit Merkle soundness `< 2^{-128}` (`logCells ∈ [16, 28]`, `Q ≤ 2^64`). -/
theorem zkHemV2_deployed_succinct_qrom_soundness_128 {D : Type} [DecidableEq D]
    {cardX cardAnc Q : Nat} (logCells : Nat)
    (hLo : 16 ≤ logCells) (hHi : logCells ≤ 28) (hQ : Q ≤ 2 ^ 64)
    (env : WhirEnv QuinticGoldilocks) (M : MerkleSetup D QuinticGoldilocks) (dfltRoot : D)
    (sc : WhirScheduleCert env (zkHemV2ProdSched logCells) 400)
    (codec : FsCodec (SuccinctRoundMsg D (WhirPub QuinticGoldilocks))
      (zkHemV2ProdSched logCells).numRounds cardX)
    (aux : Fin cardX → List (QuinticGoldilocks × List D))
    (claim : QuinticGoldilocks) (initRoots : Nat → D)
    (tblOf : Nat → D → Nat → QuinticGoldilocks)
    (hx : ¬ whirInLang env (zkHemV2ProdSched logCells)
      ((whirSuccinctBridge env (zkHemV2ProdSched logCells) 400 dfltRoot).liftStmt
        claim initRoots tblOf))
    (hRoots : ∀ (H : Fin cardX → BitVec 400) (o : Fin cardX),
      succinctFsAccept (whirOracleIop env (zkHemV2ProdSched logCells) 400)
        (whirSuccinctBridge env (zkHemV2ProdSched logCells) 400 dfltRoot)
        M codec aux claim initRoots H o = true →
      let str := fsTranscript codec H (codec.dec o)
      ∀ q ∈ (whirOracleIop env (zkHemV2ProdSched logCells) 400).queries claim
          (str.map (fun sc' => (sc'.1.pub, sc'.2))),
        M.root q.1 ((whirOracleIop env (zkHemV2ProdSched logCells) 400).depth q.1)
          (tblOf q.1 ((whirSuccinctBridge env (zkHemV2ProdSched logCells) 400 dfltRoot).rootsOf
            initRoots (str.map Prod.fst) q.1)) =
          (whirSuccinctBridge env (zkHemV2ProdSched logCells) 400 dfltRoot).rootsOf
            initRoots (str.map Prod.fst) q.1)
    (A : QuantumAdv cardX 400 cardAnc Q)
    (hMerkle : RatBound.le
      ⟨uniformOracleSum 400 cardX (fun H =>
          QVec.queryMassOn
            (succinctFsCollisionEvent (whirOracleIop env (zkHemV2ProdSched logCells) 400)
              (whirSuccinctBridge env (zkHemV2ProdSched logCells) 400 dfltRoot)
              M codec aux claim initRoots tblOf H)
            (runQuantumAdv A H)),
        (2 ^ 400) ^ cardX * (prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init),
        Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos 400))
          (Nat.mul_pos (prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩
      (merkle400QromBound Q)) :
    RatBound.lt
      ⟨uniformOracleSum 400 cardX (fun H =>
          QVec.queryMassOn
            (succinctFsAccept (whirOracleIop env (zkHemV2ProdSched logCells) 400)
              (whirSuccinctBridge env (zkHemV2ProdSched logCells) 400 dfltRoot)
              M codec aux claim initRoots H)
            (runQuantumAdv A H)),
        (2 ^ 400) ^ cardX * (prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init),
        Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos 400))
          (Nat.mul_pos (prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩
      (RatBound.invPow2 128) := by
  let sched := zkHemV2ProdSched logCells
  have hRbr : RatBound.le
      ⟨(2 * Q + 1) ^ 2 * qsum sched.numRounds sc.cert.bad, 2 ^ 400, Nat.two_pow_pos 400⟩
      (scheduleQromError sched Q) := by
    rw [scheduleQromError_eq]
    exact dfm_sum_le Q 400 sched.numRounds sc.cert.bad sched.roundBounds
      sched.roundBounds_length sc.covers
  have hBudget := succinct_fs_qrom_total_error_budget
    (whirOracleIop env sched 400) (whirSuccinctBridge env sched 400 dfltRoot)
    M sc.cert codec aux claim initRoots tblOf hx hRoots A
    (scheduleQromError sched Q) (merkle400QromBound Q) hRbr hMerkle
  exact ratBound_lt_of_le_of_lt hBudget
    (zkHemV2_prod_qrom_error_lt_128_at_2pow64 logCells Q hLo hHi hQ)

/-- 32B `tree_nonce` Stage-0 Canopy disjointness and `< 2^{-128}` multi-proof bound (`P ≤ 2^64`). -/
theorem zkHemV2_treeNonce_disjoint_and_multiproof_128 {cardX w P : Nat}
    (L : SaltedCanopyLayout (2 ^ 256) cardX w) {s₁ s₂ : Fin (2 ^ 256)} (hNe : s₁ ≠ s₂)
    (l₁ n₁ l₂ n₂ : Nat) (u₁ v₁ u₂ v₂ : BitVec w)
    (hl₁ : l₁ < L.levels) (hn₁ : n₁ < L.nodes) (hl₂ : l₂ < L.levels) (hn₂ : n₂ < L.nodes)
    (hP : P ≤ 2 ^ 64) :
    L.encode s₁ l₁ n₁ u₁ v₁ ≠ L.encode s₂ l₂ n₂ u₂ v₂ ∧
    RatBound.lt ⟨P * P, 2 ^ 257, Nat.two_pow_pos 257⟩ (RatBound.invPow2 128) := by
  refine ⟨saltedCanopy_cross_salt_disjoint L hNe l₁ n₁ l₂ n₂ u₁ v₁ u₂ v₂ hl₁ hn₁ hl₂ hn₂, ?_⟩
  show P * P * 2 ^ 128 < 1 * 2 ^ 257
  have hCap : 2 ^ 64 * 2 ^ 64 * 2 ^ 128 < 1 * 2 ^ 257 := by decide +kernel
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.mul_le_mul hP hP)) hCap

/-- `#tooth` Legacy `v1` 256-bit digests (`85`-bit QROM wall) violate `< 2^{-128}` at `Q = 2^64`. -/
theorem tooth_v1_256bit_digest_violates_qrom_128_at_2pow64 (logCells : Nat) :
    ¬ RatBound.lt (RatBound.add (scheduleQromError (zkHemV2ProdSched logCells) (2 ^ 64))
        (merkle256QromBound (2 ^ 64))) (RatBound.invPow2 128) := by
  intro hLt
  have hMerLe : RatBound.le (merkle256QromBound (2 ^ 64))
      (RatBound.add (scheduleQromError (zkHemV2ProdSched logCells) (2 ^ 64))
        (merkle256QromBound (2 ^ 64))) := by
    let s := scheduleQromError (zkHemV2ProdSched logCells) (2 ^ 64); let m := merkle256QromBound (2 ^ 64)
    show m.num * (s.den * m.den) ≤ (s.num * m.den + m.num * s.den) * m.den
    have h1 : m.num * (s.den * m.den) = (m.num * s.den) * m.den := by
      simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    rw [h1]; exact Nat.mul_le_mul_right m.den (Nat.le_add_left _ _)
  have hMerLt := ratBound_lt_of_le_of_lt hMerLe hLt
  revert hMerLt; unfold merkle256QromBound; decide +kernel

theorem goldilocksPrime_pos_v2 : 0 < goldilocksPrime := by decide
def zkHemV2BaseFieldMutSched (logCells : Nat) : WhirVerifierSchedule :=
  ⟨logCells, goldilocksPrime, goldilocksPrime_pos_v2, zkHemV2ProdStages logCells⟩

/-- `#tooth` Base-field `Goldilocks` challenges violate `< 2^{-128}` QROM soundness at `Q = 2^64`. -/
theorem tooth_base_field_challenges_violate_qrom_128 :
    ¬ RatBound.lt (RatBound.add (scheduleQromError (zkHemV2BaseFieldMutSched 17) (2 ^ 64))
        (merkle400QromBound (2 ^ 64))) (RatBound.invPow2 128) := by
  intro hLt
  let st0 : WhirStage := ⟨5, 14, 2, 5, 267, 4097, 8203, 1, 2048, 2048, 17, 23519292652270⟩
  have hFold0Le : RatBound.le (dfmRoundScale (2 ^ 64) (st0.foldBound goldilocksPrime goldilocksPrime_pos_v2))
      (RatBound.add (scheduleQromError (zkHemV2BaseFieldMutSched 17) (2 ^ 64)) (merkle400QromBound (2 ^ 64))) := by
    have hHeadLe : ∀ (b : RatBound) (bs : List RatBound), RatBound.le b (RatBound.sumList (b :: bs)) := fun b bs => by
      let r := RatBound.sumList bs; show b.num * (b.den * r.den) ≤ (b.num * r.den + r.num * b.den) * b.den
      have e : b.num * (b.den * r.den) = (b.num * r.den) * b.den := by
        simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      rw [e]; exact Nat.mul_le_mul_right b.den (Nat.le_add_right _ _)
    have hAddLeft : ∀ (a b : RatBound), RatBound.le a (RatBound.add a b) := fun a b => by
      show a.num * (a.den * b.den) ≤ (a.num * b.den + b.num * a.den) * a.den
      have e : a.num * (a.den * b.den) = (a.num * b.den) * a.den := by
        simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      rw [e]; exact Nat.mul_le_mul_right a.den (Nat.le_add_right _ _)
    have hSchedEq : (scheduleQromError (zkHemV2BaseFieldMutSched 17) (2 ^ 64)) =
        RatBound.sumList (dfmRoundScale (2 ^ 64) (st0.foldBound goldilocksPrime goldilocksPrime_pos_v2) ::
          ((List.replicate 4 (st0.foldBound goldilocksPrime goldilocksPrime_pos_v2) ++
            [st0.oodBound goldilocksPrime goldilocksPrime_pos_v2,
             st0.shiftBound goldilocksPrime goldilocksPrime_pos_v2] ++
            stagesRoundBounds goldilocksPrime goldilocksPrime_pos_v2 ((zkHemV2ProdStages 17).drop 1)).map
            (dfmRoundScale (2 ^ 64)))) := by
      have hSt17 : zkHemV2ProdStages 17 = st0 :: (zkHemV2ProdStages 17).drop 1 := rfl
      rw [scheduleQromError_eq, WhirVerifierSchedule.roundBounds_eq]
      unfold zkHemV2BaseFieldMutSched; dsimp only
      rw [hSt17, stagesRoundBounds_cons, WhirStage.roundBounds_eq]; rfl
    rw [hSchedEq]
    exact RatBound.le_trans (hHeadLe _ _) (hAddLeft _ _)
  have hBad := ratBound_lt_of_le_of_lt hFold0Le hLt
  rw [WhirStage.foldBound_eq] at hBad
  revert hBad; unfold dfmRoundScale; dsimp only [st0]; decide +kernel

theorem inhabited_zkHemV2_prod_qrom_128 :
    ∃ logCells Q : Nat, 16 ≤ logCells ∧ logCells ≤ 28 ∧ Q ≤ 2 ^ 64 ∧
      (zkHemV2ProdSched logCells).johnsonOk = true :=
  ⟨20, 2 ^ 64, by decide, by decide, Nat.le_refl _, by decide +kernel⟩

#verify_kernel
  Qsag.ZkHemV2Cert.zkHemV2QuinticCert

#verify_constructive
  Qsag.toom3MulFp5_eq_quinticMul
  Qsag.tooth_toom3_wrong_reduction_ne_quinticMul
  Qsag.ZkHemV2Cert.ringDot_maskLine
  Qsag.ZkHemV2Cert.v2_maskLine_linForm_false_pair_bad_challenges_le_one
  Qsag.ZkHemV2Cert.v2_maskLine_false_pair_bad_challenges_le_one
  Qsag.ZkHemV2Cert.v2_maskLine_claim_bad_count_le_pairs
  Qsag.ZkHemV2Cert.dkt26_threshold_inside_johnson
  Qsag.ZkHemV2Cert.dkt26_at_28_clears_265
  Qsag.ZkHemV2Cert.tooth_bcgm25_deg7_mask_line_fails_at_28
  Qsag.ZkHemV2Cert.quinticCoset64_nodup
  Qsag.ZkHemV2Cert.zkHemV2QuinticSched_johnsonOk
  Qsag.ZkHemV2Cert.zkHemV2Quintic_honest_accepts
  Qsag.ZkHemV2Cert.zkHemV2Quintic_false_not_inLang
  Qsag.ZkHemV2Cert.zkHemV2Quintic_qrom_lt_128_at_2pow28
  Qsag.ZkHemV2Cert.zkHemV2Stage0Queries_table
  Qsag.ZkHemV2Cert.zkHemV2ProdStages_dkt26_exact
  Qsag.ZkHemV2Cert.zkHemV2ProdSched_johnsonOk
  Qsag.ZkHemV2Cert.zkHemV2_prod_qrom_error_lt_128_at_2pow64
  Qsag.ZkHemV2Cert.zkHemV2_cdhz25_qrom_lt_128_at_2pow64
  Qsag.ZkHemV2Cert.zkHemV2_deployed_succinct_qrom_soundness_128
  Qsag.ZkHemV2Cert.zkHemV2_treeNonce_disjoint_and_multiproof_128
  Qsag.ZkHemV2Cert.tooth_v1_256bit_digest_violates_qrom_128_at_2pow64
  Qsag.ZkHemV2Cert.tooth_base_field_challenges_violate_qrom_128
  Qsag.ZkHemV2Cert.inhabited_zkHemV2_prod_qrom_128

#verify_inhabited
  Qsag.ZkHemV2Cert.zkHemV2_prod_qrom_error_lt_128_at_2pow64
  Qsag.ZkHemV2Cert.inhabited_zkHemV2_prod_qrom_128

#tooth_pair Qsag.toom3MulFp5_eq_quinticMul vs
  Qsag.tooth_toom3_wrong_reduction_ne_quinticMul
#tooth_pair Qsag.ZkHemV2Cert.zkHemV2ProdStages_dkt26_exact vs
  Qsag.ZkHemV2Cert.tooth_bcgm25_deg7_mask_line_fails_at_28
#tooth_pair Qsag.ZkHemV2Cert.zkHemV2Quintic_honest_accepts vs
  Qsag.ZkHemV2Cert.zkHemV2Quintic_false_not_inLang
#tooth_pair Qsag.ZkHemV2Cert.zkHemV2_prod_qrom_error_lt_128_at_2pow64 vs
  Qsag.ZkHemV2Cert.tooth_v1_256bit_digest_violates_qrom_128_at_2pow64
#tooth_pair Qsag.ZkHemV2Cert.zkHemV2_prod_qrom_error_lt_128_at_2pow64 vs
  Qsag.ZkHemV2Cert.tooth_base_field_challenges_violate_qrom_128

end Qsag.ZkHemV2Cert
end

public section
namespace Qsag.ZkHemV2Cert
#export_eqns zkHemV2ProdStages zkHemV2ProdSched dkt26Covers
end Qsag.ZkHemV2Cert
end
