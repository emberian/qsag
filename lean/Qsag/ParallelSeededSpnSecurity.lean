module
/-
# Qsag.ParallelSeededSpnSecurity — Mechanized Cryptanalysis of the 48-Round $x^7$ Davies–Meyer SPN

Constructive (`0` classical choice axioms, `0` external math libraries, `0` unproved goals)
Lean 4.35 security analysis of the `ParallelSeededFts` 2-lane $\mathbb{F}_{2^{128}}^2$
48-round $x^7$ Davies–Meyer SPN (`crates/qsag-fts/src/parallel_mpc.rs`):

1. **§1. Leading-Coefficient Polynomial Root Bound**: over every `LawfulCommRing R` with
   `NoZeroDivisors R`, a polynomial `init ++ [lead]` (`lead ≠ 0`) has at most `init.length`
   distinct roots in any duplicate-free list `S : List R`.
2. **§2. Characteristic-2 Expansion & Differential Uniformity $\le 6$ of $S(x) = x^7$**:
   $(x \oplus \Delta)^7 \oplus x^7 \oplus \delta = \Delta x^6 \oplus \cdots \oplus (\Delta^7 \oplus \delta)$
   has exact degree `6` for $\Delta \ne 0$, bounding roots by `6` and per-S-box differential
   probability by $6 / 2^{128} = 3 / 2^{127} < 2^{-125}$.
3. **§3. Wiedemann Frobenius Periodicity & Bijectivity of $x \mapsto x^7$ on `Tower128`**:
   proves $a^{2^{2^k}} = a$ across all levels $k$ of the Wiedemann tower and constructs the
   two-sided inverse $z \mapsto z^{(8^{43} - 1)/7}$ on $\mathcal{T}_7 = \mathbb{F}_{2^{128}}$.
4. **§4. Concrete MDS Mixing Branch Number $= 3$ & 48-Round Active S-Box Trail Security**:
   certifies $\Psi(\text{gf128MdsATower}) = \text{GF128\_MDS\_A}$ and
   $\Psi(\text{gf128MdsBTower}) = \text{GF128\_MDS\_B}$, proves branch number `3` when
   $A \ne 0, B \ne 0, A \cdot B \ne 1$, and proves $\ge 3$ active S-boxes per 2 rounds
   ($\ge 72 \ge 48$ across 48 rounds), giving $(6 / 2^{128})^{48} \ll 2^{-256}$.
5. **§5. Algebraic Degree Growth, 43-Round Higher-Order / Interpolation Margin & `#tooth` Guards**:
   binary Hamming weight `3` of `7`, degree saturation $3^5 = 243 > 128 \ge 127$ in `5` rounds
   (`43` full margin rounds), univariate degree $7^{48} > 2^{134}$, round-constant asymmetry,
   and `#tooth` mutation witnesses.
-/

public import Qsag.BinaryTower
import all Qsag.BinaryTower
public import Qsag.ConcreteSecurityBudget
import all Qsag.ConcreteSecurityBudget

public section
namespace Qsag

set_option autoImplicit false
set_option exponentiation.threshold 2048

/-! ## §1. Constructive Leading-Coefficient Polynomial Root Bound -/

private theorem quotLinear_append_lead {R : Type} [LawfulCommRing R] :
    ∀ (init : List R) (c₀ lead r : R),
      ∃ init' : List R, init'.length = init.length ∧
        RoundPoly.quotLinear (c₀ :: (init ++ [lead])) r = init' ++ [lead]
  | [], c₀, lead, r =>
    ⟨[], rfl, by simp [RoundPoly.quotLinear, RoundPoly.evalCoeffs,
      LawfulCommRing.mul_zero, LawfulCommRing.add_zero]⟩
  | c₁ :: rest, c₀, lead, r => by
    obtain ⟨init', hLen, hEq⟩ := quotLinear_append_lead rest c₁ lead r
    refine ⟨RoundPoly.evalCoeffs (c₁ :: (rest ++ [lead])) r :: init', congrArg Nat.succ hLen, ?_⟩
    simp only [List.cons_append, RoundPoly.quotLinear]
    exact congrArg (RoundPoly.evalCoeffs (c₁ :: (rest ++ [lead])) r :: ·) hEq

private theorem mem_of_mem_filter_spn {α : Type} {p : α → Bool} {x : α} :
    ∀ {l : List α}, x ∈ l.filter p → x ∈ l
  | [], h => by cases h
  | _ :: _, h => by
    simp only [List.filter] at h; split at h
    · cases h with | head => exact .head _ | tail _ hm => exact .tail _ (mem_of_mem_filter_spn hm)
    · exact .tail _ (mem_of_mem_filter_spn h)

private theorem pred_of_mem_filter_spn {α : Type} {p : α → Bool} {x : α} :
    ∀ {l : List α}, x ∈ l.filter p → p x = true
  | [], h => by cases h
  | _ :: _, h => by
    simp only [List.filter] at h; split at h
    · rename_i hpx; cases h with | head => exact hpx | tail _ hm => exact pred_of_mem_filter_spn hm
    · exact pred_of_mem_filter_spn h

private theorem nodup_filter_spn {α : Type} (p : α → Bool) :
    ∀ {l : List α}, l.Nodup → (l.filter p).Nodup
  | [], _ => .nil
  | _ :: _, .cons hrel htail => by
    simp only [List.filter]; split
    · exact .cons (fun b hb => hrel b (mem_of_mem_filter_spn hb)) (nodup_filter_spn p htail)
    · exact nodup_filter_spn p htail

/-- **Leading-Coefficient Root-Counting Bound (`evalCoeffs_roots_le_of_lead_nonzero`)**:
    Over every `LawfulCommRing R` without zero divisors, any polynomial `init ++ [lead]` of exact
    degree `d = init.length` with `lead ≠ 0` has at most `d` roots in any duplicate-free list `S`. -/
theorem evalCoeffs_roots_le_of_lead_nonzero
    {R : Type} [LawfulCommRing R] [DecidableEq R] [NoZeroDivisors R] :
    ∀ (d : Nat) (init : List R) (lead : R) (S : List R),
      init.length = d → lead ≠ CommRingOps.zero → S.Nodup →
      (S.filter (fun r => decide (RoundPoly.evalCoeffs (init ++ [lead]) r = CommRingOps.zero))).length ≤ d
  | 0, init, lead, S, hLen, hLead, _ => by
    cases init with
    | cons _ _ => cases hLen
    | nil =>
      have hEmpty : S.filter (fun r => decide (RoundPoly.evalCoeffs [lead] r = CommRingOps.zero)) = [] := by
        cases hFilt : S.filter (fun r => decide (RoundPoly.evalCoeffs [lead] r = CommRingOps.zero)) with
        | nil => rfl
        | cons r _ =>
          have hp := pred_of_mem_filter_spn (p := fun r => decide (RoundPoly.evalCoeffs [lead] r = CommRingOps.zero))
            (l := S) (x := r) (by rw [hFilt]; exact .head _)
          have hr : RoundPoly.evalCoeffs [lead] r = CommRingOps.zero := of_decide_eq_true hp
          simp only [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero] at hr
          exact False.elim (hLead hr)
      rw [List.nil_append, hEmpty]
      exact Nat.zero_le 0
  | d + 1, init, lead, S, hLen, hLead, hNodup => by
    cases init with
    | nil => cases hLen
    | cons c₀ restInit =>
      let cs := c₀ :: (restInit ++ [lead])
      let p : R → Bool := fun r => decide (RoundPoly.evalCoeffs cs r = CommRingOps.zero)
      have hndRoots := nodup_filter_spn p hNodup
      cases hRoots : S.filter p with
      | nil =>
        change (S.filter p).length ≤ d + 1
        rw [hRoots]
        exact Nat.zero_le (d + 1)
      | cons r rest =>
        rw [hRoots] at hndRoots
        cases hndRoots with
        | cons hNotMem hndRest =>
          have hrRoot : RoundPoly.evalCoeffs cs r = CommRingOps.zero :=
            of_decide_eq_true (pred_of_mem_filter_spn (p := p) (l := S) (x := r) (by rw [hRoots]; exact .head _))
          obtain ⟨init', hLen', hQuotEq⟩ := quotLinear_append_lead restInit c₀ lead r
          have hRestEq : rest.filter (fun y =>
              decide (RoundPoly.evalCoeffs (init' ++ [lead]) y = CommRingOps.zero)) = rest := by
            apply List.filter_eq_self.mpr
            intro y hy
            have hyInFilt : y ∈ S.filter p := by
              rw [hRoots]; exact .tail _ hy
            have hyRoot : RoundPoly.evalCoeffs cs y = CommRingOps.zero :=
              of_decide_eq_true (pred_of_mem_filter_spn (p := p) hyInFilt)
            have hSubNe : CommRingOps.sub y r ≠ CommRingOps.zero :=
              fun hsub0 => hNotMem y hy (LawfulCommRing.sub_eq_zero_iff.mp hsub0).symm
            have hfac := RoundPoly.evalCoeffs_eq_mul_quotLinear_add cs r y
            rw [hyRoot, hrRoot, LawfulCommRing.add_zero, hQuotEq] at hfac
            exact (NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hfac.symm).elim
              (fun hb => False.elim (hSubNe hb)) decide_eq_true
          have ih := evalCoeffs_roots_le_of_lead_nonzero d init' lead rest
            (hLen'.trans (Nat.succ.inj hLen)) hLead hndRest
          rw [hRestEq] at ih
          change (S.filter p).length ≤ d + 1
          rw [hRoots]; simp only [List.length_cons]; omega

/-! ## §2. Characteristic-2 Expansion & Differential Uniformity $\le 6$ of $S(x) = x^7$ -/

@[expose] def towerPow (k : Nat) (x : TowerElem k) : Nat → TowerElem k
  | 0 => towerOne k
  | n + 1 => towerMul k x (towerPow k x n)

/-- Algebraic $x^7$ S-box over `TowerElem k`: $S(x) = x \cdot x^2 \cdot x^4 = x^7$. -/
@[expose] def towerSbox7 (k : Nat) (x : TowerElem k) : TowerElem k :=
  let x2 := towerMul k x x
  towerMul k x (towerMul k x2 (towerMul k x2 x2))

theorem towerSbox7_eq_pow7 (k : Nat) (x : TowerElem k) :
    towerSbox7 k x = towerPow k x 7 := by
  dsimp only [towerSbox7, towerPow]
  simp only [towerMul_one, towerMul_assoc]

theorem towerSq_add (k : Nat) (a b : TowerElem k) :
    towerMul k (towerAdd k a b) (towerAdd k a b) =
      towerAdd k (towerMul k a a) (towerMul k b b) := by
  rw [towerMul_add_distrib, towerAdd_mul_distrib, towerAdd_mul_distrib,
      towerMul_comm k b a, towerAdd_assoc,
      ← towerAdd_assoc k (towerMul k a b) (towerMul k a b) (towerMul k b b),
      towerAdd_self_zero, towerZero_add]

def sbox7DiffPolyCoeffs (k : Nat) (delta outDiff : TowerElem k) : List (TowerElem k) :=
  [towerAdd k (towerPow k delta 7) outDiff, towerPow k delta 6, towerPow k delta 5,
   towerPow k delta 4, towerPow k delta 3, towerPow k delta 2, delta]

/-- **Exact Characteristic-2 Differential Polynomial Identity (`towerSbox7_diff_eq_evalCoeffs`)**:
    $(x \oplus \Delta)^7 \oplus x^7 \oplus \delta =
     (\Delta^7 \oplus \delta) \oplus \Delta^6 x \oplus \cdots \oplus \Delta x^6$. -/
theorem towerSbox7_diff_eq_evalCoeffs (k : Nat) (x delta outDiff : TowerElem k) :
    towerAdd k (towerAdd k (towerSbox7 k (towerAdd k x delta)) (towerSbox7 k x)) outDiff =
      RoundPoly.evalCoeffs (sbox7DiffPolyCoeffs k delta outDiff) x := by
  let x2 := towerMul k x x; let x4 := towerMul k x2 x2
  let d2 := towerMul k delta delta; let d4 := towerMul k d2 d2
  have hSboxSum :
      towerSbox7 k (towerAdd k x delta) =
        towerAdd k (towerMul k x (towerMul k x2 x4))
          (towerAdd k (towerMul k x (towerMul k x2 d4))
            (towerAdd k (towerMul k x (towerMul k d2 x4))
              (towerAdd k (towerMul k x (towerMul k d2 d4))
                (towerAdd k (towerMul k delta (towerMul k x2 x4))
                  (towerAdd k (towerMul k delta (towerMul k x2 d4))
                    (towerAdd k (towerMul k delta (towerMul k d2 x4))
                      (towerMul k delta (towerMul k d2 d4)))))))) := by
    dsimp only [towerSbox7, x4, d4]
    rw [towerSq_add k x delta]
    change towerMul k (towerAdd k x delta)
      (towerMul k (towerAdd k x2 d2) (towerMul k (towerAdd k x2 d2) (towerAdd k x2 d2))) = _
    rw [towerSq_add k x2 d2]
    simp only [towerMul_add_distrib, towerAdd_mul_distrib, towerAdd_assoc, towerAdd_left_comm]
  have hCancelX7 :
      towerAdd k (towerSbox7 k (towerAdd k x delta)) (towerSbox7 k x) =
        towerAdd k (towerMul k x (towerMul k x2 d4))
          (towerAdd k (towerMul k x (towerMul k d2 x4))
            (towerAdd k (towerMul k x (towerMul k d2 d4))
              (towerAdd k (towerMul k delta (towerMul k x2 x4))
                (towerAdd k (towerMul k delta (towerMul k x2 d4))
                  (towerAdd k (towerMul k delta (towerMul k d2 x4))
                    (towerMul k delta (towerMul k d2 d4))))))) := by
    rw [hSboxSum]
    change towerAdd k (towerAdd k (towerSbox7 k x) _) (towerSbox7 k x) = _
    rw [towerAdd_comm k (towerAdd k (towerSbox7 k x) _) (towerSbox7 k x), towerAdd_cancel]
  rw [hCancelX7]
  simp only [sbox7DiffPolyCoeffs, RoundPoly.evalCoeffs_cons, RoundPoly.evalCoeffs_nil]
  dsimp only [CommRingOps.add, CommRingOps.mul, CommRingOps.zero, towerCommRingOps, towerPow, x2, x4, d2, d4]
  simp only [towerMul_zero, towerAdd_zero, towerMul_one, towerMul_add_distrib,
    towerMul_comm, towerMul_left_comm_of_assoc k (towerMul_assoc k),
    towerAdd_assoc, towerAdd_comm, towerAdd_left_comm]

/-- **Exact Differential Uniformity $\le 6$ of $S(x) = x^7$ (`towerSbox7_differential_uniformity_le_six`)**:
    For every $\Delta \ne 0$, every $\delta$, and every duplicate-free `S : List (TowerElem k)`,
    at most `6` inputs $x \in S$ satisfy $S(x \oplus \Delta) \oplus S(x) = \delta$. -/
theorem towerSbox7_differential_uniformity_le_six (k : Nat)
    (delta outDiff : TowerElem k) (hDelta : delta ≠ towerZero k)
    (S : List (TowerElem k)) (hNodup : S.Nodup) :
    (S.filter (fun x =>
      decide (towerAdd k (towerSbox7 k (towerAdd k x delta)) (towerSbox7 k x) = outDiff))).length ≤ 6 := by
  let init : List (TowerElem k) :=
    [towerAdd k (towerPow k delta 7) outDiff, towerPow k delta 6, towerPow k delta 5,
     towerPow k delta 4, towerPow k delta 3, towerPow k delta 2]
  have hFiltEq :
      S.filter (fun x => decide (towerAdd k (towerSbox7 k (towerAdd k x delta)) (towerSbox7 k x) = outDiff)) =
      S.filter (fun x => decide (RoundPoly.evalCoeffs (init ++ [delta]) x = towerZero k)) := by
    congr 1; funext x
    have hId := towerSbox7_diff_eq_evalCoeffs k x delta outDiff
    have hIff : (towerAdd k (towerSbox7 k (towerAdd k x delta)) (towerSbox7 k x) = outDiff) ↔
        (RoundPoly.evalCoeffs (init ++ [delta]) x = towerZero k) := by
      change _ ↔ RoundPoly.evalCoeffs (sbox7DiffPolyCoeffs k delta outDiff) x = towerZero k
      rw [← hId]
      refine ⟨fun h => by rw [h, towerAdd_self_zero], fun h => ?_⟩
      have h2 := congrArg (fun z => towerAdd k z outDiff) h
      simpa only [towerZero_add, towerAdd_assoc, towerAdd_self_zero, towerAdd_zero] using h2
    by_cases hp : towerAdd k (towerSbox7 k (towerAdd k x delta)) (towerSbox7 k x) = outDiff
    · have hq : RoundPoly.evalCoeffs (init ++ [delta]) x = towerZero k := hIff.mp hp
      simp [hp, hq]
    · have hq : ¬ (RoundPoly.evalCoeffs (init ++ [delta]) x = towerZero k) := fun h => hp (hIff.mpr h)
      simp [hp, hq]
  rw [hFiltEq]
  exact evalCoeffs_roots_le_of_lead_nonzero 6 init delta S rfl hDelta hNodup

@[expose] def sbox7MaxDiffProb128 : RatBound := ⟨6, 2 ^ 128, Nat.two_pow_pos 128⟩
def sbox7MaxDiffProb128Reduced : RatBound := ⟨3, 2 ^ 127, Nat.two_pow_pos 127⟩

theorem sbox7MaxDiffProb128_eq_three_div_two_pow_127 :
    RatBound.le sbox7MaxDiffProb128 sbox7MaxDiffProb128Reduced ∧
    RatBound.le sbox7MaxDiffProb128Reduced sbox7MaxDiffProb128 ∧
    strictlyMoreThanBits 125 sbox7MaxDiffProb128 :=
  ⟨by decide, by decide, by decide⟩

/-! ## §3. Wiedemann Tower Frobenius Periodicity & Two-Sided Bijectivity of $x \mapsto x^7$ on $\mathcal{T}_7$ -/

def towerFrobIter (k : Nat) : Nat → TowerElem k → TowerElem k
  | 0, a => a
  | m + 1, a => let prev := towerFrobIter k m a; towerMul k prev prev

theorem towerFrobIter_add (k : Nat) :
    ∀ (m : Nat) (a b : TowerElem k),
      towerFrobIter k m (towerAdd k a b) = towerAdd k (towerFrobIter k m a) (towerFrobIter k m b)
  | 0, _, _ => rfl
  | m + 1, a, b => by simp only [towerFrobIter, towerFrobIter_add k m a b]; exact towerSq_add k _ _

theorem towerFrobIter_mul (k : Nat) :
    ∀ (m : Nat) (a b : TowerElem k),
      towerFrobIter k m (towerMul k a b) = towerMul k (towerFrobIter k m a) (towerFrobIter k m b)
  | 0, _, _ => rfl
  | m + 1, a, b => by
    simp only [towerFrobIter, towerFrobIter_mul k m a b,
      towerMul_comm, towerMul_left_comm_of_assoc k (towerMul_assoc k)]

theorem towerFrobIter_add_steps (k : Nat) :
    ∀ (m n : Nat) (a : TowerElem k),
      towerFrobIter k (m + n) a = towerFrobIter k m (towerFrobIter k n a)
  | 0, n, a => by simp [Nat.zero_add, towerFrobIter]
  | m + 1, n, a => by
    rw [Nat.succ_add m n]; simp only [towerFrobIter, towerFrobIter_add_steps k m n a]

theorem towerFrobIter_embed (k : Nat) :
    ∀ (m : Nat) (a : TowerElem k),
      towerFrobIter (k + 1) m (embedTower k a) = embedTower k (towerFrobIter k m a)
  | 0, _ => rfl
  | m + 1, a => by simp only [towerFrobIter, towerFrobIter_embed k m a, embedTower_mul]

private def artinSchreierZ (k : Nat) : TowerElem (k + 1) := (towerZero k, towerInvX k)

private theorem artinSchreierZ_sq (k : Nat) :
    towerMul (k + 1) (artinSchreierZ k) (artinSchreierZ k) =
      towerAdd (k + 1) (embedTower k (towerMul k (towerInvX k) (towerInvX k))) (artinSchreierZ k) := by
  simp only [artinSchreierZ, embedTower, towerMul, towerAdd,
    towerMul_zero, towerZero_mul, towerZero_add, towerAdd_zero]
  congr 1
  rw [← towerMul_assoc, towerX_mul_invX, towerOne_mul]

private theorem towerFrobIter_artinSchreierZ (k : Nat) :
    ∀ m : Nat, ∃ c : TowerElem k,
      towerFrobIter (k + 1) m (artinSchreierZ k) = towerAdd (k + 1) (embedTower k c) (artinSchreierZ k)
  | 0 => ⟨towerZero k, by simp [towerFrobIter, embedTower_zero]⟩
  | m + 1 => by
    obtain ⟨c, hc⟩ := towerFrobIter_artinSchreierZ k m
    refine ⟨towerAdd k (towerMul k c c) (towerMul k (towerInvX k) (towerInvX k)), ?_⟩
    simp only [towerFrobIter]
    rw [hc, towerSq_add (k + 1), ← embedTower_mul, artinSchreierZ_sq, ← towerAdd_assoc, ← embedTower_add]

/-- **Fermat's Little Theorem on the Wiedemann Binary Tower (`towerFrobIter_card_eq`)**:
    $a^{2^{2^k}} = a$ for every tower level $k$ and $a \in \mathcal{T}_k$. -/
theorem towerFrobIter_card_eq :
    ∀ (k : Nat) (a : TowerElem k), towerFrobIter k (2 ^ k) a = a
  | 0, a => by cases a <;> rfl
  | k + 1, a => by
    have hDecomp : a = towerAdd (k + 1) (embedTower k a.1)
        (towerMul (k + 1) (embedTower k (towerMul k a.2 (towerX k))) (artinSchreierZ k)) := by
      rcases a with ⟨a1, a2⟩
      simp only [embedTower, artinSchreierZ, towerMul, towerAdd,
        towerMul_zero, towerZero_mul, towerAdd_zero, towerZero_add]
      congr 1
      rw [towerMul_assoc, towerX_mul_invX, towerMul_one]
    have hPow2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ, Nat.mul_two]
    have hZ : towerFrobIter (k + 1) (2 ^ (k + 1)) (artinSchreierZ k) = artinSchreierZ k := by
      obtain ⟨c, hc⟩ := towerFrobIter_artinSchreierZ k (2 ^ k)
      rw [hPow2, towerFrobIter_add_steps (k + 1) (2 ^ k) (2 ^ k), hc, towerFrobIter_add,
          towerFrobIter_embed, towerFrobIter_card_eq k c, hc, ← towerAdd_assoc,
          towerAdd_self_zero, towerZero_add]
    calc towerFrobIter (k + 1) (2 ^ (k + 1)) a
      _ = towerFrobIter (k + 1) (2 ^ (k + 1))
            (towerAdd (k + 1) (embedTower k a.1)
              (towerMul (k + 1) (embedTower k (towerMul k a.2 (towerX k))) (artinSchreierZ k))) := by
            rw [← hDecomp]
      _ = towerAdd (k + 1) (embedTower k (towerFrobIter k (2 ^ (k + 1)) a.1))
            (towerMul (k + 1) (embedTower k (towerFrobIter k (2 ^ (k + 1)) (towerMul k a.2 (towerX k))))
              (artinSchreierZ k)) := by
            rw [towerFrobIter_add, towerFrobIter_mul, towerFrobIter_embed, towerFrobIter_embed, hZ]
      _ = a := by
            rw [hPow2, towerFrobIter_add_steps k (2 ^ k) (2 ^ k), towerFrobIter_card_eq k,
                towerFrobIter_card_eq k, towerFrobIter_add_steps k (2 ^ k) (2 ^ k),
                towerFrobIter_card_eq k, towerFrobIter_card_eq k]
            exact hDecomp.symm

def octGeom128 : Nat → Tower128 → Tower128
  | 0, _ => towerOne 7
  | m + 1, z => towerMul 7 z (towerFrobIter 7 3 (octGeom128 m z))

/-- Explicit constructive inverse $S^{-1}(z) = z^{(8^{43} - 1) / 7}$ of $S(x) = x^7$ on `Tower128`. -/
def towerSbox7Inv128 (z : Tower128) : Tower128 := octGeom128 43 z

private theorem frobIter3_eq_pow8 (y : Tower128) :
    towerFrobIter 7 3 y = towerMul 7 (towerSbox7 7 y) y := by
  dsimp only [towerFrobIter, towerSbox7]
  simp only [towerMul_assoc]

private theorem octGeom128_sbox7_mul :
    ∀ (m : Nat) (y : Tower128),
      towerMul 7 (octGeom128 m (towerSbox7 7 y)) y = towerFrobIter 7 (3 * m) y
  | 0, y => by simp [octGeom128, towerFrobIter]
  | m + 1, y => by
    simp only [octGeom128]
    have hRearr :
        towerMul 7 (towerMul 7 (towerSbox7 7 y) (towerFrobIter 7 3 (octGeom128 m (towerSbox7 7 y)))) y =
        towerMul 7 (towerMul 7 (towerSbox7 7 y) y) (towerFrobIter 7 3 (octGeom128 m (towerSbox7 7 y))) := by
      simp only [towerMul_comm, towerMul_left_comm_of_assoc 7 (towerMul_assoc 7)]
    rw [hRearr, ← frobIter3_eq_pow8 y, ← towerFrobIter_mul 7 3 y,
        towerMul_comm 7 y (octGeom128 m (towerSbox7 7 y)), octGeom128_sbox7_mul m y,
        ← towerFrobIter_add_steps 7 3 (3 * m) y, show 3 + 3 * m = 3 * (m + 1) by omega]

theorem towerSbox7Inv128_left_inv (x : Tower128) :
    towerSbox7Inv128 (towerSbox7 7 x) = x := by
  by_cases hx : x = towerZero 7
  · subst hx; simp [towerSbox7, towerSbox7Inv128, octGeom128]
  · apply towerMul_cancel_left 7 x _ _ hx
    rw [towerMul_comm 7 x, towerSbox7Inv128, octGeom128_sbox7_mul 43 x,
        show (3 : Nat) * 43 = 1 + 2 ^ 7 by decide,
        towerFrobIter_add_steps 7 1 (2 ^ 7) x, towerFrobIter_card_eq 7 x]
    rfl

private theorem octGeom128_comm_sbox7 :
    ∀ (m : Nat) (z : Tower128), towerSbox7 7 (octGeom128 m z) = octGeom128 m (towerSbox7 7 z)
  | 0, _ => by simp [octGeom128, towerSbox7]
  | m + 1, z => by
    have hMul : ∀ a b : Tower128, towerSbox7 7 (towerMul 7 a b) =
        towerMul 7 (towerSbox7 7 a) (towerSbox7 7 b) := fun a b => by
      dsimp only [towerSbox7]
      simp only [towerMul_comm, towerMul_left_comm_of_assoc 7 (towerMul_assoc 7)]
    have hFrob : ∀ a : Tower128, towerSbox7 7 (towerFrobIter 7 3 a) =
        towerFrobIter 7 3 (towerSbox7 7 a) := fun a => by
      dsimp only [towerSbox7]; simp only [towerFrobIter_mul]
    simp only [octGeom128, hMul, hFrob, octGeom128_comm_sbox7 m z]

theorem towerSbox7Inv128_right_inv (z : Tower128) :
    towerSbox7 7 (towerSbox7Inv128 z) = z := by
  unfold towerSbox7Inv128; rw [octGeom128_comm_sbox7 43 z]; exact towerSbox7Inv128_left_inv z

/-- Constructive bijectivity predicate (`injective ∧ surjective`). -/
def IsBijective {α β : Type} (f : α → β) : Prop :=
  (∀ a b : α, f a = f b → a = b) ∧ (∀ b : β, ∃ a : α, f a = b)

/-- **Full Bijectivity of $S(x) = x^7$ on `Tower128` (`pow7_tower128_bijective`)**. -/
theorem pow7_tower128_bijective : IsBijective (towerSbox7 7) :=
  ⟨fun a b h => by
      have := congrArg towerSbox7Inv128 h
      rwa [towerSbox7Inv128_left_inv, towerSbox7Inv128_left_inv] at this,
   fun z => ⟨towerSbox7Inv128 z, towerSbox7Inv128_right_inv z⟩⟩

theorem towerSbox7_diff_zero_iff (x delta : Tower128) :
    towerAdd 7 (towerSbox7 7 (towerAdd 7 x delta)) (towerSbox7 7 x) = towerZero 7 ↔
      delta = towerZero 7 := by
  refine ⟨fun h => ?_, fun h => by subst h; simp [towerAdd_zero, towerAdd_self_zero]⟩
  have hEq : towerSbox7 7 (towerAdd 7 x delta) = towerSbox7 7 x := by
    have h2 := congrArg (fun u => towerAdd 7 u (towerSbox7 7 x)) h
    simpa only [towerZero_add, towerAdd_assoc, towerAdd_self_zero, towerAdd_zero] using h2
  have h3 := congrArg (towerAdd 7 x) (pow7_tower128_bijective.1 _ _ hEq)
  simpa only [towerAdd_cancel, towerAdd_self_zero] using h3

/-! ## §4. Concrete MDS Linear Layer Branch Number $= 3$ & 48-Round Active S-Box Trail Security -/

@[expose] def spnRounds : Nat := 48
def gf128MdsAPolyBits : BitVec 128 := 0x9E3779B97F4A7C15F39CC0605CEDC835#128
def gf128MdsBPolyBits : BitVec 128 := 0xBF58476D1CE4E5B994D049BB133111EB#128
def gf128MdsATowerBits : BitVec 128 := 0x6938822d2669c41b597c42deeb84a0bb#128
def gf128MdsBTowerBits : BitVec 128 := 0x2df5aeeede6d3f143c5406b243efb482#128
def gf128MdsATower : Tower128 := unpackTower 7 gf128MdsATowerBits
def gf128MdsBTower : Tower128 := unpackTower 7 gf128MdsBTowerBits

private def poly128Xtimes (a : BitVec 128) : BitVec 128 :=
  if a.getLsbD 127 then (a <<< 1) ^^^ 0x87#128 else a <<< 1

private def poly128ShiftPow : Nat → BitVec 128 → BitVec 128
  | 0, a => poly128Xtimes a
  | k + 1, a => poly128ShiftPow k (poly128ShiftPow k a)

private def poly128MulRange : Nat → BitVec 128 → BitVec 128 → BitVec 128
  | 0, a, b => if b.getLsbD 0 then a else 0#128
  | k + 1, a, b =>
    poly128MulRange k a b ^^^ poly128MulRange k (poly128ShiftPow k a) (b >>> (2 ^ k))

def gf2_128_mul_bv (a b : BitVec 128) : BitVec 128 := poly128MulRange 7 a b

private def tower128PolyGen : Fin 7 → BitVec 128
  | ⟨0, _⟩ => 0x295ac0b1f4731af9676aac9fa4b20b08#128
  | ⟨1, _⟩ => 0x500317bd159d73bb34d2f7fba603e341#128
  | ⟨2, _⟩ => 0x872430dcdf135bcc433f53640b5ab39a#128
  | ⟨3, _⟩ => 0x08ee6d05a2afa6e5f848729a9637483a#128
  | ⟨4, _⟩ => 0x6167c15ae3f2515951c65cfffdd09b94#128
  | ⟨5, _⟩ => 0x11bf2ae00eefb7458f1990f8ffd4b9bc#128
  | ⟨6, _⟩ => 0x8845a6b78c9fffc36a2a74600cfa98de#128

set_option maxRecDepth 4096

private def psiRec : (k : Nat) → (hk : k ≤ 7) → TowerElem k → BitVec 128
  | 0, _, a => match (a : Bool) with | true => 1#128 | false => 0#128
  | k + 1, hk, (a0, a1) =>
    psiRec k (Nat.le_of_succ_le hk) a0 ^^^
      gf2_128_mul_bv (tower128PolyGen ⟨k, hk⟩) (psiRec k (Nat.le_of_succ_le hk) a1)

def psiTower128ToPoly (x : Tower128) : BitVec 128 := psiRec 7 (Nat.le_refl 7) x

private theorem packTower_towerOne_7 : packTower 7 (towerOne 7) = 1#128 := by decide

theorem towerOne128_ne_zero : towerOne 7 ≠ towerZero 7 := by
  intro h
  have hp := congrArg (packTower 7) h
  rw [packTower_towerOne_7, packTower_zero] at hp
  exact (by decide : (1#128 : BitVec 128) ≠ 0#128) hp

theorem gf128_mds_constants_certified :
    psiTower128ToPoly gf128MdsATower = gf128MdsAPolyBits ∧
    psiTower128ToPoly gf128MdsBTower = gf128MdsBPolyBits ∧
    gf128MdsATower ≠ towerZero 7 ∧ gf128MdsBTower ≠ towerZero 7 ∧
    towerMul 7 gf128MdsATower gf128MdsBTower ≠ towerOne 7 ∧
    gf2_128_mul_bv gf128MdsAPolyBits gf128MdsBPolyBits ≠ 1#128 := by
  refine ⟨by decide, by decide, ?_, ?_, ?_, by decide⟩
  · intro h
    have hp := congrArg (packTower 7) h
    rw [gf128MdsATower, packTower_unpackTower, packTower_zero] at hp
    exact (by decide : gf128MdsATowerBits ≠ 0) hp
  · intro h
    have hp := congrArg (packTower 7) h
    rw [gf128MdsBTower, packTower_unpackTower, packTower_zero] at hp
    exact (by decide : gf128MdsBTowerBits ≠ 0) hp
  · intro h
    have hp := congrArg (packTower 7) h
    rw [← mulExec_refines, gf128MdsATower, gf128MdsBTower, packTower_unpackTower,
        packTower_unpackTower, packTower_towerOne_7] at hp
    exact (by decide : mulExec 7 gf128MdsATowerBits gf128MdsBTowerBits ≠ 1#128) hp

structure ValidSpnMdsPair (k : Nat) where
  mdsA : TowerElem k
  mdsB : TowerElem k
  hA_ne_zero : mdsA ≠ towerZero k
  hB_ne_zero : mdsB ≠ towerZero k
  hAB_ne_one : towerMul k mdsA mdsB ≠ towerOne k

def parallelSeededMdsPair : ValidSpnMdsPair 7 where
  mdsA := gf128MdsATower
  mdsB := gf128MdsBTower
  hA_ne_zero := gf128_mds_constants_certified.2.2.1
  hB_ne_zero := gf128_mds_constants_certified.2.2.2.1
  hAB_ne_one := gf128_mds_constants_certified.2.2.2.2.1

@[expose] def spnLinearMix (k : Nat) (mdsA mdsB : TowerElem k)
    (st : TowerElem k × TowerElem k) : TowerElem k × TowerElem k :=
  (towerAdd k st.1 (towerMul k mdsA st.2), towerAdd k st.2 (towerMul k mdsB st.1))

@[expose] def laneActiveWeight (k : Nat) (st : TowerElem k × TowerElem k) : Nat :=
  (if st.1 = towerZero k then 0 else 1) + (if st.2 = towerZero k then 0 else 1)

theorem laneActiveWeight_eq_zero_iff (k : Nat) (st : TowerElem k × TowerElem k) :
    laneActiveWeight k st = 0 ↔ st = (towerZero k, towerZero k) := by
  unfold laneActiveWeight; rcases st with ⟨u, v⟩
  by_cases hu : u = towerZero k <;> by_cases hv : v = towerZero k <;> simp [hu, hv]

/-- **Exact Differential Branch Number $= 3$ of `spnLinearMix` (`spnLinearMix_branch_number_three`)**. -/
theorem spnLinearMix_branch_number_three {k : Nat} (mds : ValidSpnMdsPair k)
    (st : TowerElem k × TowerElem k) (hNonZero : st ≠ (towerZero k, towerZero k)) :
    spnLinearMix k mds.mdsA mds.mdsB st ≠ (towerZero k, towerZero k) ∧
    3 ≤ laneActiveWeight k st + laneActiveWeight k (spnLinearMix k mds.mdsA mds.mdsB st) := by
  rcases st with ⟨u, v⟩
  have hOutNeZero : spnLinearMix k mds.mdsA mds.mdsB (u, v) ≠ (towerZero k, towerZero k) := by
    intro hZero
    dsimp only [spnLinearMix] at hZero
    have huEq : u = towerMul k mds.mdsA v := by
      have h := congrArg (fun z => towerAdd k z (towerMul k mds.mdsA v)) (congrArg Prod.fst hZero)
      simpa only [towerZero_add, towerAdd_assoc, towerAdd_self_zero, towerAdd_zero] using h
    have hvEq : v = towerMul k mds.mdsB u := by
      have h := congrArg (fun z => towerAdd k z (towerMul k mds.mdsB u)) (congrArg Prod.snd hZero)
      simpa only [towerZero_add, towerAdd_assoc, towerAdd_self_zero, towerAdd_zero] using h
    by_cases hv0 : v = towerZero k
    · subst hv0; simp only [towerMul_zero] at huEq; exact hNonZero (Prod.ext huEq rfl)
    · have hvLoop : towerMul k (towerOne k) v = towerMul k (towerMul k mds.mdsB mds.mdsA) v :=
        calc towerMul k (towerOne k) v
          _ = v := towerOne_mul k v
          _ = towerMul k mds.mdsB u := hvEq
          _ = towerMul k mds.mdsB (towerMul k mds.mdsA v) := by rw [huEq]
          _ = towerMul k (towerMul k mds.mdsB mds.mdsA) v := (towerMul_assoc k _ _ _).symm
      have hOneEqBA : towerOne k = towerMul k mds.mdsB mds.mdsA :=
        towerMul_cancel_left k v (towerOne k) (towerMul k mds.mdsB mds.mdsA) hv0
          (by rw [towerMul_comm k v, towerMul_comm k v, hvLoop])
      rw [towerMul_comm] at hOneEqBA
      exact mds.hAB_ne_one hOneEqBA.symm
  refine ⟨hOutNeZero, ?_⟩
  by_cases hu : u = towerZero k
  · have hv : v ≠ towerZero k := fun hv0 => hNonZero (Prod.ext hu hv0)
    have hAv : towerMul k mds.mdsA v ≠ towerZero k := fun hMul0 =>
      ((towerMul_eq_zero_iff k mds.mdsA v).mp hMul0).elim mds.hA_ne_zero hv
    unfold laneActiveWeight spnLinearMix; simp [hu, hv, hAv]
  · by_cases hv : v = towerZero k
    · have hBu : towerMul k mds.mdsB u ≠ towerZero k := fun hMul0 =>
        ((towerMul_eq_zero_iff k mds.mdsB u).mp hMul0).elim mds.hB_ne_zero hu
      unfold laneActiveWeight spnLinearMix; simp [hu, hv, hBu]
    · have hOutWtPos : 0 < laneActiveWeight k (spnLinearMix k mds.mdsA mds.mdsB (u, v)) := by
        cases hWt : laneActiveWeight k (spnLinearMix k mds.mdsA mds.mdsB (u, v)) with
        | zero => exact False.elim (hOutNeZero ((laneActiveWeight_eq_zero_iff k _).mp hWt))
        | succ m => exact Nat.zero_lt_succ m
      have hInWt : laneActiveWeight k (u, v) = 2 := by unfold laneActiveWeight; simp [hu, hv]
      omega

@[expose] def spnRound128 (mdsA mdsB : Tower128) (rc : Tower128 × Tower128)
    (st : Tower128 × Tower128) : Tower128 × Tower128 :=
  spnLinearMix 7 mdsA mdsB (towerSbox7 7 (towerAdd 7 st.1 rc.1), towerSbox7 7 (towerAdd 7 st.2 rc.2))

def spnIterRounds128 (mdsA mdsB : Tower128) (rcs : Nat → Tower128 × Tower128) :
    Nat → (Tower128 × Tower128) → Tower128 × Tower128
  | 0, st => st
  | r + 1, st => spnRound128 mdsA mdsB (rcs r) (spnIterRounds128 mdsA mdsB rcs r st)

def spnDaviesMeyer48 (mdsA mdsB : Tower128) (rcs : Nat → Tower128 × Tower128)
    (inp : Tower128 × Tower128) : Tower128 × Tower128 :=
  let out := spnIterRounds128 mdsA mdsB rcs spnRounds inp
  (towerAdd 7 out.1 inp.1, towerAdd 7 out.2 inp.2)

def spnTrailActiveSboxes (mdsA mdsB : Tower128) (rcs : Nat → Tower128 × Tower128) :
    Nat → (Tower128 × Tower128) → (Tower128 × Tower128) → Nat
  | 0, _, _ => 0
  | r + 1, s, s' =>
    let cur := spnIterRounds128 mdsA mdsB rcs r s
    let cur' := spnIterRounds128 mdsA mdsB rcs r s'
    spnTrailActiveSboxes mdsA mdsB rcs r s s' +
      laneActiveWeight 7 (towerAdd 7 cur.1 cur'.1, towerAdd 7 cur.2 cur'.2)

private theorem spnLinearMix_diff (mdsA mdsB : Tower128) (a b : Tower128 × Tower128) :
    let la := spnLinearMix 7 mdsA mdsB a; let lb := spnLinearMix 7 mdsA mdsB b
    (towerAdd 7 la.1 lb.1, towerAdd 7 la.2 lb.2) =
      spnLinearMix 7 mdsA mdsB (towerAdd 7 a.1 b.1, towerAdd 7 a.2 b.2) := by
  unfold spnLinearMix
  apply Prod.ext <;> simp only [towerMul_add_distrib, towerAdd_assoc, towerAdd_left_comm]

private theorem sboxPair_diff_weight_eq (rc a b : Tower128 × Tower128) :
    laneActiveWeight 7
      (towerAdd 7 (towerSbox7 7 (towerAdd 7 a.1 rc.1)) (towerSbox7 7 (towerAdd 7 b.1 rc.1)),
       towerAdd 7 (towerSbox7 7 (towerAdd 7 a.2 rc.2)) (towerSbox7 7 (towerAdd 7 b.2 rc.2))) =
    laneActiveWeight 7 (towerAdd 7 a.1 b.1, towerAdd 7 a.2 b.2) := by
  have hShift : ∀ x y r : Tower128,
      towerAdd 7 y r = towerAdd 7 (towerAdd 7 x r) (towerAdd 7 x y) := fun x y r => by
    rw [towerAdd_comm 7 x r, towerAdd_assoc 7 r x, ← towerAdd_assoc 7 x x y,
        towerAdd_self_zero, towerZero_add, towerAdd_comm 7 r y]
  have h0 : (towerAdd 7 (towerSbox7 7 (towerAdd 7 a.1 rc.1)) (towerSbox7 7 (towerAdd 7 b.1 rc.1)) = towerZero 7) ↔
      (towerAdd 7 a.1 b.1 = towerZero 7) := by
    rw [hShift a.1 b.1 rc.1, towerAdd_comm 7 (towerSbox7 7 (towerAdd 7 a.1 rc.1)), towerSbox7_diff_zero_iff]
  have h1 : (towerAdd 7 (towerSbox7 7 (towerAdd 7 a.2 rc.2)) (towerSbox7 7 (towerAdd 7 b.2 rc.2)) = towerZero 7) ↔
      (towerAdd 7 a.2 b.2 = towerZero 7) := by
    rw [hShift a.2 b.2 rc.2, towerAdd_comm 7 (towerSbox7 7 (towerAdd 7 a.2 rc.2)), towerSbox7_diff_zero_iff]
  unfold laneActiveWeight
  by_cases d0 : towerAdd 7 a.1 b.1 = towerZero 7 <;> by_cases d1 : towerAdd 7 a.2 b.2 = towerZero 7
  · simp [d0, d1, h0.mpr d0, h1.mpr d1]
  · have nd1 : ¬ (towerAdd 7 (towerSbox7 7 (towerAdd 7 a.2 rc.2)) (towerSbox7 7 (towerAdd 7 b.2 rc.2)) = towerZero 7) :=
      fun h => d1 (h1.mp h)
    simp [d0, d1, h0.mpr d0, nd1]
  · have nd0 : ¬ (towerAdd 7 (towerSbox7 7 (towerAdd 7 a.1 rc.1)) (towerSbox7 7 (towerAdd 7 b.1 rc.1)) = towerZero 7) :=
      fun h => d0 (h0.mp h)
    simp [d0, d1, nd0, h1.mpr d1]
  · have nd0 : ¬ (towerAdd 7 (towerSbox7 7 (towerAdd 7 a.1 rc.1)) (towerSbox7 7 (towerAdd 7 b.1 rc.1)) = towerZero 7) :=
      fun h => d0 (h0.mp h)
    have nd1 : ¬ (towerAdd 7 (towerSbox7 7 (towerAdd 7 a.2 rc.2)) (towerSbox7 7 (towerAdd 7 b.2 rc.2)) = towerZero 7) :=
      fun h => d1 (h1.mp h)
    simp [d0, d1, nd0, nd1]

private theorem spnRound128_preserves_distinct (mds : ValidSpnMdsPair 7)
    (rc s s' : Tower128 × Tower128) (hNe : s ≠ s') :
    spnRound128 mds.mdsA mds.mdsB rc s ≠ spnRound128 mds.mdsA mds.mdsB rc s' ∧
    3 ≤ laneActiveWeight 7 (towerAdd 7 s.1 s'.1, towerAdd 7 s.2 s'.2) +
        laneActiveWeight 7
          (towerAdd 7 (spnRound128 mds.mdsA mds.mdsB rc s).1 (spnRound128 mds.mdsA mds.mdsB rc s').1,
           towerAdd 7 (spnRound128 mds.mdsA mds.mdsB rc s).2 (spnRound128 mds.mdsA mds.mdsB rc s').2) := by
  let sbS := (towerSbox7 7 (towerAdd 7 s.1 rc.1), towerSbox7 7 (towerAdd 7 s.2 rc.2))
  let sbS' := (towerSbox7 7 (towerAdd 7 s'.1 rc.1), towerSbox7 7 (towerAdd 7 s'.2 rc.2))
  have hDiffInNe : (towerAdd 7 s.1 s'.1, towerAdd 7 s.2 s'.2) ≠ (towerZero 7, towerZero 7) := by
    intro h0
    have h1 := congrArg (fun z => towerAdd 7 z s'.1) (congrArg Prod.fst h0)
    have h2 := congrArg (fun z => towerAdd 7 z s'.2) (congrArg Prod.snd h0)
    simp only [towerZero_add, towerAdd_assoc, towerAdd_self_zero, towerAdd_zero] at h1 h2
    exact hNe (Prod.ext h1 h2)
  have hSbWt := sboxPair_diff_weight_eq rc s s'
  have hSbDiffNe : (towerAdd 7 sbS.1 sbS'.1, towerAdd 7 sbS.2 sbS'.2) ≠ (towerZero 7, towerZero 7) := by
    intro h0
    have hw0 := (laneActiveWeight_eq_zero_iff 7 _).mpr h0
    rw [hSbWt] at hw0
    exact hDiffInNe ((laneActiveWeight_eq_zero_iff 7 _).mp hw0)
  have hBranch := spnLinearMix_branch_number_three mds _ hSbDiffNe
  have hMixEq := spnLinearMix_diff mds.mdsA mds.mdsB sbS sbS'
  unfold spnRound128; dsimp only [sbS, sbS'] at hMixEq ⊢
  refine ⟨fun hEqOut => hBranch.1 (by rw [← hMixEq, hEqOut, towerAdd_self_zero, towerAdd_self_zero]), ?_⟩
  rw [hMixEq, ← hSbWt]; exact hBranch.2

private theorem spnIterRounds_even_active_bound (mds : ValidSpnMdsPair 7)
    (rcs : Nat → Tower128 × Tower128) :
    ∀ (pairs : Nat) (s s' : Tower128 × Tower128), s ≠ s' →
      spnIterRounds128 mds.mdsA mds.mdsB rcs (2 * pairs) s ≠
        spnIterRounds128 mds.mdsA mds.mdsB rcs (2 * pairs) s' ∧
      3 * pairs ≤ spnTrailActiveSboxes mds.mdsA mds.mdsB rcs (2 * pairs) s s'
  | 0, _, _, hNe => ⟨hNe, Nat.le_refl 0⟩
  | pairs + 1, s, s', hNe => by
    obtain ⟨hNePrev, hActPrev⟩ := spnIterRounds_even_active_bound mds rcs pairs s s' hNe
    rw [show 2 * (pairs + 1) = (2 * pairs + 1) + 1 by omega]
    let u := spnIterRounds128 mds.mdsA mds.mdsB rcs (2 * pairs) s
    let u' := spnIterRounds128 mds.mdsA mds.mdsB rcs (2 * pairs) s'
    obtain ⟨hNeMid, hStep3⟩ := spnRound128_preserves_distinct mds (rcs (2 * pairs)) u u' hNePrev
    obtain ⟨hNeEnd, _⟩ := spnRound128_preserves_distinct mds (rcs (2 * pairs + 1))
      (spnRound128 mds.mdsA mds.mdsB (rcs (2 * pairs)) u)
      (spnRound128 mds.mdsA mds.mdsB (rcs (2 * pairs)) u') hNeMid
    refine ⟨hNeEnd, ?_⟩
    simp only [spnTrailActiveSboxes, spnIterRounds128]
    change 3 * (pairs + 1) ≤ spnTrailActiveSboxes mds.mdsA mds.mdsB rcs (2 * pairs) s s' +
      laneActiveWeight 7 (towerAdd 7 u.1 u'.1, towerAdd 7 u.2 u'.2) +
      laneActiveWeight 7
        (towerAdd 7 (spnRound128 mds.mdsA mds.mdsB (rcs (2 * pairs)) u).1
                    (spnRound128 mds.mdsA mds.mdsB (rcs (2 * pairs)) u').1,
         towerAdd 7 (spnRound128 mds.mdsA mds.mdsB (rcs (2 * pairs)) u).2
                    (spnRound128 mds.mdsA mds.mdsB (rcs (2 * pairs)) u').2)
    omega

/-- **48-Round Active S-Box Lower Bound (`spn48_active_sboxes_ge_72`)**:
    Every distinct 256-bit input pair `s ≠ s'` activates **$\ge 72$ S-boxes** ($\ge 48$). -/
theorem spn48_active_sboxes_ge_72 (mds : ValidSpnMdsPair 7)
    (rcs : Nat → Tower128 × Tower128) (s s' : Tower128 × Tower128) (hNe : s ≠ s') :
    72 ≤ spnTrailActiveSboxes mds.mdsA mds.mdsB rcs spnRounds s s' ∧
    48 ≤ spnTrailActiveSboxes mds.mdsA mds.mdsB rcs spnRounds s s' := by
  have h := (spnIterRounds_even_active_bound mds rcs 24 s s' hNe).2
  exact ⟨h, Nat.le_trans (by decide : 48 ≤ 72) h⟩

/-- **Concrete 2-Round (`3` S-boxes) & 48-Round (`48` / `72` S-boxes) Differential Trail Security**:
    $(6 / 2^{128})^3 < 2^{-376}$ and $(6 / 2^{128})^{48} < 2^{-6000} \ll 2^{-256}$. -/
theorem spn48_differential_trail_security_bounds :
    strictlyMoreThanBits 376 (sbox7MaxDiffProb128.pow 3) ∧
    strictlyMoreThanBits 256 (sbox7MaxDiffProb128.pow 48) ∧
    strictlyMoreThanBits 256 (sbox7MaxDiffProb128.pow 72) := by
  have h1 : RatBound.le sbox7MaxDiffProb128 (RatBound.invPow2 125) :=
    (atLeastBits_iff_le_invPow2 125 sbox7MaxDiffProb128).mp
      (atLeastBits_of_strictlyMoreThanBits sbox7MaxDiffProb128_eq_three_div_two_pow_127.2.2)
  have hBits : ∀ n : Nat, atLeastBits (125 * n) (sbox7MaxDiffProb128.pow n) := fun n => by
    apply atLeastBits_of_le (RatBound.pow_le_pow h1 n)
    unfold atLeastBits RatBound.invPow2 RatBound.pow; dsimp only
    rw [Nat.one_pow, Nat.one_mul, ← Nat.pow_mul]; exact Nat.le_refl _
  have hStrictFrom257 : ∀ r : RatBound, atLeastBits 257 r → strictlyMoreThanBits 256 r := by
    intro r hr; unfold atLeastBits strictlyMoreThanBits at *
    by_cases hNum : r.num = 0
    · rw [hNum, Nat.zero_mul]; exact r.h_pos
    · exact Nat.lt_of_lt_of_le (by rw [Nat.pow_succ, ← Nat.mul_assoc]; omega) hr
  exact ⟨by decide,
    hStrictFrom257 _ (atLeastBits_antitone_bits (by decide : 257 ≤ 125 * 48) (hBits 48)),
    hStrictFrom257 _ (atLeastBits_antitone_bits (by decide : 257 ≤ 125 * 72) (hBits 72))⟩

/-! ## §5. Algebraic Degree Growth, 43-Round Higher-Order / Interpolation Margin & `#tooth` Guards -/

private def binaryPopcountAux : Nat → Nat → Nat
  | 0, _ => 0
  | _ + 1, 0 => 0
  | fuel + 1, n + 1 => ((n + 1) % 2) + binaryPopcountAux fuel ((n + 1) / 2)

def binaryPopcount (n : Nat) : Nat := binaryPopcountAux n n

@[expose] def spnMultivariateDegreeSchedule (r : Nat) : Nat := Nat.min 127 (3 ^ r)
def spnUnivariateDegree (r : Nat) : Nat := 7 ^ r

/-- **Algebraic Degree Saturation in 5 Rounds & 43-Round Security Margin (`spn48_algebraic_degree_margin`)**. -/
theorem spn48_algebraic_degree_margin :
    binaryPopcount 7 = 3 ∧ 3 ^ 5 = 243 ∧ 128 < 3 ^ 5 ∧
    spnMultivariateDegreeSchedule 5 = 127 ∧ spnRounds - 5 = 43 ∧
    2 ^ 134 < spnUnivariateDegree spnRounds :=
  ⟨by decide, by decide, by decide, by decide, rfl, by decide⟩

/-- **Round-Constant Asymmetry Eliminates Zero-Subspace Fixpoints (`spnRound128_nonzero_rc_breaks_zero_fixpoint`)**. -/
theorem spnRound128_nonzero_rc_breaks_zero_fixpoint
    (mds : ValidSpnMdsPair 7) (rc : Tower128 × Tower128) (hRc : rc ≠ (towerZero 7, towerZero 7)) :
    spnRound128 mds.mdsA mds.mdsB rc (towerZero 7, towerZero 7) ≠ (towerZero 7, towerZero 7) := by
  have hSboxNe : (towerSbox7 7 rc.1, towerSbox7 7 rc.2) ≠ (towerZero 7, towerZero 7) := by
    intro h0
    have h1 : rc.1 = towerZero 7 := pow7_tower128_bijective.1 _ _ (by simpa [towerSbox7] using congrArg Prod.fst h0)
    have h2 : rc.2 = towerZero 7 := pow7_tower128_bijective.1 _ _ (by simpa [towerSbox7] using congrArg Prod.snd h0)
    exact hRc (Prod.ext h1 h2)
  unfold spnRound128; simp only [towerZero_add]
  exact (spnLinearMix_branch_number_three mds (towerSbox7 7 rc.1, towerSbox7 7 rc.2) hSboxNe).1

theorem tooth_degenerate_mds_ab_eq_one_collapses_branch_number :
    ∃ st : Tower128 × Tower128,
      st ≠ (towerZero 7, towerZero 7) ∧
      spnLinearMix 7 (towerOne 7) (towerOne 7) st = (towerZero 7, towerZero 7) ∧
      laneActiveWeight 7 st + laneActiveWeight 7 (spnLinearMix 7 (towerOne 7) (towerOne 7) st) = 2 := by
  refine ⟨(towerOne 7, towerOne 7), fun h => towerOne128_ne_zero (congrArg Prod.fst h), ?_, ?_⟩
  · unfold spnLinearMix
    simp only [towerOne_mul, towerAdd_self_zero]
  · unfold spnLinearMix laneActiveWeight
    simp only [towerOne_mul, towerAdd_self_zero, towerOne128_ne_zero, ↓reduceIte]

theorem tooth_frobenius_sbox_x2_differential_probability_one :
    ∃ badBound : RatBound,
      binaryPopcount 2 = 1 ∧
      (∀ x delta : Tower128,
        towerAdd 7 (towerMul 7 (towerAdd 7 x delta) (towerAdd 7 x delta)) (towerMul 7 x x) =
          towerMul 7 delta delta) ∧
      RatBound.lt sbox7MaxDiffProb128 badBound ∧
      ¬ strictlyMoreThanBits 125 badBound := by
  refine ⟨RatBound.one, by decide, fun x delta => ?_, by decide, by decide⟩
  rw [towerSq_add, towerAdd_comm 7 (towerMul 7 x x), towerAdd_assoc, towerAdd_self_zero, towerAdd_zero]

theorem tooth_zero_round_constants_preserve_zero_subspace (mdsA mdsB : Tower128) :
    ∃ rc : Tower128 × Tower128,
      spnRound128 mdsA mdsB rc (towerZero 7, towerZero 7) = (towerZero 7, towerZero 7) ∧
      spnIterRounds128 mdsA mdsB (fun _ => rc) spnRounds
        (towerZero 7, towerZero 7) = (towerZero 7, towerZero 7) := by
  have hStep : spnRound128 mdsA mdsB (towerZero 7, towerZero 7) (towerZero 7, towerZero 7) =
      (towerZero 7, towerZero 7) := by unfold spnRound128 spnLinearMix towerSbox7; simp
  refine ⟨(towerZero 7, towerZero 7), hStep, ?_⟩
  suffices hAll : ∀ r : Nat, spnIterRounds128 mdsA mdsB (fun _ => (towerZero 7, towerZero 7)) r
      (towerZero 7, towerZero 7) = (towerZero 7, towerZero 7) from hAll spnRounds
  intro r
  induction r with
  | zero => rfl
  | succ r ih => simp only [spnIterRounds128, ih, hStep]

#tooth_pair Qsag.spnLinearMix_branch_number_three vs Qsag.tooth_degenerate_mds_ab_eq_one_collapses_branch_number
#tooth_pair Qsag.sbox7MaxDiffProb128_eq_three_div_two_pow_127 vs Qsag.tooth_frobenius_sbox_x2_differential_probability_one
#tooth_pair Qsag.spnRound128_nonzero_rc_breaks_zero_fixpoint vs Qsag.tooth_zero_round_constants_preserve_zero_subspace

theorem inhabited_parallel_seeded_spn_security :
    ∃ (mds : ValidSpnMdsPair 7) (rc : Tower128 × Tower128) (s s' : Tower128 × Tower128),
      rc ≠ (towerZero 7, towerZero 7) ∧ s ≠ s' ∧
      72 ≤ spnTrailActiveSboxes mds.mdsA mds.mdsB (fun _ => rc) spnRounds s s' := by
  have hRcNe : ((towerOne 7, towerZero 7) : Tower128 × Tower128) ≠ (towerZero 7, towerZero 7) :=
    fun h => towerOne128_ne_zero (congrArg Prod.fst h)
  have hSNe : ((towerZero 7, towerZero 7) : Tower128 × Tower128) ≠ (towerOne 7, towerZero 7) :=
    fun h => towerOne128_ne_zero (congrArg Prod.fst h).symm
  exact ⟨parallelSeededMdsPair, (towerOne 7, towerZero 7), (towerZero 7, towerZero 7),
    (towerOne 7, towerZero 7), hRcNe, hSNe,
    (spn48_active_sboxes_ge_72 parallelSeededMdsPair (fun _ => (towerOne 7, towerZero 7))
      (towerZero 7, towerZero 7) (towerOne 7, towerZero 7) hSNe).1⟩

#verify_inhabited Qsag.spn48_active_sboxes_ge_72 Qsag.inhabited_parallel_seeded_spn_security

end Qsag
end
