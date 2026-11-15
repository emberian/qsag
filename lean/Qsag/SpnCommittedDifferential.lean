module
/-
# Qsag.SpnCommittedDifferential — differentials and Davies–Meyer in the committed experiment

Continues `Qsag.SpnRoundConstantExperiment` (same roles: the pair `s ≠ s'` is committed, then
the round-constant pairs are drawn uniformly and independently from `keys`).

* `spn_two_round_differential_count_le`, `spn_differential_count_le`: a committed differential,
  with every trail leading to the target difference counted, has probability at most `(6/N)^2`
  over any number `≥ 2` of rounds. The 72-box trail product does not bound this event.
* `spn48_davies_meyer_committed_pair_collision_count_le`: a committed pair collides under the
  actual `spnDaviesMeyer48` with probability at most `36/N^2`.
* `tooth_xor_constant_permutation_davies_meyer_collapses`: a bijection whose Davies–Meyer
  feed-forward is constant; invertibility alone gives no collision or preimage resistance.

Not proved: any statement for inputs chosen after the public constants are known.
-/
public import Qsag.SpnRoundConstantExperiment
import all Qsag.SpnRoundConstantExperiment
import all Qsag.HashTrailSampling
import all Qsag.ParallelSeededSpnSecurity

public section
namespace Qsag
set_option autoImplicit false

/-! ## §1. Committed differentials: all trails summed -/

/-- Explicit inverse of the mixing layer `(u, v) ↦ (u + A v, v + B u)`. -/
def spnMixInv (mdsA mdsB : Tower128) (β : Tower128 × Tower128) : Tower128 × Tower128 :=
  let c := towerInv 7 (towerAdd 7 (towerOne 7) (towerMul 7 mdsA mdsB))
  (towerMul 7 c (towerAdd 7 β.1 (towerMul 7 mdsA β.2)),
   towerMul 7 c (towerAdd 7 β.2 (towerMul 7 mdsB β.1)))

private theorem mix_alg1 (A B x y : Tower128) :
    towerAdd 7 (towerAdd 7 x (towerMul 7 A y)) (towerMul 7 A (towerAdd 7 y (towerMul 7 B x))) =
      towerMul 7 (towerAdd 7 (towerOne 7) (towerMul 7 A B)) x := by
  rw [towerMul_add_distrib, ← towerMul_assoc, towerAdd_assoc,
    ← towerAdd_assoc 7 (towerMul 7 A y) (towerMul 7 A y), towerAdd_self_zero, towerZero_add,
    towerAdd_mul_distrib, towerOne_mul]

private theorem mix_alg2 (A B x y : Tower128) :
    towerAdd 7 (towerAdd 7 y (towerMul 7 B x)) (towerMul 7 B (towerAdd 7 x (towerMul 7 A y))) =
      towerMul 7 (towerAdd 7 (towerOne 7) (towerMul 7 A B)) y := by
  rw [towerMul_add_distrib, ← towerMul_assoc, towerAdd_assoc,
    ← towerAdd_assoc 7 (towerMul 7 B x) (towerMul 7 B x), towerAdd_self_zero, towerZero_add,
    towerAdd_mul_distrib, towerOne_mul, towerMul_comm 7 B A]

private theorem mix_det_inv (mds : ValidSpnMdsPair 7) (x : Tower128) :
    towerMul 7 (towerInv 7 (towerAdd 7 (towerOne 7) (towerMul 7 mds.mdsA mds.mdsB)))
      (towerMul 7 (towerAdd 7 (towerOne 7) (towerMul 7 mds.mdsA mds.mdsB)) x) = x := by
  have hD : towerAdd 7 (towerOne 7) (towerMul 7 mds.mdsA mds.mdsB) ≠ towerZero 7 := fun h =>
    mds.hAB_ne_one ((tadd_eq_zero_iff _ _).mp h).symm
  rw [← towerMul_assoc, towerMul_comm 7 (towerInv 7 _), towerMul_inv 7 _ hD, towerOne_mul]

/-- The mixing layer hits `β` exactly at `spnMixInv β`. -/
theorem spnLinearMix_eq_iff (mds : ValidSpnMdsPair 7) (σ β : Tower128 × Tower128) :
    spnLinearMix 7 mds.mdsA mds.mdsB σ = β ↔ σ = spnMixInv mds.mdsA mds.mdsB β := by
  constructor
  · intro h
    rcases σ with ⟨u, v⟩
    subst h
    apply Prod.ext
    · show u = towerMul 7 (towerInv 7 (towerAdd 7 (towerOne 7) (towerMul 7 mds.mdsA mds.mdsB)))
        (towerAdd 7 (towerAdd 7 u (towerMul 7 mds.mdsA v))
          (towerMul 7 mds.mdsA (towerAdd 7 v (towerMul 7 mds.mdsB u))))
      rw [mix_alg1, mix_det_inv]
    · show v = towerMul 7 (towerInv 7 (towerAdd 7 (towerOne 7) (towerMul 7 mds.mdsA mds.mdsB)))
        (towerAdd 7 (towerAdd 7 v (towerMul 7 mds.mdsB u))
          (towerMul 7 mds.mdsB (towerAdd 7 u (towerMul 7 mds.mdsA v))))
      rw [mix_alg2, mix_det_inv]
  · intro h
    rcases β with ⟨p, q⟩
    subst h
    apply Prod.ext
    · show towerAdd 7
          (towerMul 7 (towerInv 7 (towerAdd 7 (towerOne 7) (towerMul 7 mds.mdsA mds.mdsB)))
            (towerAdd 7 p (towerMul 7 mds.mdsA q)))
          (towerMul 7 mds.mdsA
            (towerMul 7 (towerInv 7 (towerAdd 7 (towerOne 7) (towerMul 7 mds.mdsA mds.mdsB)))
              (towerAdd 7 q (towerMul 7 mds.mdsB p)))) = p
      rw [towerMul_left_comm_of_assoc 7 (towerMul_assoc 7) mds.mdsA, ← towerMul_add_distrib,
        mix_alg1, mix_det_inv]
    · show towerAdd 7
          (towerMul 7 (towerInv 7 (towerAdd 7 (towerOne 7) (towerMul 7 mds.mdsA mds.mdsB)))
            (towerAdd 7 q (towerMul 7 mds.mdsB p)))
          (towerMul 7 mds.mdsB
            (towerMul 7 (towerInv 7 (towerAdd 7 (towerOne 7) (towerMul 7 mds.mdsA mds.mdsB)))
              (towerAdd 7 p (towerMul 7 mds.mdsA q)))) = q
      rw [towerMul_left_comm_of_assoc 7 (towerMul_assoc 7) mds.mdsB, ← towerMul_add_distrib,
        mix_alg2, mix_det_inv]

/-- Number of constant lists of length `n` under which the committed pair ends with state
    difference `β`. Every trail leading to `β` is counted: this is the differential. -/
def spnFinalDiffCount (keys : List Tower128) (mdsA mdsB : Tower128) (n : Nat)
    (s s' β : Tower128 × Tower128) : Nat :=
  ((freshInputAssignments (rcPairs keys) n).filter fun ks =>
    decide (pairXor (spnRunList mdsA mdsB ks s) (spnRunList mdsA mdsB ks s') = β)).length

theorem spnFinalDiffCount_succ (keys : List Tower128) (mdsA mdsB : Tower128) (n : Nat)
    (s s' β : Tower128 × Tower128) :
    spnFinalDiffCount keys mdsA mdsB (n + 1) s s' β =
      rcSum (fun rc => spnFinalDiffCount keys mdsA mdsB n
        (spnRound128 mdsA mdsB rc s) (spnRound128 mdsA mdsB rc s') β) (rcPairs keys) := by
  unfold spnFinalDiffCount
  rw [freshInputAssignments, filter_prefixAssignments_length]
  rfl

/-- One round, exact: the differential count is a product of two lane counts at the unique
    S-box output difference that the mixing layer sends to `β`. -/
theorem spnFinalDiffCount_one (mds : ValidSpnMdsPair 7) (keys : List Tower128)
    (t t' β : Tower128 × Tower128) :
    spnFinalDiffCount keys mds.mdsA mds.mdsB 1 t t' β =
      laneCount keys t.1 t'.1 (spnMixInv mds.mdsA mds.mdsB β).1 *
        laneCount keys t.2 t'.2 (spnMixInv mds.mdsA mds.mdsB β).2 := by
  rw [spnFinalDiffCount_succ, ← sboxPairDiff_count]
  have hTerm : (fun rc => spnFinalDiffCount keys mds.mdsA mds.mdsB 0
      (spnRound128 mds.mdsA mds.mdsB rc t) (spnRound128 mds.mdsA mds.mdsB rc t') β) =
      fun rc => if decide (sboxPairDiff rc t t' = spnMixInv mds.mdsA mds.mdsB β) then 1 else 0 := by
    funext rc
    unfold spnFinalDiffCount
    refine (filter_singleton_length _ []).trans ?_
    show (if decide (pairXor (spnRound128 mds.mdsA mds.mdsB rc t)
        (spnRound128 mds.mdsA mds.mdsB rc t') = β) = true then 1 else 0) = _
    by_cases h : sboxPairDiff rc t t' = spnMixInv mds.mdsA mds.mdsB β
    · have hβ : pairXor (spnRound128 mds.mdsA mds.mdsB rc t)
          (spnRound128 mds.mdsA mds.mdsB rc t') = β := by
        rw [spnRound128_diff]; exact (spnLinearMix_eq_iff mds _ _).mpr h
      rw [ite_eq_left (decide_eq_true h), ite_eq_left (decide_eq_true hβ)]
    · have hβ : ¬ pairXor (spnRound128 mds.mdsA mds.mdsB rc t)
          (spnRound128 mds.mdsA mds.mdsB rc t') = β := fun hb =>
        h ((spnLinearMix_eq_iff mds _ _).mp (by rw [← spnRound128_diff]; exact hb))
      rw [ite_eq_right (fun hd => h (of_decide_eq_true hd)),
        ite_eq_right (fun hd => hβ (of_decide_eq_true hd))]
  rw [hTerm, rcSum_ite, Nat.mul_one]

/-- For a committed pair `s ≠ s'` and a nonzero multiplier `c`, at most `6·N` first-round
    constants make the second lane's S-box difference equal `c` times the first lane's. These
    are the constants after which one lane of the next round is inactive. -/
theorem lane_collapse_count_le (keys : List Tower128) (hNd : keys.Nodup)
    (c : Tower128) (hc : c ≠ towerZero 7) (s s' : Tower128 × Tower128) (hNe : s ≠ s') :
    ((rcPairs keys).filter fun rc => decide
      (sboxLaneDiff rc.2 s.2 s'.2 = towerMul 7 c (sboxLaneDiff rc.1 s.1 s'.1))).length ≤
      keys.length * 6 := by
  rw [filter_rcPairs_length]
  apply rcSum_le_const
  intro a _
  show laneCount keys s.2 s'.2 (towerMul 7 c (sboxLaneDiff a s.1 s'.1)) ≤ 6
  apply laneCount_le_six keys hNd
  by_cases h2 : s.2 = s'.2
  · left
    intro hZero
    have h1 : s.1 = s'.1 := (sboxLaneDiff_eq_zero_iff a s.1 s'.1).mp
      (((towerMul_eq_zero_iff 7 _ _).mp hZero).resolve_left hc)
    exact hNe (Prod.ext h1 h2)
  · exact Or.inr h2

private theorem mix_snd_eq_iff (B x1 x2 y1 y2 : Tower128) :
    towerAdd 7 x2 (towerMul 7 B x1) = towerAdd 7 y2 (towerMul 7 B y1) ↔
      towerAdd 7 x2 y2 = towerMul 7 B (towerAdd 7 x1 y1) := by
  rw [tadd_cross_iff, towerMul_add_distrib]

/-- Second lanes agree after the round exactly on a `lane_collapse` event with `c = B`. -/
theorem spnRound128_snd_eq_count_le (mds : ValidSpnMdsPair 7) (keys : List Tower128)
    (hNd : keys.Nodup) (s s' : Tower128 × Tower128) (hNe : s ≠ s') :
    ((rcPairs keys).filter fun rc => decide
      ((spnRound128 mds.mdsA mds.mdsB rc s).2 = (spnRound128 mds.mdsA mds.mdsB rc s').2)).length ≤
      keys.length * 6 := by
  refine Nat.le_trans (Nat.le_of_eq ?_)
    (lane_collapse_count_le keys hNd mds.mdsB mds.hB_ne_zero s s' hNe)
  apply congrArg List.length
  apply List.filter_congr
  intro rc _
  exact decide_eq_decide.mpr (mix_snd_eq_iff mds.mdsB _ _ _ _)

/-- First lanes agree after the round exactly on a `lane_collapse` event with `c = A⁻¹`. -/
theorem spnRound128_fst_eq_count_le (mds : ValidSpnMdsPair 7) (keys : List Tower128)
    (hNd : keys.Nodup) (s s' : Tower128 × Tower128) (hNe : s ≠ s') :
    ((rcPairs keys).filter fun rc => decide
      ((spnRound128 mds.mdsA mds.mdsB rc s).1 = (spnRound128 mds.mdsA mds.mdsB rc s').1)).length ≤
      keys.length * 6 := by
  have hInv : towerMul 7 mds.mdsA (towerInv 7 mds.mdsA) = towerOne 7 :=
    towerMul_inv 7 _ mds.hA_ne_zero
  have hInvNe : towerInv 7 mds.mdsA ≠ towerZero 7 := fun h0 => by
    rw [h0, towerMul_zero] at hInv
    exact towerOne128_ne_zero hInv.symm
  refine Nat.le_trans (Nat.le_of_eq ?_)
    (lane_collapse_count_le keys hNd (towerInv 7 mds.mdsA) hInvNe s s' hNe)
  apply congrArg List.length
  apply List.filter_congr
  intro rc _
  apply decide_eq_decide.mpr
  show towerAdd 7 _ (towerMul 7 mds.mdsA _) = towerAdd 7 _ (towerMul 7 mds.mdsA _) ↔ _
  rw [tadd_cross_iff, ← towerMul_add_distrib]
  constructor
  · intro h
    show sboxLaneDiff rc.2 s.2 s'.2 = _
    have h2 := congrArg (towerMul 7 (towerInv 7 mds.mdsA)) h
    rw [← towerMul_assoc, towerMul_comm 7 (towerInv 7 mds.mdsA) mds.mdsA, hInv,
      towerOne_mul] at h2
    exact h2.symm
  · intro h
    have h2 : sboxLaneDiff rc.2 s.2 s'.2 =
        towerMul 7 (towerInv 7 mds.mdsA) (sboxLaneDiff rc.1 s.1 s'.1) := h
    show sboxLaneDiff rc.1 s.1 s'.1 = towerMul 7 mds.mdsA (sboxLaneDiff rc.2 s.2 s'.2)
    rw [h2, ← towerMul_assoc, hInv, towerOne_mul]

/-- **Two rounds, committed differential.** For a committed pair `s ≠ s'` and any target
    difference `β`, at most `36·N²` of the `N⁴` two-round constant lists produce `β`: the
    probability of a differential, with every trail counted, is at most `(6/N)²`. The four
    cases are the activity pattern of the last S-box layer's required output difference. -/
theorem spn_two_round_differential_count_le (mds : ValidSpnMdsPair 7) (keys : List Tower128)
    (hNd : keys.Nodup) (s s' : Tower128 × Tower128) (hNe : s ≠ s') (β : Tower128 × Tower128) :
    spnFinalDiffCount keys mds.mdsA mds.mdsB 2 s s' β ≤ 36 * (keys.length * keys.length) := by
  rw [spnFinalDiffCount_succ]
  simp only [spnFinalDiffCount_one]
  generalize spnMixInv mds.mdsA mds.mdsB β = ν
  have hU : ∀ rc, spnRound128 mds.mdsA mds.mdsB rc s ≠ spnRound128 mds.mdsA mds.mdsB rc s' :=
    fun rc => spnRound128_ne mds rc s s' hNe
  by_cases h1 : ν.1 = towerZero 7 <;> by_cases h2 : ν.2 = towerZero 7
  · refine Nat.le_trans (rcSum_le_const _ 0 _ fun rc _ => ?_) (by rw [Nat.mul_zero]; exact Nat.zero_le _)
    rw [h1, h2]
    by_cases hA : (spnRound128 mds.mdsA mds.mdsB rc s).1 = (spnRound128 mds.mdsA mds.mdsB rc s').1
    · have hB : (spnRound128 mds.mdsA mds.mdsB rc s).2 ≠ (spnRound128 mds.mdsA mds.mdsB rc s').2 :=
        fun hB => hU rc (Prod.ext hA hB)
      rw [laneCount_zero_target keys _ _ hB, Nat.mul_zero]; exact Nat.le_refl 0
    · rw [laneCount_zero_target keys _ _ hA, Nat.zero_mul]; exact Nat.le_refl 0
  · have hTerm : ∀ rc ∈ rcPairs keys,
        laneCount keys (spnRound128 mds.mdsA mds.mdsB rc s).1
            (spnRound128 mds.mdsA mds.mdsB rc s').1 ν.1 *
          laneCount keys (spnRound128 mds.mdsA mds.mdsB rc s).2
            (spnRound128 mds.mdsA mds.mdsB rc s').2 ν.2 ≤
        if decide ((spnRound128 mds.mdsA mds.mdsB rc s).1 =
            (spnRound128 mds.mdsA mds.mdsB rc s').1) then keys.length * 6 else 0 := by
      intro rc _
      by_cases hA : (spnRound128 mds.mdsA mds.mdsB rc s).1 = (spnRound128 mds.mdsA mds.mdsB rc s').1
      · rw [ite_eq_left (decide_eq_true hA)]
        exact Nat.mul_le_mul (laneCount_le_length keys _ _ _)
          (laneCount_le_six keys hNd _ _ _ (Or.inl h2))
      · rw [ite_eq_right (fun hd => hA (of_decide_eq_true hd)), h1,
          laneCount_zero_target keys _ _ hA, Nat.zero_mul]
        exact Nat.le_refl 0
    refine Nat.le_trans (rcSum_le_of_le _ _ _ hTerm) ?_
    rw [rcSum_ite]
    refine Nat.le_trans (Nat.mul_le_mul_right _ (spnRound128_fst_eq_count_le mds keys hNd s s' hNe)) ?_
    rw [Nat.mul_mul_mul_comm, Nat.mul_comm]
    exact Nat.le_refl _
  · have hTerm : ∀ rc ∈ rcPairs keys,
        laneCount keys (spnRound128 mds.mdsA mds.mdsB rc s).1
            (spnRound128 mds.mdsA mds.mdsB rc s').1 ν.1 *
          laneCount keys (spnRound128 mds.mdsA mds.mdsB rc s).2
            (spnRound128 mds.mdsA mds.mdsB rc s').2 ν.2 ≤
        if decide ((spnRound128 mds.mdsA mds.mdsB rc s).2 =
            (spnRound128 mds.mdsA mds.mdsB rc s').2) then keys.length * 6 else 0 := by
      intro rc _
      by_cases hB : (spnRound128 mds.mdsA mds.mdsB rc s).2 = (spnRound128 mds.mdsA mds.mdsB rc s').2
      · rw [ite_eq_left (decide_eq_true hB), Nat.mul_comm]
        exact Nat.mul_le_mul (laneCount_le_length keys _ _ _)
          (laneCount_le_six keys hNd _ _ _ (Or.inl h1))
      · rw [ite_eq_right (fun hd => hB (of_decide_eq_true hd)), h2,
          laneCount_zero_target keys _ _ hB, Nat.mul_zero]
        exact Nat.le_refl 0
    refine Nat.le_trans (rcSum_le_of_le _ _ _ hTerm) ?_
    rw [rcSum_ite]
    refine Nat.le_trans (Nat.mul_le_mul_right _ (spnRound128_snd_eq_count_le mds keys hNd s s' hNe)) ?_
    rw [Nat.mul_mul_mul_comm, Nat.mul_comm]
    exact Nat.le_refl _
  · refine Nat.le_trans (rcSum_le_const _ (6 * 6) _ fun rc _ =>
      Nat.mul_le_mul (laneCount_le_six keys hNd _ _ _ (Or.inl h1))
        (laneCount_le_six keys hNd _ _ _ (Or.inl h2))) ?_
    rw [rcPairs_length, Nat.mul_comm]
    exact Nat.le_refl _

/-- **Any number of rounds `≥ 2`, committed differential.** Earlier rounds only average the
    two-round bound over the states they reach, which stay distinct. -/
theorem spn_differential_count_le (mds : ValidSpnMdsPair 7) (keys : List Tower128)
    (hNd : keys.Nodup) (β : Tower128 × Tower128) :
    ∀ (n : Nat) (s s' : Tower128 × Tower128), s ≠ s' →
      spnFinalDiffCount keys mds.mdsA mds.mdsB (n + 2) s s' β ≤
        36 * (keys.length * keys.length) * (keys.length * keys.length) ^ n
  | 0, s, s', hNe => by
    rw [Nat.pow_zero, Nat.mul_one]
    exact spn_two_round_differential_count_le mds keys hNd s s' hNe β
  | n + 1, s, s', hNe => by
    rw [spnFinalDiffCount_succ]
    refine Nat.le_trans (rcSum_le_const _ _ _ fun rc _ =>
      spn_differential_count_le mds keys hNd β n _ _ (spnRound128_ne mds rc s s' hNe)) ?_
    rw [rcPairs_length, Nat.pow_succ, Nat.mul_left_comm, Nat.mul_comm (keys.length * keys.length),
      Nat.mul_assoc]
    exact Nat.le_refl _

/-! ## §2. Davies–Meyer: the committed-pair collision game, and what invertibility gives -/

/-- Number of 48-round constant lists under which the committed pair collides in the actual
    `spnDaviesMeyer48` (permutation output xor input, as in Rust `algebraic_step_plain`). -/
def spnDmCollisionCount (keys : List Tower128) (mdsA mdsB : Tower128)
    (s s' : Tower128 × Tower128) : Nat :=
  ((freshInputAssignments (rcPairs keys) spnRounds).filter fun ks =>
    decide (spnDaviesMeyer48 mdsA mdsB (rcSchedule ks) s =
      spnDaviesMeyer48 mdsA mdsB (rcSchedule ks) s')).length

/-- **Committed-pair collision bound.** A Davies–Meyer collision of `s ≠ s'` is the
    differential `s ⊕ s' → s ⊕ s'` of the permutation, so at most a `36/N²` fraction of the
    constant lists make a committed pair collide. Scope: the pair is fixed before the
    constants are drawn. Nothing is claimed about finding a colliding pair for given constants. -/
theorem spn48_davies_meyer_committed_pair_collision_count_le (mds : ValidSpnMdsPair 7)
    (keys : List Tower128) (hNd : keys.Nodup) (s s' : Tower128 × Tower128) (hNe : s ≠ s') :
    spnDmCollisionCount keys mds.mdsA mds.mdsB s s' ≤
      36 * (keys.length * keys.length) * (keys.length * keys.length) ^ 46 := by
  refine Nat.le_trans (Nat.le_of_eq ?_)
    (spn_differential_count_le mds keys hNd (pairXor s s') 46 s s' hNe)
  unfold spnDmCollisionCount spnFinalDiffCount
  apply congrArg List.length
  apply List.filter_congr
  intro ks hks
  have hLen : ks.length = spnRounds := mem_freshInputAssignments_length _ _ _ hks
  apply decide_eq_decide.mpr
  unfold spnDaviesMeyer48
  rw [← hLen, ← spnRunList_eq_iter, ← spnRunList_eq_iter]
  show (towerAdd 7 _ s.1, towerAdd 7 _ s.2) = (towerAdd 7 _ s'.1, towerAdd 7 _ s'.2) ↔
    (towerAdd 7 _ _, towerAdd 7 _ _) = (towerAdd 7 s.1 s'.1, towerAdd 7 s.2 s'.2)
  rw [Prod.mk.injEq, Prod.mk.injEq, tadd_cross_iff, tadd_cross_iff _ s.2]

/-- The committed-pair collision probability over `2^128` lane constants is below `2^-250`. -/
theorem spn48_davies_meyer_committed_pair_collision_atLeast_250_bits
    (mds : ValidSpnMdsPair 7) (keys : List Tower128) (hNd : keys.Nodup)
    (hN : keys.length = 2 ^ 128) (s s' : Tower128 × Tower128) (hNe : s ≠ s') :
    atLeastBits 250 ⟨spnDmCollisionCount keys mds.mdsA mds.mdsB s s',
      (2 ^ 128 * 2 ^ 128) ^ 48,
      Nat.pow_pos (Nat.mul_pos (Nat.two_pow_pos 128) (Nat.two_pow_pos 128))⟩ := by
  have h := spn48_davies_meyer_committed_pair_collision_count_le mds keys hNd s s' hNe
  rw [hN] at h
  show spnDmCollisionCount keys mds.mdsA mds.mdsB s s' * 2 ^ 250 ≤ (2 ^ 128 * 2 ^ 128) ^ 48
  refine Nat.le_trans (Nat.mul_le_mul_right _ h) ?_
  rw [show (2 ^ 128 * 2 ^ 128 : Nat) ^ 48 = (2 ^ 128 * 2 ^ 128) ^ 46 * (2 ^ 128 * 2 ^ 128) ^ 2 from
    Nat.pow_add _ 46 2, Nat.mul_right_comm]
  rw [Nat.mul_comm (36 * (2 ^ 128 * 2 ^ 128) * 2 ^ 250)]
  exact Nat.mul_le_mul_left _ (by decide)

/-- **Invertibility is not collision or preimage resistance.** Xor with a constant is a
    bijection of the 256-bit state, and its Davies–Meyer feed-forward is the constant map:
    every pair collides and every input is a preimage of `c`. Any collision or preimage claim
    for `spnDaviesMeyer48` must therefore use more than `pow7_tower128_bijective`. -/
theorem tooth_xor_constant_permutation_davies_meyer_collapses (c : Tower128 × Tower128) :
    IsBijective (fun x => pairXor x c) ∧ ∀ x, pairXor (pairXor x c) x = c := by
  have hInv : ∀ x, pairXor (pairXor x c) c = x := fun x => by
    unfold pairXor
    apply Prod.ext <;> simp only [towerAdd_assoc, towerAdd_self_zero, towerAdd_zero]
  refine ⟨⟨fun a b h => ?_, fun b => ⟨pairXor b c, hInv b⟩⟩, fun x => ?_⟩
  · have h2 := congrArg (fun z => pairXor z c) h
    simpa only [hInv] using h2
  · unfold pairXor
    apply Prod.ext
    · show towerAdd 7 (towerAdd 7 x.1 c.1) x.1 = c.1
      rw [towerAdd_comm 7 x.1 c.1, towerAdd_assoc, towerAdd_comm 7 x.1 x.1, towerAdd_self_zero,
        towerAdd_zero]
    · show towerAdd 7 (towerAdd 7 x.2 c.2) x.2 = c.2
      rw [towerAdd_comm 7 x.2 c.2, towerAdd_assoc, towerAdd_self_zero, towerAdd_zero]

end Qsag
end

#verify_constructive
  Qsag.spnLinearMix_eq_iff
  Qsag.spn_two_round_differential_count_le
  Qsag.spn_differential_count_le
  Qsag.spn48_davies_meyer_committed_pair_collision_count_le
  Qsag.spn48_davies_meyer_committed_pair_collision_atLeast_250_bits
  Qsag.tooth_xor_constant_permutation_davies_meyer_collapses
