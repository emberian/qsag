module
/-
# Qsag.Oracle.SpnFixedConstantTrail — the deployed shape: fixed public constants, random input

`Qsag.SpnRoundConstantExperiment` draws the round constants after the pair is committed.
Deployment is the other way round: the constants are public and fixed, and only the input
can be random. This module states what the component lemmas give in that experiment.

* `spn_fixed_constants_trail_count_le`: for ANY fixed constant list of at least two rounds,
  any nonzero input difference and any S-box trail, at most `36` inputs out of any
  duplicate-free input list follow the trail. Reason: one of the first two rounds has both
  lanes active (branch number three), the state entering that round is an injective image
  of the input, and each lane condition has at most six roots.
* With the atom floor of `HashTrailSampling` (a realized trail has at least one input) the
  fixed-constant trail probability over the `2^256` inputs is between `2^-256` and
  `36·2^-256`: about 251 to 256 bits, never the `72·125` bits of the product.
  `spn_fixed_constants_trail_atLeast_250_bits` records the upper end and
  `spn48_full_list_fixed_constants_trail_sandwich` both ends on the full list.
* `towerAll`: an explicit duplicate-free enumeration of `TowerElem k` of length `2^(2^k)`,
  so the hypotheses `keys.Nodup`, `keys.length = 2^128` and `coins.length = 2^256` used by
  the experiment theorems are inhabited (`spn_experiment_sample_lists_inhabited`).

No statement here bounds a differential (all trails summed) under fixed constants; that is
the open cryptanalytic question for the public permutation and is not derivable from the
root count, the branch number or the active-box count.
-/
public import Qsag.Oracle.SpnRoundConstantExperiment
import all Qsag.Oracle.SpnRoundConstantExperiment
import all Qsag.Oracle.HashTrailSampling
import all Qsag.Oracle.ParallelSeededSpnSecurity

public section
namespace Qsag
set_option autoImplicit false

/-! ## §1. Counting a duplicate-free list of pairs inside a rectangle -/

theorem rcFilter_length_le_of_imp {α : Type} (p q : α → Bool) :
    ∀ l : List α, (∀ x ∈ l, p x = true → q x = true) →
      (l.filter p).length ≤ (l.filter q).length
  | [], _ => Nat.le_refl 0
  | x :: xs, h => by
    have ih := rcFilter_length_le_of_imp p q xs fun y hy => h y (List.mem_cons_of_mem _ hy)
    by_cases hp : p x = true
    · rw [List.filter_cons_of_pos hp, List.filter_cons_of_pos (h x List.mem_cons_self hp)]
      exact Nat.succ_le_succ ih
    · rw [List.filter_cons_of_neg hp]
      by_cases hq : q x = true
      · rw [List.filter_cons_of_pos hq]; exact Nat.le_succ_of_le ih
      · rw [List.filter_cons_of_neg hq]; exact ih

theorem rcFilter_split_length {α : Type} (p r : α → Bool) :
    ∀ l : List α, (l.filter p).length =
      (l.filter fun x => p x && r x).length + (l.filter fun x => p x && !r x).length
  | [] => rfl
  | x :: xs => by
    have ih := rcFilter_split_length p r xs
    by_cases hp : p x = true
    · by_cases hr : r x = true
      · have h1 : (p x && r x) = true := by rw [hp, hr]; rfl
        have h2 : ¬ (p x && !r x) = true := by rw [hp, hr]; exact Bool.false_ne_true
        rw [List.filter_cons_of_pos hp, List.filter_cons_of_pos (p := fun x => p x && r x) h1,
          List.filter_cons_of_neg (p := fun x => p x && !r x) h2,
          List.length_cons, List.length_cons, ih, Nat.add_right_comm]
      · have hr' : r x = false := Bool.eq_false_iff.mpr hr
        have h1 : ¬ (p x && r x) = true := by rw [hp, hr']; exact Bool.false_ne_true
        have h2 : (p x && !r x) = true := by rw [hp, hr']; rfl
        rw [List.filter_cons_of_pos hp, List.filter_cons_of_neg (p := fun x => p x && r x) h1,
          List.filter_cons_of_pos (p := fun x => p x && !r x) h2,
          List.length_cons, List.length_cons, ih, Nat.add_assoc]
    · have hp' : p x = false := Bool.eq_false_iff.mpr hp
      have h1 : ¬ (p x && r x) = true := by rw [hp']; exact Bool.false_ne_true
      have h2 : ¬ (p x && !r x) = true := by rw [hp']; exact Bool.false_ne_true
      rw [List.filter_cons_of_neg hp, List.filter_cons_of_neg (p := fun x => p x && r x) h1,
        List.filter_cons_of_neg (p := fun x => p x && !r x) h2, ih]

theorem nodup_map_snd_of_fst_eq {α : Type} (a : α) :
    ∀ L : List (α × α), L.Nodup → (∀ x ∈ L, x.1 = a) → (L.map Prod.snd).Nodup
  | [], _, _ => List.nodup_nil
  | x :: xs, hNd, hFst => by
    have hx := List.nodup_cons.mp hNd
    rw [List.map_cons]
    refine List.nodup_cons.mpr ⟨fun hm => ?_,
      nodup_map_snd_of_fst_eq a xs hx.2 fun y hy => hFst y (List.mem_cons_of_mem _ hy)⟩
    obtain ⟨y, hy, hySnd⟩ := List.mem_map.mp hm
    have hyEq : y = x := Prod.ext
      ((hFst y (List.mem_cons_of_mem _ hy)).trans (hFst x List.mem_cons_self).symm) hySnd
    rw [hyEq] at hy
    exact hx.1 hy

/-- If the first coordinates satisfying `p` take at most `m` distinct values and the second
    coordinates satisfying `q` at most `n`, a duplicate-free list of pairs has at most `m·n`
    members in the rectangle `p × q`. No enumeration of the coordinate type is needed. -/
theorem rect_count_le {α : Type} [DecidableEq α] (q : α → Bool) (n : Nat)
    (hq : ∀ S : List α, S.Nodup → (S.filter q).length ≤ n) :
    ∀ (m : Nat) (p : α → Bool), (∀ S : List α, S.Nodup → (S.filter p).length ≤ m) →
      ∀ l : List (α × α), l.Nodup → (l.filter fun x => p x.1 && q x.2).length ≤ m * n
  | 0, p, hp, l, _ => by
    rw [filter_length_eq_zero _ l]
    · exact Nat.zero_le _
    · intro x _ hx
      have hp1 : p x.1 = true := (Bool.and_eq_true_iff.mp hx).1
      have hB := hp [x.1] (List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩)
      rw [List.filter_cons_of_pos hp1] at hB
      exact Nat.not_succ_le_zero _ hB
  | m + 1, p, hp, l, hNd => by
    cases hF : l.filter (fun x => p x.1 && q x.2) with
    | nil => exact Nat.zero_le _
    | cons x0 more =>
      have hx0 : x0 ∈ l.filter (fun x => p x.1 && q x.2) := by rw [hF]; exact List.mem_cons_self
      have hpx0 : p x0.1 = true := (Bool.and_eq_true_iff.mp (List.mem_filter.mp hx0).2).1
      rw [← hF, rcFilter_split_length _ (fun x => decide (x.1 = x0.1)) l]
      have h1 : (l.filter fun x => (p x.1 && q x.2) && decide (x.1 = x0.1)).length ≤ n := by
        have hT : ((l.filter fun x => decide (x.1 = x0.1)).map Prod.snd).Nodup :=
          nodup_map_snd_of_fst_eq x0.1 _ (List.Pairwise.filter _ hNd)
            fun x hx => of_decide_eq_true (List.mem_filter.mp hx).2
        have hB := hq _ hT
        rw [List.filter_map, List.length_map, List.filter_filter] at hB
        refine Nat.le_trans (rcFilter_length_le_of_imp _ _ l fun x _ hx => ?_) hB
        have h3 := Bool.and_eq_true_iff.mp hx
        exact Bool.and_eq_true_iff.mpr ⟨(Bool.and_eq_true_iff.mp h3.1).2, h3.2⟩
      have h2 : (l.filter fun x => (p x.1 && q x.2) && !decide (x.1 = x0.1)).length ≤ m * n := by
        refine Nat.le_trans (Nat.le_of_eq ?_)
          (rect_count_le q n hq m (fun a => p a && !decide (a = x0.1)) ?_ l hNd)
        · apply congrArg List.length
          apply List.filter_congr
          intro x _
          show ((p x.1 && q x.2) && !decide (x.1 = x0.1)) =
            ((p x.1 && !decide (x.1 = x0.1)) && q x.2)
          cases p x.1 <;> cases q x.2 <;> cases decide (x.1 = x0.1) <;> rfl
        · intro S hS
          have hNd' : (x0.1 :: S.filter fun a => p a && !decide (a = x0.1)).Nodup :=
            List.nodup_cons.mpr ⟨fun hm => by
              have hb := (Bool.and_eq_true_iff.mp (List.mem_filter.mp hm).2).2
              rw [decide_eq_true rfl] at hb
              exact Bool.false_ne_true hb, List.Pairwise.filter _ hS⟩
          have hB := hp _ hNd'
          have hSelf : (S.filter fun a => p a && !decide (a = x0.1)).filter p =
              S.filter fun a => p a && !decide (a = x0.1) :=
            List.filter_eq_self.mpr fun a ha =>
              (Bool.and_eq_true_iff.mp (List.mem_filter.mp ha).2).1
          rw [List.filter_cons_of_pos hpx0, List.length_cons, hSelf] at hB
          exact Nat.le_of_succ_le_succ hB
      exact Nat.le_trans (Nat.add_le_add h1 h2)
        (Nat.le_of_eq (by rw [Nat.succ_mul, Nat.add_comm]))

/-! ## §2. Lane roots as a function of the input, and one fully active round -/

theorem sboxLaneDiff_input_symm (k a δ : Tower128) :
    sboxLaneDiff k a (towerAdd 7 a δ) = sboxLaneDiff a k (towerAdd 7 k δ) := by
  unfold sboxLaneDiff
  rw [towerAdd_comm 7 a k, towerAdd_assoc 7 a δ k, towerAdd_comm 7 (towerAdd 7 k δ) a,
    towerAdd_comm 7 δ k]

/-- For a fixed lane constant and nonzero difference, at most six lane inputs give a
    prescribed x^7 output difference. Same root bound, with the input as the unknown. -/
theorem laneRoots_le_six (k δ γ : Tower128) (hδ : δ ≠ towerZero 7) (S : List Tower128)
    (hS : S.Nodup) :
    (S.filter fun a => decide (sboxLaneDiff k a (towerAdd 7 a δ) = γ)).length ≤ 6 := by
  have h := laneCount_le_laneBound S hS k (towerAdd 7 k δ) γ
  unfold laneBound at h
  rw [towerAdd_cancel, ite_eq_right hδ] at h
  refine Nat.le_trans (Nat.le_of_eq ?_) h
  unfold laneCount
  apply congrArg List.length
  apply List.filter_congr
  intro a _
  rw [sboxLaneDiff_input_symm]

/-- A fully active S-box layer with fixed constant: at most `36` states of any
    duplicate-free list produce a prescribed output difference. -/
theorem active_layer_states_le_36 (rc δ γ : Tower128 × Tower128)
    (h1 : δ.1 ≠ towerZero 7) (h2 : δ.2 ≠ towerZero 7) (l : List (Tower128 × Tower128))
    (hNd : l.Nodup) :
    (l.filter fun u => decide (sboxPairDiff rc u (pairXor u δ) = γ)).length ≤ 36 := by
  have hR := rect_count_le
    (fun b => decide (sboxLaneDiff rc.2 b (towerAdd 7 b δ.2) = γ.2)) 6
    (fun S hS => laneRoots_le_six rc.2 δ.2 γ.2 h2 S hS) 6
    (fun a => decide (sboxLaneDiff rc.1 a (towerAdd 7 a δ.1) = γ.1))
    (fun S hS => laneRoots_le_six rc.1 δ.1 γ.1 h1 S hS) l hNd
  refine Nat.le_trans (rcFilter_length_le_of_imp _ _ l fun u _ hu => ?_) hR
  have hEq : sboxPairDiff rc u (pairXor u δ) = γ := of_decide_eq_true hu
  exact Bool.and_eq_true_iff.mpr
    ⟨decide_eq_true (congrArg Prod.fst hEq), decide_eq_true (congrArg Prod.snd hEq)⟩

theorem laneActiveWeight_le_one_left (st : Tower128 × Tower128) (h : st.1 = towerZero 7) :
    laneActiveWeight 7 st ≤ 1 := by
  unfold laneActiveWeight
  rw [ite_eq_left h]
  by_cases h2 : st.2 = towerZero 7
  · rw [ite_eq_left h2]; decide
  · rw [ite_eq_right h2]; decide

theorem laneActiveWeight_le_one_right (st : Tower128 × Tower128) (h : st.2 = towerZero 7) :
    laneActiveWeight 7 st ≤ 1 := by
  unfold laneActiveWeight
  rw [ite_eq_left h]
  by_cases h1 : st.1 = towerZero 7
  · rw [ite_eq_left h1]; decide
  · rw [ite_eq_right h1]; decide

theorem pairXor_eq_right {a b c : Tower128 × Tower128} (h : pairXor a b = c) :
    b = pairXor a c := by
  rw [← h]
  unfold pairXor
  exact Prod.ext (towerAdd_cancel 7 a.1 b.1).symm (towerAdd_cancel 7 a.2 b.2).symm

/-! ## §3. Fixed constants: at most 36 inputs follow any trail of two or more rounds -/

/-- **Fixed public constants.** For every constant list `rc1 :: rc2 :: rest` (any values:
    cSHAKE output, zero, adversarial), every nonzero input difference `δ`, every S-box trail
    and every duplicate-free input list, at most `36` inputs `x` make the pair
    `(x, x ⊕ δ)` follow the trail. -/
theorem spn_fixed_constants_trail_count_le (mds : ValidSpnMdsPair 7)
    (rc1 rc2 : Tower128 × Tower128) (rest : List (Tower128 × Tower128))
    (δ : Tower128 × Tower128) (hδ : δ ≠ (towerZero 7, towerZero 7))
    (trail : List (Tower128 × Tower128)) (inputs : List (Tower128 × Tower128))
    (hNd : inputs.Nodup) :
    (inputs.filter fun x => decide
      (spnSboxTrail mds.mdsA mds.mdsB (rc1 :: rc2 :: rest) x (pairXor x δ) = trail)).length ≤ 36 := by
  cases hF : inputs.filter (fun x => decide
      (spnSboxTrail mds.mdsA mds.mdsB (rc1 :: rc2 :: rest) x (pairXor x δ) = trail)) with
  | nil => exact Nat.zero_le _
  | cons x0 more =>
    rw [← hF]
    have hx0 : x0 ∈ inputs.filter (fun x => decide
        (spnSboxTrail mds.mdsA mds.mdsB (rc1 :: rc2 :: rest) x (pairXor x δ) = trail)) := by
      rw [hF]; exact List.mem_cons_self
    have hT0 : spnSboxTrail mds.mdsA mds.mdsB (rc1 :: rc2 :: rest) x0 (pairXor x0 δ) = trail :=
      of_decide_eq_true (List.mem_filter.mp hx0).2
    -- the trail's first two entries, read off the realizing input
    obtain ⟨g1, g2, tl, hTrail⟩ : ∃ g1 g2 tl, trail = g1 :: g2 :: tl := ⟨_, _, _, hT0.symm⟩
    subst hTrail
    have hHead : ∀ x, spnSboxTrail mds.mdsA mds.mdsB (rc1 :: rc2 :: rest) x (pairXor x δ) =
        g1 :: g2 :: tl →
        sboxPairDiff rc1 x (pairXor x δ) = g1 ∧
        sboxPairDiff rc2 (spnRound128 mds.mdsA mds.mdsB rc1 x)
          (pairXor (spnRound128 mds.mdsA mds.mdsB rc1 x) (spnLinearMix 7 mds.mdsA mds.mdsB g1)) =
          g2 := by
      intro x hx
      have hA : sboxPairDiff rc1 x (pairXor x δ) = g1 := List.head_eq_of_cons_eq hx
      have hB : sboxPairDiff rc2 (spnRound128 mds.mdsA mds.mdsB rc1 x)
          (spnRound128 mds.mdsA mds.mdsB rc1 (pairXor x δ)) = g2 :=
        List.head_eq_of_cons_eq (List.tail_eq_of_cons_eq hx)
      have hD := spnRound128_diff mds.mdsA mds.mdsB rc1 x (pairXor x δ)
      rw [hA] at hD
      rw [pairXor_eq_right hD] at hB
      exact ⟨hA, hB⟩
    have hg1 : g1.1 = towerZero 7 ↔ δ.1 = towerZero 7 := by
      rw [← (hHead x0 hT0).1]
      show sboxLaneDiff rc1.1 x0.1 (towerAdd 7 x0.1 δ.1) = towerZero 7 ↔ _
      rw [sboxLaneDiff_eq_zero_iff]
      constructor
      · intro h
        have h2 := congrArg (towerAdd 7 x0.1) h
        rw [towerAdd_self_zero, towerAdd_cancel] at h2
        exact h2.symm
      · intro h; rw [h, towerAdd_zero]
    have hg2 : g1.2 = towerZero 7 ↔ δ.2 = towerZero 7 := by
      rw [← (hHead x0 hT0).1]
      show sboxLaneDiff rc1.2 x0.2 (towerAdd 7 x0.2 δ.2) = towerZero 7 ↔ _
      rw [sboxLaneDiff_eq_zero_iff]
      constructor
      · intro h
        have h2 := congrArg (towerAdd 7 x0.2) h
        rw [towerAdd_self_zero, towerAdd_cancel] at h2
        exact h2.symm
      · intro h; rw [h, towerAdd_zero]
    by_cases hA : δ.1 ≠ towerZero 7 ∧ δ.2 ≠ towerZero 7
    · -- first round fully active
      refine Nat.le_trans (rcFilter_length_le_of_imp _ _ inputs fun x _ hx => ?_)
        (active_layer_states_le_36 rc1 δ g1 hA.1 hA.2 inputs hNd)
      exact decide_eq_true (hHead x (of_decide_eq_true hx)).1
    · -- otherwise the branch number forces the second round to be fully active
      have hg1Ne : g1 ≠ (towerZero 7, towerZero 7) := fun h0 =>
        hδ (Prod.ext (hg1.mp (congrArg Prod.fst h0)) (hg2.mp (congrArg Prod.snd h0)))
      have hBr := (spnLinearMix_branch_number_three mds g1 hg1Ne).2
      have hW1 : laneActiveWeight 7 g1 ≤ 1 := by
        by_cases h1 : δ.1 = towerZero 7
        · exact laneActiveWeight_le_one_left g1 (hg1.mpr h1)
        · by_cases h2 : δ.2 = towerZero 7
          · exact laneActiveWeight_le_one_right g1 (hg2.mpr h2)
          · exact absurd ⟨h1, h2⟩ hA
      have hM1 : (spnLinearMix 7 mds.mdsA mds.mdsB g1).1 ≠ towerZero 7 := fun h0 => by
        have hW := laneActiveWeight_le_one_left _ h0
        omega
      have hM2 : (spnLinearMix 7 mds.mdsA mds.mdsB g1).2 ≠ towerZero 7 := fun h0 => by
        have hW := laneActiveWeight_le_one_right _ h0
        omega
      have hInj : ∀ a b : Tower128 × Tower128,
          spnRound128 mds.mdsA mds.mdsB rc1 a = spnRound128 mds.mdsA mds.mdsB rc1 b → a = b :=
        fun a b hab => if h : a = b then h else absurd hab (spnRound128_ne mds rc1 a b h)
      have hB := active_layer_states_le_36 rc2 (spnLinearMix 7 mds.mdsA mds.mdsB g1) g2 hM1 hM2
        (inputs.map (spnRound128 mds.mdsA mds.mdsB rc1))
        (rcNodup_map_of_injective _ hInj inputs hNd)
      rw [List.filter_map, List.length_map] at hB
      refine Nat.le_trans (rcFilter_length_le_of_imp _ _ inputs fun x _ hx => ?_) hB
      exact decide_eq_true (hHead x (of_decide_eq_true hx)).2

/-- On a `2^256`-element input list the fixed-constant trail probability is at most
    `36 / 2^256 < 2^-250`. Together with the `2^-256` atom floor this locates it; the
    `(6/2^128)^72` product is not a bound for this experiment. -/
theorem spn_fixed_constants_trail_atLeast_250_bits (mds : ValidSpnMdsPair 7)
    (rc1 rc2 : Tower128 × Tower128) (rest : List (Tower128 × Tower128))
    (δ : Tower128 × Tower128) (hδ : δ ≠ (towerZero 7, towerZero 7))
    (trail : List (Tower128 × Tower128)) (inputs : List (Tower128 × Tower128))
    (hNd : inputs.Nodup) :
    atLeastBits 250 ⟨(inputs.filter fun x => decide
      (spnSboxTrail mds.mdsA mds.mdsB (rc1 :: rc2 :: rest) x (pairXor x δ) = trail)).length,
      2 ^ 256, Nat.two_pow_pos 256⟩ :=
  Nat.le_trans (Nat.mul_le_mul_right _
    (spn_fixed_constants_trail_count_le mds rc1 rc2 rest δ hδ trail inputs hNd))
    (show 36 * 2 ^ 250 ≤ 2 ^ 256 by decide)

/-! ## §4. The sample lists exist -/

theorem pairList_nodup {α : Type} (l2 : List α) (h2 : l2.Nodup) :
    ∀ l1 : List α, l1.Nodup → (l1.flatMap fun a => l2.map fun b => (a, b)).Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h1 => by
    have hx := List.nodup_cons.mp h1
    rw [List.flatMap_cons]
    refine List.nodup_append.mpr
      ⟨rcNodup_map_of_injective _ (fun a b hab => congrArg Prod.snd hab) l2 h2,
        pairList_nodup l2 h2 xs hx.2, fun u hu v hv huv => ?_⟩
    obtain ⟨b, _, hb⟩ := List.mem_map.mp hu
    obtain ⟨a, ha, hav⟩ := List.mem_flatMap.mp hv
    obtain ⟨c, _, hc⟩ := List.mem_map.mp hav
    have hEq : x = a := by
      have h3 := congrArg Prod.fst huv
      rw [← hb, ← hc] at h3
      exact h3
    rw [← hEq] at ha
    exact hx.1 ha

theorem rcPairs_nodup {α : Type} (keys : List α) (h : keys.Nodup) : (rcPairs keys).Nodup :=
  pairList_nodup keys h keys h

/-- Every element of the level-`k` Wiedemann tower, once. -/
def towerAll : (k : Nat) → List (TowerElem k)
  | 0 => [false, true]
  | k + 1 => rcPairs (towerAll k)

theorem towerAll_length : ∀ k : Nat, (towerAll k).length = 2 ^ 2 ^ k
  | 0 => rfl
  | k + 1 => by
    show (rcPairs (towerAll k)).length = _
    rw [rcPairs_length, towerAll_length k, ← Nat.pow_add, Nat.pow_succ 2 k, Nat.mul_two]

theorem towerAll_nodup : ∀ k : Nat, (towerAll k).Nodup
  | 0 => by decide
  | k + 1 => rcPairs_nodup _ (towerAll_nodup k)

theorem towerAll_complete : ∀ (k : Nat) (x : TowerElem k), x ∈ towerAll k
  | 0, false => List.mem_cons_self
  | 0, true => List.mem_cons_of_mem _ List.mem_cons_self
  | k + 1, x =>
    List.mem_flatMap.mpr ⟨x.1, towerAll_complete k x.1,
      List.mem_map.mpr ⟨x.2, towerAll_complete k x.2, rfl⟩⟩

theorem mem_rcPairs {α : Type} (keys : List α) (x : α × α) (h1 : x.1 ∈ keys)
    (h2 : x.2 ∈ keys) : x ∈ rcPairs keys :=
  List.mem_flatMap.mpr ⟨x.1, h1, List.mem_map.mpr ⟨x.2, h2, rfl⟩⟩

theorem towerAll_length_128 : (towerAll 7).length = 2 ^ 128 := towerAll_length 7

theorem towerAll_pairs_length_256 : (rcPairs (towerAll 7)).length = 2 ^ 256 := by
  rw [rcPairs_length, towerAll_length_128]

/-- The lane-constant list of `2^128` elements and the input list of `2^256` states assumed
    by the experiment theorems exist, are duplicate-free and contain every element. -/
theorem spn_experiment_sample_lists_inhabited :
    (towerAll 7).Nodup ∧ (towerAll 7).length = 2 ^ 128 ∧ (∀ x : Tower128, x ∈ towerAll 7) ∧
    (rcPairs (towerAll 7)).Nodup ∧ (rcPairs (towerAll 7)).length = 2 ^ 256 :=
  ⟨towerAll_nodup 7, towerAll_length_128, towerAll_complete 7,
    rcPairs_nodup _ (towerAll_nodup 7), towerAll_pairs_length_256⟩

/-- Regime 1 on the full lists, deployed mixing constants: a committed 48-round trail under
    uniformly drawn constants has probability below `2^-256`. -/
theorem spn48_full_list_committed_trail_bits
    (s s' : Tower128 × Tower128) (hNe : s ≠ s') (trail : List (Tower128 × Tower128))
    (hLen : trail.length = spnRounds) :
    atLeastBits 256 ⟨spnTrailCount (towerAll 7) parallelSeededMdsPair.mdsA
        parallelSeededMdsPair.mdsB s s' trail, (2 ^ 128 * 2 ^ 128) ^ 48,
      Nat.pow_pos (Nat.mul_pos (Nat.two_pow_pos 128) (Nat.two_pow_pos 128))⟩ :=
  (spn48_committed_trail_atLeast_256_bits parallelSeededMdsPair (towerAll 7) (towerAll_nodup 7)
    towerAll_length_128 s s' hNe trail hLen).2

/-- Regime 2 on the full input list, deployed mixing constants, any fixed round constants:
    at most 36 of the `2^256` inputs follow a given trail. -/
theorem spn48_full_list_fixed_constants_trail_count
    (δ : Tower128 × Tower128) (hδ : δ ≠ (towerZero 7, towerZero 7))
    (trail : List (Tower128 × Tower128))
    (rc1 rc2 : Tower128 × Tower128) (rest : List (Tower128 × Tower128)) :
    ((rcPairs (towerAll 7)).filter fun x => decide
      (spnSboxTrail parallelSeededMdsPair.mdsA parallelSeededMdsPair.mdsB (rc1 :: rc2 :: rest)
        x (pairXor x δ) = trail)).length ≤ 36 :=
  spn_fixed_constants_trail_count_le parallelSeededMdsPair rc1 rc2 rest δ hδ trail _
    (rcPairs_nodup _ (towerAll_nodup 7))

/-- Regime 2, both ends, on the full input list: the trail realized by any input `x0` under
    any fixed constants is followed by at least one and at most 36 of the `2^256` inputs.
    (`realized_trace_has_positive_count` is the atom floor of `HashTrailSampling`; the general
    refutation `fixedSpnDifferenceTrace_not_bounded_by_component_product` has its two list
    hypotheses discharged by `spn_experiment_sample_lists_inhabited` and `mem_rcPairs`. The
    count is kept out of `Nat` arithmetic with large literals on purpose: the kernel would try
    to evaluate the enumeration.) -/
theorem spn48_full_list_fixed_constants_trail_sandwich
    (δ : Tower128 × Tower128) (hδ : δ ≠ (towerZero 7, towerZero 7))
    (rc1 rc2 : Tower128 × Tower128) (rest : List (Tower128 × Tower128))
    (x0 : Tower128 × Tower128) :
    0 < ((rcPairs (towerAll 7)).filter fun x => decide
      (spnSboxTrail parallelSeededMdsPair.mdsA parallelSeededMdsPair.mdsB (rc1 :: rc2 :: rest)
          x (pairXor x δ) =
        spnSboxTrail parallelSeededMdsPair.mdsA parallelSeededMdsPair.mdsB (rc1 :: rc2 :: rest)
          x0 (pairXor x0 δ))).length ∧
    ((rcPairs (towerAll 7)).filter fun x => decide
      (spnSboxTrail parallelSeededMdsPair.mdsA parallelSeededMdsPair.mdsB (rc1 :: rc2 :: rest)
          x (pairXor x δ) =
        spnSboxTrail parallelSeededMdsPair.mdsA parallelSeededMdsPair.mdsB (rc1 :: rc2 :: rest)
          x0 (pairXor x0 δ))).length ≤ 36 :=
  ⟨realized_trace_has_positive_count (rcPairs (towerAll 7))
      (fun x => spnSboxTrail parallelSeededMdsPair.mdsA parallelSeededMdsPair.mdsB
        (rc1 :: rc2 :: rest) x (pairXor x δ)) x0
      (mem_rcPairs _ x0 (towerAll_complete 7 x0.1) (towerAll_complete 7 x0.2)),
    spn48_full_list_fixed_constants_trail_count δ hδ _ rc1 rc2 rest⟩

end Qsag
end

#verify_constructive
  Qsag.rect_count_le
  Qsag.spn_fixed_constants_trail_count_le
  Qsag.spn_fixed_constants_trail_atLeast_250_bits
  Qsag.spn_experiment_sample_lists_inhabited
  Qsag.spn48_full_list_committed_trail_bits
  Qsag.spn48_full_list_fixed_constants_trail_count
  Qsag.spn48_full_list_fixed_constants_trail_sandwich
