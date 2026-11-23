module

public import Qsag.Coding.AffineProximity
public import Qsag.Math.CoeffPoly
import Qsag.Math.Tactic.CommRing
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.SuccinctWhirAgg

open CommRingOps RoundPoly
variable {K : Type} [LawfulField K] [DecidableEq K]

local infixl:65 " +ᵍ " => add
local infixl:65 " -ᵍ " => sub
local infixl:70 " *ᵍ " => mul

@[expose] def binaryFoldAgrees (f g : K → K) (Q : K → List K) (t z : K) : Bool :=
  decide (evalCoeffs (Q t) z = f z +ᵍ t *ᵍ g z)

omit [DecidableEq K] in
/-- Recover the slope of a line from two of its values. -/
private theorem recover_line (a b f g : K) (hne : a ≠ b) :
    LawfulField.inv (a -ᵍ b) *ᵍ ((f +ᵍ a *ᵍ g) -ᵍ (f +ᵍ b *ᵍ g)) = g := by
  calc
    _ = g *ᵍ ((a -ᵍ b) *ᵍ LawfulField.inv (a -ᵍ b)) := by constructive_ring
    _ = _ := by rw [LawfulField.mul_inv_cancel (fun h => hne (LawfulCommRing.sub_eq_zero_iff.mp h)),
      LawfulCommRing.mul_one]

omit [LawfulField K] [DecidableEq K] in
private theorem bounded_unique {L : List K} (hn : L.Nodup)
    (h : ∀ u ∈ L, ∀ v ∈ L, u = v) : L.length ≤ 1 := by
  cases L with
  | nil => exact Nat.zero_le _
  | cons x xs =>
    cases xs with
    | nil => exact Nat.le_refl _
    | cons y ys =>
      exact absurd (h x (.head _) y (.tail _ (.head _))) (fun eq =>
        (List.nodup_cons.mp hn).1 (eq ▸ List.mem_cons_self))

/-- At most max(1, n) distinct scalar challenges admit a close degree-<k response
    without joint agreement of the two input words. The anchor responses and
    every subsequent response agree on at least k common coordinates. -/
theorem binaryFold_exceptional_challenges (D S : List K) (k A : Nat)
    (f g : K → K) (Q : K → List K) (hd : D.Nodup) (hs : S.Nodup)
    (hk : 0 < k) (hTriple : 2 * D.length + k ≤ 3 * A)
    (hQ : ∀ t ∈ S, (Q t).length ≤ k ∧ A ≤ (D.filter (binaryFoldAgrees f g Q t)).length)
    (hfar : ∀ E O : List K, E.length ≤ k → O.length ≤ k →
      (D.filter (fun z => decide (evalCoeffs E z = f z ∧ evalCoeffs O z = g z))).length < A) :
    S.length ≤ max 1 D.length := by
  cases S with
  | nil => exact Nat.zero_le _
  | cons a tail =>
    cases tail with
    | nil => exact Nat.le_max_left _ _
    | cons b rest =>
      let S := a :: b :: rest
      have ha : a ∈ S := .head _
      have hb : b ∈ S := .tail _ (.head _)
      have hab : a ≠ b := fun eq => (List.nodup_cons.mp hs).1 (eq ▸ List.mem_cons_self)
      let O := (subCoeffs (Q a) (Q b)).map (mul (LawfulField.inv (a -ᵍ b)))
      let E := subCoeffs (Q a) (O.map (mul a))
      let line := fun t => subCoeffs E (O.map (mul (neg t)))
      have hO : O.length ≤ k := by
        simp only [O, List.length_map, subCoeffs_length]
        exact Nat.max_le.mpr ⟨(hQ a ha).1, (hQ b hb).1⟩
      have hE : E.length ≤ k := by
        simp only [E, List.length_map, subCoeffs_length]
        exact Nat.max_le.mpr ⟨(hQ a ha).1,hO⟩
      have evalLine (t z : K) : evalCoeffs (line t) z = evalCoeffs E z +ᵍ t *ᵍ evalCoeffs O z := by
        simp only [line, evalCoeffs_sub, RoundPoly.evalCoeffs_map_mul]
        constructive_ring
      let good := binaryFoldAgrees f g Q
      have collinear (t : K) (ht : t ∈ S) (z : K) :
          evalCoeffs (Q t) z = evalCoeffs E z +ᵍ t *ᵍ evalCoeffs O z := by
        let U := D.filter fun x => (good a x && good b x) && good t x
        have hlen : k ≤ U.length := by
          have h₁ := filter_overlap_len (good a) (good b) D
          have h₂ := filter_overlap_len (fun x => good a x && good b x) (good t) D
          have h₃ := (hQ a ha).2
          have h₄ := (hQ b hb).2
          have h₅ := (hQ t ht).2
          change A ≤ (D.filter (good a)).length at h₃
          change A ≤ (D.filter (good b)).length at h₄
          change A ≤ (D.filter (good t)).length at h₅
          dsimp only [U]
          omega
        have hlin : (line t).length ≤ k := by
          simp only [line, subCoeffs_length, List.length_map]; exact Nat.max_le.mpr ⟨hE,hO⟩
        have hk' : k - 1 + 1 = k := by omega
        have same := trimPoly_eq_of_agree_on_nodup (d := k-1) (P := Q t) (Q := line t)
          (by rw [hk']; exact (hQ t ht).1) (by rw [hk']; exact hlin)
          (U := U) (List.Pairwise.filter _ hd) (by rw [hk']; exact hlen) (fun x hx => by
            have hh := (List.mem_filter.mp hx).2
            change ((good a x && good b x) && good t x) = true at hh
            simp only [good, binaryFoldAgrees, Bool.and_eq_true, decide_eq_true_eq] at hh
            have ho : evalCoeffs O x = g x := by
              dsimp only [O]
              rw [RoundPoly.evalCoeffs_map_mul, evalCoeffs_sub, hh.1.1, hh.1.2]
              exact recover_line a b _ _ hab
            rw [evalLine]
            dsimp only [E]
            rw [evalCoeffs_sub, RoundPoly.evalCoeffs_map_mul, ho, hh.1.1, hh.2]
            constructive_ring)
        rw [← evalCoeffs_trimPoly z (Q t), same, evalCoeffs_trimPoly, evalLine]
      let joint := fun z => decide (evalCoeffs E z = f z ∧ evalCoeffs O z = g z)
      let hit := fun z t => good t z && !joint z
      have covered (t : K) (ht : t ∈ S) : ∃ z ∈ D, hit z t = true := by
        apply Decidable.byContradiction
        intro hn
        have le := nodup_length_le_of_subset (L := D.filter (good t)) (M := D.filter joint)
          (List.Pairwise.filter _ hd) (fun z hz => by
            obtain ⟨hm, hg⟩ := List.mem_filter.mp hz
            refine List.mem_filter.mpr ⟨hm, ?_⟩
            cases hj : joint z with
            | true => rfl
            | false => exact False.elim (hn ⟨z,hm,by simp only [hit,hg,hj]; rfl⟩))
        exact Nat.not_lt_of_ge (Nat.le_trans (hQ t ht).2 le) (hfar E O hE hO)
      have perPoint (z : K) : (S.filter (hit z)).length ≤ 1 := by
        apply bounded_unique (List.Pairwise.filter _ hs)
        intro u hu v hv
        obtain ⟨hu, hup⟩ := List.mem_filter.mp hu
        obtain ⟨hv, hvp⟩ := List.mem_filter.mp hv
        apply Decidable.byContradiction
        intro huv
        have gu := of_decide_eq_true (Bool.and_eq_true_iff.mp hup).1
        have gv := of_decide_eq_true (Bool.and_eq_true_iff.mp hvp).1
        change evalCoeffs (Q u) z = f z +ᵍ u *ᵍ g z at gu
        change evalCoeffs (Q v) z = f z +ᵍ v *ᵍ g z at gv
        rw [collinear u hu] at gu
        rw [collinear v hv] at gv
        have eqO := recover_line u v (evalCoeffs E z) (evalCoeffs O z) huv
        rw [gu, gv, recover_line u v (f z) (g z) huv] at eqO
        have eqE : evalCoeffs E z = f z := by
          rw [← eqO] at gu
          calc
            _ = (evalCoeffs E z +ᵍ u *ᵍ g z) -ᵍ u *ᵍ g z := by constructive_ring
            _ = _ := by rw [gu]; constructive_ring
        have hj : joint z = true := decide_eq_true ⟨eqE, eqO.symm⟩
        have hf := (Bool.and_eq_true_iff.mp hup).2
        rw [hj] at hf
        contradiction
      have bound := SlicedJet.cover_count hit (Function.const K 1) 1 D S hs (fun z _ => perPoint z) covered
      have ones (n : Nat) : (List.replicate n 1).sum = n := by
        induction n with
        | zero => rfl
        | succ n ih => rw [List.replicate_succ, List.sum_cons, ih, Nat.add_comm]
      simp only [List.map_const, ones, Nat.mul_one] at bound
      exact Nat.le_trans bound (Nat.le_max_right _ _)

#verify_constructive recover_line bounded_unique binaryFold_exceptional_challenges

end Qsag.SuccinctWhirAgg
end
