module
public import Qsag.Coding.Cwyz26
public import Qsag.Math.Tactic.CommRing
public import Qsag.Tactic.AssuranceKit

public section
namespace Qsag
namespace ZkHem
open CommRingOps RoundPoly
variable {F : Type} [LawfulField F]

/-- `F`-linear functional on words (an evaluation claim `⟨·, t⟩`). -/
structure LinForm (ι F : Type) [LawfulField F] where
  app : (ι → F) → F
  lin : ∀ (a b : F) (u v : ι → F),
    app (fun i => add (mul a (u i)) (mul b (v i))) = add (mul a (app u)) (mul b (app v))

/-- Coefficients of `y + (X - x) q(X)`. -/
def unquot (x : F) : F → List F → List F
  | y, [] => [y]
  | y, q0 :: qs => sub y (mul x q0) :: unquot x q0 qs

theorem unquot_quotLinear (x : F) : ∀ (cs : List F), cs ≠ [] →
    unquot x (evalCoeffs cs x) (quotLinear cs x) = cs
  | [], h => absurd rfl h
  | [c0], _ => by
    show [add c0 (mul x zero)] = [c0]
    have e : add c0 (mul x zero) = c0 := by constructive_ring
    rw [e]
  | c0 :: c1 :: cs, _ => by
    show sub (add c0 (mul x (evalCoeffs (c1 :: cs) x))) (mul x (evalCoeffs (c1 :: cs) x)) ::
      unquot x (evalCoeffs (c1 :: cs) x) (quotLinear (c1 :: cs) x) = c0 :: c1 :: cs
    rw [unquot_quotLinear x (c1 :: cs) (List.cons_ne_nil _ _)]
    have e : sub (add c0 (mul x (evalCoeffs (c1 :: cs) x))) (mul x (evalCoeffs (c1 :: cs) x)) =
        c0 := by constructive_ring
    rw [e]

/-- Divided differences against the first point. -/
def divDiff (x y : F) : List F → List F → List F
  | xi :: xs, yi :: ys => mul (sub yi y) (LawfulField.inv (sub xi x)) :: divDiff x y xs ys
  | _, _ => []

/-- Newton interpolation: the coefficient list of length `|xs|` with values `ys` at `xs`. -/
def interp : List F → List F → List F
  | x :: xs, y :: ys => unquot x y (interp xs (divDiff x y xs ys))
  | _, _ => []

def evalAll (cs xs : List F) : List F := xs.map (evalCoeffs cs)

theorem divDiff_evalAll (x : F) (cs : List F) : ∀ (xs : List F), (∀ t ∈ xs, t ≠ x) →
    divDiff x (evalCoeffs cs x) xs (xs.map (evalCoeffs cs)) =
      xs.map (evalCoeffs (quotLinear cs x))
  | [], _ => rfl
  | t :: xs, hx => by
    have hne : sub t x ≠ zero := fun h0 =>
      hx t (List.mem_cons_self) (LawfulCommRing.sub_eq_zero_iff.mp h0)
    have hi := LawfulField.mul_inv_cancel hne
    show mul (sub (evalCoeffs cs t) (evalCoeffs cs x)) (LawfulField.inv (sub t x)) ::
      divDiff x (evalCoeffs cs x) xs (xs.map (evalCoeffs cs)) =
      evalCoeffs (quotLinear cs x) t :: xs.map (evalCoeffs (quotLinear cs x))
    rw [divDiff_evalAll x cs xs (fun t' ht' => hx t' (List.mem_cons_of_mem _ ht')),
      evalCoeffs_eq_mul_quotLinear_add cs x t]
    generalize LawfulField.inv (sub t x) = j at hi
    have e : mul (sub (add (mul (sub t x) (evalCoeffs (quotLinear cs x) t)) (evalCoeffs cs x))
        (evalCoeffs cs x)) j = mul (evalCoeffs (quotLinear cs x) t) (mul (sub t x) j) := by
      constructive_ring
    rw [e, hi, LawfulCommRing.mul_one]

theorem interp_evalAll : ∀ (xs cs : List F), xs.Nodup → cs.length = xs.length →
    interp xs (evalAll cs xs) = cs
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by cases h
  | x :: xs, cs, hnd, h => by
    obtain ⟨hx, hnd'⟩ := List.nodup_cons.mp hnd
    have hcs : cs ≠ [] := fun h0 => by
      rw [h0] at h
      cases h
    have hq : (quotLinear cs x).length = xs.length := by
      rw [quotLinear_length, h]
      rfl
    show unquot x (evalCoeffs cs x)
      (interp xs (divDiff x (evalCoeffs cs x) xs (xs.map (evalCoeffs cs)))) = cs
    rw [divDiff_evalAll x cs xs (fun t ht hEq => hx (hEq ▸ ht))]
    have ih := interp_evalAll xs (quotLinear cs x) hnd' hq
    have ih' : interp xs (xs.map (evalCoeffs (quotLinear cs x))) = quotLinear cs x := ih
    rw [ih', unquot_quotLinear x cs hcs]

def vadd : List F → List F → List F
  | a :: as, b :: bs => add a b :: vadd as bs
  | _, _ => []

def vsub : List F → List F → List F
  | a :: as, b :: bs => sub a b :: vsub as bs
  | _, _ => []

theorem vadd_length : ∀ (as bs : List F), as.length = bs.length → (vadd as bs).length = bs.length
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | _ :: as, _ :: bs, h => by
    show (vadd as bs).length + 1 = bs.length + 1
    rw [vadd_length as bs (Nat.succ.inj h)]

theorem vsub_length : ∀ (as bs : List F), as.length = bs.length → (vsub as bs).length = bs.length
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | _ :: as, _ :: bs, h => by
    show (vsub as bs).length + 1 = bs.length + 1
    rw [vsub_length as bs (Nat.succ.inj h)]

theorem vsub_vadd : ∀ (v e : List F), v.length = e.length → vsub (vadd v e) v = e
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | a :: v, b :: e, h => by
    show sub (add a b) a :: vsub (vadd v e) v = b :: e
    rw [vsub_vadd v e (Nat.succ.inj h)]
    have e1 : sub (add a b) a = b := by constructive_ring
    rw [e1]

theorem vadd_vsub : ∀ (v o : List F), v.length = o.length → vadd v (vsub o v) = o
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | a :: v, b :: o, h => by
    show add a (sub b a) :: vadd v (vsub o v) = b :: o
    rw [vadd_vsub v o (Nat.succ.inj h)]
    have e1 : add a (sub b a) = b := by constructive_ring
    rw [e1]

theorem evalCoeffs_replicate_zero : ∀ (m : Nat) (x : F),
    RoundPoly.evalCoeffs (List.replicate m zero) x = zero
  | 0, _ => rfl
  | m + 1, x => by
    show add zero (mul x (RoundPoly.evalCoeffs (List.replicate m zero) x)) = zero
    rw [evalCoeffs_replicate_zero m x]
    constructive_ring

/-- Any degree-`≤ d` polynomial with at least one nonzero coefficient has at most `d` roots in
    any duplicate-free challenge pool `S` (proved constructively via `interp_evalAll`). -/
theorem roots_le_of_exists_nonzero [DecidableEq F] (d : Nat) (cs : List F)
    (hlen : cs.length ≤ d + 1) (hnz : ∃ c ∈ cs, c ≠ zero)
    (S : List F) (hS : S.Nodup) :
    (S.filter (fun x => decide (RoundPoly.evalCoeffs cs x = zero))).length ≤ d := by
  let R := S.filter (fun x => decide (RoundPoly.evalCoeffs cs x = zero))
  cases Nat.lt_or_ge d R.length with
  | inr hle => exact hle
  | inl hgt =>
    exfalso
    have hRnd : R.Nodup := hS.filter _
    let xs := R.take cs.length
    have hxsSub : xs.Sublist R := List.take_sublist cs.length R
    have hxsNd : xs.Nodup := hxsSub.nodup hRnd
    have hcsLeR : cs.length ≤ R.length := Nat.le_trans hlen hgt
    have hxsLen : xs.length = cs.length := List.length_take_of_le hcsLeR
    have hAllZero : evalAll cs xs = evalAll (List.replicate cs.length zero) xs := by
      unfold evalAll
      apply List.map_congr_left
      intro x hx
      have hxR : x ∈ R := hxsSub.subset hx
      have hx0 : RoundPoly.evalCoeffs cs x = zero := of_decide_eq_true (List.mem_filter.mp hxR).2
      rw [hx0, evalCoeffs_replicate_zero]
    have hEqCs : cs = List.replicate cs.length zero := by
      rw [← interp_evalAll xs cs hxsNd hxsLen.symm, hAllZero,
        interp_evalAll xs (List.replicate cs.length zero) hxsNd
          (List.length_replicate.trans hxsLen.symm)]
      rw [List.length_replicate]
    obtain ⟨c, hcMem, hcNe⟩ := hnz
    rw [hEqCs] at hcMem
    exact hcNe (List.eq_of_mem_replicate hcMem)

#export_eqns evalAll vadd
end ZkHem
end Qsag
