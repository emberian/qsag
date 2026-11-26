module
public import Qsag.Coding.WelchBerlekampDecoder
public import Qsag.Protocol.Aggregation.ZkHemV2
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.WhirAssignmentRecovery

/-- Invert the multilinear Möbius transform at a Boolean vertex. Monomial j
    contributes exactly when every set bit of j is set in i. -/
def vertex (coeffs : List Goldilocks) (i : Nat) : Goldilocks :=
  coeffs.zipIdx.foldl (fun acc (c,j) => if j &&& i = j then acc.add c else acc) .zero

/-- Evaluation points and values in the same strided order as the stage-zero encoder. -/
def fiberSamples (height fold : Nat) (fibers : List (Nat × List Goldilocks)) :
    List (Goldilocks × Goldilocks) :=
  let omega := powMod 1753635133440165772 (2^(32 - (height + fold))) goldilocksPrime
  fibers.flatMap fun (i,vs) =>
    if i < 2^height ∧ vs.length = 2^fold then vs.zipIdx.map fun (v,j) =>
      (Goldilocks.ofNat (7 * powMod omega (i + j * 2^height) goldilocksPrime), v)
    else []

/-- Recover monomial coefficients from opened base-field fibers in the shifted
    NTT codeword. Repeated reads of a point count only once. -/
def decode (logCells height fold : Nat) (fibers : List (Nat × List Goldilocks)) :
    Option (List Goldilocks) :=
  let samples := fiberSamples height fold fibers
  if height + fold ≤ 32 ∧ logCells ≤ height + fold ∧
      (samples.all fun (x,y) => samples.lookup x == some y) then
    let dom := (samples.map Prod.fst).eraseDups
    WelchBerlekamp.wbDecode (2^logCells) 0 dom (fun x => (samples.lookup x).getD .zero)
  else none

/-- A successful recovery agrees at every sampled point and has at least the
    required number of distinct evaluations, regardless of repeated oracle reads. -/
theorem decode_sound {k h f : Nat} {fibers : List (Nat × List Goldilocks)} {cs : List Goldilocks}
    (success : decode k h f fibers = some cs) :
    let samples := fiberSamples h f fibers
    let dom := (samples.map Prod.fst).eraseDups
    IsTrimmed cs ∧ cs.length ≤ 2^k ∧ 2^k ≤ dom.length ∧
      ∀ x ∈ dom, RoundPoly.evalCoeffs cs x = (samples.lookup x).getD .zero := by
  intro samples dom
  unfold decode at success
  dsimp only at success
  split at success
  · have result := WelchBerlekamp.wbDecode_sound _ _ _ _ _ success
    obtain ⟨trim,degree,agree,enough⟩ := result
    refine ⟨trim,degree,by simpa only [Nat.mul_zero,Nat.add_zero] using enough,?_⟩
    let agrees := fun x => decide (RoundPoly.evalCoeffs cs x = (samples.lookup x).getD .zero)
    have count : dom.length ≤ (dom.filter agrees).length := by
      simpa only [WelchBerlekamp.agreeCount,Nat.add_zero] using agree
    have all := List.filter_eq_self.mp (List.Sublist.eq_of_length (List.filter_sublist (p := agrees))
      (Nat.le_antisymm (List.length_filter_le agrees dom) count))
    exact fun x hx => of_decide_eq_true (all x hx)
  · cases success

private theorem distinctDomain (xs : List Goldilocks) : xs.eraseDups.Nodup := by
  suffices loop : ∀ (ys acc : List Goldilocks), acc.Nodup →
      (List.eraseDupsBy.loop (fun a b => a == b) ys acc).Nodup from loop xs [] .nil
  intro ys
  induction ys with
  | nil =>
    intro acc nd
    rw [List.eraseDupsBy.loop.eq_1]
    exact List.pairwise_reverse.mpr (nd.imp (fun h => Ne.symm h))
  | cons a ys ih =>
    intro acc nd
    rw [List.eraseDupsBy.loop.eq_2]
    cases h : acc.any (fun b => a == b) with
    | true => exact ih acc nd
    | false =>
      apply ih
      apply List.nodup_cons.mpr
      refine ⟨fun hm => ?_,nd⟩
      have yes := List.any_eq_true.mpr ⟨a,hm,beq_self_eq_true a⟩
      exact Bool.noConfusion (h.symm.trans yes)

/-- Enough distinct, consistent openings of a codeword recover its unique
    trimmed coefficients. The prover need not disclose the coefficient vector. -/
theorem decode_complete (k h f : Nat) (fibers : List (Nat × List Goldilocks)) (cs : List Goldilocks)
    (geom : h + f ≤ 32 ∧ k ≤ h + f) (trim : IsTrimmed cs) (degree : cs.length ≤ 2^k) :
    let samples := fiberSamples h f fibers
    let dom := (samples.map Prod.fst).eraseDups
    (samples.all fun (x,y) => samples.lookup x == some y) = true →
    2^k ≤ dom.length →
    (∀ x ∈ dom, RoundPoly.evalCoeffs cs x = (samples.lookup x).getD .zero) →
    decode k h f fibers = some cs := by
  intro samples dom consistent enough values
  unfold decode
  dsimp only
  rw [ite_eq_left ⟨geom.1,geom.2,consistent⟩]
  apply WelchBerlekamp.wbDecode_complete _ _ _ _ (distinctDomain _) (by simpa using enough) cs trim degree
  change dom.length ≤ (dom.filter (fun x => decide
    (RoundPoly.evalCoeffs cs x = (samples.lookup x).getD .zero))).length + 0
  rw [List.filter_eq_self.mpr (fun x hx => decide_eq_true (values x hx)), Nat.add_zero]
  exact Nat.le_refl _

/-- A linear polynomial 1 + 2X on the coset {7,-7} decodes to the
    Boolean-cube assignment [1,3]. Repeating one opening cannot replace the second. -/
theorem two_point_recovery :
    let vs := [Goldilocks.ofNat 15, Goldilocks.ofNat (goldilocksPrime - 13)]
    ((decode 1 0 1 [(0,vs)]).map fun cs => [vertex cs 0,vertex cs 1]) =
      some [Goldilocks.one,Goldilocks.ofNat 3] := by
  let a := Goldilocks.ofNat 7
  let b := Goldilocks.ofNat (goldilocksPrime - 7)
  let samples := [(a,Goldilocks.ofNat 15),(b,Goldilocks.ofNat (goldilocksPrime - 13))]
  let cs := [Goldilocks.one,Goldilocks.ofNat 2]
  change (WelchBerlekamp.wbDecode 2 0 [a,b] (fun x => (samples.lookup x).getD .zero)).map _ = _
  rw [WelchBerlekamp.wbDecode_complete 2 0 [a,b] _ (by decide +kernel) (by decide) cs
    (by rfl) (by decide) (by decide +kernel)]
  decide +kernel

theorem tooth_repeated_opening_insufficient :
    decode 1 1 0 [(0,[Goldilocks.ofNat 15]), (0,[Goldilocks.ofNat 15])] = none := by
  change WelchBerlekamp.wbDecode 2 0 [Goldilocks.ofNat 7] _ = none
  apply WelchBerlekamp.wbDecode_none_of_short
  decide

#verify_constructive decode_sound decode_complete
#tooth_pair two_point_recovery vs tooth_repeated_opening_insufficient
end Qsag.WhirAssignmentRecovery
