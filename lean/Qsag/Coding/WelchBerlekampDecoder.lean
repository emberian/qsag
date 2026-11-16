module
public import Qsag.Coding.ReedSolomon
import Qsag.Tactic.AssuranceKit

/-!
# Qsag.Coding.WelchBerlekampDecoder

A deterministic Reed–Solomon unique decoder with a counted number of field operations.

`Qsag.gsDecodeList` (`Qsag.Coding.ReedSolomon`) is the specification decoder: it interpolates
through every `(d + 1)`-subset of the domain, which is `choose n (d + 1)` interpolations. This
module gives the algorithm that a verifier or extractor can actually run.

## Algorithm (`wbDecodeT`, value `wbDecode`)

Input: dimension `k` (codewords are coefficient lists of length at most `k`), error budget `e`,
a domain `x₁ … xₙ` and a received word `word : F → F`.

1. Reject when `n < k + 2 * e` (the parameters are outside the unique-decoding radius).
2. On the first `k + 2 * e` domain points build the Welch–Berlekamp key equations
   `N(xᵢ) = word(xᵢ) · E(xᵢ)` in the `k + 2 * e + 1` unknown coefficients of `N` (`k + e`
   coefficients) and `E` (`e + 1` coefficients).
3. `solveT`: Gaussian elimination returns a nonzero solution `(N, E)`; one always exists
   because there are fewer equations than unknowns. `E` is not normalised to be monic: any
   nonzero solution has `N = E · P` for the codeword `P`.
4. `divT`: divide `N` by `E` (trailing zero coefficients removed), keep the quotient `Q`.
5. Accept `Q` when it has at most `k` coefficients and agrees with `word` on at least `n - e`
   points of the whole domain.

Step 2 uses a `k + 2 * e`-point subdomain, the least number of points for which the key
equations determine the codeword; step 5 re-checks the candidate on the whole domain, so
soundness never depends on the linear algebra.

## Operation count

`Tick α` is a value with a counter. The decoder is written in the `Tick` monad and touches the
field only through `tAdd`, `tMul`, `tSub`, `tNeg`, `tInv`, `tIsZero` and `tEq`, each of which
costs one. Reading `word` at a point and copying coefficients are free. `wbDecode_ops_poly`
bounds the counter by `2 * (n + 2) ^ 3 + 5 * (n + 2) ^ 2` for every field and every input.
The count is of field operations: the bit cost of one operation depends on the field.

## Radius

`wbDecode_complete` needs `k + 2 * e ≤ n`, the unique-decoding radius `(1 - ρ) / 2` at rate
`ρ = k / n`. Up to that radius `wbDecode` equals the specification decoder
(`wbDecode_eq_unique`). It is not a list decoder: between the unique-decoding radius and the
Johnson radius `1 - √ρ` the specification list can hold several codewords
(`Qsag.gsDecodeList_length_le_johnson` bounds how many), and computing that list in polynomial
time needs Guruswami–Sudan interpolation followed by root finding of a bivariate polynomial
(Roth–Ruckenstein), whose univariate root-finding step over a field of size about `2 ^ 256` is
randomised. Nothing here covers that range.
-/

public section
namespace Qsag
namespace WelchBerlekamp
set_option autoImplicit false
open CommRingOps RoundPoly

/-! ## 1. Operation counting -/

/-- A value together with the number of field operations spent on it. -/
structure Tick (α : Type) where
  val : α
  cost : Nat

namespace Tick
variable {α β : Type}

protected def pure (a : α) : Tick α := ⟨a, 0⟩

protected def bind (m : Tick α) (f : α → Tick β) : Tick β :=
  ⟨(f m.val).val, m.cost + (f m.val).cost⟩

instance : Monad Tick where
  pure := Tick.pure
  bind := Tick.bind

@[simp] theorem val_pure (a : α) : (pure a : Tick α).val = a := by rfl
@[simp] theorem cost_pure (a : α) : (pure a : Tick α).cost = 0 := by rfl
@[simp] theorem val_bind (m : Tick α) (f : α → Tick β) :
    (m >>= f).val = (f m.val).val := by rfl
@[simp] theorem cost_bind (m : Tick α) (f : α → Tick β) :
    (m >>= f).cost = m.cost + (f m.val).cost := by rfl

end Tick

variable {F : Type}

/-- One field addition. -/
def tAdd [CommRingOps F] (a b : F) : Tick F := ⟨add a b, 1⟩
/-- One field multiplication. -/
def tMul [CommRingOps F] (a b : F) : Tick F := ⟨mul a b, 1⟩
/-- One field subtraction. -/
def tSub [CommRingOps F] (a b : F) : Tick F := ⟨sub a b, 1⟩
/-- One field negation. -/
def tNeg [CommRingOps F] (a : F) : Tick F := ⟨neg a, 1⟩
/-- One field inversion. -/
def tInv [LawfulField F] (a : F) : Tick F := ⟨LawfulField.inv a, 1⟩
/-- One comparison with zero. -/
def tIsZero [CommRingOps F] [DecidableEq F] (a : F) : Tick Bool := ⟨decide (a = zero), 1⟩
/-- One comparison of two field elements. -/
def tEq [DecidableEq F] (a b : F) : Tick Bool := ⟨decide (a = b), 1⟩

@[simp] theorem val_tAdd [CommRingOps F] (a b : F) : (tAdd a b).val = add a b := by rfl
@[simp] theorem cost_tAdd [CommRingOps F] (a b : F) : (tAdd a b).cost = 1 := by rfl
@[simp] theorem val_tMul [CommRingOps F] (a b : F) : (tMul a b).val = mul a b := by rfl
@[simp] theorem cost_tMul [CommRingOps F] (a b : F) : (tMul a b).cost = 1 := by rfl
@[simp] theorem val_tSub [CommRingOps F] (a b : F) : (tSub a b).val = sub a b := by rfl
@[simp] theorem cost_tSub [CommRingOps F] (a b : F) : (tSub a b).cost = 1 := by rfl
@[simp] theorem val_tNeg [CommRingOps F] (a : F) : (tNeg a).val = neg a := by rfl
@[simp] theorem cost_tNeg [CommRingOps F] (a : F) : (tNeg a).cost = 1 := by rfl
@[simp] theorem val_tInv [LawfulField F] (a : F) : (tInv a).val = LawfulField.inv a := by rfl
@[simp] theorem cost_tInv [LawfulField F] (a : F) : (tInv a).cost = 1 := by rfl
@[simp] theorem val_tIsZero [CommRingOps F] [DecidableEq F] (a : F) :
    (tIsZero a).val = decide (a = zero) := by rfl
@[simp] theorem cost_tIsZero [CommRingOps F] [DecidableEq F] (a : F) :
    (tIsZero a).cost = 1 := by rfl
@[simp] theorem val_tEq [DecidableEq F] (a b : F) : (tEq a b).val = decide (a = b) := by rfl
@[simp] theorem cost_tEq [DecidableEq F] (a b : F) : (tEq a b).cost = 1 := by rfl

/-- Counted `List.map`. -/
def mapT {α β : Type} (f : α → Tick β) : List α → Tick (List β)
  | [] => pure []
  | x :: xs => do
    let y ← f x
    let ys ← mapT f xs
    pure (y :: ys)

theorem val_mapT {α β : Type} (f : α → Tick β) :
    ∀ l : List α, (mapT f l).val = l.map (fun x => (f x).val)
  | [] => by rfl
  | x :: xs => by
    simp only [mapT, Tick.val_bind, Tick.val_pure, List.map_cons, val_mapT f xs]

theorem cost_mapT_le {α β : Type} (f : α → Tick β) (c : Nat) :
    ∀ l : List α, (∀ x ∈ l, (f x).cost ≤ c) → (mapT f l).cost ≤ l.length * c
  | [], _ => by simp only [mapT, Tick.cost_pure, List.length_nil, Nat.zero_mul, Nat.le_refl]
  | x :: xs, h => by
    have hx := h x (.head _)
    have ih := cost_mapT_le f c xs (fun y hy => h y (.tail _ hy))
    simp only [mapT, Tick.cost_bind, Tick.cost_pure, List.length_cons, Nat.succ_mul]
    omega

/-! ## 2. Vectors: dot product and row elimination -/

/-- Counted dot product. -/
def dotT [CommRingOps F] : List F → List F → Tick F
  | [], _ => pure zero
  | _ :: _, [] => pure zero
  | a :: as, b :: bs => do
    let p ← tMul a b
    let r ← dotT as bs
    tAdd p r

theorem val_dotT [CommRingOps F] : ∀ a b : List F, (dotT a b).val = dotVec a b
  | [], _ => by simp only [dotT, Tick.val_pure, dotVec_nil_left]
  | _ :: _, [] => by simp only [dotT, Tick.val_pure, dotVec_nil_right]
  | a :: as, b :: bs => by
    simp only [dotT, Tick.val_bind, val_tMul, val_tAdd, dotVec_cons, val_dotT as bs]

theorem cost_dotT_le [CommRingOps F] : ∀ a b : List F, (dotT a b).cost ≤ 2 * b.length
  | [], _ => by simp only [dotT, Tick.cost_pure, Nat.zero_le]
  | _ :: _, [] => by simp only [dotT, Tick.cost_pure, Nat.zero_le]
  | a :: as, b :: bs => by
    have ih := cost_dotT_le as bs
    simp only [dotT, Tick.cost_bind, cost_tMul, cost_tAdd, List.length_cons]
    omega

/-- `axpy c s b` is the vector `s - c · b`, truncated to the shorter argument. -/
def axpy [CommRingOps F] (c : F) : List F → List F → List F
  | s :: ss, b :: bs => sub s (mul c b) :: axpy c ss bs
  | [], _ => []
  | _ :: _, [] => []

/-- Counted `axpy`: one multiplication and one subtraction per coordinate. -/
def axpyT [CommRingOps F] (c : F) : List F → List F → Tick (List F)
  | s :: ss, b :: bs => do
    let p ← tMul c b
    let d ← tSub s p
    let rest ← axpyT c ss bs
    pure (d :: rest)
  | [], _ => pure []
  | _ :: _, [] => pure []

theorem val_axpyT [CommRingOps F] (c : F) : ∀ s b : List F, (axpyT c s b).val = axpy c s b
  | s :: ss, b :: bs => by
    simp only [axpyT, axpy, Tick.val_bind, Tick.val_pure, val_tMul, val_tSub, val_axpyT c ss bs]
  | [], _ => by simp only [axpyT, axpy, Tick.val_pure]
  | _ :: _, [] => by simp only [axpyT, axpy, Tick.val_pure]

theorem cost_axpyT_le [CommRingOps F] (c : F) :
    ∀ s b : List F, (axpyT c s b).cost ≤ 2 * s.length
  | s :: ss, b :: bs => by
    have ih := cost_axpyT_le c ss bs
    simp only [axpyT, Tick.cost_bind, Tick.cost_pure, cost_tMul, cost_tSub, List.length_cons]
    omega
  | [], _ => by simp only [axpyT, Tick.cost_pure, Nat.zero_le]
  | _ :: _, [] => by simp only [axpyT, Tick.cost_pure, Nat.zero_le]

theorem axpy_length_le [CommRingOps F] (c : F) :
    ∀ s b : List F, (axpy c s b).length ≤ s.length
  | s :: ss, b :: bs => by
    have ih := axpy_length_le c ss bs
    simp only [axpy, List.length_cons]
    omega
  | [], _ => by simp only [axpy, List.length_nil, Nat.le_refl]
  | _ :: _, [] => by simp only [axpy, List.length_nil, Nat.zero_le]

theorem axpy_length [CommRingOps F] (c : F) :
    ∀ s b : List F, s.length = b.length → (axpy c s b).length = s.length
  | s :: ss, b :: bs, h => by
    have ih := axpy_length c ss bs (by simp only [List.length_cons] at h; omega)
    simp only [axpy, List.length_cons, ih]
  | [], _, _ => by simp only [axpy, List.length_nil]
  | _ :: _, [], h => by simp only [List.length_cons, List.length_nil] at h; exfalso; omega

theorem coeffAt_axpy [LawfulCommRing F] (c : F) :
    ∀ (s b : List F) (j : Nat), s.length = b.length →
      coeffAt (axpy c s b) j = sub (coeffAt s j) (mul c (coeffAt b j))
  | [], [], j, _ => by
    simp only [axpy, coeffAt_nil, LawfulCommRing.mul_zero, LawfulCommRing.sub_self]
  | [], _ :: _, _, h => by simp only [List.length_cons, List.length_nil] at h; exfalso; omega
  | _ :: _, [], _, h => by simp only [List.length_cons, List.length_nil] at h; exfalso; omega
  | s :: ss, b :: bs, 0, _ => by simp only [axpy, coeffAt_cons_zero]
  | s :: ss, b :: bs, j + 1, h => by
    simp only [axpy, coeffAt_cons_succ]
    exact coeffAt_axpy c ss bs j (by simp only [List.length_cons] at h; omega)

theorem dotVec_axpy [LawfulCommRing F] (c : F) :
    ∀ s b v : List F, s.length = b.length →
      dotVec (axpy c s b) v = sub (dotVec s v) (mul c (dotVec b v))
  | [], [], v, _ => by
    simp only [axpy, dotVec_nil_left, LawfulCommRing.mul_zero, LawfulCommRing.sub_self]
  | [], _ :: _, _, h => by simp only [List.length_cons, List.length_nil] at h; exfalso; omega
  | _ :: _, [], _, h => by simp only [List.length_cons, List.length_nil] at h; exfalso; omega
  | s :: ss, b :: bs, [], _ => by
    simp only [dotVec_nil_right, LawfulCommRing.mul_zero, LawfulCommRing.sub_self]
  | s :: ss, b :: bs, x :: xs, h => by
    have ih := dotVec_axpy c ss bs xs (by simp only [List.length_cons] at h; omega)
    simp only [axpy, dotVec_cons, ih]
    constructive_ring

theorem dotVec_replicate_zero_right [LawfulCommRing F] :
    ∀ (t : List F) (n : Nat), dotVec t (List.replicate n zero) = zero
  | [], _ => by simp only [dotVec_nil_left]
  | _ :: _, 0 => by simp only [List.replicate_zero, dotVec_nil_right]
  | a :: as, n + 1 => by
    simp only [List.replicate_succ, dotVec_cons, dotVec_replicate_zero_right as n,
      LawfulCommRing.mul_zero, LawfulCommRing.add_zero]

/-- Eliminate the leading coordinate of `row` against a pivot row with tail `rt` and inverse
    pivot `ai`: the result is `tail row - (head row · ai) · rt`. -/
def elimRow [CommRingOps F] (ai : F) (rt : List F) : List F → List F
  | [] => []
  | b :: bt => axpy (mul b ai) bt rt

/-- Counted `elimRow`. -/
def elimRowT [CommRingOps F] (ai : F) (rt : List F) : List F → Tick (List F)
  | [] => pure []
  | b :: bt => do
    let c ← tMul b ai
    axpyT c bt rt

theorem val_elimRowT [CommRingOps F] (ai : F) (rt : List F) :
    ∀ row : List F, (elimRowT ai rt row).val = elimRow ai rt row
  | [] => by rfl
  | b :: bt => by simp only [elimRowT, elimRow, Tick.val_bind, val_tMul, val_axpyT]

theorem cost_elimRowT_le [CommRingOps F] (ai : F) (rt : List F) :
    ∀ row : List F, (elimRowT ai rt row).cost + 1 ≤ 2 * row.length ∨ row = []
  | [] => .inr rfl
  | b :: bt => by
    have h := cost_axpyT_le (mul b ai) bt rt
    left
    simp only [elimRowT, Tick.cost_bind, cost_tMul, val_tMul, List.length_cons]
    omega

/-! ## 3. Gaussian elimination: a nonzero solution of an underdetermined homogeneous system -/

/-- Find a row whose leading coordinate is nonzero and take it out of the list. -/
def extractPivot [CommRingOps F] [DecidableEq F] :
    List (List F) → Option (List F × List (List F))
  | [] => none
  | row :: rest =>
    if row.headD zero = zero then
      match extractPivot rest with
      | none => none
      | some (p, others) => some (p, row :: others)
    else some (row, rest)

/-- Counted `extractPivot`: one zero test per inspected row. -/
def extractPivotT [CommRingOps F] [DecidableEq F] :
    List (List F) → Tick (Option (List F × List (List F)))
  | [] => pure none
  | row :: rest => do
    let z ← tIsZero (row.headD zero)
    if z then do
      let r ← extractPivotT rest
      match r with
      | none => pure none
      | some (p, others) => pure (some (p, row :: others))
    else pure (some (row, rest))

theorem val_extractPivotT [CommRingOps F] [DecidableEq F] :
    ∀ rows : List (List F), (extractPivotT rows).val = extractPivot rows
  | [] => by rfl
  | row :: rest => by
    have ih := val_extractPivotT rest
    simp only [extractPivotT, extractPivot, Tick.val_bind, val_tIsZero]
    if h : row.headD zero = zero then
      simp only [h, decide_true, ↓reduceIte, Tick.val_bind, ih]
      cases extractPivot rest with
      | none => rfl
      | some po => rfl
    else
      simp only [h, decide_false, ↓reduceIte, Tick.val_pure, Bool.false_eq_true]

theorem cost_extractPivotT_le [CommRingOps F] [DecidableEq F] :
    ∀ rows : List (List F), (extractPivotT rows).cost ≤ rows.length
  | [] => by simp only [extractPivotT, Tick.cost_pure]; exact Nat.zero_le _
  | row :: rest => by
    have ih := cost_extractPivotT_le rest
    simp only [extractPivotT, Tick.cost_bind, cost_tIsZero, val_tIsZero, List.length_cons]
    if h : row.headD zero = zero then
      simp only [h, decide_true, ↓reduceIte, Tick.cost_bind]
      cases (extractPivotT rest).val with
      | none => simp only [Tick.cost_pure]; omega
      | some po => simp only [Tick.cost_pure]; omega
    else
      simp only [h, decide_false, ↓reduceIte, Tick.cost_pure, Bool.false_eq_true]
      omega

theorem extractPivot_none [CommRingOps F] [DecidableEq F] :
    ∀ rows : List (List F), extractPivot rows = none →
      ∀ row ∈ rows, row.headD zero = zero
  | [], _, _, hm => nomatch hm
  | r :: rest, h, row, hm => by
    simp only [extractPivot] at h
    if hz : r.headD zero = zero then
      rw [ite_eq_left hz] at h
      cases hrest : extractPivot rest with
      | some po => rw [hrest] at h; exact nomatch h
      | none =>
        cases hm with
        | head => exact hz
        | tail _ hm' => exact extractPivot_none rest hrest row hm'
    else
      rw [ite_eq_right hz] at h
      exact nomatch h

theorem extractPivot_some [CommRingOps F] [DecidableEq F] :
    ∀ (rows : List (List F)) (p : List F) (others : List (List F)),
      extractPivot rows = some (p, others) →
      p.headD zero ≠ zero ∧ p ∈ rows ∧ (∀ row ∈ others, row ∈ rows) ∧
      others.length + 1 = rows.length ∧ (∀ row ∈ rows, row = p ∨ row ∈ others)
  | [], _, _, h => nomatch h
  | r :: rest, p, others, h => by
    simp only [extractPivot] at h
    if hz : r.headD zero = zero then
      rw [ite_eq_left hz] at h
      cases hrest : extractPivot rest with
      | none => rw [hrest] at h; exact nomatch h
      | some po =>
        obtain ⟨p', others'⟩ := po
        rw [hrest] at h
        have hinj := Option.some.inj h
        have hp : p' = p := congrArg Prod.fst hinj
        have ho : r :: others' = others := congrArg Prod.snd hinj
        subst hp; subst ho
        obtain ⟨h1, h2, h3, h4, h5⟩ := extractPivot_some rest p' others' hrest
        refine ⟨h1, .tail _ h2, ?_, by simp only [List.length_cons]; omega, ?_⟩
        · intro row hm
          cases hm with
          | head => exact .head _
          | tail _ hm' => exact .tail _ (h3 row hm')
        · intro row hm
          cases hm with
          | head => exact .inr (.head _)
          | tail _ hm' =>
            rcases h5 row hm' with he | hin
            · exact .inl he
            · exact .inr (.tail _ hin)
    else
      rw [ite_eq_right hz] at h
      have hinj := Option.some.inj h
      have hp : r = p := congrArg Prod.fst hinj
      have ho : rest = others := congrArg Prod.snd hinj
      subst hp; subst ho
      refine ⟨hz, .head _, fun row hm => .tail _ hm, rfl, ?_⟩
      intro row hm
      cases hm with
      | head => exact .inl rfl
      | tail _ hm' => exact .inr hm'

/-- Gaussian elimination on the leading variable. With `N` unknowns and fewer than `N` rows of
    length `N` the result is a nonzero vector orthogonal to every row (`solve_spec`).

    If no row has a nonzero leading coordinate, the first unit vector is a solution. Otherwise
    a pivot row is removed, its leading variable is eliminated from the other rows, the smaller
    system is solved and the leading variable is recovered by back substitution. -/
def solve [LawfulField F] [DecidableEq F] : Nat → List (List F) → List F
  | 0, _ => []
  | n + 1, rows =>
    match extractPivot rows with
    | none => one :: List.replicate n zero
    | some (p, others) =>
      let ai := LawfulField.inv (p.headD zero)
      let v := solve n (others.map (elimRow ai p.tail))
      neg (mul ai (dotVec p.tail v)) :: v

/-- Counted `solve`. -/
def solveT [LawfulField F] [DecidableEq F] : Nat → List (List F) → Tick (List F)
  | 0, _ => pure []
  | n + 1, rows => do
    let piv ← extractPivotT rows
    match piv with
    | none => pure (one :: List.replicate n zero)
    | some (p, others) => do
      let ai ← tInv (p.headD zero)
      let others' ← mapT (elimRowT ai p.tail) others
      let v ← solveT n others'
      let d ← dotT p.tail v
      let t ← tMul ai d
      let x0 ← tNeg t
      pure (x0 :: v)

theorem val_solveT [LawfulField F] [DecidableEq F] :
    ∀ (n : Nat) (rows : List (List F)), (solveT n rows).val = solve n rows
  | 0, _ => by rfl
  | n + 1, rows => by
    simp only [solveT, solve, Tick.val_bind, val_extractPivotT]
    cases extractPivot rows with
    | none => rfl
    | some po =>
      obtain ⟨p, others⟩ := po
      have hmap : (mapT (elimRowT (LawfulField.inv (p.headD zero)) p.tail) others).val =
          others.map (elimRow (LawfulField.inv (p.headD zero)) p.tail) := by
        rw [val_mapT]
        exact List.map_congr_left (fun row _ => val_elimRowT _ _ row)
      simp only [Tick.val_bind, Tick.val_pure, val_tInv, val_tMul, val_tNeg, val_dotT, hmap,
        val_solveT n]

theorem solve_length [LawfulField F] [DecidableEq F] :
    ∀ (n : Nat) (rows : List (List F)), (solve n rows).length = n
  | 0, _ => by rfl
  | n + 1, rows => by
    simp only [solve]
    cases extractPivot rows with
    | none => simp only [List.length_cons, List.length_replicate]
    | some po => simp only [List.length_cons, solve_length n]

/-- **Gaussian elimination is correct.** For `N` unknowns and fewer than `N` equations of
    length `N`, `solve N rows` has length `N`, has a nonzero coordinate and is orthogonal to
    every row. -/
theorem solve_spec [LawfulField F] [DecidableEq F] :
    ∀ (N : Nat) (rows : List (List F)), rows.length < N →
      (∀ row ∈ rows, row.length = N) →
      (∃ x ∈ solve N rows, x ≠ zero) ∧ ∀ row ∈ rows, dotVec row (solve N rows) = zero
  | 0, _, hlt, _ => nomatch hlt
  | n + 1, rows, hlt, hlen => by
    simp only [solve]
    cases hpiv : extractPivot rows with
    | none =>
      refine ⟨⟨one, .head _, LawfulField.one_ne_zero⟩, ?_⟩
      intro row hm
      have hz := extractPivot_none rows hpiv row hm
      have hl := hlen row hm
      cases row with
      | nil => simp only [dotVec_nil_left]
      | cons h t =>
        have hh : h = zero := hz
        simp only [dotVec_cons, hh, LawfulCommRing.zero_mul, LawfulCommRing.zero_add,
          dotVec_replicate_zero_right]
    | some po =>
      obtain ⟨p, others⟩ := po
      obtain ⟨hpz, hpm, hsub, hcnt, hcover⟩ := extractPivot_some rows p others hpiv
      have hpl := hlen p hpm
      cases p with
      | nil => simp only [List.length_nil] at hpl; exfalso; omega
      | cons a rt =>
        have ha : a ≠ zero := hpz
        have hrt : rt.length = n := by simp only [List.length_cons] at hpl; omega
        have hinv : mul a (LawfulField.inv a) = one := LawfulField.mul_inv_cancel ha
        simp only [List.headD_cons, List.tail_cons]
        generalize hai : LawfulField.inv a = ai at hinv
        have hrows' : ∀ row' ∈ others.map (elimRow ai rt), row'.length = n := by
          intro row' hm'
          obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hm'
          have hl := hlen row (hsub row hrow)
          cases row with
          | nil => simp only [List.length_nil] at hl; exfalso; omega
          | cons b bt =>
            simp only [List.length_cons] at hl
            simp only [elimRow]
            rw [axpy_length _ bt rt (by omega)]
            omega
        have hlt' : (others.map (elimRow ai rt)).length < n := by
          rw [List.length_map]; omega
        obtain ⟨⟨x, hx, hxne⟩, hdot⟩ := solve_spec n _ hlt' hrows'
        generalize solve n (others.map (elimRow ai rt)) = v at hx hdot
        refine ⟨⟨x, .tail _ hx, hxne⟩, ?_⟩
        intro row hm
        rcases hcover row hm with he | hin
        · subst he
          simp only [dotVec_cons]
          have e : add (mul a (neg (mul ai (dotVec rt v)))) (dotVec rt v) =
              add (neg (mul (mul a ai) (dotVec rt v))) (dotVec rt v) := by constructive_ring
          rw [e, hinv, LawfulCommRing.one_mul, LawfulCommRing.add_left_neg]
        · have hl := hlen row (hsub row hin)
          have h0 := hdot _ (List.mem_map.mpr ⟨row, hin, rfl⟩)
          cases row with
          | nil => simp only [dotVec_nil_left]
          | cons b bt =>
            simp only [List.length_cons] at hl
            simp only [elimRow] at h0
            rw [dotVec_axpy _ bt rt v (by omega)] at h0
            have hbt := LawfulCommRing.sub_eq_zero_iff.mp h0
            simp only [dotVec_cons, hbt]
            constructive_ring

/-- Operation count of Gaussian elimination: at most `N` levels, each costing at most
    `R * (2 * W + 2) + 2 * W + 3` for `R` rows of width at most `W + 1`. -/
theorem cost_solveT_le [LawfulField F] [DecidableEq F] (R W : Nat) :
    ∀ (N : Nat) (rows : List (List F)), N ≤ W + 1 → rows.length ≤ R →
      (∀ row ∈ rows, row.length ≤ N) →
      (solveT N rows).cost ≤ N * (R * (2 * W + 2) + 2 * W + 3)
  | 0, _, _, _, _ => by simp only [solveT, Tick.cost_pure, Nat.zero_mul, Nat.le_refl]
  | n + 1, rows, hN, hR, hlen => by
    have hce := cost_extractPivotT_le rows
    have hL : (n + 1) * (R * (2 * W + 2) + 2 * W + 3) =
        n * (R * (2 * W + 2) + 2 * W + 3) + (R * (2 * W + 2) + 2 * W + 3) := Nat.succ_mul _ _
    have hsplit : R * (2 * W + 2) = R * (2 * W + 1) + R := Nat.mul_succ R (2 * W + 1)
    rw [hL]
    simp only [solveT, Tick.cost_bind, val_extractPivotT]
    cases hpiv : extractPivot rows with
    | none =>
      simp only [Tick.cost_pure]
      omega
    | some po =>
      obtain ⟨p, others⟩ := po
      obtain ⟨_, hpm, hsub, hcnt, _⟩ := extractPivot_some rows p others hpiv
      have hmapv : (mapT (elimRowT (LawfulField.inv (p.headD zero)) p.tail) others).val =
          others.map (elimRow (LawfulField.inv (p.headD zero)) p.tail) := by
        rw [val_mapT]
        exact List.map_congr_left (fun row _ => val_elimRowT _ _ row)
      have hcm : (mapT (elimRowT (LawfulField.inv (p.headD zero)) p.tail) others).cost ≤
          others.length * (2 * n + 1) := by
        apply cost_mapT_le
        intro row hrow
        have hl := hlen row (hsub row hrow)
        rcases cost_elimRowT_le (LawfulField.inv (p.headD zero)) p.tail row with h | h
        · omega
        · subst h; simp only [elimRowT, Tick.cost_pure, Nat.zero_le]
      have hrows' : ∀ row' ∈ others.map (elimRow (LawfulField.inv (p.headD zero)) p.tail),
          row'.length ≤ n := by
        intro row' hm'
        obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hm'
        have hl := hlen row (hsub row hrow)
        cases row with
        | nil => simp only [elimRow, List.length_nil, Nat.zero_le]
        | cons b bt =>
          simp only [List.length_cons] at hl
          have := axpy_length_le (mul b (LawfulField.inv (p.headD zero))) bt p.tail
          simp only [elimRow]
          omega
      have ih := cost_solveT_le R W n
        (others.map (elimRow (LawfulField.inv (p.headD zero)) p.tail)) (by omega)
        (by rw [List.length_map]; omega) hrows'
      have hcd := cost_dotT_le p.tail
        (solve n (others.map (elimRow (LawfulField.inv (p.headD zero)) p.tail)))
      rw [solve_length] at hcd
      have hX : others.length * (2 * n + 1) ≤ R * (2 * W + 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      simp only [Tick.cost_bind, Tick.cost_pure, val_tInv, cost_tInv, cost_tMul, cost_tNeg,
        val_tMul, val_dotT, hmapv, val_solveT]
      omega

/-! ### Public affine systems

An augmented row `[a₀, …, aₙ₋₁, -b]` encodes `a · w = b`. `solveAffine` returns a
canonical solution of every consistent system. Its runtime inputs are the public augmented
rows and the number of variables; an existential consistency witness is used only in the
correctness proof. Redundant equations and free columns are supported. The counted version
has a polynomial bound in the public matrix dimensions.
-/

/-- Deterministic elimination of an augmented homogeneous system with its final coordinate
fixed to one. The algorithm reads only the public rows; consistency is a proof premise. -/
def solveAffine [LawfulField F] [DecidableEq F] : Nat → List (List F) → List F
  | 0, _ => []
  | n + 1, rows =>
    match extractPivot rows with
    | none => zero :: solveAffine n (rows.map List.tail)
    | some (p, others) =>
      let ai := LawfulField.inv (p.headD zero)
      let v := solveAffine n (others.map (elimRow ai p.tail))
      neg (mul ai (dotVec p.tail (v ++ [one]))) :: v

theorem solveAffine_length [LawfulField F] [DecidableEq F] :
    ∀ n (rows : List (List F)), (solveAffine n rows).length = n
  | 0, _ => rfl
  | n + 1, rows => by
    simp only [solveAffine]
    cases extractPivot rows with
    | none => simp only [List.length_cons, solveAffine_length]
    | some po => simp only [List.length_cons, solveAffine_length]

/-- The proof-only consistency witness is never inspected by `solveAffine`. -/
def AffineConsistent [CommRingOps F] (n : Nat) (rows : List (List F)) : Prop :=
  ∃ w : List F, w.length = n ∧ ∀ row ∈ rows, dotVec row (w ++ [one]) = zero

theorem affineConsistent_iff [CommRingOps F] (n : Nat) (rows : List (List F)) :
    AffineConsistent n rows ↔
      ∃ w : List F, w.length = n ∧ ∀ row ∈ rows, dotVec row (w ++ [one]) = zero := by
  unfold AffineConsistent
  rfl

private theorem tail_dot_of_augmented_zero [LawfulCommRing F] (a h : F) (rt wt : List F)
    (hz : dotVec (a :: rt) ((h :: wt) ++ [one]) = zero) :
    dotVec rt (wt ++ [one]) = neg (mul a h) := by
  simp only [List.cons_append, dotVec_cons] at hz
  calc
    dotVec rt (wt ++ [one]) = add (neg (mul a h))
        (add (mul a h) (dotVec rt (wt ++ [one]))) := by constructive_ring
    _ = neg (mul a h) := by rw [hz, LawfulCommRing.add_zero]

/-- Completeness for every consistent augmented system, including redundant rows. -/
theorem solveAffine_spec [LawfulField F] [DecidableEq F] :
    ∀ n (rows : List (List F)),
      (∀ row ∈ rows, row.length = n + 1) → AffineConsistent n rows →
      ∀ row ∈ rows, dotVec row (solveAffine n rows ++ [one]) = zero
  | 0, rows, _, hc => by
    obtain ⟨w, hw, hd⟩ := hc
    have he : w = [] := List.eq_nil_of_length_eq_zero hw
    subst w
    exact hd
  | n + 1, rows, hlen, hc => by
    obtain ⟨w, hw, hd⟩ := hc
    cases w with
    | nil => simp only [List.length_nil] at hw; omega
    | cons h wt =>
      have hwt : wt.length = n := by simp only [List.length_cons] at hw; omega
      simp only [solveAffine]
      cases hpiv : extractPivot rows with
      | none =>
        have hlen' : ∀ r ∈ rows.map List.tail, r.length = n + 1 := by
          intro r hr
          obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr
          rw [List.length_tail, hlen r0 hr0]
          omega
        have hc' : AffineConsistent n (rows.map List.tail) := by
          refine ⟨wt, hwt, ?_⟩
          intro r hr
          obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr
          have hz := extractPivot_none rows hpiv r0 hr0
          have he := hd r0 hr0
          cases r0 with
          | nil => exact dotVec_nil_left _
          | cons a rt =>
            have ha : a = zero := hz
            simpa only [List.tail_cons, List.cons_append, dotVec_cons, ha,
              LawfulCommRing.zero_mul, LawfulCommRing.zero_add] using he
        have ih := solveAffine_spec n (rows.map List.tail) hlen' hc'
        intro r hr
        have hz := extractPivot_none rows hpiv r hr
        have he := ih r.tail (List.mem_map.mpr ⟨r, hr, rfl⟩)
        cases r with
        | nil => exact dotVec_nil_left _
        | cons a rt =>
          have ha : a = zero := hz
          simpa only [List.cons_append, dotVec_cons, ha, List.tail_cons,
            LawfulCommRing.zero_mul, LawfulCommRing.zero_add] using he
      | some po =>
        obtain ⟨p, others⟩ := po
        obtain ⟨hpz, hpm, hsub, _, hcover⟩ := extractPivot_some rows p others hpiv
        have hpl := hlen p hpm
        cases p with
        | nil => simp only [List.length_nil] at hpl; omega
        | cons a rt =>
          have ha : a ≠ zero := hpz
          have hrt : rt.length = n + 1 := by simp only [List.length_cons] at hpl; omega
          have hinv : mul a (LawfulField.inv a) = one := LawfulField.mul_inv_cancel ha
          simp only [List.headD_cons, List.tail_cons]
          generalize hai : LawfulField.inv a = ai at hinv
          have hlen' : ∀ r ∈ others.map (elimRow ai rt), r.length = n + 1 := by
            intro r hr
            obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr
            have hl := hlen r0 (hsub r0 hr0)
            cases r0 with
            | nil => simp only [List.length_nil] at hl; omega
            | cons b bt =>
              have hbt : bt.length = n + 1 := by simp only [List.length_cons] at hl; omega
              simp only [elimRow]
              simpa only [hbt] using axpy_length _ _ _ (hbt.trans hrt.symm)
          have hc' : AffineConsistent n (others.map (elimRow ai rt)) := by
            refine ⟨wt, hwt, ?_⟩
            have hpt := tail_dot_of_augmented_zero a h rt wt (hd _ hpm)
            intro r hr
            obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr
            have hl := hlen r0 (hsub r0 hr0)
            have he := hd r0 (hsub r0 hr0)
            cases r0 with
            | nil => exact dotVec_nil_left _
            | cons b bt =>
              have hbt : bt.length = n + 1 := by simp only [List.length_cons] at hl; omega
              have hbtDot := tail_dot_of_augmented_zero b h bt wt he
              simp only [elimRow]
              rw [dotVec_axpy _ bt rt (wt ++ [one]) (hbt.trans hrt.symm), hbtDot, hpt]
              have heq : sub (neg (mul b h)) (mul (mul b ai) (neg (mul a h))) =
                  add (neg (mul b h)) (mul (mul b h) (mul a ai)) := by constructive_ring
              rw [heq, hinv, LawfulCommRing.mul_one, LawfulCommRing.add_left_neg]
          have ih := solveAffine_spec n (others.map (elimRow ai rt)) hlen' hc'
          generalize solveAffine n (others.map (elimRow ai rt)) = v at ih ⊢
          intro r hr
          rcases hcover r hr with he | ho
          · subst r
            simp only [List.cons_append, dotVec_cons]
            have heq : add (mul a (neg (mul ai (dotVec rt (v ++ [one])))))
                (dotVec rt (v ++ [one])) =
                add (neg (mul (mul a ai) (dotVec rt (v ++ [one]))))
                  (dotVec rt (v ++ [one])) := by constructive_ring
            rw [heq, hinv, LawfulCommRing.one_mul, LawfulCommRing.add_left_neg]
          · have hl := hlen r (hsub r ho)
            have he := ih _ (List.mem_map.mpr ⟨r, ho, rfl⟩)
            cases r with
            | nil => exact dotVec_nil_left _
            | cons b bt =>
              have hbt : bt.length = n + 1 := by simp only [List.length_cons] at hl; omega
              simp only [elimRow] at he
              rw [dotVec_axpy _ bt rt (v ++ [one]) (hbt.trans hrt.symm)] at he
              have ht := LawfulCommRing.sub_eq_zero_iff.mp he
              simp only [List.cons_append, dotVec_cons, ht]
              constructive_ring

/-- The same public-data algorithm with a field-operation counter. -/
def solveAffineT [LawfulField F] [DecidableEq F] : Nat → List (List F) → Tick (List F)
  | 0, _ => pure []
  | n + 1, rows => do
    let piv ← extractPivotT rows
    match piv with
    | none => do
      let v ← solveAffineT n (rows.map List.tail)
      pure (zero :: v)
    | some (p, others) => do
      let ai ← tInv (p.headD zero)
      let others' ← mapT (elimRowT ai p.tail) others
      let v ← solveAffineT n others'
      let d ← dotT p.tail (v ++ [one])
      let t ← tMul ai d
      let x0 ← tNeg t
      pure (x0 :: v)

theorem val_solveAffineT [LawfulField F] [DecidableEq F] :
    ∀ n (rows : List (List F)), (solveAffineT n rows).val = solveAffine n rows
  | 0, _ => rfl
  | n + 1, rows => by
    simp only [solveAffineT, solveAffine, Tick.val_bind, val_extractPivotT]
    cases extractPivot rows with
    | none => simp only [Tick.val_bind, Tick.val_pure, val_solveAffineT]
    | some po =>
      obtain ⟨p, others⟩ := po
      have hmap : (mapT (elimRowT (LawfulField.inv (p.headD zero)) p.tail) others).val =
          others.map (elimRow (LawfulField.inv (p.headD zero)) p.tail) := by
        rw [val_mapT]
        exact List.map_congr_left (fun row _ => val_elimRowT _ _ row)
      simp only [Tick.val_bind, Tick.val_pure, val_tInv, val_tMul, val_tNeg, val_dotT,
        hmap, val_solveAffineT]

/-- An explicit polynomial field-operation bound, including the free-variable branches. -/
theorem cost_solveAffineT_le [LawfulField F] [DecidableEq F] (R W : Nat) :
    ∀ N (rows : List (List F)), N ≤ W + 1 → rows.length ≤ R →
      (∀ row ∈ rows, row.length ≤ N + 1) →
      (solveAffineT N rows).cost ≤ N * (R * (2 * W + 4) + 2 * W + 5)
  | 0, _, _, _, _ => by simp only [solveAffineT, Tick.cost_pure, Nat.zero_mul, Nat.le_refl]
  | n + 1, rows, hN, hR, hlen => by
    have hce := cost_extractPivotT_le rows
    have hL : (n + 1) * (R * (2 * W + 4) + 2 * W + 5) =
        n * (R * (2 * W + 4) + 2 * W + 5) + (R * (2 * W + 4) + 2 * W + 5) := Nat.succ_mul _ _
    have hsplit : R * (2 * W + 4) = R * (2 * W + 3) + R := Nat.mul_succ R (2 * W + 3)
    rw [hL]
    simp only [solveAffineT, Tick.cost_bind, val_extractPivotT]
    cases hpiv : extractPivot rows with
    | none =>
      have hrows' : ∀ r ∈ rows.map List.tail, r.length ≤ n + 1 := by
        intro r hr
        obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr
        have hl := hlen r0 hr0
        rw [List.length_tail]
        omega
      have ih := cost_solveAffineT_le R W n (rows.map List.tail) (by omega)
        (by simpa only [List.length_map] using hR) hrows'
      simp only [Tick.cost_bind, Tick.cost_pure]
      omega
    | some po =>
      obtain ⟨p, others⟩ := po
      obtain ⟨_, hpm, hsub, hcnt, _⟩ := extractPivot_some rows p others hpiv
      have hmapv : (mapT (elimRowT (LawfulField.inv (p.headD zero)) p.tail) others).val =
          others.map (elimRow (LawfulField.inv (p.headD zero)) p.tail) := by
        rw [val_mapT]
        exact List.map_congr_left (fun row _ => val_elimRowT _ _ row)
      have hcm : (mapT (elimRowT (LawfulField.inv (p.headD zero)) p.tail) others).cost ≤
          others.length * (2 * n + 3) := by
        apply cost_mapT_le
        intro row hrow
        have hl := hlen row (hsub row hrow)
        rcases cost_elimRowT_le (LawfulField.inv (p.headD zero)) p.tail row with h | h
        · omega
        · subst h; simp only [elimRowT, Tick.cost_pure, Nat.zero_le]
      have hrows' : ∀ row' ∈ others.map (elimRow (LawfulField.inv (p.headD zero)) p.tail),
          row'.length ≤ n + 1 := by
        intro row' hm'
        obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hm'
        have hl := hlen row (hsub row hrow)
        cases row with
        | nil => simp only [elimRow, List.length_nil, Nat.zero_le]
        | cons b bt =>
          simp only [List.length_cons] at hl
          have he := axpy_length_le (mul b (LawfulField.inv (p.headD zero))) bt p.tail
          simp only [elimRow]
          omega
      have ih := cost_solveAffineT_le R W n
        (others.map (elimRow (LawfulField.inv (p.headD zero)) p.tail)) (by omega)
        (by rw [List.length_map]; omega) hrows'
      have hcd := cost_dotT_le p.tail
        (solveAffine n (others.map (elimRow (LawfulField.inv (p.headD zero)) p.tail)) ++ [one])
      rw [List.length_append, solveAffine_length, List.length_cons, List.length_nil] at hcd
      have hX : others.length * (2 * n + 3) ≤ R * (2 * W + 3) :=
        Nat.mul_le_mul (by omega) (by omega)
      simp only [Tick.cost_bind, Tick.cost_pure, val_tInv, cost_tInv, cost_tMul, cost_tNeg,
        val_tMul, val_dotT, hmapv, val_solveAffineT]
      omega

#verify_constructive solveAffine_length solveAffine_spec val_solveAffineT cost_solveAffineT_le
/-- Polynomial field-operation bound in the public matrix dimensions. -/
theorem solveAffine_ops_poly [LawfulField F] [DecidableEq F] (n : Nat)
    (rows : List (List F)) (hlen : ∀ row ∈ rows, row.length ≤ n + 1) :
    (solveAffineT n rows).cost ≤ n * (rows.length * (2 * n + 4) + 2 * n + 5) :=
  cost_solveAffineT_le rows.length n n rows (Nat.le_succ n) (Nat.le_refl _) hlen

#verify_constructive solveAffine_ops_poly

/-! ## 4. The Welch–Berlekamp key equations -/

/-- `geom x c j = [c, c·x, …, c·x^(j-1)]`. -/
def geom [CommRingOps F] (x : F) : F → Nat → List F
  | _, 0 => []
  | c, j + 1 => c :: geom x (mul c x) j

/-- Counted `geom`: one multiplication per entry. -/
def geomT [CommRingOps F] (x : F) : F → Nat → Tick (List F)
  | _, 0 => pure []
  | c, j + 1 => do
    let c' ← tMul c x
    let rest ← geomT x c' j
    pure (c :: rest)

theorem val_geomT [CommRingOps F] (x : F) : ∀ (c : F) (j : Nat), (geomT x c j).val = geom x c j
  | _, 0 => by rfl
  | c, j + 1 => by
    simp only [geomT, geom, Tick.val_bind, Tick.val_pure, val_tMul, val_geomT x _ j]

theorem cost_geomT [CommRingOps F] (x : F) : ∀ (c : F) (j : Nat), (geomT x c j).cost = j
  | _, 0 => by rfl
  | c, j + 1 => by
    simp only [geomT, Tick.cost_bind, Tick.cost_pure, cost_tMul, val_tMul, cost_geomT x _ j]
    omega

theorem geom_length [CommRingOps F] (x : F) : ∀ (c : F) (j : Nat), (geom x c j).length = j
  | _, 0 => by rfl
  | c, j + 1 => by simp only [geom, List.length_cons, geom_length x _ j]

theorem dotVec_geom [LawfulCommRing F] (x : F) :
    ∀ (j : Nat) (c : F) (p : List F), p.length = j →
      dotVec (geom x c j) p = mul c (evalCoeffs p x)
  | 0, c, [], _ => by
    simp only [geom, dotVec_nil_left, evalCoeffs_nil, LawfulCommRing.mul_zero]
  | 0, _, _ :: _, h => by simp only [List.length_cons] at h; exfalso; omega
  | _ + 1, _, [], h => by simp only [List.length_nil] at h; exfalso; omega
  | j + 1, c, a :: as, h => by
    have ih := dotVec_geom x j (mul c x) as (by simp only [List.length_cons] at h; omega)
    simp only [geom, dotVec_cons, evalCoeffs_cons, ih]
    constructive_ring

/-- The key-equation row of the point `x`: its dot product with the coefficients of `N`
    (`k + e` of them) followed by those of `E` (`e + 1` of them) is
    `N(x) - word x · E(x)`. -/
def wbRow [CommRingOps F] (k e : Nat) (word : F → F) (x : F) : List F :=
  geom x one (k + e) ++ geom x (neg (word x)) (e + 1)

/-- Counted `wbRow`. -/
def wbRowT [CommRingOps F] (k e : Nat) (word : F → F) (x : F) : Tick (List F) := do
  let a ← geomT x one (k + e)
  let ny ← tNeg (word x)
  let b ← geomT x ny (e + 1)
  pure (a ++ b)

theorem val_wbRowT [CommRingOps F] (k e : Nat) (word : F → F) (x : F) :
    (wbRowT k e word x).val = wbRow k e word x := by
  simp only [wbRowT, wbRow, Tick.val_bind, Tick.val_pure, val_tNeg, val_geomT]

theorem cost_wbRowT [CommRingOps F] (k e : Nat) (word : F → F) (x : F) :
    (wbRowT k e word x).cost = k + 2 * e + 2 := by
  simp only [wbRowT, Tick.cost_bind, Tick.cost_pure, cost_tNeg, cost_geomT]
  omega

theorem wbRow_length [CommRingOps F] (k e : Nat) (word : F → F) (x : F) :
    (wbRow k e word x).length = k + 2 * e + 1 := by
  simp only [wbRow, List.length_append, geom_length]
  omega

theorem wbRow_dot [LawfulCommRing F] (k e : Nat) (word : F → F) (x : F) (N E : List F)
    (hN : N.length = k + e) (hE : E.length = e + 1)
    (h : dotVec (wbRow k e word x) (N ++ E) = zero) :
    evalCoeffs N x = mul (word x) (evalCoeffs E x) := by
  unfold wbRow at h
  rw [dotVec_append_eq _ _ _ _ (by rw [geom_length, hN]), dotVec_geom x _ _ N hN,
    dotVec_geom x _ _ E hE] at h
  have e : sub (evalCoeffs N x) (mul (word x) (evalCoeffs E x)) =
      add (mul one (evalCoeffs N x)) (mul (neg (word x)) (evalCoeffs E x)) := by
    constructive_ring
  exact LawfulCommRing.sub_eq_zero_iff.mp (e.trans h)

/-! ## 5. Trimming, evaluation and division -/

/-- Counted `trimPoly`: one zero test per removed trailing coefficient, and one more. -/
def trimT [CommRingOps F] [DecidableEq F] : List F → Tick (List F)
  | [] => pure []
  | c :: cs => do
    let cs' ← trimT cs
    match cs' with
    | [] => do
      let z ← tIsZero c
      if z then pure [] else pure [c]
    | d :: ds => pure (c :: d :: ds)

theorem val_trimT [CommRingOps F] [DecidableEq F] : ∀ p : List F, (trimT p).val = trimPoly p
  | [] => by rfl
  | c :: cs => by
    have ih := val_trimT cs
    simp only [trimT, trimPoly, Tick.val_bind, ih]
    cases trimPoly cs with
    | nil =>
      if hc : c = zero then
        simp only [Tick.val_bind, val_tIsZero, hc, decide_true, ↓reduceIte, Tick.val_pure,
          and_self]
      else
        simp only [Tick.val_bind, val_tIsZero, hc, decide_false, ↓reduceIte, Tick.val_pure,
          Bool.false_eq_true, and_false]
    | cons d ds => simp only [Tick.val_pure, reduceCtorEq, false_and, ↓reduceIte]

