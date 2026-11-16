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

theorem cost_trimT_le [CommRingOps F] [DecidableEq F] :
    ∀ p : List F, (trimT p).cost ≤ p.length
  | [] => by simp only [trimT, Tick.cost_pure]; exact Nat.zero_le _
  | c :: cs => by
    have ih := cost_trimT_le cs
    simp only [trimT, Tick.cost_bind, List.length_cons]
    cases (trimT cs).val with
    | nil =>
      if hc : c = zero then
        simp only [Tick.cost_bind, cost_tIsZero, val_tIsZero, hc, decide_true, ↓reduceIte,
          Tick.cost_pure]
        omega
      else
        simp only [Tick.cost_bind, cost_tIsZero, val_tIsZero, hc, decide_false, ↓reduceIte,
          Tick.cost_pure, Bool.false_eq_true]
        omega
    | cons d ds => simp only [Tick.cost_pure]; omega

/-- Counted Horner evaluation: one multiplication and one addition per coefficient. -/
def evalT [CommRingOps F] (x : F) : List F → Tick F
  | [] => pure zero
  | c :: cs => do
    let r ← evalT x cs
    let m ← tMul x r
    tAdd c m

theorem val_evalT [CommRingOps F] (x : F) : ∀ p : List F, (evalT x p).val = evalCoeffs p x
  | [] => by rfl
  | c :: cs => by
    simp only [evalT, Tick.val_bind, val_tMul, val_tAdd, evalCoeffs_cons, val_evalT x cs]

theorem cost_evalT [CommRingOps F] (x : F) : ∀ p : List F, (evalT x p).cost = 2 * p.length
  | [] => by rfl
  | c :: cs => by
    simp only [evalT, Tick.cost_bind, cost_tMul, cost_tAdd, List.length_cons, cost_evalT x cs]
    omega

/-- Number of domain points at which the coefficient list `q` takes the value of `word`. -/
@[expose] def agreeCount [CommRingOps F] [DecidableEq F] (word : F → F) (q : List F)
    (domain : List F) : Nat :=
  (domain.filter (fun x => decide (evalCoeffs q x = word x))).length

/-- Counted `agreeCount`: one evaluation and one comparison per domain point. -/
def countAgreeT [CommRingOps F] [DecidableEq F] (word : F → F) (q : List F) :
    List F → Tick Nat
  | [] => pure 0
  | x :: xs => do
    let v ← evalT x q
    let ok ← tEq v (word x)
    let rest ← countAgreeT word q xs
    pure (if ok then rest + 1 else rest)

theorem val_countAgreeT [CommRingOps F] [DecidableEq F] (word : F → F) (q : List F) :
    ∀ domain : List F, (countAgreeT word q domain).val = agreeCount word q domain
  | [] => by rfl
  | x :: xs => by
    have ih := val_countAgreeT word q xs
    unfold agreeCount at ih ⊢
    simp only [countAgreeT, Tick.val_bind, Tick.val_pure, val_tEq, val_evalT, ih,
      List.filter_cons]
    if h : evalCoeffs q x = word x then
      simp only [h, decide_true, ↓reduceIte, List.length_cons]
    else
      simp only [h, decide_false, ↓reduceIte, Bool.false_eq_true]

theorem cost_countAgreeT [CommRingOps F] [DecidableEq F] (word : F → F) (q : List F) :
    ∀ domain : List F, (countAgreeT word q domain).cost = domain.length * (2 * q.length + 1)
  | [] => by simp only [countAgreeT, Tick.cost_pure, List.length_nil, Nat.zero_mul]
  | x :: xs => by
    simp only [countAgreeT, Tick.cost_bind, Tick.cost_pure, cost_tEq, cost_evalT,
      cost_countAgreeT word q xs, List.length_cons, Nat.succ_mul]
    omega

theorem cost_axpyT_le_right [CommRingOps F] (c : F) :
    ∀ s b : List F, (axpyT c s b).cost ≤ 2 * b.length
  | s :: ss, b :: bs => by
    have ih := cost_axpyT_le_right c ss bs
    simp only [axpyT, Tick.cost_bind, Tick.cost_pure, cost_tMul, cost_tSub, List.length_cons]
    omega
  | [], _ => by simp only [axpyT, Tick.cost_pure, Nat.zero_le]
  | _ :: _, [] => by simp only [axpyT, Tick.cost_pure, Nat.zero_le]

/-- Long division of `a` by a divisor `b` whose leading coefficient has inverse `bi`,
    by recursion on the coefficients of `a` from the top. The pair is (quotient, remainder);
    the remainder always has `b.length - 1` coefficients. Each step shifts the remainder up by
    one, brings in the next coefficient of `a` and cancels the top coefficient against `b`. -/
def divRaw [CommRingOps F] (b : List F) (bi : F) : List F → List F × List F
  | [] => ([], List.replicate (b.length - 1) zero)
  | c :: cs =>
    let qr := divRaw b bi cs
    let t := mul (coeffAt (c :: qr.2) (b.length - 1)) bi
    (t :: qr.1, (axpy t (c :: qr.2) b).dropLast)

/-- Counted `divRaw`: `2 * b.length + 1` operations per coefficient of the dividend. -/
def divT [CommRingOps F] (b : List F) (bi : F) : List F → Tick (List F × List F)
  | [] => pure ([], List.replicate (b.length - 1) zero)
  | c :: cs => do
    let qr ← divT b bi cs
    let t ← tMul (coeffAt (c :: qr.2) (b.length - 1)) bi
    let u ← axpyT t (c :: qr.2) b
    pure (t :: qr.1, u.dropLast)

theorem val_divT [CommRingOps F] (b : List F) (bi : F) :
    ∀ a : List F, (divT b bi a).val = divRaw b bi a
  | [] => by rfl
  | c :: cs => by
    simp only [divT, divRaw, Tick.val_bind, Tick.val_pure, val_tMul, val_axpyT, val_divT b bi cs]

theorem cost_divT_le [CommRingOps F] (b : List F) (bi : F) :
    ∀ a : List F, (divT b bi a).cost ≤ a.length * (2 * b.length + 1)
  | [] => by simp only [divT, Tick.cost_pure]; exact Nat.zero_le _
  | c :: cs => by
    have ih := cost_divT_le b bi cs
    have hax := cost_axpyT_le_right
      (mul (coeffAt (c :: (divT b bi cs).val.2) (b.length - 1)) bi)
      (c :: (divT b bi cs).val.2) b
    have hL : (cs.length + 1) * (2 * b.length + 1) =
        cs.length * (2 * b.length + 1) + (2 * b.length + 1) := Nat.succ_mul _ _
    simp only [divT, Tick.cost_bind, Tick.cost_pure, cost_tMul, val_tMul, List.length_cons, hL]
    omega

theorem divRaw_fst_length [CommRingOps F] (b : List F) (bi : F) :
    ∀ a : List F, (divRaw b bi a).1.length = a.length
  | [] => by rfl
  | c :: cs => by simp only [divRaw, List.length_cons, divRaw_fst_length b bi cs]

theorem coeffAt_replicate_zero [CommRingOps F] :
    ∀ (n j : Nat), coeffAt (List.replicate n (zero : F)) j = zero
  | 0, _ => coeffAt_nil _
  | _ + 1, 0 => by simp only [List.replicate_succ, coeffAt_cons_zero]
  | n + 1, j + 1 => by
    simp only [List.replicate_succ, coeffAt_cons_succ, coeffAt_replicate_zero n j]

theorem coeffAt_dropLast [CommRingOps F] :
    ∀ (u : List F) (d : Nat), u.length = d + 1 → coeffAt u d = zero →
      ∀ j, coeffAt u.dropLast j = coeffAt u j
  | [], _, h, _, _ => by simp only [List.length_nil] at h; exfalso; omega
  | [x], d, h, h0, j => by
    have hd : d = 0 := by simp only [List.length_cons, List.length_nil] at h; omega
    subst hd
    rw [coeffAt_cons_zero] at h0
    subst h0
    cases j with
    | zero => simp only [List.dropLast_singleton, coeffAt_nil, coeffAt_cons_zero]
    | succ j => simp only [List.dropLast_singleton, coeffAt_nil, coeffAt_cons_succ]
  | x :: y :: l, d, h, h0, j => by
    cases d with
    | zero => simp only [List.length_cons] at h; exfalso; omega
    | succ d' =>
      rw [coeffAt_cons_succ] at h0
      have ih := coeffAt_dropLast (y :: l) d'
        (by simp only [List.length_cons] at h ⊢; omega) h0
      cases j with
      | zero => simp only [List.dropLast_cons_cons, coeffAt_cons_zero]
      | succ j => simp only [List.dropLast_cons_cons, coeffAt_cons_succ, ih j]

/-- **Division is exact arithmetic on coefficients.** For a divisor `b` of length `d + 1`
    whose top coefficient has inverse `bi`, the remainder has `d` coefficients and
    `a = q · b + r` coefficient by coefficient. -/
theorem divRaw_spec [LawfulCommRing F] (b : List F) (d : Nat) (bi : F)
    (hb : b.length = d + 1) (hinv : mul (coeffAt b d) bi = one) :
    ∀ a : List F, (divRaw b bi a).2.length = d ∧
      ∀ j, coeffAt a j =
        add (coeffAt (rawMul (divRaw b bi a).1 b) j) (coeffAt (divRaw b bi a).2 j)
  | [] => by
    have hd : b.length - 1 = d := by omega
    simp only [divRaw, hd, List.length_replicate, rawMul, coeffAt_nil, coeffAt_replicate_zero,
      LawfulCommRing.add_zero, true_and, implies_true]
  | c :: cs => by
    have hd : b.length - 1 = d := by omega
    obtain ⟨hr, hc⟩ := divRaw_spec b d bi hb hinv cs
    simp only [divRaw, hd]
    generalize divRaw b bi cs = qr at hr hc
    obtain ⟨q, r⟩ := qr
    simp only at hr hc ⊢
    have hsl : (c :: r).length = b.length := by simp only [List.length_cons]; omega
    have hax := fun j => coeffAt_axpy (mul (coeffAt (c :: r) d) bi) (c :: r) b j hsl
    have htop : coeffAt (axpy (mul (coeffAt (c :: r) d) bi) (c :: r) b) d = zero := by
      rw [hax]
      have e : sub (coeffAt (c :: r) d) (mul (mul (coeffAt (c :: r) d) bi) (coeffAt b d)) =
          sub (coeffAt (c :: r) d) (mul (coeffAt (c :: r) d) (mul (coeffAt b d) bi)) := by
        constructive_ring
      rw [e, hinv, LawfulCommRing.mul_one, LawfulCommRing.sub_self]
    have hul : (axpy (mul (coeffAt (c :: r) d) bi) (c :: r) b).length = d + 1 := by
      rw [axpy_length _ _ _ hsl]; omega
    refine ⟨by rw [List.length_dropLast, hul]; omega, ?_⟩
    intro j
    rw [coeffAt_dropLast _ d hul htop j, hax j]
    simp only [rawMul, coeffAt_addCoeffs, coeffAt_map_mul]
    cases j with
    | zero =>
      simp only [coeffAt_cons_zero]
      constructive_ring
    | succ j =>
      simp only [coeffAt_cons_succ, hc j]
      constructive_ring

/-! ## 6. The decoder -/

/-- **Welch–Berlekamp unique decoder, with its operation count.** See the module header for
    the five steps. -/
def wbDecodeT [LawfulField F] [DecidableEq F] (k e : Nat) (domain : List F) (word : F → F) :
    Tick (Option (List F)) :=
  if domain.length < k + 2 * e then pure none
  else do
    let rows ← mapT (wbRowT k e word) (domain.take (k + 2 * e))
    let v ← solveT (k + 2 * e + 1) rows
    let eTrim ← trimT (v.drop (k + e))
    if eTrim.length = 0 then pure none
    else do
      let bi ← tInv (coeffAt eTrim (eTrim.length - 1))
      let qr ← divT eTrim bi (v.take (k + e))
      let q ← trimT qr.1
      if k < q.length then pure none
      else do
        let agree ← countAgreeT word q domain
        if domain.length ≤ agree + e then pure (some q) else pure none

/-- **Welch–Berlekamp unique decoder.** `some Q` is a trimmed coefficient list of length at
    most `k` agreeing with `word` on all but at most `e` domain points; `none` means the
    decoder found no such codeword. -/
def wbDecode [LawfulField F] [DecidableEq F] (k e : Nat) (domain : List F) (word : F → F) :
    Option (List F) :=
  (wbDecodeT k e domain word).val

/-- The explicit operation bound: a cubic polynomial in the block length. -/
@[expose] def wbOpBound (n : Nat) : Nat := 2 * (n + 2) ^ 3 + 5 * (n + 2) ^ 2

/-- The nonzero key-equation solution `N ++ E` found by Gaussian elimination. -/
def wbKeySolution [LawfulField F] [DecidableEq F] (k e : Nat) (domain : List F)
    (word : F → F) : List F :=
  solve (k + 2 * e + 1) ((domain.take (k + 2 * e)).map (wbRow k e word))

/-- The candidate codeword `N / E`, trimmed. -/
def wbCandidate [LawfulField F] [DecidableEq F] (k e : Nat) (domain : List F)
    (word : F → F) : List F :=
  trimPoly (divRaw (trimPoly ((wbKeySolution k e domain word).drop (k + e)))
    (LawfulField.inv (coeffAt (trimPoly ((wbKeySolution k e domain word).drop (k + e)))
      ((trimPoly ((wbKeySolution k e domain word).drop (k + e))).length - 1)))
    ((wbKeySolution k e domain word).take (k + e))).1

theorem val_wbRows [LawfulField F] [DecidableEq F] (k e : Nat) (word : F → F) (pts : List F) :
    (mapT (wbRowT k e word) pts).val = pts.map (wbRow k e word) := by
  rw [val_mapT]
  exact List.map_congr_left (fun x _ => val_wbRowT k e word x)

theorem Tick.val_ite {α : Type} (c : Prop) [Decidable c] (a b : Tick α) :
    (if c then a else b).val = if c then a.val else b.val := by
  split <;> rfl

/-- The value of the decoder, without the counter. -/
theorem wbDecode_eq [LawfulField F] [DecidableEq F] (k e : Nat) (domain : List F)
    (word : F → F) :
    wbDecode k e domain word =
      if domain.length < k + 2 * e then none
      else if (trimPoly ((wbKeySolution k e domain word).drop (k + e))).length = 0 then none
      else if k < (wbCandidate k e domain word).length then none
      else if domain.length ≤ agreeCount word (wbCandidate k e domain word) domain + e then
        some (wbCandidate k e domain word)
      else none := by
  unfold wbDecode wbDecodeT wbCandidate wbKeySolution
  simp only [Tick.val_ite, Tick.val_bind, Tick.val_pure, val_wbRows, val_solveT, val_trimT,
    val_tInv, val_divT, val_countAgreeT]

/-! ## 7. Soundness -/

theorem wbCandidate_trimmed [LawfulField F] [DecidableEq F] (k e : Nat) (domain : List F)
    (word : F → F) : IsTrimmed (wbCandidate k e domain word) := by
  unfold wbCandidate
  exact trimPoly_idem _

/-- **Soundness.** Whatever the received word, an accepted output is a trimmed coefficient
    list of length at most `k` that agrees with `word` on all but at most `e` domain points,
    and the parameters are inside the unique-decoding radius. -/
theorem wbDecode_sound [LawfulField F] [DecidableEq F] (k e : Nat) (domain : List F)
    (word : F → F) (Q : List F) (h : wbDecode k e domain word = some Q) :
    IsTrimmed Q ∧ Q.length ≤ k ∧ domain.length ≤ agreeCount word Q domain + e ∧
      k + 2 * e ≤ domain.length := by
  rw [wbDecode_eq] at h
  if h1 : domain.length < k + 2 * e then
    rw [ite_eq_left h1] at h; exact nomatch h
  else
    rw [ite_eq_right h1] at h
    if h2 : (trimPoly ((wbKeySolution k e domain word).drop (k + e))).length = 0 then
      rw [ite_eq_left h2] at h; exact nomatch h
    else
      rw [ite_eq_right h2] at h
      if h3 : k < (wbCandidate k e domain word).length then
        rw [ite_eq_left h3] at h; exact nomatch h
      else
        rw [ite_eq_right h3] at h
        if h4 : domain.length ≤ agreeCount word (wbCandidate k e domain word) domain + e then
          rw [ite_eq_left h4] at h
          have hQ := Option.some.inj h
          subst hQ
          exact ⟨wbCandidate_trimmed k e domain word, by omega, h4, by omega⟩
        else
          rw [ite_eq_right h4] at h; exact nomatch h

/-- The decoder rejects every input whose parameters are outside the unique-decoding radius. -/
theorem wbDecode_none_of_short [LawfulField F] [DecidableEq F] (k e : Nat) (domain : List F)
    (word : F → F) (h : domain.length < k + 2 * e) : wbDecode k e domain word = none := by
  rw [wbDecode_eq, ite_eq_left h]

/-! ## 8. Completeness -/

theorem filter_take_count {α : Type} (p : α → Bool) :
    ∀ (l : List α) (m : Nat),
      (l.filter p).length + (l.take m).length ≤ ((l.take m).filter p).length + l.length
  | [], m => by simp only [List.take_nil, List.filter_nil, List.length_nil, Nat.le_refl]
  | a :: l, 0 => by
    have := List.length_filter_le p (a :: l)
    simp only [List.take_zero, List.filter_nil, List.length_nil]
    omega
  | a :: l, m + 1 => by
    have ih := filter_take_count p l m
    cases hp : p a <;>
      simp only [List.take_succ_cons, List.filter_cons, hp, ↓reduceIte, List.length_cons,
        Bool.false_eq_true] <;> omega

theorem all_zero_of_trimPoly_nil [CommRingOps F] [DecidableEq F] :
    ∀ p : List F, trimPoly p = [] → ∀ x ∈ p, x = zero
  | [], _, _, hm => nomatch hm
  | c :: cs, h, x, hm => by
    simp only [trimPoly] at h
    if hc : trimPoly cs = [] ∧ c = zero then
      cases hm with
      | head => exact hc.2
      | tail _ hm' => exact all_zero_of_trimPoly_nil cs hc.1 x hm'
    else
      rw [ite_eq_right hc] at h
      exact nomatch h

/-- Two coefficient lists of length at most `B` that take equal values on `B` distinct points
    are equal after trimming. -/
theorem trimPoly_eq_of_agree_le [LawfulField F] [DecidableEq F] {B : Nat} {P Q U : List F}
    (hP : P.length ≤ B) (hQ : Q.length ≤ B) (hU : U.Nodup) (hUl : B ≤ U.length)
    (h : ∀ x ∈ U, evalCoeffs P x = evalCoeffs Q x) : trimPoly P = trimPoly Q := by
  have hD : (pSub P Q).length ≤ B := by
    have := length_trimPoly_le_of_coeffAt_zero (pSub P Q) B (by
      intro j hj
      rw [coeffAt_pSub, coeffAt_eq_zero_of_ge P j (by omega),
        coeffAt_eq_zero_of_ge Q j (by omega), LawfulCommRing.sub_self])
    rwa [UPoly.pSub_trimmed] at this
  if hnil : pSub P Q = [] then
    rw [trimPoly_eq_iff_coeffAt]
    intro j
    have hj := coeffAt_pSub P Q j
    rw [hnil, coeffAt_nil] at hj
    exact LawfulCommRing.sub_eq_zero_iff.mp hj.symm
  else
    obtain ⟨x, hx, hne⟩ :=
      exists_nonroot_of_trim_ne_nil (UPoly.pSub_trimmed P Q) hnil hU (by omega)
    exact absurd (by rw [evalCoeffs_pSub, h x hx, LawfulCommRing.sub_self]) hne

/-- **The key-equation argument.** Let `v` be any nonzero solution of the key equations on the
    first `k + 2 * e` domain points, and let `P` be a codeword within distance `e` of `word`.
    Then the `E` part of `v` is a nonzero polynomial and dividing the `N` part by it gives
    exactly `P`. -/
theorem key_solution_divides [LawfulField F] [DecidableEq F] (k e : Nat) (domain : List F)
    (word : F → F) (hDom : domain.Nodup) (hRad : k + 2 * e ≤ domain.length)
    (P : List F) (hPt : IsTrimmed P) (hPk : P.length ≤ k)
    (hAgree : domain.length ≤ agreeCount word P domain + e)
    (v : List F) (hvl : v.length = k + 2 * e + 1) (hnz : ∃ x ∈ v, x ≠ zero)
    (hdot : ∀ x ∈ domain.take (k + 2 * e), dotVec (wbRow k e word x) v = zero) :
    trimPoly (v.drop (k + e)) ≠ [] ∧
    trimPoly (divRaw (trimPoly (v.drop (k + e)))
      (LawfulField.inv (coeffAt (trimPoly (v.drop (k + e)))
        ((trimPoly (v.drop (k + e))).length - 1)))
      (v.take (k + e))).1 = P := by
  have hNE : v.take (k + e) ++ v.drop (k + e) = v := List.take_append_drop _ _
  have hNl : (v.take (k + e)).length = k + e := by rw [List.length_take]; omega
  have hEl : (v.drop (k + e)).length = e + 1 := by rw [List.length_drop]; omega
  generalize v.take (k + e) = N at hNE hNl
  generalize v.drop (k + e) = E at hNE hEl
  have hkey : ∀ x ∈ domain.take (k + 2 * e),
      evalCoeffs N x = mul (word x) (evalCoeffs E x) := by
    intro x hx
    apply wbRow_dot k e word x N E hNl hEl
    rw [hNE]
    exact hdot x hx
  -- The agreement set inside the first `k + 2 * e` points has at least `k + e` elements.
  have hUnd : ((domain.take (k + 2 * e)).filter
      (fun x => decide (evalCoeffs P x = word x))).Nodup :=
    (hDom.sublist (List.take_sublist _ _)).sublist List.filter_sublist
  have hUlen : k + e ≤ ((domain.take (k + 2 * e)).filter
      (fun x => decide (evalCoeffs P x = word x))).length := by
    have hc := filter_take_count (fun x => decide (evalCoeffs P x = word x)) domain (k + 2 * e)
    have ht : (domain.take (k + 2 * e)).length = k + 2 * e := by
      rw [List.length_take]; omega
    unfold agreeCount at hAgree
    omega
  have hprodLen : (pMul E P).length ≤ k + e := by
    have hpl : P.length = 0 ∨ 1 ≤ P.length := by omega
    rcases hpl with h0 | h1
    · have hP0 : P = [] := List.eq_nil_of_length_eq_zero h0
      rw [hP0, (pMul_eq_nil_iff E []).mpr (.inr rfl)]
      exact Nat.zero_le _
    · have := pMul_length_le E P e (k - 1) (by omega) (by omega)
      omega
  have hNP : trimPoly N = pMul E P := by
    have h := trimPoly_eq_of_agree_le (B := k + e) (P := N) (Q := pMul E P) (by omega)
      hprodLen hUnd hUlen (by
        intro x hx
        have hx' := List.mem_filter.mp hx
        have hPx : evalCoeffs P x = word x := of_decide_eq_true hx'.2
        rw [evalCoeffs_pMul, hkey x hx'.1, hPx, LawfulCommRing.mul_comm])
    rw [h]
    exact trimPoly_idem _
  have hEne : trimPoly E ≠ [] := by
    intro hE0
    have hN0 : trimPoly N = [] := by
      rw [hNP, ← pMul_trimPoly_left, hE0]
      exact pMul_nil_left_eq P
    obtain ⟨x0, hx0, hx0ne⟩ := hnz
    rw [← hNE] at hx0
    rcases List.mem_append.mp hx0 with h | h
    · exact hx0ne (all_zero_of_trimPoly_nil N hN0 x0 h)
    · exact hx0ne (all_zero_of_trimPoly_nil E hE0 x0 h)
  refine ⟨hEne, ?_⟩
  have hE1 : 1 ≤ (trimPoly E).length := by
    cases hE' : trimPoly E with
    | nil => exact absurd hE' hEne
    | cons _ _ => simp only [List.length_cons]; omega
  have hinv := LawfulField.mul_inv_cancel (leadCoeff_ne_zero_of_trimPoly_ne_nil E hEne)
  obtain ⟨hrl, hcoef⟩ := divRaw_spec (trimPoly E) ((trimPoly E).length - 1)
    (LawfulField.inv (coeffAt (trimPoly E) ((trimPoly E).length - 1))) (by omega) hinv N
  generalize divRaw (trimPoly E)
    (LawfulField.inv (coeffAt (trimPoly E) ((trimPoly E).length - 1))) N = qr at hrl hcoef
  obtain ⟨q, r⟩ := qr
  simp only at hrl hcoef ⊢
  have hdecomp : trimPoly N = pAdd (pMul q (trimPoly E)) r := by
    rw [← UPoly.pAdd_trimmed, trimPoly_eq_iff_coeffAt]
    intro j
    rw [coeffAt_pAdd, hcoef j]
    show _ = add (coeffAt (trimPoly (rawMul q (trimPoly E))) j) _
    rw [coeffAt_trimPoly]
  have h1 := pSub_pAdd_cancel_left (pMul q (trimPoly E)) r
  rw [← hdecomp, hNP, ← pMul_trimPoly_left E P, pMul_comm q (trimPoly E),
    ← pMul_pSub_right] at h1
  if hd : pSub P q = [] then
    have hPq : trimPoly P = trimPoly q := by
      rw [trimPoly_eq_iff_coeffAt]
      intro j
      have hj := coeffAt_pSub P q j
      rw [hd, coeffAt_nil] at hj
      exact LawfulCommRing.sub_eq_zero_iff.mp hj.symm
    rw [← hPq]
    exact hPt
  else
    have hlen := (pMul_length_of_trimmed_ne_nil (trimPoly_idem E) (UPoly.pSub_trimmed P q)
      hEne hd).1
    rw [h1] at hlen
    have hrt := trimPoly_length_le r
    have hdl : 1 ≤ (pSub P q).length := by
      cases hd' : pSub P q with
      | nil => exact absurd hd' hd
      | cons _ _ => simp only [List.length_cons]; omega
    omega

/-- **Completeness.** Inside the unique-decoding radius `k + 2 * e ≤ n`, on a domain of
    distinct points, every codeword (trimmed, at most `k` coefficients) that agrees with
    `word` on all but at most `e` points is the output of the decoder. -/
theorem wbDecode_complete [LawfulField F] [DecidableEq F] (k e : Nat) (domain : List F)
    (word : F → F) (hDom : domain.Nodup) (hRad : k + 2 * e ≤ domain.length)
    (P : List F) (hPt : IsTrimmed P) (hPk : P.length ≤ k)
    (hAgree : domain.length ≤ agreeCount word P domain + e) :
    wbDecode k e domain word = some P := by
  have hptsLen : (domain.take (k + 2 * e)).length = k + 2 * e := by
    rw [List.length_take]; omega
  have hspec : (∃ x ∈ wbKeySolution k e domain word, x ≠ zero) ∧
      ∀ row ∈ (domain.take (k + 2 * e)).map (wbRow k e word),
        dotVec row (wbKeySolution k e domain word) = zero :=
    solve_spec (k + 2 * e + 1) ((domain.take (k + 2 * e)).map (wbRow k e word))
      (by rw [List.length_map, hptsLen]; omega)
      (by
        intro row hm
        obtain ⟨x, _, rfl⟩ := List.mem_map.mp hm
        exact wbRow_length k e word x)
  have hvl : (wbKeySolution k e domain word).length = k + 2 * e + 1 := solve_length _ _
  obtain ⟨hE, hQ⟩ := key_solution_divides k e domain word hDom hRad P hPt hPk hAgree
    (wbKeySolution k e domain word) hvl hspec.1
    (fun x hx => hspec.2 _ (List.mem_map.mpr ⟨x, hx, rfl⟩))
  have hcand : wbCandidate k e domain word = P := hQ
  have h2 : ¬ (trimPoly ((wbKeySolution k e domain word).drop (k + e))).length = 0 :=
    fun h0 => hE (List.eq_nil_of_length_eq_zero h0)
  rw [wbDecode_eq, ite_eq_right (by omega : ¬ domain.length < k + 2 * e), ite_eq_right h2,
    hcand, ite_eq_right (by omega : ¬ k < P.length), ite_eq_left hAgree]

/-- **Unique decoding.** Inside the radius two codewords within distance `e` of the same
    received word are equal. -/
theorem wbDecode_unique [LawfulField F] [DecidableEq F] (k e : Nat) (domain : List F)
    (word : F → F) (hDom : domain.Nodup) (hRad : k + 2 * e ≤ domain.length)
    (P₁ P₂ : List F) (hT₁ : IsTrimmed P₁) (hT₂ : IsTrimmed P₂)
    (hK₁ : P₁.length ≤ k) (hK₂ : P₂.length ≤ k)
    (hA₁ : domain.length ≤ agreeCount word P₁ domain + e)
    (hA₂ : domain.length ≤ agreeCount word P₂ domain + e) : P₁ = P₂ :=
  Option.some.inj
    ((wbDecode_complete k e domain word hDom hRad P₁ hT₁ hK₁ hA₁).symm.trans
      (wbDecode_complete k e domain word hDom hRad P₂ hT₂ hK₂ hA₂))

/-- Inside the radius the decoder rejects exactly when no codeword is within distance `e`. -/
theorem wbDecode_eq_none_iff [LawfulField F] [DecidableEq F] (k e : Nat) (domain : List F)
    (word : F → F) (hDom : domain.Nodup) (hRad : k + 2 * e ≤ domain.length) :
    wbDecode k e domain word = none ↔
      ∀ P : List F, IsTrimmed P → P.length ≤ k →
        ¬ domain.length ≤ agreeCount word P domain + e := by
  constructor
  · intro hnone P hPt hPk hAgree
    have hsome := wbDecode_complete k e domain word hDom hRad P hPt hPk hAgree
    rw [hnone] at hsome
    exact nomatch hsome
  · intro hno
    cases hw : wbDecode k e domain word with
    | none => rfl
    | some Q =>
      obtain ⟨hQt, hQk, hQa, _⟩ := wbDecode_sound k e domain word Q hw
      exact absurd hQa (hno Q hQt hQk)

/-! ## 9. Agreement with the specification decoder `gsDecodeList` -/

/-- Inside the unique-decoding radius, membership in the specification list is the same as
    being the output of the Welch–Berlekamp decoder. The specification decoder is called with
    degree bound `d` (so `k = d + 1`) and agreement threshold `n - e`. -/
theorem mem_gsDecodeList_iff_wbDecode [LawfulField F] [DecidableEq F] (d e : Nat)
    (domain : List F) (word : F → F) (hDom : domain.Nodup)
    (hRad : d + 1 + 2 * e ≤ domain.length) (P : GsUniPoly F) :
    P ∈ gsDecodeList d (domain.length - e) domain word ↔
      wbDecode (d + 1) e domain word = some P.coeffs := by
  rw [mem_gsDecodeList_iff word hDom (by omega) P]
  constructor
  · rintro ⟨hdeg, hag⟩
    exact wbDecode_complete (d + 1) e domain word hDom hRad P.coeffs P.trimmed hdeg
      (by unfold agreeCount; omega)
  · intro h
    obtain ⟨_, hlen, hag, _⟩ := wbDecode_sound (d + 1) e domain word P.coeffs h
    unfold agreeCount at hag
    exact ⟨hlen, by omega⟩

/-- The output of `wbDecode` as a list of canonical polynomials: empty or a singleton. -/
def wbDecodeList [LawfulField F] [DecidableEq F] (d e : Nat) (domain : List F)
    (word : F → F) : List (GsUniPoly F) :=
  match wbDecode (d + 1) e domain word with
  | some Q => [GsUniPoly.ofCoeffs Q]
  | none => []

theorem eq_singleton_of_nodup {α : Type} :
    ∀ (L : List α) (a : α), L.Nodup → a ∈ L → (∀ b ∈ L, b = a) → L = [a]
  | [], _, _, hm, _ => nomatch hm
  | [b], a, _, _, hall => by rw [hall b (.head _)]
  | b :: c :: l, a, hnd, _, hall => by
    have hb := hall b (.head _)
    have hc := hall c (.tail _ (.head _))
    rcases hnd with _ | ⟨hne, _⟩
    exact absurd (hb.trans hc.symm) (hne c (.head _))

/-- **Equivalence with the specification decoder.** Inside the unique-decoding radius the
    subset-enumeration decoder `gsDecodeList` and the Welch–Berlekamp decoder return the same
    list: empty when no codeword is within distance `e`, and otherwise the one codeword. -/
theorem wbDecode_eq_unique [LawfulField F] [DecidableEq F] (d e : Nat) (domain : List F)
    (word : F → F) (hDom : domain.Nodup) (hRad : d + 1 + 2 * e ≤ domain.length) :
    gsDecodeList d (domain.length - e) domain word = wbDecodeList d e domain word := by
  have hnd := gsDecodeList_nodup d (domain.length - e) domain word
  have hmem := fun P => mem_gsDecodeList_iff_wbDecode d e domain word hDom hRad P
  unfold wbDecodeList
  cases hw : wbDecode (d + 1) e domain word with
  | none =>
    simp only
    cases hL : gsDecodeList d (domain.length - e) domain word with
    | nil => rfl
    | cons P _ =>
      have hP := (hmem P).mp (by rw [hL]; exact .head _)
      rw [hw] at hP
      exact nomatch hP
  | some Q =>
    simp only
    obtain ⟨hQt, _, _, _⟩ := wbDecode_sound (d + 1) e domain word Q hw
    have hQc : (GsUniPoly.ofCoeffs Q).coeffs = Q := GsUniPoly.ofCoeffs_coeffs_of_trimmed Q hQt
    apply eq_singleton_of_nodup _ _ hnd
    · exact (hmem _).mpr (by rw [hw, hQc])
    · intro P hP
      have hPw := (hmem P).mp hP
      rw [hw] at hPw
      apply UPoly.ext
      rw [hQc]
      exact (Option.some.inj hPw).symm

theorem wbDecodeList_of_some [LawfulField F] [DecidableEq F] (d e : Nat) (domain : List F)
    (word : F → F) (Q : List F) (h : wbDecode (d + 1) e domain word = some Q) :
    wbDecodeList d e domain word = [GsUniPoly.ofCoeffs Q] := by
  unfold wbDecodeList
  rw [h]

theorem wbDecodeList_of_none [LawfulField F] [DecidableEq F] (d e : Nat) (domain : List F)
    (word : F → F) (h : wbDecode (d + 1) e domain word = none) :
    wbDecodeList d e domain word = [] := by
  unfold wbDecodeList
  rw [h]

/-- Inside the radius the specification list has at most one element. -/
theorem gsDecodeList_length_le_one [LawfulField F] [DecidableEq F] (d e : Nat)
    (domain : List F) (word : F → F) (hDom : domain.Nodup)
    (hRad : d + 1 + 2 * e ≤ domain.length) :
    (gsDecodeList d (domain.length - e) domain word).length ≤ 1 := by
  rw [wbDecode_eq_unique d e domain word hDom hRad]
  unfold wbDecodeList
  cases wbDecode (d + 1) e domain word with
  | none => exact Nat.zero_le 1
  | some Q => exact Nat.le_refl 1

/-! ## 10. Operation count -/

theorem wb_cost_arith (m n c1 c2 c3 c4 c5 c6 : Nat) (hm : m ≤ n)
    (h1 : c1 ≤ m * (m + 2)) (h2 : c2 ≤ (m + 1) * (m * (2 * m + 2) + 2 * m + 3))
    (h3 : c3 ≤ m + 1) (h4 : c4 ≤ m * (2 * (m + 1) + 1)) (h5 : c5 ≤ m)
    (h6 : c6 ≤ n * (2 * m + 1)) :
    c1 + c2 + c3 + 1 + c4 + c5 + c6 ≤ wbOpBound n := by
  unfold wbOpBound
  have hm2 : m + 2 ≤ n + 2 := by omega
  have hn : n ≤ n + 2 := by omega
  generalize n + 2 = s at hm2 hn ⊢
  have eA : (m + 2) * (m + 2) = m * (m + 2) + 2 * (m + 2) := Nat.add_mul m 2 (m + 2)
  have lA : (m + 2) * (m + 2) ≤ s * s := Nat.mul_le_mul hm2 hm2
  have eB : (m + 2) * (2 * m + 2) = m * (2 * m + 2) + 2 * (2 * m + 2) :=
    Nat.add_mul m 2 (2 * m + 2)
  have lB : (m + 2) * (2 * m + 2) ≤ s * (2 * s) := Nat.mul_le_mul hm2 (by omega)
  have e2 : s * (2 * s) = 2 * (s * s) := Nat.mul_left_comm s 2 s
  have lB2 : (m + 1) * (m * (2 * m + 2) + 2 * m + 3) ≤ s * (2 * (s * s)) :=
    Nat.mul_le_mul (by omega) (by omega)
  have lC : m * (2 * (m + 1) + 1) ≤ s * (2 * s) := Nat.mul_le_mul (by omega) (by omega)
  have lD : n * (2 * m + 1) ≤ s * (2 * s) := Nat.mul_le_mul hn (by omega)
  have e3 : s * (2 * (s * s)) = 2 * (s * (s * s)) := Nat.mul_left_comm s 2 (s * s)
  have p3 : s ^ 3 = s * (s * s) := by
    rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_assoc]
  have p2 : s ^ 2 = s * s := by
    rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
  rw [p3, p2]
  omega

theorem Tick.cost_ite {α : Type} (c : Prop) [Decidable c] (a b : Tick α) :
    (if c then a else b).cost = if c then a.cost else b.cost := by
  split <;> rfl

/-- **Explicit polynomial operation count.** For every field, every `k`, `e`, every domain of
    `n` points and every received word, the decoder performs at most
    `2 * (n + 2) ^ 3 + 5 * (n + 2) ^ 2` field operations (additions, subtractions,
    multiplications, negations, inversions and equality tests). The bound does not mention
    the field. -/
theorem wbDecode_ops_poly [LawfulField F] [DecidableEq F] (k e : Nat) (domain : List F)
    (word : F → F) : (wbDecodeT k e domain word).cost ≤ wbOpBound domain.length := by
  unfold wbDecodeT
  if h1 : domain.length < k + 2 * e then
    rw [ite_eq_left h1]
    exact Nat.zero_le _
  else
    rw [ite_eq_right h1]
    have hptsLen : (domain.take (k + 2 * e)).length = k + 2 * e := by
      rw [List.length_take]; omega
    have c1 : (mapT (wbRowT k e word) (domain.take (k + 2 * e))).cost ≤
        (k + 2 * e) * (k + 2 * e + 2) := by
      have := cost_mapT_le (wbRowT k e word) (k + 2 * e + 2) (domain.take (k + 2 * e))
        (fun x _ => by rw [cost_wbRowT]; exact Nat.le_refl _)
      rwa [hptsLen] at this
    have c2 := cost_solveT_le (k + 2 * e) (k + 2 * e) (k + 2 * e + 1)
      ((domain.take (k + 2 * e)).map (wbRow k e word)) (Nat.le_refl _)
      (by rw [List.length_map, hptsLen]; exact Nat.le_refl _)
      (by
        intro row hm
        obtain ⟨x, _, rfl⟩ := List.mem_map.mp hm
        rw [wbRow_length]; exact Nat.le_refl _)
    have hvl : (solve (k + 2 * e + 1) ((domain.take (k + 2 * e)).map (wbRow k e word))).length
        = k + 2 * e + 1 := solve_length _ _
    simp only [Tick.cost_bind, Tick.cost_ite, Tick.cost_pure, val_wbRows, val_solveT,
      val_trimT, val_tInv, cost_tInv, val_divT, cost_countAgreeT]
    generalize solve (k + 2 * e + 1) ((domain.take (k + 2 * e)).map (wbRow k e word)) = v
      at hvl ⊢
    generalize LawfulField.inv (coeffAt (trimPoly (v.drop (k + e)))
      ((trimPoly (v.drop (k + e))).length - 1)) = bi
    have c3 : (trimT (v.drop (k + e))).cost ≤ k + 2 * e + 1 := by
      have := cost_trimT_le (v.drop (k + e))
      rw [List.length_drop] at this
      omega
    have hNl : (v.take (k + e)).length ≤ k + 2 * e := by rw [List.length_take]; omega
    have c4 : (divT (trimPoly (v.drop (k + e))) bi (v.take (k + e))).cost ≤
        (k + 2 * e) * (2 * (k + 2 * e + 1) + 1) := by
      have hEl := trimPoly_length_le (v.drop (k + e))
      rw [List.length_drop] at hEl
      exact Nat.le_trans (cost_divT_le _ _ _) (Nat.mul_le_mul hNl (by omega))
    have hql : (divRaw (trimPoly (v.drop (k + e))) bi (v.take (k + e))).1.length ≤
        k + 2 * e := by rw [divRaw_fst_length]; exact hNl
    have c5 : (trimT (divRaw (trimPoly (v.drop (k + e))) bi (v.take (k + e))).1).cost ≤
        k + 2 * e := Nat.le_trans (cost_trimT_le _) hql
    have hqt : (trimPoly (divRaw (trimPoly (v.drop (k + e))) bi (v.take (k + e))).1).length ≤
        k + 2 * e := Nat.le_trans (trimPoly_length_le _) hql
    have c6 : domain.length *
        (2 * (trimPoly (divRaw (trimPoly (v.drop (k + e))) bi (v.take (k + e))).1).length + 1)
        ≤ domain.length * (2 * (k + 2 * e) + 1) := Nat.mul_le_mul (Nat.le_refl _) (by omega)
    have hbase := fun c4' c5' c6' h4 h5 h6 =>
      wb_cost_arith (k + 2 * e) domain.length _ _ _ c4' c5' c6' (by omega) c1 c2 c3 h4 h5 h6
    split
    · have := hbase 0 0 0 (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
      omega
    · split
      · have := hbase _ _ 0 c4 c5 (Nat.zero_le _)
        omega
      · have := hbase _ _ _ c4 c5 c6
        split <;> omega

/-! ## 11. Worked examples over the seven-element field

`F7` exists only so that the decoder can be run by the kernel on concrete words. The facts
below are evaluated here, where the definitions are visible, and cited by
`Qsag.Tests.WelchBerlekampTeeth`. -/

/-- The prime field with seven elements. -/
structure F7 where
  v : Fin 7
  deriving DecidableEq

namespace F7

/-- The residue of `n` modulo seven. -/
def ofNat (n : Nat) : F7 := ⟨⟨n % 7, Nat.mod_lt n (by decide)⟩⟩

/-- Inverse by Fermat: `a⁻¹ = a⁵`. -/
def inv7 (a : Fin 7) : Fin 7 := a * a * a * a * a

instance : CommRingOps F7 where
  zero := ⟨0⟩
  one := ⟨1⟩
  add a b := ⟨a.v + b.v⟩
  mul a b := ⟨a.v * b.v⟩
  neg a := ⟨-a.v⟩
  sub a b := ⟨a.v - b.v⟩

theorem fin_add_assoc : ∀ a b c : Fin 7, a + b + c = a + (b + c) := by decide
theorem fin_add_comm : ∀ a b : Fin 7, a + b = b + a := by decide
theorem fin_zero_add : ∀ a : Fin 7, 0 + a = a := by decide
theorem fin_add_zero : ∀ a : Fin 7, a + 0 = a := by decide
theorem fin_add_left_neg : ∀ a : Fin 7, -a + a = 0 := by decide
theorem fin_sub_eq : ∀ a b : Fin 7, a - b = a + -b := by decide
theorem fin_mul_assoc : ∀ a b c : Fin 7, a * b * c = a * (b * c) := by decide
theorem fin_mul_comm : ∀ a b : Fin 7, a * b = b * a := by decide
theorem fin_one_mul : ∀ a : Fin 7, 1 * a = a := by decide
theorem fin_mul_one : ∀ a : Fin 7, a * 1 = a := by decide
theorem fin_left_distrib : ∀ a b c : Fin 7, a * (b + c) = a * b + a * c := by decide
theorem fin_right_distrib : ∀ a b c : Fin 7, (a + b) * c = a * c + b * c := by decide
theorem fin_mul_inv : ∀ a : Fin 7, a ≠ 0 → a * inv7 a = 1 := by decide

instance : LawfulCommRing F7 where
  add_assoc a b c := congrArg F7.mk (fin_add_assoc a.v b.v c.v)
  add_comm a b := congrArg F7.mk (fin_add_comm a.v b.v)
  zero_add a := congrArg F7.mk (fin_zero_add a.v)
  add_zero a := congrArg F7.mk (fin_add_zero a.v)
  add_left_neg a := congrArg F7.mk (fin_add_left_neg a.v)
  sub_eq_add_neg a b := congrArg F7.mk (fin_sub_eq a.v b.v)
  mul_assoc a b c := congrArg F7.mk (fin_mul_assoc a.v b.v c.v)
  mul_comm a b := congrArg F7.mk (fin_mul_comm a.v b.v)
  one_mul a := congrArg F7.mk (fin_one_mul a.v)
  mul_one a := congrArg F7.mk (fin_mul_one a.v)
  left_distrib a b c := congrArg F7.mk (fin_left_distrib a.v b.v c.v)
  right_distrib a b c := congrArg F7.mk (fin_right_distrib a.v b.v c.v)

instance : LawfulField F7 where
  inv a := ⟨inv7 a.v⟩
  zero_ne_one := by decide
  inv_zero := by decide
  mul_inv_cancel {a} ha :=
    congrArg F7.mk (fin_mul_inv a.v (fun h => ha (congrArg F7.mk h)))

/-- The list of residues of a list of naturals. -/
def ofNats (ns : List Nat) : List F7 := ns.map ofNat

/-- A received word given by its table of values at the points `0, 1, 2, …`. -/
def tableWord (ys : List Nat) (x : F7) : F7 := ofNat (ys.getD x.v.val 0)

end F7

/-- Six evaluation points `0, …, 5` of `F7`. -/
def exDomain6 : List F7 := F7.ofNats [0, 1, 2, 3, 4, 5]

/-- Five evaluation points `0, …, 4` of `F7`. -/
def exDomain5 : List F7 := F7.ofNats [0, 1, 2, 3, 4]

/-- The codeword `3 + 2 X`; its values on `0, …, 5` are `3, 5, 0, 2, 4, 6`. -/
def exCodeword : List F7 := F7.ofNats [3, 2]

/-- `exCodeword` with the values at `1` and `4` corrupted. -/
def exWordTwoErrors : F7 → F7 := F7.tableWord [3, 0, 0, 2, 1, 6]

/-- `exCodeword` with the values at `1`, `4` and `5` corrupted. -/
def exWordThreeErrors : F7 → F7 := F7.tableWord [3, 0, 0, 2, 1, 0]

/-- A word on five points at distance two from both `3 + 2 X` and the zero codeword. -/
def exWordAmbiguous : F7 → F7 := F7.tableWord [3, 5, 0, 0, 0]

theorem exDomain6_nodup : exDomain6.Nodup := by decide
theorem exDomain5_nodup : exDomain5.Nodup := by decide
theorem exDomain6_length : exDomain6.length = 6 := by decide
theorem exDomain5_length : exDomain5.length = 5 := by decide
theorem exCodeword_trimmed : IsTrimmed exCodeword := by
  show trimPoly exCodeword = exCodeword
  decide
theorem exCodeword_length : exCodeword.length = 2 := by decide
theorem exCodeword_ne_nil : ¬ (exCodeword = []) := by decide

/-- Two corrupted values out of six leave four agreements. -/
theorem exWordTwoErrors_agree : agreeCount exWordTwoErrors exCodeword exDomain6 = 4 := by
  decide +kernel

/-- Three corrupted values out of six leave three agreements. -/
theorem exWordThreeErrors_agree : agreeCount exWordThreeErrors exCodeword exDomain6 = 3 := by
  decide +kernel

/-- **Corruption recovery.** With `n = 6`, `k = 2`, `e = 2` the decoder returns `3 + 2 X` from
    a word with two corrupted values. -/
theorem exWordTwoErrors_decodes : wbDecode 2 2 exDomain6 exWordTwoErrors = some exCodeword := by
  decide +kernel

/-- **Rejection beyond the radius.** Three corrupted values are more than `e = 2`: the decoder
    rejects. -/
theorem exWordThreeErrors_rejected : wbDecode 2 2 exDomain6 exWordThreeErrors = none := by
  decide +kernel

/-- The counter on the recovery run. -/
theorem exWordTwoErrors_cost : (wbDecodeT 2 2 exDomain6 exWordTwoErrors).cost = 332 := by
  decide +kernel

theorem exWordAmbiguous_agree :
    agreeCount exWordAmbiguous exCodeword exDomain5 = 3 ∧
    agreeCount exWordAmbiguous [] exDomain5 = 3 := by
  decide +kernel

/-- Premises of `wbDecode_complete` hold together on the recovery example. -/
theorem wbDecode_complete_inhabited :
    ∃ (domain : List F7) (word : F7 → F7) (P : List F7) (k e : Nat),
      domain.Nodup ∧ k + 2 * e ≤ domain.length ∧ IsTrimmed P ∧ P.length ≤ k ∧
      domain.length ≤ agreeCount word P domain + e :=
  ⟨exDomain6, exWordTwoErrors, exCodeword, 2, 2, exDomain6_nodup, by decide,
    exCodeword_trimmed, by decide, by decide +kernel⟩

/-- **Tooth: the radius hypothesis of `wbDecode_complete` is needed.** On five points with
    `k = 2`, `e = 2` (so `k + 2 * e = 6 > 5`) the codeword `3 + 2 X` is within distance two of
    the word and the decoder still rejects. -/
theorem tooth_complete_needs_radius :
    ∃ P : List F7, IsTrimmed P ∧ P.length ≤ 2 ∧
      exDomain5.length ≤ agreeCount exWordAmbiguous P exDomain5 + 2 ∧
      wbDecode 2 2 exDomain5 exWordAmbiguous = none :=
  ⟨exCodeword, exCodeword_trimmed, by decide, by decide +kernel,
    wbDecode_none_of_short 2 2 exDomain5 exWordAmbiguous (by decide)⟩

/-- **Tooth: unique decoding fails beyond the radius.** The same word is within distance two
    of two different codewords, `3 + 2 X` and `0`. -/
theorem tooth_unique_needs_radius :
    ∃ P₁ P₂ : List F7, ¬ (P₁ = P₂) ∧ IsTrimmed P₁ ∧ IsTrimmed P₂ ∧
      P₁.length ≤ 2 ∧ P₂.length ≤ 2 ∧
      exDomain5.length ≤ agreeCount exWordAmbiguous P₁ exDomain5 + 2 ∧
      exDomain5.length ≤ agreeCount exWordAmbiguous P₂ exDomain5 + 2 :=
  ⟨exCodeword, [], exCodeword_ne_nil, exCodeword_trimmed, by rfl, by decide, by decide,
    by decide +kernel, by decide +kernel⟩

/-- **Tooth: the decoder is not the identity on its candidate.** A word with three corrupted
    values has no codeword within distance two, so soundness has nothing to accept. -/
theorem tooth_no_codeword_beyond_radius :
    ¬ ∃ Q : List F7, wbDecode 2 2 exDomain6 exWordThreeErrors = some Q := by
  rw [exWordThreeErrors_rejected]
  exact fun ⟨_, h⟩ => nomatch h

/-- **Tooth: the counter counts.** The recovery run is charged more than zero operations. -/
theorem tooth_counter_is_live : ¬ ((wbDecodeT 2 2 exDomain6 exWordTwoErrors).cost = 0) := by
  rw [exWordTwoErrors_cost]
  decide

/-- The recovery run uses 332 operations against a bound of 1344 for six points. -/
theorem exWordTwoErrors_cost_lt_bound :
    (wbDecodeT 2 2 exDomain6 exWordTwoErrors).cost < wbOpBound exDomain6.length := by
  rw [exWordTwoErrors_cost]
  decide

/-- **Tooth: the equivalence with `gsDecodeList` needs the radius.** On five points with
    `d = 1`, `e = 2` the specification list contains `3 + 2 X` while the Welch–Berlekamp list
    is empty. -/
theorem tooth_spec_equivalence_needs_radius :
    ∃ P : GsUniPoly F7,
      P ∈ gsDecodeList 1 (exDomain5.length - 2) exDomain5 exWordAmbiguous ∧
      wbDecodeList 1 2 exDomain5 exWordAmbiguous = [] := by
  refine ⟨GsUniPoly.ofCoeffs exCodeword, ?_, ?_⟩
  · have hc : (GsUniPoly.ofCoeffs exCodeword).coeffs = exCodeword :=
      GsUniPoly.ofCoeffs_coeffs_of_trimmed exCodeword exCodeword_trimmed
    apply (mem_gsDecodeList_iff exWordAmbiguous exDomain5_nodup (by decide) _).mpr
    rw [hc]
    have ha : agreeCount exWordAmbiguous exCodeword exDomain5 = 3 := exWordAmbiguous_agree.1
    unfold agreeCount at ha
    rw [ha]
    decide
  · unfold wbDecodeList
    rw [wbDecode_none_of_short 2 2 exDomain5 exWordAmbiguous (by decide)]

/-- On the recovery example the Welch–Berlekamp list is the one codeword. -/
theorem exWordTwoErrors_decodeList :
    wbDecodeList 1 2 exDomain6 exWordTwoErrors = [GsUniPoly.ofCoeffs exCodeword] := by
  unfold wbDecodeList
  rw [exWordTwoErrors_decodes]

/-- Premises of `wbDecode_eq_unique` hold together on the recovery example. -/
theorem wbDecode_eq_unique_inhabited :
    ∃ (domain : List F7) (word : F7 → F7) (d e : Nat),
      domain.Nodup ∧ d + 1 + 2 * e ≤ domain.length ∧
      wbDecodeList d e domain word = [GsUniPoly.ofCoeffs exCodeword] :=
  ⟨exDomain6, exWordTwoErrors, 1, 2, exDomain6_nodup, by decide, exWordTwoErrors_decodeList⟩

/-! ## Audits -/

#verify_constructive solve_spec
#verify_constructive cost_solveT_le
#verify_constructive divRaw_spec
#verify_constructive key_solution_divides
#verify_constructive wbDecode_eq
#verify_constructive wbDecode_sound
#verify_constructive wbDecode_none_of_short
#verify_constructive wbDecode_complete
#verify_constructive wbDecode_unique
#verify_constructive wbDecode_eq_none_iff
#verify_constructive mem_gsDecodeList_iff_wbDecode
#verify_constructive wbDecode_eq_unique
#verify_constructive gsDecodeList_length_le_one
#verify_constructive wb_cost_arith
#verify_constructive wbDecode_ops_poly
#verify_constructive exWordTwoErrors_decodes exWordThreeErrors_rejected exWordTwoErrors_cost
#verify_constructive exWordTwoErrors_agree exWordThreeErrors_agree exWordAmbiguous_agree
#verify_constructive exWordTwoErrors_cost_lt_bound
#verify_inhabited wbDecode_complete wbDecode_complete_inhabited
#verify_inhabited wbDecode_eq_unique wbDecode_eq_unique_inhabited
#tooth_pair wbDecode_complete vs tooth_complete_needs_radius
#tooth_pair wbDecode_unique vs tooth_unique_needs_radius
#tooth_pair wbDecode_sound vs tooth_no_codeword_beyond_radius
#tooth_pair wbDecode_eq_unique vs tooth_spec_equivalence_needs_radius
#tooth_pair wbDecode_ops_poly vs tooth_counter_is_live

end WelchBerlekamp
end Qsag
