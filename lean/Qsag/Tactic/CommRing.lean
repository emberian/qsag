module
/-
# Qsag.Tactic.ConstructiveRing — reflective commutative-ring normalizer without choice

`constructive_ring` proves universal polynomial identities over any `[LawfulCommRing R]`.
It reifies both sides into `CRingExpr`, normalizes `lhs - rhs` to a sparse polynomial with
sorted monomials (`normExpr`), and closes the goal by kernel reduction of `normExpr … = []`
through `eq_of_normSub_nil`. The proof term mentions only `propext` and `Quot.sound`.

Coefficients are pairs `(p, n)` of naturals denoting `p - n`. This keeps every coefficient
law a statement about `natCast` on `Nat`, so no integer homomorphism is needed; a term is
dropped exactly when `p = n`.

Recognized syntax: `CommRingOps.add/mul/neg/sub/zero/one`, and, under
`open scoped Qsag.CRing`, the notations `a + b`, `a - b`, `a * b`, `-a`, `a ^ k` and numerals.
Everything else is an atom. For identities modulo hypotheses `pᵢ = 0`, prove
`lhs - rhs = c₁ * p₁ + …` with `constructive_ring`, rewrite the hypotheses, and finish with
`eq_of_sub_eq_zero`.
-/

public import Qsag.Spec.Algebra
public import Qsag.Tactic.Prelude
public meta import Lean

public section
namespace Qsag

set_option autoImplicit false

namespace CRing
variable {R : Type}
open CommRingOps

/-- The canonical image of a natural number; `natCast 1` is `one` on the nose. -/
@[expose] def natCast [CommRingOps R] : Nat → R
  | 0 => zero
  | 1 => one
  | n + 2 => add (natCast (n + 1)) one

/-- Natural-number power by repeated right multiplication. -/
@[expose] def npow [CommRingOps R] (a : R) : Nat → R
  | 0 => one
  | k + 1 => mul (npow a k) a

scoped instance (priority := low) instAdd [CommRingOps R] : Add R := ⟨add⟩
scoped instance (priority := low) instMul [CommRingOps R] : Mul R := ⟨mul⟩
scoped instance (priority := low) instNeg [CommRingOps R] : Neg R := ⟨neg⟩
scoped instance (priority := low) instSub [CommRingOps R] : Sub R := ⟨sub⟩
scoped instance (priority := low) instPow [CommRingOps R] : HPow R Nat R := ⟨npow⟩
scoped instance (priority := low) instOfNat [CommRingOps R] (n : Nat) : OfNat R n := ⟨natCast n⟩

end CRing

/-- Reflected ring expressions over atoms indexed by `Nat`. -/
inductive CRingExpr where
  | var (i : Nat)
  | lit (n : Nat)
  | add (a b : CRingExpr)
  | sub (a b : CRingExpr)
  | mul (a b : CRingExpr)
  | neg (a : CRingExpr)
  | pow (a : CRingExpr) (k : Nat)

/-- Sparse polynomials: `(monomial, p, n)` denotes `(p - n) · monomial`, where a monomial is
    the ascending list of its variable indices with repetition. -/
abbrev CMvPoly := List (List Nat × Nat × Nat)

namespace CRingExpr

/-- Interpretation in a ring under the atom valuation `ρ`. -/
@[expose] def eval {R : Type} [CommRingOps R] (e : CRingExpr) (ρ : Nat → R) : R :=
  match e with
  | var i => ρ i
  | lit n => CRing.natCast n
  | add a b => CommRingOps.add (a.eval ρ) (b.eval ρ)
  | sub a b => CommRingOps.sub (a.eval ρ) (b.eval ρ)
  | mul a b => CommRingOps.mul (a.eval ρ) (b.eval ρ)
  | neg a => CommRingOps.neg (a.eval ρ)
  | pow a k => CRing.npow (a.eval ρ) k

end CRingExpr

namespace CMvPoly

/-- Insert a variable into an ascending monomial. -/
@[expose] def insVar (v : Nat) : List Nat → List Nat
  | [] => [v]
  | w :: ws => bif Nat.ble v w then v :: w :: ws else w :: insVar v ws

/-- Product of monomials. -/
@[expose] def monMul : List Nat → List Nat → List Nat
  | [], b => b
  | v :: a, b => insVar v (monMul a b)

/-- Lexicographic comparison of monomials. -/
@[expose] def monCmp : List Nat → List Nat → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs =>
    bif Nat.blt a b then .lt else bif Nat.blt b a then .gt else monCmp as bs

/-- Add the term `(p - n) · m` into a sorted polynomial, merging and dropping zeros. -/
@[expose] def addTerm (m : List Nat) (p n : Nat) : CMvPoly → CMvPoly
  | [] => bif Nat.beq p n then [] else [(m, p, n)]
  | (m', p', n') :: rest =>
    match monCmp m m' with
    | .lt => bif Nat.beq p n then (m', p', n') :: rest else (m, p, n) :: (m', p', n') :: rest
    | .eq => bif Nat.beq (p + p') (n + n') then rest else (m', p + p', n + n') :: rest
    | .gt => (m', p', n') :: addTerm m p n rest

@[expose] def polyAdd : CMvPoly → CMvPoly → CMvPoly
  | [], q => q
  | (m, p, n) :: rest, q => addTerm m p n (polyAdd rest q)

/-- `mulTerm m p n q acc = acc + (p - n) · m · q`. -/
@[expose] def mulTerm (m : List Nat) (p n : Nat) : CMvPoly → CMvPoly → CMvPoly
  | [], acc => acc
  | (m', p', n') :: rest, acc =>
    addTerm (monMul m m') (p * p' + n * n') (p * n' + n * p') (mulTerm m p n rest acc)

@[expose] def polyMul : CMvPoly → CMvPoly → CMvPoly
  | [], _ => []
  | (m, p, n) :: rest, q => mulTerm m p n q (polyMul rest q)

@[expose] def polyPow (p : CMvPoly) : Nat → CMvPoly
  | 0 => [([], 1, 0)]
  | k + 1 => polyMul (polyPow p k) p

end CMvPoly

/-- Normal form of a reflected expression. -/
@[expose] def normExpr : CRingExpr → CMvPoly
  | .var i => [([i], 1, 0)]
  | .lit n => CMvPoly.addTerm [] n 0 []
  | .add a b => CMvPoly.polyAdd (normExpr a) (normExpr b)
  | .sub a b => CMvPoly.mulTerm [] 0 1 (normExpr b) (normExpr a)
  | .mul a b => CMvPoly.polyMul (normExpr a) (normExpr b)
  | .neg a => CMvPoly.mulTerm [] 0 1 (normExpr a) []
  | .pow a k => CMvPoly.polyPow (normExpr a) k

/-! ## Soundness -/

namespace CRing
variable {R : Type} [LawfulCommRing R]
open CommRingOps LawfulCommRing

private local instance : Std.Associative (α := R) add := ⟨add_assoc⟩
private local instance : Std.Commutative (α := R) add := ⟨add_comm⟩
private local instance : Std.Associative (α := R) mul := ⟨mul_assoc⟩
private local instance : Std.Commutative (α := R) mul := ⟨mul_comm⟩

theorem natCast_succ (n : Nat) : (natCast (n + 1) : R) = add (natCast n) one := by
  cases n with
  | zero => exact (zero_add _).symm
  | succ n => rfl

theorem natCast_add (a : Nat) : ∀ b : Nat, (natCast (a + b) : R) = add (natCast a) (natCast b)
  | 0 => (add_zero _).symm
  | b + 1 => by
    rw [← Nat.add_assoc, natCast_succ, natCast_succ, natCast_add a b, add_assoc]

theorem natCast_mul (a : Nat) : ∀ b : Nat, (natCast (a * b) : R) = mul (natCast a) (natCast b)
  | 0 => (mul_zero _).symm
  | b + 1 => by
    rw [Nat.mul_succ, natCast_add, natCast_mul a b, natCast_succ, left_distrib, mul_one]

theorem npow_add (a : R) (j : Nat) : ∀ k : Nat, npow a (j + k) = mul (npow a j) (npow a k)
  | 0 => (mul_one _).symm
  | k + 1 => by
    rw [← Nat.add_assoc]
    change mul (npow a (j + k)) a = mul (npow a j) (mul (npow a k) a)
    rw [npow_add a j k, mul_assoc]

/-- The value `p - n` of a coefficient pair. -/
def coeff (p n : Nat) : R := sub (natCast p) (natCast n)

private theorem sub_add_sub (a b c d : R) :
    add (sub a b) (sub c d) = sub (add a c) (add b d) := by
  apply add_left_cancel (a := add b d)
  rw [add_sub_cancel_left]
  have h1 : add b (sub a b) = a := add_sub_cancel_left b a
  have h2 : add d (sub c d) = c := add_sub_cancel_left d c
  calc add (add b d) (add (sub a b) (sub c d))
      = add (add b (sub a b)) (add d (sub c d)) := by ac_rfl
    _ = add a c := by rw [h1, h2]

private theorem neg_add (a b : R) : neg (add a b) = add (neg a) (neg b) := by
  apply add_left_cancel (a := add a b)
  rw [add_right_neg]
  calc zero = add (add a (neg a)) (add b (neg b)) := by
        rw [add_right_neg, add_right_neg, add_zero]
    _ = add (add a b) (add (neg a) (neg b)) := by ac_rfl

theorem coeff_eq_zero {p n : Nat} (h : Nat.beq p n = true) : (coeff p n : R) = zero := by
  have : p = n := Nat.eq_of_beq_eq_true h
  subst this
  exact sub_self _

theorem coeff_add (p n p' n' : Nat) :
    (coeff (p + p') (n + n') : R) = add (coeff p n) (coeff p' n') := by
  unfold coeff
  rw [natCast_add, natCast_add, sub_add_sub]

theorem coeff_mul (p n p' n' : Nat) :
    (coeff (p * p' + n * n') (p * n' + n * p') : R) = mul (coeff p n) (coeff p' n') := by
  unfold coeff
  rw [natCast_add, natCast_add, natCast_mul, natCast_mul, natCast_mul, natCast_mul]
  generalize (natCast p : R) = a
  generalize (natCast n : R) = b
  generalize (natCast p' : R) = c
  generalize (natCast n' : R) = d
  rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, right_distrib, left_distrib, left_distrib,
    neg_add, mul_neg, neg_mul, neg_mul, mul_neg, neg_neg]
  ac_rfl

end CRing

namespace CMvPoly
variable {R : Type} [LawfulCommRing R]
open CommRingOps LawfulCommRing CRing

private local instance : Std.Associative (α := R) add := ⟨add_assoc⟩
private local instance : Std.Commutative (α := R) add := ⟨add_comm⟩
private local instance : Std.Associative (α := R) mul := ⟨mul_assoc⟩
private local instance : Std.Commutative (α := R) mul := ⟨mul_comm⟩

/-- Value of a monomial. -/
def monDenote (ρ : Nat → R) : List Nat → R
  | [] => one
  | v :: vs => mul (ρ v) (monDenote ρ vs)

/-- Value of a sparse polynomial. -/
def denote (ρ : Nat → R) : CMvPoly → R
  | [] => zero
  | (m, p, n) :: rest => add (mul (coeff p n) (monDenote ρ m)) (denote ρ rest)

theorem insVar_denote (ρ : Nat → R) (v : Nat) :
    ∀ m : List Nat, monDenote ρ (insVar v m) = mul (ρ v) (monDenote ρ m)
  | [] => rfl
  | w :: ws => by
    unfold insVar
    cases Nat.ble v w with
    | true => rfl
    | false =>
      change mul (ρ w) (monDenote ρ (insVar v ws)) = mul (ρ v) (mul (ρ w) (monDenote ρ ws))
      rw [insVar_denote ρ v ws]
      ac_rfl

theorem monMul_denote (ρ : Nat → R) :
    ∀ a b : List Nat, monDenote ρ (monMul a b) = mul (monDenote ρ a) (monDenote ρ b)
  | [], b => (one_mul _).symm
  | v :: a, b => by
    change monDenote ρ (insVar v (monMul a b)) = mul (mul (ρ v) (monDenote ρ a)) (monDenote ρ b)
    rw [insVar_denote, monMul_denote ρ a b, mul_assoc]

theorem monCmp_eq : ∀ a b : List Nat, monCmp a b = .eq → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | a :: as, b :: bs, h => by
    unfold monCmp at h
    cases hab : Nat.blt a b with
    | true => rw [hab] at h; cases h
    | false =>
      cases hba : Nat.blt b a with
      | true => rw [hab, hba] at h; cases h
      | false =>
        rw [hab, hba] at h
        have h1 : ¬ a < b := fun hlt => by
          have := Nat.blt_eq.mpr hlt
          rw [hab] at this; cases this
        have h2 : ¬ b < a := fun hlt => by
          have := Nat.blt_eq.mpr hlt
          rw [hba] at this; cases this
        have hEq : a = b := by omega
        rw [hEq, monCmp_eq as bs h]

theorem addTerm_denote (ρ : Nat → R) (m : List Nat) (p n : Nat) :
    ∀ q : CMvPoly, denote ρ (addTerm m p n q) = add (mul (coeff p n) (monDenote ρ m)) (denote ρ q)
  | [] => by
    unfold addTerm
    cases h : Nat.beq p n with
    | true =>
      change zero = add (mul (coeff p n) (monDenote ρ m)) zero
      rw [coeff_eq_zero h, zero_mul, add_zero]
    | false => rfl
  | (m', p', n') :: rest => by
    unfold addTerm
    cases hc : monCmp m m' with
    | lt =>
      cases h : Nat.beq p n with
      | true =>
        change denote ρ ((m', p', n') :: rest) = _
        rw [coeff_eq_zero h, zero_mul, zero_add]
      | false => rfl
    | eq =>
      have hm := monCmp_eq m m' hc
      subst hm
      cases h : Nat.beq (p + p') (n + n') with
      | true =>
        change denote ρ rest =
          add (mul (coeff p n) (monDenote ρ m))
            (add (mul (coeff p' n') (monDenote ρ m)) (denote ρ rest))
        rw [← add_assoc, ← right_distrib, ← coeff_add, coeff_eq_zero h, zero_mul, zero_add]
      | false =>
        change add (mul (coeff (p + p') (n + n')) (monDenote ρ m)) (denote ρ rest) =
          add (mul (coeff p n) (monDenote ρ m))
            (add (mul (coeff p' n') (monDenote ρ m)) (denote ρ rest))
        rw [coeff_add, right_distrib, add_assoc]
    | gt =>
      change add (mul (coeff p' n') (monDenote ρ m')) (denote ρ (addTerm m p n rest)) =
        add (mul (coeff p n) (monDenote ρ m))
          (add (mul (coeff p' n') (monDenote ρ m')) (denote ρ rest))
      rw [addTerm_denote ρ m p n rest]
      ac_rfl

theorem polyAdd_denote (ρ : Nat → R) :
    ∀ a b : CMvPoly, denote ρ (polyAdd a b) = add (denote ρ a) (denote ρ b)
  | [], b => (zero_add _).symm
  | (m, p, n) :: rest, b => by
    change denote ρ (addTerm m p n (polyAdd rest b)) =
      add (add (mul (coeff p n) (monDenote ρ m)) (denote ρ rest)) (denote ρ b)
    rw [addTerm_denote, polyAdd_denote ρ rest b, add_assoc]

theorem mulTerm_denote (ρ : Nat → R) (m : List Nat) (p n : Nat) :
    ∀ q acc : CMvPoly, denote ρ (mulTerm m p n q acc) =
      add (mul (mul (coeff p n) (monDenote ρ m)) (denote ρ q)) (denote ρ acc)
  | [], acc => by
    change denote ρ acc = add (mul _ zero) (denote ρ acc)
    rw [mul_zero, zero_add]
  | (m', p', n') :: rest, acc => by
    change denote ρ (addTerm (monMul m m') (p * p' + n * n') (p * n' + n * p')
        (mulTerm m p n rest acc)) =
      add (mul (mul (coeff p n) (monDenote ρ m))
        (add (mul (coeff p' n') (monDenote ρ m')) (denote ρ rest))) (denote ρ acc)
    rw [addTerm_denote, mulTerm_denote ρ m p n rest acc, coeff_mul, monMul_denote, left_distrib]
    ac_rfl

theorem polyMul_denote (ρ : Nat → R) :
    ∀ a b : CMvPoly, denote ρ (polyMul a b) = mul (denote ρ a) (denote ρ b)
  | [], b => (zero_mul _).symm
  | (m, p, n) :: rest, b => by
    change denote ρ (mulTerm m p n b (polyMul rest b)) =
      mul (add (mul (coeff p n) (monDenote ρ m)) (denote ρ rest)) (denote ρ b)
    rw [mulTerm_denote, polyMul_denote ρ rest b, right_distrib]

theorem polyPow_denote (ρ : Nat → R) (a : CMvPoly) :
    ∀ k : Nat, denote ρ (polyPow a k) = npow (denote ρ a) k
  | 0 => by
    change add (mul (coeff 1 0) one) zero = one
    rw [add_zero, mul_one]
    exact sub_zero _
  | k + 1 => by
    change denote ρ (polyMul (polyPow a k) a) = mul (npow (denote ρ a) k) (denote ρ a)
    rw [polyMul_denote, polyPow_denote ρ a k]

end CMvPoly

open CommRingOps LawfulCommRing CRing CMvPoly in
/-- The normal form has the same value as the expression. -/
theorem denote_normExpr {R : Type} [LawfulCommRing R] (ρ : Nat → R) :
    ∀ e : CRingExpr, denote ρ (normExpr e) = e.eval ρ
  | .var i => by
    change add (mul (coeff 1 0) (mul (ρ i) one)) zero = ρ i
    rw [add_zero, mul_one]
    change mul (sub one zero) (ρ i) = ρ i
    rw [sub_zero, one_mul]
  | .lit n => by
    change denote ρ (addTerm [] n 0 []) = natCast n
    rw [addTerm_denote]
    change add (mul (sub (natCast n) zero) one) zero = natCast n
    rw [add_zero, mul_one, sub_zero]
  | .add a b => by
    change denote ρ (polyAdd (normExpr a) (normExpr b)) = add (a.eval ρ) (b.eval ρ)
    rw [polyAdd_denote, denote_normExpr ρ a, denote_normExpr ρ b]
  | .sub a b => by
    change denote ρ (mulTerm [] 0 1 (normExpr b) (normExpr a)) = sub (a.eval ρ) (b.eval ρ)
    rw [mulTerm_denote, denote_normExpr ρ a, denote_normExpr ρ b]
    change add (mul (mul (sub zero one) one) (b.eval ρ)) (a.eval ρ) = _
    rw [mul_one, sub_eq_add_neg zero, zero_add, neg_mul, one_mul, add_comm, ← sub_eq_add_neg]
  | .mul a b => by
    change denote ρ (polyMul (normExpr a) (normExpr b)) = mul (a.eval ρ) (b.eval ρ)
    rw [polyMul_denote, denote_normExpr ρ a, denote_normExpr ρ b]
  | .neg a => by
    change denote ρ (mulTerm [] 0 1 (normExpr a) []) = neg (a.eval ρ)
    rw [mulTerm_denote, denote_normExpr ρ a]
    change add (mul (mul (sub zero one) one) (a.eval ρ)) zero = _
    rw [add_zero, mul_one, sub_eq_add_neg zero, zero_add, neg_mul, one_mul]
  | .pow a k => by
    change denote ρ (polyPow (normExpr a) k) = npow (a.eval ρ) k
    rw [polyPow_denote, denote_normExpr ρ a]

/-- Reflection principle: if `lhs - rhs` normalizes to the empty polynomial, both sides agree
    under every valuation in every lawful commutative ring. -/
theorem eq_of_normSub_nil {R : Type} [LawfulCommRing R] (ρ : Nat → R) (lhs rhs : CRingExpr)
    (h : normExpr (.sub lhs rhs) = []) : lhs.eval ρ = rhs.eval ρ := by
  have hd := denote_normExpr ρ (.sub lhs rhs)
  rw [h] at hd
  exact LawfulCommRing.sub_eq_zero_iff.mp hd.symm

/-- Cofactor helper: an identity `a - b = Σ cᵢ pᵢ` whose right side has been rewritten to
    zero yields `a = b`. -/
theorem eq_of_sub_eq_zero {R : Type} [LawfulCommRing R] {a b : R}
    (h : CommRingOps.sub a b = CommRingOps.zero) : a = b :=
  LawfulCommRing.sub_eq_zero_iff.mp h

end Qsag

/-! ## The `constructive_ring` tactic -/

namespace Qsag.Tactic.ConstructiveRing

open Lean Meta Elab Tactic

/-- Find or allocate the atom index of `e`. -/
private meta def atomIndex (e : Expr) : StateT (Array Expr) MetaM Nat := do
  let atoms ← get
  for h : i in [0:atoms.size] do
    if atoms[i] == e then return i
  for h : i in [0:atoms.size] do
    if ← withReducible (isDefEq atoms[i] e) then return i
  set (atoms.push e)
  return atoms.size

private meta def litNat? (e : Expr) : Option Nat :=
  match e.consumeMData with
  | .lit (.natVal n) => some n
  | e => if e.isAppOfArity ``OfNat.ofNat 3 then e.appFn!.appArg!.rawNatLit? else none

/-- Reify a ring term into a `CRingExpr`, collecting atoms. -/
private meta partial def reify (e : Expr) : StateT (Array Expr) MetaM Expr := do
  let e := e.consumeMData
  let fn := e.getAppFn
  let args := e.getAppArgs
  let bin (c : Name) (a b : Expr) : StateT (Array Expr) MetaM Expr := do
    return mkApp2 (mkConst c) (← reify a) (← reify b)
  let lit (n : Nat) : Expr := mkApp (mkConst ``Qsag.CRingExpr.lit) (mkRawNatLit n)
  let atom : StateT (Array Expr) MetaM Expr := do
    return mkApp (mkConst ``Qsag.CRingExpr.var) (mkRawNatLit (← atomIndex e))
  match fn.constName?, args.size with
  | some ``Qsag.CommRingOps.add, 4 => bin ``Qsag.CRingExpr.add args[2]! args[3]!
  | some ``Qsag.CommRingOps.sub, 4 => bin ``Qsag.CRingExpr.sub args[2]! args[3]!
  | some ``Qsag.CommRingOps.mul, 4 => bin ``Qsag.CRingExpr.mul args[2]! args[3]!
  | some ``HAdd.hAdd, 6 => bin ``Qsag.CRingExpr.add args[4]! args[5]!
  | some ``HSub.hSub, 6 => bin ``Qsag.CRingExpr.sub args[4]! args[5]!
  | some ``HMul.hMul, 6 => bin ``Qsag.CRingExpr.mul args[4]! args[5]!
  | some ``Qsag.CommRingOps.neg, 3 =>
    return mkApp (mkConst ``Qsag.CRingExpr.neg) (← reify args[2]!)
  | some ``Neg.neg, 3 => return mkApp (mkConst ``Qsag.CRingExpr.neg) (← reify args[2]!)
  | some ``Qsag.CommRingOps.zero, 2 => return lit 0
  | some ``Qsag.CommRingOps.one, 2 => return lit 1
  | some ``OfNat.ofNat, 3 =>
    match args[1]!.rawNatLit? with
    | some n => return lit n
    | none => atom
  | some ``Qsag.CRing.natCast, 3 =>
    match litNat? args[2]! with
    | some n => return lit n
    | none => atom
  | some ``HPow.hPow, 6 =>
    match litNat? args[5]! with
    | some k => return mkApp2 (mkConst ``Qsag.CRingExpr.pow) (← reify args[4]!) (mkRawNatLit k)
    | none => atom
  | some ``Qsag.CRing.npow, 4 =>
    match litNat? args[3]! with
    | some k => return mkApp2 (mkConst ``Qsag.CRingExpr.pow) (← reify args[2]!) (mkRawNatLit k)
    | none => atom
  | _, _ => atom

/-- `constructive_ring` closes `lhs = rhs` in a `LawfulCommRing` when both sides are equal as
    polynomials in their atoms. The certificate is checked by kernel reduction. -/
elab "constructive_ring" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let some (ty, lhs, rhs) := target.consumeMData.eq?
    | throwError "constructive_ring: goal is not an equality{indentExpr target}"
  let inst ← synthInstance (mkApp (mkConst ``Qsag.LawfulCommRing) ty)
  let ops := mkApp2 (mkConst ``Qsag.LawfulCommRing.toCommRingOps) ty inst
  let ((l, r), atoms) ← (do return (← reify lhs, ← reify rhs) : StateT _ MetaM _).run #[]
  let zero := mkApp2 (mkConst ``Qsag.CommRingOps.zero) ty ops
  let atomList ← mkListLit ty atoms.toList
  let ρ := Expr.lam `i (mkConst ``Nat)
    (mkApp4 (mkConst ``List.getD [Level.zero]) ty atomList (.bvar 0) zero) .default
  let polyTy := mkConst ``Qsag.CMvPoly
  let nil := mkApp (mkConst ``List.nil [Level.zero]) (← whnfR polyTy).appArg!
  let nf := mkApp (mkConst ``Qsag.normExpr) (mkApp2 (mkConst ``Qsag.CRingExpr.sub) l r)
  -- The certificate is checked once, as an auxiliary theorem, and then shared.
  let cert ←
    try mkAuxTheorem (← mkEq nf nil) (mkApp2 (mkConst ``Eq.refl [Level.one]) polyTy nil)
    catch _ =>
      throwError "constructive_ring: the two sides differ as polynomials in {atoms.size} atoms"
  let proof := mkApp6 (mkConst ``Qsag.eq_of_normSub_nil) ty inst ρ l r cert
  let evalOf (x : Expr) := mkApp4 (mkConst ``Qsag.CRingExpr.eval) ty ops x ρ
  let stated ← mkEq (evalOf l) (evalOf r)
  unless ← isDefEq stated target do
    throwError "constructive_ring: reified sides do not unfold to the goal{indentExpr stated}"
  goal.assign proof

end Qsag.Tactic.ConstructiveRing

