module
/-
# Qsag.Tactic.AssuranceKit — `0-Classical` Proof Automation & Constructive Assurance Gates

Reusable Lean 4.35 tactic and command-elaboration infrastructure for QSAG (`LAW-M2`):
1. **`#verify_constructive <ident>+`**:
   Compile-time kernel axiom and `Prop`-type auditor enforcing `0 sorryAx`, `0` custom axioms,
   `0` compiler-trust axioms (`_native` / `ofReduceBool`), and **`0` transitive `Classical.choice`**
   (`axioms ⊆ {propext, Quot.sound}`).
2. **`#tooth_pair <secIdent> vs <toothIdent>`**:
   Compile-time structural pairing auditor verifying that a security theorem is paired with a
   structurally related counterexample/refusal theorem and that both satisfy
   `#verify_constructive` without vacuous `False` hypotheses.
3. **`by bv_xor_cancel`**:
   Constructive (`0 Classical.choice`, `0 ofReduceBool`) XOR one-time-pad normalizer and
   unbounded reflected AC normalization over `BitVec w`; a Boolean fallback handles
   other bitwise identities over `UInt64`, `UInt8`, and `Bool`.
4. **`by compose_forward_sim` / `by compose_forward_sim [h₁, ...]`**:
   Goal-directed `TacticM` spine synthesizer chaining `ForwardSim.refl`, `ForwardSim.trans`, and
   `LockstepSim.toForwardSim` across multi-layer protocol state machines.
5. **`by mask_bijection_hop` / `by mask_bijection_hop <equiv>`**:
   Relational pad-bijection synthesizer discharging `finSum` uniform-mask invariance goals via
   `SimpleEquiv` combinators (`bvXorEquiv`, `u64XorEquiv`, `boolXorEquiv`, `ringAddEquiv`,
   `SimpleEquiv.prodCongr`) and `bv_xor_cancel` with `0 Classical.choice`.
-/

public import Qsag.Constructive
public import Qsag.SimulationSpine
public import Qsag.UcGames
public meta import Lean

public section

namespace Qsag

set_option autoImplicit false

/-! ## 1. Constructive `Bool`, `BitVec w`, `UInt64` & `UInt8` XOR Algebra (`0 Classical.choice`) -/

theorem bool_xor_self (a : Bool) : (a ^^ a) = false := by
  cases a <;> rfl

theorem bool_xor_false (a : Bool) : (a ^^ false) = a := by
  cases a <;> rfl

theorem bool_false_xor (a : Bool) : (false ^^ a) = a := by
  cases a <;> rfl

theorem bool_xor_comm (a b : Bool) : (a ^^ b) = (b ^^ a) := by
  cases a <;> cases b <;> rfl

theorem bool_xor_assoc (a b c : Bool) : ((a ^^ b) ^^ c) = (a ^^ (b ^^ c)) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem bool_xor_cancel_right (a m : Bool) : ((a ^^ m) ^^ m) = a := by
  cases a <;> cases m <;> rfl

theorem bool_xor_cancel_left (m a : Bool) : (m ^^ (m ^^ a)) = a := by
  cases m <;> cases a <;> rfl

theorem bool_xor_cancel_mid (a m : Bool) : ((m ^^ a) ^^ m) = a := by
  cases m <;> cases a <;> rfl

theorem bool_xor_cancel_outer (m a : Bool) : (m ^^ (a ^^ m)) = a := by
  cases m <;> cases a <;> rfl

theorem bool_bne_self (a : Bool) : (a != a) = false := by
  cases a <;> rfl

theorem bool_bne_false (a : Bool) : (a != false) = a := by
  cases a <;> rfl

theorem bool_false_bne (a : Bool) : (false != a) = a := by
  cases a <;> rfl

theorem bool_bne_comm (a b : Bool) : (a != b) = (b != a) := by
  cases a <;> cases b <;> rfl

theorem bool_bne_assoc (a b c : Bool) : ((a != b) != c) = (a != (b != c)) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem bool_bne_cancel_right (a m : Bool) : ((a != m) != m) = a := by
  cases a <;> cases m <;> rfl

theorem bool_bne_cancel_left (m a : Bool) : (m != (m != a)) = a := by
  cases m <;> cases a <;> rfl

theorem bool_bne_cancel_mid (a m : Bool) : ((m != a) != m) = a := by
  cases m <;> cases a <;> rfl

theorem bool_bne_cancel_outer (m a : Bool) : (m != (a != m)) = a := by
  cases m <;> cases a <;> rfl

theorem bool_bne_eq_false_iff (a b : Bool) : (a != b) = false ↔ a = b := by
  cases a <;> cases b <;> decide

theorem bool_bne_eq_true_iff (a b : Bool) : (a != b) = true ↔ a ≠ b := by
  cases a <;> cases b <;> decide

/-- Extensional equality on `BitVec w` from bounded `getLsbD` agreement (`0 Classical.choice`). -/
theorem bv_eq_of_getLsbD_eq {w : Nat} {x y : BitVec w}
    (h : ∀ i : Nat, i < w → x.getLsbD i = y.getLsbD i) : x = y := by
  apply BitVec.eq_of_toNat_eq
  apply Nat.eq_of_testBit_eq
  intro i
  if hi : i < w then
    exact h i hi
  else
    have hGe : w ≤ i := Nat.le_of_not_gt hi
    have hx : x.getLsbD i = false := BitVec.getLsbD_of_ge x i hGe
    have hy : y.getLsbD i = false := BitVec.getLsbD_of_ge y i hGe
    exact hx.trans hy.symm

theorem bv_xor_self {w : Nat} (x : BitVec w) : x ^^^ x = 0#w := by
  apply bv_eq_of_getLsbD_eq
  intro i _
  rw [BitVec.getLsbD_xor, BitVec.getLsbD_zero, bool_xor_self]

theorem bv_xor_zero {w : Nat} (x : BitVec w) : x ^^^ 0#w = x := by
  apply bv_eq_of_getLsbD_eq
  intro i _
  rw [BitVec.getLsbD_xor, BitVec.getLsbD_zero, bool_xor_false]

theorem bv_zero_xor {w : Nat} (x : BitVec w) : 0#w ^^^ x = x := by
  apply bv_eq_of_getLsbD_eq
  intro i _
  rw [BitVec.getLsbD_xor, BitVec.getLsbD_zero, bool_false_xor]

theorem bv_xor_comm {w : Nat} (x y : BitVec w) : x ^^^ y = y ^^^ x := by
  apply bv_eq_of_getLsbD_eq
  intro i _
  rw [BitVec.getLsbD_xor, BitVec.getLsbD_xor, bool_xor_comm]

theorem bv_xor_assoc {w : Nat} (x y z : BitVec w) : (x ^^^ y) ^^^ z = x ^^^ (y ^^^ z) := by
  apply bv_eq_of_getLsbD_eq
  intro i _
  rw [BitVec.getLsbD_xor, BitVec.getLsbD_xor, BitVec.getLsbD_xor, BitVec.getLsbD_xor,
      bool_xor_assoc]

theorem bv_xor_left_comm {w : Nat} (x y z : BitVec w) : x ^^^ (y ^^^ z) = y ^^^ (x ^^^ z) := by
  rw [← bv_xor_assoc, bv_xor_comm x y, bv_xor_assoc]

theorem bv_xor_cancel_right {w : Nat} (x m : BitVec w) : (x ^^^ m) ^^^ m = x := by
  rw [bv_xor_assoc, bv_xor_self, bv_xor_zero]

theorem bv_xor_cancel_left {w : Nat} (m x : BitVec w) : m ^^^ (m ^^^ x) = x := by
  rw [← bv_xor_assoc, bv_xor_self, bv_zero_xor]

theorem bv_xor_cancel_mid {w : Nat} (x m : BitVec w) : (m ^^^ x) ^^^ m = x := by
  rw [bv_xor_comm m x, bv_xor_cancel_right]

theorem bv_xor_cancel_outer {w : Nat} (m x : BitVec w) : m ^^^ (x ^^^ m) = x := by
  rw [bv_xor_comm x m, bv_xor_cancel_left]

theorem bv_xor_eq_zero_iff {w : Nat} (x y : BitVec w) : x ^^^ y = 0#w ↔ x = y := by
  constructor
  · intro h
    have h1 : (x ^^^ y) ^^^ y = 0#w ^^^ y := congrArg (· ^^^ y) h
    rw [bv_xor_cancel_right, bv_zero_xor] at h1
    exact h1
  · rintro rfl
    exact bv_xor_self x

theorem bv_xor_ne_zero_iff {w : Nat} (x y : BitVec w) : x ^^^ y ≠ 0#w ↔ x ≠ y :=
  not_congr (bv_xor_eq_zero_iff x y)

theorem bv_bne_zero_eq_true_iff_ne {w : Nat} (x y : BitVec w) :
    (x ^^^ y != 0#w) = true ↔ x ≠ y := by
  rw [bne_iff_ne]
  exact bv_xor_ne_zero_iff x y

theorem bv_bne_zero_eq_false_iff_eq {w : Nat} (x y : BitVec w) :
    (x ^^^ y != 0#w) = false ↔ x = y := by
  rw [bne_eq_false_iff_eq]
  exact bv_xor_eq_zero_iff x y

theorem u64_toBitVec_xor (x y : UInt64) : (x ^^^ y).toBitVec = x.toBitVec ^^^ y.toBitVec := rfl
theorem u64_toBitVec_zero : (0 : UInt64).toBitVec = 0#64 := rfl
theorem u8_toBitVec_xor (x y : UInt8) : (x ^^^ y).toBitVec = x.toBitVec ^^^ y.toBitVec := rfl
theorem u8_toBitVec_zero : (0 : UInt8).toBitVec = 0#8 := rfl

theorem u64_xor_self (x : UInt64) : x ^^^ x = 0 :=
  UInt64.eq_of_toBitVec_eq (bv_xor_self x.toBitVec)

theorem u64_xor_zero (x : UInt64) : x ^^^ 0 = x :=
  UInt64.eq_of_toBitVec_eq (bv_xor_zero x.toBitVec)

theorem u64_zero_xor (x : UInt64) : 0 ^^^ x = x :=
  UInt64.eq_of_toBitVec_eq (bv_zero_xor x.toBitVec)

theorem u64_xor_comm (x y : UInt64) : x ^^^ y = y ^^^ x :=
  UInt64.eq_of_toBitVec_eq (bv_xor_comm x.toBitVec y.toBitVec)

theorem u64_xor_assoc (x y z : UInt64) : (x ^^^ y) ^^^ z = x ^^^ (y ^^^ z) :=
  UInt64.eq_of_toBitVec_eq (bv_xor_assoc x.toBitVec y.toBitVec z.toBitVec)

theorem u64_xor_cancel_right (x m : UInt64) : (x ^^^ m) ^^^ m = x :=
  UInt64.eq_of_toBitVec_eq (bv_xor_cancel_right x.toBitVec m.toBitVec)

theorem u64_xor_cancel_left (m x : UInt64) : m ^^^ (m ^^^ x) = x :=
  UInt64.eq_of_toBitVec_eq (bv_xor_cancel_left m.toBitVec x.toBitVec)

theorem u64_xor_cancel_mid (x m : UInt64) : (m ^^^ x) ^^^ m = x :=
  UInt64.eq_of_toBitVec_eq (bv_xor_cancel_mid x.toBitVec m.toBitVec)

theorem u64_xor_cancel_outer (m x : UInt64) : m ^^^ (x ^^^ m) = x :=
  UInt64.eq_of_toBitVec_eq (bv_xor_cancel_outer m.toBitVec x.toBitVec)

theorem u8_xor_self (x : UInt8) : x ^^^ x = 0 :=
  UInt8.eq_of_toBitVec_eq (bv_xor_self x.toBitVec)

theorem u8_xor_zero (x : UInt8) : x ^^^ 0 = x :=
  UInt8.eq_of_toBitVec_eq (bv_xor_zero x.toBitVec)

theorem u8_zero_xor (x : UInt8) : 0 ^^^ x = x :=
  UInt8.eq_of_toBitVec_eq (bv_zero_xor x.toBitVec)

theorem u8_xor_comm (x y : UInt8) : x ^^^ y = y ^^^ x :=
  UInt8.eq_of_toBitVec_eq (bv_xor_comm x.toBitVec y.toBitVec)

theorem u8_xor_assoc (x y z : UInt8) : (x ^^^ y) ^^^ z = x ^^^ (y ^^^ z) :=
  UInt8.eq_of_toBitVec_eq (bv_xor_assoc x.toBitVec y.toBitVec z.toBitVec)

theorem u8_xor_cancel_right (x m : UInt8) : (x ^^^ m) ^^^ m = x :=
  UInt8.eq_of_toBitVec_eq (bv_xor_cancel_right x.toBitVec m.toBitVec)

theorem u8_xor_cancel_left (m x : UInt8) : m ^^^ (m ^^^ x) = x :=
  UInt8.eq_of_toBitVec_eq (bv_xor_cancel_left m.toBitVec x.toBitVec)

theorem u8_xor_cancel_mid (x m : UInt8) : (m ^^^ x) ^^^ m = x :=
  UInt8.eq_of_toBitVec_eq (bv_xor_cancel_mid x.toBitVec m.toBitVec)

theorem u8_xor_cancel_outer (m x : UInt8) : m ^^^ (x ^^^ m) = x :=
  UInt8.eq_of_toBitVec_eq (bv_xor_cancel_outer m.toBitVec x.toBitVec)

theorem ring_add_sub_cancel_right {R : Type} [LawfulCommRing R] (a b : R) :
    CommRingOps.sub (CommRingOps.add a b) b = a := by
  rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_assoc,
      LawfulCommRing.add_right_neg, LawfulCommRing.add_zero]

theorem ring_sub_add_cancel_right {R : Type} [LawfulCommRing R] (a b : R) :
    CommRingOps.add (CommRingOps.sub a b) b = a := by
  rw [LawfulCommRing.add_comm, LawfulCommRing.add_sub_cancel_left]

/-! ## 2. Constructive `SimpleEquiv` Pad-Bijection Combinators (`0 Classical.choice`) -/

@[expose] def SimpleEquiv.refl (α : Type) : SimpleEquiv α α where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl

@[expose] def SimpleEquiv.symm {α β : Type} (e : SimpleEquiv α β) : SimpleEquiv β α where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv

@[expose] def SimpleEquiv.trans {α β γ : Type}
    (e₁ : SimpleEquiv α β) (e₂ : SimpleEquiv β γ) : SimpleEquiv α γ where
  toFun a := e₂.toFun (e₁.toFun a)
  invFun c := e₁.invFun (e₂.invFun c)
  left_inv a := by rw [e₂.left_inv, e₁.left_inv]
  right_inv c := by rw [e₁.right_inv, e₂.right_inv]

@[expose] def SimpleEquiv.prodCongr {α₁ β₁ α₂ β₂ : Type}
    (e₁ : SimpleEquiv α₁ β₁) (e₂ : SimpleEquiv α₂ β₂) : SimpleEquiv (α₁ × α₂) (β₁ × β₂) where
  toFun p := (e₁.toFun p.1, e₂.toFun p.2)
  invFun q := (e₁.invFun q.1, e₂.invFun q.2)
  left_inv := fun ⟨a₁, a₂⟩ => Prod.ext (e₁.left_inv a₁) (e₂.left_inv a₂)
  right_inv := fun ⟨b₁, b₂⟩ => Prod.ext (e₁.right_inv b₁) (e₂.right_inv b₂)

/-- Constructive involutive one-time-pad bijection `x ↦ x ^^^ mask` on `BitVec w`. -/
@[expose] def bvXorEquiv {w : Nat} (mask : BitVec w) : SimpleEquiv (BitVec w) (BitVec w) where
  toFun x := x ^^^ mask
  invFun y := y ^^^ mask
  left_inv x := bv_xor_cancel_right x mask
  right_inv y := bv_xor_cancel_right y mask

/-- Constructive involutive one-time-pad bijection `x ↦ x ^^^ mask` on `UInt64`. -/
@[expose] def u64XorEquiv (mask : UInt64) : SimpleEquiv UInt64 UInt64 where
  toFun x := x ^^^ mask
  invFun y := y ^^^ mask
  left_inv x := u64_xor_cancel_right x mask
  right_inv y := u64_xor_cancel_right y mask

/-- Constructive involutive one-time-pad bijection `x ↦ x != mask` on `Bool`. -/
@[expose] def boolXorEquiv (mask : Bool) : SimpleEquiv Bool Bool where
  toFun x := x != mask
  invFun y := y != mask
  left_inv x := bool_bne_cancel_right x mask
  right_inv y := bool_bne_cancel_right y mask

/-- Constructive additive shift bijection `x ↦ x + delta` over any `LawfulCommRing R`. -/
@[expose] def ringAddEquiv {R : Type} [LawfulCommRing R] (delta : R) : SimpleEquiv R R where
  toFun x := CommRingOps.add x delta
  invFun y := CommRingOps.sub y delta
  left_inv x := ring_add_sub_cancel_right x delta
  right_inv y := ring_sub_add_cancel_right y delta

theorem SimpleEquiv.refl_toFun {α : Type} (x : α) :
    (SimpleEquiv.refl α).toFun x = x := rfl

theorem SimpleEquiv.symm_toFun {α β : Type} (e : SimpleEquiv α β) (y : β) :
    (SimpleEquiv.symm e).toFun y = e.invFun y := rfl

theorem SimpleEquiv.trans_toFun {α β γ : Type}
    (e₁ : SimpleEquiv α β) (e₂ : SimpleEquiv β γ) (x : α) :
    (SimpleEquiv.trans e₁ e₂).toFun x = e₂.toFun (e₁.toFun x) := rfl

theorem SimpleEquiv.prodCongr_toFun {α₁ β₁ α₂ β₂ : Type}
    (e₁ : SimpleEquiv α₁ β₁) (e₂ : SimpleEquiv α₂ β₂) (p : α₁ × α₂) :
    (SimpleEquiv.prodCongr e₁ e₂).toFun p = (e₁.toFun p.1, e₂.toFun p.2) := rfl

theorem bvXorEquiv_toFun {w : Nat} (mask x : BitVec w) :
    (bvXorEquiv mask).toFun x = x ^^^ mask := rfl

theorem u64XorEquiv_toFun (mask x : UInt64) :
    (u64XorEquiv mask).toFun x = x ^^^ mask := rfl

theorem boolXorEquiv_toFun (mask x : Bool) :
    (boolXorEquiv mask).toFun x = (x != mask) := rfl

theorem ringAddEquiv_toFun {R : Type} [LawfulCommRing R] (delta x : R) :
    (ringAddEquiv delta).toFun x = CommRingOps.add x delta := rfl

/-- Relational `finSum` pad-bijection hop reducing distributional equality over a sample space `Ω`
    enumerated by `enum` to pointwise equality after applying mask bijection `e`. -/
theorem finSum_bijection_hop_eq {Ω : Type} {C : Nat}
    (enum : SimpleEquiv (Fin C) Ω) (e : SimpleEquiv Ω Ω)
    (f g : Ω → Nat)
    (hPointwise : ∀ ω : Ω, f (e.toFun ω) = g ω) :
    finSum C (fun i => f (enum.toFun i)) = finSum C (fun i => g (enum.toFun i)) := by
  rw [← finSum_bijection_invariant enum e f]
  exact finSum_congr (fun i => hPointwise (enum.toFun i))

/-! Reflection uses merge sort on natural atom indices, followed by a linear
parity pass. No enumeration of Boolean assignments is involved. -/
@[expose] def xorEval {w : Nat} (atoms : Nat → BitVec w) : List Nat → BitVec w
  | [] => 0#w
  | a :: as => atoms a ^^^ xorEval atoms as

@[expose] def xorParity : List Nat → List Nat
  | [] => []
  | [a] => [a]
  | a :: b :: rest => if a = b then xorParity rest else a :: xorParity (b :: rest)

/-- Structurally recursive merge: the fallback preserves evaluation even if a
caller supplies insufficient fuel. Sorting supplies the sum of input lengths. -/
@[expose] def xorMerge : Nat → List Nat → List Nat → List Nat
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, xs, [] => xs
  | fuel + 1, x :: xs, y :: ys =>
    if x ≤ y then x :: xorMerge fuel xs (y :: ys)
    else y :: xorMerge fuel (x :: xs) ys

@[expose] def xorSort : Nat → List Nat → List Nat
  | 0, xs => xs
  | _ + 1, [] => []
  | _ + 1, [x] => [x]
  | fuel + 1, x :: y :: xs =>
    let all := x :: y :: xs
    let mid := all.length / 2
    xorMerge all.length (xorSort fuel (all.take mid)) (xorSort fuel (all.drop mid))

@[expose] def xorNorm (xs : List Nat) : List Nat :=
  xorParity (xorSort xs.length xs)

theorem xorEval_parity {w : Nat} (atoms : Nat → BitVec w) (xs : List Nat) :
    xorEval atoms (xorParity xs) = xorEval atoms xs := by
  induction xs using xorParity.induct with
  | case1 => rfl
  | case2 a => rfl
  | case3 a rest ih =>
    simp only [xorParity, ite_eq_left, xorEval, ih, bv_xor_cancel_left]
  | case4 a b rest h ih =>
    simp only [xorParity, ite_eq_right h, xorEval, ih]

theorem xorEval_perm {w : Nat} (atoms : Nat → BitVec w) {xs ys : List Nat}
    (h : xs.Perm ys) : xorEval atoms xs = xorEval atoms ys := by
  induction h with
  | nil => rfl
  | cons a h ih => simp only [xorEval, ih]
  | swap a b rest =>
    simp only [xorEval, ← bv_xor_assoc]
    rw [bv_xor_comm (atoms b) (atoms a)]
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem xorEval_append {w : Nat} (atoms : Nat → BitVec w) (xs ys : List Nat) :
    xorEval atoms (xs ++ ys) = xorEval atoms xs ^^^ xorEval atoms ys := by
  induction xs with
  | nil => simp only [List.nil_append, xorEval, bv_zero_xor]
  | cons a rest ih => simp only [List.cons_append, xorEval, ih, bv_xor_assoc]

theorem xorEval_merge {w : Nat} (atoms : Nat → BitVec w) (fuel : Nat) (xs ys : List Nat) :
    xorEval atoms (xorMerge fuel xs ys) = xorEval atoms xs ^^^ xorEval atoms ys := by
  induction fuel generalizing xs ys with
  | zero => exact xorEval_append atoms xs ys
  | succ fuel ih =>
    cases xs with
    | nil => simp only [xorMerge, xorEval, bv_zero_xor]
    | cons x xs =>
      cases ys with
      | nil => simp only [xorMerge, xorEval, bv_xor_zero]
      | cons y ys =>
        simp only [xorMerge]
        split
        · simp only [xorEval, ih, bv_xor_assoc]
        · simp only [xorEval, ih]
          rw [← bv_xor_assoc (atoms y), bv_xor_comm (atoms y), bv_xor_assoc]

theorem xorEval_sort {w : Nat} (atoms : Nat → BitVec w) (fuel : Nat) (xs : List Nat) :
    xorEval atoms (xorSort fuel xs) = xorEval atoms xs := by
  induction fuel generalizing xs with
  | zero => rfl
  | succ fuel ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      cases xs with
      | nil => rfl
      | cons y xs =>
        simp only [xorSort, xorEval_merge, ih, ← xorEval_append, List.take_append_drop]

theorem xorEval_norm_eq {w : Nat} (atoms : Nat → BitVec w) (xs : List Nat) :
    xorEval atoms (xorNorm xs) = xorEval atoms xs :=
  (xorEval_parity atoms _).trans (xorEval_sort atoms _ xs)

theorem xorEval_congr_norm {w : Nat} (atoms : Nat → BitVec w) (xs ys : List Nat)
    (h : xorNorm xs = xorNorm ys) : xorEval atoms xs = xorEval atoms ys := by
  rw [← xorEval_norm_eq atoms xs, ← xorEval_norm_eq atoms ys, h]

inductive XorTree where
  | zero
  | atom (index : Nat)
  | xor (left right : XorTree)

@[expose] def XorTree.eval {w : Nat} (atoms : Nat → BitVec w) : XorTree → BitVec w
  | .zero => 0#w
  | .atom i => atoms i
  | .xor l r => l.eval atoms ^^^ r.eval atoms

/-- Accumulator flattening visits each tree node once, including left-heavy trees. -/
@[expose] def XorTree.flatten : XorTree → List Nat → List Nat
  | .zero, rest => rest
  | .atom i, rest => i :: rest
  | .xor l r, rest => l.flatten (r.flatten rest)

theorem XorTree.eval_flatten {w : Nat} (atoms : Nat → BitVec w)
    (t : XorTree) (rest : List Nat) :
    xorEval atoms (t.flatten rest) = t.eval atoms ^^^ xorEval atoms rest := by
  induction t generalizing rest with
  | zero => simp only [flatten, eval, bv_zero_xor]
  | atom i => rfl
  | xor l r il ir => simp only [flatten, eval, il, ir, bv_xor_assoc]

theorem XorTree.norm_sound {w : Nat} (atoms : Nat → BitVec w) (l r : XorTree)
    (h : xorNorm (l.flatten []) = xorNorm (r.flatten [])) : l.eval atoms = r.eval atoms := by
  have he := xorEval_congr_norm atoms (l.flatten []) (r.flatten []) h
  simpa only [eval_flatten, xorEval, bv_xor_zero] using he

/-- An unbounded unary length prefix: `n` one bytes and a zero delimiter.
Unlike a fixed-width length field this encoding needs no size precondition.
The payload is arbitrary bytes, including zero and one. -/
def frameLength : Nat → List UInt8 → List UInt8
  | 0, bytes => 0 :: bytes
  | n + 1, bytes => 1 :: frameLength n bytes

def frameList (a : List UInt8) : List UInt8 := frameLength a.length a

theorem frameLength_append (n : Nat) (a rest : List UInt8) :
    frameLength n a ++ rest = frameLength n (a ++ rest) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (List.cons 1) ih

theorem frameLength_inj (n m : Nat) (a b : List UInt8)
    (h : frameLength n a = frameLength m b) : n = m ∧ a = b := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => exact ⟨rfl, (List.cons.inj h).2⟩
    | succ m =>
      have bad : (0 : UInt8) = 1 := (List.cons.inj h).1
      exact absurd bad (by decide)
  | succ n ih =>
    cases m with
    | zero =>
      have bad : (1 : UInt8) = 0 := (List.cons.inj h).1
      exact absurd bad (by decide)
    | succ m =>
      have parts := ih m (List.cons.inj h).2
      exact ⟨congrArg Nat.succ parts.1, parts.2⟩

theorem frameList_append_inj {a b rest₁ rest₂ : List UInt8}
    (h : frameList a ++ rest₁ = frameList b ++ rest₂) :
    a = b ∧ rest₁ = rest₂ := by
  simp only [frameList, frameLength_append] at h
  have parts := frameLength_inj _ _ _ _ h
  exact List.append_inj parts.2 parts.1

theorem frameList_inj {a b : List UInt8} (h : frameList a = frameList b) : a = b :=
  (frameList_append_inj (rest₁ := []) (rest₂ := []) (by simpa using h)).1

end Qsag

/-! ## 3. `MetaM` / `TacticM` / `CommandElabM` Automation (`LAW-M2`) -/

namespace Qsag.Tactic.AssuranceKit

open Lean Meta Elab Command Tactic

/-- Strip outer `Expr.mdata` wrappers. -/
private meta partial def stripMData (e : Expr) : Expr :=
  match e with
  | .mdata _ inner => stripMData inner
  | _ => e

/-- Strip outer `.lam`, `.letE`, and `.mdata` binders to inspect a proof's head combinator. -/
private meta partial def stripBinders (e : Expr) : Expr :=
  match stripMData e with
  | .lam _ _ body _ => stripBinders body
  | .letE _ _ val body _ => stripBinders (body.instantiate1 val)
  | core => core

/-- Walk every available body once, including types and constructor dependencies.
Imported opaque bodies require Lean's exported kernel axiom summaries as well. -/
private meta partial def auditDag (env : Environment) (todo : List Name)
    (seen : Std.HashSet Name := {}) : CoreM Unit := do
  match todo with
  | [] => pure ()
  | n :: rest =>
    if seen.contains n then return ← auditDag env rest seen
    let seen := seen.insert n
    if [``sorryAx, ``Classical.choice, `Lean.ofReduceBool, `Lean.ofReduceNat,
        `Lean.trustCompiler].contains n then
      throwError "constructive audit: forbidden dependency {n}"
    let some ci := env.checked.get.find? n | throwError "constructive audit: missing dependency {n}"
    if let .axiomInfo _ := ci then
      let axs ← Lean.collectAxioms n
      for ax in axs do
        unless ax == ``propext || ax == ``Quot.sound do
          throwError "constructive audit: forbidden axiom {ax} via {n}"
    let deps := ci.type.getUsedConstants.toList ++
      (ci.value? (allowOpaque := true)).toList.flatMap (·.getUsedConstants.toList)
    let deps := match ci with
      | .inductInfo v => v.ctors ++ deps
      | _ => deps
    auditDag env (deps ++ rest) seen

private meta def literal? (e : Expr) : MetaM (Option Expr) := do
  let e ← whnf e
  match e with
  | .lit _ => return some e
  | _ =>
    if e.isConstOf ``Bool.true || e.isConstOf ``Bool.false || e.isConstOf ``Nat.zero then
      return some e
    return none

/-- Deliberately syntactic diagnostics, not a decision procedure for satisfiability.
Use the opened proof body, not its lambda binder types, to detect unused premises. -/
private meta def auditPremises (ci : ConstantInfo) : MetaM Unit := do
  let some value := ci.value? (allowOpaque := true)
    | throwError "constructive audit: proof body unavailable; use import all"
  forallTelescope ci.type fun xs _ => do
    let body := (mkAppN value xs).headBeta
    let mut eqs : Array (Expr × Expr) := #[]
    for x in xs do
      let ty ← inferType x
      let t ← whnf ty
      if [``False, ``Empty, ``PEmpty].any t.getAppFn.isConstOf then
        throwError "constructive audit: empty premise {ty}"
      if ← isProp ty then
        unless body.containsFVar x.fvarId! do
          throwError "constructive audit: unused Prop premise {ty}"
      -- Not and Ne unfold to an arrow whose codomain is False.
      if let .forallE _ dom cod _ := t then
        if cod.isConstOf ``False then
          if let some (_, a, b) := dom.eq? then
            if ← withoutModifyingState (isDefEq a b) then
              throwError "constructive audit: reflexive disequality premise {ty}"
      if let some (_, a, b) := t.eq? then
        for (target, lit) in #[(a, b), (b, a)] do
          if let some v ← literal? lit then
            if let some u ← literal? target then
              unless ← withoutModifyingState (isDefEq u v) do
                throwError "constructive audit: contradictory literal equality {ty}"
            for (prev, pv) in eqs do
              if !(← withoutModifyingState (isDefEq pv v)) &&
                  (← withoutModifyingState (isDefEq prev target)) then
                throwError "constructive audit: conflicting equalities for {target}"
            eqs := eqs.push (target, v)

/-- Strict constructive theorem audit, with structural premise diagnostics. -/
meta def verifyConstructiveDecl (id : Ident) : CommandElabM (Name × ConstantInfo) := do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let env ← getEnv
  let some ci := env.find? n | throwErrorAt id "unknown theorem {n}"
  unless ci matches .thmInfo _ do
    throwErrorAt id "constructive audit: expected a theorem with visible body: {n}"
  liftCoreM <| auditDag env [n]
  let axs ← liftCoreM <| Lean.collectAxioms n
  for ax in axs do
    unless ax == ``propext || ax == ``Quot.sound do
      throwErrorAt id "constructive audit: forbidden axiom {ax}"
  liftTermElabM <| auditPremises ci
  if (stripBinders (ci.value! (allowOpaque := true))).getAppFn.isConstOf ``True.intro then
    throwErrorAt id "constructive audit: trivial True conclusion"
  return (n, ci)

syntax "#verify_constructive " ident+ : command
elab_rules : command
  | `(command| #verify_constructive $[$ids:ident]*) => do
    for id in ids do discard <| verifyConstructiveDecl id

private meta def domainConstants (e : Expr) : Array Name :=
  e.getUsedConstants.filter fun n =>
    (`Qsag).isPrefixOf n || [``BitVec, ``ByteArray, ``UInt8, ``UInt64].contains n

private meta def requireOverlap (a b : Expr) : MetaM Unit := do
  let common := (domainConstants a).filter (domainConstants b).contains
  if common.isEmpty then
    throwError "pair audit: no shared protocol/domain constants"

private meta partial def meaningfulWitness (e : Expr) : MetaM Bool := do
  if e.isConstOf ``True then return false
  if let some (_, a, b) := e.eq? then
    return !(← withoutModifyingState (isDefEq a b))
  if e.getAppFn.isConstOf ``And then
    return (← meaningfulWitness e.getAppArgs[0]!) || (← meaningfulWitness e.getAppArgs[1]!)
  if e.getAppFn.isConstOf ``Or then
    return (← meaningfulWitness e.getAppArgs[0]!) && (← meaningfulWitness e.getAppArgs[1]!)
  if e.getAppFn.isConstOf ``Exists then
    let args := e.getAppArgs
    return ← withLocalDeclD `_ args[0]! fun x => meaningfulWitness ((mkApp args[1]! x).headBeta)
  return true

private meta partial def refutationShape (e : Expr) : MetaM Bool := do
  let e := stripMData e
  if e.getAppFn.isConstOf ``Exists then return ← meaningfulWitness e
  if e.getAppFn.isConstOf ``Not then
    return !(← whnf e.getAppArgs[0]!).isConstOf ``False
  if e.getAppFn.isConstOf ``Ne then
    let args := e.getAppArgs
    return !(← withoutModifyingState (isDefEq args[1]! args[2]!))
  if let some (_, a, b) := e.eq? then
    if ← withoutModifyingState (isDefEq a b) then return false
    return #[a, b].any fun x =>
      x.isConstOf ``Bool.false || x.getAppFn.isConstOf ``Except.error ||
        x.getAppFn.isConstOf ``Option.none
  if let .forallE _ dom body _ := e then
    if body.isConstOf ``False then return true
    return ← withLocalDeclD `_ dom fun x => refutationShape (body.instantiate1 x)
  return false

private meta def checkToothPair (secId toothId : Ident) : CommandElabM Unit := do
  let (sn, s) ← verifyConstructiveDecl secId
  let (tn, t) ← verifyConstructiveDecl toothId
  if sn == tn || s.type == t.type then
    throwError "pair audit: declarations and propositions must be distinct"
  liftTermElabM do
    requireOverlap s.type t.type
    unless ← refutationShape t.type do
      throwError "pair audit: tooth has no counterexample/refutation conclusion"

syntax "#tooth_pair " ident " vs " ident : command
syntax "#tooth_pair " ident ident : command
elab_rules : command
  | `(command| #tooth_pair $s:ident vs $t:ident) => checkToothPair s t
  | `(command| #tooth_pair $s:ident $t:ident) => checkToothPair s t

private meta partial def witnessContains (premise e : Expr) : MetaM Bool := do
  if e.getAppFn.isConstOf ``Exists then
    let args := e.getAppArgs
    withLocalDeclD `_ args[0]! fun v => witnessContains premise ((mkApp args[1]! v).headBeta)
  else if e.getAppFn.isConstOf ``Nonempty then
    let carrier ← whnf e.getAppArgs[0]!
    unless carrier.getAppFn.isConstOf ``Subtype do return false
    let args := carrier.getAppArgs
    withLocalDeclD `_ args[0]! fun v => witnessContains premise ((mkApp args[1]! v).headBeta)
  else if e.getAppFn.isConstOf ``And then
    return (← witnessContains premise e.getAppArgs[0]!) ||
      (← witnessContains premise e.getAppArgs[1]!)
  else
    let (_, _, body) ← forallMetaTelescope premise
    withoutModifyingState (isDefEq body e)

/-- An inhabitedness witness must supply an existential containing an instance of an
actual security premise. Merely mentioning the same carrier is insufficient.
All witness Prop assumptions are rejected: a conditional witness does not establish
that the security precondition is reachable. Parameters of data types are allowed. -/
private meta def checkInhabited (s w : ConstantInfo) : MetaM Unit := do
  requireOverlap s.type w.type
  forallTelescope s.type fun sx _ => do
    forallTelescope w.type fun wx conclusion => do
      for x in wx do
        if ← isProp (← inferType x) then
          throwError "inhabitedness audit: witness has undischarged Prop assumptions"
      unless conclusion.getAppFn.isConstOf ``Exists || conclusion.getAppFn.isConstOf ``Nonempty do
        throwError "inhabitedness audit: expected an existential reachable-state witness"
      let mut matched := false
      for x in sx do
        let premise ← inferType x
        if ← isProp premise then
          let pred := premise.getAppFn
          if pred.isConst && ((`Qsag).isPrefixOf pred.constName!) then
            -- Match predicate applications under existential binders, not names alone.
            let generalized ← mkForallFVars sx premise
            if ← witnessContains generalized conclusion then matched := true
      unless matched do
        throwError "inhabitedness audit: existential does not discharge a protocol premise"

syntax "#verify_inhabited " ident ident : command
elab_rules : command
  | `(command| #verify_inhabited $s:ident $w:ident) => do
    let (_, sec) ← verifyConstructiveDecl s
    let (_, wit) ← verifyConstructiveDecl w
    liftTermElabM <| checkInhabited sec wit

/-! ### `by bv_xor_cancel` — Constructive XOR / Bitwise Canceller (`0 Classical.choice`) -/

/-- Reify XOR structure with hash-consed atoms; other bitwise operations stay opaque. -/
private meta partial def reifyXor (e zero : Expr)
    (atoms : Array Expr) (indices : Std.HashMap Expr Nat) :
    MetaM (Expr × Array Expr × Std.HashMap Expr Nat) := do
  let e := stripMData e
  let args := e.getAppArgs
  if (e.getAppFn.isConstOf ``HXor.hXor && args.size == 6) ||
      (e.getAppFn.isConstOf ``BitVec.xor && args.size == 3) then
    let (l, atoms, indices) ← reifyXor args[args.size - 2]! zero atoms indices
    let (r, atoms, indices) ← reifyXor args[args.size - 1]! zero atoms indices
    return (mkApp2 (mkConst ``Qsag.XorTree.xor) l r, atoms, indices)
  if ← withoutModifyingState (isDefEq e zero) then
    return (mkConst ``Qsag.XorTree.zero, atoms, indices)
  if let some i := indices[e]? then
    return (mkApp (mkConst ``Qsag.XorTree.atom) (mkNatLit i), atoms, indices)
  return (mkApp (mkConst ``Qsag.XorTree.atom) (mkNatLit atoms.size),
    atoms.push e, indices.insert e atoms.size)

/-- Balanced lookup keeps each reflected atom access logarithmic in the atom count. -/
private meta partial def atomLookup (xs : Array Expr) (index : Expr)
    (lo hi : Nat) : MetaM Expr := do
  if hi ≤ lo + 1 then return xs[lo]!
  let mid := (lo + hi) / 2
  let l ← atomLookup xs index lo mid
  let r ← atomLookup xs index mid hi
  let cond ← mkAppM ``Nat.blt #[index, mkNatLit mid]
  mkAppM ``cond #[cond, l, r]

private meta def solveReflectedXor (goal : MVarId) : TacticM Bool := goal.withContext do
  let some (ty, lhs, rhs) := (← instantiateMVars (← goal.getType)).eq? | return false
  unless ty.getAppFn.isConstOf ``BitVec do return false
  let width := ty.getAppArgs[0]!
  let zero ← mkAppM ``BitVec.ofNat #[width, mkNatLit 0]
  let (l, atoms, indices) ← reifyXor lhs zero #[] {}
  let (r, atoms, _) ← reifyXor rhs zero atoms indices
  let lookup ← withLocalDeclD `i (mkConst ``Nat) fun i => do
    let body ← if atoms.isEmpty then pure zero else atomLookup atoms i 0 atoms.size
    mkLambdaFVars #[i] body
  let lt ← mkAppM ``Qsag.XorTree.flatten #[l, ← mkListLit (mkConst ``Nat) []]
  let rt ← mkAppM ``Qsag.XorTree.flatten #[r, ← mkListLit (mkConst ``Nat) []]
  let ln ← mkAppM ``Qsag.xorNorm #[lt]
  let rn ← mkAppM ``Qsag.xorNorm #[rt]
  unless ← withTransparency .all (isDefEq ln rn) do return false
  let proof ← mkAppM ``Qsag.XorTree.norm_sound #[lookup, l, r, ← mkEqRefl ln]
  unless ← withTransparency .all (isDefEq (← inferType proof) (← goal.getType)) do return false
  goal.assign proof
  return true

/-- Collect distinct non-literal `Bool`-typed subexpressions inside a bit-level expression. -/
private meta partial def collectBoolAtoms (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
  let e := stripMData e
  if e.isConstOf ``Bool.true || e.isConstOf ``Bool.false then
    return acc
  let fn := stripMData e.getAppFn
  let args := e.getAppArgs
  if (fn.isConstOf ``HXor.hXor || fn.isConstOf ``HAnd.hAnd || fn.isConstOf ``HOr.hOr) &&
      args.size == 6 then
    let acc ← collectBoolAtoms args[4]! acc
    return (← collectBoolAtoms args[5]! acc)
  if (fn.isConstOf ``bne || fn.isConstOf ``BEq.beq) && args.size >= 2 then
    let acc ← collectBoolAtoms args[args.size - 2]! acc
    return (← collectBoolAtoms args[args.size - 1]! acc)
  if (fn.isConstOf ``Bool.xor || fn.isConstOf ``Bool.and || fn.isConstOf ``Bool.or) && args.size == 2 then
    let acc ← collectBoolAtoms args[0]! acc
    return (← collectBoolAtoms args[1]! acc)
  if fn.isConstOf ``Bool.not && args.size == 1 then
    return (← collectBoolAtoms args[0]! acc)
  let ty ← inferType e
  if ← withoutModifyingState (isDefEq ty (mkConst ``Bool)) then
    for prev in acc do
      if ← withoutModifyingState (isDefEq prev e) then
        return acc
    return acc.push e
  return acc

/-- Split generalized `Bool` atoms constructively via `Bool.casesOn` and close leaves by `rfl`. -/
private meta partial def splitBoolAtomsAndClose (atoms : List Expr) (goal : MVarId) :
    TacticM (List MVarId) :=
  goal.withContext do
    if ← goal.isAssigned then return []
    let closed ← withoutModifyingState do
      try
        let rem ← evalTacticAt (← `(tactic| rfl)) goal
        pure rem.isEmpty
      catch _ =>
        pure false
    if closed then
      return (← evalTacticAt (← `(tactic| rfl)) goal)
    match atoms with
    | [] =>
      evalTacticAt (← `(tactic| first | rfl | decide)) goal
    | a :: rest =>
      let a ← instantiateMVars a
      let (fvars, goalGen) ← goal.generalize #[{ expr := a, xName? := some `_bAtom }]
      goalGen.withContext do
        let targetFVar? : Option FVarId :=
          match fvars[0]? with
          | some fid => some fid
          | none => if a.isFVar then some a.fvarId! else none
        let some fvarId := targetFVar? | return [goalGen]
        let subgoals ← goalGen.cases fvarId
        let mut unpaid : List MVarId := []
        for sg in subgoals do
          unpaid := unpaid ++ (← splitBoolAtomsAndClose rest sg.mvarId)
        return unpaid

/-- Solve a bit-reduced `Bool` equality goal by splitting its `Bool` atoms constructively. -/
private meta def solveBitBoolEqGoal (goal : MVarId) : TacticM (List MVarId) :=
  goal.withContext do
    if ← goal.isAssigned then return []
    let tgt ← instantiateMVars (← goal.getType)
    let some (_, lhs, rhs) := tgt.eq? | return [goal]
    let atoms ← collectBoolAtoms lhs #[]
    let atoms ← collectBoolAtoms rhs atoms
    splitBoolAtomsAndClose atoms.toList goal

/-- Fast constructive algebraic XOR rewrite step over `BitVec`, `UInt64`, `UInt8`, and `Bool`. -/
private meta def runAlgebraicXorSimp (goal : MVarId) : TacticM (List MVarId) := do
  let stx ← `(tactic| (
    try simp only [
      Qsag.bv_xor_self, Qsag.bv_xor_zero, Qsag.bv_zero_xor,
      Qsag.bv_xor_cancel_right, Qsag.bv_xor_cancel_left, Qsag.bv_xor_cancel_mid,
      Qsag.bv_xor_cancel_outer,
      Qsag.u64_xor_self, Qsag.u64_xor_zero, Qsag.u64_zero_xor,
      Qsag.u64_xor_cancel_right, Qsag.u64_xor_cancel_left, Qsag.u64_xor_cancel_mid,
      Qsag.u64_xor_cancel_outer,
      Qsag.u8_xor_self, Qsag.u8_xor_zero, Qsag.u8_zero_xor,
      Qsag.u8_xor_cancel_right, Qsag.u8_xor_cancel_left, Qsag.u8_xor_cancel_mid,
      Qsag.u8_xor_cancel_outer,
      Qsag.bool_xor_self, Qsag.bool_xor_false, Qsag.bool_false_xor,
      Qsag.bool_xor_cancel_right, Qsag.bool_xor_cancel_left, Qsag.bool_xor_cancel_mid,
      Qsag.bool_xor_cancel_outer,
      Qsag.bool_bne_self, Qsag.bool_bne_false, Qsag.bool_false_bne,
      Qsag.bool_bne_cancel_right, Qsag.bool_bne_cancel_left, Qsag.bool_bne_cancel_mid,
      Qsag.bool_bne_cancel_outer
    ]
    try simp only [
      Qsag.bv_xor_assoc, Qsag.bv_xor_self, Qsag.bv_xor_zero, Qsag.bv_zero_xor,
      Qsag.bv_xor_cancel_right, Qsag.bv_xor_cancel_left, Qsag.bv_xor_cancel_mid,
      Qsag.bv_xor_cancel_outer,
      Qsag.u64_xor_assoc, Qsag.u64_xor_self, Qsag.u64_xor_zero, Qsag.u64_zero_xor,
      Qsag.u64_xor_cancel_right, Qsag.u64_xor_cancel_left, Qsag.u64_xor_cancel_mid,
      Qsag.u64_xor_cancel_outer,
      Qsag.u8_xor_assoc, Qsag.u8_xor_self, Qsag.u8_xor_zero, Qsag.u8_zero_xor,
      Qsag.u8_xor_cancel_right, Qsag.u8_xor_cancel_left, Qsag.u8_xor_cancel_mid,
      Qsag.u8_xor_cancel_outer,
      Qsag.bool_xor_assoc, Qsag.bool_xor_self, Qsag.bool_xor_false, Qsag.bool_false_xor,
      Qsag.bool_xor_cancel_right, Qsag.bool_xor_cancel_left, Qsag.bool_xor_cancel_mid,
      Qsag.bool_xor_cancel_outer,
      Qsag.bool_bne_assoc, Qsag.bool_bne_self, Qsag.bool_bne_false, Qsag.bool_false_bne,
      Qsag.bool_bne_cancel_right, Qsag.bool_bne_cancel_left, Qsag.bool_bne_cancel_mid,
      Qsag.bool_bne_cancel_outer
    ]
    try rfl
  ))
  evalTacticAt stx goal

/-- Bit-blast or congruence-peel a single remaining equality subgoal with bounded fuel. -/
private meta def solveSingleXorGoalAux : Nat → MVarId → TacticM (List MVarId)
  | 0, goal => runAlgebraicXorSimp goal
  | fuel + 1, goal =>
    goal.withContext do
      if ← goal.isAssigned then return []
      if ← solveReflectedXor goal then return []
      let rem ← runAlgebraicXorSimp goal
      if rem.isEmpty then return []
      let mut out : List MVarId := []
      for g in rem do
        if !(← g.isAssigned) then
          let gSub ← g.withContext do
            let tgt ← instantiateMVars (← g.getType)
            match tgt.eq? with
            | none => return [g]
            | some (eqTyRaw, _, _) =>
              let eqTy := stripMData (← whnf eqTyRaw)
              if eqTy.isConstOf ``UInt64 then
                let stx ← `(tactic| (
                  apply UInt64.eq_of_toBitVec_eq
                  apply Qsag.bv_eq_of_getLsbD_eq
                  intro _i _hi
                  simp only [Qsag.u64_toBitVec_xor, Qsag.u64_toBitVec_zero,
                    BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_or,
                    BitVec.getLsbD_zero, Qsag.Constructive.getLsbD_allOnes,
                    Qsag.Constructive.getLsbD_not, _hi, decide_true, Bool.true_and]
                ))
                let gs ← evalTacticAt stx g
                let mut gOut : List MVarId := []
                for sg in gs do
                  gOut := gOut ++ (← solveBitBoolEqGoal sg)
                return gOut
              else if eqTy.isConstOf ``UInt8 then
                let stx ← `(tactic| (
                  apply UInt8.eq_of_toBitVec_eq
                  apply Qsag.bv_eq_of_getLsbD_eq
                  intro _i _hi
                  simp only [Qsag.u8_toBitVec_xor, Qsag.u8_toBitVec_zero,
                    BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_or,
                    BitVec.getLsbD_zero, Qsag.Constructive.getLsbD_allOnes,
                    Qsag.Constructive.getLsbD_not, _hi, decide_true, Bool.true_and]
                ))
                let gs ← evalTacticAt stx g
                let mut gOut : List MVarId := []
                for sg in gs do
                  gOut := gOut ++ (← solveBitBoolEqGoal sg)
                return gOut
              else if (stripMData eqTy.getAppFn).isConstOf ``BitVec then
                let stx ← `(tactic| (
                  apply Qsag.bv_eq_of_getLsbD_eq
                  intro _i _hi
                  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_or,
                    BitVec.getLsbD_zero, Qsag.Constructive.getLsbD_allOnes,
                    Qsag.Constructive.getLsbD_not, _hi, decide_true, Bool.true_and]
                ))
                let gs ← evalTacticAt stx g
                let mut gOut : List MVarId := []
                for sg in gs do
                  gOut := gOut ++ (← solveBitBoolEqGoal sg)
                return gOut
              else if eqTy.isConstOf ``Bool then
                return (← solveBitBoolEqGoal g)
              else
                let gs ← evalTacticAt (← `(tactic| try congr 1)) g
                if gs == [g] then
                  return [g]
                else
                  let mut gOut : List MVarId := []
                  for sg in gs do
                    gOut := gOut ++ (← solveSingleXorGoalAux fuel sg)
                  return gOut
          out := out ++ gSub
      return out

/-- Reduce a single `BitVec w`, `UInt64`, `UInt8`, or `Bool` equality goal to bit-level `Bool`
    atoms and discharge it with `0 Classical.choice` and `0 ofReduceBool`. -/
private meta def solveSingleXorGoal (goal : MVarId) : TacticM (List MVarId) :=
  solveSingleXorGoalAux 6 goal

private meta def xorSyntaxDepth : Expr → Nat
  | .app f a => 1 + max (xorSyntaxDepth f) (xorSyntaxDepth a)
  | .lam _ t b _ | .forallE _ t b _ => 1 + max (xorSyntaxDepth t) (xorSyntaxDepth b)
  | .letE _ t v b _ => 1 + max (xorSyntaxDepth t) (max (xorSyntaxDepth v) (xorSyntaxDepth b))
  | .mdata _ e | .proj _ _ e => 1 + xorSyntaxDepth e
  | _ => 1

/-- `by bv_xor_cancel`: discharges XOR one-time-pad and bitwise cancellation equalities over
    `BitVec w` (including polymorphic width `w : Nat`), `UInt64`, `UInt8`, and `Bool`
    constructively (`0 Classical.choice`, `0 ofReduceBool`, `0 native_decide`). -/
elab "bv_xor_cancel" : tactic => do
  let goal ← getMainGoal
  -- Left-associated source expressions need stack proportional to their syntax,
  -- even though normalization work is O(k log k). Keep Lean's caller budget if larger.
  let depth := 32 * xorSyntaxDepth (← goal.getType) + 1024
  let rem ← withOptions (fun opts => maxRecDepth.set opts (max (maxRecDepth.get opts) depth)) <| solveSingleXorGoal goal
  replaceMainGoal rem

/-! ### `by compose_forward_sim` — Compositional `ForwardSim` & `LockstepSim` Spine Synthesizer -/

/-- Coerce a `ForwardSim` or `LockstepSim` expression into `(srcMachine, dstMachine, forwardSimExpr)`. -/
private meta def asForwardSimLink? (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let ty := stripMData (← instantiateMVars (← inferType e))
  let fn := stripMData ty.getAppFn
  let args := ty.getAppArgs
  if fn.isConstOf ``Qsag.ForwardSim && args.size >= 2 then
    return some (args[args.size - 2]!, args[args.size - 1]!, e)
  if fn.isConstOf ``Qsag.LockstepSim && args.size >= 2 then
    let fsExpr ← mkAppM ``Qsag.LockstepSim.toForwardSim #[e]
    return some (args[args.size - 2]!, args[args.size - 1]!, fsExpr)
  return none

/-- Bounded DFS search over local `ForwardSim` / `LockstepSim` links to connect `curM` to `endM`. -/
private meta partial def searchForwardSimPath (fuel : Nat) (used : Array FVarId)
    (links : Array (FVarId × Expr × Expr × Expr)) (curM endM : Expr) : MetaM (Option Expr) := do
  if ← withoutModifyingState (isDefEq curM endM) then
    let _ ← isDefEq curM endM
    return some (← mkAppM ``Qsag.ForwardSim.refl #[curM])
  match fuel with
  | 0 => return none
  | fuel' + 1 =>
    for (fid, srcM, dstM, linkExpr) in links do
      if used.contains fid then continue
      if ← withoutModifyingState (isDefEq curM srcM) then
        if ← withoutModifyingState (isDefEq dstM endM) then
          let _ ← isDefEq curM srcM
          let _ ← isDefEq dstM endM
          return some linkExpr
        let tail? ← withoutModifyingState do
          let _ ← isDefEq curM srcM
          searchForwardSimPath fuel' (used.push fid) links dstM endM
        if tail?.isSome then
          let _ ← isDefEq curM srcM
          if let some tailExpr ← searchForwardSimPath fuel' (used.push fid) links dstM endM then
            return some (← mkAppM ``Qsag.ForwardSim.trans #[linkExpr, tailExpr])
    return none

syntax "compose_forward_sim" (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| compose_forward_sim [$[$ts:term],*]) => do
    let goal ← getMainGoal
    goal.withContext do
      let tgt := stripMData (← instantiateMVars (← goal.getType))
      let args := tgt.getAppArgs
      unless (stripMData tgt.getAppFn).isConstOf ``Qsag.ForwardSim && args.size >= 2 do
        throwError "compose_forward_sim: goal `{tgt}` is not a `Qsag.ForwardSim C A`"
      let startM := args[args.size - 2]!
      if ts.isEmpty then
        let reflExpr ← mkAppM ``Qsag.ForwardSim.refl #[startM]
        unless ← isDefEq (← goal.getType) (← inferType reflExpr) do
          throwError "compose_forward_sim []: machines are not definitionally equal"
        goal.assign reflExpr
        replaceMainGoal []
      else
        let mut chainExpr? : Option Expr := none
        for t in ts do
          let raw ← Tactic.elabTerm t none
          let some (_, _, fsLink) ← asForwardSimLink? raw
            | throwErrorAt t "compose_forward_sim: `{t}` has type `{← inferType raw}`, expected `ForwardSim` or `LockstepSim`"
          match chainExpr? with
          | none => chainExpr? := some fsLink
          | some prev => chainExpr? := some (← mkAppM ``Qsag.ForwardSim.trans #[prev, fsLink])
        let some finalChain := chainExpr? | unreachable!
        unless ← isDefEq (← goal.getType) (← inferType finalChain) do
          throwError "compose_forward_sim: composed spine has type `{← inferType finalChain}`, expected `{← goal.getType}`"
        goal.assign finalChain
        replaceMainGoal []
  | `(tactic| compose_forward_sim) => do
    let goal ← getMainGoal
    goal.withContext do
      let tgt := stripMData (← instantiateMVars (← goal.getType))
      let args := tgt.getAppArgs
      unless (stripMData tgt.getAppFn).isConstOf ``Qsag.ForwardSim && args.size >= 2 do
        throwError "compose_forward_sim: goal `{tgt}` is not a `Qsag.ForwardSim C A`"
      let startM := args[args.size - 2]!
      let endM := args[args.size - 1]!
      let mut links : Array (FVarId × Expr × Expr × Expr) := #[]
      for ldecl in ← getLCtx do
        if ldecl.isImplementationDetail then continue
        if let some (srcM, dstM, fsExpr) ← asForwardSimLink? ldecl.toExpr then
          links := links.push (ldecl.fvarId, srcM, dstM, fsExpr)
      let some proof ← searchForwardSimPath (links.size + 1) #[] links startM endM
        | throwError "compose_forward_sim: could not find a `ForwardSim`/`LockstepSim` path from `{startM}` to `{endM}` in local context"
      unless ← isDefEq (← goal.getType) (← inferType proof) do
        throwError "compose_forward_sim: synthesized proof type mismatch"
      goal.assign proof
      replaceMainGoal []

private meta partial def framingConclusion (ty : Expr) : MetaM Expr := do
  for decl in ← getLCtx do
    if ← isDefEq decl.type ty then return decl.toExpr
  if ty.getAppFn.isConstOf ``And then
    let args := ty.getAppArgs
    mkAppM ``And.intro #[← framingConclusion args[0]!, ← framingConclusion args[1]!]
  else throwError "frame_prefix_inj: cannot derive {ty} from framed equalities"

/-- Peel all framed equalities in the context, preserving every remainder. -/
elab "frame_prefix_inj" : tactic => do
  evalTactic (← `(tactic| simp only [List.append_assoc] at *))
  let mut pending := true
  while pending do
    pending := false
    let goal ← getMainGoal
    pending ← goal.withContext do
      for decl in ← getLCtx do
        if decl.isImplementationDetail then continue
        let some (_, lhs, _) := decl.type.eq? | continue
        let isFrame := lhs.getAppFn.isConstOf ``Qsag.frameList
        let args := lhs.getAppArgs
        let isAppend := lhs.getAppFn.isConstOf ``HAppend.hAppend && args.size == 6 &&
          args[4]!.getAppFn.isConstOf ``Qsag.frameList
        unless isFrame || isAppend do continue
        let proof? ← try
          pure <| some (← mkAppM (if isFrame then ``Qsag.frameList_inj
            else ``Qsag.frameList_append_inj) #[decl.toExpr])
          catch _ => pure none
        if let some proof := proof? then
          let next ← goal.assert `_frameParts (← inferType proof) proof
          let (fid, next) ← next.intro1
          let next ← next.clear decl.fvarId
          if isFrame then replaceMainGoal [next]
          else
            let cases ← next.cases fid
            replaceMainGoal (cases.toList.map (·.mvarId))
          return true
      return false
  let goal ← getMainGoal
  goal.withContext do
    goal.assign (← framingConclusion (← goal.getType))
  replaceMainGoal []

/-- Symbolically split monadic results, retaining equations for each branch. -/
private meta partial def mirStep (goal : MVarId) : TacticM (List MVarId) := do
  let rem ← evalTacticAt (← `(tactic| first
    | compose_forward_sim
    | (solve | simp_all)
    | skip)) goal
  if rem.isEmpty then return []
  goal.withContext do
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let ty ← whnf decl.type
      if ty.getAppFn.isConstOf ``Option || ty.getAppFn.isConstOf ``Except then
        let cases ← goal.cases decl.fvarId
        let mut out := []
        for c in cases do out := out ++ (← mirStep c.mvarId)
        return out
    return ← evalTacticAt (← `(tactic| simp_all [Bind.bind, Option.bind, Except.bind])) goal

elab "mir_sim_step" : tactic => do
  replaceMainGoal (← mirStep (← getMainGoal))

/-! ### `by mask_bijection_hop` — Constructive `SimpleEquiv` & `finSum` Pad-Bijection Synthesizer -/

/-- Search an expression `body` for `SimpleEquiv.toFun _ _ enum _`, returning `enum`. -/
private meta partial def findEnumInExpr? (e : Expr) : Option Expr :=
  let e := stripMData e
  let fn := stripMData e.getAppFn
  let args := e.getAppArgs
  if fn.isConstOf ``Qsag.SimpleEquiv.toFun && args.size == 4 then
    some args[2]!
  else
    args.findSome? findEnumInExpr? <|>
      match e with
      | .lam _ _ b _ => findEnumInExpr? b
      | .letE _ _ v b _ => findEnumInExpr? v <|> findEnumInExpr? b
      | .proj _ _ inner => findEnumInExpr? inner
      | _ => none

/-- Check whether `sub` is definitionally equal to `sampleExpr`. -/
private meta def matchesSample (sub sampleExpr : Expr) : MetaM Bool :=
  withoutModifyingState (isDefEq (stripMData sub) (stripMData sampleExpr))

/-- Search `body` for a mask expression `mask ^^^ sampleExpr`, `sampleExpr ^^^ mask`,
    `mask != sampleExpr`, or `sampleExpr != mask` applied to `sampleExpr`. -/
private meta partial def findXorMaskForSample? (body sampleExpr : Expr) : MetaM (Option Expr) := do
  let body := stripMData body
  let fn := stripMData body.getAppFn
  let args := body.getAppArgs
  if fn.isConstOf ``HXor.hXor && args.size == 6 then
    let lhs := args[4]!
    let rhs := args[5]!
    if ← matchesSample rhs sampleExpr then
      if !(lhs.hasLooseBVars) then return some lhs
    if ← matchesSample lhs sampleExpr then
      if !(rhs.hasLooseBVars) then return some rhs
  if fn.isConstOf ``bne && args.size == 4 then
    let lhs := args[2]!
    let rhs := args[3]!
    if ← matchesSample rhs sampleExpr then
      if !(lhs.hasLooseBVars) then return some lhs
    if ← matchesSample lhs sampleExpr then
      if !(rhs.hasLooseBVars) then return some rhs
  if fn.isConstOf ``Bool.xor && args.size == 2 then
    let lhs := args[0]!
    let rhs := args[1]!
    if ← matchesSample rhs sampleExpr then
      if !(lhs.hasLooseBVars) then return some lhs
    if ← matchesSample lhs sampleExpr then
      if !(rhs.hasLooseBVars) then return some rhs
  for a in args do
    if let some m ← findXorMaskForSample? a sampleExpr then
      return some m
  match body with
  | .letE _ _ v b _ =>
    if let some m ← findXorMaskForSample? v sampleExpr then return some m
    return (← findXorMaskForSample? (b.instantiate1 v) sampleExpr)
  | .proj _ _ inner => findXorMaskForSample? inner sampleExpr
  | _ => return none

/-- Synthesize a `SimpleEquiv Ω Ω` pad bijection for sample `sampleExpr : Ω` appearing in `body`. -/
private meta partial def synthesizePadEquiv (omegaTy body sampleExpr : Expr) : MetaM Expr := do
  let omegaWhnf := stripMData (← whnf omegaTy)
  let fn := stripMData omegaWhnf.getAppFn
  let args := omegaWhnf.getAppArgs
  if fn.isConstOf ``Prod && args.size == 2 then
    let fstSample ← mkAppM ``Prod.fst #[sampleExpr]
    let sndSample ← mkAppM ``Prod.snd #[sampleExpr]
    let e1 ← synthesizePadEquiv args[0]! body fstSample
    let e2 ← synthesizePadEquiv args[1]! body sndSample
    return (← mkAppM ``Qsag.SimpleEquiv.prodCongr #[e1, e2])
  if fn.isConstOf ``BitVec && args.size == 1 then
    if let some mask ← findXorMaskForSample? body sampleExpr then
      return (← mkAppM ``Qsag.bvXorEquiv #[mask])
    return (← mkAppM ``Qsag.SimpleEquiv.refl #[omegaTy])
  if omegaWhnf.isConstOf ``UInt64 then
    if let some mask ← findXorMaskForSample? body sampleExpr then
      return (← mkAppM ``Qsag.u64XorEquiv #[mask])
    return (← mkAppM ``Qsag.SimpleEquiv.refl #[omegaTy])
  if omegaWhnf.isConstOf ``Bool then
    if let some mask ← findXorMaskForSample? body sampleExpr then
      return (← mkAppM ``Qsag.boolXorEquiv #[mask])
    return (← mkAppM ``Qsag.SimpleEquiv.refl #[omegaTy])
  return (← mkAppM ``Qsag.SimpleEquiv.refl #[omegaTy])

/-- Discharge the pointwise obligation produced by `finSum_bijection_hop_eq`. -/
private meta def dischargeMaskPointwise (goal : MVarId) : TacticM (List MVarId) := do
  let (omegaFVar, goalIntro) ← goal.intro `_ω
  let isProd ← goalIntro.withContext do
    let ty ← whnf (← omegaFVar.getType)
    pure ((stripMData ty.getAppFn).isConstOf ``Prod && ty.getAppArgs.size == 2)
  let postIntroGoals ←
    if isProd then
      let subgs ← goalIntro.cases omegaFVar
      pure (subgs.toList.map (·.mvarId))
    else
      pure [goalIntro]
  let stx ← `(tactic| (
    try dsimp only [
      Qsag.SimpleEquiv.prodCongr, Qsag.SimpleEquiv.refl, Qsag.SimpleEquiv.symm,
      Qsag.SimpleEquiv.trans, Qsag.bvXorEquiv, Qsag.u64XorEquiv, Qsag.boolXorEquiv,
      Qsag.ringAddEquiv
    ]
    try simp only [
      Qsag.SimpleEquiv.refl_toFun, Qsag.SimpleEquiv.symm_toFun,
      Qsag.SimpleEquiv.trans_toFun, Qsag.SimpleEquiv.prodCongr_toFun,
      Qsag.bvXorEquiv_toFun, Qsag.u64XorEquiv_toFun, Qsag.boolXorEquiv_toFun,
      Qsag.ringAddEquiv_toFun
    ]
    try simp only [
      Qsag.bv_xor_self, Qsag.bv_xor_zero, Qsag.bv_zero_xor,
      Qsag.bv_xor_cancel_right, Qsag.bv_xor_cancel_left, Qsag.bv_xor_cancel_mid,
      Qsag.bv_xor_cancel_outer,
      Qsag.u64_xor_self, Qsag.u64_xor_zero, Qsag.u64_zero_xor,
      Qsag.u64_xor_cancel_right, Qsag.u64_xor_cancel_left, Qsag.u64_xor_cancel_mid,
      Qsag.u64_xor_cancel_outer,
      Qsag.u8_xor_self, Qsag.u8_xor_zero, Qsag.u8_zero_xor,
      Qsag.u8_xor_cancel_right, Qsag.u8_xor_cancel_left, Qsag.u8_xor_cancel_mid,
      Qsag.u8_xor_cancel_outer,
      Qsag.bool_xor_self, Qsag.bool_xor_false, Qsag.bool_false_xor,
      Qsag.bool_xor_cancel_right, Qsag.bool_xor_cancel_left, Qsag.bool_xor_cancel_mid,
      Qsag.bool_xor_cancel_outer,
      Qsag.bool_bne_self, Qsag.bool_bne_false, Qsag.bool_false_bne,
      Qsag.bool_bne_cancel_right, Qsag.bool_bne_cancel_left, Qsag.bool_bne_cancel_mid,
      Qsag.bool_bne_cancel_outer,
      Qsag.ring_add_sub_cancel_right, Qsag.ring_sub_add_cancel_right
    ]
    try simp only [
      Qsag.bv_xor_assoc, Qsag.bv_xor_self, Qsag.bv_xor_zero, Qsag.bv_zero_xor,
      Qsag.bv_xor_cancel_right, Qsag.bv_xor_cancel_left, Qsag.bv_xor_cancel_mid,
      Qsag.bv_xor_cancel_outer,
      Qsag.u64_xor_assoc, Qsag.u64_xor_self, Qsag.u64_xor_zero, Qsag.u64_zero_xor,
      Qsag.u64_xor_cancel_right, Qsag.u64_xor_cancel_left, Qsag.u64_xor_cancel_mid,
      Qsag.u64_xor_cancel_outer,
      Qsag.u8_xor_assoc, Qsag.u8_xor_self, Qsag.u8_xor_zero, Qsag.u8_zero_xor,
      Qsag.u8_xor_cancel_right, Qsag.u8_xor_cancel_left, Qsag.u8_xor_cancel_mid,
      Qsag.u8_xor_cancel_outer,
      Qsag.bool_xor_assoc, Qsag.bool_xor_self, Qsag.bool_xor_false, Qsag.bool_false_xor,
      Qsag.bool_xor_cancel_right, Qsag.bool_xor_cancel_left, Qsag.bool_xor_cancel_mid,
      Qsag.bool_xor_cancel_outer,
      Qsag.bool_bne_assoc, Qsag.bool_bne_self, Qsag.bool_bne_false, Qsag.bool_false_bne,
      Qsag.bool_bne_cancel_right, Qsag.bool_bne_cancel_left, Qsag.bool_bne_cancel_mid,
      Qsag.bool_bne_cancel_outer
    ]
    try rfl
  ))
  let mut rem : List MVarId := []
  for pg in postIntroGoals do
    let gs ← evalTacticAt stx pg
    for g in gs do
      if !(← g.isAssigned) then
        rem := rem ++ (← solveSingleXorGoal g)
  return rem

/-- Abstract `(enum.toFun idx)` out of a `finSum C (fun idx => body)` integrand to form `Ω → Nat`. -/
private meta def extractFinSumWeightFn (omegaTy enumExpr sumExpr : Expr) : MetaM Expr := do
  let args := (stripMData sumExpr).getAppArgs
  unless (stripMData sumExpr.getAppFn).isConstOf ``Qsag.finSum && args.size == 2 do
    throwError "mask_bijection_hop: `{sumExpr}` is not a `Qsag.finSum` application"
  let lamFn ← whnf args[1]!
  match stripMData lamFn with
  | .lam nm dom body bi =>
    withLocalDecl nm bi dom fun idxVar => do
      let bodyInst ← instantiateMVars (body.instantiate1 idxVar)
      let sampleExpr ← mkAppM ``Qsag.SimpleEquiv.toFun #[enumExpr, idxVar]
      let absBody ← kabstract bodyInst sampleExpr
      if absBody.hasLooseBVars then
        -- `kabstract` turned `sampleExpr` into `.bvar 0`; verify `idxVar` no longer occurs freely
        let checkClosed := absBody.instantiate1 (mkBVar 0)
        let _ := checkClosed
      if (absBody.instantiate1 enumExpr).containsFVar idxVar.fvarId! then
        throwError "mask_bijection_hop: `finSum` body depends on loop index `{nm}` outside `enum.toFun`"
      return Expr.lam `_ω omegaTy absBody .default
  | _ =>
    throwError "mask_bijection_hop: expected lambda integrand inside `finSum`"

syntax "mask_bijection_hop" (ppSpace term)? : tactic

elab_rules : tactic
  | `(tactic| mask_bijection_hop $eStx:term) => do
    let goal ← getMainGoal
    goal.withContext do
      let tgt := stripMData (← instantiateMVars (← goal.getType))
      let some (_, lhs, rhs) := tgt.eq?
        | throwError "mask_bijection_hop: expected `finSum C ... = finSum C ...` equality goal"
      let some enumExpr := findEnumInExpr? lhs <|> findEnumInExpr? rhs
        | throwError "mask_bijection_hop: could not locate `enum.toFun` inside `finSum` goal"
      let enumTy := stripMData (← whnf (← inferType enumExpr))
      unless (stripMData enumTy.getAppFn).isConstOf ``Qsag.SimpleEquiv && enumTy.getAppArgs.size == 2 do
        throwError "mask_bijection_hop: `{enumExpr}` is not a `SimpleEquiv`"
      let omegaTy := enumTy.getAppArgs[1]!
      let fExpr ← extractFinSumWeightFn omegaTy enumExpr lhs
      let gExpr ← extractFinSumWeightFn omegaTy enumExpr rhs
      let eExpr ← Tactic.elabTermEnsuringType eStx (← mkAppM ``Qsag.SimpleEquiv #[omegaTy, omegaTy])
      let hopThm ← mkAppOptM ``Qsag.finSum_bijection_hop_eq
        #[some omegaTy, none, some enumExpr, some eExpr, some fExpr, some gExpr]
      let subgoals ← goal.apply hopThm
      let mut rem : List MVarId := []
      for sg in subgoals do
        rem := rem ++ (← dischargeMaskPointwise sg)
      replaceMainGoal rem
  | `(tactic| mask_bijection_hop) => do
    let goal ← getMainGoal
    goal.withContext do
      let tgt := stripMData (← instantiateMVars (← goal.getType))
      if (stripMData tgt.getAppFn).isConstOf ``Qsag.SimpleEquiv && tgt.getAppArgs.size == 2 then
        let a := tgt.getAppArgs[0]!
        let b := tgt.getAppArgs[1]!
        if ← isDefEq a b then
          let reflEq ← mkAppM ``Qsag.SimpleEquiv.refl #[a]
          goal.assign reflEq
          replaceMainGoal []
          return
      let some (_, lhs, rhs) := tgt.eq?
        | throwError "mask_bijection_hop: expected `finSum` equality or `SimpleEquiv` goal"
      let lhsArgs := lhs.getAppArgs
      unless (stripMData lhs.getAppFn).isConstOf ``Qsag.finSum && lhsArgs.size == 2 do
        throwError "mask_bijection_hop: LHS `{lhs}` is not a `Qsag.finSum` application"
      let some enumExpr := findEnumInExpr? lhs <|> findEnumInExpr? rhs
        | throwError "mask_bijection_hop: could not locate `enum.toFun` inside `finSum` goal"
      let enumTy := stripMData (← whnf (← inferType enumExpr))
      unless (stripMData enumTy.getAppFn).isConstOf ``Qsag.SimpleEquiv && enumTy.getAppArgs.size == 2 do
        throwError "mask_bijection_hop: `{enumExpr}` is not a `SimpleEquiv`"
      let omegaTy := enumTy.getAppArgs[1]!
      let fExpr ← extractFinSumWeightFn omegaTy enumExpr lhs
      let gExpr ← extractFinSumWeightFn omegaTy enumExpr rhs
      let lamFn ← whnf lhsArgs[1]!
      let eExpr ← match stripMData lamFn with
        | .lam nm dom body bi =>
          withLocalDecl nm bi dom fun idxVar => do
            let bodyInst := body.instantiate1 idxVar
            let sampleExpr ← mkAppM ``Qsag.SimpleEquiv.toFun #[enumExpr, idxVar]
            synthesizePadEquiv omegaTy bodyInst sampleExpr
        | _ => mkAppM ``Qsag.SimpleEquiv.refl #[omegaTy]
      let hopThm ← mkAppOptM ``Qsag.finSum_bijection_hop_eq
        #[some omegaTy, none, some enumExpr, some eExpr, some fExpr, some gExpr]
      let subgoals ← goal.apply hopThm
      let mut rem : List MVarId := []
      for sg in subgoals do
        rem := rem ++ (← dischargeMaskPointwise sg)
      replaceMainGoal rem

end Qsag.Tactic.AssuranceKit

/-! ## 4. Self-Tests of `#verify_constructive` & Constructive Automation -/

namespace Qsag

/-- Smoke test: `bv_xor_cancel` cancels permuted 4-party shares on polymorphic width `w : Nat`. -/
theorem bv_three_share_fault_shift {w : Nat} (s0 s1 s2 delta : BitVec w) :
    ((s0 ^^^ delta) ^^^ s1) ^^^ s2 = (((s0 ^^^ s1) ^^^ s2) ^^^ delta) := by
  bv_xor_cancel

#verify_constructive
  Qsag.bv_eq_of_getLsbD_eq
  Qsag.bv_three_share_fault_shift
  Qsag.finSum_bijection_hop_eq

/-! End-to-end regressions: each audited proof is kernel-checked, including the
large reflected goal and both successful/error monadic branches. -/
theorem xor_rss16 (a b c d e f g h i j k l m n o p : BitVec 256) :
    (a ^^^ b ^^^ c ^^^ d ^^^ e ^^^ f ^^^ g ^^^ h ^^^ i ^^^ j ^^^ k ^^^ l ^^^ m ^^^ n ^^^ o ^^^ p) ^^^
    (p ^^^ n ^^^ l ^^^ j ^^^ h ^^^ f ^^^ d ^^^ b ^^^ o ^^^ m ^^^ k ^^^ i ^^^ g ^^^ e ^^^ c ^^^ a) = 0 := by
  bv_xor_cancel

theorem xor_rss32 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 : BitVec 256) :
    (a0 ^^^ a1 ^^^ a2 ^^^ a3 ^^^ a4 ^^^ a5 ^^^ a6 ^^^ a7 ^^^ a8 ^^^ a9 ^^^ a10 ^^^ a11 ^^^ a12 ^^^ a13 ^^^ a14 ^^^ a15 ^^^ a16 ^^^ a17 ^^^ a18 ^^^ a19 ^^^ a20 ^^^ a21 ^^^ a22 ^^^ a23 ^^^ a24 ^^^ a25 ^^^ a26 ^^^ a27 ^^^ a28 ^^^ a29 ^^^ a30 ^^^ a31) ^^^
    (a0 ^^^ a2 ^^^ a4 ^^^ a6 ^^^ a8 ^^^ a10 ^^^ a12 ^^^ a14 ^^^ a16 ^^^ a18 ^^^ a20 ^^^ a22 ^^^ a24 ^^^ a26 ^^^ a28 ^^^ a30 ^^^ a31 ^^^ a29 ^^^ a27 ^^^ a25 ^^^ a23 ^^^ a21 ^^^ a19 ^^^ a17 ^^^ a15 ^^^ a13 ^^^ a11 ^^^ a9 ^^^ a7 ^^^ a5 ^^^ a3 ^^^ a1) = 0 := by
  bv_xor_cancel

theorem frame_five (a b c d e a' b' c' d' e' : List UInt8)
    (tail tail' : List UInt8)
    (h : frameList a ++ frameList b ++ frameList c ++ frameList d ++ frameList e ++ tail =
      frameList a' ++ frameList b' ++ frameList c' ++ frameList d' ++ frameList e' ++ tail') :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' ∧ e = e' ∧ tail = tail' := by
  frame_prefix_inj

theorem mir_option_test (x : Option Nat) (f g : Nat → Option Nat)
    (h : ∀ n, f n = g n) : (x >>= f) = (x >>= g) := by
  mir_sim_step

theorem mir_except_test (x : Except String Nat) (f g : Nat → Except String Nat)
    (h : ∀ n, f n = g n) : (x >>= f) = (x >>= g) := by
  mir_sim_step

def mir_compose_test {S₁ S₂ S₃ In Out : Type}
    {C : PartyMachine S₁ In Out} {A : PartyMachine S₂ In Out} {B : PartyMachine S₃ In Out} (ca : ForwardSim C A)
    (ab : ForwardSim A B) : ForwardSim C B := by
  mir_sim_step

namespace AssuranceRegression
structure State where
  counter : Nat

def reachable (s : State) : Prop := s.counter = 0
def step (s : State) : State := ⟨s.counter + 1⟩
def mutant (s : State) : State := s

theorem security (s : State) (h : reachable s) : (step s).counter = 1 := by
  exact congrArg (· + 1) h

theorem witness : ∃ s : State, reachable s ∧ (step s).counter = 1 :=
  ⟨⟨0⟩, rfl, rfl⟩

theorem inhabitedWitness : Nonempty {s : State // reachable s} := ⟨⟨⟨0⟩, rfl⟩⟩

theorem tooth : ∃ s : State, reachable s ∧ (mutant s).counter ≠ (step s).counter := by
  exact ⟨⟨0⟩, rfl, by decide⟩

theorem securityRenamed (t : State) (hr : reachable t) : (step t).counter = 1 :=
  security t hr

theorem trivialTooth : True := True.intro
theorem unrelated : (1 : Nat) ≠ 2 := by decide
theorem reflexiveTooth (s : State) : step s = step s := rfl
theorem unused (s : State) (_h : reachable s) : step s = step s := rfl
theorem impossible (n : Nat) (ha : n = 1) (hb : n = 2) : False := by
  have bad : (1 : Nat) = 2 := ha.symm.trans hb
  cases bad
theorem impossibleBool (b : Bool) (ht : b = true) (hf : b = false) : False := by
  have bad : true = false := ht.symm.trans hf
  cases bad
theorem emptyPremise (x : Empty) : False := nomatch x
theorem pemptyPremise (x : PEmpty) : False := nomatch x
theorem falsePremise (h : False) : False := h

theorem sameZero (n : Nat) (h : n = 0) (h' : n = Nat.zero) : n = 0 ∧ n = Nat.zero := ⟨h, h'⟩
#verify_constructive sameZero

theorem selfNe (n : Nat) (h : n ≠ n) : False := h rfl
theorem conditionalWitness (s : State) (h : reachable s) : ∃ t, reachable t := ⟨s, h⟩
theorem detachedWitness : ∃ s : State, step s = step s := ⟨⟨0⟩, rfl⟩

#verify_constructive security witness tooth
#verify_inhabited security witness
#verify_inhabited security inhabitedWitness
#tooth_pair security vs tooth
#tooth_pair security tooth
end AssuranceRegression

#verify_constructive xorEval_norm_eq XorTree.norm_sound xor_rss16 xor_rss32 frameList_append_inj
  frame_five mir_option_test mir_except_test

end Qsag
namespace Qsag.Tactic.AssuranceKit
open Lean Meta Elab Command Tactic
private meta def expectRejection (label : String) (action : CommandElabM Unit) : CommandElabM Unit := do
  let rejected ← try action; pure false catch _ => pure true
  unless rejected do throwError "negative assurance self-test accepted {label}"

run_cmd do
  let sec ← `(ident| Qsag.AssuranceRegression.security)
  for t in #[← `(ident| Qsag.AssuranceRegression.trivialTooth),
      ← `(ident| Qsag.AssuranceRegression.unrelated),
      ← `(ident| Qsag.AssuranceRegression.reflexiveTooth),
      ← `(ident| Qsag.AssuranceRegression.detachedWitness),
      ← `(ident| Qsag.AssuranceRegression.securityRenamed), sec] do
    expectRejection "tooth" (checkToothPair sec t)
  for t in #[← `(ident| Qsag.AssuranceRegression.unused),
      ← `(ident| Qsag.AssuranceRegression.impossible),
      ← `(ident| Qsag.AssuranceRegression.selfNe),
      ← `(ident| Qsag.AssuranceRegression.impossibleBool),
      ← `(ident| Qsag.AssuranceRegression.emptyPremise),
      ← `(ident| Qsag.AssuranceRegression.pemptyPremise),
      ← `(ident| Qsag.AssuranceRegression.falsePremise)] do
    expectRejection "premise" (discard <| verifyConstructiveDecl t)
  let (_, s) ← verifyConstructiveDecl sec
  for t in #[← `(ident| Qsag.AssuranceRegression.conditionalWitness),
      ← `(ident| Qsag.AssuranceRegression.detachedWitness)] do
    expectRejection "inhabitedness" do
      let (_, w) ← verifyConstructiveDecl t
      liftTermElabM <| checkInhabited s w
end Qsag.Tactic.AssuranceKit

end
