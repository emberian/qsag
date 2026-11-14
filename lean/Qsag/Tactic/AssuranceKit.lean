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

