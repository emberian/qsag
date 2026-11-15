module
public meta import Lean
public section
namespace Qsag.Constructive

attribute [-instance] BitVec.instLawfulEqOrd

instance (priority := 1100) : LawfulBEq UInt64 where
  eq_of_beq {a b} h := UInt64.eq_of_toBitVec_eq (eq_of_beq h)
  rfl {a} := by
    change (a.toBitVec == a.toBitVec) = true
    exact BEq.rfl

instance (priority := 1100) : LawfulBEq UInt8 where
  eq_of_beq {a b} h := UInt8.eq_of_toBitVec_eq (eq_of_beq h)
  rfl {a} := by
    change (a.toBitVec == a.toBitVec) = true
    exact BEq.rfl


theorem testBit_mask (n i : Nat) : (2^n - 1).testBit i = decide (i < n) := by
  induction n generalizing i with
  | zero => simp only [Nat.pow_zero, Nat.sub_self, Nat.zero_testBit, Nat.not_lt_zero, decide_false]
  | succ n ih =>
    have hp := Nat.two_pow_pos n
    have he : 2^(n+1) - 1 = 2 * (2^n - 1) + 1 := by
      rw [Nat.pow_succ]
      omega
    rw [he]
    cases i with
    | zero =>
      rw [Nat.testBit_zero]
      have hm : (2 * (2^n - 1) + 1) % 2 = 1 := by omega
      rw [hm]
      simp only [Nat.zero_lt_succ, decide_true]
    | succ i =>
      rw [Nat.testBit_succ]
      have hd : (2 * (2^n - 1) + 1) / 2 = 2^n - 1 := by omega
      rw [hd, ih]
      simp only [Nat.succ_lt_succ_iff]

theorem getLsbD_allOnes (w i : Nat) :
    (BitVec.allOnes w).getLsbD i = decide (i < w) := by
  change (BitVec.allOnes w).toNat.testBit i = _
  rw [BitVec.toNat_allOnes, testBit_mask]

/-- Complement bits without the classical simplifier dependencies. -/
theorem getLsbD_not {w : Nat} (x : BitVec w) (i : Nat) :
    (~~~x).getLsbD i = (decide (i < w) && !x.getLsbD i) := by
  rw [BitVec.not_def, BitVec.getLsbD_xor, getLsbD_allOnes]
  by_cases h : i < w
  · simp only [h, decide_true, Bool.true_bne, Bool.true_and]
  · rw [BitVec.getLsbD_of_ge x i (Nat.le_of_not_gt h)]
    simp only [h, decide_false]
    rfl

/-- Cancellation avoids propositional preprocessing in arithmetic automation. -/
theorem left_eq_add {a b : Nat} : a = a + b ↔ b = 0 := by
  constructor
  · intro h
    exact Nat.add_left_cancel (show a + b = a + 0 from h.symm)
  · intro h
    rw [h, Nat.add_zero]

theorem and_mask (x n : Nat) : x &&& (2^n - 1) = x % 2^n := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_mod_two_pow, testBit_mask]
  exact Bool.and_comm _ _

theorem nodup_range (n : Nat) : (List.range n).Nodup := by
  induction n with
  | zero => exact List.Pairwise.nil
  | succ n ih =>
    rw [List.range_succ]
    rw [List.nodup_append]
    refine ⟨ih, List.Pairwise.cons (by intro _ h; cases h) .nil, ?_⟩
    intro a ha b hb heq
    have hb' : b = n := List.mem_singleton.mp hb
    subst b
    subst a
    exact Nat.lt_irrefl n (List.mem_range.mp ha)

/-- Negative boundary regression: complement has no bits beyond its width. -/
theorem complement_out_of_range (x : BitVec 8) : (~~~x).getLsbD 8 = false := by
  rw [getLsbD_not]
  rfl

end Qsag.Constructive

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

/-- Share a checked proof without abstracting away the values of local `let`s.
    The kernel still checks the auxiliary theorem and its application. -/
elab "qsag_aux_lemma" " => " body:tacticSeq : tactic => withMainContext do
  let goal ← getMainGoal
  let remaining ← Tactic.run goal (evalTactic body)
  unless remaining.isEmpty do
    throwError "qsag_aux_lemma requires all goals to be closed"
  let proof ← instantiateMVars (mkMVar goal)
  let shared ← mkAuxTheorem (← goal.getType) proof (zetaDelta := true)
  goal.assign shared

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
  liftTermElabM <| forallTelescope ci.type fun _ conclusion => do
    if (← whnf conclusion).isConstOf ``True then
      throwError "constructive audit: trivial True conclusion"
  if (stripBinders (ci.value! (allowOpaque := true))).getAppFn.isConstOf ``True.intro then
    throwErrorAt id "constructive audit: trivial True conclusion"
  return (n, ci)

syntax "#verify_constructive " ident+ : command
elab_rules : command
  | `(command| #verify_constructive $[$ids:ident]*) => do
    for id in ids do discard <| verifyConstructiveDecl id

/-- Only domain operations/predicates count; carrier types and constructors do not.
Inspect one definition layer so a named protocol wrapper can expose its checker. -/
private meta def domainConstants (e : Expr) : MetaM (Array Name) := do
  let env ← getEnv
  let direct := e.getUsedConstants
  let mut names := direct
  for n in direct do
    if (`Qsag).isPrefixOf n then
      if let some ci := env.find? n then
        if let .defnInfo d := ci then
          names := names ++ d.value.getUsedConstants
  names.filterM fun n => do
    unless (`Qsag).isPrefixOf n do return false
    let some ci := env.find? n | return false
    match ci with
    | .defnInfo _ => forallTelescope ci.type fun xs result =>
        return (!xs.isEmpty && !result.isSort) || result == mkSort Level.zero
    | .inductInfo _ => forallTelescope ci.type fun _ result =>
        return result == mkSort Level.zero
    | _ => return false

private meta def requireOverlap (a b : Expr) : MetaM Unit := do
  let da ← domainConstants a
  let db ← domainConstants b
  if (da.filter db.contains).isEmpty then
    throwError "pair audit: no shared protocol/domain constants"

private meta partial def meaningfulWitness (e : Expr) : MetaM Bool := do
  if e.isConstOf ``True then return false
  if let some (_, a, b) := e.eq? then
    return !(← withoutModifyingState (isDefEq a b))
  if e.getAppFn.isConstOf ``And then
    if ← meaningfulWitness e.getAppArgs[0]! then return true
    return ← meaningfulWitness e.getAppArgs[1]!
  if e.getAppFn.isConstOf ``Or then
    unless ← meaningfulWitness e.getAppArgs[0]! do return false
    return ← meaningfulWitness e.getAppArgs[1]!
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

syntax "#tooth_pair " ident &"vs" ident : command
syntax "#tooth_pair " ident ident : command
elab_rules : command
  | `(command| #tooth_pair $s:ident vs $t:ident) => checkToothPair s t
  | `(command| #tooth_pair $s:ident $t:ident) => checkToothPair s t

/-- Reveal constructor witnesses without normalizing their cryptographic data. -/
private meta def witnessHead (e : Expr) (fuel : Nat := 64) : MetaM Expr := do
  let e ← whnf e
  match fuel with
  | 0 => return e
  | fuel + 1 =>
    if let .const n ls := e.getAppFn then
      if let some ci := (← getEnv).find? n then
        if let some value := ci.value? (allowOpaque := true) then
          return ← witnessHead (mkAppN (value.instantiateLevelParams ci.levelParams ls) e.getAppArgs) fuel
    return e

/-- Preserve one common witness assignment across all premises. -/
private meta partial def withWitnessFacts (e proof : Expr) (facts : Array Expr)
    (k : Array Expr → MetaM Unit) : MetaM Unit := do
  if e.getAppFn.isConstOf ``Exists then
    let args := e.getAppArgs
    let p ← witnessHead proof
    if p.getAppFn.isConstOf ``Exists.intro then
      let pa := p.getAppArgs
      let v := pa[pa.size - 2]!
      withWitnessFacts ((mkApp args[1]! v).headBeta) pa.back! (facts.push v) k
    else
      withLocalDeclD `_ args[0]! fun v =>
        let ty := (mkApp args[1]! v).headBeta
        withLocalDeclD `_ ty fun h => withWitnessFacts ty h (facts.push v) k
  else if e.getAppFn.isConstOf ``Nonempty then
    let carrier ← whnf e.getAppArgs[0]!
    let useValue (v : Expr) : MetaM Unit := do
      if carrier.getAppFn.isConstOf ``Subtype then
        let val ← mkAppM ``Subtype.val #[v]
        let prop ← mkAppM ``Subtype.property #[v]
        k (facts ++ #[v, val, prop])
      else k (facts.push v)
    let p ← witnessHead proof
    if p.getAppFn.isConstOf ``Nonempty.intro then useValue p.getAppArgs.back!
    else withLocalDeclD `_ carrier useValue
  else if e.getAppFn.isConstOf ``And then
    withWitnessFacts e.getAppArgs[0]! (← mkAppM ``And.left #[proof]) facts fun facts => do
      withWitnessFacts e.getAppArgs[1]! (← mkAppM ``And.right #[proof]) facts k
  else k (facts.push (mkApp2 (mkConst ``id [Level.zero]) e proof))

/-- Failed candidate unification must not constrain later witness candidates. -/
private meta def matchWitnessType (a b : Expr) : MetaM Bool := do
  -- Match the stated predicate before unfolding. Unfolding a different predicate
  -- can both trigger enormous computations and assign unrelated index variables.
  let a ← instantiateMVars a
  let b ← instantiateMVars b
  let ah := a.getAppFn
  let bh := b.getAppFn
  if ah.isConst && bh.isConst && ah.constName! != bh.constName! then return false
  let saved ← saveState
  if ← isDefEq a b then return true
  saved.restore
  return false

/-- Construct data without choice, including ordinary records lacking an Inhabited instance.
Fuel bounds constructor search; every successful term is subsequently type-checked and audited. -/
private meta def constructWitnessValue (ty : Expr) (fuel : Nat := 16) : MetaM Expr := do
  try return ← mkDefault ty catch _ => pure ()
  if ← isProp ty then
    let dec ← mkDecide ty
    unless ← isDefEq dec (mkConst ``Bool.true) do throwError "unproved constructor field"
    return ← mkDecideProof ty
  match fuel with
  | 0 => throwError "inhabitedness audit: constructor search exhausted"
  | fuel + 1 =>
    let ty ← whnf ty
    if ty.isForall then
      return ← forallTelescope ty fun xs result => do
        mkLambdaFVars xs (← constructWitnessValue result fuel)
    let .const name _ := ty.getAppFn | throwError "inhabitedness audit: no data constructor"
    let .inductInfo info ← getConstInfo name | throwError "inhabitedness audit: no inductive carrier"
    for ctor in info.ctors do
      let saved ← saveState
      try
        let c ← mkConstWithFreshMVarLevels ctor
        let (args, _, result) ← forallMetaTelescope (← inferType c)
        unless ← isDefEq result ty do throwError "constructor result mismatch"
        for arg in args do
          let arg ← instantiateMVars arg
          if arg.isMVar then
            let value ← constructWitnessValue (← instantiateMVars (← inferType arg)) fuel
            unless ← isDefEq arg value do throwError "constructor field mismatch"
        return ← instantiateMVars (mkAppN c args)
      catch _ => saved.restore
    throwError "inhabitedness audit: cannot construct {ty}"

private meta def checkInhabited (s w : ConstantInfo) : MetaM Unit := do
  requireOverlap s.type w.type
  -- A parameterized witness is callable only when every argument can be constructed.
  let (wx, _, conclusion) ← forallMetaTelescope w.type
  for x in wx do
    let ty ← instantiateMVars (← inferType x)
    if ← isProp ty then
      throwError "inhabitedness audit: witness has undischarged Prop assumptions"
    let value ← constructWitnessValue ty
    unless ← isDefEq x value do
      throwError "inhabitedness audit: cannot instantiate witness parameter"
  for x in wx do
    let value ← instantiateMVars x
    if value.hasExprMVar then throwError "inhabitedness audit: unresolved witness parameter"
    check value
    auditDag (← getEnv) value.getUsedConstants.toList
  let conclusion ← instantiateMVars conclusion
  unless conclusion.getAppFn.isConstOf ``Exists || conclusion.getAppFn.isConstOf ``Nonempty do
    throwError "inhabitedness audit: expected an existential reachable-state witness"
  let proof ← instantiateMVars (mkAppN (w.value! (allowOpaque := true)) wx)
  withWitnessFacts conclusion proof #[] fun facts => do
    let (sx, _, sConclusion) ← forallMetaTelescope s.type
    let mut matchedWitnessPremise := false
    for x in sx do
      let ty ← instantiateMVars (← inferType x)
      if ← isProp ty then
        let mut found := false
        for fact in facts do
          if ← matchWitnessType ty (← inferType fact) then
            unless ← isDefEq x fact do
              throwError "inhabitedness audit: inconsistent proof assignment"
            found := true
            matchedWitnessPremise := true
            break
        if !found then pure ()
    -- A premise-free characterization `A ↔ B` is exercised when the witness establishes a side.
    unless matchedWitnessPremise do
      let c ← instantiateMVars sConclusion
      if c.getAppFn.isConstOf ``Iff then
        for side in c.getAppArgs do
          for fact in facts do
            unless matchedWitnessPremise do
              if ← matchWitnessType side (← inferType fact) then
                let f ← instantiateMVars fact
                check f
                auditDag (← getEnv) f.getUsedConstants.toList
                matchedWitnessPremise := true
    unless matchedWitnessPremise do
      throwError "inhabitedness audit: no security premise supplied by the witness"
    for x in sx do
      let x ← instantiateMVars x
      if x.isMVar && !(← isProp (← inferType x)) then
        let ty ← instantiateMVars (← inferType x)
        if let .some inst ← (try trySynthInstance ty catch _ => pure .none) then
          if ← isDefEq x inst then continue
        let mut found := false
        -- Pass 1: directly bind any witness value of matching type not yet bound to an
        -- earlier binder in `sx` (never silently replacing explicit list witnesses with
        -- `List.replicate _ default`).
        for fact in facts do
          if ← matchWitnessType ty (← inferType fact) then
            let alreadyBound ← sx.anyM fun b => do
              let b ← instantiateMVars b
              if b.isMVar then pure false
              else if b == fact then pure true
              else withNewMCtxDepth <| isDefEq b fact
            if !alreadyBound then
              if ← isDefEq x fact then
                found := true
                break
        -- Pass 2: only for remaining auxiliary binders whose matching witness values were
        -- already consumed by earlier binders, synthesize a dimension-matched default.
        if !found then
          for fact in facts do
            if ← matchWitnessType ty (← inferType fact) then
              let candidate ← try
                if ty.getAppFn.isConstOf ``List then
                  let d ← mkDefault ty.getAppArgs[0]!
                  mkAppM ``List.replicate #[← mkAppM ``List.length #[fact], d]
                else pure fact
              catch _ => pure fact
              if ← isDefEq x candidate then
                found := true
                break
        if !found then pure ()
    -- Infer dimensions from structured witness values before defaulting free data.
    for x in sx do
      let x ← instantiateMVars x
      if x.isMVar && !(← isProp (← inferType x)) then
        let value ← constructWitnessValue (← instantiateMVars (← inferType x))
        unless ← isDefEq x value do
          throwError "inhabitedness audit: cannot construct value binder"
    for x in sx do
      let x ← instantiateMVars x
      if x.isMVar then
        let ty ← instantiateMVars (← inferType x)
        let proof ← try
          let .some inst ← trySynthInstance ty | throwError "not an instance"
          pure inst
        catch _ =>
          try
            let (target, dec) ← try
              pure (ty, ← mkDecide ty)
            catch _ => do
              let target ← withTransparency .all (whnf ty)
              pure (target, ← mkDecide target)
            unless ← isDefEq dec (mkConst ``Bool.true) do
              throwError "decision is not true"
            mkDecideProof target
          catch err => throwError "inhabitedness audit: joint witness does not discharge {ty}\n{err.toMessageData}"
        unless ← isDefEq x proof do
          throwError "inhabitedness audit: inconsistent joint proof"
    for x in sx do
      let value ← instantiateMVars x
      if value.hasExprMVar then
        throwError "inhabitedness audit: incomplete joint witness"
      check value
      auditDag (← getEnv) value.getUsedConstants.toList

syntax "#verify_inhabited " ident ident : command
elab_rules : command
  | `(command| #verify_inhabited $s:ident $w:ident) => do
    let (_, sec) ← verifyConstructiveDecl s
    let (_, wit) ← verifyConstructiveDecl w
    -- Keep witness search bounded even in modules that disable proof heartbeat limits.
    liftTermElabM <| withOptions (fun o => maxRecDepth.set (maxHeartbeats.set o 200000) (max 4096 (maxRecDepth.get o))) <|
      checkInhabited sec wit

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


end Qsag.Tactic.AssuranceKit
