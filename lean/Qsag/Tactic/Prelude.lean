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

