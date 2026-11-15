module
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
