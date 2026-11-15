module
/-
# Finite coherent bit-oracle register: exact Walsh basis

The table register is quantum. Its Fourier labels are not a classical query log.
All amplitudes remain Gaussian integers; Walsh is unnormalized, with squared-norm scale
2^n and square equal to multiplication by 2^n. This full truth-table representation uses
2^n amplitudes, not a sparse compressed-oracle data structure.
-/
public import Qsag.Oracle.QromClassicalQueryTransfer
import all Qsag.Oracle.QromClassicalQueryTransfer
import all Qsag.Oracle.ConcreteSecurityBudget

public section
namespace Qsag
set_option autoImplicit false

/-- One bit for each of n oracle addresses. -/
@[reducible, expose] def OracleBitTable : Nat → Type
  | 0 => Unit
  | n + 1 => Bool × OracleBitTable n

def oracleTableSum : (n : Nat) → (OracleBitTable n → Nat) → Nat
  | 0, f => f ()
  | n + 1, f => oracleTableSum n (fun h => f (false, h)) +
    oracleTableSum n (fun h => f (true, h))

theorem oracleTableSum_congr : ∀ n (f g : OracleBitTable n → Nat),
    (∀ h, f h = g h) → oracleTableSum n f = oracleTableSum n g
  | 0, _, _, h => h ()
  | n + 1, _, _, h => by
    simp only [oracleTableSum]
    rw [oracleTableSum_congr n _ _ (fun x => h (false, x)),
      oracleTableSum_congr n _ _ (fun x => h (true, x))]

theorem oracleTableSum_add : ∀ n (f g : OracleBitTable n → Nat),
    oracleTableSum n (fun h => f h + g h) = oracleTableSum n f + oracleTableSum n g
  | 0, _, _ => rfl
  | n + 1, _, _ => by
    simp only [oracleTableSum, oracleTableSum_add]; omega

theorem oracleTableSum_mul : ∀ n (c : Nat) (f : OracleBitTable n → Nat),
    oracleTableSum n (fun h => c * f h) = c * oracleTableSum n f
  | 0, _, _ => rfl
  | n + 1, _, _ => by simp only [oracleTableSum, oracleTableSum_mul, Nat.mul_add]

/-- Multiplication by 2^k, implemented additively for the existing linearity interface. -/
def gaussDoublePow : Nat → GaussInt → GaussInt
  | 0, z => z
  | k + 1, z => (gaussDoublePow k z).add (gaussDoublePow k z)

def oracleWalsh : (n : Nat) → (OracleBitTable n → GaussInt) → OracleBitTable n → GaussInt
  | 0, f, _ => f ()
  | n + 1, f, (b, d) =>
    let u := oracleWalsh n (fun h => f (false, h)) d
    let v := oracleWalsh n (fun h => f (true, h)) d
    if b then u.sub v else u.add v

theorem oracleWalsh_congr : ∀ n (f g : OracleBitTable n → GaussInt),
    (∀ h, f h = g h) → oracleWalsh n f = oracleWalsh n g := by
  intro n f g h
  exact congrArg (oracleWalsh n) (funext h)

theorem oracleWalsh_add : ∀ n (f g : OracleBitTable n → GaussInt) (d : OracleBitTable n),
    oracleWalsh n (fun h => (f h).add (g h)) d =
      (oracleWalsh n f d).add (oracleWalsh n g d)
  | 0, _, _, _ => rfl
  | n + 1, f, g, (b, d) => by
    simp only [oracleWalsh, oracleWalsh_add]
    cases b <;> apply GaussInt.ext <;> simp [GaussInt.add, GaussInt.sub] <;> omega

theorem oracleWalsh_sub : ∀ n (f g : OracleBitTable n → GaussInt) (d : OracleBitTable n),
    oracleWalsh n (fun h => (f h).sub (g h)) d =
      (oracleWalsh n f d).sub (oracleWalsh n g d)
  | 0, _, _, _ => rfl
  | n + 1, f, g, (b, d) => by
    simp only [oracleWalsh, oracleWalsh_sub]
    cases b <;> apply GaussInt.ext <;> simp [GaussInt.add, GaussInt.sub] <;> omega

theorem oracleWalsh_doublePow (n k : Nat) (f : OracleBitTable n → GaussInt) (d : OracleBitTable n) :
    oracleWalsh n (fun h => gaussDoublePow k (f h)) d = gaussDoublePow k (oracleWalsh n f d) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [gaussDoublePow, oracleWalsh_add, ih]

/-- Exact inverse up to the known integer normalization. -/
theorem oracleWalsh_square : ∀ n (f : OracleBitTable n → GaussInt) (d : OracleBitTable n),
    oracleWalsh n (oracleWalsh n f) d = gaussDoublePow n (f d)
  | 0, _, () => rfl
  | n + 1, f, (b, d) => by
    change (if b then
      (oracleWalsh n (fun h => (oracleWalsh n (fun z => f (false, z)) h).add
        (oracleWalsh n (fun z => f (true, z)) h)) d).sub
      (oracleWalsh n (fun h => (oracleWalsh n (fun z => f (false, z)) h).sub
        (oracleWalsh n (fun z => f (true, z)) h)) d)
      else (oracleWalsh n (fun h => (oracleWalsh n (fun z => f (false, z)) h).add
        (oracleWalsh n (fun z => f (true, z)) h)) d).add
      (oracleWalsh n (fun h => (oracleWalsh n (fun z => f (false, z)) h).sub
        (oracleWalsh n (fun z => f (true, z)) h)) d)) = _
    rw [oracleWalsh_add, oracleWalsh_sub, oracleWalsh_square, oracleWalsh_square]
    cases b <;> apply GaussInt.ext <;> simp [gaussDoublePow, GaussInt.add, GaussInt.sub] <;> omega

/-- Scaled isometry on the entire oracle register, for arbitrary coherent amplitudes. -/
theorem oracleWalsh_norm : ∀ n (f : OracleBitTable n → GaussInt),
    oracleTableSum n (fun d => GaussInt.normSq (oracleWalsh n f d)) =
      2 ^ n * oracleTableSum n (fun h => GaussInt.normSq (f h))
  | 0, _ => by simp [oracleTableSum, oracleWalsh]
  | n + 1, f => by
    change oracleTableSum n (fun d => GaussInt.normSq
      ((oracleWalsh n (fun h => f (false, h)) d).add (oracleWalsh n (fun h => f (true, h)) d))) +
      oracleTableSum n (fun d => GaussInt.normSq
      ((oracleWalsh n (fun h => f (false, h)) d).sub (oracleWalsh n (fun h => f (true, h)) d))) = _
    rw [← oracleTableSum_add]
    rw [oracleTableSum_congr n _ _ (fun d => (Nat.add_comm _ _).trans (GaussInt.normSq_parallelogram _ _))]
    rw [oracleTableSum_add, oracleTableSum_mul, oracleTableSum_mul,
      oracleWalsh_norm, oracleWalsh_norm]
    simp only [oracleTableSum, Nat.pow_succ, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm]

theorem gaussDoublePow_norm (k : Nat) (z : GaussInt) :
    GaussInt.normSq (gaussDoublePow k z) = 4 ^ k * GaussInt.normSq z := by
  induction k with
  | zero => simp [gaussDoublePow]
  | succ k ih =>
    have h := GaussInt.normSq_parallelogram (gaussDoublePow k z) (gaussDoublePow k z)
    have hz : (gaussDoublePow k z).sub (gaussDoublePow k z) = GaussInt.zero := by
      apply GaussInt.ext <;> simp [GaussInt.sub, GaussInt.zero]
    rw [hz, GaussInt.normSq_zero, Nat.zero_add, ih] at h
    change GaussInt.normSq ((gaussDoublePow k z).add (gaussDoublePow k z)) = _
    rw [h, Nat.pow_succ]
    simp only [Nat.mul_assoc, Nat.mul_comm]
    omega

#verify_constructive
  Qsag.oracleWalsh_square
  Qsag.oracleWalsh_norm
  Qsag.gaussDoublePow_norm
end Qsag
end
