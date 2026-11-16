module
/-
# Qsag.Oracle.BlockCompressedOracle — Fourier database support for `w`-bit oracle answers

`Qsag.Oracle.Qrom` proves the Fourier ("compressed oracle") support invariant only for one-bit
answers (`fourier_coherent_support`, `fourier_runtime_support`,
`fourier_database_overflow_mass_zero`, all over `QuantumAdv n 1 …`). This module proves the same
three statements for answers in `BitVec w` with `w` arbitrary. The database label of an oracle
`Fin n → BitVec w` is one `w`-bit Fourier block per address, and the invariant bounds the number
of addresses whose block is nonzero (`blockWeight`), not the number of nonzero bits: one query
can populate all `w` bits of one block. Every sum and induction keeps `w` symbolic, so the
`w = 256` instances at the end are instantiations and never enumerate `2 ^ 256`.

## What is proved about which objects

`Qrom.lean` does not expose the bodies of `advStateAt`, `oracleXor`, `QVec.sub`, `QVec.zero`,
`GaussInt.add`, `oracleWalsh`, `tableWeight`, …; it publishes one equation lemma per definition
(`advStateAt_succ`, `oracleXor_apply`, `oracleWalsh_succ`, …). The development is split:

* §1–§7 are unconditional. They use the `Qrom` carriers `GaussInt`, `QVec`, `OracleBitTable`
  and the function `xorFin` as given, and define the remaining operations here (`zadd`, `zsub`,
  `qsub`, `blockQuery`, `BlockAdv`, `blockAdvStateAt`) with the same bodies as their `Qrom`
  counterparts. A `BlockAdv` step is any map that preserves pointwise subtraction; no norm law
  is needed for the support invariant.
* §8 transports the results to `Qrom`'s own `QuantumAdv` / `advStateAt` / `oracleXor`. The
  transport needs the defining equations of those constants, collected as the fields of
  `QromRuntimeLaws` (five equations) and, for the one-bit comparison, `QromBitTableLaws` (six
  equations). §9 proves both structures from the `Qrom` equation lemmas (`qromRuntimeLaws`,
  `qromBitTableLaws`) and states the results without premises:
  `quantumAdv_block_fourier_coherent_support` for every answer width, its `w = 256` instance,
  and `quantumAdv_fourier_coherent_support_from_block`, which has the statement of
  `Qsag.fourier_coherent_support` and is derived from the block theorem at `w = 1`.

No statement here concerns measured or classical query logs; the coherent cover premise
`ClassicalQueryAddresses` of `Qrom.lean` is not touched by this module.
-/
public import Qsag.Oracle.Qrom
public section
namespace Qsag.BlockCompressedOracle
set_option autoImplicit false
set_option exponentiation.threshold 2048

/-! ## §1. Gaussian-integer operations with visible bodies -/

def zzero : GaussInt := ⟨0, 0⟩
def zadd (z v : GaussInt) : GaussInt := ⟨z.re + v.re, z.im + v.im⟩
def zsub (z v : GaussInt) : GaussInt := ⟨z.re - v.re, z.im - v.im⟩

theorem zzero_eq : zzero = ⟨0, 0⟩ := by rfl
theorem zadd_eq (z v : GaussInt) : zadd z v = ⟨z.re + v.re, z.im + v.im⟩ := by rfl
theorem zsub_eq (z v : GaussInt) : zsub z v = ⟨z.re - v.re, z.im - v.im⟩ := by rfl

theorem zsub_self (z : GaussInt) : zsub z z = zzero := by
  apply GaussInt.ext <;> dsimp only [zsub, zzero] <;> omega

theorem zadd_zzero : zadd zzero zzero = zzero := by rfl

/-- The carrier has no 2-torsion: a sum and a difference vanish only for vanishing terms. -/
theorem zero_of_zadd_zsub {u v : GaussInt} (ha : zadd u v = zzero) (hs : zsub u v = zzero) :
    u = zzero ∧ v = zzero := by
  have h1 := congrArg GaussInt.re ha
  have h2 := congrArg GaussInt.im ha
  have h3 := congrArg GaussInt.re hs
  have h4 := congrArg GaussInt.im hs
  dsimp only [zadd, zsub, zzero] at h1 h2 h3 h4
  exact ⟨GaussInt.ext (by dsimp only [zzero]; omega) (by dsimp only [zzero]; omega),
    GaussInt.ext (by dsimp only [zzero]; omega) (by dsimp only [zzero]; omega)⟩

theorem zero_of_zadd_self {z : GaussInt} (h : zadd z z = zzero) : z = zzero :=
  (zero_of_zadd_zsub h (zsub_self z)).1

theorem zadd_zadd_comm (a b c d : GaussInt) :
    zadd (zadd a b) (zadd c d) = zadd (zadd a c) (zadd b d) := by
  apply GaussInt.ext <;> dsimp only [zadd] <;> omega

theorem zsub_zadd_comm (a b c d : GaussInt) :
    zsub (zadd a b) (zadd c d) = zadd (zsub a c) (zsub b d) := by
  apply GaussInt.ext <;> dsimp only [zadd, zsub] <;> omega

theorem zadd_zsub_comm (a b c d : GaussInt) :
    zadd (zsub a b) (zsub c d) = zsub (zadd a c) (zadd b d) := by
  apply GaussInt.ext <;> dsimp only [zadd, zsub] <;> omega

theorem zsub_zsub_comm (a b c d : GaussInt) :
    zsub (zsub a b) (zsub c d) = zsub (zsub a c) (zsub b d) := by
  apply GaussInt.ext <;> dsimp only [zsub] <;> omega

theorem zadd_add_sub (p r : GaussInt) : zadd (zadd p r) (zsub p r) = zadd p p := by
  apply GaussInt.ext <;> dsimp only [zadd, zsub] <;> omega

theorem zsub_add_sub (p r : GaussInt) : zsub (zadd p r) (zsub p r) = zadd r r := by
  apply GaussInt.ext <;> dsimp only [zadd, zsub] <;> omega

theorem zsub_zadd_cancel (p r : GaussInt) : zsub (zadd p r) r = p := by
  apply GaussInt.ext <;> dsimp only [zadd, zsub] <;> omega

/-- Multiplication by `2 ^ k`, written additively. -/
def zdblPow : Nat → GaussInt → GaussInt
  | 0, z => z
  | k + 1, z => zadd (zdblPow k z) (zdblPow k z)

theorem zdblPow_zero (z : GaussInt) : zdblPow 0 z = z := by rfl
theorem zdblPow_succ (k : Nat) (z : GaussInt) :
    zdblPow (k + 1) z = zadd (zdblPow k z) (zdblPow k z) := by rfl

theorem zdblPow_zzero : ∀ k, zdblPow k zzero = zzero
  | 0 => rfl
  | k + 1 => by rw [zdblPow_succ, zdblPow_zzero k]; rfl

theorem zdblPow_add_exp (k l : Nat) (z : GaussInt) :
    zdblPow k (zdblPow l z) = zdblPow (k + l) z := by
  induction k with
  | zero => rw [Nat.zero_add]; rfl
  | succ k ih => rw [Nat.succ_add, zdblPow_succ, zdblPow_succ, ih]

/-- Doubling never creates a zero. -/
theorem zdblPow_eq_zzero : ∀ (k : Nat) (z : GaussInt), zdblPow k z = zzero → z = zzero
  | 0, _, h => h
  | k + 1, z, h => zdblPow_eq_zzero k z (zero_of_zadd_self h)

/-! ## §2. The Walsh transform of one `w`-bit block -/

/-- Some bit of the block is set. -/
def bitsNonzero : (k : Nat) → OracleBitTable k → Bool
  | 0, _ => false
  | k + 1, (b, e) => b || bitsNonzero k e

/-- The all-zero block. -/
def bitsZero : (k : Nat) → OracleBitTable k
  | 0 => ()
  | k + 1 => (false, bitsZero k)

theorem bitsNonzero_bitsZero : ∀ k, bitsNonzero k (bitsZero k) = false
  | 0 => rfl
  | k + 1 => bitsNonzero_bitsZero k

theorem bitsNonzero_true_cons (k : Nat) (e : OracleBitTable k) :
    bitsNonzero (k + 1) (true, e) = true := by rfl

def bitWalsh : (k : Nat) → (OracleBitTable k → GaussInt) → OracleBitTable k → GaussInt
  | 0, f, _ => f ()
  | k + 1, f, (b, e) =>
    if b then zsub (bitWalsh k (fun h => f (false, h)) e) (bitWalsh k (fun h => f (true, h)) e)
    else zadd (bitWalsh k (fun h => f (false, h)) e) (bitWalsh k (fun h => f (true, h)) e)

theorem bitWalsh_nil (f : OracleBitTable 0 → GaussInt) (u : OracleBitTable 0) :
    bitWalsh 0 f u = f () := by rfl

theorem bitWalsh_false (k : Nat) (f : OracleBitTable (k + 1) → GaussInt) (e : OracleBitTable k) :
    bitWalsh (k + 1) f (false, e) =
      zadd (bitWalsh k (fun h => f (false, h)) e) (bitWalsh k (fun h => f (true, h)) e) := by rfl

theorem bitWalsh_true (k : Nat) (f : OracleBitTable (k + 1) → GaussInt) (e : OracleBitTable k) :
    bitWalsh (k + 1) f (true, e) =
      zsub (bitWalsh k (fun h => f (false, h)) e) (bitWalsh k (fun h => f (true, h)) e) := by rfl

theorem bitWalsh_zero_fun : ∀ (k : Nat) (e : OracleBitTable k),
    bitWalsh k (fun _ => zzero) e = zzero
  | 0, _ => rfl
  | k + 1, (b, e) => by
    cases b
    · rw [bitWalsh_false, bitWalsh_zero_fun k e]; rfl
    · rw [bitWalsh_true]; exact zsub_self _

/-- A constant function has no amplitude on a nonzero block label. -/
theorem bitWalsh_const : ∀ (k : Nat) (z : GaussInt) (e : OracleBitTable k),
    bitsNonzero k e = true → bitWalsh k (fun _ => z) e = zzero
  | 0, _, _, h => absurd h Bool.false_ne_true
  | k + 1, z, (b, e), h => by
    cases b
    · have h' : bitsNonzero k e = true := h
      rw [bitWalsh_false, bitWalsh_const k z e h']; rfl
    · rw [bitWalsh_true]; exact zsub_self _

/-- On the zero label a constant function is multiplied by `2 ^ k`. -/
theorem bitWalsh_const_bitsZero : ∀ (k : Nat) (z : GaussInt),
    bitWalsh k (fun _ => z) (bitsZero k) = zdblPow k z
  | 0, _ => rfl
  | k + 1, z => by
    show bitWalsh (k + 1) (fun _ => z) (false, bitsZero k) = _
    rw [bitWalsh_false, bitWalsh_const_bitsZero k z, zdblPow_succ]

/-- The block transform is injective: a function whose transform vanishes everywhere is zero. -/
theorem bitWalsh_injective : ∀ (k : Nat) (f : OracleBitTable k → GaussInt),
    (∀ e, bitWalsh k f e = zzero) → ∀ b, f b = zzero
  | 0, _, h, () => h ()
  | k + 1, f, h, (b, e) => by
    have hu : ∀ e', bitWalsh k (fun x => f (false, x)) e' = zzero ∧
        bitWalsh k (fun x => f (true, x)) e' = zzero := by
      intro e'
      have ha := h (false, e')
      have hs := h (true, e')
      rw [bitWalsh_false] at ha
      rw [bitWalsh_true] at hs
      exact zero_of_zadd_zsub ha hs
    cases b
    · exact bitWalsh_injective k (fun x => f (false, x)) (fun e' => (hu e').1) e
    · exact bitWalsh_injective k (fun x => f (true, x)) (fun e' => (hu e').2) e

theorem bitWalsh_add : ∀ (k : Nat) (f g : OracleBitTable k → GaussInt) (e : OracleBitTable k),
    bitWalsh k (fun h => zadd (f h) (g h)) e = zadd (bitWalsh k f e) (bitWalsh k g e)
  | 0, _, _, _ => rfl
  | k + 1, f, g, (b, e) => by
    cases b
    · rw [bitWalsh_false, bitWalsh_false, bitWalsh_false,
        bitWalsh_add k (fun h => f (false, h)) (fun h => g (false, h)) e,
        bitWalsh_add k (fun h => f (true, h)) (fun h => g (true, h)) e]
      exact zadd_zadd_comm _ _ _ _
    · rw [bitWalsh_true, bitWalsh_true, bitWalsh_true,
        bitWalsh_add k (fun h => f (false, h)) (fun h => g (false, h)) e,
        bitWalsh_add k (fun h => f (true, h)) (fun h => g (true, h)) e]
      exact zsub_zadd_comm _ _ _ _

theorem bitWalsh_sub : ∀ (k : Nat) (f g : OracleBitTable k → GaussInt) (e : OracleBitTable k),
    bitWalsh k (fun h => zsub (f h) (g h)) e = zsub (bitWalsh k f e) (bitWalsh k g e)
  | 0, _, _, _ => rfl
  | k + 1, f, g, (b, e) => by
    cases b
    · rw [bitWalsh_false, bitWalsh_false, bitWalsh_false,
        bitWalsh_sub k (fun h => f (false, h)) (fun h => g (false, h)) e,
        bitWalsh_sub k (fun h => f (true, h)) (fun h => g (true, h)) e]
      exact zadd_zsub_comm _ _ _ _
    · rw [bitWalsh_true, bitWalsh_true, bitWalsh_true,
        bitWalsh_sub k (fun h => f (false, h)) (fun h => g (false, h)) e,
        bitWalsh_sub k (fun h => f (true, h)) (fun h => g (true, h)) e]
      exact zsub_zsub_comm _ _ _ _

theorem bitWalsh_dbl (k : Nat) (f : OracleBitTable k → GaussInt) (e : OracleBitTable k) :
    ∀ j, bitWalsh k (fun h => zdblPow j (f h)) e = zdblPow j (bitWalsh k f e)
  | 0 => rfl
  | j + 1 => by
    show bitWalsh k (fun h => zadd (zdblPow j (f h)) (zdblPow j (f h))) e = _
    rw [bitWalsh_add, bitWalsh_dbl k f e j, zdblPow_succ]

/-- Applying the block transform twice multiplies by `2 ^ k`. -/
theorem bitWalsh_square : ∀ (k : Nat) (f : OracleBitTable k → GaussInt) (e : OracleBitTable k),
    bitWalsh k (bitWalsh k f) e = zdblPow k (f e)
  | 0, _, () => rfl
  | k + 1, f, (b, e) => by
    have h0 : (fun h => bitWalsh (k + 1) f (false, h)) = fun h =>
        zadd (bitWalsh k (fun x => f (false, x)) h) (bitWalsh k (fun x => f (true, x)) h) := rfl
    have h1 : (fun h => bitWalsh (k + 1) f (true, h)) = fun h =>
        zsub (bitWalsh k (fun x => f (false, x)) h) (bitWalsh k (fun x => f (true, x)) h) := rfl
    cases b
    · rw [bitWalsh_false, h0, h1, bitWalsh_add, bitWalsh_sub,
        bitWalsh_square k (fun x => f (false, x)) e, bitWalsh_square k (fun x => f (true, x)) e,
        zdblPow_succ]
      exact zadd_add_sub _ _
    · rw [bitWalsh_true, h0, h1, bitWalsh_add, bitWalsh_sub,
        bitWalsh_square k (fun x => f (false, x)) e, bitWalsh_square k (fun x => f (true, x)) e,
        zdblPow_succ]
      exact zsub_add_sub _ _

/-! ## §3. Block tables and their transform -/

/-- One `w`-bit block for each of `n` oracle addresses. As an oracle it is the truth table of
    a function `Fin n → BitVec w`; as a Fourier label it is the compressed-oracle database. -/
@[reducible, expose] def BlockTable (w : Nat) : Nat → Type
  | 0 => Unit
  | n + 1 => OracleBitTable w × BlockTable w n

def blockWalsh (w : Nat) : (n : Nat) → (BlockTable w n → GaussInt) → BlockTable w n → GaussInt
  | 0, f, _ => f ()
  | n + 1, f, (e, d) => bitWalsh w (fun b => blockWalsh w n (fun h => f (b, h)) d) e

theorem blockWalsh_nil (w : Nat) (f : BlockTable w 0 → GaussInt) (u : BlockTable w 0) :
    blockWalsh w 0 f u = f () := by rfl

theorem blockWalsh_succ (w n : Nat) (f : BlockTable w (n + 1) → GaussInt)
    (e : OracleBitTable w) (d : BlockTable w n) :
    blockWalsh w (n + 1) f (e, d) =
      bitWalsh w (fun b => blockWalsh w n (fun h => f (b, h)) d) e := by rfl

theorem blockWalsh_add (w : Nat) : ∀ (n : Nat) (f g : BlockTable w n → GaussInt)
    (d : BlockTable w n),
    blockWalsh w n (fun h => zadd (f h) (g h)) d = zadd (blockWalsh w n f d) (blockWalsh w n g d)
  | 0, _, _, _ => rfl
  | n + 1, f, g, (e, d) => by
    rw [blockWalsh_succ, blockWalsh_succ, blockWalsh_succ, ← bitWalsh_add]
    exact congrArg (fun F => bitWalsh w F e)
      (funext fun b => blockWalsh_add w n (fun h => f (b, h)) (fun h => g (b, h)) d)

theorem blockWalsh_sub (w : Nat) : ∀ (n : Nat) (f g : BlockTable w n → GaussInt)
    (d : BlockTable w n),
    blockWalsh w n (fun h => zsub (f h) (g h)) d = zsub (blockWalsh w n f d) (blockWalsh w n g d)
  | 0, _, _, _ => rfl
  | n + 1, f, g, (e, d) => by
    rw [blockWalsh_succ, blockWalsh_succ, blockWalsh_succ, ← bitWalsh_sub]
    exact congrArg (fun F => bitWalsh w F e)
      (funext fun b => blockWalsh_sub w n (fun h => f (b, h)) (fun h => g (b, h)) d)

theorem blockWalsh_dbl (w n : Nat) (f : BlockTable w n → GaussInt) (d : BlockTable w n) :
    ∀ j, blockWalsh w n (fun h => zdblPow j (f h)) d = zdblPow j (blockWalsh w n f d)
  | 0 => rfl
  | j + 1 => by
    show blockWalsh w n (fun h => zadd (zdblPow j (f h)) (zdblPow j (f h))) d = _
    rw [blockWalsh_add, blockWalsh_dbl w n f d j, zdblPow_succ]

theorem blockWalsh_zero_fun (w : Nat) : ∀ (n : Nat) (d : BlockTable w n),
    blockWalsh w n (fun _ => zzero) d = zzero
  | 0, _ => rfl
  | n + 1, (e, d) => by
    rw [blockWalsh_succ]
    have hfun : (fun _ : OracleBitTable w => blockWalsh w n (fun _ => zzero) d) =
        fun _ => zzero := funext fun _ => blockWalsh_zero_fun w n d
    exact (congrArg (fun F => bitWalsh w F e) hfun).trans (bitWalsh_zero_fun w e)

/-- A block transform and a table transform over different registers commute. -/
theorem bitWalsh_blockWalsh_comm (w : Nat) : ∀ (k n : Nat)
    (F : OracleBitTable k → BlockTable w n → GaussInt) (e : OracleBitTable k)
    (d : BlockTable w n),
    bitWalsh k (fun b => blockWalsh w n (F b) d) e =
      blockWalsh w n (fun h => bitWalsh k (fun b => F b h) e) d
  | 0, _, _, _, _ => rfl
  | k + 1, n, F, (b, e), d => by
    cases b
    · have hR : (fun h => bitWalsh (k + 1) (fun b => F b h) (false, e)) = fun h =>
          zadd (bitWalsh k (fun b => F (false, b) h) e) (bitWalsh k (fun b => F (true, b) h) e) :=
        rfl
      rw [bitWalsh_false, hR, blockWalsh_add,
        bitWalsh_blockWalsh_comm w k n (fun b => F (false, b)) e d,
        bitWalsh_blockWalsh_comm w k n (fun b => F (true, b)) e d]
    · have hR : (fun h => bitWalsh (k + 1) (fun b => F b h) (true, e)) = fun h =>
          zsub (bitWalsh k (fun b => F (false, b) h) e) (bitWalsh k (fun b => F (true, b) h) e) :=
        rfl
      rw [bitWalsh_true, hR, blockWalsh_sub,
        bitWalsh_blockWalsh_comm w k n (fun b => F (false, b)) e d,
        bitWalsh_blockWalsh_comm w k n (fun b => F (true, b)) e d]

/-- Applying the table transform twice multiplies by `2 ^ (n * w)`; `w` stays symbolic. -/
theorem blockWalsh_square (w : Nat) : ∀ (n : Nat) (f : BlockTable w n → GaussInt)
    (d : BlockTable w n), blockWalsh w n (blockWalsh w n f) d = zdblPow (n * w) (f d)
  | 0, _, () => by rw [Nat.zero_mul]; rfl
  | n + 1, f, (e, d) => by
    rw [blockWalsh_succ]
    have h0 : (fun b => blockWalsh w n (fun h => blockWalsh w (n + 1) f (b, h)) d) =
        fun b => bitWalsh w (fun b' => zdblPow (n * w) (f (b', d))) b := by
      funext b
      have h1 : (fun h => blockWalsh w (n + 1) f (b, h)) = fun h =>
          bitWalsh w (fun b' => blockWalsh w n (fun h' => f (b', h')) h) b := rfl
      rw [h1, ← bitWalsh_blockWalsh_comm w w n
        (fun b' h => blockWalsh w n (fun h' => f (b', h')) h) b d]
      exact congrArg (fun F => bitWalsh w F b)
        (funext fun b' => blockWalsh_square w n (fun h' => f (b', h')) d)
    rw [h0, bitWalsh_square, zdblPow_add_exp, Nat.succ_mul, Nat.add_comm]

/-! ## §4. Database size, block access and the query law -/

/-- Number of addresses whose Fourier block is nonzero: the compressed-database size. -/
@[expose] def blockWeight (w : Nat) : (n : Nat) → BlockTable w n → Nat
  | 0, _ => 0
  | n + 1, (e, d) => (bitsNonzero w e).toNat + blockWeight w n d

theorem blockWeight_nil (w : Nat) (u : BlockTable w 0) : blockWeight w 0 u = 0 := by rfl

theorem blockWeight_succ (w n : Nat) (e : OracleBitTable w) (d : BlockTable w n) :
    blockWeight w (n + 1) (e, d) = (bitsNonzero w e).toNat + blockWeight w n d := by rfl

/-- The empty database. -/
def zeroLabel (w : Nat) : (n : Nat) → BlockTable w n
  | 0 => ()
  | n + 1 => (bitsZero w, zeroLabel w n)

theorem blockWeight_zeroLabel (w : Nat) : ∀ n, blockWeight w n (zeroLabel w n) = 0
  | 0 => rfl
  | n + 1 => by
    show (bitsNonzero w (bitsZero w)).toNat + blockWeight w n (zeroLabel w n) = 0
    rw [bitsNonzero_bitsZero, blockWeight_zeroLabel w n]; rfl

def blockAt (w : Nat) : (n : Nat) → BlockTable w n → Fin n → OracleBitTable w
  | 0, _, x => x.elim0
  | _ + 1, (e, _), ⟨0, _⟩ => e
  | n + 1, (_, h), ⟨i + 1, hi⟩ => blockAt w n h ⟨i, Nat.lt_of_succ_lt_succ hi⟩

def setBlock (w : Nat) : (n : Nat) → BlockTable w n → Fin n → OracleBitTable w → BlockTable w n
  | 0, _, x, _ => x.elim0
  | _ + 1, (_, d), ⟨0, _⟩, e' => (e', d)
  | n + 1, (e, d), ⟨i + 1, hi⟩, e' => (e, setBlock w n d ⟨i, Nat.lt_of_succ_lt_succ hi⟩ e')

/-- Rewriting one block changes the database size by at most one, whatever the block width. -/
theorem blockWeight_setBlock_le (w : Nat) : ∀ (n : Nat) (d : BlockTable w n) (x : Fin n)
    (e : OracleBitTable w), blockWeight w n d ≤ blockWeight w n (setBlock w n d x e) + 1
  | 0, _, x, _ => x.elim0
  | n + 1, (e0, d), x, e => by
    refine Fin.cases ?_ (fun j => ?_) x
    · show (bitsNonzero w e0).toNat + blockWeight w n d ≤
        (bitsNonzero w e).toNat + blockWeight w n d + 1
      have h1 := Bool.toNat_le (bitsNonzero w e0)
      omega
    · have ih := blockWeight_setBlock_le w n d j e
      show (bitsNonzero w e0).toNat + blockWeight w n d ≤
        (bitsNonzero w e0).toNat + blockWeight w n (setBlock w n d j e) + 1
      omega

theorem blockWalsh_const (w : Nat) : ∀ (n : Nat) (z : GaussInt) (d : BlockTable w n),
    blockWeight w n d ≠ 0 → blockWalsh w n (fun _ => z) d = zzero
  | 0, _, _, h => absurd rfl h
  | n + 1, z, (e, d), h => by
    rw [blockWalsh_succ]
    cases he : bitsNonzero w e
    · have hd : blockWeight w n d ≠ 0 := by
        intro h0
        apply h
        rw [blockWeight_succ, he, h0]
        rfl
      have hfun : (fun _ : OracleBitTable w => blockWalsh w n (fun _ => z) d) =
          fun _ => zzero := funext fun _ => blockWalsh_const w n z d hd
      exact (congrArg (fun F => bitWalsh w F e) hfun).trans (bitWalsh_zero_fun w e)
    · exact bitWalsh_const w _ e he

theorem blockWalsh_const_zeroLabel (w : Nat) : ∀ (n : Nat) (z : GaussInt),
    blockWalsh w n (fun _ => z) (zeroLabel w n) = zdblPow (n * w) z
  | 0, _ => by rw [Nat.zero_mul]; rfl
  | n + 1, z => by
    show blockWalsh w (n + 1) (fun _ => z) (bitsZero w, zeroLabel w n) = _
    rw [blockWalsh_succ]
    have hfun : (fun _ : OracleBitTable w => blockWalsh w n (fun _ => z) (zeroLabel w n)) =
        fun _ => zdblPow (n * w) z := funext fun _ => blockWalsh_const_zeroLabel w n z
    rw [hfun, bitWalsh_const_bitsZero, zdblPow_add_exp, Nat.succ_mul, Nat.add_comm]

/-- **Block query law.** Let `g h v` be any amplitude that reads the oracle `h` and, separately,
    a block value `v`. If its table transform vanishes on every label that differs from `d`
    only in block `x`, then so does the transform of `h ↦ g h (h x)`, the amplitude after the
    block at address `x` has been read into the computation. The address is arbitrary and the
    statement is used pointwise under a superposition of addresses. -/
theorem blockWalsh_query (w : Nat) : ∀ (n : Nat)
    (g : BlockTable w n → OracleBitTable w → GaussInt) (d : BlockTable w n) (x : Fin n),
    (∀ v e, blockWalsh w n (fun h => g h v) (setBlock w n d x e) = zzero) →
    blockWalsh w n (fun h => g h (blockAt w n h x)) d = zzero
  | 0, _, _, x, _ => x.elim0
  | n + 1, g, (e0, d), x, hyp => by
    revert hyp
    refine Fin.cases ?_ (fun j => ?_) x
    · intro hyp
      have hG : ∀ v b, blockWalsh w n (fun h => g (b, h) v) d = zzero := by
        intro v
        refine bitWalsh_injective w (fun b => blockWalsh w n (fun h => g (b, h) v) d) ?_
        intro e
        exact hyp v e
      rw [blockWalsh_succ]
      have hfun : (fun b => blockWalsh w n
          (fun h => g (b, h) (blockAt w (n + 1) (b, h) 0)) d) = fun _ => zzero :=
        funext fun b => hG b b
      exact (congrArg (fun F => bitWalsh w F e0) hfun).trans (bitWalsh_zero_fun w e0)
    · intro hyp
      rw [blockWalsh_succ]
      have h1 : (fun b => blockWalsh w n
          (fun h => g (b, h) (blockAt w (n + 1) (b, h) j.succ)) d) =
          fun b => blockWalsh w n (fun h => g (b, h) (blockAt w n h j)) d := rfl
      rw [h1, bitWalsh_blockWalsh_comm w w n (fun b h => g (b, h) (blockAt w n h j)) e0 d]
      refine blockWalsh_query w n (fun h v => bitWalsh w (fun b => g (b, h) v) e0) d j
        (fun v e => ?_)
      rw [← bitWalsh_blockWalsh_comm w w n (fun b h => g (b, h) v) e0 (setBlock w n d j e)]
      exact hyp v e

/-! ## §5. Coherent states, gates and the query -/

abbrev CoherentBlockState (w n cardAnc : Nat) := BlockTable w n → QVec n w cardAnc

def qzero (n w cardAnc : Nat) : QVec n w cardAnc := fun _ _ _ => zzero

def qadd {n w cardAnc : Nat} (ψ φ : QVec n w cardAnc) : QVec n w cardAnc :=
  fun x y a => zadd (ψ x y a) (φ x y a)

def qsub {n w cardAnc : Nat} (ψ φ : QVec n w cardAnc) : QVec n w cardAnc :=
  fun x y a => zsub (ψ x y a) (φ x y a)

def qdblPow {n w cardAnc : Nat} (k : Nat) (ψ : QVec n w cardAnc) : QVec n w cardAnc :=
  fun x y a => zdblPow k (ψ x y a)

theorem qzero_apply (n w cardAnc : Nat) (x : Fin n) (y : Fin (2 ^ w)) (a : Fin cardAnc) :
    qzero n w cardAnc x y a = zzero := by rfl

theorem qadd_apply {n w cardAnc : Nat} (ψ φ : QVec n w cardAnc)
    (x : Fin n) (y : Fin (2 ^ w)) (a : Fin cardAnc) :
    qadd ψ φ x y a = zadd (ψ x y a) (φ x y a) := by rfl

theorem qsub_apply {n w cardAnc : Nat} (ψ φ : QVec n w cardAnc)
    (x : Fin n) (y : Fin (2 ^ w)) (a : Fin cardAnc) :
    qsub ψ φ x y a = zsub (ψ x y a) (φ x y a) := by rfl

theorem qdblPow_apply {n w cardAnc : Nat} (k : Nat) (ψ : QVec n w cardAnc)
    (x : Fin n) (y : Fin (2 ^ w)) (a : Fin cardAnc) :
    qdblPow k ψ x y a = zdblPow k (ψ x y a) := by rfl

theorem qsub_self {n w cardAnc : Nat} (ψ : QVec n w cardAnc) : qsub ψ ψ = qzero n w cardAnc :=
  funext fun _ => funext fun _ => funext fun _ => zsub_self _

/-- An adversary gate: any map on states that preserves pointwise subtraction. Every
    `Qsag.ScaledUnitary` is one (`QromRuntimeLaws.toBlockGate`); the support invariant uses
    nothing else about a gate. -/
structure BlockGate (n w cardAnc : Nat) where
  apply : QVec n w cardAnc → QVec n w cardAnc
  map_sub : ∀ ψ φ, apply (qsub ψ φ) = qsub (apply ψ) (apply φ)

/-- The identity gate. -/
def BlockGate.id (n w cardAnc : Nat) : BlockGate n w cardAnc where
  apply ψ := ψ
  map_sub _ _ := rfl

theorem BlockGate.id_apply (n w cardAnc : Nat) (ψ : QVec n w cardAnc) :
    (BlockGate.id n w cardAnc).apply ψ = ψ := by rfl

theorem BlockGate.apply_zero {n w cardAnc : Nat} (U : BlockGate n w cardAnc) :
    U.apply (qzero n w cardAnc) = qzero n w cardAnc := by
  have h := U.map_sub (qzero n w cardAnc) (qzero n w cardAnc)
  rw [qsub_self] at h
  exact h.trans (qsub_self _)

theorem BlockGate.map_add {n w cardAnc : Nat} (U : BlockGate n w cardAnc)
    (ψ φ : QVec n w cardAnc) : U.apply (qadd ψ φ) = qadd (U.apply ψ) (U.apply φ) := by
  have he : qsub (qadd ψ φ) φ = ψ :=
    funext fun _ => funext fun _ => funext fun _ => zsub_zadd_cancel _ _
  have h := U.map_sub (qadd ψ φ) φ
  rw [he] at h
  funext x y a
  have hp := congrFun (congrFun (congrFun h x) y) a
  have hr := congrArg GaussInt.re hp
  have hi := congrArg GaussInt.im hp
  dsimp only [qsub, zsub] at hr hi
  apply GaussInt.ext <;> dsimp only [qadd, zadd] <;> omega

