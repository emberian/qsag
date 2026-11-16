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

theorem BlockGate.map_dblPow {n w cardAnc : Nat} (U : BlockGate n w cardAnc)
    (ψ : QVec n w cardAnc) : ∀ k, U.apply (qdblPow k ψ) = qdblPow k (U.apply ψ)
  | 0 => rfl
  | k + 1 => by
    show U.apply (qadd (qdblPow k ψ) (qdblPow k ψ)) =
      qadd (qdblPow k (U.apply ψ)) (qdblPow k (U.apply ψ))
    rw [U.map_add, BlockGate.map_dblPow U ψ k]

/-- A gate commutes with the block transform of the oracle register. -/
theorem bitWalsh_local {n w cardAnc : Nat} (U : BlockGate n w cardAnc) : ∀ (k : Nat)
    (ψ : OracleBitTable k → QVec n w cardAnc) (e : OracleBitTable k),
    U.apply (fun x y a => bitWalsh k (fun b => ψ b x y a) e) =
      fun x y a => bitWalsh k (fun b => U.apply (ψ b) x y a) e
  | 0, _, _ => rfl
  | k + 1, ψ, (b, e) => by
    cases b
    · show U.apply (qadd (fun x y a => bitWalsh k (fun h => ψ (false, h) x y a) e)
        (fun x y a => bitWalsh k (fun h => ψ (true, h) x y a) e)) = _
      rw [U.map_add, bitWalsh_local U k (fun h => ψ (false, h)) e,
        bitWalsh_local U k (fun h => ψ (true, h)) e]
      rfl
    · show U.apply (qsub (fun x y a => bitWalsh k (fun h => ψ (false, h) x y a) e)
        (fun x y a => bitWalsh k (fun h => ψ (true, h) x y a) e)) = _
      rw [U.map_sub, bitWalsh_local U k (fun h => ψ (false, h)) e,
        bitWalsh_local U k (fun h => ψ (true, h)) e]
      rfl

/-- A gate commutes with the table transform: nothing acts on the oracle register but the
    query. -/
theorem blockWalsh_local {n w cardAnc : Nat} (U : BlockGate n w cardAnc) : ∀ (m : Nat)
    (ψ : BlockTable w m → QVec n w cardAnc) (d : BlockTable w m),
    U.apply (fun x y a => blockWalsh w m (fun h => ψ h x y a) d) =
      fun x y a => blockWalsh w m (fun h => U.apply (ψ h) x y a) d
  | 0, _, _ => rfl
  | m + 1, ψ, (e, d) => by
    refine (bitWalsh_local U w
      (fun b => fun x y a => blockWalsh w m (fun h => ψ (b, h) x y a) d) e).trans ?_
    funext x y a
    show bitWalsh w (fun b => U.apply
        (fun x y a => blockWalsh w m (fun h => ψ (b, h) x y a) d) x y a) e =
      bitWalsh w (fun b => blockWalsh w m (fun h => U.apply (ψ (b, h)) x y a) d) e
    exact congrArg (fun F => bitWalsh w F e) (funext fun b =>
      congrFun (congrFun (congrFun (blockWalsh_local U m (fun h => ψ (b, h)) d) x) y) a)

/-- The value of a block as a `w`-bit answer. -/
def blockValue : (k : Nat) → OracleBitTable k → BitVec k
  | 0, _ => BitVec.nil
  | k + 1, (b, e) => BitVec.cons b (blockValue k e)

/-- The oracle `Fin n → BitVec w` whose truth table is `h`. -/
def blockOracle (w n : Nat) (h : BlockTable w n) : Fin n → BitVec w :=
  fun x => blockValue w (blockAt w n h x)

theorem blockOracle_apply (w n : Nat) (h : BlockTable w n) (x : Fin n) :
    blockOracle w n h x = blockValue w (blockAt w n h x) := by rfl

/-- The XOR query `|x, y, a⟩ ↦ |x, y ⊕ H x, a⟩` on amplitudes, with the body of
    `Qsag.oracleXor`. -/
def blockQuery {n w cardAnc : Nat} (H : Fin n → BitVec w) (ψ : QVec n w cardAnc) :
    QVec n w cardAnc :=
  fun x y a => ψ x (xorFin y (H x)) a

theorem blockQuery_apply {n w cardAnc : Nat} (H : Fin n → BitVec w) (ψ : QVec n w cardAnc)
    (x : Fin n) (y : Fin (2 ^ w)) (a : Fin cardAnc) :
    blockQuery H ψ x y a = ψ x (xorFin y (H x)) a := by rfl

@[expose] def fourierBlockState {w n cardAnc : Nat} (ψ : CoherentBlockState w n cardAnc) :
    CoherentBlockState w n cardAnc :=
  fun d x y a => blockWalsh w n (fun h => ψ h x y a) d

def doubleBlockState {w n cardAnc : Nat} (k : Nat) (ψ : CoherentBlockState w n cardAnc) :
    CoherentBlockState w n cardAnc :=
  fun h => qdblPow k (ψ h)

theorem fourierBlockState_apply {w n cardAnc : Nat} (ψ : CoherentBlockState w n cardAnc)
    (d : BlockTable w n) (x : Fin n) (y : Fin (2 ^ w)) (a : Fin cardAnc) :
    fourierBlockState ψ d x y a = blockWalsh w n (fun h => ψ h x y a) d := by rfl

theorem fourierBlockState_square {w n cardAnc : Nat} (ψ : CoherentBlockState w n cardAnc) :
    fourierBlockState (fourierBlockState ψ) = doubleBlockState (n * w) ψ := by
  funext h x y a
  exact blockWalsh_square w n _ h

theorem fourierBlockState_double {w n cardAnc : Nat} (k : Nat)
    (ψ : CoherentBlockState w n cardAnc) :
    fourierBlockState (doubleBlockState k ψ) = doubleBlockState k (fourierBlockState ψ) := by
  funext h x y a
  exact blockWalsh_dbl w n _ h k

theorem doubleBlockState_add {w n cardAnc : Nat} (k l : Nat)
    (ψ : CoherentBlockState w n cardAnc) :
    doubleBlockState k (doubleBlockState l ψ) = doubleBlockState (k + l) ψ := by
  funext h x y a
  exact zdblPow_add_exp k l _

/-- **A full `w`-bit XOR query only mixes labels that differ in the queried block.** If the
    Fourier register vanishes on every label obtained from `d` by rewriting one block, it
    still vanishes at `d` after the query, for every superposition of addresses. -/
theorem fourier_block_query_zero {w n cardAnc : Nat} (ψ : CoherentBlockState w n cardAnc)
    (d : BlockTable w n)
    (hz : ∀ x e, fourierBlockState ψ (setBlock w n d x e) = qzero n w cardAnc) :
    fourierBlockState (fun h => blockQuery (blockOracle w n h) (ψ h)) d = qzero n w cardAnc := by
  funext x y a
  show blockWalsh w n (fun h => ψ h x (xorFin y (blockValue w (blockAt w n h x))) a) d = zzero
  refine blockWalsh_query w n (fun h v => ψ h x (xorFin y (blockValue w v)) a) d x
    (fun v e => ?_)
  exact congrFun (congrFun (congrFun (hz x e) x) (xorFin y (blockValue w v))) a

/-! ## §6. Block-valued adversaries and the three support theorems -/

/-- A `Q`-query adversary against an oracle with `w`-bit answers. -/
structure BlockAdv (n w cardAnc Q : Nat) where
  init : QVec n w cardAnc
  steps : Fin Q → BlockGate n w cardAnc

/-- State before query `t`, with the recursion of `Qsag.advStateAt`. -/
def blockAdvStateAt {n w cardAnc Q : Nat} (A : BlockAdv n w cardAnc Q)
    (H : Fin n → BitVec w) : (t : Nat) → t ≤ Q → QVec n w cardAnc
  | 0, _ => A.init
  | t + 1, ht =>
    (A.steps ⟨t, ht⟩).apply (blockQuery H (blockAdvStateAt A H t (Nat.le_of_succ_le ht)))

theorem blockAdvStateAt_zero {n w cardAnc Q : Nat} (A : BlockAdv n w cardAnc Q)
    (H : Fin n → BitVec w) (h0 : 0 ≤ Q) : blockAdvStateAt A H 0 h0 = A.init := by rfl

theorem blockAdvStateAt_succ {n w cardAnc Q : Nat} (A : BlockAdv n w cardAnc Q)
    (H : Fin n → BitVec w) (t : Nat) (ht : t + 1 ≤ Q) :
    blockAdvStateAt A H (t + 1) ht =
      (A.steps ⟨t, ht⟩).apply (blockQuery H (blockAdvStateAt A H t (Nat.le_of_succ_le ht))) := by
  rfl

/-- **Coherent sparsity for `w`-bit answers.** After `t` queries the Fourier register has no
    amplitude on a database with more than `t` nonzero blocks. Queries are in superposition;
    no address is measured and no cover premise is assumed. -/
theorem block_fourier_coherent_support {n w cardAnc Q : Nat} (A : BlockAdv n w cardAnc Q) :
    ∀ (t : Nat) (ht : t ≤ Q) (d : BlockTable w n), t < blockWeight w n d →
      fourierBlockState (fun h => blockAdvStateAt A (blockOracle w n h) t ht) d =
        qzero n w cardAnc
  | 0, _, d, hd => by
    funext x y a
    exact blockWalsh_const w n (A.init x y a) d (by omega)
  | t + 1, ht, d, hd => by
    have hT : ∀ x e, fourierBlockState
        (fun h => blockAdvStateAt A (blockOracle w n h) t (Nat.le_of_succ_le ht))
        (setBlock w n d x e) = qzero n w cardAnc := by
      intro x e
      have hw := blockWeight_setBlock_le w n d x e
      exact block_fourier_coherent_support A t (Nat.le_of_succ_le ht) _ (by omega)
    have hz := fourier_block_query_zero
      (fun h => blockAdvStateAt A (blockOracle w n h) t (Nat.le_of_succ_le ht)) d hT
    have hl := blockWalsh_local (A.steps ⟨t, ht⟩) n
      (fun h => blockQuery (blockOracle w n h)
        (blockAdvStateAt A (blockOracle w n h) t (Nat.le_of_succ_le ht))) d
    show (fun x y a => blockWalsh w n
      (fun h => (A.steps ⟨t, ht⟩).apply (blockQuery (blockOracle w n h)
        (blockAdvStateAt A (blockOracle w n h) t (Nat.le_of_succ_le ht))) x y a) d) = _
    rw [← hl]
    show (A.steps ⟨t, ht⟩).apply (fourierBlockState
      (fun h => blockQuery (blockOracle w n h)
        (blockAdvStateAt A (blockOracle w n h) t (Nat.le_of_succ_le ht))) d) = _
    rw [hz, BlockGate.apply_zero]

/-- One coherent query to the block table, then the oracle-independent gate. -/
def coherentBlockStep {w n cardAnc : Nat} (U : BlockGate n w cardAnc)
    (ψ : CoherentBlockState w n cardAnc) : CoherentBlockState w n cardAnc :=
  fun h => U.apply (blockQuery (blockOracle w n h) (ψ h))

/-- The same step conjugated into the Fourier basis of the oracle register. The unnormalized
    transform multiplies amplitudes by `2 ^ (n * w)` per step. -/
def fourierBlockStep {w n cardAnc : Nat} (U : BlockGate n w cardAnc)
    (ψ : CoherentBlockState w n cardAnc) : CoherentBlockState w n cardAnc :=
  fourierBlockState (coherentBlockStep U (fourierBlockState ψ))

theorem coherentBlockStep_double {w n cardAnc : Nat} (U : BlockGate n w cardAnc) (k : Nat)
    (ψ : CoherentBlockState w n cardAnc) :
    coherentBlockStep U (doubleBlockState k ψ) = doubleBlockState k (coherentBlockStep U ψ) := by
  funext h
  exact U.map_dblPow (blockQuery (blockOracle w n h) (ψ h)) k

/-- The runtime stepped entirely in the Fourier basis, started on the Fourier encoding of the
    uniform superposition of oracles. -/
@[expose] def fourierBlockAdvStateAt {n w cardAnc Q : Nat} (A : BlockAdv n w cardAnc Q) :
    (t : Nat) → t ≤ Q → CoherentBlockState w n cardAnc
  | 0, _ => fourierBlockState (fun _ => A.init)
  | t + 1, ht => fourierBlockStep (A.steps ⟨t, ht⟩)
      (fourierBlockAdvStateAt A t (Nat.le_of_succ_le ht))

/-- The Fourier runtime is the transform of the ordinary coherent execution, up to the known
    oracle-independent scale `2 ^ ((n * w) * t)`. -/
theorem fourierBlockAdvStateAt_eq {n w cardAnc Q : Nat} (A : BlockAdv n w cardAnc Q) :
    ∀ (t : Nat) (ht : t ≤ Q), fourierBlockAdvStateAt A t ht =
      doubleBlockState ((n * w) * t)
        (fourierBlockState (fun h => blockAdvStateAt A (blockOracle w n h) t ht))
  | 0, _ => rfl
  | t + 1, ht => by
    show fourierBlockState (coherentBlockStep (A.steps ⟨t, ht⟩)
      (fourierBlockState (fourierBlockAdvStateAt A t (Nat.le_of_succ_le ht)))) = _
    rw [fourierBlockAdvStateAt_eq A t (Nat.le_of_succ_le ht), fourierBlockState_double,
      fourierBlockState_square, doubleBlockState_add, coherentBlockStep_double,
      fourierBlockState_double, Nat.mul_succ]
    rfl

/-- **Runtime support for `w`-bit answers.** The independently stepped Fourier runtime obeys
    the same cap: at most `t` nonzero blocks after `t` queries. -/
theorem block_fourier_runtime_support {n w cardAnc Q : Nat} (A : BlockAdv n w cardAnc Q)
    (t : Nat) (ht : t ≤ Q) (d : BlockTable w n) (hd : t < blockWeight w n d) :
    fourierBlockAdvStateAt A t ht d = qzero n w cardAnc := by
  rw [fourierBlockAdvStateAt_eq]
  show qdblPow ((n * w) * t) (fourierBlockState
    (fun h => blockAdvStateAt A (blockOracle w n h) t ht) d) = _
  rw [block_fourier_coherent_support A t ht d hd]
  funext x y a
  exact zdblPow_zzero _

/-- Squared modulus, with the body of `Qsag.GaussInt.normSq`. -/
def znormSq (z : GaussInt) : Nat := z.re.natAbs * z.re.natAbs + z.im.natAbs * z.im.natAbs

/-- Squared norm of a state, with the body of `Qsag.QVec.stateNormSq`. The response register
    is summed by `qsum (2 ^ w)`; nothing below evaluates that sum. -/
def qnormSq {n w cardAnc : Nat} (ψ : QVec n w cardAnc) : Nat :=
  qsum n (fun x => qsum (2 ^ w) (fun y => qsum cardAnc (fun a => znormSq (ψ x y a))))

theorem qnormSq_qzero (n w cardAnc : Nat) : qnormSq (qzero n w cardAnc) = 0 := by
  show qsum n (fun _ => qsum (2 ^ w) (fun _ => qsum cardAnc (fun _ => 0))) = 0
  rw [qsum_const cardAnc 0, qsum_const (2 ^ w) (cardAnc * 0), qsum_const,
    Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]

/-- Sum over every database label, one block at a time. -/
def blockTableSum (w : Nat) : (n : Nat) → (BlockTable w n → Nat) → Nat
  | 0, f => f ()
  | n + 1, f => oracleTableSum w (fun e => blockTableSum w n (fun d => f (e, d)))

theorem blockTableSum_zero_fun (w : Nat) : ∀ n, blockTableSum w n (fun _ => 0) = 0
  | 0 => rfl
  | n + 1 => by
    show oracleTableSum w (fun _ => blockTableSum w n (fun _ => 0)) = 0
    exact (oracleTableSum_congr w _ (fun _ => 0 * 0) (fun _ => blockTableSum_zero_fun w n)).trans
      ((oracleTableSum_mul w 0 (fun _ => 0)).trans (Nat.zero_mul _))

/-- **Database overflow has zero mass for `w`-bit answers.** A terminal measurement of the
    Fourier label never reports more than `Q` nonzero blocks. -/
theorem block_fourier_database_overflow_mass_zero {n w cardAnc Q : Nat}
    (A : BlockAdv n w cardAnc Q) :
    blockTableSum w n (fun d => if Q < blockWeight w n d then
      qnormSq (fourierBlockAdvStateAt A Q (Nat.le_refl Q) d) else 0) = 0 := by
  have h : (fun d : BlockTable w n => if Q < blockWeight w n d then
      qnormSq (fourierBlockAdvStateAt A Q (Nat.le_refl Q) d) else 0) = fun _ => 0 := by
    funext d
    by_cases hd : Q < blockWeight w n d
    · rw [ite_eq_left hd, block_fourier_runtime_support A Q (Nat.le_refl Q) d hd, qnormSq_qzero]
    · exact ite_eq_right hd
  exact (congrArg (blockTableSum w n) h).trans (blockTableSum_zero_fun w n)

/-! ### Sharpness at the empty database -/

/-- Before any query the empty database carries the whole initial state, scaled by
    `2 ^ (n * w)`. The hypothesis `t < blockWeight w n d` of the support theorems therefore
    cannot be weakened to `t ≤ blockWeight w n d`. -/
theorem fourier_block_initial_zeroLabel {n w cardAnc Q : Nat} (A : BlockAdv n w cardAnc Q)
    (h0 : 0 ≤ Q) :
    fourierBlockState (fun h => blockAdvStateAt A (blockOracle w n h) 0 h0) (zeroLabel w n) =
      qdblPow (n * w) A.init := by
  funext x y a
  exact blockWalsh_const_zeroLabel w n (A.init x y a)

theorem fourierBlockAdvStateAt_initial_zeroLabel {n w cardAnc Q : Nat}
    (A : BlockAdv n w cardAnc Q) (h0 : 0 ≤ Q) :
    fourierBlockAdvStateAt A 0 h0 (zeroLabel w n) = qdblPow (n * w) A.init :=
  fourier_block_initial_zeroLabel A h0

/-- A state with a nonzero amplitude is not the zero state after doubling. -/
theorem qdblPow_ne_qzero {n w cardAnc : Nat} (k : Nat) (ψ : QVec n w cardAnc)
    (x : Fin n) (y : Fin (2 ^ w)) (a : Fin cardAnc) (hne : ¬ (ψ x y a = zzero)) :
    ¬ (qdblPow k ψ = qzero n w cardAnc) :=
  fun h => hne (zdblPow_eq_zzero k _ (congrFun (congrFun (congrFun h x) y) a))

/-! ## §7. The deployed digest width, `w = 256`

These are instantiations of the parametric theorems. Their types mention `Fin (2 ^ 256)` as
an index type only; no term is reduced and no sum over it is evaluated. -/

theorem block256_fourier_coherent_support {n cardAnc Q : Nat} (A : BlockAdv n 256 cardAnc Q)
    (t : Nat) (ht : t ≤ Q) (d : BlockTable 256 n) (hd : t < blockWeight 256 n d) :
    fourierBlockState (fun h => blockAdvStateAt A (blockOracle 256 n h) t ht) d =
      qzero n 256 cardAnc :=
  block_fourier_coherent_support A t ht d hd

theorem block256_fourier_runtime_support {n cardAnc Q : Nat} (A : BlockAdv n 256 cardAnc Q)
    (t : Nat) (ht : t ≤ Q) (d : BlockTable 256 n) (hd : t < blockWeight 256 n d) :
    fourierBlockAdvStateAt A t ht d = qzero n 256 cardAnc :=
  block_fourier_runtime_support A t ht d hd

theorem block256_fourier_database_overflow_mass_zero {n cardAnc Q : Nat}
    (A : BlockAdv n 256 cardAnc Q) :
    blockTableSum 256 n (fun d => if Q < blockWeight 256 n d then
      qnormSq (fourierBlockAdvStateAt A Q (Nat.le_refl Q) d) else 0) = 0 :=
  block_fourier_database_overflow_mass_zero A

/-- A one-address database whose single block has exactly its top bit set. -/
def hotLabel (k : Nat) : BlockTable (k + 1) 1 := ((true, bitsZero k), ())

theorem blockWeight_hotLabel (k : Nat) : blockWeight (k + 1) 1 (hotLabel k) = 1 := by rfl

/-- A two-address database with both blocks nonzero. -/
def hotLabel₂ (k : Nat) : BlockTable (k + 1) 2 := ((true, bitsZero k), ((true, bitsZero k), ()))

theorem blockWeight_hotLabel₂ (k : Nat) : blockWeight (k + 1) 2 (hotLabel₂ k) = 2 := by rfl

/-! ## §8. Transport to `Qsag.QuantumAdv` and the one-bit statement

The fields below are the defining equations of constants whose bodies `Qrom.lean` keeps
private to its own module. Each is closed by `rfl` in a module that can see those bodies. -/

/-- Defining equations of the `Qrom` runtime for an arbitrary answer width. -/
structure QromRuntimeLaws : Prop where
  qvec_zero : ∀ (n w cardAnc : Nat), QVec.zero n w cardAnc = qzero n w cardAnc
  qvec_sub : ∀ {n w cardAnc : Nat} (ψ φ : QVec n w cardAnc), QVec.sub ψ φ = qsub ψ φ
  oracle_xor : ∀ {n w cardAnc : Nat} (H : Fin n → BitVec w) (ψ : QVec n w cardAnc),
    oracleXor H ψ = blockQuery H ψ
  adv_zero : ∀ {n w cardAnc q : Nat} (A : QuantumAdv n w cardAnc q) (H : Fin n → BitVec w)
    (h0 : 0 ≤ q), advStateAt A H 0 h0 = A.init
  adv_succ : ∀ {n w cardAnc q : Nat} (A : QuantumAdv n w cardAnc q) (H : Fin n → BitVec w)
    (t : Nat) (ht : t + 1 ≤ q), advStateAt A H (t + 1) ht =
      (A.steps ⟨t, ht⟩).apply (oracleXor H (advStateAt A H t (Nat.le_of_succ_le ht)))

/-- Every scaled unitary is a block gate. -/
def QromRuntimeLaws.toBlockGate (L : QromRuntimeLaws) {n w cardAnc : Nat}
    (U : ScaledUnitary n w cardAnc) : BlockGate n w cardAnc where
  apply := U.apply
  map_sub ψ φ := by rw [← L.qvec_sub, ← L.qvec_sub]; exact U.map_sub ψ φ

/-- Every `Qrom` adversary is a block adversary with the same initial state and gates. -/
def QromRuntimeLaws.toBlockAdv (L : QromRuntimeLaws) {n w cardAnc Q : Nat}
    (A : QuantumAdv n w cardAnc Q) : BlockAdv n w cardAnc Q where
  init := A.init
  steps i := L.toBlockGate (A.steps i)

theorem QromRuntimeLaws.advStateAt_eq (L : QromRuntimeLaws) {n w cardAnc Q : Nat}
    (A : QuantumAdv n w cardAnc Q) (H : Fin n → BitVec w) :
    ∀ (t : Nat) (ht : t ≤ Q), advStateAt A H t ht = blockAdvStateAt (L.toBlockAdv A) H t ht
  | 0, h0 => L.adv_zero A H h0
  | t + 1, ht => by
    rw [L.adv_succ A H t ht, L.oracle_xor, QromRuntimeLaws.advStateAt_eq L A H t
      (Nat.le_of_succ_le ht)]
    rfl

/-- `fourier_coherent_support` of `Qrom.lean` for `QuantumAdv n w …` with `w` arbitrary. -/
theorem qrom_block_fourier_coherent_support (L : QromRuntimeLaws) {n w cardAnc Q : Nat}
    (A : QuantumAdv n w cardAnc Q) (t : Nat) (ht : t ≤ Q) (d : BlockTable w n)
    (hd : t < blockWeight w n d) :
    fourierBlockState (fun h => advStateAt A (blockOracle w n h) t ht) d =
      QVec.zero n w cardAnc := by
  have hfun : (fun h => advStateAt A (blockOracle w n h) t ht) =
      fun h => blockAdvStateAt (L.toBlockAdv A) (blockOracle w n h) t ht :=
    funext fun h => L.advStateAt_eq A (blockOracle w n h) t ht
  rw [hfun, L.qvec_zero]
  exact block_fourier_coherent_support (L.toBlockAdv A) t ht d hd

/-- The deployed width: the support cap for `Qrom` adversaries with 256-bit answers. -/
theorem qrom_block256_fourier_coherent_support (L : QromRuntimeLaws) {n cardAnc Q : Nat}
    (A : QuantumAdv n 256 cardAnc Q) (t : Nat) (ht : t ≤ Q) (d : BlockTable 256 n)
    (hd : t < blockWeight 256 n d) :
    fourierBlockState (fun h => advStateAt A (blockOracle 256 n h) t ht) d =
      QVec.zero n 256 cardAnc :=
  qrom_block_fourier_coherent_support L A t ht d hd

/-- Defining equations of the one-bit Fourier objects of `Qrom.lean`. -/
structure QromBitTableLaws : Prop where
  walsh_zero : ∀ (f : OracleBitTable 0 → GaussInt) (u : OracleBitTable 0),
    oracleWalsh 0 f u = f ()
  walsh_succ : ∀ (n : Nat) (f : OracleBitTable (n + 1) → GaussInt) (b : Bool)
    (d : OracleBitTable n), oracleWalsh (n + 1) f (b, d) =
      if b then zsub (oracleWalsh n (fun h => f (false, h)) d)
        (oracleWalsh n (fun h => f (true, h)) d)
      else zadd (oracleWalsh n (fun h => f (false, h)) d)
        (oracleWalsh n (fun h => f (true, h)) d)
  fourier_state : ∀ {n cardAnc : Nat} (ψ : CoherentBitState n cardAnc) (d : OracleBitTable n),
    fourierOracleState ψ d = fun x y a => oracleWalsh n (fun h => ψ h x y a) d
  weight_zero : ∀ u : OracleBitTable 0, tableWeight 0 u = 0
  weight_succ : ∀ (n : Nat) (b : Bool) (d : OracleBitTable n),
    tableWeight (n + 1) (b, d) = (if b then 1 else 0) + tableWeight n d
  bit_oracle_succ : ∀ (n : Nat) (b : Bool) (h : OracleBitTable n) (x : Fin (n + 1)),
    tableBitOracle (n + 1) (b, h) x =
      Fin.cases (if b then 1#1 else 0#1) (tableBitOracle n h) x

/-- A one-bit table as a table of one-bit blocks. -/
def liftBits : (n : Nat) → OracleBitTable n → BlockTable 1 n
  | 0, _ => ()
  | n + 1, (b, h) => ((b, ()), liftBits n h)

def lowerBits : (n : Nat) → BlockTable 1 n → OracleBitTable n
  | 0, _ => ()
  | n + 1, ((b, _), h) => (b, lowerBits n h)

theorem lowerBits_liftBits : ∀ (n : Nat) (h : OracleBitTable n), lowerBits n (liftBits n h) = h
  | 0, () => rfl
  | n + 1, (b, h) => by
    show (b, lowerBits n (liftBits n h)) = (b, h)
    rw [lowerBits_liftBits n h]

theorem liftBits_lowerBits : ∀ (n : Nat) (h : BlockTable 1 n), liftBits n (lowerBits n h) = h
  | 0, () => rfl
  | n + 1, ((b, ()), h) => by
    show ((b, ()), liftBits n (lowerBits n h)) = ((b, ()), h)
    rw [liftBits_lowerBits n h]

theorem QromBitTableLaws.walsh_eq (B : QromBitTableLaws) : ∀ (n : Nat)
    (f : OracleBitTable n → GaussInt) (d : OracleBitTable n),
    oracleWalsh n f d = blockWalsh 1 n (fun h => f (lowerBits n h)) (liftBits n d)
  | 0, f, u => B.walsh_zero f u
  | n + 1, f, (b, d) => by
    rw [B.walsh_succ, QromBitTableLaws.walsh_eq B n (fun h => f (false, h)) d,
      QromBitTableLaws.walsh_eq B n (fun h => f (true, h)) d]
    cases b <;> rfl

theorem QromBitTableLaws.weight_eq (B : QromBitTableLaws) : ∀ (n : Nat) (d : OracleBitTable n),
    tableWeight n d = blockWeight 1 n (liftBits n d)
  | 0, u => B.weight_zero u
  | n + 1, (b, d) => by
    rw [B.weight_succ, QromBitTableLaws.weight_eq B n d]
    cases b <;> rfl

theorem QromBitTableLaws.bit_oracle_eq (B : QromBitTableLaws) : ∀ (n : Nat)
    (h : OracleBitTable n) (x : Fin n), tableBitOracle n h x = blockOracle 1 n (liftBits n h) x
  | 0, _, x => x.elim0
  | n + 1, (b, h), x => by
    rw [B.bit_oracle_succ]
    refine Fin.cases ?_ (fun j => ?_) x
    · cases b <;> rfl
    · exact QromBitTableLaws.bit_oracle_eq B n h j

/-- **The one-bit statement is the `w = 1` instance.** This has the statement of
    `Qsag.fourier_coherent_support` and is derived from `block_fourier_coherent_support` at
    `w = 1`, not from the `Qrom` proof. -/
theorem qrom_fourier_coherent_support_recovered (L : QromRuntimeLaws) (B : QromBitTableLaws)
    {n cardAnc Q : Nat} (A : QuantumAdv n 1 cardAnc Q) (t : Nat) (ht : t ≤ Q)
    (d : OracleBitTable n) (hd : t < tableWeight n d) :
    fourierOracleState (fun h => advStateAt A (tableBitOracle n h) t ht) d =
      QVec.zero n 1 cardAnc := by
  rw [B.weight_eq] at hd
  have hBlock := qrom_block_fourier_coherent_support L A t ht (liftBits n d) hd
  rw [B.fourier_state, ← hBlock]
  funext x y a
  rw [B.walsh_eq]
  show blockWalsh 1 n (fun h => advStateAt A (tableBitOracle n (lowerBits n h)) t ht x y a)
      (liftBits n d) =
    blockWalsh 1 n (fun h => advStateAt A (blockOracle 1 n h) t ht x y a) (liftBits n d)
  have hO : ∀ h : BlockTable 1 n, tableBitOracle n (lowerBits n h) = blockOracle 1 n h := by
    intro h
    funext x'
    rw [B.bit_oracle_eq, liftBits_lowerBits]
  exact congrArg (fun F => blockWalsh 1 n F (liftBits n d))
    (funext fun h => by rw [hO h])

/-! ## §9 The law structures hold for `Qsag.Oracle.Qrom` -/

theorem gaussZero_eq : GaussInt.zero = zzero := by rw [GaussInt.zero_def, zzero_eq]
theorem gaussAdd_eq (z v : GaussInt) : GaussInt.add z v = zadd z v := by
  rw [GaussInt.add_def, zadd_eq]
theorem gaussSub_eq (z v : GaussInt) : GaussInt.sub z v = zsub z v := by
  rw [GaussInt.sub_def, zsub_eq]

theorem qromRuntimeLaws : QromRuntimeLaws where
  qvec_zero n w cardAnc := by
    funext x y a
    rw [QVec.zero_apply, qzero_apply, gaussZero_eq]
  qvec_sub ψ φ := by
    funext x y a
    rw [QVec.sub_apply, qsub_apply, gaussSub_eq]
  oracle_xor H ψ := by
    funext x y a
    rw [oracleXor_apply, blockQuery_apply]
  adv_zero A H h0 := advStateAt_zero A H h0
  adv_succ A H t ht := advStateAt_succ A H t ht

theorem qromBitTableLaws : QromBitTableLaws where
  walsh_zero f u := oracleWalsh_zero f u
  walsh_succ n f b d := by
    rw [oracleWalsh_succ, gaussSub_eq, gaussAdd_eq]
  fourier_state ψ d := by
    funext x y a
    exact fourierOracleState_apply ψ d x y a
  weight_zero u := tableWeight_zero u
  weight_succ n b d := tableWeight_succ n b d
  bit_oracle_succ n b h x := tableBitOracle_succ n b h x

/-- Block support for `Qsag.QuantumAdv`, any answer width. -/
theorem quantumAdv_block_fourier_coherent_support {n w cardAnc Q : Nat}
    (A : QuantumAdv n w cardAnc Q) (t : Nat) (ht : t ≤ Q) (d : BlockTable w n)
    (hd : t < blockWeight w n d) :
    fourierBlockState (fun h => advStateAt A (blockOracle w n h) t ht) d =
      QVec.zero n w cardAnc :=
  qrom_block_fourier_coherent_support qromRuntimeLaws A t ht d hd

/-- The one-bit statement, from the block theorem at `w = 1`. -/
theorem quantumAdv_fourier_coherent_support_from_block {n cardAnc Q : Nat}
    (A : QuantumAdv n 1 cardAnc Q) (t : Nat) (ht : t ≤ Q) (d : OracleBitTable n)
    (hd : t < tableWeight n d) :
    fourierOracleState (fun h => advStateAt A (tableBitOracle n h) t ht) d =
      QVec.zero n 1 cardAnc :=
  qrom_fourier_coherent_support_recovered qromRuntimeLaws qromBitTableLaws A t ht d hd

/-- The deployed answer width `w = 256`, for `Qsag.QuantumAdv`. -/
theorem quantumAdv_block256_fourier_coherent_support {n cardAnc Q : Nat}
    (A : QuantumAdv n 256 cardAnc Q) (t : Nat) (ht : t ≤ Q) (d : BlockTable 256 n)
    (hd : t < blockWeight 256 n d) :
    fourierBlockState (fun h => advStateAt A (blockOracle 256 n h) t ht) d =
      QVec.zero n 256 cardAnc :=
  qrom_block256_fourier_coherent_support qromRuntimeLaws A t ht d hd

#verify_constructive
  Qsag.BlockCompressedOracle.qromRuntimeLaws
  Qsag.BlockCompressedOracle.qromBitTableLaws
  Qsag.BlockCompressedOracle.quantumAdv_block_fourier_coherent_support
  Qsag.BlockCompressedOracle.quantumAdv_block256_fourier_coherent_support
  Qsag.BlockCompressedOracle.quantumAdv_fourier_coherent_support_from_block

end Qsag.BlockCompressedOracle
