module
/-
# Qsag.Protocol.Threshold.LatticePreprocessingFull — End-to-End Lattice Base-OT, OR-Sigma, Bitwise KOS, Binary LHL & Dense Dual-LPN PCG

Constructive algebra and executable preprocessing models. This module does not establish
end-to-end active security of the Rust preprocessing protocol.
1. Negacyclic arithmetic, exact rounding margins, and FO acceptance under explicit key premises.
2. Production v3 joint Fiat–Shamir framing and 11-bit signed-monomial OR-Sigma challenges
   (`24 × 11 = 264` classical / `132` Grover bits in `rlweZkpokPq256Reps`, alongside `13 × 11 = 143`
   legacy parameterization), with a constructive fork-difference extractor and total cyclotomic
   cofactor/isometric lifts. The relaxed relation is not itself a short-RLWE hardness assumption.
   Fixed-point `Q192` Gaussian rejection-sampling rounding, `K`-attempt HVZK simulation, abort
   marginal secret-independence, and dense expand-accumulate dual-LPN piling-up / ISD bounds are
   conditional on the finite-weight premises of `q192_gaussian_hvzk_statistical_distance`
   and the cost model of `pcg_dense_depth15_prange_and_stern_dumer_pq128`. The production
   Gaussian distribution and balanced dual-test hypotheses are not instantiated here.
3. **Real Bitwise-AND KOS OT Extension + `128 × 384` `GF(2)` Leftover Hash Lemma (`[P0-05]` Closure)**:
   - Exact 128-bit bitwise correlation `q_l = t_l ^^^ (x_l &&& Delta)` over `BitVec 128` (`Tower128Exec`).
   - `kos_bitwise_selective_failure_exact`: fault mask `e : BitVec 128` of Hamming weight `w` passes row
     check iff `e &&& Delta = 0#128`, satisfied by **exactly `2^(128 - w)`** of `2^128` keys `Delta`
     (exact probability `2^(-w)`, leaking `w` bits; `1/2` at `w = 1` `#tooth`), paired with `Tower128`
     linear sacrifice soundness (`≤ 1 / 2^128` when `e &&& Delta ≠ 0`) and sticky channel poisoning.
   - Constructive `128 × 384` `GF(2)` universal linear hash (`evalSystematicGF2 256 128`, `[I_128 | R_{128×256}]`),
     exact 2-universality, and constructive finite Leftover Hash Lemma (`finite_lhl_collision_bound`)
     proving statistical bias squared `≤ 2^(-130)` (`Δ_TV ≤ 2^(-65)`) after `s = 128` leakage bits on a
     `384`-bit source and joint selective-failure advantage `< 2^(-128)` for **every** pass event.
4. **Full GGM Punctured-Tree + Dense Dual-LPN PCG Correctness, SPCOT Tag Recomputation & Uniformity (`[P0-02]` Closure)**:
   - Depth-`d` binary GGM tree (`ggmExpandFull`, `ggmMakeCopath`, `ggmExpandPunctured`) proving exact leaf
     recovery at all `u ≠ p*` and `0#128` at `p*` (`ggmExpandPunctured_exact`), active `Tower128` SPCOT
     tag recomputation (`computeSpcotCheckTag`, `"QSAG.DPCG.SPCOT.TAG/v1"`), `LSB(macAlpha) == 1` and
     peer `LSB(alpha_sender) == 1` enforcement, and single-use `pcgSeedExpandMachine` (`P1-06`, `#tooth`).
   - Exact dense dual-LPN cancellation `(H * fullLeaves) ^^^ (H * puncLeaves ^^^ H[:, p*] · corr) = H[:, p*] · Δ`,
     constructive 50/50 share uniformity bijection (`pcg_dense_share_uniform_bijection`), and `#tooth`
     proving omitting `H * fullLeaves` collapses 1-density from `1/2` to `rowWeight / 2^d` (`1 / 2^d` in `P0-02`).
-/

public import Qsag.Tactic.Prelude
import all Qsag.Tactic.Prelude
public import Qsag.Math.Goldilocks
import all Qsag.Math.Goldilocks
public import Qsag.Math.Gf2Pow128
import all Qsag.Math.Gf2Pow128
public import Qsag.Protocol.Aggregation.UcGames
import all Qsag.Protocol.Aggregation.UcGames
public import Qsag.Exec.SimulationSpine
import all Qsag.Exec.SimulationSpine
import all Qsag.Oracle.Keccak
import all Qsag.Oracle.Poseidon2
public import Qsag.Protocol.Threshold.RlweCyclotomicExtraction
import all Qsag.Protocol.Threshold.RlweCyclotomicExtraction
public import Qsag.Protocol.Threshold.Preprocessing
import all Qsag.Protocol.Threshold.Preprocessing
public import Qsag.Math.Lattices
import all Qsag.Math.Lattices
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false

/-! ## 1. Negacyclic Ring $R_q = \mathbb{Z}_{12289}[X]/(X^{1024} + 1)$ & Rounding Margin -/

/-- Prime RLWE modulus $q = 12289$ ($q - 1 = 3 \cdot 2^{12}$). -/
def rlweQ : Nat := 12289

/-- Production RLWE ring dimension $N = 1024$. -/
def rlweN1024 : Nat := 1024

/-- Prime residue ring $\mathbb{Z}_{12289}$. -/
structure Zq12289 where
  val : Nat
  isLt : val < 12289
  deriving DecidableEq, Repr

theorem Zq12289.ext {a b : Zq12289} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp only [mk.injEq]; exact h

/-- Canonical projection $\mathbb{Z} \to \mathbb{Z}_{12289}$ via Euclidean modulo. -/
@[expose] def Zq12289.ofInt (z : Int) : Zq12289 :=
  ⟨(z % 12289).toNat, by
    have h0 : 0 ≤ z % 12289 := Int.emod_nonneg z (by decide)
    have h1 : z % 12289 < 12289 := Int.emod_lt_of_pos z (by decide)
    omega⟩

theorem Zq12289.ofInt_val_int (z : Int) : ((Zq12289.ofInt z).val : Int) = z % 12289 := by
  unfold Zq12289.ofInt
  dsimp only
  exact Int.toNat_of_nonneg (Int.emod_nonneg z (by decide))

@[simp] theorem Zq12289.ofInt_natVal (a : Zq12289) : Zq12289.ofInt (a.val : Int) = a := by
  apply Zq12289.ext
  have h := a.isLt
  unfold Zq12289.ofInt
  dsimp only
  omega

/-- Centered representative in $[-6144, 6144]$. -/
def Zq12289.centered (a : Zq12289) : Int :=
  if a.val ≤ 6144 then (a.val : Int) else (a.val : Int) - 12289

theorem Zq12289.ofInt_centered (a : Zq12289) : Zq12289.ofInt a.centered = a := by
  apply Zq12289.ext
  unfold Zq12289.centered Zq12289.ofInt
  dsimp only
  have h := a.isLt
  split <;> omega

theorem Zq12289.centered_ofInt_small {z : Int} (hz : z.natAbs ≤ 6144) :
    (Zq12289.ofInt z).centered = z := by
  unfold Zq12289.centered Zq12289.ofInt
  dsimp only
  omega

instance : CommRingOps Zq12289 where
  zero := ⟨0, by decide⟩
  one := ⟨1, by decide⟩
  add a b := ⟨(a.val + b.val) % 12289, Nat.mod_lt _ (by decide)⟩
  mul a b := ⟨(a.val * b.val) % 12289, Nat.mod_lt _ (by decide)⟩
  neg a := ⟨(12289 - a.val) % 12289, Nat.mod_lt _ (by decide)⟩
  sub a b := ⟨(a.val + 12289 - b.val) % 12289, Nat.mod_lt _ (by decide)⟩

theorem Zq12289.ofInt_zero : Zq12289.ofInt 0 = CommRingOps.zero := rfl
theorem Zq12289.ofInt_one : Zq12289.ofInt 1 = CommRingOps.one := rfl

theorem Zq12289.ofInt_add (x y : Int) :
    Zq12289.ofInt (x + y) = CommRingOps.add (Zq12289.ofInt x) (Zq12289.ofInt y) := by
  apply Zq12289.ext
  change ((x + y) % 12289).toNat = ((Zq12289.ofInt x).val + (Zq12289.ofInt y).val) % 12289
  have hx := Zq12289.ofInt_val_int x
  have hy := Zq12289.ofInt_val_int y
  have hxLt := (Zq12289.ofInt x).isLt
  have hyLt := (Zq12289.ofInt y).isLt
  have hMod : (x + y) % 12289 = (x % 12289 + y % 12289) % 12289 := Int.add_emod x y 12289
  rw [← hx, ← hy] at hMod
  omega

theorem Zq12289.ofInt_neg (x : Int) :
    Zq12289.ofInt (-x) = CommRingOps.neg (Zq12289.ofInt x) := by
  apply Zq12289.ext
  change ((-x) % 12289).toNat = (12289 - (Zq12289.ofInt x).val) % 12289
  have hx := Zq12289.ofInt_val_int x
  have hxLt := (Zq12289.ofInt x).isLt
  have hSum : (x + (-x)) % 12289 = 0 := by rw [Int.add_right_neg]; rfl
  have hMod : (x % 12289 + (-x) % 12289) % 12289 = 0 := by
    rw [← Int.add_emod]; exact hSum
  have hn0 : 0 ≤ (-x) % 12289 := Int.emod_nonneg (-x) (by decide)
  have hn1 : (-x) % 12289 < 12289 := Int.emod_lt_of_pos (-x) (by decide)
  rw [← hx] at hMod
  omega

theorem Zq12289.ofInt_sub (x y : Int) :
    Zq12289.ofInt (x - y) = CommRingOps.sub (Zq12289.ofInt x) (Zq12289.ofInt y) := by
  apply Zq12289.ext
  change ((x - y) % 12289).toNat = ((Zq12289.ofInt x).val + 12289 - (Zq12289.ofInt y).val) % 12289
  have hx := Zq12289.ofInt_val_int x
  have hy := Zq12289.ofInt_val_int y
  have hxLt := (Zq12289.ofInt x).isLt
  have hyLt := (Zq12289.ofInt y).isLt
  have hMod : (x - y) % 12289 = (x % 12289 - y % 12289) % 12289 := Int.sub_emod x y 12289
  rw [← hx, ← hy] at hMod
  omega

theorem Zq12289.ofInt_mul (x y : Int) :
    Zq12289.ofInt (x * y) = CommRingOps.mul (Zq12289.ofInt x) (Zq12289.ofInt y) := by
  apply Zq12289.ext
  change ((x * y) % 12289).toNat = ((Zq12289.ofInt x).val * (Zq12289.ofInt y).val) % 12289
  have hx := Zq12289.ofInt_val_int x
  have hy := Zq12289.ofInt_val_int y
  have hMod : (x * y) % 12289 = ((x % 12289) * (y % 12289)) % 12289 := Int.mul_emod x y 12289
  rw [← hx, ← hy] at hMod
  have hNat : (((Zq12289.ofInt x).val * (Zq12289.ofInt y).val : Nat) : Int) % 12289 =
      ((((Zq12289.ofInt x).val * (Zq12289.ofInt y).val) % 12289 : Nat) : Int) := by
    exact (Int.natCast_emod _ _).symm
  have hCast : ((Zq12289.ofInt x).val : Int) * ((Zq12289.ofInt y).val : Int) =
      (((Zq12289.ofInt x).val * (Zq12289.ofInt y).val : Nat) : Int) :=
    (Int.natCast_mul _ _).symm
  rw [hCast, hNat] at hMod
  have hPos : 0 ≤ (x * y) % 12289 := Int.emod_nonneg (x * y) (by decide)
  omega

instance : LawfulCommRing Zq12289 where
  add_assoc a b c := by
    rw [← a.ofInt_natVal, ← b.ofInt_natVal, ← c.ofInt_natVal]
    simp only [← Zq12289.ofInt_add, Int.add_assoc]
  add_comm a b := by
    rw [← a.ofInt_natVal, ← b.ofInt_natVal]
    simp only [← Zq12289.ofInt_add, Int.add_comm]
  zero_add a := by
    rw [← a.ofInt_natVal, ← Zq12289.ofInt_zero, ← Zq12289.ofInt_add, Int.zero_add]
  add_zero a := by
    rw [← a.ofInt_natVal, ← Zq12289.ofInt_zero, ← Zq12289.ofInt_add, Int.add_zero]
  add_left_neg a := by
    rw [← a.ofInt_natVal, ← Zq12289.ofInt_neg, ← Zq12289.ofInt_add, Int.add_left_neg]; rfl
  sub_eq_add_neg a b := by
    rw [← a.ofInt_natVal, ← b.ofInt_natVal, ← Zq12289.ofInt_sub, ← Zq12289.ofInt_neg,
        ← Zq12289.ofInt_add, Int.sub_eq_add_neg]
  mul_assoc a b c := by
    rw [← a.ofInt_natVal, ← b.ofInt_natVal, ← c.ofInt_natVal]
    simp only [← Zq12289.ofInt_mul, Int.mul_assoc]
  mul_comm a b := by
    rw [← a.ofInt_natVal, ← b.ofInt_natVal]
    simp only [← Zq12289.ofInt_mul, Int.mul_comm]
  one_mul a := by
    rw [← a.ofInt_natVal, ← Zq12289.ofInt_one, ← Zq12289.ofInt_mul, Int.one_mul]
  mul_one a := by
    rw [← a.ofInt_natVal, ← Zq12289.ofInt_one, ← Zq12289.ofInt_mul, Int.mul_one]
  left_distrib a b c := by
    rw [← a.ofInt_natVal, ← b.ofInt_natVal, ← c.ofInt_natVal]
    simp only [← Zq12289.ofInt_add, ← Zq12289.ofInt_mul, Int.mul_add]
  right_distrib a b c := by
    rw [← a.ofInt_natVal, ← b.ofInt_natVal, ← c.ofInt_natVal]
    simp only [← Zq12289.ofInt_add, ← Zq12289.ofInt_mul, Int.add_mul]

/-- Repeated squaring in $\mathbb{Z}_{12289}$ for primitive-root verification. -/
def zqPow (base : Zq12289) : Nat → Zq12289
  | 0 => CommRingOps.one
  | k + 1 => CommRingOps.mul base (zqPow base k)

/-- Primitive 2048-th root of unity $\psi_{2048} = 11^6 \bmod 12289 = 1945$ matching `RLWE_PSI_2048`. -/
def rlwePsi2048 : Zq12289 := ⟨1945, by decide⟩

/-- Fast binary exponentiation in $\mathbb{Z}_{12289}$. -/
def zqFastPow (base : Zq12289) (e : Nat) : Zq12289 :=
  let rec loop : Nat → Zq12289 → Nat → Zq12289
    | 0, _, _ => CommRingOps.one
    | fuel + 1, b, exp =>
      if exp == 0 then CommRingOps.one
      else
        let half := loop fuel (CommRingOps.mul b b) (exp / 2)
        if exp % 2 == 1 then CommRingOps.mul b half else half
  loop e base e

/-- $\psi_{2048} = 11^6 \bmod 12289$ satisfies $\psi_{2048}^{1024} \equiv -1 \pmod{12289}$ (splitting $X^{1024} + 1$). -/
theorem rlwePsi2048_is_negacyclic_root :
    zqFastPow ⟨11, by decide⟩ 6 = rlwePsi2048 ∧
    zqFastPow rlwePsi2048 1024 = CommRingOps.neg CommRingOps.one ∧
    zqFastPow rlwePsi2048 2048 = CommRingOps.one := by
  decide

/-! ### 1.1 Constructive Finite Integer Summation & $\mathbb{Z}[X]/(X^N + 1)$ Negacyclic Algebra -/

def natFinSum : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => f ⟨0, Nat.zero_lt_succ n⟩ + natFinSum n (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)

def natDist (a b : Nat) : Nat :=
  if a ≤ b then b - a else a - b

private theorem natFinSum_congr {n : Nat} {f g : Fin n → Nat} (h : ∀ i, f i = g i) :
    natFinSum n f = natFinSum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [natFinSum, h ⟨0, Nat.zero_lt_succ n⟩]
    rw [ih (fun i => h ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)]

private theorem natFinSum_const (n c : Nat) : natFinSum n (fun _ => c) = n * c := by
  induction n with
  | zero => simp [natFinSum]
  | succ n ih =>
    simp only [natFinSum, ih, Nat.succ_mul]
    omega

private theorem natFinSum_add {n : Nat} (f g : Fin n → Nat) :
    natFinSum n (fun i => f i + g i) = natFinSum n f + natFinSum n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [natFinSum, ih]; omega

private theorem natFinSum_le {n : Nat} {f g : Fin n → Nat} (h : ∀ i, f i ≤ g i) :
    natFinSum n f ≤ natFinSum n g := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    simp only [natFinSum]
    have h0 := h ⟨0, Nat.zero_lt_succ n⟩
    have hRest := ih (fun i => h ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
    omega

private theorem natFinSum_mul_right {n : Nat} (f : Fin n → Nat) (c : Nat) :
    natFinSum n (fun i => f i * c) = natFinSum n f * c := by
  induction n with
  | zero => simp [natFinSum]
  | succ n ih => simp only [natFinSum, ih, Nat.add_mul]

def intFinSum : (n : Nat) → (Fin n → Int) → Int
  | 0, _ => 0
  | n + 1, f => f ⟨0, Nat.zero_lt_succ n⟩ + intFinSum n (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)

private theorem intFinSum_congr {n : Nat} {f g : Fin n → Int} (h : ∀ i, f i = g i) :
    intFinSum n f = intFinSum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [intFinSum, h ⟨0, Nat.zero_lt_succ n⟩]
    rw [ih (fun i => h ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)]

private theorem intFinSum_zero (n : Nat) : intFinSum n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [intFinSum, ih]

private theorem intFinSum_add {n : Nat} (f g : Fin n → Int) :
    intFinSum n (fun i => f i + g i) = intFinSum n f + intFinSum n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [intFinSum, ih]; omega

private theorem intFinSum_neg {n : Nat} (f : Fin n → Int) :
    intFinSum n (fun i => -f i) = -intFinSum n f := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [intFinSum, ih]; omega

private theorem intFinSum_mul_left {n : Nat} (c : Int) (f : Fin n → Int) :
    intFinSum n (fun i => c * f i) = c * intFinSum n f := by
  induction n with
  | zero => simp [intFinSum]
  | succ n ih => simp only [intFinSum, ih, Int.mul_add]

private theorem intFinSum_mul_right {n : Nat} (f : Fin n → Int) (c : Int) :
    intFinSum n (fun i => f i * c) = intFinSum n f * c := by
  induction n with
  | zero => simp [intFinSum]
  | succ n ih => simp only [intFinSum, ih, Int.add_mul]

private theorem intFinSum_comm (m n : Nat) (g : Fin m → Fin n → Int) :
    intFinSum m (fun i => intFinSum n (fun j => g i j)) =
    intFinSum n (fun j => intFinSum m (fun i => g i j)) := by
  induction m with
  | zero => symm; exact intFinSum_zero n
  | succ m ih =>
    simp only [intFinSum]
    rw [ih (fun i j => g ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ j), ← intFinSum_add]

private theorem intFinSum_eq_single : ∀ {n : Nat} (i₀ : Fin n) (f : Fin n → Int),
    (∀ i : Fin n, i ≠ i₀ → f i = 0) → intFinSum n f = f i₀
  | 0, i₀, _, _ => Fin.elim0 i₀
  | n + 1, ⟨0, _⟩, f, hZero => by
    simp only [intFinSum]
    have hRest : intFinSum n (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) = intFinSum n (fun _ => 0) := by
      apply intFinSum_congr
      intro i
      apply hZero
      intro heq
      have hv := congrArg Fin.val heq
      dsimp only at hv
      omega
    rw [hRest, intFinSum_zero, Int.add_zero]
  | n + 1, ⟨k + 1, hk⟩, f, hZero => by
    simp only [intFinSum]
    have h0 : f ⟨0, Nat.zero_lt_succ n⟩ = 0 :=
      hZero _ (by intro heq; have hv := congrArg Fin.val heq; dsimp only at hv; omega)
    rw [h0, Int.zero_add]
    exact intFinSum_eq_single ⟨k, Nat.lt_of_succ_lt_succ hk⟩
      (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
      (fun i hi => hZero _ (fun heq => hi (by
        have hv : i.1 + 1 = k + 1 := congrArg Fin.val heq
        exact Fin.ext (Nat.succ.inj hv))))

private def zqFinSum : (m : Nat) → (Fin m → Zq12289) → Zq12289
  | 0, _ => CommRingOps.zero
  | m + 1, g => CommRingOps.add (g ⟨0, Nat.zero_lt_succ m⟩)
      (zqFinSum m (fun i => g ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩))

private theorem zqFinSum_congr {m : Nat} {f g : Fin m → Zq12289} (h : ∀ i, f i = g i) :
    zqFinSum m f = zqFinSum m g := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [zqFinSum, h ⟨0, Nat.zero_lt_succ m⟩]
    rw [ih (fun i => h ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)]

private theorem intFinSum_ofInt_hom {n : Nat} (f : Fin n → Int) :
    Zq12289.ofInt (intFinSum n f) = zqFinSum n (fun i => Zq12289.ofInt (f i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [intFinSum, zqFinSum, Zq12289.ofInt_add]
    rw [ih (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)]

private theorem intFinSum_natAbs_le : ∀ {n : Nat} (f : Fin n → Int),
    (intFinSum n f).natAbs ≤ natFinSum n (fun i => (f i).natAbs)
  | 0, _ => Nat.le_refl 0
  | n + 1, f => by
    simp only [intFinSum, natFinSum]
    have ih := intFinSum_natAbs_le (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
    exact Nat.le_trans (Int.natAbs_add_le _ _) (Nat.add_le_add_left ih _)

/-- Signed integer polynomial of degree $< N$. -/
abbrev PolyInt (N : Nat) := Fin N → Int

/-- Two-way negacyclic convolution kernel for $X^N \equiv -1$. -/
def negacyclicKernel (N k i j : Nat) (prod : Int) : Int :=
  if i + j = k then prod
  else if i + j = N + k then -prod
  else 0

/-- Three-way negacyclic convolution kernel for associativity in $\mathbb{Z}[X]/(X^N + 1)$. -/
private def negacyclicKernel3 (N m s : Nat) (prod : Int) : Int :=
  if s = m then prod
  else if s = N + m then -prod
  else if s = 2 * N + m then prod
  else 0

/-- Exact integer negacyclic multiplication $(a \circledast b) \in \mathbb{Z}[X]/(X^N + 1)$. -/
def polyIntMul {N : Nat} (a b : PolyInt N) : PolyInt N :=
  fun k => intFinSum N (fun i => intFinSum N (fun j => negacyclicKernel N k.val i.val j.val (a i * b j)))

/-- Operational $O(N^2)$ single-sum negacyclic convolution. -/
def polyIntMulSingle {N : Nat} (a b : PolyInt N) : PolyInt N :=
  fun k => intFinSum N (fun i =>
    if h : i.val ≤ k.val then
      a i * b ⟨k.val - i.val, by omega⟩
    else
      -(a i * b ⟨N + k.val - i.val, by omega⟩))

theorem polyIntMul_eq_single {N : Nat} (a b : PolyInt N) :
    polyIntMul a b = polyIntMulSingle a b := by
  funext k
  unfold polyIntMul polyIntMulSingle
  apply intFinSum_congr
  intro i
  by_cases hik : i.val ≤ k.val
  · simp only [hik, ↓reduceDIte]
    let j₀ : Fin N := ⟨k.val - i.val, by omega⟩
    rw [intFinSum_eq_single j₀]
    · unfold negacyclicKernel
      have hij : i.val + j₀.val = k.val := by dsimp [j₀]; omega
      simp only [hij, ↓reduceIte]
      rfl
    · intro j hjNe
      unfold negacyclicKernel
      have h1 : i.val + j.val ≠ k.val := by
        intro heq; apply hjNe; apply Fin.ext; dsimp [j₀]; omega
      have h2 : i.val + j.val ≠ N + k.val := by
        have hjLt := j.isLt; omega
      simp only [h1, h2, ↓reduceIte]
  · simp only [hik, ↓reduceDIte]
    let j₀ : Fin N := ⟨N + k.val - i.val, by omega⟩
    rw [intFinSum_eq_single j₀]
    · unfold negacyclicKernel
      have hiLt := i.isLt
      have h1 : i.val + j₀.val ≠ k.val := by dsimp [j₀]; omega
      have h2 : i.val + j₀.val = N + k.val := by dsimp [j₀]; omega
      have hIf1 : (if i.val + j₀.val = k.val then a i * b j₀
          else if i.val + j₀.val = N + k.val then -(a i * b j₀) else 0) =
          (if i.val + j₀.val = N + k.val then -(a i * b j₀) else 0) := by
        simp only [h1, ↓reduceIte]
      have hIf2 : (if i.val + j₀.val = N + k.val then -(a i * b j₀) else 0) = -(a i * b j₀) := by
        simp only [h2, ↓reduceIte]
      exact hIf1.trans hIf2
    · intro j hjNe
      unfold negacyclicKernel
      have h1 : i.val + j.val ≠ k.val := by omega
      have h2 : i.val + j.val ≠ N + k.val := by
        intro heq; apply hjNe; apply Fin.ext; dsimp [j₀]; omega
      simp only [h1, h2, ↓reduceIte]

theorem polyIntMul_comm {N : Nat} (a b : PolyInt N) :
    polyIntMul a b = polyIntMul b a := by
  funext k
  unfold polyIntMul
  rw [intFinSum_comm]
  apply intFinSum_congr
  intro j
  apply intFinSum_congr
  intro i
  unfold negacyclicKernel
  rw [Nat.add_comm i.val j.val, Int.mul_comm (a i) (b j)]

theorem polyIntMul_left_distrib {N : Nat} (a b c : PolyInt N) :
    polyIntMul a (fun k => b k + c k) = fun k => polyIntMul a b k + polyIntMul a c k := by
  funext k
  unfold polyIntMul
  rw [← intFinSum_add]
  apply intFinSum_congr
  intro i
  rw [← intFinSum_add]
  apply intFinSum_congr
  intro j
  unfold negacyclicKernel
  rw [Int.mul_add]
  split
  · rfl
  · split <;> omega

private theorem negacyclicKernel_compose_left {N : Nat} (hN : 0 < N)
    (m : Fin N) (i j l : Fin N) (P : Int) :
    intFinSum N (fun u => negacyclicKernel N m.val u.val l.val
      (negacyclicKernel N u.val i.val j.val P)) =
    negacyclicKernel3 N m.val (i.val + j.val + l.val) P := by
  have hi := i.isLt; have hj := j.isLt; have hl := l.isLt; have hm := m.isLt
  by_cases hij : i.val + j.val < N
  · let u₀ : Fin N := ⟨i.val + j.val, hij⟩
    rw [intFinSum_eq_single u₀]
    · unfold negacyclicKernel negacyclicKernel3
      dsimp only [u₀]
      have hNot2N : i.val + j.val + l.val ≠ 2 * N + m.val := by omega
      simp only [↓reduceIte, hNot2N]
    · intro u huNe
      unfold negacyclicKernel
      have h1 : i.val + j.val ≠ u.val := fun heq => huNe (Fin.ext heq.symm)
      have h2 : i.val + j.val ≠ N + u.val := by omega
      simp only [h1, h2, ↓reduceIte, Int.neg_zero, ite_self]
  · let u₀ : Fin N := ⟨i.val + j.val - N, by omega⟩
    rw [intFinSum_eq_single u₀]
    · unfold negacyclicKernel negacyclicKernel3
      dsimp only [u₀]
      split
      · omega
      · split
        · split
          · split
            · omega
            · split
              · omega
              · omega
          · split
            · omega
            · split
              · omega
              · split <;> omega
        · omega
    · intro u huNe
      unfold negacyclicKernel
      have hu := u.isLt
      have h1 : i.val + j.val ≠ u.val := by omega
      have h2 : i.val + j.val ≠ N + u.val := by
        intro heq; apply huNe; apply Fin.ext; dsimp [u₀]; omega
      simp only [h1, h2, ↓reduceIte, Int.neg_zero, ite_self]

private theorem negacyclicKernel_mul_right (N k i j : Nat) (P c : Int) :
    negacyclicKernel N k i j P * c = negacyclicKernel N k i j (P * c) := by
  unfold negacyclicKernel
  split
  · rfl
  · split
    · exact Int.neg_mul P c
    · exact Int.zero_mul c

private theorem polyIntMul_triple_eq {N : Nat} (hN : 0 < N) (a b c : PolyInt N) (m : Fin N) :
    polyIntMul (polyIntMul a b) c m =
      intFinSum N (fun i => intFinSum N (fun j => intFinSum N (fun l =>
        negacyclicKernel3 N m.val (i.val + j.val + l.val) ((a i * b j) * c l)))) := by
  unfold polyIntMul
  rw [intFinSum_comm]
  have hStep : ∀ l : Fin N,
      intFinSum N (fun u => negacyclicKernel N m.val u.val l.val
        (intFinSum N (fun i => intFinSum N (fun j => negacyclicKernel N u.val i.val j.val (a i * b j))) * c l)) =
      intFinSum N (fun i => intFinSum N (fun j =>
        negacyclicKernel3 N m.val (i.val + j.val + l.val) ((a i * b j) * c l))) := by
    intro l
    have hPush : ∀ u : Fin N,
        negacyclicKernel N m.val u.val l.val
          (intFinSum N (fun i => intFinSum N (fun j => negacyclicKernel N u.val i.val j.val (a i * b j))) * c l) =
        intFinSum N (fun i => intFinSum N (fun j =>
          negacyclicKernel N m.val u.val l.val
            (negacyclicKernel N u.val i.val j.val ((a i * b j) * c l)))) := by
      intro u
      have hIn : intFinSum N (fun i => intFinSum N (fun j => negacyclicKernel N u.val i.val j.val (a i * b j))) * c l =
          intFinSum N (fun i => intFinSum N (fun j => negacyclicKernel N u.val i.val j.val ((a i * b j) * c l))) := by
        rw [← intFinSum_mul_right]
        apply intFinSum_congr; intro i
        rw [← intFinSum_mul_right]
        apply intFinSum_congr; intro j
        exact negacyclicKernel_mul_right N u.val i.val j.val (a i * b j) (c l)
      rw [hIn]
      unfold negacyclicKernel
      split
      · rfl
      · split
        · rw [← intFinSum_neg]
          apply intFinSum_congr; intro i
          rw [← intFinSum_neg]
        · symm
          have hZ : ∀ _ : Fin N, intFinSum N (fun _ : Fin N => (0 : Int)) = 0 := fun _ => intFinSum_zero N
          rw [intFinSum_congr hZ, intFinSum_zero]
    rw [intFinSum_congr hPush, intFinSum_comm]
    apply intFinSum_congr; intro i
    rw [intFinSum_comm]
    apply intFinSum_congr; intro j
    exact negacyclicKernel_compose_left hN m i j l ((a i * b j) * c l)
  rw [intFinSum_congr hStep, intFinSum_comm]
  apply intFinSum_congr; intro i
  rw [intFinSum_comm]

theorem polyIntMul_assoc {N : Nat} (a b c : PolyInt N) :
    polyIntMul (polyIntMul a b) c = polyIntMul a (polyIntMul b c) := by
  cases N with
  | zero => funext k; exact Fin.elim0 k
  | succ n =>
    have hN : 0 < n + 1 := Nat.zero_lt_succ n
    funext m
    rw [polyIntMul_comm a (polyIntMul b c), polyIntMul_triple_eq hN, polyIntMul_triple_eq hN]
    rw [intFinSum_comm]
    apply intFinSum_congr; intro j
    rw [intFinSum_comm]
    apply intFinSum_congr; intro l
    apply intFinSum_congr; intro i
    have hIdx : i.val + j.val + l.val = j.val + l.val + i.val := by omega
    have hProd : (a i * b j) * c l = (b j * c l) * a i := by
      rw [Int.mul_assoc, Int.mul_comm (a i) (b j * c l)]
    rw [hIdx, hProd]

theorem polyIntMul_one_left {N : Nat} (hN : 0 < N) (a : PolyInt N) :
    polyIntMul (fun k => if k.val = 0 then 1 else 0) a = a := by
  rw [polyIntMul_eq_single]
  funext k
  unfold polyIntMulSingle
  rw [intFinSum_eq_single ⟨0, hN⟩]
  · simp
  · intro i hiNe
    have hi0 : i.val ≠ 0 := fun heq => hiNe (Fin.ext heq)
    split <;> simp [hi0]

/-! ### 1.2 Polynomial Quotient Ring `PolyRq N = Z_12289[X]/(X^N + 1)` & `PolyRq1024` -/

/-- Element of $R_{12289, N} = \mathbb{Z}_{12289}[X]/(X^N + 1)$. -/
abbrev PolyRq (N : Nat) := Fin N → Zq12289

/-- Production negacyclic RLWE ring $R_q = \mathbb{Z}_{12289}[X]/(X^{1024} + 1)$. -/
abbrev PolyRq1024 := PolyRq 1024

/-- Coefficient-wise ring projection $\mathbb{Z}^N \to R_{12289, N}$. -/
@[expose] def polyIntToRq {N : Nat} (p : PolyInt N) : PolyRq N :=
  fun k => Zq12289.ofInt (p k)

/-- Canonical lift $R_{12289, N} \to \mathbb{Z}^N$ in $[0, 12289)$. -/
def polyRqToNatInt {N : Nat} (p : PolyRq N) : PolyInt N :=
  fun k => ((p k).val : Int)

/-- Centered lift $R_{12289, N} \to [-6144, 6144]^N$. -/
def polyRqCentered {N : Nat} (p : PolyRq N) : PolyInt N :=
  fun k => (p k).centered

@[simp] theorem polyIntToRq_toNatInt {N : Nat} (p : PolyRq N) :
    polyIntToRq (polyRqToNatInt p) = p := by
  funext k; exact Zq12289.ofInt_natVal (p k)

@[simp] theorem polyIntToRq_centered {N : Nat} (p : PolyRq N) :
    polyIntToRq (polyRqCentered p) = p := by
  funext k; exact Zq12289.ofInt_centered (p k)

/-- Negacyclic polynomial multiplication in $R_{12289, N}$. -/
def polyRqMul {N : Nat} (a b : PolyRq N) : PolyRq N :=
  polyIntToRq (polyIntMul (polyRqToNatInt a) (polyRqToNatInt b))

instance polyRqCommRingOps (N : Nat) : CommRingOps (PolyRq N) where
  zero := fun _ => CommRingOps.zero
  one := fun k => if k.val = 0 then CommRingOps.one else CommRingOps.zero
  add a b := fun k => CommRingOps.add (a k) (b k)
  mul := polyRqMul
  neg a := fun k => CommRingOps.neg (a k)
  sub a b := fun k => CommRingOps.sub (a k) (b k)

theorem polyIntToRq_add {N : Nat} (a b : PolyInt N) :
    polyIntToRq (fun k => a k + b k) = CommRingOps.add (polyIntToRq a) (polyIntToRq b) := by
  funext k; exact Zq12289.ofInt_add (a k) (b k)

theorem polyIntToRq_neg {N : Nat} (a : PolyInt N) :
    polyIntToRq (fun k => -a k) = CommRingOps.neg (polyIntToRq a) := by
  funext k; exact Zq12289.ofInt_neg (a k)

theorem polyIntToRq_sub {N : Nat} (a b : PolyInt N) :
    polyIntToRq (fun k => a k - b k) = CommRingOps.sub (polyIntToRq a) (polyIntToRq b) := by
  funext k; exact Zq12289.ofInt_sub (a k) (b k)

private theorem ofInt_negacyclicKernel (N k i j : Nat) (x y : Int) :
    Zq12289.ofInt (negacyclicKernel N k i j (x * y)) =
    Zq12289.ofInt (negacyclicKernel N k i j (((Zq12289.ofInt x).val : Int) * ((Zq12289.ofInt y).val : Int))) := by
  unfold negacyclicKernel
  split
  · rw [Zq12289.ofInt_mul, Zq12289.ofInt_mul, Zq12289.ofInt_natVal, Zq12289.ofInt_natVal]
  · split
    · rw [Zq12289.ofInt_neg, Zq12289.ofInt_neg, Zq12289.ofInt_mul, Zq12289.ofInt_mul,
          Zq12289.ofInt_natVal, Zq12289.ofInt_natVal]
    · rfl

/-- **Surjective Negacyclic Ring Homomorphism (`polyIntToRq_mul`)**:
    Integer negacyclic convolution projects homomorphically to `PolyRq N`. -/
theorem polyIntToRq_mul {N : Nat} (a b : PolyInt N) :
    polyIntToRq (polyIntMul a b) = CommRingOps.mul (polyIntToRq a) (polyIntToRq b) := by
  funext k
  change Zq12289.ofInt (polyIntMul a b k) =
    Zq12289.ofInt (polyIntMul (polyRqToNatInt (polyIntToRq a)) (polyRqToNatInt (polyIntToRq b)) k)
  unfold polyIntMul
  rw [intFinSum_ofInt_hom, intFinSum_ofInt_hom]
  apply zqFinSum_congr
  intro i
  rw [intFinSum_ofInt_hom, intFinSum_ofInt_hom]
  apply zqFinSum_congr
  intro j
  exact ofInt_negacyclicKernel N k.val i.val j.val (a i) (b j)

/-- **Exact Negacyclic Quotient Ring Law (`polyRqRing`)**:
    For every $N \ge 1$ (specifically $N = 1024$), $R_{12289, N} = \mathbb{Z}_{12289}[X]/(X^N + 1)$
    is a `LawfulCommRing` with $0$ axioms beyond `{propext, Quot.sound}`. -/
instance polyRqRing (N : Nat) [NeZero N] : LawfulCommRing (PolyRq N) where
  add_assoc a b c := by funext k; exact LawfulCommRing.add_assoc (a k) (b k) (c k)
  add_comm a b := by funext k; exact LawfulCommRing.add_comm (a k) (b k)
  zero_add a := by funext k; exact LawfulCommRing.zero_add (a k)
  add_zero a := by funext k; exact LawfulCommRing.add_zero (a k)
  add_left_neg a := by funext k; exact LawfulCommRing.add_left_neg (a k)
  sub_eq_add_neg a b := by funext k; exact LawfulCommRing.sub_eq_add_neg (a k) (b k)
  mul_assoc a b c := by
    rw [← polyIntToRq_toNatInt a, ← polyIntToRq_toNatInt b, ← polyIntToRq_toNatInt c]
    simp only [← polyIntToRq_mul, polyIntMul_assoc]
  mul_comm a b := by
    rw [← polyIntToRq_toNatInt a, ← polyIntToRq_toNatInt b]
    simp only [← polyIntToRq_mul, polyIntMul_comm]
  one_mul a := by
    have hOne : (CommRingOps.one : PolyRq N) = polyIntToRq (fun k => if k.val = 0 then 1 else 0) := by
      funext k
      change (if k.val = 0 then (CommRingOps.one : Zq12289) else CommRingOps.zero) =
        Zq12289.ofInt (if k.val = 0 then 1 else 0)
      split <;> rfl
    rw [hOne, ← polyIntToRq_toNatInt a, ← polyIntToRq_mul,
        polyIntMul_one_left (Nat.pos_of_ne_zero (NeZero.ne N)), polyIntToRq_toNatInt]
  mul_one a := by
    have hOne : (CommRingOps.one : PolyRq N) = polyIntToRq (fun k => if k.val = 0 then 1 else 0) := by
      funext k
      change (if k.val = 0 then (CommRingOps.one : Zq12289) else CommRingOps.zero) =
        Zq12289.ofInt (if k.val = 0 then 1 else 0)
      split <;> rfl
    rw [hOne, ← polyIntToRq_toNatInt a, ← polyIntToRq_mul, polyIntMul_comm,
        polyIntMul_one_left (Nat.pos_of_ne_zero (NeZero.ne N)), polyIntToRq_toNatInt]
  left_distrib a b c := by
    rw [← polyIntToRq_toNatInt a, ← polyIntToRq_toNatInt b, ← polyIntToRq_toNatInt c]
    rw [← polyIntToRq_add, ← polyIntToRq_mul, polyIntMul_left_distrib, polyIntToRq_add,
        polyIntToRq_mul, polyIntToRq_mul]
  right_distrib a b c := by
    rw [← polyIntToRq_toNatInt a, ← polyIntToRq_toNatInt b, ← polyIntToRq_toNatInt c]
    rw [← polyIntToRq_add, ← polyIntToRq_mul, polyIntMul_comm _ (polyRqToNatInt c),
        polyIntMul_left_distrib, polyIntToRq_add, polyIntMul_comm (polyRqToNatInt c),
        polyIntMul_comm (polyRqToNatInt c), polyIntToRq_mul, polyIntToRq_mul]

/-- Indeterminate $X \in R_{12289, 1024}$ and monomial $X^d$. -/
def polyRq1024Monomial (d : Fin 1024) : PolyRq1024 :=
  fun k => if k = d then CommRingOps.one else CommRingOps.zero

def polyRq1024X : PolyRq1024 := polyRq1024Monomial ⟨1, by decide⟩

def polyRq1024Pow (p : PolyRq1024) : Nat → PolyRq1024
  | 0 => CommRingOps.one
  | d + 1 => CommRingOps.mul p (polyRq1024Pow p d)

private theorem polyRq1024Monomial_eq_ofInt (d : Fin 1024) :
    polyRq1024Monomial d = polyIntToRq (fun k : Fin 1024 => if k.val = d.val then 1 else 0) := by
  funext k
  unfold polyRq1024Monomial polyIntToRq
  split
  · rename_i hkeq; subst hkeq; simp only [↓reduceIte]; rfl
  · rename_i hkne
    have hk : k.val ≠ d.val := fun h => hkne (Fin.ext h)
    simp only [hk, ↓reduceIte]; rfl

private theorem polyRq1024_mul_X_monomial (d : Nat) (hd : d + 1 < 1024) :
    CommRingOps.mul polyRq1024X (polyRq1024Monomial ⟨d, by omega⟩) =
      polyRq1024Monomial ⟨d + 1, hd⟩ := by
  have hM1 : polyRq1024X = polyIntToRq (fun k : Fin 1024 => if k.val = 1 then 1 else 0) :=
    polyRq1024Monomial_eq_ofInt ⟨1, by decide⟩
  have hMd : polyRq1024Monomial ⟨d, by omega⟩ =
      polyIntToRq (fun k : Fin 1024 => if k.val = d then 1 else 0) :=
    polyRq1024Monomial_eq_ofInt ⟨d, by omega⟩
  rw [hM1, hMd, ← polyIntToRq_mul, polyIntMul_eq_single]
  funext k
  unfold polyRq1024Monomial polyIntToRq polyIntMulSingle
  rw [intFinSum_eq_single ⟨1, by decide⟩]
  · simp only [↓reduceIte, Int.one_mul]
    by_cases hle : 1 ≤ k.val
    · simp only [hle, ↓reduceDIte]
      split
      · rename_i hsub
        have hkeq : k = ⟨d + 1, hd⟩ := Fin.ext (by change k.val = d + 1; omega)
        simp only [hkeq, ↓reduceIte]; rfl
      · rename_i hsub
        have hkne : k ≠ ⟨d + 1, hd⟩ := fun heq => hsub (by
          have hv := congrArg Fin.val heq; change k.val = d + 1 at hv; omega)
        simp only [hkne, ↓reduceIte]; rfl
    · simp only [hle, ↓reduceDIte]
      have hk0 : k.val = 0 := by omega
      have hkne : k ≠ ⟨d + 1, hd⟩ := fun heq => by
        have hv := congrArg Fin.val heq; change k.val = d + 1 at hv; omega
      have hsub : 1024 + k.val - 1 ≠ d := by omega
      simp only [hsub, ↓reduceIte, hkne]; rfl
  · intro i hiNe
    have hi1 : i.val ≠ 1 := fun heq => hiNe (Fin.ext heq)
    split <;> simp only [hi1, ↓reduceIte, Int.zero_mul, Int.neg_zero]

private theorem polyRq1024Pow_X_eq_monomial : ∀ (d : Nat) (hd : d < 1024),
    polyRq1024Pow polyRq1024X d = polyRq1024Monomial ⟨d, hd⟩
  | 0, _ => by
    funext k; unfold polyRq1024Pow polyRq1024Monomial
    change (if k.val = 0 then (CommRingOps.one : Zq12289) else CommRingOps.zero) =
      (if k = ⟨0, _⟩ then CommRingOps.one else CommRingOps.zero)
    by_cases hk : k.val = 0
    · have hkeq : k = ⟨0, by decide⟩ := Fin.ext hk
      simp only [hkeq, ↓reduceIte]
    · have hkne : k ≠ ⟨0, by decide⟩ := fun heq => hk (congrArg Fin.val heq)
      simp only [hk, hkne, ↓reduceIte]
  | d + 1, hd => by
    simp only [polyRq1024Pow, polyRq1024Pow_X_eq_monomial d (by omega)]
    exact polyRq1024_mul_X_monomial d hd

/-- **Quotient Defining Identity (`polyRq1024_X_pow_1024_add_one_eq_zero`)**:
    In `PolyRq1024`, $X^{1024} + 1 = 0$ identically! -/
theorem polyRq1024_X_pow_1024_add_one_eq_zero :
    CommRingOps.add (polyRq1024Pow polyRq1024X 1024) CommRingOps.one = CommRingOps.zero := by
  change CommRingOps.add (CommRingOps.mul polyRq1024X (polyRq1024Pow polyRq1024X 1023))
      CommRingOps.one = CommRingOps.zero
  rw [polyRq1024Pow_X_eq_monomial 1023 (by decide)]
  have hM1 : polyRq1024X = polyIntToRq (fun k : Fin 1024 => if k.val = 1 then 1 else 0) :=
    polyRq1024Monomial_eq_ofInt ⟨1, by decide⟩
  have hM1023 : polyRq1024Monomial ⟨1023, by decide⟩ =
      polyIntToRq (fun k : Fin 1024 => if k.val = 1023 then 1 else 0) :=
    polyRq1024Monomial_eq_ofInt ⟨1023, by decide⟩
  rw [hM1, hM1023, ← polyIntToRq_mul, polyIntMul_eq_single]
  funext k
  change CommRingOps.add
      (Zq12289.ofInt (polyIntMulSingle (fun k : Fin 1024 => if k.val = 1 then 1 else 0)
        (fun k : Fin 1024 => if k.val = 1023 then 1 else 0) k))
      (if k.val = 0 then (CommRingOps.one : Zq12289) else CommRingOps.zero) =
    CommRingOps.zero
  unfold polyIntMulSingle
  rw [intFinSum_eq_single ⟨1, by decide⟩]
  · by_cases hk0 : k.val = 0
    · have hkEq : k = ⟨0, by decide⟩ := Fin.ext hk0
      rw [hkEq]; decide
    · have hle : 1 ≤ k.val := by omega
      have hsub : k.val - 1 ≠ 1023 := by have := k.isLt; omega
      simp only [↓reduceIte, hle, ↓reduceDIte, hsub, Int.mul_zero, hk0,
        Zq12289.ofInt_zero, LawfulCommRing.add_zero]
  · intro i hiNe
    have hi1 : i.val ≠ 1 := fun heq => hiNe (Fin.ext heq)
    split <;> simp only [hi1, ↓reduceIte, Int.zero_mul, Int.neg_zero]

/-! ### 1.3 $\ell_1$-$\ell_\infty$ Convolution Bounds, 1-Bit / 2-Bit Rounding & Overflow `#tooth` -/

/-- $\ell_\infty$ norm $\|p\|_\infty = \max_{k < N} |p_k|$ of an integer polynomial. -/
def polyIntInfNorm : {N : Nat} → PolyInt N → Nat
  | 0, _ => 0
  | n + 1, p => max (p ⟨0, Nat.zero_lt_succ n⟩).natAbs
      (polyIntInfNorm (fun i => p ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩))

/-- $\ell_1$ norm $\|p\|_1 = \sum_{k < N} |p_k|$ of an integer polynomial. -/
def polyIntL1Norm {N : Nat} (p : PolyInt N) : Nat :=
  natFinSum N (fun i => (p i).natAbs)

theorem coeff_natAbs_le_infNorm : ∀ {N : Nat} (p : PolyInt N) (k : Fin N),
    (p k).natAbs ≤ polyIntInfNorm p
  | 0, _, k => Fin.elim0 k
  | _ + 1, _, ⟨0, _⟩ => Nat.le_max_left _ _
  | _ + 1, p, ⟨k + 1, hk⟩ =>
    Nat.le_trans (coeff_natAbs_le_infNorm (fun i => p ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
      ⟨k, Nat.lt_of_succ_lt_succ hk⟩) (Nat.le_max_right _ _)

theorem polyIntInfNorm_le_iff : ∀ {N : Nat} (p : PolyInt N) (B : Nat),
    polyIntInfNorm p ≤ B ↔ ∀ k : Fin N, (p k).natAbs ≤ B
  | 0, _, _ => ⟨fun _ k => Fin.elim0 k, fun _ => Nat.zero_le _⟩
  | n + 1, p, B => by
    simp only [polyIntInfNorm, Nat.max_le, polyIntInfNorm_le_iff]
    constructor
    · rintro ⟨h0, hRest⟩ ⟨k, hk⟩
      cases k with
      | zero => exact h0
      | succ k' => exact hRest ⟨k', Nat.lt_of_succ_lt_succ hk⟩
    · intro hAll
      exact ⟨hAll ⟨0, Nat.zero_lt_succ n⟩, fun i => hAll ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩⟩

theorem polyIntL1Norm_le_dim_mul_infNorm {N : Nat} (p : PolyInt N) :
    polyIntL1Norm p ≤ N * polyIntInfNorm p := by
  unfold polyIntL1Norm
  have hLe := natFinSum_le (fun i : Fin N => coeff_natAbs_le_infNorm p i)
  rw [natFinSum_const] at hLe
  exact hLe

/-- **Exact Negacyclic $\ell_1$-$\ell_\infty$ Convolution Bound (`negacyclic_infNorm_mul_add_le`)**:
    For all polynomials $a, s, e \in \mathbb{Z}[X]/(X^N + 1)$,
    $\|a \circledast s + e\|_\infty \le \|a\|_1 \cdot \|s\|_\infty + \|e\|_\infty$. -/
theorem negacyclic_infNorm_mul_add_le {N : Nat} (a s e : PolyInt N) :
    polyIntInfNorm (fun k => polyIntMul a s k + e k) ≤
      polyIntL1Norm a * polyIntInfNorm s + polyIntInfNorm e := by
  rw [polyIntInfNorm_le_iff]
  intro k
  rw [polyIntMul_eq_single]
  unfold polyIntMulSingle
  let convTerm : Fin N → Int := fun i =>
    if h : i.val ≤ k.val then a i * s ⟨k.val - i.val, by omega⟩
    else -(a i * s ⟨N + k.val - i.val, by omega⟩)
  change (intFinSum N convTerm + e k).natAbs ≤ polyIntL1Norm a * polyIntInfNorm s + polyIntInfNorm e
  have hSumAbs := intFinSum_natAbs_le convTerm
  have hTermBound : ∀ i : Fin N, (convTerm i).natAbs ≤ (a i).natAbs * polyIntInfNorm s := by
    intro i
    dsimp only [convTerm]
    by_cases hik : i.val ≤ k.val
    · simp only [hik, ↓reduceDIte, Int.natAbs_mul]
      exact Nat.mul_le_mul_left _ (coeff_natAbs_le_infNorm s _)
    · simp only [hik, ↓reduceDIte, Int.natAbs_neg, Int.natAbs_mul]
      exact Nat.mul_le_mul_left _ (coeff_natAbs_le_infNorm s _)
  have hConvLe : (intFinSum N convTerm).natAbs ≤ polyIntL1Norm a * polyIntInfNorm s := by
    have h2 := natFinSum_le hTermBound
    rw [natFinSum_mul_right] at h2
    exact Nat.le_trans hSumAbs h2
  have hEk := coeff_natAbs_le_infNorm e k
  exact Nat.le_trans (Int.natAbs_add_le _ _) (Nat.add_le_add hConvLe hEk)

/-- 1-bit modular rounding decoder on $\mathbb{Z}_{12289}$ (`0` vs `6144`, margin `< 3072`). -/
@[expose] def decodeBitZq12289 (z : Zq12289) : Bool :=
  decide (3072 ≤ z.val && z.val < 9216)

/-- 1-bit modular encoder (`false ↦ 0`, `true ↦ 6144`). -/
@[expose] def encodeBitZq12289 (b : Bool) : Zq12289 :=
  if b then ⟨6144, by decide⟩ else ⟨0, by decide⟩

/-- 2-bit modular encoder on $\mathbb{Z}_{12289}$ (`{0, 1, 2, 3} ↦ {0, 3072, 6144, 9216}`). -/
def encode2BitZq12289 (sym : Fin 4) : Zq12289 :=
  ⟨sym.val * 3072, by have := sym.isLt; omega⟩

/-- 2-bit modular rounding decoder on $\mathbb{Z}_{12289}$ (margin `< 1536` around `{0, 3072, 6144, 9216}`). -/
def decode2BitZq12289 (z : Zq12289) : Fin 4 :=
  if z.val < 1536 || 10753 ≤ z.val then ⟨0, by decide⟩
  else if z.val < 4608 then ⟨1, by decide⟩
  else if z.val < 7680 then ⟨2, by decide⟩
  else ⟨3, by decide⟩

theorem decodeBitZq12289_noisy_exact (b : Bool) (err : Int) (hErr : err.natAbs < 3072) :
    decodeBitZq12289 (CommRingOps.add (encodeBitZq12289 b) (Zq12289.ofInt err)) = b := by
  unfold decodeBitZq12289 encodeBitZq12289
  cases b <;> simp only [↓reduceIte, Bool.false_eq_true]
  · change decide (3072 ≤ (0 + (Zq12289.ofInt err).val) % 12289 &&
        (0 + (Zq12289.ofInt err).val) % 12289 < 9216) = false
    have hVal := Zq12289.ofInt_val_int err
    have hLt := (Zq12289.ofInt err).isLt
    rw [decide_eq_false_iff_not]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rintro ⟨hGe, hHi⟩; omega
  · change decide (3072 ≤ (6144 + (Zq12289.ofInt err).val) % 12289 &&
        (6144 + (Zq12289.ofInt err).val) % 12289 < 9216) = true
    have hVal := Zq12289.ofInt_val_int err
    have hLt := (Zq12289.ofInt err).isLt
    rw [decide_eq_true_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor <;> omega

private theorem ite_true_of {α : Type} {p : Prop} [inst : Decidable p] (hp : p) (a b : α) :
    (if p then a else b) = a := by
  cases inst with
  | isTrue _ => rfl
  | isFalse hnp => exact False.elim (hnp hp)

private theorem ite_false_of {α : Type} {p : Prop} [inst : Decidable p] (hnp : ¬p) (a b : α) :
    (if p then a else b) = b := by
  cases inst with
  | isTrue hp => exact False.elim (hnp hp)
  | isFalse _ => rfl

/-- **2-Bit Modular Rounding Correctness (`decode2BitZq12289_noisy_exact`)**:
    Any additive noise `|err| < 1536` (including $N = 512$ ternary noise $\le 1025 < 1536$)
    recovers the exact 2-bit symbol in `Fin 4`. -/
theorem decode2BitZq12289_noisy_exact (sym : Fin 4) (err : Int) (hErr : err.natAbs < 1536) :
    decode2BitZq12289 (CommRingOps.add (encode2BitZq12289 sym) (Zq12289.ofInt err)) = sym := by
  rcases sym with ⟨s, hs⟩
  have hVal := Zq12289.ofInt_val_int err
  have hLt := (Zq12289.ofInt err).isLt
  apply Fin.ext
  unfold decode2BitZq12289 encode2BitZq12289
  let v := (s * 3072 + (Zq12289.ofInt err).val) % 12289
  have hvDef : v = (s * 3072 + (Zq12289.ofInt err).val) % 12289 := rfl
  change (if (decide (v < 1536) || decide (10753 ≤ v)) = true then (⟨0, _⟩ : Fin 4)
          else if v < 4608 then ⟨1, _⟩
          else if v < 7680 then ⟨2, _⟩
          else ⟨3, _⟩).val = s
  have hsCases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 := by omega
  rcases hsCases with rfl | rfl | rfl | rfl
  · have hC0 : (decide (v < 1536) || decide (10753 ≤ v)) = true := by
      simp only [Bool.or_eq_true, decide_eq_true_eq]; omega
    rw [ite_true_of hC0]
  · have hC0 : ¬((decide (v < 1536) || decide (10753 ≤ v)) = true) := by
      simp only [Bool.or_eq_true, decide_eq_true_eq]; omega
    have hC1 : v < 4608 := by omega
    rw [ite_false_of hC0, ite_true_of hC1]
  · have hC0 : ¬((decide (v < 1536) || decide (10753 ≤ v)) = true) := by
      simp only [Bool.or_eq_true, decide_eq_true_eq]; omega
    have hC1 : ¬(v < 4608) := by omega
    have hC2 : v < 7680 := by omega
    rw [ite_false_of hC0, ite_false_of hC1, ite_true_of hC2]
  · have hC0 : ¬((decide (v < 1536) || decide (10753 ≤ v)) = true) := by
      simp only [Bool.or_eq_true, decide_eq_true_eq]; omega
    have hC1 : ¬(v < 4608) := by omega
    have hC2 : ¬(v < 7680) := by omega
    rw [ite_false_of hC0, ite_false_of hC1, ite_false_of hC2]

/-- Encode a 512-bit (`64`-byte `seed || rho`) payload into the lower 512 coefficients of `PolyRq1024`. -/
def encodePayload512 (msg : Fin 512 → Bool) : PolyRq1024 :=
  fun k => if h : k.val < 512 then encodeBitZq12289 (msg ⟨k.val, h⟩) else CommRingOps.zero

/-- Decode a 512-bit (`64`-byte `seed || rho`) payload from `PolyRq1024`. -/
def decodePayload512 (noisy : PolyRq1024) : Fin 512 → Bool :=
  fun idx => decodeBitZq12289 (noisy ⟨idx.val, by have := idx.isLt; omega⟩)

/-- **Full Polynomial RLWE Base-OT Zero-Error Decryption (`rlwe1024_poly_ot_decrypt_correct`)**:
    Over $R_q = \mathbb{Z}_{12289}[X]/(X^{1024} + 1)$ with ternary secrets/errors ($\|s_R\|_\infty, \|e_1\|_\infty,
    \|r\|_\infty, \|e_2\|_\infty, \|e_3\|_\infty \le 1$), Receiver's active branch `pk_c = a * s_R + e_1`
    satisfies `‖e_1 ⊛ r - e_2 ⊛ s_R + e_3‖_∞ ≤ 2049 < 3072`, recovering all 512 payload bits exactly! -/
theorem rlwe1024_poly_ot_decrypt_correct
    (a tCrs : PolyRq1024) (choiceBit : Bool)
    (sR e1 r e2 e3 : PolyInt 1024)
    (msg0 msg1 : Fin 512 → Bool)
    (hsR : polyIntInfNorm sR ≤ 1) (he1 : polyIntInfNorm e1 ≤ 1)
    (hr : polyIntInfNorm r ≤ 1) (he2 : polyIntInfNorm e2 ≤ 1) (he3 : polyIntInfNorm e3 ≤ 1) :
    let rlweSample := CommRingOps.add (CommRingOps.mul a (polyIntToRq sR)) (polyIntToRq e1)
    let pk0 := if choiceBit then CommRingOps.sub rlweSample tCrs else rlweSample
    let pk1 := CommRingOps.add pk0 tCrs
    let pk_c := if choiceBit then pk1 else pk0
    let u_c := CommRingOps.add (CommRingOps.mul a (polyIntToRq r)) (polyIntToRq e2)
    let msg_c := if choiceBit then msg1 else msg0
    let v_c := CommRingOps.add
      (CommRingOps.add (CommRingOps.mul pk_c (polyIntToRq r)) (polyIntToRq e3))
      (encodePayload512 msg_c)
    decodePayload512 (CommRingOps.sub v_c (CommRingOps.mul u_c (polyIntToRq sR))) = msg_c := by
  intro rlweSample pk0 pk1 pk_c u_c msg_c v_c
  have hPkEq : pk_c = rlweSample := by
    dsimp only [pk_c, pk1, pk0]
    cases choiceBit
    · rfl
    · simp only [↓reduceIte]
      rw [LawfulCommRing.add_comm, LawfulCommRing.add_sub_cancel_left]
  let errPoly : PolyInt 1024 := fun k =>
    (polyIntMul e1 r k + -(polyIntMul e2 sR k)) + e3 k
  have hDiffAlg :
      CommRingOps.sub v_c (CommRingOps.mul u_c (polyIntToRq sR)) =
        CommRingOps.add (encodePayload512 msg_c) (polyIntToRq errPoly) := by
    dsimp only [v_c, u_c, errPoly]
    rw [hPkEq]
    dsimp only [rlweSample]
    rw [polyIntToRq_add, polyIntToRq_add, polyIntToRq_neg,
        polyIntToRq_mul, polyIntToRq_mul]
    funext k
    change CommRingOps.sub
        (CommRingOps.add
          (CommRingOps.add
            (CommRingOps.mul (CommRingOps.add (CommRingOps.mul a (polyIntToRq sR)) (polyIntToRq e1)) (polyIntToRq r) k)
            (polyIntToRq e3 k))
          (encodePayload512 msg_c k))
        (CommRingOps.mul (CommRingOps.add (CommRingOps.mul a (polyIntToRq r)) (polyIntToRq e2)) (polyIntToRq sR) k) =
      CommRingOps.add (encodePayload512 msg_c k)
        (CommRingOps.add
          (CommRingOps.add (CommRingOps.mul (polyIntToRq e1) (polyIntToRq r) k)
            (CommRingOps.neg (CommRingOps.mul (polyIntToRq e2) (polyIntToRq sR) k)))
          (polyIntToRq e3 k))
    have hMulCancel :
        CommRingOps.mul (CommRingOps.mul a (polyIntToRq sR)) (polyIntToRq r) =
        CommRingOps.mul (CommRingOps.mul a (polyIntToRq r)) (polyIntToRq sR) := by
      rw [LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm (polyIntToRq sR) (polyIntToRq r),
          ← LawfulCommRing.mul_assoc]
    have hL : CommRingOps.mul (CommRingOps.add (CommRingOps.mul a (polyIntToRq sR)) (polyIntToRq e1)) (polyIntToRq r) =
        CommRingOps.add (CommRingOps.mul (CommRingOps.mul a (polyIntToRq r)) (polyIntToRq sR))
          (CommRingOps.mul (polyIntToRq e1) (polyIntToRq r)) := by
      rw [LawfulCommRing.right_distrib, hMulCancel]
    have hR : CommRingOps.mul (CommRingOps.add (CommRingOps.mul a (polyIntToRq r)) (polyIntToRq e2)) (polyIntToRq sR) =
        CommRingOps.add (CommRingOps.mul (CommRingOps.mul a (polyIntToRq r)) (polyIntToRq sR))
          (CommRingOps.mul (polyIntToRq e2) (polyIntToRq sR)) := by
      rw [LawfulCommRing.right_distrib]
    rw [hL, hR]
    let X := CommRingOps.mul (CommRingOps.mul a (polyIntToRq r)) (polyIntToRq sR) k
    let E1R := CommRingOps.mul (polyIntToRq e1) (polyIntToRq r) k
    let E2S := CommRingOps.mul (polyIntToRq e2) (polyIntToRq sR) k
    let E3 := polyIntToRq e3 k
    let M := encodePayload512 msg_c k
    show CommRingOps.sub (CommRingOps.add (CommRingOps.add (CommRingOps.add X E1R) E3) M)
        (CommRingOps.add X E2S) =
      CommRingOps.add M (CommRingOps.add (CommRingOps.add E1R (CommRingOps.neg E2S)) E3)
    rw [← Zq12289.ofInt_natVal X, ← Zq12289.ofInt_natVal E1R, ← Zq12289.ofInt_natVal E2S,
        ← Zq12289.ofInt_natVal E3, ← Zq12289.ofInt_natVal M]
    simp only [← Zq12289.ofInt_add, ← Zq12289.ofInt_sub, ← Zq12289.ofInt_neg]
    congr 1; omega
  have hErrBound : polyIntInfNorm errPoly ≤ 2049 := by
    have hB1 := negacyclic_infNorm_mul_add_le e1 r (fun _ => 0)
    have hZ : polyIntInfNorm (fun _ : Fin 1024 => (0 : Int)) = 0 := by
      rw [← Nat.le_zero_eq, polyIntInfNorm_le_iff]; intro _; decide
    rw [hZ, Nat.add_zero] at hB1
    have hL1_e1 : polyIntL1Norm e1 ≤ 1024 := by
      have := polyIntL1Norm_le_dim_mul_infNorm e1; omega
    have h1024_1 : polyIntInfNorm (polyIntMul e1 r) ≤ 1024 := by
      have hMulLe : polyIntL1Norm e1 * polyIntInfNorm r ≤ 1024 * 1 := Nat.mul_le_mul hL1_e1 hr
      have hSame : (fun k => polyIntMul e1 r k + 0) = polyIntMul e1 r := by funext _; omega
      rw [hSame] at hB1; omega
    have hB2 := negacyclic_infNorm_mul_add_le e2 sR (fun _ => 0)
    rw [hZ, Nat.add_zero] at hB2
    have hL1_e2 : polyIntL1Norm e2 ≤ 1024 := by
      have := polyIntL1Norm_le_dim_mul_infNorm e2; omega
    have h1024_2 : polyIntInfNorm (polyIntMul e2 sR) ≤ 1024 := by
      have hMulLe : polyIntL1Norm e2 * polyIntInfNorm sR ≤ 1024 * 1 := Nat.mul_le_mul hL1_e2 hsR
      have hSame : (fun k => polyIntMul e2 sR k + 0) = polyIntMul e2 sR := by funext _; omega
      rw [hSame] at hB2; omega
    rw [polyIntInfNorm_le_iff]
    intro k
    have hc1 := Nat.le_trans (coeff_natAbs_le_infNorm (polyIntMul e1 r) k) h1024_1
    have hc2 := Nat.le_trans (coeff_natAbs_le_infNorm (polyIntMul e2 sR) k) h1024_2
    have hc3 := Nat.le_trans (coeff_natAbs_le_infNorm e3 k) he3
    dsimp only [errPoly]
    omega
  rw [hDiffAlg]
  funext idx
  unfold decodePayload512
  let k : Fin 1024 := ⟨idx.val, by have := idx.isLt; omega⟩
  change decodeBitZq12289 (CommRingOps.add (encodePayload512 msg_c k) (Zq12289.ofInt (errPoly k))) = msg_c idx
  have hEnc : encodePayload512 msg_c k = encodeBitZq12289 (msg_c idx) := by
    unfold encodePayload512
    have hkLt : k.val < 512 := idx.isLt
    simp only [hkLt, ↓reduceDIte]
    rfl
  rw [hEnc]
  apply decodeBitZq12289_noisy_exact
  have hkBound := Nat.le_trans (coeff_natAbs_le_infNorm errPoly k) hErrBound
  omega

/-- **`#tooth` Overflowing Noise Flips Decoded RLWE OT Bit (`tooth_rlwe1024_overflow_noise_flips_bit`)**:
    When noise exceeds the rounding margin (`|err| = 3072` for 1-bit or `|err| = 1536` for 2-bit, e.g.,
    realized by summing 3072 unit terms or setting $\eta = 2$ on $N = 1024$), both 1-bit and 2-bit
    decoders flip the transmitted OT symbol! -/
private theorem intFinSum_const (n : Nat) (c : Int) :
    intFinSum n (fun _ => c) = (n : Int) * c := by
  induction n with
  | zero => simp [intFinSum]
  | succ n ih =>
    simp only [intFinSum, ih]
    rw [Int.natCast_add, Int.natCast_one, Int.add_mul, Int.one_mul]
    omega

/-- **`#tooth` Overflowing Noise Flips Decoded RLWE OT Bit (`tooth_rlwe1024_overflow_noise_flips_bit`)**:
    When noise exceeds the rounding margin (`|err| = 3072` for 1-bit or `|err| = 1536` for 2-bit, e.g.,
    realized over $R_{12289, 1024}$ by $\eta = 2$ polynomials `e1, r` with `‖e1‖_∞ = 2, ‖r‖_∞ = 2` producing
    degree-0 negacyclic convolution `4096 ∈ [3072, 9216)`), both 1-bit and 2-bit decoders flip the OT symbol! -/
theorem tooth_rlwe1024_overflow_noise_flips_bit :
    (∀ b : Bool, decodeBitZq12289 (CommRingOps.add (encodeBitZq12289 b) (Zq12289.ofInt 3072)) = !b) ∧
    decode2BitZq12289 (CommRingOps.add (encode2BitZq12289 ⟨0, by decide⟩) (Zq12289.ofInt 1536)) =
      ⟨1, by decide⟩ ∧
    (let e1Two : PolyInt 1024 := fun _ => 2
     let rTwo : PolyInt 1024 := fun k => if k.val = 0 then 2 else -2
     let errOver : PolyInt 1024 := polyIntMul e1Two rTwo
     polyIntInfNorm e1Two ≤ 2 ∧
     polyIntInfNorm rTwo ≤ 2 ∧
     errOver ⟨0, by decide⟩ = 4096 ∧
     decodePayload512 (CommRingOps.add (encodePayload512 (fun _ => false)) (polyIntToRq errOver))
       ⟨0, by decide⟩ = true) := by
  refine ⟨?_, by decide, ?_⟩
  · intro b; cases b <;> decide
  · let e1Two : PolyInt 1024 := fun _ => 2
    let rTwo : PolyInt 1024 := fun k => if k.val = 0 then 2 else -2
    let errOver : PolyInt 1024 := polyIntMul e1Two rTwo
    show polyIntInfNorm e1Two ≤ 2 ∧
      polyIntInfNorm rTwo ≤ 2 ∧
      errOver ⟨0, by decide⟩ = 4096 ∧
      decodePayload512 (CommRingOps.add (encodePayload512 (fun _ => false)) (polyIntToRq errOver))
        ⟨0, by decide⟩ = true
    have he1 : polyIntInfNorm e1Two ≤ 2 := by
      rw [polyIntInfNorm_le_iff]; intro _; decide
    have hr : polyIntInfNorm rTwo ≤ 2 := by
      rw [polyIntInfNorm_le_iff]; intro k; dsimp only [rTwo]; split <;> decide
    have hVal0 : errOver ⟨0, by decide⟩ = 4096 := by
      dsimp only [errOver]
      rw [polyIntMul_eq_single]
      unfold polyIntMulSingle
      have hEach : ∀ i : Fin 1024,
          (if h : i.val ≤ (⟨0, by decide⟩ : Fin 1024).val then
            e1Two i * rTwo ⟨0 - i.val, by omega⟩
          else
            -(e1Two i * rTwo ⟨1024 + 0 - i.val, by omega⟩)) = 4 := by
        intro i
        have hiLt := i.isLt
        dsimp only
        split
        · rename_i hi0
          have hz : i.val = 0 := by omega
          simp only [e1Two, rTwo, hz, Nat.sub_zero, ↓reduceIte]; rfl
        · rename_i hi0
          have hnz : 1024 + 0 - i.val ≠ 0 := by omega
          simp only [e1Two, rTwo, hnz, ↓reduceIte]; rfl
      rw [intFinSum_congr hEach, intFinSum_const]
      decide
    refine ⟨he1, hr, hVal0, ?_⟩
    have hCoeff0 : (CommRingOps.add (encodePayload512 (fun _ => false)) (polyIntToRq errOver)) ⟨0, by decide⟩ =
        CommRingOps.add (encodePayload512 (fun _ => false) ⟨0, by decide⟩) (Zq12289.ofInt (errOver ⟨0, by decide⟩)) := rfl
    unfold decodePayload512
    dsimp only
    rw [hCoeff0, hVal0]
    unfold encodePayload512
    decide


/-! ## 2. Joint Fiat-Shamir Signed-Monomial OR-Sigma (`7×20` & `13×20` QROM) + Discrete-Gaussian HVZK + FO Check -/

/-- Decidable universal quantifier over `Fin n` (`0 Classical.choice`). -/
def allFin : (n : Nat) → (Fin n → Bool) → Bool
  | 0, _ => true
  | n + 1, p => p ⟨0, Nat.zero_lt_succ n⟩ && allFin n (fun i => p ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)

theorem allFin_eq_true_iff : ∀ {n : Nat} (p : Fin n → Bool),
    allFin n p = true ↔ ∀ i : Fin n, p i = true
  | 0, _ => ⟨fun _ i => Fin.elim0 i, fun _ => rfl⟩
  | n + 1, p => by
    simp only [allFin, Bool.and_eq_true, allFin_eq_true_iff]
    constructor
    · rintro ⟨h0, hRest⟩ ⟨k, hk⟩
      cases k with
      | zero => exact h0
      | succ k' => exact hRest ⟨k', Nat.lt_of_succ_lt_succ hk⟩
    · intro hAll
      exact ⟨hAll ⟨0, Nat.zero_lt_succ n⟩, fun i => hAll ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩⟩

theorem allFin_eq_false_of_false {n : Nat} {p : Fin n → Bool} (j : Fin n) (hj : p j = false) :
    allFin n p = false := by
  cases hb : allFin n p
  · rfl
  · have hTrue := (allFin_eq_true_iff p).mp hb j
    rw [hj] at hTrue
    cases hTrue

/-- Executable extensional equality on `PolyRq N` (`0 Classical.choice`). -/
def polyRqEq {N : Nat} (a b : PolyRq N) : Bool :=
  allFin N (fun k => decide (a k = b k))

theorem polyRqEq_iff {N : Nat} (a b : PolyRq N) : polyRqEq a b = true ↔ a = b := by
  unfold polyRqEq
  rw [allFin_eq_true_iff]
  constructor
  · intro h; funext k; exact of_decide_eq_true (h k)
  · intro h k; subst h; exact decide_eq_true rfl

@[simp] private theorem polyRqEq_self {N : Nat} (a : PolyRq N) : polyRqEq a a = true :=
  (polyRqEq_iff a a).mpr rfl

theorem polyRqEq_eq_false_iff {N : Nat} (a b : PolyRq N) : polyRqEq a b = false ↔ a ≠ b := by
  constructor
  · intro hFalse hEq
    have ht := (polyRqEq_iff a b).mpr hEq
    rw [hFalse] at ht
    cases ht
  · intro hNe
    cases hb : polyRqEq a b
    · rfl
    · exact False.elim (hNe ((polyRqEq_iff a b).mp hb))

private theorem natFinSum_zero (n : Nat) : natFinSum n (fun _ => 0) = 0 := by
  simpa using natFinSum_const n 0

private theorem natFinSum_eq_single : ∀ {n : Nat} (i₀ : Fin n) (f : Fin n → Nat),
    (∀ i : Fin n, i ≠ i₀ → f i = 0) → natFinSum n f = f i₀
  | 0, i₀, _, _ => Fin.elim0 i₀
  | n + 1, ⟨0, _⟩, f, hZero => by
    simp only [natFinSum]
    have hRest : natFinSum n (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) = natFinSum n (fun _ => 0) := by
      apply natFinSum_congr
      intro i
      apply hZero
      intro heq
      have hv := congrArg Fin.val heq
      dsimp only at hv
      omega
    rw [hRest, natFinSum_zero, Nat.add_zero]
  | n + 1, ⟨k + 1, hk⟩, f, hZero => by
    simp only [natFinSum]
    have h0 : f ⟨0, Nat.zero_lt_succ n⟩ = 0 :=
      hZero _ (by intro heq; have hv := congrArg Fin.val heq; dsimp only at hv; omega)
    rw [h0, Nat.zero_add]
    exact natFinSum_eq_single ⟨k, Nat.lt_of_succ_lt_succ hk⟩
      (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
      (fun i hi => hZero _ (fun heq => hi (by
        have hv : i.1 + 1 = k + 1 := congrArg Fin.val heq
        exact Fin.ext (Nat.succ.inj hv))))

/-- Classical 7-repetition count retained for `#tooth` contrast. -/
def rlweZkpokClassicalReps : Nat := 7

/-- Production 13-repetition (`13 × 11 = 143`-bit classical challenge space) OR-Sigma repetition count
    matching `RLWE_ZKPOK_REPS = 13` in `preprocessing.rs:827`. -/
def rlweZkpokReps : Nat := 13

/-- Alias for the 13-repetition parameter (`rlweZkpokReps = 13`). -/
abbrev rlweZkpokPqReps : Nat := rlweZkpokReps

/-- Post-quantum QROM 24-repetition (`24 × 11 = 264`-bit, `≥ 2^132` Grover) OR-Sigma repetition count. -/
def rlweZkpokPq256Reps : Nat := 24

/-- Production 11-bit signed-monomial challenge bit-width matching `RLWE_ZKPOK_CHAL_BITS = 11` (`preprocessing.rs:830`). -/
def rlweZkpokChalBits : Nat := 11

/-- Half-width `RLWE_ZKPOK_Z_BOUND = 3070` of the verifier's response box (`preprocessing.rs:852`). -/
def rlweZkpokZBound : Nat := 3070

/-- The production constants match `Qsag.RlweCyclotomicExtraction` and `preprocessing.rs`. -/
theorem rlwe_production_constants_agree :
    rlweZkpokZBound = rlweProductionBz ∧ rlweQ = rlweProductionQ ∧ rlweN1024 = rlweCyclotomicN ∧
    rlweZkpokReps = rlweOrSigmaParallelReps ∧ 2 ^ rlweZkpokChalBits = 2 * rlweCyclotomicN :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Exact response box of `RlweReceiverZkPok::verify`: every coefficient lies in the half-open
    interval `-3070 ≤ z_i < 3070` (`(-RLWE_ZKPOK_Z_BOUND..RLWE_ZKPOK_Z_BOUND).contains(&v)`). The box is
    not symmetric: `-3070` is accepted and `3070` is rejected. -/
def polyIntInZkpokBox {N : Nat} (z : PolyInt N) : Bool :=
  allFin N (fun k => decide (-(rlweZkpokZBound : Int) ≤ z k ∧ z k < (rlweZkpokZBound : Int)))

theorem polyIntInZkpokBox_iff {N : Nat} (z : PolyInt N) :
    polyIntInZkpokBox z = true ↔
      ∀ k : Fin N, -(rlweZkpokZBound : Int) ≤ z k ∧ z k < (rlweZkpokZBound : Int) := by
  unfold polyIntInZkpokBox
  rw [allFin_eq_true_iff]
  simp only [decide_eq_true_eq]

/-- In-box responses have `‖z‖_∞ ≤ 3070`; the bound is attained by the accepted value `-3070`. -/
theorem polyIntInZkpokBox_infNorm_le {N : Nat} {z : PolyInt N} (h : polyIntInZkpokBox z = true) :
    polyIntInfNorm z ≤ rlweZkpokZBound := by
  rw [polyIntInfNorm_le_iff]
  intro k
  have hk := (polyIntInZkpokBox_iff z).mp h k
  unfold rlweZkpokZBound at hk ⊢
  omega

/-- **`#tooth`: the response box is half-open.** `-3070` is accepted and has `‖z‖_∞ = 3070`; `3070` is
    rejected. A model with `‖z‖_∞ < 3070` would reject a response the Rust verifier accepts. -/
theorem tooth_zkpok_box_is_half_open :
    polyIntInZkpokBox (fun _ : Fin 1 => (-3070 : Int)) = true ∧
    polyIntInZkpokBox (fun _ : Fin 1 => (3070 : Int)) = false ∧
    polyIntInfNorm (fun _ : Fin 1 => (-3070 : Int)) = rlweZkpokZBound := by
  decide

theorem polyIntInZkpokBox_of_infNorm_lt {N : Nat} {z : PolyInt N}
    (h : polyIntInfNorm z < rlweZkpokZBound) : polyIntInZkpokBox z = true := by
  rw [polyIntInZkpokBox_iff]
  intro k
  have hk := coeff_natAbs_le_infNorm z k
  unfold rlweZkpokZBound at h ⊢
  constructor <;> omega

/-- Production v3 domain-separation string `"QSAG.OT.RLWE.ZKPOK/v3"` for `cSHAKE256` (`preprocessing.rs:1160`). -/
def rlweZkpokDomain : List UInt8 := "QSAG.OT.RLWE.ZKPOK/v3".toUTF8.toList

/-- Legacy v2 domain-separation string retained only for historical `#tooth` contrast. -/
def rlweZkpokDomainLegacyV2 : List UInt8 := "QSAG.OT.RLWE.ZKPOK/v2".toUTF8.toList

/-- Lower-half monomial degree `pos0 ∈ [0, 512)` of a 20-bit challenge (`u & 0x1FF`). -/
def chal20Pos0 (u : BitVec 20) : Fin 1024 :=
  ⟨u.toNat % 512, by omega⟩

/-- Sign bit of the lower-half monomial (`(u >> 9) & 1`). -/
def chal20Sign0 (u : BitVec 20) : Bool :=
  decide ((u.toNat / 512) % 2 = 1)

/-- Upper-half monomial degree `pos1 ∈ [512, 1024)` of a 20-bit challenge (`512 + ((u >> 10) & 0x1FF)`). -/
def chal20Pos1 (u : BitVec 20) : Fin 1024 :=
  ⟨512 + ((u.toNat / 1024) % 512), by omega⟩

/-- Sign bit of the upper-half monomial (`(u >> 19) & 1`). -/
def chal20Sign1 (u : BitVec 20) : Bool :=
  decide ((u.toNat / 524288) % 2 = 1)

/-- Signed unit coefficient `±1` for the lower-half monomial. -/
def chal20Val0 (u : BitVec 20) : Int :=
  if chal20Sign0 u then -1 else 1

/-- Signed unit coefficient `±1` for the upper-half monomial. -/
def chal20Val1 (u : BitVec 20) : Int :=
  if chal20Sign1 u then -1 else 1

theorem chal20Pos0_ne_pos1 (u : BitVec 20) : chal20Pos0 u ≠ chal20Pos1 u := by
  intro hEq
  have hv := congrArg Fin.val hEq
  dsimp only [chal20Pos0, chal20Pos1] at hv
  omega

/-- Exact 20-bit signed-monomial challenge polynomial $d(u) = \pm X^{p_0} \pm X^{512 + p_1} \in \mathbb{Z}[X]/(X^{1024}+1)$
    matching `poly_from_chal20` (`preprocessing.rs:787-800`). -/
def polyIntFromChal20 (u : BitVec 20) : PolyInt 1024 :=
  fun k =>
    if k = chal20Pos0 u then chal20Val0 u
    else if k = chal20Pos1 u then chal20Val1 u
    else 0

/-- Ring-LWE 20-bit signed-monomial challenge polynomial $d(u) \in R_q = \mathbb{Z}_{12289}[X]/(X^{1024}+1)$. -/
def polyRqFromChal20 (u : BitVec 20) : PolyRq1024 :=
  polyIntToRq (polyIntFromChal20 u)

private theorem chal20Val0_natAbs (u : BitVec 20) : (chal20Val0 u).natAbs = 1 := by
  unfold chal20Val0; cases chal20Sign0 u <;> rfl

private theorem chal20Val1_natAbs (u : BitVec 20) : (chal20Val1 u).natAbs = 1 := by
  unfold chal20Val1; cases chal20Sign1 u <;> rfl

/-- Exact $\ell_\infty$ norm $\|d(u)\|_\infty = 1$ for every 20-bit challenge $u$. -/
theorem polyIntFromChal20_infNorm_eq_one (u : BitVec 20) :
    polyIntInfNorm (polyIntFromChal20 u) = 1 := by
  have hLe : polyIntInfNorm (polyIntFromChal20 u) ≤ 1 := by
    rw [polyIntInfNorm_le_iff]
    intro k
    unfold polyIntFromChal20
    split
    · rw [chal20Val0_natAbs]; exact Nat.le_refl 1
    · split
      · rw [chal20Val1_natAbs]; exact Nat.le_refl 1
      · decide
  have hGe : 1 ≤ polyIntInfNorm (polyIntFromChal20 u) := by
    have h0 := coeff_natAbs_le_infNorm (polyIntFromChal20 u) (chal20Pos0 u)
    unfold polyIntFromChal20 at h0
    simp only [↓reduceIte, chal20Val0_natAbs] at h0
    exact h0
  omega

/-- Exact $\ell_1$ norm $\|d(u)\|_1 = 2$ (two disjoint signed monomials) for every 20-bit challenge $u$. -/
theorem polyIntFromChal20_l1Norm_eq_two (u : BitVec 20) :
    polyIntL1Norm (polyIntFromChal20 u) = 2 := by
  unfold polyIntL1Norm
  have hSplit : ∀ k : Fin 1024,
      (polyIntFromChal20 u k).natAbs =
        (if k = chal20Pos0 u then 1 else 0) + (if k = chal20Pos1 u then 1 else 0) := by
    intro k
    if hk0 : k = chal20Pos0 u then
      subst hk0
      have hk1 : chal20Pos0 u ≠ chal20Pos1 u := chal20Pos0_ne_pos1 u
      unfold polyIntFromChal20
      simp only [↓reduceIte, hk1, chal20Val0_natAbs, Nat.add_zero]
    else if hk1 : k = chal20Pos1 u then
      subst hk1
      have hNe : chal20Pos1 u ≠ chal20Pos0 u := (chal20Pos0_ne_pos1 u).symm
      unfold polyIntFromChal20
      simp only [hNe, ↓reduceIte, chal20Val1_natAbs, Nat.zero_add]
    else
      unfold polyIntFromChal20
      simp only [hk0, hk1, ↓reduceIte]; rfl
  rw [natFinSum_congr hSplit, natFinSum_add]
  have h0 : natFinSum 1024 (fun k => if k = chal20Pos0 u then 1 else 0) = 1 := by
    rw [natFinSum_eq_single (chal20Pos0 u)]
    · simp only [↓reduceIte]
    · intro i hi; simp only [hi, ↓reduceIte]
  have h1 : natFinSum 1024 (fun k => if k = chal20Pos1 u then 1 else 0) = 1 := by
    rw [natFinSum_eq_single (chal20Pos1 u)]
    · simp only [↓reduceIte]
    · intro i hi; simp only [hi, ↓reduceIte]
  rw [h0, h1]

private theorem zq_signed_unit_ne_zero (b : Bool) :
    Zq12289.ofInt (if b then -1 else 1) ≠ CommRingOps.zero := by
  cases b <;> decide

private theorem zq_signed_unit_inj {b b' : Bool}
    (h : Zq12289.ofInt (if b then -1 else 1) = Zq12289.ofInt (if b' then -1 else 1)) :
    b = b' := by
  cases b <;> cases b'
  · rfl
  · exfalso; revert h; decide
  · exfalso; revert h; decide
  · rfl

private theorem nat_chal20_radix_decomp (n : Nat) (hn : n < 1048576) :
    n = (n % 512) + 512 * ((n / 512) % 2) + 1024 * ((n / 1024) % 512) +
        524288 * ((n / 524288) % 2) := by
  have h0 : n = 512 * (n / 512) + n % 512 := (Nat.div_add_mod n 512).symm
  have h1 : n / 512 = 2 * ((n / 512) / 2) + (n / 512) % 2 := (Nat.div_add_mod (n / 512) 2).symm
  have hDiv1024 : (n / 512) / 2 = n / 1024 := by
    rw [Nat.div_div_eq_div_mul]
  have h2 : n / 1024 = 512 * ((n / 1024) / 512) + (n / 1024) % 512 :=
    (Nat.div_add_mod (n / 1024) 512).symm
  have hDiv524288 : (n / 1024) / 512 = n / 524288 := by
    rw [Nat.div_div_eq_div_mul]
  have hTopLt : n / 524288 < 2 := by omega
  have hTopMod : (n / 524288) % 2 = n / 524288 := Nat.mod_eq_of_lt hTopLt
  omega

/-- **Injectivity of `polyRqFromChal20` (`polyRqFromChal20_injective`)**:
    Distinct 20-bit challenge words map to distinct signed-monomial polynomials in $R_q$. -/
theorem polyRqFromChal20_injective {u u' : BitVec 20}
    (hEq : polyRqFromChal20 u = polyRqFromChal20 u') : u = u' := by
  have hAt0 := congrFun hEq (chal20Pos0 u)
  unfold polyRqFromChal20 polyIntToRq polyIntFromChal20 at hAt0
  have hPos0NePos1' : chal20Pos0 u ≠ chal20Pos1 u' := by
    intro hc
    have hv := congrArg Fin.val hc
    dsimp only [chal20Pos0, chal20Pos1] at hv
    omega
  simp only [↓reduceIte, hPos0NePos1'] at hAt0
  have hp0 : chal20Pos0 u = chal20Pos0 u' := by
    if h : chal20Pos0 u = chal20Pos0 u' then
      exact h
    else
      simp only [h, ↓reduceIte] at hAt0
      exact False.elim (zq_signed_unit_ne_zero (chal20Sign0 u) hAt0)
  simp only [hp0, ↓reduceIte] at hAt0
  have hs0 : chal20Sign0 u = chal20Sign0 u' := zq_signed_unit_inj hAt0
  have hAt1 := congrFun hEq (chal20Pos1 u)
  unfold polyRqFromChal20 polyIntToRq polyIntFromChal20 at hAt1
  have hPos1NePos0 : chal20Pos1 u ≠ chal20Pos0 u := (chal20Pos0_ne_pos1 u).symm
  have hPos1NePos0' : chal20Pos1 u ≠ chal20Pos0 u' := by
    intro hc
    have hv := congrArg Fin.val hc
    dsimp only [chal20Pos0, chal20Pos1] at hv
    omega
  simp only [hPos1NePos0, hPos1NePos0', ↓reduceIte] at hAt1
  have hp1 : chal20Pos1 u = chal20Pos1 u' := by
    if h : chal20Pos1 u = chal20Pos1 u' then
      exact h
    else
      simp only [h, ↓reduceIte] at hAt1
      exact False.elim (zq_signed_unit_ne_zero (chal20Sign1 u) hAt1)
  simp only [hp1, ↓reduceIte] at hAt1
  have hs1 : chal20Sign1 u = chal20Sign1 u' := zq_signed_unit_inj hAt1
  apply BitVec.eq_of_toNat_eq
  have hv0 : u.toNat % 512 = u'.toNat % 512 := congrArg Fin.val hp0
  have hv1 : 512 + (u.toNat / 1024) % 512 = 512 + (u'.toNat / 1024) % 512 := congrArg Fin.val hp1
  have hb0 : (u.toNat / 512) % 2 = (u'.toNat / 512) % 2 := by
    unfold chal20Sign0 at hs0
    have hL : (u.toNat / 512) % 2 < 2 := Nat.mod_lt _ (by decide)
    have hR : (u'.toNat / 512) % 2 < 2 := Nat.mod_lt _ (by decide)
    by_cases h1 : (u.toNat / 512) % 2 = 1
    · simp only [h1, decide_true, true_eq_decide_iff] at hs0; omega
    · simp only [h1, decide_false, false_eq_decide_iff] at hs0; omega
  have hb1 : (u.toNat / 524288) % 2 = (u'.toNat / 524288) % 2 := by
    unfold chal20Sign1 at hs1
    have hL : (u.toNat / 524288) % 2 < 2 := Nat.mod_lt _ (by decide)
    have hR : (u'.toNat / 524288) % 2 < 2 := Nat.mod_lt _ (by decide)
    by_cases h1 : (u.toNat / 524288) % 2 = 1
    · simp only [h1, decide_true, true_eq_decide_iff] at hs1; omega
    · simp only [h1, decide_false, false_eq_decide_iff] at hs1; omega
  have hdU := nat_chal20_radix_decomp u.toNat u.isLt
  have hdU' := nat_chal20_radix_decomp u'.toNat u'.isLt
  omega

/-- Every 20-bit signed-monomial challenge polynomial is non-zero in $R_q$. -/
theorem polyRqFromChal20_ne_zero (u : BitVec 20) :
    polyRqFromChal20 u ≠ CommRingOps.zero := by
  intro hZero
  have hAt0 := congrFun hZero (chal20Pos0 u)
  unfold polyRqFromChal20 polyIntToRq polyIntFromChal20 at hAt0
  simp only [↓reduceIte] at hAt0
  exact zq_signed_unit_ne_zero (chal20Sign0 u) hAt0

private theorem polyIntInfNorm_sub_le {N : Nat} (p q : PolyInt N) :
    polyIntInfNorm (fun k => p k - q k) ≤ polyIntInfNorm p + polyIntInfNorm q := by
  rw [polyIntInfNorm_le_iff]
  intro k
  have hp := coeff_natAbs_le_infNorm p k
  have hq := coeff_natAbs_le_infNorm q k
  omega

private theorem polyIntL1Norm_sub_le {N : Nat} (p q : PolyInt N) :
    polyIntL1Norm (fun k => p k - q k) ≤ polyIntL1Norm p + polyIntL1Norm q := by
  unfold polyIntL1Norm
  rw [← natFinSum_add]
  apply natFinSum_le
  intro i
  dsimp only
  omega

/-- **Challenge Difference Shortness & Non-Zero Guarantee (`chal20_diff_nonzero_and_short`)**:
    For any $u \ne u' \in \mathrm{BitVec}\, 20$, the difference $\Delta d = d(u) - d(u')$ satisfies
    `polyIntToRq Δd ≠ 0` in `PolyRq1024`, `‖Δd‖_∞ ≤ 2`, and `‖Δd‖_1 ≤ 4`. -/
theorem chal20_diff_nonzero_and_short {u u' : BitVec 20} (hNe : u ≠ u') :
    let deltaD : PolyInt 1024 := fun k => polyIntFromChal20 u k - polyIntFromChal20 u' k
    polyIntToRq deltaD ≠ CommRingOps.zero ∧
    polyIntInfNorm deltaD ≤ 2 ∧
    polyIntL1Norm deltaD ≤ 4 := by
  intro deltaD
  refine ⟨?_, ?_, ?_⟩
  · intro hZero
    rw [polyIntToRq_sub] at hZero
    have hEq : polyRqFromChal20 u = polyRqFromChal20 u' := by
      funext k
      have hk := congrFun hZero k
      change CommRingOps.sub (polyRqFromChal20 u k) (polyRqFromChal20 u' k) = CommRingOps.zero at hk
      have hv := congrArg Zq12289.val hk
      have h1 := (polyRqFromChal20 u k).isLt
      have h2 := (polyRqFromChal20 u' k).isLt
      change ((polyRqFromChal20 u k).val + 12289 - (polyRqFromChal20 u' k).val) % 12289 = 0 at hv
      apply Zq12289.ext
      omega
    exact hNe (polyRqFromChal20_injective hEq)
  · have hInf := polyIntInfNorm_sub_le (polyIntFromChal20 u) (polyIntFromChal20 u')
    rw [polyIntFromChal20_infNorm_eq_one, polyIntFromChal20_infNorm_eq_one] at hInf
    exact hInf
  · have hL1 := polyIntL1Norm_sub_le (polyIntFromChal20 u) (polyIntFromChal20 u')
    rw [polyIntFromChal20_l1Norm_eq_two, polyIntFromChal20_l1Norm_eq_two] at hL1
    exact hL1

/-! ### 2.0a Ring Identification `PolyRq1024 ↔ CycPolyZq 10 12289` & Production v3 11-Bit Signed Monomials (`H1`) -/

private theorem intFinSum_eq_cycIntFinSum : ∀ (n : Nat) (f : Fin n → Int),
    intFinSum n f = cycIntFinSum n f
  | 0, _ => rfl
  | n + 1, f => by
    simp only [intFinSum, cycIntFinSum, intFinSum_eq_cycIntFinSum n]

/-- The two negacyclic convolutions agree. -/
theorem polyIntMul_eq_cycIntMul {N : Nat} (a b : PolyInt N) : polyIntMul a b = cycIntMul a b := by
  funext k
  show intFinSum N (fun i => intFinSum N (fun j => negacyclicKernel N k.val i.val j.val (a i * b j))) =
    cycIntFinSum N (fun i => cycIntFinSum N (fun j =>
      cycNegacyclicKernel N k.val i.val j.val (a i * b j)))
  refine (intFinSum_eq_cycIntFinSum N _).trans ?_
  apply cycIntFinSum_congr; intro i
  refine (intFinSum_eq_cycIntFinSum N _).trans ?_
  apply cycIntFinSum_congr; intro j
  rfl

/-- The two $\ell_\infty$ norms agree. -/
theorem polyIntInfNorm_eq_cycIntInfNorm : ∀ {N : Nat} (p : PolyInt N),
    polyIntInfNorm p = cycIntInfNorm p
  | 0, _ => rfl
  | n + 1, p => by
    simp only [polyIntInfNorm, cycIntInfNorm, polyIntInfNorm_eq_cycIntInfNorm (N := n)]

/-- Coefficient identification $\mathbb{Z}_{12289} \to$ `ModZq 12289`. -/
def zqToModZq (a : Zq12289) : ModZq 12289 := ⟨a.val, a.isLt⟩

/-- Inverse coefficient identification `ModZq 12289` $\to \mathbb{Z}_{12289}$. -/
def modZqToZq (a : ModZq 12289) : Zq12289 := ⟨a.val, a.isLt⟩

theorem zqToModZq_ofInt (z : Int) : zqToModZq (Zq12289.ofInt z) = ModZq.ofInt 12289 z := by
  apply ModZq.ext; rfl

/-- Ring identification `PolyRq1024 → CycPolyZq 10 12289`. -/
def polyRqToCyc (p : PolyRq1024) : CycPolyZq 10 12289 := fun k => zqToModZq (p k)

/-- Inverse ring identification `CycPolyZq 10 12289 → PolyRq1024`. -/
def cycToPolyRq (p : CycPolyZq 10 12289) : PolyRq1024 := fun k => modZqToZq (p k)

theorem polyRqToCyc_cycToPolyRq (p : CycPolyZq 10 12289) : polyRqToCyc (cycToPolyRq p) = p := by
  funext k; apply ModZq.ext; rfl

theorem cycToPolyRq_polyRqToCyc (p : PolyRq1024) : cycToPolyRq (polyRqToCyc p) = p := by
  funext k; apply Zq12289.ext; rfl

theorem polyRqToCyc_injective {p r : PolyRq1024} (h : polyRqToCyc p = polyRqToCyc r) : p = r := by
  funext k
  have hk := congrArg ModZq.val (congrFun h k)
  exact Zq12289.ext hk

theorem polyRqToCyc_polyIntToRq (p : PolyInt 1024) :
    polyRqToCyc (polyIntToRq p) = cycIntToZq 12289 p := by
  funext k; exact zqToModZq_ofInt (p k)

theorem polyRqToCyc_add (a b : PolyRq1024) :
    polyRqToCyc (CommRingOps.add a b) = cycZqAdd (polyRqToCyc a) (polyRqToCyc b) := by
  funext k; apply ModZq.ext; rfl

theorem polyRqToCyc_sub (a b : PolyRq1024) :
    polyRqToCyc (CommRingOps.sub a b) = cycZqSub (polyRqToCyc a) (polyRqToCyc b) := by
  funext k; apply ModZq.ext; rfl

theorem polyRqToCyc_zero : polyRqToCyc (CommRingOps.zero : PolyRq1024) = cycZqZero := by
  funext k; apply ModZq.ext; rfl

theorem polyRqToCyc_one : polyRqToCyc (CommRingOps.one : PolyRq1024) = cycZqOne := by
  funext k
  apply ModZq.ext
  show ((if k.val = 0 then (CommRingOps.one : Zq12289) else CommRingOps.zero) : Zq12289).val =
    ((if k.val = 0 then ModZq.one 12289 else ModZq.zero 12289) : ModZq 12289).val
  by_cases hk : k.val = 0
  · simp only [hk, ↓reduceIte]; rfl
  · simp only [hk, ↓reduceIte]; rfl

theorem polyRqToCyc_mul (a b : PolyRq1024) :
    polyRqToCyc (CommRingOps.mul a b) = cycZqMul (polyRqToCyc a) (polyRqToCyc b) := by
  show polyRqToCyc (polyIntToRq (polyIntMul (polyRqToNatInt a) (polyRqToNatInt b))) =
    cycIntToZq 12289 (cycIntMul (polyRqToNatInt a) (polyRqToNatInt b))
  rw [polyRqToCyc_polyIntToRq, polyIntMul_eq_cycIntMul]

/-- Production v3 11-bit signed-monomial challenge decoding (`deg = u & 0x3FF`, `sign = (u >> 10) & 1`),
    matching `poly_from_chal11` in `preprocessing.rs:870-879`. -/
def chal11ToSignedMonomial (u : BitVec 11) : SignedMonomialChal 10 :=
  SignedMonomialChal.ofBitVec u

/-- Production v3 11-bit signed-monomial integer polynomial $d(u) = (-1)^{\mathrm{sign}} X^{\mathrm{deg}} \in \mathbb{Z}[X]/(X^{1024}+1)$. -/
def polyIntFromChal11 (u : BitVec 11) : PolyInt 1024 :=
  (chal11ToSignedMonomial u).toIntPoly

/-- Production v3 11-bit signed-monomial challenge polynomial $d(u) = \pm X^{\mathrm{deg}} \in R_{12289}$
    matching `poly_from_chal11` (`preprocessing.rs:870-879`). -/
def polyRqFromChal11 (u : BitVec 11) : PolyRq1024 :=
  polyIntToRq (polyIntFromChal11 u)

/-- Exact bit-level specification matching `poly_from_chal11`: `deg = u.toNat % 1024`, `sign = ((u >> 10) & 1 == 1)`. -/
theorem polyIntFromChal11_spec (u : BitVec 11) :
    (chal11ToSignedMonomial u).deg.val = u.toNat % 1024 ∧
    (chal11ToSignedMonomial u).sign = decide (1024 ≤ u.toNat) :=
  SignedMonomialChal.ofBitVec_11_spec u

/-- Exact $\ell_\infty$ norm $\|d(u)\|_\infty = 1$ for every 11-bit challenge $u$. -/
theorem polyIntFromChal11_infNorm_eq_one (u : BitVec 11) :
    polyIntInfNorm (polyIntFromChal11 u) = 1 := by
  have hLe : polyIntInfNorm (polyIntFromChal11 u) ≤ 1 := by
    rw [polyIntInfNorm_le_iff]; intro k
    unfold polyIntFromChal11 SignedMonomialChal.toIntPoly signedMonomial negacyclicSignedMonomial signBitToInt
    split
    · cases (chal11ToSignedMonomial u).sign <;> decide
    · decide
  have hGe : 1 ≤ polyIntInfNorm (polyIntFromChal11 u) := by
    have hk := coeff_natAbs_le_infNorm (polyIntFromChal11 u) (chal11ToSignedMonomial u).deg
    unfold polyIntFromChal11 SignedMonomialChal.toIntPoly signedMonomial negacyclicSignedMonomial signBitToInt at hk
    simp only [↓reduceIte] at hk
    have hAbs : (if (chal11ToSignedMonomial u).sign = true then (-1 : Int) else 1).natAbs = 1 := by
      cases (chal11ToSignedMonomial u).sign <;> decide
    rw [hAbs] at hk
    exact hk
  omega

/-- Exact $\ell_1$ norm $\|d(u)\|_1 = 1$ (single signed monomial) for every 11-bit challenge $u$. -/
theorem polyIntFromChal11_l1Norm_eq_one (u : BitVec 11) :
    polyIntL1Norm (polyIntFromChal11 u) = 1 := by
  unfold polyIntL1Norm polyIntFromChal11 SignedMonomialChal.toIntPoly signedMonomial negacyclicSignedMonomial
  rw [natFinSum_eq_single (chal11ToSignedMonomial u).deg]
  · unfold signBitToInt; cases (chal11ToSignedMonomial u).sign <;> simp
  · intro i hiNe; simp only [hiNe, ↓reduceIte]; rfl

/-- **Signed-Monomial $\ell_\infty$ Isometry (`polyIntInfNorm_mul_chal11_eq`, `H2`)**:
    Multiplying any polynomial $p \in \mathbb{Z}[X]/(X^{1024}+1)$ by a production 11-bit signed monomial
    $d(u) = \pm X^k$ preserves $\|p\|_\infty$ identically! -/
theorem polyIntInfNorm_mul_chal11_eq (u : BitVec 11) (p : PolyInt 1024) :
    polyIntInfNorm (polyIntMul (polyIntFromChal11 u) p) = polyIntInfNorm p := by
  rw [polyIntInfNorm_eq_cycIntInfNorm, polyIntMul_eq_cycIntMul]
  exact (cycIntInfNorm_mul_signedMonomial_eq (chal11ToSignedMonomial u) p).trans
    (polyIntInfNorm_eq_cycIntInfNorm p).symm

/-- **Universal Pairwise Difference Invertibility & Shortness (`chal11_diff_nonzero_short_and_invertible`, `H1`/`H2`)**:
    For **every** distinct pair $u \ne u' \in \mathrm{BitVec}\, 11$:
    1. $\Delta d = d(u) - d(u')$ is non-zero in `PolyRq1024`,
    2. $\|\Delta d\|_\infty \le 2$ and $\|\Delta d\|_1 \le 2$, and
    3. $d(u) - d(u') \in R_{12289}^\times$ has an **explicit multiplicative inverse** in `PolyRq1024`
       (100% of distinct 11-bit challenge pairs are invertible, eliminating the two-monomial zero divisors of v2!). -/
theorem chal11_diff_nonzero_short_and_invertible {u u' : BitVec 11} (hNe : u ≠ u') :
    let deltaD : PolyInt 1024 := fun k => polyIntFromChal11 u k - polyIntFromChal11 u' k
    polyIntToRq deltaD ≠ CommRingOps.zero ∧
    polyIntInfNorm deltaD ≤ 2 ∧
    polyIntL1Norm deltaD ≤ 2 ∧
    ∃ inv : PolyRq1024,
      CommRingOps.mul (CommRingOps.sub (polyRqFromChal11 u) (polyRqFromChal11 u')) inv =
        CommRingOps.one := by
  intro deltaD
  have hMonoNe : chal11ToSignedMonomial u ≠ chal11ToSignedMonomial u' :=
    fun hm => hNe (SignedMonomialChal.ofBitVec_injective hm)
  have hInvCyc :=
    (signedMonomial_1024_challenge_set_2048_pairwise_invertible 12289 (by decide) (by decide)
      (chal11ToSignedMonomial u) (chal11ToSignedMonomial u') hMonoNe)
  have hInvRq : CommRingOps.mul (CommRingOps.sub (polyRqFromChal11 u) (polyRqFromChal11 u'))
      (cycToPolyRq (signedMonomialDiffInvZq 10 12289 (chal11ToSignedMonomial u) (chal11ToSignedMonomial u'))) =
      CommRingOps.one := by
    apply polyRqToCyc_injective
    unfold polyRqFromChal11 polyIntFromChal11
    rw [polyRqToCyc_mul, polyRqToCyc_sub, polyRqToCyc_one, polyRqToCyc_cycToPolyRq,
        polyRqToCyc_polyIntToRq, polyRqToCyc_polyIntToRq]
    exact hInvCyc.2.2.1
  refine ⟨?_, ?_, ?_, ⟨_, hInvRq⟩⟩
  · intro hZero
    have hEq : polyRqFromChal11 u = polyRqFromChal11 u' := by
      funext k
      have hk := congrFun hZero k
      rw [polyIntToRq_sub] at hk
      have hv := congrArg Zq12289.val hk
      have h1 := (polyRqFromChal11 u k).isLt
      have h2 := (polyRqFromChal11 u' k).isLt
      apply Zq12289.ext
      change ((polyRqFromChal11 u k).val + 12289 - (polyRqFromChal11 u' k).val) % 12289 = 0 at hv
      omega
    apply hMonoNe
    apply signedMonomial_toZq_injective (q := 12289) (by decide)
    have h := congrArg polyRqToCyc hEq
    simpa only [polyRqFromChal11, polyRqToCyc_polyIntToRq, polyIntFromChal11,
      chal11ToSignedMonomial, SignedMonomialChal.toZqPoly] using h
  · have hInf := polyIntInfNorm_sub_le (polyIntFromChal11 u) (polyIntFromChal11 u')
    rw [polyIntFromChal11_infNorm_eq_one, polyIntFromChal11_infNorm_eq_one] at hInf
    exact hInf
  · have hL1 := polyIntL1Norm_sub_le (polyIntFromChal11 u) (polyIntFromChal11 u')
    rw [polyIntFromChal11_l1Norm_eq_one, polyIntFromChal11_l1Norm_eq_one] at hL1
    exact hL1

/-- **Injectivity of `polyRqFromChal11` (`polyRqFromChal11_injective`)**:
    Distinct 11-bit challenge words map to distinct signed-monomial polynomials in $R_{12289}$. -/
theorem polyRqFromChal11_injective {u u' : BitVec 11}
    (hEq : polyRqFromChal11 u = polyRqFromChal11 u') : u = u' := by
  apply SignedMonomialChal.ofBitVec_injective (nu := 10)
  apply signedMonomial_toZq_injective (q := 12289) (by decide)
  have h := congrArg polyRqToCyc hEq
  simpa only [polyRqFromChal11, polyRqToCyc_polyIntToRq, polyIntFromChal11,
      chal11ToSignedMonomial, SignedMonomialChal.toZqPoly] using h

/-- Every 11-bit signed-monomial challenge polynomial is non-zero in $R_{12289}$. -/
theorem polyRqFromChal11_ne_zero (u : BitVec 11) :
    polyRqFromChal11 u ≠ CommRingOps.zero := by
  intro hZero
  have hAt := congrFun hZero (chal11ToSignedMonomial u).deg
  unfold polyRqFromChal11 polyIntToRq polyIntFromChal11 SignedMonomialChal.toIntPoly
    signedMonomial negacyclicSignedMonomial signBitToInt at hAt
  simp only [↓reduceIte] at hAt
  exact zq_signed_unit_ne_zero (chal11ToSignedMonomial u).sign hAt

/-! ### 2.1 Fiat-Shamir `cSHAKE256("QSAG.OT.RLWE.ZKPOK/v3")` Transcript Binding & OR-Sigma Verifier -/

/-- Canonical little-endian `u16` coefficient serializer (`2 * N` bytes) matching `c.to_le_bytes()`
    in `hash_rlwe_zkpok_joint_challenges` (`preprocessing.rs:999`). -/
def encodePolyRqLe : {N : Nat} → PolyRq N → List UInt8
  | 0, _ => []
  | n + 1, p =>
    encodeNatLeBytes 2 (p ⟨0, Nat.zero_lt_succ n⟩).val ++
    encodePolyRqLe (fun i => p ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)

theorem encodePolyRqLe_length : ∀ {N : Nat} (p : PolyRq N), (encodePolyRqLe p).length = 2 * N
  | 0, _ => rfl
  | n + 1, p => by
    simp only [encodePolyRqLe, List.length_append, encodeNatLeBytes_length,
      encodePolyRqLe_length (fun i => p ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)]
    omega

theorem encodePolyRqLe_injective : ∀ {N : Nat} {p q : PolyRq N},
    encodePolyRqLe p = encodePolyRqLe q → p = q
  | 0, p, q, _ => funext fun i => Fin.elim0 i
  | n + 1, p, q, hEq => by
    simp only [encodePolyRqLe] at hEq
    obtain ⟨hHead, hTail⟩ := List.append_inj hEq (by simp [encodeNatLeBytes_length])
    have hp0Lt : (p ⟨0, Nat.zero_lt_succ n⟩).val < 256 ^ 2 := by
      have := (p ⟨0, Nat.zero_lt_succ n⟩).isLt; omega
    have hq0Lt : (q ⟨0, Nat.zero_lt_succ n⟩).val < 256 ^ 2 := by
      have := (q ⟨0, Nat.zero_lt_succ n⟩).isLt; omega
    have hDec := congrArg decodeNatLeBytes hHead
    rw [decodeNatLeBytes_encodeNatLeBytes 2 _ hp0Lt,
        decodeNatLeBytes_encodeNatLeBytes 2 _ hq0Lt] at hDec
    have h0Eq : p ⟨0, Nat.zero_lt_succ n⟩ = q ⟨0, Nat.zero_lt_succ n⟩ := Zq12289.ext hDec
    have hRestEq := encodePolyRqLe_injective hTail
    funext ⟨k, hk⟩
    cases k with
    | zero => exact h0Eq
    | succ k' => exact congrFun hRestEq ⟨k', Nat.lt_of_succ_lt_succ hk⟩

/-- Little-endian serializer for an `R`-tuple of commitment pairs `(w0, w1)` (`4096 * R` bytes). -/
def encodeJointOrCommsLe : {R : Nat} → (Fin R → (PolyRq1024 × PolyRq1024)) → List UInt8
  | 0, _ => []
  | r + 1, comms =>
    let c0 := comms ⟨0, Nat.zero_lt_succ r⟩
    encodePolyRqLe c0.1 ++ encodePolyRqLe c0.2 ++
    encodeJointOrCommsLe (fun i => comms ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)

theorem encodeJointOrCommsLe_injective : ∀ {R : Nat} {c1 c2 : Fin R → (PolyRq1024 × PolyRq1024)},
    encodeJointOrCommsLe c1 = encodeJointOrCommsLe c2 → c1 = c2
  | 0, c1, c2, _ => funext fun i => Fin.elim0 i
  | r + 1, c1, c2, hEq => by
    simp only [encodeJointOrCommsLe, List.append_assoc] at hEq
    obtain ⟨hA, hRest1⟩ := List.append_inj hEq (by simp [encodePolyRqLe_length])
    obtain ⟨hB, hTail⟩ := List.append_inj hRest1 (by simp [encodePolyRqLe_length])
    have hHead : c1 ⟨0, Nat.zero_lt_succ r⟩ = c2 ⟨0, Nat.zero_lt_succ r⟩ :=
      Prod.ext (encodePolyRqLe_injective hA) (encodePolyRqLe_injective hB)
    have hTailEq := encodeJointOrCommsLe_injective hTail
    funext ⟨k, hk⟩
    cases k with
    | zero => exact hHead
    | succ k' => exact congrFun hTailEq ⟨k', Nat.lt_of_succ_lt_succ hk⟩

/-- Exact Fiat-Shamir byte preimage absorbed into `cSHAKE256("QSAG.OT.RLWE.ZKPOK/v3")` in
    `hash_rlwe_zkpok_joint_challenges` (`preprocessing.rs:1160-1171`), including explicit 4-byte
    big-endian challenge-bit-width framing `be 4 rlweZkpokChalBits` (`11`). -/
def encodeRlweZkpokFsInput (R : Nat)
    (crsCoin sessionId : List UInt8)
    (senderId receiverId otIdx : Nat)
    (pk0 tCrs : PolyRq1024)
    (comms : Fin R → (PolyRq1024 × PolyRq1024)) : List UInt8 :=
  crsCoin ++
  sessionId ++
  be 8 senderId ++
  be 8 receiverId ++
  be 4 otIdx ++
  be 4 R ++
  be 4 rlweZkpokChalBits ++
  encodePolyRqLe pk0 ++
  encodePolyRqLe tCrs ++
  encodeJointOrCommsLe comms

/-- **Fiat-Shamir Tuple Framing Injectivity (`encodeRlweZkpokFsInput_injective`, `H1`)**:
    On fixed-width context fields (`|crsCoin| = |sessionId| = 32`, `senderId, receiverId < 2^64`,
    `otIdx < 2^32`), `encodeRlweZkpokFsInput` is injective in all 8 absorbed statement and
    commitment components `(crsCoin, sessionId, senderId, receiverId, otIdx, pk0, tCrs, comms)`. -/
theorem encodeRlweZkpokFsInput_injective {R : Nat}
    {c1 c2 s1 s2 : List UInt8}
    {snd1 snd2 rcv1 rcv2 ot1 ot2 : Nat}
    {pk1 pk2 t1 t2 : PolyRq1024}
    {comms1 comms2 : Fin R → (PolyRq1024 × PolyRq1024)}
    (hc1 : c1.length = 32) (hc2 : c2.length = 32)
    (hs1 : s1.length = 32) (hs2 : s2.length = 32)
    (hsnd1 : snd1 < 2 ^ 64) (hsnd2 : snd2 < 2 ^ 64)
    (hrcv1 : rcv1 < 2 ^ 64) (hrcv2 : rcv2 < 2 ^ 64)
    (hot1 : ot1 < 2 ^ 32) (hot2 : ot2 < 2 ^ 32)
    (hEq : encodeRlweZkpokFsInput R c1 s1 snd1 rcv1 ot1 pk1 t1 comms1 =
           encodeRlweZkpokFsInput R c2 s2 snd2 rcv2 ot2 pk2 t2 comms2) :
    c1 = c2 ∧ s1 = s2 ∧ snd1 = snd2 ∧ rcv1 = rcv2 ∧ ot1 = ot2 ∧
    pk1 = pk2 ∧ t1 = t2 ∧ comms1 = comms2 := by
  simp only [encodeRlweZkpokFsInput, List.append_assoc] at hEq
  obtain ⟨hC, h1⟩ := List.append_inj hEq (by omega)
  obtain ⟨hS, h2⟩ := List.append_inj h1 (by omega)
  obtain ⟨hSnd, h3⟩ := List.append_inj h2 (by simp [length_be])
  obtain ⟨hRcv, h4⟩ := List.append_inj h3 (by simp [length_be])
  obtain ⟨hOt, h5⟩ := List.append_inj h4 (by simp [length_be])
  obtain ⟨_, h6⟩ := List.append_inj h5 (by simp [length_be])
  obtain ⟨_, h7⟩ := List.append_inj h6 (by simp [length_be])
  obtain ⟨hPk, h8⟩ := List.append_inj h7 (by simp [encodePolyRqLe_length])
  obtain ⟨hT, hComms⟩ := List.append_inj h8 (by simp [encodePolyRqLe_length])
  exact ⟨hC, hS,
    be_injective (by omega : snd1 < 256 ^ 8) (by omega : snd2 < 256 ^ 8) hSnd,
    be_injective (by omega : rcv1 < 256 ^ 8) (by omega : rcv2 < 256 ^ 8) hRcv,
    be_injective (by omega : ot1 < 256 ^ 4) (by omega : ot2 < 256 ^ 4) hOt,
    encodePolyRqLe_injective hPk,
    encodePolyRqLe_injective hT,
    encodeJointOrCommsLe_injective hComms⟩

/-- Squeeze `R` consecutive 11-bit signed-monomial challenges (`u32::from_le_bytes(out) & 0x7FF`,
    `preprocessing.rs:1172-1176`) from a squeezed XOF byte stream. -/
def decodeChal11Stream : (R : Nat) → List UInt8 → (Fin R → BitVec 11)
  | 0, _, i => Fin.elim0 i
  | _ + 1, bs, ⟨0, _⟩ =>
    BitVec.ofNat 11 (decodeNatLeBytes (bs.take 4) % (2 ^ 11))
  | r + 1, bs, ⟨k + 1, hk⟩ =>
    decodeChal11Stream r (bs.drop 4) ⟨k, Nat.lt_of_succ_lt_succ hk⟩

/-- Parametric `R`-repetition Fiat-Shamir 11-bit signed-monomial challenge derivation parameterized
    by XOF oracle `ro` (used for Forking-Lemma rewinding in `jointOrSigma_extract_witness`). -/
def hashRlweZkpokJointChallengesWithRo (R : Nat) (ro : List UInt8 → List UInt8)
    (crsCoin sessionId : List UInt8)
    (senderId receiverId otIdx : Nat)
    (pk0 tCrs : PolyRq1024)
    (comms : Fin R → (PolyRq1024 × PolyRq1024)) : Fin R → BitVec 11 :=
  decodeChal11Stream R
    (ro (encodeRlweZkpokFsInput R crsCoin sessionId senderId receiverId otIdx pk0 tCrs comms))

/-- Production `cSHAKE256("QSAG.OT.RLWE.ZKPOK/v3")` Fiat-Shamir challenge derivation (`preprocessing.rs:1155-1177`). -/
def hashRlweZkpokJointChallengesGen (R : Nat)
    (crsCoin sessionId : List UInt8)
    (senderId receiverId otIdx : Nat)
    (pk0 tCrs : PolyRq1024)
    (comms : Fin R → (PolyRq1024 × PolyRq1024)) : Fin R → BitVec 11 :=
  hashRlweZkpokJointChallengesWithRo R (cshake256Xof (4 * R) rlweZkpokDomain)
    crsCoin sessionId senderId receiverId otIdx pk0 tCrs comms

/-- Production 13-repetition (`13 × 11 = 143`-bit classical / `2^71.5` Grover) Fiat-Shamir challenge derivation. -/
abbrev hashRlweZkpokJointChallenges := hashRlweZkpokJointChallengesGen rlweZkpokReps

/-- Alias for 13-repetition (`143`-bit classical) Fiat-Shamir challenge derivation. -/
abbrev hashRlweZkpokJointChallengesPq13 := hashRlweZkpokJointChallengesGen rlweZkpokPqReps

/-- 24-repetition (`24 × 11 = 264`-bit QROM / `2^132 ≥ 2^128` Grover) Fiat-Shamir challenge derivation. -/
abbrev hashRlweZkpokJointChallengesPq24 := hashRlweZkpokJointChallengesGen rlweZkpokPq256Reps

/-- Public statement for 1-out-of-2 Ring-LWE Base-OT OR-Sigma proof of short witness knowledge,
    binding CRS/session coins, directed `(senderId, receiverId, otIdx)` context, CRS `(a, tCrs)`,
    and Receiver first-message key `pk0` (`preprocessing.rs:1324-1334`). -/
structure RlweOrStatement where
  crsCoin : List UInt8
  sessionId : List UInt8
  senderId : Nat
  receiverId : Nat
  otIdx : Nat
  a : PolyRq1024
  tCrs : PolyRq1024
  pk0 : PolyRq1024

/-- Branch target $Y_0 = \mathsf{pk}_0$, $Y_1 = \mathsf{pk}_0 + t_{\mathsf{crs}}$. -/
def RlweOrStatement.branchPk (stmt : RlweOrStatement) (b : Bool) : PolyRq1024 :=
  if b then CommRingOps.add stmt.pk0 stmt.tCrs else stmt.pk0

/-- Statement framing & non-degenerate CRS check (`|crsCoin| = |sessionId| = 32`, distinct bounded party IDs,
    `a ≠ 0`, `tCrs ≠ 0`). -/
def checkRlweOrStatementValid (stmt : RlweOrStatement) : Bool :=
  decide (stmt.crsCoin.length = 32) &&
  decide (stmt.sessionId.length = 32) &&
  decide (stmt.senderId < 2 ^ 64) &&
  decide (stmt.receiverId < 2 ^ 64) &&
  decide (stmt.senderId ≠ stmt.receiverId) &&
  decide (stmt.otIdx < 2 ^ 32) &&
  !polyRqEq stmt.a CommRingOps.zero &&
  !polyRqEq stmt.tCrs CommRingOps.zero

/-- Parametric `R`-repetition OR-Sigma transcript over `PolyRq1024` with 11-bit single signed-monomial
    challenges `chal0, chal1 : Fin R → BitVec 11` matching `RlweReceiverZkPok` (`preprocessing.rs:841-848`). -/
structure JointOrSigmaTranscriptGen (R : Nat) where
  comms : Fin R → (PolyRq1024 × PolyRq1024)
  chal0 : Fin R → BitVec 11
  chal1 : Fin R → BitVec 11
  zs0 : Fin R → PolyInt 1024
  ze0 : Fin R → PolyInt 1024
  zs1 : Fin R → PolyInt 1024
  ze1 : Fin R → PolyInt 1024

/-- Production 13-repetition (`143`-bit classical) OR-Sigma transcript. -/
abbrev JointOrSigmaTranscript := JointOrSigmaTranscriptGen rlweZkpokReps

/-- Alias for 13-repetition (`143`-bit classical) OR-Sigma transcript. -/
abbrev JointOrSigmaTranscriptPq13 := JointOrSigmaTranscriptGen rlweZkpokPqReps

/-- 24-repetition (`264`-bit QROM / `≥ 2^132` Grover) OR-Sigma transcript. -/
abbrev JointOrSigmaTranscriptPq24 := JointOrSigmaTranscriptGen rlweZkpokPq256Reps

/-- Recompute commitments `(w0, w1)` from responses and 11-bit signed-monomial challenges (`preprocessing.rs:1359-1367`):
    `w0 = a * zs0 + ze0 - d(chal0) * pk0`, `w1 = a * zs1 + ze1 - d(chal1) * (pk0 + tCrs)`. -/
def recomputeJointOrRepComm {R : Nat} (stmt : RlweOrStatement)
    (tr : JointOrSigmaTranscriptGen R) (j : Fin R) : PolyRq1024 × PolyRq1024 :=
  let y0 := stmt.pk0
  let y1 := CommRingOps.add stmt.pk0 stmt.tCrs
  let w0 := CommRingOps.sub
    (CommRingOps.add (CommRingOps.mul stmt.a (polyIntToRq (tr.zs0 j))) (polyIntToRq (tr.ze0 j)))
    (CommRingOps.mul (polyRqFromChal11 (tr.chal0 j)) y0)
  let w1 := CommRingOps.sub
    (CommRingOps.add (CommRingOps.mul stmt.a (polyIntToRq (tr.zs1 j))) (polyIntToRq (tr.ze1 j)))
    (CommRingOps.mul (polyRqFromChal11 (tr.chal1 j)) y1)
  (w0, w1)

/-- Recompute all `R` commitment pairs from `(stmt, tr)`. -/
def recomputeJointOrComms {R : Nat} (stmt : RlweOrStatement)
    (tr : JointOrSigmaTranscriptGen R) : Fin R → (PolyRq1024 × PolyRq1024) :=
  fun j => recomputeJointOrRepComm stmt tr j

/-- Single-repetition response-box (`-3070 ≤ z_i < 3070`), commitment-equality, and
    11-bit XOR challenge check; exactly the per-repetition checks of `RlweReceiverZkPok::verify` (`preprocessing.rs:1342-1374`). -/
def verifyJointOrRepGen {R : Nat} (stmt : RlweOrStatement) (j : Fin R) (expectedChal : BitVec 11)
    (tr : JointOrSigmaTranscriptGen R) : Bool :=
  let boundsOk :=
    polyIntInZkpokBox (tr.zs0 j) &&
    polyIntInZkpokBox (tr.ze0 j) &&
    polyIntInZkpokBox (tr.zs1 j) &&
    polyIntInZkpokBox (tr.ze1 j)
  let (w0Exp, w1Exp) := recomputeJointOrRepComm stmt tr j
  let commMatch := polyRqEq w0Exp (tr.comms j).1 && polyRqEq w1Exp (tr.comms j).2
  let chalOk := decide ((tr.chal0 j ^^^ tr.chal1 j) = expectedChal)
  boundsOk && commMatch && chalOk

/-- Parametric `R`-repetition OR-Sigma verifier under XOF oracle `ro`. -/
def verifyJointOrSigmaWithRoGen (R : Nat) (ro : List UInt8 → List UInt8)
    (stmt : RlweOrStatement) (tr : JointOrSigmaTranscriptGen R) : Bool :=
  checkRlweOrStatementValid stmt &&
  let wRecomp := recomputeJointOrComms stmt tr
  let expected := hashRlweZkpokJointChallengesWithRo R ro
    stmt.crsCoin stmt.sessionId stmt.senderId stmt.receiverId stmt.otIdx stmt.pk0 stmt.tCrs wRecomp
  allFin R (fun j => verifyJointOrRepGen stmt j (expected j) tr)

/-- Production 13-repetition (`143`-bit classical) Fiat-Shamir OR-Sigma verifier binding
    statement & recomputed commitments via `cSHAKE256("QSAG.OT.RLWE.ZKPOK/v3")` (`preprocessing.rs:1324-1375`). -/
@[expose] def verifyJointOrSigma (stmt : RlweOrStatement) (tr : JointOrSigmaTranscript) : Bool :=
  verifyJointOrSigmaWithRoGen rlweZkpokReps (cshake256Xof (4 * rlweZkpokReps) rlweZkpokDomain) stmt tr

/-- Alias for the 13-repetition (`143`-bit classical) Fiat-Shamir OR-Sigma verifier. -/
def verifyJointOrSigmaPq13 (stmt : RlweOrStatement) (tr : JointOrSigmaTranscriptPq13) : Bool :=
  verifyJointOrSigmaWithRoGen rlweZkpokPqReps (cshake256Xof (4 * rlweZkpokPqReps) rlweZkpokDomain) stmt tr

/-- 24-repetition (`264`-bit QROM / `≥ 2^132` Grover) Fiat-Shamir OR-Sigma verifier. -/
def verifyJointOrSigmaPq24 (stmt : RlweOrStatement) (tr : JointOrSigmaTranscriptPq24) : Bool :=
  verifyJointOrSigmaWithRoGen rlweZkpokPq256Reps (cshake256Xof (4 * rlweZkpokPq256Reps) rlweZkpokDomain) stmt tr

/-- Constructively locate the first index `j ∈ Fin R` where two distinct challenge vectors differ
    (`0 Classical.choice`, supporting all `R`). -/
def findDiffFin : (R : Nat) → {α : Type} → [DecidableEq α] →
    (ch ch' : Fin R → α) → ch ≠ ch' → { j : Fin R // ch j ≠ ch' j }
  | 0, _, _, _, _, hNe =>
    False.elim <| hNe <| funext fun i => Fin.elim0 i
  | r + 1, _, _, ch, ch', hNe =>
    if h0 : ch ⟨0, Nat.zero_lt_succ r⟩ = ch' ⟨0, Nat.zero_lt_succ r⟩ then
      have hTailNe : (fun i : Fin r => ch ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) ≠
          (fun i : Fin r => ch' ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) := by
        intro hTailEq
        apply hNe
        funext ⟨k, hk⟩
        cases k with
        | zero => exact h0
        | succ k' => exact congrFun hTailEq ⟨k', Nat.lt_of_succ_lt_succ hk⟩
      let ⟨jTail, hjTail⟩ := findDiffFin r
        (fun i => ch ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
        (fun i => ch' ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
        hTailNe
      ⟨⟨jTail.1 + 1, Nat.succ_lt_succ jTail.2⟩, hjTail⟩
    else
      ⟨⟨0, Nat.zero_lt_succ r⟩, h0⟩

private theorem rlweBranch_sub_extract_chal11 (a y w : PolyRq1024)
    (u u' : BitVec 11)
    (zs ze zs' ze' : PolyInt 1024)
    (huNe : u ≠ u')
    (hs : polyIntInfNorm zs ≤ rlweZkpokZBound) (he : polyIntInfNorm ze ≤ rlweZkpokZBound)
    (hs' : polyIntInfNorm zs' ≤ rlweZkpokZBound) (he' : polyIntInfNorm ze' ≤ rlweZkpokZBound)
    (h1 : CommRingOps.sub (CommRingOps.add (CommRingOps.mul a (polyIntToRq zs)) (polyIntToRq ze))
        (CommRingOps.mul (polyRqFromChal11 u) y) = w)
    (h2 : CommRingOps.sub (CommRingOps.add (CommRingOps.mul a (polyIntToRq zs')) (polyIntToRq ze'))
        (CommRingOps.mul (polyRqFromChal11 u') y) = w) :
    let deltaD : PolyInt 1024 := fun k => polyIntFromChal11 u k - polyIntFromChal11 u' k
    let sWit : PolyInt 1024 := fun k => zs k - zs' k
    let eWit : PolyInt 1024 := fun k => ze k - ze' k
    polyIntToRq deltaD ≠ CommRingOps.zero ∧
    polyIntInfNorm deltaD ≤ 2 ∧
    polyIntL1Norm deltaD ≤ 2 ∧
    polyIntInfNorm sWit ≤ 2 * rlweZkpokZBound ∧
    polyIntInfNorm eWit ≤ 2 * rlweZkpokZBound ∧
    CommRingOps.add (CommRingOps.mul a (polyIntToRq sWit)) (polyIntToRq eWit) =
      CommRingOps.mul (polyIntToRq deltaD) y := by
  intro deltaD sWit eWit
  obtain ⟨hDeltaNz, hDeltaInf, hDeltaL1, _⟩ := chal11_diff_nonzero_short_and_invertible huNe
  have hS : polyIntInfNorm sWit ≤ 2 * rlweZkpokZBound := by
    dsimp only [sWit, rlweZkpokZBound] at *
    have := polyIntInfNorm_sub_le zs zs'
    omega
  have hE : polyIntInfNorm eWit ≤ 2 * rlweZkpokZBound := by
    dsimp only [eWit, rlweZkpokZBound] at *
    have := polyIntInfNorm_sub_le ze ze'
    omega
  refine ⟨hDeltaNz, hDeltaInf, hDeltaL1, hS, hE, ?_⟩
  have hEqW := h1.trans h2.symm
  dsimp only [sWit, eWit, deltaD]
  have hSubMul : CommRingOps.mul (polyIntToRq (fun k => polyIntFromChal11 u k - polyIntFromChal11 u' k)) y =
      CommRingOps.sub (CommRingOps.mul (polyRqFromChal11 u) y) (CommRingOps.mul (polyRqFromChal11 u') y) := by
    unfold polyRqFromChal11
    rw [polyIntToRq_sub, LawfulCommRing.mul_comm _ y, LawfulCommRing.mul_sub,
        LawfulCommRing.mul_comm y _, LawfulCommRing.mul_comm y _]
  rw [polyIntToRq_sub, polyIntToRq_sub, LawfulCommRing.mul_sub, hSubMul]
  funext k
  have hk := congrFun hEqW k
  let AZ := CommRingOps.mul a (polyIntToRq zs) k
  let AZ' := CommRingOps.mul a (polyIntToRq zs') k
  let E := polyIntToRq ze k
  let E' := polyIntToRq ze' k
  let DY := CommRingOps.mul (polyRqFromChal11 u) y k
  let DY' := CommRingOps.mul (polyRqFromChal11 u') y k
  change CommRingOps.sub (CommRingOps.add AZ E) DY = CommRingOps.sub (CommRingOps.add AZ' E') DY' at hk
  show CommRingOps.add (CommRingOps.sub AZ AZ') (CommRingOps.sub E E') = CommRingOps.sub DY DY'
  rw [← Zq12289.ofInt_natVal AZ, ← Zq12289.ofInt_natVal AZ',
      ← Zq12289.ofInt_natVal E, ← Zq12289.ofInt_natVal E',
      ← Zq12289.ofInt_natVal DY, ← Zq12289.ofInt_natVal DY'] at hk ⊢
  simp only [← Zq12289.ofInt_add, ← Zq12289.ofInt_sub] at hk ⊢
  have hkVal := congrArg Zq12289.val hk
  simp only [Zq12289.ofInt] at hkVal ⊢
  apply Zq12289.ext
  dsimp only
  omega

/-- Transcript-bound relaxed short RLWE witness extracted from two forked OR-Sigma transcripts
    (`0 Classical.choice`, `0` free fields, supporting all `R`, with 11-bit signed monomials `±X^k`). -/
structure ExtractedJointOrWitnessGen {R : Nat} (stmt : RlweOrStatement)
    (ro ro' : List UInt8 → List UInt8)
    (tr tr' : JointOrSigmaTranscriptGen R) where
  repIdx : Fin R
  branch : Bool
  uChal : BitVec 11
  uChal' : BitVec 11
  deltaChal : PolyInt 1024
  sWit : PolyInt 1024
  eWit : PolyInt 1024
  branch_chal_diff : uChal ≠ uChal'
  deltaChal_eq : deltaChal = fun k => polyIntFromChal11 uChal k - polyIntFromChal11 uChal' k
  deltaChal_nonzero : polyIntToRq deltaChal ≠ CommRingOps.zero
  deltaChal_inf_le : polyIntInfNorm deltaChal ≤ 2
  deltaChal_l1_le : polyIntL1Norm deltaChal ≤ 2
  s_short : polyIntInfNorm sWit ≤ 2 * rlweZkpokZBound
  e_short : polyIntInfNorm eWit ≤ 2 * rlweZkpokZBound
  relaxed_rlwe_rel :
    CommRingOps.add (CommRingOps.mul stmt.a (polyIntToRq sWit)) (polyIntToRq eWit) =
      CommRingOps.mul (polyIntToRq deltaChal) (stmt.branchPk branch)

abbrev ExtractedJointOrWitness := @ExtractedJointOrWitnessGen rlweZkpokReps
abbrev ExtractedJointOrWitnessPq13 := @ExtractedJointOrWitnessGen rlweZkpokPqReps
abbrev ExtractedJointOrWitnessPq24 := @ExtractedJointOrWitnessGen rlweZkpokPq256Reps

/-- **Constructive 2-Special Soundness Relaxed Knowledge Extractor (`jointOrSigma_extract_witness`)**:
    Given two accepting forked OR-Sigma transcripts `(tr, tr')` under random oracles `(ro, ro')` on the
    same statement `stmt` and commitment tuple `tr.comms = tr'.comms` whose forked joint 11-bit challenges
    differ (`ch ≠ ch'`), constructively locates `j ∈ Fin R` and extracts `(branch, uChal, uChal', deltaChal, sWit, eWit)`
    satisfying `a * sWit + eWit = (d(uChal) - d(uChal')) * stmt.branchPk branch` in `PolyRq1024` with
    `polyIntToRq deltaChal ∈ R_{12289}^×`, `‖deltaChal‖_1 ≤ 2`, and `‖sWit‖_∞, ‖eWit‖_∞ ≤ 2 * 3070 = 6140 < 6144`
    (`0 Classical.choice`)! -/
def jointOrSigma_extract_witness {R : Nat} (stmt : RlweOrStatement)
    (ro ro' : List UInt8 → List UInt8)
    (tr tr' : JointOrSigmaTranscriptGen R)
    (hComms : tr.comms = tr'.comms)
    (hNe : hashRlweZkpokJointChallengesWithRo R ro stmt.crsCoin stmt.sessionId
             stmt.senderId stmt.receiverId stmt.otIdx stmt.pk0 stmt.tCrs tr.comms ≠
           hashRlweZkpokJointChallengesWithRo R ro' stmt.crsCoin stmt.sessionId
             stmt.senderId stmt.receiverId stmt.otIdx stmt.pk0 stmt.tCrs tr'.comms)
    (hAcc : verifyJointOrSigmaWithRoGen R ro stmt tr = true)
    (hAcc' : verifyJointOrSigmaWithRoGen R ro' stmt tr' = true) :
    ExtractedJointOrWitnessGen stmt ro ro' tr tr' :=
  let ch := hashRlweZkpokJointChallengesWithRo R ro stmt.crsCoin stmt.sessionId
    stmt.senderId stmt.receiverId stmt.otIdx stmt.pk0 stmt.tCrs tr.comms
  let ch' := hashRlweZkpokJointChallengesWithRo R ro' stmt.crsCoin stmt.sessionId
    stmt.senderId stmt.receiverId stmt.otIdx stmt.pk0 stmt.tCrs tr'.comms
  let ⟨j, hjDiff⟩ := findDiffFin R ch ch' hNe
  have hRecompEq : recomputeJointOrComms stmt tr = tr.comms := by
    unfold verifyJointOrSigmaWithRoGen at hAcc
    simp only [Bool.and_eq_true] at hAcc
    have hAll := (allFin_eq_true_iff _).mp hAcc.2
    funext idx
    have hIdx := hAll idx
    unfold verifyJointOrRepGen at hIdx
    simp only [Bool.and_eq_true, polyRqEq_iff] at hIdx
    exact Prod.ext hIdx.1.2.1 hIdx.1.2.2
  have hRecompEq' : recomputeJointOrComms stmt tr' = tr'.comms := by
    unfold verifyJointOrSigmaWithRoGen at hAcc'
    simp only [Bool.and_eq_true] at hAcc'
    have hAll := (allFin_eq_true_iff _).mp hAcc'.2
    funext idx
    have hIdx := hAll idx
    unfold verifyJointOrRepGen at hIdx
    simp only [Bool.and_eq_true, polyRqEq_iff] at hIdx
    exact Prod.ext hIdx.1.2.1 hIdx.1.2.2
  have hRep : verifyJointOrRepGen stmt j (ch j) tr = true := by
    unfold verifyJointOrSigmaWithRoGen at hAcc
    simp only [Bool.and_eq_true] at hAcc
    have hAll := (allFin_eq_true_iff _).mp hAcc.2 j
    rw [hRecompEq] at hAll
    exact hAll
  have hRep' : verifyJointOrRepGen stmt j (ch' j) tr' = true := by
    unfold verifyJointOrSigmaWithRoGen at hAcc'
    simp only [Bool.and_eq_true] at hAcc'
    have hAll := (allFin_eq_true_iff _).mp hAcc'.2 j
    rw [hRecompEq'] at hAll
    exact hAll
  if hc0 : tr.chal0 j = tr'.chal0 j then
    have hc1Ne : tr.chal1 j ≠ tr'.chal1 j := by
      intro hc1Eq
      unfold verifyJointOrRepGen at hRep hRep'
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hRep hRep'
      have hXor := hRep.2
      have hXor' := hRep'.2
      rw [hc0, hc1Eq] at hXor
      exact hjDiff (hXor.symm.trans hXor')
    let u := tr.chal1 j
    let u' := tr'.chal1 j
    let deltaD : PolyInt 1024 := fun k => polyIntFromChal11 u k - polyIntFromChal11 u' k
    let sWit : PolyInt 1024 := fun k => tr.zs1 j k - tr'.zs1 j k
    let eWit : PolyInt 1024 := fun k => tr.ze1 j k - tr'.ze1 j k
    have hUnp :
        polyIntInfNorm (tr.zs1 j) ≤ rlweZkpokZBound ∧
        polyIntInfNorm (tr.ze1 j) ≤ rlweZkpokZBound ∧
        CommRingOps.sub (CommRingOps.add (CommRingOps.mul stmt.a (polyIntToRq (tr.zs1 j))) (polyIntToRq (tr.ze1 j)))
          (CommRingOps.mul (polyRqFromChal11 (tr.chal1 j)) (CommRingOps.add stmt.pk0 stmt.tCrs)) = (tr.comms j).2 := by
      unfold verifyJointOrRepGen recomputeJointOrRepComm at hRep
      simp only [Bool.and_eq_true, decide_eq_true_eq, polyRqEq_iff] at hRep
      exact ⟨polyIntInZkpokBox_infNorm_le hRep.1.1.1.2, polyIntInZkpokBox_infNorm_le hRep.1.1.2, hRep.1.2.2⟩
    have hUnp' :
        polyIntInfNorm (tr'.zs1 j) ≤ rlweZkpokZBound ∧
        polyIntInfNorm (tr'.ze1 j) ≤ rlweZkpokZBound ∧
        CommRingOps.sub (CommRingOps.add (CommRingOps.mul stmt.a (polyIntToRq (tr'.zs1 j))) (polyIntToRq (tr'.ze1 j)))
          (CommRingOps.mul (polyRqFromChal11 (tr'.chal1 j)) (CommRingOps.add stmt.pk0 stmt.tCrs)) = (tr.comms j).2 := by
      unfold verifyJointOrRepGen recomputeJointOrRepComm at hRep'
      simp only [Bool.and_eq_true, decide_eq_true_eq, polyRqEq_iff] at hRep'
      have hw1' := hRep'.1.2.2
      rw [← hComms] at hw1'
      exact ⟨polyIntInZkpokBox_infNorm_le hRep'.1.1.1.2, polyIntInZkpokBox_infNorm_le hRep'.1.1.2, hw1'⟩
    let hPack := rlweBranch_sub_extract_chal11 stmt.a (CommRingOps.add stmt.pk0 stmt.tCrs) (tr.comms j).2
      u u' (tr.zs1 j) (tr.ze1 j) (tr'.zs1 j) (tr'.ze1 j) hc1Ne
      hUnp.1 hUnp.2.1 hUnp'.1 hUnp'.2.1 hUnp.2.2 hUnp'.2.2
    ⟨j, true, u, u', deltaD, sWit, eWit, hc1Ne, rfl,
      hPack.1, hPack.2.1, hPack.2.2.1, hPack.2.2.2.1, hPack.2.2.2.2.1, hPack.2.2.2.2.2⟩
  else
    let u := tr.chal0 j
    let u' := tr'.chal0 j
    let deltaD : PolyInt 1024 := fun k => polyIntFromChal11 u k - polyIntFromChal11 u' k
    let sWit : PolyInt 1024 := fun k => tr.zs0 j k - tr'.zs0 j k
    let eWit : PolyInt 1024 := fun k => tr.ze0 j k - tr'.ze0 j k
    have hUnp :
        polyIntInfNorm (tr.zs0 j) ≤ rlweZkpokZBound ∧
        polyIntInfNorm (tr.ze0 j) ≤ rlweZkpokZBound ∧
        CommRingOps.sub (CommRingOps.add (CommRingOps.mul stmt.a (polyIntToRq (tr.zs0 j))) (polyIntToRq (tr.ze0 j)))
          (CommRingOps.mul (polyRqFromChal11 (tr.chal0 j)) stmt.pk0) = (tr.comms j).1 := by
      unfold verifyJointOrRepGen recomputeJointOrRepComm at hRep
      simp only [Bool.and_eq_true, decide_eq_true_eq, polyRqEq_iff] at hRep
      exact ⟨polyIntInZkpokBox_infNorm_le hRep.1.1.1.1.1, polyIntInZkpokBox_infNorm_le hRep.1.1.1.1.2, hRep.1.2.1⟩
    have hUnp' :
        polyIntInfNorm (tr'.zs0 j) ≤ rlweZkpokZBound ∧
        polyIntInfNorm (tr'.ze0 j) ≤ rlweZkpokZBound ∧
        CommRingOps.sub (CommRingOps.add (CommRingOps.mul stmt.a (polyIntToRq (tr'.zs0 j))) (polyIntToRq (tr'.ze0 j)))
          (CommRingOps.mul (polyRqFromChal11 (tr'.chal0 j)) stmt.pk0) = (tr.comms j).1 := by
      unfold verifyJointOrRepGen recomputeJointOrRepComm at hRep'
      simp only [Bool.and_eq_true, decide_eq_true_eq, polyRqEq_iff] at hRep'
      have hw0' := hRep'.1.2.1
      rw [← hComms] at hw0'
      exact ⟨polyIntInZkpokBox_infNorm_le hRep'.1.1.1.1.1, polyIntInZkpokBox_infNorm_le hRep'.1.1.1.1.2, hw0'⟩
    let hPack := rlweBranch_sub_extract_chal11 stmt.a stmt.pk0 (tr.comms j).1
      u u' (tr.zs0 j) (tr.ze0 j) (tr'.zs0 j) (tr'.ze0 j) hc0
      hUnp.1 hUnp.2.1 hUnp'.1 hUnp'.2.1 hUnp.2.2 hUnp'.2.2
    ⟨j, false, u, u', deltaD, sWit, eWit, hc0, rfl,
      hPack.1, hPack.2.1, hPack.2.2.1, hPack.2.2.2.1, hPack.2.2.2.2.1, hPack.2.2.2.2.2⟩

/-! ### 2.1a Weld to the Cyclotomic Extractor of `Qsag.RlweCyclotomicExtraction`

`polyRqToCyc` transports the production v3 fork difference to the cyclotomic ring.
Every distinct 11-bit challenge pair supports the cofactor lift. The 20-bit constructions below
are historical counterexamples and are not consumed by the v3 verifier. -/

/-- Lower-half signed monomial $\pm X^{p_0}$ of a 20-bit challenge. -/
def chal20Mono0 (u : BitVec 20) : SignedMonomialChal 10 := ⟨chal20Sign0 u, chal20Pos0 u⟩

/-- Upper-half signed monomial $\pm X^{512 + p_1}$ of a 20-bit challenge. -/
def chal20Mono1 (u : BitVec 20) : SignedMonomialChal 10 := ⟨chal20Sign1 u, chal20Pos1 u⟩

/-- `poly_from_chal20` is the sum of its two signed monomials. -/
theorem polyIntFromChal20_eq_two_monomials (u : BitVec 20) :
    polyIntFromChal20 u = cycIntAdd (chal20Mono0 u).toIntPoly (chal20Mono1 u).toIntPoly := by
  funext k
  have hV0 : chal20Val0 u = signBitToInt (chal20Sign0 u) := rfl
  have hV1 : chal20Val1 u = signBitToInt (chal20Sign1 u) := rfl
  unfold polyIntFromChal20 cycIntAdd SignedMonomialChal.toIntPoly signedMonomial
    negacyclicSignedMonomial chal20Mono0 chal20Mono1
  dsimp only
  by_cases h0 : k = chal20Pos0 u
  · simp only [h0, chal20Pos0_ne_pos1 u, ↓reduceIte, hV0, Int.add_zero]
  · by_cases h1 : k = chal20Pos1 u
    · simp only [h1, (chal20Pos0_ne_pos1 u).symm, ↓reduceIte, hV1, Int.zero_add]
    · simp only [h0, h1, ↓reduceIte, Int.add_zero]

/-- A 20-bit challenge is determined by its two signed monomials. -/
theorem chal20_eq_of_monos_eq {u u' : BitVec 20}
    (h0 : chal20Mono0 u = chal20Mono0 u') (h1 : chal20Mono1 u = chal20Mono1 u') : u = u' := by
  apply polyRqFromChal20_injective
  unfold polyRqFromChal20
  rw [polyIntFromChal20_eq_two_monomials, polyIntFromChal20_eq_two_monomials, h0, h1]

/-- The cyclotomic OR-Sigma statement `(A, pk0, pk0 + tCrs, 3070)` of a base-OT statement. -/
def RlweOrStatement.toCyclotomic (stmt : RlweOrStatement) : RlweOrSigmaStatement 10 12289 :=
  RlweOrSigmaStatement.fromBaseOt (polyRqToCyc stmt.a) (polyRqToCyc stmt.pk0)
    (polyRqToCyc stmt.tCrs) rlweZkpokZBound

theorem RlweOrStatement.toCyclotomic_branchU (stmt : RlweOrStatement) (b : Bool) :
    stmt.toCyclotomic.branchU b = polyRqToCyc (stmt.branchPk b) := by
  cases b
  · rfl
  · show cycZqAdd (polyRqToCyc stmt.pk0) (polyRqToCyc stmt.tCrs) =
      polyRqToCyc (CommRingOps.add stmt.pk0 stmt.tCrs)
    rw [polyRqToCyc_add]

/-- **The production fork difference in the cyclotomic ring
    (`jointOrSigma_fork_difference_cyclotomic`)**:
    the witness of `jointOrSigma_extract_witness` satisfies
    `A * sWit + eWit = (d(u) - d(u')) * Y_b` in `CycPolyZq 10 12289`, and `(sWit, eWit)` are recovered
    exactly from their reductions modulo `12289` (`‖·‖_∞ ≤ 6140 < 6144`). This holds for every forked
    pair of accepting transcripts; it is a relation twisted by the challenge difference, not a witness
    for `Y_b`. -/
theorem jointOrSigma_fork_difference_cyclotomic {R : Nat} {stmt : RlweOrStatement}
    {ro ro' : List UInt8 → List UInt8} {tr tr' : JointOrSigmaTranscriptGen R}
    (w : ExtractedJointOrWitnessGen stmt ro ro' tr tr') :
    cycZqAdd (cycZqMul stmt.toCyclotomic.A (cycIntToZq 12289 w.sWit)) (cycIntToZq 12289 w.eWit) =
      cycZqMul (cycIntToZq 12289 w.deltaChal) (stmt.toCyclotomic.branchU w.branch) ∧
    cycZqCentered (cycIntToZq 12289 w.sWit) = w.sWit ∧
    cycZqCentered (cycIntToZq 12289 w.eWit) = w.eWit := by
  refine ⟨?_, ?_, ?_⟩
  · have hRel := congrArg polyRqToCyc w.relaxed_rlwe_rel
    rw [polyRqToCyc_add, polyRqToCyc_mul, polyRqToCyc_mul, polyRqToCyc_polyIntToRq,
        polyRqToCyc_polyIntToRq, polyRqToCyc_polyIntToRq] at hRel
    rw [RlweOrStatement.toCyclotomic_branchU]
    exact hRel
  · apply rlwe_fork_difference_zero_modular_wraparound_production
    have hS := w.s_short
    rw [polyIntInfNorm_eq_cycIntInfNorm] at hS
    exact hS
  · apply rlwe_fork_difference_zero_modular_wraparound_production
    have hE := w.e_short
    rw [polyIntInfNorm_eq_cycIntInfNorm] at hE
    exact hE

private theorem cycIntSub_add_cancel_right {N : Nat} (a a' c : NegacyclicPolyInt N) :
    cycIntSub (cycIntAdd a c) (cycIntAdd a' c) = cycIntSub a a' := by
  funext k; dsimp only [cycIntSub, cycIntAdd]; omega

private theorem cycIntSub_add_cancel_left {N : Nat} (c a a' : NegacyclicPolyInt N) :
    cycIntSub (cycIntAdd c a) (cycIntAdd c a') = cycIntSub a a' := by
  funext k; dsimp only [cycIntSub, cycIntAdd]; omega

/-- Total cofactor lift for the v3 single-monomial fork. The resulting large-norm
    modular relation alone is not a hardness claim. -/
def ExtractedJointOrWitnessGen.cofactorLift {R : Nat} {stmt : RlweOrStatement}
    {ro ro' : List UInt8 → List UInt8} {tr tr' : JointOrSigmaTranscriptGen R}
    (w : ExtractedJointOrWitnessGen stmt ro ro' tr tr') :
    ExtractedRlweOrSigmaWitness R 10 12289 stmt.toCyclotomic :=
  ExtractedRlweOrSigmaWitness.ofForkDifference stmt.toCyclotomic w.repIdx w.branch
    (chal11ToSignedMonomial w.uChal) (chal11ToSignedMonomial w.uChal')
    (fun h => w.branch_chal_diff (SignedMonomialChal.ofBitVec_injective h))
    w.sWit w.eWit
    (by simpa only [← polyIntInfNorm_eq_cycIntInfNorm, RlweOrStatement.toCyclotomic, RlweOrSigmaStatement.fromBaseOt] using w.s_short)
    (by simpa only [← polyIntInfNorm_eq_cycIntInfNorm, RlweOrStatement.toCyclotomic, RlweOrSigmaStatement.fromBaseOt] using w.e_short)
    (by
      have hDelta : w.deltaChal = cycIntSub
          (chal11ToSignedMonomial w.uChal).toIntPoly
          (chal11ToSignedMonomial w.uChal').toIntPoly := by
        rw [w.deltaChal_eq]
        funext k
        simp only [polyIntFromChal11, cycIntSub]
      have h := (jointOrSigma_fork_difference_cyclotomic w).1
      rw [hDelta] at h
      exact h)

/-- The v3 extractor has no shared-monomial side condition. -/
theorem ExtractedJointOrWitnessGen.cofactorLift_isLeft_iff {R : Nat} {stmt : RlweOrStatement}
    {ro ro' : List UInt8 → List UInt8} {tr tr' : JointOrSigmaTranscriptGen R}
    (w : ExtractedJointOrWitnessGen stmt ro ro' tr tr') :
    Nonempty (ExtractedRlweOrSigmaWitness R 10 12289 stmt.toCyclotomic) :=
  ⟨w.cofactorLift⟩

/-- Isometric fork relation; the relaxation remains part of the statement. -/
def ExtractedJointOrWitnessGen.toShortMonomialWitness {R : Nat} {stmt : RlweOrStatement}
    {ro ro' : List UInt8 → List UInt8} {tr tr' : JointOrSigmaTranscriptGen R}
    (w : ExtractedJointOrWitnessGen stmt ro ro' tr tr') :
    ShortMonomialRelaxedRlweWitness R 10 12289 stmt.toCyclotomic :=
  ShortMonomialRelaxedRlweWitness.ofForkDifference stmt.toCyclotomic w.repIdx w.branch
    (chal11ToSignedMonomial w.uChal) (chal11ToSignedMonomial w.uChal')
    (fun h => w.branch_chal_diff (SignedMonomialChal.ofBitVec_injective h))
    w.sWit w.eWit
    (by simpa only [← polyIntInfNorm_eq_cycIntInfNorm, RlweOrStatement.toCyclotomic, RlweOrSigmaStatement.fromBaseOt] using w.s_short)
    (by simpa only [← polyIntInfNorm_eq_cycIntInfNorm, RlweOrStatement.toCyclotomic, RlweOrSigmaStatement.fromBaseOt] using w.e_short)
    (by
      have hDelta : w.deltaChal = cycIntSub
          (chal11ToSignedMonomial w.uChal).toIntPoly
          (chal11ToSignedMonomial w.uChal').toIntPoly := by
        rw [w.deltaChal_eq]
        funext k
        simp only [polyIntFromChal11, cycIntSub]
      have h := (jointOrSigma_fork_difference_cyclotomic w).1
      rw [hDelta] at h
      exact h)

/-- **Soundness content of a cofactor witness for the production statement
    (`jointOrSigma_cofactor_witness_sound`)**:
    every `ExtractedRlweOrSigmaWitness` for `stmt.toCyclotomic` gives
    1. `‖s2‖_∞, ‖e2‖_∞ ≤ 2 * 1024 * 3070 = 6287360`,
    2. `A * s2 + e2 = 2 * Y_b` in $R_{12289}$,
    3. the exact relation `A * (h * s2) + h * e2 = Y_b` with `h = (12289 + 1) / 2`, a preimage of the
       branch public key modulo `12289` (its centered norm is not bounded by this theorem, because
       `6287360 ≥ 6144`), and
    4. the explicit inverse of the challenge difference used
       (`signedMonomial_1024_challenge_set_2048_pairwise_invertible`). -/
theorem jointOrSigma_cofactor_witness_sound {R : Nat} (stmt : RlweOrStatement)
    (cw : ExtractedRlweOrSigmaWitness R 10 12289 stmt.toCyclotomic) :
    cycIntInfNorm cw.s2 ≤ 6287360 ∧
    cycIntInfNorm cw.e2 ≤ 6287360 ∧
    cycZqAdd (cycZqMul (polyRqToCyc stmt.a) (cycIntToZq 12289 cw.s2)) (cycIntToZq 12289 cw.e2) =
      cycZqScale 2 (polyRqToCyc (stmt.branchPk cw.branch)) ∧
    cycZqAdd
      (cycZqMul (polyRqToCyc stmt.a) (cycZqScale (((12289 + 1) / 2 : Nat) : Int) (cycIntToZq 12289 cw.s2)))
      (cycZqScale (((12289 + 1) / 2 : Nat) : Int) (cycIntToZq 12289 cw.e2)) =
      polyRqToCyc (stmt.branchPk cw.branch) ∧
    cycZqMul (cycZqSub (cw.chal.toZqPoly 12289) (cw.chal'.toZqPoly 12289))
      (signedMonomialDiffInvZq 10 12289 cw.chal cw.chal') = cycZqOne := by
  have hS : cycIntInfNorm cw.s2 ≤ 6287360 := cw.s2_infNorm_le
  have hE : cycIntInfNorm cw.e2 ≤ 6287360 := cw.e2_infNorm_le
  have hRel := cw.relaxed_rlwe_mod_q
  rw [RlweOrStatement.toCyclotomic_branchU] at hRel
  have hUn := extracted_witness_unrelaxed_odd_q (by decide : 12289 % 2 = 1) cw
  dsimp only at hUn
  rw [RlweOrStatement.toCyclotomic_branchU] at hUn
  exact ⟨hS, hE, hRel, hUn,
    (signedMonomial_1024_challenge_set_2048_pairwise_invertible 12289 (by decide) (by decide)
      cw.chal cw.chal' cw.chal_ne).2.2.1⟩

/-- **`#tooth`: two production challenges whose difference has no inverse
    (`tooth_chal20_difference_not_invertible`)**:
    `u = 108` ($X^{108} + X^{512}$) and `u' = 1026` ($X^{2} + X^{513}$) differ in both signed monomials,
    and `d(u) - d(u')` is not a unit of `PolyRq1024`: both challenges take the value `11331` at the root
    `1945` of $X^{1024} + 1$ modulo `12289`. A fork on this pair yields the fork difference only. -/
theorem tooth_chal20_difference_not_invertible :
    (108#20 : BitVec 20) ≠ 1026#20 ∧
    chal20Mono0 108#20 ≠ chal20Mono0 1026#20 ∧
    chal20Mono1 108#20 ≠ chal20Mono1 1026#20 ∧
    (∀ inv : PolyRq1024,
      CommRingOps.mul (CommRingOps.sub (polyRqFromChal20 108#20) (polyRqFromChal20 1026#20)) inv ≠
        CommRingOps.one) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro inv hInv
  have hCyc := congrArg polyRqToCyc hInv
  unfold polyRqFromChal20 at hCyc
  rw [polyRqToCyc_mul, polyRqToCyc_sub, polyRqToCyc_polyIntToRq, polyRqToCyc_polyIntToRq,
      polyRqToCyc_one, polyIntFromChal20_eq_two_monomials, polyIntFromChal20_eq_two_monomials,
      ← cycIntToZq_sub] at hCyc
  exact tooth_two_term_challenge_difference_zero_divisor_12289.2.2 (polyRqToCyc inv) hCyc

/-- Masked honest OR-Sigma prover parameterized by XOF oracle `ro`, mirroring `RlweReceiverZkPok::prove_ct`
    (`preprocessing.rs:1040-1114`): computes real masked commitment `wReal = a * ysMask + yeMask ≠ 0`,
    simulated fake commitment `wFake = a * zsFake + zeFake - d(uFake) * yFake`, derives joint challenges
    via `hashRlweZkpokJointChallengesWithRo`, sets `uReal = ch ^^^ uFake`, and masks the secret witness
    `(sR, e1)` via `zReal = yMask + d(uReal) ⊛ (sR, e1)`. -/
def buildHonestJointOrTranscriptWithRoGen (R : Nat) (ro : List UInt8 → List UInt8)
    (stmt : RlweOrStatement) (branch : Bool)
    (sR e1 : PolyInt 1024)
    (ysMask yeMask : Fin R → PolyInt 1024)
    (uFake : Fin R → BitVec 11)
    (zsFake zeFake : Fin R → PolyInt 1024) : JointOrSigmaTranscriptGen R :=
  let yFake := if branch then stmt.pk0 else CommRingOps.add stmt.pk0 stmt.tCrs
  let comms : Fin R → (PolyRq1024 × PolyRq1024) := fun j =>
    let wReal := CommRingOps.add
      (CommRingOps.mul stmt.a (polyIntToRq (ysMask j)))
      (polyIntToRq (yeMask j))
    let wFake := CommRingOps.sub
      (CommRingOps.add (CommRingOps.mul stmt.a (polyIntToRq (zsFake j))) (polyIntToRq (zeFake j)))
      (CommRingOps.mul (polyRqFromChal11 (uFake j)) yFake)
    if branch then (wFake, wReal) else (wReal, wFake)
  let ch := hashRlweZkpokJointChallengesWithRo R ro
    stmt.crsCoin stmt.sessionId stmt.senderId stmt.receiverId stmt.otIdx stmt.pk0 stmt.tCrs comms
  let uReal : Fin R → BitVec 11 := fun j => ch j ^^^ uFake j
  let zsReal : Fin R → PolyInt 1024 := fun j k =>
    polyIntMul (polyIntFromChal11 (uReal j)) sR k + ysMask j k
  let zeReal : Fin R → PolyInt 1024 := fun j k =>
    polyIntMul (polyIntFromChal11 (uReal j)) e1 k + yeMask j k
  if branch then
    { comms := comms
      chal0 := uFake
      chal1 := uReal
      zs0 := zsFake
      ze0 := zeFake
      zs1 := zsReal
      ze1 := zeReal }
  else
    { comms := comms
      chal0 := uReal
      chal1 := uFake
      zs0 := zsReal
      ze0 := zeReal
      zs1 := zsFake
      ze1 := zeFake }

/-- Production masked honest OR-Sigma prover using `cSHAKE256("QSAG.OT.RLWE.ZKPOK/v3")`. -/
def buildHonestJointOrTranscriptGen (R : Nat)
    (stmt : RlweOrStatement) (branch : Bool)
    (sR e1 : PolyInt 1024)
    (ysMask yeMask : Fin R → PolyInt 1024)
    (uFake : Fin R → BitVec 11)
    (zsFake zeFake : Fin R → PolyInt 1024) : JointOrSigmaTranscriptGen R :=
  buildHonestJointOrTranscriptWithRoGen R (cshake256Xof (4 * R) rlweZkpokDomain)
    stmt branch sR e1 ysMask yeMask uFake zsFake zeFake

abbrev buildHonestJointOrTranscript := buildHonestJointOrTranscriptGen rlweZkpokReps
abbrev buildHonestJointOrTranscriptPq13 := buildHonestJointOrTranscriptGen rlweZkpokPqReps

private theorem real_branch_comm_cancel (a yReal : PolyRq1024)
    (sR e1 ys ye : PolyInt 1024) (u : BitVec 11)
    (hRel : CommRingOps.add (CommRingOps.mul a (polyIntToRq sR)) (polyIntToRq e1) = yReal) :
    CommRingOps.sub
      (CommRingOps.add
        (CommRingOps.mul a (polyIntToRq (fun k => polyIntMul (polyIntFromChal11 u) sR k + ys k)))
        (polyIntToRq (fun k => polyIntMul (polyIntFromChal11 u) e1 k + ye k)))
      (CommRingOps.mul (polyRqFromChal11 u) yReal) =
    CommRingOps.add (CommRingOps.mul a (polyIntToRq ys)) (polyIntToRq ye) := by
  rw [polyIntToRq_add, polyIntToRq_add, polyIntToRq_mul, polyIntToRq_mul]
  change CommRingOps.sub
      (CommRingOps.add
        (CommRingOps.mul a (CommRingOps.add (CommRingOps.mul (polyRqFromChal11 u) (polyIntToRq sR)) (polyIntToRq ys)))
        (CommRingOps.add (CommRingOps.mul (polyRqFromChal11 u) (polyIntToRq e1)) (polyIntToRq ye)))
      (CommRingOps.mul (polyRqFromChal11 u) yReal) =
    CommRingOps.add (CommRingOps.mul a (polyIntToRq ys)) (polyIntToRq ye)
  have hMulShift :
      CommRingOps.add
        (CommRingOps.mul a (CommRingOps.mul (polyRqFromChal11 u) (polyIntToRq sR)))
        (CommRingOps.mul (polyRqFromChal11 u) (polyIntToRq e1)) =
      CommRingOps.mul (polyRqFromChal11 u) yReal := by
    rw [← hRel, LawfulCommRing.left_distrib,
        ← LawfulCommRing.mul_assoc a (polyRqFromChal11 u) (polyIntToRq sR),
        LawfulCommRing.mul_comm a (polyRqFromChal11 u),
        LawfulCommRing.mul_assoc (polyRqFromChal11 u) a (polyIntToRq sR)]
  rw [LawfulCommRing.left_distrib]
  funext k
  have hkShift := congrFun hMulShift k
  let D_AS := CommRingOps.mul a (CommRingOps.mul (polyRqFromChal11 u) (polyIntToRq sR)) k
  let A_YS := CommRingOps.mul a (polyIntToRq ys) k
  let D_E := CommRingOps.mul (polyRqFromChal11 u) (polyIntToRq e1) k
  let YE := polyIntToRq ye k
  let DY := CommRingOps.mul (polyRqFromChal11 u) yReal k
  change CommRingOps.add D_AS D_E = DY at hkShift
  show CommRingOps.sub (CommRingOps.add (CommRingOps.add D_AS A_YS) (CommRingOps.add D_E YE)) DY =
    CommRingOps.add A_YS YE
  rw [← Zq12289.ofInt_natVal D_AS, ← Zq12289.ofInt_natVal D_E, ← Zq12289.ofInt_natVal DY] at hkShift
  rw [← Zq12289.ofInt_natVal D_AS, ← Zq12289.ofInt_natVal A_YS,
      ← Zq12289.ofInt_natVal D_E, ← Zq12289.ofInt_natVal YE,
      ← Zq12289.ofInt_natVal DY]
  simp only [← Zq12289.ofInt_add] at hkShift
  simp only [← Zq12289.ofInt_add, ← Zq12289.ofInt_sub]
  have hkVal := congrArg Zq12289.val hkShift
  simp only [Zq12289.ofInt] at hkVal ⊢
  apply Zq12289.ext
  dsimp only
  omega

private theorem bitvec20_xor_cancel_right (c f : BitVec 11) : (c ^^^ f) ^^^ f = c := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_xor]
  cases c.getLsbD i <;> cases f.getLsbD i <;> rfl

private theorem bitvec20_xor_cancel_left (f c : BitVec 11) : f ^^^ (c ^^^ f) = c := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_xor]
  cases f.getLsbD i <;> cases c.getLsbD i <;> rfl

/-- **Completeness of Masked OR-Sigma Prover (`honestJointOrTranscriptWithRo_accepts`)**:
    Whenever `(sR, e1)` is a short RLWE witness on `stmt.branchPk branch` and masks `(ysMask, yeMask)`
    lie inside the safe box (`2 * ‖sR‖_∞ + ‖ysMask‖_∞ < 3070`, `2 * ‖e1‖_∞ + ‖yeMask‖_∞ < 3070`)
    `verifyJointOrSigmaWithRoGen` accepts! -/
theorem honestJointOrTranscriptWithRo_accepts {R : Nat} (ro : List UInt8 → List UInt8)
    (stmt : RlweOrStatement) (branch : Bool)
    (sR e1 : PolyInt 1024)
    (ysMask yeMask : Fin R → PolyInt 1024)
    (uFake : Fin R → BitVec 11)
    (zsFake zeFake : Fin R → PolyInt 1024)
    (hStmt : checkRlweOrStatementValid stmt = true)
    (hRel : CommRingOps.add (CommRingOps.mul stmt.a (polyIntToRq sR)) (polyIntToRq e1) =
      stmt.branchPk branch)
    (hSafeS : ∀ j : Fin R, 2 * polyIntInfNorm sR + polyIntInfNorm (ysMask j) < rlweZkpokZBound)
    (hSafeE : ∀ j : Fin R, 2 * polyIntInfNorm e1 + polyIntInfNorm (yeMask j) < rlweZkpokZBound)
    (hFakeS : ∀ j : Fin R, polyIntInfNorm (zsFake j) < rlweZkpokZBound)
    (hFakeE : ∀ j : Fin R, polyIntInfNorm (zeFake j) < rlweZkpokZBound) :
    verifyJointOrSigmaWithRoGen R ro stmt
      (buildHonestJointOrTranscriptWithRoGen R ro stmt branch sR e1 ysMask yeMask uFake zsFake zeFake) = true := by
  let tr := buildHonestJointOrTranscriptWithRoGen R ro stmt branch sR e1 ysMask yeMask uFake zsFake zeFake
  have hRecomp : recomputeJointOrComms stmt tr = tr.comms := by
    funext j
    dsimp only [tr, buildHonestJointOrTranscriptWithRoGen, recomputeJointOrComms, recomputeJointOrRepComm]
    cases branch
    · simp only [Bool.false_eq_true, ↓reduceIte]
      unfold RlweOrStatement.branchPk at hRel
      simp only [Bool.false_eq_true, ↓reduceIte] at hRel
      exact Prod.ext
        (real_branch_comm_cancel stmt.a stmt.pk0 sR e1 (ysMask j) (yeMask j) _ hRel)
        rfl
    · simp only [↓reduceIte]
      unfold RlweOrStatement.branchPk at hRel
      simp only [↓reduceIte] at hRel
      exact Prod.ext
        rfl
        (real_branch_comm_cancel stmt.a (CommRingOps.add stmt.pk0 stmt.tCrs) sR e1 (ysMask j) (yeMask j) _ hRel)
  unfold verifyJointOrSigmaWithRoGen
  simp only [hStmt, Bool.true_and]
  change allFin R (fun j => verifyJointOrRepGen stmt j
    (hashRlweZkpokJointChallengesWithRo R ro stmt.crsCoin stmt.sessionId
      stmt.senderId stmt.receiverId stmt.otIdx stmt.pk0 stmt.tCrs (recomputeJointOrComms stmt tr) j) tr) = true
  rw [hRecomp, allFin_eq_true_iff]
  intro j
  have hRepEq : recomputeJointOrRepComm stmt tr j = tr.comms j := congrFun hRecomp j
  unfold verifyJointOrRepGen
  rw [hRepEq]
  have hRealSBound : ∀ u : BitVec 11,
      polyIntInfNorm (fun k => polyIntMul (polyIntFromChal11 u) sR k + ysMask j k) < rlweZkpokZBound := by
    intro u
    have hConv := negacyclic_infNorm_mul_add_le (polyIntFromChal11 u) sR (ysMask j)
    rw [polyIntFromChal11_l1Norm_eq_one] at hConv
    have hSafe := hSafeS j
    omega
  have hRealEBound : ∀ u : BitVec 11,
      polyIntInfNorm (fun k => polyIntMul (polyIntFromChal11 u) e1 k + yeMask j k) < rlweZkpokZBound := by
    intro u
    have hConv := negacyclic_infNorm_mul_add_le (polyIntFromChal11 u) e1 (yeMask j)
    rw [polyIntFromChal11_l1Norm_eq_one] at hConv
    have hSafe := hSafeE j
    omega
  have hBounds :
      (polyIntInZkpokBox (tr.zs0 j) &&
       polyIntInZkpokBox (tr.ze0 j) &&
       polyIntInZkpokBox (tr.zs1 j) &&
       polyIntInZkpokBox (tr.ze1 j)) = true := by
    dsimp only [tr, buildHonestJointOrTranscriptWithRoGen]
    cases branch
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true]
      exact ⟨⟨⟨polyIntInZkpokBox_of_infNorm_lt (hRealSBound _),
        polyIntInZkpokBox_of_infNorm_lt (hRealEBound _)⟩,
        polyIntInZkpokBox_of_infNorm_lt (hFakeS j)⟩, polyIntInZkpokBox_of_infNorm_lt (hFakeE j)⟩
    · simp only [↓reduceIte, Bool.and_eq_true]
      exact ⟨⟨⟨polyIntInZkpokBox_of_infNorm_lt (hFakeS j),
        polyIntInZkpokBox_of_infNorm_lt (hFakeE j)⟩,
        polyIntInZkpokBox_of_infNorm_lt (hRealSBound _)⟩, polyIntInZkpokBox_of_infNorm_lt (hRealEBound _)⟩
  have hMatch : (polyRqEq (tr.comms j).1 (tr.comms j).1 && polyRqEq (tr.comms j).2 (tr.comms j).2) = true := by
    simp only [polyRqEq_self, Bool.and_self]
  have hChal : decide ((tr.chal0 j ^^^ tr.chal1 j) =
      hashRlweZkpokJointChallengesWithRo R ro stmt.crsCoin stmt.sessionId
        stmt.senderId stmt.receiverId stmt.otIdx stmt.pk0 stmt.tCrs tr.comms j) = true := by
    dsimp only [tr, buildHonestJointOrTranscriptWithRoGen]
    cases branch
    · simp only [Bool.false_eq_true, ↓reduceIte, bitvec20_xor_cancel_right, decide_true]
    · simp only [↓reduceIte, bitvec20_xor_cancel_left, decide_true]
  dsimp only
  rw [hBounds, hMatch, hChal]
  rfl

/-- **Production Completeness of `verifyJointOrSigma` (`honestJointOrTranscript_accepts`)**:
    Honest masked transcripts accept under production `cSHAKE256("QSAG.OT.RLWE.ZKPOK/v3")` at both
    `R = 7` (`verifyJointOrSigma`) and `R = 13` (`verifyJointOrSigmaPq13`). -/
theorem honestJointOrTranscript_accepts (stmt : RlweOrStatement) (branch : Bool)
    (sR e1 : PolyInt 1024)
    (ysMask yeMask : Fin rlweZkpokReps → PolyInt 1024)
    (uFake : Fin rlweZkpokReps → BitVec 11)
    (zsFake zeFake : Fin rlweZkpokReps → PolyInt 1024)
    (hStmt : checkRlweOrStatementValid stmt = true)
    (hRel : CommRingOps.add (CommRingOps.mul stmt.a (polyIntToRq sR)) (polyIntToRq e1) =
      stmt.branchPk branch)
    (hSafeS : ∀ j, 2 * polyIntInfNorm sR + polyIntInfNorm (ysMask j) < rlweZkpokZBound)
    (hSafeE : ∀ j, 2 * polyIntInfNorm e1 + polyIntInfNorm (yeMask j) < rlweZkpokZBound)
    (hFakeS : ∀ j, polyIntInfNorm (zsFake j) < rlweZkpokZBound)
    (hFakeE : ∀ j, polyIntInfNorm (zeFake j) < rlweZkpokZBound) :
    verifyJointOrSigma stmt
      (buildHonestJointOrTranscript stmt branch sR e1 ysMask yeMask uFake zsFake zeFake) = true :=
  honestJointOrTranscriptWithRo_accepts (cshake256Xof (4 * rlweZkpokReps) rlweZkpokDomain)
    stmt branch sR e1 ysMask yeMask uFake zsFake zeFake hStmt hRel hSafeS hSafeE hFakeS hFakeE

theorem honestJointOrTranscriptPq13_accepts (stmt : RlweOrStatement) (branch : Bool)
    (sR e1 : PolyInt 1024)
    (ysMask yeMask : Fin rlweZkpokPqReps → PolyInt 1024)
    (uFake : Fin rlweZkpokPqReps → BitVec 11)
    (zsFake zeFake : Fin rlweZkpokPqReps → PolyInt 1024)
    (hStmt : checkRlweOrStatementValid stmt = true)
    (hRel : CommRingOps.add (CommRingOps.mul stmt.a (polyIntToRq sR)) (polyIntToRq e1) =
      stmt.branchPk branch)
    (hSafeS : ∀ j, 2 * polyIntInfNorm sR + polyIntInfNorm (ysMask j) < rlweZkpokZBound)
    (hSafeE : ∀ j, 2 * polyIntInfNorm e1 + polyIntInfNorm (yeMask j) < rlweZkpokZBound)
    (hFakeS : ∀ j, polyIntInfNorm (zsFake j) < rlweZkpokZBound)
    (hFakeE : ∀ j, polyIntInfNorm (zeFake j) < rlweZkpokZBound) :
    verifyJointOrSigmaPq13 stmt
      (buildHonestJointOrTranscriptPq13 stmt branch sR e1 ysMask yeMask uFake zsFake zeFake) = true :=
  honestJointOrTranscriptWithRo_accepts (cshake256Xof (4 * rlweZkpokPqReps) rlweZkpokDomain)
    stmt branch sR e1 ysMask yeMask uFake zsFake zeFake hStmt hRel hSafeS hSafeE hFakeS hFakeE

/-- Canonical inhabited OR-Sigma statement (`a = 1, tCrs = 1, pk0 = 1`). -/
def sampleRlweOrStatement : RlweOrStatement where
  crsCoin := List.replicate 32 0x11
  sessionId := List.replicate 32 0x22
  senderId := 0
  receiverId := 1
  otIdx := 0
  a := CommRingOps.one
  tCrs := CommRingOps.one
  pk0 := CommRingOps.one

def sampleUnitPolyInt : PolyInt 1024 := fun k => if k.val = 0 then 1 else 0
def sampleZeroPolyInt : PolyInt 1024 := fun _ => 0

private theorem sampleUnitPolyInt_toRq : polyIntToRq sampleUnitPolyInt = CommRingOps.one := by
  funext k; unfold polyIntToRq sampleUnitPolyInt
  change Zq12289.ofInt (if k.val = 0 then 1 else 0) =
    (if k.val = 0 then CommRingOps.one else CommRingOps.zero)
  split <;> rfl

private theorem sampleZeroPolyInt_toRq : polyIntToRq sampleZeroPolyInt = CommRingOps.zero := by
  funext _; rfl

private theorem sampleUnitPolyInt_infNorm_le : polyIntInfNorm sampleUnitPolyInt ≤ 1 := by
  rw [polyIntInfNorm_le_iff]; intro k; unfold sampleUnitPolyInt; split <;> decide

private theorem sampleZeroPolyInt_infNorm_eq : polyIntInfNorm sampleZeroPolyInt = 0 := by
  have hLe : polyIntInfNorm sampleZeroPolyInt ≤ 0 := by
    rw [polyIntInfNorm_le_iff]; intro _; unfold sampleZeroPolyInt; decide
  omega

private theorem polyRq1024_one_ne_zero : (CommRingOps.one : PolyRq1024) ≠ CommRingOps.zero := by
  intro hEq
  have h0 := congrFun hEq ⟨0, by decide⟩
  revert h0; decide

private theorem sampleRlweOrStatement_valid : checkRlweOrStatementValid sampleRlweOrStatement = true := by
  have hOneFalse : polyRqEq (CommRingOps.one : PolyRq1024) CommRingOps.zero = false :=
    (polyRqEq_eq_false_iff _ _).mpr polyRq1024_one_ne_zero
  unfold checkRlweOrStatementValid sampleRlweOrStatement
  dsimp only
  rw [hOneFalse]
  decide

/-- Concrete inhabited honest OR-Sigma transcript under production `cSHAKE256`. -/
def sampleHonestJointOrTranscript : JointOrSigmaTranscript :=
  buildHonestJointOrTranscript sampleRlweOrStatement false
    sampleUnitPolyInt sampleZeroPolyInt
    (fun _ => sampleUnitPolyInt) (fun _ => sampleZeroPolyInt)
    (fun _ => 0#11)
    (fun _ => sampleZeroPolyInt) (fun _ => sampleZeroPolyInt)

/-- **Inhabitedness Witness for `verifyJointOrSigma` & `jointOrSigma_extract_witness` (`inhabited_jointOrSigma_and_extractor`)**:
    Both production `verifyJointOrSigma` (`cSHAKE256`) and the 2-special soundness extractor
    `jointOrSigma_extract_witness` are constructively inhabited (non-vacuous). -/
theorem inhabited_jointOrSigma_and_extractor :
    verifyJointOrSigma sampleRlweOrStatement sampleHonestJointOrTranscript = true ∧
    Nonempty (Σ (ro ro' : List UInt8 → List UInt8) (tr tr' : JointOrSigmaTranscript),
      ExtractedJointOrWitness sampleRlweOrStatement ro ro' tr tr') := by
  have hRel : CommRingOps.add
      (CommRingOps.mul sampleRlweOrStatement.a (polyIntToRq sampleUnitPolyInt))
      (polyIntToRq sampleZeroPolyInt) = sampleRlweOrStatement.branchPk false := by
    rw [sampleUnitPolyInt_toRq, sampleZeroPolyInt_toRq]
    unfold sampleRlweOrStatement RlweOrStatement.branchPk
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [LawfulCommRing.mul_one, LawfulCommRing.add_zero]
  have hSafeS : ∀ _ : Fin rlweZkpokReps,
      2 * polyIntInfNorm sampleUnitPolyInt + polyIntInfNorm sampleUnitPolyInt < rlweZkpokZBound := by
    intro _; have := sampleUnitPolyInt_infNorm_le; unfold rlweZkpokZBound; omega
  have hSafeE : ∀ _ : Fin rlweZkpokReps,
      2 * polyIntInfNorm sampleZeroPolyInt + polyIntInfNorm sampleZeroPolyInt < rlweZkpokZBound := by
    intro _; rw [sampleZeroPolyInt_infNorm_eq]; decide
  have hFake : ∀ _ : Fin rlweZkpokReps, polyIntInfNorm sampleZeroPolyInt < rlweZkpokZBound := by
    intro _; rw [sampleZeroPolyInt_infNorm_eq]; decide
  refine ⟨honestJointOrTranscript_accepts sampleRlweOrStatement false
      sampleUnitPolyInt sampleZeroPolyInt
      (fun _ => sampleUnitPolyInt) (fun _ => sampleZeroPolyInt)
      (fun _ => 0#11) (fun _ => sampleZeroPolyInt) (fun _ => sampleZeroPolyInt)
      sampleRlweOrStatement_valid hRel hSafeS hSafeE hFake hFake, ?_⟩
  let ro0 : List UInt8 → List UInt8 := fun _ => encodeNatLeBytes 4 0 ++ List.replicate 48 0
  let ro1 : List UInt8 → List UInt8 := fun _ => encodeNatLeBytes 4 1 ++ List.replicate 48 0
  let tr0 := buildHonestJointOrTranscriptWithRoGen rlweZkpokReps ro0
    sampleRlweOrStatement false sampleUnitPolyInt sampleZeroPolyInt
    (fun _ => sampleUnitPolyInt) (fun _ => sampleZeroPolyInt)
    (fun _ => 0#11) (fun _ => sampleZeroPolyInt) (fun _ => sampleZeroPolyInt)
  let tr1 := buildHonestJointOrTranscriptWithRoGen rlweZkpokReps ro1
    sampleRlweOrStatement false sampleUnitPolyInt sampleZeroPolyInt
    (fun _ => sampleUnitPolyInt) (fun _ => sampleZeroPolyInt)
    (fun _ => 0#11) (fun _ => sampleZeroPolyInt) (fun _ => sampleZeroPolyInt)
  have hAcc0 := honestJointOrTranscriptWithRo_accepts ro0 sampleRlweOrStatement false
    sampleUnitPolyInt sampleZeroPolyInt
    (fun _ => sampleUnitPolyInt) (fun _ => sampleZeroPolyInt)
    (fun _ => 0#11) (fun _ => sampleZeroPolyInt) (fun _ => sampleZeroPolyInt)
    sampleRlweOrStatement_valid hRel hSafeS hSafeE hFake hFake
  have hAcc1 := honestJointOrTranscriptWithRo_accepts ro1 sampleRlweOrStatement false
    sampleUnitPolyInt sampleZeroPolyInt
    (fun _ => sampleUnitPolyInt) (fun _ => sampleZeroPolyInt)
    (fun _ => 0#11) (fun _ => sampleZeroPolyInt) (fun _ => sampleZeroPolyInt)
    sampleRlweOrStatement_valid hRel hSafeS hSafeE hFake hFake
  have hNe : hashRlweZkpokJointChallengesWithRo rlweZkpokReps ro0 sampleRlweOrStatement.crsCoin
        sampleRlweOrStatement.sessionId sampleRlweOrStatement.senderId sampleRlweOrStatement.receiverId
        sampleRlweOrStatement.otIdx sampleRlweOrStatement.pk0 sampleRlweOrStatement.tCrs tr0.comms ≠
      hashRlweZkpokJointChallengesWithRo rlweZkpokReps ro1 sampleRlweOrStatement.crsCoin
        sampleRlweOrStatement.sessionId sampleRlweOrStatement.senderId sampleRlweOrStatement.receiverId
        sampleRlweOrStatement.otIdx sampleRlweOrStatement.pk0 sampleRlweOrStatement.tCrs tr1.comms := by
    intro hEq
    have h0 := congrFun hEq ⟨0, by decide⟩
    unfold hashRlweZkpokJointChallengesWithRo decodeChal11Stream rlweZkpokReps at h0
    dsimp only [ro0, ro1] at h0
    have hTake0 : (encodeNatLeBytes 4 0 ++ List.replicate 48 0).take 4 = encodeNatLeBytes 4 0 := by
      have := encodeNatLeBytes_length 4 0
      rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
    have hTake1 : (encodeNatLeBytes 4 1 ++ List.replicate 48 0).take 4 = encodeNatLeBytes 4 1 := by
      have := encodeNatLeBytes_length 4 1
      rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
    rw [hTake0, hTake1,
        decodeNatLeBytes_encodeNatLeBytes 4 0 (by decide),
        decodeNatLeBytes_encodeNatLeBytes 4 1 (by decide)] at h0
    revert h0; decide
  exact ⟨⟨ro0, ro1, tr0, tr1,
    jointOrSigma_extract_witness sampleRlweOrStatement ro0 ro1 tr0 tr1 rfl hNe hAcc0 hAcc1⟩⟩

/-- **`#tooth` Mutation Sensitivity of `verifyJointOrSigma` (`tooth_verifyJointOrSigma_rejects_tampering`, `C0-2`)**:
    Starting from an honest accepting transcript `sampleHonestJointOrTranscript` under production
    `cSHAKE256("QSAG.OT.RLWE.ZKPOK/v3")`:
    1. **Tampered `pk0`** (`pk0' = pk0 + 1`): rejected (`verifyJointOrSigma = false`).
    2. **Tampered `comms`** (corrupting `(comms 0).1` by `+ 1`): rejected (`verifyJointOrSigma = false`).
    3. **Tampered `chal0 ^^^ chal1`** (flipping `chal0 0 ^^^ 1#11` without re-proving):
       rejected (`verifyJointOrSigma = false`).
    4. **Out-of-box response** (`z = 3070`, the excluded upper endpoint of `[-3070, 3070)`): rejected
       (`verifyJointOrSigma = false`). -/
theorem tooth_verifyJointOrSigma_rejects_tampering :
    let stmt := sampleRlweOrStatement
    let tr := sampleHonestJointOrTranscript
    let stmtBadPk0 := { stmt with pk0 := CommRingOps.add stmt.pk0 CommRingOps.one }
    let trBadComms := { tr with comms := fun j =>
      if j.val = 0 then (CommRingOps.add (tr.comms j).1 CommRingOps.one, (tr.comms j).2) else tr.comms j }
    let trBadChal := { tr with chal0 := fun j => if j.val = 0 then tr.chal0 j ^^^ 1#11 else tr.chal0 j }
    let trBadBound := { tr with zs0 := fun j => if j.val = 0 then (fun _ => 3070) else tr.zs0 j }
    verifyJointOrSigma stmt tr = true ∧
    verifyJointOrSigma stmtBadPk0 tr = false ∧
    verifyJointOrSigma stmt trBadComms = false ∧
    verifyJointOrSigma stmt trBadChal = false ∧
    verifyJointOrSigma stmt trBadBound = false := by
  intro stmt tr stmtBadPk0 trBadComms trBadChal trBadBound
  have hAcc : verifyJointOrSigma stmt tr = true := inhabited_jointOrSigma_and_extractor.1
  have hRep0 : (recomputeJointOrRepComm stmt tr ⟨0, by decide⟩).1 = (tr.comms ⟨0, by decide⟩).1 := by
    unfold verifyJointOrSigma verifyJointOrSigmaWithRoGen at hAcc
    simp only [Bool.and_eq_true] at hAcc
    have h0 := (allFin_eq_true_iff _).mp hAcc.2 ⟨0, by decide⟩
    unfold verifyJointOrRepGen at h0
    simp only [Bool.and_eq_true, polyRqEq_iff] at h0
    exact h0.1.2.1
  -- 1. Tampered `pk0`: `w0Exp` shifts by `-d(chal0 0) * 1`, which is non-zero by `polyRqFromChal11_ne_zero`!
  have hBadPk0 : verifyJointOrSigma stmtBadPk0 tr = false := by
    unfold verifyJointOrSigma verifyJointOrSigmaWithRoGen
    cases hc : checkRlweOrStatementValid stmtBadPk0
    · rfl
    · simp only [Bool.true_and]
      apply allFin_eq_false_of_false ⟨0, by decide⟩
      unfold verifyJointOrRepGen
      have hNeW0 : (recomputeJointOrRepComm stmtBadPk0 tr ⟨0, by decide⟩).1 ≠ (tr.comms ⟨0, by decide⟩).1 := by
        rw [← hRep0]
        unfold recomputeJointOrRepComm
        dsimp only [stmtBadPk0]
        intro hEq
        have hChalNz := polyRqFromChal11_ne_zero (tr.chal0 ⟨0, by decide⟩)
        apply hChalNz
        rw [LawfulCommRing.left_distrib, LawfulCommRing.mul_one] at hEq
        funext k
        have hk := congrFun hEq k
        let X := CommRingOps.add (CommRingOps.mul stmt.a (polyIntToRq (tr.zs0 ⟨0, by decide⟩)))
          (polyIntToRq (tr.ze0 ⟨0, by decide⟩)) k
        let D0 := CommRingOps.mul (polyRqFromChal11 (tr.chal0 ⟨0, by decide⟩)) stmt.pk0 k
        let D1 := polyRqFromChal11 (tr.chal0 ⟨0, by decide⟩) k
        change CommRingOps.sub X (CommRingOps.add D0 D1) = CommRingOps.sub X D0 at hk
        show D1 = CommRingOps.zero
        rw [← Zq12289.ofInt_natVal X, ← Zq12289.ofInt_natVal D0, ← Zq12289.ofInt_natVal D1] at hk
        rw [← Zq12289.ofInt_natVal D1, ← Zq12289.ofInt_zero]
        simp only [← Zq12289.ofInt_add, ← Zq12289.ofInt_sub] at hk
        have hv := congrArg Zq12289.val hk
        have hLt := D1.isLt
        simp only [Zq12289.ofInt] at hv ⊢
        apply Zq12289.ext
        dsimp only
        omega
      have hFalse := (polyRqEq_eq_false_iff _ _).mpr hNeW0
      dsimp only
      rw [hFalse]
      simp
  -- 2. Tampered `comms` (`+ 1` at rep 0): `w0Exp = (tr.comms 0).1 ≠ (tr.comms 0).1 + 1`!
  have hBadComms : verifyJointOrSigma stmt trBadComms = false := by
    unfold verifyJointOrSigma verifyJointOrSigmaWithRoGen
    cases hc : checkRlweOrStatementValid stmt
    · rfl
    · simp only [Bool.true_and]
      apply allFin_eq_false_of_false ⟨0, by decide⟩
      unfold verifyJointOrRepGen
      have hSameRecomp : (recomputeJointOrRepComm stmt trBadComms ⟨0, by decide⟩).1 =
          (tr.comms ⟨0, by decide⟩).1 := hRep0
      have hNe : (recomputeJointOrRepComm stmt trBadComms ⟨0, by decide⟩).1 ≠
          (trBadComms.comms ⟨0, by decide⟩).1 := by
        rw [hSameRecomp]
        dsimp only [trBadComms]
        simp only [↓reduceIte]
        intro hEq
        have hk0 := congrFun hEq ⟨0, by decide⟩
        have hVal := congrArg Zq12289.val hk0
        have hLt := ((tr.comms ⟨0, by decide⟩).1 ⟨0, by decide⟩).isLt
        change ((tr.comms ⟨0, by decide⟩).1 ⟨0, by decide⟩).val =
          (((tr.comms ⟨0, by decide⟩).1 ⟨0, by decide⟩).val + 1) % 12289 at hVal
        omega
      have hFalse := (polyRqEq_eq_false_iff _ _).mpr hNe
      dsimp only
      rw [hFalse]
      simp
  -- 4. Tampered `chal0 ^^^ chal1` (`chal0 0 ^^^ 1#11`): `w0Exp` shifts by `-((d(u') - d(u)) * pk0) ≠ 0`!
  have hBadChal : verifyJointOrSigma stmt trBadChal = false := by
    unfold verifyJointOrSigma verifyJointOrSigmaWithRoGen
    cases hc : checkRlweOrStatementValid stmt
    · rfl
    · simp only [Bool.true_and]
      apply allFin_eq_false_of_false ⟨0, by decide⟩
      unfold verifyJointOrRepGen
      have hU0Ne : trBadChal.chal0 ⟨0, by decide⟩ ≠ tr.chal0 ⟨0, by decide⟩ := by
        dsimp only [trBadChal]
        simp only [↓reduceIte]
        intro hEq
        have hBit := congrArg (fun x : BitVec 11 => x.getLsbD 0) hEq
        simp only [BitVec.getLsbD_xor] at hBit
        have hb1 : (1#11).getLsbD 0 = true := by decide
        rw [hb1] at hBit
        cases hb : (tr.chal0 ⟨0, by decide⟩).getLsbD 0 <;> rw [hb] at hBit <;> cases hBit
      have hNeW0 : (recomputeJointOrRepComm stmt trBadChal ⟨0, by decide⟩).1 ≠
          (trBadChal.comms ⟨0, by decide⟩).1 := by
        have hTarget : (trBadChal.comms ⟨0, by decide⟩).1 =
            (recomputeJointOrRepComm stmt tr ⟨0, by decide⟩).1 := hRep0.symm
        rw [hTarget]
        unfold recomputeJointOrRepComm
        dsimp only [trBadChal, stmt, sampleRlweOrStatement]
        simp only [↓reduceIte, LawfulCommRing.mul_one]
        intro hEq
        obtain ⟨hDiffNz, _, _⟩ := chal11_diff_nonzero_short_and_invertible hU0Ne
        apply hDiffNz
        rw [polyIntToRq_sub]
        funext k
        have hk := congrFun hEq k
        let X := CommRingOps.add
          (CommRingOps.mul CommRingOps.one (polyIntToRq (tr.zs0 ⟨0, by decide⟩)))
          (polyIntToRq (tr.ze0 ⟨0, by decide⟩)) k
        let D' := polyRqFromChal11 (tr.chal0 ⟨0, by decide⟩ ^^^ 1#11) k
        let D := polyRqFromChal11 (tr.chal0 ⟨0, by decide⟩) k
        change CommRingOps.sub X D' = CommRingOps.sub X D at hk
        show CommRingOps.sub D' D = CommRingOps.zero
        rw [← Zq12289.ofInt_natVal X, ← Zq12289.ofInt_natVal D', ← Zq12289.ofInt_natVal D] at hk
        rw [← Zq12289.ofInt_natVal D', ← Zq12289.ofInt_natVal D, ← Zq12289.ofInt_zero]
        simp only [← Zq12289.ofInt_sub] at hk ⊢
        have hv := congrArg Zq12289.val hk
        simp only [Zq12289.ofInt] at hv ⊢
        apply Zq12289.ext
        dsimp only
        omega
      have hFalse := (polyRqEq_eq_false_iff _ _).mpr hNeW0
      dsimp only
      rw [hFalse]
      simp
  -- 5. Out-of-box response (`z = 3070`): `boundsOk = false`.
  have hBadBound : verifyJointOrSigma stmt trBadBound = false := by
    unfold verifyJointOrSigma verifyJointOrSigmaWithRoGen
    cases hc : checkRlweOrStatementValid stmt
    · rfl
    · simp only [Bool.true_and]
      apply allFin_eq_false_of_false ⟨0, by decide⟩
      unfold verifyJointOrRepGen
      have hDecFalse : polyIntInZkpokBox (trBadBound.zs0 ⟨0, by decide⟩) = false := by
        cases hb : polyIntInZkpokBox (trBadBound.zs0 ⟨0, by decide⟩)
        · rfl
        · have h0 := (polyIntInZkpokBox_iff _).mp hb ⟨0, by decide⟩
          dsimp only [trBadBound] at h0
          simp only [↓reduceIte] at h0
          unfold rlweZkpokZBound at h0
          omega
      dsimp only
      rw [hDecFalse]
      simp
  exact ⟨hAcc, hBadPk0, hBadComms, hBadChal, hBadBound⟩

/-! ### 2.1b `#tooth` Independent vs. Joint Fiat-Shamir Challenge Grinding (`P0-11` & `G0-D` QROM) -/

/-- Grinding query cost under joint 7-commitment hashing `H(pk0, tCrs, C_0..C_6)` (`2^(7*m)`). -/
def jointChallengeGrindCost (m : Nat) : Nat := 2 ^ (7 * m)

/-- Grinding query cost when each repetition `j ∈ Fin 7` hashes `H(pk0, tCrs, j, C_j)` independently (`7 * 2^m`). -/
def indepChallengeGrindCost (m : Nat) : Nat := 7 * (2 ^ m)

/-- Bit-weighted independent grinding cost `k * 2^(k/7)` (`(7 * m) * 2^m`). -/
def bitWeightedIndepGrindCost (m : Nat) : Nat := (7 * m) * (2 ^ m)

/-- Arithmetic square-root search scale; not a QROM security lower bound `2^((R * m) / 2)` (`G0-D`). -/
def groverJointChallengeGrindCost (R m : Nat) : Nat := 2 ^ ((R * m) / 2)

/-- Independent per-repetition grinding query cost across `R` slots (`R * 2^m`). -/
def indepChallengeGrindCostGen (R m : Nat) : Nat := R * (2 ^ m)

private theorem seven_mul_lt_pow_six : ∀ m : Nat, 1 ≤ m → 7 * m < 2 ^ (6 * m)
  | 0, hm => by omega
  | 1, _ => by decide
  | m + 2, _ => by
    have ih := seven_mul_lt_pow_six (m + 1) (by omega)
    have hPow : 2 ^ (6 * (m + 2)) = 64 * 2 ^ (6 * (m + 1)) := by
      have hAdd : 6 * (m + 2) = 6 * (m + 1) + 6 := by omega
      rw [hAdd, Nat.pow_add, Nat.mul_comm]
    omega

/-- Arithmetic comparison of independent and joint challenge search spaces. The 20-bit
    clauses describe the historical profile. The production 13-by-11 profile has square-root
    exponent floor 71, below 128. These identities are not a QROM reduction. -/
theorem tooth_independent_challenges_drop_grinding_cost (m : Nat) (hm : 1 ≤ m) :
    indepChallengeGrindCost m ≤ bitWeightedIndepGrindCost m ∧
    bitWeightedIndepGrindCost m < jointChallengeGrindCost m ∧
    indepChallengeGrindCost 20 < 2 ^ 23 ∧
    bitWeightedIndepGrindCost 20 < 2 ^ 28 ∧
    jointChallengeGrindCost 20 = 2 ^ 140 ∧
    groverJointChallengeGrindCost rlweZkpokClassicalReps 20 = 2 ^ 70 ∧
    groverJointChallengeGrindCost rlweZkpokClassicalReps 20 < 2 ^ 128 ∧
    groverJointChallengeGrindCost rlweZkpokReps 11 = 2 ^ 71 ∧
    groverJointChallengeGrindCost rlweZkpokReps 11 < 2 ^ 128 ∧
    indepChallengeGrindCostGen rlweZkpokReps 20 < 2 ^ 24 := by
  unfold indepChallengeGrindCost bitWeightedIndepGrindCost jointChallengeGrindCost
    groverJointChallengeGrindCost indepChallengeGrindCostGen rlweZkpokClassicalReps rlweZkpokReps
  have h1 : 7 * 2 ^ m ≤ (7 * m) * 2 ^ m := by
    apply Nat.mul_le_mul_right
    omega
  have h2 : (7 * m) * 2 ^ m < 2 ^ (7 * m) := by
    have hSplit : 7 * m = 6 * m + m := by omega
    conv => rhs; rw [hSplit, Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right (seven_mul_lt_pow_six m hm) (Nat.two_pow_pos m)
  exact ⟨h1, h2, by decide, by decide, rfl, rfl, by decide, rfl, by decide, by decide⟩

/-! ### 2.2 Discrete-Gaussian Rejection Sampling Statistical HVZK Bound + `#tooth` -/

/-- Conditional finite-weight rejection model over candidate response space `Fin Z`.
    The cancellation field is an assumption, not a verified instance of the Rust Q192 sampler.
    Inside `inSafeBox z = true` (`‖z‖_∞ < B - B_s`), Lyubashevsky rejection sampling accepts
    shifted sample `y = z - v` with numerator `accNum z` such that `srcWeight z * accNum z = targetWeight z * normConst`,
    eliminating all dependence on the secret witness shift `v`! -/
structure GaussianRejWitnessInstance (Z : Nat) where
  targetWeight : Fin Z → Nat
  inSafeBox : Fin Z → Bool
  srcWeight : Fin Z → Nat
  accNum : Fin Z → Nat
  normConst : Nat
  normConst_pos : 0 < normConst
  safe_box_cancel : ∀ z : Fin Z, inSafeBox z = true →
    srcWeight z * accNum z = targetWeight z * normConst

/-- Unnormalized accepted response weight emitted by one rejection-sampling trial. -/
def GaussianRejWitnessInstance.acceptedWeight {Z : Nat}
    (inst : GaussianRejWitnessInstance Z) (z : Fin Z) : Nat :=
  if inst.inSafeBox z then inst.srcWeight z * inst.accNum z else 0

/-- Safe-box target mass $\sum_{z \in \mathsf{Safe}} \rho_\sigma(z)$. -/
def gaussianSafeMass {Z : Nat} (targetWeight : Fin Z → Nat) (inSafeBox : Fin Z → Bool) : Nat :=
  natFinSum Z (fun z => if inSafeBox z then targetWeight z else 0)

/-- Tail mass $\sum_{z \notin \mathsf{Safe}} \rho_\sigma(z)$ outside the rejection safe box. -/
def gaussianTailMass {Z : Nat} (targetWeight : Fin Z → Nat) (inSafeBox : Fin Z → Bool) : Nat :=
  natFinSum Z (fun z => if inSafeBox z then 0 else targetWeight z)

theorem gaussianTotalMass_eq_safe_add_tail {Z : Nat}
    (targetWeight : Fin Z → Nat) (inSafeBox : Fin Z → Bool) :
    natFinSum Z targetWeight =
      gaussianSafeMass targetWeight inSafeBox + gaussianTailMass targetWeight inSafeBox := by
  unfold gaussianSafeMass gaussianTailMass
  rw [← natFinSum_add]
  apply natFinSum_congr
  intro z
  cases inSafeBox z <;> simp

/-- **Exact Conditional Witness-Independence (`gaussian_rej_conditional_witness_independent`)**:
    For ANY two secret witnesses `(w₁, w₂)` sharing `(targetWeight, inSafeBox)`, cross-multiplied
    accepted response weights are **pointwise identical** (`w₁.acceptedWeight z * w₂.normConst =
    w₂.acceptedWeight z * w₁.normConst` for every `z : Fin Z`), yielding **zero** conditional
    statistical distance between any two honest witnesses! -/
theorem gaussian_rej_conditional_witness_independent {Z : Nat}
    (w₁ w₂ : GaussianRejWitnessInstance Z)
    (hTarget : w₁.targetWeight = w₂.targetWeight)
    (hBox : w₁.inSafeBox = w₂.inSafeBox) (z : Fin Z) :
    w₁.acceptedWeight z * w₂.normConst = w₂.acceptedWeight z * w₁.normConst := by
  unfold GaussianRejWitnessInstance.acceptedWeight
  rw [hBox]
  cases hSafe : w₂.inSafeBox z
  · simp
  · simp only [↓reduceIte]
    have hSafe1 : w₁.inSafeBox z = true := (congrFun hBox z).trans hSafe
    rw [w₁.safe_box_cancel z hSafe1, w₂.safe_box_cancel z hSafe, hTarget]
    exact Nat.mul_right_comm (w₂.targetWeight z) w₁.normConst w₂.normConst

/-- **Discrete-Gaussian Rejection Sampling Statistical HVZK Bound (`discrete_gaussian_rejection_hvzk_bound`)**:
    1. Conditioned on acceptance (`0 < safeMass`), the prover's accepted distribution equals the
       box-restricted target Gaussian `z ↦ if inSafeBox z then targetWeight z else 0` independently of the secret witness.
    2. Comparing the normalized accepted distribution against the unclipped ideal Gaussian `targetWeight`
       (`totalMass = safeMass + tailMass`), the exact scaled $L_1$ statistical distance is
       `2 * safeMass * tailMass` (exact TV distance `tailMass / totalMass`), and across all `rlweZkpokReps = 13`
       OR-Sigma repetitions satisfies `ratLe (rlweZkpokReps * l1Single, 2 * safeMass * totalMass) (rlweZkpokReps * tailMass, totalMass)`! -/
theorem discrete_gaussian_rejection_hvzk_bound {Z : Nat}
    (w : GaussianRejWitnessInstance Z)
    (hSafePos : 0 < gaussianSafeMass w.targetWeight w.inSafeBox) :
    let safeMass := gaussianSafeMass w.targetWeight w.inSafeBox
    let tailMass := gaussianTailMass w.targetWeight w.inSafeBox
    let totalMass := natFinSum Z w.targetWeight
    let boxWeight := fun z : Fin Z => if w.inSafeBox z then w.targetWeight z else 0
    let l1Scaled := natFinSum Z (fun z => natDist (boxWeight z * totalMass) (w.targetWeight z * safeMass))
    (∀ z : Fin Z, w.acceptedWeight z = boxWeight z * w.normConst) ∧
    l1Scaled = 2 * safeMass * tailMass ∧
    ratLe (l1Scaled, 2 * safeMass * totalMass) (tailMass, totalMass) ∧
    ratLe (rlweZkpokReps * l1Scaled, 2 * safeMass * totalMass) (rlweZkpokReps * tailMass, totalMass) := by
  intro safeMass tailMass totalMass boxWeight l1Scaled
  have hPoint : ∀ z : Fin Z, w.acceptedWeight z = boxWeight z * w.normConst := by
    intro z
    unfold GaussianRejWitnessInstance.acceptedWeight
    dsimp only [boxWeight]
    cases hSafe : w.inSafeBox z
    · simp
    · simp only [↓reduceIte, w.safe_box_cancel z hSafe]
  have hTotEq : totalMass = safeMass + tailMass :=
    gaussianTotalMass_eq_safe_add_tail w.targetWeight w.inSafeBox
  have hTotPos : 0 < totalMass := by omega
  have hTermEq : ∀ z : Fin Z,
      natDist (boxWeight z * totalMass) (w.targetWeight z * safeMass) =
        (if w.inSafeBox z then w.targetWeight z else 0) * tailMass +
        (if w.inSafeBox z then 0 else w.targetWeight z) * safeMass := by
    intro z
    dsimp only [boxWeight]
    rw [hTotEq]
    cases hSafe : w.inSafeBox z
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_mul, Nat.zero_add]
      unfold natDist; split <;> omega
    · simp only [↓reduceIte, Nat.zero_mul, Nat.add_zero]
      unfold natDist
      rw [Nat.mul_add]
      split <;> omega
  have hL1Exact : l1Scaled = 2 * safeMass * tailMass := by
    dsimp only [l1Scaled]
    rw [natFinSum_congr hTermEq, natFinSum_add, natFinSum_mul_right, natFinSum_mul_right]
    change safeMass * tailMass + tailMass * safeMass = 2 * safeMass * tailMass
    rw [Nat.mul_comm tailMass safeMass, ← Nat.two_mul, Nat.mul_assoc]
  have hDenPos : 0 < 2 * safeMass * totalMass := Nat.mul_pos (by omega) hTotPos
  refine ⟨hPoint, hL1Exact, ?_, ?_⟩
  · unfold ratLe
    dsimp only
    refine ⟨hDenPos, hTotPos, ?_⟩
    rw [hL1Exact]
    simp only [Nat.mul_assoc, Nat.mul_left_comm]
    exact Nat.le_refl _
  · unfold ratLe
    dsimp only
    refine ⟨hDenPos, hTotPos, ?_⟩
    rw [hL1Exact]
    simp only [Nat.mul_assoc, Nat.mul_left_comm]
    exact Nat.le_refl _

/-- **`#tooth` Omitting Gaussian Rejection Weight Leaks Secret Witness (`tooth_omitting_rejection_leaks_witness_shift`)**:
    Without rejection weighting (`accNum = 1`), two distinct secret shifts (`v = 0` vs `v = 1`) over
    `Fin 3` produce distinct conditional response weights inside `inSafeBox`, directly leaking `v`! -/
theorem tooth_omitting_rejection_leaks_witness_shift :
    let inSafe : Fin 3 → Bool := fun z => decide (z.val ≤ 1)
    let rawShift0 : Fin 3 → Nat := fun z => if z.val = 0 then 4 else if z.val = 1 then 2 else 1
    let rawShift1 : Fin 3 → Nat := fun z => if z.val = 0 then 2 else if z.val = 1 then 4 else 2
    let mass0 := natFinSum 3 (fun z => if inSafe z then rawShift0 z else 0)
    let mass1 := natFinSum 3 (fun z => if inSafe z then rawShift1 z else 0)
    0 < mass0 ∧ 0 < mass1 ∧
    rawShift0 ⟨0, by decide⟩ * mass1 ≠ rawShift1 ⟨0, by decide⟩ * mass0 := by
  decide

/-! ### 2.3 Fujisaki-Okamoto (`FO`) Re-Encryption Check Soundness & `PartyMachine` -/

/-- Deterministic FO encryption coins `(r, e2, e3)` derived from `(branch, payload512)`. -/
structure RlweFoCoins where
  r : PolyInt 1024
  e2 : PolyInt 1024
  e3 : PolyInt 1024

/-- Deterministic Fujisaki-Okamoto branch encryption matching `rlwe_fo_encrypt_branch`. -/
def rlweFoEncrypt (a pkBranch : PolyRq1024) (payload : Fin 512 → Bool)
    (coins : RlweFoCoins) : PolyRq1024 × PolyRq1024 :=
  let u := CommRingOps.add (CommRingOps.mul a (polyIntToRq coins.r)) (polyIntToRq coins.e2)
  let v := CommRingOps.add
    (CommRingOps.add (CommRingOps.mul pkBranch (polyIntToRq coins.r)) (polyIntToRq coins.e3))
    (encodePayload512 payload)
  (u, v)

/-- Receiver state for one FO-checked Ring-LWE Base-OT (`consumed` enforces single-use decryption). -/
structure RlweFoReceiverState where
  a : PolyRq1024
  tCrs : PolyRq1024
  pk0 : PolyRq1024
  sR : PolyInt 1024
  choiceBit : Bool
  consumed : Bool

/-- Sender wire response `((u0, v0), (u1, v1))`. -/
structure RlweFoSenderMsg where
  u0 : PolyRq1024
  v0 : PolyRq1024
  u1 : PolyRq1024
  v1 : PolyRq1024

/-- Deterministic FO-checked Base-OT Receiver transition wrapped as a `SimulationSpine.PartyMachine`. -/
def rlweFoReceiverMachine (deriveCoins : Bool → (Fin 512 → Bool) → RlweFoCoins) :
    PartyMachine RlweFoReceiverState RlweFoSenderMsg (Fin 512 → Bool) :=
  PartyMachine.ofOption fun st msg =>
    if st.consumed then none
    else
      let u_c := if st.choiceBit then msg.u1 else msg.u0
      let v_c := if st.choiceBit then msg.v1 else msg.v0
      let diff := CommRingOps.sub v_c (CommRingOps.mul u_c (polyIntToRq st.sR))
      let decoded := decodePayload512 diff
      let pk_c := if st.choiceBit then CommRingOps.add st.pk0 st.tCrs else st.pk0
      let (uExp, vExp) := rlweFoEncrypt st.a pk_c decoded (deriveCoins st.choiceBit decoded)
      if polyRqEq u_c uExp && polyRqEq v_c vExp then
        some ({ st with consumed := true }, decoded)
      else
        none

/-- **Fujisaki-Okamoto Re-Encryption Check Soundness & Honest Completeness (`fo_reencryption_soundness`)**:
    1. **Malicious-Sender Canonicality**: Whenever `rlweFoReceiverMachine` accepts `(st', out)` on an
       arbitrary adversarial message `msg`, the active ciphertext `(u_c, v_c)` is **forced** to equal
       the exact deterministic encryption `rlweFoEncrypt st.a pk_c out (deriveCoins st.choiceBit out)`
       (eliminating all out-of-range noise-flooding / key-dependent-abort ciphertexts), and `st'.consumed = true`.
    2. **Honest Zero-Failure Completeness**: When `deriveCoins` produces ternary coins (`‖·‖_∞ ≤ 1`) and
       Receiver holds ternary `(sR, e1)` (`‖·‖_∞ ≤ 1`) for `pk_c = a * sR + e1`, honest FO encryption
       of `(payload0, payload1)` is accepted with probability `1` and outputs `if choiceBit then payload1 else payload0`! -/
theorem fo_reencryption_soundness
    (deriveCoins : Bool → (Fin 512 → Bool) → RlweFoCoins) :
    (∀ (st st' : RlweFoReceiverState) (msg : RlweFoSenderMsg) (out : Fin 512 → Bool),
      (rlweFoReceiverMachine deriveCoins).step st msg = some (st', out) →
      let u_c := if st.choiceBit then msg.u1 else msg.u0
      let v_c := if st.choiceBit then msg.v1 else msg.v0
      let pk_c := if st.choiceBit then CommRingOps.add st.pk0 st.tCrs else st.pk0
      st.consumed = false ∧ st'.consumed = true ∧
      (u_c, v_c) = rlweFoEncrypt st.a pk_c out (deriveCoins st.choiceBit out)) ∧
    (∀ (a tCrs : PolyRq1024) (choiceBit : Bool) (sR e1 : PolyInt 1024)
       (payload0 payload1 : Fin 512 → Bool),
      polyIntInfNorm sR ≤ 1 → polyIntInfNorm e1 ≤ 1 →
      (∀ b p, polyIntInfNorm (deriveCoins b p).r ≤ 1 ∧
              polyIntInfNorm (deriveCoins b p).e2 ≤ 1 ∧
              polyIntInfNorm (deriveCoins b p).e3 ≤ 1) →
      let rlweSample := CommRingOps.add (CommRingOps.mul a (polyIntToRq sR)) (polyIntToRq e1)
      let pk0 := if choiceBit then CommRingOps.sub rlweSample tCrs else rlweSample
      let pk1 := CommRingOps.add pk0 tCrs
      let (u0, v0) := rlweFoEncrypt a pk0 payload0 (deriveCoins false payload0)
      let (u1, v1) := rlweFoEncrypt a pk1 payload1 (deriveCoins true payload1)
      let st : RlweFoReceiverState := ⟨a, tCrs, pk0, sR, choiceBit, false⟩
      let target := if choiceBit then payload1 else payload0
      (rlweFoReceiverMachine deriveCoins).step st ⟨u0, v0, u1, v1⟩ =
        some ({ st with consumed := true }, target)) := by
  constructor
  · intro st st' msg out hStep
    unfold rlweFoReceiverMachine PartyMachine.ofOption at hStep
    dsimp only at hStep
    cases hCons : st.consumed
    · rw [hCons] at hStep
      cases hc : st.choiceBit <;>
        simp only [hc, Bool.false_eq_true, ↓reduceIte] at hStep ⊢ <;>
        split at hStep
      · rename_i hCheck
        injection hStep with hPair
        injection hPair with hSt hOut
        subst hSt; subst hOut
        simp only [Bool.and_eq_true, polyRqEq_iff] at hCheck
        exact ⟨trivial, rfl, Prod.ext hCheck.1 hCheck.2⟩
      · cases hStep
      · rename_i hCheck
        injection hStep with hPair
        injection hPair with hSt hOut
        subst hSt; subst hOut
        simp only [Bool.and_eq_true, polyRqEq_iff] at hCheck
        exact ⟨trivial, rfl, Prod.ext hCheck.1 hCheck.2⟩
      · cases hStep
    · rw [hCons] at hStep; simp at hStep
  · intro a tCrs choiceBit sR e1 payload0 payload1 hsR he1 hTern
    intro rlweSample pk0 pk1
    let target := if choiceBit then payload1 else payload0
    let coins := deriveCoins choiceBit target
    have hC := hTern choiceBit target
    have hDec := rlwe1024_poly_ot_decrypt_correct a tCrs choiceBit sR e1 coins.r coins.e2 coins.e3
      payload0 payload1 hsR he1 hC.1 hC.2.1 hC.2.2
    unfold rlweFoReceiverMachine PartyMachine.ofOption
    dsimp only
    cases choiceBit
    · have hDec0 : decodePayload512 (CommRingOps.sub
          (rlweFoEncrypt a pk0 payload0 (deriveCoins false payload0)).2
          (CommRingOps.mul (rlweFoEncrypt a pk0 payload0 (deriveCoins false payload0)).1
            (polyIntToRq sR))) = payload0 := hDec
      simp only [Bool.false_eq_true, ↓reduceIte, hDec0, polyRqEq_self, Bool.and_self]
    · have hDec1 : decodePayload512 (CommRingOps.sub
          (rlweFoEncrypt a pk1 payload1 (deriveCoins true payload1)).2
          (CommRingOps.mul (rlweFoEncrypt a pk1 payload1 (deriveCoins true payload1)).1
            (polyIntToRq sR))) = payload1 := hDec
      have hPk1Def : CommRingOps.add pk0 tCrs = pk1 := rfl
      simp only [↓reduceIte, Bool.false_eq_true, hDec1, hPk1Def, polyRqEq_self, Bool.and_self]

/-- **The FO accept set is public (`fo_accept_iff_canonical`)**:
    for a receiver holding any ternary key `(sR, e1)` of its active public key `pk_c = a * sR + e1`, and
    ternary derived coins, the machine accepts an **arbitrary** sender message with output `out` if and
    only if the active ciphertext is the canonical encryption of `out` under `pk_c`. The right-hand side
    mentions only public data `(a, pk_c, deriveCoins)`: the inactive ciphertext is never inspected, and
    no sender message can make acceptance depend on the secret key. `fo_reencryption_soundness` gives
    only the forward direction; the converse is the decryption margin `2049 < 3072` applied to an
    adversarially chosen canonical ciphertext. -/
theorem fo_accept_iff_canonical
    (deriveCoins : Bool → (Fin 512 → Bool) → RlweFoCoins)
    (hTern : ∀ b p, polyIntInfNorm (deriveCoins b p).r ≤ 1 ∧
                    polyIntInfNorm (deriveCoins b p).e2 ≤ 1 ∧
                    polyIntInfNorm (deriveCoins b p).e3 ≤ 1)
    (a tCrs pk0 : PolyRq1024) (choiceBit : Bool) (sR e1 : PolyInt 1024)
    (hsR : polyIntInfNorm sR ≤ 1) (he1 : polyIntInfNorm e1 ≤ 1)
    (hKey : (if choiceBit then CommRingOps.add pk0 tCrs else pk0) =
      CommRingOps.add (CommRingOps.mul a (polyIntToRq sR)) (polyIntToRq e1))
    (msg : RlweFoSenderMsg) (out : Fin 512 → Bool) :
    (∃ st' : RlweFoReceiverState,
      (rlweFoReceiverMachine deriveCoins).step ⟨a, tCrs, pk0, sR, choiceBit, false⟩ msg =
        some (st', out)) ↔
      ((if choiceBit then msg.u1 else msg.u0), (if choiceBit then msg.v1 else msg.v0)) =
        rlweFoEncrypt a (if choiceBit then CommRingOps.add pk0 tCrs else pk0) out
          (deriveCoins choiceBit out) := by
  constructor
  · rintro ⟨st', hStep⟩
    exact ((fo_reencryption_soundness deriveCoins).1 _ st' msg out hStep).2.2
  · intro hCanon
    refine ⟨⟨a, tCrs, pk0, sR, choiceBit, true⟩, ?_⟩
    have hC := hTern choiceBit out
    have hDecKey := rlwe1024_poly_ot_decrypt_correct a CommRingOps.zero false sR e1
      (deriveCoins choiceBit out).r (deriveCoins choiceBit out).e2 (deriveCoins choiceBit out).e3
      out out hsR he1 hC.1 hC.2.1 hC.2.2
    unfold rlweFoReceiverMachine PartyMachine.ofOption
    dsimp only
    cases choiceBit
    · simp only [Bool.false_eq_true, ↓reduceIte] at hCanon hKey ⊢
      have hU := congrArg Prod.fst hCanon
      have hV := congrArg Prod.snd hCanon
      dsimp only at hU hV
      have hDec : decodePayload512
          (CommRingOps.sub msg.v0 (CommRingOps.mul msg.u0 (polyIntToRq sR))) = out := by
        rw [hU, hV, hKey]; exact hDecKey
      simp only [hDec, ← hU, ← hV, polyRqEq_self, Bool.and_self, ↓reduceIte]
    · simp only [↓reduceIte] at hCanon hKey ⊢
      have hU := congrArg Prod.fst hCanon
      have hV := congrArg Prod.snd hCanon
      dsimp only at hU hV
      have hDec : decodePayload512
          (CommRingOps.sub msg.v1 (CommRingOps.mul msg.u1 (polyIntToRq sR))) = out := by
        rw [hU, hV, hKey]; exact hDecKey
      simp only [hDec, ← hU, ← hV, polyRqEq_self, Bool.and_self, Bool.false_eq_true, ↓reduceIte]

/-- **No key-dependent abort (`fo_accept_key_independent`)**:
    two receivers holding different ternary keys `(sR, e1)`, `(sR', e1')` of the same public key accept
    exactly the same sender messages with exactly the same outputs. A malicious sender therefore learns
    nothing about which short key the receiver holds from the accept/abort bit. -/
theorem fo_accept_key_independent
    (deriveCoins : Bool → (Fin 512 → Bool) → RlweFoCoins)
    (hTern : ∀ b p, polyIntInfNorm (deriveCoins b p).r ≤ 1 ∧
                    polyIntInfNorm (deriveCoins b p).e2 ≤ 1 ∧
                    polyIntInfNorm (deriveCoins b p).e3 ≤ 1)
    (a tCrs pk0 : PolyRq1024) (choiceBit : Bool) (sR e1 sR' e1' : PolyInt 1024)
    (hsR : polyIntInfNorm sR ≤ 1) (he1 : polyIntInfNorm e1 ≤ 1)
    (hsR' : polyIntInfNorm sR' ≤ 1) (he1' : polyIntInfNorm e1' ≤ 1)
    (hKey : (if choiceBit then CommRingOps.add pk0 tCrs else pk0) =
      CommRingOps.add (CommRingOps.mul a (polyIntToRq sR)) (polyIntToRq e1))
    (hKey' : (if choiceBit then CommRingOps.add pk0 tCrs else pk0) =
      CommRingOps.add (CommRingOps.mul a (polyIntToRq sR')) (polyIntToRq e1'))
    (msg : RlweFoSenderMsg) (out : Fin 512 → Bool) :
    (∃ st' : RlweFoReceiverState,
      (rlweFoReceiverMachine deriveCoins).step ⟨a, tCrs, pk0, sR, choiceBit, false⟩ msg =
        some (st', out)) ↔
    (∃ st' : RlweFoReceiverState,
      (rlweFoReceiverMachine deriveCoins).step ⟨a, tCrs, pk0, sR', choiceBit, false⟩ msg =
        some (st', out)) :=
  (fo_accept_iff_canonical deriveCoins hTern a tCrs pk0 choiceBit sR e1 hsR he1 hKey msg out).trans
    (fo_accept_iff_canonical deriveCoins hTern a tCrs pk0 choiceBit sR' e1' hsR' he1' hKey' msg out).symm

/-- **Selective failure of one base OT (`fo_corrupted_branch_rejected_iff_chosen`)**:
    if the sender's branch-`badBranch` ciphertext is not a canonical encryption of any payload while
    the other branch carries a canonical one, a receiver holding a ternary key accepts exactly when its
    choice bit avoids the corrupted branch. The accept bit therefore equals the predicate
    `choiceBit ≠ badBranch`: one corrupted ciphertext leaks one choice bit and nothing about the key.
    Over `k` such OTs this is the event counted by `fo_cut_and_choose_selective_failure_bound` in
    `Qsag.Preprocessing` (one surviving choice vector out of `2^k`). -/
theorem fo_corrupted_branch_rejected_iff_chosen
    (deriveCoins : Bool → (Fin 512 → Bool) → RlweFoCoins)
    (hTern : ∀ b p, polyIntInfNorm (deriveCoins b p).r ≤ 1 ∧
                    polyIntInfNorm (deriveCoins b p).e2 ≤ 1 ∧
                    polyIntInfNorm (deriveCoins b p).e3 ≤ 1)
    (a tCrs pk0 : PolyRq1024) (choiceBit badBranch : Bool) (sR e1 : PolyInt 1024)
    (hsR : polyIntInfNorm sR ≤ 1) (he1 : polyIntInfNorm e1 ≤ 1)
    (hKey : (if choiceBit then CommRingOps.add pk0 tCrs else pk0) =
      CommRingOps.add (CommRingOps.mul a (polyIntToRq sR)) (polyIntToRq e1))
    (msg : RlweFoSenderMsg) (goodOut : Fin 512 → Bool)
    (hBad : ∀ out : Fin 512 → Bool,
      ((if badBranch then msg.u1 else msg.u0), (if badBranch then msg.v1 else msg.v0)) ≠
        rlweFoEncrypt a (if badBranch then CommRingOps.add pk0 tCrs else pk0) out
          (deriveCoins badBranch out))
    (hGood :
      ((if !badBranch then msg.u1 else msg.u0), (if !badBranch then msg.v1 else msg.v0)) =
        rlweFoEncrypt a (if !badBranch then CommRingOps.add pk0 tCrs else pk0) goodOut
          (deriveCoins (!badBranch) goodOut)) :
    (∃ (st' : RlweFoReceiverState) (out : Fin 512 → Bool),
      (rlweFoReceiverMachine deriveCoins).step ⟨a, tCrs, pk0, sR, choiceBit, false⟩ msg =
        some (st', out)) ↔ choiceBit ≠ badBranch := by
  constructor
  · rintro ⟨st', out, hStep⟩ hEq
    subst hEq
    exact hBad out ((fo_accept_iff_canonical deriveCoins hTern a tCrs pk0 choiceBit sR e1
      hsR he1 hKey msg out).mp ⟨st', hStep⟩)
  · intro hNe
    have hChoice : choiceBit = !badBranch := by
      cases choiceBit <;> cases badBranch <;> first | rfl | exact absurd rfl hNe
    subst hChoice
    obtain ⟨st', hStep⟩ := (fo_accept_iff_canonical deriveCoins hTern a tCrs pk0 (!badBranch) sR e1
      hsR he1 hKey msg goodOut).mpr hGood
    exact ⟨st', goodOut, hStep⟩

/-- **`#tooth` Passive RLWE Decryption Without FO Leaks Secret-Key Bits (`tooth_passive_rlwe_decrypt_without_fo_allows_key_dependent_abort`)**:
    A malicious sender crafting boundary ciphertext `u_mal = 1`, `v_mal = 3072` causes passive decryption
    `decodePayload512 (v_mal - u_mal * sR)` at index `0` to output `true` when `sR[0] = 0` (`3072 ∈ [3072, 9216)`)
    and `false` when `sR[0] = 1` (`3071 < 3072`) — directly leaking 1 bit of Receiver's secret key `sR` —
    whereas `rlweFoReceiverMachine` with ternary `deriveCoins` (`a = 0`, `‖e2‖_∞ ≤ 0` or `uExp = 0`) rejects `(u_mal, v_mal)`! -/
theorem tooth_passive_rlwe_decrypt_without_fo_allows_key_dependent_abort :
    let uMal : PolyRq1024 := CommRingOps.one
    let vMal : PolyRq1024 := fun k => if k.val = 0 then ⟨3072, by decide⟩ else CommRingOps.zero
    let sZero : PolyInt 1024 := fun _ => 0
    let sOne : PolyInt 1024 := fun k => if k.val = 0 then 1 else 0
    let zeroCoins : Bool → (Fin 512 → Bool) → RlweFoCoins := fun _ _ => ⟨sZero, sZero, sZero⟩
    let st0 : RlweFoReceiverState := ⟨CommRingOps.zero, CommRingOps.zero, CommRingOps.zero, sZero, false, false⟩
    let st1 : RlweFoReceiverState := ⟨CommRingOps.zero, CommRingOps.zero, CommRingOps.zero, sOne, false, false⟩
    polyIntInfNorm sZero ≤ 1 ∧ polyIntInfNorm sOne ≤ 1 ∧
    decodePayload512 (CommRingOps.sub vMal (CommRingOps.mul uMal (polyIntToRq sZero))) ⟨0, by decide⟩ = true ∧
    decodePayload512 (CommRingOps.sub vMal (CommRingOps.mul uMal (polyIntToRq sOne))) ⟨0, by decide⟩ = false ∧
    (rlweFoReceiverMachine zeroCoins).step st0 ⟨uMal, vMal, uMal, vMal⟩ = none ∧
    (rlweFoReceiverMachine zeroCoins).step st1 ⟨uMal, vMal, uMal, vMal⟩ = none := by
  intro uMal vMal sZero sOne zeroCoins st0 st1
  have hs0 : polyIntInfNorm sZero ≤ 1 := by rw [polyIntInfNorm_le_iff]; intro _; decide
  have hs1 : polyIntInfNorm sOne ≤ 1 := by rw [polyIntInfNorm_le_iff]; intro k; dsimp [sOne]; split <;> decide
  have hOneMul0 : CommRingOps.mul uMal (polyIntToRq sZero) = polyIntToRq sZero :=
    LawfulCommRing.one_mul _
  have hOneMul1 : CommRingOps.mul uMal (polyIntToRq sOne) = polyIntToRq sOne :=
    LawfulCommRing.one_mul _
  have hDec0 : decodePayload512 (CommRingOps.sub vMal (CommRingOps.mul uMal (polyIntToRq sZero)))
      ⟨0, by decide⟩ = true := by
    rw [hOneMul0]
    unfold decodePayload512; dsimp [vMal, sZero, polyIntToRq]; decide
  have hDec1 : decodePayload512 (CommRingOps.sub vMal (CommRingOps.mul uMal (polyIntToRq sOne)))
      ⟨0, by decide⟩ = false := by
    rw [hOneMul1]
    unfold decodePayload512; dsimp [vMal, sOne, polyIntToRq]; decide
  have hRej : ∀ st : RlweFoReceiverState,
      st.a = CommRingOps.zero → st.choiceBit = false → st.consumed = false →
      (rlweFoReceiverMachine zeroCoins).step st ⟨uMal, vMal, uMal, vMal⟩ = none := by
    intro st ha hc hcons
    unfold rlweFoReceiverMachine PartyMachine.ofOption
    simp only [hcons, hc, Bool.false_eq_true, ↓reduceIte]
    let dec := decodePayload512 (CommRingOps.sub vMal (CommRingOps.mul uMal (polyIntToRq st.sR)))
    have hNeU : polyRqEq uMal (rlweFoEncrypt st.a st.pk0 dec (zeroCoins false dec)).1 = false := by
      rw [Bool.eq_false_iff]
      intro hEq
      have hFun := (polyRqEq_iff _ _).mp hEq
      dsimp only [rlweFoEncrypt, zeroCoins] at hFun
      rw [ha, LawfulCommRing.zero_mul] at hFun
      have hZeroRq : polyIntToRq sZero = CommRingOps.zero := by funext _; rfl
      rw [hZeroRq, LawfulCommRing.add_zero] at hFun
      have hAt0 := congrArg Zq12289.val (congrFun hFun ⟨0, by decide⟩)
      dsimp only [uMal] at hAt0
      change 1 = 0 at hAt0
      exact absurd hAt0 (by decide)
    rw [hNeU]
    rfl
  exact ⟨hs0, hs1, hDec0, hDec1, hRej st0 rfl rfl rfl, hRej st1 rfl rfl rfl⟩

/-! ## 3. Real Bitwise-AND KOS OT Extension + Binary `GF(2)` Leftover Hash Lemma (`[P0-05]` Closure) -/

/-! ### 3.1 Exhaustive Constructive `BitVec k` Hypercube Enumeration & Summation -/

private theorem getLsbD_setWidth_of_lt {w n i : Nat} (x : BitVec w) (hi : i < n) :
    (x.setWidth n).getLsbD i = x.getLsbD i := by
  simp only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]

private theorem getLsbD_cons_of_lt {k i : Nat} (b : Bool) (u : BitVec k) (hi : i < k) :
    (BitVec.cons b u).getLsbD i = u.getLsbD i := by
  have hne : i ≠ k := Nat.ne_of_lt hi
  simp only [BitVec.getLsbD_cons, hne, ↓reduceIte]

private theorem setWidth_cons {k : Nat} (b : Bool) (u : BitVec k) :
    (BitVec.cons b u).setWidth k = u := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_setWidth_of_lt _ hi, getLsbD_cons_of_lt b u hi]

private theorem setWidth_zero (w n : Nat) : (0#w).setWidth n = 0#n := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_setWidth_of_lt _ hi, BitVec.getLsbD_zero, BitVec.getLsbD_zero]

private theorem setWidth_xor {w : Nat} (n : Nat) (u v : BitVec w) :
    (u ^^^ v).setWidth n = u.setWidth n ^^^ v.setWidth n := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_setWidth_of_lt _ hi, BitVec.getLsbD_xor, BitVec.getLsbD_xor,
      getLsbD_setWidth_of_lt _ hi, getLsbD_setWidth_of_lt _ hi]

private theorem bvCons_split {k : Nat} (v : BitVec (k + 1)) :
    BitVec.cons (v.getLsbD k) (v.setWidth k) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hik : i = k
  · subst hik; simp only [BitVec.getLsbD_cons, ↓reduceIte]
  · have hlt : i < k := by omega
    rw [getLsbD_cons_of_lt _ _ hlt, getLsbD_setWidth_of_lt _ hlt]

private theorem bvCons_inj {k : Nat} {b₁ b₂ : Bool} {u₁ u₂ : BitVec k} :
    BitVec.cons b₁ u₁ = BitVec.cons b₂ u₂ ↔ b₁ = b₂ ∧ u₁ = u₂ := by
  constructor
  · intro h
    have hb : (BitVec.cons b₁ u₁).getLsbD k = (BitVec.cons b₂ u₂).getLsbD k := by rw [h]
    have hu : (BitVec.cons b₁ u₁).setWidth k = (BitVec.cons b₂ u₂).setWidth k := by rw [h]
    simp only [BitVec.getLsbD_cons, ↓reduceIte] at hb
    rw [setWidth_cons, setWidth_cons] at hu
    exact ⟨hb, hu⟩
  · rintro ⟨rfl, rfl⟩; rfl

private theorem bvZero_eq_cons (k : Nat) : (0#(k + 1)) = BitVec.cons false (0#k) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_zero, BitVec.getLsbD_cons]
  split <;> rfl

/-- Exhaustive duplicate-free list of all $2^k$ bitvectors in `BitVec k`. -/
def bvEnum : (k : Nat) → List (BitVec k)
  | 0 => [0#0]
  | k + 1 => (bvEnum k).map (BitVec.cons false) ++ (bvEnum k).map (BitVec.cons true)

theorem bvEnum_length_nodup_complete (k : Nat) :
    (bvEnum k).length = 2 ^ k ∧
    (bvEnum k).Nodup ∧
    (∀ v : BitVec k, v ∈ bvEnum k) := by
  induction k with
  | zero =>
    refine ⟨rfl, List.Pairwise.cons (by intro _ h; cases h) .nil, ?_⟩
    intro v
    have hv : v = 0#0 := BitVec.eq_nil v
    subst hv; exact List.Mem.head _
  | succ k ih =>
    obtain ⟨hLen, hNodup, hMem⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · simp only [bvEnum, List.length_append, List.length_map, hLen, Nat.pow_succ]
      omega
    · simp only [bvEnum]
      rw [List.nodup_append]
      have hInj : ∀ b : Bool, ∀ u₁ u₂ : BitVec k,
          BitVec.cons b u₁ = BitVec.cons b u₂ → u₁ = u₂ :=
        fun _ _ _ h => (bvCons_inj.mp h).2
      refine ⟨List.Pairwise.map (BitVec.cons false) (fun u₁ u₂ hne heq => hne (hInj false u₁ u₂ heq)) hNodup,
              List.Pairwise.map (BitVec.cons true) (fun u₁ u₂ hne heq => hne (hInj true u₁ u₂ heq)) hNodup,
              ?_⟩
      intro x hx y hy hxy
      rw [List.mem_map] at hx hy
      rcases hx with ⟨u₁, _, rfl⟩
      rcases hy with ⟨u₂, _, rfl⟩
      have hb := (bvCons_inj.mp hxy).1
      contradiction
    · intro v
      rw [← bvCons_split v]
      simp only [bvEnum, List.mem_append, List.mem_map]
      cases v.getLsbD k
      · exact Or.inl ⟨v.setWidth k, hMem _, rfl⟩
      · exact Or.inr ⟨v.setWidth k, hMem _, rfl⟩

/-- Symbolic hypercube summation $\sum_{v \in \mathrm{BitVec}\, k} f(v)$ in `Nat`. -/
def bvSum : (k : Nat) → (BitVec k → Nat) → Nat
  | 0, f => f 0#0
  | k + 1, f =>
    bvSum k (fun v => f (BitVec.cons false v)) +
    bvSum k (fun v => f (BitVec.cons true v))

/-- Symbolic hypercube summation $\sum_{v \in \mathrm{BitVec}\, k} f(v)$ in `Int`. -/
def intBvSum : (k : Nat) → (BitVec k → Int) → Int
  | 0, f => f 0#0
  | k + 1, f =>
    intBvSum k (fun v => f (BitVec.cons false v)) +
    intBvSum k (fun v => f (BitVec.cons true v))

theorem bvSum_eq_enum_sum : ∀ (k : Nat) (f : BitVec k → Nat),
    bvSum k f = ((bvEnum k).map f).sum
  | 0, f => by simp [bvSum, bvEnum]
  | k + 1, f => by
    simp only [bvSum, bvEnum, List.map_append, List.sum_append, List.map_map,
      bvSum_eq_enum_sum k]
    rfl

private theorem intBvSum_of_bvSum : ∀ (k : Nat) (f : BitVec k → Nat),
    (bvSum k f : Int) = intBvSum k (fun v => (f v : Int))
  | 0, _ => rfl
  | k + 1, f => by
    simp only [bvSum, intBvSum, Int.natCast_add, intBvSum_of_bvSum k]

private theorem bvSum_congr {k : Nat} {f g : BitVec k → Nat} (h : ∀ v, f v = g v) :
    bvSum k f = bvSum k g := by
  induction k with
  | zero => exact h 0#0
  | succ k ih =>
    simp only [bvSum, ih (fun v => h (BitVec.cons false v)), ih (fun v => h (BitVec.cons true v))]

private theorem bvSum_const (k c : Nat) : bvSum k (fun _ => c) = (2 ^ k) * c := by
  induction k with
  | zero => simp [bvSum]
  | succ k ih =>
    simp only [bvSum, ih, Nat.pow_succ]
    rw [Nat.mul_assoc, Nat.two_mul, Nat.mul_add]

private theorem intBvSum_congr {k : Nat} {f g : BitVec k → Int} (h : ∀ v, f v = g v) :
    intBvSum k f = intBvSum k g := by
  induction k with
  | zero => exact h 0#0
  | succ k ih =>
    simp only [intBvSum, ih (fun v => h (BitVec.cons false v)), ih (fun v => h (BitVec.cons true v))]

private theorem intBvSum_const (k : Nat) (c : Int) :
    intBvSum k (fun _ => c) = ((2 ^ k : Nat) : Int) * c := by
  induction k with
  | zero => simp [intBvSum]
  | succ k ih =>
    simp only [intBvSum, ih, Nat.pow_succ, Int.natCast_mul]
    rw [← Int.mul_add ((2 ^ k : Nat) : Int) c c, Int.mul_assoc]
    congr 1; omega

private theorem intBvSum_add {k : Nat} (f g : BitVec k → Int) :
    intBvSum k (fun v => f v + g v) = intBvSum k f + intBvSum k g := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [intBvSum, ih]; omega

private theorem intBvSum_sub {k : Nat} (f g : BitVec k → Int) :
    intBvSum k (fun v => f v - g v) = intBvSum k f - intBvSum k g := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [intBvSum, ih]; omega

private theorem intBvSum_mul_left {k : Nat} (c : Int) (f : BitVec k → Int) :
    intBvSum k (fun v => c * f v) = c * intBvSum k f := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [intBvSum, ih, Int.mul_add]

private theorem intBvSum_mul_right {k : Nat} (f : BitVec k → Int) (c : Int) :
    intBvSum k (fun v => f v * c) = intBvSum k f * c := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [intBvSum, ih, Int.add_mul]

private theorem intBvSum_le {k : Nat} {f g : BitVec k → Int} (h : ∀ v, f v ≤ g v) :
    intBvSum k f ≤ intBvSum k g := by
  induction k with
  | zero => exact h 0#0
  | succ k ih =>
    simp only [intBvSum]
    have h0 := ih (fun v => h (BitVec.cons false v))
    have h1 := ih (fun v => h (BitVec.cons true v))
    omega

private theorem intBvSum_comm (k₁ k₂ : Nat) (g : BitVec k₁ → BitVec k₂ → Int) :
    intBvSum k₁ (fun u => intBvSum k₂ (fun v => g u v)) =
    intBvSum k₂ (fun v => intBvSum k₁ (fun u => g u v)) := by
  induction k₁ with
  | zero => rfl
  | succ k₁ ih =>
    simp only [intBvSum]
    rw [ih (fun u v => g (BitVec.cons false u) v),
        ih (fun u v => g (BitVec.cons true u) v), ← intBvSum_add]

private theorem intBvSum_indicator_one : ∀ (k : Nat) (target : BitVec k),
    intBvSum k (fun y => if y = target then 1 else 0) = 1
  | 0, target => by
    have ht : target = 0#0 := BitVec.eq_nil target
    subst ht; rfl
  | k + 1, target => by
    rw [← bvCons_split target]
    simp only [intBvSum]
    cases target.getLsbD k
    · have hL : intBvSum k (fun v => if BitVec.cons false v = BitVec.cons false (target.setWidth k) then (1 : Int) else 0) =
          intBvSum k (fun v => if v = target.setWidth k then 1 else 0) := by
        apply intBvSum_congr; intro v; simp [bvCons_inj]
      have hR : intBvSum k (fun v => if BitVec.cons true v = BitVec.cons false (target.setWidth k) then (1 : Int) else 0) =
          intBvSum k (fun _ => 0) := by
        apply intBvSum_congr; intro v; simp [bvCons_inj]
      rw [hL, hR, intBvSum_indicator_one k, intBvSum_const]; simp
    · have hL : intBvSum k (fun v => if BitVec.cons false v = BitVec.cons true (target.setWidth k) then (1 : Int) else 0) =
          intBvSum k (fun _ => 0) := by
        apply intBvSum_congr; intro v; simp [bvCons_inj]
      have hR : intBvSum k (fun v => if BitVec.cons true v = BitVec.cons true (target.setWidth k) then (1 : Int) else 0) =
          intBvSum k (fun v => if v = target.setWidth k then 1 else 0) := by
        apply intBvSum_congr; intro v; simp [bvCons_inj]
      rw [hL, hR, intBvSum_indicator_one k, intBvSum_const]; simp

/-! ### 3.2 Bitwise-AND KOS Correlation, Exact Selective-Failure Fiber Count & Poisoning -/

/-- Exact Hamming weight of `v : BitVec k`. -/
def bvHammingWeight : {k : Nat} → BitVec k → Nat
  | 0, _ => 0
  | k + 1, v => (if v.getLsbD k then 1 else 0) + bvHammingWeight (v.setWidth k)

theorem bvHammingWeight_le : ∀ {k : Nat} (v : BitVec k), bvHammingWeight v ≤ k
  | 0, _ => Nat.le_refl 0
  | k + 1, v => by
    simp only [bvHammingWeight]
    have ih := bvHammingWeight_le (v.setWidth k)
    split <;> omega

theorem bvHammingWeight_eq_zero_iff : ∀ {k : Nat} (v : BitVec k),
    bvHammingWeight v = 0 ↔ v = 0#k
  | 0, v => ⟨fun _ => BitVec.eq_nil v, fun _ => rfl⟩
  | k + 1, v => by
    simp only [bvHammingWeight]
    have ih := bvHammingWeight_eq_zero_iff (v.setWidth k)
    constructor
    · intro h
      have hBit : v.getLsbD k = false := by
        cases hb : v.getLsbD k
        · rfl
        · simp only [hb, ↓reduceIte] at h; omega
      simp only [hBit, Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at h
      have hRest : v.setWidth k = 0#k := ih.mp h
      rw [← bvCons_split v, hBit, hRest, bvZero_eq_cons]
    · intro h
      subst h
      have hSet0 : (0#(k + 1)).setWidth k = 0#k := setWidth_zero (k + 1) k
      simp only [BitVec.getLsbD_zero, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      exact ih.mpr hSet0

private theorem bvHammingWeight_cons {k : Nat} (b : Bool) (u : BitVec k) :
    bvHammingWeight (BitVec.cons b u) = (if b then 1 else 0) + bvHammingWeight u := by
  simp only [bvHammingWeight, BitVec.getLsbD_cons, ↓reduceIte, setWidth_cons]

private theorem one_toNat_pos (m : Nat) (hm : 1 ≤ m) : (1#m).toNat = 1 := by
  change 1 % (2 ^ m) = 1
  exact Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))

private theorem one_eq_cons_false (k : Nat) : (1#(k + 2)) = BitVec.cons false (1#(k + 1)) := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  rw [BitVec.getLsbD_cons]
  by_cases hik : i = k + 1
  · subst hik
    simp only [↓reduceIte, BitVec.getLsbD, one_toNat_pos (k + 2) (by omega)]
    cases hBit : Nat.testBit 1 (k + 1)
    · rfl
    · have hk0 := Nat.testBit_one_eq_true_iff_self_eq_zero.mp hBit
      omega
  · simp only [hik, ↓reduceIte, BitVec.getLsbD,
      one_toNat_pos (k + 2) (by omega), one_toNat_pos (k + 1) (by omega)]

private theorem bvHammingWeight_one : ∀ (k : Nat), bvHammingWeight (1#(k + 1)) = 1
  | 0 => by decide
  | k + 1 => by rw [one_eq_cons_false k, bvHammingWeight_cons, bvHammingWeight_one k]; rfl

private theorem bvAnd_cons {k : Nat} (b₁ b₂ : Bool) (u₁ u₂ : BitVec k) :
    (BitVec.cons b₁ u₁ &&& BitVec.cons b₂ u₂) = BitVec.cons (b₁ && b₂) (u₁ &&& u₂) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_cons]
  split <;> rfl

/-- Exact orthogonal fiber count: $|\{\Delta \in \mathrm{BitVec}\, k \mid (e \mathbin{\&} \Delta) = 0\}| = 2^{k - \mathrm{wt}(e)}$. -/
theorem bvOrthogonalCount_exact : ∀ (k : Nat) (e : BitVec k),
    bvSum k (fun delta => if (e &&& delta) = 0#k then 1 else 0) =
      2 ^ (k - bvHammingWeight e)
  | 0, e => by
    simp only [bvSum, bvHammingWeight, Nat.sub_zero, Nat.pow_zero]
    have h0 : (e &&& 0#0) = 0#0 := BitVec.eq_nil _
    rw [h0]; rfl
  | k + 1, e => by
    have hSplit := bvCons_split e
    have hWt := bvHammingWeight_le (e.setWidth k)
    simp only [bvSum, bvHammingWeight]
    have hTerm : ∀ (b : Bool) (d : BitVec k),
        ((e &&& BitVec.cons b d) = 0#(k + 1)) ↔
          ((e.getLsbD k && b) = false ∧ (e.setWidth k &&& d) = 0#k) := by
      intro b d
      conv => lhs; rw [← hSplit, bvAnd_cons, bvZero_eq_cons]
      exact bvCons_inj
    cases hb : e.getLsbD k
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      have hSub : k + 1 - bvHammingWeight (e.setWidth k) = (k - bvHammingWeight (e.setWidth k)) + 1 := by omega
      have h0 : bvSum k (fun d => if (e &&& BitVec.cons false d) = 0#(k + 1) then 1 else 0) =
          bvSum k (fun d => if (e.setWidth k &&& d) = 0#k then 1 else 0) := by
        apply bvSum_congr; intro d
        simp only [hTerm, hb, Bool.false_and, true_and]
      have h1 : bvSum k (fun d => if (e &&& BitVec.cons true d) = 0#(k + 1) then 1 else 0) =
          bvSum k (fun d => if (e.setWidth k &&& d) = 0#k then 1 else 0) := by
        apply bvSum_congr; intro d
        simp only [hTerm, hb, Bool.false_and, true_and]
      rw [h0, h1, bvOrthogonalCount_exact k (e.setWidth k), hSub, Nat.pow_succ]
      omega
    · simp only [↓reduceIte]
      have hSub : k + 1 - (1 + bvHammingWeight (e.setWidth k)) = k - bvHammingWeight (e.setWidth k) := by omega
      have h0 : bvSum k (fun d => if (e &&& BitVec.cons false d) = 0#(k + 1) then 1 else 0) =
          bvSum k (fun d => if (e.setWidth k &&& d) = 0#k then 1 else 0) := by
        apply bvSum_congr; intro d
        simp only [hTerm, hb, Bool.and_false, true_and]
      have h1 : bvSum k (fun d => if (e &&& BitVec.cons true d) = 0#(k + 1) then 1 else 0) =
          bvSum k (fun _ => 0) := by
        apply bvSum_congr; intro d
        simp only [hTerm, hb, Bool.and_true, Bool.true_eq_false, false_and, ↓reduceIte]
      rw [h0, h1, bvOrthogonalCount_exact k (e.setWidth k), bvSum_const, hSub]
      omega

/-- Real 128-column KOS OT correlation row: $q_\ell = t_\ell \oplus (x_\ell \mathbin{\&} \Delta)$. -/
@[expose] def kosBitwiseRowQ (tRow xRow delta : BitVec 128) : BitVec 128 :=
  tRow ^^^ (xRow &&& delta)

/-- **`kos_bitwise_selective_failure_exact` (`[P0-05]` Core Selective-Failure Theorem)**:
    1. Injecting column-wise fault mask `e : BitVec 128` shifts `q_l` by `e &&& delta` (`kosBitwiseRowQ_fault`),
       so the row correlation check passes **iff** `e &&& delta = 0#128`.
    2. Over all $2^{128}$ uniform choices of `delta ∈ bvEnum 128`, **exact** count `2 ^ (128 - bvHammingWeight e)`
       pass (`passCount * 2^w = 2^128`, exact probability $2^{-w}$, leaking at most $w$ bits of $\Delta$).
    3. **`#tooth`**: A weight-1 fault (`e = 1#128`, `w = 1`) passes on `2^127` of `2^128` keys (exact probability
       `1/2`, NOT $2^{-128}$!), proving why `s = 128` sacrifice + `128 × 384` `GF(2)` LHL amplification are mandatory! -/
theorem kos_bitwise_selective_failure_exact (tRow xRow e : BitVec 128) :
    let w := bvHammingWeight e
    let passCount := bvSum 128 (fun delta => if (e &&& delta) = 0#128 then 1 else 0)
    (∀ delta : BitVec 128,
      kosBitwiseRowQ tRow (xRow ^^^ e) delta = kosBitwiseRowQ tRow xRow delta ^^^ (e &&& delta)) ∧
    (∀ delta : BitVec 128,
      kosBitwiseRowQ tRow (xRow ^^^ e) delta = kosBitwiseRowQ tRow xRow delta ↔ (e &&& delta) = 0#128) ∧
    passCount = 2 ^ (128 - w) ∧
    passCount * (2 ^ w) = 2 ^ 128 ∧
    (bvHammingWeight (1#128) = 1 ∧
     bvSum 128 (fun delta => if (1#128 &&& delta) = 0#128 then 1 else 0) = 2 ^ 127) := by
  intro w passCount
  have hXorDist : ∀ delta : BitVec 128,
      kosBitwiseRowQ tRow (xRow ^^^ e) delta = kosBitwiseRowQ tRow xRow delta ^^^ (e &&& delta) := by
    intro delta
    unfold kosBitwiseRowQ
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and]
    cases tRow.getLsbD i <;> cases xRow.getLsbD i <;> cases e.getLsbD i <;> cases delta.getLsbD i <;> rfl
  have hIff : ∀ delta : BitVec 128,
      kosBitwiseRowQ tRow (xRow ^^^ e) delta = kosBitwiseRowQ tRow xRow delta ↔ (e &&& delta) = 0#128 := by
    intro delta
    rw [hXorDist delta]
    constructor
    · intro hEq
      have h := congrArg (kosBitwiseRowQ tRow xRow delta ^^^ ·) hEq
      rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor] at h
      exact h
    · intro hZ; rw [hZ, BitVec.xor_zero]
  have hCount : passCount = 2 ^ (128 - w) := bvOrthogonalCount_exact 128 e
  have hWLe : w ≤ 128 := bvHammingWeight_le e
  have hProd : passCount * (2 ^ w) = 2 ^ 128 := by
    rw [hCount, ← Nat.pow_add]
    have hAdd : 128 - w + w = 128 := by omega
    rw [hAdd]
  have hWt1 : bvHammingWeight (1#128) = 1 := bvHammingWeight_one 127
  have hTooth1 : bvSum 128 (fun delta => if (1#128 &&& delta) = 0#128 then 1 else 0) = 2 ^ 127 := by
    rw [bvOrthogonalCount_exact 128 (1#128), hWt1]
  exact ⟨hXorDist, hIff, hCount, hProd, ⟨hWt1, hTooth1⟩⟩

/-- Interactive $\mathbb{F}_{2^{128}}$ (`Tower128`) KOS linear-combination soundness when `e &&& delta ≠ 0#128`:
    for any nonzero row discrepancy `e &&& delta ≠ 0#128` locked *before* `chi` is sampled, at most
    `1` challenge `chi : Tower128` hits any target residual `rhs` (`≤ 1 / 2^128` forgery probability). -/
theorem kos_gf2_128_sacrifice_linear_soundness
    (e delta : BitVec 128) (hNonOrth : (e &&& delta) ≠ 0#128)
    (rhs : Tower128) (chi₁ chi₂ : Tower128)
    (h1 : towerMul 7 (unpackTower 7 (e &&& delta)) chi₁ = rhs)
    (h2 : towerMul 7 (unpackTower 7 (e &&& delta)) chi₂ = rhs) :
    chi₁ = chi₂ := by
  have hNz : unpackTower 7 (e &&& delta) ≠ towerZero 7 := by
    intro hZ
    have hp := congrArg (packTower 7) hZ
    rw [packTower_unpackTower, packTower_zero] at hp
    exact hNonOrth hp
  exact towerMul_cancel_left 7 (unpackTower 7 (e &&& delta)) chi₁ chi₂ hNz (h1.trans h2.symm)

/-- Sticky-poisoning KOS Sender channel state (`poisoned = true` permanently disables future batches). -/
structure KosSenderChannelState where
  delta : BitVec 128
  batchCtr : Nat
  poisoned : Bool
  deriving DecidableEq, Repr

/-- KOS Sender check input (`eBatch` row fault, challenge `chi`, residual target `rhs`). -/
structure KosBatchCheckInput where
  rowFault : BitVec 128
  chi : Tower128
  claimedResidual : Tower128

/-- Error-mutating KOS Sender `PartyMachine` permanently poisoning the channel on first check failure! -/
def kosSenderChannelMachine : PartyMachine KosSenderChannelState KosBatchCheckInput Nat :=
  PartyMachine.ofOutcome fun st inp =>
    if st.poisoned then
      .err st ()
    else
      let actualRes := towerMul 7 (unpackTower 7 (inp.rowFault &&& st.delta)) inp.chi
      if actualRes = inp.claimedResidual then
        .ok { st with batchCtr := st.batchCtr + 1 } st.batchCtr
      else
        .err { st with poisoned := true } ()

/-- Once a KOS check fails (`poisoned = true`), no subsequent batch is ever accepted along any `ValidTrace`. -/
theorem kosSenderChannel_poisoned_terminal :
    ∀ {st stFinal : KosSenderChannelState} {trace : List (KosBatchCheckInput × Nat)},
      st.poisoned = true →
      kosSenderChannelMachine.ValidTrace st trace stFinal →
      trace = [] ∧ stFinal.poisoned = true
  | _, _, _, hPois, .nil _ => ⟨rfl, hPois⟩
  | st, _, _, hPois, .accept hStep _ => by
    unfold kosSenderChannelMachine PartyMachine.ofOutcome at hStep
    simp [hPois] at hStep
  | st, _, _, hPois, .reject inp _ hTail => by
    have hPois' : (kosSenderChannelMachine.errStep st inp).poisoned = true := by
      unfold kosSenderChannelMachine PartyMachine.ofOutcome
      simp [hPois]
    exact kosSenderChannel_poisoned_terminal hPois' hTail

/-! ### 3.3 `128 × 384` `GF(2)` Universal Linear Hash & Constructive Finite Leftover Hash Lemma -/

/-- `GF(2)` inner product $\bigoplus_{j=0}^{n-1} (r_j \land v_j)$ over `BitVec n`. -/
def gf2Dot : (n : Nat) → BitVec n → BitVec n → Bool
  | 0, _, _ => false
  | n + 1, r, v => (r.getLsbD n && v.getLsbD n) ^^ gf2Dot n (r.setWidth n) (v.setWidth n)

private theorem gf2Dot_zero_right : ∀ (n : Nat) (r : BitVec n), gf2Dot n r 0#n = false
  | 0, _ => rfl
  | n + 1, r => by
    have hSet0 : (0#(n + 1)).setWidth n = 0#n := setWidth_zero (n + 1) n
    simp only [gf2Dot, BitVec.getLsbD_zero, Bool.and_false, Bool.false_xor, hSet0, gf2Dot_zero_right n]

private theorem gf2Dot_xor_right : ∀ (n : Nat) (r u v : BitVec n),
    gf2Dot n r (u ^^^ v) = (gf2Dot n r u ^^ gf2Dot n r v)
  | 0, _, _, _ => rfl
  | n + 1, r, u, v => by
    have hSet : (u ^^^ v).setWidth n = u.setWidth n ^^^ v.setWidth n := setWidth_xor n u v
    simp only [gf2Dot, BitVec.getLsbD_xor, hSet, gf2Dot_xor_right n]
    cases r.getLsbD n <;> cases u.getLsbD n <;> cases v.getLsbD n <;>
      cases gf2Dot n (r.setWidth n) (u.setWidth n) <;>
      cases gf2Dot n (r.setWidth n) (v.setWidth n) <;> rfl

private theorem gf2Dot_comm : ∀ (n : Nat) (r v : BitVec n), gf2Dot n r v = gf2Dot n v r
  | 0, _, _ => rfl
  | n + 1, r, v => by
    simp only [gf2Dot, Bool.and_comm, gf2Dot_comm n]

/-- Exact hyperplane balance over $\mathrm{GF}(2)^n$: for any nonzero $v \in \mathrm{BitVec}\, n$ and $b \in \mathrm{Bool}$,
    $|\{r \in \mathrm{BitVec}\, n \mid \langle r, v \rangle = b\}| = 2^{n - 1}$. -/
theorem gf2Dot_balanced : ∀ (n : Nat) (v : BitVec n) (_hv : v ≠ 0#n) (b : Bool),
    intBvSum n (fun r => if gf2Dot n r v = b then 1 else 0) = ((2 ^ (n - 1) : Nat) : Int)
  | 0, v, hv, _ => False.elim (hv (BitVec.eq_nil v))
  | n + 1, v, hv, b => by
    simp only [intBvSum, Nat.add_sub_cancel]
    have hConsStep : ∀ (rHi : Bool) (rLo : BitVec n),
        gf2Dot (n + 1) (BitVec.cons rHi rLo) v =
          ((rHi && v.getLsbD n) ^^ gf2Dot n rLo (v.setWidth n)) := by
      intro rHi rLo
      have hSet : (BitVec.cons rHi rLo).setWidth n = rLo := setWidth_cons rHi rLo
      conv => lhs; unfold gf2Dot
      simp only [BitVec.getLsbD_cons, ↓reduceIte, hSet]
    cases hvHi : v.getLsbD n
    · -- `v_hi = false` => `v.setWidth n ≠ 0#n` and `n ≥ 1`
      have hvLo : v.setWidth n ≠ 0#n := by
        intro hZeroLo
        apply hv
        have hSplit : BitVec.cons (v.getLsbD n) (v.setWidth n) = v := bvCons_split v
        rw [← hSplit, hvHi, hZeroLo, bvZero_eq_cons]
      have hnPos : 1 ≤ n := by
        cases n with
        | zero => exact False.elim (hvLo (BitVec.eq_nil _))
        | succ n' => omega
      have hL : intBvSum n (fun rLo => if gf2Dot (n + 1) (BitVec.cons false rLo) v = b then (1 : Int) else 0) =
          intBvSum n (fun rLo => if gf2Dot n rLo (v.setWidth n) = b then 1 else 0) := by
        apply intBvSum_congr; intro rLo; simp only [hConsStep, hvHi, Bool.and_false, Bool.false_xor]
      have hR : intBvSum n (fun rLo => if gf2Dot (n + 1) (BitVec.cons true rLo) v = b then (1 : Int) else 0) =
          intBvSum n (fun rLo => if gf2Dot n rLo (v.setWidth n) = b then 1 else 0) := by
        apply intBvSum_congr; intro rLo; simp only [hConsStep, hvHi, Bool.and_false, Bool.false_xor]
      rw [hL, hR, gf2Dot_balanced n (v.setWidth n) hvLo b]
      have hPow : 2 ^ n = 2 ^ (n - 1) + 2 ^ (n - 1) := by
        have hEq : n = (n - 1) + 1 := by omega
        conv => lhs; rw [hEq, Nat.pow_succ]
        omega
      rw [hPow, Int.natCast_add]
    · -- `v_hi = true` => for every `rLo`, `rHi = false` and `rHi = true` give opposite bits `g` and `!g`, summing to `1`!
      rw [← intBvSum_add]
      have hOneEach : ∀ rLo : BitVec n,
          (if gf2Dot (n + 1) (BitVec.cons false rLo) v = b then (1 : Int) else 0) +
          (if gf2Dot (n + 1) (BitVec.cons true rLo) v = b then 1 else 0) = 1 := by
        intro rLo
        rw [hConsStep false rLo, hConsStep true rLo, hvHi]
        cases gf2Dot n rLo (v.setWidth n) <;> cases b <;> decide
      rw [intBvSum_congr hOneEach, intBvSum_const, Int.mul_one]

/-- Systematic $m \times (n + m)$ `GF(2)` universal linear hash $[R_{m \times n} \mid I_m]$:
    at $n = 256, m = 128$, `BitVec (256 * 128) → BitVec (256 + 128) → BitVec 128` is
    definitionally `BitVec 32768 → BitVec 384 → BitVec 128` matching `preprocessing.rs`! -/
@[expose] def evalSystematicGF2 (n : Nat) : (m : Nat) → BitVec (n * m) → BitVec (n + m) → BitVec m
  | 0, _, _ => 0#0
  | m + 1, R, x =>
    BitVec.cons
      (x.getLsbD (n + m) ^^ gf2Dot n (R.extractLsb' (n * m) n) (x.setWidth n))
      (evalSystematicGF2 n m (R.setWidth (n * m)) (x.setWidth (n + m)))

/-- Concrete `128 × 384` `GF(2)` base-OT combiner (`256` entropy-slack bits + `128` systematic bits). -/
abbrev evalGf2Combiner128x384 : BitVec 32768 → BitVec 384 → BitVec 128 :=
  evalSystematicGF2 256 128

theorem evalSystematicGF2_xor (n : Nat) : ∀ (m : Nat) (R : BitVec (n * m)) (x x' : BitVec (n + m)),
    evalSystematicGF2 n m R (x ^^^ x') =
      (evalSystematicGF2 n m R x ^^^ evalSystematicGF2 n m R x')
  | 0, _, _, _ => (BitVec.eq_nil _).trans (BitVec.eq_nil _).symm
  | m + 1, R, x, x' => by
    have hSetCore : (x ^^^ x').setWidth n = x.setWidth n ^^^ x'.setWidth n := setWidth_xor n x x'
    have hSetRest : (x ^^^ x').setWidth (n + m) = x.setWidth (n + m) ^^^ x'.setWidth (n + m) :=
      setWidth_xor (n + m) x x'
    have hConsXor : ∀ (b₁ b₂ : Bool) (u₁ u₂ : BitVec m),
        (BitVec.cons b₁ u₁ ^^^ BitVec.cons b₂ u₂) = BitVec.cons (b₁ ^^ b₂) (u₁ ^^^ u₂) := by
      intro b₁ b₂ u₁ u₂
      apply BitVec.eq_of_getLsbD_eq; intro i _
      simp only [BitVec.getLsbD_xor, BitVec.getLsbD_cons]
      split <;> rfl
    simp only [evalSystematicGF2, BitVec.getLsbD_xor, hSetCore, hSetRest, gf2Dot_xor_right,
      evalSystematicGF2_xor n m, hConsXor]
    congr 1
    cases x.getLsbD (n + m) <;> cases x'.getLsbD (n + m) <;>
      cases gf2Dot n (R.extractLsb' (n * m) n) (x.setWidth n) <;>
      cases gf2Dot n (R.extractLsb' (n * m) n) (x'.setWidth n) <;> rfl

private def bvAppendLoHi (a : Nat) : (b : Nat) → BitVec a → BitVec b → BitVec (a + b)
  | 0, lo, _ => lo
  | b + 1, lo, hi => BitVec.cons (hi.getLsbD b) (bvAppendLoHi a b lo (hi.setWidth b))

private theorem bvAppendLoHi_setWidth (a : Nat) : ∀ (b : Nat) (lo : BitVec a) (hi : BitVec b),
    (bvAppendLoHi a b lo hi).setWidth a = lo
  | 0, lo, _ => by
    apply BitVec.eq_of_getLsbD_eq; intro i hiLt
    exact getLsbD_setWidth_of_lt lo hiLt
  | b + 1, lo, hi => by
    apply BitVec.eq_of_getLsbD_eq; intro i hiLt
    have ih := bvAppendLoHi_setWidth a b lo (hi.setWidth b)
    have hLtAb : i < a + b := by omega
    rw [getLsbD_setWidth_of_lt _ hiLt]
    dsimp only [bvAppendLoHi]
    rw [getLsbD_cons_of_lt _ _ hLtAb]
    have hEq := congrArg (fun v => v.getLsbD i) ih
    rwa [getLsbD_setWidth_of_lt _ hiLt] at hEq

private theorem bvAppendLoHi_extractHi (a : Nat) : ∀ (b : Nat) (lo : BitVec a) (hi : BitVec b),
    (bvAppendLoHi a b lo hi).extractLsb' a b = hi
  | 0, _, hi => (BitVec.eq_nil _).trans (BitVec.eq_nil hi).symm
  | b + 1, lo, hi => by
    apply BitVec.eq_of_getLsbD_eq; intro i hiLt
    simp only [BitVec.getLsbD_extractLsb', hiLt, decide_true, Bool.true_and]
    dsimp only [bvAppendLoHi]
    by_cases hib : i = b
    · subst hib
      simp only [BitVec.getLsbD_cons]
      split
      · rfl
      · rename_i hNe; exact False.elim (hNe rfl)
    · have hltB : i < b := by omega
      have hLtAb : a + i < a + b := by omega
      rw [getLsbD_cons_of_lt _ _ hLtAb]
      have ih := bvAppendLoHi_extractHi a b lo (hi.setWidth b)
      have hExtr : ((bvAppendLoHi a b lo (hi.setWidth b)).extractLsb' a b).getLsbD i =
          (hi.setWidth b).getLsbD i := by rw [ih]
      simp only [BitVec.getLsbD_extractLsb', hltB, decide_true, Bool.true_and] at hExtr
      rwa [getLsbD_setWidth_of_lt _ hltB] at hExtr

private theorem intBvSum_split_lo_hi (a : Nat) : ∀ (b : Nat) (g : BitVec (a + b) → Int),
    intBvSum (a + b) g = intBvSum b (fun hi => intBvSum a (fun lo => g (bvAppendLoHi a b lo hi)))
  | 0, g => by
    simp only [Nat.add_zero, intBvSum]
    apply intBvSum_congr; intro lo; rfl
  | b + 1, g => by
    change intBvSum (a + b) (fun v => g (BitVec.cons false v)) +
           intBvSum (a + b) (fun v => g (BitVec.cons true v)) =
           intBvSum b (fun hi => intBvSum a (fun lo => g (bvAppendLoHi a (b + 1) lo (BitVec.cons false hi)))) +
           intBvSum b (fun hi => intBvSum a (fun lo => g (bvAppendLoHi a (b + 1) lo (BitVec.cons true hi))))
    rw [intBvSum_split_lo_hi a b, intBvSum_split_lo_hi a b]
    congr 1
    · apply intBvSum_congr; intro hi; apply intBvSum_congr; intro lo
      have hSet : (BitVec.cons false hi).setWidth b = hi := setWidth_cons false hi
      simp only [bvAppendLoHi, BitVec.getLsbD_cons, ↓reduceIte, hSet]
    · apply intBvSum_congr; intro hi; apply intBvSum_congr; intro lo
      have hSet : (BitVec.cons true hi).setWidth b = hi := setWidth_cons true hi
      simp only [bvAppendLoHi, BitVec.getLsbD_cons, ↓reduceIte, hSet]

private theorem evalSystematicGF2_zero_core_ne (n : Nat) :
    ∀ (m : Nat) (R : BitVec (n * m)) (d : BitVec (n + m)),
      d.setWidth n = 0#n → d ≠ 0#(n + m) → evalSystematicGF2 n m R d ≠ 0#m
  | 0, _, d, hCore, hNe => by
    intro _
    apply hNe
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have hiN : i < n := by omega
    have hBit : (d.setWidth n).getLsbD i = (0#n).getLsbD i := by rw [hCore]
    rw [getLsbD_setWidth_of_lt _ hiN, BitVec.getLsbD_zero] at hBit
    rw [BitVec.getLsbD_zero]
    exact hBit
  | m + 1, R, d, hCore, hNe => by
    simp only [evalSystematicGF2, hCore, gf2Dot_zero_right, Bool.xor_false]
    intro hEq0
    rw [bvZero_eq_cons] at hEq0
    obtain ⟨hBit0, hRest0⟩ := bvCons_inj.mp hEq0
    have hCoreRest : (d.setWidth (n + m)).setWidth n = 0#n := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have hLt : i < n + m := by omega
      rw [getLsbD_setWidth_of_lt _ hi, getLsbD_setWidth_of_lt _ hLt]
      have hB : (d.setWidth n).getLsbD i = (0#n).getLsbD i := by rw [hCore]
      rwa [getLsbD_setWidth_of_lt _ hi] at hB
    have hRestZero : d.setWidth (n + m) = 0#(n + m) := by
      by_cases hNz : d.setWidth (n + m) = 0#(n + m)
      · exact hNz
      · exact False.elim (evalSystematicGF2_zero_core_ne n m (R.setWidth (n * m))
          (d.setWidth (n + m)) hCoreRest hNz hRest0)
    apply hNe
    have hSplit : BitVec.cons (d.getLsbD (n + m)) (d.setWidth (n + m)) = d := bvCons_split d
    rw [← hSplit, hBit0, hRestZero]
    exact (bvZero_eq_cons (n + m)).symm

private theorem evalSystematicGF2_nonzero_core_exact (n : Nat) (hn : 1 ≤ n) :
    ∀ (m : Nat) (d : BitVec (n + m)),
      d.setWidth n ≠ 0#n →
      intBvSum (n * m) (fun R => if evalSystematicGF2 n m R d = 0#m then 1 else 0) =
        ((2 ^ (n * m - m) : Nat) : Int)
  | 0, d, _ => by
    simp only [Nat.mul_zero, Nat.sub_zero, Nat.pow_zero, intBvSum]
    have h0 : evalSystematicGF2 n 0 0#0 d = 0#0 := rfl
    simp only [h0, ↓reduceIte]
    rfl
  | m + 1, d, hCoreNz => by
    change intBvSum (n * m + n) _ = _
    rw [intBvSum_split_lo_hi (n * m) n]
    have hCoreRest : (d.setWidth (n + m)).setWidth n = d.setWidth n := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have hLt : i < n + m := by omega
      rw [getLsbD_setWidth_of_lt _ hi, getLsbD_setWidth_of_lt _ hLt, getLsbD_setWidth_of_lt _ hi]
    have hInner : ∀ hi : BitVec n,
        intBvSum (n * m) (fun lo =>
          if evalSystematicGF2 n (m + 1) (bvAppendLoHi (n * m) n lo hi) d = 0#(m + 1) then (1 : Int) else 0) =
        (if gf2Dot n hi (d.setWidth n) = d.getLsbD (n + m) then 1 else 0) *
          ((2 ^ (n * m - m) : Nat) : Int) := by
      intro hi
      have hEach : ∀ lo : BitVec (n * m),
          (if evalSystematicGF2 n (m + 1) (bvAppendLoHi (n * m) n lo hi) d = 0#(m + 1) then (1 : Int) else 0) =
          (if gf2Dot n hi (d.setWidth n) = d.getLsbD (n + m) then 1 else 0) *
            (if evalSystematicGF2 n m lo (d.setWidth (n + m)) = 0#m then 1 else 0) := by
        intro lo
        simp only [evalSystematicGF2, bvAppendLoHi_extractHi, bvAppendLoHi_setWidth]
        conv => lhs; rw [bvZero_eq_cons]
        by_cases hRow : gf2Dot n hi (d.setWidth n) = d.getLsbD (n + m)
        · have hXor0 : (d.getLsbD (n + m) ^^ gf2Dot n hi (d.setWidth n)) = false := by
            rw [hRow]; cases d.getLsbD (n + m) <;> rfl
          rw [hXor0, hRow]
          simp only [bvCons_inj, true_and, ↓reduceIte, Int.one_mul]
        · have hXor1 : (d.getLsbD (n + m) ^^ gf2Dot n hi (d.setWidth n)) = true := by
            cases hb1 : d.getLsbD (n + m) <;> cases hb2 : gf2Dot n hi (d.setWidth n) <;> simp_all
          rw [hXor1]
          simp only [hRow, bvCons_inj, Bool.true_eq_false, false_and, ↓reduceIte, Int.zero_mul]
      rw [intBvSum_congr hEach, intBvSum_mul_left,
          evalSystematicGF2_nonzero_core_exact n hn m (d.setWidth (n + m)) (hCoreRest.symm ▸ hCoreNz)]
    rw [intBvSum_congr hInner, intBvSum_mul_right,
        gf2Dot_balanced n (d.setWidth n) hCoreNz (d.getLsbD (n + m))]
    rw [← Int.natCast_mul, ← Nat.pow_add]
    congr 2
    have hGe : m ≤ n * m := by
      have := Nat.mul_le_mul_right m hn; simpa using this
    have hMulSucc : n * (m + 1) = n * m + n := Nat.mul_succ n m
    omega

/-- **Exact 2-Universality of `evalSystematicGF2` (`evalSystematicGF2_two_universal`)**:
    For every $n \ge 1, m \ge 0$ and distinct inputs $x \neq x' \in \mathrm{BitVec}\,(n + m)$,
    at most $2^{nm - m} = |\mathcal{R}| / 2^m$ matrices $R$ collide (exact $2^{nm - m}$ when $x, x'$
    differ in the lower $n$ slack bits, and $0$ collisions when they differ only in the upper $m$ bits!). -/
theorem evalSystematicGF2_two_universal (n m : Nat) (hn : 1 ≤ n)
    (x x' : BitVec (n + m)) (hNe : x ≠ x') :
    intBvSum (n * m) (fun R => if evalSystematicGF2 n m R x = evalSystematicGF2 n m R x' then 1 else 0) ≤
      ((2 ^ (n * m - m) : Nat) : Int) := by
  let d := x ^^^ x'
  have hdNe : d ≠ 0#(n + m) := by
    intro hd0
    apply hNe
    have hx := congrArg (x ^^^ ·) hd0
    dsimp only [d] at hx
    rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor, BitVec.xor_zero] at hx
    exact hx.symm
  have hDiff : ∀ R : BitVec (n * m),
      (evalSystematicGF2 n m R x = evalSystematicGF2 n m R x') ↔
        (evalSystematicGF2 n m R d = 0#m) := by
    intro R
    dsimp only [d]
    rw [evalSystematicGF2_xor]
    constructor
    · intro hEq; rw [hEq, BitVec.xor_self]
    · intro hZ
      have hx := congrArg (evalSystematicGF2 n m R x ^^^ ·) hZ
      rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor, BitVec.xor_zero] at hx
      exact hx.symm
  have hCongr : intBvSum (n * m) (fun R => if evalSystematicGF2 n m R x = evalSystematicGF2 n m R x' then (1 : Int) else 0) =
      intBvSum (n * m) (fun R => if evalSystematicGF2 n m R d = 0#m then 1 else 0) := by
    apply intBvSum_congr; intro R; simp only [hDiff R]
  rw [hCongr]
  by_cases hCore : d.setWidth n = 0#n
  · have hZeroEach : ∀ R : BitVec (n * m),
        (if evalSystematicGF2 n m R d = 0#m then (1 : Int) else 0) = 0 := by
      intro R
      have hNz := evalSystematicGF2_zero_core_ne n m R d hCore hdNe
      simp only [hNz, ↓reduceIte]
    rw [intBvSum_congr hZeroEach, intBvSum_const, Int.mul_zero]
    exact Int.natCast_nonneg _
  · rw [evalSystematicGF2_nonzero_core_exact n hn m d hCore]
    exact Int.le_refl _

/-! ### 3.4 Constructive Integer Cauchy-Schwarz & Finite Leftover Hash Lemma (`[P0-05]`) -/

private theorem int_sq_nonneg (z : Int) : 0 ≤ z * z := by
  by_cases h : 0 ≤ z
  · exact Int.mul_nonneg h h
  · have hn : 0 ≤ -z := by omega
    have hm := Int.mul_nonneg hn hn
    simpa only [Int.neg_mul_neg] using hm

/-- Constructive hypercube Cauchy-Schwarz inequality (`0 Classical.choice`, `0` reals):
    $\left(\sum_{u \in \mathrm{BitVec}\, k} |f(u)|\right)^2 \le 2^k \sum_{u \in \mathrm{BitVec}\, k} f(u)^2$. -/
private theorem intBvSum_abs_sq_le : ∀ (k : Nat) (f : BitVec k → Int),
    let s1 := intBvSum k (fun u => ((f u).natAbs : Int))
    s1 * s1 ≤ ((2 ^ k : Nat) : Int) * intBvSum k (fun u => f u * f u)
  | 0, f => by
    simp only [intBvSum, Nat.pow_zero, Int.natCast_one, Int.one_mul]
    have hAbsSq : ((f 0#0).natAbs : Int) * ((f 0#0).natAbs : Int) = f 0#0 * f 0#0 := by
      rw [← Int.natCast_mul, Int.natAbs_mul_self]
    rw [hAbsSq]; exact Int.le_refl _
  | k + 1, f => by
    simp only [intBvSum, Nat.pow_succ, Int.natCast_mul]
    have ih0 := intBvSum_abs_sq_le k (fun v => f (BitVec.cons false v))
    have ih1 := intBvSum_abs_sq_le k (fun v => f (BitVec.cons true v))
    let A0 := intBvSum k (fun v => ((f (BitVec.cons false v)).natAbs : Int))
    let A1 := intBvSum k (fun v => ((f (BitVec.cons true v)).natAbs : Int))
    let S0 := intBvSum k (fun v => f (BitVec.cons false v) * f (BitVec.cons false v))
    let S1 := intBvSum k (fun v => f (BitVec.cons true v) * f (BitVec.cons true v))
    change (A0 + A1) * (A0 + A1) ≤ (((2 ^ k : Nat) : Int) * 2) * (S0 + S1)
    have hDiffSq : 0 ≤ (A0 - A1) * (A0 - A1) := int_sq_nonneg (A0 - A1)
    have hIdent : (A0 + A1) * (A0 + A1) + (A0 - A1) * (A0 - A1) = 2 * (A0 * A0 + A1 * A1) := by
      simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul]
      rw [Int.mul_comm A1 A0]
      omega
    have hTwoLe : (A0 + A1) * (A0 + A1) ≤ 2 * (A0 * A0 + A1 * A1) := by omega
    have hSumIh : A0 * A0 + A1 * A1 ≤ ((2 ^ k : Nat) : Int) * S0 + ((2 ^ k : Nat) : Int) * S1 :=
      Int.add_le_add ih0 ih1
    have hRhsEq : 2 * (((2 ^ k : Nat) : Int) * S0 + ((2 ^ k : Nat) : Int) * S1) =
        (((2 ^ k : Nat) : Int) * 2) * (S0 + S1) := by
      rw [← Int.mul_add ((2 ^ k : Nat) : Int) S0 S1, ← Int.mul_assoc 2, Int.mul_comm 2 ((2 ^ k : Nat) : Int)]
    exact Int.le_trans hTwoLe (hRhsEq ▸ Int.mul_le_mul_of_nonneg_left hSumIh (by decide))

private theorem intBvSum_fiber_total {inBits m : Nat}
    (h : BitVec inBits → BitVec m) (w : BitVec inBits → Int) :
    intBvSum m (fun y => intBvSum inBits (fun x => if h x = y then w x else 0)) =
      intBvSum inBits w := by
  rw [intBvSum_comm]
  apply intBvSum_congr; intro x
  have hFactor : ∀ y : BitVec m,
      (if h x = y then w x else 0) = w x * (if y = h x then 1 else 0) := by
    intro y
    by_cases hy : y = h x
    · subst hy; simp only [↓reduceIte, Int.mul_one]
    · have hne : h x ≠ y := fun heq => hy heq.symm
      simp only [hy, hne, ↓reduceIte, Int.mul_zero]
  rw [intBvSum_congr hFactor, intBvSum_mul_left, intBvSum_indicator_one, Int.mul_one]

private theorem intBvSum_fiber_sq {inBits m : Nat}
    (h : BitVec inBits → BitVec m) (w : BitVec inBits → Int) :
    intBvSum m (fun y =>
      let M := intBvSum inBits (fun x => if h x = y then w x else 0)
      M * M) =
    intBvSum inBits (fun x => intBvSum inBits (fun x' => if h x = h x' then w x * w x' else 0)) := by
  have hExpandY : ∀ y : BitVec m,
      (intBvSum inBits (fun x => if h x = y then w x else 0)) *
      (intBvSum inBits (fun x' => if h x' = y then w x' else 0)) =
      intBvSum inBits (fun x => intBvSum inBits (fun x' =>
        (if h x = y then w x else 0) * (if h x' = y then w x' else 0))) := by
    intro y
    rw [← intBvSum_mul_right]
    apply intBvSum_congr; intro x
    rw [← intBvSum_mul_left]
  rw [intBvSum_congr hExpandY, intBvSum_comm]
  apply intBvSum_congr; intro x
  rw [intBvSum_comm]
  apply intBvSum_congr; intro x'
  by_cases hEq : h x = h x'
  · simp only [hEq, ↓reduceIte]
    have hPair : ∀ y : BitVec m,
        (if h x' = y then w x else 0) * (if h x' = y then w x' else 0) =
          (w x * w x') * (if y = h x' then 1 else 0) := by
      intro y
      by_cases hy : y = h x'
      · subst hy; simp only [↓reduceIte, Int.mul_one]
      · have hne : h x' ≠ y := fun he => hy he.symm
        simp only [hy, hne, ↓reduceIte, Int.mul_zero]
    rw [intBvSum_congr hPair, intBvSum_mul_left, intBvSum_indicator_one, Int.mul_one]
  · simp only [hEq, ↓reduceIte]
    have hZero : ∀ y : BitVec m,
        (if h x = y then w x else 0) * (if h x' = y then w x' else 0) = 0 := by
      intro y
      by_cases hy : h x = y
      · subst hy
        have hne' : h x' ≠ h x := fun he => hEq he.symm
        simp only [↓reduceIte, hne', Int.mul_zero]
      · simp only [hy, ↓reduceIte, Int.zero_mul]
    rw [intBvSum_congr hZero, intBvSum_const, Int.mul_zero]

/-- Unnormalized $L_1$ statistical distance numerator of $(R, H_R(X))$ from uniform $\mathcal{R} \times \mathrm{BitVec}\, m$.
    Dividing `lhlScaledL1 H w` by `2 * 2^seedBits * 2^m * W` yields exact total variation distance $\Delta_{\mathrm{TV}}$. -/
def lhlScaledL1 {seedBits inBits m : Nat}
    (H : BitVec seedBits → BitVec inBits → BitVec m)
    (w : BitVec inBits → Nat) : Nat :=
  bvSum seedBits (fun R =>
    bvSum m (fun y =>
      natDist
        ((2 ^ m) * bvSum inBits (fun x => if H R x = y then w x else 0))
        (bvSum inBits w)))

/-- **Constructive Finite Leftover Hash Lemma / Collision-Entropy Bound (`finite_lhl_collision_bound`)**:
    For ANY 2-universal hash family `H : BitVec seedBits → BitVec inBits → BitVec m` (`m ≤ seedBits`)
    and ANY finite source mass distribution `w : BitVec inBits → Nat` with total mass `W = bvSum inBits w > 0`
    and collision mass `C2 = bvSum inBits (fun x => w x * w x)`:
    $$\Delta_{\mathrm{TV}}\big((R, H_R(X)),\, U_{\mathcal{R}} \times U_m\big)^2 \le \frac{2^m \cdot C_2}{4 \cdot W^2},$$
    certified constructively via `ratLe (L1^2, (2 * K * 2^m * W)^2) (2^m * C2, 4 * W^2)` (`0 Classical.choice`)! -/
theorem finite_lhl_collision_bound {seedBits inBits m : Nat}
    (H : BitVec seedBits → BitVec inBits → BitVec m)
    (hLeBits : m ≤ seedBits)
    (hTwoUniv : ∀ x x' : BitVec inBits, x ≠ x' →
      intBvSum seedBits (fun R => if H R x = H R x' then 1 else 0) ≤
        ((2 ^ (seedBits - m) : Nat) : Int))
    (w : BitVec inBits → Nat)
    (hWPos : 0 < bvSum inBits w) :
    let K := 2 ^ seedBits
    let W := bvSum inBits w
    let C2 := bvSum inBits (fun x => w x * w x)
    let L1 := lhlScaledL1 H w
    L1 * L1 ≤ K * K * (2 ^ (3 * m)) * C2 ∧
    ratLe (L1 * L1, (2 * K * (2 ^ m) * W) * (2 * K * (2 ^ m) * W))
          ((2 ^ m) * C2, 4 * (W * W)) := by
  intro K W C2 L1
  let wInt : BitVec inBits → Int := fun x => (w x : Int)
  let WInt : Int := intBvSum inBits wInt
  let C2Int : Int := intBvSum inBits (fun x => wInt x * wInt x)
  have hWEq : (W : Int) = WInt := intBvSum_of_bvSum inBits w
  have hC2Eq : (C2 : Int) = C2Int := by
    rw [intBvSum_of_bvSum]
    apply intBvSum_congr; intro x; exact Int.natCast_mul (w x) (w x)
  let diffFn : BitVec seedBits → BitVec m → Int := fun R y =>
    ((2 ^ m : Nat) : Int) * intBvSum inBits (fun x => if H R x = y then wInt x else 0) - WInt
  have hNatAbsEq : ∀ (a b : Nat), (natDist a b : Int) = (((a : Int) - (b : Int)).natAbs : Int) := by
    intro a b; unfold natDist; split <;> omega
  have hL1Int : (L1 : Int) = intBvSum seedBits (fun R => intBvSum m (fun y => ((diffFn R y).natAbs : Int))) := by
    dsimp only [L1]
    unfold lhlScaledL1
    rw [intBvSum_of_bvSum]
    apply intBvSum_congr; intro R
    rw [intBvSum_of_bvSum]
    apply intBvSum_congr; intro y
    rw [hNatAbsEq, Int.natCast_mul, hWEq]
    have hFib : (bvSum inBits (fun x => if H R x = y then w x else 0) : Int) =
        intBvSum inBits (fun x => if H R x = y then wInt x else 0) := by
      rw [intBvSum_of_bvSum]
      apply intBvSum_congr; intro x; split <;> rfl
    rw [hFib]
  -- Variance expansion for each fixed seed `R`:
  have hVarR : ∀ R : BitVec seedBits,
      intBvSum m (fun y => diffFn R y * diffFn R y) =
        ((2 ^ (2 * m) : Nat) : Int) *
          intBvSum inBits (fun x => intBvSum inBits (fun x' => if H R x = H R x' then wInt x * wInt x' else 0)) -
        ((2 ^ m : Nat) : Int) * (WInt * WInt) := by
    intro R
    let M : BitVec m → Int := fun y => intBvSum inBits (fun x => if H R x = y then wInt x else 0)
    have hExpandSq : ∀ y : BitVec m,
        diffFn R y * diffFn R y =
          (((2 ^ (2 * m) : Nat) : Int) * (M y * M y) - (2 * ((2 ^ m : Nat) : Int) * WInt) * M y) + WInt * WInt := by
      intro y
      have hPow2m : ((2 ^ (2 * m) : Nat) : Int) = ((2 ^ m : Nat) : Int) * ((2 ^ m : Nat) : Int) := by
        rw [← Int.natCast_mul, ← Nat.pow_add, Nat.two_mul]
      dsimp only [diffFn, M]
      rw [hPow2m]
      let P := ((2 ^ m : Nat) : Int)
      let My := intBvSum inBits (fun x => if H R x = y then wInt x else 0)
      show (P * My - WInt) * (P * My - WInt) =
        ((P * P) * (My * My) - (2 * P * WInt) * My) + WInt * WInt
      calc
        (P * My - WInt) * (P * My - WInt)
          = (P * My) * (P * My) - (P * My) * WInt - WInt * (P * My) + WInt * WInt := by
            simp only [Int.sub_mul, Int.mul_sub]; omega
        _ = (P * P) * (My * My) - (2 * P * WInt) * My + WInt * WInt := by
            have h1 : (P * My) * (P * My) = (P * P) * (My * My) := by
              rw [Int.mul_assoc P My (P * My), ← Int.mul_assoc My P My, Int.mul_comm My P,
                  Int.mul_assoc P My My, ← Int.mul_assoc P P (My * My)]
            have h2 : (P * My) * WInt = (P * WInt) * My := by
              rw [Int.mul_assoc, Int.mul_comm My WInt, ← Int.mul_assoc]
            have h3 : WInt * (P * My) = (P * WInt) * My := by
              rw [← Int.mul_assoc, Int.mul_comm WInt P]
            rw [h1, h2, h3]
            have h4 : (2 * P * WInt) * My = (P * WInt) * My + (P * WInt) * My := by
              have : 2 * P * WInt = P * WInt + P * WInt := by
                rw [Int.mul_assoc]; omega
              rw [this, Int.add_mul]
            omega
    rw [intBvSum_congr hExpandSq, intBvSum_add, intBvSum_sub,
        intBvSum_mul_left, intBvSum_mul_left, intBvSum_const,
        intBvSum_fiber_total (H R) wInt, intBvSum_fiber_sq (H R) wInt]
    let S := intBvSum inBits (fun x => intBvSum inBits (fun x' => if H R x = H R x' then wInt x * wInt x' else 0))
    let P := ((2 ^ m : Nat) : Int)
    let P2 := ((2 ^ (2 * m) : Nat) : Int)
    show (P2 * S - (2 * P * WInt) * WInt) + P * (WInt * WInt) = P2 * S - P * (WInt * WInt)
    have hMid : (2 * P * WInt) * WInt = P * (WInt * WInt) + P * (WInt * WInt) := by
      have : 2 * P * WInt = P * WInt + P * WInt := by
        rw [Int.mul_assoc]; omega
      rw [this, Int.add_mul, Int.mul_assoc]
    omega
  -- Sum variance across all `R ∈ BitVec seedBits` and apply 2-universality:
  have hPairBound : ∀ x x' : BitVec inBits,
      intBvSum seedBits (fun R => if H R x = H R x' then wInt x * wInt x' else 0) ≤
        (if x = x' then ((K : Nat) : Int) else ((2 ^ (seedBits - m) : Nat) : Int)) * (wInt x * wInt x') := by
    intro x x'
    have hFactor : ∀ R : BitVec seedBits,
        (if H R x = H R x' then wInt x * wInt x' else 0) =
          (if H R x = H R x' then 1 else 0) * (wInt x * wInt x') := by
      intro R; split <;> simp only [Int.one_mul, Int.zero_mul]
    rw [intBvSum_congr hFactor, intBvSum_mul_right]
    have hNonneg : 0 ≤ wInt x * wInt x' := Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    by_cases hxx : x = x'
    · subst hxx
      simp only [↓reduceIte, intBvSum_const, Int.mul_one]
      exact Int.le_refl _
    · simp only [hxx, ↓reduceIte]
      exact Int.mul_le_mul_of_nonneg_right (hTwoUniv x x' hxx) hNonneg
  have hSumCollLe :
      intBvSum seedBits (fun R =>
        intBvSum inBits (fun x => intBvSum inBits (fun x' => if H R x = H R x' then wInt x * wInt x' else 0))) ≤
      (K : Int) * C2Int + ((2 ^ (seedBits - m) : Nat) : Int) * (WInt * WInt) := by
    rw [intBvSum_comm]
    have hExch : ∀ x : BitVec inBits,
        intBvSum seedBits (fun R => intBvSum inBits (fun x' => if H R x = H R x' then wInt x * wInt x' else 0)) =
        intBvSum inBits (fun x' => intBvSum seedBits (fun R => if H R x = H R x' then wInt x * wInt x' else 0)) :=
      fun _ => intBvSum_comm seedBits inBits _
    rw [intBvSum_congr hExch]
    have hStep1 :
        intBvSum inBits (fun x => intBvSum inBits (fun x' =>
          intBvSum seedBits (fun R => if H R x = H R x' then wInt x * wInt x' else 0))) ≤
        intBvSum inBits (fun x => intBvSum inBits (fun x' =>
          (if x = x' then (K : Int) * (wInt x * wInt x') else 0) +
          ((2 ^ (seedBits - m) : Nat) : Int) * (wInt x * wInt x'))) := by
      apply intBvSum_le; intro x; apply intBvSum_le; intro x'
      have hb := hPairBound x x'
      by_cases hxx : x = x'
      · subst hxx
        have hNonneg : 0 ≤ ((2 ^ (seedBits - m) : Nat) : Int) * (wInt x * wInt x) :=
          Int.mul_nonneg (Int.natCast_nonneg _) (Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _))
        simp only [↓reduceIte] at hb ⊢
        omega
      · simp only [hxx, ↓reduceIte] at hb ⊢
        omega
    have hDiag : intBvSum inBits (fun x => intBvSum inBits (fun x' =>
        if x = x' then (K : Int) * (wInt x * wInt x') else 0)) = (K : Int) * C2Int := by
      have hRow : ∀ x : BitVec inBits,
          intBvSum inBits (fun x' => if x = x' then (K : Int) * (wInt x * wInt x') else 0) =
            (K : Int) * (wInt x * wInt x) := by
        intro x
        have hEqInd : ∀ x' : BitVec inBits,
            (if x = x' then (K : Int) * (wInt x * wInt x') else 0) =
              ((K : Int) * (wInt x * wInt x)) * (if x' = x then 1 else 0) := by
          intro x'
          by_cases hx' : x' = x
          · subst hx'; simp only [↓reduceIte, Int.mul_one]
          · have hne : x ≠ x' := fun he => hx' he.symm
            simp only [hx', hne, ↓reduceIte, Int.mul_zero]
        rw [intBvSum_congr hEqInd, intBvSum_mul_left, intBvSum_indicator_one, Int.mul_one]
      rw [intBvSum_congr hRow, intBvSum_mul_left]
    have hAllPairs : intBvSum inBits (fun x => intBvSum inBits (fun x' =>
        ((2 ^ (seedBits - m) : Nat) : Int) * (wInt x * wInt x'))) =
        ((2 ^ (seedBits - m) : Nat) : Int) * (WInt * WInt) := by
      have hRow : ∀ x : BitVec inBits,
          intBvSum inBits (fun x' => ((2 ^ (seedBits - m) : Nat) : Int) * (wInt x * wInt x')) =
            (((2 ^ (seedBits - m) : Nat) : Int) * wInt x) * WInt := by
        intro x
        have hAssoc : ∀ x' : BitVec inBits,
            ((2 ^ (seedBits - m) : Nat) : Int) * (wInt x * wInt x') =
              (((2 ^ (seedBits - m) : Nat) : Int) * wInt x) * wInt x' :=
          fun _ => (Int.mul_assoc _ _ _).symm
        rw [intBvSum_congr hAssoc, intBvSum_mul_left]
      rw [intBvSum_congr hRow, intBvSum_mul_right, intBvSum_mul_left, Int.mul_assoc]
    have hSplitSum :
        intBvSum inBits (fun x => intBvSum inBits (fun x' =>
          (if x = x' then (K : Int) * (wInt x * wInt x') else 0) +
          ((2 ^ (seedBits - m) : Nat) : Int) * (wInt x * wInt x'))) =
        (K : Int) * C2Int + ((2 ^ (seedBits - m) : Nat) : Int) * (WInt * WInt) := by
      have hIn : ∀ x : BitVec inBits,
          intBvSum inBits (fun x' =>
            (if x = x' then (K : Int) * (wInt x * wInt x') else 0) +
            ((2 ^ (seedBits - m) : Nat) : Int) * (wInt x * wInt x')) =
          intBvSum inBits (fun x' => if x = x' then (K : Int) * (wInt x * wInt x') else 0) +
          intBvSum inBits (fun x' => ((2 ^ (seedBits - m) : Nat) : Int) * (wInt x * wInt x')) :=
        fun _ => intBvSum_add _ _
      rw [intBvSum_congr hIn, intBvSum_add, hDiag, hAllPairs]
    exact hSplitSum ▸ hStep1
  have hTotVarLe :
      intBvSum seedBits (fun R => intBvSum m (fun y => diffFn R y * diffFn R y)) ≤
        ((2 ^ (2 * m) : Nat) : Int) * ((K : Int) * C2Int) := by
    rw [intBvSum_congr hVarR, intBvSum_sub, intBvSum_mul_left, intBvSum_const]
    have hMul := Int.mul_le_mul_of_nonneg_left hSumCollLe (Int.natCast_nonneg (2 ^ (2 * m)))
    rw [Int.mul_add] at hMul
    have hCancelTerm :
        ((2 ^ (2 * m) : Nat) : Int) * (((2 ^ (seedBits - m) : Nat) : Int) * (WInt * WInt)) =
        (((2 ^ seedBits : Nat) : Int)) * (((2 ^ m : Nat) : Int) * (WInt * WInt)) := by
      rw [← Int.mul_assoc ((2 ^ (2 * m) : Nat) : Int), ← Int.mul_assoc ((2 ^ seedBits : Nat) : Int),
          ← Int.natCast_mul, ← Int.natCast_mul]
      congr 2
      rw [← Nat.pow_add, ← Nat.pow_add]
      congr 1
      omega
    dsimp only [K] at hMul ⊢
    rw [hCancelTerm] at hMul
    omega
  -- Apply two-level constructive Cauchy-Schwarz (`seedBits` then `m`):
  have hCsTotal : (L1 : Int) * (L1 : Int) ≤
      (K : Int) * ((2 ^ m : Nat) : Int) *
        intBvSum seedBits (fun R => intBvSum m (fun y => diffFn R y * diffFn R y)) := by
    rw [hL1Int]
    let rowAbs : BitVec seedBits → Int := fun R => intBvSum m (fun y => ((diffFn R y).natAbs : Int))
    have hOuter := intBvSum_abs_sq_le seedBits rowAbs
    have hAbsRowEq : intBvSum seedBits (fun R => ((rowAbs R).natAbs : Int)) = intBvSum seedBits rowAbs := by
      apply intBvSum_congr; intro R
      have hNonneg : 0 ≤ rowAbs R := by
        dsimp only [rowAbs]
        have hZeroLe : ∀ y : BitVec m, (0 : Int) ≤ ((diffFn R y).natAbs : Int) :=
          fun _ => Int.natCast_nonneg _
        have h1 := intBvSum_le hZeroLe
        rw [intBvSum_const, Int.mul_zero] at h1
        exact h1
      omega
    rw [hAbsRowEq] at hOuter
    have hInnerEach : ∀ R : BitVec seedBits,
        rowAbs R * rowAbs R ≤ ((2 ^ m : Nat) : Int) * intBvSum m (fun y => diffFn R y * diffFn R y) :=
      fun R => intBvSum_abs_sq_le m (diffFn R)
    have hSumInner := intBvSum_le hInnerEach
    rw [intBvSum_mul_left] at hSumInner
    have hStep := Int.le_trans hOuter (Int.mul_le_mul_of_nonneg_left hSumInner (Int.natCast_nonneg K))
    simpa only [Int.mul_assoc] using hStep
  have hFinalInt : (L1 : Int) * (L1 : Int) ≤
      (((K * K * (2 ^ (3 * m)) * C2 : Nat) : Int)) := by
    have h1 := Int.le_trans hCsTotal
      (Int.mul_le_mul_of_nonneg_left hTotVarLe
        (Int.mul_nonneg (Int.natCast_nonneg K) (Int.natCast_nonneg (2 ^ m))))
    have hRhs : (K : Int) * ((2 ^ m : Nat) : Int) * (((2 ^ (2 * m) : Nat) : Int) * ((K : Int) * C2Int)) =
        (((K * K * (2 ^ (3 * m)) * C2 : Nat) : Int)) := by
      rw [← hC2Eq]
      simp only [Int.natCast_mul]
      have hPow3m : ((2 ^ m : Nat) : Int) * ((2 ^ (2 * m) : Nat) : Int) = ((2 ^ (3 * m) : Nat) : Int) := by
        rw [← Int.natCast_mul, ← Nat.pow_add]; congr 2; omega
      calc
        (K : Int) * ((2 ^ m : Nat) : Int) * (((2 ^ (2 * m) : Nat) : Int) * ((K : Int) * (C2 : Int)))
          = ((K : Int) * (K : Int)) * (((2 ^ m : Nat) : Int) * ((2 ^ (2 * m) : Nat) : Int)) * (C2 : Int) := by
            simp only [Int.mul_assoc]
            rw [Int.mul_comm ((2 ^ m : Nat) : Int) (((2 ^ (2 * m) : Nat) : Int) * ((K : Int) * (C2 : Int))),
                Int.mul_assoc ((2 ^ (2 * m) : Nat) : Int) ((K : Int) * (C2 : Int)) ((2 ^ m : Nat) : Int),
                Int.mul_comm ((K : Int) * (C2 : Int)) ((2 ^ m : Nat) : Int),
                ← Int.mul_assoc ((2 ^ (2 * m) : Nat) : Int) ((2 ^ m : Nat) : Int),
                Int.mul_comm ((2 ^ (2 * m) : Nat) : Int) ((2 ^ m : Nat) : Int),
                ← Int.mul_assoc (((2 ^ m : Nat) : Int) * ((2 ^ (2 * m) : Nat) : Int)) (K : Int) (C2 : Int),
                Int.mul_comm (((2 ^ m : Nat) : Int) * ((2 ^ (2 * m) : Nat) : Int)) (K : Int),
                ← Int.mul_assoc (K : Int) (K : Int)]
            simp only [Int.mul_assoc]
        _ = (K : Int) * (K : Int) * ((2 ^ (3 * m) : Nat) : Int) * (C2 : Int) := by rw [hPow3m]
    exact hRhs ▸ h1
  have hMainNat : L1 * L1 ≤ K * K * (2 ^ (3 * m)) * C2 := by
    rw [← Int.natCast_mul] at hFinalInt
    exact Int.ofNat_le.mp hFinalInt
  refine ⟨hMainNat, ?_⟩
  unfold ratLe
  have hKPos : 0 < K := Nat.two_pow_pos seedBits
  have h2mPos : 0 < 2 ^ m := Nat.two_pow_pos m
  have hDen1Pos : 0 < (2 * K * (2 ^ m) * W) * (2 * K * (2 ^ m) * W) := by
    have hHalf : 0 < 2 * K * (2 ^ m) * W :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) hKPos) h2mPos) hWPos
    exact Nat.mul_pos hHalf hHalf
  have hDen2Pos : 0 < 4 * (W * W) := Nat.mul_pos (by decide) (Nat.mul_pos hWPos hWPos)
  refine ⟨hDen1Pos, hDen2Pos, ?_⟩
  have hMul := Nat.mul_le_mul_right (4 * (W * W)) hMainNat
  have hEqRhs : K * K * (2 ^ (3 * m)) * C2 * (4 * (W * W)) =
      (2 ^ m) * C2 * ((2 * K * (2 ^ m) * W) * (2 * K * (2 ^ m) * W)) := by
    have hPowSplit : 2 ^ (3 * m) = (2 ^ m) * ((2 ^ m) * (2 ^ m)) := by
      rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
    rw [hPowSplit]
    let k := K; let p := 2 ^ m; let c := C2; let w0 := W
    show k * k * (p * (p * p)) * c * (4 * (w0 * w0)) =
      p * c * ((2 * k * p * w0) * (2 * k * p * w0))
    have hSq : (2 * k * p * w0) * (2 * k * p * w0) = 4 * (k * k) * (p * p) * (w0 * w0) := by
      calc
        (2 * k * p * w0) * (2 * k * p * w0)
          = (2 * 2) * (k * k) * (p * p) * (w0 * w0) := by
            simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        _ = 4 * (k * k) * (p * p) * (w0 * w0) := rfl
    rw [hSq]
    simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  exact hEqRhs ▸ hMul

private theorem bvSum_bool_le_two_pow (k : Nat) (pred : BitVec k → Bool) :
    bvSum k (fun x => if pred x then 1 else 0) ≤ 2 ^ k := by
  have hInt : intBvSum k (fun x => (((if pred x then 1 else 0 : Nat) : Int))) ≤
      intBvSum k (fun _ => 1) := by
    apply intBvSum_le; intro x; split <;> decide
  rw [← intBvSum_of_bvSum, intBvSum_const, Int.mul_one] at hInt
  exact Int.ofNat_le.mp hInt

private theorem lhl_part1_lhs_rearr (L2 WW Pm Pm2 Pn : Nat)
    (hPn : Pn = Pm * Pm) (hPm2 : Pm2 = Pm * 4) :
    L2 * (4 * WW) * Pn = (Pm * WW) * (L2 * Pm2) := by
  subst hPn; subst hPm2
  simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

private theorem lhl_part1_rhs_rearr (Pm C2 D2 Pn : Nat) :
    Pm * C2 * D2 * Pn = Pm * (C2 * Pn) * D2 := by
  simp only [Nat.mul_left_comm, Nat.mul_comm]

private theorem lhl_part2_lhs_rearr (L1 P P2m2 : Nat) :
    (L1 * L1) * (4 * (P * P)) * (P * P2m2) =
      (4 * P) * ((P * L1) * (P * L1) * P2m2) := by
  simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

private theorem lhl_part2_rhs_rearr (Pm P D2 P2m2 Pnm : Nat)
    (hPow : Pm * P2m2 = 4 * Pnm) :
    Pm * P * D2 * (P * P2m2) = (4 * P) * ((P * Pnm) * D2) := by
  calc
    Pm * P * D2 * (P * P2m2)
      = (Pm * P2m2) * (P * P * D2) := by
        simp only [Nat.mul_left_comm, Nat.mul_comm]
    _ = (4 * Pnm) * (P * P * D2) := by rw [hPow]
    _ = (4 * P) * ((P * Pnm) * D2) := by
        simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

private theorem lhl_part2_jden_sq (Pnm D0 : Nat) :
    1 * ((Pnm * D0) * (Pnm * D0)) = (Pnm * Pnm) * (D0 * D0) := by
  rw [Nat.one_mul]
  simp only [Nat.mul_assoc, Nat.mul_left_comm]

/-- Parametric Leftover Hash Lemma & joint selective-failure bound for any 2-universal hash `H`. -/
theorem lhl_security_of_two_universal {seedBits inBits m : Nat}
    (n m2 m22 : Nat)
    (H : BitVec seedBits → BitVec inBits → BitVec m)
    (hLeBits : m ≤ seedBits)
    (hInEq : inBits = n + m)
    (h2m : n = 2 * m)
    (hm2 : m2 = m + 2)
    (hm22 : m22 = 2 * m + 2)
    (hTwoUniv : ∀ x x' : BitVec inBits, x ≠ x' →
      intBvSum seedBits (fun R => if H R x = H R x' then 1 else 0) ≤
        ((2 ^ (seedBits - m) : Nat) : Int)) :
    let K := 2 ^ seedBits
    (∀ (w : BitVec inBits → Nat),
      0 < bvSum inBits w →
      bvSum inBits (fun x => w x * w x) * (2 ^ n) ≤ (bvSum inBits w) * (bvSum inBits w) →
      let W := bvSum inBits w
      let L1 := lhlScaledL1 H w
      let Den := 2 * K * (2 ^ m) * W
      ratLe (L1 * L1, Den * Den) (1, 2 ^ m2)) ∧
    (∀ (passPred : BitVec inBits → Bool),
      let wEvent : BitVec inBits → Nat := fun x => if passPred x then 1 else 0
      let passCount := bvSum inBits wEvent
      0 < passCount →
      let L1 := lhlScaledL1 H wEvent
      let jointNum := passCount * L1
      let jointDen := (2 ^ inBits) * (2 * K * (2 ^ m) * passCount)
      ratLe (jointNum * jointNum, jointDen * jointDen) (1, 2 ^ m22)) := by
  intro K
  constructor
  · intro w hWPos hEnt W L1 Den
    have hBase := (finite_lhl_collision_bound H hLeBits hTwoUniv w hWPos).2
    unfold ratLe at hBase ⊢
    dsimp only at hBase ⊢
    refine ⟨hBase.1, Nat.two_pow_pos m2, ?_⟩
    have hWWPos : 0 < W * W := Nat.mul_pos hWPos hWPos
    have hPn : 2 ^ n = (2 ^ m) * (2 ^ m) := by rw [h2m, Nat.two_mul, Nat.pow_add]
    have hPm2 : 2 ^ m2 = (2 ^ m) * 4 := by rw [hm2, Nat.pow_succ, Nat.pow_succ, Nat.mul_assoc]
    have hStep1 := Nat.mul_le_mul_right (2 ^ n) hBase.2.2
    have hStep2 : (2 ^ m) * bvSum inBits (fun x => w x * w x) * (Den * Den) * (2 ^ n) ≤
        ((2 ^ m) * (W * W)) * (1 * (Den * Den)) := by
      rw [lhl_part1_rhs_rearr, Nat.one_mul]
      dsimp only [W]
      exact Nat.mul_le_mul_right (Den * Den) (Nat.mul_le_mul_left (2 ^ m) hEnt)
    have hCombined := Nat.le_trans hStep1 hStep2
    rw [lhl_part1_lhs_rearr (L1 * L1) (W * W) (2 ^ m) (2 ^ m2) (2 ^ n) hPn hPm2] at hCombined
    exact Nat.le_of_mul_le_mul_left hCombined (Nat.mul_pos (Nat.two_pow_pos m) hWWPos)
  · intro passPred wEvent passCount hPassPos L1 jointNum jointDen
    have hC2Eq : bvSum inBits (fun x => wEvent x * wEvent x) = passCount := by
      dsimp only [passCount, wEvent]
      apply bvSum_congr; intro x; cases passPred x <;> rfl
    have hPassMax : passCount ≤ 2 ^ inBits := bvSum_bool_le_two_pow inBits passPred
    have hBase := (finite_lhl_collision_bound H hLeBits hTwoUniv wEvent hPassPos).2
    rw [hC2Eq] at hBase
    unfold ratLe at hBase ⊢
    dsimp only at hBase ⊢
    let D0 := 2 * K * (2 ^ m) * passCount
    have hD0Pos : 0 < D0 :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) (Nat.two_pow_pos seedBits)) (Nat.two_pow_pos m)) hPassPos
    have hDenPos : 0 < jointDen * jointDen :=
      Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos inBits) hD0Pos)
                  (Nat.mul_pos (Nat.two_pow_pos inBits) hD0Pos)
    refine ⟨hDenPos, Nat.two_pow_pos m22, ?_⟩
    have hPow : (2 ^ m) * (2 ^ m22) = 4 * (2 ^ inBits) := by
      have h1 : 2 ^ m22 = (2 ^ (2 * m)) * 4 := by
        rw [hm22, Nat.pow_succ, Nat.pow_succ, Nat.mul_assoc]
      have h2 : 2 ^ inBits = (2 ^ (2 * m)) * (2 ^ m) := by
        rw [hInEq, h2m, Nat.pow_add]
      rw [h1, h2]
      simp only [Nat.mul_assoc, Nat.mul_comm]
    have hStep1 := Nat.mul_le_mul_right (passCount * (2 ^ m22)) hBase.2.2
    have hLhs := lhl_part2_lhs_rearr L1 passCount (2 ^ m22)
    have hRhs := lhl_part2_rhs_rearr (2 ^ m) passCount (D0 * D0) (2 ^ m22) (2 ^ inBits) hPow
    dsimp only [K, D0] at hStep1 hRhs ⊢
    rw [hLhs, hRhs] at hStep1
    have hRhsLe : (4 * passCount) * ((passCount * (2 ^ inBits)) * ((2 * (2 ^ seedBits) * (2 ^ m) * passCount) * (2 * (2 ^ seedBits) * (2 ^ m) * passCount))) ≤
        (4 * passCount) * (1 * (jointDen * jointDen)) := by
      apply Nat.mul_le_mul_left
      dsimp only [jointDen, K]
      rw [lhl_part2_jden_sq]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right (2 ^ inBits) hPassMax)
    exact Nat.le_of_mul_le_mul_left (Nat.le_trans hStep1 hRhsLe) (Nat.mul_pos (by decide) hPassPos)

private theorem evalGf2Combiner128x384_two_universal :
    ∀ x x' : BitVec 384, x ≠ x' →
      intBvSum 32768 (fun R => if evalGf2Combiner128x384 R x = evalGf2Combiner128x384 R x' then 1 else 0) ≤
        ((2 ^ (32768 - 128) : Nat) : Int) := by
  have hGen : ∀ (n m seedBits inBits : Nat), 1 ≤ n → n * m = seedBits → n + m = inBits →
      ∀ (H : BitVec seedBits → BitVec inBits → BitVec m),
      HEq H (evalSystematicGF2 n m) →
      ∀ x x' : BitVec inBits, x ≠ x' →
        intBvSum seedBits (fun R => if H R x = H R x' then 1 else 0) ≤
          ((2 ^ (seedBits - m) : Nat) : Int) := by
    intro n m seedBits inBits hn hSeed hIn H hHEq
    subst hSeed; subst hIn
    cases hHEq
    exact evalSystematicGF2_two_universal n m hn
  exact hGen 256 128 32768 384 (by decide) rfl rfl evalGf2Combiner128x384 HEq.rfl

/-- **`128 × 384` `GF(2)` Combiner Leftover Hash Lemma After `s = 128` Leakage Bits & Joint Selective-Failure Closure (`kos_combiner_128x384_lhl_security`)**:
    Instantiating `finite_lhl_collision_bound` with the actual `128 × 384` `GF(2)` universal linear hash
    `evalGf2Combiner128x384 = evalSystematicGF2 256 128`:
    1. **128-Bit Leakage Bound (`s = 128` on `384`-bit high-entropy source)**: For ANY source distribution
       `w : BitVec 384 → Nat` with collision entropy $H_2(X) \ge 384 - 128 = 256$ bits
       (`C2 * 2^256 ≤ W^2`), statistical distance squared satisfies
       `ratLe (L1^2, Den^2) (1, 2^130)` (`Δ_TV ≤ 2^(-65) < 2^(-64)`)!
    2. **Unconditional Joint Selective-Failure Security (`p * Δ_TV < 2^(-128)`)**: For **EVERY** non-empty
       adversarial pass predicate `passPred : BitVec 384 → Bool` (`0 < passCount`), the joint pass-and-distinguish
       advantage `(passCount / 2^384) * Δ_TV` satisfies `ratLe (jointNum^2, jointDen^2) (1, 2^258)`
       (`jointAdv ≤ 2^(-129) < 2^(-128)` unconditionally across all fault weights $0 \le w \le 384$)! -/
theorem kos_combiner_128x384_lhl_security :
    let K := 2 ^ 32768
    (∀ (w : BitVec 384 → Nat),
      0 < bvSum 384 w →
      bvSum 384 (fun x => w x * w x) * (2 ^ 256) ≤ (bvSum 384 w) * (bvSum 384 w) →
      let W := bvSum 384 w
      let L1 := lhlScaledL1 evalGf2Combiner128x384 w
      let Den := 2 * K * (2 ^ 128) * W
      ratLe (L1 * L1, Den * Den) (1, 2 ^ 130)) ∧
    (∀ (passPred : BitVec 384 → Bool),
      let wEvent : BitVec 384 → Nat := fun x => if passPred x then 1 else 0
      let passCount := bvSum 384 wEvent
      0 < passCount →
      let L1 := lhlScaledL1 evalGf2Combiner128x384 wEvent
      let jointNum := passCount * L1
      let jointDen := (2 ^ 384) * (2 * K * (2 ^ 128) * passCount)
      ratLe (jointNum * jointNum, jointDen * jointDen) (1, 2 ^ 258)) :=
  lhl_security_of_two_universal 256 130 258 evalGf2Combiner128x384 (by decide) rfl rfl rfl rfl
    evalGf2Combiner128x384_two_universal


/-! ## 4. Legacy Single-Tree GGM / SPCOT Model (V3 Forest Specification Below) -/

/-! ### 4.1 Binary GGM Tree Expansion (`depth d`) & Punctured Co-Path Evaluation -/

/-- Level-domain-separated length-doubling 128-bit PRG `lvl → BitVec 128 → (BitVec 128 × BitVec 128)`. -/
abbrev GgmPrg := Nat → BitVec 128 → BitVec 128 × BitVec 128

/-- Full depth-`d` binary GGM tree expansion mapping leaf index `idx : BitVec d` to its 128-bit leaf seed. -/
@[expose] def ggmExpandFull (prg : GgmPrg) : (d : Nat) → Nat → BitVec 128 → BitVec d → BitVec 128
  | 0, _, seed, _ => seed
  | d + 1, lvl, seed, idx =>
    let (sL, sR) := prg lvl seed
    if idx.getLsbD d then
      ggmExpandFull prg d (lvl + 1) sR (idx.setWidth d)
    else
      ggmExpandFull prg d (lvl + 1) sL (idx.setWidth d)

/-- `d`-element sibling co-path for a punctured GGM tree of depth `d`. -/
@[expose] def GgmCopath : Nat → Type
  | 0 => Unit
  | d + 1 => BitVec 128 × GgmCopath d

/-- Construct the `d`-sibling co-path puncturing leaf `pStar : BitVec d` from root `seed`. -/
def ggmMakeCopath (prg : GgmPrg) : (d : Nat) → Nat → BitVec 128 → BitVec d → GgmCopath d
  | 0, _, _, _ => ()
  | d + 1, lvl, seed, pStar =>
    let (sL, sR) := prg lvl seed
    if pStar.getLsbD d then
      (sL, ggmMakeCopath prg d (lvl + 1) sR (pStar.setWidth d))
    else
      (sR, ggmMakeCopath prg d (lvl + 1) sL (pStar.setWidth d))

/-- Receiver's punctured GGM tree evaluator: evaluates all `u ≠ pStar` from `copath` and outputs `0#128` at `pStar`. -/
@[expose] def ggmExpandPunctured (prg : GgmPrg) :
    (d : Nat) → Nat → BitVec d → GgmCopath d → BitVec d → BitVec 128
  | 0, _, _, _, _ => 0#128
  | d + 1, lvl, pStar, (sibSeed, rest), idx =>
    if idx.getLsbD d = pStar.getLsbD d then
      ggmExpandPunctured prg d (lvl + 1) (pStar.setWidth d) rest (idx.setWidth d)
    else
      ggmExpandFull prg d (lvl + 1) sibSeed (idx.setWidth d)

/-- **Exact Punctured GGM Tree Recovery (`ggmExpandPunctured_exact`)**:
    For every depth $d$ (including deployed $d \in \{14, 15\}$), root `seed`, and puncture `pStar : BitVec d`:
    1. At `u = pStar`, `ggmExpandPunctured` evaluates to `0#128`.
    2. At every `u ≠ pStar`, `ggmExpandPunctured` recovers the **exact** sender leaf `ggmExpandFull prg d lvl seed u`! -/
theorem ggmExpandPunctured_exact (prg : GgmPrg) :
    ∀ (d lvl : Nat) (seed : BitVec 128) (pStar : BitVec d),
      let copath := ggmMakeCopath prg d lvl seed pStar
      ggmExpandPunctured prg d lvl pStar copath pStar = 0#128 ∧
      (∀ u : BitVec d, u ≠ pStar →
        ggmExpandPunctured prg d lvl pStar copath u = ggmExpandFull prg d lvl seed u)
  | 0, _, _, pStar => by
    dsimp only
    refine ⟨rfl, ?_⟩
    intro u hNe
    exact False.elim (hNe ((BitVec.eq_nil u).trans (BitVec.eq_nil pStar).symm))
  | d + 1, lvl, seed, pStar => by
    dsimp only
    cases hPrg : prg lvl seed with
    | mk sL sR =>
      cases hp : pStar.getLsbD d
      · have hCp : ggmMakeCopath prg (d + 1) lvl seed pStar =
            (sR, ggmMakeCopath prg d (lvl + 1) sL (pStar.setWidth d)) := by
          simp only [ggmMakeCopath, hPrg, hp, Bool.false_eq_true, ↓reduceIte]; rfl
        rw [hCp]
        have ih := ggmExpandPunctured_exact prg d (lvl + 1) sL (pStar.setWidth d)
        dsimp only at ih
        refine ⟨?_, ?_⟩
        · simp only [ggmExpandPunctured, ↓reduceIte, ih.1]
        · intro u huNe
          have hFull : ggmExpandFull prg (d + 1) lvl seed u =
              if u.getLsbD d then ggmExpandFull prg d (lvl + 1) sR (u.setWidth d)
              else ggmExpandFull prg d (lvl + 1) sL (u.setWidth d) := by
            simp only [ggmExpandFull, hPrg]
          rw [hFull]
          dsimp only [ggmExpandPunctured]
          rw [hp]
          cases hu : u.getLsbD d
          · have huLoNe : u.setWidth d ≠ pStar.setWidth d := by
              intro hEqLo
              apply huNe
              have hSu : BitVec.cons (u.getLsbD d) (u.setWidth d) = u := bvCons_split u
              have hSp : BitVec.cons (pStar.getLsbD d) (pStar.setWidth d) = pStar := bvCons_split pStar
              rw [← hSu, ← hSp, hu, hp, hEqLo]
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact ih.2 (u.setWidth d) huLoNe
          · simp only [Bool.true_eq_false, ↓reduceIte]
      · have hCp : ggmMakeCopath prg (d + 1) lvl seed pStar =
            (sL, ggmMakeCopath prg d (lvl + 1) sR (pStar.setWidth d)) := by
          simp only [ggmMakeCopath, hPrg, hp, ↓reduceIte]; rfl
        rw [hCp]
        have ih := ggmExpandPunctured_exact prg d (lvl + 1) sR (pStar.setWidth d)
        dsimp only at ih
        refine ⟨?_, ?_⟩
        · simp only [ggmExpandPunctured, ↓reduceIte, ih.1]
        · intro u huNe
          have hFull : ggmExpandFull prg (d + 1) lvl seed u =
              if u.getLsbD d then ggmExpandFull prg d (lvl + 1) sR (u.setWidth d)
              else ggmExpandFull prg d (lvl + 1) sL (u.setWidth d) := by
            simp only [ggmExpandFull, hPrg]
          rw [hFull]
          dsimp only [ggmExpandPunctured]
          rw [hp]
          cases hu : u.getLsbD d
          · simp only [Bool.false_eq_true, ↓reduceIte]
          · have huLoNe : u.setWidth d ≠ pStar.setWidth d := by
              intro hEqLo
              apply huNe
              have hSu : BitVec.cons (u.getLsbD d) (u.setWidth d) = u := bvCons_split u
              have hSp : BitVec.cons (pStar.getLsbD d) (pStar.setWidth d) = pStar := bvCons_split pStar
              rw [← hSu, ← hSp, hu, hp, hEqLo]
            simp only [↓reduceIte]
            exact ih.2 (u.setWidth d) huLoNe

/-- Keyed-ROM hiding of the punctured GGM leaf seed (`ggm_punctured_seed_keyed_rom_hiding`):
    Because `root` / punctured path seeds have cardinality `2^128` (`> 0`), any `Q`-query oracle
    distinguisher `A` trying to distinguish the punctured seed expansion from an independent random
    function achieves advantage at most `2 * Q / 2^128` via `UcGames.hidingAdv_le`! -/
theorem ggm_punctured_seed_keyed_rom_hiding {TagDom Cod : Type} (Q : Nat)
    (basePrf : Fin (2 ^ 128) × TagDom → Cod)
    (puncLeafFn : TagDom → Cod)
    (A : OracleComp (Fin (2 ^ 128) × TagDom) Cod Bool)
    (hQb : QueryBounded Q A) :
    ratLe (natAbsDiff (keyedPrfRealAccept (2 ^ 128) basePrf puncLeafFn A)
                      (keyedPrfIdealAccept (2 ^ 128) basePrf A),
           2 ^ 128)
          (2 * Q, 2 ^ 128) :=
  (hidingAdv_le (2 ^ 128) Q (Nat.two_pow_pos 128) basePrf puncLeafFn A hQb).2

/-! ### 4.2 Active SPCOT Consistency Check & Single-Use / Peer-ID Validated `PartyMachine` (`P1-06`) -/

/-- Symbolic hypercube XOR sum $\bigoplus_{u \in \mathrm{BitVec}\, d} f(u)$ over `BitVec 128`. -/
def bvXorSum128 : (d : Nat) → (BitVec d → BitVec 128) → BitVec 128
  | 0, f => f 0#0
  | d + 1, f =>
    bvXorSum128 d (fun u => f (BitVec.cons false u)) ^^^
    bvXorSum128 d (fun u => f (BitVec.cons true u))

private theorem bvXorSum128_congr {d : Nat} {f g : BitVec d → BitVec 128} (h : ∀ u, f u = g u) :
    bvXorSum128 d f = bvXorSum128 d g := by
  induction d with
  | zero => exact h 0#0
  | succ d ih =>
    simp only [bvXorSum128, ih (fun u => h (BitVec.cons false u)),
      ih (fun u => h (BitVec.cons true u))]

private theorem bvXorSum128_zero (d : Nat) : bvXorSum128 d (fun _ => 0#128) = 0#128 := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [bvXorSum128, ih, BitVec.xor_zero]

private theorem bvXor128_four_rearr (a b c e : BitVec 128) :
    (a ^^^ b) ^^^ (c ^^^ e) = (a ^^^ c) ^^^ (b ^^^ e) := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_xor]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> cases e.getLsbD i <;> rfl

private theorem bvXorSum128_xor {d : Nat} (f g : BitVec d → BitVec 128) :
    bvXorSum128 d (fun u => f u ^^^ g u) = bvXorSum128 d f ^^^ bvXorSum128 d g := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [bvXorSum128, ih]
    exact bvXor128_four_rearr _ _ _ _

private theorem bvXorSum128_single : ∀ (d : Nat) (pStar : BitVec d) (val : BitVec 128),
    bvXorSum128 d (fun u => if u = pStar then val else 0#128) = val
  | 0, pStar, val => by
    have hp : pStar = 0#0 := BitVec.eq_nil pStar
    subst hp; rfl
  | d + 1, pStar, val => by
    have hSp : BitVec.cons (pStar.getLsbD d) (pStar.setWidth d) = pStar := bvCons_split pStar
    rw [← hSp]
    simp only [bvXorSum128]
    cases pStar.getLsbD d
    · have hL : bvXorSum128 d (fun u => if BitVec.cons false u = BitVec.cons false (pStar.setWidth d) then val else 0#128) =
          bvXorSum128 d (fun u => if u = pStar.setWidth d then val else 0#128) := by
        apply bvXorSum128_congr; intro u; simp only [bvCons_inj, true_and]
      have hR : bvXorSum128 d (fun u => if BitVec.cons true u = BitVec.cons false (pStar.setWidth d) then val else 0#128) =
          bvXorSum128 d (fun _ => 0#128) := by
        apply bvXorSum128_congr; intro u; simp only [bvCons_inj, Bool.true_eq_false, false_and, ↓reduceIte]
      rw [hL, hR, bvXorSum128_single d, bvXorSum128_zero, BitVec.xor_zero]
    · have hL : bvXorSum128 d (fun u => if BitVec.cons false u = BitVec.cons true (pStar.setWidth d) then val else 0#128) =
          bvXorSum128 d (fun _ => 0#128) := by
        apply bvXorSum128_congr; intro u; simp only [bvCons_inj, Bool.false_eq_true, false_and, ↓reduceIte]
      have hR : bvXorSum128 d (fun u => if BitVec.cons true u = BitVec.cons true (pStar.setWidth d) then val else 0#128) =
          bvXorSum128 d (fun u => if u = pStar.setWidth d then val else 0#128) := by
        apply bvXorSum128_congr; intro u; simp only [bvCons_inj, true_and]
      rw [hL, hR, bvXorSum128_single d, bvXorSum128_zero, BitVec.zero_xor]

/-- Honest SPCOT GGM-sum identity & malicious consistency check soundness (`spcot_consistency_soundness`):
    1. Honest Receiver's `(bvXorSum128 d puncLeaves) ^^^ corrOffset` (with `corrOffset = bvXorSum128 d fullLeaves ^^^ delta`)
       equals `fullLeaves pStar ^^^ delta` identically!
    2. Degree-one core: a single non-zero discrepancy coefficient `errSum ≠ 0#128` multiplied by a
       challenge hits any fixed target for at most one challenge value. This is not yet the bound for
       the production check, whose leaf weights are `chi^(u+1)`: a discrepancy spread over several
       leaves is a polynomial of degree up to `2^d` in `chi`, bounded by
       `spcot_weighted_check_root_bound` (at most `2^d` accepting challenges, not one). -/
theorem spcot_consistency_soundness {d : Nat}
    (fullLeaves puncLeaves : BitVec d → BitVec 128) (pStar : BitVec d) (delta : BitVec 128)
    (hPuncZero : puncLeaves pStar = 0#128)
    (hPuncEq : ∀ u : BitVec d, u ≠ pStar → puncLeaves u = fullLeaves u) :
    let corrOffset := bvXorSum128 d fullLeaves ^^^ delta
    (bvXorSum128 d puncLeaves ^^^ corrOffset = fullLeaves pStar ^^^ delta) ∧
    (∀ (errSum : BitVec 128), errSum ≠ 0#128 →
      ∀ (target chi₁ chi₂ : Tower128),
        towerMul 7 (unpackTower 7 errSum) chi₁ = target →
        towerMul 7 (unpackTower 7 errSum) chi₂ = target →
        chi₁ = chi₂) := by
  intro corrOffset
  have hDiffPoint : ∀ u : BitVec d,
      fullLeaves u ^^^ puncLeaves u = (if u = pStar then fullLeaves pStar else 0#128) := by
    intro u
    by_cases hu : u = pStar
    · subst hu; rw [hPuncZero, BitVec.xor_zero]; simp only [↓reduceIte]
    · rw [hPuncEq u hu, BitVec.xor_self]; simp only [hu, ↓reduceIte]
  have hSumDiff : bvXorSum128 d fullLeaves ^^^ bvXorSum128 d puncLeaves = fullLeaves pStar := by
    rw [← bvXorSum128_xor, bvXorSum128_congr hDiffPoint, bvXorSum128_single]
  refine ⟨?_, ?_⟩
  · dsimp only [corrOffset]
    have hRearr : bvXorSum128 d puncLeaves ^^^ (bvXorSum128 d fullLeaves ^^^ delta) =
        (bvXorSum128 d fullLeaves ^^^ bvXorSum128 d puncLeaves) ^^^ delta := by
      apply BitVec.eq_of_getLsbD_eq; intro i _
      simp only [BitVec.getLsbD_xor]
      cases (bvXorSum128 d puncLeaves).getLsbD i <;>
        cases (bvXorSum128 d fullLeaves).getLsbD i <;>
        cases delta.getLsbD i <;> rfl
    rw [hRearr, hSumDiff]
  · intro errSum hNz target chi₁ chi₂ h1 h2
    have hTowerNz : unpackTower 7 errSum ≠ towerZero 7 := by
      intro hZ
      have hp := congrArg (packTower 7) hZ
      rw [packTower_unpackTower, packTower_zero] at hp
      exact hNz hp
    exact towerMul_cancel_left 7 (unpackTower 7 errSum) chi₁ chi₂ hTowerNz (h1.trans h2.symm)

/-- **Root bound for the `chi^(u+1)`-weighted SPCOT check (`spcot_weighted_check_root_bound`)**:
    one repetition of the production check compares `mask + Σ_u chi^(u+1) · leaf[u]` between the
    sender's full tree and the receiver's reconstruction (`pcg_dense.rs`, step 6). Writing `errBits`
    for the per-leaf discrepancies in leaf order, the two sides agree exactly when `chi` is a root of
    `mask' + Σ_u chi^(u+1) · errBits[u]`. If any leaf discrepancy is non-zero and was fixed before the
    challenge, every duplicate-free list of accepting challenges has length at most
    `m ≥ errBits.length`: `2^d / 2^128` per repetition at tree depth `d`, matching the Rust comment's
    degree count and not `1 / 2^128`.
    The proof is the polynomial-identity lemma behind `kos_batched_poly_check_sound` in
    `Qsag.Preprocessing`: more accepting challenges than coefficients force every coefficient to zero.
    Not covered here: the `gamma` weights across trees, the product bound over the two repetitions,
    and the identification of this coefficient form with `evalPuncturedTreeSpcotCombo`'s
    `spcotLeafWeight` sum. -/
theorem spcot_weighted_check_root_bound (m : Nat) (errBits : List (BitVec 128)) (mask : Tower128)
    (roots : List Tower128) (hNodup : roots.Nodup) (hLen : errBits.length ≤ m)
    (hFault : ∃ e ∈ errBits, e ≠ 0#128)
    (hAll : ∀ chi ∈ roots,
      RoundPoly.evalCoeffs (mask :: errBits.map (fun e => unpackTower 7 e)) chi = towerZero 7) :
    roots.length ≤ m := by
  by_cases hSmall : roots.length ≤ m
  · exact hSmall
  · exfalso
    obtain ⟨e, he, hne⟩ := hFault
    have hLenCs : (mask :: errBits.map (fun e => unpackTower 7 e)).length ≤ roots.length := by
      simp only [List.length_cons, List.length_map]; omega
    have hZero : unpackTower 7 e = towerZero 7 :=
      poly_coeffs_zero_of_vanish_nodup_local roots
        (mask :: errBits.map (fun e => unpackTower 7 e)) hNodup hLenCs hAll
        (unpackTower 7 e) (List.mem_cons_of_mem _ (List.mem_map_of_mem he))
    have hp := congrArg (packTower 7) hZero
    rw [packTower_unpackTower, packTower_zero] at hp
    exact hne hp

/-- Constant-term bit (`LSB`, coefficient of $1 \in \mathbb{F}_2 \subset \mathcal{T}_k$) of a binary tower element,
    matching `(alpha.0 & 1) != 0` in `DensePcgPartySeed::validate_invariants` (`pcg_dense.rs:1260`). -/
def towerLsb : {k : Nat} → TowerElem k → Bool
  | 0, b => b
  | _ + 1, a => towerLsb a.1

theorem towerLsb_zero (k : Nat) : towerLsb (towerZero k) = false := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

theorem towerLsb_one (k : Nat) : towerLsb (towerOne k) = true := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

theorem towerLsb_add (k : Nat) (a b : TowerElem k) :
    towerLsb (towerAdd k a b) = (towerLsb a ^^ towerLsb b) := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih a.1 b.1

/-- Recursive extraction of the $\mathbb{F}_2$ constant-term slice from `TowerBitVec k`. -/
def lowBitsChain : (k : Nat) → TowerBitVec k → BitVec 1
  | 0, x => x
  | k + 1, x => lowBitsChain k (lowBits k x)

theorem lowBitsChain_packTower (k : Nat) (a : TowerElem k) :
    lowBitsChain k (packTower k a) = BitVec.ofBool (towerLsb a) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [lowBitsChain, packTower, lowBits_join, towerLsb]
    exact ih a.1

theorem towerLsb_unpackTower (k : Nat) (x : TowerBitVec k) :
    towerLsb (unpackTower k x) = (lowBitsChain k x).getLsbD 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [unpackTower, towerLsb, lowBitsChain]
    exact ih (lowBits k x)

/-- Fixed-length `cSHAKE256` wrapper (`cshake256_32` when `outLen = 32`, `pcg_dense.rs:750`). -/
def cshake256Fixed (outLen : Nat) (domain input : List UInt8) : List UInt8 :=
  cshake256Xof outLen domain input

/-- `cSHAKE256` customization `"QSAG.DPCG.SPCOT.TAG/v1"` (`pcg_dense.rs:751`). -/
def spcotTagDomain : List UInt8 := "QSAG.DPCG.SPCOT.TAG/v1".toUTF8.toList

/-- `cSHAKE256` customization `"QSAG.DPCG.SPCOT.CHAL/v1"` (`pcg_dense.rs:651`). -/
def spcotChalDomain : List UInt8 := "QSAG.DPCG.SPCOT.CHAL/v1".toUTF8.toList

/-- Canonical 16-byte little-endian `Tower128` serializer matching `w.0.to_le_bytes()` (`pcg_dense.rs:748`). -/
def encodeTower128Le (x : Tower128) : List UInt8 :=
  encodeNatLeBytes 16 (packTower 7 x).toNat

theorem encodeTower128Le_length (x : Tower128) : (encodeTower128Le x).length = 16 :=
  encodeNatLeBytes_length 16 _

theorem encodeTower128Le_injective {x y : Tower128}
    (h : encodeTower128Le x = encodeTower128Le y) : x = y := by
  unfold encodeTower128Le at h
  have hxLt : (packTower 7 x).toNat < 256 ^ 16 := by
    have := (packTower 7 x).isLt
    have hPow : (2 : Nat) ^ 128 = 256 ^ 16 := by decide
    omega
  have hyLt : (packTower 7 y).toNat < 256 ^ 16 := by
    have := (packTower 7 y).isLt
    have hPow : (2 : Nat) ^ 128 = 256 ^ 16 := by decide
    omega
  have hDec := congrArg decodeNatLeBytes h
  rw [decodeNatLeBytes_encodeNatLeBytes 16 _ hxLt,
      decodeNatLeBytes_encodeNatLeBytes 16 _ hyLt] at hDec
  exact packTower_injective 7 x y (BitVec.eq_of_toNat_eq hDec)

/-- Active SPCOT consistency tag (`compute_spcot_check_tag` in `pcg_dense.rs:737-756`):
    `cSHAKE256("QSAG.DPCG.SPCOT.TAG/v1", encodeMultiFrame [sessionId, u64le(senderId), u64le(receiverId), chalCoin, wBytes])`. -/
@[expose] def computeSpcotCheckTag
    (sessionId : List UInt8)
    (senderId receiverId : Nat)
    (chalCoin : List UInt8)
    (wVals : Tower128 × Tower128) : List UInt8 :=
  let sBytes := encodeNatLeBytes 8 senderId
  let rBytes := encodeNatLeBytes 8 receiverId
  let wBytes := encodeTower128Le wVals.1 ++ encodeTower128Le wVals.2
  cshake256Fixed 32 spcotTagDomain
    (encodeMultiFrame [sessionId, sBytes, rBytes, chalCoin, wBytes])

/-- **Injective Multi-Frame Binding of `computeSpcotCheckTag` (`computeSpcotCheckTag_binding`)**:
    Two SPCOT tag evaluations collide only if either every framed input field
    `(sessionId, senderId, receiverId, chalCoin, wVals)` is identical, or they yield a constructive
    `HashCollisionWitness` against `cshake256Fixed 32 spcotTagDomain` (`0 Classical.choice`). -/
def computeSpcotCheckTag_binding
    {sid₁ sid₂ : List UInt8} {s₁ s₂ r₁ r₂ : Nat} {coin₁ coin₂ : List UInt8}
    {w₁ w₂ : Tower128 × Tower128}
    (hs₁ : s₁ < 2 ^ 64) (hs₂ : s₂ < 2 ^ 64)
    (hr₁ : r₁ < 2 ^ 64) (hr₂ : r₂ < 2 ^ 64)
    (hTagEq : computeSpcotCheckTag sid₁ s₁ r₁ coin₁ w₁ = computeSpcotCheckTag sid₂ s₂ r₂ coin₂ w₂) :
    PSum (sid₁ = sid₂ ∧ s₁ = s₂ ∧ r₁ = r₂ ∧ coin₁ = coin₂ ∧ w₁ = w₂)
         (HashCollisionWitness (cshake256Fixed 32 spcotTagDomain)) :=
  let m₁ := encodeMultiFrame [sid₁, encodeNatLeBytes 8 s₁, encodeNatLeBytes 8 r₁, coin₁,
    encodeTower128Le w₁.1 ++ encodeTower128Le w₁.2]
  let m₂ := encodeMultiFrame [sid₂, encodeNatLeBytes 8 s₂, encodeNatLeBytes 8 r₂, coin₂,
    encodeTower128Le w₂.1 ++ encodeTower128Le w₂.2]
  if hm : m₁ = m₂ then
    PSum.inl <| by
      have hList := encodeMultiFrame_injective hm
      simp only [List.cons.injEq, and_true] at hList
      rcases hList with ⟨hSid, hS, hR, hCoin, hW⟩
      have hPow64 : (2 : Nat) ^ 64 = 256 ^ 8 := by decide
      have hsEq : s₁ = s₂ := by
        have hd := congrArg decodeNatLeBytes hS
        rw [decodeNatLeBytes_encodeNatLeBytes 8 s₁ (hPow64 ▸ hs₁),
            decodeNatLeBytes_encodeNatLeBytes 8 s₂ (hPow64 ▸ hs₂)] at hd
        exact hd
      have hrEq : r₁ = r₂ := by
        have hd := congrArg decodeNatLeBytes hR
        rw [decodeNatLeBytes_encodeNatLeBytes 8 r₁ (hPow64 ▸ hr₁),
            decodeNatLeBytes_encodeNatLeBytes 8 r₂ (hPow64 ▸ hr₂)] at hd
        exact hd
      obtain ⟨hW1, hW2⟩ := List.append_inj hW (by simp [encodeTower128Le_length])
      exact ⟨hSid, hsEq, hrEq, hCoin, Prod.ext (encodeTower128Le_injective hW1) (encodeTower128Le_injective hW2)⟩
  else
    PSum.inr ⟨m₁, m₂, hm, hTagEq⟩

/-- Symbolic hypercube sum $\bigoplus_{u \in \mathrm{BitVec}\, d} f(u)$ in `Tower128`. -/
def bvTowerSum128 : (d : Nat) → (BitVec d → Tower128) → Tower128
  | 0, f => f 0#0
  | d + 1, f =>
    towerAdd 7
      (bvTowerSum128 d (fun u => f (BitVec.cons false u)))
      (bvTowerSum128 d (fun u => f (BitVec.cons true u)))

private theorem bvTowerSum128_congr {d : Nat} {f g : BitVec d → Tower128}
    (h : ∀ u, f u = g u) : bvTowerSum128 d f = bvTowerSum128 d g := by
  induction d with
  | zero => exact h 0#0
  | succ d ih =>
    simp only [bvTowerSum128, ih (fun u => h (BitVec.cons false u)),
      ih (fun u => h (BitVec.cons true u))]

private theorem bvTowerSum128_zero (d : Nat) :
    bvTowerSum128 d (fun _ => towerZero 7) = towerZero 7 := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [bvTowerSum128, ih, towerAdd_zero]

private theorem bvTowerSum128_add {d : Nat} (f g : BitVec d → Tower128) :
    bvTowerSum128 d (fun u => towerAdd 7 (f u) (g u)) =
      towerAdd 7 (bvTowerSum128 d f) (bvTowerSum128 d g) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [bvTowerSum128, ih]
    simp only [towerAdd_assoc, towerAdd_left_comm]

private theorem bvTowerSum128_single : ∀ (d : Nat) (pStar : BitVec d) (val : Tower128),
    bvTowerSum128 d (fun u => if u = pStar then val else towerZero 7) = val
  | 0, pStar, val => by
    have hp : pStar = 0#0 := BitVec.eq_nil pStar
    subst hp; rfl
  | d + 1, pStar, val => by
    have hSp : BitVec.cons (pStar.getLsbD d) (pStar.setWidth d) = pStar := bvCons_split pStar
    rw [← hSp]
    simp only [bvTowerSum128]
    cases pStar.getLsbD d
    · have hL : bvTowerSum128 d (fun u => if BitVec.cons false u = BitVec.cons false (pStar.setWidth d) then val else towerZero 7) =
          bvTowerSum128 d (fun u => if u = pStar.setWidth d then val else towerZero 7) := by
        apply bvTowerSum128_congr; intro u; simp only [bvCons_inj, true_and]
      have hR : bvTowerSum128 d (fun u => if BitVec.cons true u = BitVec.cons false (pStar.setWidth d) then val else towerZero 7) =
          bvTowerSum128 d (fun _ => towerZero 7) := by
        apply bvTowerSum128_congr; intro u; simp only [bvCons_inj, Bool.true_eq_false, false_and, ↓reduceIte]
      rw [hL, hR, bvTowerSum128_single d, bvTowerSum128_zero, towerAdd_zero]
    · have hL : bvTowerSum128 d (fun u => if BitVec.cons false u = BitVec.cons true (pStar.setWidth d) then val else towerZero 7) =
          bvTowerSum128 d (fun _ => towerZero 7) := by
        apply bvTowerSum128_congr; intro u; simp only [bvCons_inj, Bool.false_eq_true, false_and, ↓reduceIte]
      have hR : bvTowerSum128 d (fun u => if BitVec.cons true u = BitVec.cons true (pStar.setWidth d) then val else towerZero 7) =
          bvTowerSum128 d (fun u => if u = pStar.setWidth d then val else towerZero 7) := by
        apply bvTowerSum128_congr; intro u; simp only [bvCons_inj, true_and]
      rw [hL, hR, bvTowerSum128_single d, bvTowerSum128_zero, towerZero_add]

/-- Repeated squaring $\chi^{2^d}$ in `Tower128` ($O(d)$ squarings). -/
def towerSqPow128 : Nat → Tower128 → Tower128
  | 0, x => x
  | d + 1, x =>
    let prev := towerSqPow128 d x
    towerMul 7 prev prev

/-- Vandermonde leaf weight $\chi^{u + 1} \in \mathrm{Tower128}$ evaluated in $O(d)$ multiplications
    (`leaf_powers` in `pcg_dense.rs:665-668`). -/
def spcotLeafWeight : {d : Nat} → Tower128 → BitVec d → Tower128
  | 0, chi, _ => chi
  | d + 1, chi, u =>
    let lo := spcotLeafWeight chi (u.setWidth d)
    if u.getLsbD d then towerMul 7 (towerSqPow128 d chi) lo else lo

private theorem spcotLeafWeight_zero_idx (d : Nat) (chi : Tower128) :
    spcotLeafWeight chi (0#d) = chi := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [spcotLeafWeight, BitVec.getLsbD_zero, Bool.false_eq_true, ↓reduceIte]
    rw [setWidth_zero (d + 1) d, ih]

/-- Map a squeezed 128-bit word into `Tower128 \ {0, 1}` (`squeeze_nonzero_tower128` in `pcg_dense.rs:627-636`). -/
def sanitizeSpcotChallengeElem (raw : BitVec 128) : Tower128 :=
  let t := unpackTower 7 raw
  if decide (t = towerZero 7) || decide (t = towerOne 7) then towerX 7 else t

theorem sanitizeSpcotChallengeElem_ne_zero (raw : BitVec 128) :
    sanitizeSpcotChallengeElem raw ≠ towerZero 7 := by
  unfold sanitizeSpcotChallengeElem
  dsimp only
  if h0 : unpackTower 7 raw = towerZero 7 then
    simp only [h0, decide_true, Bool.true_or, ↓reduceIte]
    decide
  else if h1 : unpackTower 7 raw = towerOne 7 then
    simp only [h1, decide_true, Bool.or_true, ↓reduceIte]
    decide
  else
    simp only [h0, h1, decide_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    exact h0

/-- Derive `(gamma, chiBase)` in `Tower128 \ {0, 1}` for SPCOT repetition `rep` via `cSHAKE256`
    with customization `"QSAG.DPCG.SPCOT.CHAL/v1"` (`derive_spcot_challenge_weights` in `pcg_dense.rs:643-661`). -/
def deriveSpcotChallengePair
    (sessionId : List UInt8)
    (senderId receiverId treeDepth rep : Nat)
    (chalCoin : List UInt8) : Tower128 × Tower128 :=
  let chalInput :=
    sessionId ++
    encodeNatLeBytes 8 senderId ++
    encodeNatLeBytes 8 receiverId ++
    encodeNatLeBytes 4 treeDepth ++
    encodeNatLeBytes 4 rep ++
    chalCoin
  let raw := cshake256Fixed 32 spcotChalDomain chalInput
  let rawGamma := BitVec.ofNat 128 (decodeNatLeBytes (raw.take 16))
  let rawChi := BitVec.ofNat 128 (decodeNatLeBytes (raw.drop 16))
  (sanitizeSpcotChallengeElem rawGamma, sanitizeSpcotChallengeElem rawChi)

theorem deriveSpcotChallengePair_ne_zero
    (sessionId : List UInt8) (senderId receiverId treeDepth rep : Nat) (chalCoin : List UInt8) :
    (deriveSpcotChallengePair sessionId senderId receiverId treeDepth rep chalCoin).1 ≠ towerZero 7 ∧
    (deriveSpcotChallengePair sessionId senderId receiverId treeDepth rep chalCoin).2 ≠ towerZero 7 :=
  ⟨sanitizeSpcotChallengeElem_ne_zero _, sanitizeSpcotChallengeElem_ne_zero _⟩

/-- Convert a length-`d` sibling list into a typed `GgmCopath d`. -/
def listToGgmCopath : (d : Nat) → List (BitVec 128) → GgmCopath d
  | 0, _ => ()
  | d + 1, [] => (0#128, listToGgmCopath d [])
  | d + 1, s :: rest => (s, listToGgmCopath d rest)

/-- Serialize a typed `GgmCopath d` to a length-`d` list of 128-bit sibling seeds. -/
def ggmCopathToList : {d : Nat} → GgmCopath d → List (BitVec 128)
  | 0, _ => []
  | _ + 1, (s, rest) => s :: ggmCopathToList rest

theorem ggmCopathToList_length : ∀ {d : Nat} (cp : GgmCopath d),
    (ggmCopathToList cp).length = d
  | 0, _ => rfl
  | _ + 1, (_, rest) => congrArg Nat.succ (ggmCopathToList_length rest)

theorem listToGgmCopath_toList : ∀ {d : Nat} (cp : GgmCopath d),
    listToGgmCopath d (ggmCopathToList cp) = cp
  | 0, () => rfl
  | _ + 1, (_, rest) => Prod.ext rfl (listToGgmCopath_toList rest)

/-- Evaluate Receiver's single-repetition SPCOT linear combination term
    $\gamma \cdot \bigoplus_{u \in \mathrm{BitVec}\, d} \chi^{u+1} \cdot s'[u]$
    (`eval_punctured_tree_spcot_term` in `pcg_dense.rs:714-733`). -/
def evalPuncturedTreeSpcotCombo (d : Nat)
    (gamma chi : Tower128)
    (puncLeaves : BitVec d → BitVec 128)
    (pStar : BitVec d)
    (deltaCorr : Tower128) : Tower128 :=
  let sum := bvTowerSum128 d (fun u =>
    let eff := if u = pStar then deltaCorr else unpackTower 7 (puncLeaves u)
    towerMul 7 (spcotLeafWeight chi u) eff)
  towerMul 7 gamma sum

/-- **Exact Sender–Receiver SPCOT Check-Value Agreement (`spcot_reconstruct_matches_sender`)**:
    For every GGM PRG `prg`, depth `d`, root `seed`, Sender MAC key `alphaSender`, puncture `pStar`,
    challenge weights `(gamma, chi)`, and 1-element $\mathbb{F}_{2^{128}}$ VOLE mask `(keySender, macRecv)`
    satisfying `macRecv + keySender = (gamma * chi^{p* + 1}) * alphaSender`, Receiver's punctured
    reconstruction equals Sender's full-tree linear combination identically! -/
theorem spcot_reconstruct_matches_sender (prg : GgmPrg) (d : Nat)
    (seed : BitVec 128) (alphaSender gamma chi keySender macRecv : Tower128)
    (pStar : BitVec d)
    (hVole : towerAdd 7 macRecv keySender =
      towerMul 7 (towerMul 7 gamma (spcotLeafWeight chi pStar)) alphaSender) :
    let fullLeaves := ggmExpandFull prg d 0 seed
    let copath := ggmMakeCopath prg d 0 seed pStar
    let puncLeaves := ggmExpandPunctured prg d 0 pStar copath
    let corrOffset := towerAdd 7 (unpackTower 7 (bvXorSum128 d fullLeaves)) alphaSender
    let deltaCorr := towerAdd 7 (unpackTower 7 (bvXorSum128 d puncLeaves)) corrOffset
    let senderCombo := towerMul 7 gamma
      (bvTowerSum128 d (fun u => towerMul 7 (spcotLeafWeight chi u) (unpackTower 7 (fullLeaves u))))
    towerAdd 7 macRecv (evalPuncturedTreeSpcotCombo d gamma chi puncLeaves pStar deltaCorr) =
      towerAdd 7 keySender senderCombo := by
  intro fullLeaves copath puncLeaves corrOffset deltaCorr senderCombo
  obtain ⟨hPuncZero, hPuncEq⟩ := ggmExpandPunctured_exact prg d 0 seed pStar
  have hXorId := (spcot_consistency_soundness fullLeaves puncLeaves pStar (packTower 7 alphaSender)
    hPuncZero hPuncEq).1
  have hDeltaEq : deltaCorr = towerAdd 7 (unpackTower 7 (fullLeaves pStar)) alphaSender := by
    apply packTower_injective 7
    dsimp only [deltaCorr, corrOffset]
    rw [packTower_add, packTower_add, packTower_add, packTower_unpackTower,
        packTower_unpackTower, packTower_unpackTower]
    exact hXorId
  have hTermSplit : evalPuncturedTreeSpcotCombo d gamma chi puncLeaves pStar deltaCorr =
      towerAdd 7 senderCombo
        (towerMul 7 (towerMul 7 gamma (spcotLeafWeight chi pStar)) alphaSender) := by
    unfold evalPuncturedTreeSpcotCombo
    have hPoint : ∀ u : BitVec d,
        towerMul 7 (spcotLeafWeight chi u)
          (if u = pStar then deltaCorr else unpackTower 7 (puncLeaves u)) =
        towerAdd 7
          (towerMul 7 (spcotLeafWeight chi u) (unpackTower 7 (fullLeaves u)))
          (if u = pStar then towerMul 7 (spcotLeafWeight chi pStar) alphaSender else towerZero 7) := by
      intro u
      if hu : u = pStar then
        subst hu
        simp only [↓reduceIte, hDeltaEq, towerMul_add_distrib]
      else
        simp only [hu, ↓reduceIte, towerAdd_zero]
        dsimp only [puncLeaves, fullLeaves, copath]
        rw [hPuncEq u hu]
    rw [bvTowerSum128_congr hPoint, bvTowerSum128_add, bvTowerSum128_single,
        towerMul_add_distrib, towerMul_assoc]
  rw [hTermSplit]
  have hKeyEq : keySender = towerAdd 7 macRecv
      (towerMul 7 (towerMul 7 gamma (spcotLeafWeight chi pStar)) alphaSender) := by
    rw [← hVole, towerAdd_cancel]
  rw [hKeyEq]
  rw [towerAdd_assoc 7 macRecv _ senderCombo,
      towerAdd_comm 7 (towerMul 7 (towerMul 7 gamma (spcotLeafWeight chi pStar)) alphaSender) senderCombo]

/-- Recursive check of peer Sender's `LSB(alpha_sender) == 1` correlation proof across 128 dedicated
    OT-authenticated check rows (`lsb(M_i) ^^ k_i = x_i`). -/
def verifySenderAlphaLsbAux : Nat → BitVec 128 → List Tower128 → BitVec 128 → Bool
  | _, _, [], _ => true
  | idx, choices, m :: rest, keyBits =>
    decide ((towerLsb m ^^ keyBits.getLsbD idx) = choices.getLsbD idx) &&
    verifySenderAlphaLsbAux (idx + 1) choices rest keyBits

/-- Verify peer Sender's `LSB(alpha_sender) == 1` over 128 non-zero OT check correlations. -/
def verifyPeerSenderAlphaLsb
    (choices : BitVec 128) (recvMacs : List Tower128) (senderKeyLsbBits : BitVec 128) : Bool :=
  decide (choices ≠ 0#128) &&
  decide (recvMacs.length = 128) &&
  verifySenderAlphaLsbAux 0 choices recvMacs senderKeyLsbBits

/-- Construct Receiver's `n` OT-authenticated MACs starting at row `idx`:
    `M_{idx + j} = K_{idx + j} + choices[idx + j] * alphaSender`. -/
def mkSenderAlphaRecvMacsAux (alphaSender : Tower128) (senderKeys : Nat → Tower128)
    (choices : BitVec 128) : Nat → Nat → List Tower128
  | _, 0 => []
  | idx, n + 1 =>
    towerAdd 7 (senderKeys idx) (if choices.getLsbD idx then alphaSender else towerZero 7) ::
      mkSenderAlphaRecvMacsAux alphaSender senderKeys choices (idx + 1) n

/-- Construct Receiver's 128 OT-authenticated MACs `M_i = K_i + choices[i] * alphaSender`. -/
def mkSenderAlphaRecvMacs (alphaSender : Tower128) (senderKeys : Nat → Tower128)
    (choices : BitVec 128) : List Tower128 :=
  mkSenderAlphaRecvMacsAux alphaSender senderKeys choices 0 128

private theorem mkSenderAlphaRecvMacsAux_length (alphaSender : Tower128) (senderKeys : Nat → Tower128)
    (choices : BitVec 128) : ∀ (idx n : Nat),
    (mkSenderAlphaRecvMacsAux alphaSender senderKeys choices idx n).length = n
  | _, 0 => rfl
  | idx, n + 1 => congrArg Nat.succ (mkSenderAlphaRecvMacsAux_length alphaSender senderKeys choices (idx + 1) n)

private theorem verifySenderAlphaLsbAux_mkOneLsb
    (alphaSender : Tower128) (hOneLsb : towerLsb alphaSender = true)
    (senderKeys : Nat → Tower128) (choices keyBits : BitVec 128) :
    ∀ (idx n : Nat),
      (∀ j : Nat, j < n → keyBits.getLsbD (idx + j) = towerLsb (senderKeys (idx + j))) →
      verifySenderAlphaLsbAux idx choices
        (mkSenderAlphaRecvMacsAux alphaSender senderKeys choices idx n) keyBits = true
  | _, 0, _ => rfl
  | idx, n + 1, hHonest => by
    have h0 : keyBits.getLsbD idx = towerLsb (senderKeys idx) := by
      simpa only [Nat.add_zero] using hHonest 0 (Nat.zero_lt_succ n)
    have hHead :
        (towerLsb (towerAdd 7 (senderKeys idx) (if choices.getLsbD idx then alphaSender else towerZero 7)) ^^
          keyBits.getLsbD idx) = choices.getLsbD idx := by
      rw [towerLsb_add, h0]
      cases choices.getLsbD idx
      · simp only [Bool.false_eq_true, ↓reduceIte, towerLsb_zero]
        cases towerLsb (senderKeys idx) <;> rfl
      · simp only [↓reduceIte, hOneLsb]
        cases towerLsb (senderKeys idx) <;> rfl
    have hTail : verifySenderAlphaLsbAux (idx + 1) choices
        (mkSenderAlphaRecvMacsAux alphaSender senderKeys choices (idx + 1) n) keyBits = true :=
      verifySenderAlphaLsbAux_mkOneLsb alphaSender hOneLsb senderKeys choices keyBits (idx + 1) n
        (fun j hj => by
          have hStep := hHonest (j + 1) (Nat.succ_lt_succ hj)
          have hIdx : idx + 1 + j = idx + (j + 1) := by omega
          rwa [hIdx])
    simp only [mkSenderAlphaRecvMacsAux, verifySenderAlphaLsbAux, hHead, decide_true, hTail, Bool.and_self]

/-- **Completeness of `verifyPeerSenderAlphaLsb` (`verifyPeerSenderAlphaLsb_complete`)**:
    Any honest peer Sender with `towerLsb alphaSender = true` and `keyBits_i = towerLsb K_i`
    passes `verifyPeerSenderAlphaLsb` for every non-zero `choices ≠ 0#128`. -/
theorem verifyPeerSenderAlphaLsb_complete
    (alphaSender : Tower128) (hOneLsb : towerLsb alphaSender = true)
    (senderKeys : Nat → Tower128)
    (choices keyBits : BitVec 128)
    (hChoicesNz : choices ≠ 0#128)
    (hHonest : ∀ i : Nat, i < 128 → keyBits.getLsbD i = towerLsb (senderKeys i)) :
    verifyPeerSenderAlphaLsb choices (mkSenderAlphaRecvMacs alphaSender senderKeys choices) keyBits = true := by
  unfold verifyPeerSenderAlphaLsb mkSenderAlphaRecvMacs
  have hcDec : decide (choices ≠ 0#128) = true := decide_eq_true hChoicesNz
  have hlDec : decide ((mkSenderAlphaRecvMacsAux alphaSender senderKeys choices 0 128).length = 128) = true :=
    decide_eq_true (mkSenderAlphaRecvMacsAux_length alphaSender senderKeys choices 0 128)
  have hAux : verifySenderAlphaLsbAux 0 choices
      (mkSenderAlphaRecvMacsAux alphaSender senderKeys choices 0 128) keyBits = true :=
    verifySenderAlphaLsbAux_mkOneLsb alphaSender hOneLsb senderKeys choices keyBits 0 128
      (fun j hj => by simpa only [Nat.zero_add] using hHonest j hj)
  rw [hcDec, hlDec, hAux]
  rfl

private theorem verifySenderAlphaLsbAux_mkZeroLsb
    (alphaSender : Tower128) (hZeroLsb : towerLsb alphaSender = false)
    (senderKeys : Nat → Tower128) (choices keyBits : BitVec 128) :
    ∀ (idx n : Nat),
      verifySenderAlphaLsbAux idx choices
        (mkSenderAlphaRecvMacsAux alphaSender senderKeys choices idx n) keyBits = true ↔
      ∀ j : Nat, j < n →
        (towerLsb (senderKeys (idx + j)) ^^ keyBits.getLsbD (idx + j)) = choices.getLsbD (idx + j)
  | _, 0 => ⟨fun _ _ hj => False.elim (Nat.not_lt_zero _ hj), fun _ => rfl⟩
  | idx, n + 1 => by
    have hHeadLsb :
        towerLsb (towerAdd 7 (senderKeys idx) (if choices.getLsbD idx then alphaSender else towerZero 7)) =
          towerLsb (senderKeys idx) := by
      rw [towerLsb_add]
      cases choices.getLsbD idx
      · simp only [Bool.false_eq_true, ↓reduceIte, towerLsb_zero]
        cases towerLsb (senderKeys idx) <;> rfl
      · simp only [↓reduceIte, hZeroLsb]
        cases towerLsb (senderKeys idx) <;> rfl
    simp only [mkSenderAlphaRecvMacsAux, verifySenderAlphaLsbAux, hHeadLsb,
      Bool.and_eq_true, decide_eq_true_eq,
      verifySenderAlphaLsbAux_mkZeroLsb alphaSender hZeroLsb senderKeys choices keyBits (idx + 1) n]
    constructor
    · rintro ⟨h0, hRest⟩ j hj
      cases j with
      | zero => simpa only [Nat.add_zero] using h0
      | succ j' =>
        have hStep := hRest j' (Nat.lt_of_succ_lt_succ hj)
        have hIdx : idx + 1 + j' = idx + (j' + 1) := by omega
        rwa [hIdx] at hStep
    · intro hAll
      refine ⟨by simpa only [Nat.add_zero] using hAll 0 (Nat.zero_lt_succ n), ?_⟩
      intro j' hj'
      have hStep := hAll (j' + 1) (Nat.succ_lt_succ hj')
      have hIdx : idx + 1 + j' = idx + (j' + 1) := by omega
      rwa [hIdx]

/-- **Soundness of `verifyPeerSenderAlphaLsb` Against Zero-LSB Sender MAC Keys (`senderAlphaLsb_soundness`)**:
    When a malicious peer Sender chooses a global MAC key `alphaSender` with `towerLsb alphaSender = false`
    so Receiver's OT MACs satisfy `M_i = K_i + x_i * alphaSender`:
    1. Submitting the honest key parities `keyBits_i = towerLsb K_i` is **deterministically rejected**
       (`verifyPeerSenderAlphaLsb = false`) for every `choices` (non-zero `choices` fails parity,
       `0#128` fails the `choices ≠ 0#128` guard).
    2. Even if the malicious Sender submits an **arbitrary forged** `forgedKeyBits : BitVec 128`,
       at most **1** of the `2^128` OT-hidden choice vectors `choices : BitVec 128` can pass
       (`c₁ = c₂`, forgery probability `≤ 1 / 2^128`)! -/
theorem senderAlphaLsb_soundness
    (alphaSender : Tower128) (hZeroLsb : towerLsb alphaSender = false)
    (senderKeys : Nat → Tower128) :
    let mkRecvMacs := mkSenderAlphaRecvMacs alphaSender senderKeys
    (∀ (choices honestKeyBits : BitVec 128),
      (∀ i : Nat, i < 128 → honestKeyBits.getLsbD i = towerLsb (senderKeys i)) →
      verifyPeerSenderAlphaLsb choices (mkRecvMacs choices) honestKeyBits = false) ∧
    (∀ (forgedKeyBits c₁ c₂ : BitVec 128),
      verifyPeerSenderAlphaLsb c₁ (mkRecvMacs c₁) forgedKeyBits = true →
      verifyPeerSenderAlphaLsb c₂ (mkRecvMacs c₂) forgedKeyBits = true →
      c₁ = c₂) := by
  intro mkRecvMacs
  refine ⟨?_, ?_⟩
  · intro choices honestKeyBits hHonest
    cases hb : verifyPeerSenderAlphaLsb choices (mkRecvMacs choices) honestKeyBits
    · rfl
    · exfalso
      unfold verifyPeerSenderAlphaLsb mkRecvMacs mkSenderAlphaRecvMacs at hb
      simp only [Bool.and_eq_true, decide_eq_true_eq,
        verifySenderAlphaLsbAux_mkZeroLsb alphaSender hZeroLsb senderKeys choices honestKeyBits 0 128] at hb
      rcases hb with ⟨⟨hChoicesNz, _⟩, hAll⟩
      apply hChoicesNz
      apply BitVec.eq_of_getLsbD_eq
      intro idx hIdx
      have hRow := hAll idx hIdx
      simp only [Nat.zero_add] at hRow
      rw [hHonest idx hIdx] at hRow
      have hSelf : (towerLsb (senderKeys idx) ^^ towerLsb (senderKeys idx)) = false := by
        cases towerLsb (senderKeys idx) <;> rfl
      rw [hSelf] at hRow
      rw [← hRow]
      simp only [BitVec.getLsbD_zero]
  · intro forgedKeyBits c₁ c₂ hAcc1 hAcc2
    unfold verifyPeerSenderAlphaLsb mkRecvMacs mkSenderAlphaRecvMacs at hAcc1 hAcc2
    simp only [Bool.and_eq_true, decide_eq_true_eq,
      verifySenderAlphaLsbAux_mkZeroLsb alphaSender hZeroLsb senderKeys c₁ forgedKeyBits 0 128,
      verifySenderAlphaLsbAux_mkZeroLsb alphaSender hZeroLsb senderKeys c₂ forgedKeyBits 0 128] at hAcc1 hAcc2
    apply BitVec.eq_of_getLsbD_eq
    intro idx hIdx
    have h1 := hAcc1.2 idx hIdx
    have h2 := hAcc2.2 idx hIdx
    simp only [Nat.zero_add] at h1 h2
    exact h1.symm.trans h2

/-- Legacy single-tree SPCOT record. This is not the V3 `DensePcgPeerSeed` wire schema:
    V3 has 64 trees, 256-bit nodes, and no sender-MAC-LSB transcript fields. -/
structure PcgPeerSpcotRecord where
  peerId : Nat
  puncturedIdx : Nat
  copath : List (BitVec 128)
  corrOffset : Tower128
  spcotChalCoin : List UInt8
  spcotMaskMacs : Tower128 × Tower128
  spcotExpectedTag : List UInt8
  lsbCheckChoices : BitVec 128
  lsbCheckRecvMacs : List Tower128
  senderAlphaLsbKeyBits : BitVec 128

/-- Reconstruct Receiver's 2-repetition (`SPCOT_CHECK_REPS = 2`) SPCOT check values `w_recv`
    from `(puncturedIdx, copath, corrOffset, spcotChalCoin, spcotMaskMacs)` via `ggmExpandPunctured`
    (`receiver_spcot_check_values` in `pcg_dense.rs:1747-1804`). -/
def reconstructPeerSpcotCheckValues (prg : GgmPrg)
    (sessionId : List UInt8)
    (receiverId treeDepth : Nat)
    (peer : PcgPeerSpcotRecord) : Tower128 × Tower128 :=
  let pStar : BitVec treeDepth := BitVec.ofNat treeDepth peer.puncturedIdx
  let cp := listToGgmCopath treeDepth peer.copath
  let puncLeaves := ggmExpandPunctured prg treeDepth 0 pStar cp
  let puncXorSum := bvXorSum128 treeDepth puncLeaves
  let deltaCorr := towerAdd 7 (unpackTower 7 puncXorSum) peer.corrOffset
  let (gamma0, chi0) := deriveSpcotChallengePair sessionId peer.peerId receiverId treeDepth 0 peer.spcotChalCoin
  let (gamma1, chi1) := deriveSpcotChallengePair sessionId peer.peerId receiverId treeDepth 1 peer.spcotChalCoin
  let term0 := evalPuncturedTreeSpcotCombo treeDepth gamma0 chi0 puncLeaves pStar deltaCorr
  let term1 := evalPuncturedTreeSpcotCombo treeDepth gamma1 chi1 puncLeaves pStar deltaCorr
  (towerAdd 7 peer.spcotMaskMacs.1 term0, towerAdd 7 peer.spcotMaskMacs.2 term1)

/-- Validated PCG wire seed header closing `[P1-06]` and `[C0-2]` (session framing, peer-ID bounds,
    uniqueness, self-exclusion, `LSB(macAlpha) == 1`, peer `LSB(alpha_sender) == 1`, validated tree
    depth `∈ {14, 15}`, punctured index `< 2^d`, copath length `= d`, and active `cSHAKE256`
    SPCOT tag recomputation against `spcotExpectedTag` with zero caller-supplied trust flags). -/
structure ValidatedPcgSeedHeader where
  sessionId : List UInt8
  numParties : Nat
  myPartyId : Nat
  treeDepth : Nat
  macAlpha : Tower128
  peers : List PcgPeerSpcotRecord

/-- Peer party IDs extracted from `ValidatedPcgSeedHeader.peers`. -/
def ValidatedPcgSeedHeader.peerIds (hdr : ValidatedPcgSeedHeader) : List Nat :=
  hdr.peers.map PcgPeerSpcotRecord.peerId

/-- Punctured leaf indices extracted from `ValidatedPcgSeedHeader.peers`. -/
def ValidatedPcgSeedHeader.puncturedIndices (hdr : ValidatedPcgSeedHeader) : List Nat :=
  hdr.peers.map PcgPeerSpcotRecord.puncturedIdx

/-- Parametric single-peer structural + sender-`LSB(alpha) == 1` + SPCOT tag validator. -/
def checkPeerSpcotRecordWithTag
    (tagFn : List UInt8 → Nat → Nat → List UInt8 → (Tower128 × Tower128) → List UInt8)
    (prg : GgmPrg) (hdr : ValidatedPcgSeedHeader)
    (peer : PcgPeerSpcotRecord) : Bool :=
  decide (peer.peerId < hdr.numParties ∧ peer.peerId ≠ hdr.myPartyId) &&
  decide (peer.puncturedIdx < 2 ^ hdr.treeDepth) &&
  decide (peer.copath.length = hdr.treeDepth) &&
  decide (peer.spcotChalCoin.length = 32) &&
  decide (peer.spcotExpectedTag.length = 32) &&
  verifyPeerSenderAlphaLsb peer.lsbCheckChoices peer.lsbCheckRecvMacs peer.senderAlphaLsbKeyBits &&
  let wRecv := reconstructPeerSpcotCheckValues prg hdr.sessionId hdr.myPartyId hdr.treeDepth peer
  let recomputedTag := tagFn hdr.sessionId peer.peerId hdr.myPartyId peer.spcotChalCoin wRecv
  decide (recomputedTag = peer.spcotExpectedTag)

/-- Validate a single peer's structural bounds, sender-`LSB(alpha) == 1` proof, and active
    `cSHAKE256` SPCOT consistency tag (`pcg_dense.rs:1269-1285, 1553-1581`). -/
def checkPeerSpcotRecord (prg : GgmPrg) (hdr : ValidatedPcgSeedHeader)
    (peer : PcgPeerSpcotRecord) : Bool :=
  checkPeerSpcotRecordWithTag computeSpcotCheckTag prg hdr peer

/-- Parametric seed-header validator under tag oracle `tagFn`. -/
def checkPcgSeedHeaderWithTag
    (tagFn : List UInt8 → Nat → Nat → List UInt8 → (Tower128 × Tower128) → List UInt8)
    (prg : GgmPrg) (hdr : ValidatedPcgSeedHeader) : Bool :=
  decide (hdr.sessionId.length = 32) &&
  decide (2 ≤ hdr.numParties) &&
  decide (hdr.myPartyId < hdr.numParties) &&
  decide (hdr.treeDepth = 14 ∨ hdr.treeDepth = 15) &&
  towerLsb hdr.macAlpha &&
  decide (hdr.peers.length + 1 = hdr.numParties) &&
  decide hdr.peerIds.Nodup &&
  hdr.peers.all (checkPeerSpcotRecordWithTag tagFn prg hdr)

/-- Boolean validator matching `DensePcgPartySeed::from_wire_bytes` & `expand_local`
    (`pcg_dense.rs:1257-1290, 1546-1581`), enforcing `LSB(macAlpha) == 1`, peer `LSB(alpha_sender) == 1`,
    and byte-exact `computeSpcotCheckTag` verification without any boolean trust flag. -/
def checkPcgSeedHeader (prg : GgmPrg) (hdr : ValidatedPcgSeedHeader) : Bool :=
  checkPcgSeedHeaderWithTag computeSpcotCheckTag prg hdr

/-- Single-use PCG seed state (`consumed = true` forbids seed reuse, matching move-only `DensePcgPartySeed`). -/
structure PcgSeedMachineState where
  consumed : Bool
  deriving DecidableEq, Repr

/-- `SimulationSpine.PartyMachine` enforcing single-use consumption + `P1-06` bounds + `LSB(alpha) == 1`
    + active `computeSpcotCheckTag` recomputation! -/
def pcgSeedExpandMachine (prg : GgmPrg) :
    PartyMachine PcgSeedMachineState ValidatedPcgSeedHeader ValidatedPcgSeedHeader :=
  PartyMachine.ofOption fun st hdr =>
    if !st.consumed && checkPcgSeedHeader prg hdr then
      some (⟨true⟩, hdr)
    else
      none

/-- **Single-Use Consumption, `LSB(alpha) == 1`, & Active SPCOT Tag Safety Along Multi-Turn Traces (`pcgSeedExpandMachine_trace_safety`)**:
    Along ANY `PartyMachine.ValidTrace` starting from `⟨false⟩`, at most **1** seed expansion is ever
    accepted, and every accepted header satisfies `sessionId.length = 32`, `myPartyId < numParties`,
    `treeDepth ∈ {14, 15}`, `towerLsb hdr.macAlpha = true`, `peerIds.Nodup`, `myPartyId ∉ peerIds`,
    and for every `peer ∈ hdr.peers`: `peer.peerId < numParties`, `peer.puncturedIdx < 2 ^ treeDepth`,
    `peer.copath.length = treeDepth`, `verifyPeerSenderAlphaLsb ... = true`, and byte-exact SPCOT tag
    equality `computeSpcotCheckTag ... (reconstructPeerSpcotCheckValues prg ...) = peer.spcotExpectedTag`! -/
theorem pcgSeedExpandMachine_trace_safety (prg : GgmPrg)
    {stFinal : PcgSeedMachineState}
    {trace : List (ValidatedPcgSeedHeader × ValidatedPcgSeedHeader)}
    (hTrace : (pcgSeedExpandMachine prg).ValidTrace ⟨false⟩ trace stFinal) :
    trace.length ≤ 1 ∧
    ∀ pair ∈ trace,
      let hdr := pair.2
      hdr.sessionId.length = 32 ∧
      hdr.myPartyId < hdr.numParties ∧
      (hdr.treeDepth = 14 ∨ hdr.treeDepth = 15) ∧
      towerLsb hdr.macAlpha = true ∧
      hdr.peerIds.Nodup ∧
      hdr.myPartyId ∉ hdr.peerIds ∧
      (∀ p ∈ hdr.peerIds, p < hdr.numParties) ∧
      (∀ idx ∈ hdr.puncturedIndices, idx < 2 ^ hdr.treeDepth) ∧
      (∀ peer ∈ hdr.peers,
        peer.copath.length = hdr.treeDepth ∧
        verifyPeerSenderAlphaLsb peer.lsbCheckChoices peer.lsbCheckRecvMacs peer.senderAlphaLsbKeyBits = true ∧
        computeSpcotCheckTag hdr.sessionId peer.peerId hdr.myPartyId peer.spcotChalCoin
          (reconstructPeerSpcotCheckValues prg hdr.sessionId hdr.myPartyId hdr.treeDepth peer) =
          peer.spcotExpectedTag) := by
  have hConsumedEmpty : ∀ {sEnd : PcgSeedMachineState}
      {tr : List (ValidatedPcgSeedHeader × ValidatedPcgSeedHeader)},
      (pcgSeedExpandMachine prg).ValidTrace ⟨true⟩ tr sEnd → tr = [] := by
    intro sEnd tr hTr
    generalize hs0 : (⟨true⟩ : PcgSeedMachineState) = s0 at hTr
    induction hTr with
    | nil _ => rfl
    | accept hStep _ =>
      subst hs0
      unfold pcgSeedExpandMachine PartyMachine.ofOption at hStep
      simp at hStep
    | reject _ _ _ ih =>
      subst hs0
      exact ih rfl
  generalize hsInit : (⟨false⟩ : PcgSeedMachineState) = sInit at hTrace
  induction hTrace with
  | nil _ => exact ⟨Nat.zero_le 1, fun _ hm => False.elim (List.not_mem_nil hm)⟩
  | @accept s s' _ inp out rest hStep hTail _ =>
    subst hsInit
    unfold pcgSeedExpandMachine PartyMachine.ofOption at hStep
    dsimp only at hStep
    split at hStep
    · rename_i hCond
      injection hStep with hPair
      injection hPair with hs' hOut
      subst hs'; subst hOut
      have hRestNil := hConsumedEmpty hTail
      subst hRestNil
      refine ⟨Nat.le_refl 1, ?_⟩
      intro pair hMem
      simp only [List.mem_singleton] at hMem
      subst hMem
      dsimp only
      unfold checkPcgSeedHeader checkPcgSeedHeaderWithTag at hCond
      simp only [Bool.not_false, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq,
        List.all_eq_true, and_assoc] at hCond
      rcases hCond with ⟨hSidLen, _, hMyLt, hDepth, hLsbSelf, _, hNodup, hPeersAll⟩
      have hPeerUnpack : ∀ peer ∈ inp.peers,
          (peer.peerId < inp.numParties ∧ peer.peerId ≠ inp.myPartyId) ∧
          peer.puncturedIdx < 2 ^ inp.treeDepth ∧
          peer.copath.length = inp.treeDepth ∧
          verifyPeerSenderAlphaLsb peer.lsbCheckChoices peer.lsbCheckRecvMacs peer.senderAlphaLsbKeyBits = true ∧
          computeSpcotCheckTag inp.sessionId peer.peerId inp.myPartyId peer.spcotChalCoin
            (reconstructPeerSpcotCheckValues prg inp.sessionId inp.myPartyId inp.treeDepth peer) =
            peer.spcotExpectedTag := by
        intro peer hp
        have hc := hPeersAll peer hp
        unfold checkPeerSpcotRecordWithTag at hc
        simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hc
        exact ⟨⟨hc.1, hc.2.1⟩, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2⟩
      refine ⟨hSidLen, hMyLt, hDepth, hLsbSelf, hNodup, ?_, ?_, ?_, ?_⟩
      · intro hIn
        unfold ValidatedPcgSeedHeader.peerIds at hIn
        rw [List.mem_map] at hIn
        rcases hIn with ⟨peer, hpMem, hpEq⟩
        exact (hPeerUnpack peer hpMem).1.2 hpEq
      · intro p hpIn
        unfold ValidatedPcgSeedHeader.peerIds at hpIn
        rw [List.mem_map] at hpIn
        rcases hpIn with ⟨peer, hpMem, hpEq⟩
        rw [← hpEq]
        exact (hPeerUnpack peer hpMem).1.1
      · intro idx hIdxIn
        unfold ValidatedPcgSeedHeader.puncturedIndices at hIdxIn
        rw [List.mem_map] at hIdxIn
        rcases hIdxIn with ⟨peer, hpMem, hIdxEq⟩
        rw [← hIdxEq]
        exact (hPeerUnpack peer hpMem).2.1
      · intro peer hpMem
        have hu := hPeerUnpack peer hpMem
        exact ⟨hu.2.2.1, hu.2.2.2.1, hu.2.2.2.2⟩
    · cases hStep
  | reject _ _ _ ih =>
    subst hsInit
    exact ih rfl

/-- Canonical zero GGM PRG for fast symbolic evaluation at production depth `d = 14`. -/
def zeroGgmPrg : GgmPrg := fun _ _ => (0#128, 0#128)

private theorem ggmExpandFull_zeroGgmPrg : ∀ (d lvl : Nat) (u : BitVec d),
    ggmExpandFull zeroGgmPrg d lvl 0#128 u = 0#128
  | 0, _, _ => rfl
  | d + 1, lvl, u => by
    simp only [ggmExpandFull, zeroGgmPrg]
    cases u.getLsbD d <;> exact ggmExpandFull_zeroGgmPrg d (lvl + 1) (u.setWidth d)

private theorem ggmExpandPunctured_zeroGgmPrg : ∀ (d lvl : Nat) (pStar : BitVec d) (u : BitVec d),
    ggmExpandPunctured zeroGgmPrg d lvl pStar (listToGgmCopath d (List.replicate d 0#128)) u = 0#128
  | 0, _, _, _ => rfl
  | d + 1, lvl, pStar, u => by
    simp only [List.replicate_succ, listToGgmCopath, ggmExpandPunctured]
    split
    · exact ggmExpandPunctured_zeroGgmPrg d (lvl + 1) (pStar.setWidth d) (u.setWidth d)
    · exact ggmExpandFull_zeroGgmPrg d (lvl + 1) (u.setWidth d)

private theorem reconstructPeerSpcotCheckValues_zeroGgmPrg
    (sessionId : List UInt8) (receiverId d : Nat) (peer : PcgPeerSpcotRecord)
    (hCp : peer.copath = List.replicate d 0#128) :
    let pStar : BitVec d := BitVec.ofNat d peer.puncturedIdx
    let (gamma0, chi0) := deriveSpcotChallengePair sessionId peer.peerId receiverId d 0 peer.spcotChalCoin
    let (gamma1, chi1) := deriveSpcotChallengePair sessionId peer.peerId receiverId d 1 peer.spcotChalCoin
    reconstructPeerSpcotCheckValues zeroGgmPrg sessionId receiverId d peer =
      (towerAdd 7 peer.spcotMaskMacs.1
        (towerMul 7 gamma0 (towerMul 7 (spcotLeafWeight chi0 pStar) peer.corrOffset)),
       towerAdd 7 peer.spcotMaskMacs.2
        (towerMul 7 gamma1 (towerMul 7 (spcotLeafWeight chi1 pStar) peer.corrOffset))) := by
  intro pStar
  unfold reconstructPeerSpcotCheckValues
  rw [hCp]
  have hPuncZeroFn : ggmExpandPunctured zeroGgmPrg d 0 pStar
      (listToGgmCopath d (List.replicate d 0#128)) = (fun _ => 0#128) := by
    funext u; exact ggmExpandPunctured_zeroGgmPrg d 0 pStar u
  dsimp only [pStar] at hPuncZeroFn ⊢
  rw [hPuncZeroFn, bvXorSum128_zero]
  have hUnpackZero : unpackTower 7 (0#128) = towerZero 7 := unpackTower_zero 7
  rw [hUnpackZero, towerZero_add]
  have hCombo : ∀ (gamma chi : Tower128),
      evalPuncturedTreeSpcotCombo d gamma chi (fun _ => 0#128) (BitVec.ofNat d peer.puncturedIdx) peer.corrOffset =
        towerMul 7 gamma (towerMul 7 (spcotLeafWeight chi (BitVec.ofNat d peer.puncturedIdx)) peer.corrOffset) := by
    intro gamma chi
    unfold evalPuncturedTreeSpcotCombo
    have hEach : ∀ u : BitVec d,
        towerMul 7 (spcotLeafWeight chi u)
          (if u = BitVec.ofNat d peer.puncturedIdx then peer.corrOffset else unpackTower 7 (0#128)) =
        (if u = BitVec.ofNat d peer.puncturedIdx then
          towerMul 7 (spcotLeafWeight chi (BitVec.ofNat d peer.puncturedIdx)) peer.corrOffset
        else towerZero 7) := by
      intro u
      if hu : u = BitVec.ofNat d peer.puncturedIdx then
        subst hu; simp only [↓reduceIte]
      else
        simp only [hu, ↓reduceIte, hUnpackZero, towerMul_zero]
    rw [bvTowerSum128_congr hEach, bvTowerSum128_single]
  cases deriveSpcotChallengePair sessionId peer.peerId receiverId d 0 peer.spcotChalCoin with
  | mk g0 c0 =>
    cases deriveSpcotChallengePair sessionId peer.peerId receiverId d 1 peer.spcotChalCoin with
    | mk g1 c1 =>
      dsimp only
      rw [hCombo g0 c0, hCombo g1 c1]

def samplePcgSessionId : List UInt8 := List.replicate 32 0x33
def samplePcgChalCoin : List UInt8 := List.replicate 32 0x44

def sampleHonestPeerRecordWithTag
    (tagFn : List UInt8 → Nat → Nat → List UInt8 → (Tower128 × Tower128) → List UInt8) :
    PcgPeerSpcotRecord where
  peerId := 1
  puncturedIdx := 0
  copath := List.replicate 14 0#128
  corrOffset := towerZero 7
  spcotChalCoin := samplePcgChalCoin
  spcotMaskMacs := (towerZero 7, towerZero 7)
  spcotExpectedTag := tagFn samplePcgSessionId 1 0 samplePcgChalCoin (towerZero 7, towerZero 7)
  lsbCheckChoices := 1#128
  lsbCheckRecvMacs := mkSenderAlphaRecvMacs (towerOne 7) (fun _ => towerZero 7) (1#128)
  senderAlphaLsbKeyBits := 0#128

def sampleHonestPeerRecord : PcgPeerSpcotRecord :=
  sampleHonestPeerRecordWithTag computeSpcotCheckTag

def sampleHonestPcgSeedHeaderWithTag
    (tagFn : List UInt8 → Nat → Nat → List UInt8 → (Tower128 × Tower128) → List UInt8) :
    ValidatedPcgSeedHeader where
  sessionId := samplePcgSessionId
  numParties := 2
  myPartyId := 0
  treeDepth := 14
  macAlpha := towerOne 7
  peers := [sampleHonestPeerRecordWithTag tagFn]

def sampleHonestPcgSeedHeader : ValidatedPcgSeedHeader :=
  sampleHonestPcgSeedHeaderWithTag computeSpcotCheckTag

/-- Bijective 32-byte tag oracle `encodeTower128Le w.1 ++ encodeTower128Le w.2` for ideal-tag `#tooth` tests. -/
def raw32SpcotTagOracle
    (_sessionId : List UInt8) (_senderId _receiverId : Nat) (_chalCoin : List UInt8)
    (wVals : Tower128 × Tower128) : List UInt8 :=
  encodeTower128Le wVals.1 ++ encodeTower128Le wVals.2

/-- Deterministic length-preserving byte flip on the head byte of a non-empty tag. -/
def flipHeadByte : List UInt8 → List UInt8
  | [] => []
  | b :: bs => (if b = 0 then 1 else 0) :: bs

private theorem flipHeadByte_length (xs : List UInt8) : (flipHeadByte xs).length = xs.length := by
  cases xs <;> rfl

private theorem flipHeadByte_ne_of_pos {xs : List UInt8} (hPos : 0 < xs.length) :
    flipHeadByte xs ≠ xs := by
  cases xs with
  | nil => cases hPos
  | cons b bs =>
    intro hEq
    have hb : (if b = 0 then (1 : UInt8) else 0) = b := (List.cons.inj hEq).1
    if h0 : b = 0 then
      subst h0
      simp only [↓reduceIte] at hb
      revert hb; decide
    else
      simp only [h0, ↓reduceIte] at hb
      exact h0 hb.symm

private theorem reconstructCorruptCorrOffset_ne_zero
    (tagFn : List UInt8 → Nat → Nat → List UInt8 → (Tower128 × Tower128) → List UInt8)
    (corrOffset' : Tower128) (hNz : corrOffset' ≠ towerZero 7) :
    reconstructPeerSpcotCheckValues zeroGgmPrg samplePcgSessionId 0 14
      { sampleHonestPeerRecordWithTag tagFn with corrOffset := corrOffset' } ≠
      (towerZero 7, towerZero 7) := by
  let peer' := { sampleHonestPeerRecordWithTag tagFn with corrOffset := corrOffset' }
  have hSimp := reconstructPeerSpcotCheckValues_zeroGgmPrg samplePcgSessionId 0 14 peer' rfl
  dsimp only [peer', sampleHonestPeerRecordWithTag] at hSimp
  have hIdx0 : BitVec.ofNat 14 0 = 0#14 := rfl
  have ⟨hg0, hc0⟩ := deriveSpcotChallengePair_ne_zero samplePcgSessionId 1 0 14 0 samplePcgChalCoin
  cases hPair0 : deriveSpcotChallengePair samplePcgSessionId 1 0 14 0 samplePcgChalCoin with
  | mk g0 c0 =>
    rw [hPair0] at hg0 hc0 hSimp
    dsimp only at hg0 hc0
    cases hPair1 : deriveSpcotChallengePair samplePcgSessionId 1 0 14 1 samplePcgChalCoin with
    | mk g1 c1 =>
      rw [hPair1] at hSimp
      dsimp only at hSimp
      rw [hIdx0, spcotLeafWeight_zero_idx 14 c0, spcotLeafWeight_zero_idx 14 c1,
          towerZero_add, towerZero_add] at hSimp
      intro hEqZero
      dsimp only [sampleHonestPeerRecordWithTag] at hEqZero
      rw [hSimp] at hEqZero
      have hFst : towerMul 7 g0 (towerMul 7 c0 corrOffset') = towerZero 7 :=
        congrArg Prod.fst hEqZero
      rcases (towerMul_eq_zero_iff 7 g0 (towerMul 7 c0 corrOffset')).mp hFst with hZ0 | hZ1
      · exact hg0 hZ0
      · rcases (towerMul_eq_zero_iff 7 c0 corrOffset').mp hZ1 with hZ2 | hZ3
        · exact hc0 hZ2
        · exact hNz hZ3

private theorem sampleHonestPcgSeedHeaderWithTag_accepts
    (tagFn : List UInt8 → Nat → Nat → List UInt8 → (Tower128 × Tower128) → List UInt8)
    (hTagLen : (tagFn samplePcgSessionId 1 0 samplePcgChalCoin (towerZero 7, towerZero 7)).length = 32) :
    checkPcgSeedHeaderWithTag tagFn zeroGgmPrg (sampleHonestPcgSeedHeaderWithTag tagFn) = true := by
  have hW0 : reconstructPeerSpcotCheckValues zeroGgmPrg samplePcgSessionId 0 14
      (sampleHonestPeerRecordWithTag tagFn) = (towerZero 7, towerZero 7) := by
    have hSimp := reconstructPeerSpcotCheckValues_zeroGgmPrg samplePcgSessionId 0 14
      (sampleHonestPeerRecordWithTag tagFn) rfl
    dsimp only [sampleHonestPeerRecordWithTag] at hSimp
    cases hP0 : deriveSpcotChallengePair samplePcgSessionId 1 0 14 0 samplePcgChalCoin with
    | mk g0 c0 =>
      rw [hP0] at hSimp
      cases hP1 : deriveSpcotChallengePair samplePcgSessionId 1 0 14 1 samplePcgChalCoin with
      | mk g1 c1 =>
        rw [hP1] at hSimp
        dsimp only at hSimp
        simp only [towerMul_zero, towerAdd_zero] at hSimp
        exact hSimp
  have hZeroKeyHonest : ∀ i : Nat, i < 128 → (0#128).getLsbD i = towerLsb (towerZero 7) := by
    intro i _; rw [BitVec.getLsbD_zero, towerLsb_zero 7]
  have hLsbOk : verifyPeerSenderAlphaLsb (1#128)
      (mkSenderAlphaRecvMacs (towerOne 7) (fun _ => towerZero 7) (1#128)) (0#128) = true :=
    verifyPeerSenderAlphaLsb_complete (towerOne 7) (towerLsb_one 7) (fun _ => towerZero 7)
      (1#128) (0#128) (by decide) hZeroKeyHonest
  have hPeerOk : checkPeerSpcotRecordWithTag tagFn zeroGgmPrg
      (sampleHonestPcgSeedHeaderWithTag tagFn) (sampleHonestPeerRecordWithTag tagFn) = true := by
    unfold checkPeerSpcotRecordWithTag
    rw [show (sampleHonestPcgSeedHeaderWithTag tagFn).sessionId = samplePcgSessionId from rfl,
        show (sampleHonestPcgSeedHeaderWithTag tagFn).myPartyId = 0 from rfl,
        show (sampleHonestPcgSeedHeaderWithTag tagFn).treeDepth = 14 from rfl,
        show (sampleHonestPcgSeedHeaderWithTag tagFn).numParties = 2 from rfl,
        hW0,
        show (sampleHonestPeerRecordWithTag tagFn).peerId = 1 from rfl,
        show (sampleHonestPeerRecordWithTag tagFn).puncturedIdx = 0 from rfl,
        show (sampleHonestPeerRecordWithTag tagFn).copath = List.replicate 14 0#128 from rfl,
        show (sampleHonestPeerRecordWithTag tagFn).spcotChalCoin = samplePcgChalCoin from rfl,
        show (sampleHonestPeerRecordWithTag tagFn).spcotExpectedTag =
          tagFn samplePcgSessionId 1 0 samplePcgChalCoin (towerZero 7, towerZero 7) from rfl,
        show (sampleHonestPeerRecordWithTag tagFn).lsbCheckChoices = 1#128 from rfl,
        show (sampleHonestPeerRecordWithTag tagFn).lsbCheckRecvMacs =
          mkSenderAlphaRecvMacs (towerOne 7) (fun _ => towerZero 7) (1#128) from rfl,
        show (sampleHonestPeerRecordWithTag tagFn).senderAlphaLsbKeyBits = 0#128 from rfl]
    have hTagRefl : decide
        (tagFn samplePcgSessionId 1 0 samplePcgChalCoin (towerZero 7, towerZero 7) =
         tagFn samplePcgSessionId 1 0 samplePcgChalCoin (towerZero 7, towerZero 7)) = true :=
      decide_eq_true rfl
    rw [hLsbOk, hTagLen, hTagRefl]
    decide
  have hAllOk : (sampleHonestPcgSeedHeaderWithTag tagFn).peers.all
      (checkPeerSpcotRecordWithTag tagFn zeroGgmPrg (sampleHonestPcgSeedHeaderWithTag tagFn)) = true := by
    change (checkPeerSpcotRecordWithTag tagFn zeroGgmPrg
      (sampleHonestPcgSeedHeaderWithTag tagFn) (sampleHonestPeerRecordWithTag tagFn) && true) = true
    rw [hPeerOk]
    rfl
  unfold checkPcgSeedHeaderWithTag
  rw [hAllOk,
      show (sampleHonestPcgSeedHeaderWithTag tagFn).sessionId = samplePcgSessionId from rfl,
      show (sampleHonestPcgSeedHeaderWithTag tagFn).numParties = 2 from rfl,
      show (sampleHonestPcgSeedHeaderWithTag tagFn).myPartyId = 0 from rfl,
      show (sampleHonestPcgSeedHeaderWithTag tagFn).treeDepth = 14 from rfl,
      show (sampleHonestPcgSeedHeaderWithTag tagFn).macAlpha = towerOne 7 from rfl,
      show (sampleHonestPcgSeedHeaderWithTag tagFn).peers.length = 1 from rfl,
      show (sampleHonestPcgSeedHeaderWithTag tagFn).peerIds = [1] from rfl,
      towerLsb_one 7]
  decide

/-- Constructive `0 Classical.choice` collision extractor: if `checkPcgSeedHeader` accepts a
    seed header whose `corrOffset` was mutated to any `corrOffset' ≠ towerZero 7`, extracts an
    explicit `HashCollisionWitness (cshake256Fixed 32 spcotTagDomain)`! -/
def extractCollisionFromCorruptCorrOffset
    (corrOffset' : Tower128) (hNz : corrOffset' ≠ towerZero 7)
    (hAcc : checkPcgSeedHeader zeroGgmPrg
      { sampleHonestPcgSeedHeader with
        peers := [{ sampleHonestPeerRecord with corrOffset := corrOffset' }] } = true) :
    HashCollisionWitness (cshake256Fixed 32 spcotTagDomain) :=
  have hTagEq :
      computeSpcotCheckTag samplePcgSessionId 1 0 samplePcgChalCoin
        (reconstructPeerSpcotCheckValues zeroGgmPrg samplePcgSessionId 0 14
          { sampleHonestPeerRecord with corrOffset := corrOffset' }) =
      computeSpcotCheckTag samplePcgSessionId 1 0 samplePcgChalCoin (towerZero 7, towerZero 7) := by
    unfold checkPcgSeedHeader checkPcgSeedHeaderWithTag at hAcc
    simp only [Bool.and_eq_true] at hAcc
    have hPeers := hAcc.2
    dsimp only [List.all] at hPeers
    simp only [Bool.and_true] at hPeers
    unfold checkPeerSpcotRecordWithTag at hPeers
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hPeers
    exact hPeers.2
  match computeSpcotCheckTag_binding (by decide : 1 < 2 ^ 64) (by decide : 1 < 2 ^ 64)
      (by decide : 0 < 2 ^ 64) (by decide : 0 < 2 ^ 64) hTagEq with
  | PSum.inl hInl =>
    False.elim (reconstructCorruptCorrOffset_ne_zero computeSpcotCheckTag corrOffset' hNz hInl.2.2.2.2)
  | PSum.inr col => col

/-- **Inhabitedness & `#tooth` Mutation Sensitivity of `checkPcgSeedHeader` (`tooth_checkPcgSeedHeader_rejects_corrupt_corrOffset_and_zero_lsb`, `C0-2`)**:
    At production tree depth `d = 14`:
    1. **Honest Acceptance**: `checkPcgSeedHeader zeroGgmPrg sampleHonestPcgSeedHeader = true` (inhabited!).
    2. **Self `LSB(macAlpha) = 0` Rejected**: setting `macAlpha := towerZero 7` returns `false`.
    3. **Peer Sender `LSB(alpha_sender) = 0` Rejected**: replacing `lsbCheckRecvMacs` with zero-LSB
       OT MACs (`List.replicate 128 (towerZero 7)`) returns `false`.
    4. **Tampered `spcotExpectedTag` Rejected**: flipping byte 0 of `spcotExpectedTag` returns `false`
       unconditionally (`0` collision assumption).
    5. **Corrupted `corrOffset` Rejected**: flipping `corrOffset` from `towerZero 7` to `towerOne 7`
       shifts `reconstructPeerSpcotCheckValues` to a provably non-zero check pair (`NoZeroDivisors`),
       returning `checkPcgSeedHeaderWithTag raw32SpcotTagOracle = false` unconditionally AND returning
       production `checkPcgSeedHeader = false` under `¬ Collision (cshake256Fixed 32 spcotTagDomain)`
       (with constructive extractor `extractCollisionFromCorruptCorrOffset`)! -/
theorem tooth_checkPcgSeedHeader_rejects_corrupt_corrOffset_and_zero_lsb :
    let hdr := sampleHonestPcgSeedHeader
    let hdrZeroSelfLsb := { hdr with macAlpha := towerZero 7 }
    let peerZeroSenderLsb := { sampleHonestPeerRecord with lsbCheckRecvMacs := List.replicate 128 (towerZero 7) }
    let hdrZeroSenderLsb := { hdr with peers := [peerZeroSenderLsb] }
    let peerTamperedTag := { sampleHonestPeerRecord with
      spcotExpectedTag := flipHeadByte sampleHonestPeerRecord.spcotExpectedTag }
    let hdrTamperedTag := { hdr with peers := [peerTamperedTag] }
    let hdrIdealCorrupt := { sampleHonestPcgSeedHeaderWithTag raw32SpcotTagOracle with
      peers := [{ sampleHonestPeerRecordWithTag raw32SpcotTagOracle with corrOffset := towerOne 7 }] }
    let hdrCorruptOffset := { hdr with
      peers := [{ sampleHonestPeerRecord with corrOffset := towerOne 7 }] }
    checkPcgSeedHeader zeroGgmPrg hdr = true ∧
    checkPcgSeedHeader zeroGgmPrg hdrZeroSelfLsb = false ∧
    checkPcgSeedHeader zeroGgmPrg hdrZeroSenderLsb = false ∧
    checkPcgSeedHeader zeroGgmPrg hdrTamperedTag = false ∧
    checkPcgSeedHeaderWithTag raw32SpcotTagOracle zeroGgmPrg hdrIdealCorrupt = false ∧
    (¬ Collision (cshake256Fixed 32 spcotTagDomain) →
      checkPcgSeedHeader zeroGgmPrg hdrCorruptOffset = false) := by
  intro hdr hdrZeroSelfLsb peerZeroSenderLsb hdrZeroSenderLsb peerTamperedTag hdrTamperedTag
    hdrIdealCorrupt hdrCorruptOffset
  -- 1. Honest header accepts!
  have hAccept : checkPcgSeedHeader zeroGgmPrg hdr = true :=
    sampleHonestPcgSeedHeaderWithTag_accepts computeSpcotCheckTag (cshake256Xof_length 32 _ _)
  -- 2. Self `LSB(macAlpha) = 0` rejected!
  have hRejSelfLsb : checkPcgSeedHeader zeroGgmPrg hdrZeroSelfLsb = false := by
    unfold checkPcgSeedHeader checkPcgSeedHeaderWithTag
    dsimp only [hdrZeroSelfLsb, hdr, sampleHonestPcgSeedHeader, sampleHonestPcgSeedHeaderWithTag]
    rw [towerLsb_zero 7]
    simp
  -- 3. Peer Sender `LSB(alpha_sender) = 0` rejected!
  have hLsbZeroRej : verifyPeerSenderAlphaLsb peerZeroSenderLsb.lsbCheckChoices
      peerZeroSenderLsb.lsbCheckRecvMacs peerZeroSenderLsb.senderAlphaLsbKeyBits = false := by
    unfold verifyPeerSenderAlphaLsb
    dsimp only [peerZeroSenderLsb, sampleHonestPeerRecord, sampleHonestPeerRecordWithTag]
    have hAux0 : verifySenderAlphaLsbAux 0 (1#128) (List.replicate 128 (towerZero 7)) (0#128) = false := by
      change (decide ((towerLsb (towerZero 7) ^^ (0#128).getLsbD 0) = (1#128).getLsbD 0) &&
        verifySenderAlphaLsbAux 1 (1#128) (List.replicate 127 (towerZero 7)) (0#128)) = false
      rw [towerLsb_zero 7]
      have hb0 : (0#128).getLsbD 0 = false := by decide
      have hb1 : (1#128).getLsbD 0 = true := by decide
      rw [hb0, hb1]
      rfl
    rw [hAux0, Bool.and_false]
  have hRejSenderLsb : checkPcgSeedHeader zeroGgmPrg hdrZeroSenderLsb = false := by
    unfold checkPcgSeedHeader checkPcgSeedHeaderWithTag checkPeerSpcotRecordWithTag
    dsimp only [hdrZeroSenderLsb, hdr, sampleHonestPcgSeedHeader, sampleHonestPcgSeedHeaderWithTag, List.all]
    rw [hLsbZeroRej]
    simp
  -- 4. Tampered `spcotExpectedTag` rejected unconditionally!
  have hRejTamperedTag : checkPcgSeedHeader zeroGgmPrg hdrTamperedTag = false := by
    have hW0 : reconstructPeerSpcotCheckValues zeroGgmPrg samplePcgSessionId 0 14 peerTamperedTag =
        (towerZero 7, towerZero 7) := by
      have hSimp := reconstructPeerSpcotCheckValues_zeroGgmPrg samplePcgSessionId 0 14 peerTamperedTag rfl
      dsimp only [peerTamperedTag, sampleHonestPeerRecord, sampleHonestPeerRecordWithTag] at hSimp
      cases hP0 : deriveSpcotChallengePair samplePcgSessionId 1 0 14 0 samplePcgChalCoin with
      | mk g0 c0 =>
        rw [hP0] at hSimp
        cases hP1 : deriveSpcotChallengePair samplePcgSessionId 1 0 14 1 samplePcgChalCoin with
        | mk g1 c1 =>
          rw [hP1] at hSimp
          dsimp only at hSimp
          simp only [towerMul_zero, towerAdd_zero] at hSimp
          exact hSimp
    have hTagLen : (computeSpcotCheckTag samplePcgSessionId 1 0 samplePcgChalCoin
        (towerZero 7, towerZero 7)).length = 32 := cshake256Xof_length 32 _ _
    have hNeTag : computeSpcotCheckTag samplePcgSessionId 1 0 samplePcgChalCoin (towerZero 7, towerZero 7) ≠
        flipHeadByte (computeSpcotCheckTag samplePcgSessionId 1 0 samplePcgChalCoin (towerZero 7, towerZero 7)) :=
      fun hEq => flipHeadByte_ne_of_pos (by omega : 0 < (computeSpcotCheckTag samplePcgSessionId 1 0 samplePcgChalCoin (towerZero 7, towerZero 7)).length) hEq.symm
    cases hb : checkPcgSeedHeader zeroGgmPrg hdrTamperedTag
    · rfl
    · exfalso
      unfold checkPcgSeedHeader checkPcgSeedHeaderWithTag at hb
      simp only [Bool.and_eq_true] at hb
      have hPeers := hb.2
      dsimp only [hdrTamperedTag, List.all] at hPeers
      simp only [Bool.and_true] at hPeers
      unfold checkPeerSpcotRecordWithTag at hPeers
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hPeers
      have hEqTag := hPeers.2
      dsimp only [hdrTamperedTag, hdr, sampleHonestPcgSeedHeader, sampleHonestPcgSeedHeaderWithTag] at hEqTag
      have hpId : peerTamperedTag.peerId = 1 := rfl
      have hpCoin : peerTamperedTag.spcotChalCoin = samplePcgChalCoin := rfl
      have hpExp : peerTamperedTag.spcotExpectedTag =
          flipHeadByte (computeSpcotCheckTag samplePcgSessionId 1 0 samplePcgChalCoin (towerZero 7, towerZero 7)) := rfl
      rw [hW0, hpId, hpCoin, hpExp] at hEqTag
      exact hNeTag hEqTag
  -- 5a. Corrupted `corrOffset = towerOne 7` rejected unconditionally under injective 32-byte tag oracle!
  have hRejIdealCorrupt : checkPcgSeedHeaderWithTag raw32SpcotTagOracle zeroGgmPrg hdrIdealCorrupt = false := by
    cases hb : checkPcgSeedHeaderWithTag raw32SpcotTagOracle zeroGgmPrg hdrIdealCorrupt
    · rfl
    · exfalso
      unfold checkPcgSeedHeaderWithTag at hb
      simp only [Bool.and_eq_true] at hb
      have hPeers := hb.2
      dsimp only [hdrIdealCorrupt, List.all] at hPeers
      simp only [Bool.and_true] at hPeers
      unfold checkPeerSpcotRecordWithTag raw32SpcotTagOracle at hPeers
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hPeers
      have hRawEq := hPeers.2
      dsimp only [sampleHonestPcgSeedHeaderWithTag, sampleHonestPeerRecordWithTag, raw32SpcotTagOracle] at hRawEq
      obtain ⟨h1, h2⟩ := List.append_inj hRawEq (by simp [encodeTower128Le_length])
      have hwEq : reconstructPeerSpcotCheckValues zeroGgmPrg samplePcgSessionId 0 14
          { sampleHonestPeerRecordWithTag raw32SpcotTagOracle with corrOffset := towerOne 7 } =
          (towerZero 7, towerZero 7) :=
        Prod.ext (encodeTower128Le_injective h1) (encodeTower128Le_injective h2)
      exact reconstructCorruptCorrOffset_ne_zero raw32SpcotTagOracle (towerOne 7) (towerOne_ne_zero 7) hwEq
  -- 5b. Corrupted `corrOffset = towerOne 7` rejected on production `checkPcgSeedHeader` under collision-resistance!
  have hRejProdCorrupt : ¬ Collision (cshake256Fixed 32 spcotTagDomain) →
      checkPcgSeedHeader zeroGgmPrg hdrCorruptOffset = false := by
    intro hNoCol
    cases hb : checkPcgSeedHeader zeroGgmPrg hdrCorruptOffset
    · rfl
    · exact False.elim (hNoCol (extractCollisionFromCorruptCorrOffset (towerOne 7) (towerOne_ne_zero 7) hb).toCollision)
  exact ⟨hAccept, hRejSelfLsb, hRejSenderLsb, hRejTamperedTag, hRejIdealCorrupt, hRejProdCorrupt⟩

/-! ### 4.3 Dense Dual-LPN PCG Cancellation, 50/50 Share Uniformity & `[P0-02]` `#tooth` -/

/-- Matrix-vector `GF(2)` product `(H_lpn * leaves)` over 128-bit leaf seeds (`m` output rows, `2^d` columns). -/
def lpnMatVec128 (d m : Nat) (H : Fin m → BitVec d → Bool)
    (leaves : BitVec d → BitVec 128) : Fin m → BitVec 128 :=
  fun row => bvXorSum128 d (fun u => if H row u then leaves u else 0#128)

/-- Sender's dense dual-LPN share vector: $s_{\mathsf{dense}} = H_{\mathsf{lpn}} \cdot \mathsf{fullLeaves}$. -/
def pcgDenseSenderShare (d m : Nat) (H : Fin m → BitVec d → Bool)
    (fullLeaves : BitVec d → BitVec 128) : Fin m → BitVec 128 :=
  lpnMatVec128 d m H fullLeaves

/-- Receiver's dense dual-LPN share vector:
    $r_{\mathsf{dense}} = (H_{\mathsf{lpn}} \cdot \mathsf{puncLeaves}) \oplus H_{\mathsf{lpn}}[:, p^*] \cdot \mathsf{corr}$. -/
def pcgDenseReceiverShare (d m : Nat) (H : Fin m → BitVec d → Bool)
    (puncLeaves : BitVec d → BitVec 128) (pStar : BitVec d) (corr : BitVec 128) : Fin m → BitVec 128 :=
  fun row => lpnMatVec128 d m H puncLeaves row ^^^ (if H row pStar then corr else 0#128)

/-- **Exact Dense Dual-LPN Algebraic Cancellation (`pcg_dense_dual_lpn_cancellation`)**:
    Composing `ggmExpandFull` and `ggmExpandPunctured` with ANY $m \times 2^d$ binary parity-check matrix
    `H` (including Expand-Accumulate `E ∘ Acc` in `pcg_dense.rs`):
    1. `(H * fullLeaves) ^^^ (H * puncLeaves ^^^ H[:, p*] · corr) = H[:, p*] · (fullLeaves p* ^^^ corr)`
       for every row `row : Fin m`!
    2. Setting `corr = fullLeaves p* ^^^ delta` (honest SPCOT correlation offset!) yields the **exact**
       sparse LPN correlation `if H row p* then delta else 0#128` (`H[:, p*] · delta`) while cancelling
       all $2^d - 1$ non-punctured dense leaf contributions! -/
theorem pcg_dense_dual_lpn_cancellation (prg : GgmPrg) (d m : Nat)
    (H : Fin m → BitVec d → Bool)
    (root delta : BitVec 128) (pStar : BitVec d) :
    let fullLeaves := ggmExpandFull prg d 0 root
    let copath := ggmMakeCopath prg d 0 root pStar
    let puncLeaves := ggmExpandPunctured prg d 0 pStar copath
    (∀ (corr : BitVec 128) (row : Fin m),
      pcgDenseSenderShare d m H fullLeaves row ^^^
        pcgDenseReceiverShare d m H puncLeaves pStar corr row =
      if H row pStar then (fullLeaves pStar ^^^ corr) else 0#128) ∧
    (∀ row : Fin m,
      let corr := fullLeaves pStar ^^^ delta
      pcgDenseSenderShare d m H fullLeaves row ^^^
        pcgDenseReceiverShare d m H puncLeaves pStar corr row =
      if H row pStar then delta else 0#128) := by
  intro fullLeaves copath puncLeaves
  obtain ⟨hZeroAtP, hAgreeOffP⟩ := ggmExpandPunctured_exact prg d 0 root pStar
  have hZeroAtP' : puncLeaves pStar = 0#128 := hZeroAtP
  have hAgreeOffP' : ∀ u : BitVec d, u ≠ pStar → puncLeaves u = fullLeaves u := hAgreeOffP
  have hGen : ∀ (corr : BitVec 128) (row : Fin m),
      pcgDenseSenderShare d m H fullLeaves row ^^^
        pcgDenseReceiverShare d m H puncLeaves pStar corr row =
      if H row pStar then (fullLeaves pStar ^^^ corr) else 0#128 := by
    intro corr row
    unfold pcgDenseSenderShare pcgDenseReceiverShare lpnMatVec128
    have hAssoc : ∀ (a b c : BitVec 128), a ^^^ (b ^^^ c) = (a ^^^ b) ^^^ c := by
      intro a b c; apply BitVec.eq_of_getLsbD_eq; intro i _
      simp only [BitVec.getLsbD_xor]
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> rfl
    rw [hAssoc, ← bvXorSum128_xor]
    have hPoint : ∀ u : BitVec d,
        (if H row u then fullLeaves u else 0#128) ^^^ (if H row u then puncLeaves u else 0#128) =
          if u = pStar then (if H row pStar then fullLeaves pStar else 0#128) else 0#128 := by
      intro u
      by_cases hu : u = pStar
      · rw [hu, hZeroAtP']
        simp only [↓reduceIte]
        cases H row pStar
        · simp only [Bool.false_eq_true, ↓reduceIte, BitVec.xor_zero]
        · simp only [↓reduceIte, BitVec.xor_zero]
      · rw [hAgreeOffP' u hu]
        simp only [BitVec.xor_self, hu, ↓reduceIte]
    rw [bvXorSum128_congr hPoint, bvXorSum128_single]
    cases H row pStar
    · simp only [Bool.false_eq_true, ↓reduceIte, BitVec.zero_xor]
    · simp only [↓reduceIte]
  refine ⟨hGen, ?_⟩
  intro row
  dsimp only
  rw [hGen (fullLeaves pStar ^^^ delta) row]
  have hCancel : fullLeaves pStar ^^^ (fullLeaves pStar ^^^ delta) = delta := by
    apply BitVec.eq_of_getLsbD_eq; intro i _
    simp only [BitVec.getLsbD_xor]
    cases (fullLeaves pStar).getLsbD i <;> cases delta.getLsbD i <;> rfl
  rw [hCancel]

/-- Constructive lowest-set-bit mask `oneHotLowest n h` (`0 Classical.choice`) satisfying
    `gf2Dot n h (oneHotLowest n h) = true` whenever `h ≠ 0#n`! -/
def oneHotLowest : (n : Nat) → BitVec n → BitVec n
  | 0, _ => 0#0
  | n + 1, h =>
    if h.getLsbD n then
      BitVec.cons true (0#n)
    else
      BitVec.cons false (oneHotLowest n (h.setWidth n))

private theorem gf2Dot_oneHotLowest : ∀ (n : Nat) (h : BitVec n),
    h ≠ 0#n → gf2Dot n h (oneHotLowest n h) = true
  | 0, h, hNe => False.elim (hNe (BitVec.eq_nil h))
  | n + 1, h, hNe => by
    simp only [oneHotLowest]
    cases hb : h.getLsbD n
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hLoNe : h.setWidth n ≠ 0#n := by
        intro hz; apply hNe
        have hSplit : BitVec.cons (h.getLsbD n) (h.setWidth n) = h := bvCons_split h
        rw [← hSplit, hb, hz, bvZero_eq_cons]
      have hSet : (BitVec.cons false (oneHotLowest n (h.setWidth n))).setWidth n =
          oneHotLowest n (h.setWidth n) := setWidth_cons false (oneHotLowest n (h.setWidth n))
      conv => lhs; unfold gf2Dot
      simp only [hb, BitVec.getLsbD_cons, ↓reduceIte, Bool.false_and, Bool.false_xor,
        hSet, gf2Dot_oneHotLowest n (h.setWidth n) hLoNe]
    · simp only [↓reduceIte]
      have hSet0 : (BitVec.cons true (0#n)).setWidth n = 0#n := setWidth_cons true (0#n)
      conv => lhs; unfold gf2Dot
      simp only [hb, BitVec.getLsbD_cons, ↓reduceIte, Bool.true_and,
        hSet0, gf2Dot_zero_right, Bool.xor_false]

/-- **Constructive 50/50 Uniformity Bijection of Dense PCG Shares (`pcg_dense_share_uniform_bijection`)**:
    For ANY non-zero LPN parity-check row `h : BitVec L` (`h ≠ 0#L`, e.g. 4-regular Expand-Accumulate
    at $L = 2^{14} = 16384$ or $L = 2^{15} = 32768$):
    1. We construct an explicit involutive `SimpleEquiv` between `{ s : BitVec L // gf2Dot L h s = false }`
       and `{ s : BitVec L // gf2Dot L h s = true }` (`0 Classical.choice`).
    2. Over all $2^L$ leaf bit-vectors, **exact** count $2^{L - 1}$ produce share bit `true` and
       $2^{L - 1}$ produce `false` (`2 * oneCount = 2^L`, exact `1/2 = 50%` density)! -/
def pcg_dense_share_uniform_bijection (L : Nat) (h : BitVec L) (hNe : h ≠ 0#L) :
    SimpleEquiv { s : BitVec L // gf2Dot L h s = false } { s : BitVec L // gf2Dot L h s = true } :=
  let pivot := oneHotLowest L h
  have hPivotDot : gf2Dot L h pivot = true := gf2Dot_oneHotLowest L h hNe
  have hSelfXor : ∀ s : BitVec L, (s ^^^ pivot) ^^^ pivot = s := by
    intro s; apply BitVec.eq_of_getLsbD_eq; intro i _
    simp only [BitVec.getLsbD_xor]
    cases s.getLsbD i <;> cases pivot.getLsbD i <;> rfl
  { toFun := fun ⟨s, hs⟩ => ⟨s ^^^ pivot, by rw [gf2Dot_xor_right, hs, hPivotDot]; rfl⟩
    invFun := fun ⟨s, hs⟩ => ⟨s ^^^ pivot, by rw [gf2Dot_xor_right, hs, hPivotDot]; rfl⟩
    left_inv := fun ⟨s, _⟩ => Subtype.ext (hSelfXor s)
    right_inv := fun ⟨s, _⟩ => Subtype.ext (hSelfXor s) }

theorem pcg_dense_share_exact_half_density (L : Nat) (h : BitVec L) (hNe : h ≠ 0#L) :
    let oneCount := bvSum L (fun s => if gf2Dot L h s = true then 1 else 0)
    oneCount = 2 ^ (L - 1) ∧ 2 * oneCount = 2 ^ L := by
  intro oneCount
  have hLPos : 1 ≤ L := by
    cases L with
    | zero => exact False.elim (hNe (BitVec.eq_nil h))
    | succ l => omega
  have hInt : (oneCount : Int) = ((2 ^ (L - 1) : Nat) : Int) := by
    dsimp [oneCount]
    rw [intBvSum_of_bvSum]
    have hCongr : intBvSum L (fun s => (((if gf2Dot L h s = true then 1 else 0 : Nat) : Int))) =
        intBvSum L (fun s => if gf2Dot L s h = true then 1 else 0) := by
      apply intBvSum_congr; intro s; rw [gf2Dot_comm]; split <;> rfl
    rw [hCongr]
    exact gf2Dot_balanced L h hNe true
  have hEq : oneCount = 2 ^ (L - 1) := Int.ofNat.inj hInt
  refine ⟨hEq, ?_⟩
  rw [hEq]
  have hSplit : L = (L - 1) + 1 := by omega
  conv => rhs; rw [hSplit, Nat.pow_succ]
  omega

/-- **`#tooth` Omitting `H_lpn * fullLeaves` Collapses Share Density to `rowWeight / 2^d` (`tooth_omitting_dense_baseline_collapses_density`, `P0-02`)**:
    If a broken PCG implementation omits the dense baseline `H_lpn * fullLeaves` and outputs only the
    punctured LPN term `H[row, p*]` across `p* ∈ BitVec d`:
    1. Its `1`-count over all $2^d$ punctures equals `bvRowWeight = bvSum d (fun p => if rowPred p then 1 else 0)`.
    2. For a unit-vector column (`rowPred p := (p = targetCol)`, the exact `compress_binary_bundle` `P0-02` bug!),
       `1`-count is **literally `1` out of `2^d`** (`1 / 16384` at `d = 14`, `1 / 32768` at `d = 15`),
       strictly collapsing below dense `1/2` (`2 * 1 < 2^d`) for every tree depth `d ≥ 2`! -/
theorem tooth_omitting_dense_baseline_collapses_density
    (d : Nat) (hd : 2 ≤ d) (targetCol : BitVec d) :
    let unitSparseShare : BitVec d → Bool := fun pStar => decide (pStar = targetCol)
    let sparseOneCount := bvSum d (fun pStar => if unitSparseShare pStar = true then 1 else 0)
    sparseOneCount = 1 ∧
    2 * sparseOneCount < 2 ^ d ∧
    bvSum 14 (fun pStar => if pStar = (0#14) then 1 else 0) = 1 ∧
    2 ^ 14 = 16384 := by
  intro unitSparseShare sparseOneCount
  have hInt : (sparseOneCount : Int) = 1 := by
    dsimp only [sparseOneCount, unitSparseShare]
    rw [intBvSum_of_bvSum]
    have hCongr : intBvSum d (fun pStar => (((if decide (pStar = targetCol) = true then 1 else 0 : Nat) : Int))) =
        intBvSum d (fun pStar => if pStar = targetCol then 1 else 0) := by
      apply intBvSum_congr; intro pStar
      by_cases hp : pStar = targetCol <;> simp [hp]
    rw [hCongr]
    exact intBvSum_indicator_one d targetCol
  have hOne : sparseOneCount = 1 := Int.ofNat.inj hInt
  have hPowGt : 2 < 2 ^ d := by
    have hSub : d = (d - 2) + 2 := by omega
    rw [hSub, Nat.pow_add]
    have hPos : 1 ≤ 2 ^ (d - 2) := Nat.two_pow_pos (d - 2)
    omega
  have h14Int : (bvSum 14 (fun pStar => if pStar = (0#14) then 1 else 0) : Int) = 1 := by
    rw [intBvSum_of_bvSum]
    have hC : intBvSum 14 (fun pStar => (((if pStar = (0#14) then 1 else 0 : Nat) : Int))) =
        intBvSum 14 (fun pStar => if pStar = (0#14) then 1 else 0) := by
      apply intBvSum_congr; intro p; split <;> rfl
    rw [hC]
    exact intBvSum_indicator_one 14 (0#14)
  exact ⟨hOne, by omega, Int.ofNat.inj h14Int, by decide⟩

/-- A fork extracted from the joint verifier, retaining both oracle/transcript inputs. -/
def HasJointOrFork (stmt : RlweOrStatement) : Prop :=
  ∃ (ro ro' : List UInt8 → List UInt8) (tr tr' : JointOrSigmaTranscript),
    Nonempty (ExtractedJointOrWitness stmt ro ro' tr tr')

theorem joint_fork_has_isometric_relation (stmt : RlweOrStatement)
    (h : HasJointOrFork stmt) :
    Nonempty (ShortMonomialRelaxedRlweWitness rlweZkpokReps 10 12289 stmt.toCyclotomic) := by
  rcases h with ⟨ro, ro', tr, tr', ⟨w⟩⟩
  exact ⟨w.toShortMonomialWitness⟩

theorem tooth_legacy_challenge_pair_has_no_inverse (inv : PolyRq1024) :
    CommRingOps.mul (CommRingOps.sub (polyRqFromChal20 108#20) (polyRqFromChal20 1026#20)) inv ≠
      CommRingOps.one := tooth_chal20_difference_not_invertible.2.2.2 inv

theorem witness_joint_or_fork : ∃ stmt, HasJointOrFork stmt := by
  rcases inhabited_jointOrSigma_and_extractor.2 with ⟨ro, ro', tr, tr', w⟩
  exact ⟨sampleRlweOrStatement, ro, ro', tr, tr', ⟨w⟩⟩

/-! ## V3 forest geometry (`QSAGDPC3`)
The earlier single-tree 128-bit API remains a legacy mathematical model for callers.
This namespace specifies the V3 node width and 64 independent regular-noise trees.
The salted API below models production node inputs, level-XOR wire recovery,
64-tree correlation, and two-repetition tag recomputation. Wire encoding is specified
for typed records; parsing arbitrary byte strings is outside this API.
The legacy sender-alpha-LSB transcript is not a V3 wire field.
-/
namespace DensePcgV3

def wireMagic : List UInt8 := [0x51, 0x53, 0x41, 0x47, 0x44, 0x50, 0x43, 0x33]
def numTrees : Nat := 64
def tapsPerTree : Nat := 3

/-- Level-domain-separated length-doubling 256-bit PRG `lvl → BitVec 256 → (BitVec 256 × BitVec 256)`. -/
abbrev GgmPrg := Nat → BitVec 256 → BitVec 256 × BitVec 256

/-- Full depth-`d` binary GGM tree expansion mapping leaf index `idx : BitVec d` to its 256-bit leaf seed. -/
def ggmExpandFull (prg : GgmPrg) : (d : Nat) → Nat → BitVec 256 → BitVec d → BitVec 256
  | 0, _, seed, _ => seed
  | d + 1, lvl, seed, idx =>
    let (sL, sR) := prg lvl seed
    if idx.getLsbD d then
      ggmExpandFull prg d (lvl + 1) sR (idx.setWidth d)
    else
      ggmExpandFull prg d (lvl + 1) sL (idx.setWidth d)

/-- `d`-element sibling co-path for a punctured GGM tree of depth `d`. -/
@[expose] def GgmCopath : Nat → Type
  | 0 => Unit
  | d + 1 => BitVec 256 × GgmCopath d

/-- Construct the `d`-sibling co-path puncturing leaf `pStar : BitVec d` from root `seed`. -/
def ggmMakeCopath (prg : GgmPrg) : (d : Nat) → Nat → BitVec 256 → BitVec d → GgmCopath d
  | 0, _, _, _ => ()
  | d + 1, lvl, seed, pStar =>
    let (sL, sR) := prg lvl seed
    if pStar.getLsbD d then
      (sL, ggmMakeCopath prg d (lvl + 1) sR (pStar.setWidth d))
    else
      (sR, ggmMakeCopath prg d (lvl + 1) sL (pStar.setWidth d))

/-- Receiver's punctured GGM tree evaluator: evaluates all `u ≠ pStar` from `copath` and outputs `0#256` at `pStar`. -/
def ggmExpandPunctured (prg : GgmPrg) :
    (d : Nat) → Nat → BitVec d → GgmCopath d → BitVec d → BitVec 256
  | 0, _, _, _, _ => 0#256
  | d + 1, lvl, pStar, (sibSeed, rest), idx =>
    if idx.getLsbD d = pStar.getLsbD d then
      ggmExpandPunctured prg d (lvl + 1) (pStar.setWidth d) rest (idx.setWidth d)
    else
      ggmExpandFull prg d (lvl + 1) sibSeed (idx.setWidth d)

/-- **Exact Punctured GGM Tree Recovery (`ggmExpandPunctured_exact`)**:
    For every depth $d$ (including deployed $d \in \{14, 15\}$), root `seed`, and puncture `pStar : BitVec d`:
    1. At `u = pStar`, `ggmExpandPunctured` evaluates to `0#256`.
    2. At every `u ≠ pStar`, `ggmExpandPunctured` recovers the **exact** sender leaf `ggmExpandFull prg d lvl seed u`! -/
theorem ggmExpandPunctured_exact (prg : GgmPrg) :
    ∀ (d lvl : Nat) (seed : BitVec 256) (pStar : BitVec d),
      let copath := ggmMakeCopath prg d lvl seed pStar
      ggmExpandPunctured prg d lvl pStar copath pStar = 0#256 ∧
      (∀ u : BitVec d, u ≠ pStar →
        ggmExpandPunctured prg d lvl pStar copath u = ggmExpandFull prg d lvl seed u)
  | 0, _, _, pStar => by
    dsimp only
    refine ⟨rfl, ?_⟩
    intro u hNe
    exact False.elim (hNe ((BitVec.eq_nil u).trans (BitVec.eq_nil pStar).symm))
  | d + 1, lvl, seed, pStar => by
    dsimp only
    cases hPrg : prg lvl seed with
    | mk sL sR =>
      cases hp : pStar.getLsbD d
      · have hCp : ggmMakeCopath prg (d + 1) lvl seed pStar =
            (sR, ggmMakeCopath prg d (lvl + 1) sL (pStar.setWidth d)) := by
          simp only [ggmMakeCopath, hPrg, hp, Bool.false_eq_true, ↓reduceIte]; rfl
        rw [hCp]
        have ih := ggmExpandPunctured_exact prg d (lvl + 1) sL (pStar.setWidth d)
        dsimp only at ih
        refine ⟨?_, ?_⟩
        · simp only [ggmExpandPunctured, ↓reduceIte, ih.1]
        · intro u huNe
          have hFull : ggmExpandFull prg (d + 1) lvl seed u =
              if u.getLsbD d then ggmExpandFull prg d (lvl + 1) sR (u.setWidth d)
              else ggmExpandFull prg d (lvl + 1) sL (u.setWidth d) := by
            simp only [ggmExpandFull, hPrg]
          rw [hFull]
          dsimp only [ggmExpandPunctured]
          rw [hp]
          cases hu : u.getLsbD d
          · have huLoNe : u.setWidth d ≠ pStar.setWidth d := by
              intro hEqLo
              apply huNe
              have hSu : BitVec.cons (u.getLsbD d) (u.setWidth d) = u := bvCons_split u
              have hSp : BitVec.cons (pStar.getLsbD d) (pStar.setWidth d) = pStar := bvCons_split pStar
              rw [← hSu, ← hSp, hu, hp, hEqLo]
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact ih.2 (u.setWidth d) huLoNe
          · simp only [Bool.true_eq_false, ↓reduceIte]
      · have hCp : ggmMakeCopath prg (d + 1) lvl seed pStar =
            (sL, ggmMakeCopath prg d (lvl + 1) sR (pStar.setWidth d)) := by
          simp only [ggmMakeCopath, hPrg, hp, ↓reduceIte]; rfl
        rw [hCp]
        have ih := ggmExpandPunctured_exact prg d (lvl + 1) sR (pStar.setWidth d)
        dsimp only at ih
        refine ⟨?_, ?_⟩
        · simp only [ggmExpandPunctured, ↓reduceIte, ih.1]
        · intro u huNe
          have hFull : ggmExpandFull prg (d + 1) lvl seed u =
              if u.getLsbD d then ggmExpandFull prg d (lvl + 1) sR (u.setWidth d)
              else ggmExpandFull prg d (lvl + 1) sL (u.setWidth d) := by
            simp only [ggmExpandFull, hPrg]
          rw [hFull]
          dsimp only [ggmExpandPunctured]
          rw [hp]
          cases hu : u.getLsbD d
          · simp only [Bool.false_eq_true, ↓reduceIte]
          · have huLoNe : u.setWidth d ≠ pStar.setWidth d := by
              intro hEqLo
              apply huNe
              have hSu : BitVec.cons (u.getLsbD d) (u.setWidth d) = u := bvCons_split u
              have hSp : BitVec.cons (pStar.getLsbD d) (pStar.setWidth d) = pStar := bvCons_split pStar
              rw [← hSu, ← hSp, hu, hp, hEqLo]
            simp only [↓reduceIte]
            exact ih.2 (u.setWidth d) huLoNe


/-- A structurally decoded peer: exactly 64 punctures, copaths, and corrections;
    no fictitious sender-alpha parity proof fields. -/
structure PeerRecord (depth : Nat) where
  peerId : Nat
  senderMasterSeed : BitVec 256
  puncturedIndices : Fin 64 → BitVec depth
  copaths : Fin 64 → GgmCopath depth
  corrOffsets : Fin 64 → Tower128
  spcotChalCoin : BitVec 256
  spcotMaskMacs : Tower128 × Tower128
  spcotExpectedTag : BitVec 256

/-- V3 structural header after decoding fixed-size byte arrays and tree copaths. -/
structure SeedHeader where
  sessionId : BitVec 256
  numParties : Nat
  myPartyId : Nat
  treeDepth : Nat
  macAlpha : Tower128
  peers : List (PeerRecord treeDepth)

/-- Structural invariants only; authentication additionally requires the recomputed SPCOT tag. -/
def checkHeaderGeometry (hdr : SeedHeader) : Bool :=
  decide (2 ≤ hdr.numParties ∧ hdr.myPartyId < hdr.numParties ∧
    (hdr.treeDepth = 14 ∨ hdr.treeDepth = 15) ∧
    hdr.peers.length + 1 = hdr.numParties ∧
    (hdr.peers.map (·.peerId)).Nodup) && towerLsb hdr.macAlpha &&
  hdr.peers.all (fun peer => decide (peer.peerId < hdr.numParties ∧ peer.peerId ≠ hdr.myPartyId))

theorem checkHeaderGeometry_sound (hdr : SeedHeader) (h : checkHeaderGeometry hdr = true) :
    (hdr.treeDepth = 14 ∨ hdr.treeDepth = 15) ∧ towerLsb hdr.macAlpha = true ∧
    ∀ peer ∈ hdr.peers, peer.peerId < hdr.numParties ∧ peer.peerId ≠ hdr.myPartyId := by
  simp only [checkHeaderGeometry, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1.1.2.2.1, h.1.2, h.2⟩

/-- Each tree has its own domain-separated PRG instance. -/
abbrev ForestPrg := Fin 64 → GgmPrg

def ForestRecovery (prg : ForestPrg) (depth : Nat)
    (roots : Fin 64 → BitVec 256) (punctures : Fin 64 → BitVec depth) : Prop :=
  ∀ tree : Fin 64, ∀ leaf : BitVec depth, leaf ≠ punctures tree →
    ggmExpandPunctured (prg tree) depth 0 (punctures tree)
      (ggmMakeCopath (prg tree) depth 0 (roots tree) (punctures tree)) leaf =
      ggmExpandFull (prg tree) depth 0 (roots tree) leaf

theorem forest_recovery (prg : ForestPrg) (depth : Nat)
    (roots : Fin 64 → BitVec 256) (punctures : Fin 64 → BitVec depth) :
    ForestRecovery prg depth roots punctures := by
  intro tree leaf h
  exact (ggmExpandPunctured_exact (prg tree) depth 0 (roots tree) (punctures tree)).2 leaf h

theorem forest_recovery_at (prg : ForestPrg) (depth : Nat)
    (roots : Fin 64 → BitVec 256) (punctures : Fin 64 → BitVec depth)
    (h : ForestRecovery prg depth roots punctures) (tree : Fin 64) (leaf : BitVec depth)
    (hne : leaf ≠ punctures tree) :
    ggmExpandPunctured (prg tree) depth 0 (punctures tree)
      (ggmMakeCopath (prg tree) depth 0 (roots tree) (punctures tree)) leaf =
      ggmExpandFull (prg tree) depth 0 (roots tree) leaf := h tree leaf hne

theorem witness_forest_recovery :
    ∃ (prg : ForestPrg) (roots : Fin 64 → BitVec 256) (punctures : Fin 64 → BitVec 15)
      (tree : Fin 64) (leaf : BitVec 15),
      ForestRecovery prg 15 roots punctures ∧ leaf ≠ punctures tree :=
  ⟨fun _ _ seed => (seed, seed + 1), fun _ => 1, fun _ => 0, 0, 1,
    forest_recovery _ _ _ _, by decide⟩

/-- Including the punctured point in a recovery claim is false. -/
theorem tooth_punctured_leaf_not_recovered (seed : BitVec 256) (h : seed ≠ 0) :
    ggmExpandPunctured (fun _ s => (s, s)) 0 0 (0#0) () (0#0) ≠
      ggmExpandFull (fun _ s => (s, s)) 0 0 seed (0#0) := by
  exact Ne.symm h

#tooth_pair Qsag.DensePcgV3.forest_recovery_at vs Qsag.DensePcgV3.tooth_punctured_leaf_not_recovered
#verify_inhabited Qsag.DensePcgV3.forest_recovery_at Qsag.DensePcgV3.witness_forest_recovery

namespace Salted

/-- Exact production domain: session, directed party pair, tree, level, and node. -/
structure Domain where
  sessionId : BitVec 256
  senderId : BitVec 16
  receiverId : BitVec 16
  tree : Fin 64

def nodeInput (dom : Domain) (level node : Nat) (seed : BitVec 256) : List UInt8 :=
  "QSAG.DPCG.GGM.N2".toUTF8.toList ++ encodeNatLeBytes 32 dom.sessionId.toNat ++
    encodeNatLeBytes 2 dom.senderId.toNat ++ encodeNatLeBytes 2 dom.receiverId.toNat ++
    encodeNatLeBytes 1 dom.tree.val ++ encodeNatLeBytes 1 level ++
    encodeNatLeBytes 4 node ++ encodeNatLeBytes 32 seed.toNat

abbrev GgmPrg := Nat → Nat → BitVec 256 → BitVec 256 × BitVec 256

/-- SHAKE256's first 64 output bytes are the two child seeds. -/
def nodePrg (dom : Domain) : GgmPrg := fun level node seed =>
  let out := shake256Xof 64 (nodeInput dom level node seed)
  (BitVec.ofNat 256 (decodeNatLeBytes (out.take 32)),
   BitVec.ofNat 256 (decodeNatLeBytes (out.drop 32)))

/-- Full depth-`d` binary GGM tree expansion mapping leaf index `idx : BitVec d` to its 256-bit leaf seed. -/
def ggmExpandFull (prg : GgmPrg) : (d : Nat) → Nat → Nat → BitVec 256 → BitVec d → BitVec 256
  | 0, _, _, seed, _ => seed
  | d + 1, lvl, node, seed, idx =>
    let (sL, sR) := prg lvl node seed
    if idx.getLsbD d then
      ggmExpandFull prg d (lvl + 1) (2 * node + 1) sR (idx.setWidth d)
    else
      ggmExpandFull prg d (lvl + 1) (2 * node) sL (idx.setWidth d)

/-- Construct the `d`-sibling co-path puncturing leaf `pStar : BitVec d` from root `seed`. -/
def ggmMakeCopath (prg : GgmPrg) : (d : Nat) → Nat → Nat → BitVec 256 → BitVec d → GgmCopath d
  | 0, _, _, _, _ => ()
  | d + 1, lvl, node, seed, pStar =>
    let (sL, sR) := prg lvl node seed
    if pStar.getLsbD d then
      (sL, ggmMakeCopath prg d (lvl + 1) (2 * node + 1) sR (pStar.setWidth d))
    else
      (sR, ggmMakeCopath prg d (lvl + 1) (2 * node) sL (pStar.setWidth d))

/-- Receiver's punctured GGM tree evaluator: evaluates all `u ≠ pStar` from `copath` and outputs `0#256` at `pStar`. -/
def ggmExpandPunctured (prg : GgmPrg) :
    (d : Nat) → Nat → Nat → BitVec d → GgmCopath d → BitVec d → BitVec 256
  | 0, _, _, _, _, _ => 0#256
  | d + 1, lvl, node, pStar, (sibSeed, rest), idx =>
    if idx.getLsbD d = pStar.getLsbD d then
      ggmExpandPunctured prg d (lvl + 1) (2 * node + if pStar.getLsbD d then 1 else 0) (pStar.setWidth d) rest (idx.setWidth d)
    else
      ggmExpandFull prg d (lvl + 1) (2 * node + if idx.getLsbD d then 1 else 0) sibSeed (idx.setWidth d)

/-- **Exact Punctured GGM Tree Recovery (`ggmExpandPunctured_exact`)**:
    For every depth $d$ (including deployed $d \in \{14, 15\}$), root `seed`, and puncture `pStar : BitVec d`:
    1. At `u = pStar`, `ggmExpandPunctured` evaluates to `0#256`.
    2. At every `u ≠ pStar`, `ggmExpandPunctured` recovers the **exact** sender leaf `ggmExpandFull prg d lvl node seed u`! -/
theorem ggmExpandPunctured_exact (prg : GgmPrg) :
    ∀ (d lvl node : Nat) (seed : BitVec 256) (pStar : BitVec d),
      let copath := ggmMakeCopath prg d lvl node seed pStar
      ggmExpandPunctured prg d lvl node pStar copath pStar = 0#256 ∧
      (∀ u : BitVec d, u ≠ pStar →
        ggmExpandPunctured prg d lvl node pStar copath u = ggmExpandFull prg d lvl node seed u)
  | 0, _, _, _, pStar => by
    dsimp only
    refine ⟨rfl, ?_⟩
    intro u hNe
    exact False.elim (hNe ((BitVec.eq_nil u).trans (BitVec.eq_nil pStar).symm))
  | d + 1, lvl, node, seed, pStar => by
    dsimp only
    cases hPrg : prg lvl node seed with
    | mk sL sR =>
      cases hp : pStar.getLsbD d
      · have hCp : ggmMakeCopath prg (d + 1) lvl node seed pStar =
            (sR, ggmMakeCopath prg d (lvl + 1) (2 * node) sL (pStar.setWidth d)) := by
          simp only [ ggmMakeCopath, hPrg, hp, Bool.false_eq_true, ↓reduceIte]; rfl
        rw [hCp]
        have ih := ggmExpandPunctured_exact prg d (lvl + 1) (2 * node) sL (pStar.setWidth d)
        dsimp only at ih
        refine ⟨?_, ?_⟩
        · simp only [ ggmExpandPunctured, hp, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, ih.1]
        · intro u huNe
          have hFull : ggmExpandFull prg (d + 1) lvl node seed u =
              if u.getLsbD d then ggmExpandFull prg d (lvl + 1) (2 * node + 1) sR (u.setWidth d)
              else ggmExpandFull prg d (lvl + 1) (2 * node) sL (u.setWidth d) := by
            simp only [ ggmExpandFull, hPrg]
          rw [hFull]
          dsimp only [ ggmExpandPunctured]
          rw [hp]
          cases hu : u.getLsbD d
          · have huLoNe : u.setWidth d ≠ pStar.setWidth d := by
              intro hEqLo
              apply huNe
              have hSu : BitVec.cons (u.getLsbD d) (u.setWidth d) = u := bvCons_split u
              have hSp : BitVec.cons (pStar.getLsbD d) (pStar.setWidth d) = pStar := bvCons_split pStar
              rw [← hSu, ← hSp, hu, hp, hEqLo]
            simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
            exact ih.2 (u.setWidth d) huLoNe
          · simp only [ Bool.true_eq_false, ↓reduceIte]
      · have hCp : ggmMakeCopath prg (d + 1) lvl node seed pStar =
            (sL, ggmMakeCopath prg d (lvl + 1) (2 * node + 1) sR (pStar.setWidth d)) := by
          simp only [ ggmMakeCopath, hPrg, hp, ↓reduceIte]; rfl
        rw [hCp]
        have ih := ggmExpandPunctured_exact prg d (lvl + 1) (2 * node + 1) sR (pStar.setWidth d)
        dsimp only at ih
        refine ⟨?_, ?_⟩
        · simp only [ggmExpandPunctured, hp, ↓reduceIte, ih.1]
        · intro u huNe
          have hFull : ggmExpandFull prg (d + 1) lvl node seed u =
              if u.getLsbD d then ggmExpandFull prg d (lvl + 1) (2 * node + 1) sR (u.setWidth d)
              else ggmExpandFull prg d (lvl + 1) (2 * node) sL (u.setWidth d) := by
            simp only [ ggmExpandFull, hPrg]
          rw [hFull]
          dsimp only [ ggmExpandPunctured]
          rw [hp]
          cases hu : u.getLsbD d
          · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
          · have huLoNe : u.setWidth d ≠ pStar.setWidth d := by
              intro hEqLo
              apply huNe
              have hSu : BitVec.cons (u.getLsbD d) (u.setWidth d) = u := bvCons_split u
              have hSp : BitVec.cons (pStar.getLsbD d) (pStar.setWidth d) = pStar := bvCons_split pStar
              rw [← hSu, ← hSp, hu, hp, hEqLo]
            simp only [ ↓reduceIte]
            exact ih.2 (u.setWidth d) huLoNe


def bvXorSum256 : (d : Nat) → (BitVec d → BitVec 256) → BitVec 256
  | 0, f => f 0#0
  | d + 1, f =>
    bvXorSum256 d (fun u => f (BitVec.cons false u)) ^^^
    bvXorSum256 d (fun u => f (BitVec.cons true u))

private theorem bvXorSum256_congr {d : Nat} {f g : BitVec d → BitVec 256} (h : ∀ u, f u = g u) :
    bvXorSum256 d f = bvXorSum256 d g := by
  induction d with
  | zero => exact h 0#0
  | succ d ih =>
    simp only [bvXorSum256, ih (fun u => h (BitVec.cons false u)),
      ih (fun u => h (BitVec.cons true u))]

private theorem bvXorSum256_zero (d : Nat) : bvXorSum256 d (fun _ => 0#256) = 0#256 := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [bvXorSum256, ih, BitVec.xor_zero]

private theorem bvXor256_four_rearr (a b c e : BitVec 256) :
    (a ^^^ b) ^^^ (c ^^^ e) = (a ^^^ c) ^^^ (b ^^^ e) := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_xor]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> cases e.getLsbD i <;> rfl

private theorem bvXorSum256_xor {d : Nat} (f g : BitVec d → BitVec 256) :
    bvXorSum256 d (fun u => f u ^^^ g u) = bvXorSum256 d f ^^^ bvXorSum256 d g := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [bvXorSum256, ih]
    exact bvXor256_four_rearr _ _ _ _

private theorem bvXorSum256_single : ∀ (d : Nat) (pStar : BitVec d) (val : BitVec 256),
    bvXorSum256 d (fun u => if u = pStar then val else 0#256) = val
  | 0, pStar, val => by
    have hp : pStar = 0#0 := BitVec.eq_nil pStar
    subst hp; rfl
  | d + 1, pStar, val => by
    have hSp : BitVec.cons (pStar.getLsbD d) (pStar.setWidth d) = pStar := bvCons_split pStar
    rw [← hSp]
    simp only [bvXorSum256]
    cases pStar.getLsbD d
    · have hL : bvXorSum256 d (fun u => if BitVec.cons false u = BitVec.cons false (pStar.setWidth d) then val else 0#256) =
          bvXorSum256 d (fun u => if u = pStar.setWidth d then val else 0#256) := by
        apply bvXorSum256_congr; intro u; simp only [bvCons_inj, true_and]
      have hR : bvXorSum256 d (fun u => if BitVec.cons true u = BitVec.cons false (pStar.setWidth d) then val else 0#256) =
          bvXorSum256 d (fun _ => 0#256) := by
        apply bvXorSum256_congr; intro u; simp only [bvCons_inj, Bool.true_eq_false, false_and, ↓reduceIte]
      rw [hL, hR, bvXorSum256_single d, bvXorSum256_zero, BitVec.xor_zero]
    · have hL : bvXorSum256 d (fun u => if BitVec.cons false u = BitVec.cons true (pStar.setWidth d) then val else 0#256) =
          bvXorSum256 d (fun _ => 0#256) := by
        apply bvXorSum256_congr; intro u; simp only [bvCons_inj, Bool.false_eq_true, false_and, ↓reduceIte]
      have hR : bvXorSum256 d (fun u => if BitVec.cons true u = BitVec.cons true (pStar.setWidth d) then val else 0#256) =
          bvXorSum256 d (fun u => if u = pStar.setWidth d then val else 0#256) := by
        apply bvXorSum256_congr; intro u; simp only [bvCons_inj, true_and]
      rw [hL, hR, bvXorSum256_single d, bvXorSum256_zero, BitVec.zero_xor]

/-- A serialized opposite-branch level XOR recovers the missing sibling exactly.
    This is the masked `sibling_msg XOR known_xor` operation in Rust. -/
theorem level_wire_recovery (level : Nat) (full known : BitVec level → BitVec 256)
    (missing : BitVec level) (hz : known missing = 0#256)
    (he : ∀ i, i ≠ missing → known i = full i) :
    bvXorSum256 level full ^^^ bvXorSum256 level known = full missing := by
  have hp : ∀ i, full i ^^^ known i = if i = missing then full missing else 0#256 := by
    intro i
    by_cases h : i = missing
    · subst i; simp only [hz, BitVec.xor_zero, ↓reduceIte]
    · simp only [he i h, h, BitVec.xor_self, ↓reduceIte]
  rw [← bvXorSum256_xor, bvXorSum256_congr hp, bvXorSum256_single]

/-- Only leaves are projected to 128 bits; internal and wire seeds keep all 256 bits. -/
def leaf128 (seed : BitVec 256) : BitVec 128 := seed.setWidth 128

theorem projected_recovery (prg : GgmPrg) (d : Nat)
    (seed : BitVec 256) (p : BitVec d) :
    let full := fun i => leaf128 (ggmExpandFull prg d 0 0 seed i)
    let recv := fun i => leaf128 (ggmExpandPunctured prg d 0 0 p
      (ggmMakeCopath prg d 0 0 seed p) i)
    recv p = 0 ∧ ∀ i, i ≠ p → recv i = full i := by
  obtain ⟨hz, he⟩ := ggmExpandPunctured_exact prg d 0 0 seed p
  refine ⟨?_, ?_⟩
  · dsimp only; rw [hz]; rfl
  · intro i hi; dsimp only; rw [he i hi]

end Salted

/-- Tree contribution after restoring the puncture with the correlated correction. -/
def correctedTreeTerm (d : Nat) (gamma chi : Tower128)
    (recv : BitVec d → BitVec 128) (p : BitVec d) (corr : Tower128) : Tower128 :=
  evalPuncturedTreeSpcotCombo d gamma chi recv p
    (towerAdd 7 (unpackTower 7 (bvXorSum128 d recv)) corr)

def fullTreeTerm (d : Nat) (gamma chi : Tower128)
    (full : BitVec d → BitVec 128) : Tower128 :=
  towerMul 7 gamma (bvTowerSum128 d
    (fun i => towerMul 7 (spcotLeafWeight chi i) (unpackTower 7 (full i))))

theorem correctedTreeTerm_eq (d : Nat)
    (fullLeaves puncLeaves : BitVec d → BitVec 128)
    (alphaSender gamma chi : Tower128) (pStar : BitVec d)
    (hPuncZero : puncLeaves pStar = 0)
    (hPuncEq : ∀ i, i ≠ pStar → puncLeaves i = fullLeaves i) :
    correctedTreeTerm d gamma chi puncLeaves pStar
      (towerAdd 7 (unpackTower 7 (bvXorSum128 d fullLeaves)) alphaSender) =
    towerAdd 7 (fullTreeTerm d gamma chi fullLeaves)
      (towerMul 7 (towerMul 7 gamma (spcotLeafWeight chi pStar)) alphaSender) := by
  let corrOffset := towerAdd 7 (unpackTower 7 (bvXorSum128 d fullLeaves)) alphaSender
  let deltaCorr := towerAdd 7 (unpackTower 7 (bvXorSum128 d puncLeaves)) corrOffset
  let senderCombo := fullTreeTerm d gamma chi fullLeaves
  have hXorId := (spcot_consistency_soundness fullLeaves puncLeaves pStar (packTower 7 alphaSender)
    hPuncZero hPuncEq).1
  have hDeltaEq : deltaCorr = towerAdd 7 (unpackTower 7 (fullLeaves pStar)) alphaSender := by
    apply packTower_injective 7
    dsimp only [deltaCorr, corrOffset]
    rw [packTower_add, packTower_add, packTower_add, packTower_unpackTower,
        packTower_unpackTower, packTower_unpackTower]
    exact hXorId
  have hTermSplit : evalPuncturedTreeSpcotCombo d gamma chi puncLeaves pStar deltaCorr =
      towerAdd 7 senderCombo
        (towerMul 7 (towerMul 7 gamma (spcotLeafWeight chi pStar)) alphaSender) := by
    unfold evalPuncturedTreeSpcotCombo
    have hPoint : ∀ u : BitVec d,
        towerMul 7 (spcotLeafWeight chi u)
          (if u = pStar then deltaCorr else unpackTower 7 (puncLeaves u)) =
        towerAdd 7
          (towerMul 7 (spcotLeafWeight chi u) (unpackTower 7 (fullLeaves u)))
          (if u = pStar then towerMul 7 (spcotLeafWeight chi pStar) alphaSender else towerZero 7) := by
      intro u
      if hu : u = pStar then
        subst hu
        simp only [↓reduceIte, hDeltaEq, towerMul_add_distrib]
      else
        simp only [hu, ↓reduceIte, towerAdd_zero]
        rw [hPuncEq u hu]
    rw [bvTowerSum128_congr hPoint, bvTowerSum128_add, bvTowerSum128_single,
        towerMul_add_distrib, towerMul_assoc]
    rfl
  exact hTermSplit

private theorem sum_mul_right (d : Nat) (f : BitVec d → Tower128) (a : Tower128) :
    bvTowerSum128 d (fun i => towerMul 7 (f i) a) = towerMul 7 (bvTowerSum128 d f) a := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [bvTowerSum128, ih, towerAdd_mul_distrib]

/-- One production repetition aggregates all 64 trees with one VOLE mask.
    Its premise is the checked mask correlation, not an assumption of tag equality. -/
theorem forest_spcot_correlation (d : Nat)
    (full recv : BitVec 6 → BitVec d → BitVec 128)
    (p : BitVec 6 → BitVec d) (gamma : BitVec 6 → Tower128)
    (chi alpha mac key x : Tower128)
    (hz : ∀ j, recv j (p j) = 0)
    (he : ∀ j i, i ≠ p j → recv j i = full j i)
    (hVole : towerAdd 7 mac key = towerMul 7 x alpha) :
    towerAdd 7 mac (bvTowerSum128 6 (fun j => correctedTreeTerm d (gamma j) chi
      (recv j) (p j) (towerAdd 7 (unpackTower 7 (bvXorSum128 d (full j))) alpha))) =
    towerAdd 7 (towerAdd 7 key
      (towerMul 7 (towerAdd 7 x (bvTowerSum128 6
        (fun j => towerMul 7 (gamma j) (spcotLeafWeight chi (p j))))) alpha))
      (bvTowerSum128 6 (fun j => fullTreeTerm d (gamma j) chi (full j))) := by
  rw [bvTowerSum128_congr (fun j => correctedTreeTerm_eq d (full j) (recv j)
    alpha (gamma j) chi (p j) (hz j) (he j)), bvTowerSum128_add, sum_mul_right]
  rw [towerAdd_mul_distrib, ← hVole]
  simp only [towerAdd_assoc, towerAdd_left_comm, towerAdd_cancel]
  rw [towerAdd_comm 7 (bvTowerSum128 6 (fun j => fullTreeTerm d (gamma j) chi (full j)))]

/-- Wire copaths hold opposite-branch level XORs. Reconstruct the known frontier
    exactly as the production masked traversal, retaining the missing prefix. -/
def expandWireLevels (prg : Salted.GgmPrg) :
    (remaining : Nat) → Nat → Nat → Nat → (Nat → BitVec 256) →
      GgmCopath remaining → (Nat → BitVec 256)
  | 0, _, _, missing, known, _ => fun i => if i = missing then 0#256 else known i
  | d + 1, level, puncture, missing, known, (msg, rest) =>
    let bit := puncture / 2 ^ d % 2
    let children := fun i =>
      if i / 2 = missing then 0#256
      else if i % 2 = 0 then (prg level (i / 2) (known (i / 2))).1
      else (prg level (i / 2) (known (i / 2))).2
    let knownXor := Salted.bvXorSum256 level
      (fun i => children (2 * i.toNat + (1 - bit)))
    let sibling := 2 * missing + (1 - bit)
    let next := fun i => if i = sibling then msg ^^^ knownXor else children i
    expandWireLevels prg d (level + 1) puncture (2 * missing + bit) next rest

def wireLeaves (dom : Salted.Domain) (depth : Nat) (p : BitVec depth)
    (cp : GgmCopath depth) : BitVec depth → BitVec 128 := fun i =>
  Salted.leaf128 (expandWireLevels (Salted.nodePrg dom) depth 0 p.toNat 0
    (fun _ => 0#256) cp i.toNat)

/-- Bounded observation of the production rejection-sampling stream. Fuel counts
    squeezed 16-byte candidates; exhaustion is explicit, never a substitute weight. -/
def challengeCandidates (fuel : Nat) (sid : BitVec 256)
    (sender receiver depth rep : Nat) (coin : BitVec 256) : List Tower128 :=
  let input := encodeNatLeBytes 32 sid.toNat ++ encodeNatLeBytes 8 sender ++
    encodeNatLeBytes 8 receiver ++ encodeNatLeBytes 4 depth ++
    encodeNatLeBytes 4 rep ++ encodeNatLeBytes 32 coin.toNat
  let bytes := cshake256Fixed (16 * fuel) spcotChalDomain input
  ((List.range fuel).map (fun i => BitVec.ofNat 128
    (decodeNatLeBytes ((bytes.drop (16 * i)).take 16)))).filterMap
      (fun raw => if raw.toNat > 1 then some (unpackTower 7 raw) else none)

structure Weights where
  gamma : BitVec 6 → Tower128
  chi : Tower128

def deriveWeights (fuel : Nat) (sid : BitVec 256)
    (sender receiver depth rep : Nat) (coin : BitVec 256) : Option Weights :=
  let candidates := challengeCandidates fuel sid sender receiver depth rep coin
  if 65 ≤ candidates.length then
    some ⟨fun j => candidates.getD j.toNat (towerZero 7),
      candidates.getD 64 (towerZero 7)⟩
  else none

def receiverCheckValue (sid : BitVec 256) (receiver : Nat) (depth : Nat)
    (peer : PeerRecord depth) (weights : Weights) (mask : Tower128) : Tower128 :=
  towerAdd 7 mask (bvTowerSum128 6 (fun j =>
    let tree : Fin 64 := ⟨j.toNat, j.isLt⟩
    let dom : Salted.Domain := ⟨sid, BitVec.ofNat 16 peer.peerId,
      BitVec.ofNat 16 receiver, tree⟩
    correctedTreeTerm depth (weights.gamma j) weights.chi
      (wireLeaves dom depth (peer.puncturedIndices tree) (peer.copaths tree))
      (peer.puncturedIndices tree) (peer.corrOffsets tree)))

/-- Both repetition values are recomputed from the 64 wire trees. -/
def receiverCheckValues (fuel : Nat) (hdr : SeedHeader)
    (peer : PeerRecord hdr.treeDepth) : Option (Tower128 × Tower128) := do
  let w0 ← deriveWeights fuel hdr.sessionId peer.peerId hdr.myPartyId hdr.treeDepth 0 peer.spcotChalCoin
  let w1 ← deriveWeights fuel hdr.sessionId peer.peerId hdr.myPartyId hdr.treeDepth 1 peer.spcotChalCoin
  return (receiverCheckValue hdr.sessionId hdr.myPartyId hdr.treeDepth peer w0 peer.spcotMaskMacs.1,
    receiverCheckValue hdr.sessionId hdr.myPartyId hdr.treeDepth peer w1 peer.spcotMaskMacs.2)

def checkWirePeer (fuel : Nat) (hdr : SeedHeader) (peer : PeerRecord hdr.treeDepth) : Bool :=
  match receiverCheckValues fuel hdr peer with
  | none => false
  | some vals => computeSpcotCheckTag (encodeNatLeBytes 32 hdr.sessionId.toNat)
      peer.peerId hdr.myPartyId (encodeNatLeBytes 32 peer.spcotChalCoin.toNat) vals ==
      encodeNatLeBytes 32 peer.spcotExpectedTag.toNat

def checkWireHeader (fuel : Nat) (hdr : SeedHeader) : Bool :=
  checkHeaderGeometry hdr && hdr.peers.all (checkWirePeer fuel hdr)

theorem checkWireHeader_sound (fuel : Nat) (hdr : SeedHeader)
    (h : checkWireHeader fuel hdr = true) :
    checkHeaderGeometry hdr = true ∧ ∀ peer ∈ hdr.peers, checkWirePeer fuel hdr peer = true := by
  simpa only [checkWireHeader, Bool.and_eq_true, List.all_eq_true] using h

theorem checkWirePeer_sound (fuel : Nat) (hdr : SeedHeader) (peer : PeerRecord hdr.treeDepth)
    (h : checkWirePeer fuel hdr peer = true) :
    ∃ vals, receiverCheckValues fuel hdr peer = some vals ∧
      computeSpcotCheckTag (encodeNatLeBytes 32 hdr.sessionId.toNat) peer.peerId hdr.myPartyId
        (encodeNatLeBytes 32 peer.spcotChalCoin.toNat) vals =
          encodeNatLeBytes 32 peer.spcotExpectedTag.toNat := by
  unfold checkWirePeer at h
  cases he : receiverCheckValues fuel hdr peer with
  | none => simp only [he, Bool.false_eq_true] at h
  | some vals => exact ⟨vals, rfl, by simpa only [he, beq_iff_eq] using h⟩

/-- Checking a tag establishes value agreement or returns an explicit hash collision;
    no injectivity of a fixed-size hash is assumed. -/
def checkedValuesBinding (sid coin : List UInt8) (sender receiver : Nat)
    (hs : sender < 2 ^ 64) (hr : receiver < 2 ^ 64)
    (sent received : Tower128 × Tower128)
    (h : computeSpcotCheckTag sid sender receiver coin sent =
      computeSpcotCheckTag sid sender receiver coin received) :
    PSum (sent = received) (HashCollisionWitness (cshake256Fixed 32 spcotTagDomain)) :=
  match computeSpcotCheckTag_binding hs hs hr hr h with
  | .inl eqs => .inl eqs.2.2.2.2
  | .inr collision => .inr collision

/-- Tree-major wire order: punctures, level-XOR copaths, corrections, then two masks. -/
def encodeCopath : {depth : Nat} → GgmCopath depth → List UInt8
  | 0, _ => []
  | _ + 1, (node, rest) => encodeNatLeBytes 32 node.toNat ++ encodeCopath rest

def encodePeer {depth : Nat} (peer : PeerRecord depth) : List UInt8 :=
  let trees := List.finRange 64
  encodeNatLeBytes 2 peer.peerId ++ encodeNatLeBytes 32 peer.senderMasterSeed.toNat ++
    (trees.flatMap (fun j => encodeNatLeBytes 2 (peer.puncturedIndices j).toNat)) ++
    (trees.flatMap (fun j => encodeCopath (peer.copaths j))) ++
    (trees.flatMap (fun j => encodeTower128Le (peer.corrOffsets j))) ++
    encodeNatLeBytes 32 peer.spcotChalCoin.toNat ++
    encodeTower128Le peer.spcotMaskMacs.1 ++ encodeTower128Le peer.spcotMaskMacs.2 ++
    encodeNatLeBytes 32 peer.spcotExpectedTag.toNat

def encodeHeader (hdr : SeedHeader) (multiPartyFix : List (BitVec 64)) : List UInt8 :=
  wireMagic ++ encodeNatLeBytes 32 hdr.sessionId.toNat ++
    encodeNatLeBytes 2 hdr.myPartyId ++ encodeNatLeBytes 2 hdr.numParties ++
    encodeNatLeBytes 1 hdr.treeDepth ++ encodeTower128Le hdr.macAlpha ++
    encodeNatLeBytes 2 hdr.peers.length ++ hdr.peers.flatMap encodePeer ++
    (if multiPartyFix.isEmpty then [0] else
      1 :: multiPartyFix.flatMap (fun word => encodeNatLeBytes 8 word.toNat))

theorem encodeCopath_length : ∀ {depth : Nat} (cp : GgmCopath depth),
    (encodeCopath cp).length = 32 * depth
  | 0, _ => rfl
  | d + 1, (_, rest) => by
    simp only [encodeCopath, List.length_append, encodeNatLeBytes_length, encodeCopath_length]
    omega

theorem encodeHeader_magic (hdr : SeedHeader) (fix : List (BitVec 64)) :
    (encodeHeader hdr fix).take 8 = wireMagic := by
  simp [encodeHeader, wireMagic]


def nextNodes (prg : Salted.GgmPrg) (level : Nat) (full : Nat → BitVec 256)
    (i : Nat) : BitVec 256 :=
  if i % 2 = 0 then (prg level (i / 2) (full (i / 2))).1
  else (prg level (i / 2) (full (i / 2))).2

def recoverLevel (prg : Salted.GgmPrg) (level missing bit : Nat)
    (known : Nat → BitVec 256) (msg : BitVec 256) : Nat → BitVec 256 :=
  let children := fun i => if i / 2 = missing then 0#256 else nextNodes prg level known i
  let knownXor := Salted.bvXorSum256 level (fun i => children (2 * i.toNat + (1 - bit)))
  fun i => if i = 2 * missing + (1 - bit) then msg ^^^ knownXor else children i

theorem recoverLevel_exact (prg : Salted.GgmPrg) (level missing bit : Nat)
    (full known : Nat → BitVec 256) (hm : missing < 2 ^ level) (hb : bit < 2)
    (he : ∀ i, i ≠ missing → known i = full i) :
    let msg := Salted.bvXorSum256 level (fun j => nextNodes prg level full (2 * j.toNat + (1 - bit)))
    let next := recoverLevel prg level missing bit known msg
    next (2 * missing + bit) = 0#256 ∧
      ∀ i, i ≠ 2 * missing + bit → next i = nextNodes prg level full i := by
  intro msg next
  let children := fun i => if i / 2 = missing then 0#256 else nextNodes prg level known i
  let p := BitVec.ofNat level missing
  have hp : p.toNat = missing := by simp only [p, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm]
  have hchildren : ∀ i, i / 2 ≠ missing → children i = nextNodes prg level full i := by
    intro i hi
    simp only [children, hi, ↓reduceIte, nextNodes, he (i / 2) hi]
  have hrec := Salted.level_wire_recovery level
    (fun j => nextNodes prg level full (2 * j.toNat + (1 - bit)))
    (fun j => children (2 * j.toNat + (1 - bit))) p
    (by dsimp only [children]; rw [hp, ite_eq_left (by omega)])
    (by
      intro j hj
      apply hchildren
      have hjn : j.toNat ≠ missing := by
        intro h; apply hj; apply BitVec.eq_of_toNat_eq; exact h.trans hp.symm
      omega)
  rw [hp] at hrec
  refine ⟨?_, ?_⟩
  · change (if 2 * missing + bit = 2 * missing + (1 - bit) then _ else _) = _
    rw [ite_eq_right (by omega)]
    change (if (2 * missing + bit) / 2 = missing then 0#256 else _) = _
    rw [ite_eq_left (by omega)]
  · intro i hi
    change (if i = 2 * missing + (1 - bit) then _ else _) = _
    by_cases hs : i = 2 * missing + (1 - bit)
    · rw [ite_eq_left hs, hs]; exact hrec
    · rw [ite_eq_right hs]
      apply hchildren
      omega



def fullLevels (prg : Salted.GgmPrg) : Nat → Nat → (Nat → BitVec 256) → Nat → BitVec 256
  | 0, _, full => full
  | d + 1, level, full => fullLevels prg d (level + 1) (nextNodes prg level full)

def missingAfter : Nat → Nat → Nat → Nat
  | 0, _, missing => missing
  | d + 1, puncture, missing => missingAfter d puncture (2 * missing + puncture / 2 ^ d % 2)

def wireMessages (prg : Salted.GgmPrg) :
    (d : Nat) → Nat → Nat → (Nat → BitVec 256) → GgmCopath d
  | 0, _, _, _ => ()
  | d + 1, level, puncture, full =>
    (Salted.bvXorSum256 level (fun j => nextNodes prg level full
      (2 * j.toNat + (1 - puncture / 2 ^ d % 2))),
     wireMessages prg d (level + 1) puncture (nextNodes prg level full))

theorem wireLevels_exact (prg : Salted.GgmPrg) :
    ∀ (d level puncture missing : Nat) (full known : Nat → BitVec 256),
      missing < 2 ^ level →
      (∀ i, i ≠ missing → known i = full i) →
      let recv := expandWireLevels prg d level puncture missing known
        (wireMessages prg d level puncture full)
      recv (missingAfter d puncture missing) = 0#256 ∧
        ∀ i, i ≠ missingAfter d puncture missing → recv i = fullLevels prg d level full i
  | 0, level, puncture, missing, full, known, hm, he => by
    dsimp only [expandWireLevels, wireMessages, missingAfter, fullLevels]
    exact ⟨ite_eq_left rfl, fun i hi => (ite_eq_right hi).trans (he i hi)⟩
  | d + 1, level, puncture, missing, full, known, hm, he => by
    have hb : puncture / 2 ^ d % 2 < 2 := Nat.mod_lt _ (by decide)
    have step := recoverLevel_exact prg level missing (puncture / 2 ^ d % 2) full known hm hb he
    have hmNext : 2 * missing + puncture / 2 ^ d % 2 < 2 ^ (level + 1) := by
      rw [Nat.pow_succ]; omega
    exact wireLevels_exact prg d (level + 1) puncture
      (2 * missing + puncture / 2 ^ d % 2) (nextNodes prg level full)
      (recoverLevel prg level missing (puncture / 2 ^ d % 2) known
        (Salted.bvXorSum256 level (fun j => nextNodes prg level full
          (2 * j.toNat + (1 - puncture / 2 ^ d % 2))))) hmNext step.2



theorem mod_mul_two_constructive (p n : Nat) (hn : 0 < n) :
    p % (n * 2) = p % n + n * (p / n % 2) := by
  have hlt : p % (n * 2) / n < 2 := by
    have hr := Nat.mod_lt p (Nat.mul_pos hn (by decide : 0 < 2))
    have hd := Nat.div_add_mod (p % (n * 2)) n
    by_cases h : p % (n * 2) / n < 2
    · exact h
    · have hh : 2 ≤ p % (n * 2) / n := by omega
      have hm := Nat.mul_le_mul_left n hh
      omega
  have hd : p % (n * 2) / n = p / n % 2 := by
    conv => rhs; rw [← Nat.mod_add_div p (n * 2)]
    rw [Nat.mul_assoc, Nat.add_mul_div_left _ _ hn, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hlt]
  rw [Nat.add_comm, ← Nat.div_add_mod (p % (n * 2)) n,
    Nat.mod_mul_right_mod, hd]

theorem missingAfter_eq (d puncture missing : Nat) :
    missingAfter d puncture missing = 2 ^ d * missing + puncture % 2 ^ d := by
  induction d generalizing missing with
  | zero => simp [missingAfter, Nat.mod_one]
  | succ d ih =>
    simp only [missingAfter, ih, Nat.pow_succ, mod_mul_two_constructive puncture (2 ^ d) (Nat.two_pow_pos d), Nat.mul_add, Nat.mul_assoc]
    omega

def rootFrontier (seed : BitVec 256) : Nat → BitVec 256 :=
  fun i => if i = 0 then seed else 0#256

theorem wire_root_recovery (dom : Salted.Domain) (d : Nat)
    (seed : BitVec 256) (p : BitVec d) :
    let full := fun i : BitVec d => Salted.leaf128
      (fullLevels (Salted.nodePrg dom) d 0 (rootFrontier seed) i.toNat)
    let recv := wireLeaves dom d p
      (wireMessages (Salted.nodePrg dom) d 0 p.toNat (rootFrontier seed))
    recv p = 0#128 ∧ ∀ i, i ≠ p → recv i = full i := by
  have h := wireLevels_exact (Salted.nodePrg dom) d 0 p.toNat 0
    (rootFrontier seed) (fun _ => 0#256) (by decide)
    (fun i hi => by simp only [rootFrontier, hi, ↓reduceIte])
  rw [missingAfter_eq, Nat.mul_zero, Nat.zero_add, Nat.mod_eq_of_lt p.isLt] at h
  refine ⟨?_, ?_⟩
  · dsimp only [wireLeaves]; rw [h.1]; rfl
  · intro i hi
    have hn : i.toNat ≠ p.toNat := fun he => hi (BitVec.eq_of_toNat_eq he)
    dsimp only [wireLeaves]; rw [h.2 i.toNat hn]


/-- Production root derivation consumes 2048 consecutive cSHAKE bytes. -/
def deriveRoots (sid : BitVec 256) (sender receiver : Nat) (master : BitVec 256) :
    Fin 64 → BitVec 256 :=
  let bytes := cshake256Fixed 2048 "QSAG.DPCG.ROOTS/v2".toUTF8.toList
    (encodeNatLeBytes 32 sid.toNat ++ encodeNatLeBytes 8 sender ++
      encodeNatLeBytes 8 receiver ++ encodeNatLeBytes 32 master.toNat)
  fun j => BitVec.ofNat 256 (decodeNatLeBytes ((bytes.drop (32 * j.val)).take 32))

def fullWireTree (dom : Salted.Domain) (d : Nat) (root : BitVec 256) : BitVec d → BitVec 128 :=
  fun i => Salted.leaf128 (fullLevels (Salted.nodePrg dom) d 0 (rootFrontier root) i.toNat)

/-- The actual level-XOR wire reconstruction supplies all recovery premises of
    the 64-tree SPCOT correlation theorem. The only cryptographic premise here
    is the one-time VOLE mask equation. -/
theorem wire_forest_spcot_correlation (d : Nat)
    (dom : BitVec 6 → Salted.Domain) (roots : BitVec 6 → BitVec 256)
    (p : BitVec 6 → BitVec d) (gamma : BitVec 6 → Tower128)
    (chi alpha mac key x : Tower128)
    (hVole : towerAdd 7 mac key = towerMul 7 x alpha) :
    let full := fun j => fullWireTree (dom j) d (roots j)
    let recv := fun j => wireLeaves (dom j) d (p j)
      (wireMessages (Salted.nodePrg (dom j)) d 0 (p j).toNat (rootFrontier (roots j)))
    towerAdd 7 mac (bvTowerSum128 6 (fun j => correctedTreeTerm d (gamma j) chi
      (recv j) (p j) (towerAdd 7 (unpackTower 7 (bvXorSum128 d (full j))) alpha))) =
    towerAdd 7 (towerAdd 7 key
      (towerMul 7 (towerAdd 7 x (bvTowerSum128 6
        (fun j => towerMul 7 (gamma j) (spcotLeafWeight chi (p j))))) alpha))
      (bvTowerSum128 6 (fun j => fullTreeTerm d (gamma j) chi (full j))) := by
  apply forest_spcot_correlation
  · intro j; exact (wire_root_recovery (dom j) d (roots j) (p j)).1
  · intro j; exact (wire_root_recovery (dom j) d (roots j) (p j)).2
  · exact hVole

/-- Nontrivial deployed-depth recovery: a distinct, nonpunctured leaf exists. -/
theorem witness_wire_recovery :
    ∃ (dom : Salted.Domain) (root : BitVec 256) (p i : BitVec 15),
      i ≠ p ∧ wireLeaves dom 15 p
        (wireMessages (Salted.nodePrg dom) 15 0 p.toNat (rootFrontier root)) i =
          fullWireTree dom 15 root i := by
  let dom : Salted.Domain := ⟨1, 0, 1, 0⟩
  refine ⟨dom, 1, 0, 1, by decide, ?_⟩
  exact (wire_root_recovery dom 15 1 0).2 1 (by decide)

/-- An honest decoded wire peer's recomputed value is precisely the sender value.
    This connects the wire traversal and correlation theorem to the checker API. -/
theorem receiverCheckValue_honest (sid : BitVec 256) (receiver d : Nat)
    (peer : PeerRecord d) (roots : Fin 64 → BitVec 256) (weights : Weights)
    (alpha mac key x : Tower128)
    (hVole : towerAdd 7 mac key = towerMul 7 x alpha)
    (hcp : ∀ j, peer.copaths j = wireMessages
      (Salted.nodePrg ⟨sid, BitVec.ofNat 16 peer.peerId, BitVec.ofNat 16 receiver, j⟩)
      d 0 (peer.puncturedIndices j).toNat (rootFrontier (roots j)))
    (hcorr : ∀ j, peer.corrOffsets j = towerAdd 7
      (unpackTower 7 (bvXorSum128 d (fullWireTree
        ⟨sid, BitVec.ofNat 16 peer.peerId, BitVec.ofNat 16 receiver, j⟩ d (roots j)))) alpha) :
    let dom := fun j : BitVec 6 =>
      (⟨sid, BitVec.ofNat 16 peer.peerId, BitVec.ofNat 16 receiver, ⟨j.toNat, j.isLt⟩⟩ : Salted.Domain)
    let full := fun j : BitVec 6 => fullWireTree (dom j) d (roots ⟨j.toNat, j.isLt⟩)
    receiverCheckValue sid receiver d peer weights mac =
      towerAdd 7 (towerAdd 7 key (towerMul 7
        (towerAdd 7 x (bvTowerSum128 6 (fun j => towerMul 7 (weights.gamma j)
          (spcotLeafWeight weights.chi (peer.puncturedIndices ⟨j.toNat, j.isLt⟩))))) alpha))
        (bvTowerSum128 6 (fun j => fullTreeTerm d (weights.gamma j) weights.chi (full j))) := by
  dsimp only
  simpa only [receiverCheckValue, hcp, hcorr] using
    wire_forest_spcot_correlation d
      (fun j => ⟨sid, BitVec.ofNat 16 peer.peerId, BitVec.ofNat 16 receiver, ⟨j.toNat, j.isLt⟩⟩)
      (fun j => roots ⟨j.toNat, j.isLt⟩) (fun j => peer.puncturedIndices ⟨j.toNat, j.isLt⟩)
      weights.gamma weights.chi alpha mac key x hVole

end DensePcgV3

/-- Production `24`-repetition OR-Sigma (`RLWE_ZKPOK_REPS = 24`) achieves `2^132 ≥ 2^128` QROM
    Grover challenge-grinding cost and matches `rlweZkpok24Reps` and `inHalfOpenBox`. -/
theorem rlwe_pq24_grover_and_box_bridge {N : Nat} (z : PolyInt N) :
    rlweZkpokPq256Reps = rlweZkpok24Reps ∧
    groverJointChallengeGrindCost rlweZkpokPq256Reps 11 = 2 ^ 132 ∧
    2 ^ 128 ≤ groverJointChallengeGrindCost rlweZkpokPq256Reps 11 ∧
    (polyIntInZkpokBox z = true ↔ ∀ k : Fin N, inHalfOpenBox rlweAcceptHalfWidth (z k) = true) := by
  refine ⟨rfl, rfl, by decide, ?_⟩
  rw [polyIntInZkpokBox_iff]
  unfold inHalfOpenBox rlweAcceptHalfWidth rlweZkpokZBound
  simp only [decide_eq_true_eq]

end Qsag
end

#tooth_pair Qsag.chal11_diff_nonzero_short_and_invertible vs Qsag.tooth_legacy_challenge_pair_has_no_inverse
#verify_inhabited Qsag.joint_fork_has_isometric_relation Qsag.witness_joint_or_fork
