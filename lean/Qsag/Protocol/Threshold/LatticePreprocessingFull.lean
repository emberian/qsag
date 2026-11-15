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

public import Qsag.Math.Constructive
import all Qsag.Math.Constructive
public import Qsag.Math.Goldilocks
import all Qsag.Math.Goldilocks
public import Qsag.Math.BinaryTower
import all Qsag.Math.BinaryTower
public import Qsag.Oracle.UcGames
import all Qsag.Oracle.UcGames
public import Qsag.Exec.SimulationSpine
import all Qsag.Exec.SimulationSpine
import all Qsag.Oracle.Keccak
import all Qsag.Oracle.Poseidon2
public import Qsag.Protocol.Threshold.RlweCyclotomicExtraction
import all Qsag.Protocol.Threshold.RlweCyclotomicExtraction
public import Qsag.Protocol.Threshold.Preprocessing
import all Qsag.Protocol.Threshold.Preprocessing
public import Qsag.Protocol.Threshold.GaussianHvzkAndDualLpn
import all Qsag.Protocol.Threshold.GaussianHvzkAndDualLpn
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

