module
/-
# Qsag.LatticePreprocessingFull — End-to-End Lattice Base-OT, OR-Sigma, Bitwise KOS, Binary LHL & Dense Dual-LPN PCG

Complete `0 Classical.choice` formalization of the active-secure lattice/OT/PCG preprocessing stack:
1. **Negacyclic Ring $R_q = \mathbb{Z}_{12289}[X]/(X^{1024} + 1)$ & Rounding Margin**:
   - Exact prime-field coefficient ring `Zq12289` and polynomial quotient ring `PolyRq N` (`PolyRq1024`)
     with proved `LawfulCommRing` laws, $X^{1024} + 1 = 0$, and primitive root $\psi_{2048}^{1024} \equiv -1 \pmod{12289}$.
   - Exact $\ell_1$-$\ell_\infty$ negacyclic convolution norm bound `‖a * s + e‖_∞ ≤ ‖a‖_1 * ‖s‖_∞ + ‖e‖_∞`,
     proving worst-case ternary RLWE OT decryption noise `≤ 2049 < 3072 = ⌊12289/4⌋` (`0` decryption error),
     2-bit rounding margin `< 1536`, and `#tooth` showing overflowing noise flips the decoded OT bit.
2. **Joint Fiat-Shamir Signed-Monomial OR-Sigma (`13×20 = 260`-bit QROM) + Discrete-Gaussian HVZK + FO Check**:
   - Exact 20-bit signed-monomial challenge map $d(u) = \pm X^{p_0} \pm X^{512 + p_1} \in R_q$
     (`polyIntFromChal20`, `polyRqFromChal20`) with proved injectivity (`polyRqFromChal20_injective`),
     $\|d(u)\|_\infty = 1$, $\|d(u)\|_1 = 2$, and non-zero difference $\|d(u) - d(u')\|_1 \le 4$ for $u \ne u'$.
   - Domain-separated Fiat-Shamir challenge derivation (`hashRlweZkpokJointChallenges`) via `cSHAKE256`
     (`"QSAG.OT.RLWE.ZKPOK/v2"`), active commitment recomputation & non-zero commitment/CRS checks in
     `verifyJointOrSigma` (`rlweZkpokReps = 13`, `13 × 20 = 260`-bit, $\ge 2^{130}$ Grover QROM grinding),
     masked honest prover `buildHonestJointOrTranscript`, constructive `0 Classical.choice` 2-Special
     Soundness Relaxed Knowledge Extractor (`jointOrSigma_extract_witness`), and `#tooth` witnesses for
     tampered `pk0`/`comms`/`chal0 ^^^ chal1`/`|z| ≥ 3070` and independent-challenge grinding.
   - Discrete-Gaussian rejection-sampling statistical HVZK bound (`discrete_gaussian_rejection_hvzk_bound`)
     proving exact conditional witness-independence inside the safe box and exact rational tail-clipping
     distance `tailMass / totalMass` (`13 * tailMass / totalMass` across all `rlweZkpokReps = 13` repetitions), plus `#tooth`.
   - Active Fujisaki-Okamoto (`FO`) re-encryption check `PartyMachine` (`rlweFoReceiverMachine`) proving
     malicious-sender ciphertext canonicality (`fo_reencryption_soundness`) and `#tooth` showing passive
     RLWE decryption without FO leaks secret-key bits via boundary ciphertexts.
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

public import Qsag.Constructive
public import Qsag.Goldilocks
public import Qsag.BinaryTower
public import Qsag.UcGames
public import Qsag.SimulationSpine

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

/-- Classical 7-repetition (`7 × 20 = 140`-bit, `2^70` Grover) count retained only for `#tooth` contrast. -/
def rlweZkpokClassicalReps : Nat := 7

/-- Production post-quantum QROM 13-repetition (`13 × 20 = 260`-bit, `≥ 2^130` Grover) OR-Sigma repetition count
    matching `RLWE_ZKPOK_REPS = 13` in `preprocessing.rs:746`. -/
def rlweZkpokReps : Nat := 13

/-- Alias for the 13-repetition QROM parameter (`rlweZkpokReps = 13`). -/
abbrev rlweZkpokPqReps : Nat := rlweZkpokReps

/-- Strict response infinity-norm bound `RLWE_ZKPOK_Z_BOUND = 3070` (`|z_i| < 3070`, `preprocessing.rs:771`). -/
def rlweZkpokZBound : Nat := 3070

/-- Domain-separation string `"QSAG.OT.RLWE.ZKPOK/v2"` for `cSHAKE256` (`preprocessing.rs:990`). -/
def rlweZkpokDomain : List UInt8 := "QSAG.OT.RLWE.ZKPOK/v2".toUTF8.toList

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

/-! ### 2.1 Fiat-Shamir `cSHAKE256("QSAG.OT.RLWE.ZKPOK/v2")` Transcript Binding & OR-Sigma Verifier -/

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

/-- Exact Fiat-Shamir byte preimage absorbed into `cSHAKE256("QSAG.OT.RLWE.ZKPOK/v2")` in
    `hash_rlwe_zkpok_joint_challenges` (`preprocessing.rs:990-1000`). -/
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
  encodePolyRqLe pk0 ++
  encodePolyRqLe tCrs ++
  encodeJointOrCommsLe comms

/-- Squeeze `R` consecutive 20-bit challenges (`u32::from_le_bytes(out) & 0xFFFFF`,
    `preprocessing.rs:1001-1005`) from a squeezed XOF byte stream. -/
def decodeChal20Stream : (R : Nat) → List UInt8 → (Fin R → BitVec 20)
  | 0, _, i => Fin.elim0 i
  | _ + 1, bs, ⟨0, _⟩ =>
    BitVec.ofNat 20 (decodeNatLeBytes (bs.take 4) % (2 ^ 20))
  | r + 1, bs, ⟨k + 1, hk⟩ =>
    decodeChal20Stream r (bs.drop 4) ⟨k, Nat.lt_of_succ_lt_succ hk⟩

/-- Parametric `R`-repetition Fiat-Shamir challenge derivation parameterized by XOF oracle `ro`
    (used for Forking-Lemma rewinding in `jointOrSigma_extract_witness`). -/
def hashRlweZkpokJointChallengesWithRo (R : Nat) (ro : List UInt8 → List UInt8)
    (crsCoin sessionId : List UInt8)
    (senderId receiverId otIdx : Nat)
    (pk0 tCrs : PolyRq1024)
    (comms : Fin R → (PolyRq1024 × PolyRq1024)) : Fin R → BitVec 20 :=
  decodeChal20Stream R
    (ro (encodeRlweZkpokFsInput R crsCoin sessionId senderId receiverId otIdx pk0 tCrs comms))

/-- Production `cSHAKE256("QSAG.OT.RLWE.ZKPOK/v2")` Fiat-Shamir challenge derivation (`preprocessing.rs:985-1006`). -/
def hashRlweZkpokJointChallengesGen (R : Nat)
    (crsCoin sessionId : List UInt8)
    (senderId receiverId otIdx : Nat)
    (pk0 tCrs : PolyRq1024)
    (comms : Fin R → (PolyRq1024 × PolyRq1024)) : Fin R → BitVec 20 :=
  hashRlweZkpokJointChallengesWithRo R (cshake256Xof (4 * R) rlweZkpokDomain)
    crsCoin sessionId senderId receiverId otIdx pk0 tCrs comms

/-- 7-repetition (`140`-bit classical) Fiat-Shamir challenge derivation. -/
abbrev hashRlweZkpokJointChallenges := hashRlweZkpokJointChallengesGen rlweZkpokReps

/-- 13-repetition (`260`-bit QROM / `≥ 2^130` Grover) Fiat-Shamir challenge derivation (`G0-D`). -/
abbrev hashRlweZkpokJointChallengesPq13 := hashRlweZkpokJointChallengesGen rlweZkpokPqReps

/-- Public statement for 1-out-of-2 Ring-LWE Base-OT OR-Sigma proof of short witness knowledge,
    binding CRS/session coins, directed `(senderId, receiverId, otIdx)` context, CRS `(a, tCrs)`,
    and Receiver first-message key `pk0` (`preprocessing.rs:1117-1127`). -/
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

/-- Parametric `R`-repetition OR-Sigma transcript over `PolyRq1024` with 20-bit signed-monomial
    challenges `chal0, chal1 : Fin R → BitVec 20` matching `RlweReceiverZkPok` (`preprocessing.rs:777-784`). -/
structure JointOrSigmaTranscriptGen (R : Nat) where
  comms : Fin R → (PolyRq1024 × PolyRq1024)
  chal0 : Fin R → BitVec 20
  chal1 : Fin R → BitVec 20
  zs0 : Fin R → PolyInt 1024
  ze0 : Fin R → PolyInt 1024
  zs1 : Fin R → PolyInt 1024
  ze1 : Fin R → PolyInt 1024

/-- 7-repetition (`140`-bit classical) OR-Sigma transcript. -/
abbrev JointOrSigmaTranscript := JointOrSigmaTranscriptGen rlweZkpokReps

/-- 13-repetition (`260`-bit QROM / `≥ 2^130` Grover) OR-Sigma transcript (`G0-D`). -/
abbrev JointOrSigmaTranscriptPq13 := JointOrSigmaTranscriptGen rlweZkpokPqReps

/-- Recompute commitments `(w0, w1)` from responses and 20-bit challenges (`preprocessing.rs:1147-1155`):
    `w0 = a * zs0 + ze0 - d(chal0) * pk0`, `w1 = a * zs1 + ze1 - d(chal1) * (pk0 + tCrs)`. -/
def recomputeJointOrRepComm {R : Nat} (stmt : RlweOrStatement)
    (tr : JointOrSigmaTranscriptGen R) (j : Fin R) : PolyRq1024 × PolyRq1024 :=
  let y0 := stmt.pk0
  let y1 := CommRingOps.add stmt.pk0 stmt.tCrs
  let w0 := CommRingOps.sub
    (CommRingOps.add (CommRingOps.mul stmt.a (polyIntToRq (tr.zs0 j))) (polyIntToRq (tr.ze0 j)))
    (CommRingOps.mul (polyRqFromChal20 (tr.chal0 j)) y0)
  let w1 := CommRingOps.sub
    (CommRingOps.add (CommRingOps.mul stmt.a (polyIntToRq (tr.zs1 j))) (polyIntToRq (tr.ze1 j)))
    (CommRingOps.mul (polyRqFromChal20 (tr.chal1 j)) y1)
  (w0, w1)

/-- Recompute all `R` commitment pairs from `(stmt, tr)`. -/
def recomputeJointOrComms {R : Nat} (stmt : RlweOrStatement)
    (tr : JointOrSigmaTranscriptGen R) : Fin R → (PolyRq1024 × PolyRq1024) :=
  fun j => recomputeJointOrRepComm stmt tr j

/-- Single-repetition response-box (`|z| < 3070`), commitment-equality, non-zero commitment, and
    20-bit XOR challenge check (`preprocessing.rs:1135-1161`). -/
def verifyJointOrRepGen {R : Nat} (stmt : RlweOrStatement) (j : Fin R) (expectedChal : BitVec 20)
    (tr : JointOrSigmaTranscriptGen R) : Bool :=
  let boundsOk :=
    decide (polyIntInfNorm (tr.zs0 j) < rlweZkpokZBound) &&
    decide (polyIntInfNorm (tr.ze0 j) < rlweZkpokZBound) &&
    decide (polyIntInfNorm (tr.zs1 j) < rlweZkpokZBound) &&
    decide (polyIntInfNorm (tr.ze1 j) < rlweZkpokZBound)
  let (w0Exp, w1Exp) := recomputeJointOrRepComm stmt tr j
  let commNonZero := !polyRqEq w0Exp CommRingOps.zero || !polyRqEq w1Exp CommRingOps.zero
  let commMatch := polyRqEq w0Exp (tr.comms j).1 && polyRqEq w1Exp (tr.comms j).2
  let chalOk := decide ((tr.chal0 j ^^^ tr.chal1 j) = expectedChal)
  boundsOk && commNonZero && commMatch && chalOk

/-- Parametric `R`-repetition OR-Sigma verifier under XOF oracle `ro`. -/
def verifyJointOrSigmaWithRoGen (R : Nat) (ro : List UInt8 → List UInt8)
    (stmt : RlweOrStatement) (tr : JointOrSigmaTranscriptGen R) : Bool :=
  checkRlweOrStatementValid stmt &&
  let wRecomp := recomputeJointOrComms stmt tr
  let expected := hashRlweZkpokJointChallengesWithRo R ro
    stmt.crsCoin stmt.sessionId stmt.senderId stmt.receiverId stmt.otIdx stmt.pk0 stmt.tCrs wRecomp
  allFin R (fun j => verifyJointOrRepGen stmt j (expected j) tr)

/-- Production 13-repetition (`260`-bit QROM / `≥ 2^130` Grover) Fiat-Shamir OR-Sigma verifier binding
    statement & recomputed commitments via `cSHAKE256("QSAG.OT.RLWE.ZKPOK/v2")` (`preprocessing.rs:1117-1163`). -/
@[expose] def verifyJointOrSigma (stmt : RlweOrStatement) (tr : JointOrSigmaTranscript) : Bool :=
  verifyJointOrSigmaWithRoGen rlweZkpokReps (cshake256Xof (4 * rlweZkpokReps) rlweZkpokDomain) stmt tr

/-- Alias for the 13-repetition (`260`-bit QROM / `≥ 2^130` Grover) Fiat-Shamir OR-Sigma verifier. -/
def verifyJointOrSigmaPq13 (stmt : RlweOrStatement) (tr : JointOrSigmaTranscriptPq13) : Bool :=
  verifyJointOrSigmaWithRoGen rlweZkpokPqReps (cshake256Xof (4 * rlweZkpokPqReps) rlweZkpokDomain) stmt tr

/-- Constructively locate the first index `j ∈ Fin R` where two distinct challenge vectors differ
    (`0 Classical.choice`, supporting both `R = 7` and `R = 13`). -/
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

private theorem rlweBranch_sub_extract_chal20 (a y w : PolyRq1024)
    (u u' : BitVec 20)
    (zs ze zs' ze' : PolyInt 1024)
    (huNe : u ≠ u')
    (hs : polyIntInfNorm zs < rlweZkpokZBound) (he : polyIntInfNorm ze < rlweZkpokZBound)
    (hs' : polyIntInfNorm zs' < rlweZkpokZBound) (he' : polyIntInfNorm ze' < rlweZkpokZBound)
    (h1 : CommRingOps.sub (CommRingOps.add (CommRingOps.mul a (polyIntToRq zs)) (polyIntToRq ze))
        (CommRingOps.mul (polyRqFromChal20 u) y) = w)
    (h2 : CommRingOps.sub (CommRingOps.add (CommRingOps.mul a (polyIntToRq zs')) (polyIntToRq ze'))
        (CommRingOps.mul (polyRqFromChal20 u') y) = w) :
    let deltaD : PolyInt 1024 := fun k => polyIntFromChal20 u k - polyIntFromChal20 u' k
    let sWit : PolyInt 1024 := fun k => zs k - zs' k
    let eWit : PolyInt 1024 := fun k => ze k - ze' k
    polyIntToRq deltaD ≠ CommRingOps.zero ∧
    polyIntInfNorm deltaD ≤ 2 ∧
    polyIntL1Norm deltaD ≤ 4 ∧
    polyIntInfNorm sWit < 2 * rlweZkpokZBound ∧
    polyIntInfNorm eWit < 2 * rlweZkpokZBound ∧
    CommRingOps.add (CommRingOps.mul a (polyIntToRq sWit)) (polyIntToRq eWit) =
      CommRingOps.mul (polyIntToRq deltaD) y := by
  intro deltaD sWit eWit
  obtain ⟨hDeltaNz, hDeltaInf, hDeltaL1⟩ := chal20_diff_nonzero_and_short huNe
  have hS : polyIntInfNorm sWit < 2 * rlweZkpokZBound := by
    dsimp only [sWit, rlweZkpokZBound] at *
    have := polyIntInfNorm_sub_le zs zs'
    omega
  have hE : polyIntInfNorm eWit < 2 * rlweZkpokZBound := by
    dsimp only [eWit, rlweZkpokZBound] at *
    have := polyIntInfNorm_sub_le ze ze'
    omega
  refine ⟨hDeltaNz, hDeltaInf, hDeltaL1, hS, hE, ?_⟩
  have hEqW := h1.trans h2.symm
  dsimp only [sWit, eWit, deltaD]
  have hSubMul : CommRingOps.mul (polyIntToRq (fun k => polyIntFromChal20 u k - polyIntFromChal20 u' k)) y =
      CommRingOps.sub (CommRingOps.mul (polyRqFromChal20 u) y) (CommRingOps.mul (polyRqFromChal20 u') y) := by
    unfold polyRqFromChal20
    rw [polyIntToRq_sub, LawfulCommRing.mul_comm _ y, LawfulCommRing.mul_sub,
        LawfulCommRing.mul_comm y _, LawfulCommRing.mul_comm y _]
  rw [polyIntToRq_sub, polyIntToRq_sub, LawfulCommRing.mul_sub, hSubMul]
  funext k
  have hk := congrFun hEqW k
  let AZ := CommRingOps.mul a (polyIntToRq zs) k
  let AZ' := CommRingOps.mul a (polyIntToRq zs') k
  let E := polyIntToRq ze k
  let E' := polyIntToRq ze' k
  let DY := CommRingOps.mul (polyRqFromChal20 u) y k
  let DY' := CommRingOps.mul (polyRqFromChal20 u') y k
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
    (`0 Classical.choice`, `0` free fields, supporting both `R = 7` and `R = 13`). -/
structure ExtractedJointOrWitnessGen {R : Nat} (stmt : RlweOrStatement)
    (ro ro' : List UInt8 → List UInt8)
    (tr tr' : JointOrSigmaTranscriptGen R) where
  repIdx : Fin R
  branch : Bool
  uChal : BitVec 20
  uChal' : BitVec 20
  deltaChal : PolyInt 1024
  sWit : PolyInt 1024
  eWit : PolyInt 1024
  branch_chal_diff : uChal ≠ uChal'
  deltaChal_eq : deltaChal = fun k => polyIntFromChal20 uChal k - polyIntFromChal20 uChal' k
  deltaChal_nonzero : polyIntToRq deltaChal ≠ CommRingOps.zero
  deltaChal_inf_le : polyIntInfNorm deltaChal ≤ 2
  deltaChal_l1_le : polyIntL1Norm deltaChal ≤ 4
  s_short : polyIntInfNorm sWit < 2 * rlweZkpokZBound
  e_short : polyIntInfNorm eWit < 2 * rlweZkpokZBound
  relaxed_rlwe_rel :
    CommRingOps.add (CommRingOps.mul stmt.a (polyIntToRq sWit)) (polyIntToRq eWit) =
      CommRingOps.mul (polyIntToRq deltaChal) (stmt.branchPk branch)

abbrev ExtractedJointOrWitness := @ExtractedJointOrWitnessGen rlweZkpokReps
abbrev ExtractedJointOrWitnessPq13 := @ExtractedJointOrWitnessGen rlweZkpokPqReps

/-- **Constructive 2-Special Soundness Relaxed Knowledge Extractor (`jointOrSigma_extract_witness`)**:
    Given two accepting forked OR-Sigma transcripts `(tr, tr')` under random oracles `(ro, ro')` on the
    same statement `stmt` and commitment tuple `tr.comms = tr'.comms` whose forked joint 20-bit challenges
    differ (`ch ≠ ch'`), constructively locates `j ∈ Fin R` and extracts `(branch, uChal, uChal', deltaChal, sWit, eWit)`
    satisfying `a * sWit + eWit = (d(uChal) - d(uChal')) * stmt.branchPk branch` in `PolyRq1024` with
    `polyIntToRq deltaChal ≠ 0`, `‖deltaChal‖_1 ≤ 4`, and `‖sWit‖_∞, ‖eWit‖_∞ < 2 * 3070` (`0 Classical.choice`)! -/
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
    let deltaD : PolyInt 1024 := fun k => polyIntFromChal20 u k - polyIntFromChal20 u' k
    let sWit : PolyInt 1024 := fun k => tr.zs1 j k - tr'.zs1 j k
    let eWit : PolyInt 1024 := fun k => tr.ze1 j k - tr'.ze1 j k
    have hUnp :
        polyIntInfNorm (tr.zs1 j) < rlweZkpokZBound ∧
        polyIntInfNorm (tr.ze1 j) < rlweZkpokZBound ∧
        CommRingOps.sub (CommRingOps.add (CommRingOps.mul stmt.a (polyIntToRq (tr.zs1 j))) (polyIntToRq (tr.ze1 j)))
          (CommRingOps.mul (polyRqFromChal20 (tr.chal1 j)) (CommRingOps.add stmt.pk0 stmt.tCrs)) = (tr.comms j).2 := by
      unfold verifyJointOrRepGen recomputeJointOrRepComm at hRep
      simp only [Bool.and_eq_true, decide_eq_true_eq, polyRqEq_iff] at hRep
      exact ⟨hRep.1.1.1.1.2, hRep.1.1.1.2, hRep.1.2.2⟩
    have hUnp' :
        polyIntInfNorm (tr'.zs1 j) < rlweZkpokZBound ∧
        polyIntInfNorm (tr'.ze1 j) < rlweZkpokZBound ∧
        CommRingOps.sub (CommRingOps.add (CommRingOps.mul stmt.a (polyIntToRq (tr'.zs1 j))) (polyIntToRq (tr'.ze1 j)))
          (CommRingOps.mul (polyRqFromChal20 (tr'.chal1 j)) (CommRingOps.add stmt.pk0 stmt.tCrs)) = (tr.comms j).2 := by
      unfold verifyJointOrRepGen recomputeJointOrRepComm at hRep'
      simp only [Bool.and_eq_true, decide_eq_true_eq, polyRqEq_iff] at hRep'
      have hw1' := hRep'.1.2.2
      rw [← hComms] at hw1'
      exact ⟨hRep'.1.1.1.1.2, hRep'.1.1.1.2, hw1'⟩
    let hPack := rlweBranch_sub_extract_chal20 stmt.a (CommRingOps.add stmt.pk0 stmt.tCrs) (tr.comms j).2
      u u' (tr.zs1 j) (tr.ze1 j) (tr'.zs1 j) (tr'.ze1 j) hc1Ne
      hUnp.1 hUnp.2.1 hUnp'.1 hUnp'.2.1 hUnp.2.2 hUnp'.2.2
    ⟨j, true, u, u', deltaD, sWit, eWit, hc1Ne, rfl,
      hPack.1, hPack.2.1, hPack.2.2.1, hPack.2.2.2.1, hPack.2.2.2.2.1, hPack.2.2.2.2.2⟩
  else
    let u := tr.chal0 j
    let u' := tr'.chal0 j
    let deltaD : PolyInt 1024 := fun k => polyIntFromChal20 u k - polyIntFromChal20 u' k
    let sWit : PolyInt 1024 := fun k => tr.zs0 j k - tr'.zs0 j k
    let eWit : PolyInt 1024 := fun k => tr.ze0 j k - tr'.ze0 j k
    have hUnp :
        polyIntInfNorm (tr.zs0 j) < rlweZkpokZBound ∧
        polyIntInfNorm (tr.ze0 j) < rlweZkpokZBound ∧
        CommRingOps.sub (CommRingOps.add (CommRingOps.mul stmt.a (polyIntToRq (tr.zs0 j))) (polyIntToRq (tr.ze0 j)))
          (CommRingOps.mul (polyRqFromChal20 (tr.chal0 j)) stmt.pk0) = (tr.comms j).1 := by
      unfold verifyJointOrRepGen recomputeJointOrRepComm at hRep
      simp only [Bool.and_eq_true, decide_eq_true_eq, polyRqEq_iff] at hRep
      exact ⟨hRep.1.1.1.1.1.1, hRep.1.1.1.1.1.2, hRep.1.2.1⟩
    have hUnp' :
        polyIntInfNorm (tr'.zs0 j) < rlweZkpokZBound ∧
        polyIntInfNorm (tr'.ze0 j) < rlweZkpokZBound ∧
        CommRingOps.sub (CommRingOps.add (CommRingOps.mul stmt.a (polyIntToRq (tr'.zs0 j))) (polyIntToRq (tr'.ze0 j)))
          (CommRingOps.mul (polyRqFromChal20 (tr'.chal0 j)) stmt.pk0) = (tr.comms j).1 := by
      unfold verifyJointOrRepGen recomputeJointOrRepComm at hRep'
      simp only [Bool.and_eq_true, decide_eq_true_eq, polyRqEq_iff] at hRep'
      have hw0' := hRep'.1.2.1
      rw [← hComms] at hw0'
      exact ⟨hRep'.1.1.1.1.1.1, hRep'.1.1.1.1.1.2, hw0'⟩
    let hPack := rlweBranch_sub_extract_chal20 stmt.a stmt.pk0 (tr.comms j).1
      u u' (tr.zs0 j) (tr.ze0 j) (tr'.zs0 j) (tr'.ze0 j) hc0
      hUnp.1 hUnp.2.1 hUnp'.1 hUnp'.2.1 hUnp.2.2 hUnp'.2.2
    ⟨j, false, u, u', deltaD, sWit, eWit, hc0, rfl,
      hPack.1, hPack.2.1, hPack.2.2.1, hPack.2.2.2.1, hPack.2.2.2.2.1, hPack.2.2.2.2.2⟩

/-- Masked honest OR-Sigma prover parameterized by XOF oracle `ro`, mirroring `RlweReceiverZkPok::prove_ct`
    (`preprocessing.rs:1040-1114`): computes real masked commitment `wReal = a * ysMask + yeMask ≠ 0`,
    simulated fake commitment `wFake = a * zsFake + zeFake - d(uFake) * yFake`, derives joint challenges
    via `hashRlweZkpokJointChallengesWithRo`, sets `uReal = ch ^^^ uFake`, and masks the secret witness
    `(sR, e1)` via `zReal = yMask + d(uReal) ⊛ (sR, e1)`. -/
def buildHonestJointOrTranscriptWithRoGen (R : Nat) (ro : List UInt8 → List UInt8)
    (stmt : RlweOrStatement) (branch : Bool)
    (sR e1 : PolyInt 1024)
    (ysMask yeMask : Fin R → PolyInt 1024)
    (uFake : Fin R → BitVec 20)
    (zsFake zeFake : Fin R → PolyInt 1024) : JointOrSigmaTranscriptGen R :=
  let yFake := if branch then stmt.pk0 else CommRingOps.add stmt.pk0 stmt.tCrs
  let comms : Fin R → (PolyRq1024 × PolyRq1024) := fun j =>
    let wReal := CommRingOps.add
      (CommRingOps.mul stmt.a (polyIntToRq (ysMask j)))
      (polyIntToRq (yeMask j))
    let wFake := CommRingOps.sub
      (CommRingOps.add (CommRingOps.mul stmt.a (polyIntToRq (zsFake j))) (polyIntToRq (zeFake j)))
      (CommRingOps.mul (polyRqFromChal20 (uFake j)) yFake)
    if branch then (wFake, wReal) else (wReal, wFake)
  let ch := hashRlweZkpokJointChallengesWithRo R ro
    stmt.crsCoin stmt.sessionId stmt.senderId stmt.receiverId stmt.otIdx stmt.pk0 stmt.tCrs comms
  let uReal : Fin R → BitVec 20 := fun j => ch j ^^^ uFake j
  let zsReal : Fin R → PolyInt 1024 := fun j k =>
    polyIntMul (polyIntFromChal20 (uReal j)) sR k + ysMask j k
  let zeReal : Fin R → PolyInt 1024 := fun j k =>
    polyIntMul (polyIntFromChal20 (uReal j)) e1 k + yeMask j k
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

/-- Production masked honest OR-Sigma prover using `cSHAKE256("QSAG.OT.RLWE.ZKPOK/v2")`. -/
def buildHonestJointOrTranscriptGen (R : Nat)
    (stmt : RlweOrStatement) (branch : Bool)
    (sR e1 : PolyInt 1024)
    (ysMask yeMask : Fin R → PolyInt 1024)
    (uFake : Fin R → BitVec 20)
    (zsFake zeFake : Fin R → PolyInt 1024) : JointOrSigmaTranscriptGen R :=
  buildHonestJointOrTranscriptWithRoGen R (cshake256Xof (4 * R) rlweZkpokDomain)
    stmt branch sR e1 ysMask yeMask uFake zsFake zeFake

abbrev buildHonestJointOrTranscript := buildHonestJointOrTranscriptGen rlweZkpokReps
abbrev buildHonestJointOrTranscriptPq13 := buildHonestJointOrTranscriptGen rlweZkpokPqReps

private theorem real_branch_comm_cancel (a yReal : PolyRq1024)
    (sR e1 ys ye : PolyInt 1024) (u : BitVec 20)
    (hRel : CommRingOps.add (CommRingOps.mul a (polyIntToRq sR)) (polyIntToRq e1) = yReal) :
    CommRingOps.sub
      (CommRingOps.add
        (CommRingOps.mul a (polyIntToRq (fun k => polyIntMul (polyIntFromChal20 u) sR k + ys k)))
        (polyIntToRq (fun k => polyIntMul (polyIntFromChal20 u) e1 k + ye k)))
      (CommRingOps.mul (polyRqFromChal20 u) yReal) =
    CommRingOps.add (CommRingOps.mul a (polyIntToRq ys)) (polyIntToRq ye) := by
  rw [polyIntToRq_add, polyIntToRq_add, polyIntToRq_mul, polyIntToRq_mul]
  change CommRingOps.sub
      (CommRingOps.add
        (CommRingOps.mul a (CommRingOps.add (CommRingOps.mul (polyRqFromChal20 u) (polyIntToRq sR)) (polyIntToRq ys)))
        (CommRingOps.add (CommRingOps.mul (polyRqFromChal20 u) (polyIntToRq e1)) (polyIntToRq ye)))
      (CommRingOps.mul (polyRqFromChal20 u) yReal) =
    CommRingOps.add (CommRingOps.mul a (polyIntToRq ys)) (polyIntToRq ye)
  have hMulShift :
      CommRingOps.add
        (CommRingOps.mul a (CommRingOps.mul (polyRqFromChal20 u) (polyIntToRq sR)))
        (CommRingOps.mul (polyRqFromChal20 u) (polyIntToRq e1)) =
      CommRingOps.mul (polyRqFromChal20 u) yReal := by
    rw [← hRel, LawfulCommRing.left_distrib,
        ← LawfulCommRing.mul_assoc a (polyRqFromChal20 u) (polyIntToRq sR),
        LawfulCommRing.mul_comm a (polyRqFromChal20 u),
        LawfulCommRing.mul_assoc (polyRqFromChal20 u) a (polyIntToRq sR)]
  rw [LawfulCommRing.left_distrib]
  funext k
  have hkShift := congrFun hMulShift k
  let D_AS := CommRingOps.mul a (CommRingOps.mul (polyRqFromChal20 u) (polyIntToRq sR)) k
  let A_YS := CommRingOps.mul a (polyIntToRq ys) k
  let D_E := CommRingOps.mul (polyRqFromChal20 u) (polyIntToRq e1) k
  let YE := polyIntToRq ye k
  let DY := CommRingOps.mul (polyRqFromChal20 u) yReal k
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

private theorem bitvec20_xor_cancel_right (c f : BitVec 20) : (c ^^^ f) ^^^ f = c := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_xor]
  cases c.getLsbD i <;> cases f.getLsbD i <;> rfl

private theorem bitvec20_xor_cancel_left (f c : BitVec 20) : f ^^^ (c ^^^ f) = c := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_xor]
  cases f.getLsbD i <;> cases c.getLsbD i <;> rfl

/-- **Completeness of Masked OR-Sigma Prover (`honestJointOrTranscriptWithRo_accepts`)**:
    Whenever `(sR, e1)` is a short RLWE witness on `stmt.branchPk branch` and masks `(ysMask, yeMask)`
    lie inside the safe box (`2 * ‖sR‖_∞ + ‖ysMask‖_∞ < 3070`, `2 * ‖e1‖_∞ + ‖yeMask‖_∞ < 3070`)
    with non-zero real commitments `a * ysMask + yeMask ≠ 0`, `verifyJointOrSigmaWithRoGen` accepts! -/
theorem honestJointOrTranscriptWithRo_accepts {R : Nat} (ro : List UInt8 → List UInt8)
    (stmt : RlweOrStatement) (branch : Bool)
    (sR e1 : PolyInt 1024)
    (ysMask yeMask : Fin R → PolyInt 1024)
    (uFake : Fin R → BitVec 20)
    (zsFake zeFake : Fin R → PolyInt 1024)
    (hStmt : checkRlweOrStatementValid stmt = true)
    (hRel : CommRingOps.add (CommRingOps.mul stmt.a (polyIntToRq sR)) (polyIntToRq e1) =
      stmt.branchPk branch)
    (hSafeS : ∀ j : Fin R, 2 * polyIntInfNorm sR + polyIntInfNorm (ysMask j) < rlweZkpokZBound)
    (hSafeE : ∀ j : Fin R, 2 * polyIntInfNorm e1 + polyIntInfNorm (yeMask j) < rlweZkpokZBound)
    (hFakeS : ∀ j : Fin R, polyIntInfNorm (zsFake j) < rlweZkpokZBound)
    (hFakeE : ∀ j : Fin R, polyIntInfNorm (zeFake j) < rlweZkpokZBound)
    (hwRealNz : ∀ j : Fin R,
      CommRingOps.add (CommRingOps.mul stmt.a (polyIntToRq (ysMask j))) (polyIntToRq (yeMask j)) ≠
        CommRingOps.zero) :
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
  have hRealSBound : ∀ u : BitVec 20,
      polyIntInfNorm (fun k => polyIntMul (polyIntFromChal20 u) sR k + ysMask j k) < rlweZkpokZBound := by
    intro u
    have hConv := negacyclic_infNorm_mul_add_le (polyIntFromChal20 u) sR (ysMask j)
    rw [polyIntFromChal20_l1Norm_eq_two] at hConv
    have hSafe := hSafeS j
    omega
  have hRealEBound : ∀ u : BitVec 20,
      polyIntInfNorm (fun k => polyIntMul (polyIntFromChal20 u) e1 k + yeMask j k) < rlweZkpokZBound := by
    intro u
    have hConv := negacyclic_infNorm_mul_add_le (polyIntFromChal20 u) e1 (yeMask j)
    rw [polyIntFromChal20_l1Norm_eq_two] at hConv
    have hSafe := hSafeE j
    omega
  have hwNzFalse : polyRqEq
      (CommRingOps.add (CommRingOps.mul stmt.a (polyIntToRq (ysMask j))) (polyIntToRq (yeMask j)))
      CommRingOps.zero = false :=
    (polyRqEq_eq_false_iff _ _).mpr (hwRealNz j)
  have hBounds :
      (decide (polyIntInfNorm (tr.zs0 j) < rlweZkpokZBound) &&
       decide (polyIntInfNorm (tr.ze0 j) < rlweZkpokZBound) &&
       decide (polyIntInfNorm (tr.zs1 j) < rlweZkpokZBound) &&
       decide (polyIntInfNorm (tr.ze1 j) < rlweZkpokZBound)) = true := by
    dsimp only [tr, buildHonestJointOrTranscriptWithRoGen]
    cases branch
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨hRealSBound _, hRealEBound _⟩, hFakeS j⟩, hFakeE j⟩
    · simp only [↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨hFakeS j, hFakeE j⟩, hRealSBound _⟩, hRealEBound _⟩
  have hNz : (!polyRqEq (tr.comms j).1 CommRingOps.zero || !polyRqEq (tr.comms j).2 CommRingOps.zero) = true := by
    dsimp only [tr, buildHonestJointOrTranscriptWithRoGen]
    cases branch
    · simp only [Bool.false_eq_true, ↓reduceIte, hwNzFalse, Bool.not_false, Bool.true_or]
    · simp only [↓reduceIte, hwNzFalse, Bool.not_false, Bool.or_true]
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
  rw [hBounds, hNz, hMatch, hChal]
  rfl

/-- **Production Completeness of `verifyJointOrSigma` (`honestJointOrTranscript_accepts`)**:
    Honest masked transcripts accept under production `cSHAKE256("QSAG.OT.RLWE.ZKPOK/v2")` at both
    `R = 7` (`verifyJointOrSigma`) and `R = 13` (`verifyJointOrSigmaPq13`). -/
theorem honestJointOrTranscript_accepts (stmt : RlweOrStatement) (branch : Bool)
    (sR e1 : PolyInt 1024)
    (ysMask yeMask : Fin rlweZkpokReps → PolyInt 1024)
    (uFake : Fin rlweZkpokReps → BitVec 20)
    (zsFake zeFake : Fin rlweZkpokReps → PolyInt 1024)
    (hStmt : checkRlweOrStatementValid stmt = true)
    (hRel : CommRingOps.add (CommRingOps.mul stmt.a (polyIntToRq sR)) (polyIntToRq e1) =
      stmt.branchPk branch)
    (hSafeS : ∀ j, 2 * polyIntInfNorm sR + polyIntInfNorm (ysMask j) < rlweZkpokZBound)
    (hSafeE : ∀ j, 2 * polyIntInfNorm e1 + polyIntInfNorm (yeMask j) < rlweZkpokZBound)
    (hFakeS : ∀ j, polyIntInfNorm (zsFake j) < rlweZkpokZBound)
    (hFakeE : ∀ j, polyIntInfNorm (zeFake j) < rlweZkpokZBound)
    (hwRealNz : ∀ j,
      CommRingOps.add (CommRingOps.mul stmt.a (polyIntToRq (ysMask j))) (polyIntToRq (yeMask j)) ≠
        CommRingOps.zero) :
    verifyJointOrSigma stmt
      (buildHonestJointOrTranscript stmt branch sR e1 ysMask yeMask uFake zsFake zeFake) = true :=
  honestJointOrTranscriptWithRo_accepts (cshake256Xof (4 * rlweZkpokReps) rlweZkpokDomain)
    stmt branch sR e1 ysMask yeMask uFake zsFake zeFake hStmt hRel hSafeS hSafeE hFakeS hFakeE hwRealNz

theorem honestJointOrTranscriptPq13_accepts (stmt : RlweOrStatement) (branch : Bool)
    (sR e1 : PolyInt 1024)
    (ysMask yeMask : Fin rlweZkpokPqReps → PolyInt 1024)
    (uFake : Fin rlweZkpokPqReps → BitVec 20)
    (zsFake zeFake : Fin rlweZkpokPqReps → PolyInt 1024)
    (hStmt : checkRlweOrStatementValid stmt = true)
    (hRel : CommRingOps.add (CommRingOps.mul stmt.a (polyIntToRq sR)) (polyIntToRq e1) =
      stmt.branchPk branch)
    (hSafeS : ∀ j, 2 * polyIntInfNorm sR + polyIntInfNorm (ysMask j) < rlweZkpokZBound)
    (hSafeE : ∀ j, 2 * polyIntInfNorm e1 + polyIntInfNorm (yeMask j) < rlweZkpokZBound)
    (hFakeS : ∀ j, polyIntInfNorm (zsFake j) < rlweZkpokZBound)
    (hFakeE : ∀ j, polyIntInfNorm (zeFake j) < rlweZkpokZBound)
    (hwRealNz : ∀ j,
      CommRingOps.add (CommRingOps.mul stmt.a (polyIntToRq (ysMask j))) (polyIntToRq (yeMask j)) ≠
        CommRingOps.zero) :
    verifyJointOrSigmaPq13 stmt
      (buildHonestJointOrTranscriptPq13 stmt branch sR e1 ysMask yeMask uFake zsFake zeFake) = true :=
  honestJointOrTranscriptWithRo_accepts (cshake256Xof (4 * rlweZkpokPqReps) rlweZkpokDomain)
    stmt branch sR e1 ysMask yeMask uFake zsFake zeFake hStmt hRel hSafeS hSafeE hFakeS hFakeE hwRealNz

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
    (fun _ => 0#20)
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
  have hwNz : ∀ _ : Fin rlweZkpokReps,
      CommRingOps.add (CommRingOps.mul sampleRlweOrStatement.a (polyIntToRq sampleUnitPolyInt))
        (polyIntToRq sampleZeroPolyInt) ≠ CommRingOps.zero := by
    intro _
    rw [sampleUnitPolyInt_toRq, sampleZeroPolyInt_toRq]
    unfold sampleRlweOrStatement; dsimp only
    rw [LawfulCommRing.mul_one, LawfulCommRing.add_zero]
    exact polyRq1024_one_ne_zero
  refine ⟨honestJointOrTranscript_accepts sampleRlweOrStatement false
      sampleUnitPolyInt sampleZeroPolyInt
      (fun _ => sampleUnitPolyInt) (fun _ => sampleZeroPolyInt)
      (fun _ => 0#20) (fun _ => sampleZeroPolyInt) (fun _ => sampleZeroPolyInt)
      sampleRlweOrStatement_valid hRel hSafeS hSafeE hFake hFake hwNz, ?_⟩
  let ro0 : List UInt8 → List UInt8 := fun _ => encodeNatLeBytes 4 0 ++ List.replicate 48 0
  let ro1 : List UInt8 → List UInt8 := fun _ => encodeNatLeBytes 4 1 ++ List.replicate 48 0
  let tr0 := buildHonestJointOrTranscriptWithRoGen rlweZkpokReps ro0
    sampleRlweOrStatement false sampleUnitPolyInt sampleZeroPolyInt
    (fun _ => sampleUnitPolyInt) (fun _ => sampleZeroPolyInt)
    (fun _ => 0#20) (fun _ => sampleZeroPolyInt) (fun _ => sampleZeroPolyInt)
  let tr1 := buildHonestJointOrTranscriptWithRoGen rlweZkpokReps ro1
    sampleRlweOrStatement false sampleUnitPolyInt sampleZeroPolyInt
    (fun _ => sampleUnitPolyInt) (fun _ => sampleZeroPolyInt)
    (fun _ => 0#20) (fun _ => sampleZeroPolyInt) (fun _ => sampleZeroPolyInt)
  have hAcc0 := honestJointOrTranscriptWithRo_accepts ro0 sampleRlweOrStatement false
    sampleUnitPolyInt sampleZeroPolyInt
    (fun _ => sampleUnitPolyInt) (fun _ => sampleZeroPolyInt)
    (fun _ => 0#20) (fun _ => sampleZeroPolyInt) (fun _ => sampleZeroPolyInt)
    sampleRlweOrStatement_valid hRel hSafeS hSafeE hFake hFake hwNz
  have hAcc1 := honestJointOrTranscriptWithRo_accepts ro1 sampleRlweOrStatement false
    sampleUnitPolyInt sampleZeroPolyInt
    (fun _ => sampleUnitPolyInt) (fun _ => sampleZeroPolyInt)
    (fun _ => 0#20) (fun _ => sampleZeroPolyInt) (fun _ => sampleZeroPolyInt)
    sampleRlweOrStatement_valid hRel hSafeS hSafeE hFake hFake hwNz
  have hNe : hashRlweZkpokJointChallengesWithRo rlweZkpokReps ro0 sampleRlweOrStatement.crsCoin
        sampleRlweOrStatement.sessionId sampleRlweOrStatement.senderId sampleRlweOrStatement.receiverId
        sampleRlweOrStatement.otIdx sampleRlweOrStatement.pk0 sampleRlweOrStatement.tCrs tr0.comms ≠
      hashRlweZkpokJointChallengesWithRo rlweZkpokReps ro1 sampleRlweOrStatement.crsCoin
        sampleRlweOrStatement.sessionId sampleRlweOrStatement.senderId sampleRlweOrStatement.receiverId
        sampleRlweOrStatement.otIdx sampleRlweOrStatement.pk0 sampleRlweOrStatement.tCrs tr1.comms := by
    intro hEq
    have h0 := congrFun hEq ⟨0, by decide⟩
    unfold hashRlweZkpokJointChallengesWithRo decodeChal20Stream rlweZkpokReps at h0
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
    `cSHAKE256("QSAG.OT.RLWE.ZKPOK/v2")`:
    1. **Tampered `pk0`** (`pk0' = pk0 + 1`): rejected (`verifyJointOrSigma = false`).
    2. **Tampered `comms`** (corrupting `(comms 0).1` by `+ 1`, or setting cosplay `comms := fun _ => (0, 0)`):
       rejected (`verifyJointOrSigma = false`).
    3. **Tampered `chal0 ^^^ chal1`** (flipping `chal0 0 ^^^ 1#20` without re-proving):
       rejected (`verifyJointOrSigma = false`).
    4. **Out-of-box response** (`|z| = 3070 ≥ rlweZkpokZBound`): rejected (`verifyJointOrSigma = false`). -/
theorem tooth_verifyJointOrSigma_rejects_tampering :
    let stmt := sampleRlweOrStatement
    let tr := sampleHonestJointOrTranscript
    let stmtBadPk0 := { stmt with pk0 := CommRingOps.add stmt.pk0 CommRingOps.one }
    let trBadComms := { tr with comms := fun j =>
      if j.val = 0 then (CommRingOps.add (tr.comms j).1 CommRingOps.one, (tr.comms j).2) else tr.comms j }
    let trZeroComms := { tr with comms := fun _ => (CommRingOps.zero, CommRingOps.zero) }
    let trBadChal := { tr with chal0 := fun j => if j.val = 0 then tr.chal0 j ^^^ 1#20 else tr.chal0 j }
    let trBadBound := { tr with zs0 := fun j => if j.val = 0 then (fun _ => 3070) else tr.zs0 j }
    verifyJointOrSigma stmt tr = true ∧
    verifyJointOrSigma stmtBadPk0 tr = false ∧
    verifyJointOrSigma stmt trBadComms = false ∧
    verifyJointOrSigma stmt trZeroComms = false ∧
    verifyJointOrSigma stmt trBadChal = false ∧
    verifyJointOrSigma stmt trBadBound = false := by
  intro stmt tr stmtBadPk0 trBadComms trZeroComms trBadChal trBadBound
  have hAcc : verifyJointOrSigma stmt tr = true := inhabited_jointOrSigma_and_extractor.1
  have hRep0 : (recomputeJointOrRepComm stmt tr ⟨0, by decide⟩).1 = (tr.comms ⟨0, by decide⟩).1 := by
    unfold verifyJointOrSigma verifyJointOrSigmaWithRoGen at hAcc
    simp only [Bool.and_eq_true] at hAcc
    have h0 := (allFin_eq_true_iff _).mp hAcc.2 ⟨0, by decide⟩
    unfold verifyJointOrRepGen at h0
    simp only [Bool.and_eq_true, polyRqEq_iff] at h0
    exact h0.1.2.1
  -- 1. Tampered `pk0`: `w0Exp` shifts by `-d(chal0 0) * 1`, which is non-zero by `polyRqFromChal20_ne_zero`!
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
        have hChalNz := polyRqFromChal20_ne_zero (tr.chal0 ⟨0, by decide⟩)
        apply hChalNz
        rw [LawfulCommRing.left_distrib, LawfulCommRing.mul_one] at hEq
        funext k
        have hk := congrFun hEq k
        let X := CommRingOps.add (CommRingOps.mul stmt.a (polyIntToRq (tr.zs0 ⟨0, by decide⟩)))
          (polyIntToRq (tr.ze0 ⟨0, by decide⟩)) k
        let D0 := CommRingOps.mul (polyRqFromChal20 (tr.chal0 ⟨0, by decide⟩)) stmt.pk0 k
        let D1 := polyRqFromChal20 (tr.chal0 ⟨0, by decide⟩) k
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
  -- 3. Cosplay `(0, 0)` commitments: if `w0Exp = 0 ∧ w1Exp = 0`, `commNonZero = false`; else `commMatch = false`!
  have hZeroComms : verifyJointOrSigma stmt trZeroComms = false := by
    unfold verifyJointOrSigma verifyJointOrSigmaWithRoGen
    cases hc : checkRlweOrStatementValid stmt
    · rfl
    · simp only [Bool.true_and]
      apply allFin_eq_false_of_false ⟨0, by decide⟩
      unfold verifyJointOrRepGen
      dsimp only [trZeroComms]
      cases hw0 : polyRqEq (recomputeJointOrRepComm stmt trZeroComms ⟨0, by decide⟩).1 CommRingOps.zero <;>
        cases hw1 : polyRqEq (recomputeJointOrRepComm stmt trZeroComms ⟨0, by decide⟩).2 CommRingOps.zero <;>
        simp
  -- 4. Tampered `chal0 ^^^ chal1` (`chal0 0 ^^^ 1#20`): `w0Exp` shifts by `-((d(u') - d(u)) * pk0) ≠ 0`!
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
        have hBit := congrArg (fun x : BitVec 20 => x.getLsbD 0) hEq
        simp only [BitVec.getLsbD_xor] at hBit
        have hb1 : (1#20).getLsbD 0 = true := by decide
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
        obtain ⟨hDiffNz, _, _⟩ := chal20_diff_nonzero_and_short hU0Ne
        apply hDiffNz
        rw [polyIntToRq_sub]
        funext k
        have hk := congrFun hEq k
        let X := CommRingOps.add
          (CommRingOps.mul CommRingOps.one (polyIntToRq (tr.zs0 ⟨0, by decide⟩)))
          (polyIntToRq (tr.ze0 ⟨0, by decide⟩)) k
        let D' := polyRqFromChal20 (tr.chal0 ⟨0, by decide⟩ ^^^ 1#20) k
        let D := polyRqFromChal20 (tr.chal0 ⟨0, by decide⟩) k
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
  -- 5. Out-of-bounds response (`|z| = 3070 ≥ rlweZkpokZBound`): `boundsOk = false`!
  have hBadBound : verifyJointOrSigma stmt trBadBound = false := by
    unfold verifyJointOrSigma verifyJointOrSigmaWithRoGen
    cases hc : checkRlweOrStatementValid stmt
    · rfl
    · simp only [Bool.true_and]
      apply allFin_eq_false_of_false ⟨0, by decide⟩
      unfold verifyJointOrRepGen
      have hNotLt : ¬(polyIntInfNorm (trBadBound.zs0 ⟨0, by decide⟩) < rlweZkpokZBound) := by
        have hGe : 3070 ≤ polyIntInfNorm (trBadBound.zs0 ⟨0, by decide⟩) := by
          have h0 := coeff_natAbs_le_infNorm (trBadBound.zs0 ⟨0, by decide⟩) ⟨0, by decide⟩
          dsimp only [trBadBound] at h0
          simp only [↓reduceIte] at h0
          exact h0
        unfold rlweZkpokZBound
        omega
      have hDecFalse : decide (polyIntInfNorm (trBadBound.zs0 ⟨0, by decide⟩) < rlweZkpokZBound) = false :=
        decide_eq_false hNotLt
      dsimp only
      rw [hDecFalse]
      simp
  exact ⟨hAcc, hBadPk0, hBadComms, hZeroComms, hBadChal, hBadBound⟩

/-! ### 2.1b `#tooth` Independent vs. Joint Fiat-Shamir Challenge Grinding (`P0-11` & `G0-D` QROM) -/

/-- Grinding query cost under joint 7-commitment hashing `H(pk0, tCrs, C_0..C_6)` (`2^(7*m)`). -/
def jointChallengeGrindCost (m : Nat) : Nat := 2 ^ (7 * m)

/-- Grinding query cost when each repetition `j ∈ Fin 7` hashes `H(pk0, tCrs, j, C_j)` independently (`7 * 2^m`). -/
def indepChallengeGrindCost (m : Nat) : Nat := 7 * (2 ^ m)

/-- Bit-weighted independent grinding cost `k * 2^(k/7)` (`(7 * m) * 2^m`). -/
def bitWeightedIndepGrindCost (m : Nat) : Nat := (7 * m) * (2 ^ m)

/-- Post-quantum Grover QROM square-root grinding query lower bound `2^((R * m) / 2)` (`G0-D`). -/
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

/-- **`#tooth` Independent Per-Repetition Fiat-Shamir Collapses Grinding Cost (`tooth_independent_challenges_drop_grinding_cost`)**:
    For every per-repetition challenge width $m \ge 1$:
    1. Independent per-slot grinding finds all 7 target challenges in `7 * 2^m < 2^(7 * m)` evaluations
       (dropping classical work at `m = 20` from `2^140` below `2^23`).
    2. Under quantum QROM adversaries, `rlweZkpokClassicalReps = 7` (`140` bits) only provides `2^70 < 2^128`
       Grover square-root grinding resistance, whereas `rlweZkpokReps = 13` (`13 × 20 = 260` bits, matching
       `RLWE_ZKPOK_REPS = 13` in `preprocessing.rs:746`) achieves `2^130 ≥ 2^128` Grover QROM grinding
       security while independent challenges collapse `R = 13` below `2^24`! -/
theorem tooth_independent_challenges_drop_grinding_cost (m : Nat) (hm : 1 ≤ m) :
    indepChallengeGrindCost m ≤ bitWeightedIndepGrindCost m ∧
    bitWeightedIndepGrindCost m < jointChallengeGrindCost m ∧
    indepChallengeGrindCost 20 < 2 ^ 23 ∧
    bitWeightedIndepGrindCost 20 < 2 ^ 28 ∧
    jointChallengeGrindCost 20 = 2 ^ 140 ∧
    groverJointChallengeGrindCost rlweZkpokClassicalReps 20 = 2 ^ 70 ∧
    groverJointChallengeGrindCost rlweZkpokClassicalReps 20 < 2 ^ 128 ∧
    groverJointChallengeGrindCost rlweZkpokReps 20 = 2 ^ 130 ∧
    2 ^ 128 ≤ groverJointChallengeGrindCost rlweZkpokReps 20 ∧
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

/-- Finite discrete-Gaussian rejection-sampling specification over candidate response space `Fin Z`.
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

/-- **`#tooth` Passive RLWE Decryption Without FO Leaks Secret-Key Bits (`tooth_passive_rlwe_decrypt_without_fo_allows_key_dependent_abort`)**:
    A malicious sender crafting boundary ciphertext `u_mal = 1`, `v_mal = 3072` causes passive decryption
    `decodePayload512 (v_mal - u_mal * sR)` at index `0` to output `true` when `sR[0] = 0` (`3072 ∈ [3072, 9216)`)
    and `false` when `sR[0] = 1` (`3071 < 3072`) — directly leaking 1 bit of Receiver's secret key `sR` —
    whereas `rlweFoReceiverMachine` with ternary `deriveCoins` (`a = 0`, `‖e2‖_∞ ≤ 0` or `uExp = 0`) rejects `(u_mal, v_mal)`! -/
