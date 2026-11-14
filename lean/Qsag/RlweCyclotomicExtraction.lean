module
/-
# Qsag.RlweCyclotomicExtraction — Cyclotomic Signed-Monomial Cofactor & 13-Parallel RLWE OR-Sigma Extraction

Constructive, choice-free, kernel-checked formalization of signed-monomial challenge-difference
invertibility over power-of-two cyclotomic rings and 2-special-soundness relaxed RLWE/SIS witness
extraction for a 13-parallel Ring-LWE OR-Sigma protocol over the single signed-monomial challenge set,
together with the challenge-agnostic fork lemma and cofactor step that `Qsag.LatticePreprocessingFull`
applies to the production verifier of `crates/qsag-core/src/preprocessing.rs`:

1. **Parametric Negacyclic Ring Algebra (`NegacyclicPolyInt`, `CycPolyInt`, `ModZq`, `CycPolyZq`)**:
   - Arbitrary-modulus residue ring `ModZq q` ($\mathbb{Z}_q$) with surjective homomorphism `ModZq.ofInt`,
     centered representative `ModZq.centered`, and odd-modulus inverse `(q + 1) / 2` of `2`.
   - Degree-$< 2^\nu$ integer negacyclic ring $\mathbb{Z}[X]/(X^{2^\nu} + 1)$ (`CycPolyInt nu`) and
     quotient ring $R_q = \mathbb{Z}_q[X]/(X^{2^\nu} + 1)$ (`CycPolyZq nu q`) with proved commutativity,
     associativity, distributivity, $X^{2^\nu} = -1$, $\ell_1$-$\ell_\infty$ convolution bounds, and
     signed monomials `signedMonomial nu sign k` ($\pm X^k$).
2. **Exact Cyclotomic Signed-Monomial Cofactor Theorem (`signedMonomial_diff_mul_cofactor_eq_two`)**:
   - For any distinct signed monomials $c_1 \ne c_2$ in $\mathbb{Z}[X]/(X^{2^\nu} + 1)$:
     * When $k_1 = k_2$ and $s_1 \ne s_2$, multiplying $c_1 - c_2 = \pm 2 X^{k_1}$ by $(\pm X^{k_1})^{-1}$
       ($\pm 1$ at $k_1 = 0$, $\mp X^{2^\nu - k_1}$ at $k_1 > 0$) yields $2$ identically with support weight $1$.
     * When $k_1 \ne k_2$, writing $d = |k_2 - k_1| = 2^a \cdot u$ ($u$ odd, $0 \le a < \nu$) and
       $m = 2^{\nu - a}$ (always even since $\nu - a \ge 1$), the explicit $\{-1, 0, +1\}$-coefficient
       geometric-sum cofactor $g(X)$ has support weight $m \le 2^\nu$, $\ell_\infty$ norm $1$, and satisfies
       $(c_1 - c_2) \circledast g(X) = 2$ in $\mathbb{Z}[X]/(X^{2^\nu} + 1)$ prior to any mod-$q$ reduction.
   - **Pairwise Invertibility (`signedMonomial_challenge_set_pairwise_invertible`)**:
     For every odd modulus $q \ge 3$, $((q + 1) / 2) \cdot g(X) \bmod q$ is the exact two-sided inverse
     of $c_1 - c_2$ in $R_q$, covering all $2 \cdot 2^{10} = 2048$ challenges at $\nu = 10, N = 1024$.
3. **13-Parallel RLWE OR-Sigma Witness Extractor & $\ell_\infty$ Norm-Slack (`extract_rlwe_or_sigma_13_witness`)**:
   - Models the 13-parallel RLWE OR-Sigma relation (`c0 ⊕ c1 = c`, `A * zs_b + ze_b = t_b + c_b * u_b`
     in $R_q$, `‖zs_b‖_∞ ≤ B_z`, `‖ze_b‖_∞ ≤ B_z`).
   - Constructive choice-free (`PSum` & direct) extractor locating $(i \in \mathrm{Fin}\, 13, b \in \mathrm{Bool})$
     with $c_{i,b} \ne c'_{i,b}$ and outputting $(s_2, e_2) = (g \circledast \Delta z_s, g \circledast \Delta z_e)$
     satisfying $A \cdot s_2 + e_2 \equiv 2 \cdot u_{i,b} \pmod{q, X^N + 1}$, $\|s_2\|_\infty \le 2 N B_z$,
     $\|e_2\|_\infty \le 2 N B_z$, and exact odd-$q$ unrelaxed inversion modulo $q$. The cofactor witness is
     wraparound-free only for $q \ge 12574722$ at $(N, B_z) = (1024, 3070)$; at $q = 12289$ that premise is
     false and only the fork difference ($2 B_z = 6140 < 6144$) is wraparound-free.
   - **Scope**: the challenge set here is the $2 \cdot 2^\nu$ single signed monomials. Production
     `poly_from_chal20` uses two-term challenges $\pm X^{p_0} \pm X^{512 + p_1}$; their differences are
     signed-monomial differences exactly when one term agrees, and are zero divisors of $R_{12289}$ for
     other pairs (`tooth_two_term_challenge_difference_zero_divisor_12289`). The challenge-agnostic part
     is `rlwe_sigma_fork_difference_relation`; `ExtractedRlweOrSigmaWitness.ofForkDifference` is the
     cofactor step that `Qsag.LatticePreprocessingFull` applies to the production verifier.
4. **Inhabitedness & `#tooth` Counterexamples**:
   - Concrete $N = 1024, q = 12289$ inhabited transcripts and distinct signed-monomial pairs.
   - `#tooth` (a): Over non-power-of-two $\mathbb{Z}_q[X]/(X^3 + 1)$, $(1 + X)(1 - X + X^2) = 0$ makes
     the signed-monomial difference $(+1) - (-X) = 1 + X$ a non-invertible zero divisor for all $q \ge 2$
     (and $1 - X$ at $q = 2$).
   - `#tooth` (b): Over $\mathbb{Z}_q[X]/(X^{2^\nu} + 1)$ for every even $q \ge 2$, $c_1 - c_2 = 2$ is
     a zero divisor / non-unit with no multiplicative inverse.
   - `#tooth` (c): Unforked challenges and norm-violating transcripts are deterministically refused by
     the computational `PSum` extractor.
   - `#tooth` (d): the production challenges $X^{108} + X^{512}$ and $X^{2} + X^{513}$ agree at the root
     $\psi = 1945$ of $X^{1024} + 1$ modulo $12289$, so their difference is a zero divisor with no inverse.
-/

public import Qsag.Constructive

public section
namespace Qsag

set_option autoImplicit false

/-! ## 1. Residue Ring $\mathbb{Z}_q$ & Negacyclic Ring Algebra $\mathbb{Z}[X]/(X^{2^\nu} + 1)$, $R_q$ -/

/-- Production cyclotomic log-dimension $\nu = 10$ ($N = 2^{10} = 1024$). -/
def rlweCyclotomicNu : Nat := 10

/-- Production cyclotomic ring dimension $N = 2^{10} = 1024$ (`RLWE_N` in `preprocessing.rs`). -/
def rlweCyclotomicN : Nat := 2 ^ rlweCyclotomicNu

theorem rlweCyclotomicN_eq_1024 : rlweCyclotomicN = 1024 := by
  unfold rlweCyclotomicN rlweCyclotomicNu; rfl

/-- Production Ring-LWE odd prime modulus $q = 12289$ (`RLWE_Q` in `preprocessing.rs`). -/
def rlweProductionQ : Nat := 12289

/-- Production parallel OR-Sigma repetition count `RLWE_ZKPOK_REPS = 13`. -/
def rlweOrSigmaParallelReps : Nat := 13

/-- Production response-box half-width `RLWE_ZKPOK_Z_BOUND = 3070`. `RlweReceiverZkPok::verify`
    accepts every coefficient of the half-open box `-3070 ≤ z_i < 3070`
    (`(-RLWE_ZKPOK_Z_BOUND..RLWE_ZKPOK_Z_BOUND).contains(&v)`), so the value `-3070` is accepted and the
    tight symmetric bound is `‖z‖_∞ ≤ 3070`. -/
def rlweProductionBz : Nat := 3070

instance : NeZero rlweProductionQ := ⟨by decide⟩

/-- Residue ring $\mathbb{Z}_q = \mathbb{Z}/q\mathbb{Z}$ for arbitrary modulus $q \ge 1$. -/
structure ModZq (q : Nat) where
  val : Nat
  isLt : val < q
  deriving DecidableEq, Repr

theorem ModZq.ext {q : Nat} {a b : ModZq q} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp only [mk.injEq]; exact h

private theorem ModZq.ext_int {q : Nat} {a b : ModZq q} (h : (a.val : Int) = (b.val : Int)) : a = b :=
  ModZq.ext (Int.ofNat.inj h)

private theorem modZq_pos (q : Nat) [NeZero q] : 0 < q :=
  Nat.pos_of_ne_zero (NeZero.ne q)

/-- Canonical Euclidean projection $\mathbb{Z} \to \mathbb{Z}_q$. -/
@[expose] def ModZq.ofInt (q : Nat) [NeZero q] (z : Int) : ModZq q :=
  ⟨(z % (q : Int)).toNat, by
    have hqPos : (0 : Int) < (q : Int) := Int.natCast_pos.mpr (modZq_pos q)
    have h0 : 0 ≤ z % (q : Int) := Int.emod_nonneg z (Int.ne_of_gt hqPos)
    have h1 : z % (q : Int) < (q : Int) := Int.emod_lt_of_pos z hqPos
    omega⟩

theorem ModZq.ofInt_val_int (q : Nat) [NeZero q] (z : Int) :
    ((ModZq.ofInt q z).val : Int) = z % (q : Int) := by
  unfold ModZq.ofInt
  dsimp only
  have hqPos : (0 : Int) < (q : Int) := Int.natCast_pos.mpr (modZq_pos q)
  exact Int.toNat_of_nonneg (Int.emod_nonneg z (Int.ne_of_gt hqPos))

@[simp] theorem ModZq.ofInt_natVal {q : Nat} [NeZero q] (a : ModZq q) :
    ModZq.ofInt q (a.val : Int) = a := by
  apply ModZq.ext
  have hLt := a.isLt
  unfold ModZq.ofInt
  dsimp only
  have hMod : (a.val : Int) % (q : Int) = (a.val : Int) :=
    Int.emod_eq_of_lt (Int.natCast_nonneg a.val) (Int.ofNat_lt.mpr hLt)
  rw [hMod]
  exact Int.toNat_natCast a.val

/-- Centered representative of $a \in \mathbb{Z}_q$ in $[-\lceil(q-1)/2\rceil, \lfloor q/2 \rfloor]$. -/
def ModZq.centered {q : Nat} (a : ModZq q) : Int :=
  if a.val ≤ q / 2 then (a.val : Int) else (a.val : Int) - (q : Int)

theorem ModZq.ofInt_centered {q : Nat} [NeZero q] (a : ModZq q) :
    ModZq.ofInt q a.centered = a := by
  unfold ModZq.centered
  split
  · exact ModZq.ofInt_natVal a
  · apply ModZq.ext
    have hVal := ModZq.ofInt_val_int q ((a.val : Int) - (q : Int))
    have hSub : ((a.val : Int) - (q : Int)) % (q : Int) = (a.val : Int) % (q : Int) := by
      have hEq : (a.val : Int) - (q : Int) = (a.val : Int) + (-1) * (q : Int) := by omega
      rw [hEq, Int.add_mul_emod_self_right]
    have hMod : (a.val : Int) % (q : Int) = (a.val : Int) :=
      Int.emod_eq_of_lt (Int.natCast_nonneg a.val) (Int.ofNat_lt.mpr a.isLt)
    omega

/-- Exact zero-wraparound recovery: any integer $z$ with $|z| < \lfloor q / 2 \rfloor$ (or $|z| \le \lfloor q / 2 \rfloor$
    when $q$ is odd) lifts back identically from $\mathbb{Z}_q$ via `ModZq.centered`. -/
theorem ModZq.centered_ofInt_exact {q : Nat} [NeZero q] (z : Int)
    (hSmall : z.natAbs < q / 2 ∨ (q % 2 = 1 ∧ z.natAbs ≤ q / 2)) :
    (ModZq.ofInt q z).centered = z := by
  have hqPos := modZq_pos q
  have hVal := ModZq.ofInt_val_int q z
  have hLt := (ModZq.ofInt q z).isLt
  unfold ModZq.centered
  by_cases hzNonneg : 0 ≤ z
  · have hzLtQ : z < (q : Int) := by omega
    have hMod : z % (q : Int) = z := Int.emod_eq_of_lt hzNonneg hzLtQ
    rw [hMod] at hVal
    have hLe : (ModZq.ofInt q z).val ≤ q / 2 := by omega
    simp only [hLe, ↓reduceIte]
    omega
  · have hzPosQ : 0 < (q : Int) + z := by omega
    have hzLtQ : (q : Int) + z < (q : Int) := by omega
    have hShift : z % (q : Int) = (q : Int) + z := by
      have hEq : z = ((q : Int) + z) + (-1) * (q : Int) := by omega
      conv => lhs; rw [hEq]
      rw [Int.add_mul_emod_self_right]
      exact Int.emod_eq_of_lt (by omega) hzLtQ
    rw [hShift] at hVal
    have hNotLe : ¬((ModZq.ofInt q z).val ≤ q / 2) := by omega
    simp only [hNotLe, ↓reduceIte]
    omega

def ModZq.zero (q : Nat) [NeZero q] : ModZq q := ⟨0, modZq_pos q⟩
def ModZq.one (q : Nat) [NeZero q] : ModZq q := ⟨1 % q, Nat.mod_lt 1 (modZq_pos q)⟩
def ModZq.add {q : Nat} [NeZero q] (a b : ModZq q) : ModZq q :=
  ⟨(a.val + b.val) % q, Nat.mod_lt _ (modZq_pos q)⟩
def ModZq.mul {q : Nat} [NeZero q] (a b : ModZq q) : ModZq q :=
  ⟨(a.val * b.val) % q, Nat.mod_lt _ (modZq_pos q)⟩
def ModZq.neg {q : Nat} [NeZero q] (a : ModZq q) : ModZq q :=
  ⟨(q - a.val) % q, Nat.mod_lt _ (modZq_pos q)⟩
def ModZq.sub {q : Nat} [NeZero q] (a b : ModZq q) : ModZq q :=
  ⟨(a.val + q - b.val) % q, Nat.mod_lt _ (modZq_pos q)⟩

theorem ModZq.ofInt_zero (q : Nat) [NeZero q] : ModZq.ofInt q 0 = ModZq.zero q := by
  apply ModZq.ext_int
  dsimp only [ModZq.zero]
  rw [ModZq.ofInt_val_int, Int.zero_emod]
  rfl

theorem ModZq.ofInt_one (q : Nat) [NeZero q] : ModZq.ofInt q 1 = ModZq.one q := by
  apply ModZq.ext_int
  dsimp only [ModZq.one]
  rw [ModZq.ofInt_val_int, Int.natCast_emod]
  rfl

theorem ModZq.ofInt_add (q : Nat) [NeZero q] (x y : Int) :
    ModZq.ofInt q (x + y) = ModZq.add (ModZq.ofInt q x) (ModZq.ofInt q y) := by
  apply ModZq.ext_int
  dsimp only [ModZq.add]
  rw [ModZq.ofInt_val_int, Int.natCast_emod, Int.natCast_add,
      ModZq.ofInt_val_int, ModZq.ofInt_val_int]
  exact Int.add_emod x y (q : Int)

theorem ModZq.ofInt_sub (q : Nat) [NeZero q] (x y : Int) :
    ModZq.ofInt q (x - y) = ModZq.sub (ModZq.ofInt q x) (ModZq.ofInt q y) := by
  apply ModZq.ext_int
  dsimp only [ModZq.sub]
  rw [ModZq.ofInt_val_int, Int.natCast_emod]
  have hyLt := (ModZq.ofInt q y).isLt
  have hNat : (((ModZq.ofInt q x).val + q - (ModZq.ofInt q y).val : Nat) : Int) =
      ((ModZq.ofInt q x).val : Int) + (q : Int) - ((ModZq.ofInt q y).val : Int) := by omega
  rw [hNat, ModZq.ofInt_val_int, ModZq.ofInt_val_int]
  have hShift : x % (q : Int) + (q : Int) - y % (q : Int) =
      (x % (q : Int) - y % (q : Int)) + 1 * (q : Int) := by omega
  rw [hShift, Int.add_mul_emod_self_right, ← Int.sub_emod]

theorem ModZq.ofInt_neg (q : Nat) [NeZero q] (x : Int) :
    ModZq.ofInt q (-x) = ModZq.neg (ModZq.ofInt q x) := by
  have hSub : (-x : Int) = 0 - x := by omega
  rw [hSub, ModZq.ofInt_sub, ModZq.ofInt_zero]
  apply ModZq.ext
  dsimp only [ModZq.sub, ModZq.zero, ModZq.neg]
  rw [Nat.zero_add]

theorem ModZq.ofInt_mul (q : Nat) [NeZero q] (x y : Int) :
    ModZq.ofInt q (x * y) = ModZq.mul (ModZq.ofInt q x) (ModZq.ofInt q y) := by
  apply ModZq.ext_int
  dsimp only [ModZq.mul]
  rw [ModZq.ofInt_val_int, Int.natCast_emod, Int.natCast_mul,
      ModZq.ofInt_val_int, ModZq.ofInt_val_int]
  exact Int.mul_emod x y (q : Int)

/-- Multiplicative inverse $(q + 1) / 2 \bmod q$ of $2$ in $\mathbb{Z}_q$ for any odd modulus $q$. -/
def ModZq.invTwo (q : Nat) [NeZero q] : ModZq q :=
  ModZq.ofInt q (((q + 1) / 2 : Nat) : Int)

theorem ModZq.two_mul_invTwo (q : Nat) [NeZero q] (hOdd : q % 2 = 1) :
    ModZq.mul (ModZq.ofInt q 2) (ModZq.invTwo q) = ModZq.one q := by
  unfold ModZq.invTwo
  rw [← ModZq.ofInt_mul, ← ModZq.ofInt_one]
  apply ModZq.ext_int
  rw [ModZq.ofInt_val_int, ModZq.ofInt_val_int]
  have hMul : (2 : Int) * (((q + 1) / 2 : Nat) : Int) = 1 + 1 * (q : Int) := by omega
  rw [hMul, Int.add_mul_emod_self_right]

/-! ### 1.1 Constructive Finite Summations & Integer Negacyclic Algebra $\mathbb{Z}[X]/(X^N + 1)$ -/

private def cycNatFinSum : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => f ⟨0, Nat.zero_lt_succ n⟩ + cycNatFinSum n (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)

private theorem cycNatFinSum_congr {n : Nat} {f g : Fin n → Nat} (h : ∀ i, f i = g i) :
    cycNatFinSum n f = cycNatFinSum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [cycNatFinSum, h ⟨0, Nat.zero_lt_succ n⟩]
    rw [ih (fun i => h ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)]

private theorem cycNatFinSum_const (n c : Nat) : cycNatFinSum n (fun _ => c) = n * c := by
  induction n with
  | zero => simp [cycNatFinSum]
  | succ n ih => simp only [cycNatFinSum, ih, Nat.succ_mul]; omega

private theorem cycNatFinSum_zero (n : Nat) : cycNatFinSum n (fun _ => 0) = 0 := by
  simpa using cycNatFinSum_const n 0

private theorem cycNatFinSum_add {n : Nat} (f g : Fin n → Nat) :
    cycNatFinSum n (fun i => f i + g i) = cycNatFinSum n f + cycNatFinSum n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [cycNatFinSum, ih]; omega

private theorem cycNatFinSum_le {n : Nat} {f g : Fin n → Nat} (h : ∀ i, f i ≤ g i) :
    cycNatFinSum n f ≤ cycNatFinSum n g := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    simp only [cycNatFinSum]
    have h0 := h ⟨0, Nat.zero_lt_succ n⟩
    have hRest := ih (fun i => h ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
    omega

private theorem cycNatFinSum_mul_right {n : Nat} (f : Fin n → Nat) (c : Nat) :
    cycNatFinSum n (fun i => f i * c) = cycNatFinSum n f * c := by
  induction n with
  | zero => simp [cycNatFinSum]
  | succ n ih => simp only [cycNatFinSum, ih, Nat.add_mul]

private theorem cycNatFinSum_comm (m n : Nat) (g : Fin m → Fin n → Nat) :
    cycNatFinSum m (fun i => cycNatFinSum n (fun j => g i j)) =
    cycNatFinSum n (fun j => cycNatFinSum m (fun i => g i j)) := by
  induction m with
  | zero => symm; exact cycNatFinSum_zero n
  | succ m ih =>
    simp only [cycNatFinSum]
    rw [ih (fun i j => g ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ j), ← cycNatFinSum_add]

private theorem cycNatFinSum_eq_single : ∀ {n : Nat} (i₀ : Fin n) (f : Fin n → Nat),
    (∀ i : Fin n, i ≠ i₀ → f i = 0) → cycNatFinSum n f = f i₀
  | 0, i₀, _, _ => Fin.elim0 i₀
  | n + 1, ⟨0, _⟩, f, hZero => by
    simp only [cycNatFinSum]
    have hRest : cycNatFinSum n (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) = cycNatFinSum n (fun _ => 0) := by
      apply cycNatFinSum_congr
      intro i
      apply hZero
      intro heq
      have hv := congrArg Fin.val heq
      dsimp only at hv
      omega
    rw [hRest, cycNatFinSum_zero, Nat.add_zero]
  | n + 1, ⟨k + 1, hk⟩, f, hZero => by
    simp only [cycNatFinSum]
    have h0 : f ⟨0, Nat.zero_lt_succ n⟩ = 0 :=
      hZero _ (by intro heq; have hv := congrArg Fin.val heq; dsimp only at hv; omega)
    rw [h0, Nat.zero_add]
    exact cycNatFinSum_eq_single ⟨k, Nat.lt_of_succ_lt_succ hk⟩
      (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
      (fun i hi => hZero _ (fun heq => hi (by
        have hv : i.1 + 1 = k + 1 := congrArg Fin.val heq
        exact Fin.ext (Nat.succ.inj hv))))

private def cycIntFinSum : (n : Nat) → (Fin n → Int) → Int
  | 0, _ => 0
  | n + 1, f => f ⟨0, Nat.zero_lt_succ n⟩ + cycIntFinSum n (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)

private theorem cycIntFinSum_congr {n : Nat} {f g : Fin n → Int} (h : ∀ i, f i = g i) :
    cycIntFinSum n f = cycIntFinSum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [cycIntFinSum, h ⟨0, Nat.zero_lt_succ n⟩]
    rw [ih (fun i => h ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)]

private theorem cycIntFinSum_zero (n : Nat) : cycIntFinSum n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [cycIntFinSum, ih]

private theorem cycIntFinSum_add {n : Nat} (f g : Fin n → Int) :
    cycIntFinSum n (fun i => f i + g i) = cycIntFinSum n f + cycIntFinSum n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [cycIntFinSum, ih]; omega

private theorem cycIntFinSum_neg {n : Nat} (f : Fin n → Int) :
    cycIntFinSum n (fun i => -f i) = -cycIntFinSum n f := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [cycIntFinSum, ih]; omega

private theorem cycIntFinSum_mul_left {n : Nat} (c : Int) (f : Fin n → Int) :
    cycIntFinSum n (fun i => c * f i) = c * cycIntFinSum n f := by
  induction n with
  | zero => simp [cycIntFinSum]
  | succ n ih => simp only [cycIntFinSum, ih, Int.mul_add]

private theorem cycIntFinSum_mul_right {n : Nat} (f : Fin n → Int) (c : Int) :
    cycIntFinSum n (fun i => f i * c) = cycIntFinSum n f * c := by
  induction n with
  | zero => simp [cycIntFinSum]
  | succ n ih => simp only [cycIntFinSum, ih, Int.add_mul]

private theorem cycIntFinSum_comm (m n : Nat) (g : Fin m → Fin n → Int) :
    cycIntFinSum m (fun i => cycIntFinSum n (fun j => g i j)) =
    cycIntFinSum n (fun j => cycIntFinSum m (fun i => g i j)) := by
  induction m with
  | zero => symm; exact cycIntFinSum_zero n
  | succ m ih =>
    simp only [cycIntFinSum]
    rw [ih (fun i j => g ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ j), ← cycIntFinSum_add]

private theorem cycIntFinSum_eq_single : ∀ {n : Nat} (i₀ : Fin n) (f : Fin n → Int),
    (∀ i : Fin n, i ≠ i₀ → f i = 0) → cycIntFinSum n f = f i₀
  | 0, i₀, _, _ => Fin.elim0 i₀
  | n + 1, ⟨0, _⟩, f, hZero => by
    simp only [cycIntFinSum]
    have hRest : cycIntFinSum n (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) = cycIntFinSum n (fun _ => 0) := by
      apply cycIntFinSum_congr
      intro i
      apply hZero
      intro heq
      have hv := congrArg Fin.val heq
      dsimp only at hv
      omega
    rw [hRest, cycIntFinSum_zero, Int.add_zero]
  | n + 1, ⟨k + 1, hk⟩, f, hZero => by
    simp only [cycIntFinSum]
    have h0 : f ⟨0, Nat.zero_lt_succ n⟩ = 0 :=
      hZero _ (by intro heq; have hv := congrArg Fin.val heq; dsimp only at hv; omega)
    rw [h0, Int.zero_add]
    exact cycIntFinSum_eq_single ⟨k, Nat.lt_of_succ_lt_succ hk⟩
      (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
      (fun i hi => hZero _ (fun heq => hi (by
        have hv : i.1 + 1 = k + 1 := congrArg Fin.val heq
        exact Fin.ext (Nat.succ.inj hv))))

private theorem cycIntFinSum_natAbs_le : ∀ {n : Nat} (f : Fin n → Int),
    (cycIntFinSum n f).natAbs ≤ cycNatFinSum n (fun i => (f i).natAbs)
  | 0, _ => Nat.le_refl 0
  | n + 1, f => by
    simp only [cycIntFinSum, cycNatFinSum]
    have ih := cycIntFinSum_natAbs_le (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
    exact Nat.le_trans (Int.natAbs_add_le _ _) (Nat.add_le_add_left ih _)

private def cycModZqFinSum {q : Nat} [NeZero q] : (m : Nat) → (Fin m → ModZq q) → ModZq q
  | 0, _ => ModZq.zero q
  | m + 1, g => ModZq.add (g ⟨0, Nat.zero_lt_succ m⟩)
      (cycModZqFinSum m (fun i => g ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩))

private theorem cycModZqFinSum_congr {q : Nat} [NeZero q] {m : Nat}
    {f g : Fin m → ModZq q} (h : ∀ i, f i = g i) :
    cycModZqFinSum m f = cycModZqFinSum m g := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [cycModZqFinSum, h ⟨0, Nat.zero_lt_succ m⟩]
    rw [ih (fun i => h ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)]

private theorem cycIntFinSum_ofInt_hom (q : Nat) [NeZero q] {n : Nat} (f : Fin n → Int) :
    ModZq.ofInt q (cycIntFinSum n f) = cycModZqFinSum n (fun i => ModZq.ofInt q (f i)) := by
  induction n with
  | zero => exact ModZq.ofInt_zero q
  | succ n ih =>
    simp only [cycIntFinSum, cycModZqFinSum, ModZq.ofInt_add]
    rw [ih (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)]

/-- Degree-$< N$ integer polynomial representing an element of $\mathbb{Z}[X]/(X^N + 1)$. -/
abbrev NegacyclicPolyInt (N : Nat) := Fin N → Int

/-- Power-of-two cyclotomic integer polynomial in $\mathbb{Z}[X]/(X^{2^\nu} + 1)$. -/
abbrev CycPolyInt (nu : Nat) := NegacyclicPolyInt (2 ^ nu)

def cycIntZero {N : Nat} : NegacyclicPolyInt N := fun _ => 0
def cycIntOne {N : Nat} : NegacyclicPolyInt N := fun k => if k.val = 0 then 1 else 0
def cycIntAdd {N : Nat} (a b : NegacyclicPolyInt N) : NegacyclicPolyInt N := fun k => a k + b k
def cycIntSub {N : Nat} (a b : NegacyclicPolyInt N) : NegacyclicPolyInt N := fun k => a k - b k
def cycIntNeg {N : Nat} (a : NegacyclicPolyInt N) : NegacyclicPolyInt N := fun k => -a k
def cycIntScale {N : Nat} (c : Int) (a : NegacyclicPolyInt N) : NegacyclicPolyInt N := fun k => c * a k

private def cycNegacyclicKernel (N k i j : Nat) (prod : Int) : Int :=
  if i + j = k then prod
  else if i + j = N + k then -prod
  else 0

private def cycNegacyclicKernel3 (N m s : Nat) (prod : Int) : Int :=
  if s = m then prod
  else if s = N + m then -prod
  else if s = 2 * N + m then prod
  else 0

/-- Negacyclic polynomial multiplication in $\mathbb{Z}[X]/(X^N + 1)$ ($X^N = -1$). -/
def cycIntMul {N : Nat} (a b : NegacyclicPolyInt N) : NegacyclicPolyInt N :=
  fun k => cycIntFinSum N (fun i => cycIntFinSum N (fun j =>
    cycNegacyclicKernel N k.val i.val j.val (a i * b j)))

/-- Single-sum $O(N^2)$ negacyclic convolution in $\mathbb{Z}[X]/(X^N + 1)$. -/
def cycIntMulSingle {N : Nat} (a b : NegacyclicPolyInt N) : NegacyclicPolyInt N :=
  fun k => cycIntFinSum N (fun i =>
    if h : i.val ≤ k.val then
      a i * b ⟨k.val - i.val, by omega⟩
    else
      -(a i * b ⟨N + k.val - i.val, by omega⟩))

theorem cycIntMul_eq_single {N : Nat} (a b : NegacyclicPolyInt N) :
    cycIntMul a b = cycIntMulSingle a b := by
  funext k
  unfold cycIntMul cycIntMulSingle
  apply cycIntFinSum_congr
  intro i
  by_cases hik : i.val ≤ k.val
  · simp only [hik, ↓reduceDIte]
    let j₀ : Fin N := ⟨k.val - i.val, by omega⟩
    rw [cycIntFinSum_eq_single j₀]
    · unfold cycNegacyclicKernel
      dsimp only [j₀]
      have hij : i.val + (k.val - i.val) = k.val := by omega
      simp only [hij, ↓reduceIte]
    · intro j hjNe
      unfold cycNegacyclicKernel
      have h1 : i.val + j.val ≠ k.val := by
        intro heq; apply hjNe; apply Fin.ext; dsimp [j₀]; omega
      have h2 : i.val + j.val ≠ N + k.val := by have := j.isLt; omega
      simp only [h1, h2, ↓reduceIte]
  · simp only [hik, ↓reduceDIte]
    let j₀ : Fin N := ⟨N + k.val - i.val, by omega⟩
    rw [cycIntFinSum_eq_single j₀]
    · unfold cycNegacyclicKernel
      dsimp only [j₀]
      have hiLt := i.isLt
      have h1 : i.val + (N + k.val - i.val) ≠ k.val := by omega
      have h2 : i.val + (N + k.val - i.val) = N + k.val := by omega
      simp only [h1, ↓reduceIte]
      simp only [h2, ↓reduceIte]
    · intro j hjNe
      unfold cycNegacyclicKernel
      have h1 : i.val + j.val ≠ k.val := by omega
      have h2 : i.val + j.val ≠ N + k.val := by
        intro heq; apply hjNe; apply Fin.ext; dsimp [j₀]; omega
      simp only [h1, h2, ↓reduceIte]

theorem cycIntMul_comm {N : Nat} (a b : NegacyclicPolyInt N) :
    cycIntMul a b = cycIntMul b a := by
  funext k
  unfold cycIntMul
  rw [cycIntFinSum_comm]
  apply cycIntFinSum_congr; intro j
  apply cycIntFinSum_congr; intro i
  unfold cycNegacyclicKernel
  rw [Nat.add_comm i.val j.val, Int.mul_comm (a i) (b j)]

theorem cycIntMul_left_distrib {N : Nat} (a b c : NegacyclicPolyInt N) :
    cycIntMul a (cycIntAdd b c) = cycIntAdd (cycIntMul a b) (cycIntMul a c) := by
  funext k
  unfold cycIntMul cycIntAdd
  rw [← cycIntFinSum_add]
  apply cycIntFinSum_congr; intro i
  rw [← cycIntFinSum_add]
  apply cycIntFinSum_congr; intro j
  unfold cycNegacyclicKernel
  rw [Int.mul_add]
  split
  · rfl
  · split <;> omega

theorem cycIntMul_right_distrib {N : Nat} (a b c : NegacyclicPolyInt N) :
    cycIntMul (cycIntAdd a b) c = cycIntAdd (cycIntMul a c) (cycIntMul b c) := by
  rw [cycIntMul_comm, cycIntMul_left_distrib, cycIntMul_comm c a, cycIntMul_comm c b]

theorem cycIntMul_neg_right {N : Nat} (a b : NegacyclicPolyInt N) :
    cycIntMul a (cycIntNeg b) = cycIntNeg (cycIntMul a b) := by
  funext k
  unfold cycIntMul cycIntNeg
  rw [← cycIntFinSum_neg]
  apply cycIntFinSum_congr; intro i
  rw [← cycIntFinSum_neg]
  apply cycIntFinSum_congr; intro j
  unfold cycNegacyclicKernel
  rw [Int.mul_neg]
  split
  · rfl
  · split <;> omega

theorem cycIntMul_neg_left {N : Nat} (a b : NegacyclicPolyInt N) :
    cycIntMul (cycIntNeg a) b = cycIntNeg (cycIntMul a b) := by
  rw [cycIntMul_comm, cycIntMul_neg_right, cycIntMul_comm]

theorem cycIntMul_sub_right {N : Nat} (a b c : NegacyclicPolyInt N) :
    cycIntMul a (cycIntSub b c) = cycIntSub (cycIntMul a b) (cycIntMul a c) := by
  have hEq : cycIntSub b c = cycIntAdd b (cycIntNeg c) := by
    funext k; dsimp only [cycIntSub, cycIntAdd, cycIntNeg]; omega
  rw [hEq, cycIntMul_left_distrib, cycIntMul_neg_right]
  funext k; dsimp only [cycIntSub, cycIntAdd, cycIntNeg]; omega

theorem cycIntMul_sub_left {N : Nat} (a b c : NegacyclicPolyInt N) :
    cycIntMul (cycIntSub a b) c = cycIntSub (cycIntMul a c) (cycIntMul b c) := by
  rw [cycIntMul_comm, cycIntMul_sub_right, cycIntMul_comm c a, cycIntMul_comm c b]

theorem cycIntMul_zero_right {N : Nat} (a : NegacyclicPolyInt N) :
    cycIntMul a cycIntZero = cycIntZero := by
  funext k
  unfold cycIntMul cycIntZero
  have h0 : ∀ i : Fin N, cycIntFinSum N (fun j : Fin N =>
      cycNegacyclicKernel N k.val i.val j.val (a i * 0)) = 0 := by
    intro i
    have hIn : ∀ j : Fin N, cycNegacyclicKernel N k.val i.val j.val (a i * 0) = 0 := by
      intro j; unfold cycNegacyclicKernel; rw [Int.mul_zero]
      split
      · rfl
      · split <;> rfl
    rw [cycIntFinSum_congr hIn, cycIntFinSum_zero]
  rw [cycIntFinSum_congr h0, cycIntFinSum_zero]

theorem cycIntMul_zero_left {N : Nat} (a : NegacyclicPolyInt N) :
    cycIntMul cycIntZero a = cycIntZero := by
  rw [cycIntMul_comm, cycIntMul_zero_right]

theorem cycIntMul_scale_right {N : Nat} (c : Int) (a b : NegacyclicPolyInt N) :
    cycIntMul a (cycIntScale c b) = cycIntScale c (cycIntMul a b) := by
  funext k
  unfold cycIntMul cycIntScale
  rw [← cycIntFinSum_mul_left]
  apply cycIntFinSum_congr; intro i
  rw [← cycIntFinSum_mul_left]
  apply cycIntFinSum_congr; intro j
  unfold cycNegacyclicKernel
  have hMul : a i * (c * b j) = c * (a i * b j) := by
    rw [← Int.mul_assoc, Int.mul_comm (a i) c, Int.mul_assoc]
  rw [hMul]
  split
  · rfl
  · split
    · exact (Int.mul_neg c (a i * b j)).symm
    · exact (Int.mul_zero c).symm

theorem cycIntMul_scale_left {N : Nat} (c : Int) (a b : NegacyclicPolyInt N) :
    cycIntMul (cycIntScale c a) b = cycIntScale c (cycIntMul a b) := by
  rw [cycIntMul_comm, cycIntMul_scale_right, cycIntMul_comm]

private theorem cycNegacyclicKernel_compose_left {N : Nat}
    (m : Fin N) (i j l : Fin N) (P : Int) :
    cycIntFinSum N (fun u => cycNegacyclicKernel N m.val u.val l.val
      (cycNegacyclicKernel N u.val i.val j.val P)) =
    cycNegacyclicKernel3 N m.val (i.val + j.val + l.val) P := by
  have hi := i.isLt; have hj := j.isLt; have hl := l.isLt; have hm := m.isLt
  by_cases hij : i.val + j.val < N
  · let u₀ : Fin N := ⟨i.val + j.val, hij⟩
    rw [cycIntFinSum_eq_single u₀]
    · unfold cycNegacyclicKernel cycNegacyclicKernel3
      dsimp only [u₀]
      have hNot2N : i.val + j.val + l.val ≠ 2 * N + m.val := by omega
      simp only [↓reduceIte, hNot2N]
    · intro u huNe
      unfold cycNegacyclicKernel
      have h1 : i.val + j.val ≠ u.val := fun heq => huNe (Fin.ext heq.symm)
      have h2 : i.val + j.val ≠ N + u.val := by omega
      simp only [h1, h2, ↓reduceIte, Int.neg_zero, ite_self]
  · let u₀ : Fin N := ⟨i.val + j.val - N, by omega⟩
    rw [cycIntFinSum_eq_single u₀]
    · have hInner : cycNegacyclicKernel N (i.val + j.val - N) i.val j.val P = -P := by
        unfold cycNegacyclicKernel
        split
        · exfalso; omega
        · split
          · rfl
          · exfalso; omega
      dsimp only [u₀]
      rw [hInner]
      unfold cycNegacyclicKernel cycNegacyclicKernel3
      split
      · split
        · exfalso; omega
        · split
          · rfl
          · exfalso; omega
      · split
        · split
          · exfalso; omega
          · split
            · exfalso; omega
            · split
              · exact Int.neg_neg P
              · exfalso; omega
        · split
          · exfalso; omega
          · split
            · exfalso; omega
            · split
              · exfalso; omega
              · rfl
    · intro u huNe
      unfold cycNegacyclicKernel
      have hu := u.isLt
      have h1 : i.val + j.val ≠ u.val := by omega
      have h2 : i.val + j.val ≠ N + u.val := by
        intro heq; apply huNe; apply Fin.ext; dsimp [u₀]; omega
      simp only [h1, h2, ↓reduceIte, Int.neg_zero, ite_self]

private theorem cycNegacyclicKernel_mul_right (N k i j : Nat) (P c : Int) :
    cycNegacyclicKernel N k i j P * c = cycNegacyclicKernel N k i j (P * c) := by
  unfold cycNegacyclicKernel
  split
  · rfl
  · split
    · exact Int.neg_mul P c
    · exact Int.zero_mul c

private theorem cycIntMul_triple_eq {N : Nat} (a b c : NegacyclicPolyInt N) (m : Fin N) :
    cycIntMul (cycIntMul a b) c m =
      cycIntFinSum N (fun i => cycIntFinSum N (fun j => cycIntFinSum N (fun l =>
        cycNegacyclicKernel3 N m.val (i.val + j.val + l.val) ((a i * b j) * c l)))) := by
  unfold cycIntMul
  rw [cycIntFinSum_comm]
  have hStep : ∀ l : Fin N,
      cycIntFinSum N (fun u => cycNegacyclicKernel N m.val u.val l.val
        (cycIntFinSum N (fun i => cycIntFinSum N (fun j => cycNegacyclicKernel N u.val i.val j.val (a i * b j))) * c l)) =
      cycIntFinSum N (fun i => cycIntFinSum N (fun j =>
        cycNegacyclicKernel3 N m.val (i.val + j.val + l.val) ((a i * b j) * c l))) := by
    intro l
    have hPush : ∀ u : Fin N,
        cycNegacyclicKernel N m.val u.val l.val
          (cycIntFinSum N (fun i => cycIntFinSum N (fun j => cycNegacyclicKernel N u.val i.val j.val (a i * b j))) * c l) =
        cycIntFinSum N (fun i => cycIntFinSum N (fun j =>
          cycNegacyclicKernel N m.val u.val l.val
            (cycNegacyclicKernel N u.val i.val j.val ((a i * b j) * c l)))) := by
      intro u
      have hIn : cycIntFinSum N (fun i => cycIntFinSum N (fun j => cycNegacyclicKernel N u.val i.val j.val (a i * b j))) * c l =
          cycIntFinSum N (fun i => cycIntFinSum N (fun j => cycNegacyclicKernel N u.val i.val j.val ((a i * b j) * c l))) := by
        rw [← cycIntFinSum_mul_right]
        apply cycIntFinSum_congr; intro i
        rw [← cycIntFinSum_mul_right]
        apply cycIntFinSum_congr; intro j
        exact cycNegacyclicKernel_mul_right N u.val i.val j.val (a i * b j) (c l)
      rw [hIn]
      unfold cycNegacyclicKernel
      split
      · rfl
      · split
        · rw [← cycIntFinSum_neg]
          apply cycIntFinSum_congr; intro i
          rw [← cycIntFinSum_neg]
        · symm
          have hZ : ∀ _ : Fin N, cycIntFinSum N (fun _ : Fin N => (0 : Int)) = 0 := fun _ => cycIntFinSum_zero N
          rw [cycIntFinSum_congr hZ, cycIntFinSum_zero]
    rw [cycIntFinSum_congr hPush, cycIntFinSum_comm]
    apply cycIntFinSum_congr; intro i
    rw [cycIntFinSum_comm]
    apply cycIntFinSum_congr; intro j
    exact cycNegacyclicKernel_compose_left m i j l ((a i * b j) * c l)
  rw [cycIntFinSum_congr hStep, cycIntFinSum_comm]
  apply cycIntFinSum_congr; intro i
  rw [cycIntFinSum_comm]

theorem cycIntMul_assoc {N : Nat} (a b c : NegacyclicPolyInt N) :
    cycIntMul (cycIntMul a b) c = cycIntMul a (cycIntMul b c) := by
  funext m
  rw [cycIntMul_comm a (cycIntMul b c), cycIntMul_triple_eq, cycIntMul_triple_eq]
  rw [cycIntFinSum_comm]
  apply cycIntFinSum_congr; intro j
  rw [cycIntFinSum_comm]
  apply cycIntFinSum_congr; intro l
  apply cycIntFinSum_congr; intro i
  have hIdx : i.val + j.val + l.val = j.val + l.val + i.val := by omega
  have hProd : (a i * b j) * c l = (b j * c l) * a i := by
    rw [Int.mul_assoc, Int.mul_comm (a i) (b j * c l)]
  rw [hIdx, hProd]

theorem cycIntMul_one_left {N : Nat} (hN : 0 < N) (a : NegacyclicPolyInt N) :
    cycIntMul cycIntOne a = a := by
  rw [cycIntMul_eq_single]
  funext k
  unfold cycIntMulSingle cycIntOne
  rw [cycIntFinSum_eq_single ⟨0, hN⟩]
  · simp
  · intro i hiNe
    have hi0 : i.val ≠ 0 := fun heq => hiNe (Fin.ext heq)
    by_cases hik : i.val ≤ k.val
    · simp [hik, hi0]
    · simp [hik, hi0]

theorem cycIntMul_one_right {N : Nat} (hN : 0 < N) (a : NegacyclicPolyInt N) :
    cycIntMul a cycIntOne = a := by
  rw [cycIntMul_comm, cycIntMul_one_left hN]

/-! ### 1.2 $\ell_\infty$, $\ell_1$, Support Weight & Negacyclic Convolution Norm Bounds -/

/-- $\ell_\infty$ norm $\|p\|_\infty = \max_{k < N} |p_k|$. -/
def cycIntInfNorm : {N : Nat} → NegacyclicPolyInt N → Nat
  | 0, _ => 0
  | n + 1, p => max (p ⟨0, Nat.zero_lt_succ n⟩).natAbs
      (cycIntInfNorm (fun i => p ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩))

/-- $\ell_1$ norm $\|p\|_1 = \sum_{k < N} |p_k|$. -/
def cycIntL1Norm {N : Nat} (p : NegacyclicPolyInt N) : Nat :=
  cycNatFinSum N (fun i => (p i).natAbs)

/-- Hamming support weight $|\{k < N \mid p_k \ne 0\}|$. -/
def cycIntSupportWeight {N : Nat} (p : NegacyclicPolyInt N) : Nat :=
  cycNatFinSum N (fun i => if p i = 0 then 0 else 1)

theorem cycCoeff_natAbs_le_infNorm : ∀ {N : Nat} (p : NegacyclicPolyInt N) (k : Fin N),
    (p k).natAbs ≤ cycIntInfNorm p
  | 0, _, k => Fin.elim0 k
  | _ + 1, _, ⟨0, _⟩ => Nat.le_max_left _ _
  | _ + 1, p, ⟨k + 1, hk⟩ =>
    Nat.le_trans (cycCoeff_natAbs_le_infNorm (fun i => p ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
      ⟨k, Nat.lt_of_succ_lt_succ hk⟩) (Nat.le_max_right _ _)

theorem cycIntInfNorm_le_iff : ∀ {N : Nat} (p : NegacyclicPolyInt N) (B : Nat),
    cycIntInfNorm p ≤ B ↔ ∀ k : Fin N, (p k).natAbs ≤ B
  | 0, _, _ => ⟨fun _ k => Fin.elim0 k, fun _ => Nat.zero_le _⟩
  | n + 1, p, B => by
    simp only [cycIntInfNorm, Nat.max_le, cycIntInfNorm_le_iff]
    constructor
    · rintro ⟨h0, hRest⟩ ⟨k, hk⟩
      cases k with
      | zero => exact h0
      | succ k' => exact hRest ⟨k', Nat.lt_of_succ_lt_succ hk⟩
    · intro hAll
      exact ⟨hAll ⟨0, Nat.zero_lt_succ n⟩, fun i => hAll ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩⟩

theorem cycIntInfNorm_neg {N : Nat} (p : NegacyclicPolyInt N) :
    cycIntInfNorm (cycIntNeg p) = cycIntInfNorm p := by
  have h1 : cycIntInfNorm (cycIntNeg p) ≤ cycIntInfNorm p := by
    rw [cycIntInfNorm_le_iff]; intro k
    unfold cycIntNeg; rw [Int.natAbs_neg]; exact cycCoeff_natAbs_le_infNorm p k
  have h2 : cycIntInfNorm p ≤ cycIntInfNorm (cycIntNeg p) := by
    rw [cycIntInfNorm_le_iff]; intro k
    have hc := cycCoeff_natAbs_le_infNorm (cycIntNeg p) k
    unfold cycIntNeg at hc; rw [Int.natAbs_neg] at hc; exact hc
  omega

theorem cycIntL1Norm_neg {N : Nat} (p : NegacyclicPolyInt N) :
    cycIntL1Norm (cycIntNeg p) = cycIntL1Norm p := by
  unfold cycIntL1Norm cycIntNeg
  apply cycNatFinSum_congr; intro i; exact Int.natAbs_neg (p i)

theorem cycIntSupportWeight_neg {N : Nat} (p : NegacyclicPolyInt N) :
    cycIntSupportWeight (cycIntNeg p) = cycIntSupportWeight p := by
  unfold cycIntSupportWeight cycIntNeg
  apply cycNatFinSum_congr; intro i
  by_cases hz : p i = 0
  · simp [hz]
  · have hnz : -p i ≠ 0 := by omega
    simp [hz, hnz]

theorem cycIntInfNorm_sub_le {N : Nat} (p r : NegacyclicPolyInt N) :
    cycIntInfNorm (cycIntSub p r) ≤ cycIntInfNorm p + cycIntInfNorm r := by
  rw [cycIntInfNorm_le_iff]
  intro k
  unfold cycIntSub
  have hp := cycCoeff_natAbs_le_infNorm p k
  have hr := cycCoeff_natAbs_le_infNorm r k
  omega

/-- **Exact Negacyclic $\ell_1$-$\ell_\infty$ Convolution Inequality (`cycIntInfNorm_mul_le`)**:
    $\|a \circledast b\|_\infty \le \|a\|_1 \cdot \|b\|_\infty$ in $\mathbb{Z}[X]/(X^N + 1)$. -/
theorem cycIntInfNorm_mul_le {N : Nat} (a b : NegacyclicPolyInt N) :
    cycIntInfNorm (cycIntMul a b) ≤ cycIntL1Norm a * cycIntInfNorm b := by
  rw [cycIntInfNorm_le_iff]
  intro k
  rw [cycIntMul_eq_single]
  unfold cycIntMulSingle
  let term : Fin N → Int := fun i =>
    if h : i.val ≤ k.val then a i * b ⟨k.val - i.val, by omega⟩
    else -(a i * b ⟨N + k.val - i.val, by omega⟩)
  change (cycIntFinSum N term).natAbs ≤ cycIntL1Norm a * cycIntInfNorm b
  have hSumAbs := cycIntFinSum_natAbs_le term
  have hTermBound : ∀ i : Fin N, (term i).natAbs ≤ (a i).natAbs * cycIntInfNorm b := by
    intro i; dsimp only [term]
    by_cases hik : i.val ≤ k.val
    · simp only [hik, ↓reduceDIte, Int.natAbs_mul]
      exact Nat.mul_le_mul_left _ (cycCoeff_natAbs_le_infNorm b _)
    · simp only [hik, ↓reduceDIte, Int.natAbs_neg, Int.natAbs_mul]
      exact Nat.mul_le_mul_left _ (cycCoeff_natAbs_le_infNorm b _)
  have h2 := cycNatFinSum_le hTermBound
  rw [cycNatFinSum_mul_right] at h2
  exact Nat.le_trans hSumAbs h2

/-! ### 1.3 Quotient Ring $R_q = \mathbb{Z}_q[X]/(X^N + 1)$ (`NegacyclicPolyZq`, `CycPolyZq`) -/

/-- Degree-$< N$ polynomial over $\mathbb{Z}_q$ representing an element of $\mathbb{Z}_q[X]/(X^N + 1)$. -/
abbrev NegacyclicPolyZq (N q : Nat) := Fin N → ModZq q

/-- Power-of-two cyclotomic quotient ring $R_q = \mathbb{Z}_q[X]/(X^{2^\nu} + 1)$. -/
abbrev CycPolyZq (nu q : Nat) := NegacyclicPolyZq (2 ^ nu) q

/-- Coefficient-wise projection $\mathbb{Z}[X]/(X^N + 1) \to \mathbb{Z}_q[X]/(X^N + 1)$. -/
@[expose] def cycIntToZq {N : Nat} (q : Nat) [NeZero q] (p : NegacyclicPolyInt N) : NegacyclicPolyZq N q :=
  fun k => ModZq.ofInt q (p k)

def cycZqToNatInt {N q : Nat} (p : NegacyclicPolyZq N q) : NegacyclicPolyInt N :=
  fun k => ((p k).val : Int)

def cycZqCentered {N q : Nat} (p : NegacyclicPolyZq N q) : NegacyclicPolyInt N :=
  fun k => (p k).centered

@[simp] theorem cycIntToZq_toNatInt {N q : Nat} [NeZero q] (p : NegacyclicPolyZq N q) :
    cycIntToZq q (cycZqToNatInt p) = p := by
  funext k; exact ModZq.ofInt_natVal (p k)

@[simp] theorem cycIntToZq_centered {N q : Nat} [NeZero q] (p : NegacyclicPolyZq N q) :
    cycIntToZq q (cycZqCentered p) = p := by
  funext k; exact ModZq.ofInt_centered (p k)

def cycZqZero {N q : Nat} [NeZero q] : NegacyclicPolyZq N q := fun _ => ModZq.zero q
def cycZqOne {N q : Nat} [NeZero q] : NegacyclicPolyZq N q :=
  fun k => if k.val = 0 then ModZq.one q else ModZq.zero q
def cycZqAdd {N q : Nat} [NeZero q] (a b : NegacyclicPolyZq N q) : NegacyclicPolyZq N q :=
  fun k => ModZq.add (a k) (b k)
def cycZqSub {N q : Nat} [NeZero q] (a b : NegacyclicPolyZq N q) : NegacyclicPolyZq N q :=
  fun k => ModZq.sub (a k) (b k)
def cycZqNeg {N q : Nat} [NeZero q] (a : NegacyclicPolyZq N q) : NegacyclicPolyZq N q :=
  fun k => ModZq.neg (a k)
def cycZqScale {N q : Nat} [NeZero q] (c : Int) (a : NegacyclicPolyZq N q) : NegacyclicPolyZq N q :=
  fun k => ModZq.mul (ModZq.ofInt q c) (a k)

/-- Negacyclic polynomial multiplication in $\mathbb{Z}_q[X]/(X^N + 1)$. -/
def cycZqMul {N q : Nat} [NeZero q] (a b : NegacyclicPolyZq N q) : NegacyclicPolyZq N q :=
  cycIntToZq q (cycIntMul (cycZqToNatInt a) (cycZqToNatInt b))

theorem cycIntToZq_zero {N : Nat} (q : Nat) [NeZero q] :
    cycIntToZq q (@cycIntZero N) = cycZqZero := by
  funext _; exact ModZq.ofInt_zero q

theorem cycIntToZq_one {N : Nat} (q : Nat) [NeZero q] :
    cycIntToZq q (@cycIntOne N) = cycZqOne := by
  funext k; unfold cycIntToZq cycIntOne cycZqOne
  split
  · exact ModZq.ofInt_one q
  · exact ModZq.ofInt_zero q

theorem cycIntToZq_add {N : Nat} (q : Nat) [NeZero q] (a b : NegacyclicPolyInt N) :
    cycIntToZq q (cycIntAdd a b) = cycZqAdd (cycIntToZq q a) (cycIntToZq q b) := by
  funext k; exact ModZq.ofInt_add q (a k) (b k)

theorem cycIntToZq_sub {N : Nat} (q : Nat) [NeZero q] (a b : NegacyclicPolyInt N) :
    cycIntToZq q (cycIntSub a b) = cycZqSub (cycIntToZq q a) (cycIntToZq q b) := by
  funext k; exact ModZq.ofInt_sub q (a k) (b k)

theorem cycIntToZq_neg {N : Nat} (q : Nat) [NeZero q] (a : NegacyclicPolyInt N) :
    cycIntToZq q (cycIntNeg a) = cycZqNeg (cycIntToZq q a) := by
  funext k; exact ModZq.ofInt_neg q (a k)

theorem cycIntToZq_scale {N : Nat} (q : Nat) [NeZero q] (c : Int) (a : NegacyclicPolyInt N) :
    cycIntToZq q (cycIntScale c a) = cycZqScale c (cycIntToZq q a) := by
  funext k; exact ModZq.ofInt_mul q c (a k)

private theorem ofInt_cycNegacyclicKernel (q : Nat) [NeZero q] (N k i j : Nat) (x y : Int) :
    ModZq.ofInt q (cycNegacyclicKernel N k i j (x * y)) =
    ModZq.ofInt q (cycNegacyclicKernel N k i j
      (((ModZq.ofInt q x).val : Int) * ((ModZq.ofInt q y).val : Int))) := by
  unfold cycNegacyclicKernel
  split
  · rw [ModZq.ofInt_mul, ModZq.ofInt_mul, ModZq.ofInt_natVal, ModZq.ofInt_natVal]
  · split
    · rw [ModZq.ofInt_neg, ModZq.ofInt_neg, ModZq.ofInt_mul, ModZq.ofInt_mul,
          ModZq.ofInt_natVal, ModZq.ofInt_natVal]
    · rfl

/-- **Surjective Negacyclic Ring Homomorphism (`cycIntToZq_mul`)**:
    Integer negacyclic multiplication projects homomorphically to $\mathbb{Z}_q[X]/(X^N + 1)$. -/
theorem cycIntToZq_mul {N : Nat} (q : Nat) [NeZero q] (a b : NegacyclicPolyInt N) :
    cycIntToZq q (cycIntMul a b) = cycZqMul (cycIntToZq q a) (cycIntToZq q b) := by
  funext k
  change ModZq.ofInt q (cycIntMul a b k) =
    ModZq.ofInt q (cycIntMul (cycZqToNatInt (cycIntToZq q a)) (cycZqToNatInt (cycIntToZq q b)) k)
  unfold cycIntMul
  rw [cycIntFinSum_ofInt_hom q, cycIntFinSum_ofInt_hom q]
  apply cycModZqFinSum_congr; intro i
  rw [cycIntFinSum_ofInt_hom q, cycIntFinSum_ofInt_hom q]
  apply cycModZqFinSum_congr; intro j
  exact ofInt_cycNegacyclicKernel q N k.val i.val j.val (a i) (b j)

theorem cycZqMul_comm {N q : Nat} [NeZero q] (a b : NegacyclicPolyZq N q) :
    cycZqMul a b = cycZqMul b a := by
  rw [← cycIntToZq_toNatInt a, ← cycIntToZq_toNatInt b,
      ← cycIntToZq_mul, ← cycIntToZq_mul, cycIntMul_comm]

theorem cycZqMul_assoc {N q : Nat} [NeZero q] (a b c : NegacyclicPolyZq N q) :
    cycZqMul (cycZqMul a b) c = cycZqMul a (cycZqMul b c) := by
  rw [← cycIntToZq_toNatInt a, ← cycIntToZq_toNatInt b, ← cycIntToZq_toNatInt c]
  simp only [← cycIntToZq_mul, cycIntMul_assoc]

theorem cycZqMul_one_left {N q : Nat} [NeZero q] (hN : 0 < N) (a : NegacyclicPolyZq N q) :
    cycZqMul cycZqOne a = a := by
  rw [← cycIntToZq_one q, ← cycIntToZq_toNatInt a, ← cycIntToZq_mul,
      cycIntMul_one_left hN, cycIntToZq_toNatInt]

theorem cycZqMul_one_right {N q : Nat} [NeZero q] (hN : 0 < N) (a : NegacyclicPolyZq N q) :
    cycZqMul a cycZqOne = a := by
  rw [cycZqMul_comm, cycZqMul_one_left hN]

theorem cycZqMul_left_distrib {N q : Nat} [NeZero q] (a b c : NegacyclicPolyZq N q) :
    cycZqMul a (cycZqAdd b c) = cycZqAdd (cycZqMul a b) (cycZqMul a c) := by
  rw [← cycIntToZq_toNatInt a, ← cycIntToZq_toNatInt b, ← cycIntToZq_toNatInt c,
      ← cycIntToZq_add, ← cycIntToZq_mul, cycIntMul_left_distrib,
      cycIntToZq_add, cycIntToZq_mul, cycIntToZq_mul]

theorem cycZqMul_right_distrib {N q : Nat} [NeZero q] (a b c : NegacyclicPolyZq N q) :
    cycZqMul (cycZqAdd a b) c = cycZqAdd (cycZqMul a c) (cycZqMul b c) := by
  rw [cycZqMul_comm, cycZqMul_left_distrib, cycZqMul_comm c a, cycZqMul_comm c b]

theorem cycZqMul_sub_right {N q : Nat} [NeZero q] (a b c : NegacyclicPolyZq N q) :
    cycZqMul a (cycZqSub b c) = cycZqSub (cycZqMul a b) (cycZqMul a c) := by
  rw [← cycIntToZq_toNatInt a, ← cycIntToZq_toNatInt b, ← cycIntToZq_toNatInt c,
      ← cycIntToZq_sub, ← cycIntToZq_mul, cycIntMul_sub_right,
      cycIntToZq_sub, cycIntToZq_mul, cycIntToZq_mul]

theorem cycZqMul_sub_left {N q : Nat} [NeZero q] (a b c : NegacyclicPolyZq N q) :
    cycZqMul (cycZqSub a b) c = cycZqSub (cycZqMul a c) (cycZqMul b c) := by
  rw [cycZqMul_comm, cycZqMul_sub_right, cycZqMul_comm c a, cycZqMul_comm c b]

theorem cycZqMul_zero_right {N q : Nat} [NeZero q] (a : NegacyclicPolyZq N q) :
    cycZqMul a cycZqZero = cycZqZero := by
  rw [← cycIntToZq_toNatInt a, ← cycIntToZq_zero q, ← cycIntToZq_mul,
      cycIntMul_zero_right, cycIntToZq_zero]

theorem cycZqMul_zero_left {N q : Nat} [NeZero q] (a : NegacyclicPolyZq N q) :
    cycZqMul cycZqZero a = cycZqZero := by
  rw [cycZqMul_comm, cycZqMul_zero_right]

theorem cycZqSub_self {N q : Nat} [NeZero q] (a : NegacyclicPolyZq N q) :
    cycZqSub a a = cycZqZero := by
  rw [← cycIntToZq_toNatInt a, ← cycIntToZq_sub]
  have hZero : cycIntSub (cycZqToNatInt a) (cycZqToNatInt a) = cycIntZero := by
    funext k; dsimp only [cycIntSub, cycIntZero]; omega
  rw [hZero, cycIntToZq_zero]

theorem cycZqScale_add {N q : Nat} [NeZero q] (c : Int) (a b : NegacyclicPolyZq N q) :
    cycZqScale c (cycZqAdd a b) = cycZqAdd (cycZqScale c a) (cycZqScale c b) := by
  rw [← cycIntToZq_toNatInt a, ← cycIntToZq_toNatInt b,
      ← cycIntToZq_add, ← cycIntToZq_scale, ← cycIntToZq_scale, ← cycIntToZq_scale,
      ← cycIntToZq_add]
  congr 1; funext k; dsimp only [cycIntScale, cycIntAdd]; exact Int.mul_add c _ _

theorem cycZqScale_scale {N q : Nat} [NeZero q] (c1 c2 : Int) (a : NegacyclicPolyZq N q) :
    cycZqScale c1 (cycZqScale c2 a) = cycZqScale (c1 * c2) a := by
  rw [← cycIntToZq_toNatInt a, ← cycIntToZq_scale, ← cycIntToZq_scale, ← cycIntToZq_scale]
  congr 1; funext k; dsimp only [cycIntScale]; exact (Int.mul_assoc c1 c2 _).symm

/-- Decidable universal quantifier over `Fin n` (choice-free). -/
def cycAllFin : (n : Nat) → (Fin n → Bool) → Bool
  | 0, _ => true
  | n + 1, p => p ⟨0, Nat.zero_lt_succ n⟩ && cycAllFin n (fun i => p ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)

theorem cycAllFin_eq_true_iff : ∀ {n : Nat} (p : Fin n → Bool),
    cycAllFin n p = true ↔ ∀ i : Fin n, p i = true
  | 0, _ => ⟨fun _ i => Fin.elim0 i, fun _ => rfl⟩
  | n + 1, p => by
    simp only [cycAllFin, Bool.and_eq_true, cycAllFin_eq_true_iff]
    constructor
    · rintro ⟨h0, hRest⟩ ⟨k, hk⟩
      cases k with
      | zero => exact h0
      | succ k' => exact hRest ⟨k', Nat.lt_of_succ_lt_succ hk⟩
    · intro hAll
      exact ⟨hAll ⟨0, Nat.zero_lt_succ n⟩, fun i => hAll ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩⟩

/-- Constructive boolean equality on `NegacyclicPolyZq N q` (choice-free). -/
def cycZqEq {N q : Nat} (a b : NegacyclicPolyZq N q) : Bool :=
  cycAllFin N (fun k => decide (a k = b k))

theorem cycZqEq_iff {N q : Nat} (a b : NegacyclicPolyZq N q) : cycZqEq a b = true ↔ a = b := by
  unfold cycZqEq
  rw [cycAllFin_eq_true_iff]
  constructor
  · intro h; funext k; exact of_decide_eq_true (h k)
  · intro h k; subst h; exact decide_eq_true rfl

/-! ### 1.4 Signed Monomials $\pm X^k$, Negacyclic Signed Powers & $X^{2^\nu} = -1$ -/

/-- Sign bit interpretation (`false ↦ +1`, `true ↦ -1`). -/
def signBitToInt (sign : Bool) : Int :=
  if sign then -1 else 1

private theorem signBitToInt_false : signBitToInt false = 1 := rfl

private theorem signBitToInt_true : signBitToInt true = -1 := rfl

private theorem signBitToInt_natAbs (s : Bool) : (signBitToInt s).natAbs = 1 := by
  cases s <;> rfl

private theorem signBitToInt_mul (s1 s2 : Bool) :
    signBitToInt s1 * signBitToInt s2 = signBitToInt (bne s1 s2) := by
  cases s1 <;> cases s2 <;> rfl

private theorem signBitToInt_neg (s : Bool) :
    -signBitToInt s = signBitToInt (!s) := by
  cases s <;> rfl

/-- Signed monomial $(-1)^{\mathsf{sign}} X^k \in \mathbb{Z}[X]/(X^N + 1)$ for general $N$. -/
def negacyclicSignedMonomial {N : Nat} (sign : Bool) (k : Fin N) : NegacyclicPolyInt N :=
  fun i => if i = k then signBitToInt sign else 0

/-- Concrete signed monomial $(-1)^{\mathsf{sign}} X^k \in \mathbb{Z}[X]/(X^{2^\nu} + 1)$ (`k : Fin (2^nu)`). -/
@[expose] def signedMonomial (nu : Nat) (sign : Bool) (k : Fin (2 ^ nu)) : CycPolyInt nu :=
  negacyclicSignedMonomial sign k

/-- Challenge index pair `(sign, deg)` parameterizing the $2 \cdot 2^\nu$-element signed-monomial challenge set. -/
structure SignedMonomialChal (nu : Nat) where
  sign : Bool
  deg : Fin (2 ^ nu)
  deriving DecidableEq, Repr

/-- Realize a signed-monomial challenge as an integer polynomial in $\mathbb{Z}[X]/(X^{2^\nu} + 1)$. -/
def SignedMonomialChal.toIntPoly {nu : Nat} (c : SignedMonomialChal nu) : CycPolyInt nu :=
  signedMonomial nu c.sign c.deg

/-- Realize a signed-monomial challenge in $R_q = \mathbb{Z}_q[X]/(X^{2^\nu} + 1)$. -/
def SignedMonomialChal.toZqPoly {nu : Nat} (q : Nat) [NeZero q] (c : SignedMonomialChal nu) :
    CycPolyZq nu q :=
  cycIntToZq q c.toIntPoly

/-- Exact bijection between `SignedMonomialChal nu` and `Fin (2 * 2 ^ nu)` (`2048` elements at $\nu = 10$). -/
def SignedMonomialChal.toFinIndex {nu : Nat} (c : SignedMonomialChal nu) : Fin (2 * 2 ^ nu) :=
  ⟨(if c.sign then 2 ^ nu else 0) + c.deg.val, by
    have hd := c.deg.isLt
    cases c.sign <;> simp <;> omega⟩

def SignedMonomialChal.ofFinIndex {nu : Nat} (idx : Fin (2 * 2 ^ nu)) : SignedMonomialChal nu where
  sign := decide (2 ^ nu ≤ idx.val)
  deg := ⟨idx.val % (2 ^ nu), Nat.mod_lt _ (Nat.two_pow_pos nu)⟩

theorem SignedMonomialChal.ext {nu : Nat} {a b : SignedMonomialChal nu}
    (hs : a.sign = b.sign) (hd : a.deg.val = b.deg.val) : a = b := by
  cases a; cases b
  dsimp only at hs hd
  subst hs
  congr 1
  exact Fin.ext hd

theorem SignedMonomialChal.ofFinIndex_toFinIndex {nu : Nat} (c : SignedMonomialChal nu) :
    SignedMonomialChal.ofFinIndex c.toFinIndex = c := by
  rcases c with ⟨s, ⟨k, hk⟩⟩
  apply SignedMonomialChal.ext
  · unfold toFinIndex ofFinIndex
    cases s
    · change decide (2 ^ nu ≤ 0 + k) = false
      exact decide_eq_false (by omega)
    · change decide (2 ^ nu ≤ 2 ^ nu + k) = true
      exact decide_eq_true (by omega)
  · unfold toFinIndex ofFinIndex
    cases s
    · change (0 + k) % 2 ^ nu = k
      rw [Nat.zero_add]; exact Nat.mod_eq_of_lt hk
    · change (2 ^ nu + k) % 2 ^ nu = k
      have hEq : 2 ^ nu + k = k + 2 ^ nu * 1 := by omega
      rw [hEq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]

theorem SignedMonomialChal.toFinIndex_ofFinIndex {nu : Nat} (idx : Fin (2 * 2 ^ nu)) :
    (SignedMonomialChal.ofFinIndex idx).toFinIndex = idx := by
  rcases idx with ⟨v, hv⟩
  apply Fin.ext
  unfold toFinIndex ofFinIndex
  dsimp only
  by_cases hGe : 2 ^ nu ≤ v
  · simp only [hGe, decide_true, ↓reduceIte]
    have hSubLt : v - 2 ^ nu < 2 ^ nu := by omega
    have hEq : v = (v - 2 ^ nu) + 2 ^ nu * 1 := by omega
    have hMod : v % 2 ^ nu = v - 2 ^ nu := by
      conv => lhs; rw [hEq]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hSubLt]
    omega
  · simp only [hGe, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
    exact Nat.mod_eq_of_lt (by omega)

theorem signedMonomial_injective {nu : Nat} {s1 s2 : Bool} {k1 k2 : Fin (2 ^ nu)}
    (hEq : signedMonomial nu s1 k1 = signedMonomial nu s2 k2) :
    s1 = s2 ∧ k1 = k2 := by
  have hAt1 := congrFun hEq k1
  unfold signedMonomial negacyclicSignedMonomial at hAt1
  simp only [↓reduceIte] at hAt1
  by_cases hk : k1 = k2
  · subst hk
    simp only [↓reduceIte] at hAt1
    refine ⟨?_, rfl⟩
    cases s1 <;> cases s2
    · rfl
    · exfalso; rw [signBitToInt_false, signBitToInt_true] at hAt1; omega
    · exfalso; rw [signBitToInt_true, signBitToInt_false] at hAt1; omega
    · rfl
  · simp only [hk, ↓reduceIte] at hAt1
    exfalso
    cases s1
    · rw [signBitToInt_false] at hAt1; omega
    · rw [signBitToInt_true] at hAt1; omega

/-- For every modulus $q \ge 3$, all $2 \cdot 2^\nu$ signed monomials project to pairwise distinct elements of $R_q$. -/
theorem signedMonomial_toZq_injective {nu q : Nat} [NeZero q] (hq3 : 3 ≤ q)
    {c1 c2 : SignedMonomialChal nu}
    (hEq : c1.toZqPoly q = c2.toZqPoly q) : c1 = c2 := by
  rcases c1 with ⟨s1, k1⟩
  rcases c2 with ⟨s2, k2⟩
  have hAt1 := congrFun hEq k1
  unfold SignedMonomialChal.toZqPoly SignedMonomialChal.toIntPoly signedMonomial
    negacyclicSignedMonomial cycIntToZq at hAt1
  simp only [↓reduceIte] at hAt1
  have hMod1 : (1 : Int) % (q : Int) = 1 := Int.emod_eq_of_lt (by omega) (by omega)
  have hModNeg1 : (-1 : Int) % (q : Int) = (q : Int) - 1 := by
    have hEq1 : (-1 : Int) = ((q : Int) - 1) + (-1) * (q : Int) := by omega
    conv => lhs; rw [hEq1]
    rw [Int.add_mul_emod_self_right]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  by_cases hk : k1 = k2
  · subst hk
    simp only [↓reduceIte] at hAt1
    have hs : s1 = s2 := by
      cases s1 <;> cases s2
      · rfl
      · exfalso
        rw [signBitToInt_false, signBitToInt_true] at hAt1
        have hv1 := ModZq.ofInt_val_int q 1
        have hv2 := ModZq.ofInt_val_int q (-1)
        rw [hAt1, hMod1] at hv1
        rw [hModNeg1] at hv2
        omega
      · exfalso
        rw [signBitToInt_true, signBitToInt_false] at hAt1
        have hv1 := ModZq.ofInt_val_int q (-1)
        have hv2 := ModZq.ofInt_val_int q 1
        rw [hAt1, hModNeg1] at hv1
        rw [hMod1] at hv2
        omega
      · rfl
    subst hs; rfl
  · simp only [hk, ↓reduceIte] at hAt1
    exfalso
    have hv0 := ModZq.ofInt_val_int q 0
    simp only [Int.zero_emod] at hv0
    cases s1
    · rw [signBitToInt_false] at hAt1
      have hv1 := ModZq.ofInt_val_int q 1
      rw [hAt1, hMod1] at hv1
      omega
    · rw [signBitToInt_true] at hAt1
      have hv1 := ModZq.ofInt_val_int q (-1)
      rw [hAt1, hModNeg1] at hv1
      omega

/-- Arbitrary-exponent negacyclic signed power $(-1)^s X^e = (-1)^{s \oplus ((e/N) \bmod 2)} X^{e \bmod N}$
    in $\mathbb{Z}[X]/(X^N + 1)$. -/
def cycSignedPow {N : Nat} (hN : 0 < N) (s : Bool) (e : Nat) : NegacyclicPolyInt N :=
  negacyclicSignedMonomial (bne s (decide ((e / N) % 2 = 1))) ⟨e % N, Nat.mod_lt e hN⟩

private theorem cycSignedPow_of_lt {N : Nat} (hN : 0 < N) (s : Bool) {e : Nat} (he : e < N) :
    cycSignedPow hN s e = negacyclicSignedMonomial s ⟨e, he⟩ := by
  unfold cycSignedPow
  have hDiv : e / N = 0 := Nat.div_eq_of_lt he
  have hMod : e % N = e := Nat.mod_eq_of_lt he
  simp only [hDiv, Nat.zero_mod, Nat.zero_ne_one, decide_false, Bool.bne_false]
  congr 1
  exact Fin.ext hMod

private theorem cycSignedPow_zero {N : Nat} (hN : 0 < N) :
    cycSignedPow hN false 0 = cycIntOne := by
  rw [cycSignedPow_of_lt hN false hN]
  funext k; unfold negacyclicSignedMonomial cycIntOne signBitToInt
  by_cases hk : k.val = 0
  · have hkeq : k = ⟨0, hN⟩ := Fin.ext hk
    simp [hkeq]
  · have hkne : k ≠ ⟨0, hN⟩ := fun h => hk (congrArg Fin.val h)
    simp [hkne, hk]

theorem negacyclicSignedMonomial_mul {N : Nat} (hN : 0 < N)
    (s1 s2 : Bool) (k1 k2 : Fin N) :
    cycIntMul (negacyclicSignedMonomial s1 k1) (negacyclicSignedMonomial s2 k2) =
      if h : k1.val + k2.val < N then
        negacyclicSignedMonomial (bne s1 s2) ⟨k1.val + k2.val, h⟩
      else
        negacyclicSignedMonomial (!(bne s1 s2)) ⟨k1.val + k2.val - N, by omega⟩ := by
  have _ := hN
  rw [cycIntMul_eq_single]
  funext k
  unfold cycIntMulSingle
  rw [cycIntFinSum_eq_single k1]
  · have hk1 := k1.isLt; have hk2 := k2.isLt; have hk := k.isLt
    by_cases hSum : k1.val + k2.val < N
    · simp only [hSum, ↓reduceDIte]
      by_cases hLe : k1.val ≤ k.val
      · simp only [hLe, ↓reduceDIte, negacyclicSignedMonomial, ↓reduceIte]
        by_cases hEqK : k.val = k1.val + k2.val
        · have hSubEq : (⟨k.val - k1.val, by omega⟩ : Fin N) = k2 := Fin.ext (by dsimp; omega)
          have hkEq : k = ⟨k1.val + k2.val, hSum⟩ := Fin.ext hEqK
          rw [hSubEq, hkEq]
          simp only [↓reduceIte, signBitToInt_mul]
        · have hSubNe : (⟨k.val - k1.val, by omega⟩ : Fin N) ≠ k2 := fun h => by
            have hv := congrArg Fin.val h; dsimp at hv; omega
          have hkNe : k ≠ ⟨k1.val + k2.val, hSum⟩ := fun h => hEqK (congrArg Fin.val h)
          simp only [hSubNe, hkNe, ↓reduceIte, Int.mul_zero]
      · simp only [hLe, ↓reduceDIte, negacyclicSignedMonomial, ↓reduceIte]
        have hSubNe : (⟨N + k.val - k1.val, by omega⟩ : Fin N) ≠ k2 := fun h => by
          have hv := congrArg Fin.val h; dsimp at hv; omega
        have hkNe : k ≠ ⟨k1.val + k2.val, hSum⟩ := fun h => by
          have hv := congrArg Fin.val h; dsimp at hv; omega
        simp only [hSubNe, hkNe, ↓reduceIte, Int.mul_zero, Int.neg_zero]
    · simp only [hSum, ↓reduceDIte]
      by_cases hLe : k1.val ≤ k.val
      · simp only [hLe, ↓reduceDIte, negacyclicSignedMonomial, ↓reduceIte]
        have hSubNe : (⟨k.val - k1.val, by omega⟩ : Fin N) ≠ k2 := fun h => by
          have hv := congrArg Fin.val h; dsimp at hv; omega
        have hkNe : k ≠ ⟨k1.val + k2.val - N, by omega⟩ := fun h => by
          have hv := congrArg Fin.val h; dsimp at hv; omega
        simp only [hSubNe, hkNe, ↓reduceIte, Int.mul_zero]
      · simp only [hLe, ↓reduceDIte, negacyclicSignedMonomial, ↓reduceIte]
        by_cases hEqK : k.val = k1.val + k2.val - N
        · have hSubEq : (⟨N + k.val - k1.val, by omega⟩ : Fin N) = k2 := Fin.ext (by dsimp; omega)
          have hkEq : k = ⟨k1.val + k2.val - N, by omega⟩ := Fin.ext hEqK
          rw [hSubEq, hkEq]
          simp only [↓reduceIte, signBitToInt_mul, signBitToInt_neg]
        · have hSubNe : (⟨N + k.val - k1.val, by omega⟩ : Fin N) ≠ k2 := fun h => by
            have hv := congrArg Fin.val h; dsimp at hv; omega
          have hkNe : k ≠ ⟨k1.val + k2.val - N, by omega⟩ := fun h => hEqK (congrArg Fin.val h)
          simp only [hSubNe, hkNe, ↓reduceIte, Int.mul_zero, Int.neg_zero]
  · intro i hiNe
    by_cases hik : i.val ≤ k.val
    · simp only [hik, ↓reduceDIte, negacyclicSignedMonomial, hiNe, ↓reduceIte, Int.zero_mul]
    · simp only [hik, ↓reduceDIte, negacyclicSignedMonomial, hiNe, ↓reduceIte, Int.zero_mul, Int.neg_zero]

private theorem div_mod_of_eq_add_mul {x r q N : Nat} (hr : r < N) (hx : x = r + N * q) :
    x / N = q ∧ x % N = r := by
  have hN : 0 < N := by omega
  subst hx
  refine ⟨?_, ?_⟩
  · rw [Nat.add_mul_div_left r q hN, Nat.div_eq_of_lt hr, Nat.zero_add]
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]

private theorem parity_add_bool (a b : Nat) :
    decide ((a + b) % 2 = 1) = bne (decide (a % 2 = 1)) (decide (b % 2 = 1)) := by
  by_cases ha : a % 2 = 1 <;> by_cases hb : b % 2 = 1
  · have hSum : (a + b) % 2 = 0 := by omega
    simp [ha, hb, hSum]
  · have hSum : (a + b) % 2 = 1 := by omega
    simp [ha, hb, hSum]
  · have hSum : (a + b) % 2 = 1 := by omega
    simp [ha, hb, hSum]
  · have hSum : (a + b) % 2 = 0 := by omega
    simp [ha, hb, hSum]

/-- **Unified Negacyclic Signed-Power Law (`cycSignedPow_mul`)**:
    $(-1)^{s_1} X^{e_1} \circledast (-1)^{s_2} X^{e_2} = (-1)^{s_1 \oplus s_2} X^{e_1 + e_2}$ in $\mathbb{Z}[X]/(X^N + 1)$. -/
theorem cycSignedPow_mul {N : Nat} (hN : 0 < N) (s1 s2 : Bool) (e1 e2 : Nat) :
    cycIntMul (cycSignedPow hN s1 e1) (cycSignedPow hN s2 e2) =
      cycSignedPow hN (bne s1 s2) (e1 + e2) := by
  unfold cycSignedPow
  rw [negacyclicSignedMonomial_mul hN]
  let q1 := e1 / N; let r1 := e1 % N
  let q2 := e2 / N; let r2 := e2 % N
  have hd1 : N * q1 + r1 = e1 := Nat.div_add_mod e1 N
  have hr1 : r1 < N := Nat.mod_lt e1 hN
  have hd2 : N * q2 + r2 = e2 := Nat.div_add_mod e2 N
  have hr2 : r2 < N := Nat.mod_lt e2 hN
  by_cases hSum : r1 + r2 < N
  · simp only [r1, r2] at hSum
    simp only [hSum, ↓reduceDIte]
    have hEq : e1 + e2 = (e1 % N + e2 % N) + N * (q1 + q2) := by
      have hMul : N * (q1 + q2) = N * q1 + N * q2 := Nat.mul_add N q1 q2
      omega
    obtain ⟨hDiv, hMod⟩ := div_mod_of_eq_add_mul hSum hEq
    rw [hDiv, parity_add_bool q1 q2]
    have hSign : bne (bne s1 (decide (q1 % 2 = 1))) (bne s2 (decide (q2 % 2 = 1))) =
        bne (bne s1 s2) (bne (decide (q1 % 2 = 1)) (decide (q2 % 2 = 1))) := by
      cases s1 <;> cases s2 <;> cases (decide (q1 % 2 = 1)) <;> cases (decide (q2 % 2 = 1)) <;> rfl
    rw [hSign]
    congr 1
    exact Fin.ext hMod.symm
  · simp only [r1, r2] at hSum
    simp only [hSum, ↓reduceDIte]
    have hSubLt : e1 % N + e2 % N - N < N := by omega
    have hEq : e1 + e2 = (e1 % N + e2 % N - N) + N * (q1 + q2 + 1) := by
      have hMul1 : N * (q1 + q2 + 1) = N * q1 + N * q2 + N := by
        rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
      omega
    obtain ⟨hDiv, hMod⟩ := div_mod_of_eq_add_mul hSubLt hEq
    rw [hDiv, parity_add_bool (q1 + q2) 1, parity_add_bool q1 q2]
    have hOneOdd : decide (1 % 2 = 1) = true := rfl
    rw [hOneOdd]
    have hSign : Bool.not (bne (bne s1 (decide (q1 % 2 = 1))) (bne s2 (decide (q2 % 2 = 1)))) =
        bne (bne s1 s2) (bne (bne (decide (q1 % 2 = 1)) (decide (q2 % 2 = 1))) true) := by
      cases s1 <;> cases s2 <;> cases (decide (q1 % 2 = 1)) <;> cases (decide (q2 % 2 = 1)) <;> rfl
    rw [hSign]
    congr 1
    exact Fin.ext hMod.symm

private theorem cycSignedPow_mul_N {N : Nat} (hN : 0 < N) (s : Bool) (u : Nat) :
    cycSignedPow hN s (u * N) =
      negacyclicSignedMonomial (bne s (decide (u % 2 = 1))) ⟨0, hN⟩ := by
  unfold cycSignedPow
  have hDiv : (u * N) / N = u := Nat.mul_div_cancel u hN
  have hMod : (u * N) % N = 0 := Nat.mul_mod_left u N
  rw [hDiv]
  congr 1
  exact Fin.ext hMod

/-- Iterated polynomial power $p^j$ in $\mathbb{Z}[X]/(X^N + 1)$. -/
def cycPolyPow {N : Nat} (p : NegacyclicPolyInt N) : Nat → NegacyclicPolyInt N
  | 0 => cycIntOne
  | j + 1 => cycIntMul (cycPolyPow p j) p

theorem cycPolyPow_cycSignedPow {N : Nat} (hN : 0 < N) (s : Bool) (d : Nat) :
    ∀ j : Nat, cycPolyPow (cycSignedPow hN s d) j =
      cycSignedPow hN (decide (j % 2 = 1) && s) (j * d)
  | 0 => by
    simp only [cycPolyPow, Nat.zero_mod, Nat.zero_ne_one, decide_false, Bool.false_and, Nat.zero_mul]
    exact (cycSignedPow_zero hN).symm
  | j + 1 => by
    simp only [cycPolyPow, cycPolyPow_cycSignedPow hN s d j, cycSignedPow_mul hN]
    have hMul : j * d + d = (j + 1) * d := (Nat.succ_mul j d).symm
    rw [hMul, parity_add_bool j 1]
    have hOne : decide (1 % 2 = 1) = true := rfl
    rw [hOne]
    have hBool : bne (decide (j % 2 = 1) && s) s = (bne (decide (j % 2 = 1)) true && s) := by
      cases (decide (j % 2 = 1)) <;> cases s <;> rfl
    rw [hBool]

/-- **Quotient Defining Identity (`cycX_pow_two_pow_eq_neg_one`)**:
    In $\mathbb{Z}[X]/(X^{2^\nu} + 1)$ ($\nu \ge 1$), $X^{2^\nu} = -1$ and $X^{2^\nu} + 1 = 0$. -/
theorem cycX_pow_two_pow_eq_neg_one (nu : Nat) (hNu : 1 ≤ nu) :
    let xPoly : CycPolyInt nu := signedMonomial nu false ⟨1, by
      have : 2 ^ 1 ≤ 2 ^ nu := Nat.pow_le_pow_right (by decide) hNu
      omega⟩
    cycPolyPow xPoly (2 ^ nu) = cycIntNeg cycIntOne ∧
    cycIntAdd (cycPolyPow xPoly (2 ^ nu)) cycIntOne = cycIntZero := by
  intro xPoly
  have hN := Nat.two_pow_pos nu
  have h1Lt : 1 < 2 ^ nu := by
    have : 2 ^ 1 ≤ 2 ^ nu := Nat.pow_le_pow_right (by decide) hNu
    omega
  have hxEq : xPoly = cycSignedPow hN false 1 := (cycSignedPow_of_lt hN false h1Lt).symm
  have hPow : cycPolyPow xPoly (2 ^ nu) = cycIntNeg cycIntOne := by
    rw [hxEq, cycPolyPow_cycSignedPow hN false 1 (2 ^ nu)]
    simp only [Bool.and_false, Nat.mul_one]
    have hMul1 : cycSignedPow hN false (2 ^ nu) = cycSignedPow hN false (1 * 2 ^ nu) := by
      rw [Nat.one_mul]
    rw [hMul1, cycSignedPow_mul_N hN false 1]
    funext k
    dsimp only [negacyclicSignedMonomial, cycIntNeg, cycIntOne, signBitToInt]
    by_cases hk : k.val = 0
    · have hkEq : k = ⟨0, hN⟩ := Fin.ext hk
      simp [hkEq]
    · have hkNe : k ≠ ⟨0, hN⟩ := fun h => hk (congrArg Fin.val h)
      simp [hkNe, hk]
  refine ⟨hPow, ?_⟩
  rw [hPow]
  funext k; dsimp only [cycIntAdd, cycIntNeg, cycIntOne, cycIntZero]; omega


/-! ## 2. Exact Cyclotomic Signed-Monomial Cofactor Theorem & Odd-Modulus Pairwise Invertibility -/

/-- Exact integer multiplicative inverse $(\pm X^k)^{-1}$ in $\mathbb{Z}[X]/(X^N + 1)$ (`±1` at $k = 0$,
    `∓X^{N - k}` at $k > 0$), unified via `cycSignedPow hN (!s) (N - k.val)`. -/
def negacyclicSignedMonomialInv {N : Nat} (hN : 0 < N) (s : Bool) (k : Fin N) : NegacyclicPolyInt N :=
  cycSignedPow hN (!s) (N - k.val)

theorem negacyclicSignedMonomial_mul_inv {N : Nat} (hN : 0 < N) (s : Bool) (k : Fin N) :
    cycIntMul (negacyclicSignedMonomial s k) (negacyclicSignedMonomialInv hN s k) = cycIntOne := by
  unfold negacyclicSignedMonomialInv
  rw [← cycSignedPow_of_lt hN s k.isLt, cycSignedPow_mul hN]
  have hAdd : k.val + (N - k.val) = 1 * N := by have := k.isLt; omega
  have hSign : bne s (!s) = true := by cases s <;> rfl
  rw [hAdd, hSign, cycSignedPow_mul_N hN true 1]
  funext i
  dsimp only [negacyclicSignedMonomial, cycIntOne, signBitToInt]
  by_cases hi : i.val = 0
  · have hiEq : i = ⟨0, hN⟩ := Fin.ext hi
    simp [hiEq]
  · have hiNe : i ≠ ⟨0, hN⟩ := fun h => hi (congrArg Fin.val h)
    simp [hiNe, hi]

/-- Unsigned distance $|a - b|$ on `Nat`. -/
def cycNatDist (a b : Nat) : Nat :=
  if a ≤ b then b - a else a - b

/-- Structural 2-adic factorization `factorTwos fuel d = (a, u)` writing $d = 2^a \cdot u$ with $u$ odd
    whenever $0 < d < 2^{\mathsf{fuel}}$. -/
def factorTwos : Nat → Nat → Nat × Nat
  | 0, d => (0, d)
  | fuel + 1, d =>
    if d % 2 = 0 then
      let res := factorTwos fuel (d / 2)
      (res.1 + 1, res.2)
    else
      (0, d)

theorem factorTwos_spec : ∀ (nu d : Nat), 0 < d → d < 2 ^ nu →
    let res := factorTwos nu d
    d = 2 ^ res.1 * res.2 ∧ res.1 < nu ∧ res.2 % 2 = 1
  | 0, d, hdPos, hdLt => by
    simp only [Nat.pow_zero] at hdLt; omega
  | nu + 1, d, hdPos, hdLt => by
    unfold factorTwos
    by_cases hEven : d % 2 = 0
    · simp only [hEven, ↓reduceIte]
      have hPow : 2 ^ (nu + 1) = 2 * 2 ^ nu := by rw [Nat.pow_succ]; omega
      have hdHalfPos : 0 < d / 2 := by omega
      have hdHalfLt : d / 2 < 2 ^ nu := by omega
      obtain ⟨hEq, haLt, huOdd⟩ := factorTwos_spec nu (d / 2) hdHalfPos hdHalfLt
      refine ⟨?_, by omega, huOdd⟩
      have hTwo : d = 2 * (d / 2) := by omega
      have hPowSucc : 2 ^ ((factorTwos nu (d / 2)).1 + 1) = 2 * 2 ^ (factorTwos nu (d / 2)).1 := by
        rw [Nat.pow_succ]; omega
      rw [hPowSucc, Nat.mul_assoc, ← hEq, ← hTwo]
    · simp only [hEven, ↓reduceIte]
      exact ⟨(Nat.one_mul d).symm, Nat.zero_lt_succ nu, by omega⟩

/-- Geometric sum $\sum_{j=0}^{m-1} r^j$ in $\mathbb{Z}[X]/(X^N + 1)$. -/
def cycGeomSum {N : Nat} (r : NegacyclicPolyInt N) : Nat → NegacyclicPolyInt N
  | 0 => cycIntZero
  | m + 1 => cycIntAdd (cycGeomSum r m) (cycPolyPow r m)

theorem one_sub_mul_cycGeomSum {N : Nat} (hN : 0 < N) (r : NegacyclicPolyInt N) :
    ∀ m : Nat, cycIntMul (cycIntSub cycIntOne r) (cycGeomSum r m) =
      cycIntSub cycIntOne (cycPolyPow r m)
  | 0 => by
    simp only [cycGeomSum, cycPolyPow, cycIntMul_zero_right]
    funext k; dsimp only [cycIntSub, cycIntZero]; omega
  | m + 1 => by
    simp only [cycGeomSum, cycPolyPow]
    rw [cycIntMul_left_distrib, one_sub_mul_cycGeomSum hN r m,
        cycIntMul_sub_left, cycIntMul_one_left hN, cycIntMul_comm r (cycPolyPow r m)]
    funext k; dsimp only [cycIntAdd, cycIntSub]; omega

/-- Support size $m \le 2^\nu$ of the cyclotomic cofactor $g(X)$ for $(c_1, c_2)$:
    $1$ when $k_1 = k_2$, and $m = 2^{\nu - a}$ (always even) when $|k_2 - k_1| = 2^a \cdot u$. -/
def signedMonomialCofactorSupportSize (nu : Nat) (c1 c2 : SignedMonomialChal nu) : Nat :=
  if c1.deg = c2.deg then
    1
  else
    let d := cycNatDist c1.deg.val c2.deg.val
    let a := (factorTwos nu d).1
    2 ^ (nu - a)

/-- Explicit $\{-1, 0, +1\}$-coefficient cyclotomic cofactor $g(X) \in \mathbb{Z}[X]/(X^{2^\nu} + 1)$
    satisfying $(c_1 - c_2) \circledast g(X) = 2$ for every distinct pair $c_1 \ne c_2$. -/
def signedMonomialCofactor (nu : Nat) (c1 c2 : SignedMonomialChal nu) : CycPolyInt nu :=
  let hN := Nat.two_pow_pos nu
  if c1.deg = c2.deg then
    negacyclicSignedMonomialInv hN c1.sign c1.deg
  else
    let d := cycNatDist c1.deg.val c2.deg.val
    let a := (factorTwos nu d).1
    let m := 2 ^ (nu - a)
    if c1.deg.val < c2.deg.val then
      let r := cycSignedPow hN (bne c1.sign c2.sign) d
      cycIntMul (negacyclicSignedMonomialInv hN c1.sign c1.deg) (cycGeomSum r m)
    else
      let r := cycSignedPow hN (bne c2.sign c1.sign) d
      cycIntNeg (cycIntMul (negacyclicSignedMonomialInv hN c2.sign c2.deg) (cycGeomSum r m))

/-- Key coprimality lemma: if $u$ is odd and $2^b \mid x \cdot u$, then $2^b \mid x$. -/
private theorem mod_two_pow_eq_zero_of_mul_odd :
    ∀ (b x u : Nat), u % 2 = 1 → (x * u) % (2 ^ b) = 0 → x % (2 ^ b) = 0
  | 0, x, _, _, _ => Nat.mod_one x
  | b + 1, x, u, huOdd, hMod => by
    have hPow : 2 ^ (b + 1) = 2 * 2 ^ b := by rw [Nat.pow_succ]; omega
    let q := (x * u) / (2 ^ (b + 1))
    have hDivEq : 2 ^ (b + 1) * q + (x * u) % (2 ^ (b + 1)) = x * u :=
      Nat.div_add_mod (x * u) (2 ^ (b + 1))
    rw [hMod, Nat.add_zero, hPow] at hDivEq
    have hxEven : x % 2 = 0 := by
      have hxuMod2 : (x * u) % 2 = 0 := by
        rw [← hDivEq, Nat.mul_assoc, Nat.mul_mod_right]
      have hMulMod : (x * u) % 2 = ((x % 2) * (u % 2)) % 2 := Nat.mul_mod x u 2
      rw [hxuMod2, huOdd] at hMulMod
      omega
    have hxHalf : x = 2 * (x / 2) := by omega
    have hHalfMul : (x / 2) * u = 2 ^ b * q := by
      have hTwoMul : 2 * ((x / 2) * u) = 2 * (2 ^ b * q) := by
        calc 2 * ((x / 2) * u)
          _ = (2 * (x / 2)) * u := (Nat.mul_assoc 2 (x / 2) u).symm
          _ = x * u := by rw [← hxHalf]
          _ = (2 * 2 ^ b) * q := hDivEq.symm
          _ = 2 * (2 ^ b * q) := Nat.mul_assoc 2 (2 ^ b) q
      exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) hTwoMul
    have hHalfMod : ((x / 2) * u) % (2 ^ b) = 0 := by
      rw [hHalfMul, Nat.mul_mod_right]
    have ih := mod_two_pow_eq_zero_of_mul_odd b (x / 2) u huOdd hHalfMod
    let q2 := (x / 2) / (2 ^ b)
    have hHalfDiv : 2 ^ b * q2 + (x / 2) % (2 ^ b) = x / 2 :=
      Nat.div_add_mod (x / 2) (2 ^ b)
    rw [ih, Nat.add_zero] at hHalfDiv
    have hxFull : x = (2 ^ (b + 1)) * q2 := by
      rw [hPow, Nat.mul_assoc, hHalfDiv, ← hxHalf]
    rw [hxFull, Nat.mul_mod_right]

private theorem geom_term_deg_injective {nu a u : Nat} (haLt : a < nu) (huOdd : u % 2 = 1)
    (offset : Nat) {j1 j2 : Fin (2 ^ (nu - a))}
    (hModEq : (offset + j1.val * (2 ^ a * u)) % (2 ^ nu) =
              (offset + j2.val * (2 ^ a * u)) % (2 ^ nu)) :
    j1 = j2 := by
  have hSplitPow : 2 ^ nu = 2 ^ a * 2 ^ (nu - a) := by
    rw [← Nat.pow_add]
    congr 1; omega
  have wlog_lt : ∀ {x y : Nat}, x < y → y < 2 ^ (nu - a) →
      (offset + x * (2 ^ a * u)) % (2 ^ nu) = (offset + y * (2 ^ a * u)) % (2 ^ nu) → False := by
    intro x y hxy hyLt hEq
    let delta := y - x
    have hDeltaPos : 0 < delta := by omega
    have hDeltaLt : delta < 2 ^ (nu - a) := by omega
    have hAdd : offset + y * (2 ^ a * u) = (offset + x * (2 ^ a * u)) + delta * (2 ^ a * u) := by
      have hy : y = x + delta := by omega
      rw [hy, Nat.add_mul, Nat.add_assoc]
    have hDiv1 := Nat.div_add_mod (offset + x * (2 ^ a * u)) (2 ^ nu)
    have hDiv2 := Nat.div_add_mod (offset + y * (2 ^ a * u)) (2 ^ nu)
    rw [← hEq] at hDiv2
    have hLeQuot : (offset + x * (2 ^ a * u)) / (2 ^ nu) ≤ (offset + y * (2 ^ a * u)) / (2 ^ nu) :=
      Nat.div_le_div_right (by omega)
    let qDiff := (offset + y * (2 ^ a * u)) / (2 ^ nu) - (offset + x * (2 ^ a * u)) / (2 ^ nu)
    have hDiffMul : delta * (2 ^ a * u) = (2 ^ nu) * qDiff := by
      have hMulSub : (2 ^ nu) * qDiff =
          (2 ^ nu) * ((offset + y * (2 ^ a * u)) / (2 ^ nu)) -
          (2 ^ nu) * ((offset + x * (2 ^ a * u)) / (2 ^ nu)) := Nat.mul_sub_left_distrib _ _ _
      omega
    have hRearr : 2 ^ a * (delta * u) = 2 ^ a * (2 ^ (nu - a) * qDiff) := by
      calc 2 ^ a * (delta * u)
        _ = delta * (2 ^ a * u) := by
            rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ a) delta, Nat.mul_assoc]
        _ = (2 ^ nu) * qDiff := hDiffMul
        _ = (2 ^ a * 2 ^ (nu - a)) * qDiff := by rw [hSplitPow]
        _ = 2 ^ a * (2 ^ (nu - a) * qDiff) := Nat.mul_assoc _ _ _
    have hCancel := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos a) hRearr
    have hModZero : (delta * u) % (2 ^ (nu - a)) = 0 := by
      rw [hCancel, Nat.mul_mod_right]
    have hDeltaMod := mod_two_pow_eq_zero_of_mul_odd (nu - a) delta u huOdd hModZero
    rw [Nat.mod_eq_of_lt hDeltaLt] at hDeltaMod
    omega
  by_cases h12 : j1.val < j2.val
  · exact False.elim (wlog_lt h12 j2.isLt hModEq)
  · by_cases h21 : j2.val < j1.val
    · exact False.elim (wlog_lt h21 j1.isLt hModEq.symm)
    · exact Fin.ext (by omega)

private theorem cycIntFinSum_succ_last : ∀ (n : Nat) (f : Fin (n + 1) → Int),
    cycIntFinSum (n + 1) f =
      cycIntFinSum n (fun j => f ⟨j.1, Nat.lt_succ_of_lt j.2⟩) + f ⟨n, Nat.lt_succ_self n⟩
  | 0, f => by simp [cycIntFinSum]
  | n' + 1, f => by
    have ih := cycIntFinSum_succ_last n' (fun j => f ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)
    change f ⟨0, Nat.zero_lt_succ (n' + 1)⟩ +
        cycIntFinSum (n' + 1) (fun j => f ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩) =
      (f ⟨0, Nat.zero_lt_succ (n' + 1)⟩ +
        cycIntFinSum n' (fun j => f ⟨j.1 + 1, Nat.lt_succ_of_lt (Nat.succ_lt_succ j.2)⟩)) +
      f ⟨n' + 1, Nat.lt_succ_self (n' + 1)⟩
    rw [ih]
    exact (Int.add_assoc _ _ _).symm

/-- Express `inv1 * cycGeomSum r m` as an explicit finite sum of $m$ signed monomials. -/
private theorem inv_mul_cycGeomSum_eq_finSum {N : Nat} (hN : 0 < N)
    (sInv sigma : Bool) (offset d : Nat) :
    ∀ m : Nat,
      cycIntMul (cycSignedPow hN sInv offset) (cycGeomSum (cycSignedPow hN sigma d) m) =
      fun k => cycIntFinSum m (fun j =>
        cycSignedPow hN (bne sInv (decide (j.val % 2 = 1) && sigma)) (offset + j.val * d) k)
  | 0 => by
    rw [cycGeomSum, cycIntMul_zero_right]
    rfl
  | m + 1 => by
    simp only [cycGeomSum, cycIntMul_left_distrib, inv_mul_cycGeomSum_eq_finSum hN sInv sigma offset d m,
      cycPolyPow_cycSignedPow hN sigma d m, cycSignedPow_mul hN]
    funext k
    rw [cycIntFinSum_succ_last m]
    rfl

/-- Constructive search over `Fin m` (choice-free). -/
private def cycFindFin? : (m : Nat) → (p : Fin m → Bool) →
    Option { j : Fin m // p j = true }
  | 0, _ => none
  | m + 1, p =>
    if h0 : p ⟨0, Nat.zero_lt_succ m⟩ = true then
      some ⟨⟨0, Nat.zero_lt_succ m⟩, h0⟩
    else
      match cycFindFin? m (fun j => p ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩) with
      | some ⟨j', hj'⟩ => some ⟨⟨j'.1 + 1, Nat.succ_lt_succ j'.2⟩, hj'⟩
      | none => none

private theorem cycFindFin?_none_iff : ∀ {m : Nat} {p : Fin m → Bool},
    cycFindFin? m p = none → ∀ j : Fin m, p j = false
  | 0, _, _, j => Fin.elim0 j
  | m + 1, p, hNone, ⟨k, hk⟩ => by
    unfold cycFindFin? at hNone
    split at hNone
    · cases hNone
    · rename_i h0
      cases k with
      | zero =>
        cases hb : p ⟨0, Nat.zero_lt_succ m⟩
        · rfl
        · exact False.elim (h0 hb)
      | succ j =>
        cases hRec : cycFindFin? m (fun i => p ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) with
        | some _ => rw [hRec] at hNone; cases hNone
        | none => exact cycFindFin?_none_iff hRec ⟨j, Nat.lt_of_succ_lt_succ hk⟩

/-- Sum of $m$ signed monomials at pairwise-distinct degrees has $\{-1, 0, +1\}$ coefficients,
    $\ell_\infty = 1$ (for $m \ge 1$), support weight $m$, and $\ell_1$ norm $m$. -/
private theorem disjoint_monomial_sum_norms {N m : Nat} (hm : 1 ≤ m)
    (signs : Fin m → Bool) (degs : Fin m → Fin N)
    (hInj : ∀ j1 j2 : Fin m, degs j1 = degs j2 → j1 = j2) :
    let g : NegacyclicPolyInt N := fun k =>
      cycIntFinSum m (fun j => negacyclicSignedMonomial (signs j) (degs j) k)
    (∀ k : Fin N, g k = -1 ∨ g k = 0 ∨ g k = 1) ∧
    cycIntInfNorm g = 1 ∧
    cycIntSupportWeight g = m ∧
    cycIntL1Norm g = m := by
  intro g
  have hPointwise : ∀ k : Fin N,
      (g k = -1 ∨ g k = 0 ∨ g k = 1) ∧
      (g k).natAbs = cycNatFinSum m (fun j => if k = degs j then 1 else 0) ∧
      (if g k = 0 then 0 else 1) = (g k).natAbs := by
    intro k
    rcases hSearch : cycFindFin? m (fun j => decide (k = degs j)) with _ | ⟨j₀, hj₀⟩
    · have hAllFalse := cycFindFin?_none_iff hSearch
      have hgZero : g k = 0 := by
        dsimp only [g]
        have hZ : ∀ j : Fin m, negacyclicSignedMonomial (signs j) (degs j) k = 0 := by
          intro j
          have hf := hAllFalse j
          have hkNe : k ≠ degs j := fun h => by simp [h] at hf
          unfold negacyclicSignedMonomial; simp [hkNe]
        rw [cycIntFinSum_congr hZ, cycIntFinSum_zero]
      have hNatSum : cycNatFinSum m (fun j => if k = degs j then 1 else 0) = 0 := by
        have hZ : ∀ j : Fin m, (if k = degs j then 1 else 0) = 0 := by
          intro j
          have hf := hAllFalse j
          have hkNe : k ≠ degs j := fun h => by simp [h] at hf
          simp [hkNe]
        rw [cycNatFinSum_congr hZ, cycNatFinSum_zero]
      rw [hgZero, hNatSum]
      decide
    · have hkEq : k = degs j₀ := of_decide_eq_true hj₀
      have hgVal : g k = signBitToInt (signs j₀) := by
        dsimp only [g]
        rw [cycIntFinSum_eq_single j₀]
        · unfold negacyclicSignedMonomial; simp [hkEq]
        · intro j hjNe
          unfold negacyclicSignedMonomial
          have hkNe : k ≠ degs j := fun h => hjNe (hInj j j₀ (h.symm.trans hkEq))
          simp [hkNe]
      have hNatSum : cycNatFinSum m (fun j => if k = degs j then 1 else 0) = 1 := by
        rw [cycNatFinSum_eq_single j₀]
        · simp [hkEq]
        · intro j hjNe
          have hkNe : k ≠ degs j := fun h => hjNe (hInj j j₀ (h.symm.trans hkEq))
          simp [hkNe]
      rw [hgVal, hNatSum]
      cases signs j₀ <;> decide
  have hTernary : ∀ k : Fin N, g k = -1 ∨ g k = 0 ∨ g k = 1 := fun k => (hPointwise k).1
  have hL1 : cycIntL1Norm g = m := by
    unfold cycIntL1Norm
    rw [cycNatFinSum_congr (fun k => (hPointwise k).2.1), cycNatFinSum_comm]
    have hEachJ : ∀ j : Fin m, cycNatFinSum N (fun k => if k = degs j then 1 else 0) = 1 := by
      intro j
      rw [cycNatFinSum_eq_single (degs j)]
      · simp
      · intro k hkNe; simp [hkNe]
    rw [cycNatFinSum_congr hEachJ, cycNatFinSum_const, Nat.mul_one]
  have hSupp : cycIntSupportWeight g = m := by
    unfold cycIntSupportWeight
    rw [cycNatFinSum_congr (fun k => (hPointwise k).2.2)]
    exact hL1
  have hInf : cycIntInfNorm g = 1 := by
    have hLe : cycIntInfNorm g ≤ 1 := by
      rw [cycIntInfNorm_le_iff]; intro k
      rcases hTernary k with h | h | h <;> rw [h] <;> decide
    let j0 : Fin m := ⟨0, hm⟩
    have hAtJ0 : g (degs j0) = signBitToInt (signs j0) := by
      dsimp only [g]
      rw [cycIntFinSum_eq_single j0]
      · unfold negacyclicSignedMonomial; simp
      · intro j hjNe
        unfold negacyclicSignedMonomial
        have hNe : degs j0 ≠ degs j := fun h => hjNe (hInj j j0 h.symm)
        simp [hNe]
    have hGe : 1 ≤ cycIntInfNorm g := by
      have hc := cycCoeff_natAbs_le_infNorm g (degs j0)
      rw [hAtJ0, signBitToInt_natAbs] at hc
      exact hc
    omega
  exact ⟨hTernary, hInf, hSupp, hL1⟩

/-- Helper proving Case 2a (`c1.deg.val < c2.deg.val`) of the cyclotomic cofactor theorem. -/
private theorem cofactor_lt_core (nu : Nat) (c1 c2 : SignedMonomialChal nu)
    (hLt : c1.deg.val < c2.deg.val) :
    let hN := Nat.two_pow_pos nu
    let d := c2.deg.val - c1.deg.val
    let res := factorTwos nu d
    let a := res.1
    let m := 2 ^ (nu - a)
    let r := cycSignedPow hN (bne c1.sign c2.sign) d
    let g := cycIntMul (negacyclicSignedMonomialInv hN c1.sign c1.deg) (cycGeomSum r m)
    cycIntMul (cycIntSub c1.toIntPoly c2.toIntPoly) g = cycIntScale 2 cycIntOne ∧
    (∀ k : Fin (2 ^ nu), g k = -1 ∨ g k = 0 ∨ g k = 1) ∧
    cycIntInfNorm g = 1 ∧
    cycIntSupportWeight g = m ∧
    cycIntL1Norm g = m := by
  intro hN d res a m r g
  have hdPos : 0 < d := by omega
  have hdLt : d < 2 ^ nu := by have := c2.deg.isLt; omega
  obtain ⟨hdFact, haLt, huOdd⟩ := factorTwos_spec nu d hdPos hdLt
  let u := res.2
  have hdEq : d = 2 ^ a * u := hdFact
  -- Factor c1 - c2 = c1 * (1 - r)
  have hFactorDiff : cycIntSub c1.toIntPoly c2.toIntPoly =
      cycIntMul c1.toIntPoly (cycIntSub cycIntOne r) := by
    rw [cycIntMul_sub_right, cycIntMul_one_right hN]
    have hc1Pow : c1.toIntPoly = cycSignedPow hN c1.sign c1.deg.val :=
      (cycSignedPow_of_lt hN c1.sign c1.deg.isLt).symm
    have hMulR : cycIntMul c1.toIntPoly r = c2.toIntPoly := by
      rw [hc1Pow]
      dsimp only [r]
      rw [cycSignedPow_mul hN]
      have hSign : bne c1.sign (bne c1.sign c2.sign) = c2.sign := by
        cases c1.sign <;> cases c2.sign <;> rfl
      have hAdd : c1.deg.val + d = c2.deg.val := by omega
      rw [hSign, hAdd, cycSignedPow_of_lt hN c2.sign c2.deg.isLt]
      rfl
    rw [hMulR]
  -- Evaluate r^m = -1
  have haLt' : a < nu := haLt
  have hmEven : m % 2 = 0 := by
    have hPosExp : nu - a = (nu - a - 1) + 1 := by omega
    dsimp only [m]
    rw [hPosExp, Nat.pow_succ]
    omega
  have hmd : m * d = u * (2 ^ nu) := by
    dsimp only [m]
    rw [hdEq, ← Nat.mul_assoc, ← Nat.pow_add]
    have hExp : nu - a + a = nu := by omega
    rw [hExp, Nat.mul_comm]
  have hRm : cycPolyPow r m = cycIntNeg cycIntOne := by
    dsimp only [r]
    rw [cycPolyPow_cycSignedPow hN (bne c1.sign c2.sign) d m]
    have hEvenBool : decide (m % 2 = 1) = false := decide_eq_false (by omega)
    have hOddBool : decide (u % 2 = 1) = true := decide_eq_true huOdd
    rw [hEvenBool, Bool.false_and, hmd, cycSignedPow_mul_N hN false u, hOddBool]
    funext k
    dsimp only [negacyclicSignedMonomial, cycIntNeg, cycIntOne, signBitToInt]
    by_cases hk : k.val = 0
    · have hkEq : k = ⟨0, hN⟩ := Fin.ext hk
      simp [hkEq]
    · have hkNe : k ≠ ⟨0, hN⟩ := fun h => hk (congrArg Fin.val h)
      simp [hkNe, hk]
  -- Conclude (c1 - c2) * g = 2
  have hProdTwo : cycIntMul (cycIntSub c1.toIntPoly c2.toIntPoly) g = cycIntScale 2 cycIntOne := by
    dsimp only [g]
    rw [hFactorDiff, ← cycIntMul_assoc,
        cycIntMul_assoc c1.toIntPoly (cycIntSub cycIntOne r),
        cycIntMul_comm (cycIntSub cycIntOne r) (negacyclicSignedMonomialInv hN c1.sign c1.deg),
        ← cycIntMul_assoc c1.toIntPoly]
    have hInv : cycIntMul c1.toIntPoly (negacyclicSignedMonomialInv hN c1.sign c1.deg) = cycIntOne :=
      negacyclicSignedMonomial_mul_inv hN c1.sign c1.deg
    rw [hInv, cycIntMul_one_left hN, one_sub_mul_cycGeomSum hN r m, hRm]
    funext k
    dsimp only [cycIntSub, cycIntNeg, cycIntScale, cycIntOne]
    split <;> omega
  -- Prove disjoint degrees & exact norms
  have hgSum : g = fun k => cycIntFinSum m (fun j =>
      negacyclicSignedMonomial
        (bne (bne (!c1.sign) (decide (j.val % 2 = 1) && bne c1.sign c2.sign))
             (decide ((((2 ^ nu - c1.deg.val) + j.val * d) / (2 ^ nu)) % 2 = 1)))
        ⟨((2 ^ nu - c1.deg.val) + j.val * d) % (2 ^ nu), Nat.mod_lt _ hN⟩ k) := by
    dsimp only [g, negacyclicSignedMonomialInv, r]
    exact inv_mul_cycGeomSum_eq_finSum hN (!c1.sign) (bne c1.sign c2.sign) (2 ^ nu - c1.deg.val) d m
  have hmGe1 : 1 ≤ m := Nat.two_pow_pos (nu - a)
  have hDegInj : ∀ j1 j2 : Fin m,
      (⟨((2 ^ nu - c1.deg.val) + j1.val * d) % (2 ^ nu), Nat.mod_lt _ hN⟩ : Fin (2 ^ nu)) =
      ⟨((2 ^ nu - c1.deg.val) + j2.val * d) % (2 ^ nu), Nat.mod_lt _ hN⟩ → j1 = j2 := by
    intro j1 j2 hEqFin
    have hEqMod := congrArg Fin.val hEqFin
    dsimp only at hEqMod
    rw [hdEq] at hEqMod
    exact geom_term_deg_injective haLt huOdd (2 ^ nu - c1.deg.val) hEqMod
  obtain ⟨hTern, hInf, hSupp, hL1⟩ := disjoint_monomial_sum_norms hmGe1
    (fun j => bne (bne (!c1.sign) (decide (j.val % 2 = 1) && bne c1.sign c2.sign))
                  (decide ((((2 ^ nu - c1.deg.val) + j.val * d) / (2 ^ nu)) % 2 = 1)))
    (fun j => ⟨((2 ^ nu - c1.deg.val) + j.val * d) % (2 ^ nu), Nat.mod_lt _ hN⟩)
    hDegInj
  rw [← hgSum] at hTern hInf hSupp hL1
  exact ⟨hProdTwo, hTern, hInf, hSupp, hL1⟩

/-- **Exact Cyclotomic Signed-Monomial Cofactor Theorem (`signedMonomial_diff_mul_cofactor_eq_two`)**:
    For ANY two distinct signed monomials $c_1 \ne c_2$ in $\mathbb{Z}[X]/(X^{2^\nu} + 1)$, the explicit
    cofactor $g = \mathsf{signedMonomialCofactor}\, \nu\, c_1\, c_2$ of support size
    $m = \mathsf{signedMonomialCofactorSupportSize}\, \nu\, c_1\, c_2 \le 2^\nu$ has coefficients in
    $\{-1, 0, +1\}$, $\|g\|_\infty = 1$, $\|g\|_1 = m$, and satisfies
    $(c_1 - c_2) \circledast g = 2$ identically in $\mathbb{Z}[X]/(X^{2^\nu} + 1)$ BEFORE any mod-$q$ reduction! -/
theorem signedMonomial_diff_mul_cofactor_eq_two (nu : Nat)
    (c1 c2 : SignedMonomialChal nu) (hNe : c1 ≠ c2) :
    let g := signedMonomialCofactor nu c1 c2
    let m := signedMonomialCofactorSupportSize nu c1 c2
    cycIntMul (cycIntSub c1.toIntPoly c2.toIntPoly) g = cycIntScale 2 cycIntOne ∧
    cycIntMul g (cycIntSub c1.toIntPoly c2.toIntPoly) = cycIntScale 2 cycIntOne ∧
    (∀ k : Fin (2 ^ nu), g k = -1 ∨ g k = 0 ∨ g k = 1) ∧
    cycIntInfNorm g = 1 ∧
    cycIntSupportWeight g = m ∧
    cycIntL1Norm g = m ∧
    1 ≤ m ∧ m ≤ 2 ^ nu ∧
    (c1.deg = c2.deg → m = 1) ∧
    (c1.deg ≠ c2.deg →
      let d := cycNatDist c1.deg.val c2.deg.val
      let res := factorTwos nu d
      d = 2 ^ res.1 * res.2 ∧ res.1 < nu ∧ res.2 % 2 = 1 ∧ m = 2 ^ (nu - res.1) ∧ m % 2 = 0) := by
  intro g m
  have hN := Nat.two_pow_pos nu
  by_cases hDegEq : c1.deg = c2.deg
  · -- Case 1: k1 = k2 and s1 ≠ s2, so c1 - c2 = ±2 X^{k1} and multiplying by (c1)⁻¹ yields 2 with support 1
    have hsNe : c1.sign ≠ c2.sign := by
      intro hsEq; apply hNe
      cases c1; cases c2; dsimp at hsEq hDegEq; subst hsEq; subst hDegEq; rfl
    have hgDef : g = negacyclicSignedMonomialInv hN c1.sign c1.deg := by
      dsimp only [g, signedMonomialCofactor]; simp [hDegEq]
    have hmDef : m = 1 := by
      dsimp only [m, signedMonomialCofactorSupportSize]; simp [hDegEq]
    have hc2Neg : c2.toIntPoly = cycIntNeg c1.toIntPoly := by
      funext k
      dsimp only [SignedMonomialChal.toIntPoly, signedMonomial, negacyclicSignedMonomial, cycIntNeg]
      rw [← hDegEq]
      split
      · cases h1 : c1.sign <;> cases h2 : c2.sign
        · rw [h1, h2] at hsNe; exact False.elim (hsNe rfl)
        · rfl
        · rfl
        · rw [h1, h2] at hsNe; exact False.elim (hsNe rfl)
      · rfl
    have hDiffTwo : cycIntSub c1.toIntPoly c2.toIntPoly = cycIntScale 2 c1.toIntPoly := by
      rw [hc2Neg]
      funext k; dsimp only [cycIntSub, cycIntNeg, cycIntScale]; omega
    have hProd : cycIntMul (cycIntSub c1.toIntPoly c2.toIntPoly) g = cycIntScale 2 cycIntOne := by
      rw [hDiffTwo, hgDef, cycIntMul_scale_left]
      unfold SignedMonomialChal.toIntPoly signedMonomial
      rw [negacyclicSignedMonomial_mul_inv hN c1.sign c1.deg]
    -- Single signed monomial norms
    let degInv : Fin (2 ^ nu) := ⟨(2 ^ nu - c1.deg.val) % (2 ^ nu), Nat.mod_lt _ hN⟩
    let signInv : Bool := bne (!c1.sign) (decide (((2 ^ nu - c1.deg.val) / (2 ^ nu)) % 2 = 1))
    have hgSingle : g = fun k => cycIntFinSum 1 (fun _ => negacyclicSignedMonomial signInv degInv k) := by
      rw [hgDef]
      funext k
      dsimp only [negacyclicSignedMonomialInv, cycSignedPow, cycIntFinSum, signInv, degInv]
      rw [Int.add_zero]
    obtain ⟨hTern, hInf, hSupp, hL1⟩ := disjoint_monomial_sum_norms (by decide : 1 ≤ 1)
      (fun _ => signInv) (fun _ => degInv) (fun j1 j2 _ => Fin.ext (by have := j1.isLt; have := j2.isLt; omega))
    rw [← hgSingle] at hTern hInf hSupp hL1
    refine ⟨hProd, by rw [cycIntMul_comm]; exact hProd, hTern, hInf, ?_, ?_, ?_, ?_,
      fun _ => hmDef, fun hNeDeg => False.elim (hNeDeg hDegEq)⟩
    · rw [hSupp, hmDef]
    · rw [hL1, hmDef]
    · rw [hmDef]; exact Nat.le_refl 1
    · rw [hmDef]; exact hN
  · -- Case 2: k1 ≠ k2, d = |k2 - k1| = 2^a * u, m = 2^(nu - a) even
    let d := cycNatDist c1.deg.val c2.deg.val
    have hdPos : 0 < d := by
      have hvNe : c1.deg.val ≠ c2.deg.val := fun h => hDegEq (Fin.ext h)
      dsimp only [d, cycNatDist]; split <;> omega
    have hdLt : d < 2 ^ nu := by
      have h1 := c1.deg.isLt; have h2 := c2.deg.isLt
      dsimp only [d, cycNatDist]; split <;> omega
    obtain ⟨hdFact, haLt, huOdd⟩ := factorTwos_spec nu d hdPos hdLt
    let a := (factorTwos nu d).1
    have hmDef : m = 2 ^ (nu - a) := by
      dsimp only [m, signedMonomialCofactorSupportSize]; simp [hDegEq]; rfl
    have hmGe1 : 1 ≤ m := by rw [hmDef]; exact Nat.two_pow_pos (nu - a)
    have hmLeN : m ≤ 2 ^ nu := by
      rw [hmDef]; exact Nat.pow_le_pow_right (by decide) (by omega)
    have hmEven : m % 2 = 0 := by
      rw [hmDef]
      have hPosExp : nu - a = (nu - a - 1) + 1 := by omega
      rw [hPosExp, Nat.pow_succ]; omega
    by_cases hLt : c1.deg.val < c2.deg.val
    · have hdEqSub : d = c2.deg.val - c1.deg.val := by
        dsimp only [d, cycNatDist]
        have hLe : c1.deg.val ≤ c2.deg.val := Nat.le_of_lt hLt
        simp [hLe]
      have hgEq : g = cycIntMul (negacyclicSignedMonomialInv hN c1.sign c1.deg)
          (cycGeomSum (cycSignedPow hN (bne c1.sign c2.sign) (c2.deg.val - c1.deg.val))
            (2 ^ (nu - (factorTwos nu (c2.deg.val - c1.deg.val)).1))) := by
        dsimp only [g, signedMonomialCofactor]
        simp only [hDegEq, hLt, ↓reduceIte]
        change cycIntMul (negacyclicSignedMonomialInv hN c1.sign c1.deg)
            (cycGeomSum (cycSignedPow hN (bne c1.sign c2.sign) d)
              (2 ^ (nu - (factorTwos nu d).1))) = _
        rw [hdEqSub]
      have hCore := cofactor_lt_core nu c1 c2 hLt
      dsimp only at hCore
      obtain ⟨hProd, hTern, hInf, hSupp, hL1⟩ := hCore
      rw [← hgEq] at hProd hTern hInf hSupp hL1
      rw [← hdEqSub, ← hmDef] at hSupp hL1
      exact ⟨hProd, by rw [cycIntMul_comm]; exact hProd, hTern, hInf, hSupp, hL1,
        hmGe1, hmLeN, fun hEq => False.elim (hDegEq hEq),
        fun _ => ⟨hdFact, haLt, huOdd, hmDef, hmEven⟩⟩
    · have hGt : c2.deg.val < c1.deg.val := by
        have hvNe : c1.deg.val ≠ c2.deg.val := fun h => hDegEq (Fin.ext h)
        omega
      have hdEqSub : d = c1.deg.val - c2.deg.val := by
        dsimp only [d, cycNatDist]
        have hNotLe : ¬(c1.deg.val ≤ c2.deg.val) := by omega
        simp [hNotLe]
      let g21 := cycIntMul (negacyclicSignedMonomialInv hN c2.sign c2.deg)
        (cycGeomSum (cycSignedPow hN (bne c2.sign c1.sign) (c1.deg.val - c2.deg.val))
          (2 ^ (nu - (factorTwos nu (c1.deg.val - c2.deg.val)).1)))
      have hgEq : g = cycIntNeg g21 := by
        dsimp only [g, signedMonomialCofactor, g21]
        simp only [hDegEq, hLt, ↓reduceIte]
        change cycIntNeg (cycIntMul (negacyclicSignedMonomialInv hN c2.sign c2.deg)
            (cycGeomSum (cycSignedPow hN (bne c2.sign c1.sign) d)
              (2 ^ (nu - (factorTwos nu d).1)))) = _
        rw [hdEqSub]
      have hCore21 := cofactor_lt_core nu c2 c1 hGt
      dsimp only at hCore21
      obtain ⟨hProd21, hTern21, hInf21, hSupp21, hL121⟩ := hCore21
      have hSubNeg : cycIntSub c1.toIntPoly c2.toIntPoly = cycIntNeg (cycIntSub c2.toIntPoly c1.toIntPoly) := by
        funext k; dsimp only [cycIntSub, cycIntNeg]; omega
      have hProd : cycIntMul (cycIntSub c1.toIntPoly c2.toIntPoly) g = cycIntScale 2 cycIntOne := by
        rw [hgEq, hSubNeg, cycIntMul_neg_left, cycIntMul_neg_right]
        have hNegNeg : cycIntNeg (cycIntNeg (cycIntMul (cycIntSub c2.toIntPoly c1.toIntPoly) g21)) =
            cycIntMul (cycIntSub c2.toIntPoly c1.toIntPoly) g21 := by
          funext k; dsimp only [cycIntNeg]; omega
        rw [hNegNeg]
        exact hProd21
      have hTern : ∀ k : Fin (2 ^ nu), g k = -1 ∨ g k = 0 ∨ g k = 1 := by
        intro k; rw [hgEq]; dsimp only [cycIntNeg, g21]
        rcases hTern21 k with h | h | h <;> rw [h] <;> decide
      have hInf : cycIntInfNorm g = 1 := by rw [hgEq, cycIntInfNorm_neg]; exact hInf21
      have hSupp : cycIntSupportWeight g = m := by
        rw [hgEq, cycIntSupportWeight_neg]; dsimp only [g21]; rw [hSupp21, ← hdEqSub, hmDef]
      have hL1 : cycIntL1Norm g = m := by
        rw [hgEq, cycIntL1Norm_neg]; dsimp only [g21]; rw [hL121, ← hdEqSub, hmDef]
      exact ⟨hProd, by rw [cycIntMul_comm]; exact hProd, hTern, hInf, hSupp, hL1,
        hmGe1, hmLeN, fun hEq => False.elim (hDegEq hEq),
        fun _ => ⟨hdFact, haLt, huOdd, hmDef, hmEven⟩⟩

/-- Explicit two-sided multiplicative inverse $((q + 1) / 2) \cdot g(X) \bmod q$ of $c_1 - c_2$
    in $R_q = \mathbb{Z}_q[X]/(X^{2^\nu} + 1)$ for any odd modulus $q$. -/
@[expose] def signedMonomialDiffInvZq (nu q : Nat) [NeZero q]
    (c1 c2 : SignedMonomialChal nu) : CycPolyZq nu q :=
  cycIntToZq q (cycIntScale (((q + 1) / 2 : Nat) : Int) (signedMonomialCofactor nu c1 c2))

/-- **Pairwise Invertibility of the Full $2 \cdot 2^\nu$-Element Signed-Monomial Challenge Space
    (`signedMonomial_challenge_set_pairwise_invertible`)**:
    For EVERY $\nu \ge 0$ and EVERY odd modulus $q \ge 3$, all $2 \cdot 2^\nu$ signed monomials are
    pairwise distinct in $R_q = \mathbb{Z}_q[X]/(X^{2^\nu} + 1)$ and every non-zero challenge difference
    $c_1 - c_2$ has exact two-sided multiplicative inverse `((q + 1) / 2) * g(X) mod q`! -/
theorem signedMonomial_challenge_set_pairwise_invertible (nu q : Nat) [NeZero q]
    (hOdd : q % 2 = 1) (hq3 : 3 ≤ q)
    (c1 c2 : SignedMonomialChal nu) (hNe : c1 ≠ c2) :
    c1.toZqPoly q ≠ c2.toZqPoly q ∧
    cycZqMul (cycZqSub (c1.toZqPoly q) (c2.toZqPoly q))
      (signedMonomialDiffInvZq nu q c1 c2) = cycZqOne ∧
    cycZqMul (signedMonomialDiffInvZq nu q c1 c2)
      (cycZqSub (c1.toZqPoly q) (c2.toZqPoly q)) = cycZqOne := by
  have hDistZq : c1.toZqPoly q ≠ c2.toZqPoly q :=
    fun hEq => hNe (signedMonomial_toZq_injective hq3 hEq)
  obtain ⟨hTwo, _, _⟩ := signedMonomial_diff_mul_cofactor_eq_two nu c1 c2 hNe
  have hRightInv :
      cycZqMul (cycZqSub (c1.toZqPoly q) (c2.toZqPoly q))
        (signedMonomialDiffInvZq nu q c1 c2) = cycZqOne := by
    unfold SignedMonomialChal.toZqPoly signedMonomialDiffInvZq
    rw [← cycIntToZq_sub, ← cycIntToZq_mul, cycIntMul_scale_right, hTwo]
    have hScale : cycIntScale (((q + 1) / 2 : Nat) : Int) (cycIntScale 2 (@cycIntOne (2 ^ nu))) =
        cycIntScale ((q : Int) + 1) cycIntOne := by
      funext k; unfold cycIntScale
      have hOddMul : (((q + 1) / 2 : Nat) : Int) * 2 = (q : Int) + 1 := by omega
      rw [← Int.mul_assoc, hOddMul]
    rw [hScale]
    funext k
    unfold cycIntToZq cycIntScale cycIntOne cycZqOne
    split
    · rw [Int.mul_one, ← ModZq.ofInt_one]
      apply ModZq.ext_int
      rw [ModZq.ofInt_val_int, ModZq.ofInt_val_int]
      have hEq : (q : Int) + 1 = 1 + 1 * (q : Int) := by omega
      rw [hEq, Int.add_mul_emod_self_right]
    · rw [Int.mul_zero]; exact ModZq.ofInt_zero q
  exact ⟨hDistZq, hRightInv, by rw [cycZqMul_comm]; exact hRightInv⟩

/-- Specialization of pairwise invertibility at production $\nu = 10, N = 1024$ (`2048` challenges)
    for every odd modulus $q \ge 3$ (including $q = 12289$). -/
theorem signedMonomial_1024_challenge_set_2048_pairwise_invertible (q : Nat) [NeZero q]
    (hOdd : q % 2 = 1) (hq3 : 3 ≤ q)
    (c1 c2 : SignedMonomialChal 10) (hNe : c1 ≠ c2) :
    2 * 2 ^ 10 = 2048 ∧
    c1.toZqPoly q ≠ c2.toZqPoly q ∧
    cycZqMul (cycZqSub (c1.toZqPoly q) (c2.toZqPoly q))
      (signedMonomialDiffInvZq 10 q c1 c2) = cycZqOne ∧
    cycZqMul (signedMonomialDiffInvZq 10 q c1 c2)
      (cycZqSub (c1.toZqPoly q) (c2.toZqPoly q)) = cycZqOne :=
  ⟨rfl, signedMonomial_challenge_set_pairwise_invertible 10 q hOdd hq3 c1 c2 hNe⟩


/-! ## 3. 13-Parallel RLWE OR-Sigma Relation, Choice-Free Witness Extractor & $\ell_\infty$ Norm-Slack -/

/-- Bitwise XOR group operation on `(nu + 1)`-bit signed-monomial challenge codes (`c0 ⊕ c1 = c`).
    Production splits the joint challenge the same way (`self.chal0[rep] ^ self.chal1[rep] == *expected`),
    on 20-bit two-term codes rather than these `(nu + 1)`-bit single-monomial codes. -/
def SignedMonomialChal.xor {nu : Nat} (c0 c1 : SignedMonomialChal nu) : SignedMonomialChal nu where
  sign := bne c0.sign c1.sign
  deg := ⟨((BitVec.ofNat nu c0.deg.val) ^^^ (BitVec.ofNat nu c1.deg.val)).toNat,
          ((BitVec.ofNat nu c0.deg.val) ^^^ (BitVec.ofNat nu c1.deg.val)).isLt⟩

private theorem bitvec_xor_cancel_right {w : Nat} (a b : BitVec w) : (a ^^^ b) ^^^ b = a := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_xor]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

private theorem bitvec_xor_cancel_left {w : Nat} (a b : BitVec w) : a ^^^ (a ^^^ b) = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_xor]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem SignedMonomialChal.xor_cancel_right {nu : Nat} (c f : SignedMonomialChal nu) :
    (c.xor f).xor f = c := by
  apply SignedMonomialChal.ext
  · unfold SignedMonomialChal.xor; dsimp only
    cases c.sign <;> cases f.sign <;> rfl
  · unfold SignedMonomialChal.xor; dsimp only
    have hOfNat : ∀ x : BitVec nu, BitVec.ofNat nu x.toNat = x :=
      fun x => (BitVec.ofNat_toNat nu x).trans (BitVec.setWidth_eq x)
    rw [hOfNat, bitvec_xor_cancel_right, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt c.deg.isLt

theorem SignedMonomialChal.xor_cancel_left {nu : Nat} (f c : SignedMonomialChal nu) :
    f.xor (f.xor c) = c := by
  apply SignedMonomialChal.ext
  · unfold SignedMonomialChal.xor; dsimp only
    cases f.sign <;> cases c.sign <;> rfl
  · unfold SignedMonomialChal.xor; dsimp only
    have hOfNat : ∀ x : BitVec nu, BitVec.ofNat nu x.toNat = x :=
      fun x => (BitVec.ofNat_toNat nu x).trans (BitVec.setWidth_eq x)
    rw [hOfNat, bitvec_xor_cancel_left, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt c.deg.isLt

/-- Public statement for the parallel Ring-LWE OR-Sigma proof of short witness knowledge:
    public CRS polynomial $A \in R_q$, branch targets $(u_0, u_1) \in R_q^2$ (`pk0` and `pk0 + t_crs`
    in `preprocessing.rs:1158-1159`), and verifier $\ell_\infty$ response bound $B_z$. -/
structure RlweOrSigmaStatement (nu q : Nat) where
  A : CycPolyZq nu q
  u0 : CycPolyZq nu q
  u1 : CycPolyZq nu q
  Bz : Nat

def RlweOrSigmaStatement.branchU {nu q : Nat} (stmt : RlweOrSigmaStatement nu q) (b : Bool) :
    CycPolyZq nu q :=
  if b then stmt.u1 else stmt.u0

/-- Construct an OR-Sigma statement from Ring-LWE Base-OT parameters `(A, pk0, t_crs, B_z)`. -/
def RlweOrSigmaStatement.fromBaseOt {nu q : Nat} [NeZero q]
    (A pk0 tCrs : CycPolyZq nu q) (Bz : Nat) : RlweOrSigmaStatement nu q where
  A := A
  u0 := pk0
  u1 := cycZqAdd pk0 tCrs
  Bz := Bz

/-- `R`-parallel OR-Sigma transcript over single signed-monomial challenges, carrying commitments
    `(t0, t1)`, branch challenges `(c0, c1)`, and integer responses `(zs0, ze0, zs1, ze1)`. It has the
    shape of `RlweReceiverZkPok` (`R = 13`) with the challenge set narrowed to the pairwise-invertible one. -/
structure RlweOrSigmaTranscript (R nu q : Nat) where
  t0 : Fin R → CycPolyZq nu q
  t1 : Fin R → CycPolyZq nu q
  c0 : Fin R → SignedMonomialChal nu
  c1 : Fin R → SignedMonomialChal nu
  zs0 : Fin R → CycPolyInt nu
  ze0 : Fin R → CycPolyInt nu
  zs1 : Fin R → CycPolyInt nu
  ze1 : Fin R → CycPolyInt nu

def RlweOrSigmaTranscript.branchT {R nu q : Nat} (tr : RlweOrSigmaTranscript R nu q)
    (b : Bool) (i : Fin R) : CycPolyZq nu q :=
  if b then tr.t1 i else tr.t0 i

def RlweOrSigmaTranscript.branchChal {R nu q : Nat} (tr : RlweOrSigmaTranscript R nu q)
    (b : Bool) (i : Fin R) : SignedMonomialChal nu :=
  if b then tr.c1 i else tr.c0 i

def RlweOrSigmaTranscript.branchZs {R nu q : Nat} (tr : RlweOrSigmaTranscript R nu q)
    (b : Bool) (i : Fin R) : CycPolyInt nu :=
  if b then tr.zs1 i else tr.zs0 i

def RlweOrSigmaTranscript.branchZe {R nu q : Nat} (tr : RlweOrSigmaTranscript R nu q)
    (b : Bool) (i : Fin R) : CycPolyInt nu :=
  if b then tr.ze1 i else tr.ze0 i

/-- Single-repetition OR-Sigma verifier checking:
    1. `c0_i ⊕ c1_i = c_i`,
    2. `‖zs_b‖_∞ ≤ B_z` and `‖ze_b‖_∞ ≤ B_z` for `b ∈ {0, 1}`,
    3. `A * zs_b + ze_b = t_b + c_b * u_b` in $R_q$ for `b ∈ {0, 1}`. -/
def verifyRlweOrSigmaRep {R nu q : Nat} [NeZero q]
    (stmt : RlweOrSigmaStatement nu q) (i : Fin R) (expectedChal : SignedMonomialChal nu)
    (tr : RlweOrSigmaTranscript R nu q) : Bool :=
  let chalOk := decide ((tr.c0 i).xor (tr.c1 i) = expectedChal)
  let normOk :=
    decide (cycIntInfNorm (tr.zs0 i) ≤ stmt.Bz) &&
    decide (cycIntInfNorm (tr.ze0 i) ≤ stmt.Bz) &&
    decide (cycIntInfNorm (tr.zs1 i) ≤ stmt.Bz) &&
    decide (cycIntInfNorm (tr.ze1 i) ≤ stmt.Bz)
  let eq0Ok := cycZqEq
    (cycZqAdd (cycZqMul stmt.A (cycIntToZq q (tr.zs0 i))) (cycIntToZq q (tr.ze0 i)))
    (cycZqAdd (tr.t0 i) (cycZqMul ((tr.c0 i).toZqPoly q) stmt.u0))
  let eq1Ok := cycZqEq
    (cycZqAdd (cycZqMul stmt.A (cycIntToZq q (tr.zs1 i))) (cycIntToZq q (tr.ze1 i)))
    (cycZqAdd (tr.t1 i) (cycZqMul ((tr.c1 i).toZqPoly q) stmt.u1))
  chalOk && normOk && eq0Ok && eq1Ok

/-- Full `R`-parallel RLWE OR-Sigma verifier (`R = 13` in `verifyRlweOrSigma13`). -/
def verifyRlweOrSigma (R nu q : Nat) [NeZero q]
    (stmt : RlweOrSigmaStatement nu q)
    (jointChal : Fin R → SignedMonomialChal nu)
    (tr : RlweOrSigmaTranscript R nu q) : Bool :=
  cycAllFin R (fun i => verifyRlweOrSigmaRep stmt i (jointChal i) tr)

theorem verifyRlweOrSigma_iff (R nu q : Nat) [NeZero q]
    (stmt : RlweOrSigmaStatement nu q)
    (jointChal : Fin R → SignedMonomialChal nu)
    (tr : RlweOrSigmaTranscript R nu q) :
    verifyRlweOrSigma R nu q stmt jointChal tr = true ↔
      ∀ i : Fin R, verifyRlweOrSigmaRep stmt i (jointChal i) tr = true := by
  unfold verifyRlweOrSigma
  exact cycAllFin_eq_true_iff _

abbrev verifyRlweOrSigma13 (nu q : Nat) [NeZero q] :=
  verifyRlweOrSigma rlweOrSigmaParallelReps nu q

/-- Honest masked OR-Sigma prover on active branch `branch : Bool` with short secret `(s, e)`
    satisfying `A * s + e = u_{branch}`: commits `(t0, t1)` independent of `jointChal` so rewinding
    with `jointChal' ≠ jointChal` yields two accepting transcripts on the exact same commitment! -/
def buildHonestRlweOrSigmaTranscript (R nu q : Nat) [NeZero q]
    (stmt : RlweOrSigmaStatement nu q) (branch : Bool)
    (sSecret eSecret : CycPolyInt nu)
    (ysMask yeMask : Fin R → CycPolyInt nu)
    (cFake : Fin R → SignedMonomialChal nu)
    (zsFake zeFake : Fin R → CycPolyInt nu)
    (jointChal : Fin R → SignedMonomialChal nu) : RlweOrSigmaTranscript R nu q :=
  let uFake := if branch then stmt.u0 else stmt.u1
  let tReal : Fin R → CycPolyZq nu q := fun i =>
    cycZqAdd (cycZqMul stmt.A (cycIntToZq q (ysMask i))) (cycIntToZq q (yeMask i))
  let tFake : Fin R → CycPolyZq nu q := fun i =>
    cycZqSub
      (cycZqAdd (cycZqMul stmt.A (cycIntToZq q (zsFake i))) (cycIntToZq q (zeFake i)))
      (cycZqMul ((cFake i).toZqPoly q) uFake)
  let cReal : Fin R → SignedMonomialChal nu := fun i =>
    if branch then (cFake i).xor (jointChal i) else (jointChal i).xor (cFake i)
  let zsReal : Fin R → CycPolyInt nu := fun i =>
    cycIntAdd (ysMask i) (cycIntMul (cReal i).toIntPoly sSecret)
  let zeReal : Fin R → CycPolyInt nu := fun i =>
    cycIntAdd (yeMask i) (cycIntMul (cReal i).toIntPoly eSecret)
  if branch then
    { t0 := tFake, t1 := tReal, c0 := cFake, c1 := cReal,
      zs0 := zsFake, ze0 := zeFake, zs1 := zsReal, ze1 := zeReal }
  else
    { t0 := tReal, t1 := tFake, c0 := cReal, c1 := cFake,
      zs0 := zsReal, ze0 := zeReal, zs1 := zsFake, ze1 := zeFake }

/-- Commitments of `buildHonestRlweOrSigmaTranscript` are strictly independent of `jointChal`. -/
theorem buildHonestRlweOrSigmaTranscript_same_commitments (R nu q : Nat) [NeZero q]
    (stmt : RlweOrSigmaStatement nu q) (branch : Bool)
    (sSecret eSecret : CycPolyInt nu)
    (ysMask yeMask : Fin R → CycPolyInt nu)
    (cFake : Fin R → SignedMonomialChal nu)
    (zsFake zeFake : Fin R → CycPolyInt nu)
    (ch ch' : Fin R → SignedMonomialChal nu) :
    let tr := buildHonestRlweOrSigmaTranscript R nu q stmt branch sSecret eSecret
      ysMask yeMask cFake zsFake zeFake ch
    let tr' := buildHonestRlweOrSigmaTranscript R nu q stmt branch sSecret eSecret
      ysMask yeMask cFake zsFake zeFake ch'
    tr.t0 = tr'.t0 ∧ tr.t1 = tr'.t1 := by
  cases branch <;> exact ⟨rfl, rfl⟩

private theorem signedMonomial_l1Norm_eq_one (nu : Nat) (c : SignedMonomialChal nu) :
    cycIntL1Norm c.toIntPoly = 1 := by
  unfold cycIntL1Norm SignedMonomialChal.toIntPoly signedMonomial negacyclicSignedMonomial
  rw [cycNatFinSum_eq_single c.deg]
  · simp [signBitToInt_natAbs]
  · intro i hiNe; simp [hiNe]

/-- Completeness of `buildHonestRlweOrSigmaTranscript` for all `R, nu, q`. -/
theorem buildHonestRlweOrSigmaTranscript_accepts {R nu q : Nat} [NeZero q]
    (stmt : RlweOrSigmaStatement nu q) (branch : Bool)
    (sSecret eSecret : CycPolyInt nu)
    (ysMask yeMask : Fin R → CycPolyInt nu)
    (cFake : Fin R → SignedMonomialChal nu)
    (zsFake zeFake : Fin R → CycPolyInt nu)
    (jointChal : Fin R → SignedMonomialChal nu)
    (hRel : cycZqAdd (cycZqMul stmt.A (cycIntToZq q sSecret)) (cycIntToZq q eSecret) =
      stmt.branchU branch)
    (hSafeS : ∀ i : Fin R, cycIntInfNorm (ysMask i) + cycIntInfNorm sSecret ≤ stmt.Bz)
    (hSafeE : ∀ i : Fin R, cycIntInfNorm (yeMask i) + cycIntInfNorm eSecret ≤ stmt.Bz)
    (hFakeS : ∀ i : Fin R, cycIntInfNorm (zsFake i) ≤ stmt.Bz)
    (hFakeE : ∀ i : Fin R, cycIntInfNorm (zeFake i) ≤ stmt.Bz) :
    verifyRlweOrSigma R nu q stmt jointChal
      (buildHonestRlweOrSigmaTranscript R nu q stmt branch sSecret eSecret
        ysMask yeMask cFake zsFake zeFake jointChal) = true := by
  unfold verifyRlweOrSigma
  rw [cycAllFin_eq_true_iff]
  intro i
  unfold verifyRlweOrSigmaRep buildHonestRlweOrSigmaTranscript
  have hRealSBound : ∀ c : SignedMonomialChal nu,
      cycIntInfNorm (cycIntAdd (ysMask i) (cycIntMul c.toIntPoly sSecret)) ≤ stmt.Bz := by
    intro c
    have hMulLe := cycIntInfNorm_mul_le c.toIntPoly sSecret
    rw [signedMonomial_l1Norm_eq_one, Nat.one_mul] at hMulLe
    rw [cycIntInfNorm_le_iff]; intro k
    unfold cycIntAdd
    have hy := cycCoeff_natAbs_le_infNorm (ysMask i) k
    have hcs := Nat.le_trans (cycCoeff_natAbs_le_infNorm (cycIntMul c.toIntPoly sSecret) k) hMulLe
    have hSafe := hSafeS i
    omega
  have hRealEBound : ∀ c : SignedMonomialChal nu,
      cycIntInfNorm (cycIntAdd (yeMask i) (cycIntMul c.toIntPoly eSecret)) ≤ stmt.Bz := by
    intro c
    have hMulLe := cycIntInfNorm_mul_le c.toIntPoly eSecret
    rw [signedMonomial_l1Norm_eq_one, Nat.one_mul] at hMulLe
    rw [cycIntInfNorm_le_iff]; intro k
    unfold cycIntAdd
    have hy := cycCoeff_natAbs_le_infNorm (yeMask i) k
    have hce := Nat.le_trans (cycCoeff_natAbs_le_infNorm (cycIntMul c.toIntPoly eSecret) k) hMulLe
    have hSafe := hSafeE i
    omega
  have hFakeEq : ∀ (uTgt : CycPolyZq nu q) (cf : SignedMonomialChal nu),
      cycZqAdd (cycZqMul stmt.A (cycIntToZq q (zsFake i))) (cycIntToZq q (zeFake i)) =
      cycZqAdd (cycZqSub (cycZqAdd (cycZqMul stmt.A (cycIntToZq q (zsFake i))) (cycIntToZq q (zeFake i)))
        (cycZqMul (cf.toZqPoly q) uTgt)) (cycZqMul (cf.toZqPoly q) uTgt) := by
    intro uTgt cf
    let X := cycZqAdd (cycZqMul stmt.A (cycIntToZq q (zsFake i))) (cycIntToZq q (zeFake i))
    let Y := cycZqMul (cf.toZqPoly q) uTgt
    show X = cycZqAdd (cycZqSub X Y) Y
    funext k; unfold cycZqAdd cycZqSub
    rw [← ModZq.ofInt_natVal (X k), ← ModZq.ofInt_natVal (Y k),
        ← ModZq.ofInt_sub, ← ModZq.ofInt_add]
    congr 1; omega
  have hRealEq : ∀ (uTgt : CycPolyZq nu q) (cr : SignedMonomialChal nu),
      cycZqAdd (cycZqMul stmt.A (cycIntToZq q sSecret)) (cycIntToZq q eSecret) = uTgt →
      cycZqAdd (cycZqMul stmt.A (cycIntToZq q (cycIntAdd (ysMask i) (cycIntMul cr.toIntPoly sSecret))))
        (cycIntToZq q (cycIntAdd (yeMask i) (cycIntMul cr.toIntPoly eSecret))) =
      cycZqAdd (cycZqAdd (cycZqMul stmt.A (cycIntToZq q (ysMask i))) (cycIntToZq q (yeMask i)))
        (cycZqMul (cr.toZqPoly q) uTgt) := by
    intro uTgt cr huTgt
    rw [cycIntToZq_add, cycIntToZq_add, cycIntToZq_mul, cycIntToZq_mul, cycZqMul_left_distrib]
    have hShift : cycZqAdd (cycZqMul stmt.A (cycZqMul (cr.toZqPoly q) (cycIntToZq q sSecret)))
        (cycZqMul (cr.toZqPoly q) (cycIntToZq q eSecret)) = cycZqMul (cr.toZqPoly q) uTgt := by
      rw [← huTgt, cycZqMul_left_distrib, ← cycZqMul_assoc stmt.A (cr.toZqPoly q),
          cycZqMul_comm stmt.A (cr.toZqPoly q), cycZqMul_assoc]
    funext k
    have hk := congrFun hShift k
    let AY := cycZqMul stmt.A (cycIntToZq q (ysMask i)) k
    let ACS := cycZqMul stmt.A (cycZqMul (cr.toZqPoly q) (cycIntToZq q sSecret)) k
    let YE := cycIntToZq q (yeMask i) k
    let CE := cycZqMul (cr.toZqPoly q) (cycIntToZq q eSecret) k
    let CU := cycZqMul (cr.toZqPoly q) uTgt k
    change ModZq.add ACS CE = CU at hk
    show ModZq.add (ModZq.add AY ACS) (ModZq.add YE CE) = ModZq.add (ModZq.add AY YE) CU
    rw [← hk]
    rw [← ModZq.ofInt_natVal AY, ← ModZq.ofInt_natVal ACS,
        ← ModZq.ofInt_natVal YE, ← ModZq.ofInt_natVal CE]
    simp only [← ModZq.ofInt_add]
    congr 1; omega
  cases branch
  · simp only [Bool.false_eq_true, ↓reduceIte]
    unfold RlweOrSigmaStatement.branchU at hRel
    simp only [Bool.false_eq_true, ↓reduceIte] at hRel
    simp only [Bool.and_eq_true, decide_eq_true_eq, cycZqEq_iff]
    exact ⟨⟨⟨SignedMonomialChal.xor_cancel_right _ _,
      ⟨⟨⟨hRealSBound _, hRealEBound _⟩, hFakeS i⟩, hFakeE i⟩⟩,
      hRealEq stmt.u0 _ hRel⟩, hFakeEq stmt.u1 _⟩
  · simp only [↓reduceIte]
    unfold RlweOrSigmaStatement.branchU at hRel
    simp only [↓reduceIte] at hRel
    simp only [Bool.and_eq_true, decide_eq_true_eq, cycZqEq_iff]
    exact ⟨⟨⟨SignedMonomialChal.xor_cancel_left _ _,
      ⟨⟨⟨hFakeS i, hFakeE i⟩, hRealSBound _⟩, hRealEBound _⟩⟩,
      hFakeEq stmt.u0 _⟩, hRealEq stmt.u1 _ hRel⟩

/-- Relaxed short RLWE / Ring-SIS witness produced by 2-special-soundness extraction on the
    `R`-parallel signed-monomial OR-Sigma protocol (`R = 13` in production). -/
