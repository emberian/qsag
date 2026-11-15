module
public import Qsag.Tactic.Prelude
public import Qsag.Math.Algebra
public import Qsag.Math.Primality

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
