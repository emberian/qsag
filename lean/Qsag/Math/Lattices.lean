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
private theorem inv_mul_cycGeomSum_eq_qsum {N : Nat} (hN : 0 < N)
    (sInv sigma : Bool) (offset d : Nat) :
    ∀ m : Nat,
      cycIntMul (cycSignedPow hN sInv offset) (cycGeomSum (cycSignedPow hN sigma d) m) =
      fun k => cycIntFinSum m (fun j =>
        cycSignedPow hN (bne sInv (decide (j.val % 2 = 1) && sigma)) (offset + j.val * d) k)
  | 0 => by
    rw [cycGeomSum, cycIntMul_zero_right]
    rfl
  | m + 1 => by
    simp only [cycGeomSum, cycIntMul_left_distrib, inv_mul_cycGeomSum_eq_qsum hN sInv sigma offset d m,
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
    exact inv_mul_cycGeomSum_eq_qsum hN (!c1.sign) (bne c1.sign c2.sign) (2 ^ nu - c1.deg.val) d m
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



/-! ## §1. Exact NIST FIPS 204 (`ML-DSA-44`) Field, 256-Point Negacyclic NTT & Rounding Laws -/

/-- NIST FIPS 204 prime modulus $q = 8380417 = 2^{23} - 2^{13} + 1 = 1023 \cdot 2^{13} + 1$. -/
@[expose] def mldsaQ : Nat := 8380417

/-- Cyclotomic ring degree $N = 256$. -/
def mldsaN : Nat := 256

/-- Dropped public-key low-order bit width $d = 13$ ($2^{13} = 8192$). -/
def mldsaD : Nat := 13

/-- Primitive 512-th root of unity $\zeta = 1753 \in \mathbb{Z}_q$ ($\zeta^{256} \equiv -1 \pmod q$). -/
def mldsaZetaNat : Nat := 1753

/-- `ML-DSA-44` (`FIPS 204` Category 2) parameter constants. -/
def mldsa44Gamma2 : Nat := 95232        -- (q - 1) / 88
def mldsa44Alpha : Nat := 190464        -- 2 * gamma2 = (q - 1) / 44
def mldsa44HighMod : Nat := 44          -- (q - 1) / alpha
def mldsa44Tau : Nat := 39
def mldsa44Eta : Nat := 2
def mldsa44Omega : Nat := 80
def mldsa44K : Nat := 4
def mldsa44L : Nat := 4

/-! ### §1.1 Constructive Primality Certificate for `mldsaQ = 8380417` -/

/-- Exported primality witness structure on `Nat` (`0` `@[expose]` overhead). -/
abbrev IsPrime204 := IsPrimeNat
namespace IsPrime204
theorem ge_two {p : Nat} (h : IsPrime204 p) : 2 ≤ p := h.1
theorem dvd_cases {p : Nat} (h : IsPrime204 p) (d : Nat) (hd : d ∣ p) : d = 1 ∨ d = p := h.2 d hd
end IsPrime204

private def noDivTree (n lo : Nat) : Nat → Bool
  | 0 => (n % lo != 0)
  | d + 1 => noDivTree n lo d && noDivTree n (lo + 2 ^ d) d

private theorem noDivTree_sound :
    ∀ (d n lo : Nat), noDivTree n lo d = true →
      ∀ k : Nat, lo ≤ k → k < lo + 2 ^ d → ¬ (k ∣ n)
  | 0, n, lo, hok, k, hlo, hhi, hdvd => by
    have hk : k = lo := by simp at hhi; omega
    subst hk
    simp only [noDivTree, bne_iff_ne] at hok
    exact hok (Nat.mod_eq_zero_of_dvd hdvd)
  | d + 1, n, lo, hok, k, hlo, hhi, hdvd => by
    simp only [noDivTree, Bool.and_eq_true] at hok
    have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; omega
    if hmid : k < lo + 2 ^ d then
      exact noDivTree_sound d n lo hok.1 k hlo hmid hdvd
    else
      exact noDivTree_sound d n (lo + 2 ^ d) hok.2 k (by omega) (by omega) hdvd

private theorem mldsaQ_no_small_div : noDivTree mldsaQ 2 12 = true := by decide

/-- Every divisor of `mldsaQ = 8380417` is `1` or `8380417` ($\lfloor\sqrt{8380417}\rfloor = 2894 < 2 + 2^{12}$). -/
theorem mldsaQ_dvd_cases (d : Nat) (hd : d ∣ mldsaQ) :
    d = 1 ∨ d = mldsaQ := by
  if hd1 : d = 1 then exact .inl hd1
  else if hdq : d = mldsaQ then exact .inr hdq
  else
    exfalso
    obtain ⟨e, he⟩ := hd
    have hdPos : 2 ≤ d := by
      if hd0 : d = 0 then subst hd0; simp [mldsaQ] at he
      else omega
    have hePos : 2 ≤ e := by
      if he0 : e = 0 then subst he0; simp [mldsaQ] at he
      else if he1 : e = 1 then subst he1; simp at he; exact False.elim (hdq he.symm)
      else omega
    have hno := noDivTree_sound 12 mldsaQ 2 mldsaQ_no_small_div
    have h2pow12 : (2 : Nat) + 2 ^ 12 = 4098 := rfl
    rw [h2pow12] at hno
    if hle : d ≤ e then
      have hdLt : d < 2896 := by
        if hge : 2896 ≤ d then
          have hsq : 2896 * 2896 ≤ d * e := Nat.mul_le_mul hge (Nat.le_trans hge hle)
          unfold mldsaQ at he; omega
        else omega
      exact hno d hdPos (by omega) ⟨e, he⟩
    else
      have heLt : e < 2896 := by
        if hge : 2896 ≤ e then
          have hsq : 2896 * 2896 ≤ d * e := Nat.mul_le_mul (by omega) hge
          unfold mldsaQ at he; omega
        else omega
      exact hno e hePos (by omega) ⟨d, Nat.mul_comm d e ▸ he⟩

/-- **Constructive Primality of FIPS 204 Modulus `mldsaQ = 8380417`**. -/
theorem mldsaQ_isPrime : IsPrime204 mldsaQ :=
  ⟨by decide, mldsaQ_dvd_cases⟩

theorem IsPrime204.dvd_mul {p a b : Nat} (hp : IsPrime204 p)
    (hdvd : p ∣ a * b) (hna : ¬ (p ∣ a)) : p ∣ b := IsPrimeNat.dvd_mul hp hdvd hna

/-! ### §1.2 Canonical Field `Fq204`, Barrett Multiplication & Constructive Bézout Inversion -/

/-- Canonical element of $\mathbb{Z}_q$ ($q = 8380417$). -/
abbrev Fq204 := ModZq mldsaQ

namespace Fq204
abbrev mk (v : Nat) (h : v < mldsaQ) : Fq204 := ModZq.mk v h

theorem ext {a b : Fq204} (h : a.val = b.val) : a = b := by
  exact ModZq.ext h

@[expose] def ofNat (n : Nat) : Fq204 :=
  ⟨n % mldsaQ, Nat.mod_lt n (by decide)⟩

def zero : Fq204 := ⟨0, by decide⟩
def one : Fq204 := ⟨1, by decide⟩

instance : Inhabited Fq204 := ⟨zero⟩

@[simp] theorem zero_val : zero.val = 0 := by rfl
@[simp] theorem one_val : one.val = 1 := by rfl
@[simp] theorem ofNat_val (n : Nat) : (ofNat n).val = n % mldsaQ := by rfl

def add (a b : Fq204) : Fq204 :=
  if h : a.val + b.val < mldsaQ then
    ⟨a.val + b.val, h⟩
  else
    ⟨a.val + b.val - mldsaQ, by have := a.isLt; have := b.isLt; omega⟩

theorem add_val (a b : Fq204) : (add a b).val = (a.val + b.val) % mldsaQ := by
  unfold add
  have ha := a.isLt; have hb := b.isLt
  if hlt : a.val + b.val < mldsaQ then
    simp only [hlt, ↓reduceDIte]
    exact (Nat.mod_eq_of_lt hlt).symm
  else
    simp only [hlt, ↓reduceDIte]
    have hEq : a.val + b.val = (a.val + b.val - mldsaQ) + mldsaQ * 1 := by omega
    conv => rhs; rw [hEq, Nat.add_mul_mod_self_left]
    exact (Nat.mod_eq_of_lt (by omega)).symm

def neg (a : Fq204) : Fq204 :=
  if h : a.val = 0 then ⟨0, by decide⟩ else ⟨mldsaQ - a.val, by have := a.isLt; omega⟩

theorem neg_val (a : Fq204) : (neg a).val = (mldsaQ - a.val) % mldsaQ := by
  unfold neg
  have ha := a.isLt
  if h0 : a.val = 0 then
    simp [h0]
  else
    simp only [h0, ↓reduceDIte]
    exact (Nat.mod_eq_of_lt (by omega)).symm

def sub (a b : Fq204) : Fq204 :=
  if h : b.val ≤ a.val then
    ⟨a.val - b.val, by have := a.isLt; omega⟩
  else
    ⟨a.val + mldsaQ - b.val, by have := a.isLt; have := b.isLt; omega⟩

theorem sub_val (a b : Fq204) : (sub a b).val = (a.val + mldsaQ - b.val) % mldsaQ := by
  unfold sub
  have ha := a.isLt; have hb := b.isLt
  if hle : b.val ≤ a.val then
    simp only [hle, ↓reduceDIte]
    have hEq : a.val + mldsaQ - b.val = (a.val - b.val) + mldsaQ * 1 := by omega
    conv => rhs; rw [hEq, Nat.add_mul_mod_self_left]
    exact (Nat.mod_eq_of_lt (by omega)).symm
  else
    simp only [hle, ↓reduceDIte]
    exact (Nat.mod_eq_of_lt (by omega)).symm

def mul (a b : Fq204) : Fq204 :=
  ⟨(a.val * b.val) % mldsaQ, Nat.mod_lt _ (by decide)⟩

@[simp] theorem mul_val (a b : Fq204) : (mul a b).val = (a.val * b.val) % mldsaQ := by rfl

theorem add_assoc (a b c : Fq204) : add (add a b) c = add a (add b c) :=
  ext <| by rw [add_val, add_val, add_val, add_val, Nat.add_mod_mod, Nat.mod_add_mod, Nat.add_assoc]

theorem add_comm (a b : Fq204) : add a b = add b a :=
  ext <| by rw [add_val, add_val, Nat.add_comm]

theorem zero_add (a : Fq204) : add zero a = a :=
  ext <| by rw [add_val, zero_val, Nat.zero_add, Nat.mod_eq_of_lt a.isLt]

theorem add_zero (a : Fq204) : add a zero = a :=
  ext <| by rw [add_val, zero_val, Nat.add_zero, Nat.mod_eq_of_lt a.isLt]

theorem add_left_neg (a : Fq204) : add (neg a) a = zero :=
  ext <| by
    rw [add_val, neg_val, Nat.mod_add_mod]
    have ha := a.isLt
    have hEq : mldsaQ - a.val + a.val = mldsaQ := by omega
    rw [hEq, Nat.mod_self, zero_val]

theorem add_right_neg (a : Fq204) : add a (neg a) = zero := by
  rw [add_comm, add_left_neg]

theorem sub_eq_add_neg (a b : Fq204) : sub a b = add a (neg b) :=
  ext <| by
    rw [sub_val, add_val, neg_val, Nat.add_mod_mod]
    have hb := b.isLt
    have hEq : a.val + (mldsaQ - b.val) = a.val + mldsaQ - b.val := by omega
    rw [hEq]

theorem mul_assoc (a b c : Fq204) : mul (mul a b) c = mul a (mul b c) :=
  ext <| by rw [mul_val, mul_val, mul_val, mul_val, Nat.mod_mul_mod, Nat.mul_mod_mod, Nat.mul_assoc]

theorem mul_comm (a b : Fq204) : mul a b = mul b a :=
  ext <| by rw [mul_val, mul_val, Nat.mul_comm]

theorem one_mul (a : Fq204) : mul one a = a :=
  ext <| by rw [mul_val, one_val, Nat.one_mul, Nat.mod_eq_of_lt a.isLt]

theorem mul_one (a : Fq204) : mul a one = a :=
  ext <| by rw [mul_val, one_val, Nat.mul_one, Nat.mod_eq_of_lt a.isLt]

theorem mul_zero (a : Fq204) : mul a zero = zero :=
  ext <| by rw [mul_val, zero_val, Nat.mul_zero, Nat.zero_mod]

theorem zero_mul (a : Fq204) : mul zero a = zero :=
  ext <| by rw [mul_val, zero_val, Nat.zero_mul, Nat.zero_mod]

theorem left_distrib (a b c : Fq204) : mul a (add b c) = add (mul a b) (mul a c) :=
  ext <| by
    rw [mul_val, add_val, add_val, mul_val, mul_val,
        Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.left_distrib, Nat.add_mod]

theorem right_distrib (a b c : Fq204) : mul (add a b) c = add (mul a c) (mul b c) :=
  ext <| by
    rw [mul_val, add_val, add_val, mul_val, mul_val,
        Nat.mod_mul_mod, Nat.right_distrib, Nat.add_mod]

theorem add_left_cancel {a b c : Fq204} (h : add a b = add a c) : b = c := by
  have h1 := congrArg (add (neg a)) h
  rwa [← add_assoc, ← add_assoc, add_left_neg, zero_add, zero_add] at h1

theorem sub_zero (a : Fq204) : sub a zero = a := by
  apply ext
  rw [sub_val, zero_val]
  have ha := a.isLt
  have hEq : a.val + mldsaQ - 0 = a.val + mldsaQ * 1 := by omega
  rw [hEq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

theorem mul_neg (a b : Fq204) : mul a (neg b) = neg (mul a b) := by
  apply add_left_cancel (a := mul a b)
  rw [← left_distrib, add_right_neg, mul_zero, add_right_neg]

theorem neg_add (a b : Fq204) : neg (add a b) = add (neg a) (neg b) := by
  apply add_left_cancel (a := add a b)
  rw [add_right_neg, add_assoc a b, ← add_assoc b (neg a), add_comm b (neg a),
      add_assoc (neg a) b, add_right_neg, add_zero, add_right_neg]

def ofInt (z : Int) : Fq204 :=
  ⟨(z % (mldsaQ : Int)).toNat, by
    have := Int.emod_nonneg z (show (mldsaQ : Int) ≠ 0 by decide)
    have := Int.emod_lt_of_pos z (show (0 : Int) < mldsaQ by decide)
    omega⟩

theorem ofInt_val (z : Int) : ((ofInt z).val : Int) = z % (mldsaQ : Int) :=
  Int.toNat_of_nonneg (Int.emod_nonneg z (by decide))

theorem ofInt_nat (a : Fq204) : ofInt (a.val : Int) = a := by
  apply ext; apply Int.ofNat_inj.mp
  rw [ofInt_val]
  exact Int.emod_eq_of_lt (by omega) (by have := a.isLt; omega)

theorem add_int (a b : Fq204) :
    ((add a b).val : Int) = ((a.val : Int) + (b.val : Int)) % (mldsaQ : Int) := by
  rw [add_val, Int.natCast_emod, Int.natCast_add]

theorem sub_int (a b : Fq204) :
    ((sub a b).val : Int) = ((a.val : Int) - (b.val : Int)) % (mldsaQ : Int) := by
  rw [sub_val, Int.natCast_emod, Int.ofNat_sub (by have := b.isLt; omega), Int.natCast_add]
  have he : (a.val : Int) + (mldsaQ : Int) - (b.val : Int) =
      ((a.val : Int) - (b.val : Int)) + (mldsaQ : Int) := by omega
  rw [he, Int.add_emod_right]

theorem mul_int (a b : Fq204) :
    ((mul a b).val : Int) = ((a.val : Int) * (b.val : Int)) % (mldsaQ : Int) := by
  rw [mul_val, Int.natCast_emod, Int.natCast_mul]

theorem ofInt_add (a b : Int) : add (ofInt a) (ofInt b) = ofInt (a + b) := by
  apply ext; apply Int.ofNat_inj.mp
  rw [add_int, ofInt_val, ofInt_val, ofInt_val, ← Int.add_emod]

theorem ofInt_sub (a b : Int) : sub (ofInt a) (ofInt b) = ofInt (a - b) := by
  apply ext; apply Int.ofNat_inj.mp
  rw [sub_int, ofInt_val, ofInt_val, ofInt_val, ← Int.sub_emod]

theorem ofInt_mul (a b : Int) : mul (ofInt a) (ofInt b) = ofInt (a * b) := by
  apply ext; apply Int.ofNat_inj.mp
  rw [mul_int, ofInt_val, ofInt_val, ofInt_val, ← Int.mul_emod]

theorem ofInt_neg (a : Int) : neg (ofInt a) = ofInt (-a) := by
  have h0 : ofInt 0 = zero := by decide
  apply add_left_cancel (a := ofInt a)
  rw [add_right_neg, ofInt_add]
  have hz : a + (-a) = 0 := by omega
  rw [hz, h0]

/-- Centered representative in $(-q/2, q/2] = [-4190208, 4190208]$. -/
def toCenteredInt (a : Fq204) : Int :=
  if a.val ≤ mldsaQ / 2 then (a.val : Int) else (a.val : Int) - (mldsaQ : Int)

/-- Infinity-norm magnitude $|a \bmod^\pm q| \in [0, 4190208]$. -/
def centeredAbs (a : Fq204) : Nat :=
  if a.val ≤ mldsaQ / 2 then a.val else mldsaQ - a.val

theorem ofInt_toCenteredInt (a : Fq204) : ofInt (toCenteredInt a) = a := by
  apply ext; apply Int.ofNat_inj.mp
  rw [ofInt_val]; unfold toCenteredInt
  have ha := a.isLt
  split
  · exact Int.emod_eq_of_lt (by omega) (by omega)
  · have hEq : ((a.val : Int) - (mldsaQ : Int)) + (mldsaQ : Int) = (a.val : Int) := by omega
    rw [← Int.add_emod_right ((a.val : Int) - (mldsaQ : Int)) (mldsaQ : Int), hEq]
    exact Int.emod_eq_of_lt (by omega) (by omega)

theorem toCenteredInt_natAbs (a : Fq204) : (toCenteredInt a).natAbs = centeredAbs a := by
  unfold toCenteredInt centeredAbs
  have ha := a.isLt
  split <;> omega

theorem toCenteredInt_ofInt_eq {z : Int} (hLo : -4190208 ≤ z) (hHi : z ≤ 4190208) :
    toCenteredInt (ofInt z) = z := by
  unfold toCenteredInt
  have hv : ((ofInt z).val : Int) = z % (8380417 : Int) := ofInt_val z
  unfold mldsaQ
  if hz : 0 ≤ z then
    have hmod : z % (8380417 : Int) = z := Int.emod_eq_of_lt hz (by omega)
    rw [hmod] at hv
    split <;> omega
  else
    have hmod : z % (8380417 : Int) = z + 8380417 := by
      rw [← Int.add_emod_right z (8380417 : Int)]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    rw [hmod] at hv
    split <;> omega

end Fq204

/-- Division-free 64-bit Barrett modular multiplication (`fips204_ntt.rs:fq_mul`). -/
def fqMulBarrettSpec (a b : Nat) : Nat :=
  let barrettM64 : Nat := 18446744073709551616 / mldsaQ  -- 2_201_154_512_929
  let prod := a * b
  let qEst := (prod * barrettM64) / 18446744073709551616
  let rem := prod - qEst * mldsaQ
  if rem < mldsaQ then rem else rem - mldsaQ

/-- **`fqMulBarrett_sound`**: hardware-exact 64-bit Barrett multiplication equals `(a * b) % q`
    for all `a, b < 8380417` with zero division instructions and zero underflow. -/
theorem fqMulBarrett_sound {a b : Nat} (ha : a < mldsaQ) (hb : b < mldsaQ) :
    fqMulBarrettSpec a b = (a * b) % mldsaQ := by
  unfold fqMulBarrettSpec mldsaQ at *
  have hprod : a * b ≤ 8380416 * 8380416 := Nat.mul_le_mul (by omega) (by omega)
  dsimp only
  split <;> omega

instance : CommRingOps Fq204 where
  zero := Fq204.zero
  one := Fq204.one
  add := Fq204.add
  mul := Fq204.mul
  neg := Fq204.neg
  sub := Fq204.sub

instance : LawfulCommRing Fq204 where
  add_assoc := Fq204.add_assoc
  add_comm := Fq204.add_comm
  zero_add := Fq204.zero_add
  add_zero := Fq204.add_zero
  add_left_neg := Fq204.add_left_neg
  sub_eq_add_neg := Fq204.sub_eq_add_neg
  mul_assoc := Fq204.mul_assoc
  mul_comm := Fq204.mul_comm
  one_mul := Fq204.one_mul
  mul_one := Fq204.mul_one
  left_distrib := Fq204.left_distrib
  right_distrib := Fq204.right_distrib

instance : NoZeroDivisors Fq204 where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} h := by
    have hval : (a.val * b.val) % mldsaQ = 0 := congrArg ModZq.val h
    have hdvd : mldsaQ ∣ a.val * b.val := Nat.dvd_of_mod_eq_zero hval
    if ha0 : a.val = 0 then
      exact .inl (Fq204.ext ha0)
    else
      have hna : ¬ (mldsaQ ∣ a.val) := fun hda => by
        have hle := Nat.le_of_dvd (by omega) hda
        have := a.isLt; omega
      have hdb := mldsaQ_isPrime.dvd_mul hdvd hna
      if hb0 : b.val = 0 then
        exact .inr (Fq204.ext hb0)
      else
        have hle := Nat.le_of_dvd (by omega) hdb
        have := b.isLt; omega

namespace Fq204

/-- Field power $a^e \in \mathbb{Z}_q$. -/
def pow (a : Fq204) : Nat → Fq204
  | 0 => one
  | k + 1 => mul (pow a k) a

@[simp] theorem pow_val (a : Fq204) : ∀ k : Nat, (pow a k).val = (a.val ^ k) % mldsaQ
  | 0 => by rfl
  | k + 1 => by
    dsimp only [pow]
    rw [mul_val, pow_val a k, Nat.pow_succ, Nat.mod_mul_mod]

theorem pow_add (a : Fq204) (m n : Nat) : pow a (m + n) = mul (pow a m) (pow a n) := by
  apply ext; rw [pow_val, mul_val, pow_val, pow_val, ← Nat.mul_mod, ← Nat.pow_add]

theorem pow_mul (a : Fq204) (m n : Nat) : pow a (m * n) = pow (pow a m) n := by
  induction n with
  | zero => dsimp only [Nat.mul_zero, pow]
  | succ n ih => rw [Nat.mul_succ, pow_add, ih]; dsimp only [pow]

/-- Constructive Bézout field inverse via `extGcd` (`0 ↦ 0`). -/
def inv (a : Fq204) : Fq204 :=
  if a.val = 0 then zero else ofInt (extGcd a.val mldsaQ).2.1

/-- **`Fq204.mul_inv_cancel`**: every nonzero element in $\mathbb{Z}_{8380417}$ has a multiplicative inverse. -/
theorem mul_inv_cancel {a : Fq204} (ha : a ≠ zero) : mul a (inv a) = one := by
  have ha0 : a.val ≠ 0 := fun hz => ha (ext hz)
  unfold inv
  simp only [ha0, ↓reduceIte]
  obtain ⟨hda, hdq⟩ := extGcd_dvd a.val mldsaQ
  have hg1 : (extGcd a.val mldsaQ).1 = 1 := by
    rcases mldsaQ_isPrime.dvd_cases _ hdq with h1 | hqq
    · exact h1
    · rw [hqq] at hda
      have hle := Nat.le_of_dvd (by omega) hda
      have := a.isLt; omega
  have hbez := extGcd_bezout a.val mldsaQ
  rw [hg1] at hbez
  generalize hx : (extGcd a.val mldsaQ).2.1 = x at hbez ⊢
  generalize hy : (extGcd a.val mldsaQ).2.2 = y at hbez
  rw [← ofInt_nat a, ofInt_mul]
  apply ext; apply Int.ofNat_inj.mp
  rw [ofInt_val, one_val]
  have hEq : (a.val : Int) * x = (1 : Int) + (mldsaQ : Int) * (-y) := by
    rw [Int.mul_neg]
    omega
  rw [hEq, Int.add_mul_emod_self_left]
  decide

theorem inv_mul_cancel {a : Fq204} (ha : a ≠ zero) : mul (inv a) a = one := by
  rw [mul_comm, mul_inv_cancel ha]

end Fq204

instance : LawfulField Fq204 where
  inv := Fq204.inv
  zero_ne_one := by decide
  mul_inv_cancel := Fq204.mul_inv_cancel

/-! ### §1.3 256-Point Negacyclic Ring $R_q = \mathbb{Z}_q[X]/(X^{256} + 1)$ & 8-Stage NTT Isomorphism -/

/-- Primitive 512-th root $\zeta = 1753 \in \mathbb{Z}_{8380417}$. -/
def mldsaZeta : Fq204 := ⟨1753, by decide⟩

/-- Multiplicative inverse $2^{-1} \equiv 4190209 \pmod{8380417}$. -/
def mldsaInv2 : Fq204 := ⟨4190209, by decide⟩

/-- Multiplicative inverse $256^{-1} \equiv 8347681 \pmod{8380417}$. -/
def mldsaInv256 : Fq204 := ⟨8347681, by decide⟩

private theorem fq204_sq_eq_pow2 (a : Fq204) : Fq204.pow a 2 = Fq204.mul a a := by
  dsimp only [Fq204.pow]; rw [Fq204.one_mul]

theorem mldsaZeta_pow256_eq_neg_one :
    Fq204.pow mldsaZeta 256 = Fq204.neg Fq204.one := by
  have h256 : (256 : Nat) = 2 * (2 * (2 * (2 * (2 * (2 * (2 * 2)))))) := rfl
  rw [h256, Fq204.pow_mul, Fq204.pow_mul, Fq204.pow_mul, Fq204.pow_mul,
      Fq204.pow_mul, Fq204.pow_mul, Fq204.pow_mul,
      fq204_sq_eq_pow2, fq204_sq_eq_pow2, fq204_sq_eq_pow2, fq204_sq_eq_pow2,
      fq204_sq_eq_pow2, fq204_sq_eq_pow2, fq204_sq_eq_pow2, fq204_sq_eq_pow2]
  decide

theorem mldsaZeta_pow512_eq_one :
    Fq204.pow mldsaZeta 512 = Fq204.one := by
  have h512 : (512 : Nat) = 256 * 2 := rfl
  rw [h512, Fq204.pow_mul, mldsaZeta_pow256_eq_neg_one]
  decide

theorem mldsa_two_mul_inv2 : Fq204.mul (Fq204.ofNat 2) mldsaInv2 = Fq204.one := by decide

/-- Inductive binary tree of $2^d$ field elements (`0` `module` opacity mismatch). -/
inductive PolyTree : Nat → Type where
  | leaf (x : Fq204) : PolyTree 0
  | branch {d : Nat} (lo hi : PolyTree d) : PolyTree (d + 1)
  deriving DecidableEq, Repr

/-- Exact 256-coefficient polynomial / NTT vector over $\mathbb{Z}_{8380417}$ ($2^8 = 256$). -/
abbrev Poly256 := PolyTree 8

namespace PolyTree

def zero : (d : Nat) → PolyTree d
  | 0 => .leaf Fq204.zero
  | d + 1 => .branch (zero d) (zero d)

def constUnit : (d : Nat) → PolyTree d
  | 0 => .leaf Fq204.one
  | d + 1 => .branch (constUnit d) (zero d)

def ones : (d : Nat) → PolyTree d
  | 0 => .leaf Fq204.one
  | d + 1 => .branch (ones d) (ones d)

instance (d : Nat) : Inhabited (PolyTree d) := ⟨zero d⟩

def add : {d : Nat} → PolyTree d → PolyTree d → PolyTree d
  | 0, .leaf a, .leaf b => .leaf (Fq204.add a b)
  | _ + 1, .branch a0 a1, .branch b0 b1 => .branch (add a0 b0) (add a1 b1)

def sub : {d : Nat} → PolyTree d → PolyTree d → PolyTree d
  | 0, .leaf a, .leaf b => .leaf (Fq204.sub a b)
  | _ + 1, .branch a0 a1, .branch b0 b1 => .branch (sub a0 b0) (sub a1 b1)

def neg : {d : Nat} → PolyTree d → PolyTree d
  | 0, .leaf a => .leaf (Fq204.neg a)
  | _ + 1, .branch a0 a1 => .branch (neg a0) (neg a1)

def scale (k : Fq204) : {d : Nat} → PolyTree d → PolyTree d
  | 0, .leaf a => .leaf (Fq204.mul k a)
  | _ + 1, .branch a0 a1 => .branch (scale k a0) (scale k a1)

def pointwiseMul : {d : Nat} → PolyTree d → PolyTree d → PolyTree d
  | 0, .leaf a, .leaf b => .leaf (Fq204.mul a b)
  | _ + 1, .branch a0 a1, .branch b0 b1 => .branch (pointwiseMul a0 b0) (pointwiseMul a1 b1)

def toList : {d : Nat} → PolyTree d → List Fq204
  | 0, .leaf x => [x]
  | _ + 1, .branch lo hi => toList lo ++ toList hi

@[simp] theorem length_toList : ∀ {d : Nat} (p : PolyTree d), (toList p).length = 2 ^ d
  | 0, .leaf _ => by rfl
  | d + 1, .branch lo hi => by
    simp only [toList, List.length_append, length_toList, Nat.pow_succ]
    omega

def ofList : (d : Nat) → List Fq204 → PolyTree d
  | 0, xs => .leaf (xs.headD Fq204.zero)
  | d + 1, xs =>
    let half := 2 ^ d
    .branch (ofList d (xs.take half)) (ofList d (xs.drop half))

theorem ofList_toList : ∀ {d : Nat} (p : PolyTree d), ofList d (toList p) = p
  | 0, .leaf _ => by rfl
  | d + 1, .branch lo hi => by
    simp only [toList, ofList]
    have hlen : (toList lo).length = 2 ^ d := length_toList lo
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
        List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega),
        List.nil_append, ofList_toList lo, ofList_toList hi]

theorem toList_ofList : ∀ {d : Nat} {xs : List Fq204}, xs.length = 2 ^ d → toList (ofList d xs) = xs
  | 0, xs, hlen => by
    cases xs with
    | nil => exact absurd hlen (by decide)
    | cons x rest =>
      cases rest with
      | nil => rfl
      | cons _ _ => simp only [List.length_cons] at hlen; omega
  | d + 1, xs, hlen => by
    simp only [ofList, toList]
    have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; omega
    have htake : (xs.take (2 ^ d)).length = 2 ^ d := by
      rw [List.length_take, hlen, hpow]; omega
    have hdrop : (xs.drop (2 ^ d)).length = 2 ^ d := by
      rw [List.length_drop, hlen, hpow]; omega
    rw [toList_ofList htake, toList_ofList hdrop, List.take_append_drop]

/-- Infinity norm $\max_{j} |p_j \bmod^\pm q|$ across all $2^d$ coefficients. -/
def infNorm : {d : Nat} → PolyTree d → Nat
  | 0, .leaf x => Fq204.centeredAbs x
  | _ + 1, .branch lo hi => max (infNorm lo) (infNorm hi)

/-- Taxicab ($\ell_1$) norm $\sum_j |p_j \bmod^\pm q|$. -/
def l1Norm : {d : Nat} → PolyTree d → Nat
  | 0, .leaf x => Fq204.centeredAbs x
  | _ + 1, .branch lo hi => l1Norm lo + l1Norm hi

/-- Leafwise predicate over a single `PolyTree d`. -/
def AllLeaves : {d : Nat} → (Fq204 → Prop) → PolyTree d → Prop
  | 0, P, .leaf a => P a
  | _ + 1, P, .branch a0 a1 => AllLeaves P a0 ∧ AllLeaves P a1

end PolyTree

/-- Exact 8-stage Cooley–Tukey radix-2 butterfly recursion (`fips204_ntt.rs:Poly256::ntt`). -/
def nttStage : (d : Nat) → Nat → PolyTree d → PolyTree d
  | 0, _, .leaf x => .leaf x
  | d + 1, e, .branch lo hi =>
    let z := Fq204.pow mldsaZeta (e / 2)
    let zh := PolyTree.scale z hi
    .branch (nttStage d (e / 2) (PolyTree.add lo zh))
            (nttStage d (e / 2 + 256) (PolyTree.sub lo zh))

/-- Exact 8-stage Gentleman–Sande inverse butterfly recursion (`fips204_ntt.rs:Poly256::inv_ntt`). -/
def invNttStage : (d : Nat) → Nat → PolyTree d → PolyTree d
  | 0, _, .leaf x => .leaf x
  | d + 1, e, .branch u v =>
    let u' := invNttStage d (e / 2) u
    let v' := invNttStage d (e / 2 + 256) v
    let zInv := Fq204.inv (Fq204.pow mldsaZeta (e / 2))
    .branch (PolyTree.scale mldsaInv2 (PolyTree.add u' v'))
            (PolyTree.scale (Fq204.mul mldsaInv2 zInv) (PolyTree.sub u' v'))

/-- Forward 256-point NIST FIPS 204 NTT (`Algorithm 41`). -/
def fips204Ntt (p : Poly256) : Poly256 := nttStage 8 256 p

/-- Inverse 256-point NIST FIPS 204 NTT (`Algorithm 42`). -/
def fips204InvNtt (u : Poly256) : Poly256 := invNttStage 8 256 u

private theorem mldsaZeta_pow_ne_zero (k : Nat) : Fq204.pow mldsaZeta k ≠ Fq204.zero := by
  induction k with
  | zero => decide
  | succ k ih =>
    intro h0
    rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h0 with h1 | h2
    · exact ih h1
    · exact absurd h2 (by decide)

private theorem polyTree_butterfly_left_inv {d : Nat} (z : Fq204) (hz : z ≠ Fq204.zero)
    (lo hi : PolyTree d) :
    let zh := PolyTree.scale z hi
    let u := PolyTree.add lo zh
    let v := PolyTree.sub lo zh
    PolyTree.branch (PolyTree.scale mldsaInv2 (PolyTree.add u v))
      (PolyTree.scale (Fq204.mul mldsaInv2 (Fq204.inv z)) (PolyTree.sub u v)) =
      PolyTree.branch lo hi := by
  induction d with
  | zero =>
    cases lo with | leaf a =>
    cases hi with | leaf b =>
    dsimp only [PolyTree.scale, PolyTree.add, PolyTree.sub]
    have hTwo : Fq204.add Fq204.one Fq204.one = Fq204.ofNat 2 := by decide
    have h1 : Fq204.mul mldsaInv2 (Fq204.add (Fq204.add a (Fq204.mul z b)) (Fq204.sub a (Fq204.mul z b))) = a := by
      have hsum : Fq204.add (Fq204.add a (Fq204.mul z b)) (Fq204.sub a (Fq204.mul z b)) =
          Fq204.mul (Fq204.ofNat 2) a := by
        rw [Fq204.sub_eq_add_neg, Fq204.add_assoc a (Fq204.mul z b),
            ← Fq204.add_assoc (Fq204.mul z b) a, Fq204.add_comm (Fq204.mul z b) a,
            Fq204.add_assoc a (Fq204.mul z b), Fq204.add_right_neg, Fq204.add_zero]
        calc Fq204.add a a = Fq204.add (Fq204.mul Fq204.one a) (Fq204.mul Fq204.one a) := by
              rw [Fq204.one_mul]
        _ = Fq204.mul (Fq204.ofNat 2) a := by rw [← Fq204.right_distrib, hTwo]
      rw [hsum, ← Fq204.mul_assoc, Fq204.mul_comm mldsaInv2, mldsa_two_mul_inv2, Fq204.one_mul]
    have h2 : Fq204.mul (Fq204.mul mldsaInv2 (Fq204.inv z))
        (Fq204.sub (Fq204.add a (Fq204.mul z b)) (Fq204.sub a (Fq204.mul z b))) = b := by
      have hdiff : Fq204.sub (Fq204.add a (Fq204.mul z b)) (Fq204.sub a (Fq204.mul z b)) =
          Fq204.mul (Fq204.ofNat 2) (Fq204.mul z b) := by
        apply Fq204.add_left_cancel (a := Fq204.sub a (Fq204.mul z b))
        rw [Fq204.sub_eq_add_neg (Fq204.add a _), Fq204.add_comm (Fq204.sub a _),
            Fq204.add_assoc, Fq204.add_left_neg, Fq204.add_zero]
        calc Fq204.add a (Fq204.mul z b)
          _ = Fq204.add (Fq204.sub a (Fq204.mul z b)) (Fq204.add (Fq204.mul z b) (Fq204.mul z b)) := by
            rw [Fq204.sub_eq_add_neg, Fq204.add_assoc, ← Fq204.add_assoc (Fq204.neg _),
                Fq204.add_left_neg, Fq204.zero_add]
          _ = Fq204.add (Fq204.sub a (Fq204.mul z b)) (Fq204.mul (Fq204.ofNat 2) (Fq204.mul z b)) := by
            congr 1
            calc Fq204.add (Fq204.mul z b) (Fq204.mul z b)
              _ = Fq204.add (Fq204.mul Fq204.one (Fq204.mul z b)) (Fq204.mul Fq204.one (Fq204.mul z b)) := by
                rw [Fq204.one_mul]
              _ = Fq204.mul (Fq204.ofNat 2) (Fq204.mul z b) := by rw [← Fq204.right_distrib, hTwo]
      rw [hdiff, Fq204.mul_comm mldsaInv2 (Fq204.inv z), Fq204.mul_assoc (Fq204.inv z) mldsaInv2,
          ← Fq204.mul_assoc mldsaInv2 (Fq204.ofNat 2), Fq204.mul_comm mldsaInv2 (Fq204.ofNat 2),
          mldsa_two_mul_inv2, Fq204.one_mul, ← Fq204.mul_assoc, Fq204.inv_mul_cancel hz, Fq204.one_mul]
    rw [h1, h2]
  | succ d ih =>
    cases lo with | branch lo0 lo1 =>
    cases hi with | branch hi0 hi1 =>
    have ih0 := PolyTree.branch.inj (ih lo0 hi0)
    have ih1 := PolyTree.branch.inj (ih lo1 hi1)
    simp only [PolyTree.scale, PolyTree.add, PolyTree.sub, ih0.1, ih1.1, ih0.2, ih1.2]

private theorem polyTree_butterfly_right_inv {d : Nat} (z : Fq204) (hz : z ≠ Fq204.zero)
    (u v : PolyTree d) :
    let lo := PolyTree.scale mldsaInv2 (PolyTree.add u v)
    let hi := PolyTree.scale (Fq204.mul mldsaInv2 (Fq204.inv z)) (PolyTree.sub u v)
    let zh := PolyTree.scale z hi
    PolyTree.branch (PolyTree.add lo zh) (PolyTree.sub lo zh) = PolyTree.branch u v := by
  induction d with
  | zero =>
    cases u with | leaf a =>
    cases v with | leaf b =>
    dsimp only [PolyTree.scale, PolyTree.add, PolyTree.sub]
    have hTwo : Fq204.add Fq204.one Fq204.one = Fq204.ofNat 2 := by decide
    have hzh : Fq204.mul z (Fq204.mul (Fq204.mul mldsaInv2 (Fq204.inv z)) (Fq204.sub a b)) =
        Fq204.mul mldsaInv2 (Fq204.sub a b) := by
      rw [Fq204.mul_comm mldsaInv2 (Fq204.inv z), ← Fq204.mul_assoc z,
          ← Fq204.mul_assoc z (Fq204.inv z), Fq204.mul_inv_cancel hz, Fq204.one_mul]
    rw [hzh, ← Fq204.left_distrib]
    have hsum : Fq204.add (Fq204.add a b) (Fq204.sub a b) = Fq204.mul (Fq204.ofNat 2) a := by
      rw [Fq204.sub_eq_add_neg, Fq204.add_assoc a b, ← Fq204.add_assoc b a,
          Fq204.add_comm b a, Fq204.add_assoc a b, Fq204.add_right_neg, Fq204.add_zero]
      calc Fq204.add a a = Fq204.add (Fq204.mul Fq204.one a) (Fq204.mul Fq204.one a) := by
            rw [Fq204.one_mul]
      _ = Fq204.mul (Fq204.ofNat 2) a := by rw [← Fq204.right_distrib, hTwo]
    have h1 : Fq204.mul mldsaInv2 (Fq204.add (Fq204.add a b) (Fq204.sub a b)) = a := by
      rw [hsum, ← Fq204.mul_assoc, Fq204.mul_comm mldsaInv2, mldsa_two_mul_inv2, Fq204.one_mul]
    have h2 : Fq204.sub (Fq204.mul mldsaInv2 (Fq204.add a b)) (Fq204.mul mldsaInv2 (Fq204.sub a b)) = b := by
      apply Fq204.add_left_cancel (a := Fq204.mul mldsaInv2 (Fq204.sub a b))
      rw [Fq204.sub_eq_add_neg (Fq204.mul mldsaInv2 (Fq204.add a b)),
          Fq204.add_comm (Fq204.mul mldsaInv2 (Fq204.sub a b)),
          Fq204.add_assoc, Fq204.add_left_neg, Fq204.add_zero]
      calc Fq204.mul mldsaInv2 (Fq204.add a b)
        _ = Fq204.add (Fq204.mul mldsaInv2 (Fq204.sub a b)) (Fq204.mul mldsaInv2 (Fq204.add b b)) := by
          rw [← Fq204.left_distrib]
          congr 1
          rw [Fq204.sub_eq_add_neg, Fq204.add_assoc, ← Fq204.add_assoc (Fq204.neg b),
              Fq204.add_left_neg, Fq204.zero_add]
        _ = Fq204.add (Fq204.mul mldsaInv2 (Fq204.sub a b)) b := by
          congr 1
          have hbb : Fq204.add b b = Fq204.mul (Fq204.ofNat 2) b := by
            calc Fq204.add b b = Fq204.add (Fq204.mul Fq204.one b) (Fq204.mul Fq204.one b) := by
                  rw [Fq204.one_mul]
            _ = Fq204.mul (Fq204.ofNat 2) b := by rw [← Fq204.right_distrib, hTwo]
          rw [hbb, ← Fq204.mul_assoc, Fq204.mul_comm mldsaInv2, mldsa_two_mul_inv2, Fq204.one_mul]
    rw [h1, h2]
  | succ d ih =>
    cases u with | branch u0 u1 =>
    cases v with | branch v0 v1 =>
    have ih0 := PolyTree.branch.inj (ih u0 v0)
    have ih1 := PolyTree.branch.inj (ih u1 v1)
    simp only [PolyTree.scale, PolyTree.add, PolyTree.sub, ih0.1, ih1.1, ih0.2, ih1.2]

private theorem invNttStage_nttStage : ∀ (d e : Nat) (p : PolyTree d),
    invNttStage d e (nttStage d e p) = p
  | 0, _, .leaf _ => rfl
  | d + 1, e, .branch lo hi => by
    simp only [nttStage, invNttStage, invNttStage_nttStage d]
    exact polyTree_butterfly_left_inv (Fq204.pow mldsaZeta (e / 2)) (mldsaZeta_pow_ne_zero _) lo hi

private theorem nttStage_invNttStage : ∀ (d e : Nat) (u : PolyTree d),
    nttStage d e (invNttStage d e u) = u
  | 0, _, .leaf _ => rfl
  | d + 1, e, .branch u v => by
    simp only [invNttStage]
    have h := PolyTree.branch.inj <|
      polyTree_butterfly_right_inv (Fq204.pow mldsaZeta (e / 2)) (mldsaZeta_pow_ne_zero _)
        (invNttStage d (e / 2) u) (invNttStage d (e / 2 + 256) v)
    simp only [nttStage, h.1, h.2, nttStage_invNttStage d]

/-- **`fips204InvNtt_ntt`**: 256-point FIPS 204 inverse NTT left-inverts forward NTT. -/
theorem fips204InvNtt_ntt (p : Poly256) : fips204InvNtt (fips204Ntt p) = p :=
  invNttStage_nttStage 8 256 p

/-- **`fips204Ntt_invNtt`**: 256-point FIPS 204 forward NTT right-inverts inverse NTT. -/
theorem fips204Ntt_invNtt (u : Poly256) : fips204Ntt (fips204InvNtt u) = u :=
  nttStage_invNttStage 8 256 u

/-! #### Coefficient-Domain Polynomial Evaluation & Negacyclic Convolution -/

/-- Horner polynomial evaluation $\sum_{j=0}^{m-1} p_j \omega^j$ over $\mathbb{Z}_q$. -/
def evalPoly204 : List Fq204 → Fq204 → Fq204
  | [], _ => Fq204.zero
  | c :: cs, w => Fq204.add c (Fq204.mul w (evalPoly204 cs w))

theorem evalPoly204_append : ∀ (xs ys : List Fq204) (w : Fq204),
    evalPoly204 (xs ++ ys) w =
      Fq204.add (evalPoly204 xs w) (Fq204.mul (Fq204.pow w xs.length) (evalPoly204 ys w))
  | [], ys, w => by
    dsimp only [List.nil_append, evalPoly204, List.length_nil, Fq204.pow]
    rw [Fq204.zero_add, Fq204.one_mul]
  | c :: cs, ys, w => by
    simp only [List.cons_append, evalPoly204, evalPoly204_append cs ys w, List.length_cons,
      Fq204.pow, Fq204.left_distrib, Fq204.add_assoc]
    congr 2
    rw [← Fq204.mul_assoc, Fq204.mul_comm w (Fq204.pow w cs.length)]

def addPolyList : List Fq204 → List Fq204 → List Fq204
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => Fq204.add x y :: addPolyList xs ys

def subPolyList : List Fq204 → List Fq204 → List Fq204
  | [], [] => []
  | [], y :: ys => Fq204.neg y :: subPolyList [] ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => Fq204.sub x y :: subPolyList xs ys

def scalePolyList (k : Fq204) : List Fq204 → List Fq204
  | [] => []
  | x :: xs => Fq204.mul k x :: scalePolyList k xs

/-- Unreduced Cauchy product of two polynomials in $\mathbb{Z}_q[X]$. -/
def cauchyMulList : List Fq204 → List Fq204 → List Fq204
  | [], _ => []
  | a :: as, bs => addPolyList (scalePolyList a bs) (Fq204.zero :: cauchyMulList as bs)

theorem evalPoly204_addPolyList : ∀ (xs ys : List Fq204) (w : Fq204),
    evalPoly204 (addPolyList xs ys) w = Fq204.add (evalPoly204 xs w) (evalPoly204 ys w)
  | [], ys, w => by dsimp only [addPolyList, evalPoly204]; rw [Fq204.zero_add]
  | x :: xs, [], w => by dsimp only [addPolyList, evalPoly204]; rw [Fq204.add_zero]
  | x :: xs, y :: ys, w => by
    simp only [addPolyList, evalPoly204, evalPoly204_addPolyList xs ys w, Fq204.left_distrib]
    rw [Fq204.add_assoc x y,
        ← Fq204.add_assoc y (Fq204.mul w (evalPoly204 xs w)),
        Fq204.add_comm y (Fq204.mul w (evalPoly204 xs w)),
        Fq204.add_assoc (Fq204.mul w (evalPoly204 xs w)) y,
        ← Fq204.add_assoc x (Fq204.mul w (evalPoly204 xs w))]

theorem evalPoly204_subPolyList : ∀ (xs ys : List Fq204) (w : Fq204),
    evalPoly204 (subPolyList xs ys) w = Fq204.sub (evalPoly204 xs w) (evalPoly204 ys w)
  | [], [], _ => by dsimp only [subPolyList, evalPoly204]; rw [Fq204.sub_zero]
  | [], y :: ys, w => by
    simp only [subPolyList, evalPoly204, evalPoly204_subPolyList [] ys w]
    rw [Fq204.sub_eq_add_neg, Fq204.zero_add, Fq204.sub_eq_add_neg Fq204.zero,
        Fq204.zero_add, Fq204.mul_neg, Fq204.neg_add]
  | x :: xs, [], w => by dsimp only [subPolyList, evalPoly204]; rw [Fq204.sub_zero]
  | x :: xs, y :: ys, w => by
    simp only [subPolyList, evalPoly204, evalPoly204_subPolyList xs ys w,
      Fq204.sub_eq_add_neg, Fq204.left_distrib, Fq204.mul_neg, Fq204.neg_add]
    rw [Fq204.add_assoc x, ← Fq204.add_assoc (Fq204.neg y),
        Fq204.add_comm (Fq204.neg y) (Fq204.mul w _),
        Fq204.add_assoc (Fq204.mul w _), ← Fq204.add_assoc x]

theorem evalPoly204_scalePolyList (k : Fq204) : ∀ (xs : List Fq204) (w : Fq204),
    evalPoly204 (scalePolyList k xs) w = Fq204.mul k (evalPoly204 xs w)
  | [], _ => by dsimp only [scalePolyList, evalPoly204]; rw [Fq204.mul_zero]
  | x :: xs, w => by
    simp only [scalePolyList, evalPoly204, evalPoly204_scalePolyList k xs w, Fq204.left_distrib]
    congr 1
    rw [← Fq204.mul_assoc, Fq204.mul_comm w k, Fq204.mul_assoc]

theorem evalPoly204_cauchyMulList : ∀ (xs ys : List Fq204) (w : Fq204),
    evalPoly204 (cauchyMulList xs ys) w = Fq204.mul (evalPoly204 xs w) (evalPoly204 ys w)
  | [], ys, _ => by dsimp only [cauchyMulList, evalPoly204]; rw [Fq204.zero_mul]
  | a :: as, ys, w => by
    simp only [cauchyMulList, evalPoly204, evalPoly204_addPolyList, evalPoly204_scalePolyList,
      Fq204.zero_add, evalPoly204_cauchyMulList as ys w, Fq204.right_distrib, Fq204.mul_assoc]

private theorem length_addPolyList : ∀ (xs ys : List Fq204),
    (addPolyList xs ys).length = max xs.length ys.length
  | [], ys => by simp [addPolyList]
  | x :: xs, [] => by simp [addPolyList]
  | _ :: xs, _ :: ys => by simp [addPolyList, length_addPolyList xs ys, Nat.succ_max_succ]

private theorem length_subPolyList_left : ∀ (xs ys : List Fq204),
    ys.length ≤ xs.length → (subPolyList xs ys).length = xs.length
  | xs, [], _ => by cases xs <;> rfl
  | [], _ :: _, h => by simp at h
  | _ :: xs, _ :: ys, h => by
    simp only [List.length_cons] at h
    simp [subPolyList, length_subPolyList_left xs ys (by omega)]

private theorem length_scalePolyList (k : Fq204) : ∀ (xs : List Fq204),
    (scalePolyList k xs).length = xs.length
  | [] => rfl
  | _ :: xs => by simp [scalePolyList, length_scalePolyList k xs]

private theorem length_cauchyMulList : ∀ (xs ys : List Fq204),
    xs ≠ [] → ys ≠ [] → (cauchyMulList xs ys).length = xs.length + ys.length - 1
  | [], _, h, _ => False.elim (h rfl)
  | [a], ys, _, hys => by
    have hpos : 1 ≤ ys.length := by
      cases ys with
      | nil => exact False.elim (hys rfl)
      | cons _ _ => simp
    dsimp only [cauchyMulList]
    rw [length_addPolyList, length_scalePolyList]
    simp only [List.length_cons, List.length_nil]
    omega
  | a :: b :: as, ys, _, hys => by
    have hpos : 1 ≤ ys.length := by
      cases ys with
      | nil => exact False.elim (hys rfl)
      | cons _ _ => simp
    have ih := length_cauchyMulList (b :: as) ys (by simp) hys
    change (addPolyList (scalePolyList a ys) (Fq204.zero :: cauchyMulList (b :: as) ys)).length =
      (a :: b :: as).length + ys.length - 1
    rw [length_addPolyList, length_scalePolyList, List.length_cons, ih]
    simp only [List.length_cons]
    omega

/-- Coefficient-domain negacyclic multiplication in $\mathbb{Z}_q[X]/(X^{256} + 1)$ (`X^256 ≡ -1`). -/
def negacyclicMulList (xs ys : List Fq204) : List Fq204 :=
  let prod := cauchyMulList xs ys
  subPolyList (prod.take 256) (prod.drop 256)

/-- Coefficient-domain negacyclic multiplication on `Poly256`. -/
def negacyclicMul (a b : Poly256) : Poly256 :=
  PolyTree.ofList 8 (negacyclicMulList (PolyTree.toList a) (PolyTree.toList b))

theorem length_negacyclicMulList {xs ys : List Fq204}
    (hx : xs.length = 256) (hy : ys.length = 256) :
    (negacyclicMulList xs ys).length = 256 := by
  unfold negacyclicMulList
  have hxNe : xs ≠ [] := by intro h; rw [h] at hx; simp at hx
  have hyNe : ys ≠ [] := by intro h; rw [h] at hy; simp at hy
  have hlen : (cauchyMulList xs ys).length = 511 := by
    rw [length_cauchyMulList xs ys hxNe hyNe, hx, hy]
  have htake : ((cauchyMulList xs ys).take 256).length = 256 := by simp [hlen]
  have hdrop : ((cauchyMulList xs ys).drop 256).length = 255 := by simp [hlen]
  rw [length_subPolyList_left _ _ (by omega), htake]

/-- Evaluation at any root $\omega$ of $X^{256} + 1 = 0$ ($\omega^{256} = -1$) is a ring homomorphism. -/
theorem evalPoly204_negacyclicMulList {xs ys : List Fq204}
    (hx : xs.length = 256) (hy : ys.length = 256)
    {w : Fq204} (hw : Fq204.pow w 256 = Fq204.neg Fq204.one) :
    evalPoly204 (negacyclicMulList xs ys) w =
      Fq204.mul (evalPoly204 xs w) (evalPoly204 ys w) := by
  unfold negacyclicMulList
  have hxNe : xs ≠ [] := by intro h; rw [h] at hx; simp at hx
  have hyNe : ys ≠ [] := by intro h; rw [h] at hy; simp at hy
  have hlen : (cauchyMulList xs ys).length = 511 := by
    rw [length_cauchyMulList xs ys hxNe hyNe, hx, hy]
  let prod := cauchyMulList xs ys
  have hsplit : prod = prod.take 256 ++ prod.drop 256 := (List.take_append_drop 256 prod).symm
  have htakeLen : (prod.take 256).length = 256 := by dsimp [prod]; simp [hlen]
  have hevalProd : evalPoly204 prod w = Fq204.mul (evalPoly204 xs w) (evalPoly204 ys w) :=
    evalPoly204_cauchyMulList xs ys w
  rw [← hevalProd, hsplit, evalPoly204_append, htakeLen, hw, evalPoly204_subPolyList,
      Fq204.sub_eq_add_neg]
  congr 1
  rw [Fq204.mul_comm (Fq204.neg Fq204.one), Fq204.mul_neg, Fq204.mul_one]

/-! #### Connecting 8-Stage `nttStage` Leaves to `evalPoly204` at Roots of $X^{256} + 1$ -/

/-- Tree of evaluation roots generated by the FIPS 204 radix-2 twist `e ↦ (e/2, e/2 + 256)`. -/
def rootTree : (d : Nat) → Nat → PolyTree d
  | 0, e => .leaf (Fq204.pow mldsaZeta e)
  | d + 1, e => .branch (rootTree d (e / 2)) (rootTree d (e / 2 + 256))

/-- Map polynomial evaluation `evalPoly204 coeffs` across every root in a `PolyTree d`. -/
def evalAtTree (coeffs : List Fq204) : {d : Nat} → PolyTree d → PolyTree d
  | 0, .leaf w => .leaf (evalPoly204 coeffs w)
  | _ + 1, .branch rL rR => .branch (evalAtTree coeffs rL) (evalAtTree coeffs rR)

private theorem addPolyList_append : ∀ {xs1 xs2 ys1 ys2 : List Fq204},
    xs1.length = ys1.length →
    addPolyList (xs1 ++ xs2) (ys1 ++ ys2) = addPolyList xs1 ys1 ++ addPolyList xs2 ys2
  | [], _, [], _, _ => rfl
  | [], _, _ :: _, _, h => (Nat.succ_ne_zero _ h.symm).elim
  | _ :: _, _, [], _, h => (Nat.succ_ne_zero _ h).elim
  | _ :: xs1, xs2, _ :: ys1, ys2, h => by
    simp only [List.length_cons] at h
    simp [addPolyList, addPolyList_append (Nat.succ.inj h)]

private theorem subPolyList_append : ∀ {xs1 xs2 ys1 ys2 : List Fq204},
    xs1.length = ys1.length →
    subPolyList (xs1 ++ xs2) (ys1 ++ ys2) = subPolyList xs1 ys1 ++ subPolyList xs2 ys2
  | [], _, [], _, _ => rfl
  | [], _, _ :: _, _, h => (Nat.succ_ne_zero _ h.symm).elim
  | _ :: _, _, [], _, h => (Nat.succ_ne_zero _ h).elim
  | _ :: xs1, xs2, _ :: ys1, ys2, h => by
    simp only [List.length_cons] at h
    simp [subPolyList, subPolyList_append (Nat.succ.inj h)]

private theorem scalePolyList_append (k : Fq204) : ∀ (xs1 xs2 : List Fq204),
    scalePolyList k (xs1 ++ xs2) = scalePolyList k xs1 ++ scalePolyList k xs2
  | [], _ => rfl
  | _ :: xs1, xs2 => by simp [scalePolyList, scalePolyList_append k xs1 xs2]

private theorem toList_addTree : ∀ {d : Nat} (a b : PolyTree d),
    PolyTree.toList (PolyTree.add a b) = addPolyList (PolyTree.toList a) (PolyTree.toList b)
  | 0, .leaf _, .leaf _ => rfl
  | _ + 1, .branch a0 a1, .branch b0 b1 => by
    simp only [PolyTree.add, PolyTree.toList, toList_addTree]
    exact (addPolyList_append (by rw [PolyTree.length_toList, PolyTree.length_toList])).symm

private theorem toList_subTree : ∀ {d : Nat} (a b : PolyTree d),
    PolyTree.toList (PolyTree.sub a b) = subPolyList (PolyTree.toList a) (PolyTree.toList b)
  | 0, .leaf _, .leaf _ => rfl
  | _ + 1, .branch a0 a1, .branch b0 b1 => by
    simp only [PolyTree.sub, PolyTree.toList, toList_subTree]
    exact (subPolyList_append (by rw [PolyTree.length_toList, PolyTree.length_toList])).symm

private theorem toList_scaleTree (k : Fq204) : ∀ {d : Nat} (a : PolyTree d),
    PolyTree.toList (PolyTree.scale k a) = scalePolyList k (PolyTree.toList a)
  | 0, .leaf _ => rfl
  | _ + 1, .branch a0 a1 => by
    simp only [PolyTree.scale, PolyTree.toList, toList_scaleTree k, scalePolyList_append]

private theorem allLeaves_imp {P Q : Fq204 → Prop} (hImp : ∀ x, P x → Q x) :
    ∀ {d : Nat} {r : PolyTree d}, PolyTree.AllLeaves P r → PolyTree.AllLeaves Q r
  | 0, .leaf _, h => hImp _ h
  | _ + 1, .branch _ _, h => ⟨allLeaves_imp hImp h.1, allLeaves_imp hImp h.2⟩

private theorem evalAtTree_congr {c1 c2 : List Fq204} {P : Fq204 → Prop}
    (hEq : ∀ w, P w → evalPoly204 c1 w = evalPoly204 c2 w) :
    ∀ {d : Nat} {r : PolyTree d}, PolyTree.AllLeaves P r → evalAtTree c1 r = evalAtTree c2 r
  | 0, .leaf w, hw => congrArg PolyTree.leaf (hEq w hw)
  | _ + 1, .branch _ _, h => by
    simp only [evalAtTree, evalAtTree_congr hEq h.1, evalAtTree_congr hEq h.2]

private theorem rootTree_allLeavesPow :
    ∀ (d e : Nat), 2 ^ d ∣ e → d ≤ 8 →
      PolyTree.AllLeaves (fun w => Fq204.pow w (2 ^ d) = Fq204.pow mldsaZeta e) (rootTree d e)
  | 0, e, _, _ => by
    dsimp only [rootTree, PolyTree.AllLeaves, Nat.pow_zero, Fq204.pow]
    rw [Fq204.one_mul]
  | d + 1, e, hdvd, hdle => by
    obtain ⟨k, hk⟩ := hdvd
    have hk2 : e = (2 ^ d * k) * 2 := by rw [hk, Nat.pow_succ, Nat.mul_right_comm]
    have heDiv : e / 2 = 2 ^ d * k := by rw [hk2]; exact Nat.mul_div_cancel _ (by decide)
    have hdvdL : 2 ^ d ∣ (e / 2) := ⟨k, heDiv⟩
    have hdvd256 : 2 ^ d ∣ 256 := by
      obtain ⟨t, ht⟩ : ∃ t, 8 = d + t := ⟨8 - d, by omega⟩
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ht, Nat.pow_add]
      exact Nat.dvd_mul_right (2 ^ d) (2 ^ t)
    have hdvdR : 2 ^ d ∣ (e / 2 + 256) := Nat.dvd_add hdvdL hdvd256
    have he2 : 2 * (e / 2) = e := by rw [heDiv, hk2, Nat.mul_comm]
    simp only [rootTree, PolyTree.AllLeaves]
    refine ⟨allLeaves_imp ?_ (rootTree_allLeavesPow d (e / 2) hdvdL (by omega)),
            allLeaves_imp ?_ (rootTree_allLeavesPow d (e / 2 + 256) hdvdR (by omega))⟩
    · intro w hw
      rw [Nat.pow_succ, Fq204.pow_mul, hw, ← Fq204.pow_mul, Nat.mul_comm _ 2, he2]
    · intro w hw
      rw [Nat.pow_succ, Fq204.pow_mul, hw, ← Fq204.pow_mul]
      have hmul : (e / 2 + 256) * 2 = e + 512 := by omega
      rw [hmul, Fq204.pow_add, mldsaZeta_pow512_eq_one, Fq204.mul_one]

private theorem nttStage_eq_evalAtTree :
    ∀ (d e : Nat), 2 ^ d ∣ e → d ≤ 8 →
      ∀ (p : PolyTree d), nttStage d e p = evalAtTree (PolyTree.toList p) (rootTree d e)
  | 0, _, _, _, .leaf x => by
    dsimp only [nttStage, rootTree, evalAtTree, PolyTree.toList, evalPoly204]
    rw [Fq204.mul_zero, Fq204.add_zero]
  | d + 1, e, hdvd, hdle, .branch lo hi => by
    obtain ⟨k, hk⟩ := hdvd
    have hk2 : e = (2 ^ d * k) * 2 := by rw [hk, Nat.pow_succ, Nat.mul_right_comm]
    have heDiv : e / 2 = 2 ^ d * k := by rw [hk2]; exact Nat.mul_div_cancel _ (by decide)
    have hdvdL : 2 ^ d ∣ (e / 2) := ⟨k, heDiv⟩
    have hdvd256 : 2 ^ d ∣ 256 := by
      obtain ⟨t, ht⟩ : ∃ t, 8 = d + t := ⟨8 - d, by omega⟩
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ht, Nat.pow_add]
      exact Nat.dvd_mul_right (2 ^ d) (2 ^ t)
    have hdvdR : 2 ^ d ∣ (e / 2 + 256) := Nat.dvd_add hdvdL hdvd256
    simp only [nttStage, rootTree, evalAtTree, PolyTree.toList,
      nttStage_eq_evalAtTree d (e / 2) hdvdL (by omega),
      nttStage_eq_evalAtTree d (e / 2 + 256) hdvdR (by omega)]
    congr 1
    · apply evalAtTree_congr _ (rootTree_allLeavesPow d (e / 2) hdvdL (by omega))
      intro w hw
      rw [toList_addTree, toList_scaleTree, evalPoly204_addPolyList, evalPoly204_scalePolyList,
          evalPoly204_append, PolyTree.length_toList, hw]
    · apply evalAtTree_congr _ (rootTree_allLeavesPow d (e / 2 + 256) hdvdR (by omega))
      intro w hw
      rw [toList_subTree, toList_scaleTree, evalPoly204_subPolyList, evalPoly204_scalePolyList,
          evalPoly204_append, PolyTree.length_toList, hw,
          Fq204.pow_add mldsaZeta (e / 2) 256, mldsaZeta_pow256_eq_neg_one,
          Fq204.sub_eq_add_neg]
      congr 1
      rw [Fq204.mul_neg (Fq204.pow mldsaZeta (e / 2)) Fq204.one, Fq204.mul_one,
          Fq204.mul_comm (Fq204.neg _) (evalPoly204 hi.toList w),
          Fq204.mul_neg (evalPoly204 hi.toList w), Fq204.mul_comm (evalPoly204 hi.toList w)]

private theorem evalAtTree_pointwiseMul {xs ys : List Fq204}
    (hx : xs.length = 256) (hy : ys.length = 256) :
    ∀ {d : Nat} {r : PolyTree d},
      PolyTree.AllLeaves (fun w => Fq204.pow w 256 = Fq204.neg Fq204.one) r →
      evalAtTree (negacyclicMulList xs ys) r =
        PolyTree.pointwiseMul (evalAtTree xs r) (evalAtTree ys r)
  | 0, .leaf _, hw => congrArg PolyTree.leaf (evalPoly204_negacyclicMulList hx hy hw)
  | _ + 1, .branch _ _, h => by
    simp only [evalAtTree, PolyTree.pointwiseMul,
      evalAtTree_pointwiseMul hx hy h.1, evalAtTree_pointwiseMul hx hy h.2]

/-- **`fips204Ntt_negacyclicMul` (NTT Convolution Homomorphism)**:
    Forward 256-point FIPS 204 NTT maps negacyclic polynomial multiplication in
    $R_q = \mathbb{Z}_q[X]/(X^{256} + 1)$ to coordinatewise multiplication in $\mathbb{Z}_q^{256}$. -/
theorem fips204Ntt_negacyclicMul (a b : Poly256) :
    fips204Ntt (negacyclicMul a b) =
      PolyTree.pointwiseMul (fips204Ntt a) (fips204Ntt b) := by
  unfold fips204Ntt negacyclicMul
  have hlenA : (PolyTree.toList a).length = 256 := PolyTree.length_toList a
  have hlenB : (PolyTree.toList b).length = 256 := PolyTree.length_toList b
  have hlenM : (negacyclicMulList (PolyTree.toList a) (PolyTree.toList b)).length = 256 :=
    length_negacyclicMulList hlenA hlenB
  rw [nttStage_eq_evalAtTree 8 256 (Nat.dvd_refl 256) (Nat.le_refl 8),
      nttStage_eq_evalAtTree 8 256 (Nat.dvd_refl 256) (Nat.le_refl 8),
      nttStage_eq_evalAtTree 8 256 (Nat.dvd_refl 256) (Nat.le_refl 8),
      PolyTree.toList_ofList hlenM]
  have hRoots := rootTree_allLeavesPow 8 256 (Nat.dvd_refl 256) (Nat.le_refl 8)
  rw [show (2 : Nat) ^ 8 = 256 from rfl, mldsaZeta_pow256_eq_neg_one] at hRoots
  exact evalAtTree_pointwiseMul hlenA hlenB hRoots

/-- **`fips204InvNtt_pointwiseMul`**: inverse NTT of coordinatewise product equals exact
    negacyclic polynomial multiplication in $R_q = \mathbb{Z}_q[X]/(X^{256} + 1)$. -/
theorem fips204InvNtt_pointwiseMul (a b : Poly256) :
    fips204InvNtt (PolyTree.pointwiseMul (fips204Ntt a) (fips204Ntt b)) = negacyclicMul a b := by
  rw [← fips204Ntt_negacyclicMul, fips204InvNtt_ntt]

/-! #### `LawfulCommRing Poly256` via Linearity & NTT Homomorphism -/

private theorem polyTree_scale_add (z : Fq204) : ∀ {d : Nat} (x y : PolyTree d),
    PolyTree.scale z (PolyTree.add x y) = PolyTree.add (PolyTree.scale z x) (PolyTree.scale z y)
  | 0, .leaf x, .leaf y => congrArg PolyTree.leaf (Fq204.left_distrib z x y)
  | _ + 1, .branch x0 x1, .branch y0 y1 => by
    simp only [PolyTree.add, PolyTree.scale, polyTree_scale_add z]

private theorem polyTree_add_add_comm : ∀ {d : Nat} (x0 y0 x1 y1 : PolyTree d),
    PolyTree.add (PolyTree.add x0 y0) (PolyTree.add x1 y1) =
      PolyTree.add (PolyTree.add x0 x1) (PolyTree.add y0 y1)
  | 0, .leaf x0, .leaf y0, .leaf x1, .leaf y1 => congrArg PolyTree.leaf <| by
    rw [Fq204.add_assoc x0, ← Fq204.add_assoc y0, Fq204.add_comm y0 x1,
        Fq204.add_assoc x1, ← Fq204.add_assoc x0]
  | _ + 1, .branch a0 a1, .branch b0 b1, .branch c0 c1, .branch d0 d1 => by
    simp only [PolyTree.add, polyTree_add_add_comm]

private theorem polyTree_sub_add_comm : ∀ {d : Nat} (x0 y0 x1 y1 : PolyTree d),
    PolyTree.sub (PolyTree.add x0 y0) (PolyTree.add x1 y1) =
      PolyTree.add (PolyTree.sub x0 x1) (PolyTree.sub y0 y1)
  | 0, .leaf x0, .leaf y0, .leaf x1, .leaf y1 => congrArg PolyTree.leaf <| by
    rw [Fq204.sub_eq_add_neg, Fq204.sub_eq_add_neg, Fq204.sub_eq_add_neg, Fq204.neg_add,
        Fq204.add_assoc x0, ← Fq204.add_assoc y0, Fq204.add_comm y0 (Fq204.neg x1),
        Fq204.add_assoc (Fq204.neg x1), ← Fq204.add_assoc x0]
  | _ + 1, .branch a0 a1, .branch b0 b1, .branch c0 c1, .branch d0 d1 => by
    simp only [PolyTree.add, PolyTree.sub, polyTree_sub_add_comm]

private theorem nttStage_add : ∀ (d e : Nat) (a b : PolyTree d),
    nttStage d e (PolyTree.add a b) = PolyTree.add (nttStage d e a) (nttStage d e b)
  | 0, _, .leaf _, .leaf _ => rfl
  | d + 1, e, .branch a0 a1, .branch b0 b1 => by
    simp only [PolyTree.add, nttStage, polyTree_scale_add, polyTree_add_add_comm,
      polyTree_sub_add_comm, nttStage_add d]

theorem fips204Ntt_add (a b : Poly256) :
    fips204Ntt (PolyTree.add a b) = PolyTree.add (fips204Ntt a) (fips204Ntt b) :=
  nttStage_add 8 256 a b

private theorem evalPoly204_toList_zero :
    ∀ (d : Nat) (w : Fq204), evalPoly204 (PolyTree.toList (PolyTree.zero d)) w = Fq204.zero
  | 0, _ => by dsimp only [PolyTree.zero, PolyTree.toList, evalPoly204]; rw [Fq204.mul_zero, Fq204.add_zero]
  | d + 1, w => by
    simp only [PolyTree.zero, PolyTree.toList, evalPoly204_append, evalPoly204_toList_zero d w,
      Fq204.mul_zero, Fq204.add_zero]

private theorem evalPoly204_toList_constUnit :
    ∀ (d : Nat) (w : Fq204), evalPoly204 (PolyTree.toList (PolyTree.constUnit d)) w = Fq204.one
  | 0, _ => by dsimp only [PolyTree.constUnit, PolyTree.toList, evalPoly204]; rw [Fq204.mul_zero, Fq204.add_zero]
  | d + 1, w => by
    simp only [PolyTree.constUnit, PolyTree.toList, evalPoly204_append,
      evalPoly204_toList_constUnit d w, evalPoly204_toList_zero d w,
      Fq204.mul_zero, Fq204.add_zero]

private theorem evalAtTree_eq_ones {coeffs : List Fq204}
    (h1 : ∀ w, evalPoly204 coeffs w = Fq204.one) :
    ∀ {d : Nat} (r : PolyTree d), evalAtTree coeffs r = PolyTree.ones d
  | 0, .leaf w => congrArg PolyTree.leaf (h1 w)
  | _ + 1, .branch r0 r1 => by
    simp only [evalAtTree, PolyTree.ones, evalAtTree_eq_ones h1 r0, evalAtTree_eq_ones h1 r1]

private theorem evalAtTree_eq_zero {coeffs : List Fq204}
    (h0 : ∀ w, evalPoly204 coeffs w = Fq204.zero) :
    ∀ {d : Nat} (r : PolyTree d), evalAtTree coeffs r = PolyTree.zero d
  | 0, .leaf w => congrArg PolyTree.leaf (h0 w)
  | _ + 1, .branch r0 r1 => by
    simp only [evalAtTree, PolyTree.zero, evalAtTree_eq_zero h0 r0, evalAtTree_eq_zero h0 r1]

theorem fips204Ntt_constUnit :
    fips204Ntt (PolyTree.constUnit 8) = PolyTree.ones 8 := by
  unfold fips204Ntt
  rw [nttStage_eq_evalAtTree 8 256 (Nat.dvd_refl 256) (Nat.le_refl 8)]
  exact evalAtTree_eq_ones (evalPoly204_toList_constUnit 8) _

theorem fips204Ntt_zero :
    fips204Ntt (PolyTree.zero 8) = PolyTree.zero 8 := by
  unfold fips204Ntt
  rw [nttStage_eq_evalAtTree 8 256 (Nat.dvd_refl 256) (Nat.le_refl 8)]
  exact evalAtTree_eq_zero (evalPoly204_toList_zero 8) _

theorem polyTree_add_assoc : ∀ {d : Nat} (a b c : PolyTree d),
    PolyTree.add (PolyTree.add a b) c = PolyTree.add a (PolyTree.add b c)
  | 0, .leaf a, .leaf b, .leaf c => congrArg PolyTree.leaf (Fq204.add_assoc a b c)
  | _ + 1, .branch a0 a1, .branch b0 b1, .branch c0 c1 => by
    simp only [PolyTree.add, polyTree_add_assoc a0 b0 c0, polyTree_add_assoc a1 b1 c1]

theorem polyTree_add_comm : ∀ {d : Nat} (a b : PolyTree d),
    PolyTree.add a b = PolyTree.add b a
  | 0, .leaf a, .leaf b => congrArg PolyTree.leaf (Fq204.add_comm a b)
  | _ + 1, .branch a0 a1, .branch b0 b1 => by
    simp only [PolyTree.add, polyTree_add_comm a0 b0, polyTree_add_comm a1 b1]

theorem polyTree_zero_add : ∀ {d : Nat} (a : PolyTree d),
    PolyTree.add (PolyTree.zero d) a = a
  | 0, .leaf a => congrArg PolyTree.leaf (Fq204.zero_add a)
  | _ + 1, .branch a0 a1 => by
    simp only [PolyTree.zero, PolyTree.add, polyTree_zero_add a0, polyTree_zero_add a1]

theorem polyTree_add_zero : ∀ {d : Nat} (a : PolyTree d),
    PolyTree.add a (PolyTree.zero d) = a
  | 0, .leaf a => congrArg PolyTree.leaf (Fq204.add_zero a)
  | _ + 1, .branch a0 a1 => by
    simp only [PolyTree.zero, PolyTree.add, polyTree_add_zero a0, polyTree_add_zero a1]

theorem polyTree_add_left_neg : ∀ {d : Nat} (a : PolyTree d),
    PolyTree.add (PolyTree.neg a) a = PolyTree.zero d
  | 0, .leaf a => congrArg PolyTree.leaf (Fq204.add_left_neg a)
  | _ + 1, .branch a0 a1 => by
    simp only [PolyTree.neg, PolyTree.add, PolyTree.zero, polyTree_add_left_neg a0, polyTree_add_left_neg a1]

theorem polyTree_sub_eq_add_neg : ∀ {d : Nat} (a b : PolyTree d),
    PolyTree.sub a b = PolyTree.add a (PolyTree.neg b)
  | 0, .leaf a, .leaf b => congrArg PolyTree.leaf (Fq204.sub_eq_add_neg a b)
  | _ + 1, .branch a0 a1, .branch b0 b1 => by
    simp only [PolyTree.sub, PolyTree.add, PolyTree.neg, polyTree_sub_eq_add_neg a0 b0, polyTree_sub_eq_add_neg a1 b1]

private theorem polyTree_zero_pmul : ∀ {d : Nat} (a : PolyTree d),
    PolyTree.pointwiseMul (PolyTree.zero d) a = PolyTree.zero d
  | 0, .leaf a => congrArg PolyTree.leaf (Fq204.zero_mul a)
  | _ + 1, .branch a0 a1 => by
    simp only [PolyTree.zero, PolyTree.pointwiseMul, polyTree_zero_pmul a0, polyTree_zero_pmul a1]

private theorem polyTree_pmul_assoc : ∀ {d : Nat} (a b c : PolyTree d),
    PolyTree.pointwiseMul (PolyTree.pointwiseMul a b) c = PolyTree.pointwiseMul a (PolyTree.pointwiseMul b c)
  | 0, .leaf a, .leaf b, .leaf c => congrArg PolyTree.leaf (Fq204.mul_assoc a b c)
  | _ + 1, .branch a0 a1, .branch b0 b1, .branch c0 c1 => by simp only [PolyTree.pointwiseMul, polyTree_pmul_assoc]

private theorem polyTree_pmul_comm : ∀ {d : Nat} (a b : PolyTree d),
    PolyTree.pointwiseMul a b = PolyTree.pointwiseMul b a
  | 0, .leaf a, .leaf b => congrArg PolyTree.leaf (Fq204.mul_comm a b)
  | _ + 1, .branch a0 a1, .branch b0 b1 => by simp only [PolyTree.pointwiseMul, polyTree_pmul_comm a0, polyTree_pmul_comm a1]

private theorem polyTree_ones_pmul : ∀ {d : Nat} (a : PolyTree d),
    PolyTree.pointwiseMul (PolyTree.ones d) a = a
  | 0, .leaf a => congrArg PolyTree.leaf (Fq204.one_mul a)
  | _ + 1, .branch a0 a1 => by simp only [PolyTree.ones, PolyTree.pointwiseMul, polyTree_ones_pmul]

private theorem polyTree_pmul_left_distrib : ∀ {d : Nat} (a b c : PolyTree d),
    PolyTree.pointwiseMul a (PolyTree.add b c) =
      PolyTree.add (PolyTree.pointwiseMul a b) (PolyTree.pointwiseMul a c)
  | 0, .leaf a, .leaf b, .leaf c => congrArg PolyTree.leaf (Fq204.left_distrib a b c)
  | _ + 1, .branch a0 a1, .branch b0 b1, .branch c0 c1 => by
    simp only [PolyTree.pointwiseMul, PolyTree.add, polyTree_pmul_left_distrib]

private theorem fips204Ntt_injective {a b : Poly256} (h : fips204Ntt a = fips204Ntt b) : a = b := by
  have := congrArg fips204InvNtt h
  rwa [fips204InvNtt_ntt, fips204InvNtt_ntt] at this

theorem negacyclicMul_assoc (a b c : Poly256) :
    negacyclicMul (negacyclicMul a b) c = negacyclicMul a (negacyclicMul b c) :=
  fips204Ntt_injective <| by simp only [fips204Ntt_negacyclicMul, polyTree_pmul_assoc]

theorem negacyclicMul_comm (a b : Poly256) :
    negacyclicMul a b = negacyclicMul b a :=
  fips204Ntt_injective <| by rw [fips204Ntt_negacyclicMul, fips204Ntt_negacyclicMul, polyTree_pmul_comm]

theorem negacyclicMul_zero_left (a : Poly256) :
    negacyclicMul (PolyTree.zero 8) a = PolyTree.zero 8 :=
  fips204Ntt_injective <| by rw [fips204Ntt_negacyclicMul, fips204Ntt_zero, polyTree_zero_pmul]

theorem negacyclicMul_one_left (a : Poly256) :
    negacyclicMul (PolyTree.constUnit 8) a = a :=
  fips204Ntt_injective <| by rw [fips204Ntt_negacyclicMul, fips204Ntt_constUnit, polyTree_ones_pmul]

theorem negacyclicMul_one_right (a : Poly256) :
    negacyclicMul a (PolyTree.constUnit 8) = a := by
  rw [negacyclicMul_comm, negacyclicMul_one_left]

theorem negacyclicMul_left_distrib (a b c : Poly256) :
    negacyclicMul a (PolyTree.add b c) = PolyTree.add (negacyclicMul a b) (negacyclicMul a c) :=
  fips204Ntt_injective <| by
    rw [fips204Ntt_negacyclicMul, fips204Ntt_add, fips204Ntt_add,
        fips204Ntt_negacyclicMul, fips204Ntt_negacyclicMul, polyTree_pmul_left_distrib]

theorem negacyclicMul_right_distrib (a b c : Poly256) :
    negacyclicMul (PolyTree.add a b) c = PolyTree.add (negacyclicMul a c) (negacyclicMul b c) := by
  rw [negacyclicMul_comm, negacyclicMul_left_distrib, negacyclicMul_comm c a, negacyclicMul_comm c b]

theorem poly256_add_left_cancel {a b c : Poly256} (h : PolyTree.add a b = PolyTree.add a c) : b = c := by
  have h1 := congrArg (PolyTree.add (PolyTree.neg a)) h
  rwa [← polyTree_add_assoc, ← polyTree_add_assoc, polyTree_add_left_neg,
       polyTree_zero_add, polyTree_zero_add] at h1

instance : CommRingOps Poly256 where
  zero := PolyTree.zero 8
  one := PolyTree.constUnit 8
  add := PolyTree.add
  mul := negacyclicMul
  neg := PolyTree.neg
  sub := PolyTree.sub

instance : LawfulCommRing Poly256 where
  add_assoc := polyTree_add_assoc
  add_comm := polyTree_add_comm
  zero_add := polyTree_zero_add
  add_zero := polyTree_add_zero
  add_left_neg := polyTree_add_left_neg
  sub_eq_add_neg := polyTree_sub_eq_add_neg
  mul_assoc := negacyclicMul_assoc
  mul_comm := negacyclicMul_comm
  one_mul := negacyclicMul_one_left
  mul_one := negacyclicMul_one_right
  left_distrib := negacyclicMul_left_distrib
  right_distrib := negacyclicMul_right_distrib

namespace Fq204
abbrev val (a : Fq204) := ModZq.val a
theorem isLt (a : Fq204) : a.val < mldsaQ := ModZq.isLt a
end Fq204
end Qsag

public section
namespace Qsag
/-! ## 1. Constructive Signed Rationals (`ExactRat`) -/

structure ExactRat where
  num : Int
  den : Nat
  den_pos : 0 < den
  deriving DecidableEq, Repr

@[expose] def ExactRat.ofInt (n : Int) : ExactRat := ⟨n, 1, Nat.one_pos⟩
@[expose] def ExactRat.twoNegPow (k : Nat) : ExactRat := ⟨1, 2 ^ k, Nat.two_pow_pos k⟩
@[expose] def ExactRat.eqv (x y : ExactRat) : Prop := x.num * (y.den : Int) = y.num * (x.den : Int)
@[expose] def ExactRat.le (x y : ExactRat) : Prop := x.num * (y.den : Int) ≤ y.num * (x.den : Int)
@[expose] def ExactRat.lt (x y : ExactRat) : Prop := x.num * (y.den : Int) < y.num * (x.den : Int)
instance (x y : ExactRat) : Decidable (ExactRat.eqv x y) := inferInstanceAs (Decidable (_ = _))
instance (x y : ExactRat) : Decidable (ExactRat.le x y) := inferInstanceAs (Decidable (_ ≤ _))
instance (x y : ExactRat) : Decidable (ExactRat.lt x y) := inferInstanceAs (Decidable (_ < _))

def ExactRat.add (x y : ExactRat) : ExactRat :=
  ⟨x.num * (y.den : Int) + y.num * (x.den : Int), x.den * y.den, Nat.mul_pos x.den_pos y.den_pos⟩
def ExactRat.sub (x y : ExactRat) : ExactRat :=
  ⟨x.num * (y.den : Int) - y.num * (x.den : Int), x.den * y.den, Nat.mul_pos x.den_pos y.den_pos⟩
def ExactRat.mul (x y : ExactRat) : ExactRat := ⟨x.num * y.num, x.den * y.den, Nat.mul_pos x.den_pos y.den_pos⟩
def ExactRat.abs (x : ExactRat) : ExactRat := ⟨(x.num.natAbs : Int), x.den, x.den_pos⟩
def ExactRat.scaleNat (k : Nat) (x : ExactRat) : ExactRat := ⟨(k : Int) * x.num, x.den, x.den_pos⟩
def ExactRat.min (x y : ExactRat) : ExactRat := if ExactRat.le x y then x else y
def ExactRat.pow (x : ExactRat) : Nat → ExactRat
  | 0 => ExactRat.ofInt 1
  | n + 1 => ExactRat.mul x (ExactRat.pow x n)

private theorem ExactRat.mul_num (a b : ExactRat) : (a.mul b).num = a.num * b.num := rfl
private theorem ExactRat.mul_den (a b : ExactRat) : (a.mul b).den = a.den * b.den := rfl
private theorem ExactRat.abs_le_twoNegPow {x : ExactRat} {k : Nat} (h : x.num.natAbs * 2 ^ k ≤ x.den) :
    ExactRat.le x.abs (ExactRat.twoNegPow k) := by
  unfold ExactRat.le ExactRat.abs ExactRat.twoNegPow; dsimp only; rw [Int.one_mul, ← Int.natCast_mul]; exact Int.ofNat_le.mpr h
private theorem ExactRat.abs_lt_twoNegPow {x : ExactRat} {k : Nat} (h : x.num.natAbs * 2 ^ k < x.den) :
    ExactRat.lt x.abs (ExactRat.twoNegPow k) := by
  unfold ExactRat.lt ExactRat.abs ExactRat.twoNegPow; dsimp only; rw [Int.one_mul, ← Int.natCast_mul]; exact Int.ofNat_lt.mpr h
private theorem ExactRat.not_lt_twoNegPow_of_gt {x : ExactRat} {k : Nat} (h : x.den < x.num.natAbs * 2 ^ k) :
    ¬ ExactRat.lt x.abs (ExactRat.twoNegPow k) := by
  unfold ExactRat.lt ExactRat.abs ExactRat.twoNegPow; dsimp only; rw [Int.one_mul, ← Int.natCast_mul]
  intro hLt; exact Nat.lt_asymm h (Int.ofNat_lt.mp hLt)
private theorem ExactRat.le_of_nat_mul {x y : ExactRat} {a c : Nat}
    (hx : x.num = (a : Int)) (hy : y.num = (c : Int)) (h : a * y.den ≤ c * x.den) : ExactRat.le x y := by
  unfold ExactRat.le; rw [hx, hy, ← Int.natCast_mul, ← Int.natCast_mul]; exact Int.ofNat_le.mpr h
private theorem nat_mul4_swap (a b c d : Nat) : (a * b) * (c * d) = (a * c) * (b * d) := by ac_rfl
private theorem nat_mul_right_comm (a b c : Nat) : a * b * c = a * c * b := by ac_rfl
private theorem nat_lt_of_mul_lt_left {a b c : Nat} (h : a * b < a * c) : b < c :=
  Decidable.byContradiction fun hN => Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (Nat.mul_le_mul_left a (Nat.le_of_not_lt hN)) h)
private theorem nat_lt_of_mul_lt_right {a b c : Nat} (h : b * a < c * a) : b < c :=
  Decidable.byContradiction fun hN => Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (Nat.mul_le_mul_right a (Nat.le_of_not_lt hN)) h)

/-! ## 2. Production `24`-Rep Parameters, Exact Rejection Law & Fixed-Point `Q192` Rounding -/

def rlweZkpok24Reps : Nat := 24
def rlweZkpok11ChalBits : Nat := 11
def rlweGaussianSigma : Nat := 700
def rlweGaussianTwoSigmaSq : Nat := 2 * rlweGaussianSigma ^ 2
def rlweProposalHalfWidth : Nat := 3072
def rlweAcceptHalfWidth : Nat := 3070
def rlweSingleRepScaleM : Nat := 24
def rlweJoint24RepScaleM : Nat := 40

theorem rlwe_24rep_pq128_soundness_bits :
    rlweZkpok24Reps * rlweZkpok11ChalBits = 264 ∧ (rlweZkpok24Reps * rlweZkpok11ChalBits) / 2 = 132 ∧
    128 ≤ (rlweZkpok24Reps * rlweZkpok11ChalBits) / 2 ∧ rlweGaussianTwoSigmaSq = 980000 := by decide

def inHalfOpenBox (half : Nat) (x : Int) : Bool := decide (-(half : Int) ≤ x ∧ x < (half : Int))

theorem rlwe_accept_box_preimage_in_proposal_box (z v : Int)
    (hz : inHalfOpenBox rlweAcceptHalfWidth z = true) (hvLo : -1 ≤ v) (hvHi : v ≤ 1) :
    inHalfOpenBox rlweProposalHalfWidth (z - v) = true := by
  have ⟨hzLo, hzHi⟩ := of_decide_eq_true hz; apply decide_eq_true
  unfold rlweAcceptHalfWidth rlweProposalHalfWidth at *; constructor <;> omega

def acceptProbExact (rho : Int → Nat) (M : Nat) (z v : Int) : ExactRat :=
  let den := M * rho (z - v)
  if hPos : 0 < den then ExactRat.min (ExactRat.ofInt 1) ⟨(rho z : Int), den, hPos⟩ else ExactRat.ofInt 0

theorem acceptProbExact_safe_cancels_shift (rho : Int → Nat) (M : Nat) (hM : 0 < M)
    (z v : Int) (hRhoPos : 0 < rho (z - v)) (hSafe : rho z ≤ M * rho (z - v)) :
    ExactRat.eqv (ExactRat.scaleNat (rho (z - v)) (acceptProbExact rho M z v)) ⟨(rho z : Int), M, hM⟩ := by
  have hDenPos : 0 < M * rho (z - v) := Nat.mul_pos hM hRhoPos
  unfold acceptProbExact; simp only [hDenPos, dite_true, ExactRat.min]; split
  · next hOneLe =>
    unfold ExactRat.le ExactRat.ofInt at hOneLe; dsimp only at hOneLe
    have hEqNat : rho z = M * rho (z - v) := by omega
    unfold ExactRat.scaleNat ExactRat.ofInt ExactRat.eqv; dsimp only; rw [hEqNat, Int.natCast_mul]; ac_rfl
  · unfold ExactRat.scaleNat ExactRat.eqv; dsimp only; rw [Int.natCast_mul]; ac_rfl

def q192ToRat (w : Nat) : ExactRat := ⟨(w : Int), 2 ^ 192, Nat.two_pow_pos 192⟩
def acceptProbQ192FloorNum (rho : Int → Nat) (M : Nat) (z v : Int) : Nat :=
  let den := M * rho (z - v)
  if den = 0 then 0 else min (2 ^ 192) ((rho z * (2 ^ 192)) / den)
def acceptProbQ192 (rho : Int → Nat) (M : Nat) (z v : Int) : ExactRat := q192ToRat (acceptProbQ192FloorNum rho M z v)

private theorem q192_scaled_err_le_four_den (rz den W qNum : Nat)
    (hUlp : ((qNum : Int) - ((if den = 0 then 0 else min W ((rz * W) / den) : Nat) : Int)).natAbs ≤ 3) :
    ((qNum : Int) * (den : Int) - ((W * min den rz : Nat) : Int)).natAbs ≤ 4 * den := by
  by_cases hZero : den = 0
  · simp only [hZero, Nat.zero_min, Nat.mul_zero, Int.natCast_zero, Int.mul_zero, Int.sub_self, Int.natAbs_zero]
    exact Nat.le_refl 0
  · have hDenPos : 0 < den := Nat.pos_of_ne_zero hZero
    simp only [hZero, ↓reduceIte] at hUlp
    by_cases hClip : den ≤ rz
    · have hGe : W ≤ (rz * W) / den := (Nat.le_div_iff_mul_le hDenPos).mpr
        (by rw [Nat.mul_comm W den]; exact Nat.mul_le_mul_right W hClip)
      rw [Nat.min_eq_left hGe] at hUlp
      rw [Nat.min_eq_left hClip, Int.natCast_mul, ← Int.sub_mul, Int.natAbs_mul, Int.natAbs_natCast]
      exact Nat.le_trans (Nat.mul_le_mul_right den hUlp) (Nat.mul_le_mul_right den (by decide))
    · have hLt : rz < den := Nat.lt_of_not_le hClip
      have hDivLe : (rz * W) / den ≤ W := Nat.div_le_of_le_mul (Nat.mul_le_mul_right W (Nat.le_of_lt hLt))
      rw [Nat.min_eq_right hDivLe] at hUlp; rw [Nat.min_eq_right (Nat.le_of_lt hLt)]
      let q0 := (rz * W) / den; let r0 := (rz * W) % den
      have hDMI : (q0 : Int) * (den : Int) + (r0 : Int) = ((W * rz : Nat) : Int) := by
        rw [← Int.natCast_mul, ← Int.natCast_add, Nat.mul_comm q0 den, Nat.mul_comm W rz, Nat.div_add_mod]
      rw [show (qNum : Int) * (den : Int) - ((W * rz : Nat) : Int) =
          ((qNum : Int) - (q0 : Int)) * (den : Int) - (r0 : Int) from by rw [← hDMI, Int.sub_mul]; omega]
      have hTri := Int.natAbs_sub_le (((qNum : Int) - (q0 : Int)) * (den : Int)) (r0 : Int)
      rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast] at hTri
      have hMod : r0 ≤ den := Nat.le_of_lt (Nat.mod_lt (rz * W) hDenPos)
      have hSum := Nat.add_le_add (Nat.mul_le_mul_right den hUlp) hMod
      exact Nat.le_trans hTri ((by omega : 3 * den + den = 4 * den) ▸ hSum)

private theorem q192_rounding_core (rz den U qNum : Nat) (hUPos : 0 < U)
    (hUlp : ((qNum : Int) - ((if den = 0 then 0 else min (4 * U) ((rz * (4 * U)) / den) : Nat) : Int)).natAbs ≤ 3) :
    let ex : ExactRat := if hPos : 0 < den then ExactRat.min (ExactRat.ofInt 1) ⟨(rz : Int), den, hPos⟩ else ExactRat.ofInt 0
    let qRat : ExactRat := ⟨(qNum : Int), 4 * U, Nat.mul_pos (by decide) hUPos⟩
    (qRat.sub ex).num.natAbs * U ≤ (qRat.sub ex).den := by
  intro ex qRat
  by_cases hZero : den = 0
  · have hNotPos : ¬ (0 < den) := by omega
    simp only [hZero, ↓reduceIte] at hUlp; unfold ex qRat ExactRat.sub ExactRat.ofInt; simp only [hNotPos, dite_false]
    rw [show ((qNum : Int) * (1 : Nat) - 0 * ((4 * U : Nat) : Int)).natAbs = qNum from by omega, Nat.mul_one]
    exact Nat.mul_le_mul_right U (by omega)
  · have hDenPos : 0 < den := Nat.pos_of_ne_zero hZero
    have hErr := q192_scaled_err_le_four_den rz den (4 * U) qNum hUlp
    unfold ex qRat ExactRat.sub ExactRat.min; simp only [hDenPos, dite_true]; split
    · next hOneLe =>
      unfold ExactRat.le ExactRat.ofInt at hOneLe; dsimp only at hOneLe
      have hGe : 4 * U ≤ (rz * (4 * U)) / den := (Nat.le_div_iff_mul_le hDenPos).mpr
        (by rw [Nat.mul_comm (4 * U) den]; exact Nat.mul_le_mul_right (4 * U) (by omega))
      simp only [hZero, ↓reduceIte, Nat.min_eq_left hGe] at hUlp
      unfold ExactRat.ofInt; dsimp only; rw [Nat.mul_one]; exact Nat.mul_le_mul_right U (by omega)
    · next hNotOneLe =>
      unfold ExactRat.le ExactRat.ofInt at hNotOneLe; dsimp only at hNotOneLe
      rw [Nat.min_eq_right (by omega : rz ≤ den), Nat.mul_comm (4 * U) rz, Int.natCast_mul] at hErr; dsimp only
      have hMul := Nat.mul_le_mul_right U hErr; rw [nat_mul_right_comm 4 den U] at hMul; exact hMul

theorem q192_acceptProb_rounding_le_two_neg_190 (rho : Int → Nat) (M : Nat) (z v : Int) (qNum : Nat)
    (hUlp : ((qNum : Int) - (acceptProbQ192FloorNum rho M z v : Int)).natAbs ≤ 3) :
    ExactRat.le (ExactRat.abs (ExactRat.sub (q192ToRat qNum) (acceptProbExact rho M z v))) (ExactRat.twoNegPow 190) := by
  apply ExactRat.abs_le_twoNegPow
  have hPow : (2 : Nat) ^ 192 = 4 * 2 ^ 190 := by rw [show (192 : Nat) = 2 + 190 from rfl, Nat.pow_add]
  unfold acceptProbQ192FloorNum at hUlp; unfold q192ToRat acceptProbExact; simp only [hPow] at hUlp ⊢
  exact q192_rounding_core (rho z) (M * rho (z - v)) (2 ^ 190) qNum (Nat.two_pow_pos 190) hUlp

/-! ## 3. Constructive `K`-Attempt & Conditional HVZK Transcript Simulation + Abort Independence -/

def natSumList {α : Type} : List α → (α → Nat) → Nat
  | [], _ => 0
  | x :: tl, f => f x + natSumList tl f

private theorem natSumList_zero {α : Type} : ∀ xs : List α, natSumList xs (fun _ => 0) = 0
  | [] => rfl
  | _ :: tl => by simp only [natSumList, Nat.zero_add, natSumList_zero tl]

def retryWeight {α : Type} : Nat → Nat → Nat → (α → Nat) → α → Nat
  | 0, _, _, _, _ => 0
  | K + 1, D, R, w, x => w x * (D ^ K) + R * retryWeight K D R w x

theorem retryWeight_sum_add_abort_eq_pow {α : Type} (xs : List α) (D : Nat) (w : α → Nat) (hSub : natSumList xs w ≤ D) :
    ∀ K : Nat, natSumList xs (retryWeight K D (D - natSumList xs w) w) + (D - natSumList xs w) ^ K = D ^ K
  | 0 => by have hZ : retryWeight 0 D (D - natSumList xs w) w = (fun _ => 0) := rfl; rw [hZ, natSumList_zero]; rfl
  | K + 1 => by
    let R := D - natSumList xs w
    have hSplit : ∀ ys : List α, natSumList ys (retryWeight (K + 1) D R w) =
        natSumList ys w * (D ^ K) + R * natSumList ys (retryWeight K D R w) := by
      intro ys; induction ys with
      | nil => simp only [natSumList, Nat.zero_mul, Nat.mul_zero, Nat.add_zero]
      | cons _ _ ih => simp only [natSumList, retryWeight] at ih ⊢; rw [ih, Nat.add_mul, Nat.mul_add]; ac_rfl
    rw [hSplit xs, Nat.pow_succ' (n := K), Nat.add_assoc, ← Nat.mul_add R,
        retryWeight_sum_add_abort_eq_pow xs D w hSub K, ← Nat.add_mul, Nat.add_sub_of_le hSub, Nat.pow_succ']

def natL1Diff {α : Type} (xs : List α) (f g : α → Nat) : Nat := natSumList xs (fun x => ((f x : Int) - (g x : Int)).natAbs)

private theorem natL1Diff_self {α : Type} : ∀ (xs : List α) (f : α → Nat), natL1Diff xs f f = 0
  | [], _ => rfl
  | _ :: tl, f => by unfold natL1Diff; dsimp only [natSumList]; rw [Int.sub_self, Int.natAbs_zero, Nat.zero_add]; exact natL1Diff_self tl f

private theorem natSumList_diff_le_l1 {α : Type} (xs : List α) (f g : α → Nat) :
    ((natSumList xs f : Int) - (natSumList xs g : Int)).natAbs ≤ natL1Diff xs f g := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x tl ih =>
    unfold natL1Diff at ih ⊢; simp only [natSumList]
    rw [show ((f x + natSumList tl f : Nat) : Int) - ((g x + natSumList tl g : Nat) : Int) =
        ((f x : Int) - (g x : Int)) + ((natSumList tl f : Int) - (natSumList tl g : Int)) from by omega]
    exact Nat.le_trans (Int.natAbs_add_le _ _) (Nat.add_le_add_left ih _)

private theorem natL1_retry_step {α : Type} (xs : List α) (D R1 R2 : Nat) (w1 w2 : α → Nat) (K : Nat) :
    natL1Diff xs (retryWeight (K + 1) D R1 w1) (retryWeight (K + 1) D R2 w2) ≤
      natL1Diff xs w1 w2 * (D ^ K) + R1 * natL1Diff xs (retryWeight K D R1 w1) (retryWeight K D R2 w2) +
      ((R1 : Int) - (R2 : Int)).natAbs * natSumList xs (retryWeight K D R2 w2) := by
  induction xs with
  | nil => simp only [natL1Diff, natSumList, Nat.zero_mul, Nat.mul_zero, Nat.add_zero]; exact Nat.le_refl 0
  | cons x tl ih =>
    unfold natL1Diff at ih ⊢; simp only [natSumList, retryWeight]
    let u1 := retryWeight K D R1 w1 x; let u2 := retryWeight K D R2 w2 x; let P := D ^ K
    have hPt : (((w1 x * P + R1 * u1 : Nat) : Int) - ((w2 x * P + R2 * u2 : Nat) : Int)).natAbs ≤
        ((w1 x : Int) - (w2 x : Int)).natAbs * P + R1 * ((u1 : Int) - (u2 : Int)).natAbs +
        ((R1 : Int) - (R2 : Int)).natAbs * u2 := by
      rw [show ((w1 x * P + R1 * u1 : Nat) : Int) - ((w2 x * P + R2 * u2 : Nat) : Int) =
          ((w1 x : Int) - (w2 x : Int)) * (P : Int) + (R1 : Int) * ((u1 : Int) - (u2 : Int)) +
          ((R1 : Int) - (R2 : Int)) * (u2 : Int) from by simp only [Int.natCast_add, Int.natCast_mul, Int.sub_mul, Int.mul_sub]; omega]
      have a1 := Int.natAbs_add_le (((w1 x : Int) - (w2 x : Int)) * (P : Int) + (R1 : Int) * ((u1 : Int) - (u2 : Int)))
        (((R1 : Int) - (R2 : Int)) * (u2 : Int))
      have a2 := Int.natAbs_add_le (((w1 x : Int) - (w2 x : Int)) * (P : Int)) ((R1 : Int) * ((u1 : Int) - (u2 : Int)))
      simp only [Int.natAbs_mul, Int.natAbs_natCast] at a1 a2; exact Nat.le_trans a1 (Nat.add_le_add_right a2 _)
    have hSum := Nat.add_le_add hPt ih
    have hRhs : ∀ a1 a2 b1 b2 c1 c2 : Nat,
        (a1 * P + R1 * b1 + ((R1 : Int) - (R2 : Int)).natAbs * c1) + (a2 * P + R1 * b2 + ((R1 : Int) - (R2 : Int)).natAbs * c2) =
        (a1 + a2) * P + R1 * (b1 + b2) + ((R1 : Int) - (R2 : Int)).natAbs * (c1 + c2) :=
      fun _ _ _ _ _ _ => by rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; ac_rfl
    rw [hRhs] at hSum; exact hSum

private theorem sub_sub_natAbs_eq {M a b : Nat} (ha : a ≤ M) (hb : b ≤ M) :
    (((M - a : Nat) : Int) - ((M - b : Nat) : Int)).natAbs = ((a : Int) - (b : Int)).natAbs := by omega

private theorem abort_pow_step_le (R1 R2 P1 P2 : Nat) :
    (((R1 * P1 : Nat) : Int) - ((R2 * P2 : Nat) : Int)).natAbs ≤
      R1 * ((P1 : Int) - (P2 : Int)).natAbs + ((R1 : Int) - (R2 : Int)).natAbs * P2 := by
  rw [show ((R1 * P1 : Nat) : Int) - ((R2 * P2 : Nat) : Int) =
      (R1 : Int) * ((P1 : Int) - (P2 : Int)) + ((R1 : Int) - (R2 : Int)) * (P2 : Int) from by
    simp only [Int.natCast_mul, Int.mul_sub, Int.sub_mul]; omega]
  simpa only [Int.natAbs_mul, Int.natAbs_natCast] using
    Int.natAbs_add_le ((R1 : Int) * ((P1 : Int) - (P2 : Int))) (((R1 : Int) - (R2 : Int)) * (P2 : Int))

theorem retry_full_l1_le_two_K_mul_single {α : Type} (xs : List α) (D : Nat)
    (w1 w2 : α → Nat) (hSub1 : natSumList xs w1 ≤ D) (hSub2 : natSumList xs w2 ≤ D) :
    ∀ K : Nat, let R1 := D - natSumList xs w1; let R2 := D - natSumList xs w2
      (natL1Diff xs (retryWeight K D R1 w1) (retryWeight K D R2 w2) +
        (((R1 ^ K : Nat) : Int) - ((R2 ^ K : Nat) : Int)).natAbs) * D ≤ 2 * K * natL1Diff xs w1 w2 * (D ^ K)
  | 0 => by
    intro R1 R2; have hZ1 : retryWeight 0 D R1 w1 = (fun _ => 0) := rfl; have hZ2 : retryWeight 0 D R2 w2 = (fun _ => 0) := rfl
    rw [hZ1, hZ2, natL1Diff_self xs (fun _ => 0)]
    simp only [Nat.pow_zero, Int.sub_self, Int.natAbs_zero, Nat.add_zero, Nat.zero_mul]; exact Nat.zero_le _
  | K + 1 => by
    intro R1 R2; have ih := retry_full_l1_le_two_K_mul_single xs D w1 w2 hSub1 hSub2 K; dsimp only at ih
    have hRDiff : ((R1 : Int) - (R2 : Int)).natAbs ≤ natL1Diff xs w1 w2 := by
      rw [sub_sub_natAbs_eq hSub1 hSub2]; exact natSumList_diff_le_l1 xs w1 w2
    have hAbLe : (((R1 ^ (K + 1) : Nat) : Int) - ((R2 ^ (K + 1) : Nat) : Int)).natAbs ≤
        R1 * (((R1 ^ K : Nat) : Int) - ((R2 ^ K : Nat) : Int)).natAbs + ((R1 : Int) - (R2 : Int)).natAbs * R2 ^ K := by
      rw [Nat.pow_succ' (n := K), Nat.pow_succ' (n := K)]; exact abort_pow_step_le R1 R2 (R1 ^ K) (R2 ^ K)
    let LK := natL1Diff xs (retryWeight K D R1 w1) (retryWeight K D R2 w2)
    let AK := (((R1 ^ K : Nat) : Int) - ((R2 ^ K : Nat) : Int)).natAbs
    have hAdd := Nat.add_le_add (natL1_retry_step xs D R1 R2 w1 w2 K) hAbLe
    have hRe : ∀ d1 P dR SK : Nat, (d1 * P + R1 * LK + dR * SK) + (R1 * AK + dR * R2 ^ K) =
        (d1 * P + dR * (SK + R2 ^ K)) + R1 * (LK + AK) := fun _ _ _ _ => by rw [Nat.mul_add, Nat.mul_add]; ac_rfl
    rw [hRe, retryWeight_sum_add_abort_eq_pow xs D w2 hSub2 K] at hAdd
    have p1 : natL1Diff xs w1 w2 * D ^ K + ((R1 : Int) - (R2 : Int)).natAbs * D ^ K ≤ 2 * natL1Diff xs w1 w2 * D ^ K := by
      have m := Nat.add_le_add_left (Nat.mul_le_mul_right (D ^ K) hRDiff) (natL1Diff xs w1 w2 * D ^ K)
      rw [← Nat.two_mul, ← Nat.mul_assoc] at m; exact m
    have hMulD := Nat.mul_le_mul_right D (Nat.le_trans hAdd (Nat.add_le_add p1 (Nat.mul_le_mul_right (LK + AK) (Nat.sub_le D _))))
    have hRhs1 : ∀ X Y : Nat, (X + D * Y) * D = X * D + D * (Y * D) := fun _ _ => by rw [Nat.add_mul, Nat.mul_assoc]
    rw [hRhs1] at hMulD
    have hStep2 := Nat.le_trans hMulD (Nat.add_le_add_left (Nat.mul_le_mul_left D ih) _)
    have hRhs2 : ∀ d P : Nat, 2 * d * P * D + D * (2 * K * d * P) = 2 * (K + 1) * d * (P * D) :=
      fun _ _ => by rw [Nat.mul_add 2 K 1, Nat.mul_one, Nat.add_mul, Nat.add_mul]; ac_rfl
    rw [Nat.pow_succ]; exact hRhs2 _ _ ▸ hStep2

theorem retry_abort_diff_le_K_mul_single {α : Type} (xs : List α) (D : Nat)
    (w1 w2 : α → Nat) (hSub1 : natSumList xs w1 ≤ D) (hSub2 : natSumList xs w2 ≤ D) :
    ∀ K : Nat, let R1 := D - natSumList xs w1; let R2 := D - natSumList xs w2
      (((R1 ^ K : Nat) : Int) - ((R2 ^ K : Nat) : Int)).natAbs * D ≤ K * natL1Diff xs w1 w2 * (D ^ K)
  | 0 => by intro _ _; simp only [Nat.pow_zero, Int.sub_self, Int.natAbs_zero, Nat.zero_mul]; exact Nat.zero_le _
  | K + 1 => by
    intro R1 R2; have ih := retry_abort_diff_le_K_mul_single xs D w1 w2 hSub1 hSub2 K; dsimp only at ih
    have hRDiff : ((R1 : Int) - (R2 : Int)).natAbs ≤ natL1Diff xs w1 w2 := by
      rw [sub_sub_natAbs_eq hSub1 hSub2]; exact natSumList_diff_le_l1 xs w1 w2
    have hAb := abort_pow_step_le R1 R2 (R1 ^ K) (R2 ^ K)
    rw [← Nat.pow_succ' (n := K), ← Nat.pow_succ' (n := K)] at hAb
    have hMulD := Nat.mul_le_mul_right D (Nat.le_trans hAb (Nat.add_le_add
      (Nat.mul_le_mul_right _ (Nat.sub_le D _)) (Nat.mul_le_mul hRDiff (Nat.pow_le_pow_left (Nat.sub_le D _) K))))
    rw [Nat.add_mul, Nat.mul_assoc D _ D] at hMulD
    have hStep2 := Nat.le_trans hMulD (Nat.add_le_add_right (Nat.mul_le_mul_left D ih) _)
    have hRhs : ∀ d P : Nat, D * (K * d * P) + d * P * D = (K + 1) * d * (P * D) :=
      fun _ _ => by rw [Nat.add_mul K 1, Nat.one_mul, Nat.add_mul]; ac_rfl
    rw [Nat.pow_succ]; exact hRhs _ _ ▸ hStep2

theorem conditional_accepted_l1_le_two_mul_single {α : Type} (xs : List α) (w1 w2 : α → Nat) :
    let A1 := natSumList xs w1; let A2 := natSumList xs w2
    natSumList xs (fun x => ((w1 x * A2 : Int) - (w2 x * A1 : Int)).natAbs) ≤ 2 * A1 * natL1Diff xs w1 w2 := by
  intro A1 A2
  have hDiffA : ((A2 : Int) - (A1 : Int)).natAbs ≤ natL1Diff xs w1 w2 :=
    (by omega : ((A2 : Int) - (A1 : Int)).natAbs = ((A1 : Int) - (A2 : Int)).natAbs) ▸ natSumList_diff_le_l1 xs w1 w2
  have hGen : ∀ ys : List α, natSumList ys (fun x => ((w1 x * A2 : Int) - (w2 x * A1 : Int)).natAbs) ≤
      A1 * natL1Diff ys w1 w2 + natSumList ys w1 * ((A2 : Int) - (A1 : Int)).natAbs := by
    intro ys; induction ys with
    | nil => simp only [natSumList, natL1Diff, Nat.mul_zero, Nat.zero_mul, Nat.add_zero]; exact Nat.le_refl 0
    | cons x tl ih =>
      unfold natL1Diff at ih ⊢; simp only [natSumList]
      have hPt : ((w1 x * A2 : Int) - (w2 x * A1 : Int)).natAbs ≤
          A1 * ((w1 x : Int) - (w2 x : Int)).natAbs + w1 x * ((A2 : Int) - (A1 : Int)).natAbs := by
        rw [show (w1 x * A2 : Int) - (w2 x * A1 : Int) =
            ((w1 x : Int) - (w2 x : Int)) * (A1 : Int) + (w1 x : Int) * ((A2 : Int) - (A1 : Int)) from by rw [Int.sub_mul, Int.mul_sub]; omega]
        have b := Int.natAbs_add_le (((w1 x : Int) - (w2 x : Int)) * (A1 : Int)) ((w1 x : Int) * ((A2 : Int) - (A1 : Int)))
        simp only [Int.natAbs_mul, Int.natAbs_natCast] at b; rw [Nat.mul_comm _ A1] at b; exact b
      have hSum := Nat.add_le_add hPt ih
      have hRhs : ∀ d1 d2 s1 dA : Nat, (A1 * d1 + w1 x * dA) + (A1 * d2 + s1 * dA) = A1 * (d1 + d2) + (w1 x + s1) * dA :=
        fun _ _ _ _ => by rw [Nat.mul_add, Nat.add_mul]; ac_rfl
      rw [hRhs] at hSum; exact hSum
  have hStep := Nat.le_trans (hGen xs) (Nat.add_le_add_left (Nat.mul_le_mul_left A1 hDiffA) _)
  rw [← Nat.two_mul, ← Nat.mul_assoc] at hStep; exact hStep

structure Q192GaussianSamplerParams where
  rho : Int → Nat
  zProp : Nat
  zProp_pos : 0 < zProp
  scaleM : Nat
  scaleM_pos : 0 < scaleM
  challenges : List Nat
  challenges_nonempty : 0 < challenges.length
  support : List Int

def Q192GaussianSamplerParams.trialDenom (P : Q192GaussianSamplerParams) : Nat :=
  P.challenges.length * P.zProp * P.scaleM * (2 ^ 192)
theorem Q192GaussianSamplerParams.trialDenom_pos (P : Q192GaussianSamplerParams) : 0 < P.trialDenom :=
  Nat.mul_pos (Nat.mul_pos (Nat.mul_pos P.challenges_nonempty P.zProp_pos) P.scaleM_pos) (Nat.two_pow_pos 192)
def prodPairs {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  xs.foldr (fun x acc => ys.map (fun y => (x, y)) ++ acc) []
def realQ192TrialWeight (P : Q192GaussianSamplerParams) (shift : Nat → Int) (q192Num : Int → Int → Nat) (cz : Nat × Int) : Nat :=
  P.scaleM * P.rho (cz.2 - shift cz.1) * q192Num cz.2 (shift cz.1)
def idealSimTrialWeight (P : Q192GaussianSamplerParams) (cz : Nat × Int) : Nat := (2 ^ 192) * P.rho cz.2
def tailDeficitAt (P : Q192GaussianSamplerParams) (shift : Nat → Int) (cz : Nat × Int) : Nat :=
  P.rho cz.2 - min (P.scaleM * P.rho (cz.2 - shift cz.1)) (P.rho cz.2)
def tailMassRat (P : Q192GaussianSamplerParams) (shift : Nat → Int) : ExactRat :=
  ⟨(natSumList (prodPairs P.challenges P.support) (tailDeficitAt P shift) : Int),
   P.challenges.length * P.zProp * P.scaleM, Nat.mul_pos (Nat.mul_pos P.challenges_nonempty P.zProp_pos) P.scaleM_pos⟩

def q192RetryTranscriptTv (P : Q192GaussianSamplerParams) (shift : Nat → Int) (q192Num : Int → Int → Nat) (K : Nat) : ExactRat :=
  let pts := prodPairs P.challenges P.support; let D := P.trialDenom
  let wReal := realQ192TrialWeight P shift q192Num; let wSim := idealSimTrialWeight P
  let R1 := D - natSumList pts wReal; let R2 := D - natSumList pts wSim
  ⟨(natL1Diff pts (retryWeight K D R1 wReal) (retryWeight K D R2 wSim) + (((R1 ^ K : Nat) : Int) - ((R2 ^ K : Nat) : Int)).natAbs : Int),
   2 * (D ^ K), Nat.mul_pos (by decide) (Nat.pow_pos P.trialDenom_pos)⟩

def q192ConditionalAcceptedTv (P : Q192GaussianSamplerParams) (shift : Nat → Int) (q192Num : Int → Int → Nat)
    (hRealPos : 0 < natSumList (prodPairs P.challenges P.support) (realQ192TrialWeight P shift q192Num))
    (hSimPos : 0 < natSumList (prodPairs P.challenges P.support) (idealSimTrialWeight P)) : ExactRat :=
  let pts := prodPairs P.challenges P.support
  let wReal := realQ192TrialWeight P shift q192Num; let wSim := idealSimTrialWeight P
  let A1 := natSumList pts wReal; let A2 := natSumList pts wSim
  ⟨(natSumList pts (fun x => ((wReal x * A2 : Int) - (wSim x * A1 : Int)).natAbs) : Int),
   2 * A1 * A2, Nat.mul_pos (Nat.mul_pos (by decide) hRealPos) hSimPos⟩

private theorem natSumList_append {α : Type} (xs ys : List α) (f : α → Nat) :
    natSumList (xs ++ ys) f = natSumList xs f + natSumList ys f := by
  induction xs with
  | nil => simp only [List.nil_append, natSumList, Nat.zero_add]
  | cons _ _ ih => simp only [List.cons_append, natSumList, ih, Nat.add_assoc]

private theorem natL1_single_trial_gen (P : Q192GaussianSamplerParams) (shift : Nat → Int)
    (q192Num : Int → Int → Nat) (W : Nat) (hRhoLe : ∀ z : Int, P.rho z ≤ P.zProp)
    (hUlp : ∀ c z, ((q192Num z (shift c) : Int) -
      ((if P.scaleM * P.rho (z - shift c) = 0 then 0 else min W ((P.rho z * W) / (P.scaleM * P.rho (z - shift c))) : Nat) : Int)).natAbs ≤ 3) :
    natL1Diff (prodPairs P.challenges P.support) (realQ192TrialWeight P shift q192Num) (fun cz => W * P.rho cz.2) ≤
      W * natSumList (prodPairs P.challenges P.support) (tailDeficitAt P shift) +
      4 * P.challenges.length * P.zProp * P.scaleM * P.support.length := by
  have hPt : ∀ cz : Nat × Int, (((realQ192TrialWeight P shift q192Num cz : Nat) : Int) -
      ((W * P.rho cz.2 : Nat) : Int)).natAbs ≤ W * tailDeficitAt P shift cz + 4 * P.scaleM * P.zProp := by
    intro ⟨c, z⟩; unfold realQ192TrialWeight tailDeficitAt; dsimp only
    let mRho := P.scaleM * P.rho (z - shift c); let minVal := min mRho (P.rho z)
    have hErr := q192_scaled_err_le_four_den (P.rho z) mRho W (q192Num z (shift c)) (hUlp c z)
    have hWDecomp : W * P.rho z = W * minVal + W * (P.rho z - minVal) := by
      rw [← Nat.mul_add, Nat.add_sub_of_le (Nat.min_le_right _ _)]
    change (((mRho * q192Num z (shift c) : Nat) : Int) - ((W * P.rho z : Nat) : Int)).natAbs ≤ _
    rw [show ((mRho * q192Num z (shift c) : Nat) : Int) - ((W * P.rho z : Nat) : Int) =
        ((q192Num z (shift c) : Int) * (mRho : Int) - ((W * minVal : Nat) : Int)) - ((W * (P.rho z - minVal) : Nat) : Int) from by
      rw [Nat.mul_comm mRho, hWDecomp, Int.natCast_mul (q192Num z (shift c)), Int.natCast_add]; omega]
    have hTri := Int.natAbs_sub_le ((q192Num z (shift c) : Int) * (mRho : Int) - ((W * minVal : Nat) : Int))
      ((W * (P.rho z - minVal) : Nat) : Int)
    rw [Int.natAbs_natCast] at hTri
    have hB4 : 4 * mRho ≤ 4 * P.scaleM * P.zProp := by rw [← Nat.mul_assoc 4 P.scaleM]; exact Nat.mul_le_mul_left _ (hRhoLe _)
    have hStep := Nat.le_trans hTri (Nat.add_le_add_right (Nat.le_trans hErr hB4) _)
    rw [Nat.add_comm] at hStep; exact hStep
  have hInner : ∀ (c : Nat) (zs : List Int),
      natL1Diff (zs.map (fun z => (c, z))) (realQ192TrialWeight P shift q192Num) (fun cz => W * P.rho cz.2) ≤
      W * natSumList (zs.map (fun z => (c, z))) (tailDeficitAt P shift) + 4 * P.scaleM * P.zProp * zs.length := by
    intro c zs; induction zs with
    | nil => simp only [List.map, natL1Diff, natSumList, List.length, Nat.mul_zero, Nat.add_zero]; exact Nat.le_refl 0
    | cons z tl ih =>
      unfold natL1Diff at ih ⊢; simp only [List.map, natSumList, List.length]
      have hAdd := Nat.add_le_add (hPt (c, z)) ih
      have hR : ∀ t1 t2 n : Nat, (W * t1 + 4 * P.scaleM * P.zProp) + (W * t2 + 4 * P.scaleM * P.zProp * n) =
          W * (t1 + t2) + 4 * P.scaleM * P.zProp * (n + 1) :=
        fun _ _ _ => by rw [Nat.mul_add W, Nat.mul_add (4 * P.scaleM * P.zProp), Nat.mul_one]; ac_rfl
      rw [hR] at hAdd; exact hAdd
  have hOuter : ∀ cs : List Nat,
      natL1Diff (prodPairs cs P.support) (realQ192TrialWeight P shift q192Num) (fun cz => W * P.rho cz.2) ≤
      W * natSumList (prodPairs cs P.support) (tailDeficitAt P shift) + 4 * cs.length * P.zProp * P.scaleM * P.support.length := by
    intro cs; induction cs with
    | nil => simp only [prodPairs, List.foldr, natL1Diff, natSumList, List.length, Nat.mul_zero, Nat.zero_mul, Nat.add_zero]; exact Nat.le_refl 0
    | cons c tl ih =>
      simp only [prodPairs, List.foldr, List.length] at ih ⊢; unfold natL1Diff at ih ⊢
      rw [natSumList_append, natSumList_append]
      have hAdd := Nat.add_le_add (hInner c P.support) ih
      have hR : ∀ t1 t2 n : Nat, (W * t1 + 4 * P.scaleM * P.zProp * P.support.length) +
          (W * t2 + 4 * n * P.zProp * P.scaleM * P.support.length) =
          W * (t1 + t2) + 4 * (n + 1) * P.zProp * P.scaleM * P.support.length :=
        fun _ _ _ => by rw [Nat.mul_add W, Nat.mul_add 4 _ 1, Nat.mul_one, Nat.add_mul, Nat.add_mul, Nat.add_mul]; ac_rfl
      unfold natL1Diff at hAdd; rw [hR] at hAdd; exact hAdd
  exact hOuter P.challenges

private theorem hvzk_nat_algebra (baseDen U T S K EK CNum A1 A2 delta1 : Nat)
    (hDPos : 0 < baseDen * (4 * U)) (hSingle : delta1 ≤ 4 * U * T + 4 * baseDen * S)
    (hRetry : EK * (baseDen * (4 * U)) ≤ 2 * K * delta1 * (baseDen * (4 * U)) ^ K)
    (hCond : CNum ≤ 2 * A1 * delta1) (hSimRate : baseDen * (4 * U) ≤ K * A2) :
    EK * (baseDen * U) ≤ K * (T * U + S * baseDen) * (2 * (baseDen * (4 * U)) ^ K) ∧
    CNum * (baseDen * U) ≤ K * (T * U + S * baseDen) * (2 * A1 * A2) := by
  let D := baseDen * (4 * U)
  have hCancel : delta1 * (baseDen * U) ≤ (T * U + S * baseDen) * D := by
    have h4 := Nat.mul_le_mul_left 4 (Nat.mul_le_mul_right (baseDen * U) hSingle)
    have hR : 4 * ((4 * U * T + 4 * baseDen * S) * (baseDen * U)) = 4 * ((T * U + S * baseDen) * (baseDen * (4 * U))) := by
      rw [Nat.add_mul, Nat.add_mul, Nat.mul_add, Nat.mul_add]; ac_rfl
    rw [hR] at h4; exact Nat.le_of_mul_le_mul_left h4 (by decide)
  constructor
  · have m := Nat.mul_le_mul_right (baseDen * U) hRetry
    have eL : EK * (baseDen * U) * D = EK * D * (baseDen * U) := by ac_rfl
    have eR : 2 * K * delta1 * D ^ K * (baseDen * U) = 2 * K * D ^ K * (delta1 * (baseDen * U)) := by ac_rfl
    have s1 : EK * (baseDen * U) * D ≤ (2 * K * D ^ K) * (delta1 * (baseDen * U)) := by rw [eL, ← eR]; exact m
    have s2 := Nat.mul_le_mul_left (2 * K * D ^ K) hCancel
    have eR2 : 2 * K * D ^ K * ((T * U + S * baseDen) * D) = K * (T * U + S * baseDen) * (2 * D ^ K) * D := by ac_rfl
    rw [eR2] at s2; exact Nat.le_of_mul_le_mul_right (Nat.le_trans s1 s2) hDPos
  · have h1 := Nat.mul_le_mul_right (baseDen * U) hCond; rw [Nat.mul_assoc (2 * A1)] at h1
    have hChain := Nat.le_trans h1 (Nat.mul_le_mul_left (2 * A1)
      (Nat.le_trans hCancel (Nat.mul_le_mul_left (T * U + S * baseDen) hSimRate)))
    have eR : 2 * A1 * ((T * U + S * baseDen) * (K * A2)) = K * (T * U + S * baseDen) * (2 * A1 * A2) := by ac_rfl
    exact eR ▸ hChain

theorem q192_gaussian_hvzk_statistical_distance
    (P : Q192GaussianSamplerParams) (shift : Nat → Int) (q192Num : Int → Int → Nat) (K : Nat)
    (hRhoLe : ∀ z : Int, P.rho z ≤ P.zProp)
    (hUlp : ∀ c z, ((q192Num z (shift c) : Int) - (acceptProbQ192FloorNum P.rho P.scaleM z (shift c) : Int)).natAbs ≤ 3)
    (hSubReal : natSumList (prodPairs P.challenges P.support) (realQ192TrialWeight P shift q192Num) ≤ P.trialDenom)
    (hSubSim : natSumList (prodPairs P.challenges P.support) (idealSimTrialWeight P) ≤ P.trialDenom)
    (hRealPos : 0 < natSumList (prodPairs P.challenges P.support) (realQ192TrialWeight P shift q192Num))
    (hSimPos : 0 < natSumList (prodPairs P.challenges P.support) (idealSimTrialWeight P))
    (hSimRate : P.trialDenom ≤ K * natSumList (prodPairs P.challenges P.support) (idealSimTrialWeight P)) :
    let bound := ExactRat.scaleNat K ((tailMassRat P shift).add (ExactRat.scaleNat P.support.length (ExactRat.twoNegPow 190)))
    ExactRat.le (q192RetryTranscriptTv P shift q192Num K) bound ∧
    ExactRat.le (q192ConditionalAcceptedTv P shift q192Num hRealPos hSimPos) bound := by
  intro bound; let pts := prodPairs P.challenges P.support; let baseDen := P.challenges.length * P.zProp * P.scaleM
  have hPow : (2 : Nat) ^ 192 = 4 * 2 ^ 190 := by rw [show (192 : Nat) = 2 + 190 from rfl, Nat.pow_add]
  have hSingle := natL1_single_trial_gen P shift q192Num (2 ^ 192) hRhoLe hUlp
  change natL1Diff pts (realQ192TrialWeight P shift q192Num) (idealSimTrialWeight P) ≤ _ at hSingle
  have hRetry := retry_full_l1_le_two_K_mul_single pts P.trialDenom
    (realQ192TrialWeight P shift q192Num) (idealSimTrialWeight P) hSubReal hSubSim K
  have hCond := conditional_accepted_l1_le_two_mul_single pts (realQ192TrialWeight P shift q192Num) (idealSimTrialWeight P)
  dsimp only at hRetry hCond
  have hDDef : P.trialDenom = baseDen * (4 * 2 ^ 190) := by unfold Q192GaussianSamplerParams.trialDenom baseDen; rw [hPow]
  have hSingle' : natL1Diff pts (realQ192TrialWeight P shift q192Num) (idealSimTrialWeight P) ≤
      4 * 2 ^ 190 * natSumList pts (tailDeficitAt P shift) + 4 * baseDen * P.support.length := by
    rw [hPow] at hSingle; simpa only [baseDen, Nat.mul_assoc] using hSingle
  have hAlg := hvzk_nat_algebra baseDen (2 ^ 190) (natSumList pts (tailDeficitAt P shift))
    P.support.length K _ _ _ _ _ (hDDef ▸ P.trialDenom_pos) hSingle' (hDDef ▸ hRetry) hCond (hDDef ▸ hSimRate)
  have hBNum : bound.num = ((K * (natSumList pts (tailDeficitAt P shift) * 2 ^ 190 + P.support.length * baseDen) : Nat) : Int) := by
    unfold bound tailMassRat ExactRat.scaleNat ExactRat.add ExactRat.twoNegPow; dsimp only
    simp only [Int.natCast_mul, Int.natCast_add, Int.mul_one, pts, baseDen]
  refine ⟨ExactRat.le_of_nat_mul rfl hBNum ?_, ExactRat.le_of_nat_mul rfl hBNum hAlg.2⟩
  change _ ≤ _ * (2 * P.trialDenom ^ K); exact hDDef.symm ▸ hAlg.1

def q192AcceptIndicatorProb (P : Q192GaussianSamplerParams) (shift : Nat → Int)
    (q192Num : Int → Int → Nat) (K : Nat) (b : Bool) : ExactRat :=
  let pts := prodPairs P.challenges P.support; let D := P.trialDenom
  let R := D - natSumList pts (realQ192TrialWeight P shift q192Num)
  ⟨((if b then D ^ K - R ^ K else R ^ K : Nat) : Int), D ^ K, Nat.pow_pos P.trialDenom_pos⟩

private theorem abort_marginal_core (D K d1 d2 R1K R2K RSK p : Nat) (b : Bool)
    (hDPos : 0 < D) (hR1Le : R1K ≤ D ^ K) (hR2Le : R2K ≤ D ^ K)
    (hAb1 : ((R1K : Int) - (RSK : Int)).natAbs * D ≤ K * d1 * D ^ K)
    (hAb2 : ((R2K : Int) - (RSK : Int)).natAbs * D ≤ K * d2 * D ^ K)
    (hS1 : 2 * K * d1 * p < D) (hS2 : 2 * K * d2 * p ≤ D) :
    (((if b then D ^ K - R1K else R1K : Nat) : Int) * ((D ^ K : Nat) : Int) -
      ((if b then D ^ K - R2K else R2K : Nat) : Int) * ((D ^ K : Nat) : Int)).natAbs * p < D ^ K * D ^ K := by
  have hDKPos : 0 < D ^ K := Nat.pow_pos hDPos
  have hTri : ((R1K : Int) - (R2K : Int)).natAbs * D ≤ (K * d1 + K * d2) * D ^ K := by
    have hAbs := Int.natAbs_add_le ((R1K : Int) - (RSK : Int)) ((RSK : Int) - (R2K : Int))
    rw [show (R1K : Int) - (RSK : Int) + ((RSK : Int) - (R2K : Int)) = (R1K : Int) - (R2K : Int) from by omega,
        show ((RSK : Int) - (R2K : Int)).natAbs = ((R2K : Int) - (RSK : Int)).natAbs from by omega] at hAbs
    have hM := Nat.mul_le_mul_right D hAbs; rw [Nat.add_mul] at hM; rw [Nat.add_mul]; exact Nat.le_trans hM (Nat.add_le_add hAb1 hAb2)
  have hSumLt : (K * d1 + K * d2) * p < D := by
    have h2 : 2 * ((K * d1 + K * d2) * p) < 2 * D := by
      have e : 2 * ((K * d1 + K * d2) * p) = 2 * K * d1 * p + 2 * K * d2 * p := by rw [Nat.add_mul, Nat.mul_add]; ac_rfl
      rw [e, Nat.two_mul D]; exact Nat.add_lt_add_of_lt_of_le hS1 hS2
    exact nat_lt_of_mul_lt_left h2
  have hRK : ((R1K : Int) - (R2K : Int)).natAbs * p < D ^ K := by
    have p1 := Nat.mul_le_mul_right p hTri; have p2 := Nat.mul_lt_mul_of_pos_right hSumLt hDKPos
    have e1 : ((R1K : Int) - (R2K : Int)).natAbs * p * D = ((R1K : Int) - (R2K : Int)).natAbs * D * p := by ac_rfl
    have e2 : (K * d1 + K * d2) * D ^ K * p = (K * d1 + K * d2) * p * D ^ K := by ac_rfl
    have hLtD : ((R1K : Int) - (R2K : Int)).natAbs * p * D < D ^ K * D := by
      rw [e1, Nat.mul_comm (D ^ K) D]; exact Nat.lt_of_le_of_lt p1 (e2.symm ▸ p2)
    exact nat_lt_of_mul_lt_right hLtD
  rw [← Int.sub_mul, Int.natAbs_mul, Int.natAbs_natCast]
  have hB : (((if b then D ^ K - R1K else R1K : Nat) : Int) - ((if b then D ^ K - R2K else R2K : Nat) : Int)).natAbs =
      ((R1K : Int) - (R2K : Int)).natAbs := by
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]; exact sub_sub_natAbs_eq hR1Le hR2Le
  rw [hB, nat_mul_right_comm _ (D ^ K) p]; exact Nat.mul_lt_mul_of_pos_right hRK hDKPos

theorem q192_gaussian_abort_marginal_secret_independent
    (P : Q192GaussianSamplerParams) (shift1 shift2 : Nat → Int) (q192Num : Int → Int → Nat) (K : Nat) (b : Bool)
    (hSub1 : natSumList (prodPairs P.challenges P.support) (realQ192TrialWeight P shift1 q192Num) ≤ P.trialDenom)
    (hSub2 : natSumList (prodPairs P.challenges P.support) (realQ192TrialWeight P shift2 q192Num) ≤ P.trialDenom)
    (hSubSim : natSumList (prodPairs P.challenges P.support) (idealSimTrialWeight P) ≤ P.trialDenom)
    (hSmall1 : 2 * K * natL1Diff (prodPairs P.challenges P.support) (realQ192TrialWeight P shift1 q192Num) (idealSimTrialWeight P) * (2 ^ 128) < P.trialDenom)
    (hSmall2 : 2 * K * natL1Diff (prodPairs P.challenges P.support) (realQ192TrialWeight P shift2 q192Num) (idealSimTrialWeight P) * (2 ^ 128) ≤ P.trialDenom) :
    ExactRat.lt (ExactRat.abs (ExactRat.sub (q192AcceptIndicatorProb P shift1 q192Num K b) (q192AcceptIndicatorProb P shift2 q192Num K b)))
      (ExactRat.twoNegPow 128) := by
  apply ExactRat.abs_lt_twoNegPow; let pts := prodPairs P.challenges P.support; let D := P.trialDenom
  exact abort_marginal_core D K _ _ _ _ _ (2 ^ 128) b P.trialDenom_pos
    (Nat.pow_le_pow_left (Nat.sub_le D _) K) (Nat.pow_le_pow_left (Nat.sub_le D _) K)
    (retry_abort_diff_le_K_mul_single pts D _ _ hSub1 hSubSim K)
    (retry_abort_diff_le_K_mul_single pts D _ _ hSub2 hSubSim K) hSmall1 hSmall2

/-! ## 4. Dense Expand-Accumulate Dual-LPN Structure & Constructive Piling-Up Lemma -/

def accPrefixXor (e : Nat → Bool) : Nat → Bool
  | 0 => e 0
  | k + 1 => Bool.xor (accPrefixXor e k) (e (k + 1))

def unitPunctureVec (pStar i : Nat) : Bool := decide (i = pStar)

theorem accUnitPuncture_eq_stepIndicator (pStar : Nat) :
    ∀ k : Nat, accPrefixXor (unitPunctureVec pStar) k = decide (pStar ≤ k)
  | 0 => by unfold accPrefixXor unitPunctureVec; by_cases h : pStar = 0 <;> simp [h]; omega
  | k + 1 => by
    simp only [accPrefixXor, accUnitPuncture_eq_stepIndicator pStar k, unitPunctureVec]
    by_cases h1 : pStar ≤ k
    · have h2 : ¬ (k + 1 = pStar) := by omega
      have h3 : pStar ≤ k + 1 := by omega
      simp [h1, h2, h3]
    · by_cases h2 : k + 1 = pStar
      · simp [h1, h2]
      · have h3 : ¬ (pStar ≤ k + 1) := by omega
        simp [h1, h2, h3]

def accSuffixXor (L : Nat) (u : Nat → Bool) (i : Nat) : Bool :=
  (List.range (L - i)).foldl (fun acc d => Bool.xor acc (u (i + d))) false
def gf2InnerProd : Nat → (Nat → Bool) → (Nat → Bool) → Bool
  | 0, _, _ => false
  | k + 1, a, b => Bool.xor (gf2InnerProd k a b) (a k && b k)

theorem acc_transpose_duality (u : Nat → Bool) (pStar : Nat) :
    ∀ d : Nat, gf2InnerProd (pStar + d) u (accPrefixXor (unitPunctureVec pStar)) = accSuffixXor (pStar + d) u pStar := by
  have hBelow : ∀ m : Nat, m ≤ pStar → gf2InnerProd m u (accPrefixXor (unitPunctureVec pStar)) = false := by
    intro m hm; induction m with
    | zero => rfl
    | succ m' ih =>
      simp only [gf2InnerProd, ih (by omega), accUnitPuncture_eq_stepIndicator]
      have hN : ¬ (pStar ≤ m') := by omega
      simp [hN]
  intro d; induction d with
  | zero => rw [Nat.add_zero, hBelow pStar (Nat.le_refl pStar)]; unfold accSuffixXor; simp [Nat.sub_self]
  | succ d' ih =>
    rw [Nat.add_succ, gf2InnerProd, ih, accUnitPuncture_eq_stepIndicator]; unfold accSuffixXor
    rw [Nat.add_sub_cancel_left, show (pStar + d').succ - pStar = d' + 1 from by omega,
        List.range_succ, List.foldl_append, List.foldl]; simp [Nat.le_add_right pStar d']

def xorStepProb (tau p : ExactRat) : ExactRat :=
  ⟨tau.num * ((p.den : Int) - p.num) + ((tau.den : Int) - tau.num) * p.num, tau.den * p.den, Nat.mul_pos tau.den_pos p.den_pos⟩
def bernoulliXorOneProb (tau : ExactRat) : Nat → ExactRat
  | 0 => ExactRat.ofInt 0
  | w + 1 => xorStepProb tau (bernoulliXorOneProb tau w)
def regularBlockXorOneProb : List ExactRat → ExactRat
  | [] => ExactRat.ofInt 0
  | tau :: tl => xorStepProb tau (regularBlockXorOneProb tl)
def parityBias (p : ExactRat) : ExactRat := ⟨(p.den : Int) - 2 * p.num, p.den, p.den_pos⟩

private theorem parityBias_xorStepProb (tau p : ExactRat) :
    parityBias (xorStepProb tau p) = ExactRat.mul (parityBias tau) (parityBias p) := by
  rcases tau with ⟨tn, td, htd⟩; rcases p with ⟨pn, pd, hpd⟩
  unfold parityBias xorStepProb ExactRat.mul; dsimp only; congr 1
  rw [Int.natCast_mul, Int.mul_sub tn, Int.sub_mul (td : Int), Int.mul_add 2, Int.mul_sub 2, Int.mul_sub 2,
      Int.mul_sub ((td : Int) - 2 * tn), Int.sub_mul (td : Int), Int.sub_mul (td : Int)]
  have c1 : 2 * tn * (pd : Int) = 2 * (tn * (pd : Int)) := Int.mul_assoc 2 tn (pd : Int)
  have c2 : (td : Int) * (2 * pn) = 2 * ((td : Int) * pn) := by ac_rfl
  have c3 : 2 * tn * (2 * pn) = 4 * (tn * pn) := by rw [Int.mul_assoc 2 tn, Int.mul_left_comm tn 2 pn, ← Int.mul_assoc 2 2]; rfl
  rw [c1, c2, c3]; omega

theorem piling_up_lemma_bernoulli_rat (tau : ExactRat) :
    ∀ w : Nat, parityBias (bernoulliXorOneProb tau w) = ExactRat.pow (parityBias tau) w
  | 0 => rfl
  | w + 1 => by simp only [bernoulliXorOneProb, ExactRat.pow, parityBias_xorStepProb, piling_up_lemma_bernoulli_rat tau w]

theorem piling_up_lemma_regular_blocks_rat :
    ∀ rates : List ExactRat, parityBias (regularBlockXorOneProb rates) =
      rates.foldr (fun tau acc => ExactRat.mul (parityBias tau) acc) (ExactRat.ofInt 1)
  | [] => rfl
  | tau :: tl => by simp only [regularBlockXorOneProb, List.foldr, parityBias_xorStepProb, piling_up_lemma_regular_blocks_rat tl]

theorem bernoulli_dual_min_weight_bias_lt_two_neg_256 (dMin : Nat) (hd : 1536 ≤ dMin) :
    let tau : ExactRat := ⟨1, 16, by decide⟩
    ExactRat.lt (ExactRat.abs (parityBias (bernoulliXorOneProb tau dMin))) (ExactRat.twoNegPow 256) := by
  intro tau; rw [piling_up_lemma_bernoulli_rat]; apply ExactRat.abs_lt_twoNegPow
  have hPowF : ∀ n : Nat, (ExactRat.pow (parityBias tau) n).num = ((14 ^ n : Nat) : Int) ∧
      (ExactRat.pow (parityBias tau) n).den = 16 ^ n := by
    intro n; induction n with
    | zero => exact ⟨rfl, rfl⟩
    | succ n' ih =>
      rw [ExactRat.pow, ExactRat.mul_num, ExactRat.mul_den, ih.1, ih.2]
      exact ⟨by change (14 : Int) * ((14 ^ n' : Nat) : Int) = _; rw [Nat.pow_succ', Int.natCast_mul]; rfl,
             by change 16 * 16 ^ n' = 16 ^ (n' + 1); rw [Nat.pow_succ']⟩
  have hBase6 : 14 ^ 6 * 2 < 16 ^ 6 := by decide
  have hStep6 : ∀ m : Nat, 14 ^ (6 * (m + 1)) * 2 ^ (m + 1) < 16 ^ (6 * (m + 1)) := by
    intro m; induction m with
    | zero => exact hBase6
    | succ m' ih =>
      rw [show 6 * (m' + 2) = 6 * (m' + 1) + 6 from by omega, Nat.pow_add 14, Nat.pow_add 16, Nat.pow_succ 2 (m' + 1), nat_mul4_swap]
      exact Nat.lt_trans (Nat.mul_lt_mul_of_pos_right ih (by decide)) (Nat.mul_lt_mul_of_pos_left hBase6 (Nat.pow_pos (by decide)))
  have hMono : ∀ k : Nat, 14 ^ (6 * (255 + 1) + k) * 2 ^ (255 + 1) < 16 ^ (6 * (255 + 1) + k) := by
    intro k; induction k with
    | zero => rw [Nat.add_zero]; exact hStep6 255
    | succ k' ih =>
      rw [Nat.add_succ, Nat.pow_succ 14, Nat.pow_succ 16, nat_mul_right_comm _ 14]
      exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right ih (by decide)) (Nat.mul_le_mul_left _ (by decide))
  rw [(hPowF dMin).1, (hPowF dMin).2, Int.natAbs_natCast]
  have hk := hMono (dMin - 1536)
  rw [show 6 * (255 + 1) + (dMin - 1536) = dMin from by omega] at hk; exact hk

def depth15TreeRate (w : Nat) : ExactRat := ⟨(w : Int), 32768, by decide⟩

theorem pcg_dense_dual_lpn_linear_bias_lt_two_neg_256
    (weights : List Nat) (hLen : weights.length = 64)
    (hBal : ∀ w ∈ weights, ((32768 : Int) - 2 * (w : Int)).natAbs ≤ 2047) :
    ExactRat.lt (ExactRat.abs (parityBias (regularBlockXorOneProb (weights.map depth15TreeRate)))) (ExactRat.twoNegPow 256) := by
  rw [piling_up_lemma_regular_blocks_rat]; apply ExactRat.abs_lt_twoNegPow
  have hProd : ∀ ws : List Nat, (∀ w ∈ ws, ((32768 : Int) - 2 * (w : Int)).natAbs ≤ 2047) →
      ((ws.map depth15TreeRate).foldr (fun tau acc => ExactRat.mul (parityBias tau) acc) (ExactRat.ofInt 1)).num.natAbs ≤ 2047 ^ ws.length ∧
      ((ws.map depth15TreeRate).foldr (fun tau acc => ExactRat.mul (parityBias tau) acc) (ExactRat.ofInt 1)).den = 32768 ^ ws.length := by
    intro ws hW; induction ws with
    | nil => exact ⟨by decide, rfl⟩
    | cons w tl ih =>
      have htl := ih (fun x hx => hW x (.tail w hx))
      rw [List.map_cons, List.foldr_cons, ExactRat.mul_num, ExactRat.mul_den, List.length_cons]
      exact ⟨by rw [Int.natAbs_mul, Nat.pow_succ']; exact Nat.mul_le_mul (hW w (.head tl)) htl.1, by rw [htl.2, Nat.pow_succ']; rfl⟩
  have h64 := hProd weights hBal; rw [hLen] at h64; rw [h64.2]
  have hScale : ∀ m : Nat, 2048 ^ m * 2 ^ (4 * m) = 32768 ^ m := by
    intro m; induction m with
    | zero => rfl
    | succ m' ih =>
      rw [show 4 * (m' + 1) = 4 * m' + 4 from by omega, Nat.pow_succ 2048, Nat.pow_add 2, Nat.pow_succ 32768,
          ← ih, nat_mul4_swap, show 2048 * 2 ^ 4 = 32768 from by decide]
  rw [← hScale 64]
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right (2 ^ 256) h64.1)
    (Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_left (by decide) (by decide)) (Nat.two_pow_pos 256))

/-! ## 5. Prange & Universal Stern–Dumer ISD Work-Factor Lower Bounds (`Depth15`) -/

def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, j + 1 => binom n j + binom n (j + 1)

theorem binom_zero_right (n : Nat) : binom n 0 = 1 := by cases n <;> rfl
theorem binom_one_right : ∀ n : Nat, binom n 1 = n
  | 0 => rfl
  | n + 1 => by simp only [binom, binom_one_right n, binom_zero_right n]; omega

theorem binom_mul_succ : ∀ (n j : Nat), (j + 1) * binom (n + 1) (j + 1) = (n + 1) * binom n j
  | 0, 0 => rfl
  | 0, _ + 1 => Nat.mul_zero _
  | n + 1, 0 => by rw [Nat.zero_add, binom_one_right (n + 2), binom_zero_right (n + 1), Nat.one_mul, Nat.mul_one]
  | n + 1, j + 1 => by
    have ih1 : (j + 1) * (binom n j + binom n (j + 1)) = (n + 1) * binom n j := binom_mul_succ n j
    have ih2 : (j + 2) * binom (n + 1) (j + 2) = (n + 1) * binom n (j + 1) := binom_mul_succ n (j + 1)
    change (j + 2) * ((binom n j + binom n (j + 1)) + binom (n + 1) (j + 2)) = (n + 2) * (binom n j + binom n (j + 1))
    have hL : (j + 2) * (binom n j + binom n (j + 1)) =
        (binom n j + binom n (j + 1)) + (j + 1) * (binom n j + binom n (j + 1)) := by
      rw [show j + 2 = 1 + (j + 1) from by omega, Nat.add_mul, Nat.one_mul]
    have hR : (n + 2) * (binom n j + binom n (j + 1)) =
        (binom n j + binom n (j + 1)) + ((n + 1) * binom n j + (n + 1) * binom n (j + 1)) := by
      rw [show n + 2 = 1 + (n + 1) from by omega, Nat.add_mul, Nat.one_mul, Nat.mul_add]
    rw [Nat.mul_add (j + 2), hL, ih1, ih2, hR, Nat.add_assoc]

theorem binom_step_right (n j : Nat) : (j + 1) * binom n (j + 1) = (n - j) * binom n j := by
  by_cases hLe : j ≤ n
  · have hAbs : (j + 1) * (binom n j + binom n (j + 1)) = (n + 1) * binom n j := binom_mul_succ n j
    rw [Nat.mul_add] at hAbs
    have hSub : (j + 1) * binom n j + (n - j) * binom n j = (n + 1) * binom n j := by
      rw [← Nat.add_mul, show j + 1 + (n - j) = n + 1 from by omega]
    omega
  · have hZ : ∀ m k : Nat, m < k → binom m k = 0 := by
      intro m; induction m with
      | zero => intro k hk; cases k with | zero => omega | succ _ => rfl
      | succ _ ih => intro k hk; cases k with | zero => omega | succ k' => simp only [binom, ih k' (by omega), ih (k' + 1) (by omega)]
    rw [hZ n (j + 1) (by omega), show n - j = 0 from by omega, Nat.zero_mul, Nat.mul_zero]

theorem binom_mono_left {a b : Nat} (h : a ≤ b) : ∀ j : Nat, binom a j ≤ binom b j := by
  induction h with
  | refl => intro _; exact Nat.le_refl _
  | step _ ih => intro j; cases j with
    | zero => simp only [binom_zero_right]; exact Nat.le_refl 1
    | succ j' => simp only [binom]; exact Nat.le_trans (ih (j' + 1)) (Nat.le_add_left _ _)

theorem binom_pos : ∀ {n j : Nat}, j ≤ n → 0 < binom n j
  | n, 0, _ => by rw [binom_zero_right n]; exact Nat.one_pos
  | 0, _ + 1, h => by omega
  | n + 1, j + 1, h => by simp only [binom]; exact Nat.add_pos_left (binom_pos (n := n) (j := j) (by omega)) _

theorem binom_scale_lower_bound {c : Nat} (hc : 1 ≤ c) :
    ∀ {t r M : Nat}, t ≤ r → c * r ≤ M → c ^ t * binom r t ≤ binom M t
  | 0, _, _, _, _ => by rw [Nat.pow_zero, binom_zero_right, binom_zero_right, Nat.one_mul]; exact Nat.le_refl 1
  | _ + 1, 0, _, ht, _ => by omega
  | _ + 1, r + 1, 0, _, hcr => False.elim (Nat.ne_of_gt (Nat.mul_pos hc (Nat.succ_pos r)) (Nat.eq_zero_of_le_zero hcr))
  | t + 1, r + 1, M + 1, ht, hcr => by
    have hcr' : c * r ≤ M := by rw [Nat.mul_add, Nat.mul_one] at hcr; omega
    have hMul := Nat.mul_le_mul hcr (binom_scale_lower_bound hc (t := t) (r := r) (M := M) (by omega) hcr')
    have hRe : c * (r + 1) * (c ^ t * binom r t) = (t + 1) * (c ^ (t + 1) * binom (r + 1) (t + 1)) := by
      have p : c * (r + 1) * (c ^ t * binom r t) = c ^ (t + 1) * ((r + 1) * binom r t) := by rw [Nat.pow_succ']; ac_rfl
      rw [p, ← binom_mul_succ r t]; ac_rfl
    rw [hRe, ← binom_mul_succ M t] at hMul; exact Nat.le_of_mul_le_mul_left hMul (Nat.succ_pos t)

theorem binom_scale_upper_bound (c : Nat) :
    ∀ {t M r : Nat}, t ≤ r → M ≤ c * (r - t) → binom M t ≤ c ^ t * binom r t
  | 0, _, _, _, _ => by rw [binom_zero_right, binom_zero_right, Nat.pow_zero, Nat.one_mul]; exact Nat.le_refl 1
  | _ + 1, 0, _, _, _ => Nat.zero_le _
  | _ + 1, _ + 1, 0, ht, _ => by omega
  | t + 1, M + 1, r + 1, ht, hMc => by
    rw [Nat.succ_sub_succ] at hMc
    have ih := binom_scale_upper_bound c (t := t) (M := M) (r := r) (by omega) (Nat.le_of_succ_le hMc)
    have hMul := Nat.mul_le_mul (Nat.le_trans hMc (Nat.mul_le_mul_left c (Nat.le_trans (Nat.sub_le r t) (Nat.le_succ r)))) ih
    have hRhs : c * (r + 1) * (c ^ t * binom r t) = (t + 1) * (c ^ (t + 1) * binom (r + 1) (t + 1)) := by
      have p : c * (r + 1) * (c ^ t * binom r t) = c ^ (t + 1) * ((r + 1) * binom r t) := by rw [Nat.pow_succ']; ac_rfl
      rw [p, ← binom_mul_succ r t]; ac_rfl
    rw [← binom_mul_succ M t, hRhs] at hMul; exact Nat.le_of_mul_le_mul_left hMul (Nat.succ_pos t)

attribute [irreducible] binom

private theorem binom_step2 (n u : Nat) : (u + 2) * (u + 1) * binom n (u + 2) = (n - (u + 1)) * (n - u) * binom n u := by
  have s1 := binom_step_right n (u + 1); have s0 := binom_step_right n u
  calc (u + 2) * (u + 1) * binom n (u + 2) = (u + 1) * ((u + 2) * binom n (u + 2)) := by ac_rfl
    _ = (n - (u + 1)) * ((u + 1) * binom n (u + 1)) := by rw [s1]; ac_rfl
    _ = (n - (u + 1)) * (n - u) * binom n u := by rw [s0]; ac_rfl

private theorem chain_rel2 (k1 k2 d1 d2 b4 b2 b0 : Nat) (h1 : k1 * b4 = d1 * b2) (h2 : k2 * b2 = d2 * b0) :
    (k1 * k2) * b4 = (d1 * d2) * b0 := by
  calc (k1 * k2) * b4 = k2 * (k1 * b4) := by ac_rfl
    _ = d1 * (k2 * b2) := by rw [h1]; ac_rfl
    _ = (d1 * d2) * b0 := by rw [h2]; ac_rfl

private theorem step_ratio_le (m3 subL u21 subR bL3 bL2 bRu bRu2 : Nat)
    (hPos : 0 < m3 * u21) (hRatio : subL * u21 ≤ m3 * subR) (h1 : m3 * bL3 = subL * bL2) (h2 : u21 * bRu2 = subR * bRu) :
    bL3 * bRu ≤ bL2 * bRu2 := by
  have m := Nat.mul_le_mul_right (bL2 * bRu) hRatio
  have e1 : subL * u21 * (bL2 * bRu) = m3 * u21 * (bL3 * bRu) := by
    calc subL * u21 * (bL2 * bRu) = u21 * (subL * bL2) * bRu := by ac_rfl
      _ = m3 * u21 * (bL3 * bRu) := by rw [← h1]; ac_rfl
  have e2 : m3 * subR * (bL2 * bRu) = m3 * u21 * (bL2 * bRu2) := by
    calc m3 * subR * (bL2 * bRu) = m3 * bL2 * (subR * bRu) := by ac_rfl
      _ = m3 * u21 * (bL2 * bRu2) := by rw [← h2]; ac_rfl
  rw [e1, e2] at m; exact Nat.le_of_mul_le_mul_left m hPos

private theorem scale_binom_bound (P256 P15 K A R D bHi bLo : Nat)
    (hK : 0 < K) (hP : P256 ≤ 81 * P15) (hRel : K * bHi = D * bLo) (hNum : K * A * 81 ≤ R * D) :
    P256 * (A * bLo) ≤ R * (P15 * bHi) := by
  have m1 := Nat.mul_le_mul_left (K * A) hP; have m2 := Nat.mul_le_mul_right P15 hNum
  have r1 : K * A * (81 * P15) = K * A * 81 * P15 := by ac_rfl
  have m3 := Nat.mul_le_mul_right bLo (Nat.le_trans m1 (r1 ▸ m2))
  have eL : K * A * P256 * bLo = K * (P256 * (A * bLo)) := by ac_rfl
  have eR : R * D * P15 * bLo = K * (R * (P15 * bHi)) := by
    calc R * D * P15 * bLo = R * P15 * (D * bLo) := by ac_rfl
      _ = K * (R * (P15 * bHi)) := by rw [← hRel]; ac_rfl
  rw [eL, eR] at m3; exact Nat.le_of_mul_le_mul_left m3 hK

private theorem finish_q2_bound (P256 P15 L2 Lq R0 b64 b60 bq : Nat)
    (hMono : Lq * bq ≤ L2 * b60) (hBase2 : P256 * ((2 * L2) * b60) ≤ 4 * (P15 * b64)) :
    P256 * (Lq ^ 2 * bq) ≤ (R0 + 2 * Lq) * (P15 * b64) := by
  have e2 : P256 * ((2 * L2) * b60) = 2 * (P256 * (L2 * b60)) := by ac_rfl
  have e4 : 4 * (P15 * b64) = 2 * (2 * (P15 * b64)) := by rw [show (4 : Nat) = 2 * 2 from rfl, Nat.mul_assoc]
  rw [e2, e4] at hBase2; have hBase := Nat.le_of_mul_le_mul_left hBase2 (by decide)
  have hMulLq := Nat.mul_le_mul_left Lq (Nat.le_trans (Nat.mul_le_mul_left P256 hMono) hBase)
  have fL : Lq * (P256 * (Lq * bq)) = P256 * (Lq ^ 2 * bq) := by rw [Nat.pow_two]; ac_rfl
  have fR : Lq * (2 * (P15 * b64)) ≤ (R0 + 2 * Lq) * (P15 * b64) := by
    have c : Lq * (2 * (P15 * b64)) = (2 * Lq) * (P15 * b64) := by ac_rfl
    rw [c]; exact Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
  rw [fL] at hMulLq; exact Nat.le_trans hMulLq fR

def pcgDenseRows : Nat := 136 * 1024
def pcgDenseWeightT : Nat := 64
def pcgDepth15Cols : Nat := 2048 * 1024
def pcgDepth14Cols : Nat := 1024 * 1024

def sternDumerWorkExceedsPow2 (M r t q l bits : Nat) : Prop :=
  let Lq := binom ((M - r) / 2) q
  2 ^ bits * (Lq ^ 2 * binom (r - l) (t - 2 * q)) ≤ (r ^ 2 + 2 * Lq + Lq ^ 2 / (2 ^ l)) * binom M t

private theorem add_sub_ge_gen (A B d : Nat) (hd : d ≤ B) : A ≤ (A + B) - d := by omega

private theorem rows_sub_ge (d : Nat) (hd : d ≤ 1024) : 135 * 1024 ≤ pcgDenseRows - d := by
  have h : pcgDenseRows = 135 * 1024 + 1024 := by unfold pcgDenseRows; rw [show (136 : Nat) = 135 + 1 from rfl, Nat.add_mul, Nat.one_mul]
  rw [h]; exact add_sub_ge_gen (135 * 1024) 1024 d hd

private theorem half_diff_depth15 : (pcgDepth15Cols - pcgDenseRows) / 2 = 956 * 1024 := by
  unfold pcgDepth15Cols pcgDenseRows
  rw [← Nat.sub_mul, show 2048 - 136 = 2 * 956 from by decide, Nat.mul_assoc 2 956 1024, Nat.mul_div_right _ (by decide : 0 < 2)]

private theorem half_diff_depth14 : (pcgDepth14Cols - pcgDenseRows) / 2 = 888 * 512 := by
  unfold pcgDepth14Cols pcgDenseRows
  have h1024 : 888 * 1024 = 2 * (888 * 512) := by decide
  rw [← Nat.sub_mul, show 1024 - 136 = 888 from by decide, h1024, Nat.mul_div_right _ (by decide : 0 < 2)]

private theorem fifteen_pow64_gt_256 : 2 ^ 256 < 81 * 15 ^ 64 := by
  have sq : ∀ a b c : Nat, 0 < a → 0 < b → 0 < c → a < c * b → a * a < (c * c) * (b * b) := by
    intro a b c ha hb hc h; rw [nat_mul4_swap c c b b]
    exact Nat.lt_trans (Nat.mul_lt_mul_of_pos_right h ha) (Nat.mul_lt_mul_of_pos_left h (Nat.mul_pos hc hb))
  have h2 := sq (2 ^ 64) (15 ^ 16) 3 (Nat.two_pow_pos 64) (Nat.pow_pos (by decide)) (by decide) (by decide)
  rw [← Nat.pow_add, ← Nat.pow_add] at h2
  have h3 := sq (2 ^ 128) (15 ^ 32) 9 (Nat.two_pow_pos 128) (Nat.pow_pos (by decide)) (by decide) h2
  rw [← Nat.pow_add, ← Nat.pow_add] at h3; exact h3

private theorem sq956_bound (K : Nat) (hK : 32 * 32 = K) : (956 * K) * (956 * K) ≤ (15 * 64) * K * K * K := by
  have m := Nat.mul_le_mul (by decide : 956 ≤ 30 * 32) (by decide : 956 ≤ 30 * 32)
  rw [nat_mul4_swap 30 32 30 32, hK] at m
  have m2 := Nat.le_trans m (Nat.mul_le_mul_right K (by decide : 30 * 30 ≤ 15 * 64))
  have eL : (956 * K) * (956 * K) = (956 * 956) * (K * K) := nat_mul4_swap 956 K 956 K
  have eR : ((15 * 64) * K) * (K * K) = (15 * 64) * K * K * K := by ac_rfl
  rw [eL, ← eR]; exact Nat.mul_le_mul_right (K * K) m2

private theorem q1_num_bound (K R0 R63 R62 : Nat) (hK : 32 * 32 = K) (hK1024 : 5 * 1024 ≤ 5 * K)
    (hR1 : 32 * K ≤ R0) (hR2 : 32 * K ≤ R63) (hR3 : 32 * K ≤ R62) :
    (64 * 63) * ((956 * K) ^ 2) * 81 ≤ (R0 ^ 2 + 2 * (956 * K)) * (R63 * R62) := by
  have h63 : (64 * 63) * 81 ≤ 5 * 64 * K := by
    have p := Nat.mul_le_mul_left 64 (Nat.le_trans (by decide : 63 * 81 ≤ 5 * 1024) hK1024)
    have e : 64 * (5 * K) = 5 * 64 * K := by ac_rfl
    rw [e] at p; exact p
  have hSq : (956 * K) ^ 2 ≤ (15 * 64) * K * K * K := by rw [Nat.pow_two]; exact sq956_bound K hK
  have hL1 := Nat.mul_le_mul h63 hSq
  have eL1 : (64 * 63) * 81 * (956 * K) ^ 2 = (64 * 63) * (956 * K) ^ 2 * 81 := by ac_rfl
  have eL2 : (5 * 64 * K) * ((15 * 64) * K * K * K) = (5 * 64 * (15 * 64)) * (K * K * K * K) := by ac_rfl
  rw [eL1, eL2] at hL1
  have hCoeff : 5 * 64 * (15 * 64) ≤ 32 * 32 * 32 * 32 := by
    have e : 5 * (2 * 32) * (15 * (2 * 32)) = (5 * 2 * 15 * 2) * 32 * 32 := by ac_rfl
    rw [show (64 : Nat) = 2 * 32 from rfl, e]
    exact Nat.mul_le_mul_right 32 (Nat.mul_le_mul_right 32 (by decide : 5 * 2 * 15 * 2 ≤ 32 * 32))
  have hR1Sq : 32 * K * (32 * K) ≤ R0 ^ 2 + 2 * (956 * K) := by
    rw [Nat.pow_two]; exact Nat.le_trans (Nat.mul_le_mul hR1 hR1) (Nat.le_add_right _ _)
  have hRProd := Nat.mul_le_mul hR1Sq (Nat.mul_le_mul hR2 hR3)
  have eR : (32 * K * (32 * K)) * (32 * K * (32 * K)) = (32 * 32 * 32 * 32) * (K * K * K * K) := by ac_rfl
  rw [eR] at hRProd
  exact Nat.le_trans hL1 (Nat.le_trans (Nat.mul_le_mul_right _ hCoeff) hRProd)

private theorem q2_num_bound (K H R63 R62 R61 R60 : Nat)
    (hK : 32 * 32 = K) (hK64 : 64 * 16 = K) (hH : 2 * H = K) (hK5 : 63 * 81 ≤ 5 * K)
    (h63 : 135 * K ≤ R63) (h62 : 135 * K ≤ R62) (h61 : 135 * K ≤ R61) (h60 : 135 * K ≤ R60) :
    ((64 * 63) * (62 * 61)) * ((956 * K - 1) * (956 * K)) * 81 ≤ 4 * ((R63 * R62) * (R61 * R60)) := by
  have hA : ((64 * 63) * (62 * 61)) * 81 ≤ (75 * 16) * (K * K) := by
    have p2 : 64 * (62 * 61) ≤ 240 * K := by
      have c := Nat.mul_le_mul_left 64 (by decide : 62 * 61 ≤ 240 * 16)
      have e : 64 * (240 * 16) = 240 * (64 * 16) := by ac_rfl
      rw [e, hK64] at c; exact c
    have m := Nat.mul_le_mul hK5 p2
    have eL : (63 * 81) * (64 * (62 * 61)) = ((64 * 63) * (62 * 61)) * 81 := by ac_rfl
    have eR : (5 * K) * (240 * K) = (5 * 240) * (K * K) := by ac_rfl
    rw [eL, eR, show 5 * 240 = 75 * 16 from by decide] at m; exact m
  have hB : (956 * K - 1) * (956 * K) ≤ (15 * 64) * K * K * K :=
    Nat.le_trans (Nat.mul_le_mul_right _ (Nat.sub_le _ 1)) (sq956_bound K hK)
  have hAB := Nat.mul_le_mul hA hB
  have eAB1 : ((64 * 63) * (62 * 61)) * 81 * ((956 * K - 1) * (956 * K)) =
      ((64 * 63) * (62 * 61)) * ((956 * K - 1) * (956 * K)) * 81 := by ac_rfl
  have eAB2 : ((75 * 16) * (K * K)) * ((15 * 64) * K * K * K) = (75 * 15) * (64 * 16) * (K * K * K * K * K) := by ac_rfl
  rw [eAB1, eAB2, hK64] at hAB
  have h135 : 35 * H ≤ 135 * 135 := by
    have h2 : 2 * (16 * 32) = 2 * H := by rw [hH, ← hK]
    have hH16 : 16 * 32 = H := Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) h2
    have m := Nat.mul_le_mul (by decide : 5 * 16 ≤ 9 * 9) (by decide : 7 * 32 ≤ 15 * 15)
    rw [nat_mul4_swap 5 16 7 32, nat_mul4_swap 9 9 15 15, hH16, show 9 * 15 = 135 from by decide] at m; exact m
  have h135_4 : (35 * 35) * (K * K) ≤ 4 * ((135 * 135) * (135 * 135)) := by
    have m := Nat.mul_le_mul_left 4 (Nat.mul_le_mul h135 h135)
    have e : 4 * ((35 * H) * (35 * H)) = (35 * 35) * ((2 * H) * (2 * H)) := by rw [show (4 : Nat) = 2 * 2 from rfl]; ac_rfl
    rw [e, hH] at m; exact m
  have hR4 := Nat.mul_le_mul_left 4 (Nat.mul_le_mul (Nat.mul_le_mul h63 h62) (Nat.mul_le_mul h61 h60))
  have eR4 : 4 * (((135 * K) * (135 * K)) * ((135 * K) * (135 * K))) = (4 * ((135 * 135) * (135 * 135))) * (K * K * K * K) := by ac_rfl
  rw [eR4] at hR4
  have c2 := Nat.mul_le_mul_right (K * K * K * K) (Nat.le_trans (Nat.mul_le_mul_right (K * K) (by decide : 75 * 15 ≤ 35 * 35)) h135_4)
  have ec : (75 * 15) * (K * K) * (K * K * K * K) = (75 * 15) * K * (K * K * K * K * K) := by ac_rfl
  rw [ec] at c2
  exact Nat.le_trans hAB (Nat.le_trans c2 hR4)

private theorem mono_q_ratio (K subL u21 m3 R1 R2 : Nat)
    (hSubL : subL ≤ K * K) (hU : u21 ≤ 4 * K) (hm : 3 ≤ m3) (hR1 : 64 * K ≤ R1) (hR2 : 64 * K ≤ R2)
    (h64 : 4 * K ≤ 3 * (64 * 64)) : subL * u21 ≤ m3 * (R1 * R2) := by
  have hL := Nat.mul_le_mul hSubL hU
  have eL : (K * K) * (4 * K) = (4 * K) * (K * K) := by ac_rfl
  rw [eL] at hL
  have hR := Nat.mul_le_mul hm (Nat.mul_le_mul hR1 hR2)
  have eR : 3 * ((64 * K) * (64 * K)) = (3 * (64 * 64)) * (K * K) := by ac_rfl
  rw [eR] at hR
  exact Nat.le_trans hL (Nat.le_trans (Nat.mul_le_mul_right (K * K) h64) hR)

private theorem stern_dumer_depth15_gen (B : Nat → Nat → Nat)
    (bZero : ∀ n, B n 0 = 1) (bOne : ∀ n, B n 1 = n)
    (bStep : ∀ n j, (j + 1) * B n (j + 1) = (n - j) * B n j)
    (bStep2 : ∀ n u, (u + 2) * (u + 1) * B n (u + 2) = (n - (u + 1)) * (n - u) * B n u)
    (bMono : ∀ {a b}, a ≤ b → ∀ j, B a j ≤ B b j)
    (hScaleM : 15 ^ 64 * B pcgDenseRows 64 ≤ B pcgDepth15Cols 64)
    (q l : Nat) (hq : q ≤ 32) :
    let Lq := B ((pcgDepth15Cols - pcgDenseRows) / 2) q
    2 ^ 256 * (Lq ^ 2 * B (pcgDenseRows - l) (pcgDenseWeightT - 2 * q)) ≤
      (pcgDenseRows ^ 2 + 2 * Lq + Lq ^ 2 / (2 ^ l)) * B pcgDepth15Cols pcgDenseWeightT := by
  dsimp only; rw [half_diff_depth15]; unfold pcgDenseWeightT
  have hWin := bMono (Nat.sub_le pcgDenseRows l) (64 - 2 * q)
  suffices hCore : 2 ^ 256 * (B (956 * 1024) q ^ 2 * B pcgDenseRows (64 - 2 * q)) ≤
      (pcgDenseRows ^ 2 + 2 * B (956 * 1024) q) * (15 ^ 64 * B pcgDenseRows 64) by
    exact Nat.le_trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hWin))
      (Nat.le_trans hCore (Nat.mul_le_mul (Nat.le_add_right _ _) hScaleM))
  have h15 := Nat.le_of_lt fifteen_pow64_gt_256
  match q with
  | 0 =>
    rw [bZero]; simp only [Nat.one_pow, Nat.one_mul, Nat.mul_one, ← Nat.mul_assoc]
    have h9 : 9 ≤ pcgDenseRows := Nat.le_trans (by decide : 9 ≤ 1024) (Nat.le_mul_of_pos_left 1024 (by decide : 0 < 136))
    have h81 : 81 ≤ pcgDenseRows ^ 2 + 2 := Nat.le_trans (by rw [Nat.pow_two]; exact Nat.mul_le_mul h9 h9) (Nat.le_add_right _ 2)
    exact Nat.mul_le_mul_right _ (Nat.le_trans h15 (Nat.mul_le_mul_right _ h81))
  | 1 =>
    rw [bOne]
    exact scale_binom_bound (2 ^ 256) (15 ^ 64) (64 * 63) ((956 * 1024) ^ 2)
      (pcgDenseRows ^ 2 + 2 * (956 * 1024)) ((pcgDenseRows - 63) * (pcgDenseRows - 62))
      _ _ (by decide) h15 (bStep2 pcgDenseRows 62)
      (q1_num_bound 1024 pcgDenseRows _ _ (by decide) (Nat.le_refl _)
        (by unfold pcgDenseRows; exact Nat.mul_le_mul_right 1024 (by decide))
        (Nat.le_trans (Nat.mul_le_mul_right 1024 (by decide)) (rows_sub_ge 63 (by decide)))
        (Nat.le_trans (Nat.mul_le_mul_right 1024 (by decide)) (rows_sub_ge 62 (by decide))))
  | q' + 2 =>
    have hMonoQ : ∀ m : Nat, m ≤ 30 →
        B (956 * 1024) (m + 2) * B pcgDenseRows (64 - 2 * (m + 2)) ≤ B (956 * 1024) 2 * B pcgDenseRows 60 := by
      intro m hm; induction m with
      | zero => exact Nat.le_refl _
      | succ m' ih =>
        refine Nat.le_trans ?_ (ih (by omega))
        rw [show 64 - 2 * (m' + 3) = 58 - 2 * m' from by omega, show 64 - 2 * (m' + 2) = (58 - 2 * m') + 2 from by omega]
        let u := 58 - 2 * m'
        have huMax : u + 2 ≤ 60 := by unfold u; omega
        have hRatio := mono_q_ratio 1024 (956 * 1024 - (m' + 2)) ((u + 2) * (u + 1)) (m' + 3)
          (pcgDenseRows - (u + 1)) (pcgDenseRows - u)
          (Nat.le_trans (Nat.sub_le _ _) (Nat.mul_le_mul_right 1024 (by decide)))
          (Nat.le_trans (Nat.mul_le_mul huMax (by omega : u + 1 ≤ 60)) (by decide)) (by omega)
          (Nat.le_trans (Nat.mul_le_mul_right 1024 (by decide : 64 ≤ 135)) (rows_sub_ge (u + 1) (by omega)))
          (Nat.le_trans (Nat.mul_le_mul_right 1024 (by decide : 64 ≤ 135)) (rows_sub_ge u (by omega)))
          (by decide)
        exact step_ratio_le (m' + 3) (956 * 1024 - (m' + 2)) ((u + 2) * (u + 1))
          ((pcgDenseRows - (u + 1)) * (pcgDenseRows - u)) _ _ _ _
          (Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega))) hRatio
          (bStep (956 * 1024) (m' + 2)) (bStep2 pcgDenseRows u)
    have sL1 := bStep (956 * 1024) 1; rw [bOne] at sL1
    change 2 * B (956 * 1024) 2 = (956 * 1024 - 1) * (956 * 1024) at sL1
    have hRel4 := chain_rel2 _ _ _ _ _ _ _ (bStep2 pcgDenseRows 62) (bStep2 pcgDenseRows 60)
    have hBase2 := scale_binom_bound (2 ^ 256) (15 ^ 64) ((64 * 63) * (62 * 61))
      (2 * B (956 * 1024) 2) 4 (((pcgDenseRows - 63) * (pcgDenseRows - 62)) * ((pcgDenseRows - 61) * (pcgDenseRows - 60)))
      _ _ (by decide) h15 hRel4
      (by rw [sL1]; exact q2_num_bound 1024 512 _ _ _ _ (by decide) (by decide) (by decide) (by decide)
            (rows_sub_ge 63 (by decide)) (rows_sub_ge 62 (by decide)) (rows_sub_ge 61 (by decide)) (rows_sub_ge 60 (by decide)))
    exact finish_q2_bound (2 ^ 256) (15 ^ 64) _ _ (pcgDenseRows ^ 2) _ _ _ (hMonoQ q' (by omega)) hBase2

theorem pcg_dense_depth15_prange_and_stern_dumer_pq128 (q l : Nat) (hq : q ≤ 32) :
    sternDumerWorkExceedsPow2 pcgDepth15Cols pcgDenseRows pcgDenseWeightT q l 256 ∧ 256 / 2 = 128 :=
  ⟨stern_dumer_depth15_gen binom binom_zero_right binom_one_right binom_step_right binom_step2
    (fun h => binom_mono_left h)
    (binom_scale_lower_bound (by decide)
      (Nat.le_trans (by decide : 64 ≤ 1024) (Nat.le_mul_of_pos_left 1024 (by decide : 0 < 136)))
      (by unfold pcgDenseRows pcgDepth15Cols; rw [← Nat.mul_assoc 15 136 1024]; exact Nat.mul_le_mul_right 1024 (by decide)))
    q l hq, rfl⟩

private theorem contra_isd_bound (C L2 bM bW P39 P80 P180 P256 P70 : Nat)
    (hbW : 0 < bW) (hP : 0 < P80 * P180) (hBM : bM ≤ P80 * P180 * bW) (hCost : C < P39)
    (hSq : P70 ≤ L2 ^ 2) (hPow : P39 * P80 * P180 ≤ P256 * P70) (hIn : P256 * (L2 ^ 2 * bW) ≤ C * bM) : False := by
  have hUp : C * bM < P39 * P80 * P180 * bW := by
    have t := Nat.lt_of_le_of_lt (Nat.mul_le_mul_left C hBM)
      (Nat.mul_lt_mul_of_pos_right hCost (Nat.mul_pos hP hbW))
    have e : P39 * ((P80 * P180) * bW) = P39 * P80 * P180 * bW := by ac_rfl
    rw [e] at t; exact t
  have hDn : P39 * P80 * P180 * bW ≤ C * bM := by
    have s1 := Nat.mul_le_mul_right bW hPow; rw [Nat.mul_assoc P256 P70 bW] at s1
    exact Nat.le_trans s1 (Nat.le_trans (Nat.mul_le_mul_left P256 (Nat.mul_le_mul_right bW hSq)) hIn)
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hUp hDn)

private theorem l2_cost_and_sq (L2 R0 P35 P36 P37 P22 P52 P70 P74 P39 : Nat)
    (hP35 : 0 < P35) (hP37 : 0 < P37) (hR0 : R0 ^ 2 < P36) (hLo : P35 ≤ L2) (hHi : L2 < P37)
    (hSq70 : P35 * P35 = P70) (hSq74 : P37 * P37 = P74) (hDiv74 : P74 = P22 * P52) (h22 : P22 ≤ P36)
    (hSum : P36 + 2 * P37 + P36 ≤ P39) : R0 ^ 2 + 2 * L2 + L2 ^ 2 / P52 < P39 ∧ P70 ≤ L2 ^ 2 := by
  have hSqLt : L2 ^ 2 < P74 := by
    rw [Nat.pow_two, ← hSq74]
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right L2 (Nat.le_of_lt hHi)) (Nat.mul_lt_mul_of_pos_left hHi hP37)
  have _ := hP35
  have hDivLe : L2 ^ 2 / P52 ≤ P36 := Nat.le_trans
    (Nat.div_le_of_le_mul (by rw [Nat.mul_comm P52 P22, ← hDiv74]; exact Nat.le_of_lt hSqLt)) h22
  refine ⟨Nat.lt_of_lt_of_le (Nat.add_lt_add_of_lt_of_le
      (Nat.add_lt_add_of_lt_of_le hR0 (Nat.mul_le_mul_left 2 (Nat.le_of_lt hHi))) hDivLe) hSum, ?_⟩
  rw [Nat.pow_two, ← hSq70]; exact Nat.mul_le_mul hLo hLo

private theorem stern_dumer_depth14_contra_gen (B : Nat → Nat → Nat)
    (bOne : ∀ n, B n 1 = n) (bStep : ∀ n j, (j + 1) * B n (j + 1) = (n - j) * B n j)
    (hUp60 : B pcgDepth14Cols 60 ≤ 8 ^ 60 * B (pcgDenseRows - 52) 60)
    (hPos60 : 0 < B (pcgDenseRows - 52) 60)
    (hBad : let Lq := B ((pcgDepth14Cols - pcgDenseRows) / 2) 2
      2 ^ 256 * (Lq ^ 2 * B (pcgDenseRows - 52) (pcgDenseWeightT - 2 * 2)) ≤
        (pcgDenseRows ^ 2 + 2 * Lq + Lq ^ 2 / (2 ^ 52)) * B pcgDepth14Cols pcgDenseWeightT) : False := by
  dsimp only at hBad; rw [half_diff_depth14] at hBad; unfold pcgDenseWeightT at hBad
  have hM14 : pcgDepth14Cols = 2 ^ 20 := by
    unfold pcgDepth14Cols; rw [show (1024 : Nat) = 2 ^ 10 from by decide, ← Nat.pow_add]
  have hStepUp : ∀ j : Nat, B pcgDepth14Cols (j + 1) ≤ 2 ^ 20 * B pcgDepth14Cols j := by
    intro j; have s := bStep pcgDepth14Cols j
    have p1 : B pcgDepth14Cols (j + 1) ≤ (j + 1) * B pcgDepth14Cols (j + 1) := Nat.le_mul_of_pos_left _ (Nat.succ_pos j)
    rw [s] at p1; exact Nat.le_trans p1 (Nat.mul_le_mul_right _ (hM14 ▸ Nat.sub_le pcgDepth14Cols j))
  have p8 : ∀ m : Nat, 8 ^ m = 2 ^ (3 * m) := by
    intro m; induction m with
    | zero => rfl
    | succ m' ih => rw [show 3 * (m' + 1) = 3 * m' + 3 from by omega, Nat.pow_succ 8, ih, Nat.pow_add 2]
  have hUp64 : B pcgDepth14Cols 64 ≤ 2 ^ 80 * 2 ^ 180 * B (pcgDenseRows - 52) 60 := by
    have p := Nat.le_trans (hStepUp 63) (Nat.mul_le_mul_left (2 ^ 20) (Nat.le_trans (hStepUp 62)
      (Nat.mul_le_mul_left (2 ^ 20) (Nat.le_trans (hStepUp 61)
        (Nat.mul_le_mul_left (2 ^ 20) (Nat.le_trans (hStepUp 60) (Nat.mul_le_mul_left (2 ^ 20) hUp60)))))))
    rw [p8 60, ← Nat.mul_assoc (2 ^ 20), ← Nat.pow_add 2 20 20, ← Nat.mul_assoc (2 ^ 40),
        ← Nat.pow_add 2 40 20, ← Nat.mul_assoc (2 ^ 60), ← Nat.pow_add 2 60 20, ← Nat.mul_assoc (2 ^ 80)] at p
    exact p
  have sL2 := bStep (888 * 512) 1; rw [bOne] at sL2
  change 2 * B (888 * 512) 2 = (888 * 512 - 1) * (888 * 512) at sL2
  have hLo : 2 ^ 35 ≤ B (888 * 512) 2 := by
    have a : 2 ^ 18 ≤ 888 * 512 - 1 := by
      have h888 : 888 * 512 = 887 * 512 + 512 := by rw [show (888 : Nat) = 887 + 1 from rfl, Nat.add_mul, Nat.one_mul]
      have sub1 : 887 * 512 ≤ 888 * 512 - 1 := by rw [h888]; exact add_sub_ge_gen (887 * 512) 512 1 (by decide)
      have m := Nat.mul_le_mul (by decide : 2 ^ 9 ≤ 887) (by decide : 2 ^ 9 ≤ 512)
      rw [← Nat.pow_add] at m; exact Nat.le_trans m sub1
    have b : 2 * 2 ^ 17 ≤ 888 * 512 := by
      have m := Nat.mul_le_mul (by decide : 2 * 2 ^ 8 ≤ 888) (by decide : 2 ^ 9 ≤ 512)
      rw [Nat.mul_assoc 2, ← Nat.pow_add] at m; exact m
    have prod := Nat.mul_le_mul a b
    have e : 2 ^ 18 * (2 * 2 ^ 17) = 2 * 2 ^ 35 := by rw [Nat.mul_left_comm (2 ^ 18) 2 (2 ^ 17), ← Nat.pow_add]
    rw [e, ← sL2] at prod; exact Nat.le_of_mul_le_mul_left prod (by decide)
  have hHi : B (888 * 512) 2 < 2 ^ 37 := by
    have a : 888 * 512 - 1 < 2 ^ 19 := Nat.lt_of_le_of_lt (Nat.sub_le _ 1)
      (by rw [show (2 : Nat) ^ 19 = 2 ^ 10 * 2 ^ 9 from by rw [← Nat.pow_add], show 2 ^ 9 = 512 from by decide]
          exact Nat.mul_lt_mul_of_pos_right (by decide : 888 < 2 ^ 10) (by decide))
    have b : 888 * 512 ≤ 2 * 2 ^ 18 := by
      have m := Nat.mul_le_mul (by decide : 888 ≤ 2 * 2 ^ 9) (by decide : 512 ≤ 2 ^ 9)
      rw [Nat.mul_assoc 2, ← Nat.pow_add] at m; exact m
    have prod := Nat.mul_lt_mul_of_lt_of_le a b (by decide)
    have e : 2 ^ 19 * (2 * 2 ^ 18) = 2 * 2 ^ 37 := by rw [Nat.mul_left_comm (2 ^ 19) 2 (2 ^ 18), ← Nat.pow_add]
    rw [e, ← sL2] at prod; exact nat_lt_of_mul_lt_left prod
  have hR0 : pcgDenseRows ^ 2 < 2 ^ 36 := by
    have r : pcgDenseRows < 2 ^ 18 := by
      unfold pcgDenseRows; rw [show (2 : Nat) ^ 18 = 2 ^ 8 * 2 ^ 10 from by rw [← Nat.pow_add], show 2 ^ 10 = 1024 from by decide]
      exact Nat.mul_lt_mul_of_pos_right (by decide : 136 < 2 ^ 8) (by decide)
    rw [Nat.pow_two, show (2 : Nat) ^ 36 = 2 ^ 18 * 2 ^ 18 from by rw [← Nat.pow_add]]
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.le_of_lt r)) (Nat.mul_lt_mul_of_pos_left r (Nat.two_pow_pos 18))
  have hSum39 : 2 ^ 36 + 2 * 2 ^ 37 + 2 ^ 36 ≤ 2 ^ 39 := by
    have h8 : ∀ u : Nat, u + 2 * (2 * u) + u ≤ 8 * u := fun _ => by omega
    rw [show (2 : Nat) ^ 37 = 2 * 2 ^ 36 from by rw [Nat.pow_succ'], show (2 : Nat) ^ 39 = 8 * 2 ^ 36 from by rw [show (8 : Nat) = 2 ^ 3 from rfl, ← Nat.pow_add]]
    exact h8 (2 ^ 36)
  have hBounds := l2_cost_and_sq (B (888 * 512) 2) pcgDenseRows (2 ^ 35) (2 ^ 36) (2 ^ 37)
    (2 ^ 22) (2 ^ 52) (2 ^ 70) (2 ^ 74) (2 ^ 39) (Nat.two_pow_pos 35) (Nat.two_pow_pos 37)
    hR0 hLo hHi (by rw [← Nat.pow_add]) (by rw [← Nat.pow_add]) (by rw [← Nat.pow_add])
    (Nat.pow_le_pow_right (by decide) (by decide)) hSum39
  have hPow : 2 ^ 39 * 2 ^ 80 * 2 ^ 180 ≤ 2 ^ 256 * 2 ^ 70 := by
    rw [← Nat.pow_add 2 39 80, show (180 : Nat) = 110 + 70 from rfl, Nat.pow_add 2 110 70,
        ← Nat.mul_assoc (2 ^ 119) (2 ^ 110) (2 ^ 70), ← Nat.pow_add 2 119 110]
    exact Nat.mul_le_mul_right (2 ^ 70) (Nat.pow_le_pow_right (by decide) (by decide))
  exact contra_isd_bound _ (B (888 * 512) 2) (B pcgDepth14Cols 64) (B (pcgDenseRows - 52) 60)
    (2 ^ 39) (2 ^ 80) (2 ^ 180) (2 ^ 256) (2 ^ 70) hPos60
    (Nat.mul_pos (Nat.two_pow_pos 80) (Nat.two_pow_pos 180)) hUp64 hBounds.1 hBounds.2 hPow hBad


end Qsag
end
