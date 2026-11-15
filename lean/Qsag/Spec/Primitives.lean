module
/-
# Qsag.Spec.Primitives — Canonical Byte, Digest, Rational, and Framing Primitives

Layer-0 specification primitives unifying byte/digest carriers, exact non-negative rational bounds,
and prefix-free serialization codecs across the verification hierarchy.

In particular, `Qsag.Spec.RatBound` provides a single canonical rational upper-bound carrier with
proved lossless, order-preserving conversions to and from all three rational representations used
in existing subsystem proofs:
1. `Qsag.RatBound` (`ConcreteSecurityBudget`),
2. `Qsag.ratLe` over `Nat × Nat` (`UcGames`), and
3. `Qsag.ExactRat` (`GaussianHvzkAndDualLpn`).
-/

public import Qsag.Digest256
public import Qsag.UcGames
public import Qsag.ConcreteSecurityBudget
public import Qsag.GaussianHvzkAndDualLpn
public import Qsag.SimulationSpine
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Spec

set_option autoImplicit false

/-! ## 1. Canonical Byte and 256-Bit Digest Carriers -/

/-- Canonical variable-length byte sequence. -/
abbrev Bytes : Type := List UInt8

/-- Canonical fixed-width 32-byte digest or seed slice. -/
abbrev Bytes32 : Type := { bs : List UInt8 // bs.length = 32 }

/-- Canonical 256-bit digest carrier (`BitVec 256`). -/
abbrev Digest256 : Type := Qsag.Digest256

/-- Exact finite sum `∑_{i < n} f i` re-exported at Layer 0. -/
abbrev finSum (n : Nat) (f : Fin n → Nat) : Nat := Qsag.finSum n f

/-- Constructive absolute difference `|a - b|` over `Nat`. -/
@[expose] def natAbsDiff (a b : Nat) : Nat :=
  if a ≤ b then b - a else a - b

theorem natAbsDiff_comm (a b : Nat) : natAbsDiff a b = natAbsDiff b a := by
  unfold natAbsDiff
  by_cases hab : a ≤ b <;> by_cases hba : b ≤ a <;>
    simp only [hab, hba, ↓reduceIte] <;> omega

theorem natAbsDiff_triangle (a b c : Nat) :
    natAbsDiff a c ≤ natAbsDiff a b + natAbsDiff b c := by
  unfold natAbsDiff
  by_cases hac : a ≤ c <;> by_cases hab : a ≤ b <;> by_cases hbc : b ≤ c <;>
    simp only [hac, hab, hbc, ↓reduceIte] <;> omega

/-! ## 2. Unified Canonical Rational Bound (`Spec.RatBound`) -/

/-- Exact non-negative rational bound `num / den` with certified positive denominator (`0 < den`). -/
structure RatBound where
  num : Nat
  den : Nat
  den_pos : 0 < den
  deriving DecidableEq, Repr

@[ext] theorem RatBound.ext {a b : RatBound} (hn : a.num = b.num) (hd : a.den = b.den) :
    a = b := by
  cases a; cases b; cases hn; cases hd; rfl

@[expose] def RatBound.zero : RatBound := ⟨0, 1, Nat.one_pos⟩

@[expose] def RatBound.one : RatBound := ⟨1, 1, Nat.one_pos⟩

/-- Exact dyadic reciprocal `2^{-b}`. -/
@[expose] def RatBound.invPow2 (b : Nat) : RatBound :=
  ⟨1, 2 ^ b, Nat.two_pow_pos b⟩

/-- Exact cross-multiplied rational equality `a.num / a.den = b.num / b.den`. -/
@[expose] def RatBound.eqv (a b : RatBound) : Prop :=
  a.num * b.den = b.num * a.den

/-- Exact cross-multiplied rational inequality `a.num / a.den ≤ b.num / b.den`. -/
@[expose] def RatBound.le (a b : RatBound) : Prop :=
  a.num * b.den ≤ b.num * a.den

/-- Exact strict rational inequality `a.num / a.den < b.num / b.den`. -/
@[expose] def RatBound.lt (a b : RatBound) : Prop :=
  a.num * b.den < b.num * a.den

instance RatBound.instDecidableEqv (a b : RatBound) : Decidable (RatBound.eqv a b) :=
  Nat.decEq (a.num * b.den) (b.num * a.den)

instance RatBound.instDecidableLe (a b : RatBound) : Decidable (RatBound.le a b) :=
  Nat.decLe (a.num * b.den) (b.num * a.den)

instance RatBound.instDecidableLt (a b : RatBound) : Decidable (RatBound.lt a b) :=
  Nat.decLt (a.num * b.den) (b.num * a.den)

/-- Constructive `b`-bit security predicate: `r ≤ 2^{-b}` (`r.num * 2^b ≤ r.den`). -/
@[expose] def RatBound.atLeastBits (b : Nat) (r : RatBound) : Prop :=
  r.num * 2 ^ b ≤ r.den

/-- Strict `b`-bit margin predicate: `r < 2^{-b}` (`r.num * 2^b < r.den`). -/
@[expose] def RatBound.strictlyMoreThanBits (b : Nat) (r : RatBound) : Prop :=
  r.num * 2 ^ b < r.den

/-- Negative bit-budget predicate: `r > 2^{-b}` (`r.den < r.num * 2^b`). -/
@[expose] def RatBound.exceedsBitBudget (b : Nat) (r : RatBound) : Prop :=
  r.den < r.num * 2 ^ b

/-- Exact rational sum `(a.num * b.den + b.num * a.den) / (a.den * b.den)`. -/
@[expose] def RatBound.add (a b : RatBound) : RatBound :=
  ⟨a.num * b.den + b.num * a.den, a.den * b.den, Nat.mul_pos a.den_pos b.den_pos⟩

/-- Exact rational product `(a.num * b.num) / (a.den * b.den)`. -/
def RatBound.mul (a b : RatBound) : RatBound :=
  ⟨a.num * b.num, a.den * b.den, Nat.mul_pos a.den_pos b.den_pos⟩

/-- Non-negative integer scaling `(k * r.num) / r.den`. -/
@[expose] def RatBound.scale (k : Nat) (r : RatBound) : RatBound :=
  ⟨k * r.num, r.den, r.den_pos⟩

/-- Natural-number exponentiation `r ^ n`. -/
def RatBound.pow (r : RatBound) : Nat → RatBound
  | 0 => RatBound.one
  | n + 1 => r.mul (r.pow n)

/-- Constructive right-cancellation for `Nat` multiplication inequality (`0 Classical.choice`). -/
theorem nat_le_of_mul_le_mul_right {a b k : Nat} (h : a * k ≤ b * k) (hk : 0 < k) : a ≤ b :=
  match Nat.lt_or_ge b a with
  | .inr hge => hge
  | .inl hlt => by
    have h1 : (b + 1) * k ≤ a * k := Nat.mul_le_mul_right k hlt
    rw [Nat.succ_mul] at h1
    omega

/-- Constructive strict right-cancellation for `Nat` multiplication (`0 Classical.choice`). -/
theorem nat_lt_of_mul_lt_mul_right {a b k : Nat} (h : a * k < b * k) : a < b :=
  match Nat.lt_or_ge a b with
  | .inl hlt => hlt
  | .inr hge => False.elim (Nat.not_lt_of_ge (Nat.mul_le_mul_right k hge) h)

/-- Constructive strict right-scaling for `Nat` multiplication (`0 Classical.choice`). -/
theorem nat_mul_lt_mul_of_pos_right {a b k : Nat} (h : a < b) (hk : 0 < k) : a * k < b * k := by
  have h1 : (a + 1) * k ≤ b * k := Nat.mul_le_mul_right k h
  rw [Nat.succ_mul] at h1
  omega

theorem RatBound.le_refl (a : RatBound) : a.le a :=
  Nat.le_refl _

theorem RatBound.le_trans {a b c : RatBound} (hab : a.le b) (hbc : b.le c) : a.le c := by
  unfold RatBound.le at *
  have h1 : a.num * b.den * c.den ≤ b.num * a.den * c.den :=
    Nat.mul_le_mul_right c.den hab
  have h2 : b.num * c.den * a.den ≤ c.num * b.den * a.den :=
    Nat.mul_le_mul_right a.den hbc
  have hMid : b.num * a.den * c.den = b.num * c.den * a.den := by
    rw [Nat.mul_assoc, Nat.mul_comm a.den c.den, ← Nat.mul_assoc]
  have hChain : a.num * c.den * b.den ≤ c.num * a.den * b.den := by
    have hL : a.num * c.den * b.den = a.num * b.den * c.den := by
      rw [Nat.mul_assoc, Nat.mul_comm c.den b.den, ← Nat.mul_assoc]
    have hR : c.num * a.den * b.den = c.num * b.den * a.den := by
      rw [Nat.mul_assoc, Nat.mul_comm a.den b.den, ← Nat.mul_assoc]
    rw [hL, hR]
    exact Nat.le_trans h1 (hMid ▸ h2)
  exact nat_le_of_mul_le_mul_right hChain b.den_pos

theorem RatBound.le_of_lt {a b : RatBound} (h : a.lt b) : a.le b :=
  Nat.le_of_lt h

theorem RatBound.lt_of_le_of_lt {a b c : RatBound} (hab : a.le b) (hbc : b.lt c) : a.lt c := by
  unfold RatBound.le RatBound.lt at *
  have h1 : a.num * b.den * c.den ≤ b.num * a.den * c.den :=
    Nat.mul_le_mul_right c.den hab
  have h2 : b.num * c.den * a.den < c.num * b.den * a.den :=
    nat_mul_lt_mul_of_pos_right hbc a.den_pos
  have hMid : b.num * a.den * c.den = b.num * c.den * a.den := by
    rw [Nat.mul_assoc, Nat.mul_comm a.den c.den, ← Nat.mul_assoc]
  have hChain : a.num * c.den * b.den < c.num * a.den * b.den := by
    have hL : a.num * c.den * b.den = a.num * b.den * c.den := by
      rw [Nat.mul_assoc, Nat.mul_comm c.den b.den, ← Nat.mul_assoc]
    have hR : c.num * a.den * b.den = c.num * b.den * a.den := by
      rw [Nat.mul_assoc, Nat.mul_comm a.den b.den, ← Nat.mul_assoc]
    rw [hL, hR]
    exact Nat.lt_of_le_of_lt h1 (hMid ▸ h2)
  exact nat_lt_of_mul_lt_mul_right hChain

theorem RatBound.add_le_add {a₁ a₂ b₁ b₂ : RatBound}
    (ha : a₁.le a₂) (hb : b₁.le b₂) : (a₁.add b₁).le (a₂.add b₂) := by
  unfold RatBound.le RatBound.add at *
  dsimp only
  have h1 : a₁.num * b₁.den * (a₂.den * b₂.den) ≤ a₂.num * b₂.den * (a₁.den * b₁.den) := by
    have hL : a₁.num * b₁.den * (a₂.den * b₂.den) = (a₁.num * a₂.den) * (b₁.den * b₂.den) := by
      simp only [Nat.mul_left_comm, Nat.mul_comm]
    have hR : a₂.num * b₂.den * (a₁.den * b₁.den) = (a₂.num * a₁.den) * (b₁.den * b₂.den) := by
      simp only [Nat.mul_left_comm, Nat.mul_comm]
    rw [hL, hR]
    exact Nat.mul_le_mul_right _ ha
  have h2 : b₁.num * a₁.den * (a₂.den * b₂.den) ≤ b₂.num * a₂.den * (a₁.den * b₁.den) := by
    have hL : b₁.num * a₁.den * (a₂.den * b₂.den) = (b₁.num * b₂.den) * (a₁.den * a₂.den) := by
      simp only [Nat.mul_left_comm, Nat.mul_comm]
    have hR : b₂.num * a₂.den * (a₁.den * b₁.den) = (b₂.num * b₁.den) * (a₁.den * a₂.den) := by
      simp only [Nat.mul_left_comm, Nat.mul_comm]
    rw [hL, hR]
    exact Nat.mul_le_mul_right _ hb
  rw [Nat.right_distrib, Nat.right_distrib]
  exact Nat.add_le_add h1 h2

theorem RatBound.mul_le_mul {a₁ a₂ b₁ b₂ : RatBound}
    (ha : a₁.le a₂) (hb : b₁.le b₂) : (a₁.mul b₁).le (a₂.mul b₂) := by
  unfold RatBound.le RatBound.mul at *
  dsimp only
  have hL : a₁.num * b₁.num * (a₂.den * b₂.den) = (a₁.num * a₂.den) * (b₁.num * b₂.den) := by
    simp only [Nat.mul_left_comm, Nat.mul_comm]
  have hR : a₂.num * b₂.num * (a₁.den * b₁.den) = (a₂.num * a₁.den) * (b₂.num * b₁.den) := by
    simp only [Nat.mul_left_comm, Nat.mul_comm]
  rw [hL, hR]
  exact Nat.mul_le_mul ha hb

theorem RatBound.scale_le_scale (k : Nat) {a b : RatBound} (h : a.le b) :
    (a.scale k).le (b.scale k) := by
  unfold RatBound.le RatBound.scale at *
  dsimp only
  rw [Nat.mul_assoc, Nat.mul_assoc]
  exact Nat.mul_le_mul_left k h

theorem RatBound.atLeastBits_iff_le_invPow2 (b : Nat) (r : RatBound) :
    r.atLeastBits b ↔ r.le (RatBound.invPow2 b) := by
  unfold RatBound.atLeastBits RatBound.le RatBound.invPow2
  dsimp only
  rw [Nat.one_mul]

theorem RatBound.atLeastBits_of_le {b : Nat} {r₁ r₂ : RatBound}
    (hle : r₁.le r₂) (hBits : r₂.atLeastBits b) : r₁.atLeastBits b :=
  (RatBound.atLeastBits_iff_le_invPow2 b r₁).mpr
    (RatBound.le_trans hle ((RatBound.atLeastBits_iff_le_invPow2 b r₂).mp hBits))

/-! ## 3. Lossless Deduplication Bridges to Existing Rational Models -/

/-- Lossless conversion to `ConcreteSecurityBudget.RatBound` (`Qsag.RatBound`). -/
def RatBound.toBudget (r : RatBound) : Qsag.RatBound :=
  ⟨r.num, r.den, r.den_pos⟩

/-- Lossless conversion from `ConcreteSecurityBudget.RatBound` (`Qsag.RatBound`). -/
def RatBound.ofBudget (r : Qsag.RatBound) : RatBound :=
  ⟨r.num, r.den, r.h_pos⟩

theorem RatBound.ofBudget_toBudget (r : RatBound) :
    RatBound.ofBudget r.toBudget = r := by
  cases r; rfl

theorem RatBound.toBudget_ofBudget (r : Qsag.RatBound) :
    (RatBound.ofBudget r).toBudget = r := by
  cases r; rfl

theorem RatBound.le_iff_budget_le (r₁ r₂ : RatBound) :
    r₁.le r₂ ↔ Qsag.RatBound.le r₁.toBudget r₂.toBudget := Iff.rfl

theorem RatBound.ofBudget_le_iff (r₁ r₂ : Qsag.RatBound) :
    (RatBound.ofBudget r₁).le (RatBound.ofBudget r₂) ↔ Qsag.RatBound.le r₁ r₂ := Iff.rfl

theorem RatBound.lt_iff_budget_lt (r₁ r₂ : RatBound) :
    r₁.lt r₂ ↔ Qsag.RatBound.lt r₁.toBudget r₂.toBudget := Iff.rfl

theorem RatBound.ofBudget_lt_iff (r₁ r₂ : Qsag.RatBound) :
    (RatBound.ofBudget r₁).lt (RatBound.ofBudget r₂) ↔ Qsag.RatBound.lt r₁ r₂ := Iff.rfl

theorem RatBound.atLeastBits_iff_budget (b : Nat) (r : RatBound) :
    r.atLeastBits b ↔ Qsag.atLeastBits b r.toBudget := Iff.rfl

theorem RatBound.ofBudget_atLeastBits_iff (b : Nat) (r : Qsag.RatBound) :
    (RatBound.ofBudget r).atLeastBits b ↔ Qsag.atLeastBits b r := Iff.rfl

theorem RatBound.strictlyMoreThanBits_iff_budget (b : Nat) (r : RatBound) :
    r.strictlyMoreThanBits b ↔ Qsag.strictlyMoreThanBits b r.toBudget := Iff.rfl

theorem RatBound.ofBudget_strictlyMoreThanBits_iff (b : Nat) (r : Qsag.RatBound) :
    (RatBound.ofBudget r).strictlyMoreThanBits b ↔ Qsag.strictlyMoreThanBits b r := Iff.rfl

theorem RatBound.exceedsBitBudget_iff_budget (b : Nat) (r : RatBound) :
    r.exceedsBitBudget b ↔ Qsag.exceedsBitBudget b r.toBudget := Iff.rfl

theorem RatBound.ofBudget_exceedsBitBudget_iff (b : Nat) (r : Qsag.RatBound) :
    (RatBound.ofBudget r).exceedsBitBudget b ↔ Qsag.exceedsBitBudget b r := Iff.rfl

/-- Lossless pair projection to `UcGames` `(num, den)` carrier. -/
def RatBound.toUcPair (r : RatBound) : Nat × Nat :=
  (r.num, r.den)

/-- Lift a certified positive-denominator `UcGames` pair `(num, den)` into `Spec.RatBound`. -/
def RatBound.ofUcPair (p : Nat × Nat) (hp : 0 < p.2) : RatBound :=
  ⟨p.1, p.2, hp⟩

/-- Equivalence between `Spec.RatBound.le` and `UcGames.ratLe`. -/
theorem RatBound.le_iff_ucRatLe (r₁ r₂ : RatBound) :
    r₁.le r₂ ↔ Qsag.ratLe r₁.toUcPair r₂.toUcPair := by
  unfold RatBound.le Qsag.ratLe RatBound.toUcPair
  dsimp only
  exact ⟨fun h => ⟨r₁.den_pos, r₂.den_pos, h⟩, fun ⟨_, _, h⟩ => h⟩

theorem RatBound.ucRatLe_iff_ofUcPair_le {p₁ p₂ : Nat × Nat}
    (hp₁ : 0 < p₁.2) (hp₂ : 0 < p₂.2) :
    Qsag.ratLe p₁ p₂ ↔ (RatBound.ofUcPair p₁ hp₁).le (RatBound.ofUcPair p₂ hp₂) := by
  unfold Qsag.ratLe RatBound.le RatBound.ofUcPair
  dsimp only
  exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨hp₁, hp₂, h⟩⟩

/-- Order-preserving embedding into signed `Qsag.ExactRat` (`GaussianHvzkAndDualLpn`). -/
def RatBound.toExactRat (r : RatBound) : Qsag.ExactRat :=
  ⟨(r.num : Int), r.den, r.den_pos⟩

/-- Magnitude projection from signed `Qsag.ExactRat` (`|x.num| / x.den`) into `Spec.RatBound`. -/
def RatBound.ofExactRatAbs (x : Qsag.ExactRat) : RatBound :=
  ⟨x.num.natAbs, x.den, x.den_pos⟩

theorem RatBound.toExactRat_nonneg (r : RatBound) :
    0 ≤ (r.toExactRat).num :=
  Int.natCast_nonneg r.num

theorem RatBound.ofExactRatAbs_toExactRat (r : RatBound) :
    RatBound.ofExactRatAbs r.toExactRat = r := by
  cases r with
  | mk num den hpos =>
    unfold RatBound.ofExactRatAbs RatBound.toExactRat
    dsimp only
    rw [Int.natAbs_natCast]

theorem RatBound.toExactRat_ofNonneg {x : Qsag.ExactRat} (hx : 0 ≤ x.num) :
    (RatBound.ofExactRatAbs x).toExactRat = x := by
  cases x with
  | mk num den hpos =>
    dsimp only at hx
    unfold RatBound.ofExactRatAbs RatBound.toExactRat
    dsimp only
    exact congrArg (fun n => Qsag.ExactRat.mk n den hpos) (Int.natAbs_of_nonneg hx)

theorem RatBound.le_iff_toExactRat_le (r₁ r₂ : RatBound) :
    r₁.le r₂ ↔ Qsag.ExactRat.le r₁.toExactRat r₂.toExactRat := by
  unfold RatBound.le Qsag.ExactRat.le RatBound.toExactRat
  dsimp only
  rw [← Int.natCast_mul, ← Int.natCast_mul]
  exact Int.ofNat_le.symm

theorem RatBound.lt_iff_toExactRat_lt (r₁ r₂ : RatBound) :
    r₁.lt r₂ ↔ Qsag.ExactRat.lt r₁.toExactRat r₂.toExactRat := by
  unfold RatBound.lt Qsag.ExactRat.lt RatBound.toExactRat
  dsimp only
  rw [← Int.natCast_mul, ← Int.natCast_mul]
  exact Int.ofNat_lt.symm

theorem RatBound.exactRat_nonneg_le_iff {x y : Qsag.ExactRat}
    (hx : 0 ≤ x.num) (hy : 0 ≤ y.num) :
    (RatBound.ofExactRatAbs x).le (RatBound.ofExactRatAbs y) ↔
      Qsag.ExactRat.le x y := by
  rw [RatBound.le_iff_toExactRat_le, RatBound.toExactRat_ofNonneg hx,
      RatBound.toExactRat_ofNonneg hy]

/-- Non-negative clamping projection `max(0, x.num) / x.den` from `Qsag.ExactRat` into `Spec.RatBound`. -/
def RatBound.clampExactRat (x : Qsag.ExactRat) : RatBound :=
  ⟨x.num.toNat, x.den, x.den_pos⟩

/-- Any `Qsag.ExactRat` bounded by `ExactRat.twoNegPow b` maps under `clampExactRat` to `atLeastBits b`. -/
theorem RatBound.clampExactRat_atLeastBits_of_le_twoNegPow {x : Qsag.ExactRat} {b : Nat}
    (hLe : Qsag.ExactRat.le x (Qsag.ExactRat.twoNegPow b)) :
    (RatBound.clampExactRat x).atLeastBits b := by
  unfold Qsag.ExactRat.le Qsag.ExactRat.twoNegPow at hLe
  dsimp only at hLe
  unfold RatBound.atLeastBits RatBound.clampExactRat
  dsimp only
  by_cases hx : 0 ≤ x.num
  · have hEq : ((x.num.toNat : Nat) : Int) = x.num := Int.toNat_of_nonneg hx
    apply Int.ofNat_le.mp
    rw [Int.natCast_mul, hEq]
    omega
  · have hZero : x.num.toNat = 0 := Int.toNat_of_nonpos (by omega)
    rw [hZero, Nat.zero_mul]
    exact Nat.zero_le _

theorem RatBound.clampExactRat_strictlyMoreThanBits_of_lt_twoNegPow {x : Qsag.ExactRat} {b : Nat}
    (hLt : Qsag.ExactRat.lt x (Qsag.ExactRat.twoNegPow b)) :
    (RatBound.clampExactRat x).strictlyMoreThanBits b := by
  unfold Qsag.ExactRat.lt Qsag.ExactRat.twoNegPow at hLt
  dsimp only at hLt
  unfold RatBound.strictlyMoreThanBits RatBound.clampExactRat
  dsimp only
  have hPowPos : (0 : Int) < ((2 ^ b : Nat) : Int) := Int.ofNat_lt.mpr (Nat.two_pow_pos b)
  by_cases hx : 0 ≤ x.num
  · have hEq : ((x.num.toNat : Nat) : Int) = x.num := Int.toNat_of_nonneg hx
    apply Int.ofNat_lt.mp
    rw [Int.natCast_mul, hEq]
    omega
  · have hZero : x.num.toNat = 0 := Int.toNat_of_nonpos (by omega)
    rw [hZero, Nat.zero_mul]
    exact x.den_pos

/-! ## 4. Canonical Fixed-Width and Prefix-Free Framed Codecs -/

/-- Canonical fixed-width byte codec (`encode` emits `width` bytes and `decode` round-trips). -/
abbrev FixedCodec (α : Type) (width : Nat) : Type := Qsag.FixedCodec α width

/-- Canonical variable-length prefix-free framed codec (`decodePrefix` recovers `(x, rest)`
    for any arbitrary trailing byte stream `rest`). -/
structure FramedCodec (α : Type) where
  encode : α → Bytes
  decodePrefix : Bytes → Option (α × Bytes)
  decodePrefix_append : ∀ (x : α) (rest : Bytes),
    decodePrefix (encode x ++ rest) = some (x, rest)

/-- Every `FramedCodec` is strictly prefix-free injective under arbitrary suffix concatenation. -/
theorem FramedCodec.prefix_injective {α : Type} (c : FramedCodec α)
    {x y : α} {rest₁ rest₂ : Bytes} :
    c.encode x ++ rest₁ = c.encode y ++ rest₂ ↔ x = y ∧ rest₁ = rest₂ := by
  constructor
  · intro hEq
    have hDec := congrArg c.decodePrefix hEq
    rw [c.decodePrefix_append x rest₁, c.decodePrefix_append y rest₂] at hDec
    injection hDec with hPair
    injection hPair with hx hr
    exact ⟨hx, hr⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem FramedCodec.encode_injective {α : Type} (c : FramedCodec α)
    {x y : α} (h : c.encode x = c.encode y) : x = y := by
  have hApp : c.encode x ++ [] = c.encode y ++ [] := by simpa using h
  exact ((c.prefix_injective).mp hApp).1

/-- Every `FixedCodec α width` canonically induces a prefix-free `FramedCodec α`. -/
def FramedCodec.ofFixed {α : Type} {width : Nat} (c : FixedCodec α width) : FramedCodec α where
  encode := c.encode
  decodePrefix := c.decodePrefix
  decodePrefix_append := c.decodePrefix_append

/-- Sequential pair combinator for `FramedCodec`. -/
def FramedCodec.pair {α β : Type} (c₁ : FramedCodec α) (c₂ : FramedCodec β) :
    FramedCodec (α × β) where
  encode p := c₁.encode p.1 ++ c₂.encode p.2
  decodePrefix buf :=
    match c₁.decodePrefix buf with
    | none => none
    | some (a, rem₁) =>
      match c₂.decodePrefix rem₁ with
      | none => none
      | some (b, rem₂) => some ((a, b), rem₂)
  decodePrefix_append p rest := by
    rcases p with ⟨a, b⟩
    rw [List.append_assoc, c₁.decodePrefix_append a (c₂.encode b ++ rest)]
    dsimp only
    rw [c₂.decodePrefix_append b rest]

private def parseUnframedBounded (res : Option (List UInt8 × List UInt8)) :
    Option ({ bs : Bytes // bs.length < 2 ^ 32 } × Bytes) :=
  match res with
  | none => none
  | some (bs, rest) =>
    if h : bs.length < 2 ^ 32 then some (⟨bs, h⟩, rest) else none

private theorem parseUnframedBounded_on_some (s : { bs : Bytes // bs.length < 2 ^ 32 })
    (rest : Bytes) {res : Option (List UInt8 × List UInt8)}
    (hRes : res = some (s.val, rest)) :
    parseUnframedBounded res = some (s, rest) := by
  subst hRes
  unfold parseUnframedBounded
  dsimp only
  simp only [s.property, ↓reduceDIte]

/-- Length-bounded byte slice (`< 2^32` bytes) framed with 4-byte big-endian length prefix. -/
def FramedCodec.boundedBytes : FramedCodec { bs : Bytes // bs.length < 2 ^ 32 } where
  encode s := Qsag.frameBytes s.val
  decodePrefix buf := parseUnframedBounded (Qsag.unframeBytes buf)
  decodePrefix_append s rest :=
    parseUnframedBounded_on_some s rest
      (Qsag.FramedBytesCodec.unframe_frame_append s.property rest)

/-- Single-byte domain separation tag prepended to framed payloads. -/
structure DomainTag where
  tagByte : UInt8
  deriving DecidableEq, Repr

/-- Prepend a 1-byte domain separator to a payload. -/
def DomainTag.apply (t : DomainTag) (payload : Bytes) : Bytes :=
  t.tagByte :: payload

/-- Distinct domain tags produce disjoint byte encodings for all payloads. -/
theorem DomainTag.disjoint {t₁ t₂ : DomainTag} (hNe : t₁ ≠ t₂) (p₁ p₂ : Bytes) :
    t₁.apply p₁ ≠ t₂.apply p₂ := by
  intro hEq
  unfold DomainTag.apply at hEq
  injection hEq with hTag _
  apply hNe
  cases t₁; cases t₂
  cases hTag
  rfl

#verify_constructive
  Qsag.Spec.natAbsDiff_comm
  Qsag.Spec.natAbsDiff_triangle
  Qsag.Spec.RatBound.le_refl
  Qsag.Spec.RatBound.le_trans
  Qsag.Spec.RatBound.lt_of_le_of_lt
  Qsag.Spec.RatBound.add_le_add
  Qsag.Spec.RatBound.mul_le_mul
  Qsag.Spec.RatBound.scale_le_scale
  Qsag.Spec.RatBound.atLeastBits_iff_le_invPow2
  Qsag.Spec.RatBound.atLeastBits_of_le
  Qsag.Spec.RatBound.ofBudget_toBudget
  Qsag.Spec.RatBound.toBudget_ofBudget
  Qsag.Spec.RatBound.le_iff_ucRatLe
  Qsag.Spec.RatBound.ucRatLe_iff_ofUcPair_le
  Qsag.Spec.RatBound.ofExactRatAbs_toExactRat
  Qsag.Spec.RatBound.toExactRat_ofNonneg
  Qsag.Spec.RatBound.le_iff_toExactRat_le
  Qsag.Spec.RatBound.lt_iff_toExactRat_lt
  Qsag.Spec.RatBound.exactRat_nonneg_le_iff
  Qsag.Spec.RatBound.clampExactRat_atLeastBits_of_le_twoNegPow
  Qsag.Spec.RatBound.clampExactRat_strictlyMoreThanBits_of_lt_twoNegPow
  Qsag.Spec.FramedCodec.prefix_injective
  Qsag.Spec.FramedCodec.encode_injective
  Qsag.Spec.DomainTag.disjoint

end Qsag.Spec
end
