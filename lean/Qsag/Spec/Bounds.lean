module
public import Qsag.Tactic.Prelude

public section
namespace Qsag
set_option autoImplicit false
set_option exponentiation.threshold 2048
/-! ## §1. Exact Constructive `RatBound`, Log2 Bit-Margin Predicates & Union Calculus -/

/-- Non-negative rational probability / advantage upper bound `num / den` with certified positive
    denominator (`0 < den`), eliminating division-by-zero vacuity and floating-point rounding. -/
structure RatBound where
  num : Nat
  den : Nat
  h_pos : 0 < den
  deriving DecidableEq, Repr

@[ext] theorem RatBound.ext {a b : RatBound} (hn : a.num = b.num) (hd : a.den = b.den) : a = b := by
  cases a; cases b; cases hn; cases hd; rfl

/-- Exact cross-multiplied rational inequality `a.num / a.den ≤ b.num / b.den`. -/
@[expose] def RatBound.le (a b : RatBound) : Prop :=
  a.num * b.den ≤ b.num * a.den

/-- Strict cross-multiplied rational inequality `a.num / a.den < b.num / b.den`. -/
@[expose] def RatBound.lt (a b : RatBound) : Prop :=
  a.num * b.den < b.num * a.den

/-- Constructive `b`-bit concrete security predicate: `bound ≤ 2^{-b}`, expressed as the exact
    integer inequality `bound.num * 2 ^ b ≤ bound.den`. -/
@[expose] def atLeastBits (b : Nat) (bound : RatBound) : Prop :=
  bound.num * 2 ^ b ≤ bound.den

/-- Strict `b`-bit margin predicate: `bound < 2^{-b}` (`bound.num * 2 ^ b < bound.den`). -/
@[expose] def strictlyMoreThanBits (b : Nat) (bound : RatBound) : Prop :=
  bound.num * 2 ^ b < bound.den

/-- Negative concrete security witness predicate: `bound > 2^{-b}` (`bound.den < bound.num * 2 ^ b`),
    certifying that a bound fails to meet a `b`-bit budget (at `b = 0`, `bound > 1`). -/
@[expose] def exceedsBitBudget (b : Nat) (bound : RatBound) : Prop :=
  bound.den < bound.num * 2 ^ b

/- These two instances are named: the generated names `instDecidableLe` / `instDecidableLt` are
   also generated for `ExactRat` in `GaussianHvzkAndDualLpn.lean`, and the library root imports both. -/
instance RatBound.decidableLe (a b : RatBound) : Decidable (RatBound.le a b) :=
  Nat.decLe (a.num * b.den) (b.num * a.den)

instance RatBound.decidableLt (a b : RatBound) : Decidable (RatBound.lt a b) :=
  Nat.decLt (a.num * b.den) (b.num * a.den)

instance (b : Nat) (bound : RatBound) : Decidable (atLeastBits b bound) :=
  Nat.decLe (bound.num * 2 ^ b) bound.den

instance (b : Nat) (bound : RatBound) : Decidable (strictlyMoreThanBits b bound) :=
  Nat.decLt (bound.num * 2 ^ b) bound.den

instance (b : Nat) (bound : RatBound) : Decidable (exceedsBitBudget b bound) :=
  Nat.decLt bound.den (bound.num * 2 ^ b)

/-- Exact zero error bound `0 / 1`. -/
@[expose] def RatBound.zero : RatBound := ⟨0, 1, Nat.zero_lt_one⟩

/-- Unit probability bound `1 / 1`. -/
def RatBound.one : RatBound := ⟨1, 1, Nat.zero_lt_one⟩

/-- Canonical `b`-bit target threshold `1 / 2 ^ b`. -/
@[expose] def RatBound.invPow2 (b : Nat) : RatBound := ⟨1, 2 ^ b, Nat.two_pow_pos b⟩

/-- Exact rational sum `(a.num * b.den + b.num * a.den) / (a.den * b.den)`. -/
@[expose] def RatBound.add (a b : RatBound) : RatBound :=
  ⟨a.num * b.den + b.num * a.den, a.den * b.den, Nat.mul_pos a.h_pos b.h_pos⟩

/-- Exact rational product `(a.num * b.num) / (a.den * b.den)`. -/
@[expose] def RatBound.mul (a b : RatBound) : RatBound :=
  ⟨a.num * b.num, a.den * b.den, Nat.mul_pos a.h_pos b.h_pos⟩

/-- Exact integer scaling `(k * a.num) / a.den`. -/
@[expose] def RatBound.scale (k : Nat) (a : RatBound) : RatBound :=
  ⟨k * a.num, a.den, a.h_pos⟩

/-- Exact `k`-fold independent repetition power `a.num ^ k / a.den ^ k`. -/
@[expose] def RatBound.pow (a : RatBound) (k : Nat) : RatBound :=
  ⟨a.num ^ k, a.den ^ k, Nat.pow_pos a.h_pos⟩

/-- Sum a list of component error bounds into a single composed `RatBound`. -/
@[expose] def RatBound.sumList : List RatBound → RatBound
  | [] => RatBound.zero
  | r :: rs => r.add (RatBound.sumList rs)

theorem atLeastBits_iff_le_invPow2 (b : Nat) (r : RatBound) :
    atLeastBits b r ↔ RatBound.le r (RatBound.invPow2 b) := by
  unfold atLeastBits RatBound.le RatBound.invPow2
  dsimp only
  rw [Nat.one_mul]

theorem atLeastBits_of_strictlyMoreThanBits {b : Nat} {r : RatBound}
    (h : strictlyMoreThanBits b r) : atLeastBits b r :=
  Nat.le_of_lt h

theorem exceedsBitBudget_not_atLeastBits {b : Nat} {r : RatBound}
    (h : exceedsBitBudget b r) : ¬ atLeastBits b r := by
  unfold exceedsBitBudget atLeastBits at *
  omega

theorem RatBound.le_refl (a : RatBound) : RatBound.le a a :=
  Nat.le_refl _

theorem RatBound.le_trans {a b c : RatBound}
    (hab : RatBound.le a b) (hbc : RatBound.le b c) : RatBound.le a c := by
  unfold RatBound.le at *
  have h1 : a.num * b.den * c.den ≤ b.num * a.den * c.den :=
    Nat.mul_le_mul_right c.den hab
  have h2 : b.num * c.den * a.den ≤ c.num * b.den * a.den :=
    Nat.mul_le_mul_right a.den hbc
  have hL : a.num * c.den * b.den = a.num * b.den * c.den := by
    rw [Nat.mul_right_comm]
  have hM : b.num * a.den * c.den = b.num * c.den * a.den := by
    rw [Nat.mul_right_comm]
  have hR : c.num * b.den * a.den = c.num * a.den * b.den := by
    rw [Nat.mul_right_comm]
  have hChain : a.num * c.den * b.den ≤ c.num * a.den * b.den := by
    rw [hL, ← hR]
    exact Nat.le_trans h1 (hM ▸ h2)
  exact Nat.le_of_mul_le_mul_right hChain b.h_pos

theorem atLeastBits_of_le {a b : RatBound} {bits : Nat}
    (hab : RatBound.le a b) (hb : atLeastBits bits b) : atLeastBits bits a :=
  (atLeastBits_iff_le_invPow2 bits a).mpr
    (RatBound.le_trans hab ((atLeastBits_iff_le_invPow2 bits b).mp hb))

theorem atLeastBits_antitone_bits {b₁ b₂ : Nat} {r : RatBound}
    (hBits : b₁ ≤ b₂) (h : atLeastBits b₂ r) : atLeastBits b₁ r := by
  unfold atLeastBits at *
  have hPow : 2 ^ b₁ ≤ 2 ^ b₂ := Nat.pow_le_pow_right (by decide) hBits
  exact Nat.le_trans (Nat.mul_le_mul_left r.num hPow) h

theorem RatBound.add_le_add {a₁ b₁ a₂ b₂ : RatBound}
    (h1 : RatBound.le a₁ b₁) (h2 : RatBound.le a₂ b₂) :
    RatBound.le (a₁.add a₂) (b₁.add b₂) := by
  unfold RatBound.le RatBound.add at *
  dsimp only
  have t1 : a₁.num * a₂.den * (b₁.den * b₂.den) ≤ b₁.num * b₂.den * (a₁.den * a₂.den) := by
    have p1 : a₁.num * b₁.den * (a₂.den * b₂.den) ≤ b₁.num * a₁.den * (a₂.den * b₂.den) :=
      Nat.mul_le_mul_right _ h1
    have eqL : a₁.num * a₂.den * (b₁.den * b₂.den) = a₁.num * b₁.den * (a₂.den * b₂.den) := by
      rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_right_comm a₁.num a₂.den b₁.den]
    have eqR : b₁.num * b₂.den * (a₁.den * a₂.den) = b₁.num * a₁.den * (a₂.den * b₂.den) := by
      rw [Nat.mul_comm a₂.den b₂.den, ← Nat.mul_assoc, ← Nat.mul_assoc,
          Nat.mul_right_comm b₁.num b₂.den a₁.den]
    rw [eqL, eqR]; exact p1
  have t2 : a₂.num * a₁.den * (b₁.den * b₂.den) ≤ b₂.num * b₁.den * (a₁.den * a₂.den) := by
    have p2 : a₂.num * b₂.den * (a₁.den * b₁.den) ≤ b₂.num * a₂.den * (a₁.den * b₁.den) :=
      Nat.mul_le_mul_right _ h2
    have eqL : a₂.num * a₁.den * (b₁.den * b₂.den) = a₂.num * b₂.den * (a₁.den * b₁.den) := by
      rw [Nat.mul_comm b₁.den b₂.den, ← Nat.mul_assoc, ← Nat.mul_assoc,
          Nat.mul_right_comm a₂.num a₁.den b₂.den]
    have eqR : b₂.num * b₁.den * (a₁.den * a₂.den) = b₂.num * a₂.den * (a₁.den * b₁.den) := by
      rw [Nat.mul_comm a₁.den b₁.den, Nat.mul_comm a₁.den a₂.den, ← Nat.mul_assoc, ← Nat.mul_assoc,
          Nat.mul_right_comm b₂.num b₁.den a₂.den]
    rw [eqL, eqR]; exact p2
  rw [Nat.right_distrib, Nat.right_distrib]
  exact Nat.add_le_add t1 t2

theorem RatBound.mul_le_mul {a₁ b₁ a₂ b₂ : RatBound}
    (h1 : RatBound.le a₁ b₁) (h2 : RatBound.le a₂ b₂) :
    RatBound.le (a₁.mul a₂) (b₁.mul b₂) := by
  unfold RatBound.le RatBound.mul at *
  dsimp only
  have hProd := Nat.mul_le_mul h1 h2
  have eqL : a₁.num * a₂.num * (b₁.den * b₂.den) = (a₁.num * b₁.den) * (a₂.num * b₂.den) := by
    rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_right_comm a₁.num a₂.num b₁.den]
  have eqR : b₁.num * b₂.num * (a₁.den * a₂.den) = (b₁.num * a₁.den) * (b₂.num * a₂.den) := by
    rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_right_comm b₁.num b₂.num a₁.den]
  rw [eqL, eqR]
  exact hProd

theorem RatBound.pow_le_pow {a b : RatBound} (h : RatBound.le a b) :
    ∀ k : Nat, RatBound.le (a.pow k) (b.pow k)
  | 0 => by simp [RatBound.pow, RatBound.le]
  | k + 1 => by
    have ih := RatBound.pow_le_pow h k
    have hEqA : a.pow (k + 1) = (a.pow k).mul a := by
      ext <;> simp [RatBound.pow, RatBound.mul, Nat.pow_succ]
    have hEqB : b.pow (k + 1) = (b.pow k).mul b := by
      ext <;> simp [RatBound.pow, RatBound.mul, Nat.pow_succ]
    rw [hEqA, hEqB]
    exact RatBound.mul_le_mul ih h

/-- **2-Way Union-Bound Bit Loss**: summing two `(b + 1)`-bit bounds preserves `b` bits. -/
theorem atLeastBits_add_union_loss {b : Nat} {r₁ r₂ : RatBound}
    (h₁ : atLeastBits (b + 1) r₁) (h₂ : atLeastBits (b + 1) r₂) :
    atLeastBits b (r₁.add r₂) := by
  unfold atLeastBits RatBound.add at *
  dsimp only
  rw [Nat.pow_succ] at h₁ h₂
  have m₁ : r₁.num * (2 ^ b * 2) * r₂.den ≤ r₁.den * r₂.den :=
    Nat.mul_le_mul_right r₂.den h₁
  have m₂ : r₂.num * (2 ^ b * 2) * r₁.den ≤ r₂.den * r₁.den :=
    Nat.mul_le_mul_right r₁.den h₂
  have sum2 : (r₁.num * r₂.den + r₂.num * r₁.den) * 2 ^ b * 2 ≤ (r₁.den * r₂.den) * 2 := by
    have lhsEq : (r₁.num * r₂.den + r₂.num * r₁.den) * 2 ^ b * 2 =
        r₁.num * (2 ^ b * 2) * r₂.den + r₂.num * (2 ^ b * 2) * r₁.den := by
      rw [Nat.right_distrib, Nat.right_distrib]
      have e1 : r₁.num * r₂.den * 2 ^ b * 2 = r₁.num * (2 ^ b * 2) * r₂.den := by
        rw [Nat.mul_right_comm r₁.num r₂.den (2 ^ b),
            Nat.mul_right_comm (r₁.num * 2 ^ b) r₂.den 2,
            Nat.mul_assoc r₁.num (2 ^ b) 2]
      have e2 : r₂.num * r₁.den * 2 ^ b * 2 = r₂.num * (2 ^ b * 2) * r₁.den := by
        rw [Nat.mul_right_comm r₂.num r₁.den (2 ^ b),
            Nat.mul_right_comm (r₂.num * 2 ^ b) r₁.den 2,
            Nat.mul_assoc r₂.num (2 ^ b) 2]
      rw [e1, e2]
    have m₂' : r₂.num * (2 ^ b * 2) * r₁.den ≤ r₁.den * r₂.den := by
      rw [Nat.mul_comm r₁.den r₂.den]
      exact m₂
    rw [lhsEq, Nat.mul_two (r₁.den * r₂.den)]
    exact Nat.add_le_add m₁ m₂'
  exact Nat.le_of_mul_le_mul_right sum2 (by decide)

theorem RatBound.sumList_le_length_mul {bound : RatBound} :
    ∀ (xs : List RatBound), (∀ r ∈ xs, RatBound.le r bound) →
      RatBound.le (RatBound.sumList xs) (RatBound.scale xs.length bound)
  | [], _ => by simp [RatBound.sumList, RatBound.zero, RatBound.scale, RatBound.le]
  | x :: xs, hAll => by
    have hx := hAll x (.head _)
    have hxs := RatBound.sumList_le_length_mul xs (fun r hr => hAll r (.tail _ hr))
    have hAdd := RatBound.add_le_add hx hxs
    apply RatBound.le_trans hAdd
    unfold RatBound.add RatBound.scale RatBound.le
    dsimp only [List.length_cons]
    have hEq : (bound.num * bound.den + xs.length * bound.num * bound.den) * bound.den =
        (xs.length + 1) * bound.num * (bound.den * bound.den) := by
      calc (bound.num * bound.den + xs.length * bound.num * bound.den) * bound.den
        _ = bound.num * (bound.den * bound.den) + xs.length * (bound.num * (bound.den * bound.den)) := by
          rw [Nat.add_mul, Nat.mul_assoc bound.num, Nat.mul_assoc (xs.length * bound.num),
              Nat.mul_assoc xs.length bound.num]
        _ = (1 + xs.length) * (bound.num * (bound.den * bound.den)) := by
          rw [Nat.add_mul, Nat.one_mul]
        _ = (xs.length + 1) * bound.num * (bound.den * bound.den) := by
          rw [Nat.add_comm 1 xs.length, Nat.mul_assoc]
    exact Nat.le_of_eq hEq

/-- **`N`-Way Compositional Union-Bound Bit Loss**: summing up to `2 ^ loss` component bounds,
    each achieving `b + loss` bits, guarantees `atLeastBits b` on their exact rational sum. -/
theorem atLeastBits_sumList_union_loss {b loss : Nat} {xs : List RatBound}
    (hLen : xs.length ≤ 2 ^ loss)
    (hEach : ∀ r ∈ xs, atLeastBits (b + loss) r) :
    atLeastBits b (RatBound.sumList xs) := by
  have hLeInv : ∀ r ∈ xs, RatBound.le r (RatBound.invPow2 (b + loss)) :=
    fun r hr => (atLeastBits_iff_le_invPow2 (b + loss) r).mp (hEach r hr)
  have hSumLe := RatBound.sumList_le_length_mul xs hLeInv
  apply atLeastBits_of_le hSumLe
  unfold atLeastBits RatBound.scale RatBound.invPow2
  dsimp only
  rw [Nat.mul_one, Nat.pow_add, Nat.mul_comm (2 ^ b) (2 ^ loss)]
  exact Nat.mul_le_mul_right (2 ^ b) hLen

/-- **Multi-Session Scaling Bit Loss**: scaling a `(b + sLog)`-bit bound across up to `2 ^ sLog`
    concurrent or sequential protocol sessions preserves `atLeastBits b` on `RatBound.scale S r`. -/
theorem atLeastBits_scale_session_loss {b sLog S : Nat} {r : RatBound}
    (hS : S ≤ 2 ^ sLog) (hBits : atLeastBits (b + sLog) r) :
    atLeastBits b (RatBound.scale S r) := by
  unfold atLeastBits RatBound.scale at *
  dsimp only
  have h1 : S * r.num * 2 ^ b = r.num * (S * 2 ^ b) := by
    rw [Nat.mul_comm S r.num, Nat.mul_assoc]
  have h2 : S * 2 ^ b ≤ 2 ^ (b + sLog) := by
    rw [Nat.pow_add, Nat.mul_comm (2 ^ b) (2 ^ sLog)]
    exact Nat.mul_le_mul_right (2 ^ b) hS
  rw [h1]
  exact Nat.le_trans (Nat.mul_le_mul_left r.num h2) hBits

/-- Adversarial query resource budget across random-oracle / permutation calls, signing
    invocations, and concurrent or sequential interactive protocol sessions. -/
structure QueryBudget where
  qHash : Nat
  qSign : Nat
  qOnlineSessions : Nat
  deriving DecidableEq, Repr

/-- Standard `PQ128` QROM evaluation budget (`qHash = 2^60`, `qSign = 2^16`, `qOnlineSessions = 2^20`),
    accounting for the explicit `8 (q + 1)^2` Zhandry/BBBV constant factor inside 256-bit targets. -/
def standardPq128Budget : QueryBudget where
  qHash := 2 ^ 60
  qSign := 2 ^ 16
  qOnlineSessions := 2 ^ 20



namespace RatBound
theorem zero_num : zero.num = 0 := by rfl
theorem zero_den : zero.den = 1 := by rfl
theorem sumList_nil : sumList [] = zero := by rfl
theorem sumList_cons (r : RatBound) (rs : List RatBound) : sumList (r :: rs) = r.add (sumList rs) := by rfl
end RatBound
end Qsag

namespace Qsag.RatBound
@[simp] theorem one_num : one.num = 1 := by rfl
@[simp] theorem one_den : one.den = 1 := by rfl
end Qsag.RatBound

namespace Qsag
public section

theorem RatBound.scale_mono {a b : RatBound} (k : Nat) (h : a.le b) :
    (a.scale k).le (b.scale k) := by
  unfold RatBound.le RatBound.scale at *
  dsimp only
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left k h

theorem RatBound.le_add_left (a b : RatBound) : a.le (a.add b) := by
  unfold RatBound.le RatBound.add
  dsimp only
  rw [Nat.add_mul, ← Nat.mul_assoc, Nat.mul_right_comm a.num a.den b.den]
  exact Nat.le_add_right _ _

theorem RatBound.le_add_right (a b : RatBound) : b.le (a.add b) := by
  unfold RatBound.le RatBound.add
  dsimp only
  rw [Nat.add_mul]
  have h : b.num * (a.den * b.den) = b.num * a.den * b.den := (Nat.mul_assoc _ _ _).symm
  rw [h]
  exact Nat.le_add_left _ _

theorem RatBound.strictlyMoreThanBits_of_le {a b : RatBound} {bits : Nat}
    (hab : a.le b) (hb : strictlyMoreThanBits bits b) : strictlyMoreThanBits bits a := by
  unfold RatBound.le at hab
  unfold strictlyMoreThanBits at *
  have hm := Nat.mul_le_mul_right (2 ^ bits) hab
  have hs := Nat.mul_lt_mul_of_pos_right hb a.h_pos
  have hlt : a.num * 2 ^ bits * b.den < a.den * b.den := by
    have he1 : a.num * b.den * 2 ^ bits = a.num * 2 ^ bits * b.den := by rw [Nat.mul_right_comm]
    have he2 : b.num * a.den * 2 ^ bits = b.num * 2 ^ bits * a.den := by rw [Nat.mul_right_comm]
    rw [he1, he2] at hm
    exact Nat.lt_of_le_of_lt hm (by simpa only [Nat.mul_comm a.den b.den] using hs)
  if hSmall : a.num * 2 ^ bits < a.den then
    exact hSmall
  else
    have hGe := Nat.mul_le_mul_right b.den (Nat.le_of_not_lt hSmall)
    exact False.elim (Nat.not_le_of_gt hlt hGe)

theorem RatBound.num_pos_of_le {a b : RatBound} (ha : 0 < a.num) (h : a.le b) : 0 < b.num := by
  have hp := Nat.mul_pos ha b.h_pos
  unfold RatBound.le at h
  have hb : 0 < b.num * a.den := Nat.lt_of_lt_of_le hp h
  exact Nat.pos_of_mul_pos_right hb

end
end Qsag
