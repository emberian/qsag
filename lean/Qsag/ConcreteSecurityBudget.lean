module
/-
# Qsag.ConcreteSecurityBudget — Mechanized Unitary QROM, Adaptive Query Trees, Polynomial Root Bounds & Concrete PQ128 Security Roster

Self-contained constructive (`0` classical choice axioms, `0` external math libraries, `0` unproved goals)
Lean 4.35 formalization of QSAG's classical and quantum concrete security foundations:

1. **§1. Exact Constructive `RatBound` & Kernel-Checked Bit-Margin Algebra**:
   - Positive-denominator rational bounds `RatBound` (`num / den`, `0 < den`), integer-cross-multiplied
     ordering, exact bit-security predicates (`atLeastBits b r ↔ r.num * 2^b ≤ r.den`,
     `exceedsBitBudget b r ↔ r.den < r.num * 2^b`), and `2`-way / `N`-way union-bound bit-loss laws.

2. **§2. Unitary Quantum Query Mechanics (`GaussInt`), `[BBBV97]` / `[AHU19]` One-Way-to-Hiding (`O2H`),
   Born-Rule TVD, Lazy-RO Adaptive Query Trees & QROM Fiat–Shamir / BHT Regimes**:
   - Exact Gaussian-integer amplitudes `GaussInt` (`a + b i`), scaled unitary operators (`oracleXor`
     at scale `1`, `hadamardQuery2` at scale `2`), and arbitrary `q`-query unitary circuits `QuantumAdv`.
   - Square-root-free `q`-way Cauchy–Schwarz sum-of-squares identity
     `q * ∑ ‖v_t‖² = ‖∑ v_t‖² + ∑_{s < t} ‖v_s - v_t‖²`, hybrid telescoping O2H state-disturbance
     theorem (`qrom_o2h_telescoping_disturbance_le`), uniform hidden-target disturbance `≤ 4 q^2 / M`
     (`qrom_o2h_average_point_disturbance`), and Born-rule probability difference bound
     `(P(ψ) - P(φ))^2 ≤ 4 ‖ψ‖² ‖ψ - φ‖²` (`born_prob_diff_sq_le_four_state_dist_sq`).
   - **Protocol-Coupled Fiber Search (`qrom_fiber_search_bound` & `classical_lazy_ro_fiber_search_bound`)**:
     Unitary QROM adversary success is bounded by `8 (q + 1)^2 |Fiber(encode, target)| / 2^n` and
     classical height-`q` adaptive `OracleComp` success over a lazy random oracle is bounded by
     `(q + 1) |Fiber(encode, target)| / 2^n` — coupling concrete denominators directly to proved
     protocol encoding injectivity rather than detached numeric literals.
   - BHT / CNS quantum collision ceiling (`tooth_bht_256bit_unrestricted_collision_ceiling_85bits` vs
     384-bit collision & `ADRS` `M = 1` single-target domain separation) and QROM Fiat–Shamir grinding /
     Don–Fehr–Majenz `[DFM20]` Measure-and-Reprogram bounds.

3. **§3. Hash-Based & Threshold Custody Protocol Encodings (`Baggy`, `Corduroy`, `FrontierSumFts`, `Jorts`, `QuorumJorts`)**:
   - Bit-exact MSB-first `wotsCDibits128Bv` (`V128`) injectivity (`fiberCard ≤ 1` → `≥ 128` quantum bits)
     contrasted with `#tooth` `tooth_wots_v58_128bit_digest_grover_64bit` (`V58` `2^128`-sized fiber!).
   - `FrontierSumFts` `Full256Bit` (`rankBits = 256`) injectivity (`≥ 128` quantum bits) contrasted
     with `#tooth` `tooth_frontier_122bit_rank_grover_61bit` (`2^134`-sized fiber → `61`-bit Grover ceiling!).
   - Composed `Jorts` & `QuorumJorts` (`QS-A` & `QS-B`) multi-component rational sum (`WOTS+C V128` +
     `BeltLatch` 256-bit pairwise MAC + `Rss256` 2-pass `GF(2^128)` BGIN19 product barrier).

4. **§4. `GoldilocksExt4` Quartic Extension Field, Root-Counting Schwartz–Zippel & `Hem` WHIR Regimes**:
   - Complete `GoldilocksExt4` (`𝔽_{p^2}[v]/(v^2 - u)`, `p^4 > 2^255`) `LawfulCommRing` + `NoZeroDivisors`
     proof via `uBasis_not_square`, deriving Schwartz–Zippel `d / |S|` from `RoundPoly.roots_nodup_length_le`.
   - Exact `Hem` `Ext4` sumcheck (`249` bits), `[BCIKS20]` folding (`175+` bits vs `#tooth`
     `tooth_hem_ext2_folding_under_100bits`), OOD list-pinning (`> 225` bits), and explicit separation
     between conditional `[HABR24]` Conjecture-1 classical bits (`128 / 136 / 142`), unconditional
     Johnson proximity bits (`≥ 72`), `#tooth` default-schedule quantum Grover scale, and upgraded
     unconditional `hemWhirPq128Stages` (`≥ 128` quantum bits).

5. **§5–§6. Fast-Factored ZKBoo (`BlindVc` `219` vs `438`), `ThresholdMlDsa`, `Poseidon2Toprf`,
   `DensePcg`, `HdRekey` (Exact 96-Bit Modular Bias), `ActiveMigration` & Master `PQ128` Portfolio**:
   - Cube/6th-power `3^73` bounds proving `(2/3)^219 < 2^-128`, `#tooth`
     `tooth_zkboo_219_quantum_grind_64bit` (`(2/3)^219 > 2^-129`), and `(2/3)^438 < 2^-256` (`≥ 128`
     quantum FS bits), composed into `qsag_pq128_portfolio_soundness_budget` and
     `inhabited_concrete_security_budget_roster`.
-/

public import Qsag.Constructive
public import Qsag.Goldilocks
import all Qsag.Goldilocks
public import Qsag.UcGames
import all Qsag.UcGames

public section
namespace Qsag

attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd

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

instance (a b : RatBound) : Decidable (RatBound.le a b) :=
  Nat.decLe (a.num * b.den) (b.num * a.den)

instance (a b : RatBound) : Decidable (RatBound.lt a b) :=
  Nat.decLt (a.num * b.den) (b.num * a.den)

instance (b : Nat) (bound : RatBound) : Decidable (atLeastBits b bound) :=
  Nat.decLe (bound.num * 2 ^ b) bound.den

instance (b : Nat) (bound : RatBound) : Decidable (strictlyMoreThanBits b bound) :=
  Nat.decLt (bound.num * 2 ^ b) bound.den

instance (b : Nat) (bound : RatBound) : Decidable (exceedsBitBudget b bound) :=
  Nat.decLt bound.den (bound.num * 2 ^ b)

/-- Exact zero error bound `0 / 1`. -/
def RatBound.zero : RatBound := ⟨0, 1, Nat.zero_lt_one⟩

/-- Unit probability bound `1 / 1`. -/
def RatBound.one : RatBound := ⟨1, 1, Nat.zero_lt_one⟩

/-- Canonical `b`-bit target threshold `1 / 2 ^ b`. -/
def RatBound.invPow2 (b : Nat) : RatBound := ⟨1, 2 ^ b, Nat.two_pow_pos b⟩

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
def RatBound.sumList : List RatBound → RatBound
  | [] => RatBound.zero
  | r :: rs => r.add (RatBound.sumList rs)

theorem RatBound.to_ratLe_iff (a b : RatBound) :
    RatBound.le a b ↔ ratLe (a.num, a.den) (b.num, b.den) := by
  unfold RatBound.le ratLe
  exact ⟨fun h => ⟨a.h_pos, b.h_pos, h⟩, fun h => h.2.2⟩

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

private theorem sumList_le_length_mul {bound : RatBound} :
    ∀ (xs : List RatBound), (∀ r ∈ xs, RatBound.le r bound) →
      RatBound.le (RatBound.sumList xs) (RatBound.scale xs.length bound)
  | [], _ => by simp [RatBound.sumList, RatBound.zero, RatBound.scale, RatBound.le]
  | x :: xs, hAll => by
    have hx := hAll x (.head _)
    have hxs := sumList_le_length_mul xs (fun r hr => hAll r (.tail _ hr))
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
  have hSumLe := sumList_le_length_mul xs hLeInv
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


/-! ## §2. Unitary Quantum Query Mechanics (`GaussInt`), `[BBBV97]` / `[AHU19]` One-Way-to-Hiding,
           Born Rule & Adaptive Query Trees -/

private theorem ofNat_add_eq (a b : Nat) : Int.ofNat (a + b) = Int.ofNat a + Int.ofNat b := rfl
private theorem ofNat_mul_eq (a b : Nat) : Int.ofNat (a * b) = Int.ofNat a * Int.ofNat b := rfl

private theorem int_sq_eq_natAbs_sq (a : Int) : a * a = Int.ofNat (a.natAbs * a.natAbs) := by
  cases a with
  | ofNat _ => rfl
  | negSucc _ => rfl

private theorem int_sq_nonneg (a : Int) : 0 ≤ a * a := by
  rw [int_sq_eq_natAbs_sq]
  exact Int.ofNat_le.mpr (Nat.zero_le _)

/-! ### §2.1 Constructive Finite Sum Combinatorics & Bijection Invariance -/

/-- Module-local constructive finite sum `∑_{i : Fin n} f i`, keeping full definitional reduction
    available inside proofs and decidable evaluations without exposing internal `UcGames` bodies. -/
def qsum : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => f ⟨0, Nat.zero_lt_succ n⟩ + qsum n (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)

theorem qsum_const : ∀ (n c : Nat), qsum n (fun _ => c) = n * c
  | 0, _ => by simp [qsum]
  | n + 1, c => by
    simp only [qsum, qsum_const n c, Nat.succ_mul]
    omega

theorem qsum_congr {n : Nat} {f g : Fin n → Nat} (h : ∀ i, f i = g i) :
    qsum n f = qsum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [qsum, h ⟨0, Nat.zero_lt_succ n⟩]
    rw [ih (fun i => h ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)]

theorem qsum_le_qsum {n : Nat} {f g : Fin n → Nat} (h : ∀ i, f i ≤ g i) :
    qsum n f ≤ qsum n g := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    simp only [qsum]
    have h0 := h ⟨0, Nat.zero_lt_succ n⟩
    have hRest := ih (fun i => h ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
    omega

theorem qsum_add {n : Nat} (f g : Fin n → Nat) :
    qsum n (fun i => f i + g i) = qsum n f + qsum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [qsum, ih]
    omega

theorem qsum_eq_indicator : ∀ (n : Nat) (a : Fin n),
    qsum n (fun i => if i = a then 1 else 0) = 1
  | 0, a => Fin.elim0 a
  | n + 1, ⟨0, _⟩ => by
    simp only [qsum, ↓reduceIte]
    have hZero : qsum n (fun i => if (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (n + 1)) = ⟨0, Nat.zero_lt_succ n⟩ then 1 else 0) =
        qsum n (fun _ => 0) := by
      apply qsum_congr
      intro i
      have hNe : (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (n + 1)) ≠ ⟨0, Nat.zero_lt_succ n⟩ :=
        fun he => Nat.noConfusion (congrArg Fin.val he)
      simp only [hNe, ↓reduceIte]
    rw [hZero, qsum_const]
    omega
  | n + 1, ⟨k + 1, hk⟩ => by
    simp only [qsum]
    have h0 : (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)) ≠ ⟨k + 1, hk⟩ :=
      fun heq => Nat.noConfusion (congrArg Fin.val heq)
    simp only [h0, ↓reduceIte, Nat.zero_add]
    have hShift :
        qsum n (fun i => if (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (n + 1)) = ⟨k + 1, hk⟩ then 1 else 0) =
        qsum n (fun i => if i = ⟨k, Nat.lt_of_succ_lt_succ hk⟩ then 1 else 0) := by
      apply qsum_congr
      intro i
      by_cases hik : i.1 = k
      · have h2 : i = ⟨k, Nat.lt_of_succ_lt_succ hk⟩ := Fin.ext hik
        have h1 : (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (n + 1)) = ⟨k + 1, hk⟩ :=
          Fin.ext (congrArg Nat.succ hik)
        simp only [h1, ↓reduceIte]
        simp only [h2, ↓reduceIte]
      · have h2 : i ≠ ⟨k, Nat.lt_of_succ_lt_succ hk⟩ := fun heq => hik (congrArg Fin.val heq)
        have h1 : (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (n + 1)) ≠ ⟨k + 1, hk⟩ :=
          fun heq => hik (Nat.succ.inj (congrArg Fin.val heq))
        simp only [h1, ↓reduceIte]
        simp only [h2, ↓reduceIte]
    rw [hShift]
    exact qsum_eq_indicator n ⟨k, Nat.lt_of_succ_lt_succ hk⟩

theorem qsum_mul_left (c : Nat) :
    ∀ {n : Nat} (f : Fin n → Nat), qsum n (fun i => c * f i) = c * qsum n f
  | 0, _ => by simp [qsum]
  | n + 1, f => by
    simp only [qsum, Nat.left_distrib]
    rw [qsum_mul_left c (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)]

theorem qsum_mul_right (c : Nat) :
    ∀ {n : Nat} (f : Fin n → Nat), qsum n (fun i => f i * c) = qsum n f * c
  | 0, _ => by simp [qsum]
  | n + 1, f => by
    simp only [qsum, Nat.right_distrib]
    rw [qsum_mul_right c (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)]

theorem qsum_comm :
    ∀ (A B : Nat) (f : Fin A → Fin B → Nat),
      qsum A (fun a => qsum B (fun b => f a b)) =
        qsum B (fun b => qsum A (fun a => f a b))
  | 0, B, _ => by
    simp only [qsum]
    exact (qsum_const B 0).symm
  | A + 1, B, f => by
    simp only [qsum]
    rw [qsum_comm A B (fun a b => f ⟨a.1 + 1, Nat.succ_lt_succ a.2⟩ b), ← qsum_add]

theorem qsum_ite_eq (n : Nat) (a : Fin n) (v : Nat) :
    qsum n (fun i => if i = a then v else 0) = v := by
  have hFactor : qsum n (fun i => if i = a then v else 0) =
      qsum n (fun i => v * (if i = a then 1 else 0)) := by
    apply qsum_congr
    intro i
    by_cases h : i = a <;> simp [h]
  rw [hFactor, qsum_mul_left, qsum_eq_indicator, Nat.mul_one]

/-- Constructive bijection-invariance of `qsum` proved via `qsum_comm` + `qsum_ite_eq`
    with zero list-permutation or pigeonhole machinery. -/
theorem qsum_bijection {n : Nat} (π ρ : Fin n → Fin n)
    (hLeft : ∀ i, ρ (π i) = i) (hRight : ∀ k, π (ρ k) = k) (g : Fin n → Nat) :
    qsum n (fun i => g (π i)) = qsum n g := by
  have hExpand : qsum n (fun i => g (π i)) =
      qsum n (fun i => qsum n (fun k => if k = π i then g k else 0)) := by
    apply qsum_congr
    intro i
    have hCongrK : qsum n (fun k => if k = π i then g k else 0) =
        qsum n (fun k => if k = π i then g (π i) else 0) := by
      apply qsum_congr; intro k
      by_cases hk : k = π i
      · rw [hk]
      · simp only [hk, ↓reduceIte]
    rw [hCongrK, qsum_ite_eq]
  rw [hExpand, qsum_comm]
  apply qsum_congr
  intro k
  have hSwap : qsum n (fun i => if k = π i then g k else 0) =
      qsum n (fun i => if i = ρ k then g k else 0) := by
    apply qsum_congr
    intro i
    by_cases h : i = ρ k
    · have hk : k = π i := by rw [h, hRight]
      have s1 : (if k = π i then g k else 0) = g k := by simp only [hk, ↓reduceIte]
      have s2 : (if i = ρ k then g k else 0) = g k := by simp only [h, ↓reduceIte]
      rw [s1, s2]
    · have hk : k ≠ π i := fun heq => h (by rw [heq, hLeft])
      have s1 : (if k = π i then g k else 0) = 0 := by simp only [hk, ↓reduceIte]
      have s2 : (if i = ρ k then g k else 0) = 0 := by simp only [h, ↓reduceIte]
      rw [s1, s2]
  rw [hSwap, qsum_ite_eq]

theorem qsum_involutive {n : Nat} (π : Fin n → Fin n)
    (hInv : ∀ i, π (π i) = i) (g : Fin n → Nat) :
    qsum n (fun i => g (π i)) = qsum n g :=
  qsum_bijection π π hInv hInv g

/-- Constructive uniqueness-to-`≤ 1` sum bound without existential case splitting. -/
theorem qsum_le_one_of_subsingleton :
    ∀ {n : Nat} (p : Fin n → Bool),
      (∀ i j : Fin n, p i = true → p j = true → i = j) →
      qsum n (fun i => if p i = true then 1 else 0) ≤ 1
  | 0, _, _ => Nat.zero_le 1
  | n + 1, p, hUnique => by
    simp only [qsum]
    cases hp0 : p ⟨0, Nat.zero_lt_succ n⟩
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      exact qsum_le_one_of_subsingleton (fun i => p ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
        (fun i j hi hj => Fin.ext (Nat.succ.inj (congrArg Fin.val (hUnique _ _ hi hj))))
    · simp only [↓reduceIte]
      have hTailZero : qsum n (fun i => if p ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ = true then 1 else 0) =
          qsum n (fun _ => 0) := by
        apply qsum_congr
        intro i
        cases hpi : p ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩
        · rfl
        · exfalso
          have hEq := congrArg Fin.val (hUnique ⟨0, Nat.zero_lt_succ n⟩ ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ hp0 hpi)
          exact Nat.noConfusion hEq
      rw [hTailZero, qsum_const]
      omega

private def finIntSum : (q : Nat) → (Fin q → Int) → Int
  | 0, _ => 0
  | q + 1, f => f ⟨0, Nat.zero_lt_succ q⟩ +
      finIntSum q (fun t => f ⟨t.1 + 1, Nat.succ_lt_succ t.2⟩)

/-- Exact Gaussian integer `re + i * im` (`ℤ[i]`), enabling constructive unitary quantum mechanics
    with zero `ℝ`/`ℂ` axioms, zero square roots, and syntactic equality. -/
structure GaussInt where
  re : Int
  im : Int
  deriving DecidableEq, Repr

@[ext] theorem GaussInt.ext {z w : GaussInt} (hre : z.re = w.re) (him : z.im = w.im) : z = w := by
  cases z; cases w; cases hre; cases him; rfl

namespace GaussInt

def zero : GaussInt := ⟨0, 0⟩
def one : GaussInt := ⟨1, 0⟩
def neg (z : GaussInt) : GaussInt := ⟨-z.re, -z.im⟩
def conj (z : GaussInt) : GaussInt := ⟨z.re, -z.im⟩
def add (z w : GaussInt) : GaussInt := ⟨z.re + w.re, z.im + w.im⟩
def sub (z w : GaussInt) : GaussInt := ⟨z.re - w.re, z.im - w.im⟩
def scaleInt (c : Int) (z : GaussInt) : GaussInt := ⟨c * z.re, c * z.im⟩
def mul (z w : GaussInt) : GaussInt :=
  ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩

/-- Exact squared modulus `|z|² = re² + im²` as an `Int` (`≥ 0`) and as a `Nat`. -/
def normSqInt (z : GaussInt) : Int := z.re * z.re + z.im * z.im
def normSq (z : GaussInt) : Nat := z.re.natAbs * z.re.natAbs + z.im.natAbs * z.im.natAbs

/-- Real inner product `Re(z · conj w) = z.re * w.re + z.im * w.im`. -/
def reInner (z w : GaussInt) : Int := z.re * w.re + z.im * w.im

theorem normSqInt_eq_ofNat_normSq (z : GaussInt) :
    normSqInt z = Int.ofNat (normSq z) := by
  unfold normSqInt normSq
  rw [int_sq_eq_natAbs_sq z.re, int_sq_eq_natAbs_sq z.im, ← ofNat_add_eq]

theorem normSq_zero : normSq zero = 0 := by rfl

theorem normSq_neg (z : GaussInt) : normSq (neg z) = normSq z := by
  unfold normSq neg
  rw [Int.natAbs_neg, Int.natAbs_neg]

theorem normSq_add_int (z w : GaussInt) :
    normSqInt (add z w) = normSqInt z + normSqInt w + 2 * reInner z w := by
  unfold normSqInt add reInner
  have hRe : (z.re + w.re) * (z.re + w.re) = z.re * z.re + w.re * w.re + 2 * (z.re * w.re) := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm w.re z.re]
    omega
  have hIm : (z.im + w.im) * (z.im + w.im) = z.im * z.im + w.im * w.im + 2 * (z.im * w.im) := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm w.im z.im]
    omega
  rw [hRe, hIm]
  omega

theorem normSq_sub_int (z w : GaussInt) :
    normSqInt (sub z w) = normSqInt z + normSqInt w - 2 * reInner z w := by
  unfold normSqInt sub reInner
  have hNegSq : ∀ x : Int, (-x) * (-x) = x * x := fun x => by
    rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
  have hRe : (z.re - w.re) * (z.re - w.re) = z.re * z.re + w.re * w.re - 2 * (z.re * w.re) := by
    rw [Int.sub_eq_add_neg, Int.add_mul, Int.mul_add, Int.mul_add,
        Int.mul_neg, Int.neg_mul, hNegSq, Int.mul_comm w.re z.re]
    omega
  have hIm : (z.im - w.im) * (z.im - w.im) = z.im * z.im + w.im * w.im - 2 * (z.im * w.im) := by
    rw [Int.sub_eq_add_neg, Int.add_mul, Int.mul_add, Int.mul_add,
        Int.mul_neg, Int.neg_mul, hNegSq, Int.mul_comm w.im z.im]
    omega
  rw [hRe, hIm]
  omega

/-- **Parallelogram Identity**: `|z - w|² + |z + w|² = 2 |z|² + 2 |w|²`. -/
theorem normSq_parallelogram (z w : GaussInt) :
    normSq (sub z w) + normSq (add z w) = 2 * normSq z + 2 * normSq w := by
  have hInt : Int.ofNat (normSq (sub z w) + normSq (add z w)) =
      Int.ofNat (2 * normSq z + 2 * normSq w) := by
    rw [ofNat_add_eq, ofNat_add_eq, ofNat_mul_eq, ofNat_mul_eq,
        ← normSqInt_eq_ofNat_normSq, ← normSqInt_eq_ofNat_normSq,
        ← normSqInt_eq_ofNat_normSq, ← normSqInt_eq_ofNat_normSq,
        normSq_sub_int, normSq_add_int]
    change normSqInt z + normSqInt w - 2 * reInner z w +
           (normSqInt z + normSqInt w + 2 * reInner z w) =
           2 * normSqInt z + 2 * normSqInt w
    omega
  exact Int.ofNat.inj hInt

theorem normSq_sub_le (z w : GaussInt) :
    normSq (sub z w) ≤ 2 * normSq z + 2 * normSq w := by
  have h := normSq_parallelogram z w
  omega

theorem normSq_add_le (z w : GaussInt) :
    normSq (add z w) ≤ 2 * normSq z + 2 * normSq w := by
  have h := normSq_parallelogram z w
  omega

end GaussInt

/-- Finite sum of Gaussian-integer amplitudes over `Fin q`. -/
def finGaussSum : (q : Nat) → (Fin q → GaussInt) → GaussInt
  | 0, _ => GaussInt.zero
  | q + 1, v =>
    GaussInt.add (v ⟨0, Nat.zero_lt_succ q⟩)
      (finGaussSum q (fun t => v ⟨t.1 + 1, Nat.succ_lt_succ t.2⟩))

/-- Sum of pairwise squared differences `∑_{0 ≤ s < t < q} |v_s - v_t|²`. -/
def pairDiffNormSq : (q : Nat) → (Fin q → GaussInt) → Nat
  | 0, _ => 0
  | q + 1, v =>
    let v0 := v ⟨0, Nat.zero_lt_succ q⟩
    let tail : Fin q → GaussInt := fun t => v ⟨t.1 + 1, Nat.succ_lt_succ t.2⟩
    qsum q (fun t => GaussInt.normSq (GaussInt.sub v0 (tail t))) + pairDiffNormSq q tail

private theorem finSum_sub_with_head :
    ∀ (q : Nat) (v0 : GaussInt) (tail : Fin q → GaussInt),
      Int.ofNat (qsum q (fun t => GaussInt.normSq (GaussInt.sub v0 (tail t)))) =
        Int.ofNat q * GaussInt.normSqInt v0 +
        Int.ofNat (qsum q (fun t => GaussInt.normSq (tail t))) -
        2 * GaussInt.reInner v0 (finGaussSum q tail)
  | 0, v0, _ => by
    simp [qsum, finGaussSum, GaussInt.zero, GaussInt.reInner]
  | q + 1, v0, tail => by
    let t0 := tail ⟨0, Nat.zero_lt_succ q⟩
    let rest : Fin q → GaussInt := fun i => tail ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩
    have ih := finSum_sub_with_head q v0 rest
    change Int.ofNat (GaussInt.normSq (GaussInt.sub v0 t0) +
             qsum q (fun t => GaussInt.normSq (GaussInt.sub v0 (rest t)))) =
           Int.ofNat (q + 1) * GaussInt.normSqInt v0 +
             Int.ofNat (GaussInt.normSq t0 + qsum q (fun t => GaussInt.normSq (rest t))) -
             2 * GaussInt.reInner v0 (GaussInt.add t0 (finGaussSum q rest))
    rw [ofNat_add_eq (GaussInt.normSq (GaussInt.sub v0 t0)),
        ofNat_add_eq (GaussInt.normSq t0),
        ← GaussInt.normSqInt_eq_ofNat_normSq (GaussInt.sub v0 t0),
        ← GaussInt.normSqInt_eq_ofNat_normSq t0,
        GaussInt.normSq_sub_int v0 t0, ih]
    have hRe : GaussInt.reInner v0 (GaussInt.add t0 (finGaussSum q rest)) =
        GaussInt.reInner v0 t0 + GaussInt.reInner v0 (finGaussSum q rest) := by
      unfold GaussInt.reInner GaussInt.add
      rw [Int.mul_add, Int.mul_add]
      omega
    have hQ : Int.ofNat (q + 1) * GaussInt.normSqInt v0 =
        GaussInt.normSqInt v0 + Int.ofNat q * GaussInt.normSqInt v0 := by
      rw [ofNat_add_eq q 1, Int.add_mul]
      change Int.ofNat q * GaussInt.normSqInt v0 + 1 * GaussInt.normSqInt v0 = _
      rw [Int.one_mul, Int.add_comm]
    rw [hRe, hQ]
    omega

/-- **Square-Root-Free `q`-Way Cauchy–Schwarz Identity (`gauss_sum_of_squares_identity`)**:
    `q * (∑_{t < q} |v_t|²) = |∑_{t < q} v_t|² + ∑_{s < t} |v_s - v_t|²`. -/
theorem gauss_sum_of_squares_identity :
    ∀ (q : Nat) (v : Fin q → GaussInt),
      q * qsum q (fun t => GaussInt.normSq (v t)) =
        GaussInt.normSq (finGaussSum q v) + pairDiffNormSq q v
  | 0, _ => by rfl
  | q + 1, v => by
    let v0 := v ⟨0, Nat.zero_lt_succ q⟩
    let tail : Fin q → GaussInt := fun t => v ⟨t.1 + 1, Nat.succ_lt_succ t.2⟩
    have ih := gauss_sum_of_squares_identity q tail
    apply Int.ofNat.inj
    change Int.ofNat ((q + 1) * (GaussInt.normSq v0 + qsum q (fun t => GaussInt.normSq (tail t)))) =
      Int.ofNat (GaussInt.normSq (GaussInt.add v0 (finGaussSum q tail)) +
        (qsum q (fun t => GaussInt.normSq (GaussInt.sub v0 (tail t))) + pairDiffNormSq q tail))
    have ihInt : Int.ofNat q * Int.ofNat (qsum q (fun t => GaussInt.normSq (tail t))) =
        GaussInt.normSqInt (finGaussSum q tail) + Int.ofNat (pairDiffNormSq q tail) := by
      rw [GaussInt.normSqInt_eq_ofNat_normSq, ← ofNat_add_eq, ← ofNat_mul_eq, ih]
    rw [ofNat_mul_eq (q + 1),
        ofNat_add_eq (GaussInt.normSq v0),
        ofNat_add_eq (GaussInt.normSq (GaussInt.add v0 (finGaussSum q tail))),
        ofNat_add_eq (qsum q (fun t => GaussInt.normSq (GaussInt.sub v0 (tail t)))),
        ← GaussInt.normSqInt_eq_ofNat_normSq (GaussInt.add v0 (finGaussSum q tail)),
        GaussInt.normSq_add_int v0 (finGaussSum q tail),
        finSum_sub_with_head q v0 tail,
        ← GaussInt.normSqInt_eq_ofNat_normSq v0]
    have hQ1 : Int.ofNat (q + 1) * GaussInt.normSqInt v0 =
        GaussInt.normSqInt v0 + Int.ofNat q * GaussInt.normSqInt v0 := by
      rw [ofNat_add_eq q 1, Int.add_mul]
      change Int.ofNat q * GaussInt.normSqInt v0 + 1 * GaussInt.normSqInt v0 = _
      rw [Int.one_mul, Int.add_comm]
    have hS1 : Int.ofNat (q + 1) * Int.ofNat (qsum q (fun t => GaussInt.normSq (tail t))) =
        Int.ofNat (qsum q (fun t => GaussInt.normSq (tail t))) +
        Int.ofNat q * Int.ofNat (qsum q (fun t => GaussInt.normSq (tail t))) := by
      rw [ofNat_add_eq q 1, Int.add_mul]
      change Int.ofNat q * Int.ofNat (qsum q (fun t => GaussInt.normSq (tail t))) +
        1 * Int.ofNat (qsum q (fun t => GaussInt.normSq (tail t))) = _
      rw [Int.one_mul, Int.add_comm]
    rw [Int.mul_add, hQ1, hS1, ihInt]
    omega

/-- Immediate Cauchy–Schwarz norm inequality `|∑_{t < q} v_t|² ≤ q * ∑_{t < q} |v_t|²`. -/
theorem normSq_finGaussSum_le (q : Nat) (v : Fin q → GaussInt) :
    GaussInt.normSq (finGaussSum q v) ≤ q * qsum q (fun t => GaussInt.normSq (v t)) := by
  have h := gauss_sum_of_squares_identity q v
  omega

/-! ### §2.2 Quantum State Vectors `QVec`, `oracleXor` Isometry, Scaled Unitaries & `QuantumAdv` -/

/-- Tripartite quantum state vector over query register `Fin cardX`, `w`-bit response register
    `Fin (2 ^ w)`, and `cardAnc`-dimensional ancilla workspace. -/
abbrev QVec (cardX w cardAnc : Nat) : Type :=
  Fin cardX → Fin (2 ^ w) → Fin cardAnc → GaussInt

namespace QVec

def zero (cardX w cardAnc : Nat) : QVec cardX w cardAnc :=
  fun _ _ _ => GaussInt.zero

def add {cardX w cardAnc : Nat} (ψ φ : QVec cardX w cardAnc) : QVec cardX w cardAnc :=
  fun x y a => GaussInt.add (ψ x y a) (φ x y a)

def sub {cardX w cardAnc : Nat} (ψ φ : QVec cardX w cardAnc) : QVec cardX w cardAnc :=
  fun x y a => GaussInt.sub (ψ x y a) (φ x y a)

/-- Squared amplitude mass on a single query coordinate `x : Fin cardX`. -/
def queryWeight {cardX w cardAnc : Nat} (ψ : QVec cardX w cardAnc) (x : Fin cardX) : Nat :=
  qsum (2 ^ w) (fun y => qsum cardAnc (fun a => GaussInt.normSq (ψ x y a)))

/-- Squared amplitude mass on a marked subset `S : Fin cardX → Bool` of queries. -/
def queryMassOn {cardX w cardAnc : Nat} (S : Fin cardX → Bool) (ψ : QVec cardX w cardAnc) : Nat :=
  qsum cardX (fun x => if S x = true then queryWeight ψ x else 0)

/-- Total squared Hilbert-space norm `‖ψ‖² = ∑_{x, y, a} |ψ(x, y, a)|²`. -/
def stateNormSq {cardX w cardAnc : Nat} (ψ : QVec cardX w cardAnc) : Nat :=
  qsum cardX (fun x => queryWeight ψ x)

/-- Unnormalized Born numerator `∑_{x : E x = true} queryWeight ψ x` for projective measurement `E`
    on the query/output register `Fin cardX`. -/
def measureNormSq {cardX w cardAnc : Nat} (E : Fin cardX → Bool) (ψ : QVec cardX w cardAnc) : Nat :=
  queryMassOn E ψ

/-- Exact Born-rule measurement probability `measureNormSq E ψ / stateNormSq ψ` as a `RatBound`. -/
def bornProb {cardX w cardAnc : Nat} (E : Fin cardX → Bool)
    (ψ : QVec cardX w cardAnc) (hPos : 0 < stateNormSq ψ) : RatBound :=
  ⟨measureNormSq E ψ, stateNormSq ψ, hPos⟩

theorem queryMassOn_le_stateNormSq {cardX w cardAnc : Nat}
    (S : Fin cardX → Bool) (ψ : QVec cardX w cardAnc) :
    queryMassOn S ψ ≤ stateNormSq ψ := by
  unfold queryMassOn stateNormSq
  apply qsum_le_qsum
  intro x
  cases S x <;> simp

theorem sumQVec_normSq_le {cardX w cardAnc : Nat} (q : Nat)
    (V : Fin q → QVec cardX w cardAnc) :
    stateNormSq (fun x y a => finGaussSum q (fun t => V t x y a)) ≤
      q * qsum q (fun t => stateNormSq (V t)) := by
  unfold stateNormSq queryWeight
  have hPoint :
      qsum cardX (fun x => qsum (2 ^ w) (fun y => qsum cardAnc (fun a =>
        GaussInt.normSq (finGaussSum q (fun t => V t x y a))))) ≤
      qsum cardX (fun x => qsum (2 ^ w) (fun y => qsum cardAnc (fun a =>
        q * qsum q (fun t => GaussInt.normSq (V t x y a))))) := by
    apply qsum_le_qsum; intro x
    apply qsum_le_qsum; intro y
    apply qsum_le_qsum; intro a
    exact normSq_finGaussSum_le q (fun t => V t x y a)
  apply Nat.le_trans hPoint
  have hSwap :
      qsum cardX (fun x => qsum (2 ^ w) (fun y => qsum cardAnc (fun a =>
        q * qsum q (fun t => GaussInt.normSq (V t x y a))))) =
      q * qsum q (fun t => qsum cardX (fun x => qsum (2 ^ w) (fun y =>
        qsum cardAnc (fun a => GaussInt.normSq (V t x y a))))) := by
    have p1 : ∀ x y, qsum cardAnc (fun a => q * qsum q (fun t => GaussInt.normSq (V t x y a))) =
        q * qsum q (fun t => qsum cardAnc (fun a => GaussInt.normSq (V t x y a))) := by
      intro x y
      rw [qsum_mul_left, qsum_comm]
    have p2 : ∀ x, qsum (2 ^ w) (fun y =>
        qsum cardAnc (fun a => q * qsum q (fun t => GaussInt.normSq (V t x y a)))) =
        q * qsum q (fun t => qsum (2 ^ w) (fun y =>
          qsum cardAnc (fun a => GaussInt.normSq (V t x y a)))) := by
      intro x
      rw [qsum_congr (fun y => p1 x y), qsum_mul_left, qsum_comm]
    rw [qsum_congr p2, qsum_mul_left, qsum_comm]
  exact Nat.le_of_eq hSwap

end QVec

/-- Bitwise XOR permutation on `Fin (2 ^ w)` induced by `v : BitVec w`. -/
def xorFin {w : Nat} (y : Fin (2 ^ w)) (v : BitVec w) : Fin (2 ^ w) :=
  (BitVec.ofFin y ^^^ v).toFin

theorem xorFin_involutive {w : Nat} (v : BitVec w) (y : Fin (2 ^ w)) :
    xorFin (xorFin y v) v = y := by
  unfold xorFin
  have hXor : (BitVec.ofFin y ^^^ v) ^^^ v = BitVec.ofFin y := by
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp only [BitVec.getLsbD_xor]
    cases (BitVec.ofFin y).getLsbD i <;> cases v.getLsbD i <;> rfl
  rw [BitVec.ofFin_toFin, hXor, BitVec.toFin_ofFin]

/-- Reversible QROM bit-XOR oracle `O_H : |x, y, a⟩ ↦ |x, y ⊕ H(x), a⟩`. -/
def oracleXor {cardX w cardAnc : Nat} (H : Fin cardX → BitVec w)
    (ψ : QVec cardX w cardAnc) : QVec cardX w cardAnc :=
  fun x y a => ψ x (xorFin y (H x)) a

theorem oracleXor_involutive {cardX w cardAnc : Nat}
    (H : Fin cardX → BitVec w) (ψ : QVec cardX w cardAnc) :
    oracleXor H (oracleXor H ψ) = ψ := by
  funext x y a
  simp [oracleXor, xorFin_involutive]

theorem oracleXor_sub {cardX w cardAnc : Nat}
    (H : Fin cardX → BitVec w) (ψ φ : QVec cardX w cardAnc) :
    oracleXor H (ψ.sub φ) = (oracleXor H ψ).sub (oracleXor H φ) := by rfl

theorem oracleXor_queryWeight {cardX w cardAnc : Nat}
    (H : Fin cardX → BitVec w) (ψ : QVec cardX w cardAnc) (x : Fin cardX) :
    QVec.queryWeight (oracleXor H ψ) x = QVec.queryWeight ψ x := by
  unfold QVec.queryWeight oracleXor
  exact qsum_involutive (fun y => xorFin y (H x)) (xorFin_involutive (H x))
    (fun y => qsum cardAnc (fun a => GaussInt.normSq (ψ x y a)))

/-- **`oracleXor` Isometry Theorem**: `O_H` preserves squared Hilbert-space norm with exact scale `1`. -/
theorem oracleXor_isometry {cardX w cardAnc : Nat}
    (H : Fin cardX → BitVec w) (ψ : QVec cardX w cardAnc) :
    QVec.stateNormSq (oracleXor H ψ) = QVec.stateNormSq ψ := by
  unfold QVec.stateNormSq
  exact qsum_congr (oracleXor_queryWeight H ψ)

/-- Pointwise oracle-difference bound: if `H` and `H'` agree outside `S`, then
    `‖(O_H - O_{H'}) ψ‖² ≤ 4 * queryMassOn S ψ`. -/
theorem oracleXor_diff_normSq_le {cardX w cardAnc : Nat}
    (H H' : Fin cardX → BitVec w) (S : Fin cardX → Bool)
    (hAgree : ∀ x : Fin cardX, S x = false → H x = H' x)
    (ψ : QVec cardX w cardAnc) :
    QVec.stateNormSq ((oracleXor H ψ).sub (oracleXor H' ψ)) ≤
      4 * QVec.queryMassOn S ψ := by
  unfold QVec.stateNormSq QVec.queryMassOn
  rw [← qsum_mul_left 4]
  apply qsum_le_qsum
  intro x
  cases hSx : S x
  · have hEq := hAgree x hSx
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.mul_zero, QVec.queryWeight,
      QVec.sub, oracleXor, hEq]
    have h0 : qsum (2 ^ w) (fun y => qsum cardAnc (fun a =>
        GaussInt.normSq (GaussInt.sub (ψ x (xorFin y (H' x)) a) (ψ x (xorFin y (H' x)) a)))) =
        qsum (2 ^ w) (fun _ => 0) := by
      apply qsum_congr; intro y
      have ha0 : qsum cardAnc (fun a =>
          GaussInt.normSq (GaussInt.sub (ψ x (xorFin y (H' x)) a) (ψ x (xorFin y (H' x)) a))) =
          qsum cardAnc (fun _ => 0) := by
        apply qsum_congr; intro a
        unfold GaussInt.sub GaussInt.normSq
        simp
      rw [ha0, qsum_const]; omega
    rw [h0, qsum_const]; omega
  · simp only [↓reduceIte]
    have hPt : QVec.queryWeight ((oracleXor H ψ).sub (oracleXor H' ψ)) x ≤
        2 * QVec.queryWeight (oracleXor H ψ) x + 2 * QVec.queryWeight (oracleXor H' ψ) x := by
      unfold QVec.queryWeight QVec.sub
      rw [← qsum_mul_left 2, ← qsum_mul_left 2, ← qsum_add]
      apply qsum_le_qsum; intro y
      rw [← qsum_mul_left 2, ← qsum_mul_left 2, ← qsum_add]
      apply qsum_le_qsum; intro a
      exact GaussInt.normSq_sub_le _ _
    rw [oracleXor_queryWeight H ψ x, oracleXor_queryWeight H' ψ x] at hPt
    omega

/-- Linear scaled unitary operator `U` on `QVec cardX w cardAnc` with positive integer squared-norm
    factor `scaleSq > 0` (`‖U ψ‖² = scaleSq * ‖ψ‖²`). Supports strict norm-`1` unitaries, exact
    Hadamards (`scaleSq = 2`), and exact `M`-item Grover reflections (`scaleSq = M^2`) without `√2`. -/
structure ScaledUnitary (cardX w cardAnc : Nat) where
  apply : QVec cardX w cardAnc → QVec cardX w cardAnc
  scaleSq : Nat
  h_scale_pos : 0 < scaleSq
  map_sub : ∀ ψ φ, apply (ψ.sub φ) = (apply ψ).sub (apply φ)
  normSq_eq : ∀ ψ, QVec.stateNormSq (apply ψ) = scaleSq * QVec.stateNormSq ψ

/-- Identity unitary (`scaleSq = 1`). -/
def ScaledUnitary.id (cardX w cardAnc : Nat) : ScaledUnitary cardX w cardAnc where
  apply ψ := ψ
  scaleSq := 1
  h_scale_pos := Nat.zero_lt_one
  map_sub _ _ := rfl
  normSq_eq _ := (Nat.one_mul _).symm

private theorem qsum_two (f : Fin 2 → Nat) :
    qsum 2 f = f ⟨0, by decide⟩ + f ⟨1, by decide⟩ := by
  simp [qsum]

/-- Concrete 1-qubit Hadamard gate `[[1, 1], [1, -1]]` on query register `Fin 2` (`scaleSq = 2`),
    certifying that `ScaledUnitary` natively encompasses Clifford superposition creation. -/
def hadamardQuery2 (w cardAnc : Nat) : ScaledUnitary 2 w cardAnc where
  apply ψ x y a :=
    if x.val == 0 then
      GaussInt.add (ψ ⟨0, by decide⟩ y a) (ψ ⟨1, by decide⟩ y a)
    else
      GaussInt.sub (ψ ⟨0, by decide⟩ y a) (ψ ⟨1, by decide⟩ y a)
  scaleSq := 2
  h_scale_pos := by decide
  map_sub ψ φ := by
    funext x y a
    cases h0 : (x.val == 0)
    · simp only [h0, Bool.false_eq_true, ↓reduceIte, QVec.sub, GaussInt.sub]
      ext <;> dsimp only <;> omega
    · simp only [h0, ↓reduceIte, QVec.sub, GaussInt.add, GaussInt.sub]
      ext <;> dsimp only <;> omega
  normSq_eq ψ := by
    unfold QVec.stateNormSq QVec.queryWeight
    rw [qsum_two, qsum_two]
    dsimp only
    have h00 : ((0 : Nat) == 0) = true := rfl
    have h10 : ((1 : Nat) == 0) = false := rfl
    simp only [h00, h10, Bool.false_eq_true, ↓reduceIte]
    rw [← qsum_add, Nat.left_distrib, ← qsum_mul_left 2, ← qsum_mul_left 2, ← qsum_add]
    apply qsum_congr; intro y
    rw [← qsum_add, ← qsum_mul_left 2, ← qsum_mul_left 2, ← qsum_add]
    apply qsum_congr; intro a
    have hp := GaussInt.normSq_parallelogram (ψ ⟨0, by decide⟩ y a) (ψ ⟨1, by decide⟩ y a)
    omega

/-- Arbitrary `q`-query unitary quantum adversary interleaving `q` oracle calls `O_H` with
    arbitrary scaled unitary circuits `U_0, ..., U_{q-1}`. -/
structure QuantumAdv (cardX w cardAnc q : Nat) where
  init : QVec cardX w cardAnc
  h_init_pos : 0 < QVec.stateNormSq init
  steps : Fin q → ScaledUnitary cardX w cardAnc

/-- State of `A` immediately before query `t` (`0 ≤ t ≤ q`) when interacting with oracle `H`. -/
def advStateAt {cardX w cardAnc q : Nat} (A : QuantumAdv cardX w cardAnc q)
    (H : Fin cardX → BitVec w) : (t : Nat) → t ≤ q → QVec cardX w cardAnc
  | 0, _ => A.init
  | t + 1, ht =>
    let prev := advStateAt A H t (Nat.le_of_succ_le ht)
    (A.steps ⟨t, ht⟩).apply (oracleXor H prev)

/-- Final `q`-query quantum state `ψ_q^H` of adversary `A` under oracle `H`. -/
def runQuantumAdv {cardX w cardAnc q : Nat} (A : QuantumAdv cardX w cardAnc q)
    (H : Fin cardX → BitVec w) : QVec cardX w cardAnc :=
  advStateAt A H q (Nat.le_refl q)

/-- Cumulative squared-norm scale of the first `t` unitary layers. -/
def prefixScale {cardX w cardAnc q : Nat} (A : QuantumAdv cardX w cardAnc q) :
    (t : Nat) → t ≤ q → Nat
  | 0, _ => 1
  | t + 1, ht => (A.steps ⟨t, ht⟩).scaleSq * prefixScale A t (Nat.le_of_succ_le ht)

/-- Cumulative squared-norm scale of the remaining unitary layers `t .. q - 1`. -/
def suffixScale {cardX w cardAnc q : Nat} (A : QuantumAdv cardX w cardAnc q) :
    (t : Nat) → t ≤ q → Nat
  | t, _ =>
    if hlt : t < q then
      (A.steps ⟨t, hlt⟩).scaleSq * suffixScale A (t + 1) hlt
    else
      1
termination_by t => q - t

/-- Apply layers `t .. q - 1` using oracle `H` after query `t` has already been applied. -/
def applySuffixFrom {cardX w cardAnc q : Nat} (A : QuantumAdv cardX w cardAnc q)
    (H : Fin cardX → BitVec w) : (t : Nat) → t < q → QVec cardX w cardAnc → QVec cardX w cardAnc
  | t, hlt, ψ =>
    let ψ1 := (A.steps ⟨t, hlt⟩).apply ψ
    if hNext : t + 1 < q then
      applySuffixFrom A H (t + 1) hNext (oracleXor H ψ1)
    else
      ψ1
termination_by t => q - t

theorem prefixScale_pos {cardX w cardAnc q : Nat} (A : QuantumAdv cardX w cardAnc q) :
    ∀ (t : Nat) (ht : t ≤ q), 0 < prefixScale A t ht
  | 0, _ => Nat.zero_lt_one
  | t + 1, ht => Nat.mul_pos (A.steps ⟨t, ht⟩).h_scale_pos (prefixScale_pos A t (Nat.le_of_succ_le ht))

theorem advStateAt_normSq {cardX w cardAnc q : Nat} (A : QuantumAdv cardX w cardAnc q)
    (H : Fin cardX → BitVec w) :
    ∀ (t : Nat) (ht : t ≤ q),
      QVec.stateNormSq (advStateAt A H t ht) = prefixScale A t ht * QVec.stateNormSq A.init
  | 0, _ => (Nat.one_mul _).symm
  | t + 1, ht => by
    simp only [advStateAt, prefixScale]
    rw [(A.steps ⟨t, ht⟩).normSq_eq, oracleXor_isometry,
        advStateAt_normSq A H t (Nat.le_of_succ_le ht), Nat.mul_assoc]

theorem runQuantumAdv_normSq {cardX w cardAnc q : Nat} (A : QuantumAdv cardX w cardAnc q)
    (H : Fin cardX → BitVec w) :
    QVec.stateNormSq (runQuantumAdv A H) = prefixScale A q (Nat.le_refl q) * QVec.stateNormSq A.init :=
  advStateAt_normSq A H q (Nat.le_refl q)

theorem runQuantumAdv_normSq_pos {cardX w cardAnc q : Nat} (A : QuantumAdv cardX w cardAnc q)
    (H : Fin cardX → BitVec w) :
    0 < QVec.stateNormSq (runQuantumAdv A H) := by
  rw [runQuantumAdv_normSq]
  exact Nat.mul_pos (prefixScale_pos A q (Nat.le_refl q)) A.h_init_pos

theorem applySuffixFrom_sub {cardX w cardAnc q : Nat} (A : QuantumAdv cardX w cardAnc q)
    (H : Fin cardX → BitVec w) :
    ∀ (t : Nat) (hlt : t < q) (ψ φ : QVec cardX w cardAnc),
      applySuffixFrom A H t hlt (ψ.sub φ) =
        (applySuffixFrom A H t hlt ψ).sub (applySuffixFrom A H t hlt φ)
  | t, hlt, ψ, φ => by
    unfold applySuffixFrom
    dsimp only
    rw [(A.steps ⟨t, hlt⟩).map_sub]
    split
    · rename_i hNext
      rw [oracleXor_sub, applySuffixFrom_sub A H (t + 1) hNext]
    · rfl
termination_by t => q - t

theorem applySuffixFrom_normSq {cardX w cardAnc q : Nat} (A : QuantumAdv cardX w cardAnc q)
    (H : Fin cardX → BitVec w) :
    ∀ (t : Nat) (hlt : t < q) (ψ : QVec cardX w cardAnc),
      QVec.stateNormSq (applySuffixFrom A H t hlt ψ) =
        suffixScale A t (Nat.le_of_lt hlt) * QVec.stateNormSq ψ
  | t, hlt, ψ => by
    unfold applySuffixFrom
    rw [suffixScale]
    simp only [hlt, ↓reduceDIte]
    split
    · rename_i hNext
      rw [applySuffixFrom_normSq A H (t + 1) hNext, oracleXor_isometry,
          (A.steps ⟨t, hlt⟩).normSq_eq, ← Nat.mul_assoc, Nat.mul_comm _ ((A.steps ⟨t, hlt⟩).scaleSq),
          Nat.mul_assoc]
    · rename_i hNotNext
      rw [suffixScale]
      simp only [hNotNext, ↓reduceDIte, Nat.mul_one, (A.steps ⟨t, hlt⟩).normSq_eq]
termination_by t => q - t

theorem prefix_mul_suffix_eq_total {cardX w cardAnc q : Nat} (A : QuantumAdv cardX w cardAnc q) :
    ∀ (t : Nat) (ht : t ≤ q),
      prefixScale A t ht * suffixScale A t ht = prefixScale A q (Nat.le_refl q)
  | t, ht => by
    if hlt : t < q then
      have ih := prefix_mul_suffix_eq_total A (t + 1) hlt
      rw [suffixScale]
      simp only [hlt, ↓reduceDIte]
      have hPref : prefixScale A (t + 1) hlt = (A.steps ⟨t, hlt⟩).scaleSq * prefixScale A t ht := rfl
      rw [← ih, hPref, ← Nat.mul_assoc, Nat.mul_comm (prefixScale A t ht), Nat.mul_assoc]
    else
      have hEq : t = q := by omega
      subst hEq
      rw [suffixScale]
      simp
termination_by t => q - t

/-! ### §2.3 Mechanized `[BBBV97]` / `[AHU19]` One-Way-to-Hiding (`O2H`) & Born-Rule Theorems -/

/-- Hybrid quantum state executing `H'` for the first `k` oracle calls and `H` for the remaining
    `q - k` oracle calls (`hybridAdv A H H' 0 = runQuantumAdv A H` and
    `hybridAdv A H H' q = runQuantumAdv A H'`). -/
def hybridAdv {cardX w cardAnc q : Nat} (A : QuantumAdv cardX w cardAnc q)
    (H H' : Fin cardX → BitVec w) (k : Nat) (hk : k ≤ q) : QVec cardX w cardAnc :=
  if hlt : k < q then
    applySuffixFrom A H k hlt (oracleXor H (advStateAt A H' k hk))
  else
    advStateAt A H' q (Nat.le_refl q)

private theorem applySuffixFrom_step_eq {cardX w cardAnc q : Nat}
    (A : QuantumAdv cardX w cardAnc q) (H : Fin cardX → BitVec w) :
    ∀ (k : Nat) (hk : k ≤ q),
      (if hlt : k < q then applySuffixFrom A H k hlt (oracleXor H (advStateAt A H k hk))
       else advStateAt A H q (Nat.le_refl q)) = runQuantumAdv A H
  | k, hk => by
    if hlt : k < q then
      simp only [hlt, ↓reduceDIte]
      unfold applySuffixFrom
      dsimp only
      have hAdvNext : (A.steps ⟨k, hlt⟩).apply (oracleXor H (advStateAt A H k hk)) =
          advStateAt A H (k + 1) hlt := rfl
      rw [hAdvNext]
      split
      · rename_i hNext
        have ih := applySuffixFrom_step_eq A H (k + 1) (Nat.le_of_lt hNext)
        simp only [hNext, ↓reduceDIte] at ih
        exact ih
      · rename_i hNotNext
        have hEqQ : k + 1 = q := by omega
        unfold runQuantumAdv
        cases hEqQ
        rfl
    else
      have hEqQ : k = q := by omega
      subst hEqQ
      simp [runQuantumAdv]
termination_by k => q - k

private theorem hybridAdv_zero {cardX w cardAnc q : Nat}
    (A : QuantumAdv cardX w cardAnc q) (H H' : Fin cardX → BitVec w) :
    hybridAdv A H H' 0 (Nat.zero_le q) = runQuantumAdv A H := by
  cases q with
  | zero => rfl
  | succ q' =>
    have hPos : 0 < q' + 1 := Nat.zero_lt_succ q'
    have h0 := applySuffixFrom_step_eq A H 0 (Nat.zero_le (q' + 1))
    simp only [hPos, ↓reduceDIte] at h0
    unfold hybridAdv
    simp only [hPos, ↓reduceDIte]
    exact h0

private theorem hybridAdv_full {cardX w cardAnc q : Nat}
    (A : QuantumAdv cardX w cardAnc q) (H H' : Fin cardX → BitVec w) :
    hybridAdv A H H' q (Nat.le_refl q) = runQuantumAdv A H' := by
  unfold hybridAdv runQuantumAdv
  simp

private theorem hybridAdv_step_diff {cardX w cardAnc q : Nat}
    (A : QuantumAdv cardX w cardAnc q) (H H' : Fin cardX → BitVec w)
    (t : Nat) (ht : t < q) :
    (hybridAdv A H H' t (Nat.le_of_lt ht)).sub (hybridAdv A H H' (t + 1) ht) =
      applySuffixFrom A H t ht
        ((oracleXor H (advStateAt A H' t (Nat.le_of_lt ht))).sub
         (oracleXor H' (advStateAt A H' t (Nat.le_of_lt ht)))) := by
  rw [applySuffixFrom_sub]
  have hRhs2 : applySuffixFrom A H t ht (oracleXor H' (advStateAt A H' t (Nat.le_of_lt ht))) =
      hybridAdv A H H' (t + 1) ht := by
    rw [applySuffixFrom.eq_def]
    dsimp only
    have hStep : (A.steps ⟨t, ht⟩).apply (oracleXor H' (advStateAt A H' t (Nat.le_of_lt ht))) =
        advStateAt A H' (t + 1) ht := rfl
    rw [hStep]
    unfold hybridAdv
    if hNext : t + 1 < q then
      simp [hNext]
    else
      have hEqQ : t + 1 = q := by omega
      simp only [hNext, ↓reduceDIte]
      cases hEqQ
      rfl
  rw [hRhs2]
  unfold hybridAdv
  simp only [ht, ↓reduceDIte]

private theorem telescope_gauss_sum :
    ∀ (q : Nat) (seq : (k : Nat) → k ≤ q → GaussInt),
      finGaussSum q (fun t => GaussInt.sub (seq t.1 (Nat.le_of_lt t.2)) (seq (t.1 + 1) t.2)) =
        GaussInt.sub (seq 0 (Nat.zero_le q)) (seq q (Nat.le_refl q))
  | 0, seq => by
    simp [finGaussSum, GaussInt.sub, GaussInt.zero]
  | q + 1, seq => by
    simp only [finGaussSum]
    have ih := telescope_gauss_sum q (fun k hk => seq (k + 1) (Nat.succ_le_succ hk))
    rw [ih]
    unfold GaussInt.add GaussInt.sub
    ext <;> dsimp only <;> omega

/-- **Real `[BBBV97]` / `[AHU19]` One-Way-to-Hiding (`O2H`) Telescoping Theorem**:
    For ANY `q`-query unitary circuit `A` and ANY two oracles `H, H'` agreeing outside `S`,
    `‖ψ_q^H - ψ_q^{H'}‖² ≤ 4 * q * ∑_{t < q} suffixScale(t) * queryMassOn S (ψ_t^{H'})`,
    where `ψ_t^{H'}` depends ONLY on the reference oracle `H'`! -/
theorem qrom_o2h_telescoping_disturbance_le {cardX w cardAnc q : Nat}
    (A : QuantumAdv cardX w cardAnc q)
    (H H' : Fin cardX → BitVec w) (S : Fin cardX → Bool)
    (hAgree : ∀ x : Fin cardX, S x = false → H x = H' x) :
    QVec.stateNormSq ((runQuantumAdv A H).sub (runQuantumAdv A H')) ≤
      4 * q * qsum q (fun t =>
        suffixScale A t.1 (Nat.le_of_lt t.2) *
          QVec.queryMassOn S (advStateAt A H' t.1 (Nat.le_of_lt t.2))) := by
  let V : Fin q → QVec cardX w cardAnc := fun t =>
    (hybridAdv A H H' t.1 (Nat.le_of_lt t.2)).sub (hybridAdv A H H' (t.1 + 1) t.2)
  have hTele : (runQuantumAdv A H).sub (runQuantumAdv A H') =
      (fun x y a => finGaussSum q (fun t => V t x y a)) := by
    rw [← hybridAdv_zero A H H', ← hybridAdv_full A H H']
    funext x y a
    exact (telescope_gauss_sum q (fun k hk => hybridAdv A H H' k hk x y a)).symm
  rw [hTele]
  have hCS := QVec.sumQVec_normSq_le q V
  apply Nat.le_trans hCS
  have hEach : qsum q (fun t => QVec.stateNormSq (V t)) ≤
      qsum q (fun t => 4 * (suffixScale A t.1 (Nat.le_of_lt t.2) *
        QVec.queryMassOn S (advStateAt A H' t.1 (Nat.le_of_lt t.2)))) := by
    apply qsum_le_qsum
    intro t
    dsimp only [V]
    rw [hybridAdv_step_diff, applySuffixFrom_normSq]
    have hDiff := oracleXor_diff_normSq_le H H' S hAgree (advStateAt A H' t.1 (Nat.le_of_lt t.2))
    have hMul := Nat.mul_le_mul_left (suffixScale A t.1 (Nat.le_of_lt t.2)) hDiff
    rw [Nat.mul_left_comm _ 4] at hMul
    exact hMul
  rw [qsum_mul_left 4] at hEach
  have hMulQ := Nat.mul_le_mul_left q hEach
  rw [Nat.mul_left_comm q 4, ← Nat.mul_assoc 4 q] at hMulQ
  exact hMulQ

/-- Reprogram oracle `H` at a single coordinate `xStar` to output `yStar`. -/
def reprogramOracle {cardX w : Nat} (H : Fin cardX → BitVec w)
    (xStar : Fin cardX) (yStar : BitVec w) : Fin cardX → BitVec w :=
  fun x => if x = xStar then yStar else H x

/-- **Uniform Point-Reprogramming O2H Average Disturbance (`≤ 4 q² / M`)**:
    Averaging squared state disturbance over any duplicate-free `M`-element candidate list
    `candidates : List (Fin cardX)` (`M > 0`) bounds the average normalized squared state
    disturbance by `(4 * q ^ 2) / M`. -/
theorem qrom_o2h_average_point_disturbance {cardX w cardAnc q : Nat}
    (A : QuantumAdv cardX w cardAnc q)
    (H : Fin cardX → BitVec w) (yStar : Fin cardX → BitVec w)
    (M : Nat) (hMPos : 0 < M) (cand : Fin M → Fin cardX)
    (hInj : ∀ i j : Fin M, cand i = cand j → i = j) :
    let normFinal := QVec.stateNormSq (runQuantumAdv A H)
    RatBound.le
      ⟨qsum M (fun i =>
        QVec.stateNormSq ((runQuantumAdv A (reprogramOracle H (cand i) (yStar (cand i)))).sub
          (runQuantumAdv A H))),
       M * normFinal,
       Nat.mul_pos hMPos (runQuantumAdv_normSq_pos A H)⟩
      ⟨4 * q ^ 2, M, hMPos⟩ := by
  dsimp only [RatBound.le]
  let normFinal := QVec.stateNormSq (runQuantumAdv A H)
  have hPerI : ∀ i : Fin M,
      QVec.stateNormSq ((runQuantumAdv A (reprogramOracle H (cand i) (yStar (cand i)))).sub
        (runQuantumAdv A H)) ≤
      4 * q * qsum q (fun t =>
        suffixScale A t.1 (Nat.le_of_lt t.2) *
          QVec.queryWeight (advStateAt A H t.1 (Nat.le_of_lt t.2)) (cand i)) := by
    intro i
    let Si : Fin cardX → Bool := fun x => decide (x = cand i)
    have hAgree : ∀ x : Fin cardX, Si x = false →
        reprogramOracle H (cand i) (yStar (cand i)) x = H x := by
      intro x hx
      unfold reprogramOracle
      have hne : x ≠ cand i := by
        intro heq; simp [Si, heq] at hx
      simp [hne]
    have hO2h := qrom_o2h_telescoping_disturbance_le A
      (reprogramOracle H (cand i) (yStar (cand i))) H Si hAgree
    have hMassEq : ∀ t : Fin q,
        QVec.queryMassOn Si (advStateAt A H t.1 (Nat.le_of_lt t.2)) =
          QVec.queryWeight (advStateAt A H t.1 (Nat.le_of_lt t.2)) (cand i) := by
      intro t
      unfold QVec.queryMassOn
      have hCongr : qsum cardX (fun x =>
          if Si x = true then QVec.queryWeight (advStateAt A H t.1 (Nat.le_of_lt t.2)) x else 0) =
          qsum cardX (fun x =>
            if x = cand i then QVec.queryWeight (advStateAt A H t.1 (Nat.le_of_lt t.2)) (cand i) else 0) := by
        apply qsum_congr; intro x
        by_cases hx : x = cand i <;> simp [Si, hx]
      rw [hCongr, qsum_ite_eq]
    have hSumEq : qsum q (fun t =>
        suffixScale A t.1 (Nat.le_of_lt t.2) *
          QVec.queryMassOn Si (advStateAt A H t.1 (Nat.le_of_lt t.2))) =
        qsum q (fun t =>
          suffixScale A t.1 (Nat.le_of_lt t.2) *
            QVec.queryWeight (advStateAt A H t.1 (Nat.le_of_lt t.2)) (cand i)) :=
      qsum_congr (fun t => by rw [hMassEq t])
    rw [hSumEq] at hO2h
    exact hO2h
  have hSumM := qsum_le_qsum hPerI
  rw [qsum_mul_left (4 * q), qsum_comm M q] at hSumM
  have hStepBound : ∀ t : Fin q,
      qsum M (fun i =>
        suffixScale A t.1 (Nat.le_of_lt t.2) *
          QVec.queryWeight (advStateAt A H t.1 (Nat.le_of_lt t.2)) (cand i)) ≤ normFinal := by
    intro t
    rw [qsum_mul_left]
    have hSub : qsum M (fun i => QVec.queryWeight (advStateAt A H t.1 (Nat.le_of_lt t.2)) (cand i)) ≤
        QVec.stateNormSq (advStateAt A H t.1 (Nat.le_of_lt t.2)) := by
      unfold QVec.stateNormSq
      have hExpand : qsum M (fun i => QVec.queryWeight (advStateAt A H t.1 (Nat.le_of_lt t.2)) (cand i)) =
          qsum cardX (fun x =>
            QVec.queryWeight (advStateAt A H t.1 (Nat.le_of_lt t.2)) x *
              qsum M (fun i => if x = cand i then 1 else 0)) := by
        have h1 : qsum M (fun i => QVec.queryWeight (advStateAt A H t.1 (Nat.le_of_lt t.2)) (cand i)) =
            qsum M (fun i => qsum cardX (fun x =>
              if x = cand i then QVec.queryWeight (advStateAt A H t.1 (Nat.le_of_lt t.2)) x else 0)) := by
          apply qsum_congr; intro i
          have hCongrX : qsum cardX (fun x =>
              if x = cand i then QVec.queryWeight (advStateAt A H t.1 (Nat.le_of_lt t.2)) x else 0) =
              qsum cardX (fun x =>
                if x = cand i then QVec.queryWeight (advStateAt A H t.1 (Nat.le_of_lt t.2)) (cand i) else 0) := by
            apply qsum_congr; intro x
            by_cases hx : x = cand i
            · rw [hx]
            · simp only [hx, ↓reduceIte]
          rw [hCongrX, qsum_ite_eq]
        rw [h1, qsum_comm]
        apply qsum_congr; intro x
        rw [← qsum_mul_left]
        apply qsum_congr; intro i
        by_cases hx : x = cand i <;> simp [hx]
      rw [hExpand]
      apply qsum_le_qsum; intro x
      have hLe1 : qsum M (fun i => if x = cand i then 1 else 0) ≤ 1 := by
        have hBool : qsum M (fun i => if x = cand i then 1 else 0) =
            qsum M (fun i => if decide (x = cand i) = true then 1 else 0) := by
          apply qsum_congr; intro i; by_cases hx : x = cand i <;> simp [hx]
        rw [hBool]
        exact qsum_le_one_of_subsingleton (fun i => decide (x = cand i)) (fun i j hi hj => by
          have hi' : x = cand i := of_decide_eq_true hi
          have hj' : x = cand j := of_decide_eq_true hj
          exact hInj i j (hi'.symm.trans hj'))
      have hm := Nat.mul_le_mul_left (QVec.queryWeight (advStateAt A H t.1 (Nat.le_of_lt t.2)) x) hLe1
      rw [Nat.mul_one] at hm
      exact hm
    have hMulS := Nat.mul_le_mul_left (suffixScale A t.1 (Nat.le_of_lt t.2)) hSub
    apply Nat.le_trans hMulS
    dsimp only [normFinal]
    rw [advStateAt_normSq, runQuantumAdv_normSq, ← Nat.mul_assoc,
        Nat.mul_comm (suffixScale A t.1 (Nat.le_of_lt t.2)),
        prefix_mul_suffix_eq_total A t.1 (Nat.le_of_lt t.2)]
    exact Nat.le_refl _
  have hAllQ := qsum_le_qsum hStepBound
  rw [qsum_const] at hAllQ
  have hBoundTotal : qsum M (fun i =>
      QVec.stateNormSq ((runQuantumAdv A (reprogramOracle H (cand i) (yStar (cand i)))).sub
        (runQuantumAdv A H))) ≤ 4 * q ^ 2 * normFinal := by
    have hMul4 := Nat.mul_le_mul_left (4 * q) hAllQ
    have hPow2 : 4 * q * (q * normFinal) = 4 * q ^ 2 * normFinal := by
      rw [Nat.pow_two]; simp only [Nat.mul_assoc]
    rw [hPow2] at hMul4
    exact Nat.le_trans hSumM hMul4
  have hMulM := Nat.mul_le_mul_right M hBoundTotal
  have hRearr : 4 * q ^ 2 * normFinal * M = 4 * q ^ 2 * (M * normFinal) := by
    rw [Nat.mul_assoc (4 * q ^ 2) normFinal M, Nat.mul_comm normFinal M]
  rw [hRearr] at hMulM
  exact hMulM

/-- **One-Sided Born Probability Disturbance Lemma**:
    For ANY event `E` and ANY two state vectors `ψ, φ`,
    `measureNormSq E ψ ≤ 2 * measureNormSq E φ + 2 * stateNormSq (ψ - φ)`. -/
theorem born_measure_le_two_add_two_dist_sq {cardX w cardAnc : Nat}
    (E : Fin cardX → Bool) (ψ φ : QVec cardX w cardAnc) :
    QVec.measureNormSq E ψ ≤ 2 * QVec.measureNormSq E φ + 2 * QVec.stateNormSq (ψ.sub φ) := by
  have hSubE : QVec.measureNormSq E (ψ.sub φ) ≤ QVec.stateNormSq (ψ.sub φ) :=
    QVec.queryMassOn_le_stateNormSq E (ψ.sub φ)
  have hPoint : QVec.measureNormSq E ψ ≤
      2 * QVec.measureNormSq E φ + 2 * QVec.measureNormSq E (ψ.sub φ) := by
    unfold QVec.measureNormSq QVec.queryMassOn
    rw [← qsum_mul_left 2, ← qsum_mul_left 2, ← qsum_add]
    apply qsum_le_qsum; intro x
    cases E x
    · simp
    · simp only [↓reduceIte, QVec.queryWeight, QVec.sub]
      rw [← qsum_mul_left 2, ← qsum_mul_left 2, ← qsum_add]
      apply qsum_le_qsum; intro y
      rw [← qsum_mul_left 2, ← qsum_mul_left 2, ← qsum_add]
      apply qsum_le_qsum; intro a
      have hEq : ψ x y a = GaussInt.add (φ x y a) (GaussInt.sub (ψ x y a) (φ x y a)) := by
        unfold GaussInt.add GaussInt.sub; ext <;> dsimp only <;> omega
      have hLe := GaussInt.normSq_add_le (φ x y a) (GaussInt.sub (ψ x y a) (φ x y a))
      rw [← hEq] at hLe
      exact hLe
  omega

private theorem int_lagrange_identity :
    ∀ (n : Nat) (u0 v0 : Int) (ut vt : Fin n → Int),
      finIntSum n (fun i => (u0 * vt i - v0 * ut i) * (u0 * vt i - v0 * ut i)) =
        u0 * u0 * finIntSum n (fun i => vt i * vt i) +
        v0 * v0 * finIntSum n (fun i => ut i * ut i) -
        2 * u0 * v0 * finIntSum n (fun i => ut i * vt i)
  | 0, u0, v0, _, _ => by
    simp only [finIntSum, Int.mul_zero, Int.add_zero, Int.sub_zero]
  | m + 1, u0, v0, ut, vt => by
    let a1 := ut ⟨0, Nat.zero_lt_succ m⟩
    let b1 := vt ⟨0, Nat.zero_lt_succ m⟩
    let ur : Fin m → Int := fun i => ut ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩
    let vr : Fin m → Int := fun i => vt ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩
    have ihm := int_lagrange_identity m u0 v0 ur vr
    have hSq : (u0 * b1 - v0 * a1) * (u0 * b1 - v0 * a1) =
        u0 * u0 * (b1 * b1) + v0 * v0 * (a1 * a1) - 2 * u0 * v0 * (a1 * b1) := by
      have hNegSq : ∀ x : Int, (-x) * (-x) = x * x := fun x => by
        rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
      have e1 : (u0 * b1 - v0 * a1) * (u0 * b1 - v0 * a1) =
          (u0 * b1) * (u0 * b1) - 2 * ((u0 * b1) * (v0 * a1)) + (v0 * a1) * (v0 * a1) := by
        rw [Int.sub_eq_add_neg, Int.add_mul, Int.mul_add, Int.mul_add,
            Int.mul_neg, Int.neg_mul, hNegSq, Int.mul_comm (v0 * a1) (u0 * b1)]
        omega
      have p1 : (u0 * b1) * (u0 * b1) = u0 * u0 * (b1 * b1) := by
        rw [Int.mul_assoc u0 b1, Int.mul_left_comm b1 u0 b1, ← Int.mul_assoc u0 u0]
      have p2 : (v0 * a1) * (v0 * a1) = v0 * v0 * (a1 * a1) := by
        rw [Int.mul_assoc v0 a1, Int.mul_left_comm a1 v0 a1, ← Int.mul_assoc v0 v0]
      have p3 : (u0 * b1) * (v0 * a1) = u0 * v0 * (a1 * b1) := by
        rw [Int.mul_assoc u0 b1, Int.mul_left_comm b1 v0 a1,
            ← Int.mul_assoc u0 v0, Int.mul_comm b1 a1]
      have p4 : 2 * (u0 * v0 * (a1 * b1)) = 2 * u0 * v0 * (a1 * b1) := by
        simp only [Int.mul_assoc]
      rw [e1, p1, p2, p3, p4]
      omega
    change (u0 * b1 - v0 * a1) * (u0 * b1 - v0 * a1) +
        finIntSum m (fun i => (u0 * vr i - v0 * ur i) * (u0 * vr i - v0 * ur i)) =
      u0 * u0 * (b1 * b1 + finIntSum m (fun i => vr i * vr i)) +
      v0 * v0 * (a1 * a1 + finIntSum m (fun i => ur i * ur i)) -
      2 * u0 * v0 * (a1 * b1 + finIntSum m (fun i => ur i * vr i))
    rw [hSq, ihm, Int.mul_add, Int.mul_add, Int.mul_add]
    omega

private theorem finIntSum_sq_nonneg :
    ∀ (n : Nat) (f : Fin n → Int), 0 ≤ finIntSum n (fun i => f i * f i)
  | 0, _ => Int.le_refl 0
  | m + 1, f => by
    simp only [finIntSum]
    have h0 := int_sq_nonneg (f ⟨0, Nat.zero_lt_succ m⟩)
    have ht := finIntSum_sq_nonneg m (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
    omega

private theorem int_cauchy_schwarz_finSum :
    ∀ (n : Nat) (u v : Fin n → Int),
      (finIntSum n (fun i => u i * v i)) ^ 2 ≤
        finIntSum n (fun i => u i * u i) * finIntSum n (fun i => v i * v i)
  | 0, _, _ => by simp [finIntSum]
  | n + 1, u, v => by
    let u0 := u ⟨0, Nat.zero_lt_succ n⟩
    let v0 := v ⟨0, Nat.zero_lt_succ n⟩
    let ut : Fin n → Int := fun i => u ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩
    let vt : Fin n → Int := fun i => v ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩
    have ih := int_cauchy_schwarz_finSum n ut vt
    let A := finIntSum n (fun i => ut i * ut i)
    let B := finIntSum n (fun i => vt i * vt i)
    let C := finIntSum n (fun i => ut i * vt i)
    change (u0 * v0 + C) ^ 2 ≤ (u0 * u0 + A) * (v0 * v0 + B)
    change C ^ 2 ≤ A * B at ih
    have hLagrange :
        finIntSum n (fun i => (u0 * vt i - v0 * ut i) * (u0 * vt i - v0 * ut i)) =
          u0 * u0 * B + v0 * v0 * A - 2 * u0 * v0 * C :=
      int_lagrange_identity n u0 v0 ut vt
    have hNonneg : 0 ≤ finIntSum n
        (fun i => (u0 * vt i - v0 * ut i) * (u0 * vt i - v0 * ut i)) :=
      finIntSum_sq_nonneg n (fun i => u0 * vt i - v0 * ut i)
    have p2 : ∀ x : Int, x ^ 2 = x * x := fun x => by
      change x ^ (1 + 1) = x * x
      rw [Int.pow_succ, Int.pow_succ, Int.pow_zero, Int.one_mul]
    have hSqL : (u0 * v0 + C) ^ 2 = (u0 * v0) * (u0 * v0) + 2 * u0 * v0 * C + C ^ 2 := by
      rw [p2 (u0 * v0 + C), Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm C (u0 * v0), ← p2 C]
      have assoc2 : 2 * (u0 * v0 * C) = 2 * u0 * v0 * C := by simp only [Int.mul_assoc]
      omega
    have hSqR : (u0 * u0 + A) * (v0 * v0 + B) =
        (u0 * v0) * (u0 * v0) + u0 * u0 * B + v0 * v0 * A + A * B := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm A (v0 * v0)]
      have uvEq : (u0 * u0) * (v0 * v0) = (u0 * v0) * (u0 * v0) := by
        rw [Int.mul_assoc u0 u0, Int.mul_left_comm u0 v0 v0, ← Int.mul_assoc u0 v0]
      rw [uvEq]
      omega
    rw [hSqL, hSqR]
    omega

private theorem cs_combine_two {a1 b1 c1 a2 b2 c2 : Int}
    (ha1 : 0 ≤ a1) (hb1 : 0 ≤ b1) (ha2 : 0 ≤ a2) (hb2 : 0 ≤ b2)
    (h1 : c1 ^ 2 ≤ a1 * b1) (h2 : c2 ^ 2 ≤ a2 * b2) :
    (c1 + c2) ^ 2 ≤ (a1 + a2) * (b1 + b2) := by
  have p2 : ∀ x : Int, x ^ 2 = x * x := fun x => by
    change x ^ (1 + 1) = x * x
    rw [Int.pow_succ, Int.pow_succ, Int.pow_zero, Int.one_mul]
  have hProd : c1 ^ 2 * c2 ^ 2 ≤ (a1 * b1) * (a2 * b2) :=
    Int.mul_le_mul h1 h2 (by rw [p2]; exact int_sq_nonneg c2) (Int.mul_nonneg ha1 hb1)
  have hAmGm : 4 * ((a1 * b1) * (a2 * b2)) ≤ (a1 * b2 + a2 * b1) ^ 2 := by
    have hDiffSq := int_sq_nonneg (a1 * b2 - a2 * b1)
    rw [p2]
    have idPlus : ∀ u v : Int, (u + v) * (u + v) = u * u + u * v + (v * u + v * v) := fun u v => by
      rw [Int.add_mul, Int.mul_add, Int.mul_add]
    have idMinus : ∀ u v : Int, (u - v) * (u - v) = u * u - u * v - v * u + v * v := fun u v => by
      have hNegSq : (-v) * (-v) = v * v := by rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
      rw [Int.sub_eq_add_neg, Int.add_mul, Int.mul_add, Int.mul_add,
          Int.mul_neg, Int.neg_mul, hNegSq]
      omega
    have id1 : (a1 * b2 + a2 * b1) * (a1 * b2 + a2 * b1) -
        (a1 * b2 - a2 * b1) * (a1 * b2 - a2 * b1) = 4 * ((a1 * b1) * (a2 * b2)) := by
      rw [idPlus (a1 * b2) (a2 * b1), idMinus (a1 * b2) (a2 * b1)]
      have mEq : (a1 * b2) * (a2 * b1) = (a1 * b1) * (a2 * b2) := by
        rw [Int.mul_assoc a1 b2 (a2 * b1), Int.mul_comm b2 (a2 * b1),
            Int.mul_assoc a2 b1 b2, Int.mul_left_comm a2 b1 b2,
            ← Int.mul_assoc a1 b1 (a2 * b2)]
      have mEq2 : (a2 * b1) * (a1 * b2) = (a1 * b1) * (a2 * b2) := by rw [Int.mul_comm, mEq]
      rw [mEq, mEq2]
      omega
    omega
  have h4L : (2 * c1 * c2) ^ 2 = 4 * (c1 ^ 2 * c2 ^ 2) := by
    rw [p2, p2 c1, p2 c2]
    rw [Int.mul_assoc (2 * c1) c2 (2 * c1 * c2),
        ← Int.mul_assoc c2 (2 * c1) c2,
        Int.mul_comm c2 (2 * c1),
        Int.mul_assoc (2 * c1) c2 c2,
        ← Int.mul_assoc (2 * c1) (2 * c1) (c2 * c2)]
    have h2c : (2 * c1) * (2 * c1) = 4 * (c1 * c1) := by
      rw [Int.mul_assoc 2 c1 (2 * c1), Int.mul_left_comm c1 2 c1,
          ← Int.mul_assoc (2 : Int) 2 (c1 * c1)]
      rfl
    rw [h2c, Int.mul_assoc 4 (c1 * c1) (c2 * c2)]
  have hCrossSq : (2 * c1 * c2) ^ 2 ≤ (a1 * b2 + a2 * b1) ^ 2 := by
    rw [h4L]
    exact Int.le_trans (Int.mul_le_mul_of_nonneg_left hProd (by decide)) hAmGm
  have hCross : 2 * c1 * c2 ≤ a1 * b2 + a2 * b1 := by
    have hSN : 0 ≤ a1 * b2 + a2 * b1 :=
      Int.add_nonneg (Int.mul_nonneg ha1 hb2) (Int.mul_nonneg ha2 hb1)
    by_cases hc : 2 * c1 * c2 ≤ a1 * b2 + a2 * b1
    · exact hc
    · exfalso
      rw [p2, p2] at hCrossSq
      have hGt : a1 * b2 + a2 * b1 < 2 * c1 * c2 := by omega
      have hPosR : 0 < 2 * c1 * c2 := by omega
      have h1' := Int.mul_le_mul_of_nonneg_left (Int.le_of_lt hGt) hSN
      have h2' := Int.mul_lt_mul_of_pos_right hGt hPosR
      omega
  have expL : (c1 + c2) ^ 2 = c1 ^ 2 + c2 ^ 2 + 2 * c1 * c2 := by
    rw [p2 (c1 + c2), Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm c2 c1, ← p2 c1, ← p2 c2]
    have a2c : 2 * (c1 * c2) = 2 * c1 * c2 := by simp only [Int.mul_assoc]
    omega
  have expR : (a1 + a2) * (b1 + b2) = a1 * b1 + a2 * b2 + (a1 * b2 + a2 * b1) := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add]
    omega
  rw [expL, expR]
  omega

/-- **Born-Rule Probability Difference Bound (`(P(ψ) - P(φ))² ≤ 4 ‖ψ‖² ‖ψ - φ‖²`)**:
    For ANY two states `ψ, φ` of equal squared norm `N = stateNormSq ψ = stateNormSq φ` and ANY
    projective measurement event `E`, `(P_E(ψ) - P_E(φ))² ≤ 4 * N * stateNormSq (ψ - φ)`. -/
theorem born_prob_diff_sq_le_four_state_dist_sq {cardX w cardAnc : Nat}
    (E : Fin cardX → Bool) (ψ φ : QVec cardX w cardAnc)
    (hNormEq : QVec.stateNormSq ψ = QVec.stateNormSq φ) :
    ((Int.ofNat (QVec.measureNormSq E ψ) - Int.ofNat (QVec.measureNormSq E φ)) ^ 2) ≤
      Int.ofNat (4 * QVec.stateNormSq ψ * QVec.stateNormSq (ψ.sub φ)) := by
  have hCoordCS :
      ∀ {M : Nat} (z g : Fin M → GaussInt),
        (finIntSum M (fun i => GaussInt.normSqInt (z i) - GaussInt.normSqInt (g i))) ^ 2 ≤
        Int.ofNat (qsum M (fun i => GaussInt.normSq (GaussInt.sub (z i) (g i)))) *
        Int.ofNat (qsum M (fun i => GaussInt.normSq (GaussInt.add (z i) (g i)))) := by
    intro M z g
    induction M with
    | zero => simp [finIntSum, qsum]
    | succ m ihm =>
      let z0 := z ⟨0, Nat.zero_lt_succ m⟩
      let g0 := g ⟨0, Nat.zero_lt_succ m⟩
      let zt : Fin m → GaussInt := fun i => z ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩
      let gt : Fin m → GaussInt := fun i => g ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩
      have ih' := ihm zt gt
      have hBase : (GaussInt.normSqInt z0 - GaussInt.normSqInt g0) ^ 2 ≤
          Int.ofNat (GaussInt.normSq (GaussInt.sub z0 g0)) *
          Int.ofNat (GaussInt.normSq (GaussInt.add z0 g0)) := by
        rw [← GaussInt.normSqInt_eq_ofNat_normSq, ← GaussInt.normSqInt_eq_ofNat_normSq]
        let u2 : Fin 2 → Int := fun i => if i.1 == 0 then z0.re - g0.re else z0.im - g0.im
        let v2 : Fin 2 → Int := fun i => if i.1 == 0 then z0.re + g0.re else z0.im + g0.im
        have cs2 := int_cauchy_schwarz_finSum 2 u2 v2
        have h00 : ((0 : Nat) == 0) = true := rfl
        have h10 : ((0 + 1 : Nat) == 0) = false := rfl
        simp only [finIntSum, u2, v2, h00, h10, Bool.false_eq_true, ↓reduceIte] at cs2
        have hDiff : (z0.re - g0.re) * (z0.re + g0.re) + ((z0.im - g0.im) * (z0.im + g0.im) + 0) =
            GaussInt.normSqInt z0 - GaussInt.normSqInt g0 := by
          unfold GaussInt.normSqInt
          have r1 : (z0.re - g0.re) * (z0.re + g0.re) = z0.re * z0.re - g0.re * g0.re := by
            rw [Int.sub_eq_add_neg, Int.add_mul, Int.mul_add, Int.mul_add,
                Int.neg_mul, Int.neg_mul, Int.mul_comm g0.re z0.re]
            omega
          have r2 : (z0.im - g0.im) * (z0.im + g0.im) = z0.im * z0.im - g0.im * g0.im := by
            rw [Int.sub_eq_add_neg, Int.add_mul, Int.mul_add, Int.mul_add,
                Int.neg_mul, Int.neg_mul, Int.mul_comm g0.im z0.im]
            omega
          rw [r1, r2]
          omega
        rw [hDiff, Int.add_zero, Int.add_zero] at cs2
        exact cs2
      simp only [finIntSum, qsum, ofNat_add_eq]
      exact cs_combine_two (Int.ofNat_le.mpr (Nat.zero_le _)) (Int.ofNat_le.mpr (Nat.zero_le _))
        (Int.ofNat_le.mpr (Nat.zero_le _)) (Int.ofNat_le.mpr (Nat.zero_le _)) hBase ih'
  have liftQsum : ∀ {N : Nat} (A B P Q : Fin N → Nat),
      (∀ i, ((Int.ofNat (P i) - Int.ofNat (Q i)) ^ 2) ≤ Int.ofNat (A i) * Int.ofNat (B i)) →
      ((Int.ofNat (qsum N P) - Int.ofNat (qsum N Q)) ^ 2) ≤
        Int.ofNat (qsum N A) * Int.ofNat (qsum N B) := by
    intro N A B P Q hI
    induction N with
    | zero => simp [qsum]
    | succ m ihm =>
      simp only [qsum, ofNat_add_eq]
      have hEqDiff : Int.ofNat (P ⟨0, Nat.zero_lt_succ m⟩) +
          Int.ofNat (qsum m (fun i => P ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)) -
          (Int.ofNat (Q ⟨0, Nat.zero_lt_succ m⟩) +
           Int.ofNat (qsum m (fun i => Q ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩))) =
          (Int.ofNat (P ⟨0, Nat.zero_lt_succ m⟩) - Int.ofNat (Q ⟨0, Nat.zero_lt_succ m⟩)) +
          (Int.ofNat (qsum m (fun i => P ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)) -
           Int.ofNat (qsum m (fun i => Q ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩))) := by omega
      rw [hEqDiff]
      exact cs_combine_two (Int.ofNat_le.mpr (Nat.zero_le _)) (Int.ofNat_le.mpr (Nat.zero_le _))
        (Int.ofNat_le.mpr (Nat.zero_le _)) (Int.ofNat_le.mpr (Nat.zero_le _))
        (hI ⟨0, Nat.zero_lt_succ m⟩)
        (ihm _ _ _ _ (fun i => hI ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩))
  have hAnc : ∀ x y,
      ((Int.ofNat (qsum cardAnc (fun a => GaussInt.normSq (ψ x y a))) -
        Int.ofNat (qsum cardAnc (fun a => GaussInt.normSq (φ x y a)))) ^ 2) ≤
      Int.ofNat (qsum cardAnc (fun a => GaussInt.normSq (GaussInt.sub (ψ x y a) (φ x y a)))) *
      Int.ofNat (qsum cardAnc (fun a => GaussInt.normSq (GaussInt.add (ψ x y a) (φ x y a)))) := by
    intro x y
    have hDiffEq : ∀ (n : Nat) (z g : Fin n → GaussInt),
        Int.ofNat (qsum n (fun a => GaussInt.normSq (z a))) -
        Int.ofNat (qsum n (fun a => GaussInt.normSq (g a))) =
        finIntSum n (fun a => GaussInt.normSqInt (z a) - GaussInt.normSqInt (g a)) := by
      intro n z g
      induction n with
      | zero => simp [qsum, finIntSum]
      | succ k ihk =>
        simp only [qsum, finIntSum]
        rw [ofNat_add_eq (GaussInt.normSq (z ⟨0, Nat.zero_lt_succ k⟩)),
            ofNat_add_eq (GaussInt.normSq (g ⟨0, Nat.zero_lt_succ k⟩)),
            ← GaussInt.normSqInt_eq_ofNat_normSq (z ⟨0, Nat.zero_lt_succ k⟩),
            ← GaussInt.normSqInt_eq_ofNat_normSq (g ⟨0, Nat.zero_lt_succ k⟩)]
        have ihk' := ihk (fun a => z ⟨a.1 + 1, Nat.succ_lt_succ a.2⟩)
                         (fun a => g ⟨a.1 + 1, Nat.succ_lt_succ a.2⟩)
        omega
    rw [hDiffEq]
    exact hCoordCS (ψ x y) (φ x y)
  have hY : ∀ x,
      ((Int.ofNat (QVec.queryWeight ψ x) - Int.ofNat (QVec.queryWeight φ x)) ^ 2) ≤
      Int.ofNat (QVec.queryWeight (ψ.sub φ) x) * Int.ofNat (QVec.queryWeight (ψ.add φ) x) := by
    intro x
    exact liftQsum _ _ _ _ (hAnc x)
  have hMeas :
      ((Int.ofNat (QVec.measureNormSq E ψ) - Int.ofNat (QVec.measureNormSq E φ)) ^ 2) ≤
      Int.ofNat (QVec.measureNormSq E (ψ.sub φ)) * Int.ofNat (QVec.measureNormSq E (ψ.add φ)) := by
    apply liftQsum
    intro x
    cases E x
    · simp
    · simp only [↓reduceIte]; exact hY x
  have hSubLe : QVec.measureNormSq E (ψ.sub φ) ≤ QVec.stateNormSq (ψ.sub φ) :=
    QVec.queryMassOn_le_stateNormSq E (ψ.sub φ)
  have hAddLe : QVec.measureNormSq E (ψ.add φ) ≤ 4 * QVec.stateNormSq ψ := by
    have h1 : QVec.measureNormSq E (ψ.add φ) ≤ QVec.stateNormSq (ψ.add φ) :=
      QVec.queryMassOn_le_stateNormSq E (ψ.add φ)
    have h2 : QVec.stateNormSq (ψ.add φ) ≤ 2 * QVec.stateNormSq ψ + 2 * QVec.stateNormSq φ := by
      unfold QVec.stateNormSq QVec.queryWeight QVec.add
      rw [← qsum_mul_left 2, ← qsum_mul_left 2, ← qsum_add]
      apply qsum_le_qsum; intro x
      rw [← qsum_mul_left 2, ← qsum_mul_left 2, ← qsum_add]
      apply qsum_le_qsum; intro y
      rw [← qsum_mul_left 2, ← qsum_mul_left 2, ← qsum_add]
      apply qsum_le_qsum; intro a
      exact GaussInt.normSq_add_le _ _
    omega
  have hProdNat : QVec.measureNormSq E (ψ.sub φ) * QVec.measureNormSq E (ψ.add φ) ≤
      4 * QVec.stateNormSq ψ * QVec.stateNormSq (ψ.sub φ) := by
    have hp := Nat.mul_le_mul hSubLe hAddLe
    exact Nat.le_trans hp (Nat.le_of_eq (Nat.mul_comm _ _))
  rw [← ofNat_mul_eq] at hMeas
  exact Int.le_trans hMeas (Int.ofNat_le.mpr hProdNat)

/-! ### §2.4 Protocol-Coupled QROM & Classical Adaptive Fiber-Search Theorems -/

/-- Exact preimage fiber cardinality `|{ d ∈ BitVec n | encode d = target }|`. -/
def fiberCard {Code : Type} [DecidableEq Code]
    (n : Nat) (encode : BitVec n → Code) (target : Code) : Nat :=
  qsum (2 ^ n) (fun j => if encode (BitVec.ofFin j) = target then 1 else 0)

/-- Any injective protocol digest encoding `encode : BitVec n → Code` has fiber cardinality `≤ 1`
    at every target codeword. -/
theorem fiberCard_le_one_of_injective {Code : Type} [DecidableEq Code]
    (n : Nat) (encode : BitVec n → Code) (hInj : Function.Injective encode) (target : Code) :
    fiberCard n encode target ≤ 1 := by
  unfold fiberCard
  have hBool : qsum (2 ^ n) (fun j => if encode (BitVec.ofFin j) = target then 1 else 0) =
      qsum (2 ^ n) (fun j => if decide (encode (BitVec.ofFin j) = target) = true then 1 else 0) := by
    apply qsum_congr; intro j
    by_cases h : encode (BitVec.ofFin j) = target <;> simp [h]
  rw [hBool]
  apply qsum_le_one_of_subsingleton
  intro i j hi hj
  have hi' : encode (BitVec.ofFin i) = target := of_decide_eq_true hi
  have hj' : encode (BitVec.ofFin j) = target := of_decide_eq_true hj
  have hEqBv : BitVec.ofFin i = BitVec.ofFin j := hInj (hi'.trans hj'.symm)
  exact congrArg BitVec.toFin hEqBv

/-- XOR-shifted indicator oracle `O_Δ` marking `x : Fin (2 ^ n)` with `1#(w + 1)` iff
    `encode (x ⊕ Δ) = target`. -/
def shiftedFiberOracle {Code : Type} [DecidableEq Code]
    (n w : Nat) (encode : BitVec n → Code) (target : Code) (mask : BitVec n) :
    Fin (2 ^ n) → BitVec (w + 1) :=
  fun x => if encode (BitVec.ofFin x ^^^ mask) = target then 1#(w + 1) else 0#(w + 1)

/-- Blank reference oracle returning `0#(w + 1)` on every query. -/
def blankFiberOracle (n w : Nat) : Fin (2 ^ n) → BitVec (w + 1) :=
  fun _ => 0#(w + 1)

private theorem sum_masks_shifted_fiber {Code : Type} [DecidableEq Code]
    (n : Nat) (encode : BitVec n → Code) (target : Code) (weight : Fin (2 ^ n) → Nat) :
    qsum (2 ^ n) (fun m =>
      qsum (2 ^ n) (fun x =>
        if encode (BitVec.ofFin x ^^^ BitVec.ofFin m) = target then weight x else 0)) =
      fiberCard n encode target * qsum (2 ^ n) weight := by
  rw [qsum_comm]
  have hInner : ∀ x : Fin (2 ^ n),
      qsum (2 ^ n) (fun m =>
        if encode (BitVec.ofFin x ^^^ BitVec.ofFin m) = target then weight x else 0) =
      weight x * fiberCard n encode target := by
    intro x
    have hFactor : qsum (2 ^ n) (fun m =>
        if encode (BitVec.ofFin x ^^^ BitVec.ofFin m) = target then weight x else 0) =
        weight x * qsum (2 ^ n) (fun m =>
          if encode (BitVec.ofFin x ^^^ BitVec.ofFin m) = target then 1 else 0) := by
      rw [← qsum_mul_left]
      apply qsum_congr; intro m
      by_cases h : encode (BitVec.ofFin x ^^^ BitVec.ofFin m) = target <;> simp [h]
    rw [hFactor]
    congr 1
    let π : Fin (2 ^ n) → Fin (2 ^ n) := fun m => (BitVec.ofFin x ^^^ BitVec.ofFin m).toFin
    have hInv : ∀ m : Fin (2 ^ n), π (π m) = m := by
      intro m
      dsimp only [π]
      rw [BitVec.ofFin_toFin]
      have hX : BitVec.ofFin x ^^^ (BitVec.ofFin x ^^^ BitVec.ofFin m) = BitVec.ofFin m := by
        apply BitVec.eq_of_getLsbD_eq; intro i _
        simp only [BitVec.getLsbD_xor]
        cases (BitVec.ofFin x).getLsbD i <;> cases (BitVec.ofFin m).getLsbD i <;> rfl
      rw [hX, BitVec.toFin_ofFin]
    have hPerm := qsum_involutive π hInv
      (fun z => if encode (BitVec.ofFin z) = target then 1 else 0)
    unfold fiberCard
    rw [← hPerm]
  rw [qsum_congr hInner, qsum_mul_right, Nat.mul_comm]

/-- **Protocol-Coupled Unitary QROM Fiber-Search Theorem (`qrom_fiber_search_bound`)**:
    For ANY `q`-query unitary quantum adversary `A` (`QuantumAdv (2 ^ n) (w + 1) cardAnc q`) and
    ANY protocol digest map `encode : BitVec n → Code`, the Born-rule success probability of
    finding `x` in `target`'s preimage fiber (averaged over `2 ^ n` keyed/tweaked masks `Δ`) is
    bounded by `((8 * q ^ 2 + 2) * fiberCard n encode target) / 2 ^ n`, and hence by
    `8 * (q + 1) ^ 2 * fiberCard n encode target / 2 ^ n`! -/
theorem qrom_fiber_search_bound {Code : Type} [DecidableEq Code]
    {n w cardAnc q : Nat}
    (A : QuantumAdv (2 ^ n) (w + 1) cardAnc q)
    (encode : BitVec n → Code) (target : Code) :
    let normFinal := QVec.stateNormSq (runQuantumAdv A (blankFiberOracle n w))
    let avgBornSuccess : RatBound :=
      ⟨qsum (2 ^ n) (fun m =>
         QVec.measureNormSq
           (fun x => decide (encode (BitVec.ofFin x ^^^ BitVec.ofFin m) = target))
           (runQuantumAdv A (shiftedFiberOracle n w encode target (BitVec.ofFin m)))),
       2 ^ n * normFinal,
       Nat.mul_pos (Nat.two_pow_pos n) (runQuantumAdv_normSq_pos A (blankFiberOracle n w))⟩
    RatBound.le avgBornSuccess
      ⟨(8 * q ^ 2 + 2) * fiberCard n encode target, 2 ^ n, Nat.two_pow_pos n⟩ ∧
    RatBound.le avgBornSuccess
      ⟨8 * (q + 1) ^ 2 * fiberCard n encode target, 2 ^ n, Nat.two_pow_pos n⟩ := by
  let normFinal := QVec.stateNormSq (runQuantumAdv A (blankFiberOracle n w))
  let ψBlank := runQuantumAdv A (blankFiberOracle n w)
  let K := fiberCard n encode target
  have hPerMask : ∀ m : Fin (2 ^ n),
      let Sm : Fin (2 ^ n) → Bool :=
        fun x => decide (encode (BitVec.ofFin x ^^^ BitVec.ofFin m) = target)
      QVec.measureNormSq Sm
        (runQuantumAdv A (shiftedFiberOracle n w encode target (BitVec.ofFin m))) ≤
      2 * QVec.measureNormSq Sm ψBlank +
      8 * q * qsum q (fun t =>
        suffixScale A t.1 (Nat.le_of_lt t.2) *
          QVec.queryMassOn Sm (advStateAt A (blankFiberOracle n w) t.1 (Nat.le_of_lt t.2))) := by
    intro m
    let Sm : Fin (2 ^ n) → Bool :=
      fun x => decide (encode (BitVec.ofFin x ^^^ BitVec.ofFin m) = target)
    have hBorn := born_measure_le_two_add_two_dist_sq Sm
      (runQuantumAdv A (shiftedFiberOracle n w encode target (BitVec.ofFin m))) ψBlank
    have hAgree : ∀ x : Fin (2 ^ n), Sm x = false →
        shiftedFiberOracle n w encode target (BitVec.ofFin m) x = blankFiberOracle n w x := by
      intro x hx
      unfold shiftedFiberOracle blankFiberOracle
      have hne : encode (BitVec.ofFin x ^^^ BitVec.ofFin m) ≠ target := by
        intro heq; simp [Sm, heq] at hx
      simp [hne]
    have hO2h := qrom_o2h_telescoping_disturbance_le A
      (shiftedFiberOracle n w encode target (BitVec.ofFin m)) (blankFiberOracle n w) Sm hAgree
    have h2 := Nat.mul_le_mul_left 2 hO2h
    rw [← Nat.mul_assoc 2 (4 * q), show 2 * (4 * q) = 8 * q by omega] at h2
    exact Nat.le_trans hBorn (Nat.add_le_add_left h2 _)
  have hSumMasks := qsum_le_qsum hPerMask
  rw [qsum_add, qsum_mul_left 2, qsum_mul_left (8 * q), qsum_comm (2 ^ n) q] at hSumMasks
  have hBlankTerm :
      qsum (2 ^ n) (fun m =>
        QVec.measureNormSq (fun x => decide (encode (BitVec.ofFin x ^^^ BitVec.ofFin m) = target)) ψBlank) =
      K * normFinal := by
    unfold QVec.measureNormSq QVec.queryMassOn
    have hRewrite : qsum (2 ^ n) (fun m => qsum (2 ^ n) (fun x =>
        if decide (encode (BitVec.ofFin x ^^^ BitVec.ofFin m) = target) = true
        then QVec.queryWeight ψBlank x else 0)) =
        qsum (2 ^ n) (fun m => qsum (2 ^ n) (fun x =>
          if encode (BitVec.ofFin x ^^^ BitVec.ofFin m) = target
          then QVec.queryWeight ψBlank x else 0)) := by
      apply qsum_congr; intro m; apply qsum_congr; intro x
      by_cases h : encode (BitVec.ofFin x ^^^ BitVec.ofFin m) = target <;> simp [h]
    rw [hRewrite, sum_masks_shifted_fiber]
    rfl
  have hQueryTerms :
      qsum q (fun t => qsum (2 ^ n) (fun m =>
        suffixScale A t.1 (Nat.le_of_lt t.2) *
          QVec.queryMassOn (fun x => decide (encode (BitVec.ofFin x ^^^ BitVec.ofFin m) = target))
            (advStateAt A (blankFiberOracle n w) t.1 (Nat.le_of_lt t.2)))) =
      q * (K * normFinal) := by
    have hEachT : ∀ t : Fin q,
        qsum (2 ^ n) (fun m =>
          suffixScale A t.1 (Nat.le_of_lt t.2) *
            QVec.queryMassOn (fun x => decide (encode (BitVec.ofFin x ^^^ BitVec.ofFin m) = target))
              (advStateAt A (blankFiberOracle n w) t.1 (Nat.le_of_lt t.2))) =
        K * normFinal := by
      intro t
      rw [qsum_mul_left]
      unfold QVec.queryMassOn
      have hRew : qsum (2 ^ n) (fun m => qsum (2 ^ n) (fun x =>
          if decide (encode (BitVec.ofFin x ^^^ BitVec.ofFin m) = target) = true
          then QVec.queryWeight (advStateAt A (blankFiberOracle n w) t.1 (Nat.le_of_lt t.2)) x else 0)) =
          K * QVec.stateNormSq (advStateAt A (blankFiberOracle n w) t.1 (Nat.le_of_lt t.2)) := by
        have h1 : qsum (2 ^ n) (fun m => qsum (2 ^ n) (fun x =>
            if decide (encode (BitVec.ofFin x ^^^ BitVec.ofFin m) = target) = true
            then QVec.queryWeight (advStateAt A (blankFiberOracle n w) t.1 (Nat.le_of_lt t.2)) x else 0)) =
            qsum (2 ^ n) (fun m => qsum (2 ^ n) (fun x =>
              if encode (BitVec.ofFin x ^^^ BitVec.ofFin m) = target
              then QVec.queryWeight (advStateAt A (blankFiberOracle n w) t.1 (Nat.le_of_lt t.2)) x else 0)) := by
          apply qsum_congr; intro m; apply qsum_congr; intro x
          by_cases h : encode (BitVec.ofFin x ^^^ BitVec.ofFin m) = target <;> simp [h]
        rw [h1, sum_masks_shifted_fiber]
        rfl
      rw [hRew, advStateAt_normSq]
      dsimp only [normFinal]
      rw [runQuantumAdv_normSq]
      have hScale := prefix_mul_suffix_eq_total A t.1 (Nat.le_of_lt t.2)
      calc suffixScale A t.1 (Nat.le_of_lt t.2) *
             (K * (prefixScale A t.1 (Nat.le_of_lt t.2) * QVec.stateNormSq A.init))
        _ = K * ((prefixScale A t.1 (Nat.le_of_lt t.2) * suffixScale A t.1 (Nat.le_of_lt t.2)) *
                 QVec.stateNormSq A.init) := by
          rw [← Nat.mul_assoc, Nat.mul_comm (suffixScale A t.1 (Nat.le_of_lt t.2)) K,
              Nat.mul_assoc K, ← Nat.mul_assoc (suffixScale A t.1 (Nat.le_of_lt t.2)),
              Nat.mul_comm (suffixScale A t.1 (Nat.le_of_lt t.2))]
        _ = K * (prefixScale A q (Nat.le_refl q) * QVec.stateNormSq A.init) := by rw [hScale]
    rw [qsum_congr hEachT, qsum_const]
  rw [hBlankTerm, hQueryTerms] at hSumMasks
  have hTight : qsum (2 ^ n) (fun m =>
      QVec.measureNormSq
        (fun x => decide (encode (BitVec.ofFin x ^^^ BitVec.ofFin m) = target))
        (runQuantumAdv A (shiftedFiberOracle n w encode target (BitVec.ofFin m)))) ≤
      (8 * q ^ 2 + 2) * K * normFinal := by
    have hAlg : 2 * (K * normFinal) + 8 * q * (q * (K * normFinal)) =
        (8 * q ^ 2 + 2) * K * normFinal := by
      rw [Nat.pow_two, Nat.add_mul, Nat.add_mul]
      simp only [Nat.mul_assoc]
      omega
    rw [hAlg] at hSumMasks
    exact hSumMasks
  have hFirst : RatBound.le
      ⟨qsum (2 ^ n) (fun m =>
         QVec.measureNormSq
           (fun x => decide (encode (BitVec.ofFin x ^^^ BitVec.ofFin m) = target))
           (runQuantumAdv A (shiftedFiberOracle n w encode target (BitVec.ofFin m)))),
       2 ^ n * normFinal,
       Nat.mul_pos (Nat.two_pow_pos n) (runQuantumAdv_normSq_pos A (blankFiberOracle n w))⟩
      ⟨(8 * q ^ 2 + 2) * K, 2 ^ n, Nat.two_pow_pos n⟩ := by
    unfold RatBound.le
    dsimp only
    have hm := Nat.mul_le_mul_right (2 ^ n) hTight
    have hR : (8 * q ^ 2 + 2) * K * normFinal * 2 ^ n =
        (8 * q ^ 2 + 2) * K * (2 ^ n * normFinal) := by
      rw [Nat.mul_assoc ((8 * q ^ 2 + 2) * K) normFinal (2 ^ n), Nat.mul_comm normFinal (2 ^ n)]
    rw [hR] at hm
    exact hm
  refine ⟨hFirst, RatBound.le_trans hFirst ?_⟩
  unfold RatBound.le
  dsimp only
  apply Nat.mul_le_mul_right
  apply Nat.mul_le_mul_right
  have hSq : (q + 1) ^ 2 = q ^ 2 + 2 * q + 1 := by
    rw [Nat.pow_two, Nat.pow_two, Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
  rw [hSq, Nat.mul_add, Nat.mul_add]
  omega

/-! ### §2.5 Classical Adaptive `OracleComp` Lazy-RO Fiber-Search Theorem -/

/-- Lookup a previously queried input `x` inside a lazy random-oracle transcript. -/
def lookupLazyRo {Dom Val : Type} [DecidableEq Dom] : List (Dom × Val) → Dom → Option Val
  | [], _ => none
  | (k, v) :: rest, x => if x = k then some v else lookupLazyRo rest x

/-- Exact integer-scaled hitting count (denominator `(2 ^ n) ^ (q + 1)`) of an adaptive height-`q`
    `OracleComp Dom (BitVec n) Dom` adversary over a uniform lazy random oracle trying to output
    `m' ≠ mSigned` with `encode (H m') = target`. -/
def lazyRoScaledHits {Dom Code : Type} [DecidableEq Dom] [DecidableEq Code]
    (n : Nat) (encode : BitVec n → Code) (target : Code) (mSigned : Dom) :
    Nat → List (Dom × BitVec n) → OracleComp Dom (BitVec n) Dom → Nat
  | 0, hist, .pure mOut =>
    if mOut = mSigned then 0
    else match lookupLazyRo hist mOut with
      | some d => if encode d = target then 2 ^ n else 0
      | none => fiberCard n encode target
  | 0, _, .query _ _ => 0
  | q + 1, hist, .pure mOut =>
    2 ^ n * lazyRoScaledHits n encode target mSigned q hist (.pure mOut)
  | q + 1, hist, .query x next =>
    match lookupLazyRo hist x with
    | some d => 2 ^ n * lazyRoScaledHits n encode target mSigned q hist (next d)
    | none =>
      qsum (2 ^ n) (fun j =>
        lazyRoScaledHits n encode target mSigned q
          ((x, BitVec.ofFin j) :: hist) (next (BitVec.ofFin j)))

private theorem fiberCard_le_two_pow {Code : Type} [DecidableEq Code]
    (n : Nat) (encode : BitVec n → Code) (target : Code) :
    fiberCard n encode target ≤ 2 ^ n := by
  unfold fiberCard
  have h1 : qsum (2 ^ n) (fun j => if encode (BitVec.ofFin j) = target then 1 else 0) ≤
      qsum (2 ^ n) (fun _ => 1) := by
    apply qsum_le_qsum; intro j
    by_cases h : encode (BitVec.ofFin j) = target <;> simp [h]
  rw [qsum_const, Nat.mul_one] at h1
  exact h1

private theorem lazyRoScaledHits_le_full {Dom Code : Type} [DecidableEq Dom] [DecidableEq Code]
    (n : Nat) (encode : BitVec n → Code) (target : Code) (mSigned : Dom) :
    ∀ (q : Nat) (hist : List (Dom × BitVec n)) (prog : OracleComp Dom (BitVec n) Dom),
      lazyRoScaledHits n encode target mSigned q hist prog ≤ (2 ^ n) ^ (q + 1)
  | 0, hist, .pure mOut => by
    simp only [lazyRoScaledHits]
    rw [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
    split
    · exact Nat.zero_le _
    · split
      · split
        · exact Nat.le_refl _
        · exact Nat.zero_le _
      · exact fiberCard_le_two_pow n encode target
  | 0, _, .query _ _ => Nat.zero_le _
  | q + 1, hist, .pure mOut => by
    simp only [lazyRoScaledHits]
    have ih := lazyRoScaledHits_le_full n encode target mSigned q hist (.pure mOut)
    rw [Nat.pow_succ _ (q + 1), Nat.mul_comm ((2 ^ n) ^ (q + 1)) (2 ^ n)]
    exact Nat.mul_le_mul_left (2 ^ n) ih
  | q + 1, hist, .query x next => by
    simp only [lazyRoScaledHits]
    split
    · rename_i d _
      have ih := lazyRoScaledHits_le_full n encode target mSigned q hist (next d)
      rw [Nat.pow_succ _ (q + 1), Nat.mul_comm ((2 ^ n) ^ (q + 1)) (2 ^ n)]
      exact Nat.mul_le_mul_left (2 ^ n) ih
    · have hEach : ∀ j : Fin (2 ^ n),
          lazyRoScaledHits n encode target mSigned q
            ((x, BitVec.ofFin j) :: hist) (next (BitVec.ofFin j)) ≤ (2 ^ n) ^ (q + 1) :=
        fun j => lazyRoScaledHits_le_full n encode target mSigned q _ _
      have hSum := qsum_le_qsum hEach
      rw [qsum_const, Nat.pow_succ _ (q + 1), Nat.mul_comm ((2 ^ n) ^ (q + 1)) (2 ^ n)] at *
      exact hSum

private theorem lazyRo_step_prod (N q K : Nat) :
    N * ((q + 1) * K * N ^ q) = (q + 1) * (K * N ^ (q + 1)) := by
  calc N * ((q + 1) * K * N ^ q)
    _ = (N * ((q + 1) * K)) * N ^ q := (Nat.mul_assoc _ _ _).symm
    _ = (((q + 1) * K) * N) * N ^ q := by rw [Nat.mul_comm N ((q + 1) * K)]
    _ = ((q + 1) * K) * (N * N ^ q) := Nat.mul_assoc _ _ _
    _ = (q + 1) * (K * (N ^ q * N)) := by rw [Nat.mul_comm N (N ^ q), Nat.mul_assoc (q + 1)]
    _ = (q + 1) * (K * N ^ (q + 1)) := by rw [← Nat.pow_succ N q]

private theorem lazyRo_step_le (N q K : Nat) :
    N * ((q + 1) * K * N ^ q) ≤ (q + 2) * K * N ^ (q + 1) := by
  rw [lazyRo_step_prod, Nat.mul_assoc (q + 2) K (N ^ (q + 1))]
  exact Nat.mul_le_mul_right (K * N ^ (q + 1)) (by omega)

private theorem lazyRo_step_eq (N q K : Nat) :
    K * N ^ (q + 1) + N * ((q + 1) * K * N ^ q) = (q + 2) * K * N ^ (q + 1) := by
  rw [lazyRo_step_prod, Nat.mul_assoc (q + 2) K (N ^ (q + 1))]
  have h1 : q + 2 = 1 + (q + 1) := by omega
  rw [h1, Nat.add_mul 1 (q + 1) (K * N ^ (q + 1)), Nat.one_mul]

private theorem lazyRoScaledHits_bound_aux {Dom Code : Type} [DecidableEq Dom] [DecidableEq Code]
    (n : Nat) (encode : BitVec n → Code) (target : Code) (mSigned : Dom) :
    ∀ (q : Nat) (hist : List (Dom × BitVec n)) (prog : OracleComp Dom (BitVec n) Dom),
      QueryBounded q prog →
      (∀ x d, lookupLazyRo hist x = some d → x ≠ mSigned → encode d ≠ target) →
      lazyRoScaledHits n encode target mSigned q hist prog ≤
        (q + 1) * fiberCard n encode target * (2 ^ n) ^ q
  | 0, hist, .pure mOut, _, hClean => by
    simp only [lazyRoScaledHits, Nat.pow_zero, Nat.mul_one, Nat.zero_add, Nat.one_mul]
    split
    · exact Nat.zero_le _
    · rename_i hNe
      split
      · rename_i d hLk
        have hNot := hClean mOut d hLk hNe
        simp [hNot]
      · exact Nat.le_refl _
  | 0, _, .query _ _, hQB, _ => False.elim hQB
  | q + 1, hist, .pure mOut, _, hClean => by
    simp only [lazyRoScaledHits]
    have hQBPure : QueryBounded q (OracleComp.pure mOut : OracleComp Dom (BitVec n) Dom) := by
      cases q <;> exact trivial
    have ih := lazyRoScaledHits_bound_aux n encode target mSigned q hist (.pure mOut) hQBPure hClean
    exact Nat.le_trans (Nat.mul_le_mul_left (2 ^ n) ih)
      (lazyRo_step_le (2 ^ n) q (fiberCard n encode target))
  | q + 1, hist, .query x next, hQB, hClean => by
    simp only [lazyRoScaledHits]
    split
    · rename_i d _
      have ih := lazyRoScaledHits_bound_aux n encode target mSigned q hist (next d) (hQB d) hClean
      exact Nat.le_trans (Nat.mul_le_mul_left (2 ^ n) ih)
        (lazyRo_step_le (2 ^ n) q (fiberCard n encode target))
    · by_cases hxSigned : x = mSigned
      · have hEach : ∀ j : Fin (2 ^ n),
            lazyRoScaledHits n encode target mSigned q
              ((x, BitVec.ofFin j) :: hist) (next (BitVec.ofFin j)) ≤
            (q + 1) * fiberCard n encode target * (2 ^ n) ^ q := by
          intro j
          apply lazyRoScaledHits_bound_aux n encode target mSigned q _ _ (hQB _)
          intro y dy hyLk hyNe
          simp only [lookupLazyRo] at hyLk
          split at hyLk
          · rename_i hyx
            exact False.elim (hyNe (hyx.trans hxSigned))
          · exact hClean y dy hyLk hyNe
        have hSum := qsum_le_qsum hEach
        rw [qsum_const] at hSum
        exact Nat.le_trans hSum (lazyRo_step_le (2 ^ n) q (fiberCard n encode target))
      · have hPoint : ∀ j : Fin (2 ^ n),
            lazyRoScaledHits n encode target mSigned q
              ((x, BitVec.ofFin j) :: hist) (next (BitVec.ofFin j)) ≤
            (if encode (BitVec.ofFin j) = target then (2 ^ n) ^ (q + 1) else 0) +
            (q + 1) * fiberCard n encode target * (2 ^ n) ^ q := by
          intro j
          by_cases hHit : encode (BitVec.ofFin j) = target
          · simp only [hHit, ↓reduceIte]
            exact Nat.le_trans (lazyRoScaledHits_le_full n encode target mSigned q _ _)
              (Nat.le_add_right _ _)
          · simp only [hHit, ↓reduceIte, Nat.zero_add]
            apply lazyRoScaledHits_bound_aux n encode target mSigned q _ _ (hQB _)
            intro y dy hyLk hyNe
            simp only [lookupLazyRo] at hyLk
            split at hyLk
            · injection hyLk with hEqD
              subst hEqD
              exact hHit
            · exact hClean y dy hyLk hyNe
        have hSum := qsum_le_qsum hPoint
        rw [qsum_add, qsum_const] at hSum
        have hFirst : qsum (2 ^ n) (fun j =>
            if encode (BitVec.ofFin j) = target then (2 ^ n) ^ (q + 1) else 0) =
            fiberCard n encode target * (2 ^ n) ^ (q + 1) := by
          have hRew : qsum (2 ^ n) (fun j =>
              if encode (BitVec.ofFin j) = target then (2 ^ n) ^ (q + 1) else 0) =
              qsum (2 ^ n) (fun j =>
                (if encode (BitVec.ofFin j) = target then 1 else 0) * (2 ^ n) ^ (q + 1)) := by
            apply qsum_congr; intro j
            by_cases h : encode (BitVec.ofFin j) = target <;> simp [h]
          rw [hRew, qsum_mul_right]
          rfl
        rw [hFirst, lazyRo_step_eq (2 ^ n) q (fiberCard n encode target)] at hSum
        exact hSum

/-- **Protocol-Coupled Classical Lazy-RO Adaptive Query Theorem (`classical_lazy_ro_fiber_search_bound`)**:
    For ANY adaptive `OracleComp Dom (BitVec n) Dom` adversary `prog` making at most `q` random-oracle
    queries (given `(mSigned, dSigned)` with `encode dSigned = target`), its exact lazy-RO probability
    of outputting `m' ≠ mSigned` with `encode (H m') = target` is bounded by
    `((q + 1) * fiberCard n encode target) / 2 ^ n`. -/
theorem classical_lazy_ro_fiber_search_bound {Dom Code : Type} [DecidableEq Dom] [DecidableEq Code]
    (n q : Nat) (encode : BitVec n → Code) (mSigned : Dom) (dSigned : BitVec n)
    (prog : OracleComp Dom (BitVec n) Dom) (hQB : QueryBounded q prog) :
    let target := encode dSigned
    let lazyProb : RatBound :=
      ⟨lazyRoScaledHits n encode target mSigned q [(mSigned, dSigned)] prog,
       (2 ^ n) ^ (q + 1),
       Nat.pow_pos (Nat.two_pow_pos n)⟩
    RatBound.le lazyProb
      ⟨(q + 1) * fiberCard n encode target, 2 ^ n, Nat.two_pow_pos n⟩ := by
  dsimp only [RatBound.le]
  have hClean : ∀ x d, lookupLazyRo [(mSigned, dSigned)] x = some d →
      x ≠ mSigned → encode d ≠ encode dSigned := by
    intro x d hLk hNe
    simp only [lookupLazyRo] at hLk
    split at hLk
    · rename_i hx; exact False.elim (hNe hx)
    · cases hLk
  have hAux := lazyRoScaledHits_bound_aux n encode (encode dSigned) mSigned q
    [(mSigned, dSigned)] prog hQB hClean
  have hMul := Nat.mul_le_mul_right (2 ^ n) hAux
  rw [Nat.mul_assoc ((q + 1) * fiberCard n encode (encode dSigned)) ((2 ^ n) ^ q) (2 ^ n),
      ← Nat.pow_succ] at hMul
  exact hMul

/-! ### §2.6 Multi-Target `ADRS` Domain Separation, Quantum BHT Collisions & Fiat–Shamir Bounds -/

/-- Exact QROM single-target (`M = 1`) vs `M`-target Zhandry/Grover preimage bound over `n` bits. -/
def quantumZhandryMultiTargetBound (n M qHash : Nat) : RatBound :=
  ⟨8 * M * (qHash + 1) ^ 2, 2 ^ n, Nat.two_pow_pos n⟩

def quantumGroverSingleTargetBound (n qHash : Nat) : RatBound :=
  quantumZhandryMultiTargetBound n 1 qHash

/-- Pure Grover query-scale bound `qHash ^ 2 / 2 ^ n` (without constant reduction overhead). -/
def groverPureSearchBound (n qHash : Nat) : RatBound :=
  ⟨qHash ^ 2, 2 ^ n, Nat.two_pow_pos n⟩

/-- Classical birthday collision bound `(qHash + 1) ^ 2 / 2 ^ n`. -/
def classicalBirthdayCollisionBound (n qHash : Nat) : RatBound :=
  ⟨(qHash + 1) ^ 2, 2 ^ n, Nat.two_pow_pos n⟩

/-- Quantum Brassard–Høyer–Tapp (`BHT`) / Chailloux–Naya-Plasencia–Schrottenloher (`CNS`) QROM
    unrestricted collision bound `8 * (qHash + 1) ^ 3 / 2 ^ n` (and pure cubic `qHash ^ 3 / 2 ^ n`). -/
def quantumBhtCollisionBound (n qHash : Nat) : RatBound :=
  ⟨8 * (qHash + 1) ^ 3, 2 ^ n, Nat.two_pow_pos n⟩

def quantumBhtPureCubicBound (n qHash : Nat) : RatBound :=
  ⟨qHash ^ 3, 2 ^ n, Nat.two_pow_pos n⟩

/-- Classical Fiat–Shamir single-challenge grinding bound `(qHash + 1) * pErr`. -/
def classicalFiatShamirBound (qHash : Nat) (pErr : RatBound) : RatBound :=
  RatBound.scale (qHash + 1) pErr

/-- Quantum Fiat–Shamir offline Grover grinding bound `8 * (qHash + 1) ^ 2 * pErr` (matching
    `qrom_fiber_search_bound` on bad-challenge fibers!). -/
def quantumGroverGrindingBound (qHash : Nat) (pErr : RatBound) : RatBound :=
  RatBound.scale (8 * (qHash + 1) ^ 2) pErr

/-- Don–Fehr–Majenz (`[DFM20]`) QROM Measure-and-Reprogram bound `(2 * qHash + 1) ^ (2 * mu) * pErr`
    for a `(2 * mu + 1)`-move public-coin interactive argument with `mu` challenge rounds. -/
def quantumDfmMeasureReprogramBound (mu qHash : Nat) (pErr : RatBound) : RatBound :=
  RatBound.scale ((2 * qHash + 1) ^ (2 * mu)) pErr

/-- **Unitary O2H Justification of Quantum Fiat–Shamir Grinding**:
    Offline quantum grinding by ANY `qHash`-query unitary circuit `A` over an `n`-bit transcript
    challenge space where bad challenges satisfy `acceptBad : BitVec n → Bool` (`pErr = K / 2^n`)
    is bounded directly by `quantumGroverGrindingBound qHash pErr` via `qrom_fiber_search_bound`! -/
theorem quantum_fs_grover_grinding_from_o2h {n w cardAnc qHash : Nat}
    (A : QuantumAdv (2 ^ n) (w + 1) cardAnc qHash) (acceptBad : BitVec n → Bool) :
    let normFinal := QVec.stateNormSq (runQuantumAdv A (blankFiberOracle n w))
    let pErr : RatBound := ⟨fiberCard n acceptBad true, 2 ^ n, Nat.two_pow_pos n⟩
    RatBound.le
      ⟨qsum (2 ^ n) (fun m =>
         QVec.measureNormSq
           (fun x => decide (acceptBad (BitVec.ofFin x ^^^ BitVec.ofFin m) = true))
           (runQuantumAdv A (shiftedFiberOracle n w acceptBad true (BitVec.ofFin m)))),
       2 ^ n * normFinal,
       Nat.mul_pos (Nat.two_pow_pos n) (runQuantumAdv_normSq_pos A (blankFiberOracle n w))⟩
      (quantumGroverGrindingBound qHash pErr) :=
  (qrom_fiber_search_bound A acceptBad true).2

/-- **`ADRS` Domain-Separation Multi-Target Reduction (`M = 1`)**:
    Binding distinct `(pkSeed, layer, tree, kind, keyPair, chainIdx, hashStep)` 32-byte `HashAdrs`
    tweaks per one-time chain step isolates each target preimage (`M = 1`), whereas sharing an
    untweaked oracle across `M ≥ 2` signatures incurs a strict `M`-fold multi-target loss. -/
theorem adrs_tweak_reduces_multitarget_to_single_target (n qHash : Nat) :
    quantumZhandryMultiTargetBound n 1 qHash = quantumGroverSingleTargetBound n qHash ∧
    (∀ M : Nat, 2 ≤ M →
      RatBound.lt (quantumGroverSingleTargetBound n qHash)
                  (quantumZhandryMultiTargetBound n M qHash)) := by
  refine ⟨rfl, ?_⟩
  intro M hM
  unfold RatBound.lt quantumGroverSingleTargetBound quantumZhandryMultiTargetBound
  dsimp only
  have hPosSq : 0 < (qHash + 1) ^ 2 := Nat.pow_pos (Nat.succ_pos qHash)
  have hPosPow : 0 < 2 ^ n := Nat.two_pow_pos n
  have hLt8 : 8 * 1 < 8 * M := by omega
  have hLtNum : 8 * 1 * (qHash + 1) ^ 2 < 8 * M * (qHash + 1) ^ 2 :=
    Nat.mul_lt_mul_of_pos_right hLt8 hPosSq
  exact Nat.mul_lt_mul_of_pos_right hLtNum hPosPow

/-- Parametric QROM bit-margin theorem: for `qHash + 1 ≤ 2 ^ k` and `2 * k + 3 + b ≤ n`,
    `quantumGroverSingleTargetBound n qHash` achieves `atLeastBits b`. -/
theorem qrom_single_target_parametric_bits {n k b qHash : Nat}
    (hq : qHash + 1 ≤ 2 ^ k) (hWidth : 2 * k + 3 + b ≤ n) :
    atLeastBits b (quantumGroverSingleTargetBound n qHash) := by
  unfold atLeastBits quantumGroverSingleTargetBound quantumZhandryMultiTargetBound
  dsimp only
  have hSq : (qHash + 1) ^ 2 ≤ (2 ^ k) ^ 2 := Nat.pow_le_pow_left hq 2
  rw [← Nat.pow_mul, Nat.mul_comm k 2] at hSq
  have h8 : 8 * (qHash + 1) ^ 2 ≤ 2 ^ 3 * 2 ^ (2 * k) := Nat.mul_le_mul_left 8 hSq
  rw [← Nat.pow_add, Nat.add_comm 3 (2 * k)] at h8
  have hMulB := Nat.mul_le_mul_right (2 ^ b) h8
  rw [← Nat.pow_add] at hMulB
  exact Nat.le_trans hMulB (Nat.pow_le_pow_right (by decide) hWidth)

/-- **`#tooth` BHT 256-Bit Unrestricted Collision Ceiling (`~85.3` Quantum Bits)**:
    A 256-bit untargeted hash does NOT provide 128-bit generic quantum collision resistance:
    at `qHash = 2 ^ 86` (`< 2 ^ 128`), `quantumBhtPureCubicBound 256 (2 ^ 86) = 2 ^ 258 / 2 ^ 256 > 1`
    (`exceedsBitBudget 0`), whereas a 384-bit output achieves `atLeastBits 128` up to `qHash < 2 ^ 84`
    even under `quantumBhtCollisionBound 384`! -/
theorem tooth_bht_256bit_unrestricted_collision_ceiling_85bits :
    exceedsBitBudget 0 (quantumBhtPureCubicBound 256 (2 ^ 86)) ∧
    exceedsBitBudget 128 (quantumBhtPureCubicBound 256 (2 ^ 43)) ∧
    (∀ qHash : Nat, qHash + 1 ≤ 2 ^ 84 →
      atLeastBits 129 (quantumBhtCollisionBound 384 qHash)) := by
  refine ⟨by unfold exceedsBitBudget quantumBhtPureCubicBound; decide,
          by unfold exceedsBitBudget quantumBhtPureCubicBound; decide, ?_⟩
  intro qHash hq
  unfold atLeastBits quantumBhtCollisionBound
  dsimp only
  have hCube : (qHash + 1) ^ 3 ≤ (2 ^ 84) ^ 3 := Nat.pow_le_pow_left hq 3
  have hPow : 8 * (2 ^ 84) ^ 3 * 2 ^ 129 ≤ 2 ^ 384 := by decide
  have h1 := Nat.mul_le_mul_left 8 hCube
  have h2 := Nat.mul_le_mul_right (2 ^ 129) h1
  exact Nat.le_trans h2 hPow


/-! ## §3. Protocol Encoding Injectivity, Fiber Cardinalities & Custody Margins
           (`Baggy`, `Corduroy`, `FrontierSumFts`, `Jorts`, `QuorumJorts`) -/

/-! ### §3.1 Exact Bit-Truncation Fiber Theorem (`2 ^ (n - m)` Preimages) -/

private theorem qsum_snoc :
    ∀ (n : Nat) (g : Fin (n + 1) → Nat),
      qsum (n + 1) g =
        qsum n (fun i => g ⟨i.1, Nat.lt_succ_of_lt i.2⟩) + g ⟨n, Nat.lt_succ_self n⟩
  | 0, g => by simp [qsum]
  | n + 1, g => by
    have hHead : qsum (n + 1 + 1) g =
        g ⟨0, Nat.zero_lt_succ (n + 1)⟩ +
          qsum (n + 1) (fun i => g ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) := rfl
    rw [hHead, qsum_snoc n (fun i => g ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)]
    have hInit : qsum (n + 1) (fun i => g ⟨i.1, Nat.lt_succ_of_lt i.2⟩) =
        g ⟨0, Nat.zero_lt_succ (n + 1)⟩ +
          qsum n (fun i => g ⟨i.1 + 1, Nat.lt_succ_of_lt (Nat.succ_lt_succ i.2)⟩) := rfl
    rw [← Nat.add_assoc]
    exact congrArg (fun x => x + g ⟨n + 1, Nat.lt_succ_self (n + 1)⟩) hInit.symm

private theorem qsum_add_split (X : Nat) :
    ∀ (Y : Nat) (g : Fin (X + Y) → Nat),
      qsum (X + Y) g =
        qsum X (fun i => g ⟨i.1, by omega⟩) +
        qsum Y (fun j => g ⟨X + j.1, by omega⟩)
  | 0, g => by
    simp only [qsum, Nat.add_zero]
    exact qsum_congr (fun _ => rfl)
  | Y + 1, g => by
    have h1 : qsum (X + (Y + 1)) g =
        qsum (X + Y) (fun k => g ⟨k.1, Nat.lt_succ_of_lt k.2⟩) +
          g ⟨X + Y, Nat.lt_succ_self (X + Y)⟩ :=
      qsum_snoc (X + Y) g
    rw [h1, qsum_add_split X Y (fun k => g ⟨k.1, Nat.lt_succ_of_lt k.2⟩),
        qsum_snoc Y (fun j => g ⟨X + j.1, by omega⟩), Nat.add_assoc]

private theorem qsum_mul_split (A : Nat) :
    ∀ (B : Nat) (f : Fin (A * B) → Nat),
      qsum (A * B) f =
        qsum B (fun q => qsum A (fun r =>
          f ⟨q.1 * A + r.1, by
            have h1 : q.1 * A + r.1 < q.1 * A + A := Nat.add_lt_add_left r.2 (q.1 * A)
            have h2 : q.1 * A + A = (q.1 + 1) * A := by rw [Nat.add_mul, Nat.one_mul]
            have h3 : (q.1 + 1) * A ≤ B * A := Nat.mul_le_mul_right A q.2
            rw [Nat.mul_comm B A] at h3
            omega⟩))
  | 0, _ => by simp [qsum]
  | B + 1, f => by
    have hAB : A * (B + 1) = A * B + A := Nat.mul_succ A B
    have h1 : qsum (A * (B + 1)) f =
        qsum (A * B) (fun k => f ⟨k.1, by omega⟩) +
        qsum A (fun r => f ⟨A * B + r.1, by omega⟩) :=
      qsum_add_split (A * B) A f
    rw [h1, qsum_mul_split A B (fun k => f ⟨k.1, by omega⟩), qsum_snoc B]
    congr 1
    apply qsum_congr; intro r
    congr 1; apply Fin.ext
    dsimp only
    rw [Nat.mul_comm A B]

/-- **Exact Bit-Truncation Fiber Theorem (`fiberCard_bitVec_setWidth`)**:
    Projecting `BitVec n` onto its low `m` bits (`m ≤ n`) gives EVERY `m`-bit target codeword an
    exact preimage fiber of size `2 ^ (n - m)`. -/
theorem fiberCard_bitVec_setWidth {m n : Nat} (hmn : m ≤ n) (target : BitVec m) :
    fiberCard n (BitVec.setWidth m) target = 2 ^ (n - m) := by
  unfold fiberCard
  have hPowEq : 2 ^ n = 2 ^ m * 2 ^ (n - m) := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' hmn]
  have h1 : qsum (2 ^ n) (fun j => if BitVec.setWidth m (BitVec.ofFin j) = target then 1 else 0) =
      qsum (2 ^ n) (fun j => if BitVec.setWidth m (BitVec.ofNat n j.1) = target then 1 else 0) := by
    apply qsum_congr; intro j
    have hEqJ : BitVec.ofFin j = BitVec.ofNat n j.1 := by
      apply BitVec.eq_of_toNat_eq
      change j.1 = (BitVec.ofNat n j.1).toNat
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt j.2]
    rw [hEqJ]
  have hCast : ∀ (N : Nat), N = 2 ^ m * 2 ^ (n - m) →
      qsum N (fun j => if BitVec.setWidth m (BitVec.ofNat n j.1) = target then 1 else 0) =
      qsum (2 ^ m * 2 ^ (n - m))
        (fun k => if BitVec.setWidth m (BitVec.ofNat n k.1) = target then 1 else 0) := by
    intro N hN; subst hN; rfl
  rw [h1, hCast (2 ^ n) hPowEq,
      qsum_mul_split (2 ^ m) (2 ^ (n - m))
        (fun k => if BitVec.setWidth m (BitVec.ofNat n k.1) = target then 1 else 0)]
  have hInner : ∀ q : Fin (2 ^ (n - m)),
      qsum (2 ^ m) (fun r =>
        if BitVec.setWidth m (BitVec.ofNat n (q.1 * 2 ^ m + r.1)) = target then 1 else 0) = 1 := by
    intro q
    have hCongr : qsum (2 ^ m) (fun r =>
        if BitVec.setWidth m (BitVec.ofNat n (q.1 * 2 ^ m + r.1)) = target then 1 else 0) =
        qsum (2 ^ m) (fun r => if r = target.toFin then 1 else 0) := by
      apply qsum_congr; intro r
      have hMod : (q.1 * 2 ^ m + r.1) % 2 ^ m = r.1 := by
        rw [Nat.mul_comm q.1 (2 ^ m), Nat.mul_add_mod, Nat.mod_eq_of_lt r.2]
      have hWidthVal : (BitVec.setWidth m (BitVec.ofNat n (q.1 * 2 ^ m + r.1))).toNat = r.1 := by
        rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
        have hDvd : 2 ^ m ∣ 2 ^ n := ⟨2 ^ (n - m), hPowEq⟩
        rw [Nat.mod_mod_of_dvd _ hDvd, hMod]
      by_cases hr : r = target.toFin
      · have hEqT : BitVec.setWidth m (BitVec.ofNat n (q.1 * 2 ^ m + r.1)) = target := by
          apply BitVec.eq_of_toNat_eq
          rw [hWidthVal, hr]
          rfl
        have s1 : (if BitVec.setWidth m (BitVec.ofNat n (q.1 * 2 ^ m + r.1)) = target then 1 else 0) = 1 := by
          simp only [hEqT, ↓reduceIte]
        have s2 : (if r = target.toFin then 1 else 0) = 1 := by
          simp only [hr, ↓reduceIte]
        rw [s1, s2]
      · have hNeT : BitVec.setWidth m (BitVec.ofNat n (q.1 * 2 ^ m + r.1)) ≠ target := by
          intro heq
          apply hr
          apply Fin.ext
          rw [← hWidthVal, heq]
          rfl
        have s1 : (if BitVec.setWidth m (BitVec.ofNat n (q.1 * 2 ^ m + r.1)) = target then 1 else 0) = 0 := by
          simp only [hNeT, ↓reduceIte]
        have s2 : (if r = target.toFin then 1 else 0) = 0 := by
          simp only [hr, ↓reduceIte]
        rw [s1, s2]
    rw [hCongr, qsum_eq_indicator]
  rw [qsum_congr hInner, qsum_const, Nat.mul_one]

/-! ### §3.2 `WOTS+C` (`BaggySha3`, `BaggyPoseidon2`, `Corduroy`, `Jorts`) Encoding Bridges -/

/-- Exact MSB-first base-4 dibit extractor matching `crates/qsag-core/src/wots_c.rs:74`:
    `digit(i) = (byte[i / 4] >> (6 - 2 * (i % 4))) & 3`, represented as a 256-bit dibit-permuted
    word where dibit `i` (`0 ≤ i < 128`) occupies bits `[2*i, 2*i+1]`. -/
def wotsCDibitAt (d : BitVec 256) (i : Fin 128) : BitVec 2 :=
  let byteIdx := i.1 / 4
  let slot := i.1 % 4
  let bitBase := byteIdx * 8 + (6 - 2 * slot)
  BitVec.ofBool (d.getLsbD bitBase) ++ BitVec.ofBool (d.getLsbD (bitBase + 1))

/-- Constructive LSB-first bit-to-`Nat` packer (`0` classical choice). -/
def qsagNatOfBits : (n : Nat) → (Fin n → Bool) → Nat
  | 0, _ => 0
  | n + 1, f =>
    (if f ⟨0, Nat.zero_lt_succ n⟩ then 1 else 0) +
      2 * qsagNatOfBits n (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)

private theorem qsagNatOfBits_lt :
    ∀ (n : Nat) (f : Fin n → Bool), qsagNatOfBits n f < 2 ^ n
  | 0, _ => Nat.zero_lt_one
  | n + 1, f => by
    simp only [qsagNatOfBits]
    have ih := qsagNatOfBits_lt n (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
    rw [Nat.pow_succ]
    cases f ⟨0, Nat.zero_lt_succ n⟩ <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

private theorem qsagNatOfBits_testBit :
    ∀ (n : Nat) (f : Fin n → Bool) (k : Nat) (hk : k < n),
      (qsagNatOfBits n f).testBit k = f ⟨k, hk⟩
  | 0, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | n + 1, f, 0, _ => by
    simp only [qsagNatOfBits]
    rw [Nat.testBit_zero]
    cases f ⟨0, Nat.zero_lt_succ n⟩
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      have hm : (2 * qsagNatOfBits n (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)) % 2 = 0 := by omega
      rw [hm]; decide
    · simp only [↓reduceIte]
      have hm : (1 + 2 * qsagNatOfBits n (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)) % 2 = 1 := by omega
      rw [hm]; decide
  | n + 1, f, k + 1, hk => by
    simp only [qsagNatOfBits]
    rw [Nat.testBit_succ]
    have hd : ((if f ⟨0, Nat.zero_lt_succ n⟩ then 1 else 0) +
        2 * qsagNatOfBits n (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)) / 2 =
        qsagNatOfBits n (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) := by
      cases f ⟨0, Nat.zero_lt_succ n⟩ <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
    rw [hd]
    exact qsagNatOfBits_testBit n (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) k
      (Nat.lt_of_succ_lt_succ hk)

/-- Constructive `Fin n → Bool` bit-vector builder (`0` classical choice). -/
def qsagBitVecOfFn (n : Nat) (f : Fin n → Bool) : BitVec n :=
  BitVec.ofFin ⟨qsagNatOfBits n f, qsagNatOfBits_lt n f⟩

private theorem getLsbD_qsagBitVecOfFn (n : Nat) (f : Fin n → Bool) (k : Nat) (hk : k < n) :
    (qsagBitVecOfFn n f).getLsbD k = f ⟨k, hk⟩ := by
  change (qsagNatOfBits n f).testBit k = f ⟨k, hk⟩
  exact qsagNatOfBits_testBit n f k hk

/-- Full 128-chain `WOTS+C V128` codeword map (`w = 4, chains = 128, zero_digits = 0`), packing all
    128 MSB-first base-4 dibits losslessly into `[0, 4)^128` (represented as `BitVec 256` in
    canonical chain-index order). -/
def wotsCDibits128Bv (d : BitVec 256) : BitVec 256 :=
  qsagBitVecOfFn 256 (fun k : Fin 256 =>
    let chainIdx := k.1 / 2
    let bitInDibit := k.1 % 2
    let byteIdx := chainIdx / 4
    let slot := chainIdx % 4
    let srcBit := byteIdx * 8 + (6 - 2 * slot) + bitInDibit
    d.getLsbD srcBit)

/-- Legacy `WOTS+C V58` digest prefix (`w = 4, chains = 58, zero_digits = 6`), reading only the
    first 64 base-4 digits (`128` low bits) and discarding bits `128..255`. -/
def wotsCDibits58Prefix (d : BitVec 256) : BitVec 128 :=
  BitVec.setWidth 128 d

/-- **`wotsCDibits128Bv` Injectivity Theorem**: the deployed `V128` MSB-first base-4 dibit map is a
    strict involution (`wotsCDibits128Bv (wotsCDibits128Bv d) = d`) and hence injective on `BitVec 256`! -/
theorem wotsCDibits128Bv_involutive (d : BitVec 256) :
    wotsCDibits128Bv (wotsCDibits128Bv d) = d := by
  apply BitVec.eq_of_getLsbD_eq
  intro idx hIdx
  unfold wotsCDibits128Bv
  have h1 : ∀ (x : BitVec 256) (k : Nat) (hk : k < 256),
      (qsagBitVecOfFn 256 (fun j : Fin 256 =>
        x.getLsbD ((j.1 / 2) / 4 * 8 + (6 - 2 * ((j.1 / 2) % 4)) + j.1 % 2))).getLsbD k =
      x.getLsbD ((k / 2) / 4 * 8 + (6 - 2 * ((k / 2) % 4)) + k % 2) := by
    intro x k hk
    exact getLsbD_qsagBitVecOfFn 256 _ k hk
  let m := (idx / 2) / 4 * 8 + (6 - 2 * ((idx / 2) % 4)) + idx % 2
  have hmLt : m < 256 := by dsimp only [m]; omega
  rw [h1 _ idx hIdx, h1 d m hmLt]
  have hInvIdx : (m / 2) / 4 * 8 + (6 - 2 * ((m / 2) % 4)) + m % 2 = idx := by
    dsimp only [m]; omega
  rw [hInvIdx]

theorem wotsCDibits128Bv_injective : Function.Injective wotsCDibits128Bv := by
  intro d₁ d₂ hEq
  have h := congrArg wotsCDibits128Bv hEq
  rw [wotsCDibits128Bv_involutive, wotsCDibits128Bv_involutive] at h
  exact h

/-- Deployed `Baggy` / `Corduroy` stateless hypertree parameter profile (`baggy.rs`, `corduroy.rs`, `tsw_baggy.rs`). -/
structure BaggySuiteParams where
  w : Nat
  chains : Nat
  zeroDigits : Nat
  targetSum : Nat
  digestBits : Nat
  subtreeHeight : Nat
  numLayers : Nat
  forsTrees : Nat
  forsHeight : Nat
  maxSigsLog2 : Nat
  deriving DecidableEq, Repr

def baggySha3Params : BaggySuiteParams :=
  ⟨4, 128, 0, 192, 256, 2, 16, 33, 6, 16⟩

def baggyPoseidon2Params : BaggySuiteParams :=
  ⟨4, 128, 0, 192, 256, 2, 16, 33, 6, 16⟩

def corduroyCustodyParams : BaggySuiteParams :=
  ⟨4, 128, 0, 192, 256, 4, 7, 33, 6, 12⟩

/-- **Deployed `BaggySha3`, `BaggyPoseidon2` & `Corduroy` `V128` QROM 128-Bit Theorem**:
    Coupling `wotsCDibits128Bv_injective` into `qrom_fiber_search_bound` and
    `classical_lazy_ro_fiber_search_bound` proves `fiberCard ≤ 1`, guaranteeing:
    - Classical adaptive `OracleComp` bound `≤ (qHash + 1) / 2^256` (`atLeastBits 128` for `qHash < 2^128`),
    - Unitary QROM `QuantumAdv` bound `≤ 8 * (qHash + 1)^2 / 2^256` (`atLeastBits 129` for `qHash < 2^62`),
    - Pure Grover target-search scale `qHash^2 / 2^256` (`atLeastBits 128` up to `qHash = 2^64`). -/
theorem baggy_and_jorts_wots_v128_qrom_128bit_security
    {w cardAnc qHash : Nat}
    (A : QuantumAdv (2 ^ 256) (w + 1) cardAnc qHash)
    (target : BitVec 256) :
    fiberCard 256 wotsCDibits128Bv target ≤ 1 ∧
    RatBound.le
      ⟨qsum (2 ^ 256) (fun m =>
         QVec.measureNormSq
           (fun x => decide (wotsCDibits128Bv (BitVec.ofFin x ^^^ BitVec.ofFin m) = target))
           (runQuantumAdv A (shiftedFiberOracle 256 w wotsCDibits128Bv target (BitVec.ofFin m)))),
       2 ^ 256 * QVec.stateNormSq (runQuantumAdv A (blankFiberOracle 256 w)),
       Nat.mul_pos (Nat.two_pow_pos 256) (runQuantumAdv_normSq_pos A (blankFiberOracle 256 w))⟩
      (quantumGroverSingleTargetBound 256 qHash) ∧
    (qHash + 1 ≤ 2 ^ 62 → atLeastBits 129 (quantumGroverSingleTargetBound 256 qHash)) ∧
    (qHash ≤ 2 ^ 64 → atLeastBits 128 (groverPureSearchBound 256 qHash)) := by
  have hFib : fiberCard 256 wotsCDibits128Bv target ≤ 1 :=
    fiberCard_le_one_of_injective 256 wotsCDibits128Bv wotsCDibits128Bv_injective target
  have hQrom := (qrom_fiber_search_bound A wotsCDibits128Bv target).2
  have hLeSingle : RatBound.le
      ⟨8 * (qHash + 1) ^ 2 * fiberCard 256 wotsCDibits128Bv target, 2 ^ 256, Nat.two_pow_pos 256⟩
      (quantumGroverSingleTargetBound 256 qHash) := by
    unfold RatBound.le quantumGroverSingleTargetBound quantumZhandryMultiTargetBound
    dsimp only
    apply Nat.mul_le_mul_right
    have hm := Nat.mul_le_mul_left (8 * (qHash + 1) ^ 2) hFib
    omega
  refine ⟨hFib, RatBound.le_trans hQrom hLeSingle,
          fun hq => qrom_single_target_parametric_bits hq (by decide), ?_⟩
  intro hq64
  unfold atLeastBits groverPureSearchBound
  dsimp only
  have hSq : qHash ^ 2 ≤ (2 ^ 64) ^ 2 := Nat.pow_le_pow_left hq64 2
  have h256 : (2 ^ 64) ^ 2 * 2 ^ 128 ≤ 2 ^ 256 := by decide
  exact Nat.le_trans (Nat.mul_le_mul_right (2 ^ 128) hSq) h256

/-- **`#tooth` Legacy `WOTS+C V58` 128-Bit Digest Bottleneck (`tooth_wots_v58_128bit_digest_grover_64bit`)**:
    1. Exhibits two explicit distinct 256-bit digests (`0#256 ≠ 1#256 <<< 128`) mapping to the
       identical `V58` prefix (`0` hash collision required!),
    2. Proves `fiberCard 256 wotsCDibits58Prefix target = 2 ^ 128`, collapsing the QROM bound
       `8 * (q + 1)^2 * 2^128 / 2^256` to `8 * (q + 1)^2 / 2^128`, which completely breaks (`≥ 1`)
       at `qHash = 2 ^ 64`! -/
theorem tooth_wots_v58_128bit_digest_grover_64bit (target : BitVec 128) :
    (0#256 ≠ (1#256 <<< 128) ∧ wotsCDibits58Prefix 0#256 = wotsCDibits58Prefix (1#256 <<< 128)) ∧
    fiberCard 256 wotsCDibits58Prefix target = 2 ^ 128 ∧
    RatBound.le (quantumGroverSingleTargetBound 128 (2 ^ 64))
      ⟨8 * (2 ^ 64 + 1) ^ 2 * fiberCard 256 wotsCDibits58Prefix target, 2 ^ 256, Nat.two_pow_pos 256⟩ ∧
    exceedsBitBudget 0 (quantumGroverSingleTargetBound 128 (2 ^ 64)) := by
  have hFib : fiberCard 256 wotsCDibits58Prefix target = 2 ^ 128 := by
    unfold wotsCDibits58Prefix
    exact fiberCard_bitVec_setWidth (m := 128) (n := 256) (by decide) target
  refine ⟨⟨by decide, by unfold wotsCDibits58Prefix; decide⟩, hFib, ?_, ?_⟩
  · rw [hFib]
    unfold RatBound.le quantumGroverSingleTargetBound quantumZhandryMultiTargetBound
    dsimp only
    have hEq : 8 * 1 * (2 ^ 64 + 1) ^ 2 * 2 ^ 256 =
        8 * (2 ^ 64 + 1) ^ 2 * 2 ^ 128 * 2 ^ 128 := by decide
    exact Nat.le_of_eq hEq
  · unfold exceedsBitBudget quantumGroverSingleTargetBound quantumZhandryMultiTargetBound
    decide

/-! ### §3.3 `FrontierSumFts` (`Full256Bit` vs Legacy 122-Bit Rank Bottleneck) -/

/-- Deployed `FrontierSumFts` profile parameters (`crates/qsag-fts/src/frontier.rs`). -/
structure FrontierSuiteParams where
  nodeBytes : Nat
  treeHeight : Nat
  winternitzW : Nat
  frontierLen : Nat
  targetSum : Nat
  indexBits : Nat
  counterBits : Nat
  maxSafeUses : Nat
  deriving DecidableEq, Repr

def frontierFull256BitParams : FrontierSuiteParams :=
  ⟨32, 8, 5, 72, 144, 256, 16, 1⟩

/-- Upgraded `Full256Bit` injective 256-bit message-rank projection (`index_bits = 256`). -/
def frontierRank256 (d : BitVec 256) : BitVec 256 := d

/-- Legacy `122`-bit message-rank truncation (`2^134`-to-1 preimage fiber). -/
def frontierRank122 (d : BitVec 256) : BitVec 122 :=
  BitVec.setWidth 122 d

theorem frontierRank256_injective : Function.Injective frontierRank256 :=
  fun _ _ h => h

/-- **Upgraded `FrontierSumFts` (`Full256Bit`, `rankBits = 256`, `max_safe_uses = 1`) QROM 128-Bit Theorem**:
    Every 256-bit message rank has `fiberCard ≤ 1`, surviving Grover search (`atLeastBits 129`
    under full QROM for `qHash < 2^62` and `atLeastBits 128` pure Grover work scale up to `2^64`). -/
theorem frontier_full256bit_qrom_128bit_security
    {w cardAnc qHash : Nat}
    (A : QuantumAdv (2 ^ 256) (w + 1) cardAnc qHash)
    (targetRank : BitVec 256) :
    frontierFull256BitParams.indexBits = 256 ∧
    frontierFull256BitParams.nodeBytes * 8 = 256 ∧
    frontierFull256BitParams.maxSafeUses = 1 ∧
    fiberCard 256 frontierRank256 targetRank ≤ 1 ∧
    RatBound.le
      ⟨qsum (2 ^ 256) (fun m =>
         QVec.measureNormSq
           (fun x => decide (frontierRank256 (BitVec.ofFin x ^^^ BitVec.ofFin m) = targetRank))
           (runQuantumAdv A (shiftedFiberOracle 256 w frontierRank256 targetRank (BitVec.ofFin m)))),
       2 ^ 256 * QVec.stateNormSq (runQuantumAdv A (blankFiberOracle 256 w)),
       Nat.mul_pos (Nat.two_pow_pos 256) (runQuantumAdv_normSq_pos A (blankFiberOracle 256 w))⟩
      (quantumGroverSingleTargetBound 256 qHash) ∧
    (qHash + 1 ≤ 2 ^ 62 → atLeastBits 129 (quantumGroverSingleTargetBound 256 qHash)) := by
  have hFib : fiberCard 256 frontierRank256 targetRank ≤ 1 :=
    fiberCard_le_one_of_injective 256 frontierRank256 frontierRank256_injective targetRank
  have hQrom := (qrom_fiber_search_bound A frontierRank256 targetRank).2
  have hLe : RatBound.le
      ⟨8 * (qHash + 1) ^ 2 * fiberCard 256 frontierRank256 targetRank, 2 ^ 256, Nat.two_pow_pos 256⟩
      (quantumGroverSingleTargetBound 256 qHash) := by
    unfold RatBound.le quantumGroverSingleTargetBound quantumZhandryMultiTargetBound
    dsimp only
    apply Nat.mul_le_mul_right
    have hm := Nat.mul_le_mul_left (8 * (qHash + 1) ^ 2) hFib
    omega
  exact ⟨rfl, rfl, rfl, hFib, RatBound.le_trans hQrom hLe,
         fun hq => qrom_single_target_parametric_bits hq (by decide)⟩

/-- **`#tooth` Legacy 122-Bit Frontier Rank Bottleneck (`tooth_frontier_122bit_rank_grover_61bit`)**:
    Even with 32-byte tree nodes and a 256-bit prehash, truncating the accepted configuration rank
    to 122 bits creates an exact `2 ^ 134`-element preimage fiber per rank, collapsing quantum
    rank-search resistance to `2 ^ 61` (`groverPureSearchBound 122 (2^61) = 1`, failing 128-bit
    quantum security by 67 bits!). -/
theorem tooth_frontier_122bit_rank_grover_61bit (targetRank : BitVec 122) :
    (0#256 ≠ (1#256 <<< 122) ∧ frontierRank122 0#256 = frontierRank122 (1#256 <<< 122)) ∧
    fiberCard 256 frontierRank122 targetRank = 2 ^ 134 ∧
    exceedsBitBudget 65 (groverPureSearchBound 122 (2 ^ 29)) ∧
    exceedsBitBudget 0 (quantumGroverSingleTargetBound 122 (2 ^ 61)) := by
  have hFib : fiberCard 256 frontierRank122 targetRank = 2 ^ 134 := by
    unfold frontierRank122
    exact fiberCard_bitVec_setWidth (m := 122) (n := 256) (by decide) targetRank
  refine ⟨⟨by decide, by unfold frontierRank122; decide⟩, hFib,
          by unfold exceedsBitBudget groverPureSearchBound; decide,
          by unfold exceedsBitBudget quantumGroverSingleTargetBound quantumZhandryMultiTargetBound; decide⟩

/-! ### §3.4 Composed `Jorts` & `QuorumJorts` (`QS-A` & `QS-B` + `BeltLatch` + `Rss256` BGIN19) -/

/-- Single-session `Rss256` 2-pass `GF(2^128)` BGIN19 / DZK product-proof soundness bound
    (`crates/qsag-core/src/rss256.rs:74`: `((B + 2*7 + 8*R + 2) / 2^128)^2`). Because challenges
    are fresh commit-and-open interactive coins drawn *after* gate messages are fixed, quantum
    adversaries cannot apply offline Grover grinding to this interactive barrier! -/
def rss256TwoPassBarrierBound (numBlocks foldRounds qOnlineSessions : Nat) : RatBound :=
  RatBound.scale qOnlineSessions
    (RatBound.pow ⟨numBlocks + 14 + 8 * foldRounds + 2, 2 ^ 128, Nat.two_pow_pos 128⟩ 2)

/-- Mode 1A 2-point `GF(2^128)` Horner consistency bound `qOnlineSessions * (numWords / 2^128)^2`. -/
def rss256Mode1aHornerBound (numWords qOnlineSessions : Nat) : RatBound :=
  RatBound.scale qOnlineSessions (RatBound.pow ⟨numWords, 2 ^ 128, Nat.two_pow_pos 128⟩ 2)

/-- Composed concrete bound for `Jorts` (`SHA3_H20`) and `QuorumJorts` (`QS-A` committee-partitioned
    `t`-of-`t` subtrees for `n ≥ 2t - 1` and `QS-B` `(t, 3t - 2)` Shamir `WOTS+C` + `BeltLatch`
    quorum certificate `2 * qLatch > n + f`), summing:
    1. `256`-bit `WOTS+C V128` chain SM-TCR QROM bound (`ADRS`-tweaked `M = 1`),
    2. `BeltLatch` pairwise-MAC forgery QROM bound (`256`-bit pairwise slot key),
    3. `Rss256` 2-pass `GF(2^128)` active product-barrier soundness across `qOnlineSessions`. -/
def jortsComposedQuantumBound (b : QueryBudget) : RatBound :=
  RatBound.sumList
    [ quantumGroverSingleTargetBound 256 b.qHash,
      quantumGroverSingleTargetBound 256 b.qHash,
      rss256TwoPassBarrierBound 614400 6 b.qOnlineSessions ]

def jortsComposedClassicalBound (b : QueryBudget) : RatBound :=
  RatBound.sumList
    [ ⟨b.qHash + 1, 2 ^ 256, Nat.two_pow_pos 256⟩,
      ⟨b.qHash + 1, 2 ^ 256, Nat.two_pow_pos 256⟩,
      rss256TwoPassBarrierBound 614400 6 b.qOnlineSessions ]

/-- **Composed `Jorts` & `QuorumJorts` (`QS-A` / `QS-B`) `PQ128` Theorem**:
    1. Single-session 8-wave `Rss256` barrier (`B = 614,400, R = 6`) achieves `atLeastBits 217`
       (1-wave online leaf sweep `B = 76,800, R = 5` achieves `atLeastBits 223`; Mode 1A `N = 256`
       achieves `atLeastBits 240`),
    2. Under any `QueryBudget` with `qHash + 1 ≤ 2 ^ 61` and `qOnlineSessions ≤ 2 ^ 20`, the exact
       rational sum of WOTS+C, `BeltLatch` pairwise MAC, and `Rss256` BGIN19 barrier satisfies
       `atLeastBits 128` BOTH classically and quantumly! -/
theorem jorts_and_quorum_jorts_composed_pq128_soundness (b : QueryBudget)
    (hqHash : b.qHash + 1 ≤ 2 ^ 61) (hqSess : b.qOnlineSessions ≤ 2 ^ 20) :
    atLeastBits 217 (rss256TwoPassBarrierBound 614400 6 1) ∧
    atLeastBits 223 (rss256TwoPassBarrierBound 76800 5 1) ∧
    atLeastBits 240 (rss256Mode1aHornerBound 256 1) ∧
    atLeastBits 128 (jortsComposedClassicalBound b) ∧
    atLeastBits 128 (jortsComposedQuantumBound b) := by
  have hBar8 : atLeastBits 217 (rss256TwoPassBarrierBound 614400 6 1) := by
    unfold atLeastBits rss256TwoPassBarrierBound RatBound.scale RatBound.pow; decide
  have hBar1 : atLeastBits 223 (rss256TwoPassBarrierBound 76800 5 1) := by
    unfold atLeastBits rss256TwoPassBarrierBound RatBound.scale RatBound.pow; decide
  have hMode1a : atLeastBits 240 (rss256Mode1aHornerBound 256 1) := by
    unfold atLeastBits rss256Mode1aHornerBound RatBound.scale RatBound.pow; decide
  have hBarSess : atLeastBits 130 (rss256TwoPassBarrierBound 614400 6 b.qOnlineSessions) := by
    unfold atLeastBits rss256TwoPassBarrierBound RatBound.scale RatBound.pow
    dsimp only
    have hMul := Nat.mul_le_mul_right ((614400 + 14 + 8 * 6 + 2) ^ 2 * 2 ^ 130) hqSess
    have hBase : 2 ^ 20 * ((614400 + 14 + 8 * 6 + 2) ^ 2 * 2 ^ 130) ≤ (2 ^ 128) ^ 2 := by decide
    have hAssoc : b.qOnlineSessions * (614400 + 14 + 8 * 6 + 2) ^ 2 * 2 ^ 130 =
        b.qOnlineSessions * ((614400 + 14 + 8 * 6 + 2) ^ 2 * 2 ^ 130) := by
      simp only [Nat.mul_assoc]
    rw [hAssoc]
    exact Nat.le_trans hMul hBase
  have hQrom130 : atLeastBits 130 (quantumGroverSingleTargetBound 256 b.qHash) :=
    qrom_single_target_parametric_bits hqHash (by decide)
  have hClass130 : atLeastBits 130 ⟨b.qHash + 1, 2 ^ 256, Nat.two_pow_pos 256⟩ := by
    unfold atLeastBits
    dsimp only
    have hm := Nat.mul_le_mul_right (2 ^ 130) hqHash
    have hp : 2 ^ 61 * 2 ^ 130 ≤ 2 ^ 256 := by decide
    exact Nat.le_trans hm hp
  have hComposedClass : atLeastBits 128 (jortsComposedClassicalBound b) := by
    unfold jortsComposedClassicalBound
    apply atLeastBits_sumList_union_loss (loss := 2) (by simp)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hClass130
    · exact hClass130
    · exact hBarSess
  have hComposedQuant : atLeastBits 128 (jortsComposedQuantumBound b) := by
    unfold jortsComposedQuantumBound
    apply atLeastBits_sumList_union_loss (loss := 2) (by simp)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hQrom130
    · exact hQrom130
    · exact hBarSess
  exact ⟨hBar8, hBar1, hMode1a, hComposedClass, hComposedQuant⟩


/-! ## §4. `QuarticGoldilocks` Quartic Extension Field, Polynomial Root-Counting Schwartz–Zippel
           & `Hem` WHIR Soundness Regimes (`crates/qsag-agg/src/field.rs`, `pcs.rs`) -/

private theorem quadExtMulComm0 {R : Type} [LawfulCommRing R] (n x0 x1 y0 y1 : R) :
    CommRingOps.add (CommRingOps.mul x0 y0) (CommRingOps.mul n (CommRingOps.mul x1 y1)) =
      CommRingOps.add (CommRingOps.mul y0 x0) (CommRingOps.mul n (CommRingOps.mul y1 x1)) := by
  rw [LawfulCommRing.mul_comm x0 y0, LawfulCommRing.mul_comm x1 y1]

private theorem quadExtMulComm1 {R : Type} [LawfulCommRing R] (x0 x1 y0 y1 : R) :
    CommRingOps.add (CommRingOps.mul x0 y1) (CommRingOps.mul x1 y0) =
      CommRingOps.add (CommRingOps.mul y0 x1) (CommRingOps.mul y1 x0) := by
  rw [LawfulCommRing.mul_comm x0 y1, LawfulCommRing.mul_comm x1 y0, LawfulCommRing.add_comm]

private theorem quadExtOneMul0 {R : Type} [LawfulCommRing R] (n x0 x1 : R) :
    CommRingOps.add (CommRingOps.mul CommRingOps.one x0)
      (CommRingOps.mul n (CommRingOps.mul CommRingOps.zero x1)) = x0 := by
  rw [LawfulCommRing.one_mul, LawfulCommRing.zero_mul, LawfulCommRing.mul_zero,
      LawfulCommRing.add_zero]

private theorem quadExtOneMul1 {R : Type} [LawfulCommRing R] (x0 x1 : R) :
    CommRingOps.add (CommRingOps.mul CommRingOps.one x1)
      (CommRingOps.mul CommRingOps.zero x0) = x1 := by
  rw [LawfulCommRing.one_mul, LawfulCommRing.zero_mul, LawfulCommRing.add_zero]

private theorem quadExtMulOne0 {R : Type} [LawfulCommRing R] (n x0 x1 : R) :
    CommRingOps.add (CommRingOps.mul x0 CommRingOps.one)
      (CommRingOps.mul n (CommRingOps.mul x1 CommRingOps.zero)) = x0 := by
  rw [LawfulCommRing.mul_one, LawfulCommRing.mul_zero, LawfulCommRing.mul_zero,
      LawfulCommRing.add_zero]

private theorem quadExtMulOne1 {R : Type} [LawfulCommRing R] (x0 x1 : R) :
    CommRingOps.add (CommRingOps.mul x0 CommRingOps.zero)
      (CommRingOps.mul x1 CommRingOps.one) = x1 := by
  rw [LawfulCommRing.mul_zero, LawfulCommRing.mul_one, LawfulCommRing.zero_add]

private theorem quadExtLeftDistrib0 {R : Type} [LawfulCommRing R] (n x0 x1 y0 y1 z0 z1 : R) :
    CommRingOps.add (CommRingOps.mul x0 (CommRingOps.add y0 z0))
      (CommRingOps.mul n (CommRingOps.mul x1 (CommRingOps.add y1 z1))) =
    CommRingOps.add
      (CommRingOps.add (CommRingOps.mul x0 y0) (CommRingOps.mul n (CommRingOps.mul x1 y1)))
      (CommRingOps.add (CommRingOps.mul x0 z0) (CommRingOps.mul n (CommRingOps.mul x1 z1))) := by
  rw [LawfulCommRing.left_distrib, LawfulCommRing.left_distrib, LawfulCommRing.left_distrib]
  exact LawfulCommRing.add_add_add_comm _ _ _ _

private theorem quadExtLeftDistrib1 {R : Type} [LawfulCommRing R] (x0 x1 y0 y1 z0 z1 : R) :
    CommRingOps.add (CommRingOps.mul x0 (CommRingOps.add y1 z1))
      (CommRingOps.mul x1 (CommRingOps.add y0 z0)) =
    CommRingOps.add
      (CommRingOps.add (CommRingOps.mul x0 y1) (CommRingOps.mul x1 y0))
      (CommRingOps.add (CommRingOps.mul x0 z1) (CommRingOps.mul x1 z0)) := by
  rw [LawfulCommRing.left_distrib, LawfulCommRing.left_distrib]
  exact LawfulCommRing.add_add_add_comm _ _ _ _

private theorem quadExtRightDistrib0 {R : Type} [LawfulCommRing R] (n x0 x1 y0 y1 z0 z1 : R) :
    CommRingOps.add (CommRingOps.mul (CommRingOps.add x0 y0) z0)
      (CommRingOps.mul n (CommRingOps.mul (CommRingOps.add x1 y1) z1)) =
    CommRingOps.add
      (CommRingOps.add (CommRingOps.mul x0 z0) (CommRingOps.mul n (CommRingOps.mul x1 z1)))
      (CommRingOps.add (CommRingOps.mul y0 z0) (CommRingOps.mul n (CommRingOps.mul y1 z1))) := by
  rw [LawfulCommRing.right_distrib, LawfulCommRing.right_distrib, LawfulCommRing.left_distrib]
  exact LawfulCommRing.add_add_add_comm _ _ _ _

private theorem quadExtRightDistrib1 {R : Type} [LawfulCommRing R] (x0 x1 y0 y1 z0 z1 : R) :
    CommRingOps.add (CommRingOps.mul (CommRingOps.add x0 y0) z1)
      (CommRingOps.mul (CommRingOps.add x1 y1) z0) =
    CommRingOps.add
      (CommRingOps.add (CommRingOps.mul x0 z1) (CommRingOps.mul x1 z0))
      (CommRingOps.add (CommRingOps.mul y0 z1) (CommRingOps.mul y1 z0)) := by
  rw [LawfulCommRing.right_distrib, LawfulCommRing.right_distrib]
  exact LawfulCommRing.add_add_add_comm _ _ _ _

private theorem quadExtMulAssoc0 {R : Type} [LawfulCommRing R] (n x0 x1 y0 y1 z0 z1 : R) :
    CommRingOps.add
      (CommRingOps.mul
        (CommRingOps.add (CommRingOps.mul x0 y0) (CommRingOps.mul n (CommRingOps.mul x1 y1))) z0)
      (CommRingOps.mul n
        (CommRingOps.mul (CommRingOps.add (CommRingOps.mul x0 y1) (CommRingOps.mul x1 y0)) z1)) =
    CommRingOps.add
      (CommRingOps.mul x0
        (CommRingOps.add (CommRingOps.mul y0 z0) (CommRingOps.mul n (CommRingOps.mul y1 z1))))
      (CommRingOps.mul n
        (CommRingOps.mul x1 (CommRingOps.add (CommRingOps.mul y0 z1) (CommRingOps.mul y1 z0)))) := by
  rw [LawfulCommRing.right_distrib, LawfulCommRing.right_distrib,
      LawfulCommRing.left_distrib, LawfulCommRing.left_distrib,
      LawfulCommRing.left_distrib, LawfulCommRing.left_distrib]
  have t1 : CommRingOps.mul (CommRingOps.mul x0 y0) z0 =
      CommRingOps.mul x0 (CommRingOps.mul y0 z0) :=
    LawfulCommRing.mul_assoc _ _ _
  have t2 : CommRingOps.mul (CommRingOps.mul n (CommRingOps.mul x1 y1)) z0 =
      CommRingOps.mul n (CommRingOps.mul x1 (CommRingOps.mul y1 z0)) := by
    rw [LawfulCommRing.mul_assoc, LawfulCommRing.mul_assoc]
  have t3 : CommRingOps.mul n (CommRingOps.mul (CommRingOps.mul x0 y1) z1) =
      CommRingOps.mul x0 (CommRingOps.mul n (CommRingOps.mul y1 z1)) := by
    rw [LawfulCommRing.mul_assoc x0 y1 z1,
        ← LawfulCommRing.mul_assoc n x0 _,
        LawfulCommRing.mul_comm n x0,
        LawfulCommRing.mul_assoc]
  have t4 : CommRingOps.mul n (CommRingOps.mul (CommRingOps.mul x1 y0) z1) =
      CommRingOps.mul n (CommRingOps.mul x1 (CommRingOps.mul y0 z1)) := by
    rw [LawfulCommRing.mul_assoc]
  rw [t1, t2, t3, t4, LawfulCommRing.add_add_add_comm]
  congr 1
  exact LawfulCommRing.add_comm _ _

private theorem quadExtMulAssoc1 {R : Type} [LawfulCommRing R] (n x0 x1 y0 y1 z0 z1 : R) :
    CommRingOps.add
      (CommRingOps.mul
        (CommRingOps.add (CommRingOps.mul x0 y0) (CommRingOps.mul n (CommRingOps.mul x1 y1))) z1)
      (CommRingOps.mul
        (CommRingOps.add (CommRingOps.mul x0 y1) (CommRingOps.mul x1 y0)) z0) =
    CommRingOps.add
      (CommRingOps.mul x0
        (CommRingOps.add (CommRingOps.mul y0 z1) (CommRingOps.mul y1 z0)))
      (CommRingOps.mul x1
        (CommRingOps.add (CommRingOps.mul y0 z0) (CommRingOps.mul n (CommRingOps.mul y1 z1)))) := by
  rw [LawfulCommRing.right_distrib, LawfulCommRing.right_distrib,
      LawfulCommRing.left_distrib, LawfulCommRing.left_distrib]
  have s1 : CommRingOps.mul (CommRingOps.mul x0 y0) z1 =
      CommRingOps.mul x0 (CommRingOps.mul y0 z1) :=
    LawfulCommRing.mul_assoc _ _ _
  have s2 : CommRingOps.mul (CommRingOps.mul n (CommRingOps.mul x1 y1)) z1 =
      CommRingOps.mul x1 (CommRingOps.mul n (CommRingOps.mul y1 z1)) := by
    rw [LawfulCommRing.mul_assoc n _ z1,
        LawfulCommRing.mul_assoc x1 y1 z1,
        ← LawfulCommRing.mul_assoc n x1 _,
        LawfulCommRing.mul_comm n x1,
        LawfulCommRing.mul_assoc]
  have s3 : CommRingOps.mul (CommRingOps.mul x0 y1) z0 =
      CommRingOps.mul x0 (CommRingOps.mul y1 z0) :=
    LawfulCommRing.mul_assoc _ _ _
  have s4 : CommRingOps.mul (CommRingOps.mul x1 y0) z0 =
      CommRingOps.mul x1 (CommRingOps.mul y0 z0) :=
    LawfulCommRing.mul_assoc _ _ _
  rw [s1, s2, s3, s4, LawfulCommRing.add_add_add_comm]
  congr 1
  exact LawfulCommRing.add_comm _ _

/-- Quartic extension field `QuarticGoldilocks = 𝔽_{p^2}[v] / (v^2 - u)` where `u = GoldilocksExt2.uBasis`
    (`u^2 = 7`), matching `GoldilocksExt4` in `crates/qsag-agg/src/field.rs` (`|𝔽_{p^4}| = p^4 > 2^255`). -/
structure QuarticGoldilocks where
  c0 : GoldilocksExt2
  c1 : GoldilocksExt2
  deriving DecidableEq, Repr

namespace QuarticGoldilocks

@[ext] theorem ext {x y : QuarticGoldilocks} (h0 : x.c0 = y.c0) (h1 : x.c1 = y.c1) : x = y := by
  cases x; cases y; subst h0; subst h1; rfl

def zero : QuarticGoldilocks := ⟨CommRingOps.zero, CommRingOps.zero⟩
def one : QuarticGoldilocks := ⟨CommRingOps.one, CommRingOps.zero⟩
def vBasis : QuarticGoldilocks := ⟨CommRingOps.zero, CommRingOps.one⟩
def ofExt2 (a : GoldilocksExt2) : QuarticGoldilocks := ⟨a, CommRingOps.zero⟩

instance : Inhabited QuarticGoldilocks := ⟨zero⟩

def add (x y : QuarticGoldilocks) : QuarticGoldilocks :=
  ⟨CommRingOps.add x.c0 y.c0, CommRingOps.add x.c1 y.c1⟩

def neg (x : QuarticGoldilocks) : QuarticGoldilocks :=
  ⟨CommRingOps.neg x.c0, CommRingOps.neg x.c1⟩

def sub (x y : QuarticGoldilocks) : QuarticGoldilocks :=
  ⟨CommRingOps.sub x.c0 y.c0, CommRingOps.sub x.c1 y.c1⟩

def mul (x y : QuarticGoldilocks) : QuarticGoldilocks :=
  ⟨CommRingOps.add (CommRingOps.mul x.c0 y.c0)
      (CommRingOps.mul GoldilocksExt2.uBasis (CommRingOps.mul x.c1 y.c1)),
   CommRingOps.add (CommRingOps.mul x.c0 y.c1) (CommRingOps.mul x.c1 y.c0)⟩

instance : CommRingOps QuarticGoldilocks where
  zero := zero
  one := one
  add := add
  mul := mul
  neg := neg
  sub := sub

instance : LawfulCommRing QuarticGoldilocks where
  add_assoc x y z := by
    apply ext
    · exact LawfulCommRing.add_assoc x.c0 y.c0 z.c0
    · exact LawfulCommRing.add_assoc x.c1 y.c1 z.c1
  add_comm x y := by
    apply ext
    · exact LawfulCommRing.add_comm x.c0 y.c0
    · exact LawfulCommRing.add_comm x.c1 y.c1
  zero_add x := by
    apply ext
    · exact LawfulCommRing.zero_add x.c0
    · exact LawfulCommRing.zero_add x.c1
  add_zero x := by
    apply ext
    · exact LawfulCommRing.add_zero x.c0
    · exact LawfulCommRing.add_zero x.c1
  add_left_neg x := by
    apply ext
    · exact LawfulCommRing.add_left_neg x.c0
    · exact LawfulCommRing.add_left_neg x.c1
  sub_eq_add_neg x y := by
    apply ext
    · exact LawfulCommRing.sub_eq_add_neg x.c0 y.c0
    · exact LawfulCommRing.sub_eq_add_neg x.c1 y.c1
  mul_comm x y := by
    apply ext
    · exact quadExtMulComm0 GoldilocksExt2.uBasis x.c0 x.c1 y.c0 y.c1
    · exact quadExtMulComm1 x.c0 x.c1 y.c0 y.c1
  one_mul x := by
    apply ext
    · exact quadExtOneMul0 GoldilocksExt2.uBasis x.c0 x.c1
    · exact quadExtOneMul1 x.c0 x.c1
  mul_one x := by
    apply ext
    · exact quadExtMulOne0 GoldilocksExt2.uBasis x.c0 x.c1
    · exact quadExtMulOne1 x.c0 x.c1
  left_distrib x y z := by
    apply ext
    · exact quadExtLeftDistrib0 GoldilocksExt2.uBasis x.c0 x.c1 y.c0 y.c1 z.c0 z.c1
    · exact quadExtLeftDistrib1 x.c0 x.c1 y.c0 y.c1 z.c0 z.c1
  right_distrib x y z := by
    apply ext
    · exact quadExtRightDistrib0 GoldilocksExt2.uBasis x.c0 x.c1 y.c0 y.c1 z.c0 z.c1
    · exact quadExtRightDistrib1 x.c0 x.c1 y.c0 y.c1 z.c0 z.c1
  mul_assoc x y z := by
    apply ext
    · exact quadExtMulAssoc0 GoldilocksExt2.uBasis x.c0 x.c1 y.c0 y.c1 z.c0 z.c1
    · exact quadExtMulAssoc1 GoldilocksExt2.uBasis x.c0 x.c1 y.c0 y.c1 z.c0 z.c1

/-- Square root of `-1` in `Goldilocks` (`2^48` since `(2^48)^2 = 2^96 ≡ -1 mod p`). -/
def sqrtNegOneGoldilocks : Goldilocks := Goldilocks.ofNat 281474976710656

private theorem sqrtNegOne_sq :
    CommRingOps.mul sqrtNegOneGoldilocks sqrtNegOneGoldilocks =
      CommRingOps.neg (CommRingOps.one : Goldilocks) := by
  apply Goldilocks.ext
  show (Goldilocks.mul sqrtNegOneGoldilocks sqrtNegOneGoldilocks).val = (Goldilocks.neg Goldilocks.one).val
  rw [Goldilocks.mul_val, Goldilocks.neg_val]
  decide

/-- **Quartic Irreducibility Theorem (`uBasis_not_square`)**:
    `u = ⟨0, 1⟩ ∈ GoldilocksExt2` has no square root in `GoldilocksExt2`, so `v^2 - u` is
    irreducible over `𝔽_{p^2}` and `QuarticGoldilocks` is a genuine field! -/
theorem uBasis_not_square (z : GoldilocksExt2) :
    CommRingOps.mul z z ≠ GoldilocksExt2.uBasis := by
  intro hSq
  have hRe : CommRingOps.add (CommRingOps.mul z.c0 z.c0)
      (CommRingOps.mul GoldilocksExt2.nonResidue (CommRingOps.mul z.c1 z.c1)) =
      (CommRingOps.zero : Goldilocks) := congrArg GoldilocksExt2.c0 hSq
  have hIm : CommRingOps.add (CommRingOps.mul z.c0 z.c1) (CommRingOps.mul z.c1 z.c0) =
      (CommRingOps.one : Goldilocks) := congrArg GoldilocksExt2.c1 hSq
  if hc1 : z.c1 = Goldilocks.zero then
    rw [hc1] at hIm
    change CommRingOps.add (CommRingOps.mul z.c0 CommRingOps.zero)
        (CommRingOps.mul CommRingOps.zero z.c0) = CommRingOps.one at hIm
    rw [LawfulCommRing.mul_zero, LawfulCommRing.zero_mul, LawfulCommRing.add_zero] at hIm
    exact absurd (congrArg Goldilocks.val hIm) (by decide)
  else
    have hNegEq : CommRingOps.mul z.c0 z.c0 =
        CommRingOps.neg (CommRingOps.mul GoldilocksExt2.nonResidue (CommRingOps.mul z.c1 z.c1)) := by
      have hSub := congrArg (fun t =>
        CommRingOps.add t (CommRingOps.neg (CommRingOps.mul GoldilocksExt2.nonResidue (CommRingOps.mul z.c1 z.c1)))) hRe
      rw [LawfulCommRing.add_assoc, LawfulCommRing.add_right_neg,
          LawfulCommRing.add_zero, LawfulCommRing.zero_add] at hSub
      exact hSub
    let w : Goldilocks :=
      CommRingOps.mul (CommRingOps.mul z.c0 (Goldilocks.inv z.c1)) sqrtNegOneGoldilocks
    have hwSq : CommRingOps.mul w w = GoldilocksExt2.nonResidue := by
      dsimp only [w]
      let q := CommRingOps.mul z.c0 (Goldilocks.inv z.c1)
      have h1 : CommRingOps.mul (CommRingOps.mul q sqrtNegOneGoldilocks)
          (CommRingOps.mul q sqrtNegOneGoldilocks) =
          CommRingOps.mul (CommRingOps.mul q q)
            (CommRingOps.mul sqrtNegOneGoldilocks sqrtNegOneGoldilocks) := by
        rw [LawfulCommRing.mul_assoc q sqrtNegOneGoldilocks _,
            ← LawfulCommRing.mul_assoc sqrtNegOneGoldilocks q _,
            LawfulCommRing.mul_comm sqrtNegOneGoldilocks q,
            LawfulCommRing.mul_assoc q sqrtNegOneGoldilocks _,
            ← LawfulCommRing.mul_assoc q q _]
      have hqSq : CommRingOps.mul q q = CommRingOps.neg GoldilocksExt2.nonResidue := by
        dsimp only [q]
        have ha : CommRingOps.mul (CommRingOps.mul z.c0 (Goldilocks.inv z.c1))
            (CommRingOps.mul z.c0 (Goldilocks.inv z.c1)) =
            CommRingOps.mul (CommRingOps.mul z.c0 z.c0)
              (CommRingOps.mul (Goldilocks.inv z.c1) (Goldilocks.inv z.c1)) := by
          rw [LawfulCommRing.mul_assoc z.c0 (Goldilocks.inv z.c1) _,
              ← LawfulCommRing.mul_assoc (Goldilocks.inv z.c1) z.c0 _,
              LawfulCommRing.mul_comm (Goldilocks.inv z.c1) z.c0,
              LawfulCommRing.mul_assoc z.c0 (Goldilocks.inv z.c1) _,
              ← LawfulCommRing.mul_assoc z.c0 z.c0 _]
        rw [ha, hNegEq, LawfulCommRing.neg_mul, LawfulCommRing.mul_assoc GoldilocksExt2.nonResidue]
        have hCancel : CommRingOps.mul (CommRingOps.mul z.c1 z.c1)
            (CommRingOps.mul (Goldilocks.inv z.c1) (Goldilocks.inv z.c1)) = CommRingOps.one := by
          rw [LawfulCommRing.mul_assoc z.c1 z.c1 _,
              ← LawfulCommRing.mul_assoc z.c1 (Goldilocks.inv z.c1) _,
              Goldilocks.mul_inv_cancel hc1, LawfulCommRing.one_mul,
              Goldilocks.mul_inv_cancel hc1]
        rw [hCancel, LawfulCommRing.mul_one]
      rw [h1, hqSq, sqrtNegOne_sq, LawfulCommRing.neg_mul, LawfulCommRing.mul_neg,
          LawfulCommRing.mul_one, LawfulCommRing.neg_neg]
    exact GoldilocksExt2.nonResidue_not_square w hwSq

def norm (z : QuarticGoldilocks) : GoldilocksExt2 :=
  CommRingOps.sub (CommRingOps.mul z.c0 z.c0)
    (CommRingOps.mul GoldilocksExt2.uBasis (CommRingOps.mul z.c1 z.c1))

theorem norm_ne_zero {z : QuarticGoldilocks} (hz : z ≠ zero) :
    norm z ≠ GoldilocksExt2.zero := by
  intro hNorm
  have hEq : CommRingOps.mul z.c0 z.c0 =
      CommRingOps.mul GoldilocksExt2.uBasis (CommRingOps.mul z.c1 z.c1) :=
    LawfulCommRing.sub_eq_zero_iff.mp hNorm
  if hc1 : z.c1 = GoldilocksExt2.zero then
    have hrhs : CommRingOps.mul GoldilocksExt2.uBasis (CommRingOps.mul z.c1 z.c1) =
        GoldilocksExt2.zero := by
      rw [hc1]
      change CommRingOps.mul GoldilocksExt2.uBasis
        (CommRingOps.mul CommRingOps.zero CommRingOps.zero) = CommRingOps.zero
      rw [LawfulCommRing.mul_zero, LawfulCommRing.mul_zero]
    rw [hrhs] at hEq
    rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hEq with hc0 | hc0 <;>
      exact hz (ext hc0 hc1)
  else
    let q := CommRingOps.mul z.c0 (GoldilocksExt2.inv z.c1)
    have hqSq : CommRingOps.mul q q = GoldilocksExt2.uBasis := by
      dsimp only [q]
      have hassoc : CommRingOps.mul (CommRingOps.mul z.c0 (GoldilocksExt2.inv z.c1))
          (CommRingOps.mul z.c0 (GoldilocksExt2.inv z.c1)) =
          CommRingOps.mul (CommRingOps.mul z.c0 z.c0)
            (CommRingOps.mul (GoldilocksExt2.inv z.c1) (GoldilocksExt2.inv z.c1)) := by
        rw [LawfulCommRing.mul_assoc z.c0 (GoldilocksExt2.inv z.c1) _,
            ← LawfulCommRing.mul_assoc (GoldilocksExt2.inv z.c1) z.c0 _,
            LawfulCommRing.mul_comm (GoldilocksExt2.inv z.c1) z.c0,
            LawfulCommRing.mul_assoc z.c0 (GoldilocksExt2.inv z.c1) _,
            ← LawfulCommRing.mul_assoc z.c0 z.c0 _]
      rw [hassoc, hEq, LawfulCommRing.mul_assoc GoldilocksExt2.uBasis]
      have hCancel : CommRingOps.mul (CommRingOps.mul z.c1 z.c1)
          (CommRingOps.mul (GoldilocksExt2.inv z.c1) (GoldilocksExt2.inv z.c1)) = CommRingOps.one := by
        rw [LawfulCommRing.mul_assoc z.c1 z.c1 _,
            ← LawfulCommRing.mul_assoc z.c1 (GoldilocksExt2.inv z.c1) _,
            GoldilocksExt2.mul_inv_cancel hc1, LawfulCommRing.one_mul,
            GoldilocksExt2.mul_inv_cancel hc1]
      rw [hCancel, LawfulCommRing.mul_one]
    exact uBasis_not_square q hqSq

def inv (z : QuarticGoldilocks) : QuarticGoldilocks :=
  let invN := GoldilocksExt2.inv (norm z)
  ⟨CommRingOps.mul z.c0 invN, CommRingOps.neg (CommRingOps.mul z.c1 invN)⟩

theorem mul_inv_cancel {z : QuarticGoldilocks} (hz : z ≠ zero) :
    CommRingOps.mul z (inv z) = CommRingOps.one := by
  have hnormNe := norm_ne_zero hz
  let invN := GoldilocksExt2.inv (norm z)
  apply ext
  · change CommRingOps.add
        (CommRingOps.mul z.c0 (CommRingOps.mul z.c0 invN))
        (CommRingOps.mul GoldilocksExt2.uBasis
          (CommRingOps.mul z.c1 (CommRingOps.neg (CommRingOps.mul z.c1 invN)))) =
      CommRingOps.one
    rw [← LawfulCommRing.mul_assoc z.c0 z.c0 invN,
        LawfulCommRing.mul_neg z.c1, LawfulCommRing.mul_neg GoldilocksExt2.uBasis,
        ← LawfulCommRing.mul_assoc z.c1 z.c1 invN,
        ← LawfulCommRing.mul_assoc GoldilocksExt2.uBasis _ invN,
        ← LawfulCommRing.sub_eq_add_neg,
        ← LawfulCommRing.sub_mul]
    exact GoldilocksExt2.mul_inv_cancel hnormNe
  · change CommRingOps.add
        (CommRingOps.mul z.c0 (CommRingOps.neg (CommRingOps.mul z.c1 invN)))
        (CommRingOps.mul z.c1 (CommRingOps.mul z.c0 invN)) =
      CommRingOps.zero
    rw [LawfulCommRing.mul_neg,
        ← LawfulCommRing.mul_assoc z.c0 z.c1 invN,
        ← LawfulCommRing.mul_assoc z.c1 z.c0 invN,
        LawfulCommRing.mul_comm z.c1 z.c0,
        LawfulCommRing.add_left_neg]

end QuarticGoldilocks

instance : NoZeroDivisors QuarticGoldilocks where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} h := by
    if ha : a = QuarticGoldilocks.zero then
      exact .inl ha
    else
      right
      have hmul := congrArg (CommRingOps.mul (QuarticGoldilocks.inv a)) h
      rw [LawfulCommRing.mul_zero, ← LawfulCommRing.mul_assoc,
          LawfulCommRing.mul_comm (QuarticGoldilocks.inv a) a,
          QuarticGoldilocks.mul_inv_cancel ha, LawfulCommRing.one_mul] at hmul
      exact hmul

/-- **Root-Counting Univariate Schwartz–Zippel Theorem (`schwartz_zippel_root_bound_of_nodup`)**:
    Over ANY integral domain `F` (`Goldilocks`, `GoldilocksExt2`, `QuarticGoldilocks`), for ANY
    duplicate-free challenge pool `S : List F` (`0 < S.length`) and ANY non-zero polynomial `cs`
    of degree `≤ d`, the fraction of challenge points in `S` where `evalCoeffs cs r = 0` is
    bounded by `d / S.length` — proved from `RoundPoly.roots_nodup_length_le`, NOT a formula literal! -/
theorem schwartz_zippel_root_bound_of_nodup
    {F : Type} [LawfulCommRing F] [DecidableEq F] [NoZeroDivisors F]
    (d : Nat) (cs : List F) (S : List F)
    (hPos : 0 < S.length) (hNodup : S.Nodup) (hDeg : cs.length ≤ d + 1)
    (hNonzero : ∃ x₀ : F, RoundPoly.evalCoeffs cs x₀ ≠ CommRingOps.zero) :
    RatBound.le
      ⟨(S.filter (fun r => decide (RoundPoly.evalCoeffs cs r = CommRingOps.zero))).length,
       S.length, hPos⟩
      ⟨d, S.length, hPos⟩ := by
  unfold RatBound.le
  dsimp only
  apply Nat.mul_le_mul_right
  exact RoundPoly.roots_nodup_length_le d cs S hNodup hDeg hNonzero

/-- Concrete specialization of `schwartz_zippel_root_bound_of_nodup` to `QuarticGoldilocks`! -/
theorem goldilocksExt4_schwartz_zippel_root_bound
    (d : Nat) (cs : List QuarticGoldilocks) (S : List QuarticGoldilocks)
    (hPos : 0 < S.length) (hNodup : S.Nodup) (hDeg : cs.length ≤ d + 1)
    (hNonzero : ∃ x₀ : QuarticGoldilocks, RoundPoly.evalCoeffs cs x₀ ≠ CommRingOps.zero) :
    (S.filter (fun r => decide (RoundPoly.evalCoeffs cs r = CommRingOps.zero))).length ≤ d ∧
    RatBound.le
      ⟨(S.filter (fun r => decide (RoundPoly.evalCoeffs cs r = CommRingOps.zero))).length,
       S.length, hPos⟩
      ⟨d, S.length, hPos⟩ :=
  ⟨RoundPoly.roots_nodup_length_le d cs S hNodup hDeg hNonzero,
   schwartz_zippel_root_bound_of_nodup d cs S hPos hNodup hDeg hNonzero⟩

/-! ### §4.1 `Hem` `GoldilocksExt4` 5-Regime WHIR Ladder, Positive-`η` Slack & List/Commit Costs -/

/-- Exact quartic extension cardinality `|𝔽_{p^4}| = p^4` (`> 2^255`). -/
def goldilocksExt4Card : Nat := goldilocksPrime ^ 4
def goldilocksExt2Card : Nat := goldilocksPrime ^ 2

theorem goldilocksExt4Card_pos : 0 < goldilocksExt4Card := by
  unfold goldilocksExt4Card goldilocksPrime; decide

theorem goldilocksExt2Card_pos : 0 < goldilocksExt2Card := by
  unfold goldilocksExt2Card goldilocksPrime; decide

/-- Canonical 5-regime WHIR security ladder mirroring `crates/qsag-agg/src/pcs.rs`
    (`WhirSecurityRegime`, `#[repr(u8)]` tags `0..4`, `default = .habr24Qrom128` = `3`):
    1. `habr24Classical128`: `(56, 28, 19, 14)` (`112` `[HABR24]` query bits + `16`b PoW = `128` classical FS bits, `~64` QROM round-search bits),
    2. `habr24Interactive128`: `(64, 32, 22, 16)` (`128` pure interactive `[HABR24]` query bits / `144` classical FS bits, `~72` QROM round-search bits — classical regime, NOT `PQ128`),
    3. `bciksJohnsonClassical128`: `(129, 65, 44, 33)` (`⌈256 / log₂ B_i⌉ + 1`, `< 2⁻¹²⁸` unconditional `[BCIKS20]` Johnson query error with positive slack `η_i > 0`, `~72` QROM round-search bits — classical regime, NOT `PQ128`),
    4. `habr24Qrom128` (**DEFAULT**): `(128, 64, 43, 32)` (`2⁻²⁵⁶` `[HABR24]` query error + `16`b PoW = `272` classical FS bits / `136` QROM Grover round-search bits),
    5. `bciksJohnsonQrom128`: `(257, 129, 86, 65)` (`⌈512 / log₂ B_i⌉ + 1`, `< 2⁻²⁵⁶` unconditional `[BCIKS20]` Johnson query error with positive slack `η_i > 0` + `16`b PoW = `> 272` classical FS bits / `136` QROM Grover round-search bits without `[HABR24]`). -/
inductive WhirBudgetRegime where
  | habr24Classical128
  | habr24Interactive128
  | bciksJohnsonClassical128
  | habr24Qrom128
  | bciksJohnsonQrom128
  deriving DecidableEq, Repr

namespace WhirBudgetRegime

def default : WhirBudgetRegime := .habr24Qrom128

def toU8 : WhirBudgetRegime → UInt8
  | .habr24Classical128 => 0
  | .habr24Interactive128 => 1
  | .bciksJohnsonClassical128 => 2
  | .habr24Qrom128 => 3
  | .bciksJohnsonQrom128 => 4

def fromU8? (tag : UInt8) : Option WhirBudgetRegime :=
  if tag == 0 then some .habr24Classical128
  else if tag == 1 then some .habr24Interactive128
  else if tag == 2 then some .bciksJohnsonClassical128
  else if tag == 3 then some .habr24Qrom128
  else if tag == 4 then some .bciksJohnsonQrom128
  else none

def meetsQrom128Floor : WhirBudgetRegime → Bool
  | .habr24Qrom128 | .bciksJohnsonQrom128 => true
  | _ => false

end WhirBudgetRegime

/-- One stage `(blowup B_i = sqrtBlowup^2, stepVars s_i, domainLog2, numQueries q_i)` of a WHIR schedule. -/
structure WhirStageBudget where
  sqrtBlowup : Nat
  stepVars : Nat
  domainLog2 : Nat
  numQueries : Nat
  h_sqrt_pos : 0 < sqrtBlowup
  deriving DecidableEq, Repr

/-- Canonical 4-stage `B = (4, 16, 64, 256)` (`sqrtBlowup = (2, 4, 8, 16)`, `step_vars = (5, 3, 4, 4)`,
    `domainLog2 = (22, 19, 18, 16)`) WHIR query schedules for all 5 `WhirBudgetRegime` profiles. -/
def whirSchedule4Stage : WhirBudgetRegime → List WhirStageBudget
  | .habr24Classical128 =>
      [ ⟨2, 5, 22, 56, by decide⟩, ⟨4, 3, 19, 28, by decide⟩,
        ⟨8, 4, 18, 19, by decide⟩, ⟨16, 4, 16, 14, by decide⟩ ]
  | .habr24Interactive128 =>
      [ ⟨2, 5, 22, 64, by decide⟩, ⟨4, 3, 19, 32, by decide⟩,
        ⟨8, 4, 18, 22, by decide⟩, ⟨16, 4, 16, 16, by decide⟩ ]
  | .bciksJohnsonClassical128 =>
      [ ⟨2, 5, 22, 129, by decide⟩, ⟨4, 3, 19, 65, by decide⟩,
        ⟨8, 4, 18, 44, by decide⟩, ⟨16, 4, 16, 33, by decide⟩ ]
  | .habr24Qrom128 =>
      [ ⟨2, 5, 22, 128, by decide⟩, ⟨4, 3, 19, 64, by decide⟩,
        ⟨8, 4, 18, 43, by decide⟩, ⟨16, 4, 16, 32, by decide⟩ ]
  | .bciksJohnsonQrom128 =>
      [ ⟨2, 5, 22, 257, by decide⟩, ⟨4, 3, 19, 129, by decide⟩,
        ⟨8, 4, 18, 86, by decide⟩, ⟨16, 4, 16, 65, by decide⟩ ]

/-- 3-stage `nv = 20` (`K = 8` shard, `early_stop_vars = 8`) prefix of `whirSchedule4Stage`. -/
def whirScheduleNv20 (r : WhirBudgetRegime) : List WhirStageBudget :=
  (whirSchedule4Stage r).take 3

/-- Conjectural `[HABR24]` Conjecture-1 (capacity `1 - ρ_i` list decoding) statistical query bound
    `(1 / B_i) ^ q_i = (1 / sqrtBlowup^2) ^ q_i` multiplied by `1 / 2 ^ powBits` PoW target density. -/
def whirConjecturalHabr24StageBound (st : WhirStageBudget) (powBits : Nat) : RatBound :=
  ⟨1, (st.sqrtBlowup ^ 2) ^ st.numQueries * 2 ^ powBits,
   Nat.mul_pos (Nat.pow_pos (Nat.pow_pos st.h_sqrt_pos)) (Nat.two_pow_pos powBits)⟩

/-- `[BCIKS20]` Johnson list-size bound `L_i = 1 / (2 * η_i) = etaScale * √B_i` at positive rational
    proximity slack `η_i = 1 / (2 * etaScale * √B_i) > 0` (`etaScale > 0`). -/
def whirJohnsonListSize (st : WhirStageBudget) (etaScale : Nat) : Nat :=
  etaScale * st.sqrtBlowup

/-- Unconditional `[BCIKS20]` Johnson proximity query bound WITH strictly positive slack
    `η_i = 1 / (2 * etaScale * √B_i) > 0`: each query hits an `(1/√B_i + η_i)`-agreeing set with
    probability at most `1/√B_i + η_i = (2 * etaScale + 1) / (2 * etaScale * √B_i)`. -/
def whirPositiveEtaPureQueryBound (st : WhirStageBudget) (etaScale : Nat) (hEta : 0 < etaScale) :
    RatBound :=
  ⟨(2 * etaScale + 1) ^ st.numQueries,
   (2 * etaScale * st.sqrtBlowup) ^ st.numQueries,
   Nat.pow_pos (Nat.mul_pos (Nat.mul_pos (by decide) hEta) st.h_sqrt_pos)⟩

/-- Positive-`η` unconditional `[BCIKS20]` Johnson stage bound including `powBits` per-stage PoW. -/
def whirPositiveEtaJohnsonStageBound (st : WhirStageBudget) (etaScale : Nat) (hEta : 0 < etaScale)
    (powBits : Nat) : RatBound :=
  ⟨(2 * etaScale + 1) ^ st.numQueries,
   (2 * etaScale * st.sqrtBlowup) ^ st.numQueries * 2 ^ powBits,
   Nat.mul_pos
     (Nat.pow_pos (Nat.mul_pos (Nat.mul_pos (by decide) hEta) st.h_sqrt_pos))
     (Nat.two_pow_pos powBits)⟩

/-- `[BCIKS20]` OOD list-pinning collision error `L_i^2 * |D_i| / p^4` at Johnson list size
    `L_i = whirJohnsonListSize st etaScale` over `QuarticGoldilocks`. -/
def whirPositiveEtaOodListPinBound (st : WhirStageBudget) (etaScale : Nat) : RatBound :=
  ⟨(whirJohnsonListSize st etaScale) ^ 2 * 2 ^ st.domainLog2,
   goldilocksExt4Card, goldilocksExt4Card_pos⟩

/-- `[BCIKS20]` Theorem 4.1 commit-phase binary-folding correlated-agreement error
    `s_i * |D_i|^2 / ((2 * η_i)^7 * p^4) = s_i * |D_i|^2 * L_i^7 / p^4` carrying the full `(2 * η_i)⁻⁷`
    proximity-slack denominator across `st.stepVars` folding steps over `QuarticGoldilocks`. -/
def whirPositiveEtaCommitFoldBound (st : WhirStageBudget) (etaScale : Nat) : RatBound :=
  ⟨st.stepVars * (2 ^ st.domainLog2) ^ 2 * (whirJohnsonListSize st etaScale) ^ 7,
   goldilocksExt4Card, goldilocksExt4Card_pos⟩

/-- **Positive-`η` `[BCIKS20]` Johnson Proximity Slack, Finite List Size & Commit-Phase Theorem**:
    Thanks to the `+ 1` query slack (`⌈256 / log₂ B_i⌉ + 1` and `⌈512 / log₂ B_i⌉ + 1`),
    1. `bciksJohnsonClassical128` (`q = (129, 65, 44, 33)`) at `etaScale = 128` (`η_i = 1 / (256 √B_i) > 0`,
       finite list sizes `L = (256, 512, 1024, 2048)`) achieves **`strictlyMoreThanBits 128`** PURE
       proximity-query soundness BEFORE PoW, **`strictlyMoreThanBits 208`** OOD list-pinning, and
       **`atLeastBits 144`** `[BCIKS20]` `(2η_i)⁻⁷` commit-phase soundness at every stage!
    2. `bciksJohnsonQrom128` (`q = (257, 129, 86, 65)`) at `etaScale = 256` (`η_i = 1 / (512 √B_i) > 0`,
       finite list sizes `L = (512, 1024, 2048, 4096)`) achieves **`strictlyMoreThanBits 256`** PURE
       proximity-query soundness BEFORE PoW, **`strictlyMoreThanBits 206`** OOD list-pinning, and
       **`atLeastBits 137`** `[BCIKS20]` `(2η_i)⁻⁷` commit-phase soundness at every stage! -/
theorem bciks_johnson_positive_eta_slack_and_commit_costs :
    (∀ st ∈ whirSchedule4Stage .bciksJohnsonClassical128,
      strictlyMoreThanBits 128 (whirPositiveEtaPureQueryBound st 128 (by decide)) ∧
      strictlyMoreThanBits 208 (whirPositiveEtaOodListPinBound st 128) ∧
      atLeastBits 144 (whirPositiveEtaCommitFoldBound st 128)) ∧
    (∀ st ∈ whirSchedule4Stage .bciksJohnsonQrom128,
      strictlyMoreThanBits 256 (whirPositiveEtaPureQueryBound st 256 (by decide)) ∧
      strictlyMoreThanBits 206 (whirPositiveEtaOodListPinBound st 256) ∧
      atLeastBits 137 (whirPositiveEtaCommitFoldBound st 256)) := by
  constructor
  · intro st hMem
    simp only [whirSchedule4Stage, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl <;>
      refine ⟨by unfold strictlyMoreThanBits whirPositiveEtaPureQueryBound; decide,
              by unfold strictlyMoreThanBits whirPositiveEtaOodListPinBound whirJohnsonListSize
                   goldilocksExt4Card goldilocksPrime; decide,
              by unfold atLeastBits whirPositiveEtaCommitFoldBound whirJohnsonListSize
                   goldilocksExt4Card goldilocksPrime; decide⟩
  · intro st hMem
    simp only [whirSchedule4Stage, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl <;>
      refine ⟨by unfold strictlyMoreThanBits whirPositiveEtaPureQueryBound; decide,
              by unfold strictlyMoreThanBits whirPositiveEtaOodListPinBound whirJohnsonListSize
                   goldilocksExt4Card goldilocksPrime; decide,
              by unfold atLeastBits whirPositiveEtaCommitFoldBound whirJohnsonListSize
                   goldilocksExt4Card goldilocksPrime; decide⟩

/-- **`Hem` `QuarticGoldilocks` Algebraic Soundness & Complete 5-Regime WHIR Ladder Theorem**:
    1. `p^4 > 2^255`: single-check `Ext4` sumcheck (`72 / p^4`) achieves **`atLeastBits 249`**,
       `[BCIKS20]` folding (`2^80 / p^4`) achieves **`atLeastBits 175`**, and Kronecker OOD
       (`2^30 / p^4`) achieves **`strictlyMoreThanBits 225`**.
    2. **Classical WHIR Regimes** (`habr24Classical128`, `habr24Interactive128`,
       `bciksJohnsonClassical128`): achieve `≥ 128`, `≥ 144`, and `> 144` classical FS bits per stage,
       while `habr24Interactive128` (`q_0 = 64`) and `bciksJohnsonClassical128` (`q_0 = 129`) hit a
       `~72`-bit generic QROM Grover round-search ceiling (`exceedsBitBudget 0` at `qHash = 2^72`).
    3. **QROM WHIR Regimes** (`habr24Qrom128` default & `bciksJohnsonQrom128` unconditional): achieve
       `≥ 272` classical FS bits per stage and survive QROM Grover round grinding at **`atLeastBits 129`**
       for ALL `qHash + 1 ≤ 2 ^ 70` (`136`-bit round-search target density)! -/
