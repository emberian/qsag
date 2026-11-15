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
     `tooth_hem_ext2_folding_under_100bits`), OOD list-pinning (`> 225` bits), unconditional
     `[BCIKS20]` Johnson `WhirBudgetRegime` profiles (`bciksJohnsonClassical128` wire tag `2` and
     default `bciksJohnsonQrom128` wire tag `4`, with retired capacity wire tags `0, 1, 3` rejected
     by `tooth_whirBudgetRegime_fromU8_rejects_retired_tags` and capacity query deficits certified
     by `tooth_retired_capacity_queries_fail_johnson_bounds`), and upgraded unconditional
     `hemWhirPq128Stages` (`≥ 128` quantum bits).

5. **§5–§6. Fast-Factored ZKBoo (`BlindVc` `219` vs `438`), `ThresholdMlDsa`, `Poseidon2Toprf`,
   `DensePcg`, `HdRekey` (Exact 96-Bit Modular Bias), `ActiveMigration` & Master `PQ128` Portfolio**:
   - Cube/6th-power `3^73` bounds proving `(2/3)^219 < 2^-128`, `#tooth`
     `tooth_zkboo_219_quantum_grind_64bit` (`(2/3)^219 > 2^-129`), and `(2/3)^438 < 2^-256` (`≥ 128`
     quantum FS bits), composed into `qsag_pq128_portfolio_soundness_budget` and
     `inhabited_concrete_security_budget_roster`.
   - `DensePcg` V3 seed search over the complete 64-tree depth-15 forest: the per-node-tweak
     query-partition bound `tweaked_multi_target_query_partition_union_bound` (140 bits at
     `2^56` queries) beside the one-function bound (120 bits), with their exact crossover.
   - FIPS 204 challenge spaces for ML-DSA-44 / 65 / 87 and their offline grinding ceilings
     (`2^30 / 2^47 / 2^63`); the roster's threshold entry is the deployed Category-2 ML-DSA-44
     and carries a `2^30` hash-query ceiling.
-/

public import Qsag.Constructive
public import Qsag.Tactic.AssuranceKit
public import Qsag.Goldilocks
import all Qsag.Goldilocks
public import Qsag.UcGames
import all Qsag.UcGames
public import Qsag.AffineProximityGaps
import all Qsag.AffineProximityGaps

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
  | 0, _, _ => by unfold finIntSum; decide
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

private theorem int_mul_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n => exact Int.ofNat_le.mpr (Nat.zero_le (m * n))
    | negSucc n => cases hb
  | negSucc m => cases ha

private theorem int_mul_pos {a b : Int} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      exact Int.ofNat_lt.mpr (Nat.mul_pos (Int.ofNat_lt.mp ha) (Int.ofNat_lt.mp hb))
    | negSucc n => cases hb
  | negSucc m => cases ha

private theorem cs_combine_two {a1 b1 c1 a2 b2 c2 : Int}
    (ha1 : 0 ≤ a1) (hb1 : 0 ≤ b1) (ha2 : 0 ≤ a2) (hb2 : 0 ≤ b2)
    (h1 : c1 ^ 2 ≤ a1 * b1) (h2 : c2 ^ 2 ≤ a2 * b2) :
    (c1 + c2) ^ 2 ≤ (a1 + a2) * (b1 + b2) := by
  have p2 : ∀ x : Int, x ^ 2 = x * x := fun x => by
    change x ^ (1 + 1) = x * x
    rw [Int.pow_succ, Int.pow_succ, Int.pow_zero, Int.one_mul]
  have hProd : c1 ^ 2 * c2 ^ 2 ≤ (a1 * b1) * (a2 * b2) := by
    have hs1 : 0 ≤ (a1 * b1 - c1 ^ 2) * c2 ^ 2 :=
      int_mul_nonneg (by omega) (by rw [p2]; exact int_sq_nonneg c2)
    rw [Int.sub_eq_add_neg, Int.add_mul, Int.neg_mul] at hs1
    have hs2 : 0 ≤ (a1 * b1) * (a2 * b2 - c2 ^ 2) :=
      int_mul_nonneg (int_mul_nonneg ha1 hb1) (by omega)
    rw [Int.sub_eq_add_neg, Int.mul_add, Int.mul_neg] at hs2
    omega
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
    omega
  have hCross : 2 * c1 * c2 ≤ a1 * b2 + a2 * b1 := by
    let u := 2 * c1 * c2
    let v := a1 * b2 + a2 * b1
    have hSN : 0 ≤ v := by
      have pA := int_mul_nonneg ha1 hb2
      have pB := int_mul_nonneg ha2 hb1
      dsimp only [v]; omega
    if hc : u ≤ v then
      exact hc
    else
      exfalso
      have hSqUV : u * u ≤ v * v := by
        change (2 * c1 * c2) * (2 * c1 * c2) ≤ (a1 * b2 + a2 * b1) * (a1 * b2 + a2 * b1)
        rwa [p2, p2] at hCrossSq
      have hPosDiff : 0 < u - v := by omega
      have hPosSum : 0 < u + v := by omega
      have hPosProd : 0 < (u - v) * (u + v) := int_mul_pos hPosDiff hPosSum
      have hDiffSq : (u - v) * (u + v) = u * u - v * v := by
        calc (u - v) * (u + v)
          _ = u * (u + v) - v * (u + v) := Int.sub_mul u v (u + v)
          _ = (u * u + u * v) - (v * u + v * v) := by rw [Int.mul_add u u v, Int.mul_add v u v]
          _ = (u * u + u * v) - (u * v + v * v) := by rw [Int.mul_comm v u]
          _ = u * u - v * v := by omega
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
    | zero => unfold finIntSum qsum; decide
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
    | zero => unfold qsum; decide
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
    · simp only [Bool.false_eq_true, ↓reduceIte]; decide
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
      rw [Nat.pow_two, Nat.add_mul, Nat.add_mul, Nat.add_comm]
      simp only [Nat.mul_assoc]
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

/-- Canonical 2-regime unconditional WHIR Johnson security ladder mirroring
    `crates/qsag-agg/src/pcs.rs` (`WhirSecurityRegime`, `#[repr(u8)]` tags `{2, 4}`,
    `default = .bciksJohnsonQrom128` = `4`; retired capacity wire tags `0, 1, 3` are rejected per
    `Crites & Stewart 2025/2046` and `Krachun-Kazanin-Habock 2026/782`):
    1. `bciksJohnsonClassical128` (wire tag `2`): `(129, 65, 44, 33)` (`⌈256 / log₂ B_i⌉ + 1`,
       `< 2⁻¹²⁸` unconditional `[BCIKS20]` Johnson query error with positive slack `η_i > 0`,
       `~72` QROM round-search bits — classical regime, NOT `PQ128`),
    2. `bciksJohnsonQrom128` (**DEFAULT**, wire tag `4`): `(258, 130, 88, 66)`
       (`⌈512 / log₂ B_i⌉ + 2`, `pcs.rs::minimum_queries`, `< 2⁻²⁵⁶` unconditional `[BCIKS20]`
       Johnson query error with positive slack `η_i > 0` + `16`b PoW = `> 272` classical FS bits /
       `136` QROM Grover round-search bits). -/
inductive WhirBudgetRegime where
  | bciksJohnsonClassical128
  | bciksJohnsonQrom128
  deriving DecidableEq, Repr

namespace WhirBudgetRegime

def default : WhirBudgetRegime := .bciksJohnsonQrom128

def toU8 : WhirBudgetRegime → UInt8
  | .bciksJohnsonClassical128 => 2
  | .bciksJohnsonQrom128 => 4

def fromU8? (tag : UInt8) : Option WhirBudgetRegime :=
  if tag == 2 then some .bciksJohnsonClassical128
  else if tag == 4 then some .bciksJohnsonQrom128
  else none

def meetsQrom128Floor : WhirBudgetRegime → Bool
  | .bciksJohnsonQrom128 => true
  | .bciksJohnsonClassical128 => false

end WhirBudgetRegime

/-- `#tooth`: retired capacity-proximity wire tags `0`, `1`, and `3` are rejected (`none`) by
    `WhirBudgetRegime.fromU8?`, matching `WhirSecurityRegime::from_u8` in `pcs.rs`. -/
theorem tooth_whirBudgetRegime_fromU8_rejects_retired_tags :
    WhirBudgetRegime.fromU8? 0 = none ∧
    WhirBudgetRegime.fromU8? 1 = none ∧
    WhirBudgetRegime.fromU8? 3 = none ∧
    WhirBudgetRegime.default = .bciksJohnsonQrom128 := by
  decide

/-- One stage `(blowup B_i = sqrtBlowup^2, stepVars s_i, domainLog2, numQueries q_i)` of a WHIR schedule. -/
structure WhirStageBudget where
  sqrtBlowup : Nat
  stepVars : Nat
  domainLog2 : Nat
  numQueries : Nat
  h_sqrt_pos : 0 < sqrtBlowup
  deriving DecidableEq, Repr

/-- Canonical 4-stage `B = (4, 16, 64, 256)` (`sqrtBlowup = (2, 4, 8, 16)`) WHIR query schedules
    for both unconditional `WhirBudgetRegime` profiles on the DEPLOYED `num_vars = 24` geometry of
    `pcs.rs::stage_geometry`: `step_vars = (6, 4, 3, 3)` and committed-domain sizes
    `|D_i| = 2^(26, 22, 20, 19)` (`= B_i * 2^(24, 18, 14, 11)`); see
    `whirSchedule4Stage_matches_deployed_geometry`. -/
def whirSchedule4Stage : WhirBudgetRegime → List WhirStageBudget
  | .bciksJohnsonClassical128 =>
      [ ⟨2, 6, 26, 129, by decide⟩, ⟨4, 4, 22, 65, by decide⟩,
        ⟨8, 3, 20, 44, by decide⟩, ⟨16, 3, 19, 33, by decide⟩ ]
  | .bciksJohnsonQrom128 =>
      [ ⟨2, 6, 26, 258, by decide⟩, ⟨4, 4, 22, 130, by decide⟩,
        ⟨8, 3, 20, 88, by decide⟩, ⟨16, 3, 19, 66, by decide⟩ ]

/-- 3-stage `nv = 20` (`K = 8` shard, `early_stop_vars = 8`) schedule on its own deployed geometry
    `step_vars = (5, 3, 4)`, `|D_i| = 2^(22, 19, 18)` (query counts depend only on the blowup). -/
def whirScheduleNv20 (r : WhirBudgetRegime) : List WhirStageBudget :=
  ((whirSchedule4Stage r).take 3).zipWith
    (fun st g => ⟨st.sqrtBlowup, g.1, g.2, st.numQueries, st.h_sqrt_pos⟩)
    [(5, 22), (3, 19), (4, 18)]

/-- **Schedule ↔ Deployed-Geometry Weld**: the `(√B_i, step_vars, log₂|D_i|)` columns of
    `whirSchedule4Stage` / `whirScheduleNv20` are exactly the `pcs.rs::stage_geometry` mirror
    `hemStageGeoms 24` / `hemStageGeoms 20` (`|D_i| = n_i * 2^step_vars`), the two Johnson regimes
    carry exactly `hemJohnsonMinQueries` (`pcs.rs::minimum_queries`), and every query count of
    every regime fits the wire cap `NUM_PCS_QUERIES = 512`. -/
theorem whirSchedule4Stage_matches_deployed_geometry :
    (∀ r : WhirBudgetRegime,
      (whirSchedule4Stage r).map (fun st => (st.sqrtBlowup ^ 2, st.stepVars, 2 ^ st.domainLog2)) =
        (hemStageGeoms 24).map (fun g => (2 ^ g.logBlowup, g.stepVars, g.n * 2 ^ g.stepVars))) ∧
    (∀ r : WhirBudgetRegime,
      (whirScheduleNv20 r).map (fun st => (st.sqrtBlowup ^ 2, st.stepVars, 2 ^ st.domainLog2)) =
        (hemStageGeoms 20).map (fun g => (2 ^ g.logBlowup, g.stepVars, g.n * 2 ^ g.stepVars))) ∧
    (whirSchedule4Stage .bciksJohnsonQrom128).map (·.numQueries) =
      (hemStageGeoms 24).map (fun g => hemJohnsonMinQueries true g.logBlowup) ∧
    (whirSchedule4Stage .bciksJohnsonClassical128).map (·.numQueries) =
      (hemStageGeoms 24).map (fun g => hemJohnsonMinQueries false g.logBlowup) ∧
    (whirSchedule4Stage .bciksJohnsonQrom128).map (·.numQueries) = [258, 130, 88, 66] ∧
    (∀ r : WhirBudgetRegime, ∀ st ∈ whirSchedule4Stage r, st.numQueries ≤ 512) := by
  refine ⟨?_, ?_, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  · intro r; cases r <;> decide +kernel
  · intro r; cases r <;> decide +kernel
  · intro r; cases r <;> decide +kernel

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

/-- `#tooth`: historical capacity-proximity query counts `[128, 64, 43, 32]` (and classical
    `[56, 28, 19, 14]`) across blowups `B = (4, 16, 64, 256)` (`√B = (2, 4, 8, 16)`) fail the
    unconditional `[BCIKS20]` Johnson 256-bit and 128-bit pure query bounds at EVERY stage
    (`exceedsBitBudget 256` and `exceedsBitBudget 128` respectively). -/
theorem tooth_retired_capacity_queries_fail_johnson_bounds :
    (∀ st ∈ ([ ⟨2, 6, 26, 128, by decide⟩, ⟨4, 4, 22, 64, by decide⟩,
               ⟨8, 3, 20, 43, by decide⟩, ⟨16, 3, 19, 32, by decide⟩ ] : List WhirStageBudget),
      exceedsBitBudget 256 (whirPositiveEtaPureQueryBound st 256 (by decide))) ∧
    (∀ st ∈ ([ ⟨2, 6, 26, 56, by decide⟩, ⟨4, 4, 22, 28, by decide⟩,
               ⟨8, 3, 20, 19, by decide⟩, ⟨16, 3, 19, 14, by decide⟩ ] : List WhirStageBudget),
      exceedsBitBudget 128 (whirPositiveEtaPureQueryBound st 128 (by decide))) := by
  constructor
  · intro st hMem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl <;>
      (unfold exceedsBitBudget whirPositiveEtaPureQueryBound; decide)
  · intro st hMem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl <;>
      (unfold exceedsBitBudget whirPositiveEtaPureQueryBound; decide)

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

/-- **Positive-`η` `[BCIKS20]` Johnson Proximity Slack, Finite List Size & Commit-Phase Theorem**
    (on the deployed `num_vars = 24` geometry `|D_i| = 2^(26, 22, 20, 19)`, `s_i = (6, 4, 3, 3)`):
    Thanks to the query slack (`⌈256 / log₂ B_i⌉ + 1` and `⌈512 / log₂ B_i⌉ + 2`),
    1. `bciksJohnsonClassical128` (`q = (129, 65, 44, 33)`) at `etaScale = 128` (`η_i = 1 / (256 √B_i) > 0`,
       finite list sizes `L = (256, 512, 1024, 2048)`) achieves **`strictlyMoreThanBits 128`** PURE
       proximity-query soundness BEFORE PoW, **`strictlyMoreThanBits 213`** OOD list-pinning, and
       **`atLeastBits 139`** `[BCIKS20]` `(2η_i)⁻⁷` commit-phase soundness at every stage
       (stage 3, `|D_3| = 2^19`, `L_3 = 2048`, is the bottleneck);
    2. `bciksJohnsonQrom128` (`q = (258, 130, 88, 66)`) at `etaScale = 256` (`η_i = 1 / (512 √B_i) > 0`,
       finite list sizes `L = (512, 1024, 2048, 4096)`) achieves **`strictlyMoreThanBits 256`** PURE
       proximity-query soundness BEFORE PoW, **`strictlyMoreThanBits 211`** OOD list-pinning, and
       **`atLeastBits 132`** `[BCIKS20]` `(2η_i)⁻⁷` commit-phase soundness at every stage! -/
theorem bciks_johnson_positive_eta_slack_and_commit_costs :
    (∀ st ∈ whirSchedule4Stage .bciksJohnsonClassical128,
      strictlyMoreThanBits 128 (whirPositiveEtaPureQueryBound st 128 (by decide)) ∧
      strictlyMoreThanBits 213 (whirPositiveEtaOodListPinBound st 128) ∧
      atLeastBits 139 (whirPositiveEtaCommitFoldBound st 128)) ∧
    (∀ st ∈ whirSchedule4Stage .bciksJohnsonQrom128,
      strictlyMoreThanBits 256 (whirPositiveEtaPureQueryBound st 256 (by decide)) ∧
      strictlyMoreThanBits 211 (whirPositiveEtaOodListPinBound st 256) ∧
      atLeastBits 132 (whirPositiveEtaCommitFoldBound st 256)) := by
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

/-- **`Hem` `QuarticGoldilocks` Algebraic Soundness & Unconditional 2-Regime WHIR Ladder Theorem**:
    1. `p^4 > 2^255`: single-check `Ext4` sumcheck (`72 / p^4`) achieves **`atLeastBits 249`**,
       `[BCIKS20]` folding (`2^80 / p^4`) achieves **`atLeastBits 175`**, and Kronecker OOD
       (`2^30 / p^4`) achieves **`strictlyMoreThanBits 225`**.
    2. **Classical Johnson WHIR Regime** (`bciksJohnsonClassical128`): achieves `> 144` classical FS
       bits per stage (`q = (129, 65, 44, 33)` + `16`b PoW), while Stage 0 (`q_0 = 129`) hits a
       `~72`-bit generic QROM Grover round-search ceiling (`exceedsBitBudget 0` at `qHash = 2^72`).
    3. **Default QROM Johnson WHIR Regime** (`bciksJohnsonQrom128`): achieves `> 272` classical FS
       bits per stage and survives QROM Grover round grinding at **`atLeastBits 129`** for ALL
       `qHash + 1 ≤ 2 ^ 70` (`136`-bit round-search target density)! -/
theorem hem_ext4_algebraic_and_whir_regime_soundness :
    2 ^ 255 < goldilocksExt4Card ∧
    atLeastBits 249 ⟨72, goldilocksExt4Card, goldilocksExt4Card_pos⟩ ∧
    atLeastBits 175 ⟨2 ^ 80, goldilocksExt4Card, goldilocksExt4Card_pos⟩ ∧
    strictlyMoreThanBits 225 ⟨2 ^ 30, goldilocksExt4Card, goldilocksExt4Card_pos⟩ ∧
    (∀ st ∈ whirSchedule4Stage .bciksJohnsonClassical128,
      strictlyMoreThanBits 144 (whirPositiveEtaJohnsonStageBound st 128 (by decide) 16)) ∧
    exceedsBitBudget 0
      (quantumGroverGrindingBound (2 ^ 72)
        (whirPositiveEtaJohnsonStageBound ⟨2, 6, 26, 129, by decide⟩ 128 (by decide) 16)) ∧
    (∀ st ∈ whirSchedule4Stage .bciksJohnsonQrom128, ∀ qHash : Nat, qHash + 1 ≤ 2 ^ 70 →
      atLeastBits 129
        (quantumGroverGrindingBound qHash (whirPositiveEtaJohnsonStageBound st 256 (by decide) 16))) := by
  have hSq70 : ∀ {qHash : Nat}, qHash + 1 ≤ 2 ^ 70 → 8 * (qHash + 1) ^ 2 ≤ 2 ^ 143 := by
    intro qHash hq
    have p1 : (qHash + 1) ^ 2 ≤ (2 ^ 70) ^ 2 := Nat.pow_le_pow_left hq 2
    have p2 : 8 * (2 ^ 70) ^ 2 = 2 ^ 143 := by decide
    rw [← p2]; exact Nat.mul_le_mul_left 8 p1
  refine ⟨by unfold goldilocksExt4Card goldilocksPrime; decide,
          by unfold atLeastBits goldilocksExt4Card goldilocksPrime; decide,
          by unfold atLeastBits goldilocksExt4Card goldilocksPrime; decide,
          by unfold strictlyMoreThanBits goldilocksExt4Card goldilocksPrime; decide,
          ?_,
          by unfold exceedsBitBudget quantumGroverGrindingBound whirPositiveEtaJohnsonStageBound
               RatBound.scale; decide,
          ?_⟩
  · intro st hMem
    have hPure := (bciks_johnson_positive_eta_slack_and_commit_costs.1 st hMem).1
    unfold strictlyMoreThanBits whirPositiveEtaPureQueryBound at hPure
    unfold strictlyMoreThanBits whirPositiveEtaJohnsonStageBound
    dsimp only at hPure ⊢
    have hMul := Nat.mul_lt_mul_of_pos_right hPure (Nat.two_pow_pos 16)
    have hPow : (2 * 128 + 1) ^ st.numQueries * 2 ^ 128 * 2 ^ 16 =
        (2 * 128 + 1) ^ st.numQueries * 2 ^ 144 := by
      simp only [Nat.mul_assoc, ← Nat.pow_add]
    rwa [hPow] at hMul
  · intro st hMem qHash hq
    have h8 := hSq70 hq
    have hPure := Nat.le_of_lt (bciks_johnson_positive_eta_slack_and_commit_costs.2 st hMem).1
    unfold strictlyMoreThanBits whirPositiveEtaPureQueryBound at hPure
    unfold atLeastBits quantumGroverGrindingBound whirPositiveEtaJohnsonStageBound RatBound.scale
    dsimp only at hPure ⊢
    have hMul8 := Nat.mul_le_mul_right ((2 * 256 + 1) ^ st.numQueries * 2 ^ 129) h8
    have hAssocL : 8 * (qHash + 1) ^ 2 * (2 * 256 + 1) ^ st.numQueries * 2 ^ 129 =
        8 * (qHash + 1) ^ 2 * ((2 * 256 + 1) ^ st.numQueries * 2 ^ 129) := by
      simp only [Nat.mul_assoc]
    have hMid : 2 ^ 143 * ((2 * 256 + 1) ^ st.numQueries * 2 ^ 129) =
        (2 * 256 + 1) ^ st.numQueries * 2 ^ 256 * 2 ^ 16 := by
      have h1 : 2 ^ 143 * ((2 * 256 + 1) ^ st.numQueries * 2 ^ 129) =
          (2 * 256 + 1) ^ st.numQueries * (2 ^ 143 * 2 ^ 129) := by
        rw [Nat.mul_left_comm (2 ^ 143)]
      have h2 : (2 : Nat) ^ 143 * 2 ^ 129 = 2 ^ 256 * 2 ^ 16 := by decide
      rw [h1, h2, Nat.mul_assoc]
    have hP2 := Nat.mul_le_mul_right (2 ^ 16) hPure
    rw [← hMid] at hP2
    rw [hAssocL]
    exact Nat.le_trans hMul8 hP2

/-- Complete 13-term unconditional `[BCIKS20]` multi-stage rational union list for a positive-`η`
    `WhirBudgetRegime` (`4` positive-`η` query-plus-PoW stages + `4` OOD list-pinning bounds +
    `4` `(2η_i)⁻⁷` commit-folding bounds + `Ext4` algebraic sumcheck). -/
def whirUnconditionalMultiStageTerms
    (r : WhirBudgetRegime) (etaScale : Nat) (hEta : 0 < etaScale) (powBits : Nat) :
    List RatBound :=
  ⟨72, goldilocksExt4Card, goldilocksExt4Card_pos⟩ ::
  ((whirSchedule4Stage r).map (fun st => whirPositiveEtaJohnsonStageBound st etaScale hEta powBits) ++
   (whirSchedule4Stage r).map (fun st => whirPositiveEtaOodListPinBound st etaScale) ++
   (whirSchedule4Stage r).map (fun st => whirPositiveEtaCommitFoldBound st etaScale))

/-- **`WhirBudgetRegime` (`pcs.rs` `WhirSecurityRegime`) Wire Bijection, Multi-Stage Union &
    Multi-Session Scaling Theorem**:
    1. **Wire-Tag Bijection (`pcs.rs:121-141`)**: `fromU8? (r.toU8) = some r`,
       `WhirBudgetRegime.default = .bciksJohnsonQrom128`, and `meetsQrom128Floor = true` iff
       `r = .bciksJohnsonQrom128` (with wire tags `0, 1, 3` rejected).
    2. **4-Stage + Multi-Session QROM Union Slack (`pcs.rs:174`)**: summing ALL 4 QROM Grover
       round-search bounds (`RatBound.sumList`) and scaling across up to `S ≤ 2 ^ 7 = 128`
       online sessions preserves **`atLeastBits 128`** for unconditional positive-`η`
       `bciksJohnsonQrom128` for ALL `qHash + 1 ≤ 2 ^ 66` (`137` per-stage bits
       minus `2` stage-union bits minus `7` session-union bits = `128` quantum bits!).
    3. **Full 13-Event Multi-Stage + Multi-Session Unconditional `[BCIKS20]` Union Bounds**:
       (exact 13-term rational sums on the deployed `num_vars = 24` geometry, kernel-decided)
       - `bciksJohnsonClassical128` (`etaScale = 128`): the sum of ALL 13 multi-stage proximity +
         OOD list-pinning + `(2η_i)⁻⁷` commit-folding + `Ext4` sumcheck bounds is
         **`atLeastBits 139`** per session, hence **`atLeastBits 128`** across `S ≤ 2 ^ 11` sessions,
       - `bciksJohnsonQrom128` (`etaScale = 256`): the sum of ALL 13 unconditional multi-stage bounds
         is **`atLeastBits 132`** per session, hence **`atLeastBits 128`** across `S ≤ 2 ^ 4` sessions.
       The `(2η_i)⁻⁷` commit-folding term of the last stage (`|D_3| = 2^19`, `L_3 = 4096`) is the
       bottleneck; `[CWYZ26]` affine folding (§4.2) removes it. -/
theorem whirBudgetRegime_multistage_union_and_session_bounds :
    (∀ r : WhirBudgetRegime, WhirBudgetRegime.fromU8? r.toU8 = some r) ∧
    (∀ r : WhirBudgetRegime,
      r.meetsQrom128Floor = true ↔ r = .bciksJohnsonQrom128) ∧
    (∀ qHash S : Nat, qHash + 1 ≤ 2 ^ 66 → S ≤ 2 ^ 7 →
      atLeastBits 128
        (RatBound.scale S
          (RatBound.sumList
            ((whirSchedule4Stage .bciksJohnsonQrom128).map
              (fun st => quantumGroverGrindingBound qHash
                (whirPositiveEtaJohnsonStageBound st 256 (by decide) 16)))))) ∧
    (∀ S : Nat, S ≤ 2 ^ 11 →
      atLeastBits 128
        (RatBound.scale S
          (RatBound.sumList (whirUnconditionalMultiStageTerms .bciksJohnsonClassical128 128 (by decide) 16)))) ∧
    (∀ S : Nat, S ≤ 2 ^ 4 →
      atLeastBits 128
        (RatBound.scale S
          (RatBound.sumList (whirUnconditionalMultiStageTerms .bciksJohnsonQrom128 256 (by decide) 16)))) := by
  have hSq66 : ∀ {qHash : Nat}, qHash + 1 ≤ 2 ^ 66 → 8 * (qHash + 1) ^ 2 ≤ 2 ^ 135 := by
    intro qHash hq
    have p1 : (qHash + 1) ^ 2 ≤ (2 ^ 66) ^ 2 := Nat.pow_le_pow_left hq 2
    have p2 : 8 * (2 ^ 66) ^ 2 = 2 ^ 135 := by decide
    rw [← p2]; exact Nat.mul_le_mul_left 8 p1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r; cases r <;> decide
  · intro r; cases r <;> decide
  · intro qHash S hq hS
    apply atLeastBits_scale_session_loss hS
    apply atLeastBits_sumList_union_loss (loss := 2) (by simp [whirSchedule4Stage])
    intro b hb
    rw [List.mem_map] at hb
    rcases hb with ⟨st, hMem, rfl⟩
    have h8 := hSq66 hq
    have hPure := Nat.le_of_lt (bciks_johnson_positive_eta_slack_and_commit_costs.2 st hMem).1
    unfold strictlyMoreThanBits whirPositiveEtaPureQueryBound at hPure
    unfold atLeastBits quantumGroverGrindingBound whirPositiveEtaJohnsonStageBound RatBound.scale
    dsimp only at hPure ⊢
    have hMul8 := Nat.mul_le_mul_right ((2 * 256 + 1) ^ st.numQueries * 2 ^ 137) h8
    have hAssocL : 8 * (qHash + 1) ^ 2 * (2 * 256 + 1) ^ st.numQueries * 2 ^ 137 =
        8 * (qHash + 1) ^ 2 * ((2 * 256 + 1) ^ st.numQueries * 2 ^ 137) := by
      simp only [Nat.mul_assoc]
    have hMid : 2 ^ 135 * ((2 * 256 + 1) ^ st.numQueries * 2 ^ 137) =
        (2 * 256 + 1) ^ st.numQueries * 2 ^ 256 * 2 ^ 16 := by
      have h1 : 2 ^ 135 * ((2 * 256 + 1) ^ st.numQueries * 2 ^ 137) =
          (2 * 256 + 1) ^ st.numQueries * (2 ^ 135 * 2 ^ 137) := by
        rw [Nat.mul_left_comm (2 ^ 135)]
      have h2 : (2 : Nat) ^ 135 * 2 ^ 137 = 2 ^ 256 * 2 ^ 16 := by decide
      rw [h1, h2, Nat.mul_assoc]
    have hP2 := Nat.mul_le_mul_right (2 ^ 16) hPure
    rw [← hMid] at hP2
    rw [hAssocL]
    exact Nat.le_trans hMul8 hP2
  · intro S hS
    apply atLeastBits_scale_session_loss (sLog := 11) hS
    show atLeastBits 139 _
    decide +kernel
  · intro S hS
    apply atLeastBits_scale_session_loss (sLog := 4) hS
    show atLeastBits 132 _
    decide +kernel

/-- **`#tooth` Legacy `GoldilocksExt2` Folding Bottleneck & Classical-128 Grover Ceiling
    (`tooth_hem_ext2_folding_under_100bits`)**:
    1. Over `GoldilocksExt2` (`p^2 < 2^128`), at domain `|D| = 2^22`, even `|D|^2 / p^2 = 2^44 / p^2`
       falls strictly below 100 bits (`exceedsBitBudget 100`, ~84 bits before `(2η)^7` loss!),
    2. On `bciksJohnsonClassical128` Stage 0 (`q_0 = 129`, `16`b PoW = `~144` classical round bits),
       offline quantum Grover grinding at `qHash = 2 ^ 72` breaks quantum soundness
       (`exceedsBitBudget 0`), justifying why default `bciksJohnsonQrom128` (`q = 258, 130, 88, 66`)
       is required for `136`-bit QROM round-search work! -/
theorem tooth_hem_ext2_folding_under_100bits :
    exceedsBitBudget 100 ⟨(2 ^ 22) ^ 2, goldilocksExt2Card, goldilocksExt2Card_pos⟩ ∧
    exceedsBitBudget 0
      (quantumGroverGrindingBound (2 ^ 72)
        (whirPositiveEtaJohnsonStageBound ⟨2, 6, 26, 129, by decide⟩ 128 (by decide) 16)) := by
  refine ⟨by unfold exceedsBitBudget goldilocksExt2Card goldilocksPrime; decide,
          by unfold exceedsBitBudget quantumGroverGrindingBound whirPositiveEtaJohnsonStageBound
               RatBound.scale; decide⟩


/-! ## §5. Fast-Factored ZKBoo (`BlindVc` `219` vs `438`) & Remaining Deployed Suite
           (`ThresholdMlDsa`, `Poseidon2Toprf`, `DensePcg`, `HdRekey`, `ActiveMigration`) -/

/-! ### §5.1 Fast-Factored `3 ^ 73` Engine for `BlindVc` (`219` vs `438` Repetitions) -/

/-- Exact per-repetition ZKBoo soundness error `2 / 3` (`blind_vc.rs:48`, `zk_engine.rs:16`). -/
def zkbooSingleRepError : RatBound := ⟨2, 3, by decide⟩

def blindVcClassical128Reps : Nat := 219
def blindVcQuantum128Reps : Nat := 438

/-- Kernel-instant 35-digit base bounds on `3 ^ 73` (`3 ^ 73 = 67585198634817526699668407807368083`,
    `2 ^ 115 = 41538374868278621028243970633760768`):
    `13 * 2 ^ 115 < 8 * 3 ^ 73` (`(13/8)^3 = 2197/512 > 4` and `(13/8)^6 = 4826809/262144 > 16`)
    and `3 ^ 73 < 2 ^ 116` (`(3^73)^3 < 2^348`). -/
private theorem zkboo_pow73_sandwich :
    13 * 2 ^ 115 < 8 * 3 ^ 73 ∧ 3 ^ 73 < 2 ^ 116 :=
  ⟨by decide, by decide⟩

private theorem nat_pow_lt_pow_succ {a b : Nat} (h : a < b) :
    ∀ k : Nat, a ^ (k + 1) < b ^ (k + 1)
  | 0 => by simp [h]
  | k + 1 => by
    have ih := nat_pow_lt_pow_succ h k
    rw [Nat.pow_succ a (k + 1), Nat.pow_succ b (k + 1)]
    have hbPos : 0 < b := Nat.lt_of_le_of_lt (Nat.zero_le a) h
    have h1 : a ^ (k + 1) * a ≤ a ^ (k + 1) * b :=
      Nat.mul_le_mul_left (a ^ (k + 1)) (Nat.le_of_lt h)
    have h2 : a ^ (k + 1) * b < b ^ (k + 1) * b :=
      Nat.mul_lt_mul_of_pos_right ih hbPos
    exact Nat.lt_of_le_of_lt h1 h2

private theorem nat_lt_of_mul_lt_mul_left {k a b : Nat} (h : k * a < k * b) : a < b :=
  if hab : a < b then hab
  else absurd (Nat.mul_le_mul_left k (Nat.le_of_not_lt hab)) (Nat.not_le_of_gt h)

/-- Fast constructive proof of `2 ^ 219 * 2 ^ 128 < 3 ^ 219 < 2 ^ 219 * 2 ^ 129` by cubing `3 ^ 73`,
    never building large unstructured proof terms (`0` classical choice). -/
theorem zkboo_219_exact_bit_sandwich :
    2 ^ 219 * 2 ^ 128 < 3 ^ 219 ∧ 3 ^ 219 < 2 ^ 219 * 2 ^ 129 := by
  rcases zkboo_pow73_sandwich with ⟨hLo, hHi⟩
  constructor
  · have hCube : (13 * 2 ^ 115) ^ 3 < (8 * 3 ^ 73) ^ 3 :=
      nat_pow_lt_pow_succ hLo 2
    rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul] at hCube
    have hL : 2 ^ 9 * (2 ^ 219 * 2 ^ 128) < 13 ^ 3 * 2 ^ (115 * 3) := by
      have h13 : 2 ^ 11 < 13 ^ 3 := by decide
      have hp : 2 ^ 9 * (2 ^ 219 * 2 ^ 128) = 2 ^ 11 * 2 ^ (115 * 3) := by
        simp only [← Nat.pow_add]
      rw [hp]
      exact Nat.mul_lt_mul_of_pos_right h13 (Nat.two_pow_pos _)
    have hR : 8 ^ 3 * 3 ^ (73 * 3) = 2 ^ 9 * 3 ^ 219 := by
      have h8 : (8 : Nat) ^ 3 = 2 ^ 9 := by decide
      rw [h8]
    rw [hR] at hCube
    exact nat_lt_of_mul_lt_mul_left (Nat.lt_trans hL hCube)
  · have hCubeHi : (3 ^ 73) ^ 3 < (2 ^ 116) ^ 3 :=
      nat_pow_lt_pow_succ hHi 2
    rw [← Nat.pow_mul, ← Nat.pow_mul] at hCubeHi
    have hEq2 : 2 ^ (116 * 3) = 2 ^ 219 * 2 ^ 129 := by simp only [← Nat.pow_add]
    have hEq3 : 3 ^ (73 * 3) = 3 ^ 219 := rfl
    rw [hEq3, hEq2] at hCubeHi
    exact hCubeHi

/-- Fast constructive proof of `2 ^ 438 * 2 ^ 256 < 3 ^ 438` by raising `13 * 2 ^ 115 < 8 * 3 ^ 73`
    to the 6th power (`13 ^ 6 = 4,826,809 > 2 ^ 22 = 4,194,304`, `8 ^ 6 = 2 ^ 18`). -/
theorem zkboo_438_gt_two_pow_256_margin :
    2 ^ 438 * 2 ^ 256 < 3 ^ 438 := by
  have hLo := zkboo_pow73_sandwich.1
  have hSix : (13 * 2 ^ 115) ^ 6 < (8 * 3 ^ 73) ^ 6 :=
    nat_pow_lt_pow_succ hLo 5
  rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul] at hSix
  have hL : 2 ^ 18 * (2 ^ 438 * 2 ^ 256) < 13 ^ 6 * 2 ^ (115 * 6) := by
    have h13 : 2 ^ 22 < 13 ^ 6 := by decide
    have hp : 2 ^ 18 * (2 ^ 438 * 2 ^ 256) = 2 ^ 22 * 2 ^ (115 * 6) := by
      simp only [← Nat.pow_add]
    rw [hp]
    exact Nat.mul_lt_mul_of_pos_right h13 (Nat.two_pow_pos _)
  have hR : 8 ^ 6 * 3 ^ (73 * 6) = 2 ^ 18 * 3 ^ 438 := by
    have h8 : (8 : Nat) ^ 6 = 2 ^ 18 := by decide
    rw [h8]
  rw [hR] at hSix
  exact nat_lt_of_mul_lt_mul_left (Nat.lt_trans hL hSix)

/-- **`BlindVc` `Classical128` (`219` Reps) vs `Quantum128` (`438` Reps) Soundness Theorem**:
    1. `(2/3)^219 < 2^-128` (`strictlyMoreThanBits 128` interactive statistical soundness),
    2. `(2/3)^438 < 2^-256` (`strictlyMoreThanBits 256` statistical soundness),
    3. Under BOTH unitary O2H Grover grinding (`quantumGroverGrindingBound` for `qHash + 1 ≤ 2^62`)
       AND Don–Fehr–Majenz `[DFM20]` single-challenge Measure-and-Reprogram
       (`quantumDfmMeasureReprogramBound 1 qHash` for `2 * qHash + 1 ≤ 2^64`), `Quantum128` (`438` reps)
       certifies **`atLeastBits 128` quantum Fiat–Shamir soundness**! -/
theorem blindvc_classical219_and_quantum438_soundness :
    strictlyMoreThanBits 128 (zkbooSingleRepError.pow blindVcClassical128Reps) ∧
    strictlyMoreThanBits 256 (zkbooSingleRepError.pow blindVcQuantum128Reps) ∧
    (∀ qHash : Nat, qHash + 1 ≤ 2 ^ 62 →
      atLeastBits 129
        (quantumGroverGrindingBound qHash (zkbooSingleRepError.pow blindVcQuantum128Reps))) ∧
    (∀ qHash : Nat, 2 * qHash + 1 ≤ 2 ^ 64 →
      atLeastBits 128
        (quantumDfmMeasureReprogramBound 1 qHash (zkbooSingleRepError.pow blindVcQuantum128Reps))) := by
  refine ⟨zkboo_219_exact_bit_sandwich.1, zkboo_438_gt_two_pow_256_margin, ?_, ?_⟩
  · intro qHash hq
    unfold atLeastBits quantumGroverGrindingBound RatBound.scale RatBound.pow
      zkbooSingleRepError blindVcQuantum128Reps
    dsimp only
    have h8 : 8 * (qHash + 1) ^ 2 ≤ 2 ^ 127 := by
      have p1 : (qHash + 1) ^ 2 ≤ (2 ^ 62) ^ 2 := Nat.pow_le_pow_left hq 2
      have p2 : 8 * (2 ^ 62) ^ 2 = 2 ^ 127 := by decide
      rw [← p2]; exact Nat.mul_le_mul_left 8 p1
    have hMul := Nat.mul_le_mul_right (2 ^ 438 * 2 ^ 129) h8
    have hAssoc : 8 * (qHash + 1) ^ 2 * 2 ^ 438 * 2 ^ 129 =
        8 * (qHash + 1) ^ 2 * (2 ^ 438 * 2 ^ 129) := by simp only [Nat.mul_assoc]
    have hPowEq : 2 ^ 127 * (2 ^ 438 * 2 ^ 129) = 2 ^ 438 * 2 ^ 256 := by
      simp only [← Nat.pow_add]
    rw [hPowEq] at hMul
    rw [hAssoc]
    exact Nat.le_trans hMul (Nat.le_of_lt zkboo_438_gt_two_pow_256_margin)
  · intro qHash hq
    unfold atLeastBits quantumDfmMeasureReprogramBound RatBound.scale RatBound.pow
      zkbooSingleRepError blindVcQuantum128Reps
    dsimp only
    have hSq : (2 * qHash + 1) ^ (2 * 1) ≤ (2 ^ 64) ^ 2 := Nat.pow_le_pow_left hq 2
    have hMul := Nat.mul_le_mul_right (2 ^ 438 * 2 ^ 128) hSq
    have hAssoc : (2 * qHash + 1) ^ (2 * 1) * 2 ^ 438 * 2 ^ 128 =
        (2 * qHash + 1) ^ (2 * 1) * (2 ^ 438 * 2 ^ 128) := by simp only [Nat.mul_assoc]
    have hPowEq : (2 ^ 64) ^ 2 * (2 ^ 438 * 2 ^ 128) = 2 ^ 438 * 2 ^ 256 := by decide
    rw [hPowEq] at hMul
    rw [hAssoc]
    exact Nat.le_trans hMul (Nat.le_of_lt zkboo_438_gt_two_pow_256_margin)

/-- **`#tooth` ZKBoo 219-Repetition Quantum Grinding Ceiling (`tooth_zkboo_219_quantum_grind_64bit`)**:
    Because `3 ^ 219 < 2 ^ 219 * 2 ^ 129` (`(2/3)^219 > 2^-129`), `Classical128` (`219` reps) achieves
    only `~64.05` quantum Fiat–Shamir grinding bits: at `qHash = 2 ^ 64`, BOTH
    `quantumGroverGrindingBound` and `groverPureSearchBound`-scaled `(2^64)^2 * (2/3)^219` exceed `1`
    (`exceedsBitBudget 0`), proving why `Quantum128 = 438` is mandatory for `PQ128`! -/
theorem tooth_zkboo_219_quantum_grind_64bit :
    exceedsBitBudget 129 (zkbooSingleRepError.pow blindVcClassical128Reps) ∧
    exceedsBitBudget 0
      (RatBound.scale ((2 ^ 65) ^ 2) (zkbooSingleRepError.pow blindVcClassical128Reps)) ∧
    exceedsBitBudget 0
      (quantumGroverGrindingBound (2 ^ 64) (zkbooSingleRepError.pow blindVcClassical128Reps)) := by
  have hHi := zkboo_219_exact_bit_sandwich.2
  refine ⟨hHi, ?_, ?_⟩
  · unfold exceedsBitBudget RatBound.scale RatBound.pow zkbooSingleRepError blindVcClassical128Reps
    dsimp only
    rw [Nat.pow_zero, Nat.mul_one]
    have hEq : (2 ^ 65) ^ 2 * 2 ^ 219 = 2 ^ 219 * 2 ^ 129 * 2 := by decide
    rw [hEq]
    omega
  · unfold exceedsBitBudget quantumGroverGrindingBound RatBound.scale RatBound.pow
      zkbooSingleRepError blindVcClassical128Reps
    dsimp only
    rw [Nat.pow_zero, Nat.mul_one]
    have hGe : 2 ^ 219 * 2 ^ 129 ≤ 8 * (2 ^ 64 + 1) ^ 2 * 2 ^ 219 := by
      have p1 : 2 ^ 129 ≤ 8 * (2 ^ 64 + 1) ^ 2 := by decide
      rw [Nat.mul_comm (2 ^ 219) (2 ^ 129)]
      exact Nat.mul_le_mul_right (2 ^ 219) p1
    omega

/-! ### §5.2 `ThresholdMlDsa`, `Poseidon2Toprf`, `DensePcg`, `HdRekey` (Exact 96-Bit Bias) & `ActiveMigration` -/

/-- Exact `ML-DSA-44` (`FIPS 204`) challenge ball size `2^39 * C(256, 39)` (`≈ 2^192.76 > 2^192`),
    computed via the exact falling factorial `256 * 255 * ... * 218 / 39!`. -/
def mldsa44ChallengeLowerBound : Nat :=
  (2 ^ 39 *
    (256 * 255 * 254 * 253 * 252 * 251 * 250 * 249 * 248 * 247 * 246 * 245 * 244 *
     243 * 242 * 241 * 240 * 239 * 238 * 237 * 236 * 235 * 234 * 233 * 232 * 231 *
     230 * 229 * 228 * 227 * 226 * 225 * 224 * 223 * 222 * 221 * 220 * 219 * 218)) /
    (1 * 2 * 3 * 4 * 5 * 6 * 7 * 8 * 9 * 10 * 11 * 12 * 13 *
     14 * 15 * 16 * 17 * 18 * 19 * 20 * 21 * 22 * 23 * 24 * 25 * 26 *
     27 * 28 * 29 * 30 * 31 * 32 * 33 * 34 * 35 * 36 * 37 * 38 * 39)

theorem threshold_mldsa_challenge_and_dkg_commit_pq128 (qHash : Nat) (hq : qHash + 1 ≤ 2 ^ 62) :
    2 ^ 192 < mldsa44ChallengeLowerBound ∧
    atLeastBits 129 (quantumGroverSingleTargetBound 256 qHash) :=
  ⟨by unfold mldsa44ChallengeLowerBound; decide,
   qrom_single_target_parametric_bits hq (by decide)⟩

/-! #### FIPS 204 challenge spaces and the offline grinding regime per parameter set

FIPS 204 (ML-DSA), Table 1 and Table 2: ML-DSA-44 / 65 / 87 claim NIST security categories
2 / 3 / 5 and sample the challenge from the ball `B_τ` of ternary polynomials of weight
`τ = 39 / 49 / 60`, of size `2^τ · C(256, τ)` (`crates/qsag-cred/src/fips204_ntt.rs:133-177`
carries the same three rows). Category 2 is defined against collision search on SHA-256, not
against a 128-bit quantum preimage search, and the 192-bit challenge space of ML-DSA-44 is sized
for that claim.

The offline term below is the search term of the QROM Fiat–Shamir analysis of Kiltz, Lyubashevsky
and Schaffner ("A Concrete Treatment of Fiat–Shamir Signatures in the Quantum Random-Oracle
Model", EUROCRYPT 2018): a `qHash`-query adversary finds a challenge in a set of density `1/|C|`
with probability at most `8 (qHash + 1)^2 / |C|`. It is a budget for that provable bound; no
forgery of ML-DSA by challenge grinding alone is known. -/

/-- The three FIPS 204 parameter sets. -/
inductive MlDsaParamSet where
  | mldsa44
  | mldsa65
  | mldsa87
  deriving DecidableEq, Repr

/-- Challenge weight `τ` (FIPS 204 Table 1). -/
def MlDsaParamSet.tau : MlDsaParamSet → Nat
  | .mldsa44 => 39
  | .mldsa65 => 49
  | .mldsa87 => 60

/-- Claimed NIST security category (FIPS 204 Table 1). -/
def MlDsaParamSet.nistCategory : MlDsaParamSet → Nat
  | .mldsa44 => 2
  | .mldsa65 => 3
  | .mldsa87 => 5

/-- Largest `k` for which the threshold ML-DSA portfolio entry of this parameter set keeps 128
    bits at `qHash + 1 ≤ 2^k` and `2^20` online sessions
    (`threshold_mldsa_entry_pq128_within_ceiling`, exact by
    `tooth_threshold_mldsa_entry_above_ceiling_not_pq128`). -/
def MlDsaParamSet.pq128HashQueryCeilingLog2 : MlDsaParamSet → Nat
  | .mldsa44 => 30
  | .mldsa65 => 47
  | .mldsa87 => 62

/-- `C(n, k)` by the exact running product `C(n, i + 1) = C(n, i) · (n − i) / (i + 1)`. -/
def binomialProduct (n k : Nat) : Nat :=
  (List.range k).foldl (fun acc i => acc * (n - i) / (i + 1)) 1

/-- Size of the FIPS 204 challenge ball `B_τ`: `2^τ · C(256, τ)`. -/
def mlDsaChallengeCard (p : MlDsaParamSet) : Nat := 2 ^ p.tau * binomialProduct 256 p.tau

theorem mlDsaChallengeCard_pos (p : MlDsaParamSet) : 0 < mlDsaChallengeCard p := by
  cases p <;> decide

/-- Exact bit intervals: 192, 225 and 257 bits of challenge entropy, and agreement of the
    ML-DSA-44 value with the falling-factorial form `mldsa44ChallengeLowerBound`. -/
theorem mlDsaChallengeCard_bit_intervals :
    mlDsaChallengeCard .mldsa44 = mldsa44ChallengeLowerBound ∧
    (2 ^ 192 < mlDsaChallengeCard .mldsa44 ∧ mlDsaChallengeCard .mldsa44 < 2 ^ 193) ∧
    (2 ^ 225 < mlDsaChallengeCard .mldsa65 ∧ mlDsaChallengeCard .mldsa65 < 2 ^ 226) ∧
    (2 * 2 ^ 256 < mlDsaChallengeCard .mldsa87 ∧ mlDsaChallengeCard .mldsa87 < 4 * 2 ^ 256) := by
  decide

/-- Offline Fiat–Shamir challenge search in the QROM: `8 (qHash + 1)^2 / |B_τ|`. -/
def mlDsaOfflineChallengeQuantumBound (p : MlDsaParamSet) (qHash : Nat) : RatBound :=
  ⟨8 * (qHash + 1) ^ 2, mlDsaChallengeCard p, mlDsaChallengeCard_pos p⟩

/-- Classical offline challenge search: `(qHash + 1) / |B_τ|`. -/
def mlDsaOfflineChallengeClassicalBound (p : MlDsaParamSet) (qHash : Nat) : RatBound :=
  ⟨qHash + 1, mlDsaChallengeCard p, mlDsaChallengeCard_pos p⟩

private theorem mlDsaOffline_bits_of_cap (p : MlDsaParamSet) (k bits q : Nat)
    (hq : q + 1 ≤ 2 ^ k) (hcap : 8 * (2 ^ k) ^ 2 * 2 ^ bits ≤ mlDsaChallengeCard p) :
    atLeastBits bits (mlDsaOfflineChallengeQuantumBound p q) := by
  unfold atLeastBits mlDsaOfflineChallengeQuantumBound
  dsimp only
  exact Nat.le_trans
    (Nat.mul_le_mul_right (2 ^ bits) (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left hq 2))) hcap

private theorem mlDsaOffline_not_bits_of_floor (p : MlDsaParamSet) (k bits q : Nat)
    (hq : q + 1 = 2 ^ k) (hfloor : mlDsaChallengeCard p < 8 * (2 ^ k) ^ 2 * 2 ^ bits) :
    ¬ atLeastBits bits (mlDsaOfflineChallengeQuantumBound p q) := by
  unfold atLeastBits mlDsaOfflineChallengeQuantumBound
  dsimp only
  rw [hq]
  exact Nat.not_le_of_gt hfloor

/-- Offline query ceilings under which each challenge space alone keeps 128 bits against QROM
    grinding: `2^30` for ML-DSA-44, `2^47` for ML-DSA-65, `2^63` for ML-DSA-87. The ceilings are
    exact to the power of two, see the three `tooth_mldsa*_offline_grinding_above_*` theorems. -/
theorem mlDsa_offline_grinding_pq128_regime :
    (∀ q : Nat, q + 1 ≤ 2 ^ 30 →
      atLeastBits 128 (mlDsaOfflineChallengeQuantumBound .mldsa44 q)) ∧
    (∀ q : Nat, q + 1 ≤ 2 ^ 47 →
      atLeastBits 128 (mlDsaOfflineChallengeQuantumBound .mldsa65 q)) ∧
    (∀ q : Nat, q + 1 ≤ 2 ^ 63 →
      atLeastBits 128 (mlDsaOfflineChallengeQuantumBound .mldsa87 q)) :=
  ⟨fun q hq => mlDsaOffline_bits_of_cap .mldsa44 30 128 q hq (by decide),
   fun q hq => mlDsaOffline_bits_of_cap .mldsa65 47 128 q hq (by decide),
   fun q hq => mlDsaOffline_bits_of_cap .mldsa87 63 128 q hq (by decide)⟩

/-- What each challenge space gives at the portfolio's `2^56` offline queries: 77, 110 and 142
    bits. Only ML-DSA-87 clears 128. -/
theorem mlDsa_offline_grinding_bits_at_2pow56 (q : Nat) (hq : q + 1 ≤ 2 ^ 56) :
    atLeastBits 77 (mlDsaOfflineChallengeQuantumBound .mldsa44 q) ∧
    atLeastBits 110 (mlDsaOfflineChallengeQuantumBound .mldsa65 q) ∧
    atLeastBits 142 (mlDsaOfflineChallengeQuantumBound .mldsa87 q) :=
  ⟨mlDsaOffline_bits_of_cap .mldsa44 56 77 q hq (by decide),
   mlDsaOffline_bits_of_cap .mldsa65 56 110 q hq (by decide),
   mlDsaOffline_bits_of_cap .mldsa87 56 142 q hq (by decide)⟩

theorem tooth_mldsa44_offline_grinding_above_2pow30 (q : Nat) (hq : q + 1 = 2 ^ 31) :
    ¬ atLeastBits 128 (mlDsaOfflineChallengeQuantumBound .mldsa44 q) :=
  mlDsaOffline_not_bits_of_floor .mldsa44 31 128 q hq (by decide)

theorem tooth_mldsa65_offline_grinding_above_2pow47 (q : Nat) (hq : q + 1 = 2 ^ 48) :
    ¬ atLeastBits 128 (mlDsaOfflineChallengeQuantumBound .mldsa65 q) :=
  mlDsaOffline_not_bits_of_floor .mldsa65 48 128 q hq (by decide)

theorem tooth_mldsa87_offline_grinding_above_2pow63 (q : Nat) (hq : q + 1 = 2 ^ 64) :
    ¬ atLeastBits 128 (mlDsaOfflineChallengeQuantumBound .mldsa87 q) :=
  mlDsaOffline_not_bits_of_floor .mldsa87 64 128 q hq (by decide)

/-- ML-DSA-44 at `2^56` offline queries: 77 bits is exact, 78 fails. -/
theorem tooth_mldsa44_offline_grinding_not_78_at_2pow56 (q : Nat) (hq : q + 1 = 2 ^ 56) :
    ¬ atLeastBits 78 (mlDsaOfflineChallengeQuantumBound .mldsa44 q) :=
  mlDsaOffline_not_bits_of_floor .mldsa44 56 78 q hq (by decide)

/-- ML-DSA-65 at `2^56` offline queries: 110 bits is exact, 111 fails. -/
theorem tooth_mldsa65_offline_grinding_not_111_at_2pow56 (q : Nat) (hq : q + 1 = 2 ^ 56) :
    ¬ atLeastBits 111 (mlDsaOfflineChallengeQuantumBound .mldsa65 q) :=
  mlDsaOffline_not_bits_of_floor .mldsa65 56 111 q hq (by decide)

/-- Parameter set the threshold protocol signs with: `threshold_mldsa.rs:405-407` rejects every
    level other than `MlDsaLevel::MlDsa44` with `ThresholdMlDsaError::UnsupportedLevel`. -/
def deployedThresholdMlDsaParamSet : MlDsaParamSet := .mldsa44

/-- `Poseidon2Toprf` 2-of-5 $\binom{5}{3} = 10$ replicated secret sharing: `0` statistical 1-curious-server
    leakage (`RatBound.zero`) + `Digest4` (`p^4 > 2^255`) salted input-root QROM target resistance! -/
def toprfDigest4QromBound (qHash : Nat) : RatBound :=
  ⟨8 * (qHash + 1) ^ 2, goldilocksExt4Card, goldilocksExt4Card_pos⟩

theorem poseidon2_toprf_privacy_and_root_qrom_pq128 (qHash : Nat) (hq : qHash + 1 ≤ 2 ^ 61) :
    atLeastBits 256 RatBound.zero ∧
    atLeastBits 128 (toprfDigest4QromBound qHash) := by
  refine ⟨by unfold atLeastBits RatBound.zero; simp, ?_⟩
  unfold atLeastBits toprfDigest4QromBound
  dsimp only
  have hSq : 8 * (qHash + 1) ^ 2 ≤ 2 ^ 125 := by
    have p1 : (qHash + 1) ^ 2 ≤ (2 ^ 61) ^ 2 := Nat.pow_le_pow_left hq 2
    have p2 : 8 * (2 ^ 61) ^ 2 = 2 ^ 125 := by decide
    rw [← p2]; exact Nat.mul_le_mul_left 8 p1
  have hm := Nat.mul_le_mul_right (2 ^ 128) hSq
  have hp : 2 ^ 125 * 2 ^ 128 ≤ goldilocksExt4Card := by
    unfold goldilocksExt4Card goldilocksPrime; decide
  exact Nat.le_trans hm hp

/-- `DensePcg` (`pcg_dense.rs:29`) 2-challenge `GF(2^128)` SPCOT consistency error
    `((2 ^ depth + 1) / (2 ^ 128 - 2)) ^ 2` across `qOnlineSessions` directed pairs. -/
def densePcgSpcotBound (depth qOnlineSessions : Nat) : RatBound :=
  RatBound.scale qOnlineSessions
    (RatBound.pow ⟨2 ^ depth + 1, 2 ^ 128 - 2, by decide⟩ 2)

/-! #### `DensePcg` V3 GGM forest: target count, per-node tweak, salted versus unsalted targets

Every internal GGM node of the V3 forest is expanded by one single-block `SHAKE256` call on the
96-byte block built by `encode_ggm_node_state` (`crates/qsag-core/src/pcg_dense.rs:227-256`):

| bytes    | field                                   |
|----------|-----------------------------------------|
| `0..16`  | domain tag `"QSAG.DPCG.GGM.N2"`         |
| `16..48` | `session_id` (32 bytes)                 |
| `48..50` | `sender_id` (`u16`, little-endian)      |
| `50..52` | `receiver_id` (`u16`, little-endian)    |
| `52`     | `tree_idx` (`u8`)                       |
| `53`     | `level` (`u8`)                          |
| `54..58` | `node_idx` (`u32`, little-endian)       |
| `58..90` | the 256-bit node seed (the secret)      |

Bytes `16..58` are a fixed-width tweak, so two expansions share a hash function only when they
agree on session, ordered peer pair, tree, level and node. The seed search against the forest is
therefore a search against one target under each of `M` distinct functions (the multi-function
multi-target setting of Hülsing, Rijneveld and Song, "Mitigating Multi-Target Attacks in
Hash-based Signatures", PKC 2016), and not against `M` targets of one function (Zhandry's
multi-target search bound, the optimality side being Bennett, Bernstein, Brassard and Vazirani,
"Strengths and Weaknesses of Quantum Computing", 1997). Both models are kept below. -/

/-- Internal PRG expansions in one V3 forest: `DENSE_PCG_NUM_TREES = 64` trees
    (`pcg_dense.rs:54`), each a complete binary tree of depth 15 whose level `lvl < 15` holds
    `2^lvl` expanded nodes (`ggm_expand_full_depth`, `pcg_dense.rs:288-322`). -/
def densePcgV3NodeTargets : Nat := 64 * (2 ^ 15 - 1)

theorem densePcgV3NodeTargets_exact :
    densePcgV3NodeTargets = 2097088 ∧
    densePcgV3NodeTargets = 64 * (List.range 15).foldl (fun acc lvl => acc + 2 ^ lvl) 0 ∧
    2048 * (64 * 15) < densePcgV3NodeTargets := by decide

/-- Integer value of block bytes `52..58`: `tree_idx` (one byte), `level` (one byte) and
    `node_idx` (four bytes, little-endian), as laid out at `pcg_dense.rs:243-245`. -/
def ggmNodeTweakIndex (tree level node : Nat) : Nat := tree + 2 ^ 8 * level + 2 ^ 16 * node

/-- The `(tree, level, node)` part of the tweak is injective on the byte widths of the block.
    The V3 ranges (`tree < 64`, `level < 15`, `node < 2^level ≤ 2^14`) lie inside them. -/
theorem ggmNodeTweakIndex_injective {t l i t' l' i' : Nat}
    (ht : t < 2 ^ 8) (hl : l < 2 ^ 8) (ht' : t' < 2 ^ 8) (hl' : l' < 2 ^ 8)
    (h : ggmNodeTweakIndex t l i = ggmNodeTweakIndex t' l' i') :
    t = t' ∧ l = l' ∧ i = i' := by
  unfold ggmNodeTweakIndex at h
  exact ⟨by omega, by omega, by omega⟩

/-- Without the one-byte width bound on `tree_idx` two different nodes share a tweak. -/
theorem tooth_ggmNodeTweakIndex_unbounded_tree_collides :
    ∃ t l i t' l' i' : Nat,
      ggmNodeTweakIndex t l i = ggmNodeTweakIndex t' l' i' ∧ t ≠ t' :=
  ⟨256, 0, 0, 0, 1, 0, by decide, by decide⟩

/-- Search bound against `M` tweaks, each tweak shared by `S` targets, with `qHash` hash queries
    in total: `8 · S · (qHash + M)^2 / 2^n`. `S = 1` is the salted V3 forest. It is the union over
    tweaks of the per-function `S`-target bound, see
    `tweaked_multi_target_query_partition_union_bound`. -/
def tweakedMultiTargetBound (n S M qHash : Nat) : RatBound :=
  ⟨8 * S * (qHash + M) ^ 2, 2 ^ n, Nat.two_pow_pos n⟩

/-- Classical counterpart: one guess per tweak plus the queries spent, `(qHash + M) / 2^n`. -/
def tweakedClassicalMultiTargetBound (n M qHash : Nat) : RatBound :=
  ⟨qHash + M, 2 ^ n, Nat.two_pow_pos n⟩

private def sumSqSucc : List Nat → Nat
  | [] => 0
  | q :: qs => (q + 1) ^ 2 + sumSqSucc qs

private def sumSucc : List Nat → Nat
  | [] => 0
  | q :: qs => (q + 1) + sumSucc qs

private theorem add_common_den_step {a d rn rd b : Nat} (h : rn * d ≤ b * rd) :
    (a * rd + rn * d) * d ≤ (a + b) * (d * rd) := by
  have h1 : rn * d * d ≤ b * rd * d := Nat.mul_le_mul_right d h
  have e1 : (a * rd + rn * d) * d = a * rd * d + rn * d * d := Nat.add_mul _ _ _
  have e2 : (a + b) * (d * rd) = a * rd * d + b * rd * d := by
    rw [Nat.add_mul, Nat.mul_comm d rd, ← Nat.mul_assoc, ← Nat.mul_assoc]
  rw [e1, e2]
  exact Nat.add_le_add_left h1 _

private theorem sq_add_sq_le_add_sq (a b : Nat) : a ^ 2 + b ^ 2 ≤ (a + b) ^ 2 := by
  rw [Nat.pow_two, Nat.pow_two, Nat.pow_two, Nat.add_mul]
  exact Nat.add_le_add (Nat.mul_le_mul_left a (Nat.le_add_right a b))
    (Nat.mul_le_mul_left b (Nat.le_add_left b a))

private theorem sumSqSucc_le_sq : ∀ qs : List Nat, sumSqSucc qs ≤ (qs.sum + qs.length) ^ 2
  | [] => Nat.zero_le _
  | q :: rs => by
    have e : (q :: rs).sum + (q :: rs).length = (q + 1) + (rs.sum + rs.length) := by
      rw [List.sum_cons, List.length_cons]; omega
    rw [e]
    exact Nat.le_trans (Nat.add_le_add_left (sumSqSucc_le_sq rs) _)
      (sq_add_sq_le_add_sq (q + 1) (rs.sum + rs.length))

private theorem sumSucc_eq : ∀ qs : List Nat, sumSucc qs = qs.sum + qs.length
  | [] => rfl
  | q :: rs => by
    have e : (q :: rs).sum + (q :: rs).length = (q + 1) + (rs.sum + rs.length) := by
      rw [List.sum_cons, List.length_cons]; omega
    rw [e, ← sumSucc_eq rs]
    rfl

private theorem sumList_tweak_quantum_le (n S : Nat) :
    ∀ qs : List Nat,
      RatBound.le (RatBound.sumList (qs.map (quantumZhandryMultiTargetBound n S)))
        ⟨8 * S * sumSqSucc qs, 2 ^ n, Nat.two_pow_pos n⟩
  | [] => by
    unfold RatBound.le
    dsimp only [List.map, RatBound.sumList, RatBound.zero]
    rw [Nat.zero_mul]
    exact Nat.zero_le _
  | q :: rs => by
    have ih := sumList_tweak_quantum_le n S rs
    unfold RatBound.le at ih ⊢
    dsimp only [List.map, RatBound.sumList, RatBound.add, quantumZhandryMultiTargetBound,
      sumSqSucc] at ih ⊢
    rw [Nat.mul_add]
    exact add_common_den_step ih

private theorem sumList_tweak_classical_le (n : Nat) :
    ∀ qs : List Nat,
      RatBound.le
        (RatBound.sumList (qs.map (fun qi => (⟨qi + 1, 2 ^ n, Nat.two_pow_pos n⟩ : RatBound))))
        ⟨sumSucc qs, 2 ^ n, Nat.two_pow_pos n⟩
  | [] => by
    unfold RatBound.le
    dsimp only [List.map, RatBound.sumList, RatBound.zero]
    rw [Nat.zero_mul]
    exact Nat.zero_le _
  | q :: rs => by
    have ih := sumList_tweak_classical_le n rs
    unfold RatBound.le at ih ⊢
    dsimp only [List.map, RatBound.sumList, RatBound.add, sumSucc] at ih ⊢
    exact add_common_den_step ih

/-- **Query-partition union bound for tweaked targets.** `qs` lists, per tweak, the number of
    hash queries the adversary spends under that tweak; a query under one tweak is a query to a
    different function than any other tweak's and gives nothing against the other targets. Each
    tweak carries `S` targets and is charged the `S`-target search bound
    `8 · S · (q_i + 1)^2 / 2^n` (`quantumZhandryMultiTargetBound`; `S = 1` is the single-target
    bound). If the allocation fits the budget, `Σ q_i ≤ q`, the union over all `M = qs.length`
    tweaks is at most `8 · S · (q + M)^2 / 2^n`, because `Σ (q_i + 1)^2 ≤ (Σ (q_i + 1))^2`.

    Contrast `quantumZhandryMultiTargetBound n M q = 8 · M · (q + 1)^2 / 2^n`, where all `M`
    targets sit under one function and every query counts against all of them: there the loss is
    a factor `M`, here it is an additive `M` inside the square.

    What carries the separation is distinctness of the tweaks: `session_id` unique per session and
    `(sender, receiver, tree, level, node)` injective into block bytes `48..58`
    (`ggmNodeTweakIndex_injective` for the last three). The allocation `qs` is by whole queries,
    which is exact for an adversary whose tweak register is classical. For queries in
    superposition over tweaks the per-tweak count is not defined; that full quantum superposition
    regime across `(t : Fin M) × (x : Fin (2 ^ n))` is mechanized below in
    `hrs16_superposition_multi_tweak_bound` and `hrs16_superposition_multi_tweak_pq256_bound`
    following Hülsing, Rijneveld and Song (PKC 2016), achieving `8 * (q + 1) ^ 2 / 2 ^ n` with
    zero linear dependence on `M`. -/
theorem tweaked_multi_target_query_partition_union_bound (n S q : Nat) (qs : List Nat)
    (hBudget : qs.sum ≤ q) :
    RatBound.le (RatBound.sumList (qs.map (quantumZhandryMultiTargetBound n S)))
      (tweakedMultiTargetBound n S qs.length q) := by
  refine RatBound.le_trans (sumList_tweak_quantum_le n S qs) ?_
  unfold RatBound.le tweakedMultiTargetBound
  dsimp only
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
    (Nat.le_trans (sumSqSucc_le_sq qs)
      (Nat.pow_le_pow_left (Nat.add_le_add_right hBudget _) 2)))

/-- Classical form of the partition bound: per tweak `(q_i + 1) / 2^n`, in total at most
    `(q + M) / 2^n`. -/
theorem tweaked_classical_query_partition_union_bound (n q : Nat) (qs : List Nat)
    (hBudget : qs.sum ≤ q) :
    RatBound.le
      (RatBound.sumList (qs.map (fun qi => (⟨qi + 1, 2 ^ n, Nat.two_pow_pos n⟩ : RatBound))))
      (tweakedClassicalMultiTargetBound n qs.length q) := by
  refine RatBound.le_trans (sumList_tweak_classical_le n qs) ?_
  unfold RatBound.le tweakedClassicalMultiTargetBound
  dsimp only
  rw [sumSucc_eq]
  exact Nat.mul_le_mul_right _ (Nat.add_le_add_right hBudget _)

private theorem salted_unsalted_expand (q m : Nat) :
    (m + 1) * (q + 1) ^ 2 + m * (m + 1) = (q + (m + 1)) ^ 2 + m * (q * q) := by
  simp only [Nat.pow_two, Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
  have h : q * m = m * q := Nat.mul_comm q m
  omega

private theorem lt_of_add_eq_add {A B x y : Nat} (e : A + x = B + y) (h : x < y) : B < A := by
  omega

private theorem le_of_add_eq_add {A B x y : Nat} (e : A + x = B + y) (h : y ≤ x) : A ≤ B := by
  omega

/-- The salted bound is strictly below the unsalted one exactly once `q^2` exceeds the target
    count: `M · (q + 1)^2 − (q + M)^2 = (M − 1) · (q^2 − M)`. -/
theorem tweaked_lt_untweaked_of_targets_lt_sq (n q M : Nat) (hM : 2 ≤ M) (hq : M < q * q) :
    RatBound.lt (tweakedMultiTargetBound n 1 M q) (quantumZhandryMultiTargetBound n M q) := by
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
  have hcore : (q + (m + 1)) ^ 2 < (m + 1) * (q + 1) ^ 2 :=
    lt_of_add_eq_add (salted_unsalted_expand q m)
      (Nat.mul_lt_mul_of_pos_left hq (by omega))
  unfold RatBound.lt tweakedMultiTargetBound quantumZhandryMultiTargetBound
  dsimp only
  rw [Nat.mul_one, Nat.mul_assoc 8 (m + 1)]
  exact Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_left hcore (by decide))
    (Nat.two_pow_pos n)

/-- Below the crossover the additive `M` dominates and the union form is the weaker bound. -/
theorem untweaked_le_tweaked_of_sq_le_targets (n q M : Nat) (hM : 1 ≤ M) (hq : q * q ≤ M) :
    RatBound.le (quantumZhandryMultiTargetBound n M q) (tweakedMultiTargetBound n 1 M q) := by
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
  have hcore : (m + 1) * (q + 1) ^ 2 ≤ (q + (m + 1)) ^ 2 :=
    le_of_add_eq_add (salted_unsalted_expand q m) (Nat.mul_le_mul_left m hq)
  unfold RatBound.le tweakedMultiTargetBound quantumZhandryMultiTargetBound
  dsimp only
  rw [Nat.mul_one, Nat.mul_assoc 8 (m + 1)]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 8 hcore)

/-- Offline hash-query budget used for the V3 seed-search statements. -/
def DensePcgV3QueryBudget (q : Nat) : Prop := q + 1 ≤ 2 ^ 56

/-- Unsalted model: all `densePcgV3NodeTargets` seeds as targets of one function. This is what
    the forest would cost if the node block carried no tweak. -/
def densePcgV3SeedQuantumBound (qHash : Nat) : RatBound :=
  quantumZhandryMultiTargetBound 256 densePcgV3NodeTargets qHash

/-- `S` sessions run under one repeated `session_id`: every tweak is shared by `S` seeds. -/
def densePcgV3SharedTweakSeedQuantumBound (S qHash : Nat) : RatBound :=
  tweakedMultiTargetBound 256 S densePcgV3NodeTargets qHash

/-- Salted V3 model: one seed per tweak. -/
def densePcgV3SaltedSeedQuantumBound (qHash : Nat) : RatBound :=
  densePcgV3SharedTweakSeedQuantumBound 1 qHash

def densePcgV3SaltedSeedClassicalBound (qHash : Nat) : RatBound :=
  tweakedClassicalMultiTargetBound 256 densePcgV3NodeTargets qHash

/-- Salted V3 forest at `q + 1 ≤ 2^56`: 140 bits. -/
theorem densePcgV3SaltedSeedQuantumBound_140 (q : Nat) (hq : DensePcgV3QueryBudget q) :
    atLeastBits 140 (densePcgV3SaltedSeedQuantumBound q) := by
  unfold atLeastBits densePcgV3SaltedSeedQuantumBound densePcgV3SharedTweakSeedQuantumBound
    tweakedMultiTargetBound
  dsimp only
  exact Nat.le_trans
    (Nat.mul_le_mul_right (2 ^ 140)
      (Nat.mul_le_mul_left (8 * 1)
        (Nat.pow_le_pow_left
          (Nat.add_le_add_right (Nat.le_of_succ_le hq) densePcgV3NodeTargets) 2)))
    (by decide)

/-- 140 is exact at the ceiling: the salted bound is above `2^-141` at `q + 1 = 2^56`. -/
theorem tooth_densePcgV3_salted_not_141 (q : Nat) (hq : q + 1 = 2 ^ 56) :
    ¬ atLeastBits 141 (densePcgV3SaltedSeedQuantumBound q) := by
  obtain rfl : q = 2 ^ 56 - 1 := by omega
  unfold atLeastBits densePcgV3SaltedSeedQuantumBound densePcgV3SharedTweakSeedQuantumBound
    tweakedMultiTargetBound
  dsimp only
  decide

/-- Unsalted model at `q + 1 ≤ 2^56`: 120 bits. -/
theorem densePcgV3SeedQuantumBound_120 (q : Nat) (hq : DensePcgV3QueryBudget q) :
    atLeastBits 120 (densePcgV3SeedQuantumBound q) := by
  unfold atLeastBits densePcgV3SeedQuantumBound quantumZhandryMultiTargetBound
  dsimp only
  exact Nat.le_trans
    (Nat.mul_le_mul_right (2 ^ 120)
      (Nat.mul_le_mul_left (8 * densePcgV3NodeTargets) (Nat.pow_le_pow_left hq 2)))
    (by decide)

/-- Unsalted model reaches 128 bits only for `q + 1 ≤ 2^52`. -/
theorem densePcgV3SeedQuantumBound_128 (q : Nat) (hq : q + 1 ≤ 2 ^ 52) :
    atLeastBits 128 (densePcgV3SeedQuantumBound q) := by
  unfold atLeastBits densePcgV3SeedQuantumBound quantumZhandryMultiTargetBound
  dsimp only
  exact Nat.le_trans
    (Nat.mul_le_mul_right (2 ^ 128)
      (Nat.mul_le_mul_left (8 * densePcgV3NodeTargets) (Nat.pow_le_pow_left hq 2)))
    (by decide)

/-- Dropping the tweak from the node block: the forest fails PQ128 at `q + 1 = 2^56`. -/
theorem tooth_densePcgV3_untweaked_not_pq128 (q : Nat) (hq : q + 1 = 2 ^ 56) :
    ¬ atLeastBits 128 (densePcgV3SeedQuantumBound q) := by
  unfold atLeastBits densePcgV3SeedQuantumBound quantumZhandryMultiTargetBound
  dsimp only
  rw [hq]
  decide

/-- The partition bound does not cover untweaked targets: at the production ceiling the
    one-function bound is not below the salted one. -/
theorem tooth_untweaked_targets_exceed_partition_bound (q : Nat) (hq : q + 1 = 2 ^ 56) :
    ¬ RatBound.le (densePcgV3SeedQuantumBound q) (densePcgV3SaltedSeedQuantumBound q) := by
  obtain rfl : q = 2 ^ 56 - 1 := by omega
  unfold RatBound.le densePcgV3SeedQuantumBound densePcgV3SaltedSeedQuantumBound
    densePcgV3SharedTweakSeedQuantumBound tweakedMultiTargetBound quantumZhandryMultiTargetBound
  dsimp only
  decide

/-- **Salted V3 seed search, end to end.** For every allocation `qs` of at most `q` hash queries
    (`q + 1 ≤ 2^56`) over the `densePcgV3NodeTargets` node tweaks of the forest, the union of the
    per-tweak single-target QROM bounds `8 (q_i + 1)^2 / 2^256` is at most `2^-140`. -/
theorem densePcgV3_partitioned_seed_search_140 (q : Nat) (qs : List Nat)
    (hLen : qs.length = densePcgV3NodeTargets) (hBudget : qs.sum ≤ q)
    (hq : DensePcgV3QueryBudget q) :
    atLeastBits 140 (RatBound.sumList (qs.map (quantumGroverSingleTargetBound 256))) := by
  have hUnion := tweaked_multi_target_query_partition_union_bound 256 1 q qs hBudget
  rw [hLen] at hUnion
  exact atLeastBits_of_le hUnion (densePcgV3SaltedSeedQuantumBound_140 q hq)

/-- Exact crossover for the V3 forest: `1448^2 < M < 1449^2`, so from 1449 queries on the salted
    bound is strictly the smaller one, and up to 1448 queries the unsalted form is. -/
theorem densePcgV3_salted_unsalted_crossover :
    1448 * 1448 < densePcgV3NodeTargets ∧ densePcgV3NodeTargets < 1449 * 1449 ∧
    (∀ q : Nat, 1449 ≤ q →
      RatBound.lt (densePcgV3SaltedSeedQuantumBound q) (densePcgV3SeedQuantumBound q)) ∧
    (∀ q : Nat, q ≤ 1448 →
      RatBound.le (densePcgV3SeedQuantumBound q) (densePcgV3SaltedSeedQuantumBound q)) := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · intro q hq
    exact tweaked_lt_untweaked_of_targets_lt_sq 256 q densePcgV3NodeTargets (by decide)
      (Nat.lt_of_lt_of_le (by decide : densePcgV3NodeTargets < 1449 * 1449)
        (Nat.mul_le_mul hq hq))
  · intro q hq
    exact untweaked_le_tweaked_of_sq_le_targets 256 q densePcgV3NodeTargets (by decide)
      (Nat.le_trans (Nat.mul_le_mul hq hq)
        (Nat.le_of_lt (by decide : 1448 * 1448 < densePcgV3NodeTargets)))

/-- `session_id` repeated across `S ≤ 2^12` sessions still leaves 128 bits at `q + 1 ≤ 2^56`:
    each doubling of `S` costs one bit of the 140. -/
theorem densePcgV3SharedTweakSeedQuantumBound_128 (S q : Nat) (hS : S ≤ 2 ^ 12)
    (hq : DensePcgV3QueryBudget q) :
    atLeastBits 128 (densePcgV3SharedTweakSeedQuantumBound S q) := by
  unfold atLeastBits densePcgV3SharedTweakSeedQuantumBound tweakedMultiTargetBound
  dsimp only
  exact Nat.le_trans
    (Nat.mul_le_mul_right (2 ^ 128)
      (Nat.mul_le_mul (Nat.mul_le_mul_left 8 hS)
        (Nat.pow_le_pow_left
          (Nat.add_le_add_right (Nat.le_of_succ_le hq) densePcgV3NodeTargets) 2)))
    (by decide)

/-- `session_id` repeated across `2^13` sessions: the forest fails PQ128 at `q + 1 = 2^56`. -/
theorem tooth_densePcgV3_session_id_reuse_not_pq128 (q : Nat) (hq : q + 1 = 2 ^ 56) :
    ¬ atLeastBits 128 (densePcgV3SharedTweakSeedQuantumBound (2 ^ 13) q) := by
  obtain rfl : q = 2 ^ 56 - 1 := by omega
  unfold atLeastBits densePcgV3SharedTweakSeedQuantumBound tweakedMultiTargetBound
  dsimp only
  decide

theorem witness_densePcgV3_query_budget : ∃ q : Nat, DensePcgV3QueryBudget q :=
  ⟨2 ^ 56 - 1, by unfold DensePcgV3QueryBudget; decide⟩

theorem witness_densePcgV3_shared_tweak_budget :
    ∃ S q : Nat, S ≤ 2 ^ 12 ∧ DensePcgV3QueryBudget q :=
  ⟨2 ^ 12, 2 ^ 56 - 1, by decide, by unfold DensePcgV3QueryBudget; decide⟩

private theorem sum_replicate_nat (m a : Nat) : (List.replicate m a).sum = m * a := by
  induction m with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.sum_cons, ih, Nat.succ_mul, Nat.add_comm]

/-- A query allocation at production size: `2^34` queries under each of the
    `densePcgV3NodeTargets` tweaks, inside the `2^56` budget. -/
theorem witness_densePcgV3_query_partition :
    ∃ (qs : List Nat) (q : Nat),
      qs.sum ≤ q ∧ qs.length = densePcgV3NodeTargets ∧ DensePcgV3QueryBudget q :=
  ⟨List.replicate densePcgV3NodeTargets (2 ^ 34), 2 ^ 56 - 1,
    by rw [sum_replicate_nat]; decide,
    List.length_replicate,
    by unfold DensePcgV3QueryBudget; decide⟩

/-- **`DensePcg` Active SPCOT Soundness & `#tooth` 128-Bit Seed Grover Bottleneck**:
    1. Interactive 2-challenge SPCOT achieves `strictlyMoreThanBits 225` per directed pair at `depth = 15`
       (`strictlyMoreThanBits 227` at `depth = 14`, and `atLeastBits 193` across `2^32` sessions!),
    2. `#tooth` `tooth_dense_pcg_128bit_seed_grover_64bit`: 128-bit GGM seeds cap quantum seed-search
       at 64 Grover bits (`exceedsBitBudget 0` at `qHash = 2^64`), whereas the 256-bit, per-node
       tweaked V3 forest of `densePcgV3NodeTargets` seeds achieves `atLeastBits 140` at
       `qHash + 1 ≤ 2^56` (`densePcgV3SaltedSeedQuantumBound_140`). -/
theorem dense_pcg_spcot_and_tooth_128bit_seed :
    strictlyMoreThanBits 225 (densePcgSpcotBound 15 1) ∧
    strictlyMoreThanBits 227 (densePcgSpcotBound 14 1) ∧
    (∀ qSess : Nat, qSess ≤ 2 ^ 32 → atLeastBits 193 (densePcgSpcotBound 15 qSess)) ∧
    exceedsBitBudget 0 (quantumGroverSingleTargetBound 128 (2 ^ 64)) ∧
    (∀ qHash : Nat, qHash + 1 ≤ 2 ^ 56 →
      atLeastBits 140 (densePcgV3SaltedSeedQuantumBound qHash)) := by
  refine ⟨by unfold strictlyMoreThanBits densePcgSpcotBound RatBound.scale RatBound.pow; decide,
          by unfold strictlyMoreThanBits densePcgSpcotBound RatBound.scale RatBound.pow; decide,
          ?_, by unfold exceedsBitBudget quantumGroverSingleTargetBound quantumZhandryMultiTargetBound; decide,
          densePcgV3SaltedSeedQuantumBound_140⟩
  · intro qSess hq
    unfold atLeastBits densePcgSpcotBound RatBound.scale RatBound.pow
    dsimp only
    have hm := Nat.mul_le_mul_right ((2 ^ 15 + 1) ^ 2 * 2 ^ 193) hq
    have hb : 2 ^ 32 * ((2 ^ 15 + 1) ^ 2 * 2 ^ 193) ≤ (2 ^ 128 - 2) ^ 2 := by decide
    have ha : qSess * (2 ^ 15 + 1) ^ 2 * 2 ^ 193 = qSess * ((2 ^ 15 + 1) ^ 2 * 2 ^ 193) := by
      simp only [Nat.mul_assoc]
    rw [ha]; exact Nat.le_trans hm hb

/-- Exact constructive modular-bias lemma (`dealerless.rs:87`):
    Reducing a uniform `M`-element draw (`M = 2^96 > 0`) modulo `q > 0` maps **at most
    `(M - 1) / q + 1`** inputs `u ∈ Fin M` to any fixed residue `r < q`. -/
theorem mod_residue_fiber_le_ceil_div {M q : Nat} (_hMPos : 0 < M) (_hqPos : 0 < q) (r : Nat) :
    qsum M (fun u => if u.1 % q = r then 1 else 0) ≤ (M - 1) / q + 1 := by
  let Q := (M - 1) / q + 1
  have hQuotLt : ∀ u : Fin M, u.1 / q < Q := by
    intro u
    have huLe : u.1 ≤ M - 1 := by omega
    have hDivLe : u.1 / q ≤ (M - 1) / q := Nat.div_le_div_right huLe
    omega
  have hDecomp : qsum M (fun u => if u.1 % q = r then 1 else 0) =
      qsum Q (fun k => qsum M (fun u => if u.1 % q = r ∧ u.1 / q = k.1 then 1 else 0)) := by
    rw [← qsum_comm]
    apply qsum_congr; intro u
    by_cases hmr : u.1 % q = r
    · simp only [hmr, true_and, ↓reduceIte]
      have hInd : qsum Q (fun k => if u.1 / q = k.1 then 1 else 0) =
          qsum Q (fun k => if k = ⟨u.1 / q, hQuotLt u⟩ then 1 else 0) := by
        apply qsum_congr; intro k
        by_cases hk : k = ⟨u.1 / q, hQuotLt u⟩
        · subst hk; simp
        · have hne : u.1 / q ≠ k.1 := fun heq => hk (Fin.ext heq.symm)
          simp [hk, hne]
      rw [hInd, qsum_eq_indicator]
    · simp only [hmr, false_and, ↓reduceIte]
      exact (qsum_const Q 0).symm
  rw [hDecomp]
  have hEachLe1 : ∀ k : Fin Q,
      qsum M (fun u => if u.1 % q = r ∧ u.1 / q = k.1 then 1 else 0) ≤ 1 := by
    intro k
    have hBool : qsum M (fun u => if u.1 % q = r ∧ u.1 / q = k.1 then 1 else 0) =
        qsum M (fun u => if decide (u.1 % q = r ∧ u.1 / q = k.1) = true then 1 else 0) := by
      apply qsum_congr; intro u
      by_cases h : u.1 % q = r ∧ u.1 / q = k.1 <;> simp [h]
    rw [hBool]
    apply qsum_le_one_of_subsingleton
    intro u₁ u₂ h₁ h₂
    rcases of_decide_eq_true h₁ with ⟨hr1, hq1⟩
    rcases of_decide_eq_true h₂ with ⟨hr2, hq2⟩
    apply Fin.ext
    have d1 := Nat.div_add_mod u₁.1 q
    have d2 := Nat.div_add_mod u₂.1 q
    rw [hq1, hr1] at d1
    rw [hq2, hr2] at d2
    exact d1.symm.trans d2
  have hSum := qsum_le_qsum hEachLe1
  rw [qsum_const, Nat.mul_one] at hSum
  exact hSum

/-- Exact 96-bit wide-reduction biased 7-repetition 14-lane `HdRekey` sacrifice bound
    (`14 * (((2^96 - 1) / 8380417 + 1) / 2^96)^7`), explicitly accounting for modular bias! -/
def hdRekeyBiasedSacrificeBound (qOnlineSessions : Nat) : RatBound :=
  RatBound.scale (14 * qOnlineSessions)
    (RatBound.pow ⟨(2 ^ 96 - 1) / 8380417 + 1, 2 ^ 96, Nat.two_pow_pos 96⟩ 7)

def hdRekeyComposedQuantumBound (b : QueryBudget) : RatBound :=
  RatBound.add (hdRekeyBiasedSacrificeBound b.qOnlineSessions)
               (quantumGroverSingleTargetBound 256 b.qHash)

/-- **`HdRekey` Biased 96-Bit Sacrifice (`> 157` Bits) & Composed `PQ128` Theorem**:
    Even accounting for exact 96-bit modular reduction bias modulo `q = 8380417`, a single rekey
    session achieves `strictlyMoreThanBits 157` across all 14 child + parent MAC lanes, and
    composed with 256-bit `cSHAKE256` commitment QROM binding achieves **`atLeastBits 128`** across
    `qOnlineSessions ≤ 2 ^ 20` and `qHash + 1 ≤ 2 ^ 61`! -/
theorem hd_rekey_biased_96bit_sacrifice_and_composed_pq128 (b : QueryBudget)
    (hqHash : b.qHash + 1 ≤ 2 ^ 61) (hqSess : b.qOnlineSessions ≤ 2 ^ 20) :
    strictlyMoreThanBits 157 (hdRekeyBiasedSacrificeBound 1) ∧
    atLeastBits 137 (hdRekeyBiasedSacrificeBound b.qOnlineSessions) ∧
    atLeastBits 128 (hdRekeyComposedQuantumBound b) := by
  have hSingle : strictlyMoreThanBits 157 (hdRekeyBiasedSacrificeBound 1) := by
    unfold strictlyMoreThanBits hdRekeyBiasedSacrificeBound RatBound.scale RatBound.pow
    decide
  have hSess137 : atLeastBits 137 (hdRekeyBiasedSacrificeBound b.qOnlineSessions) := by
    unfold atLeastBits hdRekeyBiasedSacrificeBound RatBound.scale RatBound.pow
    dsimp only
    have hm := Nat.mul_le_mul_left 14 hqSess
    have hm2 := Nat.mul_le_mul_right (((2 ^ 96 - 1) / 8380417 + 1) ^ 7 * 2 ^ 137) hm
    have hb : 14 * 2 ^ 20 * (((2 ^ 96 - 1) / 8380417 + 1) ^ 7 * 2 ^ 137) ≤ (2 ^ 96) ^ 7 := by
      decide
    have ha : 14 * b.qOnlineSessions * ((2 ^ 96 - 1) / 8380417 + 1) ^ 7 * 2 ^ 137 =
        14 * b.qOnlineSessions * (((2 ^ 96 - 1) / 8380417 + 1) ^ 7 * 2 ^ 137) := by
      simp only [Nat.mul_assoc]
    rw [ha]; exact Nat.le_trans hm2 hb
  have hQrom130 : atLeastBits 130 (quantumGroverSingleTargetBound 256 b.qHash) :=
    qrom_single_target_parametric_bits hqHash (by decide)
  exact ⟨hSingle, hSess137,
         atLeastBits_antitone_bits (by decide)
           (atLeastBits_add_union_loss (atLeastBits_antitone_bits (by decide) hSess137) hQrom130)⟩

/-- **`ActiveMigration` Pre-Quantum Shor Boundary vs Post-Migration `HybridPinnedEnvelope` Theorem**:
    Explicitly distinguishes the legacy elliptic-curve discrete-log witness (`Ed25519` / `secp256k1`,
    broken in polynomial quantum time by Shor's algorithm — hence `ActiveMigration` must execute
    *before* a cryptographically relevant quantum computer observes the legacy public key) from:
    1. Perfect `0 / 1` inside-MPC 3-of-3 XOR custodian key-share privacy on input faults,
    2. `Quantum128` (`438`-rep) ZKBoo ceremony soundness (`atLeastBits 128` under QROM), and
    3. Post-migration 256-bit `HybridPinnedEnvelope` custody target (`atLeastBits 129` QROM)! -/
def shorPolynomialQuantumBreak : RatBound := RatBound.one

theorem active_migration_shor_boundary_vs_post_migration_pq128 (b : QueryBudget)
    (hqHash : b.qHash + 1 ≤ 2 ^ 61) :
    ¬ atLeastBits 1 shorPolynomialQuantumBreak ∧
    atLeastBits 256 RatBound.zero ∧
    atLeastBits 129
      (quantumGroverGrindingBound b.qHash (zkbooSingleRepError.pow blindVcQuantum128Reps)) ∧
    atLeastBits 130 (quantumGroverSingleTargetBound 256 b.qHash) := by
  refine ⟨by unfold atLeastBits shorPolynomialQuantumBreak RatBound.one; decide,
          by unfold atLeastBits RatBound.zero; simp,
          blindvc_classical219_and_quantum438_soundness.2.2.1 b.qHash
            (Nat.le_trans hqHash (by decide)),
          qrom_single_target_parametric_bits hqHash (by decide)⟩


/-- **`#tooth` Single-Challenge `QuarticGoldilocks` QROM Folding Budget vs Constant-Success Work
    (`tooth_hem_ext4_single_challenge_qrom_folding_ceiling`)**:
    Explicitly separates fixed-query-budget advantage `Adv(qHash) ≤ 2⁻¹²⁸` from constant-success
    quantum attack cost for single-check `Ext4` folding (`2^80 / p^4 ≈ 2⁻¹⁷⁶`, without squaring
    unimplemented paired checks):
    1. For `qHash + 1 ≤ 2 ^ 21`, single-challenge `Ext4` folding achieves **`atLeastBits 130`**,
    2. Constant-success QROM round grinding (`Adv(qHash) ≤ 1/2`, `atLeastBits 1`) holds all the way
       up to `qHash + 1 ≤ 2 ^ 85` (`> 85` bits of quantum oracle work),
    3. At `qHash = 2 ^ 32`, `Adv(2^32)` exceeds `2⁻¹²⁸` (`exceedsBitBudget 128`) unless per-round
       PoW or verified paired independent challenges are bound into the folding step! -/
theorem tooth_hem_ext4_single_challenge_qrom_folding_ceiling :
    (∀ qHash : Nat, qHash + 1 ≤ 2 ^ 21 →
      atLeastBits 130
        (quantumGroverGrindingBound qHash ⟨2 ^ 80, goldilocksExt4Card, goldilocksExt4Card_pos⟩)) ∧
    (∀ qHash : Nat, qHash + 1 ≤ 2 ^ 85 →
      atLeastBits 1
        (quantumGroverGrindingBound qHash ⟨2 ^ 80, goldilocksExt4Card, goldilocksExt4Card_pos⟩)) ∧
    exceedsBitBudget 128
      (quantumGroverGrindingBound (2 ^ 32)
        ⟨2 ^ 80, goldilocksExt4Card, goldilocksExt4Card_pos⟩) := by
  refine ⟨?_, ?_,
          by unfold exceedsBitBudget quantumGroverGrindingBound RatBound.scale
               goldilocksExt4Card goldilocksPrime; decide⟩
  · intro qHash hq
    unfold atLeastBits quantumGroverGrindingBound RatBound.scale
    dsimp only
    have h8 : 8 * (qHash + 1) ^ 2 ≤ 2 ^ 45 := by
      have p1 : (qHash + 1) ^ 2 ≤ (2 ^ 21) ^ 2 := Nat.pow_le_pow_left hq 2
      have p2 : 8 * (2 ^ 21) ^ 2 = 2 ^ 45 := by decide
      rw [← p2]; exact Nat.mul_le_mul_left 8 p1
    have hm := Nat.mul_le_mul_right (2 ^ 80 * 2 ^ 130) h8
    have ha : 8 * (qHash + 1) ^ 2 * 2 ^ 80 * 2 ^ 130 =
        8 * (qHash + 1) ^ 2 * (2 ^ 80 * 2 ^ 130) := by simp only [Nat.mul_assoc]
    have hb : 2 ^ 45 * (2 ^ 80 * 2 ^ 130) ≤ goldilocksExt4Card := by
      unfold goldilocksExt4Card goldilocksPrime; decide
    rw [ha]; exact Nat.le_trans hm hb
  · intro qHash hq
    unfold atLeastBits quantumGroverGrindingBound RatBound.scale
    dsimp only
    have h8 : 8 * (qHash + 1) ^ 2 ≤ 2 ^ 173 := by
      have p1 : (qHash + 1) ^ 2 ≤ (2 ^ 85) ^ 2 := Nat.pow_le_pow_left hq 2
      have p2 : 8 * (2 ^ 85) ^ 2 = 2 ^ 173 := by decide
      rw [← p2]; exact Nat.mul_le_mul_left 8 p1
    have hm := Nat.mul_le_mul_right (2 ^ 80 * 2 ^ 1) h8
    have ha : 8 * (qHash + 1) ^ 2 * 2 ^ 80 * 2 ^ 1 =
        8 * (qHash + 1) ^ 2 * (2 ^ 80 * 2 ^ 1) := by simp only [Nat.mul_assoc]
    have hb : 2 ^ 173 * (2 ^ 80 * 2 ^ 1) ≤ goldilocksExt4Card := by
      unfold goldilocksExt4Card goldilocksPrime; decide
    rw [ha]; exact Nat.le_trans hm hb


/-! ### §4.2 `[CWYZ26]` Affine Combiner WHIR Upgrade & Dual-OOD List Pinning -/

/-- Constructive `LawfulField` instance for `QuarticGoldilocks` (`𝔽_{p^4}`), discharging
    every generic theorem in `Qsag.AffineProximityGaps` (`0` axioms, `0` classical choice). -/
instance : LawfulField QuarticGoldilocks where
  inv := QuarticGoldilocks.inv
  zero_ne_one := by decide
  mul_inv_cancel := QuarticGoldilocks.mul_inv_cancel

/-- Concrete `QuarticGoldilocks` specialization of `committed_polynomial_pair_bad_lines_le_choose2`
    (`[CWYZ26]` Claim 4.10 / Claim 4.13 Case (b)): for any candidate polynomial pair `(F_poly, G_poly)`,
    at most `|D|(|D| - 1)/2` challenge pairs `(α, β) ∈ S × S` produce `≥ 2` accidental agreements on `D`. -/
theorem goldilocksExt4_committed_pair_bad_lines_le_choose2
    (F_poly G_poly : List QuarticGoldilocks)
    (f g : QuarticGoldilocks → QuarticGoldilocks)
    (D S : List QuarticGoldilocks)
    (hD : D.Nodup) (hS : S.Nodup) :
    ((prodPool S).filter (fun p =>
      decide (2 ≤ (D.filter (isAccidentalAgreement F_poly G_poly f g p.1 p.2)).length))).length ≤
      D.length * (D.length - 1) / 2 :=
  committed_polynomial_pair_bad_lines_le_choose2 F_poly G_poly f g D S hD hS

/-- Concrete `QuarticGoldilocks` specialization of `welch_berlekamp_affine_proximity_gap`
    (`[CWYZ26]` Theorem 4.1 / Remark 4.16 at `m = 1, D = 1`): in the `2|D| + d + 1 < 3A` regime,
    at most `max(|S|, |D|(|D|-1)/2)` challenge pairs `(α, β) ∈ S × S` fail `s = 1` persistent
    agreement, collapsing scalar batching's `n/q` barrier to `1/q + n(n-1)/(2q^2)`! -/
theorem goldilocksExt4_welch_berlekamp_affine_proximity_gap
    (f g : QuarticGoldilocks → QuarticGoldilocks)
    (D S : List QuarticGoldilocks)
    (d A : Nat)
    (badPairs : List (QuarticGoldilocks × QuarticGoldilocks))
    (P_of : QuarticGoldilocks × QuarticGoldilocks → List QuarticGoldilocks)
    (hD : D.Nodup) (hS : S.Nodup)
    (hAD : A ≤ D.length) (hWB : 2 * D.length + d + 1 < 3 * A)
    (hBadNd : badPairs.Nodup)
    (hBadSub : ∀ p ∈ badPairs, p ∈ prodPool S)
    (hBadDeg : ∀ p ∈ badPairs, (P_of p).length ≤ d + 1)
    (hBadAgree : ∀ p ∈ badPairs, A ≤ (D.filter (fun z =>
      decide (RoundPoly.evalCoeffs (P_of p) z =
        CommRingOps.add (f z)
          (CommRingOps.mul (CommRingOps.add p.1 (CommRingOps.mul p.2 z)) (g z))))).length)
    (hBadExc : ∀ p ∈ badPairs, ¬ HasAffineWitnessS1 d f g D p.1 p.2 (P_of p)) :
    badPairs.length ≤ Nat.max S.length (D.length * (D.length - 1) / 2) :=
  welch_berlekamp_affine_proximity_gap f g D S d A badPairs P_of
    hD hS hAD hWB hBadNd hBadSub hBadDeg hBadAgree hBadExc

/-- `[CWYZ26]` Theorem 4.8 + Theorem 5.1 (`Eq. 5.7`) commit-phase equal-degree affine folding
    error bound `whirAffineStageSimpleNum w / p^4` across `w.sFolds` binary folds over
    `QuarticGoldilocks` (certified upper-bounding `whirAffineStageExactNumQ2 w (p^4) / (p^4)^2`
    whenever `checkWhirAffineWitness w (goldilocksPrime ^ 4) = true`). -/
def whirAffineEqualDegreeCommitFoldBound (w : WhirAffineWitness) : RatBound :=
  ⟨whirAffineStageSimpleNum w, goldilocksExt4Card, goldilocksExt4Card_pos⟩

/-- Exact pure `s_i`-loss proximity query bound for `[CWYZ26]` affine WHIR stage witness `w`
    (before per-stage PoW): the probability `(A + s_i)_{q_i} / (n)_{q_i}` that `q_i` DISTINCT
    uniformly sampled fibers all land in a set of `A + s_i` out of `n` fibers. -/
def whirAffinePureQueryBound (w : WhirAffineWitness) (hq : w.queries ≤ w.n) : RatBound :=
  ⟨affineFallingFactorial (w.A + w.sFolds) w.queries, affineFallingFactorial w.n w.queries,
   affineFallingFactorial_pos w.n w.queries hq⟩

/-- Total form of `whirAffinePureQueryBound`: the exact distinct-fiber bound
    `(A + s_i)_{q_i} / (n)_{q_i}` of the witness row, and `RatBound.one` (no soundness credit)
    for a row with `queries > n`. No proof-of-work density is credited: a prover choosing the
    grinding nonce searches the joint nonce/query oracle, which the compiler charges through the
    Fiat–Shamir search factor applied to this pure bound. -/
def whirAffinePureQueryBoundOrOne (w : WhirAffineWitness) : RatBound :=
  if hq : w.queries ≤ w.n then whirAffinePureQueryBound w hq else RatBound.one

/-- Every one of the 46 deployed `BciksJohnsonQrom128` rows (`num_vars ∈ 2..=24`) has pure query
    error strictly below `2^-256` at ITS OWN agreement threshold `A + s_i` and fiber count `n`.
    The bound `1/1` of the fallback branch fails the inequality, so each row is in the
    `queries ≤ n` branch. -/
theorem whirAffine_deployed_pure_query_bounds :
    ∀ nv : Nat, 2 ≤ nv → nv ≤ 24 → ∀ w ∈ whirAffineStageWitnesses nv true,
      strictlyMoreThanBits 256 (whirAffinePureQueryBoundOrOne w) := by
  have hAll : ((List.range 23).all (fun i =>
      (whirAffineStageWitnesses (i + 2) true).all (fun w =>
        decide (strictlyMoreThanBits 256 (whirAffinePureQueryBoundOrOne w))))) = true := by
    decide +kernel
  intro nv h2 h24 w hw
  have h := List.all_eq_true.mp hAll (nv - 2) (List.mem_range.mpr (by omega))
  have he : nv - 2 + 2 = nv := by omega
  rw [he] at h
  exact of_decide_eq_true (List.all_eq_true.mp h w hw)

/-- Dual-OOD list-pinning collision bound of a witness row: at most `D` polynomials of degree
    at most `d` lie in the agreement list (`guruswami_sudan_agreement_list_bound`), two distinct
    ones agree at a uniform point with probability at most `d / p^4`, and both OOD points are
    sampled independently: `D^2 * (d / p^4)^2`. -/
def whirAffineDualOodListPinBound (w : WhirAffineWitness) : RatBound :=
  ⟨(w.D * w.d) ^ 2, goldilocksExt4Card ^ 2, Nat.pow_pos goldilocksExt4Card_pos⟩

/-- Interactive error terms of `Hem` at `num_vars = 20`, over EVERY deployed stage: the `Ext4`
    point-reduction sumcheck, then for each of the three stage rows of
    `whirAffineStageWitnesses 20 true` its fold bound, its dual-OOD bound and its pure query
    bound. Commitment extraction is charged separately (`qromMerkleOnlineExtractBound`). -/
def hemNv20ComposedPureTerms : List RatBound :=
  ⟨72, goldilocksExt4Card, goldilocksExt4Card_pos⟩ ::
    ((whirAffineStageWitnesses 20 true).map whirAffineEqualDegreeCommitFoldBound ++
     (whirAffineStageWitnesses 20 true).map whirAffineDualOodListPinBound ++
     (whirAffineStageWitnesses 20 true).map whirAffinePureQueryBoundOrOne)

/-- One sumcheck term and three terms for each of the three stages. -/
theorem hemNv20ComposedPureTerms_length : hemNv20ComposedPureTerms.length = 10 := by
  decide +kernel

/-- A term list scaled by a search factor is monotone in that factor. -/
private theorem sumList_map_scale_mono {a b : Nat} (hab : a ≤ b) :
    ∀ rs : List RatBound,
      RatBound.le (RatBound.sumList (rs.map (RatBound.scale a)))
        (RatBound.sumList (rs.map (RatBound.scale b)))
  | [] => RatBound.le_refl _
  | r :: rs => by
    show RatBound.le
      ((RatBound.scale a r).add (RatBound.sumList (rs.map (RatBound.scale a))))
      ((RatBound.scale b r).add (RatBound.sumList (rs.map (RatBound.scale b))))
    refine RatBound.add_le_add ?_ (sumList_map_scale_mono hab rs)
    unfold RatBound.le RatBound.scale
    dsimp only
    exact Nat.mul_le_mul_right r.den (Nat.mul_le_mul_right r.num hab)

/-- Dual-OOD (`m_OOD = 2`) list-pinning collision bound `L_i^2 * (|D_i| / p^4)^2` over
    `QuarticGoldilocks`, replacing single-OOD `L_i^2 * |D_i| / p^4` (`≈ 2⁻²¹¹`) with `> 441` bits
    of collision resistance so list-pinning never bottlenecks QROM grinding at `qHash ≤ 2^56`. -/
def whirDualOodListPinBound (st : WhirStageBudget) (etaScale : Nat) : RatBound :=
  ⟨(whirJohnsonListSize st etaScale) ^ 2 * (2 ^ st.domainLog2) ^ 2,
   goldilocksExt4Card ^ 2,
   Nat.pow_pos goldilocksExt4Card_pos⟩

/-- Soundness extractor turning a validated `WhirAffineWitness` (`checkWhirAffineWitness = true`,
    `whirAffineStageSimpleNum < 1900`) into exact rational and QROM bit-security bounds. -/
theorem whirAffineWitness_sound_of_valid (w : WhirAffineWitness)
    (hok : checkWhirAffineWitness w (goldilocksPrime ^ 4) = true)
    (hSimple : whirAffineStageSimpleNum w < 1900) :
    ∃ hq : w.queries ≤ w.n,
      whirAffineStageExactNumQ2 w goldilocksExt4Card ≤
        whirAffineStageSimpleNum w * goldilocksExt4Card ∧
      atLeastBits 244 (whirAffineEqualDegreeCommitFoldBound w) ∧
      strictlyMoreThanBits w.queryTargetBits (whirAffinePureQueryBound w hq) ∧
      (∀ qHash : Nat, qHash + 1 ≤ 2 ^ 56 →
        atLeastBits 130
          (quantumGroverGrindingBound qHash (whirAffineEqualDegreeCommitFoldBound w))) := by
  have hCardEq : goldilocksExt4Card = goldilocksPrime ^ 4 := rfl
  have hExact := whirAffineStageExactNumQ2_le_simple_mul_q w (goldilocksPrime ^ 4) hok
  rw [← hCardEq] at hExact
  unfold checkWhirAffineWitness at hok
  have hProps := of_decide_eq_true hok
  rcases hProps with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hqn, hQuery⟩
  refine ⟨hqn, hExact, ?_, hQuery, ?_⟩
  · unfold atLeastBits whirAffineEqualDegreeCommitFoldBound
    dsimp only
    have h1 : whirAffineStageSimpleNum w * 2 ^ 244 ≤ 1900 * 2 ^ 244 :=
      Nat.mul_le_mul_right _ (Nat.le_of_lt hSimple)
    have h2 : 1900 * 2 ^ 244 ≤ goldilocksExt4Card := by
      unfold goldilocksExt4Card goldilocksPrime; decide
    exact Nat.le_trans h1 h2
  · intro qHash hq
    unfold atLeastBits quantumGroverGrindingBound whirAffineEqualDegreeCommitFoldBound RatBound.scale
    dsimp only
    have h8 : 8 * (qHash + 1) ^ 2 ≤ 2 ^ 115 := by
      have p1 : (qHash + 1) ^ 2 ≤ (2 ^ 56) ^ 2 := Nat.pow_le_pow_left hq 2
      have p2 : 8 * (2 ^ 56) ^ 2 = 2 ^ 115 := by decide
      rw [← p2]; exact Nat.mul_le_mul_left 8 p1
    have hm1 := Nat.mul_le_mul_right (whirAffineStageSimpleNum w * 2 ^ 130) h8
    have hm2 : 2 ^ 115 * (whirAffineStageSimpleNum w * 2 ^ 130) ≤ 2 ^ 115 * (1900 * 2 ^ 130) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.le_of_lt hSimple))
    have ha : 8 * (qHash + 1) ^ 2 * whirAffineStageSimpleNum w * 2 ^ 130 =
        8 * (qHash + 1) ^ 2 * (whirAffineStageSimpleNum w * 2 ^ 130) := by
      simp only [Nat.mul_assoc]
    have hb : 2 ^ 115 * (1900 * 2 ^ 130) ≤ goldilocksExt4Card := by
      unfold goldilocksExt4Card goldilocksPrime; decide
    rw [ha]
    exact Nat.le_trans hm1 (Nat.le_trans hm2 hb)

/-- **`[CWYZ26]` All-Stage `nv = 20` & `nv = 24` Affine WHIR + Dual-OOD Soundness Theorem
    (`cwyz26_affine_whir_nv20_and_nv24_stage_soundness`)**:
    1. Every stage witness across `nv = 20` (`3` stages) and `nv = 24` (`4` stages) for both
       `BciksJohnsonClassical128` (`129, 65, 44, 33`) and `BciksJohnsonQrom128` (`258, 130, 88, 66`)
       satisfies `whirAffineStageExactNumQ2 ≤ whirAffineStageSimpleNum * p^4`, achieves
       **`atLeastBits 244`** commit-folding soundness (replacing `[BCIKS20]`'s `132–175` bits!),
       achieves **`strictlyMoreThanBits queryTargetBits`** (`> 128` classical / `> 256` QROM) exact
       distinct-fiber `s_i`-loss query soundness BEFORE PoW, and survives QROM Grover grinding at **`atLeastBits 130`**
       for ALL `qHash + 1 ≤ 2 ^ 56`!
    2. Dual-OOD (`m_OOD = 2`) list pinning achieves **`strictlyMoreThanBits 441`** across all 4
       `bciksJohnsonQrom128` stages! -/
theorem cwyz26_affine_whir_nv20_and_nv24_stage_soundness :
    (∀ w ∈ whirAffineStageWitnesses 20 false ++ whirAffineStageWitnesses 20 true ++
           whirAffineStageWitnesses 24 false ++ whirAffineStageWitnesses 24 true,
      ∃ hq : w.queries ≤ w.n,
        whirAffineStageExactNumQ2 w goldilocksExt4Card ≤
          whirAffineStageSimpleNum w * goldilocksExt4Card ∧
        atLeastBits 244 (whirAffineEqualDegreeCommitFoldBound w) ∧
        strictlyMoreThanBits w.queryTargetBits (whirAffinePureQueryBound w hq) ∧
        (∀ qHash : Nat, qHash + 1 ≤ 2 ^ 56 →
          atLeastBits 130
            (quantumGroverGrindingBound qHash (whirAffineEqualDegreeCommitFoldBound w)))) ∧
    (∀ st ∈ whirSchedule4Stage .bciksJohnsonQrom128,
      strictlyMoreThanBits 441 (whirDualOodListPinBound st 256)) := by
  rcases cwyz26_whir_nv20_and_nv24_all_stages_valid with ⟨h20c, h20q, h24c, h24q⟩
  refine ⟨?_, ?_⟩
  · intro w hw
    simp only [List.mem_append] at hw
    rcases hw with ((hw | hw) | hw) | hw
    · rcases h20c w hw with ⟨hok, hlt⟩; exact whirAffineWitness_sound_of_valid w hok hlt
    · rcases h20q w hw with ⟨hok, hlt⟩; exact whirAffineWitness_sound_of_valid w hok hlt
    · rcases h24c w hw with ⟨hok, hlt⟩; exact whirAffineWitness_sound_of_valid w hok hlt
    · rcases h24q w hw with ⟨hok, hlt⟩; exact whirAffineWitness_sound_of_valid w hok hlt
  · intro st hMem
    simp only [whirSchedule4Stage, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl <;>
      (unfold strictlyMoreThanBits whirDualOodListPinBound whirJohnsonListSize
         goldilocksExt4Card goldilocksPrime; decide)


/-! ## §6. Master Composed `PQ128` Portfolio Theorem & Non-Vacuity Inhabitedness Witness -/

/-- Enumeration of all 12 certified `PQ128` post-quantum profiles across the QSAG suite. -/
inductive QsagPq128ProfileId where
  | baggySha3V128
  | baggyPoseidon2V128
  | corduroyCustodyV128
  | jortsAndQuorumJortsV128
  | frontierSumFtsFull256
  | hemExt4WhirPq128
  | blindVcQuantum438
  | thresholdMlDsaDkgAndSign
  | poseidon2Toprf2of5
  | densePcg256BitSeedSpcot
  | hdRekeyBiased96
  | activeMigrationPostCeremony
  deriving DecidableEq, Repr

/-- Machine-checked classical and quantum error-bound entry for a portfolio profile, with the
    offline hash-query ceiling up to which the entry is claimed at 128 bits. -/
structure QsagPq128ProfileEntry where
  profileId : QsagPq128ProfileId
  classicalBound : RatBound
  quantumBound : RatBound
  /-- `k` such that the 128-bit claim for this entry is made for `qHash + 1 ≤ 2^k`. -/
  pq128HashQueryCeilingLog2 : Nat := 56
  /-- The FIPS 204 parameter set whose challenge space the entry's Fiat–Shamir term uses. -/
  fips204ParamSet : Option MlDsaParamSet := none
  deriving DecidableEq, Repr

/-- Threshold ML-DSA DKG and signing for parameter set `p`: offline challenge grinding over
    `qHash` (`mlDsaOfflineChallenge*Bound`), one online challenge guess per session, and search
    against the 256-bit DKG commitment. The entry records `p` and its query ceiling; for
    ML-DSA-44 (FIPS 204 Category 2) that ceiling is `2^30`, not the portfolio's `2^56`. -/
def thresholdMlDsaDkgAndSignEntry (p : MlDsaParamSet) (b : QueryBudget) : QsagPq128ProfileEntry :=
  { profileId := .thresholdMlDsaDkgAndSign
    classicalBound := RatBound.add
      (mlDsaOfflineChallengeClassicalBound p b.qHash)
      (RatBound.add
        ⟨b.qOnlineSessions + 1, mlDsaChallengeCard p, mlDsaChallengeCard_pos p⟩
        ⟨b.qHash + 1, 2 ^ 256, Nat.two_pow_pos 256⟩)
    quantumBound := RatBound.add
      (mlDsaOfflineChallengeQuantumBound p b.qHash)
      (RatBound.add
        ⟨b.qOnlineSessions + 1, mlDsaChallengeCard p, mlDsaChallengeCard_pos p⟩
        (quantumGroverSingleTargetBound 256 b.qHash))
    pq128HashQueryCeilingLog2 := p.pq128HashQueryCeilingLog2
    fips204ParamSet := some p }

private theorem ratBound_le_of_num_le {a a' d : Nat} (hd : 0 < d) (h : a ≤ a') :
    RatBound.le ⟨a, d, hd⟩ ⟨a', d, hd⟩ :=
  Nat.mul_le_mul_right d h

/-- The threshold ML-DSA entry is monotone in the hash-query and session budgets. -/
theorem thresholdMlDsaDkgAndSignEntry_mono (p : MlDsaParamSet) {b b' : QueryBudget}
    (hq : b.qHash ≤ b'.qHash) (hs : b.qOnlineSessions ≤ b'.qOnlineSessions) :
    RatBound.le (thresholdMlDsaDkgAndSignEntry p b).classicalBound
        (thresholdMlDsaDkgAndSignEntry p b').classicalBound ∧
    RatBound.le (thresholdMlDsaDkgAndSignEntry p b).quantumBound
        (thresholdMlDsaDkgAndSignEntry p b').quantumBound := by
  have hq1 : b.qHash + 1 ≤ b'.qHash + 1 := Nat.succ_le_succ hq
  have hs1 : b.qOnlineSessions + 1 ≤ b'.qOnlineSessions + 1 := Nat.succ_le_succ hs
  have hsq : (b.qHash + 1) ^ 2 ≤ (b'.qHash + 1) ^ 2 := Nat.pow_le_pow_left hq1 2
  exact ⟨RatBound.add_le_add (ratBound_le_of_num_le _ hq1)
           (RatBound.add_le_add (ratBound_le_of_num_le _ hs1) (ratBound_le_of_num_le _ hq1)),
         RatBound.add_le_add (ratBound_le_of_num_le _ (Nat.mul_le_mul_left 8 hsq))
           (RatBound.add_le_add (ratBound_le_of_num_le _ hs1)
             (ratBound_le_of_num_le _ (Nat.mul_le_mul_left (8 * 1) hsq)))⟩

/-- **Threshold ML-DSA entry inside its ceiling.** For `qHash + 1 ≤ 2^k` with `k` the parameter
    set's ceiling (`30 / 47 / 62` for ML-DSA-44 / 65 / 87) and at most `2^20` online sessions, the
    entry keeps 128 bits classically and in the QROM. -/
theorem threshold_mldsa_entry_pq128_within_ceiling (p : MlDsaParamSet) (b : QueryBudget)
    (hqHash : b.qHash + 1 ≤ 2 ^ p.pq128HashQueryCeilingLog2)
    (hqSess : b.qOnlineSessions + 1 ≤ 2 ^ 20) :
    atLeastBits 128 (thresholdMlDsaDkgAndSignEntry p b).classicalBound ∧
    atLeastBits 128 (thresholdMlDsaDkgAndSignEntry p b).quantumBound := by
  have key : ∀ b' : QueryBudget, b.qHash ≤ b'.qHash → b.qOnlineSessions ≤ b'.qOnlineSessions →
      atLeastBits 128 (thresholdMlDsaDkgAndSignEntry p b').classicalBound →
      atLeastBits 128 (thresholdMlDsaDkgAndSignEntry p b').quantumBound →
      atLeastBits 128 (thresholdMlDsaDkgAndSignEntry p b).classicalBound ∧
      atLeastBits 128 (thresholdMlDsaDkgAndSignEntry p b).quantumBound :=
    fun _ h1 h2 hc hQ =>
      ⟨atLeastBits_of_le (thresholdMlDsaDkgAndSignEntry_mono p h1 h2).1 hc,
       atLeastBits_of_le (thresholdMlDsaDkgAndSignEntry_mono p h1 h2).2 hQ⟩
  have hs' : b.qOnlineSessions ≤ 2 ^ 20 - 1 := by omega
  cases p
  · have hq' : b.qHash + 1 ≤ 2 ^ 30 := hqHash
    exact key ⟨2 ^ 30 - 1, 0, 2 ^ 20 - 1⟩ (by show b.qHash ≤ 2 ^ 30 - 1; omega) hs'
      (by decide +kernel) (by decide +kernel)
  · have hq' : b.qHash + 1 ≤ 2 ^ 47 := hqHash
    exact key ⟨2 ^ 47 - 1, 0, 2 ^ 20 - 1⟩ (by show b.qHash ≤ 2 ^ 47 - 1; omega) hs'
      (by decide +kernel) (by decide +kernel)
  · have hq' : b.qHash + 1 ≤ 2 ^ 62 := hqHash
    exact key ⟨2 ^ 62 - 1, 0, 2 ^ 20 - 1⟩ (by show b.qHash ≤ 2 ^ 62 - 1; omega) hs'
      (by decide +kernel) (by decide +kernel)

/-- One power of two above its ceiling every parameter set's entry is below 128 QROM bits, even
    with no online session. -/
theorem tooth_threshold_mldsa_entry_above_ceiling_not_pq128 (p : MlDsaParamSet) :
    ¬ atLeastBits 128
        (thresholdMlDsaDkgAndSignEntry p
          ⟨2 ^ (p.pq128HashQueryCeilingLog2 + 1) - 1, 0, 0⟩).quantumBound := by
  cases p <;> decide +kernel

/-- The threshold entry at the portfolio's `2^56` offline queries and `2^20` sessions, per
    parameter set: 77 bits for the deployed ML-DSA-44 (Category 2), 110 for ML-DSA-65, 140 for
    ML-DSA-87 (there the 256-bit commitment search is the binding term). Each figure is exact. -/
theorem threshold_mldsa_entry_bits_at_2pow56 :
    let b : QueryBudget := ⟨2 ^ 56 - 1, 0, 2 ^ 20 - 1⟩
    (atLeastBits 77 (thresholdMlDsaDkgAndSignEntry .mldsa44 b).quantumBound ∧
      ¬ atLeastBits 78 (thresholdMlDsaDkgAndSignEntry .mldsa44 b).quantumBound) ∧
    (atLeastBits 110 (thresholdMlDsaDkgAndSignEntry .mldsa65 b).quantumBound ∧
      ¬ atLeastBits 111 (thresholdMlDsaDkgAndSignEntry .mldsa65 b).quantumBound) ∧
    (atLeastBits 140 (thresholdMlDsaDkgAndSignEntry .mldsa87 b).quantumBound ∧
      ¬ atLeastBits 141 (thresholdMlDsaDkgAndSignEntry .mldsa87 b).quantumBound) := by
  decide +kernel

/-- The deployed Category-2 entry does not reach 128 QROM bits at the portfolio's `2^56`. -/
theorem tooth_threshold_mldsa44_entry_not_pq128_at_2pow56 :
    ¬ atLeastBits 128
        (thresholdMlDsaDkgAndSignEntry deployedThresholdMlDsaParamSet
          ⟨2 ^ 56 - 1, 0, 2 ^ 20 - 1⟩).quantumBound := by
  decide +kernel

theorem witness_threshold_mldsa_budget :
    ∃ b : QueryBudget,
      b.qHash + 1 ≤ 2 ^ deployedThresholdMlDsaParamSet.pq128HashQueryCeilingLog2 ∧
      b.qOnlineSessions + 1 ≤ 2 ^ 20 :=
  ⟨⟨2 ^ 30 - 1, 2 ^ 16, 2 ^ 20 - 1⟩, by decide, by decide⟩

/-- The 12-profile portfolio roster. Each entry carries the offline hash-query ceiling of its
    128-bit claim (`pq128HashQueryCeilingLog2`): `2^56` for eleven entries and `2^30` for
    `.thresholdMlDsaDkgAndSign`, which is built on the deployed ML-DSA-44 challenge space
    (FIPS 204 Category 2, `fips204ParamSet = some .mldsa44`). The `.densePcg256BitSeedSpcot`
    entry charges the complete depth-15 V3 forest under the per-node tweak
    (`densePcgV3Salted*Bound`).
    `.hemExt4WhirPq128` is the Fiat–Shamir-ground IOP-layer budget of `Hem` at `num_vars = 20`
    over ALL three deployed stages: every term of `hemNv20ComposedPureTerms` (sumcheck, and per
    stage the `[CWYZ26]` fold bound, the dual-OOD bound and the pure distinct-fiber query bound
    of that stage's witness row) scaled by the classical search factor `qHash + 1`
    (`classicalFiatShamirBound`) or the Grover search factor `8 (qHash + 1)^2`
    (`quantumGroverGrindingBound`). No proof-of-work density is credited. The entry does not
    depend on `qOnlineSessions` (the argument is non-interactive) and does NOT include Merkle
    commitment extraction or the row-constraint (AIR) reduction: commitment extraction is charged
    in `Qsag.multiRoundFsQromCompilerBound`, whose collision term limits the composed QROM bound
    to `Q + 1 ≤ 2^40`. -/
def qsagPq128PortfolioRoster (b : QueryBudget) : List QsagPq128ProfileEntry :=
  [ { profileId := .baggySha3V128
      classicalBound := ⟨b.qHash + 1, 2 ^ 256, Nat.two_pow_pos 256⟩
      quantumBound := quantumGroverSingleTargetBound 256 b.qHash },
    { profileId := .baggyPoseidon2V128
      classicalBound := ⟨b.qHash + 1, 2 ^ 256, Nat.two_pow_pos 256⟩
      quantumBound := quantumGroverSingleTargetBound 256 b.qHash },
    { profileId := .corduroyCustodyV128
      classicalBound := ⟨b.qHash + 1, 2 ^ 256, Nat.two_pow_pos 256⟩
      quantumBound := quantumGroverSingleTargetBound 256 b.qHash },
    { profileId := .jortsAndQuorumJortsV128
      classicalBound := jortsComposedClassicalBound b
      quantumBound := jortsComposedQuantumBound b },
    { profileId := .frontierSumFtsFull256
      classicalBound := ⟨b.qHash + 1, 2 ^ 256, Nat.two_pow_pos 256⟩
      quantumBound := quantumGroverSingleTargetBound 256 b.qHash },
    { profileId := .hemExt4WhirPq128
      classicalBound :=
        RatBound.sumList (hemNv20ComposedPureTerms.map (RatBound.scale (b.qHash + 1)))
      quantumBound :=
        RatBound.sumList
          (hemNv20ComposedPureTerms.map (RatBound.scale (8 * (b.qHash + 1) ^ 2))) },
    { profileId := .blindVcQuantum438
      classicalBound :=
        RatBound.add
          (classicalFiatShamirBound b.qHash (zkbooSingleRepError.pow blindVcQuantum128Reps))
          ⟨b.qHash + 1, goldilocksExt4Card, goldilocksExt4Card_pos⟩
      quantumBound :=
        RatBound.add
          (quantumGroverGrindingBound b.qHash (zkbooSingleRepError.pow blindVcQuantum128Reps))
          (toprfDigest4QromBound b.qHash) },
    thresholdMlDsaDkgAndSignEntry deployedThresholdMlDsaParamSet b,
    { profileId := .poseidon2Toprf2of5
      classicalBound := ⟨b.qHash + 1, goldilocksExt4Card, goldilocksExt4Card_pos⟩
      quantumBound := toprfDigest4QromBound b.qHash },
    { profileId := .densePcg256BitSeedSpcot
      classicalBound :=
        RatBound.add
          (densePcgSpcotBound 15 (b.qOnlineSessions + 1))
          (densePcgV3SaltedSeedClassicalBound b.qHash)
      quantumBound :=
        RatBound.add
          (densePcgSpcotBound 15 (b.qOnlineSessions + 1))
          (densePcgV3SaltedSeedQuantumBound b.qHash) },
    { profileId := .hdRekeyBiased96
      classicalBound :=
        RatBound.add (hdRekeyBiasedSacrificeBound (b.qOnlineSessions + 1))
                     ⟨b.qHash + 1, 2 ^ 256, Nat.two_pow_pos 256⟩
      quantumBound :=
        RatBound.add (hdRekeyBiasedSacrificeBound (b.qOnlineSessions + 1))
                     (quantumGroverSingleTargetBound 256 b.qHash) },
    { profileId := .activeMigrationPostCeremony
      classicalBound :=
        RatBound.add
          (classicalFiatShamirBound b.qHash (zkbooSingleRepError.pow blindVcQuantum128Reps))
          ⟨b.qHash + 1, 2 ^ 256, Nat.two_pow_pos 256⟩
      quantumBound :=
        RatBound.add
          (quantumGroverGrindingBound b.qHash (zkbooSingleRepError.pow blindVcQuantum128Reps))
          (quantumGroverSingleTargetBound 256 b.qHash) } ]

/-- High-Query (`qHash + 1 ≤ 2 ^ 56`) Portfolio Theorem across the 10 profiles that are neither
    the folding entry (single-check `Ext4` folding is governed by
    `tooth_hem_ext4_single_challenge_qrom_folding_ceiling`) nor the Category-2 threshold ML-DSA
    entry, which at `2^56` offline queries has 77 QROM bits
    (`threshold_mldsa_entry_bits_at_2pow56`) and is covered up to `2^30` by
    `threshold_mldsa_entry_pq128_within_ceiling`. -/
theorem qsag_pq128_high_query_2pow56_non_folding_budget (b : QueryBudget)
    (hqHash : b.qHash + 1 ≤ 2 ^ 56) (hqSess : b.qOnlineSessions + 1 ≤ 2 ^ 20) :
    ∀ entry ∈ qsagPq128PortfolioRoster b,
      entry.profileId ≠ .hemExt4WhirPq128 →
      entry.profileId ≠ .thresholdMlDsaDkgAndSign →
      atLeastBits 128 entry.classicalBound ∧ atLeastBits 128 entry.quantumBound := by
  have hq61 : b.qHash + 1 ≤ 2 ^ 61 := Nat.le_trans hqHash (by decide)
  have hq62 : b.qHash + 1 ≤ 2 ^ 62 := Nat.le_trans hqHash (by decide)
  have hqSessPlain : b.qOnlineSessions ≤ 2 ^ 20 := by omega
  have h8Sq : 8 * (b.qHash + 1) ^ 2 ≤ 2 ^ 115 := by
    have p1 : (b.qHash + 1) ^ 2 ≤ (2 ^ 56) ^ 2 := Nat.pow_le_pow_left hqHash 2
    have p2 : 8 * (2 ^ 56) ^ 2 = 2 ^ 115 := by decide
    rw [← p2]; exact Nat.mul_le_mul_left 8 p1
  have hClass256 : atLeastBits 130 ⟨b.qHash + 1, 2 ^ 256, Nat.two_pow_pos 256⟩ := by
    unfold atLeastBits; dsimp only
    have hm := Nat.mul_le_mul_right (2 ^ 130) hqHash
    have hb : 2 ^ 56 * 2 ^ 130 ≤ 2 ^ 256 := by decide
    exact Nat.le_trans hm hb
  have hQrom256 : atLeastBits 130 (quantumGroverSingleTargetBound 256 b.qHash) :=
    qrom_single_target_parametric_bits hq61 (by decide)
  have hClassExt4 : atLeastBits 130 ⟨b.qHash + 1, goldilocksExt4Card, goldilocksExt4Card_pos⟩ := by
    unfold atLeastBits; dsimp only
    have hm := Nat.mul_le_mul_right (2 ^ 130) hqHash
    have hb : 2 ^ 56 * 2 ^ 130 ≤ goldilocksExt4Card := by
      unfold goldilocksExt4Card goldilocksPrime; decide
    exact Nat.le_trans hm hb
  have hQromExt4 : atLeastBits 130 (toprfDigest4QromBound b.qHash) := by
    unfold atLeastBits toprfDigest4QromBound; dsimp only
    have hm := Nat.mul_le_mul_right (2 ^ 130) h8Sq
    have hb : 2 ^ 115 * 2 ^ 130 ≤ goldilocksExt4Card := by
      unfold goldilocksExt4Card goldilocksPrime; decide
    exact Nat.le_trans hm hb
  have hClassZkb438 :
      atLeastBits 129
        (classicalFiatShamirBound b.qHash (zkbooSingleRepError.pow blindVcQuantum128Reps)) := by
    unfold atLeastBits classicalFiatShamirBound RatBound.scale RatBound.pow
      zkbooSingleRepError blindVcQuantum128Reps
    dsimp only
    have hm := Nat.mul_le_mul_right (2 ^ 438 * 2 ^ 129) hqHash
    have ha : (b.qHash + 1) * 2 ^ 438 * 2 ^ 129 = (b.qHash + 1) * (2 ^ 438 * 2 ^ 129) := by
      simp only [Nat.mul_assoc]
    have hb : 2 ^ 56 * (2 ^ 438 * 2 ^ 129) ≤ 2 ^ 438 * 2 ^ 256 := by
      have p : 2 ^ 56 * (2 ^ 438 * 2 ^ 129) = 2 ^ 438 * 2 ^ 185 := by
        rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ 56) (2 ^ 438), Nat.mul_assoc, ← Nat.pow_add]
      rw [p]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by decide))
    rw [ha]
    exact Nat.le_trans hm (Nat.le_trans hb (Nat.le_of_lt zkboo_438_gt_two_pow_256_margin))
  have hQromZkb438 :
      atLeastBits 129
        (quantumGroverGrindingBound b.qHash (zkbooSingleRepError.pow blindVcQuantum128Reps)) :=
    blindvc_classical219_and_quantum438_soundness.2.2.1 b.qHash hq62
  have hJorts := jorts_and_quorum_jorts_composed_pq128_soundness b hq61 hqSessPlain
  have hHdPlus1 := hd_rekey_biased_96bit_sacrifice_and_composed_pq128
    ⟨b.qHash, b.qSign, b.qOnlineSessions + 1⟩ hq61 hqSess
  intro entry hMem hNe hNeMl
  simp only [qsagPq128PortfolioRoster, List.mem_cons, List.not_mem_nil, or_false] at hMem
  rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨atLeastBits_antitone_bits (by decide) hClass256,
           atLeastBits_antitone_bits (by decide) hQrom256⟩
  · exact ⟨atLeastBits_antitone_bits (by decide) hClass256,
           atLeastBits_antitone_bits (by decide) hQrom256⟩
  · exact ⟨atLeastBits_antitone_bits (by decide) hClass256,
           atLeastBits_antitone_bits (by decide) hQrom256⟩
  · exact ⟨hJorts.2.2.2.1, hJorts.2.2.2.2⟩
  · exact ⟨atLeastBits_antitone_bits (by decide) hClass256,
           atLeastBits_antitone_bits (by decide) hQrom256⟩
  · exact absurd rfl hNe
  · exact ⟨atLeastBits_add_union_loss hClassZkb438 (atLeastBits_antitone_bits (by decide) hClassExt4),
           atLeastBits_add_union_loss hQromZkb438 (atLeastBits_antitone_bits (by decide) hQromExt4)⟩
  · exact absurd rfl hNeMl
  · exact ⟨atLeastBits_antitone_bits (by decide) hClassExt4,
           atLeastBits_antitone_bits (by decide) hQromExt4⟩
  · have hSpcot : atLeastBits 129 (densePcgSpcotBound 15 (b.qOnlineSessions + 1)) := by
      unfold atLeastBits densePcgSpcotBound RatBound.scale RatBound.pow; dsimp only
      have hm := Nat.mul_le_mul_right ((2 ^ 15 + 1) ^ 2 * 2 ^ 129) hqSess
      have ha : (b.qOnlineSessions + 1) * (2 ^ 15 + 1) ^ 2 * 2 ^ 129 =
          (b.qOnlineSessions + 1) * ((2 ^ 15 + 1) ^ 2 * 2 ^ 129) := by simp only [Nat.mul_assoc]
      have hb : 2 ^ 20 * ((2 ^ 15 + 1) ^ 2 * 2 ^ 129) ≤ (2 ^ 128 - 2) ^ 2 := by decide
      rw [ha]; exact Nat.le_trans hm hb
    have hSeedClass : atLeastBits 129 (densePcgV3SaltedSeedClassicalBound b.qHash) := by
      unfold atLeastBits densePcgV3SaltedSeedClassicalBound tweakedClassicalMultiTargetBound
      dsimp only
      exact Nat.le_trans
        (Nat.mul_le_mul_right (2 ^ 129)
          (Nat.add_le_add_right (Nat.le_of_succ_le hqHash) densePcgV3NodeTargets))
        (by decide)
    have hSeedQrom : atLeastBits 129 (densePcgV3SaltedSeedQuantumBound b.qHash) :=
      atLeastBits_antitone_bits (by decide) (densePcgV3SaltedSeedQuantumBound_140 b.qHash hqHash)
    exact ⟨atLeastBits_add_union_loss hSpcot hSeedClass,
           atLeastBits_add_union_loss hSpcot hSeedQrom⟩
  · exact ⟨atLeastBits_add_union_loss
              (atLeastBits_antitone_bits (by decide) hHdPlus1.2.1)
              (atLeastBits_antitone_bits (by decide) hClass256),
           hHdPlus1.2.2⟩
  · exact ⟨atLeastBits_add_union_loss hClassZkb438 (atLeastBits_antitone_bits (by decide) hClass256),
           atLeastBits_add_union_loss hQromZkb438 (atLeastBits_antitone_bits (by decide) hQrom256)⟩

private theorem roster_ceiling_of_not_mldsa (b : QueryBudget) :
    ∀ entry ∈ qsagPq128PortfolioRoster b,
      entry.profileId ≠ .thresholdMlDsaDkgAndSign → entry.pq128HashQueryCeilingLog2 = 56 := by
  intro entry hMem hNe
  simp only [qsagPq128PortfolioRoster, List.mem_cons, List.not_mem_nil, or_false] at hMem
  rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | rfl | exact absurd rfl hNe

private theorem roster_ceiling_ge_30 (b : QueryBudget) :
    ∀ entry ∈ qsagPq128PortfolioRoster b, 30 ≤ entry.pq128HashQueryCeilingLog2 := by
  intro entry hMem
  simp only [qsagPq128PortfolioRoster, List.mem_cons, List.not_mem_nil, or_false] at hMem
  rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact (by decide : 30 ≤ 56) | exact Nat.le_refl 30

/-- The roster's threshold ML-DSA entry is the deployed ML-DSA-44 one: FIPS 204 Category 2, with
    a `2^30` offline hash-query ceiling for its 128-bit claim. -/
theorem roster_threshold_mldsa_entry_is_category2 (b : QueryBudget) :
    ∃ entry ∈ qsagPq128PortfolioRoster b,
      entry.profileId = .thresholdMlDsaDkgAndSign ∧
      entry.fips204ParamSet = some .mldsa44 ∧
      entry.fips204ParamSet.map MlDsaParamSet.nistCategory = some 2 ∧
      entry.pq128HashQueryCeilingLog2 = 30 :=
  ⟨thresholdMlDsaDkgAndSignEntry deployedThresholdMlDsaParamSet b,
   by simp [qsagPq128PortfolioRoster], rfl, rfl, rfl, rfl⟩

/-- **Master Composed Portfolio Theorem (`qsag_pq128_portfolio_soundness_budget`)**:
    For ANY `QueryBudget` `b` with `qOnlineSessions + 1 ≤ 2 ^ 20`, every one of the 12 entries of
    `qsagPq128PortfolioRoster b` achieves `atLeastBits 128` for both its classical bound and its
    QROM bound whenever `qHash + 1` is within that entry's own ceiling
    `2 ^ entry.pq128HashQueryCeilingLog2`: `2^56` for eleven entries, `2^30` for the Category-2
    threshold ML-DSA-44 entry. There is no single `2^56` statement over all 12:
    `tooth_portfolio_category2_entry_fails_at_2pow56`. The `Hem` entry is the all-stage IOP-layer
    budget `hemNv20ComposedPureTerms` under Fiat–Shamir search (about `129.7` QROM bits at
    `qHash + 1 = 2^56`); it excludes Merkle commitment extraction and the AIR reduction, see
    `qsagPq128PortfolioRoster`. -/
theorem qsag_pq128_portfolio_soundness_budget (b : QueryBudget)
    (hqSess : b.qOnlineSessions + 1 ≤ 2 ^ 20) :
    (qsagPq128PortfolioRoster b).length = 12 ∧
    (∀ entry ∈ qsagPq128PortfolioRoster b,
      b.qHash + 1 ≤ 2 ^ entry.pq128HashQueryCeilingLog2 →
      atLeastBits 128 entry.classicalBound ∧ atLeastBits 128 entry.quantumBound) := by
  refine ⟨rfl, ?_⟩
  intro entry hMem hCeil
  by_cases hMl : entry.profileId = .thresholdMlDsaDkgAndSign
  · simp only [qsagPq128PortfolioRoster, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · cases hMl
    · cases hMl
    · cases hMl
    · cases hMl
    · cases hMl
    · cases hMl
    · cases hMl
    · exact threshold_mldsa_entry_pq128_within_ceiling deployedThresholdMlDsaParamSet b
        hCeil hqSess
    · cases hMl
    · cases hMl
    · cases hMl
    · cases hMl
  have hqHash : b.qHash + 1 ≤ 2 ^ 56 := by
    rw [roster_ceiling_of_not_mldsa b entry hMem hMl] at hCeil
    exact hCeil
  have hHi := qsag_pq128_high_query_2pow56_non_folding_budget b hqHash hqSess
  have h8Sq : 8 * (b.qHash + 1) ^ 2 ≤ 2 ^ 115 := by
    have p1 : (b.qHash + 1) ^ 2 ≤ (2 ^ 56) ^ 2 := Nat.pow_le_pow_left hqHash 2
    have p2 : 8 * (2 ^ 56) ^ 2 = 2 ^ 115 := by decide
    rw [← p2]; exact Nat.mul_le_mul_left 8 p1
  have hHemClassical : atLeastBits 128
      (RatBound.sumList (hemNv20ComposedPureTerms.map (RatBound.scale (2 ^ 56)))) := by
    decide +kernel
  have hHemQuantum : atLeastBits 128
      (RatBound.sumList (hemNv20ComposedPureTerms.map (RatBound.scale (2 ^ 115)))) := by
    decide +kernel
  by_cases hId : entry.profileId = .hemExt4WhirPq128
  · simp only [qsagPq128PortfolioRoster, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · cases hId
    · cases hId
    · cases hId
    · cases hId
    · cases hId
    · exact ⟨atLeastBits_of_le (sumList_map_scale_mono hqHash hemNv20ComposedPureTerms)
               hHemClassical,
             atLeastBits_of_le (sumList_map_scale_mono h8Sq hemNv20ComposedPureTerms)
               hHemQuantum⟩
    · cases hId
    · cases hId
    · cases hId
    · cases hId
    · cases hId
    · cases hId
  · exact hHi entry hMem hId hMl

private theorem ratBound_add_num_pos_left {a b : RatBound} (ha : 0 < a.num) :
    0 < (RatBound.add a b).num := by
  unfold RatBound.add
  dsimp only
  exact Nat.lt_of_lt_of_le (Nat.mul_pos ha b.h_pos) (Nat.le_add_right _ _)

/-- Concrete 2-query Hadamard superposition circuit (`QuantumAdv 2 2 1 2`) preparing
    `|0, 0, 0⟩ + |1, 0, 0⟩` via `hadamardQuery2 2 1` after query 0 so query 1 probes `oracleXor`
    in uniform superposition across both basis inputs! -/
def concreteSuperpositionAdv : QuantumAdv 2 2 1 2 where
  init := fun x y _ => if x.1 == 0 && y.1 == 0 then ⟨1, 0⟩ else GaussInt.zero
  h_init_pos := by decide
  steps := fun i => if i.1 == 0 then hadamardQuery2 2 1 else ScaledUnitary.id 2 2 1

/-- Concrete 2-query adaptive `OracleComp` decision tree branching on the LSB of its first
    256-bit oracle query response before choosing its second query input! -/
def concreteAdaptiveTwoQueryAdv : OracleComp (BitVec 8) (BitVec 256) (BitVec 8) :=
  .query (BitVec.ofNat 8 1) (fun d₁ =>
    let x₂ := if d₁.getLsbD 0 then BitVec.ofNat 8 2 else BitVec.ofNat 8 3
    .query x₂ (fun _ => .pure x₂))

/-- Non-scalar quartic basis element `v ∈ QuarticGoldilocks` (`v^2 = u ∈ GoldilocksExt2`) and
    non-zero quadratic polynomial `P(X) = X^2 - u` (`cs = [-u, 0, 1]`). -/
def quarticGoldilocksVBasis : QuarticGoldilocks :=
  ⟨GoldilocksExt2.zero, GoldilocksExt2.one⟩

def quarticGoldilocksQuadraticPoly : List QuarticGoldilocks :=
  [ ⟨CommRingOps.neg GoldilocksExt2.uBasis, GoldilocksExt2.zero⟩,
    QuarticGoldilocks.zero,
    QuarticGoldilocks.one ]

/-- **Master Non-Vacuity & Inhabitedness Witness (`inhabited_concrete_security_budget_roster`)**:
    Certifies that EVERY foundational carrier and reduction in `ConcreteSecurityBudget.lean` is
    genuinely inhabited by non-trivial witnesses (`0` identity-hash or empty-list shortcuts):
    1. `concreteSuperpositionAdv` prepares genuine uniform quantum superposition across both basis
       queries (`queryWeight = 1` on `x = 0` AND `x = 1`) before applying `oracleXor`,
    2. `concreteAdaptiveTwoQueryAdv` satisfies `QueryBounded 2` and instantiates
       `classical_lazy_ro_fiber_search_bound` on `wotsCDibits128Bv` (`fiberCard ≤ 1`),
    3. `quarticGoldilocksQuadraticPoly` (`X^2 - u`) is non-zero at `0`, vanishes at the two distinct
       non-scalar quartic elements `+v` and `-v`, and satisfies `goldilocksExt4_schwartz_zippel_root_bound`,
    4. At concrete budget `b₀ = ⟨2^30 - 1, 2^16, 2^20 - 1⟩` (the largest power-of-two hash budget
       inside every entry's ceiling, at the full `2^20` sessions), all 12 entries of
       `qsagPq128PortfolioRoster b₀` have strictly positive numerators (`0 < num`, non-zero
       bounds!) and simultaneously satisfy `atLeastBits 128` classically and in the QROM! -/
theorem inhabited_concrete_security_budget_roster :
    let b₀ : QueryBudget := ⟨2 ^ 30 - 1, 2 ^ 16, 2 ^ 20 - 1⟩
    let ψPre := advStateAt concreteSuperpositionAdv (fun _ => BitVec.zero 2) 1 (by decide)
    let dRef : BitVec 256 := BitVec.ofNat 256 0xdeadbeefcafebabe
    let S4 : List QuarticGoldilocks :=
      [QuarticGoldilocks.zero, quarticGoldilocksVBasis, CommRingOps.neg quarticGoldilocksVBasis]
    (QVec.queryWeight ψPre ⟨0, by decide⟩ = 1 ∧ QVec.queryWeight ψPre ⟨1, by decide⟩ = 1) ∧
    (QueryBounded 2 concreteAdaptiveTwoQueryAdv ∧
      fiberCard 256 wotsCDibits128Bv (wotsCDibits128Bv dRef) ≤ 1) ∧
    (RoundPoly.evalCoeffs quarticGoldilocksQuadraticPoly QuarticGoldilocks.zero ≠ CommRingOps.zero ∧
      RoundPoly.evalCoeffs quarticGoldilocksQuadraticPoly quarticGoldilocksVBasis = CommRingOps.zero ∧
      (S4.filter (fun r =>
        decide (RoundPoly.evalCoeffs quarticGoldilocksQuadraticPoly r = CommRingOps.zero))).length = 2) ∧
    ((qsagPq128PortfolioRoster b₀).length = 12 ∧
      ∀ entry ∈ qsagPq128PortfolioRoster b₀,
        0 < entry.classicalBound.num ∧
        0 < entry.quantumBound.num ∧
        atLeastBits 128 entry.classicalBound ∧
        atLeastBits 128 entry.quantumBound) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- 1. Genuine superposition query weights on both `x = 0` and `x = 1`:
    constructor <;> decide
  · -- 2. Adaptive 2-query `OracleComp` + `wotsCDibits128Bv` injectivity fiber bound:
    refine ⟨?_, fiberCard_le_one_of_injective 256 wotsCDibits128Bv
                  (fun _ _ h => wotsCDibits128Bv_injective h) _⟩
    unfold concreteAdaptiveTwoQueryAdv QueryBounded
    intro _ _
    exact trivial
  · -- 3. Non-scalar quadratic polynomial `X^2 - u` over `QuarticGoldilocks`:
    refine ⟨by decide, by decide, by decide⟩
  · -- 4. Concrete 12-profile portfolio evaluation at `b₀ = ⟨2^30 - 1, 2^16, 2^20 - 1⟩`:
    let b₀ : QueryBudget := ⟨2 ^ 30 - 1, 2 ^ 16, 2 ^ 20 - 1⟩
    have hPort := qsag_pq128_portfolio_soundness_budget b₀ (by decide)
    refine ⟨hPort.1, ?_⟩
    intro entry hMem
    have hBits := hPort.2 entry hMem
      (Nat.le_trans (by decide : b₀.qHash + 1 ≤ 2 ^ 30)
        (Nat.pow_le_pow_right (by decide) (roster_ceiling_ge_30 b₀ entry hMem)))
    have hPos : 0 < entry.classicalBound.num ∧ 0 < entry.quantumBound.num := by
      simp only [qsagPq128PortfolioRoster, List.mem_cons, List.not_mem_nil, or_false] at hMem
      rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨by decide, by decide⟩
      · exact ⟨by decide, by decide⟩
      · exact ⟨by decide, by decide⟩
      · exact ⟨ratBound_add_num_pos_left (by decide), ratBound_add_num_pos_left (by decide)⟩
      · exact ⟨by decide, by decide⟩
      · exact ⟨ratBound_add_num_pos_left (by decide), ratBound_add_num_pos_left (by decide)⟩
      · exact ⟨ratBound_add_num_pos_left (by decide), ratBound_add_num_pos_left (by decide)⟩
      · exact ⟨ratBound_add_num_pos_left (by decide), ratBound_add_num_pos_left (by decide)⟩
      · exact ⟨by decide, by decide⟩
      · exact ⟨ratBound_add_num_pos_left (by decide), ratBound_add_num_pos_left (by decide)⟩
      · exact ⟨ratBound_add_num_pos_left (by decide), ratBound_add_num_pos_left (by decide)⟩
      · exact ⟨ratBound_add_num_pos_left (by decide), ratBound_add_num_pos_left (by decide)⟩
    exact ⟨hPos.1, hPos.2, hBits.1, hBits.2⟩

/-- Cardinality of the joint 13-repetition, 11-bit signed-monomial RLWE challenge.
    This is challenge-space arithmetic, not an RLWE hardness or extraction theorem. -/
def rlweJointSignedMonomialChallengeCard : Nat := (2 ^ 11) ^ 13

/-- The deployed joint challenge has 143 bits, not 260 bits. Its squared search-space
    threshold lies strictly between the squares of `2^71` and `2^72`; it alone cannot
    supply a 128-bit quantum search budget. -/
theorem rlwe_joint_signed_monomial_challenge_143_bits :
    rlweJointSignedMonomialChallengeCard = 2 ^ 143 ∧
    (2 ^ 71) ^ 2 < rlweJointSignedMonomialChallengeCard ∧
    rlweJointSignedMonomialChallengeCard < (2 ^ 72) ^ 2 := by
  decide +kernel

/-- Cardinality `(2^11)^24 = 2^264` of the 24-repetition, 11-bit signed-monomial `PQ128`
    RLWE OR-Sigma challenge space (`264` classical bits = `132` Grover bits). -/
def rlweJointSignedMonomial24ChallengeCard : Nat := (2 ^ 11) ^ 24

/-- Single-execution interactive soundness error `1 / (2^11)^reps` of the `reps`-challenge
    signed-monomial RLWE OR-Sigma (`1 / 2^143` at `reps = 13`, `1 / 2^264` at `reps = 24`). -/
def rlweOrSigmaSoundnessError (reps : Nat) : RatBound :=
  ⟨1, (2 ^ 11) ^ reps, Nat.pow_pos (by decide)⟩

/-- Single-execution interactive soundness error `1 / 2^143` of the 13-challenge RLWE OR-Sigma. -/
abbrev rlweOrSigma13SoundnessError : RatBound := rlweOrSigmaSoundnessError 13

/-- Single-execution interactive soundness error `1 / 2^264` of the 24-challenge `PQ128`
    RLWE OR-Sigma (`extract_rlwe_or_sigma_24_short_witness` in `Qsag.RlweCyclotomicExtraction`). -/
abbrev rlweOrSigma24SoundnessError : RatBound := rlweOrSigmaSoundnessError 24

/-- **24-Challenge `PQ128` RLWE OR-Sigma Within `2^66` Query Ceiling
    (`rlwe_or_sigma_24_pq128_within_ceiling`)**:
    For every `QueryBudget` `b` with `b.qHash + 1 ≤ 2^66` (including the portfolio ceiling `2^56`),
    the 24-repetition signed-monomial OR-Sigma (`1 / 2^264`) achieves `atLeastBits 128` both
    classically (`classicalFiatShamirBound`) and in the QROM (`quantumGroverGrindingBound`). -/
theorem rlwe_or_sigma_24_pq128_within_ceiling (b : QueryBudget)
    (hqHash : b.qHash + 1 ≤ 2 ^ 66) :
    atLeastBits 128 (classicalFiatShamirBound b.qHash (rlweOrSigmaSoundnessError 24)) ∧
    atLeastBits 128 (quantumGroverGrindingBound b.qHash (rlweOrSigmaSoundnessError 24)) := by
  have h264 : (2 ^ 11) ^ 24 = 2 ^ 264 := (Nat.pow_mul 2 11 24).symm
  refine ⟨?_, ?_⟩
  · unfold atLeastBits classicalFiatShamirBound RatBound.scale rlweOrSigmaSoundnessError
    dsimp only
    rw [Nat.mul_one, h264]
    have hm := Nat.mul_le_mul_right (2 ^ 128) hqHash
    rw [← Nat.pow_add] at hm
    exact Nat.le_trans hm (Nat.pow_le_pow_right (by decide : 0 < 2) (by decide : 66 + 128 ≤ 264))
  · unfold atLeastBits quantumGroverGrindingBound RatBound.scale rlweOrSigmaSoundnessError
    dsimp only
    rw [Nat.mul_one, h264]
    have hSq : (b.qHash + 1) ^ 2 ≤ 2 ^ 132 := by
      have p1 := Nat.pow_le_pow_left hqHash 2
      have p2 : (2 ^ 66) ^ 2 = 2 ^ 132 := (Nat.pow_mul 2 66 2).symm
      rw [p2] at p1; exact p1
    have h8 : 8 * (b.qHash + 1) ^ 2 ≤ 2 ^ 135 := by
      have p1 := Nat.mul_le_mul_left 8 hSq
      have p2 : 8 * 2 ^ 132 = 2 ^ 3 * 2 ^ 132 := rfl
      rw [p2, ← Nat.pow_add] at p1; exact p1
    have hm := Nat.mul_le_mul_right (2 ^ 128) h8
    rw [← Nat.pow_add] at hm
    exact Nat.le_trans hm (Nat.pow_le_pow_right (by decide : 0 < 2) (by decide : 135 + 128 ≤ 264))

/-- **24-Challenge `PQ128` Signed-Monomial RLWE OR-Sigma Classical & QROM Soundness Budget
    (`rlwe_or_sigma_24_pq128_classical_and_qrom_soundness`)**:
    1. The 24-repetition signed-monomial challenge space has exact cardinality `2^264 = (2^132)^2`
       (`264` classical bits, `132` Grover bits `≥ 128`),
    2. Under unitary O2H quantum Fiat–Shamir (`quantumGroverGrindingBound`), for ALL
       `qHash + 1 ≤ 2 ^ 66`, the 24-challenge profile achieves `atLeastBits 129` (hence
       `atLeastBits 128`) in the QROM and `atLeastBits 198` classically,
    3. Under `[DFM20]` QROM Measure-and-Reprogram (`quantumDfmMeasureReprogramBound 1`), for ALL
       `qHash + 1 ≤ 2 ^ 67`, the 24-challenge profile achieves `atLeastBits 128` in the QROM,
    4. At the portfolio ceiling `qHash + 1 ≤ 2 ^ 56`, the 24-challenge profile achieves
       `atLeastBits 208` classically and `atLeastBits 149` in the QROM! -/
theorem rlwe_or_sigma_24_pq128_classical_and_qrom_soundness :
    rlweJointSignedMonomial24ChallengeCard = 2 ^ 264 ∧
    (2 ^ 132) ^ 2 = rlweJointSignedMonomial24ChallengeCard ∧
    (∀ qHash : Nat, qHash + 1 ≤ 2 ^ 66 →
      atLeastBits 198 (classicalFiatShamirBound qHash (rlweOrSigmaSoundnessError 24)) ∧
      atLeastBits 129 (quantumGroverGrindingBound qHash (rlweOrSigmaSoundnessError 24)) ∧
      atLeastBits 128 (quantumGroverGrindingBound qHash (rlweOrSigmaSoundnessError 24))) ∧
    (∀ qHash : Nat, qHash + 1 ≤ 2 ^ 67 →
      atLeastBits 128 (quantumDfmMeasureReprogramBound 1 qHash (rlweOrSigmaSoundnessError 24))) ∧
    (∀ qHash : Nat, qHash + 1 ≤ 2 ^ 56 →
      atLeastBits 208 (classicalFiatShamirBound qHash (rlweOrSigmaSoundnessError 24)) ∧
      atLeastBits 149 (quantumGroverGrindingBound qHash (rlweOrSigmaSoundnessError 24))) := by
  have h264Card : rlweJointSignedMonomial24ChallengeCard = 2 ^ 264 := by
    unfold rlweJointSignedMonomial24ChallengeCard
    exact (Nat.pow_mul 2 11 24).symm
  have h264 : (2 ^ 11) ^ 24 = 2 ^ 264 := (Nat.pow_mul 2 11 24).symm
  have h132 : (2 ^ 132) ^ 2 = rlweJointSignedMonomial24ChallengeCard :=
    (Nat.pow_mul 2 132 2).symm.trans h264Card.symm
  refine ⟨h264Card, h132, ?_, ?_, ?_⟩
  · intro qHash hq66
    have hCl : atLeastBits 198 (classicalFiatShamirBound qHash (rlweOrSigmaSoundnessError 24)) := by
      unfold atLeastBits classicalFiatShamirBound RatBound.scale rlweOrSigmaSoundnessError
      dsimp only
      rw [Nat.mul_one, h264]
      have hm := Nat.mul_le_mul_right (2 ^ 198) hq66
      rw [← Nat.pow_add] at hm
      exact hm
    have hQu129 : atLeastBits 129 (quantumGroverGrindingBound qHash (rlweOrSigmaSoundnessError 24)) := by
      unfold atLeastBits quantumGroverGrindingBound RatBound.scale rlweOrSigmaSoundnessError
      dsimp only
      rw [Nat.mul_one, h264]
      have hSq : (qHash + 1) ^ 2 ≤ 2 ^ 132 := by
        have p1 := Nat.pow_le_pow_left hq66 2
        rw [(Nat.pow_mul 2 66 2).symm] at p1; exact p1
      have h8 : 8 * (qHash + 1) ^ 2 ≤ 2 ^ 135 := by
        have p1 := Nat.mul_le_mul_left 8 hSq
        have p2 : 8 * 2 ^ 132 = 2 ^ 3 * 2 ^ 132 := rfl
        rw [p2, ← Nat.pow_add] at p1; exact p1
      have hm := Nat.mul_le_mul_right (2 ^ 129) h8
      rw [← Nat.pow_add] at hm
      exact hm
    exact ⟨hCl, hQu129, atLeastBits_antitone_bits (by decide) hQu129⟩
  · intro qHash hq67
    unfold atLeastBits quantumDfmMeasureReprogramBound RatBound.scale rlweOrSigmaSoundnessError
    dsimp only
    rw [Nat.mul_one, h264]
    have h2q : 2 * qHash + 1 ≤ 2 ^ 68 := by omega
    have hSq : (2 * qHash + 1) ^ 2 ≤ 2 ^ 136 := by
      have p1 := Nat.pow_le_pow_left h2q 2
      rw [(Nat.pow_mul 2 68 2).symm] at p1; exact p1
    have hm := Nat.mul_le_mul_right (2 ^ 128) hSq
    rw [← Nat.pow_add] at hm
    exact hm
  · intro qHash hq56
    refine ⟨?_, ?_⟩
    · unfold atLeastBits classicalFiatShamirBound RatBound.scale rlweOrSigmaSoundnessError
      dsimp only
      rw [Nat.mul_one, h264]
      have hm := Nat.mul_le_mul_right (2 ^ 208) hq56
      rw [← Nat.pow_add] at hm
      exact hm
    · unfold atLeastBits quantumGroverGrindingBound RatBound.scale rlweOrSigmaSoundnessError
      dsimp only
      rw [Nat.mul_one, h264]
      have hSq : (qHash + 1) ^ 2 ≤ 2 ^ 112 := by
        have p1 := Nat.pow_le_pow_left hq56 2
        rw [(Nat.pow_mul 2 56 2).symm] at p1; exact p1
      have h8 : 8 * (qHash + 1) ^ 2 ≤ 2 ^ 115 := by
        have p1 := Nat.mul_le_mul_left 8 hSq
        have p2 : 8 * 2 ^ 112 = 2 ^ 3 * 2 ^ 112 := rfl
        rw [p2, ← Nat.pow_add] at p1; exact p1
      have hm := Nat.mul_le_mul_right (2 ^ 149) h8
      rw [← Nat.pow_add] at hm
      exact hm

/-- `#tooth`: the 13-challenge RLWE OR-Sigma (`1 / 2^143`) fails 128-bit QROM soundness at the
    portfolio ceiling `qHash = 2^56 - 1` (and even at `qHash = 2^8`). -/
theorem tooth_rlwe_or_sigma_13_not_pq128_at_2pow56 :
    ¬ atLeastBits 128 (quantumGroverGrindingBound (2 ^ 56 - 1) (rlweOrSigmaSoundnessError 13)) := by
  decide +kernel

theorem tooth_rlwe_or_sigma_13_not_pq128_qrom :
    ¬ atLeastBits 128 (quantumGroverGrindingBound (2 ^ 8) rlweOrSigma13SoundnessError) ∧
    ¬ atLeastBits 128 (quantumDfmMeasureReprogramBound 1 (2 ^ 8) rlweOrSigma13SoundnessError) ∧
    ¬ atLeastBits 128 (quantumGroverGrindingBound (2 ^ 56 - 1) rlweOrSigma13SoundnessError) := by
  refine ⟨by decide +kernel, by decide +kernel, tooth_rlwe_or_sigma_13_not_pq128_at_2pow56⟩

theorem witness_rlwe_or_sigma_24_qrom_budget :
    ∃ b : QueryBudget, b.qHash + 1 ≤ 2 ^ 66 :=
  ⟨⟨2 ^ 56 - 1, 0, 0⟩, by decide⟩

/-- At `2^56` offline queries the roster contains an entry below 128 QROM bits: the Category-2
    threshold ML-DSA-44 entry. This is why `qsag_pq128_portfolio_soundness_budget` is stated
    per-entry ceiling. -/
theorem tooth_portfolio_category2_entry_fails_at_2pow56 :
    ∃ entry ∈ qsagPq128PortfolioRoster ⟨2 ^ 56 - 1, 0, 2 ^ 20 - 1⟩,
      ¬ atLeastBits 128 entry.quantumBound :=
  ⟨thresholdMlDsaDkgAndSignEntry deployedThresholdMlDsaParamSet ⟨2 ^ 56 - 1, 0, 2 ^ 20 - 1⟩,
   by simp [qsagPq128PortfolioRoster],
   tooth_threshold_mldsa44_entry_not_pq128_at_2pow56⟩

#tooth_pair Qsag.ggmNodeTweakIndex_injective vs Qsag.tooth_ggmNodeTweakIndex_unbounded_tree_collides
#tooth_pair Qsag.tweaked_multi_target_query_partition_union_bound vs Qsag.tooth_untweaked_targets_exceed_partition_bound
#tooth_pair Qsag.densePcgV3SaltedSeedQuantumBound_140 vs Qsag.tooth_densePcgV3_untweaked_not_pq128
#tooth_pair Qsag.densePcgV3_partitioned_seed_search_140 vs Qsag.tooth_densePcgV3_untweaked_not_pq128
#tooth_pair Qsag.densePcgV3SaltedSeedQuantumBound_140 vs Qsag.tooth_densePcgV3_salted_not_141
#tooth_pair Qsag.densePcgV3SeedQuantumBound_128 vs Qsag.tooth_densePcgV3_untweaked_not_pq128
#tooth_pair Qsag.densePcgV3SharedTweakSeedQuantumBound_128 vs Qsag.tooth_densePcgV3_session_id_reuse_not_pq128
#tooth_pair Qsag.mlDsa_offline_grinding_pq128_regime vs Qsag.tooth_mldsa44_offline_grinding_above_2pow30
#tooth_pair Qsag.mlDsa_offline_grinding_pq128_regime vs Qsag.tooth_mldsa65_offline_grinding_above_2pow47
#tooth_pair Qsag.mlDsa_offline_grinding_pq128_regime vs Qsag.tooth_mldsa87_offline_grinding_above_2pow63
#tooth_pair Qsag.mlDsa_offline_grinding_bits_at_2pow56 vs Qsag.tooth_mldsa44_offline_grinding_not_78_at_2pow56
#tooth_pair Qsag.mlDsa_offline_grinding_bits_at_2pow56 vs Qsag.tooth_mldsa65_offline_grinding_not_111_at_2pow56
#tooth_pair Qsag.threshold_mldsa_entry_pq128_within_ceiling vs Qsag.tooth_threshold_mldsa_entry_above_ceiling_not_pq128
#tooth_pair Qsag.threshold_mldsa_entry_pq128_within_ceiling vs Qsag.tooth_threshold_mldsa44_entry_not_pq128_at_2pow56
#tooth_pair Qsag.qsag_pq128_portfolio_soundness_budget vs Qsag.tooth_portfolio_category2_entry_fails_at_2pow56
#tooth_pair Qsag.rlwe_or_sigma_24_pq128_within_ceiling vs Qsag.tooth_rlwe_or_sigma_13_not_pq128_at_2pow56

#verify_inhabited Qsag.densePcgV3_partitioned_seed_search_140 Qsag.witness_densePcgV3_query_partition
#verify_inhabited Qsag.densePcgV3SaltedSeedQuantumBound_140 Qsag.witness_densePcgV3_query_budget
#verify_inhabited Qsag.densePcgV3SeedQuantumBound_120 Qsag.witness_densePcgV3_query_budget
#verify_inhabited Qsag.densePcgV3SharedTweakSeedQuantumBound_128 Qsag.witness_densePcgV3_shared_tweak_budget
#verify_inhabited Qsag.threshold_mldsa_entry_pq128_within_ceiling Qsag.witness_threshold_mldsa_budget
#verify_inhabited Qsag.qsag_pq128_portfolio_soundness_budget Qsag.witness_threshold_mldsa_budget
#verify_inhabited Qsag.rlwe_or_sigma_24_pq128_within_ceiling Qsag.witness_rlwe_or_sigma_24_qrom_budget

/-! ## §8. Mechanized `[HRS16]` Quantum Superposition Multi-Tweak Security & Un-Tweaked Grover Loss

Genuine quantum superposition multi-function / multi-tweak preimage & Davies–Meyer second-preimage
resistance following Hülsing, Rijneveld and Song (PKC 2016) / Zhandry multi-function QROM:
1. Joint tweak-input Hilbert-space packing `packTweakQuery : Fin M → Fin (2 ^ n) → Fin (M * 2 ^ n)`
   and exact per-tweak squared-amplitude norm partition `tweakNormSq_partition_eq_stateNormSq`
   (`∑_{t < M} tweakNormSq ψ t = QVec.stateNormSq ψ`).
2. Constructive `q`-query unitary QROM bound `hrs16_superposition_multi_tweak_bound`: for ANY
   quantum circuit `QuantumAdv (M * 2 ^ n) (w + 1) cardAnc q` querying arbitrary superpositions
   across `(t : Fin M) × (x : Fin (2 ^ n))`, simultaneous multi-target fiber-search Born success
   is bounded by `((8 * q ^ 2 + 2) * K) / 2 ^ n` and `8 * K * (q + 1) ^ 2 / 2 ^ n`, **completely
   independent of the tweak count `M`**.
3. Concrete 256-bit security `hrs16_superposition_multi_tweak_pq256_bound` (`≤ 2^-124` for
   `q ≤ 2 ^ 64` and `≤ 2^-132` for `q ≤ 2 ^ 60` across `M = 2 ^ 64` distinct `ADRS` tweaks).
4. Constructive `q`-query unitary Grover lower bound `untweaked_multi_target_grover_lower_bound`
   and `#tooth` witness `tooth_untweaked_multi_target_grover_linear_M_loss` proving un-tweaked
   multi-target (`F(x)` independent of `t`) suffers `≥ M * (q + 1) ^ 2 / (4 * N)` linear `M` loss. -/

/-- Pack tweak index `t : Fin M` and `n`-bit input `x : Fin (2 ^ n)` into `Fin (M * 2 ^ n)`. -/
def packTweakQuery {M n : Nat} (t : Fin M) (x : Fin (2 ^ n)) : Fin (M * 2 ^ n) :=
  ⟨t.1 * 2 ^ n + x.1, by
    have ht : (t.1 + 1) * 2 ^ n ≤ M * 2 ^ n := Nat.mul_le_mul_right (2 ^ n) t.2
    rw [Nat.add_mul, Nat.one_mul] at ht
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left x.2 (t.1 * 2 ^ n)) ht⟩

private theorem div_lt_of_lt_mul_constructive {k M B : Nat} (hk : k < M * B) : k / B < M :=
  match Nat.lt_or_ge (k / B) M with
  | Or.inl h => h
  | Or.inr hGe => False.elim <| by
      have hMul : B * M ≤ B * (k / B) := Nat.mul_le_mul_left B hGe
      have hDivMod : B * (k / B) + k % B = k := Nat.div_add_mod k B
      rw [Nat.mul_comm B M] at hMul
      omega

/-- Extract tweak index `t : Fin M` from packed query coordinate `idx : Fin (M * 2 ^ n)`. -/
def unpackTweakIdx {M n : Nat} (idx : Fin (M * 2 ^ n)) : Fin M :=
  ⟨idx.1 / 2 ^ n, div_lt_of_lt_mul_constructive idx.2⟩

/-- Extract input coordinate `x : Fin (2 ^ n)` from packed query coordinate `idx : Fin (M * 2 ^ n)`. -/
def unpackInputIdx {M n : Nat} (idx : Fin (M * 2 ^ n)) : Fin (2 ^ n) :=
  ⟨idx.1 % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩

theorem unpack_packTweakQuery {M n : Nat} (t : Fin M) (x : Fin (2 ^ n)) :
    unpackTweakIdx (packTweakQuery t x) = t ∧
    unpackInputIdx (packTweakQuery t x) = x := by
  have hPos : 0 < 2 ^ n := Nat.two_pow_pos n
  refine ⟨Fin.ext ?_, Fin.ext ?_⟩
  · dsimp only [unpackTweakIdx, packTweakQuery]
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hPos, Nat.div_eq_of_lt x.2, Nat.zero_add]
  · dsimp only [unpackInputIdx, packTweakQuery]
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt x.2]

private theorem qsum_cast {a b : Nat} (h : a = b) (f : Fin a → Nat) :
    qsum a f = qsum b (fun i => f ⟨i.1, h ▸ i.2⟩) := by
  subst h; rfl

private theorem qsum_mul_tweak_split (M B : Nat) (f : Fin (M * B) → Nat) :
    qsum (M * B) f =
      qsum M (fun t => qsum B (fun x =>
        f ⟨t.1 * B + x.1, by
          have ht : (t.1 + 1) * B ≤ M * B := Nat.mul_le_mul_right B t.2
          rw [Nat.add_mul, Nat.one_mul] at ht
          exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left x.2 (t.1 * B)) ht⟩)) := by
  rw [qsum_cast (Nat.mul_comm M B) f, qsum_mul_split B M]

/-- Per-tweak squared Hilbert-space amplitude norm `‖ψ_t‖² = ∑_{x < 2^n} queryWeight ψ (t, x)`. -/
def tweakNormSq {M n w cardAnc : Nat} (ψ : QVec (M * 2 ^ n) w cardAnc) (t : Fin M) : Nat :=
  qsum (2 ^ n) (fun x => QVec.queryWeight ψ (packTweakQuery t x))

/-- **Superposition Amplitude-Norm Partition Identity (`tweakNormSq_partition_eq_stateNormSq`)**:
    Across any `M`-tweak superposition state `ψ`, `∑_{t < M} ‖ψ_t‖² = ‖ψ‖²`. -/
theorem tweakNormSq_partition_eq_stateNormSq {M n w cardAnc : Nat}
    (ψ : QVec (M * 2 ^ n) w cardAnc) :
    qsum M (fun t => tweakNormSq ψ t) = QVec.stateNormSq ψ := by
  unfold QVec.stateNormSq tweakNormSq packTweakQuery
  exact (qsum_mul_tweak_split M (2 ^ n) (QVec.queryWeight ψ)).symm

/-- Multi-tweak shifted fiber oracle marking `(t, x)` iff `encode t (x ⊕ mask) = targets t`. -/
def hrs16ShiftedMultiTweakOracle {Code : Type} [DecidableEq Code]
    (M n w : Nat) (encode : Fin M → BitVec n → Code) (targets : Fin M → Code) (mask : BitVec n) :
    Fin (M * 2 ^ n) → BitVec (w + 1) :=
  fun idx =>
    let t := unpackTweakIdx idx
    let x := unpackInputIdx idx
    if encode t (BitVec.ofFin x ^^^ mask) = targets t then 1#(w + 1) else 0#(w + 1)

/-- Blank reference oracle over the joint `M`-tweak query space `Fin (M * 2 ^ n)`. -/
def hrs16BlankMultiTweakOracle (M n w : Nat) : Fin (M * 2 ^ n) → BitVec (w + 1) :=
  fun _ => 0#(w + 1)

/-- `[HRS16]` quantum superposition multi-tweak preimage / DM-SPR bound `8 * (q + 1)^2 / 2^n`
    (independent of the number of tweaks `M`). -/
def hrs16SuperpositionBound (n q : Nat) : RatBound :=
  ⟨8 * (q + 1) ^ 2, 2 ^ n, Nat.two_pow_pos n⟩

private theorem sum_masks_multi_tweak_fiber {Code : Type} [DecidableEq Code]
    (M n K : Nat) (encode : Fin M → BitVec n → Code) (targets : Fin M → Code)
    (hFiberLe : ∀ t : Fin M, fiberCard n (encode t) (targets t) ≤ K)
    {w cardAnc : Nat} (ψ : QVec (M * 2 ^ n) w cardAnc) :
    qsum (2 ^ n) (fun m =>
      QVec.queryMassOn
        (fun idx => decide (encode (unpackTweakIdx idx)
          (BitVec.ofFin (unpackInputIdx idx) ^^^ BitVec.ofFin m) = targets (unpackTweakIdx idx)))
        ψ) ≤
      K * QVec.stateNormSq ψ := by
  have hSplitEach : ∀ m : Fin (2 ^ n),
      QVec.queryMassOn
        (fun idx => decide (encode (unpackTweakIdx idx)
          (BitVec.ofFin (unpackInputIdx idx) ^^^ BitVec.ofFin m) = targets (unpackTweakIdx idx))) ψ =
      qsum M (fun t => qsum (2 ^ n) (fun x =>
        if encode t (BitVec.ofFin x ^^^ BitVec.ofFin m) = targets t
        then QVec.queryWeight ψ (packTweakQuery t x) else 0)) := by
    intro m
    unfold QVec.queryMassOn
    rw [qsum_mul_tweak_split M (2 ^ n)]
    apply qsum_congr; intro t
    apply qsum_congr; intro x
    have hPack : (⟨t.1 * 2 ^ n + x.1, _⟩ : Fin (M * 2 ^ n)) = packTweakQuery t x := rfl
    obtain ⟨hT, hX⟩ := unpack_packTweakQuery t x
    simp only [hPack, hT, hX]
    by_cases h : encode t (BitVec.ofFin x ^^^ BitVec.ofFin m) = targets t <;> simp [h]
  rw [qsum_congr hSplitEach, qsum_comm (2 ^ n) M]
  have hPerTweak : ∀ t : Fin M,
      qsum (2 ^ n) (fun m => qsum (2 ^ n) (fun x =>
        if encode t (BitVec.ofFin x ^^^ BitVec.ofFin m) = targets t
        then QVec.queryWeight ψ (packTweakQuery t x) else 0)) ≤
      K * tweakNormSq ψ t := by
    intro t
    rw [sum_masks_shifted_fiber n (encode t) (targets t) (fun x => QVec.queryWeight ψ (packTweakQuery t x))]
    exact Nat.mul_le_mul_right (tweakNormSq ψ t) (hFiberLe t)
  apply Nat.le_trans (qsum_le_qsum hPerTweak)
  rw [qsum_mul_left K, tweakNormSq_partition_eq_stateNormSq]
  exact Nat.le_refl _

/-- **Quantum Superposition Multi-Tweak Preimage & Second-Preimage Theorem
    (`hrs16_superposition_multi_tweak_bound`, Hülsing–Rijneveld–Song PKC 2016)**:
    For ANY `q`-query unitary quantum adversary `A : QuantumAdv (M * 2 ^ n) (w + 1) cardAnc q`
    making arbitrary superposition queries across `(t : Fin M) × (x : Fin (2 ^ n))` and ANY
    `M` tweak-separated functions `encode t` with preimage fiber size `≤ K` at `targets t`,
    the average Born-rule probability of finding a valid `(t, x)` preimage for ANY of the `M`
    tweaks simultaneously is bounded by `((8 * q ^ 2 + 2) * K) / 2 ^ n` and
    `8 * K * (q + 1) ^ 2 / 2 ^ n` — **completely independent of `M`** (`0` linear `M` loss). -/
theorem hrs16_superposition_multi_tweak_bound {Code : Type} [DecidableEq Code]
    {M n w cardAnc q K : Nat}
    (A : QuantumAdv (M * 2 ^ n) (w + 1) cardAnc q)
    (encode : Fin M → BitVec n → Code) (targets : Fin M → Code)
    (hFiberLe : ∀ t : Fin M, fiberCard n (encode t) (targets t) ≤ K) :
    let ψBlank := runQuantumAdv A (hrs16BlankMultiTweakOracle M n w)
    let normFinal := QVec.stateNormSq ψBlank
    let avgBornSuccess : RatBound :=
      ⟨qsum (2 ^ n) (fun m =>
         QVec.measureNormSq
           (fun idx => decide (encode (unpackTweakIdx idx)
             (BitVec.ofFin (unpackInputIdx idx) ^^^ BitVec.ofFin m) = targets (unpackTweakIdx idx)))
           (runQuantumAdv A (hrs16ShiftedMultiTweakOracle M n w encode targets (BitVec.ofFin m)))),
       2 ^ n * normFinal,
       Nat.mul_pos (Nat.two_pow_pos n) (runQuantumAdv_normSq_pos A (hrs16BlankMultiTweakOracle M n w))⟩
    RatBound.le avgBornSuccess ⟨(8 * q ^ 2 + 2) * K, 2 ^ n, Nat.two_pow_pos n⟩ ∧
    RatBound.le avgBornSuccess ⟨8 * K * (q + 1) ^ 2, 2 ^ n, Nat.two_pow_pos n⟩ := by
  let ψBlank := runQuantumAdv A (hrs16BlankMultiTweakOracle M n w)
  let normFinal := QVec.stateNormSq ψBlank
  have hPerMask : ∀ m : Fin (2 ^ n),
      let Sm : Fin (M * 2 ^ n) → Bool := fun idx =>
        decide (encode (unpackTweakIdx idx)
          (BitVec.ofFin (unpackInputIdx idx) ^^^ BitVec.ofFin m) = targets (unpackTweakIdx idx))
      QVec.measureNormSq Sm
        (runQuantumAdv A (hrs16ShiftedMultiTweakOracle M n w encode targets (BitVec.ofFin m))) ≤
      2 * QVec.measureNormSq Sm ψBlank +
      8 * q * qsum q (fun step =>
        suffixScale A step.1 (Nat.le_of_lt step.2) *
          QVec.queryMassOn Sm (advStateAt A (hrs16BlankMultiTweakOracle M n w) step.1 (Nat.le_of_lt step.2))) := by
    intro m
    let Sm : Fin (M * 2 ^ n) → Bool := fun idx =>
      decide (encode (unpackTweakIdx idx)
        (BitVec.ofFin (unpackInputIdx idx) ^^^ BitVec.ofFin m) = targets (unpackTweakIdx idx))
    have hBorn := born_measure_le_two_add_two_dist_sq Sm
      (runQuantumAdv A (hrs16ShiftedMultiTweakOracle M n w encode targets (BitVec.ofFin m))) ψBlank
    have hAgree : ∀ idx : Fin (M * 2 ^ n), Sm idx = false →
        hrs16ShiftedMultiTweakOracle M n w encode targets (BitVec.ofFin m) idx =
          hrs16BlankMultiTweakOracle M n w idx := by
      intro idx hFalse
      unfold hrs16ShiftedMultiTweakOracle hrs16BlankMultiTweakOracle
      have hNe : encode (unpackTweakIdx idx)
          (BitVec.ofFin (unpackInputIdx idx) ^^^ BitVec.ofFin m) ≠ targets (unpackTweakIdx idx) := by
        intro hEq; simp [Sm, hEq] at hFalse
      simp [hNe]
    have hO2h := qrom_o2h_telescoping_disturbance_le A
      (hrs16ShiftedMultiTweakOracle M n w encode targets (BitVec.ofFin m))
      (hrs16BlankMultiTweakOracle M n w) Sm hAgree
    have h2 := Nat.mul_le_mul_left 2 hO2h
    rw [← Nat.mul_assoc 2 (4 * q), show 2 * (4 * q) = 8 * q by omega] at h2
    exact Nat.le_trans hBorn (Nat.add_le_add_left h2 _)
  have hSumMasks := qsum_le_qsum hPerMask
  rw [qsum_add, qsum_mul_left 2, qsum_mul_left (8 * q), qsum_comm (2 ^ n) q] at hSumMasks
  have hBlankLe :
      qsum (2 ^ n) (fun m =>
        QVec.measureNormSq
          (fun idx => decide (encode (unpackTweakIdx idx)
            (BitVec.ofFin (unpackInputIdx idx) ^^^ BitVec.ofFin m) = targets (unpackTweakIdx idx)))
          ψBlank) ≤ K * normFinal :=
    sum_masks_multi_tweak_fiber M n K encode targets hFiberLe ψBlank
  have hQueryLe :
      qsum q (fun step => qsum (2 ^ n) (fun m =>
        suffixScale A step.1 (Nat.le_of_lt step.2) *
          QVec.queryMassOn
            (fun idx => decide (encode (unpackTweakIdx idx)
              (BitVec.ofFin (unpackInputIdx idx) ^^^ BitVec.ofFin m) = targets (unpackTweakIdx idx)))
            (advStateAt A (hrs16BlankMultiTweakOracle M n w) step.1 (Nat.le_of_lt step.2)))) ≤
      q * (K * normFinal) := by
    have hEachStep : ∀ step : Fin q,
        qsum (2 ^ n) (fun m =>
          suffixScale A step.1 (Nat.le_of_lt step.2) *
            QVec.queryMassOn
              (fun idx => decide (encode (unpackTweakIdx idx)
                (BitVec.ofFin (unpackInputIdx idx) ^^^ BitVec.ofFin m) = targets (unpackTweakIdx idx)))
              (advStateAt A (hrs16BlankMultiTweakOracle M n w) step.1 (Nat.le_of_lt step.2))) ≤
        K * normFinal := by
      intro step
      rw [qsum_mul_left]
      have hStepMass := sum_masks_multi_tweak_fiber M n K encode targets hFiberLe
        (advStateAt A (hrs16BlankMultiTweakOracle M n w) step.1 (Nat.le_of_lt step.2))
      have hMulS := Nat.mul_le_mul_left (suffixScale A step.1 (Nat.le_of_lt step.2)) hStepMass
      apply Nat.le_trans hMulS
      rw [advStateAt_normSq]
      dsimp only [normFinal, ψBlank]
      rw [runQuantumAdv_normSq]
      have hScale := prefix_mul_suffix_eq_total A step.1 (Nat.le_of_lt step.2)
      apply Nat.le_of_eq
      calc suffixScale A step.1 (Nat.le_of_lt step.2) *
             (K * (prefixScale A step.1 (Nat.le_of_lt step.2) * QVec.stateNormSq A.init))
        _ = K * ((prefixScale A step.1 (Nat.le_of_lt step.2) * suffixScale A step.1 (Nat.le_of_lt step.2)) *
                 QVec.stateNormSq A.init) := by
          rw [← Nat.mul_assoc, Nat.mul_comm (suffixScale A step.1 (Nat.le_of_lt step.2)) K,
              Nat.mul_assoc K, ← Nat.mul_assoc (suffixScale A step.1 (Nat.le_of_lt step.2)),
              Nat.mul_comm (suffixScale A step.1 (Nat.le_of_lt step.2))]
        _ = K * (prefixScale A q (Nat.le_refl q) * QVec.stateNormSq A.init) := by rw [hScale]
    simpa only [qsum_const] using qsum_le_qsum hEachStep
  have hTotalLe :
      qsum (2 ^ n) (fun m =>
        QVec.measureNormSq
          (fun idx => decide (encode (unpackTweakIdx idx)
            (BitVec.ofFin (unpackInputIdx idx) ^^^ BitVec.ofFin m) = targets (unpackTweakIdx idx)))
          (runQuantumAdv A (hrs16ShiftedMultiTweakOracle M n w encode targets (BitVec.ofFin m)))) ≤
      (8 * q ^ 2 + 2) * K * normFinal := by
    have hComb := Nat.le_trans hSumMasks
      (Nat.add_le_add (Nat.mul_le_mul_left 2 hBlankLe) (Nat.mul_le_mul_left (8 * q) hQueryLe))
    have hAlg : 2 * (K * normFinal) + 8 * q * (q * (K * normFinal)) =
        (8 * q ^ 2 + 2) * K * normFinal := by
      rw [Nat.pow_two, Nat.add_mul, Nat.add_mul, Nat.add_comm]
      simp only [Nat.mul_assoc]
    rwa [hAlg] at hComb
  have hFirst : RatBound.le
      ⟨qsum (2 ^ n) (fun m =>
         QVec.measureNormSq
           (fun idx => decide (encode (unpackTweakIdx idx)
             (BitVec.ofFin (unpackInputIdx idx) ^^^ BitVec.ofFin m) = targets (unpackTweakIdx idx)))
           (runQuantumAdv A (hrs16ShiftedMultiTweakOracle M n w encode targets (BitVec.ofFin m)))),
       2 ^ n * normFinal,
       Nat.mul_pos (Nat.two_pow_pos n) (runQuantumAdv_normSq_pos A (hrs16BlankMultiTweakOracle M n w))⟩
      ⟨(8 * q ^ 2 + 2) * K, 2 ^ n, Nat.two_pow_pos n⟩ := by
    unfold RatBound.le; dsimp only
    have hm := Nat.mul_le_mul_right (2 ^ n) hTotalLe
    rwa [Nat.mul_assoc ((8 * q ^ 2 + 2) * K) normFinal (2 ^ n), Nat.mul_comm normFinal (2 ^ n)] at hm
  refine ⟨hFirst, RatBound.le_trans hFirst ?_⟩
  unfold RatBound.le; dsimp only
  apply Nat.mul_le_mul_right
  have hLe8 : 8 * q ^ 2 + 2 ≤ 8 * (q + 1) ^ 2 := by
    simp only [Nat.pow_two, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    omega
  calc (8 * q ^ 2 + 2) * K
    _ ≤ (8 * (q + 1) ^ 2) * K := Nat.mul_le_mul_right K hLe8
    _ = 8 * K * (q + 1) ^ 2 := by
      rw [Nat.mul_assoc 8 K, Nat.mul_comm K ((q + 1) ^ 2), ← Nat.mul_assoc]

/-- **Concrete 256-Bit `[HRS16]` Quantum Superposition Multi-Tweak Security
    (`hrs16_superposition_multi_tweak_pq256_bound`)**:
    For `N = 2 ^ 256` and ANY number `M` of distinct `ADRS` tweaks (including `M = 2 ^ 64`) with
    injective per-tweak encodings (`fiberCard ≤ 1`), full quantum superposition across all `M`
    tweaks achieves `≤ 2^-124` (`atLeastBits 124`) for all `q ≤ 2 ^ 64` and `≤ 2^-132`
    (`atLeastBits 132`) for all `q ≤ 2 ^ 60`, with `0` linear `M` loss. -/
theorem hrs16_superposition_multi_tweak_pq256_bound {Code : Type} [DecidableEq Code]
    {M w cardAnc q : Nat}
    (A : QuantumAdv (M * 2 ^ 256) (w + 1) cardAnc q)
    (encode : Fin M → BitVec 256 → Code) (targets : Fin M → Code)
    (hInj : ∀ t : Fin M, Function.Injective (encode t)) :
    let ψBlank := runQuantumAdv A (hrs16BlankMultiTweakOracle M 256 w)
    let avgBornSuccess : RatBound :=
      ⟨qsum (2 ^ 256) (fun m =>
         QVec.measureNormSq
           (fun idx => decide (encode (unpackTweakIdx idx)
             (BitVec.ofFin (unpackInputIdx idx) ^^^ BitVec.ofFin m) = targets (unpackTweakIdx idx)))
           (runQuantumAdv A (hrs16ShiftedMultiTweakOracle M 256 w encode targets (BitVec.ofFin m)))),
       2 ^ 256 * QVec.stateNormSq ψBlank,
       Nat.mul_pos (Nat.two_pow_pos 256) (runQuantumAdv_normSq_pos A (hrs16BlankMultiTweakOracle M 256 w))⟩
    RatBound.le avgBornSuccess (hrs16SuperpositionBound 256 q) ∧
    (q ≤ 2 ^ 64 → atLeastBits 124 avgBornSuccess) ∧
    (q ≤ 2 ^ 60 → atLeastBits 132 avgBornSuccess) := by
  have hFib : ∀ t : Fin M, fiberCard 256 (encode t) (targets t) ≤ 1 :=
    fun t => fiberCard_le_one_of_injective 256 (encode t) (hInj t) (targets t)
  have hBound := (hrs16_superposition_multi_tweak_bound (K := 1) A encode targets hFib).2
  have hBound1 : RatBound.le
      ⟨qsum (2 ^ 256) (fun m =>
         QVec.measureNormSq
           (fun idx => decide (encode (unpackTweakIdx idx)
             (BitVec.ofFin (unpackInputIdx idx) ^^^ BitVec.ofFin m) = targets (unpackTweakIdx idx)))
           (runQuantumAdv A (hrs16ShiftedMultiTweakOracle M 256 w encode targets (BitVec.ofFin m)))),
       2 ^ 256 * QVec.stateNormSq (runQuantumAdv A (hrs16BlankMultiTweakOracle M 256 w)),
       Nat.mul_pos (Nat.two_pow_pos 256) (runQuantumAdv_normSq_pos A (hrs16BlankMultiTweakOracle M 256 w))⟩
      (hrs16SuperpositionBound 256 q) := by
    simpa only [hrs16SuperpositionBound, Nat.mul_one] using hBound
  refine ⟨hBound1, fun hq64 => atLeastBits_of_le hBound1 ?_, fun hq60 => atLeastBits_of_le hBound1 ?_⟩
  · unfold atLeastBits hrs16SuperpositionBound; dsimp only
    have hMono : 8 * (q + 1) ^ 2 * 2 ^ 124 ≤ 8 * (2 ^ 64 + 1) ^ 2 * 2 ^ 124 :=
      Nat.mul_le_mul_right (2 ^ 124) (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left (Nat.add_le_add_right hq64 1) 2))
    exact Nat.le_trans hMono (by decide)
  · unfold atLeastBits hrs16SuperpositionBound; dsimp only
    have hMono : 8 * (q + 1) ^ 2 * 2 ^ 132 ≤ 8 * (2 ^ 60 + 1) ^ 2 * 2 ^ 132 :=
      Nat.mul_le_mul_right (2 ^ 132) (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left (Nat.add_le_add_right hq60 1) 2))
    exact Nat.le_trans hMono (by decide)

/-- **`DensePcg` V3 Full-Forest (`2,097,088` GGM Tweaks) Quantum Superposition Bound
    (`densePcgV3_hrs16_superposition_141`)**:
    Upgrades `densePcgV3_partitioned_seed_search_140` from classical query-partitioning (`qs : List Nat`)
    to arbitrary `q`-query unitary quantum superposition across all `densePcgV3NodeTargets = 2,097,088`
    salted GGM node tweaks: for `q + 1 ≤ 2 ^ 56`, average Born-rule recovery probability satisfies
    `atLeastBits 141` (and `atLeastBits 140`) with `0` linear `2,097,088`-target loss. -/
theorem densePcgV3_hrs16_superposition_141 {Code : Type} [DecidableEq Code]
    {w cardAnc q : Nat} (hq : q + 1 ≤ 2 ^ 56)
    (A : QuantumAdv (densePcgV3NodeTargets * 2 ^ 256) (w + 1) cardAnc q)
    (encode : Fin densePcgV3NodeTargets → BitVec 256 → Code)
    (targets : Fin densePcgV3NodeTargets → Code)
    (hInj : ∀ t : Fin densePcgV3NodeTargets, Function.Injective (encode t)) :
    let ψBlank := runQuantumAdv A (hrs16BlankMultiTweakOracle densePcgV3NodeTargets 256 w)
    let avgBornSuccess : RatBound :=
      ⟨qsum (2 ^ 256) (fun m =>
         QVec.measureNormSq
           (fun idx => decide (encode (unpackTweakIdx idx)
             (BitVec.ofFin (unpackInputIdx idx) ^^^ BitVec.ofFin m) = targets (unpackTweakIdx idx)))
           (runQuantumAdv A (hrs16ShiftedMultiTweakOracle densePcgV3NodeTargets 256 w encode targets (BitVec.ofFin m)))),
       2 ^ 256 * QVec.stateNormSq ψBlank,
       Nat.mul_pos (Nat.two_pow_pos 256)
         (runQuantumAdv_normSq_pos A (hrs16BlankMultiTweakOracle densePcgV3NodeTargets 256 w))⟩
    densePcgV3NodeTargets = 2097088 ∧
    atLeastBits 141 avgBornSuccess ∧
    atLeastBits 140 avgBornSuccess := by
  have hBound := (hrs16_superposition_multi_tweak_pq256_bound A encode targets hInj).1
  have h141 : atLeastBits 141 (hrs16SuperpositionBound 256 q) := by
    unfold atLeastBits hrs16SuperpositionBound; dsimp only
    have hMono : 8 * (q + 1) ^ 2 * 2 ^ 141 ≤ 8 * (2 ^ 56) ^ 2 * 2 ^ 141 :=
      Nat.mul_le_mul_right (2 ^ 141) (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left hq 2))
    exact Nat.le_trans hMono (by decide)
  have hAvg141 := atLeastBits_of_le hBound h141
  exact ⟨densePcgV3NodeTargets_exact.1, hAvg141, atLeastBits_antitone_bits (by decide) hAvg141⟩

/-! ### §8.2 Constructive `q`-Query Unitary Multi-Target Grover Lower Bound (`#tooth` for Un-Tweaked `F(x)`) -/

private theorem finIntSum_const :
    ∀ (N : Nat) (c : Int), finIntSum N (fun _ => c) = Int.ofNat N * c
  | 0, c => by simp [finIntSum]
  | n + 1, c => by
    simp only [finIntSum, finIntSum_const n c]
    have h1 : Int.ofNat 1 * c = c := Int.one_mul c
    rw [ofNat_add_eq n 1, Int.add_mul, h1, Int.add_comm]

private theorem finIntSum_add :
    ∀ (N : Nat) (f g : Fin N → Int),
      finIntSum N (fun i => f i + g i) = finIntSum N f + finIntSum N g
  | 0, _, _ => rfl
  | n + 1, f, g => by
    simp only [finIntSum, finIntSum_add n]
    omega

private theorem finIntSum_mul_left (c : Int) :
    ∀ (N : Nat) (f : Fin N → Int),
      finIntSum N (fun i => c * f i) = c * finIntSum N f
  | 0, _ => by simp [finIntSum]
  | n + 1, f => by
    simp only [finIntSum, finIntSum_mul_left c n, Int.mul_add]

private theorem finIntSum_ofNat_eq :
    ∀ (N : Nat) (f : Fin N → Nat),
      finIntSum N (fun i => Int.ofNat (f i)) = Int.ofNat (qsum N f)
  | 0, _ => rfl
  | n + 1, f => by
    simp only [finIntSum, qsum, finIntSum_ofNat_eq n, ofNat_add_eq]

private theorem grover_int_reflection_normSq (N : Nat) (v : Fin N → Int) :
    finIntSum N (fun x =>
      (2 * finIntSum N v - Int.ofNat N * v x) * (2 * finIntSum N v - Int.ofNat N * v x)) =
      Int.ofNat (N ^ 2) * finIntSum N (fun x => v x * v x) := by
  let S := finIntSum N v
  change finIntSum N (fun x => (2 * S - Int.ofNat N * v x) * (2 * S - Int.ofNat N * v x)) = _
  have hPoint : ∀ x : Fin N,
      (2 * S - Int.ofNat N * v x) * (2 * S - Int.ofNat N * v x) =
        4 * S * S + (-(4 * S * Int.ofNat N)) * v x +
          (Int.ofNat N * Int.ofNat N) * (v x * v x) := fun x => by
    have hNegSq : ∀ u : Int, (-u) * (-u) = u * u := fun u => by
      rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
    calc (2 * S - Int.ofNat N * v x) * (2 * S - Int.ofNat N * v x)
      _ = (2 * S) * (2 * S) + (2 * S) * (-(Int.ofNat N * v x)) +
            (-(Int.ofNat N * v x)) * (2 * S) + (Int.ofNat N * v x) * (Int.ofNat N * v x) := by
          rw [Int.sub_eq_add_neg, Int.add_mul, Int.mul_add, Int.mul_add, hNegSq, ← Int.add_assoc]
      _ = 4 * S * S + (-(4 * S * Int.ofNat N)) * v x +
            (Int.ofNat N * Int.ofNat N) * (v x * v x) := by
          have p1 : (2 * S) * (2 * S) = 4 * S * S := by
            rw [Int.mul_assoc 2 S, Int.mul_left_comm S 2 S, ← Int.mul_assoc (2 : Int) 2, Int.mul_assoc 4 S S]
            rfl
          have p2 : (2 * S) * (-(Int.ofNat N * v x)) = -(2 * S * Int.ofNat N * v x) := by
            rw [Int.mul_neg, ← Int.mul_assoc (2 * S) (Int.ofNat N) (v x)]
          have p3 : (-(Int.ofNat N * v x)) * (2 * S) = -(2 * S * Int.ofNat N * v x) := by
            rw [Int.neg_mul, Int.mul_comm (Int.ofNat N * v x) (2 * S),
                ← Int.mul_assoc (2 * S) (Int.ofNat N) (v x)]
          have p4 : (-(4 * S * Int.ofNat N)) * v x = -(4 * S * Int.ofNat N * v x) := by
            rw [Int.neg_mul]
          have p5 : (Int.ofNat N * v x) * (Int.ofNat N * v x) =
              (Int.ofNat N * Int.ofNat N) * (v x * v x) := by
            rw [Int.mul_assoc (Int.ofNat N) (v x), Int.mul_left_comm (v x) (Int.ofNat N) (v x),
                ← Int.mul_assoc (Int.ofNat N) (Int.ofNat N)]
          rw [p1, p2, p3, p4, p5]
          have p6 : 4 * S * Int.ofNat N * v x =
              2 * S * Int.ofNat N * v x + 2 * S * Int.ofNat N * v x := by
            have e4 : (4 : Int) = 2 + 2 := rfl
            rw [e4, Int.add_mul, Int.add_mul, Int.add_mul]
          omega
  have hCongr : finIntSum N (fun x => (2 * S - Int.ofNat N * v x) * (2 * S - Int.ofNat N * v x)) =
      finIntSum N (fun x => (4 * S * S + (-(4 * S * Int.ofNat N)) * v x) +
        (Int.ofNat N * Int.ofNat N) * (v x * v x)) := by
    have : (fun x => (2 * S - Int.ofNat N * v x) * (2 * S - Int.ofNat N * v x)) =
        (fun x => (4 * S * S + (-(4 * S * Int.ofNat N)) * v x) +
          (Int.ofNat N * Int.ofNat N) * (v x * v x)) := funext hPoint
    rw [this]
  rw [hCongr, finIntSum_add, finIntSum_add, finIntSum_const,
      finIntSum_mul_left (-(4 * S * Int.ofNat N)),
      finIntSum_mul_left (Int.ofNat N * Int.ofNat N)]
  change Int.ofNat N * (4 * S * S) + (-(4 * S * Int.ofNat N)) * S +
      (Int.ofNat N * Int.ofNat N) * finIntSum N (fun x => v x * v x) = _
  have hCancel : Int.ofNat N * (4 * S * S) + (-(4 * S * Int.ofNat N)) * S = 0 := by
    rw [Int.neg_mul, Int.mul_assoc 4 S (Int.ofNat N), Int.mul_comm S (Int.ofNat N),
        ← Int.mul_assoc 4 (Int.ofNat N) S, Int.mul_comm 4 (Int.ofNat N),
        Int.mul_assoc (Int.ofNat N) 4 S, Int.mul_assoc (Int.ofNat N) (4 * S) S,
        Int.mul_assoc 4 S S]
    omega
  rw [hCancel, Int.zero_add, Nat.pow_two, ofNat_mul_eq]

/-- Exact integer `N`-item Grover diffusion operator `D_N : ψ_x ↦ 2 ∑_z ψ_z - N ψ_x` (`scaleSq = N^2`). -/
def groverDiffusion (N : Nat) (hN : 0 < N) : ScaledUnitary N 1 1 where
  apply ψ x y a :=
    let s := finGaussSum N (fun z => ψ z y a)
    GaussInt.sub (GaussInt.scaleInt 2 s) (GaussInt.scaleInt (Int.ofNat N) (ψ x y a))
  scaleSq := N ^ 2
  h_scale_pos := Nat.pow_pos hN
  map_sub ψ φ := by
    have hSumSub : ∀ (K : Nat) (f g : Fin K → GaussInt),
        finGaussSum K (fun z => GaussInt.sub (f z) (g z)) =
          GaussInt.sub (finGaussSum K f) (finGaussSum K g) := by
      intro K
      induction K with
      | zero => intros; rfl
      | succ k ih =>
        intro f g
        simp only [finGaussSum, ih]
        unfold GaussInt.add GaussInt.sub; ext <;> dsimp only <;> omega
    funext x y a
    dsimp only [QVec.sub]
    rw [hSumSub]
    unfold GaussInt.sub GaussInt.scaleInt
    ext <;> dsimp only <;> rw [Int.mul_sub, Int.mul_sub] <;> omega
  normSq_eq ψ := by
    have hSumRe : ∀ (K : Nat) (f : Fin K → GaussInt),
        (finGaussSum K f).re = finIntSum K (fun z => (f z).re) := by
      intro K; induction K with
      | zero => intros; rfl
      | succ k ih => intro f; simp only [finGaussSum, finIntSum, GaussInt.add, ih]
    have hSumIm : ∀ (K : Nat) (f : Fin K → GaussInt),
        (finGaussSum K f).im = finIntSum K (fun z => (f z).im) := by
      intro K; induction K with
      | zero => intros; rfl
      | succ k ih => intro f; simp only [finGaussSum, finIntSum, GaussInt.add, ih]
    have hFiber : ∀ (y : Fin 2) (a : Fin 1),
        qsum N (fun x => GaussInt.normSq
          (GaussInt.sub (GaussInt.scaleInt 2 (finGaussSum N (fun z => ψ z y a)))
            (GaussInt.scaleInt (Int.ofNat N) (ψ x y a)))) =
        N ^ 2 * qsum N (fun x => GaussInt.normSq (ψ x y a)) := by
      intro y a
      apply Int.ofNat.inj
      rw [ofNat_mul_eq, ← finIntSum_ofNat_eq, ← finIntSum_ofNat_eq]
      have hLHS : finIntSum N (fun x => Int.ofNat (GaussInt.normSq
          (GaussInt.sub (GaussInt.scaleInt 2 (finGaussSum N (fun z => ψ z y a)))
            (GaussInt.scaleInt (Int.ofNat N) (ψ x y a))))) =
          finIntSum N (fun x =>
            (2 * finIntSum N (fun z => (ψ z y a).re) - Int.ofNat N * (ψ x y a).re) *
              (2 * finIntSum N (fun z => (ψ z y a).re) - Int.ofNat N * (ψ x y a).re) +
            (2 * finIntSum N (fun z => (ψ z y a).im) - Int.ofNat N * (ψ x y a).im) *
              (2 * finIntSum N (fun z => (ψ z y a).im) - Int.ofNat N * (ψ x y a).im)) := by
        congr 1; funext x
        rw [← GaussInt.normSqInt_eq_ofNat_normSq]
        unfold GaussInt.normSqInt GaussInt.sub GaussInt.scaleInt
        dsimp only
        rw [hSumRe, hSumIm]
      have hRHS : finIntSum N (fun x => Int.ofNat (GaussInt.normSq (ψ x y a))) =
          finIntSum N (fun x => (ψ x y a).re * (ψ x y a).re + (ψ x y a).im * (ψ x y a).im) := by
        congr 1; funext x; exact (GaussInt.normSqInt_eq_ofNat_normSq _).symm
      rw [hLHS, hRHS, finIntSum_add, finIntSum_add,
          grover_int_reflection_normSq N (fun z => (ψ z y a).re),
          grover_int_reflection_normSq N (fun z => (ψ z y a).im), Int.mul_add]
    unfold QVec.stateNormSq QVec.queryWeight
    simp only [qsum, Nat.add_zero]
    rw [qsum_add, qsum_add, hFiber ⟨0, by decide⟩ ⟨0, by decide⟩,
        hFiber ⟨1, by decide⟩ ⟨0, by decide⟩, Nat.left_distrib]

/-- Un-tweaked `M`-target indicator oracle `F : Fin N → BitVec 1` (`F(x) = 1` iff `x < M`),
    modeling a hash family that omits distinct `ADRS` tweaks across `M` targets. -/
def untweakedMultiTargetOracle (N M : Nat) : Fin N → BitVec 1 :=
  fun x => if x.1 < M then 1#1 else 0#1

private def groverTemplateState (N M : Nat) (α β : Int) : QVec N 1 1 :=
  fun x y _ =>
    let amp := if x.1 < M then α else β
    ⟨if y.1 == 0 then amp else -amp, 0⟩

private def untweakedGroverAmpsNat (N M : Nat) : Nat → Nat × Nat
  | 0 => (1, 1)
  | j + 1 =>
    let p := untweakedGroverAmpsNat N M j
    ((N - 2 * M) * p.1 + 2 * (N - M) * p.2,
     (N - 2 * M) * p.2 - 2 * M * p.1)

private theorem qsum_prefix_const :
    ∀ (N M : Nat), M ≤ N → ∀ (c d : Nat),
      qsum N (fun x => if x.1 < M then c else d) = M * c + (N - M) * d
  | 0, M, hLe, c, d => by
    have hM0 : M = 0 := by omega
    subst hM0; simp [qsum]
  | n + 1, 0, _, c, d => by
    have hEq : qsum (n + 1) (fun x : Fin (n + 1) => if x.1 < 0 then c else d) =
        qsum (n + 1) (fun _ => d) := by
      apply qsum_congr; intro x; simp
    rw [hEq, qsum_const]; simp
  | n + 1, m + 1, hLe, c, d => by
    simp only [qsum, Nat.zero_lt_succ, ↓reduceIte]
    have hTail : qsum n (fun i : Fin n => if i.1 + 1 < m + 1 then c else d) =
        qsum n (fun i : Fin n => if i.1 < m then c else d) := by
      apply qsum_congr; intro i
      by_cases hi : i.1 < m
      · have hi1 : i.1 + 1 < m + 1 := Nat.succ_lt_succ hi; simp [hi, hi1]
      · have hi1 : ¬ (i.1 + 1 < m + 1) := fun h => hi (Nat.lt_of_succ_lt_succ h); simp [hi, hi1]
    rw [hTail, qsum_prefix_const n m (Nat.le_of_succ_le_succ hLe) c d]
    have hSub : n + 1 - (m + 1) = n - m := Nat.succ_sub_succ_eq_sub n m
    rw [hSub, Nat.add_mul, Nat.one_mul]; omega

private theorem finIntSum_prefix_const :
    ∀ (N M : Nat), M ≤ N → ∀ (u v : Int),
      finIntSum N (fun x => if x.1 < M then u else v) = Int.ofNat M * u + Int.ofNat (N - M) * v
  | 0, M, hLe, u, v => by
    have hM0 : M = 0 := by omega
    subst hM0; simp [finIntSum]
  | n + 1, 0, _, u, v => by
    have hEq : (fun x : Fin (n + 1) => if x.1 < 0 then u else v) = (fun _ => v) := by
      funext x; simp
    rw [hEq, finIntSum_const]; simp
  | n + 1, m + 1, hLe, u, v => by
    simp only [finIntSum, Nat.zero_lt_succ, ↓reduceIte]
    have hTail : (fun i : Fin n => if i.1 + 1 < m + 1 then u else v) =
        (fun i : Fin n => if i.1 < m then u else v) := by
      funext i
      by_cases hi : i.1 < m
      · have hi1 : i.1 + 1 < m + 1 := Nat.succ_lt_succ hi; simp [hi, hi1]
      · have hi1 : ¬ (i.1 + 1 < m + 1) := fun h => hi (Nat.lt_of_succ_lt_succ h); simp [hi, hi1]
    rw [hTail, finIntSum_prefix_const n m (Nat.le_of_succ_le_succ hLe) u v]
    have hSub : n + 1 - (m + 1) = n - m := Nat.succ_sub_succ_eq_sub n m
    have h1 : Int.ofNat 1 * u = u := Int.one_mul u
    rw [hSub, ofNat_add_eq m 1, Int.add_mul, h1]
    omega

/-- Explicit `q`-query unitary Grover circuit (`QuantumAdv N 1 1 q`) attacking un-tweaked `M`-target `F`. -/
def untweakedGroverAdv (N M q : Nat) (hN : 0 < N) : QuantumAdv N 1 1 q where
  init := groverTemplateState N M 1 1
  h_init_pos := by
    have hEach : ∀ x : Fin N, QVec.queryWeight (groverTemplateState N M 1 1) x = 2 := by
      intro x; unfold QVec.queryWeight groverTemplateState
      simp only [qsum]
      by_cases hx : x.1 < M <;> simp [hx, GaussInt.normSq]
    unfold QVec.stateNormSq
    rw [qsum_congr hEach, qsum_const]
    exact Nat.mul_pos hN (by decide)
  steps _ := groverDiffusion N hN

private theorem grover_sub_guard {N M j α β : Nat}
    (_hM_pos : 1 ≤ M)
    (hStep4 : 4 * (j + 1) * (j + 2) * M ≤ N)
    (hαHi : α ≤ (2 * j + 1) * N ^ j)
    (hβHi : β ≤ N ^ j)
    (hβLo : N ^ (j + 1) ≤ N * β + 2 * j * (j + 1) * M * N ^ j) :
    2 * M * α ≤ (N - 2 * M) * β := by
  have hN_ge_8M : 8 * M ≤ N := by
    have h8 : 8 ≤ 4 * (j + 1) * (j + 2) := by
      simp only [Nat.mul_add, Nat.add_mul]; omega
    exact Nat.le_trans (Nat.mul_le_mul_right M h8) hStep4
  have hN_pos : 0 < N := by omega
  have hSumHi : α + β ≤ (2 * j + 2) * N ^ j := by
    have hAdd := Nat.add_le_add hαHi hβHi
    have hR : (2 * j + 1) * N ^ j + N ^ j = (2 * j + 2) * N ^ j := by
      rw [← Nat.succ_mul (2 * j + 1) (N ^ j)]
    rwa [hR] at hAdd
  have hMulSum : N * (2 * M * α + 2 * M * β) ≤ 2 * M * (2 * j + 2) * N ^ (j + 1) := by
    have hL : N * (2 * M * α + 2 * M * β) = 2 * M * N * (α + β) := by
      rw [← Nat.mul_add (2 * M) α β, ← Nat.mul_assoc N (2 * M), Nat.mul_comm N (2 * M)]
    have hR : 2 * M * N * ((2 * j + 2) * N ^ j) = 2 * M * (2 * j + 2) * N ^ (j + 1) := by
      rw [Nat.pow_succ, Nat.mul_comm (N ^ j) N, Nat.mul_assoc (2 * M) N,
          Nat.mul_left_comm N (2 * j + 2) (N ^ j), ← Nat.mul_assoc (2 * M) (2 * j + 2)]
    rw [hL, ← hR]
    exact Nat.mul_le_mul_left (2 * M * N) hSumHi
  have hMulLo : N ^ (j + 2) ≤ N * (N * β) + 2 * j * (j + 1) * M * N ^ (j + 1) := by
    have hm := Nat.mul_le_mul_left N hβLo
    have eL : N * N ^ (j + 1) = N ^ (j + 2) := by rw [Nat.pow_succ N (j + 1), Nat.mul_comm]
    have eR : N * (2 * j * (j + 1) * M * N ^ j) = 2 * j * (j + 1) * M * N ^ (j + 1) := by
      rw [Nat.pow_succ N j, Nat.mul_comm (N ^ j) N, ← Nat.mul_assoc N (2 * j * (j + 1) * M) (N ^ j),
          Nat.mul_comm N (2 * j * (j + 1) * M), Nat.mul_assoc]
    rw [Nat.mul_add, eL, eR] at hm
    exact hm
  have hCoefLe : 2 * M * (2 * j + 2) + 2 * j * (j + 1) * M ≤ N := by
    have hCoef : 2 * (2 * j + 2) + 2 * j * (j + 1) ≤ 4 * (j + 1) * (j + 2) := by
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.mul_assoc]
      omega
    have hRearr : 2 * M * (2 * j + 2) + 2 * j * (j + 1) * M =
        (2 * (2 * j + 2) + 2 * j * (j + 1)) * M := by
      rw [Nat.add_mul, Nat.mul_assoc 2 M (2 * j + 2), Nat.mul_comm M (2 * j + 2),
          ← Nat.mul_assoc 2 (2 * j + 2) M]
    rw [hRearr]
    exact Nat.le_trans (Nat.mul_le_mul_right M hCoef) hStep4
  have hCap : 2 * M * (2 * j + 2) * N ^ (j + 1) + 2 * j * (j + 1) * M * N ^ (j + 1) ≤ N ^ (j + 2) := by
    rw [← Nat.add_mul, Nat.pow_succ N (j + 1), Nat.mul_comm (N ^ (j + 1)) N]
    exact Nat.mul_le_mul_right (N ^ (j + 1)) hCoefLe
  have hChain : N * (2 * M * α + 2 * M * β) + 2 * j * (j + 1) * M * N ^ (j + 1) ≤
      N * (N * β) + 2 * j * (j + 1) * M * N ^ (j + 1) :=
    Nat.le_trans (Nat.add_le_add_right hMulSum _) (Nat.le_trans hCap hMulLo)
  have hNMul : N * (2 * M * α + 2 * M * β) ≤ N * (N * β) := Nat.le_of_add_le_add_right hChain
  have hCancN : 2 * M * α + 2 * M * β ≤ N * β := Nat.le_of_mul_le_mul_left hNMul hN_pos
  have hSplitN : (N - 2 * M) * β + 2 * M * β = N * β := by
    rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
  omega

private theorem untweakedGroverAmpsNat_bounds (N M q : Nat)
    (hM_pos : 1 ≤ M) (hRegime : 4 * q * (q + 1) * M ≤ N) :
    ∀ j : Nat, j ≤ q →
      let p := untweakedGroverAmpsNat N M j
      p.1 ≤ (2 * j + 1) * N ^ j ∧
      p.2 ≤ N ^ j ∧
      N ^ (j + 1) ≤ N * p.2 + 2 * j * (j + 1) * M * N ^ j ∧
      (j + 1) * N ^ j ≤ 2 * p.1
  | 0, _ => by
    simp only [untweakedGroverAmpsNat, Nat.pow_zero, Nat.zero_add, Nat.pow_one]
    refine ⟨by decide, by decide, ?_, by decide⟩
    omega
  | j + 1, hj1 => by
    obtain ⟨hαHi, hβHi, hβLo, hαLo⟩ :=
      untweakedGroverAmpsNat_bounds N M q hM_pos hRegime j (Nat.le_of_succ_le hj1)
    let α := (untweakedGroverAmpsNat N M j).1
    let β := (untweakedGroverAmpsNat N M j).2
    change α ≤ (2 * j + 1) * N ^ j at hαHi
    change β ≤ N ^ j at hβHi
    change N ^ (j + 1) ≤ N * β + 2 * j * (j + 1) * M * N ^ j at hβLo
    change (j + 1) * N ^ j ≤ 2 * α at hαLo
    have hStepProd : (j + 1) * (j + 2) ≤ q * (q + 1) :=
      Nat.mul_le_mul hj1 (Nat.add_le_add_right hj1 1)
    have hStep4 : 4 * (j + 1) * (j + 2) * M ≤ N := by
      have hm := Nat.mul_le_mul_right M (Nat.mul_le_mul_left 4 hStepProd)
      simp only [Nat.mul_assoc] at hm hRegime ⊢
      exact Nat.le_trans hm hRegime
    have hN_ge_8M : 8 * M ≤ N := by
      have h8 : 8 ≤ 4 * (j + 1) * (j + 2) := by
        simp only [Nat.mul_add, Nat.add_mul]; omega
      exact Nat.le_trans (Nat.mul_le_mul_right M h8) hStep4
    have hN_pos : 0 < N := by omega
    have hSub : 2 * M * α ≤ (N - 2 * M) * β :=
      grover_sub_guard hM_pos hStep4 hαHi hβHi hβLo
    have h2β_ge : N ^ j ≤ 2 * β := by
      have hPrev4 : 4 * j * (j + 1) * M ≤ N := by
        have hLe : 4 * j * (j + 1) ≤ 4 * (j + 1) * (j + 2) := by
          have : j * (j + 1) ≤ (j + 1) * (j + 2) :=
            Nat.le_trans (Nat.mul_le_mul_right (j + 1) (Nat.le_succ j))
              (Nat.mul_le_mul_left (j + 1) (Nat.le_succ (j + 1)))
          have h4 := Nat.mul_le_mul_left 4 this
          simpa only [Nat.mul_assoc] using h4
        exact Nat.le_trans (Nat.mul_le_mul_right M hLe) hStep4
      have hDoubLo : 2 * (N * N ^ j) ≤ N * (2 * β) + 4 * j * (j + 1) * M * N ^ j := by
        have hm := Nat.mul_le_mul_left 2 hβLo
        have eL : 2 * N ^ (j + 1) = 2 * (N * N ^ j) := by rw [Nat.pow_succ N j, Nat.mul_comm (N ^ j) N]
        have eR1 : 2 * (N * β) = N * (2 * β) := by rw [← Nat.mul_assoc, Nat.mul_comm 2 N, Nat.mul_assoc]
        have eR2 : 2 * (2 * j * (j + 1) * M * N ^ j) = 4 * j * (j + 1) * M * N ^ j := by
          simp only [← Nat.mul_assoc]
        rw [Nat.mul_add, eL, eR1, eR2] at hm
        exact hm
      have hCap : 4 * j * (j + 1) * M * N ^ j ≤ N * N ^ j := Nat.mul_le_mul_right (N ^ j) hPrev4
      have hChain : N * N ^ j + N * N ^ j ≤ N * (2 * β) + N * N ^ j := by
        have e2 : 2 * (N * N ^ j) = N * N ^ j + N * N ^ j := Nat.two_mul _
        rw [← e2]
        exact Nat.le_trans hDoubLo (Nat.add_le_add_left hCap _)
      exact Nat.le_of_mul_le_mul_left (Nat.le_of_add_le_add_right hChain) hN_pos
    let α' := (N - 2 * M) * α + 2 * (N - M) * β
    let β' := (N - 2 * M) * β - 2 * M * α
    change α' ≤ (2 * (j + 1) + 1) * N ^ (j + 1) ∧
      β' ≤ N ^ (j + 1) ∧
      N ^ (j + 2) ≤ N * β' + 2 * (j + 1) * (j + 2) * M * N ^ (j + 1) ∧
      (j + 2) * N ^ (j + 1) ≤ 2 * α'
    have hα'_hi : α' ≤ (2 * (j + 1) + 1) * N ^ (j + 1) := by
      have p1 : (N - 2 * M) * α ≤ N * ((2 * j + 1) * N ^ j) :=
        Nat.le_trans (Nat.mul_le_mul_right α (Nat.sub_le N (2 * M))) (Nat.mul_le_mul_left N hαHi)
      have p2 : 2 * (N - M) * β ≤ 2 * N * N ^ j :=
        Nat.le_trans (Nat.mul_le_mul_right β (Nat.mul_le_mul_left 2 (Nat.sub_le N M)))
          (Nat.mul_le_mul_left (2 * N) hβHi)
      have hRhsEq : N * ((2 * j + 1) * N ^ j) + 2 * N * N ^ j = (2 * (j + 1) + 1) * N ^ (j + 1) := by
        rw [Nat.pow_succ N j, Nat.mul_comm (N ^ j) N, ← Nat.mul_assoc N (2 * j + 1) (N ^ j),
            Nat.mul_comm N (2 * j + 1), Nat.mul_assoc (2 * j + 1) N (N ^ j),
            Nat.mul_assoc 2 N (N ^ j), ← Nat.add_mul (2 * j + 1) 2 (N * N ^ j)]
        exact congrArg (· * (N * N ^ j)) (by omega)
      rw [← hRhsEq]
      exact Nat.add_le_add p1 p2
    have hβ'_hi : β' ≤ N ^ (j + 1) := by
      have s1 : β' ≤ N * β :=
        Nat.le_trans (Nat.sub_le _ _) (Nat.mul_le_mul_right β (Nat.sub_le N (2 * M)))
      have s2 : N * β ≤ N ^ (j + 1) := by
        rw [Nat.pow_succ N j, Nat.mul_comm (N ^ j) N]
        exact Nat.mul_le_mul_left N hβHi
      exact Nat.le_trans s1 s2
    have hβ'_lo : N ^ (j + 2) ≤ N * β' + 2 * (j + 1) * (j + 2) * M * N ^ (j + 1) := by
      have hId : β' + 2 * M * α + 2 * M * β = N * β := by
        rw [Nat.sub_add_cancel hSub, ← Nat.add_mul, Nat.sub_add_cancel (by omega)]
      have hIdN : N * β' + 2 * M * N * (α + β) = N * (N * β) := by
        have hId2 : β' + 2 * M * (α + β) = N * β := by
          rw [Nat.mul_add, ← Nat.add_assoc]; exact hId
        have hm := congrArg (N * ·) hId2
        rw [Nat.mul_add, ← Nat.mul_assoc N (2 * M) (α + β), Nat.mul_comm N (2 * M)] at hm
        exact hm
      have hSumHi : α + β ≤ (2 * j + 2) * N ^ j := by
        have hAdd := Nat.add_le_add hαHi hβHi
        rwa [← Nat.succ_mul (2 * j + 1) (N ^ j)] at hAdd
      have hLossLe : 2 * M * N * (α + β) ≤ (4 * j + 4) * M * N ^ (j + 1) := by
        have hm := Nat.mul_le_mul_left (2 * M * N) hSumHi
        have hRearr : 2 * M * N * ((2 * j + 2) * N ^ j) = (4 * j + 4) * M * N ^ (j + 1) := by
          have c2 : 2 * (2 * j + 2) = 4 * j + 4 := by omega
          rw [Nat.pow_succ N j, Nat.mul_comm (N ^ j) N, Nat.mul_assoc (2 * M) N,
              Nat.mul_left_comm N (2 * j + 2) (N ^ j), ← Nat.mul_assoc (2 * M) (2 * j + 2),
              Nat.mul_assoc 2 M (2 * j + 2), Nat.mul_comm M (2 * j + 2),
              ← Nat.mul_assoc 2 (2 * j + 2) M, c2]
        rwa [hRearr] at hm
      have hMulLo : N ^ (j + 2) ≤ N * (N * β) + 2 * j * (j + 1) * M * N ^ (j + 1) := by
        have hm := Nat.mul_le_mul_left N hβLo
        have eL : N * N ^ (j + 1) = N ^ (j + 2) := by rw [Nat.pow_succ N (j + 1), Nat.mul_comm]
        have eR : N * (2 * j * (j + 1) * M * N ^ j) = 2 * j * (j + 1) * M * N ^ (j + 1) := by
          rw [Nat.pow_succ N j, Nat.mul_comm (N ^ j) N, ← Nat.mul_assoc N (2 * j * (j + 1) * M) (N ^ j),
              Nat.mul_comm N (2 * j * (j + 1) * M), Nat.mul_assoc]
        rw [Nat.mul_add, eL, eR] at hm
        exact hm
      have hPoly : (4 * j + 4) * M * N ^ (j + 1) + 2 * j * (j + 1) * M * N ^ (j + 1) =
          2 * (j + 1) * (j + 2) * M * N ^ (j + 1) := by
        have hc : 4 * j + 4 + 2 * j * (j + 1) = 2 * (j + 1) * (j + 2) := by
          simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.mul_assoc]; omega
        rw [← Nat.add_mul, ← Nat.add_mul, hc]
      calc N ^ (j + 2)
        _ ≤ N * (N * β) + 2 * j * (j + 1) * M * N ^ (j + 1) := hMulLo
        _ = N * β' + 2 * M * N * (α + β) + 2 * j * (j + 1) * M * N ^ (j + 1) := by rw [← hIdN]
        _ ≤ N * β' + (4 * j + 4) * M * N ^ (j + 1) + 2 * j * (j + 1) * M * N ^ (j + 1) :=
          Nat.add_le_add_right (Nat.add_le_add_left hLossLe (N * β')) _
        _ = N * β' + 2 * (j + 1) * (j + 2) * M * N ^ (j + 1) := by rw [Nat.add_assoc, hPoly]
    have h2α'_ge : (j + 2) * N ^ (j + 1) ≤ 2 * α' := by
      have p1 : (N - 2 * M) * ((j + 1) * N ^ j) ≤ (N - 2 * M) * (2 * α) :=
        Nat.mul_le_mul_left (N - 2 * M) hαLo
      have p2 : 2 * (N - M) * N ^ j ≤ 2 * (N - M) * (2 * β) :=
        Nat.mul_le_mul_left (2 * (N - M)) h2β_ge
      have h2α'Eq : 2 * α' = (N - 2 * M) * (2 * α) + 2 * (N - M) * (2 * β) := by
        dsimp only [α']
        rw [Nat.mul_add, ← Nat.mul_assoc 2 (N - 2 * M) α, Nat.mul_comm 2 (N - 2 * M), Nat.mul_assoc,
            ← Nat.mul_assoc 2 (2 * (N - M)) β, Nat.mul_comm 2 (2 * (N - M)), Nat.mul_assoc]
      have hBound2j4 : 2 * M * (j + 1) + 2 * M ≤ N := by
        have hRearr : 2 * M * (j + 1) + 2 * M = (2 * j + 4) * M := by
          rw [Nat.mul_comm (2 * M) (j + 1), ← Nat.mul_assoc (j + 1) 2 M,
              Nat.mul_comm (j + 1) 2]
          have : 2 * (j + 1) * M + 2 * M = (2 * (j + 1) + 2) * M := (Nat.add_mul _ _ M).symm
          rw [this]; exact congrArg (· * M) (by omega)
        have hCoef : 2 * j + 4 ≤ 4 * (j + 1) * (j + 2) := by
          simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.mul_assoc]; omega
        rw [hRearr]
        exact Nat.le_trans (Nat.mul_le_mul_right M hCoef) hStep4
      have hLinear : (j + 2) * N ≤ (N - 2 * M) * (j + 1) + 2 * (N - M) := by
        have u1 : (N - 2 * M) * (j + 1) + 2 * M * (j + 1) = N * (j + 1) := by
          rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
        have u2 : 2 * (N - M) + 2 * M = 2 * N := by
          rw [← Nat.mul_add, Nat.sub_add_cancel (by omega)]
        have u3 : (j + 2) * N + N = N * (j + 1) + 2 * N := by
          rw [Nat.mul_comm N (j + 1), ← Nat.add_mul (j + 1) 2 N, ← Nat.succ_mul (j + 2) N]
        omega
      calc (j + 2) * N ^ (j + 1)
        _ = (j + 2) * N * N ^ j := by
          rw [Nat.pow_succ N j, Nat.mul_comm (N ^ j) N, Nat.mul_assoc]
        _ ≤ ((N - 2 * M) * (j + 1) + 2 * (N - M)) * N ^ j :=
          Nat.mul_le_mul_right (N ^ j) hLinear
        _ = (N - 2 * M) * ((j + 1) * N ^ j) + 2 * (N - M) * N ^ j := by
          rw [Nat.add_mul, Nat.mul_assoc]
        _ ≤ (N - 2 * M) * (2 * α) + 2 * (N - M) * (2 * β) := Nat.add_le_add p1 p2
        _ = 2 * α' := h2α'Eq.symm
    exact ⟨hα'_hi, hβ'_hi, hβ'_lo, h2α'_ge⟩

private theorem untweakedGroverAdv_state_eq (N M q : Nat)
    (hM_pos : 1 ≤ M) (hMN : M ≤ N) (hRegime : 4 * q * (q + 1) * M ≤ N) (hN : 0 < N) :
    ∀ (j : Nat) (hj : j ≤ q),
      advStateAt (untweakedGroverAdv N M q hN) (untweakedMultiTargetOracle N M) j hj =
        groverTemplateState N M
          (Int.ofNat (untweakedGroverAmpsNat N M j).1)
          (Int.ofNat (untweakedGroverAmpsNat N M j).2)
  | 0, _ => rfl
  | j + 1, hj => by
    unfold advStateAt
    dsimp only
    rw [untweakedGroverAdv_state_eq N M q hM_pos hMN hRegime hN j (Nat.le_of_succ_le hj)]
    simp only [untweakedGroverAdv]
    obtain ⟨hαHi, hβHi, hβLo, _⟩ :=
      untweakedGroverAmpsNat_bounds N M q hM_pos hRegime j (Nat.le_of_succ_le hj)
    let αNat := (untweakedGroverAmpsNat N M j).1
    let βNat := (untweakedGroverAmpsNat N M j).2
    let α := Int.ofNat αNat
    let β := Int.ofNat βNat
    have hStepProd : (j + 1) * (j + 2) ≤ q * (q + 1) :=
      Nat.mul_le_mul hj (Nat.add_le_add_right hj 1)
    have hStep4 : 4 * (j + 1) * (j + 2) * M ≤ N := by
      have hm := Nat.mul_le_mul_right M (Nat.mul_le_mul_left 4 hStepProd)
      simp only [Nat.mul_assoc] at hm hRegime ⊢
      exact Nat.le_trans hm hRegime
    have hN_ge_8M : 8 * M ≤ N := by
      have h8 : 8 ≤ 4 * (j + 1) * (j + 2) := by
        simp only [Nat.mul_add, Nat.add_mul]; omega
      exact Nat.le_trans (Nat.mul_le_mul_right M h8) hStep4
    have hSub : 2 * M * αNat ≤ (N - 2 * M) * βNat :=
      grover_sub_guard hM_pos hStep4 hαHi hβHi hβLo
    have hIntN2M : Int.ofNat (N - 2 * M) = Int.ofNat N - 2 * Int.ofNat M := by
      have h1 := congrArg Int.ofNat (Nat.sub_add_cancel (by omega : 2 * M ≤ N))
      rw [ofNat_add_eq, ofNat_mul_eq] at h1
      have h2 : Int.ofNat 2 = 2 := rfl
      rw [h2] at h1; omega
    have hIntα' : Int.ofNat ((N - 2 * M) * αNat + 2 * (N - M) * βNat) =
        (Int.ofNat N - 2 * Int.ofNat M) * α + 2 * Int.ofNat (N - M) * β := by
      rw [ofNat_add_eq, ofNat_mul_eq, ofNat_mul_eq, ofNat_mul_eq 2, hIntN2M]
      rfl
    have hIntβ' : Int.ofNat ((N - 2 * M) * βNat - 2 * M * αNat) =
        (Int.ofNat N - 2 * Int.ofNat M) * β - 2 * Int.ofNat M * α := by
      have h1 := congrArg Int.ofNat (Nat.sub_add_cancel hSub)
      rw [ofNat_add_eq, ofNat_mul_eq, ofNat_mul_eq, ofNat_mul_eq, hIntN2M] at h1
      have h2 : Int.ofNat 2 = 2 := rfl
      rw [h2] at h1
      dsimp only [α, β]
      omega
    have hOracle : oracleXor (untweakedMultiTargetOracle N M) (groverTemplateState N M α β) =
        groverTemplateState N M (-α) β := by
      funext x y _
      unfold oracleXor untweakedMultiTargetOracle groverTemplateState
      rcases y with ⟨yv, hyv⟩
      have hCasesY : yv = 0 ∨ yv = 1 := by omega
      have hx0 : (xorFin (⟨0, by decide⟩ : Fin (2 ^ 1)) 1#1).1 = 1 := rfl
      have hx1 : (xorFin (⟨1, by decide⟩ : Fin (2 ^ 1)) 1#1).1 = 0 := rfl
      have hz0 : (xorFin (⟨0, by decide⟩ : Fin (2 ^ 1)) 0#1).1 = 0 := rfl
      have hz1 : (xorFin (⟨1, by decide⟩ : Fin (2 ^ 1)) 0#1).1 = 1 := rfl
      by_cases hxM : x.1 < M
      · rcases hCasesY with rfl | rfl
        · simp only [hxM, ↓reduceIte, hx0]; rfl
        · simp only [hxM, ↓reduceIte, hx1]; ext <;> dsimp <;> omega
      · rcases hCasesY with rfl | rfl
        · simp only [hxM, ↓reduceIte, hz0]
        · simp only [hxM, ↓reduceIte, hz1]
    rw [hOracle]
    funext x y _
    unfold groverDiffusion groverTemplateState untweakedGroverAmpsNat
    dsimp only
    rw [hIntα', hIntβ']
    have hSumRe : ∀ (K : Nat) (f : Fin K → GaussInt),
        (finGaussSum K f).re = finIntSum K (fun z => (f z).re) := by
      intro K; induction K with
      | zero => intros; rfl
      | succ k ih => intro f; simp only [finGaussSum, finIntSum, GaussInt.add, ih]
    have hSumIm0 : ∀ (K : Nat) (f : Fin K → Int),
        (finGaussSum K (fun z => (⟨f z, 0⟩ : GaussInt))).im = 0 := by
      intro K; induction K with
      | zero => intros; rfl
      | succ k ih => intro f; simp only [finGaussSum, GaussInt.add, ih]; omega
    have hSubEqβ : Int.ofNat (N - M) * β = Int.ofNat N * β - Int.ofNat M * β := by
      have hAdd : (N - M) + M = N := Nat.sub_add_cancel hMN
      have h1 := congrArg (fun k => Int.ofNat k * β) hAdd
      rw [ofNat_add_eq, Int.add_mul] at h1
      omega
    have hPushNeg : (fun z : Fin N => -(if z.1 < M then -α else β)) =
        (fun z : Fin N => if z.1 < M then α else -β) := by
      funext z; by_cases h : z.1 < M <;> simp only [h, ↓reduceIte, Int.neg_neg]
    have hLinPos :
        2 * (Int.ofNat M * (-α) + Int.ofNat (N - M) * β) - Int.ofNat N * (-α) =
        (Int.ofNat N - 2 * Int.ofNat M) * α + 2 * Int.ofNat (N - M) * β := by
      rw [Int.mul_neg (Int.ofNat M) α, Int.mul_neg (Int.ofNat N) α,
          Int.sub_mul, Int.mul_assoc 2 (Int.ofNat M) α,
          Int.mul_assoc 2 (Int.ofNat (N - M)) β, Int.mul_add, Int.mul_neg]
      omega
    have hLinNeg :
        2 * (Int.ofNat M * (-α) + Int.ofNat (N - M) * β) - Int.ofNat N * β =
        (Int.ofNat N - 2 * Int.ofNat M) * β - 2 * Int.ofNat M * α := by
      rw [Int.mul_neg (Int.ofNat M) α, hSubEqβ,
          Int.sub_mul, Int.mul_assoc 2 (Int.ofNat M) β, Int.mul_assoc 2 (Int.ofNat M) α,
          Int.mul_add, Int.mul_neg, Int.mul_sub]
      omega
    have hLinPos1 :
        2 * (Int.ofNat M * α + Int.ofNat (N - M) * (-β)) - Int.ofNat N * α =
        -((Int.ofNat N - 2 * Int.ofNat M) * α + 2 * Int.ofNat (N - M) * β) := by
      rw [Int.mul_neg (Int.ofNat (N - M)) β,
          Int.sub_mul, Int.mul_assoc 2 (Int.ofNat M) α,
          Int.mul_assoc 2 (Int.ofNat (N - M)) β, Int.mul_add, Int.mul_neg]
      omega
    have hLinNeg1 :
        2 * (Int.ofNat M * α + Int.ofNat (N - M) * (-β)) - Int.ofNat N * (-β) =
        -((Int.ofNat N - 2 * Int.ofNat M) * β - 2 * Int.ofNat M * α) := by
      rw [Int.mul_neg (Int.ofNat (N - M)) β, Int.mul_neg (Int.ofNat N) β, hSubEqβ,
          Int.sub_mul, Int.mul_assoc 2 (Int.ofNat M) β, Int.mul_assoc 2 (Int.ofNat M) α,
          Int.mul_add, Int.mul_neg, Int.mul_sub]
      omega
    rcases y with ⟨yv, hyv⟩
    have hCasesY : yv = 0 ∨ yv = 1 := by omega
    ext
    · dsimp only [GaussInt.sub, GaussInt.scaleInt]
      rw [hSumRe]
      rcases hCasesY with rfl | rfl
      · simp only [beq_self_eq_true, ↓reduceIte, finIntSum_prefix_const N M hMN (-α) β]
        by_cases hxM : x.1 < M <;> simp only [hxM, ↓reduceIte]
        · exact hLinPos
        · exact hLinNeg
      · have h10 : ((1 : Nat) == 0) = false := rfl
        simp only [h10, Bool.false_eq_true, ↓reduceIte]
        rw [hPushNeg, finIntSum_prefix_const N M hMN α (-β)]
        by_cases hxM : x.1 < M <;> simp only [hxM, ↓reduceIte, Int.neg_neg]
        · exact hLinPos1
        · exact hLinNeg1
    · dsimp only [GaussInt.sub, GaussInt.scaleInt]
      rw [hSumIm0]
      omega

private theorem prefixScale_untweakedGrover (N M q : Nat) (hN : 0 < N) :
    ∀ (j : Nat) (hj : j ≤ q),
      prefixScale (untweakedGroverAdv N M q hN) j hj = N ^ (2 * j)
  | 0, _ => by simp [prefixScale]
  | j + 1, hj => by
    unfold prefixScale
    rw [prefixScale_untweakedGrover N M q hN j (Nat.le_of_succ_le hj)]
    simp only [untweakedGroverAdv, groverDiffusion]
    rw [show 2 * (j + 1) = 2 * j + 2 by omega, Nat.pow_add, Nat.mul_comm]

/-- **Constructive `q`-Query Unitary Multi-Target Grover Lower Bound
    (`untweaked_multi_target_grover_lower_bound`)**:
    When `M` targets share a single un-tweaked function `untweakedMultiTargetOracle N M`
    (`1 ≤ M`, `M ≤ N`, `4 * q * (q + 1) * M ≤ N`), the explicit `q`-query unitary Grover circuit
    `untweakedGroverAdv N M q` achieves Born success probability `≥ M * (q + 1) ^ 2 / (4 * N)` —
    exhibiting genuine linear `M` amplification (`Ω(M · q^2 / N)`). -/
theorem untweaked_multi_target_grover_lower_bound
    (N M q : Nat) (hM_pos : 1 ≤ M) (hMN : M ≤ N) (hRegime : 4 * q * (q + 1) * M ≤ N) :
    let hN : 0 < N := Nat.lt_of_lt_of_le (Nat.zero_lt_of_ne_zero (by omega)) hMN
    let A := untweakedGroverAdv N M q hN
    let H := untweakedMultiTargetOracle N M
    RatBound.le
      ⟨M * (q + 1) ^ 2, 4 * N, Nat.mul_pos (by decide) hN⟩
      (QVec.bornProb (fun x => decide (x.1 < M)) (runQuantumAdv A H)
        (runQuantumAdv_normSq_pos A H)) := by
  let hN : 0 < N := Nat.lt_of_lt_of_le (Nat.zero_lt_of_ne_zero (by omega)) hMN
  let A := untweakedGroverAdv N M q hN
  let H := untweakedMultiTargetOracle N M
  obtain ⟨_, _, _, h2αGe⟩ := untweakedGroverAmpsNat_bounds N M q hM_pos hRegime q (Nat.le_refl q)
  let αq := (untweakedGroverAmpsNat N M q).1
  let βq := (untweakedGroverAmpsNat N M q).2
  change (q + 1) * N ^ q ≤ 2 * αq at h2αGe
  have hState : runQuantumAdv A H = groverTemplateState N M (Int.ofNat αq) (Int.ofNat βq) :=
    untweakedGroverAdv_state_eq N M q hM_pos hMN hRegime hN q (Nat.le_refl q)
  have hInitNorm : QVec.stateNormSq A.init = 2 * N := by
    have hEach : ∀ x : Fin N, QVec.queryWeight (groverTemplateState N M 1 1) x = 2 := by
      intro x; unfold QVec.queryWeight groverTemplateState
      simp only [qsum]
      by_cases hx : x.1 < M <;> simp [hx, GaussInt.normSq]
    unfold QVec.stateNormSq
    change qsum N (fun x => QVec.queryWeight (groverTemplateState N M 1 1) x) = 2 * N
    rw [qsum_congr hEach, qsum_const, Nat.mul_comm]
  have hDenom : QVec.stateNormSq (runQuantumAdv A H) = 2 * N ^ (2 * q + 1) := by
    rw [runQuantumAdv_normSq, prefixScale_untweakedGrover N M q hN q (Nat.le_refl q), hInitNorm]
    rw [Nat.pow_succ, ← Nat.mul_assoc (N ^ (2 * q)) 2 N, Nat.mul_comm (N ^ (2 * q)) 2, Nat.mul_assoc]
  have hNum : QVec.measureNormSq (fun x => decide (x.1 < M)) (runQuantumAdv A H) =
      M * (2 * (αq * αq)) := by
    rw [hState]
    unfold QVec.measureNormSq QVec.queryMassOn
    have hMarkEach : ∀ x : Fin N,
        (if decide (x.1 < M) = true then
           QVec.queryWeight (groverTemplateState N M (Int.ofNat αq) (Int.ofNat βq)) x
         else 0) =
        (if x.1 < M then 2 * (αq * αq) else 0) := by
      intro x
      by_cases hx : x.1 < M
      · have h00 : ((0 : Nat) == 0) = true := rfl
        have h10 : ((1 : Nat) == 0) = false := rfl
        have hAbsNeg : (-Int.ofNat αq).natAbs = αq := Int.natAbs_neg (Int.ofNat αq)
        have hAbsPos : (Int.ofNat αq).natAbs = αq := rfl
        simp only [hx, decide_true, ↓reduceIte, QVec.queryWeight, groverTemplateState, qsum,
          Nat.zero_add, h00, h10, Bool.false_eq_true, GaussInt.normSq, hAbsNeg, hAbsPos, Nat.add_zero]
        have h0 : Int.natAbs 0 = 0 := rfl
        rw [h0]
        omega
      · simp [hx]
    rw [qsum_congr hMarkEach, qsum_prefix_const N M hMN (2 * (αq * αq)) 0,
        Nat.mul_zero, Nat.add_zero]
  have hSq4 : ((q + 1) * N ^ q) ^ 2 ≤ (2 * αq) ^ 2 := Nat.pow_le_pow_left h2αGe 2
  have hSqExpandL : ((q + 1) * N ^ q) ^ 2 = (q + 1) ^ 2 * N ^ (2 * q) := by
    rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm q 2]
  have hSqExpandR : (2 * αq) ^ 2 = 4 * (αq * αq) := by
    rw [Nat.mul_pow, Nat.pow_two αq]
  rw [hSqExpandL, hSqExpandR] at hSq4
  unfold QVec.bornProb RatBound.le
  dsimp only
  rw [hNum, hDenom]
  have hLhs : M * (q + 1) ^ 2 * (2 * N ^ (2 * q + 1)) =
      2 * M * N * ((q + 1) ^ 2 * N ^ (2 * q)) := by
    rw [Nat.pow_succ N (2 * q)]
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hRhs : M * (2 * (αq * αq)) * (4 * N) =
      2 * M * N * (4 * (αq * αq)) := by
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [hLhs, hRhs]
  exact Nat.mul_le_mul_left (2 * M * N) hSq4

private def groverPq256LowerBound : RatBound :=
  ⟨2 ^ 64 * (2 ^ 60 + 1) ^ 2, 4 * 2 ^ 256, by decide⟩

/-- `#tooth`: Un-tweaked `M`-target search (`M = 2 ^ 64` targets under a single function
    `untweakedMultiTargetOracle (2 ^ 256) (2 ^ 64)` at `q = 2 ^ 60` unitary Grover queries)
    suffers linear `M` amplification (`bornProb > 2^-74`, breaking 124-bit and 128-bit security
    and strictly exceeding `hrs16SuperpositionBound 256 (2 ^ 60)`). -/
theorem tooth_untweaked_multi_target_grover_linear_M_loss :
    ∃ A : QuantumAdv (2 ^ 256) 1 1 (2 ^ 60),
      let H := untweakedMultiTargetOracle (2 ^ 256) (2 ^ 64)
      let winProb := QVec.bornProb (fun x => decide (x.1 < 2 ^ 64))
        (runQuantumAdv A H) (runQuantumAdv_normSq_pos A H)
      RatBound.lt (hrs16SuperpositionBound 256 (2 ^ 60)) winProb ∧
      ¬ atLeastBits 124 winProb ∧
      ¬ atLeastBits 74 winProb := by
  have hN : 0 < 2 ^ 256 := Nat.two_pow_pos 256
  have hGrover := untweaked_multi_target_grover_lower_bound (2 ^ 256) (2 ^ 64) (2 ^ 60)
    (by decide) (by decide) (by decide)
  let A := untweakedGroverAdv (2 ^ 256) (2 ^ 64) (2 ^ 60) hN
  let H := untweakedMultiTargetOracle (2 ^ 256) (2 ^ 64)
  let winProb := QVec.bornProb (fun x => decide (x.1 < 2 ^ 64))
    (runQuantumAdv A H) (runQuantumAdv_normSq_pos A H)
  have hLoLe : RatBound.le groverPq256LowerBound winProb := hGrover
  refine ⟨A, ?_, ?_, ?_⟩
  · have hStrict : RatBound.lt (hrs16SuperpositionBound 256 (2 ^ 60)) groverPq256LowerBound := by
      unfold RatBound.lt hrs16SuperpositionBound groverPq256LowerBound; decide
    unfold RatBound.lt at hStrict ⊢
    unfold RatBound.le at hLoLe
    have h1 := Nat.mul_lt_mul_of_pos_right hStrict winProb.h_pos
    have hCancel : (hrs16SuperpositionBound 256 (2 ^ 60)).num * groverPq256LowerBound.den * winProb.den <
        groverPq256LowerBound.num * winProb.den * (hrs16SuperpositionBound 256 (2 ^ 60)).den := by
      calc (hrs16SuperpositionBound 256 (2 ^ 60)).num * groverPq256LowerBound.den * winProb.den
        _ < groverPq256LowerBound.num * (hrs16SuperpositionBound 256 (2 ^ 60)).den * winProb.den := h1
        _ = groverPq256LowerBound.num * winProb.den * (hrs16SuperpositionBound 256 (2 ^ 60)).den := by
          rw [Nat.mul_assoc groverPq256LowerBound.num, Nat.mul_comm _ winProb.den,
              ← Nat.mul_assoc groverPq256LowerBound.num]
    have hChain : (hrs16SuperpositionBound 256 (2 ^ 60)).num * (groverPq256LowerBound.den * winProb.den) <
        winProb.num * (groverPq256LowerBound.den * (hrs16SuperpositionBound 256 (2 ^ 60)).den) := by
      have hMid : groverPq256LowerBound.num * winProb.den * (hrs16SuperpositionBound 256 (2 ^ 60)).den ≤
          winProb.num * groverPq256LowerBound.den * (hrs16SuperpositionBound 256 (2 ^ 60)).den :=
        Nat.mul_le_mul_right _ hLoLe
      have hLt := Nat.lt_of_lt_of_le hCancel hMid
      simpa only [Nat.mul_assoc] using hLt
    have hRearrL : (hrs16SuperpositionBound 256 (2 ^ 60)).num * (groverPq256LowerBound.den * winProb.den) =
        ((hrs16SuperpositionBound 256 (2 ^ 60)).num * winProb.den) * groverPq256LowerBound.den := by
      rw [← Nat.mul_assoc, Nat.mul_right_comm]
    have hRearrR : winProb.num * (groverPq256LowerBound.den * (hrs16SuperpositionBound 256 (2 ^ 60)).den) =
        (winProb.num * (hrs16SuperpositionBound 256 (2 ^ 60)).den) * groverPq256LowerBound.den := by
      rw [← Nat.mul_assoc, Nat.mul_right_comm]
    rw [hRearrL, hRearrR] at hChain
    exact match Nat.lt_or_ge
        ((hrs16SuperpositionBound 256 (2 ^ 60)).num * winProb.den)
        (winProb.num * (hrs16SuperpositionBound 256 (2 ^ 60)).den) with
      | .inl hlt => hlt
      | .inr hge => False.elim (Nat.not_lt_of_ge (Nat.mul_le_mul_right _ hge) hChain)
  · intro h124
    have hLo124 : atLeastBits 124 groverPq256LowerBound := atLeastBits_of_le hLoLe h124
    exact (by decide : ¬ atLeastBits 124 groverPq256LowerBound) hLo124
  · intro h74
    have hLo74 : atLeastBits 74 groverPq256LowerBound := atLeastBits_of_le hLoLe h74
    exact (by decide : ¬ atLeastBits 74 groverPq256LowerBound) hLo74

theorem witness_hrs16_superposition_pq256 :
    ∃ (A : QuantumAdv (2 ^ 64 * 2 ^ 256) 1 1 (2 ^ 64))
      (encode : Fin (2 ^ 64) → BitVec 256 → BitVec 256)
      (targets : Fin (2 ^ 64) → BitVec 256),
      0 < QVec.stateNormSq A.init ∧
      (∀ t : Fin (2 ^ 64), Function.Injective (encode t)) ∧
      (∀ t : Fin (2 ^ 64), fiberCard 256 (encode t) (targets t) ≤ 1) := by
  have hN : 0 < 2 ^ 64 * 2 ^ 256 := Nat.mul_pos (Nat.two_pow_pos 64) (Nat.two_pow_pos 256)
  let A₀ := untweakedGroverAdv (2 ^ 64 * 2 ^ 256) 1 (2 ^ 64) hN
  refine ⟨A₀, (fun _ x => x), (fun _ => 0#256), A₀.h_init_pos, (fun _ _ _ h => h), ?_⟩
  intro _
  exact fiberCard_le_one_of_injective 256 (fun x => x) (fun _ _ h => h) 0#256

#tooth_pair Qsag.hrs16_superposition_multi_tweak_bound vs Qsag.tooth_untweaked_multi_target_grover_linear_M_loss
#tooth_pair Qsag.hrs16_superposition_multi_tweak_pq256_bound vs Qsag.tooth_untweaked_multi_target_grover_linear_M_loss
#tooth_pair Qsag.densePcgV3_hrs16_superposition_141 vs Qsag.tooth_untweaked_multi_target_grover_linear_M_loss
#verify_inhabited Qsag.hrs16_superposition_multi_tweak_pq256_bound Qsag.witness_hrs16_superposition_pq256
#verify_inhabited Qsag.hrs16_superposition_multi_tweak_bound Qsag.witness_hrs16_superposition_pq256

end Qsag
