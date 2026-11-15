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

public import Qsag.Tactic.Prelude
public import Qsag.Oracle.Qrom
public import Qsag.Tactic.AssuranceKit
public import Qsag.Math.Goldilocks
import all Qsag.Math.Goldilocks
public import Qsag.Protocol.Aggregation.UcGames
import all Qsag.Protocol.Aggregation.UcGames
public import Qsag.Coding.Cwyz26
import all Qsag.Coding.Cwyz26

public import Qsag.Math.QuarticExt4

public import Qsag.Spec.Bounds
public section
namespace Qsag

attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd

set_option autoImplicit false
set_option exponentiation.threshold 2048

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
/-- Quadratic extension cardinality `p^2` (`< 2^128`). Named apart from `Qsag.goldilocksExt2Card`
    in `ThresholdMpc.lean` (`p * p`, the index type of its field enumeration): the library root and
    `CorduroyAndHemAirCompleteness` import both modules. -/
def goldilocksQuadraticExtCard : Nat := goldilocksPrime ^ 2

theorem goldilocksExt4Card_pos : 0 < goldilocksExt4Card := by
  unfold goldilocksExt4Card goldilocksPrime; decide

theorem goldilocksQuadraticExtCard_pos : 0 < goldilocksQuadraticExtCard := by
  unfold goldilocksQuadraticExtCard goldilocksPrime; decide

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
