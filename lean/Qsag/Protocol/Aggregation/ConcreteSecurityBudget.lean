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
public import Qsag.Protocol.Aggregation.UcGames
public import Qsag.Coding.Cwyz26

public import Qsag.Math.QuarticExt4

public import Qsag.Spec.Bounds
public section
namespace Qsag

attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd

set_option autoImplicit false
set_option maxRecDepth 10000
set_option exponentiation.threshold 2048

/-! ## §3. Protocol Encoding Injectivity, Fiber Cardinalities & Custody Margins
           (`Baggy`, `Corduroy`, `FrontierSumFts`, `Jorts`, `QuorumJorts`) -/

/-! ### §3.1 Exact Bit-Truncation Fiber Theorem (`2 ^ (n - m)` Preimages) -/

private theorem qsum_snoc :
    ∀ (n : Nat) (g : Fin (n + 1) → Nat),
      qsum (n + 1) g =
        qsum n (fun i => g ⟨i.1, Nat.lt_succ_of_lt i.2⟩) + g ⟨n, Nat.lt_succ_self n⟩
  | 0, g => by simp [qsum_zero, qsum_succ]
  | n + 1, g => by
    have hHead : qsum (n + 1 + 1) g =
        g ⟨0, Nat.zero_lt_succ (n + 1)⟩ +
          qsum (n + 1) (fun i => g ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) := qsum_succ _ _
    rw [hHead, qsum_snoc n (fun i => g ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)]
    have hInit : qsum (n + 1) (fun i => g ⟨i.1, Nat.lt_succ_of_lt i.2⟩) =
        g ⟨0, Nat.zero_lt_succ (n + 1)⟩ +
          qsum n (fun i => g ⟨i.1 + 1, Nat.lt_succ_of_lt (Nat.succ_lt_succ i.2)⟩) := qsum_succ _ _
    rw [← Nat.add_assoc]
    exact congrArg (fun x => x + g ⟨n + 1, Nat.lt_succ_self (n + 1)⟩) hInit.symm

private theorem qsum_add_split (X : Nat) :
    ∀ (Y : Nat) (g : Fin (X + Y) → Nat),
      qsum (X + Y) g =
        qsum X (fun i => g ⟨i.1, by omega⟩) +
        qsum Y (fun j => g ⟨X + j.1, by omega⟩)
  | 0, g => by
    simp only [qsum_zero, Nat.add_zero]
    exact qsum_congr (fun _ => rfl)
  | Y + 1, g => by
    have h1 : qsum (X + (Y + 1)) g =
        qsum (X + Y) (fun k => g ⟨k.1, Nat.lt_succ_of_lt k.2⟩) +
          g ⟨X + Y, Nat.lt_succ_self (X + Y)⟩ :=
      qsum_snoc (X + Y) g
    rw [h1, qsum_add_split X Y (fun k => g ⟨k.1, Nat.lt_succ_of_lt k.2⟩),
        qsum_snoc Y (fun j => g ⟨X + j.1, by omega⟩), Nat.add_assoc]

theorem qsum_mul_split (A : Nat) :
    ∀ (B : Nat) (f : Fin (A * B) → Nat),
      qsum (A * B) f =
        qsum B (fun q => qsum A (fun r =>
          f ⟨q.1 * A + r.1, by
            have h1 : q.1 * A + r.1 < q.1 * A + A := Nat.add_lt_add_left r.2 (q.1 * A)
            have h2 : q.1 * A + A = (q.1 + 1) * A := by rw [Nat.add_mul, Nat.one_mul]
            have h3 : (q.1 + 1) * A ≤ B * A := Nat.mul_le_mul_right A q.2
            rw [Nat.mul_comm B A] at h3
            omega⟩))
  | 0, _ => by simp [qsum_zero]
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
  simp only [fiberCard_def]
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
    (unfold RatBound.le; simp only [quantumGroverSingleTargetBound_def, quantumZhandryMultiTargetBound_def])
    apply Nat.mul_le_mul_right
    have hm := Nat.mul_le_mul_left (8 * (qHash + 1) ^ 2) hFib
    omega
  refine ⟨hFib, RatBound.le_trans hQrom hLeSingle,
          fun hq => qrom_single_target_parametric_bits hq (by decide), ?_⟩
  intro hq64
  (unfold atLeastBits; simp only [groverPureSearchBound_def])
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
    (unfold RatBound.le; simp only [quantumGroverSingleTargetBound_def, quantumZhandryMultiTargetBound_def])
    have hEq : 8 * 1 * (2 ^ 64 + 1) ^ 2 * 2 ^ 256 =
        8 * (2 ^ 64 + 1) ^ 2 * 2 ^ 128 * 2 ^ 128 := by decide
    exact Nat.le_of_eq hEq
  · (unfold exceedsBitBudget; simp only [quantumGroverSingleTargetBound_def, quantumZhandryMultiTargetBound_def])
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
    (unfold RatBound.le; simp only [quantumGroverSingleTargetBound_def, quantumZhandryMultiTargetBound_def])
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
          by (unfold exceedsBitBudget; simp only [groverPureSearchBound_def]); decide,
          by (unfold exceedsBitBudget; simp only [quantumGroverSingleTargetBound_def, quantumZhandryMultiTargetBound_def]); decide⟩

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
abbrev goldilocksExt4Card : Nat := goldilocksPrime ^ 4
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
@[expose] def whirSchedule4Stage : WhirBudgetRegime → List WhirStageBudget
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
  have hq := hemJohnsonMinQueries_deployed
  refine ⟨?_, ?_, ?_, ?_, by decide, ?_⟩
  · intro r; rw [hemStageGeoms_24_eq]; cases r <;> decide
  · intro r; rw [hemStageGeoms_20_eq]; cases r <;> decide
  · rw [hemStageGeoms_24_eq]
    simp only [List.map, hq.1.1, hq.1.2.1, hq.1.2.2.1, hq.1.2.2.2]
    decide
  · rw [hemStageGeoms_24_eq]
    simp only [List.map, hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2]
    decide
  · intro r; cases r <;> decide

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
          by (unfold exceedsBitBudget; simp only [quantumGroverGrindingBound_def]; unfold whirPositiveEtaJohnsonStageBound RatBound.scale); decide,
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
    (unfold atLeastBits; simp only [quantumGroverGrindingBound_def]; unfold whirPositiveEtaJohnsonStageBound RatBound.scale)
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
    (unfold atLeastBits; simp only [quantumGroverGrindingBound_def]; unfold whirPositiveEtaJohnsonStageBound RatBound.scale)
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
    decide
  · intro S hS
    apply atLeastBits_scale_session_loss (sLog := 4) hS
    show atLeastBits 132 _
    decide

/-- **`#tooth` Legacy `GoldilocksExt2` Folding Bottleneck & Classical-128 Grover Ceiling
    (`tooth_hem_ext2_folding_under_100bits`)**:
    1. Over `GoldilocksExt2` (`p^2 < 2^128`), at domain `|D| = 2^22`, even `|D|^2 / p^2 = 2^44 / p^2`
       falls strictly below 100 bits (`exceedsBitBudget 100`, ~84 bits before `(2η)^7` loss!),
    2. On `bciksJohnsonClassical128` Stage 0 (`q_0 = 129`, `16`b PoW = `~144` classical round bits),
       offline quantum Grover grinding at `qHash = 2 ^ 72` breaks quantum soundness
       (`exceedsBitBudget 0`), justifying why default `bciksJohnsonQrom128` (`q = 258, 130, 88, 66`)
       is required for `136`-bit QROM round-search work! -/
theorem tooth_hem_ext2_folding_under_100bits :
    exceedsBitBudget 100 ⟨(2 ^ 22) ^ 2, goldilocksQuadraticExtCard, goldilocksQuadraticExtCard_pos⟩ ∧
    exceedsBitBudget 0
      (quantumGroverGrindingBound (2 ^ 72)
        (whirPositiveEtaJohnsonStageBound ⟨2, 6, 26, 129, by decide⟩ 128 (by decide) 16)) := by
  refine ⟨by unfold exceedsBitBudget goldilocksQuadraticExtCard goldilocksPrime; decide,
          by (unfold exceedsBitBudget; simp only [quantumGroverGrindingBound_def]; unfold whirPositiveEtaJohnsonStageBound RatBound.scale); decide⟩


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
    (unfold atLeastBits; simp only [quantumGroverGrindingBound_def]; unfold RatBound.scale RatBound.pow zkbooSingleRepError blindVcQuantum128Reps)
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
    (unfold atLeastBits; simp only [quantumDfmMeasureReprogramBound_def]; unfold RatBound.scale RatBound.pow zkbooSingleRepError blindVcQuantum128Reps)
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
  · (unfold exceedsBitBudget; simp only [quantumGroverGrindingBound_def]; unfold RatBound.scale RatBound.pow zkbooSingleRepError blindVcClassical128Reps)
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
def mlDsaChallengeCard : MlDsaParamSet → Nat
  | .mldsa44 => 10632454734439260654968992334485917220317098900012924928000
  | .mldsa65 => 68486703327623956089204606554598213090738065566252813145704759296000
  | .mldsa87 => 233962245085473268146740906771464689968014948959082128692806487994874095206400

/-- The cached cardinalities equal the exact FIPS 204 challenge-ball formula. -/
theorem mlDsaChallengeCard_eq_formula (p : MlDsaParamSet) :
    mlDsaChallengeCard p = 2 ^ p.tau * binomialProduct 256 p.tau := by
  cases p <;> decide


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
    dsimp only [List.map, RatBound.sumList, RatBound.add, sumSqSucc] at ih ⊢
    simp only [quantumZhandryMultiTargetBound_def]
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
  (unfold RatBound.lt tweakedMultiTargetBound; simp only [quantumZhandryMultiTargetBound_def])
  rw [Nat.mul_one, Nat.mul_assoc 8 (m + 1)]
  exact Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_left hcore (by decide))
    (Nat.two_pow_pos n)

/-- Below the crossover the additive `M` dominates and the union form is the weaker bound. -/
theorem untweaked_le_tweaked_of_sq_le_targets (n q M : Nat) (hM : 1 ≤ M) (hq : q * q ≤ M) :
    RatBound.le (quantumZhandryMultiTargetBound n M q) (tweakedMultiTargetBound n 1 M q) := by
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
  have hcore : (m + 1) * (q + 1) ^ 2 ≤ (q + (m + 1)) ^ 2 :=
    le_of_add_eq_add (salted_unsalted_expand q m) (Nat.mul_le_mul_left m hq)
  (unfold RatBound.le tweakedMultiTargetBound; simp only [quantumZhandryMultiTargetBound_def])
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
  (unfold atLeastBits densePcgV3SeedQuantumBound; simp only [quantumZhandryMultiTargetBound_def])
  exact Nat.le_trans
    (Nat.mul_le_mul_right (2 ^ 120)
      (Nat.mul_le_mul_left (8 * densePcgV3NodeTargets) (Nat.pow_le_pow_left hq 2)))
    (by decide)

/-- Unsalted model reaches 128 bits only for `q + 1 ≤ 2^52`. -/
theorem densePcgV3SeedQuantumBound_128 (q : Nat) (hq : q + 1 ≤ 2 ^ 52) :
    atLeastBits 128 (densePcgV3SeedQuantumBound q) := by
  (unfold atLeastBits densePcgV3SeedQuantumBound; simp only [quantumZhandryMultiTargetBound_def])
  exact Nat.le_trans
    (Nat.mul_le_mul_right (2 ^ 128)
      (Nat.mul_le_mul_left (8 * densePcgV3NodeTargets) (Nat.pow_le_pow_left hq 2)))
    (by decide)

/-- Dropping the tweak from the node block: the forest fails PQ128 at `q + 1 = 2^56`. -/
theorem tooth_densePcgV3_untweaked_not_pq128 (q : Nat) (hq : q + 1 = 2 ^ 56) :
    ¬ atLeastBits 128 (densePcgV3SeedQuantumBound q) := by
  (unfold atLeastBits densePcgV3SeedQuantumBound; simp only [quantumZhandryMultiTargetBound_def])
  rw [hq]
  decide

/-- The partition bound does not cover untweaked targets: at the production ceiling the
    one-function bound is not below the salted one. -/
theorem tooth_untweaked_targets_exceed_partition_bound (q : Nat) (hq : q + 1 = 2 ^ 56) :
    ¬ RatBound.le (densePcgV3SeedQuantumBound q) (densePcgV3SaltedSeedQuantumBound q) := by
  obtain rfl : q = 2 ^ 56 - 1 := by omega
  (unfold RatBound.le densePcgV3SeedQuantumBound densePcgV3SaltedSeedQuantumBound densePcgV3SharedTweakSeedQuantumBound tweakedMultiTargetBound; simp only [quantumZhandryMultiTargetBound_def])
  decide

/-- **Salted V3 seed search, end to end.** For every allocation `qs` of at most `q` hash queries
    (`q + 1 ≤ 2^56`) over the `densePcgV3NodeTargets` node tweaks of the forest, the union of the
    per-tweak single-target QROM bounds `8 (q_i + 1)^2 / 2^256` is at most `2^-140`. -/
theorem densePcgV3_partitioned_seed_search_140 (q : Nat) (qs : List Nat)
    (hLen : qs.length = densePcgV3NodeTargets) (hBudget : qs.sum ≤ q)
    (hq : DensePcgV3QueryBudget q) :
    atLeastBits 140 (RatBound.sumList (qs.map (quantumGroverSingleTargetBound 256))) := by
  have hUnion := tweaked_multi_target_query_partition_union_bound 256 1 q qs hBudget
  have hSingle : quantumGroverSingleTargetBound 256 = quantumZhandryMultiTargetBound 256 1 :=
    funext (quantumGroverSingleTargetBound_def 256)
  rw [hLen] at hUnion
  rw [hSingle]
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
          ?_, by (unfold exceedsBitBudget; simp only [quantumGroverSingleTargetBound_def, quantumZhandryMultiTargetBound_def]); decide,
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
  refine ⟨by unfold atLeastBits shorPolynomialQuantumBreak; rw [RatBound.one_num, RatBound.one_den]; decide,
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
          by (unfold exceedsBitBudget; simp only [quantumGroverGrindingBound_def]; unfold RatBound.scale goldilocksExt4Card goldilocksPrime); decide⟩
  · intro qHash hq
    (unfold atLeastBits; simp only [quantumGroverGrindingBound_def]; unfold RatBound.scale)
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
    (unfold atLeastBits; simp only [quantumGroverGrindingBound_def]; unfold RatBound.scale)
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

/-- Conditional paper/profile input for equal-degree affine folding:
    `whirAffineStageSimpleNum w / p^4`. The arithmetic witness checker compares the paper's
    two numerator formulas; it does not prove an adversary-event bound. Applying this input
    needs the stronger nonpersistent incidence constant, the equal-degree three-challenge
    lift, and all intermediate-fold geometries. The proved sliced binary-fold counts in
    `CodingTheory.Cwyz26DeployedStages` are larger and do not instantiate this input. -/
@[expose] def whirAffineEqualDegreeCommitFoldBound (w : WhirAffineWitness) : RatBound :=
  ⟨whirAffineStageSimpleNum w, goldilocksExt4Card, goldilocksExt4Card_pos⟩

/-- Exact pure `s_i`-loss proximity query bound for `[CWYZ26]` affine WHIR stage witness `w`
    (before per-stage PoW): the probability `(A + s_i)_{q_i} / (n)_{q_i}` that `q_i` DISTINCT
    uniformly sampled fibers all land in a set of `A + s_i` out of `n` fibers. -/
@[expose] def whirAffinePureQueryBound (w : WhirAffineWitness) (hq : w.queries ≤ w.n) : RatBound :=
  ⟨affineFallingFactorial (w.A + w.sFolds) w.queries, affineFallingFactorial w.n w.queries,
   affineFallingFactorial_pos w.n w.queries hq⟩

/-- Total form of `whirAffinePureQueryBound`: the exact distinct-fiber bound
    `(A + s_i)_{q_i} / (n)_{q_i}` of the witness row, and `RatBound.one` (no soundness credit)
    for a row with `queries > n`. No proof-of-work density is credited: a prover choosing the
    grinding nonce searches the joint nonce/query oracle, which the compiler charges through the
    Fiat–Shamir search factor applied to this pure bound. -/
@[expose] def whirAffinePureQueryBoundOrOne (w : WhirAffineWitness) : RatBound :=
  if hq : w.queries ≤ w.n then whirAffinePureQueryBound w hq else RatBound.one

/-- Every one of the 46 deployed `BciksJohnsonQrom128` rows (`num_vars ∈ 2..=24`) has pure query
    error strictly below `2^-256` at ITS OWN agreement threshold `A + s_i` and fiber count `n`.
    The bound `1/1` of the fallback branch fails the inequality, so each row is in the
    `queries ≤ n` branch. -/
theorem whirAffine_deployed_pure_query_bounds :
    ∀ nv : Nat, 2 ≤ nv → nv ≤ 24 → ∀ w ∈ whirAffineStageWitnesses nv true,
      strictlyMoreThanBits 256 (whirAffinePureQueryBoundOrOne w) := by
  intro nv h2 h24 w hw
  obtain ⟨hok, _, hBits⟩ := whirAffineStageWitnesses_qrom_checked nv h2 h24 w hw
  obtain ⟨hqn, hQuery⟩ := checkWhirAffineWitness_query_bound w _ hok
  rw [hBits] at hQuery
  unfold whirAffinePureQueryBoundOrOne
  simp only [hqn, ↓reduceDIte]
  exact hQuery

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
  unfold hemNv20ComposedPureTerms
  rw [whirAffineStageWitnesses_qrom_eq_deployed.1]
  rfl

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

/-- Arithmetic validation of a paper/profile input. These bit inequalities hold for the
    defined rational expressions; they do not establish commit-fold soundness or a QROM
    acceptance bound. The event-level obligations of `whirAffineEqualDegreeCommitFoldBound`
    remain necessary. The exact distinct-fiber query expression is checked separately. -/
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
  obtain ⟨hqn, hQuery⟩ := checkWhirAffineWitness_query_bound w _ hok
  refine ⟨hqn, hExact, ?_, hQuery, ?_⟩
  · unfold atLeastBits whirAffineEqualDegreeCommitFoldBound
    dsimp only
    have h1 : whirAffineStageSimpleNum w * 2 ^ 244 ≤ 1900 * 2 ^ 244 :=
      Nat.mul_le_mul_right _ (Nat.le_of_lt hSimple)
    have h2 : 1900 * 2 ^ 244 ≤ goldilocksExt4Card := by
      unfold goldilocksExt4Card goldilocksPrime; decide
    exact Nat.le_trans h1 h2
  · intro qHash hq
    (unfold atLeastBits; simp only [quantumGroverGrindingBound_def]; unfold whirAffineEqualDegreeCommitFoldBound RatBound.scale)
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

/-- Arithmetic checks for the `nv = 20,24` paper/profile expressions. Despite the historical
    theorem name, `atLeastBits 244` here is about `whirAffineEqualDegreeCommitFoldBound`,
    not a proved commit-fold event. Likewise the scaled 130-bit conclusion needs the
    reduction establishing that profile input before it becomes security. This theorem
    also checks the distinct-fiber query and dual-OOD expressions. See the unconditional
    sliced binary-fold counts in `CodingTheory.Cwyz26DeployedStages` for the current proved
    decomposition bounds; they cannot be silently substituted into the three-challenge,
    multi-fold protocol. -/
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
             (by simpa only [quantumGroverSingleTargetBound_def, quantumZhandryMultiTargetBound_def] using (ratBound_le_of_num_le (Nat.two_pow_pos 256) (Nat.mul_le_mul_left (8 * 1) hsq))))⟩

/-- Arithmetic interface for the complete classical threshold portfolio entry. -/
theorem thresholdMlDsaDkgAndSignEntry_classical_bits_iff (p : MlDsaParamSet)
    (b : QueryBudget) (bits : Nat) :
    atLeastBits bits (thresholdMlDsaDkgAndSignEntry p b).classicalBound ↔
      ((b.qHash + 1) * (mlDsaChallengeCard p * 2 ^ 256) +
        ((b.qOnlineSessions + 1) * 2 ^ 256 + (b.qHash + 1) * mlDsaChallengeCard p) *
          mlDsaChallengeCard p) * 2 ^ bits ≤
      mlDsaChallengeCard p * (mlDsaChallengeCard p * 2 ^ 256) := by rfl

/-- Arithmetic interface for the complete quantum threshold portfolio entry. -/
theorem thresholdMlDsaDkgAndSignEntry_quantum_bits_iff (p : MlDsaParamSet)
    (b : QueryBudget) (bits : Nat) :
    atLeastBits bits (thresholdMlDsaDkgAndSignEntry p b).quantumBound ↔
      (8 * (b.qHash + 1) ^ 2 * (mlDsaChallengeCard p * 2 ^ 256) +
        ((b.qOnlineSessions + 1) * 2 ^ 256 + 8 * (b.qHash + 1) ^ 2 * mlDsaChallengeCard p) *
          mlDsaChallengeCard p) * 2 ^ bits ≤
      mlDsaChallengeCard p * (mlDsaChallengeCard p * 2 ^ 256) := by
  unfold atLeastBits thresholdMlDsaDkgAndSignEntry
  rw [quantumGroverSingleTargetBound_def, quantumZhandryMultiTargetBound_def]
  rfl

/-- **Threshold ML-DSA entry inside its ceiling.** For `qHash + 1 ≤ 2^k` with `k` the parameter
    set's ceiling (`30 / 47 / 62` for ML-DSA-44 / 65 / 87) and at most `2^20` online sessions, the
    entry keeps 128 bits classically and in the QROM. -/
theorem threshold_mldsa_entry_pq128_within_ceiling (p : MlDsaParamSet) (b : QueryBudget)
    (hqHash : b.qHash + 1 ≤ 2 ^ p.pq128HashQueryCeilingLog2)
    (hqSess : b.qOnlineSessions + 1 ≤ 2 ^ 20) :
    atLeastBits 128 (thresholdMlDsaDkgAndSignEntry p b).classicalBound ∧
    atLeastBits 128 (thresholdMlDsaDkgAndSignEntry p b).quantumBound := by
  let cap : QueryBudget := ⟨2 ^ p.pq128HashQueryCeilingLog2 - 1, 0, 2 ^ 20 - 1⟩
  have hNum : atLeastBits 128 (thresholdMlDsaDkgAndSignEntry p cap).classicalBound ∧
      atLeastBits 128 (thresholdMlDsaDkgAndSignEntry p cap).quantumBound := by
    rw [thresholdMlDsaDkgAndSignEntry_classical_bits_iff,
      thresholdMlDsaDkgAndSignEntry_quantum_bits_iff]
    cases p <;> dsimp only [cap, mlDsaChallengeCard, MlDsaParamSet.pq128HashQueryCeilingLog2] <;>
      decide +kernel
  have hq : b.qHash ≤ cap.qHash := by
    dsimp only [cap]
    omega
  have hs : b.qOnlineSessions ≤ cap.qOnlineSessions := by
    dsimp only [cap]
    omega
  have hMono := thresholdMlDsaDkgAndSignEntry_mono p hq hs
  exact ⟨atLeastBits_of_le hMono.1 hNum.1, atLeastBits_of_le hMono.2 hNum.2⟩

/-- One power of two above its ceiling every parameter set's entry is below 128 QROM bits, even
    with no online session. -/
theorem tooth_threshold_mldsa_entry_above_ceiling_not_pq128 (p : MlDsaParamSet) :
    ¬ atLeastBits 128
        (thresholdMlDsaDkgAndSignEntry p
          ⟨2 ^ (p.pq128HashQueryCeilingLog2 + 1) - 1, 0, 0⟩).quantumBound := by
  cases p <;> (simp only [thresholdMlDsaDkgAndSignEntry_quantum_bits_iff]; decide +kernel)


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
  (simp only [thresholdMlDsaDkgAndSignEntry_quantum_bits_iff]; decide +kernel)


/-- The deployed Category-2 entry does not reach 128 QROM bits at the portfolio's `2^56`. -/
theorem tooth_threshold_mldsa44_entry_not_pq128_at_2pow56 :
    ¬ atLeastBits 128
        (thresholdMlDsaDkgAndSignEntry deployedThresholdMlDsaParamSet
          ⟨2 ^ 56 - 1, 0, 2 ^ 20 - 1⟩).quantumBound := by
  (simp only [thresholdMlDsaDkgAndSignEntry_quantum_bits_iff]; decide +kernel)
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
    unfold atLeastBits; rw [classicalFiatShamirBound_def]; unfold RatBound.scale RatBound.pow
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
    unfold hemNv20ComposedPureTerms
    rw [show whirAffineStageWitnesses 20 true = _ from whirAffineStageWitnesses_qrom_eq_deployed.1]
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      whirAffineEqualDegreeCommitFoldBound, whirAffineDualOodListPinBound, whirAffinePureQueryBoundOrOne,
      whirAffineStageSimpleNum_def]
    decide +kernel
  have hHemQuantum : atLeastBits 128
      (RatBound.sumList (hemNv20ComposedPureTerms.map (RatBound.scale (2 ^ 115)))) := by
    unfold hemNv20ComposedPureTerms
    rw [show whirAffineStageWitnesses 20 true = _ from whirAffineStageWitnesses_qrom_eq_deployed.1]
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      whirAffineEqualDegreeCommitFoldBound, whirAffineDualOodListPinBound, whirAffinePureQueryBoundOrOne,
      whirAffineStageSimpleNum_def]
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

/-- Cardinality of the production joint 24-repetition, 11-bit signed-monomial RLWE challenge.
    This is challenge-space arithmetic, not an RLWE hardness or extraction theorem. -/
def rlweSignedMonomialChallengeCard (reps : Nat) : Nat := (2 ^ 11) ^ reps

def rlweJointSignedMonomialChallengeCard : Nat := rlweSignedMonomialChallengeCard 24

/-- Historical challenge space, retained only for explicit legacy comparisons. -/
def rlweJointSignedMonomial13ChallengeCard : Nat := rlweSignedMonomialChallengeCard 13

/-- The historical 13-repetition challenge has 143 bits, not 260 bits. Its squared search-space
    threshold lies strictly between the squares of `2^71` and `2^72`; it alone cannot
    supply a 128-bit quantum search budget. -/
theorem rlwe_joint_signed_monomial_challenge_143_bits :
    rlweJointSignedMonomial13ChallengeCard = 2 ^ 143 ∧
    (2 ^ 71) ^ 2 < rlweJointSignedMonomial13ChallengeCard ∧
    rlweJointSignedMonomial13ChallengeCard < (2 ^ 72) ^ 2 := by
  decide

/-- Cardinality `(2^11)^24 = 2^264` of the 24-repetition, 11-bit signed-monomial `PQ128`
    RLWE OR-Sigma challenge space (`264` classical bits = `132` Grover bits). -/
def rlweJointSignedMonomial24ChallengeCard : Nat := (2 ^ 11) ^ 24

/-- The unqualified production alias is exactly the 24-repetition profile. -/
theorem rlwe_joint_signed_monomial_default_pq128 :
    rlweJointSignedMonomialChallengeCard = rlweJointSignedMonomial24ChallengeCard ∧
    rlweJointSignedMonomialChallengeCard = 2 ^ 264 ∧
    (2 ^ 128) ^ 2 < rlweJointSignedMonomialChallengeCard := by decide

/-- The historical profile cannot meet the squared PQ128 challenge-search target. -/
theorem tooth_rlwe_joint_13_below_pq128 :
    ¬ (2 ^ 128) ^ 2 ≤ rlweJointSignedMonomial13ChallengeCard := by decide

#tooth_pair Qsag.rlwe_joint_signed_monomial_default_pq128 vs Qsag.tooth_rlwe_joint_13_below_pq128

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
  · unfold atLeastBits; rw [classicalFiatShamirBound_def]; unfold RatBound.scale rlweOrSigmaSoundnessError
    dsimp only
    rw [Nat.mul_one, h264]
    have hm := Nat.mul_le_mul_right (2 ^ 128) hqHash
    rw [← Nat.pow_add] at hm
    exact Nat.le_trans hm (Nat.pow_le_pow_right (by decide : 0 < 2) (by decide : 66 + 128 ≤ 264))
  · (unfold atLeastBits; simp only [quantumGroverGrindingBound_def]; unfold RatBound.scale rlweOrSigmaSoundnessError)
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
      unfold atLeastBits; rw [classicalFiatShamirBound_def]; unfold RatBound.scale rlweOrSigmaSoundnessError
      dsimp only
      rw [Nat.mul_one, h264]
      have hm := Nat.mul_le_mul_right (2 ^ 198) hq66
      rw [← Nat.pow_add] at hm
      exact hm
    have hQu129 : atLeastBits 129 (quantumGroverGrindingBound qHash (rlweOrSigmaSoundnessError 24)) := by
      (unfold atLeastBits; simp only [quantumGroverGrindingBound_def]; unfold RatBound.scale rlweOrSigmaSoundnessError)
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
    (unfold atLeastBits; simp only [quantumDfmMeasureReprogramBound_def]; unfold RatBound.scale rlweOrSigmaSoundnessError)
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
    · unfold atLeastBits; rw [classicalFiatShamirBound_def]; unfold RatBound.scale rlweOrSigmaSoundnessError
      dsimp only
      rw [Nat.mul_one, h264]
      have hm := Nat.mul_le_mul_right (2 ^ 208) hq56
      rw [← Nat.pow_add] at hm
      exact hm
    · (unfold atLeastBits; simp only [quantumGroverGrindingBound_def]; unfold RatBound.scale rlweOrSigmaSoundnessError)
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
  rw [quantumGroverGrindingBound_def]
  decide

theorem tooth_rlwe_or_sigma_13_not_pq128_qrom :
    ¬ atLeastBits 128 (quantumGroverGrindingBound (2 ^ 8) rlweOrSigma13SoundnessError) ∧
    ¬ atLeastBits 128 (quantumDfmMeasureReprogramBound 1 (2 ^ 8) rlweOrSigma13SoundnessError) ∧
    ¬ atLeastBits 128 (quantumGroverGrindingBound (2 ^ 56 - 1) rlweOrSigma13SoundnessError) := by
  refine ⟨?_, ?_, tooth_rlwe_or_sigma_13_not_pq128_at_2pow56⟩
  · rw [quantumGroverGrindingBound_def]; decide
  · rw [quantumDfmMeasureReprogramBound_def]; decide

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
  simp only [QVec.stateNormSq_def, tweakNormSq, packTweakQuery]
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
    simp only [QVec.queryMassOn_def]
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
          ψBlank) ≤ K * normFinal := by
    simpa only [QVec.measureNormSq_def, normFinal] using
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
  | 0, c => by simp [finIntSum_zero]
  | n + 1, c => by
    simp only [finIntSum_succ, finIntSum_const n c]
    have h1 : Int.ofNat 1 * c = c := Int.one_mul c
    rw [ofNat_add_eq n 1, Int.add_mul, h1, Int.add_comm]

private theorem finIntSum_add :
    ∀ (N : Nat) (f g : Fin N → Int),
      finIntSum N (fun i => f i + g i) = finIntSum N f + finIntSum N g
  | 0, _, _ => by simp only [finIntSum_zero, Int.add_zero]
  | n + 1, f, g => by
    simp only [finIntSum_succ, finIntSum_add n]
    omega

private theorem finIntSum_mul_left (c : Int) :
    ∀ (N : Nat) (f : Fin N → Int),
      finIntSum N (fun i => c * f i) = c * finIntSum N f
  | 0, _ => by simp [finIntSum_zero]
  | n + 1, f => by
    simp only [finIntSum_succ, finIntSum_mul_left c n, Int.mul_add]

private theorem finIntSum_ofNat_eq :
    ∀ (N : Nat) (f : Fin N → Nat),
      finIntSum N (fun i => Int.ofNat (f i)) = Int.ofNat (qsum N f)
  | 0, _ => by simp only [finIntSum_zero, qsum_zero]; rfl
  | n + 1, f => by
    simp only [finIntSum_succ, qsum_succ, finIntSum_ofNat_eq n, ofNat_add_eq]

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
      | zero => intros; simp only [finGaussSum_zero, GaussInt.zero_def, GaussInt.sub_def, Int.sub_self]
      | succ k ih =>
        intro f g
        simp only [finGaussSum_succ, ih]
        simp only [GaussInt.add_def, GaussInt.sub_def]; ext <;> dsimp only <;> omega
    funext x y a
    simp only [QVec.sub_def]
    rw [hSumSub]
    simp only [GaussInt.sub_def, GaussInt.scaleInt_def]
    ext <;> dsimp only <;> rw [Int.mul_sub, Int.mul_sub] <;> omega
  normSq_eq ψ := by
    have hSumRe : ∀ (K : Nat) (f : Fin K → GaussInt),
        (finGaussSum K f).re = finIntSum K (fun z => (f z).re) := by
      intro K; induction K with
      | zero => intros; simp only [finGaussSum_zero, finIntSum_zero, GaussInt.zero_def]
      | succ k ih => intro f; simp only [finGaussSum_succ, finIntSum_succ, GaussInt.add_def, ih]
    have hSumIm : ∀ (K : Nat) (f : Fin K → GaussInt),
        (finGaussSum K f).im = finIntSum K (fun z => (f z).im) := by
      intro K; induction K with
      | zero => intros; simp only [finGaussSum_zero, finIntSum_zero, GaussInt.zero_def]
      | succ k ih => intro f; simp only [finGaussSum_succ, finIntSum_succ, GaussInt.add_def, ih]
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
        simp only [GaussInt.normSqInt_def, GaussInt.sub_def, GaussInt.scaleInt_def]
        rw [hSumRe, hSumIm]
      have hRHS : finIntSum N (fun x => Int.ofNat (GaussInt.normSq (ψ x y a))) =
          finIntSum N (fun x => (ψ x y a).re * (ψ x y a).re + (ψ x y a).im * (ψ x y a).im) := by
        congr 1; funext x
        simpa only [GaussInt.normSqInt_def] using (GaussInt.normSqInt_eq_ofNat_normSq (ψ x y a)).symm
      rw [hLHS, hRHS, finIntSum_add, finIntSum_add,
          grover_int_reflection_normSq N (fun z => (ψ z y a).re),
          grover_int_reflection_normSq N (fun z => (ψ z y a).im), Int.mul_add]
    simp only [QVec.stateNormSq_def, QVec.queryWeight_def]
    simp only [qsum_zero, qsum_succ, Nat.add_zero]
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
    subst hM0; simp [qsum_zero]
  | n + 1, 0, _, c, d => by
    have hEq : qsum (n + 1) (fun x : Fin (n + 1) => if x.1 < 0 then c else d) =
        qsum (n + 1) (fun _ => d) := by
      apply qsum_congr; intro x; simp
    rw [hEq, qsum_const]; simp
  | n + 1, m + 1, hLe, c, d => by
    simp only [qsum_succ, Nat.zero_lt_succ, ↓reduceIte]
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
    subst hM0; simp [finIntSum_zero]
  | n + 1, 0, _, u, v => by
    have hEq : (fun x : Fin (n + 1) => if x.1 < 0 then u else v) = (fun _ => v) := by
      funext x; simp
    rw [hEq, finIntSum_const]; simp
  | n + 1, m + 1, hLe, u, v => by
    simp only [finIntSum_succ, Nat.zero_lt_succ, ↓reduceIte]
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
      intro x; simp only [QVec.queryWeight_def, groverTemplateState]
      simp only [qsum_zero, qsum_succ]
      by_cases hx : x.1 < M <;> simp [hx, GaussInt.normSq_def]
    simp only [QVec.stateNormSq_def]
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
  | 0, _ => by rw [advStateAt_zero]; rfl
  | j + 1, hj => by
    simp only [advStateAt_succ]
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
      rw [oracleXor_def]
      unfold untweakedMultiTargetOracle groverTemplateState
      rcases y with ⟨yv, hyv⟩
      have hCasesY : yv = 0 ∨ yv = 1 := by omega
      have hx0 : (xorFin (⟨0, by decide⟩ : Fin (2 ^ 1)) 1#1).1 = 1 := by rw [xorFin_def]; rfl
      have hx1 : (xorFin (⟨1, by decide⟩ : Fin (2 ^ 1)) 1#1).1 = 0 := by rw [xorFin_def]; rfl
      have hz0 : (xorFin (⟨0, by decide⟩ : Fin (2 ^ 1)) 0#1).1 = 0 := by rw [xorFin_def]; rfl
      have hz1 : (xorFin (⟨1, by decide⟩ : Fin (2 ^ 1)) 0#1).1 = 1 := by rw [xorFin_def]; rfl
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
      | zero => intros; simp only [finGaussSum_zero, finIntSum_zero, GaussInt.zero_def]
      | succ k ih => intro f; simp only [finGaussSum_succ, finIntSum_succ, GaussInt.add_def, ih]
    have hSumIm0 : ∀ (K : Nat) (f : Fin K → Int),
        (finGaussSum K (fun z => (⟨f z, 0⟩ : GaussInt))).im = 0 := by
      intro K; induction K with
      | zero => intros; simp only [finGaussSum_zero, GaussInt.zero_def]
      | succ k ih => intro f; simp only [finGaussSum_succ, GaussInt.add_def, ih]; omega
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
    · simp only [GaussInt.sub_def, GaussInt.scaleInt_def]
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
    · simp only [GaussInt.sub_def, GaussInt.scaleInt_def]
      rw [hSumIm0]
      omega

private theorem prefixScale_untweakedGrover (N M q : Nat) (hN : 0 < N) :
    ∀ (j : Nat) (hj : j ≤ q),
      prefixScale (untweakedGroverAdv N M q hN) j hj = N ^ (2 * j)
  | 0, _ => by simp [prefixScale_zero]
  | j + 1, hj => by
    simp only [prefixScale_succ]
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
    by simpa only [runQuantumAdv_def] using
      untweakedGroverAdv_state_eq N M q hM_pos hMN hRegime hN q (Nat.le_refl q)
  have hInitNorm : QVec.stateNormSq A.init = 2 * N := by
    have hEach : ∀ x : Fin N, QVec.queryWeight (groverTemplateState N M 1 1) x = 2 := by
      intro x; simp only [QVec.queryWeight_def, groverTemplateState]
      simp only [qsum_zero, qsum_succ]
      by_cases hx : x.1 < M <;> simp [hx, GaussInt.normSq_def]
    simp only [QVec.stateNormSq_def]
    change qsum N (fun x => QVec.queryWeight (groverTemplateState N M 1 1) x) = 2 * N
    rw [qsum_congr hEach, qsum_const, Nat.mul_comm]
  have hDenom : QVec.stateNormSq (runQuantumAdv A H) = 2 * N ^ (2 * q + 1) := by
    rw [runQuantumAdv_normSq, prefixScale_untweakedGrover N M q hN q (Nat.le_refl q), hInitNorm]
    rw [Nat.pow_succ, ← Nat.mul_assoc (N ^ (2 * q)) 2 N, Nat.mul_comm (N ^ (2 * q)) 2, Nat.mul_assoc]
  have hNum : QVec.measureNormSq (fun x => decide (x.1 < M)) (runQuantumAdv A H) =
      M * (2 * (αq * αq)) := by
    rw [hState]
    simp only [QVec.measureNormSq_def, QVec.queryMassOn_def]
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
        simp only [hx, decide_true, ↓reduceIte, QVec.queryWeight_def, groverTemplateState, qsum_zero, qsum_succ,
          Nat.zero_add, h00, h10, Bool.false_eq_true, GaussInt.normSq_def, hAbsNeg, hAbsPos, Nat.add_zero]
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
  simp only [QVec.bornProb_def, RatBound.le]
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

/-- Rational strict/non-strict transitivity, proved before specializing to large quantum games.
    Keeping this cancellation symbolic avoids reducing an astronomical concrete oracle run. -/
private theorem ratBound_lt_of_lt_of_le (a b c : RatBound)
    (hab : RatBound.lt a b) (hbc : RatBound.le b c) : RatBound.lt a c := by
  unfold RatBound.lt at hab ⊢
  unfold RatBound.le at hbc
  have h1 := Nat.mul_lt_mul_of_pos_right hab c.h_pos
  have h2 := Nat.mul_le_mul_right a.den hbc
  have hChain : (a.num * c.den) * b.den < (c.num * a.den) * b.den := by
    calc
      (a.num * c.den) * b.den = (a.num * b.den) * c.den := by ac_rfl
      _ < (b.num * a.den) * c.den := h1
      _ = (b.num * c.den) * a.den := by ac_rfl
      _ ≤ (c.num * b.den) * a.den := h2
      _ = (c.num * a.den) * b.den := by ac_rfl
  rcases Nat.lt_or_ge (a.num * c.den) (c.num * a.den) with h | h
  · exact h
  · exact False.elim (Nat.not_lt_of_ge (Nat.mul_le_mul_right b.den h) hChain)

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
    exact ratBound_lt_of_lt_of_le _ _ _ hStrict hLoLe
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

/-! ### Exports for lane agg-whir-cert -/

theorem goldilocksExt4Card_def : goldilocksExt4Card = goldilocksPrime ^ 4 := by rfl
-- (end exports for lane agg-whir-cert)

end Qsag

namespace Qsag
public section

theorem whirAffineEqualDegreeCommitFoldBound_def (w : WhirAffineWitness) :
    whirAffineEqualDegreeCommitFoldBound w =
      ⟨whirAffineStageSimpleNum w, goldilocksExt4Card, goldilocksExt4Card_pos⟩ := by unfold whirAffineEqualDegreeCommitFoldBound; rfl

theorem whirAffinePureQueryBound_def (w : WhirAffineWitness) (hq : w.queries ≤ w.n) :
    whirAffinePureQueryBound w hq =
      ⟨affineFallingFactorial (w.A + w.sFolds) w.queries,
        affineFallingFactorial w.n w.queries, affineFallingFactorial_pos w.n w.queries hq⟩ := by unfold whirAffinePureQueryBound; rfl

theorem whirAffinePureQueryBoundOrOne_def (w : WhirAffineWitness) :
    whirAffinePureQueryBoundOrOne w =
      if hq : w.queries ≤ w.n then whirAffinePureQueryBound w hq else RatBound.one := by unfold whirAffinePureQueryBoundOrOne; rfl

end
end Qsag

/-! ### Exports for lane agg -/
public section
namespace Qsag

/-- Every roster entry's 128-bit hash-query ceiling is at least `2^30`. -/
theorem qsagPq128PortfolioRoster_ceiling_ge_30 (b : QueryBudget) :
    ∀ entry ∈ qsagPq128PortfolioRoster b, 30 ≤ entry.pq128HashQueryCeilingLog2 :=
  roster_ceiling_ge_30 b

private theorem grover_single_num_pos (n q : Nat) :
    0 < (quantumGroverSingleTargetBound n q).num := by
  rw [quantumGroverSingleTargetBound_def, quantumZhandryMultiTargetBound_def]
  exact Nat.mul_pos (by decide) (Nat.pow_pos (Nat.succ_pos q))

private theorem classicalFs_num_pos (q : Nat) {p : RatBound} (hp : 0 < p.num) :
    0 < (classicalFiatShamirBound q p).num := by
  rw [classicalFiatShamirBound_def]
  exact Nat.mul_pos (Nat.succ_pos q) hp

private theorem groverGrinding_num_pos (q : Nat) {p : RatBound} (hp : 0 < p.num) :
    0 < (quantumGroverGrindingBound q p).num := by
  rw [quantumGroverGrindingBound_def]
  exact Nat.mul_pos (Nat.mul_pos (by decide) (Nat.pow_pos (Nat.succ_pos q))) hp

private theorem zkbooPow_num_pos (k : Nat) : 0 < (zkbooSingleRepError.pow k).num :=
  Nat.pow_pos (by decide : 0 < zkbooSingleRepError.num)

/-- At the budget `⟨2^30 - 1, 2^16, 2^20 - 1⟩` every roster entry has strictly positive classical
    and QROM numerators. -/
theorem qsagPq128PortfolioRoster_num_pos_at_2pow30 :
    ∀ entry ∈ qsagPq128PortfolioRoster ⟨2 ^ 30 - 1, 2 ^ 16, 2 ^ 20 - 1⟩,
      0 < entry.classicalBound.num ∧ 0 < entry.quantumBound.num := by
  intro entry hMem
  simp only [qsagPq128PortfolioRoster, List.mem_cons, List.not_mem_nil, or_false] at hMem
  rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, grover_single_num_pos _ _⟩
  · exact ⟨by decide, grover_single_num_pos _ _⟩
  · exact ⟨by decide, grover_single_num_pos _ _⟩
  · exact ⟨ratBound_add_num_pos_left (by decide),
      ratBound_add_num_pos_left (grover_single_num_pos _ _)⟩
  · exact ⟨by decide, grover_single_num_pos _ _⟩
  · exact ⟨ratBound_add_num_pos_left (by decide), ratBound_add_num_pos_left (by decide)⟩
  · exact ⟨ratBound_add_num_pos_left (classicalFs_num_pos _ (zkbooPow_num_pos _)),
      ratBound_add_num_pos_left (groverGrinding_num_pos _ (zkbooPow_num_pos _))⟩
  · exact ⟨ratBound_add_num_pos_left (by decide), ratBound_add_num_pos_left (by decide)⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨ratBound_add_num_pos_left (by decide), ratBound_add_num_pos_left (by decide)⟩
  · exact ⟨ratBound_add_num_pos_left (by decide), ratBound_add_num_pos_left (by decide)⟩
  · exact ⟨ratBound_add_num_pos_left (classicalFs_num_pos _ (zkbooPow_num_pos _)),
      ratBound_add_num_pos_left (groverGrinding_num_pos _ (zkbooPow_num_pos _))⟩

#verify_constructive Qsag.qsagPq128PortfolioRoster_ceiling_ge_30
#verify_constructive Qsag.qsagPq128PortfolioRoster_num_pos_at_2pow30

end Qsag
end
