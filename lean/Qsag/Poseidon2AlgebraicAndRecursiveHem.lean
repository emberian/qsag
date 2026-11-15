module
/-
# Qsag.Poseidon2AlgebraicAndRecursiveHem — Poseidon2 Algebraic Margins & 2-Layer `Hem` Extraction

1. **§1 Power maps on `Goldilocks`.** Fermat on the field carrier (`goldilocksPow_fermat`), the
   exponent-inverse law `d * e = k * (p - 1) + 1 → (x ^ d) ^ e = x`
   (`goldilocksPow_pow_of_exponent_inverse`), its `d = 7` instance, and non-injectivity of
   `x ↦ x ^ d` for every `2 ≤ d < 7` (`sbox7_is_minimal_nontrivial_power_permutation`,
   `tooth_d3_not_permutation_on_goldilocks`, `tooth_d5_not_permutation_on_goldilocks`).
2. **§2 Width-16 external layer.** `applyM4` is `circ(2, 3, 1, 1)` (`applyM4_eq_circ_2_3_1_1`);
   the width-16 layer `M_E = circ(2 M_4, M_4, M_4, M_4)` has a two-sided inverse
   (`applyME16Inv_applyME16`, `applyME16_applyME16Inv`) and maps non-zero states to non-zero
   states. The deployed permutation `poseidon2Perm12` has width 12; its layer is inverted in
   `Qsag.Poseidon2`.
3. **§3 Round-count arithmetic for `R_F = 8`, `R_P = 22`, `d = 7`.** The nominal degree `7 ^ r`
   first reaches `p` at `r = 23` (`poseidon2_nominal_degree_threshold`), `2 ^ 84 < 7 ^ 30 < 2 ^ 85`
   (`tooth_univariate_degree_alone_below_two_pow_128`), the interpolation round inequality
   `1 + ⌈64 log_7 2⌉ + ⌈log_7 t⌉ ≤ R_F + R_P` for `t ∈ {12, 16}` with a failing `R_P = 17`
   tooth, and the sample lower bound behind it: any `n` sample points admit a non-zero polynomial
   with `n + 1` coefficients vanishing on all of them (`univariate_interpolation_underdetermined`).
   These are statements about the parameter set and about polynomials of a given degree. The
   degree of the permutation's actual interpolation polynomial is not computed here.
4. **§4 Two-layer hierarchical `Hem`.** Root verifiers (`verifyHierarchicalHem`, `verifyHemHierarchy`,
   and direct policy check `verifyHemHierarchyAgainstRegistry`) over `M` shard certificates, each a
   `verifySuccinctAggregate` proof on `shardBoundMessage shardId epochFloor msg`, with
   pairwise-distinct shard ids, pairwise-disjoint committees, and an injective commitment to the
   shard policy registry (`ShardRegistration` binding `shardId`, `threshold`, `suiteId`, `params`,
   and `committee`, with `1 ≤ threshold ≤ |committee|`). `extractShardEnvFromTranscript` grounds
   `StagesBound` in prover commitment-opening transcripts with exact opening-cost accounting
   (`hierarchyTranscriptQueryCost`) and composes with `extractHierarchicalHemQuorums`
   (`extractHierarchicalHemFromTranscripts`). `hierarchical_hem_soundness_error_bound` establishes
   the finite-coin union bound under authenticated registry digests (`HashCollisionWitness H` on
   root mismatch), paired with `#tooth` theorems `tooth_forged_lower_shard_threshold_rejected` and
   `tooth_unscoped_shard_id_allows_quorum_replay_multiplication`. The root verifies shard
   certificates directly; no verifier is arithmetized inside another proof.
5. **§5 Deployed width-12 inverses and exact M4 branch number.** Both actual linear layers and
   both round types have two-sided inverses. The deployed permutation is injective. Cofactor
   certificates for all 69 square minors establish the universal M4 branch bound, with a unit
   vector attaining five; `m4_mds_branch_number_eq_five` uses the `Fin 4 → Goldilocks` interface.
6. **§6 Actual four-lane differential and symbolic circuits.** The seventh-power S-box preserves
   differential support. Two consecutive four-lane rounds have at least five active S-boxes;
   eight such rounds have at least twenty. A polynomial-expression circuit evaluates to the
   actual four-lane round and has degree at most `7^r` after `r` rounds. These are component
   bounds, not a differential probability or interpolation-degree lower bound for width 12.
7. **§7 Concrete hierarchical certificates & prover transcripts.** Two distinct singleton committees
   with threshold one use the honest two-stage WHIR prover, verified commitment-opening transcripts,
   and a Poseidon2 registry commitment, alongside concrete Poseidon2 forged-threshold rejection
   witnesses (`1 → 0` and `2 → 1` on a two-key committee) and unconditional replay rejection. The
   example uses the field-based signature suite from `Aggregation`, not a claimed secure
   instantiation of that suite.
8. **§8 Width-12 `M_E` & `M_I` differential and linear branch numbers.** Exact 12-lane differential
   and transpose-linear branch bounds for `applyME` (single-block `≥ 7 ≥ 5`, multi-block `≥ 8`,
   universal `= 7`) and `applyMI` (nonzero-sum `= 13` with full 12-lane diffusion on single-lane
   inputs, universal `≥ 4`).
9. **§9 `sbox7` differential uniformity `≤ 6` & width-12 `(R_F = 8, R_P = 22)` wide-trail bounds.**
   Degree-6 root bound on `(x + Δ)^7 - x^7 = δ` (`Δ ≠ 0`), `≥ 28` active S-boxes across the
   deployed 30-round `poseidon2Perm12`, and `< 2 ^ (-256)` differential and squared-linear
   characteristic bounds.
10. **§10 Width-12 symbolic circuit, univariate saturation & CICO-1 Macaulay/Bézout bounds.**
    Full width-12 `PoseidonExpr` lifting of `poseidon2Perm12`, forward/backward degree saturation
    past `goldilocksPrime`, and CICO-1 Bézout and Macaulay matrix dimension bounds `> 2 ^ 128`.
11. **§11 Succinct outer recursive `Hem` aggregation & soundness composition.** Single outer
    `bciksJohnsonQrom128` certificate over length-framed compressed shard headers with constructive
    witness extraction and finite-coin error bound `M · ε_hem + ε_outer`.
-/

public import Qsag.Goldilocks
import all Qsag.Goldilocks
public import Qsag.Poseidon2
import all Qsag.Poseidon2
public import Qsag.Aggregation
import all Qsag.Aggregation
import Lean

import Qsag.Tactic.AssuranceKit
import Qsag.Tactic.ConstructiveRing

public section
namespace Qsag

open Aggregation RoundPoly

set_option autoImplicit false

/-! ## 1. Power Maps on `Goldilocks`: Fermat, Exponent Inverses, and Minimality of `d = 7` -/

private theorem gold_ne_of_val_ne {a b : Goldilocks} (h : a.val ≠ b.val) : a ≠ b :=
  fun e => h (congrArg Goldilocks.val e)

private theorem gold_not_dvd_val {a : Goldilocks} (h0 : a.val ≠ 0) :
    ¬ (goldilocksPrime ∣ a.val) := fun hd => by
  have hle := Nat.le_of_dvd (by omega) hd
  have hlt := a.isLt
  omega

/-- **Fermat's little theorem on the `Goldilocks` carrier**: `a ^ (p - 1) = 1` for `a ≠ 0`. -/
theorem goldilocksPow_fermat {a : Goldilocks} (ha : a ≠ Goldilocks.zero) :
    goldilocksPow a (goldilocksPrime - 1) = Goldilocks.one := by
  apply Goldilocks.ext
  rw [goldilocksPow_val]
  exact (goldilocksPrime_isPrime ()).pow_sub_one_mod
    (gold_not_dvd_val (fun h => ha (Goldilocks.ext h)))

private theorem pow_cycle_mod (a : Goldilocks) (k : Nat) :
    (a.val ^ (k * (goldilocksPrime - 1) + 1)) % goldilocksPrime = a.val := by
  if h0 : a.val = 0 then
    rw [h0, Nat.zero_pow (Nat.succ_pos _), Nat.zero_mod]
  else
    have hflt : (a.val ^ (goldilocksPrime - 1)) % goldilocksPrime = 1 :=
      (goldilocksPrime_isPrime ()).pow_sub_one_mod (gold_not_dvd_val h0)
    have h1 : ((a.val ^ (goldilocksPrime - 1)) ^ k) % goldilocksPrime = 1 := by
      rw [Nat.pow_mod, hflt, Nat.one_pow]
      decide
    rw [Nat.pow_add, Nat.pow_one, Nat.mul_comm k, Nat.pow_mul, Nat.mul_mod, h1,
        Nat.one_mul, Nat.mod_mod, Nat.mod_eq_of_lt a.isLt]

/-- **Exponent-inverse law**: if `d * e ≡ 1 (mod p - 1)` then `x ↦ x ^ e` undoes `x ↦ x ^ d` on
    all of `Goldilocks`, including `0`. -/
theorem goldilocksPow_pow_of_exponent_inverse (x : Goldilocks) (d e k : Nat)
    (h : d * e = k * (goldilocksPrime - 1) + 1) :
    goldilocksPow (goldilocksPow x d) e = x := by
  apply Goldilocks.ext
  rw [goldilocksPow_val, goldilocksPow_val, ← Nat.pow_mod, ← Nat.pow_mul, h]
  exact pow_cycle_mod x k

/-- A power map with an exponent inverse modulo `p - 1` is injective. -/
theorem goldilocksPow_injective_of_exponent_inverse (d e k : Nat)
    (h : d * e = k * (goldilocksPrime - 1) + 1) (x y : Goldilocks) :
    goldilocksPow x d = goldilocksPow y d ↔ x = y := by
  constructor
  · intro hxy
    have hx := goldilocksPow_pow_of_exponent_inverse x d e k h
    have hy := goldilocksPow_pow_of_exponent_inverse y d e k h
    rw [hxy] at hx
    exact hx.symm.trans hy
  · intro hxy
    rw [hxy]

theorem poseidon2DInv_exponent_inverse :
    7 * poseidon2DInv = 4 * (goldilocksPrime - 1) + 1 := by decide

theorem goldilocksPow_seven_eq_sbox7 (x : Goldilocks) : goldilocksPow x 7 = sbox7 x := by
  apply Goldilocks.ext
  rw [goldilocksPow_val, sbox7_val]

/-- `(x ^ 7) ^ d_inv = x` for every `x : Goldilocks`. -/
theorem sbox7_dInv_roundtrip (x : Goldilocks) :
    goldilocksPow (sbox7 x) poseidon2DInv = x := by
  rw [← goldilocksPow_seven_eq_sbox7]
  exact goldilocksPow_pow_of_exponent_inverse x 7 poseidon2DInv 4 poseidon2DInv_exponent_inverse

/-- `x ^ 7 = y ^ 7 ↔ x = y` on `Goldilocks`. -/
theorem goldilocksPow_seven_injective (x y : Goldilocks) :
    goldilocksPow x 7 = goldilocksPow y 7 ↔ x = y :=
  goldilocksPow_injective_of_exponent_inverse 7 poseidon2DInv 4 poseidon2DInv_exponent_inverse x y

/-- Primitive cube root of unity `7 ^ ((p - 1) / 3)`. -/
def goldilocksOmega3 : Goldilocks := ⟨18446744065119617025, by decide⟩

/-- Primitive fifth root of unity `7 ^ ((p - 1) / 5)`. -/
def goldilocksOmega5 : Goldilocks := ⟨1373043270956696022, by decide⟩

/-- `-1` in `Goldilocks`. -/
def goldilocksNegOne : Goldilocks := ⟨18446744069414584320, by decide⟩

/-- `x ↦ x ^ 3` identifies `ω₃ ≠ 1` with `1`, because `3 ∣ p - 1`. -/
theorem tooth_d3_not_permutation_on_goldilocks :
    goldilocksOmega3 ≠ Goldilocks.one ∧ goldilocksOmega3 ≠ Goldilocks.zero ∧
    goldilocksPow goldilocksOmega3 3 = goldilocksPow Goldilocks.one 3 ∧
    3 ∣ goldilocksPrime - 1 := by
  refine ⟨gold_ne_of_val_ne (by decide), gold_ne_of_val_ne (by decide), ?_,
    ⟨6148914689804861440, by decide⟩⟩
  apply Goldilocks.ext
  rw [goldilocksPow_val, goldilocksPow_val]
  decide

/-- `x ↦ x ^ 5` identifies `ω₅ ≠ 1` with `1`, because `5 ∣ p - 1`. -/
theorem tooth_d5_not_permutation_on_goldilocks :
    goldilocksOmega5 ≠ Goldilocks.one ∧ goldilocksOmega5 ≠ Goldilocks.zero ∧
    goldilocksPow goldilocksOmega5 5 = goldilocksPow Goldilocks.one 5 ∧
    5 ∣ goldilocksPrime - 1 := by
  refine ⟨gold_ne_of_val_ne (by decide), gold_ne_of_val_ne (by decide), ?_,
    ⟨3689348813882916864, by decide⟩⟩
  apply Goldilocks.ext
  rw [goldilocksPow_val, goldilocksPow_val]
  decide

private theorem pow_collision_with_one (w : Goldilocks) (d : Nat)
    (hne : w.val ≠ 1) (hpow : w.val ^ d % goldilocksPrime = 1 ^ d % goldilocksPrime) :
    ∃ x y : Goldilocks, x ≠ y ∧ goldilocksPow x d = goldilocksPow y d :=
  ⟨w, Goldilocks.one, gold_ne_of_val_ne hne, by
    apply Goldilocks.ext
    rw [goldilocksPow_val, goldilocksPow_val]
    exact hpow⟩

/-- **`d = 7` is the least exponent `d ≥ 2` whose power map permutes `Goldilocks`**: every
    `2 ≤ d < 7` has a collision (`-1` for even `d`, `ω₃` for `d = 3`, `ω₅` for `d = 5`), while
    `goldilocksPow_seven_injective` holds for `d = 7`. -/
theorem sbox7_is_minimal_nontrivial_power_permutation (d : Nat) (h2 : 2 ≤ d) (h7 : d < 7) :
    ∃ x y : Goldilocks, x ≠ y ∧ goldilocksPow x d = goldilocksPow y d := by
  have hd : d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 := by omega
  rcases hd with rfl | rfl | rfl | rfl | rfl
  · exact pow_collision_with_one goldilocksNegOne 2 (by decide) (by decide)
  · exact pow_collision_with_one goldilocksOmega3 3 (by decide) (by decide)
  · exact pow_collision_with_one goldilocksNegOne 4 (by decide) (by decide)
  · exact pow_collision_with_one goldilocksOmega5 5 (by decide) (by decide)
  · exact pow_collision_with_one goldilocksNegOne 6 (by decide) (by decide)

/-! ## 2. Width-16 External Layer `M_E = circ(2 M_4, M_4, M_4, M_4)` -/

private theorem ofNat_eq_goldOfInt16 (k : Nat) : Goldilocks.ofNat k = goldOfInt (k : Int) := by
  apply Goldilocks.ext
  apply Int.ofNat_inj.mp
  rw [goldOfInt_val]
  simp [Goldilocks.ofNat, goldP, Int.natCast_emod]

/-- `applyM4` is multiplication by the circulant matrix `circ(2, 3, 1, 1)`. -/
theorem applyM4_eq_circ_2_3_1_1 (b : Lane4) :
    applyM4 b =
      ⟨Goldilocks.add (Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 2) b.x0)
          (Goldilocks.mul (Goldilocks.ofNat 3) b.x1)) (Goldilocks.add b.x2 b.x3),
       Goldilocks.add (Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 2) b.x1)
          (Goldilocks.mul (Goldilocks.ofNat 3) b.x2)) (Goldilocks.add b.x3 b.x0),
       Goldilocks.add (Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 2) b.x2)
          (Goldilocks.mul (Goldilocks.ofNat 3) b.x3)) (Goldilocks.add b.x0 b.x1),
       Goldilocks.add (Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 2) b.x3)
          (Goldilocks.mul (Goldilocks.ofNat 3) b.x0)) (Goldilocks.add b.x1 b.x2)⟩ := by
  unfold applyM4 lane4Sum
  apply Lane4.ext <;>
    (dsimp only
     rw [← goldOfInt_nat b.x0, ← goldOfInt_nat b.x1, ← goldOfInt_nat b.x2, ← goldOfInt_nat b.x3]
     simp only [ofNat_eq_goldOfInt16, goldOfInt_add, goldOfInt_mul]
     congr 1
     omega)

/-- Width-16 Poseidon2 state as four `Lane4` blocks. -/
structure Poseidon2State16 where
  b0 : Lane4
  b1 : Lane4
  b2 : Lane4
  b3 : Lane4
  deriving DecidableEq, Repr

theorem Poseidon2State16.ext {s t : Poseidon2State16}
    (h0 : s.b0 = t.b0) (h1 : s.b1 = t.b1) (h2 : s.b2 = t.b2) (h3 : s.b3 = t.b3) : s = t := by
  cases s; cases t; simp only at *; subst h0 h1 h2 h3; rfl

def state16Zero : Poseidon2State16 := ⟨lane4Zero, lane4Zero, lane4Zero, lane4Zero⟩

private def inv5Gold : Goldilocks := ⟨14757395255531667457, by decide⟩

/-- Width-16 external layer: block `i` of the output is `M_4 b_i + Σ_j M_4 b_j`. -/
def applyME16 (st : Poseidon2State16) : Poseidon2State16 :=
  let y0 := applyM4 st.b0
  let y1 := applyM4 st.b1
  let y2 := applyM4 st.b2
  let y3 := applyM4 st.b3
  let s := lane4Add (lane4Add (lane4Add y0 y1) y2) y3
  ⟨lane4Add y0 s, lane4Add y1 s, lane4Add y2 s, lane4Add y3 s⟩

/-- Explicit inverse of `applyME16`: the block sum is recovered as `5⁻¹ · Σ_i y_i`. -/
def applyME16Inv (st : Poseidon2State16) : Poseidon2State16 :=
  let s := lane4Scale inv5Gold (lane4Add (lane4Add (lane4Add st.b0 st.b1) st.b2) st.b3)
  ⟨applyM4Inv (lane4Sub st.b0 s), applyM4Inv (lane4Sub st.b1 s),
   applyM4Inv (lane4Sub st.b2 s), applyM4Inv (lane4Sub st.b3 s)⟩

private theorem gold_mul_cancel_of_prod_one {u k : Goldilocks}
    (h : Goldilocks.mul u k = Goldilocks.one) (x : Goldilocks) :
    Goldilocks.mul u (Goldilocks.mul k x) = x := by
  change CommRingOps.mul u (CommRingOps.mul k x) = x
  rw [← LawfulCommRing.mul_assoc]
  change CommRingOps.mul (Goldilocks.mul u k) x = x
  rw [h]
  exact LawfulCommRing.one_mul x

private theorem inv5Gold_mul_cancel (x : Goldilocks) :
    Goldilocks.mul inv5Gold (Goldilocks.mul (Goldilocks.ofNat 5) x) = x :=
  gold_mul_cancel_of_prod_one (Goldilocks.ext (by rw [Goldilocks.mul_val]; decide)) x

private theorem mul_inv5Gold_cancel (x : Goldilocks) :
    Goldilocks.mul (Goldilocks.ofNat 5) (Goldilocks.mul inv5Gold x) = x :=
  gold_mul_cancel_of_prod_one (Goldilocks.ext (by rw [Goldilocks.mul_val]; decide)) x

private theorem scalar_sum_five_cancel (a b c d : Goldilocks) :
    Goldilocks.mul inv5Gold (Goldilocks.add (Goldilocks.add (Goldilocks.add
      (Goldilocks.add a (Goldilocks.add (Goldilocks.add (Goldilocks.add a b) c) d))
      (Goldilocks.add b (Goldilocks.add (Goldilocks.add (Goldilocks.add a b) c) d)))
      (Goldilocks.add c (Goldilocks.add (Goldilocks.add (Goldilocks.add a b) c) d)))
      (Goldilocks.add d (Goldilocks.add (Goldilocks.add (Goldilocks.add a b) c) d))) =
      Goldilocks.add (Goldilocks.add (Goldilocks.add a b) c) d := by
  have h : Goldilocks.add (Goldilocks.add (Goldilocks.add
      (Goldilocks.add a (Goldilocks.add (Goldilocks.add (Goldilocks.add a b) c) d))
      (Goldilocks.add b (Goldilocks.add (Goldilocks.add (Goldilocks.add a b) c) d)))
      (Goldilocks.add c (Goldilocks.add (Goldilocks.add (Goldilocks.add a b) c) d)))
      (Goldilocks.add d (Goldilocks.add (Goldilocks.add (Goldilocks.add a b) c) d)) =
      Goldilocks.mul (Goldilocks.ofNat 5)
        (Goldilocks.add (Goldilocks.add (Goldilocks.add a b) c) d) := by
    rw [← goldOfInt_nat a, ← goldOfInt_nat b, ← goldOfInt_nat c, ← goldOfInt_nat d]
    simp only [ofNat_eq_goldOfInt16, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [h, inv5Gold_mul_cancel]

private theorem lane4_sum_five_cancel (y0 y1 y2 y3 : Lane4) :
    lane4Scale inv5Gold (lane4Add (lane4Add (lane4Add
      (lane4Add y0 (lane4Add (lane4Add (lane4Add y0 y1) y2) y3))
      (lane4Add y1 (lane4Add (lane4Add (lane4Add y0 y1) y2) y3)))
      (lane4Add y2 (lane4Add (lane4Add (lane4Add y0 y1) y2) y3)))
      (lane4Add y3 (lane4Add (lane4Add (lane4Add y0 y1) y2) y3))) =
    lane4Add (lane4Add (lane4Add y0 y1) y2) y3 := by
  unfold lane4Scale lane4Add
  exact Lane4.ext
    (scalar_sum_five_cancel y0.x0 y1.x0 y2.x0 y3.x0)
    (scalar_sum_five_cancel y0.x1 y1.x1 y2.x1 y3.x1)
    (scalar_sum_five_cancel y0.x2 y1.x2 y2.x2 y3.x2)
    (scalar_sum_five_cancel y0.x3 y1.x3 y2.x3 y3.x3)

private theorem lane4Sub_add_cancel (a s : Lane4) : lane4Sub (lane4Add a s) s = a := by
  unfold lane4Sub lane4Add
  apply Lane4.ext <;>
    (change CommRingOps.sub (CommRingOps.add _ _) _ = _
     rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_assoc,
         LawfulCommRing.add_right_neg, LawfulCommRing.add_zero])

theorem applyME16Inv_applyME16 (st : Poseidon2State16) : applyME16Inv (applyME16 st) = st := by
  unfold applyME16Inv applyME16
  dsimp only
  rw [lane4_sum_five_cancel]
  rw [lane4Sub_add_cancel, lane4Sub_add_cancel, lane4Sub_add_cancel, lane4Sub_add_cancel]
  rw [applyM4Inv_applyM4, applyM4Inv_applyM4, applyM4Inv_applyM4, applyM4Inv_applyM4]

private theorem scalar_block_recover (y a b c d s : Goldilocks)
    (h : Goldilocks.mul (Goldilocks.ofNat 5) s =
      Goldilocks.add (Goldilocks.add (Goldilocks.add a b) c) d) :
    Goldilocks.add (Goldilocks.sub y s)
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.sub a s) (Goldilocks.sub b s))
        (Goldilocks.sub c s)) (Goldilocks.sub d s)) = y := by
  have e : Goldilocks.add (Goldilocks.sub y s)
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.sub a s) (Goldilocks.sub b s))
        (Goldilocks.sub c s)) (Goldilocks.sub d s)) =
      Goldilocks.add y (Goldilocks.sub (Goldilocks.add (Goldilocks.add (Goldilocks.add a b) c) d)
        (Goldilocks.mul (Goldilocks.ofNat 5) s)) := by
    rw [← goldOfInt_nat y, ← goldOfInt_nat a, ← goldOfInt_nat b, ← goldOfInt_nat c,
        ← goldOfInt_nat d, ← goldOfInt_nat s]
    simp only [ofNat_eq_goldOfInt16, goldOfInt_add, goldOfInt_sub, goldOfInt_mul]
    congr 1
    omega
  rw [e, h]
  change CommRingOps.add y (CommRingOps.sub _ _) = y
  rw [LawfulCommRing.sub_self, LawfulCommRing.add_zero]

private theorem lane4_block_recover (y a b c d s : Lane4)
    (h : lane4Scale (Goldilocks.ofNat 5) s = lane4Add (lane4Add (lane4Add a b) c) d) :
    lane4Add (lane4Sub y s)
      (lane4Add (lane4Add (lane4Add (lane4Sub a s) (lane4Sub b s)) (lane4Sub c s))
        (lane4Sub d s)) = y := by
  have h0 := congrArg Lane4.x0 h
  have h1 := congrArg Lane4.x1 h
  have h2 := congrArg Lane4.x2 h
  have h3 := congrArg Lane4.x3 h
  unfold lane4Scale lane4Add at h0 h1 h2 h3
  unfold lane4Add lane4Sub
  exact Lane4.ext
    (scalar_block_recover y.x0 a.x0 b.x0 c.x0 d.x0 s.x0 h0)
    (scalar_block_recover y.x1 a.x1 b.x1 c.x1 d.x1 s.x1 h1)
    (scalar_block_recover y.x2 a.x2 b.x2 c.x2 d.x2 s.x2 h2)
    (scalar_block_recover y.x3 a.x3 b.x3 c.x3 d.x3 s.x3 h3)

theorem applyME16_applyME16Inv (st : Poseidon2State16) : applyME16 (applyME16Inv st) = st := by
  have h5 : lane4Scale (Goldilocks.ofNat 5)
      (lane4Scale inv5Gold (lane4Add (lane4Add (lane4Add st.b0 st.b1) st.b2) st.b3)) =
      lane4Add (lane4Add (lane4Add st.b0 st.b1) st.b2) st.b3 := by
    unfold lane4Scale
    exact Lane4.ext (mul_inv5Gold_cancel _) (mul_inv5Gold_cancel _)
      (mul_inv5Gold_cancel _) (mul_inv5Gold_cancel _)
  unfold applyME16 applyME16Inv
  dsimp only
  rw [applyM4_applyM4Inv, applyM4_applyM4Inv, applyM4_applyM4Inv, applyM4_applyM4Inv]
  exact Poseidon2State16.ext
    (lane4_block_recover st.b0 st.b0 st.b1 st.b2 st.b3 _ h5)
    (lane4_block_recover st.b1 st.b0 st.b1 st.b2 st.b3 _ h5)
    (lane4_block_recover st.b2 st.b0 st.b1 st.b2 st.b3 _ h5)
    (lane4_block_recover st.b3 st.b0 st.b1 st.b2 st.b3 _ h5)

theorem applyME16_injective {s t : Poseidon2State16} (h : applyME16 s = applyME16 t) : s = t := by
  have hInv := congrArg applyME16Inv h
  rwa [applyME16Inv_applyME16, applyME16Inv_applyME16] at hInv

theorem applyME16Inv_zero : applyME16Inv state16Zero = state16Zero := by decide

/-- **Non-singular width-16 external layer**: two-sided inverse, surjectivity, and no non-zero
    state in the kernel. -/
theorem applyME16_nonsingular (s y : Poseidon2State16) :
    applyME16Inv (applyME16 s) = s ∧
    applyME16 (applyME16Inv y) = y ∧
    (∃ z : Poseidon2State16, applyME16 z = y) ∧
    (s ≠ state16Zero → applyME16 s ≠ state16Zero) := by
  refine ⟨applyME16Inv_applyME16 s, applyME16_applyME16Inv y,
    ⟨applyME16Inv y, applyME16_applyME16Inv y⟩, ?_⟩
  intro hne hz
  apply hne
  have hInv := congrArg applyME16Inv hz
  rwa [applyME16Inv_applyME16, applyME16Inv_zero] at hInv

/-! ## 3. Round-Count Arithmetic for `d = 7`, `R_F = 8`, `R_P = 22` -/

/-- The deployed permutation runs `4 + 4` external and `22` internal rounds. -/
theorem poseidon2_deployed_round_counts :
    poseidon2InitialExtConsts.length + poseidon2TerminalExtConsts.length = 8 ∧
    poseidon2InternalConsts.length = 22 := by
  simp [poseidon2InitialExtConsts, poseidon2TerminalExtConsts, poseidon2InternalConsts]

/-- **Nominal degree threshold**: `7 ^ r` stays below `p` for every `r ≤ 22` and reaches `p` at
    `r = 23`, seven rounds before the `30`-round total. -/
theorem poseidon2_nominal_degree_threshold :
    (∀ r : Nat, r ≤ 22 → 7 ^ r < goldilocksPrime) ∧
    goldilocksPrime ≤ 7 ^ 23 ∧ 23 + 7 = 8 + 22 ∧
    goldilocksPrime < 2 ^ 84 ∧ 2 ^ 84 < 7 ^ (8 + 22) := by
  refine ⟨fun r hr => ?_, by decide, rfl, by decide, by decide⟩
  exact Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) hr) (by decide)

/-- The univariate degree alone stays below `2 ^ 85`: `7 ^ 30 > 2 ^ 128` is false, and `46`
    rounds would be the least count with `7 ^ r ≥ 2 ^ 128`. What exceeds `2 ^ 128` at `30` rounds
    is the square `(7 ^ 30) ^ 2`. -/
theorem tooth_univariate_degree_alone_below_two_pow_128 :
    7 ^ (8 + 22) < 2 ^ 85 ∧ 7 ^ 45 < 2 ^ 128 ∧ 2 ^ 128 ≤ 7 ^ 46 ∧
    2 ^ 128 < (7 ^ (8 + 22)) ^ 2 := by decide

/-- Interpolation round inequality `1 + a + b ≤ R_F + R_P` with `7 ^ a ≥ 2 ^ 64`
    (`a ≥ ⌈64 log_7 2⌉`) and `7 ^ b ≥ t` (`b ≥ ⌈log_7 t⌉`), together with the statistical floor
    `R_F ≥ 6`. -/
def Poseidon2InterpolationMargin (t rF rP : Nat) : Prop :=
  6 ≤ rF ∧ ∃ a b : Nat, 2 ^ 64 ≤ 7 ^ a ∧ t ≤ 7 ^ b ∧ 1 + a + b ≤ rF + rP

theorem poseidon2_interpolation_margin_width12 : Poseidon2InterpolationMargin 12 8 22 :=
  ⟨by decide, 23, 2, by decide, by decide, by decide⟩

theorem poseidon2_interpolation_margin_width16 : Poseidon2InterpolationMargin 16 8 22 :=
  ⟨by decide, 23, 2, by decide, by decide, by decide⟩

/-- Any witness of the margin needs `26` rounds once `t > 7`: the slack at `8 + 22` is `4`. -/
theorem poseidon2_interpolation_margin_needs_26 (t rF rP : Nat) (ht : 7 < t)
    (h : Poseidon2InterpolationMargin t rF rP) : 26 ≤ rF + rP := by
  obtain ⟨_, a, b, ha, hb, hsum⟩ := h
  have ha' : 23 ≤ a := Nat.le_of_not_lt (fun hlt =>
    Nat.not_lt.mpr ha (Nat.lt_of_le_of_lt
      (Nat.pow_le_pow_right (by decide) (Nat.le_of_lt_succ hlt)) (by decide)))
  have hb' : 2 ≤ b := Nat.le_of_not_lt (fun hlt => by
    have h7 : 7 ^ b ≤ 7 ^ 1 := Nat.pow_le_pow_right (by decide) (Nat.le_of_lt_succ hlt)
    omega)
  omega

theorem tooth_poseidon2_margin_fails_at_rp17 : ¬ Poseidon2InterpolationMargin 16 8 17 :=
  fun h => by
    have := poseidon2_interpolation_margin_needs_26 16 8 17 (by decide) h
    omega

namespace RoundPoly

theorem evalCoeffs_map_mul {R : Type} [LawfulCommRing R] (s : R) :
    ∀ (cs : List R) (x : R),
      evalCoeffs (cs.map (CommRingOps.mul s)) x = CommRingOps.mul s (evalCoeffs cs x)
  | [], x => by
    simp only [List.map_nil, evalCoeffs_nil]
    exact (LawfulCommRing.mul_zero s).symm
  | c :: cs, x => by
    simp only [List.map_cons, evalCoeffs_cons]
    rw [evalCoeffs_map_mul s cs x, LawfulCommRing.left_distrib,
        ← LawfulCommRing.mul_assoc x s, LawfulCommRing.mul_comm x s, LawfulCommRing.mul_assoc]

/-- Coefficients of `(X - s) · cs`. -/
def mulLinear {R : Type} [CommRingOps R] (s : R) (cs : List R) : List R :=
  subCoeffs (CommRingOps.zero :: cs) (cs.map (CommRingOps.mul s))

theorem evalCoeffs_mulLinear {R : Type} [LawfulCommRing R] (s : R) (cs : List R) (x : R) :
    evalCoeffs (mulLinear s cs) x = CommRingOps.mul (CommRingOps.sub x s) (evalCoeffs cs x) := by
  unfold mulLinear
  rw [evalCoeffs_sub, evalCoeffs_cons, evalCoeffs_map_mul, LawfulCommRing.zero_add,
      LawfulCommRing.sub_mul]

theorem mulLinear_length {R : Type} [CommRingOps R] (s : R) (cs : List R) :
    (mulLinear s cs).length = cs.length + 1 := by
  unfold mulLinear
  rw [subCoeffs_length]
  simp only [List.length_cons, List.length_map]
  exact Nat.max_eq_left (Nat.le_succ _)

/-- Coefficients of the vanishing polynomial `∏_{s ∈ S} (X - s)`. -/
def vanishingCoeffs {R : Type} [CommRingOps R] : List R → List R
  | [] => [CommRingOps.one]
  | s :: rest => mulLinear s (vanishingCoeffs rest)

theorem vanishingCoeffs_length {R : Type} [CommRingOps R] :
    ∀ S : List R, (vanishingCoeffs S).length = S.length + 1
  | [] => rfl
  | s :: rest => by
    simp only [vanishingCoeffs, mulLinear_length, vanishingCoeffs_length rest, List.length_cons]

theorem evalCoeffs_vanishingCoeffs_of_mem {R : Type} [LawfulCommRing R] :
    ∀ (S : List R) (x : R), x ∈ S → evalCoeffs (vanishingCoeffs S) x = CommRingOps.zero
  | [], _, h => by cases h
  | s :: rest, x, h => by
    simp only [vanishingCoeffs, evalCoeffs_mulLinear]
    rcases List.mem_cons.mp h with rfl | hRest
    · rw [LawfulCommRing.sub_self, LawfulCommRing.zero_mul]
    · rw [evalCoeffs_vanishingCoeffs_of_mem rest x hRest, LawfulCommRing.mul_zero]

theorem evalCoeffs_vanishingCoeffs_ne_zero {R : Type} [LawfulCommRing R] [NoZeroDivisors R]
    (hOne : (CommRingOps.one : R) ≠ CommRingOps.zero) :
    ∀ (S : List R) (x : R), x ∉ S → evalCoeffs (vanishingCoeffs S) x ≠ CommRingOps.zero
  | [], x, _ => by
    simp only [vanishingCoeffs, evalCoeffs_cons, evalCoeffs_nil]
    rw [LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    exact hOne
  | s :: rest, x, h => by
    simp only [vanishingCoeffs, evalCoeffs_mulLinear]
    intro hz
    rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hz with hx | hv
    · exact h (List.mem_cons.mpr (.inl (LawfulCommRing.sub_eq_zero_iff.mp hx)))
    · exact evalCoeffs_vanishingCoeffs_ne_zero hOne rest x
        (fun hm => h (List.mem_cons.mpr (.inr hm))) hv

end RoundPoly

/-- **Sample lower bound for univariate interpolation over `Goldilocks`**: for any sample set `S`
    and any point `x₀` outside it there is a polynomial with `|S| + 1` coefficients that vanishes
    on all of `S` and not at `x₀`. Adding it to a target changes the target off `S` only, so `|S|`
    evaluations do not determine a polynomial whose degree is at least `|S|`. -/
theorem univariate_interpolation_underdetermined (S : List Goldilocks) (x₀ : Goldilocks)
    (hx₀ : x₀ ∉ S) :
    ∃ cs : List Goldilocks, cs.length = S.length + 1 ∧
      (∀ s ∈ S, evalCoeffs cs s = Goldilocks.zero) ∧
      evalCoeffs cs x₀ ≠ Goldilocks.zero :=
  ⟨vanishingCoeffs S, vanishingCoeffs_length S,
    fun s hs => evalCoeffs_vanishingCoeffs_of_mem S s hs,
    evalCoeffs_vanishingCoeffs_ne_zero (R := Goldilocks) (gold_ne_of_val_ne (by decide)) S x₀ hx₀⟩

/-! ## 4. Two-Layer Hierarchical `Hem`: Root Verifier, Tree Extractor, Union Bound -/

def hemShardDomainTag : List UInt8 := "QSAG.HEM.SHARD/v1".toUTF8.toList

/-- Shard-scoped signing message: every field is length-framed by `encodeMultiFrame`. -/
def shardBoundMessage (shardId epochFloor msg : List UInt8) : List UInt8 :=
  encodeMultiFrame [hemShardDomainTag, shardId, epochFloor, msg]

theorem shardBoundMessage_injective {s₁ e₁ m₁ s₂ e₂ m₂ : List UInt8}
    (h : shardBoundMessage s₁ e₁ m₁ = shardBoundMessage s₂ e₂ m₂) :
    s₁ = s₂ ∧ e₁ = e₂ ∧ m₁ = m₂ := by
  have hList := encodeMultiFrame_injective h
  simp only [List.cons.injEq, and_true, true_and] at hList
  exact hList

/-- One regional shard certificate presented to the root verifier. -/
structure HemShardProof where
  shardId : List UInt8
  threshold : Nat
  inst : AggPublicInstance
  proof : SuccinctAggregateProof
  fs : List UInt8

/-- Registry row: a shard id together with its authorized quorum threshold, hash suite id,
    signature parameter profile, and custodian cluster's committee. -/
structure ShardRegistration where
  shardId : List UInt8
  threshold : Nat
  suiteId : List UInt8
  params : PqHashParams
  committee : List PqPublicKey
  deriving DecidableEq

/-- A shard policy row is well-formed when its required quorum threshold satisfies
    `1 ≤ threshold ≤ |committee|`. -/
def ShardRegistration.WellFormed (r : ShardRegistration) : Bool :=
  decide (1 ≤ r.threshold) && decide (r.threshold ≤ r.committee.length)

def HemShardProof.registration (s : HemShardProof) : ShardRegistration :=
  ⟨s.shardId, s.threshold, s.inst.suite.suiteId, s.inst.params, s.inst.committee⟩

/-- Canonical length-framed serialization of all 8 fields of `PqHashParams`. -/
def encodePqHashParams (p : PqHashParams) : List UInt8 :=
  encodeMultiFrame [
    leb128 p.w,
    leb128 p.ell1,
    leb128 p.subtreeHeight,
    leb128 p.numLayers,
    leb128 p.forsTrees,
    leb128 p.forsHeight,
    leb128 p.maxSigsLog2,
    [if p.statefulJorts then 1 else 0]
  ]

/-- Canonical length-framed serialization of all 5 fields of `ShardRegistration`. -/
def encodeRegistration (r : ShardRegistration) : List UInt8 :=
  encodeMultiFrame [
    r.shardId,
    leb128 r.threshold,
    r.suiteId,
    encodePqHashParams r.params,
    encodeMultiFrame (r.committee.map fun pk => encodeMultiFrame [pk.pkSeed, pk.pkRoot])
  ]

def encodeRegistry (rs : List ShardRegistration) : List UInt8 :=
  encodeMultiFrame (rs.map encodeRegistration)

private theorem leb128_injective {a b : Nat} (h : leb128 a = leb128 b) : a = b :=
  (leb128_prefix_inj (r₁ := []) (r₂ := []) (by simpa using h)).1

private theorem map_inj_of_inj {α β : Type} {f : α → β} (hf : ∀ a b, f a = f b → a = b) :
    ∀ {l l' : List α}, l.map f = l'.map f → l = l'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: l, b :: l', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [hf a b h.1, map_inj_of_inj hf h.2]

private theorem encodePk_injective (a b : PqPublicKey)
    (h : encodeMultiFrame [a.pkSeed, a.pkRoot] = encodeMultiFrame [b.pkSeed, b.pkRoot]) :
    a = b := by
  have h0 := encodeMultiFrame_injective h
  obtain ⟨hSeed, h1⟩ := List.cons.inj h0
  obtain ⟨hRoot, _⟩ := List.cons.inj h1
  cases a; cases b
  simp only at hSeed hRoot
  rw [hSeed, hRoot]

theorem encodePqHashParams_injective {a b : PqHashParams}
    (h : encodePqHashParams a = encodePqHashParams b) : a = b := by
  have h0 := encodeMultiFrame_injective h
  obtain ⟨hw, h1⟩ := List.cons.inj h0
  obtain ⟨hell, h2⟩ := List.cons.inj h1
  obtain ⟨hsub, h3⟩ := List.cons.inj h2
  obtain ⟨hlay, h4⟩ := List.cons.inj h3
  obtain ⟨hft, h5⟩ := List.cons.inj h4
  obtain ⟨hfh, h6⟩ := List.cons.inj h5
  obtain ⟨hmax, h7⟩ := List.cons.inj h6
  obtain ⟨hst, _⟩ := List.cons.inj h7
  have hb : a.statefulJorts = b.statefulJorts := by
    cases ha : a.statefulJorts <;> cases hb' : b.statefulJorts <;>
      simp [ha, hb'] at hst <;> rfl
  cases a; cases b
  simp only at hw hell hsub hlay hft hfh hmax hb
  rw [leb128_injective hw, leb128_injective hell, leb128_injective hsub,
      leb128_injective hlay, leb128_injective hft, leb128_injective hfh,
      leb128_injective hmax, hb]

theorem encodeRegistration_injective {a b : ShardRegistration}
    (h : encodeRegistration a = encodeRegistration b) : a = b := by
  have h0 := encodeMultiFrame_injective h
  obtain ⟨hSid, h1⟩ := List.cons.inj h0
  obtain ⟨hThr, h2⟩ := List.cons.inj h1
  obtain ⟨hSuite, h3⟩ := List.cons.inj h2
  obtain ⟨hParams, h4⟩ := List.cons.inj h3
  obtain ⟨hComRaw, _⟩ := List.cons.inj h4
  have hThrEq := leb128_injective hThr
  have hParamsEq := encodePqHashParams_injective hParams
  have hCom := map_inj_of_inj encodePk_injective (encodeMultiFrame_injective hComRaw)
  cases a; cases b
  simp only at hSid hThrEq hSuite hParamsEq hCom
  rw [hSid, hThrEq, hSuite, hParamsEq, hCom]

theorem encodeRegistry_injective {rs₁ rs₂ : List ShardRegistration}
    (h : encodeRegistry rs₁ = encodeRegistry rs₂) : rs₁ = rs₂ :=
  map_inj_of_inj (fun _ _ => encodeRegistration_injective) (encodeMultiFrame_injective h)

/-- Two distinct registries under one digest are a concrete collision of `H`. -/
def registryCollision (H : Hash) {digest : List UInt8} {claimed registry : List ShardRegistration}
    (hClaimed : H (encodeRegistry claimed) = digest) (hReg : H (encodeRegistry registry) = digest)
    (hNe : claimed ≠ registry) : HashCollisionWitness H :=
  ⟨encodeRegistry claimed, encodeRegistry registry,
    fun h => hNe (encodeRegistry_injective h), hClaimed.trans hReg.symm⟩

/-- Per-shard check: shard-scoped message, well-formed threshold (`1 ≤ threshold ≤ |committee|`),
    threshold met by the bitmap, and accepting succinct aggregate certificate. -/
def verifyHemShard (arith : RowArithmetization) (dom : WhirDomain)
    (epochFloor msg : List UInt8) (s : HemShardProof) : Bool :=
  decide (s.inst.message = shardBoundMessage s.shardId epochFloor msg) &&
  decide (1 ≤ s.threshold) &&
  decide (s.threshold ≤ s.inst.committee.length) &&
  decide (s.threshold ≤ bitmapPopcountSpec s.proof.agg.bitmap) &&
  verifySuccinctAggregate arith dom s.inst s.proof s.fs

def hierarchicalShardIds : List HemShardProof → List (List UInt8)
  | [] => []
  | s :: rest => s.shardId :: hierarchicalShardIds rest

def hierarchicalCommittee : List HemShardProof → List PqPublicKey
  | [] => []
  | s :: rest => s.inst.committee ++ hierarchicalCommittee rest

def hierarchicalClaimedWeight : List HemShardProof → Nat
  | [] => 0
  | s :: rest => bitmapPopcountSpec s.proof.agg.bitmap + hierarchicalClaimedWeight rest

def hierarchicalThresholdSum : List HemShardProof → Nat
  | [] => 0
  | s :: rest => s.threshold + hierarchicalThresholdSum rest

def registryThresholdSum : List ShardRegistration → Nat
  | [] => 0
  | r :: rest => r.threshold + registryThresholdSum rest

theorem hierarchicalThresholdSum_eq_registryThresholdSum :
    ∀ shards : List HemShardProof,
      hierarchicalThresholdSum shards =
        registryThresholdSum (shards.map HemShardProof.registration)
  | [] => rfl
  | s :: rest => by
    simp only [List.map_cons, hierarchicalThresholdSum, registryThresholdSum,
      HemShardProof.registration, hierarchicalThresholdSum_eq_registryThresholdSum rest]

/-- Root verifier of the two-layer hierarchy: registry commitment, pairwise-distinct shard ids,
    pairwise-disjoint duplicate-free committees, and every shard certificate. -/
def verifyHierarchicalHem (H : Hash) (arith : RowArithmetization) (dom : WhirDomain)
    (registryDigest epochFloor msg : List UInt8) (shards : List HemShardProof) : Bool :=
  decide (H (encodeRegistry (shards.map HemShardProof.registration)) = registryDigest) &&
  decide ((hierarchicalShardIds shards).Nodup) &&
  decide ((hierarchicalCommittee shards).Nodup) &&
  shards.all (verifyHemShard arith dom epochFloor msg)

abbrev verifyHemHierarchy := verifyHierarchicalHem

/-- Direct registered-policy root verifier: enforces `ShardRegistration.WellFormed` on every row
    and exact structural equality between `shards.map HemShardProof.registration` and `registry`. -/
def verifyHemHierarchyAgainstRegistry (arith : RowArithmetization) (dom : WhirDomain)
    (registry : List ShardRegistration) (epochFloor msg : List UInt8)
    (shards : List HemShardProof) : Bool :=
  registry.all ShardRegistration.WellFormed &&
  decide (shards.map HemShardProof.registration = registry) &&
  decide ((hierarchicalShardIds shards).Nodup) &&
  decide ((hierarchicalCommittee shards).Nodup) &&
  shards.all (verifyHemShard arith dom epochFloor msg)

theorem verifyHemShard_facts {arith : RowArithmetization} {dom : WhirDomain}
    {epochFloor msg : List UInt8} {s : HemShardProof}
    (h : verifyHemShard arith dom epochFloor msg s = true) :
    s.inst.message = shardBoundMessage s.shardId epochFloor msg ∧
    1 ≤ s.threshold ∧
    s.threshold ≤ s.inst.committee.length ∧
    s.threshold ≤ bitmapPopcountSpec s.proof.agg.bitmap ∧
    verifySuccinctAggregate arith dom s.inst s.proof s.fs = true := by
  unfold verifyHemShard at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem verifyHemShard_wellFormed {arith : RowArithmetization} {dom : WhirDomain}
    {epochFloor msg : List UInt8} {s : HemShardProof}
    (h : verifyHemShard arith dom epochFloor msg s = true) :
    s.registration.WellFormed = true := by
  have hF := verifyHemShard_facts h
  exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true hF.2.1, decide_eq_true hF.2.2.1⟩

theorem verifyHierarchicalHem_facts {H : Hash} {arith : RowArithmetization} {dom : WhirDomain}
    {registryDigest epochFloor msg : List UInt8} {shards : List HemShardProof}
    (h : verifyHierarchicalHem H arith dom registryDigest epochFloor msg shards = true) :
    H (encodeRegistry (shards.map HemShardProof.registration)) = registryDigest ∧
    (hierarchicalShardIds shards).Nodup ∧
    (hierarchicalCommittee shards).Nodup ∧
    ∀ s ∈ shards, verifyHemShard arith dom epochFloor msg s = true := by
  unfold verifyHierarchicalHem at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem verifyHemHierarchyAgainstRegistry_facts {arith : RowArithmetization} {dom : WhirDomain}
    {registry : List ShardRegistration} {epochFloor msg : List UInt8}
    {shards : List HemShardProof}
    (h : verifyHemHierarchyAgainstRegistry arith dom registry epochFloor msg shards = true) :
    (∀ r ∈ registry, r.WellFormed = true) ∧
    shards.map HemShardProof.registration = registry ∧
    (hierarchicalShardIds shards).Nodup ∧
    (hierarchicalCommittee shards).Nodup ∧
    ∀ s ∈ shards, verifyHemShard arith dom epochFloor msg s = true := by
  unfold verifyHemHierarchyAgainstRegistry at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem verifyHemHierarchyAgainstRegistry_implies_verifyHierarchicalHem (H : Hash)
    {arith : RowArithmetization} {dom : WhirDomain}
    {registry : List ShardRegistration} {registryDigest epochFloor msg : List UInt8}
    {shards : List HemShardProof}
    (hReg : H (encodeRegistry registry) = registryDigest)
    (h : verifyHemHierarchyAgainstRegistry arith dom registry epochFloor msg shards = true) :
    verifyHierarchicalHem H arith dom registryDigest epochFloor msg shards = true := by
  have hF := verifyHemHierarchyAgainstRegistry_facts h
  unfold verifyHierarchicalHem
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  rw [hF.2.1]
  exact ⟨⟨⟨hReg, hF.2.2.1⟩, hF.2.2.2.1⟩, hF.2.2.2.2⟩

/-- Signing slot of the hierarchy: one committee key of one shard. -/
structure HemSlot where
  shardId : List UInt8
  suite : TweakableHashSuite
  params : PqHashParams
  pk : PqPublicKey

/-- An extracted signature, valid for its slot on the shard-scoped message. -/
structure ExtractedQuorumSig (epochFloor msg : List UInt8) where
  slot : HemSlot
  sig : PqHashSig
  valid : verifyPqHashSig slot.suite slot.params slot.pk
    (shardBoundMessage slot.shardId epochFloor msg) sig = true

def activeKeys : List PqPublicKey → SignerBitmapSpec → List PqPublicKey
  | pk :: pks, b :: bs => if b then pk :: activeKeys pks bs else activeKeys pks bs
  | _, _ => []

def shardActiveSlots (s : HemShardProof) : List HemSlot :=
  (activeKeys s.inst.committee s.proof.agg.bitmap).map
    (HemSlot.mk s.shardId s.inst.suite s.inst.params)

def hierarchicalActiveSlots : List HemShardProof → List HemSlot
  | [] => []
  | s :: rest => shardActiveSlots s ++ hierarchicalActiveSlots rest

theorem activeKeys_sublist :
    ∀ (pks : List PqPublicKey) (bs : SignerBitmapSpec), (activeKeys pks bs).Sublist pks
  | [], _ => by simp [activeKeys]
  | _ :: _, [] => by simp [activeKeys]
  | pk :: pks, true :: bs => by
    simp only [activeKeys, ite_true]
    exact (activeKeys_sublist pks bs).cons_cons pk
  | pk :: pks, false :: bs => by
    simp only [activeKeys, Bool.false_eq_true, ite_false]
    exact (activeKeys_sublist pks bs).cons pk

theorem hierarchicalActiveSlots_pk_sublist :
    ∀ shards : List HemShardProof,
      ((hierarchicalActiveSlots shards).map HemSlot.pk).Sublist (hierarchicalCommittee shards)
  | [] => by simp [hierarchicalActiveSlots, hierarchicalCommittee]
  | s :: rest => by
    simp only [hierarchicalActiveSlots, hierarchicalCommittee, List.map_append]
    refine List.Sublist.append ?_ (hierarchicalActiveSlots_pk_sublist rest)
    have hMap : (shardActiveSlots s).map HemSlot.pk =
        activeKeys s.inst.committee s.proof.agg.bitmap := by
      unfold shardActiveSlots
      rw [List.map_map]
      exact List.map_id _
    rw [hMap]
    exact activeKeys_sublist _ _

/-- Signatures of the active signers of one shard, read off an all-active-signers check. -/
def collectShardSigs (epochFloor msg shardId : List UInt8) (suite : TweakableHashSuite)
    (params : PqHashParams) :
    (pks : List PqPublicKey) → (bs : SignerBitmapSpec) → (sigs : List PqHashSig) →
    checkAllActiveSigners suite params (shardBoundMessage shardId epochFloor msg) pks bs sigs
      = true →
    List (ExtractedQuorumSig epochFloor msg)
  | [], [], _, _ => []
  | [], _ :: _, _, h => absurd h (by simp [checkAllActiveSigners])
  | _ :: _, [], _, h => absurd h (by simp [checkAllActiveSigners])
  | _ :: _, _ :: _, [], h => absurd h (by simp [checkAllActiveSigners])
  | pk :: pks, true :: bs, sig :: sigs, h =>
    have h' : verifyPqHashSig suite params pk (shardBoundMessage shardId epochFloor msg) sig = true ∧
        checkAllActiveSigners suite params (shardBoundMessage shardId epochFloor msg) pks bs sigs
          = true := by
      simpa [checkAllActiveSigners] using h
    ⟨⟨shardId, suite, params, pk⟩, sig, h'.1⟩ ::
      collectShardSigs epochFloor msg shardId suite params pks bs sigs h'.2
  | _ :: pks, false :: bs, _ :: sigs, h =>
    collectShardSigs epochFloor msg shardId suite params pks bs sigs
      (by simpa [checkAllActiveSigners] using h)

theorem collectShardSigs_slots (epochFloor msg shardId : List UInt8) (suite : TweakableHashSuite)
    (params : PqHashParams) :
    ∀ (pks : List PqPublicKey) (bs : SignerBitmapSpec) (sigs : List PqHashSig)
      (h : checkAllActiveSigners suite params (shardBoundMessage shardId epochFloor msg) pks bs sigs
        = true),
      (collectShardSigs epochFloor msg shardId suite params pks bs sigs h).map (·.slot) =
        (activeKeys pks bs).map (HemSlot.mk shardId suite params) ∧
      (collectShardSigs epochFloor msg shardId suite params pks bs sigs h).length =
        bitmapPopcountSpec bs
  | [], [], _, _ => by simp [collectShardSigs, activeKeys, bitmapPopcountSpec]
  | [], _ :: _, _, h => absurd h (by simp [checkAllActiveSigners])
  | _ :: _, [], _, h => absurd h (by simp [checkAllActiveSigners])
  | _ :: _, _ :: _, [], h => absurd h (by simp [checkAllActiveSigners])
  | pk :: pks, true :: bs, sig :: sigs, h => by
    have h' : checkAllActiveSigners suite params (shardBoundMessage shardId epochFloor msg)
        pks bs sigs = true := by
      have := h
      simp [checkAllActiveSigners] at this
      exact this.2
    have ih := collectShardSigs_slots epochFloor msg shardId suite params pks bs sigs h'
    refine ⟨?_, ?_⟩
    · simp only [collectShardSigs, activeKeys, ite_true, List.map_cons, ih.1]
    · have h2 := ih.2
      simp only [collectShardSigs, bitmapPopcountSpec, ite_true, List.length_cons]
      omega
  | _ :: pks, false :: bs, _ :: sigs, h => by
    have h' : checkAllActiveSigners suite params (shardBoundMessage shardId epochFloor msg)
        pks bs sigs = true := by
      simpa [checkAllActiveSigners] using h
    have ih := collectShardSigs_slots epochFloor msg shardId suite params pks bs sigs h'
    refine ⟨?_, ?_⟩
    · simp only [collectShardSigs, activeKeys, Bool.false_eq_true, ite_false]
      exact ih.1
    · have h2 := ih.2
      simp only [collectShardSigs, bitmapPopcountSpec, Bool.false_eq_true, ite_false]
      omega

/-- Extraction context of one shard: its certificate with the lawful arithmetization and the
    committed tables the single-layer extractor reads. -/
structure HemShardEnv (arith : RowArithmetization) (dom : WhirDomain) where
  shard : HemShardProof
  law : arith.Lawful dom shard.inst
  view : SuccinctExtractionView
  bound : StagesBound view.authPath dom.stages view.allTables shard.proof.stages

/-- Break witness of the single-layer extractor for one shard certificate. -/
@[expose] def HemShardBreak (arith : RowArithmetization) (dom : WhirDomain)
    (proof : SuccinctAggregateProof) (view : SuccinctExtractionView) : Type :=
  PSum (SumcheckSchwartzZippelHit 8 proof.agg.roundPolys
      (adaptivePolys (arith.honestRound ((view.allTables.headD []).headD [])) proof.agg.challenges)
      proof.agg.challenges)
    (PSum (HashCollisionWitness pcsMerkleHash)
      (PSum (WhirStageQueryMiss proof.finalWord dom view.allTables proof)
        (WhirProximityHit arith dom proof.finalWord view.allTables proof)))

/-- Single-shard step: the active signers' signatures on the shard-scoped message, or the
    single-layer break witness. -/
def extractShardQuorum (arith : RowArithmetization) (dom : WhirDomain)
    (epochFloor msg : List UInt8) (e : HemShardEnv arith dom)
    (h : verifyHemShard arith dom epochFloor msg e.shard = true) :
    PSum { sigs : List (ExtractedQuorumSig epochFloor msg) //
        sigs.map (·.slot) = shardActiveSlots e.shard ∧
        sigs.length = bitmapPopcountSpec e.shard.proof.agg.bitmap }
      (HemShardBreak arith dom e.shard.proof e.view) :=
  have hF := verifyHemShard_facts h
  match succinct_aggregation_knowledge_soundness arith dom e.shard.inst e.law e.shard.proof
      e.shard.fs e.view hF.2.2.2.2 e.bound with
  | .inl ⟨_, hAll⟩ =>
    have hAll' : checkAllActiveSigners e.shard.inst.suite e.shard.inst.params
        (shardBoundMessage e.shard.shardId epochFloor msg) e.shard.inst.committee
        e.shard.proof.agg.bitmap
        (arith.decodeSigs ((e.view.allTables.headD []).headD [])) = true := by
      rw [← hF.1]; exact hAll
    .inl ⟨collectShardSigs epochFloor msg e.shard.shardId e.shard.inst.suite e.shard.inst.params
        e.shard.inst.committee e.shard.proof.agg.bitmap _ hAll',
      collectShardSigs_slots epochFloor msg e.shard.shardId e.shard.inst.suite
        e.shard.inst.params _ _ _ hAll'⟩
  | .inr brk => .inr brk

/-- Shard-by-shard tree walk: all shards' signatures, or the first shard index with a break. -/
def extractShardList (arith : RowArithmetization) (dom : WhirDomain)
    (epochFloor msg : List UInt8) :
    (envs : List (HemShardEnv arith dom)) →
    (∀ e ∈ envs, verifyHemShard arith dom epochFloor msg e.shard = true) →
    PSum { sigs : List (ExtractedQuorumSig epochFloor msg) //
        sigs.map (·.slot) = hierarchicalActiveSlots (envs.map (·.shard)) ∧
        sigs.length = hierarchicalClaimedWeight (envs.map (·.shard)) }
      (Σ j : Fin envs.length,
        HemShardBreak arith dom (envs.get j).shard.proof (envs.get j).view)
  | [], _ => .inl ⟨[], rfl, rfl⟩
  | e :: es, h =>
    match extractShardQuorum arith dom epochFloor msg e (h e (List.mem_cons_self ..)) with
    | .inr brk => .inr ⟨⟨0, Nat.succ_pos _⟩, brk⟩
    | .inl ⟨s0, h0⟩ =>
      match extractShardList arith dom epochFloor msg es
          (fun e' he' => h e' (List.mem_cons_of_mem _ he')) with
      | .inr ⟨⟨j, hj⟩, brk⟩ => .inr ⟨⟨j + 1, Nat.succ_lt_succ hj⟩, brk⟩
      | .inl ⟨ss, hs⟩ => .inl ⟨s0 ++ ss, by
          refine ⟨?_, ?_⟩
          · simp only [List.map_cons, List.map_append, hierarchicalActiveSlots, h0.1, hs.1]
          · have h1 := h0.2
            have h2 := hs.2
            simp only [List.map_cons, hierarchicalClaimedWeight, List.length_append]
            omega⟩

theorem hierarchicalThresholdSum_le_claimedWeight {arith : RowArithmetization} {dom : WhirDomain}
    {epochFloor msg : List UInt8} :
    ∀ shards : List HemShardProof,
      (∀ s ∈ shards, verifyHemShard arith dom epochFloor msg s = true) →
      hierarchicalThresholdSum shards ≤ hierarchicalClaimedWeight shards
  | [], _ => Nat.le_refl _
  | s :: rest, h => by
    have hs := (verifyHemShard_facts (h s (List.mem_cons_self ..))).2.2.2.1
    have ih := hierarchicalThresholdSum_le_claimedWeight rest
      (fun s' hs' => h s' (List.mem_cons_of_mem _ hs'))
    simp only [hierarchicalThresholdSum, hierarchicalClaimedWeight]
    omega

/-- Constructive policy-binding theorem for `verifyHierarchicalHem`: under an authenticated
    registry digest `H (encodeRegistry registry) = registryDigest`, acceptance either yields a
    concrete `HashCollisionWitness H`, or guarantees that `verifyHemHierarchyAgainstRegistry`
    accepts, every shard's `(shardId, threshold, suiteId, params, committee)` equals its registered
    row in `registry` with `1 ≤ threshold ≤ |committee|`, and
    `hierarchicalThresholdSum shards = registryThresholdSum registry ≤ hierarchicalClaimedWeight shards`. -/
def verifyHierarchicalHem_authenticates_registry (H : Hash) (arith : RowArithmetization)
    (dom : WhirDomain) (registryDigest epochFloor msg : List UInt8)
    (registry : List ShardRegistration)
    (hReg : H (encodeRegistry registry) = registryDigest)
    (shards : List HemShardProof)
    (hAccept : verifyHierarchicalHem H arith dom registryDigest epochFloor msg shards = true) :
    PSum
      (PLift (verifyHemHierarchyAgainstRegistry arith dom registry epochFloor msg shards = true ∧
        shards.map HemShardProof.registration = registry ∧
        (∀ r ∈ registry, r.WellFormed = true ∧ 1 ≤ r.threshold ∧ r.threshold ≤ r.committee.length) ∧
        hierarchicalThresholdSum shards = registryThresholdSum registry ∧
        registryThresholdSum registry ≤ hierarchicalClaimedWeight shards))
      (HashCollisionWitness H) :=
  have hF := verifyHierarchicalHem_facts hAccept
  if hEq : shards.map HemShardProof.registration = registry then
    .inl ⟨by
      have hWf : ∀ r ∈ registry,
          r.WellFormed = true ∧ 1 ≤ r.threshold ∧ r.threshold ≤ r.committee.length := by
        intro r hr
        rw [← hEq] at hr
        obtain ⟨s, hsMem, rfl⟩ := List.mem_map.mp hr
        have hsF := verifyHemShard_facts (hF.2.2.2 s hsMem)
        exact ⟨verifyHemShard_wellFormed (hF.2.2.2 s hsMem), hsF.2.1, hsF.2.2.1⟩
      have hSumEq : hierarchicalThresholdSum shards = registryThresholdSum registry := by
        rw [hierarchicalThresholdSum_eq_registryThresholdSum, hEq]
      have hSumLe : registryThresholdSum registry ≤ hierarchicalClaimedWeight shards := by
        rw [← hSumEq]
        exact hierarchicalThresholdSum_le_claimedWeight shards hF.2.2.2
      have hAgainst :
          verifyHemHierarchyAgainstRegistry arith dom registry epochFloor msg shards = true := by
        unfold verifyHemHierarchyAgainstRegistry
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
        exact ⟨⟨⟨⟨fun r hr => (hWf r hr).1, hEq⟩, hF.2.1⟩, hF.2.2.1⟩, hF.2.2.2⟩
      exact ⟨hAgainst, hEq, hWf, hSumEq, hSumLe⟩⟩
  else
    .inr (registryCollision H hF.1 hReg hEq)

/-- Left outcome of the tree extractor: one valid signature per active slot of every shard, for
    exactly the registered policies (`shardId`, `threshold`, `suiteId`, `params`, `committee`). -/
structure HierarchicalQuorumWitness (epochFloor msg : List UInt8)
    (registry : List ShardRegistration) (shards : List HemShardProof) where
  sigs : List (ExtractedQuorumSig epochFloor msg)
  slots_eq : sigs.map (·.slot) = hierarchicalActiveSlots shards
  weight_eq : sigs.length = hierarchicalClaimedWeight shards
  registry_eq : shards.map HemShardProof.registration = registry

/-- Right outcome: a registry hash collision at the root, or a shard index with a single-layer
    break witness. -/
@[expose] def HemHierarchyBreak (H : Hash) (arith : RowArithmetization) (dom : WhirDomain)
    (envs : List (HemShardEnv arith dom)) : Type :=
  PSum (HashCollisionWitness H)
    (Σ j : Fin envs.length, HemShardBreak arith dom (envs.get j).shard.proof (envs.get j).view)

/-- **Two-layer tree witness extractor (`extractHierarchicalHemQuorums`)**: from an accepting
    root verification against a committed registry, returns the signatures of all active signers
    of all shards, or a `HemHierarchyBreak`. -/
def extractHierarchicalHemQuorums (H : Hash) (arith : RowArithmetization) (dom : WhirDomain)
    (registryDigest epochFloor msg : List UInt8) (registry : List ShardRegistration)
    (hReg : H (encodeRegistry registry) = registryDigest)
    (envs : List (HemShardEnv arith dom))
    (hAccept : verifyHierarchicalHem H arith dom registryDigest epochFloor msg
      (envs.map (·.shard)) = true) :
    PSum (HierarchicalQuorumWitness epochFloor msg registry (envs.map (·.shard)))
      (HemHierarchyBreak H arith dom envs) :=
  have hF := verifyHierarchicalHem_facts hAccept
  if hEq : (envs.map (·.shard)).map HemShardProof.registration = registry then
    match extractShardList arith dom epochFloor msg envs
        (fun e he => hF.2.2.2 e.shard (List.mem_map.mpr ⟨e, he, rfl⟩)) with
    | .inl ⟨sigs, hSlots, hLen⟩ => .inl ⟨sigs, hSlots, hLen, hEq⟩
    | .inr brk => .inr (.inr brk)
  else
    .inr (.inl (registryCollision H hF.1 hReg hEq))

/-- **Two-layer hierarchical knowledge soundness
    (`recursive_hem_two_layer_knowledge_soundness`)**: an accepting root verification against a
    committed registry yields signatures `sigs` with one entry per active slot, at least
    `registryThresholdSum registry` (`= Σ_j K_j`) of them, under pairwise-distinct public keys
    taken from the registered committees with well-formed thresholds; otherwise there is a registry
    hash collision or a shard index with a single-layer break. -/
theorem recursive_hem_two_layer_knowledge_soundness (H : Hash) (arith : RowArithmetization)
    (dom : WhirDomain) (registryDigest epochFloor msg : List UInt8)
    (registry : List ShardRegistration) (hReg : H (encodeRegistry registry) = registryDigest)
    (envs : List (HemShardEnv arith dom))
    (hAccept : verifyHierarchicalHem H arith dom registryDigest epochFloor msg
      (envs.map (·.shard)) = true) :
    (∃ sigs : List (ExtractedQuorumSig epochFloor msg),
      sigs.map (·.slot) = hierarchicalActiveSlots (envs.map (·.shard)) ∧
      sigs.length = hierarchicalClaimedWeight (envs.map (·.shard)) ∧
      hierarchicalThresholdSum (envs.map (·.shard)) = registryThresholdSum registry ∧
      registryThresholdSum registry ≤ sigs.length ∧
      (sigs.map (·.slot.pk)).Nodup ∧
      (∀ r ∈ registry, r.WellFormed = true) ∧
      (envs.map (·.shard)).map HemShardProof.registration = registry) ∨
    Nonempty (HemHierarchyBreak H arith dom envs) := by
  have hF := verifyHierarchicalHem_facts hAccept
  match extractHierarchicalHemQuorums H arith dom registryDigest epochFloor msg registry hReg
      envs hAccept with
  | .inr brk => exact .inr ⟨brk⟩
  | .inl w =>
    have hSumEq :
        hierarchicalThresholdSum (envs.map (·.shard)) = registryThresholdSum registry := by
      rw [hierarchicalThresholdSum_eq_registryThresholdSum, w.registry_eq]
    refine .inl ⟨w.sigs, w.slots_eq, w.weight_eq, hSumEq, ?_, ?_, ?_, w.registry_eq⟩
    · rw [w.weight_eq, ← hSumEq]
      exact hierarchicalThresholdSum_le_claimedWeight _ hF.2.2.2
    · have hMap : w.sigs.map (·.slot.pk) = (w.sigs.map (·.slot)).map HemSlot.pk := by
        rw [List.map_map]; rfl
      rw [hMap, w.slots_eq]
      exact (hierarchicalActiveSlots_pk_sublist _).nodup hF.2.2.1
    · intro r hr
      rw [← w.registry_eq] at hr
      obtain ⟨s, hsMem, rfl⟩ := List.mem_map.mp hr
      exact verifyHemShard_wellFormed (hF.2.2.2 s hsMem)

/-! ### Prover commitment-opening transcript extraction (`StagesBound` grounding & query cost) -/

/-- Additional Merkle duet opening collected from a rewound prover run at `(stagePos, layer, cosetIdx)`. -/
structure RewoundDuetOpening where
  stagePos : Nat
  layer : Nat
  cosetIdx : Nat
  opening : FoldLayerOpening

/-- Prover commitment-opening transcript for one WHIR proof: `stageLayerOpenings[pos][layer][g]`
    records the prover's Merkle duet opening for coset `g` at `(stagePos = pos, layer)`, and
    `rewoundOpenings` records any auxiliary coset openings from rewound prover runs against the
    same committed Merkle roots. Contains zero unproved `Prop` assumptions. -/
structure CommittedTableTranscript where
  stageLayerOpenings : List (List (List FoldLayerOpening))
  rewoundOpenings : List RewoundDuetOpening := []

/-- Shard prover extraction bundle pairing a shard certificate with its `CommittedTableTranscript`. -/
structure ShardProverTranscript (arith : RowArithmetization) (dom : WhirDomain) where
  shard : HemShardProof
  law : arith.Lawful dom shard.inst
  transcript : CommittedTableTranscript

/-- Number of coset duet openings required across `foldLayers` intra-stage folding layers
    starting from `groups` initial cosets. -/
def stageLayerQueryCost : Nat → Nat → Nat
  | _, 0 => 0
  | groups, k + 1 => groups + stageLayerQueryCost (groups / 2) k

/-- Number of coset duet openings required to sweep all folding layers of stage `sdom`. -/
def stageTranscriptQueryCost (sdom : WhirStageDomain) : Nat :=
  stageLayerQueryCost sdom.groups0 sdom.foldLayers

/-- Number of coset duet openings required to sweep every stage in `dom`. -/
def domainTranscriptQueryCost (dom : WhirDomain) : Nat :=
  dom.stages.foldr (fun sdom acc => stageTranscriptQueryCost sdom + acc) 0

/-- Total base coset-sweep opening cost across `numShards` regional shards on `dom`. -/
def hierarchyTranscriptQueryCost (dom : WhirDomain) (numShards : Nat) : Nat :=
  numShards * domainTranscriptQueryCost dom

def layerOpeningsCount : List (List FoldLayerOpening) → Nat
  | [] => 0
  | ops :: rest => ops.length + layerOpeningsCount rest

def transcriptSweepOpeningCount (tr : CommittedTableTranscript) : Nat :=
  tr.stageLayerOpenings.foldr (fun stOps acc => layerOpeningsCount stOps + acc) 0

def transcriptTotalOpeningCount (tr : CommittedTableTranscript) : Nat :=
  transcriptSweepOpeningCount tr + tr.rewoundOpenings.length

def hierarchySweepOpeningCount {arith : RowArithmetization} {dom : WhirDomain}
    (trs : List (ShardProverTranscript arith dom)) : Nat :=
  trs.foldr (fun t acc => transcriptSweepOpeningCount t.transcript + acc) 0

def defaultFoldOpening : FoldLayerOpening :=
  ⟨GoldilocksExt4.zero, GoldilocksExt4.zero, []⟩

def layerGroupsAt : Nat → Nat → Nat
  | groups, 0 => groups
  | groups, l + 1 => layerGroupsAt (groups / 2) l

/-- Executable check that `op` is a valid Merkle duet opening at `(stageIdx, layer, g)` to `root`. -/
def verifyDuetCosetOpening (stageIdx layer groups : Nat) (root : List UInt8)
    (g : Nat) (op : FoldLayerOpening) : Bool :=
  decide (op.path.length = merkleDepth groups) &&
  decide (merklePathRoot pcsMerkleHash
    (pcsMerkleHash (duetLeafFrame stageIdx layer g op.v0 op.v1)) g op.path = root)

def verifyLayerSweepAux (stageIdx layer groups : Nat) (root : List UInt8) :
    Nat → List FoldLayerOpening → Bool
  | _, [] => true
  | g, op :: ops =>
    verifyDuetCosetOpening stageIdx layer groups root g op &&
    verifyLayerSweepAux stageIdx layer groups root (g + 1) ops

def verifyLayerSweep (stageIdx layer groups : Nat) (root : List UInt8)
    (ops : List FoldLayerOpening) : Bool :=
  decide (ops.length = groups) &&
  verifyLayerSweepAux stageIdx layer groups root 0 ops

def verifyStageLayerSweeps (stageIdx : Nat) :
    Nat → Nat → List (List FoldLayerOpening) → List (List UInt8) → Bool
  | _, _, [], [] => true
  | layer, groups, ops :: restOps, root :: roots =>
    verifyLayerSweep stageIdx layer groups root ops &&
    verifyStageLayerSweeps stageIdx (layer + 1) (groups / 2) restOps roots
  | _, _, _, _ => false

def verifyAllStageSweeps :
    List WhirStageDomain → List (List (List FoldLayerOpening)) → List WhirStageProof → Bool
  | [], [], [] => true
  | sdom :: sdoms, stOps :: restOps, sp :: sps =>
    decide (stOps ≠ []) &&
    verifyStageLayerSweeps sdom.stageIdx 0 sdom.groups0 stOps (stageAllRoots sp) &&
    verifyAllStageSweeps sdoms restOps sps
  | _, _, _ => false

def verifyRewoundOpening (dom : WhirDomain) (proof : SuccinctAggregateProof)
    (ro : RewoundDuetOpening) : Bool :=
  match dom.stages[ro.stagePos]?, proof.stages[ro.stagePos]? with
  | some sdom, some sp =>
    match (stageAllRoots sp)[ro.layer]? with
    | some root =>
      let groups := layerGroupsAt sdom.groups0 ro.layer
      decide (ro.cosetIdx < groups) &&
      verifyDuetCosetOpening sdom.stageIdx ro.layer groups root ro.cosetIdx ro.opening
    | none => false
  | _, _ => false

/-- Executable Boolean acceptor for a prover commitment-opening transcript against `(dom, proof)`. -/
def verifyCommittedTableTranscript (dom : WhirDomain) (proof : SuccinctAggregateProof)
    (tr : CommittedTableTranscript) : Bool :=
  decide ((dom.stages.map (·.stageIdx)).Nodup) &&
  verifyAllStageSweeps dom.stages tr.stageLayerOpenings proof.stages &&
  tr.rewoundOpenings.all (verifyRewoundOpening dom proof)

/-- Reconstruct the length-`2 * ops.length` layer codeword from its `ops.length` coset duet openings. -/
def reconstructLayerTable (ops : List FoldLayerOpening) : List GoldilocksExt4 :=
  ops.map (·.v0) ++ ops.map (·.v1)

def lookupStageOpenings :
    List WhirStageDomain → List (List (List FoldLayerOpening)) → Nat →
      List (List FoldLayerOpening)
  | sdom :: sdoms, stOps :: restOps, stageIdx =>
    if sdom.stageIdx = stageIdx then stOps
    else lookupStageOpenings sdoms restOps stageIdx
  | _, _, _ => []

def transcriptAuthPath (dom : WhirDomain) (tr : CommittedTableTranscript)
    (stageIdx layer g : Nat) : List (List UInt8) :=
  (((lookupStageOpenings dom.stages tr.stageLayerOpenings stageIdx).getD layer []).getD
    g defaultFoldOpening).path

/-- Reconstruct the `SuccinctExtractionView` directly from a `CommittedTableTranscript`. -/
def reconstructSuccinctView (dom : WhirDomain) (tr : CommittedTableTranscript) :
    SuccinctExtractionView where
  allTables := tr.stageLayerOpenings.map (fun stOps => stOps.map reconstructLayerTable)
  authPath := transcriptAuthPath dom tr

private theorem getD_append_left {α : Type} (d : α) :
    ∀ (xs ys : List α) (i : Nat), i < xs.length → (xs ++ ys).getD i d = xs.getD i d
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, _, 0, _ => rfl
  | _ :: xs, ys, i + 1, h => getD_append_left d xs ys i (Nat.lt_of_succ_lt_succ h)

private theorem getD_append_right {α : Type} (d : α) :
    ∀ (xs ys : List α) (i : Nat), (xs ++ ys).getD (i + xs.length) d = ys.getD i d
  | [], _, _ => rfl
  | _ :: xs, ys, i => by
    have hEq : i + (xs.length + 1) = (i + xs.length) + 1 := by omega
    rw [List.cons_append, List.length_cons, hEq]
    exact getD_append_right d xs ys i

private theorem getD_map_of_lt {α β : Type} (f : α → β) (da : α) (db : β) :
    ∀ (xs : List α) (i : Nat), i < xs.length → (xs.map f).getD i db = f (xs.getD i da)
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: xs, i + 1, h => getD_map_of_lt f da db xs i (Nat.lt_of_succ_lt_succ h)

private theorem reconstructLayerTable_getD_left (ops : List FoldLayerOpening) (g : Nat)
    (hg : g < ops.length) :
    (reconstructLayerTable ops).getD g CommRingOps.zero =
      (ops.getD g defaultFoldOpening).v0 := by
  unfold reconstructLayerTable
  rw [getD_append_left _ _ _ g (by simpa using hg)]
  exact getD_map_of_lt (·.v0) defaultFoldOpening CommRingOps.zero ops g hg

private theorem reconstructLayerTable_getD_right (ops : List FoldLayerOpening) (g : Nat)
    (hg : g < ops.length) :
    (reconstructLayerTable ops).getD (g + ops.length) CommRingOps.zero =
      (ops.getD g defaultFoldOpening).v1 := by
  unfold reconstructLayerTable
  have hLen : (ops.map (·.v0)).length = ops.length := List.length_map _
  rw [← hLen, getD_append_right]
  exact getD_map_of_lt (·.v1) defaultFoldOpening CommRingOps.zero ops g hg

private theorem verifyLayerSweepAux_getD {stageIdx layer groups : Nat} {root : List UInt8} :
    ∀ (ops : List FoldLayerOpening) (base i : Nat),
      i < ops.length →
      verifyLayerSweepAux stageIdx layer groups root base ops = true →
      verifyDuetCosetOpening stageIdx layer groups root (base + i)
        (ops.getD i defaultFoldOpening) = true
  | [], _, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | _ :: _, base, 0, _, h => by
    rw [Nat.add_zero]
    exact (Bool.and_eq_true_iff.mp h).1
  | _ :: ops, base, i + 1, hi, h => by
    have ih := verifyLayerSweepAux_getD ops (base + 1) i (Nat.lt_of_succ_lt_succ hi)
      (Bool.and_eq_true_iff.mp h).2
    have hAdd : base + (i + 1) = (base + 1) + i := by omega
    rw [hAdd]
    exact ih

private theorem verifyLayerSweep_at {stageIdx layer groups : Nat} {root : List UInt8}
    {ops : List FoldLayerOpening}
    (h : verifyLayerSweep stageIdx layer groups root ops = true) :
    ops.length = groups ∧
    ∀ g, g < groups →
      verifyDuetCosetOpening stageIdx layer groups root g (ops.getD g defaultFoldOpening) = true := by
  obtain ⟨hLen, hAux⟩ := Bool.and_eq_true_iff.mp h
  have hEq : ops.length = groups := of_decide_eq_true hLen
  refine ⟨hEq, fun g hg => ?_⟩
  simpa only [Nat.zero_add] using
    verifyLayerSweepAux_getD ops 0 g (hEq.symm ▸ hg) hAux

private theorem verifyDuetCosetOpening_facts {stageIdx layer groups : Nat} {root : List UInt8}
    {g : Nat} {op : FoldLayerOpening}
    (h : verifyDuetCosetOpening stageIdx layer groups root g op = true) :
    op.path.length = merkleDepth groups ∧
    merklePathRoot pcsMerkleHash
      (pcsMerkleHash (duetLeafFrame stageIdx layer g op.v0 op.v1)) g op.path = root := by
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
  exact ⟨of_decide_eq_true h1, of_decide_eq_true h2⟩

private theorem stageLayersBound_of_sweeps (authPath : Nat → Nat → Nat → List (List UInt8))
    (stageIdx : Nat) :
    ∀ (stOps : List (List FoldLayerOpening)) (roots : List (List UInt8)) (baseLayer groups : Nat),
      (∀ k g, authPath stageIdx (baseLayer + k) g =
        ((stOps.getD k []).getD g defaultFoldOpening).path) →
      verifyStageLayerSweeps stageIdx baseLayer groups stOps roots = true →
      StageLayersBound authPath stageIdx baseLayer groups (stOps.map reconstructLayerTable) roots
  | [], [], _, _, _, _ => trivial
  | [], _ :: _, _, _, _, h => absurd h Bool.false_ne_true
  | _ :: _, [], _, _, _, h => absurd h Bool.false_ne_true
  | ops :: restOps, root :: roots, baseLayer, groups, hAuth, hSw => by
    obtain ⟨hHead, hTail⟩ := Bool.and_eq_true_iff.mp hSw
    obtain ⟨hLen, hAt⟩ := verifyLayerSweep_at hHead
    refine ⟨fun g hg => ?_, ?_⟩
    · have hgOps : g < ops.length := hLen.symm ▸ hg
      have hOpen := verifyDuetCosetOpening_facts (hAt g hg)
      have hPath : authPath stageIdx baseLayer g = (ops.getD g defaultFoldOpening).path := by
        have h0 := hAuth 0 g
        rw [Nat.add_zero] at h0
        exact h0
      rw [reconstructLayerTable_getD_left ops g hgOps,
          ← hLen, reconstructLayerTable_getD_right ops g hgOps, hLen, hPath]
      exact ⟨hOpen.2, hOpen.1⟩
    · apply stageLayersBound_of_sweeps authPath stageIdx restOps roots (baseLayer + 1) (groups / 2)
      · intro k g
        have hAdd : (baseLayer + 1) + k = baseLayer + (k + 1) := by omega
        rw [hAdd]
        exact hAuth (k + 1) g
      · exact hTail

private theorem lookupStageOpenings_of_nodup :
    ∀ (sdoms : List WhirStageDomain) (allOps : List (List (List FoldLayerOpening)))
      (pos : Nat) (sdom : WhirStageDomain) (stOps : List (List FoldLayerOpening)),
      (sdoms.map (·.stageIdx)).Nodup →
      sdoms[pos]? = some sdom →
      allOps[pos]? = some stOps →
      lookupStageOpenings sdoms allOps sdom.stageIdx = stOps
  | [], _, _, _, _, _, hd, _ => by cases hd
  | _ :: _, [], _, _, _, _, _, ha => by cases ha
  | sd :: sds, ops0 :: rest, 0, sdom, stOps, _, hd, ha => by
    cases hd; cases ha
    simp [lookupStageOpenings]
  | sd :: sds, ops0 :: rest, pos + 1, sdom, stOps, hNd, hd, ha => by
    obtain ⟨hNotMem, hNdTail⟩ := List.nodup_cons.mp hNd
    have hMem : sdom ∈ sds := List.mem_of_getElem? hd
    have hNe : sd.stageIdx ≠ sdom.stageIdx := fun hEq =>
      hNotMem (List.mem_map.mpr ⟨sdom, hMem, hEq.symm⟩)
    simp only [lookupStageOpenings, hNe, ↓reduceIte]
    exact lookupStageOpenings_of_nodup sds rest pos sdom stOps hNdTail hd ha

private theorem stagesBound_of_sweeps (authPath : Nat → Nat → Nat → List (List UInt8)) :
    ∀ (sdoms : List WhirStageDomain) (allOps : List (List (List FoldLayerOpening)))
      (sps : List WhirStageProof),
      (∀ (pos : Nat) (sdom : WhirStageDomain) (stOps : List (List FoldLayerOpening)),
        sdoms[pos]? = some sdom → allOps[pos]? = some stOps →
        ∀ layer g, authPath sdom.stageIdx layer g =
          ((stOps.getD layer []).getD g defaultFoldOpening).path) →
      verifyAllStageSweeps sdoms allOps sps = true →
      StagesBound authPath sdoms (allOps.map (fun stOps => stOps.map reconstructLayerTable)) sps
  | [], [], [], _, _ => trivial
  | [], _ :: _, _, _, h => absurd h Bool.false_ne_true
  | [], [], _ :: _, _, h => absurd h Bool.false_ne_true
  | _ :: _, [], _, _, h => absurd h Bool.false_ne_true
  | _ :: _, _ :: _, [], _, h => absurd h Bool.false_ne_true
  | sdom :: sdoms, stOps :: restOps, sp :: sps, hAuth, hSw => by
    rcases Bool.and_eq_true_iff.mp hSw with ⟨h12, hRest⟩
    rcases Bool.and_eq_true_iff.mp h12 with ⟨hNeDec, hLayers⟩
    have hNe : stOps ≠ [] := of_decide_eq_true hNeDec
    refine ⟨fun hMapNil => hNe (List.map_eq_nil_iff.mp hMapNil), ?_, ?_⟩
    · apply stageLayersBound_of_sweeps authPath sdom.stageIdx stOps (stageAllRoots sp)
        0 sdom.groups0
      · intro k g
        rw [Nat.zero_add]
        exact hAuth 0 sdom stOps rfl rfl k g
      · exact hLayers
    · exact stagesBound_of_sweeps authPath sdoms restOps sps
        (fun pos sd ops hd ha => hAuth (pos + 1) sd ops hd ha) hRest

/-- Every accepted `CommittedTableTranscript` satisfies `StagesBound` on its reconstructed view. -/
theorem reconstructSuccinctView_stagesBound (dom : WhirDomain) (proof : SuccinctAggregateProof)
    (tr : CommittedTableTranscript)
    (hTr : verifyCommittedTableTranscript dom proof tr = true) :
    StagesBound (reconstructSuccinctView dom tr).authPath dom.stages
      (reconstructSuccinctView dom tr).allTables proof.stages := by
  rcases Bool.and_eq_true_iff.mp hTr with ⟨h12, _⟩
  rcases Bool.and_eq_true_iff.mp h12 with ⟨hNdDec, hSweeps⟩
  have hNd : (dom.stages.map (·.stageIdx)).Nodup := of_decide_eq_true hNdDec
  refine stagesBound_of_sweeps (transcriptAuthPath dom tr) dom.stages tr.stageLayerOpenings
    proof.stages ?_ hSweeps
  intro pos sdom stOps hd ha layer g
  unfold transcriptAuthPath
  rw [lookupStageOpenings_of_nodup dom.stages tr.stageLayerOpenings pos sdom stOps hNd hd ha]

private theorem verifyAllStageSweeps_at :
    ∀ (sdoms : List WhirStageDomain) (allOps : List (List (List FoldLayerOpening)))
      (sps : List WhirStageProof) (pos : Nat) (sdom : WhirStageDomain) (sp : WhirStageProof),
      verifyAllStageSweeps sdoms allOps sps = true →
      sdoms[pos]? = some sdom →
      sps[pos]? = some sp →
      verifyStageLayerSweeps sdom.stageIdx 0 sdom.groups0 (allOps.getD pos [])
        (stageAllRoots sp) = true
  | [], _, _, _, _, _, _, hd, _ => by cases hd
  | _ :: _, [], _, _, _, _, h, _, _ => absurd h Bool.false_ne_true
  | _ :: _, _ :: _, [], _, _, _, h, _, _ => absurd h Bool.false_ne_true
  | sd :: _, stOps :: _, sp0 :: _, 0, sdom, sp, h, hd, hp => by
    cases hd; cases hp
    exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2
  | _ :: sds, _ :: restOps, _ :: sps, pos + 1, sdom, sp, h, hd, hp =>
    verifyAllStageSweeps_at sds restOps sps pos sdom sp (Bool.and_eq_true_iff.mp h).2 hd hp

private theorem verifyStageLayerSweeps_at (stageIdx : Nat) :
    ∀ (stOps : List (List FoldLayerOpening)) (roots : List (List UInt8))
      (baseLayer groups layer : Nat) (root : List UInt8),
      verifyStageLayerSweeps stageIdx baseLayer groups stOps roots = true →
      roots[layer]? = some root →
      verifyLayerSweep stageIdx (baseLayer + layer) (layerGroupsAt groups layer)
        root (stOps.getD layer []) = true
  | _, [], _, _, _, _, _, hr => by cases hr
  | [], _ :: _, _, _, _, _, h, _ => absurd h Bool.false_ne_true
  | _ :: _, _ :: _, baseLayer, groups, 0, root, h, hr => by
    cases hr
    rw [Nat.add_zero]
    exact (Bool.and_eq_true_iff.mp h).1
  | _ :: restOps, _ :: roots, baseLayer, groups, l + 1, root, h, hr => by
    have ih := verifyStageLayerSweeps_at stageIdx restOps roots (baseLayer + 1) (groups / 2)
      l root (Bool.and_eq_true_iff.mp h).2 hr
    have hAdd : (baseLayer + 1) + l = baseLayer + (l + 1) := by omega
    rw [← hAdd]
    exact ih

/-- Constructively cross-check one rewound opening against the base coset sweep: either the duet
    values agree with the reconstructed table, or `duetOpeningCollision` extracts a concrete
    `HashCollisionWitness pcsMerkleHash`. -/
def checkOneRewoundOpening (dom : WhirDomain) (proof : SuccinctAggregateProof)
    (tr : CommittedTableTranscript) (ro : RewoundDuetOpening)
    (hSweeps : verifyAllStageSweeps dom.stages tr.stageLayerOpenings proof.stages = true)
    (hRo : verifyRewoundOpening dom proof ro = true) :
    let sweepOp := ((tr.stageLayerOpenings.getD ro.stagePos []).getD ro.layer []).getD
      ro.cosetIdx defaultFoldOpening
    PSum (PLift (ro.opening.v0 = sweepOp.v0 ∧ ro.opening.v1 = sweepOp.v1))
      (HashCollisionWitness pcsMerkleHash) :=
  let sweepOp := ((tr.stageLayerOpenings.getD ro.stagePos []).getD ro.layer []).getD
    ro.cosetIdx defaultFoldOpening
  if hEq : ro.opening.v0 = sweepOp.v0 ∧ ro.opening.v1 = sweepOp.v1 then
    .inl ⟨hEq⟩
  else
    match hd : dom.stages[ro.stagePos]?, hp : proof.stages[ro.stagePos]? with
    | none, _ => by simp [verifyRewoundOpening, hd] at hRo
    | some _, none => by simp [verifyRewoundOpening, hd, hp] at hRo
    | some sdom, some sp =>
      match hr : (stageAllRoots sp)[ro.layer]? with
      | none => by simp [verifyRewoundOpening, hd, hp, hr] at hRo
      | some root =>
        have hRo' : ro.cosetIdx < layerGroupsAt sdom.groups0 ro.layer ∧
            verifyDuetCosetOpening sdom.stageIdx ro.layer
              (layerGroupsAt sdom.groups0 ro.layer) root ro.cosetIdx ro.opening = true := by
          have h0 : (decide (ro.cosetIdx < layerGroupsAt sdom.groups0 ro.layer) &&
              verifyDuetCosetOpening sdom.stageIdx ro.layer
                (layerGroupsAt sdom.groups0 ro.layer) root ro.cosetIdx ro.opening) = true := by
            simpa [verifyRewoundOpening, hd, hp, hr] using hRo
          exact ⟨of_decide_eq_true (Bool.and_eq_true_iff.mp h0).1, (Bool.and_eq_true_iff.mp h0).2⟩
        have hStSw := verifyAllStageSweeps_at dom.stages tr.stageLayerOpenings proof.stages
          ro.stagePos sdom sp hSweeps hd hp
        have hLaySw : verifyLayerSweep sdom.stageIdx ro.layer
            (layerGroupsAt sdom.groups0 ro.layer) root
            ((tr.stageLayerOpenings.getD ro.stagePos []).getD ro.layer []) = true := by
          simpa only [Nat.zero_add] using
            verifyStageLayerSweeps_at sdom.stageIdx _ (stageAllRoots sp) 0 sdom.groups0
              ro.layer root hStSw hr
        have hSwOpen := verifyDuetCosetOpening_facts
          ((verifyLayerSweep_at hLaySw).2 ro.cosetIdx hRo'.1)
        have hRoOpen := verifyDuetCosetOpening_facts hRo'.2
        .inr (duetOpeningCollision sdom.stageIdx ro.layer ro.cosetIdx
          ro.opening.v0 ro.opening.v1 sweepOp.v0 sweepOp.v1
          ro.opening.path sweepOp.path root hEq
          (hRoOpen.1.trans hSwOpen.1.symm) hRoOpen.2 hSwOpen.2)

def checkRewoundOpeningsList (dom : WhirDomain) (proof : SuccinctAggregateProof)
    (tr : CommittedTableTranscript)
    (hSweeps : verifyAllStageSweeps dom.stages tr.stageLayerOpenings proof.stages = true) :
    (ros : List RewoundDuetOpening) →
    ros.all (verifyRewoundOpening dom proof) = true →
    PSum
      (PLift (∀ ro ∈ ros,
        let sweepOp := ((tr.stageLayerOpenings.getD ro.stagePos []).getD ro.layer []).getD
          ro.cosetIdx defaultFoldOpening
        ro.opening.v0 = sweepOp.v0 ∧ ro.opening.v1 = sweepOp.v1))
      (HashCollisionWitness pcsMerkleHash)
  | [], _ => .inl ⟨fun _ h => by cases h⟩
  | ro :: ros, hAll =>
    have hSplit := Bool.and_eq_true_iff.mp hAll
    match checkOneRewoundOpening dom proof tr ro hSweeps hSplit.1 with
    | .inr col => .inr col
    | .inl ⟨hHead⟩ =>
      match checkRewoundOpeningsList dom proof tr hSweeps ros hSplit.2 with
      | .inr col => .inr col
      | .inl ⟨hTail⟩ => .inl ⟨fun ro' hMem => by
          rcases List.mem_cons.mp hMem with rfl | hRest
          · exact hHead
          · exact hTail ro' hRest⟩

/-- **Constructive Prover-Transcript `HemShardEnv` Extractor (`extractShardEnvFromTranscript`,
    `0 Classical.choice`)**:
    Given an accepted `CommittedTableTranscript` for shard `t`, reconstructs the committed stage
    tables and authentication paths, cross-checks all rewound openings against the sweep tables,
    and returns either a verified `HemShardEnv arith dom` (with proved `StagesBound`) or a
    concrete `HashCollisionWitness pcsMerkleHash`. -/
def extractShardEnvFromTranscript (arith : RowArithmetization) (dom : WhirDomain)
    (t : ShardProverTranscript arith dom)
    (hTr : verifyCommittedTableTranscript dom t.shard.proof t.transcript = true) :
    PSum (HemShardEnv arith dom) (HashCollisionWitness pcsMerkleHash) :=
  have hSweeps : verifyAllStageSweeps dom.stages t.transcript.stageLayerOpenings
      t.shard.proof.stages = true :=
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hTr).1).2
  have hRew : t.transcript.rewoundOpenings.all (verifyRewoundOpening dom t.shard.proof) = true :=
    (Bool.and_eq_true_iff.mp hTr).2
  match checkRewoundOpeningsList dom t.shard.proof t.transcript hSweeps
      t.transcript.rewoundOpenings hRew with
  | .inr col => .inr col
  | .inl _ =>
    .inl { shard := t.shard
           law := t.law
           view := reconstructSuccinctView dom t.transcript
           bound := reconstructSuccinctView_stagesBound dom t.shard.proof t.transcript hTr }

theorem extractShardEnvFromTranscript_inl_eq {arith : RowArithmetization} {dom : WhirDomain}
    {t : ShardProverTranscript arith dom}
    {hTr : verifyCommittedTableTranscript dom t.shard.proof t.transcript = true}
    {env : HemShardEnv arith dom}
    (h : extractShardEnvFromTranscript arith dom t hTr = .inl env) :
    env.shard = t.shard ∧ env.view = reconstructSuccinctView dom t.transcript := by
  unfold extractShardEnvFromTranscript at h
  dsimp only at h
  split at h
  · cases h
  · cases h; exact ⟨rfl, rfl⟩

/-- `#tooth` Equivocation sensitivity of `extractShardEnvFromTranscript`: if an accepted prover
    transcript contains any rewound opening `ro ∈ t.transcript.rewoundOpenings` whose duet pair
    `(v0, v1)` differs from the base coset-sweep opening at `(ro.stagePos, ro.layer, ro.cosetIdx)`,
    `extractShardEnvFromTranscript` cannot return `.inl` and constructively extracts a
    `HashCollisionWitness pcsMerkleHash`. -/
theorem extractShardEnvFromTranscript_equivocation_extracts_collision
    (arith : RowArithmetization) (dom : WhirDomain)
    (t : ShardProverTranscript arith dom)
    (hTr : verifyCommittedTableTranscript dom t.shard.proof t.transcript = true)
    (ro : RewoundDuetOpening) (hMem : ro ∈ t.transcript.rewoundOpenings)
    (hDisagree : ¬ (ro.opening.v0 =
        (((t.transcript.stageLayerOpenings.getD ro.stagePos []).getD ro.layer []).getD
          ro.cosetIdx defaultFoldOpening).v0 ∧
      ro.opening.v1 =
        (((t.transcript.stageLayerOpenings.getD ro.stagePos []).getD ro.layer []).getD
          ro.cosetIdx defaultFoldOpening).v1)) :
    ∃ col : HashCollisionWitness pcsMerkleHash,
      extractShardEnvFromTranscript arith dom t hTr = .inr col := by
  unfold extractShardEnvFromTranscript
  dsimp only
  generalize hChk : checkRewoundOpeningsList dom t.shard.proof t.transcript _
    t.transcript.rewoundOpenings _ = res
  cases res with
  | inr col => exact ⟨col, rfl⟩
  | inl hall => exact False.elim (hDisagree (hall.down ro hMem))

/-- Canonical honest-prover transcript builder converting any `StagesBound` view into a
    `CommittedTableTranscript` (`rewoundOpenings = []`). -/
def mapCosetsAux {α : Type} (f : Nat → α) : Nat → Nat → List α
  | _, 0 => []
  | base, k + 1 => f base :: mapCosetsAux f (base + 1) k

def buildLayerOpeningsFromTable (authPath : Nat → Nat → Nat → List (List UInt8))
    (stageIdx : Nat) : Nat → Nat → List (List GoldilocksExt4) → List (List FoldLayerOpening)
  | _, _, [] => []
  | layer, groups, w :: ws =>
    mapCosetsAux
      (fun g => { v0 := w.getD g CommRingOps.zero
                  v1 := w.getD (g + groups) CommRingOps.zero
                  path := authPath stageIdx layer g }) 0 groups ::
      buildLayerOpeningsFromTable authPath stageIdx (layer + 1) (groups / 2) ws

def buildStageOpeningsFromView (authPath : Nat → Nat → Nat → List (List UInt8)) :
    List WhirStageDomain → List (List (List GoldilocksExt4)) →
      List (List (List FoldLayerOpening))
  | sdom :: sdoms, stTables :: restTables =>
    buildLayerOpeningsFromTable authPath sdom.stageIdx 0 sdom.groups0 stTables ::
      buildStageOpeningsFromView authPath sdoms restTables
  | _, _ => []

def transcriptOfBoundView (dom : WhirDomain) (view : SuccinctExtractionView) :
    CommittedTableTranscript where
  stageLayerOpenings := buildStageOpeningsFromView view.authPath dom.stages view.allTables
  rewoundOpenings := []

private theorem mapCosetsAux_length {α : Type} (f : Nat → α) :
    ∀ (base k : Nat), (mapCosetsAux f base k).length = k
  | _, 0 => rfl
  | base, k + 1 => congrArg Nat.succ (mapCosetsAux_length f (base + 1) k)

private theorem verifyLayerSweepAux_mapCosetsAux (stageIdx layer groups : Nat) (root : List UInt8)
    (f : Nat → FoldLayerOpening) :
    ∀ (base k : Nat),
      (∀ g, base ≤ g → g < base + k → verifyDuetCosetOpening stageIdx layer groups root g (f g) = true) →
      verifyLayerSweepAux stageIdx layer groups root base (mapCosetsAux f base k) = true
  | _, 0, _ => rfl
  | base, k + 1, h => by
    simp only [mapCosetsAux, verifyLayerSweepAux, Bool.and_eq_true]
    refine ⟨h base (Nat.le_refl _) (by omega),
      verifyLayerSweepAux_mapCosetsAux stageIdx layer groups root f (base + 1) k
        (fun g hge hlt => h g (by omega) (by omega))⟩

private theorem verifyStageLayerSweeps_buildLayerOpenings
    (authPath : Nat → Nat → Nat → List (List UInt8)) (stageIdx : Nat) :
    ∀ (stTables : List (List GoldilocksExt4)) (roots : List (List UInt8)) (layer groups : Nat),
      StageLayersBound authPath stageIdx layer groups stTables roots →
      verifyStageLayerSweeps stageIdx layer groups
        (buildLayerOpeningsFromTable authPath stageIdx layer groups stTables) roots = true
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, hB => False.elim hB
  | _ :: _, [], _, _, hB => False.elim hB
  | w :: ws, root :: roots, layer, groups, hB => by
    simp only [buildLayerOpeningsFromTable, verifyStageLayerSweeps, verifyLayerSweep,
      Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨mapCosetsAux_length _ 0 groups, ?_⟩,
      verifyStageLayerSweeps_buildLayerOpenings authPath stageIdx ws roots (layer + 1) (groups / 2) hB.2⟩
    apply verifyLayerSweepAux_mapCosetsAux
    intro g _ hg
    have hOpen := hB.1 g (by omega)
    simp only [verifyDuetCosetOpening, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hOpen.2, hOpen.1⟩

private theorem verifyAllStageSweeps_buildStageOpenings
    (authPath : Nat → Nat → Nat → List (List UInt8)) :
    ∀ (sdoms : List WhirStageDomain) (allTables : List (List (List GoldilocksExt4)))
      (sps : List WhirStageProof),
      StagesBound authPath sdoms allTables sps →
      verifyAllStageSweeps sdoms (buildStageOpeningsFromView authPath sdoms allTables) sps = true
  | [], [], [], _ => rfl
  | [], _ :: _, _, hB => False.elim hB
  | [], [], _ :: _, hB => False.elim hB
  | _ :: _, [], _, hB => False.elim hB
  | _ :: _, _ :: _, [], hB => False.elim hB
  | sdom :: sdoms, stTables :: restTables, sp :: sps, hB => by
    have hNe : buildLayerOpeningsFromTable authPath sdom.stageIdx 0 sdom.groups0 stTables ≠ [] := by
      cases stTables with
      | nil => exact False.elim (hB.1 rfl)
      | cons _ _ => simp [buildLayerOpeningsFromTable]
    simp only [buildStageOpeningsFromView, verifyAllStageSweeps, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hNe, verifyStageLayerSweeps_buildLayerOpenings authPath sdom.stageIdx stTables
      (stageAllRoots sp) 0 sdom.groups0 hB.2.1⟩,
      verifyAllStageSweeps_buildStageOpenings authPath sdoms restTables sps hB.2.2⟩

/-- Completeness of `transcriptOfBoundView`: every `StagesBound` view on a stage-distinct `WhirDomain`
    produces a valid `CommittedTableTranscript` accepted by `verifyCommittedTableTranscript`. -/
theorem verifyCommittedTableTranscript_transcriptOfBoundView (dom : WhirDomain)
    (proof : SuccinctAggregateProof) (view : SuccinctExtractionView)
    (hNodup : (dom.stages.map (·.stageIdx)).Nodup)
    (hBound : StagesBound view.authPath dom.stages view.allTables proof.stages) :
    verifyCommittedTableTranscript dom proof (transcriptOfBoundView dom view) = true := by
  unfold verifyCommittedTableTranscript transcriptOfBoundView
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨hNodup, verifyAllStageSweeps_buildStageOpenings view.authPath dom.stages view.allTables
    proof.stages hBound⟩

private theorem layerOpeningsCount_eq_stageLayerQueryCost (stageIdx : Nat) :
    ∀ (stOps : List (List FoldLayerOpening)) (roots : List (List UInt8)) (layer groups : Nat),
      verifyStageLayerSweeps stageIdx layer groups stOps roots = true →
      layerOpeningsCount stOps = stageLayerQueryCost groups roots.length
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => absurd h Bool.false_ne_true
  | _ :: _, [], _, _, h => absurd h Bool.false_ne_true
  | ops :: restOps, _ :: roots, layer, groups, h => by
    obtain ⟨hHead, hTail⟩ := Bool.and_eq_true_iff.mp h
    have hLen := (verifyLayerSweep_at hHead).1
    have ih := layerOpeningsCount_eq_stageLayerQueryCost stageIdx restOps roots
      (layer + 1) (groups / 2) hTail
    simp only [layerOpeningsCount, List.length_cons, stageLayerQueryCost, hLen, ih]

private theorem verifyOneWhirStage_allRoots_len {rowChalls finalWord : List GoldilocksExt4}
    {prior : List UInt8} {sdom : WhirStageDomain} {sp : WhirStageProof}
    {nextInfo : Option (WhirStageDomain × List UInt8)}
    (h : verifyOneWhirStage rowChalls finalWord prior sdom sp nextInfo = true) :
    (stageAllRoots sp).length = sdom.foldLayers := by
  unfold verifyOneWhirStage at h
  dsimp only at h
  rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨_, hRoots⟩
  exact of_decide_eq_true hRoots

private theorem sweepCount_eq_domainCost_aux {rowChalls finalWord : List GoldilocksExt4} :
    ∀ (prior : List UInt8) (sdoms : List WhirStageDomain)
      (allOps : List (List (List FoldLayerOpening))) (sps : List WhirStageProof),
      verifyWhirStages rowChalls finalWord prior sdoms sps = true →
      verifyAllStageSweeps sdoms allOps sps = true →
      allOps.foldr (fun stOps acc => layerOpeningsCount stOps + acc) 0 =
        sdoms.foldr (fun sdom acc => stageTranscriptQueryCost sdom + acc) 0
  | _, [], [], [], _, _ => rfl
  | _, [], _ :: _, _, _, hSw => absurd hSw Bool.false_ne_true
  | _, [], [], _ :: _, hVer, _ => absurd hVer Bool.false_ne_true
  | _, _ :: _, [], _, _, hSw => absurd hSw Bool.false_ne_true
  | _, _ :: _, _ :: _, [], _, hSw => absurd hSw Bool.false_ne_true
  | prior, [sdom], [stOps], [sp], hVer, hSw => by
    have hRootsLen := verifyOneWhirStage_allRoots_len hVer
    have hLay := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hSw).1).2
    have hEq := layerOpeningsCount_eq_stageLayerQueryCost sdom.stageIdx stOps (stageAllRoots sp)
      0 sdom.groups0 hLay
    simp only [List.foldr_cons, List.foldr_nil, stageTranscriptQueryCost, hEq, hRootsLen]
  | _, [_], _ :: _ :: _, [_], _, hSw =>
    absurd (Bool.and_eq_true_iff.mp hSw).2 Bool.false_ne_true
  | _, [_], _, _ :: _ :: _, hVer, _ => absurd hVer Bool.false_ne_true
  | _, _ :: _ :: _, _, [_], hVer, _ => absurd hVer Bool.false_ne_true
  | _, _ :: _ :: _, [_], _ :: _ :: _, _, hSw =>
    absurd (Bool.and_eq_true_iff.mp hSw).2 Bool.false_ne_true
  | prior, sdom :: nextDom :: restDoms, stOps :: nextOps :: restOps,
      sp :: nextSp :: restSps, hVer, hSw => by
    obtain ⟨hVer0, hVerRest⟩ := Bool.and_eq_true_iff.mp hVer
    rcases Bool.and_eq_true_iff.mp hSw with ⟨hSw0, hSwRest⟩
    have hRootsLen := verifyOneWhirStage_allRoots_len hVer0
    have hLay := (Bool.and_eq_true_iff.mp hSw0).2
    have hEq := layerOpeningsCount_eq_stageLayerQueryCost sdom.stageIdx stOps (stageAllRoots sp)
      0 sdom.groups0 hLay
    have ih := sweepCount_eq_domainCost_aux _ (nextDom :: restDoms) (nextOps :: restOps)
      (nextSp :: restSps) hVerRest hSwRest
    simp only [List.foldr_cons, stageTranscriptQueryCost, hEq, hRootsLen, ih]

theorem transcriptSweepOpeningCount_eq_domainQueryCost {arith : RowArithmetization}
    {dom : WhirDomain} {epochFloor msg : List UInt8}
    {t : ShardProverTranscript arith dom}
    (hShard : verifyHemShard arith dom epochFloor msg t.shard = true)
    (hTr : verifyCommittedTableTranscript dom t.shard.proof t.transcript = true) :
    transcriptSweepOpeningCount t.transcript = domainTranscriptQueryCost dom := by
  have hAcc := (verifyHemShard_facts hShard).2.2.2.2
  have hWhir := (succinct_acceptance_facts arith dom t.shard.inst t.shard.proof
    t.shard.fs hAcc).2.2.2.2.2.2
  have hSw := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hTr).1).2
  exact sweepCount_eq_domainCost_aux _ dom.stages t.transcript.stageLayerOpenings
    t.shard.proof.stages hWhir hSw

/-- **Exact Prover-Transcript Query Cost Accounting (`hierarchySweepOpeningCount_eq_queryCost`)**:
    across any list `trs` of accepted shard certificates and prover commitment transcripts, the
    total number of verified coset-sweep Merkle duet openings equals
    `hierarchyTranscriptQueryCost dom trs.length` (`= trs.length * domainTranscriptQueryCost dom`). -/
theorem hierarchySweepOpeningCount_eq_queryCost {arith : RowArithmetization}
    {dom : WhirDomain} {epochFloor msg : List UInt8} :
    ∀ (trs : List (ShardProverTranscript arith dom)),
      (∀ t ∈ trs, verifyHemShard arith dom epochFloor msg t.shard = true ∧
        verifyCommittedTableTranscript dom t.shard.proof t.transcript = true) →
      hierarchySweepOpeningCount trs = hierarchyTranscriptQueryCost dom trs.length
  | [], _ => by simp [hierarchySweepOpeningCount, hierarchyTranscriptQueryCost]
  | t :: rest, h => by
    have ht := h t (List.mem_cons_self ..)
    have hHead := transcriptSweepOpeningCount_eq_domainQueryCost ht.1 ht.2
    have ih := hierarchySweepOpeningCount_eq_queryCost rest
      (fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))
    change transcriptSweepOpeningCount t.transcript + hierarchySweepOpeningCount rest =
      hierarchyTranscriptQueryCost dom (rest.length + 1)
    rw [hHead, ih, hierarchyTranscriptQueryCost, hierarchyTranscriptQueryCost,
        Nat.add_one_mul, Nat.add_comm]

/-- Shard-by-shard transcript conversion into `HemShardEnv`, preserving shards and reconstructed views. -/
def extractShardEnvsFromTranscripts (arith : RowArithmetization) (dom : WhirDomain) :
    (trs : List (ShardProverTranscript arith dom)) →
    (∀ t ∈ trs, verifyCommittedTableTranscript dom t.shard.proof t.transcript = true) →
    PSum { envs : List (HemShardEnv arith dom) //
        envs.map (·.shard) = trs.map (·.shard) ∧
        envs.length = trs.length ∧
        ∀ (i : Nat) (he : i < envs.length) (ht : i < trs.length),
          (envs[i]'he).shard = (trs[i]'ht).shard ∧
          (envs[i]'he).view = reconstructSuccinctView dom (trs[i]'ht).transcript }
      (Fin trs.length × HashCollisionWitness pcsMerkleHash)
  | [], _ => .inl ⟨[], rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | t :: ts, hTrs =>
    have ht0 := hTrs t (List.mem_cons_self ..)
    match hExt0 : extractShardEnvFromTranscript arith dom t ht0 with
    | .inr col => .inr ⟨⟨0, Nat.succ_pos _⟩, col⟩
    | .inl env0 =>
      have hEq0 := extractShardEnvFromTranscript_inl_eq hExt0
      match extractShardEnvsFromTranscripts arith dom ts
          (fun t' ht' => hTrs t' (List.mem_cons_of_mem _ ht')) with
      | .inr ⟨⟨j, hj⟩, col⟩ => .inr ⟨⟨j + 1, Nat.succ_lt_succ hj⟩, col⟩
      | .inl ⟨envsRest, hMap, hLen, hIdx⟩ =>
        .inl ⟨env0 :: envsRest, by
          refine ⟨by simp [hEq0.1, hMap], congrArg Nat.succ hLen, ?_⟩
          intro i he ht
          cases i with
          | zero => exact hEq0
          | succ k =>
            exact hIdx k (Nat.lt_of_succ_lt_succ he) (Nat.lt_of_succ_lt_succ ht)⟩

/-- Unified break outcome for transcript-grounded hierarchical extraction. -/
@[expose] def HemTranscriptHierarchyBreak (H : Hash) (arith : RowArithmetization)
    (dom : WhirDomain) (trs : List (ShardProverTranscript arith dom)) : Type :=
  PSum (HashCollisionWitness H)
    (Σ j : Fin trs.length,
      HemShardBreak arith dom (trs.get j).shard.proof
        (reconstructSuccinctView dom (trs.get j).transcript))

/-- **Transcript-Grounded Two-Layer Hierarchical Extractor (`extractHierarchicalHemFromTranscripts`,
    `0 Classical.choice`)**:
    Composes `extractShardEnvFromTranscript` with `extractHierarchicalHemQuorums` so hierarchical
    extraction is grounded directly in prover commitment-opening transcripts (`CommittedTableTranscript`)
    rather than externally assumed `StagesBound` proofs. -/
def extractHierarchicalHemFromTranscripts (H : Hash) (arith : RowArithmetization)
    (dom : WhirDomain) (registryDigest epochFloor msg : List UInt8)
    (registry : List ShardRegistration)
    (hReg : H (encodeRegistry registry) = registryDigest)
    (trs : List (ShardProverTranscript arith dom))
    (hTrs : ∀ t ∈ trs, verifyCommittedTableTranscript dom t.shard.proof t.transcript = true)
    (hAccept : verifyHierarchicalHem H arith dom registryDigest epochFloor msg
      (trs.map (·.shard)) = true) :
    PSum (HierarchicalQuorumWitness epochFloor msg registry (trs.map (·.shard)))
      (HemTranscriptHierarchyBreak H arith dom trs) :=
  match extractShardEnvsFromTranscripts arith dom trs hTrs with
  | .inr ⟨j, merkleCol⟩ => .inr (.inr ⟨j, .inr (.inl merkleCol)⟩)
  | .inl ⟨envs, hShards, hLen, hIdx⟩ =>
    have hAccEnvs : verifyHierarchicalHem H arith dom registryDigest epochFloor msg
        (envs.map (·.shard)) = true := by
      rwa [hShards]
    match extractHierarchicalHemQuorums H arith dom registryDigest epochFloor msg registry hReg
        envs hAccEnvs with
    | .inl w =>
      .inl ⟨w.sigs, hShards ▸ w.slots_eq, hShards ▸ w.weight_eq, hShards ▸ w.registry_eq⟩
    | .inr (.inl rootCol) => .inr (.inl rootCol)
    | .inr (.inr ⟨j, brk⟩) =>
      let j' : Fin trs.length := ⟨j.val, hLen ▸ j.isLt⟩
      have hPair := hIdx j.val j.isLt j'.isLt
      have hProofEq : (envs.get j).shard.proof = (trs.get j').shard.proof :=
        congrArg HemShardProof.proof hPair.1
      have hViewEq : (envs.get j).view = reconstructSuccinctView dom (trs.get j').transcript :=
        hPair.2
      .inr (.inr ⟨j', by rw [← hProofEq, ← hViewEq]; exact brk⟩)

theorem recursive_hem_transcript_knowledge_soundness (H : Hash) (arith : RowArithmetization)
    (dom : WhirDomain) (registryDigest epochFloor msg : List UInt8)
    (registry : List ShardRegistration) (hReg : H (encodeRegistry registry) = registryDigest)
    (trs : List (ShardProverTranscript arith dom))
    (hTrs : ∀ t ∈ trs, verifyCommittedTableTranscript dom t.shard.proof t.transcript = true)
    (hAccept : verifyHierarchicalHem H arith dom registryDigest epochFloor msg
      (trs.map (·.shard)) = true) :
    (∃ sigs : List (ExtractedQuorumSig epochFloor msg),
      sigs.map (·.slot) = hierarchicalActiveSlots (trs.map (·.shard)) ∧
      sigs.length = hierarchicalClaimedWeight (trs.map (·.shard)) ∧
      hierarchicalThresholdSum (trs.map (·.shard)) = registryThresholdSum registry ∧
      registryThresholdSum registry ≤ sigs.length ∧
      (sigs.map (·.slot.pk)).Nodup ∧
      (∀ r ∈ registry, r.WellFormed = true) ∧
      (trs.map (·.shard)).map HemShardProof.registration = registry) ∧
      hierarchySweepOpeningCount trs = hierarchyTranscriptQueryCost dom trs.length ∨
    Nonempty (HemTranscriptHierarchyBreak H arith dom trs) := by
  have hF := verifyHierarchicalHem_facts hAccept
  match extractHierarchicalHemFromTranscripts H arith dom registryDigest epochFloor msg registry
      hReg trs hTrs hAccept with
  | .inr brk => exact .inr ⟨brk⟩
  | .inl w =>
    have hSumEq :
        hierarchicalThresholdSum (trs.map (·.shard)) = registryThresholdSum registry := by
      rw [hierarchicalThresholdSum_eq_registryThresholdSum, w.registry_eq]
    have hCost : hierarchySweepOpeningCount trs = hierarchyTranscriptQueryCost dom trs.length :=
      hierarchySweepOpeningCount_eq_queryCost trs (fun t ht =>
        ⟨hF.2.2.2 t.shard (List.mem_map.mpr ⟨t, ht, rfl⟩), hTrs t ht⟩)
    refine .inl ⟨⟨w.sigs, w.slots_eq, w.weight_eq, hSumEq, ?_, ?_, ?_, w.registry_eq⟩, hCost⟩
    · rw [w.weight_eq, ← hSumEq]
      exact hierarchicalThresholdSum_le_claimedWeight _ hF.2.2.2
    · have hMap : w.sigs.map (·.slot.pk) = (w.sigs.map (·.slot)).map HemSlot.pk := by
        rw [List.map_map]; rfl
      rw [hMap, w.slots_eq]
      exact (hierarchicalActiveSlots_pk_sublist _).nodup hF.2.2.1
    · intro r hr
      rw [← w.registry_eq] at hr
      obtain ⟨s, hsMem, rfl⟩ := List.mem_map.mp hr
      exact verifyHemShard_wellFormed (hF.2.2.2 s hsMem)

/-! ### Union bound `ε_hier ≤ ε_root + Σ_j ε_shard(j)` over a finite coin space -/

def countTrue {Ω : Type} (p : Ω → Bool) : List Ω → Nat
  | [] => 0
  | ω :: rest => (if p ω then 1 else 0) + countTrue p rest

def sumOver : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | m + 1, f => sumOver m f + f m

private theorem sumOver_add (m : Nat) (f g : Nat → Nat) :
    sumOver m (fun j => f j + g j) = sumOver m f + sumOver m g := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [sumOver, ih]
    omega

private theorem le_sumOver_of_lt (m : Nat) (f : Nat → Nat) (j : Nat) (hj : j < m) :
    f j ≤ sumOver m f := by
  induction m with
  | zero => omega
  | succ m ih =>
    simp only [sumOver]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · have := ih hlt
      omega
    · omega

/-- Counting union bound: if every bad outcome of the hierarchy is a root-bad outcome or a
    shard-bad outcome for some `j < m`, the bad counts add up accordingly. Dividing by
    `coins.length` gives `ε_hier ≤ ε_root + Σ_{j < m} ε_shard(j)`. -/
theorem countTrue_union_bound {Ω : Type} (coins : List Ω) (m : Nat)
    (hierBad rootBad : Ω → Bool) (shardBad : Nat → Ω → Bool)
    (hCover : ∀ ω, hierBad ω = true →
      rootBad ω = true ∨ ∃ j, j < m ∧ shardBad j ω = true) :
    countTrue hierBad coins ≤
      countTrue rootBad coins + sumOver m (fun j => countTrue (shardBad j) coins) := by
  induction coins with
  | nil => exact Nat.zero_le _
  | cons ω rest ih =>
    have hs : sumOver m (fun j => countTrue (shardBad j) (ω :: rest)) =
        sumOver m (fun j => if shardBad j ω then 1 else 0) +
        sumOver m (fun j => countTrue (shardBad j) rest) := by
      rw [← sumOver_add]
      rfl
    have hstep : (if hierBad ω then 1 else 0) ≤
        (if rootBad ω then 1 else 0) + sumOver m (fun j => if shardBad j ω then 1 else 0) := by
      cases hb : hierBad ω with
      | false => exact Nat.zero_le _
      | true =>
        rcases hCover ω hb with hr | ⟨j, hj, hsj⟩
        · rw [hr]
          exact Nat.le_add_right _ _
        · have hle : (if shardBad j ω then 1 else 0) ≤
              sumOver m (fun j => if shardBad j ω then 1 else 0) :=
            le_sumOver_of_lt m (fun j => if shardBad j ω then 1 else 0) j hj
          rw [hsj] at hle
          exact Nat.le_trans hle (Nat.le_add_left _ _)
    rw [hs]
    simp only [countTrue]
    omega

/-- **Composed soundness error of the two-layer hierarchy
    (`hierarchical_hem_soundness_error_bound`)**: over a finite coin space, let `hierBad` mark
    coins where the root verifier accepts against the authenticated `registryDigest ω =
    H (encodeRegistry (registry ω))` although no `HierarchicalQuorumWitness` exists, let `rootBad`
    mark every coin whose run yields a concrete `HashCollisionWitness H`, and let `shardBad j` mark
    every coin whose run contains a single-layer break at shard `j`. Then
    `#hierBad ≤ #rootBad + Σ_{j < m} #shardBad j`. -/
theorem hierarchical_hem_soundness_error_bound {Ω : Type} (coins : List Ω) (m : Nat)
    (H : Hash) (arith : RowArithmetization) (dom : WhirDomain)
    (registryDigest epochFloor msg : Ω → List UInt8)
    (registry : Ω → List ShardRegistration)
    (envs : Ω → List (HemShardEnv arith dom))
    (hLen : ∀ ω, (envs ω).length ≤ m)
    (hierBad rootBad : Ω → Bool) (shardBad : Nat → Ω → Bool)
    (hHier : ∀ ω, hierBad ω = true →
      verifyHierarchicalHem H arith dom (registryDigest ω) (epochFloor ω) (msg ω)
        ((envs ω).map (·.shard)) = true ∧
      (HierarchicalQuorumWitness (epochFloor ω) (msg ω) (registry ω)
        ((envs ω).map (·.shard)) → False))
    (hRegAuth : ∀ ω, hierBad ω = true → H (encodeRegistry (registry ω)) = registryDigest ω)
    (hRoot : ∀ ω, HashCollisionWitness H → rootBad ω = true)
    (hShard : ∀ ω (j : Fin (envs ω).length),
      HemShardBreak arith dom ((envs ω).get j).shard.proof ((envs ω).get j).view →
      shardBad j.val ω = true) :
    countTrue hierBad coins ≤
      countTrue rootBad coins + sumOver m (fun j => countTrue (shardBad j) coins) := by
  apply countTrue_union_bound
  intro ω hb
  obtain ⟨hAcc, hNo⟩ := hHier ω hb
  have hF := verifyHierarchicalHem_facts hAcc
  if hEq : ((envs ω).map (·.shard)).map HemShardProof.registration = registry ω then
    match extractShardList arith dom (epochFloor ω) (msg ω) (envs ω)
        (fun e he => hF.2.2.2 e.shard (List.mem_map.mpr ⟨e, he, rfl⟩)) with
    | .inl ⟨sigs, hSlots, hWeight⟩ => exact (hNo ⟨sigs, hSlots, hWeight, hEq⟩).elim
    | .inr ⟨j, brk⟩ =>
      exact .inr ⟨j.val, Nat.lt_of_lt_of_le j.isLt (hLen ω), hShard ω j brk⟩
  else
    exact .inl (hRoot ω (registryCollision H hF.1 (hRegAuth ω hb) hEq))

/-- Transcript-grounded finite-coin union bound composing `extractHierarchicalHemFromTranscripts`
    with `countTrue_union_bound`. -/
theorem hierarchical_hem_transcript_soundness_error_bound {Ω : Type} (coins : List Ω) (m : Nat)
    (H : Hash) (arith : RowArithmetization) (dom : WhirDomain)
    (registryDigest epochFloor msg : Ω → List UInt8)
    (registry : Ω → List ShardRegistration)
    (trs : Ω → List (ShardProverTranscript arith dom))
    (hLen : ∀ ω, (trs ω).length ≤ m)
    (hierBad rootBad : Ω → Bool) (shardBad : Nat → Ω → Bool)
    (hHier : ∀ ω, hierBad ω = true →
      verifyHierarchicalHem H arith dom (registryDigest ω) (epochFloor ω) (msg ω)
        ((trs ω).map (·.shard)) = true ∧
      (∀ t ∈ trs ω, verifyCommittedTableTranscript dom t.shard.proof t.transcript = true) ∧
      (HierarchicalQuorumWitness (epochFloor ω) (msg ω) (registry ω)
        ((trs ω).map (·.shard)) → False))
    (hRegAuth : ∀ ω, hierBad ω = true → H (encodeRegistry (registry ω)) = registryDigest ω)
    (hRoot : ∀ ω, HashCollisionWitness H → rootBad ω = true)
    (hShard : ∀ ω (j : Fin (trs ω).length),
      HemShardBreak arith dom ((trs ω).get j).shard.proof
        (reconstructSuccinctView dom ((trs ω).get j).transcript) →
      shardBad j.val ω = true) :
    countTrue hierBad coins ≤
      countTrue rootBad coins + sumOver m (fun j => countTrue (shardBad j) coins) := by
  apply countTrue_union_bound
  intro ω hb
  obtain ⟨hAcc, hTrs, hNo⟩ := hHier ω hb
  match extractHierarchicalHemFromTranscripts H arith dom (registryDigest ω) (epochFloor ω)
      (msg ω) (registry ω) (hRegAuth ω hb) (trs ω) hTrs hAcc with
  | .inl w => exact (hNo w).elim
  | .inr (.inl col) => exact .inl (hRoot ω col)
  | .inr (.inr ⟨j, brk⟩) =>
    exact .inr ⟨j.val, Nat.lt_of_lt_of_le j.isLt (hLen ω), hShard ω j brk⟩

/-! ### `#tooth`: lowered shard threshold & unscoped shard replay refutations -/

/-- Constructive forged-threshold refutation (`0 Classical.choice`): if any shard `i` presents a
    threshold strictly below its registered threshold `(shards[i]).threshold < (registry[i]).threshold`
    under `registryDigest = H (encodeRegistry registry)`, then `verifyHemHierarchyAgainstRegistry`
    unconditionally rejects and either `verifyHierarchicalHem` rejects or `registryCollision`
    constructively extracts a `HashCollisionWitness H`. -/
def forgedLowerThreshold_rejected_or_collision (H : Hash)
    (arith : RowArithmetization) (dom : WhirDomain)
    (registryDigest epochFloor msg : List UInt8)
    (registry : List ShardRegistration)
    (hReg : H (encodeRegistry registry) = registryDigest)
    (shards : List HemShardProof)
    (i : Nat) (hiS : i < shards.length) (hiR : i < registry.length)
    (hLower : (shards[i]'hiS).threshold < (registry[i]'hiR).threshold) :
    PSum
      (PLift (verifyHierarchicalHem H arith dom registryDigest epochFloor msg shards = false ∧
        verifyHemHierarchyAgainstRegistry arith dom registry epochFloor msg shards = false))
      (HashCollisionWitness H) :=
  have hNe : shards.map HemShardProof.registration ≠ registry := fun hEq => by
    have hAt : (shards.map HemShardProof.registration)[i]? = registry[i]? :=
      congrArg (·[i]?) hEq
    rw [List.getElem?_map, List.getElem?_eq_getElem hiS, List.getElem?_eq_getElem hiR,
        Option.map_some, Option.some.injEq] at hAt
    have hThr : (shards[i]'hiS).threshold = (registry[i]'hiR).threshold :=
      congrArg ShardRegistration.threshold hAt
    omega
  have hDirectFalse :
      verifyHemHierarchyAgainstRegistry arith dom registry epochFloor msg shards = false := by
    unfold verifyHemHierarchyAgainstRegistry
    simp [decide_eq_false hNe]
  if hAcc : verifyHierarchicalHem H arith dom registryDigest epochFloor msg shards = true then
    .inr (registryCollision H (verifyHierarchicalHem_facts hAcc).1 hReg hNe)
  else
    .inl ⟨Bool.eq_false_iff.mpr hAcc, hDirectFalse⟩

/-- Root verifier with the shard-id and committee-disjointness checks removed. -/
def verifyHierarchicalHemUnscoped (arith : RowArithmetization) (dom : WhirDomain)
    (shards : List HemShardProof) : Bool :=
  shards.all fun s =>
    decide (1 ≤ s.threshold) &&
    decide (s.threshold ≤ s.inst.committee.length) &&
    decide (s.threshold ≤ bitmapPopcountSpec s.proof.agg.bitmap) &&
    verifySuccinctAggregate arith dom s.inst s.proof s.fs

private theorem hierarchicalClaimedWeight_replicate (s : HemShardProof) :
    ∀ m : Nat, hierarchicalClaimedWeight (List.replicate m s) =
      m * bitmapPopcountSpec s.proof.agg.bitmap
  | 0 => by simp [hierarchicalClaimedWeight]
  | m + 1 => by
    simp only [List.replicate_succ, hierarchicalClaimedWeight,
      hierarchicalClaimedWeight_replicate s m, Nat.succ_mul]
    omega

private theorem hierarchicalActiveSlots_replicate (s : HemShardProof) :
    ∀ (m : Nat) (q : HemSlot), q ∈ hierarchicalActiveSlots (List.replicate m s) →
      q ∈ shardActiveSlots s
  | 0, _, h => by simp [hierarchicalActiveSlots] at h
  | m + 1, q, h => by
    simp only [List.replicate_succ, hierarchicalActiveSlots, List.mem_append] at h
    rcases h with h | h
    · exact h
    · exact hierarchicalActiveSlots_replicate s m q h

private theorem hierarchicalShardIds_replicate (s : HemShardProof) :
    ∀ m : Nat, hierarchicalShardIds (List.replicate m s) = List.replicate m s.shardId
  | 0 => rfl
  | m + 1 => by
    simp only [List.replicate_succ, hierarchicalShardIds, hierarchicalShardIds_replicate s m]

/-- **Replay multiplication without shard scoping**: any shard certificate accepted by
    `verifyHemShard`, repeated `m ≥ 2` times, passes the unscoped root check with claimed weight
    `m` times the shard's weight and `m` times its threshold, although every active slot is one
    of the single shard's slots. `verifyHierarchicalHem` rejects the same list. -/
theorem tooth_unscoped_shard_id_allows_quorum_replay_multiplication (H : Hash)
    (arith : RowArithmetization) (dom : WhirDomain) (registryDigest epochFloor msg : List UInt8)
    (s : HemShardProof) (m : Nat) (hm : 2 ≤ m)
    (hs : verifyHemShard arith dom epochFloor msg s = true) :
    verifyHierarchicalHemUnscoped arith dom (List.replicate m s) = true ∧
    hierarchicalClaimedWeight (List.replicate m s) = m * bitmapPopcountSpec s.proof.agg.bitmap ∧
    m * s.threshold ≤ hierarchicalClaimedWeight (List.replicate m s) ∧
    (∀ q ∈ hierarchicalActiveSlots (List.replicate m s), q ∈ shardActiveSlots s) ∧
    verifyHierarchicalHem H arith dom registryDigest epochFloor msg (List.replicate m s)
      = false := by
  have hF := verifyHemShard_facts hs
  refine ⟨?_, hierarchicalClaimedWeight_replicate s m, ?_,
    hierarchicalActiveSlots_replicate s m, ?_⟩
  · unfold verifyHierarchicalHemUnscoped
    rw [List.all_eq_true]
    intro x hx
    rw [List.eq_of_mem_replicate hx]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨hF.2.1, hF.2.2.1⟩, hF.2.2.2.1⟩, hF.2.2.2.2⟩
  · rw [hierarchicalClaimedWeight_replicate]
    exact Nat.mul_le_mul_left m hF.2.2.2.1
  · apply Bool.eq_false_iff.mpr
    intro hAcc
    have hNodup := (verifyHierarchicalHem_facts hAcc).2.1
    rw [hierarchicalShardIds_replicate] at hNodup
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    simp [List.replicate_succ] at hNodup


/-! ## 5. Deployed width-12 inverses and exact four-lane diffusion -/

/-- The deployed external linear layer, on the actual three-block state. -/
abbrev poseidon2ExternalLinear12 := applyME

/-- The deployed internal linear layer, including its nonuniform diagonal. -/
abbrev poseidon2InternalLinear12 := applyMI

theorem poseidon2ExternalLinear12_two_sided_inverse (x : Poseidon2State12) :
    applyMEInv (poseidon2ExternalLinear12 x) = x ∧
    poseidon2ExternalLinear12 (applyMEInv x) = x :=
  ⟨applyMEInv_applyME x, applyME_applyMEInv x⟩

theorem poseidon2InternalLinear12_two_sided_inverse (x : Poseidon2State12) :
    applyMIInv (poseidon2InternalLinear12 x) = x ∧
    poseidon2InternalLinear12 (applyMIInv x) = x :=
  ⟨applyMIInv_applyMI x, applyMI_applyMIInv x⟩

theorem poseidon2_full_round_two_sided_inverse (rc x : Poseidon2State12) :
    externalRoundInv rc (externalRound rc x) = x ∧
    externalRound rc (externalRoundInv rc x) = x :=
  ⟨externalRoundInv_externalRound rc x, externalRound_externalRoundInv rc x⟩

theorem poseidon2_partial_round_two_sided_inverse (rc : Goldilocks) (x : Poseidon2State12) :
    internalRoundInv rc (internalRound rc x) = x ∧
    internalRound rc (internalRoundInv rc x) = x :=
  ⟨internalRoundInv_internalRound rc x, internalRound_internalRoundInv rc x⟩

theorem poseidon2_deployed_permutation_injective (x y : Poseidon2State12) :
    poseidon2Perm12 x = poseidon2Perm12 y ↔ x = y :=
  (poseidon2Perm12_bijective x y).2.2.1

/-- Number of nonzero coordinates; this counts field elements, not bits. -/
def laneWeight4 (x : Lane4) : Nat :=
  (if x.x0 = Goldilocks.zero then 0 else 1) +
  (if x.x1 = Goldilocks.zero then 0 else 1) +
  (if x.x2 = Goldilocks.zero then 0 else 1) +
  (if x.x3 = Goldilocks.zero then 0 else 1)

private theorem minor_scalar_cancel (d : Int) (hd : goldOfInt d ≠ Goldilocks.zero)
    (x : Goldilocks) (h : Goldilocks.mul (goldOfInt d) x = Goldilocks.zero) :
    x = Goldilocks.zero := by
  rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h with h | h
  · exact False.elim (hd h)
  · exact h

/-- Cofactor certificates below cover every equally sized set of input columns and output rows.
    Each certificate recovers one supported input coordinate from the selected zero outputs.
    The determinants are small nonzero integers, hence units in the Goldilocks field. -/
private theorem m4_minor_0_0 (x : Lane4)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (2)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-3)) x.x1)) (Goldilocks.mul (goldOfInt (-1)) x.x2)) (Goldilocks.mul (goldOfInt (-1)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx1, hx2, hx3, hy0] at he
  apply minor_scalar_cancel (2) (by decide) x.x0
  exact he.trans (by decide)

private theorem m4_minor_0_1 (x : Lane4)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (1)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x1) (Goldilocks.mul (goldOfInt (-2)) x.x1)) (Goldilocks.mul (goldOfInt (-3)) x.x2)) (Goldilocks.mul (goldOfInt (-1)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx1, hx2, hx3, hy1] at he
  apply minor_scalar_cancel (1) (by decide) x.x0
  exact he.trans (by decide)

private theorem m4_minor_0_2 (x : Lane4)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (1)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x2) (Goldilocks.mul (goldOfInt (-1)) x.x1)) (Goldilocks.mul (goldOfInt (-2)) x.x2)) (Goldilocks.mul (goldOfInt (-3)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx1, hx2, hx3, hy2] at he
  apply minor_scalar_cancel (1) (by decide) x.x0
  exact he.trans (by decide)

private theorem m4_minor_0_3 (x : Lane4)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (3)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x3) (Goldilocks.mul (goldOfInt (-1)) x.x1)) (Goldilocks.mul (goldOfInt (-1)) x.x2)) (Goldilocks.mul (goldOfInt (-2)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx1, hx2, hx3, hy3] at he
  apply minor_scalar_cancel (3) (by decide) x.x0
  exact he.trans (by decide)

private theorem m4_minor_1_0 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    : x.x1 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (3)) x.x1) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-2)) x.x0)) (Goldilocks.mul (goldOfInt (-1)) x.x2)) (Goldilocks.mul (goldOfInt (-1)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx2, hx3, hy0] at he
  apply minor_scalar_cancel (3) (by decide) x.x1
  exact he.trans (by decide)

private theorem m4_minor_1_1 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    : x.x1 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (2)) x.x1) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x1) (Goldilocks.mul (goldOfInt (-1)) x.x0)) (Goldilocks.mul (goldOfInt (-3)) x.x2)) (Goldilocks.mul (goldOfInt (-1)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx2, hx3, hy1] at he
  apply minor_scalar_cancel (2) (by decide) x.x1
  exact he.trans (by decide)

private theorem m4_minor_1_2 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    : x.x1 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (1)) x.x1) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x2) (Goldilocks.mul (goldOfInt (-1)) x.x0)) (Goldilocks.mul (goldOfInt (-2)) x.x2)) (Goldilocks.mul (goldOfInt (-3)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx2, hx3, hy2] at he
  apply minor_scalar_cancel (1) (by decide) x.x1
  exact he.trans (by decide)

private theorem m4_minor_1_3 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x1 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (1)) x.x1) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x3) (Goldilocks.mul (goldOfInt (-3)) x.x0)) (Goldilocks.mul (goldOfInt (-1)) x.x2)) (Goldilocks.mul (goldOfInt (-2)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx2, hx3, hy3] at he
  apply minor_scalar_cancel (1) (by decide) x.x1
  exact he.trans (by decide)

private theorem m4_minor_2_0 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    : x.x2 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (1)) x.x2) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-2)) x.x0)) (Goldilocks.mul (goldOfInt (-3)) x.x1)) (Goldilocks.mul (goldOfInt (-1)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx1, hx3, hy0] at he
  apply minor_scalar_cancel (1) (by decide) x.x2
  exact he.trans (by decide)

private theorem m4_minor_2_1 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    : x.x2 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (3)) x.x2) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x1) (Goldilocks.mul (goldOfInt (-1)) x.x0)) (Goldilocks.mul (goldOfInt (-2)) x.x1)) (Goldilocks.mul (goldOfInt (-1)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx1, hx3, hy1] at he
  apply minor_scalar_cancel (3) (by decide) x.x2
  exact he.trans (by decide)

private theorem m4_minor_2_2 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    : x.x2 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (2)) x.x2) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x2) (Goldilocks.mul (goldOfInt (-1)) x.x0)) (Goldilocks.mul (goldOfInt (-1)) x.x1)) (Goldilocks.mul (goldOfInt (-3)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx1, hx3, hy2] at he
  apply minor_scalar_cancel (2) (by decide) x.x2
  exact he.trans (by decide)

private theorem m4_minor_2_3 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x2 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (1)) x.x2) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x3) (Goldilocks.mul (goldOfInt (-3)) x.x0)) (Goldilocks.mul (goldOfInt (-1)) x.x1)) (Goldilocks.mul (goldOfInt (-2)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx1, hx3, hy3] at he
  apply minor_scalar_cancel (1) (by decide) x.x2
  exact he.trans (by decide)

private theorem m4_minor_3_0 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    : x.x3 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (1)) x.x3) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-2)) x.x0)) (Goldilocks.mul (goldOfInt (-3)) x.x1)) (Goldilocks.mul (goldOfInt (-1)) x.x2)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx1, hx2, hy0] at he
  apply minor_scalar_cancel (1) (by decide) x.x3
  exact he.trans (by decide)

private theorem m4_minor_3_1 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    : x.x3 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (1)) x.x3) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x1) (Goldilocks.mul (goldOfInt (-1)) x.x0)) (Goldilocks.mul (goldOfInt (-2)) x.x1)) (Goldilocks.mul (goldOfInt (-3)) x.x2)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx1, hx2, hy1] at he
  apply minor_scalar_cancel (1) (by decide) x.x3
  exact he.trans (by decide)

private theorem m4_minor_3_2 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    : x.x3 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (3)) x.x3) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x2) (Goldilocks.mul (goldOfInt (-1)) x.x0)) (Goldilocks.mul (goldOfInt (-1)) x.x1)) (Goldilocks.mul (goldOfInt (-2)) x.x2)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx1, hx2, hy2] at he
  apply minor_scalar_cancel (3) (by decide) x.x3
  exact he.trans (by decide)

private theorem m4_minor_3_3 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x3 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (2)) x.x3) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x3) (Goldilocks.mul (goldOfInt (-3)) x.x0)) (Goldilocks.mul (goldOfInt (-1)) x.x1)) (Goldilocks.mul (goldOfInt (-1)) x.x2)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx1, hx2, hy3] at he
  apply minor_scalar_cancel (2) (by decide) x.x3
  exact he.trans (by decide)

private theorem m4_minor_01_01 (x : Lane4)
    (hx2 : x.x2 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (1)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (2)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-3)) (applyM4 x).x1)) (Goldilocks.mul (goldOfInt (7)) x.x2)) (Goldilocks.mul (goldOfInt (1)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx2, hx3, hy0, hy1] at he
  apply minor_scalar_cancel (1) (by decide) x.x0
  exact he.trans (by decide)

private theorem m4_minor_01_02 (x : Lane4)
    (hx2 : x.x2 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (-1)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-3)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (5)) x.x2)) (Goldilocks.mul (goldOfInt (8)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx2, hx3, hy0, hy2] at he
  apply minor_scalar_cancel (-1) (by decide) x.x0
  exact he.trans (by decide)

private theorem m4_minor_01_03 (x : Lane4)
    (hx2 : x.x2 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (-7)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-3)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (2)) x.x2)) (Goldilocks.mul (goldOfInt (5)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx2, hx3, hy0, hy3] at he
  apply minor_scalar_cancel (-7) (by decide) x.x0
  exact he.trans (by decide)

private theorem m4_minor_01_12 (x : Lane4)
    (hx2 : x.x2 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (-1)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x1) (Goldilocks.mul (goldOfInt (-2)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (1)) x.x2)) (Goldilocks.mul (goldOfInt (5)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx2, hx3, hy1, hy2] at he
  apply minor_scalar_cancel (-1) (by decide) x.x0
  exact he.trans (by decide)

private theorem m4_minor_01_13 (x : Lane4)
    (hx2 : x.x2 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (-5)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x1) (Goldilocks.mul (goldOfInt (-2)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (-1)) x.x2)) (Goldilocks.mul (goldOfInt (3)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx2, hx3, hy1, hy3] at he
  apply minor_scalar_cancel (-5) (by decide) x.x0
  exact he.trans (by decide)

private theorem m4_minor_01_23 (x : Lane4)
    (hx2 : x.x2 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (-2)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x2) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (-1)) x.x2)) (Goldilocks.mul (goldOfInt (-1)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx2, hx3, hy2, hy3] at he
  apply minor_scalar_cancel (-2) (by decide) x.x0
  exact he.trans (by decide)

private theorem m4_minor_02_01 (x : Lane4)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (5)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (3)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x1)) (Goldilocks.mul (goldOfInt (-7)) x.x1)) (Goldilocks.mul (goldOfInt (-2)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx1, hx3, hy0, hy1] at he
  apply minor_scalar_cancel (5) (by decide) x.x0
  exact he.trans (by decide)

private theorem m4_minor_02_02 (x : Lane4)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (3)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (2)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (-5)) x.x1)) (Goldilocks.mul (goldOfInt (1)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx1, hx3, hy0, hy2] at he
  apply minor_scalar_cancel (3) (by decide) x.x0
  exact he.trans (by decide)

private theorem m4_minor_02_03 (x : Lane4)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (-1)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (-2)) x.x1)) (Goldilocks.mul (goldOfInt (1)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx1, hx3, hy0, hy3] at he
  apply minor_scalar_cancel (-1) (by decide) x.x0
  exact he.trans (by decide)

private theorem m4_minor_02_12 (x : Lane4)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (-1)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (2)) (applyM4 x).x1) (Goldilocks.mul (goldOfInt (-3)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (-1)) x.x1)) (Goldilocks.mul (goldOfInt (7)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx1, hx3, hy1, hy2] at he
  apply minor_scalar_cancel (-1) (by decide) x.x0
  exact he.trans (by decide)

private theorem m4_minor_02_13 (x : Lane4)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (-8)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x1) (Goldilocks.mul (goldOfInt (-3)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (1)) x.x1)) (Goldilocks.mul (goldOfInt (5)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx1, hx3, hy1, hy3] at he
  apply minor_scalar_cancel (-8) (by decide) x.x0
  exact he.trans (by decide)

private theorem m4_minor_02_23 (x : Lane4)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (-5)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x2) (Goldilocks.mul (goldOfInt (-2)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (1)) x.x1)) (Goldilocks.mul (goldOfInt (1)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx1, hx3, hy2, hy3] at he
  apply minor_scalar_cancel (-5) (by decide) x.x0
  exact he.trans (by decide)

private theorem m4_minor_03_01 (x : Lane4)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (1)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x1)) (Goldilocks.mul (goldOfInt (-1)) x.x1)) (Goldilocks.mul (goldOfInt (2)) x.x2)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx1, hx2, hy0, hy1] at he
  apply minor_scalar_cancel (1) (by decide) x.x0
  exact he.trans (by decide)

private theorem m4_minor_03_02 (x : Lane4)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (5)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (3)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (-8)) x.x1)) (Goldilocks.mul (goldOfInt (-1)) x.x2)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx1, hx2, hy0, hy2] at he
  apply minor_scalar_cancel (5) (by decide) x.x0
  exact he.trans (by decide)

private theorem m4_minor_03_03 (x : Lane4)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (1)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (2)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (-5)) x.x1)) (Goldilocks.mul (goldOfInt (-1)) x.x2)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx1, hx2, hy0, hy3] at he
  apply minor_scalar_cancel (1) (by decide) x.x0
  exact he.trans (by decide)

private theorem m4_minor_03_12 (x : Lane4)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (2)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (3)) (applyM4 x).x1) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (-5)) x.x1)) (Goldilocks.mul (goldOfInt (-7)) x.x2)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx1, hx2, hy1, hy2] at he
  apply minor_scalar_cancel (2) (by decide) x.x0
  exact he.trans (by decide)

private theorem m4_minor_03_13 (x : Lane4)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (-1)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (2)) (applyM4 x).x1) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (-3)) x.x1)) (Goldilocks.mul (goldOfInt (-5)) x.x2)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx1, hx2, hy1, hy3] at he
  apply minor_scalar_cancel (-1) (by decide) x.x0
  exact he.trans (by decide)

private theorem m4_minor_03_23 (x : Lane4)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (-7)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (2)) (applyM4 x).x2) (Goldilocks.mul (goldOfInt (-3)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (1)) x.x1)) (Goldilocks.mul (goldOfInt (-1)) x.x2)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx1, hx2, hy2, hy3] at he
  apply minor_scalar_cancel (-7) (by decide) x.x0
  exact he.trans (by decide)

private theorem m4_minor_12_01 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    : x.x1 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (7)) x.x1) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (3)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x1)) (Goldilocks.mul (goldOfInt (-5)) x.x0)) (Goldilocks.mul (goldOfInt (-2)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx3, hy0, hy1] at he
  apply minor_scalar_cancel (7) (by decide) x.x1
  exact he.trans (by decide)

private theorem m4_minor_12_02 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    : x.x1 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (5)) x.x1) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (2)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (-3)) x.x0)) (Goldilocks.mul (goldOfInt (1)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx3, hy0, hy2] at he
  apply minor_scalar_cancel (5) (by decide) x.x1
  exact he.trans (by decide)

private theorem m4_minor_12_03 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x1 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (2)) x.x1) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (1)) x.x0)) (Goldilocks.mul (goldOfInt (1)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx3, hy0, hy3] at he
  apply minor_scalar_cancel (2) (by decide) x.x1
  exact he.trans (by decide)

private theorem m4_minor_12_12 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    : x.x1 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (1)) x.x1) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (2)) (applyM4 x).x1) (Goldilocks.mul (goldOfInt (-3)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (1)) x.x0)) (Goldilocks.mul (goldOfInt (7)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx3, hy1, hy2] at he
  apply minor_scalar_cancel (1) (by decide) x.x1
  exact he.trans (by decide)

private theorem m4_minor_12_13 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x1 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (-1)) x.x1) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x1) (Goldilocks.mul (goldOfInt (-3)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (8)) x.x0)) (Goldilocks.mul (goldOfInt (5)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx3, hy1, hy3] at he
  apply minor_scalar_cancel (-1) (by decide) x.x1
  exact he.trans (by decide)

private theorem m4_minor_12_23 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x1 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (-1)) x.x1) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x2) (Goldilocks.mul (goldOfInt (-2)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (5)) x.x0)) (Goldilocks.mul (goldOfInt (1)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx3, hy2, hy3] at he
  apply minor_scalar_cancel (-1) (by decide) x.x1
  exact he.trans (by decide)

private theorem m4_minor_13_01 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    : x.x1 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (1)) x.x1) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x1)) (Goldilocks.mul (goldOfInt (-1)) x.x0)) (Goldilocks.mul (goldOfInt (2)) x.x2)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx2, hy0, hy1] at he
  apply minor_scalar_cancel (1) (by decide) x.x1
  exact he.trans (by decide)

private theorem m4_minor_13_02 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    : x.x1 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (8)) x.x1) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (3)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (-5)) x.x0)) (Goldilocks.mul (goldOfInt (-1)) x.x2)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx2, hy0, hy2] at he
  apply minor_scalar_cancel (8) (by decide) x.x1
  exact he.trans (by decide)

private theorem m4_minor_13_03 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x1 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (5)) x.x1) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (2)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (-1)) x.x0)) (Goldilocks.mul (goldOfInt (-1)) x.x2)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx2, hy0, hy3] at he
  apply minor_scalar_cancel (5) (by decide) x.x1
  exact he.trans (by decide)

private theorem m4_minor_13_12 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    : x.x1 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (5)) x.x1) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (3)) (applyM4 x).x1) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (-2)) x.x0)) (Goldilocks.mul (goldOfInt (-7)) x.x2)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx2, hy1, hy2] at he
  apply minor_scalar_cancel (5) (by decide) x.x1
  exact he.trans (by decide)

private theorem m4_minor_13_13 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x1 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (3)) x.x1) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (2)) (applyM4 x).x1) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (1)) x.x0)) (Goldilocks.mul (goldOfInt (-5)) x.x2)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx2, hy1, hy3] at he
  apply minor_scalar_cancel (3) (by decide) x.x1
  exact he.trans (by decide)

private theorem m4_minor_13_23 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x1 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (-1)) x.x1) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (2)) (applyM4 x).x2) (Goldilocks.mul (goldOfInt (-3)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (7)) x.x0)) (Goldilocks.mul (goldOfInt (-1)) x.x2)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx2, hy2, hy3] at he
  apply minor_scalar_cancel (-1) (by decide) x.x1
  exact he.trans (by decide)

private theorem m4_minor_23_01 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx1 : x.x1 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    : x.x2 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (-2)) x.x2) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x1)) (Goldilocks.mul (goldOfInt (-1)) x.x0)) (Goldilocks.mul (goldOfInt (-1)) x.x1)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx1, hy0, hy1] at he
  apply minor_scalar_cancel (-2) (by decide) x.x2
  exact he.trans (by decide)

private theorem m4_minor_23_02 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx1 : x.x1 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    : x.x2 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (1)) x.x2) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (3)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (-5)) x.x0)) (Goldilocks.mul (goldOfInt (-8)) x.x1)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx1, hy0, hy2] at he
  apply minor_scalar_cancel (1) (by decide) x.x2
  exact he.trans (by decide)

private theorem m4_minor_23_03 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx1 : x.x1 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x2 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (1)) x.x2) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (2)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (-1)) x.x0)) (Goldilocks.mul (goldOfInt (-5)) x.x1)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx1, hy0, hy3] at he
  apply minor_scalar_cancel (1) (by decide) x.x2
  exact he.trans (by decide)

private theorem m4_minor_23_12 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx1 : x.x1 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    : x.x2 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (7)) x.x2) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (3)) (applyM4 x).x1) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (-2)) x.x0)) (Goldilocks.mul (goldOfInt (-5)) x.x1)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx1, hy1, hy2] at he
  apply minor_scalar_cancel (7) (by decide) x.x2
  exact he.trans (by decide)

private theorem m4_minor_23_13 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx1 : x.x1 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x2 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (5)) x.x2) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (2)) (applyM4 x).x1) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (1)) x.x0)) (Goldilocks.mul (goldOfInt (-3)) x.x1)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx1, hy1, hy3] at he
  apply minor_scalar_cancel (5) (by decide) x.x2
  exact he.trans (by decide)

private theorem m4_minor_23_23 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx1 : x.x1 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x2 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (1)) x.x2) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (2)) (applyM4 x).x2) (Goldilocks.mul (goldOfInt (-3)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (7)) x.x0)) (Goldilocks.mul (goldOfInt (1)) x.x1)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx1, hy2, hy3] at he
  apply minor_scalar_cancel (1) (by decide) x.x2
  exact he.trans (by decide)

private theorem m4_minor_012_012 (x : Lane4)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (4)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-5)) (applyM4 x).x1)) (Goldilocks.mul (goldOfInt (7)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (-17)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx3, hy0, hy1, hy2] at he
  apply minor_scalar_cancel (4) (by decide) x.x0
  exact he.trans (by decide)

private theorem m4_minor_012_013 (x : Lane4)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (17)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-2)) (applyM4 x).x1)) (Goldilocks.mul (goldOfInt (7)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (-11)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx3, hy0, hy1, hy3] at he
  apply minor_scalar_cancel (17) (by decide) x.x0
  exact he.trans (by decide)

private theorem m4_minor_012_023 (x : Lane4)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (11)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-2)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (5)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (-3)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx3, hy0, hy2, hy3] at he
  apply minor_scalar_cancel (11) (by decide) x.x0
  exact he.trans (by decide)

private theorem m4_minor_012_123 (x : Lane4)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (3)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x1) (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (-4)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx3, hy1, hy2, hy3] at he
  apply minor_scalar_cancel (3) (by decide) x.x0
  exact he.trans (by decide)

private theorem m4_minor_013_012 (x : Lane4)
    (hx2 : x.x2 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (3)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (5)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-8)) (applyM4 x).x1)) (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (17)) x.x2)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx2, hy0, hy1, hy2] at he
  apply minor_scalar_cancel (3) (by decide) x.x0
  exact he.trans (by decide)

private theorem m4_minor_013_013 (x : Lane4)
    (hx2 : x.x2 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (4)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (3)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-5)) (applyM4 x).x1)) (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (11)) x.x2)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx2, hy0, hy1, hy3] at he
  apply minor_scalar_cancel (4) (by decide) x.x0
  exact he.trans (by decide)

private theorem m4_minor_013_023 (x : Lane4)
    (hx2 : x.x2 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (17)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-5)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (8)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (3)) x.x2)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx2, hy0, hy2, hy3] at he
  apply minor_scalar_cancel (17) (by decide) x.x0
  exact he.trans (by decide)

private theorem m4_minor_013_123 (x : Lane4)
    (hx2 : x.x2 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (11)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x1) (Goldilocks.mul (goldOfInt (-3)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (5)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (4)) x.x2)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx2, hy1, hy2, hy3] at he
  apply minor_scalar_cancel (11) (by decide) x.x0
  exact he.trans (by decide)

private theorem m4_minor_023_012 (x : Lane4)
    (hx1 : x.x1 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (11)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (7)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x1)) (Goldilocks.mul (goldOfInt (-2)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (-17)) x.x1)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx1, hy0, hy1, hy2] at he
  apply minor_scalar_cancel (11) (by decide) x.x0
  exact he.trans (by decide)

private theorem m4_minor_023_013 (x : Lane4)
    (hx1 : x.x1 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (3)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (5)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x1)) (Goldilocks.mul (goldOfInt (-2)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (-11)) x.x1)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx1, hy0, hy1, hy3] at he
  apply minor_scalar_cancel (3) (by decide) x.x0
  exact he.trans (by decide)

private theorem m4_minor_023_023 (x : Lane4)
    (hx1 : x.x1 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (4)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (-3)) x.x1)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx1, hy0, hy2, hy3] at he
  apply minor_scalar_cancel (4) (by decide) x.x0
  exact he.trans (by decide)

private theorem m4_minor_023_123 (x : Lane4)
    (hx1 : x.x1 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (17)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x1) (Goldilocks.mul (goldOfInt (-5)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (7)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (-4)) x.x1)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx1, hy1, hy2, hy3] at he
  apply minor_scalar_cancel (17) (by decide) x.x0
  exact he.trans (by decide)

private theorem m4_minor_123_012 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    : x.x1 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (17)) x.x1) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (7)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x1)) (Goldilocks.mul (goldOfInt (-2)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (-11)) x.x0)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hy0, hy1, hy2] at he
  apply minor_scalar_cancel (17) (by decide) x.x1
  exact he.trans (by decide)

private theorem m4_minor_123_013 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x1 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (11)) x.x1) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (5)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x1)) (Goldilocks.mul (goldOfInt (-2)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (-3)) x.x0)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hy0, hy1, hy3] at he
  apply minor_scalar_cancel (11) (by decide) x.x1
  exact he.trans (by decide)

private theorem m4_minor_123_023 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x1 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (3)) x.x1) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (-4)) x.x0)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hy0, hy2, hy3] at he
  apply minor_scalar_cancel (3) (by decide) x.x1
  exact he.trans (by decide)

private theorem m4_minor_123_123 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x1 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (4)) x.x1) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x1) (Goldilocks.mul (goldOfInt (-5)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (7)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (-17)) x.x0)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hy1, hy2, hy3] at he
  apply minor_scalar_cancel (4) (by decide) x.x1
  exact he.trans (by decide)

private theorem m4_minor_0123_0123 (x : Lane4)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (-35)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (4)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-3)) (applyM4 x).x1)) (Goldilocks.mul (goldOfInt (11)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (-17)) (applyM4 x).x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hy0, hy1, hy2, hy3] at he
  apply minor_scalar_cancel (-35) (by decide) x.x0
  exact he.trans (by decide)

/-- Any nonzero input has input/output support sum at least five. -/
theorem m4_mds_branch_lower (x : Lane4) (hne : x ≠ lane4Zero) :
    5 ≤ laneWeight4 x + laneWeight4 (applyM4 x) := by
  by_cases hx0 : x.x0 = Goldilocks.zero <;>
    by_cases hx1 : x.x1 = Goldilocks.zero <;>
    by_cases hx2 : x.x2 = Goldilocks.zero <;>
    by_cases hx3 : x.x3 = Goldilocks.zero
  · exact False.elim (hne (Lane4.ext hx0 hx1 hx2 hx3))
  · by_cases hy0 : (applyM4 x).x0 = Goldilocks.zero <;>
      by_cases hy1 : (applyM4 x).x1 = Goldilocks.zero <;>
      by_cases hy2 : (applyM4 x).x2 = Goldilocks.zero <;>
      by_cases hy3 : (applyM4 x).x3 = Goldilocks.zero
    · exact False.elim (hx3 (m4_minor_3_0 x hx0 hx1 hx2 hy0))
    · exact False.elim (hx3 (m4_minor_3_0 x hx0 hx1 hx2 hy0))
    · exact False.elim (hx3 (m4_minor_3_0 x hx0 hx1 hx2 hy0))
    · exact False.elim (hx3 (m4_minor_3_0 x hx0 hx1 hx2 hy0))
    · exact False.elim (hx3 (m4_minor_3_0 x hx0 hx1 hx2 hy0))
    · exact False.elim (hx3 (m4_minor_3_0 x hx0 hx1 hx2 hy0))
    · exact False.elim (hx3 (m4_minor_3_0 x hx0 hx1 hx2 hy0))
    · exact False.elim (hx3 (m4_minor_3_0 x hx0 hx1 hx2 hy0))
    · exact False.elim (hx3 (m4_minor_3_1 x hx0 hx1 hx2 hy1))
    · exact False.elim (hx3 (m4_minor_3_1 x hx0 hx1 hx2 hy1))
    · exact False.elim (hx3 (m4_minor_3_1 x hx0 hx1 hx2 hy1))
    · exact False.elim (hx3 (m4_minor_3_1 x hx0 hx1 hx2 hy1))
    · exact False.elim (hx3 (m4_minor_3_2 x hx0 hx1 hx2 hy2))
    · exact False.elim (hx3 (m4_minor_3_2 x hx0 hx1 hx2 hy2))
    · exact False.elim (hx3 (m4_minor_3_3 x hx0 hx1 hx2 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
  · by_cases hy0 : (applyM4 x).x0 = Goldilocks.zero <;>
      by_cases hy1 : (applyM4 x).x1 = Goldilocks.zero <;>
      by_cases hy2 : (applyM4 x).x2 = Goldilocks.zero <;>
      by_cases hy3 : (applyM4 x).x3 = Goldilocks.zero
    · exact False.elim (hx2 (m4_minor_2_0 x hx0 hx1 hx3 hy0))
    · exact False.elim (hx2 (m4_minor_2_0 x hx0 hx1 hx3 hy0))
    · exact False.elim (hx2 (m4_minor_2_0 x hx0 hx1 hx3 hy0))
    · exact False.elim (hx2 (m4_minor_2_0 x hx0 hx1 hx3 hy0))
    · exact False.elim (hx2 (m4_minor_2_0 x hx0 hx1 hx3 hy0))
    · exact False.elim (hx2 (m4_minor_2_0 x hx0 hx1 hx3 hy0))
    · exact False.elim (hx2 (m4_minor_2_0 x hx0 hx1 hx3 hy0))
    · exact False.elim (hx2 (m4_minor_2_0 x hx0 hx1 hx3 hy0))
    · exact False.elim (hx2 (m4_minor_2_1 x hx0 hx1 hx3 hy1))
    · exact False.elim (hx2 (m4_minor_2_1 x hx0 hx1 hx3 hy1))
    · exact False.elim (hx2 (m4_minor_2_1 x hx0 hx1 hx3 hy1))
    · exact False.elim (hx2 (m4_minor_2_1 x hx0 hx1 hx3 hy1))
    · exact False.elim (hx2 (m4_minor_2_2 x hx0 hx1 hx3 hy2))
    · exact False.elim (hx2 (m4_minor_2_2 x hx0 hx1 hx3 hy2))
    · exact False.elim (hx2 (m4_minor_2_3 x hx0 hx1 hx3 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
  · by_cases hy0 : (applyM4 x).x0 = Goldilocks.zero <;>
      by_cases hy1 : (applyM4 x).x1 = Goldilocks.zero <;>
      by_cases hy2 : (applyM4 x).x2 = Goldilocks.zero <;>
      by_cases hy3 : (applyM4 x).x3 = Goldilocks.zero
    · exact False.elim (hx2 (m4_minor_23_01 x hx0 hx1 hy0 hy1))
    · exact False.elim (hx2 (m4_minor_23_01 x hx0 hx1 hy0 hy1))
    · exact False.elim (hx2 (m4_minor_23_01 x hx0 hx1 hy0 hy1))
    · exact False.elim (hx2 (m4_minor_23_01 x hx0 hx1 hy0 hy1))
    · exact False.elim (hx2 (m4_minor_23_02 x hx0 hx1 hy0 hy2))
    · exact False.elim (hx2 (m4_minor_23_02 x hx0 hx1 hy0 hy2))
    · exact False.elim (hx2 (m4_minor_23_03 x hx0 hx1 hy0 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · exact False.elim (hx2 (m4_minor_23_12 x hx0 hx1 hy1 hy2))
    · exact False.elim (hx2 (m4_minor_23_12 x hx0 hx1 hy1 hy2))
    · exact False.elim (hx2 (m4_minor_23_13 x hx0 hx1 hy1 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · exact False.elim (hx2 (m4_minor_23_23 x hx0 hx1 hy2 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
  · by_cases hy0 : (applyM4 x).x0 = Goldilocks.zero <;>
      by_cases hy1 : (applyM4 x).x1 = Goldilocks.zero <;>
      by_cases hy2 : (applyM4 x).x2 = Goldilocks.zero <;>
      by_cases hy3 : (applyM4 x).x3 = Goldilocks.zero
    · exact False.elim (hx1 (m4_minor_1_0 x hx0 hx2 hx3 hy0))
    · exact False.elim (hx1 (m4_minor_1_0 x hx0 hx2 hx3 hy0))
    · exact False.elim (hx1 (m4_minor_1_0 x hx0 hx2 hx3 hy0))
    · exact False.elim (hx1 (m4_minor_1_0 x hx0 hx2 hx3 hy0))
    · exact False.elim (hx1 (m4_minor_1_0 x hx0 hx2 hx3 hy0))
    · exact False.elim (hx1 (m4_minor_1_0 x hx0 hx2 hx3 hy0))
    · exact False.elim (hx1 (m4_minor_1_0 x hx0 hx2 hx3 hy0))
    · exact False.elim (hx1 (m4_minor_1_0 x hx0 hx2 hx3 hy0))
    · exact False.elim (hx1 (m4_minor_1_1 x hx0 hx2 hx3 hy1))
    · exact False.elim (hx1 (m4_minor_1_1 x hx0 hx2 hx3 hy1))
    · exact False.elim (hx1 (m4_minor_1_1 x hx0 hx2 hx3 hy1))
    · exact False.elim (hx1 (m4_minor_1_1 x hx0 hx2 hx3 hy1))
    · exact False.elim (hx1 (m4_minor_1_2 x hx0 hx2 hx3 hy2))
    · exact False.elim (hx1 (m4_minor_1_2 x hx0 hx2 hx3 hy2))
    · exact False.elim (hx1 (m4_minor_1_3 x hx0 hx2 hx3 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
  · by_cases hy0 : (applyM4 x).x0 = Goldilocks.zero <;>
      by_cases hy1 : (applyM4 x).x1 = Goldilocks.zero <;>
      by_cases hy2 : (applyM4 x).x2 = Goldilocks.zero <;>
      by_cases hy3 : (applyM4 x).x3 = Goldilocks.zero
    · exact False.elim (hx1 (m4_minor_13_01 x hx0 hx2 hy0 hy1))
    · exact False.elim (hx1 (m4_minor_13_01 x hx0 hx2 hy0 hy1))
    · exact False.elim (hx1 (m4_minor_13_01 x hx0 hx2 hy0 hy1))
    · exact False.elim (hx1 (m4_minor_13_01 x hx0 hx2 hy0 hy1))
    · exact False.elim (hx1 (m4_minor_13_02 x hx0 hx2 hy0 hy2))
    · exact False.elim (hx1 (m4_minor_13_02 x hx0 hx2 hy0 hy2))
    · exact False.elim (hx1 (m4_minor_13_03 x hx0 hx2 hy0 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · exact False.elim (hx1 (m4_minor_13_12 x hx0 hx2 hy1 hy2))
    · exact False.elim (hx1 (m4_minor_13_12 x hx0 hx2 hy1 hy2))
    · exact False.elim (hx1 (m4_minor_13_13 x hx0 hx2 hy1 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · exact False.elim (hx1 (m4_minor_13_23 x hx0 hx2 hy2 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
  · by_cases hy0 : (applyM4 x).x0 = Goldilocks.zero <;>
      by_cases hy1 : (applyM4 x).x1 = Goldilocks.zero <;>
      by_cases hy2 : (applyM4 x).x2 = Goldilocks.zero <;>
      by_cases hy3 : (applyM4 x).x3 = Goldilocks.zero
    · exact False.elim (hx1 (m4_minor_12_01 x hx0 hx3 hy0 hy1))
    · exact False.elim (hx1 (m4_minor_12_01 x hx0 hx3 hy0 hy1))
    · exact False.elim (hx1 (m4_minor_12_01 x hx0 hx3 hy0 hy1))
    · exact False.elim (hx1 (m4_minor_12_01 x hx0 hx3 hy0 hy1))
    · exact False.elim (hx1 (m4_minor_12_02 x hx0 hx3 hy0 hy2))
    · exact False.elim (hx1 (m4_minor_12_02 x hx0 hx3 hy0 hy2))
    · exact False.elim (hx1 (m4_minor_12_03 x hx0 hx3 hy0 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · exact False.elim (hx1 (m4_minor_12_12 x hx0 hx3 hy1 hy2))
    · exact False.elim (hx1 (m4_minor_12_12 x hx0 hx3 hy1 hy2))
    · exact False.elim (hx1 (m4_minor_12_13 x hx0 hx3 hy1 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · exact False.elim (hx1 (m4_minor_12_23 x hx0 hx3 hy2 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
  · by_cases hy0 : (applyM4 x).x0 = Goldilocks.zero <;>
      by_cases hy1 : (applyM4 x).x1 = Goldilocks.zero <;>
      by_cases hy2 : (applyM4 x).x2 = Goldilocks.zero <;>
      by_cases hy3 : (applyM4 x).x3 = Goldilocks.zero
    · exact False.elim (hx1 (m4_minor_123_012 x hx0 hy0 hy1 hy2))
    · exact False.elim (hx1 (m4_minor_123_012 x hx0 hy0 hy1 hy2))
    · exact False.elim (hx1 (m4_minor_123_013 x hx0 hy0 hy1 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · exact False.elim (hx1 (m4_minor_123_023 x hx0 hy0 hy2 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · exact False.elim (hx1 (m4_minor_123_123 x hx0 hy1 hy2 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
  · by_cases hy0 : (applyM4 x).x0 = Goldilocks.zero <;>
      by_cases hy1 : (applyM4 x).x1 = Goldilocks.zero <;>
      by_cases hy2 : (applyM4 x).x2 = Goldilocks.zero <;>
      by_cases hy3 : (applyM4 x).x3 = Goldilocks.zero
    · exact False.elim (hx0 (m4_minor_0_0 x hx1 hx2 hx3 hy0))
    · exact False.elim (hx0 (m4_minor_0_0 x hx1 hx2 hx3 hy0))
    · exact False.elim (hx0 (m4_minor_0_0 x hx1 hx2 hx3 hy0))
    · exact False.elim (hx0 (m4_minor_0_0 x hx1 hx2 hx3 hy0))
    · exact False.elim (hx0 (m4_minor_0_0 x hx1 hx2 hx3 hy0))
    · exact False.elim (hx0 (m4_minor_0_0 x hx1 hx2 hx3 hy0))
    · exact False.elim (hx0 (m4_minor_0_0 x hx1 hx2 hx3 hy0))
    · exact False.elim (hx0 (m4_minor_0_0 x hx1 hx2 hx3 hy0))
    · exact False.elim (hx0 (m4_minor_0_1 x hx1 hx2 hx3 hy1))
    · exact False.elim (hx0 (m4_minor_0_1 x hx1 hx2 hx3 hy1))
    · exact False.elim (hx0 (m4_minor_0_1 x hx1 hx2 hx3 hy1))
    · exact False.elim (hx0 (m4_minor_0_1 x hx1 hx2 hx3 hy1))
    · exact False.elim (hx0 (m4_minor_0_2 x hx1 hx2 hx3 hy2))
    · exact False.elim (hx0 (m4_minor_0_2 x hx1 hx2 hx3 hy2))
    · exact False.elim (hx0 (m4_minor_0_3 x hx1 hx2 hx3 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
  · by_cases hy0 : (applyM4 x).x0 = Goldilocks.zero <;>
      by_cases hy1 : (applyM4 x).x1 = Goldilocks.zero <;>
      by_cases hy2 : (applyM4 x).x2 = Goldilocks.zero <;>
      by_cases hy3 : (applyM4 x).x3 = Goldilocks.zero
    · exact False.elim (hx0 (m4_minor_03_01 x hx1 hx2 hy0 hy1))
    · exact False.elim (hx0 (m4_minor_03_01 x hx1 hx2 hy0 hy1))
    · exact False.elim (hx0 (m4_minor_03_01 x hx1 hx2 hy0 hy1))
    · exact False.elim (hx0 (m4_minor_03_01 x hx1 hx2 hy0 hy1))
    · exact False.elim (hx0 (m4_minor_03_02 x hx1 hx2 hy0 hy2))
    · exact False.elim (hx0 (m4_minor_03_02 x hx1 hx2 hy0 hy2))
    · exact False.elim (hx0 (m4_minor_03_03 x hx1 hx2 hy0 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · exact False.elim (hx0 (m4_minor_03_12 x hx1 hx2 hy1 hy2))
    · exact False.elim (hx0 (m4_minor_03_12 x hx1 hx2 hy1 hy2))
    · exact False.elim (hx0 (m4_minor_03_13 x hx1 hx2 hy1 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · exact False.elim (hx0 (m4_minor_03_23 x hx1 hx2 hy2 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
  · by_cases hy0 : (applyM4 x).x0 = Goldilocks.zero <;>
      by_cases hy1 : (applyM4 x).x1 = Goldilocks.zero <;>
      by_cases hy2 : (applyM4 x).x2 = Goldilocks.zero <;>
      by_cases hy3 : (applyM4 x).x3 = Goldilocks.zero
    · exact False.elim (hx0 (m4_minor_02_01 x hx1 hx3 hy0 hy1))
    · exact False.elim (hx0 (m4_minor_02_01 x hx1 hx3 hy0 hy1))
    · exact False.elim (hx0 (m4_minor_02_01 x hx1 hx3 hy0 hy1))
    · exact False.elim (hx0 (m4_minor_02_01 x hx1 hx3 hy0 hy1))
    · exact False.elim (hx0 (m4_minor_02_02 x hx1 hx3 hy0 hy2))
    · exact False.elim (hx0 (m4_minor_02_02 x hx1 hx3 hy0 hy2))
    · exact False.elim (hx0 (m4_minor_02_03 x hx1 hx3 hy0 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · exact False.elim (hx0 (m4_minor_02_12 x hx1 hx3 hy1 hy2))
    · exact False.elim (hx0 (m4_minor_02_12 x hx1 hx3 hy1 hy2))
    · exact False.elim (hx0 (m4_minor_02_13 x hx1 hx3 hy1 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · exact False.elim (hx0 (m4_minor_02_23 x hx1 hx3 hy2 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
  · by_cases hy0 : (applyM4 x).x0 = Goldilocks.zero <;>
      by_cases hy1 : (applyM4 x).x1 = Goldilocks.zero <;>
      by_cases hy2 : (applyM4 x).x2 = Goldilocks.zero <;>
      by_cases hy3 : (applyM4 x).x3 = Goldilocks.zero
    · exact False.elim (hx0 (m4_minor_023_012 x hx1 hy0 hy1 hy2))
    · exact False.elim (hx0 (m4_minor_023_012 x hx1 hy0 hy1 hy2))
    · exact False.elim (hx0 (m4_minor_023_013 x hx1 hy0 hy1 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · exact False.elim (hx0 (m4_minor_023_023 x hx1 hy0 hy2 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · exact False.elim (hx0 (m4_minor_023_123 x hx1 hy1 hy2 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
  · by_cases hy0 : (applyM4 x).x0 = Goldilocks.zero <;>
      by_cases hy1 : (applyM4 x).x1 = Goldilocks.zero <;>
      by_cases hy2 : (applyM4 x).x2 = Goldilocks.zero <;>
      by_cases hy3 : (applyM4 x).x3 = Goldilocks.zero
    · exact False.elim (hx0 (m4_minor_01_01 x hx2 hx3 hy0 hy1))
    · exact False.elim (hx0 (m4_minor_01_01 x hx2 hx3 hy0 hy1))
    · exact False.elim (hx0 (m4_minor_01_01 x hx2 hx3 hy0 hy1))
    · exact False.elim (hx0 (m4_minor_01_01 x hx2 hx3 hy0 hy1))
    · exact False.elim (hx0 (m4_minor_01_02 x hx2 hx3 hy0 hy2))
    · exact False.elim (hx0 (m4_minor_01_02 x hx2 hx3 hy0 hy2))
    · exact False.elim (hx0 (m4_minor_01_03 x hx2 hx3 hy0 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · exact False.elim (hx0 (m4_minor_01_12 x hx2 hx3 hy1 hy2))
    · exact False.elim (hx0 (m4_minor_01_12 x hx2 hx3 hy1 hy2))
    · exact False.elim (hx0 (m4_minor_01_13 x hx2 hx3 hy1 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · exact False.elim (hx0 (m4_minor_01_23 x hx2 hx3 hy2 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
  · by_cases hy0 : (applyM4 x).x0 = Goldilocks.zero <;>
      by_cases hy1 : (applyM4 x).x1 = Goldilocks.zero <;>
      by_cases hy2 : (applyM4 x).x2 = Goldilocks.zero <;>
      by_cases hy3 : (applyM4 x).x3 = Goldilocks.zero
    · exact False.elim (hx0 (m4_minor_013_012 x hx2 hy0 hy1 hy2))
    · exact False.elim (hx0 (m4_minor_013_012 x hx2 hy0 hy1 hy2))
    · exact False.elim (hx0 (m4_minor_013_013 x hx2 hy0 hy1 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · exact False.elim (hx0 (m4_minor_013_023 x hx2 hy0 hy2 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · exact False.elim (hx0 (m4_minor_013_123 x hx2 hy1 hy2 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
  · by_cases hy0 : (applyM4 x).x0 = Goldilocks.zero <;>
      by_cases hy1 : (applyM4 x).x1 = Goldilocks.zero <;>
      by_cases hy2 : (applyM4 x).x2 = Goldilocks.zero <;>
      by_cases hy3 : (applyM4 x).x3 = Goldilocks.zero
    · exact False.elim (hx0 (m4_minor_012_012 x hx3 hy0 hy1 hy2))
    · exact False.elim (hx0 (m4_minor_012_012 x hx3 hy0 hy1 hy2))
    · exact False.elim (hx0 (m4_minor_012_013 x hx3 hy0 hy1 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · exact False.elim (hx0 (m4_minor_012_023 x hx3 hy0 hy2 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · exact False.elim (hx0 (m4_minor_012_123 x hx3 hy1 hy2 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
  · by_cases hy0 : (applyM4 x).x0 = Goldilocks.zero <;>
      by_cases hy1 : (applyM4 x).x1 = Goldilocks.zero <;>
      by_cases hy2 : (applyM4 x).x2 = Goldilocks.zero <;>
      by_cases hy3 : (applyM4 x).x3 = Goldilocks.zero
    · exact False.elim (hx0 (m4_minor_0123_0123 x hy0 hy1 hy2 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]

def vectorLane4 (x : Fin 4 → Goldilocks) : Lane4 := ⟨x 0, x 1, x 2, x 3⟩

def lane4Vector (x : Lane4) (i : Fin 4) : Goldilocks :=
  if i.val = 0 then x.x0 else if i.val = 1 then x.x1 else if i.val = 2 then x.x2 else x.x3

def hammingWeight4 (x : Fin 4 → Goldilocks) : Nat := laneWeight4 (vectorLane4 x)

/-- Function-vector interface to the deployed four-lane matrix. -/
def applyM4Vector (x : Fin 4 → Goldilocks) : Fin 4 → Goldilocks :=
  lane4Vector (applyM4 (vectorLane4 x))

private theorem vectorLane4_lane4Vector (x : Lane4) : vectorLane4 (lane4Vector x) = x := by
  cases x
  rfl

/-- Exact branch number: universal lower bound and an attaining nonzero input. -/
theorem m4_mds_branch_number_eq_five :
    (∀ x : Fin 4 → Goldilocks, x ≠ (fun _ => Goldilocks.zero) →
      5 ≤ hammingWeight4 x + hammingWeight4 (applyM4Vector x)) ∧
    (∃ x : Fin 4 → Goldilocks, x ≠ (fun _ => Goldilocks.zero) ∧
      hammingWeight4 x + hammingWeight4 (applyM4Vector x) = 5) := by
  constructor
  · intro x hx
    have hn : vectorLane4 x ≠ lane4Zero := by
      intro hz
      apply hx
      funext i
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
        have := i.isLt
        omega
      rcases hi with rfl | rfl | rfl | rfl
      · exact congrArg Lane4.x0 hz
      · exact congrArg Lane4.x1 hz
      · exact congrArg Lane4.x2 hz
      · exact congrArg Lane4.x3 hz
    simpa only [hammingWeight4, applyM4Vector, vectorLane4_lane4Vector] using
      m4_mds_branch_lower (vectorLane4 x) hn
  · refine ⟨lane4Vector ⟨Goldilocks.one, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩, ?_, ?_⟩
    · intro h
      have := congrFun h 0
      contradiction
    · decide


/-! ## 6. Two-round differential activity for the deployed four-lane S-box/MDS component -/

private theorem gold_sub_zero_iff (a b : Goldilocks) :
    Goldilocks.sub a b = Goldilocks.zero ↔ a = b :=
  LawfulCommRing.sub_eq_zero_iff

private theorem sbox7_add_diff_zero_iff (a b c : Goldilocks) :
    Goldilocks.sub (sbox7 (Goldilocks.add a c)) (sbox7 (Goldilocks.add b c)) =
      Goldilocks.zero ↔ Goldilocks.sub a b = Goldilocks.zero := by
  rw [gold_sub_zero_iff, (sbox7_bijective _ _).2.2.1, gold_sub_zero_iff]
  constructor
  · intro h
    apply LawfulCommRing.add_left_cancel (a := c)
    change Goldilocks.add c a = Goldilocks.add c b
    simpa only [show ∀ u v : Goldilocks, Goldilocks.add u v = Goldilocks.add v u from
      LawfulCommRing.add_comm] using h
  · intro h
    rw [h]

/-- Bijection of the actual seventh-power S-box preserves differential support, also after
    adding an arbitrary shared round constant. -/
theorem sbox7_preserves_differential_activity (a b rc : Lane4) :
    laneWeight4 (lane4Sub (sboxLane4 (lane4Add a rc)) (sboxLane4 (lane4Add b rc))) =
      laneWeight4 (lane4Sub a b) := by
  simp only [laneWeight4, lane4Sub, sboxLane4, lane4Add, sbox7_add_diff_zero_iff]
  rfl

private theorem applyM4_sub (a b : Lane4) :
    lane4Sub (applyM4 a) (applyM4 b) = applyM4 (lane4Sub a b) := by
  unfold applyM4 lane4Sub lane4Sum
  apply Lane4.ext <;>
    (dsimp only
     rw [← goldOfInt_nat a.x0, ← goldOfInt_nat a.x1,
       ← goldOfInt_nat a.x2, ← goldOfInt_nat a.x3,
       ← goldOfInt_nat b.x0, ← goldOfInt_nat b.x1,
       ← goldOfInt_nat b.x2, ← goldOfInt_nat b.x3]
     simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_sub, goldOfInt_mul]
     congr 1
     omega)

private theorem lane4Sub_eq_zero_iff (a b : Lane4) : lane4Sub a b = lane4Zero ↔ a = b := by
  constructor
  · intro h
    apply Lane4.ext
    · exact (gold_sub_zero_iff _ _).mp (congrArg Lane4.x0 h)
    · exact (gold_sub_zero_iff _ _).mp (congrArg Lane4.x1 h)
    · exact (gold_sub_zero_iff _ _).mp (congrArg Lane4.x2 h)
    · exact (gold_sub_zero_iff _ _).mp (congrArg Lane4.x3 h)
  · intro h
    subst b
    apply Lane4.ext <;> exact (gold_sub_zero_iff _ _).mpr rfl

/-- One full round of the four-lane component: shared constant, actual S-box, actual M4. -/
def poseidon2Round4 (rc x : Lane4) : Lane4 := applyM4 (sboxLane4 (lane4Add x rc))

/-- At least five active S-boxes across two successive four-lane rounds. The first term counts
    the first S-box inputs and the second counts the next round's S-box inputs. Arbitrary shared
    round constants preserve these counts. This is a structural bound, not a probability claim
    for the full twelve-lane permutation or for partial rounds. -/
theorem poseidon2_two_round_active_sboxes_ge_five (a b rc : Lane4) (hne : a ≠ b) :
    5 ≤ laneWeight4 (lane4Sub a b) +
      laneWeight4 (lane4Sub (poseidon2Round4 rc a) (poseidon2Round4 rc b)) := by
  let d := lane4Sub (sboxLane4 (lane4Add a rc)) (sboxLane4 (lane4Add b rc))
  have hd : d ≠ lane4Zero := by
    intro h
    have hEq := (lane4Sub_eq_zero_iff _ _).mp h
    apply hne
    apply Lane4.ext
    · exact (gold_sub_zero_iff _ _).mp ((sbox7_add_diff_zero_iff _ _ _).mp
        ((gold_sub_zero_iff _ _).mpr (congrArg Lane4.x0 hEq)))
    · exact (gold_sub_zero_iff _ _).mp ((sbox7_add_diff_zero_iff _ _ _).mp
        ((gold_sub_zero_iff _ _).mpr (congrArg Lane4.x1 hEq)))
    · exact (gold_sub_zero_iff _ _).mp ((sbox7_add_diff_zero_iff _ _ _).mp
        ((gold_sub_zero_iff _ _).mpr (congrArg Lane4.x2 hEq)))
    · exact (gold_sub_zero_iff _ _).mp ((sbox7_add_diff_zero_iff _ _ _).mp
        ((gold_sub_zero_iff _ _).mpr (congrArg Lane4.x3 hEq)))
  have hm := m4_mds_branch_lower d hd
  rw [sbox7_preserves_differential_activity] at hm
  simpa only [poseidon2Round4, applyM4_sub] using hm

private theorem laneWeight4_le_four (x : Lane4) : laneWeight4 x ≤ 4 := by
  unfold laneWeight4
  split <;> split <;> split <;> split <;> decide

private theorem poseidon2Round4_injective (rc : Lane4) (a b : Lane4)
    (h : poseidon2Round4 rc a = poseidon2Round4 rc b) : a = b := by
  if he : a = b then exact he else
    have hm := poseidon2_two_round_active_sboxes_ge_five a b rc he
    have hu := laneWeight4_le_four (lane4Sub a b)
    have hz := (lane4Sub_eq_zero_iff _ _).mpr h
    rw [hz] at hm
    have hw : laneWeight4 lane4Zero = 0 := rfl
    rw [hw] at hm
    omega

/-- Eight full four-lane rounds contain four disjoint two-round windows. This counts actual
    differential supports in a supplied nonzero trajectory, rather than a nominal round floor. -/
theorem poseidon2_eight_round_active_sboxes_ge_twenty
    (a b : Nat → Lane4) (rc : Nat → Lane4)
    (ha : ∀ i, a (i + 1) = poseidon2Round4 (rc i) (a i))
    (hb : ∀ i, b (i + 1) = poseidon2Round4 (rc i) (b i))
    (hInitial : a 0 ≠ b 0) :
    20 ≤ (laneWeight4 (lane4Sub (a 0) (b 0)) + laneWeight4 (lane4Sub (a 1) (b 1))) +
      (laneWeight4 (lane4Sub (a 2) (b 2)) + laneWeight4 (lane4Sub (a 3) (b 3))) +
      (laneWeight4 (lane4Sub (a 4) (b 4)) + laneWeight4 (lane4Sub (a 5) (b 5))) +
      (laneWeight4 (lane4Sub (a 6) (b 6)) + laneWeight4 (lane4Sub (a 7) (b 7))) := by
  have hne : ∀ i, a i ≠ b i := by
    intro i
    induction i with
    | zero => exact hInitial
    | succ i ih =>
      intro h
      rw [ha i, hb i] at h
      exact ih (poseidon2Round4_injective (rc i) (a i) (b i) h)
  have h0 := poseidon2_two_round_active_sboxes_ge_five (a 0) (b 0) (rc 0) (hne 0)
  have h2 := poseidon2_two_round_active_sboxes_ge_five (a 2) (b 2) (rc 2) (hne 2)
  have h4 := poseidon2_two_round_active_sboxes_ge_five (a 4) (b 4) (rc 4) (hne 4)
  have h6 := poseidon2_two_round_active_sboxes_ge_five (a 6) (b 6) (rc 6) (hne 6)
  rw [← ha 0, ← hb 0] at h0
  rw [← ha 2, ← hb 2] at h2
  rw [← ha 4, ← hb 4] at h4
  rw [← ha 6, ← hb 6] at h6
  simp only [Nat.reduceAdd] at h0 h2 h4 h6
  omega


/-! ### Symbolic degree of actual four-lane rounds -/

/-- Scalar polynomial syntax. Degree here is a syntactic upper bound; cancellations and
    reduction modulo `X^p - X` may lower the degree of the induced field function. -/
inductive PoseidonExpr where
  | variable : Nat → PoseidonExpr
  | constant : Goldilocks → PoseidonExpr
  | add : PoseidonExpr → PoseidonExpr → PoseidonExpr
  | mul : PoseidonExpr → PoseidonExpr → PoseidonExpr

def PoseidonExpr.eval (v : Nat → Goldilocks) : PoseidonExpr → Goldilocks
  | .variable i => v i
  | .constant c => c
  | .add a b => Goldilocks.add (a.eval v) (b.eval v)
  | .mul a b => Goldilocks.mul (a.eval v) (b.eval v)

def PoseidonExpr.degree : PoseidonExpr → Nat
  | .variable _ => 1
  | .constant _ => 0
  | .add a b => max a.degree b.degree
  | .mul a b => a.degree + b.degree

/-- Exactly the multiplication circuit used by `sbox7`. -/
def PoseidonExpr.seventh (x : PoseidonExpr) : PoseidonExpr :=
  let x2 := .mul x x
  let x3 := .mul x2 x
  let x4 := .mul x2 x2
  .mul x3 x4

theorem symbolic_sbox7_eval (v : Nat → Goldilocks) (x : PoseidonExpr) :
    x.seventh.eval v = sbox7 (x.eval v) := by
  simp only [PoseidonExpr.seventh, PoseidonExpr.eval, sbox7]

theorem symbolic_sbox7_degree (x : PoseidonExpr) : x.seventh.degree = 7 * x.degree := by
  simp only [PoseidonExpr.seventh, PoseidonExpr.degree]
  omega

private def symbolicM4Lane (s a b : PoseidonExpr) : PoseidonExpr :=
  .add s (.add a (.mul (.constant (Goldilocks.ofNat 2)) b))

/-- The operational circuit of `applyM4`, lifted to polynomial expressions. -/
def symbolicM4 (x : Fin 4 → PoseidonExpr) (i : Fin 4) : PoseidonExpr :=
  let s := PoseidonExpr.add (.add (x 0) (x 1)) (.add (x 2) (x 3))
  if i.val = 0 then symbolicM4Lane s (x 0) (x 1)
  else if i.val = 1 then symbolicM4Lane s (x 1) (x 2)
  else if i.val = 2 then symbolicM4Lane s (x 2) (x 3)
  else symbolicM4Lane s (x 3) (x 0)

private theorem fin4_cases (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  have := i.isLt
  omega

theorem symbolicM4_eval (v : Nat → Goldilocks) (x : Fin 4 → PoseidonExpr) :
    (fun i => (symbolicM4 x i).eval v) = applyM4Vector (fun i => (x i).eval v) := by
  funext i
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;> rfl

theorem symbolicM4_degree_le (x : Fin 4 → PoseidonExpr) (k : Nat)
    (hx : ∀ i, (x i).degree ≤ k) (i : Fin 4) : (symbolicM4 x i).degree ≤ k := by
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  have h3 := hx 3
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;>
    (simp [symbolicM4, symbolicM4Lane, PoseidonExpr.degree, show (3 : Fin 4).val = 3 from rfl]
     omega)

/-- Shared round constants are degree zero; each round multiplies the degree bound by seven. -/
def symbolicRound4 (rc : Lane4) (x : Fin 4 → PoseidonExpr) : Fin 4 → PoseidonExpr :=
  symbolicM4 (fun i => (PoseidonExpr.add (x i) (.constant (lane4Vector rc i))).seventh)

theorem symbolicRound4_eval (v : Nat → Goldilocks) (rc : Lane4)
    (x : Fin 4 → PoseidonExpr) :
    (fun i => (symbolicRound4 rc x i).eval v) =
      lane4Vector (poseidon2Round4 rc (vectorLane4 (fun i => (x i).eval v))) := by
  rw [symbolicRound4, symbolicM4_eval]
  rfl

theorem symbolicRound4_degree_le (rc : Lane4) (x : Fin 4 → PoseidonExpr) (k : Nat)
    (hx : ∀ i, (x i).degree ≤ k) (i : Fin 4) : (symbolicRound4 rc x i).degree ≤ 7 * k := by
  apply symbolicM4_degree_le
  intro j
  rw [symbolic_sbox7_degree]
  simp only [PoseidonExpr.degree, Nat.max_zero]
  exact Nat.mul_le_mul_left 7 (hx j)

/-- Round-by-round symbolic bound for any sequence of actual four-lane rounds, starting with
    coordinate variables. This gives `7^r` as an upper bound, never as a lower bound on security. -/
theorem poseidon2_symbolic_round_degree_bound (x : Nat → Fin 4 → PoseidonExpr)
    (rc : Nat → Lane4) (h0 : ∀ i, x 0 i = .variable i.val)
    (hstep : ∀ r, x (r + 1) = symbolicRound4 (rc r) (x r)) :
    ∀ r i, (x r i).degree ≤ 7 ^ r := by
  intro r
  induction r with
  | zero => intro i; rw [h0]; exact Nat.le_refl 1
  | succ r ih =>
    intro i
    rw [hstep]
    have h := symbolicRound4_degree_le (rc r) (x r) (7 ^ r) ih i
    simpa only [Nat.pow_succ, Nat.mul_comm] using h

/-! ## 7. Concrete accepting hierarchical certificates & prover transcripts -/

/-- Two distinct singleton committees use the same relation `x^7 = 0`, represented by
    `(seed, root) = (0, 0)` and `(1, 1)`. Both use the honest two-stage WHIR prover.
    This is an inhabitedness example for the field-based signature suite, not a security
    assertion about that suite. The threshold and the actual signer count are both one. -/
def concreteHemShard (second : Bool) : HemShardProof :=
  let seed := if second then Goldilocks.one else Goldilocks.zero
  let sid : List UInt8 := [if second then 1 else 0]
  let msg := shardBoundMessage sid [] []
  let bundle := buildHonestSbox7WhirBundle seed Goldilocks.zero Goldilocks.one msg
  { shardId := sid, threshold := 1, inst := rsSbox7Inst seed seed msg,
    proof := bundle.1, fs := bundle.2.1 }

def concreteHemArith : RowArithmetization := rsSbox7TraceArith Goldilocks.zero Goldilocks.zero

def concreteHemRegistry : List ShardRegistration :=
  [concreteHemShard false, concreteHemShard true].map HemShardProof.registration

def concreteHemRegistryDigest : List UInt8 :=
  poseidon2Hash32 (encodeRegistry concreteHemRegistry)

private theorem concreteHemArith_eq_seed (second : Bool) :
    let seed := if second then Goldilocks.one else Goldilocks.zero
    rsSbox7TraceArith seed (CommRingOps.add (pow7Goldilocks Goldilocks.zero) seed) =
      concreteHemArith := by
  cases second <;>
    (dsimp only [concreteHemArith, rsSbox7TraceArith]
     congr 1)

private theorem concreteSeedRoot_eq (second : Bool) :
    let seed := if second then Goldilocks.one else Goldilocks.zero
    CommRingOps.add (pow7Goldilocks Goldilocks.zero) seed = seed := by
  cases second <;> decide

theorem concreteHemShard_accepts (second : Bool) :
    verifyHemShard concreteHemArith rsSbox7WhirDomain [] [] (concreteHemShard second) = true := by
  have hAcc := (honestSbox7WhirProof_accepts
    (if second then Goldilocks.one else Goldilocks.zero)
    Goldilocks.zero Goldilocks.one
    (shardBoundMessage [if second then 1 else 0] [] [])).1
  rw [concreteHemArith_eq_seed second, concreteSeedRoot_eq second] at hAcc
  have c1 : decide ((concreteHemShard second).inst.message =
      shardBoundMessage (concreteHemShard second).shardId [] []) = true := by
    cases second <;> exact decide_eq_true rfl
  have c2 : decide (1 ≤ (concreteHemShard second).threshold) = true := by
    cases second <;> decide
  have c3 : decide ((concreteHemShard second).threshold ≤
      (concreteHemShard second).inst.committee.length) = true := by
    cases second <;> decide
  have c4 : decide ((concreteHemShard second).threshold ≤
      bitmapPopcountSpec (concreteHemShard second).proof.agg.bitmap) = true := by
    cases second <;> exact decide_eq_true (Nat.le_refl 1)
  unfold verifyHemShard
  rw [c1, c2, c3, c4]
  exact hAcc

theorem concreteHemShard_lawful (second : Bool) :
    concreteHemArith.Lawful rsSbox7WhirDomain (concreteHemShard second).inst := by
  cases second
  · exact rsSbox7TraceArith_lawful Goldilocks.zero Goldilocks.zero (shardBoundMessage [0] [] [])
  · have hLaw := rsSbox7TraceArith_lawful Goldilocks.one Goldilocks.one (shardBoundMessage [1] [] [])
    have hEq : rsSbox7TraceArith Goldilocks.one Goldilocks.one = concreteHemArith := by
      dsimp only [concreteHemArith, rsSbox7TraceArith]
      congr 1
    rwa [hEq] at hLaw

/-- Concrete prover commitment-opening transcript for `concreteHemShard second`. -/
def concreteHemShardTranscript (second : Bool) :
    ShardProverTranscript concreteHemArith rsSbox7WhirDomain :=
  let seed := if second then Goldilocks.one else Goldilocks.zero
  let sid : List UInt8 := [if second then 1 else 0]
  let msg := shardBoundMessage sid [] []
  let bundle := buildHonestSbox7WhirBundle seed Goldilocks.zero Goldilocks.one msg
  { shard := concreteHemShard second
    law := concreteHemShard_lawful second
    transcript := transcriptOfBoundView rsSbox7WhirDomain bundle.2.2 }

theorem concreteHemShardTranscript_accepts (second : Bool) :
    verifyCommittedTableTranscript rsSbox7WhirDomain (concreteHemShard second).proof
      (concreteHemShardTranscript second).transcript = true := by
  have hBound := (honestSbox7WhirProof_accepts
    (if second then Goldilocks.one else Goldilocks.zero)
    Goldilocks.zero Goldilocks.one
    (shardBoundMessage [if second then 1 else 0] [] [])).2
  have hNodup : (rsSbox7WhirDomain.stages.map (·.stageIdx)).Nodup := by decide
  exact verifyCommittedTableTranscript_transcriptOfBoundView rsSbox7WhirDomain _ _ hNodup hBound

/-- A root certificate with two distinct shard ids, two distinct public keys, and two active
    signers. Its registry commitment is computed by the deployed Poseidon2 hash. -/
theorem inhabited_verifyHierarchicalHem_two_shards :
    verifyHierarchicalHem poseidon2Hash32 concreteHemArith rsSbox7WhirDomain
      concreteHemRegistryDigest [] [] [concreteHemShard false, concreteHemShard true] = true ∧
    verifyHemHierarchyAgainstRegistry concreteHemArith rsSbox7WhirDomain
      concreteHemRegistry [] [] [concreteHemShard false, concreteHemShard true] = true ∧
    hierarchicalClaimedWeight [concreteHemShard false, concreteHemShard true] = 2 ∧
    hierarchicalThresholdSum [concreteHemShard false, concreteHemShard true] = 2 ∧
    registryThresholdSum concreteHemRegistry = 2 := by
  have hIds : (hierarchicalShardIds [concreteHemShard false, concreteHemShard true]).Nodup := by
    decide
  have hKeys : (hierarchicalCommittee [concreteHemShard false, concreteHemShard true]).Nodup := by
    decide
  have hall : [concreteHemShard false, concreteHemShard true].all
      (verifyHemShard concreteHemArith rsSbox7WhirDomain [] []) = true := by
    simp only [List.all_cons, List.all_nil, concreteHemShard_accepts, Bool.and_self]
  have hWf : concreteHemRegistry.all ShardRegistration.WellFormed = true := by decide
  have hDig : decide (poseidon2Hash32 (encodeRegistry
      ([concreteHemShard false, concreteHemShard true].map HemShardProof.registration)) =
      concreteHemRegistryDigest) = true := decide_eq_true rfl
  have hRegEq : decide ([concreteHemShard false, concreteHemShard true].map
      HemShardProof.registration = concreteHemRegistry) = true := decide_eq_true rfl
  refine ⟨?_, ?_, rfl, rfl, rfl⟩
  · unfold verifyHierarchicalHem
    rw [hDig, decide_eq_true hIds, decide_eq_true hKeys, hall]
    rfl
  · unfold verifyHemHierarchyAgainstRegistry
    rw [hWf, hRegEq, decide_eq_true hIds, decide_eq_true hKeys, hall]
    rfl

/-- End-to-end inhabitedness of transcript-grounded hierarchical extraction & query cost accounting:
    two concrete prover transcripts pass `verifyCommittedTableTranscript` with exact sweep cost
    `hierarchyTranscriptQueryCost rsSbox7WhirDomain 2 = 24`. -/
theorem inhabited_transcript_grounded_two_shards :
    let trs := [concreteHemShardTranscript false, concreteHemShardTranscript true]
    (∀ t ∈ trs, verifyCommittedTableTranscript rsSbox7WhirDomain t.shard.proof t.transcript = true) ∧
    verifyHierarchicalHem poseidon2Hash32 concreteHemArith rsSbox7WhirDomain
      concreteHemRegistryDigest [] [] (trs.map (·.shard)) = true ∧
    hierarchySweepOpeningCount trs = 24 ∧
    hierarchyTranscriptQueryCost rsSbox7WhirDomain trs.length = 24 := by
  intro trs
  have hAllTr : ∀ t ∈ trs,
      verifyCommittedTableTranscript rsSbox7WhirDomain t.shard.proof t.transcript = true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht'
    · exact concreteHemShardTranscript_accepts false
    · rcases List.mem_cons.mp ht' with rfl | hNil
      · exact concreteHemShardTranscript_accepts true
      · cases hNil
  have hVer : verifyHierarchicalHem poseidon2Hash32 concreteHemArith rsSbox7WhirDomain
      concreteHemRegistryDigest [] [] (trs.map (·.shard)) = true :=
    inhabited_verifyHierarchicalHem_two_shards.1
  have hF := verifyHierarchicalHem_facts hVer
  have hCostEq : hierarchySweepOpeningCount trs =
      hierarchyTranscriptQueryCost rsSbox7WhirDomain trs.length :=
    hierarchySweepOpeningCount_eq_queryCost trs (fun t ht =>
      ⟨hF.2.2.2 t.shard (List.mem_map.mpr ⟨t, ht, rfl⟩), hAllTr t ht⟩)
  have hQuery24 : hierarchyTranscriptQueryCost rsSbox7WhirDomain trs.length = 24 := by decide
  exact ⟨hAllTr, hVer, hCostEq.trans hQuery24, hQuery24⟩

/-- Kernel-reducible UTF-8 bytes of `"QSAG.PQ.SUITE.SBOX7/v1"` for concrete Poseidon2 evaluation. -/
def concretePoseidonSuiteTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2e, 0x50, 0x51, 0x2e, 0x53, 0x55, 0x49, 0x54,
   0x45, 0x2e, 0x53, 0x42, 0x4f, 0x58, 0x37, 0x2f, 0x76, 0x31]

def concreteTwoKeyCommittee : List PqPublicKey :=
  [mkSbox7Pk Goldilocks.zero Goldilocks.zero, mkSbox7Pk Goldilocks.one Goldilocks.one]

def concreteTwoKeyRegistry : List ShardRegistration :=
  [{ shardId := [0]
     threshold := 2
     suiteId := concretePoseidonSuiteTag
     params := sbox7Params
     committee := concreteTwoKeyCommittee }]

def concreteTwoKeyRegistryDigest : List UInt8 :=
  poseidon2Hash32 (encodeRegistry concreteTwoKeyRegistry)

def concreteLoweredTwoKeyShard : HemShardProof :=
  let base := concreteHemShard false
  { shardId := [0]
    threshold := 1
    inst := { rsSbox7Inst Goldilocks.zero Goldilocks.zero (shardBoundMessage [0] [] []) with
              suite := { sbox7FieldSuite with suiteId := concretePoseidonSuiteTag }
              committee := concreteTwoKeyCommittee }
    proof := base.proof
    fs := base.fs }

set_option maxRecDepth 16384 in
/-- `#tooth` **Forged Lower Shard Threshold Rejected (`tooth_forged_lower_shard_threshold_rejected`)**:
    (a) **General security refutation**: for any hash `H`, registered policy `registry`, and
        submitted `shards`, if shard `i` lowers `threshold < (registry[i]).threshold` under an
        unchanged `registryDigest = H (encodeRegistry registry)`, then
        `verifyHemHierarchyAgainstRegistry` unconditionally returns `false`, and either
        `verifyHierarchicalHem` returns `false` or `forgedLowerThreshold_rejected_or_collision`
        constructively extracts a `HashCollisionWitness H`.
    (b) **Concrete `poseidon2Hash32` witnesses**:
        1. Lowering shard `0`'s threshold from `1` to `0` on the accepted two-shard Poseidon2
           hierarchy flips `verifyHierarchicalHem` from `true` to `false`.
        2. Lowering a 2-key committee's threshold from `2` to `1` (while keeping `1 ≤ 1 ≤ 2`
           well-formed and keeping `shardId`, `suiteId`, `params`, and `committee` identical)
           changes the concrete `poseidon2Hash32` registry digest and causes
           `verifyHierarchicalHem` to evaluate to `false`. -/
theorem tooth_forged_lower_shard_threshold_rejected :
    (∀ (H : Hash) (arith : RowArithmetization) (dom : WhirDomain)
       (registryDigest epochFloor msg : List UInt8) (registry : List ShardRegistration)
       (_hReg : H (encodeRegistry registry) = registryDigest)
       (shards : List HemShardProof) (i : Nat)
       (hiS : i < shards.length) (hiR : i < registry.length),
      (shards[i]'hiS).threshold < (registry[i]'hiR).threshold →
      verifyHemHierarchyAgainstRegistry arith dom registry epochFloor msg shards = false ∧
      (verifyHierarchicalHem H arith dom registryDigest epochFloor msg shards = false ∨
       Nonempty (HashCollisionWitness H))) ∧
    verifyHierarchicalHem poseidon2Hash32 concreteHemArith rsSbox7WhirDomain
      concreteHemRegistryDigest [] []
      [{ concreteHemShard false with threshold := 0 }, concreteHemShard true] = false ∧
    concreteLoweredTwoKeyShard.registration.WellFormed = true ∧
    poseidon2Hash32 (encodeRegistry [concreteLoweredTwoKeyShard.registration]) ≠
      concreteTwoKeyRegistryDigest ∧
    verifyHierarchicalHem poseidon2Hash32 concreteHemArith rsSbox7WhirDomain
      concreteTwoKeyRegistryDigest [] [] [concreteLoweredTwoKeyShard] = false := by
  have hDigNe :
      poseidon2Hash32 (encodeRegistry [concreteLoweredTwoKeyShard.registration]) ≠
        concreteTwoKeyRegistryDigest := by
    unfold concreteTwoKeyRegistryDigest
    decide
  refine ⟨?_, ?_, by decide, hDigNe, ?_⟩
  · intro H arith dom registryDigest epochFloor msg registry hReg shards i hiS hiR hLower
    match forgedLowerThreshold_rejected_or_collision H arith dom registryDigest epochFloor msg
        registry hReg shards i hiS hiR hLower with
    | .inl ⟨hHierFalse, hDirectFalse⟩ => exact ⟨hDirectFalse, .inl hHierFalse⟩
    | .inr col =>
      have hNe : shards.map HemShardProof.registration ≠ registry := fun hEq => by
        have hAt : (shards.map HemShardProof.registration)[i]? = registry[i]? :=
          congrArg (·[i]?) hEq
        rw [List.getElem?_map, List.getElem?_eq_getElem hiS, List.getElem?_eq_getElem hiR,
            Option.map_some, Option.some.injEq] at hAt
        have hThr : (shards[i]'hiS).threshold = (registry[i]'hiR).threshold :=
          congrArg ShardRegistration.threshold hAt
        exact absurd (hThr ▸ hLower) (Nat.lt_irrefl _)
      refine ⟨?_, .inr ⟨col⟩⟩
      unfold verifyHemHierarchyAgainstRegistry
      simp [decide_eq_false hNe]
  · apply Bool.eq_false_iff.mpr
    intro hAcc
    have hAll := (verifyHierarchicalHem_facts hAcc).2.2.2
    have h0 := hAll { concreteHemShard false with threshold := 0 } (List.mem_cons_self ..)
    have hGe1 := (verifyHemShard_facts h0).2.1
    simp at hGe1
  · unfold verifyHierarchicalHem
    have hDigNeMap :
        poseidon2Hash32 (encodeRegistry ([concreteLoweredTwoKeyShard].map
          HemShardProof.registration)) ≠ concreteTwoKeyRegistryDigest := hDigNe
    rw [decide_eq_false hDigNeMap]
    rfl

/-- Unconditional replay: the same actual accepting one-signer certificate is counted twice
    by the unscoped verifier, while the scoped root rejects it. No accepted-shard premise. -/
theorem tooth_concrete_unscoped_shard_replay :
    verifyHierarchicalHemUnscoped concreteHemArith rsSbox7WhirDomain
      [concreteHemShard false, concreteHemShard false] = true ∧
    hierarchicalClaimedWeight [concreteHemShard false, concreteHemShard false] = 2 ∧
    bitmapPopcountSpec (concreteHemShard false).proof.agg.bitmap = 1 ∧
    (∀ q ∈ hierarchicalActiveSlots [concreteHemShard false, concreteHemShard false],
      q ∈ shardActiveSlots (concreteHemShard false)) ∧
    verifyHierarchicalHem poseidon2Hash32 concreteHemArith rsSbox7WhirDomain
      concreteHemRegistryDigest [] [] [concreteHemShard false, concreteHemShard false] = false := by
  have h := tooth_unscoped_shard_id_allows_quorum_replay_multiplication
    poseidon2Hash32 concreteHemArith rsSbox7WhirDomain concreteHemRegistryDigest [] []
    (concreteHemShard false) 2 (by decide) (concreteHemShard_accepts false)
  exact ⟨h.1, rfl, rfl, h.2.2.2.1, h.2.2.2.2⟩

/-- Nonvacuity of the deployed-width interpolation-margin premise. -/
theorem witness_poseidon2_margin : ∃ t rF rP, Poseidon2InterpolationMargin t rF rP :=
  ⟨12, 8, 22, poseidon2_interpolation_margin_width12⟩

/-! ## 8. Width-12 `M_E` & `M_I` Differential/Linear Branch Numbers & `2026/306` Subspace Analysis -/

/-- Exact 12-lane Hamming weight (count of nonzero `Goldilocks` elements) on `Poseidon2State12`. -/
def stateWeight12 (s : Poseidon2State12) : Nat :=
  laneWeight4 s.b0 + laneWeight4 s.b1 + laneWeight4 s.b2

/-- Count of nonzero 4-lane blocks in `Poseidon2State12` (`0..3`). -/
def activeBlocks12 (s : Poseidon2State12) : Nat :=
  (if s.b0 = lane4Zero then 0 else 1) +
  (if s.b1 = lane4Zero then 0 else 1) +
  (if s.b2 = lane4Zero then 0 else 1)

def lane4Neg (a : Lane4) : Lane4 := lane4Sub lane4Zero a

def lane4Rev (a : Lane4) : Lane4 := ⟨a.x0, a.x3, a.x2, a.x1⟩

def state12Rev4 (s : Poseidon2State12) : Poseidon2State12 :=
  ⟨lane4Rev s.b0, lane4Rev s.b1, lane4Rev s.b2⟩

/-- Exact transpose of `applyME` with respect to the standard 12-lane dot product. -/
def applyMETranspose (s : Poseidon2State12) : Poseidon2State12 :=
  state12Rev4 (applyME (state12Rev4 s))

def lane4Dot (a b : Lane4) : Goldilocks :=
  Goldilocks.add
    (Goldilocks.add (Goldilocks.mul a.x0 b.x0) (Goldilocks.mul a.x1 b.x1))
    (Goldilocks.add (Goldilocks.mul a.x2 b.x2) (Goldilocks.mul a.x3 b.x3))

def state12Dot (a b : Poseidon2State12) : Goldilocks :=
  Goldilocks.add (Goldilocks.add (lane4Dot a.b0 b.b0) (lane4Dot a.b1 b.b1)) (lane4Dot a.b2 b.b2)

private theorem gold_add_eq_zero_of_both_zero {a b : Goldilocks}
    (ha : a = Goldilocks.zero) (hb : b = Goldilocks.zero) :
    Goldilocks.add a b = Goldilocks.zero := by
  subst ha; subst hb; rfl

private theorem gold_sub_eq_zero_of_both_zero {a b : Goldilocks}
    (ha : a = Goldilocks.zero) (hb : b = Goldilocks.zero) :
    Goldilocks.sub a b = Goldilocks.zero := by
  subst ha; subst hb; rfl

private theorem coord_wt_add_le (a b : Goldilocks) :
    (if Goldilocks.add a b = Goldilocks.zero then 0 else 1) ≤
      (if a = Goldilocks.zero then 0 else 1) + (if b = Goldilocks.zero then 0 else 1) := by
  by_cases ha : a = Goldilocks.zero <;> by_cases hb : b = Goldilocks.zero
  · rw [gold_add_eq_zero_of_both_zero ha hb]; simp [ha, hb]
  · simp [ha, hb]; split <;> omega
  · simp [ha, hb]; split <;> omega
  · simp [ha, hb]; split <;> omega

private theorem coord_wt_sub_le (a b : Goldilocks) :
    (if Goldilocks.sub a b = Goldilocks.zero then 0 else 1) ≤
      (if a = Goldilocks.zero then 0 else 1) + (if b = Goldilocks.zero then 0 else 1) := by
  by_cases ha : a = Goldilocks.zero <;> by_cases hb : b = Goldilocks.zero
  · rw [gold_sub_eq_zero_of_both_zero ha hb]; simp [ha, hb]
  · simp [ha, hb]; split <;> omega
  · simp [ha, hb]; split <;> omega
  · simp [ha, hb]; split <;> omega

private theorem coord_wt_mul_nz {c : Goldilocks} (hc : c ≠ Goldilocks.zero) (a : Goldilocks) :
    (if Goldilocks.mul c a = Goldilocks.zero then 0 else 1) =
      (if a = Goldilocks.zero then 0 else 1) := by
  by_cases ha : a = Goldilocks.zero
  · subst ha
    have hz : Goldilocks.mul c Goldilocks.zero = Goldilocks.zero :=
      LawfulCommRing.mul_zero c
    simp [hz]
  · have hnz : Goldilocks.mul c a ≠ Goldilocks.zero := fun hm => by
      rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hm with h1 | h2
      · exact hc h1
      · exact ha h2
    simp [ha, hnz]

private theorem laneWeight4_pos_of_ne_zero {a : Lane4} (ha : a ≠ lane4Zero) :
    1 ≤ laneWeight4 a := by
  unfold laneWeight4
  by_cases h0 : a.x0 = Goldilocks.zero <;>
    by_cases h1 : a.x1 = Goldilocks.zero <;>
    by_cases h2 : a.x2 = Goldilocks.zero <;>
    by_cases h3 : a.x3 = Goldilocks.zero
  · exact False.elim (ha (Lane4.ext h0 h1 h2 h3))
  all_goals simp [h0, h1, h2, h3]

private theorem gold_add_cring (a b : Goldilocks) : Goldilocks.add a b = CommRingOps.add a b := rfl
private theorem gold_sub_cring (a b : Goldilocks) : Goldilocks.sub a b = CommRingOps.sub a b := rfl
private theorem gold_mul_cring (a b : Goldilocks) : Goldilocks.mul a b = CommRingOps.mul a b := rfl
private theorem gold_neg_cring (a : Goldilocks) : Goldilocks.neg a = CommRingOps.neg a := rfl
private theorem gold_zero_cring : Goldilocks.zero = (CommRingOps.zero : Goldilocks) := rfl
private theorem gold_one_cring : Goldilocks.one = (CommRingOps.one : Goldilocks) := rfl
private theorem gold_2_cring : Goldilocks.ofNat 2 = CRing.natCast 2 := by decide
private theorem gold_3_cring : Goldilocks.ofNat 3 = CRing.natCast 3 := by decide
private theorem gold_4_cring : Goldilocks.ofNat 4 = CRing.natCast 4 := by decide

macro "gold_cring" : tactic => `(tactic| (
  try dsimp only
  try simp only [gold_add_cring, gold_sub_cring, gold_mul_cring, gold_neg_cring,
    gold_zero_cring, gold_one_cring, gold_2_cring, gold_3_cring, gold_4_cring]
  try (open scoped Qsag.CRing in constructive_ring)))

private theorem laneWeight4_add_le (a b : Lane4) :
    laneWeight4 (lane4Add a b) ≤ laneWeight4 a + laneWeight4 b := by
  unfold laneWeight4 lane4Add
  dsimp only
  have h0 := coord_wt_add_le a.x0 b.x0
  have h1 := coord_wt_add_le a.x1 b.x1
  have h2 := coord_wt_add_le a.x2 b.x2
  have h3 := coord_wt_add_le a.x3 b.x3
  omega

private theorem laneWeight4_sub_le (a b : Lane4) :
    laneWeight4 (lane4Sub a b) ≤ laneWeight4 a + laneWeight4 b := by
  unfold laneWeight4 lane4Sub
  dsimp only
  have h0 := coord_wt_sub_le a.x0 b.x0
  have h1 := coord_wt_sub_le a.x1 b.x1
  have h2 := coord_wt_sub_le a.x2 b.x2
  have h3 := coord_wt_sub_le a.x3 b.x3
  omega

private theorem laneWeight4_scale_ne_zero {c : Goldilocks} (hc : c ≠ Goldilocks.zero) (a : Lane4) :
    laneWeight4 (lane4Scale c a) = laneWeight4 a := by
  unfold laneWeight4 lane4Scale
  dsimp only
  rw [coord_wt_mul_nz hc, coord_wt_mul_nz hc, coord_wt_mul_nz hc, coord_wt_mul_nz hc]

private theorem applyM4_ne_zero_of_ne_zero {a : Lane4} (ha : a ≠ lane4Zero) :
    applyM4 a ≠ lane4Zero := fun hz => by
  apply ha
  have hInv := congrArg applyM4Inv hz
  rw [applyM4Inv_applyM4] at hInv
  exact hInv.trans (by decide)

private def rot12 (s : Poseidon2State12) : Poseidon2State12 := ⟨s.b1, s.b2, s.b0⟩
private def swap01 (s : Poseidon2State12) : Poseidon2State12 := ⟨s.b1, s.b0, s.b2⟩

private theorem stateWeight12_rot12 (s : Poseidon2State12) :
    stateWeight12 (rot12 s) = stateWeight12 s := by
  unfold stateWeight12 rot12; dsimp only; omega

private theorem activeBlocks12_rot12 (s : Poseidon2State12) :
    activeBlocks12 (rot12 s) = activeBlocks12 s := by
  unfold activeBlocks12 rot12; dsimp only; omega

private theorem stateWeight12_swap01 (s : Poseidon2State12) :
    stateWeight12 (swap01 s) = stateWeight12 s := by
  unfold stateWeight12 swap01; dsimp only; omega

private theorem activeBlocks12_swap01 (s : Poseidon2State12) :
    activeBlocks12 (swap01 s) = activeBlocks12 s := by
  unfold activeBlocks12 swap01; dsimp only; omega

private theorem lane4Add_sum3_rot (a b c : Lane4) :
    lane4Add (lane4Add b c) a = lane4Add (lane4Add a b) c := by
  unfold lane4Add
  apply Lane4.ext <;> gold_cring

private theorem lane4Add_sum3_swap01 (a b c : Lane4) :
    lane4Add (lane4Add b a) c = lane4Add (lane4Add a b) c := by
  unfold lane4Add
  apply Lane4.ext <;> gold_cring

private theorem applyME_rot12 (s : Poseidon2State12) :
    applyME (rot12 s) = rot12 (applyME s) := by
  unfold applyME rot12
  dsimp only
  rw [lane4Add_sum3_rot]

private theorem applyME_swap01 (s : Poseidon2State12) :
    applyME (swap01 s) = swap01 (applyME s) := by
  unfold applyME swap01
  dsimp only
  rw [lane4Add_sum3_swap01]

private theorem applyME_single_b0 (b : Lane4) (hb : b ≠ lane4Zero) :
    7 ≤ stateWeight12 ⟨b, lane4Zero, lane4Zero⟩ +
      stateWeight12 (applyME ⟨b, lane4Zero, lane4Zero⟩) := by
  have hzM4 : applyM4 lane4Zero = lane4Zero := by decide
  have hOut : applyME ⟨b, lane4Zero, lane4Zero⟩ =
      ⟨lane4Scale (Goldilocks.ofNat 2) (applyM4 b), applyM4 b, applyM4 b⟩ := by
    unfold applyME
    dsimp only
    rw [hzM4]
    unfold lane4Add lane4Scale lane4Zero
    apply Poseidon2State12.ext <;> apply Lane4.ext <;> gold_cring
  rw [hOut]
  unfold stateWeight12
  dsimp only
  have h2nz : Goldilocks.ofNat 2 ≠ Goldilocks.zero := by decide
  rw [laneWeight4_scale_ne_zero h2nz, show laneWeight4 lane4Zero = 0 from rfl]
  have hm := m4_mds_branch_lower b hb
  have hy := laneWeight4_pos_of_ne_zero (applyM4_ne_zero_of_ne_zero hb)
  omega

/-- **Single-Active-Block Width-12 `M_E` Branch Bound (`poseidon2_me12_single_block_branch_ge_seven`)**:
    Across any nonzero state supported in a single 4-lane block (`activeBlocks12 x = 1`),
    `stateWeight12 x + stateWeight12 (applyME x) ≥ 7` (hence strictly above `5`). -/
theorem poseidon2_me12_single_block_branch_ge_seven (x : Poseidon2State12)
    (h1 : activeBlocks12 x = 1) :
    7 ≤ stateWeight12 x + stateWeight12 (applyME x) ∧
    5 ≤ stateWeight12 x + stateWeight12 (applyME x) := by
  have h7 : 7 ≤ stateWeight12 x + stateWeight12 (applyME x) := by
    unfold activeBlocks12 at h1
    by_cases hb0 : x.b0 = lane4Zero <;>
      by_cases hb1 : x.b1 = lane4Zero <;>
      by_cases hb2 : x.b2 = lane4Zero
    · simp [hb0, hb1, hb2] at h1
    · have hRot : rot12 (rot12 x) = ⟨x.b2, lane4Zero, lane4Zero⟩ :=
        Poseidon2State12.ext rfl hb0 hb1
      have hm := applyME_single_b0 x.b2 hb2
      rw [← hRot, stateWeight12_rot12, stateWeight12_rot12,
          applyME_rot12, applyME_rot12, stateWeight12_rot12, stateWeight12_rot12] at hm
      exact hm
    · have hRot : rot12 x = ⟨x.b1, lane4Zero, lane4Zero⟩ :=
        Poseidon2State12.ext rfl hb2 hb0
      have hm := applyME_single_b0 x.b1 hb1
      rw [← hRot, stateWeight12_rot12, applyME_rot12, stateWeight12_rot12] at hm
      exact hm
    · simp [hb0, hb1, hb2] at h1
    · have hx : x = ⟨x.b0, lane4Zero, lane4Zero⟩ :=
        Poseidon2State12.ext rfl hb1 hb2
      rw [hx]
      exact applyME_single_b0 x.b0 hb0
    · simp [hb0, hb1, hb2] at h1
    · simp [hb0, hb1, hb2] at h1
    · simp [hb0, hb1, hb2] at h1
  exact ⟨h7, by omega⟩

private theorem applyMEInv_single_b0 (z : Lane4) (hz : z ≠ lane4Zero) :
    7 ≤ stateWeight12 (applyMEInv ⟨z, lane4Zero, lane4Zero⟩) +
      stateWeight12 ⟨z, lane4Zero, lane4Zero⟩ := by
  let cinv4 : Goldilocks := Goldilocks.ofNat 13835058052060938241
  let c3 : Goldilocks := Goldilocks.mul (Goldilocks.ofNat 3) cinv4
  let cn1 : Goldilocks := Goldilocks.sub Goldilocks.zero cinv4
  have hc3nz : c3 ≠ Goldilocks.zero := fun h => absurd (congrArg Goldilocks.val h) (by decide)
  have hcn1nz : cn1 ≠ Goldilocks.zero := fun h => absurd (congrArg Goldilocks.val h) (by decide)
  have h4inv : Goldilocks.mul (Goldilocks.ofNat 4) cinv4 = Goldilocks.one :=
    Goldilocks.ext (by rw [Goldilocks.mul_val]; rfl)
  have hLinM4 : ∀ (c : Goldilocks) (v : Lane4), applyM4 (lane4Scale c v) = lane4Scale c (applyM4 v) :=
    fun c v => by
      unfold applyM4 lane4Scale lane4Sum
      apply Lane4.ext <;> gold_cring
  have hInvShape : applyMEInv ⟨z, lane4Zero, lane4Zero⟩ =
      ⟨lane4Scale c3 (applyM4Inv z), lane4Scale cn1 (applyM4Inv z), lane4Scale cn1 (applyM4Inv z)⟩ := by
    suffices hFwd : applyME ⟨lane4Scale c3 (applyM4Inv z),
        lane4Scale cn1 (applyM4Inv z), lane4Scale cn1 (applyM4Inv z)⟩ = ⟨z, lane4Zero, lane4Zero⟩ by
      have h := congrArg applyMEInv hFwd
      rw [applyMEInv_applyME] at h
      exact h.symm
    unfold applyME
    dsimp only
    rw [hLinM4, hLinM4, applyM4_applyM4Inv]
    unfold c3 cn1 lane4Add lane4Scale lane4Zero
    have hCoeff1 : ∀ a : Goldilocks,
        Goldilocks.add (Goldilocks.mul (Goldilocks.mul (Goldilocks.ofNat 3) cinv4) a)
          (Goldilocks.add (Goldilocks.add (Goldilocks.mul (Goldilocks.mul (Goldilocks.ofNat 3) cinv4) a)
            (Goldilocks.mul (Goldilocks.sub Goldilocks.zero cinv4) a))
            (Goldilocks.mul (Goldilocks.sub Goldilocks.zero cinv4) a)) = a := fun a => by
      have hRing : Goldilocks.add (Goldilocks.mul (Goldilocks.mul (Goldilocks.ofNat 3) cinv4) a)
          (Goldilocks.add (Goldilocks.add (Goldilocks.mul (Goldilocks.mul (Goldilocks.ofNat 3) cinv4) a)
            (Goldilocks.mul (Goldilocks.sub Goldilocks.zero cinv4) a))
            (Goldilocks.mul (Goldilocks.sub Goldilocks.zero cinv4) a)) =
          Goldilocks.mul (Goldilocks.mul (Goldilocks.ofNat 4) cinv4) a := by gold_cring
      rw [hRing, h4inv]
      exact LawfulCommRing.one_mul a
    apply Poseidon2State12.ext
    · exact Lane4.ext (hCoeff1 z.x0) (hCoeff1 z.x1) (hCoeff1 z.x2) (hCoeff1 z.x3)
    · apply Lane4.ext <;> gold_cring
    · apply Lane4.ext <;> gold_cring
  rw [hInvShape]
  unfold stateWeight12
  dsimp only
  rw [laneWeight4_scale_ne_zero hc3nz, laneWeight4_scale_ne_zero hcn1nz,
      show laneWeight4 lane4Zero = 0 from rfl]
  let v := applyM4Inv z
  have hv : v ≠ lane4Zero := fun hvz => by
    apply hz
    have := congrArg applyM4 hvz
    rw [applyM4_applyM4Inv] at this
    exact this.trans (by decide)
  have hm := m4_mds_branch_lower v hv
  have hM4v : applyM4 v = z := applyM4_applyM4Inv z
  rw [hM4v] at hm
  have hvp := laneWeight4_pos_of_ne_zero hv
  change 7 ≤ laneWeight4 v + laneWeight4 v + laneWeight4 v + (laneWeight4 z + 0 + 0)
  omega

private theorem applyME_single_out_branch_ge_seven (x : Poseidon2State12)
    (h1 : activeBlocks12 (applyME x) = 1) :
    7 ≤ stateWeight12 x + stateWeight12 (applyME x) := by
  let y := applyME x
  have hyEq : x = applyMEInv y := (applyMEInv_applyME x).symm
  unfold activeBlocks12 at h1
  change (if y.b0 = lane4Zero then 0 else 1) +
      (if y.b1 = lane4Zero then 0 else 1) +
      (if y.b2 = lane4Zero then 0 else 1) = 1 at h1
  by_cases hy0 : y.b0 = lane4Zero <;>
    by_cases hy1 : y.b1 = lane4Zero <;>
    by_cases hy2 : y.b2 = lane4Zero
  · simp [hy0, hy1, hy2] at h1
  · have hRot : rot12 (rot12 y) = ⟨y.b2, lane4Zero, lane4Zero⟩ :=
      Poseidon2State12.ext rfl hy0 hy1
    have hInvRot : applyMEInv ⟨y.b2, lane4Zero, lane4Zero⟩ = rot12 (rot12 x) := by
      suffices hFwd : applyME (applyMEInv ⟨y.b2, lane4Zero, lane4Zero⟩) = applyME (rot12 (rot12 x)) by
        have h := congrArg applyMEInv hFwd
        rwa [applyMEInv_applyME, applyMEInv_applyME] at h
      rw [applyME_applyMEInv, applyME_rot12, applyME_rot12, ← hRot]
    have hm := applyMEInv_single_b0 y.b2 hy2
    rw [hInvRot, ← hRot, stateWeight12_rot12, stateWeight12_rot12,
        stateWeight12_rot12, stateWeight12_rot12] at hm
    exact hm
  · have hRot : rot12 y = ⟨y.b1, lane4Zero, lane4Zero⟩ :=
      Poseidon2State12.ext rfl hy2 hy0
    have hInvRot : applyMEInv ⟨y.b1, lane4Zero, lane4Zero⟩ = rot12 x := by
      suffices hFwd : applyME (applyMEInv ⟨y.b1, lane4Zero, lane4Zero⟩) = applyME (rot12 x) by
        have h := congrArg applyMEInv hFwd
        rwa [applyMEInv_applyME, applyMEInv_applyME] at h
      rw [applyME_applyMEInv, applyME_rot12, ← hRot]
    have hm := applyMEInv_single_b0 y.b1 hy1
    rw [hInvRot, ← hRot, stateWeight12_rot12, stateWeight12_rot12] at hm
    exact hm
  · simp [hy0, hy1, hy2] at h1
  · have hyShape : y = ⟨y.b0, lane4Zero, lane4Zero⟩ :=
      Poseidon2State12.ext rfl hy1 hy2
    have hm := applyMEInv_single_b0 y.b0 hy0
    rw [← hyShape, ← hyEq] at hm
    exact hm
  · simp [hy0, hy1, hy2] at h1
  · simp [hy0, hy1, hy2] at h1
  · simp [hy0, hy1, hy2] at h1

private theorem applyME_block_diffs (x : Poseidon2State12) :
    lane4Sub (applyME x).b0 (applyME x).b1 = applyM4 (lane4Sub x.b0 x.b1) ∧
    lane4Sub (applyME x).b1 (applyME x).b2 = applyM4 (lane4Sub x.b1 x.b2) ∧
    lane4Sub (applyME x).b2 (applyME x).b0 = applyM4 (lane4Sub x.b2 x.b0) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold applyME applyM4 lane4Add lane4Sub lane4Sum
    apply Lane4.ext <;> gold_cring
  · unfold applyME applyM4 lane4Add lane4Sub lane4Sum
    apply Lane4.ext <;> gold_cring
  · unfold applyME applyM4 lane4Add lane4Sub lane4Sum
    apply Lane4.ext <;> gold_cring

private theorem applyME_multiblock_b1_eq_b2 (x : Poseidon2State12)
    (hEq12 : x.b1 = x.b2)
    (hIn : 2 ≤ activeBlocks12 x)
    (hOut : 2 ≤ activeBlocks12 (applyME x)) :
    8 ≤ stateWeight12 x + stateWeight12 (applyME x) := by
  have hb1nz : x.b1 ≠ lane4Zero := fun hz => by
    unfold activeBlocks12 at hIn
    rw [← hEq12, hz] at hIn
    by_cases hb0 : x.b0 = lane4Zero <;> simp [hb0] at hIn
  have houtEq12 : (applyME x).b1 = (applyME x).b2 := by
    unfold applyME; rw [hEq12]
  have hout1nz : (applyME x).b1 ≠ lane4Zero := fun hz => by
    unfold activeBlocks12 at hOut
    rw [← houtEq12, hz] at hOut
    by_cases hy0 : (applyME x).b0 = lane4Zero <;> simp [hy0] at hOut
  have h2nz : Goldilocks.ofNat 2 ≠ Goldilocks.zero := by decide
  have h3nz : Goldilocks.ofNat 3 ≠ Goldilocks.zero := by decide
  have h4nz : Goldilocks.ofNat 4 ≠ Goldilocks.zero := by decide
  have hout0Eq : (applyME x).b0 =
      lane4Scale (Goldilocks.ofNat 2) (applyM4 (lane4Add x.b0 x.b1)) := by
    unfold applyME
    rw [hEq12]
    dsimp only
    unfold applyM4 lane4Add lane4Scale lane4Sum
    apply Lane4.ext <;> gold_cring
  have h4y1 : lane4Scale (Goldilocks.ofNat 4) (applyM4 x.b1) =
      lane4Sub (lane4Scale (Goldilocks.ofNat 2) (applyME x).b1) (applyME x).b0 := by
    unfold applyME
    rw [hEq12]
    dsimp only
    unfold lane4Add lane4Sub lane4Scale
    apply Lane4.ext <;> gold_cring
  by_cases hb0 : x.b0 = lane4Zero
  · have hout1Scale : (applyME x).b1 = lane4Scale (Goldilocks.ofNat 3) (applyM4 x.b1) := by
      unfold applyME
      rw [hb0, ← hEq12, show applyM4 lane4Zero = lane4Zero from by decide]
      unfold lane4Add lane4Scale lane4Zero
      apply Lane4.ext <;> gold_cring
    have hAdd0 : lane4Add lane4Zero x.b1 = x.b1 := by
      unfold lane4Add lane4Zero
      apply Lane4.ext <;> exact LawfulCommRing.zero_add _
    unfold stateWeight12
    rw [hb0, ← hEq12, ← houtEq12, hout0Eq, hb0, hAdd0, hout1Scale,
        laneWeight4_scale_ne_zero h2nz, laneWeight4_scale_ne_zero h3nz,
        show laneWeight4 lane4Zero = 0 from rfl]
    have hm := m4_mds_branch_lower x.b1 hb1nz
    omega
  · by_cases hy0 : (applyME x).b0 = lane4Zero
    · have hSumZero : lane4Add x.b0 x.b1 = lane4Zero := by
        by_cases hs : lane4Add x.b0 x.b1 = lane4Zero
        · exact hs
        · have hm4nz := applyM4_ne_zero_of_ne_zero hs
          have hwt := laneWeight4_pos_of_ne_zero hm4nz
          rw [← laneWeight4_scale_ne_zero h2nz, ← hout0Eq, hy0] at hwt
          cases hwt
      have hb0Neg : x.b0 = lane4Scale goldilocksNegOne x.b1 := by
        have hSub : x.b0 = lane4Sub (lane4Add x.b0 x.b1) x.b1 := by
          unfold lane4Add lane4Sub
          apply Lane4.ext <;> gold_cring
        rw [hSub, hSumZero]
        unfold lane4Sub lane4Scale lane4Zero
        have hn1 : goldilocksNegOne = CommRingOps.neg CommRingOps.one := by decide
        rw [hn1]
        apply Lane4.ext <;> gold_cring
      have hw0 : laneWeight4 x.b0 = laneWeight4 x.b1 := by
        rw [hb0Neg, laneWeight4_scale_ne_zero (by decide)]
      have hwOut1 : laneWeight4 (applyM4 x.b1) = laneWeight4 (applyME x).b1 := by
        have h := congrArg laneWeight4 h4y1
        rw [hy0, laneWeight4_scale_ne_zero h4nz] at h
        have hSub0 : lane4Sub (lane4Scale (Goldilocks.ofNat 2) (applyME x).b1) lane4Zero =
            lane4Scale (Goldilocks.ofNat 2) (applyME x).b1 := by
          unfold lane4Sub lane4Zero
          apply Lane4.ext <;> exact LawfulCommRing.sub_zero _
        rw [hSub0, laneWeight4_scale_ne_zero h2nz] at h
        exact h
      unfold stateWeight12
      rw [← hEq12, ← houtEq12, hy0, hw0, ← hwOut1, show laneWeight4 lane4Zero = 0 from rfl]
      have hm := m4_mds_branch_lower x.b1 hb1nz
      omega
    · have hSumNz : lane4Add x.b0 x.b1 ≠ lane4Zero := fun hz => by
        rw [hz, show applyM4 lane4Zero = lane4Zero from by decide] at hout0Eq
        have : lane4Scale (Goldilocks.ofNat 2) lane4Zero = lane4Zero := by decide
        exact hy0 (hout0Eq.trans this)
      have hmSum : 5 ≤ laneWeight4 x.b0 + laneWeight4 x.b1 + laneWeight4 (applyME x).b0 := by
        have hm := m4_mds_branch_lower (lane4Add x.b0 x.b1) hSumNz
        have hwOut0 : laneWeight4 (applyME x).b0 = laneWeight4 (applyM4 (lane4Add x.b0 x.b1)) := by
          rw [hout0Eq, laneWeight4_scale_ne_zero h2nz]
        have hTri := laneWeight4_add_le x.b0 x.b1
        omega
      have hmB1 : 5 ≤ laneWeight4 x.b1 + laneWeight4 (applyME x).b0 + laneWeight4 (applyME x).b1 := by
        have hm := m4_mds_branch_lower x.b1 hb1nz
        have hwt4 : laneWeight4 (applyM4 x.b1) ≤
            laneWeight4 (applyME x).b1 + laneWeight4 (applyME x).b0 := by
          have h := congrArg laneWeight4 h4y1
          rw [laneWeight4_scale_ne_zero h4nz] at h
          have hTri := laneWeight4_sub_le (lane4Scale (Goldilocks.ofNat 2) (applyME x).b1) (applyME x).b0
          rw [laneWeight4_scale_ne_zero h2nz] at hTri
          omega
        omega
      have p0 := laneWeight4_pos_of_ne_zero hb0
      have p1 := laneWeight4_pos_of_ne_zero hb1nz
      have po1 := laneWeight4_pos_of_ne_zero hout1nz
      unfold stateWeight12
      rw [← hEq12, ← houtEq12]
      omega

/-- **Multi-Block Width-12 `M_E` Branch Bound (`poseidon2_me12_multiblock_branch_ge_eight`)**:
    Whenever both input `x` and output `applyME x` activate at least two 4-lane blocks,
    `8 ≤ stateWeight12 x + stateWeight12 (applyME x)`. -/
theorem poseidon2_me12_multiblock_branch_ge_eight (x : Poseidon2State12)
    (hIn : 2 ≤ activeBlocks12 x) (hOut : 2 ≤ activeBlocks12 (applyME x)) :
    8 ≤ stateWeight12 x + stateWeight12 (applyME x) := by
  by_cases h01 : x.b0 = x.b1
  · have hRotEq : (rot12 (rot12 x)).b1 = (rot12 (rot12 x)).b2 := h01
    have hIn' : 2 ≤ activeBlocks12 (rot12 (rot12 x)) := by
      rw [activeBlocks12_rot12, activeBlocks12_rot12]; exact hIn
    have hOut' : 2 ≤ activeBlocks12 (applyME (rot12 (rot12 x))) := by
      rw [applyME_rot12, applyME_rot12, activeBlocks12_rot12, activeBlocks12_rot12]; exact hOut
    have hm := applyME_multiblock_b1_eq_b2 (rot12 (rot12 x)) hRotEq hIn' hOut'
    rw [stateWeight12_rot12, stateWeight12_rot12,
        applyME_rot12, applyME_rot12, stateWeight12_rot12, stateWeight12_rot12] at hm
    exact hm
  · by_cases h12 : x.b1 = x.b2
    · exact applyME_multiblock_b1_eq_b2 x h12 hIn hOut
    · by_cases h20 : x.b2 = x.b0
      · have hRotEq : (rot12 x).b1 = (rot12 x).b2 := h20
        have hIn' : 2 ≤ activeBlocks12 (rot12 x) := by
          rw [activeBlocks12_rot12]; exact hIn
        have hOut' : 2 ≤ activeBlocks12 (applyME (rot12 x)) := by
          rw [applyME_rot12, activeBlocks12_rot12]; exact hOut
        have hm := applyME_multiblock_b1_eq_b2 (rot12 x) hRotEq hIn' hOut'
        rw [stateWeight12_rot12, applyME_rot12, stateWeight12_rot12] at hm
        exact hm
      · obtain ⟨hd01, hd12, hd20⟩ := applyME_block_diffs x
        have hn01 : lane4Sub x.b0 x.b1 ≠ lane4Zero := fun hz =>
          h01 ((lane4Sub_eq_zero_iff _ _).mp hz)
        have hn12 : lane4Sub x.b1 x.b2 ≠ lane4Zero := fun hz =>
          h12 ((lane4Sub_eq_zero_iff _ _).mp hz)
        have hn20 : lane4Sub x.b2 x.b0 ≠ lane4Zero := fun hz =>
          h20 ((lane4Sub_eq_zero_iff _ _).mp hz)
        have m01 := m4_mds_branch_lower (lane4Sub x.b0 x.b1) hn01
        have m12 := m4_mds_branch_lower (lane4Sub x.b1 x.b2) hn12
        have m20 := m4_mds_branch_lower (lane4Sub x.b2 x.b0) hn20
        rw [← hd01] at m01
        rw [← hd12] at m12
        rw [← hd20] at m20
        have t1 := laneWeight4_sub_le x.b0 x.b1
        have t2 := laneWeight4_sub_le x.b1 x.b2
        have t3 := laneWeight4_sub_le x.b2 x.b0
        have u1 := laneWeight4_sub_le (applyME x).b0 (applyME x).b1
        have u2 := laneWeight4_sub_le (applyME x).b1 (applyME x).b2
        have u3 := laneWeight4_sub_le (applyME x).b2 (applyME x).b0
        unfold stateWeight12
        omega

def me12BranchSevenWitness : Poseidon2State12 :=
  ⟨⟨Goldilocks.ofNat 3, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩,
   ⟨goldilocksNegOne, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩,
   ⟨goldilocksNegOne, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩⟩

/-- **Exact Universal Width-12 `M_E` Branch Number = 7 (`poseidon2_me12_branch_number_eq_seven`)**:
    Every nonzero 12-lane state satisfies `7 ≤ stateWeight12 x + stateWeight12 (applyME x)`,
    and `me12BranchSevenWitness` attains `3 + 4 = 7`. -/
theorem poseidon2_me12_branch_number_eq_seven :
    (∀ x : Poseidon2State12, x ≠ state12Zero →
      7 ≤ stateWeight12 x + stateWeight12 (applyME x)) ∧
    me12BranchSevenWitness ≠ state12Zero ∧
    stateWeight12 me12BranchSevenWitness + stateWeight12 (applyME me12BranchSevenWitness) = 7 := by
  refine ⟨?_, by decide, by decide⟩
  intro x hx
  have hInPos : 1 ≤ activeBlocks12 x := by
    unfold activeBlocks12
    by_cases h0 : x.b0 = lane4Zero <;>
      by_cases h1 : x.b1 = lane4Zero <;>
      by_cases h2 : x.b2 = lane4Zero
    · exact False.elim (hx (Poseidon2State12.ext h0 h1 h2))
    all_goals simp [h0, h1, h2]
  have hyNz : applyME x ≠ state12Zero := fun hz => by
    apply hx
    have hInv := congrArg applyMEInv hz
    rw [applyMEInv_applyME] at hInv
    exact hInv.trans (by decide)
  have hOutPos : 1 ≤ activeBlocks12 (applyME x) := by
    unfold activeBlocks12
    by_cases h0 : (applyME x).b0 = lane4Zero <;>
      by_cases h1 : (applyME x).b1 = lane4Zero <;>
      by_cases h2 : (applyME x).b2 = lane4Zero
    · exact False.elim (hyNz (Poseidon2State12.ext h0 h1 h2))
    all_goals simp [h0, h1, h2]
  by_cases hIn1 : activeBlocks12 x = 1
  · exact (poseidon2_me12_single_block_branch_ge_seven x hIn1).1
  · by_cases hOut1 : activeBlocks12 (applyME x) = 1
    · exact applyME_single_out_branch_ge_seven x hOut1
    · have h2In : 2 ≤ activeBlocks12 x := by omega
      have h2Out : 2 ≤ activeBlocks12 (applyME x) := by omega
      have h8 := poseidon2_me12_multiblock_branch_ge_eight x h2In h2Out
      omega

/-- Exact bilinear transpose laws for `applyME` and symmetric `applyMI` (`M_I^T = M_I`),
    plus identical universal linear branch bound `≥ 7` for `applyMETranspose`. -/
theorem poseidon2_me12_and_mi12_linear_transpose_laws (x y : Poseidon2State12) :
    state12Dot (applyME x) y = state12Dot x (applyMETranspose y) ∧
    state12Dot (applyMI x) y = state12Dot x (applyMI y) ∧
    (y ≠ state12Zero → 7 ≤ stateWeight12 y + stateWeight12 (applyMETranspose y)) := by
  have hwRev4 : ∀ b : Lane4, laneWeight4 (lane4Rev b) = laneWeight4 b := fun b => by
    unfold laneWeight4 lane4Rev; dsimp only; omega
  have hwRev12 : ∀ s : Poseidon2State12, stateWeight12 (state12Rev4 s) = stateWeight12 s := fun s => by
    unfold stateWeight12 state12Rev4; dsimp only; rw [hwRev4, hwRev4, hwRev4]
  refine ⟨?_, ?_, ?_⟩
  · unfold state12Dot applyMETranspose state12Rev4 lane4Rev applyME applyM4 lane4Add lane4Sum lane4Dot
    gold_cring
  · unfold state12Dot applyMI state12Sum lane4Sum lane4Dot
    gold_cring
  · intro hy
    have hRevNz : state12Rev4 y ≠ state12Zero := fun hz => by
      apply hy
      have hInv : state12Rev4 (state12Rev4 y) = y := by
        rcases y with ⟨⟨_, _, _, _⟩, ⟨_, _, _, _⟩, ⟨_, _, _, _⟩⟩; rfl
      rw [← hInv, hz]; rfl
    have hm := poseidon2_me12_branch_number_eq_seven.1 (state12Rev4 y) hRevNz
    unfold applyMETranspose
    rw [hwRev12]
    rw [hwRev12] at hm
    exact hm

private theorem mi_lane_wt_ge_one (v : Int) (x s : Goldilocks) (hs : s ≠ Goldilocks.zero) :
    1 ≤ (if x = Goldilocks.zero then 0 else 1) +
      (if Goldilocks.add (Goldilocks.mul (goldOfInt v) x) s = Goldilocks.zero then 0 else 1) := by
  by_cases hx : x = Goldilocks.zero
  · subst hx
    have hz : Goldilocks.add (Goldilocks.mul (goldOfInt v) Goldilocks.zero) s = s := by
      change CommRingOps.add (CommRingOps.mul (goldOfInt v) CommRingOps.zero) s = s
      rw [LawfulCommRing.mul_zero, LawfulCommRing.zero_add]
    rw [hz]
    simp [hs]
  · simp [hx]

private theorem mi_lane1_wt_ge_one (x s : Goldilocks) (hs : s ≠ Goldilocks.zero) :
    1 ≤ (if x = Goldilocks.zero then 0 else 1) +
      (if Goldilocks.add x s = Goldilocks.zero then 0 else 1) := by
  by_cases hx : x = Goldilocks.zero
  · subst hx
    have hz : Goldilocks.add Goldilocks.zero s = s := LawfulCommRing.zero_add s
    rw [hz]
    simp [hs]
  · simp [hx]

private theorem mi_lane_scaled_of_wt_le_one (v w : Int) (hvw : v * w = 1024)
    (x s : Goldilocks)
    (h1 : (if x = Goldilocks.zero then 0 else 1) +
      (if Goldilocks.add (Goldilocks.mul (goldOfInt v) x) s = Goldilocks.zero then 0 else 1) ≤ 1) :
    Goldilocks.mul (goldOfInt 1024) x =
      Goldilocks.mul (goldOfInt (if x = Goldilocks.zero then 0 else -w)) s := by
  by_cases hx : x = Goldilocks.zero
  · subst hx
    simp only [↓reduceIte]
    change CommRingOps.mul (goldOfInt 1024) CommRingOps.zero = CommRingOps.mul CommRingOps.zero s
    rw [LawfulCommRing.mul_zero, LawfulCommRing.zero_mul]
  · have hy : Goldilocks.add (Goldilocks.mul (goldOfInt v) x) s = Goldilocks.zero := by
      by_cases hy0 : Goldilocks.add (Goldilocks.mul (goldOfInt v) x) s = Goldilocks.zero
      · exact hy0
      · simp [hx, hy0] at h1
    simp only [hx, ↓reduceIte]
    have hMulW := congrArg (Goldilocks.mul (goldOfInt w)) hy
    rw [show Goldilocks.mul (goldOfInt w) Goldilocks.zero = Goldilocks.zero from
      LawfulCommRing.mul_zero _] at hMulW
    rw [← goldOfInt_nat x, ← goldOfInt_nat s] at hMulW ⊢
    simp only [goldOfInt_add, goldOfInt_mul] at hMulW ⊢
    have hSub : goldOfInt (w * (v * ↑x.val + ↑s.val)) = goldOfInt 0 := hMulW
    have hId : (1024 : Int) * ↑x.val = w * (v * ↑x.val + ↑s.val) + (-w) * ↑s.val := by
      have hvw' : w * v = 1024 := Int.mul_comm w v ▸ hvw
      have hCancel : w * ↑s.val + (-w) * ↑s.val = 0 := by
        rw [← Int.add_mul, Int.add_right_neg, Int.zero_mul]
      calc (1024 : Int) * ↑x.val = (w * v) * ↑x.val := by rw [hvw']
      _ = w * (v * ↑x.val) + 0 := by rw [Int.mul_assoc, Int.add_zero]
      _ = w * (v * ↑x.val) + (w * ↑s.val + (-w) * ↑s.val) := by rw [hCancel]
      _ = w * (v * ↑x.val + ↑s.val) + (-w) * ↑s.val := by rw [← Int.add_assoc, ← Int.mul_add]
    have hGoal : goldOfInt ((1024 : Int) * ↑x.val) =
        Goldilocks.add (goldOfInt (w * (v * ↑x.val + ↑s.val))) (goldOfInt ((-w) * ↑s.val)) := by
      rw [hId]
      exact goldOfInt_add _ _
    rw [hGoal, hSub]
    exact LawfulCommRing.zero_add _

private theorem mi_lane1_scaled_of_wt_le_one (x s : Goldilocks)
    (h1 : (if x = Goldilocks.zero then 0 else 1) +
      (if Goldilocks.add x s = Goldilocks.zero then 0 else 1) ≤ 1) :
    Goldilocks.mul (goldOfInt 1024) x =
      Goldilocks.mul (goldOfInt (if x = Goldilocks.zero then 0 else -1024)) s := by
  have hMul1 : Goldilocks.mul (goldOfInt 1) x = x := by
    change CommRingOps.mul CommRingOps.one x = x
    exact LawfulCommRing.one_mul x
  apply mi_lane_scaled_of_wt_le_one 1 1024 rfl x s
  simpa only [hMul1] using h1

private theorem ite_nonneg_bounds (p : Prop) [Decidable p] (k : Int) (hk : 0 ≤ k) :
    0 ≤ (if p then (0 : Int) else k) ∧ (if p then (0 : Int) else k) ≤ k := by
  by_cases hp : p <;> simp [hp, hk]

private theorem ite_nonpos_bounds (p : Prop) [Decidable p] (k : Int) (hk : k ≤ 0) :
    k ≤ (if p then (0 : Int) else k) ∧ (if p then (0 : Int) else k) ≤ 0 := by
  by_cases hp : p <;> simp [hp, hk]

/-- **Exact Nonzero-Sum `M_I` Branch Number = 13 (`poseidon2_mi12_nonzero_sum_branch_eq_thirteen`)**:
    1. Whenever `state12Sum x ≠ 0`, `13 ≤ stateWeight12 x + stateWeight12 (applyMI x)`
       (proven via `v_0 = -2, v_1..v_11 = 2^(i-1)` forcing `512 ≤ 1024 - Σ_{i ∈ S} (-1024 / v_i) ≤ 3071 < p`).
    2. Every single-lane partial-round difference `⟨⟨Δ, 0, 0, 0⟩, 0, 0⟩` with `Δ ≠ 0` achieves
       full 12-lane diffusion `stateWeight12 (applyMI x) = 12` and attains `1 + 12 = 13`.
    3. Across ALL nonzero `x ≠ state12Zero` (including zero-sum states), `4 ≤ stateWeight12 x + stateWeight12 (applyMI x)`. -/
theorem poseidon2_mi12_nonzero_sum_branch_eq_thirteen :
    (∀ x : Poseidon2State12, state12Sum x ≠ Goldilocks.zero →
      13 ≤ stateWeight12 x + stateWeight12 (applyMI x)) ∧
    (∀ Δ : Goldilocks, Δ ≠ Goldilocks.zero →
      let x : Poseidon2State12 :=
        ⟨⟨Δ, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩, lane4Zero, lane4Zero⟩
      stateWeight12 (applyMI x) = 12 ∧
      stateWeight12 x + stateWeight12 (applyMI x) = 13) ∧
    (∀ x : Poseidon2State12, x ≠ state12Zero →
      4 ≤ stateWeight12 x + stateWeight12 (applyMI x)) := by
  have hBranch13 : ∀ x : Poseidon2State12, state12Sum x ≠ Goldilocks.zero →
      13 ≤ stateWeight12 x + stateWeight12 (applyMI x) := by
    intro x hs
    by_cases h13 : 13 ≤ stateWeight12 x + stateWeight12 (applyMI x)
    · exact h13
    · exfalso
      let s := state12Sum x
      have hMIEq : ∀ (st : Poseidon2State12) (sm : Goldilocks), state12Sum st = sm →
          stateWeight12 (applyMI st) =
            ((if Goldilocks.add (Goldilocks.mul (goldOfInt (-2)) st.b0.x0) sm = Goldilocks.zero then 0 else 1) +
             (if Goldilocks.add st.b0.x1 sm = Goldilocks.zero then 0 else 1) +
             (if Goldilocks.add (Goldilocks.mul (goldOfInt 2) st.b0.x2) sm = Goldilocks.zero then 0 else 1) +
             (if Goldilocks.add (Goldilocks.mul (goldOfInt 4) st.b0.x3) sm = Goldilocks.zero then 0 else 1)) +
            ((if Goldilocks.add (Goldilocks.mul (goldOfInt 8) st.b1.x0) sm = Goldilocks.zero then 0 else 1) +
             (if Goldilocks.add (Goldilocks.mul (goldOfInt 16) st.b1.x1) sm = Goldilocks.zero then 0 else 1) +
             (if Goldilocks.add (Goldilocks.mul (goldOfInt 32) st.b1.x2) sm = Goldilocks.zero then 0 else 1) +
             (if Goldilocks.add (Goldilocks.mul (goldOfInt 64) st.b1.x3) sm = Goldilocks.zero then 0 else 1)) +
            ((if Goldilocks.add (Goldilocks.mul (goldOfInt 128) st.b2.x0) sm = Goldilocks.zero then 0 else 1) +
             (if Goldilocks.add (Goldilocks.mul (goldOfInt 256) st.b2.x1) sm = Goldilocks.zero then 0 else 1) +
             (if Goldilocks.add (Goldilocks.mul (goldOfInt 512) st.b2.x2) sm = Goldilocks.zero then 0 else 1) +
             (if Goldilocks.add (Goldilocks.mul (goldOfInt 1024) st.b2.x3) sm = Goldilocks.zero then 0 else 1)) := by
        intro st sm hsm; subst hsm; rfl
      have hLe12 : stateWeight12 x + stateWeight12 (applyMI x) ≤ 12 := by omega
      rw [hMIEq x s rfl] at hLe12
      unfold stateWeight12 laneWeight4 at hLe12
      dsimp only at hLe12
      have g0 := mi_lane_wt_ge_one (-2) x.b0.x0 s hs
      have g1 := mi_lane1_wt_ge_one x.b0.x1 s hs
      have g2 := mi_lane_wt_ge_one 2 x.b0.x2 s hs
      have g3 := mi_lane_wt_ge_one 4 x.b0.x3 s hs
      have g4 := mi_lane_wt_ge_one 8 x.b1.x0 s hs
      have g5 := mi_lane_wt_ge_one 16 x.b1.x1 s hs
      have g6 := mi_lane_wt_ge_one 32 x.b1.x2 s hs
      have g7 := mi_lane_wt_ge_one 64 x.b1.x3 s hs
      have g8 := mi_lane_wt_ge_one 128 x.b2.x0 s hs
      have g9 := mi_lane_wt_ge_one 256 x.b2.x1 s hs
      have g10 := mi_lane_wt_ge_one 512 x.b2.x2 s hs
      have g11 := mi_lane_wt_ge_one 1024 x.b2.x3 s hs
      have e0 := mi_lane_scaled_of_wt_le_one (-2) (-512) rfl x.b0.x0 s (by omega)
      have e1 := mi_lane1_scaled_of_wt_le_one x.b0.x1 s (by omega)
      have e2 := mi_lane_scaled_of_wt_le_one 2 512 rfl x.b0.x2 s (by omega)
      have e3 := mi_lane_scaled_of_wt_le_one 4 256 rfl x.b0.x3 s (by omega)
      have e4 := mi_lane_scaled_of_wt_le_one 8 128 rfl x.b1.x0 s (by omega)
      have e5 := mi_lane_scaled_of_wt_le_one 16 64 rfl x.b1.x1 s (by omega)
      have e6 := mi_lane_scaled_of_wt_le_one 32 32 rfl x.b1.x2 s (by omega)
      have e7 := mi_lane_scaled_of_wt_le_one 64 16 rfl x.b1.x3 s (by omega)
      have e8 := mi_lane_scaled_of_wt_le_one 128 8 rfl x.b2.x0 s (by omega)
      have e9 := mi_lane_scaled_of_wt_le_one 256 4 rfl x.b2.x1 s (by omega)
      have e10 := mi_lane_scaled_of_wt_le_one 512 2 rfl x.b2.x2 s (by omega)
      have e11 := mi_lane_scaled_of_wt_le_one 1024 1 rfl x.b2.x3 s (by omega)
      let u0 : Int := if x.b0.x0 = Goldilocks.zero then 0 else -(-512)
      let u1 : Int := if x.b0.x1 = Goldilocks.zero then 0 else -1024
      let u2 : Int := if x.b0.x2 = Goldilocks.zero then 0 else -512
      let u3 : Int := if x.b0.x3 = Goldilocks.zero then 0 else -256
      let u4 : Int := if x.b1.x0 = Goldilocks.zero then 0 else -128
      let u5 : Int := if x.b1.x1 = Goldilocks.zero then 0 else -64
      let u6 : Int := if x.b1.x2 = Goldilocks.zero then 0 else -32
      let u7 : Int := if x.b1.x3 = Goldilocks.zero then 0 else -16
      let u8 : Int := if x.b2.x0 = Goldilocks.zero then 0 else -8
      let u9 : Int := if x.b2.x1 = Goldilocks.zero then 0 else -4
      let u10 : Int := if x.b2.x2 = Goldilocks.zero then 0 else -2
      let u11 : Int := if x.b2.x3 = Goldilocks.zero then 0 else -1
      let U : Int := u0 + u1 + u2 + u3 + u4 + u5 + u6 + u7 + u8 + u9 + u10 + u11
      have hSum1024 : Goldilocks.mul (goldOfInt 1024) s = Goldilocks.mul (goldOfInt U) s := by
        have hDist : Goldilocks.mul (goldOfInt 1024) s =
            Goldilocks.add (Goldilocks.add
              (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt 1024) x.b0.x0)
                                              (Goldilocks.mul (goldOfInt 1024) x.b0.x1))
                              (Goldilocks.add (Goldilocks.mul (goldOfInt 1024) x.b0.x2)
                                              (Goldilocks.mul (goldOfInt 1024) x.b0.x3)))
              (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt 1024) x.b1.x0)
                                              (Goldilocks.mul (goldOfInt 1024) x.b1.x1))
                              (Goldilocks.add (Goldilocks.mul (goldOfInt 1024) x.b1.x2)
                                              (Goldilocks.mul (goldOfInt 1024) x.b1.x3))))
              (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt 1024) x.b2.x0)
                                              (Goldilocks.mul (goldOfInt 1024) x.b2.x1))
                              (Goldilocks.add (Goldilocks.mul (goldOfInt 1024) x.b2.x2)
                                              (Goldilocks.mul (goldOfInt 1024) x.b2.x3))) := by
          unfold s state12Sum lane4Sum
          gold_cring
        rw [hDist, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]
        rw [← goldOfInt_nat s]
        simp only [goldOfInt_add, goldOfInt_mul]
        congr 1
        dsimp only [U]
        omega
      have hDiffZero : Goldilocks.mul (goldOfInt (1024 - U)) s = Goldilocks.zero := by
        have hSub := congrArg (fun z => Goldilocks.sub z (Goldilocks.mul (goldOfInt U) s)) hSum1024
        dsimp only at hSub
        rw [show Goldilocks.sub (Goldilocks.mul (goldOfInt U) s) (Goldilocks.mul (goldOfInt U) s) =
            Goldilocks.zero from LawfulCommRing.sub_self _] at hSub
        have hFactor : Goldilocks.sub (Goldilocks.mul (goldOfInt 1024) s)
            (Goldilocks.mul (goldOfInt U) s) = Goldilocks.mul (goldOfInt (1024 - U)) s := by
          rw [← goldOfInt_nat s]
          simp only [goldOfInt_sub, goldOfInt_mul]
          congr 1
          exact (Int.sub_mul 1024 U _).symm
        rwa [hFactor] at hSub
      have b0 := ite_nonneg_bounds (x.b0.x0 = Goldilocks.zero) 512 (by omega)
      have b1 := ite_nonpos_bounds (x.b0.x1 = Goldilocks.zero) (-1024) (by omega)
      have b2 := ite_nonpos_bounds (x.b0.x2 = Goldilocks.zero) (-512) (by omega)
      have b3 := ite_nonpos_bounds (x.b0.x3 = Goldilocks.zero) (-256) (by omega)
      have b4 := ite_nonpos_bounds (x.b1.x0 = Goldilocks.zero) (-128) (by omega)
      have b5 := ite_nonpos_bounds (x.b1.x1 = Goldilocks.zero) (-64) (by omega)
      have b6 := ite_nonpos_bounds (x.b1.x2 = Goldilocks.zero) (-32) (by omega)
      have b7 := ite_nonpos_bounds (x.b1.x3 = Goldilocks.zero) (-16) (by omega)
      have b8 := ite_nonpos_bounds (x.b2.x0 = Goldilocks.zero) (-8) (by omega)
      have b9 := ite_nonpos_bounds (x.b2.x1 = Goldilocks.zero) (-4) (by omega)
      have b10 := ite_nonpos_bounds (x.b2.x2 = Goldilocks.zero) (-2) (by omega)
      have b11 := ite_nonpos_bounds (x.b2.x3 = Goldilocks.zero) (-1) (by omega)
      have hBounds : 512 ≤ 1024 - U ∧ 1024 - U < (goldilocksPrime : Int) := by
        dsimp only [U, u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11]
        simp only [goldilocksPrime]
        omega
      have hCoeffNz : goldOfInt (1024 - U) ≠ Goldilocks.zero := by
        intro hz
        have hv := congrArg (fun g => (g.val : Int)) hz
        rw [goldOfInt_val] at hv
        change (1024 - U) % (goldilocksPrime : Int) = 0 at hv
        rw [Int.emod_eq_of_lt (by omega) hBounds.2] at hv
        omega
      rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hDiffZero with h1 | h2
      · exact hCoeffNz h1
      · exact hs h2
  refine ⟨hBranch13, ?_, ?_⟩
  · intro Δ hΔ
    let x : Poseidon2State12 :=
      ⟨⟨Δ, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩, lane4Zero, lane4Zero⟩
    change stateWeight12 (applyMI x) = 12 ∧ stateWeight12 x + stateWeight12 (applyMI x) = 13
    have hSumEq : state12Sum x = Δ := by
      unfold x state12Sum lane4Sum lane4Zero
      gold_cring
    have hxWt : stateWeight12 x = 1 := by
      unfold x stateWeight12 laneWeight4 lane4Zero
      simp [hΔ]
    have h13 := hBranch13 x (hSumEq.symm ▸ hΔ)
    have hMax : stateWeight12 (applyMI x) ≤ 12 := by
      have l0 := laneWeight4_le_four (applyMI x).b0
      have l1 := laneWeight4_le_four (applyMI x).b1
      have l2 := laneWeight4_le_four (applyMI x).b2
      unfold stateWeight12; omega
    omega
  · intro x hx
    by_cases hs : state12Sum x = Goldilocks.zero
    · have hAdd0 : ∀ a : Goldilocks, Goldilocks.add a Goldilocks.zero = a :=
        LawfulCommRing.add_zero
      have hWtEq : stateWeight12 (applyMI x) = stateWeight12 x := by
        unfold applyMI stateWeight12 laneWeight4
        rw [hs]
        dsimp only
        simp only [hAdd0]
        rw [coord_wt_mul_nz (by decide), coord_wt_mul_nz (by decide), coord_wt_mul_nz (by decide),
            coord_wt_mul_nz (by decide), coord_wt_mul_nz (by decide), coord_wt_mul_nz (by decide),
            coord_wt_mul_nz (by decide), coord_wt_mul_nz (by decide), coord_wt_mul_nz (by decide),
            coord_wt_mul_nz (by decide), coord_wt_mul_nz (by decide)]
      by_cases hw1 : 2 ≤ stateWeight12 x
      · omega
      · exfalso
        have hSingle : ∀ (a b c d : Goldilocks),
            (if a = Goldilocks.zero then 0 else 1) + (if b = Goldilocks.zero then 0 else 1) +
            (if c = Goldilocks.zero then 0 else 1) + (if d = Goldilocks.zero then 0 else 1) ≤ 1 →
            lane4Sum ⟨a, b, c, d⟩ = Goldilocks.zero →
            ⟨a, b, c, d⟩ = lane4Zero := by
          intro a b c d hw hsum
          by_cases ha : a = Goldilocks.zero <;>
            by_cases hb : b = Goldilocks.zero <;>
            by_cases hc : c = Goldilocks.zero <;>
            by_cases hd : d = Goldilocks.zero
          · exact Lane4.ext ha hb hc hd
          · subst ha hb hc; unfold lane4Sum at hsum; dsimp only at hsum
            have : Goldilocks.add (Goldilocks.add Goldilocks.zero Goldilocks.zero)
                (Goldilocks.add Goldilocks.zero d) = d := by gold_cring
            exact False.elim (hd (this ▸ hsum))
          · subst ha hb hd; unfold lane4Sum at hsum; dsimp only at hsum
            have : Goldilocks.add (Goldilocks.add Goldilocks.zero Goldilocks.zero)
                (Goldilocks.add c Goldilocks.zero) = c := by gold_cring
            exact False.elim (hc (this ▸ hsum))
          · simp [ha, hb, hc, hd] at hw
          · subst ha hc hd; unfold lane4Sum at hsum; dsimp only at hsum
            have : Goldilocks.add (Goldilocks.add Goldilocks.zero b)
                (Goldilocks.add Goldilocks.zero Goldilocks.zero) = b := by gold_cring
            exact False.elim (hb (this ▸ hsum))
          · simp [ha, hb, hc, hd] at hw
          · simp [ha, hb, hc, hd] at hw
          · simp [ha, hb, hc, hd] at hw
          · subst hb hc hd; unfold lane4Sum at hsum; dsimp only at hsum
            have : Goldilocks.add (Goldilocks.add a Goldilocks.zero)
                (Goldilocks.add Goldilocks.zero Goldilocks.zero) = a := by gold_cring
            exact False.elim (ha (this ▸ hsum))
          all_goals simp [ha, hb, hc, hd] at hw
        unfold stateWeight12 at hw1
        unfold state12Sum at hs
        by_cases hb0 : x.b0 = lane4Zero <;>
          by_cases hb1 : x.b1 = lane4Zero <;>
          by_cases hb2 : x.b2 = lane4Zero
        · exact hx (Poseidon2State12.ext hb0 hb1 hb2)
        · rw [hb0, hb1] at hw1 hs
          rw [show laneWeight4 lane4Zero = 0 from rfl] at hw1
          rw [show lane4Sum lane4Zero = Goldilocks.zero from rfl] at hs
          have hs' : lane4Sum x.b2 = Goldilocks.zero := by
            have : Goldilocks.add (Goldilocks.add Goldilocks.zero Goldilocks.zero) (lane4Sum x.b2) =
                lane4Sum x.b2 := by gold_cring
            exact this ▸ hs
          exact hb2 (hSingle x.b2.x0 x.b2.x1 x.b2.x2 x.b2.x3 (by unfold laneWeight4 at hw1; omega) hs')
        · rw [hb0, hb2] at hw1 hs
          rw [show laneWeight4 lane4Zero = 0 from rfl] at hw1
          rw [show lane4Sum lane4Zero = Goldilocks.zero from rfl] at hs
          have hs' : lane4Sum x.b1 = Goldilocks.zero := by
            have : Goldilocks.add (Goldilocks.add Goldilocks.zero (lane4Sum x.b1)) Goldilocks.zero =
                lane4Sum x.b1 := by gold_cring
            exact this ▸ hs
          exact hb1 (hSingle x.b1.x0 x.b1.x1 x.b1.x2 x.b1.x3 (by unfold laneWeight4 at hw1; omega) hs')
        · have p1 := laneWeight4_pos_of_ne_zero hb1
          have p2 := laneWeight4_pos_of_ne_zero hb2
          omega
        · rw [hb1, hb2] at hw1 hs
          rw [show laneWeight4 lane4Zero = 0 from rfl] at hw1
          rw [show lane4Sum lane4Zero = Goldilocks.zero from rfl] at hs
          have hs' : lane4Sum x.b0 = Goldilocks.zero := by
            have : Goldilocks.add (Goldilocks.add (lane4Sum x.b0) Goldilocks.zero) Goldilocks.zero =
                lane4Sum x.b0 := by gold_cring
            exact this ▸ hs
          exact hb0 (hSingle x.b0.x0 x.b0.x1 x.b0.x2 x.b0.x3 (by unfold laneWeight4 at hw1; omega) hs')
        · have p0 := laneWeight4_pos_of_ne_zero hb0
          have p2 := laneWeight4_pos_of_ne_zero hb2
          omega
        · have p0 := laneWeight4_pos_of_ne_zero hb0
          have p1 := laneWeight4_pos_of_ne_zero hb1
          omega
        · have p0 := laneWeight4_pos_of_ne_zero hb0
          have p1 := laneWeight4_pos_of_ne_zero hb1
          omega
    · have h13 := hBranch13 x hs
      omega

/-! ### Merz–Rodríguez García (`2026/306`) `(X, -X, 0)` Subspace Round-Skipping & `M_4 ⊗ P_3` + Jive Mitigation -/

theorem sbox7_odd (u : Goldilocks) :
    sbox7 (Goldilocks.sub Goldilocks.zero u) = Goldilocks.sub Goldilocks.zero (sbox7 u) := by
  unfold sbox7
  gold_cring

/-- `#tooth` **Merz–Rodríguez García (`2026/306`) `(X, -X, 0)` Subspace & Partial Feed-Forward Vulnerability**:
    1. On standard `applyME = P_3 ⊗ M_4 = circ(2 M_4, M_4, M_4)`, the entire 4-dimensional subspace
       `⟨X, -X, 0⟩` maps to `⟨M_4 X, -M_4 X, 0⟩`, leaving the sponge capacity block `b2 = 0` untouched!
    2. Across a full round `sboxState12 (state12Add (applyME ⟨U0 + X, -X, U2⟩) C)` under the two linear
       antisymmetry conditions `(applyME ⟨U0, 0, U2⟩).b0 + C.b0 = -((applyME ⟨U0, 0, U2⟩).b1 + C.b1)`,
       oddness of `sbox7` preserves `(X^(1), -X^(1))` in blocks `0, 1` while keeping block `b2` independent of `X`!
    3. Partial feed-forward `(perm st).b0 + st.b0` (`poseidon2_compress12_ff` in `sponge.rs`) and naive
       uniform sum `st.b0 + st.b1 + st.b2` leave `(0, X, -X)` canceled in the feed-forward term. -/
theorem tooth_poseidon2_me_std_admits_x_neg_x_subspace_skip (X U0 U2 : Lane4)
    (C : Poseidon2State12)
    (hAnti : lane4Add (applyME ⟨U0, lane4Zero, U2⟩).b0 C.b0 =
             lane4Neg (lane4Add (applyME ⟨U0, lane4Zero, U2⟩).b1 C.b1)) :
    applyME ⟨X, lane4Neg X, lane4Zero⟩ = ⟨applyM4 X, lane4Neg (applyM4 X), lane4Zero⟩ ∧
    let afterSbox := sboxState12 (state12Add (applyME ⟨lane4Add U0 X, lane4Neg X, U2⟩) C)
    afterSbox.b1 = lane4Neg afterSbox.b0 ∧
    afterSbox.b2 = sboxLane4 (lane4Add (applyME ⟨U0, lane4Zero, U2⟩).b2 C.b2) ∧
    (⟨U0, X, lane4Neg X⟩ : Poseidon2State12).b0 = U0 ∧
    lane4Add (lane4Add U0 X) (lane4Neg X) = U0 := by
  have hLinSub : applyME ⟨X, lane4Neg X, lane4Zero⟩ =
      ⟨applyM4 X, lane4Neg (applyM4 X), lane4Zero⟩ := by
    unfold applyME lane4Neg applyM4 lane4Add lane4Sub lane4Sum lane4Zero
    apply Poseidon2State12.ext <;> apply Lane4.ext <;> gold_cring
  have hDecomp : ⟨lane4Add U0 X, lane4Neg X, U2⟩ =
      state12Add ⟨U0, lane4Zero, U2⟩ ⟨X, lane4Neg X, lane4Zero⟩ := by
    unfold state12Add lane4Add lane4Neg lane4Sub lane4Zero
    apply Poseidon2State12.ext <;> apply Lane4.ext <;> gold_cring
  refine ⟨hLinSub, ?_, ?_, rfl, ?_⟩
  · rw [hDecomp, applyME_add, hLinSub]
    unfold state12Add sboxState12 sboxLane4
    dsimp only
    have hSumAnti : lane4Add (lane4Add (applyME ⟨U0, lane4Zero, U2⟩).b1 (lane4Neg (applyM4 X))) C.b1 =
        lane4Neg (lane4Add (lane4Add (applyME ⟨U0, lane4Zero, U2⟩).b0 (applyM4 X)) C.b0) := by
      have h0 := congrArg Lane4.x0 hAnti
      have h1 := congrArg Lane4.x1 hAnti
      have h2 := congrArg Lane4.x2 hAnti
      have h3 := congrArg Lane4.x3 hAnti
      unfold lane4Add lane4Neg lane4Sub lane4Zero at h0 h1 h2 h3 ⊢
      dsimp only at h0 h1 h2 h3 ⊢
      have hInv : ∀ a : Goldilocks, Goldilocks.sub Goldilocks.zero (Goldilocks.sub Goldilocks.zero a) = a :=
        fun _ => by gold_cring
      apply Lane4.ext
      · have hL : Goldilocks.add (Goldilocks.add (applyME ⟨U0, lane4Zero, U2⟩).b1.x0
            (Goldilocks.sub Goldilocks.zero (applyM4 X).x0)) C.b1.x0 =
          Goldilocks.sub (Goldilocks.add (applyME ⟨U0, lane4Zero, U2⟩).b1.x0 C.b1.x0) (applyM4 X).x0 := by
          gold_cring
        have rhsEq : Goldilocks.sub Goldilocks.zero
            (Goldilocks.add (Goldilocks.add (applyME ⟨U0, lane4Zero, U2⟩).b0.x0 (applyM4 X).x0) C.b0.x0) =
          Goldilocks.sub (Goldilocks.sub Goldilocks.zero
            (Goldilocks.add (applyME ⟨U0, lane4Zero, U2⟩).b0.x0 C.b0.x0)) (applyM4 X).x0 := by
          gold_cring
        have hFlip : Goldilocks.add (applyME ⟨U0, lane4Zero, U2⟩).b1.x0 C.b1.x0 =
            Goldilocks.sub Goldilocks.zero (Goldilocks.add (applyME ⟨U0, lane4Zero, U2⟩).b0.x0 C.b0.x0) := by
          have := congrArg (Goldilocks.sub Goldilocks.zero) h0
          rwa [hInv] at this
        rw [hL, rhsEq, hFlip]
      · have hL : Goldilocks.add (Goldilocks.add (applyME ⟨U0, lane4Zero, U2⟩).b1.x1
            (Goldilocks.sub Goldilocks.zero (applyM4 X).x1)) C.b1.x1 =
          Goldilocks.sub (Goldilocks.add (applyME ⟨U0, lane4Zero, U2⟩).b1.x1 C.b1.x1) (applyM4 X).x1 := by
          gold_cring
        have rhsEq : Goldilocks.sub Goldilocks.zero
            (Goldilocks.add (Goldilocks.add (applyME ⟨U0, lane4Zero, U2⟩).b0.x1 (applyM4 X).x1) C.b0.x1) =
          Goldilocks.sub (Goldilocks.sub Goldilocks.zero
            (Goldilocks.add (applyME ⟨U0, lane4Zero, U2⟩).b0.x1 C.b0.x1)) (applyM4 X).x1 := by
          gold_cring
        have hFlip : Goldilocks.add (applyME ⟨U0, lane4Zero, U2⟩).b1.x1 C.b1.x1 =
            Goldilocks.sub Goldilocks.zero (Goldilocks.add (applyME ⟨U0, lane4Zero, U2⟩).b0.x1 C.b0.x1) := by
          have := congrArg (Goldilocks.sub Goldilocks.zero) h1
          rwa [hInv] at this
        rw [hL, rhsEq, hFlip]
      · have hL : Goldilocks.add (Goldilocks.add (applyME ⟨U0, lane4Zero, U2⟩).b1.x2
            (Goldilocks.sub Goldilocks.zero (applyM4 X).x2)) C.b1.x2 =
          Goldilocks.sub (Goldilocks.add (applyME ⟨U0, lane4Zero, U2⟩).b1.x2 C.b1.x2) (applyM4 X).x2 := by
          gold_cring
        have rhsEq : Goldilocks.sub Goldilocks.zero
            (Goldilocks.add (Goldilocks.add (applyME ⟨U0, lane4Zero, U2⟩).b0.x2 (applyM4 X).x2) C.b0.x2) =
          Goldilocks.sub (Goldilocks.sub Goldilocks.zero
            (Goldilocks.add (applyME ⟨U0, lane4Zero, U2⟩).b0.x2 C.b0.x2)) (applyM4 X).x2 := by
          gold_cring
        have hFlip : Goldilocks.add (applyME ⟨U0, lane4Zero, U2⟩).b1.x2 C.b1.x2 =
            Goldilocks.sub Goldilocks.zero (Goldilocks.add (applyME ⟨U0, lane4Zero, U2⟩).b0.x2 C.b0.x2) := by
          have := congrArg (Goldilocks.sub Goldilocks.zero) h2
          rwa [hInv] at this
        rw [hL, rhsEq, hFlip]
      · have hL : Goldilocks.add (Goldilocks.add (applyME ⟨U0, lane4Zero, U2⟩).b1.x3
            (Goldilocks.sub Goldilocks.zero (applyM4 X).x3)) C.b1.x3 =
          Goldilocks.sub (Goldilocks.add (applyME ⟨U0, lane4Zero, U2⟩).b1.x3 C.b1.x3) (applyM4 X).x3 := by
          gold_cring
        have rhsEq : Goldilocks.sub Goldilocks.zero
            (Goldilocks.add (Goldilocks.add (applyME ⟨U0, lane4Zero, U2⟩).b0.x3 (applyM4 X).x3) C.b0.x3) =
          Goldilocks.sub (Goldilocks.sub Goldilocks.zero
            (Goldilocks.add (applyME ⟨U0, lane4Zero, U2⟩).b0.x3 C.b0.x3)) (applyM4 X).x3 := by
          gold_cring
        have hFlip : Goldilocks.add (applyME ⟨U0, lane4Zero, U2⟩).b1.x3 C.b1.x3 =
            Goldilocks.sub Goldilocks.zero (Goldilocks.add (applyME ⟨U0, lane4Zero, U2⟩).b0.x3 C.b0.x3) := by
          have := congrArg (Goldilocks.sub Goldilocks.zero) h3
          rwa [hInv] at this
        rw [hL, rhsEq, hFlip]
    rw [hSumAnti]
    unfold lane4Neg lane4Sub lane4Zero
    dsimp only
    exact Lane4.ext (sbox7_odd _) (sbox7_odd _) (sbox7_odd _) (sbox7_odd _)
  · rw [hDecomp, applyME_add, hLinSub]
    unfold state12Add sboxState12
    dsimp only
    have hAddZ : ∀ a : Lane4, lane4Add a lane4Zero = a := fun a => by
      unfold lane4Add lane4Zero; apply Lane4.ext <;> exact LawfulCommRing.add_zero _
    rw [hAddZ]
  · unfold lane4Add lane4Neg lane4Sub lane4Zero
    apply Lane4.ext <;> gold_cring

/-- Index transposition `3×4 ↔ 4×3` converting `P_3 ⊗ M_4` (`applyME`) into `M_4 ⊗ P_3` (`2026/306` §6)
    with zero additional multiplications. -/
def transposeIdx4x3 (s : Poseidon2State12) : Poseidon2State12 :=
  ⟨⟨s.b0.x0, s.b0.x3, s.b1.x2, s.b2.x1⟩,
   ⟨s.b0.x1, s.b1.x0, s.b1.x3, s.b2.x2⟩,
   ⟨s.b0.x2, s.b1.x1, s.b2.x0, s.b2.x3⟩⟩

def transposeIdx3x4 (u : Poseidon2State12) : Poseidon2State12 :=
  ⟨⟨u.b0.x0, u.b1.x0, u.b2.x0, u.b0.x1⟩,
   ⟨u.b1.x1, u.b2.x1, u.b0.x2, u.b1.x2⟩,
   ⟨u.b2.x2, u.b0.x3, u.b1.x3, u.b2.x3⟩⟩

def applyMEKroneckerSwap (s : Poseidon2State12) : Poseidon2State12 :=
  transposeIdx3x4 (applyME (transposeIdx4x3 s))

def applyMEKroneckerSwapInv (s : Poseidon2State12) : Poseidon2State12 :=
  transposeIdx3x4 (applyMEInv (transposeIdx4x3 s))

/-- Weighted Jive feed-forward `in0 + 2 · in1 + 4 · tweak` (`M_C · x` from `2026/306` §2). -/
def jiveWeightedFeedForward (s : Poseidon2State12) : Lane4 :=
  lane4Add (lane4Add s.b0 (lane4Scale (Goldilocks.ofNat 2) s.b1))
    (lane4Scale (Goldilocks.ofNat 4) s.b2)

/-- **Zero-Extra-Mul `M_4 ⊗ P_3` & Weighted Jive Mitigation Theorem (`poseidon2_kronecker_swap_kills_subspace_skip`)**:
    1. `applyMEKroneckerSwap` (`M_4 ⊗ P_3`) has two-sided inverse `applyMEKroneckerSwapInv` and
       universal 12-lane branch number `≥ 7`.
    2. Unlike `P_3 ⊗ M_4`, `M_4 ⊗ P_3` maps `(X, -X, 0)` injectively into `b2` (`det = 128 = 2^7`)
       and `(0, X, -X)` injectively into `b0` (`|det| = 112 = 16 · 7`): ONLY `X = 0` avoids activating
       the capacity/output block!
    3. `jiveWeightedFeedForward` is injective in `X` on all three difference subspaces
       `(U0 + X, -X, U2)`, `(U0, U1 + X, -X)`, and `(U0 + X, U1, -X)`. -/
theorem poseidon2_kronecker_swap_kills_subspace_skip :
    (∀ s : Poseidon2State12,
      applyMEKroneckerSwapInv (applyMEKroneckerSwap s) = s ∧
      applyMEKroneckerSwap (applyMEKroneckerSwapInv s) = s) ∧
    (∀ s : Poseidon2State12, s ≠ state12Zero →
      7 ≤ stateWeight12 s + stateWeight12 (applyMEKroneckerSwap s)) ∧
    (∀ X : Lane4,
      (applyMEKroneckerSwap ⟨X, lane4Neg X, lane4Zero⟩).b2 = lane4Zero ↔ X = lane4Zero) ∧
    (∀ X : Lane4,
      (applyMEKroneckerSwap ⟨lane4Zero, X, lane4Neg X⟩).b0 = lane4Zero ↔ X = lane4Zero) ∧
    (∀ U0 U1 U2 X Y : Lane4,
      (jiveWeightedFeedForward ⟨lane4Add U0 X, lane4Neg X, U2⟩ =
       jiveWeightedFeedForward ⟨lane4Add U0 Y, lane4Neg Y, U2⟩ → X = Y) ∧
      (jiveWeightedFeedForward ⟨U0, lane4Add U1 X, lane4Neg X⟩ =
       jiveWeightedFeedForward ⟨U0, lane4Add U1 Y, lane4Neg Y⟩ → X = Y) ∧
      (jiveWeightedFeedForward ⟨lane4Add U0 X, U1, lane4Neg X⟩ =
       jiveWeightedFeedForward ⟨lane4Add U0 Y, U1, lane4Neg Y⟩ → X = Y)) := by
  have hT1 : ∀ s : Poseidon2State12, transposeIdx3x4 (transposeIdx4x3 s) = s := fun s => by
    rcases s with ⟨⟨_, _, _, _⟩, ⟨_, _, _, _⟩, ⟨_, _, _, _⟩⟩; rfl
  have hT2 : ∀ u : Poseidon2State12, transposeIdx4x3 (transposeIdx3x4 u) = u := fun u => by
    rcases u with ⟨⟨_, _, _, _⟩, ⟨_, _, _, _⟩, ⟨_, _, _, _⟩⟩; rfl
  have hw43 : ∀ s : Poseidon2State12, stateWeight12 (transposeIdx4x3 s) = stateWeight12 s := fun s => by
    unfold stateWeight12 transposeIdx4x3 laneWeight4; dsimp only; omega
  have hw34 : ∀ u : Poseidon2State12, stateWeight12 (transposeIdx3x4 u) = stateWeight12 u := fun u => by
    unfold stateWeight12 transposeIdx3x4 laneWeight4; dsimp only; omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s
    unfold applyMEKroneckerSwapInv applyMEKroneckerSwap
    rw [hT2, applyMEInv_applyME, hT1, hT2, applyME_applyMEInv, hT1]
    exact ⟨rfl, rfl⟩
  · intro s hs
    have hNz : transposeIdx4x3 s ≠ state12Zero := fun hz => by
      apply hs; rw [← hT1 s, hz]; rfl
    have hm := poseidon2_me12_branch_number_eq_seven.1 (transposeIdx4x3 s) hNz
    unfold applyMEKroneckerSwap
    rw [hw34]
    rw [hw43] at hm
    exact hm
  · intro X
    constructor
    · intro hb2
      let y := (applyMEKroneckerSwap ⟨X, lane4Neg X, lane4Zero⟩).b2
      have hy0 : y.x0 = Goldilocks.zero := congrArg Lane4.x0 hb2
      have hy1 : y.x1 = Goldilocks.zero := congrArg Lane4.x1 hb2
      have hy2 : y.x2 = Goldilocks.zero := congrArg Lane4.x2 hb2
      have hy3 : y.x3 = Goldilocks.zero := congrArg Lane4.x3 hb2
      have c0 : Goldilocks.mul (goldOfInt 128) X.x0 =
          Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt 32) y.x0) (Goldilocks.mul (goldOfInt 28) y.x1))
            (Goldilocks.add (Goldilocks.mul (goldOfInt (-4)) y.x2) (Goldilocks.mul (goldOfInt (-4)) y.x3)) := by
        unfold y applyMEKroneckerSwap transposeIdx3x4 transposeIdx4x3 applyME applyM4
          lane4Neg lane4Add lane4Sub lane4Sum lane4Zero
        dsimp only
        rw [← goldOfInt_nat X.x0, ← goldOfInt_nat X.x1, ← goldOfInt_nat X.x2, ← goldOfInt_nat X.x3]
        simp only [ofNat_eq_goldOfInt, show Goldilocks.zero = goldOfInt 0 from rfl,
          goldOfInt_add, goldOfInt_sub, goldOfInt_mul]
        congr 1; omega
      have c1 : Goldilocks.mul (goldOfInt 128) X.x1 =
          Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (-24)) y.x0) (Goldilocks.mul (goldOfInt (-1)) y.x1))
            (Goldilocks.add (Goldilocks.mul (goldOfInt 23) y.x2) (Goldilocks.mul (goldOfInt (-9)) y.x3)) := by
        unfold y applyMEKroneckerSwap transposeIdx3x4 transposeIdx4x3 applyME applyM4
          lane4Neg lane4Add lane4Sub lane4Sum lane4Zero
        dsimp only
        rw [← goldOfInt_nat X.x0, ← goldOfInt_nat X.x1, ← goldOfInt_nat X.x2, ← goldOfInt_nat X.x3]
        simp only [ofNat_eq_goldOfInt, show Goldilocks.zero = goldOfInt 0 from rfl,
          goldOfInt_add, goldOfInt_sub, goldOfInt_mul]
        congr 1; omega
      have c2 : Goldilocks.mul (goldOfInt 128) X.x2 =
          Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (-8)) y.x0) (Goldilocks.mul (goldOfInt (-11)) y.x1))
            (Goldilocks.add (Goldilocks.mul (goldOfInt (-3)) y.x2) (Goldilocks.mul (goldOfInt 29) y.x3)) := by
        unfold y applyMEKroneckerSwap transposeIdx3x4 transposeIdx4x3 applyME applyM4
          lane4Neg lane4Add lane4Sub lane4Sum lane4Zero
        dsimp only
        rw [← goldOfInt_nat X.x0, ← goldOfInt_nat X.x1, ← goldOfInt_nat X.x2, ← goldOfInt_nat X.x3]
        simp only [ofNat_eq_goldOfInt, show Goldilocks.zero = goldOfInt 0 from rfl,
          goldOfInt_add, goldOfInt_sub, goldOfInt_mul]
        congr 1; omega
      have c3 : Goldilocks.mul (goldOfInt 128) X.x3 =
          Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (-104)) y.x0) (Goldilocks.mul (goldOfInt 1) y.x1))
            (Goldilocks.add (Goldilocks.mul (goldOfInt (-23)) y.x2) (Goldilocks.mul (goldOfInt 9) y.x3)) := by
        unfold y applyMEKroneckerSwap transposeIdx3x4 transposeIdx4x3 applyME applyM4
          lane4Neg lane4Add lane4Sub lane4Sum lane4Zero
        dsimp only
        rw [← goldOfInt_nat X.x0, ← goldOfInt_nat X.x1, ← goldOfInt_nat X.x2, ← goldOfInt_nat X.x3]
        simp only [ofNat_eq_goldOfInt, show Goldilocks.zero = goldOfInt 0 from rfl,
          goldOfInt_add, goldOfInt_sub, goldOfInt_mul]
        congr 1; omega
      rw [hy0, hy1, hy2, hy3] at c0 c1 c2 c3
      exact Lane4.ext
        (minor_scalar_cancel 128 (by decide) X.x0 (c0.trans (by decide)))
        (minor_scalar_cancel 128 (by decide) X.x1 (c1.trans (by decide)))
        (minor_scalar_cancel 128 (by decide) X.x2 (c2.trans (by decide)))
        (minor_scalar_cancel 128 (by decide) X.x3 (c3.trans (by decide)))
    · intro hX; subst hX; decide
  · intro X
    constructor
    · intro hb0
      let y := (applyMEKroneckerSwap ⟨lane4Zero, X, lane4Neg X⟩).b0
      have hy0 : y.x0 = Goldilocks.zero := congrArg Lane4.x0 hb0
      have hy1 : y.x1 = Goldilocks.zero := congrArg Lane4.x1 hb0
      have hy2 : y.x2 = Goldilocks.zero := congrArg Lane4.x2 hb0
      have hy3 : y.x3 = Goldilocks.zero := congrArg Lane4.x3 hb0
      have c0 : Goldilocks.mul (goldOfInt 112) X.x0 =
          Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt 45) y.x0) (Goldilocks.mul (goldOfInt 5) y.x1))
            (Goldilocks.add (Goldilocks.mul (goldOfInt (-11)) y.x2) (Goldilocks.mul (goldOfInt (-8)) y.x3)) := by
        unfold y applyMEKroneckerSwap transposeIdx3x4 transposeIdx4x3 applyME applyM4
          lane4Neg lane4Add lane4Sub lane4Sum lane4Zero
        dsimp only
        rw [← goldOfInt_nat X.x0, ← goldOfInt_nat X.x1, ← goldOfInt_nat X.x2, ← goldOfInt_nat X.x3]
        simp only [ofNat_eq_goldOfInt, show Goldilocks.zero = goldOfInt 0 from rfl,
          goldOfInt_add, goldOfInt_sub, goldOfInt_mul]
        congr 1; omega
      have c1 : Goldilocks.mul (goldOfInt 112) X.x1 =
          Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (-31)) y.x0) (Goldilocks.mul (goldOfInt 9) y.x1))
            (Goldilocks.add (Goldilocks.mul (goldOfInt 25) y.x2) (Goldilocks.mul (goldOfInt 8) y.x3)) := by
        unfold y applyMEKroneckerSwap transposeIdx3x4 transposeIdx4x3 applyME applyM4
          lane4Neg lane4Add lane4Sub lane4Sum lane4Zero
        dsimp only
        rw [← goldOfInt_nat X.x0, ← goldOfInt_nat X.x1, ← goldOfInt_nat X.x2, ← goldOfInt_nat X.x3]
        simp only [ofNat_eq_goldOfInt, show Goldilocks.zero = goldOfInt 0 from rfl,
          goldOfInt_add, goldOfInt_sub, goldOfInt_mul]
        congr 1; omega
      have c2 : Goldilocks.mul (goldOfInt 112) X.x2 =
          Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt 53) y.x0) (Goldilocks.mul (goldOfInt (-19)) y.x1))
            (Goldilocks.add (Goldilocks.mul (goldOfInt (-3)) y.x2) (Goldilocks.mul (goldOfInt 8) y.x3)) := by
        unfold y applyMEKroneckerSwap transposeIdx3x4 transposeIdx4x3 applyME applyM4
          lane4Neg lane4Add lane4Sub lane4Sum lane4Zero
        dsimp only
        rw [← goldOfInt_nat X.x0, ← goldOfInt_nat X.x1, ← goldOfInt_nat X.x2, ← goldOfInt_nat X.x3]
        simp only [ofNat_eq_goldOfInt, show Goldilocks.zero = goldOfInt 0 from rfl,
          goldOfInt_add, goldOfInt_sub, goldOfInt_mul]
        congr 1; omega
      have c3 : Goldilocks.mul (goldOfInt 112) X.x3 =
          Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (-110)) y.x0) (Goldilocks.mul (goldOfInt 50) y.x1))
            (Goldilocks.add (Goldilocks.mul (goldOfInt 2) y.x2) (Goldilocks.mul (goldOfInt 32) y.x3)) := by
        unfold y applyMEKroneckerSwap transposeIdx3x4 transposeIdx4x3 applyME applyM4
          lane4Neg lane4Add lane4Sub lane4Sum lane4Zero
        dsimp only
        rw [← goldOfInt_nat X.x0, ← goldOfInt_nat X.x1, ← goldOfInt_nat X.x2, ← goldOfInt_nat X.x3]
        simp only [ofNat_eq_goldOfInt, show Goldilocks.zero = goldOfInt 0 from rfl,
          goldOfInt_add, goldOfInt_sub, goldOfInt_mul]
        congr 1; omega
      rw [hy0, hy1, hy2, hy3] at c0 c1 c2 c3
      exact Lane4.ext
        (minor_scalar_cancel 112 (by decide) X.x0 (c0.trans (by decide)))
        (minor_scalar_cancel 112 (by decide) X.x1 (c1.trans (by decide)))
        (minor_scalar_cancel 112 (by decide) X.x2 (c2.trans (by decide)))
        (minor_scalar_cancel 112 (by decide) X.x3 (c3.trans (by decide)))
    · intro hX; subst hX; decide
  · intro U0 U1 U2 X Y
    have cancelScaleNz : ∀ (c : Goldilocks) (hc : c ≠ Goldilocks.zero) (d : Lane4),
        lane4Scale c d = lane4Zero → d = lane4Zero := by
      intro c hc d hSc
      have coordNz : ∀ a : Goldilocks, Goldilocks.mul c a = Goldilocks.zero → a = Goldilocks.zero := by
        intro a hm
        rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hm with h1 | h2
        · exact False.elim (hc h1)
        · exact h2
      exact Lane4.ext
        (coordNz d.x0 (congrArg Lane4.x0 hSc))
        (coordNz d.x1 (congrArg Lane4.x1 hSc))
        (coordNz d.x2 (congrArg Lane4.x2 hSc))
        (coordNz d.x3 (congrArg Lane4.x3 hSc))
    refine ⟨?_, ?_, ?_⟩
    · intro hEq
      have hDiff : lane4Sub Y X =
          lane4Sub (jiveWeightedFeedForward ⟨lane4Add U0 X, lane4Neg X, U2⟩)
                   (jiveWeightedFeedForward ⟨lane4Add U0 Y, lane4Neg Y, U2⟩) := by
        unfold jiveWeightedFeedForward lane4Add lane4Scale lane4Neg lane4Sub lane4Zero
        apply Lane4.ext <;> gold_cring
      rw [hEq, (lane4Sub_eq_zero_iff _ _).mpr rfl] at hDiff
      exact ((lane4Sub_eq_zero_iff Y X).mp hDiff).symm
    · intro hEq
      have hDiff : lane4Scale (Goldilocks.ofNat 2) (lane4Sub Y X) =
          lane4Sub (jiveWeightedFeedForward ⟨U0, lane4Add U1 X, lane4Neg X⟩)
                   (jiveWeightedFeedForward ⟨U0, lane4Add U1 Y, lane4Neg Y⟩) := by
        unfold jiveWeightedFeedForward lane4Add lane4Scale lane4Neg lane4Sub lane4Zero
        apply Lane4.ext <;> gold_cring
      rw [hEq, (lane4Sub_eq_zero_iff _ _).mpr rfl] at hDiff
      exact ((lane4Sub_eq_zero_iff Y X).mp (cancelScaleNz (Goldilocks.ofNat 2) (by decide) _ hDiff)).symm
    · intro hEq
      have hDiff : lane4Scale (Goldilocks.ofNat 3) (lane4Sub Y X) =
          lane4Sub (jiveWeightedFeedForward ⟨lane4Add U0 X, U1, lane4Neg X⟩)
                   (jiveWeightedFeedForward ⟨lane4Add U0 Y, U1, lane4Neg Y⟩) := by
        unfold jiveWeightedFeedForward lane4Add lane4Scale lane4Neg lane4Sub lane4Zero
        apply Lane4.ext <;> gold_cring
      rw [hEq, (lane4Sub_eq_zero_iff _ _).mpr rfl] at hDiff
      exact ((lane4Sub_eq_zero_iff Y X).mp (cancelScaleNz (Goldilocks.ofNat 3) (by decide) _ hDiff)).symm

/-- Explicit rational 12-lane Goldilocks eigenvector of `applyMI` (`V[0] = -2`) for eigenvalue
    `λ₀ = 8914261387277420341`. -/
def miRationalEigvec0 : Poseidon2State12 :=
  ⟨⟨Goldilocks.ofNat 8415733694666260766, Goldilocks.ofNat 10081604446170657914,
    Goldilocks.ofNat 13429757962329074280, Goldilocks.ofNat 7212905167159261059⟩,
   ⟨Goldilocks.ofNat 7177536167446655380, Goldilocks.ofNat 16173559831921257667,
    Goldilocks.ofNat 11410676009809774369, Goldilocks.ofNat 263994636750658321⟩,
   ⟨Goldilocks.ofNat 11338638786567724180, Goldilocks.ofNat 17416777037312523837,
    Goldilocks.ofNat 8867871345638664998, Goldilocks.ofNat 17338153400129577477⟩⟩

/-- `#tooth` **Current `V[0] = -2` Internal Matrix Has Rational 1D Eigenspaces Over Goldilocks**:
    Exhibits an explicit nonzero 12-lane Goldilocks vector `miRationalEigvec0 ≠ 0` satisfying
    `applyMI miRationalEigvec0 = λ₀ · miRationalEigvec0` (`λ₀ = 8914261387277420341`), confirming
    that `diag(-2, 1, 2, ..., 1024) + 1·1ᵀ` has reducible characteristic polynomial over `𝔽_p`. -/
theorem tooth_current_mi_has_rational_eigenvector :
    miRationalEigvec0 ≠ state12Zero ∧
    applyMI miRationalEigvec0 =
      state12Scale (Goldilocks.ofNat 8914261387277420341) miRationalEigvec0 := by decide

/-- Rabin-irreducible single-shift internal diffusion matrix `diag(-64, 1, 2, 4, ..., 1024) + 1·1ᵀ`
    (`0` multiplications; `χ_{M_I^k}` irreducible of degree 12 over Goldilocks for `1 ≤ k ≤ 32`). -/
def applyMIIrred (st : Poseidon2State12) : Poseidon2State12 :=
  let s := state12Sum st
  let b0 := st.b0
  let b1 := st.b1
  let b2 := st.b2
  ⟨⟨Goldilocks.add (Goldilocks.mul (goldOfInt (-64)) b0.x0) s,
    Goldilocks.add b0.x1 s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 2) b0.x2) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 4) b0.x3) s⟩,
   ⟨Goldilocks.add (Goldilocks.mul (goldOfInt 8) b1.x0) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 16) b1.x1) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 32) b1.x2) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 64) b1.x3) s⟩,
   ⟨Goldilocks.add (Goldilocks.mul (goldOfInt 128) b2.x0) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 256) b2.x1) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 512) b2.x2) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 1024) b2.x3) s⟩⟩

private def inv1024IrredG : Goldilocks := Goldilocks.ofNat 18428729670909296641
private def inv3055IrredG : Goldilocks := Goldilocks.ofNat 10802365021336396514

private def weightedSumMIIrred (y : Poseidon2State12) : Goldilocks :=
  let t0 := Goldilocks.add
    (Goldilocks.add (Goldilocks.mul (goldOfInt (-16)) y.b0.x0) (Goldilocks.mul (goldOfInt 1024) y.b0.x1))
    (Goldilocks.add (Goldilocks.mul (goldOfInt 512) y.b0.x2) (Goldilocks.mul (goldOfInt 256) y.b0.x3))
  let t1 := Goldilocks.add
    (Goldilocks.add (Goldilocks.mul (goldOfInt 128) y.b1.x0) (Goldilocks.mul (goldOfInt 64) y.b1.x1))
    (Goldilocks.add (Goldilocks.mul (goldOfInt 32) y.b1.x2) (Goldilocks.mul (goldOfInt 16) y.b1.x3))
  let t2 := Goldilocks.add
    (Goldilocks.add (Goldilocks.mul (goldOfInt 8) y.b2.x0) (Goldilocks.mul (goldOfInt 4) y.b2.x1))
    (Goldilocks.add (Goldilocks.mul (goldOfInt 2) y.b2.x2) y.b2.x3)
  Goldilocks.add (Goldilocks.add t0 t1) t2

private def makeMIIrredInvRaw (y : Poseidon2State12) (s : Goldilocks) : Poseidon2State12 :=
  let scale (w : Int) (yi : Goldilocks) : Goldilocks :=
    Goldilocks.mul inv1024IrredG (Goldilocks.mul (goldOfInt w) (Goldilocks.sub yi s))
  ⟨⟨scale (-16) y.b0.x0, scale 1024 y.b0.x1, scale 512 y.b0.x2, scale 256 y.b0.x3⟩,
   ⟨scale 128 y.b1.x0, scale 64 y.b1.x1, scale 32 y.b1.x2, scale 16 y.b1.x3⟩,
   ⟨scale 8 y.b2.x0, scale 4 y.b2.x1, scale 2 y.b2.x2, scale 1 y.b2.x3⟩⟩

/-- Sherman–Morrison inverse of `applyMIIrred` (`1 + ∑ V_i⁻¹ = 3055 / 1024`). -/
def applyMIIrredInv (y : Poseidon2State12) : Poseidon2State12 :=
  makeMIIrredInvRaw y (Goldilocks.mul inv3055IrredG (weightedSumMIIrred y))

private theorem mul_cancel_irred {u k : Goldilocks} (h : Goldilocks.mul u k = Goldilocks.one)
    (x : Goldilocks) : Goldilocks.mul u (Goldilocks.mul k x) = x := by
  change CommRingOps.mul u (CommRingOps.mul k x) = x
  rw [← LawfulCommRing.mul_assoc]
  change CommRingOps.mul (Goldilocks.mul u k) x = x
  rw [h]
  exact LawfulCommRing.one_mul x

private theorem inv1024Irred_mul_cancel (x : Goldilocks) :
    Goldilocks.mul inv1024IrredG (Goldilocks.mul (Goldilocks.ofNat 1024) x) = x :=
  mul_cancel_irred (by decide) x

private theorem inv3055Irred_mul_cancel (x : Goldilocks) :
    Goldilocks.mul inv3055IrredG (Goldilocks.mul (Goldilocks.ofNat 3055) x) = x :=
  mul_cancel_irred (by decide) x

private theorem mul_inv3055Irred_cancel (x : Goldilocks) :
    Goldilocks.mul (Goldilocks.ofNat 3055) (Goldilocks.mul inv3055IrredG x) = x :=
  mul_cancel_irred (by decide) x

private theorem mi_irred_lane_recover (v w : Int) (hv : v * w = 1024) (x s : Goldilocks) :
    Goldilocks.mul inv1024IrredG (Goldilocks.mul (goldOfInt w)
      (Goldilocks.sub (Goldilocks.add (Goldilocks.mul (goldOfInt v) x) s) s)) = x := by
  have hProd : Goldilocks.mul (goldOfInt w)
      (Goldilocks.sub (Goldilocks.add (Goldilocks.mul (goldOfInt v) x) s) s) =
      Goldilocks.mul (Goldilocks.ofNat 1024) x := by
    rw [← goldOfInt_nat x, ← goldOfInt_nat s, ofNat_eq_goldOfInt]
    simp only [goldOfInt_add, goldOfInt_sub, goldOfInt_mul]
    congr 1
    have hEq : w * (v * (x.val : Int) + (s.val : Int) - (s.val : Int)) = (v * w) * (x.val : Int) := by
      rw [Int.add_sub_cancel, ← Int.mul_assoc, Int.mul_comm w v]
    rw [hEq, hv]
    omega
  rw [hProd, inv1024Irred_mul_cancel x]

private theorem mi_irred_lane_forward (v w : Int) (hv : v * w = 1024) (yi s : Goldilocks) :
    Goldilocks.add (Goldilocks.mul (goldOfInt v)
      (Goldilocks.mul inv1024IrredG (Goldilocks.mul (goldOfInt w) (Goldilocks.sub yi s)))) s = yi := by
  have hAssoc : Goldilocks.mul (goldOfInt v)
      (Goldilocks.mul inv1024IrredG (Goldilocks.mul (goldOfInt w) (Goldilocks.sub yi s))) =
      Goldilocks.mul inv1024IrredG (Goldilocks.mul (Goldilocks.ofNat 1024) (Goldilocks.sub yi s)) := by
    rw [← goldOfInt_nat inv1024IrredG, ← goldOfInt_nat yi, ← goldOfInt_nat s, ofNat_eq_goldOfInt]
    simp only [goldOfInt_sub, goldOfInt_mul]
    congr 1
    have hEq : v * ((inv1024IrredG.val : Int) * (w * ((yi.val : Int) - (s.val : Int)))) =
        (inv1024IrredG.val : Int) * ((v * w) * ((yi.val : Int) - (s.val : Int))) := by
      rw [← Int.mul_assoc, ← Int.mul_assoc, Int.mul_comm v (inv1024IrredG.val : Int),
          Int.mul_assoc (inv1024IrredG.val : Int) v w, Int.mul_assoc]
    rw [hEq, hv]
    rfl
  rw [hAssoc, inv1024Irred_mul_cancel (Goldilocks.sub yi s)]
  change CommRingOps.add (CommRingOps.sub yi s) s = yi
  rw [LawfulCommRing.add_comm, LawfulCommRing.add_sub_cancel_left]

/-- **Two-Sided Sherman–Morrison Invertibility of Rabin-Irreducible `applyMIIrred` (`V[0] = -64`)**. -/
theorem poseidon2_mi_irred_two_sided_inverse (st : Poseidon2State12) :
    applyMIIrredInv (applyMIIrred st) = st ∧ applyMIIrred (applyMIIrredInv st) = st := by
  constructor
  · have hWS : weightedSumMIIrred (applyMIIrred st) =
        Goldilocks.mul (Goldilocks.ofNat 3055) (state12Sum st) := by
      unfold weightedSumMIIrred applyMIIrred state12Sum lane4Sum
      dsimp only
      rw [← goldOfInt_nat st.b0.x0, ← goldOfInt_nat st.b0.x1, ← goldOfInt_nat st.b0.x2, ← goldOfInt_nat st.b0.x3,
          ← goldOfInt_nat st.b1.x0, ← goldOfInt_nat st.b1.x1, ← goldOfInt_nat st.b1.x2, ← goldOfInt_nat st.b1.x3,
          ← goldOfInt_nat st.b2.x0, ← goldOfInt_nat st.b2.x1, ← goldOfInt_nat st.b2.x2, ← goldOfInt_nat st.b2.x3]
      simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
      congr 1; omega
    unfold applyMIIrredInv
    rw [hWS, inv3055Irred_mul_cancel (state12Sum st)]
    unfold makeMIIrredInvRaw applyMIIrred
    dsimp only
    have h1 : Goldilocks.add st.b0.x1 (state12Sum st) =
        Goldilocks.add (Goldilocks.mul (goldOfInt 1) st.b0.x1) (state12Sum st) := by
      have hone : goldOfInt 1 = CommRingOps.one := rfl
      change _ = Goldilocks.add (CommRingOps.mul (goldOfInt 1) st.b0.x1) _
      rw [hone, LawfulCommRing.one_mul]
    apply Poseidon2State12.ext
    · apply Lane4.ext
      · exact mi_irred_lane_recover (-64) (-16) rfl st.b0.x0 (state12Sum st)
      · rw [h1]; exact mi_irred_lane_recover 1 1024 rfl st.b0.x1 (state12Sum st)
      · exact mi_irred_lane_recover 2 512 rfl st.b0.x2 (state12Sum st)
      · exact mi_irred_lane_recover 4 256 rfl st.b0.x3 (state12Sum st)
    · apply Lane4.ext
      · exact mi_irred_lane_recover 8 128 rfl st.b1.x0 (state12Sum st)
      · exact mi_irred_lane_recover 16 64 rfl st.b1.x1 (state12Sum st)
      · exact mi_irred_lane_recover 32 32 rfl st.b1.x2 (state12Sum st)
      · exact mi_irred_lane_recover 64 16 rfl st.b1.x3 (state12Sum st)
    · apply Lane4.ext
      · exact mi_irred_lane_recover 128 8 rfl st.b2.x0 (state12Sum st)
      · exact mi_irred_lane_recover 256 4 rfl st.b2.x1 (state12Sum st)
      · exact mi_irred_lane_recover 512 2 rfl st.b2.x2 (state12Sum st)
      · exact mi_irred_lane_recover 1024 1 rfl st.b2.x3 (state12Sum st)
  · let s := Goldilocks.mul inv3055IrredG (weightedSumMIIrred st)
    have hSumRaw : state12Sum (makeMIIrredInvRaw st s) =
        Goldilocks.mul inv1024IrredG (Goldilocks.sub (weightedSumMIIrred st)
          (Goldilocks.mul (goldOfInt 2031) s)) := by
      unfold state12Sum makeMIIrredInvRaw lane4Sum weightedSumMIIrred
      dsimp only
      rw [← goldOfInt_nat inv1024IrredG, ← goldOfInt_nat s,
          ← goldOfInt_nat st.b0.x0, ← goldOfInt_nat st.b0.x1, ← goldOfInt_nat st.b0.x2, ← goldOfInt_nat st.b0.x3,
          ← goldOfInt_nat st.b1.x0, ← goldOfInt_nat st.b1.x1, ← goldOfInt_nat st.b1.x2, ← goldOfInt_nat st.b1.x3,
          ← goldOfInt_nat st.b2.x0, ← goldOfInt_nat st.b2.x1, ← goldOfInt_nat st.b2.x2, ← goldOfInt_nat st.b2.x3]
      simp only [goldOfInt_add, goldOfInt_sub, goldOfInt_mul, ← Int.mul_add]
      congr 1; congr 1; omega
    have h3055Sub : Goldilocks.sub (Goldilocks.mul (Goldilocks.ofNat 3055) s)
        (Goldilocks.mul (goldOfInt 2031) s) = Goldilocks.mul (Goldilocks.ofNat 1024) s := by
      rw [← goldOfInt_nat s, ofNat_eq_goldOfInt, ofNat_eq_goldOfInt]
      simp only [goldOfInt_sub, goldOfInt_mul]
      congr 1; omega
    have hSum : state12Sum (makeMIIrredInvRaw st s) = s := by
      rw [hSumRaw]
      have hws : weightedSumMIIrred st = Goldilocks.mul (Goldilocks.ofNat 3055) s :=
        (mul_inv3055Irred_cancel (weightedSumMIIrred st)).symm
      rw [hws, h3055Sub, inv1024Irred_mul_cancel s]
    unfold applyMIIrredInv
    change applyMIIrred (makeMIIrredInvRaw st s) = st
    unfold applyMIIrred
    rw [hSum]
    unfold makeMIIrredInvRaw
    dsimp only
    have h1 : ∀ a : Goldilocks, a = Goldilocks.mul (goldOfInt 1) a := fun a => by
      rw [← goldOfInt_nat a, goldOfInt_mul, Int.one_mul]
    apply Poseidon2State12.ext
    · apply Lane4.ext
      · exact mi_irred_lane_forward (-64) (-16) rfl st.b0.x0 s
      · rw [h1 (Goldilocks.mul inv1024IrredG (Goldilocks.mul (goldOfInt 1024) (Goldilocks.sub st.b0.x1 s)))]
        exact mi_irred_lane_forward 1 1024 rfl st.b0.x1 s
      · exact mi_irred_lane_forward 2 512 rfl st.b0.x2 s
      · exact mi_irred_lane_forward 4 256 rfl st.b0.x3 s
    · apply Lane4.ext
      · exact mi_irred_lane_forward 8 128 rfl st.b1.x0 s
      · exact mi_irred_lane_forward 16 64 rfl st.b1.x1 s
      · exact mi_irred_lane_forward 32 32 rfl st.b1.x2 s
      · exact mi_irred_lane_forward 64 16 rfl st.b1.x3 s
    · apply Lane4.ext
      · exact mi_irred_lane_forward 128 8 rfl st.b2.x0 s
      · exact mi_irred_lane_forward 256 4 rfl st.b2.x1 s
      · exact mi_irred_lane_forward 512 2 rfl st.b2.x2 s
      · exact mi_irred_lane_forward 1024 1 rfl st.b2.x3 s

/-! ## 9. `sbox7` Differential Uniformity `≤ 6` & Width-12 `(R_F = 8, R_P = 22)` Wide-Trail Bounds -/

/-- Degree-6 polynomial `(X + Δ)^7 - X^7 - δ` (`length = 7 = 6 + 1`) over `Goldilocks`. -/
def sbox7DiffPoly (Δ δ : Goldilocks) : List Goldilocks :=
  let Δ2 := Goldilocks.mul Δ Δ
  let Δ3 := Goldilocks.mul Δ2 Δ
  let Δ4 := Goldilocks.mul Δ2 Δ2
  let Δ5 := Goldilocks.mul Δ4 Δ
  let Δ6 := Goldilocks.mul Δ3 Δ3
  let Δ7 := Goldilocks.mul Δ3 Δ4
  [Goldilocks.sub Δ7 δ,
   Goldilocks.mul (CRing.natCast 7) Δ6,
   Goldilocks.mul (CRing.natCast 21) Δ5,
   Goldilocks.mul (CRing.natCast 35) Δ4,
   Goldilocks.mul (CRing.natCast 35) Δ3,
   Goldilocks.mul (CRing.natCast 21) Δ2,
   Goldilocks.mul (CRing.natCast 7) Δ]

theorem evalCoeffs_sbox7DiffPoly (Δ δ x : Goldilocks) :
    RoundPoly.evalCoeffs (sbox7DiffPoly Δ δ) x =
      Goldilocks.sub (Goldilocks.sub (sbox7 (Goldilocks.add x Δ)) (sbox7 x)) δ := by
  simp only [sbox7DiffPoly, RoundPoly.evalCoeffs_cons, RoundPoly.evalCoeffs_nil, sbox7]
  gold_cring

/-- **Exact `sbox7` Differential Uniformity Bound (`sbox7_differential_uniformity_le_six`)**:
    For every nonzero input difference `Δ ≠ 0`, output difference `δ`, and duplicate-free set
    `S : List Goldilocks`, the equation `sbox7 (x + Δ) - sbox7 x = δ` has at most `6` solutions in `S`. -/
theorem sbox7_differential_uniformity_le_six (Δ δ : Goldilocks) (hΔ : Δ ≠ Goldilocks.zero)
    (S : List Goldilocks) (hNodup : S.Nodup) :
    (S.filter (fun x =>
      decide (Goldilocks.sub (sbox7 (Goldilocks.add x Δ)) (sbox7 x) = δ))).length ≤ 6 := by
  let p := sbox7DiffPoly Δ δ
  have hLen : p.length ≤ 6 + 1 := Nat.le_refl 7
  let c5040 : Goldilocks :=
    Goldilocks.mul (CRing.natCast 7)
      (Goldilocks.mul (CRing.natCast 8) (Goldilocks.mul (CRing.natCast 9) (CRing.natCast 10)))
  have h6Diff : ∀ (Δ' δ' : Goldilocks),
      let f := RoundPoly.evalCoeffs (sbox7DiffPoly Δ' δ')
      Goldilocks.add
        (Goldilocks.sub
          (Goldilocks.add
            (Goldilocks.sub
              (Goldilocks.add
                (Goldilocks.sub (f (CRing.natCast 6))
                  (Goldilocks.mul (CRing.natCast 6) (f (CRing.natCast 5))))
                (Goldilocks.mul (CRing.natCast 15) (f (CRing.natCast 4))))
              (Goldilocks.mul (CRing.natCast 20) (f (CRing.natCast 3))))
            (Goldilocks.mul (CRing.natCast 15) (f (CRing.natCast 2))))
          (Goldilocks.mul (CRing.natCast 6) (f (CRing.natCast 1))))
        (f (CRing.natCast 0)) =
      Goldilocks.mul c5040 Δ' := by
    intro Δ' δ'
    dsimp only [c5040]
    simp only [sbox7DiffPoly, RoundPoly.evalCoeffs_cons, RoundPoly.evalCoeffs_nil]
    gold_cring
  have h5040Nz : Goldilocks.mul c5040 Δ ≠ Goldilocks.zero := fun hz => by
    have hc : c5040 ≠ Goldilocks.zero := fun h => absurd (congrArg Goldilocks.val h) (by decide)
    rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hz with h1 | h2
    · exact hc h1
    · exact hΔ h2
  have hExistsNz : ∃ x₀ : Goldilocks, RoundPoly.evalCoeffs p x₀ ≠ CommRingOps.zero := by
    by_cases z0 : RoundPoly.evalCoeffs p (CRing.natCast 0) = Goldilocks.zero
    · by_cases z1 : RoundPoly.evalCoeffs p (CRing.natCast 1) = Goldilocks.zero
      · by_cases z2 : RoundPoly.evalCoeffs p (CRing.natCast 2) = Goldilocks.zero
        · by_cases z3 : RoundPoly.evalCoeffs p (CRing.natCast 3) = Goldilocks.zero
          · by_cases z4 : RoundPoly.evalCoeffs p (CRing.natCast 4) = Goldilocks.zero
            · by_cases z5 : RoundPoly.evalCoeffs p (CRing.natCast 5) = Goldilocks.zero
              · by_cases z6 : RoundPoly.evalCoeffs p (CRing.natCast 6) = Goldilocks.zero
                · exfalso
                  have hId := h6Diff Δ δ
                  dsimp only at hId
                  change _ = _ at hId
                  rw [z0, z1, z2, z3, z4, z5, z6] at hId
                  have hLHS : Goldilocks.add
                      (Goldilocks.sub
                        (Goldilocks.add
                          (Goldilocks.sub
                            (Goldilocks.add
                              (Goldilocks.sub Goldilocks.zero
                                (Goldilocks.mul (CRing.natCast 6) Goldilocks.zero))
                              (Goldilocks.mul (CRing.natCast 15) Goldilocks.zero))
                            (Goldilocks.mul (CRing.natCast 20) Goldilocks.zero))
                          (Goldilocks.mul (CRing.natCast 15) Goldilocks.zero))
                        (Goldilocks.mul (CRing.natCast 6) Goldilocks.zero))
                      Goldilocks.zero = Goldilocks.zero := by gold_cring
                  exact h5040Nz (hId.symm.trans hLHS)
                · exact ⟨CRing.natCast 6, z6⟩
              · exact ⟨CRing.natCast 5, z5⟩
            · exact ⟨CRing.natCast 4, z4⟩
          · exact ⟨CRing.natCast 3, z3⟩
        · exact ⟨CRing.natCast 2, z2⟩
      · exact ⟨CRing.natCast 1, z1⟩
    · exact ⟨CRing.natCast 0, z0⟩
  have hRoots := RoundPoly.roots_nodup_length_le 6 p S hNodup hLen hExistsNz
  have hFiltEq : S.filter (fun x =>
      decide (Goldilocks.sub (sbox7 (Goldilocks.add x Δ)) (sbox7 x) = δ)) =
      S.filter (fun x => decide (RoundPoly.evalCoeffs p x = CommRingOps.zero)) := by
    congr 1
    funext x
    dsimp only [p]
    rw [evalCoeffs_sbox7DiffPoly]
    change decide (Goldilocks.sub (sbox7 (Goldilocks.add x Δ)) (sbox7 x) = δ) =
      decide (Goldilocks.sub (Goldilocks.sub (sbox7 (Goldilocks.add x Δ)) (sbox7 x)) δ = Goldilocks.zero)
    simp only [gold_sub_zero_iff]
  rwa [hFiltEq]

private theorem state12Sub_eq_zero_iff (a b : Poseidon2State12) :
    state12Sub a b = state12Zero ↔ a = b := by
  constructor
  · intro h
    exact Poseidon2State12.ext
      ((lane4Sub_eq_zero_iff _ _).mp (congrArg Poseidon2State12.b0 h))
      ((lane4Sub_eq_zero_iff _ _).mp (congrArg Poseidon2State12.b1 h))
      ((lane4Sub_eq_zero_iff _ _).mp (congrArg Poseidon2State12.b2 h))
  · intro h; subst h
    exact Poseidon2State12.ext
      ((lane4Sub_eq_zero_iff _ _).mpr rfl)
      ((lane4Sub_eq_zero_iff _ _).mpr rfl)
      ((lane4Sub_eq_zero_iff _ _).mpr rfl)

private theorem applyME_sub (a b : Poseidon2State12) :
    state12Sub (applyME a) (applyME b) = applyME (state12Sub a b) := by
  unfold applyME applyM4 state12Sub lane4Add lane4Sub lane4Sum
  apply Poseidon2State12.ext <;> apply Lane4.ext <;> gold_cring

theorem sboxState12_preserves_differential_activity (a b rc : Poseidon2State12) :
    stateWeight12 (state12Sub (sboxState12 (state12Add a rc)) (sboxState12 (state12Add b rc))) =
      stateWeight12 (state12Sub a b) := by
  unfold stateWeight12 state12Sub sboxState12 state12Add
  dsimp only
  rw [sbox7_preserves_differential_activity,
      sbox7_preserves_differential_activity,
      sbox7_preserves_differential_activity]

/-- Two successive width-12 external rounds activate at least `7` S-boxes on any `a ≠ b`. -/
theorem poseidon2_width12_two_ext_rounds_active_ge_seven
    (a b rc : Poseidon2State12) (hne : a ≠ b) :
    7 ≤ stateWeight12 (state12Sub a b) +
      stateWeight12 (state12Sub (externalRound rc a) (externalRound rc b)) := by
  let d := state12Sub (sboxState12 (state12Add a rc)) (sboxState12 (state12Add b rc))
  have hdNz : d ≠ state12Zero := fun hz => by
    have hw0 : stateWeight12 d = 0 := by rw [hz]; rfl
    rw [sboxState12_preserves_differential_activity] at hw0
    have hdab : state12Sub a b ≠ state12Zero := fun hz' =>
      hne ((state12Sub_eq_zero_iff _ _).mp hz')
    unfold stateWeight12 at hw0
    by_cases h0 : (state12Sub a b).b0 = lane4Zero <;>
      by_cases h1 : (state12Sub a b).b1 = lane4Zero <;>
      by_cases h2 : (state12Sub a b).b2 = lane4Zero
    · exact hdab (Poseidon2State12.ext h0 h1 h2)
    · have := laneWeight4_pos_of_ne_zero h2; omega
    · have := laneWeight4_pos_of_ne_zero h1; omega
    · have := laneWeight4_pos_of_ne_zero h1; omega
    · have := laneWeight4_pos_of_ne_zero h0; omega
    · have := laneWeight4_pos_of_ne_zero h0; omega
    · have := laneWeight4_pos_of_ne_zero h0; omega
    · have := laneWeight4_pos_of_ne_zero h0; omega
  have hm := poseidon2_me12_branch_number_eq_seven.1 d hdNz
  rw [sboxState12_preserves_differential_activity] at hm
  unfold externalRound
  rwa [applyME_sub]

def countExtRoundsActive : List Poseidon2State12 → Poseidon2State12 → Poseidon2State12 → Nat
  | [], _, _ => 0
  | rc :: rcs, a, b =>
    stateWeight12 (state12Sub a b) +
      countExtRoundsActive rcs (externalRound rc a) (externalRound rc b)

def countIntRoundsActive : List Goldilocks → Poseidon2State12 → Poseidon2State12 → Nat
  | [], _, _ => 0
  | rc :: rcs, a, b =>
    (if a.b0.x0 = b.b0.x0 then 0 else 1) +
      countIntRoundsActive rcs (internalRound rc a) (internalRound rc b)

/-- Exact count of active degree-7 S-boxes across all `8` external + `22` internal rounds (`118` total S-boxes)
    of the deployed width-12 `poseidon2Perm12` trajectory on `(a, b)`. -/
def poseidon2Perm12ActiveSboxes (a b : Poseidon2State12) : Nat :=
  let s0a := applyME a
  let s0b := applyME b
  let s1a := runRounds externalRound poseidon2InitialExtConsts s0a
  let s1b := runRounds externalRound poseidon2InitialExtConsts s0b
  let s2a := runRounds internalRound poseidon2InternalConsts s1a
  let s2b := runRounds internalRound poseidon2InternalConsts s1b
  countExtRoundsActive poseidon2InitialExtConsts s0a s0b +
    countIntRoundsActive poseidon2InternalConsts s1a s1b +
    countExtRoundsActive poseidon2TerminalExtConsts s2a s2b

private theorem externalRound_ne_of_ne (rc a b : Poseidon2State12) (hne : a ≠ b) :
    externalRound rc a ≠ externalRound rc b := fun hEq => by
  apply hne
  have hInv := congrArg (externalRoundInv rc) hEq
  rwa [(poseidon2_full_round_two_sided_inverse rc a).1,
       (poseidon2_full_round_two_sided_inverse rc b).1] at hInv

private theorem runRounds_int_ne_of_ne :
    ∀ (rcs : List Goldilocks) (a b : Poseidon2State12),
      a ≠ b → runRounds internalRound rcs a ≠ runRounds internalRound rcs b
  | [], a, b, hne => hne
  | rc :: rcs, a, b, hne => by
    apply runRounds_int_ne_of_ne rcs
    intro hEq
    apply hne
    have hInv := congrArg (internalRoundInv rc) hEq
    rwa [(poseidon2_partial_round_two_sided_inverse rc a).1,
         (poseidon2_partial_round_two_sided_inverse rc b).1] at hInv

private theorem countExtRoundsActive_four (c0 c1 c2 c3 a b : Poseidon2State12) (hne : a ≠ b) :
    14 ≤ countExtRoundsActive [c0, c1, c2, c3] a b := by
  let a1 := externalRound c0 a
  let b1 := externalRound c0 b
  let a2 := externalRound c1 a1
  let b2 := externalRound c1 b1
  have hne2 : a2 ≠ b2 := externalRound_ne_of_ne c1 a1 b1 (externalRound_ne_of_ne c0 a b hne)
  have w01 := poseidon2_width12_two_ext_rounds_active_ge_seven a b c0 hne
  have w23 := poseidon2_width12_two_ext_rounds_active_ge_seven a2 b2 c2 hne2
  dsimp only [a1, b1, a2, b2] at w23
  simp only [countExtRoundsActive]
  omega

private theorem pow_lt_pow_of_lt_base (u v k : Nat) (hu : 1 ≤ u) (huv : u < v) (hk : 1 ≤ k) :
    u ^ k < v ^ k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  induction m with
  | zero => simpa using huv
  | succ m ih =>
    have ih' := ih (by omega)
    rw [Nat.pow_succ, Nat.pow_succ]
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right ih' (by omega))
      (Nat.mul_le_mul_left _ (Nat.le_of_lt huv))

/-- **Width-12 `(R_F = 8, R_P = 22)` Wide-Trail Active S-Box & Characteristic Probability Theorem**:
    1. Every distinct input pair `a ≠ b` activates `≥ 28` S-boxes across `poseidon2Perm12`
       (`≥ 14` in the 4 initial full rounds + `≥ 14` in the 4 terminal full rounds).
    2. Because `sbox7` has differential uniformity `≤ 6` and degree-7 squared linear correlation
       weight `≤ (7 - 1)^2 = 36`, any trail with `28 ≤ active` S-boxes satisfies both
       `(6 / p)^active < 2^(-1680) < 2^(-256)` and `(36 / p)^active < 2^(-1596) < 2^(-256)`. -/
theorem poseidon2_width12_wide_trail_and_characteristic_bounds :
    (∀ a b : Poseidon2State12, a ≠ b → 28 ≤ poseidon2Perm12ActiveSboxes a b) ∧
    (∀ active : Nat, 28 ≤ active →
      6 ^ active * 2 ^ 256 < goldilocksPrime ^ active ∧
      36 ^ active * 2 ^ 256 < goldilocksPrime ^ active ∧
      6 ^ active * 2 ^ 1680 < goldilocksPrime ^ active) := by
  refine ⟨?_, ?_⟩
  · intro a b hne
    have hs0 : applyME a ≠ applyME b := fun hEq => by
      apply hne
      have hInv := congrArg applyMEInv hEq
      rwa [applyMEInv_applyME, applyMEInv_applyME] at hInv
    have hInitConsts : poseidon2InitialExtConsts =
        [poseidon2ExtRoundConst 0 0, poseidon2ExtRoundConst 0 1,
         poseidon2ExtRoundConst 0 2, poseidon2ExtRoundConst 0 3] := rfl
    have hTermConsts : poseidon2TerminalExtConsts =
        [poseidon2ExtRoundConst 2 0, poseidon2ExtRoundConst 2 1,
         poseidon2ExtRoundConst 2 2, poseidon2ExtRoundConst 2 3] := rfl
    have hInit14 : 14 ≤ countExtRoundsActive poseidon2InitialExtConsts (applyME a) (applyME b) := by
      rw [hInitConsts]
      exact countExtRoundsActive_four _ _ _ _ _ _ hs0
    have hs1 : runRounds externalRound poseidon2InitialExtConsts (applyME a) ≠
        runRounds externalRound poseidon2InitialExtConsts (applyME b) := by
      rw [hInitConsts]
      simp only [runRounds]
      exact externalRound_ne_of_ne _ _ _ (externalRound_ne_of_ne _ _ _
        (externalRound_ne_of_ne _ _ _ (externalRound_ne_of_ne _ _ _ hs0)))
    have hs2 : runRounds internalRound poseidon2InternalConsts
          (runRounds externalRound poseidon2InitialExtConsts (applyME a)) ≠
        runRounds internalRound poseidon2InternalConsts
          (runRounds externalRound poseidon2InitialExtConsts (applyME b)) :=
      runRounds_int_ne_of_ne poseidon2InternalConsts _ _ hs1
    have hTerm14 : 14 ≤ countExtRoundsActive poseidon2TerminalExtConsts
        (runRounds internalRound poseidon2InternalConsts
          (runRounds externalRound poseidon2InitialExtConsts (applyME a)))
        (runRounds internalRound poseidon2InternalConsts
          (runRounds externalRound poseidon2InitialExtConsts (applyME b))) := by
      rw [hTermConsts]
      exact countExtRoundsActive_four _ _ _ _ _ _ hs2
    unfold poseidon2Perm12ActiveSboxes
    dsimp only
    omega
  · intro active hAct
    have h36Base : 36 * 2 ^ 57 < goldilocksPrime := by decide
    have h6Base : 6 * 2 ^ 60 < goldilocksPrime := by decide
    have hMulPow : ∀ (a b k : Nat), (a * b) ^ k = a ^ k * b ^ k := fun a b k => by
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, ih]
        ac_rfl
    have hPow36 : 36 ^ active * 2 ^ (57 * active) < goldilocksPrime ^ active := by
      have hLt := pow_lt_pow_of_lt_base (36 * 2 ^ 57) goldilocksPrime active (by decide) h36Base (by omega)
      rwa [hMulPow, ← Nat.pow_mul] at hLt
    have hPow6 : 6 ^ active * 2 ^ (60 * active) < goldilocksPrime ^ active := by
      have hLt := pow_lt_pow_of_lt_base (6 * 2 ^ 60) goldilocksPrime active (by decide) h6Base (by omega)
      rwa [hMulPow, ← Nat.pow_mul] at hLt
    have h57 : 256 ≤ 57 * active := by omega
    have h60 : 1680 ≤ 60 * active := by omega
    have h256Le : 2 ^ 256 ≤ 2 ^ (57 * active) :=
      Nat.pow_le_pow_right (by decide) h57
    have h1680Le : 2 ^ 1680 ≤ 2 ^ (60 * active) :=
      Nat.pow_le_pow_right (by decide) h60
    have h36_256 : 36 ^ active * 2 ^ 256 < goldilocksPrime ^ active :=
      Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ h256Le) hPow36
    have h6_1680 : 6 ^ active * 2 ^ 1680 < goldilocksPrime ^ active :=
      Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ h1680Le) hPow6
    have h6Le36All : ∀ n : Nat, 6 ^ n ≤ 36 ^ n := fun n => by
      induction n with
      | zero => decide
      | succ k ih =>
        rw [Nat.pow_succ, Nat.pow_succ]
        exact Nat.mul_le_mul ih (by decide)
    have h6Le36 : 6 ^ active ≤ 36 ^ active := h6Le36All active
    exact ⟨Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ h6Le36) h36_256, h36_256, h6_1680⟩

/-! ## 10. Width-12 Symbolic Circuit, Univariate Saturation & CICO-1 Macaulay / Bézout Bounds -/

structure SymbolicLane4 where
  x0 : PoseidonExpr
  x1 : PoseidonExpr
  x2 : PoseidonExpr
  x3 : PoseidonExpr

structure SymbolicState12 where
  b0 : SymbolicLane4
  b1 : SymbolicLane4
  b2 : SymbolicLane4

def SymbolicLane4.eval (v : Nat → Goldilocks) (b : SymbolicLane4) : Lane4 :=
  ⟨b.x0.eval v, b.x1.eval v, b.x2.eval v, b.x3.eval v⟩

def SymbolicState12.eval (v : Nat → Goldilocks) (s : SymbolicState12) : Poseidon2State12 :=
  ⟨s.b0.eval v, s.b1.eval v, s.b2.eval v⟩

def SymbolicLane4.maxDeg (b : SymbolicLane4) : Nat :=
  max (max b.x0.degree b.x1.degree) (max b.x2.degree b.x3.degree)

def SymbolicState12.maxDeg (s : SymbolicState12) : Nat :=
  max (max s.b0.maxDeg s.b1.maxDeg) s.b2.maxDeg

def symbolicLane4Add (a b : SymbolicLane4) : SymbolicLane4 :=
  ⟨.add a.x0 b.x0, .add a.x1 b.x1, .add a.x2 b.x2, .add a.x3 b.x3⟩

def symbolicLane4Const (c : Lane4) : SymbolicLane4 :=
  ⟨.constant c.x0, .constant c.x1, .constant c.x2, .constant c.x3⟩

def symbolicApplyM4 (b : SymbolicLane4) : SymbolicLane4 :=
  let s : PoseidonExpr := .add (.add b.x0 b.x1) (.add b.x2 b.x3)
  let c2 : PoseidonExpr := .constant (Goldilocks.ofNat 2)
  ⟨.add s (.add b.x0 (.mul c2 b.x1)),
   .add s (.add b.x1 (.mul c2 b.x2)),
   .add s (.add b.x2 (.mul c2 b.x3)),
   .add s (.add b.x3 (.mul c2 b.x0))⟩

def symbolicME12 (st : SymbolicState12) : SymbolicState12 :=
  let y0 := symbolicApplyM4 st.b0
  let y1 := symbolicApplyM4 st.b1
  let y2 := symbolicApplyM4 st.b2
  let s := symbolicLane4Add (symbolicLane4Add y0 y1) y2
  ⟨symbolicLane4Add y0 s, symbolicLane4Add y1 s, symbolicLane4Add y2 s⟩

def symbolicMI12WithSum (st : SymbolicState12) (s : PoseidonExpr) : SymbolicState12 :=
  ⟨⟨.add (.mul (.constant (goldOfInt (-2))) st.b0.x0) s,
    .add st.b0.x1 s,
    .add (.mul (.constant (goldOfInt 2)) st.b0.x2) s,
    .add (.mul (.constant (goldOfInt 4)) st.b0.x3) s⟩,
   ⟨.add (.mul (.constant (goldOfInt 8)) st.b1.x0) s,
    .add (.mul (.constant (goldOfInt 16)) st.b1.x1) s,
    .add (.mul (.constant (goldOfInt 32)) st.b1.x2) s,
    .add (.mul (.constant (goldOfInt 64)) st.b1.x3) s⟩,
   ⟨.add (.mul (.constant (goldOfInt 128)) st.b2.x0) s,
    .add (.mul (.constant (goldOfInt 256)) st.b2.x1) s,
    .add (.mul (.constant (goldOfInt 512)) st.b2.x2) s,
    .add (.mul (.constant (goldOfInt 1024)) st.b2.x3) s⟩⟩

def symbolicMI12 (st : SymbolicState12) : SymbolicState12 :=
  let sum4 (b : SymbolicLane4) : PoseidonExpr := .add (.add b.x0 b.x1) (.add b.x2 b.x3)
  symbolicMI12WithSum st (.add (.add (sum4 st.b0) (sum4 st.b1)) (sum4 st.b2))

def symbolicExtRound12 (rc : Poseidon2State12) (st : SymbolicState12) : SymbolicState12 :=
  let sbox4 (b : SymbolicLane4) (c : Lane4) : SymbolicLane4 :=
    ⟨(PoseidonExpr.add b.x0 (.constant c.x0)).seventh,
     (PoseidonExpr.add b.x1 (.constant c.x1)).seventh,
     (PoseidonExpr.add b.x2 (.constant c.x2)).seventh,
     (PoseidonExpr.add b.x3 (.constant c.x3)).seventh⟩
  symbolicME12 ⟨sbox4 st.b0 rc.b0, sbox4 st.b1 rc.b1, sbox4 st.b2 rc.b2⟩

def symbolicIntRound12 (rc : Goldilocks) (st : SymbolicState12) : SymbolicState12 :=
  let x0' := (PoseidonExpr.add st.b0.x0 (.constant rc)).seventh
  symbolicMI12 ⟨⟨x0', st.b0.x1, st.b0.x2, st.b0.x3⟩, st.b1, st.b2⟩

def symbolicPerm12 (st : SymbolicState12) : SymbolicState12 :=
  let s0 := symbolicME12 st
  let s1 := runRounds symbolicExtRound12 poseidon2InitialExtConsts s0
  let s2 := runRounds symbolicIntRound12 poseidon2InternalConsts s1
  runRounds symbolicExtRound12 poseidon2TerminalExtConsts s2

private theorem symbolicME12_eval (v : Nat → Goldilocks) (st : SymbolicState12) :
    (symbolicME12 st).eval v = applyME (st.eval v) := rfl

private theorem symbolicMI12_eval (v : Nat → Goldilocks) (st : SymbolicState12) :
    (symbolicMI12 st).eval v = applyMI (st.eval v) := rfl

private theorem symbolicExtRound12_eval (v : Nat → Goldilocks) (rc : Poseidon2State12)
    (st : SymbolicState12) :
    (symbolicExtRound12 rc st).eval v = externalRound rc (st.eval v) := rfl

private theorem symbolicIntRound12_eval (v : Nat → Goldilocks) (rc : Goldilocks)
    (st : SymbolicState12) :
    (symbolicIntRound12 rc st).eval v = internalRound rc (st.eval v) := rfl

private theorem runRounds_symbolic_eval {α : Type} (v : Nat → Goldilocks)
    (sStep : α → SymbolicState12 → SymbolicState12)
    (cStep : α → Poseidon2State12 → Poseidon2State12)
    (hStep : ∀ c st, (sStep c st).eval v = cStep c (st.eval v)) :
    ∀ (cs : List α) (st : SymbolicState12),
      (runRounds sStep cs st).eval v = runRounds cStep cs (st.eval v)
  | [], _ => rfl
  | c :: cs, st => by
    simp only [runRounds, runRounds_symbolic_eval v sStep cStep hStep cs (sStep c st), hStep]

private theorem max_le_of_le {a b k : Nat} (ha : a ≤ k) (hb : b ≤ k) : max a b ≤ k := by omega
private theorem le_of_max_le_left {a b k : Nat} (h : max a b ≤ k) : a ≤ k := by omega
private theorem le_of_max_le_right {a b k : Nat} (h : max a b ≤ k) : b ≤ k := by omega

private theorem symbolicLane4Add_maxDeg_le (a b : SymbolicLane4) (k : Nat)
    (ha : a.maxDeg ≤ k) (hb : b.maxDeg ≤ k) : (symbolicLane4Add a b).maxDeg ≤ k := by
  unfold SymbolicLane4.maxDeg at ha hb
  unfold symbolicLane4Add SymbolicLane4.maxDeg
  dsimp only [PoseidonExpr.degree]
  omega

private theorem symbolicApplyM4_maxDeg_le (b : SymbolicLane4) (k : Nat)
    (hb : b.maxDeg ≤ k) : (symbolicApplyM4 b).maxDeg ≤ k := by
  unfold SymbolicLane4.maxDeg at hb
  have h0 : b.x0.degree ≤ k := by omega
  have h1 : b.x1.degree ≤ k := by omega
  have h2 : b.x2.degree ≤ k := by omega
  have h3 : b.x3.degree ≤ k := by omega
  have hs : (PoseidonExpr.add (.add b.x0 b.x1) (.add b.x2 b.x3)).degree ≤ k := by
    dsimp only [PoseidonExpr.degree]; omega
  unfold symbolicApplyM4 SymbolicLane4.maxDeg
  dsimp only
  apply max_le_of_le <;> apply max_le_of_le <;> (dsimp only [PoseidonExpr.degree]; omega)

private theorem symbolicME12_maxDeg_le (st : SymbolicState12) (k : Nat) (h : st.maxDeg ≤ k) :
    (symbolicME12 st).maxDeg ≤ k := by
  unfold SymbolicState12.maxDeg at h
  have hb0 : st.b0.maxDeg ≤ k := le_of_max_le_left (le_of_max_le_left h)
  have hb1 : st.b1.maxDeg ≤ k := le_of_max_le_right (le_of_max_le_left h)
  have hb2 : st.b2.maxDeg ≤ k := le_of_max_le_right h
  have hy0 := symbolicApplyM4_maxDeg_le st.b0 k hb0
  have hy1 := symbolicApplyM4_maxDeg_le st.b1 k hb1
  have hy2 := symbolicApplyM4_maxDeg_le st.b2 k hb2
  have hs := symbolicLane4Add_maxDeg_le _ _ k (symbolicLane4Add_maxDeg_le _ _ k hy0 hy1) hy2
  unfold symbolicME12 SymbolicState12.maxDeg
  exact max_le_of_le
    (max_le_of_le (symbolicLane4Add_maxDeg_le _ _ k hy0 hs) (symbolicLane4Add_maxDeg_le _ _ k hy1 hs))
    (symbolicLane4Add_maxDeg_le _ _ k hy2 hs)

private theorem symbolicMI12WithSum_maxDeg_le (st : SymbolicState12) (s : PoseidonExpr) (k : Nat)
    (h : st.maxDeg ≤ k) (hs : s.degree ≤ k) :
    (symbolicMI12WithSum st s).maxDeg ≤ k := by
  unfold SymbolicState12.maxDeg at h
  have hb0 : st.b0.maxDeg ≤ k := le_of_max_le_left (le_of_max_le_left h)
  have hb1 : st.b1.maxDeg ≤ k := le_of_max_le_right (le_of_max_le_left h)
  have hb2 : st.b2.maxDeg ≤ k := le_of_max_le_right h
  unfold SymbolicLane4.maxDeg at hb0 hb1 hb2
  unfold symbolicMI12WithSum SymbolicState12.maxDeg SymbolicLane4.maxDeg
  dsimp only [PoseidonExpr.degree]
  omega

private theorem symbolicMI12_maxDeg_le (st : SymbolicState12) (k : Nat) (h : st.maxDeg ≤ k) :
    (symbolicMI12 st).maxDeg ≤ k := by
  have hb0 : st.b0.maxDeg ≤ k := by unfold SymbolicState12.maxDeg at h; omega
  have hb1 : st.b1.maxDeg ≤ k := by unfold SymbolicState12.maxDeg at h; omega
  have hb2 : st.b2.maxDeg ≤ k := by unfold SymbolicState12.maxDeg at h; omega
  have hs0 : (PoseidonExpr.add (.add st.b0.x0 st.b0.x1) (.add st.b0.x2 st.b0.x3)).degree ≤ k := by
    unfold SymbolicLane4.maxDeg at hb0; dsimp only [PoseidonExpr.degree]; omega
  have hs1 : (PoseidonExpr.add (.add st.b1.x0 st.b1.x1) (.add st.b1.x2 st.b1.x3)).degree ≤ k := by
    unfold SymbolicLane4.maxDeg at hb1; dsimp only [PoseidonExpr.degree]; omega
  have hs2 : (PoseidonExpr.add (.add st.b2.x0 st.b2.x1) (.add st.b2.x2 st.b2.x3)).degree ≤ k := by
    unfold SymbolicLane4.maxDeg at hb2; dsimp only [PoseidonExpr.degree]; omega
  exact symbolicMI12WithSum_maxDeg_le st _ k h (max_le_of_le (max_le_of_le hs0 hs1) hs2)

private theorem sbox4_maxDeg_le (b : SymbolicLane4) (c : Lane4) (k : Nat) (hb : b.maxDeg ≤ k) :
    (SymbolicLane4.mk
      (PoseidonExpr.add b.x0 (.constant c.x0)).seventh
      (PoseidonExpr.add b.x1 (.constant c.x1)).seventh
      (PoseidonExpr.add b.x2 (.constant c.x2)).seventh
      (PoseidonExpr.add b.x3 (.constant c.x3)).seventh).maxDeg ≤ 7 * k := by
  unfold SymbolicLane4.maxDeg at hb ⊢
  dsimp only
  simp only [symbolic_sbox7_degree, PoseidonExpr.degree, Nat.max_zero]
  omega

private theorem symbolicExtRound12_maxDeg_le (rc : Poseidon2State12) (st : SymbolicState12)
    (k : Nat) (h : st.maxDeg ≤ k) :
    (symbolicExtRound12 rc st).maxDeg ≤ 7 * k := by
  unfold SymbolicState12.maxDeg at h
  have hb0 := sbox4_maxDeg_le st.b0 rc.b0 k (le_of_max_le_left (le_of_max_le_left h))
  have hb1 := sbox4_maxDeg_le st.b1 rc.b1 k (le_of_max_le_right (le_of_max_le_left h))
  have hb2 := sbox4_maxDeg_le st.b2 rc.b2 k (le_of_max_le_right h)
  unfold symbolicExtRound12
  dsimp only
  exact symbolicME12_maxDeg_le _ (7 * k) (max_le_of_le (max_le_of_le hb0 hb1) hb2)

private theorem symbolicIntRound12_maxDeg_le (rc : Goldilocks) (st : SymbolicState12)
    (k : Nat) (h : st.maxDeg ≤ k) :
    (symbolicIntRound12 rc st).maxDeg ≤ 7 * k := by
  unfold SymbolicState12.maxDeg at h
  have hb0 : st.b0.maxDeg ≤ k := le_of_max_le_left (le_of_max_le_left h)
  have hb1 : st.b1.maxDeg ≤ 7 * k := by
    have := le_of_max_le_right (le_of_max_le_left h); omega
  have hb2 : st.b2.maxDeg ≤ 7 * k := by
    have := le_of_max_le_right h; omega
  have hb0' : (SymbolicLane4.mk (PoseidonExpr.add st.b0.x0 (.constant rc)).seventh
      st.b0.x1 st.b0.x2 st.b0.x3).maxDeg ≤ 7 * k := by
    unfold SymbolicLane4.maxDeg at hb0 ⊢
    dsimp only
    simp only [symbolic_sbox7_degree, PoseidonExpr.degree, Nat.max_zero]
    omega
  unfold symbolicIntRound12
  dsimp only
  exact symbolicMI12_maxDeg_le _ (7 * k) (max_le_of_le (max_le_of_le hb0' hb1) hb2)

private theorem runRounds_maxDeg_le {α : Type}
    (step : α → SymbolicState12 → SymbolicState12)
    (hStep : ∀ c st k, st.maxDeg ≤ k → (step c st).maxDeg ≤ 7 * k) :
    ∀ (cs : List α) (st : SymbolicState12) (k : Nat),
      st.maxDeg ≤ k → (runRounds step cs st).maxDeg ≤ 7 ^ cs.length * k
  | [], st, k, h => by simpa [runRounds] using h
  | c :: cs, st, k, h => by
    simp only [runRounds, List.length_cons]
    have h1 := hStep c st k h
    have ih := runRounds_maxDeg_le step hStep cs (step c st) (7 * k) h1
    have hEq : 7 ^ cs.length * (7 * k) = 7 ^ (cs.length + 1) * k := by
      rw [Nat.pow_succ]; ac_rfl
    omega

/-- Macaulay / CICO-1 semi-regularity degree `(7 * r + 1) / 2` and Pascal binomial coefficient. -/
def cicoMacaulayDegree (activeRounds : Nat) : Nat := (7 * activeRounds + 1) / 2

def binomCoeff : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binomCoeff n k + binomCoeff n (k + 1)

private theorem binomCoeff_gt_zero : ∀ (n k : Nat), n < k → binomCoeff n k = 0
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
    simp only [binomCoeff, binomCoeff_gt_zero n k (by omega),
      binomCoeff_gt_zero n (k + 1) (by omega)]

private theorem binomCoeff_self : ∀ n : Nat, binomCoeff n n = 1
  | 0 => rfl
  | n + 1 => by simp only [binomCoeff, binomCoeff_self n, binomCoeff_gt_zero n (n + 1) (by omega)]

private theorem binomCoeff_symm : ∀ (n k : Nat), k ≤ n → binomCoeff n k = binomCoeff n (n - k)
  | _, 0, _ => by simp [binomCoeff, binomCoeff_self]
  | 0, _ + 1, h => by omega
  | n + 1, k + 1, h => by
    by_cases hEq : k = n
    · subst hEq; simp [binomCoeff_self, binomCoeff, binomCoeff_gt_zero k (k + 1) (by omega)]
    · have hkLt : k < n := by omega
      have hSub : n + 1 - (k + 1) = (n - (k + 1)) + 1 := by omega
      have hSub2 : n - k = (n - (k + 1)) + 1 := by omega
      rw [hSub]
      simp only [binomCoeff]
      rw [binomCoeff_symm n k (by omega), binomCoeff_symm n (k + 1) (by omega), hSub2]
      omega

private theorem two_pow_le_binomCoeff_central : ∀ k : Nat, 2 ^ k ≤ binomCoeff (2 * k) k
  | 0 => by decide
  | 1 => by decide
  | m + 2 => by
    have ih := two_pow_le_binomCoeff_central (m + 1)
    have hSubSymm : binomCoeff (2 * m + 3) (m + 1) = binomCoeff (2 * m + 3) (m + 2) := by
      have hs := binomCoeff_symm (2 * m + 3) (m + 1) (by omega)
      have hsub : 2 * m + 3 - (m + 1) = m + 2 := by omega
      rwa [hsub] at hs
    have h2m4 : 2 * (m + 2) = (2 * m + 3) + 1 := by omega
    have h2m2 : 2 * (m + 1) = 2 * m + 2 := by omega
    have hP : binomCoeff (2 * (m + 2)) (m + 2) =
        binomCoeff (2 * m + 3) (m + 1) + binomCoeff (2 * m + 3) (m + 2) := by
      rw [h2m4]; rfl
    have hGe : binomCoeff (2 * (m + 1)) (m + 1) ≤ binomCoeff (2 * m + 3) (m + 1) := by
      have hEq : binomCoeff (2 * m + 3) (m + 1) =
          binomCoeff (2 * m + 2) m + binomCoeff (2 * m + 2) (m + 1) := rfl
      rw [h2m2]
      omega
    rw [Nat.pow_succ]
    omega

private theorem binomCoeff_mono_add_left (a b c : Nat) :
    binomCoeff (a + b) b ≤ binomCoeff (a + c + b) b := by
  induction c with
  | zero => simp
  | succ c ih =>
    have hEq : a + (c + 1) + b = (a + c + b) + 1 := by omega
    rw [hEq]
    cases b with
    | zero => simp [binomCoeff]
    | succ b' =>
      have hStep : binomCoeff ((a + c + (b' + 1)) + 1) (b' + 1) =
          binomCoeff (a + c + (b' + 1)) b' + binomCoeff (a + c + (b' + 1)) (b' + 1) := rfl
      rw [hStep]
      omega

private theorem binomCoeff_mono_both (a a' b b' : Nat) (ha : a ≤ a') (hb : b ≤ b') :
    binomCoeff (a + b) b ≤ binomCoeff (a' + b') b' := by
  have h1 : binomCoeff (a + b) b ≤ binomCoeff (a' + b) b := by
    obtain ⟨d, rfl⟩ : ∃ d, a' = a + d := ⟨a' - a, by omega⟩
    exact binomCoeff_mono_add_left a b d
  have hSym1 : binomCoeff (a' + b) b = binomCoeff (b + a') a' := by
    rw [Nat.add_comm a' b]
    have hs := binomCoeff_symm (b + a') b (by omega)
    have hsub : b + a' - b = a' := by omega
    rwa [hsub] at hs
  have h2 : binomCoeff (b + a') a' ≤ binomCoeff (b' + a') a' := by
    obtain ⟨e, rfl⟩ : ∃ e, b' = b + e := ⟨b' - b, by omega⟩
    exact binomCoeff_mono_add_left b a' e
  have hSym2 : binomCoeff (b' + a') a' = binomCoeff (a' + b') b' := by
    rw [Nat.add_comm b' a']
    have hs := binomCoeff_symm (a' + b') a' (by omega)
    have hsub : a' + b' - a' = b' := by omega
    rwa [hsub] at hs
  omega

/-- **Width-12 Symbolic Evaluation, Forward/Backward Degree Saturation & CICO-1/GSR/`2026/306` Bounds**:
    1. `symbolicPerm12` evaluates identically to `poseidon2Perm12` and has degree `≤ 7^30` on affine inputs.
    2. Forward/backward univariate root-finding saturates `goldilocksPrime`: for every split `rFwd + rBwd = 30`,
       either `rBwd = 0` (`7^rFwd = 7^30 > goldilocksPrime`), or `1 ≤ rBwd` (`poseidon2DInv > 2^63` per backward
       inverse S-box, with combined Bézout degree `7^rFwd * 7^rBwd = 7^30 > goldilocksPrime` and `(7^30)^2 > 2^128`).
    3. CICO-1 round/S-box Gröbner Macaulay & Bézout bounds exceed `2^128`:
       - Half-full + partial S-box Bézout bound `7^(12 * (8 / 2) + 22) = 7^70 > 2^196 > 2^128`;
       - Merz–Rodríguez García (`2026/306`) worst-case skipped ideal degree `7^(22 + 4) = 7^26` satisfies
         `(7^26)^2 = 7^52 > 2^145 > 2^128`;
       - Bhati–Tariq–Ashur (`2026/1692`) GSR with `R_F0 = 4` leaves `7^(3 * 11 + 16) = 7^49 > 2^128`
         (and CICO-4 `7^(4 * 22) = 7^88 > 2^247 > 2^128`);
       - Macaulay matrix column count `binomCoeff (70 + cicoMacaulayDegree 26) 70 ≥ 2^70` has quadratic
         linear-algebra cost `(binomCoeff (70 + cicoMacaulayDegree 26) 70)^2 > 2^128`. -/
theorem poseidon2_width12_cico_groebner_and_interpolation_bounds :
    (∀ (v : Nat → Goldilocks) (st : SymbolicState12),
      (symbolicPerm12 st).eval v = poseidon2Perm12 (st.eval v)) ∧
    (∀ st : SymbolicState12, st.maxDeg ≤ 1 → (symbolicPerm12 st).maxDeg ≤ 7 ^ 30) ∧
    (∀ rFwd rBwd : Nat, rFwd + rBwd = 30 →
      (rBwd = 0 → goldilocksPrime < 7 ^ rFwd) ∧
      (1 ≤ rBwd → 2 ^ 63 < poseidon2DInv ∧ goldilocksPrime < 7 ^ rFwd * 7 ^ rBwd ∧
        2 ^ 128 < (7 ^ rFwd * 7 ^ rBwd) ^ 2)) ∧
    2 ^ 128 < 7 ^ (12 * (8 / 2) + 22) ∧
    2 ^ 128 < (7 ^ (22 + 4)) ^ 2 ∧
    2 ^ 128 < 7 ^ (3 * 11 + (22 + 4 - 12 + 2)) ∧
    2 ^ 128 < (binomCoeff (70 + cicoMacaulayDegree 26) 70) ^ 2 := by
  refine ⟨?_, ?_, ?_, by decide, by decide, by decide, ?_⟩
  · intro v st
    unfold symbolicPerm12 poseidon2Perm12
    dsimp only
    rw [runRounds_symbolic_eval v symbolicExtRound12 externalRound (symbolicExtRound12_eval v),
        runRounds_symbolic_eval v symbolicIntRound12 internalRound (symbolicIntRound12_eval v),
        runRounds_symbolic_eval v symbolicExtRound12 externalRound (symbolicExtRound12_eval v),
        symbolicME12_eval]
  · intro st h1
    unfold symbolicPerm12
    have h0 := symbolicME12_maxDeg_le st 1 h1
    have h1' := runRounds_maxDeg_le symbolicExtRound12 symbolicExtRound12_maxDeg_le
      poseidon2InitialExtConsts (symbolicME12 st) 1 h0
    have h2' := runRounds_maxDeg_le symbolicIntRound12 symbolicIntRound12_maxDeg_le
      poseidon2InternalConsts _ _ h1'
    have h3' := runRounds_maxDeg_le symbolicExtRound12 symbolicExtRound12_maxDeg_le
      poseidon2TerminalExtConsts _ _ h2'
    have hLens : poseidon2InitialExtConsts.length = 4 ∧
        poseidon2InternalConsts.length = 22 ∧
        poseidon2TerminalExtConsts.length = 4 := ⟨rfl, rfl, rfl⟩
    rw [hLens.1, hLens.2.1, hLens.2.2] at h3'
    have hPow : 7 ^ 4 * (7 ^ 22 * (7 ^ 4 * 1)) = 7 ^ 30 := by decide
    omega
  · intro rFwd rBwd hSum
    refine ⟨?_, ?_⟩
    · intro h0; subst h0; simp at hSum; subst hSum; decide
    · intro _
      rw [← Nat.pow_add, hSum]
      exact ⟨by decide, by decide, by decide⟩
  · have hMac : 70 ≤ cicoMacaulayDegree 26 := by decide
    have hMono := binomCoeff_mono_both 70 (cicoMacaulayDegree 26) 70 70 hMac (Nat.le_refl 70)
    have h140 : 70 + 70 = 2 * 70 := rfl
    have h70 : 2 ^ 70 ≤ binomCoeff (70 + 70) 70 := by
      rw [h140]; exact two_pow_le_binomCoeff_central 70
    have hGe : 2 ^ 70 ≤ binomCoeff (cicoMacaulayDegree 26 + 70) 70 := Nat.le_trans h70 hMono
    rw [Nat.add_comm 70 (cicoMacaulayDegree 26)]
    have hPow2 : ∀ n : Nat, n ^ 2 = n * n := fun n => by
      rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
    have hSq : (2 ^ 70) ^ 2 ≤ (binomCoeff (cicoMacaulayDegree 26 + 70) 70) ^ 2 := by
      rw [hPow2, hPow2]; exact Nat.mul_le_mul hGe hGe
    exact Nat.lt_of_lt_of_le (by decide : 2 ^ 128 < (2 ^ 70) ^ 2) hSq

/-- `#tooth` **Reduced-Round `(R_F = 4, R_P = 10)` & Single-Initial-Round GSR Failure (`tooth_reduced_poseidon2_fails_cico_and_gsr`)**:
    1. At `(R_F = 4, R_P = 10)` (`14` rounds), univariate degree `7^14 < goldilocksPrime` and half-full +
       partial Bézout degree `7^(12 * (4 / 2) + 10) = 7^34 < 2^128` both fail!
    2. If initial full rounds were reduced from `R_F0 = 4` to `R_F0 = 1` (`2026/1692` GSR premise),
       univariate CICO-1 degree drops to `7^(22 + 4 - 12 + 2) = 7^16 < goldilocksPrime`! -/
theorem tooth_reduced_poseidon2_fails_cico_and_gsr :
    7 ^ (4 + 10) < goldilocksPrime ∧
    7 ^ (12 * (4 / 2) + 10) < 2 ^ 128 ∧
    7 ^ (22 + 4 - 12 + 2) < goldilocksPrime := by decide

/-! ## 11. Succinct Outer Recursive `Hem` Aggregation (`bciksJohnsonQrom128`) & Soundness Composition -/

def hemOuterDomainTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2e, 0x48, 0x45, 0x4d, 0x2e, 0x4f, 0x55, 0x54, 0x45, 0x52, 0x2f, 0x76, 0x31]

/-- Compact shard header carried by a succinct outer `Hem` certificate (`O(1)` outer WHIR proof,
    shipping zero child `SuccinctAggregateProof` payloads). -/
structure ShardCompressedHeader where
  shardId : List UInt8
  threshold : Nat
  suiteId : List UInt8
  params : PqHashParams
  committee : List PqPublicKey
  bitmap : SignerBitmapSpec
  childProofDigest : List UInt8
  deriving DecidableEq

def ShardCompressedHeader.registration (h : ShardCompressedHeader) : ShardRegistration :=
  ⟨h.shardId, h.threshold, h.suiteId, h.params, h.committee⟩

def encodeBitmapBytes (bm : SignerBitmapSpec) : List UInt8 :=
  bm.map (fun b => if b then 1 else 0)

private theorem encodeBitmapBytes_injective {a b : SignerBitmapSpec}
    (h : encodeBitmapBytes a = encodeBitmapBytes b) : a = b :=
  map_inj_of_inj (fun x y hxy => by cases x <;> cases y <;> first | rfl | cases hxy) h

def encodeShardCompressedHeader (h : ShardCompressedHeader) : List UInt8 :=
  encodeMultiFrame [
    encodeRegistration h.registration,
    encodeBitmapBytes h.bitmap,
    h.childProofDigest
  ]

def encodeCompressedHeaderChain (hs : List ShardCompressedHeader) : List UInt8 :=
  encodeMultiFrame (hs.map encodeShardCompressedHeader)

theorem encodeShardCompressedHeader_injective {a b : ShardCompressedHeader}
    (h : encodeShardCompressedHeader a = encodeShardCompressedHeader b) : a = b := by
  have h0 := encodeMultiFrame_injective h
  obtain ⟨hReg, h1⟩ := List.cons.inj h0
  obtain ⟨hBm, h2⟩ := List.cons.inj h1
  obtain ⟨hDig, _⟩ := List.cons.inj h2
  have hr := encodeRegistration_injective hReg
  have hb := encodeBitmapBytes_injective hBm
  cases a; cases b
  unfold ShardCompressedHeader.registration at hr
  cases hr
  subst hb hDig
  rfl

theorem encodeCompressedHeaderChain_injective {a b : List ShardCompressedHeader}
    (h : encodeCompressedHeaderChain a = encodeCompressedHeaderChain b) : a = b :=
  map_inj_of_inj (fun _ _ => encodeShardCompressedHeader_injective) (encodeMultiFrame_injective h)

def succinctOuterBoundMessage (registryDigest epochFloor msg headerChainDigest : List UInt8) :
    List UInt8 :=
  encodeMultiFrame [hemOuterDomainTag, registryDigest, epochFloor, msg, headerChainDigest]

theorem succinctOuterBoundMessage_injective {r1 e1 m1 c1 r2 e2 m2 c2 : List UInt8}
    (h : succinctOuterBoundMessage r1 e1 m1 c1 = succinctOuterBoundMessage r2 e2 m2 c2) :
    r1 = r2 ∧ e1 = e2 ∧ m1 = m2 ∧ c1 = c2 := by
  have h0 := encodeMultiFrame_injective h
  simp only [List.cons.injEq, and_true, true_and] at h0
  exact h0

/-- Succinct outer recursive `Hem` certificate: `headers` carries only compact shard metadata and
    32-byte child digests, verified by ONE outer `bciksJohnsonQrom128` `SuccinctAggregateProof`. -/
structure SuccinctOuterHemCertificate where
  headers : List ShardCompressedHeader
  outerInst : AggPublicInstance
  outerProof : SuccinctAggregateProof
  outerFs : List UInt8

def headerCommitteeFlat : List ShardCompressedHeader → List PqPublicKey
  | [] => []
  | h :: rest => h.committee ++ headerCommitteeFlat rest

def headerClaimedWeight : List ShardCompressedHeader → Nat
  | [] => 0
  | h :: rest => bitmapPopcountSpec h.bitmap + headerClaimedWeight rest

def verifyHeaderQuorum (h : ShardCompressedHeader) : Bool :=
  decide (1 ≤ h.threshold) &&
  decide (h.threshold ≤ h.committee.length) &&
  decide (h.threshold ≤ bitmapPopcountSpec h.bitmap)

/-- Executable verifier for succinct outer recursive `Hem` aggregation, pinning the outer proof and
    instance to unconditional `.bciksJohnsonQrom128` and binding `encodeCompressedHeaderChain`. -/
def verifySuccinctRecursiveHem (H : Hash) (outerArith : RowArithmetization) (outerDom : WhirDomain)
    (registryDigest epochFloor msg : List UInt8) (cert : SuccinctOuterHemCertificate) : Bool :=
  decide (1 ≤ cert.headers.length) &&
  decide (H (encodeRegistry (cert.headers.map ShardCompressedHeader.registration)) = registryDigest) &&
  decide ((cert.headers.map (·.shardId)).Nodup) &&
  decide ((headerCommitteeFlat cert.headers).Nodup) &&
  cert.headers.all verifyHeaderQuorum &&
  decide (cert.outerInst.regime = .bciksJohnsonQrom128) &&
  decide (cert.outerProof.agg.regime = .bciksJohnsonQrom128) &&
  decide (cert.outerInst.message =
    succinctOuterBoundMessage registryDigest epochFloor msg
      (H (encodeCompressedHeaderChain cert.headers))) &&
  verifySuccinctAggregate outerArith outerDom cert.outerInst cert.outerProof cert.outerFs

def shardToCompressedHeader (digestProof : SuccinctAggregateProof → List UInt8)
    (s : HemShardProof) : ShardCompressedHeader :=
  { shardId := s.shardId
    threshold := s.threshold
    suiteId := s.inst.suite.suiteId
    params := s.inst.params
    committee := s.inst.committee
    bitmap := s.proof.agg.bitmap
    childProofDigest := digestProof s.proof }

/-- Extraction witness bundle for succinct outer recursive `Hem`: connects the outer `Hem` committed
    table to the `M` inner shard extraction environments verified by the outer relation. -/
structure SuccinctRecursiveHemEnv (H : Hash)
    (outerArith : RowArithmetization) (outerDom : WhirDomain)
    (innerArith : RowArithmetization) (innerDom : WhirDomain)
    (epochFloor msg : List UInt8)
    (cert : SuccinctOuterHemCertificate) where
  digestProof : SuccinctAggregateProof → List UInt8
  outerLaw : outerArith.Lawful outerDom cert.outerInst
  outerView : SuccinctExtractionView
  outerBound : StagesBound outerView.authPath outerDom.stages outerView.allTables cert.outerProof.stages
  innerEnvs : List (HemShardEnv innerArith innerDom)
  outerRelationSound :
    checkAllActiveSigners cert.outerInst.suite cert.outerInst.params cert.outerInst.message
      cert.outerInst.committee cert.outerProof.agg.bitmap
      (outerArith.decodeSigs ((outerView.allTables.headD []).headD [])) = true →
    (innerEnvs.map (fun e => shardToCompressedHeader digestProof e.shard) = cert.headers ∧
     ∀ e ∈ innerEnvs,
       e.shard.inst.message = shardBoundMessage e.shard.shardId epochFloor msg ∧
       verifySuccinctAggregate innerArith innerDom e.shard.inst e.shard.proof e.shard.fs = true)

private theorem verifySuccinctRecursiveHem_facts {H : Hash}
    {outerArith : RowArithmetization} {outerDom : WhirDomain}
    {registryDigest epochFloor msg : List UInt8} {cert : SuccinctOuterHemCertificate}
    (h : verifySuccinctRecursiveHem H outerArith outerDom registryDigest epochFloor msg cert = true) :
    1 ≤ cert.headers.length ∧
    H (encodeRegistry (cert.headers.map ShardCompressedHeader.registration)) = registryDigest ∧
    (cert.headers.map (·.shardId)).Nodup ∧
    (headerCommitteeFlat cert.headers).Nodup ∧
    (∀ hd ∈ cert.headers, verifyHeaderQuorum hd = true) ∧
    cert.outerInst.regime = .bciksJohnsonQrom128 ∧
    cert.outerProof.agg.regime = .bciksJohnsonQrom128 ∧
    cert.outerInst.message =
      succinctOuterBoundMessage registryDigest epochFloor msg
        (H (encodeCompressedHeaderChain cert.headers)) ∧
    verifySuccinctAggregate outerArith outerDom cert.outerInst cert.outerProof cert.outerFs = true := by
  unfold verifySuccinctRecursiveHem at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2,
    h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

private theorem map_reg_of_headers (dp : SuccinctAggregateProof → List UInt8) :
    ∀ shards : List HemShardProof,
      ((shards.map (shardToCompressedHeader dp)).map ShardCompressedHeader.registration) =
        shards.map HemShardProof.registration
  | [] => rfl
  | _ :: rest => congrArg (_ :: ·) (map_reg_of_headers dp rest)

private theorem map_sid_of_headers (dp : SuccinctAggregateProof → List UInt8) :
    ∀ shards : List HemShardProof,
      ((shards.map (shardToCompressedHeader dp)).map (·.shardId)) = hierarchicalShardIds shards
  | [] => rfl
  | _ :: rest => congrArg (_ :: ·) (map_sid_of_headers dp rest)

private theorem flat_com_of_headers (dp : SuccinctAggregateProof → List UInt8) :
    ∀ shards : List HemShardProof,
      headerCommitteeFlat (shards.map (shardToCompressedHeader dp)) = hierarchicalCommittee shards
  | [] => rfl
  | _ :: rest => congrArg (_ ++ ·) (flat_com_of_headers dp rest)

/-- Constructive (`0 Classical.choice`) recursive witness extractor composing the outer
    `bciksJohnsonQrom128` `Hem` extractor with the `M`-shard `extractHierarchicalHemQuorums` tree. -/
def extractSuccinctRecursiveHem (H : Hash)
    (outerArith : RowArithmetization) (outerDom : WhirDomain)
    (innerArith : RowArithmetization) (innerDom : WhirDomain)
    (registryDigest epochFloor msg : List UInt8)
    (registry : List ShardRegistration)
    (hReg : H (encodeRegistry registry) = registryDigest)
    (cert : SuccinctOuterHemCertificate)
    (env : SuccinctRecursiveHemEnv H outerArith outerDom innerArith innerDom epochFloor msg cert)
    (hAccept : verifySuccinctRecursiveHem H outerArith outerDom registryDigest epochFloor msg cert = true) :
    PSum (HierarchicalQuorumWitness epochFloor msg registry (env.innerEnvs.map (·.shard)))
      (PSum (HemShardBreak outerArith outerDom cert.outerProof env.outerView)
        (HemHierarchyBreak H innerArith innerDom env.innerEnvs)) :=
  have hF := verifySuccinctRecursiveHem_facts hAccept
  match succinct_aggregation_knowledge_soundness outerArith outerDom cert.outerInst env.outerLaw
      cert.outerProof cert.outerFs env.outerView hF.2.2.2.2.2.2.2.2 env.outerBound with
  | .inr outerBrk => .inr (.inl outerBrk)
  | .inl ⟨_, hOuterAct⟩ =>
    have hRel := env.outerRelationSound hOuterAct
    have hMapHdr : (env.innerEnvs.map (·.shard)).map (shardToCompressedHeader env.digestProof) =
        cert.headers := by
      rw [List.map_map]; exact hRel.1
    have hHierAcc :
        verifyHierarchicalHem H innerArith innerDom registryDigest epochFloor msg
          (env.innerEnvs.map (·.shard)) = true := by
      unfold verifyHierarchicalHem
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
      have hRegDig : H (encodeRegistry ((env.innerEnvs.map (·.shard)).map HemShardProof.registration)) =
          registryDigest := by
        rw [← map_reg_of_headers env.digestProof, hMapHdr]; exact hF.2.1
      have hSidNd : (hierarchicalShardIds (env.innerEnvs.map (·.shard))).Nodup := by
        rw [← map_sid_of_headers env.digestProof, hMapHdr]; exact hF.2.2.1
      have hComNd : (hierarchicalCommittee (env.innerEnvs.map (·.shard))).Nodup := by
        rw [← flat_com_of_headers env.digestProof, hMapHdr]; exact hF.2.2.2.1
      refine ⟨⟨⟨hRegDig, hSidNd⟩, hComNd⟩, ?_⟩
      intro s hsMem
      obtain ⟨e, heMem, rfl⟩ := List.mem_map.mp hsMem
      have hHdrMem : shardToCompressedHeader env.digestProof e.shard ∈ cert.headers := by
        rw [← hMapHdr]; exact List.mem_map.mpr ⟨e.shard, List.mem_map.mpr ⟨e, heMem, rfl⟩, rfl⟩
      have hQ := hF.2.2.2.2.1 _ hHdrMem
      unfold verifyHeaderQuorum at hQ
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hQ
      have hInner := hRel.2 e heMem
      unfold verifyHemShard
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨⟨hInner.1, hQ.1.1⟩, hQ.1.2⟩, hQ.2⟩, hInner.2⟩
    match extractHierarchicalHemQuorums H innerArith innerDom registryDigest epochFloor msg
        registry hReg env.innerEnvs hHierAcc with
    | .inl w => .inl w
    | .inr hierBrk => .inr (.inr hierBrk)

private theorem sumOver_const_le (m bound : Nat) (f : Nat → Nat)
    (hf : ∀ j, j < m → f j ≤ bound) :
    sumOver m f ≤ m * bound := by
  induction m with
  | zero => simp [sumOver]
  | succ m ih =>
    have ih' := ih (fun j hj => hf j (Nat.lt_succ_of_lt hj))
    have hm := hf m (Nat.lt_succ_self m)
    simp only [sumOver, Nat.succ_mul]
    omega

private theorem countTrue_or_le {α : Type} (f g : α → Bool) :
    ∀ xs : List α, countTrue (fun x => f x || g x) xs ≤ countTrue f xs + countTrue g xs
  | [] => by decide
  | x :: rest => by
    have ih := countTrue_or_le f g rest
    simp only [countTrue]
    cases f x <;> cases g x <;> simp <;> omega

/-- **Succinct Outer Recursive `Hem` Soundness Composition (`succinct_recursive_hem_soundness_composition`)**:
    Over any finite coin space `coins`, if `recBad ω` marks coins where `verifySuccinctRecursiveHem`
    accepts under `H (encodeRegistry (registry ω)) = registryDigest ω` without a valid
    `HierarchicalQuorumWitness` across all `M` shards, then:
    1. `countTrue recBad coins ≤ countTrue outerBad coins + countTrue colBad coins + Σ_{j < m} countTrue (shardBad j) coins`;
    2. When `countTrue outerBad coins ≤ epsOuter`, `countTrue colBad coins = 0` (collision-free transcript),
       and `∀ j < m, countTrue (shardBad j) coins ≤ epsHem`, total bad coins satisfy
       `countTrue recBad coins ≤ m * epsHem + epsOuter`! -/
theorem succinct_recursive_hem_soundness_composition {Ω : Type} (coins : List Ω) (m : Nat)
    (H : Hash) (outerArith : RowArithmetization) (outerDom : WhirDomain)
    (innerArith : RowArithmetization) (innerDom : WhirDomain)
    (registryDigest epochFloor msg : Ω → List UInt8)
    (registry : Ω → List ShardRegistration)
    (cert : Ω → SuccinctOuterHemCertificate)
    (env : (ω : Ω) → SuccinctRecursiveHemEnv H outerArith outerDom innerArith innerDom
      (epochFloor ω) (msg ω) (cert ω))
    (hLen : ∀ ω, (env ω).innerEnvs.length ≤ m)
    (recBad outerBad colBad : Ω → Bool) (shardBad : Nat → Ω → Bool)
    (hRec : ∀ ω, recBad ω = true →
      verifySuccinctRecursiveHem H outerArith outerDom (registryDigest ω) (epochFloor ω) (msg ω)
        (cert ω) = true ∧
      (HierarchicalQuorumWitness (epochFloor ω) (msg ω) (registry ω)
        ((env ω).innerEnvs.map (·.shard)) → False))
    (hRegAuth : ∀ ω, recBad ω = true → H (encodeRegistry (registry ω)) = registryDigest ω)
    (hOuter : ∀ ω, HemShardBreak outerArith outerDom (cert ω).outerProof (env ω).outerView →
      outerBad ω = true)
    (hCol : ∀ ω, HashCollisionWitness H → colBad ω = true)
    (hShard : ∀ ω (j : Fin (env ω).innerEnvs.length),
      HemShardBreak innerArith innerDom ((env ω).innerEnvs.get j).shard.proof
        ((env ω).innerEnvs.get j).view →
      shardBad j.val ω = true) :
    countTrue recBad coins ≤
      countTrue outerBad coins + countTrue colBad coins +
        sumOver m (fun j => countTrue (shardBad j) coins) ∧
    (∀ epsHem epsOuter : Nat,
      countTrue outerBad coins ≤ epsOuter →
      countTrue colBad coins = 0 →
      (∀ j, j < m → countTrue (shardBad j) coins ≤ epsHem) →
      countTrue recBad coins ≤ m * epsHem + epsOuter) := by
  let rootOrOuter : Ω → Bool := fun ω => outerBad ω || colBad ω
  have hUnion : countTrue recBad coins ≤
      countTrue rootOrOuter coins + sumOver m (fun j => countTrue (shardBad j) coins) := by
    apply countTrue_union_bound
    intro ω hb
    obtain ⟨hAcc, hNo⟩ := hRec ω hb
    match extractSuccinctRecursiveHem H outerArith outerDom innerArith innerDom
        (registryDigest ω) (epochFloor ω) (msg ω) (registry ω) (hRegAuth ω hb)
        (cert ω) (env ω) hAcc with
    | .inl w => exact (hNo w).elim
    | .inr (.inl oBrk) =>
      left
      dsimp only [rootOrOuter]
      rw [hOuter ω oBrk]
      rfl
    | .inr (.inr (.inl col)) =>
      left
      dsimp only [rootOrOuter]
      rw [hCol ω col, Bool.or_true]
    | .inr (.inr (.inr ⟨j, sBrk⟩)) =>
      exact .inr ⟨j.val, Nat.lt_of_lt_of_le j.isLt (hLen ω), hShard ω j sBrk⟩
  have hOrLe : countTrue rootOrOuter coins ≤ countTrue outerBad coins + countTrue colBad coins :=
    countTrue_or_le outerBad colBad coins
  have hMain : countTrue recBad coins ≤
      countTrue outerBad coins + countTrue colBad coins +
        sumOver m (fun j => countTrue (shardBad j) coins) := by omega
  refine ⟨hMain, ?_⟩
  intro epsHem epsOuter hO hC hS
  have hSum := sumOver_const_le m epsHem (fun j => countTrue (shardBad j) coins) hS
  omega

/-- Concrete accepting `SuccinctOuterHemCertificate` over the two `concreteHemShard` shards, using
    `poseidon2Hash32` and the honest `bciksJohnsonQrom128` WHIR prover. -/
def concreteSuccinctOuterCert : SuccinctOuterHemCertificate :=
  let headers := [concreteHemShard false, concreteHemShard true].map
    (shardToCompressedHeader (fun _ => [0x01]))
  let chainDig := poseidon2Hash32 (encodeCompressedHeaderChain headers)
  let outerMsg := succinctOuterBoundMessage concreteHemRegistryDigest [] [] chainDig
  let outerBundle := buildHonestSbox7WhirBundle Goldilocks.zero Goldilocks.zero Goldilocks.one outerMsg
  { headers := headers
    outerInst := rsSbox7Inst Goldilocks.zero Goldilocks.zero outerMsg
    outerProof := outerBundle.1
    outerFs := outerBundle.2.1 }

theorem inhabited_verifySuccinctRecursiveHem :
    verifySuccinctRecursiveHem poseidon2Hash32 concreteHemArith rsSbox7WhirDomain
      concreteHemRegistryDigest [] [] concreteSuccinctOuterCert = true ∧
    concreteSuccinctOuterCert.outerProof.agg.regime = .bciksJohnsonQrom128 := by
  have hIds : (concreteSuccinctOuterCert.headers.map (·.shardId)).Nodup := by decide
  have hCom : (headerCommitteeFlat concreteSuccinctOuterCert.headers).Nodup := by decide
  have hLen : 1 ≤ concreteSuccinctOuterCert.headers.length := by decide
  have hQ : concreteSuccinctOuterCert.headers.all verifyHeaderQuorum = true := by decide
  let chainDig := poseidon2Hash32 (encodeCompressedHeaderChain concreteSuccinctOuterCert.headers)
  let outerMsg := succinctOuterBoundMessage concreteHemRegistryDigest [] [] chainDig
  have hAcc := (honestSbox7WhirProof_accepts Goldilocks.zero Goldilocks.zero Goldilocks.one outerMsg).1
  have hArithEq : rsSbox7TraceArith Goldilocks.zero
      (CommRingOps.add (pow7Goldilocks Goldilocks.zero) Goldilocks.zero) = concreteHemArith := by
    have hz : CommRingOps.add (pow7Goldilocks Goldilocks.zero) Goldilocks.zero = Goldilocks.zero := by decide
    rw [hz]; rfl
  have hRoot0 : CommRingOps.add (pow7Goldilocks Goldilocks.zero) Goldilocks.zero = Goldilocks.zero := by decide
  rw [hArithEq, hRoot0] at hAcc
  have hMapReg : concreteSuccinctOuterCert.headers.map ShardCompressedHeader.registration =
      concreteHemRegistry :=
    map_reg_of_headers (fun _ => [0x01]) [concreteHemShard false, concreteHemShard true]
  have hDig : decide (poseidon2Hash32 (encodeRegistry
      (concreteSuccinctOuterCert.headers.map ShardCompressedHeader.registration)) =
      concreteHemRegistryDigest) = true := by
    rw [hMapReg]
    exact decide_eq_true rfl
  have hInstReg : decide (concreteSuccinctOuterCert.outerInst.regime = .bciksJohnsonQrom128) = true :=
    decide_eq_true rfl
  have hPrfReg : decide (concreteSuccinctOuterCert.outerProof.agg.regime = .bciksJohnsonQrom128) = true :=
    decide_eq_true rfl
  have hMsgEq : decide (concreteSuccinctOuterCert.outerInst.message = outerMsg) = true :=
    decide_eq_true rfl
  refine ⟨?_, rfl⟩
  unfold verifySuccinctRecursiveHem
  rw [decide_eq_true hLen, hDig, decide_eq_true hIds, decide_eq_true hCom, hQ,
      hInstReg, hPrfReg, hMsgEq]
  exact hAcc

/-- `#tooth` **Succinct Outer Recursive Regime Downgrade & Header-Chain Tamper Rejection**:
    1. Downgrading `outerInst.regime` to `.bciksJohnsonClassical128` causes `verifySuccinctRecursiveHem`
       to return `false`.
    2. Tampering `headers` to any `headers' ≠ cert.headers` on an accepting certificate forces either
       `verifySuccinctRecursiveHem ... { cert with headers := headers' } = false` or an explicit
       `HashCollisionWitness H` on `encodeCompressedHeaderChain`.
    3. On concrete `concreteSuccinctOuterCert` (with injective transcript hash `fun bs => bs`),
       mutating `childProofDigest` from `[0x01]` to `[0xFF]` causes `verifySuccinctRecursiveHem` to
       evaluate to `false`. -/
theorem tooth_succinctRecursiveHem_rejects_downgrade_and_tamper :
    (∀ H outerArith outerDom regDig ep msg (cert : SuccinctOuterHemCertificate),
      cert.outerInst.regime = .bciksJohnsonClassical128 →
      verifySuccinctRecursiveHem H outerArith outerDom regDig ep msg cert = false) ∧
    (∀ H outerArith outerDom regDig ep msg (cert : SuccinctOuterHemCertificate)
        (headers' : List ShardCompressedHeader),
      verifySuccinctRecursiveHem H outerArith outerDom regDig ep msg cert = true →
      headers' ≠ cert.headers →
      (HashCollisionWitness H → False) →
      verifySuccinctRecursiveHem H outerArith outerDom regDig ep msg
        { cert with headers := headers' } = false) ∧
    verifySuccinctRecursiveHem (fun bs => bs) concreteHemArith rsSbox7WhirDomain
      (encodeRegistry concreteHemRegistry) [] []
      { concreteSuccinctOuterCert with
        headers := concreteSuccinctOuterCert.headers.map
          (fun h => { h with childProofDigest := [0xFF] })
        outerInst := rsSbox7Inst Goldilocks.zero Goldilocks.zero
          (succinctOuterBoundMessage (encodeRegistry concreteHemRegistry) [] []
            (encodeCompressedHeaderChain concreteSuccinctOuterCert.headers)) } = false := by
  refine ⟨?_, ?_, ?_⟩
  · intro H outerArith outerDom regDig ep msg cert hCl
    apply Bool.eq_false_iff.mpr
    intro hAcc
    have hQr := (verifySuccinctRecursiveHem_facts hAcc).2.2.2.2.2.1
    rw [hCl] at hQr
    cases hQr
  · intro H outerArith outerDom regDig ep msg cert headers' hAcc hNe hNoCol
    apply Bool.eq_false_iff.mpr
    intro hAcc'
    have hMsg := (verifySuccinctRecursiveHem_facts hAcc).2.2.2.2.2.2.2.1
    have hMsg' := (verifySuccinctRecursiveHem_facts hAcc').2.2.2.2.2.2.2.1
    dsimp only at hMsg'
    rw [hMsg] at hMsg'
    have hDigEq := (succinctOuterBoundMessage_injective hMsg').2.2.2
    have hEncNe : encodeCompressedHeaderChain headers' ≠ encodeCompressedHeaderChain cert.headers := by
      intro hEncEq
      exact hNe (encodeCompressedHeaderChain_injective hEncEq)
    exact hNoCol ⟨encodeCompressedHeaderChain headers', encodeCompressedHeaderChain cert.headers,
      hEncNe, hDigEq.symm⟩
  · apply Bool.eq_false_iff.mpr
    intro hAcc'
    have hMsg' := (verifySuccinctRecursiveHem_facts hAcc').2.2.2.2.2.2.2.1
    dsimp only [rsSbox7Inst] at hMsg'
    have hEncEq := (succinctOuterBoundMessage_injective hMsg').2.2.2
    have hHdrEq := encodeCompressedHeaderChain_injective hEncEq
    have hHead : (concreteSuccinctOuterCert.headers.headD
        (shardToCompressedHeader (fun _ => [0x01]) (concreteHemShard false))).childProofDigest =
      ((concreteSuccinctOuterCert.headers.map
          (fun h => { h with childProofDigest := [0xFF] })).headD
        (shardToCompressedHeader (fun _ => [0x01]) (concreteHemShard false))).childProofDigest := by
      rw [hHdrEq]
    exact absurd hHead (by decide)

end Qsag

/- Audit every declaration owned by this module, including private certificate helpers, and
    include an explicit negative control confirming `Classical.choice` would be rejected. -/
open Lean Elab Command in
run_cmd do
  let allow (ax : Name) : Bool := ax == ``propext || ax == ``Quot.sound
  let neg ← Lean.collectAxioms ``Classical.choice
  if (neg.filter (!allow ·)).isEmpty then
    throwError "Axiom audit negative control failed: Classical.choice was not rejected"
  let privEnv := (← getEnv).setExporting false
  let mut checked : Nat := 0
  for (name, _) in privEnv.constants.toList do
    if !privEnv.isImportedConst name then
      let roots ← withEnv privEnv <| Lean.collectAxioms name
      let rejected := roots.filter (!allow ·)
      unless rejected.isEmpty do
        throwError "Rejected axioms in {name}: {rejected}"
      checked := checked + 1
  if checked == 0 then throwError "Empty module axiom audit"

#tooth_pair Qsag.poseidon2_interpolation_margin_needs_26 vs Qsag.tooth_poseidon2_margin_fails_at_rp17
#verify_inhabited Qsag.poseidon2_interpolation_margin_needs_26 Qsag.witness_poseidon2_margin
