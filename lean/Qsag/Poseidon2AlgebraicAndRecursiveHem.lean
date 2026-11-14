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
-/

public import Qsag.Goldilocks
import all Qsag.Goldilocks
public import Qsag.Poseidon2
import all Qsag.Poseidon2
public import Qsag.Aggregation
import all Qsag.Aggregation
import Lean

import Qsag.Tactic.AssuranceKit

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
