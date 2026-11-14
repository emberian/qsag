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
4. **§4 Two-layer hierarchical `Hem`.** A root verifier (`verifyHierarchicalHem`) over `M` shard
   certificates, each a `verifySuccinctAggregate` proof on the shard-scoped message
   `shardBoundMessage shardId epochFloor msg`, with pairwise-distinct shard ids, pairwise-disjoint
   committees, and a hash commitment to the shard registry. `extractHierarchicalHemQuorums`
   returns one valid signature per active signer of every shard, or a registry hash collision, or
   a shard index with a single-layer break witness. `hierarchical_hem_soundness_error_bound` is
   the resulting union bound over a finite coin space, and
   `tooth_unscoped_shard_id_allows_quorum_replay_multiplication` replays one shard `M` times
   against a verifier without the namespace checks. The root verifies shard certificates
   directly; no verifier is arithmetized inside another proof.
5. **§5 Deployed width-12 inverses and exact M4 branch number.** Both actual linear layers and
   both round types have two-sided inverses. The deployed permutation is injective. Cofactor
   certificates for all 69 square minors establish the universal M4 branch bound, with a unit
   vector attaining five; `m4_mds_branch_number_eq_five` uses the `Fin 4 → Goldilocks` interface.
6. **§6 Actual four-lane differential and symbolic circuits.** The seventh-power S-box preserves
   differential support. Two consecutive four-lane rounds have at least five active S-boxes;
   eight such rounds have at least twenty. A polynomial-expression circuit evaluates to the
   actual four-lane round and has degree at most `7^r` after `r` rounds. These are component
   bounds, not a differential probability or interpolation-degree lower bound for width 12.
7. **§7 Concrete hierarchical certificates.** Two distinct singleton committees with threshold
   one use the honest two-stage WHIR prover and a Poseidon2 registry commitment. The concrete
   replay theorem has no accepting-certificate hypothesis. The example uses the field-based
   signature suite from `Aggregation`, not a claimed secure instantiation of that suite.
-/

public import Qsag.Goldilocks
import all Qsag.Goldilocks
public import Qsag.Poseidon2
import all Qsag.Poseidon2
public import Qsag.Aggregation
import all Qsag.Aggregation
import Lean

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

/-- Registry row: a shard id together with its custodian cluster's committee. -/
structure ShardRegistration where
  shardId : List UInt8
  committee : List PqPublicKey
  deriving DecidableEq

def HemShardProof.registration (s : HemShardProof) : ShardRegistration :=
  ⟨s.shardId, s.inst.committee⟩

def encodeRegistration (r : ShardRegistration) : List UInt8 :=
  encodeMultiFrame [r.shardId,
    encodeMultiFrame (r.committee.map fun pk => encodeMultiFrame [pk.pkSeed, pk.pkRoot])]

def encodeRegistry (rs : List ShardRegistration) : List UInt8 :=
  encodeMultiFrame (rs.map encodeRegistration)

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
  have hList := encodeMultiFrame_injective h
  simp only [List.cons.injEq, and_true] at hList
  cases a; cases b
  simp only at hList
  rw [hList.1, hList.2]

private theorem encodeRegistration_injective (a b : ShardRegistration)
    (h : encodeRegistration a = encodeRegistration b) : a = b := by
  have hList := encodeMultiFrame_injective h
  simp only [List.cons.injEq, and_true] at hList
  have hCom := map_inj_of_inj encodePk_injective (encodeMultiFrame_injective hList.2)
  cases a; cases b
  simp only at hList hCom
  rw [hList.1, hCom]

theorem encodeRegistry_injective {rs₁ rs₂ : List ShardRegistration}
    (h : encodeRegistry rs₁ = encodeRegistry rs₂) : rs₁ = rs₂ :=
  map_inj_of_inj encodeRegistration_injective (encodeMultiFrame_injective h)

/-- Two distinct registries under one digest are a concrete collision of `H`. -/
def registryCollision (H : Hash) {digest : List UInt8} {claimed registry : List ShardRegistration}
    (hClaimed : H (encodeRegistry claimed) = digest) (hReg : H (encodeRegistry registry) = digest)
    (hNe : claimed ≠ registry) : HashCollisionWitness H :=
  ⟨encodeRegistry claimed, encodeRegistry registry,
    fun h => hNe (encodeRegistry_injective h), hClaimed.trans hReg.symm⟩

/-- Per-shard check: shard-scoped message, threshold met by the bitmap, accepting certificate. -/
def verifyHemShard (arith : RowArithmetization) (dom : WhirDomain)
    (epochFloor msg : List UInt8) (s : HemShardProof) : Bool :=
  decide (s.inst.message = shardBoundMessage s.shardId epochFloor msg) &&
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

/-- Root verifier of the two-layer hierarchy: registry commitment, pairwise-distinct shard ids,
    pairwise-disjoint duplicate-free committees, and every shard certificate. -/
def verifyHierarchicalHem (H : Hash) (arith : RowArithmetization) (dom : WhirDomain)
    (registryDigest epochFloor msg : List UInt8) (shards : List HemShardProof) : Bool :=
  decide (H (encodeRegistry (shards.map HemShardProof.registration)) = registryDigest) &&
  decide ((hierarchicalShardIds shards).Nodup) &&
  decide ((hierarchicalCommittee shards).Nodup) &&
  shards.all (verifyHemShard arith dom epochFloor msg)

theorem verifyHemShard_facts {arith : RowArithmetization} {dom : WhirDomain}
    {epochFloor msg : List UInt8} {s : HemShardProof}
    (h : verifyHemShard arith dom epochFloor msg s = true) :
    s.inst.message = shardBoundMessage s.shardId epochFloor msg ∧
    s.threshold ≤ bitmapPopcountSpec s.proof.agg.bitmap ∧
    verifySuccinctAggregate arith dom s.inst s.proof s.fs = true := by
  unfold verifyHemShard at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

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
      e.shard.fs e.view hF.2.2 e.bound with
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

/-- Left outcome of the tree extractor: one valid signature per active slot of every shard, for
    exactly the registered committees. -/
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

theorem hierarchicalThresholdSum_le_claimedWeight {arith : RowArithmetization} {dom : WhirDomain}
    {epochFloor msg : List UInt8} :
    ∀ shards : List HemShardProof,
      (∀ s ∈ shards, verifyHemShard arith dom epochFloor msg s = true) →
      hierarchicalThresholdSum shards ≤ hierarchicalClaimedWeight shards
  | [], _ => Nat.le_refl _
  | s :: rest, h => by
    have hs := (verifyHemShard_facts (h s (List.mem_cons_self ..))).2.1
    have ih := hierarchicalThresholdSum_le_claimedWeight rest
      (fun s' hs' => h s' (List.mem_cons_of_mem _ hs'))
    simp only [hierarchicalThresholdSum, hierarchicalClaimedWeight]
    omega

/-- **Two-layer hierarchical knowledge soundness
    (`recursive_hem_two_layer_knowledge_soundness`)**: an accepting root verification against a
    committed registry yields signatures `sigs` with one entry per active slot, at least
    `Σ_j K_j` of them, under pairwise-distinct public keys taken from the registered committees;
    otherwise there is a registry hash collision or a shard index with a single-layer break. -/
theorem recursive_hem_two_layer_knowledge_soundness (H : Hash) (arith : RowArithmetization)
    (dom : WhirDomain) (registryDigest epochFloor msg : List UInt8)
    (registry : List ShardRegistration) (hReg : H (encodeRegistry registry) = registryDigest)
    (envs : List (HemShardEnv arith dom))
    (hAccept : verifyHierarchicalHem H arith dom registryDigest epochFloor msg
      (envs.map (·.shard)) = true) :
    (∃ sigs : List (ExtractedQuorumSig epochFloor msg),
      sigs.map (·.slot) = hierarchicalActiveSlots (envs.map (·.shard)) ∧
      sigs.length = hierarchicalClaimedWeight (envs.map (·.shard)) ∧
      hierarchicalThresholdSum (envs.map (·.shard)) ≤ sigs.length ∧
      (sigs.map (·.slot.pk)).Nodup ∧
      (envs.map (·.shard)).map HemShardProof.registration = registry) ∨
    Nonempty (HemHierarchyBreak H arith dom envs) := by
  have hF := verifyHierarchicalHem_facts hAccept
  match extractHierarchicalHemQuorums H arith dom registryDigest epochFloor msg registry hReg
      envs hAccept with
  | .inr brk => exact .inr ⟨brk⟩
  | .inl w =>
    refine .inl ⟨w.sigs, w.slots_eq, w.weight_eq, ?_, ?_, w.registry_eq⟩
    · rw [w.weight_eq]
      exact hierarchicalThresholdSum_le_claimedWeight _ hF.2.2.2
    · have hMap : w.sigs.map (·.slot.pk) = (w.sigs.map (·.slot)).map HemSlot.pk := by
        rw [List.map_map]; rfl
      rw [hMap, w.slots_eq]
      exact (hierarchicalActiveSlots_pk_sublist _).nodup hF.2.2.1

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
    coins where the root verifier accepts although no `HierarchicalQuorumWitness` exists, let
    `rootBad` mark every coin whose run opens the registry digest to a second registry, and let
    `shardBad j` mark every coin whose run contains a single-layer break at shard `j`. Then
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
    (hRoot : ∀ ω, ((envs ω).map (·.shard)).map HemShardProof.registration ≠ registry ω →
      rootBad ω = true)
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
    exact .inl (hRoot ω hEq)

/-! ### `#tooth`: without shard scoping one shard certificate is counted `m` times -/

/-- Root verifier with the shard-id and committee-disjointness checks removed. -/
def verifyHierarchicalHemUnscoped (arith : RowArithmetization) (dom : WhirDomain)
    (shards : List HemShardProof) : Bool :=
  shards.all fun s =>
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
    exact ⟨hF.2.1, hF.2.2⟩
  · rw [hierarchicalClaimedWeight_replicate]
    exact Nat.mul_le_mul_left m hF.2.1
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

/-! ## 7. Concrete accepting hierarchical certificates -/

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

def concreteHemRegistryDigest : List UInt8 :=
  poseidon2Hash32 (encodeRegistry ([concreteHemShard false, concreteHemShard true].map
    HemShardProof.registration))

theorem concreteHemShard_accepts (second : Bool) :
    verifyHemShard concreteHemArith rsSbox7WhirDomain [] [] (concreteHemShard second) = true := by
  have hAcc := (honestSbox7WhirProof_accepts
    (if second then Goldilocks.one else Goldilocks.zero)
    Goldilocks.zero Goldilocks.one
    (shardBoundMessage [if second then 1 else 0] [] [])).1
  cases second <;>
    (change true && true && _ = true
     simpa only [Bool.true_and] using hAcc)

/-- A root certificate with two distinct shard ids, two distinct public keys, and two active
    signers. Its registry commitment is computed by the deployed Poseidon2 hash. -/
theorem inhabited_verifyHierarchicalHem_two_shards :
    verifyHierarchicalHem poseidon2Hash32 concreteHemArith rsSbox7WhirDomain
      concreteHemRegistryDigest [] [] [concreteHemShard false, concreteHemShard true] = true ∧
    hierarchicalClaimedWeight [concreteHemShard false, concreteHemShard true] = 2 ∧
    hierarchicalThresholdSum [concreteHemShard false, concreteHemShard true] = 2 := by
  refine ⟨?_, rfl, rfl⟩
  unfold verifyHierarchicalHem concreteHemRegistryDigest
  have hIds : (hierarchicalShardIds [concreteHemShard false, concreteHemShard true]).Nodup := by
    decide
  have hKeys : (hierarchicalCommittee [concreteHemShard false, concreteHemShard true]).Nodup := by
    decide
  have hall : [concreteHemShard false, concreteHemShard true].all
      (verifyHemShard concreteHemArith rsSbox7WhirDomain [] []) = true := by
    simp only [List.all_cons, List.all_nil, concreteHemShard_accepts, Bool.and_self]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨rfl, hIds⟩, hKeys⟩, hall⟩

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

end Qsag

/- Audit every declaration owned by this module, including private certificate helpers.
    Imported proof dependencies are traversed transitively by the kernel axiom collector. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    if !env.isImportedConst name then
      let roots ← Lean.collectAxioms name
      let rejected := roots.filter fun ax => ax != ``propext && ax != ``Quot.sound
      unless rejected.isEmpty do
        throwError "Rejected axioms in {name}: {rejected}"
      checked := checked + 1
  if checked == 0 then throwError "Empty module axiom audit"
  logInfo m!"Module axiom audit: {checked} declarations; 0 rejected axioms"
