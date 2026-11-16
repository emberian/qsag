module
public import Qsag.Math.Lattices
public import Qsag.Tactic.AssuranceKit
public import Qsag.Oracle.Keccak

/-
# Qsag.Protocol.Threshold.DensePcgTapLinearTests — linear tests of the deployed three-tap dense-PCG rows

`pcg_dense.rs` builds each output row of `H_lpn` from three masked SHAKE taps per GGM tree into
that tree's own prefix accumulator, and the receiver's choice bit is the XOR over the 64 trees
of `[tap₀ ≥ p*] ⊕ [tap₁ ≥ p*] ⊕ [tap₂ ≥ p*]` with one uniform punctured leaf `p*` per tree.
This module works from that counting model instead of supplied block rates:

1. `threeTap_weight`: the per-tree weight of a row, for any three taps.
2. `noiseSignedSum_eq`: for any linear test, the signed count over all regular-noise tuples is
   the product of the per-tree signed counts (the parity bias is that product over `N^T`).
   `regularRates_parityBias_eq` identifies it with the rate model of `GaussianHvzkAndDualLpn`.
3. `prodRow0_bias_bracket`: for the taps of row 0 reproduced from the production generator
   (session `00..1f`, sender 0, receiver 1, depth 15) the bias lies strictly between
   `2^-118` and `2^-117`. The balanced-block premise of
   `pcg_dense_dual_lpn_linear_bias_lt_two_neg_256` does not hold for this row. The tap values
   are an input here: SHAKE-256 is evaluated outside Lean.
4. `tree_second_moment`, `matrix_second_moment`: summed over all tap choices, the squared
   signed count of a test with `m` taps per tree is `(Σ_{p,p'} (N - 2|p - p'|)^m)^T`.
   `denseDepth15_single_row_second_moment` and `denseDepth15_single_row_markov` evaluate this at
   `N = 2^15`, `T = 64`, `m = 3`: mean squared bias below `2^-148`, and the fraction of tap
   choices with bias at least `2^-k` at most `2^(2k-148)`.
   `denseDepth15_tap_count_ge_four_second_moment` gives the same `2^-148` for every `m ≥ 4`,
   which covers the XOR of any fixed set of two or more rows.

The second-moment statements average over uniform independent taps. Applying them to SHAKE
output is a random-oracle assumption. They bound fixed linear tests of one row (`m = 3`) or a
fixed set of rows (`m = 3·rows`), not every distinguisher, and they are not a hardness claim
for dual-LPN decoding.
-/

public section
namespace Qsag
set_option autoImplicit false

/-! ## 1. Finite sums and the per-tree row weight -/

/-- Rust `tap >= p_star`. -/
def tapGe (tap p : Nat) : Bool := decide (p ≤ tap)

/-- Restriction to one tree of a test that XORs the given taps. -/
def tapFn : List Nat → Nat → Bool
  | [], _ => false
  | a :: r, p => Bool.xor (tapGe a p) (tapFn r p)

def bsign (b : Bool) : Int := if b then -1 else 1

def sumRange : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumRange n f + f n

def leafWeight : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | n + 1, f => leafWeight n f + (if f n then 1 else 0)

theorem tapGe_eq_accumulated_unit (tap p : Nat) :
    tapGe tap p = accPrefixXor (unitPunctureVec p) tap :=
  (accUnitPuncture_eq_stepIndicator p tap).symm

theorem bsign_xor (a b : Bool) : bsign (Bool.xor a b) = bsign a * bsign b := by
  cases a <;> cases b <;> rfl

theorem sumRange_congr {n : Nat} {f g : Nat → Int} (h : ∀ i, i < n → f i = g i) :
    sumRange n f = sumRange n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    unfold sumRange
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h k (Nat.lt_succ_self k)]

theorem sumRange_add (n : Nat) (f g : Nat → Int) :
    sumRange n (fun i => f i + g i) = sumRange n f + sumRange n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show sumRange k (fun i => f i + g i) + (f k + g k) = (sumRange k f + f k) + (sumRange k g + g k)
    rw [ih]; ac_rfl

theorem sumRange_mul_left (n : Nat) (c : Int) (f : Nat → Int) :
    sumRange n (fun i => c * f i) = c * sumRange n f := by
  induction n with
  | zero => exact (Int.mul_zero c).symm
  | succ k ih => unfold sumRange; rw [ih, Int.mul_add]

theorem sumRange_zero (n : Nat) : sumRange n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => unfold sumRange; rw [ih]; rfl

theorem sumRange_const (n : Nat) (c : Int) : sumRange n (fun _ => c) = (n : Int) * c := by
  induction n with
  | zero => exact (Int.zero_mul c).symm
  | succ k ih => unfold sumRange; rw [ih, Int.natCast_succ, Int.add_mul, Int.one_mul]

theorem sumRange_comm (n m : Nat) (f : Nat → Nat → Int) :
    sumRange n (fun i => sumRange m (fun j => f i j)) =
      sumRange m (fun j => sumRange n (fun i => f i j)) := by
  induction n with
  | zero => exact (sumRange_zero m).symm
  | succ k ih =>
    have hSplit : (fun j => sumRange (k + 1) (fun i => f i j)) =
        (fun j => sumRange k (fun i => f i j) + f k j) := rfl
    rw [hSplit, sumRange_add, ← ih]; rfl

theorem sumRange_le {n : Nat} {f g : Nat → Int} (h : ∀ i, f i ≤ g i) :
    sumRange n f ≤ sumRange n g := by
  induction n with
  | zero => exact Int.le_refl 0
  | succ k ih => unfold sumRange; exact Int.add_le_add ih (h k)

theorem sumRange_succ_front (n : Nat) (f : Nat → Int) :
    sumRange (n + 1) f = f 0 + sumRange n (fun i => f (i + 1)) := by
  induction n with
  | zero => unfold sumRange sumRange; omega
  | succ k ih =>
    have h1 : sumRange (k + 1 + 1) f = sumRange (k + 1) f + f (k + 1) := rfl
    have h2 : sumRange (k + 1) (fun i => f (i + 1)) = sumRange k (fun i => f (i + 1)) + f (k + 1) := rfl
    rw [h1, ih, h2]; omega

theorem sumRange_bsign (n : Nat) (g : Nat → Bool) :
    sumRange n (fun p => bsign (g p)) = (n : Int) - 2 * (leafWeight n g : Int) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show sumRange k (fun p => bsign (g p)) + bsign (g k) =
      ((k + 1 : Nat) : Int) - 2 * ((leafWeight k g + (if g k = true then 1 else 0) : Nat) : Int)
    rw [ih]
    cases hg : g k
    · have h1 : bsign false = 1 := rfl
      rw [h1]; simp only [Bool.false_eq_true, ite_false]; omega
    · have h1 : bsign true = -1 := rfl
      rw [h1]; simp only [ite_true]; omega

/-- Signed leaf count of one tree: `N - 2·weight`. -/
def treeSigned (N : Nat) (g : Nat → Bool) : Int := (N : Int) - 2 * (leafWeight N g : Int)

/-- Weight of a three-tap row on one tree: leaves at or below the smallest tap, plus leaves
strictly above the middle tap and at or below the largest. -/
def threeTapWeight (a b c : Nat) : Nat :=
  (min a (min b c) + 1) + (max a (max b c) - (a + b + c - min a (min b c) - max a (max b c)))

private theorem threeTap_prefix (a b c : Nat) : ∀ n : Nat,
    leafWeight n (tapFn [a, b, c]) =
      min n (min a (min b c) + 1) +
        (min n (max a (max b c) + 1) -
          min n (a + b + c - min a (min b c) - max a (max b c) + 1))
  | 0 => by unfold leafWeight; omega
  | n + 1 => by
    unfold leafWeight; rw [threeTap_prefix a b c n]
    simp only [tapFn, tapGe, Bool.xor_false]
    by_cases h1 : n ≤ a <;> by_cases h2 : n ≤ b <;> by_cases h3 : n ≤ c <;>
      simp only [h1, h2, h3, decide_true, decide_false, Bool.xor_true, Bool.xor_false,
        Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_true, ite_false] <;> omega

theorem threeTap_weight (N a b c : Nat) (ha : a < N) (hb : b < N) (hc : c < N) :
    leafWeight N (tapFn [a, b, c]) = threeTapWeight a b c := by
  rw [threeTap_prefix]; unfold threeTapWeight; omega

/-! ## 2. Exact signed count of a linear test over regular noise -/

/-- Enumerates every regular-noise tuple (one punctured leaf below `N` per tree) and adds the
sign of the test parity `acc ⊕ ⨁ₜ gₜ(pₜ)`. -/
def noiseSignedSum (N : Nat) : List (Nat → Bool) → Bool → Int
  | [], acc => bsign acc
  | g :: gs, acc => sumRange N (fun p => noiseSignedSum N gs (Bool.xor acc (g p)))

def biasProd (N : Nat) : List (Nat → Bool) → Int
  | [] => 1
  | g :: gs => treeSigned N g * biasProd N gs

theorem noiseSignedSum_eq (N : Nat) : ∀ (gs : List (Nat → Bool)) (acc : Bool),
    noiseSignedSum N gs acc = bsign acc * biasProd N gs
  | [], acc => (Int.mul_one _).symm
  | g :: gs, acc => by
    have hF : (fun p => noiseSignedSum N gs (Bool.xor acc (g p))) =
        (fun p => (bsign acc * biasProd N gs) * bsign (g p)) := by
      funext p; rw [noiseSignedSum_eq N gs, bsign_xor]; ac_rfl
    show sumRange N (fun p => noiseSignedSum N gs (Bool.xor acc (g p))) =
      bsign acc * (treeSigned N g * biasProd N gs)
    rw [hF, sumRange_mul_left, sumRange_bsign]; unfold treeSigned; ac_rfl

/-- The rate model of `GaussianHvzkAndDualLpn` has exactly this numerator and denominator when
its rates are the leaf weights of the per-tree test functions. -/
theorem regularRates_parityBias_eq : ∀ gs : List (Nat → Bool),
    (parityBias (regularBlockXorOneProb
        (gs.map (fun g => depth15TreeRate (leafWeight 32768 g))))).num = biasProd 32768 gs ∧
    (parityBias (regularBlockXorOneProb
        (gs.map (fun g => depth15TreeRate (leafWeight 32768 g))))).den = 32768 ^ gs.length
  | [] => by
    simp only [List.map_nil, regularBlockXorOneProb_nil, parityBias_num, parityBias_den]
    constructor <;> first | rfl | trivial
  | g :: gs => by
    have ih := regularRates_parityBias_eq gs
    rw [List.map_cons, regularBlockXorOneProb_cons, parityBias_xorStepProb, ExactRat.mul_num,
      ExactRat.mul_den, ih.1, ih.2, List.length_cons, Nat.pow_succ']
    simp only [parityBias_num, parityBias_den, depth15TreeRate_num, depth15TreeRate_den]
    constructor <;> first | rfl | trivial

/-! ## 3. Row 0 of a production matrix -/

/-- Unsigned bias numerator of a row given its three taps in each tree. -/
def rowBiasNat (N : Nat) : List (Nat × Nat × Nat) → Nat
  | [] => 1
  | t :: ts => ((N : Int) - 2 * (threeTapWeight t.1 t.2.1 t.2.2 : Int)).natAbs * rowBiasNat N ts

def rowTestFns (taps : List (Nat × Nat × Nat)) : List (Nat → Bool) :=
  taps.map (fun t => tapFn [t.1, t.2.1, t.2.2])

def tapsBelow (N : Nat) (taps : List (Nat × Nat × Nat)) : Bool :=
  taps.all (fun t => decide (t.1 < N) && decide (t.2.1 < N) && decide (t.2.2 < N))

theorem row_signed_count_natAbs (N : Nat) : ∀ (taps : List (Nat × Nat × Nat)),
    tapsBelow N taps = true →
    (noiseSignedSum N (rowTestFns taps) false).natAbs = rowBiasNat N taps
  | [], _ => rfl
  | t :: ts, h => by
    have hAll : (decide (t.1 < N) && decide (t.2.1 < N) && decide (t.2.2 < N)) = true ∧
        tapsBelow N ts = true := by
      unfold tapsBelow at h ⊢; rw [List.all_cons, Bool.and_eq_true] at h; exact h
    have hT := hAll.1
    rw [Bool.and_eq_true, Bool.and_eq_true] at hT
    have ih := row_signed_count_natAbs N ts hAll.2
    rw [noiseSignedSum_eq] at ih ⊢
    have hb : bsign false = 1 := rfl
    rw [hb, Int.one_mul] at ih ⊢
    have hCons : rowTestFns (t :: ts) = tapFn [t.1, t.2.1, t.2.2] :: rowTestFns ts := rfl
    rw [hCons]
    show (treeSigned N (tapFn [t.1, t.2.1, t.2.2]) * biasProd N (rowTestFns ts)).natAbs =
      ((N : Int) - 2 * (threeTapWeight t.1 t.2.1 t.2.2 : Int)).natAbs * rowBiasNat N ts
    unfold treeSigned
    rw [Int.natAbs_mul, ih, threeTap_weight N _ _ _ (of_decide_eq_true hT.1.1)
      (of_decide_eq_true hT.1.2) (of_decide_eq_true hT.2)]

/-- Row 0 taps of trees 0..63 from `BatchedTapGenerator` (session `00..1f`, sender 0,
receiver 1, depth 15), reproduced with `hashlib.shake_256`. -/
def prodRow0Taps : List (Nat × Nat × Nat) := [
  (21294, 8897, 6786), (28959, 27309, 27789), (29933, 21455, 13890), (2911, 4341, 28594),
  (22146, 20330, 25444), (6642, 32212, 559), (30691, 23070, 12567), (15957, 3236, 10576),
  (25329, 13937, 29430), (28420, 26068, 19290), (24981, 25590, 28227), (6055, 23153, 15500),
  (4759, 12931, 15757), (7500, 28443, 8415), (21284, 18701, 5877), (23772, 30491, 13210),
  (5573, 15008, 22926), (989, 15616, 27938), (10226, 25558, 31699), (9430, 11566, 23931),
  (27800, 10825, 24184), (14486, 11348, 835), (21940, 8040, 19776), (5884, 3847, 10883),
  (22127, 26317, 10766), (1004, 6269, 26243), (6808, 15671, 27917), (24398, 12260, 27282),
  (22707, 18717, 7), (13430, 13903, 24204), (29676, 2555, 8210), (5584, 16326, 1179),
  (2379, 24396, 14072), (15749, 11676, 5604), (24961, 13743, 13324), (5907, 17538, 12693),
  (14084, 4175, 19802), (18900, 25779, 11341), (26842, 23770, 146), (27561, 4303, 8460),
  (31872, 6855, 5957), (9897, 9041, 8576), (16099, 2648, 3309), (19463, 7644, 486),
  (21633, 25933, 31494), (212, 17911, 8815), (28062, 18634, 18572), (25951, 9770, 7205),
  (26978, 20744, 23304), (21575, 24252, 31309), (19738, 31952, 2650), (18485, 24387, 28924),
  (9370, 15993, 4163), (24203, 24147, 14193), (23994, 18341, 12260), (27776, 22429, 11775),
  (3480, 20177, 1391), (25935, 22509, 2203), (13000, 25159, 13085), (30269, 15692, 11451),
  (16408, 15963, 18928), (4142, 2581, 15835), (3791, 10913, 28019), (11823, 28796, 13636)]

theorem prodRow0_bias_bracket :
    prodRow0Taps.length = 64 ∧
    (noiseSignedSum 32768 (rowTestFns prodRow0Taps) false).natAbs = rowBiasNat 32768 prodRow0Taps ∧
    rowBiasNat 32768 prodRow0Taps * 2 ^ 117 < 32768 ^ 64 ∧
    32768 ^ 64 < rowBiasNat 32768 prodRow0Taps * 2 ^ 118 :=
  ⟨by decide +kernel, row_signed_count_natAbs 32768 prodRow0Taps (by decide +kernel),
   by decide +kernel, by decide +kernel⟩

/-- The balanced-block premise fails on that row: only three of its 64 trees are balanced. -/
theorem prodRow0_balanced_tree_count :
    (prodRow0Taps.filter (fun t =>
      decide (((32768 : Int) - 2 * (threeTapWeight t.1 t.2.1 t.2.2 : Int)).natAbs ≤ 2047))).length = 3 := by
  decide +kernel

/-! ## 4. Second moment over uniform taps -/

/-- Sum over all tap lists of length `m` with entries below `N`. -/
def tapsSum (N : Nat) : Nat → (List Nat → Int) → Int
  | 0, F => F []
  | m + 1, F => sumRange N (fun a => tapsSum N m (fun r => F (a :: r)))

def leafDist (p p' : Nat) : Nat := (p - p') + (p' - p)

def pairKernel (N p p' : Nat) : Int := (N : Int) - 2 * (leafDist p p' : Int)

def kernelPowSum (N m : Nat) : Int :=
  sumRange N (fun p => sumRange N (fun p' => pairKernel N p p' ^ m))

private theorem tapPair_prefix (p p' : Nat) : ∀ n : Nat,
    leafWeight n (fun a => Bool.xor (tapGe a p) (tapGe a p')) =
      min n (max p p') - min n (min p p')
  | 0 => by unfold leafWeight; omega
  | n + 1 => by
    unfold leafWeight; rw [tapPair_prefix p p' n]
    simp only [tapGe]
    by_cases h1 : p ≤ n <;> by_cases h2 : p' ≤ n <;>
      simp only [h1, h2, decide_true, decide_false, Bool.xor_true, Bool.xor_false,
        Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_true, ite_false] <;> omega

theorem tap_pair_kernel (N p p' : Nat) (hp : p < N) (hp' : p' < N) :
    sumRange N (fun a => bsign (tapGe a p) * bsign (tapGe a p')) = pairKernel N p p' := by
  have hF : (fun a => bsign (tapGe a p) * bsign (tapGe a p')) =
      (fun a => bsign (Bool.xor (tapGe a p) (tapGe a p'))) := by
    funext a; rw [bsign_xor]
  rw [hF, sumRange_bsign, tapPair_prefix]; unfold pairKernel leafDist; omega

theorem tapsSum_pair (N : Nat) : ∀ (m : Nat) (W : Nat → Nat → Int),
    tapsSum N m (fun taps => sumRange N (fun p => sumRange N (fun p' =>
      W p p' * (bsign (tapFn taps p) * bsign (tapFn taps p'))))) =
    sumRange N (fun p => sumRange N (fun p' => W p p' * pairKernel N p p' ^ m))
  | 0, W => by
    unfold tapsSum
    apply sumRange_congr; intro p _; apply sumRange_congr; intro p' _
    have hb : bsign (tapFn [] p) = 1 := rfl
    have hb' : bsign (tapFn [] p') = 1 := rfl
    rw [hb, hb', Int.pow_zero, Int.mul_one]
  | m + 1, W => by
    unfold tapsSum
    have hStep : ∀ a : Nat,
        tapsSum N m (fun r => sumRange N (fun p => sumRange N (fun p' =>
          W p p' * (bsign (tapFn (a :: r) p) * bsign (tapFn (a :: r) p'))))) =
        sumRange N (fun p => sumRange N (fun p' =>
          (W p p' * (bsign (tapGe a p) * bsign (tapGe a p'))) * pairKernel N p p' ^ m)) := by
      intro a
      rw [← tapsSum_pair N m (fun p p' => W p p' * (bsign (tapGe a p) * bsign (tapGe a p')))]
      congr 1; funext r; congr 1; funext p; congr 1; funext p'
      have e1 : tapFn (a :: r) p = Bool.xor (tapGe a p) (tapFn r p) := rfl
      have e2 : tapFn (a :: r) p' = Bool.xor (tapGe a p') (tapFn r p') := rfl
      rw [e1, e2, bsign_xor, bsign_xor]; ac_rfl
    rw [show (fun a => tapsSum N m (fun r => sumRange N (fun p => sumRange N (fun p' =>
          W p p' * (bsign (tapFn (a :: r) p) * bsign (tapFn (a :: r) p')))))) =
        (fun a => sumRange N (fun p => sumRange N (fun p' =>
          (W p p' * (bsign (tapGe a p) * bsign (tapGe a p'))) * pairKernel N p p' ^ m)))
      from funext hStep]
    rw [sumRange_comm]
    apply sumRange_congr; intro p hp
    rw [sumRange_comm]
    apply sumRange_congr; intro p' hp'
    have hF : (fun a => (W p p' * (bsign (tapGe a p) * bsign (tapGe a p'))) * pairKernel N p p' ^ m) =
        (fun a => (W p p' * pairKernel N p p' ^ m) * (bsign (tapGe a p) * bsign (tapGe a p'))) := by
      funext a; ac_rfl
    rw [hF, sumRange_mul_left, tap_pair_kernel N p p' hp hp', Int.pow_succ, Int.mul_assoc]

/-- Summed over all `m`-tap choices in one tree, the squared signed count is the kernel sum. -/
theorem tree_second_moment (N m : Nat) :
    tapsSum N m (fun taps => treeSigned N (tapFn taps) * treeSigned N (tapFn taps)) =
      kernelPowSum N m := by
  have hF : (fun taps => treeSigned N (tapFn taps) * treeSigned N (tapFn taps)) =
      (fun taps => sumRange N (fun p => sumRange N (fun p' =>
        1 * (bsign (tapFn taps p) * bsign (tapFn taps p'))))) := by
    funext taps
    have hInner : (fun p => sumRange N (fun p' => 1 * (bsign (tapFn taps p) * bsign (tapFn taps p')))) =
        (fun p => treeSigned N (tapFn taps) * bsign (tapFn taps p)) := by
      funext p
      have hI : (fun p' => 1 * (bsign (tapFn taps p) * bsign (tapFn taps p'))) =
          (fun p' => bsign (tapFn taps p) * bsign (tapFn taps p')) := by
        funext p'; rw [Int.one_mul]
      rw [hI, sumRange_mul_left, sumRange_bsign]; unfold treeSigned; ac_rfl
    rw [hInner, sumRange_mul_left, sumRange_bsign]; rfl
  rw [hF, tapsSum_pair]; unfold kernelPowSum
  apply sumRange_congr; intro p _; apply sumRange_congr; intro p' _; rw [Int.one_mul]

theorem tapsSum_mul_right (N : Nat) (c : Int) : ∀ (m : Nat) (F : List Nat → Int),
    tapsSum N m (fun t => F t * c) = tapsSum N m F * c
  | 0, F => rfl
  | m + 1, F => by
    unfold tapsSum
    rw [show (fun a => tapsSum N m (fun r => F (a :: r) * c)) =
        (fun a => c * tapsSum N m (fun r => F (a :: r))) from
      funext fun a => by rw [tapsSum_mul_right N c m (fun r => F (a :: r)), Int.mul_comm]]
    rw [sumRange_mul_left, Int.mul_comm]

theorem tapsSum_le (N : Nat) : ∀ (m : Nat) (F G : List Nat → Int), (∀ t, F t ≤ G t) →
    tapsSum N m F ≤ tapsSum N m G
  | 0, _, _, h => h []
  | m + 1, F, G, h => by
    unfold tapsSum
    exact sumRange_le (fun a => tapsSum_le N m _ _ (fun r => h (a :: r)))

theorem tapsSum_const (N : Nat) (c : Int) : ∀ m : Nat,
    tapsSum N m (fun _ => c) = ((N ^ m : Nat) : Int) * c
  | 0 => by unfold tapsSum; rw [Nat.pow_zero, Int.natCast_one, Int.one_mul]
  | m + 1 => by
    unfold tapsSum
    rw [show (fun a : Nat => tapsSum N m (fun _ => c)) = (fun _ => ((N ^ m : Nat) : Int) * c) from
      funext fun _ => tapsSum_const N c m]
    rw [sumRange_const, Nat.pow_succ, Int.natCast_mul]; ac_rfl

/-- Sum over all matrices rows with `m` taps in each of `T` trees; `F` receives the per-tree
test functions. -/
def matrixSum (N m : Nat) : Nat → (List (Nat → Bool) → Int) → Int
  | 0, F => F []
  | T + 1, F => tapsSum N m (fun taps => matrixSum N m T (fun gs => F (tapFn taps :: gs)))

theorem matrixSum_mul_left (N m : Nat) : ∀ (T : Nat) (c : Int) (F : List (Nat → Bool) → Int),
    matrixSum N m T (fun gs => c * F gs) = c * matrixSum N m T F
  | 0, _, _ => rfl
  | T + 1, c, F => by
    unfold matrixSum
    rw [show (fun taps => matrixSum N m T (fun gs => c * F (tapFn taps :: gs))) =
        (fun taps => matrixSum N m T (fun gs => F (tapFn taps :: gs)) * c) from
      funext fun taps => by
        rw [matrixSum_mul_left N m T c (fun gs => F (tapFn taps :: gs)), Int.mul_comm]]
    rw [tapsSum_mul_right, Int.mul_comm]

theorem matrixSum_le (N m : Nat) : ∀ (T : Nat) (F G : List (Nat → Bool) → Int),
    (∀ gs, F gs ≤ G gs) → matrixSum N m T F ≤ matrixSum N m T G
  | 0, _, _, h => h []
  | T + 1, F, G, h => by
    unfold matrixSum
    exact tapsSum_le N m _ _ (fun taps => matrixSum_le N m T _ _ (fun gs => h (tapFn taps :: gs)))

theorem matrixSum_const (N m : Nat) (c : Int) : ∀ T : Nat,
    matrixSum N m T (fun _ => c) = (((N ^ m) ^ T : Nat) : Int) * c
  | 0 => by unfold matrixSum; rw [Nat.pow_zero, Int.natCast_one, Int.one_mul]
  | T + 1 => by
    unfold matrixSum
    rw [show (fun taps : List Nat => matrixSum N m T (fun _ => c)) =
        (fun _ => (((N ^ m) ^ T : Nat) : Int) * c) from funext fun _ => matrixSum_const N m c T]
    rw [tapsSum_const, Nat.pow_succ, Int.natCast_mul]; ac_rfl

/-- Summed over every choice of `m` taps in each of `T` trees, the squared signed count of the
regular-noise test is the `T`-th power of the per-tree kernel sum. -/
theorem matrix_second_moment (N m : Nat) : ∀ T : Nat,
    matrixSum N m T (fun gs => noiseSignedSum N gs false * noiseSignedSum N gs false) =
      kernelPowSum N m ^ T
  | 0 => by rw [Int.pow_zero]; rfl
  | T + 1 => by
    unfold matrixSum
    have hInner : ∀ taps : List Nat,
        matrixSum N m T (fun gs => noiseSignedSum N (tapFn taps :: gs) false *
          noiseSignedSum N (tapFn taps :: gs) false) =
        (treeSigned N (tapFn taps) * treeSigned N (tapFn taps)) * kernelPowSum N m ^ T := by
      intro taps
      rw [← matrix_second_moment N m T, ← matrixSum_mul_left]
      congr 1; funext gs
      rw [noiseSignedSum_eq, noiseSignedSum_eq]
      have hb : bsign false = 1 := rfl
      have hc : biasProd N (tapFn taps :: gs) = treeSigned N (tapFn taps) * biasProd N gs := rfl
      rw [hb, Int.one_mul, Int.one_mul, hc]; ac_rfl
    rw [show (fun taps => matrixSum N m T (fun gs => noiseSignedSum N (tapFn taps :: gs) false *
          noiseSignedSum N (tapFn taps :: gs) false)) =
        (fun taps => (treeSigned N (tapFn taps) * treeSigned N (tapFn taps)) * kernelPowSum N m ^ T)
      from funext hInner]
    rw [tapsSum_mul_right, tree_second_moment, Int.pow_succ, Int.mul_comm]

private theorem int_mul_self_nonneg (x : Int) : 0 ≤ x * x := by
  rcases Int.le_total 0 x with h | h
  · exact Int.mul_nonneg h h
  · have h' : 0 ≤ -x := Int.neg_nonneg_of_nonpos h
    rw [← Int.neg_mul_neg]; exact Int.mul_nonneg h' h'

/-- Number of tap choices whose squared signed count reaches `tau`. -/
def largeBiasCount (N m T : Nat) (tau : Int) : Int :=
  matrixSum N m T (fun gs =>
    if tau ≤ noiseSignedSum N gs false * noiseSignedSum N gs false then 1 else 0)

theorem largeBiasCount_markov (N m T : Nat) (tau : Int) :
    tau * largeBiasCount N m T tau ≤ kernelPowSum N m ^ T := by
  unfold largeBiasCount
  rw [← matrixSum_mul_left, ← matrix_second_moment N m T]
  apply matrixSum_le; intro gs
  by_cases h : tau ≤ noiseSignedSum N gs false * noiseSignedSum N gs false
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), Int.mul_one]; exact h
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), Int.mul_zero]; exact int_mul_self_nonneg _

/-! ## 5. Evaluating the kernel sum -/

private theorem sumRange_reverse : ∀ (n : Nat) (h : Nat → Int),
    sumRange n (fun p => h (n - p)) = sumRange n (fun d => h (d + 1))
  | 0, _ => rfl
  | n + 1, h => by
    rw [sumRange_succ_front (n := n) (f := fun d => h (d + 1))]
    have hL : sumRange (n + 1) (fun p => h (n + 1 - p)) =
        sumRange n (fun p => h (n + 1 - p)) + h (n + 1 - n) := rfl
    rw [hL, sumRange_congr (g := fun p => (fun d => h (d + 1)) (n - p))
      (fun p hp => by show h (n + 1 - p) = h (n - p + 1); rw [Nat.sub_add_comm (Nat.le_of_lt hp)]),
      sumRange_reverse n (fun d => h (d + 1)), Nat.add_sub_cancel_left]
    show sumRange n (fun d => h (d + 1 + 1)) + h 1 = h (0 + 1) + sumRange n (fun i => h (i + 1 + 1))
    rw [Nat.zero_add, Int.add_comm]

/-- Double sum of a function of the leaf distance, one row and column at a time. -/
private theorem distSum_succ (h : Nat → Int) (n : Nat) :
    sumRange (n + 1) (fun p => sumRange (n + 1) (fun p' => h (leafDist p p'))) =
      sumRange n (fun p => sumRange n (fun p' => h (leafDist p p'))) +
        (2 * sumRange n (fun d => h (d + 1)) + h 0) := by
  have hOuter : sumRange (n + 1) (fun p => sumRange (n + 1) (fun p' => h (leafDist p p'))) =
      sumRange n (fun p => sumRange n (fun p' => h (leafDist p p')) + h (leafDist p n)) +
        (sumRange n (fun p' => h (leafDist n p')) + h (leafDist n n)) := rfl
  have hCol : sumRange n (fun p => h (leafDist p n)) = sumRange n (fun d => h (d + 1)) := by
    rw [← sumRange_reverse n h]
    exact sumRange_congr (fun p hp => by
      show h (leafDist p n) = h (n - p)
      unfold leafDist; rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt hp), Nat.zero_add])
  have hRow : sumRange n (fun p' => h (leafDist n p')) = sumRange n (fun d => h (d + 1)) := by
    rw [← sumRange_reverse n h]
    exact sumRange_congr (fun p hp => by
      show h (leafDist n p) = h (n - p)
      unfold leafDist; rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt hp), Nat.add_zero])
  have hDiag : leafDist n n = 0 := by unfold leafDist; omega
  rw [hOuter, sumRange_add, hCol, hRow, hDiag]; omega

private theorem weighted_prefix (g : Nat → Int) : ∀ n : Nat,
    sumRange n (fun k => sumRange k g) = sumRange n (fun d => ((n : Int) - 1 - (d : Int)) * g d)
  | 0 => rfl
  | n + 1 => by
    have hL : sumRange (n + 1) (fun k => sumRange k g) =
        sumRange n (fun k => sumRange k g) + sumRange n g := rfl
    have hR : sumRange (n + 1) (fun d => (((n + 1 : Nat) : Int) - 1 - (d : Int)) * g d) =
        sumRange n (fun d => (((n + 1 : Nat) : Int) - 1 - (d : Int)) * g d) +
          (((n + 1 : Nat) : Int) - 1 - (n : Int)) * g n := rfl
    have hTerm : (fun d : Nat => (((n + 1 : Nat) : Int) - 1 - (d : Int)) * g d) =
        (fun d : Nat => ((n : Int) - 1 - (d : Int)) * g d + g d) := by
      funext d
      rw [show (((n + 1 : Nat) : Int) - 1 - (d : Int)) = ((n : Int) - 1 - (d : Int)) + 1 from by omega,
        Int.add_mul, Int.one_mul]
    rw [hL, hR, hTerm, sumRange_add, weighted_prefix g n,
      show (((n + 1 : Nat) : Int) - 1 - (n : Int)) = 0 from by omega, Int.zero_mul, Int.add_zero]

private theorem distSum_closed (h : Nat → Int) : ∀ n : Nat,
    sumRange n (fun p => sumRange n (fun p' => h (leafDist p p'))) =
      (n : Int) * h 0 + 2 * sumRange n (fun k => sumRange k (fun d => h (d + 1)))
  | 0 => by
    show (0 : Int) = ((0 : Nat) : Int) * h 0 + 2 * 0
    rw [Int.natCast_zero, Int.zero_mul]; rfl
  | n + 1 => by
    have hS : sumRange (n + 1) (fun k => sumRange k (fun d => h (d + 1))) =
        sumRange n (fun k => sumRange k (fun d => h (d + 1))) + sumRange n (fun d => h (d + 1)) := rfl
    rw [distSum_succ, distSum_closed h n, hS, Int.natCast_succ, Int.add_mul, Int.one_mul, Int.mul_add]
    omega

theorem kernelPowSum_closed (N m : Nat) :
    kernelPowSum N m = (N : Int) * (N : Int) ^ m +
      2 * sumRange N (fun d => ((N : Int) - 1 - (d : Int)) * ((N : Int) - 2 * ((d + 1 : Nat) : Int)) ^ m) := by
  have h := distSum_closed (fun d => ((N : Int) - 2 * (d : Int)) ^ m) N
  rw [weighted_prefix] at h
  have h0 : ((N : Int) - 2 * ((0 : Nat) : Int)) = (N : Int) := by omega
  unfold kernelPowSum pairKernel
  rw [h, h0]

/-- Balanced binary evaluation of `Σ_{i < 2^k} f (lo + i)`. -/
def dcSum : Nat → Nat → (Nat → Int) → Int
  | 0, lo, f => f lo
  | k + 1, lo, f => dcSum k lo f + dcSum k (lo + 2 ^ k) f

private theorem sumRange_append (f : Nat → Int) (a : Nat) : ∀ b : Nat,
    sumRange (a + b) f = sumRange a f + sumRange b (fun i => f (a + i))
  | 0 => (Int.add_zero _).symm
  | b + 1 => by
    have h1 : sumRange (a + (b + 1)) f = sumRange (a + b) f + f (a + b) := rfl
    have h2 : sumRange (b + 1) (fun i => f (a + i)) = sumRange b (fun i => f (a + i)) + f (a + b) := rfl
    rw [h1, h2, sumRange_append f a b, Int.add_assoc]

theorem dcSum_eq (f : Nat → Int) : ∀ (k lo : Nat),
    dcSum k lo f = sumRange (2 ^ k) (fun i => f (lo + i))
  | 0, lo => by
    show f lo = 0 + f (lo + 0)
    rw [Nat.add_zero, Int.zero_add]
  | k + 1, lo => by
    unfold dcSum
    rw [dcSum_eq f k lo, dcSum_eq f k (lo + 2 ^ k), Nat.pow_succ, Nat.mul_two,
      sumRange_append (fun i => f (lo + i)) (2 ^ k) (2 ^ k)]
    congr 1; apply sumRange_congr; intro i _; show f (lo + 2 ^ k + i) = f (lo + (2 ^ k + i))
    rw [Nat.add_assoc]

theorem dcSum_zero_eq (f : Nat → Int) (k : Nat) : dcSum k 0 f = sumRange (2 ^ k) f := by
  rw [dcSum_eq]
  exact sumRange_congr (fun i _ => by show f (0 + i) = f i; rw [Nat.zero_add])

/-- The kernel sum at `N = 2^k` in the form the kernel evaluates. -/
theorem kernelPowSum_pow2 (k m : Nat) :
    kernelPowSum (2 ^ k) m = ((2 ^ k : Nat) : Int) * ((2 ^ k : Nat) : Int) ^ m +
      2 * dcSum k 0 (fun d => (((2 ^ k : Nat) : Int) - 1 - (d : Int)) *
        (((2 ^ k : Nat) : Int) - 2 * ((d + 1 : Nat) : Int)) ^ m) := by
  rw [kernelPowSum_closed, dcSum_zero_eq]

private theorem kernelPowSum_depth15_three_aux :
    kernelPowSum (2 ^ 15) 3 = 7555786419503928442880 := by
  rw [kernelPowSum_pow2]; decide +kernel

private theorem kernelPowSum_depth15_six_aux :
    kernelPowSum (2 ^ 15) 6 = 189889716159439485911132785856217088 := by
  rw [kernelPowSum_pow2]; decide +kernel

theorem kernelPowSum_depth15_three : kernelPowSum 32768 3 = 7555786419503928442880 :=
  kernelPowSum_depth15_three_aux

theorem kernelPowSum_depth15_six :
    kernelPowSum 32768 6 = 189889716159439485911132785856217088 :=
  kernelPowSum_depth15_six_aux

/-- Mean squared bias of one row over uniform taps is below `2^-148`: the sum over all
`(2^15)^(3·64)` tap choices of the squared signed count, against `(2^15)^(2·64)` per choice. -/
theorem denseDepth15_single_row_second_moment :
    matrixSum 32768 3 64 (fun gs => noiseSignedSum 32768 gs false * noiseSignedSum 32768 gs false) *
        2 ^ 148 ≤ (((32768 ^ 3) ^ 64 : Nat) : Int) * (32768 ^ 64) ^ 2 := by
  rw [matrix_second_moment, kernelPowSum_depth15_three]; decide +kernel

/-- The same for a test that XORs two rows (six taps per tree): below `2^-179`. -/
theorem denseDepth15_two_row_second_moment :
    matrixSum 32768 6 64 (fun gs => noiseSignedSum 32768 gs false * noiseSignedSum 32768 gs false) *
        2 ^ 179 ≤ (((32768 ^ 6) ^ 64 : Nat) : Int) * (32768 ^ 64) ^ 2 := by
  rw [matrix_second_moment, kernelPowSum_depth15_six]; decide +kernel

/-! ### Every tap count at least four -/

theorem sumRange_le_of_lt {n : Nat} {f g : Nat → Int} (h : ∀ i, i < n → f i ≤ g i) :
    sumRange n f ≤ sumRange n g := by
  induction n with
  | zero => exact Int.le_refl 0
  | succ k ih =>
    show sumRange k f + f k ≤ sumRange k g + g k
    exact Int.add_le_add (ih (fun i hi => h i (Nat.lt_succ_of_lt hi))) (h k (Nat.lt_succ_self k))

private theorem natCast_natAbs_pow_four (x : Int) : ((x.natAbs : Nat) : Int) ^ 4 = x ^ 4 := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg x
  · rw [Int.natAbs_natCast]
  · rw [Int.natAbs_neg, Int.natAbs_natCast]
    simp only [Int.pow_succ, Int.pow_zero, Int.one_mul, Int.mul_neg, Int.neg_mul, Int.neg_neg]

private theorem pow_tail_le (x : Int) (N k : Nat) (h : x.natAbs ≤ N) :
    x ^ (4 + k) ≤ (N : Int) ^ k * x ^ 4 := by
  have hNat : (x ^ (4 + k)).natAbs ≤ N ^ k * x.natAbs ^ 4 := by
    rw [Int.natAbs_pow, Nat.pow_add, Nat.mul_comm]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h k)
  have hCast : ((N ^ k * x.natAbs ^ 4 : Nat) : Int) = (N : Int) ^ k * x ^ 4 := by
    rw [Int.natCast_mul, Int.natCast_pow, Int.natCast_pow, natCast_natAbs_pow_four]
  rw [← hCast]
  generalize x ^ (4 + k) = a at hNat
  generalize N ^ k * x.natAbs ^ 4 = M at hNat
  omega

theorem kernelPowSum_tail_le (N k : Nat) :
    kernelPowSum N (4 + k) ≤ (N : Int) ^ k * kernelPowSum N 4 := by
  unfold kernelPowSum
  rw [← sumRange_mul_left]
  apply sumRange_le_of_lt; intro p hp
  rw [← sumRange_mul_left]
  apply sumRange_le_of_lt; intro p' hp'
  exact pow_tail_le _ N k (by unfold pairKernel leafDist; omega)

theorem kernelPowSum_nonneg (N m : Nat) : 0 ≤ kernelPowSum N m := by
  rw [← tree_second_moment]
  have h := tapsSum_le N m (fun _ => 0)
    (fun taps => treeSigned N (tapFn taps) * treeSigned N (tapFn taps))
    (fun t => int_mul_self_nonneg _)
  rw [tapsSum_const, Int.mul_zero] at h; exact h

private theorem int_pow_le_pow_left {a b : Int} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∀ n : Nat, a ^ n ≤ b ^ n ∧ 0 ≤ a ^ n
  | 0 => by rw [Int.pow_zero, Int.pow_zero]; exact ⟨Int.le_refl 1, by decide⟩
  | n + 1 => by
    have ih := int_pow_le_pow_left ha hab n
    rw [Int.pow_succ, Int.pow_succ]
    exact ⟨Int.mul_le_mul ih.1 hab ha (Int.le_trans ih.2 ih.1), Int.mul_nonneg ih.2 ha⟩

private theorem kernelPowSum_depth15_four_aux :
    kernelPowSum (2 ^ 15) 4 = 247588009394304727216291840 := by
  rw [kernelPowSum_pow2]; decide +kernel

theorem kernelPowSum_depth15_four : kernelPowSum 32768 4 = 247588009394304727216291840 :=
  kernelPowSum_depth15_four_aux

/-- For every tap count `4 + k` per tree (in particular `3·r` for any `r ≥ 2` combined rows),
the mean squared bias over uniform taps is below `2^-148`. There are `(32768^k)^64 · 2^3840`
tap choices and `2^1920` squared noise tuples per choice. -/
theorem denseDepth15_tap_count_ge_four_second_moment (k : Nat) :
    matrixSum 32768 (4 + k) 64
        (fun gs => noiseSignedSum 32768 gs false * noiseSignedSum 32768 gs false) * 2 ^ 148 ≤
      ((32768 : Int) ^ k) ^ 64 * 2 ^ 5760 := by
  rw [matrix_second_moment]
  have hK := kernelPowSum_tail_le 32768 k
  rw [kernelPowSum_depth15_four] at hK
  have hPow := (int_pow_le_pow_left (kernelPowSum_nonneg 32768 (4 + k)) hK 64).1
  have hNum : (247588009394304727216291840 : Int) ^ 64 * 2 ^ 148 ≤ 2 ^ 5760 := by decide +kernel
  have hN : ((32768 : Nat) : Int) = 32768 := rfl
  rw [hN, Int.mul_pow] at hPow
  have hTwo : (0 : Int) ≤ 2 ^ 148 := Int.le_of_lt (Int.pow_pos (by decide : (0 : Int) < 2))
  have hBase : (0 : Int) ≤ (32768 ^ k) ^ 64 :=
    Int.le_of_lt (Int.pow_pos (Int.pow_pos (by decide : (0 : Int) < 32768)))
  refine Int.le_trans (Int.mul_le_mul_of_nonneg_right hPow hTwo) ?_
  rw [Int.mul_assoc]
  exact Int.mul_le_mul_of_nonneg_left hNum hBase

/-- At most a `2^(2k-148)` fraction of the `2^2880` single-row tap choices has bias at least
`2^-k` (squared signed count at least `2^(1920-2k)`). -/
theorem denseDepth15_single_row_markov (k : Nat) (hk : k ≤ 960) :
    largeBiasCount 32768 3 64 (2 ^ (1920 - 2 * k)) * 2 ^ 148 ≤ 2 ^ (2 * k) * 2 ^ 2880 := by
  have hM := largeBiasCount_markov 32768 3 64 (2 ^ (1920 - 2 * k))
  rw [kernelPowSum_depth15_three] at hM
  have hBound : (7555786419503928442880 : Int) ^ 64 * 2 ^ 148 ≤ 2 ^ 4800 := by decide +kernel
  have hPos : (0 : Int) < 2 ^ (1920 - 2 * k) := Int.pow_pos (by decide : (0 : Int) < 2)
  have hSplit : (2 : Int) ^ 4800 = 2 ^ (1920 - 2 * k) * (2 ^ (2 * k) * 2 ^ 2880) := by
    rw [← Int.pow_add, ← Int.pow_add]
    exact congrArg (fun e : Nat => (2 : Int) ^ e) (by omega : 4800 = 1920 - 2 * k + (2 * k + 2880))
  have hChain : 2 ^ (1920 - 2 * k) * (largeBiasCount 32768 3 64 (2 ^ (1920 - 2 * k)) * 2 ^ 148) ≤
      2 ^ (1920 - 2 * k) * (2 ^ (2 * k) * 2 ^ 2880) := by
    rw [← hSplit, ← Int.mul_assoc]
    exact Int.le_trans (Int.mul_le_mul_of_nonneg_right hM (Int.le_of_lt (Int.pow_pos (by decide : (0 : Int) < 2)))) hBound
  exact Int.le_of_mul_le_mul_left hChain hPos

/-! ## 6. Small exhaustive checks and assurance gates -/

/-- A row whose taps make one tree constant: taps `(N-1, b, b)` give the all-ones restriction,
so no bound on the bias can hold for every tap choice. -/
theorem threeTap_constant_tree : leafWeight 32768 (tapFn [32767, 5, 5]) = 32768 := by
  rw [threeTap_weight 32768 _ _ _ (by decide) (by decide) (by decide)]; decide

/-- Exhaustive check of the second-moment law on a toy size (`N = 3`, two trees, three taps). -/
theorem matrix_second_moment_toy :
    matrixSum 3 3 2 (fun gs => noiseSignedSum 3 gs false * noiseSignedSum 3 gs false) = 83 ^ 2 := by
  decide +kernel

theorem witness_single_row_markov : ∃ k : Nat, k ≤ 960 := ⟨60, by decide⟩

/-! ## 7. Depth-14 (`N = 16384`) Second-Moment Laws and Regular-Noise Entropy Boundary -/

private theorem kernelPowSum_depth14_three_aux :
    kernelPowSum (2 ^ 14) 3 = 236118330007544266752 := by
  rw [kernelPowSum_pow2]; decide +kernel

private theorem kernelPowSum_depth14_four_aux :
    kernelPowSum (2 ^ 14) 4 = 3868562718843605266464768 := by
  rw [kernelPowSum_pow2]; decide +kernel

private theorem kernelPowSum_depth14_six_aux :
    kernelPowSum (2 ^ 14) 6 = 741756732762029982447477945532416 := by
  rw [kernelPowSum_pow2]; decide +kernel

theorem kernelPowSum_depth14_three : kernelPowSum 16384 3 = 236118330007544266752 :=
  kernelPowSum_depth14_three_aux

theorem kernelPowSum_depth14_four : kernelPowSum 16384 4 = 3868562718843605266464768 :=
  kernelPowSum_depth14_four_aux

theorem kernelPowSum_depth14_six :
    kernelPowSum 16384 6 = 741756732762029982447477945532416 :=
  kernelPowSum_depth14_six_aux

/-- At depth 14 (`N = 2^14 = 16384`, `T = 64`), mean squared single-row bias over uniform taps
is below `2^-148`. -/
theorem denseDepth14_single_row_second_moment :
    matrixSum 16384 3 64 (fun gs => noiseSignedSum 16384 gs false * noiseSignedSum 16384 gs false) *
        2 ^ 148 ≤ (((16384 ^ 3) ^ 64 : Nat) : Int) * (16384 ^ 64) ^ 2 := by
  rw [matrix_second_moment, kernelPowSum_depth14_three]; decide +kernel

/-- At depth 14 (`N = 16384`, `T = 64`), mean squared two-row XOR bias (`m = 6`) is below `2^-179`. -/
theorem denseDepth14_two_row_second_moment :
    matrixSum 16384 6 64 (fun gs => noiseSignedSum 16384 gs false * noiseSignedSum 16384 gs false) *
        2 ^ 179 ≤ (((16384 ^ 6) ^ 64 : Nat) : Int) * (16384 ^ 64) ^ 2 := by
  rw [matrix_second_moment, kernelPowSum_depth14_six]; decide +kernel

/-- For every tap count `4 + k` per tree at depth 14 (`N = 16384`, `T = 64`), the mean squared
bias over uniform taps is below `2^-148`. -/
theorem denseDepth14_tap_count_ge_four_second_moment (k : Nat) :
    matrixSum 16384 (4 + k) 64
        (fun gs => noiseSignedSum 16384 gs false * noiseSignedSum 16384 gs false) * 2 ^ 148 ≤
      ((16384 : Int) ^ k) ^ 64 * 2 ^ 5376 := by
  rw [matrix_second_moment]
  have hK := kernelPowSum_tail_le 16384 k
  rw [kernelPowSum_depth14_four] at hK
  have hPow := (int_pow_le_pow_left (kernelPowSum_nonneg 16384 (4 + k)) hK 64).1
  have hNum : (3868562718843605266464768 : Int) ^ 64 * 2 ^ 148 ≤ 2 ^ 5376 := by decide +kernel
  have hN : ((16384 : Nat) : Int) = 16384 := rfl
  rw [hN, Int.mul_pow] at hPow
  have hTwo : (0 : Int) ≤ 2 ^ 148 := Int.le_of_lt (Int.pow_pos (by decide : (0 : Int) < 2))
  have hBase : (0 : Int) ≤ (16384 ^ k) ^ 64 :=
    Int.le_of_lt (Int.pow_pos (Int.pow_pos (by decide : (0 : Int) < 16384)))
  refine Int.le_trans (Int.mul_le_mul_of_nonneg_right hPow hTwo) ?_
  rw [Int.mul_assoc]
  exact Int.mul_le_mul_of_nonneg_left hNum hBase

/-- At depth 14 (`2^2688` single-row tap choices, `2^896` regular-noise tuples), at most a
`2^(2k-148)` fraction of tap choices has bias at least `2^-k`. -/
theorem denseDepth14_single_row_markov (k : Nat) (hk : k ≤ 896) :
    largeBiasCount 16384 3 64 (2 ^ (1792 - 2 * k)) * 2 ^ 148 ≤ 2 ^ (2 * k) * 2 ^ 2688 := by
  have hM := largeBiasCount_markov 16384 3 64 (2 ^ (1792 - 2 * k))
  rw [kernelPowSum_depth14_three] at hM
  have hBound : (236118330007544266752 : Int) ^ 64 * 2 ^ 148 ≤ 2 ^ 4480 := by decide +kernel
  have hPos : (0 : Int) < 2 ^ (1792 - 2 * k) := Int.pow_pos (by decide : (0 : Int) < 2)
  have hSplit : (2 : Int) ^ 4480 = 2 ^ (1792 - 2 * k) * (2 ^ (2 * k) * 2 ^ 2688) := by
    rw [← Int.pow_add, ← Int.pow_add]
    exact congrArg (fun e : Nat => (2 : Int) ^ e) (by omega : 4480 = 1792 - 2 * k + (2 * k + 2688))
  have hChain : 2 ^ (1792 - 2 * k) * (largeBiasCount 16384 3 64 (2 ^ (1792 - 2 * k)) * 2 ^ 148) ≤
      2 ^ (1792 - 2 * k) * (2 ^ (2 * k) * 2 ^ 2688) := by
    rw [← hSplit, ← Int.mul_assoc]
    exact Int.le_trans (Int.mul_le_mul_of_nonneg_right hM (Int.le_of_lt (Int.pow_pos (by decide : (0 : Int) < 2)))) hBound
  exact Int.le_of_mul_le_mul_left hChain hPos

/-- Count of distinct elements in `u` hit by an expansion image `img`. -/
def outputSupportHits {β : Type} [DecidableEq β] (img : List β) : List β → Nat
  | [] => 0
  | y :: rest => (if y ∈ img then 1 else 0) + outputSupportHits img rest

private theorem outputSupportHits_zero {β : Type} [DecidableEq β] :
    ∀ u : List β, outputSupportHits [] u = 0
  | [] => rfl
  | _ :: rest => by simp [outputSupportHits, outputSupportHits_zero rest]

private theorem outputSupportHits_not_mem {β : Type} [DecidableEq β] (a : β) (r : List β) :
    ∀ (u : List β), a ∉ u → outputSupportHits (a :: r) u = outputSupportHits r u
  | [], _ => rfl
  | y :: rest, hNot => by
    have hya : y ≠ a := fun h => hNot (h ▸ List.Mem.head rest)
    have hRest : a ∉ rest := fun h => hNot (List.Mem.tail y h)
    unfold outputSupportHits
    simp [List.mem_cons, hya, outputSupportHits_not_mem a r rest hRest]

private theorem outputSupportHits_cons_le {β : Type} [DecidableEq β] (a : β) (r : List β) :
    ∀ (u : List β), u.Nodup → outputSupportHits (a :: r) u ≤ 1 + outputSupportHits r u
  | [], _ => by simp [outputSupportHits]
  | y :: rest, hNd => by
    rw [List.nodup_cons] at hNd
    obtain ⟨hyNotIn, hRestNd⟩ := hNd
    unfold outputSupportHits
    if hya : y = a then
      subst hya
      rw [outputSupportHits_not_mem y r rest hyNotIn]
      simp [List.mem_cons]
    else
      have ih := outputSupportHits_cons_le a r rest hRestNd
      simp [List.mem_cons, hya]
      omega

/-- Any deterministic expansion `expand` of a regular-noise configuration list `configs` hits
every image element on real inputs while covering at most `configs.length` elements of any
duplicate-free output enumeration `u`. -/
theorem regularNoise_support_hits_le_config_count {α β : Type} [DecidableEq β]
    (expand : α → β) (configs : List α) (u : List β) (hNd : u.Nodup) :
    (∀ cfg ∈ configs, expand cfg ∈ configs.map expand) ∧
    outputSupportHits (configs.map expand) u ≤ configs.length := by
  refine ⟨fun cfg hMem => List.mem_map_of_mem hMem, ?_⟩
  induction configs with
  | nil => simp [outputSupportHits_zero]
  | cons c cs ih =>
    simp only [List.map_cons, List.length_cons]
    have hStep := outputSupportHits_cons_le (expand c) (cs.map expand) u hNd
    omega

/-- `#tooth` Regular noise over 64 trees of depth 15 has `2^960` configurations (`2^896` at depth 14),
so for any output space larger than `2^960` (such as the `139,264`-bit expanded vector), no
deterministic tap matrix can cover the full output space; security beyond `960` bits necessarily
rests on computational Dual-LPN hardness rather than unbounded all-subset statistical small bias. -/
theorem tooth_densePcg_regularNoise_entropy_deficit {α β : Type} [DecidableEq β]
    (expand : α → β) (configs : List α) (u : List β)
    (hCfg : configs.length ≤ (2 : Nat) ^ (15 * 64))
    (hUniv : (2 : Nat) ^ (15 * 64) < u.length) (hNd : u.Nodup) :
    outputSupportHits (configs.map expand) u ≠ u.length := by
  have hLe := (regularNoise_support_hits_le_config_count expand configs u hNd).2
  exact Nat.ne_of_lt (Nat.lt_of_le_of_lt (Nat.le_trans hLe hCfg) hUniv)

theorem densePcg_regularNoise_entropy_exponents :
    15 * 64 = 960 ∧ 14 * 64 = 896 ∧
    960 + 138304 = 139264 ∧ 896 + 138368 = 139264 := by
  decide

end Qsag
end

#tooth_pair Qsag.regularNoise_support_hits_le_config_count vs Qsag.tooth_densePcg_regularNoise_entropy_deficit

#verify_constructive Qsag.threeTap_weight Qsag.noiseSignedSum_eq Qsag.regularRates_parityBias_eq
  Qsag.row_signed_count_natAbs Qsag.prodRow0_bias_bracket Qsag.prodRow0_balanced_tree_count
  Qsag.tap_pair_kernel Qsag.tapsSum_pair Qsag.tree_second_moment Qsag.matrix_second_moment
  Qsag.largeBiasCount_markov Qsag.kernelPowSum_closed Qsag.dcSum_eq Qsag.kernelPowSum_pow2
  Qsag.kernelPowSum_depth15_three Qsag.kernelPowSum_depth15_six
  Qsag.denseDepth15_single_row_second_moment Qsag.denseDepth15_two_row_second_moment
  Qsag.denseDepth15_single_row_markov Qsag.kernelPowSum_tail_le Qsag.kernelPowSum_nonneg
  Qsag.denseDepth15_tap_count_ge_four_second_moment Qsag.threeTap_constant_tree Qsag.matrix_second_moment_toy
  Qsag.kernelPowSum_depth14_three Qsag.kernelPowSum_depth14_four Qsag.kernelPowSum_depth14_six
  Qsag.denseDepth14_single_row_second_moment Qsag.denseDepth14_two_row_second_moment
  Qsag.denseDepth14_tap_count_ge_four_second_moment Qsag.denseDepth14_single_row_markov
  Qsag.regularNoise_support_hits_le_config_count Qsag.tooth_densePcg_regularNoise_entropy_deficit
  Qsag.densePcg_regularNoise_entropy_exponents

/-
# Qsag.Protocol.Threshold.DensePcgProductionTaps — row 0 of a production tap matrix from the Keccak specification

`lpnTap` is `BatchedTapGenerator` of `pcg_dense.rs`: one SHAKE-256 block per counter over the
62-byte input `"QSAG.DPCG.LPNTAP" ‖ session ‖ sender ‖ receiver ‖ tree ‖ depth ‖ counter`, read as
68 little-endian 16-bit words per block and masked to the tree depth. `prodRow0Taps_eq_generator`
evaluates it with the kernel for the 64 trees of row 0 (session `00..1f`, sender 0, receiver 1,
depth 15) and obtains the tap list used by `prodRow0_bias_bracket`.
-/

public section
namespace Qsag
set_option autoImplicit false

/-- Absorbed state of one tap block: lanes 0..7 hold the input and the `0x1F` suffix at byte 62,
lane 16 holds the final `0x80` of the 136-byte rate. `session` is the four little-endian lanes
of the 32-byte session id. -/
@[expose] def lpnTapBlockState (session : UInt64 × UInt64 × UInt64 × UInt64)
    (sender receiver tree depth ctr : Nat) : KState :=
  { zeroKState with
    a0 := 0x4350442E47415351
    a1 := 0x5041544E504C2E47
    a2 := session.1
    a3 := session.2.1
    a4 := session.2.2.1
    a5 := session.2.2.2
    a6 := UInt64.ofNat (sender % 65536 + (receiver % 65536) * 2 ^ 16 + (tree % 256) * 2 ^ 32 +
      (depth % 256) * 2 ^ 40 + (ctr % 65536) * 2 ^ 48)
    a7 := UInt64.ofNat ((ctr / 65536) % 2 ^ 48 + 0x1F * 2 ^ 48)
    a16 := 0x8000000000000000 }

@[expose] def kstateLane (s : KState) : Nat → UInt64
  | 0 => s.a0 | 1 => s.a1 | 2 => s.a2 | 3 => s.a3 | 4 => s.a4 | 5 => s.a5 | 6 => s.a6
  | 7 => s.a7 | 8 => s.a8 | 9 => s.a9 | 10 => s.a10 | 11 => s.a11 | 12 => s.a12 | 13 => s.a13
  | 14 => s.a14 | 15 => s.a15 | _ => s.a16

/-- The `idx`-th masked tap of a tree's stream. -/
@[expose] def lpnTap (session : UInt64 × UInt64 × UInt64 × UInt64)
    (sender receiver tree depth idx : Nat) : Nat :=
  let out := keccakF1600 (lpnTapBlockState session sender receiver tree depth (idx / 68))
  ((kstateLane out ((idx % 68) / 4)).toNat / 2 ^ (16 * (idx % 4))) % 65536 % 2 ^ depth

@[expose] def lpnRowTaps (session : UInt64 × UInt64 × UInt64 × UInt64)
    (sender receiver tree depth row : Nat) : Nat × Nat × Nat :=
  (lpnTap session sender receiver tree depth (3 * row),
   lpnTap session sender receiver tree depth (3 * row + 1),
   lpnTap session sender receiver tree depth (3 * row + 2))

/-- Session id `00 01 .. 1f` as little-endian lanes. -/
@[expose] def auditSession : UInt64 × UInt64 × UInt64 × UInt64 :=
  (0x0706050403020100, 0x0F0E0D0C0B0A0908, 0x1716151413121110, 0x1F1E1D1C1B1A1918)

@[expose] def lpnMatrixRow (session : UInt64 × UInt64 × UInt64 × UInt64)
    (sender receiver depth row : Nat) : List (Nat × Nat × Nat) :=
  (List.range 64).map (fun tree => lpnRowTaps session sender receiver tree depth row)

/-- The tap list of `prodRow0_bias_bracket` is row 0 of the generator for the audit session. -/
theorem prodRow0Taps_eq_generator : lpnMatrixRow auditSession 0 1 15 0 = prodRow0Taps := by
  simp only [lpnMatrixRow, lpnRowTaps, lpnTap, lpnTapBlockState, auditSession, zeroKState_eq, keccakF1600_eq, keccakRoundConstants_eq]
  decide +kernel

/-- Row 0 of the generated matrix: the exact regular-noise signed count of its one-row test has
magnitude strictly between `2^-118` and `2^-117` of the `32768^64` noise tuples. -/
theorem generatedRow0_bias_bracket :
    (noiseSignedSum 32768 (rowTestFns (lpnMatrixRow auditSession 0 1 15 0)) false).natAbs * 2 ^ 117
        < 32768 ^ 64 ∧
    32768 ^ 64 <
      (noiseSignedSum 32768 (rowTestFns (lpnMatrixRow auditSession 0 1 15 0)) false).natAbs * 2 ^ 118 := by
  rw [prodRow0Taps_eq_generator, prodRow0_bias_bracket.2.1]
  exact prodRow0_bias_bracket.2.2

/-- Row 543 of the same matrix, the largest one-row bias among its first 1024 rows in the
external audit. -/
def prodRow543Taps : List (Nat × Nat × Nat) := [
  (17811, 19186, 1144), (8163, 8063, 7741), (14982, 9969, 29441), (11138, 17046, 28217),
  (27137, 10060, 2594), (14186, 4239, 7023), (26594, 32455, 26675), (29144, 11850, 22795),
  (13007, 32005, 7932), (9809, 5690, 6408), (7976, 9150, 20007), (8608, 23219, 10343),
  (11788, 5209, 1596), (9498, 25269, 31220), (24200, 23386, 17038), (25190, 25033, 3534),
  (31785, 12453, 31351), (25646, 15813, 16610), (16910, 23477, 16018), (14872, 13255, 2456),
  (13680, 18179, 1660), (4152, 20176, 24844), (30219, 4858, 24625), (7375, 13585, 13886),
  (13609, 27444, 13521), (29699, 10375, 26489), (28259, 3048, 24577), (32440, 507, 31497),
  (12159, 3194, 24273), (2537, 27166, 12734), (7730, 11162, 11463), (20660, 17540, 10506),
  (12915, 18221, 3417), (21164, 15848, 18517), (31037, 27423, 27934), (31861, 23242, 23731),
  (11256, 1974, 14515), (5502, 8465, 5236), (2496, 12327, 18443), (15990, 20076, 24045),
  (23817, 11317, 26044), (23259, 5891, 24656), (31247, 2015, 1429), (17016, 5659, 17455),
  (3095, 8161, 25266), (4433, 358, 10445), (8050, 103, 32212), (215, 18606, 14090),
  (7698, 25781, 10590), (27500, 27600, 26363), (22885, 29266, 4459), (7496, 25050, 22696),
  (17256, 10779, 30145), (9449, 26777, 26387), (25982, 5216, 5585), (29724, 11024, 10801),
  (32083, 29232, 22970), (11501, 2020, 9780), (25907, 6319, 26123), (19703, 7890, 26062),
  (5716, 24250, 2709), (4497, 11050, 31832), (23568, 22531, 29332), (12298, 22371, 20043)]

theorem prodRow543Taps_eq_generator : lpnMatrixRow auditSession 0 1 15 543 = prodRow543Taps := by
  simp only [lpnMatrixRow, lpnRowTaps, lpnTap, lpnTapBlockState, auditSession, zeroKState_eq, keccakF1600_eq, keccakRoundConstants_eq]
  decide +kernel

private theorem prodRow543_below : tapsBelow 32768 prodRow543Taps = true := by decide +kernel
private theorem prodRow543_upper : rowBiasNat 32768 prodRow543Taps * 2 ^ 89 < 32768 ^ 64 := by
  decide +kernel
private theorem prodRow543_lower : 32768 ^ 64 < rowBiasNat 32768 prodRow543Taps * 2 ^ 90 := by
  decide +kernel

/-- Its one-row bias lies strictly between `2^-90` and `2^-89`. -/
theorem generatedRow543_bias_bracket :
    (noiseSignedSum 32768 (rowTestFns (lpnMatrixRow auditSession 0 1 15 543)) false).natAbs * 2 ^ 89
        < 32768 ^ 64 ∧
    32768 ^ 64 <
      (noiseSignedSum 32768 (rowTestFns (lpnMatrixRow auditSession 0 1 15 543)) false).natAbs * 2 ^ 90 := by
  rw [prodRow543Taps_eq_generator, row_signed_count_natAbs 32768 prodRow543Taps prodRow543_below]
  exact ⟨prodRow543_upper, prodRow543_lower⟩

end Qsag
end

#verify_constructive Qsag.prodRow0Taps_eq_generator Qsag.generatedRow0_bias_bracket
  Qsag.prodRow543Taps_eq_generator Qsag.generatedRow543_bias_bracket
