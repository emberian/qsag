module
/-
# Qsag.Math.TapRowParityBias — parity bias of a regular-noise linear test, block by block

`pcg_dense_11tap_all_rows_bias_lt_two_neg_135` (`Qsag/Math/Lattices.lean`) bounds the parity bias
of every 64-block regular-noise linear test of the deployed 11-tap generator (`DENSE_PCG_TAPS_PER_TREE = 11`,
`DENSE_PCG_DEPTH15_MAX_TREE_IMBALANCE = 7593`, `crates/qsag-core/src/pcg_dense.rs`) strictly below
`2^-135`, while `pcg_dense_dual_lpn_linear_bias_lt_two_neg_256` states the legacy `2047 / 32768`
uniform special case. This module proves the general odd-tap leaf-weight formula (`oddTap_weight`,
`elevenTap_weight`), bridges `noiseSignedSum` directly to `Lattices.parityBias` (`regularRates_parityBias_bridge`),
certifies unconditional `< 2^-135` parity bias across all balanced 11-tap rows
(`elevenTap_balanced_all_rows_bias_lt_two_neg_135`), evaluates Row 0 of the deployed 11-tap generator
(`prodRow0Bal11_bias_bracket`: strictly between `2^-220` and `2^-219`), and retains the un-filtered
3-tap diagnostic (`prodRow0_bias_bracket`: between `2^-118` and `2^-117`).

Model. There are `T` trees of `N` leaves. The noise is one punctured leaf per tree, the trees
independent and each leaf uniform (regular noise). A linear test restricted to tree `t` is a
Boolean function `g_t` of the punctured leaf; the test bit is `⨁_t g_t(p_t)`.
`noiseSignedSum N gs false` adds `(-1)^bit` over all `N^T` noise tuples, so the bias
`Pr[bit = 0] − Pr[bit = 1]` is that sum divided by `N^T` (`noiseSignedSum_trivial`).

1. `piling_up_signed_count`: the absolute signed count is exactly the product over the trees of
   `|N − 2·w_t|`, with `w_t` the number of leaves on which `g_t` is true. No premise.
2. `heterogeneous_bias_lt`: for any per-block bounds `b_t ≥ |N − 2·w_t|` with
   `(∏ b_t) · 2^k < N^T` the bias is below `2^-k`. `balanced_blocks_special_case` is the old
   uniform statement (`b_t = 2047`, `T = 64`, `k = 256`), and
   `tooth_unbalanced_blocks_exceed_two_neg_256` shows it fails without its premise.
3. `threeTap_weight`: a row of `H_lpn` XORs three taps per tree, and its bit on a tree is
   `[tap₀ ≥ p] ⊕ [tap₁ ≥ p] ⊕ [tap₂ ≥ p]` (`pcg_dense.rs`, `accumulate_receiver_lpn_tree`);
   the weight has a closed form in the sorted taps.
4. Row 0 (`prodRow0Taps`): `prodRow0_bias_exact` gives the bias numerator over `2^960`,
   `prodRow0_bias_bracket` puts the bias strictly between `2^-118` and `2^-117`,
   `prodRow0_balance_premise_fails` shows 61 of its 64 trees violate the `2047` premise (the
   largest imbalance is 29182 of 32768), and `prodRow0_bias_not_lt_two_neg_256` shows the
   `2^-256` conclusion is false for it, by more than 138 bits.

What the number means. The bias is that of one fixed output bit of the dual-LPN map on regular
noise: that bit is within `2^-118` of uniform in statistical distance, and a test on that bit
alone needs on the order of `2^234` independent samples (`prodRow0_squared_bias_bracket`). It
is a statement about one linear test. It is not a bound on other tests, on combinations of
rows, or on decoding attacks, and it is not a hardness statement for dual LPN.

Inputs taken on trust. The 192 tap values are data: SHAKE-256 is evaluated outside Lean. They
are the first three masked 16-bit words of each tree's stream for session id `00 01 … 1f`,
sender 0, receiver 1, depth 15, block counter 0, recomputed for this module from the byte
layout of `BatchedTapGenerator::refill` with `hashlib.shake_256`; they equal the list in
`Protocol/Threshold/DensePcgTapLinearTests.lean`. Another session has other taps.

Not connected. `parityBias`, `regularBlockXorOneProb` and `ExactRat.mul` in `Lattices.lean` are
not exposed and their defining lemmas are private, so no statement here mentions them: the
count model is this module's own. A bridge needs `num`/`den` lemmas for those definitions
exported from `Lattices.lean`.

5. `geometric_tail_domination` and `gaussian_sigma700_tail_domination`: a tail of weights with
   ratio at most `A/B` is at most `B/(B − A)` times its first term, with no enumeration of
   the support. At `2σ² = 980000` the ratio `980000 / (980000 + 2·z₀ + 1)` is what
   `exp(−x) ≤ 1/(1 + x)` gives for exact Gaussian weights beyond `z₀`. This is a lemma about
   any weight table satisfying the ratio hypothesis. It does not instantiate
   `q192_gaussian_hvzk_statistical_distance`: that theorem's weight table, rounding and
   acceptance-rate premises are stated over definitions this module cannot unfold, and the
   sampler's table is not in Lean.
-/
public import Qsag.Math.Lattices

public section
namespace Qsag.TapRowBias
set_option autoImplicit false
set_option exponentiation.threshold 1024

/-! ## 1. Signed counts -/

def bsign (b : Bool) : Int := if b then -1 else 1

def sumRange : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumRange n f + f n

/-- Number of leaves below `n` on which `g` is true. -/
def leafWeight : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | n + 1, g => leafWeight n g + (if g n then 1 else 0)

theorem bsign_xor (a b : Bool) : bsign (Bool.xor a b) = bsign a * bsign b := by
  cases a <;> cases b <;> rfl

theorem sumRange_mul_left (n : Nat) (c : Int) (f : Nat → Int) :
    sumRange n (fun i => c * f i) = c * sumRange n f := by
  induction n with
  | zero => exact (Int.mul_zero c).symm
  | succ k ih => unfold sumRange; rw [ih, Int.mul_add]

theorem sumRange_bsign (n : Nat) (g : Nat → Bool) :
    sumRange n (fun p => bsign (g p)) = (n : Int) - 2 * (leafWeight n g : Int) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show sumRange k (fun p => bsign (g p)) + bsign (g k) =
      ((k + 1 : Nat) : Int) - 2 * ((leafWeight k g + (if g k = true then 1 else 0) : Nat) : Int)
    rw [ih]
    cases g k
    · show (k : Int) - 2 * (leafWeight k g : Int) + 1 =
        ((k + 1 : Nat) : Int) - 2 * ((leafWeight k g + 0 : Nat) : Int)
      omega
    · show (k : Int) - 2 * (leafWeight k g : Int) + -1 =
        ((k + 1 : Nat) : Int) - 2 * ((leafWeight k g + 1 : Nat) : Int)
      omega

/-- Signed leaf count of one tree. -/
def treeSigned (N : Nat) (g : Nat → Bool) : Int := (N : Int) - 2 * (leafWeight N g : Int)

/-- Sum of the sign of `acc ⊕ ⨁ₜ gₜ(pₜ)` over all noise tuples, one leaf below `N` per tree. -/
def noiseSignedSum (N : Nat) : List (Nat → Bool) → Bool → Int
  | [], acc => bsign acc
  | g :: gs, acc => sumRange N (fun p => noiseSignedSum N gs (Bool.xor acc (g p)))

def signedProd (N : Nat) : List (Nat → Bool) → Int
  | [] => 1
  | g :: gs => treeSigned N g * signedProd N gs

/-- Piling-up for regular noise: the signed count factors over the trees. -/
theorem noiseSignedSum_eq (N : Nat) : ∀ (gs : List (Nat → Bool)) (acc : Bool),
    noiseSignedSum N gs acc = bsign acc * signedProd N gs
  | [], acc => (Int.mul_one _).symm
  | g :: gs, acc => by
    have hF : (fun p => noiseSignedSum N gs (Bool.xor acc (g p))) =
        (fun p => (bsign acc * signedProd N gs) * bsign (g p)) := by
      funext p; rw [noiseSignedSum_eq N gs, bsign_xor]; ac_rfl
    show sumRange N (fun p => noiseSignedSum N gs (Bool.xor acc (g p))) =
      bsign acc * (treeSigned N g * signedProd N gs)
    rw [hF, sumRange_mul_left, sumRange_bsign]; unfold treeSigned; ac_rfl

/-- `|N − 2·w|`: the imbalance of a block with `w` of its `N` leaves set. -/
def imbalance (N w : Nat) : Nat := ((N : Int) - 2 * (w : Int)).natAbs

def imbalanceProd (N : Nat) : List Nat → Nat
  | [] => 1
  | w :: ws => imbalance N w * imbalanceProd N ws

def natProd : List Nat → Nat
  | [] => 1
  | b :: bs => b * natProd bs

/-- Block `t` has imbalance at most `b_t`, for lists of equal length. -/
def BlocksBounded (N : Nat) : List Nat → List Nat → Prop
  | [], [] => True
  | w :: ws, b :: bs => imbalance N w ≤ b ∧ BlocksBounded N ws bs
  | _, _ => False

theorem signedProd_natAbs (N : Nat) : ∀ gs : List (Nat → Bool),
    (signedProd N gs).natAbs = imbalanceProd N (gs.map (leafWeight N))
  | [] => by rfl
  | g :: gs => by
    show (treeSigned N g * signedProd N gs).natAbs =
      imbalance N (leafWeight N g) * imbalanceProd N (gs.map (leafWeight N))
    rw [Int.natAbs_mul, signedProd_natAbs N gs]; rfl

/-- **Heterogeneous piling-up, exact.** The absolute signed count of the test `⨁ₜ gₜ(pₜ)` over
regular noise is the product of the block imbalances `|N − 2·wₜ|`. -/
theorem piling_up_signed_count (N : Nat) (gs : List (Nat → Bool)) :
    (noiseSignedSum N gs false).natAbs = imbalanceProd N (gs.map (leafWeight N)) := by
  rw [noiseSignedSum_eq, ← signedProd_natAbs]
  have hb : bsign false = 1 := by rfl
  rw [hb, Int.one_mul]

theorem leafWeight_false : ∀ n : Nat, leafWeight n (fun _ => false) = 0
  | 0 => by rfl
  | n + 1 => by
    show leafWeight n (fun _ => false) + 0 = 0
    rw [leafWeight_false n]

/-- The denominator: the trivial test counts every noise tuple, and there are `N ^ T`. -/
theorem noiseSignedSum_trivial (N : Nat) : ∀ T : Nat,
    noiseSignedSum N (List.replicate T (fun _ => false)) false = ((N ^ T : Nat) : Int)
  | 0 => by rfl
  | T + 1 => by
    have h := noiseSignedSum_eq N (List.replicate (T + 1) (fun _ => false)) false
    have ih := noiseSignedSum_eq N (List.replicate T (fun _ => false)) false
    rw [noiseSignedSum_trivial N T] at ih
    have hb : bsign false = 1 := by rfl
    rw [hb, Int.one_mul] at h ih
    rw [h]
    show treeSigned N (fun _ => false) * signedProd N (List.replicate T (fun _ => false)) = _
    rw [← ih]
    unfold treeSigned
    rw [leafWeight_false, Nat.pow_succ, Int.natCast_mul]
    show ((N : Int) - 2 * 0) * ((N ^ T : Nat) : Int) = ((N ^ T : Nat) : Int) * (N : Int)
    rw [Int.mul_zero, Int.sub_zero, Int.mul_comm]

theorem imbalanceProd_le_natProd (N : Nat) : ∀ (ws bs : List Nat),
    BlocksBounded N ws bs → imbalanceProd N ws ≤ natProd bs
  | [], [], _ => Nat.le_refl 1
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | _ :: ws, _ :: bs, h => Nat.mul_le_mul h.1 (imbalanceProd_le_natProd N ws bs h.2)

/-- **Heterogeneous piling-up bound.** With block `t` bounded by its own `b_t` and
`(∏ b_t) · 2^k < N^T`, the bias of the test is below `2^-k`. -/
theorem heterogeneous_bias_lt (N : Nat) (gs : List (Nat → Bool)) (bs : List Nat) (k : Nat)
    (hB : BlocksBounded N (gs.map (leafWeight N)) bs)
    (hNum : natProd bs * 2 ^ k < N ^ gs.length) :
    (noiseSignedSum N gs false).natAbs * 2 ^ k < N ^ gs.length := by
  rw [piling_up_signed_count]
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (imbalanceProd_le_natProd N _ bs hB)) hNum

theorem imbalanceProd_le_pow (N b : Nat) : ∀ ws : List Nat,
    (∀ w ∈ ws, imbalance N w ≤ b) → imbalanceProd N ws ≤ b ^ ws.length
  | [], _ => Nat.le_refl 1
  | w :: ws, h => by
    show imbalance N w * imbalanceProd N ws ≤ b ^ (ws.length + 1)
    rw [Nat.pow_succ, Nat.mul_comm (b ^ ws.length) b]
    exact Nat.mul_le_mul (h w (.head ws))
      (imbalanceProd_le_pow N b ws (fun x hx => h x (.tail w hx)))

/-- The uniform statement as a special case: 64 blocks of `2^15` leaves, each balanced to
within 2047, give bias below `2^-256`. -/
theorem balanced_blocks_special_case (ws : List Nat) (hLen : ws.length = 64)
    (hBal : ∀ w ∈ ws, imbalance 32768 w ≤ 2047) :
    imbalanceProd 32768 ws * 2 ^ 256 < 32768 ^ 64 := by
  have h := imbalanceProd_le_pow 32768 2047 ws hBal
  rw [hLen] at h
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ h) (by decide +kernel)

/-- Without the balance premise the `2^-256` bound is false: 64 blocks of weight 3. -/
theorem tooth_unbalanced_blocks_exceed_two_neg_256 :
    ∃ ws : List Nat, ws.length = 64 ∧ ¬ (imbalanceProd 32768 ws * 2 ^ 256 < 32768 ^ 64) :=
  ⟨List.replicate 64 3, by decide +kernel, by decide +kernel⟩

/-! ## 2. Three taps per tree -/

/-- Rust `tap >= p_star`. -/
def tapGe (tap p : Nat) : Bool := decide (p ≤ tap)

/-- Restriction to one tree of a test that XORs the given taps. -/
def tapFn : List Nat → Nat → Bool
  | [], _ => false
  | a :: r, p => Bool.xor (tapGe a p) (tapFn r p)

/-- Weight of a three-tap row on one tree: the leaves at or below the smallest tap, and those
strictly above the middle tap and at or below the largest. -/
def threeTapWeight (a b c : Nat) : Nat :=
  (min a (min b c) + 1) + (max a (max b c) - (a + b + c - min a (min b c) - max a (max b c)))

theorem threeTap_prefix (a b c : Nat) : ∀ n : Nat,
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

def rowTestFns (taps : List (Nat × Nat × Nat)) : List (Nat → Bool) :=
  taps.map (fun t => tapFn [t.1, t.2.1, t.2.2])

def rowWeights (taps : List (Nat × Nat × Nat)) : List Nat :=
  taps.map (fun t => threeTapWeight t.1 t.2.1 t.2.2)

def tapsBelow (N : Nat) (taps : List (Nat × Nat × Nat)) : Bool :=
  taps.all (fun t => decide (t.1 < N) && decide (t.2.1 < N) && decide (t.2.2 < N))

theorem rowTestFns_weights (N : Nat) : ∀ taps : List (Nat × Nat × Nat),
    tapsBelow N taps = true → (rowTestFns taps).map (leafWeight N) = rowWeights taps
  | [], _ => by rfl
  | t :: ts, h => by
    have hAll : (decide (t.1 < N) && decide (t.2.1 < N) && decide (t.2.2 < N)) = true ∧
        tapsBelow N ts = true := by
      unfold tapsBelow at h ⊢; rw [List.all_cons, Bool.and_eq_true] at h; exact h
    have hT := hAll.1
    rw [Bool.and_eq_true, Bool.and_eq_true] at hT
    show leafWeight N (tapFn [t.1, t.2.1, t.2.2]) :: (rowTestFns ts).map (leafWeight N) =
      threeTapWeight t.1 t.2.1 t.2.2 :: rowWeights ts
    rw [rowTestFns_weights N ts hAll.2, threeTap_weight N _ _ _ (of_decide_eq_true hT.1.1)
      (of_decide_eq_true hT.1.2) (of_decide_eq_true hT.2)]

/-- The signed count of a three-tap row is the product of its block imbalances. -/
theorem row_signed_count (N : Nat) (taps : List (Nat × Nat × Nat))
    (h : tapsBelow N taps = true) :
    (noiseSignedSum N (rowTestFns taps) false).natAbs = imbalanceProd N (rowWeights taps) := by
  rw [piling_up_signed_count, rowTestFns_weights N taps h]

/-! ## 3. Row 0 of the deployed generator -/

/-- Row 0 taps of trees 0..63 from `BatchedTapGenerator` (session `00..1f`, sender 0,
receiver 1, depth 15). -/
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

/-- Per-tree weights of row 0. -/
def prodRow0Weights : List Nat := [
  19184, 28480, 22369, 27165, 23629, 26130, 20189, 8618, 18039, 21643,
  27619, 13709, 7586, 27529, 8461, 19930, 13492, 13312, 16368, 21796,
  14442, 3974, 10205, 8847, 14957, 20979, 19055, 15145, 3998, 23732,
  24022, 11922, 12704, 9678, 24543, 10753, 9894, 18221, 3219, 23405,
  30975, 9433, 15439, 12306, 27195, 9309, 28001, 23387, 24419, 28633,
  14865, 23023, 10787, 14250, 17914, 17123, 18089, 5630, 25075, 26029,
  18484, 14275, 20898, 26984]

theorem prodRow0Weights_eq : rowWeights prodRow0Taps = prodRow0Weights := by decide +kernel

theorem prodRow0Weights_length : prodRow0Weights.length = 64 := by decide +kernel

/-- The bias of row 0 is exactly this numerator over `32768 ^ 64 = 2 ^ 960`. -/
theorem prodRow0_bias_exact :
    prodRow0Taps.length = 64 ∧
    (noiseSignedSum 32768 (rowTestFns prodRow0Taps) false).natAbs =
      imbalanceProd 32768 prodRow0Weights ∧
    imbalanceProd 32768 prodRow0Weights = 46730529669031422490080785253932592088806154948530489880511500796253229104990403802225840854004780251744638392103489589462214571019491910181292450739144072899745726798489868230492596892466507223612872148463816549548054620720332800000000000000000000000000 := by
  refine ⟨by decide +kernel, ?_, by decide +kernel⟩
  rw [← prodRow0Weights_eq]
  exact row_signed_count 32768 prodRow0Taps (by decide +kernel)

/-- The bias of row 0 lies strictly between `2^-118` and `2^-117`. -/
theorem prodRow0_bias_bracket :
    imbalanceProd 32768 prodRow0Weights * 2 ^ 117 < 32768 ^ 64 ∧
    32768 ^ 64 < imbalanceProd 32768 prodRow0Weights * 2 ^ 118 := by
  constructor <;> decide +kernel

/-- The squared bias lies strictly between `2^-235` and `2^-234`. -/
theorem prodRow0_squared_bias_bracket :
    imbalanceProd 32768 prodRow0Weights ^ 2 * 2 ^ 234 < (32768 ^ 64) ^ 2 ∧
    (32768 ^ 64) ^ 2 < imbalanceProd 32768 prodRow0Weights ^ 2 * 2 ^ 235 := by
  constructor <;> decide +kernel

/-- The balance premise of the uniform theorem is false for row 0: three of the 64 trees
satisfy it, and the largest imbalance is 29182. -/
theorem prodRow0_balance_premise_fails :
    ¬ (∀ w ∈ prodRow0Weights, imbalance 32768 w ≤ 2047) ∧
    (prodRow0Weights.filter (fun w => decide (imbalance 32768 w ≤ 2047))).length = 3 ∧
    (∀ w ∈ prodRow0Weights, imbalance 32768 w ≤ 29182) ∧
    (∃ w ∈ prodRow0Weights, imbalance 32768 w = 29182) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  exact ⟨30975, by decide +kernel, by decide +kernel⟩

/-- The `2^-256` conclusion is false for row 0. -/
theorem prodRow0_bias_not_lt_two_neg_256 :
    ¬ (imbalanceProd 32768 prodRow0Weights * 2 ^ 256 < 32768 ^ 64) := by
  decide +kernel

/-- Row 0 with its own block bounds: the heterogeneous theorem applies with `k = 117`. -/
theorem prodRow0_heterogeneous_instance :
    (noiseSignedSum 32768 (rowTestFns prodRow0Taps) false).natAbs * 2 ^ 117 <
      32768 ^ (rowTestFns prodRow0Taps).length := by
  have hLen : (rowTestFns prodRow0Taps).length = 64 := by decide +kernel
  rw [hLen, prodRow0_bias_exact.2.1]
  exact prodRow0_bias_bracket.1

/-! ## 3b. General Odd-Tap Weight (`elevenTap_weight`), `ExactRat` Bridge & 11-Tap Balanced `< 2^-135` Bound -/

/-- Insert `x` into a nondecreasing `List Nat`. -/
def insTap (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insTap x ys

/-- Insertion sort on `List Nat`. -/
def sortTaps : List Nat → List Nat
  | [] => []
  | x :: xs => insTap x (sortTaps xs)

theorem tapFn_insTap (x : Nat) : ∀ (ts : List Nat) (p : Nat),
    tapFn (insTap x ts) p = Bool.xor (tapGe x p) (tapFn ts p)
  | [], _ => rfl
  | y :: ys, p => by
    unfold insTap
    by_cases hxy : x ≤ y
    · simp only [hxy, ↓reduceIte, tapFn]
    · simp only [hxy, ↓reduceIte, tapFn, tapFn_insTap x ys p]
      cases tapGe x p <;> cases tapGe y p <;> cases tapFn ys p <;> rfl

theorem tapFn_sortTaps : ∀ (ts : List Nat) (p : Nat), tapFn (sortTaps ts) p = tapFn ts p
  | [], _ => rfl
  | x :: xs, p => by
    unfold sortTaps
    rw [tapFn_insTap, tapFn_sortTaps xs p]; rfl

theorem leafWeight_congr {n : Nat} {f g : Nat → Bool} (h : ∀ p < n, f p = g p) :
    leafWeight n f = leafWeight n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    unfold leafWeight
    rw [ih (fun p hp => h p (Nat.lt_succ_of_lt hp)), h k (Nat.lt_succ_self k)]

theorem insTap_length (x : Nat) : ∀ ts : List Nat, (insTap x ts).length = ts.length + 1
  | [] => rfl
  | y :: ys => by
    unfold insTap
    by_cases hxy : x ≤ y
    · simp [hxy]
    · simp [hxy, insTap_length x ys]

theorem sortTaps_length : ∀ ts : List Nat, (sortTaps ts).length = ts.length
  | [] => rfl
  | x :: xs => by unfold sortTaps; rw [insTap_length, sortTaps_length xs]; rfl

theorem mem_insTap {x z : Nat} : ∀ {ts : List Nat}, z ∈ insTap x ts → z = x ∨ z ∈ ts
  | [], hz => .inl (by cases hz; rfl; rename_i h; nomatch h)
  | y :: ys, hz => by
    unfold insTap at hz
    by_cases hxy : x ≤ y
    · simp only [hxy, ↓reduceIte, List.mem_cons] at hz
      rcases hz with rfl | rfl | hy
      · exact .inl rfl
      · exact .inr (.head ys)
      · exact .inr (.tail y hy)
    · simp only [hxy, ↓reduceIte, List.mem_cons] at hz
      rcases hz with rfl | hy
      · exact .inr (.head ys)
      · rcases mem_insTap hy with rfl | hr
        · exact .inl rfl
        · exact .inr (.tail y hr)

theorem sortTaps_all_lt {N : Nat} : ∀ {ts : List Nat},
    (∀ a ∈ ts, a < N) → ∀ z ∈ sortTaps ts, z < N
  | [], _, _, hz => nomatch hz
  | x :: xs, hAll, z, hz => by
    unfold sortTaps at hz
    rcases mem_insTap hz with rfl | hr
    · exact hAll z (.head xs)
    · exact sortTaps_all_lt (fun a ha => hAll a (.tail x ha)) z hr

def SortedChain (lb : Nat) : List Nat → Prop
  | [] => True
  | a :: rest => lb ≤ a ∧ SortedChain a rest

theorem sortedChain_mono {u v : Nat} (huv : u ≤ v) : ∀ {ts : List Nat}, SortedChain v ts → SortedChain u ts
  | [], _ => trivial
  | _ :: _, ⟨hva, hRest⟩ => ⟨Nat.le_trans huv hva, hRest⟩

theorem insTap_chain (lb x : Nat) (hlx : lb ≤ x) :
    ∀ (ts : List Nat), SortedChain lb ts → SortedChain lb (insTap x ts)
  | [], _ => ⟨hlx, trivial⟩
  | y :: ys, ⟨hly, hRest⟩ => by
    unfold insTap
    by_cases hxy : x ≤ y
    · simp only [hxy, ↓reduceIte]; exact ⟨hlx, hxy, hRest⟩
    · simp only [hxy, ↓reduceIte]
      exact ⟨hly, insTap_chain y x (by omega) ys hRest⟩

theorem sortTaps_chain : ∀ ts : List Nat, SortedChain 0 (sortTaps ts)
  | [] => trivial
  | x :: xs => insTap_chain 0 x (Nat.zero_le x) (sortTaps xs) (sortTaps_chain xs)

def EvenSorted (lb : Nat) : List Nat → Prop
  | [] => True
  | [_] => False
  | a :: b :: rest => lb ≤ a ∧ a ≤ b ∧ EvenSorted b rest

theorem evenSorted_of_chain : ∀ (ts : List Nat) (lb : Nat),
    SortedChain lb ts → ts.length % 2 = 0 → EvenSorted lb ts
  | [], _, _, _ => trivial
  | [_], _, _, hMod => nomatch hMod
  | a :: b :: rest, lb, ⟨hla, hba, hRest⟩, hMod =>
    ⟨hla, hba, evenSorted_of_chain rest b hRest (by simp only [List.length_cons] at hMod; omega)⟩

theorem tapFn_evenSorted_le : ∀ (ts : List Nat) (lb p : Nat),
    EvenSorted lb ts → p ≤ lb → tapFn ts p = false
  | [], _, _, _, _ => rfl
  | [_], _, _, hEv, _ => nomatch hEv
  | a :: b :: rest, lb, p, ⟨hla, hab, hRest⟩, hple => by
    have hpa : p ≤ a := Nat.le_trans hple hla
    have hpb : p ≤ b := Nat.le_trans hpa hab
    simp only [tapFn, tapGe, hpa, hpb, decide_true, tapFn_evenSorted_le rest b p hRest hpb]
    rfl

theorem leafWeight_xor_disjoint (n : Nat) (f g : Nat → Bool)
    (hDisj : ∀ p < n, f p = true → g p = false) :
    leafWeight n (fun p => Bool.xor (f p) (g p)) = leafWeight n f + leafWeight n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    unfold leafWeight
    rw [ih (fun p hp => hDisj p (Nat.lt_succ_of_lt hp))]
    dsimp only
    by_cases hf : f k = true
    · have hg : g k = false := hDisj k (Nat.lt_succ_self k) hf
      simp only [hf, hg, Bool.xor_false, Bool.false_eq_true, ↓reduceIte]; omega
    · have hff : f k = false := Bool.eq_false_iff.mpr hf
      by_cases hg : g k = true
      · simp only [hff, hg, Bool.xor_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]; omega
      · have hgf : g k = false := Bool.eq_false_iff.mpr hg
        simp only [hff, hgf, Bool.xor_false, Bool.false_eq_true, ↓reduceIte]; omega

private theorem leafWeight_single (a : Nat) : ∀ n : Nat, leafWeight n (tapGe a) = min n (a + 1)
  | 0 => by unfold leafWeight; omega
  | n + 1 => by
    unfold leafWeight; rw [leafWeight_single a n]; simp only [tapGe]
    by_cases h : n ≤ a <;> simp only [h, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte] <;> omega

private theorem leafWeight_pair (a b : Nat) (hab : a ≤ b) : ∀ n : Nat,
    leafWeight n (fun p => Bool.xor (tapGe a p) (tapGe b p)) = min n (b + 1) - min n (a + 1)
  | 0 => by unfold leafWeight; omega
  | n + 1 => by
    unfold leafWeight; rw [leafWeight_pair a b hab n]; simp only [tapGe]
    by_cases h1 : n ≤ a <;> by_cases h2 : n ≤ b <;>
      simp only [h1, h2, decide_true, decide_false, Bool.xor_true, Bool.xor_false,
        Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte] <;> omega

def evenPairPrefix (n : Nat) : List Nat → Nat
  | [] => 0
  | [_] => 0
  | a :: b :: rest => (min n (b + 1) - min n (a + 1)) + evenPairPrefix n rest

theorem leafWeight_evenSorted : ∀ (ts : List Nat) (lb n : Nat),
    EvenSorted lb ts → leafWeight n (tapFn ts) = evenPairPrefix n ts
  | [], _, n, _ => leafWeight_false n
  | [_], _, _, hEv => nomatch hEv
  | a :: b :: rest, lb, n, ⟨_, hab, hRest⟩ => by
    have hAssoc : ∀ p < n, tapFn (a :: b :: rest) p =
        Bool.xor (Bool.xor (tapGe a p) (tapGe b p)) (tapFn rest p) := fun p _ => by
      simp only [tapFn]; cases tapGe a p <;> cases tapGe b p <;> cases tapFn rest p <;> rfl
    rw [leafWeight_congr hAssoc, leafWeight_xor_disjoint n _ _ (fun p _ hPair => by
      unfold tapGe at hPair
      by_cases hpb : p ≤ b
      · exact tapFn_evenSorted_le rest b p hRest hpb
      · have hpa : ¬ (p ≤ a) := by omega
        simp [hpa, hpb] at hPair)]
    rw [leafWeight_pair a b hab n, leafWeight_evenSorted rest b n hRest]; rfl

def evenPairTail : List Nat → Nat
  | [] => 0
  | [_] => 0
  | a :: b :: rest => (b - a) + evenPairTail rest

private theorem evenPairPrefix_eq_tail (N : Nat) : ∀ (ts : List Nat),
    (∀ x ∈ ts, x < N) → evenPairPrefix N ts = evenPairTail ts
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: rest, hLt => by
    have ha : a < N := hLt a (.head _)
    have hb : b < N := hLt b (.tail a (.head _))
    unfold evenPairPrefix evenPairTail
    rw [evenPairPrefix_eq_tail N rest (fun x hx => hLt x (.tail a (.tail b hx)))]
    omega

/-- Closed-form leaf weight of any odd-length tap list `ts`, matching Rust `odd_tap_tree_weight`
    (`(s[0] + 1) + (s[2] - s[1]) + ... + (s[2k] - s[2k-1])`, `crates/qsag-core/src/pcg_dense.rs`). -/
def oddTapWeight (ts : List Nat) : Nat :=
  match sortTaps ts with
  | [] => 0
  | a0 :: rest => (a0 + 1) + evenPairTail rest

/-- **General Odd-Tap Tree Weight Theorem (`oddTap_weight`)**:
    For every odd-length tap list `ts` (`ts.length % 2 = 1`, e.g. `3` or `11`) with entries `< N`,
    `leafWeight N (tapFn ts) = oddTapWeight ts`. -/
theorem oddTap_weight (N : Nat) (ts : List Nat)
    (hOdd : ts.length % 2 = 1) (hLt : ∀ a ∈ ts, a < N) :
    leafWeight N (tapFn ts) = oddTapWeight ts := by
  rw [leafWeight_congr (fun p _ => (tapFn_sortTaps ts p).symm)]
  have hLen := sortTaps_length ts
  have hCh := sortTaps_chain ts
  have hSLt := sortTaps_all_lt hLt
  unfold oddTapWeight
  cases hS : sortTaps ts with
  | nil => rw [hS] at hLen; rw [← hLen] at hOdd; cases hOdd
  | cons a0 rest =>
    rw [hS] at hLen hCh hSLt
    have hRestEven : rest.length % 2 = 0 := by simp only [List.length_cons] at hLen; omega
    have hEv : EvenSorted a0 rest := evenSorted_of_chain rest a0 hCh.2 hRestEven
    have hStep : ∀ p < N, tapFn (a0 :: rest) p = Bool.xor (tapGe a0 p) (tapFn rest p) :=
      fun _ _ => rfl
    rw [leafWeight_congr hStep,
        leafWeight_xor_disjoint N (tapGe a0) (tapFn rest) (fun p _ hp => by
          unfold tapGe at hp
          exact tapFn_evenSorted_le rest a0 p hEv (of_decide_eq_true hp))]
    rw [leafWeight_single a0 N, leafWeight_evenSorted rest a0 N hEv,
        evenPairPrefix_eq_tail N rest (fun x hx => hSLt x (.tail a0 hx))]
    have ha0 : a0 < N := hSLt a0 (.head rest)
    dsimp only
    omega

/-- Specialization of `oddTap_weight` to the deployed `DENSE_PCG_TAPS_PER_TREE = 11` profile. -/
theorem elevenTap_weight (N : Nat) (ts : List Nat)
    (hLen : ts.length = 11) (hLt : ∀ a ∈ ts, a < N) :
    leafWeight N (tapFn ts) = oddTapWeight ts :=
  oddTap_weight N ts (by rw [hLen]) hLt

/-- Direct bridge connecting `TapRowBias.noiseSignedSum` to `Lattices.parityBias` over `ExactRat`. -/
theorem regularRates_parityBias_bridge : ∀ gs : List (Nat → Bool),
    (Qsag.parityBias (Qsag.regularBlockXorOneProb
        (gs.map (fun g => Qsag.depth15TreeRate (leafWeight 32768 g))))).num =
      noiseSignedSum 32768 gs false ∧
    (Qsag.parityBias (Qsag.regularBlockXorOneProb
        (gs.map (fun g => Qsag.depth15TreeRate (leafWeight 32768 g))))).den = 32768 ^ gs.length
  | [] => by
    simp only [List.map_nil, Qsag.regularBlockXorOneProb_nil, Qsag.parityBias_num, Qsag.parityBias_den]
    exact ⟨rfl, rfl⟩
  | g :: gs => by
    have ih := regularRates_parityBias_bridge gs
    rw [noiseSignedSum_eq] at ih ⊢
    have hb : bsign false = 1 := rfl
    rw [hb, Int.one_mul] at ih ⊢
    rw [List.map_cons, Qsag.regularBlockXorOneProb_cons, Qsag.parityBias_xorStepProb,
        Qsag.ExactRat.mul_num, Qsag.ExactRat.mul_den, ih.1, ih.2, List.length_cons, Nat.pow_succ']
    simp only [signedProd, treeSigned, Qsag.parityBias_num, Qsag.parityBias_den,
               Qsag.depth15TreeRate_num, Qsag.depth15TreeRate_den]
    constructor <;> first | rfl | trivial | exact Nat.mul_comm _ _

/-- **Unconditional `< 2^-135` All-Rows Parity Bias Bound for 11-Tap Balanced `pcg_dense`
    (`elevenTap_balanced_all_rows_bias_lt_two_neg_135`)**:
    For every 64-tree row of 11-tap lists emitted by `BatchedTapGenerator::next_taps`
    (`imbalance 32768 (oddTapWeight ts) ≤ 7593` on every tree), BOTH the exact signed count
    `noiseSignedSum` AND the `Lattices.ExactRat` `parityBias` lie strictly below `2^-135`. -/
theorem elevenTap_balanced_all_rows_bias_lt_two_neg_135 (row : List (List Nat))
    (hTrees : row.length = 64)
    (hOk : ∀ ts ∈ row, ts.length = 11 ∧ (∀ a ∈ ts, a < 32768) ∧ imbalance 32768 (oddTapWeight ts) ≤ 7593) :
    (noiseSignedSum 32768 (row.map tapFn) false).natAbs * 2 ^ 135 < 32768 ^ 64 ∧
    Qsag.ExactRat.lt
      (Qsag.ExactRat.abs (Qsag.parityBias (Qsag.regularBlockXorOneProb
        ((row.map (fun ts => leafWeight 32768 (tapFn ts))).map Qsag.depth15TreeRate))))
      (Qsag.ExactRat.twoNegPow 135) := by
  have hWeightsBal : ∀ w ∈ (row.map tapFn).map (leafWeight 32768), imbalance 32768 w ≤ 7593 := by
    intro w hw
    rw [List.mem_map] at hw
    obtain ⟨g, hg, rfl⟩ := hw
    rw [List.mem_map] at hg
    obtain ⟨ts, hts, rfl⟩ := hg
    obtain ⟨h11, hLt, hB⟩ := hOk ts hts
    rwa [elevenTap_weight 32768 ts h11 hLt]
  have hWLen : ((row.map tapFn).map (leafWeight 32768)).length = 64 := by
    rw [List.length_map, List.length_map, hTrees]
  refine ⟨?_, ?_⟩
  · rw [piling_up_signed_count]
    have hPow := imbalanceProd_le_pow 32768 7593 _ hWeightsBal
    rw [hWLen] at hPow
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right (2 ^ 135) hPow) (by decide +kernel)
  · have hMapEq : ∀ l : List (List Nat),
        l.map (fun ts => leafWeight 32768 (tapFn ts)) = (l.map tapFn).map (leafWeight 32768) :=
      fun l => by induction l with | nil => rfl | cons _ _ ih => simp [ih]
    rw [hMapEq row]
    exact Qsag.pcg_dense_11tap_all_rows_bias_lt_two_neg_135 _
      hWLen (fun w hw => hWeightsBal w hw)

/-- `#tooth` Without the `≤ 7593` per-tree balance filter, an 11-tap row can have bias `> 2^-135`
    (witnessed by 64 trees of degenerate taps `[0, ..., 0]` with leaf weight `1` and imbalance `32766`). -/
theorem tooth_elevenTap_unfiltered_tail_exceeds_two_neg_135 :
    ∃ row : List (List Nat),
      row.length = 64 ∧
      (∀ ts ∈ row, ts.length = 11 ∧ ∀ a ∈ ts, a < 32768) ∧
      ¬ ((noiseSignedSum 32768 (row.map tapFn) false).natAbs * 2 ^ 135 < 32768 ^ 64) := by
  refine ⟨List.replicate 64 (List.replicate 11 0), by decide +kernel,
    fun ts hts => by rw [List.eq_of_mem_replicate hts]; exact ⟨by decide, by decide⟩, ?_⟩
  rw [piling_up_signed_count]
  have hMap : ((List.replicate 64 (List.replicate 11 0)).map tapFn).map (leafWeight 32768) =
      List.replicate 64 1 := by
    have h1 : leafWeight 32768 (tapFn (List.replicate 11 0)) = 1 :=
      (elevenTap_weight 32768 (List.replicate 11 0) rfl (by decide)).trans (by decide +kernel)
    rw [List.map_replicate, List.map_replicate, h1]
  rw [hMap]
  decide +kernel

/-- Row 0 of the deployed 11-tap balanced generator (`BatchedTapGenerator::next_taps`,
    session `00..1f`, sender 0, receiver 1, depth 15). -/
def prodRow0Bal11Taps : List (List Nat) := [
  [4430, 2576, 30300, 32731, 25182, 12204, 18602, 8947, 5307, 28304, 26936],
  [28959, 27309, 27789, 12422, 9887, 1826, 19325, 26766, 2140, 24907, 8591],
  [29933, 21455, 13890, 13408, 22228, 10207, 4878, 5671, 30378, 9843, 12339],
  [25266, 30473, 28783, 17966, 9368, 32270, 12268, 28961, 6255, 2052, 11424],
  [12769, 24894, 19235, 8009, 31709, 14434, 29970, 4044, 17130, 6219, 7241],
  [26606, 18521, 2161, 8210, 27215, 3793, 6684, 32454, 5841, 27576, 10258],
  [30691, 23070, 12567, 12598, 18673, 1262, 22866, 27192, 5344, 345, 739],
  [32266, 26427, 30521, 27706, 26470, 13941, 11121, 3950, 23694, 12112, 21170],
  [25329, 13937, 29430, 647, 13390, 15132, 25169, 19256, 18964, 27776, 3013],
  [28420, 26068, 19290, 3402, 13865, 13972, 1195, 7510, 11548, 7930, 21882],
  [24981, 25590, 28227, 17062, 12961, 4859, 30197, 7903, 25098, 7200, 53],
  [839, 19819, 20844, 6822, 5069, 15939, 9170, 14834, 17906, 8654, 31859],
  [4759, 12931, 15757, 8763, 20509, 10457, 17585, 25993, 31660, 12544, 29722],
  [7500, 28443, 8415, 22355, 27120, 23466, 25808, 25527, 18554, 21933, 23086],
  [10779, 25419, 9636, 26746, 2240, 7322, 5803, 8077, 1005, 18351, 11408],
  [23772, 30491, 13210, 15805, 18918, 2987, 6971, 9940, 25429, 19567, 14996],
  [20037, 26420, 11458, 12411, 25716, 14968, 13031, 27904, 18075, 3912, 19135],
  [12704, 10757, 6266, 3641, 24770, 25906, 11907, 8611, 26520, 29662, 14324],
  [10226, 25558, 31699, 27498, 27272, 31929, 27761, 14309, 9704, 2323, 27649],
  [9430, 11566, 23931, 23491, 24033, 28349, 21454, 16732, 4947, 23330, 6580],
  [27800, 10825, 24184, 1673, 26175, 4324, 29798, 20835, 30872, 18449, 24289],
  [14486, 11348, 835, 13553, 3903, 2436, 31959, 26505, 6285, 5481, 21758],
  [21940, 8040, 19776, 17397, 6708, 11763, 6559, 22025, 20683, 17063, 23019],
  [5884, 3847, 10883, 24995, 22578, 17896, 5925, 29374, 27830, 3765, 7518],
  [22127, 26317, 10766, 27203, 8029, 27013, 29539, 419, 28879, 26934, 8615],
  [1004, 6269, 26243, 28396, 1958, 12690, 32731, 5816, 8248, 24037, 7770],
  [32124, 5360, 23795, 27944, 19891, 12789, 9392, 23144, 2254, 670, 3572],
  [24398, 12260, 27282, 31291, 3878, 15804, 25641, 5237, 19205, 6657, 7323],
  [22707, 18717, 7, 2200, 8957, 6522, 25737, 15098, 13550, 11569, 26699],
  [26923, 12898, 25142, 22082, 32408, 8508, 21785, 16064, 21656, 31773, 4722],
  [31345, 5021, 5098, 28394, 1885, 31152, 11908, 32535, 9822, 15301, 27311],
  [5584, 16326, 1179, 24912, 23817, 19513, 11516, 29534, 10292, 28180, 25432],
  [2379, 24396, 14072, 15025, 24414, 21206, 17085, 17528, 9765, 4064, 16558],
  [15749, 11676, 5604, 15343, 5201, 25850, 22335, 31660, 4961, 8181, 18720],
  [24961, 13743, 13324, 16706, 5046, 9592, 14372, 7861, 20976, 9269, 24370],
  [5907, 17538, 12693, 17380, 26558, 27446, 18105, 4521, 1154, 14895, 30634],
  [1006, 7805, 31591, 4285, 4641, 19005, 2295, 14038, 24777, 5657, 18558],
  [18900, 25779, 11341, 17201, 21147, 32604, 14296, 32359, 25692, 22379, 18145],
  [2267, 8958, 7005, 31023, 28180, 5253, 22369, 11323, 17998, 308, 3623],
  [27561, 4303, 8460, 6049, 23294, 9320, 4004, 8876, 8876, 2471, 12552],
  [31872, 6855, 5957, 18618, 26290, 8487, 28907, 5885, 26328, 31976, 29792],
  [9897, 9041, 8576, 14033, 31767, 29039, 15757, 21942, 18417, 4659, 18123],
  [3556, 31984, 17206, 31890, 16060, 1824, 26335, 14377, 13657, 23345, 19741],
  [19463, 7644, 486, 22843, 13715, 29993, 218, 10036, 28421, 9168, 19523],
  [21633, 25933, 31494, 25726, 22549, 18471, 5985, 22468, 5581, 14875, 1869],
  [23584, 23945, 25252, 23010, 15383, 7816, 31009, 15061, 30006, 30836, 21031],
  [28062, 18634, 18572, 9863, 11792, 31405, 8987, 24093, 12372, 12218, 23441],
  [25951, 9770, 7205, 7404, 14289, 20931, 29999, 17188, 11922, 20792, 13993],
  [26978, 20744, 23304, 6335, 16374, 22995, 93, 3379, 27910, 11911, 5190],
  [21575, 24252, 31309, 32566, 23026, 26084, 3971, 800, 6369, 17285, 3494],
  [19738, 31952, 2650, 11675, 23275, 6839, 25839, 14014, 9731, 22039, 6291],
  [25291, 26721, 15997, 258, 9147, 28843, 14787, 14733, 6514, 26916, 28505],
  [9370, 15993, 4163, 24626, 14418, 23671, 31751, 11790, 15785, 22913, 32048],
  [17827, 20997, 15750, 29697, 3220, 1801, 5731, 25461, 24332, 32040, 28971],
  [23994, 18341, 12260, 2625, 32045, 17545, 30122, 19303, 24998, 28385, 30592],
  [17170, 1875, 28479, 4677, 30973, 8729, 27333, 16815, 613, 16279, 10361],
  [27784, 26558, 3012, 31250, 23193, 21080, 16525, 18090, 12000, 24042, 8668],
  [25935, 22509, 2203, 10664, 1406, 5015, 27951, 25255, 16895, 30305, 16273],
  [13000, 25159, 13085, 28210, 28373, 2040, 16250, 7524, 30062, 23357, 11469],
  [30269, 15692, 11451, 19043, 10368, 5205, 29463, 4008, 24689, 8535, 9258],
  [16408, 15963, 18928, 1962, 14169, 4761, 21012, 24210, 22283, 12146, 18207],
  [4142, 2581, 15835, 19728, 10020, 4176, 9864, 3131, 3751, 32288, 13165],
  [13328, 19222, 18276, 46, 29777, 5914, 21586, 30947, 24254, 25882, 13035],
  [11823, 28796, 13636, 7728, 14763, 6337, 14390, 659, 17313, 13677, 21574]]

def prodRow0Bal11Weights : List Nat := [
  17090, 18108, 12883, 15285, 19921, 19486, 17870, 17885,
  14326, 13973, 17834, 17142, 16091, 20046, 14737, 20123,
  15026, 13035, 14663, 19596, 13365, 18038, 17822, 18370,
  13834, 17347, 17954, 18889, 13442, 17418, 20007, 16876,
  13257, 18691, 15677, 16542, 17507, 16566, 12996, 12681,
  17942, 17880, 19228, 18885, 15443, 15406, 15128, 18729,
  13092, 16734, 18216, 12773, 16123, 15578, 13067, 18241,
  16005, 18476, 17918, 19142, 16952, 18622, 17278, 14349]

theorem prodRow0Bal11Weights_eq :
    prodRow0Bal11Taps.map oddTapWeight = prodRow0Bal11Weights := by decide +kernel

private theorem prodRow0Bal11_ok :
    (prodRow0Bal11Taps.all (fun ts =>
      decide (ts.length = 11) && ts.all (fun a => decide (a < 32768)) &&
        decide (imbalance 32768 (oddTapWeight ts) ≤ 7593))) = true := by
  decide +kernel

private theorem map_leafWeight_eq_oddTapWeight :
    ∀ row : List (List Nat),
      (row.all (fun ts => decide (ts.length = 11) && ts.all (fun a => decide (a < 32768)))) = true →
      (row.map tapFn).map (leafWeight 32768) = row.map oddTapWeight
  | [], _ => rfl
  | ts :: rest, h => by
    rw [List.all_cons, Bool.and_eq_true, Bool.and_eq_true] at h
    simp only [List.map_cons]
    rw [elevenTap_weight 32768 ts (of_decide_eq_true h.1.1)
          (fun a ha => of_decide_eq_true (List.all_eq_true.mp h.1.2 a ha)),
        map_leafWeight_eq_oddTapWeight rest h.2]

/-- Row 0 of the deployed 11-tap balanced generator satisfies `imbalance ≤ 7593` on all 64 trees
    and has exact regular-noise parity bias strictly between `2^-220` and `2^-219` (`< 2^-135`). -/
theorem prodRow0Bal11_bias_bracket :
    prodRow0Bal11Taps.length = 64 ∧
    (∀ w ∈ prodRow0Bal11Weights, imbalance 32768 w ≤ 7593) ∧
    (noiseSignedSum 32768 (prodRow0Bal11Taps.map tapFn) false).natAbs =
      imbalanceProd 32768 prodRow0Bal11Weights ∧
    imbalanceProd 32768 prodRow0Bal11Weights * 2 ^ 219 < 32768 ^ 64 ∧
    32768 ^ 64 < imbalanceProd 32768 prodRow0Bal11Weights * 2 ^ 220 ∧
    (noiseSignedSum 32768 (prodRow0Bal11Taps.map tapFn) false).natAbs * 2 ^ 135 < 32768 ^ 64 := by
  have hCount : (noiseSignedSum 32768 (prodRow0Bal11Taps.map tapFn) false).natAbs =
      imbalanceProd 32768 prodRow0Bal11Weights := by
    rw [piling_up_signed_count,
        map_leafWeight_eq_oddTapWeight prodRow0Bal11Taps (by decide +kernel),
        prodRow0Bal11Weights_eq]
  refine ⟨by decide +kernel, by decide +kernel, hCount,
          by decide +kernel, by decide +kernel, ?_⟩
  rw [hCount]; decide +kernel

theorem inhabited_elevenTap_balanced :
    ∃ row : List (List Nat),
      row.length = 64 ∧
      ∀ ts ∈ row, ts.length = 11 ∧ (∀ a ∈ ts, a < 32768) ∧ imbalance 32768 (oddTapWeight ts) ≤ 7593 := by
  refine ⟨prodRow0Bal11Taps, by decide +kernel, fun ts hts => ?_⟩
  have h := List.all_eq_true.mp prodRow0Bal11_ok ts hts
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.1.1,
         fun a ha => of_decide_eq_true (List.all_eq_true.mp h.1.2 a ha),
         of_decide_eq_true h.2⟩

/-! ## 4. Geometric tails -/

/-- `rho z0 + rho (z0 + 1) + … + rho (z0 + n − 1)`. -/
def tailSum (rho : Nat → Nat) (z0 : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => tailSum rho z0 n + rho (z0 + n)

theorem geometric_tail_invariant (rho : Nat → Nat) (A B z0 : Nat) (hAB : A ≤ B)
    (hRatio : ∀ z, z0 ≤ z → rho (z + 1) * B ≤ rho z * A) :
    ∀ n : Nat, tailSum rho z0 n * (B - A) + rho (z0 + n) * B ≤ rho z0 * B
  | 0 => by
    show 0 * (B - A) + rho z0 * B ≤ rho z0 * B
    rw [Nat.zero_mul, Nat.zero_add]; exact Nat.le_refl _
  | n + 1 => by
    have ih := geometric_tail_invariant rho A B z0 hAB hRatio n
    have hr := hRatio (z0 + n) (Nat.le_add_right z0 n)
    have e : rho (z0 + n) * (B - A) + rho (z0 + n) * A = rho (z0 + n) * B := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hAB]
    show (tailSum rho z0 n + rho (z0 + n)) * (B - A) + rho (z0 + n + 1) * B ≤ rho z0 * B
    rw [Nat.add_mul]
    have h1 : tailSum rho z0 n * (B - A) + rho (z0 + n) * (B - A) + rho (z0 + n + 1) * B ≤
        tailSum rho z0 n * (B - A) + rho (z0 + n) * (B - A) + rho (z0 + n) * A :=
      Nat.add_le_add_left hr _
    have h2 : tailSum rho z0 n * (B - A) + rho (z0 + n) * (B - A) + rho (z0 + n) * A =
        tailSum rho z0 n * (B - A) + rho (z0 + n) * B := by rw [Nat.add_assoc, e]
    exact Nat.le_trans h1 (Nat.le_trans (Nat.le_of_eq h2) ih)

/-- **Geometric tail domination.** If consecutive weights beyond `z0` shrink by at least the
factor `A / B`, every finite tail from `z0` is at most `B / (B − A)` times `rho z0`. -/
theorem geometric_tail_domination (rho : Nat → Nat) (A B z0 : Nat) (hAB : A ≤ B)
    (hRatio : ∀ z, z0 ≤ z → rho (z + 1) * B ≤ rho z * A) (n : Nat) :
    tailSum rho z0 n * (B - A) ≤ rho z0 * B :=
  Nat.le_trans (Nat.le_add_right _ _) (geometric_tail_invariant rho A B z0 hAB hRatio n)

/-- The same at `2σ² = 980000` (`rlweGaussianTwoSigmaSq`, `σ = 700`), with the ratio
`980000 / (980000 + 2·z0 + 1)`: every tail from `z0` is at most
`(980000 + 2·z0 + 1) / (2·z0 + 1)` times `rho z0`. -/
theorem gaussian_sigma700_tail_domination (rho : Nat → Nat) (z0 : Nat)
    (hRatio : ∀ z, z0 ≤ z →
      rho (z + 1) * (rlweGaussianTwoSigmaSq + (2 * z0 + 1)) ≤ rho z * rlweGaussianTwoSigmaSq)
    (n : Nat) :
    tailSum rho z0 n * (2 * z0 + 1) ≤ rho z0 * (980000 + (2 * z0 + 1)) := by
  have hS : rlweGaussianTwoSigmaSq = 980000 := rlwe_24rep_pq128_soundness_bits.2.2.2
  rw [hS] at hRatio
  have h := geometric_tail_domination rho 980000 (980000 + (2 * z0 + 1)) z0
    (Nat.le_add_right _ _) hRatio n
  rw [Nat.add_sub_cancel_left] at h
  exact h

/-- A ratio hypothesis that is too weak gives nothing: constant weights have unbounded tails. -/
theorem tooth_constant_weights_tail_unbounded :
    ∃ (rho : Nat → Nat) (n : Nat), ¬ (tailSum rho 3070 n * (2 * 3070 + 1) ≤
      rho 3070 * (980000 + (2 * 3070 + 1))) :=
  ⟨fun _ => 1, 161, by decide +kernel⟩

/-! ## 5. Witnesses -/

theorem inhabited_heterogeneous_bias_lt :
    ∃ (N : Nat) (gs : List (Nat → Bool)) (bs : List Nat) (k : Nat),
      BlocksBounded N (gs.map (leafWeight N)) bs ∧ natProd bs * 2 ^ k < N ^ gs.length :=
  ⟨4, [tapFn [0, 1, 2]], [2], 0,
    (show imbalance 4 (leafWeight 4 (tapFn [0, 1, 2])) ≤ 2 ∧ True from ⟨by decide, trivial⟩),
    by decide⟩

theorem inhabited_balanced_blocks_special_case :
    ∃ ws : List Nat, ws.length = 64 ∧ ∀ w ∈ ws, imbalance 32768 w ≤ 2047 :=
  ⟨List.replicate 64 16384, by decide +kernel, by decide +kernel⟩

theorem inhabited_row_signed_count :
    ∃ (N : Nat) (taps : List (Nat × Nat × Nat)), tapsBelow N taps = true :=
  ⟨32768, prodRow0Taps, by decide +kernel⟩

/-- All weight on `z = 0`. -/
def pointMass (z : Nat) : Nat := if z = 0 then 1 else 0

/-- For `pointMass` every later ratio is zero and the tail is that one weight. -/
theorem inhabited_gaussian_sigma700_tail_domination :
    ∃ (rho : Nat → Nat) (z0 : Nat), (∀ z, z0 ≤ z →
      rho (z + 1) * (rlweGaussianTwoSigmaSq + (2 * z0 + 1)) ≤ rho z * rlweGaussianTwoSigmaSq) ∧
      tailSum rho z0 1 = 1 := by
  refine ⟨pointMass, 0, fun z _ => ?_, by rfl⟩
  show 0 * _ ≤ _
  rw [Nat.zero_mul]; exact Nat.zero_le _

theorem inhabited_geometric_tail_domination :
    ∃ (rho : Nat → Nat) (A B z0 : Nat), A ≤ B ∧
      (∀ z, z0 ≤ z → rho (z + 1) * B ≤ rho z * A) ∧ tailSum rho z0 1 = 1 := by
  refine ⟨pointMass, 1, 2, 0, by decide, fun z _ => ?_, by rfl⟩
  show 0 * 2 ≤ _
  exact Nat.zero_le _

/-- Block bounds without the numeric premise give no bias bound: one tree of four leaves whose
test is constant has bias 1. -/
theorem tooth_block_bounds_alone_give_no_bias_bound :
    ∃ (gs : List (Nat → Bool)) (bs : List Nat), BlocksBounded 4 (gs.map (leafWeight 4)) bs ∧
      ¬ ((noiseSignedSum 4 gs false).natAbs * 2 ^ 1 < 4 ^ gs.length) :=
  ⟨[fun _ => false], [4],
    (show imbalance 4 (leafWeight 4 (fun _ => false)) ≤ 4 ∧ True from ⟨by decide, trivial⟩),
    by decide⟩

/-! ## Audits

The audit commands read proof bodies, which a module does not export, so they run here. -/

#verify_constructive piling_up_signed_count
#verify_constructive noiseSignedSum_trivial
#verify_constructive heterogeneous_bias_lt
#verify_constructive balanced_blocks_special_case
#verify_constructive threeTap_weight
#verify_constructive row_signed_count
#verify_constructive prodRow0_bias_exact
#verify_constructive prodRow0_bias_bracket
#verify_constructive prodRow0_squared_bias_bracket
#verify_constructive prodRow0_balance_premise_fails
#verify_constructive prodRow0_bias_not_lt_two_neg_256
#verify_constructive prodRow0_heterogeneous_instance
#verify_constructive oddTap_weight
#verify_constructive elevenTap_weight
#verify_constructive regularRates_parityBias_bridge
#verify_constructive elevenTap_balanced_all_rows_bias_lt_two_neg_135
#verify_constructive tooth_elevenTap_unfiltered_tail_exceeds_two_neg_135
#verify_constructive prodRow0Bal11_bias_bracket
#verify_constructive tooth_unbalanced_blocks_exceed_two_neg_256
#verify_constructive geometric_tail_domination
#verify_constructive gaussian_sigma700_tail_domination
#verify_constructive tooth_constant_weights_tail_unbounded
#verify_constructive tooth_block_bounds_alone_give_no_bias_bound

#verify_inhabited heterogeneous_bias_lt inhabited_heterogeneous_bias_lt
#verify_inhabited balanced_blocks_special_case inhabited_balanced_blocks_special_case
#verify_inhabited row_signed_count inhabited_row_signed_count
#verify_inhabited elevenTap_balanced_all_rows_bias_lt_two_neg_135 inhabited_elevenTap_balanced
#verify_inhabited geometric_tail_domination inhabited_geometric_tail_domination
#verify_inhabited gaussian_sigma700_tail_domination inhabited_gaussian_sigma700_tail_domination

#tooth_pair heterogeneous_bias_lt vs tooth_block_bounds_alone_give_no_bias_bound
#tooth_pair balanced_blocks_special_case vs tooth_unbalanced_blocks_exceed_two_neg_256
#tooth_pair balanced_blocks_special_case vs prodRow0_bias_not_lt_two_neg_256
#tooth_pair prodRow0_bias_bracket vs prodRow0_bias_not_lt_two_neg_256
#tooth_pair elevenTap_balanced_all_rows_bias_lt_two_neg_135 vs tooth_elevenTap_unfiltered_tail_exceeds_two_neg_135
#tooth_pair gaussian_sigma700_tail_domination vs tooth_constant_weights_tail_unbounded
#tooth_pair geometric_tail_domination vs tooth_constant_weights_tail_unbounded

end Qsag.TapRowBias
