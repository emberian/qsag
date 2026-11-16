module
/-
# Qsag.Math.TapRowParityBias — parity bias of a regular-noise linear test, block by block

`pcg_dense_dual_lpn_linear_bias_lt_two_neg_256` (`Qsag/Math/Lattices.lean`) bounds the bias of
a 64-block regular-noise parity by `2^-256` under the premise that every block is balanced to
within `2047 / 32768`. That premise is false for a row of the deployed tap generator. This
module removes the premise and evaluates the row.

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
#verify_constructive tooth_unbalanced_blocks_exceed_two_neg_256
#verify_constructive geometric_tail_domination
#verify_constructive gaussian_sigma700_tail_domination
#verify_constructive tooth_constant_weights_tail_unbounded
#verify_constructive tooth_block_bounds_alone_give_no_bias_bound

#verify_inhabited heterogeneous_bias_lt inhabited_heterogeneous_bias_lt
#verify_inhabited balanced_blocks_special_case inhabited_balanced_blocks_special_case
#verify_inhabited row_signed_count inhabited_row_signed_count
#verify_inhabited geometric_tail_domination inhabited_geometric_tail_domination
#verify_inhabited gaussian_sigma700_tail_domination inhabited_gaussian_sigma700_tail_domination

#tooth_pair heterogeneous_bias_lt vs tooth_block_bounds_alone_give_no_bias_bound
#tooth_pair balanced_blocks_special_case vs tooth_unbalanced_blocks_exceed_two_neg_256
#tooth_pair balanced_blocks_special_case vs prodRow0_bias_not_lt_two_neg_256
#tooth_pair prodRow0_bias_bracket vs prodRow0_bias_not_lt_two_neg_256
#tooth_pair gaussian_sigma700_tail_domination vs tooth_constant_weights_tail_unbounded
#tooth_pair geometric_tail_domination vs tooth_constant_weights_tail_unbounded

end Qsag.TapRowBias
