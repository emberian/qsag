module
/-
# Qsag.Protocol.Threshold.Rss256TernaryRound — `PassWeights` Batching & `b`-Bit Ternary Frobenius-Basis Round

Constructive (`0 Classical.choice`, `0 sorry`) mechanization of the core algebraic components of
`product_proof` in `crates/qsag-core/src/rss256.rs` (`lines 45-81, 868-976, 2412-2574`):

1. **`PassWeights` Half-Plane Batching (`passWeight_eq_towerPow`, `passBatching_false_bad_coins_le`)**:
   Gate planes are grouped `GROUP_PLANES = 128` (`2^7`) at a time and each 256-lane plane splits into
   two 128-lane half-planes (`B = 256 * groups` blocks total), packed into `Tower128` (`GF(2^{128})`)
   and weighted by `(chi^128)^j * chi^u = chi^(128 * j + u)`. Any corrupted gate message creates a
   nonzero degree-`< B` polynomial in `chi`, vanishing on at most `B` challenges in `S`.
2. **`b`-Bit Ternary `{0, 1, slope}^b` Frobenius-Basis Multiquadratic Round (`nextClaim_honest_complete`,
   `honestFold_nextClaim_false_bad_coins_le`, `#tooth` `tooth_honestFold_nextClaim_unlocked_s0_forges_all`)**:
   Both the `TENSOR_BITS = 7` plane-binding round (`3^7 = 2187` points, `w(u) = chi^u`) and every
   `b`-bit vector-folding round (`b ≤ FOLD_BITS = 4`, `3^b ≤ 81` points, `w(u) = 1`) interpolate
   with `basis(0, γ) = 1 + γ`, `basis(1, γ) = γ`, and `basis(2, γ) = towerFrobeniusPoly 7 γ = γ + γ^2`
   while locking `s(0)` from `claim`. By inductive `b`-variate degree-`(2, …, 2)` Schwartz–Zippel
   root counting over `Tower128`, a false incoming claim survives on at most `ternaryBadBound |S| b`
   (`ternaryBadBound |S| b * |S| = 2 * b * |S|^b`) challenge tuples (`14` for `TENSOR_BITS = 7` and
   `≤ 8` per folding round).
-/

public import Qsag.Tactic.Prelude
public import Qsag.Math.Goldilocks
public import Qsag.Math.Gf2Pow128
public import Qsag.Protocol.Aggregation.UcGames
public import Qsag.Protocol.Threshold.MaliciousSecurity


import Qsag.Tactic.AssuranceKit

public section
namespace Qsag
namespace Rss256ProductProof

set_option autoImplicit false
set_option maxRecDepth 8192

instance instAssocTowerAdd7 : Std.Associative (towerAdd 7) := ⟨towerAdd_assoc 7⟩
instance instCommTowerAdd7 : Std.Commutative (towerAdd 7) := ⟨towerAdd_comm 7⟩
instance instAssocTowerMul7 : Std.Associative (towerMul 7) := ⟨towerMul_assoc 7⟩
instance instCommTowerMul7 : Std.Commutative (towerMul 7) := ⟨towerMul_comm 7⟩

/-! ## 1. `Tower128` Powers, Quadratic Non-Vanishing & `PassWeights` Half-Plane Batching -/

@[expose] def TENSOR_BITS : Nat := 7
@[expose] def GROUP_PLANES : Nat := 128
@[expose] def FOLD_BITS : Nat := 4
def FIRST_FOLD_BITS : Nat := 2
def BLOCK_LANES : Nat := 128

/-- Multiplicative powers `a^n` in `Tower128` (`GF(2^{128})`). -/
def towerPow128 (a : Tower128) : Nat → Tower128
  | 0 => towerOne 7
  | n + 1 => towerMul 7 (towerPow128 a n) a

theorem towerPow128_add (a : Tower128) (m n : Nat) :
    towerPow128 a (m + n) = towerMul 7 (towerPow128 a m) (towerPow128 a n) := by
  induction n with
  | zero =>
    rw [Nat.add_zero, towerPow128, towerMul_one]
  | succ n ih =>
    rw [Nat.add_succ, towerPow128, towerPow128, ih, towerMul_assoc]

theorem towerPow128_mul (a : Tower128) (m j : Nat) :
    towerPow128 (towerPow128 a m) j = towerPow128 a (m * j) := by
  induction j with
  | zero =>
    rw [Nat.mul_zero, towerPow128, towerPow128]
  | succ j ih =>
    rw [Nat.mul_succ, towerPow128, ih, towerPow128_add]

/-- `PassWeights::new(chi, blocks)` (`rss256.rs:950-976`):
    plane `u < 128` gets `chi^u`, block `j < blocks` gets `(chi^128)^j`, and their product at
    half-plane index `J = 128 * j + u` equals `chi^(128 * j + u)`. -/
def passPlaneWeight (chi : Tower128) (u : Nat) : Tower128 :=
  towerPow128 chi u

def passBlockWeight (chi : Tower128) (j : Nat) : Tower128 :=
  towerPow128 (towerPow128 chi GROUP_PLANES) j

theorem passWeight_eq_towerPow (chi : Tower128) (j u : Nat) :
    towerMul 7 (passBlockWeight chi j) (passPlaneWeight chi u) =
      towerPow128 chi (GROUP_PLANES * j + u) := by
  unfold passBlockWeight passPlaneWeight
  rw [towerPow128_mul, ← towerPow128_add]

/-- Flat ternary index `boolean_point(u, bits) = ∑_{l < bits} ((u >> l) & 1) * 3^l` (`rss256.rs:889-897`). -/
def booleanPoint : Nat → Nat → Nat
  | 0, _ => 0
  | b + 1, u => (u % 2) + 3 * booleanPoint b (u / 2)

theorem booleanPoint_zero (b : Nat) : booleanPoint b 0 = 0 := by
  induction b with
  | zero => rfl
  | succ b ih =>
    simp only [booleanPoint, Nat.zero_mod, Nat.zero_div, ih, Nat.mul_zero]

theorem booleanPoint_lt_pow3 (b : Nat) : ∀ u : Nat, booleanPoint b u < 3 ^ b := by
  induction b with
  | zero =>
    intro _
    exact Nat.zero_lt_one
  | succ b ih =>
    intro u
    have hMod : u % 2 < 2 := Nat.mod_lt u (by decide)
    have hSub := ih (u / 2)
    have hPow : 3 ^ (b + 1) = 3 * 3 ^ b := by rw [Nat.pow_succ, Nat.mul_comm]
    simp only [booleanPoint, hPow]
    omega

/-- Any nonzero degree-`≤ 2` polynomial `[c0, c1, c2]` over `Tower128` fails to vanish at one of
    `0`, `1`, or `towerX 7`, so its root count in ANY `Nodup` list `S` is `≤ 2` unconditionally. -/
theorem exists_eval_nonzero_quadratic_tower128 (c0 c1 c2 : Tower128)
    (hNe : c0 ≠ towerZero 7 ∨ c1 ≠ towerZero 7 ∨ c2 ≠ towerZero 7) :
    ∃ x : Tower128, RoundPoly.evalCoeffs [c0, c1, c2] x ≠ CommRingOps.zero := by
  by_cases h0 : RoundPoly.evalCoeffs [c0, c1, c2] (towerZero 7) = CommRingOps.zero
  · have hc0 : c0 = towerZero 7 := by
      change towerAdd 7 c0 (towerMul 7 (towerZero 7) _) = towerZero 7 at h0
      simpa only [towerZero_mul, towerAdd_zero] using h0
    by_cases h1 : RoundPoly.evalCoeffs [c0, c1, c2] (towerOne 7) = CommRingOps.zero
    · have hc12 : c1 = c2 := by
        change towerAdd 7 c0 (towerMul 7 (towerOne 7)
          (towerAdd 7 c1 (towerMul 7 (towerOne 7)
            (towerAdd 7 c2 (towerMul 7 (towerOne 7) (towerZero 7)))))) = towerZero 7 at h1
        simp only [hc0, towerMul_zero, towerAdd_zero, towerOne_mul, towerZero_add] at h1
        have hAdd := congrArg (fun z => towerAdd 7 z c2) h1
        simpa only [towerAdd_assoc, towerAdd_self_zero, towerAdd_zero, towerZero_add] using hAdd
      refine ⟨towerX 7, ?_⟩
      intro hX
      change towerAdd 7 c0 (towerMul 7 (towerX 7)
        (towerAdd 7 c1 (towerMul 7 (towerX 7)
          (towerAdd 7 c2 (towerMul 7 (towerX 7) (towerZero 7)))))) = towerZero 7 at hX
      simp only [hc0, hc12, towerMul_zero, towerAdd_zero, towerZero_add] at hX
      have hFac : towerAdd 7 c2 (towerMul 7 (towerX 7) c2) =
          towerMul 7 (towerAdd 7 (towerOne 7) (towerX 7)) c2 := by
        rw [towerAdd_mul_distrib, towerOne_mul]
      rw [hFac] at hX
      have hXNe0 : towerX 7 ≠ towerZero 7 := by decide
      have h1XNe0 : towerAdd 7 (towerOne 7) (towerX 7) ≠ towerZero 7 := by decide
      rcases (towerMul_eq_zero_iff 7 _ _).mp hX with hBadX | hNext
      · exact hXNe0 hBadX
      · rcases (towerMul_eq_zero_iff 7 _ _).mp hNext with hBad1X | hc2
        · exact h1XNe0 hBad1X
        · rcases hNe with h | h | h
          · exact h hc0
          · exact h (hc12.trans hc2)
          · exact h hc2
    · exact ⟨towerOne 7, h1⟩
  · exact ⟨towerZero 7, h0⟩

theorem evalCoeffs3_eq (c0 c1 c2 x : Tower128) :
    RoundPoly.evalCoeffs [c0, c1, c2] x =
      towerAdd 7 c0 (towerMul 7 x (towerAdd 7 c1 (towerMul 7 x c2))) := by
  change towerAdd 7 c0 (towerMul 7 x (towerAdd 7 c1 (towerMul 7 x
    (towerAdd 7 c2 (towerMul 7 x (towerZero 7)))))) = _
  rw [towerMul_zero, towerAdd_zero]

theorem quadratic_roots_le_two_tower128 (c0 c1 c2 : Tower128) (S : List Tower128) (hS : S.Nodup)
    (hNe : c0 ≠ towerZero 7 ∨ c1 ≠ towerZero 7 ∨ c2 ≠ towerZero 7) :
    (S.filter (fun x => decide (RoundPoly.evalCoeffs [c0, c1, c2] x = towerZero 7))).length ≤ 2 := by
  have hLen : ([c0, c1, c2] : List Tower128).length ≤ 2 + 1 := Nat.le_refl 3
  exact RoundPoly.roots_nodup_length_le 2 [c0, c1, c2] S hS hLen
    (exists_eval_nonzero_quadratic_tower128 c0 c1 c2 hNe)

/-- A coefficient list of length `≤ L + 1` with a nonzero entry is nonzero at some point of any
    duplicate-free domain of size `≥ L + 1` (contrapositive of `poly_coeffs_zero_of_vanish_nodup`). -/
theorem exists_eval_nonzero_of_coeff_nonzero
    {R : Type} [LawfulCommRing R] [DecidableEq R] [NoZeroDivisors R]
    (L : Nat) (cs S : List R)
    (hNodup : S.Nodup) (hCsLen : cs.length ≤ L + 1) (hDom : L + 1 ≤ S.length)
    (hNonzero : ∃ c ∈ cs, c ≠ CommRingOps.zero) :
    ∃ x₀ : R, RoundPoly.evalCoeffs cs x₀ ≠ CommRingOps.zero := by
  have hScan : ∀ xs : List R,
      (∃ x₀ : R, RoundPoly.evalCoeffs cs x₀ ≠ CommRingOps.zero) ∨
        (∀ r ∈ xs, RoundPoly.evalCoeffs cs r = CommRingOps.zero) := by
    intro xs
    induction xs with
    | nil => exact Or.inr (fun _ hm => nomatch hm)
    | cons x xs ih =>
      by_cases hx : RoundPoly.evalCoeffs cs x = CommRingOps.zero
      · rcases ih with hEx | hAll
        · exact Or.inl hEx
        · refine Or.inr (fun r hr => ?_)
          rcases List.mem_cons.mp hr with rfl | hTl
          · exact hx
          · exact hAll r hTl
      · exact Or.inl ⟨x, hx⟩
  rcases hScan (S.take (L + 1)) with hEx | hAll
  · exact hEx
  · exfalso
    obtain ⟨d, hdMem, hdNe⟩ := hNonzero
    have hTakeLen : (S.take (L + 1)).length = L + 1 := List.length_take_of_le hDom
    have hNdTake : (S.take (L + 1)).Nodup := (List.take_sublist (L + 1) S).nodup hNodup
    have hZeroAll := poly_coeffs_zero_of_vanish_nodup (S.take (L + 1)) cs hNdTake
      (by rw [hTakeLen]; exact hCsLen) hAll
    exact hdNe (hZeroAll d hdMem)

/-- Batching root bound for `PassWeights` (`rss256.rs:50-55`):
    Given `blocks : List Tower128` of `≤ B` 128-bit half-plane error blocks (`1 ≤ B ≤ S.length`)
    containing at least one nonzero gate-message error, at most `B` challenges `chi ∈ S` cancel
    `RoundPoly.evalCoeffs blocks chi = 0` (in fact `≤ B - 1 ≤ B`). -/
theorem passBatching_false_bad_coins_le (B : Nat) (blocks S : List Tower128)
    (hS : S.Nodup) (hBPos : 1 ≤ B) (hLen : blocks.length ≤ B) (hDom : B ≤ S.length)
    (hErr : ∃ e ∈ blocks, e ≠ towerZero 7) :
    (S.filter (fun chi => decide (RoundPoly.evalCoeffs blocks chi = towerZero 7))).length ≤ B := by
  have hLenSub : blocks.length ≤ (B - 1) + 1 := by omega
  have hDomSub : (B - 1) + 1 ≤ S.length := by omega
  have hNz : ∃ c ∈ blocks, c ≠ CommRingOps.zero := hErr
  have hEx := exists_eval_nonzero_of_coeff_nonzero (B - 1) blocks S hS hLenSub hDomSub hNz
  have hCount := RoundPoly.roots_nodup_length_le (B - 1) blocks S hS hLenSub hEx
  exact Nat.le_trans hCount (by omega)

/-! ## 2. Finite Counting Combinators (`0 Classical.choice`) -/

theorem flatMap_map_len {α β γ : Type} (ys : List β) (f : α → β → γ) (xs : List α) :
    (xs.flatMap (fun x => ys.map (f x))).length = xs.length * ys.length := by
  induction xs with
  | nil => simp only [List.flatMap_nil, List.length_nil, Nat.zero_mul]
  | cons _ xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_map, ih,
      List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm]

theorem filter_flatMap_len {α β : Type} (f : α → List β) (p : β → Bool) (xs : List α) :
    ((xs.flatMap f).filter p).length = (xs.map (fun x => ((f x).filter p).length)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.filter_append, List.length_append,
      List.map_cons, List.sum_cons, ih]

theorem filter_map_len {α β : Type} (f : α → β) (p : β → Bool) (xs : List α) :
    ((xs.map f).filter p).length = (xs.filter (fun x => p (f x))).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.filter_cons]
    cases p (f x) <;> simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons, ih]

theorem filter_len_le_of_imp {α : Type} (p q : α → Bool)
    (h : ∀ x, p x = true → q x = true) (xs : List α) :
    (xs.filter p).length ≤ (xs.filter q).length := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    simp only [List.filter_cons]
    cases hp : p x
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases q x <;> simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega
    · simp only [↓reduceIte, h x hp, List.length_cons]
      omega

theorem sum_map_le_split {α : Type} (bad : α → Bool) (w : α → Nat) (hi lo : Nat)
    (hHi : ∀ x, bad x = true → w x ≤ hi)
    (hLo : ∀ x, bad x = false → w x ≤ lo) (xs : List α) :
    (xs.map w).sum ≤ (xs.filter bad).length * hi + xs.length * lo := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.filter_cons, List.length_cons]
    cases hb : bad x
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_mul, Nat.one_mul]
      have hx := hLo x hb
      omega
    · simp only [↓reduceIte, List.length_cons, Nat.add_mul, Nat.one_mul]
      have hx := hHi x hb
      omega

/-! ## 3. `b`-Bit Ternary `{0, 1, slope}^b` Frobenius-Basis Multiquadratic Round -/

/-- Length-`b` challenge tuple over `Tower128`. -/
inductive ChallengeTuple : Nat → Type where
  | nil : ChallengeTuple 0
  | cons : {b : Nat} → Tower128 → ChallengeTuple b → ChallengeTuple (b + 1)

/-- Binary hypercube table `{0, 1}^b → α` (`2^b` entries). -/
inductive BTree (α : Type) : Nat → Type where
  | leaf : α → BTree α 0
  | branch : {b : Nat} → BTree α b → BTree α b → BTree α (b + 1)
  deriving DecidableEq

/-- Ternary table `{0, 1, slope}^b → α` (`3^b` entries, matching `ternary_expand` in `rss256.rs:868`). -/
inductive TTree (α : Type) : Nat → Type where
  | leaf : α → TTree α 0
  | branch : {b : Nat} → TTree α b → TTree α b → TTree α b → TTree α (b + 1)
  deriving DecidableEq

abbrev BoolWeights (b : Nat) := BTree Tower128 b
abbrev Vec128 (n : Nat) := BTree Tower128 n
abbrev TernaryTab (b : Nat) := TTree Tower128 b

/-- Enumerate all `|S|^b` challenge tuples over `S` (outer `rest`, inner `g` for univariate slicing). -/
@[expose] def challengeTuples (S : List Tower128) : (b : Nat) → List (ChallengeTuple b)
  | 0 => [.nil]
  | b + 1 => (challengeTuples S b).flatMap (fun rest => S.map (fun g => .cons g rest))

theorem challengeTuples_length (S : List Tower128) (b : Nat) :
    (challengeTuples S b).length = S.length ^ b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [challengeTuples, flatMap_map_len, ih, Nat.pow_succ]

def unitBoolWeights : (b : Nat) → BoolWeights b
  | 0 => .leaf (towerOne 7)
  | b + 1 => .branch (unitBoolWeights b) (unitBoolWeights b)

def btreeScale (c : Tower128) : {b : Nat} → Vec128 b → Vec128 b
  | 0, .leaf w => .leaf (towerMul 7 c w)
  | _ + 1, .branch lo hi => .branch (btreeScale c lo) (btreeScale c hi)

/-- Plane weights `chi^u` for `u < 2^b` (`PassWeights.plane`, `rss256.rs:958-976`). -/
def chiBoolWeights (chi : Tower128) : (b : Nat) → BoolWeights b
  | 0 => .leaf (towerOne 7)
  | b + 1 =>
    let sub := chiBoolWeights chi b
    .branch sub (btreeScale (towerPow128 chi (2 ^ b)) sub)

def zeroCornerBool : {b : Nat} → BoolWeights b → Tower128
  | 0, .leaf w => w
  | _ + 1, .branch lo _ => zeroCornerBool lo

theorem zeroCorner_unitBoolWeights (b : Nat) :
    zeroCornerBool (unitBoolWeights b) = towerOne 7 := by
  induction b with
  | zero => rfl
  | succ b ih => exact ih

theorem zeroCorner_chiBoolWeights (chi : Tower128) (b : Nat) :
    zeroCornerBool (chiBoolWeights chi b) = towerOne 7 := by
  induction b with
  | zero => rfl
  | succ b ih => exact ih

def zeroTab : (b : Nat) → TernaryTab b
  | 0 => .leaf (towerZero 7)
  | b + 1 => .branch (zeroTab b) (zeroTab b) (zeroTab b)

def diffTab : {b : Nat} → TernaryTab b → TernaryTab b → TernaryTab b
  | 0, .leaf x, .leaf y => .leaf (towerAdd 7 x y)
  | _ + 1, .branch x0 x1 x2, .branch y0 y1 y2 =>
    .branch (diffTab x0 y0) (diffTab x1 y1) (diffTab x2 y2)

theorem diffTab_eq_zero_iff {b : Nat} (x y : TernaryTab b) :
    diffTab x y = zeroTab b ↔ x = y := by
  induction b with
  | zero =>
    cases x with | leaf xv =>
    cases y with | leaf yv =>
    simp only [diffTab, zeroTab, TTree.leaf.injEq]
    constructor
    · intro h
      have h1 := congrArg (fun z => towerAdd 7 z yv) h
      rw [towerAdd_assoc, towerAdd_self_zero, towerAdd_zero, towerZero_add] at h1
      exact h1
    · rintro rfl
      exact towerAdd_self_zero 7 xv
  | succ b ih =>
    cases x with | branch x0 x1 x2 =>
    cases y with | branch y0 y1 y2 =>
    simp only [diffTab, zeroTab, TTree.branch.injEq, ih]

/-- Ternary multiquadratic basis (`round_coefficients`, `rss256.rs:914-933`):
    `basis(0, g) = 1 + g`, `basis(1, g) = g`, `basis(2, g) = towerFrobeniusPoly 7 g = g + g^2`. -/
def ternaryBasis0 (g : Tower128) : Tower128 := towerAdd 7 (towerOne 7) g
def ternaryBasis1 (g : Tower128) : Tower128 := g
@[expose] def ternaryBasisSlope (g : Tower128) : Tower128 := towerFrobeniusPoly 7 g

theorem ternaryBasisSlope_eq_zero_iff (g : Tower128) :
    ternaryBasisSlope g = towerZero 7 ↔ (g = towerZero 7 ∨ g = towerOne 7) :=
  towerFrobenius_eq_zero_iff_bit 7 g

def ternaryEval : {b : Nat} → ChallengeTuple b → TernaryTab b → Tower128
  | 0, .nil, .leaf s => s
  | _ + 1, .cons g rest, .branch t0 t1 t2 =>
    towerAdd 7
      (towerAdd 7
        (towerMul 7 (ternaryBasis0 g) (ternaryEval rest t0))
        (towerMul 7 (ternaryBasis1 g) (ternaryEval rest t1)))
      (towerMul 7 (ternaryBasisSlope g) (ternaryEval rest t2))

theorem ternaryEval_step_eq_evalCoeffs {b : Nat} (g : Tower128) (rest : ChallengeTuple b)
    (t0 t1 t2 : TernaryTab b) :
    let e0 := ternaryEval rest t0
    let e1 := ternaryEval rest t1
    let e2 := ternaryEval rest t2
    ternaryEval (.cons g rest) (.branch t0 t1 t2) =
      RoundPoly.evalCoeffs [e0, towerAdd 7 (towerAdd 7 e0 e1) e2, e2] g := by
  dsimp only
  rw [evalCoeffs3_eq]
  simp only [ternaryEval, ternaryBasis0, ternaryBasis1, ternaryBasisSlope, towerFrobeniusPoly,
    towerAdd_mul_distrib, towerMul_add_distrib, towerOne_mul]
  ac_rfl

theorem ternaryEval_diffTab {b : Nat} (gs : ChallengeTuple b) (x y : TernaryTab b) :
    ternaryEval gs (diffTab x y) = towerAdd 7 (ternaryEval gs x) (ternaryEval gs y) := by
  induction b with
  | zero =>
    cases gs with | nil =>
    cases x with | leaf xv =>
    cases y with | leaf yv =>
    rfl
  | succ b ih =>
    cases gs with | cons g rest =>
    cases x with | branch x0 x1 x2 =>
    cases y with | branch y0 y1 y2 =>
    simp only [diffTab, ternaryEval, ih rest, towerMul_add_distrib]
    ac_rfl

def weightedBoolSum : {b : Nat} → BoolWeights b → TernaryTab b → Tower128
  | 0, .leaf w, .leaf s => towerMul 7 w s
  | _ + 1, .branch w0 w1, .branch t0 t1 _ =>
    towerAdd 7 (weightedBoolSum w0 t0) (weightedBoolSum w1 t1)

def weightedNonzeroBoolSum : {b : Nat} → BoolWeights b → TernaryTab b → Tower128
  | 0, .leaf _, .leaf _ => towerZero 7
  | _ + 1, .branch w0 w1, .branch t0 t1 _ =>
    towerAdd 7 (weightedNonzeroBoolSum w0 t0) (weightedBoolSum w1 t1)

def zeroCornerTab : {b : Nat} → TernaryTab b → Tower128
  | 0, .leaf s => s
  | _ + 1, .branch t0 _ _ => zeroCornerTab t0

def setZeroCornerTab : {b : Nat} → Tower128 → TernaryTab b → TernaryTab b
  | 0, v, .leaf _ => .leaf v
  | _ + 1, v, .branch t0 t1 t2 => .branch (setZeroCornerTab v t0) t1 t2

theorem weightedBoolSum_decomp {b : Nat} (w : BoolWeights b) (s : TernaryTab b) :
    weightedBoolSum w s =
      towerAdd 7 (towerMul 7 (zeroCornerBool w) (zeroCornerTab s))
                 (weightedNonzeroBoolSum w s) := by
  induction b with
  | zero =>
    cases w with | leaf wv =>
    cases s with | leaf sv =>
    simp only [weightedBoolSum, zeroCornerBool, zeroCornerTab,
      weightedNonzeroBoolSum, towerAdd_zero]
  | succ b ih =>
    cases w with | branch w0 w1 =>
    cases s with | branch t0 t1 t2 =>
    simp only [weightedBoolSum, zeroCornerBool, zeroCornerTab, weightedNonzeroBoolSum,
      ih w0 t0, towerAdd_assoc]

theorem weightedNonzeroBoolSum_setZeroCorner {b : Nat} (v : Tower128)
    (w : BoolWeights b) (s : TernaryTab b) :
    weightedNonzeroBoolSum w (setZeroCornerTab v s) = weightedNonzeroBoolSum w s := by
  induction b with
  | zero =>
    cases w with | leaf _ =>
    cases s with | leaf _ =>
    rfl
  | succ b ih =>
    cases w with | branch w0 w1 =>
    cases s with | branch t0 t1 t2 =>
    simp only [setZeroCornerTab, weightedNonzeroBoolSum, ih w0 t0]

theorem zeroCornerTab_setZeroCorner {b : Nat} (v : Tower128) (s : TernaryTab b) :
    zeroCornerTab (setZeroCornerTab v s) = v := by
  induction b with
  | zero =>
    cases s with | leaf _ => rfl
  | succ b ih =>
    cases s with | branch t0 _ _ => exact ih t0

/-- `next_claim` (`rss256.rs:939-947`): locks `s(0)` from `claim` and evaluates at `gammas`. -/
def lockZeroCorner {b : Nat} (claim : Tower128) (w : BoolWeights b) (s : TernaryTab b) :
    TernaryTab b :=
  setZeroCornerTab (towerAdd 7 claim (weightedNonzeroBoolSum w s)) s

@[expose] def nextClaim (b : Nat) (claim : Tower128) (w : BoolWeights b)
    (s : TernaryTab b) (gammas : ChallengeTuple b) : Tower128 :=
  ternaryEval gammas (lockZeroCorner claim w s)

theorem lockZeroCorner_weightedBoolSum {b : Nat} (claim : Tower128) (w : BoolWeights b)
    (s : TernaryTab b) (hw0 : zeroCornerBool w = towerOne 7) :
    weightedBoolSum w (lockZeroCorner claim w s) = claim := by
  unfold lockZeroCorner
  rw [weightedBoolSum_decomp, hw0, towerOne_mul, zeroCornerTab_setZeroCorner,
      weightedNonzeroBoolSum_setZeroCorner, towerAdd_assoc, towerAdd_self_zero, towerAdd_zero]

theorem setZeroCornerTab_self {b : Nat} (t : TernaryTab b) :
    setZeroCornerTab (zeroCornerTab t) t = t := by
  induction b with
  | zero =>
    cases t with | leaf _ => rfl
  | succ b ih =>
    cases t with | branch t0 _ _ =>
    simp only [zeroCornerTab, setZeroCornerTab, ih t0]

theorem lockZeroCorner_self_of_claim_eq {b : Nat} (w : BoolWeights b) (s : TernaryTab b)
    (hw0 : zeroCornerBool w = towerOne 7) :
    lockZeroCorner (weightedBoolSum w s) w s = s := by
  have h0 : towerAdd 7 (weightedBoolSum w s) (weightedNonzeroBoolSum w s) =
      zeroCornerTab s := by
    rw [weightedBoolSum_decomp, hw0, towerOne_mul,
        towerAdd_assoc, towerAdd_self_zero, towerAdd_zero]
  unfold lockZeroCorner
  rw [h0]
  exact setZeroCornerTab_self s

/-! ### Vector Folding (`Vec128`) & Exact Bilinear Completeness -/

def vecZero : (n : Nat) → Vec128 n
  | 0 => .leaf (towerZero 7)
  | n + 1 => .branch (vecZero n) (vecZero n)

def vecAdd : {n : Nat} → Vec128 n → Vec128 n → Vec128 n
  | 0, .leaf x, .leaf y => .leaf (towerAdd 7 x y)
  | _ + 1, .branch x0 x1, .branch y0 y1 => .branch (vecAdd x0 y0) (vecAdd x1 y1)

def vecDot : {n : Nat} → Vec128 n → Vec128 n → Tower128
  | 0, .leaf x, .leaf y => towerMul 7 x y
  | _ + 1, .branch x0 x1, .branch y0 y1 => towerAdd 7 (vecDot x0 y0) (vecDot x1 y1)

def vecCross {n : Nat} (xp yq xq yp : Vec128 n) : Tower128 :=
  towerAdd 7 (vecDot xp yq) (vecDot xq yp)

def btreeTernaryExpand (m : Nat) : (b : Nat) → Vec128 (m + b) → TTree (Vec128 m) b
  | 0, v => .leaf v
  | b + 1, .branch lo hi =>
    .branch (btreeTernaryExpand m b lo)
            (btreeTernaryExpand m b hi)
            (btreeTernaryExpand m b (vecAdd lo hi))

def ttreeMap4 {α β : Type} (f : α → α → α → α → β) :
    {b : Nat} → TTree α b → TTree α b → TTree α b → TTree α b → TTree β b
  | 0, .leaf a, .leaf b0, .leaf c, .leaf d => .leaf (f a b0 c d)
  | _ + 1, .branch a0 a1 a2, .branch b0 b1 b2, .branch c0 c1 c2, .branch d0 d1 d2 =>
    .branch (ttreeMap4 f a0 b0 c0 d0) (ttreeMap4 f a1 b1 c1 d1) (ttreeMap4 f a2 b2 c2 d2)

def honestRoundTab (m b : Nat) (xp yq xq yp : Vec128 (m + b)) : TernaryTab b :=
  ttreeMap4 vecCross
    (btreeTernaryExpand m b xp) (btreeTernaryExpand m b yq)
    (btreeTernaryExpand m b xq) (btreeTernaryExpand m b yp)

def foldVec (m : Nat) : (b : Nat) → ChallengeTuple b → Vec128 (m + b) → Vec128 m
  | 0, .nil, v => v
  | b + 1, .cons g rest, .branch lo hi =>
    vecAdd (btreeScale (ternaryBasis0 g) (foldVec m b rest lo))
           (btreeScale (ternaryBasis1 g) (foldVec m b rest hi))

theorem weightedBoolSum_unit_honestRoundTab (m b : Nat) :
    ∀ (xp yq xq yp : Vec128 (m + b)),
      weightedBoolSum (unitBoolWeights b) (honestRoundTab m b xp yq xq yp) =
        vecCross xp yq xq yp := by
  induction b with
  | zero =>
    intro xp yq xq yp
    dsimp only [honestRoundTab, btreeTernaryExpand, ttreeMap4, unitBoolWeights, weightedBoolSum]
    exact towerOne_mul 7 _
  | succ b ih =>
    intro xp yq xq yp
    cases xp with | branch xp0 xp1 =>
    cases yq with | branch yq0 yq1 =>
    cases xq with | branch xq0 xq1 =>
    cases yp with | branch yp0 yp1 =>
    dsimp only [honestRoundTab, btreeTernaryExpand, ttreeMap4, unitBoolWeights, weightedBoolSum]
    change towerAdd 7
      (weightedBoolSum (unitBoolWeights b) (honestRoundTab m b xp0 yq0 xq0 yp0))
      (weightedBoolSum (unitBoolWeights b) (honestRoundTab m b xp1 yq1 xq1 yp1)) =
      vecCross (.branch xp0 xp1) (.branch yq0 yq1) (.branch xq0 xq1) (.branch yp0 yp1)
    rw [ih xp0 yq0 xq0 yp0, ih xp1 yq1 xq1 yp1]
    simp only [vecCross, vecDot]
    ac_rfl

theorem vecAdd_zero (n : Nat) : vecAdd (vecZero n) (vecZero n) = vecZero n := by
  induction n with
  | zero => exact congrArg BTree.leaf (towerAdd_self_zero 7 _)
  | succ n ih => simp only [vecZero, vecAdd, ih]

theorem vecDot_zero (n : Nat) : vecDot (vecZero n) (vecZero n) = towerZero 7 := by
  induction n with
  | zero => exact towerMul_zero 7 _
  | succ n ih => simp only [vecZero, vecDot, ih, towerAdd_self_zero]

theorem vecScale_add {n : Nat} (c : Tower128) (x y : Vec128 n) :
    btreeScale c (vecAdd x y) = vecAdd (btreeScale c x) (btreeScale c y) := by
  induction n with
  | zero =>
    cases x with | leaf xv =>
    cases y with | leaf yv =>
    exact congrArg BTree.leaf (towerMul_add_distrib 7 c xv yv)
  | succ n ih =>
    cases x with | branch x0 x1 =>
    cases y with | branch y0 y1 =>
    simp only [vecAdd, btreeScale, ih]

theorem vecAdd_swap {n : Nat} (a b c d : Vec128 n) :
    vecAdd (vecAdd a b) (vecAdd c d) = vecAdd (vecAdd a c) (vecAdd b d) := by
  induction n with
  | zero =>
    cases a with | leaf av =>
    cases b with | leaf bv =>
    cases c with | leaf cv =>
    cases d with | leaf dv =>
    dsimp only [vecAdd]
    congr 1
    ac_rfl
  | succ n ih =>
    cases a with | branch a0 a1 =>
    cases b with | branch b0 b1 =>
    cases c with | branch c0 c1 =>
    cases d with | branch d0 d1 =>
    simp only [vecAdd, ih]

theorem vecDot_add_left {n : Nat} (x1 x2 y : Vec128 n) :
    vecDot (vecAdd x1 x2) y = towerAdd 7 (vecDot x1 y) (vecDot x2 y) := by
  induction n with
  | zero =>
    cases x1 with | leaf a =>
    cases x2 with | leaf b =>
    cases y with | leaf c =>
    exact towerAdd_mul_distrib 7 a b c
  | succ n ih =>
    cases x1 with | branch x10 x11 =>
    cases x2 with | branch x20 x21 =>
    cases y with | branch y0 y1 =>
    simp only [vecAdd, vecDot]
    rw [ih x10 x20 y0, ih x11 x21 y1]
    ac_rfl

theorem vecDot_add_right {n : Nat} (x y1 y2 : Vec128 n) :
    vecDot x (vecAdd y1 y2) = towerAdd 7 (vecDot x y1) (vecDot x y2) := by
  induction n with
  | zero =>
    cases x with | leaf a =>
    cases y1 with | leaf b =>
    cases y2 with | leaf c =>
    exact towerMul_add_distrib 7 a b c
  | succ n ih =>
    cases x with | branch x0 x1 =>
    cases y1 with | branch y10 y11 =>
    cases y2 with | branch y20 y21 =>
    simp only [vecAdd, vecDot]
    rw [ih x0 y10 y20, ih x1 y11 y21]
    ac_rfl

theorem vecDot_scale_left {n : Nat} (c : Tower128) (x y : Vec128 n) :
    vecDot (btreeScale c x) y = towerMul 7 c (vecDot x y) := by
  induction n with
  | zero =>
    cases x with | leaf a =>
    cases y with | leaf b =>
    exact towerMul_assoc 7 c a b
  | succ n ih =>
    cases x with | branch x0 x1 =>
    cases y with | branch y0 y1 =>
    simp only [btreeScale, vecDot]
    rw [ih x0 y0, ih x1 y1, ← towerMul_add_distrib]

theorem vecDot_scale_right {n : Nat} (c : Tower128) (x y : Vec128 n) :
    vecDot x (btreeScale c y) = towerMul 7 c (vecDot x y) := by
  induction n with
  | zero =>
    cases x with | leaf a =>
    cases y with | leaf b =>
    dsimp only [btreeScale, vecDot]
    ac_rfl
  | succ n ih =>
    cases x with | branch x0 x1 =>
    cases y with | branch y0 y1 =>
    simp only [btreeScale, vecDot]
    rw [ih x0 y0, ih x1 y1, ← towerMul_add_distrib]

theorem foldVec_add (m b : Nat) (gs : ChallengeTuple b) (u v : Vec128 (m + b)) :
    foldVec m b gs (vecAdd u v) = vecAdd (foldVec m b gs u) (foldVec m b gs v) := by
  induction b with
  | zero =>
    cases gs with | nil => rfl
  | succ b ih =>
    cases gs with | cons g rest =>
    cases u with | branch u0 u1 =>
    cases v with | branch v0 v1 =>
    simp only [vecAdd, foldVec]
    rw [ih rest u0 v0, ih rest u1 v1, vecScale_add, vecScale_add, vecAdd_swap]

theorem frobenius_quadratic_interp_eq (g p0 p1 mid : Tower128) :
    towerAdd 7
      (towerAdd 7 (towerMul 7 (ternaryBasis0 g) p0) (towerMul 7 (ternaryBasis1 g) p1))
      (towerMul 7 (ternaryBasisSlope g) (towerAdd 7 (towerAdd 7 p0 mid) p1)) =
    towerAdd 7
      (towerAdd 7
        (towerMul 7 (ternaryBasis0 g) (towerMul 7 (ternaryBasis0 g) p0))
        (towerMul 7 (ternaryBasis0 g) (towerMul 7 (ternaryBasis1 g) mid)))
      (towerMul 7 (ternaryBasis1 g) (towerMul 7 (ternaryBasis1 g) p1)) := by
  dsimp only [ternaryBasis0, ternaryBasis1, ternaryBasisSlope, towerFrobeniusPoly]
  simp only [towerAdd_mul_distrib, towerMul_add_distrib, towerOne_mul]
  have hL : towerAdd 7 (towerAdd 7 (towerAdd 7 p0 (towerMul 7 g p0)) (towerMul 7 g p1))
      (towerAdd 7 (towerAdd 7 (towerAdd 7 (towerMul 7 (towerMul 7 g g) p0) (towerMul 7 g p0))
          (towerAdd 7 (towerMul 7 (towerMul 7 g g) mid) (towerMul 7 g mid)))
        (towerAdd 7 (towerMul 7 (towerMul 7 g g) p1) (towerMul 7 g p1))) =
      towerAdd 7 (towerAdd 7 p0 (towerAdd 7 (towerAdd 7 (towerMul 7 g p0) (towerMul 7 g p0))
          (towerAdd 7 (towerMul 7 g p1) (towerMul 7 g p1))))
        (towerAdd 7 (towerMul 7 g mid) (towerAdd 7
          (towerAdd 7 (towerMul 7 (towerMul 7 g g) p0) (towerMul 7 (towerMul 7 g g) mid))
          (towerMul 7 (towerMul 7 g g) p1))) := by ac_rfl
  have hR : towerAdd 7 (towerAdd 7
        (towerAdd 7 (towerAdd 7 p0 (towerMul 7 g p0)) (towerAdd 7 (towerMul 7 g p0) (towerMul 7 g (towerMul 7 g p0))))
        (towerAdd 7 (towerMul 7 g mid) (towerMul 7 g (towerMul 7 g mid))))
      (towerMul 7 g (towerMul 7 g p1)) =
      towerAdd 7 (towerAdd 7 p0 (towerAdd 7 (towerMul 7 g p0) (towerMul 7 g p0)))
        (towerAdd 7 (towerMul 7 g mid) (towerAdd 7
          (towerAdd 7 (towerMul 7 g (towerMul 7 g p0)) (towerMul 7 g (towerMul 7 g mid)))
          (towerMul 7 g (towerMul 7 g p1)))) := by ac_rfl
  rw [hL, hR, towerAdd_self_zero, towerAdd_self_zero, towerAdd_zero, towerAdd_zero]
  simp only [towerMul_assoc]

theorem ternaryEval_honestRoundTab_eq (m b : Nat) :
    ∀ (gammas : ChallengeTuple b) (xp yq xq yp : Vec128 (m + b)),
      ternaryEval gammas (honestRoundTab m b xp yq xq yp) =
        vecCross (foldVec m b gammas xp) (foldVec m b gammas yq)
                 (foldVec m b gammas xq) (foldVec m b gammas yp) := by
  induction b with
  | zero =>
    intro gammas xp yq xq yp
    cases gammas with | nil => rfl
  | succ b ih =>
    intro gammas xp yq xq yp
    cases gammas with | cons g rest =>
    cases xp with | branch xp0 xp1 =>
    cases yq with | branch yq0 yq1 =>
    cases xq with | branch xq0 xq1 =>
    cases yp with | branch yp0 yp1 =>
    dsimp only [honestRoundTab, btreeTernaryExpand, ttreeMap4, ternaryEval, foldVec]
    change towerAdd 7
      (towerAdd 7
        (towerMul 7 (ternaryBasis0 g) (ternaryEval rest (honestRoundTab m b xp0 yq0 xq0 yp0)))
        (towerMul 7 (ternaryBasis1 g) (ternaryEval rest (honestRoundTab m b xp1 yq1 xq1 yp1))))
      (towerMul 7 (ternaryBasisSlope g)
        (ternaryEval rest (honestRoundTab m b (vecAdd xp0 xp1) (vecAdd yq0 yq1)
                                              (vecAdd xq0 xq1) (vecAdd yp0 yp1)))) = _
    rw [ih rest xp0 yq0 xq0 yp0, ih rest xp1 yq1 xq1 yp1,
        ih rest (vecAdd xp0 xp1) (vecAdd yq0 yq1) (vecAdd xq0 xq1) (vecAdd yp0 yp1),
        foldVec_add, foldVec_add, foldVec_add, foldVec_add]
    let Xp0 := foldVec m b rest xp0
    let Xp1 := foldVec m b rest xp1
    let Yq0 := foldVec m b rest yq0
    let Yq1 := foldVec m b rest yq1
    let Xq0 := foldVec m b rest xq0
    let Xq1 := foldVec m b rest xq1
    let Yp0 := foldVec m b rest yp0
    let Yp1 := foldVec m b rest yp1
    change towerAdd 7
      (towerAdd 7
        (towerMul 7 (ternaryBasis0 g) (vecCross Xp0 Yq0 Xq0 Yp0))
        (towerMul 7 (ternaryBasis1 g) (vecCross Xp1 Yq1 Xq1 Yp1)))
      (towerMul 7 (ternaryBasisSlope g)
        (vecCross (vecAdd Xp0 Xp1) (vecAdd Yq0 Yq1) (vecAdd Xq0 Xq1) (vecAdd Yp0 Yp1))) =
      vecCross
        (vecAdd (btreeScale (ternaryBasis0 g) Xp0) (btreeScale (ternaryBasis1 g) Xp1))
        (vecAdd (btreeScale (ternaryBasis0 g) Yq0) (btreeScale (ternaryBasis1 g) Yq1))
        (vecAdd (btreeScale (ternaryBasis0 g) Xq0) (btreeScale (ternaryBasis1 g) Xq1))
        (vecAdd (btreeScale (ternaryBasis0 g) Yp0) (btreeScale (ternaryBasis1 g) Yp1))
    unfold vecCross
    simp only [vecDot_add_left, vecDot_add_right, vecDot_scale_left, vecDot_scale_right]
    let p0 := towerAdd 7 (vecDot Xp0 Yq0) (vecDot Xq0 Yp0)
    let p1 := towerAdd 7 (vecDot Xp1 Yq1) (vecDot Xq1 Yp1)
    let mid := towerAdd 7
      (towerAdd 7 (vecDot Xp0 Yq1) (vecDot Xp1 Yq0))
      (towerAdd 7 (vecDot Xq0 Yp1) (vecDot Xq1 Yp0))
    have hSlopeArg :
        towerAdd 7
          (towerAdd 7 (towerAdd 7 (vecDot Xp0 Yq0) (vecDot Xp1 Yq0))
                      (towerAdd 7 (vecDot Xp0 Yq1) (vecDot Xp1 Yq1)))
          (towerAdd 7 (towerAdd 7 (vecDot Xq0 Yp0) (vecDot Xq1 Yp0))
                      (towerAdd 7 (vecDot Xq0 Yp1) (vecDot Xq1 Yp1))) =
        towerAdd 7 (towerAdd 7 p0 mid) p1 := by
      dsimp only [p0, p1, mid]
      ac_rfl
    rw [hSlopeArg, frobenius_quadratic_interp_eq g p0 p1 mid]
    dsimp only [p0, p1, mid]
    simp only [towerMul_add_distrib]
    ac_rfl

/-- **Honest Completeness of `nextClaim` (`nextClaim_honest_complete`)**. -/
theorem nextClaim_honest_complete (m b : Nat)
    (w : BoolWeights b) (hw0 : zeroCornerBool w = towerOne 7)
    (xp yq xq yp : Vec128 (m + b)) (gammas : ChallengeTuple b) :
    let sTrue := honestRoundTab m b xp yq xq yp
    let claimTrue := weightedBoolSum w sTrue
    nextClaim b claimTrue w sTrue gammas =
      vecCross (foldVec m b gammas xp) (foldVec m b gammas yq)
               (foldVec m b gammas xq) (foldVec m b gammas yp) := by
  dsimp only [nextClaim]
  rw [lockZeroCorner_self_of_claim_eq w _ hw0]
  exact ternaryEval_honestRoundTab_eq m b gammas xp yq xq yp

theorem weightedBoolSum_zeroTab {b : Nat} (w : BoolWeights b) :
    weightedBoolSum w (zeroTab b) = towerZero 7 := by
  induction b with
  | zero =>
    cases w with | leaf wv => exact towerMul_zero 7 wv
  | succ b ih =>
    cases w with | branch w0 w1 =>
    simp only [zeroTab, weightedBoolSum, ih w0, ih w1, towerAdd_self_zero]

theorem decide_eq_decide_of_iff {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) :
    decide P = decide Q := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq, decide_eq_true_eq]
  exact h

theorem vecCross_leaf (xp yq xq yp : Tower128) :
    vecCross (BTree.leaf xp) (BTree.leaf yq) (BTree.leaf xq) (BTree.leaf yp) =
      towerAdd 7 (towerMul 7 xp yq) (towerMul 7 xq yp) := by
  rfl

theorem honestRoundTab_vecZero (m b : Nat) :
    honestRoundTab m b (vecZero (m + b)) (vecZero (m + b))
      (vecZero (m + b)) (vecZero (m + b)) = zeroTab b := by
  induction b with
  | zero =>
    dsimp only [honestRoundTab, btreeTernaryExpand, ttreeMap4, zeroTab, vecCross]
    rw [vecDot_zero (m + 0), towerAdd_self_zero]
  | succ b ih =>
    dsimp only [vecZero, honestRoundTab, btreeTernaryExpand, ttreeMap4, zeroTab]
    change TTree.branch
      (honestRoundTab m b (vecZero (m + b)) (vecZero (m + b)) (vecZero (m + b)) (vecZero (m + b)))
      (honestRoundTab m b (vecZero (m + b)) (vecZero (m + b)) (vecZero (m + b)) (vecZero (m + b)))
      (honestRoundTab m b
        (vecAdd (vecZero (m + b)) (vecZero (m + b))) (vecAdd (vecZero (m + b)) (vecZero (m + b)))
        (vecAdd (vecZero (m + b)) (vecZero (m + b))) (vecAdd (vecZero (m + b)) (vecZero (m + b)))) =
      TTree.branch (zeroTab b) (zeroTab b) (zeroTab b)
    rw [vecAdd_zero, ih]

/-- Root count, including the zero-dimensional base case. -/
def ternaryBadBound (cardS : Nat) : Nat → Nat
  | 0 => 0
  | b + 1 => ternaryBadBound cardS b * cardS + 2 * cardS ^ b

theorem ternaryBadBound_scale (cardS b : Nat) :
    ternaryBadBound cardS b * cardS = 2 * b * cardS ^ b := by
  induction b with
  | zero => simp [ternaryBadBound]
  | succ b ih =>
    simp only [ternaryBadBound, Nat.add_mul]
    rw [ih]
    simp only [Nat.mul_assoc, ← Nat.pow_succ]
    simp [Nat.mul_add, Nat.add_mul]

/-- Constructive multivariate Schwartz–Zippel, in the actual ternary basis. -/
theorem ternaryEval_nonzero_roots_le (S : List Tower128) (hS : S.Nodup) :
    ∀ (b : Nat) (t : TernaryTab b), t ≠ zeroTab b →
      ((challengeTuples S b).filter (fun gs => decide (ternaryEval gs t = towerZero 7))).length ≤
        ternaryBadBound S.length b := by
  intro b
  induction b with
  | zero =>
    intro t ht
    cases t with | leaf c =>
    have hc : c ≠ towerZero 7 := fun h => ht (by rw [h]; rfl)
    simp [challengeTuples, ternaryEval, hc, ternaryBadBound]
  | succ b ih =>
    intro t ht
    cases t with | branch t0 t1 t2 =>
    have hpick : ∃ chosen : TernaryTab b, chosen ≠ zeroTab b ∧
        ∀ rest : ChallengeTuple b, ternaryEval rest chosen ≠ towerZero 7 →
          ternaryEval rest t0 ≠ towerZero 7 ∨ ternaryEval rest t1 ≠ towerZero 7 ∨
            ternaryEval rest t2 ≠ towerZero 7 := by
      by_cases h0 : t0 = zeroTab b
      · by_cases h1 : t1 = zeroTab b
        · exact ⟨t2, fun h2 => ht (by rw [h0, h1, h2]; rfl), fun _ h => .inr (.inr h)⟩
        · exact ⟨t1, h1, fun _ h => .inr (.inl h)⟩
      · exact ⟨t0, h0, fun _ h => .inl h⟩
    obtain ⟨chosen, hn, hp⟩ := hpick
    unfold challengeTuples ternaryBadBound
    rw [filter_flatMap_len]
    have hs := sum_map_le_split
      (fun rest => decide (ternaryEval rest chosen = towerZero 7))
      (fun rest => ((S.map (fun g => ChallengeTuple.cons g rest)).filter
        (fun gs => decide (ternaryEval gs (.branch t0 t1 t2) = towerZero 7))).length)
      S.length 2
      (fun rest _ => by rw [filter_map_len]; exact List.length_filter_le _ S)
      (fun rest hgood => by
        rw [filter_map_len]
        simp only [ternaryEval_step_eq_evalCoeffs]
        apply quadratic_roots_le_two_tower128 _ _ _ S hS
        have hnz := hp rest (decide_eq_false_iff_not.mp hgood)
        by_cases h0 : ternaryEval rest t0 = towerZero 7
        · by_cases h2 : ternaryEval rest t2 = towerZero 7
          · right; left
            simp only [h0, h2, towerZero_add, towerAdd_zero]
            exact (hnz.resolve_left (fun h => h h0)).resolve_right (fun h => h h2)
          · exact .inr (.inr h2)
        · exact .inl h0)
      (challengeTuples S b)
    rw [challengeTuples_length, Nat.mul_comm _ 2] at hs
    exact Nat.le_trans hs
      (Nat.add_le_add_right (Nat.mul_le_mul_right S.length (ih chosen hn)) _)

/-- The round locks the incoming claim before sampling its challenge tuple.
The table type enforces degree at most two in every variable. -/
theorem honestFold_nextClaim_false_bad_coins_le (m b : Nat)
    (w : BoolWeights b) (hw0 : zeroCornerBool w = towerOne 7)
    (xp yq xq yp : Vec128 (m + b)) (claim : Tower128) (s : TernaryTab b)
    (hf : claim ≠ weightedBoolSum w (honestRoundTab m b xp yq xq yp))
    (S : List Tower128) (hS : S.Nodup) :
    ((challengeTuples S b).filter (fun gs => decide (nextClaim b claim w s gs =
      vecCross (foldVec m b gs xp) (foldVec m b gs yq)
        (foldVec m b gs xq) (foldVec m b gs yp)))).length ≤ ternaryBadBound S.length b := by
  have hn : diffTab (lockZeroCorner claim w s) (honestRoundTab m b xp yq xq yp) ≠ zeroTab b := by
    intro hz
    have he := (diffTab_eq_zero_iff _ _).mp hz
    have hh := lockZeroCorner_weightedBoolSum claim w s hw0
    rw [he] at hh
    exact hf hh.symm
  apply Nat.le_trans (filter_len_le_of_imp _
    (fun gs => decide (ternaryEval gs
      (diffTab (lockZeroCorner claim w s) (honestRoundTab m b xp yq xq yp)) = towerZero 7)) ?_
    (challengeTuples S b))
  · exact ternaryEval_nonzero_roots_le S hS b _ hn
  · intro gs hg
    apply decide_eq_true_iff.mpr
    rw [ternaryEval_diffTab, ternaryEval_honestRoundTab_eq]
    have he := decide_eq_true_iff.mp hg
    change ternaryEval gs (lockZeroCorner claim w s) = _ at he
    rw [he, towerAdd_self_zero]

/-- Dropping the zero-corner lock lets the honest table repair any false
incoming claim at EVERY challenge, hence with probability one. -/
theorem tooth_honestFold_nextClaim_unlocked_s0_forges_all (m b : Nat)
    (w : BoolWeights b) (xp yq xq yp : Vec128 (m + b)) :
    ∃ claim, claim ≠ weightedBoolSum w (honestRoundTab m b xp yq xq yp) ∧
      ∀ gs, ternaryEval gs (honestRoundTab m b xp yq xq yp) =
        vecCross (foldVec m b gs xp) (foldVec m b gs yq)
          (foldVec m b gs xq) (foldVec m b gs yp) := by
  let honest := weightedBoolSum w (honestRoundTab m b xp yq xq yp)
  refine ⟨towerAdd 7 honest (towerOne 7), ?_, (fun gs => ternaryEval_honestRoundTab_eq m b gs xp yq xq yp)⟩
  intro he
  have hh := congrArg (towerAdd 7 honest) he
  rw [← towerAdd_assoc, towerAdd_self_zero, towerZero_add] at hh
  exact (by decide : towerOne 7 ≠ towerZero 7) hh

#tooth_pair honestFold_nextClaim_false_bad_coins_le vs tooth_honestFold_nextClaim_unlocked_s0_forges_all
#verify_constructive ternaryBadBound_scale ternaryEval_nonzero_roots_le honestFold_nextClaim_false_bad_coins_le

#verify_constructive
  Qsag.Rss256ProductProof.passWeight_eq_towerPow
  Qsag.Rss256ProductProof.passBatching_false_bad_coins_le
  Qsag.Rss256ProductProof.nextClaim_honest_complete
  Qsag.Rss256ProductProof.weightedBoolSum_zeroTab
  Qsag.Rss256ProductProof.decide_eq_decide_of_iff

end Rss256ProductProof
end Qsag
end
