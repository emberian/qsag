module
public import Qsag.Math.GoldilocksEncoding

public import Qsag.Protocol.Threshold.MlDsa44Parameters
public import Qsag.Tactic.Prelude
public import Qsag.Spec.Refines
public import Qsag.Math.Goldilocks
public import Qsag.Math.Lattices
public import Qsag.Oracle.Poseidon2
public import Qsag.Protocol.Aggregation.UcGames
public import Qsag.Protocol.Credentials.AdvancedMpcAndCreds
public import Qsag.Coding.Cwyz26
public import Qsag.Tactic.AssuranceKit
import Qsag.Math.Primality

public section

namespace Qsag

attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
attribute [-instance] Fin.instLinearOrderPackage

set_option autoImplicit false

/-! ### §1.4 Exact FIPS 204 `Power2Round`, `Decompose`, `MakeHint`, `UseHint` & `HighBits` Shift Lemma -/

/-- Exact NIST FIPS 204 `Power2Round(r)` (`Algorithm 35`, $d = 13$, $2^d = 8192$):
    returns `(r1, r0)` with `r0 ∈ (-4096, 4096]`. -/
@[expose] def power2Round (r : Fq204) : Nat × Int :=
  let low : Nat := r.val % 8192
  let r0 : Int := if 4096 < low then (low : Int) - 8192 else (low : Int)
  let r1 : Nat := ((r.val : Int) - r0).toNat / 8192
  (r1, r0)

/-- **`power2Round_reconstruct`**: for every $r \in \mathbb{Z}_q$, `power2Round r = (r1, r0)` satisfies
    $-2^{12} < r_0 \le 2^{12}$, $r_1 < 1024$, and exact integer reconstruction $r_1 \cdot 2^{13} + r_0 = r$. -/
theorem power2Round_reconstruct (r : Fq204) :
    -4096 < (power2Round r).2 ∧ (power2Round r).2 ≤ 4096 ∧ (power2Round r).1 < 1024 ∧
    (((power2Round r).1 : Int) * 8192 + (power2Round r).2 = (r.val : Int)) ∧
    Fq204.add (Fq204.mul (Fq204.ofNat (power2Round r).1) (Fq204.ofNat 8192))
              (Fq204.ofInt (power2Round r).2) = r := by
  have hr := r.isLt
  have hEqInt :
      -4096 < (power2Round r).2 ∧ (power2Round r).2 ≤ 4096 ∧
      (power2Round r).1 < 1024 ∧ (((power2Round r).1 : Int) * 8192 + (power2Round r).2 = (r.val : Int)) := by
    unfold power2Round
    unfold mldsaQ at hr
    dsimp only
    split <;> (refine ⟨?_, ?_, ?_, ?_⟩ <;> omega)
  refine ⟨hEqInt.1, hEqInt.2.1, hEqInt.2.2.1, hEqInt.2.2.2, ?_⟩
  let r1 := (power2Round r).1
  let r0 := (power2Round r).2
  have hRec : (r1 : Int) * 8192 + r0 = (r.val : Int) := hEqInt.2.2.2
  have hmul : Fq204.mul (Fq204.ofNat r1) (Fq204.ofNat 8192) = Fq204.ofInt ((r1 : Int) * 8192) := by
    have hmulNat : Fq204.mul (Fq204.ofNat r1) (Fq204.ofNat 8192) = Fq204.ofNat (r1 * 8192) := by
      apply Fq204.ext
      simp only [Fq204.mul_val, Fq204.ofNat_val, Nat.mod_mul_mod, Nat.mul_mod_mod]
    rw [hmulNat]
    apply Fq204.ext; apply Int.ofNat_inj.mp
    rw [Fq204.ofInt_val, Fq204.ofNat_val, Int.natCast_emod, Int.natCast_mul]
    rfl
  change Fq204.add (Fq204.mul (Fq204.ofNat r1) (Fq204.ofNat 8192)) (Fq204.ofInt r0) = r
  rw [hmul, Fq204.ofInt_add, hRec, Fq204.ofInt_nat]

/-- Exact NIST FIPS 204 `Decompose(r)` (`Algorithm 36`) for `ML-DSA-44`
    ($\gamma_2 = 95232, \alpha = 2\gamma_2 = 190464, m = 44$). -/
@[expose] def decompose (r : Fq204) : Nat × Int :=
  let rem : Nat := r.val % 190464
  let r0p : Int := if 95232 < rem then (rem : Int) - 190464 else (rem : Int)
  if (r.val : Int) - r0p = 8380416 then
    (0, r0p - 1)
  else
    (((r.val : Int) - r0p).toNat / 190464, r0p)

/-- Division-free 48-bit shift/multiply `decompose_ct` from `fips204_ntt.rs`
    (`M48_88 = (1 << 48) / 190464 + 1 = 1477838210`). -/
def decomposeCtSpec (r : Nat) : Nat × Int :=
  let m48 : Nat := 1477838210
  let qQuot : Nat := (r * m48) / 281474976710656
  let rem : Nat := r - qQuot * 190464
  let gtG2 : Bool := decide (95232 < rem)
  let r0Base : Int := if gtG2 then (rem : Int) - 190464 else (rem : Int)
  if (r : Int) - r0Base = 8380416 then
    (0, r0Base - 1)
  else
    (qQuot + (if gtG2 then 1 else 0), r0Base)

/-- **`decomposeCt_eq_decompose`**: division-free `decompose_ct` equals exact FIPS 204 `decompose`
    over all $8{,}380{,}417$ field elements. -/
theorem decomposeCt_eq_decompose (r : Fq204) :
    decomposeCtSpec r.val = decompose r := by
  have hr := r.isLt
  unfold decomposeCtSpec decompose mldsaQ at *
  dsimp only
  have hq : (r.val * 1477838210) / 281474976710656 = r.val / 190464 := by omega
  have hrem : r.val - (r.val / 190464) * 190464 = r.val % 190464 := by omega
  rw [hq, hrem]
  if hgt : 95232 < r.val % 190464 then
    simp only [hgt, decide_true, ↓reduceIte]
    split
    · rfl
    · congr 1; omega
  else
    simp only [hgt, decide_false, Bool.false_eq_true, ↓reduceIte]
    split
    · rfl
    · congr 1; omega

/-- FIPS 204 `HighBits(r)` (`Algorithm 37`, returning `r1 ∈ [0, 44)`). -/
def mldsaHighBits (r : Fq204) : Nat := (decompose r).1

/-- FIPS 204 `LowBits(r)` (`Algorithm 38`, returning `r0 ∈ [-95232, 95232]`). -/
def mldsaLowBits (r : Fq204) : Int := (decompose r).2

/-- **`decompose_reconstruct`**: exact reconstruction $r \equiv r_1 \cdot 2\gamma_2 + r_0 \pmod q$
    and norm bounds $r_1 < 44$, $-\gamma_2 \le r_0 \le \gamma_2$. -/
theorem decompose_reconstruct (r : Fq204) :
    mldsaHighBits r < 44 ∧
    -95232 ≤ mldsaLowBits r ∧ mldsaLowBits r ≤ 95232 ∧
    (mldsaHighBits r ≠ 0 → -95232 < mldsaLowBits r) ∧
    Fq204.ofInt ((mldsaHighBits r : Int) * 190464 + mldsaLowBits r) = r := by
  have hr := r.isLt
  have hCore :
      mldsaHighBits r < 44 ∧
      -95232 ≤ mldsaLowBits r ∧ mldsaLowBits r ≤ 95232 ∧
      (mldsaHighBits r ≠ 0 → -95232 < mldsaLowBits r) ∧
      (((mldsaHighBits r : Int) * 190464 + mldsaLowBits r = (r.val : Int)) ∨
       ((mldsaHighBits r : Int) * 190464 + mldsaLowBits r = (r.val : Int) - 8380417)) := by
    unfold mldsaHighBits mldsaLowBits decompose
    unfold mldsaQ at hr
    dsimp only
    split <;> split <;> dsimp only <;> (refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega)
  refine ⟨hCore.1, hCore.2.1, hCore.2.2.1, hCore.2.2.2.1, ?_⟩
  rcases hCore.2.2.2.2 with hExact | hWrap
  · rw [hExact, Fq204.ofInt_nat]
  · rw [hWrap]
    apply Fq204.ext; apply Int.ofNat_inj.mp
    rw [Fq204.ofInt_val]; unfold mldsaQ at hr ⊢
    rw [← Int.add_emod_right _ ((8380417 : Nat) : Int)]
    have hCancel : (r.val : Int) - 8380417 + ((8380417 : Nat) : Int) = (r.val : Int) := by omega
    rw [hCancel]
    exact Int.emod_eq_of_lt (by omega) (by omega)

/-- Interior uniqueness of `decompose`: any representation $u_1 \cdot 2\gamma_2 + u_0 \pmod q$
    with $u_1 < 44$ and $-95232 < u_0 \le 95232$ (or $u_1 = 0, u_0 = -95232$) uniquely determines
    `decompose = (u1, u0)`. -/
theorem decompose_ofInt_interior {u1 : Nat} {u0 : Int}
    (hu1 : u1 < 44) (hu0Lo : -95232 < u0 ∨ (u1 = 0 ∧ u0 = -95232)) (hu0Hi : u0 ≤ 95232) :
    decompose (Fq204.ofInt ((u1 : Int) * 190464 + u0)) = (u1, u0) := by
  if hCorner : (u1 = 0 ∧ u0 = -95232) ∨ (u1 = 0 ∧ u0 = -1) then
    rcases hCorner with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  else
    have hu0Strict : -95232 < u0 := by
      rcases hu0Lo with h | h
      · exact h
      · exact absurd (Or.inl h) hCorner
    clear hu0Lo
    have hv : ((Fq204.ofInt ((u1 : Int) * 190464 + u0)).val : Int) =
        ((u1 : Int) * 190464 + u0) % (8380417 : Int) := Fq204.ofInt_val _
    unfold decompose
    if hWrap : u1 = 0 ∧ u0 < 0 then
      rcases hWrap with ⟨hu1Zero, hu0Neg⟩
      subst hu1Zero
      have hu0NeM1 : u0 ≠ -1 := fun h => hCorner (Or.inr ⟨rfl, h⟩)
      clear hCorner
      have hu0LeMinus2 : u0 ≤ -2 := by omega
      simp only [Int.ofNat_zero, Int.zero_mul, Int.zero_add] at hv ⊢
      have hMod : u0 % (8380417 : Int) = 8380417 + u0 := by
        rw [← Int.add_emod_right u0 (8380417 : Int)]
        have hEq : u0 + (8380417 : Int) = 8380417 + u0 := by omega
        rw [hEq]
        exact Int.emod_eq_of_lt (by omega) (by omega)
      rw [hMod] at hv
      generalize (Fq204.ofInt u0).val = n at hv ⊢
      have hnDiv : n / 190464 = 43 := by omega
      have hgt : 95232 < n % 190464 := by omega
      have htop : (n : Int) - (((n % 190464 : Nat) : Int) - 190464) = 8380416 := by omega
      simp only [hgt, ↓reduceIte, htop]
      exact Prod.ext rfl (by omega)
    else
      have hNonneg : 0 ≤ (u1 : Int) * 190464 + u0 := by
        rcases Nat.eq_zero_or_pos u1 with h0 | hpos
        · have hu0nn : ¬ (u0 < 0) := fun h => hWrap ⟨h0, h⟩
          clear hWrap hCorner
          omega
        · clear hWrap hCorner
          omega
      clear hWrap hCorner
      have hMod : ((u1 : Int) * 190464 + u0) % (8380417 : Int) = (u1 : Int) * 190464 + u0 :=
        Int.emod_eq_of_lt hNonneg (by omega)
      rw [hMod] at hv
      generalize (Fq204.ofInt ((u1 : Int) * 190464 + u0)).val = n at hv ⊢
      dsimp only
      if hu0Pos : 0 ≤ u0 then
        have hngt : ¬ (95232 < n % 190464) := by omega
        have hntop : (n : Int) - ((n % 190464 : Nat) : Int) ≠ 8380416 := by omega
        simp only [hngt, ↓reduceIte, hntop]
        exact Prod.ext (by omega) (by omega)
      else
        have hgt : 95232 < n % 190464 := by omega
        have hntop : (n : Int) - (((n % 190464 : Nat) : Int) - 190464) ≠ 8380416 := by omega
        simp only [hgt, ↓reduceIte, hntop]
        exact Prod.ext (by omega) (by omega)

/-- **`centered_diff_lt_iff_lowBits_and_highBits`** (certifying `threshold_mldsa.rs` Phase 3):
    For any $r \in \mathbb{Z}_q$, $w_1 < 44$, and $B \le \gamma_2 = 95232$,
    $|(r - w_1 \cdot 2\gamma_2) \bmod^\pm q| < B$ holds if and only if
    $|\text{LowBits}(r)| < B \land \text{HighBits}(r) = w_1$. -/
theorem centered_diff_lt_iff_lowBits_and_highBits (r : Fq204) {w1 B : Nat}
    (hw1 : w1 < 44) (hB : B ≤ 95232) :
    Fq204.centeredAbs (Fq204.sub r (Fq204.ofNat (w1 * 190464))) < B ↔
      (mldsaLowBits r).natAbs < B ∧ mldsaHighBits r = w1 := by
  have hw1Int : Fq204.ofNat (w1 * 190464) = Fq204.ofInt ((w1 : Int) * 190464) := by
    apply Fq204.ext; apply Int.ofNat_inj.mp
    rw [Fq204.ofInt_val, Fq204.ofNat_val, Int.natCast_emod, Int.natCast_mul]
    rfl
  constructor
  · intro hAbs
    let diff := Fq204.sub r (Fq204.ofNat (w1 * 190464))
    let d := Fq204.toCenteredInt diff
    have hdAbs : d.natAbs < B := by dsimp [d]; rwa [Fq204.toCenteredInt_natAbs]
    have hrEq : r = Fq204.ofInt ((w1 : Int) * 190464 + d) := by
      calc r = Fq204.add (Fq204.ofNat (w1 * 190464)) diff := by
            dsimp [diff]
            rw [Fq204.sub_eq_add_neg, Fq204.add_comm _ (Fq204.add r _),
                Fq204.add_assoc, Fq204.add_left_neg, Fq204.add_zero]
      _ = Fq204.add (Fq204.ofInt ((w1 : Int) * 190464)) (Fq204.ofInt d) := by
            rw [hw1Int, Fq204.ofInt_toCenteredInt]
      _ = Fq204.ofInt ((w1 : Int) * 190464 + d) := Fq204.ofInt_add _ _
    have hdec := decompose_ofInt_interior hw1 (u0 := d) (Or.inl (by omega)) (by omega)
    rw [← hrEq] at hdec
    have h1 : mldsaHighBits r = w1 := congrArg Prod.fst hdec
    have h2 : mldsaLowBits r = d := congrArg Prod.snd hdec
    rw [h2]; exact ⟨hdAbs, h1⟩
  · rintro ⟨hLow, hHigh⟩
    obtain ⟨_, _, _, _, hRec⟩ := decompose_reconstruct r
    have hSub : Fq204.sub r (Fq204.ofNat (w1 * 190464)) = Fq204.ofInt (mldsaLowBits r) := by
      conv => lhs; rw [← hRec, hHigh, hw1Int, Fq204.ofInt_sub]
      congr 1; omega
    rw [hSub, ← Fq204.toCenteredInt_natAbs,
        Fq204.toCenteredInt_ofInt_eq (by omega) (by omega)]
    exact hLow

/-- FIPS 204 Lemma 1 corollary: whenever $|\text{LowBits}(w - cs_2)| < \gamma_2 - \beta$ and
    $|cs_2 \bmod^\pm q| \le \beta$, $\text{HighBits}(w - cs_2) = \text{HighBits}(w)$. -/
theorem highBits_sub_eq_of_lowBits_lt (w cs2 : Fq204) {beta : Nat}
    (hBeta : beta ≤ 95232)
    (hLow : (mldsaLowBits (Fq204.sub w cs2)).natAbs < 95232 - beta)
    (hCs2 : Fq204.centeredAbs cs2 ≤ beta) :
    mldsaHighBits (Fq204.sub w cs2) = mldsaHighBits w := by
  let u := Fq204.sub w cs2
  change (mldsaLowBits u).natAbs < 95232 - beta at hLow
  obtain ⟨hu1Lt, _, _, -, huRec⟩ := decompose_reconstruct u
  let e := Fq204.toCenteredInt cs2
  have heAbs : e.natAbs ≤ beta := by dsimp [e]; rwa [Fq204.toCenteredInt_natAbs]
  have hu0Bounds : -((95232 - beta : Nat) : Int) < mldsaLowBits u ∧
      mldsaLowBits u < ((95232 - beta : Nat) : Int) := by constructor <;> omega
  have heBounds : -(beta : Int) ≤ e ∧ e ≤ (beta : Int) := by constructor <;> omega
  have hwEq : w = Fq204.ofInt ((mldsaHighBits u : Int) * 190464 + (mldsaLowBits u + e)) := by
    calc w = Fq204.add u cs2 := by
          dsimp [u]
          rw [Fq204.sub_eq_add_neg, Fq204.add_assoc, Fq204.add_left_neg, Fq204.add_zero]
    _ = Fq204.add (Fq204.ofInt ((mldsaHighBits u : Int) * 190464 + mldsaLowBits u)) (Fq204.ofInt e) := by
          rw [huRec, Fq204.ofInt_toCenteredInt]
    _ = Fq204.ofInt ((mldsaHighBits u : Int) * 190464 + (mldsaLowBits u + e)) := by
          rw [Fq204.ofInt_add, Int.add_assoc]
  have hdecW := decompose_ofInt_interior hu1Lt (u0 := mldsaLowBits u + e) (Or.inl (by omega)) (by omega)
  rw [← hwEq] at hdecW
  exact (congrArg Prod.fst hdecW).symm

/-- Exact NIST FIPS 204 `MakeHint(z, r)` (`Algorithm 39`). -/
@[expose] def makeHint (z r : Fq204) : Bool :=
  decide (mldsaHighBits r ≠ mldsaHighBits (Fq204.add r z))

/-- Exact NIST FIPS 204 `UseHint(h, r)` (`Algorithm 40`, `ML-DSA-44` $m = 44$). -/
@[expose] def useHint (h : Bool) (r : Fq204) : Nat :=
  let (r1, r0) := decompose r
  if !h then r1
  else if 0 < r0 then
    if r1 + 1 = 44 then 0 else r1 + 1
  else
    if r1 = 0 then 43 else r1 - 1

/-- **Scalar FIPS 204 Supporting Hint Lemma (`useHint_makeHint_eq_highBits`)**:
    For every $u \in \mathbb{Z}_q$ with $|\text{LowBits}(u)| < \gamma_2$ and every $ct_0 \in \mathbb{Z}_q$
    with $|ct_0 \bmod^\pm q| < \gamma_2$,
    `useHint (makeHint (-ct0) (u + ct0)) (u + ct0) = mldsaHighBits u`. -/
theorem useHint_makeHint_eq_highBits (u ct0 : Fq204)
    (hLow : (mldsaLowBits u).natAbs < 95232)
    (hCt0 : Fq204.centeredAbs ct0 < 95232) :
    useHint (makeHint (Fq204.neg ct0) (Fq204.add u ct0)) (Fq204.add u ct0) = mldsaHighBits u := by
  have hCancel : Fq204.add (Fq204.add u ct0) (Fq204.neg ct0) = u := by
    rw [Fq204.add_assoc, Fq204.add_right_neg, Fq204.add_zero]
  unfold makeHint useHint
  rw [hCancel]
  obtain ⟨hu1Lt, _, _, -, huRec⟩ := decompose_reconstruct u
  let u1 := mldsaHighBits u
  let u0 := mldsaLowBits u
  let e := Fq204.toCenteredInt ct0
  have hu0Bounds : -95232 < u0 ∧ u0 < 95232 := by dsimp [u0]; constructor <;> omega
  have heAbs : e.natAbs < 95232 := by dsimp [e]; rwa [Fq204.toCenteredInt_natAbs]
  have heBounds : -95232 < e ∧ e < 95232 := by constructor <;> omega
  have hrEq : Fq204.add u ct0 = Fq204.ofInt ((u1 : Int) * 190464 + (u0 + e)) := by
    conv => lhs; rw [← huRec, ← Fq204.ofInt_toCenteredInt ct0]
    rw [Fq204.ofInt_add]; dsimp [u1, u0, e]; rw [Int.add_assoc]
  let s := u0 + e
  if hsMid : -95232 < s ∧ s ≤ 95232 then
    have hdecR : decompose (Fq204.add u ct0) = (u1, s) := by
      rw [hrEq]; exact decompose_ofInt_interior hu1Lt (Or.inl hsMid.1) hsMid.2
    have hr1 : mldsaHighBits (Fq204.add u ct0) = u1 := by unfold mldsaHighBits; rw [hdecR]
    change (let (r1, r0) := decompose (Fq204.add u ct0)
            if !decide (mldsaHighBits (Fq204.add u ct0) ≠ u1) then r1
            else if 0 < r0 then if r1 + 1 = 44 then 0 else r1 + 1
            else if r1 = 0 then 43 else r1 - 1) = u1
    rw [hdecR, hr1]
    simp only [ne_eq, not_true_eq_false, decide_false, Bool.not_false, ↓reduceIte]
  else if hsHi : 95232 < s then
    clear hsMid
    let w0 := s - 190464
    have hw0Bounds : -95232 < w0 ∧ w0 < 0 := by dsimp [w0, s] at *; constructor <;> omega
    if hu1Top : u1 + 1 = 44 then
      have hu1Val : u1 = 43 := by omega
      have hrEqWrap : Fq204.add u ct0 = Fq204.ofInt (((0 : Nat) : Int) * 190464 + (w0 - 1)) := by
        rw [hrEq]; apply Fq204.ext; apply Int.ofNat_inj.mp
        rw [Fq204.ofInt_val, Fq204.ofInt_val]; unfold mldsaQ
        have hDiff : (u1 : Int) * 190464 + (u0 + e) =
            (((0 : Nat) : Int) * 190464 + (w0 - 1)) + ((8380417 : Nat) : Int) := by
          dsimp [w0, s] at *; omega
        rw [hDiff, Int.add_emod_right]
      have hdecR : decompose (Fq204.add u ct0) = (0, w0 - 1) := by
        rw [hrEqWrap]
        exact decompose_ofInt_interior (u1 := 0) (u0 := w0 - 1) (by omega)
          (by
            if hInt : -95232 < w0 - 1 then exact Or.inl hInt
            else exact Or.inr ⟨rfl, by omega⟩)
          (by omega)
      have hr1 : mldsaHighBits (Fq204.add u ct0) = 0 := by unfold mldsaHighBits; rw [hdecR]
      have hne : (0 : Nat) ≠ u1 := by omega
      have hnPos : ¬ (0 < w0 - 1) := by omega
      change (let (r1, r0) := decompose (Fq204.add u ct0)
              if !decide (mldsaHighBits (Fq204.add u ct0) ≠ u1) then r1
              else if 0 < r0 then if r1 + 1 = 44 then 0 else r1 + 1
              else if r1 = 0 then 43 else r1 - 1) = u1
      rw [hdecR, hr1, decide_eq_true hne]
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hnPos]
      omega
    else
      have hrEqCarry : Fq204.add u ct0 = Fq204.ofInt (((u1 + 1 : Nat) : Int) * 190464 + w0) := by
        rw [hrEq]; apply congrArg Fq204.ofInt; dsimp [w0, s]; omega
      have hdecR : decompose (Fq204.add u ct0) = (u1 + 1, w0) := by
        rw [hrEqCarry]
        exact decompose_ofInt_interior (u1 := u1 + 1) (u0 := w0) (by omega) (Or.inl hw0Bounds.1) (by omega)
      have hr1 : mldsaHighBits (Fq204.add u ct0) = u1 + 1 := by unfold mldsaHighBits; rw [hdecR]
      have hne : u1 + 1 ≠ u1 := by omega
      have hnPos : ¬ (0 < w0) := by omega
      have hnz : u1 + 1 ≠ 0 := by omega
      change (let (r1, r0) := decompose (Fq204.add u ct0)
              if !decide (mldsaHighBits (Fq204.add u ct0) ≠ u1) then r1
              else if 0 < r0 then if r1 + 1 = 44 then 0 else r1 + 1
              else if r1 = 0 then 43 else r1 - 1) = u1
      rw [hdecR, hr1, decide_eq_true hne]
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hnPos, hnz]
      omega
  else
    have hsLe : s ≤ -95232 :=
      Int.not_lt.mp (fun h => hsMid ⟨h, Int.not_lt.mp hsHi⟩)
    clear hsMid
    if hsExactZero : u1 = 0 ∧ s = -95232 then
      rcases hsExactZero with ⟨hu1Zero, hsEq⟩
      have hSumEq : u0 + e = -95232 := hsEq
      have hdecR : decompose (Fq204.add u ct0) = (0, -95232) := by
        rw [hrEq, hu1Zero, hSumEq]; decide
      have hr1 : mldsaHighBits (Fq204.add u ct0) = 0 := by unfold mldsaHighBits; rw [hdecR]
      change (let (r1, r0) := decompose (Fq204.add u ct0)
              if !decide (mldsaHighBits (Fq204.add u ct0) ≠ u1) then r1
              else if 0 < r0 then if r1 + 1 = 44 then 0 else r1 + 1
              else if r1 = 0 then 43 else r1 - 1) = u1
      rw [hdecR, hr1, hu1Zero]
      simp only [ne_eq, not_true_eq_false, decide_false, Bool.not_false, ↓reduceIte]
    else
      let w0 := s + 190464
      if hu1Zero : u1 = 0 then
        have hsNe : s ≠ -95232 := fun h => hsExactZero ⟨hu1Zero, h⟩
        clear hsExactZero
        have hsLt : s < -95232 := by omega
        have hw0Bounds : 0 < w0 ∧ w0 < 95232 := by dsimp [w0, s] at *; constructor <;> omega
        have hrEqBorrow : Fq204.add u ct0 = Fq204.ofInt (((43 : Nat) : Int) * 190464 + (w0 + 1)) := by
          rw [hrEq]; apply Fq204.ext; apply Int.ofNat_inj.mp
          rw [Fq204.ofInt_val, Fq204.ofInt_val]; unfold mldsaQ
          have hDiff : ((u1 : Int) * 190464 + (u0 + e)) + ((8380417 : Nat) : Int) =
              ((43 : Nat) : Int) * 190464 + (w0 + 1) := by
            dsimp [w0, s] at *; omega
          rw [← Int.add_emod_right ((u1 : Int) * 190464 + (u0 + e)) ((8380417 : Nat) : Int), hDiff]
        have hdecR : decompose (Fq204.add u ct0) = (43, w0 + 1) := by
          rw [hrEqBorrow]
          exact decompose_ofInt_interior (u1 := 43) (u0 := w0 + 1) (by omega) (Or.inl (by omega)) (by omega)
        have hr1 : mldsaHighBits (Fq204.add u ct0) = 43 := by unfold mldsaHighBits; rw [hdecR]
        have hne : (43 : Nat) ≠ u1 := by omega
        have hPos : 0 < w0 + 1 := by omega
        change (let (r1, r0) := decompose (Fq204.add u ct0)
                if !decide (mldsaHighBits (Fq204.add u ct0) ≠ u1) then r1
                else if 0 < r0 then if r1 + 1 = 44 then 0 else r1 + 1
                else if r1 = 0 then 43 else r1 - 1) = u1
        rw [hdecR, hr1, decide_eq_true hne]
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hPos]
        omega
      else
        clear hsExactZero
        have hw0Bounds : 0 < w0 ∧ w0 ≤ 95232 := by dsimp [w0, s] at *; constructor <;> omega
        have hrEqBorrow : Fq204.add u ct0 = Fq204.ofInt (((u1 - 1 : Nat) : Int) * 190464 + w0) := by
          rw [hrEq]; apply congrArg Fq204.ofInt; dsimp [w0, s]; omega
        have hdecR : decompose (Fq204.add u ct0) = (u1 - 1, w0) := by
          rw [hrEqBorrow]
          exact decompose_ofInt_interior (u1 := u1 - 1) (u0 := w0) (by omega) (Or.inl (by omega)) (by omega)
        have hr1 : mldsaHighBits (Fq204.add u ct0) = u1 - 1 := by unfold mldsaHighBits; rw [hdecR]
        have hne : u1 - 1 ≠ u1 := by omega
        have hPos : 0 < w0 := by omega
        have hnTop : (u1 - 1) + 1 ≠ 44 := by omega
        change (let (r1, r0) := decompose (Fq204.add u ct0)
                if !decide (mldsaHighBits (Fq204.add u ct0) ≠ u1) then r1
                else if 0 < r0 then if r1 + 1 = 44 then 0 else r1 + 1
                else if r1 = 0 then 43 else r1 - 1) = u1
        rw [hdecR, hr1, decide_eq_true hne]
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hPos, hnTop]
        omega

/-- **`#tooth` (`tooth_useHint_fails_when_ct0_ge_gamma2`)**:
    Dropping the `< γ_2` norm bound on `c * t0` breaks `UseHint` recovery even when
    `‖LowBits(u)‖_∞ < γ_2 - β` (`95000 < 95154`). -/
theorem tooth_useHint_fails_when_ct0_ge_gamma2 :
    let u : Fq204 := ⟨95000, by decide⟩
    let ct0 : Fq204 := ⟨95465, by decide⟩
    (mldsaLowBits u).natAbs < mldsa44Gamma2 - mldsa44Beta ∧
    mldsa44Gamma2 < Fq204.centeredAbs ct0 ∧
    useHint (makeHint (Fq204.neg ct0) (Fq204.add u ct0)) (Fq204.add u ct0) ≠ mldsaHighBits u := by
  decide

/-! #### Module-Lattice Lifting ($R_q^4$ & $R_q^{4 \times 4}$) & `highBits_az_sub_ct_eq_w1` -/

/-- `ML-DSA-44` length-4 module vector over $R_q = \mathbb{Z}_q[X]/(X^{256} + 1)$. -/
abbrev PolyVec4 := Fin 4 → Poly256

/-- `ML-DSA-44` $4 \times 4$ public matrix over $R_q$. -/
abbrev PolyMat4 := Fin 4 → Fin 4 → Poly256

def addVec4 (u v : PolyVec4) : PolyVec4 := fun i => PolyTree.add (u i) (v i)
def subVec4 (u v : PolyVec4) : PolyVec4 := fun i => PolyTree.sub (u i) (v i)
def negVec4 (u : PolyVec4) : PolyVec4 := fun i => PolyTree.neg (u i)
@[expose] def mulPolyVec4 (c : Poly256) (v : PolyVec4) : PolyVec4 := fun i => negacyclicMul c (v i)

def matVecMul4 (A : PolyMat4) (v : PolyVec4) : PolyVec4 := fun i =>
  PolyTree.add
    (PolyTree.add (negacyclicMul (A i ⟨0, by decide⟩) (v ⟨0, by decide⟩))
                  (negacyclicMul (A i ⟨1, by decide⟩) (v ⟨1, by decide⟩)))
    (PolyTree.add (negacyclicMul (A i ⟨2, by decide⟩) (v ⟨2, by decide⟩))
                  (negacyclicMul (A i ⟨3, by decide⟩) (v ⟨3, by decide⟩)))

theorem matVecMul4_add (A : PolyMat4) (u v : PolyVec4) :
    matVecMul4 A (addVec4 u v) = addVec4 (matVecMul4 A u) (matVecMul4 A v) := by
  funext i
  dsimp only [matVecMul4, addVec4]
  rw [negacyclicMul_left_distrib, negacyclicMul_left_distrib,
      negacyclicMul_left_distrib, negacyclicMul_left_distrib,
      polyTree_add_add_comm (negacyclicMul _ (u ⟨0, _⟩)),
      polyTree_add_add_comm (negacyclicMul _ (u ⟨2, _⟩)),
      polyTree_add_add_comm (PolyTree.add _ _)]

theorem matVecMul4_mulPoly (A : PolyMat4) (c : Poly256) (v : PolyVec4) :
    matVecMul4 A (mulPolyVec4 c v) = mulPolyVec4 c (matVecMul4 A v) := by
  funext i
  dsimp only [matVecMul4, mulPolyVec4]
  have hSwapMul : ∀ x y z : Poly256, negacyclicMul x (negacyclicMul y z) =
      negacyclicMul y (negacyclicMul x z) := fun x y z => by
    rw [← negacyclicMul_assoc, negacyclicMul_comm x y, negacyclicMul_assoc]
  simp only [negacyclicMul_left_distrib, hSwapMul (A i _) c]

/-- Inductive tree of natural-number `HighBits` values ($2^d$ integers in $[0, 44)$). -/
inductive NatTree : Nat → Type where
  | leaf (n : Nat) : NatTree 0
  | branch {d : Nat} (lo hi : NatTree d) : NatTree (d + 1)
  deriving DecidableEq, Repr

/-- Inductive tree of boolean hint flags ($2^d$ bits). -/
inductive HintTree : Nat → Type where
  | leaf (b : Bool) : HintTree 0
  | branch {d : Nat} (lo hi : HintTree d) : HintTree (d + 1)
  deriving DecidableEq, Repr

def HintTree.weight : {d : Nat} → HintTree d → Nat
  | 0, .leaf b => if b then 1 else 0
  | _ + 1, .branch h0 h1 => weight h0 + weight h1

def power2RoundHighTree : {d : Nat} → PolyTree d → PolyTree d
  | 0, .leaf r => .leaf (Fq204.ofNat ((power2Round r).1 * 8192))
  | _ + 1, .branch lo hi => .branch (power2RoundHighTree lo) (power2RoundHighTree hi)

def power2RoundLowTree : {d : Nat} → PolyTree d → PolyTree d
  | 0, .leaf r => .leaf (Fq204.ofInt (power2Round r).2)
  | _ + 1, .branch lo hi => .branch (power2RoundLowTree lo) (power2RoundLowTree hi)

theorem power2RoundTree_reconstruct : ∀ {d : Nat} (p : PolyTree d),
    PolyTree.add (power2RoundHighTree p) (power2RoundLowTree p) = p
  | 0, .leaf r => congrArg PolyTree.leaf <| by
    have hmul : Fq204.ofNat ((power2Round r).1 * 8192) =
        Fq204.mul (Fq204.ofNat (power2Round r).1) (Fq204.ofNat 8192) := by
      apply Fq204.ext; simp [Fq204.ofNat_val, Fq204.mul_val, Nat.mul_mod]
    rw [hmul]
    exact (power2Round_reconstruct r).2.2.2.2
  | _ + 1, .branch lo hi => by
    simp only [power2RoundHighTree, power2RoundLowTree, PolyTree.add, power2RoundTree_reconstruct]

def highBitsTree : {d : Nat} → PolyTree d → NatTree d
  | 0, .leaf r => .leaf (mldsaHighBits r)
  | _ + 1, .branch lo hi => .branch (highBitsTree lo) (highBitsTree hi)

def lowBitsNormTree : {d : Nat} → PolyTree d → Nat
  | 0, .leaf r => (mldsaLowBits r).natAbs
  | _ + 1, .branch lo hi => max (lowBitsNormTree lo) (lowBitsNormTree hi)

def makeHintTree : {d : Nat} → PolyTree d → PolyTree d → HintTree d
  | 0, .leaf z, .leaf r => .leaf (makeHint z r)
  | _ + 1, .branch z0 z1, .branch r0 r1 => .branch (makeHintTree z0 r0) (makeHintTree z1 r1)

def useHintTree : {d : Nat} → HintTree d → PolyTree d → NatTree d
  | 0, .leaf h, .leaf r => .leaf (useHint h r)
  | _ + 1, .branch h0 h1, .branch r0 r1 => .branch (useHintTree h0 r0) (useHintTree h1 r1)

theorem useHintTree_makeHintTree : ∀ {d : Nat} (u ct0 : PolyTree d),
    lowBitsNormTree u < 95232 →
    PolyTree.infNorm ct0 < 95232 →
    useHintTree (makeHintTree (PolyTree.neg ct0) (PolyTree.add u ct0)) (PolyTree.add u ct0) =
      highBitsTree u
  | 0, .leaf u, .leaf ct0, hLow, hCt0 =>
    congrArg NatTree.leaf (useHint_makeHint_eq_highBits u ct0 hLow hCt0)
  | _ + 1, .branch u0 u1, .branch c0 c1, hLow, hCt0 => by
    simp only [lowBitsNormTree, PolyTree.infNorm] at hLow hCt0
    simp only [PolyTree.neg, PolyTree.add, makeHintTree, useHintTree, highBitsTree,
      useHintTree_makeHintTree u0 c0 (by omega) (by omega),
      useHintTree_makeHintTree u1 c1 (by omega) (by omega)]

theorem highBitsTree_sub_eq_of_lowBits_lt : ∀ {d : Nat} (w cs2 : PolyTree d) {beta : Nat},
    beta ≤ 95232 →
    lowBitsNormTree (PolyTree.sub w cs2) < 95232 - beta →
    PolyTree.infNorm cs2 ≤ beta →
    highBitsTree (PolyTree.sub w cs2) = highBitsTree w
  | 0, .leaf w, .leaf cs2, _, hB, hLow, hCs2 =>
    congrArg NatTree.leaf (highBits_sub_eq_of_lowBits_lt w cs2 hB hLow hCs2)
  | _ + 1, .branch w0 w1, .branch c0 c1, _, hB, hLow, hCs2 => by
    simp only [PolyTree.sub, lowBitsNormTree, PolyTree.infNorm] at hLow hCs2
    simp only [PolyTree.sub, highBitsTree,
      highBitsTree_sub_eq_of_lowBits_lt w0 c0 hB (by omega) (by omega),
      highBitsTree_sub_eq_of_lowBits_lt w1 c1 hB (by omega) (by omega)]

def power2RoundHighVec4 (t : PolyVec4) : PolyVec4 := fun i => power2RoundHighTree (t i)
def power2RoundLowVec4 (t : PolyVec4) : PolyVec4 := fun i => power2RoundLowTree (t i)
def highBitsVec4 (v : PolyVec4) : Fin 4 → NatTree 8 := fun i => highBitsTree (v i)
def makeHintVec4 (z r : PolyVec4) : Fin 4 → HintTree 8 := fun i => makeHintTree (z i) (r i)
def useHintVec4 (h : Fin 4 → HintTree 8) (r : PolyVec4) : Fin 4 → NatTree 8 :=
  fun i => useHintTree (h i) (r i)

def infNormVec4 (v : PolyVec4) : Nat :=
  max (max (PolyTree.infNorm (v ⟨0, by decide⟩)) (PolyTree.infNorm (v ⟨1, by decide⟩)))
      (max (PolyTree.infNorm (v ⟨2, by decide⟩)) (PolyTree.infNorm (v ⟨3, by decide⟩)))

def lowBitsNormVec4 (v : PolyVec4) : Nat :=
  max (max (lowBitsNormTree (v ⟨0, by decide⟩)) (lowBitsNormTree (v ⟨1, by decide⟩)))
      (max (lowBitsNormTree (v ⟨2, by decide⟩)) (lowBitsNormTree (v ⟨3, by decide⟩)))

def hintWeightVec4 (h : Fin 4 → HintTree 8) : Nat :=
  HintTree.weight (h ⟨0, by decide⟩) + HintTree.weight (h ⟨1, by decide⟩) +
  HintTree.weight (h ⟨2, by decide⟩) + HintTree.weight (h ⟨3, by decide⟩)

/-- **Module-Lattice Verification Identity (`az_sub_ct1_eq_w_sub_cs2_add_ct0`)**:
    Over $R_q^4$, whenever $z = y + c \cdot s_1$, $w = A \cdot y$, and $t = A \cdot s_1 + s_2 = t_1 \cdot 2^d + t_0$,
    $A \cdot z - c \cdot (t_1 \cdot 2^d) = (w - c \cdot s_2) + c \cdot t_0$ identically. -/
theorem az_sub_ct1_eq_w_sub_cs2_add_ct0
    (A : PolyMat4) (s1 s2 y : PolyVec4) (c : Poly256) :
    let t := addVec4 (matVecMul4 A s1) s2
    let t1Scaled := power2RoundHighVec4 t
    let t0 := power2RoundLowVec4 t
    let w := matVecMul4 A y
    let z := addVec4 y (mulPolyVec4 c s1)
    subVec4 (matVecMul4 A z) (mulPolyVec4 c t1Scaled) =
      addVec4 (subVec4 w (mulPolyVec4 c s2)) (mulPolyVec4 c t0) := by
  intro t t1Scaled t0 w z
  have htSplit : addVec4 t1Scaled t0 = t := by
    funext i; exact power2RoundTree_reconstruct (t i)
  have hAz : matVecMul4 A z = addVec4 w (mulPolyVec4 c (matVecMul4 A s1)) := by
    dsimp [z, w]; rw [matVecMul4_add, matVecMul4_mulPoly]
  rw [hAz]
  funext i
  have htRow : PolyTree.add (t1Scaled i) (t0 i) = PolyTree.add (matVecMul4 A s1 i) (s2 i) :=
    congrFun htSplit i
  dsimp only [addVec4, subVec4, mulPolyVec4]
  apply poly256_add_left_cancel (a := negacyclicMul c (t1Scaled i))
  have hSubCancel : ∀ x y : Poly256, PolyTree.add y (PolyTree.sub x y) = x := fun x y => by
    rw [polyTree_sub_eq_add_neg, polyTree_add_comm y, polyTree_add_assoc,
        polyTree_add_left_neg, polyTree_add_zero]
  rw [hSubCancel]
  have hRhs :
      PolyTree.add (negacyclicMul c (t1Scaled i))
        (PolyTree.add (PolyTree.sub (w i) (negacyclicMul c (s2 i))) (negacyclicMul c (t0 i))) =
      PolyTree.add (PolyTree.sub (w i) (negacyclicMul c (s2 i)))
        (negacyclicMul c (PolyTree.add (t1Scaled i) (t0 i))) := by
    rw [negacyclicMul_left_distrib, polyTree_add_comm (negacyclicMul c (t1Scaled i)),
        polyTree_add_assoc, polyTree_add_comm (negacyclicMul c (t0 i))]
  rw [hRhs, htRow, negacyclicMul_left_distrib,
      polyTree_add_comm (negacyclicMul c (matVecMul4 A s1 i)) (negacyclicMul c (s2 i)),
      ← polyTree_add_assoc, polyTree_add_comm (PolyTree.sub (w i) _), hSubCancel]

/-- **Flagship §1 Theorem — Exact `HighBits` Shift Lemma (`highBits_az_sub_ct_eq_w1`)**:
    Over $R_q = \mathbb{Z}_{8380417}[X]/(X^{256} + 1)$ (`ML-DSA-44`, $k = \ell = 4$), whenever
    $z = y + c \cdot s_1$, $w = A \cdot y$, $t = A \cdot s_1 + s_2$,
    $\|\text{LowBits}(w - c \cdot s_2)\|_\infty < \gamma_2 - \beta$, and $\|c \cdot t_0\|_\infty < \gamma_2$,
    `UseHint(MakeHint(-c*t0, w - c*s2 + c*t0), A*z - c*t1*2^d) = HighBits(w - c*s2)`. -/
theorem highBits_az_sub_ct_eq_w1
    (A : PolyMat4) (s1 s2 y : PolyVec4) (c : Poly256) (beta : Nat)
    (hLow : lowBitsNormVec4 (subVec4 (matVecMul4 A y) (mulPolyVec4 c s2)) < mldsa44Gamma2 - beta)
    (hCt0 : infNormVec4 (mulPolyVec4 c (power2RoundLowVec4 (addVec4 (matVecMul4 A s1) s2))) < mldsa44Gamma2) :
    let t := addVec4 (matVecMul4 A s1) s2
    let t1Scaled := power2RoundHighVec4 t
    let t0 := power2RoundLowVec4 t
    let w := matVecMul4 A y
    let z := addVec4 y (mulPolyVec4 c s1)
    let u := subVec4 w (mulPolyVec4 c s2)
    let ct0 := mulPolyVec4 c t0
    useHintVec4 (makeHintVec4 (negVec4 ct0) (addVec4 u ct0))
                (subVec4 (matVecMul4 A z) (mulPolyVec4 c t1Scaled)) =
      highBitsVec4 u := by
  intro t t1Scaled t0 w z u ct0
  have hId := az_sub_ct1_eq_w_sub_cs2_add_ct0 A s1 s2 y c
  dsimp only at hId
  rw [hId]
  funext i
  have hFinCases : i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ ∨ i = ⟨2, by decide⟩ ∨ i = ⟨3, by decide⟩ := by
    rcases i with ⟨idx, hidx⟩
    have hIdx : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 := by omega
    rcases hIdx with rfl | rfl | rfl | rfl <;> simp
  rcases hFinCases with rfl | rfl | rfl | rfl
  all_goals
    dsimp only [useHintVec4, makeHintVec4, highBitsVec4, negVec4, addVec4, u, ct0, w, t0, t]
    unfold lowBitsNormVec4 mldsa44Gamma2 at hLow
    unfold infNormVec4 mldsa44Gamma2 at hCt0
    exact useHintTree_makeHintTree _ _ (by omega) (by omega)

def idMat4 : PolyMat4 :=
  fun i j => if i = j then PolyTree.constUnit 8 else PolyTree.zero 8

private theorem matVecMul4_idMat4 (v : PolyVec4) : matVecMul4 idMat4 v = v := by
  funext i
  have hFinCases : i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ ∨ i = ⟨2, by decide⟩ ∨ i = ⟨3, by decide⟩ := by
    rcases i with ⟨idx, hidx⟩
    have hIdx : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 := by omega
    rcases hIdx with rfl | rfl | rfl | rfl <;> simp
  rcases hFinCases with rfl | rfl | rfl | rfl
  all_goals
    dsimp only [matVecMul4, idMat4]
    simp only [↓reduceIte, Fin.mk.injEq, Nat.reduceEqDiff,
      negacyclicMul_one_left, negacyclicMul_zero_left,
      polyTree_add_zero, polyTree_zero_add]

/-- Cyclic coordinate shift: row `i` selects coordinate `i + 1`. Not the identity. -/
def shiftMat4 : PolyMat4 :=
  fun i j => if (i.val + 1) % 4 = j.val then PolyTree.constUnit 8 else PolyTree.zero 8

private theorem matVecMul4_shiftMat4_const (p : Poly256) :
    matVecMul4 shiftMat4 (fun _ => p) = fun _ => p := by
  funext i
  have hFinCases : i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ ∨ i = ⟨2, by decide⟩ ∨ i = ⟨3, by decide⟩ := by
    rcases i with ⟨idx, hidx⟩
    have hIdx : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 := by omega
    rcases hIdx with rfl | rfl | rfl | rfl <;> simp
  rcases hFinCases with rfl | rfl | rfl | rfl
  all_goals
    dsimp only [matVecMul4, shiftMat4]
    simp only [↓reduceIte, Nat.reduceAdd, Nat.reduceMod, Nat.reduceEqDiff,
      negacyclicMul_one_left, negacyclicMul_zero_left,
      polyTree_add_zero, polyTree_zero_add]

theorem shiftMat4_ne_idMat4 : shiftMat4 ≠ idMat4 := by
  intro h
  have h00 := congrFun (congrFun h ⟨0, by decide⟩) ⟨0, by decide⟩
  simp only [shiftMat4, idMat4, ↓reduceIte, Nat.reduceAdd, Nat.reduceMod, Nat.reduceEqDiff] at h00
  exact absurd h00 (by decide)

def polyTreeConstLeaf : (d : Nat) → Fq204 → PolyTree d
  | 0, x => .leaf x
  | d + 1, x => .branch (polyTreeConstLeaf d x) (polyTreeConstLeaf d x)

private theorem polyTreeConstLeaf_zero_eq : ∀ (d : Nat), polyTreeConstLeaf d Fq204.zero = PolyTree.zero d
  | 0 => rfl
  | d + 1 => by simp only [polyTreeConstLeaf, PolyTree.zero, polyTreeConstLeaf_zero_eq d]

private theorem polyTreeConstLeaf_add (a b : Fq204) : ∀ (d : Nat),
    PolyTree.add (polyTreeConstLeaf d a) (polyTreeConstLeaf d b) = polyTreeConstLeaf d (Fq204.add a b)
  | 0 => rfl
  | d + 1 => by simp only [polyTreeConstLeaf, PolyTree.add, polyTreeConstLeaf_add a b d]

private theorem polyTreeConstLeaf_neg (a : Fq204) : ∀ (d : Nat),
    PolyTree.neg (polyTreeConstLeaf d a) = polyTreeConstLeaf d (Fq204.neg a)
  | 0 => rfl
  | d + 1 => by simp only [polyTreeConstLeaf, PolyTree.neg, polyTreeConstLeaf_neg a d]

theorem polyTreeConstLeaf_infNorm (a : Fq204) : ∀ (d : Nat),
    PolyTree.infNorm (polyTreeConstLeaf d a) = Fq204.centeredAbs a
  | 0 => rfl
  | d + 1 => by simp only [polyTreeConstLeaf, PolyTree.infNorm, polyTreeConstLeaf_infNorm a d, Nat.max_self]

private theorem polyTreeConstLeaf_lowBitsNorm (a : Fq204) : ∀ (d : Nat),
    lowBitsNormTree (polyTreeConstLeaf d a) = (mldsaLowBits a).natAbs
  | 0 => rfl
  | d + 1 => by simp only [polyTreeConstLeaf, lowBitsNormTree, polyTreeConstLeaf_lowBitsNorm a d, Nat.max_self]

private theorem polyTreeConstLeaf_power2RoundLow (a : Fq204) : ∀ (d : Nat),
    power2RoundLowTree (polyTreeConstLeaf d a) = polyTreeConstLeaf d (Fq204.ofInt (power2Round a).2)
  | 0 => rfl
  | d + 1 => by simp only [polyTreeConstLeaf, power2RoundLowTree, polyTreeConstLeaf_power2RoundLow a d]

private theorem polyTreeConstLeaf_hintWeight (z r : Fq204) : ∀ (d : Nat),
    HintTree.weight (makeHintTree (polyTreeConstLeaf d z) (polyTreeConstLeaf d r)) =
      (2 ^ d) * (if makeHint z r then 1 else 0)
  | 0 => by simp [polyTreeConstLeaf, makeHintTree, HintTree.weight]
  | d + 1 => by
    simp only [polyTreeConstLeaf, makeHintTree, HintTree.weight,
      polyTreeConstLeaf_hintWeight z r d, Nat.pow_succ]
    cases makeHint z r <;> simp <;> omega

/-- Non-vacuous inhabitedness witness for `highBits_az_sub_ct_eq_w1` with nonzero $A, s_1, s_2, y, c$. -/
theorem highBits_az_sub_ct_eq_w1_inhabited :
    ∃ (A : PolyMat4) (s1 s2 y : PolyVec4) (c : Poly256),
      c ≠ PolyTree.zero 8 ∧
      lowBitsNormVec4 (subVec4 (matVecMul4 A y) (mulPolyVec4 c s2)) < mldsa44Gamma2 - mldsa44Beta ∧
      infNormVec4 (mulPolyVec4 c (power2RoundLowVec4 (addVec4 (matVecMul4 A s1) s2))) < mldsa44Gamma2 := by
  let p1 : Poly256 := polyTreeConstLeaf 8 Fq204.one
  let v1 : PolyVec4 := fun _ => p1
  refine ⟨idMat4, v1, v1, v1, PolyTree.constUnit 8, ?_, ?_, ?_⟩
  · decide
  · have hMv : matVecMul4 idMat4 v1 = v1 := matVecMul4_idMat4 v1
    have hMul : mulPolyVec4 (PolyTree.constUnit 8) v1 = v1 := by
      funext i; exact negacyclicMul_one_left (v1 i)
    rw [hMv, hMul]
    have hSub : subVec4 v1 v1 = (fun _ => polyTreeConstLeaf 8 Fq204.zero) := by
      funext i
      dsimp only [subVec4, v1]
      rw [polyTree_sub_eq_add_neg, polyTree_add_comm, polyTree_add_left_neg, polyTreeConstLeaf_zero_eq]
    rw [hSub]
    unfold lowBitsNormVec4
    dsimp only
    simp only [polyTreeConstLeaf_lowBitsNorm, Nat.max_self]
    decide
  · have hMv : matVecMul4 idMat4 v1 = v1 := matVecMul4_idMat4 v1
    rw [hMv]
    have hMul : ∀ w : PolyVec4, mulPolyVec4 (PolyTree.constUnit 8) w = w := fun w => by
      funext i; exact negacyclicMul_one_left (w i)
    rw [hMul]
    have hAdd : addVec4 v1 v1 = (fun _ => polyTreeConstLeaf 8 (Fq204.add Fq204.one Fq204.one)) := by
      funext i; exact polyTreeConstLeaf_add Fq204.one Fq204.one 8
    rw [hAdd]
    unfold infNormVec4 power2RoundLowVec4
    dsimp only
    simp only [polyTreeConstLeaf_power2RoundLow, polyTreeConstLeaf_infNorm, Nat.max_self]
    decide

/-! ## §2. 2-Phase Committed Threshold `ML-DSA-44` DKG & Aggregate Rejection-Barrier Security -/

/-! ### §2.1 Constructive Honest-Holder Coverage (`subset_honest_holder_exists`) & Subset Intersection -/

def natMemBool (x : Nat) : List Nat → Bool
  | [] => false
  | y :: ys => decide (x = y) || natMemBool x ys

private theorem natMemBool_eq_true_iff (x : Nat) :
    ∀ (l : List Nat), natMemBool x l = true ↔ x ∈ l
  | [] => by simp [natMemBool]
  | y :: ys => by
    simp only [natMemBool, Bool.or_eq_true, decide_eq_true_eq,
      natMemBool_eq_true_iff x ys, List.mem_cons]

private theorem natMemBool_eq_false_iff (x : Nat) (l : List Nat) :
    natMemBool x l = false ↔ x ∉ l := by
  constructor
  · intro hf hm
    rw [(natMemBool_eq_true_iff x l).mpr hm] at hf
    cases hf
  · intro hnm
    cases hb : natMemBool x l
    · rfl
    · exact False.elim (hnm ((natMemBool_eq_true_iff x l).mp hb))

private def eraseFirstNat (x : Nat) : List Nat → List Nat
  | [] => []
  | y :: ys => if x = y then ys else y :: eraseFirstNat x ys

private theorem eraseFirstNat_length_succ {x : Nat} :
    ∀ {l : List Nat}, natMemBool x l = true → (eraseFirstNat x l).length + 1 = l.length
  | [], h => by cases h
  | y :: ys, h => by
    dsimp only [eraseFirstNat]
    if hxy : x = y then
      simp [hxy]
    else
      simp only [natMemBool, decide_eq_false hxy, Bool.false_or] at h
      simp only [hxy, ↓reduceIte, List.length_cons]
      have ih := eraseFirstNat_length_succ h
      omega

private theorem natMemBool_eraseFirstNat_of_ne {z x : Nat} (hne : z ≠ x) :
    ∀ {l : List Nat}, natMemBool z l = true → natMemBool z (eraseFirstNat x l) = true
  | [], h => by cases h
  | y :: ys, h => by
    dsimp only [eraseFirstNat]
    if hxy : x = y then
      subst hxy
      simp only [natMemBool, decide_eq_false hne, Bool.false_or] at h
      simp [h]
    else
      simp only [hxy, ↓reduceIte, natMemBool]
      simp only [natMemBool, Bool.or_eq_true] at h
      rcases h with hzy | hTail
      · simp [hzy]
      · simp [natMemBool_eraseFirstNat_of_ne hne hTail]

private theorem natNodup_length_le_of_subset :
    ∀ {T : List Nat} (C : List Nat),
      T.Nodup →
      (∀ x ∈ T, natMemBool x C = true) →
      T.length ≤ C.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, C, hNodup, hSub => by
    rcases List.nodup_cons.mp hNodup with ⟨hxNotMem, hxsNodup⟩
    have hxMemC : natMemBool x C = true := hSub x (.head xs)
    have hLenC := eraseFirstNat_length_succ hxMemC
    have hSubTail : ∀ z ∈ xs, natMemBool z (eraseFirstNat x C) = true := by
      intro z hz
      have hzx : z ≠ x := fun hEq => hxNotMem (hEq ▸ hz)
      exact natMemBool_eraseFirstNat_of_ne hzx (hSub z (.tail x hz))
    have ih := natNodup_length_le_of_subset (eraseFirstNat x C) hxsNodup hSubTail
    simp only [List.length_cons]
    omega

/-- Constructive (`0 Classical.choice`) finder returning the first party in subset `T`
    outside corrupt set `C`. -/
def findHonestHolder (C : List Nat) : List Nat → Option Nat
  | [] => none
  | x :: xs => if natMemBool x C then findHonestHolder C xs else some x

theorem findHonestHolder_some_spec {C : List Nat} :
    ∀ {T : List Nat} {h : Nat},
      findHonestHolder C T = some h → h ∈ T ∧ h ∉ C
  | [], _, hEq => by cases hEq
  | x :: xs, h, hEq => by
    dsimp only [findHonestHolder] at hEq
    cases hb : natMemBool x C
    · rw [hb] at hEq
      simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hEq
      subst hEq
      exact ⟨.head xs, (natMemBool_eq_false_iff x C).mp hb⟩
    · rw [hb] at hEq
      simp only [↓reduceIte] at hEq
      obtain ⟨hInXs, hNotC⟩ := findHonestHolder_some_spec hEq
      exact ⟨.tail x hInXs, hNotC⟩

theorem findHonestHolder_none_spec {C : List Nat} :
    ∀ {T : List Nat},
      findHonestHolder C T = none → ∀ x ∈ T, natMemBool x C = true
  | [], _, _, hMem => nomatch hMem
  | x :: xs, hNone, z, hMem => by
    dsimp only [findHonestHolder] at hNone
    cases hb : natMemBool x C
    · rw [hb] at hNone; cases hNone
    · rw [hb] at hNone
      simp only [↓reduceIte] at hNone
      rcases List.mem_cons.mp hMem with rfl | hzXs
      · exact hb
      · exact findHonestHolder_none_spec hNone z hzXs

/-- Replicated subset share record $(s_{1,T}, s_{2,T}, t_T)$ verified locally by every honest holder of $T$. -/
structure SubsetShareRecord where
  s1 : PolyVec4
  s2 : PolyVec4
  publicT : PolyVec4

def polyVec4EqBool (u v : PolyVec4) : Bool :=
  decide (u ⟨0, by decide⟩ = v ⟨0, by decide⟩) &&
  decide (u ⟨1, by decide⟩ = v ⟨1, by decide⟩) &&
  decide (u ⟨2, by decide⟩ = v ⟨2, by decide⟩) &&
  decide (u ⟨3, by decide⟩ = v ⟨3, by decide⟩)

theorem polyVec4EqBool_eq_true_iff (u v : PolyVec4) :
    polyVec4EqBool u v = true ↔ u = v := by
  unfold polyVec4EqBool
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩
    funext i
    rcases i with ⟨idx, hidx⟩
    have hCases : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 := by omega
    rcases hCases with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  · rintro rfl
    exact ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩

/-- Local subset-share relation & $\ell_\infty$ bound checked by every honest holder of subset `T`. -/
def validSubsetShare (A : PolyMat4) (etaSub : Nat) (sh : SubsetShareRecord) : Bool :=
  polyVec4EqBool sh.publicT (addVec4 (matVecMul4 A sh.s1) sh.s2) &&
  decide (infNormVec4 sh.s1 ≤ etaSub) &&
  decide (infNormVec4 sh.s2 ≤ etaSub)

theorem validSubsetShare_eq_true_iff (A : PolyMat4) (etaSub : Nat) (sh : SubsetShareRecord) :
    validSubsetShare A etaSub sh = true ↔
      sh.publicT = addVec4 (matVecMul4 A sh.s1) sh.s2 ∧
      infNormVec4 sh.s1 ≤ etaSub ∧
      infNormVec4 sh.s2 ≤ etaSub := by
  unfold validSubsetShare
  simp only [Bool.and_eq_true, polyVec4EqBool_eq_true_iff, decide_eq_true_eq, and_assoc]

/-- **Flagship §2.1 Theorem — Constructive Honest-Holder Coverage (`subset_honest_holder_exists`)**:
    For every threshold configuration $(t, n)$ with $t \ge 1$ and $n \ge 2t - 1$, every corrupt list
    `C` (`C.Nodup`, `C.length ≤ t - 1`), and every replicated subset `T` (`T.Nodup`, `T.length = n - t + 1`):
    1. Constructive `findHonestHolder C T` (`0 Classical.choice`) returns `some h` with `h ∈ T ∧ h ∉ C`;
    2. Whenever every honest custodian `p ∉ C` enforces `validSubsetShare A etaSub sh = true` on the
       subsets `p ∈ T` it holds, subset `T` is guaranteed to satisfy both the linear relation
       `sh.publicT = A * sh.s1 + sh.s2` and the short-secret bounds `‖sh.s1‖_∞ ≤ etaSub ∧ ‖sh.s2‖_∞ ≤ etaSub`. -/
theorem subset_honest_holder_exists
    {t n : Nat} (ht : 1 ≤ t) (hn : 2 * t - 1 ≤ n)
    {C T : List Nat} (hCLen : C.length ≤ t - 1)
    (hTNodup : T.Nodup) (hTLen : T.length = n - t + 1)
    (A : PolyMat4) (etaSub : Nat) (sh : SubsetShareRecord) :
    (∃ h : Nat, findHonestHolder C T = some h ∧ h ∈ T ∧ h ∉ C) ∧
    ((∀ p : Nat, p ∈ T → p ∉ C → validSubsetShare A etaSub sh = true) →
      sh.publicT = addVec4 (matVecMul4 A sh.s1) sh.s2 ∧
      infNormVec4 sh.s1 ≤ etaSub ∧
      infNormVec4 sh.s2 ≤ etaSub) := by
  have hEx : ∃ h : Nat, findHonestHolder C T = some h ∧ h ∈ T ∧ h ∉ C := by
    cases hOpt : findHonestHolder C T with
    | some h =>
      obtain ⟨hInT, hNotC⟩ := findHonestHolder_some_spec hOpt
      exact ⟨h, rfl, hInT, hNotC⟩
    | none =>
      have hAll := findHonestHolder_none_spec hOpt
      have hLe := natNodup_length_le_of_subset C hTNodup hAll
      omega
  refine ⟨hEx, ?_⟩
  intro hHonestCheck
  rcases hEx with ⟨h, _, hInT, hNotC⟩
  exact (validSubsetShare_eq_true_iff A etaSub sh).mp (hHonestCheck h hInT hNotC)

/-- **`#tooth` (`tooth_dkg_2of2_lacks_honest_holder_coverage`)**:
    Violating $n \ge 2t - 1$ at $(t = 2, n = 2)$ ($2 < 2 \cdot 2 - 1 = 3$) shrinks replicated subsets to
    size $n - t + 1 = 1$, allowing 1 corrupt party `C = [0]` to monopolize subset `T = [0]` with
    zero honest holders (`findHonestHolder C T = none`) and forge an invalid relation $t_T \ne A s_1 + s_2$! -/
theorem tooth_dkg_2of2_lacks_honest_holder_coverage :
    let t := 2
    let n := 2
    let C : List Nat := [0]
    let T : List Nat := [0]
    let badShare : SubsetShareRecord := {
      s1 := fun _ => PolyTree.zero 8
      s2 := fun _ => PolyTree.zero 8
      publicT := fun _ => PolyTree.constUnit 8
    }
    n < 2 * t - 1 ∧
    C.Nodup ∧ C.length ≤ t - 1 ∧
    T.Nodup ∧ T.length = n - t + 1 ∧
    findHonestHolder C T = none ∧
    (∀ p : Nat, p ∈ T → p ∉ C → validSubsetShare idMat4 mldsa44Eta badShare = true) ∧
    badShare.publicT ≠ addVec4 (matVecMul4 idMat4 badShare.s1) badShare.s2 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, rfl, ?_, ?_⟩
  · intro p hpT hpNotC
    rcases List.mem_singleton.mp hpT with rfl
    exact False.elim (hpNotC (.head []))
  · intro hEq
    have h0 := congrFun hEq ⟨0, by decide⟩
    have hMv := congrFun (matVecMul4_idMat4 (fun _ => PolyTree.zero 8)) ⟨0, by decide⟩
    dsimp only [addVec4] at h0
    rw [hMv, polyTree_add_zero] at h0
    revert h0; decide

/-- Constructive intersection witness for any two replicated subsets of size $n - t + 1$ when $n \ge 2t - 1$:
    `findCommonParty T₁ T₂` returns `some p` with `p ∈ T₁ ∧ p ∈ T₂` (certifying degree-2 cross-term coverage!). -/
def findCommonParty (T₁ T₂ : List Nat) : Option Nat :=
  findHonestHolder [] (T₁.filter (fun x => natMemBool x T₂))

theorem replicated_subsets_intersect
    {t n : Nat} (ht : 1 ≤ t) (hn : 2 * t - 1 ≤ n)
    {T₁ T₂ : List Nat}
    (h1Nodup : T₁.Nodup) (h2Nodup : T₂.Nodup)
    (h1Bounds : ∀ x ∈ T₁, x < n) (h2Bounds : ∀ x ∈ T₂, x < n)
    (h1Len : T₁.length = n - t + 1) (h2Len : T₂.length = n - t + 1) :
    ∃ p : Nat, p ∈ T₁ ∧ p ∈ T₂ := by
  cases hCommon : T₁.filter (fun x => natMemBool x T₂) with
  | cons p rest =>
    have hpMem : p ∈ T₁.filter (fun x => natMemBool x T₂) := by rw [hCommon]; exact .head rest
    rw [List.mem_filter] at hpMem
    exact ⟨p, hpMem.1, (natMemBool_eq_true_iff p T₂).mp hpMem.2⟩
  | nil =>
    have hDisj : ∀ a ∈ T₁, ∀ b ∈ T₂, a ≠ b := by
      intro a ha b hb hEq
      subst hEq
      have haFilt : a ∈ T₁.filter (fun x => natMemBool x T₂) :=
        List.mem_filter.mpr ⟨ha, (natMemBool_eq_true_iff a T₂).mpr hb⟩
      rw [hCommon] at haFilt
      cases haFilt
    have hAppNodup : (T₁ ++ T₂).Nodup := List.nodup_append.mpr ⟨h1Nodup, h2Nodup, hDisj⟩
    have hInRange : ∀ z ∈ T₁ ++ T₂, natMemBool z (List.range n) = true := by
      intro z hz
      rw [natMemBool_eq_true_iff, List.mem_range]
      rcases List.mem_append.mp hz with hz1 | hz2
      · exact h1Bounds z hz1
      · exact h2Bounds z hz2
    have hLe := natNodup_length_le_of_subset (List.range n) hAppNodup hInRange
    rw [List.length_append, List.length_range] at hLe
    omega

/-! ### §2.2 Exact 4-Bit Algebraic Nibble Rejection Circuit (`dkg_nibble_rejection_circuit_exact`) -/

/-- Exact 4-bit MPC nibble circuit from `threshold_mldsa.rs:377-392` over `Fq204`,
    returning `(is15, coeff)` where `coeff = 2 - (nib mod 5)` for all `nib < 15`. -/
def dkgNibbleCircuit (b0 b1 b2 b3 : Fq204) : Fq204 × Fq204 :=
  let p01 := Fq204.mul b0 b1
  let p12 := Fq204.mul b1 b2
  let p23 := Fq204.mul b2 b3
  let or12 := Fq204.sub (Fq204.add b1 b2) p12
  let or01 := Fq204.sub (Fq204.add b0 b1) p01
  let atLeast10 := Fq204.mul b3 or12
  let lowPart := Fq204.mul b2 or01
  let is15 := Fq204.mul p01 p23
  let atLeast5 := Fq204.sub (Fq204.add b3 lowPart) (Fq204.mul b3 lowPart)
  let comp :=
    Fq204.add (Fq204.add b0 (Fq204.mul (Fq204.ofNat 2) b1))
              (Fq204.add (Fq204.mul (Fq204.ofNat 4) b2) (Fq204.mul (Fq204.ofNat 8) b3))
  let coeff :=
    Fq204.add (Fq204.sub (Fq204.ofNat 2) comp)
              (Fq204.mul (Fq204.ofNat 5) (Fq204.add atLeast5 atLeast10))
  (is15, coeff)

def nibbleBitsToFq204 (nib : Nat) : Fq204 × Fq204 × Fq204 × Fq204 :=
  (Fq204.ofNat (nib % 2),
   Fq204.ofNat ((nib / 2) % 2),
   Fq204.ofNat ((nib / 4) % 2),
   Fq204.ofNat ((nib / 8) % 2))

def evalNibbleCircuitNat (nib : Nat) : Fq204 × Fq204 :=
  let (b0, b1, b2, b3) := nibbleBitsToFq204 nib
  dkgNibbleCircuit b0 b1 b2 b3

/-- **Exact 4-Bit DKG Nibble Rejection & Uniformity Theorem (`dkg_nibble_rejection_circuit_exact`)**:
    1. Over all 16 4-bit inputs `nib ∈ [0, 16)`, `is15 = 1 ↔ nib = 15` and `is15 = 0 ↔ nib < 15`;
    2. For all 15 accepted nibbles `nib < 15`, `coeff = Fq204.ofInt (2 - (nib % 5))` with
       `centeredAbs coeff ≤ mldsa44Eta` (`= 2`);
    3. Every target coefficient in `{-2, -1, 0, 1, 2}` has **exact multiplicity 3** across `[0, 15)`
       (zero modulo bias), whereas `#tooth` omitting `nib = 15` rejection admits `(evalNibbleCircuitNat 15).2 = -3`
       with `centeredAbs = 3 > mldsa44Eta`, violating the short-key norm bound! -/
theorem dkg_nibble_rejection_circuit_exact :
    (∀ nib : Fin 16,
      ((evalNibbleCircuitNat nib.val).1 = Fq204.one ↔ nib.val = 15) ∧
      ((evalNibbleCircuitNat nib.val).1 = Fq204.zero ↔ nib.val < 15) ∧
      (nib.val < 15 →
        (evalNibbleCircuitNat nib.val).2 = Fq204.ofInt (2 - ((nib.val % 5 : Nat) : Int)) ∧
        Fq204.centeredAbs (evalNibbleCircuitNat nib.val).2 ≤ mldsa44Eta)) ∧
    (∀ k ∈ ([-2, -1, 0, 1, 2] : List Int),
      ((List.range 15).filter (fun nib => decide ((evalNibbleCircuitNat nib).2 = Fq204.ofInt k))).length = 3) ∧
    ((evalNibbleCircuitNat 15).2 = Fq204.ofInt (-3) ∧
     mldsa44Eta < Fq204.centeredAbs (evalNibbleCircuitNat 15).2) := by
  decide

/-! ### §2.3 2-Phase Salted Commitment Anti-Rogue-Key Theorem (`dkg_phase2_commit_blocks_rogue_key`) -/

/-- Canonical fixed-width byte encoding of a $2^d$-coefficient `PolyTree` (`4 * 2^d` bytes). -/
def encodePolyTreeBytes : {d : Nat} → PolyTree d → List UInt8
  | 0, .leaf x => encodeU32BeNat x.val
  | _ + 1, .branch l r => encodePolyTreeBytes l ++ encodePolyTreeBytes r

theorem encodePolyTreeBytes_length : ∀ {d : Nat} (p : PolyTree d),
    (encodePolyTreeBytes p).length = 4 * (2 ^ d)
  | 0, .leaf x => by simp [encodePolyTreeBytes, encodeU32BeNat_length]
  | d + 1, .branch l r => by
    simp only [encodePolyTreeBytes, List.length_append,
      encodePolyTreeBytes_length l, encodePolyTreeBytes_length r, Nat.pow_succ]
    omega

theorem encodePolyTreeBytes_injective : ∀ {d : Nat} {p q : PolyTree d},
    encodePolyTreeBytes p = encodePolyTreeBytes q → p = q
  | 0, .leaf x, .leaf y, hEq => by
    dsimp only [encodePolyTreeBytes] at hEq
    have hxLt : x.val < 2 ^ 32 := Nat.lt_trans x.isLt (by decide)
    have hyLt : y.val < 2 ^ 32 := Nat.lt_trans y.isLt (by decide)
    have hDec := congrArg decodeU32BeNat hEq
    rw [decodeU32BeNat_encodeU32BeNat hxLt, decodeU32BeNat_encodeU32BeNat hyLt] at hDec
    injection hDec with hVal
    exact congrArg PolyTree.leaf (Fq204.ext hVal)
  | d + 1, .branch l1 r1, .branch l2 r2, hEq => by
    have hLen : (encodePolyTreeBytes l1).length = (encodePolyTreeBytes l2).length := by
      rw [encodePolyTreeBytes_length, encodePolyTreeBytes_length]
    obtain ⟨hL, hR⟩ := append_inj_of_eq_len hLen hEq
    rw [encodePolyTreeBytes_injective hL, encodePolyTreeBytes_injective hR]

/-- Fixed 4096-byte canonical serialization of `PolyVec4` (`4 * 1024 = 4096` bytes). -/
def encodePolyVec4Bytes (v : PolyVec4) : List UInt8 :=
  encodePolyTreeBytes (v ⟨0, by decide⟩) ++
  encodePolyTreeBytes (v ⟨1, by decide⟩) ++
  encodePolyTreeBytes (v ⟨2, by decide⟩) ++
  encodePolyTreeBytes (v ⟨3, by decide⟩)

theorem encodePolyVec4Bytes_length (v : PolyVec4) :
    (encodePolyVec4Bytes v).length = 4096 := by
  unfold encodePolyVec4Bytes
  simp only [List.length_append, encodePolyTreeBytes_length]

theorem encodePolyVec4Bytes_injective {u v : PolyVec4}
    (hEq : encodePolyVec4Bytes u = encodePolyVec4Bytes v) : u = v := by
  unfold encodePolyVec4Bytes at hEq
  simp only [List.append_assoc] at hEq
  have hL0 : (encodePolyTreeBytes (u ⟨0, by decide⟩)).length =
      (encodePolyTreeBytes (v ⟨0, by decide⟩)).length := by
    rw [encodePolyTreeBytes_length, encodePolyTreeBytes_length]
  obtain ⟨e0, r0⟩ := append_inj_of_eq_len hL0 hEq
  have hL1 : (encodePolyTreeBytes (u ⟨1, by decide⟩)).length =
      (encodePolyTreeBytes (v ⟨1, by decide⟩)).length := by
    rw [encodePolyTreeBytes_length, encodePolyTreeBytes_length]
  obtain ⟨e1, r1⟩ := append_inj_of_eq_len hL1 r0
  have hL2 : (encodePolyTreeBytes (u ⟨2, by decide⟩)).length =
      (encodePolyTreeBytes (v ⟨2, by decide⟩)).length := by
    rw [encodePolyTreeBytes_length, encodePolyTreeBytes_length]
  obtain ⟨e2, e3⟩ := append_inj_of_eq_len hL2 r1
  have p0 := encodePolyTreeBytes_injective e0
  have p1 := encodePolyTreeBytes_injective e1
  have p2 := encodePolyTreeBytes_injective e2
  have p3 := encodePolyTreeBytes_injective e3
  funext i
  rcases i with ⟨idx, hidx⟩
  have hCases : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 := by omega
  rcases hCases with rfl | rfl | rfl | rfl
  · exact p0
  · exact p1
  · exact p2
  · exact p3

theorem ite_true_of {α : Type} {c : Prop} [Decidable c] (h : c) (t e : α) :
    (if c then t else e) = t := by
  split <;> rename_i hc
  · rfl
  · exact False.elim (hc h)

theorem ite_false_of {α : Type} {c : Prop} [Decidable c] (h : ¬ c) (t e : α) :
    (if c then t else e) = e := by
  split <;> rename_i hc
  · exact False.elim (h hc)
  · rfl

/-- Exact little-endian `u64` frame body `(u64_le(f.len) || f)*` matching
    `qsag_accel::keccak::cshake256_framed_xof` (`keccak.rs:281-284`). -/
def encodeFramesU64LeBody : List (List UInt8) → List UInt8
  | [] => []
  | f :: fs => (encodeNatLeBytes 8 f.length ++ f) ++ encodeFramesU64LeBody fs

/-- Exact little-endian `u64` framed slice list `u64_le(frames.len) || (u64_le(f.len) || f)*`
    matching `qsag_accel::keccak::cshake256_framed_xof` (`keccak.rs:280-284`). -/
def encodeFramesU64Le (frames : List (List UInt8)) : List UInt8 :=
  encodeNatLeBytes 8 frames.length ++ encodeFramesU64LeBody frames

private theorem encodeFramesU64LeBody_injective_of_len :
    ∀ {fs gs : List (List UInt8)},
      fs.length = gs.length →
      (∀ f ∈ fs, f.length < 256 ^ 8) →
      (∀ g ∈ gs, g.length < 256 ^ 8) →
      encodeFramesU64LeBody fs = encodeFramesU64LeBody gs →
      fs = gs
  | [], [], _, _, _, _ => rfl
  | f :: fs, g :: gs, hCnt, hfB, hgB, hEq => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hCnt
    dsimp only [encodeFramesU64LeBody] at hEq
    rw [List.append_assoc, List.append_assoc] at hEq
    have hL8 : (encodeNatLeBytes 8 f.length).length = (encodeNatLeBytes 8 g.length).length := by
      rw [encodeNatLeBytes_length, encodeNatLeBytes_length]
    obtain ⟨hLenBytes, hRest⟩ := append_inj_of_eq_len hL8 hEq
    have hfLt : f.length < 256 ^ 8 := hfB f (.head fs)
    have hgLt : g.length < 256 ^ 8 := hgB g (.head gs)
    have hDec := congrArg decodeNatLeBytes hLenBytes
    rw [decodeNatLeBytes_encodeNatLeBytes 8 f.length hfLt,
        decodeNatLeBytes_encodeNatLeBytes 8 g.length hgLt] at hDec
    obtain ⟨hFG, hTail⟩ := append_inj_of_eq_len hDec hRest
    have hTailEq := encodeFramesU64LeBody_injective_of_len hCnt
      (fun x hx => hfB x (.tail f hx)) (fun y hy => hgB y (.tail g hy)) hTail
    rw [hFG, hTailEq]

theorem encodeFramesU64Le_injective {fs gs : List (List UInt8)}
    (hCntF : fs.length < 256 ^ 8) (hCntG : gs.length < 256 ^ 8)
    (hfB : ∀ f ∈ fs, f.length < 256 ^ 8)
    (hgB : ∀ g ∈ gs, g.length < 256 ^ 8)
    (hEq : encodeFramesU64Le fs = encodeFramesU64Le gs) : fs = gs := by
  unfold encodeFramesU64Le at hEq
  have hL8 : (encodeNatLeBytes 8 fs.length).length = (encodeNatLeBytes 8 gs.length).length := by
    rw [encodeNatLeBytes_length, encodeNatLeBytes_length]
  obtain ⟨hCntBytes, hBodyEq⟩ := append_inj_of_eq_len hL8 hEq
  have hCntEq : fs.length = gs.length := by
    have hd := congrArg decodeNatLeBytes hCntBytes
    rwa [decodeNatLeBytes_encodeNatLeBytes 8 fs.length hCntF,
         decodeNatLeBytes_encodeNatLeBytes 8 gs.length hCntG] at hd
  exact encodeFramesU64LeBody_injective_of_len hCntEq hfB hgB hBodyEq

/-- Exact SP 800-185 + `u64_le` sponge preimage absorbed by `cshake256_framed_xof` (`keccak.rs:277-286`). -/
def cshake256FramedPreimage (customization : List UInt8) (frames : List (List UInt8)) : List UInt8 :=
  if customization = [] then
    encodeFramesU64Le frames
  else
    customizationPrefix customization ++ encodeFramesU64Le frames

/-- Concrete 32-byte `cshake256_framed_32` matching `qsag_accel::keccak::cshake256_framed_32` (`keccak.rs:291-295`). -/
def cshake256FramedBytes (customization : List UInt8) (frames : List (List UInt8)) : List UInt8 :=
  cshake256Bytes customization (encodeFramesU64Le frames)

theorem cshake256FramedBytes_eq_sponge (customization : List UInt8) (frames : List (List UInt8)) :
    cshake256FramedBytes customization frames =
      squeezeXofAux 32 (absorbPadded (padForRate
        (cshake256FramedPreimage customization frames)
        (if customization = [] then 0x1f else 0x04))) := by
  unfold cshake256FramedBytes cshake256FramedPreimage cshake256Bytes cshake256Xof
  rfl

@[simp] theorem cshake256FramedBytes_length (customization : List UInt8) (frames : List (List UInt8)) :
    (cshake256FramedBytes customization frames).length = 32 := by
  unfold cshake256FramedBytes
  exact cshake256Bytes_length customization (encodeFramesU64Le frames)

theorem cshake256FramedPreimage_frames_injective {customization : List UInt8}
    {fs gs : List (List UInt8)}
    (hCntF : fs.length < 256 ^ 8) (hCntG : gs.length < 256 ^ 8)
    (hfB : ∀ f ∈ fs, f.length < 256 ^ 8)
    (hgB : ∀ g ∈ gs, g.length < 256 ^ 8)
    (hEq : cshake256FramedPreimage customization fs = cshake256FramedPreimage customization gs) :
    fs = gs := by
  unfold cshake256FramedPreimage at hEq
  if hEmpty : customization = [] then
    rw [ite_true_of hEmpty, ite_true_of hEmpty] at hEq
    exact encodeFramesU64Le_injective hCntF hCntG hfB hgB hEq
  else
    rw [ite_false_of hEmpty, ite_false_of hEmpty] at hEq
    obtain ⟨_, hFrEq⟩ := append_inj_of_eq_len rfl hEq
    exact encodeFramesU64Le_injective hCntF hCntG hfB hgB hFrEq

/-- Little-endian `u32` (`v.to_le_bytes`) polynomial serialization matching `threshold_mldsa.rs:615-618`. -/
def encodePolyTreeBytesLe : {d : Nat} → PolyTree d → List UInt8
  | 0, .leaf x => encodeNatLeBytes 4 x.val
  | _ + 1, .branch l r => encodePolyTreeBytesLe l ++ encodePolyTreeBytesLe r

theorem encodePolyTreeBytesLe_length : ∀ {d : Nat} (p : PolyTree d),
    (encodePolyTreeBytesLe p).length = 4 * (2 ^ d)
  | 0, .leaf x => by simp [encodePolyTreeBytesLe, encodeNatLeBytes_length]
  | d + 1, .branch l r => by
    simp only [encodePolyTreeBytesLe, List.length_append,
      encodePolyTreeBytesLe_length l, encodePolyTreeBytesLe_length r, Nat.pow_succ]
    omega

theorem encodePolyTreeBytesLe_injective : ∀ {d : Nat} {p q : PolyTree d},
    encodePolyTreeBytesLe p = encodePolyTreeBytesLe q → p = q
  | 0, .leaf x, .leaf y, hEq => by
    dsimp only [encodePolyTreeBytesLe] at hEq
    have hxLt : x.val < 256 ^ 4 := Nat.lt_trans x.isLt (by decide)
    have hyLt : y.val < 256 ^ 4 := Nat.lt_trans y.isLt (by decide)
    have hDec := congrArg decodeNatLeBytes hEq
    rw [decodeNatLeBytes_encodeNatLeBytes 4 x.val hxLt,
        decodeNatLeBytes_encodeNatLeBytes 4 y.val hyLt] at hDec
    exact congrArg PolyTree.leaf (Fq204.ext hDec)
  | _ + 1, .branch l1 r1, .branch l2 r2, hEq => by
    have hLen : (encodePolyTreeBytesLe l1).length = (encodePolyTreeBytesLe l2).length := by
      rw [encodePolyTreeBytesLe_length, encodePolyTreeBytesLe_length]
    obtain ⟨hL, hR⟩ := append_inj_of_eq_len hLen hEq
    rw [encodePolyTreeBytesLe_injective hL, encodePolyTreeBytesLe_injective hR]

/-- Fixed 4096-byte little-endian canonical serialization of `PolyVec4` (`threshold_mldsa.rs:615-618`). -/
def encodePolyVec4BytesLe (v : PolyVec4) : List UInt8 :=
  encodePolyTreeBytesLe (v ⟨0, by decide⟩) ++
  encodePolyTreeBytesLe (v ⟨1, by decide⟩) ++
  encodePolyTreeBytesLe (v ⟨2, by decide⟩) ++
  encodePolyTreeBytesLe (v ⟨3, by decide⟩)

theorem encodePolyVec4BytesLe_length (v : PolyVec4) :
    (encodePolyVec4BytesLe v).length = 4096 := by
  unfold encodePolyVec4BytesLe
  simp only [List.length_append, encodePolyTreeBytesLe_length]

