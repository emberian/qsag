module
/-
# Qsag.Protocol.Threshold.BaggyAndRss256Security

Constructive (`0 Classical.choice`) formalization of 256-bit `WOTS+C` extraction, active-malicious
`Rss256` field/transcript/barrier security, and `Baggy` `Waistband` canopy, MAC-enrolled cache,
crash-resilient durable release, and an upper-hypertree reduction with an explicit bottom-layer residual:

1. **256-Bit `WOTS+C` (`w = 4, chains = 128, target_sum = 192`)**:
   - MSB-first dibit packing, strict constant-sum incomparability (`wotsC256_strict_incomparability`),
     completeness, 1-use EUF-CMA witness extraction (`wotsC256_one_use_euf_cma_extract`), and
     unconstrained-sum forgery counterexample (`tooth_wotsc_without_target_sum_forges`).
2. RSS256 field isomorphism, polynomial root bounds and recorded-wave release guards.
   `rss256_packed_batch_roots` bounds fixed nonzero gate-error polynomials.
3. Verified Waistband signing with explicit `WaistbandMatchesKey` assumptions, and
   durable single-codeword reservations across multiple sessions.
4. Crash-visible reservation/write/sync/release transitions, plus adaptive Rust two-pass
   `product_proof` (`ROUND1` + `ROUND2`) Frobenius-basis tensor folding & masked cross-product
   barrier soundness (`Rss256ProductProof.rss256_two_pass_product_proof_sound` and
   `rss256_inline_wave_two_pass_product_proof_sound`). The upper reduction may return
   `bottomLayerReachedGenuineRoot`; closing that case requires the bottom WOTS/FORS/index
   derivation reduction and primitive game bounds.
-/

public import Qsag.Tactic.Prelude
public import Qsag.Math.Goldilocks
public import Qsag.Math.Gf2Pow128
public import Qsag.Protocol.Aggregation.UcGames
public import Qsag.Spec.Refines
public import Qsag.Protocol.Threshold.MaliciousSecurity
public import Qsag.Protocol.Threshold.RssSlhFullSecurity
public import Qsag.Protocol.Threshold.Rss256TwoPassProductProof

import Lean

import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

attribute [-instance] UInt8.instLawfulEqOrd UInt8.instLawfulOrderOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd BitVec.instTransOrd
set_option autoImplicit false
set_option maxRecDepth 8192

private theorem ite_pos {α : Sort _} {c : Prop} [Decidable c] (hc : c) {a b : α} :
    (if c then a else b) = a := by
  simp only [hc, ↓reduceIte]

private theorem ite_neg {α : Sort _} {c : Prop} [Decidable c] (hnc : ¬ c) {a b : α} :
    (if c then a else b) = b := by
  simp only [hnc, ↓reduceIte]

private theorem dite_pos {α : Sort _} {c : Prop} [Decidable c] (hc : c) {a : c → α} {b : ¬ c → α} :
    (if h : c then a h else b h) = a hc := by
  simp only [hc, ↓reduceDIte]

private theorem dite_neg {α : Sort _} {c : Prop} [Decidable c] (hnc : ¬ c) {a : c → α} {b : ¬ c → α} :
    (if h : c then a h else b h) = b hnc := by
  simp only [hnc, ↓reduceDIte]

/-! ## 1. 256-Bit `WOTS+C` (`w = 4, chains = 128, target_sum = 192, zero_digits = 0`) -/

def wotsC256W : Nat := 4
def wotsC256Steps : Nat := 3
def wotsC256Chains : Nat := 128
def wotsC256ZeroDigits : Nat := 0
def wotsC256TargetSum : Nat := 192

/-- Reverse dibits within each byte; byte zero occupies the low eight bits. -/
def wotsCDibitIndex (i : Fin 128) : Fin 128 :=
  ⟨4 * (i.val / 4) + (3 - i.val % 4), by have := i.isLt; omega⟩

theorem wotsCDibitIndex_involutive (i : Fin 128) :
    wotsCDibitIndex (wotsCDibitIndex i) = i := by
  apply Fin.ext
  simp only [wotsCDibitIndex]
  omega

/-- Production MSB-first byte order: shifts `6, 4, 2, 0` within each byte. -/
@[expose] def wotsC256DigitOfDigest (digest : BitVec 256) (i : Fin 128) : Fin 4 :=
  (digest.extractLsb' (2 * (wotsCDibitIndex i).val) 2).toFin

/-- Pack `n` base-4 digits into a `BitVec (2 * n)` (`0 Classical.choice`). -/
def packDigitsAux : (n : Nat) → (Fin n → Fin 4) → BitVec (2 * n)
  | 0, _ => 0#0
  | n + 1, f =>
    let lo : BitVec 2 := BitVec.ofFin (f ⟨0, Nat.zero_lt_succ n⟩)
    let hi : BitVec (2 * n) := packDigitsAux n (fun j => f ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
    (hi ++ lo).cast (by omega)

/-- Pack 128 base-4 digits into a 256-bit digest. -/
def packDigits256 (f : Fin 128 → Fin 4) : BitVec 256 :=
  packDigitsAux 128 (fun i => f (wotsCDibitIndex i))

private theorem packDigitsAux_extract_bv : ∀ (n : Nat) (f : Fin n → Fin 4) (i : Fin n),
    (packDigitsAux n f).extractLsb' (2 * i.val) 2 = BitVec.ofFin (f i)
  | 0, _, i => Fin.elim0 i
  | n + 1, f, ⟨0, _⟩ => by
    dsimp only [packDigitsAux]
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    simp [BitVec.getLsbD_append, hk]
  | n + 1, f, ⟨j + 1, hj⟩ => by
    dsimp only [packDigitsAux]
    have hShift :
        ((packDigitsAux n (fun u => f ⟨u.val + 1, Nat.succ_lt_succ u.isLt⟩) ++
          BitVec.ofFin (f ⟨0, Nat.zero_lt_succ n⟩)).cast (by omega : 2 * n + 2 = 2 * (n + 1))).extractLsb'
          (2 * (j + 1)) 2 =
        (packDigitsAux n (fun u => f ⟨u.val + 1, Nat.succ_lt_succ u.isLt⟩)).extractLsb' (2 * j) 2 := by
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      have hNotLt : ¬ (2 * (j + 1) + k < 2) := by omega
      have hSub : 2 * (j + 1) + k - 2 = 2 * j + k := by omega
      simp [BitVec.getLsbD_append, hk, hNotLt, hSub]
    rw [hShift]
    exact packDigitsAux_extract_bv n (fun u => f ⟨u.val + 1, Nat.succ_lt_succ u.isLt⟩) ⟨j, Nat.lt_of_succ_lt_succ hj⟩

private theorem packDigitsAux_extract (n : Nat) (f : Fin n → Fin 4) (i : Fin n) :
    ((packDigitsAux n f).extractLsb' (2 * i.val) 2).toFin = f i := by
  rw [packDigitsAux_extract_bv]

theorem packDigits256_extract (f : Fin 128 → Fin 4) (i : Fin 128) :
    wotsC256DigitOfDigest (packDigits256 f) i = f i :=
by
  unfold wotsC256DigitOfDigest packDigits256
  rw [packDigitsAux_extract, wotsCDibitIndex_involutive]

attribute [irreducible] packDigits256

/-- Full 256-bit digest coverage (`zero_digits = 0`): distinct 256-bit digests have distinct 128-digit base-4 vectors. -/
theorem wotsC256DigitOfDigest_injective {h₁ h₂ : BitVec 256}
    (hEq : ∀ i : Fin 128, wotsC256DigitOfDigest h₁ i = wotsC256DigitOfDigest h₂ i) :
    h₁ = h₂ := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  let idx : Fin 128 := ⟨b / 2, by omega⟩
  have hMod : b % 2 < 2 := Nat.mod_lt b (by decide)
  have hDecomp : 2 * (b / 2) + b % 2 = b := Nat.div_add_mod b 2
  have hFin := hEq (wotsCDibitIndex idx)
  simp only [wotsC256DigitOfDigest, wotsCDibitIndex_involutive] at hFin
  have hBv : h₁.extractLsb' (2 * idx.val) 2 = h₂.extractLsb' (2 * idx.val) 2 :=
    BitVec.eq_of_toFin_eq hFin
  have hBit := congrArg (fun v : BitVec 2 => v.getLsbD (b % 2)) hBv
  simpa only [idx, BitVec.getLsbD_extractLsb', hMod, decide_true, Bool.true_and, hDecomp] using hBit

/-- Public vector name for the 128 production-order dibits. -/
def wotsCDibits128 (digest : BitVec 256) : Fin 128 → Fin 4 :=
  wotsC256DigitOfDigest digest

theorem wotsCDibits128_injective {a b : BitVec 256}
    (h : wotsCDibits128 a = wotsCDibits128 b) : a = b :=
  wotsC256DigitOfDigest_injective (congrFun h)

/-- Bit-vector form of Rust's `hash[i / 4] >> (6 - 2 * (i % 4)) & 3`. -/
theorem wotsCDibits128_byte_shift (digest : BitVec 256) (i : Fin 128) :
    wotsCDibits128 digest i =
      (digest.extractLsb' (8 * (i.val / 4) + (6 - 2 * (i.val % 4))) 2).toFin := by
  unfold wotsCDibits128 wotsC256DigitOfDigest wotsCDibitIndex
  have h : 2 * (4 * (i.val / 4) + (3 - i.val % 4)) =
      8 * (i.val / 4) + (6 - 2 * (i.val % 4)) := by omega
  rw [h]

/-- The first byte `0b11100100` decodes as `[3, 2, 1, 0]`, as in Rust. -/
theorem wotsCDibits128_msb_sanity :
    [wotsC256DigitOfDigest 0xE4#256 ⟨0, by decide⟩,
     wotsC256DigitOfDigest 0xE4#256 ⟨1, by decide⟩,
     wotsC256DigitOfDigest 0xE4#256 ⟨2, by decide⟩,
     wotsC256DigitOfDigest 0xE4#256 ⟨3, by decide⟩].map Fin.val = [3, 2, 1, 0] := by
  decide

/-- Valid 256-bit `WOTS+C` codeword (`w = 4, v = 128, S = 192`). -/
structure WotsC256Digits where
  digits : Fin 128 → Fin 4
  sum_eq : qsum 128 (fun i => (digits i).val) = 192

theorem WotsC256Digits.ext {d₁ d₂ : WotsC256Digits}
    (h : ∀ i : Fin 128, d₁.digits i = d₂.digits i) : d₁ = d₂ := by
  cases d₁ with
  | mk f₁ s₁ =>
    cases d₂ with
    | mk f₂ s₂ =>
      have hf : f₁ = f₂ := funext h
      subst hf
      rfl

def finFuncEqAux : (n : Nat) → (f g : Fin n → Fin 4) →
    PSum { i : Fin n // f i ≠ g i } (∀ i : Fin n, f i = g i)
  | 0, _, _ => .inr (fun i => Fin.elim0 i)
  | n + 1, f, g =>
    let i0 : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
    if h0 : f i0 = g i0 then
      match finFuncEqAux n (fun j => f ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
                           (fun j => g ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) with
      | .inl ⟨j, hj⟩ => .inl ⟨⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩, hj⟩
      | .inr hRest => .inr fun i =>
        match i with
        | ⟨0, _⟩ => h0
        | ⟨k + 1, hk⟩ => hRest ⟨k, Nat.lt_of_succ_lt_succ hk⟩
    else
      .inl ⟨i0, h0⟩

instance constructiveWotsC256DigitsDecEq : DecidableEq WotsC256Digits :=
  fun d₁ d₂ =>
    match finFuncEqAux 128 d₁.digits d₂.digits with
    | .inl ⟨i, hNe⟩ => .isFalse (fun hEq => hNe (congrArg (fun x => x.digits i) hEq))
    | .inr hAll => .isTrue (WotsC256Digits.ext hAll)

/-- Sum of 128 base-4 digits (`0 Classical.choice`). Sealed `[irreducible]` after `wotsC256DigitSum_eq`
    so `whnf` never unfolds the 128-term `qsum` during elaboration or kernel `Decidable` synthesis! -/
def wotsC256DigitSum (f : Fin 128 → Fin 4) : Nat :=
  qsum 128 (fun i => (f i).val)

theorem wotsC256DigitSum_eq (f : Fin 128 → Fin 4) :
    wotsC256DigitSum f = qsum 128 (fun i => (f i).val) := by
  unfold wotsC256DigitSum
  exact Eq.refl _

attribute [irreducible] wotsC256DigitSum

/-- Decode a 256-bit digest into `WotsC256Digits` iff its 128 base-4 digits sum to `192`. -/
def wotsC256DecodeValidDigest (digest : BitVec 256) : Option WotsC256Digits :=
  let f := wotsC256DigitOfDigest digest
  if h : wotsC256DigitSum f = 192 then
    some { digits := f, sum_eq := (wotsC256DigitSum_eq f).symm.trans h }
  else
    none

theorem wotsC256DecodeValidDigest_some_digits {dig : BitVec 256} {d : WotsC256Digits}
    (h : wotsC256DecodeValidDigest dig = some d) :
    d.digits = wotsC256DigitOfDigest dig := by
  unfold wotsC256DecodeValidDigest at h
  dsimp only at h
  if hSum : wotsC256DigitSum (wotsC256DigitOfDigest dig) = 192 then
    rw [dite_pos hSum] at h
    have hdEq := Option.some.inj h
    exact (congrArg WotsC256Digits.digits hdEq).symm
  else
    rw [dite_neg hSum] at h
    cases h

theorem wotsC256DecodeValidDigest_of_sum_ne {dig : BitVec 256}
    (hNe : qsum 128 (fun i => (wotsC256DigitOfDigest dig i).val) ≠ 192) :
    wotsC256DecodeValidDigest dig = none := by
  unfold wotsC256DecodeValidDigest
  dsimp only
  have hNe' : wotsC256DigitSum (wotsC256DigitOfDigest dig) ≠ 192 := by
    rw [wotsC256DigitSum_eq]
    exact hNe
  exact dite_neg hNe'

theorem wotsC256DecodeValidDigest_pack (d : WotsC256Digits) :
    wotsC256DecodeValidDigest (packDigits256 d.digits) = some d := by
  unfold wotsC256DecodeValidDigest
  dsimp only
  have hFnEq : wotsC256DigitOfDigest (packDigits256 d.digits) = d.digits :=
    funext (packDigits256_extract d.digits)
  have hSum : wotsC256DigitSum (wotsC256DigitOfDigest (packDigits256 d.digits)) = 192 := by
    rw [hFnEq, wotsC256DigitSum_eq]
    exact d.sum_eq
  rw [dite_pos hSum]
  apply congrArg some
  exact WotsC256Digits.ext (packDigits256_extract d.digits)

attribute [irreducible] wotsC256DecodeValidDigest

/-- Purely computational linear search for the first coordinate `i` where `g i < f i` (`0 Classical.choice`). -/
def findStrictDropAux : (n : Nat) → (Fin n → Nat) → (Fin n → Nat) → Option (Fin n)
  | 0, _, _ => none
  | n + 1, f, g =>
    let i0 : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
    if g i0 < f i0 then
      some i0
    else
      match findStrictDropAux n (fun j => f ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
                                (fun j => g ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) with
      | some j => some ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
      | none => none

private theorem findStrictDropAux_some_lt :
    ∀ (n : Nat) (f g : Fin n → Nat) (i : Fin n),
      findStrictDropAux n f g = some i → g i < f i
  | 0, _, _, i, _ => Fin.elim0 i
  | n + 1, f, g, i, hSome => by
    unfold findStrictDropAux at hSome
    dsimp only at hSome
    split at hSome
    · next h0 =>
      injection hSome with hEq
      subst hEq
      exact h0
    · cases hRec : findStrictDropAux n (fun j => f ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
                                       (fun j => g ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) with
      | none =>
        rw [hRec] at hSome
        cases hSome
      | some j =>
        rw [hRec] at hSome
        injection hSome with hEq
        subst hEq
        exact findStrictDropAux_some_lt n _ _ j hRec

private theorem findStrictDropAux_none_le :
    ∀ (n : Nat) (f g : Fin n → Nat),
      findStrictDropAux n f g = none → ∀ i : Fin n, f i ≤ g i
  | 0, _, _, _, i => Fin.elim0 i
  | n + 1, f, g, hNone, i => by
    unfold findStrictDropAux at hNone
    dsimp only at hNone
    split at hNone
    · cases hNone
    · next h0 =>
      have hRecNone :
          findStrictDropAux n (fun j => f ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
                              (fun j => g ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) = none := by
        cases hRec : findStrictDropAux n (fun j => f ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
                                         (fun j => g ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) with
        | none => rfl
        | some j =>
          rw [hRec] at hNone
          cases hNone
      match i with
      | ⟨0, _⟩ => exact Nat.le_of_not_lt h0
      | ⟨k + 1, hk⟩ =>
        exact findStrictDropAux_none_le n _ _ hRecNone ⟨k, Nat.lt_of_succ_lt_succ hk⟩

private theorem add_eq_of_le_parts {a b c d : Nat}
    (hab : a ≤ b) (hcd : c ≤ d) (hSum : a + c = b + d) :
    a = b ∧ c = d := by
  have hb : b = a + (b - a) := (Nat.add_sub_of_le hab).symm
  have hd : d = c + (d - c) := (Nat.add_sub_of_le hcd).symm
  have hCalc : (a + c) + 0 = (a + c) + ((b - a) + (d - c)) := by
    calc
      (a + c) + 0 = a + c := Nat.add_zero (a + c)
      _ = b + d := hSum
      _ = (a + (b - a)) + (c + (d - c)) := by rw [← hb, ← hd]
      _ = (a + c) + ((b - a) + (d - c)) := by
        rw [Nat.add_assoc a (b - a) (c + (d - c)),
            ← Nat.add_assoc (b - a) c (d - c),
            Nat.add_comm (b - a) c,
            Nat.add_assoc c (b - a) (d - c),
            ← Nat.add_assoc a c ((b - a) + (d - c))]
  have hDiffZero : (b - a) + (d - c) = 0 := (Nat.add_left_cancel hCalc).symm
  have hba0 : b - a = 0 := Nat.eq_zero_of_add_eq_zero_right hDiffZero
  have hdc0 : d - c = 0 := Nat.eq_zero_of_add_eq_zero_left hDiffZero
  rw [hba0, Nat.add_zero] at hb
  rw [hdc0, Nat.add_zero] at hd
  exact ⟨hb.symm, hd.symm⟩

private theorem qsum_eq_of_le_pointwise_eq :
    ∀ (n : Nat) (f g : Fin n → Nat),
      (∀ i : Fin n, f i ≤ g i) →
      qsum n f = qsum n g →
      ∀ i : Fin n, f i = g i
  | 0, _, _, _, _, i => Fin.elim0 i
  | n + 1, f, g, hLe, hSum, i => by
    simp only [qsum_succ] at hSum
    let i0 : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
    let f' : Fin n → Nat := fun j => f ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
    let g' : Fin n → Nat := fun j => g ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
    have hLe0 : f i0 ≤ g i0 := hLe i0
    have hLeRest : qsum n f' ≤ qsum n g' :=
      qsum_le_qsum (fun j => hLe ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
    obtain ⟨hEq0, hEqRest⟩ := add_eq_of_le_parts hLe0 hLeRest hSum
    match i with
    | ⟨0, _⟩ => exact hEq0
    | ⟨k + 1, hk⟩ =>
      exact qsum_eq_of_le_pointwise_eq n f' g'
        (fun j => hLe ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) hEqRest ⟨k, Nat.lt_of_succ_lt_succ hk⟩

/-- **Constructive 256-Bit `WOTS+C` Strict-Drop Index Extractor (`extractStrictDropIdx`)**:
    For any two distinct constant-sum `WOTS+C` codewords `d ≠ d'` (`sum = 192`), constructively
    computes (`0 Classical.choice`, `Type`-valued) a chain index `i : Fin 128` with `d' i < d i`. -/
def extractStrictDropIdx (d d' : WotsC256Digits) (hNe : d ≠ d') :
    { i : Fin 128 // (d'.digits i).val < (d.digits i).val } :=
  match hSearch : findStrictDropAux 128 (fun i => (d.digits i).val) (fun i => (d'.digits i).val) with
  | some i => ⟨i, findStrictDropAux_some_lt 128 _ _ i hSearch⟩
  | none =>
    False.elim <| by
      have hLe := findStrictDropAux_none_le 128 _ _ hSearch
      have hEqSum : qsum 128 (fun i => (d.digits i).val) = qsum 128 (fun i => (d'.digits i).val) :=
        d.sum_eq.trans d'.sum_eq.symm
      have hPt := qsum_eq_of_le_pointwise_eq 128 _ _ hLe hEqSum
      exact hNe (WotsC256Digits.ext (fun i => Fin.ext (hPt i)))

/-- **Bidirectional Strict Incomparability of 256-Bit `WOTS+C` (`wotsC256_strict_incomparability`)**:
    Any two distinct `sum = 192` codewords have constructively extracted indices `i, j : Fin 128`
    with `d' i < d i` AND `d j < d' j`; neither dominates the other. -/
theorem wotsC256_strict_incomparability (d d' : WotsC256Digits) (hNe : d ≠ d') :
    let i := (extractStrictDropIdx d d' hNe).1
    let j := (extractStrictDropIdx d' d hNe.symm).1
    (d'.digits i).val < (d.digits i).val ∧
    (d.digits j).val < (d'.digits j).val ∧
    ¬ (∀ k : Fin 128, (d.digits k).val ≤ (d'.digits k).val) ∧
    ¬ (∀ k : Fin 128, (d'.digits k).val ≤ (d.digits k).val) := by
  let w1 := extractStrictDropIdx d d' hNe
  let w2 := extractStrictDropIdx d' d hNe.symm
  refine ⟨w1.2, w2.2, ?_, ?_⟩
  · intro hAll
    exact Nat.not_lt_of_ge (hAll w1.1) w1.2
  · intro hAll
    exact Nat.not_lt_of_ge (hAll w2.1) w2.2

/-- Address of a `WOTS+C` leaf inside a hypertree `(layer, tree, keyPair)`. -/
structure WotsLeafAdrs where
  layer : UInt32
  tree : UInt64
  keyPair : UInt32
  deriving DecidableEq, Repr

/-- Tweakable 256-bit hash suite for `WOTS+C` (`w = 4, v = 128, S = 192`). -/
structure WotsC256HashSuite where
  prf : BitVec 256 → BitVec 256 → WotsLeafAdrs → Fin 128 → BitVec 256
  thF : BitVec 256 → WotsLeafAdrs → Fin 128 → Fin 3 → BitVec 256 → BitVec 256
  thTl : BitVec 256 → WotsLeafAdrs → (Fin 128 → BitVec 256) → BitVec 256
  thDigest : BitVec 256 → WotsLeafAdrs → BitVec 256 → UInt32 → BitVec 256

/-- Honest chain position `pos ∈ {0, 1, 2, 3}` from base secret `x0`. -/
def wotsC256PosFrom0 (suite : WotsC256HashSuite) (pkSeed : BitVec 256)
    (adrs : WotsLeafAdrs) (chain : Fin 128) (x0 : BitVec 256) : Nat → BitVec 256
  | 0 => x0
  | 1 => suite.thF pkSeed adrs chain ⟨0, by decide⟩ x0
  | 2 => suite.thF pkSeed adrs chain ⟨1, by decide⟩ (suite.thF pkSeed adrs chain ⟨0, by decide⟩ x0)
  | _ =>
    suite.thF pkSeed adrs chain ⟨2, by decide⟩
      (suite.thF pkSeed adrs chain ⟨1, by decide⟩ (suite.thF pkSeed adrs chain ⟨0, by decide⟩ x0))

/-- Advance a signature chain value starting at digit `start : Fin 4` up to target position `target : Nat` (`start ≤ target ≤ 3`). -/
def wotsC256AdvanceTo (suite : WotsC256HashSuite) (pkSeed : BitVec 256)
    (adrs : WotsLeafAdrs) (chain : Fin 128) (start : Fin 4) (node : BitVec 256) (target : Nat) : BitVec 256 :=
  match start with
  | ⟨0, _⟩ => wotsC256PosFrom0 suite pkSeed adrs chain node target
  | ⟨1, _⟩ =>
    match target with
    | 0 | 1 => node
    | 2 => suite.thF pkSeed adrs chain ⟨1, by decide⟩ node
    | _ => suite.thF pkSeed adrs chain ⟨2, by decide⟩ (suite.thF pkSeed adrs chain ⟨1, by decide⟩ node)
  | ⟨2, _⟩ =>
    match target with
    | 0 | 1 | 2 => node
    | _ => suite.thF pkSeed adrs chain ⟨2, by decide⟩ node
  | ⟨3, _⟩ => node

/-- Complete a chain from digit `d : Fin 4` to its public endpoint at step `3`. -/
def wotsC256CompleteTo3 (suite : WotsC256HashSuite) (pkSeed : BitVec 256)
    (adrs : WotsLeafAdrs) (chain : Fin 128) (d : Fin 4) (sigNode : BitVec 256) : BitVec 256 :=
  wotsC256AdvanceTo suite pkSeed adrs chain d sigNode 3

private theorem wotsC256CompleteTo3_honest_eq (suite : WotsC256HashSuite)
    (pkSeed : BitVec 256) (adrs : WotsLeafAdrs) (chain : Fin 128) (x0 : BitVec 256) (d : Fin 4) :
    wotsC256CompleteTo3 suite pkSeed adrs chain d (wotsC256PosFrom0 suite pkSeed adrs chain x0 d.val) =
      wotsC256PosFrom0 suite pkSeed adrs chain x0 3 := by
  match d with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl

private theorem wotsC256AdvanceTo_step (suite : WotsC256HashSuite)
    (pkSeed : BitVec 256) (adrs : WotsLeafAdrs) (chain : Fin 128)
    (start : Fin 4) (node : BitVec 256) (step : Fin 3)
    (hStartLe : start.val ≤ step.val) :
    suite.thF pkSeed adrs chain step (wotsC256AdvanceTo suite pkSeed adrs chain start node step.val) =
      wotsC256AdvanceTo suite pkSeed adrs chain start node (step.val + 1) := by
  match start, step with
  | ⟨0, _⟩, ⟨0, _⟩ => rfl
  | ⟨0, _⟩, ⟨1, _⟩ => rfl
  | ⟨0, _⟩, ⟨2, _⟩ => rfl
  | ⟨1, _⟩, ⟨0, _⟩ => cases hStartLe
  | ⟨1, _⟩, ⟨1, _⟩ => rfl
  | ⟨1, _⟩, ⟨2, _⟩ => rfl
  | ⟨2, _⟩, ⟨0, _⟩ => cases hStartLe
  | ⟨2, _⟩, ⟨1, _⟩ => cases Nat.le_of_succ_le_succ hStartLe
  | ⟨2, _⟩, ⟨2, _⟩ => rfl
  | ⟨3, _⟩, ⟨0, _⟩ => cases hStartLe
  | ⟨3, _⟩, ⟨1, _⟩ => cases Nat.le_of_succ_le_succ hStartLe
  | ⟨3, _⟩, ⟨2, _⟩ => cases Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hStartLe)

private theorem wotsC256PosFrom0_step (suite : WotsC256HashSuite)
    (pkSeed : BitVec 256) (adrs : WotsLeafAdrs) (chain : Fin 128) (x0 : BitVec 256) (step : Fin 3) :
    suite.thF pkSeed adrs chain step (wotsC256PosFrom0 suite pkSeed adrs chain x0 step.val) =
      wotsC256PosFrom0 suite pkSeed adrs chain x0 (step.val + 1) := by
  match step with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl

/-- Honest leaf public key `wots_c_leaf`. -/
def wotsC256PkLeaf (suite : WotsC256HashSuite) (pkSeed skSeed : BitVec 256) (adrs : WotsLeafAdrs) : BitVec 256 :=
  suite.thTl pkSeed adrs (fun chain =>
    wotsC256PosFrom0 suite pkSeed adrs chain (suite.prf pkSeed skSeed adrs chain) 3)

/-- Sign `(msg, ctr)` when `thDigest pkSeed adrs msg ctr` satisfies the `sum = 192` constraint. -/
@[expose] def wotsC256Sign (suite : WotsC256HashSuite) (pkSeed skSeed : BitVec 256)
    (adrs : WotsLeafAdrs) (msg : BitVec 256) (ctr : UInt32) : Option (Fin 128 → BitVec 256) :=
  match wotsC256DecodeValidDigest (suite.thDigest pkSeed adrs msg ctr) with
  | none => none
  | some d =>
    some (fun chain =>
      wotsC256PosFrom0 suite pkSeed adrs chain (suite.prf pkSeed skSeed adrs chain) (d.digits chain).val)

/-- Verify a 256-bit `WOTS+C` signature `(ctr, sigChains)` on `msg` against `pkLeaf`. -/
@[expose] def wotsC256Verify (suite : WotsC256HashSuite) (pkSeed : BitVec 256)
    (adrs : WotsLeafAdrs) (pkLeaf : BitVec 256)
    (msg : BitVec 256) (ctr : UInt32) (sigChains : Fin 128 → BitVec 256) : Bool :=
  match wotsC256DecodeValidDigest (suite.thDigest pkSeed adrs msg ctr) with
  | none => false
  | some d =>
    let endpoints : Fin 128 → BitVec 256 := fun chain =>
      wotsC256CompleteTo3 suite pkSeed adrs chain (d.digits chain) (sigChains chain)
    suite.thTl pkSeed adrs endpoints == pkLeaf

theorem wotsC256_sign_verify_complete (suite : WotsC256HashSuite)
    (pkSeed skSeed : BitVec 256) (adrs : WotsLeafAdrs)
    (msg : BitVec 256) (ctr : UInt32) (sigChains : Fin 128 → BitVec 256)
    (hSign : wotsC256Sign suite pkSeed skSeed adrs msg ctr = some sigChains) :
    wotsC256Verify suite pkSeed adrs (wotsC256PkLeaf suite pkSeed skSeed adrs) msg ctr sigChains = true := by
  unfold wotsC256Sign at hSign
  unfold wotsC256Verify wotsC256PkLeaf
  cases hDec : wotsC256DecodeValidDigest (suite.thDigest pkSeed adrs msg ctr) with
  | none =>
    rw [hDec] at hSign
    cases hSign
  | some d =>
    rw [hDec] at hSign
    dsimp only at hSign ⊢
    injection hSign with hEq
    subst hEq
    have hEnds :
        (fun chain => wotsC256CompleteTo3 suite pkSeed adrs chain (d.digits chain)
          (wotsC256PosFrom0 suite pkSeed adrs chain (suite.prf pkSeed skSeed adrs chain) (d.digits chain).val)) =
        (fun chain => wotsC256PosFrom0 suite pkSeed adrs chain (suite.prf pkSeed skSeed adrs chain) 3) := by
      funext chain
      exact wotsC256CompleteTo3_honest_eq suite pkSeed adrs chain (suite.prf pkSeed skSeed adrs chain) (d.digits chain)
    simp only [hEnds, beq_self_eq_true]

/-- Constructive `Type`-valued cryptographic break extracted from any 1-use `WOTS+C` forgery. -/
inductive WotsC256BreakWitness (suite : WotsC256HashSuite)
    (pkSeed skSeed : BitVec 256) (adrs : WotsLeafAdrs)
    (msg : BitVec 256) (ctr : UInt32) : Type where
  | digestSecondPreimage (msg' : BitVec 256) (ctr' : UInt32)
      (hPairNe : (msg', ctr') ≠ (msg, ctr))
      (hDigestEq : suite.thDigest pkSeed adrs msg' ctr' = suite.thDigest pkSeed adrs msg ctr)
  | leafTlCollision (endpoints' : Fin 128 → BitVec 256) (chain : Fin 128)
      (hEndNe : endpoints' chain ≠
        wotsC256PosFrom0 suite pkSeed adrs chain (suite.prf pkSeed skSeed adrs chain) 3)
      (hTlEq : suite.thTl pkSeed adrs endpoints' =
        suite.thTl pkSeed adrs (fun c => wotsC256PosFrom0 suite pkSeed adrs c (suite.prf pkSeed skSeed adrs c) 3))
  | chainStepCollision (chain : Fin 128) (step : Fin 3) (forgerInput : BitVec 256)
      (hInputNe : forgerInput ≠
        wotsC256PosFrom0 suite pkSeed adrs chain (suite.prf pkSeed skSeed adrs chain) step.val)
      (hStepEq : suite.thF pkSeed adrs chain step forgerInput =
        suite.thF pkSeed adrs chain step
          (wotsC256PosFrom0 suite pkSeed adrs chain (suite.prf pkSeed skSeed adrs chain) step.val))
  | chainUnrevealedPreimage (chain : Fin 128) (step : Fin 3) (forgerPreimage : BitVec 256)
      (d : WotsC256Digits)
      (hHonestDec : wotsC256DecodeValidDigest (suite.thDigest pkSeed adrs msg ctr) = some d)
      (hBeforeRevealed : step.val + 1 = (d.digits chain).val)
      (hExactPreimage : forgerPreimage =
        wotsC256PosFrom0 suite pkSeed adrs chain (suite.prf pkSeed skSeed adrs chain) step.val)
      (hInvertsRevealed : suite.thF pkSeed adrs chain step forgerPreimage =
        wotsC256PosFrom0 suite pkSeed adrs chain (suite.prf pkSeed skSeed adrs chain) (d.digits chain).val)

/-- **Constructive 1-Use 256-Bit `WOTS+C` EUF-CMA Extractor (`wotsC256_one_use_euf_cma_extract`)**:
    Given one honestly signed pair `(msg, ctr)` (`wotsC256DecodeValidDigest ... = some d`) and any
    valid forgery `(msg', ctr', sigChains')` with `(msg', ctr') ≠ (msg, ctr)` (in particular any
    `msg' ≠ msg`), constructively extracts (`0 Classical.choice`) an explicit `WotsC256BreakWitness`. -/
def wotsC256_one_use_euf_cma_extract
    (suite : WotsC256HashSuite) (pkSeed skSeed : BitVec 256) (adrs : WotsLeafAdrs)
    (msg : BitVec 256) (ctr : UInt32) (d : WotsC256Digits)
    (hHonestDec : wotsC256DecodeValidDigest (suite.thDigest pkSeed adrs msg ctr) = some d)
    (msg' : BitVec 256) (ctr' : UInt32) (sigChains' : Fin 128 → BitVec 256)
    (hPairNe : (msg', ctr') ≠ (msg, ctr))
    (hVerify : wotsC256Verify suite pkSeed adrs (wotsC256PkLeaf suite pkSeed skSeed adrs) msg' ctr' sigChains' = true) :
    WotsC256BreakWitness suite pkSeed skSeed adrs msg ctr :=
  let dig := suite.thDigest pkSeed adrs msg ctr
  let dig' := suite.thDigest pkSeed adrs msg' ctr'
  if hDigEq : dig' = dig then
    .digestSecondPreimage msg' ctr' hPairNe hDigEq
  else
    match hDec' : wotsC256DecodeValidDigest dig' with
    | none =>
      False.elim <| by
        unfold wotsC256Verify at hVerify
        dsimp only [dig'] at hDec'
        rw [hDec'] at hVerify
        cases hVerify
    | some d' =>
      have hDigitsHonest : d.digits = wotsC256DigitOfDigest dig :=
        wotsC256DecodeValidDigest_some_digits hHonestDec
      have hDigitsForger : d'.digits = wotsC256DigitOfDigest dig' :=
        wotsC256DecodeValidDigest_some_digits hDec'
      have hCodeNe : d ≠ d' := fun hEq => by
        apply hDigEq
        apply wotsC256DigitOfDigest_injective
        intro k
        have hk := congrArg (fun w : WotsC256Digits => w.digits k) hEq
        rw [hDigitsHonest, hDigitsForger] at hk
        exact hk.symm
      let ⟨chain, hLt⟩ := extractStrictDropIdx d d' hCodeNe
      let endpoints' : Fin 128 → BitVec 256 := fun c =>
        wotsC256CompleteTo3 suite pkSeed adrs c (d'.digits c) (sigChains' c)
      let xPos : Nat → BitVec 256 :=
        wotsC256PosFrom0 suite pkSeed adrs chain (suite.prf pkSeed skSeed adrs chain)
      let yPos : Nat → BitVec 256 :=
        wotsC256AdvanceTo suite pkSeed adrs chain (d'.digits chain) (sigChains' chain)
      have hTlEq : suite.thTl pkSeed adrs endpoints' =
          suite.thTl pkSeed adrs (fun c => wotsC256PosFrom0 suite pkSeed adrs c (suite.prf pkSeed skSeed adrs c) 3) := by
        unfold wotsC256Verify wotsC256PkLeaf at hVerify
        dsimp only [dig'] at hDec'
        rw [hDec'] at hVerify
        dsimp only at hVerify
        exact eq_of_beq hVerify
      if hEndNe : endpoints' chain ≠ xPos 3 then
        .leafTlCollision endpoints' chain hEndNe hTlEq
      else
        have hY3Eq : yPos 3 = xPos 3 := Decidable.of_not_not hEndNe
        -- Walk backward from 3 down to `d.digits chain` (where `1 ≤ d.digits chain ≤ 3`), then at `d.digits chain - 1`.
        if hY2Ne : yPos 2 ≠ xPos 2 then
          have hDpLe2 : (d'.digits chain).val ≤ 2 := by
            have := (d.digits chain).isLt
            omega
          have hColl2 : suite.thF pkSeed adrs chain ⟨2, by decide⟩ (yPos 2) =
              suite.thF pkSeed adrs chain ⟨2, by decide⟩ (xPos 2) := by
            rw [wotsC256AdvanceTo_step suite pkSeed adrs chain (d'.digits chain) (sigChains' chain) ⟨2, by decide⟩ hDpLe2,
                wotsC256PosFrom0_step suite pkSeed adrs chain _ ⟨2, by decide⟩]
            exact hY3Eq
          if hD3 : (d.digits chain).val = 3 then
            -- `d = 3`, so step `2` is `d - 1`, and `yPos 2 ≠ xPos 2` already gives a step-2 SM-TCR collision!
            .chainStepCollision chain ⟨2, by decide⟩ (yPos 2) hY2Ne hColl2
          else
            .chainStepCollision chain ⟨2, by decide⟩ (yPos 2) hY2Ne hColl2
        else
          have hY2Eq : yPos 2 = xPos 2 := Decidable.of_not_not hY2Ne
          if hD3 : (d.digits chain).val = 3 then
            -- `yPos 2 = xPos 2` and `d = 3` (`step = 2 < 3 = d`): exact unrevealed preimage inversion!
            have hDpLe2 : (d'.digits chain).val ≤ 2 := by omega
            have hInv2 : suite.thF pkSeed adrs chain ⟨2, by decide⟩ (yPos 2) = xPos (d.digits chain).val := by
              rw [hY2Eq, wotsC256PosFrom0_step suite pkSeed adrs chain _ ⟨2, by decide⟩, hD3]
            .chainUnrevealedPreimage chain ⟨2, by decide⟩ (yPos 2) d hHonestDec
              (by simp [hD3]) hY2Eq hInv2
          else if hY1Ne : yPos 1 ≠ xPos 1 then
            have hDpLe1 : (d'.digits chain).val ≤ 1 := by
              have := (d.digits chain).isLt
              omega
            have hColl1 : suite.thF pkSeed adrs chain ⟨1, by decide⟩ (yPos 1) =
                suite.thF pkSeed adrs chain ⟨1, by decide⟩ (xPos 1) := by
              rw [wotsC256AdvanceTo_step suite pkSeed adrs chain (d'.digits chain) (sigChains' chain) ⟨1, by decide⟩ hDpLe1,
                  wotsC256PosFrom0_step suite pkSeed adrs chain _ ⟨1, by decide⟩]
              exact hY2Eq
            .chainStepCollision chain ⟨1, by decide⟩ (yPos 1) hY1Ne hColl1
          else
            have hY1Eq : yPos 1 = xPos 1 := Decidable.of_not_not hY1Ne
            if hD2 : (d.digits chain).val = 2 then
              have hInv1 : suite.thF pkSeed adrs chain ⟨1, by decide⟩ (yPos 1) = xPos (d.digits chain).val := by
                rw [hY1Eq, wotsC256PosFrom0_step suite pkSeed adrs chain _ ⟨1, by decide⟩, hD2]
              .chainUnrevealedPreimage chain ⟨1, by decide⟩ (yPos 1) d hHonestDec
                (by simp [hD2]) hY1Eq hInv1
            else
              -- Since `d' < d ≤ 3`, `d ≠ 3`, and `d ≠ 2`, we must have `d = 1` and `d' = 0`!
              have hD1 : (d.digits chain).val = 1 := by
                have := (d.digits chain).isLt
                omega
              have hDp0 : (d'.digits chain).val = 0 := by omega
              if hY0Ne : yPos 0 ≠ xPos 0 then
                have hColl0 : suite.thF pkSeed adrs chain ⟨0, by decide⟩ (yPos 0) =
                    suite.thF pkSeed adrs chain ⟨0, by decide⟩ (xPos 0) := by
                  rw [wotsC256AdvanceTo_step suite pkSeed adrs chain (d'.digits chain) (sigChains' chain) ⟨0, by decide⟩ (by omega),
                      wotsC256PosFrom0_step suite pkSeed adrs chain _ ⟨0, by decide⟩]
                  exact hY1Eq
                .chainStepCollision chain ⟨0, by decide⟩ (yPos 0) hY0Ne hColl0
              else
                have hY0Eq : yPos 0 = xPos 0 := Decidable.of_not_not hY0Ne
                have hInv0 : suite.thF pkSeed adrs chain ⟨0, by decide⟩ (yPos 0) = xPos (d.digits chain).val := by
                  rw [hY0Eq, wotsC256PosFrom0_step suite pkSeed adrs chain _ ⟨0, by decide⟩, hD1]
                .chainUnrevealedPreimage chain ⟨0, by decide⟩ (yPos 0) d hHonestDec
                  (by simp [hD1]) hY0Eq hInv0

theorem wotsC256_one_use_euf_cma_sound
    (suite : WotsC256HashSuite) (pkSeed skSeed : BitVec 256) (adrs : WotsLeafAdrs)
    (msg : BitVec 256) (ctr : UInt32) (d : WotsC256Digits)
    (hHonestDec : wotsC256DecodeValidDigest (suite.thDigest pkSeed adrs msg ctr) = some d)
    (msg' : BitVec 256) (ctr' : UInt32) (sigChains' : Fin 128 → BitVec 256)
    (hMsgNe : msg' ≠ msg)
    (hVerify : wotsC256Verify suite pkSeed adrs (wotsC256PkLeaf suite pkSeed skSeed adrs) msg' ctr' sigChains' = true) :
    Nonempty (WotsC256BreakWitness suite pkSeed skSeed adrs msg ctr) :=
  ⟨wotsC256_one_use_euf_cma_extract suite pkSeed skSeed adrs msg ctr d hHonestDec
    msg' ctr' sigChains' (fun hEq => hMsgNe (congrArg Prod.fst hEq)) hVerify⟩

/-- Unconstrained verifier omitting the `sum = 192` target-sum guard (`#tooth` baseline). -/
def wotsC256VerifyUnconstrained (suite : WotsC256HashSuite) (pkSeed : BitVec 256)
    (adrs : WotsLeafAdrs) (pkLeaf : BitVec 256)
    (msg : BitVec 256) (ctr : UInt32) (sigChains : Fin 128 → BitVec 256) : Bool :=
  let f := wotsC256DigitOfDigest (suite.thDigest pkSeed adrs msg ctr)
  let endpoints : Fin 128 → BitVec 256 := fun chain =>
    wotsC256CompleteTo3 suite pkSeed adrs chain (f chain) (sigChains chain)
  suite.thTl pkSeed adrs endpoints == pkLeaf

/-- Public 1-hash-step forgery routine (`0` access to `skSeed`, `1` evaluation of `suite.thF`). -/
def forgeStepOneChain (suite : WotsC256HashSuite) (pkSeed : BitVec 256)
    (adrs : WotsLeafAdrs) (i : Fin 128) (step : Fin 3)
    (honestSigChains : Fin 128 → BitVec 256) : Fin 128 → BitVec 256 :=
  fun j =>
    if j = i then suite.thF pkSeed adrs i step (honestSigChains i)
    else honestSigChains j

private theorem wotsC256CompleteTo3_step_one (suite : WotsC256HashSuite)
    (pkSeed : BitVec 256) (adrs : WotsLeafAdrs) (c : Fin 128)
    (dv : Fin 4) (hLt3 : dv.val < 3) (node : BitVec 256) :
    wotsC256CompleteTo3 suite pkSeed adrs c ⟨dv.val + 1, Nat.succ_lt_succ hLt3⟩
      (suite.thF pkSeed adrs c ⟨dv.val, hLt3⟩ node) =
    wotsC256CompleteTo3 suite pkSeed adrs c dv node := by
  match dv, hLt3 with
  | ⟨0, _⟩, _ => rfl
  | ⟨1, _⟩, _ => rfl
  | ⟨2, _⟩, _ => rfl
  | ⟨3, _⟩, hBad => exact False.elim (Nat.lt_irrefl 3 hBad)

/-- **`#tooth` Omitting `target_sum = 192` Enables 1-Hash-Step Forgery (`tooth_wotsc_without_target_sum_forges`)**:
    Without the `sum = 192` constraint, stepping ANY chain `i` with `d i < 3` forward by 1 public
    `thF` evaluation produces a valid `wotsC256VerifyUnconstrained = true` forgery on `msg' ≠ msg`
    with `0` secret-key access, whereas `wotsC256Verify` (`sum = 192`) rejects `msg'`. -/
theorem tooth_wotsc_without_target_sum_forges
    (suite : WotsC256HashSuite) (pkSeed skSeed : BitVec 256) (adrs : WotsLeafAdrs)
    (msg msg' : BitVec 256) (ctr ctr' : UInt32)
    (d : WotsC256Digits) (honestSig : Fin 128 → BitVec 256)
    (i : Fin 128) (hLt3 : (d.digits i).val < 3)
    (hMsgNe : msg' ≠ msg)
    (hDec : wotsC256DecodeValidDigest (suite.thDigest pkSeed adrs msg ctr) = some d)
    (hSign : wotsC256Sign suite pkSeed skSeed adrs msg ctr = some honestSig)
    (hSteppedDigest : ∀ j : Fin 128,
      wotsC256DigitOfDigest (suite.thDigest pkSeed adrs msg' ctr') j =
        if j = i then ⟨(d.digits i).val + 1, Nat.succ_lt_succ hLt3⟩ else d.digits j) :
    let forged := forgeStepOneChain suite pkSeed adrs i ⟨(d.digits i).val, hLt3⟩ honestSig
    let pkLeaf := wotsC256PkLeaf suite pkSeed skSeed adrs
    wotsC256VerifyUnconstrained suite pkSeed adrs pkLeaf msg' ctr' forged = true ∧
    wotsC256Verify suite pkSeed adrs pkLeaf msg' ctr' forged = false := by
  intro forged pkLeaf
  have _ := hMsgNe
  have hHonestVer := wotsC256_sign_verify_complete suite pkSeed skSeed adrs msg ctr honestSig hSign
  unfold wotsC256Verify at hHonestVer
  rw [hDec] at hHonestVer
  dsimp only at hHonestVer
  have hHonestTl : suite.thTl pkSeed adrs
      (fun c => wotsC256CompleteTo3 suite pkSeed adrs c (d.digits c) (honestSig c)) = pkLeaf :=
    eq_of_beq hHonestVer
  refine ⟨?_, ?_⟩
  · unfold wotsC256VerifyUnconstrained
    dsimp only
    have hSameEnds :
        (fun c => wotsC256CompleteTo3 suite pkSeed adrs c
          (wotsC256DigitOfDigest (suite.thDigest pkSeed adrs msg' ctr') c) (forged c)) =
        (fun c => wotsC256CompleteTo3 suite pkSeed adrs c (d.digits c) (honestSig c)) := by
      funext c
      rw [hSteppedDigest c]
      dsimp only [forged, forgeStepOneChain]
      if hc : c = i then
        subst hc
        simp only [↓reduceIte]
        exact wotsC256CompleteTo3_step_one suite pkSeed adrs c (d.digits c) hLt3 (honestSig c)
      else
        simp only [hc, ↓reduceIte]
    rw [hSameEnds, hHonestTl, beq_self_eq_true]
  · unfold wotsC256Verify
    have hSum193 :
        qsum 128 (fun j => (wotsC256DigitOfDigest (suite.thDigest pkSeed adrs msg' ctr') j).val) = 193 := by
      have hCongr :
          qsum 128 (fun j => (wotsC256DigitOfDigest (suite.thDigest pkSeed adrs msg' ctr') j).val) =
          qsum 128 (fun j => (d.digits j).val + (if j = i then 1 else 0)) := by
        apply qsum_congr
        intro j
        rw [hSteppedDigest j]
        if hj : j = i then
          subst hj; simp
        else
          simp [hj]
      rw [hCongr, qsum_add, d.sum_eq, qsum_eq_indicator 128 i]
    have hDecNone : wotsC256DecodeValidDigest (suite.thDigest pkSeed adrs msg' ctr') = none :=
      wotsC256DecodeValidDigest_of_sum_ne (by rw [hSum193]; decide)
    rw [hDecNone]

/-! ## 2. `Rss256Engine` 256-Way Bitsliced `CNF-RSS` Privacy, Post-Wave 2-Challenge `BGIN19` Soundness & Sticky Poisoning -/

abbrev Plane256 := BitVec 256

/-- 2-of-3 CNF-RSS sharing of a 256-lane bit-plane `x = s0 ^^^ s1 ^^^ s2`:
    - `P0` holds `(s2, s0)` and PRG pad streams `(prg0, prg1)`
    - `P1` holds `(s0, s1)` and PRG pad streams `(prg1, prg2)`
    - `P2` holds `(s1, s2)` and PRG pad streams `(prg2, prg0)`. -/
structure RssPlane256Share where
  s0 : Plane256
  s1 : Plane256
  s2 : Plane256
  deriving DecidableEq

def RssPlane256Share.reconstruct (sh : RssPlane256Share) : Plane256 :=
  sh.s0 ^^^ sh.s1 ^^^ sh.s2

/-- Unmasked CNF-RSS cross-product shares (`c0` computed by `P1`, `c1` by `P2`, `c2` by `P0`). -/
def rss256CrossTerms (x y : RssPlane256Share) : Plane256 × Plane256 × Plane256 :=
  let c0 := (x.s0 &&& y.s0) ^^^ (x.s0 &&& y.s1) ^^^ (x.s1 &&& y.s0)
  let c1 := (x.s1 &&& y.s1) ^^^ (x.s1 &&& y.s2) ^^^ (x.s2 &&& y.s1)
  let c2 := (x.s2 &&& y.s2) ^^^ (x.s2 &&& y.s0) ^^^ (x.s0 &&& y.s2)
  (c0, c1, c2)

/-- **Corrected `(prg1, prg2, prg0)` Mask-Key Assignment (`rss256AndWireCorrected`)**:
    - `u0` (`P1 -> P0`) uses `prg1 ^^^ prg2` (`P0` lacks `prg2`!)
    - `u1` (`P2 -> P1`) uses `prg2 ^^^ prg0` (`P1` lacks `prg0`!)
    - `u2` (`P0 -> P2`) uses `prg0 ^^^ prg1` (`P2` lacks `prg1`!). -/
@[expose] def rss256AndWireCorrected (x y : RssPlane256Share)
    (prg0 prg1 prg2 : Plane256) : RssPlane256Share :=
  let (c0, c1, c2) := rss256CrossTerms x y
  { s0 := c0 ^^^ prg1 ^^^ prg2
    s1 := c1 ^^^ prg2 ^^^ prg0
    s2 := c2 ^^^ prg0 ^^^ prg1 }

/-- Naive off-by-one `(prg0, prg1, prg2)` mask-key assignment (`#tooth` baseline). -/
def rss256AndWireNaiveOffByOne (x y : RssPlane256Share)
    (prg0 prg1 prg2 : Plane256) : RssPlane256Share :=
  let (c0, c1, c2) := rss256CrossTerms x y
  { s0 := c0 ^^^ prg0 ^^^ prg1
    s1 := c1 ^^^ prg1 ^^^ prg2
    s2 := c2 ^^^ prg2 ^^^ prg0 }

theorem rss256_and_gate_reconstructs (x y : RssPlane256Share) (prg0 prg1 prg2 : Plane256) :
    (rss256AndWireCorrected x y prg0 prg1 prg2).reconstruct =
      (x.reconstruct &&& y.reconstruct) ∧
    (rss256AndWireNaiveOffByOne x y prg0 prg1 prg2).reconstruct =
      (x.reconstruct &&& y.reconstruct) := by
  constructor <;> {
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [RssPlane256Share.reconstruct, rss256AndWireCorrected, rss256AndWireNaiveOffByOne,
      rss256CrossTerms, BitVec.getLsbD_xor, BitVec.getLsbD_and]
    cases x.s0.getLsbD i <;> cases x.s1.getLsbD i <;> cases x.s2.getLsbD i <;>
      cases y.s0.getLsbD i <;> cases y.s1.getLsbD i <;> cases y.s2.getLsbD i <;>
      cases prg0.getLsbD i <;> cases prg1.getLsbD i <;> cases prg2.getLsbD i <;> rfl
  }

/-- 2-of-3 CNF-RSS sharing over `Tower128` (`GF(2^{128})`) for `BGIN19` degree-2 product proofs. -/
structure RssTower128Share where
  s0 : Tower128
  s1 : Tower128
  s2 : Tower128
  deriving DecidableEq

def RssTower128Share.reconstruct (sh : RssTower128Share) : Tower128 :=
  towerAdd 7 (towerAdd 7 sh.s0 sh.s1) sh.s2

/-- `BGIN19` degree-2 multiplication-check relation witness:
    `(X0 + τ DX) * (Y0 + τ DY) - (Z0 + τ C1 + τ^2 C2) = 0` at every challenge `τ ∈ GF(2^{128})`,
    where `X0 * Y0 = Z0`, `X0 * DY + DX * Y0 = C1`, and `DX * DY = C2`. -/
structure Bgin19Deg2Witness where
  x0 : RssTower128Share
  y0 : RssTower128Share
  dx : RssTower128Share
  dy : RssTower128Share
  c1 : RssTower128Share
  c2 : RssTower128Share

def bgin19CrossProdShare (a b : RssTower128Share) : RssTower128Share where
  s0 := towerAdd 7 (towerAdd 7 (towerMul 7 a.s0 b.s0) (towerMul 7 a.s0 b.s1)) (towerMul 7 a.s1 b.s0)
  s1 := towerAdd 7 (towerAdd 7 (towerMul 7 a.s1 b.s1) (towerMul 7 a.s1 b.s2)) (towerMul 7 a.s2 b.s1)
  s2 := towerAdd 7 (towerAdd 7 (towerMul 7 a.s2 b.s2) (towerMul 7 a.s2 b.s0)) (towerMul 7 a.s0 b.s2)

private theorem bgin19CrossProdShare_reconstruct (a b : RssTower128Share) :
    (bgin19CrossProdShare a b).reconstruct = towerMul 7 a.reconstruct b.reconstruct := by
  simp only [bgin19CrossProdShare, RssTower128Share.reconstruct,
    towerAdd_mul_distrib, towerMul_add_distrib]
  simp only [towerAdd_assoc, towerAdd_comm, towerAdd_left_comm]

def Bgin19Deg2Witness.Valid (w : Bgin19Deg2Witness) : Prop :=
  w.c1.reconstruct =
    towerAdd 7 (towerMul 7 w.x0.reconstruct w.dy.reconstruct)
               (towerMul 7 w.dx.reconstruct w.y0.reconstruct) ∧
  w.c2.reconstruct = towerMul 7 w.dx.reconstruct w.dy.reconstruct

/-- Unmasked degree-1 and degree-2 residual polynomial shares (`sum = 0` iff `w.Valid`). -/
def bgin19UnmaskedCoeffShares (w : Bgin19Deg2Witness) : RssTower128Share × RssTower128Share :=
  let prod1a := bgin19CrossProdShare w.x0 w.dy
  let prod1b := bgin19CrossProdShare w.dx w.y0
  let prod2  := bgin19CrossProdShare w.dx w.dy
  let deg1 : RssTower128Share :=
    { s0 := towerAdd 7 (towerAdd 7 prod1a.s0 prod1b.s0) w.c1.s0
      s1 := towerAdd 7 (towerAdd 7 prod1a.s1 prod1b.s1) w.c1.s1
      s2 := towerAdd 7 (towerAdd 7 prod1a.s2 prod1b.s2) w.c1.s2 }
  let deg2 : RssTower128Share :=
    { s0 := towerAdd 7 prod2.s0 w.c2.s0
      s1 := towerAdd 7 prod2.s1 w.c2.s1
      s2 := towerAdd 7 prod2.s2 w.c2.s2 }
  (deg1, deg2)

private theorem bgin19UnmaskedCoeffShares_zero_sum {w : Bgin19Deg2Witness} (hValid : w.Valid) :
    (bgin19UnmaskedCoeffShares w).1.reconstruct = towerZero 7 ∧
    (bgin19UnmaskedCoeffShares w).2.reconstruct = towerZero 7 := by
  rcases hValid with ⟨hc1, hc2⟩
  have h1 := bgin19CrossProdShare_reconstruct w.x0 w.dy
  have h2 := bgin19CrossProdShare_reconstruct w.dx w.y0
  have h3 := bgin19CrossProdShare_reconstruct w.dx w.dy
  constructor
  · change towerAdd 7
      (towerAdd 7
        (towerAdd 7 (towerAdd 7 (bgin19CrossProdShare w.x0 w.dy).s0 (bgin19CrossProdShare w.dx w.y0).s0) w.c1.s0)
        (towerAdd 7 (towerAdd 7 (bgin19CrossProdShare w.x0 w.dy).s1 (bgin19CrossProdShare w.dx w.y0).s1) w.c1.s1))
      (towerAdd 7 (towerAdd 7 (bgin19CrossProdShare w.x0 w.dy).s2 (bgin19CrossProdShare w.dx w.y0).s2) w.c1.s2) =
      towerZero 7
    have hRearr :
        towerAdd 7
          (towerAdd 7
            (towerAdd 7 (towerAdd 7 (bgin19CrossProdShare w.x0 w.dy).s0 (bgin19CrossProdShare w.dx w.y0).s0) w.c1.s0)
            (towerAdd 7 (towerAdd 7 (bgin19CrossProdShare w.x0 w.dy).s1 (bgin19CrossProdShare w.dx w.y0).s1) w.c1.s1))
          (towerAdd 7 (towerAdd 7 (bgin19CrossProdShare w.x0 w.dy).s2 (bgin19CrossProdShare w.dx w.y0).s2) w.c1.s2) =
        towerAdd 7
          (towerAdd 7 (bgin19CrossProdShare w.x0 w.dy).reconstruct (bgin19CrossProdShare w.dx w.y0).reconstruct)
          w.c1.reconstruct := by
      unfold RssTower128Share.reconstruct
      simp only [towerAdd_comm, towerAdd_left_comm]
    rw [hRearr, h1, h2, hc1, towerAdd_self_zero]
  · have hRearr2 :
        (bgin19UnmaskedCoeffShares w).2.reconstruct =
        towerAdd 7 (bgin19CrossProdShare w.dx w.dy).reconstruct w.c2.reconstruct := by
      unfold bgin19UnmaskedCoeffShares RssTower128Share.reconstruct
      simp only [towerAdd_comm, towerAdd_left_comm]
    rw [hRearr2, h3, hc2, towerAdd_self_zero]

/-- Masked `BGIN19` degree-2 prover messages under `(prg1, prg2, prg0)` zero-sharing:
    each party `P1, P2, P0` masks its `(deg1, deg2)` polynomial coefficients with `(zpad1⊕zpad2, zpad2⊕zpad0, zpad0⊕zpad1)`,
    and also evaluates `m(τ) = τ * m_deg1 ⊕ τ^2 * m_deg2` at challenge `τ`. -/
structure Rss256JointCorruptView where
  inboundAndWire : Plane256
  outboundAndWire : Plane256
  proverA_deg1 : Tower128
  proverA_deg2 : Tower128
  proverB_deg1 : Tower128
  proverB_deg2 : Tower128
  own_deg1 : Tower128
  own_deg2 : Tower128
  evalAtTau_proverA : Tower128
  evalAtTau_proverB : Tower128
  deriving DecidableEq

/-- Pack/unpack `(Tower128 × Tower128)` into `BitVec 256` (`joinBits 7`). -/
def packTower128Pair (a b : Tower128) : BitVec 256 :=
  joinBits 7 (packTower 7 a) (packTower 7 b)

def unpackTower128Pair (v : BitVec 256) : Tower128 × Tower128 :=
  (unpackTower 7 (lowBits 7 v), unpackTower 7 (highBits 7 v))

private theorem lowBits_xor_7 (u v : BitVec 256) :
    lowBits 7 (u ^^^ v) = lowBits 7 u ^^^ lowBits 7 v := by
  have h := congrArg (lowBits 7)
    (joinBits_xor 7 (lowBits 7 u) (lowBits 7 v) (highBits 7 u) (highBits 7 v))
  rw [lowBits_join, joinBits_split, joinBits_split] at h
  exact h.symm

private theorem highBits_xor_7 (u v : BitVec 256) :
    highBits 7 (u ^^^ v) = highBits 7 u ^^^ highBits 7 v := by
  have h := congrArg (highBits 7)
    (joinBits_xor 7 (lowBits 7 u) (lowBits 7 v) (highBits 7 u) (highBits 7 v))
  rw [highBits_join, joinBits_split, joinBits_split] at h
  exact h.symm

private theorem unpackTower128Pair_xor_pack (v : BitVec 256) (d1 d2 : Tower128) :
    unpackTower128Pair (v ^^^ packTower128Pair d1 d2) =
      (towerAdd 7 (unpackTower128Pair v).1 d1, towerAdd 7 (unpackTower128Pair v).2 d2) := by
  unfold unpackTower128Pair packTower128Pair
  rw [lowBits_xor_7, highBits_xor_7, lowBits_join, highBits_join]
  have h1 : lowBits 7 v ^^^ packTower 7 d1 = packTower 7 (towerAdd 7 (unpackTower 7 (lowBits 7 v)) d1) := by
    rw [packTower_add, packTower_unpackTower]
  have h2 : highBits 7 v ^^^ packTower 7 d2 = packTower 7 (towerAdd 7 (unpackTower 7 (highBits 7 v)) d2) := by
    rw [packTower_add, packTower_unpackTower]
  rw [h1, h2, unpackTower_packTower, unpackTower_packTower]

/-- Real-world joint view of 1-corrupt party `corrupt : Fin 3` over the missing random-pad space
    `Fin ((2 ^ 256) * (2 ^ 256))` (256-bit missing AND pad × 256-bit missing `BGIN19` `(deg1, deg2)` pad). -/
def rss256RealCorruptView (corrupt : Fin 3)
    (x y : RssPlane256Share) (w : Bgin19Deg2Witness)
    (knownPrgA knownPrgB : Plane256)
    (knownZpadA knownZpadB : Tower128 × Tower128)
    (tau : Tower128)
    (ω : Fin ((2 ^ 256) * (2 ^ 256))) : Rss256JointCorruptView :=
  let missingAndPad : Plane256 := BitVec.ofFin (splitFinLeft (Nat.two_pow_pos 256) ω)
  let missingZpad := unpackTower128Pair (BitVec.ofFin (splitFinRight (Nat.two_pow_pos 256) ω))
  let (d1, d2) := bgin19UnmaskedCoeffShares w
  let tauSq := towerMul 7 tau tau
  let evalPoly (c1 c2 : Tower128) : Tower128 :=
    towerAdd 7 (towerMul 7 tau c1) (towerMul 7 tauSq c2)
  match corrupt with
  | ⟨0, _⟩ =>
    -- `P0` knows `(prg0 = knownPrgA, prg1 = knownPrgB)` and lacks `prg2 = missingAndPad`!
    let wires := rss256AndWireCorrected x y knownPrgA knownPrgB missingAndPad
    let m0_1 := towerAdd 7 (towerAdd 7 d1.s0 knownZpadB.1) missingZpad.1
    let m0_2 := towerAdd 7 (towerAdd 7 d2.s0 knownZpadB.2) missingZpad.2
    let m1_1 := towerAdd 7 (towerAdd 7 d1.s1 missingZpad.1) knownZpadA.1
    let m1_2 := towerAdd 7 (towerAdd 7 d2.s1 missingZpad.2) knownZpadA.2
    let m2_1 := towerAdd 7 (towerAdd 7 d1.s2 knownZpadA.1) knownZpadB.1
    let m2_2 := towerAdd 7 (towerAdd 7 d2.s2 knownZpadA.2) knownZpadB.2
    { inboundAndWire := wires.s0
      outboundAndWire := wires.s2
      proverA_deg1 := m0_1, proverA_deg2 := m0_2
      proverB_deg1 := m1_1, proverB_deg2 := m1_2
      own_deg1 := m2_1, own_deg2 := m2_2
      evalAtTau_proverA := evalPoly m0_1 m0_2
      evalAtTau_proverB := evalPoly m1_1 m1_2 }
  | ⟨1, _⟩ =>
    -- `P1` knows `(prg1 = knownPrgA, prg2 = knownPrgB)` and lacks `prg0 = missingAndPad`!
    let wires := rss256AndWireCorrected x y missingAndPad knownPrgA knownPrgB
    let m1_1 := towerAdd 7 (towerAdd 7 d1.s1 knownZpadB.1) missingZpad.1
    let m1_2 := towerAdd 7 (towerAdd 7 d2.s1 knownZpadB.2) missingZpad.2
    let m2_1 := towerAdd 7 (towerAdd 7 d1.s2 missingZpad.1) knownZpadA.1
    let m2_2 := towerAdd 7 (towerAdd 7 d2.s2 missingZpad.2) knownZpadA.2
    let m0_1 := towerAdd 7 (towerAdd 7 d1.s0 knownZpadA.1) knownZpadB.1
    let m0_2 := towerAdd 7 (towerAdd 7 d2.s0 knownZpadA.2) knownZpadB.2
    { inboundAndWire := wires.s1
      outboundAndWire := wires.s0
      proverA_deg1 := m1_1, proverA_deg2 := m1_2
      proverB_deg1 := m2_1, proverB_deg2 := m2_2
      own_deg1 := m0_1, own_deg2 := m0_2
      evalAtTau_proverA := evalPoly m1_1 m1_2
      evalAtTau_proverB := evalPoly m2_1 m2_2 }
  | ⟨2, _⟩ =>
    -- `P2` knows `(prg2 = knownPrgA, prg0 = knownPrgB)` and lacks `prg1 = missingAndPad`!
    let wires := rss256AndWireCorrected x y knownPrgB missingAndPad knownPrgA
    let m2_1 := towerAdd 7 (towerAdd 7 d1.s2 knownZpadB.1) missingZpad.1
    let m2_2 := towerAdd 7 (towerAdd 7 d2.s2 knownZpadB.2) missingZpad.2
    let m0_1 := towerAdd 7 (towerAdd 7 d1.s0 missingZpad.1) knownZpadA.1
    let m0_2 := towerAdd 7 (towerAdd 7 d2.s0 missingZpad.2) knownZpadA.2
    let m1_1 := towerAdd 7 (towerAdd 7 d1.s1 knownZpadA.1) knownZpadB.1
    let m1_2 := towerAdd 7 (towerAdd 7 d2.s1 knownZpadA.2) knownZpadB.2
    { inboundAndWire := wires.s2
      outboundAndWire := wires.s1
      proverA_deg1 := m2_1, proverA_deg2 := m2_2
      proverB_deg1 := m0_1, proverB_deg2 := m0_2
      own_deg1 := m1_1, own_deg2 := m1_2
      evalAtTau_proverA := evalPoly m2_1 m2_2
      evalAtTau_proverB := evalPoly m0_1 m0_2 }

/-- Canonical dummy sharing constructed **solely** from `corrupt`'s 2 share slots (setting the
    missing honest slot to `0` and balancing `c1, c2` so `Valid` holds with zero secret knowledge!). -/
def rss256SimDummyInputs (corrupt : Fin 3)
    (x y : RssPlane256Share) (w : Bgin19Deg2Witness) :
    RssPlane256Share × RssPlane256Share × Bgin19Deg2Witness :=
  match corrupt with
  | ⟨0, _⟩ =>
    -- `P0` holds slots `(2, 0)` only; missing slot `1` is zeroed!
    let xSim : RssPlane256Share := { s0 := x.s0, s1 := 0, s2 := x.s2 }
    let ySim : RssPlane256Share := { s0 := y.s0, s1 := 0, s2 := y.s2 }
    let x0Sim : RssTower128Share := { s0 := w.x0.s0, s1 := towerZero 7, s2 := w.x0.s2 }
    let y0Sim : RssTower128Share := { s0 := w.y0.s0, s1 := towerZero 7, s2 := w.y0.s2 }
    let dxSim : RssTower128Share := { s0 := w.dx.s0, s1 := towerZero 7, s2 := w.dx.s2 }
    let dySim : RssTower128Share := { s0 := w.dy.s0, s1 := towerZero 7, s2 := w.dy.s2 }
    let wantC1 := towerAdd 7 (towerMul 7 x0Sim.reconstruct dySim.reconstruct)
                             (towerMul 7 dxSim.reconstruct y0Sim.reconstruct)
    let wantC2 := towerMul 7 dxSim.reconstruct dySim.reconstruct
    let c1Sim : RssTower128Share :=
      { s0 := w.c1.s0, s1 := towerAdd 7 wantC1 (towerAdd 7 w.c1.s0 w.c1.s2), s2 := w.c1.s2 }
    let c2Sim : RssTower128Share :=
      { s0 := w.c2.s0, s1 := towerAdd 7 wantC2 (towerAdd 7 w.c2.s0 w.c2.s2), s2 := w.c2.s2 }
    (xSim, ySim, { x0 := x0Sim, y0 := y0Sim, dx := dxSim, dy := dySim, c1 := c1Sim, c2 := c2Sim })
  | ⟨1, _⟩ =>
    -- `P1` holds slots `(0, 1)` only; missing slot `2` is zeroed!
    let xSim : RssPlane256Share := { s0 := x.s0, s1 := x.s1, s2 := 0 }
    let ySim : RssPlane256Share := { s0 := y.s0, s1 := y.s1, s2 := 0 }
    let x0Sim : RssTower128Share := { s0 := w.x0.s0, s1 := w.x0.s1, s2 := towerZero 7 }
    let y0Sim : RssTower128Share := { s0 := w.y0.s0, s1 := w.y0.s1, s2 := towerZero 7 }
    let dxSim : RssTower128Share := { s0 := w.dx.s0, s1 := w.dx.s1, s2 := towerZero 7 }
    let dySim : RssTower128Share := { s0 := w.dy.s0, s1 := w.dy.s1, s2 := towerZero 7 }
    let wantC1 := towerAdd 7 (towerMul 7 x0Sim.reconstruct dySim.reconstruct)
                             (towerMul 7 dxSim.reconstruct y0Sim.reconstruct)
    let wantC2 := towerMul 7 dxSim.reconstruct dySim.reconstruct
    let c1Sim : RssTower128Share :=
      { s0 := w.c1.s0, s1 := w.c1.s1, s2 := towerAdd 7 wantC1 (towerAdd 7 w.c1.s0 w.c1.s1) }
    let c2Sim : RssTower128Share :=
      { s0 := w.c2.s0, s1 := w.c2.s1, s2 := towerAdd 7 wantC2 (towerAdd 7 w.c2.s0 w.c2.s1) }
    (xSim, ySim, { x0 := x0Sim, y0 := y0Sim, dx := dxSim, dy := dySim, c1 := c1Sim, c2 := c2Sim })
  | ⟨2, _⟩ =>
    -- `P2` holds slots `(1, 2)` only; missing slot `0` is zeroed!
    let xSim : RssPlane256Share := { s0 := 0, s1 := x.s1, s2 := x.s2 }
    let ySim : RssPlane256Share := { s0 := 0, s1 := y.s1, s2 := y.s2 }
    let x0Sim : RssTower128Share := { s0 := towerZero 7, s1 := w.x0.s1, s2 := w.x0.s2 }
    let y0Sim : RssTower128Share := { s0 := towerZero 7, s1 := w.y0.s1, s2 := w.y0.s2 }
    let dxSim : RssTower128Share := { s0 := towerZero 7, s1 := w.dx.s1, s2 := w.dx.s2 }
    let dySim : RssTower128Share := { s0 := towerZero 7, s1 := w.dy.s1, s2 := w.dy.s2 }
    let wantC1 := towerAdd 7 (towerMul 7 x0Sim.reconstruct dySim.reconstruct)
                             (towerMul 7 dxSim.reconstruct y0Sim.reconstruct)
    let wantC2 := towerMul 7 dxSim.reconstruct dySim.reconstruct
    let c1Sim : RssTower128Share :=
      { s0 := towerAdd 7 wantC1 (towerAdd 7 w.c1.s1 w.c1.s2), s1 := w.c1.s1, s2 := w.c1.s2 }
    let c2Sim : RssTower128Share :=
      { s0 := towerAdd 7 wantC2 (towerAdd 7 w.c2.s1 w.c2.s2), s1 := w.c2.s1, s2 := w.c2.s2 }
    (xSim, ySim, { x0 := x0Sim, y0 := y0Sim, dx := dxSim, dy := dySim, c1 := c1Sim, c2 := c2Sim })

private theorem rss256SimDummyInputs_valid (corrupt : Fin 3)
    (x y : RssPlane256Share) (w : Bgin19Deg2Witness) :
    (rss256SimDummyInputs corrupt x y w).2.2.Valid := by
  match corrupt with
  | ⟨0, _⟩ =>
    constructor <;> {
      dsimp [rss256SimDummyInputs, RssTower128Share.reconstruct]
      simp only [towerAdd_assoc, towerAdd_comm, towerAdd_zero, towerAdd_cancel]
    }
  | ⟨1, _⟩ =>
    constructor <;> {
      dsimp [rss256SimDummyInputs, RssTower128Share.reconstruct]
      simp only [towerAdd_assoc, towerAdd_comm, towerAdd_left_comm, towerAdd_zero, towerAdd_cancel]
    }
  | ⟨2, _⟩ =>
    constructor <;> {
      dsimp [rss256SimDummyInputs, RssTower128Share.reconstruct]
      simp only [towerAdd_assoc, towerAdd_comm, towerAdd_left_comm, towerAdd_cancel]
    }

/-- Simulator view (depends **solely** on `corrupt`'s 2 slots and 2 PRG streams — zero honest secret bits!). -/
def rss256SimCorruptView (corrupt : Fin 3)
    (x y : RssPlane256Share) (w : Bgin19Deg2Witness)
    (knownPrgA knownPrgB : Plane256)
    (knownZpadA knownZpadB : Tower128 × Tower128)
    (tau : Tower128)
    (ω : Fin ((2 ^ 256) * (2 ^ 256))) : Rss256JointCorruptView :=
  let (xSim, ySim, wSim) := rss256SimDummyInputs corrupt x y w
  rss256RealCorruptView corrupt xSim ySim wSim knownPrgA knownPrgB knownZpadA knownZpadB tau ω

/-- **Constructive Pad-Space Bijection (`rss256_and_bgin19_privacy_equiv`, `0 Classical.choice`)**:
    Shifts the missing party's `(Plane256, Tower128 × Tower128)` pad stream so `rss256SimCorruptView`
    matches `rss256RealCorruptView` identically on every sample point `ω`. -/
def rss256_and_bgin19_privacy_equiv (corrupt : Fin 3)
    (x y : RssPlane256Share) (w : Bgin19Deg2Witness) :
    SimpleEquiv (Fin ((2 ^ 256) * (2 ^ 256))) (Fin ((2 ^ 256) * (2 ^ 256))) :=
  let (xSim, ySim, wSim) := rss256SimDummyInputs corrupt x y w
  let (rc0, rc1, rc2) := rss256CrossTerms x y
  let (sc0, sc1, sc2) := rss256CrossTerms xSim ySim
  let (rd1, rd2) := bgin19UnmaskedCoeffShares w
  let (sd1, sd2) := bgin19UnmaskedCoeffShares wSim
  let (deltaAnd, deltaD1, deltaD2) :=
    match corrupt with
    | ⟨0, _⟩ => (rc0 ^^^ sc0, towerAdd 7 rd1.s0 sd1.s0, towerAdd 7 rd2.s0 sd2.s0)
    | ⟨1, _⟩ => (rc1 ^^^ sc1, towerAdd 7 rd1.s1 sd1.s1, towerAdd 7 rd2.s1 sd2.s1)
    | ⟨2, _⟩ => (rc2 ^^^ sc2, towerAdd 7 rd1.s2 sd1.s2, towerAdd 7 rd2.s2 sd2.s2)
  depProdFinEquiv (Nat.two_pow_pos 256)
    (finBitVecXorEquiv 256 deltaAnd)
    (fun _ => finBitVecXorEquiv 256 (packTower128Pair deltaD1 deltaD2))

private theorem bv_xor_rearr (c sc k p : Plane256) :
    sc ^^^ k ^^^ (p ^^^ (c ^^^ sc)) = c ^^^ k ^^^ p := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_xor]
  cases c.getLsbD i <;> cases sc.getLsbD i <;> cases k.getLsbD i <;> cases p.getLsbD i <;> rfl

private theorem tower128_pad_shift_A (r0 s0 k p : Tower128) :
    towerAdd 7 (towerAdd 7 s0 k) (towerAdd 7 p (towerAdd 7 r0 s0)) =
      towerAdd 7 (towerAdd 7 r0 k) p := by
  simp only [towerAdd_comm, towerAdd_left_comm, towerAdd_cancel]

private theorem tower128_pad_shift_B {r0 r1 r2 s0 s1 s2 : Tower128}
    (hRealZero : towerAdd 7 (towerAdd 7 r0 r1) r2 = towerZero 7)
    (hSimZero : towerAdd 7 (towerAdd 7 s0 s1) s2 = towerZero 7)
    (hOwnEq : s2 = r2)
    (k p : Tower128) :
    towerAdd 7 (towerAdd 7 s1 (towerAdd 7 p (towerAdd 7 r0 s0))) k =
      towerAdd 7 (towerAdd 7 r1 p) k := by
  have hr1 : r1 = towerAdd 7 r0 r2 := by
    calc r1
      _ = towerAdd 7 r0 (towerAdd 7 r0 (towerAdd 7 r1 (towerAdd 7 r2 r2))) := by
        rw [towerAdd_self_zero, towerAdd_zero, towerAdd_cancel]
      _ = towerAdd 7 (towerAdd 7 (towerAdd 7 r0 r1) r2) (towerAdd 7 r0 r2) := by
        simp only [towerAdd_comm, towerAdd_left_comm]
      _ = towerAdd 7 r0 r2 := by rw [hRealZero, towerZero_add]
  have hs1 : s1 = towerAdd 7 s0 r2 := by
    rw [hOwnEq] at hSimZero
    calc s1
      _ = towerAdd 7 s0 (towerAdd 7 s0 (towerAdd 7 s1 (towerAdd 7 r2 r2))) := by
        rw [towerAdd_self_zero, towerAdd_zero, towerAdd_cancel]
      _ = towerAdd 7 (towerAdd 7 (towerAdd 7 s0 s1) r2) (towerAdd 7 s0 r2) := by
        simp only [towerAdd_comm, towerAdd_left_comm]
      _ = towerAdd 7 s0 r2 := by rw [hSimZero, towerZero_add]
  rw [hr1, hs1]
  simp only [towerAdd_comm, towerAdd_left_comm, towerAdd_cancel]

/-- **Exact 1-Corrupt `Rss256Engine` View Simulation (`rss256_one_corrupt_view_pointwise_and_count_eq`)**:
    Under the corrected `(prg1, prg2, prg0)` mask-key assignment, for EVERY corrupt party
    `corrupt ∈ {P0, P1, P2}`, EVERY secret 256-lane input `(x, y)`, EVERY valid `BGIN19` degree-2
    witness `w`, EVERY challenge `τ ∈ GF(2^{128})`, and EVERY distinguisher `D`:
    1. `rss256SimCorruptView` (using **0** bits of the missing honest share slot) equals
       `rss256RealCorruptView` point-for-point under `rss256_and_bgin19_privacy_equiv`;
    2. `D` accepts the real view and the simulated view on equally many pad tapes.
    The same statement in the vocabulary of the interactive UC engine (`distAcceptCount`,
    `rationalAcceptDiff`) is `rss256_one_corrupt_perfect_view_privacy` in
    `Qsag.Exec.Rss256OneCorruptViewPrivacy`. -/
theorem rss256_one_corrupt_view_pointwise_and_count_eq
    (corrupt : Fin 3)
    (x y : RssPlane256Share) (w : Bgin19Deg2Witness) (hValid : w.Valid)
    (knownPrgA knownPrgB : Plane256)
    (knownZpadA knownZpadB : Tower128 × Tower128)
    (tau : Tower128)
    (D : Rss256JointCorruptView → Bool) :
    let padCard := (2 ^ 256) * (2 ^ 256)
    let bij := rss256_and_bgin19_privacy_equiv corrupt x y w
    let realExec := rss256RealCorruptView corrupt x y w knownPrgA knownPrgB knownZpadA knownZpadB tau
    let simExec := rss256SimCorruptView corrupt x y w knownPrgA knownPrgB knownZpadA knownZpadB tau
    (∀ ω : Fin padCard, realExec ω = simExec (bij.toFun ω)) ∧
    qsum padCard (fun ω => if D (realExec ω) then 1 else 0) =
      qsum padCard (fun ω => if D (simExec ω) then 1 else 0) := by
  intro padCard bij realExec simExec
  have hCardPos : 0 < padCard := Nat.mul_pos (Nat.two_pow_pos 256) (Nat.two_pow_pos 256)
  have hPointwiseGen : ∀ (c : Fin 3) (ω : Fin padCard),
      rss256RealCorruptView c x y w knownPrgA knownPrgB knownZpadA knownZpadB tau ω =
      rss256SimCorruptView c x y w knownPrgA knownPrgB knownZpadA knownZpadB tau
        ((rss256_and_bgin19_privacy_equiv c x y w).toFun ω) := by
    intro c ω
    obtain ⟨hRealZ1, hRealZ2⟩ := bgin19UnmaskedCoeffShares_zero_sum hValid
    obtain ⟨hSimZ1, hSimZ2⟩ := bgin19UnmaskedCoeffShares_zero_sum (rss256SimDummyInputs_valid c x y w)
    have hSplitL : ∀ (dAnd dBgin : BitVec 256),
        BitVec.ofFin (splitFinLeft (Nat.two_pow_pos 256)
          ((depProdFinEquiv (Nat.two_pow_pos 256) (finBitVecXorEquiv 256 dAnd)
            (fun _ => finBitVecXorEquiv 256 dBgin)).toFun ω)) =
        BitVec.ofFin (splitFinLeft (Nat.two_pow_pos 256) ω) ^^^ dAnd := by
      intro dAnd dBgin
      rw [depProdFinEquiv_toFun, splitFinLeft_pairFin (Nat.two_pow_pos 256),
        finBitVecXorEquiv_toFun]
    have hSplitR : ∀ (dAnd dBgin : BitVec 256),
        BitVec.ofFin (splitFinRight (Nat.two_pow_pos 256)
          ((depProdFinEquiv (Nat.two_pow_pos 256) (finBitVecXorEquiv 256 dAnd)
            (fun _ => finBitVecXorEquiv 256 dBgin)).toFun ω)) =
        BitVec.ofFin (splitFinRight (Nat.two_pow_pos 256) ω) ^^^ dBgin := by
      intro dAnd dBgin
      rw [depProdFinEquiv_toFun, splitFinRight_pairFin (Nat.two_pow_pos 256),
        finBitVecXorEquiv_toFun]
    match c with
    | ⟨0, hc⟩ =>
      dsimp only [rss256SimCorruptView, rss256_and_bgin19_privacy_equiv, rss256RealCorruptView]
      rw [hSplitL, hSplitR, unpackTower128Pair_xor_pack]
      dsimp only [rss256AndWireCorrected]
      have hOwnAnd : (rss256CrossTerms (rss256SimDummyInputs ⟨0, hc⟩ x y w).1
                                       (rss256SimDummyInputs ⟨0, hc⟩ x y w).2.1).2.2 =
                     (rss256CrossTerms x y).2.2 := rfl
      have hOwnD1 : (bgin19UnmaskedCoeffShares (rss256SimDummyInputs ⟨0, hc⟩ x y w).2.2).1.s2 =
                    (bgin19UnmaskedCoeffShares w).1.s2 := rfl
      have hOwnD2 : (bgin19UnmaskedCoeffShares (rss256SimDummyInputs ⟨0, hc⟩ x y w).2.2).2.s2 =
                    (bgin19UnmaskedCoeffShares w).2.s2 := rfl
      have hInAnd := bv_xor_rearr (rss256CrossTerms x y).1
        (rss256CrossTerms (rss256SimDummyInputs ⟨0, hc⟩ x y w).1
                          (rss256SimDummyInputs ⟨0, hc⟩ x y w).2.1).1
        knownPrgB (BitVec.ofFin (splitFinLeft (Nat.two_pow_pos 256) ω))
      have hPA1 := tower128_pad_shift_A (bgin19UnmaskedCoeffShares w).1.s0
        (bgin19UnmaskedCoeffShares (rss256SimDummyInputs ⟨0, hc⟩ x y w).2.2).1.s0
        knownZpadB.1 (unpackTower128Pair (BitVec.ofFin (splitFinRight (Nat.two_pow_pos 256) ω))).1
      have hPA2 := tower128_pad_shift_A (bgin19UnmaskedCoeffShares w).2.s0
        (bgin19UnmaskedCoeffShares (rss256SimDummyInputs ⟨0, hc⟩ x y w).2.2).2.s0
        knownZpadB.2 (unpackTower128Pair (BitVec.ofFin (splitFinRight (Nat.two_pow_pos 256) ω))).2
      have hPB1 := tower128_pad_shift_B hRealZ1 hSimZ1 hOwnD1
        knownZpadA.1 (unpackTower128Pair (BitVec.ofFin (splitFinRight (Nat.two_pow_pos 256) ω))).1
      have hPB2 := tower128_pad_shift_B hRealZ2 hSimZ2 hOwnD2
        knownZpadA.2 (unpackTower128Pair (BitVec.ofFin (splitFinRight (Nat.two_pow_pos 256) ω))).2
      rw [hOwnAnd, hOwnD1, hOwnD2, hInAnd, hPA1, hPA2, hPB1, hPB2]
    | ⟨1, hc⟩ =>
      dsimp only [rss256SimCorruptView, rss256_and_bgin19_privacy_equiv, rss256RealCorruptView]
      rw [hSplitL, hSplitR, unpackTower128Pair_xor_pack]
      dsimp only [rss256AndWireCorrected]
      have hOwnAnd : (rss256CrossTerms (rss256SimDummyInputs ⟨1, hc⟩ x y w).1
                                       (rss256SimDummyInputs ⟨1, hc⟩ x y w).2.1).1 =
                     (rss256CrossTerms x y).1 := rfl
      have hOwnD1 : (bgin19UnmaskedCoeffShares (rss256SimDummyInputs ⟨1, hc⟩ x y w).2.2).1.s0 =
                    (bgin19UnmaskedCoeffShares w).1.s0 := rfl
      have hOwnD2 : (bgin19UnmaskedCoeffShares (rss256SimDummyInputs ⟨1, hc⟩ x y w).2.2).2.s0 =
                    (bgin19UnmaskedCoeffShares w).2.s0 := rfl
      have hInAnd := bv_xor_rearr (rss256CrossTerms x y).2.1
        (rss256CrossTerms (rss256SimDummyInputs ⟨1, hc⟩ x y w).1
                          (rss256SimDummyInputs ⟨1, hc⟩ x y w).2.1).2.1
        knownPrgB (BitVec.ofFin (splitFinLeft (Nat.two_pow_pos 256) ω))
      have hPA1 := tower128_pad_shift_A (bgin19UnmaskedCoeffShares w).1.s1
        (bgin19UnmaskedCoeffShares (rss256SimDummyInputs ⟨1, hc⟩ x y w).2.2).1.s1
        knownZpadB.1 (unpackTower128Pair (BitVec.ofFin (splitFinRight (Nat.two_pow_pos 256) ω))).1
      have hPA2 := tower128_pad_shift_A (bgin19UnmaskedCoeffShares w).2.s1
        (bgin19UnmaskedCoeffShares (rss256SimDummyInputs ⟨1, hc⟩ x y w).2.2).2.s1
        knownZpadB.2 (unpackTower128Pair (BitVec.ofFin (splitFinRight (Nat.two_pow_pos 256) ω))).2
      have hRealZ1' : towerAdd 7 (towerAdd 7 (bgin19UnmaskedCoeffShares w).1.s1
                        (bgin19UnmaskedCoeffShares w).1.s2) (bgin19UnmaskedCoeffShares w).1.s0 = towerZero 7 := by
        unfold RssTower128Share.reconstruct at hRealZ1
        simpa only [towerAdd_comm, towerAdd_left_comm] using hRealZ1
      have hSimZ1' : towerAdd 7 (towerAdd 7
                       (bgin19UnmaskedCoeffShares (rss256SimDummyInputs ⟨1, hc⟩ x y w).2.2).1.s1
                       (bgin19UnmaskedCoeffShares (rss256SimDummyInputs ⟨1, hc⟩ x y w).2.2).1.s2)
                       (bgin19UnmaskedCoeffShares (rss256SimDummyInputs ⟨1, hc⟩ x y w).2.2).1.s0 = towerZero 7 := by
        unfold RssTower128Share.reconstruct at hSimZ1
        simpa only [towerAdd_comm, towerAdd_left_comm] using hSimZ1
      have hRealZ2' : towerAdd 7 (towerAdd 7 (bgin19UnmaskedCoeffShares w).2.s1
                        (bgin19UnmaskedCoeffShares w).2.s2) (bgin19UnmaskedCoeffShares w).2.s0 = towerZero 7 := by
        unfold RssTower128Share.reconstruct at hRealZ2
        simpa only [towerAdd_comm, towerAdd_left_comm] using hRealZ2
      have hSimZ2' : towerAdd 7 (towerAdd 7
                       (bgin19UnmaskedCoeffShares (rss256SimDummyInputs ⟨1, hc⟩ x y w).2.2).2.s1
                       (bgin19UnmaskedCoeffShares (rss256SimDummyInputs ⟨1, hc⟩ x y w).2.2).2.s2)
                       (bgin19UnmaskedCoeffShares (rss256SimDummyInputs ⟨1, hc⟩ x y w).2.2).2.s0 = towerZero 7 := by
        unfold RssTower128Share.reconstruct at hSimZ2
        simpa only [towerAdd_comm, towerAdd_left_comm] using hSimZ2
      have hPB1 := tower128_pad_shift_B hRealZ1' hSimZ1' hOwnD1
        knownZpadA.1 (unpackTower128Pair (BitVec.ofFin (splitFinRight (Nat.two_pow_pos 256) ω))).1
      have hPB2 := tower128_pad_shift_B hRealZ2' hSimZ2' hOwnD2
        knownZpadA.2 (unpackTower128Pair (BitVec.ofFin (splitFinRight (Nat.two_pow_pos 256) ω))).2
      rw [hOwnAnd, hOwnD1, hOwnD2, hInAnd, hPA1, hPA2, hPB1, hPB2]
    | ⟨2, hc⟩ =>
      dsimp only [rss256SimCorruptView, rss256_and_bgin19_privacy_equiv, rss256RealCorruptView]
      rw [hSplitL, hSplitR, unpackTower128Pair_xor_pack]
      dsimp only [rss256AndWireCorrected]
      have hOwnAnd : (rss256CrossTerms (rss256SimDummyInputs ⟨2, hc⟩ x y w).1
                                       (rss256SimDummyInputs ⟨2, hc⟩ x y w).2.1).2.1 =
                     (rss256CrossTerms x y).2.1 := rfl
      have hOwnD1 : (bgin19UnmaskedCoeffShares (rss256SimDummyInputs ⟨2, hc⟩ x y w).2.2).1.s1 =
                    (bgin19UnmaskedCoeffShares w).1.s1 := rfl
      have hOwnD2 : (bgin19UnmaskedCoeffShares (rss256SimDummyInputs ⟨2, hc⟩ x y w).2.2).2.s1 =
                    (bgin19UnmaskedCoeffShares w).2.s1 := rfl
      have hInAnd := bv_xor_rearr (rss256CrossTerms x y).2.2
        (rss256CrossTerms (rss256SimDummyInputs ⟨2, hc⟩ x y w).1
                          (rss256SimDummyInputs ⟨2, hc⟩ x y w).2.1).2.2
        knownPrgB (BitVec.ofFin (splitFinLeft (Nat.two_pow_pos 256) ω))
      have hPA1 := tower128_pad_shift_A (bgin19UnmaskedCoeffShares w).1.s2
        (bgin19UnmaskedCoeffShares (rss256SimDummyInputs ⟨2, hc⟩ x y w).2.2).1.s2
        knownZpadB.1 (unpackTower128Pair (BitVec.ofFin (splitFinRight (Nat.two_pow_pos 256) ω))).1
      have hPA2 := tower128_pad_shift_A (bgin19UnmaskedCoeffShares w).2.s2
        (bgin19UnmaskedCoeffShares (rss256SimDummyInputs ⟨2, hc⟩ x y w).2.2).2.s2
        knownZpadB.2 (unpackTower128Pair (BitVec.ofFin (splitFinRight (Nat.two_pow_pos 256) ω))).2
      have hRealZ1' : towerAdd 7 (towerAdd 7 (bgin19UnmaskedCoeffShares w).1.s2
                        (bgin19UnmaskedCoeffShares w).1.s0) (bgin19UnmaskedCoeffShares w).1.s1 = towerZero 7 := by
        unfold RssTower128Share.reconstruct at hRealZ1
        simpa only [towerAdd_assoc, towerAdd_comm, towerAdd_left_comm] using hRealZ1
      have hSimZ1' : towerAdd 7 (towerAdd 7
                       (bgin19UnmaskedCoeffShares (rss256SimDummyInputs ⟨2, hc⟩ x y w).2.2).1.s2
                       (bgin19UnmaskedCoeffShares (rss256SimDummyInputs ⟨2, hc⟩ x y w).2.2).1.s0)
                       (bgin19UnmaskedCoeffShares (rss256SimDummyInputs ⟨2, hc⟩ x y w).2.2).1.s1 = towerZero 7 := by
        unfold RssTower128Share.reconstruct at hSimZ1
        simpa only [towerAdd_assoc, towerAdd_comm, towerAdd_left_comm] using hSimZ1
      have hRealZ2' : towerAdd 7 (towerAdd 7 (bgin19UnmaskedCoeffShares w).2.s2
                        (bgin19UnmaskedCoeffShares w).2.s0) (bgin19UnmaskedCoeffShares w).2.s1 = towerZero 7 := by
        unfold RssTower128Share.reconstruct at hRealZ2
        simpa only [towerAdd_assoc, towerAdd_comm, towerAdd_left_comm] using hRealZ2
      have hSimZ2' : towerAdd 7 (towerAdd 7
                       (bgin19UnmaskedCoeffShares (rss256SimDummyInputs ⟨2, hc⟩ x y w).2.2).2.s2
                       (bgin19UnmaskedCoeffShares (rss256SimDummyInputs ⟨2, hc⟩ x y w).2.2).2.s0)
                       (bgin19UnmaskedCoeffShares (rss256SimDummyInputs ⟨2, hc⟩ x y w).2.2).2.s1 = towerZero 7 := by
        unfold RssTower128Share.reconstruct at hSimZ2
        simpa only [towerAdd_assoc, towerAdd_comm, towerAdd_left_comm] using hSimZ2
      have hPB1 := tower128_pad_shift_B hRealZ1' hSimZ1' hOwnD1
        knownZpadA.1 (unpackTower128Pair (BitVec.ofFin (splitFinRight (Nat.two_pow_pos 256) ω))).1
      have hPB2 := tower128_pad_shift_B hRealZ2' hSimZ2' hOwnD2
        knownZpadA.2 (unpackTower128Pair (BitVec.ofFin (splitFinRight (Nat.two_pow_pos 256) ω))).2
      rw [hOwnAnd, hOwnD1, hOwnD2, hInAnd, hPA1, hPA2, hPB1, hPB2]
  have hPointwise : ∀ ω : Fin padCard, realExec ω = simExec (bij.toFun ω) := hPointwiseGen corrupt
  have hCountEq : qsum padCard (fun ω => if D (realExec ω) then 1 else 0) =
      qsum padCard (fun ω => if D (simExec ω) then 1 else 0) := by
    calc
      qsum padCard (fun ω => if D (realExec ω) then 1 else 0) =
        qsum padCard (fun ω => if D (simExec (bij.toFun ω)) then 1 else 0) :=
          qsum_congr (fun ω => by rw [hPointwise ω])
      _ = qsum padCard (fun ω => if D (simExec ω) then 1 else 0) :=
          qsum_perm_invariant bij.toFun bij.invFun bij.left_inv bij.right_inv
            (fun ω => if D (simExec ω) then 1 else 0)
  exact ⟨hPointwise, hCountEq⟩

/-- Verifier `P0`'s pad-cancellation extractor against the naive `(prg0, prg1, prg2)` assignment. -/
def p0CancelNaivePads (u0Naive x0 y0 prg0 prg1 : Plane256) : Plane256 :=
  u0Naive ^^^ prg0 ^^^ prg1 ^^^ (x0 &&& y0)

/-- **`#tooth` Off-by-One `(prg0, prg1, prg2)` Mask-Key Assignment Leaks `(x0 & y1) ⊕ (x1 & y0)` (`tooth_off_by_one_prg_map_leaks_and_wire`)**:
    Under the naive `(prg0, prg1, prg2)` assignment, gate reconstruction STILL passes (`u0 ⊕ u1 ⊕ u2 = x & y`),
    yet verifier `P0` (holding `(x2, x0, y2, y0)` and `(prg0, prg1)`) cancels BOTH pads on `u0` and
    recovers `(x0 &&& y1) ^^^ (x1 &&& y0)` with probability `1` (`distAcceptCount` difference = `2^256`)! -/
theorem tooth_off_by_one_prg_map_leaks_and_wire
    (x y : RssPlane256Share) (prg0 prg1 prg2 : Plane256) :
    let uNaive := rss256AndWireNaiveOffByOne x y prg0 prg1 prg2
    uNaive.reconstruct = (x.reconstruct &&& y.reconstruct) ∧
    p0CancelNaivePads uNaive.s0 x.s0 y.s0 prg0 prg1 =
      ((x.s0 &&& y.s1) ^^^ (x.s1 &&& y.s0)) ∧
    (let xA : RssPlane256Share := { s0 := 0#256, s1 := BitVec.allOnes 256, s2 := 0#256 }
     let xB : RssPlane256Share := { s0 := 0#256, s1 := 0#256, s2 := 0#256 }
     let yFixed : RssPlane256Share := { s0 := BitVec.allOnes 256, s1 := 0#256, s2 := 0#256 }
     xA.s0 = xB.s0 ∧ xA.s2 = xB.s2 ∧
     qsum (2 ^ 256) (fun ω =>
       if p0CancelNaivePads
            (rss256AndWireNaiveOffByOne xA yFixed prg0 prg1 (BitVec.ofFin ω)).s0
            xA.s0 yFixed.s0 prg0 prg1 == BitVec.allOnes 256 then 1 else 0) = 2 ^ 256 ∧
     qsum (2 ^ 256) (fun ω =>
       if p0CancelNaivePads
            (rss256AndWireNaiveOffByOne xB yFixed prg0 prg1 (BitVec.ofFin ω)).s0
            xB.s0 yFixed.s0 prg0 prg1 == BitVec.allOnes 256 then 1 else 0) = 0) := by
  refine ⟨(rss256_and_gate_reconstructs x y prg0 prg1 prg2).2, ?_, ?_⟩
  · apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp only [p0CancelNaivePads, rss256AndWireNaiveOffByOne, rss256CrossTerms,
      BitVec.getLsbD_xor, BitVec.getLsbD_and]
    cases x.s0.getLsbD i <;> cases x.s1.getLsbD i <;>
      cases y.s0.getLsbD i <;> cases y.s1.getLsbD i <;>
      cases prg0.getLsbD i <;> cases prg1.getLsbD i <;> rfl
  · dsimp only
    have hExtractEq : ∀ (u : RssPlane256Share) (p2 : Plane256),
        p0CancelNaivePads (rss256AndWireNaiveOffByOne u { s0 := BitVec.allOnes 256, s1 := 0#256, s2 := 0#256 } prg0 prg1 p2).s0
          u.s0 (BitVec.allOnes 256) prg0 prg1 =
        (u.s1 &&& BitVec.allOnes 256) := by
      intro u p2
      apply BitVec.eq_of_getLsbD_eq
      intro i _
      simp only [p0CancelNaivePads, rss256AndWireNaiveOffByOne, rss256CrossTerms,
        BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_zero]
      cases u.s0.getLsbD i <;> cases u.s1.getLsbD i <;>
        cases (BitVec.allOnes 256).getLsbD i <;>
        cases prg0.getLsbD i <;> cases prg1.getLsbD i <;> rfl
    refine ⟨rfl, rfl, ?_, ?_⟩
    · have h1 : qsum (2 ^ 256) (fun ω =>
          if p0CancelNaivePads
               (rss256AndWireNaiveOffByOne { s0 := 0#256, s1 := BitVec.allOnes 256, s2 := 0#256 }
                 { s0 := BitVec.allOnes 256, s1 := 0#256, s2 := 0#256 } prg0 prg1 (BitVec.ofFin ω)).s0
               0#256 (BitVec.allOnes 256) prg0 prg1 == BitVec.allOnes 256 then 1 else 0) =
          qsum (2 ^ 256) (fun _ => 1) := by
        apply qsum_congr
        intro ω
        rw [hExtractEq { s0 := 0#256, s1 := BitVec.allOnes 256, s2 := 0#256 } (BitVec.ofFin ω)]
        simp
      rw [h1, qsum_const, Nat.mul_one]
    · have h0 : qsum (2 ^ 256) (fun ω =>
          if p0CancelNaivePads
               (rss256AndWireNaiveOffByOne { s0 := 0#256, s1 := 0#256, s2 := 0#256 }
                 { s0 := BitVec.allOnes 256, s1 := 0#256, s2 := 0#256 } prg0 prg1 (BitVec.ofFin ω)).s0
               0#256 (BitVec.allOnes 256) prg0 prg1 == BitVec.allOnes 256 then 1 else 0) =
          qsum (2 ^ 256) (fun _ => 0) := by
        apply qsum_congr
        intro ω
        rw [hExtractEq { s0 := 0#256, s1 := 0#256, s2 := 0#256 } (BitVec.ofFin ω)]
        dsimp only
        have hNeOnes : ((0#256 &&& BitVec.allOnes 256) == BitVec.allOnes 256) = false := by
          apply beq_false_of_ne
          intro hEq
          have hb := congrArg (fun v : BitVec 256 => v.getLsbD 0) hEq
          rw [BitVec.zero_and, BitVec.getLsbD_zero, Qsag.Constructive.getLsbD_allOnes] at hb
          cases hb
        rw [hNeOnes]
        rfl
      rw [h0, qsum_const, Nat.mul_zero]

private theorem qsum_mul_right_nat : ∀ (n c : Nat) (f : Fin n → Nat),
    qsum n (fun i => f i * c) = qsum n f * c
  | 0, _, _ => by simp [qsum_zero]
  | n + 1, c, f => by simp only [qsum_succ, qsum_mul_right_nat n c, Nat.add_mul]

/-- A full recorded AND gate, with three replicated-share components per wire. -/
structure Rss256RecordedGate where
  x : RssPlane256Share
  y : RssPlane256Share
  z : RssPlane256Share

/-- Actual reconstructed gate error, rather than a caller-supplied validity flag. -/
def Rss256RecordedGate.error (g : Rss256RecordedGate) : Plane256 :=
  g.z.reconstruct ^^^ (g.x.reconstruct &&& g.y.reconstruct)

/-- Each party holds two adjacent shares; these overlap exactly as in `(2,3)` RSS. -/
def RssPlane256Share.partyViews (s : RssPlane256Share) :
    (Plane256 × Plane256) × (Plane256 × Plane256) × (Plane256 × Plane256) :=
  ((s.s2, s.s0), (s.s0, s.s1), (s.s1, s.s2))

theorem rss256_replicated_share_binding (s : RssPlane256Share) :
    s.partyViews.1.2 = s.partyViews.2.1.1 ∧
    s.partyViews.2.1.2 = s.partyViews.2.2.1 ∧
    s.partyViews.2.2.2 = s.partyViews.1.1 ∧
    s.partyViews.1.1 ^^^ s.partyViews.1.2 ^^^ s.partyViews.2.1.2 = s.reconstruct := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [RssPlane256Share.partyViews, RssPlane256Share.reconstruct, BitVec.getLsbD_xor]
  cases s.s0.getLsbD i <;> cases s.s1.getLsbD i <;> cases s.s2.getLsbD i <;> rfl

theorem rss256_honest_recorded_gate_error (x y : RssPlane256Share) (a b c : Plane256) :
    (Rss256RecordedGate.mk x y (rss256AndWireCorrected x y a b c)).error = 0#256 := by
  unfold Rss256RecordedGate.error
  rw [(rss256_and_gate_reconstructs x y a b c).1, BitVec.xor_self]

/-- Independent-coordinate linear combination. Coins are indexed by gate/lane, never
    one scalar multiplied by the sum of all errors. A fresh stream is required per pass
    and per folding round; the transcript errors are fixed before that stream is sampled. -/
def rss256WeightedErrors : List Tower128 → (Nat → Tower128) → Tower128
  | [], _ => towerZero 7
  | e :: es, coins => towerAdd 7 (towerMul 7 e (coins 0))
      (rss256WeightedErrors es (fun i => coins (i + 1)))

/-- Expose one independently sampled coordinate, keeping all other coins fixed. -/
def rss256PivotCheck (delta : Tower128) (rest : List Tower128)
    (coins : Nat → Tower128) (r : Tower128) : Tower128 :=
  rss256WeightedErrors (delta :: rest) (fun i => if i = 0 then r else coins (i - 1))

theorem rss256PivotCheck_eq (delta : Tower128) (rest : List Tower128)
    (coins : Nat → Tower128) (r : Tower128) :
    rss256PivotCheck delta rest coins r =
      towerAdd 7 (towerMul 7 delta r) (rss256WeightedErrors rest coins) := by
  simp only [rss256PivotCheck, rss256WeightedErrors, ↓reduceIte,
    Nat.add_one_ne_zero, Nat.add_sub_cancel]

/-- Conditional on every other coin, a nonzero gate error pins at most one fresh
    GF(2^128) challenge. Thus independent gate weighting has error at most 1/2^128.
    The designated erroneous coordinate may be placed first in the batch. -/
theorem rss256_independent_gate_weight_soundness (delta : Tower128)
    (rest : List Tower128) (coins : Nat → Tower128) (hdelta : delta ≠ towerZero 7) :
    ratLe (qsum (2^128) (fun r =>
      if rss256PivotCheck delta rest coins (unpackTower 7 (BitVec.ofFin r)) == towerZero 7
      then 1 else 0), 2^128) (1, 2^128) := by
  have hCount : qsum (2^128) (fun r =>
      if rss256PivotCheck delta rest coins (unpackTower 7 (BitVec.ofFin r)) == towerZero 7
      then 1 else 0) ≤ 1 := by
    apply qsum_indicator_le_one_of_unique
    intro i j hi hj
    have hi' := eq_of_beq hi
    have hj' := eq_of_beq hj
    rw [rss256PivotCheck_eq] at hi' hj'
    have he := hi'.trans hj'.symm
    have hc := congrArg (fun v => towerAdd 7 v (rss256WeightedErrors rest coins)) he
    simp only [towerAdd_assoc, towerAdd_self_zero, towerAdd_zero] at hc
    have hf := towerMul_cancel_left 7 delta _ _ hdelta hc
    have hp := congrArg (packTower 7) hf
    simp only [packTower_unpackTower] at hp
    exact Fin.ext (congrArg BitVec.toNat hp)
  exact ⟨Nat.two_pow_pos 128, Nat.two_pow_pos 128,
    Nat.mul_le_mul_right (2^128) hCount⟩

/-- Encode every lane of every recorded gate; false lanes contribute the nonzero field
    element one. This binds the independent-coordinate check to the 256-lane RSS invariant. -/
def rss256GateErrors (gates : List Rss256RecordedGate) : List Tower128 :=
  gates.flatMap (fun g => (List.finRange 256).map (fun lane =>
    if g.error.getLsbD lane.val then towerOne 7 else towerZero 7))

def rss256Pass1Check (gates : List Rss256RecordedGate) (coins : Nat → Tower128) : Bool :=
  rss256WeightedErrors (rss256GateErrors gates) coins == towerZero 7

/-- Polynomial weighting (the production alternative to independently sampled gate
    coordinates) uses distinct monomials. In the existing Horner convention coefficient
    zero has weight chi, so the degree bound is the coefficient-list length. -/
theorem rss256_polynomial_gate_weight_soundness (deg : Nat) (errors : List Tower128)
    (hLen : errors.length ≤ deg) (hNz : ∃ e ∈ errors, e ≠ towerZero 7) :
    ratLe (qsum (2^128) (fun r =>
      if batchDeviationPoly errors (unpackTower 7 (BitVec.ofFin r)) == towerZero 7
      then 1 else 0), 2^128) (deg, 2^128) := by
  exact ⟨Nat.two_pow_pos 128, Nat.two_pow_pos 128,
    Nat.mul_le_mul_right (2^128) (tower128_roots_qsum_le deg errors hLen hNz)⟩

/-- A false bit of a reconstructed gate becomes an actual nonzero coefficient. -/
theorem rss256_recorded_fault_nonzero (gates : List Rss256RecordedGate)
    (g : Rss256RecordedGate) (hg : g ∈ gates) (lane : Fin 256)
    (hFault : g.error.getLsbD lane.val = true) :
    ∃ e ∈ rss256GateErrors gates, e ≠ towerZero 7 := by
  refine ⟨towerOne 7, ?_, towerOne_ne_zero 7⟩
  apply List.mem_flatMap.mpr
  refine ⟨g, hg, ?_⟩
  apply List.mem_map.mpr
  exact ⟨lane, List.mem_finRange lane, by rw [hFault]; rfl⟩

/-- End-to-end algebraic batching bound from an actual RSS gate/lane fault. This
    is the polynomial-weight variant; it does not assume a caller's `relationValid`. -/
theorem rss256_recorded_gate_polynomial_soundness (gates : List Rss256RecordedGate)
    (g : Rss256RecordedGate) (hg : g ∈ gates) (lane : Fin 256)
    (hFault : g.error.getLsbD lane.val = true) :
    ratLe (qsum (2^128) (fun r =>
      if batchDeviationPoly (rss256GateErrors gates)
        (unpackTower 7 (BitVec.ofFin r)) == towerZero 7 then 1 else 0), 2^128)
      ((rss256GateErrors gates).length, 2^128) :=
  rss256_polynomial_gate_weight_soundness _ _ (Nat.le_refl _)
    (rss256_recorded_fault_nonzero gates g hg lane hFault)

/-- Pass and round are separate coordinates. Uniform independent sampling of this
    family is the coin-model premise, not a claim that a deterministic XOF is random. -/
structure Rss256ChallengeFamily where
  gate : Fin 2 → Nat → Nat → Tower128
  evaluation : Fin 2 → Nat → Tower128

def rss256Pass1At (gates : List Rss256RecordedGate) (coins : Rss256ChallengeFamily)
    (pass : Fin 2) (round : Nat) : Bool :=
  rss256Pass1Check gates (coins.gate pass round)

/-- Each folding polynomial must be fixed before its own evaluation coin is drawn.
    The bound is conditional on the preceding transcript, including earlier rounds. -/
theorem rss256_folding_round_soundness (deg : Nat) (errors : List Tower128)
    (hLen : errors.length ≤ deg) (hNz : ∃ e ∈ errors, e ≠ towerZero 7) :
    ratLe (qsum (2^128) (fun r =>
      if batchDeviationPoly errors (unpackTower 7 (BitVec.ofFin r)) == towerZero 7
      then 1 else 0), 2^128) (deg, 2^128) :=
  rss256_polynomial_gate_weight_soundness deg errors hLen hNz

/-- `#tooth`: identical weights erase two equal nonzero gate errors in characteristic 2. -/
theorem tooth_rss256_reused_gate_weights (c : Tower128) :
    towerOne 7 ≠ towerZero 7 ∧
    rss256WeightedErrors [towerOne 7, towerOne 7] (fun _ => c) = towerZero 7 := by
  constructor
  · exact towerOne_ne_zero 7
  · simp only [rss256WeightedErrors, towerAdd_zero, towerAdd_self_zero]

/-- Post-wave 2-challenge `GF(2^{128})` (`Tower128`) check predicate over `Fin ((2 ^ 128) * (2 ^ 128))`. -/
def postWaveTwoChallengeAccepts (waveCoeffs : List Tower128)
    (ω : Fin ((2 ^ 128) * (2 ^ 128))) : Bool :=
  let chi1 := unpackTower 7 (BitVec.ofFin (splitFinLeft (Nat.two_pow_pos 128) ω))
  let chi2 := unpackTower 7 (BitVec.ofFin (splitFinRight (Nat.two_pow_pos 128) ω))
  (batchDeviationPoly waveCoeffs chi1 == towerZero 7) &&
  (batchDeviationPoly waveCoeffs chi2 == towerZero 7)

/-- **Post-Wave Commit-Reveal 2-Challenge `GF(2^{128})` `BGIN19` / Horner Soundness
    (`rss256_post_wave_two_challenge_bgin19_soundness`)**:
    When the joint commit-then-open coin flip runs *after* the wave gate/Horner transcript
    `waveCoeffs` (of degree `≤ 2 * deg` with at least one nonzero error coefficient) is committed,
    both independent `GF(2^{128})` challenges accept on at most `(2 * deg) ^ 2` pairs out of
    `(2 ^ 128) ^ 2`, establishing `ratLe (acceptCount, (2 ^ 128) ^ 2) ((2 * deg) ^ 2, (2 ^ 128) ^ 2)`. -/
theorem rss256_post_wave_two_challenge_bgin19_soundness
    (deg : Nat) (waveCoeffs : List Tower128)
    (hDeg : waveCoeffs.length ≤ 2 * deg)
    (hNonzero : ∃ c ∈ waveCoeffs, c ≠ towerZero 7) :
    let acceptCount := qsum ((2 ^ 128) * (2 ^ 128))
      (fun ω => if postWaveTwoChallengeAccepts waveCoeffs ω then 1 else 0)
    acceptCount ≤ (2 * deg) ^ 2 ∧
    ratLe (acceptCount, (2 ^ 128) ^ 2) ((2 * deg) ^ 2, (2 ^ 128) ^ 2) := by
  intro acceptCount
  let pass1 : Fin (2 ^ 128) → Bool :=
    fun r => batchDeviationPoly waveCoeffs (unpackTower 7 (BitVec.ofFin r)) == towerZero 7
  have hSingle : qsum (2 ^ 128) (fun r => if pass1 r then 1 else 0) ≤ 2 * deg :=
    tower128_roots_qsum_le (2 * deg) waveCoeffs hDeg hNonzero
  have hFactor :
      acceptCount =
      (qsum (2 ^ 128) (fun r => if pass1 r then 1 else 0)) *
      (qsum (2 ^ 128) (fun r => if pass1 r then 1 else 0)) := by
    dsimp only [acceptCount]
    rw [qsum_prod_eq (2 ^ 128) (2 ^ 128)]
    have hInner : ∀ r1 : Fin (2 ^ 128),
        qsum (2 ^ 128) (fun r2 => if postWaveTwoChallengeAccepts waveCoeffs (pairFin r1 r2) then 1 else 0) =
        (if pass1 r1 then 1 else 0) * qsum (2 ^ 128) (fun r2 => if pass1 r2 then 1 else 0) := by
      intro r1
      have hPt : ∀ r2 : Fin (2 ^ 128),
          (if postWaveTwoChallengeAccepts waveCoeffs (pairFin r1 r2) then 1 else 0) =
          (if pass1 r1 then 1 else 0) * (if pass1 r2 then 1 else 0) := by
        intro r2
        unfold postWaveTwoChallengeAccepts
        rw [splitFinLeft_pairFin (Nat.two_pow_pos 128), splitFinRight_pairFin (Nat.two_pow_pos 128)]
        change (if pass1 r1 && pass1 r2 then 1 else 0) = (if pass1 r1 then 1 else 0) * (if pass1 r2 then 1 else 0)
        cases pass1 r1 <;> cases pass1 r2 <;> rfl
      rw [qsum_congr hPt, qsum_mul_left]
    rw [qsum_congr hInner, qsum_mul_right_nat]
  have hSqLe : acceptCount ≤ (2 * deg) ^ 2 := by
    rw [hFactor, Nat.pow_two]
    exact Nat.mul_le_mul hSingle hSingle
  have hDenPos : 0 < (2 ^ 128) ^ 2 := by
    rw [Nat.pow_two]
    exact Nat.mul_pos (Nat.two_pow_pos 128) (Nat.two_pow_pos 128)
  refine ⟨hSqLe, hDenPos, hDenPos, Nat.mul_le_mul_right ((2 ^ 128) ^ 2) hSqLe⟩

/-- Rushing attacker's nonzero fault pair `(e1, e2) = (χ, 1) ∈ ker(χ)` when `χ` is leaked pre-wave. -/
def preWaveKernelFaultPair (chi : Tower128) : List Tower128 :=
  [chi, towerOne 7]

/-- Rushing attacker's nonzero 3-term fault `[χ1 * χ2, χ1 ⊕ χ2, 1]` annihilating BOTH pre-wave challenges `(χ1, χ2)`. -/
def preWaveTwoChallengeKernelFault (chi1 chi2 : Tower128) : List Tower128 :=
  [towerMul 7 chi1 chi2, towerAdd 7 chi1 chi2, towerOne 7]

/-- **`#tooth` Pre-Wave Challenge Kernel Bypass (`tooth_pre_wave_challenge_kernel_bypass`)**:
    If a rushing attacker learns `χ` before committing gate wire messages `u`, the explicit nonzero
    fault pair `(e1, e2) = (χ, 1)` (`e2 = 1 ≠ 0`) lies in `ker(χ)` (`batchDeviationPoly [χ, 1] χ = 0`)
    and passes verification on **100% of `Fin (2 ^ 128)`** (probability `1`), and similarly
    `preWaveTwoChallengeKernelFault χ1 χ2` passes BOTH challenges on **100% of `Fin ((2 ^ 128) ^ 2)`**! -/
theorem tooth_pre_wave_challenge_kernel_bypass :
    (∀ chi : Tower128,
      (∃ e ∈ preWaveKernelFaultPair chi, e ≠ towerZero 7) ∧
      batchDeviationPoly (preWaveKernelFaultPair chi) chi = towerZero 7) ∧
    qsum (2 ^ 128) (fun r =>
      let chi := unpackTower 7 (BitVec.ofFin r)
      if batchDeviationPoly (preWaveKernelFaultPair chi) chi == towerZero 7 then 1 else 0) = 2 ^ 128 ∧
    (∀ chi1 chi2 : Tower128,
      (∃ e ∈ preWaveTwoChallengeKernelFault chi1 chi2, e ≠ towerZero 7) ∧
      batchDeviationPoly (preWaveTwoChallengeKernelFault chi1 chi2) chi1 = towerZero 7 ∧
      batchDeviationPoly (preWaveTwoChallengeKernelFault chi1 chi2) chi2 = towerZero 7) ∧
    qsum ((2 ^ 128) * (2 ^ 128)) (fun ω =>
      let chi1 := unpackTower 7 (BitVec.ofFin (splitFinLeft (Nat.two_pow_pos 128) ω))
      let chi2 := unpackTower 7 (BitVec.ofFin (splitFinRight (Nat.two_pow_pos 128) ω))
      if postWaveTwoChallengeAccepts (preWaveTwoChallengeKernelFault chi1 chi2) ω then 1 else 0) =
      (2 ^ 128) * (2 ^ 128) := by
  have hOneEv : ∀ chi : Tower128, batchDeviationPoly (preWaveKernelFaultPair chi) chi = towerZero 7 := by
    intro chi
    change towerAdd 7 (towerZero 7)
      (towerMul 7 chi (towerAdd 7 chi (towerMul 7 chi (towerAdd 7 (towerOne 7) (towerMul 7 chi (towerZero 7)))))) =
      towerZero 7
    simp only [towerMul_zero, towerAdd_zero, towerMul_one, towerAdd_self_zero]
  have hTwoEv1 : ∀ chi1 chi2 : Tower128,
      batchDeviationPoly (preWaveTwoChallengeKernelFault chi1 chi2) chi1 = towerZero 7 := by
    intro chi1 chi2
    change towerAdd 7 (towerZero 7)
      (towerMul 7 chi1
        (towerAdd 7 (towerMul 7 chi1 chi2)
          (towerMul 7 chi1
            (towerAdd 7 (towerAdd 7 chi1 chi2)
              (towerMul 7 chi1 (towerAdd 7 (towerOne 7) (towerMul 7 chi1 (towerZero 7)))))))) =
      towerZero 7
    simp only [towerMul_zero, towerAdd_zero, towerMul_one, towerZero_add, towerMul_add_distrib]
    simp only [towerAdd_comm, towerAdd_self_zero, towerAdd_cancel]
  have hTwoEv2 : ∀ chi1 chi2 : Tower128,
      batchDeviationPoly (preWaveTwoChallengeKernelFault chi1 chi2) chi2 = towerZero 7 := by
    intro chi1 chi2
    have hSwap : preWaveTwoChallengeKernelFault chi1 chi2 = preWaveTwoChallengeKernelFault chi2 chi1 := by
      unfold preWaveTwoChallengeKernelFault
      rw [towerMul_comm 7 chi1 chi2, towerAdd_comm 7 chi1 chi2]
    rw [hSwap]
    exact hTwoEv1 chi2 chi1
  have hTwoAccept : ∀ (c1 c2 : Tower128) (ω : Fin ((2 ^ 128) * (2 ^ 128))),
      c1 = unpackTower 7 (BitVec.ofFin (splitFinLeft (Nat.two_pow_pos 128) ω)) →
      c2 = unpackTower 7 (BitVec.ofFin (splitFinRight (Nat.two_pow_pos 128) ω)) →
      postWaveTwoChallengeAccepts (preWaveTwoChallengeKernelFault c1 c2) ω = true := by
    intro c1 c2 ω hc1 hc2
    unfold postWaveTwoChallengeAccepts
    dsimp only
    rw [← hc1, ← hc2, hTwoEv1 c1 c2, hTwoEv2 c1 c2]
    simp only [beq_self_eq_true, Bool.and_self]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro chi
    exact ⟨⟨towerOne 7, .tail _ (.head _), towerOne_ne_zero 7⟩, hOneEv chi⟩
  · have hAll1 : qsum (2 ^ 128) (fun r =>
        let chi := unpackTower 7 (BitVec.ofFin r)
        if batchDeviationPoly (preWaveKernelFaultPair chi) chi == towerZero 7 then 1 else 0) =
        qsum (2 ^ 128) (fun _ => 1) := by
      apply qsum_congr
      intro r
      dsimp only
      rw [hOneEv (unpackTower 7 (BitVec.ofFin r))]
      simp only [beq_self_eq_true, ↓reduceIte]
    rw [hAll1, qsum_const, Nat.mul_one]
  · intro chi1 chi2
    exact ⟨⟨towerOne 7, .tail _ (.tail _ (.head _)), towerOne_ne_zero 7⟩,
           hTwoEv1 chi1 chi2, hTwoEv2 chi1 chi2⟩
  · have hAll2 : qsum ((2 ^ 128) * (2 ^ 128)) (fun ω =>
        let chi1 := unpackTower 7 (BitVec.ofFin (splitFinLeft (Nat.two_pow_pos 128) ω))
        let chi2 := unpackTower 7 (BitVec.ofFin (splitFinRight (Nat.two_pow_pos 128) ω))
        if postWaveTwoChallengeAccepts (preWaveTwoChallengeKernelFault chi1 chi2) ω then 1 else 0) =
        qsum ((2 ^ 128) * (2 ^ 128)) (fun _ => 1) := by
      apply qsum_congr
      intro ω
      have hAcc := hTwoAccept
        (unpackTower 7 (BitVec.ofFin (splitFinLeft (Nat.two_pow_pos 128) ω)))
        (unpackTower 7 (BitVec.ofFin (splitFinRight (Nat.two_pow_pos 128) ω)))
        ω rfl rfl
      dsimp only
      rw [hAcc]
      rfl
    rw [hAll2, qsum_const, Nat.mul_one]

/-- Boolean barrier abstraction used only for the historical sticky-poison counterexample.
    Operational inputs are defined by `Rss256EngineOp` below. -/
structure Rss256BarrierState where
  unverified : Bool
  poisoned : Bool
  pendingInlineValid : List Bool
  pendingOpenedValid : List Bool
  sharedPlane : Plane256
  taintedSinceLastCleanCheck : Bool
  deriving DecidableEq, Repr

def Rss256BarrierState.init : Rss256BarrierState :=
  { unverified := false
    poisoned := false
    pendingInlineValid := []
    pendingOpenedValid := []
    sharedPlane := 0
    taintedSinceLastCleanCheck := false }

inductive Rss256BarrierOp where
  | permuteInline (relationValid : Bool) (outPlane : Plane256)
  | permuteBank (openingConsistent : Bool) (outPlane : Plane256)
  | check
  | openPlanes
  deriving DecidableEq, Repr

inductive Rss256EngineErr where
  | enginePoisoned
  | multiplicationCheckFailed
  | openingConsistencyFailed
  | openBeforeCheck
  deriving DecidableEq, Repr

/-- Result of one `Rss256Engine` call. A rejected call also returns the next persistent state
    (the poison latch is written on the error path). -/
inductive Rss256StepOutcome (S Out : Type) where
  | ok (nextState : S) (output : Out)
  | err (nextState : S) (error : Rss256EngineErr)

/-- **Hardened `Rss256Engine` Transition (`rss256BarrierStep`)**:
    Every cryptographic barrier failure irreversibly latches `poisoned = true` and wipes state;
    every operation rejects a poisoned engine. -/
@[expose] def rss256BarrierStep (st : Rss256BarrierState) (op : Rss256BarrierOp) :
    Rss256StepOutcome Rss256BarrierState (Option Plane256) :=
  if st.poisoned then
    .err st .enginePoisoned
  else
    let poisonNow : Rss256BarrierState :=
      { st with
        poisoned := true
        pendingInlineValid := []
        pendingOpenedValid := []
        sharedPlane := 0 }
    match op with
    | .permuteInline relOk outPlane =>
      .ok { st with
            unverified := true
            pendingInlineValid := relOk :: st.pendingInlineValid
            sharedPlane := outPlane
            taintedSinceLastCleanCheck := st.taintedSinceLastCleanCheck || !relOk } none
    | .permuteBank openOk outPlane =>
      .ok { st with
            unverified := true
            pendingOpenedValid := openOk :: st.pendingOpenedValid
            sharedPlane := outPlane
            taintedSinceLastCleanCheck := st.taintedSinceLastCleanCheck || !openOk } none
    | .check =>
      if !st.unverified then
        .ok st none
      else if st.pendingInlineValid.any (fun b => !b) then
        .err poisonNow .multiplicationCheckFailed
      else if st.pendingOpenedValid.any (fun b => !b) then
        .err poisonNow .openingConsistencyFailed
      else
        .ok { st with
              unverified := false
              pendingInlineValid := []
              pendingOpenedValid := []
              taintedSinceLastCleanCheck := false } none
    | .openPlanes =>
      if st.unverified then
        .err st .openBeforeCheck
      else
        .ok st (some st.sharedPlane)

/-- The hardened `Rss256Engine` as a `Spec.Machine` started at `Rss256BarrierState.init`:
    an accepted call is a `step`, a rejected call updates the state through `errStep`. -/
def rss256BarrierMachine :
    Spec.Machine Rss256BarrierState Rss256BarrierOp (Option Plane256) where
  Init st := st = Rss256BarrierState.init
  step st op :=
    match rss256BarrierStep st op with
    | .ok st' out => some (st', out)
    | .err _ _ => none
  errStep st op :=
    match rss256BarrierStep st op with
    | .ok st' _ => st'
    | .err st' _ => st'

/-- Buggy pre-fix `Rss256Engine` transition:
    clears `pendingInlineValid` / `pendingOpenedValid` on `check()` BEFORE returning `Err`,
    without latching `poisoned = true`! -/
def rss256StepBuggy (st : Rss256BarrierState) (op : Rss256BarrierOp) :
    Rss256StepOutcome Rss256BarrierState (Option Plane256) :=
  match op with
  | .permuteInline relOk outPlane =>
    .ok { st with
          unverified := true
          pendingInlineValid := relOk :: st.pendingInlineValid
          sharedPlane := outPlane
          taintedSinceLastCleanCheck := st.taintedSinceLastCleanCheck || !relOk } none
  | .permuteBank openOk outPlane =>
    .ok { st with
          unverified := true
          pendingOpenedValid := openOk :: st.pendingOpenedValid
          sharedPlane := outPlane
          taintedSinceLastCleanCheck := st.taintedSinceLastCleanCheck || !openOk } none
  | .check =>
    if !st.unverified then
      .ok st none
    else
      -- `verify_rss_boolean_triples_seeded` clears `pending` unconditionally before returning!
      let inlineFailed := st.pendingInlineValid.any (fun b => !b)
      let stAfterInline := { st with pendingInlineValid := [] }
      if inlineFailed then
        .err stAfterInline .multiplicationCheckFailed
      else
        -- Mode-1A clears `self.opened` before returning `OpeningConsistencyFailed`!
        let openedFailed := stAfterInline.pendingOpenedValid.any (fun b => !b)
        let stAfterOpened := { stAfterInline with pendingOpenedValid := [] }
        if openedFailed then
          .err stAfterOpened .openingConsistencyFailed
        else
          .ok { stAfterOpened with unverified := false } none
  | .openPlanes =>
    if st.unverified then
      .err st .openBeforeCheck
    else
      .ok st (some st.sharedPlane)

/-- Run a multi-step call sequence and record `(finalState, releasedPlanes, stepOutcomes)`. -/
def rss256BarrierTrace (stepFn : Rss256BarrierState → Rss256BarrierOp →
      Rss256StepOutcome Rss256BarrierState (Option Plane256)) :
    Rss256BarrierState → List Rss256BarrierOp → Rss256BarrierState × List Plane256
  | st, [] => (st, [])
  | st, op :: rest =>
    match stepFn st op with
    | .ok st' (some p) =>
      let (stFinal, ps) := rss256BarrierTrace stepFn st' rest
      (stFinal, p :: ps)
    | .ok st' none => rss256BarrierTrace stepFn st' rest
    | .err st' _ => rss256BarrierTrace stepFn st' rest

/-- Data-bearing entry point: the pending result is computed from every recorded
    share relation under the two pass-specific coin streams. -/
def rss256RecordedWaveOp (gates : List Rss256RecordedGate)
    (coins : Rss256ChallengeFamily) (round : Nat) : Rss256BarrierOp :=
  .permuteInline (rss256Pass1At gates coins ⟨0, by decide⟩ round &&
    rss256Pass1At gates coins ⟨1, by decide⟩ round)
    (gates.foldl (fun _ g => g.z.reconstruct) 0#256)

theorem rss256_recorded_wave_rejection_poison (gates : List Rss256RecordedGate)
    (coins : Rss256ChallengeFamily) (round : Nat)
    (hReject : rss256Pass1At gates coins ⟨0, by decide⟩ round = false) :
    let result := rss256BarrierTrace rss256BarrierStep Rss256BarrierState.init
      [rss256RecordedWaveOp gates coins round, .check, .check, .openPlanes]
    result.1.poisoned = true ∧ result.2 = [] := by
  simp only [rss256RecordedWaveOp, hReject, Bool.false_and]
  exact ⟨rfl, rfl⟩

/-- Multi-turn invariant of `rss256BarrierStep`:
    if `taintedSinceLastCleanCheck = true` and `poisoned = false`, then `unverified = true` and at
    least one pending queue contains `false` (`any (!·) = true`). -/
def Rss256SafeInvariant (st : Rss256BarrierState) : Prop :=
  st.poisoned = true ∨
  (st.taintedSinceLastCleanCheck = false) ∨
  (st.unverified = true ∧
    (st.pendingInlineValid.any (fun b => !b) = true ∨
     st.pendingOpenedValid.any (fun b => !b) = true))

private theorem rss256BarrierStep_preserves_inv (st : Rss256BarrierState) (op : Rss256BarrierOp)
    (hInv : Rss256SafeInvariant st) :
    match rss256BarrierStep st op with
    | .ok st' (some _) => Rss256SafeInvariant st' ∧ st.taintedSinceLastCleanCheck = false ∧ st.poisoned = false
    | .ok st' none => Rss256SafeInvariant st'
    | .err st' _ => Rss256SafeInvariant st' ∧ (st'.poisoned = true ∨ st' = st) := by
  unfold rss256BarrierStep
  cases hp : st.poisoned
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hInvClean : st.taintedSinceLastCleanCheck = false ∨
        (st.unverified = true ∧
          (st.pendingInlineValid.any (fun b => !b) = true ∨
           st.pendingOpenedValid.any (fun b => !b) = true)) := by
      rcases hInv with hP | hRest
      · rw [hp] at hP; cases hP
      · exact hRest
    cases op with
    | permuteInline relOk outPlane =>
      dsimp only [Rss256SafeInvariant]
      cases relOk
      · right; right
        exact ⟨rfl, Or.inl (by simp)⟩
      · rcases hInvClean with hTaint0 | ⟨_, hAny⟩
        · right; left; simp [hTaint0]
        · right; right
          refine ⟨rfl, ?_⟩
          rcases hAny with hIn | hOp
          · exact Or.inl (by simp [hIn])
          · exact Or.inr hOp
    | permuteBank openOk outPlane =>
      dsimp only [Rss256SafeInvariant]
      cases openOk
      · right; right
        exact ⟨rfl, Or.inr (by simp)⟩
      · rcases hInvClean with hTaint0 | ⟨_, hAny⟩
        · right; left; simp [hTaint0]
        · right; right
          refine ⟨rfl, ?_⟩
          rcases hAny with hIn | hOp
          · exact Or.inl hIn
          · exact Or.inr (by simp [hOp])
    | check =>
      cases hUnv : st.unverified
      · simp only [Bool.not_false, ↓reduceIte]
        exact hInv
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        cases hInFail : st.pendingInlineValid.any (fun b => !b)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases hOpFail : st.pendingOpenedValid.any (fun b => !b)
          · simp only [Bool.false_eq_true, ↓reduceIte]
            exact Or.inr (Or.inl rfl)
          · simp only [↓reduceIte]
            exact ⟨Or.inl rfl, Or.inl trivial⟩
        · simp only [↓reduceIte]
          exact ⟨Or.inl rfl, Or.inl trivial⟩
    | openPlanes =>
      cases hUnv : st.unverified
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rcases hInvClean with hTaint0 | ⟨hUnvTrue, _⟩
        · exact ⟨hInv, hTaint0, trivial⟩
        · rw [hUnv] at hUnvTrue; cases hUnvTrue
      · simp only [↓reduceIte]
        exact ⟨hInv, Or.inr trivial⟩
  · simp only [↓reduceIte]
    exact ⟨Or.inl hp, Or.inl hp⟩

/-- **Sticky `poisoned = true` Terminal Absorption & Multi-Turn Anti-Fault Opening Safety
    (`rss256_sticky_poison_terminal_absorption`)**:
    1. **Terminal Absorption**: From ANY state with `st.poisoned = true`, across ANY call sequence
       `ops : List Rss256BarrierOp`, `poisoned` stays `true`, `rss256BarrierMachine.step` returns
       `none` on every step, and `rss256BarrierTrace` releases `[]` (`0` planes)!
    2. **Unverified/Faulted Wave Quarantine**: From `Rss256BarrierState.init`, across ANY sequence
       `ops` containing a faulted inline gate (`.permuteInline false _`) or inconsistent Mode-1A
       opening (`.permuteBank false _`), NO plane is ever released after that fault! -/
theorem rss256_sticky_poison_terminal_absorption :
    (∀ (st : Rss256BarrierState) (ops : List Rss256BarrierOp),
      st.poisoned = true →
      (∀ op : Rss256BarrierOp, rss256BarrierMachine.step st op = none) ∧
      (rss256BarrierTrace rss256BarrierStep st ops).1.poisoned = true ∧
      (rss256BarrierTrace rss256BarrierStep st ops).2 = []) ∧
    (∀ (st : Rss256BarrierState) (ops : List Rss256BarrierOp),
      Rss256SafeInvariant st →
      st.taintedSinceLastCleanCheck = true →
      (rss256BarrierTrace rss256BarrierStep st ops).2 = []) := by
  have hAbsorb : ∀ (st : Rss256BarrierState) (ops : List Rss256BarrierOp),
      st.poisoned = true →
      (rss256BarrierTrace rss256BarrierStep st ops).1.poisoned = true ∧
      (rss256BarrierTrace rss256BarrierStep st ops).2 = [] := by
    intro st ops hp
    induction ops generalizing st with
    | nil => exact ⟨hp, rfl⟩
    | cons op rest ih =>
      simp only [rss256BarrierTrace, rss256BarrierStep, hp, ↓reduceIte]
      exact ih st hp
  refine ⟨?_, ?_⟩
  · intro st ops hp
    refine ⟨fun op => by simp [rss256BarrierMachine, rss256BarrierStep, hp],
            (hAbsorb st ops hp).1, (hAbsorb st ops hp).2⟩
  · intro st ops hInv hTaint
    induction ops generalizing st with
    | nil => rfl
    | cons op rest ih =>
      have hStep := rss256BarrierStep_preserves_inv st op hInv
      cases hOut : rss256BarrierStep st op with
      | err st' errVal =>
        rw [hOut] at hStep
        simp only [rss256BarrierTrace, hOut]
        rcases hStep.2 with hPoison | hSame
        · exact (hAbsorb st' rest hPoison).2
        · subst st'
          exact ih st hStep.1 hTaint
      | ok st' mbPlane =>
        rw [hOut] at hStep
        cases mbPlane with
        | some p =>
          exfalso
          rw [hTaint] at hStep
          exact Bool.noConfusion hStep.2.1
        | none =>
          simp only [rss256BarrierTrace, hOut]
          -- Show `st'.taintedSinceLastCleanCheck = true` (since `op` was `.ok st' none` and `st` was tainted!).
          have hStillTainted : st'.taintedSinceLastCleanCheck = true := by
            unfold rss256BarrierStep at hOut
            cases hp : st.poisoned
            · rw [hp] at hOut; simp only [Bool.false_eq_true, ↓reduceIte] at hOut
              cases op with
              | permuteInline relOk outP =>
                injection hOut with hStEq _
                rw [← hStEq]; simp [hTaint]
              | permuteBank openOk outP =>
                injection hOut with hStEq _
                rw [← hStEq]; simp [hTaint]
              | check =>
                rcases hInv with hP | hT0 | ⟨hUnv, hAny⟩
                · rw [hp] at hP; cases hP
                · rw [hTaint] at hT0; cases hT0
                · simp only [hUnv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOut
                  rcases hAny with hIn | hOp
                  · rw [hIn] at hOut; simp at hOut
                  · cases hIn2 : st.pendingInlineValid.any (fun b => !b) <;>
                      simp [hIn2, hOp] at hOut
              | openPlanes =>
                cases hUnv : st.unverified <;> simp [hUnv] at hOut
            · rw [hp] at hOut; simp at hOut
          exact ih st' hStep hStillTainted

/-- **`#tooth` Non-Sticky `check()` Clear Unlocks Unverified Opening (`tooth_non_sticky_check_clear_unlocks_unverified_open`)**:
    In `rss256StepBuggy`, after a faulted inline wave (`.permuteInline false faultedPlane`) OR
    an inconsistent Mode-1A wave (`.permuteBank false faultedPlane`):
    - First `check()` returns `.err` after clearing `pending` / `opened`;
    - Second `check()` sees empty queues, sets `unverified = false`, and returns `.ok`;
    - `openPlanes()` then **succeeds and releases `[faultedPlane]`**, whereas `rss256BarrierStep`
      latches `poisoned = true` on the first `check()` and releases `[]`! -/
theorem tooth_non_sticky_check_clear_unlocks_unverified_open (faultedPlane : Plane256) :
    let inlineAttack : List Rss256BarrierOp :=
      [.permuteInline false faultedPlane, .check, .check, .openPlanes]
    let bankAttack : List Rss256BarrierOp :=
      [.permuteBank false faultedPlane, .check, .check, .openPlanes]
    (rss256BarrierTrace rss256StepBuggy Rss256BarrierState.init inlineAttack).2 = [faultedPlane] ∧
    (rss256BarrierTrace rss256StepBuggy Rss256BarrierState.init bankAttack).2 = [faultedPlane] ∧
    (rss256BarrierTrace rss256BarrierStep Rss256BarrierState.init inlineAttack).2 = [] ∧
    (rss256BarrierTrace rss256BarrierStep Rss256BarrierState.init bankAttack).2 = [] ∧
    (rss256BarrierTrace rss256BarrierStep Rss256BarrierState.init inlineAttack).1.poisoned = true ∧
    (rss256BarrierTrace rss256BarrierStep Rss256BarrierState.init bankAttack).1.poisoned = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 3. `Waistband` Canopy Top-`L` Static Child-Root Cache Soundness & `#tooth` Witnesses -/

/-- `Baggy` hypertree & `Waistband` canopy geometry (`topLayers < numLayers`, so layer `0` is dynamic). -/
structure BaggyTreeParams where
  numLayers : Nat
  subtreeHeight : Nat
  topLayers : Nat
  deriving DecidableEq, Repr

def BaggyTreeParams.WellFormed (p : BaggyTreeParams) : Prop :=
  2 ≤ p.numLayers ∧ 1 ≤ p.subtreeHeight ∧ p.topLayers < p.numLayers

def BaggyTreeParams.coversLayer (p : BaggyTreeParams) (layer : Nat) : Bool :=
  decide (p.numLayers ≤ layer + p.topLayers ∧ 1 ≤ layer)

def BaggyTreeParams.pathAt (p : BaggyTreeParams) (leafIdx : Nat) (layer : Nat) : Nat × Nat :=
  let shifted := leafIdx / (2 ^ (p.subtreeHeight * layer))
  let subLeaves := 2 ^ p.subtreeHeight
  (shifted % subLeaves, shifted / subLeaves)

/-- Child subtree index `(tree * 2^{h'} + kp)` signed by static leaf `(layer, tree, kp)` (`layer ≥ 1`). -/
def baggyChildTreeIdx (p : BaggyTreeParams) (tree kp : Nat) : Nat :=
  tree * (2 ^ p.subtreeHeight) + kp

theorem baggyChildTreeIdx_pathAt (p : BaggyTreeParams) (leafIdx layer : Nat) :
    let (kpParent, treeParent) := p.pathAt leafIdx (layer + 1)
    let (_, treeChild) := p.pathAt leafIdx layer
    baggyChildTreeIdx p treeParent kpParent = treeChild := by
  dsimp only [BaggyTreeParams.pathAt, baggyChildTreeIdx]
  have hPow : 2 ^ (p.subtreeHeight * (layer + 1)) = (2 ^ (p.subtreeHeight * layer)) * (2 ^ p.subtreeHeight) := by
    rw [Nat.mul_succ, Nat.pow_add]
  rw [hPow, ← Nat.div_div_eq_div_mul]
  let S := (leafIdx / (2 ^ (p.subtreeHeight * layer))) / (2 ^ p.subtreeHeight)
  let B := 2 ^ p.subtreeHeight
  change (S / B) * B + S % B = S
  rw [Nat.mul_comm (S / B) B]
  exact Nat.div_add_mod S B

structure BaggySecretKey256 where
  pkSeed : BitVec 256
  skSeed : BitVec 256
  skPrf : BitVec 256

structure BaggyPublicKey256 where
  pkSeed : BitVec 256
  pkRoot : BitVec 256
  deriving DecidableEq, Repr

/-- Tweakable hash & `FORS+C` suite for `Baggy` over 256-bit `WOTS+C` (`w = 4, v = 128, S = 192`). -/
structure BaggySuite256 where
  wots : WotsC256HashSuite
  thNodeH : BitVec 256 → Nat → Nat → Nat → Nat → BitVec 256 → BitVec 256 → BitVec 256
  paramsDigest : BaggyTreeParams → BitVec 256
  prfRand : BitVec 256 → BitVec 256 → BitVec 256
  hmsgLeaf : BaggyTreeParams → BaggyPublicKey256 → BitVec 256 → BitVec 256 → UInt32 → Option Nat
  forsSign : BitVec 256 → BitVec 256 → Nat → Nat → BitVec 256 → BitVec 256 × BitVec 256
  forsRecoverPk : BitVec 256 → Nat → Nat → BitVec 256 → BitVec 256 → BitVec 256
  /-- Deterministic valid `WOTS+C` grind counter (`wotsC256DecodeValidDigest ... = some d`). -/
  grindCounter : BitVec 256 → WotsLeafAdrs → BitVec 256 → UInt32

def BaggySuite256.WellGrinded (suite : BaggySuite256) : Prop :=
  (∀ pkSeed skSeed tree0 kp0 msg,
    let (forsSig, forsPk) := suite.forsSign pkSeed skSeed tree0 kp0 msg
    suite.forsRecoverPk pkSeed tree0 kp0 msg forsSig = forsPk) ∧
  (∀ pkSeed adrs node,
    (wotsC256DecodeValidDigest
      (suite.wots.thDigest pkSeed adrs node (suite.grindCounter pkSeed adrs node))).isSome = true)

/-- Binary Merkle subtree root over `2 ^ hp` leaves (`0 Classical.choice`). -/
def baggyMerkleRoot (suite : BaggySuite256) (pkSeed : BitVec 256) (layer tree : Nat) :
    (hp : Nat) → (prefixIdx : Nat) → (Fin (2 ^ hp) → BitVec 256) → BitVec 256
  | 0, _, leaves => leaves ⟨0, Nat.zero_lt_one⟩
  | hp + 1, prefixIdx, leaves =>
    let hHalf : 2 ^ hp + 2 ^ hp = 2 ^ (hp + 1) := by rw [Nat.pow_succ, Nat.mul_two]
    let left := baggyMerkleRoot suite pkSeed layer tree hp (2 * prefixIdx)
      (fun i => leaves ⟨i.val, by omega⟩)
    let right := baggyMerkleRoot suite pkSeed layer tree hp (2 * prefixIdx + 1)
      (fun i => leaves ⟨2 ^ hp + i.val, by omega⟩)
    suite.thNodeH pkSeed layer tree (hp + 1) prefixIdx left right

/-- Root-first authentication path of leaf `kp < 2 ^ hp` (`baggy.rs` / `wots_c.rs:307`). -/
def baggyMerkleAuthPath (suite : BaggySuite256) (pkSeed : BitVec 256) (layer tree : Nat) :
    (hp : Nat) → (prefixIdx : Nat) → (Fin (2 ^ hp) → BitVec 256) → (kp : Nat) → List (BitVec 256)
  | 0, _, _, _ => []
  | hp + 1, prefixIdx, leaves, kp =>
    let hHalf : 2 ^ hp + 2 ^ hp = 2 ^ (hp + 1) := by rw [Nat.pow_succ, Nat.mul_two]
    let leftFn : Fin (2 ^ hp) → BitVec 256 := fun i => leaves ⟨i.val, by omega⟩
    let rightFn : Fin (2 ^ hp) → BitVec 256 := fun i => leaves ⟨2 ^ hp + i.val, by omega⟩
    if kp < 2 ^ hp then
      baggyMerkleRoot suite pkSeed layer tree hp (2 * prefixIdx + 1) rightFn ::
        baggyMerkleAuthPath suite pkSeed layer tree hp (2 * prefixIdx) leftFn kp
    else
      baggyMerkleRoot suite pkSeed layer tree hp (2 * prefixIdx) leftFn ::
        baggyMerkleAuthPath suite pkSeed layer tree hp (2 * prefixIdx + 1) rightFn (kp - 2 ^ hp)

/-- Walk a root-first authentication path from `leaf` at `kp` up to the height-`hp` subtree root. -/
def baggyWalkMerkleRootFirst (suite : BaggySuite256) (pkSeed : BitVec 256) (layer tree : Nat) :
    (hp : Nat) → (prefixIdx : Nat) → (kp : Nat) → BitVec 256 → List (BitVec 256) → Option (BitVec 256)
  | 0, _, _, leaf, [] => some leaf
  | 0, _, _, _, _ :: _ => none
  | _ + 1, _, _, _, [] => none
  | hp + 1, prefixIdx, kp, leaf, sib :: rest =>
    if kp < 2 ^ hp then
      match baggyWalkMerkleRootFirst suite pkSeed layer tree hp (2 * prefixIdx) kp leaf rest with
      | none => none
      | some childL => some (suite.thNodeH pkSeed layer tree (hp + 1) prefixIdx childL sib)
    else
      match baggyWalkMerkleRootFirst suite pkSeed layer tree hp (2 * prefixIdx + 1) (kp - 2 ^ hp) leaf rest with
      | none => none
      | some childR => some (suite.thNodeH pkSeed layer tree (hp + 1) prefixIdx sib childR)

private theorem baggyWalkMerkle_authPath_eq (suite : BaggySuite256) (pkSeed : BitVec 256) (layer tree : Nat) :
    ∀ (hp prefixIdx : Nat) (leaves : Fin (2 ^ hp) → BitVec 256) (kp : Fin (2 ^ hp)),
      baggyWalkMerkleRootFirst suite pkSeed layer tree hp prefixIdx kp.val (leaves kp)
        (baggyMerkleAuthPath suite pkSeed layer tree hp prefixIdx leaves kp.val) =
      some (baggyMerkleRoot suite pkSeed layer tree hp prefixIdx leaves)
  | 0, _, leaves, ⟨0, _⟩ => rfl
  | 0, _, _, ⟨k + 1, hk⟩ => False.elim (Nat.not_lt_zero k (Nat.lt_of_succ_lt_succ hk))
  | hp + 1, prefixIdx, leaves, ⟨kp, hKp⟩ => by
    have hHalf : 2 ^ hp + 2 ^ hp = 2 ^ (hp + 1) := by rw [Nat.pow_succ, Nat.mul_two]
    simp only [baggyMerkleAuthPath, baggyMerkleRoot]
    if hLt : kp < 2 ^ hp then
      simp only [hLt, ↓reduceIte, baggyWalkMerkleRootFirst]
      have ih := baggyWalkMerkle_authPath_eq suite pkSeed layer tree hp (2 * prefixIdx)
        (fun i => leaves ⟨i.val, by have := i.isLt; omega⟩)
        ⟨kp, hLt⟩
      rw [ih]
    else
      simp only [hLt, ↓reduceIte, baggyWalkMerkleRootFirst]
      have hSubLt : kp - 2 ^ hp < 2 ^ hp := by omega
      have ih := baggyWalkMerkle_authPath_eq suite pkSeed layer tree hp (2 * prefixIdx + 1)
        (fun i => leaves ⟨2 ^ hp + i.val, by have := i.isLt; omega⟩)
        ⟨kp - 2 ^ hp, hSubLt⟩
      have hIdxEq : (⟨2 ^ hp + (kp - 2 ^ hp), by omega⟩ : Fin (2 ^ (hp + 1))) =
          ⟨kp, hKp⟩ := Fin.ext (Nat.add_sub_of_le (Nat.le_of_not_lt hLt))
      rw [hIdxEq] at ih
      rw [ih]

/-- Explicit Merkle node collision witness (`0 Classical.choice`). -/
structure BaggyMerkleCollision (suite : BaggySuite256) (pkSeed : BitVec 256) : Type where
  layer : Nat
  tree : Nat
  height : Nat
  prefixIdx : Nat
  left1 : BitVec 256
  right1 : BitVec 256
  left2 : BitVec 256
  right2 : BitVec 256
  pair_ne : (left1, right1) ≠ (left2, right2)
  hash_eq : suite.thNodeH pkSeed layer tree height prefixIdx left1 right1 =
            suite.thNodeH pkSeed layer tree height prefixIdx left2 right2

/-- Constructively extract a `BaggyMerkleCollision` whenever a walked path reaches the genuine root from a different leaf. -/
def extractBaggyMerkleCollision (suite : BaggySuite256) (pkSeed : BitVec 256) (layer tree : Nat) :
    ∀ (hp prefixIdx : Nat) (leaves : Fin (2 ^ hp) → BitVec 256) (kp : Fin (2 ^ hp))
      (leaf' : BitVec 256) (auth' : List (BitVec 256)),
      leaf' ≠ leaves kp →
      baggyWalkMerkleRootFirst suite pkSeed layer tree hp prefixIdx kp.val leaf' auth' =
        some (baggyMerkleRoot suite pkSeed layer tree hp prefixIdx leaves) →
      BaggyMerkleCollision suite pkSeed
  | 0, _, leaves, ⟨0, _⟩, leaf', [], hLeafNe, hWalk =>
    False.elim <| by
      simp only [baggyWalkMerkleRootFirst, baggyMerkleRoot] at hWalk
      injection hWalk with hEq
      exact hLeafNe hEq
  | 0, _, _, ⟨0, _⟩, _, _ :: _, _, hWalk => False.elim (by cases hWalk)
  | 0, _, _, ⟨k + 1, hk⟩, _, _, _, _ => False.elim (Nat.not_lt_zero k (Nat.lt_of_succ_lt_succ hk))
  | _ + 1, _, _, _, _, [], _, hWalk => False.elim (by cases hWalk)
  | hp + 1, prefixIdx, leaves, ⟨kp, hKp⟩, leaf', sib :: rest, hLeafNe, hWalk =>
    let hHalf : 2 ^ hp + 2 ^ hp = 2 ^ (hp + 1) := by rw [Nat.pow_succ, Nat.mul_two]
    let leftFn : Fin (2 ^ hp) → BitVec 256 := fun i => leaves ⟨i.val, by have := i.isLt; omega⟩
    let rightFn : Fin (2 ^ hp) → BitVec 256 := fun i => leaves ⟨2 ^ hp + i.val, by have := i.isLt; omega⟩
    let L := baggyMerkleRoot suite pkSeed layer tree hp (2 * prefixIdx) leftFn
    let R := baggyMerkleRoot suite pkSeed layer tree hp (2 * prefixIdx + 1) rightFn
    if hLt : kp < 2 ^ hp then
      match hChild : baggyWalkMerkleRootFirst suite pkSeed layer tree hp (2 * prefixIdx) kp leaf' rest with
      | none =>
        False.elim <| by
          simp only [baggyWalkMerkleRootFirst, hLt, ↓reduceIte, hChild] at hWalk
          cases hWalk
      | some childL =>
        have hRootEq : suite.thNodeH pkSeed layer tree (hp + 1) prefixIdx childL sib =
            suite.thNodeH pkSeed layer tree (hp + 1) prefixIdx L R := by
          simp only [baggyWalkMerkleRootFirst, baggyMerkleRoot, hLt, ↓reduceIte, hChild] at hWalk
          injection hWalk with hEq
        if hPairEq : (childL, sib) = (L, R) then
          extractBaggyMerkleCollision suite pkSeed layer tree hp (2 * prefixIdx) leftFn ⟨kp, hLt⟩
            leaf' rest hLeafNe (hChild.trans (congrArg (some ∘ Prod.fst) hPairEq))
        else
          { layer := layer, tree := tree, height := hp + 1, prefixIdx := prefixIdx
            left1 := childL, right1 := sib, left2 := L, right2 := R
            pair_ne := hPairEq, hash_eq := hRootEq }
    else
      match hChild : baggyWalkMerkleRootFirst suite pkSeed layer tree hp (2 * prefixIdx + 1) (kp - 2 ^ hp) leaf' rest with
      | none =>
        False.elim <| by
          simp only [baggyWalkMerkleRootFirst, hLt, ↓reduceIte, hChild] at hWalk
          cases hWalk
      | some childR =>
        have hRootEq : suite.thNodeH pkSeed layer tree (hp + 1) prefixIdx sib childR =
            suite.thNodeH pkSeed layer tree (hp + 1) prefixIdx L R := by
          simp only [baggyWalkMerkleRootFirst, baggyMerkleRoot, hLt, ↓reduceIte, hChild] at hWalk
          injection hWalk with hEq
        if hPairEq : (sib, childR) = (L, R) then
          have hSubLt : kp - 2 ^ hp < 2 ^ hp := by omega
          have hIdxEq : (⟨2 ^ hp + (kp - 2 ^ hp), by omega⟩ : Fin (2 ^ (hp + 1))) = ⟨kp, hKp⟩ :=
            Fin.ext (Nat.add_sub_of_le (Nat.le_of_not_lt hLt))
          have hLeafNeR : leaf' ≠ rightFn ⟨kp - 2 ^ hp, hSubLt⟩ := by
            dsimp [rightFn]; rw [hIdxEq]; exact hLeafNe
          extractBaggyMerkleCollision suite pkSeed layer tree hp (2 * prefixIdx + 1) rightFn
            ⟨kp - 2 ^ hp, hSubLt⟩ leaf' rest hLeafNeR
            (hChild.trans (congrArg (some ∘ Prod.snd) hPairEq))
        else
          { layer := layer, tree := tree, height := hp + 1, prefixIdx := prefixIdx
            left1 := sib, right1 := childR, left2 := L, right2 := R
            pair_ne := hPairEq, hash_eq := hRootEq }

def baggyLeafAdrs (layer tree kp : Nat) : WotsLeafAdrs :=
  { layer := UInt32.ofNat layer, tree := UInt64.ofNat tree, keyPair := UInt32.ofNat kp }

def baggySubtreeLeaves (suite : BaggySuite256) (p : BaggyTreeParams)
    (sk : BaggySecretKey256) (layer tree : Nat) : Fin (2 ^ p.subtreeHeight) → BitVec 256 :=
  fun kp => wotsC256PkLeaf suite.wots sk.pkSeed sk.skSeed (baggyLeafAdrs layer tree kp.val)

def baggyTrueSubtreeRoot (suite : BaggySuite256) (p : BaggyTreeParams)
    (sk : BaggySecretKey256) (layer tree : Nat) : BitVec 256 :=
  baggyMerkleRoot suite sk.pkSeed layer tree p.subtreeHeight 0 (baggySubtreeLeaves suite p sk layer tree)

def baggyKeygen256 (suite : BaggySuite256) (p : BaggyTreeParams) (sk : BaggySecretKey256) : BaggyPublicKey256 :=
  { pkSeed := sk.pkSeed
    pkRoot := baggyTrueSubtreeRoot suite p sk (p.numLayers - 1) 0 }

/-- Layer signature (`WOTS+C` counter + 128 chain nodes + height-`h'` authentication path). -/
structure BaggyLayerSig256 where
  ctr : UInt32
  chains : Fin 128 → BitVec 256
  auth : List (BitVec 256)

/-- Complete `Baggy` signature over 256-bit `WOTS+C`. -/
structure BaggySig256 where
  r : BitVec 256
  msgCtr : UInt32
  forsSig : BitVec 256
  layers : List BaggyLayerSig256

/-- Recompute the subtree root implied by `layerSig` signing `childNode` (`baggy.rs:313` `layer_root`). -/
def baggyLayerRecoverRoot (suite : BaggySuite256) (p : BaggyTreeParams)
    (pkSeed : BitVec 256) (layer tree kp : Nat) (childNode : BitVec 256)
    (sig : BaggyLayerSig256) : Option (BitVec 256) :=
  let adrs := baggyLeafAdrs layer tree kp
  match wotsC256DecodeValidDigest (suite.wots.thDigest pkSeed adrs childNode sig.ctr) with
  | none => none
  | some d =>
    let leaf := suite.wots.thTl pkSeed adrs (fun c =>
      wotsC256CompleteTo3 suite.wots pkSeed adrs c (d.digits c) (sig.chains c))
    baggyWalkMerkleRootFirst suite pkSeed layer tree p.subtreeHeight 0 kp leaf sig.auth

def baggyWalkLayersVerify (suite : BaggySuite256) (p : BaggyTreeParams)
    (pkSeed : BitVec 256) (leafIdx : Nat) :
    Nat → BitVec 256 → List BaggyLayerSig256 → Option (BitVec 256)
  | _, node, [] => some node
  | layer, node, sig :: rest =>
    let (kp, tree) := p.pathAt leafIdx layer
    match baggyLayerRecoverRoot suite p pkSeed layer tree kp node sig with
    | none => none
    | some nextRoot => baggyWalkLayersVerify suite p pkSeed leafIdx (layer + 1) nextRoot rest

/-- Standalone `Baggy` signature verification (`baggy.rs:351` `baggy_verify`). -/
@[expose] def baggyVerify (suite : BaggySuite256) (p : BaggyTreeParams)
    (pk : BaggyPublicKey256) (msg : BitVec 256) (sig : BaggySig256) : Bool :=
  if sig.layers.length != p.numLayers then false
  else
    match suite.hmsgLeaf p pk sig.r msg sig.msgCtr with
    | none => false
    | some leafIdx =>
      let (kp0, tree0) := p.pathAt leafIdx 0
      let forsPk := suite.forsRecoverPk pk.pkSeed tree0 kp0 msg sig.forsSig
      match baggyWalkLayersVerify suite p pk.pkSeed leafIdx 0 forsPk sig.layers with
      | none => false
      | some finalRoot => finalRoot == pk.pkRoot

/-- Static child root signed by `(layer, tree, kp)` for `layer ≥ 1` (`trueSubtreeRoot (layer - 1) childTree`). -/
def baggyCanonicalStaticChildRoot (suite : BaggySuite256) (p : BaggyTreeParams)
    (sk : BaggySecretKey256) (layer tree kp : Nat) : BitVec 256 :=
  baggyTrueSubtreeRoot suite p sk (layer - 1) (baggyChildTreeIdx p tree kp)

/-- Canonical single `WOTS+C` codeword ever signed by static address `(layer, tree, kp)` (`layer ≥ 1`) in uncached `Baggy`. -/
def baggyCanonicalStaticDigits (suite : BaggySuite256) (p : BaggyTreeParams)
    (sk : BaggySecretKey256) (layer tree kp : Nat) : Option WotsC256Digits :=
  let adrs := baggyLeafAdrs layer tree kp
  let childRoot := baggyCanonicalStaticChildRoot suite p sk layer tree kp
  let ctr := suite.grindCounter sk.pkSeed adrs childRoot
  wotsC256DecodeValidDigest (suite.wots.thDigest sk.pkSeed adrs childRoot ctr)

/-- Record of a static (`layer ≥ 1`) WOTS+C Round-2 codeword opening during signing. -/
structure StaticWotsOpeningRecord where
  layer : Nat
  tree : Nat
  kp : Nat
  signedNode : BitVec 256
  digits : WotsC256Digits
  deriving DecidableEq

/-- Build one genuine layer signature and record static (`layer ≥ 1`) codeword openings. -/
def baggySignLayerFresh (suite : BaggySuite256) (p : BaggyTreeParams)
    (sk : BaggySecretKey256) (layer tree kp : Nat) (childNode : BitVec 256) :
    Option (BaggyLayerSig256 × BitVec 256 × Option StaticWotsOpeningRecord) :=
  if _hKp : kp < 2 ^ p.subtreeHeight then
    let adrs := baggyLeafAdrs layer tree kp
    let ctr := suite.grindCounter sk.pkSeed adrs childNode
    match wotsC256DecodeValidDigest (suite.wots.thDigest sk.pkSeed adrs childNode ctr),
          wotsC256Sign suite.wots sk.pkSeed sk.skSeed adrs childNode ctr with
    | some d, some chains =>
      let leaves := baggySubtreeLeaves suite p sk layer tree
      let auth := baggyMerkleAuthPath suite sk.pkSeed layer tree p.subtreeHeight 0 leaves kp
      let root := baggyMerkleRoot suite sk.pkSeed layer tree p.subtreeHeight 0 leaves
      let recOpt := if 1 ≤ layer then some { layer := layer, tree := tree, kp := kp, signedNode := childNode, digits := d } else none
      some ({ ctr := ctr, chains := chains, auth := auth }, root, recOpt)
    | _, _ => none
  else
    none

def baggySignLayersUncachedAux (suite : BaggySuite256) (p : BaggyTreeParams)
    (sk : BaggySecretKey256) (leafIdx : Nat) :
    Nat → Nat → BitVec 256 → Option (List BaggyLayerSig256 × BitVec 256 × List StaticWotsOpeningRecord)
  | _, 0, node => some ([], node, [])
  | layer, rem + 1, node =>
    let (kp, tree) := p.pathAt leafIdx layer
    match baggySignLayerFresh suite p sk layer tree kp node with
    | none => none
    | some (sig, nextRoot, recOpt) =>
      match baggySignLayersUncachedAux suite p sk leafIdx (layer + 1) rem nextRoot with
      | none => none
      | some (restSigs, topRoot, restRecs) =>
        let allRecs := match recOpt with | some r => r :: restRecs | none => restRecs
        some (sig :: restSigs, topRoot, allRecs)

/-- Uncached `Baggy` signer returning `(sig, staticOpenings)`. -/
def baggySignUncached (suite : BaggySuite256) (p : BaggyTreeParams)
    (sk : BaggySecretKey256) (pk : BaggyPublicKey256)
    (msg : BitVec 256) (msgCtr : UInt32) : Option (BaggySig256 × List StaticWotsOpeningRecord) :=
  if pk.pkSeed != sk.pkSeed then none
  else
    let r := suite.prfRand sk.skPrf msg
    match suite.hmsgLeaf p pk r msg msgCtr with
    | none => none
    | some leafIdx =>
      let (kp0, tree0) := p.pathAt leafIdx 0
      let (forsSig, forsPk) := suite.forsSign sk.pkSeed sk.skSeed tree0 kp0 msg
      match baggySignLayersUncachedAux suite p sk leafIdx 0 p.numLayers forsPk with
      | none => none
      | some (layers, topRoot, recs) =>
        if topRoot != pk.pkRoot then none
        else
          let sig : BaggySig256 := { r := r, msgCtr := msgCtr, forsSig := forsSig, layers := layers }
          if baggyVerify suite p pk msg sig then some (sig, recs) else none

/-- **Hardened `VerifiedWaistbandCache` (cache-mutation Fix)**:
    1. Pinned to `(pinnedPkSeed, pinnedPkRoot, pinnedParamsDigest)`.
    2. Carries authenticated `expectedSubtreeRoot (layer, tree)` chained up to `(d - 1, 0) = pkRoot`! -/
structure VerifiedWaistbandCache where
  pinnedPkSeed : BitVec 256
  pinnedPkRoot : BitVec 256
  pinnedParamsDigest : BitVec 256
  expectedSubtreeRoot : Nat → Nat → Option (BitVec 256)
  cachedSig : Nat → Nat → Nat → Option BaggyLayerSig256

/-- Check upward Merkle-signature chaining from `(layer, tree)` up to `(d - 1, 0) == pkRoot` (`0 Classical.choice`). -/
def verifyCanopyChainToTop (suite : BaggySuite256) (p : BaggyTreeParams)
    (pk : BaggyPublicKey256) (cache : VerifiedWaistbandCache) :
    (stepsToTop : Nat) → (layer : Nat) → (tree : Nat) → (curRoot : BitVec 256) → Bool
  | 0, layer, tree, curRoot =>
    (layer == p.numLayers - 1) && (tree == 0) && (curRoot == pk.pkRoot)
  | rem + 1, layer, tree, curRoot =>
    let subLeaves := 2 ^ p.subtreeHeight
    let kpParent := tree % subLeaves
    let treeParent := tree / subLeaves
    let parentLayer := layer + 1
    match cache.expectedSubtreeRoot parentLayer treeParent,
          cache.cachedSig parentLayer treeParent kpParent with
    | some expParentRoot, some parentSig =>
      (baggyLayerRecoverRoot suite p pk.pkSeed parentLayer treeParent kpParent curRoot parentSig ==
        some expParentRoot) &&
      verifyCanopyChainToTop suite p pk cache rem parentLayer treeParent expParentRoot
    | _, _ => false

/-- Verify a `VerifiedWaistbandCache` hit at `(layer, tree, kp)` on `childNode` BEFORE using it. -/
@[expose] def verifyWaistbandCanopy (suite : BaggySuite256) (p : BaggyTreeParams)
    (pk : BaggyPublicKey256) (cache : VerifiedWaistbandCache)
    (layer tree kp : Nat) (childNode : BitVec 256) : Option (BaggyLayerSig256 × BitVec 256) :=
  if cache.pinnedPkSeed != pk.pkSeed ||
     cache.pinnedPkRoot != pk.pkRoot ||
     cache.pinnedParamsDigest != suite.paramsDigest p ||
     !p.coversLayer layer then
    none
  else
    match cache.expectedSubtreeRoot (layer - 1) (baggyChildTreeIdx p tree kp),
          cache.expectedSubtreeRoot layer tree,
          cache.cachedSig layer tree kp with
    | some expChildRoot, some expLayerRoot, some sig =>
      if childNode != expChildRoot then none
      else if baggyLayerRecoverRoot suite p pk.pkSeed layer tree kp childNode sig != some expLayerRoot then none
      else if !verifyCanopyChainToTop suite p pk cache ((p.numLayers - 1) - layer) layer tree expLayerRoot then none
      else some (sig, expLayerRoot)
    | _, _, _ => none

/-- Abstract per-party static WOTS record `(layer, tree, kp) ↦ firstSignedDigits`. -/
abbrev DurableStaticWotsGuard := List (Nat × Nat × Nat × WotsC256Digits)

def lookupDurableDigits (g : DurableStaticWotsGuard) (layer tree kp : Nat) : Option WotsC256Digits :=
  match g with
  | [] => none
  | (l, t, k, d) :: rest =>
    if l == layer && t == tree && k == kp then some d
    else lookupDurableDigits rest layer tree kp

/-- Atomic specification of first-signed consistency. Persistence and release
    are modeled separately by `baggyReleaseStep` below. -/
def enforceDurableStaticOpenings :
    DurableStaticWotsGuard → List StaticWotsOpeningRecord → Option DurableStaticWotsGuard
  | g, [] => some g
  | g, rec :: rest =>
    match lookupDurableDigits g rec.layer rec.tree rec.kp with
    | some prevDigits =>
      if prevDigits == rec.digits then
        enforceDurableStaticOpenings g rest
      else
        none
    | none =>
      enforceDurableStaticOpenings ((rec.layer, rec.tree, rec.kp, rec.digits) :: g) rest

/-- Recursive layer planner/signer with `VerifiedWaistbandCache`:
    cached hits emit `0` fresh MPC openings; misses compute genuine subtree roots and record static openings. -/
def baggySignLayersVerifiedCacheAux (suite : BaggySuite256) (p : BaggyTreeParams)
    (sk : BaggySecretKey256) (pk : BaggyPublicKey256) (cache : VerifiedWaistbandCache)
    (leafIdx : Nat) :
    Nat → Nat → BitVec 256 → Option (List BaggyLayerSig256 × BitVec 256 × List StaticWotsOpeningRecord)
  | _, 0, node => some ([], node, [])
  | layer, rem + 1, node =>
    let (kp, tree) := p.pathAt leafIdx layer
    match verifyWaistbandCanopy suite p pk cache layer tree kp node with
    | some (cachedLayerSig, verifiedRoot) =>
      match baggySignLayersVerifiedCacheAux suite p sk pk cache leafIdx (layer + 1) rem verifiedRoot with
      | none => none
      | some (restSigs, topRoot, restRecs) =>
        some (cachedLayerSig :: restSigs, topRoot, restRecs)
    | none =>
      if (cache.cachedSig layer tree kp).isSome then none else
      match baggySignLayerFresh suite p sk layer tree kp node with
      | none => none
      | some (sig, nextRoot, recOpt) =>
        match baggySignLayersVerifiedCacheAux suite p sk pk cache leafIdx (layer + 1) rem nextRoot with
        | none => none
        | some (restSigs, topRoot, restRecs) =>
          let allRecs := match recOpt with | some r => r :: restRecs | none => restRecs
          some (sig :: restSigs, topRoot, allRecs)

/-- Pure single-session signature specification with cache checking and an atomic
    first-signed guard. This function has no crash or storage semantics. -/
def baggySignVerifiedWaistband (suite : BaggySuite256) (p : BaggyTreeParams)
    (sk : BaggySecretKey256) (pk : BaggyPublicKey256)
    (cache : VerifiedWaistbandCache) (guard : DurableStaticWotsGuard)
    (msg : BitVec 256) (msgCtr : UInt32) :
    Option (BaggySig256 × DurableStaticWotsGuard × List StaticWotsOpeningRecord) :=
  if pk.pkSeed != sk.pkSeed then none
  else
    let r := suite.prfRand sk.skPrf msg
    match suite.hmsgLeaf p pk r msg msgCtr with
    | none => none
    | some leafIdx =>
      let (kp0, tree0) := p.pathAt leafIdx 0
      let (forsSig, forsPk) := suite.forsSign sk.pkSeed sk.skSeed tree0 kp0 msg
      match baggySignLayersVerifiedCacheAux suite p sk pk cache leafIdx 0 p.numLayers forsPk with
      | none => none
      | some (layers, topRoot, recs) =>
        if topRoot != pk.pkRoot then none
        else
          -- Pure guard specification; actual durability belongs to baggyReleaseStep.
          match enforceDurableStaticOpenings guard recs with
          | none => none
          | some guard' =>
            let sig : BaggySig256 := { r := r, msgCtr := msgCtr, forsSig := forsSig, layers := layers }
            if baggyVerify suite p pk msg sig then some (sig, guard', recs) else none

/-- Multi-session `Baggy` signing runner accumulating all Round-2 static WOTS codeword openings across sessions. -/
def baggyRunMultiSessionVerified (suite : BaggySuite256) (p : BaggyTreeParams)
    (sk : BaggySecretKey256) (pk : BaggyPublicKey256) :
    DurableStaticWotsGuard → List (VerifiedWaistbandCache × BitVec 256 × UInt32) →
    DurableStaticWotsGuard × List (BitVec 256 × BaggySig256) × List StaticWotsOpeningRecord
  | guard, [] => (guard, [], [])
  | guard, (cache, msg, msgCtr) :: rest =>
    match baggySignVerifiedWaistband suite p sk pk cache guard msg msgCtr with
    | none => (guard, [], [])
    | some (sig, guard', recs) =>
      let (guardFinal, sigs, restRecs) := baggyRunMultiSessionVerified suite p sk pk guard' rest
      (guardFinal, (msg, sig) :: sigs, recs ++ restRecs)

/-- Predicate stating that `cache` was honestly populated (`WaistbandCache::precompute`) from `sk`. -/
def WaistbandMatchesKey (suite : BaggySuite256) (p : BaggyTreeParams)
    (sk : BaggySecretKey256) (cache : VerifiedWaistbandCache) : Prop :=
  ∀ layer tree v, cache.expectedSubtreeRoot layer tree = some v →
    v = baggyTrueSubtreeRoot suite p sk layer tree

/-- Honest root enrollment constructs the key-matching premise directly. -/
def enrollWaistbandRoots (suite : BaggySuite256) (p : BaggyTreeParams)
    (sk : BaggySecretKey256) (cache : VerifiedWaistbandCache) : VerifiedWaistbandCache :=
  { cache with
    pinnedPkSeed := sk.pkSeed
    pinnedPkRoot := (baggyKeygen256 suite p sk).pkRoot
    expectedSubtreeRoot := fun layer tree => some (baggyTrueSubtreeRoot suite p sk layer tree) }

theorem enrolled_waistband_matches_key (suite : BaggySuite256) (p : BaggyTreeParams)
    (sk : BaggySecretKey256) (cache : VerifiedWaistbandCache) :
    WaistbandMatchesKey suite p sk (enrollWaistbandRoots suite p sk cache) := by
  intro layer tree v hv
  exact (Option.some.inj hv).symm

private theorem baggySignLayerFresh_props (suite : BaggySuite256) (p : BaggyTreeParams)
    (sk : BaggySecretKey256) (layer tree kp : Nat) (childNode : BitVec 256)
    {sig : BaggyLayerSig256} {nextRoot : BitVec 256} {recOpt : Option StaticWotsOpeningRecord}
    (hFresh : baggySignLayerFresh suite p sk layer tree kp childNode = some (sig, nextRoot, recOpt)) :
    nextRoot = baggyTrueSubtreeRoot suite p sk layer tree ∧
    baggyLayerRecoverRoot suite p sk.pkSeed layer tree kp childNode sig = some nextRoot ∧
    (∀ r : StaticWotsOpeningRecord, recOpt = some r →
      1 ≤ layer ∧ r.layer = layer ∧ r.tree = tree ∧ r.kp = kp ∧ r.signedNode = childNode ∧
      wotsC256DecodeValidDigest
        (suite.wots.thDigest sk.pkSeed (baggyLeafAdrs layer tree kp) childNode
          (suite.grindCounter sk.pkSeed (baggyLeafAdrs layer tree kp) childNode)) = some r.digits) := by
  unfold baggySignLayerFresh at hFresh
  if hKp : kp < 2 ^ p.subtreeHeight then
    rw [dite_pos hKp] at hFresh
    let adrs := baggyLeafAdrs layer tree kp
    let ctr := suite.grindCounter sk.pkSeed adrs childNode
    cases hDec : wotsC256DecodeValidDigest (suite.wots.thDigest sk.pkSeed adrs childNode ctr) with
    | none =>
      simp [adrs, ctr, hDec] at hFresh
    | some d =>
      cases hSign : wotsC256Sign suite.wots sk.pkSeed sk.skSeed adrs childNode ctr with
      | none =>
        simp [adrs, ctr, hDec, hSign] at hFresh
      | some chains =>
        simp only [adrs, ctr, hDec, hSign] at hFresh
        injection hFresh with hTuple
        rcases Prod.mk.inj hTuple with ⟨hSigEq, hRestEq⟩
        rcases Prod.mk.inj hRestEq with ⟨hRootEq, hRecEq⟩
        subst hSigEq hRootEq
        refine ⟨rfl, ?_, ?_⟩
        · unfold baggyLayerRecoverRoot
          dsimp only
          dsimp only [adrs, ctr] at hDec
          rw [hDec]
          dsimp only
          have hVer := wotsC256_sign_verify_complete suite.wots sk.pkSeed sk.skSeed adrs childNode ctr chains hSign
          unfold wotsC256Verify at hVer
          rw [hDec] at hVer
          dsimp only at hVer
          have hLeafEq : suite.wots.thTl sk.pkSeed adrs
              (fun c => wotsC256CompleteTo3 suite.wots sk.pkSeed adrs c (d.digits c) (chains c)) =
              baggySubtreeLeaves suite p sk layer tree ⟨kp, hKp⟩ := eq_of_beq hVer
          rw [hLeafEq]
          exact baggyWalkMerkle_authPath_eq suite sk.pkSeed layer tree p.subtreeHeight 0
            (baggySubtreeLeaves suite p sk layer tree) ⟨kp, hKp⟩
        · intro r hr
          rw [← hRecEq] at hr
          if hGe1 : 1 ≤ layer then
            rw [ite_pos hGe1] at hr
            injection hr with hrEq
            subst hrEq
            exact ⟨hGe1, rfl, rfl, rfl, rfl, rfl⟩
          else
            rw [ite_neg hGe1] at hr
            cases hr
  else
    rw [dite_neg hKp] at hFresh
    cases hFresh

private theorem baggyLayersVerifiedCacheAux_canonical
    (suite : BaggySuite256) (p : BaggyTreeParams)
    (sk : BaggySecretKey256) (pk : BaggyPublicKey256) (cache : VerifiedWaistbandCache)
    (hSeedEq : pk.pkSeed = sk.pkSeed)
    (hMatch : WaistbandMatchesKey suite p sk cache)
    (leafIdx : Nat) :
    ∀ (rem layer : Nat) (node : BitVec 256)
      {layers : List BaggyLayerSig256} {topRoot : BitVec 256} {recs : List StaticWotsOpeningRecord},
      (1 ≤ layer → node = baggyTrueSubtreeRoot suite p sk (layer - 1) (p.pathAt leafIdx (layer - 1)).2) →
      baggySignLayersVerifiedCacheAux suite p sk pk cache leafIdx layer rem node = some (layers, topRoot, recs) →
      (∀ r ∈ recs,
        1 ≤ r.layer ∧
        r.signedNode = baggyCanonicalStaticChildRoot suite p sk r.layer r.tree r.kp ∧
        baggyCanonicalStaticDigits suite p sk r.layer r.tree r.kp = some r.digits) := by
  have _ := hSeedEq
  intro rem
  induction rem with
  | zero =>
    intro layer node layers topRoot recs _ hAux r hr
    unfold baggySignLayersVerifiedCacheAux at hAux
    injection hAux with hEq
    rcases Prod.mk.inj hEq with ⟨_, hEq2⟩
    rcases Prod.mk.inj hEq2 with ⟨_, hRecs⟩
    rw [← hRecs] at hr
    cases hr
  | succ rem ihRem =>
    intro layer node layers topRoot recs hNodeInv hAux r hr
    unfold baggySignLayersVerifiedCacheAux at hAux
    dsimp only at hAux
    let kp := (p.pathAt leafIdx layer).1
    let tree := (p.pathAt leafIdx layer).2
    cases hCanopy : verifyWaistbandCanopy suite p pk cache layer tree kp node with
    | some hit =>
      rcases hit with ⟨cachedSig, verifiedRoot⟩
      rw [hCanopy] at hAux
      dsimp only at hAux
      cases hRec : baggySignLayersVerifiedCacheAux suite p sk pk cache leafIdx (layer + 1) rem verifiedRoot with
      | none => rw [hRec] at hAux; cases hAux
      | some res =>
        rcases res with ⟨restSigs, topR, restRecs⟩
        rw [hRec] at hAux
        injection hAux with hEq
        rcases Prod.mk.inj hEq with ⟨_, hEq2⟩
        rcases Prod.mk.inj hEq2 with ⟨_, hRecsEq⟩
        rw [← hRecsEq] at hr
        have hVerRoot : verifiedRoot = baggyTrueSubtreeRoot suite p sk layer tree := by
          unfold verifyWaistbandCanopy at hCanopy
          split at hCanopy
          · cases hCanopy
          · cases hExpC : cache.expectedSubtreeRoot (layer - 1) (baggyChildTreeIdx p tree kp) <;>
            cases hExpL : cache.expectedSubtreeRoot layer tree <;>
            cases hCSig : cache.cachedSig layer tree kp <;>
              simp [hExpC, hExpL, hCSig] at hCanopy
            rcases hCanopy with ⟨_, _, _, _, hVr⟩
            rw [← hVr]
            exact hMatch layer tree _ hExpL
        exact ihRem (layer + 1) verifiedRoot (fun _ => by simp [tree, hVerRoot]) hRec r hr
    | none =>
      rw [hCanopy] at hAux
      dsimp only at hAux
      by_cases hPresent : (cache.cachedSig layer tree kp).isSome = true
      · simp only [kp, tree, hPresent, ↓reduceIte] at hAux
        cases hAux
      · have hAbsent : (cache.cachedSig layer tree kp).isSome = false :=
          Bool.eq_false_iff.mpr hPresent
        simp only [kp, tree, hAbsent, Bool.false_eq_true, ↓reduceIte] at hAux
        cases hFresh : baggySignLayerFresh suite p sk layer tree kp node with
        | none =>
          have hFresh' : baggySignLayerFresh suite p sk layer (p.pathAt leafIdx layer).2 (p.pathAt leafIdx layer).1 node = none := hFresh
          rw [hFresh'] at hAux; cases hAux
        | some freshRes =>
          rcases freshRes with ⟨sig, nextRoot, recOpt⟩
          have hFresh' : baggySignLayerFresh suite p sk layer (p.pathAt leafIdx layer).2 (p.pathAt leafIdx layer).1 node = some (sig, nextRoot, recOpt) := hFresh
          rw [hFresh'] at hAux
          dsimp only at hAux
          obtain ⟨hNextTrue, _, hRecProps⟩ := baggySignLayerFresh_props suite p sk layer tree kp node hFresh
          cases hRec : baggySignLayersVerifiedCacheAux suite p sk pk cache leafIdx (layer + 1) rem nextRoot with
          | none => rw [hRec] at hAux; cases hAux
          | some res =>
            rcases res with ⟨restSigs, topR, restRecs⟩
            rw [hRec] at hAux
            dsimp only at hAux
            injection hAux with hEq
            rcases Prod.mk.inj hEq with ⟨_, hEq2⟩
            rcases Prod.mk.inj hEq2 with ⟨_, hRecsEq⟩
            rw [← hRecsEq] at hr
            have ih := ihRem (layer + 1) nextRoot (fun _ => by simp [tree, hNextTrue]) hRec
            cases hOpt : recOpt with
            | none =>
              rw [hOpt] at hr
              exact ih r hr
            | some rec0 =>
              rw [hOpt] at hr
              rcases List.mem_cons.mp hr with rfl | hMemRest
              · obtain ⟨hGe1, hRLayer, hRTree, hRKp, hSignedEq, hDigEq⟩ := hRecProps r hOpt
                have hChildTree : (p.pathAt leafIdx (layer - 1)).2 = baggyChildTreeIdx p tree kp := by
                  have hLayerSucc : (layer - 1) + 1 = layer := Nat.sub_add_cancel hGe1
                  have hPath := baggyChildTreeIdx_pathAt p leafIdx (layer - 1)
                  dsimp only at hPath
                  rw [hLayerSucc] at hPath
                  exact hPath.symm
                have hNodeCanon : node = baggyCanonicalStaticChildRoot suite p sk layer tree kp := by
                  rw [hNodeInv hGe1, hChildTree]
                  rfl
                rw [hRLayer, hRTree, hRKp]
                refine ⟨hGe1, hSignedEq.trans hNodeCanon, ?_⟩
                unfold baggyCanonicalStaticDigits
                rw [← hNodeCanon]
                exact hDigEq
              · exact ih r hMemRest
private theorem lookupDurableDigits_preserved :
    ∀ {g g' : DurableStaticWotsGuard} {recs : List StaticWotsOpeningRecord}
      {layer tree kp : Nat} {d0 : WotsC256Digits},
      lookupDurableDigits g layer tree kp = some d0 →
      enforceDurableStaticOpenings g recs = some g' →
      lookupDurableDigits g' layer tree kp = some d0 ∧
      (∀ r ∈ recs, r.layer = layer ∧ r.tree = tree ∧ r.kp = kp → r.digits = d0)
  | g, g', [], _, _, _, _, hLook, hEnf => by
    injection hEnf with hEq
    subst hEq
    exact ⟨hLook, fun _ hm => by cases hm⟩
  | g, g', rec :: rest, layer, tree, kp, d0, hLook, hEnf => by
    unfold enforceDurableStaticOpenings at hEnf
    cases hCur : lookupDurableDigits g rec.layer rec.tree rec.kp with
    | some prev =>
      rw [hCur] at hEnf
      dsimp only at hEnf
      if hEqD : prev == rec.digits then
        rw [ite_pos hEqD] at hEnf
        obtain ⟨hPres, hRest⟩ := lookupDurableDigits_preserved hLook hEnf
        refine ⟨hPres, fun r hr ⟨hl, ht, hk⟩ => ?_⟩
        rcases List.mem_cons.mp hr with rfl | hTl
        · subst hl ht hk
          rw [hLook] at hCur
          injection hCur with hPrevEq
          exact (eq_of_beq hEqD).symm.trans hPrevEq.symm
        · exact hRest r hTl ⟨hl, ht, hk⟩
      else
        rw [ite_neg hEqD] at hEnf
        cases hEnf
    | none =>
      rw [hCur] at hEnf
      dsimp only at hEnf
      have hDiffAddr : ¬ (rec.layer == layer && rec.tree == tree && rec.kp == kp) = true := by
        intro hSame
        rcases Bool.and_eq_true_iff.mp hSame with ⟨h12, hk⟩
        rcases Bool.and_eq_true_iff.mp h12 with ⟨hl, ht⟩
        rw [eq_of_beq hl, eq_of_beq ht, eq_of_beq hk, hLook] at hCur
        cases hCur
      have hLookCons :
          lookupDurableDigits ((rec.layer, rec.tree, rec.kp, rec.digits) :: g) layer tree kp = some d0 := by
        simp [lookupDurableDigits, hDiffAddr, hLook]
      obtain ⟨hPres, hRest⟩ := lookupDurableDigits_preserved hLookCons hEnf
      refine ⟨hPres, fun r hr ⟨hl, ht, hk⟩ => ?_⟩
      rcases List.mem_cons.mp hr with rfl | hTl
      · subst hl ht hk
        rw [hLook] at hCur
        cases hCur
      · exact hRest r hTl ⟨hl, ht, hk⟩

private theorem enforceDurableStaticOpenings_unique :
    ∀ {g g' : DurableStaticWotsGuard} {recs : List StaticWotsOpeningRecord},
      enforceDurableStaticOpenings g recs = some g' →
      ∀ r ∈ recs, lookupDurableDigits g' r.layer r.tree r.kp = some r.digits
  | _, _, [], _, _, hr => by cases hr
  | g, g', rec :: rest, hEnf, r, hr => by
    unfold enforceDurableStaticOpenings at hEnf
    cases hCur : lookupDurableDigits g rec.layer rec.tree rec.kp with
    | some prev =>
      rw [hCur] at hEnf
      dsimp only at hEnf
      if hEqD : prev == rec.digits then
        rw [ite_pos hEqD] at hEnf
        rcases List.mem_cons.mp hr with rfl | hTl
        · have hEqPrev : prev = r.digits := eq_of_beq hEqD
          subst hEqPrev
          exact (lookupDurableDigits_preserved hCur hEnf).1
        · exact enforceDurableStaticOpenings_unique hEnf r hTl
      else
        rw [ite_neg hEqD] at hEnf
        cases hEnf
    | none =>
      rw [hCur] at hEnf
      dsimp only at hEnf
      have hHead : lookupDurableDigits ((rec.layer, rec.tree, rec.kp, rec.digits) :: g)
          rec.layer rec.tree rec.kp = some rec.digits := by
        simp [lookupDurableDigits]
      rcases List.mem_cons.mp hr with rfl | hTl
      · exact (lookupDurableDigits_preserved hHead hEnf).1
      · exact enforceDurableStaticOpenings_unique hEnf r hTl

/-- **Crown-Jewel `Waistband` Theorem 1 (`waistband_verified_multi_session_single_codeword`)**:
    1. **Exact Single-Codeword Equivalence with Uncached `Baggy`**: Across ANY multi-session signing
       batch where `WaistbandMatchesKey` holds, EVERY static (`layer ≥ 1`) WOTS opening in
       `baggyRunMultiSessionVerified` signs `baggyCanonicalStaticChildRoot` and opens the **exact
       single codeword `baggyCanonicalStaticDigits`** opened by uncached `Baggy`!
    2. **Unconditional Multi-Session Anti-Double-Codeword Safety (`DurableStaticWotsGuard`)**: Even
       against an **arbitrarily corrupted** sequence of caches across sessions (`0` assumptions on
       `cache`!), for any two openings `r1, r2` at the same static address `(layer, tree, kp)` across
       the entire multi-session execution, **`r1.digits = r2.digits`**! -/
theorem waistband_verified_multi_session_single_codeword
    (suite : BaggySuite256) (p : BaggyTreeParams)
    (sk : BaggySecretKey256) (pk : BaggyPublicKey256) :
    (∀ (sessions : List (VerifiedWaistbandCache × BitVec 256 × UInt32))
       (guard : DurableStaticWotsGuard),
      (∀ s ∈ sessions, WaistbandMatchesKey suite p sk s.1) →
      ∀ r ∈ (baggyRunMultiSessionVerified suite p sk pk guard sessions).2.2,
        1 ≤ r.layer ∧
        r.signedNode = baggyCanonicalStaticChildRoot suite p sk r.layer r.tree r.kp ∧
        baggyCanonicalStaticDigits suite p sk r.layer r.tree r.kp = some r.digits) ∧
    (∀ (sessions : List (VerifiedWaistbandCache × BitVec 256 × UInt32))
       (guard : DurableStaticWotsGuard)
       (r1 r2 : StaticWotsOpeningRecord),
      let (_, _, allOpenings) := baggyRunMultiSessionVerified suite p sk pk guard sessions
      r1 ∈ allOpenings → r2 ∈ allOpenings →
      r1.layer = r2.layer ∧ r1.tree = r2.tree ∧ r1.kp = r2.kp →
      r1.digits = r2.digits) := by
  have hGuardTrace :
      ∀ (sessions : List (VerifiedWaistbandCache × BitVec 256 × UInt32))
        (guard : DurableStaticWotsGuard),
        let (guardFinal, _, allOpenings) := baggyRunMultiSessionVerified suite p sk pk guard sessions
        (∀ l t k d0, lookupDurableDigits guard l t k = some d0 →
          lookupDurableDigits guardFinal l t k = some d0 ∧
          (∀ r ∈ allOpenings, r.layer = l ∧ r.tree = t ∧ r.kp = k → r.digits = d0)) ∧
        (∀ r ∈ allOpenings, lookupDurableDigits guardFinal r.layer r.tree r.kp = some r.digits) := by
    intro sessions
    induction sessions with
    | nil =>
      intro guard
      dsimp [baggyRunMultiSessionVerified]
      refine ⟨fun _ _ _ _ hLook => ⟨hLook, fun _ hm => by cases hm⟩, fun _ hm => by cases hm⟩
    | cons sess rest ih =>
      intro guard
      rcases sess with ⟨cache, msg, msgCtr⟩
      simp only [baggyRunMultiSessionVerified]
      cases hSign : baggySignVerifiedWaistband suite p sk pk cache guard msg msgCtr with
      | none =>
        exact ⟨fun _ _ _ _ h => ⟨h, fun _ hm => by cases hm⟩, fun _ hm => by cases hm⟩
      | some out =>
        rcases out with ⟨sig, guard', recs⟩
        have hEnf : enforceDurableStaticOpenings guard recs = some guard' := by
          unfold baggySignVerifiedWaistband at hSign
          if hS : pk.pkSeed != sk.pkSeed then simp [hS] at hSign
          else
            simp only [hS, Bool.false_eq_true, ↓reduceIte] at hSign
            cases hL : suite.hmsgLeaf p pk (suite.prfRand sk.skPrf msg) msg msgCtr with
            | none => simp [hL] at hSign
            | some leafIdx =>
              simp only [hL] at hSign
              cases hA : baggySignLayersVerifiedCacheAux suite p sk pk cache leafIdx 0 p.numLayers
                  (suite.forsSign sk.pkSeed sk.skSeed (p.pathAt leafIdx 0).2 (p.pathAt leafIdx 0).1 msg).2 with
              | none => simp [hA] at hSign
              | some aRes =>
                rcases aRes with ⟨ls, topR, rs⟩
                simp only [hA] at hSign
                if hTop : topR != pk.pkRoot then simp [hTop] at hSign
                else
                  simp only [hTop, Bool.false_eq_true, ↓reduceIte] at hSign
                  cases hE : enforceDurableStaticOpenings guard rs with
                  | none => simp [hE] at hSign
                  | some gNext =>
                    simp only [hE] at hSign
                    let candSig : BaggySig256 :=
                      { r := suite.prfRand sk.skPrf msg
                        msgCtr := msgCtr
                        forsSig := (suite.forsSign sk.pkSeed sk.skSeed (p.pathAt leafIdx 0).2 (p.pathAt leafIdx 0).1 msg).1
                        layers := ls }
                    if hV : baggyVerify suite p pk msg candSig then
                      simp only [candSig, hV, ↓reduceIte] at hSign
                      injection hSign with hTuple
                      rcases Prod.mk.inj hTuple with ⟨_, hRestT⟩
                      rcases Prod.mk.inj hRestT with ⟨hGEq, hREq⟩
                      subst hGEq hREq
                      exact hE
                    else
                      simp [candSig, hV] at hSign
        have ih' := ih guard'
        rcases hRunRest : baggyRunMultiSessionVerified suite p sk pk guard' rest with ⟨gFinal, sigsRest, restRecs⟩
        dsimp only
        rw [hRunRest] at ih' ⊢
        dsimp only at ih' ⊢
        refine ⟨?_, ?_⟩
        · intro l t k d0 hLook
          obtain ⟨hMidLook, hHeadEq⟩ := lookupDurableDigits_preserved hLook hEnf
          obtain ⟨hFinLook, hTailEq⟩ := ih'.1 l t k d0 hMidLook
          refine ⟨hFinLook, fun r hr hAddr => ?_⟩
          rcases List.mem_append.mp hr with hInHead | hInTail
          · exact hHeadEq r hInHead hAddr
          · exact hTailEq r hInTail hAddr
        · intro r hr
          rcases List.mem_append.mp hr with hInHead | hInTail
          · have hMid := enforceDurableStaticOpenings_unique hEnf r hInHead
            exact (ih'.1 r.layer r.tree r.kp r.digits hMid).1
          · exact ih'.2 r hInTail
  refine ⟨?_, ?_⟩
  · intro sessions guard hAllMatch
    induction sessions generalizing guard with
    | nil => intro _ hm; cases hm
    | cons sess rest ih =>
      rcases sess with ⟨cache, msg, msgCtr⟩
      have hHeadMatch : WaistbandMatchesKey suite p sk cache := hAllMatch _ (.head _)
      have hTailMatch : ∀ s ∈ rest, WaistbandMatchesKey suite p sk s.1 :=
        fun s hs => hAllMatch s (.tail _ hs)
      simp only [baggyRunMultiSessionVerified]
      cases hSign : baggySignVerifiedWaistband suite p sk pk cache guard msg msgCtr with
      | none => intro _ hm; cases hm
      | some out =>
        rcases out with ⟨sig, guard', recs⟩
        rcases hRunRest : baggyRunMultiSessionVerified suite p sk pk guard' rest with ⟨gFinal, sigsRest, restRecs⟩
        have ihRest := ih guard' hTailMatch
        dsimp only
        rw [hRunRest] at ihRest ⊢
        dsimp only at ihRest ⊢
        intro r hr
        rcases List.mem_append.mp hr with hInHead | hInTail
        · unfold baggySignVerifiedWaistband at hSign
          if hSeedNe : pk.pkSeed != sk.pkSeed then simp [hSeedNe] at hSign
          else
            have hSeedEq : pk.pkSeed = sk.pkSeed := by
              cases hBeq : (pk.pkSeed == sk.pkSeed)
              · rw [bne, hBeq] at hSeedNe; simp at hSeedNe
              · exact eq_of_beq hBeq
            simp only [hSeedNe, Bool.false_eq_true, ↓reduceIte] at hSign
            cases hL : suite.hmsgLeaf p pk (suite.prfRand sk.skPrf msg) msg msgCtr with
            | none => simp [hL] at hSign
            | some leafIdx =>
              simp only [hL] at hSign
              cases hA : baggySignLayersVerifiedCacheAux suite p sk pk cache leafIdx 0 p.numLayers
                  (suite.forsSign sk.pkSeed sk.skSeed (p.pathAt leafIdx 0).2 (p.pathAt leafIdx 0).1 msg).2 with
              | none => simp [hA] at hSign
              | some aRes =>
                rcases aRes with ⟨ls, topR, rs⟩
                simp only [hA] at hSign
                if hTop : topR != pk.pkRoot then simp [hTop] at hSign
                else
                  simp only [hTop, Bool.false_eq_true, ↓reduceIte] at hSign
                  cases hE : enforceDurableStaticOpenings guard rs with
                  | none => simp [hE] at hSign
                  | some gNext =>
                    simp only [hE] at hSign
                    split at hSign
                    · injection hSign with hTup
                      have hRsEq : rs = recs := (Prod.mk.inj (Prod.mk.inj hTup).2).2
                      rw [← hRsEq] at hInHead
                      exact baggyLayersVerifiedCacheAux_canonical suite p sk pk cache hSeedEq hHeadMatch
                        leafIdx p.numLayers 0 _ (fun h1 => False.elim (Nat.not_succ_le_zero 0 h1)) hA r hInHead
                    · cases hSign
        · exact ihRest r hInTail
  · intro sessions guard r1 r2
    have hTr := hGuardTrace sessions guard
    rcases hRun : baggyRunMultiSessionVerified suite p sk pk guard sessions with ⟨gFinal, sigs, allOpenings⟩
    rw [hRun] at hTr
    dsimp only at hTr ⊢
    intro hr1 hr2 ⟨hl, ht, hk⟩
    have hLook1 := hTr.2 r1 hr1
    have hLook2 := hTr.2 r2 hr2
    rw [hl, ht, hk, hLook2] at hLook1
    injection hLook1 with hEq
    exact hEq.symm

/-- Upper-hypertree reduction factor over the abstract `BaggySuite256` interface.
A concrete bottom-layer reduction remains a separate obligation. -/
inductive BaggyUpperReductionResult (suite : BaggySuite256) (p : BaggyTreeParams)
    (sk : BaggySecretKey256) (approvedMsgs : List (BitVec 256)) (msgStar : BitVec 256) : Type where
  | bottomLayerReachedGenuineRoot
      (leafIdx : Nat) (forsSigStar : BitVec 256) (sig0 : BaggyLayerSig256)
      (hNotApproved : msgStar ∉ approvedMsgs)
      (hLayer0RecoversTrue :
        let (kp0, tree0) := p.pathAt leafIdx 0
        baggyLayerRecoverRoot suite p sk.pkSeed 0 tree0 kp0
          (suite.forsRecoverPk sk.pkSeed tree0 kp0 msgStar forsSigStar) sig0 =
        some (baggyTrueSubtreeRoot suite p sk 0 tree0))
  | merkleCollision (coll : BaggyMerkleCollision suite sk.pkSeed)
  | staticLayerWotsBreak (layer tree kp : Nat)
      (hStaticLayer : 1 ≤ layer)
      (wotsBreak : WotsC256BreakWitness suite.wots sk.pkSeed sk.skSeed
        (baggyLeafAdrs layer tree kp)
        (baggyCanonicalStaticChildRoot suite p sk layer tree kp)
        (suite.grindCounter sk.pkSeed (baggyLeafAdrs layer tree kp)
          (baggyCanonicalStaticChildRoot suite p sk layer tree kp)))

def extractStaticLayerBreakFromTransition
    (suite : BaggySuite256) (p : BaggyTreeParams) (sk : BaggySecretKey256)
    (hGrind : BaggySuite256.WellGrinded suite)
    (approvedMsgs : List (BitVec 256)) (msgStar : BitVec 256)
    (leafIdx layer : Nat) (hGe1 : 1 ≤ layer)
    (nodeStar : BitVec 256) (sigStar : BaggyLayerSig256)
    (hChildMismatch : nodeStar ≠ baggyCanonicalStaticChildRoot suite p sk layer
      (p.pathAt leafIdx layer).2 (p.pathAt leafIdx layer).1)
    (hParentMatchesTrue :
      baggyLayerRecoverRoot suite p sk.pkSeed layer
        (p.pathAt leafIdx layer).2 (p.pathAt leafIdx layer).1 nodeStar sigStar =
      some (baggyTrueSubtreeRoot suite p sk layer (p.pathAt leafIdx layer).2)) :
    BaggyUpperReductionResult suite p sk approvedMsgs msgStar :=
  let kp := (p.pathAt leafIdx layer).1
  let tree := (p.pathAt leafIdx layer).2
  let adrs := baggyLeafAdrs layer tree kp
  let canonChild := baggyCanonicalStaticChildRoot suite p sk layer tree kp
  let canonCtr := suite.grindCounter sk.pkSeed adrs canonChild
  have hKpLt : kp < 2 ^ p.subtreeHeight :=
    Nat.mod_lt _ (Nat.two_pow_pos p.subtreeHeight)
  match hHonDec : wotsC256DecodeValidDigest (suite.wots.thDigest sk.pkSeed adrs canonChild canonCtr) with
  | none =>
    False.elim <| by
      have hSome := hGrind.2 sk.pkSeed adrs canonChild
      change (wotsC256DecodeValidDigest (suite.wots.thDigest sk.pkSeed adrs canonChild canonCtr)).isSome = true at hSome
      rw [hHonDec] at hSome
      cases hSome
  | some dCanon =>
    match hStarDec : wotsC256DecodeValidDigest (suite.wots.thDigest sk.pkSeed adrs nodeStar sigStar.ctr) with
    | none =>
      False.elim <| by
        unfold baggyLayerRecoverRoot at hParentMatchesTrue
        dsimp only at hParentMatchesTrue
        dsimp only [adrs, kp, tree] at hStarDec
        rw [hStarDec] at hParentMatchesTrue
        cases hParentMatchesTrue
    | some dStar =>
      let leafStar := suite.wots.thTl sk.pkSeed adrs (fun c =>
        wotsC256CompleteTo3 suite.wots sk.pkSeed adrs c (dStar.digits c) (sigStar.chains c))
      let honestLeaf := baggySubtreeLeaves suite p sk layer tree ⟨kp, hKpLt⟩
      if hLeafEq : leafStar = honestLeaf then
        have hWotsVer : wotsC256Verify suite.wots sk.pkSeed adrs
            (wotsC256PkLeaf suite.wots sk.pkSeed sk.skSeed adrs) nodeStar sigStar.ctr sigStar.chains = true := by
          unfold wotsC256Verify
          rw [hStarDec]
          dsimp only
          exact beq_iff_eq.mpr hLeafEq
        .staticLayerWotsBreak layer tree kp hGe1
          (wotsC256_one_use_euf_cma_extract suite.wots sk.pkSeed sk.skSeed adrs
            canonChild canonCtr dCanon hHonDec nodeStar sigStar.ctr sigStar.chains
            (fun hEq => hChildMismatch (congrArg Prod.fst hEq)) hWotsVer)
      else
        have hWalkEq : baggyWalkMerkleRootFirst suite sk.pkSeed layer tree p.subtreeHeight 0 kp leafStar sigStar.auth =
            some (baggyMerkleRoot suite sk.pkSeed layer tree p.subtreeHeight 0 (baggySubtreeLeaves suite p sk layer tree)) := by
          unfold baggyLayerRecoverRoot at hParentMatchesTrue
          dsimp only at hParentMatchesTrue
          dsimp only [adrs, kp, tree] at hStarDec
          rw [hStarDec] at hParentMatchesTrue
          exact hParentMatchesTrue
        .merkleCollision (extractBaggyMerkleCollision suite sk.pkSeed layer tree
          p.subtreeHeight 0 (baggySubtreeLeaves suite p sk layer tree) ⟨kp, hKpLt⟩ leafStar sigStar.auth hLeafEq hWalkEq)

private theorem pathAt_topLayer_tree_zero (p : BaggyTreeParams) (hWf : p.WellFormed)
    {leafIdx : Nat} (hLeafBound : leafIdx < 2 ^ (p.subtreeHeight * p.numLayers)) :
    (p.pathAt leafIdx (p.numLayers - 1)).2 = 0 := by
  dsimp [BaggyTreeParams.pathAt]
  rw [Nat.div_div_eq_div_mul]
  have hExp : p.subtreeHeight * (p.numLayers - 1) + p.subtreeHeight = p.subtreeHeight * p.numLayers := by
    calc p.subtreeHeight * (p.numLayers - 1) + p.subtreeHeight
      _ = p.subtreeHeight * ((p.numLayers - 1) + 1) := (Nat.mul_succ p.subtreeHeight (p.numLayers - 1)).symm
      _ = p.subtreeHeight * p.numLayers := by
        have hGe1 : 1 ≤ p.numLayers := Nat.le_of_succ_le hWf.1
        rw [Nat.sub_add_cancel hGe1]
  have hPowEq : (2 ^ (p.subtreeHeight * (p.numLayers - 1))) * (2 ^ p.subtreeHeight) =
      2 ^ (p.subtreeHeight * p.numLayers) := by
    rw [← Nat.pow_add, hExp]
  rw [hPowEq]
  exact Nat.div_eq_of_lt hLeafBound

def walkUpperLayersBoundedExtract
    (suite : BaggySuite256) (p : BaggyTreeParams) (sk : BaggySecretKey256)
    (hWf : p.WellFormed) (hGrind : BaggySuite256.WellGrinded suite)
    (approvedMsgs : List (BitVec 256)) (msgStar : BitVec 256)
    (leafIdx : Nat) (hLeafBound : leafIdx < 2 ^ (p.subtreeHeight * p.numLayers)) :
    ∀ (layer : Nat) (sigs : List BaggyLayerSig256) (nodeStar : BitVec 256) (finalRoot : BitVec 256),
      1 ≤ layer →
      1 ≤ sigs.length →
      layer + sigs.length = p.numLayers →
      nodeStar ≠ baggyTrueSubtreeRoot suite p sk (layer - 1) (p.pathAt leafIdx (layer - 1)).2 →
      baggyWalkLayersVerify suite p sk.pkSeed leafIdx layer nodeStar sigs = some finalRoot →
      finalRoot = baggyTrueSubtreeRoot suite p sk (p.numLayers - 1) 0 →
      BaggyUpperReductionResult suite p sk approvedMsgs msgStar
  | _, [], _, _, _, hNeEmpty, _, _, _, _ => False.elim (Nat.not_succ_le_zero 0 hNeEmpty)
  | layer, [topSig], nodeStar, finalRoot, hGe1, _, hSum, hNodeNe, hWalk, hFinalEq =>
    have hTopLayer : layer = p.numLayers - 1 := by simp at hSum; omega
    have hTree0 : (p.pathAt leafIdx layer).2 = 0 := by
      rw [hTopLayer]; exact pathAt_topLayer_tree_zero p hWf hLeafBound
    match hRec : baggyLayerRecoverRoot suite p sk.pkSeed layer (p.pathAt leafIdx layer).2 (p.pathAt leafIdx layer).1 nodeStar topSig with
    | none =>
      False.elim <| by
        unfold baggyWalkLayersVerify at hWalk
        dsimp only at hWalk
        rw [hRec] at hWalk
        cases hWalk
    | some topOut =>
      have hTopOutEq : topOut = finalRoot := by
        unfold baggyWalkLayersVerify at hWalk
        dsimp only at hWalk
        rw [hRec] at hWalk
        unfold baggyWalkLayersVerify at hWalk
        injection hWalk with hE
      have hParentTrue : baggyLayerRecoverRoot suite p sk.pkSeed layer (p.pathAt leafIdx layer).2 (p.pathAt leafIdx layer).1 nodeStar topSig =
          some (baggyTrueSubtreeRoot suite p sk layer (p.pathAt leafIdx layer).2) := by
        rw [hRec, hTopOutEq, hFinalEq, ← hTopLayer, hTree0]
      have hChildNe : nodeStar ≠ baggyCanonicalStaticChildRoot suite p sk layer (p.pathAt leafIdx layer).2 (p.pathAt leafIdx layer).1 := by
        unfold baggyCanonicalStaticChildRoot
        have hPath := baggyChildTreeIdx_pathAt p leafIdx (layer - 1)
        dsimp only at hPath
        have hSucc : (layer - 1) + 1 = layer := Nat.sub_add_cancel hGe1
        rw [hSucc] at hPath
        rw [hPath]
        exact hNodeNe
      extractStaticLayerBreakFromTransition suite p sk hGrind approvedMsgs msgStar leafIdx layer hGe1
        nodeStar topSig hChildNe hParentTrue
  | layer, sigCur :: sigNext :: rest, nodeStar, finalRoot, hGe1, _, hSum, hNodeNe, hWalk, hFinalEq =>
    match hRec : baggyLayerRecoverRoot suite p sk.pkSeed layer (p.pathAt leafIdx layer).2 (p.pathAt leafIdx layer).1 nodeStar sigCur with
    | none =>
      False.elim <| by
        unfold baggyWalkLayersVerify at hWalk
        dsimp only at hWalk
        rw [hRec] at hWalk
        cases hWalk
    | some nextRoot =>
      if hHitTrue : nextRoot = baggyTrueSubtreeRoot suite p sk layer (p.pathAt leafIdx layer).2 then
        have hChildNe : nodeStar ≠ baggyCanonicalStaticChildRoot suite p sk layer (p.pathAt leafIdx layer).2 (p.pathAt leafIdx layer).1 := by
          unfold baggyCanonicalStaticChildRoot
          have hPath := baggyChildTreeIdx_pathAt p leafIdx (layer - 1)
          dsimp only at hPath
          have hSucc : (layer - 1) + 1 = layer := Nat.sub_add_cancel hGe1
          rw [hSucc] at hPath
          rw [hPath]
          exact hNodeNe
        extractStaticLayerBreakFromTransition suite p sk hGrind approvedMsgs msgStar leafIdx layer hGe1
          nodeStar sigCur hChildNe (hRec.trans (congrArg some hHitTrue))
      else
        have hWalkRest : baggyWalkLayersVerify suite p sk.pkSeed leafIdx (layer + 1) nextRoot (sigNext :: rest) = some finalRoot := by
          unfold baggyWalkLayersVerify at hWalk
          dsimp only at hWalk
          rw [hRec] at hWalk
          exact hWalk
        walkUpperLayersBoundedExtract suite p sk hWf hGrind approvedMsgs msgStar leafIdx hLeafBound
          (layer + 1) (sigNext :: rest) nextRoot finalRoot
          (by omega) (by simp) (by simp at hSum ⊢; omega)
          (by simpa [Nat.add_sub_cancel] using hHitTrue) hWalkRest hFinalEq

/-- Upper-hypertree extraction factor over `BaggySuite256`. -/
def baggy_verified_waistband_upper_extract
    (suite : BaggySuite256) (p : BaggyTreeParams) (sk : BaggySecretKey256)
    (hWf : p.WellFormed) (hGrind : BaggySuite256.WellGrinded suite)
    (hLeafDomain : ∀ pk r msg ctr leafIdx,
      suite.hmsgLeaf p pk r msg ctr = some leafIdx →
      leafIdx < 2 ^ (p.subtreeHeight * p.numLayers))
    (sessions : List (VerifiedWaistbandCache × BitVec 256 × UInt32))
    (msgStar : BitVec 256) (sigStar : BaggySig256)
    (hNotSigned : msgStar ∉ sessions.map (fun s => s.2.1))
    (hVerifyStar : baggyVerify suite p (baggyKeygen256 suite p sk) msgStar sigStar = true) :
    BaggyUpperReductionResult suite p sk (sessions.map (fun s => s.2.1)) msgStar :=
  let pk := baggyKeygen256 suite p sk
  have hLenEq : sigStar.layers.length = p.numLayers := by
    unfold baggyVerify at hVerifyStar
    if hNe : sigStar.layers.length != p.numLayers then
      simp [hNe] at hVerifyStar
    else
      cases hB : (sigStar.layers.length == p.numLayers)
      · rw [bne, hB] at hNe; simp at hNe
      · exact eq_of_beq hB
  match hLeaf : suite.hmsgLeaf p pk sigStar.r msgStar sigStar.msgCtr with
  | none =>
    False.elim <| by
      unfold baggyVerify at hVerifyStar
      have hNotBne : (sigStar.layers.length != p.numLayers) = false := by
        rw [bne, beq_iff_eq.mpr hLenEq]; rfl
      rw [ite_neg (by rw [hNotBne]; decide)] at hVerifyStar
      dsimp only [pk] at hLeaf
      rw [hLeaf] at hVerifyStar
      cases hVerifyStar
  | some leafIdx =>
    have hLeafBd := hLeafDomain pk sigStar.r msgStar sigStar.msgCtr leafIdx hLeaf
    match hLayers : sigStar.layers with
    | [] =>
      False.elim <| by
        rw [hLayers, List.length_nil] at hLenEq
        have := hWf.1
        omega
    | [only0] =>
      False.elim <| by
        rw [hLayers, List.length_singleton] at hLenEq
        have := hWf.1
        omega
    | sig0 :: sig1 :: rest =>
      let forsPkStar := suite.forsRecoverPk sk.pkSeed (p.pathAt leafIdx 0).2 (p.pathAt leafIdx 0).1 msgStar sigStar.forsSig
      have hWalk0 : ∃ finalRoot,
          baggyWalkLayersVerify suite p sk.pkSeed leafIdx 0 forsPkStar (sig0 :: sig1 :: rest) = some finalRoot ∧
          finalRoot = baggyTrueSubtreeRoot suite p sk (p.numLayers - 1) 0 := by
        unfold baggyVerify at hVerifyStar
        have hNotBne : (sigStar.layers.length != p.numLayers) = false := by
          rw [bne, beq_iff_eq.mpr hLenEq]; rfl
        rw [ite_neg (by rw [hNotBne]; decide)] at hVerifyStar
        dsimp only [pk] at hLeaf
        rw [hLeaf] at hVerifyStar
        dsimp only [baggyKeygen256] at hVerifyStar
        rw [hLayers] at hVerifyStar
        cases hW : baggyWalkLayersVerify suite p sk.pkSeed leafIdx 0 forsPkStar (sig0 :: sig1 :: rest) with
        | none =>
          dsimp only [forsPkStar] at hW
          rw [hW] at hVerifyStar
          cases hVerifyStar
        | some fr =>
          dsimp only [forsPkStar] at hW
          rw [hW] at hVerifyStar
          exact ⟨fr, rfl, eq_of_beq hVerifyStar⟩
      match hRec0 : baggyLayerRecoverRoot suite p sk.pkSeed 0 (p.pathAt leafIdx 0).2 (p.pathAt leafIdx 0).1 forsPkStar sig0 with
      | none =>
        False.elim <| by
          obtain ⟨fr, hW, _⟩ := hWalk0
          unfold baggyWalkLayersVerify at hW
          dsimp only at hW
          rw [hRec0] at hW
          cases hW
      | some root0Star =>
        if hMatch0 : root0Star = baggyTrueSubtreeRoot suite p sk 0 (p.pathAt leafIdx 0).2 then
          .bottomLayerReachedGenuineRoot leafIdx sigStar.forsSig sig0 hNotSigned
            (hRec0.trans (congrArg some hMatch0))
        else
          have hWalkUpper :
              baggyWalkLayersVerify suite p sk.pkSeed leafIdx 1 root0Star (sig1 :: rest) =
                some (baggyTrueSubtreeRoot suite p sk (p.numLayers - 1) 0) := by
            obtain ⟨fr, hW, hFrEq⟩ := hWalk0
            unfold baggyWalkLayersVerify at hW
            dsimp only at hW
            rw [hRec0] at hW
            rw [← hFrEq]
            exact hW
          walkUpperLayersBoundedExtract suite p sk hWf hGrind (sessions.map (fun s => s.2.1)) msgStar
            leafIdx hLeafBd 1 (sig1 :: rest) root0Star (baggyTrueSubtreeRoot suite p sk (p.numLayers - 1) 0)
            (Nat.le_refl 1) (by simp) (by rw [hLayers] at hLenEq; simp at hLenEq ⊢; omega)
            hMatch0 hWalkUpper rfl

theorem baggy_verified_waistband_upper_reduction
    (suite : BaggySuite256) (p : BaggyTreeParams) (sk : BaggySecretKey256)
    (hWf : p.WellFormed) (hGrind : BaggySuite256.WellGrinded suite)
    (hLeafDomain : ∀ pk r msg ctr leafIdx,
      suite.hmsgLeaf p pk r msg ctr = some leafIdx →
      leafIdx < 2 ^ (p.subtreeHeight * p.numLayers))
    (sessions : List (VerifiedWaistbandCache × BitVec 256 × UInt32))
    (hCanopyMatch : ∀ s ∈ sessions, WaistbandMatchesKey suite p sk s.1)
    (msgStar : BitVec 256) (sigStar : BaggySig256)
    (hNotSigned : msgStar ∉ sessions.map (fun s => s.2.1))
    (hVerifyStar : baggyVerify suite p (baggyKeygen256 suite p sk) msgStar sigStar = true) :
    (∀ r ∈ (baggyRunMultiSessionVerified suite p sk (baggyKeygen256 suite p sk) [] sessions).2.2,
      baggyCanonicalStaticDigits suite p sk r.layer r.tree r.kp = some r.digits) ∧
    Nonempty (BaggyUpperReductionResult suite p sk (sessions.map (fun s => s.2.1)) msgStar) :=
  ⟨fun r hr => ((waistband_verified_multi_session_single_codeword suite p sk
      (baggyKeygen256 suite p sk)).1 sessions [] hCanopyMatch r hr).2.2,
   ⟨baggy_verified_waistband_upper_extract suite p sk hWf hGrind hLeafDomain
      sessions msgStar sigStar hNotSigned hVerifyStar⟩⟩

/-! ### `#tooth` cache-mutation: Corrupted Intermediate `Waistband` Opens 2nd Ancestor Codeword -/

/-- Unhardened `Waistband` cache (`baggy.rs:494` prior to cache-mutation fixes):
    indexed by `(layer, tree, kp)` alone without `expectedSubtreeRoot` chaining or durable `firstSigned`. -/
abbrev UnhardenedWaistbandCache := Nat → Nat → Nat → Option BaggyLayerSig256

def baggySignLayersUnhardenedAux (suite : BaggySuite256) (p : BaggyTreeParams)
    (sk : BaggySecretKey256) (cache : UnhardenedWaistbandCache) (leafIdx : Nat) :
    Nat → Nat → BitVec 256 → Option (List BaggyLayerSig256 × BitVec 256 × List StaticWotsOpeningRecord)
  | _, 0, node => some ([], node, [])
  | layer, rem + 1, node =>
    let (kp, tree) := p.pathAt leafIdx layer
    match (if p.coversLayer layer then cache layer tree kp else none) with
    | some cachedSig =>
      -- `baggy.rs:832-835`: `node` becomes `layer_root(..., node, &cachedSig)` with NO expected-root check!
      match baggyLayerRecoverRoot suite p sk.pkSeed layer tree kp node cachedSig with
      | none => none
      | some nextNode =>
        match baggySignLayersUnhardenedAux suite p sk cache leafIdx (layer + 1) rem nextNode with
        | none => none
        | some (restSigs, topRoot, restRecs) =>
          some (cachedSig :: restSigs, topRoot, restRecs)
    | none =>
      -- `baggy.rs:839-858`: uncached parent derives digits from `node`, then resets `node = levels[hp][0]`!
      match baggySignLayerFresh suite p sk layer tree kp node with
      | none => none
      | some (sig, nextRoot, recOpt) =>
        match baggySignLayersUnhardenedAux suite p sk cache leafIdx (layer + 1) rem nextRoot with
        | none => none
        | some (restSigs, topRoot, restRecs) =>
          let allRecs := match recOpt with | some r => r :: restRecs | none => restRecs
          some (sig :: restSigs, topRoot, allRecs)

/-- Unhardened `baggy_sign_mpc` (`baggy.rs:829-894`): checks `topRoot == pk.pkRoot` BEFORE Round-2
    node opening AND runs `baggyVerify` before returning! -/
def baggySignUnhardened (suite : BaggySuite256) (p : BaggyTreeParams)
    (sk : BaggySecretKey256) (pk : BaggyPublicKey256)
    (cache : UnhardenedWaistbandCache)
    (msg : BitVec 256) (msgCtr : UInt32) : Option (BaggySig256 × List StaticWotsOpeningRecord) :=
  if pk.pkSeed != sk.pkSeed then none
  else
    let r := suite.prfRand sk.skPrf msg
    match suite.hmsgLeaf p pk r msg msgCtr with
    | none => none
    | some leafIdx =>
      let (kp0, tree0) := p.pathAt leafIdx 0
      let (forsSig, forsPk) := suite.forsSign sk.pkSeed sk.skSeed tree0 kp0 msg
      match baggySignLayersUnhardenedAux suite p sk cache leafIdx 0 p.numLayers forsPk with
      | none => none
      | some (layers, topRoot, recs) =>
        if topRoot != pk.pkRoot then none
        else
          let sig : BaggySig256 := { r := r, msgCtr := msgCtr, forsSig := forsSig, layers := layers }
          if baggyVerify suite p pk msg sig then some (sig, recs) else none

/-- Structural unrolling of `qsum`, used to evaluate `qsum` on closed digit maps (the body of
    `qsum` is not exported by `Qsag.Math.Counting`). -/
private def qsumUnrolled : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f =>
    f ⟨0, Nat.zero_lt_succ n⟩ + qsumUnrolled n (fun i => f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)

private theorem qsum_eq_qsumUnrolled : ∀ (n : Nat) (f : Fin n → Nat), qsum n f = qsumUnrolled n f
  | 0, f => qsum_zero f
  | n + 1, f => by
    rw [qsum_succ, qsum_eq_qsumUnrolled n]
    rfl

/-- Concrete constant-sum (`S = 192`) codewords for the 2-codeword top-layer exploit witness:
    - `dBad` (`(0, 3, 1, 2)` + alternating `(1, 2)`)
    - `dGood` (`(3, 0, 2, 1)` + alternating `(1, 2)`)
    - `dRogue` (`(2, 2, 1, 1)` + alternating `(1, 2)`) — dominated by `min(dBad, dGood)` on ALL 128 chains! -/
def dToothBadFn (i : Fin 128) : Fin 4 :=
  if i.val == 0 then ⟨0, by decide⟩
  else if i.val == 1 then ⟨3, by decide⟩
  else if i.val == 2 then ⟨1, by decide⟩
  else if i.val == 3 then ⟨2, by decide⟩
  else if i.val % 2 == 0 then ⟨1, by decide⟩
  else ⟨2, by decide⟩

def dToothGoodFn (i : Fin 128) : Fin 4 :=
  if i.val == 0 then ⟨3, by decide⟩
  else if i.val == 1 then ⟨0, by decide⟩
  else if i.val == 2 then ⟨2, by decide⟩
  else if i.val == 3 then ⟨1, by decide⟩
  else if i.val % 2 == 0 then ⟨1, by decide⟩
  else ⟨2, by decide⟩

def dToothRogueFn (i : Fin 128) : Fin 4 :=
  if i.val == 0 then ⟨2, by decide⟩
  else if i.val == 1 then ⟨2, by decide⟩
  else if i.val == 2 then ⟨1, by decide⟩
  else if i.val == 3 then ⟨1, by decide⟩
  else if i.val % 2 == 0 then ⟨1, by decide⟩
  else ⟨2, by decide⟩

def dToothBad : WotsC256Digits := ⟨dToothBadFn, (qsum_eq_qsumUnrolled _ _).trans rfl⟩
def dToothGood : WotsC256Digits := ⟨dToothGoodFn, (qsum_eq_qsumUnrolled _ _).trans rfl⟩
def dToothRogue : WotsC256Digits := ⟨dToothRogueFn, (qsum_eq_qsumUnrolled _ _).trans rfl⟩

/-- Concrete `BaggySuite256` & 3-layer (`d = 3, h' = 1, L = 2`) instance for cache-mutation. -/
def toothBaggyParams : BaggyTreeParams :=
  { numLayers := 3, subtreeHeight := 1, topLayers := 2 }

def toothRogueRoot : BitVec 256 := 0xDEADBEEF#256

def toothBaggySuite (badRoot1 : BitVec 256) : BaggySuite256 where
  wots :=
    { prf := fun pkSeed skSeed adrs chain =>
        pkSeed ^^^ skSeed ^^^ BitVec.ofNat 256 (adrs.layer.toNat * 1024 + chain.val + 1)
      thF := fun pkSeed _ chain step node =>
        node ^^^ pkSeed ^^^ BitVec.ofNat 256 (256 * (step.val + 1) + chain.val + 7)
      thTl := fun pkSeed adrs ends =>
        pkSeed ^^^ ends ⟨0, by decide⟩ ^^^ ends ⟨1, by decide⟩ ^^^ BitVec.ofNat 256 adrs.keyPair.toNat
      thDigest := fun _ adrs msg _ =>
        if adrs.layer == 2 && msg == badRoot1 then
          packDigits256 dToothBadFn
        else if adrs.layer == 2 && msg == toothRogueRoot then
          packDigits256 dToothRogueFn
        else
          packDigits256 dToothGoodFn }
  thNodeH := fun pkSeed layer _ height _ left right =>
    pkSeed ^^^ (left <<< 1) ^^^ right ^^^ BitVec.ofNat 256 (16 * layer + height + 3)
  paramsDigest := fun p => BitVec.ofNat 256 (p.numLayers * 64 + p.subtreeHeight * 8 + p.topLayers)
  prfRand := fun skPrf msg => skPrf ^^^ msg
  hmsgLeaf := fun _ _ _ _ _ => some 0
  forsSign := fun pkSeed skSeed _ _ msg => (skSeed ^^^ msg, pkSeed ^^^ msg)
  forsRecoverPk := fun pkSeed _ _ msg _ => pkSeed ^^^ msg
  grindCounter := fun _ _ _ => 0

/-- Public 2-codeword top-layer rogue-root forgery routine (`0` access to `skSeed`!):
    combines Session 1 (`chainsBad` for `dToothBad`) and Session 2 (`chainsGood` for `dToothGood`)
    to forge a valid `S = 192` signature on `toothRogueRoot` (`dToothRogue`)! -/
def forgeRogueRootFromTwoTopOpenings (suite : WotsC256HashSuite) (pkSeed : BitVec 256)
    (topAdrs : WotsLeafAdrs)
    (chainsBad chainsGood : Fin 128 → BitVec 256) : Fin 128 → BitVec 256 :=
  fun c =>
    if c.val == 0 then
      -- `dBad 0 = 0`, `dRogue 0 = 2`: step `chainsBad 0` forward through steps `0` and `1`!
      wotsC256AdvanceTo suite pkSeed topAdrs c ⟨0, by decide⟩ (chainsBad c) 2
    else if c.val == 1 then
      -- `dGood 1 = 0`, `dRogue 1 = 2`: step `chainsGood 1` forward through steps `0` and `1`!
      wotsC256AdvanceTo suite pkSeed topAdrs c ⟨0, by decide⟩ (chainsGood c) 2
    else if c.val == 2 then
      -- `dBad 2 = 1 = dRogue 2`!
      chainsBad c
    else if c.val == 3 then
      -- `dGood 3 = 1 = dRogue 3`!
      chainsGood c
    else
      -- For `c ≥ 4`, `dBad c = dGood c = dRogue c`!
      chainsGood c

/-- **`#tooth` Corrupted Intermediate `Waistband` Opens 2nd Ancestor Codeword & Enables Top-Layer Forgery
    (`tooth_corrupted_intermediate_waistband_opens_second_ancestor_codeword`, cache-mutation)**:
    On a 3-layer (`d = 3, h' = 1, L = 2`) `Baggy` hypertree where intermediate layer `1` is cached
    with a single mutated auth-path sibling while top layer `2` is uncached:
    1. **Session 1 (Corrupted Intermediate Cache)**: `baggySignUnhardened` **passes** `pkRoot` self-check,
       **passes** `baggyVerify = true`, and opens codeword **`dToothBad`** at top-layer key `(2, 0, 0)`!
    2. **Session 2 (Clean Cache)**: `baggySignUnhardened` **passes** `pkRoot` self-check, **passes**
       `baggyVerify = true`, and opens a **SECOND distinct codeword `dToothGood ≠ dToothBad`** at the
       **exact same top-layer key `(2, 0, 0)`**!
    3. **Explicit Top-Layer Rogue-Subtree Forgery (`0` `skSeed` access)**: `forgeRogueRootFromTwoTopOpenings`
       uses ONLY the two public top-layer signatures to forge a valid 256-bit `WOTS+C` (`sum = 192`)
       signature (`wotsC256Verify = true`) on a **3rd unseen rogue root `toothRogueRoot`**!
    4. **Hardened `VerifiedWaistbandCache` Blocks the Attack**: `verifyWaistbandCanopy` rejects the
       corrupted intermediate entry (`none`) so `baggySignVerifiedWaistband` NEVER opens `dToothBad`! -/
theorem tooth_corrupted_intermediate_waistband_opens_second_ancestor_codeword :
    let sk : BaggySecretKey256 := { pkSeed := 0x11#256, skSeed := 0x22#256, skPrf := 0x33#256 }
    -- Note: subtree roots of layer 0 and layer 1 do not depend on layer-2 `thDigest`, so we compute
    -- `badRoot1` first using `toothBaggySuite 0#256` where layer 1's leaf is hashed with mutated sibling `0xFF#256`!
    let baseSuite := toothBaggySuite 0#256
    let honestSib1 := baggyMerkleRoot baseSuite sk.pkSeed 1 0 0 1
      (fun _ => (baggySubtreeLeaves baseSuite toothBaggyParams sk 1 0) ⟨1, by decide⟩)
    let mutatedSib1 : BitVec 256 := honestSib1 ^^^ 0xFF#256
    let leaf1_0 := (baggySubtreeLeaves baseSuite toothBaggyParams sk 1 0) ⟨0, by decide⟩
    let badRoot1 := baseSuite.thNodeH sk.pkSeed 1 0 1 0 leaf1_0 mutatedSib1
    let suite := toothBaggySuite badRoot1
    let pk := baggyKeygen256 suite toothBaggyParams sk
    let node0 := baggyTrueSubtreeRoot suite toothBaggyParams sk 0 0
    -- Genuine layer-1 signature on `node0`, vs corrupted `badCachedSig1` with `[mutatedSib1]`!
    let chains1 : Fin 128 → BitVec 256 := fun c =>
      wotsC256PosFrom0 suite.wots sk.pkSeed (baggyLeafAdrs 1 0 0) c
        (suite.wots.prf sk.pkSeed sk.skSeed (baggyLeafAdrs 1 0 0) c) (dToothGoodFn c).val
    let badCachedSig1 : BaggyLayerSig256 := { ctr := 0, chains := chains1, auth := [mutatedSib1] }
    let corruptCache : UnhardenedWaistbandCache := fun l t k =>
      if l == 1 && t == 0 && k == 0 then some badCachedSig1 else none
    let cleanCache : UnhardenedWaistbandCache := fun _ _ _ => none
    let msg1 : BitVec 256 := 0xAA#256
    let msg2 : BitVec 256 := 0xBB#256
    dToothBad ≠ dToothGood ∧
    dToothRogue ≠ dToothBad ∧
    dToothRogue ≠ dToothGood ∧
    badRoot1 ≠ baggyTrueSubtreeRoot suite toothBaggyParams sk 1 0 ∧
    toothRogueRoot ≠ badRoot1 ∧
    toothRogueRoot ≠ baggyTrueSubtreeRoot suite toothBaggyParams sk 1 0 ∧
    (match baggySignUnhardened suite toothBaggyParams sk pk corruptCache msg1 0,
           baggySignUnhardened suite toothBaggyParams sk pk cleanCache msg2 0 with
     | some (sig1, recs1), some (sig2, recs2) =>
       baggyVerify suite toothBaggyParams pk msg1 sig1 = true ∧
       baggyVerify suite toothBaggyParams pk msg2 sig2 = true ∧
       (∃ rBad ∈ recs1, rBad.layer = 2 ∧ rBad.tree = 0 ∧ rBad.kp = 0 ∧ rBad.digits = dToothBad) ∧
       (∃ rGood ∈ recs2, rGood.layer = 2 ∧ rGood.tree = 0 ∧ rGood.kp = 0 ∧ rGood.digits = dToothGood) ∧
       (match sig1.layers, sig2.layers with
        | [_, _, topSig1], [_, _, topSig2] =>
          let forgedTopChains := forgeRogueRootFromTwoTopOpenings suite.wots sk.pkSeed
            (baggyLeafAdrs 2 0 0) topSig1.chains topSig2.chains
          wotsC256Verify suite.wots sk.pkSeed (baggyLeafAdrs 2 0 0)
            (wotsC256PkLeaf suite.wots sk.pkSeed sk.skSeed (baggyLeafAdrs 2 0 0))
            toothRogueRoot 0 forgedTopChains = true
        | _, _ => False)
     | _, _ => False) ∧
    (let hardenedCorruptCache : VerifiedWaistbandCache :=
       { pinnedPkSeed := pk.pkSeed
         pinnedPkRoot := pk.pkRoot
         pinnedParamsDigest := suite.paramsDigest toothBaggyParams
         expectedSubtreeRoot := fun l t =>
           if t == 0 then some (baggyTrueSubtreeRoot suite toothBaggyParams sk l 0) else none
         cachedSig := fun l t k => if l == 1 && t == 0 && k == 0 then some badCachedSig1 else none }
     verifyWaistbandCanopy suite toothBaggyParams pk hardenedCorruptCache 1 0 0 node0 = none) := by
  intro sk baseSuite honestSib1 mutatedSib1 leaf1_0 badRoot1 suite pk node0 chains1 badCachedSig1
        corruptCache cleanCache msg1 msg2
  have hBadNeGood : dToothBad ≠ dToothGood := fun h => by
    have h0 := congrArg (fun x => (x.digits ⟨0, by decide⟩).val) h
    nomatch h0
  have hRogueNeBad : dToothRogue ≠ dToothBad := fun h => by
    have h0 := congrArg (fun x => (x.digits ⟨0, by decide⟩).val) h
    nomatch h0
  have hRogueNeGood : dToothRogue ≠ dToothGood := fun h => by
    have h0 := congrArg (fun x => (x.digits ⟨0, by decide⟩).val) h
    nomatch h0
  have hGoodRoot1Eq : baggyTrueSubtreeRoot suite toothBaggyParams sk 1 0 =
      baseSuite.thNodeH sk.pkSeed 1 0 1 0 leaf1_0 honestSib1 := rfl
  have hBadNeTrue1 : badRoot1 ≠ baggyTrueSubtreeRoot suite toothBaggyParams sk 1 0 := by
    rw [hGoodRoot1Eq]
    decide
  have hRogueNeBadRoot : toothRogueRoot ≠ badRoot1 := by decide
  have hRogueNeGoodRoot : toothRogueRoot ≠ baggyTrueSubtreeRoot suite toothBaggyParams sk 1 0 := by
    rw [hGoodRoot1Eq]
    decide
  -- Helper decoding lemmas for `packDigits256` on our 3 constant-sum digit maps (`0` 256-bit enumeration!).
  have hDecGood : wotsC256DecodeValidDigest (packDigits256 dToothGoodFn) = some dToothGood :=
    wotsC256DecodeValidDigest_pack dToothGood
  have hDecBad : wotsC256DecodeValidDigest (packDigits256 dToothBadFn) = some dToothBad :=
    wotsC256DecodeValidDigest_pack dToothBad
  have hDecRogue : wotsC256DecodeValidDigest (packDigits256 dToothRogueFn) = some dToothRogue :=
    wotsC256DecodeValidDigest_pack dToothRogue
  have hLayer1RecoversBad :
      baggyLayerRecoverRoot suite toothBaggyParams sk.pkSeed 1 0 0 node0 badCachedSig1 = some badRoot1 := by
    unfold baggyLayerRecoverRoot
    dsimp only [badCachedSig1]
    have hDig1 : suite.wots.thDigest sk.pkSeed (baggyLeafAdrs 1 0 0) node0 0 = packDigits256 dToothGoodFn := rfl
    rw [hDig1, hDecGood]
    dsimp only
    have hEnds1 :
        (fun c => wotsC256CompleteTo3 suite.wots sk.pkSeed (baggyLeafAdrs 1 0 0) c (dToothGood.digits c) (chains1 c)) =
        (fun c => wotsC256PosFrom0 suite.wots sk.pkSeed (baggyLeafAdrs 1 0 0) c
          (suite.wots.prf sk.pkSeed sk.skSeed (baggyLeafAdrs 1 0 0) c) 3) := by
      funext c
      exact wotsC256CompleteTo3_honest_eq suite.wots sk.pkSeed (baggyLeafAdrs 1 0 0) c _ (dToothGood.digits c)
    rw [hEnds1]
    rfl
  have hDig0 : ∀ m : BitVec 256,
      suite.wots.thDigest sk.pkSeed (baggyLeafAdrs 0 0 0) m 0 = packDigits256 dToothGoodFn := fun _ => rfl
  have hDig1Good : suite.wots.thDigest sk.pkSeed (baggyLeafAdrs 1 0 0) node0 0 = packDigits256 dToothGoodFn := rfl
  have hDig2Bad : suite.wots.thDigest sk.pkSeed (baggyLeafAdrs 2 0 0) badRoot1 0 = packDigits256 dToothBadFn := by
    dsimp [suite, toothBaggySuite, baggyLeafAdrs]
    simp
  have hDig2Good : suite.wots.thDigest sk.pkSeed (baggyLeafAdrs 2 0 0)
      (baggyTrueSubtreeRoot suite toothBaggyParams sk 1 0) 0 = packDigits256 dToothGoodFn := by
    change (if ((baggyLeafAdrs 2 0 0).layer == 2 &&
                baggyTrueSubtreeRoot suite toothBaggyParams sk 1 0 == badRoot1) then
              packDigits256 dToothBadFn
            else if ((baggyLeafAdrs 2 0 0).layer == 2 &&
                     baggyTrueSubtreeRoot suite toothBaggyParams sk 1 0 == toothRogueRoot) then
              packDigits256 dToothRogueFn
            else packDigits256 dToothGoodFn) = packDigits256 dToothGoodFn
    have hL2 : ((baggyLeafAdrs 2 0 0).layer == 2) = true := rfl
    have h1 : (baggyTrueSubtreeRoot suite toothBaggyParams sk 1 0 == badRoot1) = false :=
      beq_false_of_ne hBadNeTrue1.symm
    have h2 : (baggyTrueSubtreeRoot suite toothBaggyParams sk 1 0 == toothRogueRoot) = false :=
      beq_false_of_ne hRogueNeGoodRoot.symm
    rw [hL2, h1, h2]
    rfl
  have hDig2Rogue : suite.wots.thDigest sk.pkSeed (baggyLeafAdrs 2 0 0) toothRogueRoot 0 = packDigits256 dToothRogueFn := by
    dsimp [suite, toothBaggySuite, baggyLeafAdrs]
    have h1 : (toothRogueRoot == badRoot1) = false := beq_false_of_ne hRogueNeBadRoot
    simp [h1]
  -- Evaluate `baggySignLayerFresh` on layers 0, 1, and 2 (on both `badRoot1` and `goodRoot1`) symbolically!
  have hFreshEval : ∀ (layer : Nat) (child : BitVec 256) (d : WotsC256Digits)
      (hD : wotsC256DecodeValidDigest (suite.wots.thDigest sk.pkSeed (baggyLeafAdrs layer 0 0) child 0) = some d),
      ∃ (sig : BaggyLayerSig256),
        sig.chains = (fun c => wotsC256PosFrom0 suite.wots sk.pkSeed (baggyLeafAdrs layer 0 0) c
          (suite.wots.prf sk.pkSeed sk.skSeed (baggyLeafAdrs layer 0 0) c) (d.digits c).val) ∧
        baggyLayerRecoverRoot suite toothBaggyParams sk.pkSeed layer 0 0 child sig =
          some (baggyTrueSubtreeRoot suite toothBaggyParams sk layer 0) ∧
        baggySignLayerFresh suite toothBaggyParams sk layer 0 0 child =
          some (sig, baggyTrueSubtreeRoot suite toothBaggyParams sk layer 0,
            if 1 ≤ layer then some { layer := layer, tree := 0, kp := 0, signedNode := child, digits := d } else none) := by
    intro layer child d hD
    have hKp : 0 < 2 ^ toothBaggyParams.subtreeHeight := by decide
    have hSign : wotsC256Sign suite.wots sk.pkSeed sk.skSeed (baggyLeafAdrs layer 0 0) child 0 =
        some (fun c => wotsC256PosFrom0 suite.wots sk.pkSeed (baggyLeafAdrs layer 0 0) c
          (suite.wots.prf sk.pkSeed sk.skSeed (baggyLeafAdrs layer 0 0) c) (d.digits c).val) := by
      unfold wotsC256Sign
      rw [hD]
    let sigOut : BaggyLayerSig256 :=
      { ctr := 0
        chains := fun c => wotsC256PosFrom0 suite.wots sk.pkSeed (baggyLeafAdrs layer 0 0) c
          (suite.wots.prf sk.pkSeed sk.skSeed (baggyLeafAdrs layer 0 0) c) (d.digits c).val
        auth := baggyMerkleAuthPath suite sk.pkSeed layer 0 toothBaggyParams.subtreeHeight 0
          (baggySubtreeLeaves suite toothBaggyParams sk layer 0) 0 }
    have hFreshEq : baggySignLayerFresh suite toothBaggyParams sk layer 0 0 child =
        some (sigOut, baggyTrueSubtreeRoot suite toothBaggyParams sk layer 0,
          if 1 ≤ layer then some { layer := layer, tree := 0, kp := 0, signedNode := child, digits := d } else none) := by
      unfold baggySignLayerFresh
      rw [dite_pos hKp]
      dsimp only
      have hCtr0 : suite.grindCounter sk.pkSeed (baggyLeafAdrs layer 0 0) child = 0 := rfl
      rw [hCtr0, hD, hSign]
      rfl
    obtain ⟨_, hRecOk, _⟩ := baggySignLayerFresh_props suite toothBaggyParams sk layer 0 0 child hFreshEq
    exact ⟨sigOut, rfl, hRecOk, hFreshEq⟩
  obtain ⟨sig0_1, _, hRec0_1, hFresh0_1⟩ := hFreshEval 0 (sk.pkSeed ^^^ msg1) dToothGood (by rw [hDig0]; exact hDecGood)
  obtain ⟨sig0_2, _, hRec0_2, hFresh0_2⟩ := hFreshEval 0 (sk.pkSeed ^^^ msg2) dToothGood (by rw [hDig0]; exact hDecGood)
  obtain ⟨sig1_clean, _, hRec1_clean, hFresh1_clean⟩ := hFreshEval 1 node0 dToothGood (by rw [hDig1Good]; exact hDecGood)
  obtain ⟨topSigBad, hTopChainsBad, hRec2_bad, hFresh2_bad⟩ := hFreshEval 2 badRoot1 dToothBad (by rw [hDig2Bad]; exact hDecBad)
  obtain ⟨topSigGood, hTopChainsGood, hRec2_good, hFresh2_good⟩ := hFreshEval 2
    (baggyTrueSubtreeRoot suite toothBaggyParams sk 1 0) dToothGood (by rw [hDig2Good]; exact hDecGood)
  have hNotLe10 : ¬ ((1 : Nat) ≤ 0) := by decide
  have hLe11 : (1 : Nat) ≤ 1 := by decide
  have hLe12 : (1 : Nat) ≤ 2 := by decide
  rw [ite_neg hNotLe10] at hFresh0_1 hFresh0_2
  rw [ite_pos hLe11] at hFresh1_clean
  rw [ite_pos hLe12] at hFresh2_bad hFresh2_good
  have hRec1_bad' :
      baggyLayerRecoverRoot suite toothBaggyParams sk.pkSeed 1 0 0
        (baggyTrueSubtreeRoot suite toothBaggyParams sk 0 0) badCachedSig1 = some badRoot1 :=
    hLayer1RecoversBad
  have hRec1_clean' :
      baggyLayerRecoverRoot suite toothBaggyParams sk.pkSeed 1 0 0
        (baggyTrueSubtreeRoot suite toothBaggyParams sk 0 0) sig1_clean =
        some (baggyTrueSubtreeRoot suite toothBaggyParams sk 1 0) :=
    hRec1_clean
  have hFresh1_clean' :
      baggySignLayerFresh suite toothBaggyParams sk 1 0 0 (baggyTrueSubtreeRoot suite toothBaggyParams sk 0 0) =
        some (sig1_clean, baggyTrueSubtreeRoot suite toothBaggyParams sk 1 0,
          some { layer := 1, tree := 0, kp := 0, signedNode := node0, digits := dToothGood }) :=
    hFresh1_clean
  refine ⟨hBadNeGood, hRogueNeBad, hRogueNeGood, hBadNeTrue1, hRogueNeBadRoot, hRogueNeGoodRoot, ?_, ?_⟩
  · have hPath0 : ∀ l, toothBaggyParams.pathAt 0 l = (0, 0) := fun _ => by simp [BaggyTreeParams.pathAt]
    have hCov0 : toothBaggyParams.coversLayer 0 = false := by decide
    have hCov1 : toothBaggyParams.coversLayer 1 = true := by decide
    have hCov2 : toothBaggyParams.coversLayer 2 = true := by decide
    have hNum : toothBaggyParams.numLayers = 3 := rfl
    have hVer1 : baggyVerify suite toothBaggyParams pk msg1
        { r := suite.prfRand sk.skPrf msg1, msgCtr := 0, forsSig := sk.skSeed ^^^ msg1,
          layers := [sig0_1, badCachedSig1, topSigBad] } = true := by
      unfold baggyVerify
      have hL : ([sig0_1, badCachedSig1, topSigBad].length != toothBaggyParams.numLayers) = false := rfl
      have hH : suite.hmsgLeaf toothBaggyParams pk (suite.prfRand sk.skPrf msg1) msg1 0 = some 0 := rfl
      have hPkS : pk.pkSeed = sk.pkSeed := rfl
      have hPkR : pk.pkRoot = baggyTrueSubtreeRoot suite toothBaggyParams sk 2 0 := rfl
      rw [ite_neg (by rw [hL]; decide), hH]
      dsimp only
      rw [hPath0 0, hPkS]
      dsimp only
      have hFRec : suite.forsRecoverPk sk.pkSeed 0 0 msg1 (sk.skSeed ^^^ msg1) = sk.pkSeed ^^^ msg1 := rfl
      rw [hFRec]
      dsimp only [baggyWalkLayersVerify]
      simp only [hPath0 0, hPath0 1, hPath0 2,
        hRec0_1, hRec1_bad', hRec2_bad, hPkR, beq_self_eq_true]
    have hVer2 : baggyVerify suite toothBaggyParams pk msg2
        { r := suite.prfRand sk.skPrf msg2, msgCtr := 0, forsSig := sk.skSeed ^^^ msg2,
          layers := [sig0_2, sig1_clean, topSigGood] } = true := by
      unfold baggyVerify
      have hL : ([sig0_2, sig1_clean, topSigGood].length != toothBaggyParams.numLayers) = false := rfl
      have hH : suite.hmsgLeaf toothBaggyParams pk (suite.prfRand sk.skPrf msg2) msg2 0 = some 0 := rfl
      have hPkS : pk.pkSeed = sk.pkSeed := rfl
      have hPkR : pk.pkRoot = baggyTrueSubtreeRoot suite toothBaggyParams sk 2 0 := rfl
      rw [ite_neg (by rw [hL]; decide), hH]
      dsimp only
      rw [hPath0 0, hPkS]
      dsimp only
      have hFRec : suite.forsRecoverPk sk.pkSeed 0 0 msg2 (sk.skSeed ^^^ msg2) = sk.pkSeed ^^^ msg2 := rfl
      rw [hFRec]
      dsimp only [baggyWalkLayersVerify]
      simp only [hPath0 0, hPath0 1, hPath0 2,
        hRec0_2, hRec1_clean', hRec2_good, hPkR, beq_self_eq_true]
    have hUnhard1 : baggySignUnhardened suite toothBaggyParams sk pk corruptCache msg1 0 =
        some ({ r := suite.prfRand sk.skPrf msg1, msgCtr := 0, forsSig := sk.skSeed ^^^ msg1,
                layers := [sig0_1, badCachedSig1, topSigBad] },
              [{ layer := 2, tree := 0, kp := 0, signedNode := badRoot1, digits := dToothBad }]) := by
      unfold baggySignUnhardened
      have hPkS : pk.pkSeed = sk.pkSeed := rfl
      have hSeedBne : (pk.pkSeed != sk.pkSeed) = false := by
        rw [hPkS]; exact bne_self_eq_false _
      rw [ite_neg (by rw [hSeedBne]; decide)]
      have hHm1 : suite.hmsgLeaf toothBaggyParams pk (suite.prfRand sk.skPrf msg1) msg1 0 = some 0 := rfl
      dsimp only
      rw [hHm1]
      dsimp only
      rw [hPath0 0]
      dsimp only
      have hForsFst : (suite.forsSign sk.pkSeed sk.skSeed 0 0 msg1).1 = sk.skSeed ^^^ msg1 := rfl
      have hForsSnd : (suite.forsSign sk.pkSeed sk.skSeed 0 0 msg1).2 = sk.pkSeed ^^^ msg1 := rfl
      rw [hForsFst, hForsSnd, hNum]
      have hLayers1 :
          baggySignLayersUnhardenedAux suite toothBaggyParams sk corruptCache 0 0 3 (sk.pkSeed ^^^ msg1) =
            some ([sig0_1, badCachedSig1, topSigBad], baggyTrueSubtreeRoot suite toothBaggyParams sk 2 0,
              [{ layer := 2, tree := 0, kp := 0, signedNode := badRoot1, digits := dToothBad }]) := by
        dsimp only [baggySignLayersUnhardenedAux]
        have hC1 : corruptCache 1 0 0 = some badCachedSig1 := rfl
        have hC2 : corruptCache 2 0 0 = none := rfl
        simp only [hPath0 0, hPath0 1, hPath0 2, hCov0, hCov1, hCov2,
          Bool.false_eq_true, ite_false, ite_true, hFresh0_1, hC1, hRec1_bad', hC2, hFresh2_bad]
      rw [hLayers1]
      dsimp only
      have hPkR : pk.pkRoot = baggyTrueSubtreeRoot suite toothBaggyParams sk 2 0 := rfl
      have hTopBne : (baggyTrueSubtreeRoot suite toothBaggyParams sk 2 0 != pk.pkRoot) = false := by
        rw [hPkR]; exact bne_self_eq_false _
      rw [ite_neg (by rw [hTopBne]; decide), ite_pos hVer1]
    have hUnhard2 : baggySignUnhardened suite toothBaggyParams sk pk cleanCache msg2 0 =
        some ({ r := suite.prfRand sk.skPrf msg2, msgCtr := 0, forsSig := sk.skSeed ^^^ msg2,
                layers := [sig0_2, sig1_clean, topSigGood] },
              [{ layer := 1, tree := 0, kp := 0, signedNode := node0, digits := dToothGood },
               { layer := 2, tree := 0, kp := 0, signedNode := baggyTrueSubtreeRoot suite toothBaggyParams sk 1 0, digits := dToothGood }]) := by
      unfold baggySignUnhardened
      have hPkS : pk.pkSeed = sk.pkSeed := rfl
      have hSeedBne : (pk.pkSeed != sk.pkSeed) = false := by
        rw [hPkS]; exact bne_self_eq_false _
      rw [ite_neg (by rw [hSeedBne]; decide)]
      have hHm2 : suite.hmsgLeaf toothBaggyParams pk (suite.prfRand sk.skPrf msg2) msg2 0 = some 0 := rfl
      dsimp only
      rw [hHm2]
      dsimp only
      rw [hPath0 0]
      dsimp only
      have hForsFst : (suite.forsSign sk.pkSeed sk.skSeed 0 0 msg2).1 = sk.skSeed ^^^ msg2 := rfl
      have hForsSnd : (suite.forsSign sk.pkSeed sk.skSeed 0 0 msg2).2 = sk.pkSeed ^^^ msg2 := rfl
      rw [hForsFst, hForsSnd, hNum]
      have hLayers2 :
          baggySignLayersUnhardenedAux suite toothBaggyParams sk cleanCache 0 0 3 (sk.pkSeed ^^^ msg2) =
            some ([sig0_2, sig1_clean, topSigGood], baggyTrueSubtreeRoot suite toothBaggyParams sk 2 0,
              [{ layer := 1, tree := 0, kp := 0, signedNode := node0, digits := dToothGood },
               { layer := 2, tree := 0, kp := 0, signedNode := baggyTrueSubtreeRoot suite toothBaggyParams sk 1 0, digits := dToothGood }]) := by
        dsimp only [baggySignLayersUnhardenedAux]
        have hC1 : cleanCache 1 0 0 = none := rfl
        have hC2 : cleanCache 2 0 0 = none := rfl
        simp only [hPath0 0, hPath0 1, hPath0 2, hCov0, hCov1, hCov2,
          Bool.false_eq_true, ite_false, ite_true, hFresh0_2, hC1, hFresh1_clean', hC2, hFresh2_good]
      rw [hLayers2]
      dsimp only
      have hPkR : pk.pkRoot = baggyTrueSubtreeRoot suite toothBaggyParams sk 2 0 := rfl
      have hTopBne : (baggyTrueSubtreeRoot suite toothBaggyParams sk 2 0 != pk.pkRoot) = false := by
        rw [hPkR]; exact bne_self_eq_false _
      rw [ite_neg (by rw [hTopBne]; decide), ite_pos hVer2]
    rw [hUnhard1, hUnhard2]
    refine ⟨hVer1, hVer2,
      ⟨_, .head _, rfl, rfl, rfl, rfl⟩,
      ⟨_, .tail _ (.head _), rfl, rfl, rfl, rfl⟩, ?_⟩
    -- Prove the forged 3rd top-layer signature on `toothRogueRoot` verifies (`wotsC256Verify = true`)!
    unfold wotsC256Verify wotsC256PkLeaf
    rw [hDig2Rogue, hDecRogue]
    dsimp only
    have hForgedEnds :
        (fun c => wotsC256CompleteTo3 suite.wots sk.pkSeed (baggyLeafAdrs 2 0 0) c (dToothRogue.digits c)
          (forgeRogueRootFromTwoTopOpenings suite.wots sk.pkSeed (baggyLeafAdrs 2 0 0)
            topSigBad.chains topSigGood.chains c)) =
        (fun c => wotsC256PosFrom0 suite.wots sk.pkSeed (baggyLeafAdrs 2 0 0) c
          (suite.wots.prf sk.pkSeed sk.skSeed (baggyLeafAdrs 2 0 0) c) 3) := by
      funext c
      rw [hTopChainsBad, hTopChainsGood]
      unfold forgeRogueRootFromTwoTopOpenings dToothRogue dToothBad dToothGood
      dsimp only
      if hc0 : c.val == 0 then
        have hVal0 : c = ⟨0, by decide⟩ := Fin.ext (eq_of_beq hc0)
        subst hVal0
        rfl
      else if hc1 : c.val == 1 then
        have hVal1 : c = ⟨1, by decide⟩ := Fin.ext (eq_of_beq hc1)
        subst hVal1
        rfl
      else if hc2 : c.val == 2 then
        have hVal2 : c = ⟨2, by decide⟩ := Fin.ext (eq_of_beq hc2)
        subst hVal2
        rfl
      else if hc3 : c.val == 3 then
        have hVal3 : c = ⟨3, by decide⟩ := Fin.ext (eq_of_beq hc3)
        subst hVal3
        rfl
      else
        simp only [hc0, hc1, hc2, hc3, Bool.false_eq_true, ↓reduceIte, dToothRogueFn, dToothGoodFn]
        exact wotsC256CompleteTo3_honest_eq suite.wots sk.pkSeed (baggyLeafAdrs 2 0 0) c _ _
    rw [hForgedEnds, beq_self_eq_true]
  · -- Prove `verifyWaistbandCanopy` rejects `badCachedSig1` because `some badRoot1 != some goodRoot1`!
    intro hardenedCorruptCache
    unfold verifyWaistbandCanopy
    have hGuardOk : ((hardenedCorruptCache.pinnedPkSeed != pk.pkSeed ||
        hardenedCorruptCache.pinnedPkRoot != pk.pkRoot ||
        hardenedCorruptCache.pinnedParamsDigest != suite.paramsDigest toothBaggyParams ||
        !toothBaggyParams.coversLayer 1)) = false := by
      dsimp only [hardenedCorruptCache]
      simp only [bne_self_eq_false, Bool.false_or]
      decide
    rw [ite_neg (by rw [hGuardOk]; decide)]
    have hExp0 : hardenedCorruptCache.expectedSubtreeRoot (1 - 1) (baggyChildTreeIdx toothBaggyParams 0 0) =
        some node0 := rfl
    have hExp1 : hardenedCorruptCache.expectedSubtreeRoot 1 0 =
        some (baggyTrueSubtreeRoot suite toothBaggyParams sk 1 0) := rfl
    have hCSig1 : hardenedCorruptCache.cachedSig 1 0 0 = some badCachedSig1 := rfl
    rw [hExp0, hExp1, hCSig1]
    dsimp only
    have hChildEq : (node0 != node0) = false := bne_self_eq_false _
    rw [ite_neg (by rw [hChildEq]; decide)]
    have hPkSeedEq : pk.pkSeed = sk.pkSeed := rfl
    rw [hPkSeedEq, hLayer1RecoversBad]
    have hRootBne : (some badRoot1 != some (baggyTrueSubtreeRoot suite toothBaggyParams sk 1 0)) = true := by
      rw [bne]
      have hNeOpt : some badRoot1 ≠ some (baggyTrueSubtreeRoot suite toothBaggyParams sk 1 0) :=
        fun h => hBadNeTrue1 (Option.some.inj h)
      rw [beq_false_of_ne hNeOpt]
      rfl
    rw [ite_pos hRootBne]

/-! ## 4. Non-Vacuity Witnesses (`inhabited_*`) -/

/-- Non-vacuity witness for Section 1 (`WotsC256Digits`, `extractStrictDropIdx`, `wotsC256Sign`, `wotsC256Verify`). -/
theorem inhabited_wotsC256_incomparability_and_signing :
    ∃ (d1 d2 : WotsC256Digits) (hNe : d1 ≠ d2) (suite : WotsC256HashSuite)
      (pkSeed skSeed msg : BitVec 256) (adrs : WotsLeafAdrs) (sig : Fin 128 → BitVec 256),
      (d2.digits (extractStrictDropIdx d1 d2 hNe).1).val <
        (d1.digits (extractStrictDropIdx d1 d2 hNe).1).val ∧
      wotsC256Sign suite pkSeed skSeed adrs msg 0 = some sig ∧
      wotsC256Verify suite pkSeed adrs (wotsC256PkLeaf suite pkSeed skSeed adrs) msg 0 sig = true := by
  have hNe : dToothGood ≠ dToothBad := fun h => by
    have h0 := congrArg (fun x => (x.digits ⟨0, by decide⟩).val) h
    nomatch h0
  let suite := (toothBaggySuite 0#256).wots
  let adrs : WotsLeafAdrs := { layer := 0, tree := 0, keyPair := 0 }
  have hDec : wotsC256DecodeValidDigest (suite.thDigest 0x11#256 adrs 0x44#256 0) = some dToothGood := by
    have hd : suite.thDigest 0x11#256 adrs 0x44#256 0 = packDigits256 dToothGoodFn := rfl
    rw [hd]
    exact wotsC256DecodeValidDigest_pack dToothGood
  let sig : Fin 128 → BitVec 256 := fun c =>
    wotsC256PosFrom0 suite 0x11#256 adrs c (suite.prf 0x11#256 0x22#256 adrs c) (dToothGood.digits c).val
  have hSign : wotsC256Sign suite 0x11#256 0x22#256 adrs 0x44#256 0 = some sig := by
    unfold wotsC256Sign; rw [hDec]
  exact ⟨dToothGood, dToothBad, hNe, suite, 0x11#256, 0x22#256, 0x44#256, adrs, sig,
    (extractStrictDropIdx dToothGood dToothBad hNe).2, hSign,
    wotsC256_sign_verify_complete suite 0x11#256 0x22#256 adrs 0x44#256 0 sig hSign⟩

/-- Non-vacuity witness for Section 2 (`Rss256Engine` 1-corrupt privacy + 2-challenge `BGIN19` soundness + sticky poison). -/
theorem inhabited_rss256_privacy_soundness_and_poison :
    ∃ (x y : RssPlane256Share) (w : Bgin19Deg2Witness) (waveCoeffs : List Tower128)
      (ops : List Rss256BarrierOp),
      x.reconstruct ≠ 0#256 ∧
      y.reconstruct ≠ 0#256 ∧
      w.Valid ∧
      waveCoeffs.length ≤ 2 * 2 ∧
      (∃ c ∈ waveCoeffs, c ≠ towerZero 7) ∧
      ratLe (qsum ((2 ^ 128) * (2 ^ 128))
        (fun ω => if postWaveTwoChallengeAccepts waveCoeffs ω then 1 else 0), (2 ^ 128) ^ 2)
        ((2 * 2) ^ 2, (2 ^ 128) ^ 2) ∧
      (rss256BarrierTrace rss256BarrierStep Rss256BarrierState.init ops).2 = [0xABCD#256] ∧
      (rss256BarrierTrace rss256BarrierStep Rss256BarrierState.init ops).1.poisoned = true := by
  let x : RssPlane256Share := { s0 := 1#256, s1 := 2#256, s2 := 4#256 }
  let y : RssPlane256Share := { s0 := 3#256, s1 := 5#256, s2 := 0#256 }
  let oneSh : RssTower128Share := { s0 := towerOne 7, s1 := towerZero 7, s2 := towerZero 7 }
  let zeroSh : RssTower128Share := { s0 := towerZero 7, s1 := towerZero 7, s2 := towerZero 7 }
  let w : Bgin19Deg2Witness :=
    { x0 := oneSh, y0 := oneSh, dx := oneSh, dy := oneSh, c1 := zeroSh, c2 := oneSh }
  have hValid : w.Valid := by
    constructor <;> simp [w, oneSh, zeroSh, RssTower128Share.reconstruct]
  let waveCoeffs : List Tower128 := [towerOne 7, towerX 7]
  have hDeg : waveCoeffs.length ≤ 2 * 2 := by decide
  have hNz : ∃ c ∈ waveCoeffs, c ≠ towerZero 7 := ⟨towerOne 7, .head _, towerOne_ne_zero 7⟩
  let ops : List Rss256BarrierOp :=
    [.permuteInline true 0xABCD#256, .check, .openPlanes,
     .permuteInline false 0xFFFF#256, .check, .check, .openPlanes]
  exact ⟨x, y, w, waveCoeffs, ops, by decide, by decide, hValid, hDeg, hNz,
    (rss256_post_wave_two_challenge_bgin19_soundness 2 waveCoeffs hDeg hNz).2, rfl, rfl⟩

/-- Minimal hash oracle for the existence witness. The security statements remain
    parameterized by the hash suite; inhabitedness must not evaluate a hash implementation. -/
def inhabitedBaggySuite : BaggySuite256 :=
  { toothBaggySuite 0#256 with
    wots :=
      { prf := fun _ _ _ _ => 0#256
        thF := fun _ _ _ _ node => node
        thTl := fun _ _ _ => 0#256
        thDigest := fun _ _ _ _ => packDigits256 dToothGoodFn }
    thNodeH := fun _ _ _ _ _ _ _ => 0#256 }

/- Keep witness evaluation behind small equations. In particular, never ask `dsimp`
   to normalize signing while its valid-digest match is still unreduced. -/
private theorem inhabitedBaggy_pos (seed : BitVec 256) (adrs : WotsLeafAdrs)
    (c : Fin 128) (n : Nat) :
    wotsC256PosFrom0 inhabitedBaggySuite.wots seed adrs c 0#256 n = 0#256 := by
  cases n with
  | zero => rfl
  | succ n => cases n with
    | zero => rfl
    | succ n => cases n <;> rfl

private def inhabitedLayerSig : BaggyLayerSig256 :=
  { ctr := 0, chains := fun _ => 0#256, auth := [0#256] }

private theorem inhabitedBaggy_sign (seed secret msg : BitVec 256) (adrs : WotsLeafAdrs) :
    wotsC256Sign inhabitedBaggySuite.wots seed secret adrs msg 0 =
      some (fun _ : Fin 128 => 0#256) := by
  unfold wotsC256Sign
  change (match wotsC256DecodeValidDigest (packDigits256 dToothGoodFn) with
    | none => none
    | some d => some (fun c => wotsC256PosFrom0 inhabitedBaggySuite.wots seed adrs c
        0#256 (d.digits c).val)) = some (fun _ : Fin 128 => 0#256)
  have hDec : wotsC256DecodeValidDigest (packDigits256 dToothGoodFn) = some dToothGood :=
    wotsC256DecodeValidDigest_pack dToothGood
  rw [hDec]
  simp only [inhabitedBaggy_pos]

private theorem inhabitedBaggy_recover (seed node : BitVec 256) (layer : Nat) :
    baggyLayerRecoverRoot inhabitedBaggySuite toothBaggyParams seed layer 0 0 node
      inhabitedLayerSig = some (0#256) := by
  change (match wotsC256DecodeValidDigest (packDigits256 dToothGoodFn) with
    | none => none | some _ => some (0#256)) = some (0#256)
  have hDec : wotsC256DecodeValidDigest (packDigits256 dToothGoodFn) = some dToothGood :=
    wotsC256DecodeValidDigest_pack dToothGood
  rw [hDec]

private theorem inhabitedBaggy_fresh (sk : BaggySecretKey256) (layer : Nat) (node : BitVec 256) :
    baggySignLayerFresh inhabitedBaggySuite toothBaggyParams sk layer 0 0 node =
      some (inhabitedLayerSig, 0#256,
        if 1 ≤ layer then some { layer := layer, tree := 0, kp := 0, signedNode := node, digits := dToothGood } else none) := by
  change ((match wotsC256DecodeValidDigest (packDigits256 dToothGoodFn),
      wotsC256Sign inhabitedBaggySuite.wots sk.pkSeed sk.skSeed (baggyLeafAdrs layer 0 0) node 0 with
    | some d, some chains => some ({ ctr := 0, chains := chains, auth := [0#256] }, 0#256,
        if 1 ≤ layer then some { layer := layer, tree := 0, kp := 0, signedNode := node, digits := d } else none)
    | _, _ => none) : Option (BaggyLayerSig256 × BitVec 256 × Option StaticWotsOpeningRecord)) = _
  have hDec : wotsC256DecodeValidDigest (packDigits256 dToothGoodFn) = some dToothGood :=
    wotsC256DecodeValidDigest_pack dToothGood
  rw [hDec, inhabitedBaggy_sign]
  rfl

private def inhabitedKey : BaggySecretKey256 :=
  { pkSeed := 0#256, skSeed := 0#256, skPrf := 0#256 }

private def inhabitedPk : BaggyPublicKey256 :=
  baggyKeygen256 inhabitedBaggySuite toothBaggyParams inhabitedKey

private def inhabitedCache : VerifiedWaistbandCache :=
  { pinnedPkSeed := inhabitedPk.pkSeed
    pinnedPkRoot := inhabitedPk.pkRoot
    pinnedParamsDigest := inhabitedBaggySuite.paramsDigest toothBaggyParams
    expectedSubtreeRoot := fun _ t => if t == 0 then some 0#256 else none
    cachedSig := fun l t k => if l == 2 && t == 0 && k == 0 then some inhabitedLayerSig else none }

private def inhabitedRecord : StaticWotsOpeningRecord :=
  { layer := 1, tree := 0, kp := 0, signedNode := 0#256, digits := dToothGood }

private def inhabitedGuard : DurableStaticWotsGuard := [(1, 0, 0, dToothGood)]

private def inhabitedSignature (msg : BitVec 256) : BaggySig256 :=
  { r := 0#256 ^^^ msg, msgCtr := 0, forsSig := 0#256 ^^^ msg
    layers := [inhabitedLayerSig, inhabitedLayerSig, inhabitedLayerSig] }

private theorem inhabited_path (l : Nat) : toothBaggyParams.pathAt 0 l = (0, 0) := by
  simp [BaggyTreeParams.pathAt]

private theorem inhabited_cache0 (node : BitVec 256) :
    verifyWaistbandCanopy inhabitedBaggySuite toothBaggyParams inhabitedPk inhabitedCache 0 0 0 node = none := rfl

private theorem inhabited_cache1 (node : BitVec 256) :
    verifyWaistbandCanopy inhabitedBaggySuite toothBaggyParams inhabitedPk inhabitedCache 1 0 0 node = none := rfl

private theorem inhabited_cache2 :
    verifyWaistbandCanopy inhabitedBaggySuite toothBaggyParams inhabitedPk inhabitedCache 2 0 0 0#256 =
      some (inhabitedLayerSig, 0#256) := by
  change (if baggyLayerRecoverRoot inhabitedBaggySuite toothBaggyParams 0#256 2 0 0 0#256
      inhabitedLayerSig != some 0#256 then none else some (inhabitedLayerSig, 0#256)) = _
  rw [inhabitedBaggy_recover]
  rfl

private theorem inhabited_cachedSig0 : (inhabitedCache.cachedSig 0 0 0).isSome = false := rfl

private theorem inhabited_cachedSig1 : (inhabitedCache.cachedSig 1 0 0).isSome = false := rfl

private theorem inhabited_layers (node : BitVec 256) :
    baggySignLayersVerifiedCacheAux inhabitedBaggySuite toothBaggyParams inhabitedKey inhabitedPk
      inhabitedCache 0 0 3 node =
      some ([inhabitedLayerSig, inhabitedLayerSig, inhabitedLayerSig], 0#256, [inhabitedRecord]) := by
  simp only [baggySignLayersVerifiedCacheAux, Nat.reduceAdd, inhabited_path, inhabited_cache0,
    inhabited_cache1, inhabited_cache2, inhabited_cachedSig0, inhabited_cachedSig1,
    inhabitedBaggy_fresh]
  rfl

private theorem inhabited_verify (msg : BitVec 256) :
    baggyVerify inhabitedBaggySuite toothBaggyParams inhabitedPk msg (inhabitedSignature msg) = true := by
  change (match baggyWalkLayersVerify inhabitedBaggySuite toothBaggyParams 0#256 0 0
      (0#256 ^^^ msg) [inhabitedLayerSig, inhabitedLayerSig, inhabitedLayerSig] with
    | none => false | some root => root == 0#256) = true
  simp only [baggyWalkLayersVerify, inhabited_path, inhabitedBaggy_recover]
  rfl

private theorem inhabited_enforce_again :
    enforceDurableStaticOpenings inhabitedGuard [inhabitedRecord] = some inhabitedGuard := by
  change (if dToothGood == dToothGood then some inhabitedGuard else none) = some inhabitedGuard
  have h : (dToothGood == dToothGood) = true := decide_eq_true rfl
  rw [ite_pos h]

private theorem inhabited_sign_session (g g' : DurableStaticWotsGuard) (msg : BitVec 256)
    (hGuard : enforceDurableStaticOpenings g [inhabitedRecord] = some g') :
    baggySignVerifiedWaistband inhabitedBaggySuite toothBaggyParams inhabitedKey inhabitedPk
      inhabitedCache g msg 0 = some (inhabitedSignature msg, g', [inhabitedRecord]) := by
  change (match baggySignLayersVerifiedCacheAux inhabitedBaggySuite toothBaggyParams
      inhabitedKey inhabitedPk inhabitedCache 0 0 3 (0#256 ^^^ msg) with
    | none => none
    | some (layers, root, recs) =>
      if root != 0#256 then none else
      match enforceDurableStaticOpenings g recs with
      | none => none
      | some guard =>
        let sig : BaggySig256 := { r := 0#256 ^^^ msg, msgCtr := 0, forsSig := 0#256 ^^^ msg, layers := layers }
        if baggyVerify inhabitedBaggySuite toothBaggyParams inhabitedPk msg sig then
          some (sig, guard, recs) else none) = _
  rw [inhabited_layers]
  change (match enforceDurableStaticOpenings g [inhabitedRecord] with
    | none => none
    | some guard => if baggyVerify inhabitedBaggySuite toothBaggyParams inhabitedPk msg
        (inhabitedSignature msg) then some (inhabitedSignature msg, guard, [inhabitedRecord]) else none) = _
  rw [hGuard]
  simp only [inhabited_verify, ↓reduceIte]

/-- Non-vacuity witness for Section 3 (`VerifiedWaistbandCache` passing `verifyWaistbandCanopy` + multi-session signing). -/
theorem inhabited_waistband_verified_multi_session :
    ∃ (suite : BaggySuite256) (p : BaggyTreeParams) (sk : BaggySecretKey256)
      (cache : VerifiedWaistbandCache) (msg1 msg2 : BitVec 256),
      p.WellFormed ∧
      WaistbandMatchesKey suite p sk cache ∧
      (verifyWaistbandCanopy suite p (baggyKeygen256 suite p sk) cache 2 0 0
        (baggyTrueSubtreeRoot suite p sk 1 0)).isSome = true ∧
      ((baggyRunMultiSessionVerified suite p sk (baggyKeygen256 suite p sk) []
        [(cache, msg1, 0), (cache, msg2, 0)]).2.1.length = 2) := by
  refine ⟨inhabitedBaggySuite, toothBaggyParams, inhabitedKey, inhabitedCache, 1#256, 2#256,
    ⟨by decide, by decide, by decide⟩, ?_, ?_, ?_⟩
  · intro l t v h
    change (if t == 0 then some 0#256 else none) = some v at h
    split at h
    · have hv := Option.some.inj h
      exact hv.symm
    · cases h
  · change (verifyWaistbandCanopy inhabitedBaggySuite toothBaggyParams inhabitedPk
      inhabitedCache 2 0 0 0#256).isSome = true
    rw [inhabited_cache2]
    rfl
  · have hFirst := inhabited_sign_session [] inhabitedGuard 1#256 rfl
    have hSecond := inhabited_sign_session inhabitedGuard inhabitedGuard 2#256 inhabited_enforce_again
    change (baggyRunMultiSessionVerified inhabitedBaggySuite toothBaggyParams inhabitedKey inhabitedPk []
      [(inhabitedCache, 1#256, 0), (inhabitedCache, 2#256, 0)]).2.1.length = 2
    simp only [baggyRunMultiSessionVerified, hFirst, hSecond]
    rfl

/- Build-time audit: every public theorem and executable reduction in this module must
    exist and depend only on kernel extensionality/quotient axioms. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names : Array Name := #[
    `Qsag.wotsC256W,
    `Qsag.wotsC256Steps,
    `Qsag.wotsC256Chains,
    `Qsag.wotsC256ZeroDigits,
    `Qsag.wotsC256TargetSum,
    `Qsag.wotsCDibitIndex,
    `Qsag.wotsCDibitIndex_involutive,
    `Qsag.wotsC256DigitOfDigest,
    `Qsag.packDigitsAux,
    `Qsag.packDigits256,
    `Qsag.packDigits256_extract,
    `Qsag.wotsC256DigitOfDigest_injective,
    `Qsag.wotsCDibits128,
    `Qsag.wotsCDibits128_injective,
    `Qsag.wotsCDibits128_byte_shift,
    `Qsag.wotsCDibits128_msb_sanity,
    `Qsag.WotsC256Digits.ext,
    `Qsag.finFuncEqAux,
    `Qsag.wotsC256DigitSum,
    `Qsag.wotsC256DigitSum_eq,
    `Qsag.wotsC256DecodeValidDigest,
    `Qsag.wotsC256DecodeValidDigest_some_digits,
    `Qsag.wotsC256DecodeValidDigest_of_sum_ne,
    `Qsag.wotsC256DecodeValidDigest_pack,
    `Qsag.findStrictDropAux,
    `Qsag.extractStrictDropIdx,
    `Qsag.wotsC256_strict_incomparability,
    `Qsag.wotsC256PosFrom0,
    `Qsag.wotsC256AdvanceTo,
    `Qsag.wotsC256CompleteTo3,
    `Qsag.wotsC256PkLeaf,
    `Qsag.wotsC256Sign,
    `Qsag.wotsC256Verify,
    `Qsag.wotsC256_sign_verify_complete,
    `Qsag.wotsC256_one_use_euf_cma_extract,
    `Qsag.wotsC256_one_use_euf_cma_sound,
    `Qsag.wotsC256VerifyUnconstrained,
    `Qsag.forgeStepOneChain,
    `Qsag.tooth_wotsc_without_target_sum_forges,
    `Qsag.RssPlane256Share.reconstruct,
    `Qsag.rss256CrossTerms,
    `Qsag.rss256AndWireCorrected,
    `Qsag.rss256AndWireNaiveOffByOne,
    `Qsag.rss256_and_gate_reconstructs,
    `Qsag.RssTower128Share.reconstruct,
    `Qsag.bgin19CrossProdShare,
    `Qsag.Bgin19Deg2Witness.Valid,
    `Qsag.bgin19UnmaskedCoeffShares,
    `Qsag.packTower128Pair,
    `Qsag.unpackTower128Pair,
    `Qsag.rss256RealCorruptView,
    `Qsag.rss256SimDummyInputs,
    `Qsag.rss256SimCorruptView,
    `Qsag.rss256_and_bgin19_privacy_equiv,
    `Qsag.rss256_one_corrupt_view_pointwise_and_count_eq,
    `Qsag.p0CancelNaivePads,
    `Qsag.tooth_off_by_one_prg_map_leaks_and_wire,
    `Qsag.Rss256RecordedGate.error,
    `Qsag.RssPlane256Share.partyViews,
    `Qsag.rss256_replicated_share_binding,
    `Qsag.rss256_honest_recorded_gate_error,
    `Qsag.rss256WeightedErrors,
    `Qsag.rss256PivotCheck,
    `Qsag.rss256PivotCheck_eq,
    `Qsag.rss256_independent_gate_weight_soundness,
    `Qsag.rss256GateErrors,
    `Qsag.rss256Pass1Check,
    `Qsag.rss256_polynomial_gate_weight_soundness,
    `Qsag.rss256_recorded_fault_nonzero,
    `Qsag.rss256_recorded_gate_polynomial_soundness,
    `Qsag.rss256Pass1At,
    `Qsag.rss256_folding_round_soundness,
    `Qsag.tooth_rss256_reused_gate_weights,
    `Qsag.postWaveTwoChallengeAccepts,
    `Qsag.rss256_post_wave_two_challenge_bgin19_soundness,
    `Qsag.preWaveKernelFaultPair,
    `Qsag.preWaveTwoChallengeKernelFault,
    `Qsag.tooth_pre_wave_challenge_kernel_bypass,
    `Qsag.Rss256BarrierState.init,
    `Qsag.rss256BarrierStep,
    `Qsag.rss256BarrierMachine,
    `Qsag.rss256StepBuggy,
    `Qsag.rss256BarrierTrace,
    `Qsag.rss256RecordedWaveOp,
    `Qsag.rss256_recorded_wave_rejection_poison,
    `Qsag.Rss256SafeInvariant,
    `Qsag.rss256_sticky_poison_terminal_absorption,
    `Qsag.tooth_non_sticky_check_clear_unlocks_unverified_open,
    `Qsag.BaggyTreeParams.WellFormed,
    `Qsag.BaggyTreeParams.coversLayer,
    `Qsag.BaggyTreeParams.pathAt,
    `Qsag.baggyChildTreeIdx,
    `Qsag.baggyChildTreeIdx_pathAt,
    `Qsag.BaggySuite256.WellGrinded,
    `Qsag.baggyMerkleRoot,
    `Qsag.baggyMerkleAuthPath,
    `Qsag.baggyWalkMerkleRootFirst,
    `Qsag.extractBaggyMerkleCollision,
    `Qsag.baggyLeafAdrs,
    `Qsag.baggySubtreeLeaves,
    `Qsag.baggyTrueSubtreeRoot,
    `Qsag.baggyKeygen256,
    `Qsag.baggyLayerRecoverRoot,
    `Qsag.baggyWalkLayersVerify,
    `Qsag.baggyVerify,
    `Qsag.baggyCanonicalStaticChildRoot,
    `Qsag.baggyCanonicalStaticDigits,
    `Qsag.baggySignLayerFresh,
    `Qsag.baggySignLayersUncachedAux,
    `Qsag.baggySignUncached,
    `Qsag.verifyCanopyChainToTop,
    `Qsag.verifyWaistbandCanopy,
    `Qsag.lookupDurableDigits,
    `Qsag.enforceDurableStaticOpenings,
    `Qsag.baggySignLayersVerifiedCacheAux,
    `Qsag.baggySignVerifiedWaistband,
    `Qsag.baggyRunMultiSessionVerified,
    `Qsag.WaistbandMatchesKey,
    `Qsag.waistband_verified_multi_session_single_codeword,
    `Qsag.extractStaticLayerBreakFromTransition,
    `Qsag.walkUpperLayersBoundedExtract,
    `Qsag.baggy_verified_waistband_upper_extract,
    `Qsag.baggy_verified_waistband_upper_reduction,
    `Qsag.baggySignLayersUnhardenedAux,
    `Qsag.baggySignUnhardened,
    `Qsag.dToothBadFn,
    `Qsag.dToothGoodFn,
    `Qsag.dToothRogueFn,
    `Qsag.dToothBad,
    `Qsag.dToothGood,
    `Qsag.dToothRogue,
    `Qsag.toothBaggyParams,
    `Qsag.toothRogueRoot,
    `Qsag.toothBaggySuite,
    `Qsag.forgeRogueRootFromTwoTopOpenings,
    `Qsag.tooth_corrupted_intermediate_waistband_opens_second_ancestor_codeword,
    `Qsag.inhabited_wotsC256_incomparability_and_signing,
    `Qsag.inhabited_rss256_privacy_soundness_and_poison,
    `Qsag.inhabitedBaggySuite,
    `Qsag.inhabited_waistband_verified_multi_session]
  for name in names do
    if (env.find? name).isNone then
      throwError "Missing audited declaration {name}"
    let dependencies ← Lean.collectAxioms name
    let forbidden := dependencies.filter fun ax => ax != ``propext && ax != ``Quot.sound
    unless forbidden.isEmpty do
      throwError "Forbidden axioms in {name}: {forbidden}"
  logInfo m!"Baggy/RSS constructive audit: {names.size} declarations passed"

/-! ## Recorded RSS checks and degree-two product rounds

Recorded gate checks and fixed-polynomial root bounds. The checks reject zero
challenges; sampling assumptions are stated separately from deterministic acceptance.
-/

/-- Two 128-bit blocks per plane. Packing preserves all bits (unlike treating
individual erroneous bits as independent product-proof coefficients). -/
def rss256PackedGateErrors (gates : List Rss256RecordedGate) : List Tower128 :=
  gates.flatMap (fun g => let p := unpackTower128Pair g.error; [p.1, p.2])

/-- The final masked-product check has three coefficients and degree at most two. -/
def rss256ProductResidual (a0 a1 b0 b1 c0 c1 c2 : Tower128) : List Tower128 :=
  [towerAdd 7 (towerMul 7 a0 b0) c0,
   towerAdd 7 (towerAdd 7 (towerMul 7 a0 b1) (towerMul 7 a1 b0)) c1,
   towerAdd 7 (towerMul 7 a1 b1) c2]

/-- Root count for the actual quadratic product-minus-claim coefficients, rather
than a degree parameter attached to a list of bit errors. The polynomial is fixed
before the challenge; the candidate domain contains more than two distinct points. -/
theorem rss256_product_degree_two_roots
    (a0 a1 b0 b1 c0 c1 c2 : Tower128) (domain : List Tower128)
    (hNodup : domain.Nodup) (hDomain : 2 < domain.length)
    (hFalse : ∃ c ∈ rss256ProductResidual a0 a1 b0 b1 c0 c1 c2, c ≠ towerZero 7) :
    (domain.filter (fun tau => decide
      (RoundPoly.evalCoeffs (rss256ProductResidual a0 a1 b0 b1 c0 c1 c2) tau = towerZero 7))).length ≤ 2 := by
  have hLen : (rss256ProductResidual a0 a1 b0 b1 c0 c1 c2).length ≤ 2 + 1 := by
    simp [rss256ProductResidual]
  exact RoundPoly.roots_nodup_length_le 2 _ domain hNodup hLen
    (Rss256ProductProof.exists_eval_nonzero_of_coeff_nonzero 2 _ domain hNodup hLen hDomain hFalse)

/-- Binding between the coefficient list and the final masked-product equation. -/
theorem rss256_product_residual_evaluation
    (a0 a1 b0 b1 c0 c1 c2 tau : Tower128) :
    RoundPoly.evalCoeffs (rss256ProductResidual a0 a1 b0 b1 c0 c1 c2) tau =
      towerAdd 7
        (towerMul 7 (towerAdd 7 a0 (towerMul 7 tau a1))
          (towerAdd 7 b0 (towerMul 7 tau b1)))
        (RoundPoly.evalCoeffs [c0, c1, c2] tau) := by
  simp only [rss256ProductResidual, RoundPoly.evalCoeffs]
  change towerAdd 7 (towerAdd 7 (towerMul 7 a0 b0) c0)
    (towerMul 7 tau (towerAdd 7
      (towerAdd 7 (towerAdd 7 (towerMul 7 a0 b1) (towerMul 7 a1 b0)) c1)
      (towerMul 7 tau (towerAdd 7 (towerAdd 7 (towerMul 7 a1 b1) c2)
        (towerMul 7 tau (towerZero 7)))))) =
    towerAdd 7
      (towerMul 7 (towerAdd 7 a0 (towerMul 7 tau a1))
        (towerAdd 7 b0 (towerMul 7 tau b1)))
      (towerAdd 7 c0
        (towerMul 7 tau (towerAdd 7 c1
          (towerMul 7 tau (towerAdd 7 c2 (towerMul 7 tau (towerZero 7)))))))
  simp only [towerMul_zero, towerAdd_zero, towerMul_add_distrib, towerAdd_mul_distrib]
  simp only [towerMul_comm, towerMul_left_comm_of_assoc 7 (towerMul_assoc 7),
    towerAdd_assoc, towerAdd_comm, towerAdd_left_comm]

/-- Check each recorded gate's left operand is the preceding gate's output.
The output is read from those same recorded shares, never a separate output plane. -/
def rss256GateLinks : Plane256 → List Rss256RecordedGate → Bool
  | _, [] => true
  | input, g :: gs => (g.x.reconstruct == input) && rss256GateLinks g.z.reconstruct gs

def rss256GateOutput : Plane256 → List Rss256RecordedGate → Plane256
  | input, [] => input
  | _, g :: gs => rss256GateOutput g.z.reconstruct gs

def rss256GateIdeal : Plane256 → List Rss256RecordedGate → Plane256
  | input, [] => input
  | input, g :: gs => rss256GateIdeal (input &&& g.y.reconstruct) gs

structure Rss256InlineWave where
  input : Plane256
  gates : List Rss256RecordedGate

/-- Bank-mode holder copies are compared by Horner at two fresh challenges. -/
structure Rss256BankWave where
  firstHolder : List Tower128
  secondHolder : List Tower128

inductive Rss256Wave where
  | inlineWave (wave : Rss256InlineWave)
  | bankWave (wave : Rss256BankWave)

def Rss256Wave.check (w : Rss256Wave) (chi1 chi2 : Tower128) : Bool :=
  (chi1 != towerZero 7) && (chi2 != towerZero 7) &&
  (match w with
  | .inlineWave w =>
    rss256GateLinks w.input w.gates &&
      (batchDeviationPoly (rss256PackedGateErrors w.gates) chi1 == towerZero 7) &&
      (batchDeviationPoly (rss256PackedGateErrors w.gates) chi2 == towerZero 7)
  | .bankWave w =>
    decide (w.firstHolder.length = w.secondHolder.length) &&
      (ghashPoly chi1 w.firstHolder == ghashPoly chi1 w.secondHolder) &&
      (ghashPoly chi2 w.firstHolder == ghashPoly chi2 w.secondHolder))

theorem rss256_zero_challenge_rejected (w : Rss256Wave) (a : Tower128) :
    w.check (towerZero 7) a = false ∧ w.check a (towerZero 7) = false := by
  cases w <;> simp [Rss256Wave.check]

/-- Two independent samples from a fixed finite coin set have at most L² root
pairs for a nonzero frozen error polynomial. This is a cardinality bound, not a
case split on an integrity failure. -/
theorem rss256_two_coin_root_bound (errors coins : List Tower128) (L : Nat)
    (hn : coins.Nodup) (hl : errors.length ≤ L) (hd : L + 1 ≤ coins.length)
    (he : ∃ d ∈ errors, d ≠ towerZero 7) :
    (coins.filter (fun r => decide (batchDeviationPoly errors r = towerZero 7))).length *
      (coins.filter (fun r => decide (batchDeviationPoly errors r = towerZero 7))).length ≤ L * L := by
  have h := (bdoz_2lane_mac_soundness L errors coins hn hl hd he).1
  exact Nat.mul_le_mul h h

private theorem rss256_packed_zero_gate (g : Rss256RecordedGate)
    (h0 : (unpackTower128Pair g.error).1 = towerZero 7)
    (h1 : (unpackTower128Pair g.error).2 = towerZero 7) :
    g.z.reconstruct = g.x.reconstruct &&& g.y.reconstruct := by
  have hp := congrArg (packTower 8) (show unpackTower 8 g.error = towerZero 8 from Prod.ext h0 h1)
  simp only [packTower_unpackTower, packTower_zero] at hp
  exact BitVec.xor_eq_zero_iff.mp hp

private theorem rss256_zero_errors_integrity (input : Plane256) (gates : List Rss256RecordedGate)
    (hl : rss256GateLinks input gates = true)
    (hz : ∀ e ∈ rss256PackedGateErrors gates, e = towerZero 7) :
    rss256GateOutput input gates = rss256GateIdeal input gates := by
  induction gates generalizing input with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨hx, ht⟩ := Bool.and_eq_true_iff.mp hl
    have h0 := hz (unpackTower128Pair g.error).1 (by simp [rss256PackedGateErrors])
    have h1 := hz (unpackTower128Pair g.error).2 (by simp [rss256PackedGateErrors])
    have hg := rss256_packed_zero_gate g h0 h1
    have tail := ih g.z.reconstruct ht (fun e he => hz e (by
      simp only [rss256PackedGateErrors, List.flatMap_cons, List.mem_append] at he ⊢
      exact Or.inr he))
    simp only [rss256GateOutput, rss256GateIdeal]
    rw [tail, hg, eq_of_beq hx]

private theorem rss256_nonzero_of_all_false (xs : List Tower128)
    (h : xs.all (fun e => e == towerZero 7) = false) :
    ∃ e ∈ xs, e ≠ towerZero 7 := by
  induction xs with
  | nil => cases h
  | cons x xs ih =>
    if hx : x = towerZero 7 then
      have ht : xs.all (fun e => e == towerZero 7) = false := by
        simpa only [List.all_cons, hx, beq_self_eq_true, Bool.true_and] using h
      obtain ⟨e, he, hn⟩ := ih ht
      exact ⟨e, List.mem_cons_of_mem x he, hn⟩
    else exact ⟨x, List.mem_cons_self, hx⟩

theorem rss256_fault_has_nonzero_errors (w : Rss256InlineWave)
    (hl : rss256GateLinks w.input w.gates = true)
    (hf : rss256GateOutput w.input w.gates ≠ rss256GateIdeal w.input w.gates) :
    ∃ e ∈ rss256PackedGateErrors w.gates, e ≠ towerZero 7 := by
  cases ha : (rss256PackedGateErrors w.gates).all (fun e => e == towerZero 7) with
  | true =>
    exact False.elim (hf (rss256_zero_errors_integrity w.input w.gates hl
      (fun e he => eq_of_beq (List.all_eq_true.mp ha e he))))
  | false =>
    exact rss256_nonzero_of_all_false _ ha

/-- Semantic output corruption forces a nonzero polynomial; for two independent
uniform points in any listed coin set, accepting pairs are bounded by degree². -/
theorem rss256_inline_integrity_root_bound (w : Rss256InlineWave) (coins : List Tower128)
    (hl : rss256GateLinks w.input w.gates = true)
    (hf : rss256GateOutput w.input w.gates ≠ rss256GateIdeal w.input w.gates)
    (hn : coins.Nodup) (hd : (rss256PackedGateErrors w.gates).length + 1 ≤ coins.length) :
    (coins.filter (fun r => decide (batchDeviationPoly (rss256PackedGateErrors w.gates) r = towerZero 7))).length ^ 2 ≤
      (rss256PackedGateErrors w.gates).length ^ 2 := by
  simpa only [Nat.pow_two] using rss256_two_coin_root_bound (rss256PackedGateErrors w.gates)
    coins _ hn (Nat.le_refl _) hd (rss256_fault_has_nonzero_errors w hl hf)

/-- **Inline Wave Semantic Fault → 2-Pass `product_proof` Barrier Soundness
    (`rss256_inline_wave_two_pass_product_proof_sound`)**:
    Any `w : Rss256InlineWave` with valid gate links (`rss256GateLinks w.input w.gates = true`)
    and corrupted semantic output (`rss256GateOutput w.input w.gates ≠ rss256GateIdeal w.input w.gates`)
    has a nonzero packed gate-error block (`rss256_fault_has_nonzero_errors`), so across both passes
    (`ROUND1` + `ROUND2`) of `product_proof`, ANY adaptive `Rss256ProductProof.TwoPassProver foldBits`
    accepts on at most `((B + 16 + 8 * foldBits.length) * |S|^(TENSOR_BITS + foldBits.sum + 1))^2`
    out of `(|S|^(TENSOR_BITS + foldBits.sum + 2))^2` coin pairs! -/
theorem rss256_inline_wave_two_pass_product_proof_sound
    (w : Rss256InlineWave) (B : Nat) (foldBits : List Nat)
    (batch : Rss256ProductProof.RecordedPassBatch foldBits)
    (prover : Rss256ProductProof.TwoPassProver foldBits)
    (S : List Tower128)
    (hl : rss256GateLinks w.input w.gates = true)
    (hf : rss256GateOutput w.input w.gates ≠ rss256GateIdeal w.input w.gates)
    (hBatch : batch.gateErrorBlocks = rss256PackedGateErrors w.gates)
    (hS : S.Nodup) (hBPos : 1 ≤ B) (hBLen : batch.gateErrorBlocks.length ≤ B)
    (hDom : B ≤ S.length) (hArity : ∀ b ∈ foldBits, b ≤ Rss256ProductProof.FOLD_BITS) :
    ((Rss256ProductProof.twoPassCoinSpace S foldBits).filter
      (Rss256ProductProof.twoPassAccepts foldBits batch prover)).length ≤
      ((B + 16 + 8 * foldBits.length) *
        S.length ^ (Rss256ProductProof.TENSOR_BITS + foldBits.sum + 1)) ^ 2 := by
  have hFault : ∃ e ∈ batch.gateErrorBlocks, e ≠ towerZero 7 := by
    rw [hBatch]
    exact rss256_fault_has_nonzero_errors w hl hf
  exact Rss256ProductProof.rss256_two_pass_product_proof_sound
    B foldBits batch prover S hS hBPos hBLen hDom hArity hFault

/-- Semantic fault is independent of verifier acceptance. In particular zero
challenges do not turn a false gate into a semantically clean gate. -/
def Rss256Wave.Fault : Rss256Wave → Prop
  | .inlineWave w => rss256GateOutput w.input w.gates ≠ rss256GateIdeal w.input w.gates
  | .bankWave w => w.firstHolder ≠ w.secondHolder

def Rss256Wave.BadChallenge (w : Rss256Wave) (chi1 chi2 : Tower128) : Prop :=
  w.Fault ∧ w.check chi1 chi2 = true

def rss256WaveBytes : Rss256Wave → List UInt8
  | .inlineWave w =>
    encodeMultiFrame ([0] :: be 32 w.input.toNat :: w.gates.map (fun g =>
      encodeMultiFrame ([g.x.s0, g.x.s1, g.x.s2, g.y.s0, g.y.s1, g.y.s2,
        g.z.s0, g.z.s1, g.z.s2].map (fun x => be 32 x.toNat))))
  | .bankWave w => encodeMultiFrame [[1],
      encodeMultiFrame (w.firstHolder.map (fun x => be 16 (packTower 7 x).toNat)),
      encodeMultiFrame (w.secondHolder.map (fun x => be 16 (packTower 7 x).toNat))]

def rss256Transcript (waves : List Rss256Wave) : List UInt8 :=
  cshake256Bytes "QSAG-WAVE-TRANSCRIPT-v1".toUTF8.data.toList
    (encodeMultiFrame (waves.map rss256WaveBytes))

def rss256CoinCommit (transcript : List UInt8) (seed : Tower128) : List UInt8 :=
  cshake256Bytes "QSAG-WAVE-CHECK-COIN-v1".toUTF8.data.toList
    (encodeMultiFrame [transcript, be 16 (packTower 7 seed).toNat])

/-- The two lanes are domain-separated XOF outputs of the frozen transcript and
revealed contributions. Zero is rejected by the wave checker. -/
def rss256DerivedCoin (waves : List Rss256Wave) (a b : Tower128) (lane : Nat) : Tower128 :=
  let seed := cshake256Bytes "QSAG-WAVE-CHECK-v1".toUTF8.data.toList
    (encodeMultiFrame [rss256Transcript waves, be 16 (packTower 7 a).toNat,
      be 16 (packTower 7 b).toNat])
  let bytes := cshake256Bytes "QSAG-WAVE-HORNER-v1".toUTF8.data.toList
    (encodeMultiFrame [seed, be 8 lane])
  unpackTower 7 (BitVec.ofNat 128 (bytes.take 16 |>.foldl (fun n x => n * 256 + x.toNat) 0))

structure Rss256EngineState where
  pending : List Rss256Wave
  accepted : List (Rss256Wave × Tower128 × Tower128)
  poisoned : Bool
  coinCommits : Option (List UInt8 × List UInt8) := none

def Rss256EngineState.init : Rss256EngineState := ⟨[], [], false, none⟩

inductive Rss256EngineOp where
  | permuteInline (wave : Rss256InlineWave)
  | permuteBank (wave : Rss256BankWave)
  | commitCoins (commit1 commit2 : List UInt8)
  | check (seed1 seed2 : Tower128)
  | openPlanes

/-- Recorded-transcript barrier. Checks compute Horner equations internally;
there is no validity flag and no independent caller-selected output plane.
Both revealed coin shares and both derived Horner evaluation points must be nonzero. -/
def rss256StepHardened (st : Rss256EngineState) (op : Rss256EngineOp) :
    Rss256StepOutcome Rss256EngineState (List Plane256) :=
  if st.poisoned then .err st .enginePoisoned
  else match op with
  | .permuteInline w => .ok { st with pending := st.pending ++ [.inlineWave w], coinCommits := none } []
  | .permuteBank w => .ok { st with pending := st.pending ++ [.bankWave w], coinCommits := none } []
  | .commitCoins c1 c2 => .ok { st with coinCommits := some (c1, c2) } []
  | .check a b =>
    let x := rss256DerivedCoin st.pending a b 0
    let y := rss256DerivedCoin st.pending a b 1
    if a != towerZero 7 && b != towerZero 7 &&
        x != towerZero 7 && y != towerZero 7 &&
        st.coinCommits == some (rss256CoinCommit (rss256Transcript st.pending) a,
        rss256CoinCommit (rss256Transcript st.pending) b) &&
        st.pending.all (fun w => w.check x y) then
      .ok { st with pending := [], coinCommits := none, accepted := st.accepted ++ st.pending.map (fun w => (w,x,y)) } []
    else .err { st with poisoned := true, pending := [], accepted := [] } .multiplicationCheckFailed
  | .openPlanes =>
    if st.pending.isEmpty then
      .ok st (st.accepted.filterMap (fun entry => match entry.1 with
        | .inlineWave w => some (rss256GateOutput w.input w.gates)
        | .bankWave _ => none))
    else .err st .openBeforeCheck

/-- The operational step itself rejects a zero reveal, including when no wave is pending. -/
theorem rss256_step_zero_coin_rejected (st : Rss256EngineState) (a : Tower128)
    (hp : st.poisoned = false) :
    rss256StepHardened st (.check (towerZero 7) a) =
      .err { st with poisoned := true, pending := [], accepted := [] } .multiplicationCheckFailed ∧
    rss256StepHardened st (.check a (towerZero 7)) =
      .err { st with poisoned := true, pending := [], accepted := [] } .multiplicationCheckFailed := by
  simp [rss256StepHardened, hp]

/-- The operational step also rejects a zero derived Horner point on either lane, even when `pending = []`. -/
theorem rss256_step_zero_derived_coin_rejected (st : Rss256EngineState) (a b : Tower128)
    (hp : st.poisoned = false)
    (hz : rss256DerivedCoin st.pending a b 0 = towerZero 7 ∨
          rss256DerivedCoin st.pending a b 1 = towerZero 7) :
    rss256StepHardened st (.check a b) =
      .err { st with poisoned := true, pending := [], accepted := [] } .multiplicationCheckFailed := by
  rcases hz with h0 | h1
  · simp [rss256StepHardened, hp, h0]
  · simp [rss256StepHardened, hp, h1]

/-- API misuse is recoverable; a cryptographic barrier failure is not. -/
theorem rss256_premature_open_preserves_state (st : Rss256EngineState)
    (hp : st.poisoned = false) (hu : st.pending.isEmpty = false) :
    rss256StepHardened st .openPlanes = .err st .openBeforeCheck := by
  simp [rss256StepHardened, hp, hu]

theorem rss256_failed_horner_poisons (st : Rss256EngineState) (a b : Tower128)
    (hp : st.poisoned = false) (hf : st.pending.all (fun w => w.check
      (rss256DerivedCoin st.pending a b 0) (rss256DerivedCoin st.pending a b 1)) = false) :
    rss256StepHardened st (.check a b) =
      .err { st with poisoned := true, pending := [], accepted := [] } .multiplicationCheckFailed := by
  simp [rss256StepHardened, hp, hf]

/-- Output integrity is explicitly conditional on absence of the checker bad
 event, rather than on a syntactic taint bit. -/
theorem rss256_checked_inline_integrity (w : Rss256InlineWave) (a b : Tower128)
    (ha : (Rss256Wave.inlineWave w).check a b = true)
    (hn : ¬ (Rss256Wave.inlineWave w).BadChallenge a b) :
    rss256GateOutput w.input w.gates = rss256GateIdeal w.input w.gates := by
  by_cases he : rss256GateOutput w.input w.gates = rss256GateIdeal w.input w.gates
  · exact he
  · exact False.elim (hn ⟨he, ha⟩)

/-- The packed-block batching bound is conditional on a fixed nonzero error
polynomial. It does not claim a tensor/folding transcript refinement. -/
theorem rss256_packed_batch_roots (gates : List Rss256RecordedGate)
    (hn : ∃ e ∈ rss256PackedGateErrors gates, e ≠ towerZero 7) :
    ratLe (qsum (2^128) (fun r =>
      if batchDeviationPoly (rss256PackedGateErrors gates)
        (unpackTower 7 (BitVec.ofFin r)) == towerZero 7 then 1 else 0), 2^128)
      ((rss256PackedGateErrors gates).length, 2^128) :=
  rss256_polynomial_gate_weight_soundness _ _ (Nat.le_refl _) hn

/-! ## Crash-visible reservation and release

The pure signature functions above are specifications. This state machine makes
reservation write, durable sync, opening and recovery different transitions. Its
durable storage contract is an acknowledged atomic record-batch sync; it does not
assert a POSIX implementation theorem. Failures never roll back acknowledged
records. The identity indexes the whole ledger, including recovery.
-/
structure BaggyLedgerIdentity where
  pkSeed : BitVec 256
  pkRoot : BitVec 256
  paramsDigest : BitVec 256
  deriving DecidableEq

inductive BaggyRootProvenance where
  | computed
  | cachedSignature
  | cachedLeaves
  deriving DecidableEq

structure BaggyPlannedOpening where
  record : StaticWotsOpeningRecord
  provenance : BaggyRootProvenance

/-- Cached roots may only use an already durably anchored codeword. -/
def admitBaggyPlannedOpening (guard : DurableStaticWotsGuard)
    (plan : BaggyPlannedOpening) : Bool :=
  let r := plan.record
  match lookupDurableDigits guard r.layer r.tree r.kp with
  | some d => d == r.digits
  | none => match plan.provenance with
    | .computed => true
    | .cachedSignature | .cachedLeaves => false

inductive BaggyReleasePhase where
  | idle | planned | written | synced | opened | aborted
  deriving DecidableEq

structure BaggyReleaseState (identity : BaggyLedgerIdentity) where
  durable : DurableStaticWotsGuard
  staged : DurableStaticWotsGuard
  plan : List BaggyPlannedOpening
  phase : BaggyReleasePhase
  /-- Public ghost history of releases; crash does not erase prior observations. -/
  released : List StaticWotsOpeningRecord

def BaggyReleaseState.init (identity : BaggyLedgerIdentity) : BaggyReleaseState identity :=
  ⟨[], [], [], .idle, []⟩

inductive BaggyReleaseOp where
  | plan (openings : List BaggyPlannedOpening)
  | write
  | syncAck
  | release
  | storageFailure
  | verificationFailure
  | crash

/-- `syncAck` is the storage contract's durable-commit event. No earlier state
can emit an opening, and no failure event removes a committed reservation. -/
def baggyReleaseStep {identity : BaggyLedgerIdentity}
    (st : BaggyReleaseState identity) (op : BaggyReleaseOp) : BaggyReleaseState identity :=
  match op with
  | .crash => { st with staged := [], plan := [], phase := .idle }
  | .storageFailure | .verificationFailure =>
    { st with staged := [], plan := [], phase := .aborted }
  | .plan ps =>
    if (st.phase == .idle || st.phase == .opened) && ps.all (admitBaggyPlannedOpening st.durable) then
      { st with plan := ps, phase := .planned }
    else { st with phase := .aborted }
  | .write =>
    if st.phase == .planned then
      match enforceDurableStaticOpenings st.durable (st.plan.map (·.record)) with
      | some staged => { st with staged := staged, phase := .written }
      | none => { st with phase := .aborted }
    else { st with phase := .aborted }
  | .syncAck =>
    if st.phase == .written then { st with durable := st.staged, phase := .synced }
    else { st with phase := .aborted }
  | .release =>
    if st.phase == .synced && st.plan.all (fun p =>
        lookupDurableDigits st.durable p.record.layer p.record.tree p.record.kp == some p.record.digits) then
      { st with released := st.released ++ st.plan.map (·.record), phase := .opened }
    else { st with phase := .aborted }

def baggyReleaseTrace {identity : BaggyLedgerIdentity} :
    BaggyReleaseState identity → List BaggyReleaseOp → BaggyReleaseState identity
  | st, [] => st
  | st, op :: ops => baggyReleaseTrace (baggyReleaseStep st op) ops

theorem baggy_crash_preserves_reservations {identity : BaggyLedgerIdentity}
    (st : BaggyReleaseState identity) :
    (baggyReleaseStep st .crash).durable = st.durable ∧
    (baggyReleaseStep st .crash).released = st.released := ⟨rfl, rfl⟩

theorem baggy_failed_verification_preserves_reservations {identity : BaggyLedgerIdentity}
    (st : BaggyReleaseState identity) :
    (baggyReleaseStep st .verificationFailure).durable = st.durable := by
  unfold baggyReleaseStep
  rfl

theorem baggy_release_requires_sync {identity : BaggyLedgerIdentity}
    (st : BaggyReleaseState identity) (h : st.phase ≠ .synced) :
    (baggyReleaseStep st .release).released = st.released := by
  have hb : (st.phase == .synced) = false := beq_false_of_ne h
  simp [baggyReleaseStep, hb]

/-- Every newly emitted opening is checked against an acknowledged durable entry.
The theorem concerns the released record, not a discarded tentative reservation. -/
theorem baggy_release_has_durable_codeword {identity : BaggyLedgerIdentity}
    (st : BaggyReleaseState identity) (r : StaticWotsOpeningRecord)
    (hNew : r ∈ (baggyReleaseStep st .release).released) (hOld : r ∉ st.released) :
    lookupDurableDigits st.durable r.layer r.tree r.kp = some r.digits := by
  unfold baggyReleaseStep at hNew
  dsimp only at hNew
  split at hNew
  next hGuard =>
    have hAll := (Bool.and_eq_true_iff.mp hGuard).2
    rcases List.mem_append.mp hNew with ho | hn
    · exact False.elim (hOld ho)
    · obtain ⟨p, hp, he⟩ := List.mem_map.mp hn
      have hv := List.all_eq_true.mp hAll p hp
      subst r
      exact eq_of_beq hv
  next => exact False.elim (hOld hNew)

/-- `#tooth`: a crash between write and sync loses the tentative record and
cannot release; a crash after sync retains the codeword but still requires replanning. -/
theorem tooth_baggy_crash_between_write_and_sync (identity : BaggyLedgerIdentity)
    (g : DurableStaticWotsGuard) (ps : List BaggyPlannedOpening) :
    let st : BaggyReleaseState identity := ⟨[], g, ps, .written, []⟩
    (baggyReleaseTrace st [.crash, .release]).released = [] ∧
    (baggyReleaseTrace st [.syncAck, .crash]).durable = g := by
  exact ⟨rfl, rfl⟩

/-- Secret chain generation consumes a durable reservation. The record's digits
must also match the actual hash grind, preventing an arbitrary signedNode from
borrowing a reservation for another codeword. -/
def baggyOpenReservedChains (suite : BaggySuite256) (p : BaggyTreeParams) (sk : BaggySecretKey256)
    (identity : BaggyLedgerIdentity) (st : BaggyReleaseState identity)
    (r : StaticWotsOpeningRecord) : Option (Fin 128 → BitVec 256) :=
  let adrs := baggyLeafAdrs r.layer r.tree r.kp
  let ctr := suite.grindCounter sk.pkSeed adrs r.signedNode
  if decide (identity.pkSeed = sk.pkSeed ∧
      identity.pkRoot = (baggyKeygen256 suite p sk).pkRoot ∧
      identity.paramsDigest = suite.paramsDigest p ∧
      r ∈ st.plan.map (·.record) ∧ r.layer < p.numLayers ∧ r.kp < 2 ^ p.subtreeHeight) &&
      (st.phase == .synced) &&
      (lookupDurableDigits st.durable r.layer r.tree r.kp == some r.digits) &&
      (wotsC256DecodeValidDigest (suite.wots.thDigest sk.pkSeed adrs r.signedNode ctr) == some r.digits) then
    wotsC256Sign suite.wots sk.pkSeed sk.skSeed adrs r.signedNode ctr
  else none

/-! ## Cache modes and authenticated cache records -/
inductive BaggyLayerCachePlan (p : BaggyTreeParams) where
  | fresh
  | signature (childRoot layerRoot : BitVec 256) (sig : BaggyLayerSig256)
  | leaves (root : BitVec 256) (values : Fin (2 ^ p.subtreeHeight) → BitVec 256)

/-- Invalid cache material rejects. A miss is represented only by `fresh`.
Cached leaf sets are committed by the same Merkle root computation as fresh sets. -/
def authenticateBaggyLayerPlan (suite : BaggySuite256) (p : BaggyTreeParams)
    (pkSeed : BitVec 256) (layer tree kp : Nat) (plan : BaggyLayerCachePlan p) :
    Option (Option (BitVec 256) × BaggyRootProvenance) :=
  match plan with
  | .fresh => some (none, .computed)
  | .signature child root sig =>
    if baggyLayerRecoverRoot suite p pkSeed layer tree kp child sig == some root then
      some (some root, .cachedSignature)
    else none
  | .leaves root values =>
    if baggyMerkleRoot suite pkSeed layer tree p.subtreeHeight 0 values == root then
      some (some root, .cachedLeaves)
    else none

/-- Cache authority signs the full identity/address/root tuple. This structured
message is deliberately not an ambiguous concatenation of variable-width fields. -/
structure BaggyCacheMessage where
  identity : BaggyLedgerIdentity
  layer : Nat
  tree : Nat
  root : BitVec 256
  deriving DecidableEq

structure BaggyAuthenticatedCacheEntry where
  message : BaggyCacheMessage
  tag : BitVec 256

/-- The key is captured by the enrolled MAC function, never supplied by a cache entry. -/
def verifyBaggyCacheMac (mac : BaggyCacheMessage → BitVec 256)
    (identity : BaggyLedgerIdentity) (e : BaggyAuthenticatedCacheEntry) : Bool :=
  decide (e.message.identity = identity) && (e.tag == mac e.message)

def BaggyCacheMacForgery (mac : BaggyCacheMessage → BitVec 256)
    (history : List BaggyCacheMessage) (e : BaggyAuthenticatedCacheEntry) : Prop :=
  e.tag = mac e.message ∧ e.message ∉ history

/-- Successful entry verification yields an enrolled genuine root or the actual
accepted, unsigned cache entry as a MAC-game forgery. The authenticity premise is
on the authority's signing history, not on adversarial cache contents. -/
theorem baggy_cache_authentic_or_forgery
    (mac : BaggyCacheMessage → BitVec 256) (identity : BaggyLedgerIdentity)
    (history : List BaggyCacheMessage) (genuine : Nat → Nat → BitVec 256)
    (hHistory : ∀ m ∈ history, m.identity = identity → m.root = genuine m.layer m.tree)
    (e : BaggyAuthenticatedCacheEntry) (h : verifyBaggyCacheMac mac identity e = true) :
    e.message.root = genuine e.message.layer e.message.tree ∨ BaggyCacheMacForgery mac history e := by
  obtain ⟨hi, ht⟩ := Bool.and_eq_true_iff.mp h
  by_cases hm : e.message ∈ history
  · exact .inl (hHistory e.message hm (of_decide_eq_true hi))
  · exact .inr ⟨eq_of_beq ht, hm⟩

/-- Accepted transcripts retain the exact coins with which they were checked. -/
def Rss256EngineState.Checked (st : Rss256EngineState) : Prop :=
  ∀ e ∈ st.accepted, e.1.check e.2.1 e.2.2 = true

theorem rss256_recorded_step_preserves_checked (st : Rss256EngineState)
    (op : Rss256EngineOp) (h : st.Checked) :
    match rss256StepHardened st op with
    | .ok next _ => next.Checked
    | .err next _ => next.Checked := by
  unfold rss256StepHardened
  cases hp : st.poisoned
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases op with
    | permuteInline w => exact h
    | permuteBank w => exact h
    | commitCoins c1 c2 => exact h
    | openPlanes =>
      dsimp only
      cases hEmp : st.pending.isEmpty
      · rw [ite_neg (by decide)]; exact h
      · rw [ite_pos rfl]; exact h
    | check a b =>
      dsimp only
      cases good : (a != towerZero 7 && b != towerZero 7 &&
          rss256DerivedCoin st.pending a b 0 != towerZero 7 &&
          rss256DerivedCoin st.pending a b 1 != towerZero 7 &&
          st.coinCommits == some (rss256CoinCommit (rss256Transcript st.pending) a,
            rss256CoinCommit (rss256Transcript st.pending) b) &&
          st.pending.all (fun w => w.check (rss256DerivedCoin st.pending a b 0)
            (rss256DerivedCoin st.pending a b 1)))
      · rw [ite_neg (by decide)]
        intro e he; cases he
      · rw [ite_pos rfl]
        intro e he
        rcases List.mem_append.mp he with ho | hn
        · exact h e ho
        · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hn
          exact List.all_eq_true.mp (Bool.and_eq_true_iff.mp good).2 w hw
  · simp only [↓reduceIte]
    exact h

/-- Every emitted plane comes from the very transcript whose equations passed.
Its semantic output is correct or that transcript is a concrete bad-challenge
witness. This conclusion never equates verifier acceptance with semantic validity. -/
theorem rss256_recorded_release_integrity (st next : Rss256EngineState)
    (outputs : List Plane256) (h : st.Checked)
    (ho : rss256StepHardened st .openPlanes = .ok next outputs)
    (out : Plane256) (hm : out ∈ outputs) :
    ∃ w : Rss256InlineWave, ∃ a b : Tower128,
      out = rss256GateOutput w.input w.gates ∧
      (out = rss256GateIdeal w.input w.gates ∨ (Rss256Wave.inlineWave w).BadChallenge a b) := by
  unfold rss256StepHardened at ho
  dsimp only at ho
  cases hp : st.poisoned
  · rw [hp] at ho
    simp only [Bool.false_eq_true, ↓reduceIte] at ho
    cases hEmp : st.pending.isEmpty
    · rw [hEmp] at ho
      simp only [Bool.false_eq_true, ↓reduceIte] at ho
      cases ho
    · rw [hEmp] at ho
      simp only [↓reduceIte] at ho
      injection ho with _ hOutputs
      rw [← hOutputs] at hm
      obtain ⟨entry, he, hv⟩ := List.mem_filterMap.mp hm
      rcases entry with ⟨wave, a, b⟩
      cases wave with
      | bankWave w => cases hv
      | inlineWave w =>
        have heq : rss256GateOutput w.input w.gates = out := Option.some.inj hv
        refine ⟨w, a, b, heq.symm, ?_⟩
        by_cases hi : out = rss256GateIdeal w.input w.gates
        · exact .inl hi
        · right
          exact ⟨fun hc => hi (heq.symm.trans hc), h _ he⟩
  · rw [hp] at ho
    simp only [↓reduceIte] at ho
    cases ho

/-- Multi-step execution of `rss256StepHardened`, accumulating all released `Plane256` outputs. -/
def rss256TraceHardened : Rss256EngineState → List Rss256EngineOp → Rss256EngineState × List Plane256
  | st, [] => (st, [])
  | st, op :: rest =>
    match rss256StepHardened st op with
    | .ok next outs =>
      let (final, tail) := rss256TraceHardened next rest
      (final, outs ++ tail)
    | .err next _ => rss256TraceHardened next rest

/-- Across any arbitrary multi-wave trace of `rss256StepHardened` from `Rss256EngineState.init`,
    `Checked` is preserved, `poisoned = true` is terminally absorbing, and every emitted `Plane256`
    either equals its ideal Keccak gate evaluation or witnesses a concrete `BadChallenge`. -/
theorem rss256_recorded_trace_integrity (ops : List Rss256EngineOp) :
    (rss256TraceHardened Rss256EngineState.init ops).1.Checked ∧
    (∀ out ∈ (rss256TraceHardened Rss256EngineState.init ops).2,
      ∃ w : Rss256InlineWave, ∃ a b : Tower128,
        out = rss256GateOutput w.input w.gates ∧
        (out = rss256GateIdeal w.input w.gates ∨ (Rss256Wave.inlineWave w).BadChallenge a b)) := by
  suffices hGen : ∀ (st : Rss256EngineState) (ops : List Rss256EngineOp),
      st.Checked →
      (rss256TraceHardened st ops).1.Checked ∧
      (∀ out ∈ (rss256TraceHardened st ops).2,
        ∃ w : Rss256InlineWave, ∃ a b : Tower128,
          out = rss256GateOutput w.input w.gates ∧
          (out = rss256GateIdeal w.input w.gates ∨ (Rss256Wave.inlineWave w).BadChallenge a b)) by
    exact hGen Rss256EngineState.init ops (fun _ he => by cases he)
  intro st tr hChk
  induction tr generalizing st with
  | nil => exact ⟨hChk, fun _ hm => by cases hm⟩
  | cons op rest ih =>
    have hPres := rss256_recorded_step_preserves_checked st op hChk
    cases hStep : rss256StepHardened st op with
    | err next errVal =>
      rw [hStep] at hPres
      simp only [rss256TraceHardened, hStep]
      exact ih next hPres
    | ok next outs =>
      rw [hStep] at hPres
      simp only [rss256TraceHardened, hStep]
      have hSub := ih next hPres
      refine ⟨hSub.1, fun out hm => ?_⟩
      rcases List.mem_append.mp hm with hHead | hTail
      · cases op with
        | permuteInline w =>
          unfold rss256StepHardened at hStep
          cases hp : st.poisoned <;> simp [hp] at hStep
          rcases hStep with ⟨_, rfl⟩; cases hHead
        | permuteBank w =>
          unfold rss256StepHardened at hStep
          cases hp : st.poisoned <;> simp [hp] at hStep
          rcases hStep with ⟨_, rfl⟩; cases hHead
        | commitCoins c1 c2 =>
          unfold rss256StepHardened at hStep
          cases hp : st.poisoned <;> simp [hp] at hStep
          rcases hStep with ⟨_, rfl⟩; cases hHead
        | check a b =>
          unfold rss256StepHardened at hStep
          cases hp : st.poisoned
          · rw [hp] at hStep; simp only [Bool.false_eq_true, ↓reduceIte] at hStep
            split at hStep
            · injection hStep with _ hOut; subst hOut; cases hHead
            · cases hStep
          · rw [hp] at hStep; simp at hStep
        | openPlanes =>
          exact rss256_recorded_release_integrity st next outs hChk hStep out hHead
      · exact hSub.2 out hTail

/-- A present invalid signature cache entry cannot fall back to fresh signing. -/
theorem baggy_invalid_cache_entry_rejects (suite : BaggySuite256) (p : BaggyTreeParams)
    (sk : BaggySecretKey256) (pk : BaggyPublicKey256) (cache : VerifiedWaistbandCache)
    (leaf layer remaining : Nat) (node : BitVec 256)
    (hInvalid : verifyWaistbandCanopy suite p pk cache layer
      (p.pathAt leaf layer).2 (p.pathAt leaf layer).1 node = none)
    (hPresent : (cache.cachedSig layer (p.pathAt leaf layer).2 (p.pathAt leaf layer).1).isSome = true) :
    baggySignLayersVerifiedCacheAux suite p sk pk cache leaf layer (remaining + 1) node = none := by
  simp only [baggySignLayersVerifiedCacheAux, hInvalid, hPresent, ↓reduceIte]

/-- Convert an authenticated cached child root into a planned ancestor opening.
The provenance tag is produced here, and Rust's `must_exist` rule is checked
against the durable guard. Authentication failure is never treated as a miss. -/
def planBaggyCachedChild (mac : BaggyCacheMessage → BitVec 256)
    (suite : BaggySuite256) (p : BaggyTreeParams)
    (identity : BaggyLedgerIdentity) (guard : DurableStaticWotsGuard)
    (entry : BaggyAuthenticatedCacheEntry) (childKp : Nat) (childPlan : BaggyLayerCachePlan p)
    (r : StaticWotsOpeningRecord) : Option BaggyPlannedOpening :=
  if verifyBaggyCacheMac mac identity entry && decide
      (1 ≤ r.layer ∧ entry.message.layer = r.layer - 1 ∧
        entry.message.tree = baggyChildTreeIdx p r.tree r.kp ∧
        entry.message.root = r.signedNode) then
    match authenticateBaggyLayerPlan suite p identity.pkSeed entry.message.layer
        entry.message.tree childKp childPlan with
    | some (some root, provenance) =>
      let plan : BaggyPlannedOpening := ⟨r, provenance⟩
      if root == entry.message.root && admitBaggyPlannedOpening guard plan then some plan else none
    | _ => none
  else none

private theorem enforceDurableStaticOpenings_preserves_lookup
    (g g' : DurableStaticWotsGuard) (recs : List StaticWotsOpeningRecord)
    (l t k : Nat) (d : WotsC256Digits)
    (hEq : enforceDurableStaticOpenings g recs = some g')
    (hLook : lookupDurableDigits g l t k = some d) :
    lookupDurableDigits g' l t k = some d := by
  induction recs generalizing g with
  | nil =>
    injection hEq with h; subst h; exact hLook
  | cons rec rest ih =>
    unfold enforceDurableStaticOpenings at hEq
    cases hRec : lookupDurableDigits g rec.layer rec.tree rec.kp with
    | some prevDigits =>
      rw [hRec] at hEq
      dsimp only at hEq
      cases hSameDigits : (prevDigits == rec.digits)
      · rw [hSameDigits] at hEq; simp at hEq
      · rw [hSameDigits] at hEq; simp only [↓reduceIte] at hEq
        exact ih g hEq hLook
    | none =>
      rw [hRec] at hEq
      dsimp only at hEq
      have hLook' :
          lookupDurableDigits ((rec.layer, rec.tree, rec.kp, rec.digits) :: g) l t k = some d := by
        unfold lookupDurableDigits
        cases hSame : (rec.layer == l && rec.tree == t && rec.kp == k)
        · exact hLook
        · rcases Bool.and_eq_true_iff.mp hSame with ⟨h12, hk⟩
          rcases Bool.and_eq_true_iff.mp h12 with ⟨hl, ht⟩
          rw [eq_of_beq hl, eq_of_beq ht, eq_of_beq hk, hLook] at hRec
          cases hRec
      exact ih _ hEq hLook'

/-- Multi-session invariant of `baggyReleaseStep`: staged writes preserve all existing durable
    entries, and every released static opening record is anchored in `st.durable`. -/
def BaggyReleaseInv {identity : BaggyLedgerIdentity} (st : BaggyReleaseState identity) : Prop :=
  (st.phase = .written →
    ∀ l t k d, lookupDurableDigits st.durable l t k = some d →
      lookupDurableDigits st.staged l t k = some d) ∧
  (∀ r ∈ st.released, lookupDurableDigits st.durable r.layer r.tree r.kp = some r.digits)

private theorem baggyReleaseStep_preserves_inv {identity : BaggyLedgerIdentity}
    (st : BaggyReleaseState identity) (op : BaggyReleaseOp) (hInv : BaggyReleaseInv st) :
    BaggyReleaseInv (baggyReleaseStep st op) ∧
    (∀ l t k d, lookupDurableDigits st.durable l t k = some d →
      lookupDurableDigits (baggyReleaseStep st op).durable l t k = some d) := by
  unfold baggyReleaseStep
  cases op with
  | crash =>
    exact ⟨⟨(fun h => by cases h), hInv.2⟩, fun _ _ _ _ h => h⟩
  | storageFailure =>
    exact ⟨⟨(fun h => by cases h), hInv.2⟩, fun _ _ _ _ h => h⟩
  | verificationFailure =>
    exact ⟨⟨(fun h => by cases h), hInv.2⟩, fun _ _ _ _ h => h⟩
  | plan ps =>
    dsimp only
    split
    · exact ⟨⟨(fun h => by cases h), hInv.2⟩, fun _ _ _ _ h => h⟩
    · exact ⟨⟨(fun h => by cases h), hInv.2⟩, fun _ _ _ _ h => h⟩
  | write =>
    dsimp only
    split
    · cases hEnf : enforceDurableStaticOpenings st.durable (st.plan.map (·.record)) with
      | none =>
        exact ⟨⟨(fun h => by cases h), hInv.2⟩, fun _ _ _ _ h => h⟩
      | some staged =>
        refine ⟨⟨(fun _ l t k d hLook =>
          enforceDurableStaticOpenings_preserves_lookup st.durable staged _ l t k d hEnf hLook),
          hInv.2⟩, fun _ _ _ _ h => h⟩
    · exact ⟨⟨(fun h => by cases h), hInv.2⟩, fun _ _ _ _ h => h⟩
  | syncAck =>
    dsimp only
    cases hPh : (st.phase == .written)
    · rw [ite_neg (by decide)]
      exact ⟨⟨(fun h => by cases h), hInv.2⟩, fun _ _ _ _ h => h⟩
    · rw [ite_pos rfl]
      have hWr : st.phase = .written := eq_of_beq hPh
      refine ⟨⟨(fun h => by cases h), fun r hr => hInv.1 hWr r.layer r.tree r.kp r.digits (hInv.2 r hr)⟩,
        fun l t k d hLook => hInv.1 hWr l t k d hLook⟩
  | release =>
    dsimp only
    split
    next hGuard =>
      have hAll := (Bool.and_eq_true_iff.mp hGuard).2
      refine ⟨⟨(fun h => by cases h), fun r hr => ?_⟩, fun _ _ _ _ h => h⟩
      rcases List.mem_append.mp hr with hOld | hNew
      · exact hInv.2 r hOld
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hNew
        exact eq_of_beq (List.all_eq_true.mp hAll p hp)
    next =>
      exact ⟨⟨(fun h => by cases h), hInv.2⟩, fun _ _ _ _ h => h⟩

/-- **Multi-Session `Baggy` Durable Anchoring & Cross-Session Static `WOTS+C` Non-Equivocation**:
    Across ANY arbitrary multi-session sequence `ops : List BaggyReleaseOp` (interleaving
    `.opened` session progression, `.crash`, `.storageFailure`, and `.verificationFailure`),
    every released static opening is durably anchored in `durable`, and NO two released openings
    at the same static `(layer, tree, kp)` address can ever carry distinct `WotsC256Digits`. -/
theorem baggy_multiturn_durable_and_non_equivocating (identity : BaggyLedgerIdentity)
    (ops : List BaggyReleaseOp) :
    let final := baggyReleaseTrace (BaggyReleaseState.init identity) ops
    (∀ r ∈ final.released,
      lookupDurableDigits final.durable r.layer r.tree r.kp = some r.digits) ∧
    (∀ r₁ ∈ final.released, ∀ r₂ ∈ final.released,
      r₁.layer = r₂.layer → r₁.tree = r₂.tree → r₁.kp = r₂.kp → r₁.digits = r₂.digits) := by
  have hInv : BaggyReleaseInv (baggyReleaseTrace (BaggyReleaseState.init identity) ops) := by
    suffices hGen : ∀ (st : BaggyReleaseState identity) (tr : List BaggyReleaseOp),
        BaggyReleaseInv st → BaggyReleaseInv (baggyReleaseTrace st tr) by
      exact hGen (BaggyReleaseState.init identity) ops ⟨(fun h => by cases h), (fun _ hr => by cases hr)⟩
    intro st tr h0
    induction tr generalizing st with
    | nil => exact h0
    | cons op rest ih =>
      exact ih (baggyReleaseStep st op) (baggyReleaseStep_preserves_inv st op h0).1
  refine ⟨hInv.2, fun r₁ hr₁ r₂ hr₂ hl ht hk => ?_⟩
  have h1 := hInv.2 r₁ hr₁
  have h2 := hInv.2 r₂ hr₂
  rw [hl, ht, hk] at h1
  exact Option.some.inj (h1.symm.trans h2)

/-- Any released static opening in a multi-session `Baggy` trace is durably anchored, and any
    other released opening at the same `(layer, tree, kp)` carries the identical codeword. -/
theorem baggy_released_opening_durable_and_unique (identity : BaggyLedgerIdentity)
    (ops : List BaggyReleaseOp) (r : StaticWotsOpeningRecord)
    (hr : r ∈ (baggyReleaseTrace (BaggyReleaseState.init identity) ops).released) :
    lookupDurableDigits (baggyReleaseTrace (BaggyReleaseState.init identity) ops).durable
      r.layer r.tree r.kp = some r.digits ∧
    ∀ r₂ ∈ (baggyReleaseTrace (BaggyReleaseState.init identity) ops).released,
      r.layer = r₂.layer → r.tree = r₂.tree → r.kp = r₂.kp → r.digits = r₂.digits :=
  let h := baggy_multiturn_durable_and_non_equivocating identity ops
  ⟨h.1 r hr, fun r₂ hr₂ hl ht hk => h.2 r hr r₂ hr₂ hl ht hk⟩

/-- Concrete two-session `.opened`-progression witness: session 1 completes `.plan -> .write -> .syncAck -> .release`
    into `.opened`, then session 2 advances directly from `.opened` to release a second distinct static opening! -/
theorem witness_baggy_two_session_opened_progression :
    ∃ (identity : BaggyLedgerIdentity) (ops : List BaggyReleaseOp) (r : StaticWotsOpeningRecord),
      r ∈ (baggyReleaseTrace (BaggyReleaseState.init identity) ops).released ∧
      (baggyReleaseTrace (BaggyReleaseState.init identity) ops).phase = .opened ∧
      (baggyReleaseTrace (BaggyReleaseState.init identity) ops).released.length = 2 := by
  let id0 : BaggyLedgerIdentity := ⟨0#256, 0#256, 0#256⟩
  let d0 : WotsC256Digits :=
    { digits := fun i => if i.val < 64 then ⟨3, by decide⟩ else ⟨0, by decide⟩
      sum_eq := (qsum_eq_qsumUnrolled _ _).trans (by decide) }
  let r1 : StaticWotsOpeningRecord := ⟨1, 0, 0, 1#256, d0⟩
  let r2 : StaticWotsOpeningRecord := ⟨1, 0, 1, 2#256, d0⟩
  let ops : List BaggyReleaseOp :=
    [.plan [⟨r1, .computed⟩], .write, .syncAck, .release,
     .plan [⟨r2, .computed⟩], .write, .syncAck, .release]
  have hRun :
      baggyReleaseTrace (BaggyReleaseState.init id0) ops =
        { durable := [(1, 0, 1, d0), (1, 0, 0, d0)]
          staged := [(1, 0, 1, d0), (1, 0, 0, d0)]
          plan := [⟨r2, .computed⟩]
          phase := .opened
          released := [r1, r2] } := by
    simp [id0, ops, r1, r2, BaggyReleaseState.init, baggyReleaseTrace, baggyReleaseStep,
      admitBaggyPlannedOpening, enforceDurableStaticOpenings, lookupDurableDigits]
  refine ⟨id0, ops, r1, ?_, ?_, ?_⟩
  · rw [hRun]; exact List.mem_cons_self
  · rw [hRun]
  · rw [hRun]; rfl

/-- `#tooth`: once session 1 releases `r1`, any second session attempting to release a conflicting
    codeword `r2` (`r1.digits ≠ r2.digits`) at the same `(layer, tree, kp)` is rejected before
    durability and never enters `released`. -/
theorem tooth_baggy_conflicting_digits_not_released
    (identity : BaggyLedgerIdentity) (r1 r2 : StaticWotsOpeningRecord)
    (hl : r1.layer = r2.layer) (ht : r1.tree = r2.tree) (hk : r1.kp = r2.kp)
    (hDiff : r1.digits ≠ r2.digits) :
    r2 ∉ (baggyReleaseTrace (BaggyReleaseState.init identity)
      [.plan [⟨r1, .computed⟩], .write, .syncAck, .release,
       .plan [⟨r2, .computed⟩], .write, .syncAck, .release]).released := by
  intro hr2
  have hr1 : r1 ∈ (baggyReleaseTrace (BaggyReleaseState.init identity)
      [.plan [⟨r1, .computed⟩], .write, .syncAck, .release,
       .plan [⟨r2, .computed⟩], .write, .syncAck, .release]).released := by
    have hDiffBeq : (r1.digits == r2.digits) = false := beq_eq_false_iff_ne.mpr hDiff
    simp [BaggyReleaseState.init, baggyReleaseTrace, baggyReleaseStep,
      admitBaggyPlannedOpening, enforceDurableStaticOpenings, lookupDurableDigits,
      hl, ht, hk, hDiffBeq]
  exact hDiff ((baggy_released_opening_durable_and_unique identity _ r1 hr1).2 r2 hr2 hl ht hk)

run_cmd do
  let env ← Lean.getEnv
  let names : Array Lean.Name := #[
    `Qsag.rss256_product_degree_two_roots,
    `Qsag.rss256_product_residual_evaluation,
    `Qsag.rss256_step_zero_derived_coin_rejected,
    `Qsag.rss256_recorded_step_preserves_checked,
    `Qsag.rss256_recorded_release_integrity,
    `Qsag.rss256_recorded_trace_integrity,
    `Qsag.baggy_release_has_durable_codeword,
    `Qsag.baggy_multiturn_durable_and_non_equivocating,
    `Qsag.baggy_released_opening_durable_and_unique,
    `Qsag.witness_baggy_two_session_opened_progression,
    `Qsag.tooth_baggy_crash_between_write_and_sync,
    `Qsag.tooth_baggy_conflicting_digits_not_released,
    `Qsag.baggy_cache_authentic_or_forgery,
    `Qsag.baggy_invalid_cache_entry_rejects,
    `Qsag.context_cut_fault_extract,
    `Qsag.tooth_context_cut_epoch_replay,
    `Qsag.signed_slashing_attribution,
    `Qsag.evalGeneratedDkgFrobenius_sound,
    `Qsag.rss256_inline_wave_two_pass_product_proof_sound]
  for name in names do
    if (env.find? name).isNone then
      throwError "Missing Baggy/RSS256 declaration {name}"
    let dependencies ← Lean.collectAxioms name
    let forbidden := dependencies.filter fun ax => ax != ``propext && ax != ``Quot.sound
    unless forbidden.isEmpty do
      throwError "Forbidden axioms in {name}: {forbidden}"


/-- The adaptive error is nonzero yet passes the challenge it was chosen after. -/
theorem tooth_pre_wave_adaptive_error_exists (chi : Tower128) :
    ∃ errors : List Tower128,
      (∃ e ∈ errors, e ≠ towerZero 7) ∧ batchDeviationPoly errors chi = towerZero 7 :=
  ⟨preWaveKernelFaultPair chi, tooth_pre_wave_challenge_kernel_bypass.1 chi⟩

#verify_inhabited rss256_one_corrupt_view_pointwise_and_count_eq inhabited_rss256_privacy_soundness_and_poison
#verify_inhabited baggy_released_opening_durable_and_unique witness_baggy_two_session_opened_progression
#tooth_pair baggy_released_opening_durable_and_unique vs tooth_baggy_conflicting_digits_not_released
#tooth_pair rss256_polynomial_gate_weight_soundness vs tooth_pre_wave_adaptive_error_exists

/-! ### Exports for lane custody-a -/

/-- `wotsCDibits128` is the production digit map `wotsC256DigitOfDigest`. -/
theorem wotsCDibits128_eq_digitOfDigest (digest : BitVec 256) :
    wotsCDibits128 digest = wotsC256DigitOfDigest digest := by
  unfold wotsCDibits128
  rfl

end Qsag
end
