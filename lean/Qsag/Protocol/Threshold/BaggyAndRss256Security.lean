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

public import Qsag.Math.Constructive
public import Qsag.Math.Goldilocks
public import Qsag.Math.BinaryTower
public import Qsag.Oracle.UcGames
public import Qsag.Exec.SimulationSpine
public import Qsag.Protocol.Threshold.MaliciousSecurity
public import Qsag.Exec.InteractiveUcEngine
public import Qsag.Protocol.Threshold.RssSlhFullSecurity
public import Qsag.Protocol.Threshold.Rss256TwoPassProductProof

import all Qsag.Oracle.UcGames
import all Qsag.Math.BinaryTower
import all Qsag.Protocol.Threshold.MaliciousSecurity
import all Qsag.Exec.InteractiveUcEngine
import all Qsag.Protocol.Threshold.RssSlhFullSecurity
import all Qsag.Protocol.Threshold.Rss256TwoPassProductProof
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
  sum_eq : finSum 128 (fun i => (digits i).val) = 192

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
    so `whnf` never unfolds the 128-term `finSum` during elaboration or kernel `Decidable` synthesis! -/
def wotsC256DigitSum (f : Fin 128 → Fin 4) : Nat :=
  finSum 128 (fun i => (f i).val)

theorem wotsC256DigitSum_eq (f : Fin 128 → Fin 4) :
    wotsC256DigitSum f = finSum 128 (fun i => (f i).val) := by
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
    (hNe : finSum 128 (fun i => (wotsC256DigitOfDigest dig i).val) ≠ 192) :
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

private theorem finSum_eq_of_le_pointwise_eq :
    ∀ (n : Nat) (f g : Fin n → Nat),
      (∀ i : Fin n, f i ≤ g i) →
      finSum n f = finSum n g →
      ∀ i : Fin n, f i = g i
  | 0, _, _, _, _, i => Fin.elim0 i
  | n + 1, f, g, hLe, hSum, i => by
    simp only [finSum] at hSum
    let i0 : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
    let f' : Fin n → Nat := fun j => f ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
    let g' : Fin n → Nat := fun j => g ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
    have hLe0 : f i0 ≤ g i0 := hLe i0
    have hLeRest : finSum n f' ≤ finSum n g' :=
      finSum_le_finSum (fun j => hLe ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
    obtain ⟨hEq0, hEqRest⟩ := add_eq_of_le_parts hLe0 hLeRest hSum
    match i with
    | ⟨0, _⟩ => exact hEq0
    | ⟨k + 1, hk⟩ =>
      exact finSum_eq_of_le_pointwise_eq n f' g'
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
      have hEqSum : finSum 128 (fun i => (d.digits i).val) = finSum 128 (fun i => (d'.digits i).val) :=
        d.sum_eq.trans d'.sum_eq.symm
      have hPt := finSum_eq_of_le_pointwise_eq 128 _ _ hLe hEqSum
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
        finSum 128 (fun j => (wotsC256DigitOfDigest (suite.thDigest pkSeed adrs msg' ctr') j).val) = 193 := by
      have hCongr :
          finSum 128 (fun j => (wotsC256DigitOfDigest (suite.thDigest pkSeed adrs msg' ctr') j).val) =
          finSum 128 (fun j => (d.digits j).val + (if j = i then 1 else 0)) := by
        apply finSum_congr
        intro j
        rw [hSteppedDigest j]
        if hj : j = i then
          subst hj; simp
        else
          simp [hj]
      rw [hCongr, finSum_add, d.sum_eq, finSum_eq_indicator 128 i]
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
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [lowBits, hi]

private theorem highBits_xor_7 (u v : BitVec 256) :
    highBits 7 (u ^^^ v) = highBits 7 u ^^^ highBits 7 v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [highBits, hi]

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

/-- **Exact 1-Corrupt `Rss256Engine` View Privacy (`rss256_one_corrupt_perfect_view_privacy`)**:
    Under the corrected `(prg1, prg2, prg0)` mask-key assignment, for EVERY corrupt party
    `corrupt ∈ {P0, P1, P2}`, EVERY secret 256-lane input `(x, y)`, EVERY valid `BGIN19` degree-2
    witness `w`, EVERY challenge `τ ∈ GF(2^{128})`, and EVERY distinguisher `D`:
    1. `rss256SimCorruptView` (using **0** bits of the missing honest share slot!) equals
       `rss256RealCorruptView` point-for-point under `rss256_and_bgin19_privacy_equiv`;
    2. Acceptance counts are equal and rational statistical distance is **identically `0`**! -/
theorem rss256_one_corrupt_perfect_view_privacy
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
    distAcceptCount padCard realExec D = distAcceptCount padCard simExec D ∧
    ratLe (rationalAcceptDiff padCard realExec padCard simExec D) (0, 1) := by
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
      dsimp [depProdFinEquiv, finBitVecXorEquiv]
      rw [splitFinLeft_pairFin (Nat.two_pow_pos 256)]
    have hSplitR : ∀ (dAnd dBgin : BitVec 256),
        BitVec.ofFin (splitFinRight (Nat.two_pow_pos 256)
          ((depProdFinEquiv (Nat.two_pow_pos 256) (finBitVecXorEquiv 256 dAnd)
            (fun _ => finBitVecXorEquiv 256 dBgin)).toFun ω)) =
        BitVec.ofFin (splitFinRight (Nat.two_pow_pos 256) ω) ^^^ dBgin := by
      intro dAnd dBgin
      dsimp [depProdFinEquiv, finBitVecXorEquiv]
      rw [splitFinRight_pairFin (Nat.two_pow_pos 256)]
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
  have hCountEq : distAcceptCount padCard realExec D = distAcceptCount padCard simExec D := by
    unfold distAcceptCount
    calc
      finSum padCard (fun ω => if D (realExec ω) then 1 else 0) =
        finSum padCard (fun ω => if D (simExec (bij.toFun ω)) then 1 else 0) :=
          finSum_congr (fun ω => by rw [hPointwise ω])
      _ = finSum padCard (fun ω => if D (simExec ω) then 1 else 0) :=
          finSum_equiv_eq bij (fun ω => if D (simExec ω) then 1 else 0)
  have hBad := bad_event_fundamental_lemma padCard hCardPos realExec simExec bij
    (fun _ => false) (fun ω _ => hPointwise ω) D
  have hZeroBad : finSum padCard (fun _ : Fin padCard => if false then 1 else 0) = 0 := by
    simp [finSum_const]
  have hRatDiff : ratLe (rationalAcceptDiff padCard realExec padCard simExec D) (0, 1) := by
    obtain ⟨_, _, hR⟩ := hBad
    rw [hZeroBad] at hR
    refine ⟨hR.1, by decide, ?_⟩
    have hNum0 : (rationalAcceptDiff padCard realExec padCard simExec D).1 * padCard ≤ 0 := by
      simpa only [Nat.zero_mul] using hR.2.2
    have hProd0 : (rationalAcceptDiff padCard realExec padCard simExec D).1 * padCard = 0 :=
      Nat.eq_zero_of_le_zero hNum0
    rcases Nat.mul_eq_zero.mp hProd0 with hN0 | hC0
    · rw [hN0]; simp
    · exact False.elim (Nat.ne_of_gt hCardPos hC0)
  exact ⟨hPointwise, hCountEq, hRatDiff⟩

/-- Verifier `P0`'s pad-cancellation extractor against the naive `(prg0, prg1, prg2)` assignment. -/
