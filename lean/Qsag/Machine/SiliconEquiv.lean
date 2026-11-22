module
/-
# Qsag.Machine.SiliconEquiv — Mechanized RTL-to-Lean Equivalence (`Arch 4`: FPGA & Dregg-180 Silicon)

Constructive bit-level and cycle-level hardware equivalence proofs (`0 sorry`, `0 bv_decide`,
`0 native_decide`, `0 Classical.choice`, `axioms ⊆ {propext, Quot.sound}`) bridging `qsag`'s
SystemVerilog RTL datapaths directly to canonical `Qsag.Math.Goldilocks`:

1. **Carry-Save & Parallel-Prefix Adder Primitives (`qsag_csa32`, `qsag_csa52`, `qsag_csa_reduce2`,
   `qsag_prefix_add`, `qsag_add_split`)**:
   - Exact bit-level full-adder 3:2 (`rtlCsa32`), 5:2 (`rtlCsa52`), and recursive Wallace/CSA tree
     (`rtlCsaReduce2`) compressors proved over arbitrary bitwidth `w` via inductive bit-weight
     identities (`natOfBits_csa_identity`, `0 bv_decide`).
   - Exact arbitrary-width Han-Carlson parallel-prefix adder (`rtlPrefixAdd`, modeling
     `hardware/gf180mcu/rtl/qsag_gl64_karatsuba_csa.sv:15-77`) and Kogge-Stone chunked split adder
     (`rtlAddSplit3Chunk`, modeling `hardware/fpga/rtl/qsag_add_split.sv`).
2. **FPGA 136-Bit Solinas Goldilocks Reducer (`hardware/fpga/rtl/qsag_gl64_reduce.sv`)**:
   - Models the exact 6-term inverted Solinas CSA stage (`t0..t5` with `C_BIAS = GL_P + 3`, 66-bit
     `qsag_csa_reduce2` + `qsag_add_split`) and Stage-2 parallel `NEG_1P` / `NEG_2P` 67-bit sign-bit
     canonicalizer (`rtlFpgaGl64Reduce` and 2-stage registered `rtlFpgaGl64Step`).
   - Proves exact bit-for-bit equivalence `(rtlFpgaGl64Reduce x).toNat = (Goldilocks.ofNat x.toNat).val`
     across **all** `2^136` inputs (`0 ≤ x < 2^136`), plus latency-2 pipeline equivalence for `REG_OUT = 1`.
3. **GF180MCU ASIC `Dregg-180` Booth-Karatsuba-CSA Goldilocks Engine
   (`hardware/gf180mcu/rtl/qsag_gl64_karatsuba_csa.sv`)**:
   - Models `qsag_gl64_canon` (76-bit guard-bit fold + `ε = 2^32 - 1` conditional correction),
     `qsag_mul33` (17-row radix-4 Booth encoder + `neg_row` + 66-bit CSA tree + Han-Carlson CPA),
     `qsag_gl64_sqrows` / `qsag_gl64_sq_pipe` (5-row 64-bit Goldilocks squarer), and the 4-cycle
     `mph = 0..3` `qsag_gl64_karatsuba_csa` FSM (`rtlKaratsubaStep`).
   - Proves exact equivalence of `rtlMul33` (`= a * b` for all 33-bit operands), `rtlGl64SqPipe`
     (`= Goldilocks.mul a a`), and the 4-cycle `qsag_gl64_karatsuba_csa` state machine
     (`= Goldilocks.mul a b` for all 64-bit inputs, even non-canonical `[p, 2^64 - 1]`)!
-/

public import Qsag.Math.Goldilocks
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Silicon

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

private theorem ite_pos {α : Type} {c : Prop} [Decidable c] (h : c) (t e : α) :
    (if c then t else e) = t := by
  split
  · rfl
  · next hn => exact absurd h hn

private theorem ite_neg {α : Type} {c : Prop} [Decidable c] (h : ¬ c) (t e : α) :
    (if c then t else e) = e := by
  split
  · next hp => exact absurd hp h
  · rfl

private theorem dite_pos {α : Type} {c : Prop} [Decidable c] (h : c)
    (t : c → α) (e : ¬ c → α) : (if hc : c then t hc else e hc) = t h := by
  split
  · rfl
  · next hn => exact absurd h hn

private theorem dite_neg {α : Type} {c : Prop} [Decidable c] (h : ¬ c)
    (t : c → α) (e : ¬ c → α) : (if hc : c then t hc else e hc) = e h := by
  split
  · next hp => exact absurd hp h
  · rfl

/-! ## 1. Constructive Bit-Weight Foundations (`natOfBits`, `0 bv_decide`) -/

/-- Weighted binary value `∑_{i=0}^{w-1} 2^i * (f i).toNat`. -/
def natOfBits : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | w + 1, f => (f 0).toNat + 2 * natOfBits w (fun i => f (i + 1))

theorem natOfBits_lt : ∀ (w : Nat) (f : Nat → Bool), natOfBits w f < 2 ^ w
  | 0, _ => by rw [natOfBits]; decide
  | w + 1, f => by
    have ih := natOfBits_lt w (fun i => f (i + 1))
    have hb : (f 0).toNat ≤ 1 := by cases f 0 <;> decide
    have hp : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ]; omega
    dsimp only [natOfBits]
    omega

theorem natOfBits_congr : ∀ {w : Nat} {f g : Nat → Bool},
    (∀ i, i < w → f i = g i) → natOfBits w f = natOfBits w g
  | 0, _, _, _ => rfl
  | w + 1, f, g, h => by
    dsimp only [natOfBits]
    rw [h 0 (Nat.zero_lt_succ w),
        natOfBits_congr (fun i hi => h (i + 1) (Nat.succ_lt_succ hi))]

theorem testBit_natOfBits : ∀ (w : Nat) (f : Nat → Bool) (i : Nat),
    (natOfBits w f).testBit i = (decide (i < w) && f i)
  | 0, _, i => by
    rw [natOfBits, Nat.zero_testBit, decide_eq_false (Nat.not_lt_zero i), Bool.false_and]
  | w + 1, f, 0 => by
    dsimp only [natOfBits]
    rw [decide_eq_true (Nat.zero_lt_succ w), Bool.true_and, Nat.testBit_zero]
    cases f 0 <;> simp [Bool.toNat, Nat.add_mul_mod_self_left]
  | w + 1, f, j + 1 => by
    dsimp only [natOfBits]
    rw [Nat.testBit_succ]
    have hDiv : ((f 0).toNat + 2 * natOfBits w (fun i => f (i + 1))) / 2 =
        natOfBits w (fun i => f (i + 1)) := by
      cases f 0 <;> dsimp only [Bool.toNat, cond] <;> omega
    rw [hDiv, testBit_natOfBits w (fun i => f (i + 1)) j]
    have hCmp : decide (j < w) = decide (j + 1 < w + 1) := by
      by_cases h : j < w
      · rw [decide_eq_true h, decide_eq_true (Nat.succ_lt_succ h)]
      · rw [decide_eq_false h, decide_eq_false (fun h' => h (Nat.lt_of_succ_lt_succ h'))]
    rw [hCmp]

theorem bitVec_toNat_eq_natOfBits {w : Nat} (v : BitVec w) :
    v.toNat = natOfBits w v.getLsbD := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_natOfBits]
  by_cases hi : i < w
  · rw [decide_eq_true hi, Bool.true_and]; rfl
  · have hGe : w ≤ i := by omega
    have hLtPow : v.toNat < 2 ^ i :=
      Nat.lt_of_lt_of_le v.isLt (Nat.pow_le_pow_right (by decide) hGe)
    rw [decide_eq_false hi, Bool.false_and]
    exact Nat.testBit_lt_two_pow hLtPow

private theorem natOfBits_not_add :
    ∀ (w : Nat) (f : Nat → Bool),
      natOfBits w (fun i => !(f i)) + natOfBits w f = 2 ^ w - 1
  | 0, _ => rfl
  | w + 1, f => by
    dsimp only [natOfBits]
    have h0 : (!(f 0)).toNat + (f 0).toNat = 1 := by cases f 0 <;> rfl
    have ih := natOfBits_not_add w (fun i => f (i + 1))
    have hPos : 1 ≤ 2 ^ w := Nat.one_le_two_pow
    rw [Nat.pow_succ]
    omega

theorem bitVec_not_toNat {w : Nat} (v : BitVec w) :
    (~~~v).toNat = 2 ^ w - 1 - v.toNat := by
  have hLhs : (~~~v).toNat = natOfBits w (fun i => !(v.getLsbD i)) := by
    rw [bitVec_toNat_eq_natOfBits]
    apply natOfBits_congr
    intro i hi
    rw [BitVec.not_def, BitVec.getLsbD_xor, Qsag.Constructive.getLsbD_allOnes,
        decide_eq_true hi, Bool.true_xor]
  have hSum := natOfBits_not_add w v.getLsbD
  rw [← hLhs, ← bitVec_toNat_eq_natOfBits] at hSum
  omega

/-! ## 2. Carry-Save Compressors (`qsag_csa32`, `qsag_csa52`, `qsag_csa_reduce2`) -/

/-- Full-adder sum bit `a ^ b ^ c`. -/
def faSum (a b c : Bool) : Bool := (a ^^ b) ^^ c

/-- Full-adder majority/carry bit `(a & b) | (a & c) | (b & c)`. -/
def faMaj (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

theorem fa_bit_identity (a b c : Bool) :
    (faSum a b c).toNat + 2 * (faMaj a b c).toNat = a.toNat + b.toNat + c.toNat := by
  cases a <;> cases b <;> cases c <;> rfl

private theorem natOfBits_csa_identity :
    ∀ (w : Nat) (fa fb fc : Nat → Bool),
      natOfBits w (fun i => faSum (fa i) (fb i) (fc i)) +
        2 * natOfBits w (fun i => faMaj (fa i) (fb i) (fc i)) =
      natOfBits w fa + natOfBits w fb + natOfBits w fc
  | 0, _, _, _ => rfl
  | w + 1, fa, fb, fc => by
    dsimp only [natOfBits]
    have h0 := fa_bit_identity (fa 0) (fb 0) (fc 0)
    have ih := natOfBits_csa_identity w (fun i => fa (i + 1)) (fun i => fb (i + 1)) (fun i => fc (i + 1))
    omega

/-- Exact RTL model of `qsag_csa32` (`qsag_gl64_karatsuba_csa.sv:170-197`) and one 3:2 cell of
    `qsag_csa_reduce2` (`qsag_csa_reduce2.sv:23-29`). -/
def rtlCsa32 (w : Nat) (a b c : BitVec w) : BitVec w × BitVec w :=
  let s := a ^^^ b ^^^ c
  let m := (a &&& b) ||| (a &&& c) ||| (b &&& c)
  (s, m <<< 1)

private theorem rtlCsa32_raw_sum {w : Nat} (a b c : BitVec w) :
    let s := a ^^^ b ^^^ c
    let m := (a &&& b) ||| (a &&& c) ||| (b &&& c)
    s.toNat + 2 * m.toNat = a.toNat + b.toNat + c.toNat := by
  intro s m
  have hs : s.toNat = natOfBits w (fun i => faSum (a.getLsbD i) (b.getLsbD i) (c.getLsbD i)) := by
    rw [bitVec_toNat_eq_natOfBits]
    apply natOfBits_congr; intro i _; simp [s, faSum]
  have hm : m.toNat = natOfBits w (fun i => faMaj (a.getLsbD i) (b.getLsbD i) (c.getLsbD i)) := by
    rw [bitVec_toNat_eq_natOfBits]
    apply natOfBits_congr; intro i _; simp [m, faMaj]
  rw [hs, hm, natOfBits_csa_identity, ← bitVec_toNat_eq_natOfBits,
      ← bitVec_toNat_eq_natOfBits, ← bitVec_toNat_eq_natOfBits]

/-- **Unconditional Modular 3:2 CSA Soundness (`rtlCsa32_mod`)**:
    `(s + cy) mod 2^w = (a + b + c) mod 2^w` for all `w`-bit operands. -/
theorem rtlCsa32_mod (w : Nat) (a b c : BitVec w) :
    ((rtlCsa32 w a b c).1.toNat + (rtlCsa32 w a b c).2.toNat) % 2 ^ w =
      (a.toNat + b.toNat + c.toNat) % 2 ^ w := by
  dsimp only [rtlCsa32]
  have hRaw := rtlCsa32_raw_sum a b c
  dsimp only at hRaw
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one, Nat.add_mod_mod,
      Nat.mul_comm _ 2, hRaw]

/-- **Exact Non-Wrapping 3:2 CSA Soundness (`rtlCsa32_exact`)**:
    Whenever `a + b + c < 2^w`, the MSB carry-out vanishes so `s + cy = a + b + c` as exact `Nat`s! -/
theorem rtlCsa32_exact {w : Nat} (a b c : BitVec w)
    (hBound : a.toNat + b.toNat + c.toNat < 2 ^ w) :
    (rtlCsa32 w a b c).1.toNat + (rtlCsa32 w a b c).2.toNat =
      a.toNat + b.toNat + c.toNat := by
  dsimp only [rtlCsa32]
  have hRaw := rtlCsa32_raw_sum a b c
  dsimp only at hRaw
  have hSh : ((((a &&& b) ||| (a &&& c) ||| (b &&& c)) <<< 1)).toNat =
      2 * ((a &&& b) ||| (a &&& c) ||| (b &&& c)).toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm,
        Nat.mod_eq_of_lt (by omega)]
  rw [hSh, hRaw]

/-- Exact RTL model of `qsag_csa52` (`qsag_gl64_karatsuba_csa.sv:200-215`): 5-to-2 compressor. -/
def rtlCsa52 (w : Nat) (x y r1 r2 r3 : BitVec w) : BitVec w × BitVec w :=
  let (s1, c1) := rtlCsa32 w x y r1
  let (s2, c2) := rtlCsa32 w s1 r2 r3
  rtlCsa32 w s2 c1 c2

/-- **Exact Non-Wrapping 5:2 CSA Soundness (`rtlCsa52_exact`)**:
    Matches the RTL contract `"Five rows to two. Exact as long as the integer sum is below 2^N"`. -/
theorem rtlCsa52_exact {w : Nat} (x y r1 r2 r3 : BitVec w)
    (hBound : x.toNat + y.toNat + r1.toNat + r2.toNat + r3.toNat < 2 ^ w) :
    (rtlCsa52 w x y r1 r2 r3).1.toNat + (rtlCsa52 w x y r1 r2 r3).2.toNat =
      x.toNat + y.toNat + r1.toNat + r2.toNat + r3.toNat := by
  dsimp only [rtlCsa52]
  have h1 := rtlCsa32_exact x y r1 (by omega)
  have h2 := rtlCsa32_exact (rtlCsa32 w x y r1).1 r2 r3 (by omega)
  have h3 := rtlCsa32_exact (rtlCsa32 w (rtlCsa32 w x y r1).1 r2 r3).1
    (rtlCsa32 w x y r1).2 (rtlCsa32 w (rtlCsa32 w x y r1).1 r2 r3).2 (by omega)
  omega

theorem rtlCsa52_mod (w : Nat) (x y r1 r2 r3 : BitVec w) :
    ((rtlCsa52 w x y r1 r2 r3).1.toNat + (rtlCsa52 w x y r1 r2 r3).2.toNat) % 2 ^ w =
      (x.toNat + y.toNat + r1.toNat + r2.toNat + r3.toNat) % 2 ^ w := by
  dsimp only [rtlCsa52]
  generalize hs1c1 : rtlCsa32 w x y r1 = p1
  generalize hs2c2 : rtlCsa32 w p1.1 r2 r3 = p2
  have h1 : (p1.1.toNat + p1.2.toNat) % 2 ^ w = (x.toNat + y.toNat + r1.toNat) % 2 ^ w := by
    rw [← hs1c1]; exact rtlCsa32_mod w x y r1
  have h2 : (p2.1.toNat + p2.2.toNat) % 2 ^ w = (p1.1.toNat + r2.toNat + r3.toNat) % 2 ^ w := by
    rw [← hs2c2]; exact rtlCsa32_mod w p1.1 r2 r3
  rw [rtlCsa32_mod w p2.1 p1.2 p2.2]
  calc
    (p2.1.toNat + p1.2.toNat + p2.2.toNat) % 2 ^ w
      = ((p2.1.toNat + p2.2.toNat) + p1.2.toNat) % 2 ^ w := by
        congr 1; omega
    _ = ((p2.1.toNat + p2.2.toNat) % 2 ^ w + p1.2.toNat % 2 ^ w) % 2 ^ w :=
        Nat.add_mod _ _ _
    _ = ((p1.1.toNat + r2.toNat + r3.toNat) % 2 ^ w + p1.2.toNat % 2 ^ w) % 2 ^ w := by
        rw [h2]
    _ = ((p1.1.toNat + r2.toNat + r3.toNat) + p1.2.toNat) % 2 ^ w :=
        (Nat.add_mod _ _ _).symm
    _ = ((p1.1.toNat + p1.2.toNat) + (r2.toNat + r3.toNat)) % 2 ^ w := by
        congr 1; omega
    _ = ((p1.1.toNat + p1.2.toNat) % 2 ^ w + (r2.toNat + r3.toNat) % 2 ^ w) % 2 ^ w :=
        Nat.add_mod _ _ _
    _ = ((x.toNat + y.toNat + r1.toNat) % 2 ^ w + (r2.toNat + r3.toNat) % 2 ^ w) % 2 ^ w := by
        rw [h1]
    _ = ((x.toNat + y.toNat + r1.toNat) + (r2.toNat + r3.toNat)) % 2 ^ w :=
        (Nat.add_mod _ _ _).symm
    _ = (x.toNat + y.toNat + r1.toNat + r2.toNat + r3.toNat) % 2 ^ w := by
        congr 1; omega

/-- One compression pass of `qsag_csa_reduce2` (`qsag_csa_reduce2.sv:23-32`) grouping triples. -/
def csaCompressPass (w : Nat) : List (BitVec w) → List (BitVec w)
  | a :: b :: d :: rest =>
    let (s, c) := rtlCsa32 w a b d
    s :: c :: csaCompressPass w rest
  | tail => tail

theorem csaCompressPass_len_lt (w : Nat) :
    ∀ {xs : List (BitVec w)}, 3 ≤ xs.length → (csaCompressPass w xs).length < xs.length
  | _ :: _ :: _ :: [], _ => by simp [csaCompressPass]
  | _ :: _ :: _ :: x4 :: rest, _ => by
    cases rest with
    | nil => simp [csaCompressPass]
    | cons x5 more =>
      cases more with
      | nil => simp [csaCompressPass]
      | cons x6 more2 =>
        have ih := csaCompressPass_len_lt w (xs := x4 :: x5 :: x6 :: more2) (by simp)
        change (csaCompressPass w (x4 :: x5 :: x6 :: more2)).length + 1 + 1 <
          (x4 :: x5 :: x6 :: more2).length + 1 + 1 + 1
        omega

theorem csaCompressPass_sum_mod (w : Nat) :
    ∀ (xs : List (BitVec w)),
      ((csaCompressPass w xs).map BitVec.toNat).sum % 2 ^ w =
        (xs.map BitVec.toNat).sum % 2 ^ w
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | a :: b :: d :: rest => by
    dsimp only [csaCompressPass, List.map_cons, List.sum_cons]
    have h3 := rtlCsa32_mod w a b d
    have ih := csaCompressPass_sum_mod w rest
    calc
      ((rtlCsa32 w a b d).1.toNat +
          ((rtlCsa32 w a b d).2.toNat + ((csaCompressPass w rest).map BitVec.toNat).sum)) % 2 ^ w
        = (((rtlCsa32 w a b d).1.toNat + (rtlCsa32 w a b d).2.toNat) +
            ((csaCompressPass w rest).map BitVec.toNat).sum) % 2 ^ w := by
          rw [Nat.add_assoc]
      _ = ((a.toNat + b.toNat + d.toNat) % 2 ^ w + (rest.map BitVec.toNat).sum % 2 ^ w) % 2 ^ w := by
          rw [Nat.add_mod, h3, ih]
      _ = (a.toNat + (b.toNat + (d.toNat + (rest.map BitVec.toNat).sum))) % 2 ^ w := by
          rw [← Nat.add_mod]; congr 1; omega

/-- Exact RTL model of `qsag_csa_reduce2` (`qsag_csa_reduce2.sv:4-35`) & `qsag_mul_csa_tree` CSA
    reduction down to `(s, c)`. -/
def rtlCsaReduce2Aux (w : Nat) : Nat → List (BitVec w) → BitVec w × BitVec w
  | _, [] => (0, 0)
  | _, [a] => (a, 0)
  | _, [a, b] => (a, b)
  | 0, a :: b :: _ => (a, b)
  | fuel + 1, xs => rtlCsaReduce2Aux w fuel (csaCompressPass w xs)

def rtlCsaReduce2 (w : Nat) (rows : List (BitVec w)) : BitVec w × BitVec w :=
  rtlCsaReduce2Aux w rows.length rows

theorem rtlCsaReduce2Aux_mod (w : Nat) :
    ∀ (fuel : Nat) (rows : List (BitVec w)),
      rows.length ≤ fuel + 2 →
      ((rtlCsaReduce2Aux w fuel rows).1.toNat + (rtlCsaReduce2Aux w fuel rows).2.toNat) % 2 ^ w =
        (rows.map BitVec.toNat).sum % 2 ^ w
  | _, [], _ => by simp [rtlCsaReduce2Aux]
  | _, [a], _ => by simp [rtlCsaReduce2Aux]
  | _, [a, b], _ => by simp [rtlCsaReduce2Aux]
  | 0, _ :: _ :: _ :: _, hLen => by simp at hLen
  | fuel + 1, a :: b :: d :: rest, hLen => by
    have hLt := csaCompressPass_len_lt w (xs := a :: b :: d :: rest) (by simp)
    have ih := rtlCsaReduce2Aux_mod w fuel (csaCompressPass w (a :: b :: d :: rest)) (by omega)
    dsimp only [rtlCsaReduce2Aux]
    exact ih.trans (csaCompressPass_sum_mod w (a :: b :: d :: rest))

theorem rtlCsaReduce2_mod (w : Nat) (rows : List (BitVec w)) :
    ((rtlCsaReduce2 w rows).1.toNat + (rtlCsaReduce2 w rows).2.toNat) % 2 ^ w =
      (rows.map BitVec.toNat).sum % 2 ^ w :=
  rtlCsaReduce2Aux_mod w rows.length rows (by omega)

/-! ## 3. Han-Carlson Parallel-Prefix Adder (`qsag_prefix_add`) & Split Adder (`qsag_add_split`) -/

/-- Associative `(G, P)` prefix operator `(g_hi | (p_hi & g_lo), p_hi & p_lo)`. -/
def mergeGP (hi lo : Bool × Bool) : Bool × Bool :=
  (hi.1 || (hi.2 && lo.1), hi.2 && lo.2)

theorem mergeGP_assoc (a b c : Bool × Bool) :
    mergeGP a (mergeGP b c) = mergeGP (mergeGP a b) c := by
  rcases a with ⟨ga, pa⟩
  rcases b with ⟨gb, pb⟩
  rcases c with ⟨gc, pc⟩
  cases ga <;> cases pa <;> cases gb <;> cases pb <;> cases gc <;> cases pc <;> rfl

/-- Canonical ripple-carry chain from bit `0` with carry-in `cin`. -/
def rippleCarry (fa fb : Nat → Bool) (cin : Bool) : Nat → Bool
  | 0 => cin
  | i + 1 => (fa i && fb i) || ((fa i ^^ fb i) && rippleCarry fa fb cin i)

private theorem ripple_step_eq_faMaj (a b c : Bool) :
    ((a && b) || ((a ^^ b) && c)) = faMaj a b c := by
  cases a <;> cases b <;> cases c <;> rfl

theorem natOfBits_ripple_sum :
    ∀ (N : Nat) (fa fb : Nat → Bool) (cin : Bool),
      natOfBits N (fun i => (fa i ^^ fb i) ^^ rippleCarry fa fb cin i) +
        2 ^ N * (rippleCarry fa fb cin N).toNat =
      natOfBits N fa + natOfBits N fb + cin.toNat
  | 0, _, _, cin => by simp [natOfBits, rippleCarry]
  | N + 1, fa, fb, cin => by
    dsimp only [natOfBits]
    have hCarry0 : rippleCarry fa fb cin 0 = cin := rfl
    rw [hCarry0]
    have hCarryShift : ∀ k : Nat,
        rippleCarry fa fb cin (k + 1) =
          rippleCarry (fun i => fa (i + 1)) (fun i => fb (i + 1))
            (rippleCarry fa fb cin 1) k := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        change ((fa (k + 1) && fb (k + 1)) || ((fa (k + 1) ^^ fb (k + 1)) && rippleCarry fa fb cin (k + 1))) =
          ((fa (k + 1) && fb (k + 1)) || ((fa (k + 1) ^^ fb (k + 1)) &&
            rippleCarry (fun i => fa (i + 1)) (fun i => fb (i + 1)) (rippleCarry fa fb cin 1) k))
        rw [ih]
    have hSumTail :
        natOfBits N (fun i => (fa (i + 1) ^^ fb (i + 1)) ^^ rippleCarry fa fb cin (i + 1)) =
        natOfBits N (fun i => (fa (i + 1) ^^ fb (i + 1)) ^^
          rippleCarry (fun j => fa (j + 1)) (fun j => fb (j + 1)) (rippleCarry fa fb cin 1) i) := by
      apply natOfBits_congr; intro i _; rw [hCarryShift i]
    rw [hSumTail]
    have ih := natOfBits_ripple_sum N (fun i => fa (i + 1)) (fun i => fb (i + 1))
      (rippleCarry fa fb cin 1)
    have h0 : ((fa 0 ^^ fb 0) ^^ cin).toNat + 2 * (rippleCarry fa fb cin 1).toNat =
        (fa 0).toNat + (fb 0).toNat + cin.toNat := by
      change ((fa 0 ^^ fb 0) ^^ cin).toNat +
          2 * ((fa 0 && fb 0) || ((fa 0 ^^ fb 0) && cin)).toNat =
        (fa 0).toNat + (fb 0).toNat + cin.toNat
      rw [ripple_step_eq_faMaj]
      exact fa_bit_identity (fa 0) (fb 0) cin
    have hp : 2 ^ (N + 1) * (rippleCarry fa fb cin (N + 1)).toNat =
        2 * (2 ^ N * (rippleCarry (fun i => fa (i + 1)) (fun i => fb (i + 1))
          (rippleCarry fa fb cin 1) N).toNat) := by
      rw [hCarryShift N, Nat.pow_succ, Nat.mul_comm (2 ^ N) 2, Nat.mul_assoc]
    rw [hp]
    omega

/-- Contiguous group generate/propagate over `[lo, lo + len)`. -/
def spanGP (fa fb : Nat → Bool) (lo : Nat) : Nat → Bool × Bool
  | 0 => (false, true)
  | len + 1 => mergeGP (fa (lo + len) && fb (lo + len), fa (lo + len) ^^ fb (lo + len))
      (spanGP fa fb lo len)

theorem spanGP_split (fa fb : Nat → Bool) (lo k₁ : Nat) :
    ∀ k₂ : Nat,
      mergeGP (spanGP fa fb (lo + k₁) k₂) (spanGP fa fb lo k₁) =
        spanGP fa fb lo (k₁ + k₂)
  | 0 => by
    rcases spanGP fa fb lo k₁ with ⟨g, p⟩
    cases g <;> cases p <;> rfl
  | k₂ + 1 => by
    have hAdd : k₁ + (k₂ + 1) = (k₁ + k₂) + 1 := by omega
    rw [hAdd]
    dsimp only [spanGP]
    rw [← mergeGP_assoc, spanGP_split fa fb lo k₁ k₂]
    have hIdx : lo + k₁ + k₂ = lo + (k₁ + k₂) := by omega
    rw [hIdx]

theorem spanGP_eval_carry (fa fb : Nat → Bool) (cin : Bool) :
    ∀ k : Nat,
      let gp := spanGP fa fb 0 k
      (gp.1 || (gp.2 && cin)) = rippleCarry fa fb cin k
  | 0 => by simp [spanGP, rippleCarry]
  | k + 1 => by
    have ih := spanGP_eval_carry fa fb cin k
    dsimp only [spanGP, rippleCarry] at ih ⊢
    rw [Nat.zero_add, ← ih]
    rcases spanGP fa fb 0 k with ⟨gk, pk⟩
    cases fa k <;> cases fb k <;> cases gk <;> cases pk <;> cases cin <;> rfl

/-- Smallest `hl` (`≤ k`) such that `n ≤ 2 ^ hl` (`$clog2(N_ODD)` in `qsag_prefix_add`). -/
def clog2Bounded : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, n =>
    if n ≤ 1 then 0 else 1 + clog2Bounded k ((n + 1) / 2)

theorem pow_clog2Bounded_ge :
    ∀ (k n : Nat), n ≤ 2 ^ k → n ≤ 2 ^ clog2Bounded k n
  | 0, n, h => by simp [clog2Bounded] at h ⊢; omega
  | k + 1, n, h => by
    dsimp only [clog2Bounded]
    by_cases h1 : n ≤ 1
    · rw [ite_pos h1]; omega
    · rw [ite_neg h1]
      have hHalf : (n + 1) / 2 ≤ 2 ^ k := by
        rw [Nat.pow_succ] at h; omega
      have ih := pow_clog2Bounded_ge k ((n + 1) / 2) hHalf
      rw [Nat.pow_add, Nat.pow_one]
      omega

private theorem le_two_pow_self : ∀ m : Nat, m ≤ 2 ^ m
  | 0 => by decide
  | m + 1 => by
    have ih := le_two_pow_self m
    have hPos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    rw [Nat.pow_succ]
    omega

/-- Han-Carlson prefix levels `0 .. numLevels - 1` (`g_level` in `qsag_prefix_add`). -/
def hcLevels (N : Nat) : Nat → Nat → (Nat → Bool × Bool) → (Nat → Bool × Bool)
  | 0, _, cur => cur
  | rem + 1, l, cur =>
    let step := 2 * 2 ^ l
    let next := fun i =>
      if i % 2 == 1 && decide (step ≤ i) && decide (i < N) then
        mergeGP (cur i) (cur (i - step))
      else
        cur i
    hcLevels N rem (l + 1) next

/-- Exact RTL model of `qsag_prefix_add` (`qsag_gl64_karatsuba_csa.sv:15-77`). -/
def rtlPrefixAdd (N : Nat) (a b : BitVec N) (cin : Bool) : BitVec N :=
  if h0 : N = 0 then
    h0 ▸ 0#0
  else if h1 : N = 1 then
    h1 ▸ BitVec.ofBool ((a.getLsbD 0 ^^ b.getLsbD 0) ^^ cin)
  else
    let p0 := fun i => a.getLsbD i ^^ b.getLsbD i
    let g0 := fun i => a.getLsbD i && b.getLsbD i
    let nOdd := (N + 1) / 2
    let hl := if nOdd ≤ 1 then 0 else clog2Bounded nOdd nOdd
    let go0 : Nat → Bool × Bool := fun i =>
      if i % 2 == 1 then mergeGP (g0 i, p0 i) (g0 (i - 1), p0 (i - 1))
      else (g0 i, p0 i)
    let goFinal := hcLevels N hl 0 go0
    let endGP : Nat → Bool × Bool := fun i =>
      if i == 0 then (g0 0, p0 0)
      else if i % 2 == 1 then goFinal i
      else mergeGP (g0 i, p0 i) (goFinal (i - 1))
    let sumBit : Nat → Bool := fun i =>
      if i == 0 then p0 0 ^^ cin
      else
        let prev := endGP (i - 1)
        p0 i ^^ (prev.1 || (prev.2 && cin))
    BitVec.ofNatLT (natOfBits N sumBit) (natOfBits_lt N sumBit)

private theorem hcLevels_odd_invariant (N : Nat) (fa fb : Nat → Bool) :
    ∀ (rem l : Nat) (cur : Nat → Bool × Bool),
      (∀ i, i < N → i % 2 = 1 →
        cur i = spanGP fa fb (i + 1 - Nat.min (i + 1) (2 * 2 ^ l)) (Nat.min (i + 1) (2 * 2 ^ l))) →
      ∀ i, i < N → i % 2 = 1 →
        hcLevels N rem l cur i =
          spanGP fa fb (i + 1 - Nat.min (i + 1) (2 * 2 ^ (l + rem)))
            (Nat.min (i + 1) (2 * 2 ^ (l + rem)))
  | 0, l, cur, hInv, i, hiN, hiOdd => by
    rw [Nat.add_zero]
    exact hInv i hiN hiOdd
  | rem + 1, l, cur, hInv, i, hiN, hiOdd => by
    dsimp only [hcLevels]
    have hNextInv : ∀ j, j < N → j % 2 = 1 →
        (if j % 2 == 1 && decide (2 * 2 ^ l ≤ j) && decide (j < N) then
          mergeGP (cur j) (cur (j - 2 * 2 ^ l))
         else cur j) =
        spanGP fa fb (j + 1 - Nat.min (j + 1) (2 * 2 ^ (l + 1)))
          (Nat.min (j + 1) (2 * 2 ^ (l + 1))) := by
      intro j hjN hjOdd
      have hjOddB : (j % 2 == 1) = true := beq_iff_eq.mpr hjOdd
      have hjNB : decide (j < N) = true := decide_eq_true hjN
      generalize hSDef : 2 * 2 ^ l = S
      have hSPos : 2 ≤ S ∧ S % 2 = 0 := by
        rw [← hSDef]
        have := Nat.one_le_two_pow (n := l)
        exact ⟨by omega, by omega⟩
      have hTwoS : 2 * 2 ^ (l + 1) = 2 * S := by
        rw [Nat.pow_succ, ← hSDef]; omega
      rw [hTwoS]
      by_cases hGe : S ≤ j
      · have hCondTrue : (j % 2 == 1 && decide (S ≤ j) && decide (j < N)) = true := by
          rw [hjOddB, decide_eq_true hGe, hjNB]; rfl
        rw [hCondTrue, ite_pos rfl]
        have hSubLt : j - S < N := by omega
        have hSubOdd : (j - S) % 2 = 1 := by omega
        have hInvJ := hInv j hjN hjOdd
        have hInvSub := hInv (j - S) hSubLt hSubOdd
        rw [hSDef] at hInvJ hInvSub
        rw [hInvJ, hInvSub]
        have hMinHi : Nat.min (j + 1) S = S := Nat.min_eq_right (by omega)
        rw [hMinHi]
        by_cases hSubLe : j - S + 1 ≤ S
        · have hk1 : Nat.min (j - S + 1) S = j - S + 1 := Nat.min_eq_left hSubLe
          have hMin2S : Nat.min (j + 1) (2 * S) = j + 1 := Nat.min_eq_left (by omega)
          rw [hk1, hMin2S]
          have hSplit := spanGP_split fa fb 0 (j - S + 1) S
          have h0 : j - S + 1 - (j - S + 1) = 0 := Nat.sub_self _
          have h1 : 0 + (j - S + 1) = j + 1 - S := by omega
          have h2 : (j - S + 1) + S = j + 1 := by omega
          have h3 : j + 1 - (j + 1) = 0 := Nat.sub_self _
          rw [h1, h2] at hSplit
          rw [h0, h3]
          exact hSplit
        · have hk1 : Nat.min (j - S + 1) S = S := Nat.min_eq_right (by omega)
          have hMin2S : Nat.min (j + 1) (2 * S) = 2 * S := Nat.min_eq_right (by omega)
          rw [hk1, hMin2S]
          have hSplit := spanGP_split fa fb (j - S + 1 - S) S S
          have h1 : (j - S + 1 - S) + S = j + 1 - S := by omega
          have h2 : S + S = 2 * S := by omega
          have h3 : j - S + 1 - S = j + 1 - 2 * S := by omega
          rw [h1, h2, h3] at hSplit
          rw [h3]
          exact hSplit
      · have hCondFalse : (j % 2 == 1 && decide (S ≤ j) && decide (j < N)) = false := by
          rw [decide_eq_false hGe, Bool.and_false, Bool.false_and]
        rw [hCondFalse, ite_neg Bool.false_ne_true]
        have hInvJ := hInv j hjN hjOdd
        rw [hSDef] at hInvJ
        rw [hInvJ]
        have hj1LeS : j + 1 ≤ S := by omega
        have hMin1 : Nat.min (j + 1) S = j + 1 := Nat.min_eq_left hj1LeS
        have hMin2 : Nat.min (j + 1) (2 * S) = j + 1 := Nat.min_eq_left (by omega)
        rw [hMin1, hMin2]
    have hRes := hcLevels_odd_invariant N fa fb rem (l + 1) _ hNextInv i hiN hiOdd
    have hExp : l + 1 + rem = l + (rem + 1) := by omega
    rw [hExp] at hRes
    exact hRes

/-- **Arbitrary-Width Han-Carlson Parallel-Prefix Adder Soundness (`rtlPrefixAdd_toNat`)**:
    For every width `N`, `(rtlPrefixAdd N a b cin).toNat = (a.toNat + b.toNat + cin.toNat) % 2^N`! -/
theorem rtlPrefixAdd_toNat (N : Nat) (a b : BitVec N) (cin : Bool) :
    (rtlPrefixAdd N a b cin).toNat = (a.toNat + b.toNat + cin.toNat) % 2 ^ N := by
  unfold rtlPrefixAdd
  by_cases h0 : N = 0
  · subst h0
    rw [dite_pos rfl]
    have ha0 : a.toNat = 0 := by have := a.isLt; omega
    have hb0 : b.toNat = 0 := by have := b.isLt; omega
    simp [ha0, hb0, Nat.mod_one]
  · rw [dite_neg h0]
    by_cases h1 : N = 1
    · subst h1
      rw [dite_pos rfl]
      have hSum := natOfBits_ripple_sum 1 a.getLsbD b.getLsbD cin
      dsimp only [natOfBits, rippleCarry, Nat.pow_one] at hSum
      have ha1 := bitVec_toNat_eq_natOfBits a
      have hb1 := bitVec_toNat_eq_natOfBits b
      dsimp only [natOfBits] at ha1 hb1
      have hBoolToNat : (BitVec.ofBool ((a.getLsbD 0 ^^ b.getLsbD 0) ^^ cin)).toNat =
          ((a.getLsbD 0 ^^ b.getLsbD 0) ^^ cin).toNat := by
        cases ((a.getLsbD 0 ^^ b.getLsbD 0) ^^ cin) <;> rfl
      rw [hBoolToNat, ha1, hb1]
      omega
    · rw [dite_neg h1]
      let fa := a.getLsbD
      let fb := b.getLsbD
      let nOdd := (N + 1) / 2
      let hl := if nOdd ≤ 1 then 0 else clog2Bounded nOdd nOdd
      have hPowCover : N ≤ 2 * 2 ^ hl := by
        dsimp only [hl, nOdd]
        by_cases hn1 : (N + 1) / 2 ≤ 1
        · rw [ite_pos hn1]; omega
        · rw [ite_neg hn1]
          have hGe := pow_clog2Bounded_ge ((N + 1) / 2) ((N + 1) / 2) (le_two_pow_self _)
          omega
      let go0 : Nat → Bool × Bool := fun i =>
        if i % 2 == 1 then
          mergeGP (fa i && fb i, fa i ^^ fb i) (fa (i - 1) && fb (i - 1), fa (i - 1) ^^ fb (i - 1))
        else (fa i && fb i, fa i ^^ fb i)
      have hGo0Inv : ∀ i, i < N → i % 2 = 1 →
          go0 i = spanGP fa fb (i + 1 - Nat.min (i + 1) (2 * 2 ^ 0))
            (Nat.min (i + 1) (2 * 2 ^ 0)) := by
        intro i _ hiOdd
        have hiOddB : (i % 2 == 1) = true := beq_iff_eq.mpr hiOdd
        have hMin2 : Nat.min (i + 1) 2 = 2 := Nat.min_eq_right (by omega)
        dsimp only [go0, Nat.pow_zero, Nat.mul_one]
        rw [hiOddB, ite_pos rfl, hMin2, show i + 1 - 2 = i - 1 by omega]
        dsimp only [spanGP]
        rw [show i - 1 + 1 = i by omega, Nat.add_zero]
        rcases (fa (i - 1) && fb (i - 1), fa (i - 1) ^^ fb (i - 1)) with ⟨glo, plo⟩
        cases fa i <;> cases fb i <;> cases glo <;> cases plo <;> rfl
      have hOddFinal : ∀ i, i < N → i % 2 = 1 →
          hcLevels N hl 0 go0 i = spanGP fa fb 0 (i + 1) := by
        intro i hiN hiOdd
        have hInv := hcLevels_odd_invariant N fa fb hl 0 go0 hGo0Inv i hiN hiOdd
        rw [Nat.zero_add] at hInv
        have hMin : Nat.min (i + 1) (2 * 2 ^ hl) = i + 1 := Nat.min_eq_left (by omega)
        rw [hMin, Nat.sub_self] at hInv
        exact hInv
      let endGP : Nat → Bool × Bool := fun i =>
        if i == 0 then (fa 0 && fb 0, fa 0 ^^ fb 0)
        else if i % 2 == 1 then hcLevels N hl 0 go0 i
        else mergeGP (fa i && fb i, fa i ^^ fb i) (hcLevels N hl 0 go0 (i - 1))
      have hEndAll : ∀ i, i < N → endGP i = spanGP fa fb 0 (i + 1) := by
        intro i hiN
        dsimp only [endGP]
        by_cases hi0 : i = 0
        · subst hi0
          rw [show (0 == 0) = true from rfl, ite_pos rfl]
          dsimp only [spanGP]
          cases fa 0 <;> cases fb 0 <;> rfl
        · have hi0B : (i == 0) = false := beq_eq_false_iff_ne.mpr hi0
          rw [hi0B, ite_neg Bool.false_ne_true]
          by_cases hiOdd : i % 2 = 1
          · rw [beq_iff_eq.mpr hiOdd, ite_pos rfl, hOddFinal i hiN hiOdd]
          · have hiOddB : (i % 2 == 1) = false := beq_eq_false_iff_ne.mpr hiOdd
            have hPrevOdd : (i - 1) % 2 = 1 := by omega
            rw [hiOddB, ite_neg Bool.false_ne_true]
            rw [hOddFinal (i - 1) (by omega) hPrevOdd]
            have hSucc : i - 1 + 1 = i := by omega
            rw [hSucc]
            dsimp only [spanGP]
            rw [Nat.zero_add]
      change natOfBits N
          (fun i =>
            if i == 0 then (fa 0 ^^ fb 0) ^^ cin
            else (fa i ^^ fb i) ^^ ((endGP (i - 1)).1 || ((endGP (i - 1)).2 && cin))) = _
      have hBitsMatch : natOfBits N
          (fun i =>
            if i == 0 then (fa 0 ^^ fb 0) ^^ cin
            else (fa i ^^ fb i) ^^ ((endGP (i - 1)).1 || ((endGP (i - 1)).2 && cin))) =
          natOfBits N (fun i => (fa i ^^ fb i) ^^ rippleCarry fa fb cin i) := by
        apply natOfBits_congr
        intro i hiN
        by_cases hi0 : i = 0
        · subst hi0; rfl
        · rw [beq_eq_false_iff_ne.mpr hi0, ite_neg Bool.false_ne_true]
          rw [hEndAll (i - 1) (by omega), show i - 1 + 1 = i by omega, spanGP_eval_carry]
      rw [hBitsMatch]
      have hRipple := natOfBits_ripple_sum N fa fb cin
      have hLt : natOfBits N (fun i => (fa i ^^ fb i) ^^ rippleCarry fa fb cin i) < 2 ^ N :=
        natOfBits_lt N _
      rw [← bitVec_toNat_eq_natOfBits, ← bitVec_toNat_eq_natOfBits] at hRipple
      rw [← hRipple, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hLt]

/-- Exact RTL model of `qsag_add_split` (`qsag_add_split.sv:6-74`) for chunked Kogge-Stone
    carry-select addition (`W = 66` and `W = 67` at `CHUNK = 24` in `qsag_gl64_reduce.sv`). -/
def rtlAddSplit3Chunk (W chunk : Nat) (a b : BitVec W) : BitVec W :=
  let b0 := Nat.min W chunk
  let b1 := Nat.min (W - chunk) chunk
  let b2 := W - 2 * chunk
  let a0 := (a.extractLsb' 0 b0).toNat
  let d0 := (b.extractLsb' 0 b0).toNat
  let s0_0 := a0 + d0
  let y0 := s0_0 % 2 ^ b0
  let g0_0 : Bool := decide (2 ^ b0 ≤ s0_0)
  let p0_0 : Bool := false
  let a1 := (a.extractLsb' chunk b1).toNat
  let d1 := (b.extractLsb' chunk b1).toNat
  let c0_1 := a1 + d1
  let c1_1 := a1 + d1 + 1
  let g0_1 : Bool := decide (2 ^ b1 ≤ c0_1)
  let p0_1 : Bool := decide (2 ^ b1 ≤ c1_1)
  let cin1 : Bool := g0_0
  let y1 := if cin1 then c1_1 % 2 ^ b1 else c0_1 % 2 ^ b1
  let g1_1 : Bool := g0_1 || (p0_1 && (g0_0 || (p0_0 && false)))
  let cin2 : Bool := g1_1
  let a2 := (a.extractLsb' (2 * chunk) b2).toNat
  let d2 := (b.extractLsb' (2 * chunk) b2).toNat
  let c0_2 := a2 + d2
  let c1_2 := a2 + d2 + 1
  let y2 := if cin2 then c1_2 % 2 ^ b2 else c0_2 % 2 ^ b2
  BitVec.ofNat W (y0 + 2 ^ chunk * y1 + 2 ^ (2 * chunk) * y2)

private theorem bitVec_split3_toNat {W : Nat} (chunk : Nat)
    (hW : 2 * chunk ≤ W) (v : BitVec W) :
    v.toNat =
      (v.extractLsb' 0 chunk).toNat +
      2 ^ chunk * (v.extractLsb' chunk chunk).toNat +
      2 ^ (2 * chunk) * (v.extractLsb' (2 * chunk) (W - 2 * chunk)).toNat := by
  let x := v.toNat
  have hxLt : x < 2 ^ W := v.isLt
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one]
  have hMod0 := Nat.mod_add_div x (2 ^ chunk)
  have hMod1 := Nat.mod_add_div (x / 2 ^ chunk) (2 ^ chunk)
  have hDivDiv : (x / 2 ^ chunk) / 2 ^ chunk = x / 2 ^ (2 * chunk) := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, show chunk + chunk = 2 * chunk by omega]
  have hTopLt : x / 2 ^ (2 * chunk) < 2 ^ (W - 2 * chunk) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    have hp2 : 2 ^ (W - 2 * chunk) * 2 ^ (2 * chunk) = 2 ^ W := by
      rw [← Nat.pow_add, show W - 2 * chunk + 2 * chunk = W by omega]
    rw [hp2]; exact hxLt
  rw [Nat.mod_eq_of_lt hTopLt]
  rw [hDivDiv] at hMod1
  calc
    x = x % 2 ^ chunk + 2 ^ chunk * (x / 2 ^ chunk) := hMod0.symm
    _ = x % 2 ^ chunk + 2 ^ chunk *
          ((x / 2 ^ chunk) % 2 ^ chunk + 2 ^ chunk * (x / 2 ^ (2 * chunk))) := by
        rw [hMod1]
    _ = x % 2 ^ chunk + 2 ^ chunk * ((x / 2 ^ chunk) % 2 ^ chunk) +
          (2 ^ chunk * 2 ^ chunk) * (x / 2 ^ (2 * chunk)) := by
        rw [Nat.left_distrib, ← Nat.add_assoc, Nat.mul_assoc]
    _ = x % 2 ^ chunk + 2 ^ chunk * ((x / 2 ^ chunk) % 2 ^ chunk) +
          2 ^ (2 * chunk) * (x / 2 ^ (2 * chunk)) := by
        rw [← Nat.pow_add, show chunk + chunk = 2 * chunk by omega]

/-- **3-Chunk Kogge-Stone Carry-Select Soundness (`rtlAddSplit3Chunk_toNat`)**:
    Covers both `qsag_add_split #(.W(66), .CHUNK(24))` and `qsag_add_split #(.W(67), .CHUNK(24))`
    in `qsag_gl64_reduce.sv`! -/
theorem rtlAddSplit3Chunk_toNat {W chunk : Nat} (hW : 2 * chunk < W) (a b : BitVec W) :
    (rtlAddSplit3Chunk W chunk a b).toNat = (a.toNat + b.toNat) % 2 ^ W := by
  unfold rtlAddSplit3Chunk
  dsimp only
  have hMin0 : Nat.min W chunk = chunk := Nat.min_eq_right (by omega)
  have hMin1 : Nat.min (W - chunk) chunk = chunk := Nat.min_eq_right (by omega)
  rw [BitVec.toNat_ofNat, hMin0, hMin1, Bool.false_and, Bool.or_false]
  repeat rw [BitVec.extractLsb'_toNat]
  have haSplit := bitVec_split3_toNat chunk (by omega) a
  have hbSplit := bitVec_split3_toNat chunk (by omega) b
  simp only [BitVec.extractLsb'_toNat] at haSplit hbSplit
  generalize ha0Def : (a.toNat >>> 0) % 2 ^ chunk = a0 at haSplit ⊢
  generalize hd0Def : (b.toNat >>> 0) % 2 ^ chunk = d0 at hbSplit ⊢
  generalize ha1Def : (a.toNat >>> chunk) % 2 ^ chunk = a1 at haSplit ⊢
  generalize hd1Def : (b.toNat >>> chunk) % 2 ^ chunk = d1 at hbSplit ⊢
  generalize ha2Def : (a.toNat >>> (2 * chunk)) % 2 ^ (W - 2 * chunk) = a2 at haSplit ⊢
  generalize hd2Def : (b.toNat >>> (2 * chunk)) % 2 ^ (W - 2 * chunk) = d2 at hbSplit ⊢
  have hPosC : 0 < 2 ^ chunk := Nat.two_pow_pos _
  have hPosTop : 0 < 2 ^ (W - 2 * chunk) := Nat.two_pow_pos _
  have ha0Lt : a0 < 2 ^ chunk := by rw [← ha0Def]; exact Nat.mod_lt _ hPosC
  have hd0Lt : d0 < 2 ^ chunk := by rw [← hd0Def]; exact Nat.mod_lt _ hPosC
  have ha1Lt : a1 < 2 ^ chunk := by rw [← ha1Def]; exact Nat.mod_lt _ hPosC
  have hd1Lt : d1 < 2 ^ chunk := by rw [← hd1Def]; exact Nat.mod_lt _ hPosC
  have ha2Lt : a2 < 2 ^ (W - 2 * chunk) := by rw [← ha2Def]; exact Nat.mod_lt _ hPosTop
  have hd2Lt : d2 < 2 ^ (W - 2 * chunk) := by rw [← hd2Def]; exact Nat.mod_lt _ hPosTop
  let cin1 := if 2 ^ chunk ≤ a0 + d0 then 1 else 0
  have hChunk0 : a0 + d0 = (a0 + d0) % 2 ^ chunk + 2 ^ chunk * cin1 := by
    dsimp only [cin1]
    by_cases hGe : 2 ^ chunk ≤ a0 + d0
    · rw [ite_pos hGe]
      have hSubLt : a0 + d0 - 2 ^ chunk < 2 ^ chunk := by omega
      rw [Nat.mod_eq_sub_mod hGe, Nat.mod_eq_of_lt hSubLt]; omega
    · rw [ite_neg hGe]
      rw [Nat.mod_eq_of_lt (by omega)]; omega
  generalize hy1Def : (if decide (2 ^ chunk ≤ a0 + d0) then (a1 + d1 + 1) % 2 ^ chunk else (a1 + d1) % 2 ^ chunk) = y1
  let cin2B : Bool := decide (2 ^ chunk ≤ a1 + d1) ||
    (decide (2 ^ chunk ≤ a1 + d1 + 1) && decide (2 ^ chunk ≤ a0 + d0))
  let cin2 := if cin2B then 1 else 0
  have hChunk1 : a1 + d1 + cin1 = y1 + 2 ^ chunk * cin2 := by
    rw [← hy1Def]
    dsimp only [cin1, cin2]
    by_cases hC0 : 2 ^ chunk ≤ a0 + d0
    · have hB0 : decide (2 ^ chunk ≤ a0 + d0) = true := decide_eq_true hC0
      rw [ite_pos hC0, hB0, ite_pos rfl]
      by_cases hC1 : 2 ^ chunk ≤ a1 + d1 + 1
      · have hCin2T : cin2B = true := by
          dsimp only [cin2B]; rw [hB0, decide_eq_true hC1, Bool.and_true, Bool.or_true]
        rw [hCin2T, ite_pos rfl]
        have hSubLt : a1 + d1 + 1 - 2 ^ chunk < 2 ^ chunk := by omega
        rw [Nat.mod_eq_sub_mod hC1, Nat.mod_eq_of_lt hSubLt]; omega
      · have hNot0 : ¬ (2 ^ chunk ≤ a1 + d1) := by omega
        have hCin2F : cin2B = false := by
          dsimp only [cin2B]; rw [decide_eq_false hC1, decide_eq_false hNot0]; rfl
        rw [hCin2F, ite_neg Bool.false_ne_true]
        rw [Nat.mod_eq_of_lt (by omega)]; omega
    · have hB0 : decide (2 ^ chunk ≤ a0 + d0) = false := decide_eq_false hC0
      rw [ite_neg hC0, hB0, ite_neg Bool.false_ne_true]
      by_cases hC1 : 2 ^ chunk ≤ a1 + d1
      · have hCin2T : cin2B = true := by
          dsimp only [cin2B]; rw [decide_eq_true hC1, Bool.true_or]
        rw [hCin2T, ite_pos rfl]
        have hSubLt : a1 + d1 - 2 ^ chunk < 2 ^ chunk := by omega
        rw [Nat.mod_eq_sub_mod hC1, Nat.mod_eq_of_lt hSubLt]; omega
      · have hCin2F : cin2B = false := by
          dsimp only [cin2B]; rw [hB0, decide_eq_false hC1, Bool.and_false, Bool.or_self]
        rw [hCin2F, ite_neg Bool.false_ne_true]
        rw [Nat.mod_eq_of_lt (by omega)]; omega
  generalize hy2Def : (if cin2B then (a2 + d2 + 1) % 2 ^ (W - 2 * chunk) else (a2 + d2) % 2 ^ (W - 2 * chunk)) = y2
  let cout := if cin2B then (a2 + d2 + 1) / 2 ^ (W - 2 * chunk) else (a2 + d2) / 2 ^ (W - 2 * chunk)
  have hChunk2 : a2 + d2 + cin2 = y2 + 2 ^ (W - 2 * chunk) * cout := by
    rw [← hy2Def]
    dsimp only [cout, cin2]
    cases cin2B
    · rw [ite_neg Bool.false_ne_true, ite_neg Bool.false_ne_true, ite_neg Bool.false_ne_true]
      exact (Nat.mod_add_div (a2 + d2) (2 ^ (W - 2 * chunk))).symm
    · rw [ite_pos rfl, ite_pos rfl, ite_pos rfl]
      exact (Nat.mod_add_div (a2 + d2 + 1) (2 ^ (W - 2 * chunk))).symm
  have hPow2 : 2 ^ chunk * 2 ^ chunk = 2 ^ (2 * chunk) := by
    rw [← Nat.pow_add, show chunk + chunk = 2 * chunk by omega]
  have hPowW : 2 ^ (2 * chunk) * 2 ^ (W - 2 * chunk) = 2 ^ W := by
    rw [← Nat.pow_add, show 2 * chunk + (W - 2 * chunk) = W by omega]
  have hTotal : a.toNat + b.toNat =
      ((a0 + d0) % 2 ^ chunk + 2 ^ chunk * y1 + 2 ^ (2 * chunk) * y2) + 2 ^ W * cout := by
    calc
      a.toNat + b.toNat
        = (a0 + d0) + (2 ^ chunk * a1 + 2 ^ chunk * d1) +
            (2 ^ (2 * chunk) * a2 + 2 ^ (2 * chunk) * d2) := by
          rw [haSplit, hbSplit]; omega
      _ = (a0 + d0) + 2 ^ chunk * (a1 + d1) + 2 ^ (2 * chunk) * (a2 + d2) := by
          rw [← Nat.left_distrib, ← Nat.left_distrib]
      _ = ((a0 + d0) % 2 ^ chunk + 2 ^ chunk * cin1) + 2 ^ chunk * (a1 + d1) +
            2 ^ (2 * chunk) * (a2 + d2) := by
          exact congrArg (fun z => z + 2 ^ chunk * (a1 + d1) + 2 ^ (2 * chunk) * (a2 + d2)) hChunk0
      _ = (a0 + d0) % 2 ^ chunk + 2 ^ chunk * (a1 + d1 + cin1) + 2 ^ (2 * chunk) * (a2 + d2) := by
          rw [Nat.left_distrib (2 ^ chunk) (a1 + d1) cin1, Nat.left_distrib (2 ^ chunk) a1 d1]
          omega
      _ = (a0 + d0) % 2 ^ chunk + (2 ^ chunk * y1 + 2 ^ (2 * chunk) * cin2) +
            2 ^ (2 * chunk) * (a2 + d2) := by
          rw [hChunk1, Nat.left_distrib, ← Nat.mul_assoc, hPow2]
      _ = ((a0 + d0) % 2 ^ chunk + 2 ^ chunk * y1) + 2 ^ (2 * chunk) * (a2 + d2 + cin2) := by
          rw [Nat.left_distrib (2 ^ (2 * chunk)) (a2 + d2) cin2,
              Nat.left_distrib (2 ^ (2 * chunk)) a2 d2]
          omega
      _ = ((a0 + d0) % 2 ^ chunk + 2 ^ chunk * y1 + 2 ^ (2 * chunk) * y2) + 2 ^ W * cout := by
          rw [hChunk2, Nat.left_distrib, ← Nat.mul_assoc, hPowW, ← Nat.add_assoc]
  rw [hTotal, Nat.mul_comm (2 ^ W) cout, Nat.add_mul_mod_self_right]

-- Seal verified bit-level compressor and parallel-prefix adder primitives against WHNF tree blowup:
attribute [local irreducible] rtlCsa32 rtlCsa52 rtlCsaReduce2 rtlPrefixAdd rtlAddSplit3Chunk

/-! ## 4. FPGA 136-Bit Solinas Goldilocks Reducer (`hardware/fpga/rtl/qsag_gl64_reduce.sv`) -/

/-- Stage-1 6-term Solinas CSA + split-adder datapath of `qsag_gl64_reduce.sv:23-38`. -/
def rtlFpgaGl64Stage1 (cBias : BitVec 66) (x : BitVec 136) : BitVec 66 :=
  let lo := x.extractLsb' 0 64
  let m  := x.extractLsb' 64 32
  let h  := x.extractLsb' 96 32
  let t  := x.extractLsb' 128 8
  let t0 : BitVec 66 := BitVec.ofNat 66 lo.toNat
  let t1 : BitVec 66 := BitVec.ofNat 66 (m.toNat * 2 ^ 32)
  let t2 : BitVec 66 := ~~~(BitVec.ofNat 66 m.toNat)
  let t3 : BitVec 66 := ~~~(BitVec.ofNat 66 h.toNat)
  let t4 : BitVec 66 := ~~~(BitVec.ofNat 66 (t.toNat * 2 ^ 32))
  let t5 : BitVec 66 := cBias
  let sc := rtlCsaReduce2 66 [t0, t1, t2, t3, t4, t5]
  rtlAddSplit3Chunk 66 24 sc.1 sc.2

private def rtlFpgaGl64Mux (v_q : BitVec 66) (v1 v2 : BitVec 67) : BitVec 64 :=
  if !(v2.getLsbD 66) then v2.extractLsb' 0 64
  else if !(v1.getLsbD 66) then v1.extractLsb' 0 64
  else v_q.extractLsb' 0 64

/-- Stage-2 parallel `NEG_1P` / `NEG_2P` canonicalizer of `qsag_gl64_reduce.sv:47-63`. -/
def rtlFpgaGl64Stage2 (v_q : BitVec 66) : BitVec 64 :=
  let neg1P : BitVec 67 := BitVec.ofNat 67 (2 ^ 67 - goldilocksPrime)
  let neg2P : BitVec 67 := BitVec.ofNat 67 (2 ^ 67 - 2 * goldilocksPrime)
  let vExt  : BitVec 67 := BitVec.ofNat 67 v_q.toNat
  let v1 := rtlAddSplit3Chunk 67 24 vExt neg1P
  let v2 := rtlAddSplit3Chunk 67 24 vExt neg2P
  rtlFpgaGl64Mux v_q v1 v2

/-- Combinational (`REG_OUT = 0`, 1-stage `v_q <= v_d`) output of `qsag_gl64_reduce`. -/
def rtlFpgaGl64Reduce (x : BitVec 136) : BitVec 64 :=
  rtlFpgaGl64Stage2 (rtlFpgaGl64Stage1 (BitVec.ofNat 66 (goldilocksPrime + 3)) x)

/-- Registered pipeline state (`REG_OUT = 1`, 2 clocks: `v_q` and `r`) of `qsag_gl64_reduce.sv`. -/
structure FpgaGl64PipeState where
  v_q : BitVec 66
  r_q : BitVec 64

def rtlFpgaGl64Step (st : FpgaGl64PipeState) (x_in : BitVec 136) : FpgaGl64PipeState where
  v_q := rtlFpgaGl64Stage1 (BitVec.ofNat 66 (goldilocksPrime + 3)) x_in
  r_q := rtlFpgaGl64Stage2 st.v_q

private theorem bitVec136_slice_decomp (x : BitVec 136) :
    x.toNat =
      (x.extractLsb' 0 64).toNat +
      2 ^ 64 * (x.extractLsb' 64 32).toNat +
      2 ^ 96 * (x.extractLsb' 96 32).toNat +
      2 ^ 128 * (x.extractLsb' 128 8).toNat := by
  have hxLt : x.toNat < 2 ^ 136 := x.isLt
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one]
  have hTopLt : x.toNat / 2 ^ 128 < 2 ^ 8 := by
    rw [Nat.div_lt_iff_lt_mul (by decide)]
    exact Nat.lt_of_lt_of_eq hxLt (by decide)
  rw [Nat.mod_eq_of_lt hTopLt]
  generalize hq0 : x.toNat / 2 ^ 64 = q0
  generalize hr0 : x.toNat % 2 ^ 64 = r0
  generalize hq1 : q0 / 2 ^ 32 = q1
  generalize hr1 : q0 % 2 ^ 32 = r1
  generalize hq2 : q1 / 2 ^ 32 = q2
  generalize hr2 : q1 % 2 ^ 32 = r2
  have d0 : r0 + 18446744073709551616 * q0 = x.toNat := by
    rw [← hr0, ← hq0]; exact Nat.mod_add_div x.toNat (2 ^ 64)
  have d1 : r1 + 4294967296 * q1 = q0 := by
    rw [← hr1, ← hq1]; exact Nat.mod_add_div q0 (2 ^ 32)
  have d2 : r2 + 4294967296 * q2 = q1 := by
    rw [← hr2, ← hq2]; exact Nat.mod_add_div q1 (2 ^ 32)
  have h96Eq : x.toNat / 2 ^ 96 = q1 := by
    rw [← hq1, ← hq0, Nat.div_div_eq_div_mul]
  have h128Eq : x.toNat / 2 ^ 128 = q2 := by
    rw [← hq2, ← h96Eq, Nat.div_div_eq_div_mul]
  rw [h96Eq, hr2, h128Eq]
  change x.toNat = r0 + 18446744073709551616 * r1 +
      79228162514264337593543950336 * r2 +
      340282366920938463463374607431768211456 * q2
  omega

private theorem nat_eq_of_int_eq {a b : Nat} (h : (a : Int) = (b : Int)) : a = b :=
  Int.ofNat_inj.mp h

private theorem nat_lt_of_int_lt {a b : Nat} (h : (a : Int) < (b : Int)) : a < b := by
  omega

private theorem int_natCast_sub {a b : Nat} (h : b ≤ a) :
    ((a - b : Nat) : Int) = (a : Int) - (b : Int) := by
  omega

private theorem eq_of_two_mul_eq {b s : Nat} (h : 2 * b = 0 + 2 * s) : s = b := by
  omega

private theorem sq_split32_expand (x0 x1 : Nat) :
    (x0 + 4294967296 * x1) * (x0 + 4294967296 * x1) =
      x0 * x0 + 4294967296 * (2 * (x0 * x1)) + 18446744073709551616 * (x1 * x1) := by
  have h1 : x0 * (4294967296 * x1) = 4294967296 * (x0 * x1) := by
    rw [← Nat.mul_assoc, Nat.mul_comm x0 4294967296, Nat.mul_assoc]
  have h2 : (4294967296 * x1) * x0 = 4294967296 * (x0 * x1) := by
    rw [Nat.mul_assoc, Nat.mul_comm x1 x0]
  have h3 : (4294967296 * x1) * (4294967296 * x1) = 18446744073709551616 * (x1 * x1) := by
    rw [Nat.mul_assoc, ← Nat.mul_assoc x1 4294967296 x1, Nat.mul_comm x1 4294967296,
        Nat.mul_assoc 4294967296 x1 x1, ← Nat.mul_assoc]
  rw [Nat.left_distrib, Nat.right_distrib, Nat.right_distrib, h1, h2, h3]
  generalize x0 * x0 = A
  generalize x0 * x1 = B
  generalize x1 * x1 = C
  omega

private theorem karatsuba_split32_identity (a0 a1 b0 b1 : Nat) :
    (a0 + 4294967296 * a1) * (b0 + 4294967296 * b1) + 4294967296 * (a0 * b0 + a1 * b1) =
      a0 * b0 + 4294967296 * ((a0 + a1) * (b0 + b1)) + 18446744073709551616 * (a1 * b1) := by
  have hMid : (a0 + a1) * (b0 + b1) = a0 * b0 + a0 * b1 + a1 * b0 + a1 * b1 := by
    rw [Nat.right_distrib, Nat.left_distrib, Nat.left_distrib, ← Nat.add_assoc]
  have hProd : (a0 + 4294967296 * a1) * (b0 + 4294967296 * b1) =
      a0 * b0 + 4294967296 * (a0 * b1 + a1 * b0) + 18446744073709551616 * (a1 * b1) := by
    rw [Nat.right_distrib, Nat.left_distrib, Nat.left_distrib]
    have e1 : a0 * (4294967296 * b1) = 4294967296 * (a0 * b1) := by
      rw [← Nat.mul_assoc, Nat.mul_comm a0 4294967296, Nat.mul_assoc]
    have e2 : (4294967296 * a1) * b0 = 4294967296 * (a1 * b0) := Nat.mul_assoc _ _ _
    have e3 : (4294967296 * a1) * (4294967296 * b1) = 18446744073709551616 * (a1 * b1) := by
      rw [Nat.mul_assoc, ← Nat.mul_assoc a1 4294967296 b1, Nat.mul_comm a1 4294967296,
          Nat.mul_assoc 4294967296 a1 b1, ← Nat.mul_assoc]
    rw [e1, e2, e3, Nat.left_distrib]
    generalize a0 * b0 = p00; generalize a0 * b1 = p01
    generalize a1 * b0 = p10; generalize a1 * b1 = p11
    omega
  rw [hProd, hMid]
  generalize a0 * b0 = p00; generalize a0 * b1 = p01
  generalize a1 * b0 = p10; generalize a1 * b1 = p11
  omega

/-- **FPGA 136-Bit Solinas Goldilocks Soundness (`rtlFpgaGl64Reduce_sound`)**:
    For **all** `2^136` inputs `x : BitVec 136`, `rtlFpgaGl64Reduce x` equals the canonical
    Goldilocks residue `(Goldilocks.ofNat x.toNat).val` (`< p`)! -/
theorem rtlFpgaGl64Reduce_sound (x : BitVec 136) :
    (rtlFpgaGl64Reduce x).toNat = (Goldilocks.ofNat x.toNat).val := by
  unfold rtlFpgaGl64Reduce
  have hDecomp := bitVec136_slice_decomp x
  let lo := (x.extractLsb' 0 64).toNat
  let m  := (x.extractLsb' 64 32).toNat
  let h  := (x.extractLsb' 96 32).toNat
  let t  := (x.extractLsb' 128 8).toNat
  have hLo : lo < 18446744073709551616 := (x.extractLsb' 0 64).isLt
  have hM  : m < 4294967296  := (x.extractLsb' 64 32).isLt
  have hH  : h < 4294967296  := (x.extractLsb' 96 32).isLt
  have hT  : t < 256         := (x.extractLsb' 128 8).isLt
  have hDecompLit : x.toNat = lo + 18446744073709551616 * m +
      79228162514264337593543950336 * h +
      340282366920938463463374607431768211456 * t := hDecomp
  let v := (lo + 4294967296 * m + goldilocksPrime) - (m + h + 4294967296 * t)
  have hvLe : m + h + 4294967296 * t ≤ lo + 4294967296 * m + goldilocksPrime := by
    clear hDecomp hDecompLit; unfold goldilocksPrime; omega
  have hvCast : (v : Int) =
      (lo : Int) + 4294967296 * (m : Int) + (goldilocksPrime : Int) -
      ((m : Int) + (h : Int) + 4294967296 * (t : Int)) := by
    dsimp only [v]
    rw [int_natCast_sub hvLe]
    simp only [Int.natCast_add, Int.natCast_mul]
    clear hDecomp hDecompLit hvLe; omega
  have hvBounds : 0 < v ∧ v < 3 * goldilocksPrime ∧ 3 * goldilocksPrime < 73786976294838206464 := by
    refine ⟨?_, ?_, by decide⟩
    · apply nat_lt_of_int_lt
      rw [hvCast]; clear hDecomp hDecompLit hvLe; unfold goldilocksPrime; omega
    · apply nat_lt_of_int_lt
      rw [hvCast, Int.natCast_mul]; clear hDecomp hDecompLit hvLe; unfold goldilocksPrime; omega
  have hStage1 : (rtlFpgaGl64Stage1 (BitVec.ofNat 66 (goldilocksPrime + 3)) x).toNat = v := by
    unfold rtlFpgaGl64Stage1
    dsimp only
    rw [rtlAddSplit3Chunk_toNat (by decide), rtlCsaReduce2_mod]
    dsimp only [List.map]
    rw [List.sum_cons, List.sum_cons, List.sum_cons, List.sum_cons, List.sum_cons, List.sum_cons,
        List.sum_nil]
    have ht0 : (BitVec.ofNat 66 lo).toNat = lo := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by clear hDecomp hDecompLit hvCast; change lo < 73786976294838206464; omega)
    have ht1 : (BitVec.ofNat 66 (m * 2 ^ 32)).toNat = m * 4294967296 := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by clear hDecomp hDecompLit hvCast; change m * 4294967296 < 73786976294838206464; omega)
    have ht2 : (~~~(BitVec.ofNat 66 m)).toNat = 73786976294838206463 - m := by
      rw [bitVec_not_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by clear hDecomp hDecompLit hvCast; change m < 73786976294838206464; omega)]
    have ht3 : (~~~(BitVec.ofNat 66 h)).toNat = 73786976294838206463 - h := by
      rw [bitVec_not_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by clear hDecomp hDecompLit hvCast; change h < 73786976294838206464; omega)]
    have ht4 : (~~~(BitVec.ofNat 66 (t * 2 ^ 32))).toNat = 73786976294838206463 - t * 4294967296 := by
      rw [bitVec_not_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by clear hDecomp hDecompLit hvCast; change t * 4294967296 < 73786976294838206464; omega)]
    have ht5 : (BitVec.ofNat 66 (goldilocksPrime + 3)).toNat = goldilocksPrime + 3 := by decide
    have hL0 : ((x.extractLsb' 0 64).toNat) = lo := rfl
    have hM0 : ((x.extractLsb' 64 32).toNat) = m := rfl
    have hH0 : ((x.extractLsb' 96 32).toNat) = h := rfl
    have hT0 : ((x.extractLsb' 128 8).toNat) = t := rfl
    rw [hL0, hM0, hH0, hT0, ht0, ht1, ht2, ht3, ht4, ht5]
    have hP66 : 2 ^ 66 = 73786976294838206464 := by decide
    have hSum3 : lo + (m * 4294967296 + (73786976294838206463 - m +
        (73786976294838206463 - h + (73786976294838206463 - t * 4294967296 + (goldilocksPrime + 3 + 0))))) =
        v + 2 ^ 66 * 3 := by
      rw [hP66]
      apply nat_eq_of_int_eq
      have hmSub : m ≤ 73786976294838206463 := by clear hDecomp hDecompLit hvCast; omega
      have hhSub : h ≤ 73786976294838206463 := by clear hDecomp hDecompLit hvCast; omega
      have htSub : t * 4294967296 ≤ 73786976294838206463 := by clear hDecomp hDecompLit hvCast; omega
      simp only [Int.natCast_add, Int.natCast_mul,
        int_natCast_sub hmSub, int_natCast_sub hhSub, int_natCast_sub htSub, hvCast]
      clear hDecomp hDecompLit hvLe hvBounds ht0 ht1 ht2 ht3 ht4 ht5 hmSub hhSub htSub
      unfold goldilocksPrime
      omega
    have hvLt66 : v < 2 ^ 66 := by rw [hP66]; exact Nat.lt_trans hvBounds.2.1 hvBounds.2.2
    rw [hSum3, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hvLt66]
  have hModEq : x.toNat % goldilocksPrime = v % goldilocksPrime := by
    have hLin : x.toNat + goldilocksPrime * 1 =
        v + goldilocksPrime * (m + 4294967297 * h + 18446744078004518912 * t) := by
      rw [hDecompLit]
      apply nat_eq_of_int_eq
      simp only [Int.natCast_add, Int.natCast_mul, hvCast]
      clear hDecomp hDecompLit hvLe hvBounds hStage1
      unfold goldilocksPrime
      omega
    rw [← Nat.add_mul_mod_self_left x.toNat goldilocksPrime 1, hLin, Nat.add_mul_mod_self_left]
  have hMuxSound : ∀ (vq : BitVec 66) (v1 v2 : BitVec 67),
      vq.toNat < 3 * goldilocksPrime →
      v1.toNat = (vq.toNat + (2 ^ 67 - goldilocksPrime)) % 2 ^ 67 →
      v2.toNat = (vq.toNat + (2 ^ 67 - 2 * goldilocksPrime)) % 2 ^ 67 →
      (rtlFpgaGl64Mux vq v1 v2).toNat = vq.toNat % goldilocksPrime := by
    intro vq v1 v2 hvqLt3P hv1Val hv2Val
    have hBit66Iff : ∀ w67 : BitVec 67, w67.getLsbD 66 = decide (2 ^ 66 ≤ w67.toNat) := by
      intro w67
      have hwLt : w67.toNat < 147573952589676412928 := w67.isLt
      rw [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
      change decide (w67.toNat / 73786976294838206464 % 2 = 1) =
        decide (73786976294838206464 ≤ w67.toNat)
      by_cases hGe : 73786976294838206464 ≤ w67.toNat
      · have hDiv1 : w67.toNat / 73786976294838206464 = 1 := by omega
        rw [decide_eq_true hGe, hDiv1]; rfl
      · have hDiv0 : w67.toNat / 73786976294838206464 = 0 := by omega
        rw [decide_eq_false hGe, hDiv0]; rfl
    unfold rtlFpgaGl64Mux
    rw [hBit66Iff v2, hBit66Iff v1]
    have hP66 : 2 ^ 66 = 73786976294838206464 := by decide
    have hP67 : 2 ^ 67 = 147573952589676412928 := by decide
    have hPLt64 : goldilocksPrime < 2 ^ 64 := by decide
    by_cases hGe2 : 2 * goldilocksPrime ≤ vq.toNat
    · have hResLtP : vq.toNat - 2 * goldilocksPrime < goldilocksPrime := by omega
      have hResLt67 : vq.toNat - 2 * goldilocksPrime < 2 ^ 67 :=
        Nat.lt_trans hResLtP (by decide)
      have hv2Small : v2.toNat = vq.toNat - 2 * goldilocksPrime := by
        rw [hv2Val]
        have hW2 : vq.toNat + (2 ^ 67 - 2 * goldilocksPrime) =
            (vq.toNat - 2 * goldilocksPrime) + 2 ^ 67 * 1 := by
          rw [hP67]; unfold goldilocksPrime at *; omega
        rw [hW2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hResLt67]
      have hNotGe66 : ¬ (2 ^ 66 ≤ v2.toNat) := by
        rw [hv2Small, hP66]; unfold goldilocksPrime at *; omega
      rw [decide_eq_false hNotGe66, Bool.not_false, ite_pos rfl,
          BitVec.extractLsb'_toNat, Nat.shiftRight_zero, hv2Small,
          Nat.mod_eq_of_lt (Nat.lt_trans hResLtP hPLt64)]
      have hDecompV : vq.toNat = (vq.toNat - 2 * goldilocksPrime) + goldilocksPrime * 2 := by omega
      exact ((congrArg (· % goldilocksPrime) hDecompV).trans
        ((Nat.add_mul_mod_self_left _ _ _).trans (Nat.mod_eq_of_lt hResLtP))).symm
    · have hv2SumLt67 : vq.toNat + (2 ^ 67 - 2 * goldilocksPrime) < 2 ^ 67 := by
        rw [hP67]; unfold goldilocksPrime at *; omega
      have hv2Big : 2 ^ 66 ≤ v2.toNat := by
        rw [hv2Val, Nat.mod_eq_of_lt hv2SumLt67, hP66, hP67]
        unfold goldilocksPrime at *; omega
      rw [decide_eq_true hv2Big, Bool.not_true, ite_neg Bool.false_ne_true]
      by_cases hGe1 : goldilocksPrime ≤ vq.toNat
      · have hResLtP : vq.toNat - goldilocksPrime < goldilocksPrime := by omega
        have hResLt67 : vq.toNat - goldilocksPrime < 2 ^ 67 := Nat.lt_trans hResLtP (by decide)
        have hv1Small : v1.toNat = vq.toNat - goldilocksPrime := by
          rw [hv1Val]
          have hW1 : vq.toNat + (2 ^ 67 - goldilocksPrime) =
              (vq.toNat - goldilocksPrime) + 2 ^ 67 * 1 := by
            rw [hP67]; unfold goldilocksPrime at *; omega
          rw [hW1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hResLt67]
        have hNotGe66 : ¬ (2 ^ 66 ≤ v1.toNat) := by
          rw [hv1Small, hP66]; unfold goldilocksPrime at *; omega
        rw [decide_eq_false hNotGe66, Bool.not_false, ite_pos rfl,
            BitVec.extractLsb'_toNat, Nat.shiftRight_zero, hv1Small,
            Nat.mod_eq_of_lt (Nat.lt_trans hResLtP hPLt64)]
        rw [Nat.mod_eq_sub_mod hGe1, Nat.mod_eq_of_lt hResLtP]
      · have hvLtP : vq.toNat < goldilocksPrime := by omega
        have hv1SumLt67 : vq.toNat + (2 ^ 67 - goldilocksPrime) < 2 ^ 67 := by
          rw [hP67]; unfold goldilocksPrime at *; omega
        have hv1Big : 2 ^ 66 ≤ v1.toNat := by
          rw [hv1Val, Nat.mod_eq_of_lt hv1SumLt67, hP66, hP67]
          unfold goldilocksPrime at *; omega
        rw [decide_eq_true hv1Big, Bool.not_true, ite_neg Bool.false_ne_true,
            BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
            Nat.mod_eq_of_lt (Nat.lt_trans hvLtP hPLt64), Nat.mod_eq_of_lt hvLtP]
  have hStage2 : ∀ vq : BitVec 66, vq.toNat < 3 * goldilocksPrime →
      (rtlFpgaGl64Stage2 vq).toNat = vq.toNat % goldilocksPrime := by
    intro vq hvqLt
    have hvq67 : vq.toNat < 2 ^ 67 :=
      Nat.lt_trans vq.isLt (by decide)
    have hc1 : 2 ^ 67 - goldilocksPrime < 2 ^ 67 := by decide
    have hc2 : 2 ^ 67 - 2 * goldilocksPrime < 2 ^ 67 := by decide
    unfold rtlFpgaGl64Stage2
    dsimp only
    apply hMuxSound
    · exact hvqLt
    · rw [rtlAddSplit3Chunk_toNat (by decide), BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hvq67, Nat.mod_eq_of_lt hc1]
    · rw [rtlAddSplit3Chunk_toNat (by decide), BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hvq67, Nat.mod_eq_of_lt hc2]
  rw [Goldilocks.ofNat_val, hStage2 _ (by rw [hStage1]; exact hvBounds.2.1), hStage1, hModEq]

/-- **2-Stage Pipelined FPGA `REG_OUT = 1` Latency-2 Equivalence (`rtlFpgaGl64Step_two_clocks`)**:
    Feeding `x` at clock `t` and any next input `x_next` at clock `t + 1` registers the exact
    canonical Goldilocks residue `(Goldilocks.ofNat x.toNat).val` in `r_q`! -/
