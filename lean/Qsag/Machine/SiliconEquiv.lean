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
theorem rtlFpgaGl64Step_two_clocks (st₀ : FpgaGl64PipeState) (x x_next : BitVec 136) :
    (rtlFpgaGl64Step (rtlFpgaGl64Step st₀ x) x_next).r_q.toNat =
      (Goldilocks.ofNat x.toNat).val :=
  rtlFpgaGl64Reduce_sound x

/-! ## 5. ASIC `Dregg-180` Canonicalizer, Radix-4 Booth Multiplier, Squarer & Karatsuba FSM -/

private def rtlGl64CanonMux (u : BitVec 66) (v : BitVec 65) : BitVec 64 :=
  if u.getLsbD 64 || v.getLsbD 64 then v.extractLsb' 0 64 else u.extractLsb' 0 64

private def rtlGl64CanonStage2 (u : BitVec 66) : BitVec 64 :=
  let eps : BitVec 65 := BitVec.ofNat 65 (2 ^ 32 - 1)
  let uLo65 : BitVec 65 := BitVec.ofNat 65 (u.extractLsb' 0 64).toNat
  let v := rtlPrefixAdd 65 uLo65 eps false
  rtlGl64CanonMux u v

private def rtlGl64CanonStage1 (t : BitVec 76) : BitVec 66 :=
  let q := t.extractLsb' 64 12
  let tLo := t.extractLsb' 0 64
  let qs : BitVec 66 := BitVec.ofNat 66 (q.toNat * 2 ^ 32)
  let qInv : BitVec 66 := ~~~(BitVec.ofNat 66 q.toNat)
  let u_sc := rtlCsa32 66 (BitVec.ofNat 66 tLo.toNat) qs qInv
  rtlPrefixAdd 66 u_sc.1 u_sc.2 true

/-- Exact RTL model of `qsag_gl64_canon` (`W = 32, GB = 12`, `qsag_gl64_karatsuba_csa.sv:261-283`). -/
def rtlGl64Canon (x y : BitVec 76) : BitVec 64 :=
  rtlGl64CanonStage2 (rtlGl64CanonStage1 (rtlPrefixAdd 76 x y false))

private theorem rtlGl64CanonMux_sound (u : BitVec 66) (v : BitVec 65)
    (huLt2P : u.toNat < 2 * goldilocksPrime)
    (hvToNat : v.toNat = (u.extractLsb' 0 64).toNat + (2 ^ 32 - 1)) :
    (rtlGl64CanonMux u v).toNat = u.toNat % goldilocksPrime := by
  let uVal := u.toNat
  let uLo := (u.extractLsb' 0 64).toNat
  have huLoEq : uLo = uVal % 2 ^ 64 := by
    dsimp only [uLo, uVal]; simp [BitVec.extractLsb'_toNat]
  have huBit64 : u.getLsbD 64 = decide (2 ^ 64 ≤ uVal) := by
    rw [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
    change decide (uVal / 18446744073709551616 % 2 = 1) = decide (18446744073709551616 ≤ uVal)
    by_cases hGe : 18446744073709551616 ≤ uVal
    · have hDiv1 : uVal / 18446744073709551616 = 1 := by
        dsimp only [uVal] at *; unfold goldilocksPrime at huLt2P; omega
      rw [decide_eq_true hGe, hDiv1]; rfl
    · have hDiv0 : uVal / 18446744073709551616 = 0 := by omega
      rw [decide_eq_false hGe, hDiv0]; rfl
  have hvBit64 : v.getLsbD 64 = decide (2 ^ 64 ≤ v.toNat) := by
    have hvLt65 : v.toNat < 36893488147419103232 := v.isLt
    rw [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
    change decide (v.toNat / 18446744073709551616 % 2 = 1) = decide (18446744073709551616 ≤ v.toNat)
    by_cases hGe : 18446744073709551616 ≤ v.toNat
    · have hDiv1 : v.toNat / 18446744073709551616 = 1 := by omega
      rw [decide_eq_true hGe, hDiv1]; rfl
    · have hDiv0 : v.toNat / 18446744073709551616 = 0 := by omega
      rw [decide_eq_false hGe, hDiv0]; rfl
  unfold rtlGl64CanonMux
  rw [huBit64, hvBit64]
  have hPLt64 : goldilocksPrime < 2 ^ 64 := by decide
  by_cases hLtP : uVal < goldilocksPrime
  · have hNotU64 : ¬ (2 ^ 64 ≤ uVal) := by
      change ¬ (18446744073709551616 ≤ uVal); unfold goldilocksPrime at hLtP; omega
    have huLt64 : uVal < 2 ^ 64 := Nat.lt_trans hLtP hPLt64
    have huLoId : uLo = uVal := by rw [huLoEq, Nat.mod_eq_of_lt huLt64]
    have hNotV64 : ¬ (2 ^ 64 ≤ v.toNat) := by
      rw [hvToNat]; change ¬ (18446744073709551616 ≤ uLo + 4294967295)
      rw [huLoId]; unfold goldilocksPrime at hLtP; omega
    have hCondF : (decide (2 ^ 64 ≤ uVal) || decide (2 ^ 64 ≤ v.toNat)) = false := by
      rw [decide_eq_false hNotU64, decide_eq_false hNotV64]; rfl
    rw [hCondF, ite_neg Bool.false_ne_true]
    change uLo = uVal % goldilocksPrime
    rw [huLoId, Nat.mod_eq_of_lt hLtP]
  · have hSubLtP : uVal - goldilocksPrime < goldilocksPrime := by
      dsimp only [uVal] at *; omega
    have hSubLt64 : uVal - goldilocksPrime < 2 ^ 64 := Nat.lt_trans hSubLtP hPLt64
    change _ = uVal % goldilocksPrime
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hSubLtP]
    by_cases hGe64 : 2 ^ 64 ≤ uVal
    · have hCondT : (decide (2 ^ 64 ≤ uVal) || decide (2 ^ 64 ≤ v.toNat)) = true := by
        rw [decide_eq_true hGe64, Bool.true_or]
      rw [hCondT, ite_pos rfl, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, hvToNat]
      change (uLo + (2 ^ 32 - 1)) % 2 ^ 64 = uVal - goldilocksPrime
      rw [huLoEq]
      have huDiffLt64 : uVal - 2 ^ 64 < 2 ^ 64 := by
        change uVal - 18446744073709551616 < 18446744073709551616
        dsimp only [uVal] at *; unfold goldilocksPrime at huLt2P; omega
      have huMod64 : uVal % 2 ^ 64 = uVal - 2 ^ 64 := by
        rw [Nat.mod_eq_sub_mod hGe64, Nat.mod_eq_of_lt huDiffLt64]
      rw [huMod64]
      have hEqSub : uVal - 2 ^ 64 + (2 ^ 32 - 1) = uVal - goldilocksPrime := by
        change uVal - 18446744073709551616 + 4294967295 = uVal - goldilocksPrime
        unfold goldilocksPrime at *; omega
      rw [hEqSub, Nat.mod_eq_of_lt hSubLt64]
    · have huLt64 : uVal < 2 ^ 64 := by omega
      have huLoId : uLo = uVal := by rw [huLoEq, Nat.mod_eq_of_lt huLt64]
      have hvGe64 : 2 ^ 64 ≤ v.toNat := by
        rw [hvToNat]; change 18446744073709551616 ≤ uLo + 4294967295
        rw [huLoId]; unfold goldilocksPrime at *; omega
      have hCondT : (decide (2 ^ 64 ≤ uVal) || decide (2 ^ 64 ≤ v.toNat)) = true := by
        rw [decide_eq_true hvGe64, Bool.or_true]
      rw [hCondT, ite_pos rfl, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, hvToNat]
      change (uLo + (2 ^ 32 - 1)) % 2 ^ 64 = uVal - goldilocksPrime
      rw [huLoId]
      have hEq : uVal + (2 ^ 32 - 1) = (uVal - goldilocksPrime) + 2 ^ 64 * 1 := by
        change uVal + 4294967295 = (uVal - goldilocksPrime) + 18446744073709551616 * 1
        unfold goldilocksPrime at *; omega
      rw [hEq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hSubLt64]

private theorem rtlGl64CanonStage1_sound (t : BitVec 76) :
    (rtlGl64CanonStage1 t).toNat < 2 * goldilocksPrime ∧
    (rtlGl64CanonStage1 t).toNat % goldilocksPrime = t.toNat % goldilocksPrime := by
  let q := (t.extractLsb' 64 12).toNat
  let tLo := (t.extractLsb' 0 64).toNat
  have hqLt : q < 4096 := (t.extractLsb' 64 12).isLt
  have htLoLt : tLo < 18446744073709551616 := (t.extractLsb' 0 64).isLt
  have htSplit : t.toNat = tLo + 2 ^ 64 * q := by
    dsimp only [q, tLo]
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one]
    have hDivLt : t.toNat / 2 ^ 64 < 2 ^ 12 := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      exact Nat.lt_of_lt_of_eq t.isLt (by decide)
    rw [Nat.mod_eq_of_lt hDivLt]
    exact (Nat.mod_add_div t.toNat (2 ^ 64)).symm
  let uVal := tLo + 4294967296 * q - q
  have huLt2P : uVal < 2 * goldilocksPrime ∧ 2 * goldilocksPrime < 73786976294838206464 := by
    refine ⟨?_, by decide⟩
    dsimp only [uVal]; unfold goldilocksPrime; omega
  have huToNat : (rtlGl64CanonStage1 t).toNat = uVal := by
    unfold rtlGl64CanonStage1
    dsimp only
    rw [rtlPrefixAdd_toNat, show true.toNat = 1 from rfl]
    have hCsa := rtlCsa32_mod 66 (BitVec.ofNat 66 tLo) (BitVec.ofNat 66 (q * 2 ^ 32))
      (~~~(BitVec.ofNat 66 q))
    rw [Nat.add_mod _ 1, hCsa, ← Nat.add_mod]
    simp only [bitVec_not_toNat, BitVec.toNat_ofNat]
    have htLo66 : tLo < 2 ^ 66 := by change tLo < 73786976294838206464; omega
    have hqSh66 : q * 2 ^ 32 < 2 ^ 66 := by change q * 4294967296 < 73786976294838206464; omega
    have hq66 : q < 2 ^ 66 := by change q < 73786976294838206464; omega
    have hu66 : uVal < 2 ^ 66 := by change uVal < 73786976294838206464; omega
    change ((tLo % 2 ^ 66) + ((q * 2 ^ 32) % 2 ^ 66) + (2 ^ 66 - 1 - (q % 2 ^ 66)) + 1) % 2 ^ 66 = uVal
    rw [Nat.mod_eq_of_lt htLo66, Nat.mod_eq_of_lt hqSh66, Nat.mod_eq_of_lt hq66]
    have hWrap : tLo + q * 2 ^ 32 + (2 ^ 66 - 1 - q) + 1 = uVal + 2 ^ 66 * 1 := by
      change tLo + q * 4294967296 + (73786976294838206464 - 1 - q) + 1 =
        uVal + 73786976294838206464 * 1
      dsimp only [uVal]; omega
    rw [hWrap, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu66]
  refine ⟨by rw [huToNat]; exact huLt2P.1, ?_⟩
  rw [huToNat, htSplit]
  have hLin : tLo + 2 ^ 64 * q = uVal + goldilocksPrime * q := by
    change tLo + 18446744073709551616 * q = uVal + goldilocksPrime * q
    dsimp only [uVal]; unfold goldilocksPrime; omega
  rw [hLin, Nat.add_mul_mod_self_left]

/-- **ASIC 76-Bit Guard-Bit Canonicalizer Soundness (`rtlGl64Canon_sound`)**:
    For all `x, y : BitVec 76` with `x.toNat + y.toNat < 2 ^ 76`, `rtlGl64Canon x y` equals
    `(x.toNat + y.toNat) % goldilocksPrime`! -/
theorem rtlGl64Canon_sound (x y : BitVec 76) (hSum : x.toNat + y.toNat < 2 ^ 76) :
    (rtlGl64Canon x y).toNat = (x.toNat + y.toNat) % goldilocksPrime := by
  have hStage2 : ∀ u : BitVec 66, u.toNat < 2 * goldilocksPrime →
      (rtlGl64CanonStage2 u).toNat = u.toNat % goldilocksPrime := by
    intro u huLt2P
    unfold rtlGl64CanonStage2
    dsimp only
    apply rtlGl64CanonMux_sound u _ huLt2P
    rw [rtlPrefixAdd_toNat, show false.toNat = 0 from rfl, Nat.add_zero,
        BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have huLoLt64 : (u.extractLsb' 0 64).toNat < 18446744073709551616 := (u.extractLsb' 0 64).isLt
    have huLoLt65 : (u.extractLsb' 0 64).toNat < 2 ^ 65 := by
      change (u.extractLsb' 0 64).toNat < 36893488147419103232; omega
    have hEpsLt65 : 2 ^ 32 - 1 < 2 ^ 65 := by decide
    have hSumLt65 : (u.extractLsb' 0 64).toNat + (2 ^ 32 - 1) < 2 ^ 65 := by
      change (u.extractLsb' 0 64).toNat + 4294967295 < 36893488147419103232; omega
    rw [Nat.mod_eq_of_lt huLoLt65, Nat.mod_eq_of_lt hEpsLt65, Nat.mod_eq_of_lt hSumLt65]
  unfold rtlGl64Canon
  obtain ⟨huLt2P, huMod⟩ := rtlGl64CanonStage1_sound (rtlPrefixAdd 76 x y false)
  rw [hStage2 _ huLt2P, huMod, rtlPrefixAdd_toNat, show false.toNat = 0 from rfl,
      Nat.add_zero, Nat.mod_eq_of_lt hSum]

/-- Signed radix-4 Booth digit `b_{2j-1} + b_{2j} - 2 * b_{2j+1} ∈ {-2, -1, 0, +1, +2}`. -/
def boothDigitInt (b0 b1 b2 : Bool) : Int :=
  (b0.toNat : Int) + (b1.toNat : Int) - 2 * (b2.toNat : Int)

/-- Parameterized Booth row generator on explicit window bits `(b0, b1, b2)`. -/
def rtlBoothRow66Core (a : BitVec 33) (b0 b1 b2 : Bool) (j : Nat) : BitVec 66 × Bool :=
  let ap : BitVec 66 := BitVec.ofNat 66 a.toNat
  let ap2 : BitVec 66 := ap <<< 1
  let code := b0.toNat + 2 * b1.toNat + 4 * b2.toNat
  let (extDigit, negJ) : BitVec 66 × Bool :=
    if code == 1 || code == 2 then (ap, false)
    else if code == 3 then (ap2, false)
    else if code == 4 then (~~~ap2, true)
    else if code == 5 || code == 6 then (~~~ap, true)
    else (0, false)
  (extDigit <<< (2 * j), negJ)

/-- One 66-bit radix-4 Booth row + `neg_j` bit matching `qsag_mul33` (`qsag_gl64_karatsuba_csa.sv:94-109`). -/
def rtlBoothRow66 (a : BitVec 33) (bx : BitVec 35) (j : Nat) : BitVec 66 × Bool :=
  rtlBoothRow66Core a (bx.getLsbD (2 * j)) (bx.getLsbD (2 * j + 1)) (bx.getLsbD (2 * j + 2)) j

/-- Exact RTL model of `qsag_mul33` (`W = 32`, `qsag_gl64_karatsuba_csa.sv:79-121`) compressing 17
    radix-4 Booth rows + `neg_row` via `rtlCsaReduce2` and `rtlPrefixAdd` (RTL `qsag_mul_csa_tree`). -/
def rtlMul33 (a : BitVec 33) (b : BitVec 33) : BitVec 66 :=
  let bx : BitVec 35 := BitVec.ofNat 35 (2 * b.toNat)
  let pairs := (List.range 17).map (rtlBoothRow66 a bx)
  let negRowVal := ((List.range 17).map fun j =>
    if (rtlBoothRow66 a bx j).2 then 4 ^ j else 0).sum
  let rows : List (BitVec 66) := pairs.map Prod.fst ++ [BitVec.ofNat 66 negRowVal]
  let sc := rtlCsaReduce2 66 rows
  rtlPrefixAdd 66 sc.1 sc.2 false

private theorem boothRow66Core_int_congr (a : BitVec 33) (b0 b1 b2 : Bool) (j : Nat) :
    (((rtlBoothRow66Core a b0 b1 b2 j).1.toNat : Int) +
        (if (rtlBoothRow66Core a b0 b1 b2 j).2 then (4 ^ j : Int) else 0)) % (2 ^ 66 : Int) =
      (boothDigitInt b0 b1 b2 * (a.toNat : Int) * (4 ^ j : Int)) % (2 ^ 66 : Int) := by
  have haLt : a.toNat < 8589934592 := a.isLt
  have ha66 : a.toNat < 2 ^ 66 := by change a.toNat < 73786976294838206464; omega
  have h2a66 : 2 * a.toNat < 2 ^ 66 := by change 2 * a.toNat < 73786976294838206464; omega
  have hSh1 : ((BitVec.ofNat 66 a.toNat) <<< 1).toNat = 2 * a.toNat := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha66,
        Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm, Nat.mod_eq_of_lt h2a66]
  have h4j : (2 : Nat) ^ (2 * j) = 4 ^ j := Nat.pow_mul 2 2 j
  generalize hPj : (4 : Int) ^ j = P
  have h4jInt : ((4 ^ j : Nat) : Int) = P := by rw [← hPj]; exact Int.natCast_pow 4 j
  have h2Pow66Cast : ((2 ^ 66 : Nat) : Int) = (2 ^ 66 : Int) := Int.natCast_pow 2 66
  cases b0 <;> cases b1 <;> cases b2
  -- 000 (`code = 0`, digit = 0)
  · change (((0#66 <<< (2 * j)).toNat : Int) + 0) % (2 ^ 66 : Int) =
      ((0 + 0 - 2 * 0) * (a.toNat : Int) * P) % (2 ^ 66 : Int)
    simp
  -- 001 (`code = 4`, digit = -2, `~~~ap2`)
  · change (((((~~~(BitVec.ofNat 66 a.toNat <<< 1)) <<< (2 * j)).toNat : Int) + P) % (2 ^ 66 : Int)) =
      ((0 + 0 - 2 * 1) * (a.toNat : Int) * P) % (2 ^ 66 : Int)
    rw [BitVec.toNat_shiftLeft, bitVec_not_toNat, hSh1, Nat.shiftLeft_eq, h4j,
        Int.natCast_emod, h2Pow66Cast, Int.natCast_mul, h4jInt, Int.emod_add_emod]
    have hSub : ((2 ^ 66 - 1 - 2 * a.toNat : Nat) : Int) = (2 ^ 66 : Int) - 1 - 2 * (a.toNat : Int) := by
      change ((73786976294838206464 - 1 - 2 * a.toNat : Nat) : Int) =
        73786976294838206464 - 1 - 2 * (a.toNat : Int)
      omega
    have hEq : (((2 ^ 66 - 1 - 2 * a.toNat : Nat) : Int) * P + P) =
        ((0 + 0 - 2 * 1) * (a.toNat : Int) * P) + (2 ^ 66 : Int) * P := by
      rw [hSub, Int.sub_mul, Int.sub_mul]
      change (2 ^ 66 : Int) * P - 1 * P - 2 * (a.toNat : Int) * P + P =
        (-(2 : Int)) * (a.toNat : Int) * P + (2 ^ 66 : Int) * P
      rw [Int.one_mul, Int.neg_mul, Int.neg_mul]
      omega
    rw [hEq, Int.add_mul_emod_self_left]
  -- 010 (`code = 2`, digit = +1, `ap`)
  · change ((((BitVec.ofNat 66 a.toNat <<< (2 * j)).toNat : Int) + 0) % (2 ^ 66 : Int)) =
      ((0 + 1 - 2 * 0) * (a.toNat : Int) * P) % (2 ^ 66 : Int)
    rw [Int.add_zero, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha66,
        Nat.shiftLeft_eq, h4j, Int.natCast_emod, h2Pow66Cast, Int.natCast_mul, h4jInt]
    simp
  -- 011 (`code = 6`, digit = -1, `~~~ap`)
  · change (((((~~~(BitVec.ofNat 66 a.toNat)) <<< (2 * j)).toNat : Int) + P) % (2 ^ 66 : Int)) =
      ((0 + 1 - 2 * 1) * (a.toNat : Int) * P) % (2 ^ 66 : Int)
    rw [BitVec.toNat_shiftLeft, bitVec_not_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha66,
        Nat.shiftLeft_eq, h4j, Int.natCast_emod, h2Pow66Cast, Int.natCast_mul, h4jInt, Int.emod_add_emod]
    have hSub : ((2 ^ 66 - 1 - a.toNat : Nat) : Int) = (2 ^ 66 : Int) - 1 - (a.toNat : Int) := by
      change ((73786976294838206464 - 1 - a.toNat : Nat) : Int) =
        73786976294838206464 - 1 - (a.toNat : Int)
      omega
    have hEq : (((2 ^ 66 - 1 - a.toNat : Nat) : Int) * P + P) =
        ((0 + 1 - 2 * 1) * (a.toNat : Int) * P) + (2 ^ 66 : Int) * P := by
      rw [hSub, Int.sub_mul, Int.sub_mul]
      change (2 ^ 66 : Int) * P - 1 * P - (a.toNat : Int) * P + P =
        (-(1 : Int)) * (a.toNat : Int) * P + (2 ^ 66 : Int) * P
      rw [Int.one_mul, Int.neg_mul, Int.one_mul, Int.neg_mul]
      omega
    rw [hEq, Int.add_mul_emod_self_left]
  -- 100 (`code = 1`, digit = +1, `ap`)
  · change ((((BitVec.ofNat 66 a.toNat <<< (2 * j)).toNat : Int) + 0) % (2 ^ 66 : Int)) =
      ((1 + 0 - 2 * 0) * (a.toNat : Int) * P) % (2 ^ 66 : Int)
    rw [Int.add_zero, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha66,
        Nat.shiftLeft_eq, h4j, Int.natCast_emod, h2Pow66Cast, Int.natCast_mul, h4jInt]
    simp
  -- 101 (`code = 5`, digit = -1, `~~~ap`)
  · change (((((~~~(BitVec.ofNat 66 a.toNat)) <<< (2 * j)).toNat : Int) + P) % (2 ^ 66 : Int)) =
      ((1 + 0 - 2 * 1) * (a.toNat : Int) * P) % (2 ^ 66 : Int)
    rw [BitVec.toNat_shiftLeft, bitVec_not_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha66,
        Nat.shiftLeft_eq, h4j, Int.natCast_emod, h2Pow66Cast, Int.natCast_mul, h4jInt, Int.emod_add_emod]
    have hSub : ((2 ^ 66 - 1 - a.toNat : Nat) : Int) = (2 ^ 66 : Int) - 1 - (a.toNat : Int) := by
      change ((73786976294838206464 - 1 - a.toNat : Nat) : Int) =
        73786976294838206464 - 1 - (a.toNat : Int)
      omega
    have hEq : (((2 ^ 66 - 1 - a.toNat : Nat) : Int) * P + P) =
        ((1 + 0 - 2 * 1) * (a.toNat : Int) * P) + (2 ^ 66 : Int) * P := by
      rw [hSub, Int.sub_mul, Int.sub_mul]
      change (2 ^ 66 : Int) * P - 1 * P - (a.toNat : Int) * P + P =
        (-(1 : Int)) * (a.toNat : Int) * P + (2 ^ 66 : Int) * P
      rw [Int.one_mul, Int.neg_mul, Int.one_mul, Int.neg_mul]
      omega
    rw [hEq, Int.add_mul_emod_self_left]
  -- 110 (`code = 3`, digit = +2, `ap2`)
  · change (((((BitVec.ofNat 66 a.toNat <<< 1) <<< (2 * j)).toNat : Int) + 0) % (2 ^ 66 : Int)) =
      ((1 + 1 - 2 * 0) * (a.toNat : Int) * P) % (2 ^ 66 : Int)
    rw [Int.add_zero, BitVec.toNat_shiftLeft, hSh1, Nat.shiftLeft_eq, h4j,
        Int.natCast_emod, h2Pow66Cast, Int.natCast_mul, Int.natCast_mul, h4jInt]
    simp
  -- 111 (`code = 7`, digit = 0)
  · change (((0#66 <<< (2 * j)).toNat : Int) + 0) % (2 ^ 66 : Int) =
      ((1 + 1 - 2 * 1) * (a.toNat : Int) * P) % (2 ^ 66 : Int)
    simp

private theorem booth_telescope (fb : Nat → Bool) :
    ∀ R : Nat,
      ((List.range R).map fun j =>
        boothDigitInt (fb (2 * j)) (fb (2 * j + 1)) (fb (2 * j + 2)) * (4 ^ j : Int)).sum =
      (natOfBits (2 * R) (fun k => fb (k + 1)) : Int) +
        ((fb 0).toNat : Int) - (2 ^ (2 * R) : Int) * ((fb (2 * R)).toNat : Int)
  | 0 => by simp [natOfBits]
  | R + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
        booth_telescope fb R]
    have hSplitBits : ∀ (m : Nat) (g : Nat → Bool),
        natOfBits (m + 2) g = natOfBits m g + 2 ^ m * ((g m).toNat + 2 * (g (m + 1)).toNat) := by
      intro m
      induction m with
      | zero => intro g; simp [natOfBits]
      | succ m ih =>
        intro g
        change (g 0).toNat + 2 * natOfBits (m + 2) (fun i => g (i + 1)) =
          ((g 0).toNat + 2 * natOfBits m (fun i => g (i + 1))) +
            2 ^ (m + 1) * ((g (m + 1)).toNat + 2 * (g (m + 1 + 1)).toNat)
        rw [ih (fun i => g (i + 1)), Nat.pow_succ]
        have hAssoc : 2 ^ m * 2 * ((g (m + 1)).toNat + 2 * (g (m + 1 + 1)).toNat) =
            2 * (2 ^ m * ((g (m + 1)).toNat + 2 * (g (m + 1 + 1)).toNat)) := by
          rw [Nat.mul_comm (2 ^ m) 2, Nat.mul_assoc]
        rw [hAssoc]; omega
    have hBits := hSplitBits (2 * R) (fun k => fb (k + 1))
    have h2R2 : 2 * (R + 1) = 2 * R + 2 := by omega
    rw [h2R2, hBits]
    dsimp only [boothDigitInt]
    have h2Pow : (2 : Nat) ^ (2 * R) = 4 ^ R := Nat.pow_mul 2 2 R
    have h2PowInt : (2 : Int) ^ (2 * R) = (4 : Int) ^ R := by
      have hCast : ((2 ^ (2 * R) : Nat) : Int) = ((4 ^ R : Nat) : Int) := congrArg Int.ofNat h2Pow
      simpa [Int.natCast_pow] using hCast
    have h2PowNext : (2 : Int) ^ (2 * R + 2) = 4 * (4 : Int) ^ R := by
      rw [Int.pow_add, h2PowInt]; omega
    have h2PowNatInt : ((2 ^ (2 * R) : Nat) : Int) = (4 : Int) ^ R := by
      rw [h2Pow]; exact Int.natCast_pow 4 R
    rw [Int.natCast_add, Int.natCast_mul, h2PowInt, h2PowNext, h2PowNatInt]
    have hIdx1 : 2 * R + 1 + 1 = 2 * R + 2 := by omega
    rw [hIdx1]
    generalize (4 : Int) ^ R = P
    generalize fb (2 * R) = c0
    generalize fb (2 * R + 1) = c1
    generalize fb (2 * R + 2) = c2
    cases c0 <;> cases c1 <;> cases c2 <;> dsimp only [Bool.toNat, cond] <;> omega

private theorem boothRow66_int_congr (a : BitVec 33) (bx : BitVec 35) (j : Nat) :
    (((rtlBoothRow66 a bx j).1.toNat : Int) +
        (if (rtlBoothRow66 a bx j).2 then (4 ^ j : Int) else 0)) % (2 ^ 66 : Int) =
      (boothDigitInt (bx.getLsbD (2 * j)) (bx.getLsbD (2 * j + 1)) (bx.getLsbD (2 * j + 2)) *
        (a.toNat : Int) * (4 ^ j : Int)) % (2 ^ 66 : Int) :=
  boothRow66Core_int_congr a (bx.getLsbD (2 * j)) (bx.getLsbD (2 * j + 1)) (bx.getLsbD (2 * j + 2)) j

private theorem rtlMul33_aux (a b : BitVec 33)
    (bx : BitVec 35) (hbxDef : BitVec.ofNat 35 (2 * b.toNat) = bx)
    (negRowVal : Nat)
    (hNegDef : ((List.range 17).map fun j =>
      if (rtlBoothRow66 a bx j).2 then 4 ^ j else 0).sum = negRowVal)
    (rows : List (BitVec 66))
    (hRowsDef : ((List.range 17).map (rtlBoothRow66 a bx)).map Prod.fst ++
      [BitVec.ofNat 66 negRowVal] = rows) :
    (rtlPrefixAdd 66 (rtlCsaReduce2 66 rows).1 (rtlCsaReduce2 66 rows).2 false).toNat =
      a.toNat * b.toNat := by
  have hbLt : b.toNat < 2 ^ 33 := b.isLt
  have haLt : a.toNat < 2 ^ 33 := a.isLt
  have hProdLt : a.toNat * b.toNat < 2 ^ 66 :=
    Nat.lt_of_lt_of_eq (Nat.mul_lt_mul'' haLt hbLt) (by decide)
  have hNegLt : negRowVal < 2 ^ 66 := by
    rw [← hNegDef]
    have hBound17 : ∀ k : Nat, k ≤ 17 →
        ((List.range k).map fun j => if (rtlBoothRow66 a bx j).2 then 4 ^ j else 0).sum ≤ 4 ^ k := by
      intro k hk
      induction k with
      | zero => exact Nat.zero_le 1
      | succ k ih =>
        rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
        have ih' := ih (by omega)
        have hPow1 : 1 ≤ 4 ^ k := Nat.one_le_pow k 4 (by decide)
        rw [Nat.pow_succ]
        cases (rtlBoothRow66 a bx k).2
        · rw [ite_neg Bool.false_ne_true]; omega
        · rw [ite_pos rfl]; omega
    exact Nat.lt_of_le_of_lt (hBound17 17 (Nat.le_refl 17)) (by decide)
  rw [rtlPrefixAdd_toNat, show false.toNat = 0 from rfl, Nat.add_zero, rtlCsaReduce2_mod]
  have hRowsSum : (rows.map BitVec.toNat).sum =
      ((List.range 17).map fun j =>
        (rtlBoothRow66 a bx j).1.toNat + if (rtlBoothRow66 a bx j).2 then 4 ^ j else 0).sum := by
    rw [← hRowsDef, List.map_append, List.sum_append, List.map_map, List.map_map,
        List.map_singleton, List.sum_singleton,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt hNegLt, ← hNegDef]
    have hZipSum : ∀ k : Nat,
        ((List.range k).map (fun j => (rtlBoothRow66 a bx j).1.toNat)).sum +
        ((List.range k).map (fun j => if (rtlBoothRow66 a bx j).2 then 4 ^ j else 0)).sum =
        ((List.range k).map (fun j =>
          (rtlBoothRow66 a bx j).1.toNat + if (rtlBoothRow66 a bx j).2 then 4 ^ j else 0)).sum := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
            List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
            List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
        omega
    exact hZipSum 17
  rw [hRowsSum]
  have hIntMod :
      ((((List.range 17).map fun j =>
          (rtlBoothRow66 a bx j).1.toNat + if (rtlBoothRow66 a bx j).2 then 4 ^ j else 0).sum : Nat) : Int) %
        (2 ^ 66 : Int) =
      (((List.range 17).map fun j =>
          boothDigitInt (bx.getLsbD (2 * j)) (bx.getLsbD (2 * j + 1)) (bx.getLsbD (2 * j + 2)) *
            (a.toNat : Int) * (4 ^ j : Int)).sum) % (2 ^ 66 : Int) := by
    have hK : ∀ k : Nat, k ≤ 17 →
        ((((List.range k).map fun j =>
            (rtlBoothRow66 a bx j).1.toNat + if (rtlBoothRow66 a bx j).2 then 4 ^ j else 0).sum : Nat) : Int) %
          (2 ^ 66 : Int) =
        (((List.range k).map fun j =>
            boothDigitInt (bx.getLsbD (2 * j)) (bx.getLsbD (2 * j + 1)) (bx.getLsbD (2 * j + 2)) *
              (a.toNat : Int) * (4 ^ j : Int)).sum) % (2 ^ 66 : Int) := by
      intro k hk
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
            List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
            Int.natCast_add, Int.natCast_add]
        have hCastIf : (((if (rtlBoothRow66 a bx k).2 then 4 ^ k else 0 : Nat) : Int)) =
            (if (rtlBoothRow66 a bx k).2 then (4 ^ k : Int) else 0) := by
          cases (rtlBoothRow66 a bx k).2
          · rw [ite_neg Bool.false_ne_true, ite_neg Bool.false_ne_true]; rfl
          · rw [ite_pos rfl, ite_pos rfl]; exact Int.natCast_pow 4 k
        rw [hCastIf, Int.add_emod, ih (by omega), boothRow66_int_congr a bx k, ← Int.add_emod]
    exact hK 17 (Nat.le_refl 17)
  have hFactorA : ∀ k : Nat,
      ((List.range k).map fun j =>
        boothDigitInt (bx.getLsbD (2 * j)) (bx.getLsbD (2 * j + 1)) (bx.getLsbD (2 * j + 2)) *
          (a.toNat : Int) * (4 ^ j : Int)).sum =
      (a.toNat : Int) * ((List.range k).map fun j =>
        boothDigitInt (bx.getLsbD (2 * j)) (bx.getLsbD (2 * j + 1)) (bx.getLsbD (2 * j + 2)) *
          (4 ^ j : Int)).sum := by
    intro k
    induction k with
    | zero =>
      change (0 : Int) = (a.toNat : Int) * 0
      rw [Int.mul_zero]
    | succ k ih =>
      rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
          List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
          ih, Int.mul_add]
      congr 1
      rw [← Int.mul_assoc, Int.mul_comm _ (a.toNat : Int), Int.mul_assoc]
  rw [hFactorA 17, booth_telescope bx.getLsbD 17] at hIntMod
  have h2bLt35 : 2 * b.toNat < 2 ^ 35 := by
    change 2 * b.toNat < 34359738368
    change b.toNat < 8589934592 at hbLt; omega
  have hbxVal : bx.toNat = 2 * b.toNat := by
    rw [← hbxDef, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2bLt35]
  have hbx0 : bx.getLsbD 0 = false := by
    rw [BitVec.getLsbD, hbxVal, Nat.testBit_zero]
    exact decide_eq_false (by omega)
  have hbx34 : bx.getLsbD 34 = false := by
    simp only [BitVec.getLsbD, hbxVal]
    apply Nat.testBit_lt_two_pow
    change 2 * b.toNat < 17179869184
    change b.toNat < 8589934592 at hbLt; omega
  have hbxShift : natOfBits 34 (fun k => bx.getLsbD (k + 1)) = b.toNat := by
    have hDecomp := bitVec_toNat_eq_natOfBits bx
    rw [natOfBits, hbxVal, hbx0] at hDecomp
    exact eq_of_two_mul_eq hDecomp
  rw [hbx0, hbx34, hbxShift] at hIntMod
  have hZeroBool : ((false.toNat : Nat) : Int) = 0 := rfl
  rw [hZeroBool, Int.add_zero, Int.mul_zero, Int.sub_zero, ← Int.natCast_mul] at hIntMod
  have hPow66Cast : (2 ^ 66 : Int) = ((2 ^ 66 : Nat) : Int) := (Int.natCast_pow 2 66).symm
  rw [hPow66Cast, ← Int.natCast_emod, ← Int.natCast_emod] at hIntMod
  have hNatModEq := Int.ofNat_inj.mp hIntMod
  rw [hNatModEq, Nat.mod_eq_of_lt hProdLt]

/-- **33×33 Radix-4 Booth Multiplier Soundness (`rtlMul33_sound`)**:
    For all 33-bit operands `a, b : BitVec 33`, `rtlMul33 a b` equals the exact unsigned product
    `a.toNat * b.toNat` (`< 2^66`)! -/
theorem rtlMul33_sound (a b : BitVec 33) :
    (rtlMul33 a b).toNat = a.toNat * b.toNat :=
  rtlMul33_aux a b _ rfl _ rfl _ rfl

attribute [local irreducible] rtlMul33 rtlGl64Canon

/-- Exact RTL model of `qsag_gl64_sqrows` + `qsag_csa52` + `qsag_gl64_canon` (`qsag_gl64_sq_pipe`,
    `qsag_gl64_karatsuba_csa.sv:286-345`). -/
def rtlGl64SqPipe (x : BitVec 64) : BitVec 64 :=
  let x0 := (x.extractLsb' 0 32).toNat
  let x1 := (x.extractLsb' 32 32).toNat
  let z0 := x0 * x0
  let z2 := x1 * x1
  let p01 := x0 * x1
  let m := 2 * p01
  let m0 := m % 2 ^ 32
  let m1 := (m / 2 ^ 32) % 2 ^ 32
  let m2 := m / 2 ^ 64
  let l2 := z2 % 2 ^ 32
  let h2 := z2 / 2 ^ 32
  let c_m2 := if m2 == 1 then 3 else 4
  let topC := 2 ^ 32 - 4
  let r1 : BitVec 76 := BitVec.ofNat 76 z0
  let r2 : BitVec 76 := BitVec.ofNat 76 (m0 * 2 ^ 32 + (2 ^ 32 - 1 - m1))
  let r3 : BitVec 76 := BitVec.ofNat 76 (m1 * 2 ^ 32 + c_m2)
  let r4 : BitVec 76 := BitVec.ofNat 76 (l2 * 2 ^ 32 + (2 ^ 32 - 1 - l2))
  let r5 : BitVec 76 := BitVec.ofNat 76 (topC * 2 ^ 32 + (2 ^ 32 - 1 - h2))
  let sc := rtlCsa52 76 r1 r2 r3 r4 r5
  rtlGl64Canon sc.1 sc.2

/-- **5-Row Goldilocks Squarer Soundness (`rtlGl64SqPipe_sound`)**:
    Matches `(Goldilocks.mul a a).val` bit-for-bit across all 64-bit inputs `x`! -/
theorem rtlGl64SqPipe_sound (x : BitVec 64) :
    (rtlGl64SqPipe x).toNat = (Goldilocks.mul (Goldilocks.ofNat x.toNat) (Goldilocks.ofNat x.toNat)).val := by
  unfold rtlGl64SqPipe
  dsimp only
  let x0 := (x.extractLsb' 0 32).toNat
  let x1 := (x.extractLsb' 32 32).toNat
  have hx0Lt : x0 < 2 ^ 32 := (x.extractLsb' 0 32).isLt
  have hx1Lt : x1 < 2 ^ 32 := (x.extractLsb' 32 32).isLt
  have hxDecomp : x.toNat = x0 + 4294967296 * x1 := by
    dsimp only [x0, x1]
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one]
    have hDivLt : x.toNat / 2 ^ 32 < 2 ^ 32 := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]; exact x.isLt
    rw [Nat.mod_eq_of_lt hDivLt]
    exact (Nat.mod_add_div x.toNat 4294967296).symm
  let z0 := x0 * x0
  let z2 := x1 * x1
  let m  := 2 * (x0 * x1)
  have hz0Lt : z0 < 18446744073709551616 :=
    Nat.lt_of_lt_of_eq (Nat.mul_lt_mul'' hx0Lt hx0Lt) (by decide)
  have hz2Lt : z2 < 18446744073709551616 :=
    Nat.lt_of_lt_of_eq (Nat.mul_lt_mul'' hx1Lt hx1Lt) (by decide)
  have hmLt  : m < 2 * 18446744073709551616 := by
    have hp01 : x0 * x1 < 18446744073709551616 :=
      Nat.lt_of_lt_of_eq (Nat.mul_lt_mul'' hx0Lt hx1Lt) (by decide)
    dsimp only [m]; omega
  let m0 := m % 2 ^ 32
  let m1 := (m / 2 ^ 32) % 2 ^ 32
  let m2 := m / 2 ^ 64
  let l2 := z2 % 2 ^ 32
  let h2 := z2 / 2 ^ 32
  have hm0Lt : m0 < 4294967296 := Nat.mod_lt _ (by decide)
  have hm1Lt : m1 < 4294967296 := Nat.mod_lt _ (by decide)
  have hm2Le1 : m2 ≤ 1 := by change m / 18446744073709551616 ≤ 1; omega
  have hl2Lt : l2 < 4294967296 := Nat.mod_lt _ (by decide)
  have hh2Lt : h2 < 4294967296 := by change z2 / 4294967296 < 4294967296; omega
  have hmDecomp : m = m0 + 4294967296 * m1 + 18446744073709551616 * m2 := by
    change m = m % 4294967296 + 4294967296 * ((m / 4294967296) % 4294967296) +
      18446744073709551616 * (m / 18446744073709551616)
    have d0 := Nat.mod_add_div m 4294967296
    have d1 := Nat.mod_add_div (m / 4294967296) 4294967296
    have h64 : (m / 4294967296) / 4294967296 = m / 18446744073709551616 := by
      rw [Nat.div_div_eq_div_mul]
    rw [h64] at d1; omega
  have hz2Decomp : z2 = l2 + 4294967296 * h2 := (Nat.mod_add_div z2 4294967296).symm
  have hcM2 : (if m2 == 1 then 3 else 4) = 4 - m2 := by
    by_cases h1 : m2 = 1
    · rw [h1]; rfl
    · rw [beq_eq_false_iff_ne.mpr h1, ite_neg Bool.false_ne_true]; omega
  let r1 : BitVec 76 := BitVec.ofNat 76 z0
  let r2 : BitVec 76 := BitVec.ofNat 76 (m0 * 2 ^ 32 + (2 ^ 32 - 1 - m1))
  let r3 : BitVec 76 := BitVec.ofNat 76 (m1 * 2 ^ 32 + (if m2 == 1 then 3 else 4))
  let r4 : BitVec 76 := BitVec.ofNat 76 (l2 * 2 ^ 32 + (2 ^ 32 - 1 - l2))
  let r5 : BitVec 76 := BitVec.ofNat 76 ((2 ^ 32 - 4) * 2 ^ 32 + (2 ^ 32 - 1 - h2))
  have hr1Val : r1.toNat = z0 := by
    dsimp only [r1]; rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by change z0 < 75557863725914323419136; omega)
  have hr2Val : r2.toNat = m0 * 4294967296 + (4294967295 - m1) := by
    dsimp only [r2]; rw [BitVec.toNat_ofNat]
    change (m0 * 4294967296 + (4294967295 - m1)) % 75557863725914323419136 = _
    exact Nat.mod_eq_of_lt (by omega)
  have hr3Val : r3.toNat = m1 * 4294967296 + (4 - m2) := by
    dsimp only [r3]; rw [hcM2, BitVec.toNat_ofNat]
    change (m1 * 4294967296 + (4 - m2)) % 75557863725914323419136 = _
    exact Nat.mod_eq_of_lt (by omega)
  have hr4Val : r4.toNat = l2 * 4294967296 + (4294967295 - l2) := by
    dsimp only [r4]; rw [BitVec.toNat_ofNat]
    change (l2 * 4294967296 + (4294967295 - l2)) % 75557863725914323419136 = _
    exact Nat.mod_eq_of_lt (by omega)
  have hr5Val : r5.toNat = 4294967292 * 4294967296 + (4294967295 - h2) := by
    dsimp only [r5]; rw [BitVec.toNat_ofNat]
    change (4294967292 * 4294967296 + (4294967295 - h2)) % 75557863725914323419136 = _
    exact Nat.mod_eq_of_lt (by omega)
  let sSq := (z0 + 4294967296 * m0 + 4294967295 * (m1 + l2) + goldilocksPrime) - (m2 + h2)
  have hsSqLe : m2 + h2 ≤ z0 + 4294967296 * m0 + 4294967295 * (m1 + l2) + goldilocksPrime := by
    clear hxDecomp hmDecomp hz2Decomp; unfold goldilocksPrime; omega
  have hsSqCast : (sSq : Int) =
      (z0 : Int) + 4294967296 * (m0 : Int) + 4294967295 * ((m1 : Int) + (l2 : Int)) +
      (goldilocksPrime : Int) - ((m2 : Int) + (h2 : Int)) := by
    dsimp only [sSq]
    rw [int_natCast_sub hsSqLe]
    simp only [Int.natCast_add, Int.natCast_mul]
    clear hxDecomp hmDecomp hz2Decomp hsSqLe; omega
  have hrSum : r1.toNat + r2.toNat + r3.toNat + r4.toNat + r5.toNat = sSq := by
    rw [hr1Val, hr2Val, hr3Val, hr4Val, hr5Val]
    apply nat_eq_of_int_eq
    rw [hsSqCast]
    have sub1 : m1 ≤ 4294967295 := by clear hsSqCast; omega
    have sub2 : m2 ≤ 4 := by clear hsSqCast; omega
    have sub3 : l2 ≤ 4294967295 := by clear hsSqCast; omega
    have sub4 : h2 ≤ 4294967295 := by clear hsSqCast; omega
    simp only [Int.natCast_add, Int.natCast_mul,
      int_natCast_sub sub1, int_natCast_sub sub2, int_natCast_sub sub3, int_natCast_sub sub4]
    clear hxDecomp hmDecomp hz2Decomp hsSqLe hsSqCast hr1Val hr2Val hr3Val hr4Val hr5Val hcM2 sub1 sub2 sub3 sub4
    unfold goldilocksPrime
    omega
  have hrLt76 : r1.toNat + r2.toNat + r3.toNat + r4.toNat + r5.toNat < 2 ^ 76 := by
    rw [hrSum]
    change sSq < 75557863725914323419136
    apply nat_lt_of_int_lt
    rw [hsSqCast]
    clear hxDecomp hmDecomp hz2Decomp hsSqLe hsSqCast hr1Val hr2Val hr3Val hr4Val hr5Val hrSum hcM2
    unfold goldilocksPrime
    omega
  have hCsa := rtlCsa52_exact r1 r2 r3 r4 r5 hrLt76
  change (rtlGl64Canon (rtlCsa52 76 r1 r2 r3 r4 r5).1 (rtlCsa52 76 r1 r2 r3 r4 r5).2).toNat = _
  rw [rtlGl64Canon_sound _ _ (by rw [hCsa]; exact hrLt76), hCsa, hrSum,
      Goldilocks.mul_val, Goldilocks.ofNat_val, Nat.mod_mul_mod, Nat.mul_mod_mod]
  have hSqExpand : x.toNat * x.toNat = z0 + 4294967296 * m + 18446744073709551616 * z2 := by
    rw [hxDecomp]
    exact sq_split32_expand x0 x1
  have hCongr : x.toNat * x.toNat + goldilocksPrime * 1 =
      sSq + goldilocksPrime * (m1 + l2 + 4294967297 * (m2 + h2)) := by
    rw [hSqExpand, hmDecomp, hz2Decomp]
    apply nat_eq_of_int_eq
    rw [Int.natCast_add sSq _, hsSqCast]
    simp only [Int.natCast_add, Int.natCast_mul]
    clear hxDecomp hmDecomp hz2Decomp hsSqLe hsSqCast hr1Val hr2Val hr3Val hr4Val hr5Val hrSum hrLt76 hCsa hSqExpand hcM2
    unfold goldilocksPrime
    omega
  rw [← Nat.add_mul_mod_self_left (x.toNat * x.toNat) goldilocksPrime 1, hCongr,
      Nat.add_mul_mod_self_left]

/-- Exact RTL model of `qsag_gl64_mrows` (`W = 32, GB = 12`, `qsag_gl64_karatsuba_csa.sv:218-258`). -/
def rtlGl64Mrows (p : BitVec 66) (ph : Fin 4) : BitVec 76 × BitVec 76 × BitVec 76 :=
  let lo := (p.extractLsb' 0 32).toNat
  let hi := (p.extractLsb' 32 32).toNat
  let m2 := (p.extractLsb' 64 2).toNat
  let p64 := (p.extractLsb' 0 64).toNat
  let kMul := goldilocksPrime - 2 ^ 33 + 2
  match ph.1 with
  | 1 =>
    (BitVec.ofNat 76 p64,
     BitVec.ofNat 76 ((2 ^ 32 - 1 - lo) * 2 ^ 32 + hi),
     BitVec.ofNat 76 ((2 ^ 32 - 1 - hi) * 2 ^ 32))
  | 2 =>
    (BitVec.ofNat 76 (2 ^ 64 - 1 - p64),
     BitVec.ofNat 76 kMul,
     0)
  | 3 =>
    (BitVec.ofNat 76 (lo * 2 ^ 32 + (2 ^ 32 - 1 - hi)),
     BitVec.ofNat 76 (hi * 2 ^ 32 + (3 - m2)),
     0)
  | _ => (0, 0, 0)

/-- Cycle-accurate register state of `qsag_gl64_karatsuba_csa` (`qsag_gl64_karatsuba_csa.sv:384-390`)
    during a 4-cycle multiply (`mph = 0 → 1 → 2 → 3`). -/
structure KaratsubaState where
  opa : BitVec 64
  opb : BitVec 64
  acc_s : BitVec 76
  acc_c : BitVec 76
  preg : BitVec 66
  sa : BitVec 33
  sb : BitVec 33
  mph : Fin 4

/-- Combinational outputs `(mul_busy, mul_last, cv)` of `qsag_gl64_karatsuba_csa.sv:434-447`. -/
def rtlKaratsubaOutputs (st : KaratsubaState) : Bool × Bool × BitVec 64 :=
  let in_mul := st.mph.1 != 0
  let use0 := st.mph.1 == 1
  let cx := if use0 then 0 else st.acc_s
  let cy := if use0 then 0 else st.acc_c
  let mr := rtlGl64Mrows st.preg st.mph
  let nsc := rtlCsa52 76 cx cy mr.1 mr.2.1 mr.2.2
  let cv := rtlGl64Canon nsc.1 nsc.2
  (in_mul, st.mph.1 == 3, cv)

/-- One positive clock edge of `qsag_gl64_karatsuba_csa.sv:397-481` (`rst_n = 1`, `asel = bsel = 0`). -/
def rtlKaratsubaStep (st : KaratsubaState) (mul_start : Bool) : KaratsubaState :=
  let ab : BitVec 33 × BitVec 33 :=
    match st.mph.1 with
    | 0 => (BitVec.ofNat 33 (st.opa.extractLsb' 0 32).toNat,
            BitVec.ofNat 33 (st.opb.extractLsb' 0 32).toNat)
    | 1 => (BitVec.ofNat 33 (st.opa.extractLsb' 32 32).toNat,
            BitVec.ofNat 33 (st.opb.extractLsb' 32 32).toNat)
    | _ => (st.sa, st.sb)
  let m_p := rtlMul33 ab.1 ab.2
  let use0 := st.mph.1 == 1
  let cx := if use0 then 0 else st.acc_s
  let cy := if use0 then 0 else st.acc_c
  let mr := rtlGl64Mrows st.preg st.mph
  let nsc := rtlCsa52 76 cx cy mr.1 mr.2.1 mr.2.2
  let sa_n := rtlPrefixAdd 33
    (BitVec.ofNat 33 (st.opa.extractLsb' 0 32).toNat)
    (BitVec.ofNat 33 (st.opa.extractLsb' 32 32).toNat) false
  let sb_n := rtlPrefixAdd 33
    (BitVec.ofNat 33 (st.opb.extractLsb' 0 32).toNat)
    (BitVec.ofNat 33 (st.opb.extractLsb' 32 32).toNat) false
  let in_mul := st.mph.1 != 0
  let acc_upd := in_mul && (st.mph.1 != 3)
  let preg_upd := (st.mph.1 == 0 && mul_start) || (st.mph.1 == 1) || (st.mph.1 == 2)
  let next_mph : Fin 4 :=
    match st.mph.1 with
    | 0 => if mul_start then ⟨1, by decide⟩ else ⟨0, by decide⟩
    | 1 => ⟨2, by decide⟩
    | 2 => ⟨3, by decide⟩
    | _ => ⟨0, by decide⟩
  { opa := st.opa
    opb := st.opb
    acc_s := if acc_upd then nsc.1 else st.acc_s
    acc_c := if acc_upd then nsc.2 else st.acc_c
    preg := if preg_upd then m_p else st.preg
    sa := if st.mph.1 == 0 && mul_start then sa_n else st.sa
    sb := if st.mph.1 == 0 && mul_start then sb_n else st.sb
    mph := next_mph }

private theorem rtlKaratsuba_four_cycle_aux (st₀ st₁ st₂ st₃ : KaratsubaState)
    (hIdle : st₀.mph = ⟨0, by decide⟩)
    (hst₁ : rtlKaratsubaStep st₀ true = st₁)
    (hst₂ : rtlKaratsubaStep st₁ false = st₂)
    (hst₃ : rtlKaratsubaStep st₂ false = st₃) :
    let (busy, last, cv) := rtlKaratsubaOutputs st₃
    busy = true ∧
    last = true ∧
    cv.toNat = (Goldilocks.mul (Goldilocks.ofNat st₀.opa.toNat) (Goldilocks.ofNat st₀.opb.toNat)).val := by
  dsimp only
  have hMph0Val : st₀.mph.1 = 0 := congrArg Fin.val hIdle
  have hMph1 : st₁.mph = ⟨1, by decide⟩ := by
    rw [← hst₁]; dsimp only [rtlKaratsubaStep]; rw [hMph0Val]; rfl
  have hMph1Val : st₁.mph.1 = 1 := congrArg Fin.val hMph1
  have hMph2 : st₂.mph = ⟨2, by decide⟩ := by
    rw [← hst₂]; dsimp only [rtlKaratsubaStep]; rw [hMph1Val]; rfl
  have hMph2Val : st₂.mph.1 = 2 := congrArg Fin.val hMph2
  have hMph3 : st₃.mph = ⟨3, by decide⟩ := by
    rw [← hst₃]; dsimp only [rtlKaratsubaStep]; rw [hMph2Val]; rfl
  have hMph3Val : st₃.mph.1 = 3 := congrArg Fin.val hMph3
  let a0 := (st₀.opa.extractLsb' 0 32).toNat
  let a1 := (st₀.opa.extractLsb' 32 32).toNat
  let b0 := (st₀.opb.extractLsb' 0 32).toNat
  let b1 := (st₀.opb.extractLsb' 32 32).toNat
  have ha0Lt : a0 < 4294967296 := (st₀.opa.extractLsb' 0 32).isLt
  have ha1Lt : a1 < 4294967296 := (st₀.opa.extractLsb' 32 32).isLt
  have hb0Lt : b0 < 4294967296 := (st₀.opb.extractLsb' 0 32).isLt
  have hb1Lt : b1 < 4294967296 := (st₀.opb.extractLsb' 32 32).isLt
  have haSplit : st₀.opa.toNat = a0 + 4294967296 * a1 := by
    dsimp only [a0, a1]
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one]
    have hDivLt : st₀.opa.toNat / 2 ^ 32 < 2 ^ 32 := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]; exact st₀.opa.isLt
    rw [Nat.mod_eq_of_lt hDivLt]
    exact (Nat.mod_add_div st₀.opa.toNat 4294967296).symm
  have hbSplit : st₀.opb.toNat = b0 + 4294967296 * b1 := by
    dsimp only [b0, b1]
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one]
    have hDivLt : st₀.opb.toNat / 2 ^ 32 < 2 ^ 32 := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]; exact st₀.opb.isLt
    rw [Nat.mod_eq_of_lt hDivLt]
    exact (Nat.mod_add_div st₀.opb.toNat 4294967296).symm
  -- Cycle 0 -> `st₁`:
  have hOpa1 : st₁.opa = st₀.opa := by rw [← hst₁]; rfl
  have hOpb1 : st₁.opb = st₀.opb := by rw [← hst₁]; rfl
  have hPreg1 : st₁.preg.toNat = a0 * b0 := by
    have hSt1Preg : st₁.preg = rtlMul33 (BitVec.ofNat 33 a0) (BitVec.ofNat 33 b0) := by
      rw [← hst₁]; dsimp only [rtlKaratsubaStep]; rw [hMph0Val]; rfl
    rw [hSt1Preg, rtlMul33_sound, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show a0 < 2 ^ 33 by change a0 < 8589934592; omega),
        Nat.mod_eq_of_lt (show b0 < 2 ^ 33 by change b0 < 8589934592; omega)]
  have hSa1 : st₁.sa.toNat = a0 + a1 := by
    have hSt1Sa : st₁.sa = rtlPrefixAdd 33 (BitVec.ofNat 33 a0) (BitVec.ofNat 33 a1) false := by
      rw [← hst₁]; dsimp only [rtlKaratsubaStep]; rw [hMph0Val]; rfl
    rw [hSt1Sa, rtlPrefixAdd_toNat, show false.toNat = 0 from rfl, Nat.add_zero,
        BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show a0 < 2 ^ 33 by change a0 < 8589934592; omega),
        Nat.mod_eq_of_lt (show a1 < 2 ^ 33 by change a1 < 8589934592; omega),
        Nat.mod_eq_of_lt (show a0 + a1 < 2 ^ 33 by change a0 + a1 < 8589934592; omega)]
  have hSb1 : st₁.sb.toNat = b0 + b1 := by
    have hSt1Sb : st₁.sb = rtlPrefixAdd 33 (BitVec.ofNat 33 b0) (BitVec.ofNat 33 b1) false := by
      rw [← hst₁]; dsimp only [rtlKaratsubaStep]; rw [hMph0Val]; rfl
    rw [hSt1Sb, rtlPrefixAdd_toNat, show false.toNat = 0 from rfl, Nat.add_zero,
        BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show b0 < 2 ^ 33 by change b0 < 8589934592; omega),
        Nat.mod_eq_of_lt (show b1 < 2 ^ 33 by change b1 < 8589934592; omega),
        Nat.mod_eq_of_lt (show b0 + b1 < 2 ^ 33 by change b0 + b1 < 8589934592; omega)]
  -- Cycle 1 -> `st₂`:
  let z0 := a0 * b0
  let z0_lo := z0 % 4294967296
  let z0_hi := z0 / 4294967296
  have hz0Lt : z0 < 18446744073709551616 :=
    Nat.lt_of_lt_of_eq (Nat.mul_lt_mul'' ha0Lt hb0Lt) (by decide)
  have hz0LoLt : z0_lo < 4294967296 := Nat.mod_lt _ (by decide)
  have hz0HiLt : z0_hi < 4294967296 := by dsimp only [z0_hi]; omega
  have hz0Decomp : z0 = z0_lo + 4294967296 * z0_hi := (Nat.mod_add_div z0 4294967296).symm
  let acc2Val := (2 * (goldilocksPrime - 1) + z0) - (4294967296 * z0_lo + 4294967295 * z0_hi)
  have hAcc2Le : 4294967296 * z0_lo + 4294967295 * z0_hi ≤ 2 * (goldilocksPrime - 1) + z0 := by
    clear haSplit hbSplit hPreg1 hz0Decomp; unfold goldilocksPrime; omega
  have hAcc2Cast : (acc2Val : Int) =
      2 * ((goldilocksPrime : Int) - 1) + (z0 : Int) -
      (4294967296 * (z0_lo : Int) + 4294967295 * (z0_hi : Int)) := by
    dsimp only [acc2Val]
    have hp1 : 1 ≤ goldilocksPrime := by decide
    rw [int_natCast_sub hAcc2Le]
    simp only [Int.natCast_add, Int.natCast_mul, int_natCast_sub hp1]
    clear haSplit hbSplit hPreg1 hz0Decomp hAcc2Le hp1; omega
  have hAcc2 : st₂.acc_s.toNat + st₂.acc_c.toNat = acc2Val := by
    let m1_1 : BitVec 76 := BitVec.ofNat 76 (st₁.preg.extractLsb' 0 64).toNat
    let m1_2 : BitVec 76 := BitVec.ofNat 76
      ((2 ^ 32 - 1 - (st₁.preg.extractLsb' 0 32).toNat) * 2 ^ 32 + (st₁.preg.extractLsb' 32 32).toNat)
    let m1_3 : BitVec 76 := BitVec.ofNat 76 ((2 ^ 32 - 1 - (st₁.preg.extractLsb' 32 32).toNat) * 2 ^ 32)
    have hSt2AccS : st₂.acc_s = (rtlCsa52 76 0 0 m1_1 m1_2 m1_3).1 := by
      rw [← hst₂]; dsimp only [rtlKaratsubaStep, rtlGl64Mrows]; rw [hMph1Val]; rfl
    have hSt2AccC : st₂.acc_c = (rtlCsa52 76 0 0 m1_1 m1_2 m1_3).2 := by
      rw [← hst₂]; dsimp only [rtlKaratsubaStep, rtlGl64Mrows]; rw [hMph1Val]; rfl
    have hm1_1 : m1_1.toNat = z0 := by
      dsimp only [m1_1]
      rw [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, hPreg1]
      have hz0Lt64 : z0 < 2 ^ 64 := hz0Lt
      have hz0Lt76 : z0 < 2 ^ 76 := by clear hAcc2Cast; change z0 < 75557863725914323419136; omega
      rw [Nat.mod_eq_of_lt hz0Lt64, Nat.mod_eq_of_lt hz0Lt76]
    have hm1_2 : m1_2.toNat = (4294967295 - z0_lo) * 4294967296 + z0_hi := by
      dsimp only [m1_2]; rw [BitVec.toNat_ofNat]
      simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one, hPreg1]
      change (((4294967295 - z0_lo) * 4294967296 + z0_hi % 4294967296) %
        75557863725914323419136) = _
      rw [Nat.mod_eq_of_lt hz0HiLt]
      exact Nat.mod_eq_of_lt (by clear hAcc2Cast hz0Decomp; omega)
    have hm1_3 : m1_3.toNat = (4294967295 - z0_hi) * 4294967296 := by
      dsimp only [m1_3]; rw [BitVec.toNat_ofNat]
      simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, hPreg1]
      change (((4294967295 - z0_hi % 4294967296) * 4294967296) %
        75557863725914323419136) = _
      rw [Nat.mod_eq_of_lt hz0HiLt]
      exact Nat.mod_eq_of_lt (by clear hAcc2Cast hz0Decomp; omega)
    rw [hSt2AccS, hSt2AccC, rtlCsa52_exact]
    · change 0 + 0 + m1_1.toNat + m1_2.toNat + m1_3.toNat = acc2Val
      rw [hm1_1, hm1_2, hm1_3]
      apply nat_eq_of_int_eq
      have s1 : z0_lo ≤ 4294967295 := by clear hAcc2Cast; omega
      have s2 : z0_hi ≤ 4294967295 := by clear hAcc2Cast; omega
      simp only [Int.natCast_add, Int.natCast_mul, int_natCast_sub s1, int_natCast_sub s2, hAcc2Cast]
      clear haSplit hbSplit hm1_1 hm1_2 hm1_3 hSt2AccS hSt2AccC hPreg1 hAcc2Le hz0Decomp s1 s2
      unfold goldilocksPrime
      omega
    · change 0 + 0 + m1_1.toNat + m1_2.toNat + m1_3.toNat < 75557863725914323419136
      rw [hm1_1, hm1_2, hm1_3]
      apply nat_lt_of_int_lt
      have s1 : z0_lo ≤ 4294967295 := by clear hAcc2Cast; omega
      have s2 : z0_hi ≤ 4294967295 := by clear hAcc2Cast; omega
      simp only [Int.natCast_add, Int.natCast_mul, int_natCast_sub s1, int_natCast_sub s2]
      clear haSplit hbSplit hm1_1 hm1_2 hm1_3 hSt2AccS hSt2AccC hPreg1 hAcc2Le hAcc2Cast hz0Decomp s1 s2
      omega
  have hPreg2 : st₂.preg.toNat = a1 * b1 := by
    have hSt2Preg : st₂.preg = rtlMul33 (BitVec.ofNat 33 a1) (BitVec.ofNat 33 b1) := by
      rw [← hst₂]; dsimp only [rtlKaratsubaStep]; rw [hMph1Val, hOpa1, hOpb1]; rfl
    rw [hSt2Preg, rtlMul33_sound, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show a1 < 2 ^ 33 by clear hAcc2Cast; change a1 < 8589934592; omega),
        Nat.mod_eq_of_lt (show b1 < 2 ^ 33 by clear hAcc2Cast; change b1 < 8589934592; omega)]
  have hSa2 : st₂.sa = st₁.sa := by rw [← hst₂]; dsimp only [rtlKaratsubaStep]; rw [hMph1Val]; rfl
  have hSb2 : st₂.sb = st₁.sb := by rw [← hst₂]; dsimp only [rtlKaratsubaStep]; rw [hMph1Val]; rfl
  -- Cycle 2 -> `st₃`:
  let z2 := a1 * b1
  have hz2Lt : z2 < 18446744073709551616 :=
    Nat.lt_of_lt_of_eq (Nat.mul_lt_mul'' ha1Lt hb1Lt) (by decide)
  let acc3Add := 2 * goldilocksPrime - 4294967296 - z2
  have hAcc3AddCast : (acc3Add : Int) = 2 * (goldilocksPrime : Int) - 4294967296 - (z2 : Int) := by
    dsimp only [acc3Add]
    have s0 : 4294967296 ≤ 2 * goldilocksPrime := by decide
    have s1 : z2 ≤ 2 * goldilocksPrime - 4294967296 := by
      clear haSplit hbSplit hAcc2 hAcc2Le hAcc2Cast hz0Decomp; unfold goldilocksPrime; omega
    rw [int_natCast_sub s1, int_natCast_sub s0, Int.natCast_mul]
    clear haSplit hbSplit hAcc2 hAcc2Le hAcc2Cast hz0Decomp s0 s1; omega
  have hAcc3 : st₃.acc_s.toNat + st₃.acc_c.toNat =
      (st₂.acc_s.toNat + st₂.acc_c.toNat) + acc3Add := by
    let m2_1 : BitVec 76 := BitVec.ofNat 76 (2 ^ 64 - 1 - (st₂.preg.extractLsb' 0 64).toNat)
    let m2_2 : BitVec 76 := BitVec.ofNat 76 (goldilocksPrime - 2 ^ 33 + 2)
    have hSt3AccS : st₃.acc_s = (rtlCsa52 76 st₂.acc_s st₂.acc_c m2_1 m2_2 0).1 := by
      rw [← hst₃]; dsimp only [rtlKaratsubaStep, rtlGl64Mrows]; rw [hMph2Val]; rfl
    have hSt3AccC : st₃.acc_c = (rtlCsa52 76 st₂.acc_s st₂.acc_c m2_1 m2_2 0).2 := by
      rw [← hst₃]; dsimp only [rtlKaratsubaStep, rtlGl64Mrows]; rw [hMph2Val]; rfl
    have hm2_1 : m2_1.toNat = 18446744073709551615 - z2 := by
      dsimp only [m2_1]
      rw [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, hPreg2]
      have hz2Lt64 : z2 < 2 ^ 64 := hz2Lt
      rw [Nat.mod_eq_of_lt hz2Lt64]
      change (18446744073709551615 - z2) % 75557863725914323419136 = _
      exact Nat.mod_eq_of_lt (by clear hAcc2 hAcc2Le hAcc2Cast hAcc3AddCast hz0Decomp; omega)
    have hm2_2 : m2_2.toNat = goldilocksPrime - 8589934592 + 2 := by decide
    rw [hSt3AccS, hSt3AccC, rtlCsa52_exact]
    · change st₂.acc_s.toNat + st₂.acc_c.toNat + m2_1.toNat + m2_2.toNat + 0 =
        (st₂.acc_s.toNat + st₂.acc_c.toNat) + acc3Add
      rw [hm2_1, hm2_2]
      apply nat_eq_of_int_eq
      have sz2 : z2 ≤ 18446744073709551615 := by clear hAcc2Cast hAcc3AddCast; omega
      have sp : 8589934592 ≤ goldilocksPrime := by decide
      simp only [Int.natCast_add, int_natCast_sub sz2, int_natCast_sub sp, hAcc3AddCast]
      clear haSplit hbSplit hm2_1 hm2_2 hSt3AccS hSt3AccC hPreg1 hPreg2 hAcc2 hAcc2Le hAcc2Cast hz0Decomp sz2 sp
      unfold goldilocksPrime
      omega
    · change st₂.acc_s.toNat + st₂.acc_c.toNat + m2_1.toNat + m2_2.toNat + 0 < 75557863725914323419136
      rw [hAcc2, hm2_1, hm2_2]
      apply nat_lt_of_int_lt
      have sz2 : z2 ≤ 18446744073709551615 := by clear hAcc2Cast hAcc3AddCast; omega
      have sp : 8589934592 ≤ goldilocksPrime := by decide
      simp only [Int.natCast_add, int_natCast_sub sz2, int_natCast_sub sp, hAcc2Cast]
      clear haSplit hbSplit hm2_1 hm2_2 hSt3AccS hSt3AccC hPreg1 hPreg2 hAcc2 hAcc2Le hAcc3AddCast hz0Decomp sz2 sp
      unfold goldilocksPrime
      omega
  have hPreg3 : st₃.preg.toNat = (a0 + a1) * (b0 + b1) := by
    have hSt3Preg : st₃.preg = rtlMul33 st₁.sa st₁.sb := by
      rw [← hst₃]; dsimp only [rtlKaratsubaStep]; rw [hMph2Val, hSa2, hSb2]; rfl
    rw [hSt3Preg, rtlMul33_sound, hSa1, hSb1]
  -- Phase 3 combinational outputs (`rtlKaratsubaOutputs st₃`):
  unfold rtlKaratsubaOutputs rtlGl64Mrows
  dsimp only
  rw [hMph3Val]
  refine ⟨rfl, rfl, ?_⟩
  let zm := (a0 + a1) * (b0 + b1)
  have hzmLt : zm < 4 * 18446744073709551616 := by
    have hsa : a0 + a1 < 8589934592 := by clear hAcc2 hAcc3 hAcc2Cast hAcc3AddCast; omega
    have hsb : b0 + b1 < 8589934592 := by clear hAcc2 hAcc3 hAcc2Cast hAcc3AddCast; omega
    exact Nat.lt_of_lt_of_eq (Nat.mul_lt_mul'' hsa hsb) (by decide)
  let zm_lo := zm % 4294967296
  let zm_hi := (zm / 4294967296) % 4294967296
  let zm_m2 := zm / 18446744073709551616
  have hzmLoLt : zm_lo < 4294967296 := Nat.mod_lt _ (by decide)
  have hzmHiLt : zm_hi < 4294967296 := Nat.mod_lt _ (by decide)
  have hzmM2Le3 : zm_m2 ≤ 3 := by
    clear haSplit hbSplit hAcc2 hAcc3 hAcc2Cast hAcc3AddCast hz0Decomp; dsimp only [zm_m2]; omega
  have hzmDecomp : zm = zm_lo + 4294967296 * zm_hi + 18446744073709551616 * zm_m2 := by
    clear haSplit hbSplit hAcc2 hAcc3 hAcc2Cast hAcc3AddCast hz0Decomp
    dsimp only [zm_lo, zm_hi, zm_m2]
    have d0 := Nat.mod_add_div zm 4294967296
    have d1 := Nat.mod_add_div (zm / 4294967296) 4294967296
    have h64 : (zm / 4294967296) / 4294967296 = zm / 18446744073709551616 := by
      rw [Nat.div_div_eq_div_mul]
    rw [h64] at d1; omega
  let m3_1 : BitVec 76 := BitVec.ofNat 76
    ((st₃.preg.extractLsb' 0 32).toNat * 2 ^ 32 + (2 ^ 32 - 1 - (st₃.preg.extractLsb' 32 32).toNat))
  let m3_2 : BitVec 76 := BitVec.ofNat 76
    ((st₃.preg.extractLsb' 32 32).toNat * 2 ^ 32 + (3 - (st₃.preg.extractLsb' 64 2).toNat))
  change (rtlGl64Canon (rtlCsa52 76 st₃.acc_s st₃.acc_c m3_1 m3_2 0).1
      (rtlCsa52 76 st₃.acc_s st₃.acc_c m3_1 m3_2 0).2).toNat = _
  have hm3_1Val : m3_1.toNat = zm_lo * 4294967296 + (4294967295 - zm_hi) := by
    dsimp only [m3_1]; rw [BitVec.toNat_ofNat]
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one, hPreg3]
    change (zm_lo * 4294967296 + (4294967295 - zm_hi)) % 75557863725914323419136 = _
    exact Nat.mod_eq_of_lt (by clear haSplit hbSplit hAcc2 hAcc3 hAcc2Cast hAcc3AddCast hz0Decomp hzmDecomp; omega)
  have hm3_2Val : m3_2.toNat = zm_hi * 4294967296 + (3 - zm_m2) := by
    dsimp only [m3_2]; rw [BitVec.toNat_ofNat]
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, hPreg3]
    change (zm_hi * 4294967296 + (3 - zm_m2 % 4)) % 75557863725914323419136 = _
    rw [Nat.mod_eq_of_lt (show zm_m2 < 4 by clear hAcc2 hAcc3 hAcc2Cast hAcc3AddCast; omega)]
    exact Nat.mod_eq_of_lt (by clear haSplit hbSplit hAcc2 hAcc3 hAcc2Cast hAcc3AddCast hz0Decomp hzmDecomp; omega)
  have hFinalSumLt76 : st₃.acc_s.toNat + st₃.acc_c.toNat + m3_1.toNat + m3_2.toNat + (0#76).toNat < 2 ^ 76 := by
    change st₃.acc_s.toNat + st₃.acc_c.toNat + m3_1.toNat + m3_2.toNat + 0 < 75557863725914323419136
    rw [hAcc3, hAcc2, hm3_1Val, hm3_2Val]
    apply nat_lt_of_int_lt
    have sm1 : zm_hi ≤ 4294967295 := by clear hAcc2 hAcc3 hAcc2Cast hAcc3AddCast; omega
    have sm2 : zm_m2 ≤ 3 := hzmM2Le3
    rw [Int.natCast_add, Int.natCast_add, Int.natCast_add, Int.natCast_add, hAcc2Cast, hAcc3AddCast]
    simp only [Int.natCast_add, Int.natCast_mul, int_natCast_sub sm1, int_natCast_sub sm2]
    clear haSplit hbSplit hAcc3 hAcc2 hm3_1Val hm3_2Val hAcc2Le hAcc2Cast hAcc3AddCast
      hPreg1 hPreg2 hPreg3 hz0Decomp hzmDecomp sm1 sm2
    unfold goldilocksPrime
    omega
  have hCsaFinal := rtlCsa52_exact st₃.acc_s st₃.acc_c m3_1 m3_2 0 hFinalSumLt76
  rw [rtlGl64Canon_sound _ _ (by rw [hCsaFinal]; exact hFinalSumLt76),
      hCsaFinal, hAcc3, hAcc2, hm3_1Val, hm3_2Val,
      Goldilocks.mul_val, Goldilocks.ofNat_val, Goldilocks.ofNat_val,
      Nat.mod_mul_mod, Nat.mul_mod_mod]
  have hKara : st₀.opa.toNat * st₀.opb.toNat + 4294967296 * (z0 + z2) =
      z0 + 4294967296 * zm + 18446744073709551616 * z2 := by
    rw [haSplit, hbSplit]
    exact karatsuba_split32_identity a0 a1 b0 b1
  let S_total := (acc2Val + acc3Add) +
      (zm_lo * 4294967296 + (4294967295 - zm_hi)) + (zm_hi * 4294967296 + (3 - zm_m2)) + 0
  change S_total % goldilocksPrime = (st₀.opa.toNat * st₀.opb.toNat) % goldilocksPrime
  generalize st₀.opa.toNat * st₀.opb.toNat = prodAB at hKara ⊢
  have hCongr : S_total + goldilocksPrime * (z2 + zm_hi + 4294967297 * zm_m2) =
      prodAB + goldilocksPrime * (4 + z0_hi) := by
    dsimp only [S_total]
    apply nat_eq_of_int_eq
    have sm1 : zm_hi ≤ 4294967295 := by clear hAcc2 hAcc3 hAcc2Cast hAcc3AddCast; omega
    have sm2 : zm_m2 ≤ 3 := hzmM2Le3
    rw [Int.natCast_add, Int.natCast_add, Int.natCast_add, Int.natCast_add, Int.natCast_add,
        hAcc2Cast, hAcc3AddCast]
    simp only [Int.natCast_add, Int.natCast_mul, int_natCast_sub sm1, int_natCast_sub sm2]
    clear haSplit hbSplit hAcc2 hAcc3 hm3_1Val hm3_2Val hFinalSumLt76 hCsaFinal hAcc2Le
      hAcc2Cast hAcc3AddCast hPreg1 hPreg2 hPreg3 sm1 sm2
    unfold goldilocksPrime at *
    omega
  have hModSides := congrArg (· % goldilocksPrime) hCongr
  rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left] at hModSides
  exact hModSides

/-- **End-to-End 4-Cycle ASIC `Dregg-180` Booth-Karatsuba-CSA Theorem (`rtlKaratsuba_four_cycle_mul_sound`)**:
    Starting in idle `mph = 0` with arbitrary `opa, opb : BitVec 64` (and arbitrary prior accumulator
    contents!), pulsing `mul_start = true` and clocking 3 pipeline cycles (`mph = 1 → 2 → 3`)
    reaches `mul_last = true` with `cv.toNat = (Goldilocks.mul (Goldilocks.ofNat opa.toNat) (Goldilocks.ofNat opb.toNat)).val`! -/
theorem rtlKaratsuba_four_cycle_mul_sound (st₀ : KaratsubaState) (hIdle : st₀.mph = ⟨0, by decide⟩) :
    let st₁ := rtlKaratsubaStep st₀ true
    let st₂ := rtlKaratsubaStep st₁ false
    let st₃ := rtlKaratsubaStep st₂ false
    let (busy, last, cv) := rtlKaratsubaOutputs st₃
    busy = true ∧
    last = true ∧
    cv.toNat = (Goldilocks.mul (Goldilocks.ofNat st₀.opa.toNat) (Goldilocks.ofNat st₀.opb.toNat)).val :=
  rtlKaratsuba_four_cycle_aux st₀ _ _ _ hIdle rfl rfl rfl

/-! ## 6. Mutation-Kill Teeth & Inhabitedness Witnesses -/

/-- **Tooth (`tooth_fpga_wrong_c_bias_corrupts_residue`)**:
    Mutating `C_BIAS` in `qsag_gl64_reduce.sv:19` from `GL_P + 3` to `GL_P + 2` produces an
    off-by-one corrupted residue on `x = 1`! -/
theorem tooth_fpga_wrong_c_bias_corrupts_residue :
    (rtlFpgaGl64Stage2
      (rtlFpgaGl64Stage1 (BitVec.ofNat 66 (goldilocksPrime + 2)) (BitVec.ofNat 136 1))).toNat ≠
    (rtlFpgaGl64Reduce (BitVec.ofNat 136 1)).toNat := by
  rw [rtlFpgaGl64Reduce_sound (BitVec.ofNat 136 1)]
  have hx1 : (BitVec.ofNat 136 1).toNat = 1 := rfl
  have hGood : (Goldilocks.ofNat (BitVec.ofNat 136 1).toNat).val = 1 := by
    rw [Goldilocks.ofNat_val, hx1]
    unfold goldilocksPrime; omega
  rw [hGood]
  let vqBad := rtlFpgaGl64Stage1 (BitVec.ofNat 66 (goldilocksPrime + 2)) (BitVec.ofNat 136 1)
  have hP66 : 2 ^ 66 = 73786976294838206464 := by decide
  have hP67 : 2 ^ 67 = 147573952589676412928 := by decide
  have hBadStage1 : vqBad.toNat = goldilocksPrime := by
    dsimp only [vqBad]
    unfold rtlFpgaGl64Stage1
    dsimp only
    rw [rtlAddSplit3Chunk_toNat (by decide), rtlCsaReduce2_mod]
    dsimp only [List.map]
    rw [List.sum_cons, List.sum_cons, List.sum_cons, List.sum_cons, List.sum_cons, List.sum_cons,
        List.sum_nil]
    have hEx0 : ((BitVec.ofNat 136 1).extractLsb' 0 64).toNat = 1 := rfl
    have hEx64 : ((BitVec.ofNat 136 1).extractLsb' 64 32).toNat = 0 := rfl
    have hEx96 : ((BitVec.ofNat 136 1).extractLsb' 96 32).toNat = 0 := rfl
    have hEx128 : ((BitVec.ofNat 136 1).extractLsb' 128 8).toNat = 0 := rfl
    rw [hEx0, hEx64, hEx96, hEx128]
    decide
  have hBadStage2 : (rtlFpgaGl64Stage2 vqBad).toNat = 0 := by
    unfold rtlFpgaGl64Stage2
    dsimp only
    let v1 := rtlAddSplit3Chunk 67 24 (BitVec.ofNat 67 vqBad.toNat) (BitVec.ofNat 67 (2 ^ 67 - goldilocksPrime))
    let v2 := rtlAddSplit3Chunk 67 24 (BitVec.ofNat 67 vqBad.toNat) (BitVec.ofNat 67 (2 ^ 67 - 2 * goldilocksPrime))
    have hv1Zero : v1.toNat = 0 := by
      dsimp only [v1]
      rw [rtlAddSplit3Chunk_toNat (by decide), BitVec.toNat_ofNat, BitVec.toNat_ofNat, hBadStage1, hP67]
      unfold goldilocksPrime; omega
    have hv2Val : v2.toNat = 147573952589676412928 - goldilocksPrime := by
      dsimp only [v2]
      rw [rtlAddSplit3Chunk_toNat (by decide), BitVec.toNat_ofNat, BitVec.toNat_ofNat, hBadStage1, hP67]
      unfold goldilocksPrime; omega
    have hv2Bit : v2.getLsbD 66 = true := by
      rw [BitVec.getLsbD, hv2Val, Nat.testBit_eq_decide_div_mod_eq, hP66]
      unfold goldilocksPrime; decide
    have hv1Bit : v1.getLsbD 66 = false := by
      simp only [BitVec.getLsbD, hv1Zero, Nat.zero_testBit]
    change (rtlFpgaGl64Mux vqBad v1 v2).toNat = 0
    unfold rtlFpgaGl64Mux
    rw [hv2Bit, hv1Bit, Bool.not_true, ite_neg Bool.false_ne_true,
        Bool.not_false, ite_pos rfl, BitVec.extractLsb'_toNat, hv1Zero,
        Nat.shiftRight_zero, Nat.zero_mod]
  change (rtlFpgaGl64Stage2 vqBad).toNat ≠ 1
  rw [hBadStage2]
  omega

theorem inhabited_karatsuba_mul :
    ∃ st₀ : KaratsubaState,
      st₀.mph = ⟨0, by decide⟩ ∧
      (rtlKaratsubaOutputs (rtlKaratsubaStep (rtlKaratsubaStep (rtlKaratsubaStep st₀ true) false) false)).1 = true := by
  let st₀ : KaratsubaState :=
    { opa := BitVec.ofNat 64 (goldilocksPrime - 1)
      opb := BitVec.ofNat 64 (goldilocksPrime - 1)
      acc_s := 0, acc_c := 0, preg := 0, sa := 0, sb := 0, mph := ⟨0, by decide⟩ }
  exact ⟨st₀, rfl, (rtlKaratsuba_four_cycle_mul_sound st₀ rfl).1⟩

#verify_constructive
  Qsag.Silicon.rtlCsa32_mod
  Qsag.Silicon.rtlCsa32_exact
  Qsag.Silicon.rtlCsa52_exact
  Qsag.Silicon.rtlCsaReduce2_mod
  Qsag.Silicon.rtlPrefixAdd_toNat
  Qsag.Silicon.rtlAddSplit3Chunk_toNat
  Qsag.Silicon.rtlFpgaGl64Reduce_sound
  Qsag.Silicon.rtlFpgaGl64Step_two_clocks
  Qsag.Silicon.rtlGl64Canon_sound
  Qsag.Silicon.rtlMul33_sound
  Qsag.Silicon.rtlGl64SqPipe_sound
  Qsag.Silicon.rtlKaratsuba_four_cycle_mul_sound
  Qsag.Silicon.tooth_fpga_wrong_c_bias_corrupts_residue
  Qsag.Silicon.inhabited_karatsuba_mul

#tooth_pair
  Qsag.Silicon.rtlFpgaGl64Reduce_sound
  vs
  Qsag.Silicon.tooth_fpga_wrong_c_bias_corrupts_residue

#verify_inhabited
  Qsag.Silicon.rtlKaratsuba_four_cycle_mul_sound
  Qsag.Silicon.inhabited_karatsuba_mul

end Qsag.Silicon
end
