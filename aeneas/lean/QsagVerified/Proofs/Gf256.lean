module

public import QsagVerified.Funs
import all QsagVerified.Funs

public section

namespace qsag_verified.proofs

open Aeneas Aeneas.Std Result ControlFlow Error
open qsag_verified

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

attribute [-simp] BitVec.getLsbD_eq_getElem
attribute [local simp] UScalar.val UScalarTy.numBits

/-! ## Wiedemann binary-field arithmetic -/

private def bv8Pack (b7 b6 b5 b4 b3 b2 b1 b0 : Bool) : BitVec 8 :=
  BitVec.cons b7 (BitVec.cons b6 (BitVec.cons b5 (BitVec.cons b4
    (BitVec.cons b3 (BitVec.cons b2 (BitVec.cons b1 (BitVec.cons b0 BitVec.nil)))))))

private theorem bv8_eq_pack (bv : BitVec 8) :
    bv = bv8Pack (bv.getLsbD 7) (bv.getLsbD 6) (bv.getLsbD 5) (bv.getLsbD 4)
                 (bv.getLsbD 3) (bv.getLsbD 2) (bv.getLsbD 1) (bv.getLsbD 0) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  change i < 8 at hi
  match i, hi with
  | 0, _ => dsimp only [bv8Pack]; simp [BitVec.getLsbD_cons]
  | 1, _ => dsimp only [bv8Pack]; simp [BitVec.getLsbD_cons]
  | 2, _ => dsimp only [bv8Pack]; simp [BitVec.getLsbD_cons]
  | 3, _ => dsimp only [bv8Pack]; simp [BitVec.getLsbD_cons]
  | 4, _ => dsimp only [bv8Pack]; simp [BitVec.getLsbD_cons]
  | 5, _ => dsimp only [bv8Pack]; simp [BitVec.getLsbD_cons]
  | 6, _ => dsimp only [bv8Pack]; simp [BitVec.getLsbD_cons]
  | 7, _ => dsimp only [bv8Pack]; simp [BitVec.getLsbD_cons]
  | n + 8, hi => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 8 n) hi)

@[expose]
def pureMulT1 (a b : Std.U8) : Std.U8 :=
  let a_lo := a &&& 1#u8
  let a_hi := ⟨a.bv >>> 1⟩ &&& 1#u8
  let b_lo := b &&& 1#u8
  let b_hi := ⟨b.bv >>> 1⟩ &&& 1#u8
  let p := a_lo &&& b_lo
  let q := a_hi &&& b_hi
  let r := (a_lo ^^^ a_hi) &&& (b_lo ^^^ b_hi)
  (p ^^^ q) ||| ⟨(r ^^^ p).bv <<< 1⟩

@[expose]
def pureScaleXT1 (a : Std.U8) : Std.U8 :=
  let lo := a &&& 1#u8
  let hi := ⟨a.bv >>> 1⟩ &&& 1#u8
  hi ||| ⟨(lo ^^^ hi).bv <<< 1⟩

@[expose]
def pureMulT2 (a b : Std.U8) : Std.U8 :=
  let a_lo := a &&& 3#u8
  let a_hi := ⟨a.bv >>> 2⟩ &&& 3#u8
  let b_lo := b &&& 3#u8
  let b_hi := ⟨b.bv >>> 2⟩ &&& 3#u8
  let p := pureMulT1 a_lo b_lo
  let q := pureMulT1 a_hi b_hi
  let r := pureMulT1 (a_lo ^^^ a_hi) (b_lo ^^^ b_hi)
  let hi := ((r ^^^ p) ^^^ q) ^^^ pureScaleXT1 q
  (p ^^^ q) ||| ⟨hi.bv <<< 2⟩

@[expose]
def pureScaleXT2 (a : Std.U8) : Std.U8 :=
  let lo := a &&& 3#u8
  let hi := ⟨a.bv >>> 2⟩ &&& 3#u8
  hi ||| ⟨(lo ^^^ pureScaleXT1 hi).bv <<< 2⟩

@[expose]
def pureGf256Mul (a b : Std.U8) : Std.U8 :=
  let a_lo := a &&& 15#u8
  let a_hi := ⟨a.bv >>> 4⟩ &&& 15#u8
  let b_lo := b &&& 15#u8
  let b_hi := ⟨b.bv >>> 4⟩ &&& 15#u8
  let p := pureMulT2 a_lo b_lo
  let q := pureMulT2 a_hi b_hi
  let r := pureMulT2 (a_lo ^^^ a_hi) (b_lo ^^^ b_hi)
  let hi := ((r ^^^ p) ^^^ q) ^^^ pureScaleXT2 q
  (p ^^^ q) ||| ⟨hi.bv <<< 4⟩

theorem gf256_mul_eq_pure (a b : tower.Gf256) :
    tower.gf256_mul a b = .ok (pureGf256Mul a b) := by rfl

@[expose]
def pureGf256Inv (a : Std.U8) : Std.U8 :=
  let a2 := pureGf256Mul a a
  let a4 := pureGf256Mul a2 a2
  let a6 := pureGf256Mul a4 a2
  let a8 := pureGf256Mul a4 a4
  let a14 := pureGf256Mul a8 a6
  let a16 := pureGf256Mul a8 a8
  let a32 := pureGf256Mul a16 a16
  let a64 := pureGf256Mul a32 a32
  let a128 := pureGf256Mul a64 a64
  pureGf256Mul (pureGf256Mul (pureGf256Mul a128 a64)
    (pureGf256Mul a32 a16)) a14

theorem gf256_inv_or_zero_eq_pure (a : Std.U8) :
    tower.gf256_inv_or_zero a = .ok (pureGf256Inv a) := by
  unfold tower.gf256_inv_or_zero pureGf256Inv
  dsimp only
  simp only [gf256_mul_eq_pure, bind_eq_result_bind, result_bind_ok]

private theorem bv_or_shift_xor {w : Nat} (p1 p2 h1 h2 : BitVec w) (s : Nat)
    (hp1 : ∀ i, s ≤ i → p1.getLsbD i = false)
    (hp2 : ∀ i, s ≤ i → p2.getLsbD i = false) :
    (p1 ||| (h1 <<< s)) ^^^ (p2 ||| (h2 <<< s)) = (p1 ^^^ p2) ||| ((h1 ^^^ h2) <<< s) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  by_cases hs : i < s
  · simp [hs]
  · have hge : s ≤ i := Nat.le_of_not_gt hs
    have e1 : p1.getLsbD i = false := hp1 i hge
    have e2 : p2.getLsbD i = false := hp2 i hge
    simp [hs, hi, e1, e2]

private theorem pureMulT1_mask (a b : Std.U8) :
    pureMulT1 a b = pureMulT1 (a &&& 3#u8) (b &&& 3#u8) := by
  apply UScalar.ext
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  change i < 8 at hi
  have ha0 : a.bv.getLsbD 0 = (a &&& 3#u8).bv.getLsbD 0 := by simp [UScalar.bv_and]
  have ha1 : a.bv.getLsbD 1 = (a &&& 3#u8).bv.getLsbD 1 := by simp [UScalar.bv_and]
  have hb0 : b.bv.getLsbD 0 = (b &&& 3#u8).bv.getLsbD 0 := by simp [UScalar.bv_and]
  have hb1 : b.bv.getLsbD 1 = (b &&& 3#u8).bv.getLsbD 1 := by simp [UScalar.bv_and]
  unfold pureMulT1
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp [UScalar.bv_and, UScalar.bv_xor, UScalar.bv_or]
  | n + 8, hi => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 8 n) hi)

private theorem pureScaleXT1_mask (a : Std.U8) :
    pureScaleXT1 a = pureScaleXT1 (a &&& 3#u8) := by
  apply UScalar.ext
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  change i < 8 at hi
  unfold pureScaleXT1
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp [UScalar.bv_and, UScalar.bv_xor, UScalar.bv_or]
  | n + 8, hi => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 8 n) hi)

private def bv2Pack (b1 b0 : Bool) : Std.U8 :=
  ⟨bv8Pack false false false false false false b1 b0⟩

private theorem mask3_eq_bv2Pack (a : Std.U8) :
    (a &&& 3#u8) = bv2Pack (a.bv.getLsbD 1) (a.bv.getLsbD 0) := by
  apply UScalar.ext
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  change i < 8 at hi
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp [bv2Pack, bv8Pack, BitVec.getLsbD_cons, UScalar.bv_and]
  | n + 8, hi => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 8 n) hi)

private theorem pureMulT1_comm (a b : Std.U8) : pureMulT1 a b = pureMulT1 b a := by
  rw [pureMulT1_mask a b, pureMulT1_mask b a, mask3_eq_bv2Pack a, mask3_eq_bv2Pack b]
  generalize a.bv.getLsbD 1 = a1; generalize a.bv.getLsbD 0 = a0
  generalize b.bv.getLsbD 1 = b1; generalize b.bv.getLsbD 0 = b0
  cases a1 <;> cases a0 <;> cases b1 <;> cases b0 <;> rfl

private theorem pureMulT1_xor_right (a b c : Std.U8) :
    pureMulT1 a (b ^^^ c) = pureMulT1 a b ^^^ pureMulT1 a c := by
  have hbc : ((b ^^^ c) &&& 3#u8) = ((b &&& 3#u8) ^^^ (c &&& 3#u8)) := by
    apply UScalar.ext; apply BitVec.eq_of_getLsbD_eq; intro i hi
    change i < 8 at hi
    match i, hi with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
      simp [UScalar.bv_and, UScalar.bv_xor]
    | n + 8, hi => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 8 n) hi)
  rw [pureMulT1_mask a (b ^^^ c), hbc, pureMulT1_mask a b, pureMulT1_mask a c,
      mask3_eq_bv2Pack a, mask3_eq_bv2Pack b, mask3_eq_bv2Pack c]
  generalize a.bv.getLsbD 1 = a1; generalize a.bv.getLsbD 0 = a0
  generalize b.bv.getLsbD 1 = b1; generalize b.bv.getLsbD 0 = b0
  generalize c.bv.getLsbD 1 = c1; generalize c.bv.getLsbD 0 = c0
  cases a1 <;> cases a0 <;> cases b1 <;> cases b0 <;> cases c1 <;> cases c0 <;> rfl

private theorem pureScaleXT1_xor (a b : Std.U8) :
    pureScaleXT1 (a ^^^ b) = pureScaleXT1 a ^^^ pureScaleXT1 b := by
  have hab : ((a ^^^ b) &&& 3#u8) = ((a &&& 3#u8) ^^^ (b &&& 3#u8)) := by
    apply UScalar.ext; apply BitVec.eq_of_getLsbD_eq; intro i hi
    change i < 8 at hi
    match i, hi with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
      simp [UScalar.bv_and, UScalar.bv_xor]
    | n + 8, hi => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 8 n) hi)
  rw [pureScaleXT1_mask (a ^^^ b), hab, pureScaleXT1_mask a, pureScaleXT1_mask b,
      mask3_eq_bv2Pack a, mask3_eq_bv2Pack b]
  generalize a.bv.getLsbD 1 = a1; generalize a.bv.getLsbD 0 = a0
  generalize b.bv.getLsbD 1 = b1; generalize b.bv.getLsbD 0 = b0
  cases a1 <;> cases a0 <;> cases b1 <;> cases b0 <;> rfl

private theorem pureMulT1_high_zero (a b : Std.U8) (i : Nat) (hi : 2 ≤ i) :
    (pureMulT1 a b).bv.getLsbD i = false := by
  rw [pureMulT1_mask a b, mask3_eq_bv2Pack a, mask3_eq_bv2Pack b]
  generalize a.bv.getLsbD 1 = a1; generalize a.bv.getLsbD 0 = a0
  generalize b.bv.getLsbD 1 = b1; generalize b.bv.getLsbD 0 = b0
  by_cases h8 : i < 8
  · match i, hi, h8 with
    | 2, _, _ | 3, _, _ | 4, _, _ | 5, _, _ | 6, _, _ | 7, _, _ =>
      cases a1 <;> cases a0 <;> cases b1 <;> cases b0 <;> rfl
  · exact BitVec.getLsbD_of_ge _ i (Nat.le_of_not_gt h8)

private theorem pureMulT2_high_zero (a b : Std.U8) (i : Nat) (hi : 4 ≤ i) :
    (pureMulT2 a b).bv.getLsbD i = false := by
  unfold pureMulT2
  dsimp only
  by_cases h8 : i < 8
  · simp only [UScalar.bv_or, UScalar.bv_xor, BitVec.getLsbD_or, BitVec.getLsbD_xor,
      BitVec.getLsbD_shiftLeft, h8]
    have hp : (pureMulT1 (a &&& 3#u8) (b &&& 3#u8)).bv.getLsbD i = false :=
      pureMulT1_high_zero _ _ i (Nat.le_trans (by decide) hi)
    have hq : (pureMulT1 (⟨a.bv >>> 2⟩ &&& 3#u8) (⟨b.bv >>> 2⟩ &&& 3#u8)).bv.getLsbD i = false :=
      pureMulT1_high_zero _ _ i (Nat.le_trans (by decide) hi)
    have hr : (pureMulT1 ((a &&& 3#u8) ^^^ (⟨a.bv >>> 2⟩ &&& 3#u8))
                ((b &&& 3#u8) ^^^ (⟨b.bv >>> 2⟩ &&& 3#u8))).bv.getLsbD (i - 2) = false :=
      pureMulT1_high_zero _ _ (i - 2) (Nat.le_sub_of_add_le hi)
    have hp2 : (pureMulT1 (a &&& 3#u8) (b &&& 3#u8)).bv.getLsbD (i - 2) = false :=
      pureMulT1_high_zero _ _ (i - 2) (Nat.le_sub_of_add_le hi)
    have hq2 : (pureMulT1 (⟨a.bv >>> 2⟩ &&& 3#u8) (⟨b.bv >>> 2⟩ &&& 3#u8)).bv.getLsbD (i - 2) = false :=
      pureMulT1_high_zero _ _ (i - 2) (Nat.le_sub_of_add_le hi)
    have hs : (pureScaleXT1 (pureMulT1 (⟨a.bv >>> 2⟩ &&& 3#u8) (⟨b.bv >>> 2⟩ &&& 3#u8))).bv.getLsbD (i - 2) = false := by
      rw [pureScaleXT1_mask, mask3_eq_bv2Pack]
      generalize (pureMulT1 (⟨a.bv >>> 2⟩ &&& 3#u8) (⟨b.bv >>> 2⟩ &&& 3#u8)).bv.getLsbD 1 = q1
      generalize (pureMulT1 (⟨a.bv >>> 2⟩ &&& 3#u8) (⟨b.bv >>> 2⟩ &&& 3#u8)).bv.getLsbD 0 = q0
      match i, hi, h8 with
      | 4, _, _ | 5, _, _ | 6, _, _ | 7, _, _ =>
        cases q1 <;> cases q0 <;> rfl
    have hlt2 : ¬(i < 2) := Nat.not_lt_of_ge (Nat.le_trans (by decide) hi)
    simp [hp, hq, hr, hp2, hq2, hs, hlt2]
  · exact BitVec.getLsbD_of_ge _ i (Nat.le_of_not_gt h8)

private theorem u8_xor_4_rearrange (x1 x2 y1 y2 : Std.U8) :
    (x1 ^^^ x2) ^^^ (y1 ^^^ y2) = (x1 ^^^ y1) ^^^ (x2 ^^^ y2) := by
  apply UScalar.ext; apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [UScalar.bv_xor, BitVec.getLsbD_xor]
  cases x1.bv.getLsbD i <;> cases x2.bv.getLsbD i <;>
    cases y1.bv.getLsbD i <;> cases y2.bv.getLsbD i <;> rfl

private theorem u8_and_xor_right (a b m : Std.U8) :
    ((a ^^^ b) &&& m) = ((a &&& m) ^^^ (b &&& m)) := by
  apply UScalar.ext; apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [UScalar.bv_and, UScalar.bv_xor, BitVec.getLsbD_and, BitVec.getLsbD_xor]
  cases a.bv.getLsbD i <;> cases b.bv.getLsbD i <;> cases m.bv.getLsbD i <;> rfl

private theorem u8_shr_xor (a b : Std.U8) (s : Nat) :
    (⟨(a ^^^ b).bv >>> s⟩ : Std.U8) = (⟨a.bv >>> s⟩ ^^^ ⟨b.bv >>> s⟩) := by
  apply UScalar.ext; apply BitVec.eq_of_getLsbD_eq; intro i _
  simp [UScalar.bv_xor, BitVec.getLsbD_ushiftRight]

private theorem pureMulT2_comm (a b : Std.U8) : pureMulT2 a b = pureMulT2 b a := by
  unfold pureMulT2
  dsimp only
  rw [pureMulT1_comm (a &&& 3#u8) (b &&& 3#u8),
      pureMulT1_comm (⟨a.bv >>> 2⟩ &&& 3#u8) (⟨b.bv >>> 2⟩ &&& 3#u8),
      pureMulT1_comm ((a &&& 3#u8) ^^^ (⟨a.bv >>> 2⟩ &&& 3#u8))
                     ((b &&& 3#u8) ^^^ (⟨b.bv >>> 2⟩ &&& 3#u8))]

private theorem pureMulT2_xor_right (a b c : Std.U8) :
    pureMulT2 a (b ^^^ c) = pureMulT2 a b ^^^ pureMulT2 a c := by
  unfold pureMulT2
  dsimp only
  rw [u8_and_xor_right b c 3#u8, u8_shr_xor b c 2, u8_and_xor_right ⟨b.bv >>> 2⟩ ⟨c.bv >>> 2⟩ 3#u8]
  let al := a &&& 3#u8
  let ah := ⟨a.bv >>> 2⟩ &&& 3#u8
  let bl := b &&& 3#u8
  let bh := ⟨b.bv >>> 2⟩ &&& 3#u8
  let cl := c &&& 3#u8
  let ch := ⟨c.bv >>> 2⟩ &&& 3#u8
  rw [u8_xor_4_rearrange bl cl bh ch,
      pureMulT1_xor_right al bl cl,
      pureMulT1_xor_right ah bh ch,
      pureMulT1_xor_right (al ^^^ ah) (bl ^^^ bh) (cl ^^^ ch),
      pureScaleXT1_xor]
  let p1 := pureMulT1 al bl; let p2 := pureMulT1 al cl
  let q1 := pureMulT1 ah bh; let q2 := pureMulT1 ah ch
  let r1 := pureMulT1 (al ^^^ ah) (bl ^^^ bh)
  let r2 := pureMulT1 (al ^^^ ah) (cl ^^^ ch)
  rw [u8_xor_4_rearrange p1 p2 q1 q2]
  have hhi : ((((r1 ^^^ r2) ^^^ (p1 ^^^ p2)) ^^^ (q1 ^^^ q2)) ^^^ (pureScaleXT1 q1 ^^^ pureScaleXT1 q2)) =
      (((r1 ^^^ p1) ^^^ q1) ^^^ pureScaleXT1 q1) ^^^ (((r2 ^^^ p2) ^^^ q2) ^^^ pureScaleXT1 q2) := by
    apply UScalar.ext; apply BitVec.eq_of_getLsbD_eq; intro i _
    simp only [UScalar.bv_xor, BitVec.getLsbD_xor]
    cases r1.bv.getLsbD i <;> cases r2.bv.getLsbD i <;>
      cases p1.bv.getLsbD i <;> cases p2.bv.getLsbD i <;>
      cases q1.bv.getLsbD i <;> cases q2.bv.getLsbD i <;>
      cases (pureScaleXT1 q1).bv.getLsbD i <;> cases (pureScaleXT1 q2).bv.getLsbD i <;> rfl
  rw [hhi]
  apply UScalar.ext
  have hpq1 : ∀ i, 2 ≤ i → (p1 ^^^ q1).bv.getLsbD i = false := by
    intro i hi; simp [p1, q1, UScalar.bv_xor, pureMulT1_high_zero _ _ i hi]
  have hpq2 : ∀ i, 2 ≤ i → (p2 ^^^ q2).bv.getLsbD i = false := by
    intro i hi; simp [p2, q2, UScalar.bv_xor, pureMulT1_high_zero _ _ i hi]
  exact (bv_or_shift_xor (p1 ^^^ q1).bv (p2 ^^^ q2).bv _ _ 2 hpq1 hpq2).symm

private theorem pureScaleXT2_xor (a b : Std.U8) :
    pureScaleXT2 (a ^^^ b) = pureScaleXT2 a ^^^ pureScaleXT2 b := by
  unfold pureScaleXT2
  dsimp only
  rw [u8_and_xor_right a b 3#u8, u8_shr_xor a b 2, u8_and_xor_right ⟨a.bv >>> 2⟩ ⟨b.bv >>> 2⟩ 3#u8,
      pureScaleXT1_xor]
  let al := a &&& 3#u8; let bl := b &&& 3#u8
  let ah := ⟨a.bv >>> 2⟩ &&& 3#u8; let bh := ⟨b.bv >>> 2⟩ &&& 3#u8
  rw [u8_xor_4_rearrange al bl (pureScaleXT1 ah) (pureScaleXT1 bh)]
  apply UScalar.ext
  have hah : ∀ i, 2 ≤ i → ah.bv.getLsbD i = false := by
    intro i hi
    by_cases h8 : i < 8
    · match i, hi, h8 with
      | 2, _, _ | 3, _, _ | 4, _, _ | 5, _, _ | 6, _, _ | 7, _, _ =>
        simp [ah, UScalar.bv_and]
    · exact BitVec.getLsbD_of_ge _ i (Nat.le_of_not_gt h8)
  have hbh : ∀ i, 2 ≤ i → bh.bv.getLsbD i = false := by
    intro i hi
    by_cases h8 : i < 8
    · match i, hi, h8 with
      | 2, _, _ | 3, _, _ | 4, _, _ | 5, _, _ | 6, _, _ | 7, _, _ =>
        simp [bh, UScalar.bv_and]
    · exact BitVec.getLsbD_of_ge _ i (Nat.le_of_not_gt h8)
  exact (bv_or_shift_xor ah.bv bh.bv _ _ 2 hah hbh).symm

theorem pureGf256Mul_comm (a b : Std.U8) : pureGf256Mul a b = pureGf256Mul b a := by
  unfold pureGf256Mul
  dsimp only
  rw [pureMulT2_comm (a &&& 15#u8) (b &&& 15#u8),
      pureMulT2_comm (⟨a.bv >>> 4⟩ &&& 15#u8) (⟨b.bv >>> 4⟩ &&& 15#u8),
      pureMulT2_comm ((a &&& 15#u8) ^^^ (⟨a.bv >>> 4⟩ &&& 15#u8))
                     ((b &&& 15#u8) ^^^ (⟨b.bv >>> 4⟩ &&& 15#u8))]

theorem pureGf256Mul_xor_right (a b c : Std.U8) :
    pureGf256Mul a (b ^^^ c) = pureGf256Mul a b ^^^ pureGf256Mul a c := by
  unfold pureGf256Mul
  dsimp only
  rw [u8_and_xor_right b c 15#u8, u8_shr_xor b c 4, u8_and_xor_right ⟨b.bv >>> 4⟩ ⟨c.bv >>> 4⟩ 15#u8]
  let al := a &&& 15#u8
  let ah := ⟨a.bv >>> 4⟩ &&& 15#u8
  let bl := b &&& 15#u8
  let bh := ⟨b.bv >>> 4⟩ &&& 15#u8
  let cl := c &&& 15#u8
  let ch := ⟨c.bv >>> 4⟩ &&& 15#u8
  rw [u8_xor_4_rearrange bl cl bh ch,
      pureMulT2_xor_right al bl cl,
      pureMulT2_xor_right ah bh ch,
      pureMulT2_xor_right (al ^^^ ah) (bl ^^^ bh) (cl ^^^ ch),
      pureScaleXT2_xor]
  let p1 := pureMulT2 al bl; let p2 := pureMulT2 al cl
  let q1 := pureMulT2 ah bh; let q2 := pureMulT2 ah ch
  let r1 := pureMulT2 (al ^^^ ah) (bl ^^^ bh)
  let r2 := pureMulT2 (al ^^^ ah) (cl ^^^ ch)
  rw [u8_xor_4_rearrange p1 p2 q1 q2]
  have hhi : ((((r1 ^^^ r2) ^^^ (p1 ^^^ p2)) ^^^ (q1 ^^^ q2)) ^^^ (pureScaleXT2 q1 ^^^ pureScaleXT2 q2)) =
      (((r1 ^^^ p1) ^^^ q1) ^^^ pureScaleXT2 q1) ^^^ (((r2 ^^^ p2) ^^^ q2) ^^^ pureScaleXT2 q2) := by
    apply UScalar.ext; apply BitVec.eq_of_getLsbD_eq; intro i _
    simp only [UScalar.bv_xor, BitVec.getLsbD_xor]
    cases r1.bv.getLsbD i <;> cases r2.bv.getLsbD i <;>
      cases p1.bv.getLsbD i <;> cases p2.bv.getLsbD i <;>
      cases q1.bv.getLsbD i <;> cases q2.bv.getLsbD i <;>
      cases (pureScaleXT2 q1).bv.getLsbD i <;> cases (pureScaleXT2 q2).bv.getLsbD i <;> rfl
  rw [hhi]
  apply UScalar.ext
  have hpq1 : ∀ i, 4 ≤ i → (p1 ^^^ q1).bv.getLsbD i = false := by
    intro i hi; simp [p1, q1, UScalar.bv_xor, pureMulT2_high_zero _ _ i hi]
  have hpq2 : ∀ i, 4 ≤ i → (p2 ^^^ q2).bv.getLsbD i = false := by
    intro i hi; simp [p2, q2, UScalar.bv_xor, pureMulT2_high_zero _ _ i hi]
  exact (bv_or_shift_xor (p1 ^^^ q1).bv (p2 ^^^ q2).bv _ _ 4 hpq1 hpq2).symm

theorem pureGf256Mul_xor_left (a b c : Std.U8) :
    pureGf256Mul (a ^^^ b) c = pureGf256Mul a c ^^^ pureGf256Mul b c := by
  rw [pureGf256Mul_comm (a ^^^ b) c, pureGf256Mul_xor_right,
      pureGf256Mul_comm c a, pureGf256Mul_comm c b]

/--  Beaver-Triple Frobenius Evaluation Soundness:
    For **every** Beaver triple `(a, b, c = a * b)` and secret element `s ∈ GF(2^8)`,
    `dkg_beaver_frobenius_eval_gf256 a b c s` computes the exact Frobenius residual `s^2 ⊕ s`
    independent of the random masks `(a, b)`. -/
theorem dkg_beaver_frobenius_eval_spec (a b c s : tower.Gf256)
    (hc : tower.gf256_mul a b = .ok c) :
    threshold.dkg_beaver_frobenius_eval_gf256 a b c s =
      tower.gf256_frobenius_residual s := by
  rw [gf256_mul_eq_pure] at hc
  injection hc with hc_eq
  subst hc_eq
  change Result.ok
      (((pureGf256Mul a b ^^^ pureGf256Mul (s ^^^ a) b) ^^^
        (pureGf256Mul (s ^^^ b) a ^^^ pureGf256Mul (s ^^^ a) (s ^^^ b))) ^^^ s) =
    Result.ok (pureGf256Mul s s ^^^ s)
  congr 1
  rw [pureGf256Mul_xor_left s a b,
      pureGf256Mul_xor_left s b a,
      pureGf256Mul_xor_left s a (s ^^^ b),
      pureGf256Mul_xor_right s s b,
      pureGf256Mul_xor_right a s b,
      pureGf256Mul_comm a s,
      pureGf256Mul_comm b a]
  let ab := pureGf256Mul a b
  let sb := pureGf256Mul s b
  let sa := pureGf256Mul s a
  let ss := pureGf256Mul s s
  apply UScalar.ext; apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [UScalar.bv_xor, BitVec.getLsbD_xor]
  cases ab.bv.getLsbD i <;> cases sb.bv.getLsbD i <;>
    cases sa.bv.getLsbD i <;> cases ss.bv.getLsbD i <;>
    cases s.bv.getLsbD i <;> rfl

/-! ## Binary-field algebra by linear extension from eight basis vectors -/

private def gf256Basis (i : Fin 8) : Std.U8 := ⟨BitVec.ofNat 8 (2 ^ i.val)⟩

private theorem u8_basis_decomposition (x : Std.U8) :
    x = (if x.bv.getLsbD 0 then gf256Basis ⟨0, by decide⟩ else 0#u8) ^^^
      (if x.bv.getLsbD 1 then gf256Basis ⟨1, by decide⟩ else 0#u8) ^^^
      (if x.bv.getLsbD 2 then gf256Basis ⟨2, by decide⟩ else 0#u8) ^^^
      (if x.bv.getLsbD 3 then gf256Basis ⟨3, by decide⟩ else 0#u8) ^^^
      (if x.bv.getLsbD 4 then gf256Basis ⟨4, by decide⟩ else 0#u8) ^^^
      (if x.bv.getLsbD 5 then gf256Basis ⟨5, by decide⟩ else 0#u8) ^^^
      (if x.bv.getLsbD 6 then gf256Basis ⟨6, by decide⟩ else 0#u8) ^^^
      (if x.bv.getLsbD 7 then gf256Basis ⟨7, by decide⟩ else 0#u8) := by
  rcases x with ⟨bv⟩
  rw [bv8_eq_pack bv]
  generalize bv.getLsbD 7 = b7
  generalize bv.getLsbD 6 = b6
  generalize bv.getLsbD 5 = b5
  generalize bv.getLsbD 4 = b4
  generalize bv.getLsbD 3 = b3
  generalize bv.getLsbD 2 = b2
  generalize bv.getLsbD 1 = b1
  generalize bv.getLsbD 0 = b0
  cases b7 <;> cases b6 <;> cases b5 <;> cases b4 <;>
    cases b3 <;> cases b2 <;> cases b1 <;> cases b0 <;> rfl

private theorem gf256_basis_induction (P : Std.U8 → Prop)
    (hz : P 0#u8) (hx : ∀ a b, P a → P b → P (a ^^^ b))
    (hb : ∀ i : Fin 8, P (gf256Basis i)) (x : Std.U8) : P x := by
  have hc (b : Bool) (i : Fin 8) : P (if b then gf256Basis i else 0#u8) := by
    cases b
    · exact hz
    · exact hb i
  rw [u8_basis_decomposition x]
  repeat first | apply hx | exact hc _ _

theorem pureGf256Mul_zero (a : Std.U8) : pureGf256Mul a 0#u8 = 0#u8 := by
  have h := pureGf256Mul_xor_right a 0#u8 0#u8
  have hx (v : Std.U8) : v ^^^ v = 0#u8 := UScalar.ext BitVec.xor_self
  simpa only [hx] using h

theorem pureGf256Mul_zero_left (a : Std.U8) : pureGf256Mul 0#u8 a = 0#u8 := by
  rw [pureGf256Mul_comm, pureGf256Mul_zero]

private theorem pureGf256Inv_zero : pureGf256Inv 0#u8 = 0#u8 := by decide

/-- Force a Nat intermediate before reusing it in kernel computation. -/
private def natBind (n : Nat) (f : Nat → Nat) : Nat :=
  match n with
  | 0 => f 0
  | k + 1 => f (k + 1)

private theorem natBind_eq (n : Nat) (f : Nat → Nat) : natBind n f = f n := by
  cases n <;> rfl

private def natMulT1 (a b : Nat) : Nat :=
  natBind a fun a =>
  natBind b fun b =>
  natBind (a &&& 1) fun a_lo =>
  natBind (((a % 256) >>> 1) &&& 1) fun a_hi =>
  natBind (b &&& 1) fun b_lo =>
  natBind (((b % 256) >>> 1) &&& 1) fun b_hi =>
  natBind (a_lo &&& b_lo) fun p =>
  natBind (a_hi &&& b_hi) fun q =>
  natBind ((a_lo ^^^ a_hi) &&& (b_lo ^^^ b_hi)) fun r =>
  (p ^^^ q) ||| (((r ^^^ p) % 256) <<< 1)

private def natScaleXT1 (a : Nat) : Nat :=
  natBind (a &&& 1) fun lo =>
  natBind (((a % 256) >>> 1) &&& 1) fun hi =>
  hi ||| (((lo ^^^ hi) % 256) <<< 1)

private def natMulT2 (a b : Nat) : Nat :=
  natBind a fun a =>
  natBind b fun b =>
  natBind (a &&& 3) fun a_lo =>
  natBind (((a % 256) >>> 2) &&& 3) fun a_hi =>
  natBind (b &&& 3) fun b_lo =>
  natBind (((b % 256) >>> 2) &&& 3) fun b_hi =>
  natBind (natMulT1 a_lo b_lo) fun p =>
  natBind (natMulT1 a_hi b_hi) fun q =>
  natBind (natMulT1 (a_lo ^^^ a_hi) (b_lo ^^^ b_hi)) fun r =>
  natBind (((r ^^^ p) ^^^ q) ^^^ natScaleXT1 q) fun hi =>
  (p ^^^ q) ||| ((hi % 256) <<< 2)

private def natScaleXT2 (a : Nat) : Nat :=
  natBind (a &&& 3) fun lo =>
  natBind (((a % 256) >>> 2) &&& 3) fun hi =>
  hi ||| (((lo ^^^ natScaleXT1 hi) % 256) <<< 2)

private def natGf256Mul (a b : Nat) : Nat :=
  natBind a fun a =>
  natBind b fun b =>
  natBind (a &&& 15) fun a_lo =>
  natBind (((a % 256) >>> 4) &&& 15) fun a_hi =>
  natBind (b &&& 15) fun b_lo =>
  natBind (((b % 256) >>> 4) &&& 15) fun b_hi =>
  natBind (natMulT2 a_lo b_lo) fun p =>
  natBind (natMulT2 a_hi b_hi) fun q =>
  natBind (natMulT2 (a_lo ^^^ a_hi) (b_lo ^^^ b_hi)) fun r =>
  natBind (((r ^^^ p) ^^^ q) ^^^ natScaleXT2 q) fun hi =>
  (p ^^^ q) ||| ((hi % 256) <<< 4)

private def natByte (a : Nat) : Std.U8 := ⟨BitVec.ofNat 8 a⟩

private theorem natByte_and (a b : Nat) : natByte a &&& natByte b = natByte (a &&& b) :=
  UScalar.ext BitVec.ofNat_and.symm
private theorem natByte_xor (a b : Nat) : natByte a ^^^ natByte b = natByte (a ^^^ b) :=
  UScalar.ext BitVec.ofNat_xor.symm
private theorem natByte_or (a b : Nat) : natByte a ||| natByte b = natByte (a ||| b) :=
  UScalar.ext BitVec.ofNat_or.symm
private theorem natByte_shr (a n : Nat) :
    (⟨(natByte a).bv >>> n⟩ : Std.U8) = natByte ((a % 256) >>> n) := by
  apply UScalar.ext
  apply BitVec.eq_of_toNat_eq
  simp only [UScalarTy.numBits, natByte, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (Nat.mod_lt _ (by decide)))).symm
private theorem natByte_shl (a n : Nat) :
    (⟨(natByte a).bv <<< n⟩ : Std.U8) = natByte ((a % 256) <<< n) := by
  apply UScalar.ext
  apply BitVec.eq_of_toNat_eq
  simp only [UScalarTy.numBits, natByte, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]

private theorem pureMulT1_nat (a b : Nat) :
    pureMulT1 (natByte a) (natByte b) = natByte (natMulT1 a b) := by
  unfold pureMulT1 natMulT1
  simp only [natBind_eq]
  rw [natByte_shr a 1, natByte_shr b 1]
  change _ = natByte _
  simp only [UScalarTy.numBits, show (1#u8) = natByte 1 from rfl, natByte_and, natByte_xor]
  rw [natByte_shl _ 1, natByte_or]


private theorem pureScaleXT1_nat (a : Nat) :
    pureScaleXT1 (natByte a) = natByte (natScaleXT1 a) := by
  unfold pureScaleXT1 natScaleXT1
  simp only [natBind_eq]
  rw [natByte_shr a 1]
  simp only [UScalarTy.numBits, show (1#u8) = natByte 1 from rfl, natByte_and, natByte_xor]
  rw [natByte_shl _ 1, natByte_or]


private theorem pureMulT2_nat (a b : Nat) :
    pureMulT2 (natByte a) (natByte b) = natByte (natMulT2 a b) := by
  unfold pureMulT2 natMulT2
  simp only [natBind_eq]
  rw [natByte_shr a 2, natByte_shr b 2]
  simp only [UScalarTy.numBits, show (3#u8) = natByte 3 from rfl, natByte_and, natByte_xor, pureMulT1_nat, pureScaleXT1_nat]
  rw [natByte_shl _ 2, natByte_or]


private theorem pureScaleXT2_nat (a : Nat) :
    pureScaleXT2 (natByte a) = natByte (natScaleXT2 a) := by
  unfold pureScaleXT2 natScaleXT2
  simp only [natBind_eq]
  rw [natByte_shr a 2]
  simp only [UScalarTy.numBits, show (3#u8) = natByte 3 from rfl, natByte_and, natByte_xor, pureScaleXT1_nat]
  rw [natByte_shl _ 2, natByte_or]


private theorem pureGf256Mul_nat (a b : Nat) :
    pureGf256Mul (natByte a) (natByte b) = natByte (natGf256Mul a b) := by
  unfold pureGf256Mul natGf256Mul
  simp only [natBind_eq]
  rw [natByte_shr a 4, natByte_shr b 4]
  simp only [UScalarTy.numBits, show (15#u8) = natByte 15 from rfl, natByte_and, natByte_xor, pureMulT2_nat, pureScaleXT2_nat]
  rw [natByte_shl _ 4, natByte_or]

private def natGf256Inv (a : Nat) : Nat :=
  natBind (natGf256Mul a a) fun a2 =>
  natBind (natGf256Mul a2 a2) fun a4 =>
  natBind (natGf256Mul a4 a2) fun a6 =>
  natBind (natGf256Mul a4 a4) fun a8 =>
  natBind (natGf256Mul a8 a6) fun a14 =>
  natBind (natGf256Mul a8 a8) fun a16 =>
  natBind (natGf256Mul a16 a16) fun a32 =>
  natBind (natGf256Mul a32 a32) fun a64 =>
  natBind (natGf256Mul a64 a64) fun a128 =>
  natGf256Mul (natGf256Mul (natGf256Mul a128 a64)
    (natGf256Mul a32 a16)) a14

private theorem pureGf256Inv_nat (a : Nat) :
    pureGf256Inv (natByte a) = natByte (natGf256Inv a) := by
  simp only [pureGf256Inv, natGf256Inv, natBind_eq, pureGf256Mul_nat]

private theorem pureGf256Inv_fin : ∀ k : Fin 256, k.val ≠ 0 →
    pureGf256Mul ⟨BitVec.ofNat 8 k.val⟩ (pureGf256Inv ⟨BitVec.ofNat 8 k.val⟩) = 1#u8 := by
  have h : ∀ k : Fin 256, k.val ≠ 0 → natGf256Mul k.val (natGf256Inv k.val) = 1 := by decide
  intro k hk
  change pureGf256Mul (natByte k.val) (pureGf256Inv (natByte k.val)) = natByte 1
  rw [pureGf256Inv_nat, pureGf256Mul_nat, h k hk]

private theorem pureGf256_boolean_fin : ∀ k : Fin 256,
    (pureGf256Mul ⟨BitVec.ofNat 8 k.val⟩ ⟨BitVec.ofNat 8 k.val⟩ ^^^
      (⟨BitVec.ofNat 8 k.val⟩ : Std.U8) = 0#u8 ↔
      (⟨BitVec.ofNat 8 k.val⟩ : Std.U8) = 0#u8 ∨
      (⟨BitVec.ofNat 8 k.val⟩ : Std.U8) = 1#u8) := by
  have hmul (a : Nat) : pureGf256Mul ⟨BitVec.ofNat 8 a⟩ ⟨BitVec.ofNat 8 a⟩ =
      (⟨BitVec.ofNat 8 (natGf256Mul a a)⟩ : Std.U8) := pureGf256Mul_nat a a
  simp only [hmul]
  decide

/--  Frobenius Booleanity Characterization over Aeneas-extracted `Gf256`:
    `x^2 ⊕ x == 0` holds in Wiedemann `GF(2^8)` **if and only if** `x ∈ {0, 1}`,
    and `gf256_is_boolean_frobenius` is total and exact on all 256 elements. -/
theorem tower_gf256_boolean_iff_frobenius (x : tower.Gf256) :
    (tower.gf256_frobenius_residual x = .ok 0#u8 ↔ (x = 0#u8 ∨ x = 1#u8)) ∧
    tower.gf256_is_boolean_frobenius x = .ok (decide (x = 0#u8 ∨ x = 1#u8)) := by
  have hx : (⟨BitVec.ofNat 8 x.bv.toNat⟩ : Std.U8) = x :=
    by
      apply UScalar.ext
      simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hf := pureGf256_boolean_fin ⟨x.bv.toNat, x.bv.isLt⟩
  dsimp only at hf
  rw [hx] at hf
  simp [tower.gf256_is_boolean_frobenius, tower.gf256_frobenius_residual,
    gf256_mul_eq_pure, tower.gf256_add, hf]

/-- `gf256_inv_or_zero` ($a^{254}$ Fermat inversion in `GF(2^8)`) is total and satisfies
    `a * inv(a) = 1` for every nonzero `a : Gf256`, and `inv(0) = 0`. -/
theorem tower_gf256_inv_or_zero_spec (a : tower.Gf256) :
    ∃ inv : tower.Gf256,
      tower.gf256_inv_or_zero a = .ok inv ∧
      (a = 0#u8 → inv = 0#u8) ∧
      (a ≠ 0#u8 → tower.gf256_mul a inv = .ok 1#u8) := by
  refine ⟨pureGf256Inv a, gf256_inv_or_zero_eq_pure a, ?_, ?_⟩
  · rintro rfl
    exact pureGf256Inv_zero
  · intro ha
    have hk : a.bv.toNat ≠ 0 := by
      intro h
      exact ha (UScalar.eq_of_val_eq h)
    have hx : (⟨BitVec.ofNat 8 a.bv.toNat⟩ : Std.U8) = a :=
      by
        apply UScalar.ext
        simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have hi := pureGf256Inv_fin ⟨a.bv.toNat, a.bv.isLt⟩ hk
    dsimp only at hi
    rw [hx] at hi
    rw [gf256_mul_eq_pure, hi]

theorem pureGf256Mul_one (a : Std.U8) : pureGf256Mul a 1#u8 = a := by
  apply gf256_basis_induction (fun a => pureGf256Mul a 1#u8 = a)
  · exact pureGf256Mul_zero_left _
  · intro a b ha hb
    simp only [pureGf256Mul_xor_left, ha, hb]
  · exact (by decide : ∀ i : Fin 8, pureGf256Mul (gf256Basis i) 1#u8 = gf256Basis i)

private theorem gf256_basis_assoc : ∀ i j k : Fin 8,
    pureGf256Mul (pureGf256Mul (gf256Basis i) (gf256Basis j)) (gf256Basis k) =
      pureGf256Mul (gf256Basis i) (pureGf256Mul (gf256Basis j) (gf256Basis k)) := by
  have h : ∀ i j k : Fin 8,
      natGf256Mul (natGf256Mul (2 ^ i.val) (2 ^ j.val)) (2 ^ k.val) =
        natGf256Mul (2 ^ i.val) (natGf256Mul (2 ^ j.val) (2 ^ k.val)) := by decide
  intro i j k
  change pureGf256Mul (pureGf256Mul (natByte (2 ^ i.val)) (natByte (2 ^ j.val))) (natByte (2 ^ k.val)) =
    pureGf256Mul (natByte (2 ^ i.val)) (pureGf256Mul (natByte (2 ^ j.val)) (natByte (2 ^ k.val)))
  simp only [pureGf256Mul_nat, h]

theorem pureGf256Mul_assoc (a b c : Std.U8) :
    pureGf256Mul (pureGf256Mul a b) c = pureGf256Mul a (pureGf256Mul b c) := by
  have hbc (i j : Fin 8) (c : Std.U8) :
      pureGf256Mul (pureGf256Mul (gf256Basis i) (gf256Basis j)) c =
        pureGf256Mul (gf256Basis i) (pureGf256Mul (gf256Basis j) c) := by
    apply gf256_basis_induction (fun c =>
      pureGf256Mul (pureGf256Mul (gf256Basis i) (gf256Basis j)) c =
        pureGf256Mul (gf256Basis i) (pureGf256Mul (gf256Basis j) c))
    · change pureGf256Mul (pureGf256Mul (gf256Basis i) (gf256Basis j)) 0#u8 = pureGf256Mul (gf256Basis i) (pureGf256Mul (gf256Basis j) 0#u8)
      rw [pureGf256Mul_zero, pureGf256Mul_zero, pureGf256Mul_zero]
    · intro u v hu hv
      simp only [pureGf256Mul_xor_right, hu, hv]
    · exact gf256_basis_assoc i j
  have hc (i : Fin 8) (b c : Std.U8) :
      pureGf256Mul (pureGf256Mul (gf256Basis i) b) c =
        pureGf256Mul (gf256Basis i) (pureGf256Mul b c) := by
    apply gf256_basis_induction (fun b =>
      pureGf256Mul (pureGf256Mul (gf256Basis i) b) c =
        pureGf256Mul (gf256Basis i) (pureGf256Mul b c))
    · change pureGf256Mul (pureGf256Mul (gf256Basis i) 0#u8) c = pureGf256Mul (gf256Basis i) (pureGf256Mul 0#u8 c)
      rw [pureGf256Mul_zero, pureGf256Mul_zero_left, pureGf256Mul_zero]
    · intro u v hu hv
      simp only [pureGf256Mul_xor_right, pureGf256Mul_xor_left, hu, hv]
    · intro j; exact hbc i j c
  apply gf256_basis_induction (fun a =>
    pureGf256Mul (pureGf256Mul a b) c = pureGf256Mul a (pureGf256Mul b c))
  · change pureGf256Mul (pureGf256Mul 0#u8 b) c = pureGf256Mul 0#u8 (pureGf256Mul b c)
    rw [pureGf256Mul_zero_left, pureGf256Mul_zero_left, pureGf256Mul_zero_left]
  · intro u v hu hv
    simp only [pureGf256Mul_xor_left, hu, hv]
  · intro i; exact hc i b c

theorem tower_gf256_field_laws (a b c : tower.Gf256) :
    pureGf256Mul a 0#u8 = 0#u8 ∧ pureGf256Mul a 1#u8 = a ∧
    pureGf256Mul a b = pureGf256Mul b a ∧
    pureGf256Mul (pureGf256Mul a b) c = pureGf256Mul a (pureGf256Mul b c) ∧
    pureGf256Mul a (b ^^^ c) = pureGf256Mul a b ^^^ pureGf256Mul a c :=
  ⟨pureGf256Mul_zero a, pureGf256Mul_one a, pureGf256Mul_comm a b,
    pureGf256Mul_assoc a b c, pureGf256Mul_xor_right a b c⟩

theorem tower_gf256_inv_spec (a : tower.Gf256) :
    (a = 0#u8 → tower.gf256_inv a = .ok none) ∧
    (a ≠ 0#u8 → ∃ inv, tower.gf256_inv a = .ok (some inv) ∧
      tower.gf256_mul a inv = .ok 1#u8) := by
  obtain ⟨inv, hi, hz, hn⟩ := tower_gf256_inv_or_zero_spec a
  constructor
  · intro ha; simp [tower.gf256_inv, hi, hz ha]
  · intro ha
    have hne : inv ≠ 0#u8 := by
      intro hzero
      have he := hn ha
      rw [gf256_mul_eq_pure, hzero, pureGf256Mul_zero] at he
      cases he
    exact ⟨inv, by simp [tower.gf256_inv, hi, hne], hn ha⟩

theorem pureGf256Mul_eq_zero_iff (a b : Std.U8) :
    pureGf256Mul a b = 0#u8 ↔ a = 0#u8 ∨ b = 0#u8 := by
  constructor
  · intro h
    by_cases ha : a = 0#u8
    · exact Or.inl ha
    · obtain ⟨inv, _, hi⟩ := (tower_gf256_inv_spec a).2 ha
      have hp : pureGf256Mul a inv = 1#u8 := by
        simpa only [gf256_mul_eq_pure, Result.ok.injEq] using hi
      have he := congrArg (fun x => pureGf256Mul x inv) h
      rw [pureGf256Mul_comm a b, pureGf256Mul_assoc, hp,
        pureGf256Mul_one, pureGf256Mul_zero_left] at he
      exact Or.inr he
  · rintro (rfl | rfl)
    · exact pureGf256Mul_zero_left _
    · exact pureGf256Mul_zero _

theorem pureGf256Mul_inv (a : Std.U8) (ha : a ≠ 0#u8) :
    pureGf256Mul a (pureGf256Inv a) = 1#u8 := by
  obtain ⟨inv, he, _, hi⟩ := tower_gf256_inv_or_zero_spec a
  rw [gf256_inv_or_zero_eq_pure] at he
  have h := Result.ok.inj he
  rw [← h, gf256_mul_eq_pure] at hi
  exact Result.ok.inj (hi ha)

private theorem pureGf256Mul_four (a b c d : Std.U8) :
    pureGf256Mul (pureGf256Mul a b) (pureGf256Mul c d) =
      pureGf256Mul (pureGf256Mul a c) (pureGf256Mul b d) := by
  rw [pureGf256Mul_assoc a b, ← pureGf256Mul_assoc b c d,
    pureGf256Mul_comm b c, pureGf256Mul_assoc c b d,
    ← pureGf256Mul_assoc a c]

theorem pureGf256Inv_mul (a b : Std.U8) :
    pureGf256Inv (pureGf256Mul a b) =
      pureGf256Mul (pureGf256Inv a) (pureGf256Inv b) := by
  by_cases ha : a = 0#u8
  · subst a; rw [pureGf256Mul_zero_left, pureGf256Inv_zero, pureGf256Mul_zero_left]
  by_cases hb : b = 0#u8
  · subst b; rw [pureGf256Mul_zero, pureGf256Inv_zero, pureGf256Mul_zero]
  have hab : pureGf256Mul a b ≠ 0#u8 := by
    intro h; rcases (pureGf256Mul_eq_zero_iff a b).mp h with h | h
    · exact ha h
    · exact hb h
  have hc : pureGf256Mul (pureGf256Mul a b)
      (pureGf256Mul (pureGf256Inv a) (pureGf256Inv b)) = 1#u8 := by
    rw [pureGf256Mul_four, pureGf256Mul_inv a ha, pureGf256Mul_inv b hb,
      pureGf256Mul_one]
  calc
    pureGf256Inv (pureGf256Mul a b) =
        pureGf256Mul (pureGf256Inv (pureGf256Mul a b)) 1#u8 :=
      (pureGf256Mul_one _).symm
    _ = pureGf256Mul (pureGf256Inv (pureGf256Mul a b))
        (pureGf256Mul (pureGf256Mul a b)
          (pureGf256Mul (pureGf256Inv a) (pureGf256Inv b))) := by rw [hc]
    _ = pureGf256Mul (pureGf256Mul (pureGf256Inv (pureGf256Mul a b))
        (pureGf256Mul a b)) (pureGf256Mul (pureGf256Inv a) (pureGf256Inv b)) :=
      (pureGf256Mul_assoc _ _ _).symm
    _ = pureGf256Mul (pureGf256Inv a) (pureGf256Inv b) := by
      rw [pureGf256Mul_comm (pureGf256Inv (pureGf256Mul a b)),
        pureGf256Mul_inv _ hab, pureGf256Mul_comm 1#u8, pureGf256Mul_one]


end qsag_verified.proofs
