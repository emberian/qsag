module

public import QsagVerified.Funs
public import QsagVerified.Proofs.Gf256

public section

namespace qsag_verified.proofs

open Aeneas Aeneas.Std Result ControlFlow Error
open qsag_verified

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

attribute [-simp] BitVec.getLsbD_eq_getElem
attribute [local simp] UScalar.val UScalarTy.numBits

/-! ## Wide binary towers and replicated-sharing gates -/

private theorem mul_t3_total (a b : Std.U8) : ∃ c, tower.mul_t3 a b = .ok c :=
  ⟨_, rfl⟩

private theorem scale_x_t3_total (a : Std.U8) : ∃ c, tower.scale_x_t3 a = .ok c := ⟨_, rfl⟩

private theorem mul_t4_total (a b : Std.U16) : ∃ c, tower.mul_t4 a b = .ok c := by
  let alo : Std.U8 := UScalar.cast .U8 (a &&& 255#u16)
  let ahi : Std.U8 := UScalar.cast .U8 ((⟨a.bv >>> 8⟩ : Std.U16) &&& 255#u16)
  let blo : Std.U8 := UScalar.cast .U8 (b &&& 255#u16)
  let bhi : Std.U8 := UScalar.cast .U8 ((⟨b.bv >>> 8⟩ : Std.U16) &&& 255#u16)
  obtain ⟨p, hp⟩ := mul_t3_total alo blo
  obtain ⟨q, hq⟩ := mul_t3_total ahi bhi
  obtain ⟨r, hr⟩ := mul_t3_total (alo ^^^ ahi) (blo ^^^ bhi)
  obtain ⟨sx, hs⟩ := scale_x_t3_total q
  have ha : (a >>> 8#i32 : Result Std.U16) = .ok ⟨a.bv >>> 8⟩ := rfl
  have hb : (b >>> 8#i32 : Result Std.U16) = .ok ⟨b.bv >>> 8⟩ := rfl
  refine ⟨⟨(UScalar.cast .U16 (p ^^^ q)).bv ||| ((UScalar.cast .U16 (r ^^^ p ^^^ q ^^^ sx)).bv <<< 8)⟩, ?_⟩
  unfold tower.mul_t4
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step ha
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hb
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hp
  apply bind_ok_step hq
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hr
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hs
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  rfl



private theorem scale_x_t4_total (a : Std.U16) : ∃ c, tower.scale_x_t4 a = .ok c := by
  let hi : Std.U8 := UScalar.cast .U8 ((⟨a.bv >>> 8⟩ : Std.U16) &&& 255#u16)
  obtain ⟨sx, hs⟩ := scale_x_t3_total hi
  have ha : (a >>> 8#i32 : Result Std.U16) = .ok ⟨a.bv >>> 8⟩ := rfl
  refine ⟨⟨(UScalar.cast .U16 hi).bv ||| ((UScalar.cast .U16 ((UScalar.cast .U8 (a &&& 255#u16)) ^^^ sx)).bv <<< 8)⟩, ?_⟩
  unfold tower.scale_x_t4
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step ha
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hs
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  rfl



private theorem mul_t5_total (a b : Std.U32) : ∃ c, tower.mul_t5 a b = .ok c := by
  let alo : Std.U16 := UScalar.cast .U16 (a &&& 65535#u32)
  let ahi : Std.U16 := UScalar.cast .U16 ((⟨a.bv >>> 16⟩ : Std.U32) &&& 65535#u32)
  let blo : Std.U16 := UScalar.cast .U16 (b &&& 65535#u32)
  let bhi : Std.U16 := UScalar.cast .U16 ((⟨b.bv >>> 16⟩ : Std.U32) &&& 65535#u32)
  obtain ⟨p, hp⟩ := mul_t4_total alo blo
  obtain ⟨q, hq⟩ := mul_t4_total ahi bhi
  obtain ⟨r, hr⟩ := mul_t4_total (alo ^^^ ahi) (blo ^^^ bhi)
  obtain ⟨sx, hs⟩ := scale_x_t4_total q
  have ha : (a >>> 16#i32 : Result Std.U32) = .ok ⟨a.bv >>> 16⟩ := rfl
  have hb : (b >>> 16#i32 : Result Std.U32) = .ok ⟨b.bv >>> 16⟩ := rfl
  refine ⟨⟨(UScalar.cast .U32 (p ^^^ q)).bv ||| ((UScalar.cast .U32 (r ^^^ p ^^^ q ^^^ sx)).bv <<< 16)⟩, ?_⟩
  unfold tower.mul_t5
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step ha
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hb
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hp
  apply bind_ok_step hq
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hr
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hs
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  rfl



private theorem scale_x_t5_total (a : Std.U32) : ∃ c, tower.scale_x_t5 a = .ok c := by
  let hi : Std.U16 := UScalar.cast .U16 ((⟨a.bv >>> 16⟩ : Std.U32) &&& 65535#u32)
  obtain ⟨sx, hs⟩ := scale_x_t4_total hi
  have ha : (a >>> 16#i32 : Result Std.U32) = .ok ⟨a.bv >>> 16⟩ := rfl
  refine ⟨⟨(UScalar.cast .U32 hi).bv ||| ((UScalar.cast .U32 ((UScalar.cast .U16 (a &&& 65535#u32)) ^^^ sx)).bv <<< 16)⟩, ?_⟩
  unfold tower.scale_x_t5
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step ha
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hs
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  rfl



private theorem mul_t6_total (a b : Std.U64) : ∃ c, tower.mul_t6 a b = .ok c := by
  let alo : Std.U32 := UScalar.cast .U32 (a &&& 4294967295#u64)
  let ahi : Std.U32 := UScalar.cast .U32 ((⟨a.bv >>> 32⟩ : Std.U64) &&& 4294967295#u64)
  let blo : Std.U32 := UScalar.cast .U32 (b &&& 4294967295#u64)
  let bhi : Std.U32 := UScalar.cast .U32 ((⟨b.bv >>> 32⟩ : Std.U64) &&& 4294967295#u64)
  obtain ⟨p, hp⟩ := mul_t5_total alo blo
  obtain ⟨q, hq⟩ := mul_t5_total ahi bhi
  obtain ⟨r, hr⟩ := mul_t5_total (alo ^^^ ahi) (blo ^^^ bhi)
  obtain ⟨sx, hs⟩ := scale_x_t5_total q
  have ha : (a >>> 32#i32 : Result Std.U64) = .ok ⟨a.bv >>> 32⟩ := rfl
  have hb : (b >>> 32#i32 : Result Std.U64) = .ok ⟨b.bv >>> 32⟩ := rfl
  refine ⟨⟨(UScalar.cast .U64 (p ^^^ q)).bv ||| ((UScalar.cast .U64 (r ^^^ p ^^^ q ^^^ sx)).bv <<< 32)⟩, ?_⟩
  unfold tower.mul_t6
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step ha
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hb
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hp
  apply bind_ok_step hq
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hr
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hs
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  rfl



private theorem scale_x_t6_total (a : Std.U64) : ∃ c, tower.scale_x_t6 a = .ok c := by
  let hi : Std.U32 := UScalar.cast .U32 ((⟨a.bv >>> 32⟩ : Std.U64) &&& 4294967295#u64)
  obtain ⟨sx, hs⟩ := scale_x_t5_total hi
  have ha : (a >>> 32#i32 : Result Std.U64) = .ok ⟨a.bv >>> 32⟩ := rfl
  refine ⟨⟨(UScalar.cast .U64 hi).bv ||| ((UScalar.cast .U64 ((UScalar.cast .U32 (a &&& 4294967295#u64)) ^^^ sx)).bv <<< 32)⟩, ?_⟩
  unfold tower.scale_x_t6
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step ha
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hs
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  rfl



/-- `tower128_mul` (7-level Wiedemann binary tower `GF(2^128)` Karatsuba multiplication)
    is 100% panic-free and branchless for all 128-bit inputs. -/
theorem tower128_mul_total (a b : tower.Tower128) :
    ∃ c : tower.Tower128, tower.tower128_mul a b = .ok c := by
  let alo : Std.U64 := UScalar.cast .U64 (a &&& 18446744073709551615#u128)
  let ahi : Std.U64 := UScalar.cast .U64 ((⟨a.bv >>> 64⟩ : Std.U128) &&& 18446744073709551615#u128)
  let blo : Std.U64 := UScalar.cast .U64 (b &&& 18446744073709551615#u128)
  let bhi : Std.U64 := UScalar.cast .U64 ((⟨b.bv >>> 64⟩ : Std.U128) &&& 18446744073709551615#u128)
  obtain ⟨p, hp⟩ := mul_t6_total alo blo
  obtain ⟨q, hq⟩ := mul_t6_total ahi bhi
  obtain ⟨r, hr⟩ := mul_t6_total (alo ^^^ ahi) (blo ^^^ bhi)
  obtain ⟨sx, hs⟩ := scale_x_t6_total q
  have ha : (a >>> 64#i32 : Result Std.U128) = .ok ⟨a.bv >>> 64⟩ := rfl
  have hb : (b >>> 64#i32 : Result Std.U128) = .ok ⟨b.bv >>> 64⟩ := rfl
  refine ⟨⟨(UScalar.cast .U128 (p ^^^ q)).bv ||| ((UScalar.cast .U128 (r ^^^ p ^^^ q ^^^ sx)).bv <<< 64)⟩, ?_⟩
  unfold tower.tower128_mul
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step ha
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hb
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hp
  apply bind_ok_step hq
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hr
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hs
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  rfl




/-! Independent pure Wiedemann arithmetic. These definitions use only scalar
bit operations and smaller pure field operations; none calls extracted MIR.
The stored basis obeys X² = 1 + αX, not X² = X + α. -/
@[expose] def pureScaleXT3 (a : Std.U8) : Std.U8 :=
  let lo := a &&& 15#u8
  let hi := (⟨a.bv >>> 4⟩ : Std.U8) &&& 15#u8
  hi ||| ⟨(lo ^^^ pureScaleXT2 hi).bv <<< 4⟩

private theorem mul_t3_eq_independent (a b : Std.U8) :
    tower.mul_t3 a b = .ok (pureGf256Mul a b) := by rfl
private theorem scale_x_t3_eq_independent (a : Std.U8) :
    tower.scale_x_t3 a = .ok (pureScaleXT3 a) := by rfl

@[expose] def pureMulT4 (a b : Std.U16) : Std.U16 :=
  let alo : Std.U8 := UScalar.cast .U8 (a &&& 255#u16)
  let ahi : Std.U8 := UScalar.cast .U8 ((⟨a.bv >>> 8⟩ : Std.U16) &&& 255#u16)
  let blo : Std.U8 := UScalar.cast .U8 (b &&& 255#u16)
  let bhi : Std.U8 := UScalar.cast .U8 ((⟨b.bv >>> 8⟩ : Std.U16) &&& 255#u16)
  let p := pureGf256Mul alo blo
  let q := pureGf256Mul ahi bhi
  let r := pureGf256Mul (alo ^^^ ahi) (blo ^^^ bhi)
  let sx := pureScaleXT3 q
  ⟨(UScalar.cast .U16 (p ^^^ q)).bv ||| ((UScalar.cast .U16 (r ^^^ p ^^^ q ^^^ sx)).bv <<< 8)⟩

theorem mul_t4_eq_independent (a b : Std.U16) :
    tower.mul_t4 a b = .ok (pureMulT4 a b) := by
  let alo : Std.U8 := UScalar.cast .U8 (a &&& 255#u16)
  let ahi : Std.U8 := UScalar.cast .U8 ((⟨a.bv >>> 8⟩ : Std.U16) &&& 255#u16)
  let blo : Std.U8 := UScalar.cast .U8 (b &&& 255#u16)
  let bhi : Std.U8 := UScalar.cast .U8 ((⟨b.bv >>> 8⟩ : Std.U16) &&& 255#u16)
  let p := pureGf256Mul alo blo
  have hp := mul_t3_eq_independent alo blo
  let q := pureGf256Mul ahi bhi
  have hq := mul_t3_eq_independent ahi bhi
  let r := pureGf256Mul (alo ^^^ ahi) (blo ^^^ bhi)
  have hr := mul_t3_eq_independent (alo ^^^ ahi) (blo ^^^ bhi)
  let sx := pureScaleXT3 q
  have hs := scale_x_t3_eq_independent q
  have ha : (a >>> 8#i32 : Result Std.U16) = .ok ⟨a.bv >>> 8⟩ := rfl
  have hb : (b >>> 8#i32 : Result Std.U16) = .ok ⟨b.bv >>> 8⟩ := rfl
  change tower.mul_t4 a b = .ok (⟨(UScalar.cast .U16 (p ^^^ q)).bv ||| ((UScalar.cast .U16 (r ^^^ p ^^^ q ^^^ sx)).bv <<< 8)⟩)
  unfold tower.mul_t4
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step ha
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hb
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hp
  apply bind_ok_step hq
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hr
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hs
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  rfl

@[expose] def pureScaleXT4 (a : Std.U16) : Std.U16 :=
  let hi : Std.U8 := UScalar.cast .U8 ((⟨a.bv >>> 8⟩ : Std.U16) &&& 255#u16)
  let sx := pureScaleXT3 hi
  ⟨(UScalar.cast .U16 hi).bv ||| ((UScalar.cast .U16 ((UScalar.cast .U8 (a &&& 255#u16)) ^^^ sx)).bv <<< 8)⟩

theorem scale_x_t4_eq_independent (a : Std.U16) :
    tower.scale_x_t4 a = .ok (pureScaleXT4 a) := by
  let hi : Std.U8 := UScalar.cast .U8 ((⟨a.bv >>> 8⟩ : Std.U16) &&& 255#u16)
  let sx := pureScaleXT3 hi
  have hs := scale_x_t3_eq_independent hi
  have ha : (a >>> 8#i32 : Result Std.U16) = .ok ⟨a.bv >>> 8⟩ := rfl
  change tower.scale_x_t4 a = .ok (⟨(UScalar.cast .U16 hi).bv ||| ((UScalar.cast .U16 ((UScalar.cast .U8 (a &&& 255#u16)) ^^^ sx)).bv <<< 8)⟩)
  unfold tower.scale_x_t4
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step ha
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hs
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  rfl

@[expose] def pureMulT5 (a b : Std.U32) : Std.U32 :=
  let alo : Std.U16 := UScalar.cast .U16 (a &&& 65535#u32)
  let ahi : Std.U16 := UScalar.cast .U16 ((⟨a.bv >>> 16⟩ : Std.U32) &&& 65535#u32)
  let blo : Std.U16 := UScalar.cast .U16 (b &&& 65535#u32)
  let bhi : Std.U16 := UScalar.cast .U16 ((⟨b.bv >>> 16⟩ : Std.U32) &&& 65535#u32)
  let p := pureMulT4 alo blo
  let q := pureMulT4 ahi bhi
  let r := pureMulT4 (alo ^^^ ahi) (blo ^^^ bhi)
  let sx := pureScaleXT4 q
  ⟨(UScalar.cast .U32 (p ^^^ q)).bv ||| ((UScalar.cast .U32 (r ^^^ p ^^^ q ^^^ sx)).bv <<< 16)⟩

theorem mul_t5_eq_independent (a b : Std.U32) :
    tower.mul_t5 a b = .ok (pureMulT5 a b) := by
  let alo : Std.U16 := UScalar.cast .U16 (a &&& 65535#u32)
  let ahi : Std.U16 := UScalar.cast .U16 ((⟨a.bv >>> 16⟩ : Std.U32) &&& 65535#u32)
  let blo : Std.U16 := UScalar.cast .U16 (b &&& 65535#u32)
  let bhi : Std.U16 := UScalar.cast .U16 ((⟨b.bv >>> 16⟩ : Std.U32) &&& 65535#u32)
  let p := pureMulT4 alo blo
  have hp := mul_t4_eq_independent alo blo
  let q := pureMulT4 ahi bhi
  have hq := mul_t4_eq_independent ahi bhi
  let r := pureMulT4 (alo ^^^ ahi) (blo ^^^ bhi)
  have hr := mul_t4_eq_independent (alo ^^^ ahi) (blo ^^^ bhi)
  let sx := pureScaleXT4 q
  have hs := scale_x_t4_eq_independent q
  have ha : (a >>> 16#i32 : Result Std.U32) = .ok ⟨a.bv >>> 16⟩ := rfl
  have hb : (b >>> 16#i32 : Result Std.U32) = .ok ⟨b.bv >>> 16⟩ := rfl
  change tower.mul_t5 a b = .ok (⟨(UScalar.cast .U32 (p ^^^ q)).bv ||| ((UScalar.cast .U32 (r ^^^ p ^^^ q ^^^ sx)).bv <<< 16)⟩)
  unfold tower.mul_t5
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step ha
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hb
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hp
  apply bind_ok_step hq
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hr
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hs
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  rfl

@[expose] def pureScaleXT5 (a : Std.U32) : Std.U32 :=
  let hi : Std.U16 := UScalar.cast .U16 ((⟨a.bv >>> 16⟩ : Std.U32) &&& 65535#u32)
  let sx := pureScaleXT4 hi
  ⟨(UScalar.cast .U32 hi).bv ||| ((UScalar.cast .U32 ((UScalar.cast .U16 (a &&& 65535#u32)) ^^^ sx)).bv <<< 16)⟩

theorem scale_x_t5_eq_independent (a : Std.U32) :
    tower.scale_x_t5 a = .ok (pureScaleXT5 a) := by
  let hi : Std.U16 := UScalar.cast .U16 ((⟨a.bv >>> 16⟩ : Std.U32) &&& 65535#u32)
  let sx := pureScaleXT4 hi
  have hs := scale_x_t4_eq_independent hi
  have ha : (a >>> 16#i32 : Result Std.U32) = .ok ⟨a.bv >>> 16⟩ := rfl
  change tower.scale_x_t5 a = .ok (⟨(UScalar.cast .U32 hi).bv ||| ((UScalar.cast .U32 ((UScalar.cast .U16 (a &&& 65535#u32)) ^^^ sx)).bv <<< 16)⟩)
  unfold tower.scale_x_t5
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step ha
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hs
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  rfl

@[expose] def pureMulT6 (a b : Std.U64) : Std.U64 :=
  let alo : Std.U32 := UScalar.cast .U32 (a &&& 4294967295#u64)
  let ahi : Std.U32 := UScalar.cast .U32 ((⟨a.bv >>> 32⟩ : Std.U64) &&& 4294967295#u64)
  let blo : Std.U32 := UScalar.cast .U32 (b &&& 4294967295#u64)
  let bhi : Std.U32 := UScalar.cast .U32 ((⟨b.bv >>> 32⟩ : Std.U64) &&& 4294967295#u64)
  let p := pureMulT5 alo blo
  let q := pureMulT5 ahi bhi
  let r := pureMulT5 (alo ^^^ ahi) (blo ^^^ bhi)
  let sx := pureScaleXT5 q
  ⟨(UScalar.cast .U64 (p ^^^ q)).bv ||| ((UScalar.cast .U64 (r ^^^ p ^^^ q ^^^ sx)).bv <<< 32)⟩

theorem mul_t6_eq_independent (a b : Std.U64) :
    tower.mul_t6 a b = .ok (pureMulT6 a b) := by
  let alo : Std.U32 := UScalar.cast .U32 (a &&& 4294967295#u64)
  let ahi : Std.U32 := UScalar.cast .U32 ((⟨a.bv >>> 32⟩ : Std.U64) &&& 4294967295#u64)
  let blo : Std.U32 := UScalar.cast .U32 (b &&& 4294967295#u64)
  let bhi : Std.U32 := UScalar.cast .U32 ((⟨b.bv >>> 32⟩ : Std.U64) &&& 4294967295#u64)
  let p := pureMulT5 alo blo
  have hp := mul_t5_eq_independent alo blo
  let q := pureMulT5 ahi bhi
  have hq := mul_t5_eq_independent ahi bhi
  let r := pureMulT5 (alo ^^^ ahi) (blo ^^^ bhi)
  have hr := mul_t5_eq_independent (alo ^^^ ahi) (blo ^^^ bhi)
  let sx := pureScaleXT5 q
  have hs := scale_x_t5_eq_independent q
  have ha : (a >>> 32#i32 : Result Std.U64) = .ok ⟨a.bv >>> 32⟩ := rfl
  have hb : (b >>> 32#i32 : Result Std.U64) = .ok ⟨b.bv >>> 32⟩ := rfl
  change tower.mul_t6 a b = .ok (⟨(UScalar.cast .U64 (p ^^^ q)).bv ||| ((UScalar.cast .U64 (r ^^^ p ^^^ q ^^^ sx)).bv <<< 32)⟩)
  unfold tower.mul_t6
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step ha
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hb
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hp
  apply bind_ok_step hq
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hr
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hs
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  rfl

@[expose] def pureScaleXT6 (a : Std.U64) : Std.U64 :=
  let hi : Std.U32 := UScalar.cast .U32 ((⟨a.bv >>> 32⟩ : Std.U64) &&& 4294967295#u64)
  let sx := pureScaleXT5 hi
  ⟨(UScalar.cast .U64 hi).bv ||| ((UScalar.cast .U64 ((UScalar.cast .U32 (a &&& 4294967295#u64)) ^^^ sx)).bv <<< 32)⟩

theorem scale_x_t6_eq_independent (a : Std.U64) :
    tower.scale_x_t6 a = .ok (pureScaleXT6 a) := by
  let hi : Std.U32 := UScalar.cast .U32 ((⟨a.bv >>> 32⟩ : Std.U64) &&& 4294967295#u64)
  let sx := pureScaleXT5 hi
  have hs := scale_x_t5_eq_independent hi
  have ha : (a >>> 32#i32 : Result Std.U64) = .ok ⟨a.bv >>> 32⟩ := rfl
  change tower.scale_x_t6 a = .ok (⟨(UScalar.cast .U64 hi).bv ||| ((UScalar.cast .U64 ((UScalar.cast .U32 (a &&& 4294967295#u64)) ^^^ sx)).bv <<< 32)⟩)
  unfold tower.scale_x_t6
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step ha
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hs
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  rfl

@[expose] def pureTower128Mul (a b : Std.U128) : Std.U128 :=
  let alo : Std.U64 := UScalar.cast .U64 (a &&& 18446744073709551615#u128)
  let ahi : Std.U64 := UScalar.cast .U64 ((⟨a.bv >>> 64⟩ : Std.U128) &&& 18446744073709551615#u128)
  let blo : Std.U64 := UScalar.cast .U64 (b &&& 18446744073709551615#u128)
  let bhi : Std.U64 := UScalar.cast .U64 ((⟨b.bv >>> 64⟩ : Std.U128) &&& 18446744073709551615#u128)
  let p := pureMulT6 alo blo
  let q := pureMulT6 ahi bhi
  let r := pureMulT6 (alo ^^^ ahi) (blo ^^^ bhi)
  let sx := pureScaleXT6 q
  ⟨(UScalar.cast .U128 (p ^^^ q)).bv ||| ((UScalar.cast .U128 (r ^^^ p ^^^ q ^^^ sx)).bv <<< 64)⟩

theorem tower128_mul_eq_independent (a b : Std.U128) :
    tower.tower128_mul a b = .ok (pureTower128Mul a b) := by
  let alo : Std.U64 := UScalar.cast .U64 (a &&& 18446744073709551615#u128)
  let ahi : Std.U64 := UScalar.cast .U64 ((⟨a.bv >>> 64⟩ : Std.U128) &&& 18446744073709551615#u128)
  let blo : Std.U64 := UScalar.cast .U64 (b &&& 18446744073709551615#u128)
  let bhi : Std.U64 := UScalar.cast .U64 ((⟨b.bv >>> 64⟩ : Std.U128) &&& 18446744073709551615#u128)
  let p := pureMulT6 alo blo
  have hp := mul_t6_eq_independent alo blo
  let q := pureMulT6 ahi bhi
  have hq := mul_t6_eq_independent ahi bhi
  let r := pureMulT6 (alo ^^^ ahi) (blo ^^^ bhi)
  have hr := mul_t6_eq_independent (alo ^^^ ahi) (blo ^^^ bhi)
  let sx := pureScaleXT6 q
  have hs := scale_x_t6_eq_independent q
  have ha : (a >>> 64#i32 : Result Std.U128) = .ok ⟨a.bv >>> 64⟩ := rfl
  have hb : (b >>> 64#i32 : Result Std.U128) = .ok ⟨b.bv >>> 64⟩ := rfl
  change tower.tower128_mul a b = .ok (⟨(UScalar.cast .U128 (p ^^^ q)).bv ||| ((UScalar.cast .U128 (r ^^^ p ^^^ q ^^^ sx)).bv <<< 64)⟩)
  unfold tower.tower128_mul
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step ha
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hb
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hp
  apply bind_ok_step hq
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hr
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hs
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  rfl


theorem pureMulT4_comm (a b : Std.U16) : pureMulT4 a b = pureMulT4 b a := by
  simp only [pureMulT4, pureGf256Mul_comm]

theorem pureMulT5_comm (a b : Std.U32) : pureMulT5 a b = pureMulT5 b a := by
  simp only [pureMulT5, pureMulT4_comm]

theorem pureMulT6_comm (a b : Std.U64) : pureMulT6 a b = pureMulT6 b a := by
  simp only [pureMulT6, pureMulT5_comm]

theorem pureTower128Mul_comm (a b : Std.U128) : pureTower128Mul a b = pureTower128Mul b a := by
  simp only [pureTower128Mul, pureMulT6_comm]

theorem tower128_mul_comm (a b : tower.Tower128) :
    tower.tower128_mul a b = tower.tower128_mul b a := by
  rw [tower128_mul_eq_independent, tower128_mul_eq_independent, pureTower128Mul_comm]

/-- Basis-sensitive check: the degree-two generator squares to 1 + αX. -/
theorem tower_basis_square_vector : pureMulT2 4#u8 4#u8 = 9#u8 := by decide

/-- This distinguishes the stored Wiedemann basis from X² + X + α. -/
theorem tower_basis_is_not_untranslated_artin_schreier :
    pureMulT2 4#u8 4#u8 ≠ 6#u8 := by decide


theorem pureMulT4_zero (a : Std.U16) : pureMulT4 a 0#u16 = 0#u16 := by
  let lo : Std.U8 := UScalar.cast .U8 (a &&& 255#u16)
  let hi : Std.U8 := UScalar.cast .U8 ((⟨a.bv >>> 8⟩ : Std.U16) &&& 255#u16)
  change (⟨(UScalar.cast .U16 ((pureGf256Mul lo 0#u8) ^^^ (pureGf256Mul hi 0#u8))).bv |||
    ((UScalar.cast .U16 ((pureGf256Mul (lo ^^^ hi) 0#u8) ^^^ (pureGf256Mul lo 0#u8) ^^^ (pureGf256Mul hi 0#u8) ^^^ pureScaleXT3 (pureGf256Mul hi 0#u8))).bv <<< 8)⟩ : Std.U16) = 0#u16
  rw [pureGf256Mul_zero lo, pureGf256Mul_zero hi, pureGf256Mul_zero (lo ^^^ hi)]
  rfl

theorem pureMulT5_zero (a : Std.U32) : pureMulT5 a 0#u32 = 0#u32 := by
  let lo : Std.U16 := UScalar.cast .U16 (a &&& 65535#u32)
  let hi : Std.U16 := UScalar.cast .U16 ((⟨a.bv >>> 16⟩ : Std.U32) &&& 65535#u32)
  change (⟨(UScalar.cast .U32 ((pureMulT4 lo 0#u16) ^^^ (pureMulT4 hi 0#u16))).bv |||
    ((UScalar.cast .U32 ((pureMulT4 (lo ^^^ hi) 0#u16) ^^^ (pureMulT4 lo 0#u16) ^^^ (pureMulT4 hi 0#u16) ^^^ pureScaleXT4 (pureMulT4 hi 0#u16))).bv <<< 16)⟩ : Std.U32) = 0#u32
  rw [pureMulT4_zero lo, pureMulT4_zero hi, pureMulT4_zero (lo ^^^ hi)]
  rfl

theorem pureMulT6_zero (a : Std.U64) : pureMulT6 a 0#u64 = 0#u64 := by
  let lo : Std.U32 := UScalar.cast .U32 (a &&& 4294967295#u64)
  let hi : Std.U32 := UScalar.cast .U32 ((⟨a.bv >>> 32⟩ : Std.U64) &&& 4294967295#u64)
  change (⟨(UScalar.cast .U64 ((pureMulT5 lo 0#u32) ^^^ (pureMulT5 hi 0#u32))).bv |||
    ((UScalar.cast .U64 ((pureMulT5 (lo ^^^ hi) 0#u32) ^^^ (pureMulT5 lo 0#u32) ^^^ (pureMulT5 hi 0#u32) ^^^ pureScaleXT5 (pureMulT5 hi 0#u32))).bv <<< 32)⟩ : Std.U64) = 0#u64
  rw [pureMulT5_zero lo, pureMulT5_zero hi, pureMulT5_zero (lo ^^^ hi)]
  rfl

theorem pureTower128Mul_zero (a : Std.U128) : pureTower128Mul a 0#u128 = 0#u128 := by
  let lo : Std.U64 := UScalar.cast .U64 (a &&& 18446744073709551615#u128)
  let hi : Std.U64 := UScalar.cast .U64 ((⟨a.bv >>> 64⟩ : Std.U128) &&& 18446744073709551615#u128)
  change (⟨(UScalar.cast .U128 ((pureMulT6 lo 0#u64) ^^^ (pureMulT6 hi 0#u64))).bv |||
    ((UScalar.cast .U128 ((pureMulT6 (lo ^^^ hi) 0#u64) ^^^ (pureMulT6 lo 0#u64) ^^^ (pureMulT6 hi 0#u64) ^^^ pureScaleXT6 (pureMulT6 hi 0#u64))).bv <<< 64)⟩ : Std.U128) = 0#u128
  rw [pureMulT6_zero lo, pureMulT6_zero hi, pureMulT6_zero (lo ^^^ hi)]
  rfl

theorem tower128_mul_zero (a : tower.Tower128) :
    tower.tower128_mul a 0#u128 = .ok 0#u128 := by
  rw [tower128_mul_eq_independent, pureTower128Mul_zero]

theorem tower128_mul_small_vectors :
    pureTower128Mul 0#u128 7#u128 = 0#u128 ∧
    pureTower128Mul 1#u128 7#u128 = 7#u128 ∧
    pureTower128Mul 2#u128 2#u128 = 3#u128 := by decide

/--  `verify_mac_2lane` strictly rejects empty opening slices (`&[] -> .ok false`). -/
theorem verify_mac_2lane_rejects_empty
    (alpha_lanes : Array tower.Tower128 2#usize)
    (batch : tower.BdozCommittedBatchOpening2Lane) :
    tower.verify_mac_2lane alpha_lanes batch ⟨[], by decide⟩ = .ok false := rfl

/--  Stateful BDOZ 2-Lane Verifier Session Burn & Secret Key Zeroization Theorem:
    1. Once `session.burned = true`, `verify_mac_2lane_with_burn` unconditionally rejects and
       outputs zeroed `alpha_lanes = [0, 0]`.
    2. Whenever `verify_mac_2lane_with_burn` returns `false` on ANY opening batch, the returned
       session has `burned = true` and `alpha_lanes = [0, 0]` (preventing selective-failure
       oracles on `Δ`). -/
theorem verify_mac_2lane_burn_irreversible
    (session : tower.BdozVerifierSession2Lane)
    (batch : tower.BdozCommittedBatchOpening2Lane)
    (openings : Slice tower.BdozWireOpening2Lane) :
    (session.burned = true →
      tower.verify_mac_2lane_with_burn session batch openings =
        .ok ({ alpha_lanes := Array.make 2#usize [0#u128, 0#u128], burned := true }, false)) ∧
    (∀ session',
      tower.verify_mac_2lane_with_burn session batch openings = .ok (session', false) →
        session'.burned = true ∧
        session'.alpha_lanes = Array.make 2#usize [0#u128, 0#u128]) := by
  refine ⟨?_, ?_⟩
  · intro hb
    unfold tower.verify_mac_2lane_with_burn
    simp [hb]
  · intro session' hres
    unfold tower.verify_mac_2lane_with_burn at hres
    by_cases hb : session.burned = true
    · simp [hb] at hres
      rcases hres with ⟨rfl, _⟩
      exact ⟨rfl, rfl⟩
    · simp [hb, Bind.bind, Result.bind] at hres
      cases hmac : tower.verify_mac_2lane session.alpha_lanes batch openings with
      | fail e => simp [hmac] at hres
      | div => simp [hmac] at hres
      | ok ok1 =>
        simp [hmac] at hres
        cases ok1 with
        | true => simp at hres
        | false =>
          simp at hres
          subst hres
          exact ⟨rfl, rfl⟩

/-! ## Section 4: Pillar E — 2-of-3 Replicated Secret Sharing (`RSS`) Gate Homomorphism -/

/-- Over Aeneas-extracted `threshold.rss_and_gate`, for **every** pair of 64-bit replicated shares
    `a, b` and **every** zero-mask seed triple `(r0, r1, r2)`, reconstructing the output share
    equals the exact bitwise AND `(rss_reconstruct a) &&& (rss_reconstruct b)` across all 64 bits. -/
theorem rss_and_gate_spec
    (a b : threshold.RssShare64) (seeds : threshold.RssZeroSeeds64) :
    ∃ (c : threshold.RssShare64) (va vb vc : Std.U64),
      threshold.rss_and_gate a b seeds = .ok c ∧
      threshold.rss_reconstruct a = .ok va ∧
      threshold.rss_reconstruct b = .ok vb ∧
      threshold.rss_reconstruct c = .ok vc ∧
      vc = (va &&& vb) := by
  refine ⟨_, _, _, _, rfl, rfl, rfl, rfl, ?_⟩
  apply UScalar.ext
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [UScalar.bv_and, UScalar.bv_xor,
    BitVec.getLsbD_xor, BitVec.getLsbD_and]
  generalize a.x0.bv.getLsbD i = a0
  generalize a.x1.bv.getLsbD i = a1
  generalize a.x2.bv.getLsbD i = a2
  generalize b.x0.bv.getLsbD i = b0
  generalize b.x1.bv.getLsbD i = b1
  generalize b.x2.bv.getLsbD i = b2
  generalize seeds.r0.bv.getLsbD i = r0
  generalize seeds.r1.bv.getLsbD i = r1
  generalize seeds.r2.bv.getLsbD i = r2
  have hcancel : ∀ u0 u1 u2 : Bool,
      (((u0 ^^ (r0 ^^ r1)) ^^ (u1 ^^ (r1 ^^ r2))) ^^ (u2 ^^ (r2 ^^ r0))) = ((u0 ^^ u1) ^^ u2) := by
    intro u0 u1 u2
    cases u0 <;> cases u1 <;> cases u2 <;> cases r0 <;> cases r1 <;> cases r2 <;> rfl
  rw [hcancel]
  cases a0 <;> cases a1 <;> cases a2 <;> cases b0 <;> cases b1 <;> cases b2 <;> rfl

private theorem allOnes64_bit (i : Nat) (hi : i < 64) :
    (BitVec.allOnes 64).getLsbD i = true := by
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _ | 24, _ | 25, _ | 26, _ | 27, _ | 28, _ | 29, _ | 30, _ | 31, _ | 32, _ | 33, _ | 34, _ | 35, _ | 36, _ | 37, _ | 38, _ | 39, _ | 40, _ | 41, _ | 42, _ | 43, _ | 44, _ | 45, _ | 46, _ | 47, _ | 48, _ | 49, _ | 50, _ | 51, _ | 52, _ | 53, _ | 54, _ | 55, _ | 56, _ | 57, _ | 58, _ | 59, _ | 60, _ | 61, _ | 62, _ | 63, _ => rfl
  | n + 64, hi => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 64 n) hi)

/-- Over Aeneas-extracted `threshold.rss_keccak_chi_lane`, reconstructing the output share equals
    the exact Keccak-f[1600] $\chi$ non-linear lane formula `va ^^^ ((~~~ vb) &&& vc)`. -/
theorem rss_keccak_chi_lane_spec
    (a b c : threshold.RssShare64) (seeds : threshold.RssZeroSeeds64) :
    ∃ (out : threshold.RssShare64) (va vb vc vout : Std.U64),
      threshold.rss_keccak_chi_lane a b c seeds = .ok out ∧
      threshold.rss_reconstruct a = .ok va ∧
      threshold.rss_reconstruct b = .ok vb ∧
      threshold.rss_reconstruct c = .ok vc ∧
      threshold.rss_reconstruct out = .ok vout ∧
      vout = (va ^^^ ((~~~ vb) &&& vc)) := by
  unfold threshold.rss_keccak_chi_lane threshold.rss_not
  dsimp only [Bind.bind, Result.bind, lift]
  obtain ⟨and_sh, vnb, vc, vand, hand, hvnb, hvc, hvand, hand_eq⟩ :=
    rss_and_gate_spec { b with x0 := ~~~ b.x0 } c seeds
  rw [hand]; dsimp only [Result.bind]
  refine ⟨_, _, _, _, _, rfl, rfl, rfl, hvc, rfl, ?_⟩
  have hvnb_eq : (~~~ b.x0 ^^^ b.x1 ^^^ b.x2) = vnb := Result.ok.inj hvnb
  have hvand_eq : (and_sh.x0 ^^^ and_sh.x1 ^^^ and_sh.x2) = vand :=
    Result.ok.inj hvand
  change ((a.x0 ^^^ and_sh.x0) ^^^ (a.x1 ^^^ and_sh.x1)) ^^^
      (a.x2 ^^^ and_sh.x2) = (a.x0 ^^^ a.x1 ^^^ a.x2) ^^^ ((~~~ (b.x0 ^^^ b.x1 ^^^ b.x2)) &&& vc)
  have hrec : ((a.x0 ^^^ and_sh.x0) ^^^ (a.x1 ^^^ and_sh.x1)) ^^^
      (a.x2 ^^^ and_sh.x2) =
      (a.x0 ^^^ a.x1 ^^^ a.x2) ^^^ (and_sh.x0 ^^^ and_sh.x1 ^^^ and_sh.x2) := by
    apply UScalar.ext
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp only [UScalar.bv_xor, BitVec.getLsbD_xor]
    cases a.x0.bv.getLsbD i <;> cases a.x1.bv.getLsbD i <;> cases a.x2.bv.getLsbD i <;>
      cases and_sh.x0.bv.getLsbD i <;> cases and_sh.x1.bv.getLsbD i <;>
      cases and_sh.x2.bv.getLsbD i <;> rfl
  have hnot : (~~~ b.x0 ^^^ b.x1 ^^^ b.x2) = ~~~ (b.x0 ^^^ b.x1 ^^^ b.x2) := by
    apply UScalar.ext
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [UScalar.bv_xor, UScalar.bv_not,
      BitVec.getLsbD_xor, BitVec.not_def, BitVec.getLsbD_xor, allOnes64_bit i hi]
    cases b.x0.bv.getLsbD i <;> cases b.x1.bv.getLsbD i <;> cases b.x2.bv.getLsbD i <;> rfl
  rw [hrec, hvand_eq, hand_eq, ← hvnb_eq, hnot]

private theorem scale_x_t7_total (a : Std.U128) : ∃ c, tower.scale_x_t7 a = .ok c := by
  let hi : Std.U64 := UScalar.cast .U64 ((⟨a.bv >>> 64⟩ : Std.U128) &&& 18446744073709551615#u128)
  obtain ⟨sx, hs⟩ := scale_x_t6_total hi
  have ha : (a >>> 64#i32 : Result Std.U128) = .ok ⟨a.bv >>> 64⟩ := rfl
  refine ⟨⟨(UScalar.cast .U128 hi).bv ||| ((UScalar.cast .U128 ((UScalar.cast .U64 (a &&& 18446744073709551615#u128)) ^^^ sx)).bv <<< 64)⟩, ?_⟩
  unfold tower.scale_x_t7
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step ha
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hs
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  rfl



theorem tower256_mul_total (a b : tower.Tower256) :
    ∃ c, tower.tower256_mul a b = .ok c := by
  obtain ⟨p, hp⟩ := tower128_mul_total a.lo b.lo
  obtain ⟨q, hq⟩ := tower128_mul_total a.hi b.hi
  obtain ⟨r, hr⟩ := tower128_mul_total (a.lo ^^^ a.hi) (b.lo ^^^ b.hi)
  obtain ⟨sx, hs⟩ := scale_x_t7_total q
  refine ⟨⟨p ^^^ q, r ^^^ p ^^^ q ^^^ sx⟩, ?_⟩
  unfold tower.tower256_mul
  apply bind_ok_step hp
  apply bind_ok_step hq
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hr
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hs
  apply bind_ok_step (lift_eq_ok _)
  rfl


theorem rss_reconstruct_share_roundtrip (secret m0 m1 : Std.U64) :
    (threshold.rss_share_u64 secret m0 m1 >>= threshold.rss_reconstruct) = .ok secret := by
  change Result.ok (m0 ^^^ m1 ^^^ (secret ^^^ m0 ^^^ m1)) = Result.ok secret
  congr 1
  apply UScalar.ext
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [UScalar.bv_xor, BitVec.getLsbD_xor]
  cases secret.bv.getLsbD i <;> cases m0.bv.getLsbD i <;> cases m1.bv.getLsbD i <;> rfl

theorem rss_xor_homomorphic (a b : threshold.RssShare64) :
    ∃ va vb, threshold.rss_reconstruct a = .ok va ∧
      threshold.rss_reconstruct b = .ok vb ∧
      (threshold.rss_xor a b >>= threshold.rss_reconstruct) = .ok (va ^^^ vb) := by
  refine ⟨_, _, rfl, rfl, ?_⟩
  change Result.ok ((a.x0 ^^^ b.x0) ^^^ (a.x1 ^^^ b.x1) ^^^ (a.x2 ^^^ b.x2)) = _
  congr 1
  apply UScalar.ext
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [UScalar.bv_xor, BitVec.getLsbD_xor]
  cases a.x0.bv.getLsbD i <;> cases a.x1.bv.getLsbD i <;> cases a.x2.bv.getLsbD i <;>
    cases b.x0.bv.getLsbD i <;> cases b.x1.bv.getLsbD i <;> cases b.x2.bv.getLsbD i <;> rfl

theorem rss_not_spec (a : threshold.RssShare64) :
    ∃ va, threshold.rss_reconstruct a = .ok va ∧
      (threshold.rss_not a >>= threshold.rss_reconstruct) = .ok (~~~ va) := by
  refine ⟨_, rfl, ?_⟩
  change Result.ok (~~~ a.x0 ^^^ a.x1 ^^^ a.x2) = _
  congr 1
  apply UScalar.ext
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [UScalar.bv_xor, UScalar.bv_not, BitVec.getLsbD_xor,
    BitVec.not_def, BitVec.getLsbD_xor, allOnes64_bit i hi]
  cases a.x0.bv.getLsbD i <;> cases a.x1.bv.getLsbD i <;> cases a.x2.bv.getLsbD i <;> rfl

end qsag_verified.proofs
