module
public import Qsag.Math.Goldilocks
public import Qsag.Spec.Encoding

public section
namespace Qsag

/-- Byte `(n / d) mod 256`; `d` ranges over `256^i`. -/
def leByte (n d : Nat) : UInt8 := UInt8.ofNatLT (n / d % 256) (Nat.mod_lt _ (by decide))

theorem leByte_toNat (n d : Nat) : (leByte n d).toNat = n / d % 256 := by rfl

/-- Value of eight little-endian bytes. -/
def le64Value (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) : Nat :=
  b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat +
    4294967296 * b4.toNat + 1099511627776 * b5.toNat + 281474976710656 * b6.toNat +
    72057594037927936 * b7.toNat

private theorem le64_recompose (n : Nat) (h : n < 18446744073709551616) :
    n / 1 % 256 + 256 * (n / 256 % 256) + 65536 * (n / 65536 % 256) +
      16777216 * (n / 16777216 % 256) + 4294967296 * (n / 4294967296 % 256) +
      1099511627776 * (n / 1099511627776 % 256) +
      281474976710656 * (n / 281474976710656 % 256) +
      72057594037927936 * (n / 72057594037927936 % 256) = n := by
  omega

private theorem le64_digit (v0 v1 v2 v3 v4 v5 v6 v7 : Nat)
    (h0 : v0 < 256) (h1 : v1 < 256) (h2 : v2 < 256) (h3 : v3 < 256)
    (h4 : v4 < 256) (h5 : v5 < 256) (h6 : v6 < 256) (h7 : v7 < 256)
    (N : Nat)
    (hN : N = v0 + 256 * v1 + 65536 * v2 + 16777216 * v3 + 4294967296 * v4 +
      1099511627776 * v5 + 281474976710656 * v6 + 72057594037927936 * v7) :
    N / 1 % 256 = v0 ∧ N / 256 % 256 = v1 ∧ N / 65536 % 256 = v2 ∧
    N / 16777216 % 256 = v3 ∧ N / 4294967296 % 256 = v4 ∧
    N / 1099511627776 % 256 = v5 ∧ N / 281474976710656 % 256 = v6 ∧
    N / 72057594037927936 % 256 = v7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- `field.rs:Goldilocks::to_le_bytes`: eight little-endian bytes of the canonical value. -/
def encodeGoldilocksLe8 (a : Goldilocks) : List UInt8 :=
  [leByte a.val 1, leByte a.val 256, leByte a.val 65536, leByte a.val 16777216,
   leByte a.val 4294967296, leByte a.val 1099511627776, leByte a.val 281474976710656,
   leByte a.val 72057594037927936]

/-- `field.rs:Goldilocks::from_le_bytes_canonical` on the first eight bytes: rejects a limb
    `≥ p` and returns the unconsumed tail. -/
def decodeGoldilocksLe8 : List UInt8 → Option (Goldilocks × List UInt8)
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
    if h : le64Value b0 b1 b2 b3 b4 b5 b6 b7 < goldilocksPrime then
      some (⟨le64Value b0 b1 b2 b3 b4 b5 b6 b7, h⟩, rest)
    else none
  | _ => none

theorem decodeGoldilocksLe8_encode (a : Goldilocks) (rest : List UInt8) :
    decodeGoldilocksLe8 (encodeGoldilocksLe8 a ++ rest) = some (a, rest) := by
  have hv : le64Value (leByte a.val 1) (leByte a.val 256) (leByte a.val 65536)
      (leByte a.val 16777216) (leByte a.val 4294967296) (leByte a.val 1099511627776)
      (leByte a.val 281474976710656) (leByte a.val 72057594037927936) = a.val :=
    le64_recompose a.val (Goldilocks.val_lt_two_pow_64 a)
  have hlt : le64Value (leByte a.val 1) (leByte a.val 256) (leByte a.val 65536)
      (leByte a.val 16777216) (leByte a.val 4294967296) (leByte a.val 1099511627776)
      (leByte a.val 281474976710656) (leByte a.val 72057594037927936) < goldilocksPrime := by
    rw [hv]; exact a.isLt
  show decodeGoldilocksLe8
      (leByte a.val 1 :: leByte a.val 256 :: leByte a.val 65536 :: leByte a.val 16777216 ::
        leByte a.val 4294967296 :: leByte a.val 1099511627776 ::
        leByte a.val 281474976710656 :: leByte a.val 72057594037927936 :: rest) = some (a, rest)
  rw [decodeGoldilocksLe8, dite_eq_left hlt]
  exact congrArg (fun g => some (g, rest)) (Goldilocks.ext hv)

theorem decodeGoldilocksLe8_canonical :
    ∀ (bs : List UInt8) (a : Goldilocks) (rest : List UInt8),
      decodeGoldilocksLe8 bs = some (a, rest) → bs = encodeGoldilocksLe8 a ++ rest
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: r, a, rest, h => by
    rw [decodeGoldilocksLe8] at h
    by_cases hlt : le64Value b0 b1 b2 b3 b4 b5 b6 b7 < goldilocksPrime
    · rw [dite_eq_left hlt] at h
      obtain ⟨ha, hr⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ :=
        le64_digit b0.toNat b1.toNat b2.toNat b3.toNat b4.toNat b5.toNat b6.toNat b7.toNat
          (UInt8.toNat_lt b0) (UInt8.toNat_lt b1) (UInt8.toNat_lt b2) (UInt8.toNat_lt b3)
          (UInt8.toNat_lt b4) (UInt8.toNat_lt b5) (UInt8.toNat_lt b6) (UInt8.toNat_lt b7)
          (le64Value b0 b1 b2 b3 b4 b5 b6 b7) rfl
      rw [← ha, ← hr]
      show b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: r =
        leByte (le64Value b0 b1 b2 b3 b4 b5 b6 b7) 1 ::
        leByte (le64Value b0 b1 b2 b3 b4 b5 b6 b7) 256 ::
        leByte (le64Value b0 b1 b2 b3 b4 b5 b6 b7) 65536 ::
        leByte (le64Value b0 b1 b2 b3 b4 b5 b6 b7) 16777216 ::
        leByte (le64Value b0 b1 b2 b3 b4 b5 b6 b7) 4294967296 ::
        leByte (le64Value b0 b1 b2 b3 b4 b5 b6 b7) 1099511627776 ::
        leByte (le64Value b0 b1 b2 b3 b4 b5 b6 b7) 281474976710656 ::
        leByte (le64Value b0 b1 b2 b3 b4 b5 b6 b7) 72057594037927936 :: r
      rw [UInt8.toNat_inj.mp ((leByte_toNat _ 1).trans e0),
        UInt8.toNat_inj.mp ((leByte_toNat _ 256).trans e1),
        UInt8.toNat_inj.mp ((leByte_toNat _ 65536).trans e2),
        UInt8.toNat_inj.mp ((leByte_toNat _ 16777216).trans e3),
        UInt8.toNat_inj.mp ((leByte_toNat _ 4294967296).trans e4),
        UInt8.toNat_inj.mp ((leByte_toNat _ 1099511627776).trans e5),
        UInt8.toNat_inj.mp ((leByte_toNat _ 281474976710656).trans e6),
        UInt8.toNat_inj.mp ((leByte_toNat _ 72057594037927936).trans e7)]
    · rw [dite_eq_right hlt] at h; cases h
  | [], _, _, h => by cases h
  | [_], _, _, h => by cases h
  | [_, _], _, _, h => by cases h
  | [_, _, _], _, _, h => by cases h
  | [_, _, _, _], _, _, h => by cases h
  | [_, _, _, _, _], _, _, h => by cases h
  | [_, _, _, _, _, _], _, _, h => by cases h
  | [_, _, _, _, _, _, _], _, _, h => by cases h

theorem append_inj_of_eq_len {α : Type} :
    ∀ {l1 r1 l2 r2 : List α},
      l1.length = l2.length →
      l1 ++ r1 = l2 ++ r2 →
      l1 = l2 ∧ r1 = r2
  | [], r1, [], r2, _, hEq => ⟨rfl, hEq⟩
  | _ :: _, _, [], _, hLen, _ => by cases hLen
  | [], _, _ :: _, _, hLen, _ => by cases hLen
  | a :: l1, r1, b :: l2, r2, hLen, hEq => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hLen
    injection hEq with hHead hTail
    obtain ⟨hL, hR⟩ := append_inj_of_eq_len hLen hTail
    exact ⟨by rw [hHead, hL], hR⟩

/-- Canonical little-endian serialization of the field elements in order. -/
def encodeGoldilocksVecLe : List Goldilocks → List UInt8
  | [] => []
  | x :: xs => encodeNatLeBytes 8 x.val ++ encodeGoldilocksVecLe xs

theorem encodeGoldilocksVecLe_length (xs : List Goldilocks) :
    (encodeGoldilocksVecLe xs).length = 8 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [encodeGoldilocksVecLe, List.length_append, List.length_cons, encodeNatLeBytes_length, ih]
    omega

theorem encodeGoldilocksVecLe_injective :
    ∀ {xs ys : List Goldilocks},
      encodeGoldilocksVecLe xs = encodeGoldilocksVecLe ys → xs = ys
  | [], [], _ => rfl
  | [], y :: ys, h => by
    have hL := congrArg List.length h
    rw [encodeGoldilocksVecLe_length, encodeGoldilocksVecLe_length] at hL
    simp at hL
  | x :: xs, [], h => by
    have hL := congrArg List.length h
    rw [encodeGoldilocksVecLe_length, encodeGoldilocksVecLe_length] at hL
    simp at hL
  | x :: xs, y :: ys, h => by
    simp only [encodeGoldilocksVecLe] at h
    have hLen8 : (encodeNatLeBytes 8 x.val).length = (encodeNatLeBytes 8 y.val).length := by
      rw [encodeNatLeBytes_length, encodeNatLeBytes_length]
    obtain ⟨hHead, hTail⟩ := append_inj_of_eq_len hLen8 h
    have hxPow : x.val < 256 ^ 8 := Nat.lt_trans x.isLt (by decide)
    have hyPow : y.val < 256 ^ 8 := Nat.lt_trans y.isLt (by decide)
    have hVal : x.val = y.val := by
      have hd := congrArg decodeNatLeBytes hHead
      rwa [decodeNatLeBytes_encodeNatLeBytes 8 x.val hxPow,
           decodeNatLeBytes_encodeNatLeBytes 8 y.val hyPow] at hd
    rw [Goldilocks.ext hVal, encodeGoldilocksVecLe_injective hTail]

end Qsag
