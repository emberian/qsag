module
/- Unsigned LEB128 and injective length-prefixed byte framing, shared by protocol transcripts
and wire codecs independently of the Keccak permutation. -/
public import Qsag.Tactic.Prelude
public import Qsag.Spec.Encoding

public section
namespace Qsag
set_option autoImplicit false

/-! ## 2. Unsigned LEB128 & Self-Delimiting Multi-Field Byte Framing (`encodeMultiFrame_injective`) -/

@[expose] def leb128Aux : Nat → Nat → List UInt8
  | 0, n => [UInt8.ofNat (n % 128)]
  | fuel + 1, n =>
    if n < 128 then [UInt8.ofNat n]
    else UInt8.ofNat (128 + n % 128) :: leb128Aux fuel (n / 128)

theorem leb128Aux_zero (n : Nat) : leb128Aux 0 n = [UInt8.ofNat (n % 128)] := by rfl
theorem leb128Aux_succ (fuel n : Nat) : leb128Aux (fuel + 1) n =
    if n < 128 then [UInt8.ofNat n]
    else UInt8.ofNat (128 + n % 128) :: leb128Aux fuel (n / 128) := by rfl

/-- Canonical unsigned LEB128 encoding matching `push_leb128` in Rust. -/
@[expose] def leb128 (n : Nat) : List UInt8 :=
  leb128Aux n n

private theorem leb128Aux_prefix_inj :
    ∀ {f₁ f₂ n₁ n₂ : Nat} {r₁ r₂ : List UInt8},
      n₁ ≤ f₁ → n₂ ≤ f₂ →
      leb128Aux f₁ n₁ ++ r₁ = leb128Aux f₂ n₂ ++ r₂ →
      n₁ = n₂ ∧ r₁ = r₂
  | 0, 0, n₁, n₂, r₁, r₂, hn₁, hn₂, hEq => by
    have z₁ : n₁ = 0 := by omega
    have z₂ : n₂ = 0 := by omega
    subst z₁ z₂
    simp only [leb128Aux, List.singleton_append, List.cons.injEq] at hEq
    exact ⟨rfl, hEq.2⟩
  | 0, f₂ + 1, n₁, n₂, r₁, r₂, hn₁, _, hEq => by
    have z₁ : n₁ = 0 := by omega
    subst z₁
    simp only [leb128Aux] at hEq
    if hlt : n₂ < 128 then
      simp only [hlt, ↓reduceIte, List.singleton_append, List.cons.injEq] at hEq
      have hb := congrArg UInt8.toNat hEq.1
      simp only [UInt8.toNat_ofNat'] at hb
      have h8 : (2 : Nat) ^ 8 = 256 := rfl
      rw [h8] at hb
      exact ⟨by omega, hEq.2⟩
    else
      simp only [hlt, ↓reduceIte, List.cons_append, List.cons.injEq] at hEq
      have hb := congrArg UInt8.toNat hEq.1
      simp only [UInt8.toNat_ofNat'] at hb
      have h8 : (2 : Nat) ^ 8 = 256 := rfl
      rw [h8] at hb
      omega
  | f₁ + 1, 0, n₁, n₂, r₁, r₂, _, hn₂, hEq => by
    have z₂ : n₂ = 0 := by omega
    subst z₂
    simp only [leb128Aux] at hEq
    if hlt : n₁ < 128 then
      simp only [hlt, ↓reduceIte, List.singleton_append, List.cons.injEq] at hEq
      have hb := congrArg UInt8.toNat hEq.1
      simp only [UInt8.toNat_ofNat'] at hb
      have h8 : (2 : Nat) ^ 8 = 256 := rfl
      rw [h8] at hb
      exact ⟨by omega, hEq.2⟩
    else
      simp only [hlt, ↓reduceIte, List.cons_append, List.cons.injEq] at hEq
      have hb := congrArg UInt8.toNat hEq.1
      simp only [UInt8.toNat_ofNat'] at hb
      have h8 : (2 : Nat) ^ 8 = 256 := rfl
      rw [h8] at hb
      omega
  | f₁ + 1, f₂ + 1, n₁, n₂, r₁, r₂, hn₁, hn₂, hEq => by
    simp only [leb128Aux] at hEq
    if h₁ : n₁ < 128 then
      if h₂ : n₂ < 128 then
        simp only [h₁, h₂, ↓reduceIte, List.singleton_append, List.cons.injEq] at hEq
        have hb := congrArg UInt8.toNat hEq.1
        simp only [UInt8.toNat_ofNat'] at hb
        have h8 : (2 : Nat) ^ 8 = 256 := rfl
        rw [h8] at hb
        exact ⟨by omega, hEq.2⟩
      else
        simp only [h₁, h₂, ↓reduceIte, List.cons_append, List.cons.injEq] at hEq
        have hb := congrArg UInt8.toNat hEq.1
        simp only [UInt8.toNat_ofNat'] at hb
        have h8 : (2 : Nat) ^ 8 = 256 := rfl
        rw [h8] at hb
        omega
    else
      if h₂ : n₂ < 128 then
        simp only [h₁, h₂, ↓reduceIte, List.cons_append, List.cons.injEq] at hEq
        have hb := congrArg UInt8.toNat hEq.1
        simp only [UInt8.toNat_ofNat'] at hb
        have h8 : (2 : Nat) ^ 8 = 256 := rfl
        rw [h8] at hb
        omega
      else
        simp only [h₁, h₂, ↓reduceIte, List.cons_append, List.cons.injEq] at hEq
        have hb := congrArg UInt8.toNat hEq.1
        simp only [UInt8.toNat_ofNat'] at hb
        have h8 : (2 : Nat) ^ 8 = 256 := rfl
        rw [h8] at hb
        have hRem : n₁ % 128 = n₂ % 128 := by omega
        obtain ⟨hDiv, hRest⟩ := leb128Aux_prefix_inj (by omega) (by omega) hEq.2
        exact ⟨by omega, hRest⟩

theorem leb128_prefix_inj {n₁ n₂ : Nat} {r₁ r₂ : List UInt8}
    (h : leb128 n₁ ++ r₁ = leb128 n₂ ++ r₂) : n₁ = n₂ ∧ r₁ = r₂ :=
  leb128Aux_prefix_inj (Nat.le_refl n₁) (Nat.le_refl n₂) h

/-- Length-prefixed byte field `leb128(|x|) || x`. -/
@[expose] def encodeListField (x : List UInt8) : List UInt8 :=
  leb128 x.length ++ x

theorem encodeListField_eq (x : List UInt8) : encodeListField x = leb128 x.length ++ x := by rfl

theorem encodeListField_prefix_inj {x y r₁ r₂ : List UInt8}
    (h : encodeListField x ++ r₁ = encodeListField y ++ r₂) : x = y ∧ r₁ = r₂ := by
  simp only [encodeListField, List.append_assoc] at h
  obtain ⟨hLen, hTail⟩ := leb128_prefix_inj h
  exact List.append_inj hTail hLen

@[expose] def encodeByteFields : List (List UInt8) → List UInt8
  | [] => []
  | x :: xs => encodeListField x ++ encodeByteFields xs

theorem encodeByteFields_nil : encodeByteFields [] = [] := by rfl
theorem encodeByteFields_cons (x : List UInt8) (xs : List (List UInt8)) :
    encodeByteFields (x :: xs) = encodeListField x ++ encodeByteFields xs := by rfl

/-- Self-delimiting multi-field byte frame `leb128(count) || leb128(|f₀|) || f₀ || ...`. -/
@[expose] def encodeMultiFrame (fields : List (List UInt8)) : List UInt8 :=
  leb128 fields.length ++ encodeByteFields fields

private theorem encodeByteFields_inj_of_len :
    ∀ {xs ys : List (List UInt8)},
      xs.length = ys.length → encodeByteFields xs = encodeByteFields ys → xs = ys
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hLen, hEq => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hLen
    simp only [encodeByteFields] at hEq
    obtain ⟨hx, hRest⟩ := encodeListField_prefix_inj hEq
    have hTail := encodeByteFields_inj_of_len hLen hRest
    subst hx hTail; rfl

/-- **`encodeMultiFrame_injective`**: self-delimiting field framing is unconditionally injective. -/
theorem encodeMultiFrame_injective {xs ys : List (List UInt8)}
    (h : encodeMultiFrame xs = encodeMultiFrame ys) : xs = ys := by
  obtain ⟨hLen, hBody⟩ := leb128_prefix_inj h
  exact encodeByteFields_inj_of_len hLen hBody

/-- An LEB128 encoding has at least one byte. -/
theorem leb128_length_pos (n : Nat) : 0 < (leb128 n).length := by
  unfold leb128
  cases n with
  | zero => exact Nat.zero_lt_one
  | succ k =>
    unfold leb128Aux
    split <;> exact Nat.succ_pos _

#verify_constructive leb128_prefix_inj encodeListField_prefix_inj encodeMultiFrame_injective leb128_length_pos
end Qsag
end
