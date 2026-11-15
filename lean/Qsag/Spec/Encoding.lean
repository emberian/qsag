module
public import Qsag.Tactic.Prelude

public section
namespace Qsag
/-- Recursive `w`-byte little-endian `Nat` encoder (`0 Classical.choice`). -/
@[expose] def encodeNatLeBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | w + 1, n => UInt8.ofNat (n % 256) :: encodeNatLeBytes w (n / 256)

/-- Recursive little-endian byte list `Nat` decoder. -/
@[expose] def decodeNatLeBytes : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * decodeNatLeBytes bs

theorem encodeNatLeBytes_length : ∀ (w n : Nat), (encodeNatLeBytes w n).length = w
  | 0, _ => rfl
  | w + 1, n => congrArg Nat.succ (encodeNatLeBytes_length w (n / 256))

theorem decodeNatLeBytes_encodeNatLeBytes :
    ∀ (w n : Nat), n < 256 ^ w → decodeNatLeBytes (encodeNatLeBytes w n) = n
  | 0, n, h => by
    simp only [Nat.pow_zero] at h
    have hn : n = 0 := by omega
    subst hn; rfl
  | w + 1, n, h => by
    simp only [encodeNatLeBytes, decodeNatLeBytes]
    have hModLt : n % 256 < 256 := Nat.mod_lt n (by decide)
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt hModLt]
    have hDivLt : n / 256 < 256 ^ w := by
      rw [Nat.pow_succ] at h
      omega
    rw [decodeNatLeBytes_encodeNatLeBytes w (n / 256) hDivLt]
    omega


/-- The low `w` bytes of `n` in big-endian order. -/
@[expose] def be : Nat → Nat → List UInt8
  | 0, _ => []
  | w + 1, n => be w (n / 256) ++ [UInt8.ofNat (n % 256)]

/-- Big-endian byte list decoded as a natural number. -/
@[expose] def ofBE (bytes : List UInt8) : Nat :=
  bytes.foldl (fun acc b => acc * 256 + b.toNat) 0

@[simp] theorem length_be (w n : Nat) : (be w n).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [be, ih]

theorem be_injective {w n m : Nat} (hn : n < 256 ^ w) (hm : m < 256 ^ w)
    (h : be w n = be w m) : n = m := by
  induction w generalizing n m with
  | zero => simp at hn hm; omega
  | succ w ih =>
    simp only [be] at h
    obtain ⟨hhi, hlo⟩ := List.append_inj h (by simp)
    have hbyte : (UInt8.ofNat (n % 256)).toNat = (UInt8.ofNat (m % 256)).toNat := by
      rw [List.cons.inj hlo |>.1]
    simp only [UInt8.toNat_ofNat'] at hbyte
    have hpow : 256 ^ (w + 1) = 256 ^ w * 256 := Nat.pow_succ ..
    have hn' : n / 256 < 256 ^ w := (Nat.div_lt_iff_lt_mul (by decide)).mpr (hpow ▸ hn)
    have hm' : m / 256 < 256 ^ w := (Nat.div_lt_iff_lt_mul (by decide)).mpr (hpow ▸ hm)
    have hq := ih hn' hm' hhi
    have h8 : (2 : Nat) ^ 8 = 256 := by decide
    rw [h8] at hbyte
    omega

theorem ofBE_append_single (bytes : List UInt8) (b : UInt8) :
    ofBE (bytes ++ [b]) = ofBE bytes * 256 + b.toNat := by
  simp [ofBE, List.foldl_append]

theorem ofBE_be {w n : Nat} (hn : n < 256 ^ w) : ofBE (be w n) = n := by
  induction w generalizing n with
  | zero => simp at hn; subst hn; rfl
  | succ w ih =>
    have hpow : 256 ^ (w + 1) = 256 ^ w * 256 := Nat.pow_succ ..
    have hn' : n / 256 < 256 ^ w := (Nat.div_lt_iff_lt_mul (by decide)).mpr (hpow ▸ hn)
    simp only [be, ofBE_append_single, ih hn', UInt8.toNat_ofNat']
    have h8 : (2 : Nat) ^ 8 = 256 := by decide
    rw [h8]
    omega

private theorem ofBE_lt_aux : ∀ (bytes : List UInt8) (acc : Nat),
    bytes.foldl (fun acc b => acc * 256 + b.toNat) acc < (acc + 1) * 256 ^ bytes.length
  | [], acc => by simp
  | b :: rest, acc => by
    have hb : b.toNat < 256 := b.toNat_lt
    have ih := ofBE_lt_aux rest (acc * 256 + b.toNat)
    simp only [List.foldl_cons, List.length_cons]
    have hle : (acc * 256 + b.toNat + 1) ≤ (acc + 1) * 256 := by omega
    have hmono := Nat.mul_le_mul_right (256 ^ rest.length) hle
    rw [Nat.pow_succ, Nat.mul_comm (256 ^ rest.length) 256, ← Nat.mul_assoc]
    omega

theorem ofBE_lt (bytes : List UInt8) : ofBE bytes < 256 ^ bytes.length := by
  have := ofBE_lt_aux bytes 0
  simpa [ofBE] using this

theorem be_ofBE (xs : List UInt8) : be xs.length (ofBE xs) = xs := by
  suffices h : ∀ ys : List UInt8,
      be ys.reverse.length (ofBE ys.reverse) = ys.reverse by
    simpa only [List.reverse_reverse] using h xs.reverse
  intro ys
  induction ys with
  | nil => rfl
  | cons b ys ih =>
    let zs := ys.reverse
    rw [List.reverse_cons]
    change be (zs ++ [b]).length (ofBE (zs ++ [b])) = zs ++ [b]
    simp only [List.length_append, List.length_singleton, ofBE_append_single, be]
    have hb := b.toNat_lt
    have hdiv : (ofBE zs * 256 + b.toNat) / 256 = ofBE zs := by omega
    have hmod : (ofBE zs * 256 + b.toNat) % 256 = b.toNat := by omega
    rw [hdiv, hmod, ih, UInt8.ofNat_toNat]

end Qsag

public section
namespace Qsag
/-- Full-width digest, salt and MAC carrier. -/
abbrev Digest256 := BitVec 256
end Qsag
end
