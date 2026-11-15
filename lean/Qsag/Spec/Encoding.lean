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

set_option autoImplicit false

/-! ## 3. Canonical Fixed-Width & Length-Framed `CanonicalCodec` Combinators -/

/-- Exact `take` on a prefix of known length (`0 Classical.choice`). -/
theorem take_append_exact {α : Type} :
    ∀ (xs ys : List α), (xs ++ ys).take xs.length = xs
  | [], _ => rfl
  | x :: xs, ys => by
    simp only [List.cons_append, List.length_cons, List.take_succ_cons, take_append_exact xs ys]

/-- Exact `drop` on a prefix of known length (`0 Classical.choice`). -/
theorem drop_append_exact {α : Type} :
    ∀ (xs ys : List α), (xs ++ ys).drop xs.length = ys
  | [], _ => rfl
  | _ :: xs, ys => by
    simp only [List.cons_append, List.length_cons, List.drop_succ_cons, drop_append_exact xs ys]

theorem take_append_of_len_eq {α : Type} {xs ys : List α} {n : Nat} (h : xs.length = n) :
    (xs ++ ys).take n = xs := by
  subst h; exact take_append_exact xs ys

theorem drop_append_of_len_eq {α : Type} {xs ys : List α} {n : Nat} (h : xs.length = n) :
    (xs ++ ys).drop n = ys := by
  subst h; exact drop_append_exact xs ys

/-- Prefix concatenation injectivity when prefixes have equal length (`0 Classical.choice`). -/
theorem append_inj_of_len_eq {α : Type} {xs₁ ys₁ xs₂ ys₂ : List α}
    (hlen : xs₁.length = xs₂.length) (heq : xs₁ ++ ys₁ = xs₂ ++ ys₂) :
    xs₁ = xs₂ ∧ ys₁ = ys₂ := by
  have htake := congrArg (List.take xs₁.length) heq
  rw [take_append_exact, take_append_of_len_eq hlen.symm] at htake
  have hdrop := congrArg (List.drop xs₁.length) heq
  rw [drop_append_exact, drop_append_of_len_eq hlen.symm] at hdrop
  exact ⟨htake, hdrop⟩

/-- Canonical fixed-width byte codec (`encode` always emits `width` bytes and round-trips). -/
structure FixedCodec (α : Type) (width : Nat) where
  encode : α → List UInt8
  decode : List UInt8 → Option α
  encode_len : ∀ x : α, (encode x).length = width
  decode_encode : ∀ x : α, decode (encode x) = some x

/-- Every `FixedCodec` has a strictly injective `encode` function. -/
theorem FixedCodec.encode_injective {α : Type} {width : Nat}
    (c : FixedCodec α width) {x y : α} (h : c.encode x = c.encode y) : x = y := by
  have hd := congrArg c.decode h
  rw [c.decode_encode, c.decode_encode] at hd
  injection hd

/-- Every `FixedCodec` is prefix-free injective when concatenated with arbitrary suffixes! -/
theorem FixedCodec.prefix_injective {α : Type} {width : Nat}
    (c : FixedCodec α width) {x y : α} {rest₁ rest₂ : List UInt8}
    (h : c.encode x ++ rest₁ = c.encode y ++ rest₂) :
    x = y ∧ rest₁ = rest₂ := by
  have hLenEq : (c.encode x).length = (c.encode y).length := by
    rw [c.encode_len, c.encode_len]
  obtain ⟨hEnc, hRest⟩ := append_inj_of_len_eq hLenEq h
  exact ⟨c.encode_injective hEnc, hRest⟩

/-- Stream-decode a `FixedCodec` prefix, returning `(value, remainingBytes)`. -/
def FixedCodec.decodePrefix {α : Type} {width : Nat}
    (c : FixedCodec α width) (buf : List UInt8) : Option (α × List UInt8) :=
  if buf.length < width then
    none
  else
    match c.decode (buf.take width) with
    | some x => some (x, buf.drop width)
    | none => none

theorem FixedCodec.decodePrefix_append {α : Type} {width : Nat}
    (c : FixedCodec α width) (x : α) (rest : List UInt8) :
    c.decodePrefix (c.encode x ++ rest) = some (x, rest) := by
  unfold FixedCodec.decodePrefix
  have hNotLt : ¬ (c.encode x ++ rest).length < width := by
    rw [List.length_append, c.encode_len]
    omega
  simp only [hNotLt, ↓reduceIte, take_append_of_len_eq (c.encode_len x),
    drop_append_of_len_eq (c.encode_len x), c.decode_encode]

/-- **Concatenation Combinator (`FixedCodec.pair`)**:
    Composes `FixedCodec α w₁` and `FixedCodec β w₂` into `FixedCodec (α × β) (w₁ + w₂)`
    with proven round-trip and strict concatenation injectivity via `take`/`drop`. -/
@[expose]
def FixedCodec.pair {α β : Type} {w₁ w₂ : Nat}
    (c₁ : FixedCodec α w₁) (c₂ : FixedCodec β w₂) : FixedCodec (α × β) (w₁ + w₂) where
  encode p := c₁.encode p.1 ++ c₂.encode p.2
  decode bs :=
    if bs.length == w₁ + w₂ then
      match c₁.decode (bs.take w₁), c₂.decode (bs.drop w₁) with
      | some a, some b => some (a, b)
      | _, _ => none
    else
      none
  encode_len p := by
    rw [List.length_append, c₁.encode_len, c₂.encode_len]
  decode_encode p := by
    rcases p with ⟨a, b⟩
    have hLen : (c₁.encode a ++ c₂.encode b).length = w₁ + w₂ := by
      rw [List.length_append, c₁.encode_len, c₂.encode_len]
    have hBeq : ((c₁.encode a ++ c₂.encode b).length == w₁ + w₂) = true := by
      rw [hLen]; exact Nat.beq_refl _
    simp only [hBeq, ↓reduceIte, take_append_of_len_eq (c₁.encode_len a),
      drop_append_of_len_eq (c₁.encode_len a), c₁.decode_encode, c₂.decode_encode]

theorem FixedCodec.pair_encode_injective {α β : Type} {w₁ w₂ : Nat}
    (c₁ : FixedCodec α w₁) (c₂ : FixedCodec β w₂) {p₁ p₂ : α × β}
    (h : (c₁.pair c₂).encode p₁ = (c₁.pair c₂).encode p₂) : p₁ = p₂ :=
  (c₁.pair c₂).encode_injective h

/-! ### Ready-to-Use Fixed-Width Primitive Codecs (`u8`, `u32be`, `u64le`, `u64be`, `bytes`) -/

private theorem uint8_toNat_ofNat_lt {m : Nat} (hm : m < 256) :
    (UInt8.ofNat m).toNat = m := by
  change (BitVec.ofNat 8 m).toNat = m
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt hm

private theorem uint8_ofNat_toNat (b : UInt8) : UInt8.ofNat b.toNat = b := by
  apply UInt8.eq_of_toBitVec_eq
  apply BitVec.eq_of_toNat_eq
  change (BitVec.ofNat 8 b.toBitVec.toNat).toNat = b.toBitVec.toNat
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt b.toBitVec.isLt

/-- Single-byte `FixedCodec UInt8 1`. -/
def FixedCodec.u8 : FixedCodec UInt8 1 where
  encode b := [b]
  decode
    | [b] => some b
    | _ => none
  encode_len _ := rfl
  decode_encode _ := rfl

/-- Fixed-length byte-slice `FixedCodec { bs : List UInt8 // bs.length = width } width`. -/
def FixedCodec.bytes (width : Nat) :
    FixedCodec { bs : List UInt8 // bs.length = width } width where
  encode s := s.val
  decode bs :=
    if h : bs.length = width then some ⟨bs, h⟩ else none
  encode_len s := s.property
  decode_encode s := by
    rcases s with ⟨bs, h⟩
    simp only [h, ↓reduceDIte]

/-- Canonical 8-byte little-endian `FixedCodec UInt64 8`. -/
def FixedCodec.u64le : FixedCodec UInt64 8 where
  encode x := encodeNatLeBytes 8 x.toNat
  decode bs :=
    if bs.length == 8 then
      let v := decodeNatLeBytes bs
      if h : v < 2 ^ 64 then some (UInt64.ofNatLT v h) else none
    else
      none
  encode_len x := encodeNatLeBytes_length 8 x.toNat
  decode_encode x := by
    have hLen : (encodeNatLeBytes 8 x.toNat).length = 8 := encodeNatLeBytes_length 8 x.toNat
    have hBeq : ((encodeNatLeBytes 8 x.toNat).length == 8) = true := by
      rw [hLen]; exact Nat.beq_refl _
    have hLt64 : x.toNat < 2 ^ 64 := x.toBitVec.isLt
    have hLtPow : x.toNat < 256 ^ 8 := by simpa using hLt64
    have hDec := decodeNatLeBytes_encodeNatLeBytes 8 x.toNat hLtPow
    simp only [hBeq, ↓reduceIte, hDec, hLt64, ↓reduceDIte]
    apply congrArg some
    exact UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq rfl)

/-- Encode a natural number `< 2^32` as 4 big-endian bytes (`u32be`). -/
@[expose]
def encodeU32BeNat (n : Nat) : List UInt8 :=
  [ UInt8.ofNat ((n / 16777216) % 256),
    UInt8.ofNat ((n / 65536) % 256),
    UInt8.ofNat ((n / 256) % 256),
    UInt8.ofNat (n % 256) ]

/-- Decode 4 big-endian bytes into a `Nat`. -/
@[expose]
def decodeU32BeNat : List UInt8 → Option Nat
  | [b3, b2, b1, b0] =>
    some (b3.toNat * 16777216 + b2.toNat * 65536 + b1.toNat * 256 + b0.toNat)
  | _ => none

theorem encodeU32BeNat_length (n : Nat) : (encodeU32BeNat n).length = 4 := rfl

theorem decodeU32BeNat_encodeU32BeNat {n : Nat} (h : n < 2 ^ 32) :
    decodeU32BeNat (encodeU32BeNat n) = some n := by
  dsimp only [encodeU32BeNat, decodeU32BeNat]
  rw [uint8_toNat_ofNat_lt (Nat.mod_lt _ (by decide)),
      uint8_toNat_ofNat_lt (Nat.mod_lt _ (by decide)),
      uint8_toNat_ofNat_lt (Nat.mod_lt _ (by decide)),
      uint8_toNat_ofNat_lt (Nat.mod_lt _ (by decide))]
  apply congrArg some
  omega

/-- Canonical 4-byte big-endian `FixedCodec UInt32 4`. -/
def FixedCodec.u32be : FixedCodec UInt32 4 where
  encode x := encodeU32BeNat x.toNat
  decode bs :=
    match decodeU32BeNat bs with
    | some v => if h : v < 2 ^ 32 then some (UInt32.ofNatLT v h) else none
    | none => none
  encode_len x := encodeU32BeNat_length x.toNat
  decode_encode x := by
    have hLt : x.toNat < 2 ^ 32 := x.toBitVec.isLt
    rw [decodeU32BeNat_encodeU32BeNat hLt]
    simp only [hLt, ↓reduceDIte]
    apply congrArg some
    exact UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq rfl)

/-- Canonical 8-byte big-endian `FixedCodec UInt64 8`. -/
def FixedCodec.u64be : FixedCodec UInt64 8 where
  encode x :=
    encodeU32BeNat (x.toNat / 4294967296) ++ encodeU32BeNat (x.toNat % 4294967296)
  decode bs :=
    if bs.length == 8 then
      match decodeU32BeNat (bs.take 4), decodeU32BeNat (bs.drop 4) with
      | some hi, some lo =>
        let v := hi * 4294967296 + lo
        if h : v < 2 ^ 64 then some (UInt64.ofNatLT v h) else none
      | _, _ => none
    else
      none
  encode_len x := by simp [encodeU32BeNat_length]
  decode_encode x := by
    have hLt64 : x.toNat < 2 ^ 64 := x.toBitVec.isLt
    have hHiLt : x.toNat / 4294967296 < 2 ^ 32 := by omega
    have hLoLt : x.toNat % 4294967296 < 2 ^ 32 := Nat.mod_lt _ (by decide)
    have hLen : (encodeU32BeNat (x.toNat / 4294967296) ++ encodeU32BeNat (x.toNat % 4294967296)).length = 8 := rfl
    have hBeq : ((encodeU32BeNat (x.toNat / 4294967296) ++ encodeU32BeNat (x.toNat % 4294967296)).length == 8) = true := rfl
    simp only [hBeq, ↓reduceIte,
      take_append_of_len_eq (encodeU32BeNat_length _),
      drop_append_of_len_eq (encodeU32BeNat_length _),
      decodeU32BeNat_encodeU32BeNat hHiLt,
      decodeU32BeNat_encodeU32BeNat hLoLt]
    have hRec : (x.toNat / 4294967296) * 4294967296 + x.toNat % 4294967296 = x.toNat := by omega
    simp only [hRec, hLt64, ↓reduceDIte]
    apply congrArg some
    exact UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq rfl)

/-! ### Length-Framed `FramedBytesCodec` (`u32be_len || payload` Prefix-Free Stream Injectivity) -/

/-- Canonical length-framed byte slice: `u32be(payload.length) || payload`. -/
@[expose]
def frameBytes (payload : List UInt8) : List UInt8 :=
  encodeU32BeNat payload.length ++ payload

/-- Stream unframer for `frameBytes`: parses 4-byte `u32be` length `L` and slices `(payload, rest)`. -/
@[expose]
def unframeBytes (buf : List UInt8) : Option (List UInt8 × List UInt8) :=
  if buf.length < 4 then
    none
  else
    match decodeU32BeNat (buf.take 4) with
    | none => none
    | some len =>
      let body := buf.drop 4
      if body.length < len then
        none
      else
        some (body.take len, body.drop len)

namespace FramedBytesCodec

theorem unframe_frame_append {payload : List UInt8} (hLen : payload.length < 2 ^ 32)
    (rest : List UInt8) :
    unframeBytes (frameBytes payload ++ rest) = some (payload, rest) := by
  unfold unframeBytes frameBytes
  rw [List.append_assoc]
  have hNotLt4 : ¬ (encodeU32BeNat payload.length ++ (payload ++ rest)).length < 4 := by
    rw [List.length_append, encodeU32BeNat_length]
    omega
  have hNotLtBody : ¬ (payload ++ rest).length < payload.length := by
    rw [List.length_append]
    omega
  simp only [hNotLt4, ↓reduceIte,
    take_append_of_len_eq (encodeU32BeNat_length payload.length),
    drop_append_of_len_eq (encodeU32BeNat_length payload.length),
    decodeU32BeNat_encodeU32BeNat hLen,
    hNotLtBody, take_append_exact, drop_append_exact]

/-- **Strict Prefix-Free Injectivity (`FramedBytesCodec.prefix_free_injective`)**:
    `frameBytes xs ++ rest₁ = frameBytes ys ++ rest₂ ↔ xs = ys ∧ rest₁ = rest₂`
    for all payloads `< 2^32` bytes and **arbitrary** unframed suffixes `rest₁, rest₂`! -/
theorem prefix_free_injective {xs ys rest₁ rest₂ : List UInt8}
    (hx : xs.length < 2 ^ 32) (hy : ys.length < 2 ^ 32) :
    frameBytes xs ++ rest₁ = frameBytes ys ++ rest₂ ↔ xs = ys ∧ rest₁ = rest₂ := by
  constructor
  · intro hEq
    have hUnf := congrArg unframeBytes hEq
    rw [unframe_frame_append hx rest₁, unframe_frame_append hy rest₂] at hUnf
    injection hUnf with hPair
    injection hPair with hXs hRest
    exact ⟨hXs, hRest⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Standalone `frameBytes` injectivity. -/
theorem frameBytes_injective {xs ys : List UInt8}
    (hx : xs.length < 2 ^ 32) (hy : ys.length < 2 ^ 32)
    (hEq : frameBytes xs = frameBytes ys) : xs = ys := by
  have hApp : frameBytes xs ++ [] = frameBytes ys ++ [] := by simpa using hEq
  exact ((prefix_free_injective hx hy).mp hApp).1

end FramedBytesCodec

/-- Concatenate an arbitrary list of length-framed fields `[frameBytes x₁, ..., frameBytes xₖ]`. -/
@[expose]
def concatFramed : List (List UInt8) → List UInt8
  | [] => []
  | x :: xs => frameBytes x ++ concatFramed xs

/-- **Multi-Field Preimage Framing Injectivity (`FramedBytesCodec.concatFramed_injective`)**:
    Eliminates multi-field Merkle/transcript/intent/credential preimage collision bugs in 1 line! -/
theorem FramedBytesCodec.concatFramed_injective :
    ∀ {xs ys : List (List UInt8)},
      (∀ x ∈ xs, x.length < 2 ^ 32) →
      (∀ y ∈ ys, y.length < 2 ^ 32) →
      concatFramed xs = concatFramed ys →
      xs = ys
  | [], [], _, _, _ => rfl
  | [], y :: _, _, _, hEq => by
    unfold concatFramed frameBytes encodeU32BeNat at hEq
    cases hEq
  | x :: _, [], _, _, hEq => by
    unfold concatFramed frameBytes encodeU32BeNat at hEq
    cases hEq
  | x :: xs, y :: ys, hx, hy, hEq => by
    dsimp only [concatFramed] at hEq
    have hx0 := hx x (.head xs)
    have hy0 := hy y (.head ys)
    obtain ⟨hHead, hTail⟩ := (FramedBytesCodec.prefix_free_injective hx0 hy0).mp hEq
    subst hHead
    have hRec := FramedBytesCodec.concatFramed_injective
      (fun a ha => hx a (.tail x ha))
      (fun b hb => hy b (.tail x hb))
      hTail
    exact congrArg (x :: ·) hRec

/-! ### Domain-Separated Framing (`DomainSeparatedTag`) -/

/-- Domain-separated length-framed message `frameBytes tag ++ frameBytes payload`. -/
@[expose]
def domainFrame (tag payload : List UInt8) : List UInt8 :=
  frameBytes tag ++ frameBytes payload

/-- Lightweight 1-byte fixed domain prefix `tagByte :: payload`. -/
def taggedFixed (tagByte : UInt8) (payload : List UInt8) : List UInt8 :=
  tagByte :: payload

namespace DomainSeparatedTag

/-- **Cross-Domain Non-Collision (`DomainSeparatedTag.ne_of_tag_ne`)**:
    Distinct domain tags `tag₁ ≠ tag₂` (`< 2^32` bytes) NEVER collide across ANY payloads
    `x, y : List UInt8` (even if `x` and `y` have different types, encodings, or lengths!). -/
theorem ne_of_tag_ne {tag₁ tag₂ : List UInt8}
    (ht₁ : tag₁.length < 2 ^ 32) (ht₂ : tag₂.length < 2 ^ 32)
    (hNe : tag₁ ≠ tag₂) (x y : List UInt8) :
    domainFrame tag₁ x ≠ domainFrame tag₂ y := by
  intro hEq
  unfold domainFrame at hEq
  obtain ⟨hTagEq, _⟩ := (FramedBytesCodec.prefix_free_injective ht₁ ht₂).mp hEq
  exact hNe hTagEq

/-- Full joint injectivity of `domainFrame` on both `(tag, payload)`. -/
theorem injective {tag₁ tag₂ x y : List UInt8}
    (ht₁ : tag₁.length < 2 ^ 32) (ht₂ : tag₂.length < 2 ^ 32)
    (hx : x.length < 2 ^ 32) (hy : y.length < 2 ^ 32) :
    domainFrame tag₁ x = domainFrame tag₂ y ↔ tag₁ = tag₂ ∧ x = y := by
  unfold domainFrame
  constructor
  · intro hEq
    obtain ⟨hTag, hPay⟩ := (FramedBytesCodec.prefix_free_injective ht₁ ht₂).mp hEq
    exact ⟨hTag, FramedBytesCodec.frameBytes_injective hx hy hPay⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Distinct 1-byte fixed tags never collide. -/
theorem taggedFixed_ne_of_ne {t₁ t₂ : UInt8} (hNe : t₁ ≠ t₂) (x y : List UInt8) :
    taggedFixed t₁ x ≠ taggedFixed t₂ y := by
  intro hEq
  injection hEq with hTag _
  exact hNe hTag

end DomainSeparatedTag

end Qsag
end
