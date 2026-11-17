module
/-
# Qsag.Oracle.Keccak — Injective Framing, Keccak-f[1600], SHAKE256 XOF & SP 800-185 cSHAKE256

Self-contained Lean 4.35 sponge and byte-framing foundation (`Init` only, 0 Mathlib, 0 sorry):
1. Big-endian byte codec (`be`, `ofBE`, `be_injective`, `ofBE_be`, `ofBE_lt`).
2. Self-delimiting unsigned LEB128 and multi-field framing (`leb128_prefix_inj`,
   `encodeMultiFrame_injective`) preventing domain-concatenation collisions before hashing.
3. Constructive collision predicates and witnesses (`Collision`, `CollisionAmong`,
   `HashCollisionWitness`).
4. Full 24-round `Keccak-f[1600]` over unboxed 25-lane `KState`, proved bit-exact on $\chi$
   against the boolean MPC gate `keccakChiBit` (`chiLaneBit_eq_keccakChiBit`), paired with
   multi-block arbitrary-length `shake256Xof` (for NIST FIPS 205 `H_msg`, `PRF`, `F`, `H`, `T_l`)
   and NIST SP 800-185 `cshake256Bytes`, verified against official NIST FIPS 202 test vectors.
-/

public import Qsag.Tactic.Prelude
public import Qsag.Spec.Encoding
public import Qsag.Oracle.ByteFraming
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false

/-! ## 1. Fixed-Width Big-Endian Byte Framing & Collision Carriers -/

/-- Byte-oriented hash function `List UInt8 → List UInt8`. -/
abbrev Hash := List UInt8 → List UInt8

/-- Propositional collision of `H`. -/
def Collision (H : Hash) : Prop :=
  ∃ a b : List UInt8, a ≠ b ∧ H a = H b

/-- Scoped propositional collision of `H` restricted to domain predicate `S`. -/
def CollisionAmong (H : Hash) (S : List UInt8 → Prop) : Prop :=
  ∃ a b : List UInt8, S a ∧ S b ∧ a ≠ b ∧ H a = H b

/-- Constructive `Type`-valued collision witness for `0 Classical.choice` reductions. -/
structure HashCollisionWitness (H : Hash) where
  m1 : List UInt8
  m2 : List UInt8
  ne : m1 ≠ m2
  eq : H m1 = H m2
  deriving Repr

theorem HashCollisionWitness.toCollision {H : Hash} (w : HashCollisionWitness H) : Collision H :=
  ⟨w.m1, w.m2, w.ne, w.eq⟩

/-! ## 3. NIST SP 800-185 Framing (`left_encode`, `encode_string`, `bytepad`) -/

private def natBytesLEAux : Nat → Nat → List UInt8
  | 0, _ => []
  | fuel + 1, value =>
    if value = 0 then [] else UInt8.ofNat (value % 256) :: natBytesLEAux fuel (value / 256)

def natBytesBE (value : Nat) : List UInt8 :=
  let little := natBytesLEAux value value
  let nonempty := if little = [] then [0] else little
  nonempty.reverse

def leftEncode (value : Nat) : List UInt8 :=
  let bytes := natBytesBE value
  UInt8.ofNat bytes.length :: bytes

def encodeString (bytes : List UInt8) : List UInt8 :=
  leftEncode (8 * bytes.length) ++ bytes

def bytepad (bytes : List UInt8) (width : Nat) : List UInt8 :=
  if width = 0 then [] else
    let prefixed := leftEncode width ++ bytes
    let zeroCount := (width - prefixed.length % width) % width
    prefixed ++ List.replicate zeroCount 0

/-! ## 4. Full 24-Round `Keccak-f[1600]` over Unboxed 25-Lane `KState` -/

/-- Unboxed 25-lane `Keccak-f[1600]` state (`a(x + 5*y)` is lane `(x, y)`). -/
structure KState where
  a0 : UInt64
  a1 : UInt64
  a2 : UInt64
  a3 : UInt64
  a4 : UInt64
  a5 : UInt64
  a6 : UInt64
  a7 : UInt64
  a8 : UInt64
  a9 : UInt64
  a10 : UInt64
  a11 : UInt64
  a12 : UInt64
  a13 : UInt64
  a14 : UInt64
  a15 : UInt64
  a16 : UInt64
  a17 : UInt64
  a18 : UInt64
  a19 : UInt64
  a20 : UInt64
  a21 : UInt64
  a22 : UInt64
  a23 : UInt64
  a24 : UInt64
  deriving DecidableEq, Repr

def zeroKState : KState :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

@[inline, expose] def rotlK (x k j : UInt64) : UInt64 :=
  (x <<< k) ||| (x >>> j)

theorem rotlK_eq (x k j : UInt64) : rotlK x k j = ((x <<< k) ||| (x >>> j)) := by rfl

@[inline, expose] def thetaS (s : KState) : KState :=
  let c0 := s.a0 ^^^ s.a5 ^^^ s.a10 ^^^ s.a15 ^^^ s.a20
  let c1 := s.a1 ^^^ s.a6 ^^^ s.a11 ^^^ s.a16 ^^^ s.a21
  let c2 := s.a2 ^^^ s.a7 ^^^ s.a12 ^^^ s.a17 ^^^ s.a22
  let c3 := s.a3 ^^^ s.a8 ^^^ s.a13 ^^^ s.a18 ^^^ s.a23
  let c4 := s.a4 ^^^ s.a9 ^^^ s.a14 ^^^ s.a19 ^^^ s.a24
  let d0 := c4 ^^^ rotlK c1 1 63
  let d1 := c0 ^^^ rotlK c2 1 63
  let d2 := c1 ^^^ rotlK c3 1 63
  let d3 := c2 ^^^ rotlK c4 1 63
  let d4 := c3 ^^^ rotlK c0 1 63
  ⟨s.a0 ^^^ d0, s.a1 ^^^ d1, s.a2 ^^^ d2, s.a3 ^^^ d3, s.a4 ^^^ d4,
   s.a5 ^^^ d0, s.a6 ^^^ d1, s.a7 ^^^ d2, s.a8 ^^^ d3, s.a9 ^^^ d4,
   s.a10 ^^^ d0, s.a11 ^^^ d1, s.a12 ^^^ d2, s.a13 ^^^ d3, s.a14 ^^^ d4,
   s.a15 ^^^ d0, s.a16 ^^^ d1, s.a17 ^^^ d2, s.a18 ^^^ d3, s.a19 ^^^ d4,
   s.a20 ^^^ d0, s.a21 ^^^ d1, s.a22 ^^^ d2, s.a23 ^^^ d3, s.a24 ^^^ d4⟩

@[inline, expose] def rhoPiS (s : KState) : KState :=
  ⟨s.a0, rotlK s.a6 44 20, rotlK s.a12 43 21, rotlK s.a18 21 43, rotlK s.a24 14 50,
   rotlK s.a3 28 36, rotlK s.a9 20 44, rotlK s.a10 3 61, rotlK s.a16 45 19, rotlK s.a22 61 3,
   rotlK s.a1 1 63, rotlK s.a7 6 58, rotlK s.a13 25 39, rotlK s.a19 8 56, rotlK s.a20 18 46,
   rotlK s.a4 27 37, rotlK s.a5 36 28, rotlK s.a11 10 54, rotlK s.a17 15 49, rotlK s.a23 56 8,
   rotlK s.a2 62 2, rotlK s.a8 55 9, rotlK s.a14 39 25, rotlK s.a15 41 23, rotlK s.a21 2 62⟩

@[inline, expose] def chiS (s : KState) : KState :=
  ⟨s.a0 ^^^ ((~~~s.a1) &&& s.a2),
   s.a1 ^^^ ((~~~s.a2) &&& s.a3),
   s.a2 ^^^ ((~~~s.a3) &&& s.a4),
   s.a3 ^^^ ((~~~s.a4) &&& s.a0),
   s.a4 ^^^ ((~~~s.a0) &&& s.a1),
   s.a5 ^^^ ((~~~s.a6) &&& s.a7),
   s.a6 ^^^ ((~~~s.a7) &&& s.a8),
   s.a7 ^^^ ((~~~s.a8) &&& s.a9),
   s.a8 ^^^ ((~~~s.a9) &&& s.a5),
   s.a9 ^^^ ((~~~s.a5) &&& s.a6),
   s.a10 ^^^ ((~~~s.a11) &&& s.a12),
   s.a11 ^^^ ((~~~s.a12) &&& s.a13),
   s.a12 ^^^ ((~~~s.a13) &&& s.a14),
   s.a13 ^^^ ((~~~s.a14) &&& s.a10),
   s.a14 ^^^ ((~~~s.a10) &&& s.a11),
   s.a15 ^^^ ((~~~s.a16) &&& s.a17),
   s.a16 ^^^ ((~~~s.a17) &&& s.a18),
   s.a17 ^^^ ((~~~s.a18) &&& s.a19),
   s.a18 ^^^ ((~~~s.a19) &&& s.a15),
   s.a19 ^^^ ((~~~s.a15) &&& s.a16),
   s.a20 ^^^ ((~~~s.a21) &&& s.a22),
   s.a21 ^^^ ((~~~s.a22) &&& s.a23),
   s.a22 ^^^ ((~~~s.a23) &&& s.a24),
   s.a23 ^^^ ((~~~s.a24) &&& s.a20),
   s.a24 ^^^ ((~~~s.a20) &&& s.a21)⟩

/-- Boolean Keccak $\chi$ S-box gate $a \oplus (\neg b \land c)$ evaluated by the MPC engine. -/
@[expose] def keccakChiBit (a b c : Bool) : Bool :=
  a ^^ ((!b) && c)

/-- Bitwise bridge theorem: every bit $i < 64$ of the word-level $\chi$ step equals `keccakChiBit`. -/
theorem chiWordBit_eq_keccakChiBit (w0 w1 w2 : UInt64) (i : Nat) (hi : i < 64) :
    (w0 ^^^ ((~~~w1) &&& w2)).toBitVec.getLsbD i =
      keccakChiBit (w0.toBitVec.getLsbD i) (w1.toBitVec.getLsbD i) (w2.toBitVec.getLsbD i) := by
  simp only [UInt64.toBitVec_xor, UInt64.toBitVec_and, UInt64.toBitVec_not,
    BitVec.getLsbD_xor, BitVec.getLsbD_and, Constructive.getLsbD_not,
    hi, decide_true, Bool.true_and, keccakChiBit]

@[inline, expose] def roundS (s : KState) (rc : UInt64) : KState :=
  let m := chiS (rhoPiS (thetaS s))
  { m with a0 := m.a0 ^^^ rc }

def keccakRoundConstants : List UInt64 := [
  0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000,
  0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
  0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008
]

/-- Full 24-round `Keccak-f[1600]` permutation. -/
@[expose] def keccakF1600 (s : KState) : KState :=
  keccakRoundConstants.foldl roundS s

theorem zeroKState_eq : zeroKState = ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ := by rfl

theorem thetaS_eq (s : KState) :
    thetaS s =
      let c0 := s.a0 ^^^ s.a5 ^^^ s.a10 ^^^ s.a15 ^^^ s.a20
      let c1 := s.a1 ^^^ s.a6 ^^^ s.a11 ^^^ s.a16 ^^^ s.a21
      let c2 := s.a2 ^^^ s.a7 ^^^ s.a12 ^^^ s.a17 ^^^ s.a22
      let c3 := s.a3 ^^^ s.a8 ^^^ s.a13 ^^^ s.a18 ^^^ s.a23
      let c4 := s.a4 ^^^ s.a9 ^^^ s.a14 ^^^ s.a19 ^^^ s.a24
      let d0 := c4 ^^^ rotlK c1 1 63
      let d1 := c0 ^^^ rotlK c2 1 63
      let d2 := c1 ^^^ rotlK c3 1 63
      let d3 := c2 ^^^ rotlK c4 1 63
      let d4 := c3 ^^^ rotlK c0 1 63
      ⟨s.a0 ^^^ d0, s.a1 ^^^ d1, s.a2 ^^^ d2, s.a3 ^^^ d3, s.a4 ^^^ d4,
       s.a5 ^^^ d0, s.a6 ^^^ d1, s.a7 ^^^ d2, s.a8 ^^^ d3, s.a9 ^^^ d4,
       s.a10 ^^^ d0, s.a11 ^^^ d1, s.a12 ^^^ d2, s.a13 ^^^ d3, s.a14 ^^^ d4,
       s.a15 ^^^ d0, s.a16 ^^^ d1, s.a17 ^^^ d2, s.a18 ^^^ d3, s.a19 ^^^ d4,
       s.a20 ^^^ d0, s.a21 ^^^ d1, s.a22 ^^^ d2, s.a23 ^^^ d3, s.a24 ^^^ d4⟩ := by rfl

theorem rhoPiS_eq (s : KState) :
    rhoPiS s =
      ⟨s.a0, rotlK s.a6 44 20, rotlK s.a12 43 21, rotlK s.a18 21 43, rotlK s.a24 14 50,
       rotlK s.a3 28 36, rotlK s.a9 20 44, rotlK s.a10 3 61, rotlK s.a16 45 19, rotlK s.a22 61 3,
       rotlK s.a1 1 63, rotlK s.a7 6 58, rotlK s.a13 25 39, rotlK s.a19 8 56, rotlK s.a20 18 46,
       rotlK s.a4 27 37, rotlK s.a5 36 28, rotlK s.a11 10 54, rotlK s.a17 15 49, rotlK s.a23 56 8,
       rotlK s.a2 62 2, rotlK s.a8 55 9, rotlK s.a14 39 25, rotlK s.a15 41 23, rotlK s.a21 2 62⟩ := by rfl

theorem chiS_eq (s : KState) :
    chiS s =
      ⟨s.a0 ^^^ ((~~~s.a1) &&& s.a2), s.a1 ^^^ ((~~~s.a2) &&& s.a3),
       s.a2 ^^^ ((~~~s.a3) &&& s.a4), s.a3 ^^^ ((~~~s.a4) &&& s.a0),
       s.a4 ^^^ ((~~~s.a0) &&& s.a1), s.a5 ^^^ ((~~~s.a6) &&& s.a7),
       s.a6 ^^^ ((~~~s.a7) &&& s.a8), s.a7 ^^^ ((~~~s.a8) &&& s.a9),
       s.a8 ^^^ ((~~~s.a9) &&& s.a5), s.a9 ^^^ ((~~~s.a5) &&& s.a6),
       s.a10 ^^^ ((~~~s.a11) &&& s.a12), s.a11 ^^^ ((~~~s.a12) &&& s.a13),
       s.a12 ^^^ ((~~~s.a13) &&& s.a14), s.a13 ^^^ ((~~~s.a14) &&& s.a10),
       s.a14 ^^^ ((~~~s.a10) &&& s.a11), s.a15 ^^^ ((~~~s.a16) &&& s.a17),
       s.a16 ^^^ ((~~~s.a17) &&& s.a18), s.a17 ^^^ ((~~~s.a18) &&& s.a19),
       s.a18 ^^^ ((~~~s.a19) &&& s.a15), s.a19 ^^^ ((~~~s.a15) &&& s.a16),
       s.a20 ^^^ ((~~~s.a21) &&& s.a22), s.a21 ^^^ ((~~~s.a22) &&& s.a23),
       s.a22 ^^^ ((~~~s.a23) &&& s.a24), s.a23 ^^^ ((~~~s.a24) &&& s.a20),
       s.a24 ^^^ ((~~~s.a20) &&& s.a21)⟩ := by rfl

theorem roundS_eq (s : KState) (rc : UInt64) :
    roundS s rc = let m := chiS (rhoPiS (thetaS s)); { m with a0 := m.a0 ^^^ rc } := by rfl

theorem keccakF1600_eq (s : KState) : keccakF1600 s = keccakRoundConstants.foldl roundS s := by rfl

theorem keccakRoundConstants_eq : keccakRoundConstants = ([
  0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000,
  0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
  0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008
] : List UInt64) := by rfl

theorem keccakRoundConstants_length : keccakRoundConstants.length = 24 := by rfl

/-! ## 5. 1088-Bit Rate Sponge, Multi-Block `shake256Xof` & `cshake256Bytes` -/

def shake256RateBytes : Nat := 136

@[inline] def loadLe64 (block : List UInt8) (laneIdx : Nat) : UInt64 :=
  let base := 8 * laneIdx
  let b0 := (block.getD base 0).toUInt64
  let b1 := (block.getD (base + 1) 0).toUInt64 <<< 8
  let b2 := (block.getD (base + 2) 0).toUInt64 <<< 16
  let b3 := (block.getD (base + 3) 0).toUInt64 <<< 24
  let b4 := (block.getD (base + 4) 0).toUInt64 <<< 32
  let b5 := (block.getD (base + 5) 0).toUInt64 <<< 40
  let b6 := (block.getD (base + 6) 0).toUInt64 <<< 48
  let b7 := (block.getD (base + 7) 0).toUInt64 <<< 56
  b0 ||| b1 ||| b2 ||| b3 ||| b4 ||| b5 ||| b6 ||| b7

private theorem getD_zipXor_zero : ∀ (xs ys : List UInt8) (k : Nat),
    xs.length = ys.length →
    (List.zipWith (· ^^^ ·) xs ys).getD k 0 = (xs.getD k 0 ^^^ ys.getD k 0)
  | [], [], _, _ => by simp
  | [], _ :: _, _, h => by cases h
  | _ :: _, [], _, h => by cases h
  | _ :: _, _ :: _, 0, _ => rfl
  | _ :: xs, _ :: ys, k + 1, h =>
    getD_zipXor_zero xs ys k (Nat.succ.inj h)

private theorem uint8_toUInt64_msb_false (b : UInt8) (j : Nat) (hj : 8 ≤ j) :
    b.toUInt64.toBitVec.getLsbD j = false := by
  have hLe : 2 ^ 8 ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) hj
  have hDiv : b.toNat / 2 ^ j = 0 := Nat.div_eq_of_lt (Nat.lt_of_lt_of_le b.toNat_lt hLe)
  simp [BitVec.getLsbD, Nat.testBit, Nat.shiftRight_eq_div_pow, hDiv]

private theorem shift_lane_bit (b : UInt8) (sh : UInt64) (i : Nat) (hi : i < 64) (hsh : sh.toNat ≤ 56) :
    (b.toUInt64 <<< sh).toBitVec.getLsbD i =
      if sh.toNat ≤ i ∧ i < sh.toNat + 8 then b.toUInt64.toBitVec.getLsbD (i - sh.toNat) else false := by
  have hMod : sh.toNat % 64 = sh.toNat := Nat.mod_eq_of_lt (by omega)
  rw [UInt64.toBitVec_shiftLeft, BitVec.shiftLeft_eq']
  have hShNat : (sh.toBitVec % 64).toNat = sh.toNat := by
    simp [BitVec.toNat_umod, hMod]
  rw [hShNat, BitVec.getLsbD_shiftLeft]
  simp only [hi, decide_true, Bool.true_and]
  if hLow : i < sh.toNat then
    have hNot : ¬ (sh.toNat ≤ i ∧ i < sh.toNat + 8) := by omega
    simp [hLow, hNot]
  else
    if hHigh : i < sh.toNat + 8 then
      have hYes : sh.toNat ≤ i ∧ i < sh.toNat + 8 := ⟨by omega, hHigh⟩
      simp [hLow, hYes]
    else
      have hNot : ¬ (sh.toNat ≤ i ∧ i < sh.toNat + 8) := by omega
      simp only [hLow, hNot, ↓reduceIte]
      exact uint8_toUInt64_msb_false b (i - sh.toNat) (by omega)

theorem loadLe64_zipXor (b0 b1 : List UInt8) (hLen : b0.length = b1.length) (laneIdx : Nat) :
    loadLe64 (List.zipWith (· ^^^ ·) b0 b1) laneIdx = loadLe64 b0 laneIdx ^^^ loadLe64 b1 laneIdx := by
  unfold loadLe64
  simp only [getD_zipXor_zero b0 b1 _ hLen]
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h0x := fun (z : UInt8) => uint8_toUInt64_msb_false z i
  simp only [UInt64.toBitVec_or, UInt64.toBitVec_xor, BitVec.getLsbD_or, BitVec.getLsbD_xor]
  rw [shift_lane_bit _ 8 i hi (by decide), shift_lane_bit _ 8 i hi (by decide), shift_lane_bit _ 8 i hi (by decide),
      shift_lane_bit _ 16 i hi (by decide), shift_lane_bit _ 16 i hi (by decide), shift_lane_bit _ 16 i hi (by decide),
      shift_lane_bit _ 24 i hi (by decide), shift_lane_bit _ 24 i hi (by decide), shift_lane_bit _ 24 i hi (by decide),
      shift_lane_bit _ 32 i hi (by decide), shift_lane_bit _ 32 i hi (by decide), shift_lane_bit _ 32 i hi (by decide),
      shift_lane_bit _ 40 i hi (by decide), shift_lane_bit _ 40 i hi (by decide), shift_lane_bit _ 40 i hi (by decide),
      shift_lane_bit _ 48 i hi (by decide), shift_lane_bit _ 48 i hi (by decide), shift_lane_bit _ 48 i hi (by decide),
      shift_lane_bit _ 56 i hi (by decide), shift_lane_bit _ 56 i hi (by decide), shift_lane_bit _ 56 i hi (by decide)]
  have s8 : (8 : UInt64).toNat = 8 := rfl
  have s16 : (16 : UInt64).toNat = 16 := rfl
  have s24 : (24 : UInt64).toNat = 24 := rfl
  have s32 : (32 : UInt64).toNat = 32 := rfl
  have s40 : (40 : UInt64).toNat = 40 := rfl
  have s48 : (48 : UInt64).toNat = 48 := rfl
  have s56 : (56 : UInt64).toNat = 56 := rfl
  simp only [s8, s16, s24, s32, s40, s48, s56]
  if c0 : i < 8 then
    have n1 : ¬(8 ≤ i ∧ i < 8 + 8) := by intro h; omega
    have n2 : ¬(16 ≤ i ∧ i < 16 + 8) := by intro h; omega
    have n3 : ¬(24 ≤ i ∧ i < 24 + 8) := by intro h; omega
    have n4 : ¬(32 ≤ i ∧ i < 32 + 8) := by intro h; omega
    have n5 : ¬(40 ≤ i ∧ i < 40 + 8) := by intro h; omega
    have n6 : ¬(48 ≤ i ∧ i < 48 + 8) := by intro h; omega
    have n7 : ¬(56 ≤ i ∧ i < 56 + 8) := by intro h; omega
    simp [n1, n2, n3, n4, n5, n6, n7]
  else
    have hGe8 : 8 ≤ i := by omega
    rw [h0x _ hGe8, h0x _ hGe8, h0x _ hGe8]
    if c1 : i < 16 then
      have y1 : 8 ≤ i ∧ i < 8 + 8 := by constructor <;> omega
      have n2 : ¬(16 ≤ i ∧ i < 16 + 8) := by intro h; omega
      have n3 : ¬(24 ≤ i ∧ i < 24 + 8) := by intro h; omega
      have n4 : ¬(32 ≤ i ∧ i < 32 + 8) := by intro h; omega
      have n5 : ¬(40 ≤ i ∧ i < 40 + 8) := by intro h; omega
      have n6 : ¬(48 ≤ i ∧ i < 48 + 8) := by intro h; omega
      have n7 : ¬(56 ≤ i ∧ i < 56 + 8) := by intro h; omega
      simp [y1, n2, n3, n4, n5, n6, n7]
    else if c2 : i < 24 then
      have n1 : ¬(8 ≤ i ∧ i < 8 + 8) := by intro h; omega
      have y2 : 16 ≤ i ∧ i < 16 + 8 := by constructor <;> omega
      have n3 : ¬(24 ≤ i ∧ i < 24 + 8) := by intro h; omega
      have n4 : ¬(32 ≤ i ∧ i < 32 + 8) := by intro h; omega
      have n5 : ¬(40 ≤ i ∧ i < 40 + 8) := by intro h; omega
      have n6 : ¬(48 ≤ i ∧ i < 48 + 8) := by intro h; omega
      have n7 : ¬(56 ≤ i ∧ i < 56 + 8) := by intro h; omega
      simp [n1, y2, n3, n4, n5, n6, n7]
    else if c3 : i < 32 then
      have n1 : ¬(8 ≤ i ∧ i < 8 + 8) := by intro h; omega
      have n2 : ¬(16 ≤ i ∧ i < 16 + 8) := by intro h; omega
      have y3 : 24 ≤ i ∧ i < 24 + 8 := by constructor <;> omega
      have n4 : ¬(32 ≤ i ∧ i < 32 + 8) := by intro h; omega
      have n5 : ¬(40 ≤ i ∧ i < 40 + 8) := by intro h; omega
      have n6 : ¬(48 ≤ i ∧ i < 48 + 8) := by intro h; omega
      have n7 : ¬(56 ≤ i ∧ i < 56 + 8) := by intro h; omega
      simp [n1, n2, y3, n4, n5, n6, n7]
    else if c4 : i < 40 then
      have n1 : ¬(8 ≤ i ∧ i < 8 + 8) := by intro h; omega
      have n2 : ¬(16 ≤ i ∧ i < 16 + 8) := by intro h; omega
      have n3 : ¬(24 ≤ i ∧ i < 24 + 8) := by intro h; omega
      have y4 : 32 ≤ i ∧ i < 32 + 8 := by constructor <;> omega
      have n5 : ¬(40 ≤ i ∧ i < 40 + 8) := by intro h; omega
      have n6 : ¬(48 ≤ i ∧ i < 48 + 8) := by intro h; omega
      have n7 : ¬(56 ≤ i ∧ i < 56 + 8) := by intro h; omega
      simp [n1, n2, n3, y4, n5, n6, n7]
    else if c5 : i < 48 then
      have n1 : ¬(8 ≤ i ∧ i < 8 + 8) := by intro h; omega
      have n2 : ¬(16 ≤ i ∧ i < 16 + 8) := by intro h; omega
      have n3 : ¬(24 ≤ i ∧ i < 24 + 8) := by intro h; omega
      have n4 : ¬(32 ≤ i ∧ i < 32 + 8) := by intro h; omega
      have y5 : 40 ≤ i ∧ i < 40 + 8 := by constructor <;> omega
      have n6 : ¬(48 ≤ i ∧ i < 48 + 8) := by intro h; omega
      have n7 : ¬(56 ≤ i ∧ i < 56 + 8) := by intro h; omega
      simp [n1, n2, n3, n4, y5, n6, n7]
    else if c6 : i < 56 then
      have n1 : ¬(8 ≤ i ∧ i < 8 + 8) := by intro h; omega
      have n2 : ¬(16 ≤ i ∧ i < 16 + 8) := by intro h; omega
      have n3 : ¬(24 ≤ i ∧ i < 24 + 8) := by intro h; omega
      have n4 : ¬(32 ≤ i ∧ i < 32 + 8) := by intro h; omega
      have n5 : ¬(40 ≤ i ∧ i < 40 + 8) := by intro h; omega
      have y6 : 48 ≤ i ∧ i < 48 + 8 := by constructor <;> omega
      have n7 : ¬(56 ≤ i ∧ i < 56 + 8) := by intro h; omega
      simp [n1, n2, n3, n4, n5, y6, n7]
    else
      have n1 : ¬(8 ≤ i ∧ i < 8 + 8) := by intro h; omega
      have n2 : ¬(16 ≤ i ∧ i < 16 + 8) := by intro h; omega
      have n3 : ¬(24 ≤ i ∧ i < 24 + 8) := by intro h; omega
      have n4 : ¬(32 ≤ i ∧ i < 32 + 8) := by intro h; omega
      have n5 : ¬(40 ≤ i ∧ i < 40 + 8) := by intro h; omega
      have n6 : ¬(48 ≤ i ∧ i < 48 + 8) := by intro h; omega
      have y7 : 56 ≤ i ∧ i < 56 + 8 := by constructor <;> omega
      simp [n1, n2, n3, n4, n5, n6, y7]

theorem loadLe64_replicate_zero : ∀ (n laneIdx : Nat),
    loadLe64 (List.replicate n 0) laneIdx = 0 := by
  intro n laneIdx
  have hRep0 : ∀ m k, (List.replicate m (0 : UInt8)).getD k 0 = 0 := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro k
      cases k with
      | zero => rfl
      | succ k => exact ih k
  unfold loadLe64
  dsimp only
  simp only [hRep0]
  decide

def xorRate136 (s : KState) (block : List UInt8) : KState :=
  { s with
    a0  := s.a0  ^^^ loadLe64 block 0
    a1  := s.a1  ^^^ loadLe64 block 1
    a2  := s.a2  ^^^ loadLe64 block 2
    a3  := s.a3  ^^^ loadLe64 block 3
    a4  := s.a4  ^^^ loadLe64 block 4
    a5  := s.a5  ^^^ loadLe64 block 5
    a6  := s.a6  ^^^ loadLe64 block 6
    a7  := s.a7  ^^^ loadLe64 block 7
    a8  := s.a8  ^^^ loadLe64 block 8
    a9  := s.a9  ^^^ loadLe64 block 9
    a10 := s.a10 ^^^ loadLe64 block 10
    a11 := s.a11 ^^^ loadLe64 block 11
    a12 := s.a12 ^^^ loadLe64 block 12
    a13 := s.a13 ^^^ loadLe64 block 13
    a14 := s.a14 ^^^ loadLe64 block 14
    a15 := s.a15 ^^^ loadLe64 block 15
    a16 := s.a16 ^^^ loadLe64 block 16 }

def padForRate (bytes : List UInt8) (suffix : UInt8) : List UInt8 :=
  let count := shake256RateBytes - bytes.length % shake256RateBytes
  if count = 1 then
    bytes ++ [suffix ^^^ (0x80 : UInt8)]
  else
    bytes ++ [suffix] ++ List.replicate (count - 2) 0 ++ [0x80]

def absorbBlocks : Nat → KState → List UInt8 → KState
  | 0, s, _ => s
  | k + 1, s, rest =>
    absorbBlocks k (keccakF1600 (xorRate136 s (rest.take shake256RateBytes)))
      (rest.drop shake256RateBytes)

def absorbPadded (padded : List UInt8) : KState :=
  absorbBlocks (padded.length / shake256RateBytes) zeroKState padded

private def laneBytesLE (w : UInt64) : List UInt8 :=
  [UInt8.ofNat (w.toNat % 256),
   UInt8.ofNat ((w.toNat / 256) % 256),
   UInt8.ofNat ((w.toNat / 65536) % 256),
   UInt8.ofNat ((w.toNat / 16777216) % 256),
   UInt8.ofNat ((w.toNat / 4294967296) % 256),
   UInt8.ofNat ((w.toNat / 1099511627776) % 256),
   UInt8.ofNat ((w.toNat / 281474976710656) % 256),
   UInt8.ofNat ((w.toNat / 72057594037927936) % 256)]

def xorKState (s t : KState) : KState :=
  ⟨s.a0 ^^^ t.a0, s.a1 ^^^ t.a1, s.a2 ^^^ t.a2, s.a3 ^^^ t.a3, s.a4 ^^^ t.a4,
   s.a5 ^^^ t.a5, s.a6 ^^^ t.a6, s.a7 ^^^ t.a7, s.a8 ^^^ t.a8, s.a9 ^^^ t.a9,
   s.a10 ^^^ t.a10, s.a11 ^^^ t.a11, s.a12 ^^^ t.a12, s.a13 ^^^ t.a13, s.a14 ^^^ t.a14,
   s.a15 ^^^ t.a15, s.a16 ^^^ t.a16, s.a17 ^^^ t.a17, s.a18 ^^^ t.a18, s.a19 ^^^ t.a19,
   s.a20 ^^^ t.a20, s.a21 ^^^ t.a21, s.a22 ^^^ t.a22, s.a23 ^^^ t.a23, s.a24 ^^^ t.a24⟩

theorem xorKState_eq (s t : KState) :
    xorKState s t =
      ⟨s.a0 ^^^ t.a0, s.a1 ^^^ t.a1, s.a2 ^^^ t.a2, s.a3 ^^^ t.a3, s.a4 ^^^ t.a4,
       s.a5 ^^^ t.a5, s.a6 ^^^ t.a6, s.a7 ^^^ t.a7, s.a8 ^^^ t.a8, s.a9 ^^^ t.a9,
       s.a10 ^^^ t.a10, s.a11 ^^^ t.a11, s.a12 ^^^ t.a12, s.a13 ^^^ t.a13, s.a14 ^^^ t.a14,
       s.a15 ^^^ t.a15, s.a16 ^^^ t.a16, s.a17 ^^^ t.a17, s.a18 ^^^ t.a18, s.a19 ^^^ t.a19,
       s.a20 ^^^ t.a20, s.a21 ^^^ t.a21, s.a22 ^^^ t.a22, s.a23 ^^^ t.a23, s.a24 ^^^ t.a24⟩ := by rfl

private theorem uint8_ofNat_div_pow_xor (u v : UInt64) (sh : Nat) :
    UInt8.ofNat (((u ^^^ v).toNat / (2 ^ sh)) % (2 ^ 8)) =
      (UInt8.ofNat ((u.toNat / (2 ^ sh)) % (2 ^ 8)) ^^^ UInt8.ofNat ((v.toNat / (2 ^ sh)) % (2 ^ 8))) := by
  rw [← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow]
  apply UInt8.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hBit : ∀ (w : UInt64),
      (UInt8.ofNat ((w.toNat >>> sh) % 2 ^ 8)).toBitVec.getLsbD i = w.toBitVec.getLsbD (sh + i) := by
    intro w
    change (BitVec.ofNat 8 ((w.toNat >>> sh) % 2 ^ 8)).getLsbD i = w.toNat.testBit (sh + i)
    rw [BitVec.getLsbD_ofNat, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
    simp [hi]
  rw [UInt8.toBitVec_xor, BitVec.getLsbD_xor, hBit (u ^^^ v), hBit u, hBit v]
  simp [UInt64.toBitVec_xor]

private theorem laneBytesLE_xor (u v : UInt64) :
    laneBytesLE (u ^^^ v) = List.zipWith (· ^^^ ·) (laneBytesLE u) (laneBytesLE v) := by
  unfold laneBytesLE
  have p0 : (u ^^^ v).toNat % 256 = ((u ^^^ v).toNat / 2 ^ 0) % 256 := by simp
  have u0 : u.toNat % 256 = (u.toNat / 2 ^ 0) % 256 := by simp
  have v0 : v.toNat % 256 = (v.toNat / 2 ^ 0) % 256 := by simp
  rw [p0, u0, v0]
  have d1 : (256 : Nat) = 2 ^ 8 := rfl
  have d2 : (65536 : Nat) = 2 ^ 16 := rfl
  have d3 : (16777216 : Nat) = 2 ^ 24 := rfl
  have d4 : (4294967296 : Nat) = 2 ^ 32 := rfl
  have d5 : (1099511627776 : Nat) = 2 ^ 40 := rfl
  have d6 : (281474976710656 : Nat) = 2 ^ 48 := rfl
  have d7 : (72057594037927936 : Nat) = 2 ^ 56 := rfl
  rw [d1, d2, d3, d4, d5, d6, d7]
  simp only [List.zipWith_cons_cons, List.zipWith_nil_right, uint8_ofNat_div_pow_xor]

private theorem zipWith_append_eq {α β γ : Type} (f : α → β → γ) :
    ∀ {xs1 xs2 : List α} {ys1 ys2 : List β},
      xs1.length = ys1.length →
      List.zipWith f (xs1 ++ xs2) (ys1 ++ ys2) = List.zipWith f xs1 ys1 ++ List.zipWith f xs2 ys2
  | [], xs2, [], ys2, _ => rfl
  | _ :: xs1, xs2, _ :: ys1, ys2, h => by
    simp only [List.cons_append, List.zipWith_cons_cons,
      zipWith_append_eq f (Nat.succ.inj h)]

def rateBlockBytes (s : KState) : List UInt8 :=
  laneBytesLE s.a0 ++ laneBytesLE s.a1 ++ laneBytesLE s.a2 ++ laneBytesLE s.a3 ++
  laneBytesLE s.a4 ++ laneBytesLE s.a5 ++ laneBytesLE s.a6 ++ laneBytesLE s.a7 ++
  laneBytesLE s.a8 ++ laneBytesLE s.a9 ++ laneBytesLE s.a10 ++ laneBytesLE s.a11 ++
  laneBytesLE s.a12 ++ laneBytesLE s.a13 ++ laneBytesLE s.a14 ++ laneBytesLE s.a15 ++
  laneBytesLE s.a16

theorem shake256RateBytes_eq : shake256RateBytes = 136 := by rfl

theorem xorRate136_eq (s : KState) (block : List UInt8) :
    xorRate136 s block =
      { s with
        a0  := s.a0  ^^^ loadLe64 block 0,  a1  := s.a1  ^^^ loadLe64 block 1,
        a2  := s.a2  ^^^ loadLe64 block 2,  a3  := s.a3  ^^^ loadLe64 block 3,
        a4  := s.a4  ^^^ loadLe64 block 4,  a5  := s.a5  ^^^ loadLe64 block 5,
        a6  := s.a6  ^^^ loadLe64 block 6,  a7  := s.a7  ^^^ loadLe64 block 7,
        a8  := s.a8  ^^^ loadLe64 block 8,  a9  := s.a9  ^^^ loadLe64 block 9,
        a10 := s.a10 ^^^ loadLe64 block 10, a11 := s.a11 ^^^ loadLe64 block 11,
        a12 := s.a12 ^^^ loadLe64 block 12, a13 := s.a13 ^^^ loadLe64 block 13,
        a14 := s.a14 ^^^ loadLe64 block 14, a15 := s.a15 ^^^ loadLe64 block 15,
        a16 := s.a16 ^^^ loadLe64 block 16 } := by rfl

theorem padForRate_eq (bytes : List UInt8) (suffix : UInt8) :
    padForRate bytes suffix =
      let count := shake256RateBytes - bytes.length % shake256RateBytes
      if count = 1 then bytes ++ [suffix ^^^ (0x80 : UInt8)]
      else bytes ++ [suffix] ++ List.replicate (count - 2) 0 ++ [0x80] := by rfl

theorem absorbBlocks_zero (s : KState) (rest : List UInt8) :
    absorbBlocks 0 s rest = s := by rfl

theorem absorbBlocks_succ (k : Nat) (s : KState) (rest : List UInt8) :
    absorbBlocks (k + 1) s rest =
      absorbBlocks k (keccakF1600 (xorRate136 s (rest.take shake256RateBytes)))
        (rest.drop shake256RateBytes) := by rfl

theorem absorbPadded_eq (padded : List UInt8) :
    absorbPadded padded = absorbBlocks (padded.length / shake256RateBytes) zeroKState padded := by rfl

private theorem laneBytesLE_length (w : UInt64) : (laneBytesLE w).length = 8 := by
  simp only [laneBytesLE, List.length_cons, List.length_nil]

theorem rateBlockBytes_length (s : KState) :
    (rateBlockBytes s).length = 136 := by
  simp only [rateBlockBytes, List.length_append, laneBytesLE_length]

theorem rateBlockBytes_xor (s t : KState) :
    rateBlockBytes (xorKState s t) = List.zipWith (· ^^^ ·) (rateBlockBytes s) (rateBlockBytes t) := by
  unfold rateBlockBytes xorKState
  dsimp only
  simp only [List.append_assoc]
  repeat rw [zipWith_append_eq (· ^^^ ·) ((laneBytesLE_length _).trans (laneBytesLE_length _).symm)]
  simp only [laneBytesLE_xor]

/-- Structural fuel-driven multi-block XOF squeeze avoiding `WellFounded.fix`. -/
def squeezeXofFuel : Nat → Nat → KState → List UInt8
  | 0, _, _ => []
  | _ + 1, 0, _ => []
  | fuel + 1, outLen + 1, s =>
    let blk := rateBlockBytes s
    if outLen + 1 ≤ 136 then
      blk.take (outLen + 1)
    else
      blk ++ squeezeXofFuel fuel (outLen + 1 - 136) (keccakF1600 s)

private theorem squeezeXofFuel_length :
    ∀ (fuel outLen : Nat) (s : KState), outLen ≤ 136 * fuel →
      (squeezeXofFuel fuel outLen s).length = outLen
  | 0, outLen, _, h => by
    have h0 : outLen = 0 := by omega
    subst h0; rfl
  | _ + 1, 0, _, _ => rfl
  | fuel + 1, outLen + 1, s, h => by
    simp only [squeezeXofFuel]
    if hle : outLen + 1 ≤ 136 then
      simp only [hle, ↓reduceIte, List.length_take, rateBlockBytes_length]
      omega
    else
      have hSub : outLen + 1 - 136 ≤ 136 * fuel := by omega
      simp only [hle, ↓reduceIte, List.length_append, rateBlockBytes_length,
        squeezeXofFuel_length fuel (outLen + 1 - 136) (keccakF1600 s) hSub]
      omega

/-- Multi-block XOF squeeze extracting an exact `outLen`-byte stream. -/
def squeezeXofAux (outLen : Nat) (s : KState) : List UInt8 :=
  squeezeXofFuel outLen outLen s

theorem squeezeXofFuel_zero (outLen : Nat) (s : KState) : squeezeXofFuel 0 outLen s = [] := by rfl
theorem squeezeXofFuel_succ_zero (fuel : Nat) (s : KState) : squeezeXofFuel (fuel + 1) 0 s = [] := by rfl
theorem squeezeXofFuel_succ_succ (fuel outLen : Nat) (s : KState) :
    squeezeXofFuel (fuel + 1) (outLen + 1) s =
      let blk := rateBlockBytes s
      if outLen + 1 ≤ 136 then blk.take (outLen + 1)
      else blk ++ squeezeXofFuel fuel (outLen + 1 - 136) (keccakF1600 s) := by rfl
theorem squeezeXofAux_eq (outLen : Nat) (s : KState) :
    squeezeXofAux outLen s = squeezeXofFuel outLen outLen s := by rfl

theorem squeezeXofAux_length (n : Nat) (s : KState) : (squeezeXofAux n s).length = n :=
  squeezeXofFuel_length n n s (by omega)

/-- NIST FIPS 202 `SHAKE256(msg, 8 * outLen)` producing `outLen` bytes (`0x1F` suffix). -/
@[expose] def shake256Xof (outLen : Nat) (input : List UInt8) : List UInt8 :=
  squeezeXofAux outLen (absorbPadded (padForRate input 0x1f))

@[simp] theorem shake256Xof_length (outLen : Nat) (input : List UInt8) :
    (shake256Xof outLen input).length = outLen :=
  squeezeXofAux_length outLen _

def customizationPrefix (customization : List UInt8) : List UInt8 :=
  bytepad (encodeString [] ++ encodeString customization) shake256RateBytes

/-- NIST SP 800-185 `cSHAKE256("", input, 8 * outLen, customization)`. -/
@[expose] def cshake256Xof (outLen : Nat) (customization input : List UInt8) : List UInt8 :=
  let shakeCompatible := customization = []
  let framed := if shakeCompatible then input else customizationPrefix customization ++ input
  let suffix : UInt8 := if shakeCompatible then 0x1f else 0x04
  squeezeXofAux outLen (absorbPadded (padForRate framed suffix))

@[simp] theorem cshake256Xof_length (outLen : Nat) (customization input : List UInt8) :
    (cshake256Xof outLen customization input).length = outLen :=
  squeezeXofAux_length outLen _

/-- Canonical 32-byte `cSHAKE256` digest. -/
@[expose] def cshake256Bytes (customization input : List UInt8) : List UInt8 :=
  cshake256Xof 32 customization input

@[simp] theorem cshake256Bytes_length (customization input : List UInt8) :
    (cshake256Bytes customization input).length = 32 :=
  cshake256Xof_length 32 customization input

theorem cshake256Xof_empty_eq_shake256Xof (outLen : Nat) (input : List UInt8) :
    cshake256Xof outLen [] input = shake256Xof outLen input := by rfl


/-! ## Framing interface: prefix laws and padding equations -/
private theorem append_left_cancel_local {α : Type} :
    ∀ (xs : List α) {ys zs : List α}, xs ++ ys = xs ++ zs → ys = zs
  | [], _, _, h => h
  | _ :: xs, _, _, h => append_left_cancel_local xs (List.cons.inj h).2

private theorem ofBE_natBytesLEAux :
    ∀ (fuel x : Nat), x ≤ fuel → ofBE (natBytesLEAux fuel x).reverse = x
  | 0, x, hx => by
    obtain rfl : x = 0 := Nat.eq_zero_of_le_zero hx
    rfl
  | fuel + 1, x, hx => by
    unfold natBytesLEAux
    if hx0 : x = 0 then subst hx0; rfl
    else
      simp only [hx0, ↓reduceIte, List.reverse_cons, ofBE_append_single, UInt8.toNat_ofNat']
      have hDivLe : x / 256 ≤ fuel :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (Nat.div_lt_self (Nat.pos_of_ne_zero hx0) (by decide)) hx)
      rw [ofBE_natBytesLEAux fuel (x / 256) hDivLe]
      have h8 : (2 : Nat) ^ 8 = 256 := rfl
      rw [h8, Nat.mod_mod, Nat.mul_comm, Nat.div_add_mod]

private theorem natBytesLEAux_last_nonzero :
    ∀ (fuel x : Nat), 0 < x → x ≤ fuel →
      ∃ b rest, (natBytesLEAux fuel x).reverse = b :: rest ∧ 0 < b.toNat
  | 0, _, hxPos, hxLe => False.elim (Nat.not_lt_of_ge hxLe hxPos)
  | fuel + 1, x, hxPos, hxLe => by
    have hxNe : x ≠ 0 := Nat.ne_of_gt hxPos
    unfold natBytesLEAux
    simp only [hxNe, ↓reduceIte, List.reverse_cons]
    if hq : x / 256 = 0 then
      have hNil : natBytesLEAux fuel (x / 256) = [] := by
        rw [hq]; cases fuel <;> simp [natBytesLEAux]
      rw [hNil]
      refine ⟨UInt8.ofNat (x % 256), [], rfl, ?_⟩
      simp only [UInt8.toNat_ofNat']
      have h8 : (2 : Nat) ^ 8 = 256 := rfl
      have hDiv := Nat.div_add_mod x 256
      rw [hq, Nat.mul_zero, Nat.zero_add] at hDiv
      rw [h8, Nat.mod_mod, hDiv]; exact hxPos
    else
      have hDivLe : x / 256 ≤ fuel :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (Nat.div_lt_self hxPos (by decide)) hxLe)
      obtain ⟨b, rest, hRev, hbPos⟩ := natBytesLEAux_last_nonzero fuel (x / 256) (Nat.pos_of_ne_zero hq) hDivLe
      exact ⟨b, rest ++ [UInt8.ofNat (x % 256)], by rw [hRev, List.cons_append], hbPos⟩

private theorem ofBE_foldl_ge :
    ∀ (xs : List UInt8) (acc : Nat),
      acc * 256 ^ xs.length ≤ xs.foldl (fun a u => a * 256 + u.toNat) acc
  | [], _ => by simp
  | u :: us, acc => by
    simp only [List.foldl_cons, List.length_cons]
    have h1 := Nat.mul_le_mul_right (256 ^ us.length) (Nat.le_add_right (acc * 256) u.toNat)
    have h2 := ofBE_foldl_ge us (acc * 256 + u.toNat)
    rw [Nat.pow_succ, Nat.mul_comm (256 ^ us.length) 256, ← Nat.mul_assoc]
    exact Nat.le_trans h1 h2

private theorem ofBE_cons_ge {b : UInt8} (hb : 0 < b.toNat) (rest : List UInt8) :
    256 ^ rest.length ≤ ofBE (b :: rest) := by
  unfold ofBE
  simp only [List.foldl_cons, Nat.zero_mul, Nat.zero_add]
  have h1 : 1 * 256 ^ rest.length ≤ b.toNat * 256 ^ rest.length :=
    Nat.mul_le_mul_right (256 ^ rest.length) hb
  rw [Nat.one_mul] at h1
  exact Nat.le_trans h1 (ofBE_foldl_ge rest b.toNat)

theorem ofBE_natBytesBE (x : Nat) : ofBE (natBytesBE x) = x := by
  unfold natBytesBE
  dsimp only
  if hNil : natBytesLEAux x x = [] then
    simp only [hNil, ↓reduceIte]
    have hx0 : x = 0 := by
      have h := ofBE_natBytesLEAux x x (Nat.le_refl x)
      simpa [hNil, ofBE] using h.symm
    subst hx0; rfl
  else
    simp only [hNil, ↓reduceIte]
    exact ofBE_natBytesLEAux x x (Nat.le_refl x)

private theorem append_inj_local {α : Type} :
    ∀ {xs₁ xs₂ ys₁ ys₂ : List α},
      xs₁ ++ ys₁ = xs₂ ++ ys₂ → xs₁.length = xs₂.length → xs₁ = xs₂ ∧ ys₁ = ys₂
  | [], [], _, _, hEq, _ => ⟨rfl, hEq⟩
  | _ :: _, [], _, _, _, hLen => by cases hLen
  | [], _ :: _, _, _, _, hLen => by cases hLen
  | x₁ :: xs₁, x₂ :: xs₂, _, _, hEq, hLen => by
    obtain ⟨hx, hTail⟩ := List.cons.inj hEq
    obtain ⟨hxs, hys⟩ := append_inj_local hTail (Nat.succ.inj hLen)
    exact ⟨hx ▸ congrArg (x₁ :: ·) hxs, hys⟩

private theorem pow_le_pow_right_local {b : Nat} (hb : 0 < b) :
    ∀ {m n : Nat}, m ≤ n → b ^ m ≤ b ^ n
  | _, _, h => by
    induction h with
    | refl => exact Nat.le_refl _
    | step _ ih =>
      rw [Nat.pow_succ]
      exact Nat.le_trans (by simpa [Nat.mul_one] using ih) (Nat.mul_le_mul_left _ hb)

private theorem lt_of_pow_lt_pow_256 :
    ∀ (m n : Nat), 256 ^ m < 256 ^ n → m < n
  | m, 0, h => False.elim (Nat.not_lt_of_ge (Nat.one_le_pow m 256 (by decide)) (by rw [Nat.pow_zero] at h; exact h))
  | 0, n + 1, _ => Nat.zero_lt_succ n
  | m + 1, n + 1, h => by
    rw [Nat.pow_succ, Nat.pow_succ] at h
    have hlt : 256 ^ m < 256 ^ n :=
      if hm : 256 ^ m < 256 ^ n then hm
      else False.elim (Nat.not_lt_of_ge (Nat.mul_le_mul_right 256 (Nat.le_of_not_lt hm)) h)
    exact Nat.succ_lt_succ (lt_of_pow_lt_pow_256 m n hlt)

private theorem natBytesBE_length_le_255 {x : Nat} (hx : x < 256 ^ 255) :
    (natBytesBE x).length ≤ 255 := by
  if hx0 : x = 0 then
    subst hx0; decide
  else
    obtain ⟨b, rest, hRev, hbPos⟩ := natBytesLEAux_last_nonzero x x (Nat.pos_of_ne_zero hx0) (Nat.le_refl x)
    have hNonNil : natBytesLEAux x x ≠ [] := fun hNil => by rw [hNil] at hRev; cases hRev
    have hEq : natBytesBE x = b :: rest := by unfold natBytesBE; simp [hNonNil, hRev]
    have hPowLe : 256 ^ rest.length ≤ x := by
      rw [← ofBE_natBytesBE x, hEq]; exact ofBE_cons_ge hbPos rest
    have hRestLt : rest.length < 255 := lt_of_pow_lt_pow_256 rest.length 255 (Nat.lt_of_le_of_lt hPowLe hx)
    rw [hEq, List.length_cons]
    exact hRestLt

/-- Fast SP 800-185 bit-length bound witness avoiding kernel expansion of `256 ^ 255`. -/
theorem bitlen_lt_sp800_bound {s : List UInt8} (h : s.length ≤ 65536) :
    8 * s.length < 256 ^ 255 := by
  have h1 : 8 * s.length ≤ 8 * 65536 := Nat.mul_le_mul_left 8 h
  have h2 : 8 * 65536 < 256 ^ 3 := by decide
  have h3 : 256 ^ 3 ≤ 256 ^ 255 := pow_le_pow_right_local (by decide) (by decide)
  exact Nat.lt_of_le_of_lt h1 (Nat.lt_of_lt_of_le h2 h3)

/-- **SP 800-185 `leftEncode` Prefix Injectivity (`leftEncode_prefix_inj`)**:
    For all `x₁, x₂ < 256 ^ 255`, `leftEncode` is strictly left-self-delimiting. -/
theorem leftEncode_prefix_inj {x₁ x₂ : Nat} {r₁ r₂ : List UInt8}
    (hx₁ : x₁ < 256 ^ 255) (hx₂ : x₂ < 256 ^ 255)
    (hEq : leftEncode x₁ ++ r₁ = leftEncode x₂ ++ r₂) :
    x₁ = x₂ ∧ r₁ = r₂ := by
  unfold leftEncode at hEq
  simp only [List.cons_append, List.cons.injEq] at hEq
  have hLen₁ := natBytesBE_length_le_255 hx₁
  have hLen₂ := natBytesBE_length_le_255 hx₂
  have hByte := congrArg UInt8.toNat hEq.1
  simp only [UInt8.toNat_ofNat'] at hByte
  have h8 : (2 : Nat) ^ 8 = 256 := rfl
  rw [h8] at hByte
  have hMod₁ : (natBytesBE x₁).length % 256 = (natBytesBE x₁).length :=
    Nat.mod_eq_of_lt (Nat.lt_succ_of_le hLen₁)
  have hMod₂ : (natBytesBE x₂).length % 256 = (natBytesBE x₂).length :=
    Nat.mod_eq_of_lt (Nat.lt_succ_of_le hLen₂)
  rw [hMod₁, hMod₂] at hByte
  obtain ⟨hBytes, hRest⟩ := append_inj_local hEq.2 hByte
  have hxEq : x₁ = x₂ := by rw [← ofBE_natBytesBE x₁, ← ofBE_natBytesBE x₂, hBytes]
  exact ⟨hxEq, hRest⟩

/-- **SP 800-185 `encodeString` Prefix Injectivity (`encodeString_prefix_inj`)**. -/
theorem encodeString_prefix_inj {s₁ s₂ r₁ r₂ : List UInt8}
    (hs₁ : 8 * s₁.length < 256 ^ 255) (hs₂ : 8 * s₂.length < 256 ^ 255)
    (hEq : encodeString s₁ ++ r₁ = encodeString s₂ ++ r₂) :
    s₁ = s₂ ∧ r₁ = r₂ := by
  unfold encodeString at hEq
  rw [List.append_assoc, List.append_assoc] at hEq
  obtain ⟨hBitLen, hTail⟩ := leftEncode_prefix_inj hs₁ hs₂ hEq
  exact append_inj_local hTail (Nat.eq_of_mul_eq_mul_left (by decide) hBitLen)

private theorem pad_align_arith (L w : Nat) (hw : 0 < w) (hL : 1 ≤ L) :
    (L + (w - L % w) % w) % w = 0 ∧ w ≤ L + (w - L % w) % w := by
  have hDiv := Nat.div_add_mod L w
  have hModLt : L % w < w := Nat.mod_lt L hw
  if hRem0 : L % w = 0 then
    rw [hRem0, Nat.sub_zero, Nat.mod_self, Nat.add_zero]
    rw [hRem0, Nat.add_zero] at hDiv
    cases hq : L / w with
    | zero => rw [hq, Nat.mul_zero] at hDiv; exact False.elim (Nat.not_le_of_gt hL (Nat.le_of_eq hDiv.symm))
    | succ k =>
      rw [hq, Nat.mul_succ] at hDiv
      exact ⟨hRem0, hDiv ▸ Nat.le_add_left w (w * k)⟩
  else
    rw [Nat.mod_eq_of_lt (Nat.sub_lt hw (Nat.pos_of_ne_zero hRem0))]
    have hEq : L + (w - L % w) = w * (L / w) + w := by
      conv => lhs; arg 1; rw [← hDiv]
      rw [Nat.add_assoc, Nat.add_sub_of_le (Nat.le_of_lt hModLt)]
    rw [hEq, ← Nat.mul_succ, Nat.mul_mod_right]
    exact ⟨rfl, Nat.le_add_left w (w * (L / w))⟩

theorem bytepad_length_mod (bytes : List UInt8) {w : Nat} (hw : 0 < w) :
    (bytepad bytes w).length % w = 0 ∧ w ≤ (bytepad bytes w).length := by
  have hwNe : w ≠ 0 := Nat.ne_of_gt hw
  unfold bytepad
  simp only [hwNe, ↓reduceIte, List.length_append, List.length_replicate]
  exact pad_align_arith ((leftEncode w).length + bytes.length) w hw
    (by unfold leftEncode; simp only [List.length_cons, Nat.add_right_comm, Nat.add_assoc]; exact Nat.le_add_left 1 _)


theorem bytepad_eq (bytes : List UInt8) (width : Nat) :
    bytepad bytes width =
      if width = 0 then [] else
        let z := leftEncode width ++ bytes
        z ++ List.replicate ((width - z.length % width) % width) 0 := by
  unfold bytepad
  rfl

theorem customizationPrefix_eq (s : List UInt8) :
    customizationPrefix s = bytepad (encodeString [] ++ encodeString s) 136 := by
  unfold customizationPrefix
  rfl

/-- Byte-length interface for one-byte SP 800-185 integers. -/
theorem leftEncode_length_short {n : Nat} (h : n < 256) : (leftEncode n).length = 2 := by
  cases n with
  | zero => decide
  | succ n =>
    have hz : ∀ fuel, natBytesLEAux fuel 0 = [] := by
      intro fuel; cases fuel <;> simp [natBytesLEAux]
    simp [leftEncode, natBytesBE, natBytesLEAux, Nat.div_eq_of_lt h, hz]

/-- Framing adds two bytes to strings shorter than 32 bytes. -/
theorem encodeString_length_short {s : List UInt8} (h : s.length < 32) :
    (encodeString s).length = 2 + s.length := by
  unfold encodeString
  rw [List.length_append, leftEncode_length_short (by omega)]

/-! ### Exports for lane signing -/


end Qsag
end

public section
namespace Qsag
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
/-- Byte-level cSHAKE KAT for the aggregation stage PoW transcript fixture. -/
theorem cshake_stage_pow_fixture_70035 :
    ((cshake256Bytes [81, 83, 65, 71, 46, 80, 67, 83, 46, 80, 79, 87, 50, 47, 118, 49] ((cshake256Bytes [81, 83, 65, 71, 46, 65, 71, 71, 46, 70, 83, 95, 84, 82, 65, 78, 83, 67, 82, 73, 80, 84, 47, 118, 49] [87, 72, 73, 82, 95, 83, 84, 65, 71, 69, 95, 80, 79, 87]) ++ [147, 17, 1, 0, 0, 0, 0, 0])).take 2).all (· == 0) = true := by decide +kernel
/-- Changing the fixture nonce to zero fails its two-zero-byte target. -/
theorem cshake_stage_pow_fixture_0 :
    ((cshake256Bytes [81, 83, 65, 71, 46, 80, 67, 83, 46, 80, 79, 87, 50, 47, 118, 49] ((cshake256Bytes [81, 83, 65, 71, 46, 65, 71, 71, 46, 70, 83, 95, 84, 82, 65, 78, 83, 67, 82, 73, 80, 84, 47, 118, 49] [87, 72, 73, 82, 95, 83, 84, 65, 71, 69, 95, 80, 79, 87]) ++ [0, 0, 0, 0, 0, 0, 0, 0])).take 2).all (· == 0) = false := by decide +kernel
#verify_constructive cshake_stage_pow_fixture_70035 cshake_stage_pow_fixture_0
end Qsag
end

/-! ### Exports for lane oracle -/

public section
namespace Qsag

/-- Defining equation of `loadLe64`. -/
theorem loadLe64_eq (block : List UInt8) (laneIdx : Nat) :
    loadLe64 block laneIdx =
      ((block.getD (8 * laneIdx) 0).toUInt64 |||
        (block.getD (8 * laneIdx + 1) 0).toUInt64 <<< 8 |||
        (block.getD (8 * laneIdx + 2) 0).toUInt64 <<< 16 |||
        (block.getD (8 * laneIdx + 3) 0).toUInt64 <<< 24 |||
        (block.getD (8 * laneIdx + 4) 0).toUInt64 <<< 32 |||
        (block.getD (8 * laneIdx + 5) 0).toUInt64 <<< 40 |||
        (block.getD (8 * laneIdx + 6) 0).toUInt64 <<< 48 |||
        (block.getD (8 * laneIdx + 7) 0).toUInt64 <<< 56) := by
  unfold loadLe64
  rfl

/-- FIPS 202 `SHA3-256("")`: rate-136 sponge with domain suffix `0x06`, 32-byte squeeze. -/
theorem sha3_256_empty_squeeze_kat :
    squeezeXofAux 32 (absorbPadded (padForRate [] 0x06)) =
      [0xa7, 0xff, 0xc6, 0xf8, 0xbf, 0x1e, 0xd7, 0x66,
       0x51, 0xc1, 0x47, 0x56, 0xa0, 0x61, 0xd6, 0x62,
       0xf5, 0x80, 0xff, 0x4d, 0xe4, 0x3b, 0x49, 0xfa,
       0x82, 0xd8, 0x0a, 0x4b, 0x80, 0xf8, 0x43, 0x4a] := by
  decide +kernel

/-- Original `Keccak-256("")`: rate-136 sponge with domain suffix `0x01`, 32-byte squeeze. -/
theorem keccak256_empty_squeeze_kat :
    squeezeXofAux 32 (absorbPadded (padForRate [] 0x01)) =
      [0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c,
       0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0,
       0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b,
       0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70] := by
  decide +kernel

/-- FIPS 202 `SHA3-512("")`: one permutation of the rate-72 padded empty block
    (lane 0 is the `0x06` suffix, lane 8 carries the final `0x80` pad byte), 64-byte squeeze. -/
theorem sha3_512_empty_squeeze_kat :
    squeezeXofAux 64 (keccakF1600
      ⟨0x06, 0, 0, 0, 0, 0, 0, 0, 0x8000000000000000, 0, 0, 0, 0,
       0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩) =
      [0xa6, 0x9f, 0x73, 0xcc, 0xa2, 0x3a, 0x9a, 0xc5,
       0xc8, 0xb5, 0x67, 0xdc, 0x18, 0x5a, 0x75, 0x6e,
       0x97, 0xc9, 0x82, 0x16, 0x4f, 0xe2, 0x58, 0x59,
       0xe0, 0xd1, 0xdc, 0xc1, 0x47, 0x5c, 0x80, 0xa6,
       0x15, 0xb2, 0x12, 0x3a, 0xf1, 0xf5, 0xf9, 0x4c,
       0x11, 0xe3, 0xe9, 0x40, 0x2c, 0x3a, 0xc5, 0x58,
       0xf5, 0x00, 0x19, 0x9d, 0x95, 0xb6, 0xd3, 0xe3,
       0x01, 0x75, 0x85, 0x86, 0x28, 0x1d, 0xcd, 0x26] := by
  decide +kernel

/-! ## 6. Official NIST FIPS 202 `SHAKE256` Build-Time Conformance Vectors -/

-- NIST FIPS 202 SHAKE256("", 256) = 46b9dd2b0ba88d13233b3feb743eeb243fcd52ea62b81b82b50c27646ed5762f
example : shake256Xof 32 [] =
    [0x46, 0xb9, 0xdd, 0x2b, 0x0b, 0xa8, 0x8d, 0x13,
     0x23, 0x3b, 0x3f, 0xeb, 0x74, 0x3e, 0xeb, 0x24,
     0x3f, 0xcd, 0x52, 0xea, 0x62, 0xb8, 0x1b, 0x82,
     0xb5, 0x0c, 0x27, 0x64, 0x6e, 0xd5, 0x76, 0x2f] := by decide +kernel

-- NIST FIPS 202 SHAKE256("abc", 256) = 483366601360a8771c6863080cc4114d8db44530f8f1e1ee4f94ea37e78b5739
example : shake256Xof 32 [0x61, 0x62, 0x63] =
    [0x48, 0x33, 0x66, 0x60, 0x13, 0x60, 0xa8, 0x77,
     0x1c, 0x68, 0x63, 0x08, 0x0c, 0xc4, 0x11, 0x4d,
     0x8d, 0xb4, 0x45, 0x30, 0xf8, 0xf1, 0xe1, 0xee,
     0x4f, 0x94, 0xea, 0x37, 0xe7, 0x8b, 0x57, 0x39] := by decide +kernel


/-- The framed length behind `tooth_oversized_tag_midstate_single_block_fails` (`Tests/OracleAndQrom`):
    an empty name and a 131-byte customization string frame to 136 bytes, over the 134-byte fit. -/
theorem encodeString_empty_append_replicate131_length :
    (encodeString [] ++ encodeString (List.replicate 131 0x41)).length = 136 := by
  have hB0 : natBytesBE 0 = [0] := by decide
  have hB1048 : natBytesBE 1048 = [4, 24] := by decide
  simp only [encodeString, leftEncode, List.length_append, List.length_replicate,
    List.length_nil, Nat.mul_zero, hB0, hB1048, List.length_cons]

#verify_constructive Qsag.leftEncode_prefix_inj Qsag.encodeString_prefix_inj
  Qsag.encodeString_empty_append_replicate131_length

/-! ### Executed-Rust cSHAKE256 vectors for the SPN chain step

`cshake256_framed_xof` and the two streams behind `rust_parallel_chain_step_executed_kat` (`Oracle/Spn`,
audited in `Tests/OracleAndQrom`). They are evaluated here because the sponge body is not exported. -/

/-- Frame body of `cshake256_framed_xof` (`keccak.rs:281-284`). -/
def spnFramesU64LeBody : List (List UInt8) → List UInt8
  | [] => []
  | f :: fs => (encodeNatLeBytes 8 f.length ++ f) ++ spnFramesU64LeBody fs

/-- `cshake256_framed_xof` (`qsag-accel/src/keccak.rs`) over the `Qsag.Keccak` cSHAKE256 model. -/
def spnCshake256FramedXof (customization : List UInt8) (frames : List (List UInt8))
    (outLen : Nat) : List UInt8 :=
  cshake256Xof outLen customization
    (encodeNatLeBytes 8 frames.length ++ spnFramesU64LeBody frames)

/-- `pk_seed = 00 01 … 1f`. -/
def chainStepKatPkSeed : List UInt8 :=
  [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b,
   0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
   0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f]

/-- The `48 * 32` bytes written by the compiled Rust `cshake256_framed_xof` for the frames of
    `round_constants(chainStepKatTweak)`. -/
def chainStepKatRustStream : List UInt8 :=
  [0x42, 0xcd, 0x4c, 0x60, 0x1c, 0x0c, 0x8d, 0x58, 0x98, 0x65, 0xfa, 0x2b,
   0xd7, 0x4e, 0x3a, 0x8a, 0xfd, 0x04, 0x9d, 0x0a, 0x7c, 0x73, 0x4f, 0x61,
   0x47, 0x00, 0xf6, 0x3c, 0xdb, 0x1a, 0x89, 0x7d, 0x61, 0xc0, 0x7c, 0xc6,
   0x37, 0xa6, 0x2f, 0xf0, 0x9b, 0x97, 0xe7, 0x1b, 0x12, 0x8c, 0x7e, 0x87,
   0x3b, 0x5e, 0x3d, 0x2e, 0xd8, 0x1b, 0xb2, 0x7f, 0xfc, 0x2c, 0xe6, 0x5f,
   0xc3, 0x26, 0xa6, 0x31, 0xf9, 0x79, 0x04, 0xa6, 0x04, 0x8e, 0x42, 0xdb,
   0x45, 0xd2, 0xea, 0x9c, 0xa0, 0x7e, 0x82, 0x9d, 0x3c, 0x7d, 0x01, 0xa9,
   0xd2, 0x2d, 0x1e, 0x25, 0x6a, 0xc2, 0x6d, 0xbe, 0x56, 0xfc, 0x5b, 0x52,
   0x67, 0x49, 0x60, 0xb1, 0xc1, 0x05, 0x37, 0x4c, 0xda, 0xb7, 0x04, 0x27,
   0x54, 0x7a, 0x98, 0xa2, 0xf9, 0xbf, 0xbd, 0x81, 0xd8, 0x8a, 0x57, 0x58,
   0xd7, 0x9c, 0x94, 0x4f, 0x24, 0xd0, 0xae, 0x85, 0xc7, 0xb1, 0x99, 0xca,
   0x24, 0x5a, 0x03, 0x56, 0x23, 0x81, 0x16, 0xb3, 0xb5, 0xcd, 0x4f, 0xa3,
   0x04, 0xe0, 0x81, 0x10, 0xeb, 0xff, 0x59, 0x01, 0x0b, 0x31, 0x87, 0xc7,
   0x66, 0x79, 0x2b, 0xd5, 0xa6, 0xd6, 0xd7, 0x6d, 0xb0, 0xc2, 0x57, 0xa7,
   0x31, 0x7a, 0xa1, 0x87, 0x65, 0xb0, 0x25, 0xb8, 0x34, 0x26, 0x38, 0xfb,
   0x5c, 0xcb, 0x96, 0x32, 0x89, 0xdc, 0x5f, 0x33, 0x7b, 0xed, 0x6a, 0x9b,
   0xec, 0x23, 0xd9, 0x69, 0xbb, 0x00, 0x01, 0x5b, 0x2c, 0x5f, 0x7a, 0x52,
   0xbd, 0xfa, 0x4a, 0x3c, 0x9b, 0x3c, 0x84, 0x0b, 0x98, 0xde, 0x34, 0xe1,
   0x02, 0x80, 0xdf, 0xc2, 0x41, 0x62, 0x36, 0xcd, 0x09, 0x06, 0x10, 0xea,
   0x2d, 0xbe, 0xb3, 0x7d, 0x76, 0x6f, 0x45, 0x56, 0x8b, 0xa3, 0x4d, 0x39,
   0xf3, 0xb3, 0xe0, 0xdc, 0x4b, 0x04, 0x40, 0xdf, 0xcf, 0x2a, 0x92, 0xad,
   0x39, 0xd0, 0x14, 0x64, 0xd1, 0x80, 0xbf, 0xed, 0x80, 0xdc, 0xb9, 0x54,
   0x1a, 0xd6, 0x4b, 0xf0, 0x84, 0xef, 0xcc, 0x49, 0x5f, 0x67, 0xbb, 0xaa,
   0x38, 0xab, 0xa4, 0xff, 0xc3, 0x0a, 0x68, 0x8c, 0x0a, 0x8e, 0x07, 0x10,
   0xf0, 0x87, 0xd4, 0x02, 0x27, 0xc7, 0x61, 0x1d, 0x31, 0xce, 0x7f, 0x0b,
   0x1e, 0x17, 0x08, 0x85, 0xe7, 0xc5, 0x26, 0x63, 0x02, 0x94, 0x31, 0x9e,
   0x39, 0xb0, 0xec, 0xf9, 0x07, 0x75, 0x89, 0xde, 0xca, 0xf2, 0xf4, 0x4b,
   0xff, 0x24, 0xbc, 0xb9, 0x36, 0x29, 0xb3, 0xff, 0x60, 0x6c, 0x64, 0x3d,
   0x03, 0x34, 0x96, 0x3e, 0x46, 0x2e, 0x76, 0x5c, 0xe4, 0x1c, 0xed, 0x71,
   0x20, 0x78, 0xcd, 0x33, 0x11, 0x2f, 0xcd, 0xab, 0x8a, 0xd8, 0xca, 0x75,
   0x11, 0xcc, 0xcd, 0xa1, 0x60, 0x8f, 0xf1, 0xea, 0xf3, 0x74, 0x1f, 0x38,
   0x58, 0x24, 0x3e, 0xbf, 0x8c, 0x39, 0xe3, 0x09, 0xd5, 0x36, 0x66, 0xbc,
   0x9b, 0x18, 0x38, 0xe0, 0x41, 0xa3, 0xf9, 0x41, 0xe9, 0xc3, 0xbe, 0xf7,
   0x1c, 0x2f, 0x4c, 0x2b, 0x1c, 0xaa, 0x92, 0x6b, 0x75, 0xf0, 0x6c, 0xd9,
   0x43, 0x4a, 0x8b, 0xca, 0xe7, 0xbc, 0x26, 0x73, 0xe2, 0xcf, 0xb8, 0x0a,
   0x75, 0x22, 0x52, 0x78, 0x18, 0x06, 0x69, 0x3c, 0xce, 0xb6, 0xa1, 0xc9,
   0x74, 0xdd, 0xcb, 0x42, 0xe2, 0x76, 0x1d, 0xb6, 0xd6, 0xf7, 0x8a, 0xf6,
   0xce, 0x6b, 0x9f, 0x86, 0xfd, 0x1a, 0x31, 0x9d, 0xa5, 0xa3, 0x30, 0x82,
   0x58, 0xcb, 0x4f, 0x52, 0x94, 0xea, 0x82, 0x35, 0x4c, 0x32, 0x09, 0xe8,
   0xdd, 0x43, 0x38, 0x75, 0xd6, 0x53, 0x25, 0x86, 0xd7, 0xba, 0x9b, 0xd2,
   0x59, 0xfc, 0x0c, 0xd5, 0xca, 0x36, 0x0a, 0xdc, 0x01, 0xc7, 0xe6, 0xc2,
   0x2e, 0xe8, 0x7e, 0x2b, 0x28, 0x89, 0x54, 0x19, 0xab, 0xeb, 0x1d, 0xa5,
   0x39, 0x9a, 0x81, 0xdb, 0x19, 0xfd, 0xd6, 0x34, 0x46, 0xba, 0xb3, 0xe4,
   0xec, 0xe1, 0x39, 0x61, 0xde, 0xe7, 0x22, 0x80, 0xbe, 0x24, 0x5b, 0x3b,
   0xc2, 0xf5, 0x8f, 0xbf, 0x70, 0xe2, 0x22, 0x5d, 0xa8, 0x02, 0xec, 0x23,
   0x96, 0xa5, 0x28, 0xe6, 0x42, 0xa5, 0xdf, 0xf5, 0xea, 0x5e, 0x6d, 0x59,
   0x66, 0x1a, 0x21, 0x25, 0xa3, 0xcf, 0x23, 0x22, 0x43, 0x6f, 0x17, 0x22,
   0x0f, 0xb3, 0xb2, 0x4c, 0x04, 0xfa, 0xe5, 0x64, 0xb2, 0x75, 0x72, 0x01,
   0x68, 0x30, 0x68, 0x2c, 0x53, 0xa6, 0x52, 0xf3, 0x85, 0x04, 0xe0, 0xd1,
   0x55, 0xb2, 0xfc, 0x80, 0x21, 0xf8, 0xcb, 0xa8, 0x70, 0x2f, 0x11, 0x37,
   0x5b, 0x66, 0xa1, 0x39, 0xee, 0x41, 0xc1, 0xde, 0xfe, 0xc1, 0x69, 0x45,
   0x9b, 0xbf, 0x8c, 0x3c, 0x23, 0xfa, 0xa8, 0x00, 0x49, 0xd9, 0x88, 0x4c,
   0xee, 0x80, 0xd2, 0x9f, 0x9c, 0x6d, 0xdc, 0x89, 0x1c, 0x25, 0xd6, 0x32,
   0x9c, 0xe4, 0x78, 0x0a, 0xc3, 0xf5, 0xee, 0xac, 0xfa, 0x30, 0x2d, 0xb2,
   0x77, 0x05, 0x86, 0x1e, 0x4d, 0xba, 0x91, 0xe4, 0xb4, 0x9e, 0x2c, 0x0d,
   0xb0, 0x4d, 0x74, 0xc5, 0xf2, 0xdb, 0x95, 0xa2, 0xe2, 0x5e, 0xba, 0xba,
   0xba, 0x36, 0x83, 0xb2, 0x99, 0xe2, 0x69, 0x41, 0x37, 0x93, 0x7e, 0x7e,
   0xd8, 0x13, 0x4a, 0xa1, 0xa7, 0x32, 0x07, 0x7b, 0xb2, 0x2d, 0x9f, 0xb4,
   0x43, 0x93, 0x14, 0x9e, 0xb0, 0x2f, 0xf5, 0x17, 0xcf, 0xb4, 0xff, 0x1e,
   0x1a, 0x9e, 0xfd, 0x38, 0xa7, 0x81, 0x72, 0x38, 0x72, 0xfa, 0x41, 0xac,
   0x5a, 0x83, 0x91, 0x88, 0xa2, 0x6e, 0xb7, 0x1f, 0x36, 0xfa, 0x43, 0xcb,
   0x80, 0x80, 0xd3, 0x4b, 0x7c, 0xaa, 0x98, 0xac, 0xc8, 0xb9, 0x77, 0x56,
   0x8e, 0xbe, 0xd5, 0xfe, 0xf2, 0xe8, 0xd3, 0x7e, 0x74, 0xdc, 0x0c, 0x43,
   0x1d, 0x8c, 0xd8, 0x29, 0x60, 0x76, 0x5a, 0xa0, 0xc4, 0x50, 0x09, 0x5f,
   0xb6, 0x76, 0xe7, 0xd4, 0xa5, 0x50, 0x0d, 0x2e, 0xb9, 0xa0, 0x91, 0xc4,
   0xea, 0x58, 0xa2, 0x74, 0xfc, 0x99, 0xd9, 0x44, 0x49, 0x99, 0x1a, 0xd4,
   0xb7, 0xdc, 0x53, 0x34, 0x06, 0xed, 0x9f, 0x79, 0x01, 0xf5, 0xbd, 0x44,
   0x57, 0x86, 0x78, 0x5d, 0xa2, 0xf0, 0x38, 0x6b, 0xc4, 0x7d, 0x14, 0x0a,
   0xe3, 0x65, 0xda, 0xd6, 0x09, 0xdd, 0xf0, 0xeb, 0x59, 0x7a, 0x46, 0xe3,
   0xf9, 0x7b, 0x44, 0xb8, 0xdf, 0xf4, 0xef, 0x43, 0x69, 0xfa, 0xdd, 0xb5,
   0x78, 0x66, 0xd0, 0xb0, 0xdb, 0x34, 0x05, 0x34, 0x9e, 0x98, 0x65, 0x4c,
   0xbe, 0x3b, 0x44, 0x7f, 0x14, 0xc5, 0x01, 0x99, 0xc3, 0xbc, 0x34, 0x6b,
   0xf8, 0x20, 0xd7, 0x29, 0xc1, 0x45, 0x12, 0x47, 0x87, 0x9e, 0x04, 0x5d,
   0xac, 0xef, 0xca, 0x61, 0xe4, 0xfc, 0x45, 0x05, 0x6e, 0xbe, 0xfe, 0x57,
   0xf0, 0x0c, 0x24, 0x52, 0x1c, 0x58, 0xb5, 0xa9, 0x08, 0x14, 0x7e, 0x53,
   0xab, 0xbd, 0x4b, 0xc9, 0x41, 0xe9, 0x71, 0x43, 0x53, 0x12, 0xda, 0x9f,
   0x3a, 0x6a, 0x07, 0x7e, 0xc5, 0xc4, 0x62, 0x0f, 0xd5, 0x2f, 0x3d, 0x22,
   0x94, 0x83, 0xe6, 0xe3, 0x02, 0xa0, 0x81, 0x4e, 0xc8, 0x2e, 0xcb, 0xb5,
   0xa3, 0x79, 0x23, 0x12, 0xcd, 0x20, 0x9e, 0x33, 0x0b, 0x7b, 0xc9, 0xfb,
   0x21, 0x73, 0xf6, 0x5c, 0x89, 0xb0, 0x68, 0xa1, 0x61, 0x58, 0x91, 0x51,
   0x0e, 0x65, 0x18, 0x67, 0xc6, 0x5c, 0x18, 0x87, 0x3b, 0x7a, 0x25, 0xea,
   0xbe, 0x0e, 0xd1, 0x9b, 0x5e, 0x5c, 0x26, 0x2d, 0xae, 0xce, 0xb0, 0xfb,
   0xce, 0x4c, 0x63, 0x8d, 0xbb, 0x38, 0x99, 0xb7, 0xf8, 0xa0, 0x1c, 0x2d,
   0x66, 0xcb, 0xf5, 0x4f, 0x2f, 0x31, 0x72, 0xea, 0x39, 0x72, 0x0e, 0x41,
   0x5d, 0x1c, 0x58, 0xa8, 0x12, 0x12, 0xd8, 0xaa, 0x73, 0x36, 0x35, 0x98,
   0x11, 0xa1, 0xba, 0x2e, 0x79, 0xe1, 0x5b, 0x45, 0xe6, 0xc3, 0xa1, 0xb9,
   0x59, 0x35, 0x56, 0x21, 0x5c, 0xb0, 0x30, 0xaa, 0x42, 0xe0, 0x97, 0x2d,
   0xde, 0xb9, 0x36, 0x01, 0x27, 0x53, 0xff, 0x96, 0xf8, 0x58, 0x33, 0xa0,
   0x85, 0x4c, 0x8e, 0x80, 0x3b, 0x64, 0x20, 0x32, 0x9c, 0xaa, 0xff, 0x69,
   0x10, 0xc1, 0x18, 0x03, 0x96, 0x8d, 0xf6, 0x2c, 0x43, 0xf3, 0xfb, 0x95,
   0xc7, 0x81, 0x14, 0xf2, 0x99, 0x56, 0xba, 0xc5, 0xbe, 0x9b, 0xc3, 0x4a,
   0xee, 0xca, 0x72, 0x0d, 0xb0, 0xe0, 0x16, 0xc7, 0x32, 0x95, 0x98, 0x56,
   0x62, 0x1b, 0xf6, 0xa0, 0xa4, 0x20, 0xb1, 0x7b, 0xff, 0x11, 0x67, 0xe7,
   0x1c, 0x31, 0x4d, 0xf2, 0xb0, 0x0b, 0x94, 0x81, 0x44, 0x18, 0x70, 0x7c,
   0xde, 0xd2, 0x22, 0xa6, 0x03, 0x99, 0xc0, 0xe6, 0xb0, 0x4a, 0xf9, 0x5d,
   0x70, 0xf7, 0xab, 0x2c, 0xfd, 0x48, 0x9d, 0x0f, 0x1b, 0xf5, 0xdd, 0xc7,
   0x7b, 0x86, 0xaa, 0x8c, 0xa6, 0xfc, 0x80, 0x1f, 0xbe, 0x77, 0xaf, 0x4d,
   0x40, 0xf1, 0xc9, 0x18, 0xf7, 0x05, 0xd6, 0xd9, 0x8f, 0x6c, 0x73, 0x70,
   0x66, 0x8b, 0x5e, 0x90, 0xf8, 0x91, 0xc8, 0x66, 0x3f, 0x3a, 0xe2, 0xea,
   0x5e, 0xb5, 0xb4, 0xdd, 0x47, 0xa8, 0x46, 0x9c, 0x65, 0xe1, 0x77, 0xd2,
   0x8f, 0x4d, 0x3d, 0x4b, 0x26, 0x2b, 0x34, 0xed, 0x79, 0x71, 0xfa, 0x2d,
   0x01, 0x47, 0x77, 0xc7, 0xa7, 0xe7, 0x5c, 0xf3, 0xfa, 0x51, 0x0a, 0x74,
   0x59, 0x27, 0xcf, 0xea, 0x4f, 0xc1, 0x7c, 0x0b, 0x46, 0x88, 0xbc, 0x6f,
   0xd6, 0xe2, 0xde, 0xd1, 0xaa, 0xea, 0x35, 0xc8, 0xd2, 0x1a, 0x4d, 0x52,
   0xd3, 0xf3, 0xbe, 0xe8, 0xe3, 0x45, 0x77, 0x23, 0x03, 0xf9, 0x55, 0x61,
   0xe8, 0x6b, 0x11, 0x2c, 0xcd, 0x6d, 0x7d, 0x21, 0x7a, 0x30, 0x41, 0xc7,
   0xc0, 0xa2, 0x96, 0xb1, 0x8c, 0x68, 0xdd, 0x41, 0x84, 0xf1, 0xc7, 0x08,
   0x3b, 0xbb, 0xce, 0x73, 0xc5, 0x7e, 0x3f, 0xec, 0xa3, 0xa7, 0x4b, 0xf7,
   0x65, 0xbc, 0xb6, 0xc5, 0x63, 0x66, 0x0c, 0x3a, 0x0e, 0x7e, 0xcd, 0x56,
   0x36, 0x50, 0x48, 0xf5, 0x0b, 0x9d, 0x71, 0x9a, 0xb2, 0x58, 0x65, 0xca,
   0x65, 0xa8, 0x0c, 0x90, 0x84, 0x65, 0x4e, 0x12, 0xef, 0xd8, 0x2b, 0x67,
   0x3e, 0x4e, 0xfe, 0x6c, 0xfc, 0x9d, 0x57, 0x38, 0xc0, 0xee, 0xf8, 0x05,
   0xfc, 0xc8, 0x3f, 0x68, 0x2c, 0x2e, 0xa8, 0x9e, 0xe8, 0x20, 0x83, 0x37,
   0xce, 0xa9, 0x0f, 0xd9, 0xbe, 0x32, 0x17, 0x6b, 0x78, 0x06, 0x38, 0xc8,
   0xaa, 0xa3, 0xe1, 0x8f, 0xc2, 0xb2, 0xa1, 0xce, 0x5f, 0xa6, 0xc8, 0x2e,
   0xc9, 0x52, 0x15, 0xc8, 0xc2, 0xc8, 0x8e, 0x08, 0xf2, 0xb0, 0x96, 0x7f,
   0x5a, 0x09, 0xd8, 0x4b, 0x93, 0xfa, 0xab, 0xd3, 0x7d, 0xe8, 0x37, 0x5d,
   0xa9, 0x28, 0x2c, 0x91, 0xaf, 0xa5, 0x4b, 0x79, 0x92, 0x6c, 0xbf, 0xbd,
   0xee, 0x04, 0x34, 0xa4, 0xf8, 0x7d, 0x54, 0x36, 0xfd, 0x20, 0x5d, 0x29,
   0x72, 0x4c, 0x98, 0xa7, 0xd4, 0xd0, 0x26, 0x2f, 0x75, 0x31, 0xc5, 0xf7,
   0xcc, 0xaf, 0x76, 0x7f, 0x83, 0x3a, 0xe8, 0x82, 0x34, 0x83, 0xd3, 0x1d,
   0x1f, 0x90, 0x8a, 0xa7, 0x0c, 0x7a, 0x67, 0x51, 0x4c, 0x6c, 0x10, 0x7b,
   0x51, 0xc2, 0x57, 0xa1, 0x4e, 0x90, 0x98, 0x14, 0x24, 0xbc, 0x34, 0x32,
   0xd0, 0xb1, 0x3b, 0x29, 0xc0, 0xc4, 0x59, 0x3e, 0x95, 0x4c, 0xaf, 0xbd,
   0xe9, 0x84, 0x13, 0x06, 0xed, 0x57, 0xaf, 0xe5, 0xcf, 0x74, 0x8d, 0x87,
   0x7b, 0x72, 0xf5, 0x7c, 0x27, 0x05, 0xbc, 0x1b, 0x22, 0xcb, 0x67, 0xe1,
   0x1a, 0x1e, 0xa6, 0xaa, 0x8e, 0x99, 0xc8, 0xa2, 0xda, 0xe6, 0x04, 0x5d,
   0xd6, 0xe2, 0x31, 0x7a, 0x52, 0x81, 0x36, 0x8b, 0xea, 0x21, 0x44, 0x48]

set_option maxRecDepth 8192 in
/-- `derive_chain_tweak` stream (label `QSAG.PSFTS.CHAIN_TWK.V2`) for `(pk_seed, epoch 7, chain_idx 3, step 2)`. -/
theorem chainStepKat_tweak_stream :
    spnCshake256FramedXof [0x51, 0x53, 0x41, 0x47, 0x2e, 0x50, 0x53, 0x46, 0x54, 0x53, 0x2e, 0x43, 0x48, 0x41, 0x49, 0x4e, 0x5f, 0x54, 0x57, 0x4b, 0x2e, 0x56, 0x32]
      [chainStepKatPkSeed, be 4 7, be 2 3, [2]] 32 =
      [0x3c, 0x42, 0x34, 0xde, 0x43, 0x46, 0xe9, 0x87, 0x97, 0xee, 0x7b, 0x4f, 0x86, 0xa6, 0x68, 0x46,
       0x10, 0x0e, 0x6a, 0x70, 0x37, 0xf4, 0x03, 0x31, 0x94, 0x1c, 0xb8, 0x5e, 0x43, 0x44, 0x77, 0x2f] := by
  decide +kernel

set_option maxRecDepth 65536 in
/-- `round_constants` stream (label `QSAG.PSFTS.POW7_ROUNDS.V5`) for the tweak above: the Lean cSHAKE256
    model reproduces the whole Rust round-constant stream. -/
theorem chainStepKat_round_constant_stream :
    spnCshake256FramedXof [0x51, 0x53, 0x41, 0x47, 0x2e, 0x50, 0x53, 0x46, 0x54, 0x53, 0x2e, 0x50, 0x4f, 0x57, 0x37, 0x5f, 0x52, 0x4f, 0x55, 0x4e, 0x44, 0x53, 0x2e, 0x56, 0x35]
      [[0x3c, 0x42, 0x34, 0xde, 0x43, 0x46, 0xe9, 0x87, 0x97, 0xee, 0x7b, 0x4f, 0x86, 0xa6, 0x68, 0x46],
       [0x10, 0x0e, 0x6a, 0x70, 0x37, 0xf4, 0x03, 0x31, 0x94, 0x1c, 0xb8, 0x5e, 0x43, 0x44, 0x77, 0x2f], be 4 48] (48 * 32) =
      chainStepKatRustStream := by
  decide +kernel

#verify_constructive Qsag.chainStepKat_tweak_stream Qsag.chainStepKat_round_constant_stream
#export_eqns chainStepKatRustStream

end Qsag
end
